import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29754.Phase
instance : HXor Bool Bool Bool := ⟨Bool.xor⟩
instance : HAnd Bool Bool Bool := ⟨Bool.and⟩
@[simp] theorem xor_core (a b : Bool) : a ^^^ b = Bool.xor a b := rfl
@[simp] theorem and_core (a b : Bool) : a &&& b = Bool.and a b := rfl

def phase (x : Bool) : Int := if x then -1 else 1

def fold2 (f : Bool → Int) := f false + f true

def fold4 (f : Bool → Bool → Int) := fold2 fun a => fold2 (f a)


def invFirst (bcoef offset pivot keep : Bool) : Bool :=
  Bool.xor (Bool.xor pivot (bcoef && keep)) offset

theorem invFirst_forward (bcoef offset a b : Bool) :
    invFirst bcoef offset (Bool.xor (Bool.xor a (bcoef && b)) offset) b = a := by
  cases bcoef <;> cases offset <;> cases a <;> cases b <;> decide

theorem invFirst_backward (bcoef offset pivot keep : Bool) :
    Bool.xor (Bool.xor (invFirst bcoef offset pivot keep) (bcoef && keep)) offset = pivot := by
  cases bcoef <;> cases offset <;> cases pivot <;> cases keep <;> decide


theorem fiberFirst (bcoef offset : Bool) (f : Bool → Bool → Int) :
    fold4 f = fold4 (fun pivot keep => f (invFirst bcoef offset pivot keep) keep) := by
  cases bcoef <;> cases offset <;> simp [fold4,fold2,invFirst] <;> omega

theorem fiberSwap (f : Bool → Bool → Int) :
    fold4 f = fold4 (fun pivot keep => f keep pivot) := by
  simp [fold4,fold2]; omega

theorem phase_xor (x y : Bool) : phase (Bool.xor x y) = phase x * phase y := by
  cases x <;> cases y <;> decide


theorem gauss (u v c : Bool) :
    fold4 (fun a b => phase (Bool.xor (Bool.xor (a && b) (u && a))
      (Bool.xor (v && b) c))) = 2 * phase (Bool.xor (u && v) c) := by
  cases u <;> cases v <;> cases c <;> decide

theorem paidOr (a b : Bool) : (a || b) = Bool.xor (Bool.xor a b) (a && b) := by
  cases a <;> cases b <;> decide


theorem lastProduct (u v c coef : Bool) :
    2 * phase (Bool.xor c (coef && (u && v))) =
    phase c + phase (Bool.xor c (coef && u)) +
      phase (Bool.xor c (coef && v)) - phase (Bool.xor c (coef && Bool.xor u v)) := by
  cases u <;> cases v <;> cases c <;> cases coef <;> decide


theorem fixedQuad (a b : Bool) : (a && b) = (if b then a else false) := by
  cases a <;> cases b <;> decide


end PEqualNP.Outside.L_meta_29754.Phase

namespace PEqualNP.Outside.L_meta_29754.Tape
open PEqualNP.Outside.L_meta_29754.Phase


inductive Aff : Nat → Type
  | lit : Bool → Aff n
  | var : Fin n → Aff n
  | add : Aff n → Aff n → Aff n

abbrev Env (n : Nat) := Fin n → Bool

def snoc (x : Env n) (v : Bool) : Env (n+1) := Fin.lastCases v x

def Aff.eval (x : Env n) : Aff n → Bool
  | .lit v => v
  | .var i => x i
  | .add u v => u.eval x ^^^ v.eval x

def Aff.scale (v : Bool) (e : Aff n) : Aff n :=
  if v then e else .lit false

@[simp] theorem Aff.eval_scale (v : Bool) (e : Aff n) (x : Env n) :
    (e.scale v).eval x = v &&& e.eval x := by
  cases v <;> simp [Aff.scale,Aff.eval]

def Aff.rename (f : Fin n → Fin m) : Aff n → Aff m
  | .lit b => .lit b
  | .var i => .var (f i)
  | .add u v => .add (u.rename f) (v.rename f)

theorem Aff.eval_rename (f : Fin n → Fin m) (e : Aff n) (x : Env m) :
    (e.rename f).eval x = e.eval (x ∘ f) := by
  induction e <;> simp [Aff.eval,Aff.rename, *]

abbrev Aff.up (e : Aff n) : Aff (n+1) := e.rename Fin.castSucc

@[simp] theorem Aff.eval_up (e : Aff n) (x : Env n) (v : Bool) :
    e.up.eval (snoc x v) = e.eval x := by
  rw [Aff.eval_rename]
  congr 1
  funext i
  simp [snoc]

structure Paired (n : Nat) where
  coeffA : Bool
  coeffB : Bool
  offset : Aff n

def Paired.eval (x : Env n) (a b : Bool) (p : Paired n) : Bool :=
  (p.coeffA &&& a) ^^^ (p.coeffB &&& b) ^^^ p.offset.eval x

def Paired.subst (a b : Aff n) (p : Paired n) : Aff n :=
  .add (.add (a.scale p.coeffA) (b.scale p.coeffB)) p.offset

@[simp] theorem Paired.eval_subst (p : Paired n) (x : Env n) (a b : Aff n) :
    (p.subst a b).eval x = p.eval x (a.eval x) (b.eval x) := by
  simp [Paired.subst,Paired.eval,Aff.eval]

def Paired.quiet (p : Paired n) : Bool := !p.coeffA && !p.coeffB

theorem Paired.eval_quiet (p : Paired n) (x : Env n) (a b : Bool) (h : p.quiet=true) :
    p.eval x a b = p.offset.eval x := by
  cases p with
  | mk u v w => cases u <;> cases v <;> simp_all [Paired.eval,Paired.quiet]

inductive PairCode : Nat → Type
  | ret : Paired n → PairCode n
  | prod : Paired n → Paired n → PairCode (n+1) → PairCode n

inductive Code : Nat → Type
  | ret : Aff n → Code n
  | save : Aff n → Code (n+1) → Code n
  | prod : Aff n → Aff n → Code (n+1) → Code n

def PairCode.eval : PairCode n → Env n → Bool → Bool → Bool
  | .ret p, x, a, b => p.eval x a b
  | .prod u v next, x, a, b =>
    next.eval (snoc x (u.eval x a b &&& v.eval x a b)) a b

def Code.eval : Code n → Env n → Bool
  | .ret u, x => u.eval x
  | .save u next, x => next.eval (snoc x (u.eval x))
  | .prod u v next, x => next.eval (snoc x (u.eval x &&& v.eval x))

def PairCode.cost : PairCode n → Nat
  | .ret _ => 0
  | .prod _ _ next => next.cost+1

def Code.cost : Code n → Nat
  | .ret _ => 0
  | .save _ next => next.cost
  | .prod _ _ next => next.cost+1

def PairCode.subst : PairCode n → Aff n → Aff n → Aff n → Code n
  | .ret p, a, b, add => .ret (.add (p.subst a b) add)
  | .prod u v next, a, b, add => .prod (u.subst a b) (v.subst a b)
    (next.subst a.up b.up add.up)

@[simp] theorem PairCode.cost_subst (p : PairCode n) (a b add : Aff n) :
    (p.subst a b add).cost = p.cost := by
  induction p <;> simp [PairCode.subst,PairCode.cost,Code.cost, *]

theorem PairCode.eval_subst (p : PairCode n) (a b add : Aff n) (x : Env n) :
    (p.subst a b add).eval x = p.eval x (a.eval x) (b.eval x) ^^^ add.eval x := by
  induction p with
  | ret u => simp [PairCode.subst,Code.eval,Aff.eval,PairCode.eval]
  | prod u v next ih =>
    simp [PairCode.subst,Code.eval,ih,PairCode.eval]


def pivotSub (p : Paired n) (i j : Bool) : Aff n × Aff n :=
  if p.coeffA then
    (.add (.lit (i ^^^ (p.coeffB &&& j))) p.offset, .lit j)
  else (.lit j, .add (.lit i) p.offset)

def quadPhase (p : Paired n) (i j : Bool) : Aff n :=
  (if p.coeffA then (pivotSub p i j).1 else (pivotSub p i j).2).scale j

theorem quadPhase_eval (p : Paired n) (i j : Bool) (x : Env n) :
    (quadPhase p i j).eval x =
      (pivotSub p i j).1.eval x &&& (pivotSub p i j).2.eval x := by
  cases p with
  | mk a b off =>
    cases a <;> cases j <;> simp [quadPhase,pivotSub,Aff.eval]

theorem fixed_pivot (p : Paired n) (h : p.quiet=false) (i j : Bool) (x : Env n) :
    p.eval x ((pivotSub p i j).1.eval x) ((pivotSub p i j).2.eval x) = i := by
  cases p with
  | mk a b f =>
    cases a <;> cases b <;> cases i <;> cases j <;> cases hZ : f.eval x <;>
      simp_all [Paired.quiet,Paired.eval,pivotSub,Aff.eval]

theorem fiber_subst (p : Paired n) (h : p.quiet=false) (x : Env n) (f : Bool → Bool → Int) :
    fold4 f = fold4 (fun i j => f ((pivotSub p i j).1.eval x) ((pivotSub p i j).2.eval x)) := by
  cases p with
  | mk a b off =>
    cases a <;> cases b <;> simp_all [Paired.quiet,pivotSub,Aff.eval]
    · have hs := fiberSwap f
      have hf := fiberFirst false (off.eval x) (fun i j => f j i)
      exact hs.trans (by simpa [invFirst] using hf)
    · simpa [invFirst] using (fiberFirst false (off.eval x) f)
    · simpa [invFirst] using (fiberFirst true (off.eval x) f)


def pivotCode (p q : Paired n) (next : PairCode (n+1)) (i j : Bool) : Code n :=
  let (a,b) := pivotSub p i j
  .save ((q.subst a b).scale i) (next.subst a.up b.up (quadPhase p i j).up)

@[simp] theorem pivotCode_cost (p q : Paired n) (next : PairCode (n+1)) (i j : Bool) :
    (pivotCode p q next i j).cost = next.cost := by
  simp [pivotCode,Code.cost]

theorem pivotCode_eval (p q : Paired n) (hp : p.quiet=false)
    (next : PairCode (n+1)) (i j : Bool) (x : Env n) :
    (pivotCode p q next i j).eval x =
      let a := (pivotSub p i j).1.eval x
      let b := (pivotSub p i j).2.eval x
      (PairCode.prod p q next).eval x a b ^^^ (a &&& b) := by
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, pivotCode,Code.eval,PairCode.eval,PairCode.eval_subst]
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Aff.eval_up,Aff.eval_scale,Paired.eval_subst,quadPhase_eval,fixed_pivot p hp i j x]

theorem pivotPairSum (p q : Paired n) (hp : p.quiet=false)
    (next : PairCode (n+1)) (x : Env n) (t : Bool) :
    fold4 (fun a b => phase ((PairCode.prod p q next).eval x a b ^^^ (a &&& b) ^^^ t)) =
    fold4 (fun i j => phase ((pivotCode p q next i j).eval x ^^^ t)) := by
  rw [fiber_subst p hp x]
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, pivotCode_eval p q hp]


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape
open PEqualNP.Outside.L_meta_29754.Phase


def lastSub (u v : Aff n) : Bool → Bool → Aff n
  | false, false => .lit false
  | false, true => u
  | true, false => v
  | true, true => .add u v

def lastCode (u v : Aff n) (out : Paired (n+1)) (i j : Bool) : Code n :=
  .save (lastSub u v i j) (.ret (.add out.offset (.lit (out.coeffA &&& out.coeffB))))

def contract : PairCode n → Bool → Bool → Code n
  | .ret out, _, _ => .ret out.offset
  | .prod p q tail, i, j =>
    if p.quiet = false then pivotCode p q tail i j
    else if q.quiet = false then pivotCode q p tail i j
    else
      match tail with
      | .ret out => lastCode p.offset q.offset out i j
      | .prod p' q' tail' => .prod p.offset q.offset (contract (.prod p' q' tail') i j)

def contractSign : PairCode n → Bool → Bool → Int
  | .ret _, _, _ => 1
  | .prod p q tail, i, j =>
    if p.quiet = false then 1
    else if q.quiet = false then 1
    else
      match tail with
      | .ret _ => phase (i &&& j)
      | .prod p' q' tail' => contractSign (.prod p' q' tail') i j

theorem contract_sign (p : PairCode n) (i j : Bool) :
    contractSign p i j = 1 ∨ contractSign p i j = -1 := by
  induction p with
  | ret o => exact Or.inl rfl
  | prod u v next ih =>
    by_cases hu : u.quiet = false
    · cases next <;> simp [contractSign,hu]
    by_cases hv : v.quiet = false
    · cases next <;> simp [contractSign,hu,hv]
    cases next with
    | ret o => cases i <;> cases j <;> simp [contractSign,hu,hv,phase]
    | prod s t tail => simpa [contractSign,hu,hv] using ih

theorem contract_cost (p : PairCode n) (i j : Bool) :
    (contract p i j).cost = p.cost - 1 := by
  induction p with
  | ret o => rfl
  | prod u v next ih =>
    by_cases hu : u.quiet = false
    · cases next <;> simp [contract,hu,PairCode.cost]
    by_cases hv : v.quiet = false
    · cases next <;> simp [contract,hu,hv,PairCode.cost]
    cases next with
    | ret o => simp [contract,hu,hv,PairCode.cost,Code.cost,lastCode]
    | prod s t tail =>
      rw [contract]
      simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, hu,hv]
      simp [Code.cost,ih,PairCode.cost]

theorem Aff.at_snoc (o : Aff (n+1)) (x : Env n) (v : Bool) :
    o.eval (snoc x v) =
      o.eval (snoc x false) ^^^ (v &&& (o.eval (snoc x false) ^^^ o.eval (snoc x true))) := by
  generalize h₁ : o.eval (snoc x false) = a
  generalize h₂ : o.eval (snoc x true) = b
  cases v <;> simp_all <;> cases a <;> cases b <;> decide

theorem phase_regroup (a b u v c t : Bool) :
    phase (Bool.xor (Bool.xor (Bool.xor (Bool.xor (u && a) (v && b)) c) (a && b)) t) =
      phase (Bool.xor (Bool.xor (a && b) (u && a)) (Bool.xor (v && b) (Bool.xor c t))) := by
  cases a <;> cases b <;> cases u <;> cases v <;> cases c <;> cases t <;> decide

theorem swap_gauge (a b c : Bool) : Bool.xor (Bool.xor c a) b = Bool.xor (Bool.xor c b) a := by
  cases a <;> cases b <;> cases c <;> decide

theorem last_sum (u v : Aff n) (out : Paired (n+1)) (x : Env n) (t : Bool) :
    fold4 (fun a b =>
      phase (out.eval (snoc x (u.eval x &&& v.eval x)) a b ^^^ (a &&& b) ^^^ t)) =
    fold4 (fun i j => phase (i &&& j) * phase ((lastCode u v out i j).eval x ^^^ t)) := by
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Paired.eval, lastCode, Code.eval, Aff.eval, fold4, fold2, lastSub]
  generalize hu : u.eval x = a
  generalize hv : v.eval x = b
  cases a <;> cases b <;>
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Bool.false_and, Bool.true_and, Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false]
  all_goals
    generalize out.offset.eval (snoc x false) = c
    generalize out.offset.eval (snoc x true) = d
    cases c <;> cases d <;> cases out.coeffA <;> cases out.coeffB <;> cases t <;> decide

theorem contract_sum (p : PairCode n) (hp : 0<p.cost) (x : Env n) (t : Bool) :
    fold4 (fun a b => phase (Bool.xor (Bool.xor (p.eval x a b) (a && b)) t)) =
    fold4 (fun i j => contractSign p i j * phase (Bool.xor ((contract p i j).eval x) t)) := by
  induction p with
  | ret o => simp [PairCode.cost] at hp
  | prod u v next ih =>
    by_cases hu : u.quiet = false
    · cases next <;> simpa [contract,contractSign,hu] using pivotPairSum u v hu _ x t
    by_cases hv : v.quiet = false
    · have heq : (PairCode.prod u v next).eval x = (PairCode.prod v u next).eval x := by
        funext a b
        simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, PairCode.eval,Bool.and_comm (u.eval x a b) (v.eval x a b)]
      cases next <;> simpa [contract,contractSign,hu,hv,heq] using pivotPairSum v u hv _ x t
    have hU : u.quiet=true := by cases e : u.quiet <;> simp_all
    have hV : v.quiet=true := by cases e : v.quiet <;> simp_all
    cases next with
    | ret o =>
      simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, contract,contractSign,hu,hv,PairCode.eval,
        Paired.eval_quiet u x _ _ hU,Paired.eval_quiet v x _ _ hV]
      exact last_sum u.offset v.offset o x t
    | prod a b tail =>
      have hpart := ih (by simp [PairCode.cost]) (snoc x (u.offset.eval x &&& v.offset.eval x))
      simpa [contract,contractSign,hu,hv,Code.eval,PairCode.eval,
        Paired.eval_quiet u x _ _ hU,Paired.eval_quiet v x _ _ hV] using hpart


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape


def Paired.lit (v : Bool) : Paired n := ⟨false,false,.lit v⟩

def Paired.add (u v : Paired n) : Paired n :=
  ⟨u.coeffA ^^^ v.coeffA, u.coeffB ^^^ v.coeffB, .add u.offset v.offset⟩

def Paired.up (u : Paired n) : Paired (n+1) := ⟨u.coeffA,u.coeffB,u.offset.up⟩

@[simp] theorem Paired.eval_lit (x : Env n) (a b v : Bool) : (Paired.lit v).eval x a b=v := by
  simp [Paired.lit,Paired.eval,Aff.eval]

private theorem factor_xor (a b u v c d e f : Bool) :
    (((u ^^^ v) &&& a) ^^^ ((c ^^^ d) &&& b) ^^^ (e ^^^ f)) =
    (((u &&& a) ^^^ (c &&& b) ^^^ e) ^^^ ((v &&& a) ^^^ (d &&& b) ^^^ f)) := by
  cases a <;> cases b <;> cases u <;> cases v <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

@[simp] theorem Paired.eval_add (x : Env n) (a b : Bool) (u v : Paired n) :
    (u.add v).eval x a b = u.eval x a b ^^^ v.eval x a b := by
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Paired.add, Paired.eval, Aff.eval]
  exact factor_xor _ _ _ _ _ _ _ _

@[simp] theorem Paired.eval_up (x : Env n) (a b : Bool) (u : Paired n) (w : Bool) :
    u.up.eval (snoc x w) a b = u.eval x a b := by
  simp [Paired.up, Paired.eval]

def Aff.view (vars : Fin k → Paired n) : Aff k → Paired n
  | .lit v => .lit v
  | .var i => vars i
  | .add u v => (u.view vars).add (v.view vars)

@[simp] theorem Aff.eval_view (vars : Fin k → Paired n) (x : Env n) (a b : Bool) (u : Aff k) :
    (u.view vars).eval x a b = u.eval (fun i => (vars i).eval x a b) := by
  induction u <;> simp [Aff.view,Aff.eval, *]

def appendView (vars : Fin k → Paired n) (v : Paired n) : Fin (k+1) → Paired n :=
  Fin.lastCases v vars

@[simp] theorem appendView_eval (vars : Fin k → Paired n) (v : Paired n)
    (x : Env n) (a b : Bool) :
    (fun i => (appendView vars v i).eval x a b) =
      snoc (fun i => (vars i).eval x a b) (v.eval x a b) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendView,snoc]
  · simp [appendView,snoc]

def appendPaid (vars : Fin k → Paired n) : Fin (k+1) → Paired (n+1) :=
  appendView (fun i => (vars i).up) ⟨false,false,.var (Fin.last n)⟩

@[simp] theorem appendPaid_eval (vars : Fin k → Paired n) (x : Env n) (a b w : Bool) :
    (fun i => (appendPaid vars i).eval (snoc x w) a b) =
      snoc (fun i => (vars i).eval x a b) w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendPaid, appendView, Paired.eval, Aff.eval, snoc]
  · simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, appendPaid, appendView, Fin.lastCases_castSucc, snoc, Paired.eval_up]


def Code.reify : Code k → (Fin k → Paired n) → PairCode n
  | .ret v, vars => .ret (v.view vars)
  | .save v tail, vars => tail.reify (appendView vars (v.view vars))
  | .prod u v tail, vars => .prod (u.view vars) (v.view vars) (tail.reify (appendPaid vars))

theorem Code.cost_reify (p : Code k) (vars : Fin k → Paired n) :
    (p.reify vars).cost=p.cost := by
  induction p generalizing n <;> simp [Code.reify,Code.cost,PairCode.cost, *]

theorem Code.eval_reify (p : Code k) (vars : Fin k → Paired n)
    (x : Env n) (a b : Bool) :
    (p.reify vars).eval x a b = p.eval (fun i => (vars i).eval x a b) := by
  induction p generalizing n with
  | ret v => simp [Code.reify,PairCode.eval,Code.eval]
  | save v tail ih => simp [Code.reify,Code.eval,ih]
  | prod u v tail ih => simp [Code.reify,Code.eval,PairCode.eval,ih]

def lastTwo (n : Nat) : Fin (n+2) → Paired n :=
  appendView (appendView (fun i : Fin n => ⟨false,false,.var i⟩) ⟨true,false,.lit false⟩)
    ⟨false,true,.lit false⟩

@[simp] theorem lastTwo_eval (x : Env n) (a b : Bool) :
    (fun i => (lastTwo n i).eval x a b) = snoc (snoc x a) b := by
  rw [lastTwo, appendView_eval, appendView_eval]
  simp [Paired.eval,Aff.eval]

def Code.exposePair (p : Code (n+2)) : PairCode n := p.reify (lastTwo n)

theorem Code.cost_exposePair (p : Code (n+2)) : p.exposePair.cost=p.cost := by
  exact p.cost_reify _

theorem Code.eval_exposePair (p : Code (n+2)) (x : Env n) (a b : Bool) :
    p.exposePair.eval x a b = p.eval (snoc (snoc x a) b) := by
  simp [Code.exposePair,p.eval_reify]


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape
open PEqualNP.Outside.L_meta_29754.Phase


structure Sample (n : Nat) where
  x : Env n
  weight : Int
  target : Bool

def total {S : Type} (f : S → Int) : List S → Int
  | [] => 0
  | x::xs => f x + total f xs

def Sample.extend (x : Sample n) (a b : Bool) : Sample (n+2) :=
  ⟨snoc (snoc x.x a) b, x.weight, (a &&& b) ^^^ x.target⟩

noncomputable def spread (xs : List (Sample n)) : List (Sample (n+2)) :=
  xs.flatMap fun x => [x.extend false false, x.extend false true,
    x.extend true false, x.extend true true]

def score (p : Code n) (xs : List (Sample n)) : Int :=
  total (fun x => x.weight * phase (p.eval x.x ^^^ x.target)) xs

theorem total_append {S : Type} (f : S → Int) (xs ys : List S) :
    total f (xs++ys)=total f xs + total f ys := by
  induction xs <;> simp [total, Int.add_assoc, *]

theorem total_mul {S : Type} (f : S → Int) (c : Int) (xs : List S) :
    total (fun x => c * f x) xs = c * total f xs := by
  induction xs <;> simp [total, Int.mul_add, *]

theorem total_fold4 {S : Type} (f : S → Bool → Bool → Int) (xs : List S) :
    total (fun x => fold4 (f x)) xs = fold4 (fun a b => total (fun x => f x a b) xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, total]
    rw [ih]
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, fold4,fold2]
    omega

theorem score_spread (p : Code (n+2)) (xs : List (Sample n)) :
    score p (spread xs) = total (fun x => x.weight * fold4 (fun a b =>
      phase (p.exposePair.eval x.x a b ^^^ (a &&& b) ^^^ x.target))) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, score,spread,List.flatMap_cons,total_append,total, Sample.extend,
      Code.eval_exposePair, Bool.xor_assoc,fold4,fold2,Int.mul_add,Int.add_zero] at *
    omega

theorem score_contract (p : Code (n+2)) (hc : 0<p.cost) (xs : List (Sample n)) :
    score p (spread xs) = fold4 (fun i j =>
      contractSign p.exposePair i j * score (contract p.exposePair i j) xs) := by
  rw [score_spread]
  have hp : 0<p.exposePair.cost := by simpa [Code.cost_exposePair] using hc
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, contract_sum _ hp]
  have distribute (x : Sample n) :
      x.weight * fold4 (fun i j => contractSign p.exposePair i j *
        phase (Bool.xor ((contract p.exposePair i j).eval x.x) x.target)) =
      fold4 (fun i j => contractSign p.exposePair i j *
        (x.weight * phase (Bool.xor ((contract p.exposePair i j).eval x.x) x.target))) := by
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, fold4,fold2,Int.mul_add,Int.mul_left_comm x.weight]
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, distribute,total_fold4,total_mul,score]

theorem natAbs_fold4_le (f : Bool → Bool → Int)
    (m : Nat) (h : ∀ i j, (f i j).natAbs ≤ m) :
    (fold4 f).natAbs ≤ 4*m := by
  have h0 := h false false
  have h1 := h false true
  have h2 := h true false
  have h3 := h true true
  have a := Int.natAbs_add_le (f false false) (f false true)
  have b := Int.natAbs_add_le (f true false) (f true true)
  have c := Int.natAbs_add_le (f false false + f false true) (f true false + f true true)
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, fold4,fold2]
  omega

theorem score_contract_pick (p : Code (n+2)) (hc : 0<p.cost) (xs : List (Sample n)) :
    ∃ q : Code n, q.cost = p.cost-1 ∧
      (score p (spread xs)).natAbs ≤ 4*(score q xs).natAbs := by
  classical
  let scoreAbs := fun i j => (score (contract p.exposePair i j) xs).natAbs
  have mx : ∃ i j : Bool, ∀ a b : Bool, scoreAbs a b ≤ scoreAbs i j := by
    let c := fun i => if scoreAbs i false ≤ scoreAbs i true then true else false
    have hc : ∀ i j, scoreAbs i j ≤ scoreAbs i (c i) := by
      intro i j
      cases j <;> simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, c] <;> split <;> omega
    let d := if scoreAbs false (c false) ≤ scoreAbs true (c true) then true else false
    refine ⟨d,c d,?_⟩
    intro i j
    apply Nat.le_trans (hc i j)
    cases i <;> simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, d] <;> split <;> omega
  obtain ⟨i,j,h⟩ := mx
  refine ⟨contract p.exposePair i j, ?_, ?_⟩
  · rw [contract_cost,Code.cost_exposePair]
  · rw [score_contract p hc]
    apply natAbs_fold4_le
    intro a b
    rw [Int.natAbs_mul]
    rcases contract_sign p.exposePair a b with g|g <;> rw [g] <;> simpa using h a b

theorem score_gauss (p : Code (n+2)) (hc : p.cost=0) (xs : List (Sample n)) :
    ∃ q : Code n, q.cost=0 ∧ score p (spread xs) = 2*score q xs := by
  have h0 : p.exposePair.cost=0 := (Code.cost_exposePair p).trans hc
  cases he : p.exposePair with
  | prod a b next =>
    simp [he,PairCode.cost] at h0
  | ret out =>
    let q : Code n := .ret (.add out.offset (.lit (out.coeffA &&& out.coeffB)))
    refine ⟨q,rfl,?_⟩
    rw [score_spread]
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, he,PairCode.eval,Paired.eval,phase_regroup,gauss]
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, q,score,Code.eval,Aff.eval,swap_gauge,Int.mul_left_comm _ 2, total_mul]
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Bool.xor_comm (Bool.and out.coeffA out.coeffB)]


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape
open PEqualNP.Outside.L_meta_29754.Phase


abbrev dim (n : Nat) : Nat → Nat
  | 0 => n
  | r+1 => dim n r + 2

noncomputable def spreadMany {n : Nat} (xs : List (Sample n)) :
    (r : Nat) → List (Sample (dim n r))
  | 0 => xs
  | r+1 => spread (spreadMany xs r)

theorem dim_eq (n r : Nat) : dim n r = n+2*r := by
  induction r <;> simp [dim,Nat.mul_succ,Nat.add_assoc, *]

theorem pow_shift2 (d : Nat) : (2 : Nat)^(d+2) = 4*2^d := by
  rw [Nat.pow_succ,Nat.pow_succ]
  omega

theorem score_curve_upper (r : Nat) (p : Code (dim n r)) (xs : List (Sample n)) :
    ∃ q : Code n, q.cost = p.cost-r ∧
      (score p (spreadMany xs r)).natAbs ≤ 2^(r + min r p.cost) * (score q xs).natAbs := by
  induction r with
  | zero => exact ⟨p,rfl,by simp [spreadMany]⟩
  | succ r ih =>
    by_cases h : p.cost=0
    · obtain ⟨k,hk,hs⟩ := score_gauss p h (spreadMany xs r)
      obtain ⟨q,hq,hb⟩ := ih k
      refine ⟨q,by omega,?_⟩
      rw [spreadMany,hs,Int.natAbs_mul]
      simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, show (2 : Int).natAbs=2 from rfl,h,hk,Nat.min_zero,Nat.add_zero,
        Nat.pow_succ] at hb ⊢
      have hh := Nat.mul_le_mul_left 2 hb
      simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hh
    · have pos : 0<p.cost := by omega
      obtain ⟨k,hk,hs⟩ := score_contract_pick p pos (spreadMany xs r)
      obtain ⟨q,hq,hb⟩ := ih k
      refine ⟨q,by omega,?_⟩
      rw [spreadMany]
      apply Nat.le_trans hs
      have e : r+1+min (r+1) p.cost = (r+min r k.cost)+2 := by omega
      rw [e,pow_shift2,Nat.mul_assoc]
      exact Nat.mul_le_mul_left 4 hb


def pull (p : Code k) (rename : Fin k → Fin m) (add : Aff m) : Code m :=
  (p.reify (fun i => ⟨false,false,.var (rename i)⟩)).subst (.lit false) (.lit false) add

@[simp] theorem pull_cost (p : Code k) (rename : Fin k → Fin m) (add : Aff m) :
    (pull p rename add).cost=p.cost := by
  simp [pull,Code.cost_reify]

theorem pull_eval (p : Code k) (rename : Fin k → Fin m) (add : Aff m) (x : Env m) :
    (pull p rename add).eval x = p.eval (fun i => x (rename i)) ^^^ add.eval x := by
  simp [pull,PairCode.eval_subst,Code.eval_reify,Paired.eval,Aff.eval]

def liftPair (p : Code n) : Code (n+2) :=
  pull p (fun i => i.castSucc.castSucc) (.lit false)

def payPair (p : Code n) : Code (n+2) :=
  .prod (.var (Fin.last n).castSucc) (.var (Fin.last (n+1)))
    (pull p (fun i => i.castSucc.castSucc.castSucc) (.var (Fin.last (n+2))))

@[simp] theorem liftPair_cost (p : Code n) : (liftPair p).cost=p.cost := by
  simp [liftPair]

@[simp] theorem payPair_cost (p : Code n) : (payPair p).cost=p.cost+1 := by
  simp [payPair,Code.cost]

theorem liftPair_eval (p : Code n) (x : Env n) (a b : Bool) :
    (liftPair p).eval (snoc (snoc x a) b)=p.eval x := by
  simp [liftPair,pull_eval,Aff.eval,snoc]

theorem payPair_eval (p : Code n) (x : Env n) (a b : Bool) :
    (payPair p).eval (snoc (snoc x a) b)=p.eval x ^^^ (a &&& b) := by
  simp [payPair,Code.eval,pull_eval,Aff.eval,snoc]

theorem phase_cancel (a b t : Bool) : phase (Bool.xor (Bool.xor (Bool.xor a b) b) t)=phase (Bool.xor a t) := by
  cases a <;> cases b <;> cases t <;> decide

theorem expand_unpaid (p : Code n) (xs : List (Sample n)) :
    score (liftPair p) (spread xs) = 2*score p xs := by
  rw [score_spread]
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Code.eval_exposePair,liftPair_eval]
  have val (x : Sample n) :
      fold4 (fun a b => phase (Bool.xor (Bool.xor (p.eval x.x) (a && b)) x.target)) =
        2*phase (Bool.xor (p.eval x.x) x.target) := by
    have v := gauss false false (p.eval x.x ^^^ x.target)
    simpa [Bool.xor_assoc, Bool.xor_left_comm (p.eval x.x)] using v
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, val,score,Int.mul_left_comm _ 2,total_mul]

theorem expand_paid (p : Code n) (xs : List (Sample n)) :
    score (payPair p) (spread xs) = 4*score p xs := by
  rw [score_spread]
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Code.eval_exposePair,payPair_eval]
  have val (x : Sample n) :
      fold4 (fun a b => phase (Bool.xor (Bool.xor (Bool.xor (p.eval x.x) (a && b)) (a && b)) x.target)) =
        4*phase (Bool.xor (p.eval x.x) x.target) := by
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, phase_cancel, fold4,fold2]
    omega
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, val,score,Int.mul_left_comm _ 4,total_mul]

theorem score_curve_lower (r u : Nat) (hu : u≤r) (q : Code n) (xs : List (Sample n)) :
    ∃ p : Code (dim n r), p.cost=q.cost+u ∧
      (score p (spreadMany xs r)).natAbs = 2^(r+u)*(score q xs).natAbs := by
  induction r generalizing u with
  | zero =>
    have e : u=0 := by omega
    subst u
    exact ⟨q,rfl,by simp [spreadMany]⟩
  | succ r ih =>
    cases u with
    | zero =>
      obtain ⟨p,hp,e⟩ := ih 0 (Nat.zero_le _)
      refine ⟨liftPair p,by simpa using hp,?_⟩
      rw [spreadMany,expand_unpaid,Int.natAbs_mul,e]
      simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, show (2 : Int).natAbs=2 from rfl,Nat.add_zero,Nat.pow_succ]
      simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    | succ u =>
      obtain ⟨p,hp,e⟩ := ih u (by omega)
      refine ⟨payPair p,by simp [hp,Nat.add_assoc],?_⟩
      rw [spreadMany,expand_paid,Int.natAbs_mul,e,
        show r+1+(u+1) = (r+u)+2 by omega,pow_shift2,Nat.mul_assoc]
      rfl


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape


inductive Prim : Nat → Type
  | trueGate : Prim n
  | neg : Fin n → Prim n
  | xnor : Fin n → Fin n → Prim n
  | prod : Fin n → Fin n → Prim n

def Prim.eval (x : Env n) : Prim n → Bool
  | .trueGate => true
  | .neg i => !x i
  | .xnor i j => !(x i ^^^ x j)
  | .prod i j => x i &&& x j

def Prim.cost : Prim n → Nat
  | .prod _ _ => 1
  | _ => 0

inductive Micro : Nat → Type
  | out : Fin n → Micro n
  | step : Prim n → Micro (n+1) → Micro n

def Micro.eval : Micro n → Env n → Bool
  | .out i, x => x i
  | .step g tail, x => tail.eval (snoc x (g.eval x))

def Micro.cost : Micro n → Nat
  | .out _ => 0
  | .step g tail => g.cost + tail.cost

abbrev Kont (n : Nat) := ∀ m, (Fin n → Fin m) → Fin m → Micro m

def emitAffine : Aff k → (Fin k → Fin n) → Kont n → Micro n
  | .var i, ren, k => k n id (ren i)
  | .lit true, _, k => .step .trueGate (k (n+1) Fin.castSucc (Fin.last n))
  | .lit false, _, k => .step .trueGate (.step (.neg (Fin.last n))
    (k ((n+1)+1) (fun i => i.castSucc.castSucc) (Fin.last (n+1))))
  | .add u v, ren, k => emitAffine u ren (fun _ f l =>
    emitAffine v (fun i => f (ren i)) (fun m g r =>
      .step (.xnor (g l) r) (.step (.neg (Fin.last m))
        (k (m+2) (fun i => (g (f i)).castSucc.castSucc) (Fin.last (m+1))))))

theorem emit_affine_cost (e : Aff k) (ren : Fin k → Fin n) (k : Kont n) (c : Nat)
    (hk : ∀ m f i, (k m f i).cost=c) : (emitAffine e ren k).cost=c := by
  induction e generalizing n with
  | var i => exact hk _ _ _
  | lit b => cases b <;> simp [emitAffine,Micro.cost,Prim.cost,hk]
  | add u v iu iv =>
    rw [emitAffine]
    apply iu
    intro m f l
    apply iv
    intro p g r
    simp [Micro.cost,Prim.cost,hk]

theorem emit_affine_eval (e : Aff k) (ren : Fin k → Fin n) (k : Kont n)
    (spec : Env n → Bool → Bool) (x : Env n)
    (hk : ∀ m f v (y : Env m), (k m f v).eval y = spec (y ∘ f) (y v)) :
    (emitAffine e ren k).eval x = spec x (e.eval (x ∘ ren)) := by
  induction e generalizing n with
  | var i =>
    simpa [emitAffine,Aff.eval] using hk n id (ren i) x
  | lit b =>
    cases b <;> simp [emitAffine,Micro.eval,Prim.eval,hk,snoc,Aff.eval,Function.comp_def]
  | add u v iu iv =>
    rw [emitAffine]
    let uSpec : Env n → Bool → Bool := fun z uval => spec z (uval ^^^ (v.eval (z ∘ ren)))
    refine (iu ren _ uSpec x ?_).trans (by rfl)
    intro m f l y
    let vSpec : Env m → Bool → Bool := fun z vval => spec (z ∘ f) ((z l) ^^^ vval)
    refine (iv (fun i => f (ren i)) _ vSpec y ?_).trans (by rfl)
    intro p g r z
    simp [vSpec,Micro.eval,Prim.eval,hk,snoc,Function.comp_def]

def graft (ren : Fin k → Fin n) (v : Fin n) : Fin (k+1) → Fin n :=
  Fin.lastCases v ren

theorem graft_eval (ren : Fin k → Fin n) (v : Fin n) (x : Env n) :
    (x ∘ graft ren v) = snoc (x ∘ ren) (x v) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [graft,snoc]

def Code.emit : Code k → (Fin k → Fin n) → Micro n
  | .ret v, ren => emitAffine v ren (fun _ _ v => .out v)
  | .save v tail, ren => emitAffine v ren (fun _ f u => tail.emit (graft (f ∘ ren) u))
  | .prod u v tail, ren => emitAffine u ren (fun _ f l =>
    emitAffine v (f ∘ ren) (fun m g r =>
      .step (.prod (g l) r)
        (tail.emit (graft (fun i => (g (f (ren i))).castSucc) (Fin.last m)))))

theorem Code.cost_emit (p : Code k) (ren : Fin k → Fin n) :
    (p.emit ren).cost=p.cost := by
  induction p generalizing n with
  | ret v =>
    rw [Code.emit]
    apply emit_affine_cost
    intro m f u
    rfl
  | save v tail ih =>
    rw [Code.emit]
    apply emit_affine_cost
    intro m f u
    exact ih _
  | prod u v tail ih =>
    rw [Code.emit]
    apply emit_affine_cost
    intro m f l
    apply emit_affine_cost
    intro p g r
    simp [Micro.cost,Prim.cost,Code.cost,ih,Nat.add_comm]

theorem Code.eval_emit (p : Code k) (ren : Fin k → Fin n) (x : Env n) :
    (p.emit ren).eval x = p.eval (x ∘ ren) := by
  induction p generalizing n with
  | ret u =>
    rw [Code.emit]
    exact emit_affine_eval u ren _ (fun _ a => a) x (by intros; rfl)
  | save u tail ih =>
    rw [Code.emit]
    exact emit_affine_eval u ren _ (fun z a => tail.eval (snoc (z ∘ ren) a)) x
      (by intro m f val y; rw [ih,graft_eval]; rfl)
  | prod u v tail ih =>
    rw [Code.emit]
    let uSpec : Env n → Bool → Bool := fun z a => tail.eval (snoc (z ∘ ren) (a &&& v.eval (z ∘ ren)))
    refine (emit_affine_eval u ren _ uSpec x ?_).trans (by rfl)
    intro m f l y
    let vSpec : Env m → Bool → Bool := fun z b => tail.eval (snoc ((z ∘ f) ∘ ren) (z l &&& b))
    refine (emit_affine_eval v (f ∘ ren) _ vSpec y ?_).trans (by rfl)
    intro p g r z
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, vSpec,Micro.eval,Prim.eval,ih,graft_eval]
    simp [snoc,Function.comp_def]


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape



inductive RawOp where
  | and | or | not | mod2
deriving DecidableEq

def RawOp.compute : RawOp → List Bool → Bool
  | .and, xs => xs.all id
  | .or, xs => xs.any id
  | .not, xs => !(xs.headD false)
  | .mod2, xs => decide (xs.count true % 2 = 0)

structure RawGate where
  op : RawOp
  inputs : List Nat

def RawGate.eval (w : List Bool) (g : RawGate) : Bool :=
  g.op.compute (g.inputs.map fun i => w.getD i false)

def RawGate.cost (g : RawGate) : Nat :=
  if (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2 then 1 else 0

def RawGate.safe (n : Nat) (g : RawGate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op=.not → g.inputs.length=1) ∧ ∀ i ∈ g.inputs, i<n

def safeList : Nat → List RawGate → Prop
  | _, [] => True
  | n, g::gs => g.safe n ∧ safeList (n+1) gs

def rawCost : List RawGate → Nat
  | [] => 0
  | g::gs => g.cost + rawCost gs

def rawEval (w : List Bool) (gates : List RawGate) (output : Nat) : Bool :=
  (gates.foldl (fun v g => v++[g.eval v]) w).getD output false

def Prim.lower : Prim n → RawGate
  | .trueGate => ⟨.mod2,[]⟩
  | .neg i => ⟨.not,[i.val]⟩
  | .xnor i j => ⟨.mod2,[i.val,j.val]⟩
  | .prod i j => ⟨.and,[i.val,j.val]⟩

def Micro.gates : Micro n → List RawGate
  | .out _ => []
  | .step g tail => g.lower :: tail.gates

def Micro.output : Micro n → Nat
  | .out i => i.val
  | .step _ tail => tail.output

theorem Prim.lower_safe (p : Prim n) : p.lower.safe n := by
  cases p with
  | trueGate => simp [Prim.lower,RawGate.safe]
  | neg i => simp [Prim.lower,RawGate.safe,i.isLt]
  | xnor i j =>
    simp [Prim.lower,RawGate.safe]
  | prod i j =>
    simp [Prim.lower,RawGate.safe]

theorem Prim.lower_cost (p : Prim n) : p.lower.cost=p.cost := by
  cases p <;> simp [Prim.lower,Prim.cost,RawGate.cost]

theorem getD_env (x : Env n) (i : Fin n) :
    (List.ofFn x).getD i.val false=x i := by
  have h : i.val < (List.ofFn x).length := by simp
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some,List.getElem_ofFn]

theorem list_snoc (x : Env n) (v : Bool) :
    List.ofFn (snoc x v) = List.ofFn x ++ [v] := by
  rw [List.ofFn_succ_last]
  simp [snoc]

theorem mod2_two (a b : Bool) :
    RawOp.compute .mod2 [a,b] = !(a ^^^ b) := by
  cases a <;> cases b <;> decide

theorem Prim.lower_eval (p : Prim n) (x : Env n) :
    p.lower.eval (List.ofFn x)=p.eval x := by
  cases p <;> simp [Prim.lower,Prim.eval,RawGate.eval,RawOp.compute]
  exact mod2_two _ _

theorem Micro.safe_gates (p : Micro n) : safeList n p.gates := by
  induction p with
  | out i => trivial
  | step g tail ih =>
    exact ⟨g.lower_safe,ih⟩

theorem Micro.cost_gates (p : Micro n) : rawCost p.gates=p.cost := by
  induction p <;> simp [Micro.gates,Micro.cost,rawCost,Prim.lower_cost, *]

theorem Micro.eval_gates (p : Micro n) (x : Env n) :
    rawEval (List.ofFn x) p.gates p.output = p.eval x := by
  induction p with
  | out i => exact getD_env x i
  | step g tail ih =>
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Micro.gates,Micro.output,Micro.eval,rawEval,List.foldl_cons,Prim.lower_eval]
    rw [← list_snoc]
    exact ih _


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape


def Code.feed (tail : Code k) (ρ : Fin k → Aff n) : Code n :=
  (tail.reify (fun i => ⟨false,false,ρ i⟩)).subst (.lit false) (.lit false) (.lit false)

theorem Code.feed_cost (tail : Code k) (ρ : Fin k → Aff n) : (tail.feed ρ).cost=tail.cost := by
  simp [Code.feed,Code.cost_reify]

theorem Code.feed_eval (tail : Code k) (ρ : Fin k → Aff n) (x : Env n) :
    (tail.feed ρ).eval x = tail.eval (fun i => (ρ i).eval x) := by
  simp [Code.feed,PairCode.eval_subst,Code.eval_reify,Paired.eval,Aff.eval]

def pin (n i : Nat) : Aff n :=
  if h : i<n then .var ⟨i,h⟩ else .lit false

theorem pin_eval (n i : Nat) (x : Env n) :
    (pin n i).eval x = (List.ofFn x).getD i false := by
  unfold pin
  split
  · rename_i h
    exact (getD_env x ⟨i,h⟩).symm
  · rename_i h
    have g : i ≥ (List.ofFn x).length := by simp; omega
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Aff.eval,List.getD_eq_getElem?_getD,List.getElem?_eq_none g,Option.getD_none]

def xorAff (a b : Aff n) : Aff n := .add a b

def notAff (a : Aff n) : Aff n := .add (.lit true) a

def orD (a b : Aff n) (tail : Code (n+1)) : Code n :=
  .prod a b (tail.feed (Fin.lastCases (xorAff (xorAff a.up b.up) (.var (Fin.last n)))
    (fun i => .var i.castSucc)))

theorem orD_cost (a b : Aff n) (tail : Code (n+1)) :
    (orD a b tail).cost=1+tail.cost := by
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, orD,Code.cost,Code.feed_cost,Nat.add_comm]

theorem orD_eval (a b : Aff n) (tail : Code (n+1)) (x : Env n) :
    (orD a b tail).eval x = tail.eval (snoc x (a.eval x || b.eval x)) := by
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, orD,Code.eval,Code.feed_eval]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Fin.lastCases_last,xorAff,Aff.eval,Aff.eval_up,snoc,PEqualNP.Outside.L_meta_29754.Phase.paidOr]
  · simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Fin.lastCases_castSucc,Aff.eval,snoc]


def decGate (g : RawGate) (tail : Code (n+1)) : Code n :=
  match g.op, g.inputs with
  | .and, [] => .save (.lit true) tail
  | .and, [a] => .save (pin n a) tail
  | .and, [a,b] => .prod (pin n a) (pin n b) tail
  | .or, [] => .save (.lit false) tail
  | .or, [a] => .save (pin n a) tail
  | .or, [a,b] => orD (pin n a) (pin n b) tail
  | .not, [] => .save (.lit true) tail
  | .not, a::_ => .save (notAff (pin n a)) tail
  | .mod2, [] => .save (.lit true) tail
  | .mod2, [a] => .save (notAff (pin n a)) tail
  | .mod2, [a,b] => .save (notAff (xorAff (pin n a) (pin n b))) tail
  | _, _ => .save (.lit false) tail

theorem decGate_cost (g : RawGate) (tail : Code (n+1)) (good : g.inputs.length ≤ 2) :
    (decGate g tail).cost=g.cost+tail.cost := by
  rcases g with ⟨op,inputs⟩
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · cases op <;> simp [decGate,Code.cost,RawGate.cost]
  · cases op <;> simp [decGate,Code.cost,RawGate.cost]
  · cases op <;> simp [decGate,Code.cost,RawGate.cost,orD_cost,Nat.add_comm]
  · simp at good <;> omega

theorem notAff_eval (a : Aff n) (x : Env n) : (notAff a).eval x = !(a.eval x) := by
  simp [notAff,Aff.eval]

theorem mod2_one (a : Bool) : RawOp.compute .mod2 [a] = !a := by
  cases a <;> decide

theorem decGate_eval (g : RawGate) (tail : Code (n+1)) (good : g.inputs.length ≤ 2) (x : Env n) :
    (decGate g tail).eval x = tail.eval (snoc x (g.eval (List.ofFn x))) := by
  rcases g with ⟨op,inputs⟩
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · cases op <;> simp [decGate,Code.eval,RawOp.compute,RawGate.eval,Aff.eval]
  · cases op <;> simp [decGate,Code.eval,RawOp.compute,RawGate.eval,pin_eval,notAff_eval]
    exact congrArg (fun v => tail.eval (snoc x v)) (mod2_one _).symm
  · cases op <;> simp [decGate,Code.eval,RawOp.compute,RawGate.eval,Aff.eval,pin_eval,notAff_eval,xorAff,orD_eval]
    exact congrArg (fun v => tail.eval (snoc x v)) (mod2_two _ _).symm
  · simp at good <;> omega

def decode : (n : Nat) → List RawGate → Nat → Code n
  | n, [], output => .ret (pin n output)
  | n, g::gs, output => decGate g (decode (n+1) gs output)

theorem decode_eval (n : Nat) (gs : List RawGate) (out : Nat)
    (arity : ∀ g ∈ gs, g.inputs.length≤2) (x : Env n) :
    (decode n gs out).eval x = rawEval (List.ofFn x) gs out := by
  induction gs generalizing n with
  | nil => exact pin_eval n out x
  | cons g gs ih =>
    have arity' : ∀ h ∈ gs, h.inputs.length ≤ 2 := fun h hm => arity h (List.mem_cons_of_mem _ hm)
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, decode,decGate_eval g _ (arity g List.mem_cons_self),ih _ arity',rawEval,List.foldl_cons,list_snoc]

theorem decode_cost (n : Nat) (gs : List RawGate) (out : Nat) (arity : ∀ g ∈ gs, g.inputs.length≤2) :
    (decode n gs out).cost=rawCost gs := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    have arity' : ∀ h ∈ gs, h.inputs.length ≤ 2 := fun h hm => arity h (List.mem_cons_of_mem _ hm)
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, decode,decGate_cost g _ (arity g List.mem_cons_self),ih _ arity',rawCost]


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape

theorem safe_get (gs : List RawGate) (n j : Nat) (h : j<gs.length) (S : safeList n gs) :
    (gs[j]'h).safe (n+j) := by
  induction gs generalizing n j with
  | nil => simp at h
  | cons g gs ih =>
    cases j with
    | zero => simpa using S.1
    | succ j =>
      have h' : j<gs.length := by simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, List.length_cons] at h; omega
      have e : n+1+j = n+(j+1) := by omega
      simpa [e] using ih (n+1) j h' S.2

theorem safe_arities (gs : List RawGate) (n : Nat) (S : safeList n gs) :
    ∀ g ∈ gs, g.inputs.length≤2 := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact S.1.1
    · exact ih _ S.2 _ hu

theorem safe_getD (gs : List RawGate) (n j : Nat) (h : j<gs.length)
    (S : safeList n gs) (d : RawGate) :
    (gs.getD j d).safe (n+j) := by
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  exact safe_get gs n j h S


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape
open PEqualNP.Outside.L_meta_29754.Phase



def nested (n : Nat) : (r : Nat) → (Env (dim n r) → Bool → Int) → Env n → Bool → Int
  | 0,f,x,t => f x t
  | r+1,f,x,t => nested n r
    (fun y u => fold4 (fun a b => f (snoc (snoc y a) b) ((a &&& b) ^^^ u))) x t

theorem total_spread (xs : List (Sample n)) (f : Env (n+2) → Bool → Int) :
    total (fun x => x.weight*f x.x x.target) (spread xs) =
      total (fun x => x.weight * fold4 (fun a b =>
        f (snoc (snoc x.x a) b) ((a &&& b) ^^^ x.target))) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, spread,List.flatMap_cons,total_append,total,Sample.extend,fold4,fold2,
      Int.mul_add,Int.add_zero] at *
    omega

theorem total_spreadMany (r : Nat) (xs : List (Sample n)) (f : Env (dim n r) → Bool → Int) :
    total (fun x => x.weight*f x.x x.target) (spreadMany xs r) =
      total (fun x => x.weight*nested n r f x.x x.target) xs := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [spreadMany,total_spread]
    exact ih (fun y u => fold4 (fun a b => f (snoc (snoc y a) b) ((a &&& b) ^^^ u)))

theorem score_spreadMany_eq_nested (r : Nat) (p : Code (dim n r)) (xs : List (Sample n)) :
    score p (spreadMany xs r) =
      total (fun x => x.weight*nested n r (fun y t => phase (p.eval y ^^^ t)) x.x x.target) xs :=
  total_spreadMany r xs (fun y t => phase (p.eval y ^^^ t))

theorem total_map {A B : Type} (l : List A) (p : A → B) (f : B → Int) :
    total f (l.map p) = total (f ∘ p) l := by
  induction l <;> simp [total, *]

theorem total_flatMap {A B : Type} (l : List A) (p : A → List B) (f : B → Int) :
    total f (l.flatMap p) = total (fun a => total f (p a)) l := by
  induction l <;> simp [total,total_append, *]


end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Tape
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def tag (g : RawOp) : GateOp :=
  match g with
  | .and => .and
  | .or => .or
  | .not => .not
  | .mod2 => .mod 2

def tagIn (g : GateOp) : RawOp :=
  match g with
  | .and => .and
  | .or => .or
  | .not => .not
  | .mod _ => .mod2
  | .maj => .or

def gateOut (g : RawGate) : Gate := ⟨tag g.op,g.inputs⟩
def gateIn (g : Gate) : RawGate := ⟨tagIn g.op,g.inputs⟩

def basisOK (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length=1)

def legal (n : Nat) (C : Circuit) : Prop :=
  ReadsBack n C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧ basisOK g

noncomputable def paid (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2) (Classical.propDecidable _)

noncomputable def projectCost (C : Circuit) : Nat := C.gates.countP paid

theorem gateIn_out (g : Gate) (h : basisOK g) : gateOut (gateIn g)=g := by
  rcases g with ⟨op,inputs⟩
  rcases h with e | e | e | ⟨e,_⟩ <;>
    change op = _ at e <;> subst op <;> rfl

theorem gateOut_in (g : RawGate) : gateIn (gateOut g)=g := by
  cases g with | mk op i => cases op <;> rfl

theorem tag_eval (g : RawOp) (x : List Bool) : (tag g).eval x = g.compute x := by
  cases g <;> rfl

theorem gateOut_paid (g : RawGate) : (paid (gateOut g)).toNat = g.cost := by
  classical
  rcases g with ⟨op,inputs⟩
  cases op <;> by_cases h : inputs.length = 2 <;>
    simp [paid,gateOut,tag,RawGate.cost,h]

theorem gates_eval (gs : List RawGate) (x : List Bool) (o : Nat) :
    (⟨gs.map gateOut,o⟩ : Circuit).eval x = rawEval x gs o := by
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Circuit.eval,Circuit.wires,rawEval,List.foldl_map]
  congr 2
  funext w g
  simp [gateOut,RawGate.eval,tag_eval]

theorem gates_cost (gs : List RawGate) (out : Nat) :
    projectCost (⟨gs.map gateOut,out⟩ : Circuit) = rawCost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, projectCost,List.map_cons,List.countP_cons,rawCost] at *
    rw [← gateOut_paid g, ← ih]
    cases paid (gateOut g) <;> simp [Nat.add_comm]


theorem safe_tags (gs : List RawGate) (n : Nat) (S : safeList n gs) :
    ∀ g ∈ gs, g.op=.not → g.inputs.length=1 := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    intro u hu he
    rcases List.mem_cons.mp hu with rfl|hu
    · exact S.1.2.1 he
    · exact ih _ S.2 _ hu he

theorem gates_legal (gs : List RawGate) (n o : Nat) (safe : safeList n gs) :
    legal n ⟨gs.map gateOut,o⟩ := by
  refine ⟨?_,?_⟩
  · intro j hj i hi
    have h : j<gs.length := by simpa using hj
    have p := safe_get gs n j h safe
    apply p.2.2 i
    have h' : j<(gs.map gateOut).length := by simpa using h
    simpa only [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h',
      Option.getD_some,List.getElem_map,gateOut] using hi
  · intro g hg
    rcases List.mem_map.mp hg with ⟨raw,hr,rfl⟩
    refine ⟨safe_arities gs n safe raw hr,?_⟩
    have hn := safe_tags gs n safe raw hr
    cases e : raw.op <;> simp [gateOut,tag,basisOK,e]
    exact hn e

theorem map_invol (C : Circuit) (n : Nat) (ok : legal n C) : (C.gates.map gateIn).map gateOut=C.gates := by
  rw [List.map_map]
  exact List.map_congr_left (fun g hg => gateIn_out g (ok.2 g hg).2) |>.trans (by simp)

theorem import_arity (C : Circuit) (n : Nat) (ok : legal n C) :
    ∀ g ∈ C.gates.map gateIn, g.inputs.length≤2 := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨h,hh,rfl⟩
  exact (ok.2 h hh).1

theorem import_eval (C : Circuit) (n : Nat) (ok : legal n C) (x : Env n) :
    (decode n (C.gates.map gateIn) C.output).eval x = C.eval (List.ofFn x) := by
  rw [decode_eval _ _ _ (import_arity C n ok), ← gates_eval, map_invol C n ok]

theorem import_cost (C : Circuit) (n : Nat) (ok : legal n C) :
    (decode n (C.gates.map gateIn) C.output).cost = projectCost C := by
  rw [decode_cost _ _ _ (import_arity C n ok), ← gates_cost _ C.output, map_invol C n ok]

def exportTape (p : Code n) : Circuit :=
  let tape := p.emit id
  ⟨tape.gates.map gateOut,tape.output⟩

theorem export_legal (p : Code n) : legal n (exportTape p) := by
  exact gates_legal _ _ _ (Micro.safe_gates _)

theorem export_eval (p : Code n) (x : Env n) : (exportTape p).eval (List.ofFn x) = p.eval x := by
  rw [exportTape,gates_eval,Micro.eval_gates,Code.eval_emit]
  rfl

theorem export_cost (p : Code n) : projectCost (exportTape p) = p.cost := by
  rw [exportTape,gates_cost,Micro.cost_gates,Code.cost_emit]

end PEqualNP.Outside.L_meta_29754.Tape

namespace PEqualNP.Outside.L_meta_29754.Geometry

open scoped BigOperators
abbrev F := ZMod 2
abbrev V (n : Nat) := Fin n → F

lemma f2_add_self {U : Type*} [AddCommGroup U] [Module F U] (u : U) : u+u=0 := by
  calc
    u+u = ((1 : F)+1) • u := by rw [add_smul,one_smul]
    _ = 0 := by rw [show (1 : F)+1=0 by decide,zero_smul]

lemma f2_nonzero_one (u : F) (h : u≠0) : u=1 := by
  have h' : u.val<2 := ZMod.val_lt u
  have he : u.val=0 ∨ u.val=1 := by omega
  rcases he with he|he
  · exact (h ((ZMod.val_eq_zero u).mp he)).elim
  · calc
      u = (u.val : F) := (ZMod.natCast_zmod_val u).symm
      _ = 1 := by rw [he,Nat.cast_one]

def pol (M : Matrix (Fin n) (Fin n) F) : V n →ₗ[F] V n →ₗ[F] F :=
  (dotProductBilin F F).compl₂ M.mulVecLin

lemma pol_apply (M : Matrix (Fin n) (Fin n) F) (x y : V n) :
    pol M x y=dotProduct x (M.mulVec y) := rfl

lemma pol_symm (M : Matrix (Fin n) (Fin n) F) (Q : V n → F)
    (h : ∀ x y : V n, Q (x+y)+Q x+Q y+Q 0 = dotProduct x (M.mulVec y)) :
    ∀ x y, pol M x y=pol M y x := by
  intro x y
  rw [pol_apply,pol_apply,← h x y,← h y x]
  ac_rfl

lemma pol_alt (M : Matrix (Fin n) (Fin n) F) (Q : V n → F)
    (h : ∀ x y : V n, Q (x+y)+Q x+Q y+Q 0 = dotProduct x (M.mulVec y)) :
    ∀ x, pol M x x=0 := by
  intro x
  rw [pol_apply, ← h x x, f2_add_self x]
  calc
    Q 0 + Q x + Q x + Q 0 = (Q 0+Q 0)+(Q x+Q x) := by ac_rfl
    _ = 0 := by rw [f2_add_self (Q 0),f2_add_self (Q x),add_zero]

abbrev rad (M : Matrix (Fin n) (Fin n) F) := LinearMap.ker M.mulVecLin

lemma rad_right (M : Matrix (Fin n) (Fin n) F) {y : V n} (hy : y ∈ rad M) (x : V n) :
    pol M x y=0 := by
  have eq : M.mulVec y = 0 := LinearMap.mem_ker.mp hy
  rw [pol_apply,eq,dotProduct_zero]

lemma rad_iff (M : Matrix (Fin n) (Fin n) F) (y : V n) :
    (∀ x, pol M x y=0) ↔ y ∈ rad M := by
  refine ⟨?_, fun h x => rad_right M h x⟩
  intro h
  apply LinearMap.mem_ker.mpr
  ext i
  change M.mulVec y i = (0:F)
  specialize h (Pi.single i 1)
  simpa only [pol_apply,single_dotProduct,one_mul,Pi.zero_apply] using h

lemma rad_dim (M : Matrix (Fin n) (Fin n) F) (h : M.rank=2*r) :
    Module.finrank F (rad M)=n-2*r := by
  have eq := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + Module.finrank F (rad M) = Module.finrank F (V n) at eq
  rw [h,Module.finrank_fin_fun] at eq
  omega

def dotH (H : Submodule F (V n)) : V n →ₗ[F] H →ₗ[F] F :=
  (dotProductBilin F F).flip.compl₂ H.subtype

def polarOn (M : Matrix (Fin n) (Fin n) F) (H : Submodule F (V n)) :
    H →ₗ[F] H →ₗ[F] F := (dotH H).comp (M.mulVecLin.comp H.subtype)

lemma polarOn_apply (M : Matrix (Fin n) (Fin n) F) (H : Submodule F (V n)) (h x : H) :
    polarOn M H h x = pol M (x : V n) (h : V n) := rfl

lemma polarOn_inj (M : Matrix (Fin n) (Fin n) F) (H : Submodule F (V n))
    (hcompl : IsCompl (rad M) H) (sym : ∀ x y, pol M x y=pol M y x) :
    Function.Injective (polarOn M H) := by
  apply LinearMap.ker_eq_bot.mp
  rw [eq_bot_iff]
  intro y hy
  have hyK : (y : V n) ∈ rad M := by
    apply (rad_iff M y).mp
    intro x
    obtain ⟨k,h,hx,_⟩ := Submodule.existsUnique_add_of_isCompl hcompl x
    rw [← hx, map_add, LinearMap.add_apply]
    have zero : polarOn M H y = 0 := LinearMap.mem_ker.mp hy
    have zh := congrArg (fun f : H →ₗ[F] F => f h) zero
    change pol M (h : V n) (y : V n)=0 at zh
    rw [sym (k : V n) (y : V n),rad_right M k.property _,zh,add_zero]
  have hbot : (y : V n) ∈ (⊥ : Submodule F (V n)) := by
    rw [← hcompl.inf_eq_bot]
    exact ⟨hyK,y.property⟩
  have yz : (y : V n) = 0 := by simpa using hbot
  have he : y=0 := Subtype.ext yz
  simpa [he]

noncomputable def addr (M : Matrix (Fin n) (Fin n) F) (H : Submodule F (V n))
    (L : V t →ₗ[F] V n) (hinj : Function.Injective (polarOn M H)) :
    V t →ₗ[F] H :=
  let e := (polarOn M H).linearEquivOfInjective hinj Subspace.dual_finrank_eq.symm
  e.symm.toLinearMap.comp ((dotH H).comp L)

lemma addr_spec (M : Matrix (Fin n) (Fin n) F) (H : Submodule F (V n))
    (L : V t →ₗ[F] V n) (hinj : Function.Injective (polarOn M H))
    (z : V t) (x : H) :
    dotProduct (x : V n) (M.mulVec (addr M H L hinj z : V n)) = dotProduct (x : V n) (L z) := by
  change polarOn M H (addr M H L hinj z) x = dotH H (L z) x
  let e := (polarOn M H).linearEquivOfInjective hinj Subspace.dual_finrank_eq.symm
  change e (e.symm (dotH H (L z))) x = _
  rw [e.apply_symm_apply]

end PEqualNP.Outside.L_meta_29754.Geometry

namespace PEqualNP.Outside.L_meta_29754.Geometry
open scoped BigOperators

abbrev Bil (W : Type*) [AddCommGroup W] [Module F W] := W →ₗ[F] W →ₗ[F] F

lemma polar_norm {W : Type*} [AddCommGroup W] [Module F W] (Q : W → F) (B : Bil W)
    (hQ : ∀ x y : W, Q (x+y)+Q x+Q y+Q 0 = B x y) :
    ∀ x y : W, Q (x+y)+Q 0 = (Q x + Q 0)+(Q y+Q 0)+B x y := by
  intro x y
  rw [← hQ x y]
  have hx := f2_add_self (Q x)
  have hy := f2_add_self (Q y)
  have h0 := f2_add_self (Q 0)
  calc Q (x+y) + Q 0 = Q (x+y) + Q 0 + ((Q x+Q x)+(Q y+Q y)+(Q 0+Q 0)) := by simp [hx,hy,h0]
       _ = (Q x+Q 0)+(Q y+Q 0)+(Q (x+y)+Q x+Q y+Q 0) := by ac_rfl

lemma norm_smul {W : Type*} [AddCommGroup W] [Module F W]
    (q : W → F) (q0 : q 0=0) (a : F) (x : W) :
    q (a • x)=a*q x := by
  by_cases h : a=0
  · simp [h,q0]
  · simp [f2_nonzero_one a h]

section Pair
variable {W : Type*} [AddCommGroup W] [Module F W]

def pairedPlane (B : Bil W) (e f : W) : Submodule F W := (B e).ker ⊓ (B f).ker

lemma zero_e (B : Bil W) (e f : W) (u : pairedPlane B e f) : B e u=0 :=
  LinearMap.mem_ker.mp u.property.1
lemma zero_f (B : Bil W) (e f : W) (u : pairedPlane B e f) : B f u=0 :=
  LinearMap.mem_ker.mp u.property.2

def pairProj (B : Bil W) (e f : W) : W →ₗ[F] W :=
  LinearMap.id - (B f).smulRight e - (B e).smulRight f

lemma pairProj_mem (B : Bil W) (e f x : W)
    (ee : B e e=0) (ff : B f f=0) (ef : B e f=1) (fe : B f e=1) :
    pairProj B e f x ∈ pairedPlane B e f := by
  change pairProj B e f x ∈ (B e).ker ∧ pairProj B e f x ∈ (B f).ker
  constructor <;> apply LinearMap.mem_ker.mpr <;> simp [pairProj,ee,ff,ef,fe,smul_eq_mul]

def pairSlice (B : Bil W) (e f : W)
    (ee : B e e=0) (ff : B f f=0) (ef : B e f=1) (fe : B f e=1) :
    (pairedPlane B e f × (F × F)) ≃ₗ[F] W where
  toFun p := (p.1 : W) + p.2.1 • e + p.2.2 • f
  map_add' p q := by
    change ((p.1 + q.1 : pairedPlane B e f) : W) + (p.2.1+q.2.1) • e + (p.2.2+q.2.2) • f = _
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, Submodule.coe_add,add_smul]
    abel
  map_smul' a p := by
    change ((a • p.1 : pairedPlane B e f) : W) + (a*p.2.1) • e + (a*p.2.2) • f = _
    simp [smul_add,mul_smul]
  invFun x := (⟨pairProj B e f x,pairProj_mem B e f x ee ff ef fe⟩,(B f x,B e x))
  left_inv p := by
    rcases p with ⟨u,a,b⟩
    have uE := zero_e B e f u
    have uF := zero_f B e f u
    have evalE : B e ((u : W)+a • e+b • f)=b := by simp [uE,ee,ef,smul_eq_mul]
    have evalF : B f ((u : W)+a • e+b • f)=a := by simp [uF,fe,ff,smul_eq_mul]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext evalF evalE)
    change pairProj B e f ((u : W)+a • e+b • f) = (u : W)
    simp [pairProj,evalE,evalF] <;> abel
  right_inv x := by
    change pairProj B e f x + B f x • e + B e x • f = x
    simp [pairProj]
    abel

def restrictPair (B : Bil W) (e f : W) : Bil (pairedPlane B e f) where
  toFun x := (B x).comp (pairedPlane B e f).subtype
  map_add' x y := by ext z; simp
  map_smul' a x := by ext z; simp

lemma restrictPair_apply (B : Bil W) (e f : W) (x y : pairedPlane B e f) :
    restrictPair B e f x y = B (x : W) (y : W) := rfl

lemma restrictPair_non (B : Bil W)
    (sym : ∀ x y, B x y = B y x) (non : ∀ x, (∀ y, B x y=0) → x=0)
    (e f : W) (ee : B e e=0) (ff : B f f=0) (ef : B e f=1) (fe : B f e=1) :
    ∀ x, (∀ y, restrictPair B e f x y=0) → x=0 := by
  intro x hx
  apply Subtype.ext
  change (x : W)=0
  apply non
  intro y
  obtain ⟨⟨w,a,b⟩,rfl⟩ := (pairSlice B e f ee ff ef fe).surjective y
  have hxe : B (x : W) e=0 := (sym _ _).trans (zero_e B e f x)
  have hxf : B (x : W) f=0 := (sym _ _).trans (zero_f B e f x)
  change B (x : W) ((w : W)+a • e+b • f)=0
  have h0 := hx w
  rw [restrictPair_apply] at h0
  simp [h0,hxe,hxf]

lemma pairSlice_q (B : Bil W) (e f : W) (ee : B e e=0) (ff : B f f=0)
    (ef : B e f=1) (fe : B f e=1) (sym : ∀ x y, B x y=B y x)
    (q : W → F) (q0:q 0=0) (hq : ∀ x y, q (x+y) = q x + q y + B x y)
    (u : pairedPlane B e f) (a b : F) :
    q (pairSlice B e f ee ff ef fe (u,(a,b))) =
      q u + a*q e + b*q f + a*b := by
  change q (((u : W) + a • e) + b • f) = _
  have huE : B (u : W) e=0 := (sym _ _).trans (zero_e B e f u)
  have huF : B (u : W) f=0 := (sym _ _).trans (zero_f B e f u)
  rw [hq _ (b • f), hq _ (a • e), norm_smul q q0, norm_smul q q0]
  simp [huE,huF,ef,smul_eq_mul,mul_comm]

end Pair

end PEqualNP.Outside.L_meta_29754.Geometry

namespace PEqualNP.Outside.L_meta_29754.Geometry
open PEqualNP.Outside.L_meta_29754.Tape

def fnSnoc {α : Type*} (x : Fin n → α) (c : α) : Fin (n+1) → α :=
  Fin.lastCases c x

def pairFin (k : Nat) : (V k × (F × F)) ≃ₗ[F] V (k+2) where
  toFun p := fnSnoc (fnSnoc p.1 p.2.1) p.2.2
  invFun x := ((fun i => x i.castSucc.castSucc), (x (Fin.last k).castSucc, x (Fin.last (k+1))))
  left_inv p := by
    rcases p with ⟨y,a,b⟩
    ext <;> simp [fnSnoc]
  right_inv x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [fnSnoc]
    · refine Fin.lastCases ?_ (fun s => ?_) i <;> simp [fnSnoc]
  map_add' p q := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [fnSnoc]
    · refine Fin.lastCases ?_ (fun s => ?_) i <;> simp [fnSnoc]
  map_smul' a p := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [fnSnoc]
    · refine Fin.lastCases ?_ (fun s => ?_) i <;> simp [fnSnoc]

def qStd : (r : Nat) → V (dim 0 r) → F
  | 0,_ => 0
  | r+1,x =>
    let y := (pairFin (dim 0 r)).symm x
    qStd r y.1 + y.2.1*y.2.2

def extendLinear (l : V k →ₗ[F] F) (c d : F) : (V k × (F×F)) →ₗ[F] F where
  toFun p := l p.1 + p.2.1*c+p.2.2*d
  map_add' p q := by simp [add_mul]; abel
  map_smul' a p := by simp [smul_eq_mul,mul_add,mul_assoc]

lemma pair_restrict_dim {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (B : Bil W) (e f : W) (ee : B e e=0) (ff : B f f=0)
    (ef : B e f=1) (fe : B f e=1) (rank : Module.finrank F W=2*(r+1)) :
    Module.finrank F (pairedPlane B e f)=2*r := by
  have h := (pairSlice B e f ee ff ef fe).finrank_eq
  rw [Module.finrank_prod,Module.finrank_prod,Module.finrank_self,rank] at h
  omega

theorem hyper_normal (r : Nat) :
    ∀ (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W],
    Module.finrank F W=2*r →
    ∀ (B : Bil W), (∀ x y, B x y=B y x) → (∀ x, B x x=0) →
      (∀ x, (∀ y, B x y=0) → x=0) →
      ∀ (q : W → F), q 0=0 → (∀ x y, q (x+y)=q x+q y+B x y) →
      ∃ (E : V (dim 0 r) ≃ₗ[F] W) (l : V (dim 0 r) →ₗ[F] F),
        ∀ x, q (E x)=qStd r x+l x := by
  induction r with
  | zero =>
    intro W _ _ _ rank B sym alt non q q0 hq
    have r0 : Module.finrank F W=0 := by simpa using rank
    have ss : Subsingleton W := Module.finrank_zero_iff.mp r0
    let E := LinearEquiv.ofFinrankEq (R:=F) (M:=V 0) (M':=W)
      (by rw [Module.finrank_fin_fun,r0])
    refine ⟨E,0,?_⟩
    intro x
    change q (E x)=0+0
    rw [ss.elim (E x) 0,q0,add_zero]
  | succ r ih =>
    intro W _ _ _ rank B sym alt non q q0 hq
    have pos : 0<Module.finrank F W := by omega
    haveI : Nontrivial W := Module.finrank_pos_iff.mp pos
    obtain ⟨e,he⟩ := exists_ne (0 : W)
    have hn : ∃ f, B e f≠0 := by
      by_contra z
      apply he
      apply non
      intro y
      by_contra h
      exact z ⟨y,h⟩
    obtain ⟨f,hf⟩ := hn
    have ef : B e f=1 := f2_nonzero_one _ hf
    have fe : B f e=1 := (sym f e).trans ef
    let K := pairedPlane B e f
    let D := restrictPair B e f
    obtain ⟨E,l,hE⟩ := ih K (pair_restrict_dim B e f (alt e) (alt f) ef fe rank)
      D (fun x y => sym _ _) (fun x => alt _)
      (restrictPair_non B sym non e f (alt e) (alt f) ef fe)
      (fun x => q x) q0 (fun x y => hq _ _)
    let j := (pairFin (dim 0 r)).symm
    let H := (E.prodCongr (LinearEquiv.refl F (F×F))).trans (pairSlice B e f (alt e) (alt f) ef fe)
    refine ⟨j.trans H,(extendLinear l (q e) (q f)).comp j.toLinearMap,?_⟩
    intro x
    change q (pairSlice B e f (alt e) (alt f) ef fe (E (j x).1, (j x).2)) =
      (qStd r (j x).1 + (j x).2.1*(j x).2.2) +
        (l (j x).1 + (j x).2.1*q e+(j x).2.2*q f)
    rw [pairSlice_q B e f (alt e) (alt f) ef fe sym q q0 hq, hE]
    ac_rfl

end PEqualNP.Outside.L_meta_29754.Geometry

namespace PEqualNP.Outside.L_meta_29754.Geometry
open PEqualNP.Outside.L_meta_29754.Tape PEqualNP.Outside.L_meta_29754.Phase
open scoped BigOperators

def fbit (x : F) : Bool := decide (x=1)
def field (x : Bool) : F := if x then 1 else 0

lemma zero_or_one (x : F) : x=0 ∨ x=1 := by
  by_cases hx : x=0
  · exact Or.inl hx
  · exact Or.inr (f2_nonzero_one x hx)

@[simp] lemma fbit_field (b : Bool) : fbit (field b)=b := by cases b <;> decide
@[simp] lemma field_fbit (x : F) : field (fbit x)=x := by
  rcases zero_or_one x with rfl|rfl <;> decide

def bitEquiv : F ≃ Bool := ⟨fbit,field,field_fbit,fbit_field⟩

lemma fbit_add (x y : F) : fbit (x+y)=Bool.xor (fbit x) (fbit y) := by
  rcases zero_or_one x with rfl|rfl <;> rcases zero_or_one y with rfl|rfl <;> decide
lemma fbit_mul (x y : F) : fbit (x*y)=Bool.and (fbit x) (fbit y) := by
  rcases zero_or_one x with rfl|rfl <;> rcases zero_or_one y with rfl|rfl <;> decide

def bitsE (n : Nat) : V n ≃ Env n where
  toFun x i := fbit (x i)
  invFun x i := field (x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp


def blockEquiv (m n : Nat) : (V m × V n) ≃ₗ[F] V (m+n) where
  toFun x := Fin.addCases x.1 x.2
  invFun x := (x ∘ Fin.castAdd n, x ∘ Fin.natAdd m)
  left_inv x := by
    refine Prod.ext ?_ ?_ <;> funext i <;> simp [Function.comp_def]
  right_inv x := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Function.comp_def]
  map_add' x y := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  map_smul' c x := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

lemma bitList_block (x : V m) (y : V n) :
    List.ofFn (bitsE _ (blockEquiv m n (x,y))) =
      List.ofFn (bitsE _ x) ++ List.ofFn (bitsE _ y) := by
  rw [List.ofFn_add]
  have c (i : Fin m) : i.castLE (Nat.le_add_right m n)=i.castAdd n := rfl
  simp [bitsE,blockEquiv,Function.comp_def,c]

def linFormList (c : Fin k → F) : List (Fin k) → Aff k
  | [] => .lit false
  | i::is => .add ((Aff.var i).scale (fbit (c i))) (linFormList c is)

lemma linFormList_eval (c : Fin k → F) (l : List (Fin k)) (x : V k) :
    (linFormList c l).eval (bitsE _ x) = fbit ((l.map (fun i => c i*x i)).sum) := by
  induction l with
  | nil => rfl
  | cons i is ih =>
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, linFormList,List.map_cons,List.sum_cons,Aff.eval,Aff.eval_scale,ih,fbit_add,fbit_mul]
    rfl

noncomputable def linForm (c : Fin k → F) : Aff k := linFormList c Finset.univ.toList

lemma linForm_eval (c : Fin k → F) (x : V k) :
    (linForm c).eval (bitsE _ x) = fbit (∑ i, c i*x i) := by
  rw [linForm,linFormList_eval,Finset.sum_map_toList]

lemma sum_singles (x : V k) : (∑ i : Fin k, x i • Pi.single i (1:F))=x := by
  classical
  ext j
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

lemma linear_rows (C : V k →ₗ[F] V m) (x : V k) (j : Fin m) :
    C x j = ∑ i, C (Pi.single i 1) j * x i := by
  conv_lhs => rw [← sum_singles x]
  simp [map_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]

noncomputable def linearCode (C : V k →ₗ[F] V m) (j : Fin m) : Aff k :=
  linForm fun i => C (Pi.single i 1) j

lemma eval_linearCode (C : V k →ₗ[F] V m) (j : Fin m) (x : V k) :
    (linearCode C j).eval (bitsE _ x)=fbit (C x j) := by
  simp [linearCode,linForm_eval,← linear_rows]

lemma scalar_rows (C : V k →ₗ[F] F) (x : V k) :
    C x = ∑ i, C (Pi.single i 1) * x i := by
  conv_lhs => rw [← sum_singles x]
  simp [map_sum,smul_eq_mul,mul_comm]

noncomputable def scalarCode (C : V k →ₗ[F] F) : Aff k :=
  linForm fun i => C (Pi.single i 1)

lemma eval_scalarCode (C : V k →ₗ[F] F) (x : V k) :
    (scalarCode C).eval (bitsE _ x)=fbit (C x) := by
  simp [scalarCode,linForm_eval,← scalar_rows]

def amend : Code n → Aff n → Code n
  | .ret a, f => .ret (.add a f)
  | .save z tail, f => .save z (amend tail f.up)
  | .prod u v tail, f => .prod u v (amend tail f.up)

lemma amend_cost (p : Code n) (f : Aff n) : (amend p f).cost=p.cost := by
  induction p <;> simp [amend,Code.cost, *]

lemma amend_eval (p : Code n) (f : Aff n) (x : Env n) :
    (amend p f).eval x = p.eval x ^^^ f.eval x := by
  induction p <;> simp [amend,Code.eval,Aff.eval, *]

noncomputable def rebase (p : Code m) (L : V k →ₗ[F] V m) (phaseL : V k →ₗ[F] F) : Code k :=
  amend (p.feed (linearCode L)) (scalarCode phaseL)

lemma rebase_cost (p : Code m) (L : V k →ₗ[F] V m) (phaseL : V k →ₗ[F] F) :
    (rebase p L phaseL).cost=p.cost := by
  simp [rebase,amend_cost,Code.feed_cost]

lemma rebase_eval (p : Code m) (L : V k →ₗ[F] V m) (phaseL : V k →ₗ[F] F) (x : V k) :
    (rebase p L phaseL).eval (bitsE _ x) = p.eval (bitsE _ (L x)) ^^^ fbit (phaseL x) := by
  rw [rebase,amend_eval,Code.feed_eval,eval_scalarCode]
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, eval_linearCode]
  rfl

lemma formal_agree (a : Bool) (v : F) : (if a=fbit v then (1:Int) else -1) = phase (a ^^^ fbit v) := by
  generalize fbit v = b
  cases a <;> cases b <;> decide

end PEqualNP.Outside.L_meta_29754.Geometry

namespace PEqualNP.Outside.L_meta_29754.Geometry
open PEqualNP.Outside.L_meta_29754.Tape PEqualNP.Outside.L_meta_29754.Phase
open scoped BigOperators

def baseJoint (n : Nat) : (V n × V 0) ≃ₗ[F] V n where
  toFun := Prod.fst
  invFun x := (x,0)
  left_inv p := Prod.ext rfl (by funext i; exact Fin.elim0 i)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def joint (n : Nat) : (r : Nat) → (V n × V (dim 0 r)) ≃ₗ[F] V (dim n r)
  | 0 => baseJoint n
  | r+1 =>
    ((LinearEquiv.refl F (V n)).prodCongr (pairFin (dim 0 r)).symm).trans
      ((LinearEquiv.prodAssoc F (V n) (V (dim 0 r)) (F×F)).symm.trans
      (((joint n r).prodCongr (LinearEquiv.refl F (F×F))).trans (pairFin (dim n r))))

lemma joint_snocs (n r : Nat) (x : V n) (h : V (dim 0 r)) (a b : F) :
    joint n (r+1) (x,pairFin (dim 0 r) (h,(a,b))) = pairFin (dim n r) (joint n r (x,h),(a,b)) := by
  simp [joint]
  exact ⟨rfl,rfl⟩

lemma qStd_pair (r : Nat) (h : V (dim 0 r)) (a b : F) :
    qStd (r+1) (pairFin (dim 0 r) (h,(a,b))) = qStd r h + a * b := by
  simp [qStd]

lemma bitSnoc_pair (x : V n) (a b : F) :
    bitsE _ (pairFin n (x,(a,b))) =
      snoc (snoc (bitsE _ x) (fbit a)) (fbit b) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [bitsE,pairFin,fnSnoc,snoc]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [bitsE,pairFin,fnSnoc,snoc]

lemma sum_F2 (g : F → Int) : (∑ a, g a) = g 0+g 1 := by
  classical
  let e : Bool ≃ F := bitEquiv.symm
  calc
    (∑ a, g a) = ∑ b, g (e b) :=
      (Fintype.sum_equiv e (fun b => g (e b)) g (fun _ => rfl)).symm
    _ = g 0+g 1 := by
      have h : (Finset.univ : Finset Bool) = {false,true} := by decide
      rw [h]
      simp [e,bitEquiv,field]

lemma fold4_field (f : F → F → Int) :
    fold4 (fun a b => f (field a) (field b)) = ∑ a, ∑ b, f a b := by
  simp [fold4,fold2,field,sum_F2]

theorem nested_field (r : Nat) (f : Env (dim n r) → Bool → Int) (x : V n) (t : F) :
    nested n r f (bitsE _ x) (fbit t) =
      ∑ h : V (dim 0 r), f (bitsE _ (joint n r (x,h))) (fbit (qStd r h+t)) := by
  induction r with
  | zero =>
    haveI : Unique (V 0) := ⟨⟨0⟩, fun _ => by funext i; exact Fin.elim0 i⟩
    simp [joint,baseJoint,qStd,nested]
  | succ r ih =>
    rw [nested]
    rw [ih (fun y u => fold4 (fun a b => f (snoc (snoc y a) b) ((a &&& b) ^^^ u)))]
    let g : V (dim 0 (r+1)) → Int :=
      fun h => f (bitsE _ (joint n (r+1) (x,h))) (fbit (qStd (r+1) h+t))
    change _ = ∑ h, g h
    have perm : (∑ h, g h) = ∑ p : V (dim 0 r) × (F×F), g (pairFin (dim 0 r) p) := by
      symm
      apply Fintype.sum_equiv (pairFin (dim 0 r)).toEquiv
      intro p; rfl
    rw [perm,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro h _
    rw [Fintype.sum_prod_type]
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, g,joint_snocs,qStd_pair,bitSnoc_pair]
    rw [← fold4_field]
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, fbit_add,fbit_mul,fbit_field]
    congr 1
    funext a b
    have e : Bool.xor (Bool.xor (fbit (qStd r h)) (Bool.and a b)) (fbit t) =
        Bool.xor (Bool.and a b) (Bool.xor (fbit (qStd r h)) (fbit t)) := by
      rw [Bool.xor_comm (fbit (qStd r h)) _,Bool.xor_assoc]
    rw [e,joint_snocs,bitSnoc_pair,fbit_field,fbit_field]

theorem total_eq_sum_map {ι : Type} [Fintype ι] (f : ι → Int) :
    total f Finset.univ.toList = ∑ i, f i := by
  have aux : ∀ xs : List ι, total f xs = (xs.map f).sum := by
    intro xs
    induction xs <;> simp [total, *]
  rw [aux,Finset.sum_map_toList]

end PEqualNP.Outside.L_meta_29754.Geometry

namespace PEqualNP.Outside.L_meta_29754.Geometry
open PEqualNP.Outside.L_meta_29754.Tape PEqualNP.Outside.L_meta_29754.Phase
open scoped BigOperators

abbrev remSize (n r t : Nat) := n-2*r+t
abbrev Hyp (r : Nat) := V (dim 0 r)

structure Model (n t r : Nat) (Q : V n → F) (M : Matrix (Fin n) (Fin n) F) (L : V t →ₗ[F] V n) where
  R : V (n-2*r) →ₗ[F] V n
  H : Submodule F (V n)
  A : V t →ₗ[F] V n
  Rinj : Function.Injective R
  Rrange : ∀ x, M.mulVec x=0 ↔ ∃ y, R y=x
  Hcompl : ∀ x, ∃! y, x-R y∈H
  Aspec : ∀ z, A z∈H ∧ ∀ x∈H, dotProduct x (M.mulVec (A z))=dotProduct x (L z)
  unpack : V t → (V (n-2*r) × Hyp r) ≃ V n
  next : V (dim (remSize n r t) r) ≃ₗ[F] V (n+t)
  extra : V (dim (remSize n r t) r) →ₗ[F] F
  next_apply : ∀ y z h,
    next (joint (remSize n r t) r (blockEquiv (n-2*r) t (y,z),h)) =
      blockEquiv n t (unpack z (y,h),z)
  phase_apply : ∀ y z h,
    Q (unpack z (y,h)) + dotProduct (unpack z (y,h)) (L z) =
      (Q (A z) + dotProduct (A z) (L z) + dotProduct (R y) (L z)) +
      (qStd r h + extra (joint (remSize n r t) r (blockEquiv (n-2*r) t (y,z),h)))


def glueShift {W Z : Type*} [AddCommGroup W] [Module F W]
    [AddCommGroup Z] [Module F Z] (A : Z →ₗ[F] W) :
    (W × Z) ≃ₗ[F] (W × Z) where
  toFun x := (x.1 + A x.2,x.2)
  invFun x := (x.1 - A x.2,x.2)
  left_inv x := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv x := Prod.ext (sub_add_cancel _ _) rfl
  map_add' p q := by
    refine Prod.ext ?_ rfl
    change p.1+q.1 + A (p.2+q.2) = (p.1+A p.2) + (q.1+A q.2)
    rw [map_add]; ac_rfl
  map_smul' a p := by
    refine Prod.ext ?_ rfl
    change a • p.1 + A (a • p.2) = a • (p.1+A p.2)
    rw [map_smul,smul_add]

def translate {W : Type*} [AddCommGroup W] (a : W) : W ≃ W where
  toFun x := x+a
  invFun x := x-a
  left_inv x := add_sub_cancel_right _ _
  right_inv x := sub_add_cancel _ _

theorem makeModel (n t r : Nat) (Q : V n → F) (M : Matrix (Fin n) (Fin n) F) (L : V t →ₗ[F] V n)
    (rank : M.rank=2*r)
    (polar : ∀ x y : V n, Q (x+y)+Q x+Q y+Q 0 = dotProduct x (M.mulVec y)) :
    Nonempty (Model n t r Q M L) := by
  classical
  let d := n-2*r
  let K := rad M
  obtain ⟨H,hKH⟩ := Submodule.exists_isCompl K
  let kE : V d ≃ₗ[F] K := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun,rad_dim M rank])
  let R : V d →ₗ[F] V n := K.subtype.comp kE.toLinearMap
  have sym := pol_symm M Q polar
  have alt := pol_alt M Q polar
  have aInj := polarOn_inj M H hKH sym
  let aH := addr M H L aInj
  let A : V t →ₗ[F] V n := H.subtype.comp aH
  let sumE := K.prodEquivOfIsCompl H hKH
  have hdim : Module.finrank F H = 2*r := by
    have eq := sumE.finrank_eq
    rw [Module.finrank_prod,rad_dim M rank,Module.finrank_fin_fun] at eq
    have ra := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    change M.rank + Module.finrank F (rad M) = Module.finrank F (V n) at ra
    rw [Module.finrank_fin_fun,rank] at ra
    omega
  let q := fun x => Q x + Q 0
  have q0 : q 0=0 := f2_add_self _
  have hp : ∀ x y, Q (x+y)+Q x+Q y+Q 0 = pol M x y := polar
  have qadd : ∀ x y, q (x+y) = q x+q y+pol M x y := polar_norm Q _ hp
  have qRestore (x : V n) : Q x = q x+Q 0 := by
    change Q x=Q x+Q 0+Q 0
    rw [add_assoc,f2_add_self,add_zero]
  have hsym (x y : H) : polarOn M H x y = polarOn M H y x := sym _ _
  have halt (x : H) : polarOn M H x x = 0 := alt _
  have hnon (x : H) (hx : ∀ y, polarOn M H x y=0) : x=0 := by
    apply aInj
    ext y
    simpa using hx y
  obtain ⟨hE,hPh,hq⟩ := hyper_normal r H hdim (polarOn M H) hsym halt hnon
    (fun x => q x) q0 (fun x y => by
      change q ((x : V n)+(y : V n))=q x+q y+pol M (y : V n) (x : V n)
      rw [qadd,sym (x : V n) (y : V n)])
  let rPh : V d →ₗ[F] F :=
    { toFun := fun y => q (R y)
      map_add' := by
        intro x y
        have hRad : R y ∈ rad M := (kE y).property
        rw [map_add,qadd,rad_right M hRad,add_zero]
      map_smul' := fun a y => by
        rw [map_smul,norm_smul q q0]
        rfl }
  let shift := glueShift aH
  let rot : ((V d × V t) × Hyp r) ≃ₗ[F] ((K × H) × V t) :=
    (LinearEquiv.prodAssoc F (V d) (V t) (Hyp r)).trans
      (((LinearEquiv.refl F (V d)).prodCongr (LinearEquiv.prodComm F (V t) (Hyp r))).trans
        ((LinearEquiv.prodAssoc F (V d) (Hyp r) (V t)).symm.trans
          ((kE.prodCongr hE).prodCongr (LinearEquiv.refl F (V t)))))
  let before := (joint (d+t) r).symm.trans
    (((blockEquiv d t).symm).prodCongr (LinearEquiv.refl F (Hyp r)))
  let next := before.trans (rot.trans
    (((LinearEquiv.prodAssoc F K H (V t)).trans ((LinearEquiv.refl F K).prodCongr shift)).trans
      ((LinearEquiv.prodAssoc F K H (V t)).symm.trans
        ((sumE.prodCongr (LinearEquiv.refl F (V t))).trans (blockEquiv n t)))))
  let ℓ0 : ((V d × V t) × Hyp r) →ₗ[F] F :=
    ((rPh.comp (LinearMap.fst F (V d) (V t))).coprod hPh)
  let extra := ℓ0.comp before.toLinearMap
  let unpack : V t → (V d × Hyp r) ≃ V n :=
    fun z => ((kE.prodCongr hE).trans sumE).toEquiv.trans (translate (A z))
  refine ⟨⟨R,H,A,?_,?_,?_,?_,unpack,next,extra,?_,?_⟩⟩
  · exact Subtype.val_injective.comp kE.injective
  · intro x
    refine ⟨fun hx => ?_,?_⟩
    · let k : K := ⟨x,LinearMap.mem_ker.mpr hx⟩
      refine ⟨kE.symm k,?_⟩
      change (kE (kE.symm k) : V n)=x
      rw [kE.apply_symm_apply]
    · rintro ⟨y,rfl⟩
      exact LinearMap.mem_ker.mp (kE y).property
  · intro x
    obtain ⟨k,h,e,uniq⟩ := Submodule.existsUnique_add_of_isCompl hKH x
    refine ⟨kE.symm k,?_,?_⟩
    · have rk : R (kE.symm k) = (k : V n) := by simp [R]
      change x - R (kE.symm k) ∈ H
      rw [rk,← e,add_sub_cancel_left]
      exact h.property
    · intro y hy
      have ry : (kE y : V n) + (x - R y) = x := by rw [add_comm]; exact sub_add_cancel _ _
      exact kE.injective ((uniq (kE y) ⟨x-R y,hy⟩ ry).1.trans (kE.apply_symm_apply k).symm)
  · intro z
    exact ⟨(aH z).property,fun x hx => addr_spec M H L aInj z ⟨x,hx⟩⟩
  · intro y z h
    change next (joint (d+t) r (blockEquiv d t (y,z),h)) = _
    have hs : before (joint (d+t) r (blockEquiv d t (y,z),h)) = ((y,z),h) := by simp [before]
    have rt : rot ((y,z),h) = ((kE y,hE h),z) := rfl
    simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, next,LinearEquiv.trans_apply,hs,rt]
    change blockEquiv n t (sumE (kE y,hE h+aH z),z) =
      blockEquiv n t (sumE (kE y,hE h) + A z,z)
    apply congrArg (blockEquiv n t)
    refine Prod.ext ?_ rfl
    change (kE y : V n) + ((hE h : V n)+(aH z : V n)) =
      ((kE y : V n)+(hE h : V n))+(aH z : V n)
    exact (add_assoc _ _ _).symm
  · intro y z h
    have val : unpack z (y,h) = ((hE h : V n)+A z)+R y := by
      change ((kE y : V n)+(hE h : V n))+A z = ((hE h : V n)+A z)+R y
      change _ = _ + (kE y : V n)
      ac_rfl
    rw [val,qRestore _]
    have zh := addr_spec M H L aInj z (hE h)
    have qc : pol M (hE h : V n) (A z) = dotProduct (hE h : V n) (L z) := zh
    have hr : R y∈rad M := (kE y).property
    have he : extra (joint (d+t) r (blockEquiv d t (y,z),h)) = q (R y)+hPh h := by
      simp [extra,ℓ0,before,rPh]
    rw [qadd _ (R y),rad_right M hr,add_zero,qadd _ (A z),qc,he,qRestore (A z),add_dotProduct,add_dotProduct,hq]
    have ct (b : F) : b + b = 0 := f2_add_self b
    generalize dotProduct (hE h : V n) (L z) = b
    generalize dotProduct (A z) (L z) = a
    generalize dotProduct (R y) (L z) = c
    generalize q (A z) = qA
    generalize q (R y) = qR
    generalize qStd r h = hQ
    generalize hPh h = hL
    generalize Q 0 = qZero
    calc
      _ = (qA + qZero + a + c + (hQ + (qR+hL))) + (b+b) := by abel
      _ = _ := by rw [ct,add_zero]

end PEqualNP.Outside.L_meta_29754.Geometry

namespace PEqualNP.Outside.L_meta_29754.Geometry
open PEqualNP.Outside.L_meta_29754.Tape PEqualNP.Outside.L_meta_29754.Phase
open PEqualNP.CircuitLowerBounds
open scoped BigOperators

def remPhase {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (g : V t → F) (y : V (n-2*r)) (z : V t) : F :=
  g z + Q (geom.A z) + dotProduct (geom.A z) (L z) + dotProduct (geom.R y) (L z)

noncomputable def scenario {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (g : V t → F) (w : V t → Int) :
    List (Sample (remSize n r t)) :=
  ((Finset.univ : Finset (V t)).toList).flatMap fun z =>
    ((Finset.univ : Finset (V (n-2*r))).toList).map fun y =>
      ⟨bitsE _ (blockEquiv _ _ (y,z)),w z,fbit (remPhase geom g y z)⟩

theorem scenario_sum {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (g : V t → F) (w : V t → Int)
    (f : Env (remSize n r t) → Bool → Int) :
    total (fun v => v.weight*f v.x v.target) (scenario geom g w) =
      ∑ z, w z * ∑ y, f (bitsE _ (blockEquiv _ _ (y,z))) (fbit (remPhase geom g y z)) := by
  simp [scenario,total_flatMap,total_map,total_eq_sum_map,Function.comp_def,Finset.mul_sum]

noncomputable def signedFull {Q : V n → F} {L : V t →ₗ[F] V n}
    (p : Code (n+t)) (g : V t → F) (w : V t → Int) : Int :=
  ∑ z, w z * ∑ x : V n,
    phase (p.eval (bitsE _ (blockEquiv _ _ (x,z))) ^^^ fbit (g z+Q x+dotProduct x (L z)))

theorem score_full {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (p : Code (n+t)) (g : V t → F) (w : V t → Int) :
    score (rebase p geom.next.toLinearMap geom.extra) (spreadMany (scenario geom g w) r) =
      signedFull (Q:=Q) (L:=L) p g w := by
  rw [score_spreadMany_eq_nested,scenario_sum,signedFull]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  symm
  let term := fun x : V n =>
    phase (p.eval (bitsE _ (blockEquiv _ _ (x,z))) ^^^ fbit (g z+Q x+dotProduct x (L z)))
  change (∑ x, term x) = _
  have e : (∑ x, term x) = ∑ pair, term (geom.unpack z pair) :=
    (Fintype.sum_equiv (geom.unpack z) (term ∘ geom.unpack z) term (fun _ => rfl)).symm
  rw [e,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [nested_field]
  apply Finset.sum_congr rfl
  intro h _
  rw [rebase_eval]
  simp only [PEqualNP.Outside.L_meta_29754.Phase.xor_core, PEqualNP.Outside.L_meta_29754.Phase.and_core, LinearEquiv.coe_coe,geom.next_apply,term]
  have eq : g z + Q (geom.unpack z (y,h)) + dotProduct (geom.unpack z (y,h)) (L z) =
      geom.extra (joint (remSize n r t) r (blockEquiv _ t (y,z),h)) +
        (qStd r h + remPhase geom g y z) := by
    rw [add_assoc,geom.phase_apply,remPhase]
    ac_rfl
  rw [eq,fbit_add,Bool.xor_assoc]

theorem sample_congr (p q : Code n) (h : ∀ x, p.eval x=q.eval x) (xs : List (Sample n)) :
    score p xs=score q xs := by
  simp [score,h]

theorem inverse_rebase {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (p : Code (dim (remSize n r t) r)) (x : Env (dim (remSize n r t) r)) :
    (rebase (rebase p geom.next.symm.toLinearMap (geom.extra.comp geom.next.symm.toLinearMap))
        geom.next.toLinearMap geom.extra).eval x = p.eval x := by
  obtain ⟨f,rfl⟩ := (bitsE _).surjective x
  rw [rebase_eval,rebase_eval]
  simp [Bool.xor_assoc]

theorem full_project_bridge {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (C : Circuit) (ok : legal (n+t) C) (g : V t → F) (w : V t → Int) :
    (∑ z, w z * ∑ x : V n, (if C.eval (List.ofFn (bitsE _ x) ++ List.ofFn (bitsE _ z)) =
      fbit (g z+Q x+dotProduct x (L z)) then (1:Int) else -1)) =
      signedFull (Q:=Q) (L:=L) (decode _ (C.gates.map gateIn) C.output) g w := by
  simp [signedFull,import_eval _ _ ok,bitList_block,formal_agree]

theorem rem_project_bridge {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (D : Circuit) (ok : legal (remSize n r t) D) (g : V t → F) (w : V t → Int) :
    (∑ z : V t, w z * ∑ y : V (n-2*r), (if D.eval (List.ofFn (bitsE _ y) ++ List.ofFn (bitsE _ z)) =
      fbit (remPhase geom g y z) then (1:Int) else -1)) =
      score (decode _ (D.gates.map gateIn) D.output) (scenario geom g w) := by
  rw [score,scenario_sum geom g w
    (fun x t => phase ((decode _ (D.gates.map gateIn) D.output).eval x ^^^ t))]
  simp [import_eval _ _ ok,bitList_block,formal_agree]

end PEqualNP.Outside.L_meta_29754.Geometry

namespace PEqualNP.Outside.L_meta_29754.Geometry
open PEqualNP.Outside.L_meta_29754.Tape PEqualNP.Outside.L_meta_29754.Phase
open PEqualNP.CircuitLowerBounds
open scoped BigOperators

noncomputable def cFull (Q : V n → F) (L : V t →ₗ[F] V n)
    (g : V t → F) (w : V t → Int) (C : Circuit) : Int :=
  ∑ z, w z * ∑ x : V n, if C.eval (List.ofFn (bitsE _ x) ++ List.ofFn (bitsE _ z)) =
    fbit (g z+Q x+dotProduct x (L z)) then (1:Int) else -1

noncomputable def cRemn {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (g : V t → F) (w : V t → Int) (D : Circuit) : Int :=
  ∑ z, w z * ∑ y : V (n-2*r), if D.eval (List.ofFn (bitsE _ y) ++ List.ofFn (bitsE _ z)) =
    fbit (remPhase geom g y z) then (1:Int) else -1

theorem cfull_export (Q : V n → F) (L : V t →ₗ[F] V n) (g : V t → F)
    (w : V t → Int) (p : Code (n+t)) :
    cFull Q L g w (exportTape p) = signedFull (Q:=Q) (L:=L) p g w := by
  simp [cFull,signedFull,← bitList_block,export_eval,formal_agree]

theorem crem_export {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (g : V t → F) (w : V t → Int) (p : Code (remSize n r t)) :
    cRemn geom g w (exportTape p) = score p (scenario geom g w) := by
  rw [score,scenario_sum geom g w (fun x t=>phase (p.eval x ^^^ t))]
  simp [cRemn,← bitList_block,export_eval,formal_agree]

theorem project_curve {Q : V n → F} {M : Matrix (Fin n) (Fin n) F} {L : V t →ₗ[F] V n}
    (geom : Model n t r Q M L) (g : V t → F) (w : V t → Int) (s : Nat) :
    let u := min r s
    (∀ C : Circuit, legal (n+t) C → projectCost C ≤ s →
      ∃ D : Circuit, legal (n-2*r+t) D ∧ projectCost D ≤ s-u ∧
        (cFull Q L g w C).natAbs ≤ 2^(r+u) * (cRemn geom g w D).natAbs) ∧
    (∀ D : Circuit, legal (n-2*r+t) D → projectCost D ≤ s-u →
      ∃ C : Circuit, legal (n+t) C ∧ projectCost C ≤ s ∧
        (cFull Q L g w C).natAbs = 2^(r+u) * (cRemn geom g w D).natAbs) := by
  dsimp only
  constructor
  · intro C hC costC
    let p := decode (n+t) (C.gates.map gateIn) C.output
    let par := rebase p geom.next.toLinearMap geom.extra
    have bd : par.cost ≤ s := by simpa [par,p,rebase_cost,import_cost _ _ hC] using costC
    obtain ⟨q,hq,hi⟩ := score_curve_upper r par (scenario geom g w)
    refine ⟨exportTape q,export_legal q,?_,?_⟩
    · rw [export_cost,hq]
      omega
    · rw [crem_export,show cFull Q L g w C = signedFull (Q:=Q) (L:=L) p g w from
        full_project_bridge geom C hC g w, ← score_full geom p]
      apply Nat.le_trans hi
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_right (by decide : 0<2)
      omega
  · intro D hD costD
    let q := decode (remSize n r t) (D.gates.map gateIn) D.output
    let u := min r s
    have uc : u≤r := Nat.min_le_left _ _
    have us : u≤s := Nat.min_le_right _ _
    have bd : q.cost ≤ s-u := by simpa [q, u,import_cost _ _ hD] using costD
    obtain ⟨p,hp,hi⟩ := score_curve_lower r u uc q (scenario geom g w)
    let back := rebase p geom.next.symm.toLinearMap (geom.extra.comp geom.next.symm.toLinearMap)
    refine ⟨exportTape back,export_legal back,?_,?_⟩
    · rw [export_cost,rebase_cost,hp]
      omega
    · rw [cfull_export,← score_full geom back]
      rw [sample_congr _ p (inverse_rebase geom p),hi]
      rw [show cRemn geom g w D = score q (scenario geom g w) from rem_project_bridge geom D hD g w]

end PEqualNP.Outside.L_meta_29754.Geometry




open scoped BigOperators

theorem PEqualNP.Outside.L_meta_29754 :
  ∀ (n t r : ℕ),
    let Circ := PEqualNP.CircuitLowerBounds.Circuit
    let legal := fun (nW : ℕ) (C : Circ) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    let cost := fun (C : Circ) =>
      C.gates.countP (fun g => @decide
        ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let F := ZMod 2
    let V := Fin n → F
    let Z := Fin t → F
    let Y := Fin (n-2*r) → F
    let bits := fun (j : ℕ) (v : Fin j → F) =>
      List.ofFn (fun i : Fin j => decide (v i = 1))
    let agree := fun (a : Bool) (v : F) => if a = decide (v = 1) then (1 : ℤ) else -1
    ∀ (Q : V → F) (M : Matrix (Fin n) (Fin n) F) (L : Z →ₗ[F] V),
      M.rank = 2*r →
      (∀ x y : V, Q (x+y) + Q x + Q y + Q 0 = dotProduct x (M.mulVec y)) →
      ∃ (R : Y →ₗ[F] V) (H : Submodule F V) (A : Z →ₗ[F] V),
        Function.Injective R ∧ (∀ x : V, M.mulVec x = 0 ↔ ∃ y, R y = x) ∧
        (∀ x : V, ∃! y : Y, x-R y ∈ H) ∧
        (∀ z : Z, A z ∈ H ∧ ∀ x ∈ H, dotProduct x (M.mulVec (A z)) = dotProduct x (L z)) ∧
        ∀ (g : Z → F) (w : Z → ℤ) (s : ℕ),
          let full := fun (C : Circ) => (∑ z : Z, w z * ∑ x : V,
            agree (C.eval (bits n x ++ bits t z)) (g z + Q x + dotProduct x (L z))).natAbs
          let remn := fun (D : Circ) => (∑ z : Z, w z * ∑ y : Y,
            agree (D.eval (bits (n-2*r) y ++ bits t z))
              (g z + Q (A z) + dotProduct (A z) (L z) + dotProduct (R y) (L z))).natAbs
          let u := min r s
          (∀ C : Circ, legal (n+t) C → cost C ≤ s →
            ∃ D : Circ, legal (n-2*r+t) D ∧ cost D ≤ s-u ∧ full C ≤ 2^(r+u)*remn D) ∧
          (∀ D : Circ, legal (n-2*r+t) D → cost D ≤ s-u →
            ∃ C : Circ, legal (n+t) C ∧ cost C ≤ s ∧ full C = 2^(r+u)*remn D) := by
  intro n t r
  dsimp only
  intro Q M L hr hpolar
  obtain ⟨geom⟩ := PEqualNP.Outside.L_meta_29754.Geometry.makeModel n t r Q M L hr hpolar
  refine ⟨geom.R,geom.H,geom.A,geom.Rinj,geom.Rrange,geom.Hcompl,geom.Aspec,?_⟩
  intro g w s
  exact PEqualNP.Outside.L_meta_29754.Geometry.project_curve geom g w s
