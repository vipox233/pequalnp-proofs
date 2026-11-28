import PEqualNP.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Init
import Mathlib.Data.Fin.VecNotation

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

open PEqualNP.CircuitLowerBounds

abbrev Signal (X : Type) := X → Bool

inductive Op where
  | conj
  | disj
  | diff

def Op.eval : Op → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .diff, a, b => a && !b

def Op.on (op : Op) {X : Type} (a b : Signal X) : Signal X :=
  fun x => op.eval (a x) (b x)

def zero {X : Type} : Signal X := fun _ => false

def normalizeAt {X : Type} (origin : X) (f : Signal X) : Signal X :=
  fun x => xor (f x) (f origin)

def base (n : Nat) : List (Signal (Fin n → Bool)) :=
  zero :: List.ofFn (fun i x => x i)

def CanMake {X : Type} (bank : List (Signal X)) (f : Signal X) : Prop :=
  ∃ op : Op, ∃ a ∈ bank, ∃ b ∈ bank, f = op.on a b

def Reach {X : Type} (f : Signal X) : Nat → List (Signal X) → Prop
  | 0, bank => f ∈ bank
  | k + 1, bank => f ∈ bank ∨ ∃ s, CanMake bank s ∧ Reach f k (s :: bank)

theorem Reach.here {X : Type} {f : Signal X} {k : Nat} {bank : List (Signal X)}
    (present : f ∈ bank) : Reach f k bank := by
  cases k
  · exact present
  · exact Or.inl present

theorem Reach.extend {X : Type} {f s : Signal X} {k : Nat} {bank : List (Signal X)}
    (make : CanMake bank s) (rest : Reach f k (s :: bank)) : Reach f (k + 1) bank :=
  Or.inr ⟨s, make, rest⟩

theorem Reach.weakenBudget {X : Type} {f : Signal X} :
    ∀ k (bank : List (Signal X)), Reach f k bank → Reach f (k + 1) bank
  | 0, _, present => Reach.here present
  | k + 1, bank, step => by
    rcases step with present | ⟨v, make, rest⟩
    · exact Reach.here present
    · exact Reach.extend make (Reach.weakenBudget k (v :: bank) rest)

theorem Reach.weakenBank {X : Type} {f : Signal X} :
    ∀ k (bank other : List (Signal X)), (∀ v ∈ bank, v ∈ other) →
      Reach f k bank → Reach f k other
  | 0, _, _, subset, present => subset f present
  | k + 1, bank, other, subset, step => by
    rcases step with present | ⟨v, ⟨op, a, ha, b, hb, rfl⟩, rest⟩
    · exact Reach.here (subset f present)
    · apply Reach.extend ⟨op, a, subset a ha, b, subset b hb, rfl⟩
      apply Reach.weakenBank k (op.on a b :: bank) (op.on a b :: other) _ rest
      intro y hy
      rcases List.mem_cons.mp hy with same | old
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem _ (subset y old)

private theorem phaseTable (op : Op) (oa ob : Bool) :
    (∀ a b, xor (op.eval a b) (op.eval oa ob) = (xor a oa && xor b ob)) ∨
    (∀ a b, xor (op.eval a b) (op.eval oa ob) = (xor a oa || xor b ob)) ∨
    (∀ a b, xor (op.eval a b) (op.eval oa ob) = (xor a oa && !(xor b ob))) ∨
    (∀ a b, xor (op.eval a b) (op.eval oa ob) = (xor b ob && !(xor a oa))) := by
  cases op <;> cases oa <;> cases ob <;> decide

theorem phaseOp {X : Type} (origin : X) (op : Op) (a b : Signal X)
    (bank : List (Signal X)) (ha : normalizeAt origin a ∈ bank)
    (hb : normalizeAt origin b ∈ bank) :
    CanMake bank (normalizeAt origin (op.on a b)) := by
  rcases phaseTable op (a origin) (b origin) with h | h | h | h
  · exact ⟨.conj, _, ha, _, hb, funext (fun x => h (a x) (b x))⟩
  · exact ⟨.disj, _, ha, _, hb, funext (fun x => h (a x) (b x))⟩
  · exact ⟨.diff, _, ha, _, hb, funext (fun x => h (a x) (b x))⟩
  · exact ⟨.diff, _, hb, _, ha, funext (fun x => h (a x) (b x))⟩

@[simp] theorem phase_const {X : Type} (origin : X) (b : Bool) :
    normalizeAt origin (fun _ => b) = zero := by
  cases b <;> rfl

@[simp] theorem phase_complement {X : Type} (origin : X) (f : Signal X) :
    normalizeAt origin (fun x => !(f x)) = normalizeAt origin f := by
  funext x
  change xor (!(f x)) (!(f origin)) = xor (f x) (f origin)
  cases f x <;> cases f origin <;> rfl

def stepCost : GateOp → Nat
  | .not => 0
  | _ => 1

private theorem stepCost_le (op : GateOp) : stepCost op ≤ 1 := by
  cases op <;> simp [stepCost]

def nonNotCount : List Gate → Nat
  | [] => 0
  | g :: gs => nonNotCount gs + stepCost g.op

theorem nonNotCount_le (gates : List Gate) : nonNotCount gates ≤ gates.length := by
  induction gates with
  | nil => exact le_rfl
  | cons g rest ih =>
    have cost := stepCost_le g.op
    simp only [nonNotCount, List.length_cons]
    omega

theorem nonNotCount_add_one_le (gates : List Gate)
    (signed : ∃ g ∈ gates, g.op = .not) : nonNotCount gates + 1 ≤ gates.length := by
  induction gates with
  | nil => simp at signed
  | cons g rest ih =>
    obtain ⟨h, member, neg⟩ := signed
    rcases List.mem_cons.mp member with same | previous
    · subst h
      have tail := nonNotCount_le rest
      simpa [nonNotCount, neg, stepCost] using Nat.succ_le_succ tail
    · have tail := ih ⟨h, previous, neg⟩
      have cost := stepCost_le g.op
      simp only [nonNotCount, List.length_cons]
      omega

def gateFunction {X : Type} (wires : List (Signal X)) (g : Gate) : Signal X :=
  fun x => g.op.eval (g.inputs.map fun i => (wires.getD i zero) x)

def Legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private theorem wire_covered {X : Type} (origin : X) {wires bank : List (Signal X)}
    (hz : zero ∈ bank) (cover : ∀ f ∈ wires, normalizeAt origin f ∈ bank) (i : Nat) :
    normalizeAt origin (wires.getD i zero) ∈ bank := by
  by_cases valid : i < wires.length
  · have get : wires.getD i zero = wires[i] := by
      simp [List.getD_eq_getElem?_getD, valid]
    rw [get]
    exact cover _ (List.getElem_mem valid)
  · have get : wires.getD i zero = zero := by
      simp [List.getD_eq_getElem?_getD, not_lt.mp valid]
    rw [get]
    exact hz

private theorem gate_covered {X : Type} (origin : X) {wires bank : List (Signal X)}
    (hz : zero ∈ bank) (cover : ∀ f ∈ wires, normalizeAt origin f ∈ bank) (g : Gate)
    (legal : Legal g) :
    normalizeAt origin (gateFunction wires g) ∈ bank ∨
    (stepCost g.op = 1 ∧ CanMake bank (normalizeAt origin (gateFunction wires g))) := by
  let rd := fun i => wires.getD i zero
  have seen (i : Nat) : normalizeAt origin (rd i) ∈ bank := wire_covered origin hz cover i
  obtain ⟨operation, addresses⟩ := g
  obtain ⟨op, arity⟩ := legal
  change operation = .and ∨ operation = .or ∨ operation = .not at op
  change addresses.length ≤ 2 at arity
  rcases addresses with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases op with rfl | rfl | rfl <;> exact Or.inl hz
  · left
    rcases op with rfl | rfl | rfl
    · have gateEq : gateFunction wires ⟨.and, [a]⟩ = rd a := by
        funext x
        simp [gateFunction, GateOp.eval, rd]
      rw [gateEq]
      exact seen a
    · have gateEq : gateFunction wires ⟨.or, [a]⟩ = rd a := by
        funext x
        simp [gateFunction, GateOp.eval, rd]
      rw [gateEq]
      exact seen a
    · change normalizeAt origin (fun x => !(rd a x)) ∈ bank
      rw [phase_complement]
      exact seen a
  · rcases op with rfl | rfl | rfl
    · have gateEq : gateFunction wires ⟨.and, [a, b]⟩ = Op.conj.on (rd a) (rd b) := by
        funext x
        simp [gateFunction, GateOp.eval, rd, Op.on, Op.eval]
      rw [gateEq]
      exact Or.inr ⟨rfl, phaseOp origin .conj (rd a) (rd b) bank (seen a) (seen b)⟩
    · have gateEq : gateFunction wires ⟨.or, [a, b]⟩ = Op.disj.on (rd a) (rd b) := by
        funext x
        simp [gateFunction, GateOp.eval, rd, Op.on, Op.eval]
      rw [gateEq]
      exact Or.inr ⟨rfl, phaseOp origin .disj (rd a) (rd b) bank (seen a) (seen b)⟩
    · left
      change normalizeAt origin (fun x => !(rd a x)) ∈ bank
      rw [phase_complement]
      exact seen a
  · simp at arity

def runFunctions {X : Type} (gates : List Gate) (wires : List (Signal X)) : List (Signal X) :=
  gates.foldl (fun w g => w ++ [gateFunction w g]) wires

theorem reach_of_functions {X : Type} (origin : X) (gates : List Gate)
    (wires bank : List (Signal X)) (hz : zero ∈ bank)
    (cover : ∀ f ∈ wires, normalizeAt origin f ∈ bank)
    (legal : ∀ g ∈ gates, Legal g) (o : Nat) :
    Reach (normalizeAt origin ((runFunctions gates wires).getD o zero)) (nonNotCount gates) bank := by
  induction gates generalizing wires bank with
  | nil => exact wire_covered origin hz cover o
  | cons g rest ih =>
    let value := gateFunction wires g
    have tails : ∀ h ∈ rest, Legal h := fun h mh => legal h (List.mem_cons_of_mem _ mh)
    have extendCoverage {B : List (Signal X)} (old : ∀ f ∈ wires, normalizeAt origin f ∈ B)
        (newValue : normalizeAt origin value ∈ B) :
        ∀ f ∈ wires ++ [value], normalizeAt origin f ∈ B := by
      intro f member
      rcases List.mem_append.mp member with earlier | last
      · exact old f earlier
      · have e : f = value := List.mem_singleton.mp last
        simpa only [e] using newValue
    change Reach (normalizeAt origin ((runFunctions rest (wires ++ [value])).getD o zero))
      (nonNotCount rest + stepCost g.op) bank
    rcases gate_covered origin hz cover g (legal g List.mem_cons_self) with inBank | ⟨cost, make⟩
    · have tail := ih (wires ++ [value]) bank hz (extendCoverage cover inBank) tails
      cases g.op <;> simp only [stepCost, Nat.add_zero] <;>
        first | exact tail | exact Reach.weakenBudget _ _ tail
    · rw [cost]
      apply Reach.extend make
      exact ih (wires ++ [value]) (normalizeAt origin value :: bank)
        (List.mem_cons_of_mem _ hz)
        (extendCoverage (fun f hf => List.mem_cons_of_mem _ (cover f hf)) List.mem_cons_self)
        tails

private theorem evaluate_run {X : Type} (gates : List Gate) (wires : List (Signal X)) (x : X) :
    (runFunctions gates wires).map (fun f => f x) =
      (Circuit.mk gates 0).wires (wires.map (fun f => f x)) := by
  induction gates generalizing wires with
  | nil => rfl
  | cons g rest ih =>
    change (runFunctions rest (wires ++ [gateFunction wires g])).map (fun f => f x) =
      (Circuit.mk rest 0).wires
        (wires.map (fun f => f x) ++
          [g.op.eval (g.inputs.map (fun i => (wires.map (fun f => f x)).getD i false))])
    rw [ih]
    have agree (i : Nat) :
        (wires.getD i zero) x = (wires.map (fun f => f x)).getD i false :=
      (List.getD_map (l := wires) (d := zero) (fun f => f x)).symm
    simp [gateFunction, agree]

theorem reach_of_circuit {n : Nat} (target : Signal (Fin n → Bool)) (gates : List Gate)
    (out : Nat) (legal : ∀ g ∈ gates, Legal g)
    (exactEval : ∀ x, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = target x) :
    Reach (normalizeAt (fun _ => false) target) (nonNotCount gates) (base n) := by
  let wires : List (Signal (Fin n → Bool)) := List.ofFn (fun i x => x i)
  have evaluations : (runFunctions gates wires).getD out zero = target := by
    funext x
    rw [← exactEval x]
    change ((runFunctions gates wires).getD out zero) x =
      ((Circuit.mk gates 0).wires (List.ofFn x)).getD out false
    rw [← List.getD_map (l := runFunctions gates wires) (d := zero) (fun f => f x)]
    rw [evaluate_run]
    have raw : wires.map (fun f => f x) = List.ofFn x := by
      simp [wires, List.map_ofFn, Function.comp_def]
    rw [raw]
    rfl
  rw [← evaluations]
  apply reach_of_functions (fun _ => false) gates wires (base n) List.mem_cons_self _ legal out
  intro f hf
  have same : normalizeAt (fun _ => false) f = f := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    funext x
    change xor (x i) false = x i
    cases x i <;> rfl
  rw [same]
  exact List.mem_cons_of_mem _ hf

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

def raw {n : Nat} (p : Fin n) : Signal (Fin n → Bool) := fun x => x p

def setRaw {n : Nat} (p : Fin n) (b : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = p then b else x i

def pin {n : Nat} (p : Fin n) (b : Bool) (f : Signal (Fin n → Bool)) :
    Signal (Fin n → Bool) :=
  normalizeAt (fun _ => false) (fun x => f (setRaw p b x))

def Independent {n : Nat} (p : Fin n) (f : Signal (Fin n → Bool)) : Prop :=
  ∀ b x, f (setRaw p b x) = f x

def Stable {n : Nat} (p : Fin n) (f : Signal (Fin n → Bool)) : Prop :=
  Independent p f ∧ f (fun _ => false) = false

def PinBank {n : Nat} (p : Fin n) (bank : List (Signal (Fin n → Bool))) : Prop :=
  zero ∈ bank ∧ ∀ f ∈ bank, f = raw p ∨ Stable p f

@[simp] theorem pin_raw {n : Nat} (p : Fin n) (b : Bool) : pin p b (raw p) = zero := by
  have fixed : (fun x => raw p (setRaw p b x)) = fun _ => b := by
    funext x
    simp [raw, setRaw]
  unfold pin
  rw [fixed]
  exact phase_const _ _

theorem pin_stable {n : Nat} {p : Fin n} {f : Signal (Fin n → Bool)}
    (stable : Stable p f) (b : Bool) : pin p b f = f := by
  have unchanged : (fun x => f (setRaw p b x)) = f := funext (stable.1 b)
  unfold pin
  rw [unchanged]
  funext x
  simp [normalizeAt, stable.2]

private theorem Stable.op {n : Nat} {p : Fin n} {a b : Signal (Fin n → Bool)}
    (ha : Stable p a) (hb : Stable p b) (op : Op) : Stable p (op.on a b) := by
  constructor
  · intro bit x
    show op.eval (a (setRaw p bit x)) (b (setRaw p bit x)) = op.eval (a x) (b x)
    rw [ha.1 bit x, hb.1 bit x]
  · show op.eval (a (fun _ => false)) (b (fun _ => false)) = false
    rw [ha.2, hb.2]
    cases op <;> rfl

private theorem PinBank.consStable {n : Nat} {p : Fin n} {f : Signal (Fin n → Bool)}
    {bank : List (Signal (Fin n → Bool))} (good : PinBank p bank) (st : Stable p f) :
    PinBank p (f :: bank) := by
  refine ⟨List.mem_cons_of_mem _ good.1, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with same | other
  · rw [same]
    exact Or.inr st
  · exact good.2 a other

theorem base_pinBank {n : Nat} (p : Fin n) : PinBank p (base n) := by
  refine ⟨List.mem_cons_self, ?_⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | memRaw
  · exact Or.inr ⟨fun _ _ => rfl, rfl⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp memRaw
    by_cases same : i = p
    · left
      subst i
      rfl
    · right
      refine ⟨?_, rfl⟩
      intro b x
      simp [setRaw, same]

theorem Reach.mapPin {n : Nat} {f : Signal (Fin n → Bool)} (p : Fin n) (bit : Bool) :
    ∀ k bank, Reach f k bank → Reach (pin p bit f) k (bank.map (pin p bit))
  | 0, _, here => List.mem_map.mpr ⟨f, here, rfl⟩
  | k + 1, bank, reach => by
    rcases reach with here | ⟨_, ⟨op, a, ha, b, hb, rfl⟩, rest⟩
    · exact Reach.here (List.mem_map.mpr ⟨f, here, rfl⟩)
    · have step : CanMake (bank.map (pin p bit)) (pin p bit (op.on a b)) :=
        phaseOp (fun _ => false) op (fun x => a (setRaw p bit x)) (fun x => b (setRaw p bit x))
          _ (List.mem_map.mpr ⟨a, ha, rfl⟩) (List.mem_map.mpr ⟨b, hb, rfl⟩)
      exact Reach.extend step (Reach.mapPin p bit k (op.on a b :: bank) rest)

private theorem eq_of_xor_false {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

private theorem restriction_constant {n : Nat} {p : Fin n} {bit : Bool} {f}
    (collapsed : pin p bit f = zero) (x : Fin n → Bool) :
    f (setRaw p bit x) = f (setRaw p bit (fun _ => false)) :=
  eq_of_xor_false (congrFun collapsed x)

private theorem normalize_unary {X : Type} (origin : X) (g : Bool → Bool) (f : Signal X) :
    normalizeAt origin (fun x => g (f x)) = zero ∨
      normalizeAt origin (fun x => g (f x)) = normalizeAt origin f := by
  cases a : g false <;> cases b : g true
  · left
    funext x
    cases hx : f x <;> cases h0 : f origin <;> simp [normalizeAt, zero, a, b, hx, h0]
  · right
    funext x
    cases hx : f x <;> cases h0 : f origin <;> simp [normalizeAt, a, b, hx, h0]
  · right
    funext x
    cases hx : f x <;> cases h0 : f origin <;> simp [normalizeAt, a, b, hx, h0]
  · left
    funext x
    cases hx : f x <;> cases h0 : f origin <;> simp [normalizeAt, zero, a, b, hx, h0]

theorem pin_absorb_left {n : Nat} {p : Fin n} {bit : Bool}
    {a b : Signal (Fin n → Bool)} (op : Op) (collapse : pin p bit a = zero) :
    pin p bit (op.on a b) = zero ∨ pin p bit (op.on a b) = pin p bit b := by
  unfold pin
  have replace :
      (fun x => op.on a b (setRaw p bit x)) =
        fun x => op.eval (a (setRaw p bit (fun _ => false))) (b (setRaw p bit x)) := by
    funext x
    rw [Op.on, restriction_constant collapse x]
  rw [replace]
  exact normalize_unary (fun _ => false) (op.eval (a (setRaw p bit (fun _ => false)))) _

theorem pin_absorb_right {n : Nat} {p : Fin n} {bit : Bool}
    {a b : Signal (Fin n → Bool)} (op : Op) (collapse : pin p bit b = zero) :
    pin p bit (op.on a b) = zero ∨ pin p bit (op.on a b) = pin p bit a := by
  unfold pin
  have replace :
      (fun x => op.on a b (setRaw p bit x)) =
        fun x => op.eval (a (setRaw p bit x)) (b (setRaw p bit (fun _ => false))) := by
    funext x
    rw [Op.on, restriction_constant collapse x]
  rw [replace]
  exact normalize_unary (fun _ => false) (fun a => op.eval a (b (setRaw p bit (fun _ => false)))) _

private theorem target_not_initial {n : Nat} {p : Fin n} {bit : Bool}
    {f : Signal (Fin n → Bool)} {bank : List (Signal (Fin n → Bool))}
    (needed : ¬ Independent p f) (nonzero : pin p bit f ≠ zero) (good : PinBank p bank) :
    f ∉ bank := by
  intro present
  rcases good.2 f present with isRaw | stable
  · exact nonzero (by rw [isRaw]; exact pin_raw p bit)
  · exact needed stable.1

private theorem pin_drop_dead {n : Nat} {p : Fin n} {bit : Bool} {f : Signal (Fin n → Bool)}
    (needed : ¬ Independent p f) (nonzero : pin p bit f ≠ zero)
    (k : Nat) (bank : List (Signal (Fin n → Bool))) (dead : Signal (Fin n → Bool))
    (good : PinBank p bank) (gone : pin p bit dead = zero) (reach : Reach f k (dead :: bank)) :
    ∃ left, k = left + 1 ∧ Reach (pin p bit f) left bank := by
  have notIn (B : List (Signal (Fin n → Bool))) (G : PinBank p B) : f ∉ dead :: B := by
    intro present
    rcases List.mem_cons.mp present with same | inBank
    · exact nonzero (by rw [same]; exact gone)
    · exact target_not_initial needed nonzero G inBank
  induction k generalizing bank with
  | zero => exact (notIn bank good reach).elim
  | succ k ih =>
    rcases reach with here | ⟨_, ⟨op, a, ha, b, hb, rfl⟩, tail⟩
    · exact (notIn bank good here).elim
    have status (u : Signal (Fin n → Bool)) (hu : u ∈ dead :: bank) :
        pin p bit u = zero ∨ (u ∈ bank ∧ Stable p u) := by
      rcases List.mem_cons.mp hu with same | old
      · exact Or.inl (by rw [same]; exact gone)
      · rcases good.2 u old with fromRaw | stable
        · exact Or.inl (by rw [fromRaw]; exact pin_raw p bit)
        · exact Or.inr ⟨old, stable⟩
    have hasPin (u : Signal (Fin n → Bool)) (hu : u ∈ dead :: bank) : pin p bit u ∈ bank := by
      rcases status u hu with collapsed | ⟨member, stable⟩
      · rw [collapsed]
        exact good.1
      · rw [pin_stable stable]
        exact member
    have collapseNext (h : pin p bit (op.on a b) ∈ bank) :
        ∃ left, k + 1 = left + 1 ∧ Reach (pin p bit f) left bank := by
      refine ⟨k, rfl, ?_⟩
      apply Reach.weakenBank k _ bank _ (Reach.mapPin p bit k (op.on a b :: dead :: bank) tail)
      intro g hg
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
      rcases List.mem_cons.mp hu with same | other
      · rw [same]; exact h
      · exact hasPin u other
    rcases status a ha with aGone | ⟨aHere, aStable⟩
    · apply collapseNext
      rcases pin_absorb_left op aGone with resolved | keepsB
      · rw [resolved]
        exact good.1
      · rw [keepsB]
        exact hasPin b hb
    · rcases status b hb with bGone | ⟨bHere, bStable⟩
      · apply collapseNext
        rcases pin_absorb_right op bGone with resolved | keepsA
        · rw [resolved]
          exact good.1
        · rw [keepsA]
          exact hasPin a ha
      · have tailSwapped : Reach f k (dead :: op.on a b :: bank) :=
          Reach.weakenBank k _ _ (by intro u hu; simpa [or_comm, or_left_comm] using hu) tail
        obtain ⟨left, size, run⟩ :=
          ih (op.on a b :: bank) (good.consStable (aStable.op bStable op)) tailSwapped
        exact ⟨left + 1, by omega, Reach.extend ⟨op, a, aHere, b, bHere, rfl⟩ run⟩

theorem reach_pin_loses_one {n : Nat} (p : Fin n) (bit : Bool) (f : Signal (Fin n → Bool))
    (needed : ¬ Independent p f) (nonzero : pin p bit f ≠ zero)
    (k : Nat) (bank : List (Signal (Fin n → Bool))) (good : PinBank p bank) (reach : Reach f k bank) :
    ∃ left, k = left + 1 ∧ Reach (pin p bit f) left bank := by
  apply pin_drop_dead needed nonzero k bank zero good (by exact phase_const _ _)
  exact Reach.weakenBank k bank (zero :: bank) (fun _ => List.mem_cons_of_mem _) reach

private def leftKill : Op → Bool
  | .conj => false
  | .disj => true
  | .diff => false

private def rightKill : Op → Bool
  | .conj => false
  | .disj => true
  | .diff => true

private theorem pin_raw_left_kills {n : Nat} (p : Fin n) (b : Signal (Fin n → Bool)) (op : Op) :
    pin p (leftKill op) (op.on (raw p) b) = zero := by
  have evals (x : Bool) : op.eval (leftKill op) x = op.eval (leftKill op) false := by
    cases op <;> cases x <;> rfl
  have constant : (fun x => op.on (raw p) b (setRaw p (leftKill op) x)) =
      fun _ => op.eval (leftKill op) false := by
    funext x
    simpa [Op.on, raw, setRaw] using evals (b (setRaw p (leftKill op) x))
  unfold pin
  rw [constant]
  exact phase_const _ _

private theorem pin_raw_right_kills {n : Nat} (p : Fin n) (a : Signal (Fin n → Bool)) (op : Op) :
    pin p (rightKill op) (op.on a (raw p)) = zero := by
  have evals (x : Bool) : op.eval x (rightKill op) = op.eval false (rightKill op) := by
    cases op <;> cases x <;> rfl
  have constant : (fun x => op.on a (raw p) (setRaw p (rightKill op) x)) =
      fun _ => op.eval false (rightKill op) := by
    funext x
    simpa [Op.on, raw, setRaw] using evals (a (setRaw p (rightKill op) x))
  unfold pin
  rw [constant]
  exact phase_const _ _

theorem reach_pin_loses_two {n : Nat} (p : Fin n) (f : Signal (Fin n → Bool))
    (needed : ¬ Independent p f) (nonzero : ∀ bit, pin p bit f ≠ zero)
    (k : Nat) (bank : List (Signal (Fin n → Bool))) (good : PinBank p bank) (reach : Reach f k bank) :
    ∃ left, k = left + 2 ∧ ∃ bit, Reach (pin p bit f) left bank := by
  induction k generalizing bank with
  | zero => exact (target_not_initial needed (nonzero false) good reach).elim
  | succ k ih =>
    rcases reach with here | ⟨_, ⟨op, a, ha, b, hb, rfl⟩, tail⟩
    · exact (target_not_initial needed (nonzero false) good here).elim
    have finish (bit : Bool) (gone : pin p bit (op.on a b) = zero) :
        ∃ left, k + 1 = left + 2 ∧ ∃ bit, Reach (pin p bit f) left bank := by
      obtain ⟨left, size, run⟩ := pin_drop_dead needed (nonzero bit) k bank (op.on a b) good gone tail
      exact ⟨left, by omega, bit, run⟩
    rcases good.2 a ha with leftRaw | leftStable
    · exact finish (leftKill op) (by rw [leftRaw]; exact pin_raw_left_kills p b op)
    · rcases good.2 b hb with rightRaw | rightStable
      · exact finish (rightKill op) (by rw [rightRaw]; exact pin_raw_right_kills p a op)
      · obtain ⟨left, size, bit, run⟩ := ih (op.on a b :: bank)
          (good.consStable (leftStable.op rightStable op)) tail
        exact ⟨left + 1, by omega, bit, Reach.extend ⟨op, a, ha, b, hb, rfl⟩ run⟩

theorem pin_canMake {n : Nat} (p : Fin n) (bit : Bool)
    {bank : List (Signal (Fin n → Bool))} {v : Signal (Fin n → Bool)}
    (move : CanMake bank v) : CanMake (bank.map (pin p bit)) (pin p bit v) := by
  obtain ⟨op, a, ha, b, hb, rfl⟩ := move
  exact phaseOp (fun _ => false) op (fun x => a (setRaw p bit x)) (fun x => b (setRaw p bit x))
    _ (List.mem_map.mpr ⟨a, ha, rfl⟩) (List.mem_map.mpr ⟨b, hb, rfl⟩)

theorem Reach.pin_loses_of_difference {n : Nat} {p : Fin n} {bit : Bool}
    {f : Signal (Fin n → Bool)} (x y : Fin n → Bool) (different : f x ≠ f y)
    (nonzero : pin p bit f ≠ zero) (k : Nat) (bank : List (Signal (Fin n → Bool)))
    (hasZero : zero ∈ bank.map (pin p bit))
    (track : ∀ v ∈ bank, v x ≠ v y → pin p bit v = zero) (reach : Reach f k bank) :
    ∃ left, k = left + 1 ∧ Reach (pin p bit f) left (bank.map (pin p bit)) := by
  induction k generalizing bank with
  | zero => exact (nonzero (track f reach different)).elim
  | succ k ih =>
    rcases reach with here | ⟨_, ⟨op, a, ha, b, hb, rfl⟩, rest⟩
    · exact (nonzero (track f here different)).elim
    let next := op.on a b
    have liftMember (u : Signal (Fin n → Bool)) (hu : u ∈ bank) :
        pin p bit u ∈ bank.map (pin p bit) :=
      List.mem_map.mpr ⟨u, hu, rfl⟩
    by_cases nextDiff : next x ≠ next y
    · have saved : pin p bit next ∈ bank.map (pin p bit) := by
        by_cases aDiff : a x ≠ a y
        · rcases pin_absorb_left op (track a ha aDiff) with h | h
          · rw [show next = op.on a b from rfl, h]
            exact hasZero
          · rw [show next = op.on a b from rfl, h]
            exact liftMember b hb
        · have bDiff : b x ≠ b y := by
            intro bSame
            apply nextDiff
            change op.eval (a x) (b x) = op.eval (a y) (b y)
            rw [not_not.mp aDiff, bSame]
          rcases pin_absorb_right op (track b hb bDiff) with h | h
          · rw [show next = op.on a b from rfl, h]
            exact hasZero
          · rw [show next = op.on a b from rfl, h]
            exact liftMember a ha
      refine ⟨k, rfl, ?_⟩
      have mapped := Reach.mapPin p bit k (next :: bank) rest
      apply Reach.weakenBank k _ _ _ mapped
      intro u hu
      change u ∈ pin p bit next :: bank.map (pin p bit) at hu
      rcases List.mem_cons.mp hu with same | previous
      · rw [same]
        exact saved
      · exact previous
    · have stillZero : zero ∈ (next :: bank).map (pin p bit) :=
        List.mem_cons_of_mem _ hasZero
      have stillTracks (v : Signal (Fin n → Bool)) (member : v ∈ next :: bank)
          (diff : v x ≠ v y) : pin p bit v = zero := by
        rcases List.mem_cons.mp member with same | previous
        · exact (nextDiff (by rwa [same] at diff)).elim
        · exact track v previous diff
      obtain ⟨left, size, shortened⟩ := ih (next :: bank) stillZero stillTracks rest
      have keep : CanMake (bank.map (pin p bit)) (pin p bit next) :=
        pin_canMake p bit ⟨op, a, ha, b, hb, rfl⟩
      exact ⟨left + 1, by omega, Reach.extend keep shortened⟩

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

theorem Reach.precompose {X Y : Type} {f : Signal X} (input : Y → X) :
    ∀ k bank, Reach f k bank →
      Reach (fun y => f (input y)) k (bank.map (fun g y => g (input y)))
  | 0, _, here => List.mem_map.mpr ⟨f, here, rfl⟩
  | k + 1, bank, reach => by
    rcases reach with here | ⟨_, ⟨op, a, ha, b, hb, rfl⟩, rest⟩
    · exact Reach.here (List.mem_map.mpr ⟨f, here, rfl⟩)
    · apply Reach.extend
        ⟨op, (fun y => a (input y)), List.mem_map.mpr ⟨a, ha, rfl⟩,
          (fun y => b (input y)), List.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩
      exact Reach.precompose input k (op.on a b :: bank) rest

def expandInputs {n m : Nat} (project : Fin n → Option (Fin m)) (x : Fin m → Bool) :
    Fin n → Bool :=
  fun i => (project i).elim false x

theorem reach_expand_inputs {n m : Nat} (project : Fin n → Option (Fin m))
    {f : Signal (Fin n → Bool)} {k : Nat} (reach : Reach f k (base n)) :
    Reach (fun x => f (expandInputs project x)) k (base m) := by
  have mapped := Reach.precompose (expandInputs project) k (base n) reach
  apply Reach.weakenBank k _ (base m) _ mapped
  intro signal member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rcases List.mem_cons.mp present with rfl | presentRaw
  · exact List.mem_cons_self
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp presentRaw
  cases hx : project i with
  | none =>
    have same : (fun x => expandInputs project x i) = zero := by
      funext x
      simp [expandInputs, hx, zero]
    rw [same]
    exact List.mem_cons_self
  | some j =>
    have same : (fun x => expandInputs project x i) = fun x => x j := by
      funext x
      simp [expandInputs, hx]
    rw [same]
    exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

def projectSix28882 : Fin 8 → Option (Fin 6) :=
  ![some 0, some 1, none, none, some 2, some 3, some 4, some 5]

abbrev expandSix28882 := expandInputs projectSix28882

theorem reach_to_six28882 {f : Signal (Fin 8 → Bool)} {k : Nat}
    (reach : Reach f k (base 8)) :
    Reach (fun x => f (expandSix28882 x)) k (base 6) :=
  reach_expand_inputs projectSix28882 reach

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

inductive Live {X : Type} [DecidableEq (Signal X)] (f : Signal X) :
    Nat → Finset (Signal X) → Prop where
  | done : Live f 0 {f}
  | step {k : Nat} {after : Finset (Signal X)} (op : Op) (a b : Signal X)
      (needed : op.on a b ∈ after) (different : a ≠ b)
      (freshA : a ≠ op.on a b) (freshB : b ≠ op.on a b)
      (rest : Live f k after) :
      Live f (k + 1) (insert a (insert b (after.erase (op.on a b))))

theorem Live.agrees {X : Type} [DecidableEq (Signal X)] {f : Signal X}
    {k : Nat} {live : Finset (Signal X)} (run : Live f k live) (x y : X)
    (agrees : ∀ s ∈ live, s x = s y) : f x = f y := by
  induction run with
  | done => exact agrees f (Finset.mem_singleton_self _)
  | @step k after op a b needed distinct freshA freshB rest ih =>
    apply ih
    intro s hs
    by_cases made : s = op.on a b
    · have left : a x = a y := agrees a (Finset.mem_insert_self _ _)
      have right : b x = b y := agrees b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      subst s
      change op.eval (a x) (b x) = op.eval (a y) (b y)
      rw [left, right]
    · exact agrees s (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨made, hs⟩)))

theorem Live.card_le {X : Type} [DecidableEq (Signal X)] {f : Signal X}
    {k : Nat} {live : Finset (Signal X)} (run : Live f k live) : live.card ≤ k + 1 := by
  induction run with
  | done => simp
  | @step k after op a b needed distinct freshA freshB rest ih =>
    have upperA := Finset.card_insert_le a (insert b (after.erase (op.on a b)))
    have upperB := Finset.card_insert_le b (after.erase (op.on a b))
    have erased := Finset.card_erase_of_mem needed
    have positive : 0 < after.card := Finset.card_pos.mpr ⟨op.on a b, needed⟩
    omega

private theorem ineffective {X : Type} (op : Op) (a b : Signal X)
    (degenerate : a = zero ∨ b = zero ∨ a = b) :
    op.on a b = zero ∨ op.on a b = a ∨ op.on a b = b := by
  rcases degenerate with rfl | rfl | rfl
  · cases op
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
  · cases op
    · exact Or.inl (by funext x; simp [Op.on, Op.eval, zero])
    · exact Or.inr (Or.inl (by funext x; simp [Op.on, Op.eval, zero]))
    · exact Or.inr (Or.inl (by funext x; simp [Op.on, Op.eval, zero]))
  · cases op
    · exact Or.inr (Or.inl (by funext x; simp [Op.on, Op.eval]))
    · exact Or.inr (Or.inl (by funext x; simp [Op.on, Op.eval]))
    · exact Or.inl (by funext x; simp [Op.on, Op.eval, zero])

theorem Reach.live {X : Type} [DecidableEq (Signal X)] {f : Signal X}
    (nonzero : f ≠ zero) (k : Nat) (bank : List (Signal X)) (hz : zero ∈ bank)
    (reach : Reach f k bank) :
    ∃ steps ≤ k, ∃ live : Finset (Signal X), Live f steps live ∧
      (∀ v ∈ live, v ∈ bank) ∧ zero ∉ live := by
  have finish (j : Nat) (B : List (Signal X)) (present : f ∈ B) :
      ∃ steps ≤ j, ∃ live : Finset (Signal X), Live f steps live ∧
        (∀ v ∈ live, v ∈ B) ∧ zero ∉ live := by
    refine ⟨0, Nat.zero_le _, {f}, .done, ?_, ?_⟩
    · intro v hv
      rw [Finset.mem_singleton.mp hv]
      exact present
    · simpa using Ne.symm nonzero
  induction k generalizing bank with
  | zero => exact finish 0 bank reach
  | succ k ih =>
    rcases reach with present | ⟨s, ⟨op, a, ha, b, hb, rfl⟩, rest⟩
    · exact finish (k + 1) bank present
    let s := op.on a b
    obtain ⟨steps, bound, after, run, use, noZero⟩ :=
      ih (s :: bank) (List.mem_cons_of_mem _ hz) rest
    by_cases old : s ∈ bank
    · refine ⟨steps, by omega, after, run, ?_, noZero⟩
      intro v hv
      rcases List.mem_cons.mp (use v hv) with same | prev
      · rwa [same]
      · exact prev
    by_cases needed : s ∈ after
    · have aFresh : a ≠ s := by intro eq; exact old (eq ▸ ha)
      have bFresh : b ≠ s := by intro eq; exact old (eq ▸ hb)
      have degenerate : ¬ (a = zero ∨ b = zero ∨ a = b) := by
        intro degenerate
        apply old
        rcases ineffective op a b degenerate with const | same | same
        · rw [show s = op.on a b from rfl, const]
          exact hz
        · rw [show s = op.on a b from rfl, same]
          exact ha
        · rw [show s = op.on a b from rfl, same]
          exact hb
      have distinct : a ≠ b := fun eq => degenerate (Or.inr (Or.inr eq))
      have aLive : a ≠ zero := fun eq => degenerate (Or.inl eq)
      have bLive : b ≠ zero := fun eq => degenerate (Or.inr (Or.inl eq))
      refine ⟨steps + 1, by omega, insert a (insert b (after.erase s)),
        .step op a b needed distinct aFresh bFresh run, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with same | other
        · rwa [same]
        rcases Finset.mem_insert.mp other with same | other
        · rwa [same]
        obtain ⟨unequal, still⟩ := Finset.mem_erase.mp other
        exact (List.mem_cons.mp (use v still)).resolve_left unequal
      · intro member
        rcases Finset.mem_insert.mp member with same | other
        · exact aLive same.symm
        rcases Finset.mem_insert.mp other with same | other
        · exact bLive same.symm
        exact noZero (Finset.mem_of_mem_erase other)
    · refine ⟨steps, by omega, after, run, ?_, noZero⟩
      intro v hv
      rcases List.mem_cons.mp (use v hv) with same | prev
      · exact (needed (same ▸ hv)).elim
      · exact prev

theorem Live.initial_of_essential {X : Type} [DecidableEq (Signal X)]
    {n : Nat} {f : Signal X} {k : Nat} {live : Finset (Signal X)}
    (run : Live f k live) (raw : Fin n → Signal X)
    (start : ∀ v ∈ live, v ∈ zero :: List.ofFn raw) (noZero : zero ∉ live)
    (essential : ∀ i, ∃ x y, f x ≠ f y ∧ ∀ j, j ≠ i → raw j x = raw j y) :
    live = Finset.univ.image raw := by
  apply Finset.ext
  intro v
  constructor
  · intro present
    rcases List.mem_cons.mp (start v present) with same | fromInput
    · exact (noZero (same ▸ present)).elim
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp fromInput
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro fromInput
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp fromInput
    by_contra absent
    obtain ⟨x, y, diff, other⟩ := essential i
    apply diff
    apply run.agrees x y
    intro w hw
    rcases List.mem_cons.mp (start w hw) with same | fromOther
    · exact (noZero (same ▸ hw)).elim
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp fromOther
      exact other j (fun same => absent (same ▸ hw))

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.PhaseBank

inductive Op where
  | and | or | diff
  deriving BEq, DecidableEq, Repr

structure Action where
  op : Op
  lhs : Nat
  rhs : Nat
  dropL : Bool
  dropR : Bool
  deriving Repr

structure Problem where
  full : Nat
  target : Nat
  cap : Nat
  initial : List Nat
  positive : List Nat

def encode (signature : Nat) (marked : Bool) : Nat :=
  2 * signature + (if marked then 1 else 0)

def bits (wire : Nat) : Nat := wire / 2

def critical (wire : Nat) : Bool := wire % 2 == 1

private def insertOrdered (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: rest => if a ≤ b then a :: b :: rest else b :: insertOrdered a rest

def canonical : List Nat → List Nat
  | [] => []
  | a :: rest => insertOrdered a (canonical rest)

private theorem insertOrdered_perm (a : Nat) (bank : List Nat) :
    (insertOrdered a bank).Perm (a :: bank) := by
  induction bank with
  | nil => rfl
  | cons b rest ih =>
    simp only [insertOrdered]
    split
    · rfl
    · exact (ih.cons b).trans (.swap a b rest)

theorem canonical_perm (bank : List Nat) : (canonical bank).Perm bank := by
  induction bank with
  | nil => rfl
  | cons a rest ih => exact (insertOrdered_perm a (canonical rest)).trans (ih.cons a)

private theorem insertOrdered_sorted (a : Nat) {bank : List Nat}
    (sorted : bank.Pairwise (· ≤ ·)) : (insertOrdered a bank).Pairwise (· ≤ ·) := by
  induction bank with
  | nil => simp [insertOrdered]
  | cons b rest ih =>
    rw [List.pairwise_cons] at sorted
    simp only [insertOrdered]
    split
    · rename_i ab
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, sorted⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | found
      · exact ab
      · exact Nat.le_trans ab (sorted.1 x found)
    · rename_i ab
      rw [List.pairwise_cons]
      refine ⟨?_, ih sorted.2⟩
      intro x hx
      have found := (insertOrdered_perm a rest).mem_iff.mp hx
      rcases List.mem_cons.mp found with rfl | found
      · omega
      · exact sorted.1 x found

theorem canonical_sorted (bank : List Nat) : (canonical bank).Pairwise (· ≤ ·) := by
  induction bank with
  | nil => simp [canonical]
  | cons a rest ih => exact insertOrdered_sorted a ih

theorem canonical_eq_of_perm {a b : List Nat} (same : a.Perm b) :
    canonical a = canonical b :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba)
    (canonical_sorted a) (canonical_sorted b)
    ((canonical_perm a).trans (same.trans (canonical_perm b).symm))

def permitted (a : Action) : Bool :=
  (!critical a.lhs || (a.dropL && a.op == .or)) &&
  (!critical a.rhs || (a.dropR && a.op != .and))

def allowed (bank : List Nat) (a : Action) : Prop :=
  a.lhs ∈ bank ∧ a.rhs ∈ bank.erase a.lhs ∧ permitted a = true

def eval (p : Problem) (op : Op) (left right : Nat) : Nat :=
  match op with
  | .and => left &&& right
  | .or => left ||| right
  | .diff => left &&& (p.full ^^^ right)

def discard (bank : List Nat) (wire : Nat) (drop : Bool) : List Nat :=
  if drop then bank.erase wire else bank

def rawPerform (p : Problem) (bank : List Nat) (a : Action) : List Nat :=
  encode (eval p a.op (bits a.lhs) (bits a.rhs)) false ::
    discard (discard bank a.lhs a.dropL) a.rhs a.dropR

def perform (p : Problem) (bank : List Nat) (a : Action) : List Nat :=
  canonical (rawPerform p bank a)

def negativeMask (p : Problem) : Nat := p.full &&& (p.full ^^^ p.target)

theorem negativeMask_bit (p : Problem) (row : Nat) :
    (negativeMask p).testBit row = true ↔
      p.full.testBit row = true ∧ p.target.testBit row = false := by
  cases hf : p.full.testBit row <;> cases ht : p.target.testBit row <;>
    simp [negativeMask, Nat.testBit_and, Nat.testBit_xor, hf, ht]

private def conflicts (p : Problem) (yes : Nat) : List Nat → Nat → Nat
  | [], remaining => remaining
  | wire :: bank, remaining =>
    let signature := bits wire
    let agrees := if signature.testBit yes then signature else p.full ^^^ signature
    conflicts p yes bank (remaining &&& agrees)

private theorem conflicts_emptyBit (p : Problem) (yes no : Nat)
    (bank : List Nat) (remaining : Nat) (absent : remaining.testBit no = false) :
    (conflicts p yes bank remaining).testBit no = false := by
  induction bank generalizing remaining with
  | nil => exact absent
  | cons wire bank ih =>
    simp only [conflicts]
    apply ih
    simp [Nat.testBit_and, absent]

private theorem conflicts_bit (p : Problem) (yes no : Nat)
    (bank : List Nat) (remaining : Nat) (full : p.full.testBit no = true) :
    (conflicts p yes bank remaining).testBit no = true ↔
      remaining.testBit no = true ∧
        ∀ wire ∈ bank, (bits wire).testBit yes = (bits wire).testBit no := by
  induction bank generalizing remaining with
  | nil => simp [conflicts]
  | cons wire bank ih =>
    simp only [conflicts, ih, List.mem_cons, forall_eq_or_imp]
    have agree :
        ((if (bits wire).testBit yes then bits wire else p.full ^^^ bits wire).testBit no = true) ↔
          (bits wire).testBit yes = (bits wire).testBit no := by
      cases hy : (bits wire).testBit yes <;> cases hn : (bits wire).testBit no <;>
        simp [Nat.testBit_xor, full, hn]
    simp [Nat.testBit_and, agree, and_assoc]

def separated (p : Problem) (bank : List Nat) : Bool :=
  let mask := negativeMask p
  p.positive.all fun yes => conflicts p yes bank mask == 0

theorem separated_iff (p : Problem) (bank : List Nat) :
    separated p bank = true ↔
      ∀ yes ∈ p.positive, ∀ no, p.full.testBit no = true → p.target.testBit no = false →
        ∃ wire ∈ bank, (bits wire).testBit yes ≠ (bits wire).testBit no := by
  classical
  simp only [separated, List.all_eq_true, beq_iff_eq]
  constructor
  · intro check yes hYes no hFull hNo
    apply Classical.byContradiction
    intro absent
    have on := (negativeMask_bit p no).2 ⟨hFull, hNo⟩
    have allAgree (wire : Nat) (mem : wire ∈ bank) :
        (bits wire).testBit yes = (bits wire).testBit no :=
      Classical.byContradiction (fun diff => absent ⟨wire, mem, diff⟩)
    have conflict := (conflicts_bit p yes no bank (negativeMask p) hFull).2 ⟨on, allAgree⟩
    rw [check yes hYes] at conflict
    simp at conflict
  · intro valid yes hYes
    apply Nat.eq_of_testBit_eq
    intro no
    simp only [Nat.zero_testBit]
    cases neg : (negativeMask p).testBit no
    · exact conflicts_emptyBit p yes no bank _ neg
    · have labels := (negativeMask_bit p no).1 neg
      obtain ⟨wire, found, diff⟩ := valid yes hYes no labels.1 labels.2
      apply Bool.eq_false_iff.mpr
      intro conflict
      exact diff ((conflicts_bit p yes no bank (negativeMask p) labels.1).1 conflict |>.2 wire found)

def solved (p : Problem) (bank : List Nat) : Bool :=
  bank.any fun wire => bits wire == p.target

def within (p : Problem) (depth : Nat) (bank : List Nat) : Bool :=
  decide (depth < p.cap) && decide (depth + (bank.length - 1) ≤ p.cap)

def eligible (p : Problem) (depth : Nat) (bank : List Nat) : Bool :=
  solved p bank || (within p depth bank && separated p bank)

private def booleans : List Bool := [false, true]
private def ops : List Op := [.and, .or, .diff]

def actions (bank : List Nat) : List Action :=
  (bank.flatMap fun a => (bank.erase a).flatMap fun b =>
    ops.flatMap fun op => booleans.flatMap fun da => booleans.map fun db =>
      ⟨op, a, b, da, db⟩).filter permitted

private theorem mem_booleans (value : Bool) : value ∈ booleans := by
  cases value <;> decide

private theorem mem_ops (op : Op) : op ∈ ops := by
  cases op <;> simp [ops]

theorem action_mem {bank : List Nat} {a : Action} (ok : allowed bank a) :
    a ∈ actions bank := by
  rcases a with ⟨op, lhs, rhs, dl, dr⟩
  obtain ⟨hl, hr, pass⟩ := ok
  refine List.mem_filter.mpr ⟨?_, pass⟩
  exact List.mem_flatMap.mpr ⟨lhs, hl, List.mem_flatMap.mpr ⟨rhs, hr,
    List.mem_flatMap.mpr ⟨op, mem_ops op, List.mem_flatMap.mpr
      ⟨dl, mem_booleans dl, List.mem_map.mpr ⟨dr, mem_booleans dr, rfl⟩⟩⟩⟩⟩

inductive Reach (p : Problem) : Nat → List Nat → Prop where
  | root : Reach p 0 (canonical p.initial)
  | step {depth : Nat} {bank : List Nat} (path : Reach p depth bank) (below : depth < p.cap)
      (a : Action) (ok : allowed bank a) (keep : eligible p (depth + 1) (perform p bank a) = true) :
      Reach p (depth + 1) (perform p bank a)

def stateCheck (p : Problem) (layers : Nat → List (List Nat))
    (depth : Nat) (bank : List Nat) : Bool :=
  !solved p bank &&
    (if depth < p.cap then
      (actions bank).all fun a =>
        let next := perform p bank a
        !eligible p (depth + 1) next || (layers (depth + 1)).contains next
    else true)

theorem closure_sound (p : Problem) (layers : Nat → List (List Nat))
    (start : canonical p.initial ∈ layers 0)
    (check : ∀ depth ≤ p.cap, (layers depth).all (stateCheck p layers depth) = true)
    {depth : Nat} {bank : List Nat} (path : Reach p depth bank) : solved p bank = false := by
  have membership (d : Nat) (s : List Nat) (reachable : Reach p d s) :
      d ≤ p.cap ∧ s ∈ layers d := by
    induction reachable with
    | root => exact ⟨Nat.zero_le _, start⟩
    | @step d s _ lt a ok keep ih =>
      have checkedState := List.all_eq_true.mp (check d ih.1) s ih.2
      simp only [stateCheck, Bool.and_eq_true, ite_eq_left lt, List.all_eq_true] at checkedState
      have next := checkedState.2 a (action_mem ok)
      exact ⟨Nat.succ_le_of_lt lt, by simpa [keep] using next⟩
  have mem := membership depth bank path
  have checked := List.all_eq_true.mp (check depth mem.1) bank mem.2
  simp only [stateCheck, Bool.and_eq_true] at checked
  simpa using checked.1

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.PhaseBank

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.PhaseBank

def smallStrong : Problem := {
  full := 4294967295
  target := 4278119592
  cap := 6
  initial := [5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
  positive := [3, 5, 10, 17, 18, 20, 7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 15, 23, 27, 29, 30, 31]
}

private def PhaseBankStrong_bank0_0 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank1_0 : List (List Nat) := [
  [4581298448, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8017272284, 8084644320, 8556510720, 8589803520],
  [1145324612, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2290649224, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5389762880, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8421504500, 8556510720, 8589803520],
  [336860180, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2694881440, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank1_1 : List (List Nat) := [
  [5704340480, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8578793300, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8578793300, 8589803520],
  [22282580, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2852170240, 5726623060, 6871947672, 8084644320, 8589803520],
  [2852170240, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726535680, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589890900]
]

private def PhaseBankStrong_bank1_2 : List (List Nat) := [
  [87380, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2863267840, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6467715456, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8488876536, 8556510720, 8589803520],
  [404232216, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [1616928864, 5726623060, 6871947672, 8556510720, 8589803520],
  [1616928864, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank1_3 : List (List Nat) := [
  [5726623060, 6845208576, 6871947672, 8084644320, 8589803520],
  [5726623060, 6845208576, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8583249816, 8589803520],
  [26739096, 5726623060, 6871947672, 8084644320, 8589803520],
  [26739096, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [1711302144, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871842816, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589908376]
]

private def PhaseBankStrong_bank1_4 : List (List Nat) := [
  [104856, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [1717960704, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8053186560, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8587968480, 8589803520],
  [31457760, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [503324160, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084520960, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589926880]
]

private def PhaseBankStrong_bank1_5 : List (List Nat) := [
  [123360, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [505282560, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556380160, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589934080],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589934080],
  [130560, 5726623060, 6871947672, 8084644320, 8589803520],
  [130560, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [33423360, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank2_0 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8354132464, 8556510720, 8589803520],
  [3772834016, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8574336784, 8589803520],
  [3993038336, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589873424],
  [4008574976, 5726623060, 6871947672, 8084644320, 8556510720],
  [6871947672, 8017272284, 8084644320, 8578793300, 8589803520]
]

private def PhaseBankStrong_bank2_1 : List (List Nat) := [
  [5726623060, 8017272284, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 7986076672, 8084644320, 8589803520],
  [31195612, 5726623060, 6871947672, 8084644320, 8589803520],
  [1145324612, 6871947672, 8084644320, 8578793300, 8589803520],
  [5726623060, 6871947672, 8084644320, 8560967236, 8589803520],
  [5726623060, 6871947672, 7415642624, 8084644320, 8589803520],
  [2290649224, 5726623060, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8219388392, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank2_2 : List (List Nat) := [
  [5726623060, 5928739168, 6871947672, 8556510720, 8589803520],
  [2281736192, 5726623060, 6871947672, 8084644320, 8589803520],
  [8913032, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 7949900248, 8084644320, 8556510720, 8589803520],
  [2560137368, 5726623060, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8577482560, 8589803520],
  [3187719680, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589885760]
]

private def PhaseBankStrong_bank2_3 : List (List Nat) := [
  [3200122880, 5726623060, 6871947672, 8084644320, 8556510720],
  [5726623060, 6871947672, 8084644320, 8557821460, 8589803520],
  [5726623060, 6871947672, 8084644320, 8220961280, 8589803520],
  [2852170240, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8578793300, 8589803520],
  [2852170240, 6871947672, 8084644320, 8578793300, 8589803520],
  [5726623060, 6871947672, 8488876536, 8578793300, 8589803520],
  [1616928864, 5726623060, 6871947672, 8578793300, 8589803520]
]

private def PhaseBankStrong_bank2_4 : List (List Nat) := [
  [5726623060, 6863034640, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589934420],
  [130900, 5726623060, 6871947672, 8084644320, 8589803520],
  [2852170240, 5726623060, 6871947672, 8488876536, 8589803520],
  [1616928864, 2852170240, 5726623060, 6871947672, 8589803520],
  [4590211480, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589847040],
  [43520, 5726623060, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank2_5 : List (List Nat) := [
  [5726535680, 6871947672, 8084644320, 8556510720, 8589890900],
  [5726623060, 8017254808, 8084644320, 8556510720, 8589803520],
  [2290719128, 5726623060, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8421499360, 8556510720, 8589803520],
  [2694963680, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8578792960, 8589803520],
  [2852257280, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084603200, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank2_6 : List (List Nat) := [
  [505287700, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556511060, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556423680, 8589803520],
  [5726623060, 6871947672, 8084644320, 8567651840, 8589803520],
  [5704384000, 5726623060, 6871947672, 8084644320, 8589803520],
  [1616928864, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6845208576, 8488876536, 8589803520],
  [5726623060, 6845208576, 8488876536, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank2_7 : List (List Nat) := [
  [5726623060, 6845208576, 6871947672, 8488876536, 8589803520],
  [26739096, 5726623060, 6871947672, 8488876536, 8589803520],
  [1711302144, 5726623060, 8488876536, 8556510720, 8589803520],
  [5726623060, 8488876536, 8556510720, 8589803520, 8589908376],
  [104856, 5726623060, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488876536, 8556510720, 8589803520],
  [1616928864, 5726623060, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488876536, 8589803520, 8589934080]
]

private def PhaseBankStrong_bank2_8 : List (List Nat) := [
  [130560, 5726623060, 6871947672, 8488876536, 8589803520],
  [5726623060, 6871947672, 8455845888, 8488876536, 8589803520],
  [33030648, 5726623060, 6871947672, 8488876536, 8589803520],
  [5726623060, 6845208576, 8084644320, 8488876536, 8589803520],
  [5726623060, 6871947672, 8084644320, 8455845888, 8589803520],
  [33030648, 5726623060, 6871947672, 8084644320, 8589803520],
  [404232216, 5726623060, 6845208576, 8084644320, 8589803520],
  [1616928864, 5726623060, 6845208576, 6871947672, 8589803520]
]

private def PhaseBankStrong_bank2_9 : List (List Nat) := [
  [26739096, 1616928864, 5726623060, 6871947672, 8589803520],
  [1616928864, 5726623060, 6871947672, 8589803520, 8589934080],
  [130560, 1616928864, 5726623060, 6871947672, 8589803520],
  [1616928864, 5726623060, 6871947672, 8562802272, 8589803520],
  [1616928864, 5726623060, 6871947672, 6945873408, 8589803520],
  [5726623060, 6871947672, 8084644320, 8562802272, 8589803520],
  [5726623060, 6871947672, 6945873408, 8084644320, 8589803520],
  [6871947672, 8008359252, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank2_10 : List (List Nat) := [
  [6845208576, 6871947672, 8008359252, 8084644320, 8589803520],
  [5726623060, 6871947672, 8008359252, 8084644320, 8589803520],
  [1163150676, 6845208576, 6871947672, 8084644320, 8589803520],
  [5726623060, 6845208576, 6871947672, 8084644320, 8589803520],
  [26739096, 5726623060, 6845208576, 8084644320, 8589803520],
  [26739096, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6845208576, 6871947672, 8487303648, 8589803520],
  [1642095072, 5726623060, 6845208576, 6871947672, 8589803520]
]

private def PhaseBankStrong_bank2_11 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8589907968],
  [5726623060, 6845208576, 6871947672, 8084644320, 8589907968],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589907968],
  [1744699392, 5726623060, 6845208576, 6871947672, 8084644320],
  [104448, 5726623060, 6871947672, 8084644320, 8589803520],
  [6871947672, 8008359252, 8084644320, 8556510720, 8589803520],
  [1163150676, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8487303648, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank2_12 : List (List Nat) := [
  [1642095072, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589907968],
  [1744699392, 5726623060, 6871947672, 8084644320, 8556510720],
  [5726623060, 5735536092, 6871947672, 8084644320, 8589803520],
  [26739096, 5726623060, 6871947672, 8086217208, 8589803520],
  [26739096, 5726623060, 6871947672, 8059478112, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589803928],
  [408, 5726623060, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank2_13 : List (List Nat) := [
  [5726623060, 6871947672, 8086217208, 8556510720, 8589803520],
  [5726623060, 6871947672, 8059478112, 8556510720, 8589803520],
  [6871947672, 8017237332, 8084644320, 8556510720, 8589803520],
  [1145394516, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488870368, 8556510720, 8589803520],
  [1617027552, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8583249408, 8589803520],
  [1711406592, 5726623060, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank2_14 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8589908376, 8589934080],
  [5726623060, 6871947672, 8084644320, 8556484608, 8589803520],
  [33423768, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084650488, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084545632, 8556510720, 8589803520],
  [1717960704, 5726623060, 6871947672, 8084644320, 8589934080],
  [5726623060, 6871947672, 8084644320, 8563195392, 8589803520],
  [5726623060, 6845234688, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank2_15 : List (List Nat) := [
  [5726623060, 6878239224, 8084644320, 8556510720, 8589803520],
  [5726623060, 6846781464, 8084644320, 8556510720, 8589803520],
  [6871947672, 8084644320, 8421463380, 8556510720, 8589803520],
  [336942420, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 8084644320, 8488851864, 8556510720, 8589803520],
  [404330904, 5726623060, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8587968000, 8589803520],
  [503447040, 5726623060, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank2_16 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8558476800, 8589803520],
  [5726623060, 6871947672, 8053194240, 8084644320, 8589803520],
  [130560, 5726623060, 6871947672, 8084644320, 8589803520],
  [2863311360, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947264, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589934080],
  [130560, 5726623060, 6871947672, 8084644320, 8589934080],
  [5726623060, 5726666580, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank2_17 : List (List Nat) := [
  [5726623060, 6871843224, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank3_0 : List (List Nat) := [
  [8017272284, 8488876536, 8578793300, 8589803520],
  [6871947672, 8008359252, 8084644320, 8589803520],
  [5726623060, 7986076672, 8488876536, 8589803520],
  [2281736192, 5726623060, 8488876536, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589838336],
  [5726623060, 6863034640, 8488876536, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589908240],
  [5726623060, 6871947536, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank3_1 : List (List Nat) := [
  [8017254808, 8084644320, 8556510720, 8589890900],
  [6871947672, 8421499360, 8556510720, 8589890900],
  [5726623060, 8488868312, 8556510720, 8589803520],
  [8008359252, 8488876536, 8589803520],
  [6845208576, 8008359252, 8488876536, 8589803520],
  [5726623060, 8008359252, 8488876536, 8589803520],
  [1163150676, 6845208576, 8488876536, 8589803520],
  [5726623060, 8488876536, 8589907968]
]

private def PhaseBankStrong_bank3_2 : List (List Nat) := [
  [5726623060, 6845208576, 8488876536, 8589907968],
  [5726623060, 8488876536, 8589803520, 8589907968],
  [1744699392, 5726623060, 6845208576, 8488876536],
  [104448, 5726623060, 8488876536, 8589803520],
  [5726623060, 6845208576, 8488876536, 8589803520],
  [1643667960, 5726623060, 6845208576, 8589803520],
  [1643667960, 5726623060, 8488876536, 8589803520],
  [8008359252, 8488876536, 8556510720, 8589803520]
]

private def PhaseBankStrong_bank3_3 : List (List Nat) := [
  [5726623060, 8488876536, 8556510720, 8589907968],
  [6871947672, 8008359252, 8488876536, 8589803520],
  [5726623060, 6871947672, 8488876536, 8589907968],
  [1643667960, 5726623060, 6871947672, 8589803520],
  [5726623060, 6871947672, 8462137440, 8589803520],
  [5726623060, 8488876536, 8589908376, 8589934080],
  [5726623060, 8488876536, 8556484608, 8589803520],
  [5726623060, 6945873408, 8488876536, 8589803520]
]

private def PhaseBankStrong_bank3_4 : List (List Nat) := [
  [5726623060, 6871947264, 8488876536, 8589803520],
  [8008359252, 8084644320, 8488876536, 8589803520],
  [5726623060, 8084644320, 8488876536, 8589907968],
  [404232216, 8008359252, 8084644320, 8589803520],
  [404232216, 5726623060, 8084644320, 8589907968],
  [1616928864, 6871947672, 8008359252, 8589803520],
  [1616928864, 5726623060, 6871947672, 8589907968],
  [6871947672, 8008359252, 8487303648, 8589803520]
]

private def PhaseBankStrong_bank3_5 : List (List Nat) := [
  [1642095072, 6871947672, 8008359252, 8589803520],
  [6871947672, 8008359252, 8084644320, 8589907968],
  [1744699392, 6871947672, 8008359252, 8084644320],
  [1163150676, 6871947672, 8084644320, 8589907968],
  [5726623060, 6871947672, 8084644320, 8589907968],
  [5726623060, 6845208576, 8086217208, 8589803520],
  [5726623060, 6871947672, 8487303648, 8589907968],
  [1642095072, 5726623060, 6871947672, 8589907968]
]

private def PhaseBankStrong_bank3_6 : List (List Nat) := [
  [5726657876, 6871947672, 8084644320, 8589803520],
  [6871947672, 8017272148, 8084644320, 8589803520]
]

private def PhaseBankStrong_bank4_0 : List (List Nat) := [
  [8008359252, 8488876536, 8589803520],
  [5726623060, 8488876536, 8589838336],
  [5726623060, 8488876536, 8589908240],
  [8008359252, 8488876536, 8589907968],
  [1744699392, 8008359252, 8488876536],
  [1163150676, 8488876536, 8589907968],
  [5726623060, 8488876536, 8589907968],
  [5726657876, 8488876536, 8589803520]
]

private def PhaseBankStrong_bank4_1 : List (List Nat) := [
  [8017272148, 8488876536, 8589803520]
]

private def PhaseBankStrong_pieces : Nat → List (List (List Nat))
  | 0 => [PhaseBankStrong_bank0_0]
  | 1 => [PhaseBankStrong_bank1_0, PhaseBankStrong_bank1_1, PhaseBankStrong_bank1_2, PhaseBankStrong_bank1_3, PhaseBankStrong_bank1_4, PhaseBankStrong_bank1_5]
  | 2 => [PhaseBankStrong_bank2_0, PhaseBankStrong_bank2_1, PhaseBankStrong_bank2_2, PhaseBankStrong_bank2_3, PhaseBankStrong_bank2_4, PhaseBankStrong_bank2_5, PhaseBankStrong_bank2_6, PhaseBankStrong_bank2_7, PhaseBankStrong_bank2_8, PhaseBankStrong_bank2_9, PhaseBankStrong_bank2_10, PhaseBankStrong_bank2_11, PhaseBankStrong_bank2_12, PhaseBankStrong_bank2_13, PhaseBankStrong_bank2_14, PhaseBankStrong_bank2_15, PhaseBankStrong_bank2_16, PhaseBankStrong_bank2_17]
  | 3 => [PhaseBankStrong_bank3_0, PhaseBankStrong_bank3_1, PhaseBankStrong_bank3_2, PhaseBankStrong_bank3_3, PhaseBankStrong_bank3_4, PhaseBankStrong_bank3_5, PhaseBankStrong_bank3_6]
  | 4 => [PhaseBankStrong_bank4_0, PhaseBankStrong_bank4_1]
  | _ => []

def smallStrongLayers (depth : Nat) : List (List Nat) := (PhaseBankStrong_pieces depth).flatten

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank0_0_checked : PhaseBankStrong_bank0_0.all (stateCheck smallStrong smallStrongLayers 0) = true := by
  decide +kernel

private theorem PhaseBankStrong_depth0_checked : (smallStrongLayers 0).all (stateCheck smallStrong smallStrongLayers 0) = true := by
  simp only [smallStrongLayers, PhaseBankStrong_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankStrong_bank0_0_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank1_0_checked : PhaseBankStrong_bank1_0.all (stateCheck smallStrong smallStrongLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank1_1_checked : PhaseBankStrong_bank1_1.all (stateCheck smallStrong smallStrongLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank1_2_checked : PhaseBankStrong_bank1_2.all (stateCheck smallStrong smallStrongLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank1_3_checked : PhaseBankStrong_bank1_3.all (stateCheck smallStrong smallStrongLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank1_4_checked : PhaseBankStrong_bank1_4.all (stateCheck smallStrong smallStrongLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank1_5_checked : PhaseBankStrong_bank1_5.all (stateCheck smallStrong smallStrongLayers 1) = true := by
  decide +kernel

private theorem PhaseBankStrong_depth1_checked : (smallStrongLayers 1).all (stateCheck smallStrong smallStrongLayers 1) = true := by
  simp only [smallStrongLayers, PhaseBankStrong_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankStrong_bank1_0_checked, PhaseBankStrong_bank1_1_checked, PhaseBankStrong_bank1_2_checked, PhaseBankStrong_bank1_3_checked, PhaseBankStrong_bank1_4_checked, PhaseBankStrong_bank1_5_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_0_checked : PhaseBankStrong_bank2_0.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_1_checked : PhaseBankStrong_bank2_1.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_2_checked : PhaseBankStrong_bank2_2.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_3_checked : PhaseBankStrong_bank2_3.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_4_checked : PhaseBankStrong_bank2_4.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_5_checked : PhaseBankStrong_bank2_5.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_6_checked : PhaseBankStrong_bank2_6.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_7_checked : PhaseBankStrong_bank2_7.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_8_checked : PhaseBankStrong_bank2_8.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_9_checked : PhaseBankStrong_bank2_9.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_10_checked : PhaseBankStrong_bank2_10.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_11_checked : PhaseBankStrong_bank2_11.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_12_checked : PhaseBankStrong_bank2_12.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_13_checked : PhaseBankStrong_bank2_13.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_14_checked : PhaseBankStrong_bank2_14.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_15_checked : PhaseBankStrong_bank2_15.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_16_checked : PhaseBankStrong_bank2_16.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank2_17_checked : PhaseBankStrong_bank2_17.all (stateCheck smallStrong smallStrongLayers 2) = true := by
  decide +kernel

private theorem PhaseBankStrong_depth2_checked : (smallStrongLayers 2).all (stateCheck smallStrong smallStrongLayers 2) = true := by
  simp only [smallStrongLayers, PhaseBankStrong_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankStrong_bank2_0_checked, PhaseBankStrong_bank2_1_checked, PhaseBankStrong_bank2_2_checked, PhaseBankStrong_bank2_3_checked, PhaseBankStrong_bank2_4_checked, PhaseBankStrong_bank2_5_checked, PhaseBankStrong_bank2_6_checked, PhaseBankStrong_bank2_7_checked, PhaseBankStrong_bank2_8_checked, PhaseBankStrong_bank2_9_checked, PhaseBankStrong_bank2_10_checked, PhaseBankStrong_bank2_11_checked, PhaseBankStrong_bank2_12_checked, PhaseBankStrong_bank2_13_checked, PhaseBankStrong_bank2_14_checked, PhaseBankStrong_bank2_15_checked, PhaseBankStrong_bank2_16_checked, PhaseBankStrong_bank2_17_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank3_0_checked : PhaseBankStrong_bank3_0.all (stateCheck smallStrong smallStrongLayers 3) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank3_1_checked : PhaseBankStrong_bank3_1.all (stateCheck smallStrong smallStrongLayers 3) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank3_2_checked : PhaseBankStrong_bank3_2.all (stateCheck smallStrong smallStrongLayers 3) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank3_3_checked : PhaseBankStrong_bank3_3.all (stateCheck smallStrong smallStrongLayers 3) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank3_4_checked : PhaseBankStrong_bank3_4.all (stateCheck smallStrong smallStrongLayers 3) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank3_5_checked : PhaseBankStrong_bank3_5.all (stateCheck smallStrong smallStrongLayers 3) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank3_6_checked : PhaseBankStrong_bank3_6.all (stateCheck smallStrong smallStrongLayers 3) = true := by
  decide +kernel

private theorem PhaseBankStrong_depth3_checked : (smallStrongLayers 3).all (stateCheck smallStrong smallStrongLayers 3) = true := by
  simp only [smallStrongLayers, PhaseBankStrong_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankStrong_bank3_0_checked, PhaseBankStrong_bank3_1_checked, PhaseBankStrong_bank3_2_checked, PhaseBankStrong_bank3_3_checked, PhaseBankStrong_bank3_4_checked, PhaseBankStrong_bank3_5_checked, PhaseBankStrong_bank3_6_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank4_0_checked : PhaseBankStrong_bank4_0.all (stateCheck smallStrong smallStrongLayers 4) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankStrong_bank4_1_checked : PhaseBankStrong_bank4_1.all (stateCheck smallStrong smallStrongLayers 4) = true := by
  decide +kernel

private theorem PhaseBankStrong_depth4_checked : (smallStrongLayers 4).all (stateCheck smallStrong smallStrongLayers 4) = true := by
  simp only [smallStrongLayers, PhaseBankStrong_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankStrong_bank4_0_checked, PhaseBankStrong_bank4_1_checked, Bool.and_self]

private theorem PhaseBankStrong_depth5_checked : (smallStrongLayers 5).all (stateCheck smallStrong smallStrongLayers 5) = true := by
  rfl

private theorem PhaseBankStrong_depth6_checked : (smallStrongLayers 6).all (stateCheck smallStrong smallStrongLayers 6) = true := by
  rfl

theorem smallStrong_no_solution {depth : Nat} {bank : List Nat}
    (path : Reach smallStrong depth bank) : solved smallStrong bank = false := by
  apply closure_sound smallStrong smallStrongLayers _ _ path
  · decide +kernel
  · intro depth limit
    change depth ≤ 6 at limit
    have options : depth = 0 ∨ depth = 1 ∨ depth = 2 ∨ depth = 3 ∨ depth = 4 ∨ depth = 5 ∨ depth = 6 := by omega
    rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact PhaseBankStrong_depth0_checked
    · exact PhaseBankStrong_depth1_checked
    · exact PhaseBankStrong_depth2_checked
    · exact PhaseBankStrong_depth3_checked
    · exact PhaseBankStrong_depth4_checked
    · exact PhaseBankStrong_depth5_checked
    · exact PhaseBankStrong_depth6_checked

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.PhaseBank

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.PhaseBank

def smallWeak : Problem := {
  full := 4294967295
  target := 4278120104
  cap := 6
  initial := [5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
  positive := [3, 5, 9, 10, 17, 18, 20, 7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 15, 23, 27, 29, 30, 31]
}

private def PhaseBankWeak_bank0_0 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank1_0 : List (List Nat) := [
  [4581298448, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8017272284, 8084644320, 8556510720, 8589803520],
  [1145324612, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2290649224, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5389762880, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8421504500, 8556510720, 8589803520],
  [336860180, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2694881440, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank1_1 : List (List Nat) := [
  [5704340480, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8578793300, 8589803520],
  [22282580, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2852170240, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726535680, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589890900],
  [87380, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [2863267840, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank1_2 : List (List Nat) := [
  [5726623060, 6467715456, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8488876536, 8556510720, 8589803520],
  [404232216, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [1616928864, 5726623060, 6871947672, 8556510720, 8589803520],
  [1616928864, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6845208576, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8583249816, 8589803520]
]

private def PhaseBankWeak_bank1_3 : List (List Nat) := [
  [26739096, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [1711302144, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871842816, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589908376],
  [104856, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [1717960704, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8053186560, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8587968480, 8589803520]
]

private def PhaseBankWeak_bank1_4 : List (List Nat) := [
  [31457760, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [503324160, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084520960, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589926880],
  [123360, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [505282560, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556380160, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589934080]
]

private def PhaseBankWeak_bank1_5 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520, 8589934080],
  [130560, 5726623060, 6871947672, 8084644320, 8589803520],
  [130560, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [33423360, 5726623060, 6871947672, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank2_0 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8354132464, 8556510720, 8589803520],
  [3772834016, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8574336784, 8589803520],
  [3993038336, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589873424],
  [4008574976, 5726623060, 6871947672, 8084644320, 8556510720],
  [5726623060, 8017272284, 8488876536, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank2_1 : List (List Nat) := [
  [5726623060, 6871947672, 7986076672, 8084644320, 8589803520],
  [31195612, 5726623060, 6871947672, 8084644320, 8589803520],
  [2290649224, 5726623060, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8219388392, 8556510720, 8589803520],
  [5726623060, 5928739168, 6871947672, 8556510720, 8589803520],
  [5726623060, 7949900248, 8084644320, 8556510720, 8589803520],
  [2560137368, 5726623060, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8577482560, 8589803520]
]

private def PhaseBankWeak_bank2_2 : List (List Nat) := [
  [3187719680, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589885760],
  [3200122880, 5726623060, 6871947672, 8084644320, 8556510720],
  [5726623060, 8012815768, 8084644320, 8556510720, 8589803520],
  [2308475288, 5726623060, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8420193760, 8556510720, 8589803520],
  [2715853280, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589890560]
]

private def PhaseBankWeak_bank2_3 : List (List Nat) := [
  [2885550080, 5726623060, 6871947672, 8084644320, 8556510720],
  [5726623060, 8017254808, 8084644320, 8556510720, 8589803520],
  [2290719128, 5726623060, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8421499360, 8556510720, 8589803520],
  [2694963680, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8578792960, 8589803520],
  [2852257280, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084603200, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank2_4 : List (List Nat) := [
  [505287700, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589890900, 8589934080],
  [2863267840, 5726623060, 6871947672, 8084644320, 8589934080],
  [5726623060, 6871947672, 8084644320, 8567651840, 8589803520],
  [5704384000, 5726623060, 6871947672, 8084644320, 8589803520],
  [1616928864, 5726623060, 6871947672, 8556510720, 8589803520],
  [5726623060, 6845208576, 8488876536, 8556510720, 8589803520],
  [1711302144, 5726623060, 8488876536, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank2_5 : List (List Nat) := [
  [5726623060, 8488876536, 8556510720, 8589803520, 8589908376],
  [104856, 5726623060, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488876536, 8556510720, 8589803520],
  [1616928864, 5726623060, 8488876536, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488876536, 8589803520, 8589934080],
  [130560, 5726623060, 6871947672, 8488876536, 8589803520],
  [1616928864, 5726623060, 6871947672, 8589803520, 8589934080],
  [130560, 1616928864, 5726623060, 6871947672, 8589803520]
]

private def PhaseBankWeak_bank2_6 : List (List Nat) := [
  [1616928864, 5726623060, 6871947672, 8562802272, 8589803520],
  [1616928864, 5726623060, 6871947672, 6945873408, 8589803520],
  [5726623060, 6871947672, 8084644320, 8562802272, 8589803520],
  [5726623060, 6871947672, 6945873408, 8084644320, 8589803520],
  [6871947672, 8008359252, 8084644320, 8556510720, 8589803520],
  [1163150676, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8487303648, 8556510720, 8589803520],
  [1642095072, 5726623060, 6871947672, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank2_7 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8556510720, 8589907968],
  [1744699392, 5726623060, 6871947672, 8084644320, 8556510720],
  [5726623060, 6871947672, 8086217208, 8556510720, 8589803520],
  [5726623060, 6871947672, 8059478112, 8556510720, 8589803520],
  [6871947672, 8017237332, 8084644320, 8556510720, 8589803520],
  [1145394516, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8488870368, 8556510720, 8589803520],
  [1617027552, 5726623060, 6871947672, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank2_8 : List (List Nat) := [
  [5726623060, 6871947672, 8084644320, 8583249408, 8589803520],
  [1711406592, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589908376, 8589934080],
  [5726623060, 6871947672, 8084650488, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084545632, 8556510720, 8589803520],
  [1717960704, 5726623060, 6871947672, 8084644320, 8589934080],
  [5726623060, 6871947672, 8084644320, 8563195392, 8589803520],
  [5726623060, 6845234688, 6871947672, 8084644320, 8589803520]
]

private def PhaseBankWeak_bank2_9 : List (List Nat) := [
  [5726623060, 6878239224, 8084644320, 8556510720, 8589803520],
  [5726623060, 6846781464, 8084644320, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084644320, 8556510720, 8589811200],
  [5726623060, 6871947672, 8084644320, 8086487040, 8556510720],
  [6871947672, 8084644320, 8421463380, 8556510720, 8589803520],
  [336942420, 6871947672, 8084644320, 8556510720, 8589803520],
  [5726623060, 8084644320, 8488851864, 8556510720, 8589803520],
  [404330904, 5726623060, 8084644320, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank2_10 : List (List Nat) := [
  [5726623060, 6871947672, 8084520960, 8084644320, 8589934080],
  [5726623060, 6871947672, 8084644320, 8587968000, 8589803520],
  [503447040, 5726623060, 6871947672, 8084644320, 8589803520],
  [123360, 5726623060, 6871947672, 8084644320, 8589934080],
  [5726623060, 6871947672, 8084644320, 8558476800, 8589803520],
  [5726623060, 6871947672, 8053194240, 8084644320, 8589803520],
  [130560, 5726623060, 6871947672, 8084644320, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589803520, 8589934080]
]

private def PhaseBankWeak_bank2_11 : List (List Nat) := [
  [130560, 5726623060, 6871947672, 8084644320, 8589934080],
  [130560, 5726623060, 6871947672, 8084652000, 8589803520],
  [130560, 5726623060, 6871947672, 8084521440, 8589803520],
  [5726623060, 6871947672, 8084652000, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084521440, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank3_0 : List (List Nat) := [
  [5726623060, 7986076672, 8488876536, 8589803520],
  [5726623060, 6871947672, 8084644320, 8589925376],
  [5726623060, 8488868312, 8556510720, 8589803520],
  [5726623060, 6871947672, 8084603200, 8589934080],
  [8008359252, 8488876536, 8556510720, 8589803520],
  [5726623060, 8488876536, 8556510720, 8589907968],
  [5726623060, 8488876536, 8589908376, 8589934080],
  [5726623060, 6945873408, 8488876536, 8589803520]
]

private def PhaseBankWeak_bank3_1 : List (List Nat) := [
  [1617034848, 5726623060, 6871947672, 8589803520],
  [1616928864, 5726623060, 6871947672, 8589909504],
  [5726623060, 6871947672, 8084644320, 8589909504],
  [6871947672, 8084644320, 8421463380, 8589934080],
  [5726623060, 8084644320, 8488851864, 8589934080],
  [5726623060, 6871947672, 8084521440, 8589934080],
  [130560, 5726623060, 8488851960, 8589803520],
  [5726623060, 8488851960, 8556510720, 8589803520]
]

private def PhaseBankWeak_bank4_0 : List (List Nat) := [
  [5726623060, 8488876536, 8589925376],
  [5726623060, 8488868312, 8589934080],
  [5726623060, 8488876536, 8589909504],
  [5726623060, 8488851960, 8589934080]
]

private def PhaseBankWeak_pieces : Nat → List (List (List Nat))
  | 0 => [PhaseBankWeak_bank0_0]
  | 1 => [PhaseBankWeak_bank1_0, PhaseBankWeak_bank1_1, PhaseBankWeak_bank1_2, PhaseBankWeak_bank1_3, PhaseBankWeak_bank1_4, PhaseBankWeak_bank1_5]
  | 2 => [PhaseBankWeak_bank2_0, PhaseBankWeak_bank2_1, PhaseBankWeak_bank2_2, PhaseBankWeak_bank2_3, PhaseBankWeak_bank2_4, PhaseBankWeak_bank2_5, PhaseBankWeak_bank2_6, PhaseBankWeak_bank2_7, PhaseBankWeak_bank2_8, PhaseBankWeak_bank2_9, PhaseBankWeak_bank2_10, PhaseBankWeak_bank2_11]
  | 3 => [PhaseBankWeak_bank3_0, PhaseBankWeak_bank3_1]
  | 4 => [PhaseBankWeak_bank4_0]
  | _ => []

def smallWeakLayers (depth : Nat) : List (List Nat) := (PhaseBankWeak_pieces depth).flatten

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank0_0_checked : PhaseBankWeak_bank0_0.all (stateCheck smallWeak smallWeakLayers 0) = true := by
  decide +kernel

private theorem PhaseBankWeak_depth0_checked : (smallWeakLayers 0).all (stateCheck smallWeak smallWeakLayers 0) = true := by
  simp only [smallWeakLayers, PhaseBankWeak_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankWeak_bank0_0_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank1_0_checked : PhaseBankWeak_bank1_0.all (stateCheck smallWeak smallWeakLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank1_1_checked : PhaseBankWeak_bank1_1.all (stateCheck smallWeak smallWeakLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank1_2_checked : PhaseBankWeak_bank1_2.all (stateCheck smallWeak smallWeakLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank1_3_checked : PhaseBankWeak_bank1_3.all (stateCheck smallWeak smallWeakLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank1_4_checked : PhaseBankWeak_bank1_4.all (stateCheck smallWeak smallWeakLayers 1) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank1_5_checked : PhaseBankWeak_bank1_5.all (stateCheck smallWeak smallWeakLayers 1) = true := by
  decide +kernel

private theorem PhaseBankWeak_depth1_checked : (smallWeakLayers 1).all (stateCheck smallWeak smallWeakLayers 1) = true := by
  simp only [smallWeakLayers, PhaseBankWeak_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankWeak_bank1_0_checked, PhaseBankWeak_bank1_1_checked, PhaseBankWeak_bank1_2_checked, PhaseBankWeak_bank1_3_checked, PhaseBankWeak_bank1_4_checked, PhaseBankWeak_bank1_5_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_0_checked : PhaseBankWeak_bank2_0.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_1_checked : PhaseBankWeak_bank2_1.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_2_checked : PhaseBankWeak_bank2_2.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_3_checked : PhaseBankWeak_bank2_3.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_4_checked : PhaseBankWeak_bank2_4.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_5_checked : PhaseBankWeak_bank2_5.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_6_checked : PhaseBankWeak_bank2_6.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_7_checked : PhaseBankWeak_bank2_7.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_8_checked : PhaseBankWeak_bank2_8.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_9_checked : PhaseBankWeak_bank2_9.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_10_checked : PhaseBankWeak_bank2_10.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank2_11_checked : PhaseBankWeak_bank2_11.all (stateCheck smallWeak smallWeakLayers 2) = true := by
  decide +kernel

private theorem PhaseBankWeak_depth2_checked : (smallWeakLayers 2).all (stateCheck smallWeak smallWeakLayers 2) = true := by
  simp only [smallWeakLayers, PhaseBankWeak_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankWeak_bank2_0_checked, PhaseBankWeak_bank2_1_checked, PhaseBankWeak_bank2_2_checked, PhaseBankWeak_bank2_3_checked, PhaseBankWeak_bank2_4_checked, PhaseBankWeak_bank2_5_checked, PhaseBankWeak_bank2_6_checked, PhaseBankWeak_bank2_7_checked, PhaseBankWeak_bank2_8_checked, PhaseBankWeak_bank2_9_checked, PhaseBankWeak_bank2_10_checked, PhaseBankWeak_bank2_11_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank3_0_checked : PhaseBankWeak_bank3_0.all (stateCheck smallWeak smallWeakLayers 3) = true := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank3_1_checked : PhaseBankWeak_bank3_1.all (stateCheck smallWeak smallWeakLayers 3) = true := by
  decide +kernel

private theorem PhaseBankWeak_depth3_checked : (smallWeakLayers 3).all (stateCheck smallWeak smallWeakLayers 3) = true := by
  simp only [smallWeakLayers, PhaseBankWeak_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankWeak_bank3_0_checked, PhaseBankWeak_bank3_1_checked, Bool.and_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
private theorem PhaseBankWeak_bank4_0_checked : PhaseBankWeak_bank4_0.all (stateCheck smallWeak smallWeakLayers 4) = true := by
  decide +kernel

private theorem PhaseBankWeak_depth4_checked : (smallWeakLayers 4).all (stateCheck smallWeak smallWeakLayers 4) = true := by
  simp only [smallWeakLayers, PhaseBankWeak_pieces, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil, PhaseBankWeak_bank4_0_checked, Bool.and_self]

private theorem PhaseBankWeak_depth5_checked : (smallWeakLayers 5).all (stateCheck smallWeak smallWeakLayers 5) = true := by
  rfl

private theorem PhaseBankWeak_depth6_checked : (smallWeakLayers 6).all (stateCheck smallWeak smallWeakLayers 6) = true := by
  rfl

theorem smallWeak_no_solution {depth : Nat} {bank : List Nat}
    (path : Reach smallWeak depth bank) : solved smallWeak bank = false := by
  apply closure_sound smallWeak smallWeakLayers _ _ path
  · decide +kernel
  · intro depth limit
    change depth ≤ 6 at limit
    have options : depth = 0 ∨ depth = 1 ∨ depth = 2 ∨ depth = 3 ∨ depth = 4 ∨ depth = 5 ∨ depth = 6 := by omega
    rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact PhaseBankWeak_depth0_checked
    · exact PhaseBankWeak_depth1_checked
    · exact PhaseBankWeak_depth2_checked
    · exact PhaseBankWeak_depth3_checked
    · exact PhaseBankWeak_depth4_checked
    · exact PhaseBankWeak_depth5_checked
    · exact PhaseBankWeak_depth6_checked

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.PhaseBank

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

open scoped Classical
open PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation in
abbrev BankProblem := PhaseBank.Problem

def signalCode {width : Nat} (f : Signal (Fin width)) : Nat :=
  PhaseBank.encode (Nat.ofBits f) false

@[simp] theorem bits_signalCode {width : Nat} (f : Signal (Fin width)) :
    PhaseBank.bits (signalCode f) = Nat.ofBits f := by
  simp [PhaseBank.bits, signalCode, PhaseBank.encode]

@[simp] theorem critical_signalCode {width : Nat} (f : Signal (Fin width)) :
    PhaseBank.critical (signalCode f) = false := by
  simp [PhaseBank.critical, signalCode, PhaseBank.encode]

theorem signalCode_injective (width : Nat) : Function.Injective (@signalCode width) := by
  intro a b same
  have bitsSame := congrArg PhaseBank.bits same
  funext i
  have rowSame := congrArg (fun v : Nat => v.testBit i.val) bitsSame
  simpa only [bits_signalCode, Nat.testBit_ofBits_lt _ _ i.isLt] using rowSame

private def toBankOp : Op → PhaseBank.Op
  | .conj => .and
  | .disj => .or
  | .diff => .diff

private theorem bit_above {width j : Nat} (b : Fin width → Bool) (after : width ≤ j) :
    (Nat.ofBits b).testBit j = false :=
  Nat.testBit_lt_two_pow ((Nat.ofBits_lt_two_pow b).trans_le (Nat.pow_le_pow_right (by omega) after))

private theorem eval_mask {width : Nat} (p : BankProblem) (full : p.full = 2 ^ width - 1)
    (op : Op) (a b : Signal (Fin width)) :
    PhaseBank.eval p (toBankOp op) (Nat.ofBits a) (Nat.ofBits b) = Nat.ofBits (op.on a b) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases inside : j < width
  · cases op <;>
      simp [PhaseBank.eval, toBankOp, Op.on, Op.eval, Nat.testBit_and, Nat.testBit_or,
        Nat.testBit_xor, full, Nat.testBit_two_pow_sub_one, inside, Nat.testBit_ofBits_lt]
  · have above := Nat.le_of_not_lt inside
    cases op <;>
      simp [PhaseBank.eval, toBankOp, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
        bit_above _ above]

noncomputable def encodeBank {width : Nat} (live : Finset (Signal (Fin width))) : List Nat :=
  PhaseBank.canonical ((live.image signalCode).toList)

theorem mem_encodeBank {width : Nat} (live : Finset (Signal (Fin width))) (w : Nat) :
    w ∈ encodeBank live ↔ ∃ v ∈ live, signalCode v = w := by
  unfold encodeBank
  rw [(PhaseBank.canonical_perm _).mem_iff, Finset.mem_toList, Finset.mem_image]

private theorem length_encodeBank {width : Nat} (live : Finset (Signal (Fin width))) :
    (encodeBank live).length = live.card := by
  unfold encodeBank
  rw [(PhaseBank.canonical_perm _).length_eq, Finset.length_toList,
    Finset.card_image_of_injective _ (signalCode_injective width)]

private theorem nodup_encodeBank {width : Nat} (live : Finset (Signal (Fin width))) :
    (encodeBank live).Nodup := by
  exact (PhaseBank.canonical_perm _).nodup_iff.mpr (Finset.nodup_toList _)

private theorem mem_discard {bank : List Nat} (nd : bank.Nodup) (needle w : Nat) (drop : Bool) :
    w ∈ PhaseBank.discard bank needle drop ↔ w ∈ bank ∧ (drop = true → w ≠ needle) := by
  cases drop <;> simp [PhaseBank.discard, nd.erase_eq_filter]

private theorem nodup_discard {bank : List Nat} (nd : bank.Nodup) (needle : Nat) (drop : Bool) :
    (PhaseBank.discard bank needle drop).Nodup := by
  cases drop
  · exact nd
  · exact nd.erase needle

private theorem discard_subset {bank : List Nat} (needle : Nat) (drop : Bool) :
    PhaseBank.discard bank needle drop ⊆ bank := by
  intro w mem
  cases drop
  · exact mem
  · exact List.mem_of_mem_erase mem

noncomputable def liveAction {width : Nat} [DecidableEq (Signal (Fin width))]
    (after : Finset (Signal (Fin width))) (op : Op) (a b : Signal (Fin width)) : PhaseBank.Action :=
  ⟨toBankOp op, signalCode a, signalCode b, decide (a ∉ after), decide (b ∉ after)⟩

theorem live_step_encoded {width : Nat} [DecidableEq (Signal (Fin width))]
    (p : BankProblem) (full : p.full = 2 ^ width - 1) (after : Finset (Signal (Fin width)))
    (op : Op) (a b : Signal (Fin width)) (needed : op.on a b ∈ after) (distinct : a ≠ b)
    (freshA : a ≠ op.on a b) (freshB : b ≠ op.on a b) :
    let before := insert a (insert b (after.erase (op.on a b)))
    let move := liveAction after op a b
    PhaseBank.allowed (encodeBank before) move ∧
      PhaseBank.perform p (encodeBank before) move = encodeBank after := by
  classical
  let s := op.on a b
  let before := insert a (insert b (after.erase s))
  let move := liveAction after op a b
  let remaining := PhaseBank.discard
    (PhaseBank.discard (encodeBank before) (signalCode a) move.dropL) (signalCode b) move.dropR
  have startFresh : s ∉ before := by
    intro member
    rcases Finset.mem_insert.mp member with same | other
    · exact freshA same.symm
    rcases Finset.mem_insert.mp other with same | previous
    · exact freshB same.symm
    exact (Finset.mem_erase.mp previous).1 rfl
  have aPresent : signalCode a ∈ encodeBank before :=
    (mem_encodeBank _ _).mpr ⟨a, Finset.mem_insert_self _ _, rfl⟩
  have bPresent : signalCode b ∈ encodeBank before :=
    (mem_encodeBank _ _).mpr ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), rfl⟩
  have different : signalCode b ≠ signalCode a := fun same =>
    distinct ((signalCode_injective width same).symm)
  have nd := nodup_encodeBank before
  have restNodup : remaining.Nodup := nodup_discard (nodup_discard nd _ _) _ _
  have stay : ∀ w, w ∈ remaining →
      w ∈ encodeBank before := by
    intro w hw
    exact discard_subset _ _ (discard_subset _ _ hw)
  have fresh : signalCode s ∉ remaining := by
    intro mem
    obtain ⟨v, hv, same⟩ := (mem_encodeBank _ _).mp (stay _ mem)
    exact startFresh ((signalCode_injective width same) ▸ hv)
  have rawStep : PhaseBank.rawPerform p (encodeBank before) move = signalCode s :: remaining := by
    change PhaseBank.encode
      (PhaseBank.eval p (toBankOp op) (PhaseBank.bits (signalCode a)) (PhaseBank.bits (signalCode b)))
        false :: remaining = _
    rw [bits_signalCode, bits_signalCode, eval_mask p full]
    rfl
  refine ⟨?_, ?_⟩
  · refine ⟨aPresent, ?_, ?_⟩
    · change signalCode b ∈ (encodeBank before).erase (signalCode a)
      simp [nd.erase_eq_filter, bPresent, different]
    · simp [PhaseBank.permitted, liveAction]
  · change PhaseBank.canonical (PhaseBank.rawPerform p (encodeBank before) move) =
      PhaseBank.canonical ((after.image signalCode).toList)
    rw [rawStep]
    apply PhaseBank.canonical_eq_of_perm
    apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨fresh, restNodup⟩)
      (Finset.nodup_toList _)
    apply Finset.ext
    intro w
    simp only [List.mem_toFinset, List.mem_cons, Finset.mem_toList, Finset.mem_image]
    have restIff : w ∈ remaining ↔
        w ∈ encodeBank before ∧ (a ∉ after → w ≠ signalCode a) ∧
          (b ∉ after → w ≠ signalCode b) := by
      simp only [remaining, mem_discard (nodup_discard nd _ _), mem_discard nd,
        move, liveAction, decide_eq_true_eq, and_assoc]
    rw [restIff]
    constructor
    · rintro (rfl | ⟨mem, keepA, keepB⟩)
      · exact ⟨s, needed, rfl⟩
      · obtain ⟨v, hv, rfl⟩ := (mem_encodeBank _ _).mp mem
        refine ⟨v, ?_, rfl⟩
        rcases Finset.mem_insert.mp hv with rfl | hv
        · by_contra gone
          exact keepA gone rfl
        rcases Finset.mem_insert.mp hv with rfl | hv
        · by_contra gone
          exact keepB gone rfl
        exact Finset.mem_of_mem_erase hv
    · rintro ⟨v, hv, rfl⟩
      by_cases same : v = s
      · exact Or.inl (congrArg signalCode same)
      · refine Or.inr ⟨(mem_encodeBank _ _).mpr ⟨v,
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨same, hv⟩)), rfl⟩,
          ?_, ?_⟩
        · intro gone eq
          exact gone ((signalCode_injective width eq) ▸ hv)
        · intro gone eq
          exact gone ((signalCode_injective width eq) ▸ hv)

private theorem final_solved {width : Nat} {f : Signal (Fin width)} (p : BankProblem)
    (target : p.target = Nat.ofBits f) [DecidableEq (Signal (Fin width))] :
    PhaseBank.solved p (encodeBank {f}) = true := by
  unfold PhaseBank.solved
  apply List.any_eq_true.mpr
  exact ⟨signalCode f, (mem_encodeBank _ _).mpr ⟨f, Finset.mem_singleton_self _, rfl⟩,
    by simp [target]⟩

private theorem live_separated {width : Nat} [DecidableEq (Signal (Fin width))]
    {f : Signal (Fin width)} {k : Nat} {live : Finset (Signal (Fin width))} (run : Live f k live)
    (p : BankProblem) (full : p.full = 2 ^ width - 1) (target : p.target = Nat.ofBits f)
    (positive : ∀ i ∈ p.positive, ∃ h : i < width, f ⟨i, h⟩ = true) :
    PhaseBank.separated p (encodeBank live) = true := by
  apply (PhaseBank.separated_iff p _).mpr
  intro yes yesMem no noFull noNegative
  obtain ⟨yesValid, yesVal⟩ := positive yes yesMem
  have noValid : no < width := by
    simpa [full, Nat.testBit_two_pow_sub_one] using noFull
  have noVal : f ⟨no, noValid⟩ = false := by
    simpa only [target, Nat.testBit_ofBits_lt _ _ noValid] using noNegative
  have differs : ∃ v ∈ live, v ⟨yes, yesValid⟩ ≠ v ⟨no, noValid⟩ := by
    classical
    by_contra allSame
    have same := run.agrees (⟨yes, yesValid⟩ : Fin width) ⟨no, noValid⟩
      (fun v mem => Classical.byContradiction (fun unequal => allSame ⟨v, mem, unequal⟩))
    simp [yesVal, noVal] at same
  obtain ⟨v, mem, diff⟩ := differs
  exact ⟨signalCode v, (mem_encodeBank _ _).mpr ⟨v, mem, rfl⟩,
    by simpa only [bits_signalCode, Nat.testBit_ofBits_lt _ _ yesValid,
      Nat.testBit_ofBits_lt _ _ noValid] using diff⟩

theorem Live.reaches_phase_bank {width : Nat} [DecidableEq (Signal (Fin width))]
    {f : Signal (Fin width)} {k : Nat} {live : Finset (Signal (Fin width))}
    (run : Live f k live) (p : BankProblem)
    (full : p.full = 2 ^ width - 1) (target : p.target = Nat.ofBits f)
    (positive : ∀ i ∈ p.positive, ∃ h : i < width, f ⟨i, h⟩ = true)
    (used : Nat) (budget : used + k ≤ p.cap) (start : PhaseBank.Reach p used (encodeBank live)) :
    ∃ depth ≤ p.cap, ∃ bank, PhaseBank.Reach p depth bank ∧ PhaseBank.solved p bank = true := by
  induction run generalizing used with
  | done => exact ⟨used, by omega, _, start, final_solved p target⟩
  | @step k after op a b needed distinct freshA freshB rest ih =>
    obtain ⟨ok, eq⟩ := live_step_encoded p full after op a b needed distinct freshA freshB
    have keep : PhaseBank.eligible p (used + 1) (encodeBank after) = true := by
      by_cases last : k = 0
      · subst k
        cases rest
        simp only [PhaseBank.eligible, final_solved p target, Bool.true_or]
      · have normal : PhaseBank.within p (used + 1) (encodeBank after) = true := by
          have upper := rest.card_le
          simp only [PhaseBank.within, Bool.and_eq_true, decide_eq_true_eq, length_encodeBank]
          exact ⟨by omega, by omega⟩
        simp only [PhaseBank.eligible, normal, live_separated rest p full target positive,
          Bool.and_true, Bool.or_true]
    have bankStep : PhaseBank.Reach p (used + 1) (encodeBank after) := by
      rw [← eq]
      exact .step start (by omega) (liveAction after op a b) ok (eq.symm ▸ keep)
    exact ih (used + 1) (by omega) bankStep

theorem canonical_initial_of_members {width : Nat}
    (p : BankProblem) (live : Finset (Signal (Fin width))) (nd : p.initial.Nodup)
    (agree : ∀ w, w ∈ p.initial ↔ ∃ v ∈ live, signalCode v = w) :
    PhaseBank.canonical p.initial = encodeBank live := by
  unfold encodeBank
  apply PhaseBank.canonical_eq_of_perm
  apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
  apply Finset.ext
  intro w
  simpa only [List.mem_toFinset, Finset.mem_toList, Finset.mem_image] using agree w

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six

abbrev Input := Fin 6 → Bool

def target (x : Input) : Bool :=
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 3) ||
  (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) ||
  (x 2 && x 5) || (x 3 && x 5)

def bits (mask : Nat) (i : Fin 6) : Bool := mask.testBit i.val

abbrev agrees (p : Fin 6) (x y : Input) : Prop :=
  ∀ i, i ≠ p → x i = y i

def firstOther (p : Fin 6) : Nat := if p.val < 2 then 4 else 1

def otherWeight (p : Fin 6) : Nat := 2 ^ p.val

def surviving (p : Fin 6) : Nat :=
  if p.val = 0 then 6 else if p.val = 2 then 9 else 5

def strong (p : Fin 6) : Bool := p.val == 0 || p.val == 2

def orAnchor (p : Fin 6) (u v : Bool) : Nat :=
  (if u then 16 else 0) + (if v then 32 else 0) +
    (if u && !v then (if p.val == 1 then 8 else if p.val == 3 then 2 else 0) else 0)

def pairP (a b : Fin 6) : Fin 6 :=
  if (a.val < 2 ↔ b.val < 2) ∧ strong b then b else a

def pairAnchor (a b : Fin 6) : Nat :=
  (if pairP a b = a then otherWeight b else otherWeight a) +
    (if a.val < 2 ↔ b.val < 2 then 16 else 0)

theorem origin : target (fun _ => false) = false := by decide +kernel

theorem singleton_false : ∀ p : Fin 6, target (bits (otherWeight p)) = false ∧
    bits (otherWeight p) p = true := by decide +kernel

theorem ordinary_pivot : ∀ p : Fin 6, p.val < 4 →
    let x := bits (firstOther p)
    let y := bits (firstOther p + otherWeight p)
    agrees p x y ∧ x p = false ∧ y p = true ∧
    x 4 = false ∧ x 5 = false ∧ y 4 = false ∧ y 5 = false ∧ target x ≠ target y := by
  decide +kernel

theorem fixed_nonzero : ∀ p : Fin 6, p.val < 4 →
    bits (surviving p) p = false ∧ target (bits (surviving p)) = true := by
  decide +kernel

theorem or_small_pivot : ∀ (p : Fin 6) (u v : Bool), p.val < 4 → (u || v) = true →
    let x := bits (orAnchor p u v)
    let y := bits (orAnchor p u v + otherWeight p)
    agrees p x y ∧ x 4 = u ∧ x 5 = v ∧ y 4 = u ∧ y 5 = v ∧ target x ≠ target y := by
  decide +kernel

theorem or_pair_pivot : ∀ a b : Fin 6, a.val < 4 → b.val < 4 → a ≠ b →
    let p := pairP a b
    let x := bits (pairAnchor a b)
    let y := bits (pairAnchor a b + otherWeight p)
    p.val < 4 ∧ (p = a ∨ p = b) ∧ agrees p x y ∧ target x ≠ target y ∧
      (x a || x b) = (y a || y b) := by
  decide +kernel

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six

open PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

def Small (g : Signal Input) : Prop :=
  g (fun _ => false) = false ∧ ∀ x y, x 4 = y 4 → x 5 = y 5 → g x = g y

def Safe (bank : List (Signal Input)) : Prop :=
  zero ∈ bank ∧ ∀ g ∈ bank, Small g ∨ ∃ p : Fin 6, p.val < 4 ∧ g = raw p

def Lift (spent : Nat) (bank : List (Signal Input)) : Prop :=
  ∀ (p : Fin 6) (f : Signal Input) (k : Nat),
    Reach f k (bank.map (pin p false)) → Reach f (spent + k) (base 6)

abbrev PinLower : Prop :=
  ∀ p : Fin 6, p.val < 4 → ¬ Reach (pin p false target) 6 (base 6)

private theorem setRaw_eq_of_agrees {p : Fin 6} {x y : Input} (same : agrees p x y) :
    setRaw p (y p) x = y := by
  funext i
  by_cases equal : i = p
  · subst i; simp [setRaw]
  · simpa [setRaw, equal] using same i equal

theorem target_needed (p : Fin 6) (valid : p.val < 4) : ¬ Independent p target := by
  have choice := ordinary_pivot p valid
  intro independent
  exact choice.2.2.2.2.2.2.2 ((independent _ _).symm.trans
    (congrArg target (setRaw_eq_of_agrees choice.1)))

theorem target_pin_nonzero (p : Fin 6) (valid : p.val < 4) :
    pin p false target ≠ zero := by
  obtain ⟨pFalse, yes⟩ := fixed_nonzero p valid
  have unchanged : setRaw p false (bits (surviving p)) = bits (surviving p) := by
    simpa only [pFalse] using
      (setRaw_eq_of_agrees (p := p) (x := bits (surviving p))
        (y := bits (surviving p)) (fun _ _ => rfl))
  have zeroFixed : setRaw p false (fun _ => false) = (fun _ => false) := by
    funext i
    simp [setRaw]
  intro vanishes
  have atPoint := congrFun vanishes (bits (surviving p))
  simp [pin, normalizeAt, unchanged, zeroFixed, origin, zero, yes] at atPoint

private theorem zero_pin (p : Fin 6) : pin p false (zero : Signal Input) = zero := by
  funext x; rfl

private theorem Safe.mapZero {bank : List (Signal Input)} (safe : Safe bank) (p : Fin 6) :
    zero ∈ bank.map (pin p false) :=
  List.mem_map.mpr ⟨zero, safe.1, zero_pin p⟩

private theorem Small.op {a b : Signal Input} (ha : Small a) (hb : Small b) (op : Op) :
    Small (op.on a b) := by
  constructor
  · simp only [Op.on, ha.1, hb.1]
    cases op <;> rfl
  · intro x y same4 same5
    simp only [Op.on, ha.2 x y same4 same5, hb.2 x y same4 same5]

private theorem Small.eq_of_agrees {g : Signal Input} (small : Small g)
    {p : Fin 6} (valid : p.val < 4) {x y : Input} (same : agrees p x y) : g x = g y := by
  apply small.2 x y
  · apply same; intro equal; have := congrArg Fin.val equal; omega
  · apply same; intro equal; have := congrArg Fin.val equal; omega

private theorem Safe.tracks {bank : List (Signal Input)} (safe : Safe bank)
    {p : Fin 6} (valid : p.val < 4) {x y : Input} (same : agrees p x y)
    (g : Signal Input) (member : g ∈ bank) (differs : g x ≠ g y) : pin p false g = zero := by
  rcases safe.2 g member with small | ⟨q, _, rfl⟩
  · exact (differs (small.eq_of_agrees valid same)).elim
  · have equal : q = p := by
      by_contra different
      exact differs (same q different)
    subst q
    exact pin_raw p false

private theorem target_not_in {bank : List (Signal Input)} (safe : Safe bank) :
    target ∉ bank := by
  intro present
  rcases safe.2 target present with small | ⟨p, _, equal⟩
  · have choice := ordinary_pivot 0 (by decide)
    exact choice.2.2.2.2.2.2.2 (small.eq_of_agrees (by decide) choice.1)
  · obtain ⟨targetFalse, rawTrue⟩ := singleton_false p
    have point := congrFun equal (bits (otherWeight p))
    change target (bits (otherWeight p)) = bits (otherWeight p) p at point
    rw [targetFalse, rawTrue] at point
    contradiction

def Comparison (p : Fin 6) (g : Signal Input) : Prop :=
  ∃ x y, agrees p x y ∧ target x ≠ target y ∧
    (g x = g y ∨ pin p false g = zero)

private theorem Comparison.vanish {p : Fin 6} (valid : p.val < 4) {g : Signal Input}
    (vanishes : pin p false g = zero) : Comparison p g := by
  have choice := ordinary_pivot p valid
  exact ⟨_, _, choice.1, choice.2.2.2.2.2.2.2, Or.inr vanishes⟩

private theorem conj_left_comparison {p : Fin 6} (valid : p.val < 4)
    (g : Signal Input) : Comparison p (Op.conj.on (raw p) g) := by
  apply Comparison.vanish valid
  funext x; simp [pin, normalizeAt, setRaw, Op.on, Op.eval, raw, zero]

private theorem conj_right_comparison {p : Fin 6} (valid : p.val < 4)
    (g : Signal Input) : Comparison p (Op.conj.on g (raw p)) := by
  apply Comparison.vanish valid
  funext x; simp [pin, normalizeAt, setRaw, Op.on, Op.eval, raw, zero]

private theorem diff_left_comparison {p : Fin 6} (valid : p.val < 4)
    (g : Signal Input) : Comparison p (Op.diff.on (raw p) g) := by
  apply Comparison.vanish valid
  funext x; simp [pin, normalizeAt, setRaw, Op.on, Op.eval, raw, zero]

private theorem diff_right_small_comparison {p : Fin 6} (valid : p.val < 4)
    {g : Signal Input} (small : Small g) : Comparison p (Op.diff.on g (raw p)) := by
  let x := bits (firstOther p)
  let y := bits (firstOther p + otherWeight p)
  obtain ⟨agree, _, _, x4, x5, y4, y5, different⟩ := ordinary_pivot p valid
  have gx : g x = false := (small.2 x (fun _ => false) x4 x5).trans small.1
  have gy : g y = false := (small.2 y (fun _ => false) y4 y5).trans small.1
  exact ⟨x, y, agree, different, Or.inl (by simp [Op.on, Op.eval, gx, gy])⟩

private theorem disj_right_small_comparison {p : Fin 6} (valid : p.val < 4)
    {g : Signal Input} (small : Small g) : Comparison p (Op.disj.on (raw p) g) := by
  by_cases trivial : g = zero
  · subst g
    apply Comparison.vanish valid
    funext x; simp [pin, normalizeAt, setRaw, Op.on, Op.eval, raw, zero]
  have someTrue : ∃ z, g z = true := by
    by_contra none
    apply trivial
    funext z
    cases h : g z
    · rfl
    · exact (none ⟨z, h⟩).elim
  obtain ⟨z, yes⟩ := someTrue
  have support : (z 4 || z 5) = true := by
    cases q : z 4 <;> cases r : z 5 <;> simp
    have eqZero := (small.2 z (fun _ => false) q r).trans small.1
    rw [yes] at eqZero
    contradiction
  let x := bits (orAnchor p (z 4) (z 5))
  let y := bits (orAnchor p (z 4) (z 5) + otherWeight p)
  obtain ⟨same, x4, x5, y4, y5, different⟩ := or_small_pivot p (z 4) (z 5) valid support
  have gx : g x = true := (small.2 x z x4 x5).trans yes
  have gy : g y = true := (small.2 y z y4 y5).trans yes
  exact ⟨x, y, same, different, Or.inl (by simp [Op.on, Op.eval, gx, gy])⟩

private theorem disj_left_small_comparison {p : Fin 6} (valid : p.val < 4)
    {g : Signal Input} (small : Small g) : Comparison p (Op.disj.on g (raw p)) := by
  have eq : Op.disj.on g (raw p) = Op.disj.on (raw p) g := by
    funext x; exact Bool.or_comm _ _
  rw [eq]
  exact disj_right_small_comparison valid small

private theorem disj_pair_comparison {a b : Fin 6} (aValid : a.val < 4)
    (bValid : b.val < 4) : ∃ p : Fin 6, p.val < 4 ∧ (p = a ∨ p = b) ∧
      Comparison p (Op.disj.on (raw a) (raw b)) := by
  by_cases equal : a = b
  · subst b
    refine ⟨a, aValid, Or.inl rfl, Comparison.vanish aValid ?_⟩
    funext x; simp [pin, normalizeAt, setRaw, Op.on, Op.eval, raw, zero]
  · obtain ⟨valid, chosen, same, different, equalOut⟩ := or_pair_pivot a b aValid bValid equal
    exact ⟨pairP a b, valid, chosen, _, _, same, different, Or.inl equalOut⟩

private theorem extendLift {spent : Nat} {bank : List (Signal Input)} {g : Signal Input}
    (lift : Lift spent bank) (move : CanMake bank g) : Lift (spent + 1) (g :: bank) := by
  intro p f k reach
  have next : Reach f (k + 1) (bank.map (pin p false)) :=
    Reach.extend (pin_canMake p false move) reach
  simpa only [Nat.add_assoc, Nat.add_comm 1 k] using lift p f (k + 1) next

private theorem useBudget {f : Signal Input} {bank : List (Signal Input)} {k limit : Nat}
    (proof : Reach f k bank) (within : k ≤ limit) : Reach f limit bank := by
  induction within with
  | refl => exact proof
  | step _ ih => exact Reach.weakenBudget _ _ ih

private theorem impossibleGate (lower : PinLower) {p : Fin 6} (valid : p.val < 4)
    {bank : List (Signal Input)} {a b : Signal Input} {op : Op} {k spent : Nat}
    (safe : Safe bank) (lift : Lift spent bank) (budget : spent + (k + 1) ≤ 8)
    (aIn : a ∈ bank) (bIn : b ∈ bank) (touch : a = raw p ∨ b = raw p)
    (compare : Comparison p (op.on a b)) (rest : Reach target k (op.on a b :: bank)) :
    False := by
  obtain ⟨x, y, agree, different, masked⟩ := compare
  have tracks : ∀ g ∈ op.on a b :: bank, g x ≠ g y → pin p false g = zero := by
    intro g member changeG
    rcases List.mem_cons.mp member with rfl | old
    · rcases masked with same | vanished
      · exact (changeG same).elim
      · exact vanished
    · exact safe.tracks valid agree g old changeG
  have mappedZero : zero ∈ (op.on a b :: bank).map (pin p false) :=
    List.mem_cons_of_mem _ (safe.mapZero p)
  obtain ⟨left, used, reach⟩ := Reach.pin_loses_of_difference x y different
    (target_pin_nonzero p valid) k (op.on a b :: bank) mappedZero tracks rest
  have mappedGate : pin p false (op.on a b) ∈ bank.map (pin p false) := by
    rcases touch with leftRaw | rightRaw
    · have pinLeft : pin p false a = zero := by rw [leftRaw, pin_raw]
      rcases pin_absorb_left op pinLeft with eliminated | copy
      · rw [eliminated]; exact safe.mapZero p
      · rw [copy]; exact List.mem_map.mpr ⟨b, bIn, rfl⟩
    · have pinRight : pin p false b = zero := by rw [rightRaw, pin_raw]
      rcases pin_absorb_right op pinRight with eliminated | copy
      · rw [eliminated]; exact safe.mapZero p
      · rw [copy]; exact List.mem_map.mpr ⟨a, aIn, rfl⟩
  have smaller : Reach (pin p false target) left (bank.map (pin p false)) := by
    apply Reach.weakenBank left ((op.on a b :: bank).map (pin p false)) _ _ reach
    intro g belongs
    rcases List.mem_cons.mp belongs with rfl | other
    · exact mappedGate
    · exact other
  exact lower p valid (useBudget (lift p _ left smaller) (by omega))

private theorem impossiblePrefix (lower : PinLower) : ∀ k spent : Nat,
    ∀ bank : List (Signal Input), spent + k ≤ 8 → Safe bank → Lift spent bank →
    ¬ Reach target k bank := by
  intro k
  induction k with
  | zero =>
      intro spent bank _ safe _ present
      exact target_not_in safe present
  | succ k ih =>
      intro spent bank budget safe lift reach
      rcases reach with present | ⟨_, ⟨op, a, aIn, b, bIn, rfl⟩, rest⟩
      · exact target_not_in safe present
      · rcases safe.2 a aIn with aSmall | ⟨aRaw, aValid, rfl⟩
        · rcases safe.2 b bIn with bSmall | ⟨bRaw, bValid, rfl⟩
          · have safe' : Safe (op.on a b :: bank) := by
              refine ⟨List.mem_cons_of_mem _ safe.1, ?_⟩
              intro signal member
              rcases List.mem_cons.mp member with rfl | old
              · exact Or.inl (aSmall.op bSmall op)
              · exact safe.2 signal old
            exact ih (spent + 1) (op.on a b :: bank) (by omega) safe'
              (extendLift lift ⟨op, a, aIn, b, bIn, rfl⟩) rest
          · cases op with
            | conj =>
              exact impossibleGate lower bValid safe lift budget aIn bIn (Or.inr rfl)
                (conj_right_comparison bValid a) rest
            | disj =>
              exact impossibleGate lower bValid safe lift budget aIn bIn (Or.inr rfl)
                (disj_left_small_comparison bValid aSmall) rest
            | diff =>
              exact impossibleGate lower bValid safe lift budget aIn bIn (Or.inr rfl)
                (diff_right_small_comparison bValid aSmall) rest
        · rcases safe.2 b bIn with bSmall | ⟨bRaw, bValid, rfl⟩
          · cases op with
            | conj =>
              exact impossibleGate lower aValid safe lift budget aIn bIn (Or.inl rfl)
                (conj_left_comparison aValid b) rest
            | disj =>
              exact impossibleGate lower aValid safe lift budget aIn bIn (Or.inl rfl)
                (disj_right_small_comparison aValid bSmall) rest
            | diff =>
              exact impossibleGate lower aValid safe lift budget aIn bIn (Or.inl rfl)
                (diff_left_comparison aValid b) rest
          · cases op with
            | conj =>
              exact impossibleGate lower aValid safe lift budget aIn bIn (Or.inl rfl)
                (conj_left_comparison aValid (raw bRaw)) rest
            | diff =>
              exact impossibleGate lower aValid safe lift budget aIn bIn (Or.inl rfl)
                (diff_left_comparison aValid (raw bRaw)) rest
            | disj =>
              obtain ⟨p, valid, chosen, compare⟩ := disj_pair_comparison aValid bValid
              have touch : raw aRaw = raw p ∨ raw bRaw = raw p :=
                chosen.elim (fun eq => Or.inl (congrArg raw eq.symm))
                  (fun eq => Or.inr (congrArg raw eq.symm))
              exact impossibleGate lower valid safe lift budget aIn bIn touch compare rest

private theorem base_safe : Safe (base 6) := by
  refine ⟨List.mem_cons_self, ?_⟩
  intro g member
  rcases List.mem_cons.mp member with rfl | memberRaw
  · exact Or.inl ⟨rfl, fun _ _ _ _ => rfl⟩
  · obtain ⟨p, rfl⟩ := List.mem_ofFn.mp memberRaw
    by_cases valid : p.val < 4
    · exact Or.inr ⟨p, valid, rfl⟩
    · left
      refine ⟨rfl, ?_⟩
      intro x y eq4 eq5
      have tail : p = 4 ∨ p = 5 := by
        have bound := p.isLt
        rcases (by omega : p.val = 4 ∨ p.val = 5) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases tail with rfl | rfl
      · exact eq4
      · exact eq5

private theorem base_lift : Lift 0 (base 6) := by
  intro p f k reach
  rw [Nat.zero_add]
  apply Reach.weakenBank k _ _ _ reach
  intro g belong
  obtain ⟨value, member, rfl⟩ := List.mem_map.mp belong
  rcases (base_pinBank p).2 value member with rfl | stable
  · rw [pin_raw]; exact (base_pinBank p).1
  · rwa [pin_stable stable false]

theorem no_six_at_eight (lower : PinLower) : ¬ Reach target 8 (base 6) :=
  impossiblePrefix lower 8 0 (base 6) (by decide) base_safe base_lift

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Five

open ZeroPhase (base expandInputs normalizeAt pin Reach setRaw zero)

abbrev Input := Fin 5 → Bool

def project : Fin 6 → Fin 6 → Option (Fin 5) :=
  ![![none, some 0, some 1, some 2, some 3, some 4],
    ![some 0, none, some 1, some 2, some 3, some 4],
    ![some 1, some 2, none, some 0, some 3, some 4],
    ![some 1, some 2, some 0, none, some 3, some 4],
    ![none, none, none, none, none, none],
    ![none, none, none, none, none, none]]

def problem (p : Fin 6) : PhaseBank.Problem :=
  if Six.strong p then PhaseBank.smallStrong else PhaseBank.smallWeak

def cofactor (p : Fin 6) (x : Input) : Bool :=
  pin p false Six.target (expandInputs (project p) x)

def row (index : Nat) (i : Fin 5) : Bool := index.testBit i.val

theorem project_pinned : ∀ p : Fin 6, project p p = none := by
  decide +kernel

theorem cofactor_eq_expanded (p : Fin 6) (x : Input) :
    cofactor p x = Six.target (expandInputs (project p) x) := by
  have same : setRaw p false (expandInputs (project p) x) = expandInputs (project p) x := by
    funext i
    by_cases atPin : i = p
    · subst i
      simp [setRaw, expandInputs, project_pinned]
    · simp [setRaw, atPin]
  have origin : setRaw p false (fun _ => false) = fun _ => false := by
    funext i
    simp [setRaw]
  simp [cofactor, pin, normalizeAt, same, origin, Six.origin]

theorem reach_compact (p : Fin 6) {k : Nat}
    (reach : Reach (pin p false Six.target) k (base 6)) :
    Reach (cofactor p) k (base 5) :=
  ZeroPhase.reach_expand_inputs (project p) reach

theorem full (p : Fin 6) : (problem p).full = 2^32 - 1 := by
  unfold problem
  split <;> rfl

theorem cap (p : Fin 6) : (problem p).cap = 6 := by
  unfold problem
  split <;> rfl

theorem target_bound : ∀ p : Fin 6, (problem p).target < 2^32 := by
  decide +kernel

theorem target_bit : ∀ p : Fin 6, p.val < 4 → ∀ r : Fin 32,
    (problem p).target.testBit r.val = cofactor p (row r.val) := by
  decide +kernel

theorem target_bit_above (p : Fin 6) (r : Nat) (high : 32 ≤ r) :
    (problem p).target.testBit r = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (target_bound p)
    (Nat.pow_le_pow_right (by decide) high))

theorem target_packed (p : Fin 6) (hp : p.val < 4) :
    (problem p).target = Nat.ofBits (fun r : Fin 32 => cofactor p (row r.val)) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases within : r < 32
  · exact (target_bit p hp ⟨r, within⟩).trans
      (Nat.testBit_ofBits_lt (fun q : Fin 32 => cofactor p (row q.val)) r within).symm
  · have high := Nat.le_of_not_gt within
    have rhs := Nat.testBit_lt_two_pow ((Nat.ofBits_lt_two_pow
      (fun q : Fin 32 => cofactor p (row q.val))).trans_le
        (Nat.pow_le_pow_right (by decide) high))
    exact (target_bit_above p r high).trans rhs.symm

private theorem fullBelow : ∀ r : Fin 32, (2^32 - 1 : Nat).testBit r.val = true := by
  decide +kernel

theorem full_bit (p : Fin 6) (r : Nat) : (problem p).full.testBit r = true ↔ r < 32 := by
  rw [full]
  by_cases bound : r < 32
  · exact ⟨fun _ => bound, fun _ => fullBelow ⟨r, bound⟩⟩
  · have high : 32 ≤ r := Nat.le_of_not_gt bound
    have less : 2^32 - 1 < 2^r := Nat.lt_of_lt_of_le (by decide)
      (Nat.pow_le_pow_right (by decide) high)
    constructor
    · intro h
      rw [Nat.testBit_lt_two_pow less] at h
      cases h
    · intro found
      exact (bound found).elim

private theorem positiveCheck : ∀ p : Fin 6, p.val < 4 →
    (problem p).positive.all (fun rowIndex => decide (rowIndex < 32) &&
      cofactor p (row rowIndex)) = true := by
  decide +kernel

theorem positive (p : Fin 6) (hp : p.val < 4) (r : Nat) (found : r ∈ (problem p).positive) :
    ∃ bound : r < 32, cofactor p (row (⟨r, bound⟩ : Fin 32).val) = true := by
  have checks := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (positiveCheck p hp) r found)
  exact ⟨of_decide_eq_true checks.1, checks.2⟩

theorem positive_iff : ∀ p : Fin 6, p.val < 4 → ∀ r : Fin 32,
    r.val ∈ (problem p).positive ↔ cofactor p (row r.val) = true := by
  decide +kernel

def rawSignature : Fin 5 → Nat :=
  ![2863311530, 3435973836, 4042322160, 4278255360, 4294901760]

theorem rawSignature_bit : ∀ (r : Fin 32) (i : Fin 5),
    (rawSignature i).testBit r.val = row r.val i := by
  decide +kernel

theorem rawSignature_bound : ∀ i : Fin 5, rawSignature i < 2^32 := by
  decide +kernel

theorem rawSignature_bit_above (i : Fin 5) (r : Nat) (high : 32 ≤ r) :
    (rawSignature i).testBit r = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rawSignature_bound i)
    (Nat.pow_le_pow_right (by decide) high))

theorem rawSignature_packed (i : Fin 5) :
    rawSignature i = Nat.ofBits (fun r : Fin 32 => row r.val i) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases within : r < 32
  · exact (rawSignature_bit ⟨r, within⟩ i).trans
      (Nat.testBit_ofBits_lt (fun q : Fin 32 => row q.val i) r within).symm
  · have high := Nat.le_of_not_gt within
    have rhs := Nat.testBit_lt_two_pow ((Nat.ofBits_lt_two_pow
      (fun q : Fin 32 => row q.val i)).trans_le
        (Nat.pow_le_pow_right (by decide) high))
    exact (rawSignature_bit_above i r high).trans rhs.symm

theorem initial (p : Fin 6) :
    (problem p).initial = List.ofFn (fun i : Fin 5 => PhaseBank.encode (rawSignature i) false) := by
  unfold problem
  split <;> decide +kernel

theorem initial_codes (p : Fin 6) :
    (problem p).initial = List.ofFn (fun i : Fin 5 =>
      PhaseBank.encode (Nat.ofBits (fun r : Fin 32 => row r.val i)) false) := by
  simpa only [rawSignature_packed] using initial p

theorem initial_nodup (p : Fin 6) : (problem p).initial.Nodup := by
  unfold problem
  split <;> decide +kernel

theorem initial_mem (p : Fin 6) (w : Nat) : w ∈ (problem p).initial ↔
    ∃ i : Fin 5, PhaseBank.encode (rawSignature i) false = w := by
  rw [initial]
  exact List.mem_ofFn

theorem initial_mem_codes (p : Fin 6) (w : Nat) : w ∈ (problem p).initial ↔
    ∃ i : Fin 5, PhaseBank.encode (Nat.ofBits (fun r : Fin 32 => row r.val i)) false = w := by
  rw [initial_codes]
  exact List.mem_ofFn

private def pivotLow : Fin 5 → Fin 32 := ![2, 1, 1, 2, 1]
private def pivotHigh : Fin 5 → Fin 32 := ![3, 3, 5, 10, 17]

private theorem pivotCheck : ∀ p : Fin 6, p.val < 4 → ∀ i : Fin 5,
    cofactor p (row (pivotLow i).val) ≠ cofactor p (row (pivotHigh i).val) ∧
    ∀ j : Fin 5, j ≠ i → row (pivotLow i).val j = row (pivotHigh i).val j := by
  decide +kernel

theorem essential_rows (p : Fin 6) (hp : p.val < 4) (i : Fin 5) :
    ∃ x y : Fin 32, cofactor p (row x.val) ≠ cofactor p (row y.val) ∧
      ∀ j : Fin 5, j ≠ i → row x.val j = row y.val j :=
  ⟨pivotLow i, pivotHigh i, pivotCheck p hp i⟩

theorem essential (p : Fin 6) (hp : p.val < 4) (i : Fin 5) :
    ∃ x y : Input, cofactor p x ≠ cofactor p y ∧ ∀ j : Fin 5, j ≠ i → x j = y j := by
  obtain ⟨x, y, diff, same⟩ := essential_rows p hp i
  exact ⟨row x.val, row y.val, diff, same⟩

private theorem row_three_true : ∀ p : Fin 6, p.val < 4 →
    cofactor p (row 3) = true := by decide +kernel

theorem nonzero_rows (p : Fin 6) (hp : p.val < 4) :
    (fun r : Fin 32 => cofactor p (row r.val)) ≠ zero := by
  intro eq
  have bad := congrFun eq (3 : Fin 32)
  exact Bool.noConfusion ((row_three_true p hp).symm.trans bad)

theorem nonzero (p : Fin 6) (hp : p.val < 4) : cofactor p ≠ zero := by
  intro eq
  have bad := congrFun eq (row 3)
  exact Bool.noConfusion ((row_three_true p hp).symm.trans bad)

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Five

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882

open PEqualNP.CircuitLowerBounds

def edges : List Nat := [0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7]

def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

def tape : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [8, 10]⟩,
   ⟨.or, [0, 2]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [13, 14]⟩,
   ⟨.or, [3, 5]⟩, ⟨.and, [16, 7]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [18, 17]⟩]

def witness : Circuit := ⟨tape, 19⟩

theorem tape_legal : ∀ g ∈ tape,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [tape]

theorem tape_count : tape.length = 12 := by decide

private def extend (a b c : Bool) (tail : Fin 5 → Bool) (i : Fin 8) : Bool :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else tail (Fin.ofNat 5 (i.val - 3))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem tape_tail_exact (a b c : Bool) :
    ∀ y : Fin 5 → Bool, witness.eval (List.ofFn (extend a b c y)) = target (extend a b c y) := by
  cases a <;> cases b <;> cases c <;> decide +kernel

theorem tape_exact : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = target x := by
  intro x
  let tail (i : Fin 5) := x (Fin.natAdd 3 i)
  have same : extend (x 0) (x 1) (x 2) tail = x := by
    have index : ∀ i : Fin 8, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      decide +kernel
    funext i
    rcases index i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [← same]
  exact tape_tail_exact (x 0) (x 1) (x 2) tail

theorem replacement_at_twelve (size : Nat) (h : 12 ≤ size) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ size ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gates' o').eval (List.ofFn x) = target x :=
  ⟨tape, 19, tape_legal, by simpa only [tape_count] using h, tape_exact⟩

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

private def inputBits (mask : Nat) (i : Fin 8) : Bool := mask.testBit i.val
private abbrev pin3 := pin (3 : Fin 8) false target
private abbrev pin32 := pin (2 : Fin 8) false pin3

private theorem target_origin : target (fun _ => false) = false := by decide +kernel

private theorem target_phase : normalizeAt (fun _ => false) target = target := by
  funext x
  simp [normalizeAt, target_origin]

private theorem requires_three : ¬ Independent (3 : Fin 8) target := by
  intro independent
  have different : target (setRaw (3 : Fin 8) false (inputBits 136)) ≠ target (inputBits 136) := by
    decide +kernel
  exact different (independent false (inputBits 136))

private theorem requires_two : ¬ Independent (2 : Fin 8) pin3 := by
  intro independent
  have different : pin3 (setRaw (2 : Fin 8) false (inputBits 68)) ≠ pin3 (inputBits 68) := by
    decide +kernel
  exact different (independent false (inputBits 68))

private theorem nonzero_of_true (f : Signal (Fin 8 → Bool)) (x : Fin 8 → Bool)
    (hx : f x = true) : f ≠ zero := by
  intro h
  rw [h] at hx
  exact Bool.false_ne_true hx

private theorem pin3_nonzero : pin3 ≠ zero :=
  nonzero_of_true pin3 (inputBits 17) (by decide +kernel)

private theorem pin32_nonzero : pin32 ≠ zero :=
  nonzero_of_true pin32 (inputBits 17) (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem compact_exact : ∀ x : Fin 6 → Bool,
    pin32 (expandSix28882 x) = Six.target x := by
  decide +kernel

private theorem reach_with_budget {X : Type} {f : Signal X} {bank : List (Signal X)}
    {k cap : Nat} (leCap : k ≤ cap) (found : Reach f k bank) : Reach f cap bank := by
  induction leCap with
  | refl => exact found
  | step _ ih => exact Reach.weakenBudget _ _ ih

theorem replacement_of_small_lower
    (smallLower : ¬ Reach Six.target 8 (base 6)) (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, Legal g)
    (eval : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x) = target x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, (Circuit.mk gates' o').eval (List.ofFn x) = target x := by
  classical
  by_cases large : 12 ≤ gates.length
  · exact replacement_at_twelve gates.length large
  · by_cases signed : ∃ g ∈ gates, g.op = GateOp.not
    · exfalso
      have count := nonNotCount_add_one_le gates signed
      have phase := reach_of_circuit target gates o legal eval
      rw [target_phase] at phase
      obtain ⟨left₁, first, after₃⟩ := reach_pin_loses_one (3 : Fin 8) false target
        requires_three pin3_nonzero _ _ (base_pinBank (3 : Fin 8)) phase
      obtain ⟨left₂, second, after₂⟩ := reach_pin_loses_one (2 : Fin 8) false pin3
        requires_two pin32_nonzero _ _ (base_pinBank (2 : Fin 8)) after₃
      have projected := reach_to_six28882 after₂
      have same : (fun x => pin32 (expandSix28882 x)) = Six.target := funext compact_exact
      rw [same] at projected
      exact smallLower (reach_with_budget (by omega) projected)
    · refine ⟨gates, o, ?_, Nat.le_refl _, eval⟩
      intro g member
      obtain ⟨basis, arity⟩ := legal g member
      refine ⟨?_, arity⟩
      rcases basis with hand | hor | hnot
      · exact Or.inl hand
      · exact Or.inr hor
      · exact (signed ⟨g, member, hnot⟩).elim

theorem exact_of_small_lower
    (smallLower : ¬ Reach Six.target 8 (base 6)) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _atMostOne eval
  exact replacement_of_small_lower smallLower gates o legal eval

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

theorem no_reach_on_table {n width : Nat}
    (rawRows : Fin n → Signal (Fin width)) (f : Signal (Fin width))
    (problem : PhaseBank.Problem)
    (full : problem.full = 2 ^ width - 1)
    (target : problem.target = Nat.ofBits f)
    (positive : ∀ i ∈ problem.positive, ∃ h : i < width, f ⟨i,h⟩ = true)
    (nonzero : f ≠ zero)
    (essential : ∀ i, ∃ x y, f x ≠ f y ∧ ∀ j, j ≠ i → rawRows j x = rawRows j y)
    (distinct : problem.initial.Nodup)
    (initial : ∀ w, w ∈ problem.initial ↔ ∃ i, signalCode (rawRows i) = w)
    (excluded : ∀ depth bank, PhaseBank.Reach problem depth bank →
      PhaseBank.solved problem bank = false) :
    ¬ Reach f problem.cap (zero :: List.ofFn rawRows) := by
  classical
  intro reach
  obtain ⟨steps, budget, live, run, subset, noZero⟩ :=
    Reach.live nonzero problem.cap (zero :: List.ofFn rawRows) List.mem_cons_self reach
  have exactBank : live = Finset.univ.image rawRows :=
    run.initial_of_essential rawRows subset noZero essential
  have members : ∀ w, w ∈ problem.initial ↔ ∃ v ∈ live, signalCode v = w := by
    intro w
    rw [initial, exactBank]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨rawRows i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i, rfl⟩
  have initialEq := canonical_initial_of_members problem live distinct members
  have startPath : PhaseBank.Reach problem 0 (encodeBank live) := by
    rw [← initialEq]
    exact PhaseBank.Reach.root
  obtain ⟨depth, _, bank, path, solved⟩ :=
    run.reaches_phase_bank problem full target positive 0 (by simpa using budget) startPath
  rw [excluded depth bank path] at solved
  contradiction

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

namespace PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six

open PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.ZeroPhase

theorem all_critical_pin_lower : PinLower := by
  intro p valid pinned
  let rawRows (i : Fin 5) (r : Fin 32) : Bool := Five.row r.val i
  let rows (r : Fin 32) := Five.row r.val
  let f (r : Fin 32) := Five.cofactor p (rows r)
  let problem := Five.problem p
  have compact := Five.reach_compact p pinned
  have mapped := Reach.precompose rows 6 (base 5) compact
  have source :
      (base 5).map (fun g r => g (rows r)) = zero :: List.ofFn rawRows := by
    simp [base, rawRows, rows, zero]
    rfl
  rw [source] at mapped
  have exclusion : ∀ depth bank, PhaseBank.Reach problem depth bank →
      PhaseBank.solved problem bank = false := by
    intro depth bank reach
    by_cases strongSide : strong p = true
    · have same : problem = PhaseBank.smallStrong := by
        simp [problem, Five.problem, strongSide]
      rw [same] at reach ⊢
      exact PhaseBank.smallStrong_no_solution reach
    · have weakSide : strong p = false := Bool.eq_false_iff.mpr strongSide
      have same : problem = PhaseBank.smallWeak := by
        simp [problem, Five.problem, weakSide]
      rw [same] at reach ⊢
      exact PhaseBank.smallWeak_no_solution reach
  have noReach := no_reach_on_table rawRows f problem (Five.full p)
    (Five.target_packed p valid) (Five.positive p valid) (Five.nonzero_rows p valid)
    (Five.essential_rows p valid) (Five.initial_nodup p) (Five.initial_mem_codes p) exclusion
  apply noReach
  change Reach _ (Five.problem p).cap _
  rw [Five.cap p]
  exact mapped

end PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six

theorem PEqualNP.Outside.L_meta_28882 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.exact_of_small_lower
    (PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six.no_six_at_eight
      PEqualNP.Outside.L_meta_28882_aux.LocalInvestigation.OneNot28882.Six.all_critical_pin_lower)
