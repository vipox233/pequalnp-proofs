import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket
import PEqualNP.MetaComplexity.Helpers.CoverCircuitList
import Mathlib

namespace PEqualNP.FiniteGateBank

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open MetaComplexity.CoverCircuit (run run_length run_append run_singleton)

open Classical

variable {X J : Type} {n : Nat}

/-- A list of legal gates, relative to n input wires. -/
structure Net (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n+j

def empty (n : Nat) : Net n := ⟨[],by simp [FanInTwo],by simp⟩

def Net.cost (p : Net n) := NotBracket.notCount ⟨p.gates,0⟩

def Net.has (p : Net n) (raw : X → List Bool) (f : X → Bool) :=
  ∃ i, i < n+p.gates.length ∧ ∀ x, (run p.gates (raw x)).getD i false = f x

def Grow (raw : X → List Bool) (p q : Net n) (size neg : Nat) : Prop :=
  (∀ f, p.has raw f → q.has raw f) ∧ q.gates.length ≤ p.gates.length+size ∧ q.cost=p.cost+neg

theorem start (raw : X → List Bool) (p : Net n) : Grow raw p p 0 0 := by simp [Grow]

theorem chain {raw : X → List Bool} {p q r : Net n} {a b c d : Nat}
    (pq : Grow raw p q a b) (qr : Grow raw q r c d) : Grow raw p r (a+c) (b+d) :=
  ⟨fun f h => qr.1 f (pq.1 f h),by have := pq.2.1; have := qr.2.1; omega,
    by rw [qr.2.2,pq.2.2,Nat.add_assoc]⟩

theorem allowance {raw : X → List Bool} {p q : Net n} {a b c : Nat}
    (grow : Grow raw p q a b) (le : a≤c) : Grow raw p q c b :=
  ⟨grow.1,grow.2.1.trans (Nat.add_le_add_left le _),grow.2.2⟩

private def extend (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) : Net n where
  gates := p.gates++[g]
  fan := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact p.fan v old
    · exact (List.mem_singleton.mp last) ▸ ops
  back := by
    intro j hj i hi
    by_cases h : j < p.gates.length
    · rw [List.getElem_append_left h] at hi
      exact p.back j h i hi
    · have len : j=p.gates.length := by simp at hj; omega
      subst j
      simp at hi
      exact ok i hi

private theorem emit {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (g : Gate)
    (ops : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (ok : ∀ i ∈ g.inputs, i < n+p.gates.length) :
    ∃ q, Grow raw p q 1 (if g.op=.not then 1 else 0) ∧
      q.has raw (fun x => g.op.eval (g.inputs.map (fun i => (run p.gates (raw x)).getD i false))) := by
  let q := extend p g ops ok
  have len (x : X) : (run p.gates (raw x)).length=n+p.gates.length := by rw [run_length,width]
  refine ⟨q,⟨?_,by simp [q,extend],?_⟩,n+p.gates.length,by simp [q,extend],?_⟩
  · rintro f ⟨i,hi,read⟩
    refine ⟨i,by simp [q,extend]; omega,?_⟩
    intro x
    change (run (p.gates++[g]) (raw x)).getD i false = _
    rw [run_append,run_singleton,List.getD_append _ _ _ _ ((len x).symm ▸ hi),read]
  · unfold Net.cost NotBracket.notCount
    simp only [q,extend,List.filter_append,List.length_append]
    split <;> simp_all
  · intro x
    change (run (p.gates++[g]) (raw x)).getD (n+p.gates.length) false = _
    rw [run_append,run_singleton,←len x]; simp

theorem binary {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a b : X → Bool) (ha : p.has raw a) (hb : p.has raw b) (isAnd : Bool) :
    ∃ q, Grow raw p q 1 0 ∧ q.has raw (fun x => if isAnd then a x && b x else a x || b x) := by
  obtain ⟨i,hi,readI⟩ := ha
  obtain ⟨j,hj,readJ⟩ := hb
  let g : Gate := ⟨if isAnd then .and else .or,[i,j]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by cases isAnd <;> simp [g]) (by simp [g,hi,hj])
  refine ⟨q,by cases isAnd <;> simpa [g] using grow,?_⟩
  convert w using 2 with x
  cases isAnd <;> simp only [g,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,
    MetaComplexity.CoverCircuit.eval_and2,MetaComplexity.CoverCircuit.eval_or2, readI,readJ] <;> rfl

theorem invert {raw : X → List Bool} (width : ∀ x, (raw x).length=n)
    (p : Net n) (a : X → Bool) (ha : p.has raw a) :
    ∃ q, Grow raw p q 1 1 ∧ q.has raw (fun x => !(a x)) := by
  obtain ⟨i,hi,readI⟩ := ha
  let g : Gate := ⟨.not,[i]⟩
  obtain ⟨q,grow,w⟩ := emit width p g (by simp [g]) (by simp [g,hi])
  refine ⟨q,by simpa [g] using grow,?_⟩
  convert w using 2 with x
  change (!(a x)) = (!((run p.gates (raw x)).getD i false))
  rw [readI]

theorem anyList {raw : X → List Bool} (width : ∀ x, (raw x).length=n) (p : Net n)
    (zero : p.has raw (fun _ => false)) (l : List J) (f : J → X → Bool)
    (known : ∀ i ∈ l, p.has raw (f i)) :
    ∃ q, Grow raw p q l.length 0 ∧ q.has raw (fun x => l.any (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p,start _ _,zero⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => known i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := binary width q _ _ (gq.1 _ (known j (by simp))) old false
    exact ⟨r,chain gq gr,by simpa [List.any_cons] using ans⟩

/-- Append a bounded implementation for every requested output, keeping all earlier wires available. -/
theorem batch {raw : X → List Bool} (p : Net n) (l : List J) (f : J → X → Bool) (s z : Nat)
    (build : ∀ j ∈ l, ∀ q : Net n, (∀ a, p.has raw a → q.has raw a) →
      ∃ r, Grow raw q r s z ∧ r.has raw (f j)) :
    ∃ r, Grow raw p r (l.length*s) (l.length*z) ∧ ∀ j ∈ l, r.has raw (f j) := by
  induction l with
  | nil => exact ⟨p,by simpa using start raw p,by simp⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => build i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := build j (by simp) q gq.1
    refine ⟨r,by simpa [Nat.succ_mul] using chain gq gr,?_⟩
    intro i mem
    rcases List.mem_cons.mp mem with rfl | h
    · exact ans
    · exact gr.1 _ (old i h)

theorem Net.readsBack (p : Net n) : ReadsBack n ⟨p.gates,0⟩ := by
  intro j hj i hi
  exact p.back j hj i (by simpa [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hi)

end PEqualNP.FiniteGateBank
