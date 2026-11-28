import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_53177_aux
namespace PulseList
open CircuitLowerBounds
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

end PulseList

namespace FiniteGateBank

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open PulseList (run run_length run_append run_singleton)

open Classical

variable {X J : Type} {n : Nat}

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
    PulseList.eval_and2,PulseList.eval_or2, readI,readJ] <;> rfl

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

end FiniteGateBank

namespace OrderedThresholdBank

open FiniteGateBank

variable {X : Type} {n : Nat}

def high (r : X → Nat) (i : Nat) (x : X) := decide (i ≤ r x)
def low (r : X → Nat) (i : Nat) (x : X) := decide (r x < i)

theorem decode (raw : X → List Bool) (width : ∀ x, (raw x).length=n) (b k : Nat)
    (room : k < 2^b) (r : X → Nat) (bound : ∀ x, r x≤k) (p : Net n)
    (zero : p.has raw (fun _ => false)) (known : ∀ i : Nat, 0 < i → i ≤ k → p.has raw (high r i)) :
    ∃ q, Grow raw p q (4*k+b) b ∧ ∀ i : Nat, 0 < i → i ≤ k → q.has raw (low r i) := by
  induction b generalizing k r p with
  | zero =>
    have : k=0 := by simpa using room
    subst k
    exact ⟨p,by simpa using start raw p,by omega⟩
  | succ b ih =>
    let a := k/2
    let m := a+1
    let rem (x : X) := if r x < m then r x else r x-m
    have small : k < 2*m := by dsimp [m,a]; omega
    have rem_le (x) : rem x≤a := by
      have := bound x
      dsimp [rem,m,a] at *
      split <;> omega
    have limited : a < 2^b := by dsimp [a]; rw [pow_succ] at room; omega
    have avail (i) (pos : 0 < i) : p.has raw (high r i) := by
      by_cases le : i≤k
      · exact known i pos le
      · convert zero using 2 with x
        simp [high,show ¬i≤r x by have := bound x; omega]
    obtain ⟨p₁,g₁,hneg⟩ := invert width p (high r m) (avail m (by dsimp [m]; omega))
    let ids := List.range a
    obtain ⟨p₂,g₂,hrem⟩ := batch (raw:=raw) p₁ ids (fun j => high rem (j+1)) 2 0 (by
      intro j hj q keep
      have index : j < a := List.mem_range.mp hj
      obtain ⟨u,gu,band⟩ := binary width q _ _ (keep _ hneg) (keep _ (g₁.1 _ (avail (j+1) (by omega)))) true
      obtain ⟨v,gv,bor⟩ := binary width u _ _ band (gu.1 _ (keep _ (g₁.1 _ (avail (m+(j+1)) (by omega))))) false
      refine ⟨v,chain gu gv,?_⟩
      convert bor using 2 with x
      have := bound x
      apply Bool.eq_iff_iff.mpr
      simp only [high,rem,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
        decide_eq_false_iff_not,ite_true,ite_false,Bool.false_eq_true]
      dsimp [m] at *
      split <;> omega)
    have residual (i) (pos : 0 < i) (le : i≤a) : p₂.has raw (high rem i) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact hrem j (List.mem_range.mpr (by omega))
    obtain ⟨p₃,g₃,remneg⟩ := ih a limited rem rem_le p₂ (g₂.1 _ (g₁.1 _ zero)) residual
    have g123 := chain (chain g₁ g₂) g₃
    have mid := g₃.1 _ (g₂.1 _ hneg)
    obtain ⟨q,g₄,outs⟩ := batch (raw:=raw) p₃ (List.range k) (fun j => low r (j+1)) 1 0 (by
      intro j hj u keep
      have jk : j < k := List.mem_range.mp hj
      by_cases below : j+1 < m
      · have le : j+1≤a := by dsimp [m] at below; omega
        obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1) (by omega) le)) true
        refine ⟨v,g,?_⟩
        convert h using 2 with x
        apply Bool.eq_iff_iff.mpr
        simp only [low,high,rem,ite_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
        split <;> omega
      · by_cases eq : j+1=m
        · refine ⟨u,allowance (start raw u) (by decide : 0≤1),?_⟩
          convert keep _ mid using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [high,low,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          omega
        · have above : m < j+1 := by omega
          have ix : j+1-m≤a := by dsimp [m,a] at *; omega
          obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1-m) (by omega) ix)) false
          refine ⟨v,g,?_⟩
          convert h using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [low,high,rem,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          split <;> omega)
    have gr := chain g123 g₄
    simp only [ids,List.length_range,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at gr
    refine ⟨q,?_,?_⟩
    · have gr' := allowance gr (show 1 + a*2 + (4*a+b) + k ≤ 4*k+(b+1) by dsimp [a]; omega)
      simpa [Nat.add_comm 1 b] using gr'
    · intro i pos le
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact outs j (List.mem_range.mpr (by omega))

end OrderedThresholdBank

namespace RunIntervalBank

open FiniteGateBank OrderedThresholdBank

variable {m : Nat}

def cuts (k : Nat) (f : Nat → Fin m → Bool) : Finset Nat :=
  (Finset.range (k+1)).filter (fun e => 0 < e ∧ ∃ j, f (e-1) j=true ∧ f e j=false)

def starts (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) : Finset Nat :=
  (Finset.range (k+1)).filter (fun a => f a j=true ∧ (a=0 ∨ f (a-1) j=false))

private def stop (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) (a : Nat) : Nat :=
  Nat.find (show ∃ e, e=k+1 ∨ a < e ∧ f e j=false from ⟨k+1,Or.inl rfl⟩)

private theorem stop_spec {k a} {f : Nat → Fin m → Bool} {j : Fin m} :
    stop k f j a=k+1 ∨ a < stop k f j a ∧ f (stop k f j a) j=false := by
  unfold stop
  exact Nat.find_spec (p:=fun e => e=k+1 ∨ a < e ∧ f e j=false) _

private theorem stop_le {k a e} {f : Nat → Fin m → Bool} {j : Fin m}
    (h : e=k+1 ∨ a < e ∧ f e j=false) : stop k f j a ≤ e := Nat.find_min' _ h

private theorem interior {k a u} {f : Nat → Fin m → Bool} {j : Fin m}
    (one : f a j=true) (lo : a ≤ u) (hi : u < stop k f j a) : f u j=true := by
  by_contra! h
  have zero : f u j=false := Bool.eq_false_iff.mpr h
  by_cases eq : a=u
  · simp_all
  · have b := stop_le (k:=k) (Or.inr ⟨show a < u by omega,zero⟩)
    omega

private theorem ends {k a} {f : Nat → Fin m → Bool} {j : Fin m} (ha : a∈starts k f j) :
    stop k f j a=k+1 ∨ stop k f j a ∈ cuts k f := by
  rcases stop_spec (k:=k) (f:=f) (j:=j) (a:=a) with last | ⟨lt,zero⟩
  · exact Or.inl last
  · have upper := stop_le (a:=a) (f:=f) (j:=j) (Or.inl rfl : k+1=k+1 ∨ _)
    by_cases last : stop k f j a=k+1
    · exact Or.inl last
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,j,
        interior (k:=k) (Finset.mem_filter.mp ha).2.1 (by omega) (by omega),zero⟩)

private theorem represent (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) (u : Nat)
    (ku : u ≤ k) : f u j=true ↔ ∃ a ∈ starts k f j, a ≤ u ∧ u < stop k f j a := by
  constructor
  · intro one
    let P (a : Nat) := a ≤ u ∧ ∀ v, a ≤ v → v ≤ u → f v j=true
    have hp : ∃ a, P a := ⟨u,le_rfl,fun v lo hi => le_antisymm hi lo ▸ one⟩
    let a := Nat.find hp
    have prop : P a := Nat.find_spec hp
    have start : a=0 ∨ f (a-1) j=false := by
      by_cases za : a=0
      · exact Or.inl za
      · right
        apply Bool.eq_false_iff.mpr
        intro yes
        have prev : P (a-1) := by
          refine ⟨by have := prop.1; omega,?_⟩
          intro v lo hi
          by_cases eq : v=a-1
          · simpa [eq] using yes
          · exact prop.2 _ (by omega) hi
        have minimal := Nat.find_min' hp prev
        change a ≤ a-1 at minimal
        omega
    have au := prop.1
    refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prop.2 _ le_rfl au,start⟩,au,?_⟩
    rcases stop_spec (k:=k) (f:=f) (j:=j) (a:=a) with last | ⟨lt,zero⟩
    · omega
    · by_contra! h
      have o := prop.2 _ lt.le h
      simp_all
  · rintro ⟨a,ha,lo,hi⟩
    exact interior (Finset.mem_filter.mp ha).2.1 lo hi

private def place (s : Finset Nat) (x : Nat) :=
  Finset.univ.sup (fun i : Fin s.card => if s.orderEmbOfFin rfl i ≤ x then i.val+1 else 0)

private theorem place_le (s : Finset Nat) (x : Nat) : place s x ≤ s.card := by
  apply Finset.sup_le
  intro i _
  split <;> have := i.isLt <;> omega

private theorem place_at (s : Finset Nat) (i : Fin s.card) (x : Nat) :
    i.val+1 ≤ place s x ↔ s.orderEmbOfFin rfl i ≤ x := by
  classical
  constructor
  · intro large
    by_contra! bad
    have upper : place s x ≤ i.val := by
      apply Finset.sup_le
      intro j _
      split
      · rename_i yes
        have lt : s.orderEmbOfFin rfl j < s.orderEmbOfFin rfl i := lt_of_le_of_lt yes bad
        have jj : j < i := (s.orderEmbOfFin rfl).lt_iff_lt.mp lt
        omega
      · omega
    omega
  · intro le
    have z := Finset.le_sup (s:=Finset.univ)
      (f:=fun j : Fin s.card => if s.orderEmbOfFin rfl j ≤ x then j.val+1 else 0) (Finset.mem_univ i)
    simpa only [place,if_pos le] using z

private def word (k x : Nat) (i : Fin k) := decide (i.val < x)
private def raw (k : Nat) (x : Fin (k+1)) := List.ofFn (word k x.val) ++ [false,true]

private theorem width (k) (x) : (raw k x).length=k+2 := by simp [raw]

private theorem basic (k : Nat) (v : Nat) :
    (empty (k+2)).has (raw k) (fun x => decide (v ≤ x.val)) := by
  by_cases zv : v=0
  · refine ⟨k+1,by simp [empty],?_⟩
    intro x
    simp [empty,raw,PulseList.run,List.getD_eq_getElem?_getD,zv,
      List.getElem?_append_right (by simp : (List.ofFn (word k x.val)).length ≤ k+1)]
  · by_cases fits : v ≤ k
    · let i : Fin k := ⟨v-1,by omega⟩
      refine ⟨i.val,by have := i.isLt; simp [empty]; omega,?_⟩
      intro x
      change (List.ofFn (word k x.val) ++ [false,true]).getD i.val false=_
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using i.isLt : i.val < (List.ofFn (word k x.val)).length),word,i,show v-1 < x.val ↔ v ≤ x.val by omega]
    · refine ⟨k,by simp [empty],?_⟩
      intro x
      have no : ¬v ≤ x.val := by have := x.isLt; omega
      simp [raw,empty,PulseList.run,List.getD_eq_getElem?_getD,no]

private theorem allOutputs {X J : Type} [DecidableEq J] {w : Nat} (xs : X → List Bool)
    (p : Net w) (js : Finset J) (cost : J → Nat) (f : J → X → Bool)
    (build : ∀ j ∈ js, ∀ u : Net w, (∀ a, p.has xs a → u.has xs a) →
      ∃ v, Grow xs u v (cost j) 0 ∧ v.has xs (f j)) :
    ∃ q, Grow xs p q (js.sum cost) 0 ∧ ∀ j ∈ js, q.has xs (f j) := by
  induction js using Finset.induction_on with
  | empty => exact ⟨p,by simpa using start xs p,by simp⟩
  | @insert j js hj ih =>
    obtain ⟨u,g,old⟩ := ih (fun i hi => build i (Finset.mem_insert_of_mem hi))
    obtain ⟨v,gv,new⟩ := build j (Finset.mem_insert_self ..) u g.1
    refine ⟨v,by simpa [Finset.sum_insert hj,Nat.add_comm] using chain g gv,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | h
    · exact new
    · exact gv.1 _ (old i h)

theorem upper (k b : Nat) (f : Nat → Fin m → Bool) (room : (cuts k f).card < 2^b) :
    ∃ (C : CircuitLowerBounds.Circuit) (tap : Fin m → Fin (k+2+C.size)),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
      C.output < k+2+C.size ∧ NotBracket.notCount C=b ∧
      C.size ≤ b+4*(cuts k f).card+2*Finset.univ.sum (fun j => (starts k f j).card) ∧
      ∀ (x : Fin (k+1)) j, (C.wires (raw k x)).getD (tap j).val false=f x.val j := by
  classical
  let s := cuts k f
  let r (x : Fin (k+1)) := place s x.val
  let p := empty (k+2)
  have zero : p.has (raw k) (fun _ => false) := by
    convert basic k (k+1) using 2 with x
    simp [show ¬k+1 ≤ x.val from Nat.not_le_of_gt x.isLt]
  have known (i : Nat) (pos : 0 < i) (le : i ≤ s.card) : p.has (raw k) (high r i) := by
    let j : Fin s.card := ⟨i-1,by omega⟩
    convert basic k (s.orderEmbOfFin rfl j) using 2 with x
    have eq : i=j.val+1 := by dsimp [j]; omega
    simp only [high,r]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hh := place_at s j x.val
    rwa [←eq] at hh
  obtain ⟨q,g,lows⟩ := decode (raw k) (width k) b s.card room r (fun x => place_le s x.val) p zero known
  have ending (j) (a) (ha : a∈starts k f j) : q.has (raw k) (fun x => decide (x.val < stop k f j a)) := by
    rcases ends ha with last | mem
    · convert g.1 _ (basic k 0) using 2 with x
      simp [last,x.isLt]
    · obtain ⟨i,eq⟩ : ∃ i : Fin s.card, s.orderEmbOfFin rfl i=stop k f j a := by
        exact (show stop k f j a∈Set.range (s.orderEmbOfFin rfl) by simpa [s] using mem)
      convert lows (i.val+1) (by omega) (by have := i.isLt; omega) using 2 with x
      apply Bool.eq_iff_iff.mpr
      simp only [low,decide_eq_true_eq]
      have hh := place_at s i x.val
      rw [eq] at hh
      change x.val < stop k f j a ↔ place s x.val < i.val+1
      omega
  obtain ⟨v,gv,out⟩ := allOutputs (raw k) q Finset.univ (fun j => 2*(starts k f j).card)
    (fun j x => f x.val j) (by
      intro j _ u keep
      let l := (starts k f j).toList
      let active (a : Nat) (x : Fin (k+1)) := decide (a ≤ x.val) && decide (x.val < stop k f j a)
      obtain ⟨w,gw,intervals⟩ := batch (raw:=raw k) u l active 1 0 (by
        intro a ha v preserve
        obtain ⟨w,g',h⟩ := binary (width k) v _ _ (preserve _ (keep _ (g.1 _ (basic k a))))
          (preserve _ (keep _ (ending j a (by simpa [l] using ha)))) true
        exact ⟨w,g',by simpa [active] using h⟩)
      obtain ⟨v,gv,h⟩ := anyList (width k) w (gw.1 _ (keep _ (g.1 _ zero))) l active intervals
      refine ⟨v,by simpa [l,two_mul] using chain gw gv,?_⟩
      convert h using 2 with x
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true,active,Bool.and_eq_true,decide_eq_true_eq,l,Finset.mem_toList]
      exact represent _ _ _ _ (by have := x.isLt; omega))
  let C : CircuitLowerBounds.Circuit := ⟨v.gates,0⟩
  have tap (j : Fin m) := out j (Finset.mem_univ _)
  let ts (j : Fin m) : Fin (k+2+C.size) := ⟨(tap j).choose,(tap j).choose_spec.1⟩
  have total := chain g gv
  refine ⟨C,ts,v.fan,v.readsBack,by simp [C],?_,?_,fun x j => (tap j).choose_spec.2 x⟩
  · change v.cost=b
    simpa [p,empty,Net.cost,NotBracket.notCount] using total.2.2
  · change v.gates.length ≤ _
    have h := total.2.1
    simpa [p,empty,s,Finset.mul_sum,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

end RunIntervalBank

namespace MarkedInversionRank
open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: code gs a
    | _ => code gs a

private def mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

private theorem code_len (gs : List Gate) (w : List Bool) :
    (code gs w).length = (gs.filter mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [code,h,mark,List.filter_cons,ih]

private def ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

private theorem extend_order {x y : List Bool} (w : ordered x y) {a b : Bool}
    (ab : a=true → b=true) : ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

private theorem output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : ordered x y) (same : code gs x=code gs y) :
    ordered (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change ordered (run gs (tick x g)) (run gs (tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [code,h,List.cons.injEq] at same
      apply ih rest (extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

private theorem input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
private def driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + driverNumber bs

private theorem driver_bound (l : List Bool) : driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [driverNumber,pow_succ] <;> omega

private theorem driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : driverNumber a=driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := driver_bound xs
      have h₂ := driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

private theorem driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : ordered a b) :
    driverNumber (code gs a) ≤ driverNumber (code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : code [g] a=code [g] b) : ordered (tick a g) (tick b g) :=
      output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · simp only [code,eq]
      exact ih tailops (growth (by simp [code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (code gs (tick a g)).length=(code gs (tick b g)).length := by simp [code_len]
      change driverNumber (code (g::gs) a) ≤ driverNumber (code (g::gs) b)
      simp only [code,eq]
      rw [←eq]
      change driverNumber (out a :: code gs (tick a g)) ≤ driverNumber (out b :: code gs (tick b g))
      by_cases same : out a=out b
      · have next : ordered (tick a g) (tick b g) := extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(code gs (tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := driver_bound (code gs (tick a g))
        rw [len] at bound
        simp only [driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem circuit_rank {n : Nat} (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ h : (Fin n → Bool) → Nat, Monotone h ∧ (∀ x, h x < 2^PEqualNP.NotBracket.notCount C) ∧
      ∀ x y, x ≤ y → h x = h y → ∀ w,
        (C.wires (List.ofFn x ++ [false,true])).getD w false=true →
        (C.wires (List.ofFn y ++ [false,true])).getD w false=true := by
  let raw (x : Fin n → Bool) := List.ofFn x ++ [false,true]
  let h (x : Fin n → Bool) := driverNumber (code C.gates (raw x))
  have ops (g : Gate) (mem : g ∈ C.gates) := (fan g mem).1
  have order {x y : Fin n → Bool} (xy : x ≤ y) : ordered (raw x) (raw y) := by
    apply input_order
    intro i hi
    have v := xy i
    rw [hi] at v
    exact le_antisymm (by cases y i <;> decide) v
  have size : (C.gates.filter mark).length = PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases eq : g.op <;> simp [mark,eq]
  refine ⟨h,fun x y xy => driver_mono _ ops (order xy),?_,?_⟩
  · intro x
    simpa only [h,code_len,size] using driver_bound (code C.gates (raw x))
  · intro x y xy eq w
    have same : code C.gates (raw x)=code C.gates (raw y) := driver_injective (by simp [code_len]) eq
    exact (output_order ops (order xy) same).2 w

end MarkedInversionRank

end PEqualNP.Outside.L_meta_53177_aux
namespace PEqualNP.Outside.L_meta_53177_aux.Assignment
private theorem highest {β : Type*} [DecidableEq β] (c : β → ℕ) (p : ℕ) (B : Finset β)
    (hp : p ≤ B.card) : ∃ Q ⊆ B, Q.card = p ∧
    ∀ i ∈ Q, ∀ j ∈ B, j ∉ Q → c j ≤ c i := by
  induction p generalizing B with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ p ih =>
    obtain ⟨x,hx,hm⟩ := B.exists_max_image c (Finset.card_pos.mp (by omega))
    obtain ⟨Q,hQ,hc,hord⟩ := ih (B.erase x) (by rw [Finset.card_erase_of_mem hx]; omega)
    have hxQ : x ∉ Q := fun h => (Finset.mem_erase.mp (hQ h)).1 rfl
    refine ⟨insert x Q, Finset.insert_subset hx (hQ.trans (Finset.erase_subset ..)),
      by simp [hxQ,hc], ?_⟩
    intro i hi j hj hjQ
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hm j hj
    · exact hord i hi j (Finset.mem_erase.mpr ⟨fun e => hjQ (e ▸ Finset.mem_insert_self ..),hj⟩)
        (fun h => hjQ (Finset.mem_insert_of_mem h))

theorem assign {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (h : α → ℕ) (S : Finset α) (c : β → ℕ)
    (H : ∀ U ⊆ S, U.sum h ≤ ∑ t, min U.card (c t)) :
    ∃ rows : α → Finset β, (∀ r ∈ S, (rows r).card = h r) ∧
    ∀ t, (S.filter fun r => t ∈ rows r).card ≤ c t := by
  classical
  induction S using Finset.induction_on generalizing c with
  | empty => exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert a S ha ih =>
    let B := Finset.univ.filter fun t => 0 < c t
    have id1 (t : β) : min 1 (c t) = if 0 < c t then 1 else 0 := by split <;> omega
    have hp : h a ≤ B.card := by
      have z := H {a} (by simp)
      rw [Finset.sum_singleton,Finset.card_singleton] at z
      simpa only [B,Finset.card_filter,id1] using z
    obtain ⟨Q,hQ,hc,hord⟩ := highest c (h a) B hp
    have pos {t} (ht : t ∈ Q) : 0 < c t := (Finset.mem_filter.mp (hQ ht)).2
    have order {i j} (hi : i ∈ Q) (hj : j ∉ Q) : c j ≤ c i := by
      by_cases hb : j ∈ B
      · exact hord i hi j hb hj
      · have : ¬ 0 < c j := fun w => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,w⟩)
        omega
    let d := fun t => if t ∈ Q then c t - 1 else c t
    have next (U : Finset α) (hU : U ⊆ S) : U.sum h ≤ ∑ t, min U.card (d t) := by
      by_cases all : ∀ t ∈ Q, U.card < c t
      · have eq (t : β) : min U.card (d t) = min U.card (c t) := by
          by_cases ht : t ∈ Q
          · have := all t ht
            simp only [d,ite_eq_left ht]; omega
          · simp [d,ht]
        simpa only [eq] using H U (hU.trans (Finset.subset_insert ..))
      · push Not at all
        obtain ⟨i,hi,low⟩ := all
        have eq (t : β) : min U.card (d t) + (if t ∈ Q then 1 else 0) = min (U.card+1) (c t) := by
          by_cases ht : t ∈ Q
          · have := pos ht
            simp only [d,ite_eq_left ht]; omega
          · have := order hi ht
            simp only [d,ite_eq_right ht]; omega
        have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun t _ => eq t)
        rw [Finset.sum_add_distrib] at hs
        have hc' : (∑ t : β, if t ∈ Q then 1 else 0) = h a := by simpa using hc
        rw [hc'] at hs
        have haU : a ∉ U := fun w => ha (hU w)
        have z := H (insert a U) (Finset.insert_subset_insert _ hU)
        rw [Finset.sum_insert haU,Finset.card_insert_of_notMem haU] at z
        rw [← hs,Nat.add_comm (h a)] at z
        exact Nat.le_of_add_le_add_right z
    obtain ⟨rows,hr,ht⟩ := ih d next
    let out := fun r => if r = a then Q else rows r
    refine ⟨out, ?_, ?_⟩
    · intro r hmem
      rcases Finset.mem_insert.mp hmem with rfl | w
      · simpa [out] using hc
      · simpa [out,show r ≠ a from fun e => ha (e ▸ w)] using hr r w
    · intro t
      have eq : (S.filter fun r => t ∈ out r) = S.filter fun r => t ∈ rows r := by
        apply Finset.filter_congr
        intro r hr'
        simp [out,show r ≠ a from fun e => ha (e ▸ hr')]
      have bound := ht t
      rw [Finset.filter_insert,eq]
      by_cases hmem : t ∈ Q
      · have hw : t ∈ out a := by simpa [out] using hmem
        have hp' := pos hmem
        simp only [ite_eq_left hw,Finset.card_insert_of_notMem (fun w => ha (Finset.mem_filter.mp w).1)]
        simp only [d,ite_eq_left hmem] at bound
        omega
      · have hw : t ∉ out a := by simpa [out] using hmem
        simpa [hw,d,hmem] using bound
end PEqualNP.Outside.L_meta_53177_aux.Assignment
namespace PEqualNP.Outside.L_meta_53177_aux
open CircuitLowerBounds
def word (n k : ℕ) (i : Fin n) := decide (i.val < k)
def raw (n k : ℕ) := List.ofFn (word n k) ++ [false,true]
def val (C : Circuit) (n k j : ℕ) := (C.wires (raw n k)).getD j false

theorem fallBound {R n b : ℕ} (C : Circuit) (A : ℕ) (S : Finset (Fin R))
    (fan : MetaComplexity.FanInTwo C) (cap : NotBracket.notCount C ≤ b)
    (edge : ∀ r ∈ S, val C n (3*r.val+1) A = true ∧ val C n (3*r.val+2) A = false) :
    S.card ≤ 2^b-1 := by
  obtain ⟨rank,mono,room,persist⟩ := MarkedInversionRank.circuit_rank (n:=n) C fan
  have step {x y : ℕ} (h : x ≤ y) : word n x ≤ word n y := by
    intro i
    apply Bool.le_iff_imp.mpr
    simpa only [word,decide_eq_true_eq] using (fun z : i.val < x => lt_of_lt_of_le z h)
  let f := fun r : Fin R => rank (word n (3*r.val+1))
  have jump (r : Fin R) (hr : r ∈ S) : f r < rank (word n (3*r.val+2)) := by
    have inc := step (x:=3*r.val+1) (y:=3*r.val+2) (by omega)
    obtain ⟨yes,no⟩ := edge r hr
    apply lt_of_le_of_ne (mono inc)
    intro eq
    have force := persist _ _ inc eq A yes
    exact Bool.noConfusion (no.symm.trans force)
  have strictly (r s : Fin R) (hr : r ∈ S) (lt : r < s) : f r < f s :=
    (jump r hr).trans_le (mono (step (by change 3*r.val+2 ≤ 3*s.val+1; change r.val < s.val at lt; omega)))
  have count := Finset.card_le_card_of_injOn (s:=S) (t:=Finset.range (2^b-1)) f (by
    intro r hr
    have j := jump r hr
    have lim := (room (word n (3*r.val+2))).trans_le (Nat.pow_le_pow_right (by decide) cap)
    exact Finset.mem_range.mpr (by omega)) (by
    intro r hr s hs eq
    rcases lt_trichotomy r s with lt | e | gt
    · exact False.elim ((strictly r s hr lt).ne eq)
    · exact e
    · exact False.elim ((strictly s r hs gt).ne eq.symm))
  simpa using count
end PEqualNP.Outside.L_meta_53177_aux
namespace PEqualNP.Outside.L_meta_53177_aux
open CircuitLowerBounds
private def pattern {R : ℕ} (S : Finset (Fin R)) (k : ℕ) (_ : Fin 1) : Bool :=
  decide (∃ r ∈ S, k = 3*r.val+1)

theorem wireTrue (C : Circuit) (n k : ℕ) : val C n k (n+1) = true := by
  change (PulseList.run C.gates (raw n k)).getD (n+1) false = _
  rw [PulseList.getD_run _ _ _ (by simp [raw])]
  simp [raw,List.getD_eq_getElem?_getD,List.getElem?_append_right (show (List.ofFn (word n k)).length ≤ n+1 by simp)]

theorem single {n R b : ℕ} (S : Finset (Fin R)) (hc : S.card ≤ 2^b-1) :
    ∃ (C : Circuit) (A : ℕ), MetaComplexity.FanInTwo C ∧
    MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ NotBracket.notCount C ≤ b ∧
    C.output < n+2+C.size ∧ A < n+2+C.size ∧ C.size ≤ b + 6*S.card ∧
    ∀ k : Fin (n+1), val C n k.val A = true ↔ ∃ r ∈ S, k.val=3*r.val+1 := by
  let f := pattern S
  have cutBound : (RunIntervalBank.cuts n f).card ≤ S.card := by
    apply le_trans (Finset.card_le_card (t := S.image (fun r => 3*r.val+2)) ?_) Finset.card_image_le
    intro e he
    obtain ⟨_,ep,j,yes,_⟩ := Finset.mem_filter.mp he
    obtain ⟨r,hr,eq⟩ : ∃ r ∈ S, e-1 = 3*r.val+1 := of_decide_eq_true yes
    exact Finset.mem_image.mpr ⟨r,hr,by omega⟩
  have startBound (j : Fin 1) : (RunIntervalBank.starts n f j).card ≤ S.card := by
    apply le_trans (Finset.card_le_card (t := S.image (fun r => 3*r.val+1)) ?_) Finset.card_image_le
    intro e he
    obtain ⟨_,yes,_⟩ := Finset.mem_filter.mp he
    obtain ⟨r,hr,eq⟩ : ∃ r ∈ S, e = 3*r.val+1 := of_decide_eq_true yes
    exact Finset.mem_image.mpr ⟨r,hr,eq.symm⟩
  have room : (RunIntervalBank.cuts n f).card < 2^b := by have := Nat.two_pow_pos b; omega
  obtain ⟨C,tap,fan,back,out,neg,size,read⟩ := RunIntervalBank.upper n b f room
  refine ⟨C,(tap 0).val,fan,back,neg.le,out,(tap 0).isLt,?_,?_⟩
  · rw [Fin.sum_univ_one] at size
    have := startBound 0
    omega
  · intro k
    change (C.wires (raw n k.val)).getD (tap 0).val false = true ↔ _
    have read' : (C.wires (raw n k.val)).getD (tap 0).val false = f k.val 0 := read k 0
    rw [read']
    exact decide_eq_true_iff
end PEqualNP.Outside.L_meta_53177_aux

namespace PEqualNP.Outside.L_meta_53177_aux
open CircuitLowerBounds
def hit {T R : ℕ} (n : ℕ) (C : Fin T → Circuit) (A B : Fin T → ℕ) (t : Fin T) (r : Fin R) :=
  val (C t) n (3*r.val+1) (A t) && val (C t) n (3*r.val+1) (B t)

def Fit {T R : ℕ} (n : ℕ) (b : Fin T → ℕ) (h : Fin R → ℕ) (tight : Prop) :=
  ∃ (C : Fin T → Circuit) (A B : Fin T → ℕ),
    (∀ t, MetaComplexity.FanInTwo (C t) ∧ MetaComplexity.NestedCover.ReadsBack (n+2) (C t) ∧
      NotBracket.notCount (C t) ≤ b t ∧ (C t).output < n+2+(C t).size ∧
      A t < n+2+(C t).size ∧ B t < n+2+(C t).size) ∧
    (∀ r : Fin R, (∀ t, val (C t) n (3*r.val) (A t) = false ∧ val (C t) n (3*r.val+2) (A t) = false) ∧
      (Finset.univ.filter (fun t => hit n C A B t r = true)).card = h r) ∧
    (tight → ∀ t, B t = n+1 ∧ (C t).size ≤ b t + 6*(Finset.univ.filter
      (fun r : Fin R => hit n C A B t r = true)).card ∧
      ∀ k : Fin (n+1), val (C t) n k.val (A t) = true ↔
        ∃ r : Fin R, k.val = 3*r.val+1 ∧ hit n C A B t r = true)

def Cuts {T R : ℕ} (b : Fin T → ℕ) (h : Fin R → ℕ) :=
  ∀ U : Finset (Fin R), U.sum h ≤ ∑ t, min U.card (2^(b t)-1)

theorem required {T R n : ℕ} {b : Fin T → ℕ} {h : Fin R → ℕ} (fit : Fit n b h False) :
    Cuts b h := by
  obtain ⟨C,A,B,legal,obs,_⟩ := fit
  intro U
  let live := hit (R:=R) n C A B
  have countRow (r : Fin R) : h r = ∑ t, if live t r = true then 1 else 0 := by
    rw [← (obs r).2, Finset.card_filter]
  calc
    U.sum h = ∑ r ∈ U, ∑ t, if live t r = true then 1 else 0 :=
      Finset.sum_congr rfl (fun r _ => countRow r)
    _ = ∑ t, ∑ r ∈ U, if live t r = true then 1 else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _
      rw [← Finset.card_filter]
      apply le_min (Finset.card_le_card (Finset.filter_subset ..))
      apply fallBound (C t) (A t) _ (legal t).1 (legal t).2.2.1
      intro r hr
      have high := Finset.mem_filter.mp hr
      exact ⟨(Bool.and_eq_true_iff.mp high.2).1,((obs r).1 t).2⟩

theorem sufficient {T R n : ℕ} {b : Fin T → ℕ} {h : Fin R → ℕ}
    (space : 3*R ≤ n+1) (cuts : Cuts b h) : Fit n b h True := by
  classical
  obtain ⟨rows,hrows,hcols⟩ := Assignment.assign h Finset.univ (fun t => 2^(b t)-1)
    (fun U _ => cuts U)
  let S := fun t : Fin T => Finset.univ.filter (fun r : Fin R => t ∈ rows r)
  choose C A fan back neg out tap size read using
    (fun t : Fin T => single (n:=n) (S t) (hcols t))
  let B := fun _ : Fin T => n+1
  have mid (r : Fin R) (t : Fin T) :
      val (C t) n (3*r.val+1) (A t) = true ↔ t ∈ rows r := by
    have ri := r.isLt
    rw [read t ⟨3*r.val+1,by omega⟩]
    constructor
    · rintro ⟨s,hs,eq⟩
      change 3*r.val+1 = 3*s.val+1 at eq
      have same : r = s := Fin.ext (by omega)
      subst s
      exact (Finset.mem_filter.mp hs).2
    · intro yes
      exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩,rfl⟩
  have hits (t : Fin T) (r : Fin R) : hit n C A B t r = true ↔ t ∈ rows r := by
    simpa [hit,B,wireTrue] using mid r t
  refine ⟨C,A,B,fun t => ⟨fan t,back t,neg t,out t,tap t,by dsimp [B]; omega⟩,?_,?_⟩
  · intro r
    constructor
    · intro t
      have ri := r.isLt
      have off (k : Fin (n+1)) (avoid : ∀ s : Fin R, k.val ≠ 3*s.val+1) :
          val (C t) n k.val (A t) = false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        obtain ⟨s,_,eq⟩ := (read t k).mp yes
        exact avoid s eq
      exact ⟨off ⟨3*r.val,by omega⟩ (fun s => by dsimp; omega),
        off ⟨3*r.val+2,by omega⟩ (fun s => by dsimp; omega)⟩
    · have same : Finset.univ.filter (fun t => hit n C A B t r = true) = rows r := by
        ext t
        simp [hits]
      rw [same]
      exact hrows r (Finset.mem_univ _)
  · intro _ t
    have same : Finset.univ.filter (fun r : Fin R => hit n C A B t r = true) = S t := by
      ext r
      simp [hits,S]
    refine ⟨rfl, same.symm ▸ size t, ?_⟩
    intro k
    rw [read t k]
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,hits]
    exact exists_congr (fun _ => and_comm)
end PEqualNP.Outside.L_meta_53177_aux

open PEqualNP.Outside.L_meta_53177_aux in
theorem PEqualNP.Outside.L_meta_53177 :
∀ (n T R : Nat) (b : Fin T → Nat) (h : Fin R → Nat), 3*R ≤ n+1 →
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let raw := fun k : Nat => List.ofFn (fun i : Fin n => decide (i.val < k)) ++ [false,true]
  let fit := fun (tight : Prop) => ∃ (C : Fin T → Circ) (A B : Fin T → Nat),
    let val := fun (t : Fin T) (k j : Nat) => ((C t).wires (raw k)).getD j false
    let hit := fun (t : Fin T) (r : Fin R) =>
      val t (3*r.val+1) (A t) && val t (3*r.val+1) (B t)
    (∀ t, PEqualNP.MetaComplexity.FanInTwo (C t) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) (C t) ∧
      PEqualNP.NotBracket.notCount (C t) ≤ b t ∧ (C t).output < n+2+(C t).size ∧
      A t < n+2+(C t).size ∧ B t < n+2+(C t).size) ∧
    (∀ r : Fin R, (∀ t, val t (3*r.val) (A t) = false ∧ val t (3*r.val+2) (A t) = false) ∧
      ((Finset.univ : Finset (Fin T)).filter (fun t => hit t r = true)).card = h r) ∧
    (tight → ∀ t, B t = n+1 ∧
      (C t).size ≤ b t + 6*((Finset.univ : Finset (Fin R)).filter (fun r => hit t r = true)).card ∧
      ∀ k : Fin (n+1), val t k.val (A t) = true ↔
        ∃ r : Fin R, k.val = 3*r.val+1 ∧ hit t r = true)
  let cuts := ∀ U : Finset (Fin R), U.sum h ≤
    (Finset.univ : Finset (Fin T)).sum (fun t => min U.card (2^(b t)-1))
  (fit False ↔ cuts) ∧ (cuts → fit True) := by
  intro n T R b h space
  change (Fit n b h False ↔ Cuts b h) ∧ (Cuts b h → Fit n b h True)
  refine ⟨⟨required, ?_⟩, sufficient space⟩
  intro cuts
  obtain ⟨C,A,B,hc,hr,_⟩ := sufficient space cuts
  exact ⟨C,A,B,hc,hr,False.elim⟩
