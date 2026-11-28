import PEqualNP.Defs
import Mathlib.Data.Finset.Sort
namespace PEqualNP.Outside.L_meta_53180
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

open PulseList
open Classical
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
lemma run_gate_eval {n : Nat} (C : Circuit) (hR : ReadsBack n C)
    (w0 : List Bool) (hw : w0.length = n) (i : Fin C.size) :
    (C.wires w0).getD (n + i.val) false =
      (C.gates.get i).op.eval
        ((C.gates.get i).inputs.map fun k => (C.wires w0).getD k false) := by
  have hi : i.val < C.gates.length := i.isLt
  let g := C.gates.get i
  have hsplit : C.gates = C.gates.take i.val ++ [g] ++ C.gates.drop (i.val + 1) := by
    have h1 := List.take_append_drop i.val C.gates
    have h2 : C.gates.drop i.val = g :: C.gates.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]; rfl
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  have hlen1 : (run (C.gates.take i.val) w0).length = n + i.val := by
    rw [run_length, hw, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hlen2 : (run (C.gates.take i.val ++ [g]) w0).length = n + i.val + 1 := by
    rw [run_append, run_singleton, List.length_append, hlen1]; rfl
  have hget : (C.wires w0).getD (n + i.val) false =
      g.op.eval (g.inputs.map fun k => (run (C.gates.take i.val) w0).getD k false) := by
    change (run C.gates w0).getD (n + i.val) false = _
    conv_lhs => rw [hsplit, run_append]
    rw [getD_run _ _ _ (by rw [hlen2]; omega)]
    rw [run_append, run_singleton, ← hlen1, getD_snoc_length]
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hkl : k < n + i.val := by
    have hr := hR i.val hi k
    have hga : gateAt C i.val = g := by
      simp [gateAt, g, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    rw [hga] at hr
    exact hr hk
  change (run (C.gates.take i.val) w0).getD k false = (run C.gates w0).getD k false
  conv_rhs => rw [hsplit, List.append_assoc, run_append]
  exact (getD_run _ _ _ (by rw [hlen1]; exact hkl)).symm

lemma notCount_eq_card (C : Circuit) :
    PEqualNP.NotBracket.notCount C =
      (Finset.univ.filter (fun i : Fin C.size => (C.gates.get i).op = GateOp.not)).card := by
  unfold PEqualNP.NotBracket.notCount Circuit.size
  generalize C.gates = gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.filter_cons]
    have hsplit : (Finset.univ.filter (fun i : Fin (g :: gs).length => ((g :: gs).get i).op = GateOp.not)).card =
        (if g.op = GateOp.not then 1 else 0) +
        (Finset.univ.filter (fun i : Fin gs.length => (gs.get i).op = GateOp.not)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      exact Fin.sum_univ_succ (fun i : Fin (g :: gs).length => if ((g :: gs).get i).op = GateOp.not then 1 else 0)
    rw [hsplit, ← ih]
    by_cases h : g.op = GateOp.not
    · simp [h, Nat.add_comm]
    · simp [h]


lemma mem_A_false {m d : Nat} (X : Fin m → Fin d → Bool) :
    let inputs := fun t => List.ofFn (X t) ++ [false, true]
    let A := (Finset.range (d + 2)).image (fun j t => (inputs t).getD j false)
    (fun _ : Fin m => false) ∈ A := by
  intro inputs A
  refine Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr (by omega), ?_⟩
  funext t
  simp [inputs, List.getD_eq_getElem?_getD]

lemma mem_A_true {m d : Nat} (X : Fin m → Fin d → Bool) :
    let inputs := fun t => List.ofFn (X t) ++ [false, true]
    let A := (Finset.range (d + 2)).image (fun j t => (inputs t).getD j false)
    (fun _ : Fin m => true) ∈ A := by
  intro inputs A
  refine Finset.mem_image.mpr ⟨d + 1, Finset.mem_range.mpr (by omega), ?_⟩
  funext t
  simp [inputs, List.getD_eq_getElem?_getD]



abbrev Word (m : ℕ) := Fin (m+1) → Bool

def sg {m} (f : Word m) (s : Bool) : Word m := fun t => xor (f t) s
def nm {m} (f : Word m) := sg f (f 0)

theorem sg0 {m} (f : Word m) : sg f false = f := by funext t; simp [sg]
theorem sgs {m} (f : Word m) (a b : Bool) : sg (sg f a) b = sg f (xor a b) := by
  funext t; cases a <;> cases b <;> cases e : f t <;> simp [sg,e]
theorem nm_sg {m} (f : Word m) (b : Bool) : nm (sg f b)=nm f := by
  funext t; change xor (xor (f t) b) (xor (f 0) b) = xor (f t) (f 0); cases b <;> cases f t <;> cases f 0 <;> rfl
theorem nm_id {m} (f : Word m) : nm (nm f) = nm f := nm_sg f _
theorem recover {m} (f : Word m) : sg (nm f) (f 0) = f := by rw [nm,sgs,Bool.xor_self,sg0]
theorem sg_flip {m} (f : Word m) (b : Bool) : (fun t => !(sg f b t))=sg f (!b) := by
  funext t; cases b <;> cases e : f t <;> simp [sg,e]

def ins {m d} (X : Fin (m+1) → Fin d → Bool) (t : Fin (m+1)) := List.ofFn (X t) ++ [false,true]
noncomputable def given {m d} (X : Fin (m+1) → Fin d → Bool) : Finset (Word m) :=
  (Finset.range (d+2)).image (fun i t => (ins X t).getD i false)
def wire {m d} (X : Fin (m+1) → Fin d → Bool) (C : Circuit) (j : ℕ) : Word m := fun t => (C.wires (ins X t)).getD j false

theorem rawWire {m d} (X : Fin (m+1) → Fin d → Bool) (C : Circuit) {j : ℕ} (hj : j<d+2) :
    wire X C j = fun t => (ins X t).getD j false := by
  funext t; exact PulseList.getD_run _ _ _ (by simpa [ins] using hj)

theorem rawEq {m d} (X : Fin (m+1) → Fin d → Bool) (C : Circuit) : given X = (Finset.range (d+2)).image (wire X C) := by
  unfold given; apply Finset.image_congr; intro j hj; exact (rawWire X C (Finset.mem_range.mp hj)).symm

theorem constants {m d} (X : Fin (m+1) → Fin d → Bool) (b : Bool) : (fun _ => b) ∈ given X := by
  cases b
  · exact mem_A_false X
  · exact mem_A_true X

def Physical {m d a} (X : Fin (m+1) → Fin d → Bool) (T : Fin a → Word m) (p cp cn W : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin a → ℕ), FanInTwo C ∧ ReadsBack (d+2) C ∧ C.output < d+2+C.size ∧
    (∀ j, tap j < d+2+C.size) ∧ (∀ j t, wire X C (tap j) t=T j t) ∧
    C.size-NotBracket.notCount C ≤ p ∧ cp*(C.size-NotBracket.notCount C)+cn*NotBracket.notCount C ≤ W

def prodW {m h} (l r : Fin h → Word m) (ls rs : Fin h → Bool) (i : Fin h) : Word m :=
  fun t => sg (l i) (ls i) t && sg (r i) (rs i) t

def Ask {m h a} (R : Finset (Word m)) (T : Fin a → Word m) (B l r : Fin h → Word m) (ls rs : Fin h → Bool)
    (f : Word m) (v : Fin (h+1)) (s : Bool) : Prop :=
  (v=0 ∧ (sg f s ∈ R ∨ ∃ j, T j=sg f s)) ∨ ∃ i : Fin h, v=i.succ ∧
    ((B i=f ∧ prodW l r ls rs i 0 = s) ∨ (l i=f ∧ ls i=s) ∨ (r i=f ∧ rs i=s))

noncomputable def costs {m h a} (R : Finset (Word m)) (T : Fin a → Word m) (B l r : Fin h → Word m)
    (ls rs : Fin h → Bool) (P : Fin (h+1) → Bool) : Finset (Word m) :=
  (R.image nm ∪ Finset.univ.image B).filter fun f => ¬(f ∈ R ∧ sg f true ∈ R) ∧
    ∃ v w s t, Ask R T B l r ls rs f v s ∧ Ask R T B l r ls rs f w t ∧ xor (P v) s ≠ xor (P w) t

def Program {m a} (R : Finset (Word m)) (T : Fin a → Word m) (p cp cn W : ℕ) : Prop :=
  ∃ (h : ℕ) (B l r : Fin h → Word m) (ls rs : Fin h → Bool),
    let older := fun (i : Fin h) (f : Word m) => f ∈ R.image nm ∨ ∃ j < i, B j=f
    h ≤ p ∧ Function.Injective B ∧
    (∀ i, B i ∉ R.image nm ∧ older i (l i) ∧ older i (r i) ∧ B i=nm (prodW l r ls rs i)) ∧
    (∀ j, nm (T j) ∈ R.image nm ∨ ∃ i, B i=nm (T j)) ∧
    ∃ P : Fin (h+1) → Bool, P 0=false ∧ cp*h+cn*(costs R T B l r ls rs P).card ≤ W

theorem price {h c n k cp cn : ℕ} (hk : k≤n) (hp : h≤n-k) (hs : h+c≤n) (le : cn≤cp) :
    cp*h+cn*c ≤ cp*(n-k)+cn*k := by
  have p := Nat.mul_le_mul_left (cp-cn) hp
  have q := Nat.mul_le_mul_left cn hs
  have eq : cp=cp-cn+cn := by omega
  conv_lhs => lhs; rw [eq,Nat.add_mul]
  conv_rhs => lhs; rw [eq,Nat.add_mul]
  rw [Nat.mul_add] at q
  have z : cn*(n-k)+cn*k=cn*n := by rw [←Nat.mul_add,Nat.sub_add_cancel hk]
  omega

open Classical CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

noncomputable def fresh {m : ℕ} (n s : ℕ) (w : ℕ → Word m) : Finset (Fin s) :=
  Finset.univ.filter fun i => ∀ j < n+i.val, nm (w j) ≠ nm (w (n+i.val))

theorem fresh_spec {m n s} {w : ℕ → Word m} {i : Fin s} : i ∈ fresh n s w ↔ ∀ j < n+i.val, nm (w j) ≠ nm (w (n+i.val)) := by simp [fresh]

theorem first_at {m} (n s : ℕ) (w : ℕ → Word m) (j : ℕ) (h : j<n+s) :
    nm (w j) ∈ ((Finset.range n).image w).image nm ∨
    ∃ i ∈ fresh n s w, n+i.val ≤ j ∧ nm (w (n+i.val)) = nm (w j) := by
  have atj : ∃ k, nm (w k)=nm (w j) := ⟨j,rfl⟩
  let k := Nat.find atj
  have val : nm (w k)=nm (w j) := Nat.find_spec atj
  have le : k≤j := Nat.find_min' atj rfl
  by_cases hk : k<n
  · exact Or.inl (Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr hk,rfl⟩,val⟩)
  · let i : Fin s := ⟨k-n,by omega⟩
    have heq : n+i.val=k := by dsimp [i]; omega
    right; refine ⟨i,fresh_spec.mpr ?_,heq ▸ le,heq ▸ val⟩
    intro u hu eq
    rw [heq] at hu eq
    exact (Nat.find_min atj hu) (eq.trans val)

theorem fresh_inj {m n s} (w : ℕ → Word m) : Set.InjOn (fun i : Fin s => nm (w (n+i.val))) (fresh n s w) := by
  intro i hi j hj eq
  rcases lt_trichotomy i j with h|h|h
  · exact ((fresh_spec.mp hj _ (Nat.add_lt_add_left h n)) eq).elim
  · exact h
  · exact ((fresh_spec.mp hi _ (Nat.add_lt_add_left h n)) eq.symm).elim

theorem second_paid {m n s} (w : ℕ → Word m) (R : Finset (Word m)) (hR : R=(Finset.range n).image w)
    (f : Word m) (hf : nm f=f) (raw : ¬(f∈R ∧ sg f true∈R)) (j k : ℕ) (hj : j<n+s) (hk : k<n+s)
    (a b : Bool) (diff : a≠b) (fj : w j=sg f a) (fk : w k=sg f b) :
    f ∈ ((fresh n s w)ᶜ).image (fun i : Fin s => nm (w (n+i.val))) := by
  have ne : sg f a≠sg f b := by
    intro eq; have e := congrFun eq 0
    change xor (f 0) a = xor (f 0) b at e
    cases a <;> cases b <;> cases f 0 <;> simp_all
  have jk : j≠k := fun eq => ne (fj.symm.trans ((congrArg w eq).trans fk))
  have big : ¬(j<n ∧ k<n) := by
    rintro ⟨u,v⟩; apply raw
    have x : sg f a∈R := hR ▸ Finset.mem_image.mpr ⟨_,Finset.mem_range.mpr u,fj⟩
    have y : sg f b∈R := hR ▸ Finset.mem_image.mpr ⟨_,Finset.mem_range.mpr v,fk⟩
    cases a <;> cases b <;> simp_all [sg0]
  have jn : nm (w j) = f := by rw [fj,nm_sg,hf]
  have kn : nm (w k) = f := by rw [fk,nm_sg,hf]
  have take (u v : ℕ) (hu : u<v) (hv : n≤v) (hs : v<n+s) (wu : nm (w u)=f) (wv : nm (w v)=f) :
      f ∈ ((fresh n s w)ᶜ).image (fun i : Fin s => nm (w (n+i.val))) := by
    let i : Fin s := ⟨v-n,by omega⟩
    have vi : n+i.val=v := by dsimp [i]; omega
    refine Finset.mem_image.mpr ⟨i,Finset.mem_compl.mpr ?_,vi ▸ wv⟩
    intro h; exact fresh_spec.mp h u (vi ▸ hu) (vi ▸ wu.trans wv.symm)
  rcases lt_or_gt_of_ne jk with lt|lt
  · exact take j k lt (by omega) hk jn kn
  · exact take k j lt (by omega) hj kn jn

def mix {m} (flip : Bool) (u v : Word m) : Word m := fun t => if flip then u t || v t else u t && v t

theorem gateBirth {m d} (X : Fin (m+1) → Fin d → Bool) (C : Circuit) (fan : FanInTwo C) (back : ReadsBack (d+2) C)
    (i : Fin C.size) (hi : i ∈ fresh (d+2) C.size (wire X C)) :
    (C.gates.get i).op≠.not ∧ ∃ (a b : ℕ) (flip : Bool), a<d+2+i.val ∧ b<d+2+i.val ∧
      wire X C (d+2+i.val) = mix flip (wire X C a) (wire X C b) := by
  let g := C.gates.get i
  let w := wire X C
  let j := d+2+i.val
  have old := fresh_spec.mp hi
  have hc (b : Bool) (eq : w j=(fun _ => b)) : False := by
    have mem := constants X b; rw [rawEq X C] at mem
    obtain ⟨k,hk,h⟩ := Finset.mem_image.mp mem
    apply old k (by have := Finset.mem_range.mp hk; omega)
    exact congrArg nm (h.trans eq.symm)
  have he (t) : w j t = g.op.eval (g.inputs.map fun k => w k t) := run_gate_eval C back _ (by simp [ins]) i
  have gb (k) (hk : k ∈ g.inputs) : k < j := by
    apply back i.val i.isLt k
    have heq : gateAt C i.val = g := by
      simp [gateAt,g,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.isLt]; rfl
    rw [heq]; exact hk
  obtain ⟨hop,hl⟩ := fan g (List.get_mem _ _)
  change g.op=.and ∨ g.op=.or ∨ g.op=.not at hop
  have bn (pn : g.op=.not) : False := by
    cases es : g.inputs with
    | nil => exact hc true (funext fun t => by simpa [pn,es,GateOp.eval] using he t)
    | cons a rest =>
      have eq : w j = sg (w a) true := funext fun t => by simpa [sg,pn,es,GateOp.eval] using he t
      exact old a (gb _ (by simp [es])) ((congrArg nm eq).trans (nm_sg _ _)).symm
  refine ⟨bn,?_⟩
  rcases hop with op|op|op <;> try exact (bn op).elim
  all_goals
    cases es : g.inputs with
    | nil => exact (hc _ (funext fun t => by simpa [op,es,GateOp.eval] using he t)).elim
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : w j=w a := funext fun t => by simpa [op,es,GateOp.eval] using he t
        exact (old _ (gb _ (by simp [es])) (congrArg nm eq.symm)).elim
      | cons b tail =>
        have et : tail=[] := List.length_eq_zero_iff.mp (by rw [es] at hl; simp only [List.length_cons] at hl; omega)
        subst tail
        first | exact ⟨a,b,false,gb _ (by simp [es]),gb _ (by simp [es]),funext fun t => by simpa [mix,op,es,GateOp.eval] using he t⟩
              | exact ⟨a,b,true,gb _ (by simp [es]),gb _ (by simp [es]),funext fun t => by simpa [mix,op,es,GateOp.eval] using he t⟩


open Classical CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

theorem sig_prod {m} (u v : Word m) (b : Bool) :
    (fun t => sg (nm u) (xor (u 0) b) t && sg (nm v) (xor (v 0) b) t) = sg (mix b u v) b := by
  funext t; simp only [sg,nm,mix]
  cases b <;> cases u 0 <;> cases v 0 <;> cases u t <;> cases v t <;> rfl

theorem unswitch {m} (u : Word m) (b : Bool) : sg (nm u) (xor b (xor (u 0) b)) = u := by
  rw [show xor b (xor (u 0) b) = u 0 by cases b <;> cases u 0 <;> rfl]; exact recover _

theorem forward {m d a p cp cn W : ℕ} (X : Fin (m+1) → Fin d → Bool) (T : Fin a → Word m) (cheap : cn≤cp)
    (phys : Physical X T p cp cn W) : Program (given X) T p cp cn W := by
  classical
  obtain ⟨C,tap,fan,back,_,taplt,target,pcap,wcap⟩ := phys
  let n := d+2
  let w := wire X C
  let R := given X
  have hR : R=(Finset.range n).image w := rawEq X C
  let K := fresh n C.size w
  let h := K.card
  let e : Fin h ↪o Fin C.size := K.orderEmbOfFin rfl
  have em (j) : e j∈K := by simp [e]
  have sur {i} (hi : i∈K) : ∃ j, e j=i := by
    change i ∈ Set.range (K.orderEmbOfFin rfl); simpa using hi
  let idx (i : Fin h) := n+(e i).val
  have fresh' (i) : ∀ j < idx i, nm (w j) ≠ nm (w (idx i)) := fresh_spec.mp (em i)
  have nodes (i : Fin h) := gateBirth X C fan back (e i) (em i)
  choose lidx ridx flip hl hr hx using fun i => (nodes i).2
  change ∀ i, w (idx i) = mix (flip i) (w (lidx i)) (w (ridx i)) at hx
  let B (i : Fin h) := nm (w (idx i))
  let l (i : Fin h) := nm (w (lidx i))
  let r (i : Fin h) := nm (w (ridx i))
  let ls (i : Fin h) := xor (w (lidx i) 0) (flip i)
  let rs (i : Fin h) := xor (w (ridx i) 0) (flip i)
  let product := prodW l r ls rs
  have pr (i) : product i=sg (w (idx i)) (flip i) := by rw [hx]; exact sig_prod _ _ _
  have nbin : h ≤ C.size-NotBracket.notCount C := by
    let N := Finset.univ.filter (fun i : Fin C.size => (C.gates.get i).op=.not)
    have sub : K⊆Nᶜ := by
      intro i hi; obtain ⟨j,rfl⟩ := sur hi; exact Finset.mem_compl.mpr (fun h => (nodes j).1 (Finset.mem_filter.mp h).2)
    have hh := Finset.card_le_card sub
    rw [Finset.card_compl, Fintype.card_fin] at hh
    change h ≤ C.size - N.card at hh
    exact (notCount_eq_card C).symm ▸ hh
  have prior (j) (hj : j<n+C.size) : nm (w j)∈R.image nm ∨ ∃ u, idx u≤j ∧ B u=nm (w j) := by
    rcases first_at n C.size w j hj with a|⟨i,hi,lt,eq⟩
    · exact Or.inl (hR ▸ a)
    · obtain ⟨t,rfl⟩ := sur hi; exact Or.inr ⟨t,lt,eq⟩
  have older (j i) (hj : j < idx i) : nm (w j)∈R.image nm ∨ ∃ u < i, B u=nm (w j) := by
    have bound : idx i<n+C.size := Nat.add_lt_add_left (e i).isLt _
    rcases prior j (hj.trans bound) with a|⟨u,hu,eq⟩
    · exact Or.inl a
    · refine Or.inr ⟨u,e.lt_iff_lt.mp ?_,eq⟩
      have ht := hu.trans_lt hj; exact (Nat.add_lt_add_iff_left).mp ht
  refine ⟨h,B,l,r,ls,rs,nbin.trans pcap,?_,?_,?_,?_⟩
  · intro i j eq; apply e.injective; exact fresh_inj w (em i) (em j) eq
  · intro i; refine ⟨?_,older _ _ (hl i),older _ _ (hr i),?_⟩
    · change B i ∉ R.image nm; rw [hR]; rintro hi; obtain ⟨u,hm,hu⟩ := Finset.mem_image.mp hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hm
      exact fresh' i k (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_add_right _ _)) hu
    · change nm (w (idx i))=nm (product i); rw [pr,nm_sg]
  · intro j; have et : w (tap j)=T j := funext (target j)
    rcases prior (tap j) (taplt j) with b|⟨i,_,bi⟩
    · exact Or.inl (et ▸ b)
    · exact Or.inr ⟨i,et ▸ bi⟩
  · let P : Fin (h+1) → Bool := Fin.cases false flip
    refine ⟨P,rfl,?_⟩
    have lives (f v s) (ask : Ask R T B l r ls rs f v s) : ∃ j < n+C.size, w j = sg f (xor (P v) s) := by
      rcases ask with ⟨rfl,mem|⟨i,hi⟩⟩|⟨i,rfl,⟨rfl,eq⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
      · rw [hR] at mem; obtain ⟨j,hj,hv⟩ := Finset.mem_image.mp mem
        exact ⟨j,(Finset.mem_range.mp hj).trans_le (Nat.le_add_right _ _),by simpa [P] using hv⟩
      · exact ⟨_,taplt i,by simpa [P] using (funext (target i)).trans hi⟩
      · refine ⟨idx i,Nat.add_lt_add_left (e i).isLt _,?_⟩
        change w (idx i) = sg (nm (w (idx i))) (xor (flip i) s)
        change product i 0 = s at eq
        rw [pr] at eq; rw [←eq]; exact (unswitch _ _).symm
      · exact ⟨lidx i,(hl i).trans (Nat.add_lt_add_left (e i).isLt _),(unswitch _ _).symm⟩
      · exact ⟨ridx i,(hr i).trans (Nat.add_lt_add_left (e i).isLt _),(unswitch _ _).symm⟩
    have sub : costs R T B l r ls rs P ⊆ Kᶜ.image (fun i : Fin C.size => nm (w (n+i.val))) := by
      intro f mem; obtain ⟨cl,raw,v,v',s,s',av,aw,ne⟩ := Finset.mem_filter.mp mem
      have nf : nm f=f := by
        rcases Finset.mem_union.mp cl with h|h <;> obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp h <;> apply nm_id
      obtain ⟨j,hj,hv⟩ := lives _ _ _ av; obtain ⟨k,hk,hw⟩ := lives _ _ _ aw
      exact second_paid w R hR f nf raw j k hj hk _ _ ne hv hw
    have hc := (Finset.card_le_card sub).trans Finset.card_image_le
    have hh : h+(costs R T B l r ls rs P).card ≤ C.size := by
      rw [Finset.card_compl,Fintype.card_fin] at hc
      have hh := Finset.card_le_univ K; rw [Fintype.card_fin] at hh; dsimp only [h]; omega
    have hn : NotBracket.notCount C ≤ C.size := by
      rw [notCount_eq_card]; simpa using Finset.card_le_univ (Finset.univ.filter (fun i : Fin C.size => (C.gates.get i).op=.not))
    exact (price hn nbin hh cheap).trans wcap


open Classical CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover FiniteGateBank

theorem dual_emit {m} (l r : Word m) (ls rs b : Bool) :
    (fun t => if !b then sg l (xor b ls) t && sg r (xor b rs) t else sg l (xor b ls) t || sg r (xor b rs) t) =
    sg (fun t => sg l ls t && sg r rs t) b := by
  funext t; cases b <;> cases ls <;> cases rs <;> cases u : l t <;> cases v : r t <;> simp [sg,u,v]

theorem backward {m d a p cp cn W : ℕ} (X : Fin (m+1) → Fin d → Bool) (T : Fin a → Word m)
    (prog : Program (given X) T p cp cn W) : Physical X T p cp cn W := by
  classical
  obtain ⟨h,B,l,r,ls,rs,budget,inj,shape,goal,P,P0,limit⟩ := prog
  let R := given X
  let A := R.image nm
  let allC := A ∪ Finset.univ.image B
  let Ch := costs R T B l r ls rs P
  let prod := prodW l r ls rs
  let need (f : Word m) (b : Bool) := ∃ v s, Ask R T B l r ls rs f v s ∧ xor (P v) s=b
  have different {f : Word m} {s t : Bool} (un : f∈allC) (raw : ¬(f∈R ∧ sg f true∈R))
      (nd : need f s) (ne : need f t) (diff : s≠t) : f∈Ch := by
    obtain ⟨i,u,hi,rfl⟩ := nd; obtain ⟨j,v,hj,rfl⟩ := ne
    exact Finset.mem_filter.mpr ⟨un,raw,i,j,u,v,hi,hj,diff⟩
  let input := ins X
  let n := d+2
  have width (t) : (input t).length=n := by simp [input,ins,n]
  let q0 := empty n
  have rawHas {f} (hf : f∈R) : q0.has input f := by
    obtain ⟨j,hj,hf⟩ := Finset.mem_image.mp hf
    exact ⟨j,by simpa [q0,empty,n] using Finset.mem_range.mp hj,congrFun hf⟩
  let pick (f : Word m) := decide (f∉R)
  have origin {f} (hf : f∈A) : sg f (pick f) ∈ R := by
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    by_cases hn : nm g ∈ R
    · simpa [pick,hn,sg0] using hn
    · have h0 : g 0=true := by
        cases e : g 0 with
        | true => rfl
        | false => exact (hn (by simpa [nm,e,sg0] using hg)).elim
      have er := recover g; rw [h0] at er; simpa [pick,hn,er] using hg
  have ask0 {f s} (raw : sg f s∈R ∨ ∃ j,T j=sg f s) : need f s :=
    ⟨0,s,Or.inl ⟨rfl,raw⟩,by simp [P0]⟩
  let loc (k : ℕ) := A ∪ ((Finset.univ : Finset (Fin h)).filter (fun i => i.val<k)).image B
  have here {k} {f : Word m} : f∈loc k ↔ f∈A ∨ ∃ i : Fin h, i.val<k ∧ B i=f := by simp [loc]
  have loc0 : loc 0=A := by ext f; simp [here]
  let E := A ∩ Ch
  obtain ⟨first,gfirst,flips⟩ := batch (p:=q0) (raw:=input) (l:=E.toList)
    (fun f => sg f (!(pick f))) 1 1 (by
      intro f hf net keep
      have hm : f∈E := by simpa using hf
      obtain ⟨v,g,bit⟩ := invert width net _ (keep _ (rawHas (origin (Finset.mem_inter.mp hm).1)))
      exact ⟨v,g,sg_flip _ _ ▸ bit⟩)
  have initial (f : Word m) (hf : f∈A) (s : Bool) (dem : need f s) : first.has input (sg f s) := by
    by_cases eq : s=pick f
    · subst s; exact gfirst.1 _ (rawHas (origin hf))
    · by_cases both : f∈R ∧ sg f true∈R
      · cases s
        · rw [sg0]; exact gfirst.1 _ (rawHas both.1)
        · exact gfirst.1 _ (rawHas both.2)
      · have ch := different (Finset.mem_union_left _ hf) both dem (ask0 (Or.inl (origin hf))) eq
        have e : s= !(pick f) := by cases s <;> cases p : pick f <;> simp_all
        rw [e]; exact flips f (by simpa [E] using And.intro hf ch)
  have build : ∀ k, k ≤ h → ∃ q : Net n, q.gates.length ≤ q.cost+k ∧ q.cost ≤ (loc k ∩ Ch).card ∧
      ∀ f∈loc k, ∀ s, need f s → q.has input (sg f s) := by
    intro k; induction k with
    | zero =>
      intro _; rw [loc0]
      have hc : first.cost=E.card := by simpa [q0,empty,Net.cost,NotBracket.notCount] using gfirst.2.2
      refine ⟨first,?_,hc.le,initial⟩; rw [hc]; simpa [q0,empty] using gfirst.2.1
    | succ k ih =>
      intro lim
      obtain ⟨q,lenq,costq,held⟩ := ih (by omega)
      let i : Fin h := ⟨k,by omega⟩
      have memb (f : Word m) (old : f∈A ∨ ∃ j < i,B j=f) : f∈loc k := here.mpr old
      have missing : B i∉loc k := by
        intro mem; rcases here.mp mem with u|⟨j,lt,eq⟩
        · exact (shape i).1 u
        · have e := inj eq; subst j; exact (lt_irrefl _ lt)
      have locstep : loc (k+1)=insert (B i) (loc k) := by
        ext f; rw [Finset.mem_insert,here,here]; constructor
        · rintro (raw|⟨j,hj,hf⟩)
          · exact Or.inr (Or.inl raw)
          · by_cases e : j.val=k
            · have eq : j=i := Fin.ext e; exact Or.inl (eq ▸ hf.symm)
            · exact Or.inr (Or.inr ⟨j,by omega,hf⟩)
        · rintro (rfl|raw|⟨j,hj,hf⟩)
          · exact Or.inr ⟨i,Nat.lt_succ_self k,rfl⟩
          · exact Or.inl raw
          · exact Or.inr ⟨j,by omega,hf⟩
      let b := P i.succ
      let a0 := xor b (ls i); let a1 := xor b (rs i)
      have lneed : need (l i) a0 := ⟨i.succ,ls i,Or.inr ⟨i,rfl,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩,rfl⟩
      have rneed : need (r i) a1 := ⟨i.succ,rs i,Or.inr ⟨i,rfl,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩,rfl⟩
      obtain ⟨z,gz,vz⟩ := binary width q _ _ (held _ (memb _ (shape i).2.1) _ lneed)
        (held _ (memb _ (shape i).2.2.1) _ rneed) (!b)
      let sb := xor b (prod i 0)
      have born : z.has input (sg (B i) sb) := by
        rw [dual_emit] at vz
        have eq : sg (B i) sb=sg (prod i) b := by
          rw [(shape i).2.2.2]; change sg (sg (prod i) (prod i 0)) sb=_; rw [sgs]
          congr 1; change xor (prod i 0) (xor b (prod i 0))=b; cases b <;> cases prod i 0 <;> rfl
        exact eq.symm ▸ vz
      have bneed : need (B i) sb := ⟨i.succ,prod i 0,Or.inr ⟨i,rfl,Or.inl ⟨rfl,rfl⟩⟩,rfl⟩
      have zc : z.cost=q.cost := by simpa using gz.2.2
      have zl := gz.2.1
      rw [locstep]; by_cases ch : B i∈Ch
      · obtain ⟨v,gv,neg⟩ := invert width z _ born
        have vc := gv.2.2; have vl := gv.2.1
        have same : insert (B i) (loc k) ∩ Ch=insert (B i) (loc k ∩ Ch) := by ext; simp [ch]
        rw [same,Finset.card_insert_of_notMem (fun x => missing (Finset.mem_inter.mp x).1)]
        refine ⟨v,by omega,by omega,?_⟩
        intro f hf s dem; rcases Finset.mem_insert.mp hf with rfl|old
        · by_cases eq : s=sb
          · exact eq ▸ gv.1 _ born
          · have e : s= !sb := by cases s <;> cases w : sb <;> simp_all
            rw [e]; exact sg_flip _ _ ▸ neg
        · exact gv.1 _ (gz.1 _ (held f old s dem))
      · have same : insert (B i) (loc k) ∩ Ch=loc k ∩ Ch := by ext; simp [ch]
        rw [same]; refine ⟨z,by omega,by omega,?_⟩
        intro f hf s dem; rcases Finset.mem_insert.mp hf with rfl|old
        · have ub : B i∈allC := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
          have nr : ¬(B i∈R ∧ sg (B i) true∈R) := by
            intro br; apply (shape i).1; refine Finset.mem_image.mpr ⟨B i,br.1,?_⟩
            rw [(shape i).2.2.2,nm_id]
          by_cases eq : s=sb
          · exact eq ▸ born
          · exact (ch (different ub nr dem bneed eq)).elim
        · exact gz.1 _ (held f old s dem)
  obtain ⟨q,len,cost,held⟩ := build h le_rfl
  have taps (j) : q.has input (T j) := by
    have inside : nm (T j)∈loc h := by
      rcases goal j with mem|⟨i,eq⟩
      · exact here.mpr (Or.inl mem)
      · exact here.mpr (Or.inr ⟨i,i.isLt,eq⟩)
    have nd : need (nm (T j)) (T j 0) := ask0 (Or.inr ⟨j,(recover _).symm⟩)
    simpa [recover] using held _ inside _ nd
  choose tap tl tv using taps
  let C : Circuit := ⟨q.gates,0⟩
  have neg : NotBracket.notCount C=q.cost := rfl
  have cz : C.size=q.gates.length := rfl
  have pos : C.size-NotBracket.notCount C ≤ h := by omega
  have nc : q.cost ≤ Ch.card := cost.trans (Finset.card_le_card Finset.inter_subset_right)
  refine ⟨C,tap,q.fan,q.readsBack,by simp [C],tl,fun j t => tv j t,pos.trans budget,?_⟩
  exact (Nat.add_le_add (Nat.mul_le_mul_left cp pos) (Nat.mul_le_mul_left cn (neg ▸ nc))).trans limit


end PEqualNP.Outside.L_meta_53180

theorem PEqualNP.Outside.L_meta_53180 : (∀ (m d a p cp cn W : Nat), cn ≤ cp →
  ∀ (X : Fin (m+1) → Fin d → Bool) (T : Fin a → Fin (m+1) → Bool),
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := Fin (m+1) → Bool
  let sign := fun (f : F) (s : Bool) (t : Fin (m+1)) => xor (f t) s
  let norm := fun (f : F) => sign f (f 0)
  let inputs := fun t => List.ofFn (X t) ++ [false,true]
  let raw := (Finset.range (d+2)).image (fun i t => (inputs t).getD i false)
  let base := raw.image norm
  (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
    C.output < d+2+C.size ∧ (∀ j, tap j < d+2+C.size) ∧
    (∀ j t, (C.wires (inputs t)).getD (tap j) false = T j t) ∧
    let neg := PEqualNP.NotBracket.notCount C
    C.size-neg ≤ p ∧ cp*(C.size-neg)+cn*neg ≤ W) ↔
  ∃ (h : Nat) (birth left right : Fin h → F) (ls rs : Fin h → Bool),
    let older := fun (i : Fin h) (f : F) => f ∈ base ∨ ∃ j < i, birth j = f
    let prod := fun i t => sign (left i) (ls i) t && sign (right i) (rs i) t
    let asks := fun (f : F) (v : Fin (h+1)) (s : Bool) =>
      (v = 0 ∧ (sign f s ∈ raw ∨ ∃ j, T j = sign f s)) ∨
      ∃ i : Fin h, v = i.succ ∧ ((birth i = f ∧ prod i 0 = s) ∨
        (left i = f ∧ ls i = s) ∨ (right i = f ∧ rs i = s))
    h ≤ p ∧ Function.Injective birth ∧
    (∀ i, birth i ∉ base ∧ older i (left i) ∧ older i (right i) ∧ birth i = norm (prod i)) ∧
    (∀ j, norm (T j) ∈ base ∨ ∃ i, birth i = norm (T j)) ∧
    ∃ phase : Fin (h+1) → Bool, phase 0 = false ∧
      let classes := base ∪ Finset.univ.image birth
      let charged := classes.filter (fun f => ¬ (f ∈ raw ∧ sign f true ∈ raw) ∧
        ∃ v w s t, asks f v s ∧ asks f w t ∧ xor (phase v) s ≠ xor (phase w) t)
      cp*h + cn*charged.card ≤ W) := by
  intro m d a p cp cn W h X T
  have result := Iff.intro (PEqualNP.Outside.L_meta_53180.forward (p:=p) (W:=W) X T h)
    (PEqualNP.Outside.L_meta_53180.backward (p:=p) (cp:=cp) (cn:=cn) (W:=W) X T)
  unfold PEqualNP.Outside.L_meta_53180.Physical PEqualNP.Outside.L_meta_53180.Program PEqualNP.Outside.L_meta_53180.costs
    PEqualNP.Outside.L_meta_53180.Ask PEqualNP.Outside.L_meta_53180.prodW PEqualNP.Outside.L_meta_53180.nm
    PEqualNP.Outside.L_meta_53180.sg PEqualNP.Outside.L_meta_53180.wire PEqualNP.Outside.L_meta_53180.given PEqualNP.Outside.L_meta_53180.ins at result
  dsimp only at result ⊢
  convert! result using 100 <;> first | exact Subsingleton.elim _ _ | funext; apply Subsingleton.elim
