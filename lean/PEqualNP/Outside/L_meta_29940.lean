import Mathlib.Data.Tree.Basic
import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29940

namespace S

open PEqualNP.CircuitLowerBounds

inductive NatTree where
  | atom (i : Nat)
  | join (isAnd : Bool) (l r : NatTree)

def NatTree.eval : NatTree → (Nat → Bool) → Bool
  | .atom i, w => w i
  | .join b l r, w => if b then l.eval w && r.eval w else l.eval w || r.eval w

def NatTree.vars : NatTree → Finset Nat
  | .atom i => {i}
  | .join _ l r => l.vars ∪ r.vars

def NatTree.once : NatTree → Prop
  | .atom _ => True
  | .join _ l r => l.once ∧ r.once ∧ Disjoint l.vars r.vars

def NatTree.replace (t : NatTree) (n : Nat) (q : NatTree) : NatTree := match t with
  | .atom i => if i=n then q else .atom i
  | .join b l r => .join b (l.replace n q) (r.replace n q)

theorem NatTree.replace_eval (n : Nat) (q t : NatTree) (w : Nat → Bool) :
    (t.replace n q).eval w = t.eval (fun i => if i=n then q.eval w else w i) := by
  induction t with
  | atom i => by_cases e : i=n <;> simp [NatTree.replace,NatTree.eval,e]
  | join b l r ih jh => simp [NatTree.replace,NatTree.eval,ih,jh]

theorem NatTree.replace_vars (n : Nat) (q t : NatTree) (j : Nat) :
    j ∈ (t.replace n q).vars ↔ (j ≠ n ∧ j ∈ t.vars) ∨ (n ∈ t.vars ∧ j ∈ q.vars) := by
  induction t with
  | atom i => by_cases e : i=n <;> by_cases z : j=n <;> simp_all [NatTree.replace,NatTree.vars,eq_comm]
  | join b l r ih jh => simp only [NatTree.replace,NatTree.vars,Finset.mem_union,ih,jh]; tauto

theorem NatTree.replace_once (n : Nat) (q t : NatTree) (ht : t.once) (hq : q.once)
    (fresh : ∀ j ∈ t.vars, j ≠ n → j ∉ q.vars) : (t.replace n q).once := by
  induction t with
  | atom i => by_cases e : i=n <;> simp [NatTree.replace,NatTree.once,e,hq]
  | join b l r ih jh =>
    obtain ⟨hl,hr,dis⟩ := ht
    refine ⟨ih hl (fun j hj => fresh j (by simp [NatTree.vars,hj])),jh hr (fun j hj => fresh j (by simp [NatTree.vars,hj])),?_⟩
    rw [Finset.disjoint_left] at dis ⊢
    intro j jl jr
    rcases (replace_vars _ _ _ _).mp jl with ⟨jn,hj⟩|⟨hn,hj⟩ <;>
      rcases (replace_vars _ _ _ _).mp jr with ⟨jm,hk⟩|⟨hm,hk⟩
    · exact dis hj hk
    · exact fresh j (by simp [NatTree.vars,hj]) jn hk
    · exact fresh j (by simp [NatTree.vars,hk]) jm hj
    · exact dis hn hm

theorem NatTree.eval_congr (t : NatTree) {w v : Nat → Bool} (h : ∀ j ∈ t.vars, w j=v j) : t.eval w=t.eval v := by
  induction t with
  | atom j => exact h j (by simp [vars])
  | join b l r ih jh =>
    simp only [eval,ih (fun j hj => h j (by simp [vars,hj])),jh (fun j hj => h j (by simp [vars,hj]))]

open PEqualNP.CircuitLowerBounds

def gateInputs (n : Nat) (g : Gate) := g.inputs.toFinset.filter (fun j => j<n)
def required (n : Nat) (g : Gate) (s : Finset Nat) :=
  if n ∈ s then s.erase n ∪ gateInputs n g else s

def back : Nat → List Gate → Finset Nat → Finset Nat
  | _,[],s => s
  | n,g::gs,s => required n g (back (n+1) gs s)

def good (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

theorem stepCard (n : Nat) (g : Gate) (s : Finset Nat) (h : good g) :
    (required n g s).card ≤ s.card+1 := by
  have hg : (gateInputs n g).card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans h.2)
  by_cases e : n ∈ s
  · simp only [required,ite_eq_left e]
    have hc := Finset.card_union_le (s.erase n) (gateInputs n g)
    have hd := Finset.card_erase_add_one e
    omega
  · simp [required,e]

theorem backCard (n : Nat) (gs : List Gate) (s : Finset Nat) (h : ∀g∈gs,good g) :
    (back n gs s).card ≤ s.card+gs.length := by
  induction gs generalizing n with
  | nil => simp [back]
  | cons g gs ih =>
    have a := ih (n+1) (fun a ha => h a (by simp [ha]))
    have b := stepCard n g (back (n+1) gs s) (h _ (by simp))
    simp [back]; omega

theorem tightStep (n : Nat) (g : Gate) (s : Finset Nat) (h : good g)
    (eq : (required n g s).card = s.card+1) :
    n ∈ s ∧ ∃ a b, g.inputs=[a,b] ∧ a<n ∧ b<n ∧ a ≠ b ∧
      a ∉ s.erase n ∧ b ∉ s.erase n := by
  have mem : n ∈ s := by
    by_contra e
    simp [required,e] at eq
  simp only [required,ite_eq_left mem] at eq
  have hg : (gateInputs n g).card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans h.2)
  have hc := Finset.card_union_le (s.erase n) (gateInputs n g)
  have hd := Finset.card_erase_add_one mem
  have hm := Finset.card_union_add_card_inter (s.erase n) (gateInputs n g)
  have two : (gateInputs n g).card=2 := by omega
  have di : Disjoint (s.erase n) (gateInputs n g) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    exact Finset.card_eq_zero.mp (by omega)
  obtain ⟨op,ins⟩ := g
  have le : ins.length ≤ 2 := h.2
  rcases ins with _|⟨a,ins⟩
  · simp [gateInputs] at two
  rcases ins with _|⟨b,ins⟩
  · by_cases e : a<n <;> simp [gateInputs,Finset.filter_singleton,e] at two
  have nil : ins=[] := List.length_eq_zero_iff.mp (by simpa using le)
  subst ins
  have facts : a<n ∧ b<n ∧ a≠b := by
    by_cases ha : a<n <;> by_cases hb : b<n <;> by_cases e : a=b <;> first
      | exact ⟨ha,hb,e⟩
      | exfalso; simp [gateInputs,Finset.filter_insert,Finset.filter_singleton,ha,hb,e] at two
  obtain ⟨ha,hb,ne⟩ := facts
  refine ⟨mem,a,b,rfl,ha,hb,ne,?_,?_⟩
  · intro hana
    exact Finset.disjoint_left.mp di hana (by simp [gateInputs,ha])
  · intro hbna
    exact Finset.disjoint_left.mp di hbna (by simp [gateInputs,hb])

def valueGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def runG (gs : List Gate) (w : List Bool) := gs.foldl (fun v g => v ++ [valueGate g v]) w

theorem getPush (w : List Bool) (b : Bool) (i : Nat) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases e : i < w.length
  · exact List.getD_append _ _ _ _ e
  · rw [List.getD_eq_default _ _ (by simp;omega), List.getD_eq_default _ _ (by omega)]

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gmono (g : Gate) (hg : good g) (w v : List Bool)
    (le : ∀ i∈g.inputs, w.getD i false = true → v.getD i false = true) :
    valueGate g w = true → valueGate g v = true := by
  rcases hg.1 with e|e
  · simp only [valueGate,e,GateOp.eval,List.all_eq_true,List.mem_map]
    intro a b h
    obtain ⟨i,hi,rfl⟩ := h
    apply le i hi
    exact a _ ⟨i,hi,rfl⟩
  · simp only [valueGate,e,GateOp.eval,List.any_eq_true,List.mem_map]
    rintro ⟨b,⟨i,hi,rfl⟩,hv⟩
    exact ⟨_,⟨i,hi,rfl⟩,le i hi hv⟩

theorem leStep (n : Nat) (g : Gate) (hg : good g) (s : Finset Nat) (w v : List Bool) (lw : w.length=n) (lv : v.length=n)
    (le : ∀ j∈required n g s, w.getD j false=true → v.getD j false=true) :
    ∀ j∈s, (w ++ [valueGate g w]).getD j false=true → (v ++ [valueGate g v]).getD j false=true := by
  intro j hj
  by_cases e : j=n
  · subst j
    have gv := gmono g hg w v (by
      intro x hx
      by_cases hx' : x<n
      · exact le x (by simp [required,hj,gateInputs,hx,hx'])
      · intro pos
        rw [List.getD_eq_default _ _ (by omega : w.length ≤ x)] at pos
        contradiction)
    simpa [List.getD_append_right,lw,lv] using gv
  · rw [getPush _ _ _ (by omega),getPush _ _ _ (by omega)]
    apply le
    by_cases z : n∈s <;> simp [required,z,e,hj]

theorem leBack (n : Nat) (gs : List Gate) (s : Finset Nat) (hg : ∀ g∈gs,good g)
    (w v : List Bool) (lw : w.length=n) (lv : v.length=n)
    (le : ∀ j∈back n gs s, w.getD j false=true → v.getD j false=true) :
    ∀ j∈s, (runG gs w).getD j false=true → (runG gs v).getD j false=true := by
  induction gs generalizing n w v with
  | nil => exact le
  | cons g gs ih =>
    exact ih (n+1) (fun a ha=>hg _ (by simp [ha])) _ _ (by simp [lw]) (by simp [lv])
      (leStep n g (hg _ (by simp)) _ w v lw lv le)

theorem oneRead {k : Nat} (a : Fin k) (i : Nat) :
    (List.ofFn (fun j : Fin k => decide (j=a))).getD i false = true ↔ i=a.val := by
  by_cases hi : i<k
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [Fin.ext_iff]
  · rw [List.getD_eq_default _ _ (by simp;omega)]
    simp;omega

theorem pairRead {k : Nat} (a b : Fin k) (i : Nat) :
    (oneEach a b).getD i false = true ↔ i=a.val ∨ i=k+b.val := by
  unfold oneEach
  by_cases hi : i<k
  · rw [List.getD_append _ _ _ _ (by simpa using hi),oneRead]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp;omega),List.length_ofFn,oneRead]
    omega

theorem essential {k : Nat} (hk : 2≤k) (c : Circuit)
    (hg : ∀ g∈c.gates,good g) (rep : Represents (fun i j : Fin k => decide (i=j)) c) :
    Finset.range (2*k) ⊆ back (2*k) c.gates {c.output} := by
  intro a ha
  by_contra missing
  have lt : a<2*k := Finset.mem_range.mp ha
  have impossible (i j l : Fin k) (ne : j≠l)
      (le : ∀ v∈back (2*k) c.gates {c.output}, (oneEach i i).getD v false=true → (oneEach j l).getD v false=true) : False := by
    have hit := leBack (2*k) c.gates {c.output} hg (oneEach i i) (oneEach j l)
      (by simp [oneEach];omega) (by simp [oneEach];omega) le c.output (by simp)
    change c.eval (oneEach i i)=true → c.eval (oneEach j l)=true at hit
    rw [rep i i, rep j l] at hit
    simp [ne] at hit
  have other (i : Fin k) : ∃ j : Fin k, j≠i := by
    by_cases z : i.val=0
    · exact ⟨⟨1,by omega⟩,fun e => by have hh := congrArg Fin.val e; change 1 = i.val at hh;omega⟩
    · exact ⟨⟨0,by omega⟩,fun e => by have hh := congrArg Fin.val e; change 0 = i.val at hh;omega⟩
  by_cases left : a<k
  · let i : Fin k := ⟨a,left⟩
    obtain ⟨j,hj⟩ := other i
    apply impossible i j i hj
    intro u hu yes
    rcases (pairRead _ _ _).mp yes with h|h
    · change u = a at h
      exact (missing (h ▸ hu)).elim
    · exact (pairRead _ _ _).mpr (Or.inr h)
  · let i : Fin k := ⟨a-k,by omega⟩
    obtain ⟨j,hj⟩ := other i
    apply impossible i i j (Ne.symm hj)
    intro u hu yes
    rcases (pairRead _ _ _).mp yes with h|h
    · exact (pairRead _ _ _).mpr (Or.inl h)
    · have e : u=a := by change u=k+(a-k) at h;omega
      exact (missing (e ▸ hu)).elim

open PEqualNP.CircuitLowerBounds

theorem traceInputs (n : Nat) (gs : List Gate) (t : NatTree) (ht : t.once) (hg : ∀ g∈gs,good g)
    (tight : (back n gs t.vars).card = t.vars.card+gs.length) :
    ∃ p : NatTree, p.once ∧ p.vars = back n gs t.vars ∧
      ∀ w : List Bool, w.length=n → p.eval (fun i => w.getD i false) = t.eval (fun i => (runG gs w).getD i false) := by
  induction gs generalizing n with
  | nil => exact ⟨t,ht,rfl,fun _ _ => rfl⟩
  | cons g gs ih =>
    let s := back (n+1) gs t.vars
    have hrest (v : Gate) (hv : v∈gs) : good v := hg v (by simp [hv])
    have hG : good g := hg g (by simp)
    have eb : s.card ≤ t.vars.card+gs.length := backCard (n+1) gs _ hrest
    have es := stepCard n g s hG
    change (required n g s).card = t.vars.card+(g::gs).length at tight
    simp only [List.length_cons] at tight
    have tb : s.card = t.vars.card+gs.length := by omega
    have ts : (required n g s).card=s.card+1 := by omega
    obtain ⟨u,hu,us,ev⟩ := ih (n+1) hrest tb
    change u.vars = s at us
    obtain ⟨hn,a,b,inputs,ha,hb,ab,na,nb⟩ := tightStep n g s hG ts
    let rhs := NatTree.join (match g.op with | .and => true | _ => false) (.atom a) (.atom b)
    have hro : rhs.once := by simp [rhs,NatTree.once,NatTree.vars,ab]
    have names : rhs.vars={a,b} := by simp [rhs,NatTree.vars]
    have un : n∈u.vars := us ▸ hn
    have fr (j : Nat) (hj : j∈u.vars) (jn : j ≠ n) : j ∉ rhs.vars := by
      have mem : j ∈ s.erase n := Finset.mem_erase.mpr ⟨jn,(by rwa [← us])⟩
      rw [names];simp only [Finset.mem_insert,Finset.mem_singleton]
      rintro (rfl|rfl) <;> contradiction
    refine ⟨u.replace n rhs, NatTree.replace_once n rhs u hu hro fr,?_,?_⟩
    · change _ = required n g s
      ext j
      simp only [NatTree.replace_vars,us,required,Finset.mem_union,Finset.mem_erase,names,
        Finset.mem_insert,Finset.mem_singleton,hn,true_and,gateInputs,inputs,List.toFinset_cons,
        List.toFinset_nil,Finset.mem_filter]
      grind
    · intro w lw
      have hv : rhs.eval (fun i => w.getD i false) = valueGate g w := by
        rcases hG.1 with op|op <;> simp [rhs,NatTree.eval,valueGate,op,inputs,GateOp.eval]
      have reads (i : Nat) : (if i=n then rhs.eval (fun j => w.getD j false) else w.getD i false) =
          (w++[valueGate g w]).getD i false := by
        by_cases e : i=n
        · subst i; rw [List.getD_append_right _ _ _ _ (by omega),lw]; simpa using hv
        · rw [ite_eq_right e,getPush _ _ _ (by omega)]
      rw [NatTree.replace_eval]
      exact (u.eval_congr (fun j _ => reads j)).trans (ev _ (by simp [lw]))

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem identityTree {k : Nat} (hk : 2≤k) (c : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 c)
    (budget : c.size+1≤2*k) (rep : Represents (fun i j : Fin k => decide (i=j)) c) :
    ∃ p : NatTree, p.vars = Finset.range (2*k) ∧ p.once ∧
      ∀ w : List Bool, w.length=2*k → p.eval (fun i => w.getD i false) = c.eval w := by
  have hg (g : Gate) (mem : g∈c.gates) : good g := hm g mem
  let s := back (2*k) c.gates {c.output}
  have inclus : Finset.range (2*k) ⊆ s := essential hk c hg rep
  have low : 2*k ≤ s.card := by simpa using Finset.card_le_card inclus
  have high : s.card ≤ 1 + c.gates.length := by
    have hh := backCard (2*k) c.gates {c.output} hg
    simpa [s] using hh
  change c.gates.length+1 ≤ 2*k at budget
  have eq : s.card = 1+c.gates.length := by omega
  have varsEq : s = Finset.range (2*k) := (Finset.eq_of_subset_of_card_le inclus (by simp;omega)).symm
  let t := NatTree.atom c.output
  have tt : (back (2*k) c.gates t.vars).card=t.vars.card+c.gates.length := by
    simpa [s,t,NatTree.vars] using eq
  obtain ⟨p,hp,en,ev⟩ := traceInputs (2*k) c.gates t (by trivial) hg tt
  exact ⟨p,en.trans varsEq,hp,ev⟩

end S

namespace S
namespace IdentityClass

def lights (s : Finset Nat) (n : Nat) : Bool := decide (n ∈ s)
def cell {k : Nat} (i j : Fin k) : Nat → Bool := lights {i.val, k+j.val}

theorem zero (t : NatTree) : t.eval (fun _ => false) = false := by
  induction t with
  | atom => rfl
  | join b l r ih jh => cases b <;> simp [NatTree.eval, ih, jh]

theorem true_var {t : NatTree} {w : Nat → Bool} (good : t.eval w = true) :
    ∃ n ∈ t.vars, w n = true := by
  by_contra! bad
  have h := t.eval_congr (v := fun _ => false) (by intro n hn; simpa using bad n hn)
  simp [zero,good] at h

theorem mono {t : NatTree} {w v : Nat → Bool} (le : ∀ n ∈ t.vars, w n = true → v n = true) :
    t.eval w = true → t.eval v = true := by
  induction t with
  | atom i => exact le i (by simp [NatTree.vars])
  | join b l r ih jh =>
    have hl := ih (fun n hn => le n (by simp [NatTree.vars,hn]))
    have hr := jh (fun n hn => le n (by simp [NatTree.vars,hn]))
    cases b <;> simp only [NatTree.eval,Bool.false_eq_true,if_false,if_true,Bool.and_eq_true,Bool.or_eq_true]
    all_goals tauto

theorem need_pair {t : NatTree} (single : ∀ n, t.eval (lights {n}) = false)
    {a b : Nat} (h : t.eval (lights {a,b}) = true) : a ∈ t.vars ∧ b ∈ t.vars := by
  constructor
  · by_contra ha
    have e := t.eval_congr (w := lights {a,b}) (v := lights {b}) (by
      intro j hj; have hn : j ≠ a := by rintro rfl; contradiction
      simp [lights,hn])
    simp [h,single] at e
  · by_contra hb
    have e := t.eval_congr (w := lights {a,b}) (v := lights {a}) (by
      intro j hj; have hn : j ≠ b := by rintro rfl; contradiction
      simp [lights,hn])
    simp [h,single] at e

structure Valid {k : Nat} (t : NatTree) : Prop where
  once : t.once
  bounded : ∀ n ∈ t.vars, n < 2*k
  single : ∀ n, t.eval (lights {n}) = false
  diag : ∀ i : Fin k, i.val ∈ t.vars ∨ k+i.val ∈ t.vars → t.eval (cell i i) = true
  offdiag : ∀ i j : Fin k, i ≠ j → t.eval (cell i j) = false

theorem left_valid {k} {l r : NatTree} (h : @Valid k (.join false l r)) : @Valid k l := by
  have dis := Finset.disjoint_left.mp h.once.2.2
  have sides (w : Nat → Bool) : (NatTree.join false l r).eval w = (l.eval w || r.eval w) := rfl
  have single (n) := h.single n
  simp only [sides,Bool.or_eq_false_iff] at single
  refine ⟨h.once.1,fun n hn => h.bounded n (Finset.mem_union_left _ hn),fun n => (single n).1,?_,?_⟩
  · intro i hv
    have hg := h.diag i (hv.imp (Finset.mem_union_left _) (Finset.mem_union_left _))
    rw [sides,Bool.or_eq_true] at hg
    rcases hg with hg|hg
    · exact hg
    obtain ⟨a,b⟩ := need_pair (fun n => (single n).2) hg
    rcases hv with hv|hv
    · exact (dis hv a).elim
    · exact (dis hv b).elim
  · intro i j hne
    exact (Bool.or_eq_false_iff.mp (h.offdiag i j hne)).1

theorem right_valid {k} {l r : NatTree} (h : @Valid k (.join false l r)) : @Valid k r := by
  have hs : @Valid k (.join false r l) := by
    have V : (NatTree.join false r l).vars = (NatTree.join false l r).vars := Finset.union_comm _ _
    have E : ∀ w, (NatTree.join false r l).eval w = (NatTree.join false l r).eval w := by
      intro w; exact Bool.or_comm _ _
    exact ⟨⟨h.once.2.1,h.once.1,h.once.2.2.symm⟩,by simpa only [V] using h.bounded,
      by simpa only [E] using h.single,by simpa only [E,V] using h.diag,by simpa only [E] using h.offdiag⟩
  exact left_valid hs

theorem active_iff {k} {t : NatTree} (h : @Valid k t) (i : Fin k) :
    i.val ∈ t.vars ↔ k+i.val ∈ t.vars :=
  ⟨fun hi => (need_pair h.single (h.diag i (.inl hi))).2,
   fun hi => (need_pair h.single (h.diag i (.inr hi))).1⟩

def Hit {k : Nat} (p : Fin k → Fin k) (i : Fin k) (w : Nat → Bool) : Prop :=
  (w i.val = true ∧ w (k+i.val) = true) ∨ (p i ≠ i ∧
    ((w i.val = true ∧ w (p i).val = true) ∨ (w (k+i.val) = true ∧ w (k+(p i).val) = true)))

structure Realizes {k : Nat} (t : NatTree) (p : Fin k → Fin k) : Prop where
  invol : Function.Involutive p
  outside : ∀ i : Fin k, i.val ∉ t.vars → p i = i
  form : ∀ w, t.eval w = true ↔ ∃ i : Fin k, i.val ∈ t.vars ∧ Hit p i w

theorem inside {k : Nat} {t : NatTree} {p : Fin k → Fin k} (h : Realizes t p)
    {i : Fin k} (hi : i.val ∈ t.vars) : (p i).val ∈ t.vars := by
  by_contra hp
  have e := h.outside _ hp
  rw [h.invol] at e
  exact hp (e ▸ hi)

theorem glue {k : Nat} {l r : NatTree} {p q : Fin k → Fin k}
    (d : Disjoint l.vars r.vars) (hp : Realizes l p) (hq : Realizes r q) :
    ∃ f : Fin k → Fin k, Realizes (.join false l r) f := by
  classical
  let f (i : Fin k) := if i.val ∈ l.vars then p i else q i
  have left (i : Fin k) (hi : i.val ∈ l.vars) : f i = p i := if_pos hi
  have right (i : Fin k) (hi : i.val ∈ r.vars) : f i = q i :=
    if_neg (fun h => Finset.disjoint_left.mp d h hi)
  refine ⟨f,⟨?_,?_,?_⟩⟩
  · intro i; by_cases hl : i.val ∈ l.vars
    · rw [left _ hl, left _ (inside hp hl),hp.invol]
    · by_cases hr : i.val ∈ r.vars
      · rw [right _ hr, right _ (inside hq hr),hq.invol]
      · change f (if i.val ∈ l.vars then p i else q i) = i
        simp only [if_neg hl,hq.outside i hr,f]
  · intro i hi; change i.val ∉ l.vars ∪ r.vars at hi
    simp only [Finset.mem_union,not_or] at hi
    simp [f, hi.1, hq.outside i hi.2]
  · intro w
    change (l.eval w || r.eval w) = true ↔ ∃ i : Fin k, i.val ∈ l.vars ∪ r.vars ∧ Hit f i w
    rw [Bool.or_eq_true,hp.form,hq.form]
    constructor
    · rintro (⟨i,hi,e⟩|⟨i,hi,e⟩)
      · exact ⟨i,Finset.mem_union_left _ hi,by simpa only [Hit,left i hi] using e⟩
      · exact ⟨i,Finset.mem_union_right _ hi,by simpa only [Hit,right i hi] using e⟩
    · rintro ⟨i,hi,e⟩; rcases Finset.mem_union.mp hi with hi|hi
      · exact Or.inl ⟨i,hi,by simpa only [Hit,left i hi] using e⟩
      · exact Or.inr ⟨i,hi,by simpa only [Hit,right i hi] using e⟩

end IdentityClass
end S
namespace S.IdentityClass

def Orient {k} (l r : NatTree) (i : Fin k) : Prop :=
  i.val ∈ l.vars ∧ k+i.val ∈ r.vars ∧ l.eval (lights {i.val}) = true ∧ r.eval (lights {k+i.val}) = true

theorem swap_and {k} {l r : NatTree} (h : @Valid k (.join true l r)) : @Valid k (.join true r l) := by
  have V : (NatTree.join true r l).vars = (NatTree.join true l r).vars := Finset.union_comm _ _
  have E : ∀ w, (NatTree.join true r l).eval w = (NatTree.join true l r).eval w := by
    intro w; exact Bool.and_comm _ _
  exact ⟨⟨h.once.2.1,h.once.1,h.once.2.2.symm⟩,by simpa only [V] using h.bounded,
    by simpa only [E] using h.single,by simpa only [E,V] using h.diag,by simpa only [E] using h.offdiag⟩

theorem swap_form {k} {l r : NatTree} {p : Fin k → Fin k} (h : Realizes (.join true r l) p) :
    Realizes (.join true l r) p := by
  have V : (NatTree.join true l r).vars = (NatTree.join true r l).vars := Finset.union_comm _ _
  have E : ∀ w, (NatTree.join true l r).eval w = (NatTree.join true r l).eval w := by
    intro w; exact Bool.and_comm _ _
  exact ⟨h.invol,by simpa only [V] using h.outside,by simpa only [E,V] using h.form⟩

theorem either_var {t : NatTree} {a b : Nat} (ht : t.eval (lights {a,b}) = true) :
    a ∈ t.vars ∨ b ∈ t.vars := by
  obtain ⟨n,hn,lit⟩ := true_var ht
  simp only [lights,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at lit
  rcases lit with rfl|rfl <;> tauto

theorem to_single {t : NatTree} {a b : Nat} (h : t.eval (lights {a,b}) = true) (hb : b ∉ t.vars) :
    t.eval (lights {a}) = true := by
  rw [← h]
  apply t.eval_congr
  intro n hn
  have ne : n ≠ b := by rintro rfl; contradiction
  simp [lights,ne]

theorem split_and {k} {l r : NatTree} (h : @Valid k (.join true l r)) (i : Fin k) :
    i.val ∈ (NatTree.join true l r).vars ↔ Orient l r i ∨ Orient r l i := by
  constructor
  · intro hi
    have d := Finset.disjoint_left.mp h.once.2.2
    have both : l.eval (cell i i) = true ∧ r.eval (cell i i) = true := by
      simpa [NatTree.eval] using h.diag i (Or.inl hi)
    have row (u : NatTree) (g : u.eval (cell i i) = true) (hn : k+i.val ∉ u.vars) :=
      to_single g hn
    have col (u : NatTree) (g : u.eval (cell i i) = true) (hn : i.val ∉ u.vars) :=
      to_single (a := k+i.val) (b:=i.val) (by simpa [cell,Finset.pair_comm] using g : u.eval (lights {k+i.val,i.val}) = true) hn
    rcases either_var both.1 with a|a <;> rcases either_var both.2 with b|b
    · exact (d a b).elim
    · exact Or.inl ⟨a,b,row l both.1 (fun ha => d ha b),col r both.2 (d a)⟩
    · exact Or.inr ⟨b,a,row r both.2 (d a),col l both.1 (fun ha => d ha b)⟩
    · exact (d a b).elim
  · rintro (z|z)
    · exact Finset.mem_union_left _ z.1
    · exact Finset.mem_union_right _ z.1

theorem of_lit {t : NatTree} {n : Nat} {w : Nat → Bool}
    (hs : t.eval (lights {n}) = true) (hw : w n = true) : t.eval w = true := by
  apply mono (w := lights {n}) _ hs
  intro j _ hj
  have hn : j=n := by simpa [lights] using hj
  simpa only [hn] using hw

theorem orientation_unique {k} {l r : NatTree} (h : @Valid k (.join true l r))
    {i j : Fin k} (hi : Orient l r i) (hj : Orient l r j) : i = j := by
  by_contra bad
  have hl : l.eval (cell i j) = true := of_lit hi.2.2.1 (by simp [cell,lights])
  have hr : r.eval (cell i j) = true := of_lit hj.2.2.2 (by simp [cell,lights])
  have e := h.offdiag i j bad
  simp [NatTree.eval,hl,hr] at e

theorem light_factor {k} {l r : NatTree} (h : @Valid k (.join true l r)) (w : Nat → Bool) :
    l.eval w = true ↔ (∃ i : Fin k, Orient l r i ∧ w i.val = true) ∨
      (∃ i : Fin k, Orient r l i ∧ w (k+i.val) = true) := by
  have d := Finset.disjoint_left.mp h.once.2.2
  constructor
  · intro hw; obtain ⟨n,hn,hw⟩ := true_var hw
    have hn' : n ∈ (NatTree.join true l r).vars := Finset.mem_union_left _ hn
    by_cases lo : n < k
    · let i : Fin k := ⟨n,lo⟩
      rcases (split_and h i).mp hn' with z | z
      · exact Or.inl ⟨i,z,hw⟩
      · exact (d hn z.1).elim
    · have bound := h.bounded n hn'
      let i : Fin k := ⟨n-k,by omega⟩
      have e : k+i.val = n := by dsimp [i]; omega
      have ha := (active_iff h i).mpr (e ▸ hn')
      rcases (split_and h i).mp ha with z|z
      · exact (d hn (e ▸ z.2.1)).elim
      · exact Or.inr ⟨i,z,e ▸ hw⟩
  · rintro (⟨i,z,hw⟩|⟨i,z,hw⟩)
    · exact of_lit z.2.2.1 hw
    · exact of_lit z.2.2.2 hw

theorem single_orientation {k} {l r : NatTree} (h : @Valid k (.join true l r))
    (empty : ¬ ∃ i : Fin k, Orient r l i) : Realizes (.join true l r) (@id (Fin k)) := by
  refine ⟨fun _ => rfl,fun _ _ => rfl,?_⟩
  intro w
  change (l.eval w && r.eval w) = true ↔ _
  rw [Bool.and_eq_true,light_factor h,light_factor (swap_and h)]
  constructor
  · rintro ⟨(⟨i,zi,hi⟩|⟨i,zi,_⟩),(⟨j,zj,_⟩|⟨j,zj,hj⟩)⟩
    · exact (empty ⟨j,zj⟩).elim
    · obtain rfl := orientation_unique h zi zj
      exact ⟨i,(split_and h i).mpr (.inl zi),Or.inl ⟨hi,hj⟩⟩
    · exact (empty ⟨i,zi⟩).elim
    · exact (empty ⟨i,zi⟩).elim
  · rintro ⟨i,hi,e⟩
    have hh := e.resolve_right (fun q => q.1 rfl)
    rcases (split_and h i).mp hi with z|z
    · exact ⟨Or.inl ⟨i,z,hh.1⟩,Or.inr ⟨i,z,hh.2⟩⟩
    · exact (empty ⟨i,z⟩).elim

theorem quantified {α : Type} {P Q : α → Prop} {a : α} (pa : P a) (uniq : ∀ i, P i → i=a) :
    (∃ i, P i ∧ Q i) ↔ Q a := by
  constructor
  · rintro ⟨i,pi,qi⟩; simpa only [uniq i pi] using qi
  · exact fun q => ⟨a,pa,q⟩

theorem two_orientations {k} {l r : NatTree} (h : @Valid k (.join true l r))
    {a b : Fin k} (za : Orient l r a) (zb : Orient r l b) :
    ∃ p : Fin k → Fin k, Realizes (.join true l r) p := by
  have ab : a ≠ b := by rintro rfl; exact Finset.disjoint_left.mp h.once.2.2 za.1 zb.1
  let p (i : Fin k) := if i=a then b else if i=b then a else i
  have pa : p a = b := by simp [p]
  have pb : p b = a := by simp [p,ab.symm]
  have A : ∀ i, Orient l r i → i=a := fun _ z => orientation_unique h z za
  have B : ∀ i, Orient r l i → i=b := fun _ z => orientation_unique (swap_and h) z zb
  have support (i : Fin k) : i.val ∈ (NatTree.join true l r).vars ↔ i=a ∨ i=b := by
    rw [split_and h]; constructor
    · exact Or.imp (A i) (B i)
    · rintro (rfl|rfl); exact .inl za; exact .inr zb
  refine ⟨p,⟨?_,?_,?_⟩⟩
  · intro i; by_cases ea : i=a
    · simpa only [ea,pa,pb]
    · by_cases eb : i=b
      · simpa only [eb,pb,pa]
      · simp [p,ea,eb]
  · intro i hi; rw [support] at hi
    simp only [not_or] at hi; simp [p,hi.1,hi.2]
  · intro w
    change (l.eval w && r.eval w) = true ↔ _
    rw [Bool.and_eq_true,light_factor h,light_factor (swap_and h)]
    simp only [quantified za A,quantified zb B,support,or_and_right,exists_or,exists_eq_left,Hit,pa,pb,ab,ab.symm,true_and]
    tauto

theorem exists_realizes {k} {t : NatTree} (h : @Valid k t) :
    ∃ p : Fin k → Fin k, Realizes t p := by
  induction t with
  | atom n =>
    have bad := h.single n; simp [NatTree.eval,lights] at bad
  | join b l r ih jh =>
    cases b with
    | false =>
      obtain ⟨p,hp⟩ := ih (left_valid h)
      obtain ⟨q,hq⟩ := jh (right_valid h)
      exact glue h.once.2.2 hp hq
    | true =>
      by_cases ha : ∃ i : Fin k, Orient l r i
      · by_cases hb : ∃ i : Fin k, Orient r l i
        · obtain ⟨a,ha⟩ := ha; obtain ⟨b,hb⟩ := hb
          exact two_orientations h ha hb
        · exact ⟨_,single_orientation h hb⟩
      · exact ⟨_,swap_form (single_orientation (swap_and h) ha)⟩

end S.IdentityClass
namespace S.IdentityClass

theorem other_index {k} (hk : 2 ≤ k) (i : Fin k) : ∃ j : Fin k, j ≠ i := by
  by_cases hi : i.val=0
  · exact ⟨⟨1,by omega⟩,fun eq => by have := congrArg Fin.val eq; simp at this; omega⟩
  · exact ⟨⟨0,by omega⟩,fun eq => hi (congrArg Fin.val eq.symm)⟩

theorem valid_root {k} (hk : 2 ≤ k) (t : NatTree) (ho : t.once) (hv : t.vars = Finset.range (2*k))
    (mat : ∀ i j : Fin k, t.eval (cell i j) = decide (i=j)) : @Valid k t := by
  have bounded : ∀ n ∈ t.vars, n < 2*k := fun n hn => Finset.mem_range.mp (hv ▸ hn)
  refine ⟨ho,bounded,?_,fun i _ => by simp [mat],fun i j ne => by simp [mat,ne]⟩
  intro n
  by_contra! bad
  have lit : t.eval (lights {n}) = true := by simpa using bad
  obtain ⟨m,hm,hl⟩ := true_var lit
  have E : m=n := by simpa [lights] using hl
  subst m
  have hn := bounded n hm
  by_cases small : n < k
  · let i : Fin k := ⟨n,small⟩
    obtain ⟨j,ne⟩ := other_index hk i
    have nz : t.eval (cell i j) = true := of_lit lit (by simp [cell,lights,i])
    simp [mat,ne.symm] at nz
  · let j : Fin k := ⟨n-k,by omega⟩
    obtain ⟨i,ne⟩ := other_index hk j
    have e : k+j.val = n := by dsimp [j]; omega
    have nz : t.eval (cell i j) = true := of_lit lit (by simp [cell,lights,e])
    simp [mat,ne] at nz

theorem root_form {k} (hk : 2 ≤ k) (t : NatTree) (ho : t.once) (hv : t.vars = Finset.range (2*k))
    (mat : ∀ i j : Fin k, t.eval (cell i j) = decide (i=j)) :
    ∃ p : Equiv.Perm (Fin k), Function.Involutive p ∧ ∀ w : Nat → Bool, t.eval w = true ↔
      ∃ i : Fin k, Hit p i w := by
  obtain ⟨p,hp⟩ := exists_realizes (valid_root hk t ho hv mat)
  let bij : Equiv.Perm (Fin k) := ⟨p,p,hp.invol,hp.invol⟩
  refine ⟨bij,hp.invol,?_⟩
  intro w
  rw [hp.form]
  constructor
  · rintro ⟨i,_,hi⟩; exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩; exact ⟨i,by rw [hv,Finset.mem_range]; omega,hi⟩

end S.IdentityClass

namespace S
open IdentityClass

def Peeled (e : Nat) (t : NatTree) : Prop :=
  t = .atom e ∨ ∃ q : NatTree, q.once ∧ q.vars = t.vars.erase e ∧
    ∀ w : Nat → Bool, t.eval w = (w e || q.eval w)

theorem present_of_single {t : NatTree} {e : Nat} (h : t.eval (lights {e}) = true) :
    e ∈ t.vars := by
  obtain ⟨a,ha,he⟩ := true_var h
  have eq : a=e := by simpa [lights] using he
  exact eq ▸ ha

theorem peel_left {e : Nat} {t s : NatTree} (h : Peeled e t) (hs : s.once)
    (ne : e ∉ s.vars) (dis : Disjoint t.vars s.vars) : Peeled e (.join false t s) := by
  right
  rcases h with rfl|⟨q,hq,hv,he⟩
  · refine ⟨s,hs,?_,?_⟩
    · ext j
      simp only [NatTree.vars,Finset.mem_erase,Finset.mem_union,Finset.mem_singleton]
      by_cases h : j=e <;> simp_all
    · intro w; rfl
  · refine ⟨.join false q s,⟨hq,hs,?_⟩,?_,?_⟩
    · rw [hv]
      exact Finset.disjoint_left.mpr (fun _ hj hk => Finset.disjoint_left.mp dis (Finset.mem_erase.mp hj).2 hk)
    · ext j
      simp only [NatTree.vars,hv,Finset.mem_erase,Finset.mem_union]
      by_cases h : j=e <;> simp_all
    · intro w; simp [NatTree.eval,he,Bool.or_assoc]

theorem peel_single (e : Nat) (t : NatTree) (once : t.once) (lit : t.eval (lights {e}) = true) :
    Peeled e t := by
  induction t with
  | atom a =>
    left
    have eq : a=e := by simpa [NatTree.eval,lights] using lit
    rw [eq]
  | join b t s it is =>
    obtain ⟨ht,hs,dis⟩ := once
    cases b with
    | true =>
      obtain ⟨lt,ls⟩ := Bool.and_eq_true_iff.mp (show t.eval (lights {e}) && s.eval (lights {e}) = true from lit)
      exact (Finset.disjoint_left.mp dis (present_of_single lt) (present_of_single ls)).elim
    | false =>
      rcases Bool.or_eq_true_iff.mp (show (t.eval (lights {e}) || s.eval (lights {e})) = true from lit) with lt|ls
      · exact peel_left (it ht lt) hs (Finset.disjoint_left.mp dis (present_of_single lt)) dis
      · have rev := peel_left (is hs ls) ht (Finset.disjoint_left.mp dis.symm (present_of_single ls)) dis.symm
        rcases rev with h|⟨q,hq,hv,he⟩
        · cases h
        right
        exact ⟨q,hq,by simpa [NatTree.vars,Finset.union_comm] using hv,
          fun w => by simpa [NatTree.eval,Bool.or_comm] using he w⟩

end S
namespace S
open PEqualNP.CircuitLowerBounds PEqualNP.Represents Finset IdentityClass

def positive (k : ℕ) (a : Fin (k+2)) (b : Fin (k+1)) :=
  decide (a.val=k+1 ∨ (a.val<k ∧ a.val=b.val))

def coreNames (k : ℕ) := range k ∪ Ico (k+1) (2*k+2)

theorem core_card (k : ℕ) : (coreNames k).card=2*k+1 := by
  have dis : Disjoint (range k) (Ico (k+1) (2*k+2)) := by
    rw [disjoint_left]; intro i hi h; simp only [mem_range,mem_Ico] at *; omega
  rw [coreNames,card_union_of_disjoint dis,card_range,Nat.card_Ico]; omega

theorem pairReadRect {n m : ℕ} (a : Fin n) (b : Fin m) (i : Nat) :
    (oneEach a b).getD i false = true ↔ i=a.val ∨ i=n+b.val := by
  unfold oneEach
  by_cases hi : i<n
  · rw [List.getD_append _ _ _ _ (by simpa using hi),oneRead]; omega
  · rw [List.getD_append_right _ _ _ _ (by simp;omega),List.length_ofFn,oneRead]; omega

theorem core_essential {k : ℕ} (c : Circuit) (hg : ∀g∈c.gates, good g)
    (rep : Represents (positive k) c) :
    coreNames k ⊆ back ((k+2)+(k+1)) c.gates {c.output} := by
  let S := back ((k+2)+(k+1)) c.gates {c.output}
  have rising (a a' : Fin (k+2)) (b b' : Fin (k+1))
      (h : ∀ i ∈ S, (i=a.val ∨ i=k+2+b.val) → (i=a'.val ∨ i=k+2+b'.val)) :
      positive k a b = true → positive k a' b' = true := by
    have hit := leBack ((k+2)+(k+1)) c.gates {c.output} hg (oneEach a b) (oneEach a' b')
      (by simp [oneEach]; omega) (by simp [oneEach]; omega) (fun i hi z => (pairReadRect _ _ _).mpr (h _ hi ((pairReadRect _ _ _).mp z))) c.output (by simp)
    change c.eval (oneEach a b) = true → c.eval (oneEach a' b') = true at hit
    simpa [rep a b, rep a' b'] using hit
  intro i hi
  change i∈S
  by_contra missing
  have drop {j : ℕ} (hj : j∈S) : j≠i := fun eq => missing (eq ▸ hj)
  rcases mem_union.mp hi with low|high
  · have lt := mem_range.mp low
    let a : Fin (k+2) := ⟨i,by omega⟩
    let b : Fin (k+1) := ⟨i,by omega⟩
    let full : Fin (k+2) := ⟨k,by omega⟩
    have bad := rising a full b b (fun j hj z => by
      change (j=i ∨ j=k+2+i) at z; exact Or.inr (z.resolve_left (drop hj)))
    simp [positive,a,b,full,lt] at bad
  · obtain ⟨lo,hi⟩ := mem_Ico.mp high
    by_cases last : i=k+1
    · let a : Fin (k+2) := ⟨i,by omega⟩
      let b : Fin (k+1) := ⟨k,by omega⟩
      let full : Fin (k+2) := ⟨k,by omega⟩
      have bad := rising a full b b (fun j hj z => by
        change (j=i ∨ j=k+2+k) at z; exact Or.inr (z.resolve_left (drop hj)))
      simp [positive,a,b,full,last] at bad
    · let m := i-(k+2)
      have mk : m<k := by dsimp [m]; omega
      have idx : k+2+m=i := by dsimp [m];omega
      let a : Fin (k+2) := ⟨m,by omega⟩
      let b : Fin (k+1) := ⟨m,by omega⟩
      let pad : Fin (k+1) := ⟨k,by omega⟩
      have bad := rising a a b pad (fun j hj z => by
        change (j=m ∨ j=k+2+m) at z; rw [idx] at z; exact Or.inl (z.resolve_right (drop hj)))
      simp [positive,a,b,pad,mk,Nat.ne_of_lt mk,show m≠k+1 by omega] at bad

theorem core_tree {k : ℕ} (c : Circuit) (hg : ∀g∈c.gates,good g)
    (rep : Represents (positive k) c) (size : c.size ≤ 2*k) :
    ∃ t : NatTree, t.once ∧ t.vars=coreNames k ∧ ∀ l : List Bool, l.length=(k+2)+(k+1) →
      t.eval (fun i => l.getD i false)=c.eval l := by
  let S := back ((k+2)+(k+1)) c.gates {c.output}
  have sub : coreNames k ⊆ S := core_essential c hg rep
  have lo := card_le_card sub
  rw [core_card] at lo
  have hi : S.card ≤ 1+c.gates.length := by simpa [S] using backCard ((k+2)+(k+1)) c.gates {c.output} hg
  change c.gates.length ≤ 2*k at size
  have names : S=coreNames k := (eq_of_subset_of_card_le sub (by rw [core_card]; omega)).symm
  let t := NatTree.atom c.output
  have tight : (back ((k+2)+(k+1)) c.gates t.vars).card=t.vars.card+c.gates.length := by
    change S.card = ({c.output}:Finset ℕ).card + _; rw [card_singleton]; omega
  obtain ⟨q,ho,hv,he⟩ := traceInputs ((k+2)+(k+1)) c.gates t (by trivial) hg tight
  exact ⟨q,ho,hv.trans names,he⟩
end S
namespace S
open PEqualNP.CircuitLowerBounds PEqualNP.Represents Finset IdentityClass

def NatTree.rename (f : ℕ → ℕ) : NatTree → NatTree
  | .atom a => .atom (f a)
  | .join b l r => .join b (l.rename f) (r.rename f)

theorem NatTree.rename_vars (t : NatTree) (f : ℕ → ℕ) : (t.rename f).vars=t.vars.image f := by
  induction t with
  | atom a => simp [rename,vars]
  | join b l r il ir => simp [rename,vars,il,ir,Finset.image_union]

theorem NatTree.rename_eval (t : NatTree) (f : ℕ → ℕ) (w : ℕ → Bool) :
    (t.rename f).eval w=t.eval (w ∘ f) := by
  induction t with
  | atom a => rfl
  | join b l r il ir => simp [rename,eval,il,ir]

theorem NatTree.rename_once (t : NatTree) (f : ℕ → ℕ) (ht : t.once)
    (inj : ∀ a∈t.vars,∀ b∈t.vars,f a=f b → a=b) : (t.rename f).once := by
  induction t with
  | atom => trivial
  | join op l r il ir =>
    obtain ⟨hl,hr,ds⟩ := ht
    refine ⟨il hl (fun a ha b hb => inj a (mem_union_left _ ha) b (mem_union_left _ hb)),
      ir hr (fun a ha b hb => inj a (mem_union_right _ ha) b (mem_union_right _ hb)),?_⟩
    rw [NatTree.rename_vars,NatTree.rename_vars,disjoint_left]
    intro j h1 h2
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h1
    obtain ⟨b,hb,he⟩ := mem_image.mp h2
    have eq := inj b (mem_union_right _ hb) a (mem_union_left _ ha) he
    exact disjoint_left.mp ds ha (eq ▸ hb)

def packName (k j : ℕ) := if j<k then j else j-2
def unpackName (k j : ℕ) := if j<k then j else j+2

theorem remaining {k j : ℕ} : j ∈ (coreNames k).erase (k+1) ↔ j<k ∨ (k+2≤j ∧ j<2*k+2) := by
  simp only [coreNames,mem_erase,mem_union,mem_range,mem_Ico]; omega

theorem unpack_pack {k j : ℕ} (h : j∈(coreNames k).erase (k+1)) : unpackName k (packName k j)=j := by
  rcases remaining.mp h with lt|⟨lo,hi⟩
  · simp [packName,unpackName,lt]
  · simp [packName,unpackName,show ¬j<k by omega,show ¬j-2<k by omega];omega

theorem pack_range (k : ℕ) : ((coreNames k).erase (k+1)).image (packName k) = range (2*k) := by
  ext j
  simp only [mem_range,mem_image]
  constructor
  · rintro ⟨a,ha,rfl⟩; rcases remaining.mp ha with h|h <;> unfold packName <;> split_ifs <;> omega
  · intro h
    by_cases lt : j<k
    · exact ⟨j,remaining.mpr (Or.inl lt),by simp [packName,lt]⟩
    · exact ⟨j+2,remaining.mpr (Or.inr ⟨by omega,by omega⟩),by simp [packName,show ¬j+2<k by omega]⟩

theorem peel_physical {k : ℕ} (hk : 2≤k) (c : Circuit) (hg : ∀g∈c.gates,good g)
    (rep : Represents (positive k) c) (size : c.size≤2*k) :
    ∃ q : NatTree, q.once ∧ q.vars=(coreNames k).erase (k+1) ∧ ∀ l : List Bool,
      l.length=(k+2)+(k+1) → c.eval l=(l.getD (k+1) false || q.eval (fun i => l.getD i false)) := by
  obtain ⟨t,ht,hv,he⟩ := core_tree c hg rep size
  let a : Fin (k+2) := ⟨k+1,by omega⟩
  let b : Fin (k+1) := ⟨k,by omega⟩
  have yes : c.eval (oneEach a b)=true := (rep a b).trans (by simp [positive,a])
  have lit : t.eval (lights {k+1})=true := by
    rw [← he _ (by simp [oneEach];omega)] at yes
    refine (t.eval_congr ?_).trans yes
    intro j hj
    apply Bool.eq_iff_iff.mpr
    rw [pairReadRect]
    rw [hv] at hj
    simp only [coreNames,mem_union,mem_range,mem_Ico] at hj
    simp [lights,a,b]; omega
  rcases peel_single _ _ ht lit with eq|⟨q,hq,qv,qe⟩
  · rw [eq] at hv
    have := congrArg Finset.card hv
    simp [NatTree.vars,core_card] at this
    omega
  · exact ⟨q,hq,qv.trans (congrArg (fun s : Finset ℕ => s.erase (k+1)) hv),
      fun l h => (he l h).symm.trans (qe _)⟩

end S
namespace S
open PEqualNP.CircuitLowerBounds PEqualNP.Represents Finset IdentityClass

theorem core_class {k : ℕ} (hk : 2≤k) (c : Circuit) (hg : ∀g∈c.gates,good g)
    (rep : Represents (positive k) c) (size : c.size≤2*k) :
    ∃ p : Equiv.Perm (Fin k), Function.Involutive p ∧ ∀ (x : Fin (k+2) → Bool) (y : Fin (k+1) → Bool),
      c.eval (List.ofFn x ++ List.ofFn y) = (x (Fin.last (k+1)) || decide (∃ i : Fin k,
        (x (i.castSucc.castSucc) = true ∧ y (i.castSucc) = true) ∨
        (p i ≠ i ∧ ((x (i.castSucc.castSucc) = true ∧ x ((p i).castSucc.castSucc) = true) ∨
          (y (i.castSucc) = true ∧ y ((p i).castSucc) = true))))) := by
  classical
  obtain ⟨q,hq,qv,ev⟩ := peel_physical hk c hg rep size
  let t := q.rename (packName k)
  have tv : t.vars = range (2*k) := by rw [show t=q.rename _ from rfl,NatTree.rename_vars,qv,pack_range]
  have to1 : t.once := by
    apply q.rename_once _ hq; intro a ha b hb eq
    rw [qv] at ha hb
    exact (unpack_pack ha).symm.trans ((congrArg (unpackName k) eq).trans (unpack_pack hb))
  have mat (a b : Fin k) : t.eval (cell a b)=decide (a=b) := by
    let l := oneEach a.castSucc.castSucc b.castSucc
    have off : l.getD (k+1) false=false := by
      apply Bool.eq_false_iff.mpr; intro hit
      have z := (pairReadRect a.castSucc.castSucc b.castSucc (k+1)).mp hit
      change k+1=a.val ∨ k+1=k+2+b.val at z
      have h := a.isLt; omega
    have hpos : positive k a.castSucc.castSucc b.castSucc=decide (a=b) := by
      simp [positive,Fin.ext_iff,show a.val≠k+1 by have := a.isLt;omega]
    have ce : c.eval l=decide (a=b) := (rep _ _).trans hpos
    rw [ev l (by simp [l,oneEach];omega),off,Bool.false_or] at ce
    refine Eq.trans ?_ ce
    rw [show t=q.rename _ from rfl,NatTree.rename_eval]
    apply q.eval_congr
    intro j hj
    rw [qv] at hj
    apply Bool.eq_iff_iff.mpr
    rw [pairReadRect]
    change lights {a.val,k+b.val} (packName k j)=true ↔ j=a.val ∨ j=k+2+b.val
    simp only [lights,decide_eq_true_eq,mem_insert,mem_singleton]
    rcases remaining.mp hj with lo|lo <;> unfold packName <;> split_ifs <;> have := a.isLt <;> omega
  obtain ⟨p,hp,shape⟩ := root_form hk t to1 tv mat
  refine ⟨p,hp,?_⟩
  intro x y
  let l := List.ofFn x ++ List.ofFn y
  let w := fun n : ℕ => l.getD (unpackName k n) false
  have rowAny {n m : ℕ} (X : Fin n → Bool) (Y : Fin m → Bool) (i : Fin n) :
      (List.ofFn X ++ List.ofFn Y).getD i.val false=X i := by
    rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp)];simp
  have colAny {n m : ℕ} (X : Fin n → Bool) (Y : Fin m → Bool) (i : Fin m) :
      (List.ofFn X ++ List.ofFn Y).getD (n+i.val) false=Y i := by
    rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simp)];simp
  have row := rowAny x y
  have col := colAny x y
  have rw0 (i : Fin k) : w i.val=x i.castSucc.castSucc := by
    change l.getD (unpackName k i.val) false=_
    rw [show unpackName k i.val=i.val by simp [unpackName,i.isLt]]
    exact row i.castSucc.castSucc
  have cw0 (i : Fin k) : w (k+i.val)=y i.castSucc := by
    change l.getD (unpackName k (k+i.val)) false=_
    rw [show unpackName k (k+i.val)=k+2+i.val by simp [unpackName];omega]
    exact col i.castSucc
  have same : t.eval w=q.eval (fun j => l.getD j false) := by
    rw [show t=q.rename _ from rfl,NatTree.rename_eval]
    apply q.eval_congr
    intro j hj; rw [qv] at hj; change l.getD (unpackName k (packName k j)) false=_
    rw [unpack_pack hj]
  change c.eval l=_
  rw [ev _ (by simp [l];omega),← same,show l.getD (k+1) false=x (Fin.last (k+1)) from row (Fin.last (k+1))]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,Hit,rw0,cw0] using shape w
end S
namespace S
open PEqualNP.CircuitLowerBounds PEqualNP.Represents Finset IdentityClass

def orig (k : ℕ) (a : Fin (k+2)) (b : Fin (k+1)) :=
  decide (a.val ≠ k+1 ∧ ¬(a.val<k ∧ a.val=b.val))

def monoNames (k : ℕ) := range (k+1) ∪ Ico (k+2) (2*k+3)

theorem mono_card (k : ℕ) : (monoNames k).card = 2*k+2 := by
  have dis : Disjoint (range (k+1)) (Ico (k+2) (2*k+3)) := by
    rw [disjoint_left]; intro i hi h; simp only [mem_range,mem_Ico] at *;omega
  rw [monoNames,card_union_of_disjoint dis,card_range,Nat.card_Ico];omega

theorem mono_essential {k : ℕ} (hk : 2 ≤ k) (c : Circuit) (hg : ∀g∈c.gates,good g)
    (rep : Represents (orig k) c) : monoNames k ⊆ back ((k+2)+(k+1)) c.gates {c.output} := by
  let S := back ((k+2)+(k+1)) c.gates {c.output}
  have lift (a a' : Fin (k+2)) (b b' : Fin (k+1))
      (h : ∀ i ∈ S, (i=a.val ∨ i=k+2+b.val) → (i=a'.val ∨ i=k+2+b'.val)) :
      orig k a b = true → orig k a' b' = true := by
    have hit := leBack ((k+2)+(k+1)) c.gates {c.output} hg (oneEach a b) (oneEach a' b')
      (by simp [oneEach];omega) (by simp [oneEach];omega)
      (fun i hi z => (pairReadRect _ _ _).mpr (h _ hi ((pairReadRect _ _ _).mp z))) c.output (by simp)
    change c.eval (oneEach a b)=true → c.eval (oneEach a' b')=true at hit
    simpa [rep a b,rep a' b'] using hit
  intro i hi
  change i∈S; by_contra missing
  have drop {j : ℕ} (hj : j∈S) : j≠i := fun eq => missing (eq ▸ hj)
  rcases mem_union.mp hi with row|col
  · have lt := mem_range.mp row
    let a : Fin (k+2) := ⟨i,by omega⟩
    let empty : Fin (k+2) := ⟨k+1,by omega⟩
    let pad : Fin (k+1) := ⟨k,by omega⟩
    have bad := lift a empty pad pad (fun j hj nj => Or.inr (nj.resolve_left (drop hj)))
    simp [orig,a,empty,pad,show i≠k+1 by omega] at bad
    omega
  · obtain ⟨lo,hi⟩ := mem_Ico.mp col
    let v := i-(k+2)
    have vk : v<k+1 := by dsimp [v];omega
    have idx : k+2+v=i := by dsimp [v];omega
    let m := if v=0 then 1 else 0
    have mk : m<k := by unfold m; split <;> omega
    have ne : m≠v := by unfold m;split <;> omega
    let a : Fin (k+2) := ⟨m,by omega⟩
    let b : Fin (k+1) := ⟨v,vk⟩
    let d : Fin (k+1) := ⟨m,by omega⟩
    have bad := lift a a b d (fun j hj nj => by
      change (j=m ∨ j=k+2+v) at nj;rw [idx] at nj;exact Or.inl (nj.resolve_right (drop hj)))
    simp [orig,a,b,d,mk,ne,show m≠k+1 by omega] at bad

theorem mono_tree {k : ℕ} (hk : 2≤k) (c : Circuit) (hg : ∀g∈c.gates,good g)
    (rep : Represents (orig k) c) (size : c.size≤2*k+1) :
    ∃ t : NatTree, t.once ∧ ∀ l : List Bool, l.length=(k+2)+(k+1) →
      t.eval (fun i => l.getD i false)=c.eval l := by
  let S := back ((k+2)+(k+1)) c.gates {c.output}
  have sub : monoNames k ⊆ S := mono_essential hk c hg rep
  have lo := card_le_card sub
  rw [mono_card] at lo
  have hi : S.card ≤ 1+c.gates.length := by simpa [S] using backCard ((k+2)+(k+1)) c.gates {c.output} hg
  change c.gates.length≤2*k+1 at size
  let t := NatTree.atom c.output
  have tight : (back ((k+2)+(k+1)) c.gates t.vars).card=t.vars.card+c.gates.length := by
    change S.card=({c.output}:Finset ℕ).card + _;rw [card_singleton];omega
  obtain ⟨q,ho,_,he⟩ := traceInputs ((k+2)+(k+1)) c.gates t (by trivial) hg tight
  exact ⟨q,ho,he⟩
end S

namespace S.CrownObstruction
open IdentityClass

private theorem other (i j : Fin 3) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  revert i j
  decide

private theorem rows {A B : Fin 3 → Prop} (edges : ∀ i j, i ≠ j → (A i ↔ B j)) (i : Fin 3) : A i ↔ A 0 := by
  obtain ⟨k,hi,hz⟩ := other i 0
  exact (edges i k hi).trans (edges 0 k hz).symm

private theorem columns {A B : Fin 3 → Prop} (edges : ∀ i j, i ≠ j → (A i ↔ B j)) (j : Fin 3) : B j ↔ A 0 := by
  obtain ⟨i,hi,_⟩ := other j j
  exact (edges i j hi.symm).symm.trans (rows edges i)

private theorem keepLeft {t : NatTree} {a b c : Nat} (hb : b ∉ t.vars) :
    t.eval (lights {a,b}) = true → t.eval (lights {a,c}) = true := by
  apply mono
  intro n hn lit
  have e : n=a ∨ n=b := by simpa [lights] using lit
  rcases e with rfl|rfl
  · simp [lights]
  · exact (hb hn).elim

private theorem keepRight {t : NatTree} {a b c : Nat} (ha : a ∉ t.vars) :
    t.eval (lights {a,b}) = true → t.eval (lights {c,b}) = true := by
  apply mono
  intro n hn lit
  have e : n=a ∨ n=b := by simpa [lights] using lit
  rcases e with rfl|rfl
  · exact (ha hn).elim
  · simp [lights]

private theorem bothNames {t : NatTree} {a b : Fin 3 → Nat} {i j : Fin 3}
    (diag : ∀ q, t.eval (lights {a q,b q}) = false) (p : t.eval (lights {a i,b j}) = true) :
    a i ∈ t.vars ∧ b j ∈ t.vars := by
  constructor
  · by_contra h
    have g := keepRight (c:=a j) h p
    rw [diag] at g
    contradiction
  · by_contra h
    have g := keepLeft (c:=b i) h p
    rw [diag] at g
    contradiction

private theorem oneName {t : NatTree} {a b : Nat} (p : t.eval (lights {a,b}) = true) :
    a ∈ t.vars ∨ b ∈ t.vars := by
  obtain ⟨n,hn,lit⟩ := true_var p
  have e : n=a ∨ n=b := by simpa [lights] using lit
  rcases e with rfl|rfl
  · exact .inl hn
  · exact .inr hn

private theorem diagonal {l r : NatTree} {a b : Fin 3 → Nat}
    (ar : ∀ i, a i ∉ r.vars) (bl : ∀ i, b i ∉ l.vars)
    (pos : ∀ i j, i ≠ j → l.eval (lights {a i,b j}) = true ∧ r.eval (lights {a i,b j}) = true) :
    l.eval (lights {a 0,b 0}) = true ∧ r.eval (lights {a 0,b 0}) = true :=
  ⟨keepLeft (bl 1) (pos 0 1 (by decide)).1,keepRight (ar 1) (pos 1 0 (by decide)).2⟩

theorem noCrown (t : NatTree) (ho : t.once) (a b : Fin 3 → Nat)
    (mat : ∀ i j, t.eval (lights {a i,b j}) = decide (i ≠ j)) : False := by
  induction t with
  | atom n =>
    have d (i) := mat i i
    have neg (i) : (NatTree.atom n).eval (lights {a i,b i}) = false := by simpa using d i
    have p : (NatTree.atom n).eval (lights {a 0,b 1}) = true := by simpa using mat 0 1
    have own := (bothNames neg p).1
    have eq : a 0 = n := by simpa [NatTree.vars] using own
    simpa [NatTree.eval,lights,eq] using neg 0
  | join op l r ih jh =>
    obtain ⟨hl,hr,hd⟩ := ho
    have dis := Finset.disjoint_left.mp hd
    cases op with
    | false =>
      have neg (i : Fin 3) : l.eval (lights {a i,b i}) = false ∧ r.eval (lights {a i,b i}) = false :=
        Bool.or_eq_false_iff.mp (by simpa [NatTree.eval] using mat i i)
      have witnesses (i j : Fin 3) (ne : i ≠ j) :
          (a i ∈ l.vars ∧ b j ∈ l.vars ∧ l.eval (lights {a i,b j}) = true) ∨
          (a i ∈ r.vars ∧ b j ∈ r.vars ∧ r.eval (lights {a i,b j}) = true) := by
        have hit := Bool.or_eq_true_iff.mp (show (l.eval (lights {a i,b j}) || r.eval (lights {a i,b j})) = true by
          simpa [NatTree.eval,ne] using mat i j)
        rcases hit with p|q
        · obtain ⟨x,y⟩ := bothNames (fun s => (neg s).1) p
          exact .inl ⟨x,y,p⟩
        · obtain ⟨x,y⟩ := bothNames (fun s => (neg s).2) q
          exact .inr ⟨x,y,q⟩
      have edges (i j : Fin 3) (ne : i ≠ j) : a i ∈ l.vars ↔ b j ∈ l.vars := by
        rcases witnesses i j ne with ⟨x,y,_⟩|⟨x,y,_⟩
        · exact ⟨fun _ => y,fun _ => x⟩
        · exact ⟨fun h => (dis h x).elim,fun h => (dis h y).elim⟩
      by_cases h : a 0 ∈ l.vars
      · apply ih hl
        intro i j
        by_cases eq : i=j
        · subst j; simpa using (neg i).1
        · rcases witnesses i j eq with ⟨_,_,p⟩|⟨x,_,_⟩
          · simpa [eq] using p
          · exact (dis ((rows edges i).mpr h) x).elim
      · apply jh hr
        intro i j
        by_cases eq : i=j
        · subst j; simpa using (neg i).2
        · rcases witnesses i j eq with ⟨x,_,_⟩|⟨_,_,p⟩
          · exact (h ((rows edges i).mp x)).elim
          · simpa [eq] using p
    | true =>
      have pos (i j : Fin 3) (ne : i ≠ j) :
          l.eval (lights {a i,b j}) = true ∧ r.eval (lights {a i,b j}) = true :=
        Bool.and_eq_true_iff.mp (by simpa [NatTree.eval,ne] using mat i j)
      have edges (i j : Fin 3) (ne : i ≠ j) : a i ∈ l.vars ↔ b j ∉ l.vars := by
        obtain ⟨p,q⟩ := pos i j ne
        refine ⟨?_,?_⟩
        · intro h v
          rcases oneName q with u|u
          · exact dis h u
          · exact dis v u
        · intro h
          exact (oneName p).resolve_right h
      have dz : (l.eval (lights {a 0,b 0}) && r.eval (lights {a 0,b 0})) = false := by
        simpa [NatTree.eval] using mat 0 0
      by_cases h : a 0 ∈ l.vars
      · obtain ⟨p,q⟩ := diagonal (fun i => dis ((rows edges i).mpr h)) (fun j => (columns edges j).mpr h) pos
        simp [p,q] at dz
      · have al (i) : a i ∉ l.vars := fun h' => h ((rows edges i).mp h')
        have br (i) : b i ∉ r.vars := by
          apply dis
          by_contra hn
          exact h ((columns edges i).mp hn)
        obtain ⟨q,p⟩ := diagonal al br (fun i j ne => (pos i j ne).symm)
        simp [p,q] at dz
end S.CrownObstruction
namespace S
open PEqualNP.CircuitLowerBounds PEqualNP.Represents IdentityClass

theorem mono_lower_weak (k : ℕ) (hk : 7 ≤ k) (s : ℕ)
    (given : RepSizeAtMost (orig k) s) : 2*k+2 ≤ s := by
  by_contra! small
  obtain ⟨c,hm,hs,rep⟩ := given
  obtain ⟨t,once,he⟩ := mono_tree (by omega) c (fun g hg => hm g hg) rep (by omega)
  apply CrownObstruction.noCrown t once (fun i => i.val) (fun j => k+2+j.val)
  intro i j
  let row : Fin (k+2) := ⟨i.val,by omega⟩
  let col : Fin (k+1) := ⟨j.val,by omega⟩
  have get (n : ℕ) : lights {i.val,k+2+j.val} n = (oneEach row col).getD n false := by
    apply Bool.eq_iff_iff.mpr
    simpa only [lights,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] using (pairReadRect row col n).symm
  rw [t.eval_congr (fun n _ => get n),he _ (by simp [oneEach]; omega),rep row col]
  have lo : i.val < k := by omega
  have non : i.val ≠ k+1 := by omega
  simp [orig,row,col,lo,non,Fin.ext_iff]
end S
namespace Z.Equality
open PEqualNP.CircuitLowerBounds
lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

end Z.Equality
namespace Z.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def isN : GateOp → Bool
  | GateOp.not => true
  | _ => false

def rd (g : Gate) : List ℕ := if isN g.op then g.inputs.take 1 else g.inputs

theorem ev (g : Gate) (f : ℕ → Bool) : g.op.eval (g.inputs.map f) = g.op.eval ((rd g).map f) := by
  unfold rd
  split_ifs with h
  · cases e : g.op <;> simp_all [isN]; cases g.inputs <;> simp [GateOp.eval]
  · rfl

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, stp, ih]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card + gs.countP (fun g => isN g.op) ≤ R.card + gs.length ∧
      ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl stp x).getD w false = (gs.foldl stp y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ (rd g).toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have hr : (rd g).length + (if isN g.op then 1 else 0) ≤ 2 := by
        unfold rd; split_ifs <;> simp <;> omega
      have : R0.card + (if isN g.op then 1 else 0) ≤ R.card + 1 := by
        have hk : (if isN g.op then 1 else 0) ≤ 1 := by split_ifs <;> omega
        by_cases ht : t ∈ R
        · have e : R0 = R.erase t ∪ (rd g).toFinset := if_pos ht
          rw [e]
          have := Finset.card_union_le (R.erase t) (rd g).toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le (rd g)
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · have e : R0 = R := if_neg ht
          rw [e]; omega
      rw [List.countP_append]
      simp only [List.countP_singleton, List.length_append, List.length_singleton]
      split_ifs at this ⊢ <;> omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stp]
      rw [getD_snoc, getD_snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        rw [ev, ev]
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

end Z.Cone

namespace Z.Cone
open PEqualNP.Outside.L_meta_29940.Z.Cone PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem bound : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m → (∀ u u' : Fin n, (∀ v : Fin m, A u v = A u' v) → u = u') → (∀ v v' : Fin m, (∀ u : Fin n, A u v = A u v') → v = v') → ¬ PEqualNP.Represents.RepSizeAtMost A (n + m - 3) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → n + m - 2 ≤ C.size := by
  intro n m A hn hm hrow hcol hno C hF hR
  by_contra hlt
  obtain ⟨R', hc, hR'⟩ := cone (n + m) C.gates (fun g hg => (hF g hg).2) {C.output}
  rw [Finset.card_singleton] at hc
  have key : ∀ (u u' : Fin n) (v v' : Fin m), (∀ i ∈ R', ((oneEach u v).getD i false = true ↔
      (oneEach u' v').getD i false = true)) → A u v = A u' v' := by
    intro u u' v v' h
    have e1 := hR u v
    have e2 := hR u' v'
    simp only [Circuit.eval, Circuit.wires] at e1 e2
    change (C.gates.foldl stp _).getD _ _ = _ at e1 e2
    rw [← e1, ← e2]
    exact hR' _ _ (by simp [oneEach]) (by simp [oneEach])
      (fun i hi => Bool.eq_iff_iff.2 (h i hi)) _ (Finset.mem_singleton_self _)
  let Fr := Finset.univ.filter (fun u : Fin n => ¬ u.val ∈ R')
  let Fc := Finset.univ.filter (fun v : Fin m => ¬ n + v.val ∈ R')
  have hr : Fr.card ≤ 1 := by
    refine Finset.card_le_one.2 fun u hu u0 hu0 => hrow u u0 fun v => key _ _ v v fun i hi => ?_
    simp only [Fr, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu0
    have : i ≠ u.val := fun e => hu (e ▸ hi)
    have : i ≠ u0.val := fun e => hu0 (e ▸ hi)
    simp only [oe]
    constructor <;> intro h <;> omega
  have hl : Fc.card ≤ 1 := by
    refine Finset.card_le_one.2 fun v hv v0 hv0 => hcol v v0 fun u => key u u _ _ fun i hi => ?_
    simp only [Fc, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv0
    have : i ≠ n + v.val := fun e => hv (e ▸ hi)
    have : i ≠ n + v0.val := fun e => hv0 (e ▸ hi)
    simp only [oe]
    constructor <;> intro h <;> omega
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun u : Fin n => u.val ∈ R')
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun v : Fin m => n + v.val ∈ R')
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  change _ + Fr.card = n at h1
  change _ + Fc.card = m at h2
  have h3 : (Finset.univ.filter (fun u : Fin n => u.val ∈ R')).card ≤ (R'.filter (· < n)).card := by
    rw [← Finset.card_image_of_injective _ Fin.val_injective]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, a.2⟩
  have h4 : (Finset.univ.filter (fun v : Fin m => n + v.val ∈ R')).card ≤
      (R'.filter (¬ · < n)).card := by
    rw [← Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h) :
      Function.Injective (fun v : Fin m => n + v.val))]
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨ha, by omega⟩
  have h5 := Finset.card_filter_add_card_filter_not (s := R') (· < n)
  simp only [Circuit.size] at hlt
  have h0 : C.gates.countP (fun g => isN g.op) = 0 := by omega
  refine hno ⟨C, fun g hg => ⟨?_, (hF g hg).2⟩, by simp only [Circuit.size]; omega, hR⟩
  have hn' : isN g.op = false := by
    by_contra hc'
    exact absurd h0 (List.countP_pos_iff.2 ⟨g, hg, by simpa using hc'⟩).ne'
  have := (hF g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
  rcases this with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h] at hn'; simp [isN] at hn'

end Z.Cone

namespace Z.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

theorem run_eq (gs : List Gate) : ∀ w : List Bool, ∀ i,
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
    rw [ih, List.length_append, List.length_singleton, run]
    congr 2; funext j
    rw [getD_snoc, Function.update_apply]

theorem oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt; have hv := v.isLt
  unfold oneEach
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simp [h1])]
    simp [List.getD_eq_getElem?_getD, h1, Fin.ext_iff]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i < n + m
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, show i - n < m by omega,
        ↓reduceDIte, Option.getD_some, Fin.ext_iff, decide_eq_decide]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [false_eq_decide_iff]; omega

def GateAon (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def GateMono (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def effective (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem gate_effective (g : Gate) (x : ℕ → Bool) :
    g.op.eval (g.inputs.map x) = g.op.eval ((effective g).map x) := by
  rcases g with ⟨op, is⟩
  cases op <;> cases is <;> rfl

def oneEachFn {n m : ℕ} (u : Fin n) (v : Fin m) : ℕ → Bool :=
  fun i => decide (i = u.val ∨ i = n + v.val)

end Z.Wires

namespace Z.Equality
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Finset PEqualNP.Outside.L_meta_29940.Z.Wires

def graph (k : ℕ) (i : Fin (k+2)) (j : Fin (k+1)) :=
  decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val))
def base (k : ℕ) := (k+2)+(k+1)

lemma lower_weak (k : ℕ) (hk : 7≤k) (s : ℕ) (given : RepSizeAtMost (graph k) s) : 2*k+2≤s := PEqualNP.Outside.L_meta_29940.S.mono_lower_weak k hk s given
lemma row_distinct (k : ℕ) (hk : 7 ≤ k) (a b : Fin (k+2)) (h : ∀ j, graph k a j = graph k b j) : a=b := by
  apply Fin.ext
  by_contra hn
  have ha := a.isLt; have hb := b.isLt
  have vals (j : Fin (k+1)) : (a.val≠k+1 ∧ ¬(a.val<k ∧ a.val=j.val)) ↔
      (b.val≠k+1 ∧ ¬(b.val<k ∧ b.val=j.val)) := by simpa only [graph,decide_eq_true_eq] using Bool.eq_iff_iff.mp (h j)
  have corner := vals ⟨k,by omega⟩; dsimp only at corner
  by_cases h1 : a.val<k
  · have H := vals ⟨a.val,by omega⟩; dsimp only at H; grind
  · by_cases h2 : b.val<k
    · have H := vals ⟨b.val,by omega⟩; dsimp only at H; grind
    · grind
lemma col_distinct (k : ℕ) (hk : 7 ≤ k) (a b : Fin (k+1)) (h : ∀ i, graph k i a=graph k i b) : a=b := by
  apply Fin.ext; by_contra hn
  have ha := a.isLt; have hb := b.isLt
  have vals (i : Fin (k+2)) := Bool.eq_iff_iff.mp (h i)
  by_cases hh : a.val<k
  · have H := vals ⟨a.val,by omega⟩; simp [graph] at H; omega
  · have H := vals ⟨b.val,by omega⟩; simp [graph] at H; omega

lemma optimum (k : ℕ) (hk : 7 ≤ k) (C : Circuit) (hf : FanInTwo C) (hr : Represents (graph k) C) :
    2*k+1 ≤ C.size := by
  have h := PEqualNP.Outside.L_meta_29940.Z.Cone.bound (k+2) (k+1) (graph k) (by omega) (by omega)
    (row_distinct k hk) (col_distinct k hk) (fun hm => by have := lower_weak k hk _ hm; omega) C hf hr
  omega

lemma last_output (k : ℕ) (hk : 7 ≤ k) (C : Circuit) (hf : FanInTwo C) (hr : Represents (graph k) C)
    (hs : C.size ≤ 2*k+1) : C.output+1 = base k + C.size := by
  have lo := optimum k hk C hf hr
  cases C with
  | mk gs o =>
    induction gs using List.reverseRecOn with
    | nil => change 2*k+1 ≤ 0 at lo; omega
    | append_singleton gs g ih =>
      by_contra hn
      have size : (Circuit.mk (gs++[g]) o).size=gs.length+1 := by simp [Circuit.size]
      have ne : o ≠ base k+gs.length := by rw [size] at hn; change o+1 ≠ base k+(gs.length+1) at hn; omega
      let D : Circuit := ⟨gs,o⟩
      have df : FanInTwo D := fun x hx => hf x (List.mem_append_left _ hx)
      have dr : Represents (graph k) D := by
        intro a b
        have h := hr a b
        change (wiresFrom (gs++[g]) (oneEach a b)).getD o false = _ at h
        rw [wiresFrom_snoc,getD_snoc,length_wiresFrom,
          show (oneEach a b).length=base k from PEqualNP.Outside.L_meta_29940.Z.Wires.oneEach_len a b,if_neg ne] at h
        exact h
      have smaller := optimum k hk D df dr
      change 2*k+1 ≤ gs.length at smaller
      rw [size] at hs; omega

end Z.Equality

namespace Z.Equality
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_29940.Z.Wires
abbrev Bits := ℕ → Bool
abbrev Frontier := Finset ℕ
def agree (S : Frontier) (x y : Bits) := ∀ w ∈ S, x w=y w
def rises (S : Frontier) (x y : Bits) := ∀ w ∈ S, x w=true → y w=true
def pull (t : ℕ) (I S : Frontier) := if t ∈ S then S.erase t ∪ I else S
def update (t : ℕ) (g : Gate) (x : Bits) := Function.update x t (g.op.eval (g.inputs.map x))
def notGate : GateOp → Bool | .not => true | _ => false
def negs (gs : List Gate) := gs.countP (fun g => notGate g.op)
lemma pull_bound (t : ℕ) (I S : Frontier) (m : ℕ) (sz : I.card ≤ m+1) :
    (pull t I S).card ≤ S.card + m := by
  by_cases h : t ∈ S
  · rw [pull,if_pos h]; have := card_union_le (S.erase t) I; have := card_erase_add_one h; omega
  · simp [pull,h]
lemma pull_eq (t : ℕ) (g : Gate) (S : Frontier) (x y : Bits)
    (h : agree (pull t (effective g).toFinset S) x y) :
    agree S (update t g x) (update t g y) := by
  intro w hw
  by_cases ht : w=t
  · subst w
    rw [update,update,Function.update_self,Function.update_self,gate_effective,gate_effective g y]
    congr 1; apply List.map_congr_left
    intro a ha; apply h a
    simp [pull,hw,ha]
  · simp only [update,Function.update_of_ne ht]
    apply h
    by_cases hh : t ∈ S <;> simp [pull,hh,hw,ht]
lemma pull_mono (t : ℕ) (g : Gate) (S : Frontier) (x y : Bits)
    (op : g.op=.and ∨ g.op=.or) (h : rises (pull t g.inputs.toFinset S) x y) :
    rises S (update t g x) (update t g y) := by
  intro w hw
  by_cases ht : w=t
  · subst w; simp only [update,Function.update_self]
    apply gateOp_mono _ op
    intro a ha; apply h; simp [pull,hw,ha]
  · simp only [update,Function.update_of_ne ht]
    apply h
    by_cases hh : t ∈ S <;> simp [pull,hh,hw,ht]

lemma support (gs : List Gate) (t : ℕ) (W : Frontier) (legal : ∀ g ∈ gs, g.inputs.length≤2) :
    ∃ S : Frontier, S.card+negs gs ≤ W.card+gs.length ∧
      ∀ x y : Bits, agree S x y → agree W (run gs t x) (run gs t y) := by
  induction gs generalizing t with
  | nil => exact ⟨W,by simp [negs],fun x y h => h⟩
  | cons g gs ih =>
    obtain ⟨S,sz,h⟩ := ih (t+1) (fun a ha => legal a (List.mem_cons_of_mem _ ha))
    refine ⟨pull t (effective g).toFinset S,?_,fun x y he => h _ _ (pull_eq t g S x y he)⟩
    have len := legal g (by simp)
    have ns : negs (g::gs) = negs gs + if notGate g.op then 1 else 0 := by
      simp only [negs,List.countP_cons]
    rw [ns,List.length_cons]
    by_cases hn : notGate g.op = true
    · have op : g.op=.not := by cases ho : g.op <;> simp [ho,notGate] at hn ⊢
      have cap : (effective g).toFinset.card≤1 := by cases hI : g.inputs <;> simp [effective,op,hI]
      have b := pull_bound t (effective g).toFinset S 0 cap
      rw [if_pos hn]; omega
    · have eg : effective g = g.inputs := by cases ho : g.op <;> simp_all [effective,notGate]
      have cap : (effective g).toFinset.card≤2 := eg ▸ g.inputs.toFinset_card_le.trans len
      have b := pull_bound t (effective g).toFinset S 1 cap
      rw [if_neg hn]; omega

def raw (k : ℕ) (a : Fin (k+2)) (b : Fin (k+1)) : Bits := oneEachFn a b
lemma raw_eval (k) (C : Circuit) (a : Fin (k+2)) (b : Fin (k+1)) :
    run C.gates (base k) (raw k a b) C.output = C.eval (oneEach a b) := by
  have h := run_eq C.gates (oneEach a b) C.output
  simp only [oneEach_len,oneEach_getD] at h
  exact h.symm

def others {n m : ℕ} (r : Fin n) (c : Fin m) : Frontier :=
  (univ.erase r).image Fin.val ∪ (univ.erase c).image (fun i => n+i.val)
lemma others_card {n m : ℕ} (r : Fin n) (c : Fin m) :
    (others r c).card = n-1+(m-1) := by
  have hd : Disjoint ((univ.erase r).image Fin.val) ((univ.erase c).image (fun i => n+i.val)) := by
    apply disjoint_left.mpr; intro w h1 h2
    obtain ⟨a,_,rfl⟩ := mem_image.mp h1; obtain ⟨b,_,e⟩ := mem_image.mp h2
    have := a.isLt; omega
  rw [others,card_union_of_disjoint hd,card_image_of_injective _ Fin.val_injective,
    card_image_of_injective _ (fun _ _ h => Fin.ext (Nat.add_left_cancel h))]
  simp [card_erase_of_mem]
lemma others_mem {n m} (r : Fin n) (c : Fin m) (a : Fin n) (b : Fin m) :
    (a.val ∈ others r c ↔ a≠r) ∧ (n+b.val ∈ others r c ↔ b≠c) := by
  simp only [others,mem_union,mem_image,mem_erase,mem_univ,true_and,and_true]
  constructor
  · constructor
    · rintro (⟨i,h,e⟩|⟨j,_,e⟩)
      · exact Fin.val_injective e ▸ h
      · have := a.isLt; omega
    · intro h; exact Or.inl ⟨a,h,rfl⟩
  · constructor
    · rintro (⟨i,_,e⟩|⟨j,h,e⟩)
      · have := i.isLt;omega
      · exact Fin.ext (Nat.add_left_cancel e) ▸ h
    · intro h;exact Or.inr ⟨b,h,rfl⟩

lemma almost {α : Type} [Nonempty α] (P : α → Prop) (single : ∀ a b, ¬P a → ¬P b → a=b) :
    ∃ r, ∀ a, a≠r → P a := by
  classical
  by_cases h : ∃ a, ¬ P a
  · obtain ⟨r,hr⟩ := h; exact ⟨r,fun a ne => by by_contra hn;exact ne (single a r hn hr)⟩
  · exact ⟨Classical.arbitrary _,fun a _ => by by_contra hn;exact h ⟨a,hn⟩⟩

lemma names (k : ℕ) (hk : 7 ≤ k) (S : Frontier)
    (h : ∀ a b a' b', agree S (raw k a b) (raw k a' b') → graph k a b = graph k a' b') :
    ∃ (r : Fin (k+2)) (c : Fin (k+1)), others r c ⊆ S := by
  obtain ⟨r,hr⟩ := almost (fun a : Fin (k+2) => a.val ∈ S) (fun a a' ha ha' =>
    row_distinct k hk a a' (fun b => h _ _ _ _ (by
      intro i hi; have h1 : i≠a.val := fun eq => ha (eq ▸ hi)
      have h2 : i≠a'.val := fun eq => ha' (eq ▸ hi)
      simp [raw,oneEachFn,h1,h2])))
  obtain ⟨c,hc⟩ := almost (fun b : Fin (k+1) => k+2+b.val ∈ S) (fun b b' hb hb' =>
    col_distinct k hk b b' (fun a => h _ _ _ _ (by
      intro i hi; have h1 : i≠k+2+b.val := fun eq => hb (eq ▸ hi)
      have h2 : i≠k+2+b'.val := fun eq => hb' (eq ▸ hi)
      simp [raw,oneEachFn,h1,h2])))
  refine ⟨r,c,?_⟩
  intro w hw; rcases mem_union.mp hw with hw|hw
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp hw; exact hr _ (mem_erase.mp ha).1
  · obtain ⟨b,hb,rfl⟩ := mem_image.mp hw; exact hc _ (mem_erase.mp hb).1

lemma neg_unique (k) (hk : 7 ≤ k) (C : Circuit) (hf : FanInTwo C) (hr : Represents (graph k) C)
    (hs : C.size≤2*k+1) : negs C.gates = 1 := by
  obtain ⟨S,sz,dep⟩ := support C.gates (base k) {C.output} (fun g hg => (hf g hg).2)
  obtain ⟨r,c,hsub⟩ := names k hk S (fun a b a' b' h => by
    have hh := dep _ _ h C.output (mem_singleton_self _)
    rw [raw_eval,raw_eval,hr a b,hr a' b'] at hh; exact hh)
  have ct := card_le_card hsub
  rw [others_card] at ct; simp only [card_singleton] at sz
  change C.gates.length≤2*k+1 at hs
  have nonzero : negs C.gates ≠ 0 := by
    intro h
    have hm : Monotone2 C := by
      intro g hg
      obtain ⟨op,len⟩ := hf g hg
      have ng := List.countP_eq_zero.mp h g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *
      rcases op with ha|ho|hn
      · exact ⟨Or.inl ha,len⟩
      · exact ⟨Or.inr ho,len⟩
      · simp [hn,notGate] at ng
    have big := lower_weak k hk C.size ⟨C,hm,le_rfl,hr⟩
    change 2*k+2 ≤ C.gates.length at big; omega
  omega
end Z.Equality

namespace Z.Equality
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_29940.Z.Wires
lemma pull_union (t) (I A B : Frontier) : pull t I (A∪B) = pull t I A ∪ pull t I B := by
  ext i; by_cases eq : i=t <;> by_cases a : t ∈ A <;> by_cases b : t ∈ B <;> simp_all [pull] <;> tauto

lemma preserve (t) (I A B : Frontier) (s : I.card ≤ 2) (hd : Disjoint A B)
    (sat : (pull t I (A∪B)).card = (A∪B).card+1) :
    Disjoint (pull t I A) (pull t I B) ∧
    (A.Nonempty → (pull t I A).Nonempty) ∧ (B.Nonempty → (pull t I B).Nonempty) := by
  have mem : t ∈ A∪B := by by_contra hn; simp [pull,hn] at sat
  rw [pull,if_pos mem] at sat
  have card := card_erase_add_one mem
  have bound := card_union_le ((A∪B).erase t) I
  have hI : I.card=2 := by omega
  have dis : Disjoint ((A∪B).erase t) I := card_union_eq_card_add_card.mp (by omega)
  have ne : I.Nonempty := card_pos.mp (by omega)
  have keeps (S : Frontier) : S.Nonempty → (pull t I S).Nonempty := by
    intro h; by_cases hm : t∈S
    · rw [pull,if_pos hm]; exact ne.mono subset_union_right
    · simpa [pull,hm] using h
  refine ⟨?_,keeps A,keeps B⟩
  apply disjoint_left.mpr
  intro w hw1 hw2
  simp only [pull] at hw1 hw2
  split at hw1 <;> split at hw2
  · rename_i ha hb; exact disjoint_left.mp hd ha hb
  · rename_i ha hb
    rcases mem_union.mp hw1 with h|h
    · exact disjoint_left.mp hd (mem_of_mem_erase h) hw2
    · exact disjoint_left.mp dis (mem_erase.mpr ⟨fun eq => hb (eq ▸ hw2),mem_union_right _ hw2⟩) h
  · rename_i ha hb
    rcases mem_union.mp hw2 with h|h
    · exact disjoint_left.mp hd hw1 (mem_of_mem_erase h)
    · exact disjoint_left.mp dis (mem_erase.mpr ⟨fun eq => ha (eq ▸ hw1),mem_union_left _ hw1⟩) h
  · exact disjoint_left.mp hd hw1 hw2

lemma propagate (gs : List Gate) (t : ℕ) (A B : Frontier)
    (legal : ∀ g ∈ gs, GateMono g) :
    ∃ X Y : Frontier, (X∪Y).card ≤ (A∪B).card+gs.length ∧
      (∀ x y, rises X x y → rises A (run gs t x) (run gs t y)) ∧
      (∀ x y, rises Y x y → rises B (run gs t x) (run gs t y)) ∧
      ((X∪Y).card = (A∪B).card+gs.length → Disjoint A B →
        Disjoint X Y ∧ (A.Nonempty → X.Nonempty) ∧ (B.Nonempty → Y.Nonempty)) := by
  induction gs generalizing t with
  | nil => exact ⟨A,B,by simp,fun _ _ h => h,fun _ _ h => h,fun _ hd => ⟨hd,id,id⟩⟩
  | cons g gs ih =>
    obtain ⟨S,T,sz,f1,f2,pres⟩ := ih (t+1) (fun a ha => legal a (List.mem_cons_of_mem _ ha))
    obtain ⟨op,len⟩ := legal g (by simp)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    let I := g.inputs.toFinset
    have hI : I.card ≤ 2 := g.inputs.toFinset_card_le.trans len
    have pc := pull_bound t I (S∪T) 1 hI
    refine ⟨pull t I S,pull t I T,?_,fun x y h => f1 _ _ (pull_mono t g S x y op h),
      fun x y h => f2 _ _ (pull_mono t g T x y op h),?_⟩
    · rw [← pull_union,List.length_cons];omega
    · rw [← pull_union,List.length_cons]
      intro sat hd
      have ⟨d,ha,hb⟩ := pres (by omega) hd
      have ⟨dd,haa,hbb⟩ := preserve t I S T hI d (by omega)
      exact ⟨dd,haa ∘ ha,hbb ∘ hb⟩

lemma mono_of_zero {gs : List Gate} (h : negs gs = 0) (hf : ∀ g ∈ gs, GateAon g) :
    ∀ g ∈ gs, GateMono g := by
  intro g hg
  have ng := List.countP_eq_zero.mp h g hg
  obtain ⟨op,len⟩ := hf g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
  refine ⟨?_,len⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  rcases op with ha|ho|hn
  · exact Or.inl ha
  · exact Or.inr ho
  · simp [hn,notGate] at ng
end Z.Equality

namespace Z.Equality
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_29940.Z.Wires
lemma run_append (p q : List Gate) (t : ℕ) (x : Bits) :
    run (p++q) t x = run q (t+p.length) (run p t x) := by
  induction p generalizing t x with
  | nil => simp [run]
  | cons g p ih => simp only [List.cons_append,run,List.length_cons]; rw [ih]; congr 1 <;> omega

lemma bool_eq {a b : Bool} (hf : a=true → b=true) (hb : b=true → a=true) : a=b := Bool.eq_iff_iff.mpr ⟨hf,hb⟩
lemma agree_rises {S : Frontier} {x y : Bits} (h : agree S x y) : rises S x y := fun i hi e => (h i hi) ▸ e
lemma agree_symm {S : Frontier} {x y : Bits} (h : agree S x y) : agree S y x := fun i hi => (h i hi).symm

structure Profile (k : ℕ) (A : Frontier) (B : Frontier) where
  bit : Bits → Bool
  inner : ∀ x y, rises A x y → bit y=true → bit x=true
  outer : ∀ i j i' j', rises B (raw k i j) (raw k i' j') →
    (bit (raw k i j)=true → bit (raw k i' j')=true) →
    graph k i j=true → graph k i' j'=true

lemma split_physical (k : ℕ) (hk : 7 ≤ k) (p q : List Gate) (g : Gate) (o : ℕ)
    (op : g.op=.not) (mp : ∀ a ∈ p, GateMono a) (mq : ∀ a ∈ q, GateMono a)
    (hr : Represents (graph k) ⟨p++g::q,o⟩) (sz : (p++g::q).length ≤ 2*k+1) :
    ∃ (A B : Frontier) (r : Fin (k+2)) (c : Fin (k+1)), A∪B = others r c ∧
      Disjoint A B ∧ (0<q.length → B.Nonempty) ∧ Nonempty (Profile k A B) := by
  classical
  let N := base k
  let w := N+p.length
  let pre := run p N
  let H := fun x : Bits => g.op.eval (g.inputs.map (pre x))
  let F := fun x : Bits => run q (w+1) (Function.update (pre x) w (H x)) o
  have fe (a b) : F (raw k a b) = graph k a b := by
    rw [← hr a b,← raw_eval]; change _ = run (p++g::q) N (raw k a b) o
    rw [run_append];rfl
  obtain ⟨S,unused,st,lead,_,_⟩ := propagate q (w+1) {o} ∅ mq
  have small : S.card ≤ 1+q.length := by
    have := card_le_card (subset_union_left (s₁:=S) (s₂:=unused)); simp only [union_empty,card_singleton] at st; omega
  have head (x y : Bits) (xy : rises S x y) : run q (w+1) x o=true → run q (w+1) y o=true :=
    lead x y xy o (mem_singleton_self _)
  have hw : w ∈ S := by
    by_contra miss
    let D0 : Circuit := ⟨p++(⟨.or,[]⟩:Gate)::q,o⟩
    have hm : Monotone2 D0 := by
      intro a ha
      change a ∈ p++ _ ::q at ha
      rcases List.mem_append.mp ha with ha|ha
      · exact mp a ha
      · rcases List.mem_cons.mp ha with rfl|ha
        · simp
        · exact mq a ha
    have dr : Represents (graph k) D0 := by
      intro a b; rw [← raw_eval,← fe]
      change run (p++ _ ::q) N _ o = _
      rw [run_append]; simp only [run]
      apply bool_eq
      all_goals
        apply head
        intro i hi
        have ne : i≠w := fun eq => miss (eq ▸ hi)
        dsimp only [F,w,pre,H] at *
        simp only [Function.update_of_ne ne,update]
        exact id
    have larger := lower_weak k hk D0.size ⟨D0,hm,le_rfl,dr⟩
    change 2*k+2 ≤ (p++_::q).length at larger
    simp only [List.length_append,List.length_cons] at larger sz
    omega
  let I := (effective g).toFinset
  let T := S.erase w
  obtain ⟨A,B,namesBound,inn,out,pres⟩ := propagate p N I T mp
  have single : I.card ≤ 1 := by cases hi : g.inputs <;> simp [I,effective,op,hi]
  have denom := card_erase_add_one hw
  change T.card + 1 = S.card at denom
  have cap := card_union_le I T
  have inner (x y : Bits) (xy : rises A x y) : H y=true → H x=true := by
    have h := inn x y xy
    cases hi : g.inputs with
    | nil => simp [H,op,hi,GateOp.eval]
    | cons v l =>
      have hv : v∈I := by simp [I,effective,op,hi]
      have hmono := h v hv
      change pre x v = true → pre y v = true at hmono
      simp only [H,op,hi,List.map_cons,GateOp.eval,List.headD_cons]
      cases hx : pre x v <;> cases hy : pre y v <;> simp_all
  have outer (x y : Bits) (xy : rises B x y) (hh : H x=true → H y=true) : F x=true → F y=true := by
    apply head
    intro i hi
    by_cases e : i=w
    · subst i; simpa using hh
    · simp only [Function.update_of_ne e]
      exact out x y xy i (mem_erase.mpr ⟨e,hi⟩)
  have agreeF (x y : Bits) (h : agree (A∪B) x y) : F x=F y := by
    have ea : agree A x y := fun i hi => h i (mem_union_left _ hi)
    have eb : agree B x y := fun i hi => h i (mem_union_right _ hi)
    exact bool_eq (outer x y (agree_rises eb) (inner y x (agree_rises (agree_symm ea))))
      (outer y x (agree_rises (agree_symm eb)) (inner x y (agree_rises ea)))
  obtain ⟨r,c,sub⟩ := names k hk (A∪B) (fun a b a' b' h => by rw [← fe,← fe]; exact agreeF _ _ h)
  have nmin := card_le_card sub; rw [others_card] at nmin
  simp only [List.length_append,List.length_cons] at sz
  have card1 : (I∪T).card=I.card+T.card := by omega
  obtain ⟨d,_,keep⟩ := pres (by omega) (card_union_eq_card_add_card.mp card1)
  refine ⟨A,B,r,c,(eq_of_subset_of_card_le sub (by rw [others_card];omega)).symm,d,
    fun qpos => keep (card_pos.mp (by omega)),?_⟩
  exact ⟨⟨H,inner,fun a b a' b' h1 h2 => by rw [← fe,← fe];exact outer _ _ h1 h2⟩⟩
end Z.Equality

namespace Z.Equality
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_29940.Z.Wires

lemma row_rises {S : Frontier} {k : ℕ} (i i' : Fin (k+2)) (j : Fin (k+1))
    (miss : i.val∉S) : rises S (raw k i j) (raw k i' j) := by
  intro w hw
  have ne : w≠i.val := fun eq => miss (eq ▸ hw)
  simp [raw,oneEachFn,ne]
  tauto

lemma col_rises {S : Frontier} {k : ℕ} (i : Fin (k+2)) (j j' : Fin (k+1))
    (miss : k+2+j.val∉S) : rises S (raw k i j) (raw k i j') := by
  intro w hw
  have ne : w≠k+2+j.val := fun eq => miss (eq ▸ hw)
  simp [raw,oneEachFn,ne]
  tauto

lemma next_index {k t : ℕ} (hk : 7 ≤ k) : ∃ z, z<k ∧ z≠t := by
  by_cases e : t=0
  · exact ⟨1,by omega,by omega⟩
  · exact ⟨0,by omega,Ne.symm e⟩

lemma profile_empty (k : ℕ) (hk : 7 ≤ k) (A B : Frontier) (r : Fin (k+2)) (c : Fin (k+1))
    (h : A∪B=others r c) (d : Disjoint A B) (P : Profile k A B) : B=∅ := by
  classical
  have rm : r.val∉A∪B := by rw [h]; simp [(others_mem r c r c).1]
  have cm : k+2+c.val∉A∪B := by rw [h]; simp [(others_mem r c r c).2]
  simp only [mem_union,not_or] at rm cm
  have row (a a' : Fin (k+2)) (j : Fin (k+1)) (aB : a.val∉B) (aA : a'.val∉A) :=
    P.outer a j a' j (row_rises a a' j aB) (P.inner _ _ (row_rises a' a j aA))
  have col (i : Fin (k+2)) (b b' : Fin (k+1)) (bB : k+2+b.val∉B) (bA : k+2+b'.val∉A) :=
    P.outer i b i b' (col_rises i b b' bB) (P.inner _ _ (col_rises i b' b bA))
  have excl {w : ℕ} (hw : w∈B) : w∉A := fun ha => disjoint_left.mp d ha hw
  have ctop : c.val=k := by
    by_contra e
    have cc := c.isLt
    obtain ⟨z,hz,zn⟩ := next_index (t:=c.val) hk
    let b : Fin (k+1) := ⟨z,by omega⟩
    by_cases hb : k+2+b.val∈B
    · have f := col ⟨z,by omega⟩ c b cm.2 (excl hb)
      simp [graph,b] at f; omega
    · have f := col ⟨c.val,by omega⟩ b c hb cm.1
      simp [graph,b] at f; omega
  have allCol (b : Fin (k+1)) : k+2+b.val∉B := by
    intro hb
    have ne : b≠c := fun e => cm.2 (e ▸ hb)
    have vne : b.val≠c.val := fun e => ne (Fin.ext e)
    have bb := b.isLt
    have f := col ⟨b.val,by omega⟩ c b cm.2 (excl hb)
    simp [graph] at f; omega
  have rtop : k ≤ r.val := by
    by_contra e
    obtain ⟨z,hz,zn⟩ := next_index (t:=r.val) hk
    let a : Fin (k+2) := ⟨z,by omega⟩
    by_cases ha : a.val∈B
    · have f := row r a ⟨z,by omega⟩ rm.2 (excl ha)
      simp [graph,a] at f; omega
    · have f := row a r ⟨r.val,by omega⟩ ha rm.1
      simp [graph,a] at f; omega
  have rfull : r.val=k := by
    by_contra e
    have rr := r.isLt
    have re : r.val=k+1 := by omega
    have allRow (a : Fin (k+2)) : a.val∉A := by
      intro ha
      have ne : a≠r := fun h => rm.1 (h ▸ ha)
      have vne : a.val≠r.val := fun e => ne (Fin.ext e)
      have aB : a.val∉B := fun hb => excl hb ha
      have f := row a r ⟨k,by omega⟩ aB rm.1
      simp [graph,re] at f; omega
    let code := fun b : Fin (k+1) => P.bit (raw k r b)
    have bits (a : Fin (k+2)) (b : Fin (k+1)) : P.bit (raw k a b)=code b :=
      bool_eq (P.inner _ _ (row_rises r a b (allRow r))) (P.inner _ _ (row_rises a r b (allRow a)))
    have inj : Function.Injective code := by
      intro b b' e
      apply col_distinct k hk
      intro a
      apply bool_eq
      · apply P.outer _ _ _ _ (col_rises a b b' (allCol b))
        rw [bits,bits,e]; exact id
      · apply P.outer _ _ _ _ (col_rises a b' b (allCol b'))
        rw [bits,bits,e]; exact id
    have card := Fintype.card_le_of_injective code inj
    simp at card; omega
  have allRow (a : Fin (k+2)) : a.val∉B := by
    intro ha
    have ne : a≠r := fun h => rm.2 (h ▸ ha)
    have vne : a.val≠r.val := fun e => ne (Fin.ext e)
    let b : Fin (k+1) := ⟨min a.val k,by omega⟩
    have f := row r a b rm.2 (excl ha)
    have av := a.isLt
    simp [graph,rfull,b] at f; omega
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  have mem : w∈others r c := h ▸ mem_union_right A hw
  rcases mem_union.mp mem with m|m
  · obtain ⟨a,_,rfl⟩ := mem_image.mp m; exact allRow a hw
  · obtain ⟨b,_,rfl⟩ := mem_image.mp m; exact allCol b hw
end Z.Equality

namespace Z.Equality
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
lemma last_not (k : ℕ) (hk : 7 ≤ k) (C : Circuit) (hf : FanInTwo C) (hr : Represents (graph k) C)
    (sz : C.size≤2*k+1) : ∀ j : Fin C.size, (NestedCover.gateAt C j.val).op=.not ↔ j.val+1=C.size := by
  have count := neg_unique k hk C hf hr sz
  obtain ⟨g,hg,ng⟩ := List.countP_pos_iff.mp (show 0<negs C.gates by omega)
  have op : g.op=.not := by cases he : g.op <;> simp_all [notGate]
  obtain ⟨p,q,split⟩ := List.append_of_mem hg
  obtain ⟨gs,o⟩ := C
  change gs=p++g::q at split
  subst gs
  change negs (p++g::q)=1 at count
  have cons : negs (g::q)=negs q+1 :=
    List.countP_cons_of_pos (p:=fun a : Gate => notGate a.op) (l:=q) (a:=g) (by simp [op,notGate])
  have sum : negs p + negs (g::q)=1 := (List.countP_append ..).symm.trans count
  rw [cons] at sum
  have mp := mono_of_zero (gs:=p) (by omega) (fun a ha => hf a (List.mem_append_left _ ha))
  have mq := mono_of_zero (gs:=q) (by omega) (fun a ha => hf a (List.mem_append_right _ (List.mem_cons_of_mem _ ha)))
  obtain ⟨A,B,r,c,h,d,post,⟨P⟩⟩ := split_physical k hk p q g o op mp mq hr sz
  have empty := profile_empty k hk A B r c h d P
  have qnil : q=[] := by
    by_contra ne
    have := post (List.length_pos_iff.mpr ne)
    simpa [empty] using this
  subst q
  intro j
  have bound := j.isLt
  change j.val < (p++[g]).length at bound
  change ((p++[g]).getD j.val _).op=.not ↔ j.val+1=(p++[g]).length
  rw [List.getD_eq_getElem _ _ bound]
  simp only [List.length_append,List.length_singleton] at bound ⊢
  by_cases pre : j.val<p.length
  · rw [List.getElem_append_left pre]
    obtain ⟨hm,_⟩ := mp p[j.val] (List.getElem_mem ..)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
    rcases hm with h|h <;> rw [h] <;> simp <;> omega
  · have eq : j.val=p.length := by omega
    rw [List.getElem_append_right (by omega)]; simp [eq,op]
end Z.Equality

namespace Converse

variable {k : ℕ}

private def Accepted (p : Equiv.Perm (Fin k)) (x y : Fin k → Bool) : Prop :=
  ∃ i, (x i = true ∧ y i = true) ∨ (p i ≠ i ∧
    ((x i = true ∧ x (p i) = true) ∨ (y i = true ∧ y (p i) = true)))

private def rowPair (a b : Fin k) (i : Fin k) : Bool := decide (i = a ∨ i = b)

private theorem pair_probe {p : Equiv.Perm (Fin k)} (hinv : Function.Involutive p)
    {a b : Fin k} (hab : a ≠ b) :
    Accepted p (rowPair a b) (fun _ => false) ↔ p a = b := by
  constructor
  · rintro ⟨i, h⟩
    simp only [rowPair, decide_eq_true_eq, Bool.false_eq_true, and_false,
      or_false, false_or] at h
    rcases h with ⟨hne, (rfl | rfl), hpartner | hpartner⟩
    · exact (hne hpartner).elim
    · exact hpartner
    · rw [← hpartner, hinv]
    · exact (hne hpartner).elim
  · intro hp
    refine ⟨a, Or.inr ⟨?_, Or.inl ⟨?_, ?_⟩⟩⟩
    · simpa [hp] using Ne.symm hab
    · simp [rowPair]
    · simp [rowPair, hp]

private theorem recover {p q : Equiv.Perm (Fin k)} (hp : Function.Involutive p)
    (hq : Function.Involutive q)
    (h : ∀ x y, Accepted p x y ↔ Accepted q x y) : p = q := by
  apply Equiv.ext
  intro a
  by_cases hpa : p a = a
  · by_contra hne
    have hqa : a ≠ q a := by simpa [hpa] using hne
    have hit := (pair_probe hq hqa).mpr rfl
    have eq := (pair_probe hp hqa).mp ((h _ _).mpr hit)
    exact hne eq
  · have hit := (pair_probe hp (Ne.symm hpa)).mpr rfl
    exact ((pair_probe hq (Ne.symm hpa)).mp ((h _ _).mp hit)).symm

private def fixed (p : Equiv.Perm (Fin k)) : Finset (Fin k) := Finset.univ.filter (fun i => p i = i)
private def lower (p : Equiv.Perm (Fin k)) : Finset (Fin k) := Finset.univ.filter (fun i => i < p i)
private def upper (p : Equiv.Perm (Fin k)) : Finset (Fin k) := Finset.univ.filter (fun i => p i < i)

private theorem orbit_count {p : Equiv.Perm (Fin k)} (hp : Function.Involutive p) :
    (fixed p).card + 2 * (lower p).card = k := by
  classical
  have himg : (lower p).image p = upper p := by
    ext j
    simp only [lower, upper, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; simpa only [hp i] using hi
    · intro h; exact ⟨p j, by simpa only [hp j] using h, hp j⟩
  have hc : (upper p).card = (lower p).card := by rw [← himg, Finset.card_image_of_injective _ p.injective]
  have dis1 : Disjoint (fixed p) (lower p) := by
    simp only [Finset.disjoint_left, fixed, lower, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i h hlt; simp [h] at hlt
  have dis2 : Disjoint (fixed p ∪ lower p) (upper p) := by
    simp only [Finset.disjoint_left, fixed, lower, upper, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rintro i (h|h) hlt; · simp [h] at hlt
    exact (lt_asymm h hlt)
  have all : fixed p ∪ lower p ∪ upper p = Finset.univ := by
    ext i
    simp only [fixed, lower, upper, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases lt_trichotomy i (p i) with h|h|h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inr h
  have h := congrArg Finset.card all
  rw [Finset.card_union_of_disjoint dis2, Finset.card_union_of_disjoint dis1, Finset.card_univ, Fintype.card_fin, hc] at h
  omega

private def crossBlock (i j : Fin k) (x y : Fin k → Bool) : Bool := (x i || y j) && (x j || y i)

private theorem cross_test (i j : Fin k) (x y : Fin k → Bool) :
    crossBlock i j x y = true ↔ (x i = true ∧ y i = true) ∨ (x j = true ∧ y j = true) ∨
      (x i = true ∧ x j = true) ∨ (y i = true ∧ y j = true) := by
  simp only [crossBlock, Bool.and_eq_true, Bool.or_eq_true]
  tauto

private theorem blocks {p : Equiv.Perm (Fin k)} (hp : Function.Involutive p)
    (x y : Fin k → Bool) : Accepted p x y ↔
    (∃ i ∈ fixed p, x i = true ∧ y i = true) ∨ (∃ i ∈ lower p, crossBlock i (p i) x y = true) := by
  simp only [fixed, lower, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, h⟩
    rcases lt_trichotomy i (p i) with hi|hi|hi
    · right; refine ⟨i, hi, (cross_test _ _ _ _).mpr ?_⟩
      rcases h with diag | ⟨_, side⟩
      · exact Or.inl diag
      · exact Or.inr (Or.inr side)
    · left; refine ⟨i, hi.symm, ?_⟩
      exact h.resolve_right (fun z => z.1 hi.symm)
    · right; refine ⟨p i, by simpa only [hp i] using hi, ?_⟩
      rw [hp i, cross_test]; rcases h with diag | ⟨_, a|b⟩
      · exact Or.inr (Or.inl diag)
      · exact Or.inr (Or.inr (Or.inl a.symm))
      · exact Or.inr (Or.inr (Or.inr b.symm))
  · rintro (⟨i, _, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, Or.inl h⟩
    · rcases (cross_test _ _ _ _).mp h with a | a | a | a
      · exact ⟨i, Or.inl a⟩
      · exact ⟨p i, Or.inl a⟩
      · exact ⟨i, Or.inr ⟨hi.ne', Or.inl a⟩⟩
      · exact ⟨i, Or.inr ⟨hi.ne', Or.inr a⟩⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private theorem length_eval (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega
private theorem low_eval (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private inductive Expr (n : ℕ) where
  | leaf (i : Fin n)
  | join (conjunction : Bool) (l r : Expr n)

private def cost : Expr n → ℕ
  | .leaf _ => 0
  | .join _ l r => cost l + cost r + 1
private def value (v : Fin n → Bool) : Expr n → Bool
  | .leaf i => v i
  | .join b l r => if b then value v l && value v r else value v l || value v r
private def output : Expr n → ℕ → ℕ
  | .leaf i, _ => i.val
  | .join _ l r, ofs => ofs + cost l + cost r
private def emit : Expr n → ℕ → List Gate
  | .leaf _, _ => []
  | .join b l r, ofs => emit l ofs ++ emit r (ofs+cost l) ++
      [⟨if b then GateOp.and else GateOp.or, [output l ofs, output r (ofs+cost l)]⟩]
private theorem length_emit (t : Expr n) (ofs : ℕ) : (emit t ofs).length = cost t := by
  induction t generalizing ofs with
  | leaf => rfl
  | join _ _ _ ihl ihr => simp [emit, cost, ihl, ihr, Nat.add_assoc]
private theorem output_bound (t : Expr n) (ofs : ℕ) (h : n ≤ ofs) : output t ofs < ofs + cost t := by
  cases t with
  | leaf i => simpa [output,cost] using (lt_of_lt_of_le i.isLt h)
  | join _ l r => simp [output,cost]; omega
private theorem legal (t : Expr n) (ofs : ℕ) : ∀ g ∈ emit t ofs,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction t generalizing ofs with
  | leaf => simp [emit]
  | join b l r ihl ihr =>
    intro g hg
    simp only [emit, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact ihl _ _ hg
    · exact ihr _ _ hg
    · cases b <;> simp

private theorem emit_eval (t : Expr n) (v : Fin n → Bool) (w : List Bool) (ofs : ℕ)
    (hlen : w.length = ofs) (hbase : n ≤ ofs) (hw : ∀ i : Fin n, w.getD i.val false = v i) :
    ((emit t ofs).foldl step w).getD (output t ofs) false = value v t := by
  induction t generalizing w ofs with
  | leaf i => exact hw i
  | join b l r ihl ihr =>
    let wl := (emit l ofs).foldl step w
    let wr := (emit r (ofs + cost l)).foldl step wl
    have hl : wl.length = ofs + cost l := by simp [wl, length_eval, hlen, length_emit]
    have hr : wr.length = ofs + cost l + cost r := by simp [wr, length_eval, hl, length_emit]
    have ho : output l ofs < wl.length := by rw [hl]; exact output_bound l ofs hbase
    have hleft : wr.getD (output l ofs) false = value v l := by
      unfold wr; rw [low_eval _ _ _ ho]; exact ihl w ofs hlen hbase hw
    have hright : wr.getD (output r (ofs + cost l)) false = value v r := by
      apply ihr wl _ hl (by omega)
      intro i; unfold wl; rw [low_eval]; exact hw i; omega
    change ((emit l ofs ++ emit r (ofs+cost l) ++ [_]).foldl step w).getD _ false = _
    rw [List.foldl_append, List.foldl_append]
    change (wr ++ [_]).getD (ofs + cost l + cost r) false = _
    rw [← hr]
    have last (z : Bool) : (wr ++ [z]).getD wr.length false = z := by
      simp [List.getD_eq_getElem?_getD]
    rw [last]
    simp only [List.getD_eq_getElem?_getD] at hleft hright
    dsimp only [wr, wl] at hleft hright
    cases b <;> simp [value, GateOp.eval, hleft, hright]

private def termFixed (i : Fin k) : Expr ((k+2)+(k+1)) :=
  .join true (.leaf (Fin.castAdd (k+1) i.castSucc.castSucc)) (.leaf (Fin.natAdd (k+2) i.castSucc))
private def termPair (i j : Fin k) : Expr ((k+2)+(k+1)) :=
  .join true (.join false (.leaf (Fin.castAdd (k+1) i.castSucc.castSucc)) (.leaf (Fin.natAdd (k+2) j.castSucc)))
    (.join false (.leaf (Fin.castAdd (k+1) j.castSucc.castSucc)) (.leaf (Fin.natAdd (k+2) i.castSucc)))
private noncomputable def parts (p : Equiv.Perm (Fin k)) : List (Expr ((k+2)+(k+1))) :=
  (fixed p).toList.map termFixed ++ (lower p).toList.map (fun i => termPair i (p i))

private theorem const_sum (l : List α) (n : ℕ) : (l.map fun _ => n).sum = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Nat.add_mul, Nat.add_comm]
private theorem count_parts {p : Equiv.Perm (Fin k)} (hp : Function.Involutive p) :
    ((parts p).map (fun t => cost t+1)).sum = 2*k := by
  simp only [parts, List.map_append, List.sum_append, List.map_map]
  change ((fixed p).toList.map (fun _ => 2)).sum + ((lower p).toList.map (fun _ => 4)).sum = 2*k
  rw [const_sum, const_sum]; simp only [Finset.length_toList]
  have := orbit_count hp; omega
private theorem fold_cost (ts : List (Expr n)) (t : Expr n) :
    cost (ts.foldl (.join false) t) + 1 = cost t + 1 + (ts.map fun u => cost u+1).sum := by
  induction ts generalizing t with
  | nil => simp
  | cons v ts ih => simp [ih, cost]; omega
private theorem fold_value (ts : List (Expr n)) (t : Expr n) (v : Fin n → Bool) :
    value v (ts.foldl (.join false) t) = true ↔ value v t = true ∨ ∃ u ∈ ts, value v u = true := by
  induction ts generalizing t with
  | nil => simp
  | cons u ts ih => simp only [List.foldl_cons, ih, value, Bool.false_eq_true, ite_false, Bool.or_eq_true, List.mem_cons]; grind

private def vals (x : Fin a → Bool) (y : Fin b → Bool) (i : Fin (a+b)) : Bool :=
  (List.ofFn x ++ List.ofFn y).getD i.val false

private theorem val_row (x : Fin a → Bool) (y : Fin b → Bool) (i : Fin a) : vals x y (Fin.castAdd b i) = x i := by
  have h : i.val < (List.ofFn x).length := by simp
  simp [vals,List.getD_eq_getElem?_getD,List.getElem?_append_left h,i.isLt]

private theorem val_col (x : Fin a → Bool) (y : Fin b → Bool) (i : Fin b) : vals x y (Fin.natAdd a i) = y i := by
  simp [vals,List.getD_eq_getElem?_getD,i.isLt]

private theorem block_values {p : Equiv.Perm (Fin k)} (hp : Function.Involutive p)
    (x : Fin (k+2) → Bool) (y : Fin (k+1) → Bool) :
    (∃ u ∈ parts p, value (vals x y) u = true) ↔ Accepted p (fun i => x i.castSucc.castSucc) (fun i => y i.castSucc) := by
  rw [blocks hp]; simp only [parts, List.mem_append, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨u, ⟨i,hi,rfl⟩|⟨i,hi,rfl⟩, h⟩
    · exact Or.inl ⟨i,hi, by simpa [termFixed,value,val_row,val_col] using h⟩
    · exact Or.inr ⟨i,hi, by simpa [termPair,value,crossBlock,val_row,val_col] using h⟩
  · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
    · exact ⟨_,Or.inl ⟨i,hi,rfl⟩, by simpa [termFixed,value,val_row,val_col] using h⟩
    · exact ⟨_,Or.inr ⟨i,hi,rfl⟩, by simpa [termPair,value,crossBlock,val_row,val_col] using h⟩

def crownForm (p : Equiv.Perm (Fin k)) (x : Fin (k+2) → Bool) (y : Fin (k+1) → Bool) : Bool :=
  !(x (Fin.last (k+1)) || decide (∃ i : Fin k,
    (x i.castSucc.castSucc = true ∧ y i.castSucc = true) ∨
    (p i ≠ i ∧ ((x i.castSucc.castSucc = true ∧ x (p i).castSucc.castSucc = true) ∨
      (y i.castSucc = true ∧ y (p i).castSucc = true)))))

private theorem one_each (p : Equiv.Perm (Fin k)) (u : Fin (k+2)) (v : Fin (k+1)) :
    crownForm p (fun i => decide (i=u)) (fun j => decide (j=v)) =
      decide (u.val ≠ k+1 ∧ ¬(u.val<k ∧ u.val=v.val)) := by
  have accepted : Accepted p (fun i => decide (i.castSucc.castSucc = u)) (fun i => decide (i.castSucc = v)) ↔ u.val<k ∧ u.val=v.val := by
    simp only [Accepted,decide_eq_true_eq]
    constructor
    · rintro ⟨i,⟨l,r⟩ | ⟨hn,⟨a,b⟩ | ⟨a,b⟩⟩⟩
      · have l := congrArg Fin.val l; have r := congrArg Fin.val r
        simp only [Fin.val_castSucc] at l r
        exact ⟨l ▸ i.isLt,l.symm.trans r⟩
      · exact (hn (Fin.ext (congrArg (fun z : Fin (k+2) => z.val) (b.trans a.symm)))).elim
      · exact (hn (Fin.ext (congrArg (fun z : Fin (k+1) => z.val) (b.trans a.symm)))).elim
    · rintro ⟨lt,eq⟩; exact ⟨⟨u.val,lt⟩,Or.inl ⟨Fin.ext rfl,Fin.ext eq⟩⟩
  have last : (Fin.last (k+1) = u) ↔ u.val=k+1 := ⟨fun e => (congrArg Fin.val e).symm,fun e => Fin.ext e.symm⟩
  apply Bool.eq_iff_iff.mpr
  simp only [crownForm,Bool.not_eq_true', Bool.or_eq_false_iff,decide_eq_false_iff_not,decide_eq_true_eq,last]
  apply and_congr Iff.rfl
  simpa only [Accepted,decide_eq_true_eq] using not_congr accepted

theorem crownInjective {p q : Equiv.Perm (Fin k)} (hp : Function.Involutive p) (hq : Function.Involutive q)
    (h : ∀ x y, crownForm p x y = crownForm q x y) : p=q := by
  apply recover hp hq
  intro x y
  have probe := h (Fin.snoc (Fin.snoc x false) false) (Fin.snoc y false)
  simpa [crownForm,Accepted] using (Bool.eq_iff_iff.mp (congrArg Bool.not probe))

theorem crownRealize (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    ∃ C : Circuit, FanInTwo C ∧ PEqualNP.Represents.Represents
      (fun (i : Fin (k+2)) (j : Fin (k+1)) => decide (i.val ≠ k+1 ∧ ¬(i.val<k ∧ i.val=j.val))) C ∧
      C.size ≤ 2*k+1 ∧ ∀ x y, crownForm p x y = C.eval (List.ofFn x ++ List.ofFn y) := by
  let n := (k+2)+(k+1)
  let flag : Expr n := .leaf (Fin.castAdd (k+1) (Fin.last (k+1)))
  let expr := (parts p).foldl (.join false) flag
  let ng : Gate := ⟨GateOp.not,[output expr n]⟩
  let C : Circuit := ⟨emit expr n ++ [ng], n+cost expr⟩
  have sz : cost expr = 2*k := by
    have h := fold_cost (parts p) flag
    rw [count_parts hp] at h
    change cost expr + 1 = 0+1+2*k at h
    omega
  have correct (x : Fin (k+2) → Bool) (y : Fin (k+1) → Bool) : crownForm p x y = C.eval (List.ofFn x ++ List.ofFn y) := by
    let xs := List.ofFn x ++ List.ofFn y
    let ws := (emit expr n).foldl step xs
    have hl : xs.length = n := by simp [xs,n]; omega
    have wl : ws.length=n+cost expr := by simp [ws,length_eval,hl,length_emit]
    have ev : ws.getD (output expr n) false = value (vals x y) expr := emit_eval expr _ xs n hl le_rfl (fun _ => rfl)
    have pos : value (vals x y) expr = (x (Fin.last (k+1)) || decide (∃ i : Fin k,
      (x i.castSucc.castSucc = true ∧ y i.castSucc = true) ∨ (p i ≠ i ∧ ((x i.castSucc.castSucc = true ∧ x (p i).castSucc.castSucc = true) ∨ (y i.castSucc = true ∧ y (p i).castSucc = true))))) := by
      apply Bool.eq_iff_iff.mpr
      simp only [expr,fold_value,flag,value,val_row,Bool.or_eq_true,decide_eq_true_eq]
      exact or_congr Iff.rfl (block_values hp x y)
    change crownForm p x y = ((emit expr n ++ [ng]).foldl step xs).getD (n+cost expr) false
    rw [List.foldl_append]
    change crownForm p x y = (ws ++ [!(ws.getD (output expr n) false)]).getD (n+cost expr) false
    rw [← wl]
    simp [List.getD_eq_getElem?_getD] at ev ⊢
    rw [ev,pos]
    rfl
  refine ⟨C,?_,?_,?_,correct⟩
  · intro g hg
    change g ∈ emit expr n ++ [ng] at hg
    rcases List.mem_append.mp hg with old | last
    · have ⟨op,bnd⟩ := legal expr n g old
      exact ⟨by simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢; tauto,bnd⟩
    · have eq := List.mem_singleton.mp last; subst g; simp [ng]
  · intro i j
    exact (correct (fun u => decide (u=i)) (fun v => decide (v=j))).symm.trans (one_each p i j)
  · change (emit expr n ++ [ng]).length ≤ 2*k+1
    simp [length_emit,sz]

end Converse
namespace Split
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def runStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

private theorem run_length (gs : List Gate) (w : List Bool) : (gs.foldl runStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,runStep]; omega

private theorem final_eval {C : Circuit} {gs : List Gate} {g : Gate} (eq : C.gates = gs++[g])
    {n : Nat} (out : C.output = n+gs.length) (w : List Bool) (lw : w.length = n) :
    C.eval w = g.op.eval (g.inputs.map fun i => (gs.foldl runStep w).getD i false) := by
  change (C.gates.foldl runStep w).getD C.output false = _
  rw [out,eq,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have len := run_length gs w
  rw [lw] at len
  simp [runStep,← len,List.getD_append_right]

theorem split_signed {k : Nat} (C : Circuit) (legal : FanInTwo C)
    (repr : Represents (fun (i : Fin (k+2)) (j : Fin (k+1)) => decide (i.val ≠ k+1 ∧ ¬ (i.val<k ∧ i.val=j.val))) C)
    (bound : C.size ≤ 2*k+1) (positive : 0<C.size)
    (out : C.output+1=(2*k+3)+C.size)
    (terminal : ∀ g : Fin C.size, (NestedCover.gateAt C g.val).op=.not ↔ g.val+1=C.size) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 2*k ∧
      Represents (fun (i : Fin (k+2)) (j : Fin (k+1)) => decide (i.val=k+1 ∨ (i.val<k ∧ i.val=j.val))) D ∧
      ∀ w : List Bool, w.length=(k+2)+(k+1) → C.eval w = !D.eval w := by
  have nonnil : C.gates ≠ [] := by rintro e; simp [Circuit.size,e] at positive
  let gs := C.gates.dropLast
  let g := C.gates.getLast nonnil
  have eq : C.gates = gs++[g] := (List.dropLast_append_getLast nonnil).symm
  have len : C.size = gs.length+1 := by simp [Circuit.size,eq]
  have out' : C.output = (k+2)+(k+1)+gs.length := by omega
  have lastop : g.op=.not := by
    have h := (terminal ⟨gs.length,by omega⟩).mpr (by simpa using len.symm)
    simpa [NestedCover.gateAt,eq,List.getD_append_right] using h
  have nempty : g.inputs ≠ [] := by
    intro empty
    let i : Fin (k+2) := ⟨k+1,by omega⟩
    let j : Fin (k+1) := ⟨0,by omega⟩
    have e := final_eval eq out' (oneEach i j) (by simp [oneEach]; omega)
    rw [repr i j] at e
    simp [i,lastop,empty,GateOp.eval] at e
  obtain ⟨src,rest,inp⟩ := List.exists_cons_of_ne_nil nempty
  let D : Circuit := ⟨gs,src⟩
  have Eval (w : List Bool) (lw : w.length=(k+2)+(k+1)) : C.eval w = !D.eval w := by
    rw [final_eval eq out' w lw,inp,lastop]; rfl
  refine ⟨D,?_,?_,?_,Eval⟩
  · intro gg mem
    change gg ∈ gs at mem
    have ⟨allowed,arity⟩ := legal gg (by rw [eq]; exact List.mem_append_left [g] mem)
    obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp mem
    have atI : NestedCover.gateAt C i = gg := by
      rw [NestedCover.gateAt,eq,List.getD_eq_getElem _ _ (by simp;omega),List.getElem_append_left hi,ei]
    have nd : gg.op ≠ .not := by
      intro E
      have impossible : i+1=C.size := (terminal ⟨i,by omega⟩).mp (atI ▸ E)
      omega
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at allowed ⊢
    exact ⟨allowed.elim Or.inl (fun z => Or.inr (z.resolve_right nd)),arity⟩
  · change gs.length ≤ 2*k; omega
  · intro i j
    have e := Eval (oneEach i j) (by simp [oneEach]; omega)
    rw [repr i j] at e
    change decide (i.val ≠ k+1 ∧ ¬ (i.val<k ∧ i.val=j.val)) = !D.eval (oneEach i j) at e
    have de : D.eval (oneEach i j) = !decide (i.val ≠ k+1 ∧ ¬ (i.val<k ∧ i.val=j.val)) := by rw [e]; simp
    change D.eval (oneEach i j)=decide _
    rw [de]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq]
    tauto

end Split
end PEqualNP.Outside.L_meta_29940
open PEqualNP.Outside.L_meta_29940 in
theorem PEqualNP.Outside.L_meta_29940 : ∀ (k : Nat), 7 ≤ k →
  let A := fun (i : Fin (k+2)) (j : Fin (k+1)) =>
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val))
  let Ext := { f : (Fin (k+2) → Bool) → (Fin (k+1) → Bool) → Bool //
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents A C ∧ C.size ≤ 2*k+1 ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y) }
  let Inv := { perm : Equiv.Perm (Fin k) // Function.Involutive perm }
  ∃ bij : Inv ≃ Ext, ∀ (p : Inv) x y,
    (bij p).val x y = !(x (Fin.last (k+1)) || decide (∃ i : Fin k,
        (x (i.castSucc.castSucc) = true ∧ y (i.castSucc) = true) ∨
        (p.val i ≠ i ∧ ((x (i.castSucc.castSucc) = true ∧ x ((p.val i).castSucc.castSucc) = true) ∨
          (y (i.castSucc) = true ∧ y ((p.val i).castSucc) = true))))) := by
  classical
  intro k hk
  dsimp only
  let Inv := {p : Equiv.Perm (Fin k) // Function.Involutive p}
  let A := fun (i : Fin (k+2)) (j : Fin (k+1)) => decide (i.val≠k+1 ∧ ¬(i.val<k ∧ i.val=j.val))
  let Ext := {f : (Fin (k+2) → Bool) → (Fin (k+1) → Bool) → Bool //
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents A C ∧
      C.size ≤ 2*k+1 ∧ ∀ x y, f x y=C.eval (List.ofFn x ++ List.ofFn y)}
  let F : Inv → Ext := fun p => ⟨Converse.crownForm p.val,Converse.crownRealize p.val p.property⟩
  have injective : Function.Injective F := by
    intro p q e
    apply Subtype.ext
    apply Converse.crownInjective p.property q.property
    intro x y
    exact congrArg (fun f : Ext => f.val x y) e
  have surjective : Function.Surjective F := by
    intro f
    obtain ⟨C,hf,hr,sz,ev⟩ := f.property
    have lower := Z.Equality.optimum k hk C hf hr
    have out := Z.Equality.last_output k hk C hf hr sz
    have term := Z.Equality.last_not k hk C hf hr sz
    have out' : C.output+1=(2*k+3)+C.size := by simpa only [Z.Equality.base,show k+2+(k+1)=2*k+3 by omega] using out
    obtain ⟨D,mono,bound,rep,neg⟩ := Split.split_signed C hf hr sz (by omega) out' term
    obtain ⟨p,hp,pos⟩ := S.core_class (by omega) D (fun g hg => mono g hg) rep bound
    refine ⟨⟨p,hp⟩,Subtype.ext ?_⟩
    funext x y
    change Converse.crownForm p x y=f.val x y
    rw [ev x y,neg _ (by simp;omega),pos x y]
    rfl
  exact ⟨Equiv.ofBijective F ⟨injective,surjective⟩,fun p x y => rfl⟩
