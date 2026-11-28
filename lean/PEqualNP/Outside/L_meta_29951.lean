import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29951
namespace Foundation.Support

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

end Foundation.Support

namespace Foundation.Support
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
end Foundation.Support
namespace Foundation.Support.IdentityClass

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

end Foundation.Support.IdentityClass
namespace Foundation.Support.IdentityClass

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

end Foundation.Support.IdentityClass

namespace Foundation.Support
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem class_from_extraction {k : Nat} (hk : 2 ≤ k) (c : Circuit)
    (rep : Represents (fun i j : Fin k => decide (i=j)) c)
    (t : NatTree) (vars : t.vars = Finset.range (2*k)) (once : t.once)
    (ev : ∀ w : List Bool, w.length=2*k → t.eval (fun i => w.getD i false) = c.eval w) :
    ∃ p : Equiv.Perm (Fin k), Function.Involutive p ∧ ∀ x y : Fin k → Bool,
      c.eval (List.ofFn x ++ List.ofFn y) = decide (∃ i : Fin k,
         (x i = true ∧ y i = true) ∨ (p i ≠ i ∧
          ((x i = true ∧ x (p i) = true) ∨ (y i = true ∧ y (p i) = true)))) := by
  classical
  have mat (a b : Fin k) : t.eval (IdentityClass.cell a b) = decide (a=b) := by
    apply Eq.trans _ (rep a b)
    rw [← ev _ (by simp [oneEach]; omega)]
    apply t.eval_congr; intro n _
    apply Bool.eq_iff_iff.mpr
    rw [pairRead]
    simp [IdentityClass.cell,IdentityClass.lights]
  obtain ⟨p,hp,form⟩ := IdentityClass.root_form hk t once vars mat
  refine ⟨p,hp,?_⟩
  intro x y
  let I := List.ofFn x ++ List.ofFn y
  have row (i : Fin k) : I.getD i.val false = x i := by
    dsimp [I]; rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp)]
    simp
  have col (i : Fin k) : I.getD (k+i.val) false = y i := by
    dsimp [I]; rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simp)]
    simp
  change c.eval I = _
  rw [← ev _ (by simp [I]; omega)]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,IdentityClass.Hit,row,col] using form (fun n => I.getD n false)

theorem equality_class_exists {k : Nat} (hk : 2 ≤ k) (c : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 c) (budget : c.size+1 ≤ 2*k)
    (rep : Represents (fun i j : Fin k => decide (i=j)) c) :
    ∃ p : Equiv.Perm (Fin k), Function.Involutive p ∧ ∀ x y : Fin k → Bool,
      c.eval (List.ofFn x ++ List.ofFn y) = decide (∃ i : Fin k,
         (x i = true ∧ y i = true) ∨ (p i ≠ i ∧
          ((x i = true ∧ x (p i) = true) ∨ (y i = true ∧ y (p i) = true)))) := by
  obtain ⟨t,vars,once,ev⟩ := identityTree hk c hm budget rep
  exact class_from_extraction hk c rep t vars once ev

end Foundation.Support

namespace Foundation.Construction

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

private def termFixed (i : Fin k) : Expr (k+k) :=
  .join true (.leaf (Fin.castAdd k i)) (.leaf (Fin.natAdd k i))
private def termPair (i j : Fin k) : Expr (k+k) :=
  .join true (.join false (.leaf (Fin.castAdd k i)) (.leaf (Fin.natAdd k j)))
    (.join false (.leaf (Fin.castAdd k j)) (.leaf (Fin.natAdd k i)))
private noncomputable def parts (p : Equiv.Perm (Fin k)) : List (Expr (k+k)) :=
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

private def bankVal (x y : Fin k → Bool) (i : Fin (k+k)) : Bool := (List.ofFn x ++ List.ofFn y).getD i.val false
private theorem bank_left (x y : Fin k → Bool) (i : Fin k) : bankVal x y (Fin.castAdd k i) = x i := by
  have h : i.val < (List.ofFn x).length := by simp
  simp [bankVal, List.getD_eq_getElem?_getD, List.getElem?_append_left h, i.isLt]
private theorem bank_right (x y : Fin k → Bool) (i : Fin k) : bankVal x y (Fin.natAdd k i) = y i := by
  simp [bankVal, List.getD_eq_getElem?_getD, i.isLt]
private theorem bank_addNat (x y : Fin k → Bool) (i : Fin k) : bankVal x y (i.addNat k) = y i := by
  simpa only [Fin.natAdd_eq_addNat] using bank_right x y i
private theorem parts_iff {p : Equiv.Perm (Fin k)} (hp : Function.Involutive p) (x y : Fin k → Bool) :
    (∃ u ∈ parts p, value (bankVal x y) u = true) ↔ Accepted p x y := by
  rw [blocks hp]; simp only [parts, List.mem_append, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨u, ⟨i,hi,rfl⟩|⟨i,hi,rfl⟩, h⟩
    · exact Or.inl ⟨i,hi, by simpa [termFixed,value,bank_left,bank_addNat] using h⟩
    · exact Or.inr ⟨i,hi, by simpa [termPair,value,crossBlock,bank_left,bank_addNat] using h⟩
  · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
    · exact ⟨_,Or.inl ⟨i,hi,rfl⟩, by simpa [termFixed,value,bank_left,bank_addNat] using h⟩
    · exact ⟨_,Or.inr ⟨i,hi,rfl⟩, by simpa [termPair,value,crossBlock,bank_left,bank_addNat] using h⟩
private theorem oneEach_iff (p : Equiv.Perm (Fin k)) (u v : Fin k) :
    Accepted p (fun i => decide (i=u)) (fun i => decide (i=v)) ↔ u=v := by
  simp only [Accepted, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi,hj⟩ | ⟨hneq, ⟨hi,hj⟩ | ⟨hi,hj⟩⟩⟩
    · exact hi.symm.trans hj
    · exact (hneq (hj.trans hi.symm)).elim
    · exact (hneq (hj.trans hi.symm)).elim
  · rintro rfl; exact ⟨u, Or.inl ⟨rfl,rfl⟩⟩

private theorem realize {p : Equiv.Perm (Fin k)} (hk : 2 ≤ k) (hp : Function.Involutive p) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = 2*k ∧
      PEqualNP.Represents.Represents (fun i j : Fin k => decide (i=j)) C ∧
      ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = true ↔ Accepted p x y := by
  have weight := count_parts hp
  cases h : parts p with
  | nil => rw [h] at weight; simp at weight; omega
  | cons t ts =>
    let expr := ts.foldl (.join false) t
    let C : Circuit := ⟨emit expr (k+k), output expr (k+k)⟩
    have hsize : C.size+1 = 2*k := by
      change (emit expr (k+k)).length+1 = _; rw [length_emit, fold_cost]
      simpa [h, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using weight
    have he (x y : Fin k → Bool) : C.eval (List.ofFn x ++ List.ofFn y) = true ↔ Accepted p x y := by
      have hv := emit_eval expr (bankVal x y) (List.ofFn x ++ List.ofFn y) (k+k) (by simp) le_rfl (fun _ => rfl)
      change ((emit expr (k+k)).foldl step _).getD (output expr (k+k)) false = true ↔ _
      rw [hv, fold_value, ← parts_iff hp, h]; simp
    refine ⟨C, legal expr _, hsize, ?_, he⟩
    intro i j
    apply Bool.eq_iff_iff.mpr
    simpa [PEqualNP.Represents.oneEach] using (he (fun a => decide (a=i)) (fun a => decide (a=j))).trans (oneEach_iff p i j)

end Foundation.Construction

open PEqualNP.Outside.L_meta_29951.Foundation.Construction in
theorem Foundation : ∀ (k : Nat), 2 ≤ k → ∀ f : (Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
  ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
    ∀ x y, f x y = decide (∃ i : Fin k,
        (x i = true ∧ y i = true) ∨
        (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
          (y i = true ∧ y (p i) = true)))) := by
  intro k hk f
  constructor
  · rintro ⟨c, hm, hs, rep, hf⟩
    obtain ⟨p, hi, h⟩ := PEqualNP.Outside.L_meta_29951.Foundation.Support.equality_class_exists hk c hm hs rep
    have form : ∀ x y, f x y = _ := fun x y => (hf x y).trans (h x y)
    refine ⟨p, ⟨hi, form⟩, ?_⟩
    rintro q ⟨hq, fq⟩
    apply recover hq hi
    intro x y
    have fromq : f x y = true ↔ Accepted q x y := by rw [fq]; simp only [Accepted, decide_eq_true_eq]
    have fromp : f x y = true ↔ Accepted p x y := by rw [form]; simp only [Accepted, decide_eq_true_eq]
    exact fromq.symm.trans fromp
  · rintro ⟨p, ⟨hi, form⟩, _⟩
    obtain ⟨c, hm, size, rep, correct⟩ := realize hk hi
    refine ⟨c, hm, size.le, rep, ?_⟩
    intro x y
    apply Bool.eq_iff_iff.mpr
    rw [form]
    simpa only [Accepted, decide_eq_true_eq] using (correct x y).symm

namespace FunctionSide
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_29951.Foundation.Construction

private abbrev GoodPerm (k : Nat) := {p : Equiv.Perm (Fin k) // Function.Involutive p}
private def pfn (p : GoodPerm k) (x y : Fin k → Bool) : Bool :=
  decide (∃ i : Fin k, (x i = true ∧ y i = true) ∨ (p.val i ≠ i ∧
    ((x i = true ∧ x (p.val i) = true) ∨ (y i = true ∧ y (p.val i) = true))))
private abbrev Eligible {k q : Nat} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :=
  {f : (Fin k → Bool) → (Fin k → Bool) → Bool //
    (∃ C : Circuit, Monotone2 C ∧ C.size+1 ≤ 2*k ∧
      PEqualNP.Represents.Represents (fun i j : Fin k => decide (i=j)) C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧ ∀ a, f (X a) (Y a) = label a}
private abbrev Consistent {k q : Nat} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :=
  {p : GoodPerm k // ∀ a, pfn p (X a) (Y a) = label a}

private def produce {k q} (hk : 2 ≤ k) (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool)
    (p : Consistent X Y label) : Eligible X Y label := by
  refine ⟨pfn p.1, ?_, p.property⟩
  obtain ⟨c, hm, hc, hr, he⟩ := realize hk p.1.2
  refine ⟨c, hm, hc.le, hr, ?_⟩
  intro x y
  apply Bool.eq_iff_iff.mpr
  simpa only [pfn, decide_eq_true_eq, Accepted] using (he x y).symm

private theorem inject {k q} (hk : 2 ≤ k) (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :
    Function.Injective (produce hk X Y label) := by
  intro p q h
  apply Subtype.ext; apply Subtype.ext
  apply recover p.1.2 q.1.2
  intro x y
  have hh : pfn p.1 x y = pfn q.1 x y := congrArg (fun f : Eligible X Y label => f.val x y) h
  have iffBool : pfn p.1 x y = true ↔ pfn q.1 x y = true := by rw [hh]
  simpa only [pfn, Accepted, decide_eq_true_eq] using iffBool

private theorem surject {k q} (hk : 2 ≤ k) (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :
    Function.Surjective (produce hk X Y label) := by
  intro f
  obtain ⟨p, ⟨hi, form⟩, _⟩ := (PEqualNP.Outside.L_meta_29951.Foundation k hk f.val).mp f.property.1
  let π : GoodPerm k := ⟨p,hi⟩
  have form2 (x y) : f.val x y = pfn π x y := form x y
  refine ⟨⟨π, fun a => (form2 (X a) (Y a)).symm.trans (f.property.2 a)⟩, ?_⟩
  apply Subtype.ext; funext x y; exact (form2 x y).symm

noncomputable def permFs {k q} (hk : 2 ≤ k) (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :
    Consistent X Y label ≃ Eligible X Y label :=
  Equiv.ofBijective (produce hk X Y label) ⟨inject hk X Y label, surject hk X Y label⟩

theorem permFs_apply {k q} (hk : 2 ≤ k) (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool)
    (p : Consistent X Y label) (x y : Fin k → Bool) :
    (permFs hk X Y label p).val x y = pfn p.val x y := rfl

end FunctionSide

namespace Encoding

abbrev V (k q : Nat) := (Fin k × Fin k) ⊕ ((Fin k × Fin (k+1)) ⊕ (Fin q × Fin (k*k+1)))
def edge {k q : Nat} (i j : Fin k) : V k q := Sum.inl (i,j)
def row {k q : Nat} (i : Fin k) (s : Fin (k+1)) : V k q := Sum.inr (Sum.inl (i,s))
def step {k q : Nat} (a : Fin q) (s : Fin (k*k+1)) : V k q := Sum.inr (Sum.inr (a,s))
def across {k q : Nat} (b : V k q → Bool) (i j : Fin k) :=
  if i < j then b (edge i j) else b (edge j i)
abbrev used {k} (x y : Fin k → Bool) (i j : Fin k) :=
  (x i = true ∧ x j = true) ∨ (y i = true ∧ y j = true)
def diagonal {k} (x y : Fin k → Bool) := decide (∃ i, x i = true ∧ y i = true)
def atPos {k q} (b : V k q → Bool) (X Y : Fin q → Fin k → Bool) (a : Fin q) (t : Fin (k*k)) :=
  decide (∃ i j : Fin k, i.val*k+j.val = t.val ∧ i < j ∧ used (X a) (Y a) i j ∧ b (edge i j)=true)
def Valid {k q} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) (b : V k q → Bool) : Prop :=
  (∀ i j, j ≤ i → b (edge i j) = false) ∧
  (∀ i, b (row i 0) = false) ∧
  (∀ i j, b (row i j.succ) = (b (row i j.castSucc) || across b i j) ∧
    ¬ (b (row i j.castSucc) = true ∧ across b i j = true)) ∧
  (∀ a, b (step a 0) = diagonal (X a) (Y a) ∧ b (step a (Fin.last (k*k))) = label a) ∧
  (∀ a t, b (step a t.succ) = (b (step a t.castSucc) || atPos b X Y a t))
def result {k q} (b : V k q → Bool) (x y : Fin k → Bool) :=
  diagonal x y || decide (∃ i j : Fin k, i<j ∧ b (edge i j)=true ∧ used x y i j)

end Encoding

namespace Encoding

abbrev Inv (k : Nat) := {p : Equiv.Perm (Fin k) // Function.Involutive p}

def permValue {k} (p : Inv k) (x y : Fin k → Bool) : Bool := decide (∃ i : Fin k,
  (x i=true ∧ y i=true) ∨ (p.val i≠i ∧
    ((x i=true ∧ x (p.val i)=true) ∨ (y i=true ∧ y (p.val i)=true))))

abbrev Good {k q : Nat} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :=
  {p : Inv k // ∀ a, permValue p (X a) (Y a) = label a}

def permEdge {k} (p : Inv k) (i j : Fin k) := decide (i<j ∧ p.val i=j)

def symEdge {k} (e : Fin k → Fin k → Bool) (i j : Fin k) := if i<j then e i j else e j i

theorem flip_eq {k} (p : Inv k) {i j : Fin k} : p.val i=j ↔ p.val j=i :=
  ⟨fun e => e ▸ p.property i,fun e => e ▸ p.property j⟩

theorem sym_perm {k} (p : Inv k) (i j : Fin k) :
    symEdge (permEdge p) i j = true ↔ i≠j ∧ p.val i=j := by
  rcases lt_trichotomy i j with h|h|h
  · simp [symEdge,permEdge,h,h.ne]
  · subst j; simp [symEdge,permEdge]
  · have ne := Ne.symm h.ne
    simp [symEdge,permEdge,h.not_gt,h,ne,flip_eq p (i:=j) (j:=i)]

theorem sym_comm {k} (e : Fin k → Fin k → Bool) (i j : Fin k) : symEdge e i j = symEdge e j i := by
  rcases lt_trichotomy i j with h|h|h
  · simp [symEdge,h,h.not_gt]
  · subst j; rfl
  · simp [symEdge,h,h.not_gt]

def IsMatching {k} (e : Fin k → Fin k → Bool) : Prop :=
  (∀ i j, j ≤ i → e i j = false) ∧
  (∀ i j h, symEdge e i j = true → symEdge e i h = true → j=h)

noncomputable def matchInv {k} (e : Fin k → Fin k → Bool) (mat : IsMatching e) : Inv k := by
  classical
  let f (i : Fin k) := if h : ∃ j, symEdge e i j = true then h.choose else i
  have only (i j : Fin k) (h : symEdge e i j = true) : f i=j := by
    have ex : ∃ u, symEdge e i u = true := ⟨j,h⟩
    simp only [f,dif_pos ex]; exact mat.2 _ _ _ ex.choose_spec h
  have inv : Function.Involutive f := by
    intro i
    by_cases h : ∃ j, symEdge e i j = true
    · obtain ⟨j,h⟩ := h
      rw [only _ _ h,only _ _ (by rw [sym_comm]; exact h : symEdge e j i = true)]
    · simp [f,h]
  exact ⟨⟨f,f,inv,inv⟩,inv⟩

theorem matchInv_apply {k} (e : Fin k → Fin k → Bool) (mat : IsMatching e) (i : Fin k) :
    (matchInv e mat).val i = if h : ∃ j, symEdge e i j = true then h.choose else i := by
  classical
  rfl

theorem matchInv_sym {k} (e : Fin k → Fin k → Bool) (mat : IsMatching e) (i j : Fin k) :
    symEdge e i j = true ↔ i ≠ j ∧ (matchInv e mat).val i = j := by
  classical
  rw [matchInv_apply]
  by_cases ex : ∃ j, symEdge e i j = true
  · simp only [dif_pos ex]
    constructor
    · intro h
      refine ⟨?_,mat.2 _ _ _ ex.choose_spec h⟩
      rintro rfl; simpa [symEdge,mat.1 i i le_rfl] using h
    · rintro ⟨_,rfl⟩; exact ex.choose_spec
  · simp only [dif_neg ex]
    have bad : symEdge e i j ≠ true := fun hit => ex ⟨_,hit⟩
    tauto

theorem edge_inverse {k} (e : Fin k → Fin k → Bool) (mat : IsMatching e) :
    permEdge (matchInv e mat) = e := by
  funext i j
  by_cases lt : i<j
  · apply Bool.eq_iff_iff.mpr
    simpa [symEdge,permEdge,lt,lt.ne] using (matchInv_sym e mat i j).symm
  · simp [permEdge,lt,mat.1 i j (le_of_not_gt lt)]

theorem permEdge_injective {k} : Function.Injective (@permEdge k) := by
  intro p q eq
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hh (j : Fin k) : (i≠j ∧ p.val i=j) ↔ (i≠j ∧ q.val i=j) := by
    rw [← sym_perm p, ← sym_perm q,eq]
  by_cases mov : i ≠ p.val i
  · exact ((hh _).mp ⟨mov,rfl⟩).2.symm
  · have fixed : p.val i=i := (not_ne_iff.mp mov).symm
    by_contra neq
    have qmov : i ≠ q.val i := by simpa only [fixed] using neq
    exact neq ((hh _).mpr ⟨qmov,rfl⟩).2

def scanBits {n} (mask : Fin n → Bool) (s : Fin (n+1)) := decide (∃ i, i.val < s.val ∧ mask i=true)

theorem prefix0 {n} (bits : Fin n → Bool) : scanBits bits 0 = false := by simp [scanBits]

theorem prefixNext {n} (bits : Fin n → Bool) (s : Fin n) :
    scanBits bits s.succ = (scanBits bits s.castSucc || bits s) := by
  apply Bool.eq_iff_iff.mpr
  simp only [scanBits,decide_eq_true_eq,Fin.val_succ,Fin.val_castSucc,Bool.or_eq_true]
  constructor
  · rintro ⟨j,hj,hb⟩; by_cases e : j=s
    · exact Or.inr (e ▸ hb)
    · exact Or.inl ⟨j,by have ne := Fin.val_ne_of_ne e; omega,hb⟩
  · rintro (⟨j,hj,hb⟩|hb)
    · exact ⟨j,by omega,hb⟩
    · exact ⟨s,by omega,hb⟩

theorem prefixLast {n} (bits : Fin n → Bool) :
    scanBits bits (Fin.last n) = true ↔ ∃ i, bits i=true := by
  simp [scanBits,Fin.val_last]

theorem forcedPrefix {n} (vals : Fin (n+1) → Bool) (bits : Fin n → Bool) (d : Bool)
    (zero : vals 0 = d) (next : ∀ i, vals i.succ = (vals i.castSucc || bits i)) :
    ∀ s, vals s = (d || scanBits bits s) := by
  intro s; induction s using Fin.induction with
  | zero => simp [zero,prefix0]
  | succ i ih => rw [next,ih,prefixNext,Bool.or_assoc]

end Encoding
namespace Encoding

def edgeOf {k q} (b : V k q → Bool) (i j : Fin k) := b (edge i j)
def markPos {k} (e : Fin k → Fin k → Bool) (x y : Fin k → Bool) (t : Fin (k*k)) :=
  decide (∃ i j : Fin k, i.val*k+j.val=t.val ∧ i<j ∧ used x y i j ∧ e i j=true)

def edgeValue {k} (e : Fin k → Fin k → Bool) (x y : Fin k → Bool) :=
  diagonal x y || decide (∃ i j : Fin k, i<j ∧ e i j=true ∧ used x y i j)

def putEdges {k q} (e : Fin k → Fin k → Bool) (X Y : Fin q → Fin k → Bool) : V k q → Bool
  | .inl (i,j) => e i j
  | .inr (.inl (i,s)) => scanBits (symEdge e i) s
  | .inr (.inr (a,s)) => diagonal (X a) (Y a) || scanBits (markPos e (X a) (Y a)) s

theorem row_forced {k q} {X Y : Fin q → Fin k → Bool} {label b} (vb : Valid X Y label b)
    (i : Fin k) (s : Fin (k+1)) : b (row i s) = scanBits (across b i) s := by
  have h := forcedPrefix (fun s => b (row i s)) (across b i) false (vb.2.1 i) (fun j => (vb.2.2.1 i j).1) s
  simpa using h

theorem step_forced {k q} {X Y : Fin q → Fin k → Bool} {label b} (vb : Valid X Y label b)
    (a : Fin q) (s : Fin (k*k+1)) :
    b (step a s) = (diagonal (X a) (Y a) || scanBits (atPos b X Y a) s) :=
  forcedPrefix (fun s => b (step a s)) (atPos b X Y a) (diagonal (X a) (Y a))
    (vb.2.2.2.1 a).1 (vb.2.2.2.2 a) s

theorem selected_matching {k q} {X Y : Fin q → Fin k → Bool} {label b} (vb : Valid X Y label b) :
    IsMatching (edgeOf b) := by
  refine ⟨vb.1,?_⟩
  intro i j h h1 h2
  have contr {a z : Fin k} (lt : a<z) (p : across b i a=true) (t : across b i z=true) : False := by
    apply (vb.2.2.1 i z).2
    refine ⟨?_,t⟩; rw [row_forced vb,scanBits,decide_eq_true_eq]
    exact ⟨a,lt,p⟩
  rcases lt_trichotomy j h with lt|eq|lt
  · exact (contr lt h1 h2).elim
  · exact eq
  · exact (contr lt h2 h1).elim

theorem put_unique {k q} {X Y : Fin q → Fin k → Bool} {label b} (vb : Valid X Y label b) :
    putEdges (edgeOf b) X Y = b := by
  funext idx
  rcases idx with ⟨i,j⟩|(⟨i,s⟩|⟨a,s⟩)
  · rfl
  · exact (row_forced vb i s).symm
  · exact (step_forced vb a s).symm

theorem last_value {k} (e : Fin k → Fin k → Bool) (x y : Fin k → Bool) :
    (diagonal x y || scanBits (markPos e x y) (Fin.last (k*k))) = edgeValue e x y := by
  unfold edgeValue
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [prefixLast,decide_eq_true_eq]
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨i,j,_,lt,u,h⟩ := of_decide_eq_true ht
    exact ⟨i,j,lt,h,u⟩
  · rintro ⟨i,j,lt,h,u⟩
    have b := Nat.mul_le_mul_right k (i.isLt : i.val+1 ≤ k)
    rw [Nat.succ_mul] at b
    have z : i.val*k+j.val < k*k := by have := j.isLt; omega
    exact ⟨⟨_,z⟩,decide_eq_true ⟨i,j,rfl,lt,u,h⟩⟩

theorem labels_from {k q} {X Y : Fin q → Fin k → Bool} {label b} (h : Valid X Y label b)
    (a : Fin q) : edgeValue (edgeOf b) (X a) (Y a) = label a := by
  rw [← last_value]
  exact (step_forced h a _).symm.trans (h.2.2.2.1 a).2

theorem put_valid {k q} {X Y : Fin q → Fin k → Bool} {label}
    (e : Fin k → Fin k → Bool) (m : IsMatching e)
    (fits : ∀ a, edgeValue e (X a) (Y a)=label a) : Valid X Y label (putEdges e X Y) := by
  refine ⟨m.1,fun i => prefix0 _,?_,?_,?_⟩
  · intro i j; refine ⟨prefixNext _ _,?_⟩
    change ¬(scanBits (symEdge e i) j.castSucc = true ∧ symEdge e i j = true)
    rintro ⟨old,new⟩; obtain ⟨h,lt,lit⟩ := of_decide_eq_true old
    have eq := m.2 i h j lit new
    exact (ne_of_lt (show h<j from lt)) eq
  · intro a; refine ⟨?_,(last_value _ _ _).trans (fits a)⟩
    change (diagonal _ _ || scanBits _ 0) = _
    simp [prefix0]
  · intro a t
    change (diagonal _ _ || scanBits (markPos e (X a) (Y a)) t.succ) = ((_ || scanBits _ t.castSucc) || _)
    rw [prefixNext,Bool.or_assoc]; rfl

theorem perm_is_matching {k} (p : Inv k) : IsMatching (permEdge p) := by
  refine ⟨?_,?_⟩
  · intro i j le; simp [permEdge,not_lt_of_ge le]
  · intro i j h hj hh; exact ((sym_perm _ _ _).mp hj).2.symm.trans ((sym_perm _ _ _).mp hh).2

theorem perm_value {k} (p : Inv k) (x y : Fin k → Bool) :
    edgeValue (permEdge p) x y = permValue p x y := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeValue,diagonal,permEdge,permValue,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro (⟨i,z⟩|⟨i,j,lt,⟨_,h⟩,u⟩)
    · exact ⟨i,.inl z⟩
    · subst j; exact ⟨i,.inr ⟨lt.ne',u⟩⟩
  · rintro ⟨i,(z|⟨ne,u⟩)⟩
    · exact Or.inl ⟨i,z⟩
    · right; rcases lt_or_gt_of_ne ne with lo|hi
      · refine ⟨p.val i,i,lo,⟨lo,p.property i⟩,?_⟩
        rcases u with z|z
        · exact Or.inl z.symm
        · exact Or.inr z.symm
      · exact ⟨i,p.val i,hi,⟨hi,rfl⟩,u⟩

def permBits {k q} {X Y : Fin q → Fin k → Bool} {label} (g : Good X Y label) :
    {b : V k q → Bool // Valid X Y label b} :=
  ⟨putEdges (permEdge g.val) X Y,put_valid _ (perm_is_matching g.val)
    (fun a => (perm_value _ _ _).trans (g.property a))⟩

theorem permBits_bijective {k q} {X Y : Fin q → Fin k → Bool} {label} :
    Function.Bijective (@permBits k q X Y label) := by
  constructor
  · intro p q eq
    apply Subtype.ext
    apply permEdge_injective
    funext i j
    exact congrArg (fun (b : {z : V k _ → Bool // Valid X Y label z}) => b.val (edge i j)) eq
  · intro b
    let e := edgeOf b.val
    have m : IsMatching e := selected_matching b.property
    let p := matchInv e m
    have pe : permEdge p = e := edge_inverse e m
    have fits (a : Fin _) : permValue p (X a) (Y a) = label a := by
      rw [← perm_value,pe]; exact labels_from b.property a
    refine ⟨⟨p,fits⟩,Subtype.ext ?_⟩
    change putEdges (permEdge p) X Y = b.val
    rw [pe]; exact put_unique b.property

noncomputable def matchingEquiv {k q} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :
    {b : V k q → Bool // Valid X Y label b} ≃ Good X Y label :=
  (Equiv.ofBijective _ permBits_bijective).symm

theorem matchingEquiv_value {k q} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool)
    (b : {b : V k q → Bool // Valid X Y label b}) (x y : Fin k → Bool) :
    permValue ((matchingEquiv X Y label) b).val x y = result b.val x y := by
  let e := matchingEquiv X Y label
  have h : permBits (e b) = b := e.symm_apply_apply b
  have v := congrArg (fun (z : {b : V k q → Bool // Valid X Y label b}) => result z.val x y) h
  exact (perm_value _ _ _).symm.trans v

end Encoding

namespace Encoding
namespace Cnf

abbrev Clause (α : Type*) := Finset (α × Bool)

def holds {α : Type*} (b : α → Bool) (c : Clause α) : Prop :=
  ∃ l ∈ c, b l.1 = l.2

variable {α : Type*} [DecidableEq α]

def unit (v : α) (p : Bool) : Clause α := {(v,p)}

def taut (v : α) : Clause α := {(v,false),(v,true)}

def gate (u v w : α) (t : Fin 3) : Clause α :=
  if t=0 then {(u,false),(w,true)}
  else if t=1 then {(v,false),(w,true)}
  else {(w,false),(u,true),(v,true)}

def splitGate (u v w : α) (t : Fin 4) : Clause α :=
  if ht : t.val<3 then gate u v w ⟨t.val,ht⟩ else {(u,false),(v,false)}

@[simp] theorem holds_insert (b : α → Bool) (l : α × Bool) (c : Clause α) :
    holds b (insert l c) ↔ b l.1=l.2 ∨ holds b c := by
  exact Finset.exists_mem_insert ..

omit [DecidableEq α] in
@[simp] theorem holds_single (b : α → Bool) (l : α × Bool) :
    holds b {l} ↔ b l.1=l.2 := by
  rcases l with ⟨v,t⟩
  simp [holds]

@[simp] theorem holds_unit (b : α → Bool) (v : α) (p : Bool) : holds b (unit v p) ↔ b v=p := by
  simp [unit]

@[simp] theorem holds_taut (b : α → Bool) (v : α) : holds b (taut v) := by
  cases h : b v <;> simp [taut,h]

theorem holds_gate (b : α → Bool) (u v w : α) :
    (∀ t, holds b (gate u v w t)) ↔ b w = (b u || b v) := by
  cases hu : b u <;> cases hv : b v <;> cases hw : b w <;>
    simp [Fin.forall_fin_succ,gate,hu,hv,hw]

theorem holds_splitGate (b : α → Bool) (u v w : α) :
    (∀ t, holds b (splitGate u v w t)) ↔
      b w = (b u || b v) ∧ ¬ (b u=true ∧ b v=true) := by
  cases hu : b u <;> cases hv : b v <;> cases hw : b w <;>
    simp [Fin.forall_fin_succ,splitGate,gate,hu,hv,hw]

theorem small_two (l m : α × Bool) : ({l,m} : Clause α).card ≤ 2 := by
  exact (Finset.card_insert_le _ _).trans (by simp)

theorem small_three (l m n : α × Bool) : ({l,m,n} : Clause α).card ≤ 3 := by
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (small_two m n))

theorem small_gate (u v w : α) (i : Fin 3) : (gate u v w i).card ≤ 3 := by
  unfold gate
  split
  · exact (small_two _ _).trans (by decide)
  split
  · exact (small_two _ _).trans (by decide)
  · exact small_three _ _ _

theorem small_splitGate (u v w : α) (i : Fin 4) : (splitGate u v w i).card ≤ 3 := by
  unfold splitGate
  split
  · exact small_gate _ _ _ _
  · exact (small_two _ _).trans (by decide)

end Cnf
end Encoding

namespace Encoding
namespace Cnf

def pairAt {k} (t : Fin (k*k)) : Fin k × Fin k := finProdFinEquiv.symm t

theorem pairAt_spec {k} (t : Fin (k*k)) (i j : Fin k) :
    (i.val*k+j.val=t.val) ↔ (i,j)=pairAt t := by
  change _ ↔ (i,j) = finProdFinEquiv.symm t
  rw [Equiv.eq_symm_apply, Fin.ext_iff]
  change _ ↔ j.val+k*i.val=t.val
  rw [Nat.mul_comm k i.val,Nat.add_comm j.val]

def sampleWire {k q} (X Y : Fin q → Fin k → Bool) (a : Fin q) (t : Fin (k*k)) : V k q :=
  let p := pairAt t
  if p.1 < p.2 ∧ used (X a) (Y a) p.1 p.2 then edge p.1 p.2
  else step a t.castSucc

theorem sampleWire_spec {k q} (b : V k q → Bool) (X Y : Fin q → Fin k → Bool)
    (a : Fin q) (t : Fin (k*k)) :
    (b (step a t.castSucc) || b (sampleWire X Y a t)) =
    (b (step a t.castSucc) || atPos b X Y a t) := by
  have go : (∃ i j : Fin k, i.val*k+j.val=t.val ∧ i<j ∧ used (X a) (Y a) i j ∧ b (edge i j)=true) ↔
    (pairAt t).1 < (pairAt t).2 ∧ used (X a) (Y a) (pairAt t).1 (pairAt t).2 ∧
      b (edge (pairAt t).1 (pairAt t).2)=true := by
    constructor
    · rintro ⟨i,j,ht,ord,u,bit⟩
      have eq := (pairAt_spec t i j).mp ht
      rw [← eq]
      exact ⟨ord,u,bit⟩
    · rintro ⟨ord,u,bit⟩
      exact ⟨_,_,(pairAt_spec t _ _).mpr (Prod.eta _),ord,u,bit⟩
  by_cases h : (pairAt t).1 < (pairAt t).2 ∧ used (X a) (Y a) (pairAt t).1 (pairAt t).2
  · simp [sampleWire,h,atPos,go]
  · have neg : ¬((pairAt t).1 < (pairAt t).2 ∧ used (X a) (Y a) (pairAt t).1 (pairAt t).2 ∧
        b (edge (pairAt t).1 (pairAt t).2)=true) := fun ⟨o,u,_⟩ => h ⟨o,u⟩
    simp [sampleWire,h,atPos,go,neg]

def rowWire {k q} (i j : Fin k) : V k q := if i<j then edge i j else edge j i

theorem rowWire_spec {k q} (b : V k q → Bool) (i j : Fin k) :
    b (rowWire i j)=across b i j := by
  by_cases h : i<j <;> simp [rowWire,across,h]

end Cnf
end Encoding

namespace Encoding
namespace Cnf

abbrev Ix (k q : Nat) :=
  (Fin k × Fin k) ⊕ (Fin k ⊕ ((Fin k × Fin k × Fin 4) ⊕ ((Fin q × Bool) ⊕ (Fin q × Fin (k*k) × Fin 3))))

def make {k q} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :
    Ix k q → Clause (V k q)
  | .inl (i,j) => if j ≤ i then unit (edge i j) false else taut (edge i j)
  | .inr (.inl i) => unit (row i 0) false
  | .inr (.inr (.inl (i,j,t))) => splitGate (row i j.castSucc) (rowWire i j) (row i j.succ) t
  | .inr (.inr (.inr (.inl (a,false)))) => unit (step a 0) (diagonal (X a) (Y a))
  | .inr (.inr (.inr (.inl (a,true)))) => unit (step a (Fin.last (k*k))) (label a)
  | .inr (.inr (.inr (.inr (a,t,s)))) => gate (step a t.castSucc) (sampleWire X Y a t) (step a t.succ) s

theorem holds_make {k q} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) (b : V k q → Bool) :
    (∀ ix, holds b (make X Y label ix)) ↔ Valid X Y label b := by
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i j ord
      simpa [make,ord] using h (.inl (i,j))
    · intro i
      simpa [make] using h (.inr (.inl i))
    · intro i j
      have gateSpec := (holds_splitGate b (row i j.castSucc) (rowWire i j) (row i j.succ)).mp
        (fun t => h (.inr (.inr (.inl (i,j,t)))))
      simpa only [rowWire_spec] using gateSpec
    · intro a
      constructor
      · simpa [make] using h (.inr (.inr (.inr (.inl (a,false)))))
      · simpa [make] using h (.inr (.inr (.inr (.inl (a,true)))))
    · intro a t
      have gateSpec := (holds_gate b (step a t.castSucc) (sampleWire X Y a t) (step a t.succ)).mp
        (fun s => h (.inr (.inr (.inr (.inr (a,t,s))))))
      simpa only [sampleWire_spec] using gateSpec
  · rintro ⟨edgeZero,rowZero,rows,ends,samples⟩ ix
    rcases ix with ⟨i,j⟩ | (i | (⟨i,j,t⟩ | (⟨a,f⟩ | ⟨a,t,s⟩)))
    · by_cases ord : j ≤ i
      · simpa [make,ord] using edgeZero i j ord
      · simp [make,ord]
    · simpa [make] using rowZero i
    · apply (holds_splitGate b _ _ _).mpr _ t
      simpa only [rowWire_spec] using rows i j
    · cases f with
      | false => simpa [make] using (ends a).1
      | true => simpa [make] using (ends a).2
    · apply (holds_gate b _ _ _).mpr _ s
      simpa only [sampleWire_spec] using samples a t

theorem small_make {k q} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool)
    (ix : Ix k q) : (make X Y label ix).card ≤ 3 := by
  rcases ix with ⟨i,j⟩ | (i | (⟨i,j,t⟩ | (⟨a,f⟩ | ⟨a,t,s⟩)))
  · by_cases ord : j ≤ i
    · simp [make,ord,unit]
    · simp only [make,ord,ite_false,taut]
      exact (small_two _ _).trans (by decide)
  · simp [make,unit]
  · exact small_splitGate _ _ _ _
  · cases f <;> simp [make,unit]
  · exact small_gate _ _ _ _

theorem formula {k q} (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool) :
    ∃ f : Finset (Clause (V k q)),
      f.card ≤ k*k+k*(1+4*k)+q*(2+3*(k*k)) ∧
      (∀ c∈f, c.card≤3) ∧ ∀ b, (∀ c∈f, holds b c) ↔ Valid X Y label b := by
  classical
  refine ⟨Finset.univ.image (make X Y label),?_,?_,?_⟩
  · apply Finset.card_image_le.trans
    simp [Ix,Fintype.card_prod,Fintype.card_sum]
    ring_nf
    exact le_rfl
  · intro c hc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    exact small_make _ _ _ _
  · intro b
    rw [← holds_make]
    constructor
    · intro h i
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    · intro h c hc
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
      exact h i

end Cnf
end Encoding

end PEqualNP.Outside.L_meta_29951

open PEqualNP.Outside.L_meta_29951.Encoding PEqualNP.Outside.L_meta_29951.FunctionSide in
theorem PEqualNP.Outside.L_meta_29951 : ∀ (k q : Nat), 2 ≤ k → ∀ (X Y : Fin q → Fin k → Bool) (label : Fin q → Bool),
  let V := (Fin k × Fin k) ⊕ ((Fin k × Fin (k+1)) ⊕ (Fin q × Fin (k*k+1)))
  let edge := fun (i j : Fin k) => (Sum.inl (i,j) : V)
  let row := fun (i : Fin k) (s : Fin (k+1)) => (Sum.inr (Sum.inl (i,s)) : V)
  let step := fun (a : Fin q) (s : Fin (k*k+1)) => (Sum.inr (Sum.inr (a,s)) : V)
  let across := fun (b : V → Bool) (i j : Fin k) =>
    if i < j then b (edge i j) else b (edge j i)
  let used := fun (x y : Fin k → Bool) (i j : Fin k) =>
    (x i = true ∧ x j = true) ∨ (y i = true ∧ y j = true)
  let diagonal := fun (x y : Fin k → Bool) => decide (∃ i, x i = true ∧ y i = true)
  let atPos := fun (b : V → Bool) (a : Fin q) (t : Fin (k*k)) =>
    decide (∃ i j : Fin k, i.val*k+j.val = t.val ∧ i < j ∧
      used (X a) (Y a) i j ∧ b (edge i j) = true)
  let valid := fun b : V → Bool =>
    (∀ i j, j ≤ i → b (edge i j) = false) ∧
    (∀ i, b (row i 0) = false) ∧
    (∀ i j, b (row i j.succ) = (b (row i j.castSucc) || across b i j) ∧
      ¬ (b (row i j.castSucc) = true ∧ across b i j = true)) ∧
    (∀ a, b (step a 0) = diagonal (X a) (Y a) ∧ b (step a (Fin.last (k*k))) = label a) ∧
    (∀ a t, b (step a t.succ) = (b (step a t.castSucc) || atPos b a t))
  let eval := fun (b : V → Bool) (x y : Fin k → Bool) =>
    diagonal x y || decide (∃ i j : Fin k, i < j ∧ b (edge i j) = true ∧ used x y i j)
  let Fs := { f : (Fin k → Bool) → (Fin k → Bool) → Bool //
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k ∧
      PEqualNP.Represents.Represents (fun i j : Fin k => decide (i=j)) C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧ ∀ a, f (X a) (Y a) = label a }
  ∃ formula : Finset (Finset (V × Bool)),
    let sat := fun b : V → Bool => ∀ c ∈ formula, ∃ lit ∈ c, b lit.1 = lit.2
    formula.card ≤ k*k + k*(1+4*k) + q*(2+3*(k*k)) ∧
    (∀ c ∈ formula, c.card ≤ 3) ∧ (∀ b, sat b ↔ valid b) ∧
    ∃ e : { b : V → Bool // sat b } ≃ Fs, ∀ b x y, (e b).val x y = eval b.val x y := by
  intro k q hk X Y label
  dsimp only
  obtain ⟨f, size, width, check⟩ := Cnf.formula X Y label
  refine ⟨f, size, width, check, ?_⟩
  let cast : {b : V k q → Bool // ∀ c ∈ f, Cnf.holds b c} ≃ {b : V k q → Bool // Valid X Y label b} :=
    ⟨fun b => ⟨b.val, (check b.val).mp b.property⟩,
     fun b => ⟨b.val, (check b.val).mpr b.property⟩, fun _ => rfl, fun _ => rfl⟩
  let matchEquiv := cast.trans (matchingEquiv X Y label)
  refine ⟨matchEquiv.trans (permFs hk X Y label), ?_⟩
  intro b x y
  exact matchingEquiv_value X Y label (cast b) x y
