import PEqualNP.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_49677
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace ForestCore
def pn (a b : Nat) : Nat := a * 1000000000000000000 + b

open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [(BitVec.ofNat 512 (word80 [0xaaaaaaaa,(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450),(pn 805950 546409752783137450)])),(BitVec.ofNat 512 (word80 [0xcccccccc,(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940),(pn 967140 655691703339764940)])),(BitVec.ofNat 512 (word80 [0xf0f0f0f0,(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400),(pn 1137812 536107886282076400)])),(BitVec.ofNat 512 (word80 [0xff00ff00,(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400),(pn 1204221 828098618944454400)])),(BitVec.ofNat 512 (word80 [0xffff0000,(pn 1208907 373152026146963455),0xffff0000ffff0000,(pn 1208907 373152026146963455),0xffff0000ffff0000,(pn 1208907 373152026146963455),0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,(pn 1208925 819333154198061055),(pn 1208907 372870559760121855),0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819333154197995520),0xffffffffffffffff,0xffff,(pn 1208925 819614624879738880),0xffffffffffff,(pn 1208907 372870555465154560)])),(BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819614629174706175),(pn 1208907 372870555465154560),0xffff,(pn 1208925 819614629174706175),(pn 1208925 819333154197995520),0])),(BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819614629174706175),(pn 1208925 819614629174706175),(pn 1208925 819614629174640640),0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,(pn 1208925 819614629174706174),(pn 1208907 372870551170187260),(pn 1204184 644673428562968575),(pn 1208925 819614629174706175),(pn 1208907 372589080488378367),(pn 1208870 407037819709860352)]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 8).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (word80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (word80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (word80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (word80 [0x10000,0,0,1])
  | 4 => (word80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (word80 [0x1000000000000,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def columnPairs (m z s : Nat) (G : Sig) : List (Sig × Row × Row) :=
  if m.testBit 8 then
    (selected s).map fun (i,a) =>
      let v := 1 <<< i
      let candidates := (0 :: (List.range 8).map (fun j => 1 <<< j))
      let r := (candidates.find? fun r =>
        bit (Fin.ofNat 512 r) G != bit (Fin.ofNat 512 (r ||| v)) G).getD 0
      (a, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| v))
  else supportPairs (z/512+80) s

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := columnPairs m z s G
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨by omega,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
  else (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases ht : m.testBit 8 = true
  · simp only [bit,graphGoal,liftGoal,if_pos ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
  · simp only [bit,graphGoal,liftGoal,if_neg ht,BitVec.getLsbD_and,BitVec.getLsbD_or,
      pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
      pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]

abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

end ForestCore
end PEqualNP.Outside.L_meta_49677

namespace PEqualNP.Outside.L_meta_49677.ForestCore
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
private def proofWord80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

def g82Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x3ff63ff63ff63ff63f,(pn 1162882 43834387862124095)])),(BitVec.ofNat 152 (proofWord80 [0x492049204920492049,(pn 152464 666195390404042825)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xc7fbc7fbc7fbc7fbc7,(pn 1189003 32017409375992775)])),(BitVec.ofNat 152 (proofWord80 [0x924092409240924092,(pn 304929 332390780808085650)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xf8fdf8fdf8fdf8fdf8,(pn 1199351 813352631882546680)])),(BitVec.ofNat 152 (proofWord80 [0x248124812481248124,(pn 609858 664781561616171300)]))),(0x0,0x0),(0x0,0x0)]
def g82C : List ColumnInfo := []
def g82A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
def g82D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g82L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g82D3)
  | _ => emptyPacking
def g82I (_ _ : Nat) : Option (Nat × Nat) := none
def g82 : Forest := ⟨82,3,fun i => g82Y[i]?.getD (0,0),g82C,g82A,g82L,g82I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82P3_0 : block g82 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g82B3 : block g82 3 0 1=true := g82P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82T : checkedTables g82 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g82 0 0 0 = true)
  · exact (rfl : block g82 1 0 0 = true)
  · exact (rfl : block g82 2 0 0 = true)
  · exact g82B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g82G : graphValid g82 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low82 : Lower true (varsX 82) (graphGoal 82) 4 := lower_forest (g:=g82) (i:=0) (hints:=16842816) (before_sound [] baseKnown) g82G g82T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K82 := extendKnown [] 4 [(82,[]),(137,[16,67,118]),(161,[16,84,118]),(164,[33,84,118]),(194,[100,84,117]),(196,[33,100,84,117]),(200,[49,33,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V82 : Known true K82 := extend_ok (m:=82) baseKnown low82 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xe6de3fff03fff1ffe6,(pn 1049545 879886024386469439)])),(BitVec.ofNat 152 (proofWord80 [0x648490a2850240206,(pn 341357 731007050283370569)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x19e9c0fffc07fe3f19,(pn 1103871 610997741933160896)])),(BitVec.ofNat 152 (proofWord80 [0x50e8db2c3161408450,(pn 1099632 45411241334728923)]))),((BitVec.ofNat 152 (proofWord80 [0xece607fffff8003fec,(pn 1086291 865003813055030791)])),(BitVec.ofNat 152 (proofWord80 [0x8a7b6b04185892808,(pn 792005 210639894179260342)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x1b3df8ffffffffc01b,(pn 292657 594729400964431352)])),(BitVec.ofNat 152 (proofWord80 [0x891524c08206003089,(pn 99847 650583316231951652)]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := []
def g45A : List (List Nat) := [[],[80,50]]
def g45D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g45L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g45D3)
  | _ => emptyPacking
def g45I (_ _ : Nat) : Option (Nat × Nat) := none
def g45 : Forest := ⟨45,3,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P3_0 : block g45 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B3 : block g45 3 0 1=true := g45P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact g45B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K82) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 4 := lower_forest (g:=g45) (i:=0) (hints:=1283) (before_sound K82 V82) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K82 4 [(45,[]),(75,[96,33,16,49,83]),(77,[96,32,50,83]),(89,[96,32,67,50,83]),(101,[32,99,67]),(102,[32,16,83,67,100]),(105,[48,82,96,66,64]),(108,[32,16,49,81,65,100]),(147,[16,32,67,117,101]),(150,[16,67,117,101]),(209,[96,32,67,50,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V82 low45 (by decide +kernel)
def g86Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfdf00fff81fc7e3ffb,(pn 1058400 317033753488113727)])),(BitVec.ofNat 152 (proofWord80 [0x45c09245142904808b,(pn 609859 314374012705374793)]))),((BitVec.ofNat 152 (proofWord80 [0xe6a8703ffe007fc7cd,(pn 381930 611549317130527168)])),(BitVec.ofNat 152 (proofWord80 [0x96a9b6d618b228112d,(pn 393979 520990958612817627)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfbb781ffffff8007f7,(pn 524256 466573726212611591)])),(BitVec.ofNat 152 (proofWord80 [0x235249820c0312204,(pn 501920 936703110033233042)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x64ffe3ffffffff80c,(pn 755514 73654884983980024)])),(BitVec.ofNat 152 (proofWord80 [0x249204100400400,(pn 21587 338844555465197860)]))),(0x0,0x0),(0x0,0x0)]
def g86C : List ColumnInfo := [(4,0,82,0,4)]
def g86A : List (List Nat) := [[],[65]]
def g86D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g86L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g86D4)
  | _ => emptyPacking
def g86I (_ _ : Nat) : Option (Nat × Nat) := none
def g86 : Forest := ⟨86,4,fun i => g86Y[i]?.getD (0,0),g86C,g86A,g86L,g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4_0 : block g86 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g86B4 : block g86 4 0 1=true := g86P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=16844352) (before_sound K45 V45) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K45 5 [(86,[]),(90,[50]),(139,[32,16,67,118]),(141,[16,67,118]),(163,[32,16,84,118]),(166,[33,84,118]),(172,[33,49,84,118]),(195,[32,100,84,117]),(197,[16,32,100,84,117]),(212,[33,65,49,115,83]),(216,[49,66,114,82]),(225,[16,98,50,84,67,116]),(226,[82,50,100,116]),(232,[49,82,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V45 low86 (by decide +kernel)
def g165Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xfe7d01c7fc0fc7cfe7,(pn 982777 942906202192937415)])),(BitVec.ofNat 152 (proofWord80 [0x51d124928a290a051,(pn 987649 237003808729272905)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x3f8b8e38fff007f3f8,(pn 873113 219765359799406136)])),(BitVec.ofNat 152 (proofWord80 [0x884b924930c3210884,(pn 874312 478016607791845961)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x3fe7703ffffff803fe,(pn 562035 398437233934954559)])),(BitVec.ofNat 152 (proofWord80 [0x100024924104020100,(pn 10793 943930611532047506)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xc018ffc0fffffffc01,(pn 679948 139478437607309248)])),(BitVec.ofNat 152 (proofWord80 [0x200049248208040200,(pn 21587 887861223064095012)]))),(0x0,0x0)]
def g165C : List ColumnInfo := [(1,0,164,0,4)]
def g165A : List (List Nat) := [[],[117],[32],[32,117]]
def g165D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g165L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g165D4)
  | _ => emptyPacking
def g165I (_ _ : Nat) : Option (Nat × Nat) := none
def g165 : Forest := ⟨165,4,fun i => g165Y[i]?.getD (0,0),g165C,g165A,g165L,g165I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165P4_0 : block g165 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g165B4 : block g165 4 0 1=true := g165P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165T : checkedTables g165 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g165 0 0 0 = true)
  · exact (rfl : block g165 1 0 0 = true)
  · exact (rfl : block g165 2 0 0 = true)
  · exact (rfl : block g165 3 0 0 = true)
  · exact g165B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165G : graphValid g165 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low165 : Lower true (varsX 165) (graphGoal 165) 5 := lower_forest (g:=g165) (i:=0) (hints:=1285) (before_sound K86 V86) g165G g165T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K165 := extendKnown K86 5 [(165,[]),(169,[48,82,32]),(198,[16,101]),(201,[98,50,83]),(202,[16,50,101]),(204,[32,16,49,101]),(210,[64,16,114,50,49,81,101]),(228,[80,16,98,49,67,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V165 : Known true K165 := extend_ok (m:=165) V86 low165 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 4 := by
  have q := @lower_count true (vars 55) (graphGoal 55) (proper_of _ (by decide +kernel)) (graphPairs 55 66885) (by decide +kernel)
  exact q
def K55 := extendKnown K165 4 [(59,[48,82,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V165 low55 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0x1fff0007ff803ffc01,(pn 1208925 819614570218778631)])),(BitVec.ofNat 152 (proofWord80 [0x502a8350250681482d,(pn 25098 311408250631977837)]))),((BitVec.ofNat 152 (proofWord80 [0x1ffffff800003fffff,(pn 1208335 667884281443369016)])),(BitVec.ofNat 152 (proofWord80 [0x854c2a62b62b159148,(pn 196104 475483696833087195)]))),((BitVec.ofNat 152 (proofWord80 [0x1fffffffffffc00001,(pn 1208925 675499496466141632)])),(BitVec.ofNat 152 (proofWord80 [0x6703383384c19e270,(pn 368434 544797595573016283)]))),((BitVec.ofNat 152 (proofWord80 [0xe00000000000000001,(pn 1208925 819614569849269767)])),(BitVec.ofNat 152 (proofWord80 [0x7803c03c0701e0380,(pn 529034 204828317107651730)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (proofWord80 [0x1800c0040000200001,(pn 604905 739769085423651108)]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(2,0,77,0,4)]
def g79A : List (List Nat) := [[],[33]]
def g79D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g79L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g79D4)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,4,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 1=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 5 := lower_forest (g:=g79) (i:=0) (hints:=16778851) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 5 [(124,[80,49,66,33,16]),(151,[64,16,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffc00ffc3fe1ffc01f,(pn 1208787 468141628286304287)])),(BitVec.ofNat 152 (proofWord80 [0x22a4a228884522a950,(pn 793676 388034962658088629)]))),((BitVec.ofNat 152 (proofWord80 [0xfffff0003fffffffe0,(pn 75557 846577217508769760)])),(BitVec.ofNat 152 (proofWord80 [0xb00c0b102800b0182,(pn 909645 918637691063340131)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffffc001ffffff,(pn 1133377 178398533062983711)])),(BitVec.ofNat 152 (proofWord80 [0x4c0904c013084c0203,(pn 13024 698545425344702794)]))),((BitVec.ofNat 152 (proofWord80 [0x1ffffff,(pn 1208916 596327460503552992)])),(BitVec.ofNat 152 (proofWord80 [0x700e07021c10700c04,(pn 14169 121649533024350604)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (proofWord80 [0x803008002001803018,(pn 56749 111606712254087696)]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,1,82,8,5),(1,0,90,0,5),(2,0,89,0,4),(8,1,82,0,4),(16,0,75,0,4)]
def g91A : List (List Nat) := [[],[65]]
def g91D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d41
def g91D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x2012,(pn 10640 402918668025068849)])
def g91H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc0
def g91D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g91H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2051600028b5
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (3,1,3,0,0,5,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 11 0 7 2 1 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 1=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 3=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16842819) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(118,[80,32,50]),(155,[64,16,49,118]),(179,[64,16,49,83,118]),(182,[64,33,16,49,83,118]),(241,[64,16,33,99,82,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x3ffc003ffc01ffe00f,(pn 1208925 819614624307871807)])),(BitVec.ofNat 152 (proofWord80 [0x80a81a8128340a4160,(pn 756354 67403977169441353)]))),((BitVec.ofNat 152 (proofWord80 [0x3fffffc00001fffff0,(pn 37760 494121689374163392)])),(BitVec.ofNat 152 (proofWord80 [0x15315315b158ac8a45,(pn 232805 803210123219744475)]))),((BitVec.ofNat 152 (proofWord80 [0x3ffffffffffe000000,(pn 37778 922855771312426496)])),(BitVec.ofNat 152 (proofWord80 [0x19c19c19c260cf1389,(pn 918210 757413941402875611)]))),((BitVec.ofNat 152 (proofWord80 [0xc00000000000000000,(pn 37778 931862943200735239)])),(BitVec.ofNat 152 (proofWord80 [0x1e01e01e0380f01c0e,(pn 16536 357084527227839634)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffffffff,(pn 1171146 887751686545735672)])),(BitVec.ofNat 152 (proofWord80 [0x200200200001000000,(pn 18898 693807115063019812)]))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(4,0,90,0,5)]
def g94A : List (List Nat) := [[],[50],[65],[65,50]]
def g94D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g94L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g94D5)
  | _ => emptyPacking
def g94I (_ _ : Nat) : Option (Nat × Nat) := none
def g94 : Forest := ⟨94,5,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_0 : block g94 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B5 : block g94 5 0 1=true := g94P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact (rfl : block g94 4 0 0 = true)
  · exact g94B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 6 := lower_forest (g:=g94) (i:=0) (hints:=16868928) (before_sound K91 V91) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K91 6 [(94,[]),(143,[64,16,33,50,118]),(174,[33,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V91 low94 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xe001ffc07ff01ffe00,(pn 302158 244387923533365263)])),(BitVec.ofNat 152 (proofWord80 [0x48d4128d0522c8549a,(pn 685496 165000455572837717)]))),((BitVec.ofNat 152 (proofWord80 [0xfffe00007fffffffff,(pn 906694 940892051647762176)])),(BitVec.ofNat 152 (proofWord80 [0x82985b161644829813,(pn 26883 851876733549032243)]))),((BitVec.ofNat 152 (proofWord80 [0xffffffff80001fffff,(pn 1208925 243154148603064560)])),(BitVec.ofNat 152 (proofWord80 [0xe01c18078700e01c,(pn 8291 845361356628365585)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x1fffff,(pn 1208925 819612869302812927)])),(BitVec.ofNat 152 (proofWord80 [0x130160205808130120,(pn 179450 250608650010012330)]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (proofWord80 [0x1c01800060001c01c0,(pn 264489 921073348123872460)]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[16,101]]
def g103D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=16778597) (before_sound K94 V94) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K94 5 [(103,[]),(117,[65,49]),(121,[64,81,50,33,32,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V94 low103 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xf003ff0ff87ff007ff,(pn 1206712 209433514605544447)])),(BitVec.ofNat 152 (proofWord80 [0xa4280a201120a45214,(pn 609482 766155251386197289)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfffc000ffffffff801,(pn 1208787 451955721440066560)])),(BitVec.ofNat 152 (proofWord80 [0xc0302c40a002c06058,(pn 47242 186518030200179811)]))),((BitVec.ofNat 152 (proofWord80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (proofWord80 [0x140b002c20b008060,(pn 208412 35304608648861894)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x7fffffff,(pn 1208916 596327460471078880)])),(BitVec.ofNat 152 (proofWord80 [0x982c08b044c090481,(pn 226679 72072932537291412)]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (proofWord80 [0xe03000c00700e0701,(pn 907956 823074292147970840)]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,4),(4,0,105,0,4),(8,0,101,0,4),(32,0,77,0,4),(64,0,45,0,4)]
def g109A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x25,(pn 1199491 679115214835429632),0x2000,0x26000000bb9700,0,0x6a0000000000000000])
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (2,1,3,0,0,4,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 2 53 0 8 1 3 g109H6
  | _ => fun _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 1=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 2=true := g109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 1=true := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=33555715) (before_sound K103 V103) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K103 7 [(109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V103 low109 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xc003ff0ffc3ffc00ff,(pn 1208925 801647777983238080)])),(BitVec.ofNat 152 (proofWord80 [0x90a80a204890a92a42,(pn 685338 85838350491399379)]))),((BitVec.ofNat 152 (proofWord80 [0xfffc000fffffffff00,(pn 301954 753400233479368767)])),(BitVec.ofNat 152 (proofWord80 [0x2304c411002300c13,0x4209020009d3145145]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfffffff0003fffffff,(pn 906712 810742461308338239)])),(BitVec.ofNat 152 (proofWord80 [0x4c090026104c03004,(pn 26048 100076277203509898)]))),((BitVec.ofNat 152 (proofWord80 [0x3fffffff,(pn 1208907 373194464517427136)])),(BitVec.ofNat 152 (proofWord80 [0x2702e08b8227024098,(pn 179461 172126014715906860)]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (proofWord80 [0x3803000c00380380e0,(pn 264616 247056936965704752)]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,1,82,32,5)]
def g115A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97],[80],[80,100],[80,65],[80,65,97],[80,97,65],[80,97]]
def g115D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g115L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g115D5)
  | _ => emptyPacking
def g115I (_ _ : Nat) : Option (Nat × Nat) := none
def g115 : Forest := ⟨115,5,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 1=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact (rfl : block g115 4 0 0 = true)
  · exact g115B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 6 := lower_forest (g:=g115) (i:=0) (hints:=16842821) (before_sound K109 V109) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K109 6 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V109 low115 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffc00ffc07fe03fff,(pn 1058104 956341153021821383)])),(BitVec.ofNat 152 (proofWord80 [0xa0a86a128d0a458a05,(pn 333538 579718192495891017)]))),((BitVec.ofNat 152 (proofWord80 [0xfffff00007fffc07f,(pn 1208630 676204337220029952)])),(BitVec.ofNat 152 (proofWord80 [0xc5314c5b162c891329,(pn 626999 265501164075857627)]))),((BitVec.ofNat 152 (proofWord80 [0xfffffffff8000007f,(pn 1208925 815111080694018104)])),(BitVec.ofNat 152 (proofWord80 [0x1c0701c180f0e1c0e,(pn 33089 64418268788593225)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xf0000000000000007f,(pn 1208925 819614521773752383)])),(BitVec.ofNat 152 (proofWord80 [0x60180602030102030,(pn 37889 613453325567599762)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (proofWord80 [0x80200800040000040,(pn 75705 439930303813667108)]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5)]
def g167A : List (List Nat) := [[],[32]]
def g167D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g167L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g167D5)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,5,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P5_0 : block g167 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B5 : block g167 5 0 1=true := g167P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g167 0 0 0 = true)
  · exact (rfl : block g167 1 0 0 = true)
  · exact (rfl : block g167 2 0 0 = true)
  · exact (rfl : block g167 3 0 0 = true)
  · exact (rfl : block g167 4 0 0 = true)
  · exact g167B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1397) (before_sound K115 V115) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K115 6 [(167,[]),(171,[48,82,32]),(199,[16,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V115 low167 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xfe1ff00ff87f87ffc0,(pn 604454 839313597785501951)])),(BitVec.ofNat 152 (proofWord80 [0x1440a0a05101100285,(pn 23632 587332985302356241)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x1ffff0007ff87fff,(pn 606823 83163942432739072)])),(BitVec.ofNat 152 (proofWord80 [0x5882c0c1620a010b06,(pn 104076 823124529999196979)]))),((BitVec.ofNat 152 (proofWord80 [0x1fffffff80007fff,(pn 1206564 780369771284660239)])),(BitVec.ofNat 152 (proofWord80 [0x610b0505802c222c08,(pn 114153 685532969491916390)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffe000000000007fff,(pn 1208925 675512518183751664)])),(BitVec.ofNat 152 (proofWord80 [0x800c06060430443010,(pn 152001 225776126551671876)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (proofWord80 [0x1008080040004020,(pn 303412 118581968886073480)]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(32,0,141,0,5)]
def g173A : List (List Nat) := [[],[80,50]]
def g173D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
def g173L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P6_0 : block g173 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B6 : block g173 6 0 1=true := g173P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K167 7 [(173,[]),(203,[96,33,16,49,83]),(205,[96,32,50,83]),(214,[16,67,117,101]),(218,[16,50,66,117,101]),(229,[32,99,67]),(230,[32,16,83,67,100]),(233,[48,82,96,66,64]),(236,[32,16,49,81,65,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V167 low173 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffc01ffff0fffc00f,(pn 1138073 24265960122544128)])),(BitVec.ofNat 152 (proofWord80 [0x22a9549452202a8aa0,(pn 765357 871296181658154871)]))),((BitVec.ofNat 152 (proofWord80 [0xffffe01fff0fffff0,0xffffff2c761b0f00ff])),(BitVec.ofNat 152 (proofWord80 [0x4030181804020300c0,(pn 925657 635641965992284433)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffe0000ffffff,(pn 1204204 605828642279264015)])),(BitVec.ofNat 152 (proofWord80 [0x88c0602118448c2309,0x98488032b104aaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xf00000000000ffffff,(pn 1208924 666714341587816432)])),(BitVec.ofNat 152 (proofWord80 [0x30180c06088300c02,0x200304014868444444]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (proofWord80 [0xc0201018000c0300c,(pn 41330 797117729684359304)]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(0,1,82,128,5),(1,0,210,0,5),(16,0,195,0,5),(2,0,209,0,4),(64,0,147,0,4),(128,1,82,0,4)]
def g211A : List (List Nat) := [[],[97]]
def g211D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4931
def g211D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404fd31
def g211H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50
def g211D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x232a8bf
def g211H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g211L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g211D4)
  | 5 => (1,1,3,0,0,0,0,g211D5)
  | 6 => (1,0,3,0,0,0,0,g211D6)
  | _ => emptyPacking
def g211I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g211H5
  | 6 => lookupWord 1 2 0 4 0 0 g211H6
  | _ => fun _ => none
def g211 : Forest := ⟨211,6,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P4_0 : block g211 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B4 : block g211 4 0 1=true := g211P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P5_0 : block g211 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B5 : block g211 5 0 1=true := g211P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P6_0 : block g211 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B6 : block g211 6 0 1=true := g211P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact g211B4
  · exact g211B5
  · exact g211B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 7 := lower_forest (g:=g211) (i:=0) (hints:=16842823) (before_sound K173 V173) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior506 : Lower true (varsX 506) (graphGoal 506) 8 := by
  have h := lift_ok (u := true) (ms := ([32, 50, 100, 101, 118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 506) (T := graphGoal 506) (xs := [(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior505 : Lower true (varsX 505) (graphGoal 505) 8 := by
  have h := lift_ok (u := true) (ms := ([16, 33, 50, 115, 84, 118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 505) (T := graphGoal 505) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior499 : Lower true (varsX 499) (graphGoal 499) 8 := by
  have h := lift_ok (u := true) (ms := ([32, 33, 67, 116, 118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 499) (T := graphGoal 499) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior491 : Lower true (varsX 491) (graphGoal 491) 8 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 128 0)
    (raw := varsX 491) (T := graphGoal 491) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low109
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior489 : Lower true (varsX 489) (graphGoal 489) 7 := by
  have h := lift_ok (u := true) (ms := ([16, 33, 50, 115, 84, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 489) (T := graphGoal 489) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior483 : Lower true (varsX 483) (graphGoal 483) 7 := by
  have h := lift_ok (u := true) (ms := ([64, 113, 84, 117, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 483) (T := graphGoal 483) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior475 : Lower true (varsX 475) (graphGoal 475) 8 := by
  have h := lift_ok (u := true) (ms := ([33, 84]).map swapRows ++ fixRows 64 0)
    (raw := varsX 475) (T := graphGoal 475) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior467 : Lower true (varsX 467) (graphGoal 467) 7 := by
  have h := lift_ok (u := true) (ms := ([32, 33, 67, 116, 101, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 467) (T := graphGoal 467) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior443 : Lower true (varsX 443) (graphGoal 443) 8 := by
  have h := lift_ok (u := true) (ms := ([33, 84]).map swapRows ++ fixRows 32 0)
    (raw := varsX 443) (T := graphGoal 443) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior427 : Lower true (varsX 427) (graphGoal 427) 7 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 0 0)
    (raw := varsX 427) (T := graphGoal 427) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior411 : Lower true (varsX 411) (graphGoal 411) 7 := by
  have h := lift_ok (u := true) (ms := ([33, 84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 411) (T := graphGoal 411) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior379 : Lower true (varsX 379) (graphGoal 379) 8 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 16 0)
    (raw := varsX 379) (T := graphGoal 379) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low109
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior378 : Lower true (varsX 378) (graphGoal 378) 7 := by
  have h := lift_ok (u := true) (ms := ([32, 50, 100, 101, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 378) (T := graphGoal 378) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior371 : Lower true (varsX 371) (graphGoal 371) 7 := by
  have h := lift_ok (u := true) (ms := ([32, 33, 67, 116, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 371) (T := graphGoal 371) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior363 : Lower true (varsX 363) (graphGoal 363) 7 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 0 0)
    (raw := varsX 363) (T := graphGoal 363) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low109
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior315 : Lower true (varsX 315) (graphGoal 315) 7 := by
  have h := lift_ok (u := true) (ms := ([112, 65, 115, 101, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 315) (T := graphGoal 315) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior504 : Lower true (varsX 504) (graphGoal 504) 6 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 83, 84, 118]).map swapRows ++ fixRows 72 0)
    (raw := varsX 504) (T := graphGoal 504) (xs := [(inputs.getD 3 zero,64,72), (inputs.getD 6 zero,8,72)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72), (inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior498 : Lower true (varsX 498) (graphGoal 498) 6 := by
  have h := lift_ok (u := true) (ms := ([101]).map swapRows ++ fixRows 192 0)
    (raw := varsX 498) (T := graphGoal 498) (xs := [(inputs.getD 6 zero,2,66), (inputs.getD 7 zero,2,130)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,2,66), (inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior497 : Lower true (varsX 497) (graphGoal 497) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 192 0)
    (raw := varsX 497) (T := graphGoal 497) (xs := [(inputs.getD 6 zero,16,80), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,16,80), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior496 : Lower true (varsX 496) (graphGoal 496) 5 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 83, 84, 118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 496) (T := graphGoal 496) (xs := [(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior490 : Lower true (varsX 490) (graphGoal 490) 6 := by
  have h := lift_ok (u := true) (ms := ([84, 118]).map swapRows ++ fixRows 72 0)
    (raw := varsX 490) (T := graphGoal 490) (xs := [(inputs.getD 3 zero,64,72), (inputs.getD 6 zero,2,66)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72), (inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior482 : Lower true (varsX 482) (graphGoal 482) 5 := by
  have h := lift_ok (u := true) (ms := ([84, 118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 482) (T := graphGoal 482) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior474 : Lower true (varsX 474) (graphGoal 474) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 136 0)
    (raw := varsX 474) (T := graphGoal 474) (xs := [(inputs.getD 3 zero,64,72), (inputs.getD 7 zero,2,130)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72), (inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior473 : Lower true (varsX 473) (graphGoal 473) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 80 0)
    (raw := varsX 473) (T := graphGoal 473) (xs := [(inputs.getD 4 zero,1,17), (inputs.getD 6 zero,8,72)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17), (inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior466 : Lower true (varsX 466) (graphGoal 466) 5 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 128 0)
    (raw := varsX 466) (T := graphGoal 466) (xs := [(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior465 : Lower true (varsX 465) (graphGoal 465) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 465) (T := graphGoal 465) (xs := [(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior459 : Lower true (varsX 459) (graphGoal 459) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 66 0)
    (raw := varsX 459) (T := graphGoal 459) (xs := [(inputs.getD 1 zero,64,66), (inputs.getD 6 zero,2,66)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,64,66), (inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior457 : Lower true (varsX 457) (graphGoal 457) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 457) (T := graphGoal 457) (xs := [(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior442 : Lower true (varsX 442) (graphGoal 442) 6 := by
  have h := lift_ok (u := true) (ms := ([101]).map swapRows ++ fixRows 136 0)
    (raw := varsX 442) (T := graphGoal 442) (xs := [(inputs.getD 3 zero,128,136), (inputs.getD 7 zero,2,130)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,128,136), (inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior441 : Lower true (varsX 441) (graphGoal 441) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 48 0)
    (raw := varsX 441) (T := graphGoal 441) (xs := [(inputs.getD 4 zero,1,17), (inputs.getD 5 zero,1,33)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17), (inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior440 : Lower true (varsX 440) (graphGoal 440) 5 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 83, 84, 118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 440) (T := graphGoal 440) (xs := [(inputs.getD 3 zero,128,136)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior435 : Lower true (varsX 435) (graphGoal 435) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 130 0)
    (raw := varsX 435) (T := graphGoal 435) (xs := [(inputs.getD 1 zero,16,18), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior434 : Lower true (varsX 434) (graphGoal 434) 5 := by
  have h := lift_ok (u := true) (ms := ([101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 434) (T := graphGoal 434) (xs := [(inputs.getD 7 zero,2,130)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior433 : Lower true (varsX 433) (graphGoal 433) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 433) (T := graphGoal 433) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior432 : Lower true (varsX 432) (graphGoal 432) 4 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 83, 84, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 432) (T := graphGoal 432) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior426 : Lower true (varsX 426) (graphGoal 426) 5 := by
  have h := lift_ok (u := true) (ms := ([84, 118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 426) (T := graphGoal 426) (xs := [(inputs.getD 3 zero,128,136)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior425 : Lower true (varsX 425) (graphGoal 425) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 425) (T := graphGoal 425) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior419 : Lower true (varsX 419) (graphGoal 419) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 84, 118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 419) (T := graphGoal 419) (xs := [(inputs.getD 1 zero,32,34)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,32,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior418 : Lower true (varsX 418) (graphGoal 418) 4 := by
  have h := lift_ok (u := true) (ms := ([84, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 418) (T := graphGoal 418) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior417 : Lower true (varsX 417) (graphGoal 417) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 84, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 417) (T := graphGoal 417) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior410 : Lower true (varsX 410) (graphGoal 410) 5 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 8 0)
    (raw := varsX 410) (T := graphGoal 410) (xs := [(inputs.getD 3 zero,128,136)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior409 : Lower true (varsX 409) (graphGoal 409) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 409) (T := graphGoal 409) (xs := [(inputs.getD 4 zero,1,17)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior403 : Lower true (varsX 403) (graphGoal 403) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 403) (T := graphGoal 403) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior402 : Lower true (varsX 402) (graphGoal 402) 4 := by
  have h := lift_ok (u := true) (ms := ([118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 402) (T := graphGoal 402) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior401 : Lower true (varsX 401) (graphGoal 401) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 401) (T := graphGoal 401) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior395 : Lower true (varsX 395) (graphGoal 395) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 2 0)
    (raw := varsX 395) (T := graphGoal 395) (xs := [(inputs.getD 1 zero,128,130)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,128,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior393 : Lower true (varsX 393) (graphGoal 393) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 393) (T := graphGoal 393) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior377 : Lower true (varsX 377) (graphGoal 377) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 72 0)
    (raw := varsX 377) (T := graphGoal 377) (xs := [(inputs.getD 3 zero,1,9), (inputs.getD 6 zero,8,72)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,1,9), (inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior370 : Lower true (varsX 370) (graphGoal 370) 5 := by
  have h := lift_ok (u := true) (ms := ([101]).map swapRows ++ fixRows 64 0)
    (raw := varsX 370) (T := graphGoal 370) (xs := [(inputs.getD 6 zero,2,66)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior369 : Lower true (varsX 369) (graphGoal 369) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 64 0)
    (raw := varsX 369) (T := graphGoal 369) (xs := [(inputs.getD 6 zero,16,80)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior347 : Lower true (varsX 347) (graphGoal 347) 6 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 9 0)
    (raw := varsX 347) (T := graphGoal 347) (xs := [(inputs.getD 0 zero,8,9), (inputs.getD 3 zero,1,9)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 0 zero,8,9), (inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior346 : Lower true (varsX 346) (graphGoal 346) 5 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 8 0)
    (raw := varsX 346) (T := graphGoal 346) (xs := [(inputs.getD 3 zero,64,72)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior339 : Lower true (varsX 339) (graphGoal 339) 5 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 1 0)
    (raw := varsX 339) (T := graphGoal 339) (xs := [(inputs.getD 0 zero,16,17)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 0 zero,16,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior338 : Lower true (varsX 338) (graphGoal 338) 4 := by
  have h := lift_ok (u := true) (ms := ([]).map swapRows ++ fixRows 0 0)
    (raw := varsX 338) (T := graphGoal 338) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior313 : Lower true (varsX 313) (graphGoal 313) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 8 0)
    (raw := varsX 313) (T := graphGoal 313) (xs := [(inputs.getD 3 zero,1,9)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior307 : Lower true (varsX 307) (graphGoal 307) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 2 0)
    (raw := varsX 307) (T := graphGoal 307) (xs := [(inputs.getD 1 zero,16,18)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior306 : Lower true (varsX 306) (graphGoal 306) 4 := by
  have h := lift_ok (u := true) (ms := ([101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 306) (T := graphGoal 306) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior305 : Lower true (varsX 305) (graphGoal 305) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 305) (T := graphGoal 305) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior488 : Lower true (varsX 488) (graphGoal 488) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 65, 98, 67, 116, 101, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 488) (T := graphGoal 488) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior451 : Lower true (varsX 451) (graphGoal 451) 4 := by
  have h := lift_ok (u := true) (ms := ([32, 33, 67, 100, 117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 451) (T := graphGoal 451) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior376 : Lower true (varsX 376) (graphGoal 376) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 65, 98, 99, 101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 376) (T := graphGoal 376) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior362 : Lower true (varsX 362) (graphGoal 362) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 66, 67, 100, 101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 362) (T := graphGoal 362) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior361 : Lower true (varsX 361) (graphGoal 361) 4 := by
  have h := lift_ok (u := true) (ms := ([66, 83, 100]).map swapRows ++ fixRows 0 0)
    (raw := varsX 361) (T := graphGoal 361) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior355 : Lower true (varsX 355) (graphGoal 355) 4 := by
  have h := lift_ok (u := true) (ms := ([32, 33, 67, 100]).map swapRows ++ fixRows 0 0)
    (raw := varsX 355) (T := graphGoal 355) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior331 : Lower true (varsX 331) (graphGoal 331) 4 := by
  have h := lift_ok (u := true) (ms := ([48, 33, 101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 331) (T := graphGoal 331) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior299 : Lower true (varsX 299) (graphGoal 299) 4 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 0 0)
    (raw := varsX 299) (T := graphGoal 299) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior283 : Lower true (varsX 283) (graphGoal 283) 4 := by
  have h := lift_ok (u := true) (ms := ([33, 84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 283) (T := graphGoal 283) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

def generatedKnown : List (Nat × Nat) := [(506,8), (505,8), (499,8), (491,8), (489,7), (483,7), (475,8), (467,7), (443,8), (427,7), (411,7), (379,8), (378,7), (371,7), (363,7), (315,7), (504,6), (498,6), (497,6), (496,5), (490,6), (482,5), (474,6), (473,6), (466,5), (465,5), (459,6), (457,5), (442,6), (441,6), (440,5), (435,6), (434,5), (433,5), (432,4), (426,5), (425,5), (419,5), (418,4), (417,4), (410,5), (409,5), (403,5), (402,4), (401,4), (395,5), (393,4), (377,6), (370,5), (369,5), (347,6), (346,5), (339,5), (338,4), (313,5), (307,5), (306,4), (305,4), (488,4), (451,4), (376,4), (362,4), (361,4), (355,4), (331,4), (299,4), (283,4)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by

  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior506
  · exact prior505
  · exact prior499
  · exact prior491
  · exact prior489
  · exact prior483
  · exact prior475
  · exact prior467
  · exact prior443
  · exact prior427
  · exact prior411
  · exact prior379
  · exact prior378
  · exact prior371
  · exact prior363
  · exact prior315
  · exact prior504
  · exact prior498
  · exact prior497
  · exact prior496
  · exact prior490
  · exact prior482
  · exact prior474
  · exact prior473
  · exact prior466
  · exact prior465
  · exact prior459
  · exact prior457
  · exact prior442
  · exact prior441
  · exact prior440
  · exact prior435
  · exact prior434
  · exact prior433
  · exact prior432
  · exact prior426
  · exact prior425
  · exact prior419
  · exact prior418
  · exact prior417
  · exact prior410
  · exact prior409
  · exact prior403
  · exact prior402
  · exact prior401
  · exact prior395
  · exact prior393
  · exact prior377
  · exact prior370
  · exact prior369
  · exact prior347
  · exact prior346
  · exact prior339
  · exact prior338
  · exact prior313
  · exact prior307
  · exact prior306
  · exact prior305
  · exact prior488
  · exact prior451
  · exact prior376
  · exact prior362
  · exact prior361
  · exact prior355
  · exact prior331
  · exact prior299
  · exact prior283

def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (proofWord80 [(pn 34 587893593480888320), (pn 285694 165098146291725119)]), BitVec.ofNat 152 (proofWord80 [(pn 1918 905555577100968096), (pn 400672 576785456318976277)])), (BitVec.ofNat 152 (proofWord80 [(pn 553 512411912587969507), (pn 923222 936317764324675020)]), BitVec.ofNat 152 (proofWord80 [(pn 593 617250405795759200), (pn 932990 199038957962216780)])), (BitVec.ofNat 152 0, BitVec.ofNat 152 0), (BitVec.ofNat 152 (proofWord80 [(pn 4132 214787803101330432), (pn 286 542513141533511183)]), BitVec.ofNat 152 (proofWord80 [(pn 128 663727399636114509), (pn 657128 405374425990303242)])), (BitVec.ofNat 152 (proofWord80 [0x1c781fe0c00f001c, (pn 18595 478831366646271984)]), BitVec.ofNat 152 (proofWord80 [(pn 41 541554807794370564), (pn 10071 927893783609346720)])), (BitVec.ofNat 152 (proofWord80 [0x7fe0070000001f, (pn 1190043 334266902361927680)]), BitVec.ofNat 152 (proofWord80 [(pn 2759 13229985486098715), (pn 188970 797174346752892928)])), (BitVec.ofNat 152 (proofWord80 [0x1f800000000fffe0, 0x7f0003ffff000000]), BitVec.ofNat 152 (proofWord80 [(pn 4002 972347747252757394), (pn 228010 908069299994230784)])), (BitVec.ofNat 152 (proofWord80 [(pn 4720 60639894790209536), 0x7ffffc0000000000]), BitVec.ofNat 152 (proofWord80 [0x449114a2488200, 0x5e49280000000000])), (BitVec.ofNat 152 0, BitVec.ofNat 152 0)]

def generatedColumns : List ColumnInfo := [(1,0,506,0,8), (2,0,505,0,8), (8,0,499,0,8), (16,0,491,0,8), (18,0,489,0,7), (24,0,483,0,7), (32,0,475,0,8), (40,0,467,0,7), (64,0,443,0,8), (80,0,427,0,7), (96,0,411,0,7), (128,0,379,0,8), (129,0,378,0,7), (136,0,371,0,7), (144,0,363,0,7), (192,0,315,0,7), (3,0,504,0,6), (9,0,498,0,6), (10,0,497,0,6), (11,0,496,0,5), (17,0,490,0,6), (25,0,482,0,5), (33,0,474,0,6), (34,0,473,0,6), (41,0,466,0,5), (42,0,465,0,5), (48,0,459,0,6), (50,0,457,0,5), (65,0,442,0,6), (66,0,441,0,6), (67,0,440,0,5), (72,0,435,0,6), (73,0,434,0,5), (74,0,433,0,5), (75,0,432,0,4), (81,0,426,0,5), (82,0,425,0,5), (88,0,419,0,5), (89,0,418,0,4), (90,0,417,0,4), (97,0,410,0,5), (98,0,409,0,5), (104,0,403,0,5), (105,0,402,0,4), (106,0,401,0,4), (112,0,395,0,5), (114,0,393,0,4), (130,0,377,0,6), (137,0,370,0,5), (138,0,369,0,5), (160,0,347,0,6), (161,0,346,0,5), (168,0,339,0,5), (169,0,338,0,4), (194,0,313,0,5), (200,0,307,0,5), (201,0,306,0,4), (202,0,305,0,4), (19,0,488,0,4), (56,0,451,0,4), (131,0,376,0,4), (145,0,362,0,4), (146,0,361,0,4), (152,0,355,0,4), (176,0,331,0,4), (208,0,299,0,4), (224,0,283,0,4)]

def genData5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x88e0400000000, (pn 94632 376379146808328192), 0x813020, 0x42381000, 0x2f373b6, (pn 1029110 829866849429526602), (pn 777144 636326162826737691), (pn 364921 787324055461565770), (pn 325588 278447353365374579), (pn 44505 815107165780877600), (pn 567570 720387087816743380), (pn 98014 778574616899676938), (pn 456633 461404654258930021), (pn 1043996 94032337925354158), (pn 649659 876278882427213396), (pn 949508 398376847116083812), (pn 720023 792399531313283908), (pn 284683 136428156999803422), (pn 171666 802382324766936850), (pn 212685 951320091162797081), (pn 252744 630304105747731274), (pn 683315 861916415907439920), (pn 421900 440221267134433330), (pn 506084 161012540556498516), (pn 91814 937964916834605770), (pn 879067 812581754015155276), (pn 694450 167950214802056776), (pn 637692 739437411375125699), (pn 548037 959324602991780281), (pn 68868 706630431071591555), (pn 352713 711392772940663206), (pn 386404 349269104339964332), (pn 1105232 679054208496440886), (pn 441048 722108099911686958), (pn 843648 727493684342130521), (pn 392625 338405155682626729), (pn 690083 846964810937160905), (pn 305718 422823855070536840), (pn 445151 664701069562364975), (pn 155159 34852765568472866), (pn 1118397 666859917142364406), (pn 501654 787658339682917226), (pn 440071 963150577161833678), (pn 728068 311820396535060568), (pn 1012169 474889808637340779), (pn 202630 87078512006804885), (pn 20294 647662827153262745), (pn 160972 210485738837724305), (pn 52427 298144161781803141), (pn 496941 848737826594898610), (pn 366219 945725088564859198), (pn 1036916 368817110313112429), (pn 1004204 658450620568548200), (pn 483850 401052713107051660), (pn 277562 584400414094530977), (pn 256724 717940695522529411), (pn 190822 665157942222807443), (pn 173588 67439541524400530), (pn 458534 673470261128697138)])

def genData6 (j : Nat) : Nat := if 8 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (proofWord80 [0x32abae91, (pn 634569 375788148881497398), (pn 401754 716239474164585548), (pn 806595 817494440838343478), (pn 634721 161101297929816481), (pn 256724 718364222806136068), (pn 359682 661174542337127081), (pn 862322 476371146360814198), (pn 118987 287256865653159053), (pn 309465 590828608946275632), (pn 789568 890687025949349754), (pn 105688 700813387932129669), (pn 705768 981164324220720593), (pn 229731 40376653405815446), (pn 1181299 615250880441084057), (pn 630831 687207198824715860), (pn 950388 63851760120509506), (pn 642138 519354849064787945), (pn 719964 411306314299906518), (pn 419206 916349716617319189), (pn 11950 781914625860635167), (pn 493017 307841610484787553), (pn 681289 649392464092676499), (pn 171231 665995193793680137), (pn 1145954 428683863147923881), (pn 359311 790500359885358677), (pn 90403 60207115939368081), (pn 46973 28538580120381385), (pn 778675 718590392839866262), (pn 307306 958340459642062412), (pn 694371 361022722954120231), (pn 942764 979416956202325659), (pn 695462 77623411545104662), (pn 361575 345087965449237200), (pn 185641 143349452553231670), (pn 734722 310643646042099285), (pn 558665 636825520507592037), (pn 361960 544153100960219287), (pn 767413 905983741773109886), (pn 327084 434912655940617689), (pn 237375 427316452965009680), (pn 714231 239767305998195962), (pn 256547 394180743225202973), (pn 1025681 639235722208036041), (pn 78347 260064735898649180), (pn 1031510 616283714738678009), (pn 632081 307747223247132484), (pn 949501 707015107338511426), (pn 438483 312295167461520232), (pn 1102488 480759166877853207), (pn 475945 639184869650961188), (pn 313280 664511812507601243), (pn 1101963 371987285046175078), (pn 260999 23399489773264275), (pn 171228 945908980060557577), (pn 431689 67223857339133350), (pn 1083053 653331249112455008), (pn 392639 116170904935553364), (pn 44183 3374565573534959), (pn 785796 80737913803020696), (pn 439533 183774151292643161), (pn 396847 104443427345223716), (pn 598146 762259430133331610), (pn 714868 282213046994754945), (pn 421822 343818209115329612), (pn 774092 279481864144719774), (pn 630885 390692519119566433), (pn 558808 598846350636745060), (pn 361921 491606454322410127), (pn 257656 652308446059485758), (pn 441658 76901297768465877), (pn 473650 377649967979680050), (pn 669369 333100399144089338), (pn 407442 485926298756151685), (pn 686833 144474554045257105), (pn 238625 820778613776370207), (pn 878477 728148782598449241), (pn 632083 759953002650499077), (pn 1025999 240068763657381122), (pn 146292 362510670185921512), (pn 724991 149066372000146808), (pn 329849 727746363921389141), (pn 10013 853516431516305519), (pn 1100782 203924506967254118), (pn 110473 591741750428869078), (pn 98027 725796076203839752), (pn 452929 358033845720547237), (pn 475638 184734062823183073), (pn 109578 422348214178307347), (pn 190663 914505463608942975), (pn 781043 792629536776428437), (pn 461964 424506210263331916), (pn 685030 242331827054462012), (pn 648869 993668336899615137), (pn 318046 98537623129300278), (pn 703986 414180564372968524), (pn 860843 350130633208809790), (pn 459902 218695084095452760), (pn 629777 836003714884015732), (pn 362188 951218212268225225), (pn 253333 72899850176353940), (pn 1022491 229970083669964181), (pn 237523 395899408051930416)]) else (proofWord80 [0xc540ce65, (pn 64081 795734653650961741), (pn 558808 599936779483977076), (pn 362207 483257098003886797), (pn 270974 841312269084973622), (pn 459943 988429375271427613), (pn 473651 520999128645865778), (pn 969088 284230000910742741), (pn 702885 537884948072298758), (pn 119614 215310401701561545), (pn 457099 248689246917411629), (pn 696074 305135309023847958), (pn 253042 368728675754801157), (pn 685680 119985205167932619), (pn 205893 735087750748352081), (pn 722780 705539854890981719), (pn 497346 326047159979447085), (pn 14725 795195298021182581), (pn 1081294 390872436116965476), (pn 563244 34191900647120293), (pn 324866 179188971234153227), (pn 1137676 640939388993258405), (pn 359220 709701632978687052), (pn 90393 872722922858368145), (pn 56380 802536131388518337), (pn 763871 828234843443861832), (pn 307306 958476936101323852), (pn 694407 101757788612807727), (pn 640532 83361418152062629), (pn 228321 342387326295612720), (pn 361575 482588603232891460), (pn 223346 288450448642850086), (pn 780082 349917191951504577), (pn 478371 418998146098090290), (pn 359772 11187359981056701), (pn 87466 705434632031877701), (pn 760417 201973286621705613), (pn 473651 195617245086927120), (pn 883794 543307032275118746), (pn 481995 429802397097530948), (pn 1025995 524590339265422597), (pn 230112 78573172497384168), (pn 1182474 428875875799001172), (pn 555125 96753575452857909), (pn 685678 825486140103349450), (pn 1081313 990573289559004136), (pn 408587 685227615133655510), (pn 253037 643476043222799956), (pn 958139 625669946491743123), (pn 498545 566364940960048225), (pn 1011574 855626681935224083), (pn 171238 574576086838710539), (pn 540284 990471423128357283), (pn 310334 532063259496613469), (pn 90393 863821250817842277), (pn 54038 72811796262301096), (pn 790149 7936151574452551), (pn 359272 553391200241795152), (pn 987184 852668463305671725), (pn 716145 106560134055083665), (pn 686469 290028613447785828), (pn 361575 451133525750264396), (pn 213975 701549475911742778), (pn 748871 274215745780305), (pn 620277 762453924722594098), (pn 359735 550674514007888052), (pn 541256 607533457285745269), (pn 760417 201409804113179841), (pn 468771 892758970393529616), (pn 847343 206210886151884218), (pn 174088 866352268676012148), (pn 1025681 641207134011221193), (pn 78863 765782833205134028), (pn 1031433 353091457553230242), (pn 551801 77546058507736069), (pn 685641 477120961289798850), (pn 953808 906550322066565096), (pn 398847 241970235530629590), (pn 252963 710304236527510293), (pn 13122 127429803720313627), (pn 1103123 768341425078379109), (pn 1012164 578910959084984663), (pn 324861 492054498739000331), (pn 129429 739392353683922851), (pn 480912 782656201745131353), (pn 397656 659233977064904787), (pn 51704 501439225299479499), (pn 757383 199671654957351302), (pn 458422 685862658875929168), (pn 392158 352792146650680363), (pn 952163 378470927794644611), (pn 624765 142771115611545906), (pn 417100 119058028880814412), (pn 206744 290562294114594510), (pn 685165 185905439503173149), (pn 237747 621466789259823457), (pn 359700 818004066994041517), (pn 767413 978111910719322710), (pn 458998 250484644737287369), (pn 308358 894831035231867186), (pn 817977 240811433297097946), (pn 497641 660127194074675316), (pn 1007714 259853348118418833)])) else (if j<3 then (proofWord80 [0x650d10de, (pn 332063 318420085043435829), (pn 33173 69295597535892505), (pn 317656 937092794286411024), (pn 1049661 622327874710370585), (pn 98340 46487026719029604), (pn 912657 578603941855495437), (pn 79655 806472950221423480), (pn 724975 589130145273893433), (pn 472553 867269080474723908), (pn 950097 114009691158160579), (pn 551213 217431654786519780), (pn 105479 721750119039195472), (pn 324832 237406635643458340), (pn 923012 326555571002084818), (pn 476166 207057674942124133), (pn 105456 86455680681335127), (pn 22642 556730902680736525), (pn 993262 125974141336504656), (pn 479712 536183408151728217), (pn 90412 353373951907417235), (pn 65050 521122079146522393), (pn 700756 523013053108081991), (pn 366375 741227838992889429), (pn 90569 146345368163994806), (pn 988780 435638068350495141), (pn 30051 125538329941344612), (pn 361612 511026023251391060), (pn 258722 747507637293734693), (pn 668516 423745000082847109), (pn 478371 419524741986539826), (pn 322131 268337486040469722), (pn 483182 719683309716739654), (pn 363738 723096202122245209), (pn 317656 866162235133986096), (pn 1027882 944534709300061593), (pn 404002 598250199169783381), (pn 987902 423785345555903893), (pn 240125 126512142765605732), (pn 998454 631023575766099222), (pn 251932 35376498464266340), (pn 949506 316395007492432963), (pn 437874 694698032520065764), (pn 984130 423774231454501910), (pn 324829 929874757779018532), (pn 318106 712482669134941554), (pn 359958 653810830985474277), (pn 412705 46733584239713683), (pn 171247 795918708713230605), (pn 539753 563947378712889648), (pn 477980 848048278484103265), (pn 694856 809674124344708241), (pn 63491 745123694360671687), (pn 695913 887893200916335894), (pn 439533 184075001111709264), (pn 987221 780917667951232053), (pn 725257 681971342124410445), (pn 338858 921124639257468166), (pn 381645 653711008959120196), (pn 253118 390445413248325222), (pn 364809 239431502441512537), (pn 228164 394512466326066033), (pn 359888 574055774877200598), (pn 477209 333158522752963638), (pn 308814 371841742351197441), (pn 317656 794104595965349136), (pn 1012178 698025462629882201), (pn 250821 987185151210476573), (pn 1025994 373634679836730637), (pn 79511 683407167773524825), (pn 420674 789307185755410649), (pn 103028 634812988427687748), (pn 949506 174532048596968643), (pn 400685 645423676165542756), (pn 1026922 546582787380696534), (pn 400391 251819760090436388), (pn 317963 604293437248179539), (pn 405411 395179688653312869), (pn 1012150 455661520722811219), (pn 171246 716847448758210829), (pn 256867 888696854886799763), (pn 415979 682801146222580812), (pn 104856 143012498608806995), (pn 62375 671747433273767125), (pn 686384 262281331252026678), (pn 458422 740064510659884108), (pn 694431 399030935189015732), (pn 974749 994613044904408485), (pn 259090 511502652258704244), (pn 361575 581790555136930372), (pn 249351 837829633068290869), (pn 668645 568968738664232541), (pn 478371 419386202987794738), (pn 322093 222351674813001938), (pn 558884 778468026780080453), (pn 668036 213335573518693849), (pn 317656 714399947930060080), (pn 991284 40039883430118905), (pn 555127 406155143158552118), (pn 82148 842316420301210825), (pn 230485 587524310746858297), (pn 724976 571481937146177044), (pn 246030 299997796484067428)]) else (proofWord80 [0x53258530, (pn 1136791 953837525636989654), (pn 577630 201195330629359429), (pn 1031030 949112130139809105), (pn 240558 627163846310415297), (pn 1088299 201922619194959315), (pn 328599 44499690943747669), (pn 667051 592615807826539843), (pn 915353 152398239961378912), (pn 392068 914131246034013208), (pn 324829 936592945623962404), (pn 319867 845117089806356200), (pn 458513 716688348617197640), (pn 379058 185568840275018003), (pn 171254 426694818466665230), (pn 1068768 630773050563565976), (pn 381742 979538111116968021), (pn 704901 85759454113584403), (pn 69716 142533317923486433), (pn 634573 789111703788953889), (pn 309668 105888981198374476), (pn 685014 390153782264808506), (pn 988898 537576749922469261), (pn 610394 993890002436752646), (pn 361575 690158278069273412), (pn 277612 564018329673591589), (pn 760418 625138328677344769), (pn 624765 141057653341165891), (pn 322203 615546988959699178), (pn 784383 534818277521528902), (pn 6572 559504728743245018), (pn 398094 179625815542944050), (pn 1106023 54362695655205076), (pn 555164 371630659957020222), (pn 6572 569720244011422737), (pn 230979 5769680523936677), (pn 709941 479771568921270488), (pn 28655 92819676232210005), (pn 987913 737694005165507787), (pn 778480 670114320854455142), (pn 104880 509376010800093398), (pn 404965 41172484563473188), (pn 923902 188113347770257043), (pn 425348 885880461660611937), (pn 998362 87008516901916053), (pn 324877 487657763716010798), (pn 695829 80828934518099299), (pn 422505 798357965706454496), (pn 109883 481231482906037428), (pn 68684 260633745896258093), (pn 492635 678400095264771462), (pn 307969 888518686573151068), (pn 477224 569759856157886520), (pn 1102790 302458736789399065), (pn 638729 116225895651384582), (pn 361575 655818057907515972), (pn 268483 666022894182392677), (pn 761320 300125440666121757), (pn 29825 2460673452808498), (pn 322169 602972846130008291), (pn 479560 501176139074344500), (pn 120510 8338208783361543), (pn 549200 560976950217001264), (pn 1073838 106096855205252438), (pn 627430 714194008905144436), (pn 421531 464741953058464969), (pn 79751 439356350250107789), (pn 407120 35292973138005526), (pn 101815 814311191246344296), (pn 931503 138397387171836995), (pn 659185 536801508615401050), (pn 94550 187734563907985872), (pn 477200 39229573247350548), (pn 923431 796007067291029037), (pn 425383 492703247291212897), (pn 988838 657572532513922326), (pn 98054 377024154991137582), (pn 185833 956030719366569316), (pn 366429 422397108566177376), (pn 260118 657843030833552467), (pn 66677 618699011722590317), (pn 785717 548243192542271879), (pn 421824 940317936937952588), (pn 699170 466907481972032568), (pn 516957 993651626290820509), (pn 481097 373817104806287232), (pn 439533 892345469089431884), (pn 266175 229124672901669237), (pn 667723 800326640034526613), (pn 613263 379791080758577010), (pn 359928 517720818506600671), (pn 67570 875330382180137268), (pn 118433 614159562105095257), (pn 237376 720413588389677360), (pn 1053205 409318291971996697), (pn 626914 60048487153981460), (pn 118986 414885783223690441), (pn 79671 941697958811288444), (pn 118737 158250679369753747), (pn 20387 274282753873155652), (pn 949506 881146389995398211), (pn 571891 23795278110909541), (pn 90243 292382266970623056)]))) else (if j<6 then (if j<5 then (proofWord80 [0x501644c9, (pn 80172 225269931035640808), (pn 701077 832182654579071249), (pn 475949 149050233454351940), (pn 949508 790885735317316675), (pn 1086551 651046367817601640), (pn 105456 100088628567365846), (pn 404965 45658904320316948), (pn 925078 168237042495066002), (pn 425424 869506166513297484), (pn 105456 77479264732076371), (pn 171257 596647847060345103), (pn 691104 169816402729780577), (pn 421824 364325716969726809), (pn 387617 101977605544168593), (pn 73295 278975936591838734), (pn 700548 997423707912032611), (pn 421900 441012837161973397), (pn 90601 424834940342914238), (pn 63259 691524494085076365), (pn 625000 129412296619725157), (pn 361631 83316019841282628), (pn 291633 893908725061711620), (pn 923043 157322165591934425), (pn 95859 734903726992642354), (pn 322260 92926596355789047), (pn 21346 367996752572257396), (pn 939867 434008218365531161), (pn 317657 369354778450398480), (pn 1162975 354169416355141908), (pn 98016 76807577497621532), (pn 119300 11170714585425165), (pn 80100 724961078888645593), (pn 90112 594275759361903700), (pn 27619 622945101990170692), (pn 950098 843387137705059395), (pn 1004267 607233780129944213), (pn 996522 312336154192989206), (pn 400387 802043821892129572), (pn 320319 858136116869795666), (pn 359311 864846746667008857), (pn 379223 927048583588830613), (pn 324880 388009715706679567), (pn 247220 23046608181317985), (pn 359919 435302744424263773), (pn 104856 178897531321997521), (pn 71800 228534065419271377), (pn 233020 948040639259909475), (pn 309648 542285736326554700), (pn 685023 469082289382769724), (pn 951031 821268089021080973), (pn 638729 116437268166745350), (pn 361575 725624122445738564), (pn 287056 939009608676078373), (pn 665980 284665242785821721), (pn 549206 917189998847744306), (pn 322241 948843139045855475), (pn 101780 434413408075142710), (pn 25794 65422769077052497), (pn 237377 81755875894675728), (pn 1147932 606475191816801366), (pn 247250 91052430188400997), (pn 987901 849145357223814277), (pn 231149 673077198106723274), (pn 710513 341776348416987606), (pn 26290 232391717524362820), (pn 949508 290871810692686915), (pn 951967 636797163727431256), (pn 1003283 337054616543252503), (pn 477200 43592898705962772), (pn 924579 939302758008688421), (pn 420649 488918940585648977), (pn 988838 657589971890822548), (pn 246813 461109264580645647), (pn 166926 272816440565075299), (pn 461987 521552215100458833), (pn 694870 675215870265281716), (pn 71487 535229293974011021), (pn 469023 907760562502967655), (pn 420643 754294619560305756), (pn 392825 960100434904370364), (pn 497755 707387046383424902), (pn 185819 967621940353843557), (pn 1040452 793143477453156684), (pn 284792 893770825932534072), (pn 743244 201703480063849877), (pn 237747 622645726606366065), (pn 362373 430564658753388785), (pn 253266 255227348456887926), (pn 365492 47088437589259669), (pn 535042 933728806962577714), (pn 1139079 336310409475638486), (pn 274439 510953166995252597), (pn 704559 860041245101806795), (pn 306680 979132286924817348), (pn 1011584 669697620369955032), (pn 555269 68826734323947092), (pn 949508 191915854320051523), (pn 929535 295557301999440728), (pn 1012169 492508567318780247), (pn 329407 179698284154131236), (pn 320029 551536700841529107), (pn 419505 879713771531622109)]) else (proofWord80 [0xc9bd4da2, (pn 511552 467850400289861961), (pn 638920 445198898973420069), (pn 99885 167049400793569423), (pn 1003450 114875864161628724), (pn 989936 221818611236899009), (pn 330310 772985182826341029), (pn 94606 235970815371020276), (pn 293411 969631274378860240), (pn 720245 349181269362617153), (pn 85146 727784801007324417), (pn 340144 121719193245512691), (pn 148551 289952401500393336), (pn 583578 538054502335331617), (pn 1097050 674519384465404295), (pn 619736 948813620277655325), (pn 816619 446295920691293301), (pn 243941 848193328611967437), (pn 370197 543200392716011299), (pn 269207 697728371341859884), (pn 1062661 97021997169536243), (pn 482182 98433216031600461), (pn 549776 625614260734962485), (pn 310076 888826516847873234), (pn 30828 265806985175692086), (pn 121099 183683530663414940), (pn 473770 112979018987024721), (pn 643648 145175440334307333), (pn 1195640 812583209491691287), (pn 815733 894481002009177181), (pn 240399 640933653883527536), (pn 356471 463037761658078627), (pn 212532 381573574075618836), (pn 832418 489991805432256306), (pn 869315 833611969825429578), (pn 889385 746714646735571242), (pn 232886 288941466103628965), (pn 930991 685881411373470347), (pn 95860 902909276461976024), (pn 371046 102424534564808401), (pn 254005 346520512307435780), (pn 902667 294137024569822994), (pn 512727 581739110432836680), (pn 237300 202824492678082842), (pn 948315 286504443610842195), (pn 162941 479926583206744324), (pn 641139 297924834437644946), (pn 90030 236302087998735816), (pn 190094 996704377778210080), (pn 80276 192801614245907582), (pn 18319 832905898096603616), (pn 70622 730228011192993616), (pn 275406 506391042624658512), (pn 1066203 952959175870147971), (pn 496350 62572940528036365), (pn 323071 901333201717986355), (pn 1141005 836915642212098246), (pn 935917 534067798789063421), (pn 112465 26464465861151660), (pn 439233 484076365056060817), (pn 505499 899971448576454341), (pn 529704 117804763778820373), (pn 229786 857588529073642578), (pn 616583 893519787176251713), (pn 47155 607127203057026272), (pn 183309 117618063033832176), (pn 711982 362006994897618946), (pn 260055 319903788866802696), (pn 700169 379229094946018336), (pn 533664 883709171911868541), (pn 320385 253599619019702749), (pn 69958 539338472306968364), (pn 269207 535572390839327632), (pn 1034323 655163569803127235), (pn 340491 213306417471657228), (pn 681861 59209773019696176), (pn 7029 60775504611053751), (pn 26787 915379331145646776), (pn 101838 350626575388314192), (pn 386100 158943304776165121), (pn 250461 841906602821587716), (pn 661795 470618462852884497), (pn 78048 474827428502966335), (pn 915992 645255684949934317), (pn 34536 142395126783738492), (pn 88553 667775178537436048), (pn 42503 892436668267038097), (pn 237377 260806956178000144), (pn 1194856 508585404541431956), (pn 630823 616872815510738964), (pn 118986 416855901902234825), (pn 80188 396488827150287852), (pn 104857 707650920290998480), (pn 473734 456645935589758548), (pn 949508 898971899143595075), (pn 1105441 98962348377352272), (pn 406226 213747077889150032), (pn 477200 45809531057706036), (pn 320698 245912207838744484), (pn 419479 273591764668737360), (pn 105160 938582384203681107), (pn 174799 659756336316437263), (pn 766662 267311683459254627)])) else (if j<7 then (proofWord80 [(pn 102 578700464104292881), (pn 1059073 122201154225710096), (pn 754 28679113634013248), 0x1430150c04000028, (pn 1059176 664717577039382851), (pn 5466 18867739570996772), (pn 227266 494589878109470720), 0x2140408070543010, (pn 47593 762817620461225477), (pn 25991 541477007905798150), (pn 609205 520067352480129104), (pn 633905 178583384220254342), (pn 289300 441609050735907888), (pn 151126 684710398513522880), (pn 350489 290324742405902400), (pn 681503 724465639040519684), (pn 12064 621829703427492419), (pn 6058 620688925863260805), (pn 37936 455428210529675408), (pn 1060182 877312396419999824), (pn 349825 389091090568577024), 0x2414190504030, (pn 379192 719383339062008048), (pn 321786 161231681269399680), (pn 11515 380140382389152260), 0x2070409090400, (pn 95334 254500043752017089), (pn 381337 159858014105117744), (pn 75557 863726536025323536), (pn 1489 592598350565232704), 0x3404050c04000, 0x90c0400000, (pn 40624 558909863582239114), (pn 95084 103741805980286976), 0x90c0400, (pn 113706 883412192725831680), (pn 11829 51902422260269312), (pn 665 530980934216646665), (pn 56742 195572609837432832), 0x50504000000, 0x20981a040400000, (pn 41 721770604608094208), 0x2, (pn 609203 723034260643316237), (pn 306953 821386544756556430), (pn 21908 404437274863861760), 0x109814260581, (pn 4761 728225087840224129), 0x2824100000000002, (pn 983432 820057603615752192), (pn 59 969932638065524736), 0xe0, (pn 41357 757910439573857296), 0x34040000000c0e, (pn 343561 385000803613018376), 0xa3810000000, 0x30241c09040, (pn 718098 327856017339056128), 0x286, (pn 4722 517357855208636416), 0x0, 0x8, (pn 198432 563031091922866176), 0x20ce238200000, 0x8220400000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, (pn 39 373305236574908948), (pn 306377 964263369800746248), (pn 24017 977120176054928096), (pn 179910 375888181872036998), (pn 757067 210497248660039216), (pn 1105137 541040941882749120), (pn 560148 285930990777359092), (pn 1017498 927465680091441891), (pn 407796 178413863986112653), (pn 308908 261704843952295988), (pn 442178 620467289897161934), (pn 105832 649513697878020902), (pn 420895 330566497874365545), (pn 467571 196216754453950717), (pn 636563 946880022632252022), (pn 85897 661164838625412440), (pn 173564 696155380284916575), (pn 769622 930509352443780472), (pn 659865 238484014786581971), (pn 219395 381119196034422544), (pn 868726 6325535480568610), (pn 1007460 619523617745888715), (pn 204708 331458484747208748), (pn 138729 531818042172240047), (pn 403636 358855004129788599), (pn 404512 649011584157846195), (pn 402926 21812224453388837), (pn 381525 24071271861757429), (pn 189653 85699114463823316), (pn 191866 100334421326033743), (pn 616127 282554375720346936)]) else (proofWord80 [(pn 722 327981785478109345), (pn 311676 188019557298339840), 0x21404000002430, (pn 85381 962051066408230976), (pn 306373 302908800632914689), (pn 117875 57255264972604676), (pn 66557 16239919469773232), (pn 341458 546811386190004545), (pn 681503 724475538334713092), (pn 11898 438157918812504064)]))))

def genIndex6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xd, (pn 1171402 853214915697442979), (pn 1171423 724086769403132070), (pn 698763 746904051789393941), (pn 371113 462050739011944672), (pn 538714 136036093251721088), (pn 1133593 701626054915202132), (pn 64998 311487490957700092), (pn 8816 399190258667608518), (pn 1190052 598833326673693800), (pn 81854 682522249111141891), (pn 1018209 146159527857361624), (pn 916787 342220570763618240), (pn 456045 272984521555115523), (pn 56713 290203545633484801), (pn 645067 462847410304003652), (pn 141722 27630809865853488), (pn 378126 385847054238881878)])

def genData7 (j : Nat) : Nat := if 19 ≤ j then 0 else (if j<9 then (if j<4 then (if j<2 then (if j<1 then (proofWord80 [0xd65dc930, (pn 1071591 740825750401278809), (pn 412114 353146059507081329), (pn 551878 545270922531810474), (pn 125174 752660865545942933), (pn 2825 245835888675728645), (pn 230774 36168087271348611), (pn 378751 198409062112086168), (pn 521342 835872238721089960), (pn 47562 748044810573204535), (pn 238622 694982682183530580), (pn 81181 583487051300739993), (pn 318173 194622631219561672), (pn 719836 128861844409273505), (pn 831341 892635184605516876), (pn 260660 41906822127701272), (pn 45106 962433962543818331), (pn 365160 330541114224729130), (pn 1070085 46126533703576998), (pn 733455 308246813008860788), (pn 362268 287602436878029645), (pn 643824 24576456328454438), (pn 127089 302684035786289227), (pn 13107 594815905388368653), (pn 513588 198778757627393537), (pn 478364 836692994640414387), (pn 727602 263200490311544122), (pn 181124 934481227950021037), (pn 45826 943609414775887123), (pn 214400 881560955755746878), (pn 25462 34316019561695638), (pn 823482 689024221382918858), (pn 614610 523369392498312013), (pn 817166 886800586863109464), (pn 694425 898257192159911128), (pn 551821 976648423488743497), (pn 634487 423757847639059514), (pn 817746 928147672972334339), (pn 74617 884489379751502181), (pn 738829 875980896056279421), (pn 118577 198835745866684454), (pn 342481 306282569778642524), (pn 804584 223927115964289828), (pn 920740 562813599690468929), (pn 634209 657069330674324065), (pn 588401 279188437665261954), (pn 785269 100361676956975294), (pn 361815 346056024598757715), (pn 171240 635038925448568614), (pn 363738 416849500707531154), (pn 158136 527635237535978277), (pn 158799 482579560115259696), (pn 898661 819456326556291521), (pn 90403 95276775310401631), (pn 180689 698809346102153353), (pn 691263 818892244264169363), (pn 156763 190021906619516105), (pn 230183 986093045455505808), (pn 421824 345687040494560408), (pn 449330 499619122210654626), (pn 649659 844950822083644463), (pn 260405 885804328599761764), (pn 81179 278355469462542233), (pn 702476 461205886780709384), (pn 719541 71457174023816905), (pn 1099926 487403123748975184), (pn 220164 971164703328036183), (pn 476169 460145614415373911), (pn 366382 390709029631601074), (pn 796186 637606305274333927), (pn 957142 287787293964357938), (pn 321925 312901657460568933), (pn 865757 90146318696749352), (pn 102961 916691320524370604), (pn 275751 754381195568829450), (pn 867904 386881691347151389), (pn 478363 920323146789033247), (pn 476487 872173264478195378), (pn 793725 31434069341797650), (pn 57752 763622318724569427), (pn 197874 497664202454129028), (pn 1031621 239132196046670228), (pn 1149396 466767096363916552), (pn 869622 424126107776500333), (pn 1147741 205527025975527257), (pn 90494 487314608058349289), (pn 425335 102479176182189705), (pn 702957 406119548874878133), (pn 53018 704139331479684298), (pn 518035 602437440145872775), (pn 420644 110925733623391542), (pn 1026414 992026772292977198), (pn 45240 559928772515762044), (pn 694459 958125269440084), (pn 917277 210240650962253386), (pn 613272 673777535964394113), (pn 132102 186615335382755523), (pn 814175 35031948643340522), (pn 347147 734594429625917632), (pn 171249 494098769355500932), (pn 630528 200012114921832466), (pn 158127 299544294342581036), (pn 314888 917484750846155088)]) else (proofWord80 [0xc9847f65, (pn 191063 93154015345553574), (pn 84957 930507408976622204), (pn 89292 61405070971687176), (pn 1203196 991952726573788685), (pn 549051 483317411072541823), (pn 475632 421287666715135162), (pn 180962 384252220020506546), (pn 284133 800678787012386195), (pn 193594 611535908280719646), (pn 44683 842924998265063812), (pn 601593 875287681090227968), (pn 883828 615941259081861695), (pn 841688 248181136447407961), (pn 89890 896174326890176473), (pn 66213 744733840837126248), (pn 625697 839276801625295882), (pn 456171 993095098139354179), (pn 1171848 486196708915840304), (pn 361575 770158538043826681), (pn 94830 190588377805529128), (pn 493632 768812279191895130), (pn 122940 138049811853153060), (pn 925310 41098518387369229), (pn 20302 15385721490739809), (pn 1173877 407031725896386208), (pn 492482 518004439211127034), (pn 392731 800897615914096979), (pn 173619 110466856072805669), (pn 363719 970109549605333394), (pn 462581 292470503720522337), (pn 239185 710036834867005712), (pn 1174875 204668239942075225), (pn 379057 812396678899603580), (pn 251710 602633441198713450), (pn 766903 646173903240576418), (pn 918946 202732658714609037), (pn 80101 185678800089696611), (pn 309668 159979551326364808), (pn 581542 930585016680618800), (pn 45208 496686121519106109), (pn 690769 473186424665198948), (pn 949508 486220578090917529), (pn 468991 625952670574641864), (pn 720057 472866787194259363), (pn 814223 315312642680775756), (pn 893021 193934488224356564), (pn 475949 124329454525621854), (pn 667169 794293415784770562), (pn 956730 682192189445050156), (pn 838995 618523576777674085), (pn 362378 996196654696600409), (pn 1021019 588657552818614950), (pn 445330 148355708218354857), (pn 843691 345884454948721423), (pn 182727 444518846978209173), (pn 549210 54955777043044243), (pn 419522 33000483112274585), (pn 491685 92939631641741740), (pn 506075 221091419375946901), (pn 71549 275645381865428341), (pn 667722 324700547871713687), (pn 695600 658251091127376586), (pn 836562 13690881931805635), (pn 786480 15910035445580876), (pn 694462 609201906311093395), (pn 548111 746762030620288584), (pn 639627 895963298143553926), (pn 1098413 834211216430670915), (pn 874339 616200503062741364), (pn 361870 851643897139044825), (pn 701063 987897120345462824), (pn 493623 797332993054403786), (pn 127144 338371824370923284), (pn 924166 235405271803782365), (pn 303722 258630161874950689), (pn 1026293 38760668546883770), (pn 795433 355778314016993514), (pn 541795 472186423926806867), (pn 173614 534320386349757749), (pn 440735 127179146040355218), (pn 613111 349453926371596906), (pn 883788 878896657334652192), (pn 1092217 503438678640912204), (pn 104856 164851213132142707), (pn 479560 500115976479678683), (pn 653490 722896469077801394), (pn 522710 140169573893539213), (pn 79808 341571538322771299), (pn 441894 997890834766128296), (pn 544060 16384921185989038), (pn 951891 322897013085064249), (pn 540981 911378269535065141), (pn 685645 79073918124825757), (pn 487825 747218424482346724), (pn 764773 587420544585584306), (pn 183499 169009450038944844), (pn 874717 992676290460077526), (pn 328485 991955035619190812), (pn 521366 764284242691943210), (pn 1098419 569497190987673142), (pn 848488 798966576664909171), (pn 341056 863076016212875096)])) else (if j<3 then (proofWord80 [0xdd30b2ae, (pn 649712 441486882014142316), (pn 929286 448842824394581316), (pn 956236 774150876756424289), (pn 181019 280501428372316773), (pn 296798 746176417034874816), (pn 210322 64470341753844383), (pn 513391 530827086185291799), (pn 324856 220646786459062198), (pn 413324 454465946241764274), (pn 478118 375869284587395883), (pn 907515 935275307006023986), (pn 752860 553523161799169248), (pn 110473 694527849465557327), (pn 860863 812101147109978154), (pn 126420 65838631993485275), (pn 168892 374626864721323473), (pn 239059 178931879740173713), (pn 1060582 60686401299737753), (pn 376429 411788427711924464), (pn 52580 516117173188709543), (pn 1034820 994645618713704469), (pn 1025687 351691593787003839), (pn 700715 8674763161483970), (pn 719256 12319981243588170), (pn 231009 323975621865185616), (pn 184156 783187322948543704), (pn 404081 737431073016621586), (pn 1197541 968438467316866058), (pn 636048 923352486978463999), (pn 964225 914072530109716803), (pn 321784 945280775432208358), (pn 110473 591751689810776230), (pn 84995 128903460209029899), (pn 766877 864729460500615944), (pn 1207969 933709878010414541), (pn 312933 160309734989468799), (pn 1085413 721966935939943593), (pn 793689 581067843790323698), (pn 1115410 530245476734095569), (pn 42497 529055084625787254), (pn 118986 409324021679532292), (pn 603980 431519008010580751), (pn 116437 145513819329841727), (pn 1146580 51441176154834768), (pn 987140 600752025207119865), (pn 482040 321560283835428456), (pn 625711 656294894745418931), (pn 8165 598644071686411534), (pn 301985 610938909196178823), (pn 420641 753571981722805535), (pn 1177162 644502618562937772), (pn 493570 300235275115204604), (pn 732237 932821151167403556), (pn 312855 801147435845680717), (pn 639002 278890556115096097), (pn 150990 493453802138445504), (pn 1125288 606213471719985295), (pn 1192749 79363971865272375), (pn 99432 558351294255876094), (pn 328340 34266143428504354), (pn 477548 812401800705736482), (pn 924041 871454151462162016), (pn 679957 6681018506121569), (pn 1002110 310546617590913095), (pn 1200763 485678550586536059), (pn 842963 167833245355090941), (pn 234830 234278618088232401), (pn 229329 110282937683803799), (pn 460801 162789329336296096), (pn 339833 86330593095896174), (pn 954109 495531954643226659), (pn 1186231 328937281931589445), (pn 666159 192872543953752573), (pn 721868 803574586240897666), (pn 719127 178385247628230348), (pn 382125 51400925595971920), (pn 169916 471110043535631895), (pn 478456 700315562068255249), (pn 1197569 368038158149815202), (pn 474750 590920162109688062), (pn 964185 627122062930055026), (pn 321784 657022662901792613), (pn 1172715 825489454515790252), (pn 84958 200371542897963772), (pn 49717 454298774460490248), (pn 1203243 81369804993035781), (pn 318024 460549267657393279), (pn 480359 399458753813613242), (pn 179781 794038602338025394), (pn 1039564 427136177050705169), (pn 42479 64157591831566702), (pn 25757 177260640545180036), (pn 601615 803098625039185166), (pn 758642 93132442910378559), (pn 844052 890185985580041820), (pn 987140 528623659239415769), (pn 444224 568266756095815370), (pn 134576 309635728781864111), (pn 3452 455531033453343810), (pn 300803 861932669968733061), (pn 441892 402463692350431519), (pn 1026192 766406746975092910)]) else (proofWord80 [0x1d614c2b, (pn 1110396 726235312542848868), (pn 949503 456158136047637999), (pn 714877 278224178628801124), (pn 757197 221261259414632395), (pn 833674 279760981329523268), (pn 207178 608296426951402904), (pn 551503 509888427846313557), (pn 1131419 308852340447169442), (pn 474751 728065882474220279), (pn 954820 303982577481817394), (pn 321930 211138581852158949), (pn 110491 471639794504472866), (pn 103589 15781771686310476), (pn 13735 427100273410102538), (pn 1170135 688214086076147161), (pn 232948 645448653839369595), (pn 1079489 972960620044282000), (pn 784317 480468315189198322), (pn 208861 287294414330682643), (pn 202910 198783334458259717), (pn 1026898 873847824131704965), (pn 583910 373966812546382594), (pn 723261 522008932182409917), (pn 845814 517099191655953996), (pn 684945 391167401371983577), (pn 650823 205362266952902234), (pn 25888 138394746370354370), (pn 1117303 297930924284650562), (pn 895828 377590721053875812), (pn 434811 300447144144699742), (pn 1026922 546569552667259438), (pn 196374 482413272572276588), (pn 882060 549034643121295896), (pn 617406 965485092394743387), (pn 549206 915999719133647393), (pn 447912 931090361285815571), (pn 775234 38090361674993839), (pn 513060 344831549302409683), (pn 171236 347639670492387254), (pn 369069 220485430827207058), (pn 157587 735020121180855075), (pn 883788 842376429487573312), (pn 828416 493048759482881889), (pn 694856 764930011378780247), (pn 596663 922979650572789483), (pn 123397 42612006495202239), (pn 183004 277941383147766985), (pn 78785 799311227224448914), (pn 367573 588191623750248600), (pn 413028 325663191870654958), (pn 656890 960781398520316971), (pn 883796 365831064017729380), (pn 987872 575727082267612607), (pn 700710 469046613649918700), (pn 719404 450944991604957130), (pn 219185 519510309165687884), (pn 809869 901096395587151318), (pn 401645 619358269144408597), (pn 895273 332396005434493874), (pn 635312 132173061978065630), (pn 350355 234523306019652982), (pn 359693 3797014516162533), (pn 1021019 736635950166880936), (pn 101523 196406983790949036), (pn 51588 145446995925734186), (pn 905710 835588855611606557), (pn 478364 65557126603998559), (pn 1078331 344322146937278130), (pn 784309 339648227807506386), (pn 1114677 555910682123262292), (pn 50743 151036141642701141), (pn 1026290 383246457607858565), (pn 450490 636251648913870094), (pn 843644 942020952250958511), (pn 693821 445083992756152153), (pn 89918 567133210701025241), (pn 501112 813787198642629738), (pn 23591 482904985624108203), (pn 3276 752655919978263618), (pn 601844 351061782575333766), (pn 361575 350540407162413375), (pn 725106 436422987817255720), (pn 196070 327407927736967116), (pn 916380 682041685115508036), (pn 918485 511418721426466395), (pn 629270 396690759638587937), (pn 300337 67796865848911811), (pn 153634 67853926644928671), (pn 966001 548232690750316566), (pn 327069 937846030976438246), (pn 318802 995523528174873116), (pn 912589 904828809504878384), (pn 657154 342305463108177168), (pn 754043 102483465607944261), (pn 90393 837213986996132175), (pn 899047 492662922884951179), (pn 653554 233575406417258463), (pn 211393 528857505614558609), (pn 239060 337489444443778962), (pn 460823 70618157261179033), (pn 376576 555361379951298608), (pn 956913 697604816687352999)]))) else (if j<6 then (if j<5 then (proofWord80 [0x6197d876, (pn 63268 887758099574467078), (pn 450429 720565357380123339), (pn 116437 685366279373112111), (pn 834303 758376203386847581), (pn 89960 65343002922555350), (pn 406261 24864364809743945), (pn 634555 735197022444841659), (pn 59798 10255111821345987), (pn 150175 786495890941387126), (pn 434831 10565812331372943), (pn 1022199 963654442464623400), (pn 493602 542910015752161259), (pn 315360 430191445975052596), (pn 316369 931762383368212037), (pn 624548 30767529598657057), (pn 600207 195361492563338115), (pn 189660 630523942965428415), (pn 663543 690334510123077841), (pn 171240 941371661039984558), (pn 309450 550358706287070114), (pn 479296 636894574478874400), (pn 921567 666293181979679026), (pn 903678 540647874006061145), (pn 90412 319775255385376863), (pn 785223 8886036013526185), (pn 690083 371382042003779537), (pn 154716 195922501143381465), (pn 239646 30372384756197268), (pn 328557 571625692184077448), (pn 451544 392348660405554210), (pn 951891 301156435432457263), (pn 959314 505590552161194308), (pn 949504 586499932427524059), (pn 709758 380842275981329094), (pn 644002 230508308027665865), (pn 824202 408137559075537732), (pn 225255 966990292114367696), (pn 475945 650472440791967255), (pn 1027416 294493223853910946), (pn 181965 553306110857907175), (pn 959535 752830995220779314), (pn 359778 318300577693823973), (pn 110474 466064094095127078), (pn 414674 978697459883700780), (pn 237973 978113738061681419), (pn 1094568 583102011767622033), (pn 237523 707082167064036851), (pn 481206 722453246687496345), (pn 179889 15584306829130162), (pn 548438 750073936188628243), (pn 207319 42076892261570869), (pn 704559 856467562622888325), (pn 1149390 341497761124102784), (pn 763291 86401117397271287), (pn 238925 869989976060528208), (pn 987193 418317408973716313), (pn 322767 528108880801441354), (pn 27963 270176275143949442), (pn 673862 323880378198336770), (pn 1160282 490253685760090438), (pn 361630 823911356881338745), (pn 1026023 560257270716998438), (pn 198447 686987551662455756), (pn 803035 923529570648610389), (pn 13834 97726865085939285), (pn 610911 428260867961758309), (pn 561838 682668788283812544), (pn 785278 317400969226302139), (pn 588581 322251607513129430), (pn 400274 598691527850548666), (pn 408565 230525652476685098), (pn 479151 392420385818336042), (pn 841287 580164680890815794), (pn 882725 877792515047658325), (pn 694580 75625620640802907), (pn 1125129 492051213656142025), (pn 693033 715667466924338651), (pn 213727 348228409844254085), (pn 230047 947759055520824726), (pn 401810 817253873689953928), (pn 415242 623593761679985440), (pn 734519 472057550833402923), (pn 1167212 768412105085097828), (pn 61698 584338684654786043), (pn 681825 398989043400454888), (pn 724144 106762260397620680), (pn 228069 961339244370789188), (pn 207547 324606115653510263), (pn 472553 751183762799601173), (pn 1178532 14010975588116658), (pn 616717 879468741912234747), (pn 959498 789466558130673939), (pn 321931 364060035975314916), (pn 1021318 275755771293120930), (pn 103736 517535890250068523), (pn 766251 832812077324199178), (pn 1184344 274549783471410649), (pn 90982 506433985909491069), (pn 474439 90109639744744600), (pn 793762 645915146119200434), (pn 281326 869178088313475155), (pn 51849 829437835107588378)]) else (proofWord80 [0xa4208992, (pn 159298 301317026149784328), (pn 921568 927565497307023680), (pn 1045637 763821291046782945), (pn 407392 556933764044331374), (pn 855292 986656003568414922), (pn 766899 953891265951348570), (pn 343582 437647803231778245), (pn 306306 607690627564674371), (pn 460801 163123030837823640), (pn 518980 807080248736530476), (pn 838413 865256799492656182), (pn 1145778 231110246395369029), (pn 931244 347807373151591278), (pn 417216 299089740660681960), (pn 724545 908879728130766540), (pn 210947 914600107099182156), (pn 863511 593819725799055509), (pn 478456 865680376089683547), (pn 516617 215234865428589618), (pn 796187 696888658292575612), (pn 921747 635982368562844209), (pn 416563 424557197295009370), (pn 77417 26450417079067042), (pn 127163 89941805601239244), (pn 49081 51624173899420429), (pn 525144 705761876477641945), (pn 398093 832118883509175991), (pn 425370 750873740867207841), (pn 812740 370705469276116909), (pn 48190 2318342399233110), (pn 63136 535179554065999493), (pn 705777 919549747375778310), (pn 752518 86870619111768778), (pn 683084 805298284679973695), (pn 532661 410297427265127516), (pn 987214 223416486619357096), (pn 548260 527670948144556073), (pn 635133 58353727299111998), (pn 59650 4231770859574531), (pn 298411 263719811758562566), (pn 361575 566426697803375007), (pn 719645 781342455981703790), (pn 196097 995842902202306508), (pn 32699 277398759058511412), (pn 317564 161287984186385921), (pn 558730 48197270891600417), (pn 753649 660255413971586496), (pn 824228 663212987019243727), (pn 945414 637035212134310007), (pn 324722 584789497218099166), (pn 460223 553281883003480602), (pn 158779 801390755840519438), (pn 657154 342727114968861968), (pn 980706 893828419520661317), (pn 90177 142222948525312103), (pn 1011049 99242176126267499), (pn 664112 715357686522459115), (pn 12897 185832555116979401), (pn 79388 711992260252267799), (pn 458421 803300103856776328), (pn 489913 927411282426186032), (pn 1110537 921059072520702003), (pn 1053765 907064960346871828), (pn 950391 202471053701421549), (pn 719214 850400034977758376), (pn 724435 226195922744309449), (pn 228953 97592465726002252), (pn 849345 797675165538804184), (pn 475986 7404267037075481), (pn 1121698 197893371177004066), (pn 475490 748437023127833846), (pn 923901 254896383526474034), (pn 322077 489496790604872545), (pn 109089 519125305814980804), (pn 122439 713687382565695196), (pn 51514 363457561828332332), (pn 1164426 565038462116984337), (pn 237376 439124825324754551), (pn 1080692 489230358553455776), (pn 784390 39627959353162672), (pn 1103604 605065702543871121), (pn 61072 820990897635055716), (pn 998509 300903188198475910), (pn 563401 916042165491447554), (pn 879067 617480731366048571), (pn 787678 773916886141338332), (pn 397802 782594507873557971), (pn 481818 744475914113936938), (pn 143735 91151953975964230), (pn 1098847 619788604172342531), (pn 262993 652454264107508068), (pn 1040452 633348506903519643), (pn 1003320 235337145243321128), (pn 493605 999284053856210410), (pn 240872 443389375531832884), (pn 317283 37739679536774741), (pn 638931 879676173137715809), (pn 717365 456288486539440306), (pn 824228 654527386594914507), (pn 1118071 837973149749107031), (pn 324721 473032728753497590), (pn 459939 331953562504694570)])) else (if j<7 then (proofWord80 [0x4c940ed6, (pn 917002 173844526872254770), (pn 378884 227221507301403485), (pn 110483 401257353090734380), (pn 140145 73908128958228715), (pn 164740 482803299193197358), (pn 1013605 679247039168541965), (pn 158351 128016281657775979), (pn 380582 77657166135332513), (pn 765569 671581955159995304), (pn 1103607 59825462816952529), (pn 69924 952163140870198333), (pn 1025958 58196024980834695), (pn 487895 8078868714756840), (pn 721417 401170482043339699), (pn 788229 556252486443169356), (pn 396951 926241043505338835), (pn 329779 600090635597097009), (pn 34797 771377971005475626), (pn 45907 469101461367104579), (pn 821439 6527772384184711), (pn 421822 757124162444206550), (pn 1083590 944364052853207716), (pn 196113 922153300211460972), (pn 882097 462234285247910693), (pn 17371 134503146862523933), (pn 478371 635984954911461921), (pn 1014559 777981759919672250), (pn 180787 845410002974356203), (pn 506084 746113543062248723), (pn 171253 639309327679387061), (pn 441048 721265483659516810), (pn 462013 933642576633166638), (pn 843689 80039276323081536), (pn 1104641 388370055137150805), (pn 704901 659427955584444531), (pn 1103281 774848184576876683), (pn 123405 229267448513182194), (pn 910128 659064918940005769), (pn 79833 690083275780716896), (pn 420127 209385955356763272), (pn 547012 643001385786978476), (pn 583546 738288301953926201), (pn 1033288 797924434151855684), (pn 949507 452680060851854557), (pn 558675 79308452568998594), (pn 719929 552079810454253233), (pn 825419 929363443743277892), (pn 272620 304002812856457431), (pn 475876 486474753851828252), (pn 1045475 658067288108329766), (pn 1070067 49741244756528735), (pn 959395 208997762601655652), (pn 359960 164637544676798297), (pn 110477 924306849513519654), (pn 134558 18336742781734124), (pn 126519 332153673417053198), (pn 298462 316248082246170005), (pn 232875 803113339590674207), (pn 480912 782656420598950065), (pn 803327 846653026628243372), (pn 810379 486988999188633812), (pn 65998 464621169904400484), (pn 382571 940991944863295878), (pn 1191836 85628674977304076), (pn 763291 389814580897399678), (pn 227415 92117904564749400), (pn 987232 327095743731056408), (pn 94694 218176313400862792), (pn 637452 610636316302870711), (pn 49614 976009344067318851), (pn 592399 620420346973651332), (pn 361667 869817141219976638), (pn 415975 894450756592517670), (pn 342500 219925597567115052), (pn 48562 864814711472493348), (pn 318697 780485542590244365), (pn 25254 965650679822721633), (pn 895331 519745973166432451), (pn 180787 816966466075955422), (pn 812439 330210183848742291), (pn 171249 912016038486699838), (pn 137877 329652892656118690), (pn 480444 896804330739834632), (pn 723336 720965447242322226), (pn 1050519 189024580052072524), (pn 713464 970986763531229295), (pn 256800 785767926892078667), (pn 49026 607057595274114971), (pn 192467 322562429444437397), (pn 240221 320428588191436167), (pn 366670 889142740350838937), (pn 525180 908464850709431206), (pn 425204 493640918571764791), (pn 732236 95378373398861892), (pn 950097 134013596903545805), (pn 634209 731622478952532580), (pn 719851 187691459693110977), (pn 182606 798180437059793996), (pn 867041 773465347973926328), (pn 27470 867409100600387163), (pn 968737 795735655173876770), (pn 314488 84044591765130716)]) else (if j<8 then (proofWord80 [0x7b358d25, (pn 420644 520710127239718380), (pn 998302 134930882601730214), (pn 354319 533570768022599273), (pn 841885 234368270084674341), (pn 622599 304130856396449181), (pn 303874 588544548939598465), (pn 1112528 42130296148248707), (pn 190822 897548219619029237), (pn 959268 492981218929235990), (pn 324733 539795537681742549), (pn 685154 791838395542981130), (pn 462401 400757356978846414), (pn 763483 753796196993714499), (pn 1156594 887237494013518925), (pn 699893 380801094434072698), (pn 555195 570244376234960586), (pn 49029 848717284449729850), (pn 673853 546885935241840005), (pn 231191 465747640418737462), (pn 384065 67773051076789920), (pn 575345 113092224565555372), (pn 800630 335146124741004348), (pn 1033325 689108487846106708), (pn 950393 794837887926558317), (pn 478685 317914583447974568), (pn 724767 212315129209108145), (pn 210911 587492379451793740), (pn 286792 588931193932044627), (pn 478456 872295018344883742), (pn 441013 306442445329558538), (pn 956730 686695789542182702), (pn 839044 68248372286690625), (pn 360020 115983478792099672), (pn 1012150 158456611985330342), (pn 143393 699475083611581546), (pn 842401 154267673215947022), (pn 1179321 139669401659794897), (pn 90983 657043006476289916), (pn 441841 912122832296478857), (pn 765575 724968497494867490), (pn 1037187 103046239507464401), (pn 70697 393947716983132261), (pn 987329 999816885820344455), (pn 579699 832574395374909964), (pn 723151 416756096087638973), (pn 325404 187084926505256524), (pn 699186 130999092738907799), (pn 472553 865021992342857288), (pn 639774 713293558235744306), (pn 1098413 834244502016173123), (pn 891658 589121724825509142), (pn 361575 707815106671436254), (pn 417714 500079720898009390), (pn 238617 380715184157421356), (pn 51588 130845000286409508), (pn 319878 425181885298087045), (pn 558651 650086686807428161), (pn 1049867 458628320620063930), (pn 180787 853163209188774126), (pn 952701 454617652290339220), (pn 246812 474683530355963748), (pn 1024843 189808528593177114), (pn 159925 420730710652334688), (pn 883827 934178543019542800), (pn 1127640 451466520551829597), (pn 90393 926491848449366135), (pn 445331 226734491097376875), (pn 664117 181616249746242474), (pn 470966 734671975519053069), (pn 79960 346960606571384723), (pn 439533 184180921526551192), (pn 563102 239349206306765478), (pn 354369 5422665599697979), (pn 738139 197068285588394852), (pn 628977 366231812541914573), (pn 700636 389478187542491748), (pn 719998 767273512948131523), (pn 787631 188677000489939524), (pn 281477 481317096018369944), (pn 98158 651090182952527389), (pn 970267 975072915829737898), (pn 1098419 965879722471329510), (pn 883795 727437396017727857), (pn 359999 374064416018887517), (pn 407392 393473148296935590), (pn 140734 196455003123197673), (pn 125199 238503410732667150), (pn 1089011 501449533497501141), (pn 237598 358534122585491315), (pn 366412 705016651409713336), (pn 181180 260656664818203046), (pn 54941 648022575529741457), (pn 70366 379445956105704572), (pn 119300 10574054286715015), (pn 520940 44252568831525612), (pn 763291 518095819058463671), (pn 189100 375469150940775260), (pn 477233 23801776477952852), (pn 140956 418531642287269992), (pn 639535 201996420563168318), (pn 663956 550102360433831171), (pn 858011 836017772724622198)]) else (proofWord80 [0x2992c298, (pn 600146 747265871404768034), (pn 649659 881711478378742847), (pn 652987 872905504987042660), (pn 949509 125054804366073797), (pn 110027 52024493563816548), (pn 644586 44426107120244896), (pn 1061538 217527872729989956), (pn 299326 138207951691468817), (pn 477200 46729207948059167), (pn 800519 630983832671946786), (pn 474754 531191123025661908), (pn 760901 174365233401401650), (pn 322288 434761362850702949), (pn 699870 708924393477014054), (pn 149225 463334423583992041), (pn 616389 341888682386281231), (pn 966345 381734628799559129), (pn 20295 972331355487438822), (pn 381633 542067236428713120), (pn 784495 728965196120847144), (pn 491769 631456370733893715), (pn 74610 173167390198174581), (pn 5963 216040555050314247), (pn 1087565 871639579222090336), (pn 763291 652085533688218610), (pn 795288 893516920273048652), (pn 463083 217612509399873876), (pn 98455 120189938646657128), (pn 641749 387710863438031242), (pn 607444 517823067620381891), (pn 1145817 896521193605173558), (pn 362221 403440788559528440), (pn 1003679 360815181241299494), (pn 347239 443825937720867946), (pn 277597 640363809897817412), (pn 963098 232800207125230877), (pn 251928 566356666003067521), (pn 1175064 859902968281597083), (pn 200877 540898736473977595), (pn 361312 536895257888971091), (pn 171258 215455797400862117), (pn 308822 459746224876333474), (pn 462599 739289352810705568), (pn 732751 478218101890585906), (pn 1182597 905276949601556313), (pn 392634 617875655880776061), (pn 256509 275715722807979187), (pn 766904 134568258407546523), (pn 182745 996522937648567745), (pn 240737 835951972383935891), (pn 421824 363965873161659528), (pn 591296 943484110350239916), (pn 800780 218744867649834174), (pn 730984 670614954880620564), (pn 950099 151335847226646349), (pn 478371 853861043745428098), (pn 720109 394819613207799467), (pn 200877 144199622154605644), (pn 900102 442187645993047254), (pn 400391 262291841479418399), (pn 365159 429223846846818610), (pn 796188 943040287572561830), (pn 730427 191506406072489249), (pn 360050 263642370326645605), (pn 105475 110254543104547176), (pn 147233 1197380309461641), (pn 239192 120034392876061487), (pn 711374 98541951931655513), (pn 398094 444705290719430599), (pn 384050 46435761692789408), (pn 784486 793845796233274278), (pn 657190 811186276746942673), (pn 73061 801168316318815748), (pn 365434 917418554318277383), (pn 880021 554070671011299852), (pn 723151 488597086334895069), (pn 209115 921442681823757896), (pn 392241 527508759870565974), (pn 101921 883095186644543048), (pn 640883 272406729915550522), (pn 456623 938070036813845699), (pn 1035017 638481657600511238), (pn 439531 682502789707751917), (pn 709316 28289856546702120), (pn 493629 564149439042483915), (pn 123013 923899451323290389), (pn 18210 136263685486372237), (pn 29668 349592464918258273), (pn 1121920 994976860397006016), (pn 190869 16378458147459318), (pn 808007 497553950709859731), (pn 96879 610146091790007125), (pn 629076 77927770970942242), (pn 481327 899788571225987786), (pn 723336 721175971503637808), (pn 1163677 904967486304772960), (pn 407392 585085039937882235), (pn 252894 870317353915231403), (pn 766903 557263080066923930), (pn 938324 66029323031037381), (pn 240663 940887219506433379), (pn 420643 790341936303465608)]))))) else (if j<14 then (if j<11 then (if j<10 then (proofWord80 [0x49b64956, (pn 344553 516256162213152630), (pn 332452 217953054656709510), (pn 317104 342233326046036390), (pn 308249 769967895024385814), (pn 292901 795167462748469878), (pn 271060 566453084733454134), (pn 258959 317690329003865254), (pn 243611 392429492629023718), (pn 199042 883285435904560774), (pn 31101 360813257438654933), (pn 1111045 478679225915790981), (pn 985310 502968241672270933), (pn 820615 310210169189011477), (pn 646180 385204501355000149), (pn 504212 324252784242547765), (pn 410944 113515047101481717), (pn 294949 117757953036070181), (pn 188694 201033184863655237), (pn 75945 931310743537645716), (pn 1142903 640429524144151172), (pn 1007428 536148129946582132), (pn 862213 550995061168445844), (pn 687778 427822694535034724), (pn 536070 287840919260782468), (pn 423321 919040797972644388), (pn 284600 336421218654890036), (pn 168605 439744072271269444), (pn 39623 837076871118582163), (pn 1113074 601948946082550131), (pn 951626 382933332994537523), (pn 848618 93164025863184467), (pn 722883 266076364923700835), (pn 610134 946814327719685059), (pn 494140 597585423454499), (pn 361911 770973411435820675), (pn 232930 168306966220446339), (pn 94208 684769602361819106), (pn 1177399 330513351894818930), (pn 1032184 593062798222870850), (pn 922682 900758489802648722), (pn 790454 720675423579182258), (pn 671213 97959088786143058), (pn 538984 719716127060678978), (pn 397016 708301738037362690), (pn 271281 633512318009747138), (pn 168273 244662307178547906), (pn 23058 358590698026037457), (pn 1119236 106648828782959185), (pn 1009734 414342252643074497), (pn 896986 194161675053147937), (pn 761511 188960984474683665), (pn 619542 830762620811831185), (pn 461341 189162116926490481), (pn 303139 498022017105472369), (pn 190391 327382547268178481), (pn 61409 774254942028101520), (pn 1147847 393738883167477328), (pn 1035099 223098657415940400), (pn 928844 405457616623417216), (pn 835576 145180283627414640), (pn 761787 894345035154492208), (pn 632806 489839997258069168), (pn 529798 299153661523156000), (pn 397570 69530243472836352), (pn 327028 742898614442933472), (pn 279214 52664531023310320), (pn 189192 270720091632439088), (pn 40730 415402420863078945), (pn 1199925 256750682798752386), (pn 180787 889582853075833087), (pn 42686 385350507958976726), (pn 171259 293927136844873604), (pn 420388 367904311278078354), (pn 160524 748087699131310691), (pn 619375 411276382308994320), (pn 1202018 236982075017211992), (pn 987643 575975778942486655), (pn 324682 750456295046259401), (pn 690092 484977463551868822), (pn 59493 643631424030393545), (pn 231364 590758368752159124), (pn 359252 954041696139764888), (pn 600443 622864457807741728), (pn 649664 493473365124795455), (pn 693828 316364485936369732), (pn 950099 430302975353298889), (pn 336488 438091396678167140), (pn 644587 233325815071499416), (pn 230391 916711670751244868), (pn 300209 283262490489277463), (pn 324829 940890926279369247), (pn 950087 525286105040947506), (pn 474754 567140892646379492), (pn 687709 105566780887404833), (pn 360072 521574635694191169), (pn 718183 137644446814345510), (pn 150101 612819760497107145), (pn 804658 541497269439205647), (pn 1079118 841019285208327369), (pn 308360 354671660116838386), (pn 307398 41026515735569592), (pn 784499 169715023123839154)]) else (proofWord80 [0x8180708, (pn 31433 704519101784261576), (pn 12839 53222100703116919), (pn 1199923 594581244121709191), (pn 1178082 316327270205617991), (pn 1165981 117104866302882999), (pn 1153879 818801002809126935), (pn 1128791 864048948259318823), (pn 1100457 232800324915815975), (pn 1078615 954544839113564023), (pn 1047034 646798135147878775), (pn 1021946 692046080586536151), (pn 1003352 90288675406466423), (pn 962030 753049997340034935), (pn 936942 847839050542859495), (pn 928088 275573619509674231), (pn 909493 673815458449964295), (pn 887652 296480024942852199), (pn 862564 391268322196828775), (pn 840723 113014348246133687), (pn 802648 402731887135008359), (pn 780807 223558616861090423), (pn 765459 298297780497784279), (pn 737124 567967697563260711), (pn 708789 986257914160450999), (pn 664221 972522667277255751), (pn 619653 958786664502886311), (pn 601059 406570367121587655), (pn 588958 108264991776274023), (pn 550883 447525906172047815), (pn 535535 522265825711451431), (pn 510447 617052611148474503), (pn 485359 612761716600300343), (pn 466764 961463203713736519), (pn 448170 359704286716713463), (pn 423082 504035203586414615), (pn 414227 882229420737910151), (pn 402126 683007016835175335), (pn 393272 110741585813524759), (pn 377924 135941153526074311), (pn 352836 230728694877341655), (pn 334241 579430937905021575), (pn 309153 624678883355213463), (pn 290559 72462585939311271), (pn 268717 645586800628413607), (pn 246876 515953126255571655), (pn 238021 894145831555509799), (pn 216180 615891857616349751), (pn 197586 63675560235050919), (pn 182238 88875127959134807), (pn 153903 457624992764075095), (pn 128815 502872938202732295), (pn 103727 548120883641389495), (pn 81886 269866909725298295), (pn 66538 394147181103090487), (pn 47943 742849424142305095), (pn 26102 514134290166907207), (pn 1014 509842639727557974), (pn 1188099 51202539048860006), (pn 1175997 851979379208811894), (pn 1157403 200681622236491990), (pn 1135561 971968000147255030), (pn 1123460 723204488491887366), (pn 1108112 649322596624950358), (pn 1076531 440656596312973238), (pn 1054690 162403378299591622), (pn 1032848 884147892543477542), (pn 1011007 605893162678538886), (pn 992413 53676109359926934), (pn 970571 775422135443835910), (pn 961717 153615596658018326), (pn 939875 924901218619933206), (pn 911541 293651839362186262), (pn 879959 985905135396501190), (pn 861365 384146218376409286), (pn 829783 977320322608572950), (pn 794955 943536697999270406), (pn 756881 381875292368706566), (pn 735040 54080210688448358), (pn 709952 198407347929256646), (pn 681617 418538425007901366), (pn 650036 209873180633237366), (pn 637935 10650776730502198), (pn 619340 359353019758182646), (pn 607239 160130615855447830), (pn 598384 587865184822262918), (pn 586283 339102429104208550), (pn 577428 766836998082557974), (pn 562080 841576161719252182), (pn 549979 592814161915441910), (pn 541125 20548730893791334), (pn 525777 45748298629410086), (pn 513675 846525894726675270), (pn 504821 274260463705024870), (pn 495966 701995032683374470), (pn 483865 354151573300077462), (pn 468517 527972196516258054), (pn 456416 279209440775134662), (pn 441068 353947848474515750), (pn 412733 623619277426152582), (pn 394139 120941820008616262), (pn 382037 822639468377951750), (pn 363443 220881307306707478)])) else (if j<12 then (proofWord80 [0x96ca945a, (pn 685823 340364504743184778), (pn 641255 326626234133806426), (pn 580454 29486579239253146), (pn 542379 269664522192448650), (pn 504304 608921656959329402), (pn 472723 400257924424688106), (pn 457375 474997088038312762), (pn 425794 216790735876412906), (pn 394212 710881112763287994), (pn 333411 463281809672520458), (pn 314816 911064000439664058), (pn 279988 926819971742972010), (pn 264640 803396972123401978), (pn 210332 760168995213681530), (pn 156024 716940262332045130), (pn 101716 871874448643984858), (pn 60395 485096930556118650), (pn 19074 197399360242319657), (pn 1202911 913640879363586329), (pn 1168083 929393826986848345), (pn 1123516 64281903326947929), (pn 1104921 462523742278772329), (pn 1079833 359149120373775257), (pn 1025525 365463007130931753), (pn 984204 77763924919437497), (pn 939636 64028678047777465), (pn 914548 109277379423747961), (pn 902446 910054975521013145), (pn 893592 337789544499362745), (pn 881491 39486436919850425), (pn 853156 358695949909471337), (pn 824821 727446570628655369), (pn 793240 419699866651435433), (pn 755165 858039216923581705), (pn 739817 932779892423367289), (pn 727716 634476784855390009), (pn 705875 306681703175131449), (pn 680787 351927380847987513), (pn 645959 318145268055638121), (pn 594897 901871996238132105), (pn 530849 928235016635640697), (pn 502515 296984125526336537), (pn 470933 989237421549116953), (pn 439352 631950365733508441), (pn 398031 344253551333953897), (pn 382683 418993470884892025), (pn 364088 916316769393133961), (pn 339000 912023607067624329), (pn 313912 957272308443594649), (pn 295318 405054499199203913), (pn 266983 724265524028847529), (pn 248389 172048470721770089), (pn 236287 923284959066402425), (pn 217693 222446094306846313), (pn 169878 581753118639857417), (pn 141543 900964143457966345), (pn 109962 642757035381821689), (pn 78381 335010331404601929), (pn 40306 674268978034574409), (pn 15218 719518435313254312), (pn 1205549 887835307504106072), (pn 1173968 580088603549955512), (pn 1158620 704368119013503432), (pn 1140026 152150309746044200), (pn 1118184 774814120313152792), (pn 1070370 84580036847393352), (pn 1022555 443888573055030520), (pn 1003960 891673031587975608), (pn 988612 867332247496740472), (pn 970018 364654034153425368), (pn 948176 987319356549022504), (pn 916595 729113760347504440), (pn 898001 176895951091579720), (pn 876159 849100869411321160), (pn 851071 894346547049573160), (pn 793517 75539785817824488), (pn 729469 101903562141111688), (pn 694641 117657265690152136), (pn 653319 730878235762262872), (pn 611998 492721773178027704), (pn 596650 468380989063722840), (pn 555329 180682662801076392), (pn 530241 176391768264436568), (pn 505153 320718149533328024), (pn 463831 884399523738966664), (pn 425757 223658170357404808), (pn 394176 14992170045427864), (pn 375581 363695168975817544), (pn 353740 134980790972336312), (pn 341638 836676171564336152), (pn 316550 931466736607183064), (pn 304449 682703980866059672), (pn 285855 31406223905274456), (pn 273753 832183064065226344), (pn 255159 230426414845539112), (pn 236564 529586038280564008), (pn 208229 947878522689694008), (pn 189635 395661469359547720), (pn 171040 793904064202546664), (pn 126472 730627709566719448), (pn 101384 627254599547883480), (pn 69803 468128951028156888)]) else (if j<13 then (proofWord80 [0x46054084, (pn 3287 845801440560940083), (pn 23027 591764100256116804), (pn 643736 613645692055865168), (pn 760635 442211989942965040), (pn 256289 886509296973709744), (pn 10802 305675447608088684), (pn 54322 779310438650790676), (pn 461319 491394649759697928), (pn 910698 929794205138040320), (pn 378289 884813356800611425), (pn 831985 276397942161032976), (pn 760531 675888425953806745), (pn 106285 830255457899475240), (pn 22513 137372589824503833), (pn 173040 522803728130311008), (pn 495959 741357356856049749), (pn 40295 906512270637929602), (pn 76664 681919630502267456), (pn 1067725 273398517353349456), (pn 190132 918969217787683346), (pn 158349 806651678028475397), (pn 305193 175589709434203333), (pn 680519 72124068650158657), (pn 240902 977813836041830788), (pn 193628 413924709660438552), (pn 909573 444145926080829633), (pn 29656 79718416603727052), (pn 64956 972400676608089120), (pn 618078 670286349133718404), (pn 76960 448034058408304962), (pn 680304 996279385172664375), (pn 329757 24628611327488009), (pn 609721 132931382966355224), (pn 472416 549802465063960744), (pn 629557 616472173985409540), (pn 379620 254849303847145635), (pn 30116 678908258542953536), (pn 577407 332960397101916237), (pn 31958 591821238161920108), (pn 48572 16329639703135506), (pn 231841 188654519686082677), (pn 23843 797290700089938320), (pn 181857 807073740031485018), (pn 21406 513549593291025421), (pn 79783 654764243253746059), (pn 170526 410758006445514979), (pn 95661 81851028151415348), (pn 465304 817586864458312708), (pn 946355 161709819723146216), (pn 552688 724621011038999635), (pn 45464 491937665218788613), (pn 756817 49501197309413056), (pn 769952 413442812324156696), (pn 616086 484677536136170977), (pn 392523 911113071523005032), (pn 262189 84251232306660064), (pn 161767 580142959673677987), (pn 82667 941626541358398492), (pn 768125 342351302213634880), (pn 628487 931869874815867274), (pn 155691 982556054711015464), (pn 208254 679920481013106563), (pn 57286 440007324935415300), (pn 42757 304349669785342353), (pn 916951 132895396290499842), (pn 529237 112264325057233800), (pn 387383 976428006791463105), (pn 66728 223533568375201825), (pn 14244 959192453430120452), (pn 606898 749468354334435328), (pn 302619 17870035953128290), (pn 227448 651671924089128268), (pn 573965 881980298651124056), (pn 179528 635486921190523576), (pn 309447 643519161283084987), (pn 605855 534131926741514923), (pn 574274 325467438281095195), (pn 565419 753202007259444619), (pn 546825 101901982463650491), (pn 489270 233556381279673643), (pn 428468 886874106780931179), (pn 383900 823597752110499195), (pn 323099 526455829461680171), (pn 294764 845665342428231531), (pn 250196 782390499632426315), (pn 199135 465198687359803499), (pn 144827 471511818191181563), (pn 100259 457777327268368987), (pn 84911 582056842708847707), (pn 56577 348571169129899), (pn 15255 514488837587532506), (pn 1173120 115993870064088106), (pn 1151278 837737628359127274), (pn 1122944 57868705426237482), (pn 1094609 525698517970641274), (pn 1053288 89379136204363258), (pn 1002226 722649239928360426), (pn 967398 787945563058521562), (pn 922830 823749156162158202), (pn 897742 819455993802044154), (pn 836941 373692259700745578), (pn 769646 624476495810828954)]) else (proofWord80 [0x31c1a834, (pn 26571 97364031546187817), (pn 164030 70059011617916576), (pn 510256 18610124655837290), (pn 34398 138875131923059725), (pn 157648 830099665923610881), (pn 832098 298848022869842178), (pn 699034 813690687341233040), (pn 462066 840022877586382961), (pn 613788 829304890502192142), (pn 610514 9489425311143553), (pn 529511 554017644586345228), (pn 425107 242676229052320889), (pn 57579 788014504800985487), (pn 159457 223061716026922033), (pn 1068223 720639757930545798), (pn 285833 507522353610270827), (pn 52559 610242768665341197), (pn 344458 142643003871775244), (pn 682087 768323210334974533), (pn 757312 652057895214024288), (pn 459409 463266569290432582), (pn 1072 91677299179542536), (pn 906828 565322621646408449), (pn 189392 731002970105972068), (pn 399155 308382584920916184), (pn 122832 281317044384465256), (pn 5910 743491165907174453), (pn 518 419259036479288332), (pn 755643 439637772282107394), (pn 812915 990833986792407496), (pn 171252 678104539621032096), (pn 56693 914348819610384401), (pn 611549 648720098391756161), (pn 462942 385936375130425444), (pn 41335 47136683363451156), (pn 159457 331590160159094277), (pn 681358 671609684812238021), (pn 680431 344247690645700928), (pn 179531 815313202736185545), (pn 315814 43143594445964312), (pn 1059765 881796956623478915), (pn 132586 144749735851655960), (pn 108779 448915651172065379), (pn 616086 412584767968252673), (pn 859991 992720042144006752), (pn 258615 311028265657139680), (pn 161844 246220327312629846), (pn 29380 115838095508154636), (pn 610810 752099123007462466), (pn 378564 397242331312850276), (pn 399155 308381214792581290), (pn 62009 607353263238260774), (pn 12437 142631766120556545), (pn 155028 277800133600503040), (pn 132715 271406027475649952), (pn 16592 867696161913573864), (pn 264565 551579022242521292), (pn 421496 868984294717058562), (pn 983151 910478373830870312), (pn 491333 696408881195749608), (pn 87984 640833130651656246), (pn 319134 619057044024550411), (pn 625585 463465631231793670), (pn 343313 957442081602800176), (pn 845714 92295720505327879), (pn 105224 283169716095694086), (pn 457055 917170019013182216), (pn 418065 478755147789543510), (pn 337812 925982026152159321), (pn 657076 925113855769635352), (pn 606788 208838123708364294), (pn 152702 600095726495728808), (pn 462999 497213695740465384), (pn 87397 517808712649125940), (pn 25167 305498399952882822), (pn 1079006 450734785637526736), (pn 1041570 170495371719073947), (pn 58463 645829807932733710), (pn 158570 829239440098624592), (pn 163534 571360496323154954), (pn 79267 173180407371537666), (pn 227448 717079150775505536), (pn 86368 282331943726907404), (pn 54319 325877188667031626), (pn 1202 714921223339942931), (pn 611103 811082280290224769), (pn 188908 537304648530706437), (pn 34838 550490117963260706), (pn 908244 630052101543166208), (pn 871479 624894120956529088), (pn 774478 635990025465765890), (pn 688878 238524284322523669), (pn 9740 43405216264103620), (pn 190444 780301077868972673), (pn 312130 606747495006766032), (pn 189550 122925682028871696), (pn 54329 129915970654316628), (pn 43682 539206378569880072), (pn 306658 736620283398523969), (pn 340619 399541499334624520), (pn 623613 50883517045669968), (pn 217277 303582801012261484)])))) else (if j<16 then (if j<15 then (proofWord80 [0x704c22a0, (pn 361413 287470229554544912), (pn 90947 366291974931169289), (pn 330276 308793578282323585), (pn 642541 622692361540419764), (pn 1815 140795392125305480), (pn 1067704 668385155801677938), (pn 484135 402131576701739050), (pn 316847 654890417299672069), (pn 342529 412609986354217537), (pn 794061 32006245561270329), (pn 222278 956360683558678835), (pn 83899 306438744162174726), (pn 466518 955117611305997896), (pn 493676 430983494623249496), (pn 336482 556624173773371717), (pn 190703 176769456571221760), (pn 1025143 324634542789562570), (pn 57280 826055023742466572), (pn 227651 737771993361550913), (pn 335699 629663200243261832), (pn 193042 875833144718889035), (pn 20668 712202248255484436), (pn 159602 310605079593098274), (pn 615033 398775895204299072), (pn 700233 858962334924456189), (pn 50044 943200133201871032), (pn 59345 383258495224144514), (pn 530309 579310736073695362), (pn 983179 581554420323239528), (pn 500778 447370737274001603), (pn 106891 119538263899022622), (pn 619005 359973219965177388), (pn 986265 485643426304120328), (pn 309594 139475342478085249), (pn 416177 37253483085718284), (pn 425109 872216823994600569), (pn 66436 393796359359056411), (pn 235568 994887763249674241), (pn 22666 979712925959465604), (pn 1057886 307456857409750336), (pn 736827 526422267178193348), (pn 230322 635608854769369132), (pn 92129 978552296837894538), (pn 219655 782195673710043292), (pn 89767 702057516624728394), (pn 153528 810950766141501493), (pn 21997 889449939435577370), (pn 761944 935720365536094737), (pn 310203 763098619310789702), (pn 910274 366505107088280993), (pn 307488 999957743430959924), (pn 249206 609958862483915366), (pn 24804 28861338126280197), (pn 77643 255536676198155592), (pn 465247 638990125644613730), (pn 629265 422029086133878921), (pn 836044 848733874226798083), (pn 492611 664928524651209220), (pn 232624 991413066547905656), (pn 670889 712730200021946492), (pn 22141 156483266890533397), (pn 9740 25390845695121544), (pn 190444 807533647109819024), (pn 944641 679409562145104240), (pn 209040 819963541726536748), (pn 24804 29390757261501957), (pn 39919 641599048227890632), (pn 831510 84428178045356132), (pn 633987 212051203429290004), (pn 160894 303829138179888962), (pn 926801 480187408570585936), (pn 439365 777873186104565848), (pn 49608 57512734247362826), (pn 761539 188274709510775713), (pn 397423 853433595526387457), (pn 680320 659263984884418112), (pn 736878 261155315369627840), (pn 86813 847916655608476712), (pn 465158 397259432310493193), (pn 609648 471866062064333377), (pn 529608 599669241367825025), (pn 94910 867173606632145680), (pn 351914 329452821229166752), (pn 80900 803936729981538357), (pn 20075 608521389063233636), (pn 657890 733680993595846668), (pn 607157 26266975146413601), (pn 616329 950562997733441699), (pn 10333 204516883455312643), (pn 397656 858490797753041744), (pn 358996 743441199462679184), (pn 23768 669850886270487567), (pn 347574 993485904858580680), (pn 477155 68306933892907313), (pn 71163 228978124060926200), (pn 5991 487904504237610008), (pn 929061 485597304042096288), (pn 965005 766878164652450005), (pn 61416 284210056275893274), (pn 619541 124897202313937793), (pn 869655 865265847204584001), (pn 680265 307789120929072712)]) else (proofWord80 [0x81a50c0, (pn 624092 551769441437778432), (pn 187744 142855955315445973), (pn 94742 540639833155617184), (pn 611606 528966213872658506), (pn 75853 11660027806640518), (pn 909673 513878875973640256), (pn 302231 454903657293676592), (pn 152149 905931590804537476), (pn 907907 283312205637910656), (pn 325867 534945516406190620), (pn 99318 26984845660392472), (pn 75568 308158528370279690), (pn 90928 327273146363166720), 0x1c020ed8104060, (pn 303425 917857794369789952), 0x6040702030981000, (pn 907367 97087627401642524), (pn 77476 916494085390958912), (pn 758389 487243432736589836), (pn 661260 579806169916277121), (pn 4723 233434594017608128), (pn 608599 615845063830208899), (pn 530456 892043094430680256), (pn 912904 62985454028849827), (pn 832912 606979794076184648), (pn 236489 283964812916426766), (pn 56797 669681089739099140), (pn 1439 429284756699490497), (pn 612774 39481190812024838), (pn 56743 565300575095488705), (pn 4761 124708105593086016), (pn 473567 146795728908067868), (pn 38037 475636266276020368), (pn 529499 381638216906977360), (pn 208671 588835083762542592), (pn 229228 898994376697713680), (pn 81316 424067304445716592), (pn 994104 550584560552329538), (pn 167 570480466391751044), (pn 28353 114229474755675396), (pn 122819 360366259731596429), (pn 190333 869023053069953140), (pn 94822 425818027414016064), (pn 333371 9078563776857730), (pn 14407 234056960881142800), (pn 226678 648888908250190027), (pn 19138 641802153080934464), (pn 491718 715871811021581985), (pn 610084 579939266078965760), 0x3050400000000, 0x30483824102110, (pn 151115 727451828646838822), (pn 26010 107584888560418816), 0x308, (pn 66348 363057386825449492), (pn 170300 342135123976716296), (pn 373242 359981715474197538), (pn 47717 268495793169893394), (pn 170300 341599107206620186), (pn 85233 831065639356203008), 0x6050513020008b8, (pn 75557 863725914325000232), (pn 642615 678741999721646631), (pn 18889 493094363589251616), (pn 345030 229586486764819993), (pn 920422 715506264167553504), (pn 304615 130813437345108233), (pn 85617 683973712326492696), (pn 766576 139705849007322949), (pn 985223 330000007299334721), (pn 75954 648952185509450273), (pn 302868 38768163946104960), (pn 925989 832480407897050784), (pn 793382 985201482277520648), (pn 608017 947077299887411232), (pn 929356 982817463934398981), (pn 755652 515464676476323136), (pn 642509 323973422839333528), (pn 171252 106150406864881700), (pn 319209 668167529847070730), (pn 155322 909598909982602240), (pn 605464 46670753904859234), (pn 482964 628218206203439207), (pn 25985 199021089473372242), (pn 7824 158538221541736718), (pn 611103 818941589153654851), (pn 58181 733572394213445121), (pn 123154 61874336496356225), (pn 227171 665821756778120072), (pn 462971 822883282835177777), (pn 142326 8364670770561033), (pn 22441 368862814971822153), (pn 645796 880479606995513382), (pn 20742 285688814241411107), (pn 739 527758573277307017), (pn 836044 848725301447496881), (pn 1077589 949106403868672256), (pn 869284 538944353033324880), (pn 963639 469310588210258384), (pn 229120 695789965116031128), (pn 83854 589816024974007315), (pn 40805 540562113717617666)])) else (if j<17 then (proofWord80 [0x18214461, (pn 689984 342854941926559897), (pn 834687 540125632553946249), (pn 19429 51386895754921090), (pn 32468 593499232527387665), (pn 156737 397583832484437001), (pn 982849 465778631310073940), (pn 439217 301992588459646976), (pn 93 332882362439172096), (pn 110 797980365833192194), (pn 306372 780561614749830162), (pn 40269 530644473871077424), (pn 341046 5315227701350416), (pn 160745 508840318209892352), (pn 5017 802640896955638558), (pn 75858 579352411415527650), (pn 83532 681496569808670913), (pn 85556 288390895323598884), (pn 755948 583788765658558529), (pn 250470 467580996103536816), (pn 963511 572873670736615440), (pn 47520 622057783555143712), (pn 378421 268598008174087190), (pn 616287 318781171738398784), (pn 234948 748398443369603112), (pn 349548 77831901857990706), (pn 9518 519942588201468032), (pn 316417 3406437526964272), (pn 151129 762405659854491744), (pn 463940 550575020544120903), (pn 79115 252862678681057564), (pn 314111 636770816826343505), (pn 397050 676065748532658176), 0x2250a100089428, (pn 302231 542165334235742722), (pn 122841 696932331514370056), (pn 163233 27252291166547984), (pn 618 22344885071302800), (pn 305205 423854571829855876), (pn 621046 659640574896888085), (pn 79765 180930542977180824), (pn 361580 449802647100860480), (pn 585740 50147121270325324), (pn 41413 477562420976226645), (pn 66281 30137458932188191), (pn 9570 741515282618958624), (pn 153111 439165705446753297), (pn 99216 750138139389167299), (pn 680764 135654040437138185), (pn 20522 157681922629776650), (pn 75557 866404497657266820), (pn 613172 673360711928371240), (pn 302749 135836093731611184), (pn 302325 145573775703581188), (pn 623352 825821542891683086), (pn 156873 346103072745078787), (pn 605866 379578376140233744), (pn 199536 995175918752565317), (pn 228160 909498070618605584), (pn 364849 215894525847014420), (pn 24890 445021692981676032), (pn 7185 89678917994151946), (pn 226968 739793215424581824), (pn 492900 762181828415062016), (pn 47298 908168125860020321), (pn 607723 396697832800388110), (pn 608502 822194924150337562), (pn 66260 727389370108127312), (pn 304002 378576565220676640), (pn 557349 973577549362593830), (pn 758024 20019389665674248), (pn 122818 438653081785796614), (pn 4750 253689861537050816), (pn 307915 595491919771730), (pn 75853 34360751081492928), (pn 761191 61184732197158932), (pn 227154 939572804956720263), (pn 18889 465931479711252803), (pn 7387 979759869280130073), (pn 132402 443463678749049962), (pn 152389 852081753925163541), (pn 38101 969787696446185554), (pn 57655 758304206732143640), (pn 123225 190545974660104545), (pn 606824 247022463717736936), (pn 242341 939617054742032737), (pn 380451 450456950505475332), (pn 18889 465931481007310936), (pn 38074 106913156903735340), (pn 123012 671444137675849747), (pn 454540 465181646663585036), (pn 19075 665007118832943313), (pn 227139 561042411558803728), (pn 1064022 51246254145404968), (pn 396827 511479332184887838), (pn 11935 518651365500028290), (pn 309663 245874216754500632), (pn 247942 833307993637933317), (pn 779416 487748390954740784), (pn 77889 183645512218677404), (pn 68497 665482923658731554), (pn 132521 409425531581030624), (pn 531018 99245707237106956)]) else (if j<18 then (proofWord80 [0xa141036, (pn 761525 406522090486579975), (pn 757059 510960104127365249), (pn 724628 190395626539190945), (pn 156024 953702323239262400), (pn 14308 101534578702391592), (pn 307572 396157120148572172), (pn 170153 489044637336275585), (pn 18939 193625920152305932), (pn 49798 238226363787273338), (pn 942270 354106998097092672), (pn 775538 304829177691703827), (pn 615790 947960726754440728), (pn 61575 629803477360196098), (pn 662053 791386833907098664), (pn 368519 975888878252867848), (pn 836158 663512815168471812), (pn 1060633 130894085380114698), (pn 226682 857902462611247240), (pn 784134 233555221815168145), (pn 155869 661933878531884293), (pn 16567 613795753915483136), (pn 205 234738806181095491), (pn 681510 650143404405645857), (pn 4777 727967998244881410), (pn 624422 720943506569366528), (pn 62 280851131482505226), (pn 80289 453592920855740676), (pn 13655 346985299018293776), (pn 226673 627365969310584896), (pn 609503 484894947089453104), (pn 559633 9626027754000068), (pn 273990 536260065858951728), (pn 911447 6997492212469840), (pn 455432 27404403363291204), (pn 94817 291713650659099270), (pn 66278 432023299249123360), (pn 304815 171707530096444461), (pn 912247 702781735796639056), (pn 758548 857637987156298801), (pn 307413 986390728327309059), (pn 757072 911788156605760138), (pn 629485 416287470459359769), (pn 678277 710522755112371344), (pn 172403 722628308404542466), (pn 236874 804294746017793545), (pn 1060670 238392553860285187), (pn 606838 51419303890208288), (pn 255457 610346444764776035), (pn 945912 665207435555717892), (pn 342486 593215504999024910), (pn 635218 424364932723386179), (pn 76303 236207133466836485), (pn 61455 508540292950397966), (pn 912635 461580449757958203), (pn 23838 165880180573208578), (pn 314074 697245399218194960), (pn 667341 15217683902271689), (pn 87382 443145716680890640), (pn 83825 608522572056626188), (pn 120466 939748521236103496), (pn 152352 821378813010665512), (pn 75853 12370515330367630), (pn 611584 46618377367667330), (pn 155856 540817502938662160), (pn 725496 617270880129519672), (pn 37939 337103204291980260), (pn 873712 781890572856665348), (pn 942417 928604048624329779), (pn 142907 235403019478790198), (pn 610441 269521132225872166), (pn 455341 741126403160649921), (pn 47530 847702487692526337), (pn 77930 44829734944211345), (pn 302675 416115283099648000), (pn 725192 274307223824468384), (pn 209020 273286842459371588), (pn 377918 735915901053046049), (pn 491866 507123192274665688), (pn 670797 401726260137263104), (pn 3764 592154128385957968), (pn 625290 171253312819208515), (pn 159159 958619281886307381), (pn 327324 854673911002530436), (pn 911567 219127710876194053), (pn 40250 949764758359311876), (pn 636056 567579586412677137), (pn 56765 388055987531858080), (pn 397271 386214418117296128), 0x50c0686020018a18, (pn 75919 989518452161055753), (pn 632848 53706378455323692), (pn 19074 78055749800698896), (pn 179598 892091151807978764), (pn 37957 80895026423662104), (pn 56963 833929991332825096), (pn 75854 173595261167079952), (pn 761500 61248491312185448), (pn 880777 413682255275491408), (pn 911619 718458251386422784), (pn 307094 540881383894679859), (pn 38351 43272820624820252), (pn 314194 612146145783390522)]) else (proofWord80 [(pn 21 910945266694891169), (pn 316443 91610231489319328), (pn 795430 830519142353731584)]))))))

def genIndex7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (proofWord80 [0x75652e05, (pn 270727 838778619229369440), (pn 833825 183141465222090907), (pn 939502 315678722922905668), (pn 529207 651947807863743177), (pn 682949 954665142401409637), (pn 353816 548601302914957642), (pn 232786 995137284112249970), (pn 628416 253526062967217780), (pn 81617 884029410996324646), (pn 187714 89941940438055936), (pn 477116 4397027156495988), (pn 670543 487423973777130614), (pn 1151077 197593590364111130), (pn 1025711 605083571768106491), (pn 189595 742550593333363168), (pn 17709 414743827743257154), (pn 197813 135369900342083598), (pn 332301 113705340019727840), (pn 17709 414759209631759360), (pn 566687 183346223940900613), (pn 125256 201380981835301258), (pn 93266 999596198157499392), (pn 566701 271892477737805498), (pn 35971 150973886727717344), (pn 13228 698378942609298482), (pn 755697 32917528864694708), (pn 88920 658661737192220150), (pn 252231 92908856779760708), (pn 493098 901892145090791615), (pn 553 412729885741528322), (pn 263272 444065710569259292), (pn 43514 155007797516271631), (pn 122123 120652971941272417), (pn 10945 800748638960365095), (pn 86705 462281727358409620), (pn 149898 257087872443089376), (pn 17709 155204096601716533), (pn 840271 228958444901198311), (pn 709030 853522739541574129), (pn 530319 644755249023958016), (pn 566701 272323363334225923), (pn 247297 67941141177958880), (pn 17709 127241357817020565), (pn 566693 466430650472431628), (pn 63392 261714201120080134), (pn 68848 58890409723575296), (pn 566690 33440145356678299), (pn 165179 937812373954441088), (pn 905513 954130342044515328), (pn 566701 272124936748925519), (pn 553 413945434200605123), (pn 882756 219498516076051456), (pn 566701 272119181492846592), (pn 390148 654275578779664537), (pn 627118 720225383593372815), (pn 499241 529217152631709599), (pn 223 384390885080861511), (pn 1105096 925780593195116855), (pn 986438 486848396236888967), (pn 295701 316779541418118112), (pn 17709 346847080219442176), (pn 570187 706706073924133429), (pn 287992 441100269200407298), (pn 999961 401024500142715125), (pn 566700 462352391863240948), (pn 274932 236118184246135461), (pn 345559 868583769874120479), (pn 566687 704218471124621145), (pn 376694 763822865276619544), (pn 457812 520032641657472187), (pn 566701 271838363715338255), (pn 224 584380737804829028), (pn 943293 218859560531408117), (pn 1171164 181681444676927503), (pn 147 812996832983777688), (pn 773287 952657686024895086), (pn 85868 441207932021311017), (pn 251329 626226046459277792), (pn 17709 76387277279132672), (pn 566701 272199337587370095), (pn 553 404178605098417546), (pn 206604 74073995278040064), (pn 566698 190427217689502727), (pn 10227 306844489012960738), (pn 3850 829921830029004306), (pn 237374 265497340441946165), (pn 1771 108415666913595395), (pn 40209 872505295635236372), (pn 29516 299648258447842514), (pn 604479 141137449843163343), (pn 19558 454299764930494740), (pn 528979 698453610569420048), (pn 907727 473040432763519426), (pn 56968 446813932158460672), (pn 919942 324586486951904272), (pn 16973 328414107877789697), (pn 37792 983096272774942724), (pn 86220 419924534096826464), (pn 307108 529621469667303427), (pn 189518 782895377153951232), (pn 1060209 403372536142761041), (pn 14167 551230311141548036)]) else (if j<2 then (proofWord80 [0x3c0038, (pn 939455 917297992165374495), (pn 443906 426936165815934979), (pn 906832 719513778203704014), (pn 684448 127221712621697568), (pn 553434 315914984047763459), (pn 906832 719513741632228913), (pn 423001 128242245932765252), (pn 897250 240285338833772547), (pn 76360 885459540766359672), (pn 2367 803536608235356948), (pn 1174162 642205669764882435), (pn 906803 450619770934395000), (pn 4427 265289013310787386), (pn 1154720 729240933465367863), (pn 380152 46765529885490356), (pn 1066970 595530669711047747), (pn 1173623 13400497688220576), (pn 187744 548379319393640536), (pn 108319 418445987160524433), (pn 292788 54679300614512643), (pn 906816 659677452321947768), (pn 4320 131989873971171072), (pn 31059 801296027020859097), (pn 1006740 285416912593129848), (pn 3341 698129840105138377), (pn 29256 247906375992991746), (pn 84107 933826316306097400), (pn 4427 326923575167991552), (pn 77016 220234218990854146), (pn 245628 366958336512137785), (pn 120885 251906986422349568), (pn 141675 318041143289700355), (pn 906701 788520702744985656), (pn 115308 39871152387079889), (pn 369154 274735083877687297), (pn 634411 201818009263669368), (pn 4142 293847788370857728), (pn 48300 157061207496382250), (pn 801760 63219486358954616), (pn 4427 302008357730907842), (pn 223950 871143125145346051), (pn 906770 682428818058673077), (pn 1163475 194941753973298643), (pn 1173023 176848069932974125), (pn 327160 517870065356577956), (pn 429440 337148070456804520), (pn 95924 597817344671123347), (pn 906832 717486460383411833), (pn 660921 496523271359833135), (pn 116246 225490295062479564), (pn 354315 839837429764456568), (pn 4427 259905858506460928), (pn 85148 383410537076384636), (pn 679716 406478159499493498), (pn 338416 41725376624971040), (pn 19419 521725166268244939), (pn 762493 806351352202002549), (pn 867519 990000710754241566), (pn 897252 686902027136131074), (pn 997147 977734036513357889), (pn 56373 385000884381945600), (pn 141671 469274151244259331), (pn 906757 250625975267098744), (pn 209190 375336049624604718), (pn 191668 915529954529805473), (pn 822863 139419337202119874), (pn 193321 924005719017785041), (pn 1095972 749754666777542705), (pn 366442 942985981502475512), (pn 297 877089858337599232), (pn 137154 138504423628972503), (pn 340279 228383987876233312), (pn 301936 442109533773590272), (pn 141672 596914338931017358), (pn 548579 91999111528524664), (pn 2878 980107352059940614), (pn 862026 668795635630605651), (pn 906718 120917651777011957), (pn 341876 31624571313654173), (pn 379230 515256058545792008), (pn 909196 718152224535538038), (pn 301936 345739405601803969), (pn 596162 462573658814179205), (pn 60791 249061114558034154), (pn 155543 29007187712151296), (pn 141673 660109483291566273), (pn 659435 965326526418518136), (pn 2391 411656945678943522), (pn 303870 918871335144784883), (pn 906699 939885964440154744), (pn 4427 353686402136018688), (pn 141673 659109057213662710), (pn 506315 290624286210937121), (pn 159151 528088713300017723), (pn 292787 337937112468101274), (pn 247405 86641888733954058), (pn 31759 404330898765645575), (pn 141675 318073677054050323), (pn 906769 545313657191207886), (pn 609716 475868212822540610), (pn 668719 211358144060768845), (pn 47214 442486893402870810)]) else (proofWord80 [0xee10d914be2, (pn 681590 55317972225974517), (pn 21652 806499740760693409), (pn 807985 276973888790994292), (pn 312249 231749376976953609), (pn 148755 625080165819373951), (pn 208409 9209183769956960), (pn 328475 841874145529462733), (pn 1136499 440800945047402496), (pn 1133402 543536393530855460), (pn 158125 510019566190723761), (pn 636963 826518322304801172), (pn 7966 687885830925516830), (pn 375 32118947011500992), (pn 28534 132682039758972486), (pn 163929 883023712513441820), (pn 221877 471495990722966322), (pn 45491 300219763498105329), (pn 1133402 543764666893863370), (pn 385998 195487045257942976), (pn 35418 616406677499607487), (pn 1133402 544589416937567947), (pn 333983 817624995573679052), (pn 322671 616695005815568384), (pn 1156554 863474784977762142), (pn 1106 809271098783521033), (pn 34662 513011397171876101), (pn 467784 770179178030568912), (pn 492232 952640893704209355), (pn 413208 86399417047382016), (pn 622685 988164683478862174), (pn 1106 838982940982582208), (pn 19272 163846399379273728), (pn 401392 246305144286264222), (pn 670 493661429630578624), (pn 23761 640168039377571842), (pn 1133402 543619748396862670), (pn 266151 514160915699204882), (pn 1138147 338689065070824789), (pn 1140963 877857764233379841), (pn 447200 155387837870107124), (pn 521395 72848257690280362), (pn 1133394 786165178012017598), (pn 533 57548533668774848), (pn 217 7643064361027827), (pn 1033347 404733617468676190), (pn 109721 256333225032785344), (pn 55998 626612368643160064), (pn 1133396 265116504037272126), (pn 682 245176243731774147), (pn 1029674 362934610176560757), (pn 276809 536782609759779636), (pn 564122 292195921479846400), (pn 308586 298279985744358), (pn 90405 645666580060261054), (pn 753 309703829220565952), (pn 35418 774602468126902818), (pn 845896 883333461087688830), (pn 1106 813690036046790886), (pn 720491 821756212228487168), (pn 227667 410520624032186594), (pn 404869 145894887582860224), (pn 12192 767945538438985728), (pn 320962 292958921239564606), (pn 1106 805052350209720962), (pn 299871 352559119395485696), (pn 94813 959751406699085854), (pn 676405 218853633344551877), (pn 422684 9971464193228332), (pn 1133402 544013930055147678), (pn 1106 838422450601984270), (pn 488766 11843610652211200), (pn 240942 327792383899402256), (pn 236785 214925573176406119), (pn 879974 925961932365127901), (pn 893853 126048224194868642), (pn 285237 822020547606741382), (pn 753985 625615232115979466), (pn 98333 991535379201984102), (pn 666538 961317370089700288), (pn 35418 624277075581050424), (pn 243494 716113917459056990)])))

def genData8 (j : Nat) : Nat := if 23 ≤ j then 0 else (if j<11 then (if j<5 then (if j<2 then (if j<1 then (proofWord80 [0xd83dc940, (pn 754845 219604180198344000), (pn 754844 933995039766991200), (pn 754844 71242350310839619), (pn 754844 65612850776621379), (pn 754842 918317547168061744), (pn 754842 917191647261218096), (pn 754842 916048155168329024), (pn 754842 913813947540687152), (pn 754842 628433505527911008), (pn 754842 627870555574489184), (pn 754842 623898020063330627), (pn 754841 765399341095048515), (pn 754841 760895741467673923), (pn 754554 87819557622253840), (pn 1193290 243029859434809648), (pn 1193287 937186849729333776), (pn 1192748 369887509308819760), (pn 1192698 794297995584391472), (pn 1183912 379810441147453744), (pn 1156506 282425344291345714), (pn 1156211 134520164888188210), (pn 1156190 420215877789337936), (pn 1126692 835680496576108848), (pn 1118429 954237258442051890), (pn 1118378 15399228052085056), (pn 1104263 954811524418475296), (pn 1085373 388854910904699152), (pn 1050458 237149135344617040), (pn 1050194 597042675503187536), (pn 1049991 682857864429946448), (pn 1049899 448556953742460496), (pn 1049899 160326571756407088), (pn 1043483 81485623246506560), (pn 1043411 600088454562876704), (pn 1042908 134804811277519936), (pn 1042893 938596768675842352), (pn 1042890 460392889211210336), (pn 1042821 304858637728270912), (pn 1042821 304788268984092736), (pn 1042821 287917354041508896), (pn 1018656 19386191179943440), (pn 1014854 23159866805504528), (pn 1014853 734419316990331408), (pn 1014558 587024311032531008), (pn 1014558 567338620758575168), (pn 976780 807572650723673120), (pn 944002 153977513870973264), (pn 902711 23464243211815184), (pn 902416 743663074527184416), (pn 895334 631677759212344626), (pn 891796 154613816979214642), (pn 891793 487354738645505330), (pn 891792 627167209817166128), (pn 891790 390006293942032690), (pn 891790 320200494352435472), (pn 867002 738623524787045682), (pn 863756 816517276716536114), (pn 863461 668612097095274802), (pn 863166 229098810732185872), (pn 753963 973243494040454754), (pn 753956 28121894196201026), (pn 753956 27858011405534530), (pn 753660 880234306760984146), (pn 753660 880199122388895074), (pn 753660 879917647150716192), (pn 753373 391489742838960400), (pn 752776 588015305434976560), (pn 752776 14912461642778960), (pn 752776 11538060189221202), (pn 752480 868115589742316864), (pn 752480 865898974300717379), (pn 752192 815596437335492672), (pn 750711 424123376697430322), (pn 750416 851538756084813376), (pn 750416 561053281584531040), (pn 750416 559100548933600832), (pn 750416 558836666142934352), (pn 750416 558801481770324272), (pn 750415 985665652629294400), (pn 750415 981218127832240434), (pn 750126 816060279925360704), (pn 750121 703633576463552320), (pn 750121 413429576939982144), (pn 750121 412866626986559072), (pn 750121 411195369312339520), (pn 750121 410931486521673040), (pn 750121 410896302149584160), (pn 750120 837795657380122896), (pn 750120 836687349659320643), (pn 749825 980407834339299600), (pn 745694 769922851959066896), (pn 745399 622017672342196528), (pn 736251 189878608686598480), (pn 735664 588128235235168560), (pn 717362 877976925523001667), (pn 717069 462270951602377008), (pn 717067 730071745901740355), (pn 716775 139102813084307760), (pn 679585 99035438609451344), (pn 679585 95661037155373360), (pn 679289 951130258988190032), (pn 679289 947756222838314290)]) else (proofWord80 [0x150910bf, (pn 415951 673663978554340030), (pn 1173025 83223993241645758), (pn 1172729 935318813884101310), (pn 1172435 363874386029392574), (pn 1171549 920158847706673854), (pn 1171544 732012076707951294), (pn 1171254 195792915777794750), (pn 1096949 557742441456022206), (pn 1096875 770766146197078206), (pn 1096193 533406377338286782), (pn 1022269 67281465024524990), (pn 1022199 891991188609249982), (pn 1021983 142748322320691902), (pn 1021960 84318230116643518), (pn 1021391 694016458193977534), (pn 1020857 30609346191245502), (pn 1020801 690377125058396350), (pn 1020793 327192617027190974), (pn 1020788 431779822013067966), (pn 1020724 152465290506870974), (pn 1020719 540779272071094462), (pn 1020709 519707151146500286), (pn 1020506 250300919347491518), (pn 1020207 643631226165736126), (pn 1020193 808573170870989502), (pn 945761 772695544608665789), (pn 1171826 44295015065792701), (pn 1021447 610145382232305853), (pn 1021156 785695845096960189), (pn 1021088 475096697128693949), (pn 1021065 416666604937491133), (pn 1021019 299806420662825149), (pn 1021009 499973630822007739), (pn 1173010 963872912128164027), (pn 1097005 190142389790261435), (pn 1021447 614646783100403899), (pn 1021387 950958919637876923), (pn 1021378 727586882720317627), (pn 1021314 163982624723910843), (pn 1021225 965487522171142331), (pn 1021157 78427621106729911), (pn 1097078 977114218336694455), (pn 1021747 360722784099586231), (pn 1021609 316387005930492087), (pn 1021521 113379576702386351), (pn 1021895 245414952226873519), (pn 1021816 261267232928981151), (pn 1173306 174797701280785055), (pn 1173306 120754505752322207), (pn 1173025 83189908649095327), (pn 1173024 785389383021310623), (pn 1172730 511182531377836703), (pn 1172729 934721779074142367), (pn 1172435 363840301710520479), (pn 1172434 489579023778255007), (pn 1171845 72815017072079007), (pn 1171844 491006240210620575), (pn 1171844 193768664536265375), (pn 1171549 919561812892791455), (pn 1171549 343101060321461151), (pn 1171254 772219583224951455), (pn 1097895 808463114382684319), (pn 1097890 633827142476050591), (pn 1097816 846850847570735263), (pn 1097757 457882561435218079), (pn 1097748 234510524572053663), (pn 1097743 59874552652054687), (pn 1096139 634292019220799647), (pn 1095992 60339429342266271), (pn 1022337 944737131340050591), (pn 1022337 656506755188076703), (pn 1022333 58331535638610079), (pn 1022273 678370448704618655), (pn 1022269 66684430273036447), (pn 1022258 992132063836323999), (pn 1022254 371438846100717727), (pn 1022200 180187479904956575), (pn 1022199 891957103752982687), (pn 1022199 752345515304370335), (pn 1022199 598660178020208799), (pn 1022199 305926202237203103), (pn 1022195 279708135363600543), (pn 1022190 460856534077153439), (pn 1022190 442842135567605919), (pn 1022190 370784541529411743), (pn 1022189 875388582518464671), (pn 1022185 470868146945937567), (pn 1022185 268206163714252959), (pn 1022172 221278043210059935), (pn 1022111 409172274721670047), (pn 1022057 217357958572224671), (pn 1022056 631890007013540767), (pn 1022056 352666830116556959), (pn 1022056 69784478522093727), (pn 1022055 781554102303408287), (pn 1021982 281963758218195103), (pn 1021466 921547599329431711), (pn 1021466 56856470874034335), (pn 1021465 768626094655103135), (pn 1021392 67218192736805023), (pn 1021391 923103004460925087), (pn 1021171 778146019335803039)])) else (if j<3 then (proofWord80 [0xcd10df51, (pn 329626 85534077659700983), (pn 475945 659526673103642359), (pn 400387 795800690057600744), (pn 551506 982000746008993511), (pn 324854 143408780297166563), (pn 551506 981994148942372578), (pn 551503 523229633980980962), (pn 550251 450464637003292376), (pn 551509 287826163039788760), (pn 551503 523217488951172823), (pn 480818 49885218289147607), (pn 480522 901980034742935255), (pn 475950 271177575878418135), (pn 475945 659491556510588631), (pn 474840 7768570765303511), (pn 400387 795765522867478231), (pn 343719 397971074173034199), (pn 329407 174528068642463447), (pn 324852 990469683517906647), (pn 324848 378783665073741527), (pn 324829 932039590373285591), (pn 323724 280316672272817879), (pn 248037 289382058289979091), (pn 216145 174717277268926163), (pn 178385 842519898421518034), (pn 555045 298074196240293586), (pn 551503 523211978644578002), (pn 480742 965866595904184018), (pn 253940 247478137911303671), (pn 476095 539036472118140375), (pn 476095 539005681363377619), (pn 555159 581137967180209619), (pn 555120 237691622434856403), (pn 552782 112880277622676947), (pn 552779 807037268405837267), (pn 552776 348272754567470547), (pn 518596 837347148779740627), (pn 518449 263394559036218835), (pn 518375 476418264130903507), (pn 480818 49599345467121107), (pn 367259 748443030569409527), (pn 401645 632314699983936500), (pn 552763 665578359636679640), (pn 103013 598316470724516823), (pn 477203 496008591012322260), (pn 590536 832829806974393300), (pn 555195 321142759583177684), (pn 554014 729522039977204692), (pn 552780 959396922570890196), (pn 552776 347710904125676500), (pn 551671 848909487628934100), (pn 548148 520791381039635412), (pn 518376 844950700409740244), (pn 480782 308470852180564948), (pn 480634 734518262369934292), (pn 291703 36496299271706599), (pn 404043 852018043061458918), (pn 405260 40089252129724376), (pn 555307 9292016579303384), (pn 555268 962881195182446551), (pn 478385 239424915304798167), (pn 401660 619136333530585046), (pn 443038 971935614410217430), (pn 442817 611006712683222998), (pn 423929 297996721696069590), (pn 405224 299505980142573526), (pn 405076 725552427456059349), (pn 555268 962879064876570581), (pn 553941 947976563167383510), (pn 555159 577200616041140182), (pn 555123 692518785119473622), (pn 329521 160882161837981624), (pn 472551 449822182597771192), (pn 396995 891939208835678136), (pn 396919 799119835997192120), (pn 245877 858644096099336120), (pn 26292 428859053704265640), (pn 61486 510708681110241192), (pn 41417 606077956570005416), (pn 23707 578845689588793256), (pn 3638 674197712368353176), (pn 359290 747017327713238936), (pn 283807 823189144182505368), (pn 132692 95737178233028504), (pn 132617 155839378653757336), (pn 61631 778800670526717848), (pn 61557 991824375621402520), (pn 60380 858968170957946776), (pn 45179 588929915856142232), (pn 43998 997309197371096984), (pn 42745 771633688520474520), (pn 41637 814067760268885912), (pn 41417 606060379285274520), (pn 38096 39205605009833880), (pn 26363 909974714999685016), (pn 26214 30179115035836312), (pn 23871 293681752779833240), (pn 3638 674127481933447000), (pn 511363 399247612372631384), (pn 360247 671795580788588376), (pn 137115 855479968644513624), (pn 101698 106858433353400152)]) else (if j<4 then (proofWord80 [0x30fce544, (pn 950099 329256484918583364), (pn 950099 326195444546852932), (pn 950099 326107483616630628), (pn 1006804 617196552731809604), (pn 950099 325614902407386692), (pn 950099 325315835244630889), (pn 987915 150144156439729000), (pn 685683 695236668035224421), (pn 987915 150140256609424229), (pn 912357 286413844069798756), (pn 959839 205658988843422564), (pn 950394 472693248479253348), (pn 704573 161166755046675285), (pn 987915 150122441085080404), (pn 950984 768486015804166996), (pn 949509 28959878286988104), (pn 950099 324752885291209517), (pn 24515 494076332788994853), (pn 666462 187841150307324709), (pn 24515 494040065548276324), (pn 1006804 615745472261050933), (pn 647867 869550435712684596), (pn 628978 403073333076480068), (pn 950099 243951184515149925), (pn 62589 484069675608020020), (pn 81183 802053071870858253), (pn 43404 870190097529279497), (pn 685646 711852157837743109), (pn 66426 406785308136543237), (pn 43404 870181301436256357), (pn 62589 466029966319375381), (pn 61703 995390155026003044), (pn 950394 337797225454430276), (pn 950394 333046476463858244), (pn 950394 329950260309973060), (pn 950394 328882385176417401), (pn 383452 96516597770540149), (pn 383452 96498155415852132), (pn 950394 328790026199684133), (pn 383452 96185885523628868), (pn 950394 328261401859772996), (pn 629273 335923083237250105), (pn 685646 585808267997991992), (pn 81183 675996830242034741), (pn 383415 130899886240289844), (pn 90628 408960920265020236), (pn 931504 790559044077736773), (pn 676497 479685189686084), (pn 931504 633789043833280517), (pn 704535 890202521882825989), (pn 704535 889834460365383253), (pn 987914 723124042656048724), (pn 949508 601962338616531061), (pn 704572 729653795998848597), (pn 987914 718621525125551701), (pn 912356 854894537295189588), (pn 950394 41174516995380820), (pn 666461 756146565716039017), (pn 383451 808549829531325796), (pn 950689 188780630259193125), (pn 704572 662094303996532308), (pn 987877 753074701303141685), (pn 383451 735911092561634901), (pn 62588 926222543034242645), (pn 62588 925923742193013845), (pn 62883 767795544872687109), (pn 667051 529697662658909701), (pn 666166 85982107688998405), (pn 647276 566675112820921973), (pn 704572 153169920362731045), (pn 704572 152079204827911748), (pn 1026006 596579998477178421), (pn 704535 187607444941297205), (pn 685645 721675914787279717), (pn 63178 788860204657005412), (pn 932094 78403121758590533), (pn 676495 992517793621464645), (pn 667051 259023739496945237), (pn 676495 704305009890416213), (pn 667050 971339269794682453), (pn 647866 357502577500731236), (pn 81181 794387720503539524), (pn 61702 30677500242145349), (pn 968396 388349673560053604), (pn 61702 23612295683217220), (pn 66424 390086369235406957), (pn 987876 148131871888216173), (pn 949506 920458538840985701), (pn 987876 148123092706627685), (pn 949506 920423388291764301), (pn 931207 750293476618506309), (pn 968396 386346041251690340), (pn 363933 469500232507021385), (pn 927370 811763513049962565), (pn 927370 811745920863917932), (pn 363933 460536996537522020), (pn 363933 460528200444499788), (pn 363933 460493033252279349), (pn 936520 394905699538129269), (pn 28940 586478915257586036), (pn 936225 247000245038961005), (pn 949506 902716835858174285)]) else (proofWord80 [0xefd644c5, (pn 457771 389578776914830533), (pn 457771 322033853209011665), (pn 230805 109544882473022929), (pn 79689 368582254944069073), (pn 79689 364078655316650181), (pn 306362 905501160667833605), (pn 230805 41696287665640849), (pn 230805 32908784578020741), (pn 230805 23892926669202693), (pn 230805 23681889155184005), (pn 230802 812494873903002894), (pn 155244 948767868657890573), (pn 457476 403671242483721681), (pn 240247 541171212175041997), (pn 79687 76258849293358553), (pn 230802 803701881847174609), (pn 230802 803697337771771353), (pn 240247 532172809013315021), (pn 79687 67242707916695001), (pn 320527 753374393727198673), (pn 230802 790190936936162765), (pn 79687 58244450783860185), (pn 230802 785687483337676241), (pn 230802 781192752817767897), (pn 240247 514149623000688837), (pn 306360 599873793170040269), (pn 79687 8687335711139269), (pn 230802 736130368264955217), (pn 240247 468972880648693069), (pn 315805 332694465645077773), (pn 381918 463384065775461637), (pn 230802 735857470337934533), (pn 381918 463305107096691909), (pn 155244 872056926662776209), (pn 240247 464539649765496205), (pn 315805 328261234761876941), (pn 79686 999675656805500301), (pn 79686 999398442436347078), (pn 155244 863120027432731781), (pn 230802 726643562897159621), (pn 306360 586283692011763077), (pn 155244 858691125876569350), (pn 155244 858686796549531073), (pn 320527 622761208440311237), (pn 230802 652822352208213449), (pn 79686 781255335485388233), (pn 79686 779000580734203334), (pn 155244 359007070982792657), (pn 230214 818220612276213005), (pn 466333 137662707370571217), (pn 79099 77262369908860353), (pn 319939 763314684723729873), (pn 230214 795715795393975566), (pn 456888 386683394204374285), (pn 466333 119648308861080845), (pn 154654 655208957041736965), (pn 230212 518855912686385553), (pn 230212 517730012779541905), (pn 230212 516823809039824261), (pn 230212 516683071551468805), (pn 230212 516604112872698053), (pn 305770 376952327475586385), (pn 239657 245220115444163917), (pn 305770 375905669715354893), (pn 381328 239631300570932485), (pn 230212 512104705133405381), (pn 154654 648304161458246925), (pn 456886 95397094306628809), (pn 79096 775642447416411333), (pn 154654 639296962203497605), (pn 305770 348883789546021965), (pn 80265 261454257891316753), (pn 80263 230264855248331789), (pn 80263 29850273783825421), (pn 80262 966865849698247757), (pn 80262 964614049884556365), (pn 80262 957858650443498573), (pn 80262 955606850629809225), (pn 80256 47225965883974857), (pn 80256 42722160098165961), (pn 80254 290822248646338761), (pn 80253 741382956668183753), (pn 80253 741316848531559625), (pn 80253 733501588600801481), (pn 80253 732376788205585610), (pn 80253 732375688693957833), (pn 80249 683639486244853129), (pn 80249 251364290761462985), (pn 80249 202880226023007433), (pn 80249 193873026768258249), (pn 80237 816452295412442321), (pn 231353 323438848549860369), (pn 231351 298859709813240849), (pn 231351 238065512890197009), (pn 231351 211457194059040014), (pn 80235 483864627923846345), (pn 80235 294647610315400393), (pn 231351 17595839334862025), (pn 231351 13083443612555461), (pn 306904 467859952083625161), (pn 306897 568270762319037641), (pn 231338 835350051193504969)])))) else (if j<8 then (if j<6 then (proofWord80 [0x3660196, (pn 3385 970484750299144), (pn 65 428747288804608128), (pn 131046 431011955421216768), (pn 1207457 361583595300652336), (pn 1207457 341370173132901648), (pn 1207012 261825222613930288), (pn 1207011 110029617911828784), (pn 1207008 804186608697181488), (pn 1207007 722566234128321888), (pn 1206996 122085242383371536), (pn 1206993 815081148872921392), (pn 1206867 333790190444859696), (pn 1206867 117599816144998704), (pn 1206867 83840411125746960), (pn 1206867 63556620616517904), (pn 1206867 45559814293079328), (pn 1206867 27527823596556592), (pn 1206864 813973422370833712), (pn 1206864 795959023861287184), (pn 1206864 721684814381714704), (pn 1206863 641911619346565392), (pn 1205815 547317838126796048), (pn 1205793 640683350638479632), (pn 1205706 341835050293986608), (pn 1205706 53604674141228304), (pn 1205704 918679975857801488), (pn 1205704 900647985162257712), (pn 1205702 669096777612052752), (pn 1205702 595086450923193632), (pn 1205702 542995988044679440), (pn 1205701 461006177553108240), (pn 1203765 764384119429906738), (pn 1203474 54977255342655808), (pn 1203473 998644876604199218), (pn 1203472 846339098508839232), (pn 1203472 845723371996305714), (pn 1203471 767148644636397874), (pn 1203470 616478939842136416), (pn 1203470 539933139339626768), (pn 1203468 253267811935522080), (pn 1203467 157714426018517298), (pn 1203467 137448227695282528), (pn 1203467 81168625514961202), (pn 1203466 2541121586680114), (pn 1203454 437297278498949392), (pn 1203453 302390172399487248), (pn 1203434 873660497183689024), (pn 1203434 799313719935747378), (pn 1203433 716235392948422992), (pn 1203433 646392215312058720), (pn 1203400 268000960433128992), (pn 1203381 764977284526490944), (pn 1203362 203576909867339074), (pn 1203362 165258929639310624), (pn 1203362 146153815594078514), (pn 1203359 859415920423519520), (pn 1203359 840310806378284320), (pn 1203358 723681981581034784), (pn 1203358 687406893924927760), (pn 1198750 481527482238685488), (pn 1198743 563998454585020720), (pn 1198712 435117830134140176), (pn 1198659 417581932448698672), (pn 1198658 317633798556468528), (pn 1198658 315381998742753586), (pn 1198658 283835910630214994), (pn 1198658 264730796585979152), (pn 1198658 262443812400187664), (pn 1198658 244464598262793536), (pn 1198658 244411821704643888), (pn 1198657 148931003554055472), (pn 1198655 992629600203359776), (pn 1198655 938568812488852784), (pn 1198653 686786590987584816), (pn 1198651 347131391694671168), (pn 1189301 153781806717537600), (pn 1189267 719058173059730704), (pn 1189233 456780515745304880), (pn 1189233 131360258294859072), (pn 1189232 31412124402434371), (pn 1189231 996508127778655552), (pn 1189231 978511321455201616), (pn 1189231 978438753687766320), (pn 1189231 958225331921718594), (pn 1189230 825605210008044864), (pn 1189228 517721507213149472), (pn 1189228 481446419588498752), (pn 1189225 60909709197153600), (pn 1170417 490720838641882416), (pn 1170412 879615362352911680), (pn 1170410 573772353137120576), (pn 1170410 573191810968503616), (pn 1170378 308278180579231024), (pn 1170378 250857285330191680), (pn 1170378 232825294634648880), (pn 1170377 118237163402907954), (pn 1170360 978426814441803072), (pn 1170360 959321700397532496), (pn 1170358 689507488200740192), (pn 1132637 367708522208661808), (pn 1132599 357292482826650976), (pn 1132598 204388570405621088)]) else (if j<7 then (proofWord80 [0xb098d7ce, (pn 508488 371687374712727212), (pn 15717 322048124509339444), (pn 930791 869006546605393009), (pn 761791 743183588244363739), (pn 60939 283132901603576012), (pn 1125810 281571864831375238), (pn 419168 432982952679728307), (pn 237420 628654127631614751), (pn 45134 915297875833492888), (pn 906922 257594702241040680), (pn 926181 181958290814110760), (pn 179759 127421864219048032), (pn 359786 311969900906019010), (pn 1184751 123024126996655950), (pn 111474 522703912384751990), (pn 362345 961314308129764555), (pn 697836 212829578157930398), (pn 432579 440684876844459436), (pn 88920 325656713014929452), (pn 1039333 249167898887505457), (pn 463690 90246863701448169), (pn 51600 547520765874613421), (pn 162153 161540796217472453), (pn 410599 877505650631922823), (pn 199004 988921498843103899), (pn 761724 43845270977990036), (pn 725072 822077613970376184), (pn 766984 558991479784606221), (pn 477009 923250283956067919), (pn 203789 690121595943970402), (pn 536896 528417146404546235), (pn 91229 67150205796008241), (pn 663941 142813727373060297), (pn 524269 473631085940217210), (pn 352058 789183003872355483), (pn 313077 646497013022911012), (pn 427708 426406273982021185), (pn 142714 300142922305376694), (pn 41731 463882314391994507), (pn 511296 990089194058062436), (pn 345952 758421873741022109), (pn 159113 600514956016177684), (pn 4890 153743157844560272), (pn 407454 359380607780848088), (pn 606681 128565410514241512), (pn 774174 249482071050067006), (pn 118630 6672339629233393), (pn 1097967 759054337470373411), (pn 70868 317686819918115052), (pn 871089 715231693797758279), (pn 315284 693074346800345702), (pn 269140 41248155332420481), (pn 461590 633794860047871515), (pn 588187 100830631272231128), (pn 1018120 445166429689187658), (pn 937945 692423199912960104), (pn 180406 714353257969772035), (pn 220799 845894932647522800), (pn 117423 640839216702779783), (pn 79146 647381086240765963), (pn 1127574 535167670042016628), (pn 440843 634103077580670389), (pn 617876 100416255764815916), (pn 510422 312325271550866801), (pn 419122 369814899222517003), (pn 653863 664942009643782307), (pn 1002646 556590663436731844), (pn 1182408 116448056430054870), (pn 182624 152182277965636187), (pn 383320 501404447998779410), (pn 134753 268558602713504352), (pn 662095 548585973264451701), (pn 322045 714120235815206976), (pn 1077292 812765778856375233), (pn 1164376 450927611973344902), (pn 71537 14868693640384747), (pn 719961 737793163989244935), (pn 148819 585688797243272732), (pn 257481 603291275648811853), (pn 309960 699085837472826393), (pn 363853 850068258006337504), (pn 916736 327957046658468789), (pn 631934 931325110495535193), (pn 831953 928499031097826946), (pn 787478 872093154010474722), (pn 95554 856572064661643575), (pn 909536 337691252861608713), (pn 271620 380788025414684136), (pn 331158 443498348215895088), (pn 916466 600919912444590111), (pn 736975 818591806561573920), (pn 1107108 97027571015617973), (pn 31645 627869549856428133), (pn 454264 50071616069429634), (pn 1099157 244223041565108972), (pn 99022 859939101610918194), (pn 607228 789176634654687240), (pn 727322 225117709683686896), (pn 291017 995124663203726179), (pn 612150 647188029967335446), (pn 37973 777020014133585536), (pn 664087 614547357231220534)]) else (proofWord80 [0x3a261c0b, (pn 64517 963868059428663487), (pn 1021736 55401551537766788), (pn 995282 286398288671819436), (pn 158606 275082896577839564), (pn 457427 401775092644525580), (pn 52053 361866174732735152), (pn 319204 732659488239846189), (pn 611117 618436725434013710), (pn 963478 487769995148284608), (pn 63161 124776882683509445), (pn 1192452 725581134635818898), (pn 830045 251822050566621946), (pn 1045954 221622149342271831), (pn 955908 266463652670438432), (pn 897219 580965955405679579), (pn 481333 412397137700681822), (pn 846176 548813545451939962), (pn 1152432 230373335927303986), (pn 413618 356980616319348088), (pn 1146288 125175327865931467), (pn 915952 343233515217140595), (pn 442116 484917958172866003), (pn 391533 400617469557394862), (pn 428981 738847165588627981), (pn 531611 532229310314796783), (pn 356329 250010044746777270), (pn 440860 550863819912206485), (pn 805805 986138451049011766), (pn 212761 755310967098198733), (pn 478846 541764771841875990), (pn 346709 6388906843005738), (pn 837267 202511258328083207), (pn 630463 217295942218657367), (pn 879168 81714044889035674), (pn 873884 241560128209660753), (pn 1008823 235505189085583704), (pn 163729 649608058643767978), (pn 818838 650584715367852536), (pn 400795 461882933129860422), (pn 465785 570755774793379753), (pn 1090071 973307294692317921), (pn 363375 942741317640983727), (pn 804344 129680501939692708), (pn 242352 542530930842678693), (pn 121057 627536469626868018), (pn 795918 513863803416674949), (pn 912642 43836281010006100), (pn 66888 210671386278575990), (pn 753426 108928415953242604), (pn 476753 396667387702284366), (pn 1134095 76596646699919498), (pn 544791 816509287749986051), (pn 394237 598008986831767862), (pn 323978 98268479180458761), (pn 768949 84387009777539422), (pn 361595 832360543300515008), (pn 1144572 708922159121802533), (pn 925931 682320037628237945), (pn 206024 15292651144368792), (pn 43830 950558153841283731), (pn 605820 917572136140876404), (pn 696886 360393892585359579), (pn 776272 581890580507255363), (pn 420902 714830610061590353), (pn 1164228 688946877375257978), (pn 673366 630954224656279774), (pn 852058 150476816248030278), (pn 605111 847426476854238986), (pn 219019 839168862539391672), (pn 686346 324871912066968852), (pn 153659 451965148551523784), (pn 701350 452474528053102723), (pn 321935 31069709191443517), (pn 652244 664854171328151585), (pn 838530 387116521607010309), (pn 55497 440854078383034530), (pn 190317 663072307408042627), (pn 1200697 139870429493080900), (pn 111013 276237974822797574), (pn 757687 344914445862754819), (pn 628100 286791856934619215), (pn 1200218 628770472792489530), (pn 599486 853762607248566240), (pn 1151940 509826688783026494), (pn 489339 378490706661465873), (pn 1126154 628884226940280501), (pn 72383 268946467556425971), (pn 805045 183837059081509511), (pn 649985 79196244088092589), (pn 282043 641607635201872821), (pn 1104338 35452597094773277), (pn 509105 963176001425495012), (pn 1103197 485802089130020481), (pn 940898 347653549663904371), (pn 260791 284772953374796195), (pn 695696 541953172397373655), (pn 738479 526103670684350914), (pn 1005293 684550229345173133), (pn 1183081 540334897633746492), (pn 523854 628143398730483428), (pn 167359 362248225321750838), (pn 810388 871690802810806961)]))) else (if j<9 then (proofWord80 [0x8210818, (pn 2956 996668532079494176), (pn 453384 211615809423865907), (pn 52555 358208740985210689), (pn 237447 697790674099773704), (pn 132241 283302216481915660), (pn 919392 790924161215906274), (pn 548256 5168774443501596), (pn 3261 334311688668744386), (pn 342115 118650656085299404), (pn 127581 195428995412282375), (pn 739 320960801250353480), (pn 311952 899193311847272595), (pn 171348 70819400861882116), (pn 910383 984498808843460850), (pn 255240 892077357555374166), (pn 51950 369336874099836705), (pn 719350 493962285583766071), (pn 57893 989976938978488843), (pn 815 333587079171678856), (pn 538811 290045711116160146), (pn 20233 498539639012723456), (pn 208157 890423213774708824), (pn 85062 551429353915353794), (pn 39957 414518024029942344), (pn 80933 994158556050893824), (pn 775363 428164665824254003), (pn 31899 910683181209230085), (pn 912306 498578580724942998), (pn 165395 905604313609179939), (pn 78585 834378817275626688), (pn 944524 281992584563357784), (pn 676540 735752583338028055), (pn 10555 214448840810439312), (pn 689991 725498775627641998), (pn 921020 285998616769462400), (pn 510421 787176283507167388), (pn 146517 980157864545096516), (pn 79138 587160821818778673), (pn 657048 853680649181088783), (pn 830 995979565854433544), (pn 283351 517758184380046469), (pn 154362 498999356938834146), (pn 233974 83971354573500492), (pn 59033 918854163796134946), (pn 833831 781162787149905972), (pn 103984 937033915951501840), (pn 622172 506041056469271344), (pn 614433 744467848856623125), (pn 23781 470357767547788037), (pn 912305 778037829044209840), (pn 174824 481888965788112173), (pn 650630 787719956510595131), (pn 510351 513597799164651197), (pn 1149278 970442876032102069), (pn 995734 964670118049307661), (pn 821338 319164726645365462), (pn 516700 702224298650941654), (pn 351430 773887734572212262), (pn 828836 949974542336092876), (pn 856530 366515346395511636), (pn 1103451 720435617022425946), (pn 731031 517159826833647890), (pn 1003344 507883568627035456), (pn 937971 57765040558150249), (pn 907669 329405183941580731), (pn 355831 174452974444590234), (pn 1030839 592968445328072099), (pn 664999 316684537526364877), (pn 95748 503826081837011176), (pn 492965 324310386722702979), (pn 53148 69197748011270195), (pn 1182251 371971000499125813), (pn 750871 216367088411007461), (pn 212232 562537153754410702), (pn 908600 122461371098785030), (pn 536638 300177615873402596), (pn 847283 865327273366995765), (pn 612038 814799360492260441), (pn 774114 239156885430573536), (pn 967465 316923705623080137), (pn 861326 557296624893968230), (pn 83582 330674235153210939), (pn 220799 971997646381593298), (pn 724411 472121846664283542), (pn 41522 280365220412610604), (pn 807346 308901781242694262), (pn 477884 995976357327472207), (pn 1148265 832952072165969586), (pn 466798 213005446688220349), (pn 690549 904438345713883416), (pn 965926 158710561842451656), (pn 441027 473560799894339446), (pn 298304 559662365784892381), (pn 840204 873808332384355101), (pn 536258 291409110546105944), (pn 1059220 22336438347074912), (pn 937858 68207389865962598), (pn 29264 829745202003841891), (pn 3273 637497963784055747), (pn 100526 280206863935615283), (pn 720583 743523298282152328), (pn 626970 703356069294930028)]) else (if j<10 then (proofWord80 [0x5a1002a, (pn 23614 793607557703797890), (pn 833425 842844969442861168), (pn 71485 799628411093683200), (pn 907875 830540474016399367), (pn 28353 816872558529218561), (pn 302397 854254859785808040), (pn 181972 613260332900556359), (pn 7383 890353660944843424), (pn 377840 173346984735298576), (pn 617454 29958325628635137), (pn 1134936 983681642371825936), (pn 242058 210659022836606344), (pn 8270 487483147684200880), (pn 491518 362163865150640196), (pn 59920 793513988550558977), (pn 923 129881479725871256), (pn 675365 909867494342427669), (pn 19850 174693151168856320), (pn 283351 234878444395960325), (pn 4726 690097391670149334), (pn 236284 471037769596049411), (pn 5943 493598933379187552), (pn 37871 230378138680197140), (pn 18905 31077403434951112), (pn 434762 285929985608794124), (pn 159534 76695453538337400), (pn 519861 791104881232201737), (pn 612585 750224025671042497), (pn 227605 323011289819158048), (pn 635184 830548073971386081), (pn 435500 687505103876465843), (pn 32491 72170653675950851), (pn 607009 389829491007852694), (pn 160662 3142158074253315), (pn 39883 519173863384584256), (pn 668270 806688277140079120), (pn 964211 826459961253174289), (pn 620268 32061581763413376), (pn 170328 252571658099984456), (pn 40165 482199325372386498), (pn 1135472 254405916785578116), (pn 91554 696924241599668741), (pn 605275 945827786323362248), (pn 340167 266302980077134343), (pn 156430 840970220524499112), (pn 146506 428378606762988324), (pn 231252 350184985782157608), (pn 231548 229504289971665944), (pn 626903 955712576691380752), (pn 548182 73791498393232518), (pn 308434 464769606250930370), (pn 191387 388272529058829572), (pn 911752 450553002642572641), (pn 227374 891769114023996452), (pn 638140 923543188461847240), (pn 1115373 860037714075934832), (pn 10647 249534562027184263), (pn 157466 165890327861610700), (pn 203241 754248539390662674), (pn 3252 685147608240556738), (pn 531489 825656200059105388), (pn 713173 97879665822429723), (pn 24814 346433115328529160), (pn 737141 486143168758968339), (pn 172386 135900659666523266), (pn 906897 765671931650296066), (pn 241039 168901985245147186), (pn 4431 905736146832884352), (pn 377827 420255088076675602), (pn 619811 181315324268815088), (pn 812967 88586337916573454), (pn 615835 478687146314990176), (pn 515132 489151213402689628), (pn 89787 260486341636326945), (pn 341228 845356725493088805), (pn 36626 609918207157338753), (pn 662257 532665749775343752), (pn 113348 344521196248112260), (pn 455857 669099112332652642), (pn 82680 639805180469906819), (pn 230032 953472625798062296), (pn 193750 850334316139957291), (pn 39582 697269516309564737), (pn 1059046 943471875666501768), (pn 132239 1107778901256969), (pn 158501 59731702319088432), (pn 510324 781715981642854470), (pn 51978 316530636888016833), (pn 643755 664585351560802867), (pn 43717 658705993884246528), (pn 759944 969080188005097984), (pn 538811 362314618611708170), (pn 766212 327428834987344040), (pn 236309 880357877392132136), (pn 2673 490713251144141218), (pn 77847 63050692897882683), (pn 57302 532229074946884192), (pn 916858 962409272842919054), (pn 921020 285998616769462408), (pn 229210 128916299783341831), (pn 762077 408860952744199200), (pn 453393 429904249430527019)]) else (proofWord80 [0x688c1b05, (pn 912306 66249067222450592), (pn 403997 701541120561965094), (pn 3849 900528580614882689), (pn 227743 898696017895314514), (pn 59674 108091251831610368), (pn 908909 272198427691008264), (pn 188905 75329582857474062), (pn 316854 545509439229854432), (pn 397052 554232807435624516), (pn 2961 647624229523360866), (pn 758347 523916925306549336), (pn 99263 137428434855138304), (pn 758975 578839840862831889), (pn 19784 790896726530670607), (pn 362485 478006195479913989), (pn 609779 319289737869054436), (pn 529292 792716393239945304), (pn 85062 552916417763616264), (pn 914743 492111928696375649), (pn 757203 248689189135369258), (pn 646997 672737881413649027), (pn 381555 772239278929807041), (pn 757351 111436441385247120), (pn 396992 631433922057637396), (pn 316854 401961466283954691), (pn 906935 345835767293460628), (pn 99248 151463576563682402), (pn 909499 856344912796770460), (pn 180109 463370399345578529), (pn 24812 38129400225859792), (pn 1067993 353024394064314572), (pn 54351 65291438010675466), (pn 10929 845753637519983488), (pn 1002027 913372126474010960), (pn 359216 23635239867895892), (pn 47229 156138046083306757), (pn 4135 568634959298102144), (pn 66325 444125148167324206), (pn 651730 999291743340145867), (pn 154511 874911222744367720), (pn 472624 336383016645441804), (pn 315376 62867644566635344), (pn 964285 875032329138962626), (pn 212695 701574631732556812), (pn 921465 31241045139557410), (pn 1060542 85332504722768084), (pn 227966 111970635336962096), (pn 657622 991119225376476483), (pn 247132 481571060926054992), (pn 396992 649441691393601671), (pn 157908 888170034427822372), (pn 226805 96324267061023107), (pn 229848 847094533654446116), (pn 82697 950550905153140234), (pn 611547 181445769272771184), (pn 633341 657257971686584349), (pn 22599 587050582108672129), (pn 604647 755858502853226630), (pn 96889 282732736172395106), (pn 304446 903104913226989608), (pn 99250 475011098037749268), (pn 625139 404846434452800288), (pn 784577 459823923159072780), (pn 362482 3479082963576325), (pn 609779 895750489887027398), (pn 189067 750759698561764163), (pn 40658 390793203780449328), (pn 648173 69449825664568322), (pn 1772 257775241908388168), (pn 311934 640459668558190725), (pn 155989 703236060516196552), (pn 189033 126991144420124165), (pn 4209 427739285705130028), (pn 217404 261165752039590961), (pn 651729 847497240286726017), (pn 152315 631000681887998032), (pn 11846 590772895512015627), (pn 161894 539361496865669456), (pn 382747 61415029640333364), (pn 3256 795529408876186818), (pn 645121 300600518367826061), (pn 103988 999280777150614533), (pn 739 384398232741806544), (pn 463170 371041021949933588), (pn 316557 88946088849965216), (pn 567016 312282886562709546), (pn 23614 723733010684054562), (pn 644937 589658105734639728), (pn 103988 998154879393352207), (pn 4723 232388692790780384), (pn 349722 795767777828291852), (pn 465311 490871294399612160), (pn 208176 337147476949706842), (pn 87423 734672679463192449), (pn 189965 363456477903307864), (pn 99249 304606234853250048), (pn 832705 357641035937063208), (pn 245573 467199568888208389), (pn 760304 31568509511342260), (pn 200866 726939657448247298), (pn 912969 791511288463656353), (pn 189853 935174633751887900)]))))) else (if j<17 then (if j<14 then (if j<12 then (proofWord80 [0xca270781, (pn 492357 713877078892460082), (pn 649941 70129880208837634), (pn 152564 887683570820459579), (pn 53175 89587394824648201), (pn 765622 31194696251556480), (pn 718459 395106288670149128), (pn 913193 677236974287489441), (pn 492380 542557455969764402), (pn 49629 850877114993805505), (pn 454842 279021599986598032), (pn 11846 293252744803919493), (pn 610072 161334539412144512), (pn 411078 945422413658601995), (pn 612656 905795250126278792), (pn 118169 931537844884488769), (pn 1059434 775879942609928496), (pn 245574 620125471542225415), (pn 761189 41690263064969552), (pn 373300 15804657103276811), (pn 610371 348865524412351777), (pn 189853 939678272049721409), (pn 59664 287423797097269121), (pn 303431 403682184139423888), (pn 13016 508579362404178181), (pn 307253 4693289782485186), (pn 191387 388272529059092228), (pn 42135 861003729482056128), (pn 47518 934446576257509414), (pn 645814 771329650640356673), (pn 322053 238693496449450224), (pn 13056 893499073267775756), (pn 918065 347759684232364992), (pn 576627 115559748634763338), (pn 70867 782437454006196771), (pn 419334 126584783117910576), (pn 288308 932529127210645527), (pn 22447 970541175253043073), (pn 29451 182565736583446640), (pn 14240 937119277210412805), (pn 610074 900649046826205520), (pn 382747 56836605215010819), (pn 15655 816948476238039489), (pn 832834 971554525013387294), (pn 28943 525794184988918992), (pn 964156 531378223071635491), (pn 24816 75265352687557381), (pn 912306 498576918719574210), (pn 198517 93181668190121987), (pn 8862 224728168834958721), (pn 190001 968410972938914867), (pn 43126 207717927877083843), (pn 380004 135754626412880048), (pn 132237 830171602258244361), (pn 913193 99085376026566872), (pn 236328 342882120464599303), (pn 649036 590049941997061921), (pn 38221 703392912109259821), (pn 653491 500854170234880992), (pn 1020871 235272125966286857), (pn 47251 360018223197728137), (pn 914226 838176068119872224), (pn 453767 71141430588184662), (pn 82710 592415620878045956), (pn 230328 750143061109440560), (pn 241016 33869954650501653), (pn 626316 537705181301752600), (pn 727770 549196039322086451), (pn 47251 360018908107379844), (pn 757644 873483221383458994), (pn 196146 664043594857373699), (pn 348023 843826873227905313), (pn 946356 414940203102458036), (pn 127624 436752371613197335), (pn 22446 815159992971364033), (pn 776074 6703588866769296), (pn 434808 447914180785236115), (pn 469590 990396870095539841), (pn 227651 953636228999622804), (pn 146508 756785836279998470), (pn 6571 800248301387712097), (pn 113853 358721369089593426), (pn 60255 160260070910984963), (pn 230069 955505540733510192), (pn 586044 151224848837818389), (pn 24511 843596556848336257), (pn 906916 771091160666288332), (pn 184269 223866099754349322), (pn 7089 967568352621921440), (pn 1020547 723401549255359539), (pn 49620 617367572884488963), (pn 758088 836995708009021776), (pn 359167 501747107477860875), (pn 163077 439359736908761522), (pn 434762 317580691698718790), (pn 28337 413101624358636065), (pn 946356 125969969448006184), (pn 638139 190205974269690544), (pn 718353 594476919649215646), (pn 26142 657401313576620803), (pn 454675 547020336040415560), (pn 267046 808266887898673206), (pn 4143 33285857676233346)]) else (if j<13 then (proofWord80 [0x303c8e83, (pn 2732 605412755927916724), (pn 179612 615059327801133587), (pn 821 943814683583914184), (pn 132235 787068016961918083), (pn 153181 908030083488844192), (pn 269401 73810146032100867), (pn 608377 153506038572966439), (pn 28948 143679866906289865), (pn 757203 500979533048816040), (pn 425354 482426243225643276), (pn 766802 910905519439085744), (pn 1004335 776038716639961210), (pn 122885 374862707863624486), (pn 759788 136527467155456812), (pn 250461 366396126310733854), (pn 635184 253522991948055384), (pn 964064 288677155418914955), (pn 62630 754170664906267397), (pn 912306 498559541386619034), (pn 103977 446399256269956873), (pn 759603 560930554878035136), (pn 1134013 866820249939121699), (pn 27175 529674277749459361), (pn 435436 69998516819575088), (pn 283504 602737543580758154), (pn 313602 437952369644995488), (pn 869543 176307152420692042), (pn 70867 782440205063457986), (pn 379967 909547502123659508), (pn 250522 990779810646092823), (pn 22448 535464613666079528), (pn 727650 600261922458744859), (pn 632226 138272700828094209), (pn 906898 432752106466332788), (pn 108702 111976896469411459), (pn 229442 694078814195744812), (pn 250460 765670197647399955), (pn 15950 669793936329130792), (pn 765586 482615942773746746), (pn 40162 899528909871125123), (pn 456595 827137281110796492), (pn 184310 738071688507837199), (pn 385909 563705125162025408), (pn 42773 564674119911372821), (pn 22448 545317406082041505), (pn 359841 339577156644225035), (pn 75619 26565047858767622), (pn 913488 246707363280405090), (pn 241020 681590296132229122), (pn 924123 378028521041627521), (pn 1059508 562768052579677251), (pn 57307 733895451397605903), (pn 8265 9643975216906824), (pn 538848 237788397681258774), (pn 168543 444014917929275009), (pn 906879 323404957493938348), (pn 172497 931374693906910540), (pn 915628 935263554795669153), (pn 341376 347040631695225941), (pn 96875 439809895842462720), (pn 852278 434618699281965408), (pn 359028 991486144992793100), (pn 918211 479433389877461428), (pn 363931 429745397858332674), (pn 690358 810479306790602113), (pn 227780 442209634581834802), (pn 650536 558537005201277704), (pn 737141 486072662575052824), (pn 26290 659757719371389316), (pn 455413 443096214446917734), (pn 82673 697518792971457411), (pn 229848 558089212351570509), (pn 664718 71193286477349507), (pn 228372 331796740392296872), (pn 415909 743871677605894165), (pn 921021 442299334671075520), (pn 963861 239313931098556530), (pn 127589 250367868848770082), (pn 833831 781162718396199016), (pn 95105 702484480960774670), (pn 614647 387450632649122120), (pn 311943 747878873326959116), (pn 768725 123227476882624704), (pn 491504 500099605252343858), (pn 15060 332708909315164193), (pn 946467 203432942718741554), (pn 47858 384731287212134146), (pn 1135592 447212383403352392), (pn 349685 789634678100083468), (pn 766947 745541983713444320), (pn 434766 929255674190833698), (pn 22155 131869906497314435), (pn 154254 486205111489228956), (pn 179622 925991299955842064), (pn 911494 917626636075311776), (pn 737113 746001171644994612), (pn 620563 181092799806358528), (pn 1153236 27252929181347906), (pn 317298 417193724169751202), (pn 379709 402646710908465256), (pn 672993 764854109315815955), (pn 889 987640101198759264)]) else (proofWord80 [0xa1b05413, (pn 15943 611817554265056048), (pn 718224 323020958383249429), (pn 923680 79712270037028224), (pn 211077 123739103862581356), (pn 108702 111942046590798530), (pn 417488 370538722615833710), (pn 69121 727880856227306512), (pn 768789 264120334206550608), (pn 557719 274949423195628807), (pn 913931 401758627923230898), (pn 278843 456030833763211298), (pn 33059 464298435731032770), (pn 304336 186787534955765868), (pn 709635 933566625173234711), (pn 19779 453148404570727392), (pn 1105966 74823263012322363), (pn 61596 577246192558936208), (pn 1115253 956439017326348456), (pn 181963 398885596249725763), (pn 721381 474793276770026284), (pn 846124 603331312060235804), (pn 636365 422167419677443776), (pn 1011481 869683376750117088), (pn 165488 98877173804444169), (pn 613472 709614591512463714), (pn 241016 38361460149064739), (pn 834717 765591858649531168), (pn 831187 872473475281605136), (pn 621589 559401378516418952), (pn 387538 693097905399027731), (pn 172385 702426446349340801), (pn 906943 623383628818499650), (pn 70837 817591643172965506), (pn 493526 246490718194418235), (pn 59076 317742462791074319), (pn 739 320960801233576264), (pn 311952 899224116444298383), (pn 16099 982773634091191554), (pn 246541 674425494056091764), (pn 108702 109725372070503941), (pn 344146 352105850091012140), (pn 198519 419309559883802662), (pn 642275 302310507893886659), (pn 380604 322094804908876160), (pn 396881 712300122826354693), (pn 156577 981453469854363746), (pn 96866 190501496936239139), (pn 229479 10824355772932812), (pn 128195 744258059087144983), (pn 22446 806080233464013608), (pn 841375 92966154245030104), (pn 15554 106832695723566728), (pn 8419 503996918420425056), (pn 387499 448881992310005814), (pn 3003 79930186482879170), (pn 341930 506812911970734797), (pn 129932 581094954028267034), (pn 27175 527143956956251792), (pn 944750 5674648980711445), (pn 322457 163055548034613576), (pn 226839 702016832074421380), (pn 306366 157650050918842404), (pn 240965 323335392001283087), (pn 667 759555057925169536), (pn 321397 632159055960221831), (pn 158498 748678568992489888), (pn 415736 705494806348438021), (pn 4134 702464918648455204), (pn 127623 891251121724351502), (pn 668 769277267969737576), (pn 954776 524392902657589488), (pn 168898 448467845963594252), (pn 306658 836720153063033048), (pn 238682 516211293460641033), (pn 612142 882808027703215040), (pn 52066 25835806169518096), (pn 14761 216213203997721008), (pn 8325 288998677258458385), (pn 611700 662959128063397986), (pn 96884 673274329544985634), (pn 379598 577609563307090000), (pn 671209 22080624217817665), (pn 757064 618621924773470448), (pn 10655 890668042218246275), (pn 906842 407392208369059922), (pn 77988 224798053083680290), (pn 304040 714165673720533192), (pn 127624 440690826556763136), (pn 760304 826386740570653456), (pn 510026 22929872594166038), (pn 25540 678261070488600944), (pn 304864 946207594293282844), (pn 2959 268596384588106241), (pn 908686 653827745604264022), (pn 80326 374678805400454785), (pn 492169 220653905078330510), (pn 921168 295959933249260673), (pn 906879 751370191942092904), (pn 108702 116490928034945924), (pn 1136949 544578938917552576), (pn 52251 204418804975204400), (pn 48444 66610957581879682)]))) else (if j<15 then (proofWord80 [0x2c8a0248, (pn 661555 884507239057223956), (pn 162932 173786046234591872), (pn 718445 850732725992040498), (pn 622482 222637417321991202), (pn 1097401 646534599534752809), (pn 30721 337020061722739464), (pn 850782 806307523816102172), (pn 17872 602828606435626752), (pn 208762 722300882667636922), (pn 59044 5860421875796994), (pn 1021839 121468700735097870), (pn 519 392828222507623080), (pn 585684 134537186702807568), (pn 14916 72278712937268016), (pn 869561 501625562154721282), (pn 317297 265115959681649250), (pn 191182 487974066188798016), (pn 648774 896166821562027650), (pn 228667 354190880761545008), (pn 113349 535190323667805573), (pn 307840 994643528426848612), (pn 89789 528798045892905666), (pn 75586 760000395425640986), (pn 630457 836601890434720392), (pn 538829 736895334983151753), (pn 913931 401758487798583648), (pn 363857 534603523444967751), (pn 611035 503709737398437056), (pn 377835 570695687227099155), (pn 15348 269660246282912136), (pn 321129 304580659255317635), (pn 152591 611709018308157664), (pn 240896 33123023143048195), (pn 40880 795957971556327500), (pn 75616 129633253043733121), (pn 454898 160002796550626334), (pn 31899 53599165955577092), (pn 907875 154877427675771052), (pn 113338 821651256511172099), (pn 229405 79239406777352268), (pn 75616 133592061857254412), (pn 887 607344690954765104), (pn 699260 943785939987212937), (pn 159535 87052081732944688), (pn 510421 789251944455393282), (pn 317291 786485669631395488), (pn 831505 481126923463062042), (pn 22446 229337524585202160), (pn 463170 371041019792740494), (pn 162633 563172815121826224), (pn 425271 456478125333991426), (pn 309911 68461409299104800), (pn 982293 963448680733250076), (pn 636353 872180947232367216), (pn 463170 371041019788546190), (pn 162338 415267635769000752), (pn 415872 811052976027226114), (pn 308730 621624211335414912), (pn 982293 868802673602509332), (pn 623948 436792056734745648), (pn 500949 302763239494416408), (pn 19199 325416318489462913), (pn 302453 302608673458260082), (pn 127559 237810403953085474), (pn 644346 716331227528454284), (pn 133499 730931200216282112), (pn 835050 898193163509088464), (pn 9515 83851662662178308), (pn 908170 267176383621415360), (pn 418123 300244300317334277), (pn 610443 295345113774985400), (pn 128214 193854261112097797), (pn 739 32695240726552904), (pn 236210 568048659248726284), (pn 766947 600721595293582064), (pn 566986 316079644576612380), (pn 3255 280347409042277633), (pn 516 549599685924423208), (pn 637540 813250133841085889), (pn 463576 559971736387600496), (pn 13045 337249233271659654), (pn 758236 986194776574664898), (pn 191387 388224127204864267), (pn 916734 766038848966820288), (pn 52158 291143002786667028), (pn 20078 128710060097471937), (pn 228048 603731090376502311), (pn 40162 41178941998240386), (pn 304297 691550364521932988), (pn 181926 505396592008858818), (pn 455599 560249711121395868), (pn 181878 40453763349121047), (pn 22445 944697253103256456), (pn 775160 469119943982760141), (pn 211531 172506675697689992), (pn 613472 709614591529705706), (pn 241013 746046869971186476), (pn 608487 977488051617596608), (pn 982893 536692965634264102), (pn 24814 344748391113098977), (pn 435546 759241262134536371), (pn 210198 373855252491019783)]) else (if j<16 then (proofWord80 [0x805408a0, (pn 1001843 58304873998260400), (pn 99220 427797268729828356), (pn 493858 359730669942257786), (pn 77976 158272031605404682), (pn 757 217887101588373712), (pn 8322 980339813393379974), (pn 608153 177814125418565780), (pn 99248 151395827926701059), (pn 683748 890213434745106584), (pn 94513 101965819243415566), (pn 617450 430032185775784808), (pn 850782 716129979195746446), (pn 619380 860934250816488272), (pn 718187 452121384126335036), (pn 2968 202117914907806465), (pn 38701 426789476899801624), (pn 619811 180575799938679424), (pn 727696 617788836493152524), (pn 616867 775635842451161412), (pn 236259 88743651143066373), (pn 610666 856036470025420836), (pn 274109 515837863226794000), (pn 619297 769444223516295960), (pn 850256 610939659612338317), (pn 466932 62358714152698178), (pn 250513 900300799631956547), (pn 721047 558203221219558457), (pn 58490 32925760432178881), (pn 765937 294923330294409486), (pn 318034 848902118836014256), (pn 1002082 956085060666839090), (pn 10338 1409757177512732), (pn 189005 439484095699104195), (pn 230069 523027124182785179), (pn 24218 571018824162348288), (pn 172867 222190199050193002), (pn 59181 337463108610393184), (pn 453384 174995459562068013), (pn 625130 181335653411357960), (pn 1077585 722878794234123315), (pn 59055 105481984676332256), (pn 756280 249034450992783466), (pn 59636 608569598015997569), (pn 189817 271356907575109682), (pn 657045 962365402749406475), (pn 153072 64935812324016459), (pn 62601 356930971075226758), (pn 152204 788582671450269824), (pn 134702 840533254432888195), (pn 683601 352324598795952213), (pn 59071 692521430436742544), (pn 916619 118575300054636565), (pn 316553 627505496467145136), (pn 434868 447076252081199621), (pn 683712 754281253591384100), (pn 141777 162428419487582213), (pn 665 957868237700350288), (pn 321379 185443596967898138), (pn 166919 118069855358239140), (pn 271743 715801731267566147), (pn 645897 541308453386039401), (pn 63212 425319189864122049), (pn 766075 727124554039305267), (pn 59060 736108385573805062), (pn 170928 17384983572414576), (pn 115712 689845916791243872), (pn 942348 558031008024283175), (pn 27175 529674345058902944), (pn 1030408 256142313009815848), (pn 283504 594856784042537355), (pn 313309 309772811976508128), (pn 727733 682760299684466838), (pn 165388 971190370476887202), (pn 947427 408192392825602096), (pn 312963 495161857563456539), (pn 668 842541020225931793), (pn 463945 882541294146880568), (pn 664713 745622733592995589), (pn 911620 654941948728299720), (pn 198498 632926699701937671), (pn 4504 611110071370186792), (pn 240968 153814783214265370), (pn 26584 657412098677835457), (pn 454916 65795447179165776), (pn 14202 7437583047733386), (pn 764588 147424817612382552), (pn 385154 438124075655196748), (pn 70838 971784868635937890), (pn 985095 190371846373179446), (pn 129964 321356277246630934), (pn 22447 966037583835644696), (pn 831911 805134619518445750), (pn 63188 767194831312399111), (pn 761040 225526487070349556), (pn 269403 370815087832865670), (pn 722267 928231197351478945), (pn 492492 254201223525259346), (pn 82121 501632656666810899), (pn 998 107409734557172384), (pn 567173 150051840312778782), (pn 33377 239138898007958664), (pn 915180 552148233815843018)]) else (proofWord80 [0x330961, (pn 756759 269544280359749650), (pn 620996 310699453897285856), (pn 83249 594756065737971844), (pn 152886 777347026557513884), (pn 158335 439009745368649347), (pn 456707 482244718350540876), (pn 77977 892168897221117454), (pn 815 983504279332733728), (pn 349713 456398404584241168), (pn 166772 983155179022910192), (pn 307184 489065633140454667), (pn 916734 874406646281011648), (pn 52084 485547497994850690), (pn 1059804 17411069095149640), (pn 355382 884239118345970054), (pn 459696 897736137962209540), (pn 241018 348697041662123526), (pn 307031 250228905704456512), (pn 47435 888025460092738594), (pn 628686 381159103946688193), (pn 227873 539912091647950858), (pn 35436 497820909392498434), (pn 152591 648054612032966854), (pn 219631 566908380332954244), (pn 306994 537413607265075248), (pn 141796 766584926731506115), (pn 758974 803393184302235920), (pn 86524 766234327849115398), (pn 762224 801609955915780354), (pn 250518 487221443976261634), (pn 997318 40971010799864193), (pn 1135324 933359246531289240), (pn 90982 856312665240262674), (pn 622179 855503057279304488), (pn 690028 528835696808439091), (pn 45183 18267757116528260), (pn 906883 993756556987615320), (pn 89757 247552538891848898), (pn 1023169 738972256904840000), (pn 62107 945683937034532378), (pn 631047 564554883258303240), (pn 737141 486143168760302630), (pn 328229 560826555797739140), (pn 759271 156841639250700434), (pn 134688 985225806252870476), (pn 916809 526919798698181056), (pn 42659 338749730127092736), (pn 533260 424769197455245776), (pn 463207 309348617971613734), (pn 25102 137854266501415520), (pn 458475 769243402986653961), (pn 918065 347196803471280417), (pn 454749 184679081751413301), (pn 59664 298121510383194051), (pn 851078 395926543931408713), (pn 74422 540333045670483460), (pn 756926 385152498491136176), (pn 106255 637846378996107938), (pn 304373 188327018667753696), (pn 180760 866275057788295702), (pn 626321 149478698162201488), (pn 954619 555649766061030939), (pn 321283 785222736625405072), (pn 1191018 895242152271538272), (pn 103931 853346419241127235), (pn 191700 727726379792646329), (pn 189070 62259715489964582), (pn 36034 6008973557647249), (pn 1003209 117992833033789992), (pn 415909 785560759675146766), (pn 921462 288828970510715056), (pn 1001773 914575013769586834), (pn 141756 376018123616691974), (pn 914079 333956809372599456), (pn 359172 113405663363227670), (pn 605055 747197453927760616), (pn 690010 163226845365941294), (pn 328228 983945242446273926), (pn 762224 801047040019816536), (pn 85062 550308438387526818), (pn 342262 476113528750125161), (pn 103986 668669620333860882), (pn 14908 285780030563337000), (pn 690028 528835656999524620), (pn 766212 615095160464998560), (pn 1001843 107879718771435664), (pn 141774 840799707587483140), (pn 1063127 441579403353849896), (pn 142945 27374627893019074), (pn 540564 803311053695983624), (pn 665310 97223037124090245), (pn 156284 997103461618516312), (pn 307203 75524718437132312), (pn 3555 39375244519475778), (pn 531378 388200404979603576), (pn 127603 120650736046199313), (pn 621588 406684814037681281), (pn 95638 118316836766362677), (pn 40162 40898162274737798), (pn 154362 553165646177521932), (pn 238647 962374015595622403), (pn 319660 609026761014118305)])))) else (if j<20 then (if j<18 then (proofWord80 [0x8681704c, (pn 66153 786734545150315650), (pn 379487 608824221509150257), (pn 657633 949516229682086808), (pn 935859 352175658779550769), (pn 46664 947430318717281797), (pn 609924 500282855710247110), (pn 212681 839461992391085859), (pn 683676 438098902452176032), (pn 1133424 682202192615097900), (pn 649361 161822325452047201), (pn 860587 683533434218971432), (pn 283471 128627223265302033), (pn 471365 484511135855678083), (pn 607709 807948505996151032), (pn 276491 529980250960235564), (pn 1065820 378653634146371713), (pn 1097582 931048267994690617), (pn 662953 545115946438913047), (pn 22446 15276845127115600), (pn 935859 388318951028334832), (pn 16581 359902240261809416), (pn 159830 235097997434012272), (pn 718482 795889184011896964), (pn 137054 782407249464141320), (pn 1065637 351730805906998208), (pn 52190 682722558814493210), (pn 17709 526773419954504984), (pn 1153171 328954257801191600), (pn 16573 289451692847277192), (pn 613472 132590340105519840), (pn 642800 360244527105107986), (pn 315819 798601030435899777), (pn 794464 421175351831478822), (pn 35448 317930515058624161), (pn 463844 254100712973150247), (pn 44874 165200411186173698), (pn 170854 554927739926118560), (pn 174877 559098164716024389), (pn 4135 568632449849308248), (pn 670632 7926443455939921), (pn 86036 488867710403625102), (pn 14328 86814411824382560), (pn 401772 626169086783523085), (pn 312272 36657441230850976), (pn 680067 174287372436156951), (pn 521 51209490217378568), (pn 869626 227374950260722994), (pn 16837 566417407154717296), (pn 720437 826451209961214068), (pn 108702 109725919138024771), (pn 78842 862125803160936556), (pn 122846 723275289703511066), (pn 25993 782741509891621768), (pn 916997 592529979989901584), (pn 283505 761288547446438926), (pn 14327 365958100429045968), (pn 1002104 131871830492471418), (pn 118156 84095411104297541), (pn 4135 568633274995654712), (pn 57309 441304974301800064), (pn 1077604 250413484592896014), (pn 316706 538788660413464752), (pn 269401 62621276799775238), (pn 948609 153439539706237128), (pn 128158 809107751779110211), (pn 305931 45722624637698377), (pn 62630 211495569806994694), (pn 152094 308317102396852321), (pn 1065820 342519215359035841), (pn 1135324 933359246531256461), (pn 132296 76375148237722658), (pn 631047 567210755803825544), (pn 1143846 581004432325321000), (pn 283357 40060979955775500), (pn 164261 58667418788563712), (pn 265486 504851043118155956), (pn 181949 563837450798763534), (pn 15657 11667056616279074), (pn 1135619 828499347046348888), (pn 99263 145888083742297729), (pn 1059213 207627128037933065), (pn 68508 932631006150136451), (pn 604630 83812871790366918), (pn 212508 806023819626089569), (pn 756833 52153461187101752), (pn 59649 853372442505904928), (pn 349713 382063699390382604), (pn 609927 181419737891815744), (pn 236203 694380230074242821), (pn 609334 184293460602867793), (pn 67350 842661350886540560), (pn 935877 492145702611992717), (pn 316854 681455939130048836), (pn 233969 355022027149154821), (pn 610443 765656401895182488), (pn 99262 7602199909106243), (pn 380299 482214486565012248), (pn 878526 198928331002366992), (pn 461025 927947882934403408), (pn 384992 848753757286569219), (pn 115256 409925077512073296), (pn 77358 746256960405243073)]) else (if j<19 then (proofWord80 [0x8521083c, (pn 2964 820976144573598242), (pn 418152 561517596178960568), (pn 180772 383091446480654352), (pn 622179 855415715546104656), (pn 708982 666501839372037146), (pn 23627 983597364717817859), (pn 906879 300878167548516448), (pn 94521 184190582201324739), (pn 191922 701320838771016128), (pn 56936 33328329025195057), (pn 43704 967552882793843073), (pn 397943 432254383372829000), (pn 311916 193716160856339083), (pn 313157 696791878595412704), (pn 522250 757171248355164228), (pn 68506 599260060969866501), (pn 80357 514548224306643264), (pn 61570 792353587402408988), (pn 25993 782889154552923841), (pn 398210 774768234275356944), (pn 236321 254149206702313613), (pn 618935 685456908763925248), (pn 246541 419466462159063152), (pn 99248 151145952898979141), (pn 5650 111456686573356096), (pn 945248 564290908998625302), (pn 21265 637647478341043472), (pn 945165 518238391946193942), (pn 23923 419731682465680896), (pn 179929 938383610128207873), (pn 914374 698879676872721472), (pn 1057851 696505280946803225), (pn 24812 39463933268329745), (pn 10229 377616241806551091), (pn 31901 361979853107239429), (pn 302416 841554085672145154), (pn 191387 394992721315501637), (pn 155251 295769544747946196), (pn 241661 671032943823840256), (pn 682614 416122603563811088), (pn 9497 797923597389014150), (pn 609480 587257989269127508), (pn 392124 873084881938953480), (pn 611552 806022722820540064), (pn 680071 740996823020004402), (pn 29515 370569075581264520), (pn 500940 88390745014298647), (pn 321276 138526867257608992), (pn 519730 297336150737558341), (pn 646451 269339326619254820), (pn 846124 602202107715019797), (pn 10130 939352824012226952), (pn 434467 252818361164503173), (pn 155989 991506534595920208), (pn 326032 476873159113980678), (pn 912969 322679049041412132), (pn 278796 118653852158288407), (pn 668 336120848016130624), (pn 538811 318111872843523720), (pn 8418 926828268978153660), (pn 170136 739114998893913634), (pn 758421 743696732295995500), (pn 671813 752512192510427731), (pn 249272 447945911006871984), (pn 10686 488168723732243463), (pn 158500 480347603982262426), (pn 151247 273185740270933509), (pn 41950 563880039013613608), (pn 124063 667964838251352592), (pn 622172 508426172546549096), (pn 680556 170824958774137890), (pn 28654 732628411125340290), (pn 906898 198087886096730208), (pn 80337 883891059599739938), (pn 644346 572818752125120616), (pn 105164 929090927691695809), (pn 757092 144684488708030473), (pn 62630 355333825370921219), (pn 151964 962842540467454098), (pn 118156 64348725039372101), (pn 39551 45152852989232164), (pn 634001 930832538799113857), (pn 454898 186900999921549584), (pn 264466 387397740280821897), (pn 309467 337918238685333652), (pn 115792 592758060756767779), (pn 759197 155501323912958156), (pn 124064 219084582879234945), (pn 833075 12825556639070248), (pn 44903 435655426338989702), (pn 910826 652542033281147104), (pn 236298 265523771151758213), (pn 761559 421015007230296104), (pn 179611 462674956110828067), (pn 22446 229550410538092305), (pn 312414 715773909142117414), (pn 319216 739392006123953798), (pn 611256 140299566684772532), (pn 191428 934040752341723196), (pn 4145 340044516034448226), (pn 645011 340817707179638840), (pn 184347 597190735603468318)]) else (proofWord80 [0xb215001, (pn 922347 8941096006945698), (pn 454713 34402371413828153), (pn 58492 354545109232001872), (pn 935887 31149314455905333), (pn 56712 232474488721643010), (pn 302416 751680147102683394), (pn 177247 945438023604311557), (pn 155398 4256777784394560), (pn 47468 237416807632276004), (pn 639320 359418846272898448), (pn 945165 518238391946190883), (pn 328228 983801065625883393), (pn 302416 395609735782670486), (pn 122883 66768987040258885), (pn 684930 239636718532886848), (pn 52126 58295512330179092), (pn 20078 128710060097078417), (pn 10441 731002497260114978), (pn 22452 300340316048983808), (pn 189522 191208206777270338), (pn 42533 582977287327588868), (pn 987015 310946837988540992), (pn 528970 975473220707727910), (pn 628094 349769231231485521), (pn 530326 643975198779678864), (pn 132241 301321292343551111), (pn 461174 371237260759048544), (pn 378015 457970092821711112), (pn 1065490 284682214936544064), (pn 42715 858931719992811558), (pn 15348 341137177586508176), (pn 396992 631421807016038924), (pn 163077 439218035620364720), (pn 491532 312096715659397220), (pn 99248 157856829098826757), (pn 79693 395767751788765396), (pn 243303 422219709864477185), (pn 322311 745488046447083528), (pn 41498 281429728300634243), (pn 302398 304740287178868880), (pn 77979 1428216594568196), (pn 987051 879259196187640512), (pn 377854 121151221000620045), (pn 520 349492365040050912), (pn 718205 858253691131311142), (pn 41648 742188706040386051), (pn 302457 824187472056305784), (pn 103975 131521022059616325), (pn 610666 856002145520059777), (pn 152075 21821929583567380), (pn 619228 376082927347975176), (pn 378093 924173421462300422), (pn 157171 19531474310508740), (pn 191428 938515738871787522), (pn 997315 731961066783083138), (pn 417340 724458341973307500), (pn 99265 444403410087467026), (pn 14980 739197506436104792), (pn 491532 267111132806813731), (pn 32197 85774030393711109), (pn 609779 895802819663560854), (pn 113429 101432807191483653), (pn 79213 348112074498245440), (pn 52237 950303029179762222), (pn 42526 682901619964316033), (pn 417100 231613194145464608), (pn 283355 867982140817297427), (pn 921462 141897931946197200), (pn 1190756 461500087266371752), (pn 181958 782701482701828872), (pn 912601 433583835583743104), (pn 1133423 453861362428594213), (pn 635183 676499168894257377), (pn 331691 797703229956456800), (pn 340287 104028440376258057), (pn 461027 374029097369567840), (pn 670959 33611283710713944), (pn 85071 775690315185884258), (pn 1098617 65961510627226316), (pn 128750 835425178001368085), (pn 20084 697841664445473560), (pn 879117 176297692244181133), (pn 46086 926180744410310665), (pn 765029 427851362002245830), (pn 212681 873263266292091401), (pn 914741 291925114056868928), (pn 1095931 95102671710373421), (pn 42525 528853665626866584), (pn 935887 58461449913712912), (pn 239691 388059139711313670), (pn 157171 19531526150342884), (pn 233974 70460562106550332), (pn 3630 301630850849506849), (pn 341228 952783486880630316), (pn 647577 580987440891038146), (pn 456116 446752438431187552), (pn 529292 734198165957523469), (pn 467969 984732542070427138), (pn 208873 186377023501799574), (pn 160701 225019953074417155), (pn 797087 20875622221677889), (pn 76494 210558264634545696)]))) else (if j<21 then (proofWord80 [0xcc0e4303, (pn 60810 883217364194697744), (pn 95342 359861029058814312), (pn 382740 163209059788486746), (pn 76758 645353566647229826), (pn 47707 970692116288965792), (pn 323607 845759059853264144), (pn 944773 369460661590741320), (pn 229220 579010228812624978), (pn 59048 328484589352936724), (pn 609245 626876016382271569), (pn 222 947620923705971764), (pn 317654 32729394062038340), (pn 316693 986243934703113772), (pn 533631 811684755508885565), (pn 70902 668865898172892016), (pn 703805 697385558034364425), (pn 614869 577907502928011413), (pn 44309 514779959203815941), (pn 68515 858615405304185856), (pn 1191125 667265938984812559), (pn 317396 426184106262597249), (pn 850349 5684644248605748), (pn 308579 567918168657977540), (pn 101569 807096104254538260), (pn 118169 928699970783414722), (pn 152666 632433883245770801), (pn 46343 266377260248007588), (pn 82661 606194300529738848), (pn 330833 254332279820390211), (pn 237031 443673965198857356), (pn 453458 926092019943158563), (pn 683747 322349393907595800), (pn 382220 735433718412548160), (pn 69817 912854076990636964), (pn 233969 361794746874432416), (pn 21889 408404302357385865), (pn 43453 774287080036895362), (pn 328330 195316272364552451), (pn 167207 633914115593021505), (pn 90687 833915257488835808), (pn 380801 79533138931237706), (pn 797500 199110711447916161), (pn 859950 648711230399060484), (pn 756851 960503289531893665), (pn 454542 863311511267877122), (pn 627490 792040757482020865), (pn 39071 249080704668175441), (pn 387533 386868522228189248), (pn 1065268 638873253662173696), (pn 407249 652257759635722508), (pn 609287 28619262273062276), (pn 1024201 638814686305088021), (pn 19278 830487011738016272), (pn 156428 482552913767498766), (pn 686626 582605354300957745), (pn 659388 488188232540594181), (pn 182712 123429263115486085), (pn 1064489 616189635711533585), (pn 621586 478674516569668885), (pn 618695 52603568164051489), (pn 189891 90419102322468512), (pn 434461 349436380592648384), (pn 649995 96094232619278529), (pn 757211 609861539392176544), (pn 418040 985367891465732300), (pn 840807 66752766561022127), (pn 57169 234672208559972460), (pn 623575 395171438044386611), (pn 206912 661902617881953160), (pn 985944 187264122617136675), (pn 316999 280978963811077249), (pn 11894 745793381061035185), (pn 629295 357545729386023968), (pn 318847 960876410206495024), (pn 4901 667206756074825480), (pn 762700 540317392981459201), (pn 1059213 216537372759720016), (pn 10659 942651800574371461), (pn 609777 13429222099912866), (pn 134702 813499829946948357), (pn 913192 269191627411947561), (pn 224404 713769837430588422), (pn 666 264148867411903272), (pn 727613 679593739190824215), (pn 628093 920383965628727456), (pn 1001695 391942661321599016), (pn 23614 719295551033443456), (pn 377821 839272098268251708), (pn 667092 499505817398937041), (pn 454750 333540266168893450), (pn 62605 970870440594382340), (pn 758531 557657122299019530), (pn 181912 647769672698307078), (pn 82056 743203248470393472), (pn 377844 812077724545916993), (pn 647577 583233740999231697), (pn 454906 959922033441783817), (pn 337673 721276870354937477), (pn 610072 161351907722678532), (pn 229207 868115894612790087), (pn 612438 32720091494057633), (pn 454749 495246040932111411)]) else (if j<22 then (proofWord80 [0x5268160, (pn 382512 881387145035579412), (pn 288299 642701505139329985), (pn 922 631370348547280960), (pn 964105 407012811654051944), (pn 103985 503593662927356704), (pn 308443 982608483052815369), (pn 59048 173241845963653381), (pn 362750 646895410993824776), (pn 242183 884926709304394784), (pn 308201 312875816985641776), (pn 519534 972420190431627280), (pn 77182 619517645659182340), (pn 68605 841699936707285059), (pn 152319 482308157438723280), (pn 916511 522305980200505696), (pn 304612 315502163158909021), (pn 103966 444642287429381388), (pn 38683 167081253869749252), (pn 92109 353044516585603333), (pn 31904 949502726847416384), (pn 945660 895866053646614888), (pn 1020926 205976354852442164), (pn 415872 702856529870458209), (pn 618743 90756370886365123), (pn 834986 334605300684841238), (pn 24945 853358179946385666), (pn 96236 392223531708550017), (pn 940402 388189017313321800), (pn 381493 957311837615670128), (pn 701557 586095137921973002), (pn 615423 232789619999539912), (pn 675936 14899185559735563), (pn 189882 81457102504884), (pn 415955 762830316798743841), (pn 946097 781666773137904648), (pn 389154 26681393623399473), (pn 206649 88947964269740656), (pn 475031 460695505631751973), (pn 983543 812005057220624916), (pn 623807 133890093409958960), (pn 25397 865873287724534112), (pn 406259 564027265137837329), (pn 64390 706796635555128004), (pn 49922 695012778579697729), (pn 420035 319595797272802465), (pn 675954 474032639998116616), (pn 718100 670306144098980946), (pn 963815 95133924456467586), (pn 322536 831220876009300616), (pn 683630 771753378496256261), (pn 132689 821534426624431136), (pn 928053 489907248312697704), (pn 794040 464158262940715220), (pn 229136 304981846746288204), (pn 668233 595962585254268947), (pn 159533 788392014752056069), (pn 307878 321461736180826305), (pn 699288 739996215127707696), (pn 453700 68731230949049985), (pn 227042 553363054515512368), (pn 382144 625215433155307540), (pn 158494 498212906363228353), (pn 317361 282654650898645562), (pn 56687 434934129888592136), (pn 232607 126493278122197410), (pn 255137 8778792665156609), (pn 23734 141261590865748624), (pn 381640 103600048507986028), (pn 671812 207453421127602228), (pn 229109 213327811720316240), (pn 909214 949770542809792840), (pn 302306 690775702977925648), (pn 236414 776993252460528390), (pn 951931 839437396166926417), (pn 75576 901567924459931272), (pn 1077590 832874044563526736), (pn 491534 306978982294227212), (pn 108717 111767120743908616), (pn 458099 549871301304861040), (pn 420588 187889002882862092), (pn 278740 161366342799852961), (pn 312566 974269719348183425), (pn 307191 363893116606906628), (pn 32185 537745011945802113), (pn 315273 925063258599228424), (pn 306982 938429207085351940), (pn 90341 217945770451697936), (pn 6552 214490924941591424), (pn 666246 30201526888204812), (pn 677715 550921564835775240), (pn 684953 5664727822584680), (pn 963925 605548373755049164), (pn 671814 859546271231001384), (pn 459864 89742710996914376), (pn 76531 869779261201107472), (pn 266040 331019682151936521), (pn 61653 867004187368497955), (pn 985833 797281883049464066), (pn 984854 319074705854968452), (pn 57318 826444410899935432), (pn 727310 210105508938122112), (pn 916956 576769981810877524)]) else (proofWord80 [0x110811, (pn 241 266841735284163536), (pn 380408 981539804220494977), (pn 18991 13686327438345601), (pn 321420 850461426296357216), (pn 304707 949483959149265984)]))))))

def genIndex8 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (proofWord80 [0x19e000e1, (pn 150525 460714662716768736), (pn 8854 572265431021650212), (pn 1151667 182579570568069600), (pn 5316 216833016647422432), (pn 8854 572265430990251488), (pn 8854 497785086063149536), (pn 65 196403848686600672), (pn 4915 327714565577245152), (pn 7119 608272081142174176), (pn 3045 341078961462579218), (pn 169415 6224939155980768), (pn 8873 451353697085816903), (pn 18299 265045282198389216), (pn 7876 606599148263703008), (pn 8749 368176807260455392), (pn 8854 452853969776137609), (pn 1045429 867926006461097952), (pn 8854 572263944795193412), (pn 613317 456018718046413412), (pn 1085554 130359710110752339), (pn 773877 942490356197755446), (pn 1033212 358741687725057504), (pn 8854 572264748715564512), (pn 8854 572265431021650400), (pn 8854 536386167559593761), (pn 65522 945352540300684930), (pn 405533 356824582145982467), (pn 338415 887319924593394144), (pn 8854 572264655385981969), (pn 880035 639983219486598146), (pn 358309 691997784766926304), (pn 4173 710955713006666208), (pn 7229 34837760408783371), (pn 81659 910083146003183809), (pn 219039 917953278643060192), (pn 5482 515736382377511402), (pn 92678 594947085234078176), (pn 7708 188281049077324009), (pn 429288 402237718610121941), (pn 243293 335748952102328105), (pn 358665 389038536459757402), (pn 271733 873230600388739297), (pn 415072 892578448529334752), (pn 6301 361778257025537600), (pn 877499 645020019088860328), (pn 244972 780760081230108230), (pn 318306 198089780789510389), (pn 163427 624653700075052512), (pn 2192 127119750871897509), (pn 1189446 192982842325074400), (pn 8854 572265187916130599), (pn 364083 955238420082248292), (pn 669742 73453779324726149), (pn 73857 318949693678027744), (pn 8854 493633561768294568), (pn 583837 999773847416075753), (pn 81594 534992792554482297), (pn 430209 833864192336722411), (pn 74967 661000072589746176), (pn 758088 403260209845240704), (pn 38449 941572996976888008), (pn 610960 775418292683743490), (pn 604906 804889484995337728), (pn 872164 679496995503616449), (pn 1014 864784214290695168), (pn 57117 28874669720121584), (pn 453347 186302149910872961), 0x11002000800a0c50, (pn 831164 750662612161740800), (pn 637630 157974700130634880), (pn 114517 479399241108431489), (pn 935065 604589297995186176), (pn 76443 308082008233646240), (pn 304694 98083104036225410), (pn 209187 230717390385456136), (pn 77338 156091399569671236), 0x283160038a080424, (pn 113339 750118538218582560), (pn 2565 254877738200203536), (pn 99464 898370735245380160), (pn 782789 40006828952387715), (pn 153255 560215838289573970), (pn 157609 19927986345108099), (pn 19258 707117378187363380), (pn 156133 530087949062410304), (pn 306954 267288661523432230), (pn 23789 455091741535244304), (pn 180639 891095559407207168), (pn 1476 410703541589640208), (pn 622 613929374347427908), (pn 9445 309514727418759712), (pn 340010 424487560014200835), (pn 930324 935610169146343936), (pn 18917 199874240245155968), (pn 1060383 917971516099314305), (pn 113340 830849322182905864), (pn 4132 106987232656621574), (pn 680021 660831279588509708), (pn 453642 366430199805517890), (pn 21324 581408369476240642), (pn 321120 947858383007387648), (pn 302425 512764580100046859)]) else (if j<2 then (proofWord80 [0x95e41be0, (pn 8854 572264786584181829), (pn 1077444 442805696040929411), (pn 858880 539180345684597216), (pn 8854 559137262186004960), (pn 8854 572265431021650400), (pn 1310 493592022866693157), (pn 551522 762922719881311413), (pn 451591 380478892196905601), (pn 830002 128529545912425285), (pn 1000551 498253233276891616), (pn 1246 290785053976976864), (pn 1861 382762492142870496), (pn 8854 554259828605190624), (pn 5513 850297439130105824), (pn 4232 654068380134801425), (pn 963969 926416366821179512), (pn 358309 632123346264211523), (pn 1208335 618757825365442485), (pn 745543 743593095674986528), (pn 509425 302371416246755296), (pn 35 805499264069222131), (pn 530181 99234286319148198), (pn 552984 15341127389413521), (pn 392393 272814513311470187), (pn 529518 653868068088940512), (pn 8854 547624442711184730), (pn 145339 971712293269421024), (pn 2415 505660180575621088), (pn 9342 313057252316020905), (pn 420338 577935754458745312), (pn 8854 574486170839810528), (pn 8912 938916601743278560), (pn 2807 487633405180379399), (pn 1177239 531750019437156996), (pn 520692 606507502440853684), (pn 2961 252109359497103255), (pn 541454 731767726472710337), (pn 1167505 386207576763949060), (pn 321184 322510847333273568), (pn 5133 373993549376947168), (pn 1034 135601946491579302), (pn 155116 735520134623742762), (pn 112746 605884854117597504), (pn 59037 786594908739469511), (pn 550610 39677727579046353), (pn 324547 864076558845084128), (pn 8854 572264471873717216), (pn 2861 786000580428388832), (pn 6055 589715939522773273), (pn 518870 73454339782470632), (pn 344812 728173728561627409), (pn 981662 30369449532787335), (pn 93857 53411606678629221), (pn 856291 287588297106808385), (pn 270506 394290907853043328), (pn 131636 44890030393524391), (pn 99312 385275807333335809), (pn 237955 271394268034828907), (pn 752782 857558435437740512), (pn 8854 572263533322086264), (pn 641651 680969963464612165), (pn 20710 640558055532528096), (pn 4235 516491042489897764), (pn 1123149 685225066368233440), (pn 1349 774464884964334915), (pn 681705 823043337502564000), (pn 802694 865453733071999739), (pn 177828 171685818565012448), (pn 2807 787202541601281446), (pn 488956 285947560337801184), (pn 6963 836153777088365024), (pn 4156 635488415561810400), (pn 8854 437830343316734432), (pn 4147 914338061628129760), (pn 4247 54191121196643956), (pn 174766 342704390509799904), (pn 7704 552332464870130017), (pn 54464 867561559333798368), (pn 2807 266753797498601633), (pn 1009996 255436535146506208), (pn 7823 835301078623555040), (pn 6671 659511536576794482), (pn 1103109 666110358589276640), (pn 3654 46032813665288579), (pn 828227 671023796843708896), (pn 5423 106354312527216708), (pn 1043754 43033969536008631), (pn 1063608 786079727587688928), (pn 3024 124873181506448352), (pn 9315 176659479025073632), (pn 8854 502595437891944642), (pn 339420 190055533076665312), (pn 1562 161726841757934251), (pn 119394 868896098563391878), (pn 805929 427493847850126562), (pn 688875 294341515730572292), (pn 1057966 448134956437733416), (pn 953327 868838641328456177), (pn 271638 905308970286256099), (pn 1123332 954470527770034439), (pn 885271 128720544295943142), (pn 1119400 905128437785209898)]) else (proofWord80 [0x7161e5e0, (pn 4175 987934553448934368), (pn 2493 455627013874867680), (pn 4201 236957764446955271), (pn 208235 478393319353710548), (pn 783322 666675352962815432), (pn 407146 149895598373162464), (pn 8854 537570913307590657), (pn 972217 334770838645244384), (pn 8854 475611761856100443), (pn 254417 524525223748042889), (pn 915548 804573667247784034), (pn 190748 746627771957578274), (pn 164767 661216446655576439), (pn 247708 662773631695582087), (pn 875539 108277946938939177), (pn 315858 643586562151018401), (pn 424422 706743024664902624), (pn 4556 823335346198751300), (pn 252785 732371967087213287), (pn 380766 242556909231072), (pn 8854 447514841719686624), (pn 3634 959237728933493992), (pn 679854 599716239809970656), (pn 8854 491715589208277256), (pn 86787 493368248653670368), (pn 7225 144598236799533066), (pn 1128696 599432018650541987), (pn 1111048 388125123701525984), (pn 5908 324309531428389344), (pn 7160 508205610953147124), (pn 736099 10626496794048324), (pn 563246 62646962295931306), (pn 352502 717340643113767392), (pn 8854 572265203797801989), (pn 292991 768390259246629057), (pn 975332 240445033033140873), (pn 150525 447321641038848480), (pn 5322 760458614790422789), (pn 119938 38782639083218761), (pn 924993 550482402858500264), (pn 811656 874353270681393122), (pn 207193 964545166636235818), (pn 65522 842202501904756289), (pn 785227 727967514933043720), (pn 1128185 441025311283457504), (pn 8881 233575225054986246), (pn 429773 667845388956710688), (pn 447264 28642396693186503), (pn 302828 165905886975609847), (pn 46633 465938680424198021), (pn 131636 31684567397227488), (pn 8854 572264069697602986), (pn 1067945 992563793368527809), (pn 613317 482072745609689402), (pn 482877 107228672295959745), (pn 928151 811430956443153073), (pn 248402 99947931029837792), (pn 1189 247682000313139895), (pn 1128116 965889082135363680), (pn 1161267 260926634284286192), (pn 1104627 867335750674547109), (pn 244972 780577562319389122), (pn 783322 621843888448471104), (pn 853335 274974101466917188), (pn 846369 837002515070134913), (pn 106979 696525680467612640), (pn 1277 565284468233072096), (pn 4256 316187800638587360), (pn 8854 569238859432548707), (pn 745543 658514160684106115), (pn 1127087 983447983708940065), (pn 1104443 463875839643353397), (pn 946865 323059116369313450), (pn 159546 989319908856227745), (pn 631183 297823321385974535), (pn 394131 971952236033999334), (pn 547204 351312570567834466), (pn 591651 637042985664774624), (pn 8854 572265481319743584), (pn 120579 801173218155299296), (pn 8854 572265431005592544), (pn 8854 572265430997979937), (pn 464986 687719317091602773), (pn 1167474 636052095284074406), (pn 736098 985705825806013920), (pn 45 243163918179762496), (pn 263862 362338891181218784), (pn 5384 278535647739014185), (pn 717216 501321339905245664), (pn 8854 519739706915900384), (pn 6531 912859702603814168), (pn 263862 362339933816182181), (pn 824711 404549807433415815), (pn 219769 627172116352933656), (pn 1000886 710538878268590792), (pn 144838 493197986248890336), (pn 8854 572264073404210656), (pn 8854 572265431021650400), (pn 2396 50111811534796768), (pn 6966 285877602173321433), (pn 764433 209523087232834816), (pn 1187300 750177454004970197)]))) else (if j<5 then (if j<4 then (proofWord80 [0x2951daa6, (pn 1151667 261118538855801832), (pn 877769 890964347556324099), (pn 1180001 460015622747324609), (pn 953327 797995626861668596), (pn 726654 224425463096551035), (pn 273502 802094377505170912), (pn 8854 572265431021650400), (pn 7765 981888606133047264), (pn 8854 440035963637073013), (pn 1005973 723504222517854554), (pn 92865 71177690098400449), (pn 533733 484423387883476968), (pn 304197 322731726469972099), (pn 616350 962665886925421024), (pn 8854 564748644843520196), (pn 880202 93026059680768546), (pn 1006587 265088260593942849), (pn 879113 232797585669169514), (pn 796958 217074739744080006), (pn 1132777 725383594128071206), (pn 308168 440827103748184490), (pn 991106 800700536620996967), (pn 777006 394993064211445163), (pn 92755 536912338377123642), (pn 675329 707370007264601701), (pn 845334 772934066326587813), (pn 773877 827529238986819232), (pn 112746 634887982945946080), (pn 8381 730333354130745312), (pn 2549 244555941059662304), (pn 8854 572265431021650400), (pn 8854 520350889979123940), (pn 424422 762245395837106656), (pn 2680 245262170286933574), (pn 31111 249075426026537641), (pn 117087 96123031843504608), (pn 1285 644043873529906656), (pn 8854 572265431021649989), (pn 750273 604064927088462312), (pn 262791 154147424026493408), (pn 8854 572265431022297051), (pn 528314 885380999821131969), (pn 339420 226064354980040651), (pn 787021 535873207728809898), (pn 773877 942490313546269062), (pn 906104 179869831040860392), (pn 178859 693673299409231946), (pn 1113888 329254873845606293), (pn 1086741 267648025599148512), (pn 311 135684158913206916), (pn 1129056 188373160889511904), (pn 8854 484896038047551787), (pn 329975 382876151549001377), (pn 563848 934959302127386697), (pn 449712 608535298001346016), (pn 4241 434825684269727801), (pn 182503 115155770502545689), (pn 1060856 101772453755237572), (pn 178859 765648738249343456), (pn 8854 572263395941639136), (pn 8854 572265431021650358), (pn 1167780 59721885998852457), (pn 1038330 432465967816999904), (pn 4914 463023067520041208), (pn 56078 237093679758720290), (pn 132296 325730455738670596), (pn 481091 220551330290466851), (pn 7168 328320802974000134), (pn 887214 738079185004656097), (pn 1087967 50952576197987337), (pn 131636 29092301247610935), (pn 169414 934096003612591040), (pn 1139422 263922775604876165), (pn 933127 613871204208449848), (pn 868325 247063448174461058), (pn 906104 82838330159013122), (pn 1108591 231404023352393799), (pn 717209 501087021611908889), (pn 254417 573462287248294203), (pn 486749 471065078746864582), (pn 478777 424501126658776487), (pn 1168364 385288280204116038), (pn 953445 514527729025850336), (pn 1924 902907471539483616), (pn 3663 254958657454997560), (pn 194390 483569013246027876), (pn 1000551 536429651911534560), (pn 8854 572265189669328864), (pn 5526 87880705001774804), (pn 485322 154243926516209755), (pn 277572 302930078576148960), (pn 4869 978466480053499872), (pn 8967 217269265442460817), (pn 429333 278508759584525635), (pn 217678 183656145781384128), (pn 396872 998190534252475462), (pn 564431 917068639113855968), (pn 165954 106440555994493113), (pn 829808 146937727875547396), (pn 919771 503187541641988064), (pn 1062 967471927481272228), (pn 797386 526617895421608166)]) else (proofWord80 [0x1e001e0, (pn 5815 615294475448877536), (pn 8854 491551425905414218), (pn 367754 311049931079254809), (pn 744837 698820379314338272), (pn 4824 473544994928169960), (pn 319994 341223261676776928), (pn 3627 453944854974363463), (pn 974043 141264842078290400), (pn 7113 12828474815021067), (pn 669985 774884618658720736), (pn 8749 380414195181289681), (pn 455804 852984592120236000), (pn 5952 957068711731144672), (pn 4561 380812651273135305), (pn 462201 738535061847802336), (pn 8624 362273452098026186), (pn 331209 562116450968142304), (pn 8854 572265431021649976), (pn 443312 287282063497757152), (pn 3152 510734021708218498), (pn 849435 806216227862030304), (pn 5647 721100367076786372), (pn 953327 806672972629934241), (pn 528110 154904227171373284), (pn 821101 607318220294849018), (pn 133412 896973828997676512), (pn 2966 169794346206896523), (pn 8409 16240665812181014), (pn 651096 342317135827042784), (pn 7194 421030842550714848), (pn 173 229668296302892162), (pn 985697 24783991330870603), (pn 465789 18300870256279109), (pn 867837 19333426097509703), (pn 105085 320233551564108169), (pn 648288 607241243080199754), (pn 980680 614176872196233184), (pn 3652 412807349773800647), (pn 690146 585872712718556837), (pn 493702 444289706520382441), (pn 543247 639735455126177696), (pn 915548 902653474980152490), (pn 48518 928267826878743008), (pn 5907 940098894651720160), (pn 8913 633867969371112928), (pn 5955 839372473256640522), (pn 1208335 623246960853516768), (pn 665 103106409949560835), (pn 1182437 225951397685842453), (pn 1081615 509622503559042872), (pn 207858 99804906771771138), (pn 445188 921091664928392817), (pn 702363 254545091554241433), (pn 726654 284519996840457817), (pn 547204 239826489554687223), (pn 231602 375803577101272293), (pn 603872 689303473331634582), (pn 227988 200918233287058400), (pn 7198 724800418293500647), (pn 728530 574366450514919904), (pn 627 612638744372314592), (pn 8854 572265247848005733), (pn 2281 190305429863793120), (pn 8738 125599173869830407), (pn 349509 874497486132871264), (pn 1170556 693673628512406260), (pn 816416 578625834567434231), (pn 499980 686483874123874784), (pn 7842 497787379799032170), (pn 886702 303579235558048327), (pn 641651 596350069519057891), (pn 169414 945548766895595459), (pn 752207 925472984367995872), (pn 8854 572265431013537457), (pn 141080 786660762442617811), (pn 1103434 69398717326518793), (pn 104008 642804231383810528), (pn 5434 286506798145864177), (pn 834752 197933555049385481), (pn 276946 780293352189329601), (pn 382863 337368635332562628), (pn 232132 953727199502155459), (pn 512502 703211973814895584), (pn 8854 439358664479343072), (pn 5641 706197818058426775), (pn 953327 868839360050427945), (pn 609209 422866822548122999), (pn 200832 236757194830250025), (pn 508291 514994766484225415), (pn 516117 264092727678840266), (pn 839991 55858874171708292), (pn 733886 881727577287397092), (pn 868325 272147478884385121), (pn 82738 72239889104363747), (pn 292196 499208551731823072), (pn 2137 724620504614675815), (pn 40239 546269519980040160), (pn 8854 572265431009813595), (pn 780468 744946759521286148), (pn 197749 146264711559578568), (pn 1054300 7314798735417824), (pn 7221 747182772620351942)])) else (if j<6 then (proofWord80 [0xcbe001e0, (pn 6361 955971650263971296), (pn 8854 537330687908430304), (pn 8854 574793352322505696), (pn 8854 452937225496690742), (pn 518870 152415352704729568), (pn 8854 497793309449125930), (pn 487653 170263308852607456), (pn 7097 87546845934731684), (pn 244494 289867986881430470), (pn 1092748 937009209140188514), (pn 1132777 795187335021723878), (pn 972217 219017157224669664), (pn 8314 686692658749300235), (pn 462201 674393951524293315), (pn 484078 18598330541553412), (pn 35605 954050682449943179), (pn 103301 840699817443628512), (pn 8854 572263670848610312), (pn 216638 582859020913484768), (pn 4601 271444151686136259), (pn 325735 994833520492651488), (pn 8854 572264720875651495), (pn 857150 24181789644445738), (pn 38514 312306065207264163), (pn 917533 737387575096904160), (pn 8854 534670929444733408), (pn 136 468076914354045920), (pn 8854 572265404178680550), (pn 694362 848232494954709472), (pn 8854 476044969450257329), (pn 586187 422469429204248032), (pn 8854 484201779891421158), (pn 1142222 529297684577531328), (pn 926085 918952569080350539), (pn 811656 821904367018045920), (pn 2442 22856854647865824), (pn 8854 492824416647613697), (pn 799976 66600030622015494), (pn 1174608 432437300423778784), (pn 5351 935605986959071330), (pn 581500 354814966919552480), (pn 8296 406007781649285251), (pn 576839 478012587517411808), (pn 8854 572265183356387776), (pn 688875 345797432324312976), (pn 1038330 465529778541792224), (pn 8865 208525302731375072), (pn 5442 792124270036714659), (pn 811656 874353270693718819), (pn 634130 806102816649642184), (pn 125305 274437549838093888), (pn 971627 666166197461713376), (pn 6707 832423322048586394), (pn 1007249 863493147932647751), (pn 753976 211476088757486569), (pn 1024894 967151781587625586), (pn 4791 858291619959669216), (pn 8854 572264495505567210), (pn 329975 493100566887833056), (pn 1381 128389002874847651), (pn 116605 352256069620022752), (pn 8854 519497157480112096), (pn 6046 881191450969637344), (pn 4017 57747288741014650), (pn 303417 714028433035493735), (pn 405426 855702493144345706), (pn 906104 90035774008898528), (pn 579828 590125792429605035), (pn 400811 37960484361192416), (pn 4818 194077554871687494), (pn 911724 535758552714733018), (pn 247359 626689514752592581), (pn 321914 410054332134348790), (pn 792767 413464152452104672), (pn 8854 511405228202394080), (pn 3693 951495622671531861), (pn 1119936 507300226028250129), (pn 1071999 865218891541119216), (pn 641651 672724204144457696), (pn 5995 903393826219611299), (pn 479501 488026004043611753), (pn 1104443 470746752028508640), (pn 8854 471763786403120410), (pn 882212 68272389427822592), (pn 953389 559881529552798147), (pn 981662 67734672498068800), (pn 285857 476058775051144966), (pn 1028885 679745913877824856), (pn 848379 874232397848002722), (pn 106415 630787685835763616), (pn 1019596 465282964238279136), (pn 8420 148269359617288672), (pn 8305 338373315567882816), (pn 695841 892919989580040341), (pn 112243 905855498258588266), (pn 858880 539180607394338272), (pn 8854 572265067383540192), (pn 6871 918503419093288416), (pn 464 762476016045712857), (pn 1104443 579208835342659552), (pn 5362 81488070730842592), (pn 3037 650927112421376480)]) else (proofWord80 [0x1e0, (pn 4731 411936626275234552), (pn 1008083 976318514505451684), (pn 877769 917763843979879465), (pn 292196 428454977725838760), (pn 1019010 735368734948086944), (pn 6931 328912608492311989), (pn 418353 698241819737963608), (pn 831239 527169357332651488), (pn 2450 27084859089879275), (pn 839991 30670801282007520), (pn 8854 438874846177788384), (pn 8854 572264021094920672), (pn 1192 220892032722670148), (pn 1021333 808478080424312070), (pn 585950 9443423355638752), (pn 5691 243886941256749552), (pn 320530 734628790013886944), (pn 8888 8704056419867129), (pn 818183 87841886765194809), (pn 1203207 464061829650579776), (pn 226083 430476898854475776), (pn 273307 95304503071813035), (pn 528216 428554147982213410)]))))

def genData9 (j : Nat) : Nat := if 11 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then (proofWord80 [0x4442ff3a, (pn 58881 561333294698694142), (pn 547871 754268791835255819), (pn 1194290 661029470336399722), (pn 113222 246743242151689842), (pn 397563 332660044333648892), (pn 1076854 42571504833063959), (pn 1179545 974901202317373904), (pn 226444 34119321323830499), (pn 228442 684288302586664953), (pn 936259 869756362354427951), (pn 1150094 937284736601350824), (pn 452887 530058486568712645), (pn 154653 909310085732511731), (pn 645220 962765633887543391), (pn 1091171 244773432729649986), (pn 905773 871166668365886340), (pn 639873 462850897403535335), (pn 24995 281969376856720063), (pn 972984 324367200189382791), (pn 602618 536011783211046765), (pn 70812 107895093386592174), (pn 956389 710375801932907903), (pn 441911 64292208095487170), (pn 1202933 228608287716388531), (pn 103845 195966299223981917), (pn 477180 9536469499183870), (pn 882018 959347903957479685), (pn 1196926 514313498785176916), (pn 56574 621978048241794746), (pn 774910 92123559129978365), (pn 551782 461769294276277003), (pn 1184893 305914324024212042), (pn 113149 32568388579622260), (pn 662015 284341725051554810), (pn 1098418 281933193134875671), (pn 1160836 364689571699323928), (pn 226297 766210351305325287), (pn 762068 953985000082774005), (pn 974297 47099520922651695), (pn 1112638 535142921461229200), (pn 452594 631700775089731019), (pn 381325 208138021915078635), (pn 701299 46839628547297375), (pn 1016051 491079328772769872), (pn 905186 381097783436241806), (pn 913766 129935598592581591), (pn 137151 450119427760529599), (pn 822634 136514619811531941), (pn 601444 924968302219876121), (pn 14143 520386522987675566), (pn 231506 453904286477239679), (pn 435749 851760108657643786), (pn 1202885 94135388776148506), (pn 141623 783444621738475356), (pn 180556 362034062322911998), (pn 870252 242449973554057621), (pn 1196826 246171214653381636), (pn 207689 592825070766718522), (pn 179891 626189590025078268), (pn 539902 756311743216768267), (pn 1175327 408086390138615850), (pn 415305 475585593032829728), (pn 643401 213563144907206558), (pn 512846 935626514028906079), (pn 249569 673723434947654348), (pn 294734 178040037510176389), (pn 158087 748081943321386429), (pn 350984 888012344117251259), (pn 506075 308453049197839665), (pn 519279 993205647901977024), (pn 466320 864659491521621963), (pn 608142 917037315252562271), (pn 713096 865176366456882274), (pn 901052 184718548445148040), (pn 611502 379156003315801943), (pn 119294 713524820033953982), (pn 822321 116073735119145057), (pn 591997 669953796839499561), (pn 675136 514034394179288526), (pn 316507 969886783771017595), (pn 739108 855453152433354954), (pn 1165122 158987966184009298), (pn 141328 727933053908908892), (pn 624456 506406528698335983), (pn 271763 736987758435918485), (pn 1050487 900902726630333638), (pn 206509 440021711152672441), (pn 642674 604979338571095486), (pn 548249 768409588437943595), (pn 589854 843751680672971276), (pn 561773 713042744732401012), (pn 97655 595059870773152508), (pn 1113027 531309630271187029), (pn 1179818 59873140869068056), (pn 207556 461353355449138410), (pn 114958 330289260805772789), (pn 1017092 340508253884875819), (pn 1112869 398667453502515745), (pn 1019280 681230596622906836), (pn 154063 658261944988608499), (pn 832930 419123182493245903), (pn 1017098 307778793467926560)]) else (proofWord80 [0x2550207, (pn 7969 95616444497395850), (pn 1438 846319122996264770), (pn 360080 17077178396250110), (pn 475197 347074727118251551), (pn 1179725 848670525418533200), (pn 302001 52998078770969798), (pn 757937 894301338132029433), (pn 62589 786925711630814271), (pn 1140649 952099817469264544), (pn 603877 569081355546916313), (pn 321115 68838417730912235), (pn 765650 513594657567836287), (pn 1015992 475909287857997104), (pn 1207413 916180861228673834), (pn 481669 371014492327542742), (pn 324883 962655449107350271), (pn 814498 113556114563603105), (pn 1205842 56325236919359028), (pn 623328 282078876118613932), (pn 342518 955174766991524351), (pn 401808 130831573428028611), (pn 1202611 7313356798274154), (pn 113287 458725228744015696), (pn 1086439 44663284866810878), (pn 763918 868342710592891671), (pn 1196001 11077557824475349), (pn 75456 884155618813017761), (pn 765612 875988856201578493), (pn 309540 971063892811731983), (pn 1183000 686181793931369030), (pn 150909 440351986629737778), (pn 378968 294058353137881082), (pn 468113 788347071675804703), (pn 1155897 266969055762133320), (pn 301807 936956860445227561), (pn 40136 677947474266431476), (pn 80593 797951372527751231), (pn 1020962 864640641193086096), (pn 602993 278285675008879633), (pn 231384 466875675540996048), (pn 95074 411029005643587711), (pn 681879 570247322570069552), (pn 1204806 505380389874288682), (pn 462759 728675170576531344), (pn 341264 513766915937734911), (pn 153191 560654140100055585), (pn 1198389 346525586565058868), (pn 321020 121866120904900068), (pn 647110 567128062806868475), (pn 946282 220537303980771531), (pn 1167460 304069659608337033), (pn 717471 432600342050765708), (pn 779483 51969987444524023), (pn 119278 932978835262950023), (pn 1124851 342591981128486033), (pn 74899 12291166521259706), (pn 936794 106729948200409069), (pn 536223 750005043612099375), (pn 1033619 24451488152203846), (pn 451974 139253751088147796), (pn 362430 793137571727880154), (pn 479919 632515343314405919), (pn 853756 892301482106106500), (pn 299456 571558233530948196), (pn 757918 141513335700594612), (pn 945672 165150038342126783), (pn 496775 572379520198134425), (pn 598896 950423976685843598), (pn 155794 600711486989418345), (pn 38995 826318847375087741), (pn 1148803 552606081881790787), (pn 1188390 673038865118194090), (pn 481520 923363298451684819), (pn 173618 423246098129305847), (pn 1097544 937135362122856069), (pn 1130152 750399611589088357), (pn 56052 965176794841020328), (pn 576271 475950936141234655), (pn 1008613 706204619289736515), (pn 905092 532832702502522025), (pn 715408 927941615463554905), (pn 548070 837862802113479614), (pn 843608 658708685761710727), (pn 591832 959819679038133397), (pn 66016 983534696380202673), (pn 812762 789922557697623551), (pn 558732 277115978384249611), (pn 1203844 921555894283516584), (pn 113296 817346011076099956), (pn 399925 97006569658452990), (pn 1098252 270243179264584279), (pn 1198546 121332513417687880), (pn 226592 463756115864977124), (pn 764432 436314048962107389), (pn 949504 641000238746783983), (pn 1187868 969301655043367568), (pn 453181 543057107438795223), (pn 154653 949261940313567219), (pn 804010 536031264222851167), (pn 1092282 661105952494309984), (pn 905782 513574370192913314), (pn 942104 985836314814865383)])) else (if j<3 then (proofWord80 [0xdc50dbde, (pn 1035708 215049694748006766), (pn 1024861 361491189646087952), (pn 1013848 482169432920937677), (pn 1002835 612980891323257437), (pn 991324 676635771332775962), (pn 979979 745787472707636614), (pn 968302 786212375886089027), (pn 957787 976580704278858011), (pn 947273 174548741075158762), (pn 937588 486133425894638768), (pn 926409 591181709986677393), (pn 916558 882069538142535713), (pn 905213 953754475655445964), (pn 894699 151722667071748938), (pn 882026 40101026062972984), (pn 867526 680549464277759306), (pn 853359 375058453638263550), (pn 842678 544729925368590532), (pn 833159 882077977777188589), (pn 823807 247722401974693061), (pn 814288 572403771184228904), (pn 801781 481479064154974199), (pn 791266 679447178263045592), (pn 781748 11728294534947679), (pn 769240 936003661451600174), (pn 759224 193528490927759137), (pn 748875 396993310435286157), (pn 737198 450084394288650727), (pn 724691 359159880530565019), (pn 714176 569794639180043734), (pn 704657 894475815113691979), (pn 692150 808617657663459520), (pn 681303 962659208859782727), (pn 669460 964654138563005291), (pn 656455 814172561543891159), (pn 643782 705084156674934339), (pn 631607 663152600779948867), (pn 617274 319231539357581505), (pn 605597 367256266906631779), (pn 594584 493001253038750716), (pn 582907 525826099912472963), (pn 571396 579347687482750721), (pn 558557 449562889811948626), (pn 546548 440994525880807870), (pn 533377 247016619082149629), (pn 521700 307708145792609583), (pn 514007 890452573598411599), (pn 504323 202037335732021651), (pn 497294 887834924647213042), (pn 489270 434252613918352905), (pn 480415 864520534999458929), (pn 472557 431634964966564524), (pn 464200 923992760237908163), (pn 455014 302733984796073636), (pn 444665 531532248005827843), (pn 437969 258723086382947161), (pn 429612 756147547200969054), (pn 419429 990442361190176620), (pn 411405 544460029451916693), (pn 401720 828178189058790127), (pn 389379 773149871463157824), (pn 377038 725721532859895284), (pn 365693 794873040957688582), (pn 351858 523174798268909664), (pn 339849 522206838537799242), (pn 329666 771701571852321844), (pn 319650 21625997125501245), (pn 306810 901974878449254273), (pn 297624 273116046702099765), (pn 287109 476150671735077591), (pn 275266 478145756063610974), (pn 264419 629653877853074989), (pn 253738 809458719330284540), (pn 243722 66983548805853661), (pn 233373 288181678400286654), (pn 223522 579069815801458151), (pn 215000 55797574575860698), (pn 205315 369915534187506170), (pn 196128 743590247822534664), (pn 187606 217784654497129997), (pn 177755 511205989375747036), (pn 166908 647514385114014177), (pn 158054 92982225523974235), (pn 150859 753016485507112616), (pn 143665 413050900109663450), (pn 134644 820088883016768385), (pn 128612 637666353931295263), (pn 121916 374990291469998188), (pn 114057 939571717234366164), (pn 106697 576376116353504653), (pn 100333 344960242847847386), (pn 92142 870681384701268564), (pn 84948 530715760650883296), (pn 78418 288736632164388734), (pn 71389 964400967296814557), (pn 64195 626968656693300329), (pn 57167 307699618719468241), (pn 49972 975333973661452682), (pn 43608 733784885024786247), (pn 33093 939353055438767553), (pn 25733 576157377246135274), (pn 17377 78648580922606243)]) else (if j<4 then (proofWord80 [0x8883c160, (pn 681055 62027034703957318), (pn 164420 483348149645292830), (pn 66235 561503726767310408), (pn 416159 629140702208836064), (pn 908319 698619143656506497), (pn 304596 205418966582298627), (pn 302490 791876477076902400), (pn 531714 146799673078226980), (pn 5329 118485900804882640), (pn 18944 905401393253593148), (pn 113539 962327392986480912), (pn 491717 420243661688701312), (pn 756761 13115964542818314), (pn 626933 406319619839639680), (pn 70974 64383889448633473), (pn 151928 467028886730049536), (pn 606531 542600161304781699), (pn 5911 42646568429426697), (pn 11824 392242241376149552), (pn 66210 120440217235358176), (pn 908246 634195621065562176), (pn 3550 435308455029933579), (pn 18924 116741549760985106), (pn 28380 387923876867276896), (pn 189153 346095025771069568), (pn 226687 561590352959177344), (pn 604537 129640172925487620), (pn 7685 376171659915450405), (pn 66205 508824726487802000), (pn 283785 432533577033450177), (pn 190963 581465558377303815), (pn 15373 664500491152275738), (pn 42556 728791001594966144), (pn 227043 31343428911907232), (pn 681054 945814013618504577), (pn 304596 389644134159751689), (pn 16551 377201783050892336), (pn 85094 974773518131122376), (pn 416233 54982740931707488), (pn 908172 413581135937930498), (pn 3653 249088094164495360), (pn 265486 839437123490350786), (pn 609192 205093629875719172), (pn 610375 104794566047313170), (pn 33105 64750174934462576), (pn 245978 776123666522604129), (pn 77478 634899020579882115), (pn 6060 924139849849602057), (pn 70892 71584889682919936), (pn 85279 730973343086592352), (pn 605571 735729592351687810), (pn 154957 269797482255488008), (pn 14190 189456677185548320), (pn 56733 51541063632728138), (pn 113521 551697654885568832), (pn 548681 398076841694987906), (pn 988311 132685391249285645), (pn 18922 954786342202001944), (pn 47297 559899143420348576), (pn 274340 699003176295432768), (pn 756761 12569608930854145), (pn 57074 803682268459565168), (pn 719130 324591270720184833), (pn 607122 127767887383632904), (pn 14183 262885265924981790), (pn 66233 251165966063243013), (pn 609667 55478839426701865), (pn 87520 582949996345967024), (pn 870577 516202305922295852), (pn 42232 713867643092025953), (pn 77368 604223136000378755), (pn 913790 902847430996008975), (pn 33116 618809956959799352), (pn 87511 570410854538240256), (pn 454104 834183652280926993), (pn 304966 190350893247897096), (pn 14480 725667074218703902), (pn 66233 251174572672717200), (pn 888359 311740913175365217), (pn 834537 194407443099070498), (pn 628115 166664100407870786), (pn 458371 907571688276888581), (pn 612738 589799822214576154), (pn 51947 44063486557569048), (pn 914674 905406690272837636), (pn 14187 874588925910612024), (pn 75668 670467205463336034), (pn 208116 599689944020468232), (pn 1059621 49253370733856290), (pn 912012 800632117607800975), (pn 28975 286392203720552484), (pn 56760 775847753734553792), (pn 378306 692190051542139136), (pn 453375 123180705918354689), (pn 164 761639313924943116), (pn 1117170 282424973594061540), (pn 1106987 521786375816996980), (pn 1095310 559678081516234325), (pn 1085459 842966123957969956), (pn 1075111 64164176239452623), (pn 1064098 187375694305877855), (pn 1052255 194437289557548235)]) else (proofWord80 [0x785828, (pn 56751 498355703646662896), (pn 378241 949393128674299904), (pn 836307 942237937169637444), (pn 132300 73499866308445442), (pn 458519 343051805193986128), (pn 17842 820670461888956804), (pn 158357 526930361260449307), (pn 47297 560072011962418498), (pn 154657 936986120044168222), (pn 668325 718251709408806144), (pn 284524 312935872114227252), (pn 118266 949521059594109312), (pn 794761 976140382480663610), (pn 99243 498949615181644288), (pn 945951 201351860885393414), (pn 11235 248250633547038928), (pn 302287 83859489761266691), (pn 610370 480305013088343078), (pn 80393 347314431073452136), (pn 1002398 237372167397600305), (pn 68575 924392530670674192), (pn 605349 797212551475896321), (pn 462808 83281323558506560), (pn 75581 134045349440980482), (pn 1062243 373721394986114575), (pn 33116 625582776352002180), (pn 283877 630225493087233040), (pn 624546 806104802848727124), (pn 170263 916879626546382433), (pn 834536 329716314643933256), (pn 85090 279625895709049280), (pn 945728 540039127494955528), (pn 15965 688567241291956250), (pn 156013 671798465933086213), (pn 311686 574867245329056830), (pn 123012 518478703256412464), (pn 681277 99940933934261257), (pn 466941 301245855723069744), (pn 623979 853373796135340163), (pn 459258 800904280572205086), (pn 63839 713888542013555776), (pn 604667 14281911629259790), (pn 21278 359862684558635136), (pn 236469 173203065519653825), (pn 909502 888541326208419856), (pn 6527 904706399285314561), (pn 605644 78082814551394050), (pn 760306 196958361150830618), (pn 53165 840282806890070112), (pn 189227 295781672680997441), (pn 77479 210796822389859590), (pn 918518 754727858167488576), (pn 23750 435478367944475649), (pn 152296 682952351368228885), (pn 42565 979237498822381976), (pn 510828 752811140261622806), (pn 21254 119212120142831696), (pn 151374 306172237890601665), (pn 152593 776480220709523976), (pn 924432 111660602748841024), (pn 89891 290583014305434114), (pn 302638 726433972512892944), (pn 30697 994247366015822024), (pn 378343 587051523395290306), (pn 155033 653103374849065032), (pn 14210 991680338906317697), (pn 303559 801123152621734404), (pn 7674 424674384698695720), (pn 56760 712590621203832944), (pn 151337 412675234202895201), (pn 645272 449546984448068633), (pn 636386 218758501009146689), (pn 456007 549188271398590602), (pn 319380 49921969852817978), (pn 115873 448449008879092160), (pn 728575 93729019766002708), (pn 3263 939105154958188680), (pn 189116 65755343755626756), (pn 160279 747711414629833267), (pn 70937 125762937192908354), (pn 152887 50610334037460001), (pn 63867 370432074583429344), (pn 454123 317133063624346658), (pn 70937 35415711811551568), (pn 766445 573919127110703140), (pn 61399 456295075417784864), (pn 907284 948840184005264897), (pn 909648 149888075442685955), (pn 223 743338319214299164), (pn 47297 560044270357940400), (pn 340379 898988622290158161), (pn 1478 48887790468203521), (pn 606935 287787080550715398), (pn 267852 355157903538164800), (pn 94595 132224900652220576), (pn 302748 101371716339202), (pn 305187 553523459421118476), (pn 23644 168261881988941876), (pn 94558 190415383940350032), (pn 151344 48768841693856321), (pn 37 64942177596999426), (pn 606973 255298940408048658)])))) else (if j<8 then (if j<6 then (proofWord80 [0x20c05021, (pn 40158 566372992603996260), (pn 151281 910330941193265424), (pn 151148 279962929293951552), (pn 604611 214188914356525579), (pn 21280 627958348524339280), (pn 132466 465826778000851248), (pn 529644 70738652294809988), (pn 689627 510015593285686294), (pn 330609 518949344340885632), (pn 179787 165777328983774212), (pn 605279 183657851162744868), (pn 56751 419463442410816041), (pn 20737 172115185664542723), (pn 625305 474399726314341025), (pn 228890 953663837141606410), (pn 627226 824838109817307424), (pn 52241 612240469110819588), (pn 612737 428999222790733852), (pn 47265 174660412906446912), (pn 122789 641869707079516480), (pn 340048 541421227999625792), (pn 67055 717152226358338574), (pn 30746 191861853739659448), (pn 250738 162864734021882243), (pn 155106 933422787466944616), (pn 5967 618702655357846481), (pn 759200 840239118047526938), (pn 664788 582017887774787106), (pn 1064019 167842993927463989), (pn 123012 509929623237725061), (pn 8869 449924269009586262), (pn 105202 2534090155884640), (pn 1191994 524153011260120102), (pn 66214 750228762824450865), (pn 228151 351770673665034268), (pn 3869 264347893760295521), (pn 96664 692849925465067524), (pn 19516 725167961162711905), (pn 644607 65771970731843599), (pn 626935 723448068041343873), (pn 303532 672170450276593685), (pn 44936 408404273587849540), (pn 314 785855620219159578), (pn 37843 585615658173448344), (pn 321712 82746476115182626), (pn 4580 279059245670924408), (pn 227042 843717197900940610), (pn 458076 477928234807296007), (pn 39033 450238976121717761), (pn 909946 186579809757314076), (pn 56756 130343216992683137), (pn 604722 607843539440127008), (pn 57943 695911300425580664), (pn 756872 219417146256566348), (pn 160786 802979720646885649), (pn 456526 86172514554319044), (pn 245941 883023442434331170), (pn 1064167 322769856959578496), (pn 850912 890421076500153412), (pn 1069047 79956310166491408), (pn 529718 1830102091305352), (pn 622204 113298266184262176), (pn 832466 684454399720038928), (pn 36667 641844773376051139), (pn 460590 144344398493728790), (pn 70964 768782528348291584), (pn 85925 835672723100674062), (pn 635209 59644730033365096), (pn 227089 382531873913602688), (pn 1097510 83570803834646562), (pn 922067 452757352992899328), (pn 528951 397384282094863874), (pn 609192 520897953240471594), (pn 89877 401455289618467840), (pn 285040 821911224299053098), (pn 89877 410444150241919200), (pn 340453 830327942211372290), (pn 3547 547364169364807180), (pn 26016 881934571678368449), (pn 152886 868494267994087436), (pn 325876 780685260029509772), (pn 283785 504943840420830477), (pn 21259 876518092515467472), (pn 406622 229157125003156488), (pn 1065646 237336791689675104), (pn 794872 295260222527137836), (pn 85131 746534900953023233), (pn 456451 721602130735321176), (pn 94465 895971552819611330), (pn 1064314 317435370637205648), (pn 113376 49060139785060864), (pn 939954 133034975756096647), (pn 316399 276619602315976716), (pn 1044 560418188291008608), (pn 151189 537170654359110465), (pn 342670 182598077861862157), (pn 23940 469176671513494177), (pn 77624 134482867982182419), (pn 33114 312949217869824056), (pn 434845 819964222455161098), (pn 624560 640872594586816672), (pn 359361 761229345748427276)]) else (if j<7 then (proofWord80 [0xa0b04819, (pn 770657 731447766686798120), (pn 643350 519918483404523042), (pn 609932 958290642025078816), (pn 56765 414641607250577988), (pn 765630 984649602839909442), (pn 151402 103207845763092487), (pn 317604 530386957812953200), (pn 231617 697561504719831249), (pn 720386 146598843557914698), (pn 137188 832627226040861697), (pn 380598 274667505766150184), (pn 7142 416393944569356944), (pn 1097510 81172074721976592), (pn 36647 974497442148467232), (pn 1059120 821207928377715468), (pn 628118 627640736965750988), (pn 378232 834601405728958739), (pn 35475 489422118989529344), (pn 454049 421364831903293966), (pn 23615 596327464486406292), (pn 189208 758789505031604420), (pn 8870 605124304084652464), (pn 946025 565917013946141197), (pn 328838 638300101049876960), (pn 908320 275926900894869009), (pn 26021 526289292483510944), (pn 755708 720464572378388745), (pn 318785 142456459566622840), (pn 179750 173192019081562627), (pn 893 525444345251086488), (pn 312248 939135966455794689), (pn 6652 83785344628093032), (pn 189227 169417164120589826), (pn 912311 700608663435677744), (pn 16609 108977618382521537), (pn 304891 536423692246465560), (pn 49672 623517604491756866), (pn 304891 245948255632655424), (pn 146670 567379093504270093), (pn 331794 753842970632683608), (pn 501402 322228409931945001), (pn 67409 204017305283332355), (pn 302934 596852161426514464), (pn 66205 454564697454043392), (pn 463549 567290403404645124), (pn 8570 261171775549350032), (pn 75583 367874968596481731), (pn 81619 79479339721432094), (pn 37835 497197594170376380), (pn 132448 28495478849077600), (pn 548681 290485509546574406), (pn 457634 45145256101478500), (pn 787492 720588704929235712), (pn 42750 798196914488413445), (pn 615102 71007373007540765), (pn 61473 810664439339405512), (pn 425789 81819126481040147), (pn 498070 174539222073057284), (pn 664735 457516903258031265), (pn 986095 502420987345647127), (pn 53183 208537568594559020), (pn 113540 43462955450818816), (pn 529736 628789387205149264), (pn 908172 413457818920978243), (pn 4724 672821247105704974), (pn 29563 289905478529762380), (pn 118253 159551536785068496), (pn 926987 587592071032735266), (pn 306370 743176238517462545), (pn 334162 843332366284376188), (pn 179745 525195728590209169), (pn 2068 632861700944046088), (pn 2969 371048344761344264), (pn 548569 995937222812108963), (pn 460586 677116900657338387), (pn 37834 346532296013660288), (pn 264678 748156524515885456), (pn 567644 941259400030982726), (pn 306666 181006683690502153), (pn 623388 170436734315757586), (pn 231573 805267982449445122), (pn 304962 763668470337118726), (pn 1189 247554070424616996), (pn 56678 848483262038688448), (pn 1096770 913986021821976454), (pn 619246 264949233091628066), (pn 680145 433426276403945800), (pn 548496 715028887708633088), (pn 760454 63800257353936996), (pn 151281 917165617342202528), (pn 1135215 81380528617167113), (pn 14774 132906791158187058), (pn 92224 740631486680663169), (pn 209667 876126333097501741), (pn 40167 791472413832800544), (pn 624497 878271241416082246), (pn 160866 723799307420536976), (pn 170178 266919624187348289), (pn 1061504 344272399236676121), (pn 42577 512982472533770624), (pn 123058 662836334339687536), (pn 832245 182295856141010114)]) else (proofWord80 [0x48b84d, (pn 141920 404520683908172292), (pn 310502 515755464650155049), (pn 85141 172822208766116689), (pn 456523 628952156198959152), (pn 94528 93921335673295216), (pn 681055 379005003506653836), (pn 25426 607564737068237905), (pn 1061654 88974661465412368), (pn 642313 408521707524195201), (pn 456006 977230295570596897), (pn 75701 15372686705952130), (pn 305778 421647494030571026), (pn 34292 596470753985253720), (pn 719055 816336174576062493), (pn 56760 721603365875845264), (pn 264840 518001596844116356), (pn 308440 533396942586204296), (pn 227042 589378374456707139), (pn 4284 261384267178189840), (pn 632829 437864903692013672), (pn 134813 814362784086887568), (pn 756484 115521851708408322), (pn 608749 482389232630685700), (pn 628114 6960726308356608), (pn 983728 167989449172727322), (pn 33708 76571035631027714), (pn 609192 810043674964538648), (pn 656496 689430217580138920), (pn 964767 240031793219655716), (pn 47297 577921257931039264), (pn 794429 392624461704876064), (pn 66195 593969592889921728), (pn 378380 623335120031323785), (pn 625154 450694226582053505), (pn 191037 946030160599332115), (pn 40188 628051308302500481), (pn 1921 344181867439003787), (pn 24833 992374164757307500), (pn 217639 803534333615544832), (pn 381555 630662598678581304), (pn 118253 159621927213908673), (pn 380598 274526767739873320), (pn 7732 757240333853926081), (pn 304301 243432065945704263), (pn 14487 656724570238407784), (pn 241302 689475681744132748), (pn 329426 625998030617290960), (pn 482605 306752753660472340), (pn 33116 616456190971552088), (pn 756465 686229846643980314), (pn 2078 741722616842887560), (pn 491883 766046609990755267), (pn 461032 717572364285624520), (pn 397306 982781134310348426), (pn 22471 653959442761418001), (pn 985872 985470541580211482), (pn 655316 124866385619944962), (pn 608602 198072175479503901), (pn 66763 489020822414229548), (pn 302785 904034611415756820), (pn 42577 521998233570762976), (pn 397417 772908309647731217), (pn 33060 618652797708148980), (pn 510902 467555158571624449), (pn 1071411 728733105247625920), (pn 927210 103698941508847625), (pn 929164 834726079734522400), (pn 1134993 867386118506029841), (pn 327660 346877489501995713), (pn 153182 34519605670591768), (pn 655318 430727030019754308), (pn 311098 585457275075968284), (pn 57950 635923072394416540), (pn 463613 896284512392330266), (pn 1787 58225159248928992), (pn 463604 942705345203473926), (pn 770068 591374757634789856), (pn 984063 328233612819635213), (pn 629891 832235540347815681), (pn 1099433 20844232927089175), (pn 50857 844856451520925190), (pn 158210 826693723776098862), (pn 89886 678993925506272261), (pn 10644 371472624291710016), (pn 146568 911819924904088072), (pn 319374 267277807916757128), (pn 302804 386807481877677339), (pn 56744 621403018780418424), (pn 416122 663453948530407962), (pn 1786 192406527764168884), (pn 387769 943971005612622721), (pn 607788 661922876506912794), (pn 655316 124822284626822561), (pn 985354 164240365620575260), (pn 36068 106890983026786356), (pn 501401 925276568251411989), (pn 44931 774164952070389952), (pn 420808 10136360623538499), (pn 231844 743630699416858712), (pn 170263 474962880925369425), (pn 1061654 89538713077943571), (pn 41383 83955065702613953)]))) else (if j<9 then (proofWord80 [0x50100122, (pn 99027 608715813949859928), (pn 160745 72031123836865027), (pn 6575 125158380634734598), (pn 667152 35143817829942818), (pn 1063424 253575778764089904), (pn 101706 430258948272951623), (pn 619838 899310964770884688), (pn 151392 933861824802591368), (pn 617470 197247756601458808), (pn 264803 588502281269812747), (pn 9446 905971835372945600), (pn 397380 987541806511563780), (pn 2374 463269392087237056), (pn 794835 76878895236007960), (pn 5049 844687583165531073), (pn 910242 203126072332093604), (pn 350083 391443982693435267), (pn 6504 220483642919592112), (pn 340453 172027224292330245), (pn 313461 221701793972518926), (pn 125378 322819146577222156), (pn 26021 530806125005980577), (pn 758830 459119805242563624), (pn 80418 824406720886214662), (pn 163233 538238996098354220), (pn 99354 384583180996706816), (pn 209483 752510172454494284), (pn 151342 33685532790751488), (pn 1135436 300520039643621384), (pn 2968 798811912900071584), (pn 321564 75136137696184708), (pn 83540 996235495882102830), (pn 80418 824318535962100994), (pn 154660 962000581782686756), (pn 80430 353630270183244801), (pn 605018 620651504445448748), (pn 66205 454564699555381520), (pn 510920 913805411699655428), (pn 5762 455943728005693520), (pn 11879 788901627792524161), (pn 380301 540218438135453703), (pn 12414 679054198150060118), (pn 134781 469263900853223936), (pn 728168 74575656855282689), (pn 312652 881577786078208104), (pn 10687 646631945927459745), (pn 758830 459517620275918486), (pn 637562 205468433651925812), (pn 189153 247421090902893056), (pn 908098 338680003101226026), (pn 80400 314220137740001664), (pn 719019 283135445172487688), (pn 11828 425800708612333840), (pn 491864 92499204037805314), (pn 3842 688012577816719634), (pn 637558 733153417925198248), (pn 813502 424360305873402389), (pn 40200 157111237201904136), (pn 1154326 921278485088475202), (pn 137142 625518852514858338), (pn 154737 641638746913841272), (pn 236506 319174747833369505), (pn 607197 68793799331809818), (pn 644646 914885043962332033), (pn 77479 210792027459168781), (pn 327066 591174500756510972), (pn 369046 67275864134391305), (pn 14983 521013320780927050), (pn 151374 378819772303918274), (pn 380966 271532797041610802), (pn 941566 867148140280365632), (pn 1097363 87064567019606536), (pn 620421 680838913988570190), (pn 179699 345214402093778561), (pn 190076 622425976095127574), (pn 42556 719656117061390480), (pn 208116 635049532572509121), (pn 910612 148787218007285904), (pn 243324 319312015824455427), (pn 385033 721201908827439328), (pn 343198 665896984353213253), (pn 312873 526173784301678678), (pn 160786 672075731581603077), (pn 615104 395292224493001785), (pn 94618 250781519096581328), (pn 983730 61297140365283360), (pn 66193 288122183459111072), (pn 302692 745331749847729730), (pn 685342 96834616958655523), (pn 676580 645161421730384194), (pn 760604 223018845992661524), (pn 44938 669131931978971376), (pn 510791 822343736204472853), (pn 40204 686619112181375040), (pn 132234 410905011403408145), (pn 190372 852742828916614663), (pn 15966 860664250229293078), (pn 217579 977998943793846538), (pn 22469 334565965994236090), (pn 378491 557815872385470749), (pn 59124 282993147905115904), (pn 378749 992517282225463310)]) else (if j<10 then (proofWord80 [0x5c240e86, (pn 617470 201786272719410256), (pn 132452 649118224441675264), (pn 494893 181096302033806412), (pn 113530 793139607125066120), (pn 870430 808279640234291203), (pn 23065 432201217029055169), (pn 229186 389517369004140049), (pn 940078 415068790365110945), (pn 77624 135123882084472457), (pn 622199 501596869605304526), (pn 210404 5050450350575879), (pn 893 92528393495299162), (pn 179708 559667544891556721), (pn 20959 38433210122924056), (pn 6554 444416815009768161), (pn 190963 870258886092797201), (pn 23059 75347343601009184), (pn 756464 321321019504662281), (pn 616289 607901363441863356), (pn 321481 254898642951347465), (pn 10639 163890308909937746), (pn 175032 454475786807247969), (pn 645418 868461505888708712), (pn 208116 671676463900116257), (pn 645198 662287015626727430), (pn 650594 818879888072147841), (pn 380302 115977321713046665), (pn 321735 466339266217455702), (pn 125313 650952093699280388), (pn 456747 158588161163043914), (pn 160791 423619954522244673), (pn 834977 537943503449940072), (pn 208116 630665607628096417), (pn 683346 526776893009562903), (pn 53481 819688819640255265), (pn 380302 111508117998147594), (pn 323514 442266200271511693), (pn 250511 720977166749535749), (pn 818 295904527703955554), (pn 174958 505054165635663529), (pn 795353 426704861098977348), (pn 132387 790102008615551697), (pn 190742 364933878353372947), (pn 44344 360653870821016481), (pn 607566 870619293509504035), (pn 671288 654319976541095234), (pn 155248 342148818666795028), (pn 647028 884532400543027624), (pn 723482 854275438569861141), (pn 40204 768796134576705800), (pn 463475 346981593065456390), (pn 766806 674670608835510448), (pn 340490 722803732167493699), (pn 81616 769118411442624542), (pn 64448 510609384096466178), (pn 306071 837354426333938200), (pn 651753 556831753415475608), (pn 510865 753364780579824134), (pn 1636 587442058249185384), (pn 189227 169504790261597778), (pn 1063575 578191258500276296), (pn 113369 194682709350679169), (pn 2066 198382012068270726), (pn 11824 394479222769397814), (pn 118267 21719838880565760), (pn 495042 307247471078182972), (pn 118253 159587373891748705), (pn 266891 29295806934968360), (pn 56683 489442656510329360), (pn 794613 822905787465732998), (pn 162345 783048788963765309), (pn 57936 737735303322206976), (pn 200232 166894232323498509), (pn 14170 7685517323374752), (pn 359509 353055319818144643), (pn 535552 946301967014088752), (pn 13064 994464539924169377), (pn 77626 496514086635319574), (pn 45538 206355131904590400), (pn 906953 845622784415511058), (pn 637565 673226883699892552), (pn 567534 116186570687262736), (pn 14170 571748137776500824), (pn 170226 574732511024907041), (pn 190816 296305736663438857), (pn 623380 668541435711127574), (pn 141920 422552846906495621), (pn 10051 178687947799036474), (pn 115873 448448870903276080), (pn 1135142 19775365986174044), (pn 198616 525818131871269537), (pn 305039 402136929006817328), (pn 8301 88968887297909697), (pn 759200 836852594316684810), (pn 628118 608496053438480960), (pn 906805 622482037035507724), (pn 326476 317917358852173964), (pn 283840 809076895786476814), (pn 635209 101662532560597144), (pn 302684 139745937980391777), (pn 1061062 204517608448886840), (pn 37791 686136372060668176)]) else (proofWord80 [0x330b442188a44a1d, (pn 59121 968125123261522528), (pn 1021620 538105388788111396), (pn 61483 13872569073066512), (pn 927098 556990574741685900), (pn 919999 682965693983310144), (pn 680980 869145731973811846), (pn 161758 374054604734365722), (pn 125345 991283442705828484), (pn 309912 219670231258784298), (pn 87497 753402450961859376), (pn 1021250 413708873355499521), (pn 309327 709595924080726184), (pn 321637 479657912590010756), (pn 158506 547673133765106211), (pn 63872 49883735458514562), (pn 912014 521912558797992214), (pn 654133 204902252943114344), (pn 1003025 174889723212608021), (pn 40204 685520206253220200), (pn 775354 882297810853578780), (pn 4452 52037451173265736), (pn 700166 422461738386328325), (pn 84131 296561585413300448), (pn 26208 410091790508361282), (pn 152886 976580245927893002), (pn 18921 750435689926832244), (pn 236534 43157927367803297), (pn 1061284 431831150664665172), (pn 160800 484320938650518914), (pn 79252 985606190737154054), (pn 636385 55688482535932609), (pn 152886 813992367572979334), (pn 615092 847364046188501096), (pn 134813 832377251450326225), (pn 1099357 209770361778387020), (pn 104058 335550112558056097), (pn 341857 730970196503430663), (pn 618065 120575535794332064), (pn 680463 604375966622684682), (pn 316715 635959783403566196), (pn 141920 386488693212645892), (pn 310502 515623536146567253), (pn 127670 186373091037939921), (pn 720754 649698530256529468), (pn 118216 67511595422892705), (pn 304670 33354620643848195), (pn 328825 953894149768135072), (pn 832466 540268671101574795), (pn 169152 86735927024059329), (pn 755717 691748072832702603), (pn 325886 22107000314724924), (pn 482383 637976830896121874), (pn 644653 834645863007986008), (pn 775964 491161233290447905), (pn 68594 226340724801120452)])))))

def genIndex9 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then (proofWord80 [0x9548355a, (pn 723559 82146663330978025), (pn 235214 434883485683894954), (pn 910507 851102767299146169), (pn 17690 429261716618217468), (pn 834909 980621188510695791), (pn 129 937607405215032937), (pn 45493 61427587763878797), (pn 323463 778648216687155234), (pn 157888 775699718893255265), (pn 232895 336299542895869942), (pn 353755 653519613920068737), (pn 337 337345013834454470), (pn 313894 422073648488579087), (pn 67 776405817352469807), (pn 788721 270650243342336000), (pn 680625 71398488287692373), (pn 758439 206726786988412907), (pn 649602 96828191737905560), (pn 246730 371060941426000607), (pn 104 219834850710140591), (pn 276 703492749066830271), (pn 276 705383294719307295), (pn 40382 253986192390098373), (pn 57240 250725547997404973), (pn 914637 253787662213859398), (pn 209282 21982910236146317), (pn 206844 408432328744813552), (pn 100959 835919720384216991), 0x5f000125bf000f, (pn 253 899473227769649343), (pn 133 432368349181837317), (pn 164674 86468221943565327), (pn 60 203838387243485722), (pn 895391 962543893612499301), (pn 97061 889636027057702815), (pn 282 134522925777092608), (pn 304279 47718028129650479), (pn 38 428127580583297039), (pn 276 705383294718455419), (pn 112575 939526251266972594), (pn 291587 685865149922878637), (pn 801330 358814982479478799), (pn 276 705383294718744079), (pn 232 218826112033893615), (pn 325496 525566399989350415), (pn 115 571656477437263879), (pn 745150 984386120527052815), (pn 276 705311757743702775), (pn 41195 537064263265746948), (pn 49347 63984952633171711), (pn 204 114010583805657101), (pn 241117 395472295259996175), (pn 189 305909463156195342), (pn 114498 944687661877829102), (pn 4427 538051853284162533), (pn 354031 375651076338529315), (pn 284841 102807847227036951), (pn 287274 410288187744127430), (pn 281703 645190904576754329), (pn 182108 21943291494206186), (pn 236287 181617578868055450), (pn 197140 354490361947757631), (pn 259 497018429483712527), (pn 178 99069392423110285), (pn 16670 826190015088673275), (pn 16509 837683898709264240), (pn 457667 540652001272546049), (pn 75903 213331456674366504), (pn 531861 146389516718800899), (pn 642242 710935510343286832), (pn 569644 700775262066840042), (pn 302268 653530058947822082), (pn 94751 719582901846420224), (pn 327125 337720253612867712), (pn 20365 210032458266969152), (pn 609775 573525681940767040), (pn 28859 197052038733111312), (pn 76766 126026835121152037), (pn 906863 134988391499925506), (pn 321141 673500847168047105), (pn 613927 98887012574315265), (pn 375 861629638432001040), (pn 832317 416887110178234368), (pn 605463 666084373409890344), (pn 93269 47257453147725856), (pn 56 493153797214830594), (pn 37932 307024162730543121), (pn 37825 52105479995736449), (pn 29000 596606656259293360), (pn 154662 150033435161322055), (pn 642429 824205710969608752), (pn 417671 251409718736322785), (pn 914276 559759767425712902), (pn 132526 147214012585345024), (pn 918546 470975155791478784), (pn 122932 570386940662122498), (pn 530095 113277985705214083), (pn 184 476500858937870336), (pn 37818 276719975510052865), (pn 913777 916704880979083546), (pn 586754 152591256126245168), (pn 2416 595540047971747457)]) else (if j<2 then (proofWord80 [0x1ecb11cf, (pn 281 236004507649067922), (pn 24478 832949264137273020), (pn 113209 376969606302728207), (pn 276 704323284625369455), (pn 225 475437207296554020), (pn 267149 520062829823301359), (pn 87 718376664494702602), (pn 51337 292138553087764975), (pn 19 286443809926217737), (pn 813114 34578131966164997), (pn 15583 737955185165076783), (pn 276 705415919300444170), (pn 60858 118764366100043066), (pn 302752 773652419483798367), (pn 276 705383294719374623), (pn 276 705383294719172601), (pn 10902 29150477819317002), (pn 246056 660354118719519519), (pn 151 712479236678680579), (pn 806605 30228231481917453), (pn 69341 314113000241187439), (pn 226 846031820100665359), (pn 241 585213038617624591), (pn 149 160961103627223055), (pn 92946 949136482574276128), (pn 285979 877596908254855177), (pn 336028 437406353077382974), (pn 270452 118570829930539684), (pn 351115 639214711752294415), (pn 250 991140477376869994), (pn 954489 878917042106466316), (pn 928706 320097883950988268), (pn 233686 2636048743401288), (pn 218745 667076730610846290), (pn 326253 901083602874714859), (pn 66574 880044959151357965), (pn 107315 819314267290873639), (pn 119811 603623505138747967), (pn 204 845947640394818655), (pn 276 702073980300754959), (pn 259 857417088726157133), (pn 321152 606503605109719051), (pn 739031 910659516137406471), (pn 131582 979248227185786880), (pn 297790 130640974940930048), (pn 161427 460260255088394303), (pn 276 703172812568723471), (pn 29 893985163514150927), (pn 276 705383246244615375), (pn 113 148155619115933343), (pn 55 776831285090193256), (pn 789119 375923528273079760), (pn 149916 693068715161223183), (pn 58 784402637941065853), (pn 350026 971494732209979599), (pn 19 704405257842067332), (pn 894577 834956031863488527), (pn 276 705383261512073223), (pn 612730 901875011669344475), (pn 789965 200896122696957966), (pn 219276 448946382310484739), (pn 306935 378864598328222433), (pn 88887 559074749229545915), (pn 219866 746836725028290565), (pn 228800 458048406869394063), (pn 276 705383294719426569), (pn 322283 69935343041577762), (pn 196699 976206138445929350), (pn 261482 600074669877821455), (pn 276 701505042329508163), (pn 253808 755932358796576973), (pn 205109 350779666337116783), (pn 231 326271910622199823), (pn 142 795426627991110893), (pn 33282 595721642673897485), (pn 681001 212551738690449334), (pn 264245 447248423085342727), (pn 724940 410021950947738394), (pn 950062 663125665401516362), (pn 27301 479050785697383512), (pn 142467 682154323849969679), (pn 276 705383294719426574), (pn 205299 146776834660564992), (pn 44301 562475823787738479), (pn 189 628284498604791779), (pn 179136 332022427105034243), (pn 810333 663096821961868708), (pn 100036 697333915973918677), (pn 340343 624779423291748767), (pn 57 578239825380573199), (pn 280 407342188417974287), (pn 276 705383294719426570), (pn 305459 639338735155216399), (pn 262 312515748757577647), (pn 189 313053351898386079), (pn 133 149798877364959307), (pn 74379 831564273167505635), (pn 301032 420841327279744743), (pn 257869 520040151900697583), (pn 115384 388403242321263765), (pn 296827 997250301382175967), (pn 276 701648116280049773)]) else (proofWord80 [0x13fd0, (pn 194484 26991275205918730), (pn 138558 480128063805784079), (pn 180 121185686131769359), (pn 276 705383245864173583), (pn 88 47408146037021445), (pn 259697 685932786379063311), (pn 243 522861176452157119), (pn 166 864057449914121674), (pn 339696 794867785435007407), 0x4bf000f000f000f, (pn 276 705383291209850495), (pn 276 705383239440287519), (pn 240 454688375293559127), (pn 70985 393970774744694799), (pn 276 704741241337648255), (pn 276 701929289523466566), (pn 240233 294366772874379279), (pn 122 581151549866807485), (pn 158475 980626154481451021), (pn 280962 363208858047550934), (pn 77310 306558334500536335), (pn 276 703709356984647775), (pn 276 705383294718846415), (pn 249381 537354660209164303), 0xa4b24611b7850fdf, 0x3c1211a92d28410f, (pn 150 604593728344924649), (pn 865922 623980988405841935), (pn 134 3829154437596495), (pn 276 705111527323009039), (pn 131 504827678758731791), (pn 276 701372873789981775), (pn 244 848333034779118240), (pn 14484 413789719047897103), (pn 276 705383259027344783), (pn 150 302501401619529742), (pn 169742 581246891465310223), (pn 276 702783088340122305), (pn 18966 861746885423742218), (pn 181792 665142609365504991), (pn 75 722587800216666943), (pn 96 137222844715040769), (pn 350617 268743607954636811), (pn 235344 11987780741962255), (pn 259 879935066358878073), (pn 889967 276259922656896796), (pn 285588 154501259954421775), (pn 276 701459343878194879), 0x110f0004387f000e, (pn 193008 284532804511793155), (pn 911822 987172326977279286), (pn 113341 149645979652128774), (pn 326078 172275160476139550), (pn 6609 198286471618833544), (pn 9336 738386029327613957), (pn 353213 791265412644738390), (pn 121804 745949191201730045), (pn 784801 708276221513498631), (pn 617692 539676049477608415), (pn 276 704033314375153693), (pn 307804 498514566172520447), (pn 262 371332398512013315), (pn 93213 339487077860649583), (pn 178 369499767131712367), (pn 124 526545630123801103), (pn 51 421819134765105167), (pn 261 267043772691054607), (pn 132 63020006555713548), (pn 28061 9709837713357023), (pn 276 702086804472266767), (pn 276 705383294719235119), (pn 276 704019922322008751), (pn 85427 997423845224653907), (pn 283952 568713827766479023), (pn 97 375191518245879987), (pn 691808 244448166569508877), (pn 96199 773462525247824399), (pn 276 701211357802856452), (pn 811933 441710373040226318), (pn 711160 742046027067295158), (pn 251447 572690865058164996), (pn 209632 327394856137968710), (pn 880075 924400332307628043), (pn 801308 120040058288799759), (pn 276 703620047583510540), (pn 354623 56905141792417535), (pn 276 705383286840692433), (pn 88525 929031877128562440), (pn 681221 365387296220971474), (pn 82327 818846663039518168), (pn 18875 774707200823328776), (pn 866240 658368416007008692), (pn 275944 846855904025491359), (pn 197 495594005053918175), (pn 267 964533444265973832), (pn 57830 546893236670926529), (pn 722941 107072157995115783), (pn 115846 831523735392852494), (pn 317976 791029631786189286), (pn 238751 317355392075235343), (pn 73 967972190991487839), (pn 276 705383261185966091)]))) else (if j<4 then (proofWord80 [0x1ddc021f, (pn 276 704315918853974400), (pn 278512 509759958381690881), (pn 189987 594589922412146092), (pn 346250 50352473091159287), (pn 818759 896523869317774718), (pn 107710 540357733063117156), (pn 299542 886709462083502084), (pn 156114 797665152156704639), (pn 276 701238525571301386), (pn 719649 13726163535806264), (pn 634035 224285872458963423), (pn 19 621902165902032902), (pn 274469 109294886406782991), (pn 89359 921175407332633887), (pn 55 907404346923064111), (pn 276 705383263325595336), (pn 814589 772144984004959506), (pn 789266 547153634794078217), (pn 957280 433123738713077148), (pn 155298 529496712480751629), (pn 888967 47878292981492991), (pn 922023 609095868729343442), (pn 229849 804073131362353697), (pn 223703 669604064808474817), (pn 801012 972334496917041783), (pn 799316 825398339015939170), (pn 217303 829718504167048735), (pn 180 525947377330490188), (pn 885425 269945667367225815), (pn 253443 712867879911105672), (pn 179747 629546694765455521), (pn 128713 936541141423491957), (pn 57899 69161598962565135), (pn 276 705383294718971046), (pn 224293 962601676266209295), (pn 276 704323637152251919), (pn 151 361198465743487328), (pn 886841 46583238103935556), (pn 151618 353281320201299450), (pn 136658 449285394683854848), (pn 218154 24807734413467200), (pn 862537 87997108470038933), (pn 910708 600682326526342320), (pn 49680 184781359410856841), (pn 750542 679253323730583554), (pn 712277 893983419354818475), (pn 65524 453451566305556096), (pn 308099 424292047475393213), (pn 67824 739462804338049039), (pn 276 705383281838007579), (pn 692954 104881976701812740), (pn 258333 382866364403744783), (pn 276 705383294719269375), (pn 355248 714686231108059143), (pn 145658 332695918700535439), (pn 241 716917789677330154), (pn 24655 509278809648442178), (pn 37465 341435894098774096), (pn 962528 523897290752659929), (pn 819959 818429165251870303), (pn 80246 619574201966013245), (pn 713264 403572334621079468), (pn 649237 575424008887664645), (pn 99119 161183556027877231), (pn 278 695974330016473567), (pn 39 717876435319193610), (pn 163493 493899450429379862), (pn 77605 456540246764750591), (pn 132 98106755175103831), (pn 239276 54265975373050527), (pn 276 702031021205225855), (pn 188 679090369049067523), (pn 11308 524872117881814655), (pn 242 338414483009905775), (pn 276 705383273698623503), (pn 948901 172395754380001293), (pn 150802 133703827227025350), (pn 701929 415852562133790097), (pn 919999 373029637475991567), (pn 262 455994034062737820), (pn 59272 45279825172466127), (pn 216 442444073160314736), (pn 9602 989184396513588618), (pn 214475 951593555107653335), (pn 698923 682428172497463263), (pn 74 376727513062936568), (pn 732119 659309999802220550), (pn 186515 30219723404753867), (pn 258826 270320407794876431), (pn 276 703993512021400106), (pn 359766 853891746461319183), (pn 121 757797178726613002), (pn 324349 103772964163092491), (pn 776810 843910123780243470), (pn 61209 658830929154473987), (pn 357428 301814905764260038), (pn 295556 210247350877093903), (pn 276 702854239949357071), (pn 276 705266609047928847), (pn 40 874388807463403532), (pn 125714 565084462137624495), (pn 134 328515676427264287)]) else (if j<5 then (proofWord80 [0x458e38ad, (pn 835984 215874898290557667), (pn 755174 123871957765014040), (pn 39531 372709930532713709), (pn 296014 906372994631207910), (pn 147577 636252713850578977), (pn 287715 889152417068941327), (pn 66 4492443974565903), (pn 276 705582038153037615), (pn 214 904459897430196195), (pn 720054 951938741123350543), (pn 196 722887194745700362), (pn 329956 914231961058981340), (pn 177646 681724436223180339), (pn 21 480514291874271162), (pn 156889 941745120906922498), (pn 205869 824907243734508361), (pn 109686 797539838020618161), (pn 625837 65414939232776553), (pn 744026 359917686507651431), (pn 925676 191886630137561101), (pn 786093 683083619631824911), (pn 93 688812884221427727), 0x1761b61748df473c, (pn 770096 625384108935431615), (pn 203 862501757691018501), (pn 328776 320389675467341839), (pn 95 101457435473877023), (pn 278633 441583740330287295), (pn 85 264689040034967217), (pn 739700 133578536895916353), (pn 240824 364796273447053314), (pn 52316 515149863077216271), (pn 130 342392404822213999), (pn 75 790252322771782177), (pn 39029 193888499443367951), (pn 278 813067876349328215), (pn 121188 849687990991299151), (pn 38 258120792973062845), (pn 900527 822205315382909009), (pn 137046 64230462872551437), (pn 883419 996241665788411906), (pn 206289 940740112430268763), (pn 162978 221889566704336908), (pn 279313 226090109473853495), (pn 48573 62906666310060278), (pn 319335 396078283858575373), (pn 131914 440633006170309788), (pn 177219 833233962823516169), (pn 129720 413370274296348794), (pn 128370 896231087859518031), (pn 132 486612395759837079), (pn 222523 77983347396740774), (pn 271759 937413820661188927), (pn 166 476404844858900482), (pn 731505 932419926783951711), (pn 278 806655980831819299), (pn 10492 132361500405727247), (pn 148 681556651114963023), (pn 276 705383276497272842), (pn 909685 618089536792704725), (pn 262368 41590361769134309), (pn 261116 787580089547030532), (pn 919574 940608022315024783), (pn 276 701805997563299327), (pn 95 723728669208227583), (pn 213 320670658337636367), (pn 276 703187248311223743), (pn 240 909436992247234568), (pn 179726 630325378670134487), (pn 827618 221120693846162617), (pn 210111 25977287086715030), (pn 290501 464601190468326607), (pn 124 586743908689785583), (pn 276 702026637243140722), (pn 924868 154337008176401599), (pn 74 863055179201584577), (pn 25881 227510367059378186), (pn 204265 566158729868840703), (pn 276 705383261045260559), (pn 276 704855921250349061), (pn 282515 172835124469235727), (pn 276 705383258849422495), (pn 233 696006854396881704), (pn 232152 551459838435471410), (pn 331249 565663309284179981), (pn 759397 116978954909846409), (pn 182087 814454758177964047), (pn 226 604747734887057794), (pn 23788 274159138795359082), (pn 16890 973910821393972444), (pn 229054 469975210236592143), (pn 195 850308061438674062), (pn 295185 675350427008415004), (pn 117463 464397655874014557), (pn 346598 463689274370036600), (pn 675543 387414841959526980), (pn 91535 824274430044864514), (pn 236842 812753134040457010), (pn 198932 912386763700772980), (pn 42734 70068666799606253), (pn 33628 417484112687663008), (pn 632696 841619573044939145)]) else (proofWord80 [0xccc5f000e, (pn 813899 130755873390578389), (pn 917301 553020318610554895), (pn 276 705383259490418703), (pn 78 312728465874288655), (pn 158 783130651650246415), (pn 276 702066053495062541), (pn 87570 471292248798134991), (pn 276 704030757978308623), (pn 276 704012478597496847), 0x2c13025f000f0006, (pn 71162 579614415226997503), (pn 86 253518948110630927), (pn 276 702869890963275791), (pn 276 705383287072161796), (pn 355044 487432946631770124), (pn 254103 903324066219082783), (pn 244 846691940909662815), (pn 143 360469615079762067)]))))

def genData10 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x2f0f0e0d0c0, (pn 833208 310583148438324035), (pn 12987 93612636080508684), (pn 47390 262035368306550820), (pn 132670 429047494534066528), (pn 985211 805048918965126595), (pn 11838 306104576389744903), (pn 23685 836166405169357844), (pn 75779 261266345361219792), (pn 908766 173665001272967874), (pn 308152 916082735044497165), (pn 56871 817792170392060024), (pn 454976 570134597182173228), (pn 4465 409438023456686192), (pn 378426 309878548923696131), (pn 11847 565509808309732869), (pn 18946 861072094815597608), (pn 132670 426977727517118785), (pn 231409 837878221841385476), (pn 926824 536804953920932648), (pn 151670 865369688743150595), (pn 897 12478335634915376), (pn 132595 773076441000960449), (pn 610980 460941142884615043), (pn 619866 139901943062477112), (pn 251190 398588029732454956), (pn 1061735 518605906090393747), (pn 696612 665823770376819234), (pn 85038 405041678874341456), (pn 176167 183348294977324935), (pn 17764 395322485368565019), (pn 123040 506088580314301232), (pn 1004400 743484786988554260), (pn 41086 894102474446127264), (pn 530676 134425708976095809), (pn 912615 823754824089146382), (pn 56834 779908268512826560), (pn 815060 776120284178822192), (pn 132595 773163988258455744), (pn 302526 747771482994180294), (pn 71057 652781295003516988), (pn 265414 924391126519566464), (pn 530383 236907190611771970), (pn 148 585298799609714764), (pn 341268 523643990066704705), (pn 3553 335707957454848449), (pn 3551 433967370183573528), (pn 568754 638508302564098690), (pn 8291 910840217116869251), (pn 619852 232504542809820681), (pn 23685 842269604758042955), (pn 600752 473508039898561288), (pn 219789 725319997225072934), (pn 124112 209970088737512777), (pn 798533 713823503511361810), (pn 70408 703764770046124296), (pn 1173545 471240687820473128), (pn 136961 886670849289585663), (pn 382508 298392533448523570), (pn 1207971 196685729568547583), (pn 718978 364965258789126032), (pn 906179 6770905410930751), (pn 1062826 854446838410919893), (pn 226475 576139665664627727), (pn 1156020 355229932722393073), (pn 679954 120003931020980547), (pn 1191290 664937017234738172), (pn 231378 105322488011156786)])

def genIndex10 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (proofWord80 [0x98d315, (pn 303340 335233109534957571), (pn 906751 130054179992380424), (pn 61095 689971027104222976), (pn 53573 975697365950719714), (pn 835727 483674533142724728), (pn 4427 360104960445386496), (pn 141675 318073675238596609), (pn 660384 217005116537991672), (pn 4427 353686544768734898), (pn 368813 896150970975772675), (pn 502037 367748037414293876), (pn 226378 461508288433034944), (pn 426284 963751509418107622), (pn 986522 650872328695121344), (pn 959252 90047220925137848), (pn 1199481 663127657189082012), (pn 984309 44623296041128497), (pn 275978 658832744522450980), (pn 879867 898957619276419995), (pn 657091 673940778111993265), (pn 388290 345192397392733487), (pn 1199484 616720970588410282), (pn 4161 603041964532188024), (pn 74 112567528256451333), (pn 715400 99441696919773184), (pn 942998 542560809258319992), (pn 4427 353689694362854794), (pn 757879 580468133487697922), (pn 364793 587638170249127288), (pn 4148 455678076156660244), (pn 814634 177643072385959878), (pn 666722 244249544825246129), (pn 283046 859723237841295295), (pn 595021 684433201491772158), (pn 54002 847498038213639121), (pn 968427 863888120402168073), (pn 1049261 799708931144540163), (pn 906832 716480629368946793), (pn 675003 323354808587300608), (pn 141674 221880032586907863), (pn 906713 653346831971682257), (pn 635236 681864689223704320), (pn 142834 322182324547739649), (pn 366345 533213649128914977), (pn 693939 121164211812568832), (pn 19486 405949868393547847), (pn 906832 717297843497351928), (pn 4427 353689802384895744), (pn 141675 317968781067804675), (pn 330760 802423923149635704), (pn 929 725538989228363520), (pn 47873 624442683243069483), (pn 906796 381714409418653816), (pn 4427 353689802407939840), (pn 141671 46972379928510743), (pn 906713 919059114266769512), (pn 673272 284590159408666392), (pn 11031 155877159581120690), (pn 911643 130290209739125840), (pn 1007396 196038863841398528), (pn 141675 318073677054074883), (pn 941494 467491031075790992), (pn 186250 280725705890561792), (pn 141675 317977090763875973), (pn 376615 324500962524858661), (pn 56373 373102225060849932), (pn 1199483 990197505696703344), (pn 964543 382066091428470017), (pn 684448 101535753772560128), (pn 57226 123704234726737758), (pn 963501 113714341511430264), (pn 606 250000879913537280), (pn 34725 780240870689223830), (pn 328047 673246075219345418), (pn 185228 356391030571233024), (pn 141671 287070534565486592), (pn 54151 615799926953082912), (pn 791654 746162586293889603), (pn 66241 969870260192789015), (pn 906765 254381259137482801), (pn 769450 703831465369538304), (pn 143793 530647817542375307), (pn 906832 718980610474639362), (pn 90329 229155049354266167), (pn 492952 53783309618045384), (pn 19221 622750565375713912), (pn 2402 102948532255733292), (pn 756166 962410964046504696), (pn 684301 981757666398189796), (pn 640180 796992905401184370), (pn 5331 110382339867299108), (pn 164140 871678859220615312), (pn 917626 691270976844333440), (pn 27 670116677768451656), (pn 79286 421379293414232064), (pn 396977 392651382221194583), (pn 39637 519086185427175736), (pn 530104 674417811470352384), (pn 1116 46061718402498827), (pn 37825 123210119300022828), (pn 1133367 983063506624842848), (pn 147 575923880898068492)]) else (if j<2 then (proofWord80 [0xd0423f00, (pn 299870 347632191945406464), (pn 1133372 1176743605895198), (pn 1106 823831931301397440), (pn 14442 575663601600362496), (pn 1133380 85138074735935491), (pn 390231 398049246303232302), (pn 172886 207213176807770307), (pn 390441 479725420904137246), (pn 424 425222678562235328), (pn 35417 860716733669843155), (pn 1133402 543961870170164028), (pn 537095 434228155319374444), (pn 602479 812794782594529280), (pn 619586 934386986188734494), (pn 1150 987494371226551232), (pn 36061 6796485053311328), (pn 1133402 544589416892745088), (pn 160281 739392045006932421), (pn 447979 844837041038020668), (pn 1133377 731022691131474788), (pn 590200 583393252084278208), (pn 14197 225115033000730733), (pn 1133402 544589384568471582), (pn 1106 817411267581742016), (pn 35418 829518419263488009), (pn 1133374 293204175889633604), (pn 194372 655506809923044168), (pn 57277 68324260475336704), (pn 435553 247362326186623006), (pn 349282 935860441007522050), (pn 110976 693228427119949824), (pn 536500 548052490049601459), (pn 622098 15745245606049607), (pn 942112 742844778670526636), (pn 605198 473732817886321173), (pn 397785 622983033923568576), (pn 35418 829518419263518720), (pn 1133402 544244002705578936), (pn 143958 393355505628379857), (pn 536166 376925241427366137), (pn 532444 515250567062852945), (pn 593763 805538223524938688), (pn 28871 388293756524691949), (pn 1133379 834782648902221936), (pn 87153 585679631919350720), (pn 35418 829498819659364352), (pn 1139288 350733811943812502), (pn 305415 916455865715362666), (pn 642788 157340396114824526), (pn 988521 39915659726734228), (pn 631542 763885282719094720), (pn 15779 260815951074802039), (pn 11488 219834223891854200), (pn 83748 251872267696603072), (pn 27755 162359192671516906), (pn 304122 444259229633019922), (pn 288214 383253410879318698), (pn 747804 415528971582601216), (pn 13270 752320596211836440), (pn 516887 616345559623837446), (pn 880932 242173782065686760), (pn 765537 573999908781752324), (pn 275463 497618793198257088), (pn 9737 407583283981361451), (pn 1133402 544099000390189086), (pn 340 35827954426853258), (pn 220037 454232672426598911), (pn 304994 215046324820282110), (pn 1106 835620894974410889), (pn 715439 187836566353147904), (pn 685474 299345242082314684), (pn 247854 735417704460583872), (pn 2666 471698346247741552), (pn 539323 274204316787736578), (pn 350561 945839291860048139), (pn 450987 80010948042299435), (pn 388454 225014284673286154), (pn 93724 616786354689644655), (pn 1017972 634065191693765850), (pn 1001068 48844774883730219), (pn 122501 22275203811861317), (pn 1096046 678551055667591168), (pn 1133377 380735093080851950), (pn 344967 781887540021467528), (pn 449232 333474561423374336), (pn 1133368 471480535653693082), (pn 559798 77870553507745856), (pn 595234 796584351565903872), (pn 1133386 493392042448462233), (pn 138256 291267641277133760), (pn 35418 479222809757225144), (pn 1133402 544036018485726406), (pn 234870 354414938643427407), (pn 564322 814187966371047912), (pn 1133395 668770224952246302), (pn 889 841699517523559360), (pn 33636 412859399811627008), (pn 1133381 949811251714211010), (pn 394374 658972576907417536), (pn 14801 430261478245626226), (pn 915522 735742762615940446), (pn 158 522393757198286784)]) else (proofWord80 [(pn 129 176282206911362048), (pn 326244 615650525206117910), (pn 283350 635957992338574015), (pn 604519 571348243252845808), (pn 8854 466366656007379334), (pn 1086911 14228835772584319), (pn 604739 619412910519353344)])))

def genData11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f

def genIndex11 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x7, (pn 608892 290468483891521340), (pn 904347 425699576267342304), (pn 283480 407139721750283661), (pn 458448 247708735756072969), (pn 720229 776867835284537398), (pn 224900 414795086166655936), (pn 566961 435987309611729411), (pn 908771 857385531962463614), (pn 15144 204647950480539867), (pn 1199550 295732664229339008), (pn 1133921 585915450659716103), (pn 604953 25387097410697277), (pn 192944 700864858550834656), (pn 199532 531908609164524721), (pn 1058708 318549346640463429), (pn 323580 424457706225447308), (pn 373076 552697233670967658), (pn 1171423 701920596780187141), (pn 254525 786246004928014942), (pn 135262 590574346115361826), (pn 296 512692060585722130)])

def generatedLevels : Nat → Packing
  | 5 => (53,6,7,0,0,9,0,genData5)
  | 6 => (682,5,7,0,0,13,0,genData6)
  | 7 => (1500,4,7,0,0,16,0,genData7)
  | 8 => (1222,3,7,0,0,17,0,genData8)
  | 9 => (560,2,7,0,0,16,0,genData9)
  | 10 => (47,1,7,0,0,12,0,genData10)
  | 11 => (1,0,7,0,0,0,0,genData11)
  | _ => emptyPacking

def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 20 117 4 11 6 1 genIndex6
  | 7 => lookupWord 239 1432 6 15 10 1 genIndex7
  | 8 => lookupWord 495 2971 7 16 11 1 genIndex8
  | 9 => lookupWord 412 2472 7 16 11 1 genIndex9
  | 10 => lookupWord 177 1058 6 15 10 1 genIndex10
  | 11 => lookupWord 22 145 4 11 6 1 genIndex11
  | _ => fun _ => none

def generatedForest : Forest := ⟨507,11,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[], [16, 99, 116]],generatedLevels,generatedIndex⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_0 : block generatedForest 5 0 53 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB5 : block generatedForest 5 0 53 = true := genP5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_0 : block generatedForest 6 0 14 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_14 : block generatedForest 6 14 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_110 : block generatedForest 6 110 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_206 : block generatedForest 6 206 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_302 : block generatedForest 6 302 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_398 : block generatedForest 6 398 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_494 : block generatedForest 6 494 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_590 : block generatedForest 6 590 92 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB6 : block generatedForest 6 0 682 = true := (@block_merge generatedForest 6 0 302 380 (@block_merge generatedForest 6 0 110 192 (@block_merge generatedForest 6 0 14 96 genP6_0 genP6_14) (@block_merge generatedForest 6 110 96 96 genP6_110 genP6_206)) (@block_merge generatedForest 6 302 192 188 (@block_merge generatedForest 6 302 96 96 genP6_302 genP6_398) (@block_merge generatedForest 6 494 96 92 genP6_494 genP6_590)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_0 : block generatedForest 7 0 8 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_8 : block generatedForest 7 8 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_104 : block generatedForest 7 104 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_200 : block generatedForest 7 200 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_296 : block generatedForest 7 296 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_392 : block generatedForest 7 392 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_488 : block generatedForest 7 488 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_584 : block generatedForest 7 584 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_680 : block generatedForest 7 680 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_776 : block generatedForest 7 776 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_872 : block generatedForest 7 872 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_968 : block generatedForest 7 968 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1064 : block generatedForest 7 1064 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1160 : block generatedForest 7 1160 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1256 : block generatedForest 7 1256 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1352 : block generatedForest 7 1352 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_1448 : block generatedForest 7 1448 52 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB7 : block generatedForest 7 0 1500 = true := (@block_merge generatedForest 7 0 680 820 (@block_merge generatedForest 7 0 296 384 (@block_merge generatedForest 7 0 104 192 (@block_merge generatedForest 7 0 8 96 genP7_0 genP7_8) (@block_merge generatedForest 7 104 96 96 genP7_104 genP7_200)) (@block_merge generatedForest 7 296 192 192 (@block_merge generatedForest 7 296 96 96 genP7_296 genP7_392) (@block_merge generatedForest 7 488 96 96 genP7_488 genP7_584))) (@block_merge generatedForest 7 680 384 436 (@block_merge generatedForest 7 680 192 192 (@block_merge generatedForest 7 680 96 96 genP7_680 genP7_776) (@block_merge generatedForest 7 872 96 96 genP7_872 genP7_968)) (@block_merge generatedForest 7 1064 192 244 (@block_merge generatedForest 7 1064 96 96 genP7_1064 genP7_1160) (@block_merge generatedForest 7 1256 96 148 genP7_1256 (@block_merge generatedForest 7 1352 96 52 genP7_1352 genP7_1448)))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_0 : block generatedForest 8 0 1 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1 : block generatedForest 8 1 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_97 : block generatedForest 8 97 80 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_177 : block generatedForest 8 177 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_273 : block generatedForest 8 273 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_369 : block generatedForest 8 369 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_465 : block generatedForest 8 465 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_561 : block generatedForest 8 561 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_657 : block generatedForest 8 657 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_753 : block generatedForest 8 753 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_849 : block generatedForest 8 849 33 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_882 : block generatedForest 8 882 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_978 : block generatedForest 8 978 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1074 : block generatedForest 8 1074 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_1170 : block generatedForest 8 1170 52 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB8 : block generatedForest 8 0 1222 = true := (@block_merge generatedForest 8 0 561 661 (@block_merge generatedForest 8 0 177 384 (@block_merge generatedForest 8 0 1 176 genP8_0 (@block_merge generatedForest 8 1 96 80 genP8_1 genP8_97)) (@block_merge generatedForest 8 177 192 192 (@block_merge generatedForest 8 177 96 96 genP8_177 genP8_273) (@block_merge generatedForest 8 369 96 96 genP8_369 genP8_465))) (@block_merge generatedForest 8 561 321 340 (@block_merge generatedForest 8 561 192 129 (@block_merge generatedForest 8 561 96 96 genP8_561 genP8_657) (@block_merge generatedForest 8 753 96 33 genP8_753 genP8_849)) (@block_merge generatedForest 8 882 192 148 (@block_merge generatedForest 8 882 96 96 genP8_882 genP8_978) (@block_merge generatedForest 8 1074 96 52 genP8_1074 genP8_1170))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_0 : block generatedForest 9 0 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_96 : block generatedForest 9 96 16 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_112 : block generatedForest 9 112 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_208 : block generatedForest 9 208 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_304 : block generatedForest 9 304 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_400 : block generatedForest 9 400 62 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_462 : block generatedForest 9 462 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_558 : block generatedForest 9 558 2 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB9 : block generatedForest 9 0 560 = true := (@block_merge generatedForest 9 0 304 256 (@block_merge generatedForest 9 0 112 192 (@block_merge generatedForest 9 0 96 16 genP9_0 genP9_96) (@block_merge generatedForest 9 112 96 96 genP9_112 genP9_208)) (@block_merge generatedForest 9 304 158 98 (@block_merge generatedForest 9 304 96 62 genP9_304 genP9_400) (@block_merge generatedForest 9 462 96 2 genP9_462 genP9_558)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_0 : block generatedForest 10 0 2 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_2 : block generatedForest 10 2 45 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB10 : block generatedForest 10 0 47 = true := (@block_merge generatedForest 10 0 2 45 genP10_0 genP10_2)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP11_0 : block generatedForest 11 0 1 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB11 : block generatedForest 11 0 1 = true := genP11_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genTables : checkedTables generatedForest 11 := by
  intro k hk
  interval_cases k
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact genB5
  · exact genB6
  · exact genB7
  · exact genB8
  · exact genB9
  · exact genB10
  · exact genB11

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genGeometry : graphValid generatedForest (boundsBefore generatedKnown) = true := by
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowGenerated : Lower true (varsX 507) (graphGoal 507) 12 :=
  lower_forest (g := generatedForest) (i := 0) (hints := 16777283)
    (before_sound generatedKnown generatedPrior) genGeometry genTables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_49677.ForestCore

namespace PEqualNP.Outside.L_meta_49677
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0, 1, 2, 3, 4, 5, 6, 7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffefffffffffffffffefffffffefffffffcffffeeeeeeeeaa00fffffffffffffffefffffffffffffffefffffffefffffffcffffeeeeeeeeaa00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 2 zero, 64, 68)]) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) lowGenerated
  have count : (([(inputs.getD 2 zero, 64, 68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [count] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def sampleInput (r : Row) (i : Fin 8) : Bool := bit r (inputs.getD (coding i) zero)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampledInput (r : Row) : List.ofFn (sampleInput r) = roots.map (bit r) := by
  rw [roots, List.map_ofFn]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sampleCorrect : ∀ r : Row, bit r codedGraph = graph (sampleInput r) := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def signedNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem binaryLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    13 ≤ C.gates.countP (fun g => !signedNot g) := by
  have goalEq : (execute C.gates roots).getD C.output zero = codedGraph := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInput]
    exact (comp (sampleInput r)).trans (sampleCorrect r).symm
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [goalEq] at out
  unfold ForestCore.Repr at out
  have pg : bit 0 codedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  have properGoal : proper codedGraph := by unfold proper; decide +kernel
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates roots fit (by simp) properGoal
    (out.resolve_right (fun h => h properGoal))
  change k ≤ C.gates.countP (fun g => !signedNot g) at hk
  rw [nrm_map (by decide +kernel : roots.all plainWord = true)] at sub
  have step := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have ready : supply true (roots.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, paid⟩ := contraction (observe_proper properGoal) step _ Reach.start ready
  have lower := wholeBound q bank reach hit
  omega

def upperGates : List Gate := [⟨.or, [1, 0]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [10, 14]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩]

theorem upper_shape : ∀ g ∈ upperGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates, 21⟩ (List.ofFn x) = graph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_49677

open PEqualNP.Outside.L_meta_49677 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_49677 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ computes
  by_cases neg : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, hg, eq⟩ := neg
    have fan : FanInTwo ⟨gs, o⟩ := fun t ht => ⟨(legal t ht).1, (legal t ht).2⟩
    have low := binaryLower ⟨gs, o⟩ fan computes
    change 13 ≤ gs.countP (fun g => !signedNot g) at low
    have lt : gs.countP (fun g => !signedNot g) < gs.length := by
      rw [List.countP_eq_length_filter]
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hg, by simp [eq, signedNot]⟩
    refine ⟨upperGates, 21, upper_shape, ?_, upper_sem⟩
    change 14 ≤ gs.length
    omega
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, cap⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun eq => neg ⟨g, hg, eq⟩)), cap⟩
