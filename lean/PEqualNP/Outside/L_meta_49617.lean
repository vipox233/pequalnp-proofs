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

namespace PEqualNP.Outside.L_meta_49617
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 4) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  if m.testBit 8 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 4) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
end PEqualNP.Outside.L_meta_49617

namespace PEqualNP.Outside.L_meta_49617.ForestCore
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
def K211 := extendKnown K173 7 [(211,[]),(217,[64,49,33,118]),(242,[80,32,50]),(244,[64,33,16,49,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V173 low211 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0x7ff003ffffe03ffff0,(pn 9435 581580956095250880)])),(BitVec.ofNat 152 (proofWord80 [0x12a5a94a2a458a12a2,(pn 1001826 103178879860258523)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x7ffffc00ffffc07fff,(pn 1199481 158706453220134407)])),(BitVec.ofNat 152 (proofWord80 [0x4c1306c0c891304c0,(pn 718799 7167281371517513)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x7fffffff0000007fff,(pn 1208925 747557103605514296)])),(BitVec.ofNat 152 (proofWord80 [0x4701c0708f0e1c4708,(pn 1063568 979582212306000749)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x800000000000007fff,(pn 1208925 819614189736259647)])),(BitVec.ofNat 152 (proofWord80 [0x180601803010201803,0x40002000102c242492]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (proofWord80 [0x60080200c00000600c,(pn 7088 215488862788536612)]))),(0x0,0x0)]
def g213C : List ColumnInfo := [(1,0,212,0,5)]
def g213A : List (List Nat) := [[],[64,118]]
def g213D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g213L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g213D5)
  | _ => emptyPacking
def g213I (_ _ : Nat) : Option (Nat × Nat) := none
def g213 : Forest := ⟨213,5,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : block g213 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : block g213 5 0 1=true := g213P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : checkedTables g213 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g213 0 0 0 = true)
  · exact (rfl : block g213 1 0 0 = true)
  · exact (rfl : block g213 2 0 0 = true)
  · exact (rfl : block g213 3 0 0 = true)
  · exact (rfl : block g213 4 0 0 = true)
  · exact g213B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 6 := lower_forest (g:=g213) (i:=0) (hints:=33949191) (before_sound K211 V211) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K211 6 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V211 low213 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffc01ff87fc3fff00,(pn 1208909 678382502157253663)])),(BitVec.ofNat 152 (proofWord80 [0x222894451108808a4a,(pn 47265 476900912396145829)]))),((BitVec.ofNat 152 (proofWord80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (proofWord80 [0x40b018162050082c0c,(pn 208153 98712227001764963)]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffff80003ffff,(pn 1204205 758105008907223071)])),(BitVec.ofNat 152 (proofWord80 [0x84c120980261113010,(pn 228306 776732229628668234)]))),((BitVec.ofNat 152 (proofWord80 [0xf0000000000003ffff,(pn 1208923 513876730662093792)])),(BitVec.ofNat 152 (proofWord80 [0x701c0e0438221c060,(pn 304003 355727768339231116)]))),((BitVec.ofNat 152 (proofWord80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (proofWord80 [0x80201000400020080,(pn 606825 245970254570996240)]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5),(2,0,225,0,5),(32,0,195,0,5),(64,0,163,0,5),(33,0,194,0,4),(66,0,161,0,4)]
def g227A : List (List Nat) := [[],[97],[16,101],[16,80,96],[80],[80,97],[96,16,81],[96,81]]
def g227D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x31825f635474,(pn 45997 628584972743954704)])
def g227D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xc110204810001,(pn 642860 393083663582828395),(pn 965963 861894045253646855),(pn 893878 543212922761643266),(pn 1202589 966390085481570849),(pn 587127 888071362789329216)])
def g227H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (189208 * 1000000000000000000 + 253964038873192720)
def g227D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x3140cc503,(pn 396863 504484021018098960)])
def g227H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xd4f4400e18d31,(pn 472239 44201982521835532),(pn 151115 727451842639041599),(pn 18900 995152596810343793)])
def g227D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1605f
def g227H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xc4005e51,(pn 151115 727451832421910336),0x3c4012a00003a4000,0x10254000020000005])
def g227L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g227D4)
  | 5 => (10,2,3,0,0,7,0,g227D5)
  | 6 => (3,1,3,0,0,6,0,g227D6)
  | 7 => (1,0,3,0,0,0,0,g227D7)
  | _ => emptyPacking
def g227I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g227H5
  | 6 => lookupWord 4 29 1 10 4 2 g227H6
  | 7 => lookupWord 3 31 1 9 2 3 g227H7
  | _ => fun _ => none
def g227 : Forest := ⟨227,7,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P4_0 : block g227 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B4 : block g227 4 0 3=true := g227P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_1 : block g227 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 10=true := (@block_merge g227 5 0 1 9 g227P5_0 g227P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P6_0 : block g227 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B6 : block g227 6 0 3=true := g227P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P7_0 : block g227 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B7 : block g227 7 0 1=true := g227P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact g227B4
  · exact g227B5
  · exact g227B6
  · exact g227B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 8 := lower_forest (g:=g227) (i:=0) (hints:=16777317) (before_sound K213 V213) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K213 8 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V213 low227 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffffffffffffffffff,(pn 1188049 748233456359567423)])),(BitVec.ofNat 152 (proofWord80 [0x282a00a12802852021,(pn 356617 933690654130721093)]))),((BitVec.ofNat 152 (proofWord80 [0xffff000003fffff000,(pn 35025 28946900226674624)])),(BitVec.ofNat 152 (proofWord80 [0x14c280db0a0264206,(pn 488215 296567501390689491)]))),((BitVec.ofNat 152 (proofWord80 [0xfffffffffc00000000,0x67c4351bd4f7fc0000])),(BitVec.ofNat 152 (proofWord80 [0xb27002c9c00b37804b,(pn 605178 24298431456801743)]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffffffff,(pn 1159545 503811834377928767)])),(BitVec.ofNat 152 (proofWord80 [0xc380b30e02cc38048c,(pn 19093 709968060965433018)]))),((21453 * 1000000000000000000 + 254836694424752064),(BitVec.ofNat 152 (proofWord80 [0xfc00c3f0030fc008f0,0x88cbb5a9420cb2cb2c]))),((68276 * 1000000000000000000 + 774967573781409792),(BitVec.ofNat 152 (proofWord80 [0xfc0003f0000f00,(pn 20383 834693037717654576)]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,2,45,16,5)]
def g63A : List (List Nat) := [[],[65],[80,50],[80,65,50]]
def g63D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g63L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g63D5)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,5,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 6 := lower_forest (g:=g63) (i:=0) (hints:=66883) (before_sound K227 V227) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K227 6 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V227 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0x1ffffffffffffffff,(pn 1044272 645473274679001119)])),(BitVec.ofNat 152 (proofWord80 [0x2d1415450951429085,(pn 137578 134315874846955189)]))),((BitVec.ofNat 152 (proofWord80 [0xffffff80001ffff800,(pn 277985 541452437586477024)])),(BitVec.ofNat 152 (proofWord80 [0x4800a6006d80132019,(pn 878832 884460274381327459)]))),((BitVec.ofNat 152 (proofWord80 [0x1ffffffffe0000000,(pn 15128 772582362603028480)])),(BitVec.ofNat 152 (proofWord80 [0x705938164e059bc12e,(pn 10406 370070696457387503)]))),((BitVec.ofNat 152 (proofWord80 [0x1ffffffffffffffff,(pn 965002 750647616719028255)])),(BitVec.ofNat 152 (proofWord80 [0x8061c01870061c0230,0x58c3484e4854a5294a]))),((BitVec.ofNat 152 (proofWord80 [0xfe0000000000000000,(pn 20505 436140398239024096)])),(BitVec.ofNat 152 (proofWord80 [0x7e001f8007e003c0,(pn 20145 147607051862946188)]))),(0x0,0x0),((243983 * 1000000000000000000 + 393810807020059648),(BitVec.ofNat 152 (proofWord80 [0x18000600018000400,(pn 7121 344073119698534928)]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[],[65]]
def g95D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g95L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g95D7)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 1=true := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact g95B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=16844355) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[]),(126,[80,50]),(159,[64,16,49,118]),(190,[64,33,49,80,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffffffffffffffffff,(pn 1026556 280180980198671359)])),(BitVec.ofNat 152 (proofWord80 [0x28802a40252014805,(pn 118671 517216846202053929)]))),((BitVec.ofNat 152 (proofWord80 [0x1ffff00007fffc00,(pn 296810 583410831684239360)])),(BitVec.ofNat 152 (proofWord80 [0x54c294c15b60a99099,(pn 898875 416347826782969063)]))),((BitVec.ofNat 152 (proofWord80 [0x1ffffffff8000000,(pn 34018 381500930361162752)])),(BitVec.ofNat 152 (proofWord80 [0x2700270013800de02e,(pn 10332 726009987733752931)]))),((BitVec.ofNat 152 (proofWord80 [0x1fffffffffffffff,(pn 946113 141726850976841759)])),(BitVec.ofNat 152 (proofWord80 [0xb80338019c00ce0130,0x58c14c4a4c4c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffe000000000000000,(pn 20505 436140397198868448)])),(BitVec.ofNat 152 (proofWord80 [0xc013c009e004f001c0,(pn 20190 543609803878060692)]))),((243983 * 1000000000000000000 + 393810807020027904),(BitVec.ofNat 152 (proofWord80 [0x1c000e0007000200,(pn 7122 497000122140615448)]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[80,50]]
def g111D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g111L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=16778595) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[]),(125,[65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffffffc0003fffc00a,(pn 994035 567030403006992320)])),(BitVec.ofNat 152 (proofWord80 [0x25104a90da9094856a,(pn 918477 411696433536251091)]))),((BitVec.ofNat 152 (proofWord80 [0x3ffffffffffffff7,(pn 153929 646992754655100991)])),(BitVec.ofNat 152 (proofWord80 [0x98213021302190243,(pn 153929 497687808414077253)]))),((BitVec.ofNat 152 (proofWord80 [0x3fffffffc0000009,(pn 968614 987087710460833792)])),(BitVec.ofNat 152 (proofWord80 [0x4e009c009c00de0b88,(pn 321650 706874778220507331)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x3ffffffffffffffa,(pn 104728 656800526303756351)])),(BitVec.ofNat 152 (proofWord80 [0x7004e004e004e00c08,(pn 104575 894558447524946570)]))),((BitVec.ofNat 152 (proofWord80 [0xffc000000000000009,(pn 103348 306394496712835008)])),(BitVec.ofNat 152 (proofWord80 [0x2700270027001001,(pn 82641 782115416067459884)]))),((BitVec.ofNat 152 (proofWord80 [4,(pn 1107827 368516099187146752)])),(BitVec.ofNat 152 (proofWord80 [0x803800380038002004,(pn 642283 420274549380549680)]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7)]
def g119A : List (List Nat) := [[],[65]]
def g119D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g119L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g119D7)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,7,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 1=true := g119P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact (rfl : block g119 6 0 0 = true)
  · exact g119B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 8 := lower_forest (g:=g119) (i:=0) (hints:=16844101) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 8 [(119,[]),(123,[80,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xffffffffffffffffff,(pn 1172229 995017926644604238)])),(BitVec.ofNat 152 (proofWord80 [0x290140054012802902,(pn 717951 35994235042015560)]))),((BitVec.ofNat 152 (proofWord80 [0xff800fffe0003fff80,(pn 70421 605179252336025983)])),(BitVec.ofNat 152 (proofWord80 [0xb22a65298adb15324c,(pn 977115 970452202931118463)]))),((BitVec.ofNat 152 (proofWord80 [0xfffffffc00000,(pn 20224 401548638201251957)])),(BitVec.ofNat 152 (proofWord80 [0x3c13804e009c01bc17,0x4855b4db6cccc20a55]))),((BitVec.ofNat 152 (proofWord80 [0xfffffffffffff,(pn 1072453 24558161588654007)])),(BitVec.ofNat 152 (proofWord80 [0xc05c06700ce019c018,(pn 14495 358300769392527031)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfffff0000000000000,(pn 21088 730622208970326202)])),(BitVec.ofNat 152 (proofWord80 [0x6007800f001e0060,(pn 19904 633904163685680290)]))),(0x0,0x0),((129962 * 1000000000000000000 + 219234010589033153),(BitVec.ofNat 152 (proofWord80 [0x8001000200000,0x2221c9000]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7),(1,0,174,0,6),(4,0,171,0,6),(8,0,167,0,6),(32,0,143,0,6),(0,2,45,128,5),(3,0,172,0,5),(6,0,169,0,5),(9,0,166,0,5),(12,0,163,0,5),(34,0,141,0,5),(36,0,139,0,5),(11,0,164,0,4),(128,0,45,0,4),(128,2,45,0,4)]
def g175A : List (List Nat) := [[],[80,50]]
def g175D3 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x6304c8650,(pn 629704 181864926418315970),(pn 794023 489807658662560032)])
def g175D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [(pn 41920 225907504956049794),0x26841000438200,0x401f4f,(pn 337421 52536309910358981),(pn 844147 554643843075294193),(pn 1062022 591235707522625728),(pn 397343 949902941296525877),(pn 1061777 116414309502405984),(pn 1002974 699228480103049090),(pn 440177 738937317356029248),(pn 746577 618443134739812469),(pn 417081 587619651736863585),(pn 1044015 784120169510853457),(pn 340731 975303139244435334),(pn 440159 238219319491773728),(pn 1039957 517928924753235312),(pn 1002655 131701661766288082),(pn 457005 780909303818161488),(pn 341119 880415517904429189),(pn 417136 549010451411058976),(pn 1023413 43090679025489219),(pn 378122 477271144779252456),(pn 1062939 800542491419444544),(pn 340739 474318218830258564),(pn 1002691 546220792802246944),(pn 658627 584114104620420470),(pn 1002655 39936710686573176),(pn 454072 695684227974681189),(pn 321901 886217266297163911),(pn 381718 782422341033214224)])
def g175H4 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [9,(pn 302232 427681176815140864)])
def g175D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x18,(pn 75557 863725914323419248),(pn 159398 315540924250231556),0x40804c10e080d08041,(pn 1029570 261762543322972416),(pn 11224 844103381091383905),(pn 31397 512673081094668558),(pn 37778 953272647577763841),(pn 151127 941776968230635072),(pn 755660 510450218502738946),(pn 368768 928855297911615579),(pn 1204087 939860176909446379),(pn 164151 751067632545638778),(pn 200785 866813530399417753),(pn 237419 856335252513677303),(pn 820943 836290206466349766),(pn 725351 690515633877505429),(pn 100337 232481506321059827),(pn 1081186 264160246156201091),(pn 41249 948897115189168065),(pn 1021969 727143163200143792),(pn 11505 700655741136853077),(pn 198023 541726104698052820),(pn 560699 937500163178070865),(pn 882758 202934192735933574),(pn 1150932 303227731792442633),(pn 882671 59257908680414247),(pn 810600 854635220406980826),(pn 1116748 205571657604350827),(pn 838887 197332936492059114),(pn 1122312 21811654630062538),(pn 767986 405046154499765742),(pn 657188 420726024371893176),(pn 815364 943912829151058662),(pn 239145 289651944311171982),(pn 947136 443651746357440202),(pn 766226 668314617695156394),(pn 647107 994667307523173040),(pn 774977 520369610248628930),(pn 681763 361897998172318474),(pn 309201 853117251612011049),(pn 27844 555251057877821604),(pn 148860 852040492651290768),(pn 559717 251911859900678721),(pn 1033406 564233469466642695),(pn 960767 829512585342362655),(pn 669493 467610178769686654),(pn 250677 498176733813293434),(pn 440729 934747627860592553),(pn 398155 825560042900561797),(pn 629260 539751256653057015),(pn 328594 201918762884627036),(pn 250958 942467430520580976),(pn 399372 723840611247429067),(pn 383843 276665722660349780),(pn 628680 957316665884367186),(pn 96881 187672970319197337),(pn 382694 631799550952458580),(pn 322129 417114163039589645),(pn 80034 264455018413036596),(pn 319805 16884143717569553),(pn 73833 572825849368764628),(pn 524395 295258736290234656)])
def g175H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xf3781c00680609e780,0x63000000381dbe00,(pn 39504 639813878215671808),(pn 1071982 384985808228581385),(pn 320037 174621540755425066),(pn 226683 394616958512356039),(pn 737187 968340803021708584),0x697780000004820008,(pn 585574 150942567918471396),(pn 723924 25595473858469152)])
def g175D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x6080708,(pn 491145 283791949383566488),(pn 760374 917241791901466727),(pn 9594 747887606456713222),(pn 494991 218756898900740632),(pn 302384 847799477510343169),(pn 755773 21655437727629956),(pn 616298 826824781033152528),(pn 757941 595488380545798663),(pn 19791 125719797708374540),(pn 688313 481303596694903499),(pn 460924 206298464171473008),(pn 1058105 442758637758607712),(pn 775112 27022861875119489),(pn 7185 81698231819649441),(pn 260943 149005842052399504),(pn 234970 890663312788585101),(pn 81499 967794989341074410),(pn 577584 405258228802788003),(pn 341892 860314667276349333),(pn 238854 173511596793680005),(pn 678874 785820254737556188),(pn 403949 192049543252544513),(pn 378425 988110885140302848),(pn 56474 946514497580039553),(pn 391907 469896206498528600),(pn 250801 181258224980265981),(pn 686235 8362785511919863),(pn 1023961 180785227974857999),(pn 1044921 653955499803907392),(pn 903619 815745454520259668),(pn 75064 503670845943560597),(pn 155752 296438402595748825),(pn 85292 381127417728733109),(pn 383115 805093542476718331),(pn 1003836 50894413771592207),(pn 1044918 195485367401271568),(pn 1196318 698359136773298357),(pn 131442 514077938842834249),(pn 159229 472507715424156116),(pn 538630 302956159205773213),(pn 326451 621190630153199865),(pn 341523 873658162130784527),(pn 401642 164934533330583824)])
def g175H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [(pn 1104794 797379811612295168),0x8490000000,0x84d000000000,0x353000000a1300,0xc36000d2864a93bf,(pn 45457 977912437135086397),(pn 245693 992967865016254464),(pn 11916 596671616370343949),(pn 387234 51595310908785190),(pn 507756 276056221655665152),(pn 10258 871188377191841792),0xbc2000000000000000,0x883a1e00000049e00,0x13e24c0,0xc06937000000000000,(pn 1097655 59362013159376640),0x418000000000fc40,0x51200000054b008000,0x52d00,0xf3a000454a380,0,0xe32000000a2a00,(pn 8056 160611464061321216),(pn 139991 201364719632908288),0x42f0000004a500,(pn 14656 86785573548720128),0x651000000,0x7a300000000000,0x61ce450000000000,0xe89000,0xf000505d23f3100000,0xf3f00069c000000e,0x207000000000aac,(pn 759695 639256738510667809),(pn 43735 230600530794386224),0x41100050c0007af,0x80300000000000060,(pn 151115 727451828646838273),(pn 404740 11721261272007235),0x71700010e51f42,(pn 751526 209236552942622720),(pn 118077 614749909159805440)])
def g175D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x14c16e15c,(pn 98014 653528482142815492),(pn 51506 552672286248862583),(pn 610902 313303934715581570),(pn 21081 197053358799777090),(pn 638480 22761700381772794),(pn 783900 225699719275324447),(pn 553100 909724825035076880)])
def g175H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x31a46508f913,(pn 255008 157118513814588032),(pn 674781 898219273940447744),0x33600000000a2a,(pn 231395 957856887185080321),(pn 104652 162530912562678843),(pn 118065 881055357074145280),0xb6eab0000000015cc,0xa14000000000,0x2cb0006c00073401,(pn 171357 598978459991802883),(pn 329393 420861107524124673),(pn 188894 660414093560979897),(pn 252665 53580397899677829),(pn 604604 119804401047061083),(pn 955140 126334648563269632),0xce05c26b14710c9,(pn 1138192 328364448167021619),(pn 13134 92936194937783306)])
def g175D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9b8013f
def g175H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xa1014008a0034b0e,(pn 235740 165910892808241338),(pn 729609 297437857612300388),0x3c7e10066609100401])
def g175L : Nat → Packing
  | 3 => (3,5,4,0,0,4,0,g175D3)
  | 4 => (37,4,4,0,0,9,0,g175D4)
  | 5 => (86,3,4,0,0,10,0,g175D5)
  | 6 => (57,2,4,0,0,11,0,g175D6)
  | 7 => (11,1,4,0,0,9,0,g175D7)
  | 8 => (1,0,4,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 17 0 6 2 0 g175H4
  | 5 => lookupWord 11 67 5 11 6 1 g175H5
  | 6 => lookupWord 27 271 4 12 7 1 g175H6
  | 7 => lookupWord 18 127 5 11 6 1 g175H7
  | 8 => lookupWord 5 31 5 9 4 1 g175H8
  | _ => fun _ => none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P3_0 : block g175 3 0 3=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B3 : block g175 3 0 3=true := g175P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P4_0 : block g175 4 0 37=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B4 : block g175 4 0 37=true := g175P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_3 : block g175 5 3 83=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 86=true := (@block_merge g175 5 0 3 83 g175P5_0 g175P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_19 : block g175 6 19 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 57=true := (@block_merge g175 6 0 19 38 g175P6_0 g175P6_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_5 : block g175 7 5 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 11=true := (@block_merge g175 7 0 5 6 g175P7_0 g175P7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 1=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact g175B3
  · exact g175B4
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1395) (before_sound K119 V119) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K119 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V119 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xfffffffe0003fff801,(pn 1011051 750025154410808288)])),(BitVec.ofNat 152 (proofWord80 [0x489402540da81290ad,(pn 397143 457607857608952931)]))),((BitVec.ofNat 152 (proofWord80 [0xfc00fffffffffffffe,(pn 453441 73340422210715679)])),(BitVec.ofNat 152 (proofWord80 [0x902610982130432048,(pn 453422 337933835429385381)]))),((BitVec.ofNat 152 (proofWord80 [0xfffffffc000001,(pn 272807 894734111288359936)])),(BitVec.ofNat 152 (proofWord80 [0xe13804e009c01bc171,(pn 82728 32112042170223715)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffff,(pn 314257 150038093542195231)])),(BitVec.ofNat 152 (proofWord80 [0x1c0a7014e029c0181,(pn 12025 548204252345494362)]))),((BitVec.ofNat 152 (proofWord80 [0xffff00000000000001,(pn 165173 406518685240164320)])),(BitVec.ofNat 152 (proofWord80 [0x38007000e00200,(pn 162331 441457229052916108)]))),(0x0,0x0),((742129 * 1000000000000000000 + 573845209073025024),(BitVec.ofNat 152 (proofWord80 [0x200c0018003000400,(pn 642284 211571867668464144)]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7)]
def g183A : List (List Nat) := [[],[32]]
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g183L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g183D7)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,7,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 1=true := g183P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact g183B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 8 := lower_forest (g:=g183) (i:=0) (hints:=66885) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 8 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0x7ffc01ffffffffff,(pn 1207749 76172802391736335)])),(BitVec.ofNat 152 (proofWord80 [0xd01482c82a4252148,(pn 197162 639215795455219029)]))),((BitVec.ofNat 152 (proofWord80 [0x7ffffffff0007ffc,0xf354385e8000f000f0])),(BitVec.ofNat 152 (proofWord80 [0x5615914814c1b60990,(pn 967845 625412211484865331)]))),((BitVec.ofNat 152 (proofWord80 [0xff800001ffffff8000,0x26278cbf400f000f00])),(BitVec.ofNat 152 (proofWord80 [0x9819e2702701380de1,(pn 529606 566235414086234931)]))),((BitVec.ofNat 152 (proofWord80 [0x1ffffffffff,(pn 1201105 510886668482179087)])),(BitVec.ofNat 152 (proofWord80 [0xe01e03803801c00e01,(pn 604906 364121806052401698)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (proofWord80 [0x200000c006003002,0xf041802444444444]))),((7591 * 1000000000000000000 + 16750954317807616),(BitVec.ofNat 152 (proofWord80 [0x4000010008004000,0x888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33]]
def g207D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g207L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g207D7)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,7,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 1=true := g207P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact g207B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=16778851) (before_sound K183 V183) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K183 8 [(207,[]),(222,[64,33,49,118]),(238,[80,50,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V183 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xfe007ffe0007ffe00a,(pn 473888 424522792529871101)])),(BitVec.ofNat 152 (proofWord80 [0xa44b12545b514a456a,(pn 322772 713876412694577405)]))),((BitVec.ofNat 152 (proofWord80 [0xfffffffffffffffff7,(pn 622796 703734315361567293)])),(BitVec.ofNat 152 (proofWord80 [0xc812009802600c8247,(pn 616296 534561902490042396)]))),((BitVec.ofNat 152 (proofWord80 [0x7ffffff8000001,(pn 1041359 273497474294221919)])),(BitVec.ofNat 152 (proofWord80 [0xf09c04e013806f0381,(pn 1003580 346730908999485983)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x7ffffffffffff2,(pn 98882 438542661405913735)])),(BitVec.ofNat 152 (proofWord80 [0xe047011c04700400,(pn 96520 666831310233012867)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffff80000000000001,(pn 127709 76785802862673384)])),(BitVec.ofNat 152 (proofWord80 [0x18006001800800,(pn 42649 458364795569873248)]))),((BitVec.ofNat 152 (proofWord80 [0xc,(pn 1077852 515626583479795986)])),(BitVec.ofNat 152 (proofWord80 [0x10060018006001000,(pn 151742 935965986388115456)]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,7),(4,0,211,0,7),(0,1,86,128,6),(2,0,213,0,6),(16,0,199,0,6),(3,0,212,0,5),(4,1,82,128,5),(5,0,210,0,5),(17,0,198,0,5),(18,0,197,0,5),(64,0,151,0,5),(128,0,86,0,5),(128,1,86,0,5),(6,0,209,0,4),(65,0,150,0,4),(68,0,147,0,4),(132,0,82,0,4)]
def g215A : List (List Nat) := [[]]
def g215D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x120224040000,0xd99b0518,(pn 373568 496804470940959488),(pn 835123 416512177414472804),(pn 401792 948295335104775793),(pn 159771 70919453202271553),(pn 342299 319132306789999476),(pn 379376 64632119659696976),(pn 673972 969325629891545462),(pn 984411 140244220480930358),(pn 461449 124115227191120161),(pn 1001945 141433926115058054),(pn 379304 60357766882297680)])
def g215D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x62,(pn 26122 373104193907982342),(pn 152296 537514720171655425),(pn 19019 174170457576376324),(pn 680316 570238985802104876),(pn 21547 112147326108733456),(pn 161764 256558838483140720),(pn 906694 364710971881035792),(pn 118077 615595679640139779),(pn 656504 352985016756275882),(pn 777523 960458440620804490),(pn 437218 173338536321910922),(pn 134691 282052757738882857),(pn 889789 799069763577021865),(pn 473815 323433036388828200),(pn 1153319 83200761719063176),(pn 737381 573356272986030504),(pn 434854 645935972301146558),(pn 1089405 515227676471012987),(pn 693167 95384006890600878),(pn 317037 810303005843492786),(pn 200896 508111764986961636),(pn 803585 531478776006278034),(pn 961626 883336883842969163),(pn 200834 160263130405384874),(pn 501131 123218599272964777),(pn 803756 761609288316299943),(pn 760039 670357353915378474),(pn 619734 262141693353192554),(pn 70124 205706504232020392),(pn 242940 832655464884512416),(pn 1142024 472579305414232707),(pn 1007428 941540098336098829),(pn 1083517 436566284606252087),(pn 707291 134492050113204468),(pn 1007142 444189437342139257),(pn 1044031 853687186028826087),(pn 553998 534567289801686681),(pn 383715 946855252666416247),(pn 250380 105206229635430492),(pn 94825 989422535765060196),(pn 415902 580421109242113481),(pn 476150 230072377041983341),(pn 72322 725041535862070708),(pn 138191 239371956143355472),(pn 552764 957206349655952705),(pn 1002166 284257499282891911),(pn 381869 258182159724728861),(pn 316061 444203768043685972),(pn 74423 573797808773091656),(pn 488092 978616671652841296)])
def g215H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xf8fa5200,(pn 686200 432961750724706304),(pn 694298 616087881744743288)])
def g215D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x20200180,(pn 33144 241740208067872912),(pn 40306 156297194433458312),(pn 987587 962746221458131200),(pn 683664 149630189700383748),0x90a00b0c2020018304,(pn 18898 887747772606513668),(pn 18897 572717614547927296),(pn 57261 8459431164788930),(pn 42778 27339705657598273),(pn 68807 810629456913563715),(pn 938058 765669877693186154),(pn 910254 730467922493833673),(pn 151254 249240845482467404),(pn 264568 37851319259923330),(pn 126346 857263362383283334),(pn 143014 545025420982577731),(pn 314744 717991798366148618),(pn 481854 349654906610428548),(pn 374425 465406436886008026),(pn 48396 743582245409485037),(pn 839100 37841994070548312),(pn 654218 905698742985349632),(pn 286429 578376329881635969),(pn 586371 609109391293688836),(pn 531156 404841462207608206),(pn 400208 482259929077709784),(pn 705034 379853992327200633),(pn 686292 43074578976691191),(pn 1021603 706253700090107197),(pn 1158480 9213415066521411),(pn 905981 11407041459606740),(pn 283297 120136122716648855),(pn 311368 732786924235898841),(pn 397194 542773848432189173),(pn 383728 582734786297938429),(pn 398230 609448547032584735),(pn 876315 25870329032036641),(pn 1186883 266469613260394741),(pn 75207 902789291759101197),(pn 306922 716162709278480213),(pn 100303 400030684535070517),(pn 364248 927810504182014458),(pn 415902 302060639241663759),(pn 776964 231966196765066560)])
def g215H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x618361cffd1000f78,(pn 1081422 71496489771728903),(pn 377789 320502039919380736),0x6b35d80037d6d08b,(pn 764728 222382378605264395),(pn 759458 586015987157630976),0xc2a1d25420194cb791,(pn 482862 149305455063973888),(pn 113336 795588871494061339),(pn 4722 366486717939420544),(pn 26205 981469519047499663),(pn 551495 311335232259036252),0x2120000018380010a3,(pn 358901 422202563175028883),(pn 813243 274453581791784960),0xcad0621011a000150])
def g215D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x40e084a3062840e084,(pn 913971 754721247399870626),(pn 331389 443277451820307205),(pn 208528 922848920041185316),(pn 491738 356356218297783315),(pn 512387 241443259232983116),(pn 96075 916937520736984220),(pn 326383 720700424736608000),(pn 301246 847923168172904442),(pn 642192 410056305181182589),(pn 1007033 776258252852558096)])
def g215H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x20d2980,0x19,(pn 990811 574122820330995008),0x354003110000,0xf100132000000000,0x400,0,0,0x971af7a0000000,0x125001230001,(pn 226673 591177742970257408),0x2200034200000002f,(pn 17192 365476757767217344),0x157000000000,0x34,(pn 311820 735465602462777344),0x7dd86a800a2de45224,(pn 755578 637259143234191360),0x11,(pn 1057810 92221418275864598),(pn 1019081 657383205589745712),(pn 680091 822320950307717120),0xf002,(pn 831136 500985079435100160),(pn 12704 530207257235488790),(pn 528921 259040058797719552),0x3208420])
def g215D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6242013f
def g215H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x99a800000,(pn 439235 453586225683824892),(pn 1008230 324153050302793984)])
def g215L : Nat → Packing
  | 4 => (16,4,5,0,0,7,0,g215D4)
  | 5 => (68,3,5,0,0,10,0,g215D5)
  | 6 => (55,2,5,0,0,11,0,g215D6)
  | 7 => (14,1,5,0,0,9,0,g215D7)
  | 8 => (1,0,5,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 23 2 8 4 0 g215H5
  | 6 => lookupWord 17 109 4 11 7 0 g215H6
  | 7 => lookupWord 13 211 2 10 6 0 g215H7
  | 8 => lookupWord 3 23 5 8 4 0 g215H8
  | _ => fun _ => none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P4_0 : block g215 4 0 16=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B4 : block g215 4 0 16=true := g215P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_3 : block g215 5 3 65=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B5 : block g215 5 0 68=true := (@block_merge g215 5 0 3 65 g215P5_0 g215P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_13 : block g215 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 55=true := (@block_merge g215 6 0 13 42 g215P6_0 g215P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_6 : block g215 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 14=true := (@block_merge g215 7 0 6 8 g215P7_0 g215P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : block g215 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : block g215 8 0 1=true := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact g215B4
  · exact g215B5
  · exact g215B6
  · exact g215B7
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=16844359) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[]),(250,[80,50,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xc007ffffe0ffff4214,(pn 680021 57260005700695455)])),(BitVec.ofNat 152 (proofWord80 [0x8a510a204224404004,(pn 692662 942138411190080910)]))),((BitVec.ofNat 152 (proofWord80 [0xfff800ffffffe014ce,(pn 604481 68322111389059576)])),(BitVec.ofNat 152 (proofWord80 [0x602c028000820486,0x630c30c30c30c248b8]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffff0000ffffa110,(pn 265024 372176254625091195)])),(BitVec.ofNat 152 (proofWord80 [0x80300b040900a010,(pn 43721 711509306511362673)]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffff0000860d,(pn 1095589 28459005487091815)])),(BitVec.ofNat 152 (proofWord80 [0x2304408c008e048208,(pn 1121943 858003320377217091)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x9923,(pn 339420 95459838200389508)])),(BitVec.ofNat 152 (proofWord80 [0xc0180300830081901,(pn 9596 991805712766076164)]))),((BitVec.ofNat 152 (proofWord80 [0x6ae0,(pn 226673 586674143347073024)])),(BitVec.ofNat 152 (proofWord80 [0x300600c010c0100260,(pn 170309 711063254179586048)]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,1,82,136,6),(0,16,137,66,6),(2,16,137,64,5),(3,0,216,0,5),(8,1,82,128,5),(9,0,210,0,5),(17,0,202,0,5),(64,16,137,2,5),(80,0,139,0,5),(128,1,82,8,5),(129,0,90,0,5),(10,0,209,0,4),(19,0,200,0,4),(25,0,194,0,4),(66,0,137,0,4),(66,16,137,0,4),(72,0,147,0,4),(82,0,137,0,4),(130,0,89,0,4),(136,0,82,0,4),(136,1,82,0,4),(137,0,82,0,4)]
def g219A : List (List Nat) := [[],[64,49,118]]
def g219D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x1010,0xb6785b3060336d8f70,(pn 399411 7365666447886221),(pn 420682 990034033031055697),(pn 342239 386355465162007892),(pn 399410 382060225701430592)])
def g219D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x18,0x206000860542050401,(pn 756759 256002975084069059),(pn 18896 383603171110427672),(pn 56673 104144579597501524),(pn 95067 621276638626644492),(pn 75857 642813938496178177),(pn 379426 846053479726780416),(pn 586766 826077124269941018),(pn 77187 259370266440690274),(pn 616806 585508194853021858),(pn 163016 248491462918628993),(pn 691256 490541112615887936),(pn 1181644 85844323183682016),(pn 425252 890213161395563172),(pn 1196877 291430016688728637),(pn 1047283 77892771416418535),(pn 1007294 355089486022615871),(pn 1041693 764844229541629879),(pn 535196 835541530091993069),(pn 912935 160265369626660823),(pn 441857 283715108220125149),(pn 704896 675933828896701796),(pn 401735 205239141103820177),(pn 383848 473709741493146949),(pn 326470 235755889278410068),(pn 96946 553478850511463760),(pn 387813 586230987313203521),(pn 342057 658561632581129553),(pn 306791 127339817252967461),(pn 13866 882787149849417940),(pn 143638 502506476526981456),(pn 289430 730306953706556736)])
def g219H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x940000d6a1730000,0x72fac54000ac000d])
def g219D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x52a118465433,(pn 41514 858243227896581224),(pn 912943 362310753441122833),(pn 78161 216367717556187329),(pn 770337 776645656351617056),(pn 24885 524700023039233692),(pn 585951 825917415849657112),(pn 56816 76072289091990289),(pn 692215 276185091734313137),(pn 114545 237520625072212131),(pn 77483 451021503551285478),(pn 956359 113473967696395347),(pn 327063 828155367758135356),(pn 513422 481508471485303047),(pn 637977 419800374000394518),(pn 923451 619805849858175214),(pn 60200 340994159304665964),(pn 951643 141268908390104129),(pn 638567 415096003806146818),(pn 140545 186629469575528776),0xffd8554ff58554ff59,(pn 99759 237969315657752565),(pn 345950 191371956289348095),(pn 381719 624948397053596171),(pn 1197218 243966128067268945),(pn 905967 239399380926551316),(pn 150327 507937460271969681),(pn 160511 196139193859440212),(pn 472529 816368620986699749),(pn 327042 201926217362653367),(pn 1023944 133469798304912399),(pn 497273 561017120840812864)])
def g219H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x65400000aa20000000,(pn 43488 217168172076137472),3,(pn 680061 126182041992101912),0x64b4684600,0x80fb2c00690,0,0x91c000000000000004,(pn 953106 372800425112895488),0xf3000000722,(pn 11805 916207184984670208),0xe0dc9800d282088b69,(pn 1011019 241272696247418880),0xc33cf418000001,(pn 613908 450606237037363210),(pn 298901 817598352719609856),(pn 38429 384610891588075685),0x28e14e1c004005c])
def g219D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x228603e33451,(pn 39551 630737257258063302),(pn 67747 997225434923714688),(pn 756935 708071826166972482),(pn 675828 987979907267899656),(pn 664125 378559580691678720),(pn 1024182 948212382807361992),(pn 851411 637408259099677690),(pn 774417 518356083540731935),(pn 996712 820704909159692608)])
def g219H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x14540,0xa7491294e7,0x7c0e8e0000064d000,(pn 182991 701409022499058960),0,(pn 59140 261500312822480896),0x92f08000000000000,0x61d001a0c007600000,0x13c0020b68200,0x240800000002c7800,(pn 153477 102083190932116552),(pn 113336 795588871485128704),0x3a40004a00003400,0x261001c2000713000,0xd24000c5e54f,(pn 54426 861684442925237760),0x1a3603000000e2800,(pn 155838 93934728356823040),0x221108000001900802])
def g219D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g219H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x24600480000,0x83ba800000055913e,(pn 377789 319180426943029248),0x8c00242c0000,(pn 113336 795588871485638944),0x2880000000000044,0x320000000007c80000,8])
def g219L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g219D5)
  | 6 => (38,3,5,0,0,10,0,g219D6)
  | 7 => (34,2,5,0,0,11,0,g219D7)
  | 8 => (11,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 4 8 3 1 g219H6
  | 7 => lookupWord 12 127 3 11 6 1 g219H7
  | 8 => lookupWord 12 127 5 11 6 1 g219H8
  | 9 => lookupWord 4 71 2 9 4 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 7=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1 : block g219 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_5 : block g219 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 38=true := (@block_merge g219 6 0 1 37 g219P6_0 (@block_merge g219 6 1 4 33 g219P6_1 g219P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_6 : block g219 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_23 : block g219 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 34=true := (@block_merge g219 7 0 6 28 g219P7_0 (@block_merge g219 7 6 17 11 g219P7_6 g219P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_2 : block g219 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 11=true := (@block_merge g219 8 0 2 9 g219P8_0 g219P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 1=true := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact g219B5
  · exact g219B6
  · exact g219B7
  · exact g219B8
  · exact g219B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=16842819) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior381 : Lower true (varsX 381) (graphGoal 381) 10 := by
  have h := lift_ok (u := true) (ms := ([96, 33, 98, 99, 100, 101, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 381) (T := graphGoal 381) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low219
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior508 : Lower true (varsX 508) (graphGoal 508) 9 := by
  have h := lift_ok (u := true) (ms := ([32, 49, 84, 101]).map swapRows ++ fixRows 64 0)
    (raw := varsX 508) (T := graphGoal 508) (xs := [(inputs.getD 6 zero,4,68)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low227
  have card : (([(inputs.getD 6 zero,4,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior445 : Lower true (varsX 445) (graphGoal 445) 9 := by
  have h := lift_ok (u := true) (ms := ([32, 49, 84, 101]).map swapRows ++ fixRows 1 0)
    (raw := varsX 445) (T := graphGoal 445) (xs := [(inputs.getD 0 zero,8,9)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low227
  have card : (([(inputs.getD 0 zero,8,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior444 : Lower true (varsX 444) (graphGoal 444) 8 := by
  have h := lift_ok (u := true) (ms := ([32, 49, 84, 101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 444) (T := graphGoal 444) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low227
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior505 : Lower true (varsX 505) (graphGoal 505) 8 := by
  have h := lift_ok (u := true) (ms := ([112, 66, 115, 117, 118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 505) (T := graphGoal 505) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior501 : Lower true (varsX 501) (graphGoal 501) 8 := by
  have h := lift_ok (u := true) (ms := ([67, 84]).map swapRows ++ fixRows 64 0)
    (raw := varsX 501) (T := graphGoal 501) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior500 : Lower true (varsX 500) (graphGoal 500) 7 := by
  have h := lift_ok (u := true) (ms := ([32, 49, 50, 83, 100]).map swapRows ++ fixRows 0 0)
    (raw := varsX 500) (T := graphGoal 500) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior497 : Lower true (varsX 497) (graphGoal 497) 7 := by
  have h := lift_ok (u := true) (ms := ([112, 66, 99, 116, 117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 497) (T := graphGoal 497) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior493 : Lower true (varsX 493) (graphGoal 493) 8 := by
  have h := lift_ok (u := true) (ms := ([16, 33, 99, 100, 101, 118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 493) (T := graphGoal 493) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior477 : Lower true (varsX 477) (graphGoal 477) 8 := by
  have h := lift_ok (u := true) (ms := ([84, 118]).map swapRows ++ fixRows 128 0)
    (raw := varsX 477) (T := graphGoal 477) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior437 : Lower true (varsX 437) (graphGoal 437) 7 := by
  have h := lift_ok (u := true) (ms := ([67, 84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 437) (T := graphGoal 437) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior413 : Lower true (varsX 413) (graphGoal 413) 7 := by
  have h := lift_ok (u := true) (ms := ([84]).map swapRows ++ fixRows 0 0)
    (raw := varsX 413) (T := graphGoal 413) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior380 : Lower true (varsX 380) (graphGoal 380) 7 := by
  have h := lift_ok (u := true) (ms := ([32, 81, 82]).map swapRows ++ fixRows 0 0)
    (raw := varsX 380) (T := graphGoal 380) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low91
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior377 : Lower true (varsX 377) (graphGoal 377) 7 := by
  have h := lift_ok (u := true) (ms := ([112, 66, 115, 117, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 377) (T := graphGoal 377) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low173
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior373 : Lower true (varsX 373) (graphGoal 373) 7 := by
  have h := lift_ok (u := true) (ms := ([112, 33, 66, 117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 373) (T := graphGoal 373) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior365 : Lower true (varsX 365) (graphGoal 365) 7 := by
  have h := lift_ok (u := true) (ms := ([16, 33, 99, 100, 101, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 365) (T := graphGoal 365) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low211
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior317 : Lower true (varsX 317) (graphGoal 317) 7 := by
  have h := lift_ok (u := true) (ms := ([96, 33, 98, 99, 100, 101]).map swapRows ++ fixRows 0 0)
    (raw := varsX 317) (T := graphGoal 317) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low91
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior504 : Lower true (varsX 504) (graphGoal 504) 6 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 84, 118]).map swapRows ++ fixRows 80 0)
    (raw := varsX 504) (T := graphGoal 504) (xs := [(inputs.getD 4 zero,64,80), (inputs.getD 6 zero,8,72)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,64,80), (inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior492 : Lower true (varsX 492) (graphGoal 492) 6 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 84, 118]).map swapRows ++ fixRows 68 0)
    (raw := varsX 492) (T := graphGoal 492) (xs := [(inputs.getD 2 zero,64,68), (inputs.getD 6 zero,4,68)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68), (inputs.getD 6 zero,4,68)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior489 : Lower true (varsX 489) (graphGoal 489) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 101]).map swapRows ++ fixRows 192 0)
    (raw := varsX 489) (T := graphGoal 489) (xs := [(inputs.getD 6 zero,1,65), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior488 : Lower true (varsX 488) (graphGoal 488) 5 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 84, 118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 488) (T := graphGoal 488) (xs := [(inputs.getD 6 zero,8,72)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,8,72)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior485 : Lower true (varsX 485) (graphGoal 485) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 84, 118]).map swapRows ++ fixRows 68 0)
    (raw := varsX 485) (T := graphGoal 485) (xs := [(inputs.getD 2 zero,64,68), (inputs.getD 6 zero,1,65)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68), (inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior481 : Lower true (varsX 481) (graphGoal 481) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 84, 118]).map swapRows ++ fixRows 64 0)
    (raw := varsX 481) (T := graphGoal 481) (xs := [(inputs.getD 6 zero,1,65)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior476 : Lower true (varsX 476) (graphGoal 476) 6 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 136 0)
    (raw := varsX 476) (T := graphGoal 476) (xs := [(inputs.getD 3 zero,64,72), (inputs.getD 7 zero,4,132)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 3 zero,64,72), (inputs.getD 7 zero,4,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior473 : Lower true (varsX 473) (graphGoal 473) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67]).map swapRows ++ fixRows 144 0)
    (raw := varsX 473) (T := graphGoal 473) (xs := [(inputs.getD 4 zero,1,17), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior469 : Lower true (varsX 469) (graphGoal 469) 6 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 132 0)
    (raw := varsX 469) (T := graphGoal 469) (xs := [(inputs.getD 2 zero,16,20), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior468 : Lower true (varsX 468) (graphGoal 468) 5 := by
  have h := lift_ok (u := true) (ms := ([33]).map swapRows ++ fixRows 128 0)
    (raw := varsX 468) (T := graphGoal 468) (xs := [(inputs.getD 7 zero,4,132)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,4,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior465 : Lower true (varsX 465) (graphGoal 465) 5 := by
  have h := lift_ok (u := true) (ms := ([16]).map swapRows ++ fixRows 128 0)
    (raw := varsX 465) (T := graphGoal 465) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior461 : Lower true (varsX 461) (graphGoal 461) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67]).map swapRows ++ fixRows 132 0)
    (raw := varsX 461) (T := graphGoal 461) (xs := [(inputs.getD 2 zero,64,68), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,64,68), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior457 : Lower true (varsX 457) (graphGoal 457) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 67]).map swapRows ++ fixRows 128 0)
    (raw := varsX 457) (T := graphGoal 457) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior441 : Lower true (varsX 441) (graphGoal 441) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 101]).map swapRows ++ fixRows 144 0)
    (raw := varsX 441) (T := graphGoal 441) (xs := [(inputs.getD 4 zero,1,17), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,1,17), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior440 : Lower true (varsX 440) (graphGoal 440) 5 := by
  have h := lift_ok (u := true) (ms := ([33, 50, 84, 118]).map swapRows ++ fixRows 16 0)
    (raw := varsX 440) (T := graphGoal 440) (xs := [(inputs.getD 4 zero,128,144)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 4 zero,128,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior433 : Lower true (varsX 433) (graphGoal 433) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 118]).map swapRows ++ fixRows 32 0)
    (raw := varsX 433) (T := graphGoal 433) (xs := [(inputs.getD 5 zero,1,33)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior429 : Lower true (varsX 429) (graphGoal 429) 6 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 101]).map swapRows ++ fixRows 132 0)
    (raw := varsX 429) (T := graphGoal 429) (xs := [(inputs.getD 2 zero,128,132), (inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,128,132), (inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior425 : Lower true (varsX 425) (graphGoal 425) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 101]).map swapRows ++ fixRows 128 0)
    (raw := varsX 425) (T := graphGoal 425) (xs := [(inputs.getD 7 zero,1,129)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior421 : Lower true (varsX 421) (graphGoal 421) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 84, 118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 421) (T := graphGoal 421) (xs := [(inputs.getD 2 zero,128,132)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior405 : Lower true (varsX 405) (graphGoal 405) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 405) (T := graphGoal 405) (xs := [(inputs.getD 2 zero,16,20)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,16,20)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior397 : Lower true (varsX 397) (graphGoal 397) 5 := by
  have h := lift_ok (u := true) (ms := ([16, 67, 118]).map swapRows ++ fixRows 4 0)
    (raw := varsX 397) (T := graphGoal 397) (xs := [(inputs.getD 2 zero,128,132)])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low82
  have card : (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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
theorem prior496 : Lower true (varsX 496) (graphGoal 496) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 65, 98, 115, 101, 118]).map swapRows ++ fixRows 0 0)
    (raw := varsX 496) (T := graphGoal 496) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prior484 : Lower true (varsX 484) (graphGoal 484) 4 := by
  have h := lift_ok (u := true) (ms := ([16, 65, 66, 99, 116, 117]).map swapRows ++ fixRows 0 0)
    (raw := varsX 484) (T := graphGoal 484) (xs := [])
    (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low45
  have card : (([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 0 := by
    decide +kernel
  rw [card] at h
  exact h

def generatedKnown : List (Nat × Nat) := [(381,10), (508,9), (445,9), (444,8), (505,8), (501,8), (500,7), (497,7), (493,8), (477,8), (437,7), (413,7), (380,7), (377,7), (373,7), (365,7), (317,7), (504,6), (492,6), (489,6), (488,5), (485,6), (481,5), (476,6), (473,6), (469,6), (468,5), (465,5), (461,6), (457,5), (441,6), (440,5), (433,5), (429,6), (425,5), (421,5), (417,4), (409,5), (405,5), (401,4), (397,5), (393,4), (496,4), (484,4)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem generatedPrior : Known true generatedKnown := by

  intro e h
  simp only [generatedKnown, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prior381
  · exact prior508
  · exact prior445
  · exact prior444
  · exact prior505
  · exact prior501
  · exact prior500
  · exact prior497
  · exact prior493
  · exact prior477
  · exact prior437
  · exact prior413
  · exact prior380
  · exact prior377
  · exact prior373
  · exact prior365
  · exact prior317
  · exact prior504
  · exact prior492
  · exact prior489
  · exact prior488
  · exact prior485
  · exact prior481
  · exact prior476
  · exact prior473
  · exact prior469
  · exact prior468
  · exact prior465
  · exact prior461
  · exact prior457
  · exact prior441
  · exact prior440
  · exact prior433
  · exact prior429
  · exact prior425
  · exact prior421
  · exact prior417
  · exact prior409
  · exact prior405
  · exact prior401
  · exact prior397
  · exact prior393
  · exact prior496
  · exact prior484

def generatedSamples : Array (Bits × Bits) := #[(BitVec.ofNat 152 (proofWord80 [(pn 142 979410122191142968), (pn 283923 205609320881386303)]), BitVec.ofNat 152 (proofWord80 [(pn 1181 240420538731987016), (pn 19562 772164936340623637)])), (BitVec.ofNat 152 0, BitVec.ofNat 152 0), (BitVec.ofNat 152 (proofWord80 [(pn 1033 71737711573862336), (pn 18299 495066805860093388)]), BitVec.ofNat 152 (proofWord80 [(pn 3569 90638137315035593), (pn 365494 600384294511494476)])), (BitVec.ofNat 152 (proofWord80 [(pn 3542 280110251060525063), (pn 906759 510265335871639055)]), BitVec.ofNat 152 (proofWord80 [(pn 162 583430351040845952), (pn 910439 58965261726322186)])), (BitVec.ofNat 152 (proofWord80 [0x38001f8070078000, (pn 18816 911818940432257008)]), BitVec.ofNat 152 (proofWord80 [(pn 489 192320966682841090), (pn 692306 382774555536001696)])), (BitVec.ofNat 152 (proofWord80 [0x3e00780000007, (pn 1190043 406324496416632832)]), BitVec.ofNat 152 (proofWord80 [(pn 3378 541906008914207511), (pn 278917 193335417297608704)])), (BitVec.ofNat 152 (proofWord80 [0x3ffc00000007fff8, 0x7e0003fffe000000]), BitVec.ofNat 152 (proofWord80 [(pn 664 83523765647337012), (pn 151124 806711789465108480)])), (BitVec.ofNat 152 (proofWord80 [(pn 4717 754796885577039872), 0x7ffffc0000000000]), BitVec.ofNat 152 (proofWord80 [0x2944449144420, 0x5e49280000000000])), (BitVec.ofNat 152 0, BitVec.ofNat 152 0)]

def generatedColumns : List ColumnInfo := [(128,0,381,0,10), (1,0,508,0,9), (64,0,445,0,9), (65,0,444,0,8), (4,0,505,0,8), (8,0,501,0,8), (9,0,500,0,7), (12,0,497,0,7), (16,0,493,0,8), (32,0,477,0,8), (72,0,437,0,7), (96,0,413,0,7), (129,0,380,0,7), (132,0,377,0,7), (136,0,373,0,7), (144,0,365,0,7), (192,0,317,0,7), (5,0,504,0,6), (17,0,492,0,6), (20,0,489,0,6), (21,0,488,0,5), (24,0,485,0,6), (28,0,481,0,5), (33,0,476,0,6), (36,0,473,0,6), (40,0,469,0,6), (41,0,468,0,5), (44,0,465,0,5), (48,0,461,0,6), (52,0,457,0,5), (68,0,441,0,6), (69,0,440,0,5), (76,0,433,0,5), (80,0,429,0,6), (84,0,425,0,5), (88,0,421,0,5), (92,0,417,0,4), (100,0,409,0,5), (104,0,405,0,5), (108,0,401,0,4), (112,0,397,0,5), (116,0,393,0,4), (13,0,496,0,4), (25,0,484,0,4)]

def genData5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [(pn 3141 105445899704959280), (pn 874339 613948703151322080), (pn 119568 138800846908026892), (pn 835390 862995680570869336), (pn 261142 560883509249124891), (pn 785250 663493890219707859), (pn 171241 899098139145988498), (pn 157153 497841442326120720)])

def genData6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xa1060a8, (pn 227269 832589540483678290), (pn 618714 635279692506071040), (pn 325862 4423056057958400), 0x2c0820000000580a, (pn 567583 256717950766284802), (pn 210182 201975846631114369), (pn 18889 489294451529548800), 0x2aac9f8, (pn 7387 707062963234966000), (pn 207880 409255140699172908), (pn 24248 174980571058671584), (pn 1190326 894493736768892932), (pn 198194 106710774041813080), (pn 49297 700775046753109536), (pn 313005 577047978819489529), (pn 1040011 819401471685062253), (pn 858063 421464191646255463), (pn 60387 16178534144514797), (pn 438802 315812691856479770), (pn 894105 225610416722846612), (pn 314079 995949791187350164), (pn 992033 346175385450157094), (pn 620109 928473464650833555), (pn 625248 666243569894573445), (pn 682677 122062513312580809), (pn 80100 742957933579748312), (pn 397670 978308641638142162), (pn 549292 320370492199950148), (pn 949508 34505071187473475), (pn 874311 448118686269732060), (pn 1171327 698907476754948103), (pn 250452 661772024913187620), (pn 318690 68246070782135792), (pn 496312 17355726081070924), (pn 161829 327338975974919632), (pn 246805 138405712628584717), (pn 251998 188073535942156690), (pn 1057943 40975557854572637), (pn 90393 891035601078279313), (pn 61172 146891414921556944), (pn 719203 114236916548391808), (pn 136139 584260615279051420), (pn 1001379 945230740555518003), (pn 545440 626631478252129793), (pn 708886 767681345086701959), (pn 381664 33676532120629828), (pn 235374 211832300514101086), (pn 375748 779354169425563229), (pn 318106 106656357518478706), (pn 322002 14747516205600959), (pn 30846 937506565173353024), (pn 1043704 138380816454022337), (pn 237376 112428366152665360), (pn 884384 772688480693312602), (pn 310738 235719379417831750), (pn 48464 508951731600105933), (pn 78791 704267833213207229), (pn 274895 470789655652493859), (pn 548075 988163668883656757), (pn 42809 76209370338174018), (pn 893012 132090615989727976), (pn 119351 241510884586054808), (pn 310736 606002931837252372), (pn 616812 587895167401605620), (pn 1098416 626225367095550692), (pn 1016564 113841227717642515), (pn 171231 634626383945961737), (pn 573368 794805058679461801), (pn 438132 440098644191975517), (pn 90393 819524572787200145), (pn 42435 183253478286042097), (pn 759822 844687223924097943), (pn 458422 649695870971376716), (pn 684906 704379071463310370), (pn 1169494 37209184842677909), (pn 719516 631895063335952756), (pn 361575 702606102681170500), (pn 253835 938202812826046218), (pn 458964 869832171937302100), (pn 261142 560894945901731122), (pn 321960 654172046257361077), (pn 106630 488149181562903137), (pn 968810 69210146580694029), (pn 312933 5070353328032016)])

def genIndex6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x1e3c4287f0af822c, (pn 285573 28255397370943360)])

def genData7 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (proofWord80 [0x1844c910, (pn 754923 995883343434979421), (pn 90393 837495455098112079), (pn 1050090 439549899527303401), (pn 690078 822799805071501295), (pn 183059 167531642572535053), (pn 78504 484248827741861777), (pn 458422 649765934793909384), (pn 377095 350901993780202606), (pn 576463 148035415841326119), (pn 1110664 168584370666742069), (pn 42807 952036458441872373), (pn 719514 398110123704230500), (pn 643714 581925606552369867), (pn 1135905 689593870427964228), (pn 188510 287121044320642360), (pn 253994 417016766023148051), (pn 1159707 679154349391641618), (pn 1098103 534088400749529594), (pn 951269 454191118405993795), (pn 321857 286889113241058598), (pn 109883 295958545327372578), (pn 94107 814878122669355612), (pn 49705 927054060770055177), (pn 1052099 683652040144815569), (pn 237375 296585980927640703), (pn 1086572 386669375405099161), (pn 160892 471519156698759154), (pn 511095 41268364223831188), (pn 42497 348963326870157606), (pn 138189 469904710361049220), (pn 603957 375617930056471297), (pn 872022 700296492629131839), (pn 1143626 571674044258682704), (pn 992158 114295651493945337), (pn 28692 851115159030165034), (pn 134580 965266958691855558), (pn 1089116 671877990510171394), (pn 300813 42368807823630708), (pn 964876 43699348443373855), (pn 1027207 768268440589025448), (pn 495931 447693791209754604), (pn 788759 223348500054955828), (pn 615082 648842698377131599), (pn 615624 417482948452524577), (pn 150399 620617524972561346), (pn 219166 90427908570034319), (pn 1117116 426756255992832087), (pn 324883 490880308847869700), (pn 742302 498734548036487570), (pn 160435 113067533893052034), (pn 718545 107399076338797840), (pn 1192582 752140578341335632), (pn 95416 67630876114456828), (pn 250531 163934225635845353), (pn 690087 882439098668169126), (pn 531296 802157290404722121), (pn 79663 138650389443498368), (pn 364565 616195238732137608), (pn 525451 146665263077300336), (pn 349937 166198560856884279), (pn 766808 247604995576043561), (pn 61701 858323209029688230), (pn 342538 970006018407381604), (pn 644148 261118325314874140), (pn 313660 519355737916650052), (pn 243993 938724106418840791), (pn 321361 935064482137088535), (pn 989705 708395644782277666), (pn 30849 821352185553816552), (pn 952784 138595058070379779), (pn 321999 673357903329621092), (pn 242109 557512842678147362), (pn 111889 938162180951290497), (pn 880214 666581080148054795), (pn 806538 265852671937831133), (pn 237375 864600042410640749), (pn 477092 17625633984669369), (pn 160947 91662538279124594), (pn 57302 831220673096994961), (pn 47090 812729984504764734), (pn 5944 762735387302455428), (pn 1191885 96187958204859657), (pn 876627 608959602973229694), (pn 236489 458057350725403472), (pn 684926 692175569041308889), (pn 198583 977190129263552584), (pn 627620 862754130560269483), (pn 68937 938038959954670658), (pn 522756 813540224069689972), (pn 343884 848947037275832603), (pn 1026119 698321938554896814), (pn 647044 905155898115153417), (pn 618724 666506151945384740), (pn 318485 949135966222292237), (pn 609352 678895537302348389), (pn 797272 176771116143666882), (pn 672504 172689014685241534), (pn 59332 691764888196091344), (pn 246797 417946660437777222), (pn 416587 491942600022616218), (pn 157264 933618915884642096), (pn 876264 768168349467791665)]) else (proofWord80 [0x878a1d4, (pn 638001 85745883188199449), (pn 719658 326472797487386753), (pn 198419 92377820237267646), (pn 44717 159542792533528583), (pn 1057814 678840126877501428), (pn 669694 994917148218492577), (pn 161147 411262948510005810), (pn 347140 524117203371446481), (pn 75129 239834352064205940), (pn 912657 580874634635921543), (pn 1153661 114180993047692008), (pn 723151 553844370915738618), (pn 179636 277570407957083212), (pn 685036 601361191716125955), (pn 548039 94697214379959880), (pn 641970 460180381324683546), (pn 191562 960964481375740995), (pn 1157870 564991465054085380), (pn 343885 343735860479803898), (pn 699575 561102170341548072), (pn 495994 173508757285305514), (pn 127072 207596474341856036), (pn 320874 783812783267787985), (pn 166764 479589531217627777), (pn 1053516 904494832865453242), (pn 218566 785870316406640879), (pn 232505 541210851633159443), (pn 171254 718481605247661972), (pn 630220 81741637224393234), (pn 159921 991938742071044838), (pn 272279 168801271196207408), (pn 1125864 339832938649428829), (pn 85385 634218134389164150), (pn 1006403 863587963948542059), (pn 690089 955696975846587194), (pn 636230 961705891944412421), (pn 155432 25342308010161040), (pn 458422 650046986657129608), (pn 527982 957508703156813902), (pn 500905 320301430537602103), (pn 1090870 812193288891011133), (pn 42812 554714307086130161), (pn 638717 659068373196610180), (pn 644303 702594362519976128), (pn 757535 298666411787891268), (pn 263698 566745789312951320), (pn 197403 282871829756225563), (pn 1102714 165359600823585850), (pn 625869 173636623601044978), (pn 954808 344498252082974018), (pn 359927 277108953258325476), (pn 1022190 370853347677018662), (pn 130963 839796928002337032), (pn 181268 114762795841261837), (pn 1033187 184631603705497098), (pn 544551 873882611539117799), (pn 670948 850023330740899481), (pn 161039 756115474884280050), (pn 208863 732907479107326161), (pn 61294 544901548411910518), (pn 43751 656318145739122950), (pn 585067 920738605983678210), (pn 723261 810116196300030781), (pn 844936 171619685005886096), (pn 1001380 836124354406751954), (pn 669601 916528585091557480), (pn 634855 223394080977058987), (pn 69251 840632831593358402), (pn 1201589 501427771656522100), (pn 306087 687355977000165759), (pn 269286 237440154280212904), (pn 342481 972885615725821788), (pn 618788 77747828239963940), (pn 316342 226602904491368009), (pn 549059 342324208327299617), (pn 596662 372739969550065858), (pn 180806 191820070978662590), (pn 890662 457831818603483604), (pn 246798 606879371454603094), (pn 378809 406757734288722338), (pn 479264 364020477690083104), (pn 912162 240730151416792384), (pn 895711 699374499494860129), (pn 997088 233731220643809373), (pn 1012144 263137086667427434), (pn 85618 236797062341995511), (pn 154679 302416227917641161), (pn 78799 629898910893733777), (pn 439513 620268177314997384), (pn 414800 266082822899026510), (pn 507988 843040707006516267), (pn 1110513 137556119177463605), (pn 949503 456105497473848815), (pn 691256 508205263642952424), (pn 724140 650231881188177865), (pn 219766 591951929831661900), (pn 207177 743191916886582498), (pn 550252 590038171436787733), (pn 1055806 339151719969221538), (pn 474751 707796115033230047), (pn 954774 220758622861135218), (pn 321914 70806515687948004)])) else (if j<3 then (proofWord80 [0x484548c0, (pn 1133939 834307637729574656), (pn 384579 18686657860989116), (pn 9474 731462864581431041), (pn 1133516 7525390861004831), (pn 2073 678281636802658800), (pn 33250 335323642813743493), (pn 912967 555933959897739452), (pn 10648 404066777074768259), (pn 1133517 189718075747965002), (pn 74379 585272092020802544), (pn 28759 127352850358222343), (pn 907286 247288795302191228), (pn 8447 559540660054531846), (pn 1060097 652177470936564876), (pn 146520 252160330682140545), (pn 794519 741095970899783183), (pn 613613 2228651503698416), (pn 519603 284435629436510983), (pn 914815 400951201575065654), (pn 36600 111322754832121876), (pn 122887 689734909203977801), (pn 349745 660477520473948226), (pn 325960 946144156595523890), (pn 416730 417976795318714636), (pn 661666 722784677560787719), (pn 457333 912954427028863007), (pn 1518 436149520326742819), (pn 37206 515061997678682360), (pn 146399 727392805567266904), (pn 381550 183481738636756192), (pn 585600 546257116243954497), (pn 1133421 25181614672453972), (pn 94534 127850247717398023), (pn 907433 676897438245769560), (pn 297684 472112632024276486), (pn 611475 773213445115240568), (pn 122891 127080952892099090), (pn 455562 666743472976857146), (pn 47562 657556660890644230), (pn 907434 474734635626963180), (pn 217371 830712850655035270), (pn 1062461 988218813336076576), (pn 322453 819760967838337559), (pn 5317 582688783969223152), (pn 42644 675022801930839053), (pn 919689 808390534951146436), (pn 661629 653612129853404252), (pn 25995 937152081676140688), (pn 415920 177651024178207746), (pn 27159 377480229499666928), (pn 40271 672113853932805667), (pn 641670 875034361783413451), (pn 203590 653249232824858793), (pn 201312 377895991125907818), (pn 437580 883102204315216112), (pn 771415 926499618574133892), (pn 47447 911614562444111783), (pn 824612 296339830225149266), (pn 546203 887638079821777338), (pn 787576 438570610759982745), (pn 464634 971711648359407593), (pn 572104 192690787077694828), (pn 705003 684430182673001037), (pn 43389 385835262559982500), (pn 295459 356652827867254554), (pn 280554 919338343971342553), (pn 771157 822971867281142410), (pn 463516 567479054408753352), (pn 600366 329595654742614394), (pn 631212 204263571525501456), (pn 492216 840030203406721952), (pn 550181 781589979410235457), (pn 1206121 274947649528399852), (pn 149169 470405450340982909), (pn 122549 199565227696975719), (pn 876568 560533484936076980), (pn 578082 383580377357314532), (pn 35641 280417651573095453), (pn 1060012 883039466955241145), (pn 1029022 82862141108774742), (pn 138469 694520519561117299), (pn 688529 852464177955326119), (pn 132749 719718443665005590), (pn 530117 921473041798218172), (pn 32735 743700904589058331), (pn 549818 589148520841506137), (pn 854874 189662452232455884), (pn 732601 808365184490340459), (pn 1103544 666855522439376166), (pn 845796 72019028814633586), (pn 499125 544837907097387427), (pn 786469 593955813732799128), (pn 965167 769600796057426825), (pn 480012 29085279832900919), (pn 701609 307871438093635147), (pn 1063286 796825396092408996), (pn 311986 342438157385109458), (pn 292509 40037241911062750), (pn 922734 763503326981199627), (pn 1190893 25487004995430792), (pn 765069 57455458973164100), (pn 646265 731524164175002143)]) else (proofWord80 [0x211520224606089, (pn 76912 567329624976425250), (pn 114598 97384281175823390), (pn 618945 334704794786427481), (pn 100652 786756202651797606), (pn 20520 567331651657515457), (pn 108712 722472952836227890), (pn 7115 905415006888415494), (pn 38152 605119484813541648), (pn 119338 934782885538236420), (pn 399151 232894968003584193), (pn 869487 718488611561243217), (pn 911511 297919555735749125), (pn 77338 65753464125014403), (pn 1059009 383015080112308675), (pn 386355 561802738991040009), (pn 36626 154496359743455490), (pn 422066 297645108963612048), (pn 345919 511452045747160513), (pn 31093 181014894399230984), (pn 125170 545951872101254184), (pn 403781 395212801215373698), (pn 49616 78211448758616800), (pn 306973 736376678173660096), (pn 77215 783575328506610945), (pn 1059025 289731642373473692), (pn 153526 516646942331027823), (pn 1188 956195021142444804), (pn 228519 781093696459555488), (pn 510512 490463893813018689), (pn 756789 235256233023361107), (pn 906954 61449805785137223), (pn 38228 356776902700631641), (pn 24094 78573320259244098), (pn 775053 791277623607820838), (pn 81470 949866648877068384), (pn 631771 278795822868862768), (pn 456156 870079935758655554), (pn 14296 767378805865836546), (pn 1133400 346322600208744833), (pn 913796 361179397235966639), (pn 867 5697293049732120), (pn 480519 976942307423291142), (pn 33167 752222411735464960), (pn 304684 943932278161677280), (pn 311677 197828357884675589), (pn 117473 642038587988932624), (pn 567846 131955872648425345), (pn 38185 56803308984582584), (pn 79099 820425318585655363), (pn 7194 518480766261819408), (pn 566983 737535555205857280), (pn 52020 971332790017601632), (pn 302231 470735525994043932), (pn 132671 7763746493924609), (pn 186 201357449848509714), (pn 842140 568806309757075873), (pn 397057 269634638852220991), (pn 2958 996972586360260673), (pn 1002729 448445072925345864), (pn 686263 17662247288177921), (pn 265791 160160895528726537), (pn 34343 248880124095439494), (pn 760227 398532994959706389), (pn 180789 740546594762939525), (pn 988618 987040448605880464), (pn 137373 27071553553339680), (pn 639316 325589767456887520), (pn 779901 70417781678232904), (pn 613764 538572848366916755), (pn 160682 741030681557635634), (pn 153072 217262162188462606), (pn 613612 929044422611869928), (pn 146401 453957358180701571), (pn 1133499 752755560655677471), (pn 2073 553327348475299424), (pn 1190073 661617999727586069), (pn 623057 805702982802002264), (pn 297725 846772653468439241), (pn 310280 436074924577554752), (pn 355525 397933314565736727), (pn 7458 702143477450179056), (pn 42894 199167369317450117), (pn 388544 338150909368379592), (pn 915995 993476486703233086), (pn 36599 805359592384741396), (pn 103986 929853636068245953)])))

def genIndex7 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x1e27534, (pn 741455 204792201626657781), (pn 1068222 609987874952393184), (pn 283456 628133694885599629), (pn 955025 244838618620884993), (pn 65523 523779589658068385), (pn 297543 681178929532837398), (pn 566960 815991002133315074), (pn 1058427 281746307490443294), (pn 3836 350384749617709849), (pn 188963 868387084007638912), (pn 911349 361031860994446368), (pn 667760 462375353001365820), (pn 19275 697572713025782752), (pn 25816 237645193877686148), (pn 1111918 840336716522801199), (pn 292199 963180788806437927), (pn 302353 700612367957889217)])

def genData8 (j : Nat) : Nat := if 11 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then (proofWord80 [0xe87d0930, (pn 755144 925152182722676032), (pn 755144 617834284712266032), (pn 755144 348691430418728256), (pn 755144 41373532405221696), (pn 755140 365312535587049760), (pn 755139 793317999251623184), (pn 754849 777282187473520912), (pn 754849 776156287566661952), (pn 754849 758159481243223328), (pn 754849 509320208667987266), (pn 754849 490160119042330928), (pn 754849 469929105091233088), (pn 754849 437225231234453810), (pn 754849 202493792355421984), (pn 754849 202266193448471841), (pn 754849 201929742890372368), (pn 754849 201385484634622768), (pn 754849 200786250797468481), (pn 754849 183387578799540496), (pn 754849 167046636987270464), (pn 754846 375940767922113808), (pn 754846 372560869178329360), (pn 754846 371437168294741296), (pn 754846 370311268387639072), (pn 754846 85438800746370370), (pn 754845 219656956756477250), (pn 754845 218531056849633602), (pn 754844 934206145999524128), (pn 754844 70116450403995952), (pn 754844 68934475404135696), (pn 754844 65612850776622384), (pn 754844 64486950869520192), (pn 754843 779630975902666048), (pn 754842 913813947539640626), (pn 754841 762019442351262019), (pn 754841 760893542444418371), (pn 754841 759751149862900529), (pn 754841 475178848896799025), (pn 754841 474615898943377218), (pn 754841 473790566408129808), (pn 1195110 129589698626653456), (pn 1195109 572269244739275024), (pn 1194822 422756992877859104), (pn 1178013 188070740361547024), (pn 1175061 97129713159394609), (pn 1050285 678953145514445379), (pn 1045842 320262736459091216), (pn 1045251 447991624912882960), (pn 1043411 584010290405425218), (pn 1036398 741344393109197072), (pn 1035751 660545731253014834), (pn 1029262 950464738301381698), (pn 1029038 489914718095527713), (pn 1000391 506207978897607746), (pn 903005 435030883757575440), (pn 903005 378735888154234128), (pn 902419 169942191012104464), (pn 902415 427450900667026704), (pn 902415 372281805231164688), (pn 902127 934539185789112626), (pn 899171 51730788567026960), (pn 899170 528750281838054672), (pn 898875 903825608945765648), (pn 898875 380845102216793360), (pn 898874 139014882191774002), (pn 892087 772822788379562288), (pn 885006 527215253697906960), (pn 885005 735144669233302800), (pn 884711 379310074076645648), (pn 884710 587239489612041488), (pn 882937 628489029021124912), (pn 865822 274229498459213072), (pn 863461 2079320032791824), (pn 828044 387201618341302578), (pn 753660 305725187596338515), (pn 753373 390328658017241667), (pn 752776 590250612306332227), (pn 752481 442345431080669490), (pn 750416 561617331049582400), (pn 750416 561356746793798996), (pn 750416 561054381096160576), (pn 750416 558801481770323281), (pn 750415 984539752722449747), (pn 750121 413712151428321088), (pn 750121 413451567172537684), (pn 750121 413149201474899264), (pn 750121 410896302149061969), (pn 750120 836634573101188435), (pn 745109 304190099939512097), (pn 736251 767975434561113682), (pn 736251 767467460189080865), (pn 736251 767412484607167825), (pn 736251 190934140117697875), (pn 735956 620071354451480352), (pn 735956 619843755544530258), (pn 735956 619544688381775137), (pn 735956 619507304985906513), (pn 735956 43028960496436563), (pn 735664 588129334747320625), (pn 717068 307641905437592848), (pn 716775 140229812234341713), (pn 679289 951077482430055763)]) else (proofWord80 [0x50d20fb, (pn 549953 722598300970717435), (pn 398985 569098926171951355), (pn 397214 681667848444387835), (pn 397067 107714769942561017), (pn 1002267 319830320029709049), (pn 1002125 222817827117150457), (pn 997835 782300582986596857), (pn 997688 352463181385908729), (pn 997688 208344702837142259), (pn 1002710 627690145778774495), (pn 563248 925128278330118367), (pn 487395 913497090973839583), (pn 459061 714599829503021279), (pn 412253 101512791381577951), (pn 412105 527560184525107935), (pn 383946 572731658304819423), (pn 383798 499160941748883678), (pn 1092131 349628131841220830), (pn 1069409 149276954458144990), (pn 1021318 560378767817720798), (pn 993851 272039231134445789), (pn 1149694 414509095338713309), (pn 1149689 523599900009906397), (pn 1074131 502247881976259037), (pn 1016725 243697692794368221), (pn 1016577 669745086814822621), (pn 998578 687338604229763293), (pn 998578 629073284050600669), (pn 998578 542941941172748765), (pn 998573 796147933269799133), (pn 997853 648612468409970909), (pn 997706 218772888724648667), (pn 1020212 183010061357101787), (pn 1020138 396033751339307227), (pn 1003379 601381855096550107), (pn 1003300 904919016462758619), (pn 1003292 123462692120117467), (pn 1002133 441541641981477055), (pn 717966 104605877861429439), (pn 717953 120728152017289407), (pn 568843 188463827639931071), (pn 567971 291575967906599103), (pn 567676 720131540605538495), (pn 567649 50015429773299903), (pn 567367 448937929525760191), (pn 567072 305817824520900799), (pn 567067 401116288362811583), (pn 493285 36507467791274175), (pn 492533 619916840211648703), (pn 492459 832940545306333375), (pn 492386 45964250401018047), (pn 492312 258987955482857663), (pn 492104 444886682453217471), (pn 417874 746734075163250879), (pn 417727 461011861558333631), (pn 417722 561095466320990399), (pn 417003 138076591631438015), (pn 416975 756190857210433727), (pn 416929 639330672882290879), (pn 416901 973999636909461695), (pn 416837 261495116187111615), (pn 416782 65378083059077311), (pn 416694 155113356678205631), (pn 416607 109539758659932351), (pn 416413 130496608490557631), (pn 416325 508462258345021631), (pn 416191 769567723762028735), (pn 416103 859302997435683007), (pn 416043 921739981666717887), (pn 415956 573580783830765759), (pn 415951 673664389038023102), (pn 1172411 435686547056574654), (pn 1020857 21602146936504510), (pn 1020801 690377125050008254), (pn 1020788 431779822071259326), (pn 1020784 104383530054656190), (pn 1020714 635796327839383742), (pn 1020189 196886191650190013), (pn 1172415 763644758235361469), (pn 1171235 749047674767749309), (pn 1096567 363699546218902205), (pn 1021447 610145382232305853), (pn 1021156 785695845101154493), (pn 1021088 475659647082115773), (pn 1021079 251724660269724349), (pn 1021014 688683352180601021), (pn 1021009 499973631358349501), (pn 1020267 595546305091158203), (pn 1097005 190142389790261435), (pn 1021447 614646783100403899), (pn 1021392 562644938073129147), (pn 1021378 727586882707472571), (pn 1021300 40694193222664379), (pn 1021157 78423224195563695), (pn 1021816 261267232929030303), (pn 1173306 102740107238523039), (pn 1173301 211830911394460319), (pn 1172434 494082623673536671), (pn 1172139 629904220576616607), (pn 1171844 491006240210620575), (pn 1171549 343664010542788767), (pn 1171549 50367084541850271)])) else (if j<3 then (proofWord80 [0x5924f924, (pn 595683 782888491329977890), (pn 704263 623821581178965024), (pn 812843 464754671329951262), (pn 1091430 444645898941984797), (pn 118588 361011735792680475), (pn 142163 659678341794473753), (pn 378250 638290122549223959), (pn 656835 24068382226252309), (pn 680409 674177058713101075), (pn 576481 77816079445778193), (pn 642558 971875100541845263), (pn 751138 812818086599471373), (pn 1029724 495652829715510795), (pn 1010795 901850745068731145), (pn 949370 549420319352314631), (pn 1142952 987015375850205702), (pn 212615 444378145295475716), (pn 363694 638062440659738370), (pn 642280 320887288473115392), (pn 495848 552636091207843728), (pn 324757 307195342390886264), (pn 254142 17933223977353079), (pn 288231 600980405081145191), (pn 250452 669093258663624545), (pn 248021 157630422163717976), (pn 551503 532366374882049880), (pn 324829 941188563326533464), (pn 253994 443945449928851288), (pn 174968 592332716002836311), (pn 324829 941187525957713751), (pn 288231 600945220709056340), (pn 552757 910958920365571924), (pn 246910 894215780912660305), (pn 329552 307663800680644433), (pn 323577 868426860353879879), (pn 250452 668953692495609560), (pn 323724 289324835898719960), (pn 174969 745108944482795218), (pn 362536 238849459922992850), (pn 250380 34881236058045912), (pn 324832 246609287062945240), (pn 173864 93109910653566423), (pn 324832 246603931104378323), (pn 329407 183249394854067667), (pn 324829 940760916454866387), (pn 174823 323239068374989784), (pn 324833 398967842723920852), (pn 253924 114744173744159700), (pn 248021 156640551256259540), (pn 173643 884534357978832888), (pn 405260 186476856866824184), (pn 178586 451183857101234168), (pn 103028 731573062136291320), (pn 27470 867846182382657527), (pn 211422 808555460705181656), (pn 552795 948506780396478424), (pn 551543 875752776221908952), (pn 405260 186441741148151768), (pn 329552 298804971205353432), (pn 253994 435078988164554712), (pn 178584 145305594798202840), (pn 103028 587422689620189144), (pn 27470 867811099949981655), (pn 329554 604646949492678615), (pn 329407 174809543599251415), (pn 324829 932321066272743383), (pn 323577 859566998814515159), (pn 250452 660215801714892759), (pn 178292 672333450635698132), (pn 216144 22078347097006035), (pn 552759 46046346305912824), (pn 178586 442176657846484984), (pn 178292 663365696430850040), (pn 99411 863690718698586104), (pn 27470 858839879705673688), (pn 590465 343819634944557016), (pn 589212 118144108984319960), (pn 552686 411956643423109080), (pn 551433 186281117462872024), (pn 362536 221123133526032344), (pn 324757 289260175225569240), (pn 250454 957052709040078808), (pn 211422 817352520293220151), (pn 27468 426667649932525351), (pn 321361 953242293927477016), (pn 321361 953232260883873559), (pn 321361 953226664541486867), (pn 23852 864805841392434961), (pn 321361 953223572097924880), (pn 253994 443866350455684880), (pn 246910 894001375139659362), (pn 324829 940900761728777810), (pn 98156 349721712082943379), (pn 23852 864383628927368563), (pn 324829 940655175434829155), (pn 551503 531797957435260243), (pn 324866 834108327524367683), (pn 551503 531691339303550163), (pn 193859 210477473143848147), (pn 175006 638034141948542163), (pn 174969 744545100170722514), (pn 288233 906079042710338452)]) else (if j<4 then (proofWord80 [0x30b83c03, (pn 17224 696893814033572112), (pn 510828 317965196064753474), (pn 306370 163320313770691743), (pn 657080 81213534169825376), (pn 416201 152064213805180431), (pn 630461 296523525393315970), (pn 269525 918902922212714178), (pn 716664 564740358972497345), (pn 848874 396888471821163968), (pn 1066086 177170308617730751), (pn 943284 328044320775919550), (pn 777981 829140331095782333), (pn 825185 173417441992956348), (pn 744887 216779936160010683), (pn 707090 558517944702931386), (pn 1051809 476458681044968633), (pn 1099014 766320518082150585), (pn 64800 725708278846732472), (pn 112007 961184530045831863), (pn 541731 421441229013317558), (pn 1056458 126917823842634166), (pn 192252 522339998528545973), (pn 621975 334068455097029300), (pn 754184 517678429791053235), (pn 928896 296661028672043186), (pn 1018606 127549486325722802), (pn 409410 907149694334524337), (pn 796631 771994186394433456), (pn 1013846 146408783392290736), (pn 107137 297910300584940207), (pn 494359 459801381536191150), (pn 881581 621732045510031021), (pn 971283 670182638933258923), (pn 1037360 915693626421032873), (pn 890927 129787680648845735), (pn 446982 958444046660783269), (pn 470556 959975002272406435), (pn 324125 119713157476098209), (pn 305198 471485903213665439), (pn 243769 227886024764271261), (pn 394851 15693183819167899), (pn 333421 772083409614124185), (pn 356998 367766916485324439), (pn 168063 283534936021506709), (pn 234140 529085506833859475), (pn 470224 913554631329688977), (pn 366294 371599031072705935), (pn 517378 105030499139195277), (pn 710958 597060620857384843), (pn 862040 384847988098999433), (pn 885616 980551286934492807), (pn 1206704 610269994861094022), (pn 21354 89302180025889412), (pn 87432 631909234730242690), (pn 196011 824304186877583488), (pn 347092 963612790951437438), (pn 668179 944773569514102908), (pn 564249 402808072897479034), (pn 502822 104773129680775800), (pn 653902 595523804239692150), (pn 804985 31869101147241588), (pn 1041069 416367913966986610), (pn 1107146 661898692815053168), (pn 1173223 258901229868122479), (pn 30374 36299033049134189), (pn 53949 334935951330984810), (pn 1031438 123424739475659624), (pn 842506 281824073439188838), (pn 696073 793024091243231076), (pn 974660 124357389340320098), (pn 913233 474870479882904928), (pn 1191818 509196772413247071), (pn 303980 319290956013486173), (pn 497564 702500425767318107), (pn 563641 948031204615380057), (pn 714723 735838363519297879), (pn 950808 120337176339042901), (pn 1144392 503546646243869780), (pn 129047 824490380582357330), (pn 152623 123137194921851984), (pn 133696 474929732019718734), (pn 157272 422134475572161100), (pn 393358 103679876679263562), (pn 671943 786514619795300680), (pn 568013 893077365577667654), (pn 506584 929453368978500), (pn 317650 213773748761454402), (pn 723745 628370463904305216), (pn 789820 928316516612373054), (pn 728392 981783018565612860), (pn 1049481 908578002650502203), (pn 289148 910736463296576825), (pn 440230 698543622049476663), (pn 336300 805096471623211573), (pn 189867 19210317513320754), (pn 1124855 157881520948070960), (pn 1148431 753604611143859247), (pn 133088 371614725280991789), (pn 156663 670291227038411563), (pn 10231 181461557726523177), (pn 458825 300301027496948519), (pn 652408 386414429883187749)]) else (proofWord80 [0x41a0b850, (pn 161911 909873937155179968), (pn 756909 273130654818115073), (pn 309916 851086460834648188), (pn 170281 944260257658774561), (pn 682310 768094578458530054), (pn 312874 672324423741100327), (pn 75687 207520955697022084), (pn 274368 477981789852009026), (pn 701608 228077493415882812), (pn 11845 440987285212619104), (pn 566767 297079973422237634), (pn 911122 234926608426353179), (pn 44934 61931704430526778), (pn 345342 469673665404671754), (pn 760637 808544903567771912), (pn 689482 250924230870949906), (pn 99263 258704477991438274), (pn 1062238 104801539230019607), (pn 641114 352003801458221188), (pn 274359 272377310203184450), (pn 610081 466738504069328956), (pn 13046 786323188772291056), (pn 832243 486689660286144262), (pn 769173 335983504236776228), (pn 687228 978585391148969106), (pn 302804 170000210144789129), (pn 77775 298551629970700292), (pn 628241 949675201042235632), (pn 43350 157378119554237376), (pn 151748 105989472858805767), (pn 605799 223810323018467422), (pn 146605 768790334916284896), (pn 1002841 31708909827415048), (pn 690365 376957184060455996), (pn 113494 890223282470880641), (pn 1058254 328657695785103381), (pn 631651 110459644695877740), (pn 146596 473351882078945776), (pn 908098 554145238057356805), (pn 87087 110350057804849328), (pn 56936 272605275960938887), (pn 916746 708734729568428108), (pn 772323 962427991284451200), (pn 454611 975389339809753103), (pn 2699 432301795688405148), (pn 293211 537581610153550737), (pn 645420 310881669521118601), (pn 623680 437179436681642024), (pn 706173 938179927101606787), (pn 907435 411000476987590716), (pn 111118 782043525272979720), (pn 558181 688999688007058882), (pn 344962 487239822926737417), (pn 327066 36138875032027616), (pn 89932 876998188269965061), (pn 915550 248865308437149235), (pn 108794 564489033181114660), (pn 633868 860570684332967173), (pn 49447 953019263879569528), (pn 23945 93258592639107552), (pn 76890 902643410521230083), (pn 907361 297084395594992670), (pn 54376 401146340712794376), (pn 586293 985407961337702850), (pn 344888 118160064887795798), (pn 201085 733649252478074920), (pn 813818 17532484597451651), (pn 907435 428944447299686978), (pn 146573 496351990351334049), (pn 314593 408186992229891074), (pn 918596 858673768647749808), (pn 283388 367431091371805220), (pn 160276 282180501938657450), (pn 80946 740603029090173008), (pn 548524 6225973469779719), (pn 605978 466511028430617662), (pn 108752 802316792258380256), (pn 983952 143507027347904804), (pn 311099 168132010885655697), (pn 35470 850666012600744019), (pn 172689 753902658657059137), (pn 332246 942407375457393726), (pn 108752 806822676808360416), (pn 1021730 497640388489562404), (pn 462507 737084159230236706), (pn 949866 803221889771307968), (pn 212926 858863805948761863), (pn 605798 430964443804383310), (pn 146605 768790785711595768), (pn 416121 717140826421166816), (pn 1133497 894458851953872645), (pn 915550 106796461850665542), (pn 146642 815898468101604261), (pn 909666 744835332619402286), (pn 70849 377657118655701240), (pn 416121 734267223623698370), (pn 457781 38677457327694607), (pn 636382 764486539870286942), (pn 153740 119598442372809473), (pn 312895 765397136326788293), (pn 648007 331355153487949833), (pn 212619 681052994388985794)])))) else (if j<8 then (if j<6 then (proofWord80 [0x15a4a220, (pn 1153957 335762228399838730), (pn 993192 622659846963118320), (pn 57056 266733742924171202), (pn 911122 307812412497353254), (pn 73286 712076595399713172), (pn 364176 595372922856868549), (pn 385475 869541195011127384), (pn 141698 790923261520200769), (pn 1061653 794826144098296713), (pn 170336 137107921040556076), (pn 208174 227803517885418371), (pn 907435 121743495865843222), (pn 35422 959327280282824828), (pn 208060 867115989439259361), (pn 228964 162199837173623559), (pn 919998 528342070650770979), (pn 62659 117737733150392668), (pn 283840 862802262454735392), (pn 1135067 293229259690625219), (pn 914676 634223787414940723), (pn 54406 503289926912610490), (pn 352093 482326761901261090), (pn 306075 595979963948381262), (pn 108752 806822699543913072), (pn 1002545 883803730541156682), (pn 1066679 823002687670658449), (pn 35470 852913414367457867), (pn 165560 15260610170061121), (pn 986428 548746794578244654), (pn 70848 238014512641581464), (pn 870060 718359095575843139), (pn 233472 963226831879711028), (pn 94610 40463855730231234), (pn 911122 525111645347556900), (pn 676569 30263192639717666), (pn 274386 780363765462665027), (pn 612225 122461237734602836), (pn 141698 755408823283303217), (pn 531195 617103561977014153), (pn 170924 129344662532243504), (pn 245988 63056426916057863), (pn 919698 169751935831806524), (pn 125341 357114524344451905), (pn 456559 441928923154762782), (pn 6524 436926978750427568), (pn 662276 376940083634772555), (pn 777583 615210138850418712), (pn 137172 660191859654167428), (pn 462507 737062426712249895), (pn 79222 6166547645686452), (pn 983804 711344843843714579), (pn 35424 767672943135299800), (pn 331138 188470024338523201), (pn 1023873 135834943355139159), (pn 47562 104779445261846822), (pn 80416 509441904670081170), (pn 761667 380321457613323795), (pn 35424 119148266005844172), (pn 293137 750595578901898305), (pn 757868 920050790550769927), (pn 15667 85268646409326672), (pn 176076 775704480122339490), (pn 1059731 441097724672884242), (pn 35424 119150198282920160), (pn 501346 728596685169887492), (pn 345035 403881178900739097), (pn 54645 83714385911022048), (pn 104245 185983108165799813), (pn 613318 793754599361113119), (pn 52015 216796606747795696), (pn 491994 229703158110884104), (pn 321155 573879390171578848), (pn 624276 372378758616909859), (pn 687264 313105480077552789), (pn 649400 459860873568814016), (pn 192290 95443956797804288), (pn 618044 654323998544378882), (pn 54330 316087305447759992), (pn 21352 278682168369447392), (pn 75945 610706945680741255), (pn 920288 465283432226788932), (pn 141911 225867363949019684), (pn 737686 413950526782965906), (pn 532894 16572848782840841), (pn 473451 886203102724079660), (pn 208174 214222453842841477), (pn 915550 394747566208367697), (pn 170328 570802545976282880), (pn 1153735 796100594602114094), (pn 70847 83924694254207392), (pn 870356 515912265449540132), (pn 311100 905977243246911510), (pn 100442 695160704288523713), (pn 1058181 47651501797425693), (pn 59138 95471391230108080), (pn 908172 646874142156004865), (pn 459851 986915369272014920), (pn 141694 456634981461869040), (pn 681127 740976953428937860), (pn 613624 40974178732509984), (pn 70946 340110096505332032), (pn 685371 339988583315938817)]) else (if j<7 then (proofWord80 [0x3c0f00ac, (pn 345333 300591734101377539), (pn 781416 349181735912691820), (pn 141696 489611163647706209), (pn 1136544 693454154816301842), (pn 475817 683344903490300016), (pn 250437 839319416474509776), (pn 1059776 41967836350658063), (pn 3332 107690815204159548), (pn 9505 352703298557427952), (pn 38037 583340817833267591), (pn 919992 763704866706048286), (pn 62677 564481806864196034), (pn 350083 265414525587064579), (pn 308176 648617507802843406), (pn 30741 580708094524121106), (pn 132480 86973206259730242), (pn 1058181 48322141145155619), (pn 73305 60766254322828432), (pn 331064 256850672558457481), (pn 191407 747295721848579088), (pn 637693 614266858223280592), (pn 869035 842003933073640773), (pn 915557 450192756286310946), (pn 62677 559916398429503792), (pn 704297 879586621659808451), (pn 308441 111117184387625132), (pn 255284 545530109792469472), (pn 566751 316470928668560771), (pn 911122 234237242820014355), (pn 36649 136353492193059978), (pn 283831 657444692828980994), (pn 644940 117944694761069581), (pn 27200 341769865541050388), (pn 113549 298258879756568449), (pn 1058181 48322415416985115), (pn 35452 341943499314245738), (pn 217505 829628910326486353), (pn 228632 264925130420947236), (pn 84721 593501136092932152), (pn 108702 170688310174843129), (pn 567597 750447177334525696), (pn 767055 146757675719621676), (pn 43197 719324795257201008), (pn 586386 181675705475352996), (pn 461922 53521669394880682), (pn 649995 374130233738986432), (pn 208749 564944206843751951), (pn 630470 519340344088815788), (pn 278869 68393322067612208), (pn 1135363 523266918734899725), (pn 326450 906837940128891120), (pn 52213 879016574309566851), (pn 1064311 994547839504368670), (pn 62677 596086289813307816), (pn 889161 781101592741158401), (pn 310064 711274076104110204), (pn 208060 876264089895388129), (pn 418449 261440168956667209), (pn 927384 160424354849511598), (pn 245936 874368420846439171), (pn 907509 847692276004568595), (pn 35423 103722853504245972), (pn 435030 359179551889761473), (pn 1061727 441918193641199258), (pn 356631 558567484245508576), (pn 94828 87034089800928003), (pn 907362 236231497892785183), (pn 52015 217918653057065176), (pn 359472 495453620588186210), (pn 532894 16572849014476871), (pn 921178 552524687757326929), (pn 686062 321313302633709728), (pn 950700 335821410304007681), (pn 194839 925094219027380312), (pn 141694 171315042683109872), (pn 832243 468675512750084936), (pn 922650 246676767575171164), (pn 695507 54279041924137136), (pn 1097363 267804871223696415), (pn 52015 220174325903853880), (pn 501272 941901865270643204), (pn 647341 804889396001959947), (pn 66205 527890189653361344), (pn 1133553 983407401553500809), (pn 622787 477984610453919825), (pn 184453 867292954380927681), (pn 417268 454570409406788654), (pn 70850 543861930802831824), (pn 1021176 445810924357686409), (pn 625883 77907342229102616), (pn 113521 580819788732762050), (pn 911122 379305438448208922), (pn 652954 928096438814703944), (pn 719064 678644531488107535), (pn 3564 876155756625441012), (pn 274322 71649277260244129), (pn 985948 217540464188600853), (pn 319376 585550005771749462), (pn 106387 192188962701648448), (pn 1097584 481166851012037315), (pn 417711 968284074641988874), (pn 461325 123338382716989494)]) else (proofWord80 [0xe0161c0c, (pn 767554 70146070725272632), (pn 120513 898887818753050049), (pn 1058217 797272371618792987), (pn 35452 341927002335512880), (pn 354814 854670265141233090), (pn 609928 415553326494652170), (pn 313021 98426507481588788), (pn 94614 674702841396887712), (pn 323833 115547491941748480), (pn 758200 709601745376934948), (pn 70847 233714466140152056), (pn 416121 738843451761576067), (pn 914529 60271197740116021), (pn 96305 974464300085609408), (pn 208749 519732564125299991), (pn 36649 136355693364917398), (pn 331064 275112306264065666), (pn 663644 395723165037262853), (pn 636394 316277890677113440), (pn 1172772 363382015878664839), (pn 317310 550213750305251434), (pn 194975 465078708840106755), (pn 907583 994674449727903782), (pn 73298 272709218371289812), (pn 624497 589825376687006930), (pn 230368 425107466777932885), (pn 47894 724909595145634272), (pn 106627 410094744228728709), (pn 613318 795514445430811679), (pn 52015 217073677296363800), (pn 510588 222905444729971922), (pn 4581 720772422808901274), (pn 47313 749366972636185280), (pn 1133576 419953216288332297), (pn 622787 477984745731431478), (pn 73298 272703127506546896), (pn 359472 495453603399558290), (pn 230662 561669191622300232), (pn 18326 883089691235603024), (pn 693164 349368708854318976), (pn 379729 165500935892118543), (pn 2671 346192068584255612), (pn 208060 871657017626297169), (pn 531195 617103493258553361), (pn 174168 427887782610921840), (pn 196102 864366948042752432), (pn 988840 672547333413019137), (pn 465905 981261970372960496), (pn 510588 222905496571742386), (pn 496298 993517072887588881), (pn 475813 70568238421884968), (pn 190232 318943091639060352), (pn 341784 161397379815727142), (pn 73298 272711348062542128), (pn 501310 88225876249095685), (pn 11530 820899351558185080), (pn 26093 99973011934381025), (pn 455561 154407858992062219), (pn 23022 715432480385034278), (pn 73298 272707259840957100), (pn 718908 422809043896122371), (pn 356641 472089144221192560), (pn 586386 181693258291366083), (pn 457928 324399532167733263), (pn 632840 989624387636675745), (pn 177402 879122788533931776), (pn 844720 810172411083282494), (pn 104030 438378326928691801), (pn 115257 999530028227369482), (pn 20829 289070250906796272), (pn 52336 187859384189914309), (pn 915856 648799929185249362), (pn 161893 499335063899604864), (pn 493047 550550865406090271), (pn 52015 219189713761280548), (pn 624294 747631899989509783), (pn 91003 591721550329602296), (pn 416121 761359353944950979), (pn 156732 485193291671298344), (pn 347155 136073647685861464), (pn 492013 1498674827370251), (pn 17712 86936145573233758), (pn 108752 800058478219006528), (pn 1172920 517740239078825262), (pn 28380 404758552101699824), (pn 52196 666492624941156739), (pn 1064311 994613670683385933), (pn 166611 263130180840195968), (pn 534966 28533122844079631), (pn 2671 343213203259715644), (pn 10351 254709596649152864), (pn 566767 475425269465549636), (pn 915557 450261748491918884), (pn 682506 612102521512166716), (pn 345268 592872288042091139), (pn 309622 858901867815096508), (pn 217505 615871875770188946), (pn 79546 834217363246164500), (pn 777162 546159231604982240), (pn 113817 313205732168704270), (pn 632208 261094827342969871), (pn 2119 99053933500403896)]))) else (if j<9 then (proofWord80 [0x3c1a8b83, (pn 911122 460951082101652506), (pn 658839 367216191419020440), (pn 312211 919018228831814978), (pn 701608 228077218536912901), (pn 638912 299110066983289761), (pn 683420 595363663907033672), (pn 319376 584408653675686256), (pn 255407 30259867726577842), (pn 1059731 672610410907327518), (pn 35424 130846807753402672), (pn 624423 838036457730935460), (pn 798827 188924538037474330), (pn 49678 399236572531229632), (pn 1133574 186351401735163139), (pn 907288 413225513758780446), (pn 35422 966085753934866712), (pn 472938 706481397068466724), (pn 345702 87220639832750684), (pn 47893 22610577361715240), (pn 246006 500899885515413769), (pn 622189 81338167120998592), (pn 418285 129124694584394661), (pn 910241 985889360755595324), (pn 70849 672697883792707952), (pn 567237 461824837912007204), (pn 765924 395285727020084523), (pn 47899 434654544609452320), (pn 534407 617591229967637771), (pn 606094 343298233249372268), (pn 141809 367708009379890449), (pn 172517 776111994593090573), (pn 26169 99104972138062561), (pn 264563 708864122308563206), (pn 769172 751611504184320109), (pn 227082 491645595518636928), (pn 493195 939099186526448174), (pn 70904 684997536476479828), (pn 699981 629564040494977431), (pn 6652 523174935476048927), (pn 56748 611557190445416484), (pn 247205 539131686697375495), (pn 613318 939559127193516085), (pn 104067 577171740465584400), (pn 567663 314818051125420993), (pn 796388 319979832368177864), (pn 17739 474102121196965996), (pn 840950 795502034391795584), (pn 379711 244558452290251308), (pn 89863 448889633796424321), (pn 105296 180636428952667654), (pn 618804 145515613219148128), (pn 718907 591142370830256003), (pn 309174 68419550639048083), (pn 31334 186352668072648912), (pn 378430 992561834417724935), (pn 606240 726047345487173712), (pn 174995 307919962884293088), (pn 1002840 958662340200581123), (pn 611259 966983080459839121), (pn 33116 621013188768002733), (pn 153740 191655760595634404), (pn 425715 41652631863167684), (pn 988904 29055099247023637), (pn 48495 422959826539692512), (pn 104667 768607081618217996), (pn 329428 940817311936368800), (pn 347445 47182423301558016), (pn 910478 582000585662282754), (pn 15371 490659374125408376), (pn 21642 825041090194523585), (pn 1060024 63580891098194575), (pn 31338 779958200295052425), (pn 160837 639770782325145953), (pn 417102 72668503957593118), (pn 5935 298533949278736752), (pn 567237 470831899818723491), (pn 914529 59700521954335780), (pn 951636 533223532310003800), (pn 491902 220828728811589376), (pn 683159 787619511037900878), (pn 108752 804551538889695600), (pn 567237 452702794795484994), (pn 1062243 940676315007689872), (pn 638757 818722935128543381), (pn 172671 235100990370923393), (pn 758865 405442275813661742), (pn 6525 597117826065453424), (pn 567237 470799017458059588), (pn 310066 149893207397783594), (pn 950454 775135180756656354), (pn 435270 914663300560854535), (pn 606094 308541300370645128), (pn 255423 364762045212566177), (pn 39922 363676201565047172), (pn 310953 325823382186370104), (pn 96889 348246403799417792), (pn 189799 163303674934858503), (pn 605798 582906532527675500), (pn 141809 367738812914778761), (pn 266114 822914869340674378), (pn 693620 967791584193031352), (pn 113549 298540483935143809)]) else (if j<10 then (proofWord80 [0x92866288, (pn 435801 41378006971557004), (pn 146432 878245347782498916), (pn 454608 771744098390081860), (pn 644651 497528504157834282), (pn 63872 656541022318414165), (pn 694312 427942915616604682), (pn 617547 461880968917046299), (pn 210765 49561445746094871), (pn 10342 297585349117931626), (pn 193648 200866773717492487), (pn 620132 275994088652295192), (pn 419411 598068112594307620), (pn 345701 316315948278468772), (pn 146432 664070687937374392), (pn 83918 972303510337979232), (pn 340278 351719908841382052), (pn 113942 973392333509958244), (pn 310209 103699869860307981), (pn 307336 21914005526451971), (pn 157390 540388789966898624), (pn 662829 169746271311284640), (pn 292864 834658697448456736), (pn 494300 405352280675934424), (pn 81525 480653752339883050), (pn 636348 835443809638811410), (pn 1063274 220734036656657027), (pn 454640 5511395960463808), (pn 794723 601264763306492292), (pn 773882 567287881543190689), (pn 910408 290519989192567458), (pn 457332 941070194716639784), (pn 454197 212261941300555969), (pn 991122 234768469701195792), (pn 318858 44737083481402050), (pn 38536 501504372062110603), (pn 763116 555669376735936839), (pn 166192 916725072369300669), (pn 153744 825664735159916810), (pn 761538 486681233963296912), (pn 922216 184366281852993880), (pn 498543 482065614323326218), (pn 236175 216572491591191649), (pn 417506 78779920566002072), (pn 767518 535946911435778129), (pn 642696 981102346118928433), (pn 932107 495229060051382616), (pn 498560 630176571720884464), (pn 501322 745892130418398511), (pn 40201 311294882742118050), (pn 610695 657791494979380041), (pn 305245 308960701168511440), (pn 1001662 9949328115401240), (pn 813229 982863804799932692), (pn 307598 634452437083956494), (pn 634614 912141946838451497), (pn 57863 655523887192647966), (pn 57340 709582712388291281), (pn 416195 945008453520552524), (pn 133423 14466764662785036), (pn 247205 409020962278739589), (pn 49022 655346597668606692), (pn 146616 762608471607313928), (pn 864562 627960277904796481), (pn 618891 40890210310271168), (pn 378440 233771590393659745), (pn 531898 904930667100932158), (pn 108627 169877466600915192), (pn 378342 802474678618343844), (pn 309914 246855475879498276), (pn 82140 45938314227352512), (pn 227523 585145680550564871), (pn 605803 483945524441173080), (pn 146578 98674301703619673), (pn 248075 565666503774050826), (pn 22474 228287699291357424), (pn 52794 942496711123209347), (pn 1063131 402940728617246792), (pn 684872 506285363861323984), (pn 1106807 603860040592679972), (pn 73289 49341820552915244), (pn 643276 771824394191767050), (pn 619833 988145995059515728), (pn 586238 607756015063044772), (pn 841187 700544813716856858), (pn 122968 626709443777301252), (pn 311391 433149844825877286), (pn 66233 223976794653951318), (pn 364213 543432581141531267), (pn 327330 720035745122283580), (pn 13046 559573339273692049), (pn 380597 551407371867992086), (pn 654977 661260627433248884), (pn 869285 26496539970899844), (pn 613319 84522043858829458), (pn 323796 204062950719099399), (pn 606831 634911697576194154), (pn 217505 829640842531561864), (pn 718944 990907202185349251), (pn 914529 59700521416352808), (pn 949864 492870951586201689), (pn 532055 486355865564096015), (pn 17712 96665064477107336)]) else (proofWord80 [0x26a0e860d0c08692, (pn 682100 905497555451914350)])))))

def genIndex8 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0xf006b1563, (pn 443913 982967713958529817), (pn 45199 456450384112991232), (pn 66262 395816630219239428), (pn 819256 908736815770423114), (pn 117027 895877263466853787), (pn 990768 641610550766568352), (pn 1168053 787032884251903117), (pn 948100 713612949411016387), (pn 783556 770832893308677040), (pn 178380 672842890232098918), (pn 731244 770317160078753957), (pn 162399 697564022553240560), (pn 24238 734010308212818880), (pn 141688 290147299609628416), (pn 566748 811202674015873305), (pn 460085 694045332458947865), (pn 37705 280011302598656766), (pn 2697 812602122837968760), (pn 17711 36081395246928751), (pn 180574 601368453689784065), (pn 1060107 819404526150352667), (pn 1133474 672061646951708672), (pn 703527 15775242210762767), (pn 2213 688839829055057532), (pn 8854 741241422105870002), (pn 430718 566769437727545436), (pn 400699 23315953634302252), (pn 1005165 385651619468884993), (pn 1057998 309250175267303431), (pn 605527 633607369884418054), (pn 301936 854169039047567792), (pn 66714 433350435509895648), (pn 49631 85206926460622649), (pn 724838 493562663947042362), (pn 874841 272823494038156227), (pn 906891 753805323897447121), (pn 103744 547531798901915666), (pn 461217 990966231817851380), (pn 69797 579678049315061794), (pn 1070145 561739845224132454), (pn 342957 262577669659458561), (pn 1057814 912229912422144094), (pn 652221 28466311648755742), (pn 4427 626960480388448368), (pn 152311 169069156648353964), (pn 653850 121180214526830464), (pn 104258 695884237233604822), (pn 1016037 443615304246637715), (pn 907247 823134115714049743), (pn 486256 444028424630534204), (pn 8855 518081979424571448), (pn 962361 738936859668750272), (pn 90314 108201085680193280), (pn 566749 9360378381999211), (pn 1057838 260219749036950567), (pn 605569 791195747776501580), (pn 170311 477905240310612088), (pn 17710 670947965280775425), (pn 87769 32897519003109248), (pn 283349 464666600588838139), (pn 1133506 323359827878864002), (pn 416827 668623749152497678), (pn 349307 626405073897822836), (pn 821102 124617187990712816), (pn 35419 853825423189738432), (pn 89292 703038208852627200), (pn 566722 496284687647938621), (pn 1057925 290081045171090905), (pn 757969 797620110227149748), (pn 775404 390708781355303027), (pn 18354 591952155907740962), (pn 1166987 752738277890128684), (pn 685320 731062482409364992), (pn 1133447 37514737331956787), (pn 907247 809462400653177311), (pn 465005 794835011347852396), (pn 529348 393940642782383105), (pn 908469 973959830161850368), (pn 623352 952199626187014160), (pn 1095888 855686687357927552), (pn 16546 738546951640388096), (pn 151719 894432659011021248), (pn 764082 733770014124409098)])

def genData9 (j : Nat) : Nat := if 8 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (proofWord80 [0x2443fa3a, (pn 161147 427242062483326964), (pn 317657 517791966004564239), (pn 1049741 478785052900266534), (pn 451955 980740028154244388), (pn 945643 17140643451510746), (pn 337953 489854711435731999), (pn 833814 952659282565215564), (pn 599623 118147595927535204), (pn 720120 778677665288044404), (pn 1006804 531422304918621374), (pn 1103380 609220548847364248), (pn 594191 299042358031482133), (pn 320971 665377145597754874), (pn 134696 959027155388768379), (pn 1152940 230189992197297474), (pn 1169535 828494395629234718), (pn 613599 876959821830880212), (pn 250356 806077601414856951), (pn 794723 167863808163748515), (pn 603823 343489941248145237), (pn 33051 568170098710659054), (pn 654601 120886000348980607), (pn 1043995 498157016324981826), (pn 1207628 366336563993374314), (pn 66102 993210171491188700), (pn 704739 330838786201685759), (pn 874379 703695953875585421), (pn 1206311 871839238252125269), (pn 283321 426064007418806200), (pn 793800 130313457639196159), (pn 530398 78166001134605339), (pn 1203624 209145011304872550), (pn 415454 341439522733424244), (pn 946538 441958324507315196), (pn 1100779 469682642819630135), (pn 1179728 280614459590734924), (pn 226445 475834154919394536), (pn 644010 945899092966258681), (pn 982874 792109859948187759), (pn 1150458 972250486496618384), (pn 452890 356067257617480142), (pn 390772 255822032590122995), (pn 739114 890274469623278175), (pn 1091849 739080275764825410), (pn 905779 669551200341062554), (pn 318752 590957223195729895), (pn 231598 815981677050601919), (pn 974469 863728618784658055), (pn 602627 763887434868188957), (pn 14152 752695407535243214), (pn 239032 797557972919822719), (pn 738261 467152857208132866), (pn 1205248 439109043370307257), (pn 708308 120480681342500701), (pn 472752 790949433357928190), (pn 881467 862867679682406925), (pn 1196922 515117029109751122), (pn 132132 449534427924201146), (pn 482713 665732117041581565), (pn 551487 313863822865671483), (pn 1184892 693424773695191624), (pn 566496 214642399543950708), (pn 664376 467620543269575674), (pn 1098418 281933210314745367), (pn 1160837 589668695711249476), (pn 226297 767336251246770920), (pn 79686 997219132444260341), (pn 978724 265684942156187695), (pn 1112673 122788077920249641), (pn 452594 993114646264149454), (pn 310489 719497556228861931), (pn 737934 280621761482887263), (pn 1016272 852008652447796289), (pn 905188 725221393647528854), (pn 620979 425730604155068375), (pn 211381 148380336891777983), (pn 823206 562042395845431431), (pn 601446 19343013818390301), (pn 14143 529393722259193774), (pn 239180 299457366470723455), (pn 435716 417035897385979146), (pn 1202882 797299574824218137), (pn 670528 811581992205516636), (pn 165798 966739360553176830), (pn 869067 39140965675600277), (pn 1192181 683866856759172369), (pn 56537 444622317558365753), (pn 794389 563699879259702780), (pn 539842 804385283093320763), (pn 1175327 408086391228839970), (pn 150009 864337785200039729), (pn 663464 358094284953755486), (pn 628692 272487604675938391), (pn 1103856 750005194472386572), (pn 527494 763417972698245859), (pn 119817 876566556375807929), (pn 945390 854985748418006126), (pn 1150454 502427659027015568), (pn 1047612 576572338689472976), (pn 234784 293077776427936755), (pn 795817 875820691870851415), (pn 1016798 836417981503100977)]) else (proofWord80 [0x1c5e9c3d, (pn 132846 247341972432296899), (pn 735252 314363096739060572), (pn 128843 243359916854483678), (pn 730954 157972184870722151), (pn 124213 39946135729936871), (pn 726360 848609492527716708), (pn 119361 468284974663342272), (pn 720918 974382504595724363), (pn 114288 537383839075604421), (pn 716141 193638330992793398), (pn 108957 349250853065332402), (pn 711178 943201663431251505), (pn 104364 40451119266076079), (pn 706327 378858972021101856), (pn 99143 532782592692982940), (pn 701069 974324555358311439), (pn 94291 962247305764213627), (pn 695960 149935237990421250), (pn 89292 820574307777647230), (pn 691329 948210323905745423), (pn 84736 402447928680583549), (pn 686699 742544691426988304), (pn 80032 413183804164542618), (pn 682475 373693067300474925), (pn 75918 725922505022181295), (pn 677882 63204440690364198), (pn 71104 53942069714751156), (pn 673473 225223203838135875), (pn 66953 473755616056774105), (pn 669470 220115239763676518), (pn 62765 996703220768705762), (pn 664803 121524392638188621), (pn 57471 699806573772737455), (pn 659176 780419651924495160), (pn 52583 239723883590716092), (pn 654731 46698373347445277), (pn 47252 45961346505312659), (pn 649252 280672096446810380), (pn 42252 906540156922628252), (pn 644732 759974591753521185), (pn 37844 64055225951782807), (pn 639881 191691173359093522), (pn 32881 815870366794253962), (pn 634882 46077439797659131), (pn 27698 201689979050329463), (pn 629809 116865205609530626), (pn 23215 575043563139105932), (pn 625510 959348411013956625), (pn 18806 735936400608789387), (pn 620770 73781277641507602), (pn 14065 850932242960614052), (pn 616582 600106685154755131), (pn 10247 317768718689436121), (pn 612800 959305374034919778), (pn 5986 54302987106517226), (pn 608429 10871566207320177), (pn 1798 580628411799765013), (pn 604467 519833216482579215), (pn 1201925 892715100770375976), (pn 151056 154117321785867892), (pn 362440 736518219483910140), (pn 1089123 433249339357079679), (pn 1179507 946501892237841232), (pn 906438 21508554334141574), (pn 682379 945077399372587000), (pn 987878 469100032785403071), (pn 1138284 157164379874977945), (pn 603711 548384382923306445), (pn 316392 675474687776587755), (pn 691273 241415793376403583), (pn 1015402 180098379933401394), (pn 1207349 314295929111570974), (pn 321108 306833098247077844), (pn 269396 151842066576261887), (pn 795313 499684219644418625), (pn 1205694 257192386575717420), (pn 925558 549193313917927336), (pn 342518 946171965766525439), (pn 379303 102991828786562251), (pn 1202324 632419692697331290), (pn 37727 217169077228404556), (pn 694482 616839033226331134), (pn 720827 274051431178733975), (pn 1195373 245317130024338705), (pn 75417 396593794239167617), (pn 765611 202866407142885367), (pn 539608 749660053202587919), (pn 1126386 475592589239884130), (pn 150466 133025425814714132), (pn 322296 367693602776748012), (pn 1102829 328084076020228639), (pn 1028536 333954392163500868), (pn 300767 686505793015770151), (pn 644591 583666365505224664), (pn 363935 718859383321674815), (pn 810441 703350180785087624), (pn 601294 412416674376439051), (pn 80255 462812120433049513), (pn 690092 499155454329032959), (pn 384075 621597028640117520), (pn 1202479 912031558446327970), (pn 160510 87954709118222161)])) else (if j<3 then (proofWord80 [0xc241e1a1, (pn 383414 472313345949767700), (pn 43820 692177831107506312), (pn 549792 546407774399304463), (pn 52075 222082580313572472), (pn 473569 148605712285763270), (pn 10953 988527111344430358), (pn 92289 657121576161755180), (pn 644388 27655055613173011), (pn 71038 916078821570556048), (pn 625497 691365487782823365), (pn 11253 779660961263263004), (pn 108790 179413236274806828), (pn 492828 990008794322766087), (pn 3276 693305330556752956), (pn 170521 902351596457677217), (pn 79995 490134550102872713), (pn 39075 86485356486347846), (pn 170541 883145307765649793), (pn 307405 799373276304382978), (pn 935121 140800190724239504), (pn 529109 839414123771217475), (pn 917351 983572745040698648), (pn 80557 581859323164786804), (pn 454605 894572036799694162), (pn 1069955 120944274862026864), (pn 66520 405712481154467011), (pn 919713 167966485313102362), (pn 71020 469264653992892536), (pn 492458 614537189792777442), (pn 992321 926169964097250074), (pn 118466 527448162705639302), (pn 631685 891025350617487440), (pn 369195 811625418783131392), (pn 1065510 546433647684631592), (pn 132277 514036972716400928), (pn 1136327 508514844606826567), (pn 331852 585191975192645166), (pn 156374 350502302929002881), (pn 308000 140581789142625308), (pn 15454 126014061205332208), (pn 757645 473412083970622595), (pn 918532 574107231067063324), (pn 113633 27454947452813408), (pn 283934 302966117742838145), (pn 307856 608587423170430983), (pn 22500 614735027331144728), (pn 108891 924871590601339024), (pn 530311 334502340545888705), (pn 611268 655111789100799252), (pn 89928 528344721460834340), (pn 132614 726550781794743392), (pn 322230 327436452959469953), (pn 531569 449971161978963975), (pn 22472 872113066589429788), (pn 113725 550542955462303888), (pn 530682 7808633943000642), (pn 765055 760519056604531210), (pn 42630 859522523126572168), (pn 511941 270423598377540889), (pn 108891 924872076206309492), (pn 473717 881127005588080775), (pn 328301 677629158814970032), (pn 529165 973393637279777473), (pn 907366 834371249382626835), (pn 71038 916042809667514464), (pn 435567 699486642660344257), (pn 610978 136977837558204679), (pn 28440 538667600287657064), (pn 473734 160786463737386767), (pn 52075 231902108732116028), (pn 208300 799034041714418306), (pn 160000 244413761024042264), (pn 37908 402403607146931228), (pn 99410 298417563219018804), (pn 208300 760887286707605680), (pn 529055 294923782184436802), (pn 914961 404166489528342287), (pn 52038 310720494567977036), (pn 284155 87610754368808854), (pn 790980 777995686097889055), (pn 184350 343248846161782437), (pn 786498 150223335919429156), (pn 179683 245783950484186540), (pn 781978 628962872682259763), (pn 175237 511499756314895537), (pn 777274 638009812405298222), (pn 170349 48602282004718500), (pn 772349 281061249312662305), (pn 165460 588519643362042531), (pn 767571 500880068613743132), (pn 160609 21362167824916896), (pn 762719 934848501573132565), (pn 155720 560153586325201049), (pn 757942 155793263731646500), (pn 151459 297250821876096946), (pn 753791 575043842940772167), (pn 147308 715938476901474009), (pn 749751 675884781493526122), (pn 143231 922165342358216180), (pn 745564 201647230463024513), (pn 138896 871723358887025927), (pn 741118 466800026209721470)]) else (proofWord80 [0x94744838, (pn 208300 798288825341255904), (pn 833203 194436285096331335), (pn 324732 69638737440417053), (pn 85261 645713171082164356), (pn 549126 725227148237735172), (pn 1071430 855948496624709645), (pn 113711 749891364634215041), (pn 907514 402122584837721866), (pn 33068 184861260876368956), (pn 208300 817048444523954818), (pn 159994 434699596434776866), (pn 156378 456233190661210560), (pn 248155 438364111170839585), (pn 61594 183096317412161680), (pn 530163 184088999753451399), (pn 391403 142156722308647973), (pn 161115 957840526549730114), (pn 914962 299389322606179440), (pn 213284 2471818521801330), (pn 464012 971978832725169204), (pn 208300 889177786019186502), (pn 13620 750063377587375908), (pn 165893 160715421955360067), (pn 315250 260477217178155124), (pn 416991 974038737949230849), (pn 11552 418120646235551832), (pn 322083 329946293933314754), (pn 8283 799751390621343004), (pn 127985 317535804654389126), (pn 631685 891025368202900592), (pn 511792 316952217776230155), (pn 33075 143222924261232776), (pn 492235 809051252007014977), (pn 913803 364541411204274453), (pn 344862 277833054736381024), (pn 364288 470470692606247089), (pn 990541 819826419293239340), (pn 132282 53593379628998880), (pn 833203 265086497804060420), (pn 621042 47193229226956884), (pn 379194 451884957889921249), (pn 686230 449412997201538076), (pn 13120 680480599558963504), (pn 1136622 656701451674846982), (pn 27222 981217933153558609), (pn 213209 781749198889615570), (pn 386376 368407301060061264), (pn 360009 835762114596636358), (pn 634079 541035691891876257), (pn 533344 978341906043706395), (pn 113744 70541177606603971), (pn 919713 174735216856289353), (pn 180078 993378147474502209), (pn 838839 278035928616560728), (pn 360009 835762653573010017), (pn 914393 642249133898930712), (pn 108984 609663259794195073), (pn 907730 346908859367886603), (pn 33068 261655705827700812), (pn 284155 664106108489994817), (pn 610387 841167478870580246), (pn 99382 556886072293704642), (pn 914962 862286326794832940), (pn 175356 916257068729561553), (pn 914686 458389184364682242), (pn 936306 185847759425319152), (pn 833203 408072714999923650), (pn 612729 677982703497910290), (pn 71020 469282454495135904), (pn 701423 44299695316980225), (pn 913203 809188762484968264), (pn 33139 828705979350133285), (pn 151633 972158613925442081), (pn 988177 720464488170011692), (pn 132286 719606749699096961), (pn 533344 978334179279770643), (pn 37908 402403607147743348), (pn 454828 479356420234612491), (pn 33072 868887245107573888), (pn 568608 801854556932917958), (pn 629347 896925587043840160), (pn 529146 949075053442533254), (pn 625782 914907294717517852), (pn 113762 154670401404350640), (pn 701279 514614932938344262), (pn 22478 655114099741995120), (pn 57168 340443024943876488), (pn 336584 319444650964314212), (pn 416382 509495514288818951), (pn 3869 326607092709349436), (pn 189411 368777864987148753), (pn 686536 703751916362262), (pn 99322 387947310985363504), (pn 530904 511500570611026695), (pn 3272 88251669683656760), (pn 208300 834708788443677922), (pn 994690 94759270144847984), (pn 81056 872605546157802627), (pn 918532 576345802448842024), (pn 170616 32670194537529585), (pn 990251 306310647160019076), (pn 549200 800433825649132930)]))) else (if j<6 then (if j<5 then (proofWord80 [0x221e150d, (pn 52075 208571368368539768), (pn 322083 329945467169032002), (pn 1069955 120661764783219232), (pn 142206 763394437862310336), (pn 229263 654201296949748254), (pn 123206 887636142051676513), (pn 307926 65379533379087388), (pn 16648 548101343135461536), (pn 529091 392668089383814275), (pn 918532 575268487952888920), (pn 369177 147569447371210994), (pn 463708 605452300248983700), (pn 644462 970910754843429191), (pn 334218 506856984254489057), (pn 231113 523434885571971400), (pn 635227 647872983746233634), (pn 142151 911101848330863138), (pn 82211 421162431755856924), (pn 15518 938058816402579744), (pn 1061064 792992110868109849), (pn 104289 481234618048202179), (pn 919713 175896318180732452), (pn 137411 387236695878459768), (pn 700983 505396307671009415), (pn 334200 14229116433805552), (pn 833203 552468048781182533), (pn 622218 27127876132019225), (pn 104225 187702818878927394), (pn 84142 605272288665810988), (pn 132296 159927843284190597), (pn 23074 742712527395795056), (pn 85706 174385773957678982), (pn 629343 226868689332100178), (pn 175282 768711324430021169), (pn 837358 278045854912494636), (pn 132286 737268615411765536), (pn 1136327 508519271905134984), (pn 331815 583334227578856988), (pn 123169 993585043331723649), (pn 342822 679895149379322630), (pn 630533 140764719527817360), (pn 529128 502894438472123459), (pn 917351 983603652165185065), (pn 170634 551753337261719793), (pn 857727 573963735188393020), (pn 208300 870315372990054945), (pn 760017 416589296521595143), (pn 28435 999321757292975396), (pn 132633 173576330771510416), (pn 568460 70454803642647186), (pn 462824 305615399310854940), (pn 95836 133955599767617984), (pn 209931 464151449053567508), (pn 90002 458940457773801873), (pn 475642 709576196487396396), (pn 132300 554824524136518354), (pn 463416 884609755646991644), (pn 123155 762068947030097964), (pn 549719 399228499670995727), (pn 52075 217546919010654268), (pn 189411 332326302522958305), (pn 760908 638534133975943175), (pn 28440 538667600365560864), (pn 132577 833625584888000676), (pn 681797 447030086438143365), (pn 401454 366230372279218416), (pn 833203 551342151068108935), (pn 626963 524542394148857122), (pn 123058 952262607921259648), (pn 530682 296039010094745170), (pn 8289 573348520673220680), (pn 35528 754403425227672692), (pn 459716 940853077957347072), (pn 918660 861389983718317058), (pn 337110 933791538240581641), (pn 132420 621125391128707777), (pn 907515 852898559795928083), (pn 71038 916044464253387904), (pn 568608 225393804629461191), (pn 404145 312131890574045296), (pn 57407 891960781349421954), (pn 914961 709338321515322898), (pn 66316 549544070875275605), (pn 343416 735160322666282028), (pn 132305 274648606361707090), (pn 159992 137863786491812372), (pn 394488 848025567795096712), (pn 549792 606078253191597835), (pn 33071 670810065485977660), (pn 189411 350339596371222945), (pn 155554 506781900132583174), (pn 27222 981217914828104992), (pn 132577 833625585156456612), (pn 606239 583304172114724178), (pn 615716 707659560451600395), (pn 119434 95353745790714561), (pn 907513 251181335167179031), (pn 71038 916047207647179876), (pn 435567 699486637283263074), (pn 84139 126232692764707143), (pn 634060 981595171403886625), (pn 142133 464357774620217792)]) else (proofWord80 [0xb0700b5, (pn 912617 249096973601479682), (pn 638811 94685119823278240), (pn 529109 839412163076407937), (pn 907366 833284931927937551), (pn 47352 841929839740468264), (pn 132263 913448338073162080), (pn 1136327 508519546783274515), (pn 346070 684461334626680892), (pn 554590 430662085414160903), (pn 3277 4128505995483208), (pn 284081 877199427781902737), (pn 457785 961684539800966472), (pn 33172 255118086740391017), (pn 398175 284582911765513984), (pn 841206 249339444638528556), (pn 132277 659000112476766849), (pn 1063732 708672756376674848), (pn 142207 540762367930680130), (pn 914962 873580613852015646), (pn 94761 864159293305094513), (pn 248228 62268141250282249), (pn 336579 654014575065538881), (pn 231113 523433842113452568), (pn 105280 830751255885497025), (pn 907883 345526658049582616), (pn 85280 20399925636444452), (pn 606683 456957528664115013), (pn 22510 945923289470496779), (pn 123188 802868911257453506), (pn 612730 539278505787133706), (pn 33067 356308845769795612), (pn 9546 537488571426742512), (pn 757645 472569355582080643), (pn 918532 574067531943122962), (pn 71020 469264049466007624), (pn 284081 876986932391690576), (pn 985506 928408496632760070), (pn 27222 981217932616423509), (pn 213209 781753596936126674), (pn 312587 91753765830677556), (pn 208300 871021823182160513), (pn 913207 277031286417987349), (pn 344862 277833054736640101), (pn 170523 437808613234614737), (pn 383408 982425757660494892), (pn 132286 593027394464968864), (pn 529073 669044004996794375), (pn 26060 908682092088940628), (pn 383104 5315086319550657), (pn 380825 573564309934189596), (pn 13088 348503079376736464), (pn 833203 335168509918807107), (pn 315250 255947056664564014), (pn 194283 567015441927440129), (pn 7696 989854826389584936), (pn 132277 351623435637317872), (pn 757645 404467863772400136), (pn 639977 738798385737795716), (pn 568845 427138326902277888), (pn 992918 58980451160203400), (pn 568237 263857140558760007), (pn 328293 444273879160762480), (pn 66853 98104448766725002), (pn 344890 92841991609106504), (pn 549868 67331700458396175), (pn 47352 851290178343518641), (pn 762982 795066237426104424), (pn 435567 699489670641911044), (pn 690685 414809004422208534), (pn 99322 387947310985363500), (pn 492755 503132133908092431), (pn 47352 851096112388677784), (pn 624314 784849115834647137), (pn 1064023 235813911467595785), (pn 639959 292054311823353893), (pn 161115 742727688710828497), (pn 838838 116068175451031672), (pn 360009 835762378686661762), (pn 387854 391095186884992023), (pn 43811 469087269229440164), (pn 758245 89243359267397901), (pn 52075 222259193143734672), (pn 834098 966660725111260106), (pn 348445 811060805589950945), (pn 79407 500171611677005332), (pn 89928 546292883018400192), (pn 285489 912222829544348175), (pn 47352 846582474936449128), (pn 435567 699486934781347590), (pn 935130 382328123262841072), (pn 833203 769494084378691912), (pn 635227 647873018039248933), (pn 161115 742727688710832561), (pn 682758 990351183237612166), (pn 634083 936231165030080624), (pn 52668 58267589131339011), (pn 13018 803299735411128436), (pn 416973 455237065890006785), (pn 8591 621903199038090268), (pn 11967 813368832403300688), (pn 985506 929254093258721671), (pn 624593 117928905409637418)])) else (if j<7 then (proofWord80 [0x1c02c685, (pn 86517 671115608534577163), (pn 108989 347379697970037377), (pn 907513 540303445364448791), (pn 52075 208518454311424136), (pn 492235 809050976600793682), (pn 84441 205248275237311754), (pn 347242 16541850757769320), (pn 464494 874435861911572234), (pn 33071 643767079322542152), (pn 284081 877131467239556434), (pn 463416 902553508857517844), (pn 86359 46704341872290912), (pn 435938 438648606719870720), (pn 842384 525240312500881528), (pn 435271 391698401911702690), (pn 387854 391095186902490396), (pn 118456 453946634005495856), (pn 814171 571874648158705167), (pn 47352 851324671481639012), (pn 416900 750811276530550213), (pn 20704 277287413274905629), (pn 132651 983003694112424513), (pn 907588 197612665423930650), (pn 80557 581859465713508689), (pn 191411 516325357413991241), (pn 42009 199745643413852368), (pn 833203 483805819015334666), (pn 648302 139011769502284917), (pn 530755 929023160990176787), (pn 52075 223190681664391288), (pn 416677 945325079209788114), (pn 387859 34377048019442709), (pn 651857 821626476068454444), (pn 758245 160102468400586262), (pn 66316 549596366128648368), (pn 701427 669514213220894470), (pn 631708 918037294876749836), (pn 170546 785884424670512516), (pn 919713 169382763059617306), (pn 104169 486331266849655060), (pn 701426 510980853224638662), (pn 1012106 122504054311514123), (pn 124424 894741751689216962), (pn 612730 550569524712515104), (pn 137355 828571052884465956), (pn 720242 774308961046496006), (pn 937800 593676541668462945), (pn 155554 506786380065543956), (pn 44978 99055182946006368), (pn 388583 411698979706636032), (pn 914693 730783563656746056), (pn 284081 877270555462373954), (pn 160000 244343115725610006), (pn 100516 923064589026864240), (pn 379196 541554132790150912), (pn 838836 96053538171672652), (pn 208300 852230948754952641), (pn 686531 366428937497156504), (pn 105469 928033974187377088), (pn 266414 603516431004407311), (pn 47352 846574781521272964), (pn 530756 78489645938591365), (pn 704908 48444927430959344), (pn 757645 761788197154146438), (pn 323551 460003621422780749), (pn 151671 9202315232477393), (pn 683057 28467967226813442), (pn 634074 731049931201671344), (pn 529109 876288957373105476), (pn 622218 27132274212479260), (pn 118447 844967131558019393), (pn 231775 302718488836578307), (pn 29033 36544806286848160), (pn 529109 840318424798266306), (pn 8267 56388169254904348), (pn 123077 759583200609386772), (pn 719722 501525289283375649), (pn 760017 416585985085474566), (pn 328273 826486456808923224), (pn 364307 207142801389782784), (pn 1065511 699174780305156124), (pn 11940 56557324920234224), (pn 757645 491204925497377730), (pn 612729 677992405761594898), (pn 71020 469282246236336228), (pn 416677 945324781713883585), (pn 79407 500164975800961287), (pn 632880 389974454124430624), (pn 142115 17613700910653761), (pn 231698 333922617106105031), (pn 324999 484308075581566986), (pn 123225 696430177252442560), (pn 191041 480254245781309959), (pn 3057 638237649139940392), (pn 132272 902351504854344097), (pn 155554 506783068544780616), (pn 635227 647872983746028574), (pn 113669 920668557886177556), (pn 719575 797906632289502738), (pn 8882 188600856306917917), (pn 113710 920735347112657601), (pn 907663 714182056207717135)]) else (proofWord80 [0x686052, (pn 326528 274145135259222209), (pn 990685 27481771549670440), (pn 132282 130650259271074241), (pn 686534 847764655140115602), (pn 347251 185446279522036842), (pn 435973 24888599247522311), (pn 3574 737069102715914300), (pn 189411 368249597911736657), (pn 155554 506781969066838857), (pn 644741 790599406187728969), (pn 180078 993378147471303041), (pn 307333 738375115681039048), (pn 937505 436832332247036080), (pn 529128 287004003247097475), (pn 918532 575233200029510182), (pn 156374 857438735988007281), (pn 326887 3397309482933251), (pn 41450 330810155735834960), (pn 985506 929546004972374665), (pn 342510 299808795649665124), (pn 417120 957980944819226368), (pn 914394 818973022944771112)]))))

def genIndex9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (proofWord80 [0xdfc00c60, (pn 283348 322746427059732720), (pn 17709 955207729614818749), (pn 193543 243701407458367523), (pn 20596 89391965671523221), (pn 987306 348282697704998576), (pn 3593 337735986538374203), (pn 914831 687257777968246873), (pn 283346 25008353444102384), (pn 17709 955240646462914561), (pn 265559 382928710304807936), (pn 407299 499832843011359448), (pn 373071 275768608122142780), (pn 1793 927860277349507608), (pn 50828 470281505451183872), (pn 23608 957921573532406663), (pn 235339 923286220144361487), (pn 406 616503679820250112), (pn 1133437 135401373626532800), (pn 43798 394606182959349820), (pn 590000 899964530734592003), (pn 906971 76334961506291992), (pn 1156812 635445044715454534), (pn 1075520 47400384679022468), (pn 76696 225094622805322196), (pn 34896 632398864064151488), (pn 5743 979330314938810428), (pn 4427 225015331575329813), (pn 764421 165772239953551104), (pn 283352 516065986678940070), (pn 1207745 815779637859696655), (pn 395 778410856653782016), (pn 1133437 133563814807335493), (pn 1053092 49294915372127497), (pn 163823 197567571554529283), (pn 67719 575342083436961536), (pn 190572 161159582246510962), (pn 1161094 655723769615584255), (pn 1063 493530458972802312), (pn 16414 513967375778841932), (pn 326612 325023951652263886), (pn 278928 35034976491250882), (pn 939437 770600684732813056), (pn 46194 395210998587725394), (pn 443315 540352279814062095), (pn 618556 236011222155148288), (pn 1133439 344159155861586626), (pn 1204206 480681779097174036), (pn 1170852 10063731165097987), (pn 906954 292581334049773652), (pn 283358 577360974244486242), (pn 1003868 138795777783480335), (pn 1106 836477208594231516), (pn 1063216 10212046097788899), (pn 708935 192796286695579549), (pn 1049550 584906506827984898), (pn 930345 571127454497419008), (pn 226870 90163581617259297), (pn 799527 967628899671787326), (pn 525834 276630511793862761), (pn 1073482 264279305168093469), (pn 427550 891862959144763408), (pn 865136 714671537526768801), (pn 971313 322103287647676556), (pn 1190036 486469001138981922), (pn 141067 944547557258280975), (pn 644764 809130555819565611), (pn 535864 247058542988724498), (pn 332925 786560120823680444), (pn 2745 238869598013157379), (pn 916415 815727346232282724), (pn 611545 307550611158625776), (pn 12431 880568474845435374), (pn 398405 119334443344994518), (pn 1133437 135401373624794460), (pn 837269 755339532470806268), (pn 370 69790296482967554), (pn 966727 218885631572368393), (pn 283357 614140717822397875), (pn 962368 675030833996324748), (pn 274141 598808345649765770), (pn 337673 620424643048497992), (pn 122832 986885229796334292), (pn 1150549 172474818763945403), (pn 363004 205242083884034601), (pn 569622 134786186142286017), (pn 346159 7060999595606031), (pn 755 87028447209913344), (pn 1133437 133267023703311296), (pn 66836 713633992123944484), (pn 694035 44450032066555907), (pn 1034770 112275319749607562), (pn 701548 776889658635332736), (pn 312194 2747690674552839), (pn 38757 657548248688332057), (pn 177162 912962582272821269), (pn 911860 732122355248399967), (pn 19775 131644221422928129), (pn 22451 705153636926562672), (pn 907579 816339080944402436), (pn 18907 931833477462295816), (pn 906751 155178364589445280), (pn 311827 239177936392508545)]) else (proofWord80 [(pn 6460 684145326749673092), (pn 231100 884266482091190000), (pn 392862 846359370786145919), (pn 65431 971612853796602080), (pn 1141112 57603964083177166), (pn 509516 83123664338304000), (pn 922143 697238834027692698), (pn 23643 826249999963848709), (pn 278324 534730715295696951), (pn 1012338 870824540483620608), (pn 116893 606071771245367408), (pn 1132188 253302314795091567), (pn 1106 872198501214474363), (pn 80898 848875897093125056), (pn 70837 289575004085616700), (pn 4427 488810161349752487), (pn 1036396 596702074124206715), (pn 887822 192777572682402711), (pn 319940 359679690672344727), (pn 541471 597748062058275928), (pn 414456 838384372643444672), (pn 24058 877992051714125529), (pn 565324 562455086659892524), (pn 100350 447721161397652060), (pn 160930 608960283908120519), (pn 282162 487460841478144007), (pn 77363 170066401574534144), (pn 1133437 135401373615331605), (pn 522033 670578727745915456), (pn 394101 455072445839139560), (pn 608447 870475994138675032), (pn 1190053 648069015072505057), (pn 1076949 241731994693386249), (pn 217553 905519245718993920), (pn 1172249 83029382181195712), (pn 58153 72556266152007804), (pn 4427 255805552144778289), (pn 976330 839440958540259072), (pn 283357 417108297859270356), (pn 206604 614555431290519567), (pn 1106 845229674803230961), (pn 705694 32229965799778240), (pn 34232 257163429263900728), (pn 860078 893299254289285479), (pn 1039002 830602662580954371), (pn 887818 38056052407926884), (pn 460894 134525365120647174), (pn 590222 28638130869898340), (pn 690731 669935093292628928), (pn 35242 216586338953884821), (pn 714260 8866671772135632), (pn 654806 223947922298273536), (pn 283348 384175478005301443), (pn 924403 392435550823890959), (pn 1106 851800002606092809), (pn 983428 212593967552905634), (pn 1053092 49293936119269149), (pn 104297 584751344004060834), (pn 731653 227084891146028632), (pn 293465 16888735553902632)]))

def genData10 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x1d3668c9816, (pn 171263 629829241894383938), (pn 318871 214654420814739560), (pn 418240 804100343627753229), (pn 718133 484088459806148841), (pn 918546 687992320357838862), (pn 380391 594060535738994196), (pn 113458 804955588411318529), (pn 605967 662229572543454248), (pn 226880 131948071851442208), (pn 1102716 511716879960375950), (pn 737692 235713415435266281), (pn 464613 893844914273421963), (pn 66483 806335717098674288), (pn 608027 851267538409952552), (pn 360533 619278986047738178), (pn 318871 214654420798290512), (pn 721067 211678220007081541), (pn 38038 928109062841472273), (pn 996511 851816520747845157), (pn 323274 668948174196510228), (pn 113468 899849539242049922), (pn 618643 63522336092477601), (pn 3564 941495684171139598), (pn 94892 947342171784758344), (pn 71039 424764332525638304), (pn 1103878 692973606021982675), (pn 128470 356435681438697226), (pn 56739 61324779748418115), (pn 625843 410146288569817116), (pn 152001 768049010532287366), (pn 52205 733643202366859618), (pn 626968 444529152761467940), (pn 152005 224512655810736833), (pn 920954 350361038793870872), (pn 189932 315708467807568129), (pn 916194 479362215369911368), (pn 644319 460317891401974467), (pn 628185 505168766155891768), (pn 379561 658542380585960067), (pn 2742 80817154688817156), (pn 742302 480527462548800256), (pn 835296 386878453386936770), (pn 14173 802435139638184868), (pn 851113 724231089360850584), (pn 194881 778603005628742231), (pn 356210 559814614239364385), (pn 354846 919493374333617450), (pn 842594 415549905385623424), (pn 845414 292438651465891650), (pn 1208049 595911006679151103), (pn 964542 354323176632156053), (pn 301738 2612916395675903), (pn 1077584 499656478727897058), (pn 150918 865352848201209119), (pn 1157274 738893529986371572), (pn 963311 24955250406585475), (pn 1195072 247542496973883388), (pn 240823 144534170788951312)])

def genIndex10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (proofWord80 [0xf3b0318a, (pn 797268 819322885219622587), (pn 508836 441029312521004811), (pn 750857 479922533649655459), (pn 283376 579652484469890560), (pn 1133506 309565355061868545), (pn 776986 828662760661915956), (pn 573620 223944714808164412), (pn 8854 780515361064932853), (pn 811058 469868983288856607), (pn 89244 196547807156373775), (pn 1171216 63900747154226923), (pn 1058086 827104069270657194), (pn 337908 457757822341857310), (pn 727079 144308816856678461), (pn 843871 527969506812775904), (pn 50268 65828345251895060), (pn 887826 6622196164773163), (pn 1133399 119673489656674307), (pn 907247 815024117183406081), (pn 224164 981246151540643033), (pn 1177288 551213691091943664), (pn 34727 941801605932830957), (pn 595975 591630309933379328), (pn 151884 801849484892553287), (pn 178623 977602791561830833), (pn 395434 120227568616613904), (pn 202791 622348832326224773), (pn 678841 105228892628320525), (pn 159174 253507835425712000), (pn 230310 792400437027803352), (pn 888614 14364078326174856), (pn 963916 232385538853822479), (pn 509 692598648473605308), (pn 8855 518151249024123032), (pn 147114 366392250976082880), (pn 134955 228832869108018944), (pn 18146 992926844174261034), (pn 35694 457057119821688834), (pn 951937 459896160260440070), (pn 645842 692144299816489720), (pn 338 814882777137189889), (pn 739151 936362882446393629), (pn 283376 580839957027888803), (pn 1133372 242191244595846648), (pn 1026435 691501616383385609), (pn 63604 456071308086050846), (pn 295899 538074713016107248), (pn 13270 301230390193773577), (pn 141678 613493622765519255), (pn 1111769 394075289860848641), (pn 1057857 395723520784265220), (pn 912523 583778437538234388), (pn 896673 711490855884226594), (pn 248055 438964666028554021), (pn 316648 882301957356074880), (pn 208403 682429907545103872), (pn 112983 899932086335729945), (pn 527687 629862986915726847), (pn 2213 832250013803219002), (pn 1094999 449064019947552836), (pn 791000 709387131680330727), (pn 421625 803122846223998720), (pn 566686 484562519324113454), (pn 1128922 296693155264751527), (pn 604765 62294351701387499), (pn 122894 207064780227674182), (pn 292350 773757903543917536), (pn 10190 257558374022736446), (pn 933390 185307990200450560), (pn 259509 803309879049569664), (pn 676200 6109597816981848), (pn 214299 640874680361386036), (pn 292197 507037588543532452), (pn 853692 852522213634241032), (pn 199324 775234840096958912), (pn 1171216 71487228643219898), (pn 541937 937191689708630023), (pn 605106 231009850419040494), (pn 376237 257966408480403064), (pn 11941 817012525979060879), (pn 146397 990599136059066240), (pn 283362 20702361739075072), (pn 606570 737424273984485378), (pn 524270 970204970637582344), (pn 151443 427408101063491644), (pn 8855 458478544771362544), (pn 3403 751555206495978638), (pn 387315 654054995079415462), (pn 196077 360530751404768256), (pn 32854 910666332111433729), (pn 1060932 868246820064454319), (pn 365726 841368281119406840), (pn 5293 425994284995993568), (pn 70838 751023535570315136), (pn 283351 804935995849189472), (pn 917178 493286379143041153), (pn 492353 975621141606582148), (pn 241081 651291286573102321), (pn 628369 985076480140644546), (pn 94447 403020382122509584), (pn 151373 986583601069951008), (pn 330579 511667199704825984)]) else (proofWord80 [0x3, (pn 907216 345426829945987081), (pn 66653 175451266284203474), (pn 945348 234089815469115513), (pn 1059203 329161090528988630), (pn 633023 850136953355276962)]))

def genData11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18408027f

def genIndex11 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x3, (pn 216113 848690890442265718), (pn 262094 277621787048878526), (pn 35452 348297549019379742), (pn 35448 803224361686530078), (pn 20252 252959938671805380), (pn 224348 2154927501347392), (pn 330669 857066509909966989), (pn 31104 35682279924181483), (pn 247958 853121357636435972)])

def generatedLevels : Nat → Packing
  | 5 => (8,6,6,0,0,6,0,genData5)
  | 6 => (77,5,6,0,0,11,0,genData6)
  | 7 => (314,4,6,0,0,14,0,genData7)
  | 8 => (575,3,6,0,0,16,0,genData8)
  | 9 => (406,2,6,0,0,16,0,genData9)
  | 10 => (42,1,6,0,0,12,0,genData10)
  | 11 => (1,0,6,0,0,0,0,genData11)
  | _ => emptyPacking

def generatedIndex : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 19 4 7 3 0 genIndex6
  | 7 => lookupWord 20 115 6 11 7 0 genIndex7
  | 8 => lookupWord 79 471 7 13 9 0 genIndex8
  | 9 => lookupWord 144 866 6 14 10 0 genIndex9
  | 10 => lookupWord 102 614 6 13 9 0 genIndex10
  | 11 => lookupWord 11 67 5 10 6 0 genIndex11
  | _ => fun _ => none

def generatedForest : Forest := ⟨509,11,fun i => generatedSamples[i]?.getD (0,0),generatedColumns,[[]],generatedLevels,generatedIndex⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP5_0 : block generatedForest 5 0 8 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB5 : block generatedForest 5 0 8 = true := genP5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_0 : block generatedForest 6 0 10 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP6_10 : block generatedForest 6 10 67 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB6 : block generatedForest 6 0 77 = true := (@block_merge generatedForest 6 0 10 67 genP6_0 genP6_10)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_0 : block generatedForest 7 0 16 = true := by
  apply cellsBlock (ar := 6) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_16 : block generatedForest 7 16 70 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_86 : block generatedForest 7 86 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_182 : block generatedForest 7 182 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP7_278 : block generatedForest 7 278 36 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB7 : block generatedForest 7 0 314 = true := (@block_merge generatedForest 7 0 86 228 (@block_merge generatedForest 7 0 16 70 genP7_0 genP7_16) (@block_merge generatedForest 7 86 96 132 genP7_86 (@block_merge generatedForest 7 182 96 36 genP7_182 genP7_278)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_0 : block generatedForest 8 0 96 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_96 : block generatedForest 8 96 29 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_125 : block generatedForest 8 125 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_221 : block generatedForest 8 221 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_317 : block generatedForest 8 317 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_413 : block generatedForest 8 413 36 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_449 : block generatedForest 8 449 96 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP8_545 : block generatedForest 8 545 30 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 2)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB8 : block generatedForest 8 0 575 = true := (@block_merge generatedForest 8 0 317 258 (@block_merge generatedForest 8 0 125 192 (@block_merge generatedForest 8 0 96 29 genP8_0 genP8_96) (@block_merge generatedForest 8 125 96 96 genP8_125 genP8_221)) (@block_merge generatedForest 8 317 132 126 (@block_merge generatedForest 8 317 96 36 genP8_317 genP8_413) (@block_merge generatedForest 8 449 96 30 genP8_449 genP8_545)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_0 : block generatedForest 9 0 34 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_34 : block generatedForest 9 34 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_130 : block generatedForest 9 130 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_226 : block generatedForest 9 226 96 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_322 : block generatedForest 9 322 9 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 1)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP9_331 : block generatedForest 9 331 75 = true := by
  apply cellsBlock (ar := 9) (rows := 0) (d := 4)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB9 : block generatedForest 9 0 406 = true := (@block_merge generatedForest 9 0 226 180 (@block_merge generatedForest 9 0 34 192 genP9_0 (@block_merge generatedForest 9 34 96 96 genP9_34 genP9_130)) (@block_merge generatedForest 9 226 96 84 genP9_226 (@block_merge generatedForest 9 322 9 75 genP9_322 genP9_331)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_0 : block generatedForest 10 0 2 = true := by
  apply cellsBlock (ar := 7) (rows := 0) (d := 0)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genP10_2 : block generatedForest 10 2 40 = true := by
  apply cellsBlock (ar := 8) (rows := 0) (d := 3)
  simp only [cells, boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem genB10 : block generatedForest 10 0 42 = true := (@block_merge generatedForest 10 0 2 40 genP10_0 genP10_2)

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
theorem lowGenerated : Lower true (varsX 509) (graphGoal 509) 12 :=
  lower_forest (g := generatedForest) (i := 0) (hints := 1027)
    (before_sound generatedKnown generatedPrior) genGeometry genTables
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_49617.ForestCore

namespace PEqualNP.Outside.L_meta_49617
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![0, 1, 2, 3, 4, 5, 6, 7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffefffffffffffffffefffffffefffffffefffeffeefefaee00fffffffffffffffefffffffffffffffefffffffefffffffefffeffeefefaee00
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 2 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 1 zero, 8, 10)]) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) lowGenerated
  have count : (([(inputs.getD 1 zero, 8, 10)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by
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

def upperGates : List Gate := [⟨.or, [1, 0]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [5, 14]⟩, ⟨.and, [8, 3]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩]

theorem upper_shape : ∀ g ∈ upperGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates, 21⟩ (List.ofFn x) = graph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_49617

open PEqualNP.Outside.L_meta_49617 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_49617 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
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
