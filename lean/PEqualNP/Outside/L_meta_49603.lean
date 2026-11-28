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

namespace PEqualNP.Outside.L_meta_49603
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
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
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
  let xs := supportPairs (z/512+80) s
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
    exact ⟨hv,rfl⟩
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
end PEqualNP.Outside.L_meta_49603

namespace PEqualNP.Outside.L_meta_49603.ForestCore
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
def K219 := extendKnown K215 10 [(219,[]),(246,[64,33,16,49,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xff000fff80ffffedec,(pn 75565 934207651736187447)])),(BitVec.ofNat 152 (proofWord80 [0x2a26a2251a25228de8,(pn 129082 430531229240603143)]))),((BitVec.ofNat 152 (proofWord80 [0xfffff00000fff01992,(pn 906758 963218135685792675)])),(BitVec.ofNat 152 (proofWord80 [0x4c04c0b62c0644d992,(pn 938804 493118623883722915)]))),((BitVec.ofNat 152 (proofWord80 [0xffffffffff00000559,(pn 907802 287338817713085643)])),(BitVec.ofNat 152 (proofWord80 [0x700700383007870558,(pn 917403 889761544226997323)]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffffffffffffea0d,(pn 688284 916003617856545013)])),(BitVec.ofNat 152 (proofWord80 [0x804804c00048000205,(pn 22032 701863440351641776)]))),((BitVec.ofNat 152 (proofWord80 [0x492,(pn 217230 10011989250670338)])),(BitVec.ofNat 152 (proofWord80 [0x7007004070080000,(pn 194562 867713479521049364)]))),((BitVec.ofNat 152 (proofWord80 [0x1360,(pn 528903 893164293699403784)])),(BitVec.ofNat 152 (proofWord80 [0x8008000080000000,0x84210514a800000]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(4,0,227,0,8),(1,0,230,0,7),(2,0,229,0,7),(32,0,199,0,6),(64,0,167,0,6),(3,0,228,0,5),(33,0,198,0,5),(34,0,197,0,5),(36,0,195,0,5),(65,0,166,0,5),(66,0,165,0,5),(128,0,103,0,5),(35,0,196,0,4),(37,0,194,0,4),(67,0,164,0,4),(129,0,102,0,4),(130,0,101,0,4)]
def g231A : List (List Nat) := [[],[16,101]]
def g231D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [(pn 72648 768087422097567299),(pn 12530 975786171845055800),(pn 546783 461648817562291719),(pn 608532 26084623139996388),(pn 239226 135369723748371779)])
def g231D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x1860b88c0,(pn 75557 863725914323419136),0,(pn 681201 365153946322075648),0x10208000000000,0x907a9cee470b79b,(pn 517222 152909522893641836),(pn 27277 209596119047453100),(pn 898783 273706163774434301),(pn 1147303 802775421626039698),(pn 922524 811553683369697418),(pn 312258 343180855922416170),(pn 81606 347093635751808389),(pn 311086 677235806143073909),(pn 1059420 529378862996754532),(pn 400946 757391749012450178),(pn 440176 589537547417125203),(pn 819776 896954898267899220),(pn 1020422 644566513674440253),(pn 1059420 543734236053869408),(pn 401028 614800997871057799),(pn 420401 679888332810715475),(pn 827448 706018105071866226),(pn 113728 566364079783235382),(pn 1058831 962388093624762707),(pn 99066 334993149087901569),(pn 401809 379747343363311699),(pn 677520 469983922706317651),(pn 416845 323714690719764278),(pn 1066465 470306526465738068),(pn 684361 959658501183558528),(pn 400628 193519534313149763),(pn 975317 246101762584988528),(pn 421844 535456841724137274),(pn 1041411 338983571717210469),(pn 382283 839407021423624071),(pn 421588 18208246495024451),(pn 854012 883568439228498021),(pn 400593 878689601488752486),(pn 1043772 501958728240709971),(pn 381990 423140552391945602),(pn 119630 958485275386662211),(pn 675153 560383397352572278),(pn 382309 732819830575022653),(pn 1059420 547108570666488656),(pn 397479 921302063769374082),(pn 138539 444269170117939008),(pn 819773 438757162534700372),(pn 420070 165057139128468135),(pn 1065284 846858246496312147),(pn 378903 422838593620080513),(pn 439887 743152310737785648),(pn 677513 590721984972326260),(pn 1002083 124443432598422078),(pn 1058242 244407109701982548),(pn 359561 487064031937756032),(pn 441933 602743184117809456)])
def g231H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x7c62000007,(pn 302554 302761294742174720)])
def g231D6 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (proofWord80 [0xf7dba6c0,(pn 802500 762872561391278850),(pn 792142 188888950376655882),(pn 750751 703971681295511594),(pn 585237 898775422657544361),(pn 1131433 173833419738251943),(pn 901256 467814079630412446),(pn 1177729 499061303701940863),(pn 518563 364101495376095741),(pn 855882 903825611965507518),(pn 417745 348814674925887227),(pn 472680 900791123541914613),(pn 1031026 930139566984253431),(pn 478440 788818148505139165),(pn 704542 220115260452363120),(pn 400317 250766780508124497),(pn 463178 698709927455577413),(pn 624899 545322364726039830),(pn 6184 177195982192997333),(pn 171130 213586600914687316),(pn 684429 228611984665548114),(pn 320455 598041842719659321),(pn 73116 708995104922425444),(pn 273802 838788417552016720),(pn 1152168 415669822426551619),(pn 1038596 306971747184694542),(pn 603137 962652956479804477),(pn 1137512 900234890669543663),(pn 583558 903225172033356703),(pn 976407 675158797506383606),(pn 873871 418487789508115710),(pn 961770 34931128501071603),(pn 853099 790148160431846346),(pn 692316 84403962008022962),(pn 804759 916752180944518888),(pn 801188 99903030164255394),(pn 786900 764323511977897514),(pn 729752 536927822003583018),(pn 501105 619896855640853161),(pn 795607 33066560977347238),(pn 764427 815702486770957058),(pn 640753 795501007080909834),(pn 136938 492992067249287786),(pn 112705 383273116268669352),(pn 377628 310246739071934113),(pn 1052425 173345842082904708),(pn 1196941 269550431297727003),(pn 555122 757006416429951071),(pn 864286 403642994066628989),(pn 1040512 37049768602142203),(pn 530474 535346296777743853),(pn 912953 877260536698654711),(pn 477204 648953275782125396),(pn 1002124 198742136631720307),(pn 1001530 153101514283152846),(pn 480798 818603751746303797),(pn 393154 802904970380696918),(pn 288127 710595396447073624),(pn 1152510 554151209511277923),(pn 983246 813168235261160783),(pn 305619 790611935118554429),(pn 11800 956189296368702708),(pn 64836 173903095408972752),(pn 217148 912458059750903616),(pn 1018493 892175718073515266),(pn 598445 572100636540490765),(pn 1128105 60653876723929133),(pn 1188166 936635178254156023),(pn 519656 490266575913681630),(pn 880323 160472173128452606),(pn 1117608 102116830603128315),(pn 805285 720859746009929644),(pn 803291 277977377046781368),(pn 190850 570755348068497062),(pn 794097 593098052883565082),(pn 758535 869458899456224907),(pn 219031 945279103244941996),(pn 724975 306116539442980778),(pn 482050 161134701655077545),(pn 719788 946850439330933414),(pn 460409 697257708103805561),(pn 641567 406501216023062630),(pn 131739 102869563424285080),(pn 593085 683139750854821473),(pn 597920 372091686943725959),(pn 875193 104813082787472915),(pn 1160860 903811599865387119),(pn 864296 50353671577428414),(pn 1039331 409262827029497309),(pn 547002 674475271834702845),(pn 1026308 540898728153213910),(pn 327340 986094602269341529),(pn 100143 44974994621135204),(pn 397030 403848148227179845),(pn 379046 560261170733684513),(pn 610727 592189179457919253),(pn 232860 648075700735398744),(pn 326981 411876645752884577),(pn 684290 875816465405511061),(pn 319307 250098785023166037),(pn 68395 387462143236659444),(pn 46907 958739012313632972),(pn 188221 554296859563213104)]) else (proofWord80 [(pn 19037 67046403509944833),(pn 38369 246259462042419208),0x1082000c4c01218200,(pn 57858 429522923149656064),(pn 354528 1411126219115032),(pn 151162 42481495463690497),(pn 613909 376747456941261315),(pn 9444 746760216738017538),(pn 4872 246280685277417602),(pn 28485 817082831272149120),(pn 9445 813900826074153472),0x1608001102420821,(pn 38959 848305797697716755),(pn 99323 638324083473647632),(pn 37785 849532722425385090),(pn 311824 347360862795202563),(pn 9445 885958060796641794),(pn 614055 225873580299403397),(pn 758032 488853634614854144),(pn 425460 418439701950627840),(pn 614092 695836000589578754),0x182002020602100820,(pn 680634 236423055666618498),0x408002020e082001,(pn 9482 211957031263406088),(pn 153038 881729801156567328),(pn 625752 633917106359894016),(pn 153477 198941356633882882),(pn 40030 29118407732371648),(pn 604465 217973731473883184),(pn 151115 871575951873672192),(pn 77183 484316274348021793),(pn 455726 849988308985471080),(pn 608521 266528712341327927),0x40dc01037004070022,(pn 8880 955904162335315712),(pn 434467 481195603017883392),(pn 455546 484226259789736301),(pn 1014449 603458785500817238),(pn 497708 593838902749418993),(pn 445484 932061594134079829),(pn 1007364 251854718034333012),(pn 950594 481460962272662545),(pn 303779 341202442733971765),(pn 997326 556296570798680658),(pn 647698 790610871848718865),(pn 152626 711534611599563031),(pn 988765 465166606567018576),(pn 1100566 235991357778153553),(pn 20369 313250481921845500),(pn 980499 305716250128217423),(pn 344470 959262967639101008),(pn 1073418 983229818250582235),(pn 971052 194286815864214605),(pn 192764 796352899093875824),(pn 931713 392933754259626171),(pn 961605 154897387746013258),(pn 1098794 925120737184959104),(pn 771112 570409495145597081),(pn 951567 603489621551386440),(pn 1022628 170184209950230608),(pn 624683 459864494516717690),(pn 942415 784098151198125894),(pn 1022000 823222324611696224),(pn 473531 982836555506370650),(pn 932673 668896330731245893),(pn 39250 406562764790744176),(pn 331825 239619124381087804),(pn 924112 289465595827597890),(pn 1171991 10982694798541280),(pn 128712 739921603548219405),(pn 909941 658297462742400988),(pn 407549 644194867723564145),(pn 421272 473435866171694533),(pn 476164 574056841865975629),(pn 369887 171621068218522678),(pn 327307 475757966271541401),(pn 100274 115198677992457572),(pn 401103 373820140191105425),(pn 395939 514920407802897733),(pn 372766 736155502596904149),(pn 273803 414688435970072916)]))
def g231H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x83d921,(pn 472163 744298919631257674),(pn 656814 769488998900432910),(pn 61390 995175125244972050),0xa2600050f402b1900,0xf1a3a2d2f6,(pn 316296 782852354790653952),(pn 851579 227668115592453123),(pn 700017 44109130064723976),(pn 151732 540714028095393792),0x32900a000000b4100,0x118000000c3e0,0x33500000022a000206,0x915d0e000e3658100,(pn 4851 495423116428813184),0xa84809a23d1122ef1f,(pn 985685 298308020906754289),(pn 1049611 896767790767424584),(pn 209924 457398077199757312),(pn 386924 420124936079753216),(pn 163093 538293266404975744)])
def g231D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (proofWord80 [0x406042c1,(pn 760531 38747001886883984),(pn 685951 414174524979611920),(pn 231497 704699389391553152),(pn 308882 704108579733963286),(pn 623946 202829791255627170),(pn 85458 307567460106199426),(pn 38006 926883960439456848),(pn 337801 114518715332828177),(pn 1067552 140452767239384088),(pn 305800 974218462985654800),(pn 831740 850427622236456456),(pn 161164 699658316301812320),(pn 152005 825645879743758584),(pn 14352 735011470161313880),(pn 606834 111165735210323728),(pn 179477 705888761448522208),(pn 77782 714848287196053858),(pn 623760 438000781212260416),(pn 613612 933450147744122924),(pn 153403 233234993587208834),(pn 9742 42959792416759864),(pn 14757 688063827687379032),(pn 585601 529498525394011670),(pn 184186 200937950989050160),(pn 28635 704763037005316289),(pn 27744 774740108185010304),(pn 911445 464225711939128336),(pn 595045 959477514796740622),(pn 75783 549240769249321314),(pn 621055 778778252842377404),(pn 11861 941074915101776940),(pn 311103 189840252597559314),(pn 227640 23140842519721989),(pn 652037 355755927396169859),(pn 1134568 12097884382045752),(pn 458955 863473689301747756),(pn 368372 403202668939970054),(pn 278632 413292922778206535),(pn 674121 293389361055540736),(pn 916343 128807567748632608),(pn 835711 511988564266206223),(pn 605358 748499356421980803),(pn 1084931 481600298337562844),(pn 1122647 690227842500908061),(pn 216365 103495600157592694),(pn 933779 860333944332076731),(pn 205989 619646495318913515),(pn 17378 764305930067102305),(pn 776426 601990605872154267),(pn 196413 358459753643216376),(pn 895059 689582130687485944),(pn 590141 785078107873939566),(pn 560751 779807207457578885),(pn 1012270 94209827162240280),(pn 374926 923914864383777347),(pn 623633 604085401693075139),(pn 350394 972612716424491653),(pn 180377 461500597134018330),(pn 914093 162264111847378544),(pn 930494 159647372392640512),(pn 1207029 642030457752114469),(pn 302108 260061583333390737),(pn 396666 756924127132778453),(pn 100349 806249650918080509),(pn 365171 734517888405820415),(pn 1020423 150657382720537919),(pn 1158461 580619735719301699),(pn 1208212 467440996707162452),(pn 301965 509464176300389709),(pn 321118 44231197559881561),(pn 250579 802315216838266869),(pn 374561 89146525437743359),(pn 401789 682650126627427599),(pn 1157225 432456785760175440),(pn 1208131 749420176601240788),(pn 75360 516271534098085203),(pn 231392 864549639845625689),(pn 251391 473694182491896821),(pn 709899 840281253461775295),(pn 1025145 483306079486498107),(pn 1197144 402664063781405011),(pn 904799 338922392272983237),(pn 283223 689471982529410450),(pn 320961 17218626681552793),(pn 397784 838586197926494073),(pn 364875 973136880754574271),(pn 723780 770998504193078539),(pn 1159623 500316195350204240),(pn 903603 745820116424579285),(pn 66063 361726248406220165),(pn 382490 73758371007217497),(pn 548070 443974063713160949),(pn 72029 895022305112047855),(pn 401771 163707652655289355),(pn 1178658 225214256829535024),(pn 1167991 562249342677831731),(pn 56550 20888620675364241),(pn 231236 49210545817042841),(pn 382732 295366247407750125),(pn 610729 9198680985588667),(pn 418025 978952045636879675),(pn 1008340 804094006721351488)]) else (proofWord80 [0x16084442c31608,(pn 304021 583977559403661449),(pn 47242 222203468448302086),(pn 123521 776650288065857028)]))
def g231H7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (proofWord80 [0x3a80272796,0x4a0c0000000003,(pn 165282 826900437582479360),0x5ccd58a00000000,0x1259c10800312600,0x1596000000000,(pn 54085 853698883196026880),(pn 1005421 338993465401278467),(pn 117743 659417970155716608),0x56b1c491e171379f40,0x53980000000a000,0xc04000000000000,0,0,0,0,0x2565a,(pn 982252 228436886204448768),0x2340000000000,0xa340000000000,(pn 986074 757699808715079681),(pn 842352 121381873693753344),0x2094000000d6ccaac0,0x701400000000,0x570001d6,(pn 302231 454903657293676544),0x73c0000000,0x65b40000000000,0x179b00000000000,0x1e1500000,0,0,0x1e32000,0x537f1a8,0x40c00000000000000,0x250200000000000,0x184200,0x4d8000,0xe3e000,0,0x1ea90000,0x2d7400000000000000,0,0x933000000021,(pn 648439 732632155951464448),(pn 267477 789068788498432000),0xde40016b10000002,(pn 348274 528119496124661760),0,0x51adc9e00000,0xa69800000,0x3988000000,0x148e0000003410,(pn 761186 447457550937882624),0x102d36400000000,0,0,0x121b000000,0xb6f0000000000,0,0,4,(pn 698910 239464707491627008),0,0x1f,(pn 604462 909807314677832106),0x4b380000000000,0,0x52,(pn 680020 773533228910772224),0,0,0,0xa55b5e80000010be0,0x490511e000e5d80000,0,0xc73262a3e0b2800,(pn 135786 483126576009445376),0x10cfb368000000,0xf648,0,0x46800000000000000,0xb28c90c00000,(pn 29662 364470524962797568),0x13ac000,0x22d40000000000000,0x31940000000,0x288bce000000004,(pn 283341 989010764699009024),0x1e04000000000,0x7a2df02000000,0,0x6c631860000004,(pn 242957 310393622001090560),0xc4dac13a,(pn 192685 465221955555732992),0,(pn 153034 188835494449635328),(pn 925583 830642735808774144),0x63106204000008020,(pn 85021 909815705638805506),0x5800040031680201]) else (if j<2 then (proofWord80 [0x8a8b958000000000,0,(pn 312561 631584934642581505),(pn 177088 743110024265203712),0x1c00000000000,0x28cc00101,(pn 1012016 49999816565981184),0xc238000000000,0,0x13400,0x69e9490b40f,(pn 396679 920734793690513616),(pn 665000 512171210908369677),(pn 151115 727451828646839085),(pn 604462 909807617516766476),0,(pn 476959 14769834166583296),0x71ebf3941a00000,0x18a5000000000000,0,0xd3a8000000000,0x3e0c00000009b8,0x1e7400000000000000,0x2aa800000000000000,0x7a0800000093,(pn 944474 608247320514396160),(pn 114222 239304409543606272),0x18ee0000000000000,0,0,0,0x214600,0x2599b17000036,(pn 906694 364710971881029632),0x8890000000,0x7830,0x71a89c80,(pn 7108 913997407171285248),0x636800,0x4a5081a640000,(pn 416379 913063836686483456),0,0xf7300000000,0x26e800000000000000,0x31d000200c00,(pn 13774 561733002179641344),(pn 295479 946572679597785088),(pn 155838 93934698292051969),(pn 349455 119740277960508518),(pn 139309 811244654533804032),0x30c800000,0x5acc00,(pn 123519 398928612754771968),0x58f4000,0x1590d978,0,0x8c700,0x29,(pn 680020 773533228910772224),0,0x42d800000000066a1,(pn 624532 967359510588424192),0xf3080000,0x48000001b9800,0,0,0,0,0xc0000000004920,0xc840000b4766700000,0,0,0,0,0,0x101400000000,0x33,0,0x950000000,0,0,0,0xc4d000000000031500,0x32a5c72f6ea0,(pn 766240 855333747355025422),0xed20000000cf6000,0x60f0,0x7d280000000,0x1a880,0,(pn 8845 214065849498861574),(pn 302231 456565843996966912),1,(pn 768565 145091310935343104),0,0,0xdb0000f2d000000000,0x2c56000000000,0,0xece8000,(pn 95037 625467751609925632),0x54800000000]) else (proofWord80 [0x18ba000000,0xa00ca9945e,0x4970000001a1f0000,0,0x1b,(pn 661131 307655014685605888),(pn 30317 223885141648080896),0xea70000000001cdf,0x5840,0x62c1af0000029a,(pn 935028 563641187986047008),(pn 868915 432848014721168896),0x3d7,(pn 1057810 92162800527867904),0,(pn 609775 572100542938218496),0x1cd6c3b3a5c0000,0xc5c800000000000000,0x1a2e33f000000000,0x32c,0x2c6e000,(pn 204242 350384112155492352),(pn 133406 853146709990572032),0x10bc00000000000,0,(pn 35763 625072904393195520),0x39c4000000000,0x8480000000000,0x35b80000000000000,6,(pn 909296 738371188018905088),0x938000000000,0x214,(pn 906694 364710971881029632),0x27520000000000,0x14a80018be0000])))
def g231D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x40,(pn 320534 106597012067652099),(pn 19186 940823282309939680),(pn 114859 336734331994473477),(pn 17122 59870024998656024),(pn 47526 310678119650706016),(pn 227625 917918167852199044),(pn 276729 588989330482793472),(pn 301834 842376525105418236),(pn 642191 400828877907405343),(pn 1152550 986706547437075728)])
def g231H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x927,(pn 485150 337223128419821015),(pn 302234 109052159223795838),(pn 1077394 769903257712345520),(pn 530291 612250174190852118),(pn 528912 491036290630136092),(pn 732231 144571144736995371),(pn 924423 834849645248861459),(pn 256936 844901014080913412),(pn 1018364 992537663153557534),(pn 479804 795020232927871232),0x698e565d2d2d1,(pn 51983 576046104179256599),(pn 698393 898648316069107731),(pn 154031 894373171191399311),(pn 397269 828462128836536379),(pn 847556 604475435634472470),(pn 230405 924159983521162997),(pn 672129 697489965174229055),(pn 764728 281266375395135917),(pn 793029 502830697663864289),(pn 360756 501180742503540500),(pn 619965 746208065841418206),(pn 586050 842107485572100536),(pn 59152 760907287639362391),(pn 560995 181768541116176404),(pn 9784 850285167414567951),(pn 14187 964391487154643202),(pn 259840 849688646967689216)])
def g231D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8200ff
def g231H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x71c56000000000,(pn 648649 256975356873671021),0xa0002503b6d,0x382003200000001900,(pn 203652 169415544971198464),(pn 137243 776763819110432768),(pn 59860 260979941123822279),(pn 377799 406692736927007236)])
def g231L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g231D4)
  | 5 => (70,4,5,0,0,9,0,g231D5)
  | 6 => (231,3,5,0,0,12,0,g231D6)
  | 7 => (120,2,5,0,0,12,0,g231D7)
  | 8 => (14,1,5,0,0,9,0,g231D8)
  | 9 => (1,0,5,0,0,0,0,g231D9)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 17 0 7 3 0 g231H5
  | 6 => lookupWord 20 127 5 12 7 1 g231H6
  | 7 => lookupWord 72 1481 3 13 8 1 g231H7
  | 8 => lookupWord 37 163 8 12 7 1 g231H8
  | 9 => lookupWord 6 67 2 9 4 1 g231H9
  | _ => fun _ => none
def g231 : Forest := ⟨231,9,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P4_0 : block g231 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B4 : block g231 4 0 6=true := g231P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 70=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 70=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 18=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_18 : block g231 6 18 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_114 : block g231 6 114 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_210 : block g231 6 210 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 231=true := (@block_merge g231 6 0 114 117 (@block_merge g231 6 0 18 96 g231P6_0 g231P6_18) (@block_merge g231 6 114 96 21 g231P6_114 g231P6_210))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_9 : block g231 7 9 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_72 : block g231 7 72 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 120=true := (@block_merge g231 7 0 9 111 g231P7_0 (@block_merge g231 7 9 63 48 g231P7_9 g231P7_72))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 14=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P9_0 : block g231 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B9 : block g231 9 0 1=true := g231P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact g231B4
  · exact g231B5
  · exact g231B6
  · exact g231B7
  · exact g231B8
  · exact g231B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 10 := lower_forest (g:=g231) (i:=0) (hints:=16778597) (before_sound K219 V219) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K219 10 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V219 low231 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (proofWord80 [0xfff8fffac0000f8001,(pn 1201283 181828120289771511)])),(BitVec.ofNat 152 (proofWord80 [0x88120882c94aa4920a,(pn 379570 589391723562535488)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0x3fff3fc020007001fe,0x23e1fc261ffcf9c19])),(BitVec.ofNat 152 (proofWord80 [0xa040080318818622,(pn 227267 657486430513044808)]))),((BitVec.ofNat 152 (proofWord80 [0xc0003ff94007807e00,(pn 68552 703670459237933033)])),(BitVec.ofNat 152 (proofWord80 [0x2c082010631130c64,(pn 160637 4164603680330117)]))),(0x0,0x0),((BitVec.ofNat 152 (proofWord80 [0xffffc004a0f800001f,(pn 1138233 284655198242856990)])),(BitVec.ofNat 152 (proofWord80 [0x1300131434a55a28c4,(pn 637593 262180189668122644)]))),((BitVec.ofNat 152 (proofWord80 [0x1f00007fe0,(pn 9297 159030741732950032)])),(BitVec.ofNat 152 (proofWord80 [0x1c041c2018c66c3088,(pn 931634 362711362578432528)]))),((BitVec.ofNat 152 (proofWord80 [0x71fffff8000,(pn 9444 732948147104382976)])),(BitVec.ofNat 152 (proofWord80 [0x200020000000004111,(pn 40495 900636038534529024)]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,7),(4,0,233,0,7),(8,0,229,0,7),(32,0,205,0,7),(64,0,173,0,7),(128,0,109,0,7),(5,0,232,0,5),(9,0,228,0,5),(12,0,225,0,5),(33,0,204,0,5),(36,0,201,0,5),(40,0,197,0,5),(65,0,172,0,5),(68,0,169,0,5),(72,0,165,0,5),(96,0,141,0,5),(37,0,200,0,4),(41,0,196,0,4),(73,0,164,0,4),(76,0,161,0,4),(100,0,137,0,4),(129,0,108,0,4),(132,0,105,0,4),(136,0,101,0,4),(160,0,77,0,4),(192,0,45,0,4)]
def g237A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g237D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc7060f915c87254110
def g237D5 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (proofWord80 [0x53842973,(pn 159272 397881760613287427),(pn 535188 542713813477860003),(pn 39300 665956240006333077),(pn 1144218 877225057226425696),(pn 407401 391620533986113834),(pn 229130 386990823051985964),(pn 506117 132065462315891030),(pn 25462 568960755674024738),(pn 760457 253401428046972995),(pn 392779 323369655375273876),(pn 456726 797531530725098937),(pn 815355 686746404160365892),(pn 158183 767181897974778360),(pn 367412 41422179685002859),(pn 693201 567628024799336020),(pn 316766 373355764802787544),(pn 547205 884105655374889700),(pn 269998 689154219390637666),(pn 321729 605047895052132621),(pn 1176867 496465966121863600),(pn 1110321 381630890597375381),(pn 171242 562029778073362968),(pn 1022463 831259852761922715),(pn 64824 905505504522435981),(pn 388490 877670825608778273),(pn 659201 753975710835866060),(pn 217883 908053679616389404),(pn 99838 623164503699794210),(pn 79682 107659425762288380),(pn 732201 606846500120615029),(pn 700132 633984454919758354),(pn 158307 29752595348524086),(pn 882792 800115716997931365),(pn 438075 891079706476994593),(pn 160945 217387188225380519),(pn 437165 548493267878798616),(pn 555269 65419011832130697),(pn 690080 525199944396837130),(pn 1137081 532840887497369160),(pn 629718 16853588887475878),(pn 793986 616581361215291664),(pn 826940 651523376398308964),(pn 946051 164303568887327148),(pn 351855 603241406714500113),(pn 53805 229347328743725486),(pn 346592 745811249697155870),(pn 777569 612461731225085249),(pn 79447 541314760831698330),(pn 475597 795396790735022137),(pn 199713 828246080081973844),(pn 80495 882981591729866845),(pn 180895 857838755156947563),(pn 88039 977994738627810597),(pn 307264 194891831331915910),(pn 1021591 646603443497653004),(pn 799376 576580901411358258),(pn 396993 328558511655919752),(pn 498912 464822550476867948),(pn 503271 324903621224717623),(pn 100369 949082852380944904),(pn 636788 564938630568885442),(pn 928706 674617896087862733),(pn 384062 440720996076522144),(pn 644478 909456772606739308),(pn 530280 671335395027411540),(pn 704024 675968688505402088),(pn 40274 238237787184710691),(pn 1072858 71652212989663061),(pn 648487 222259793634429580),(pn 606976 838927574534194243),(pn 127817 208997495841659780),(pn 155069 455878972690204840),(pn 793514 792147428154097732),(pn 219058 196220153490939192),(pn 291851 797192015530846826),(pn 654057 588326494964569092),(pn 320054 79746921384251891),(pn 719522 320151403169589929),(pn 78657 531287329571112256),(pn 322269 422242681246065144),(pn 95421 53302335809111024),(pn 506111 826303117458265379),(pn 20115 774273773538648605),(pn 233541 910806848147983279),(pn 31447 521703207745639558),(pn 227932 203979367079051809),(pn 1082474 944230182693514418),(pn 824248 542742503983371348),(pn 392035 79689295035013154),(pn 138451 196832281743389323),(pn 201411 974824524140073764),(pn 628965 101478800712280450),(pn 159898 58820620156735328),(pn 843648 656592286398140722),(pn 341541 773366760802789264),(pn 160964 241725602865942735),(pn 133314 811215145847808215),(pn 251597 467469103533500985),(pn 10067 38168488797016335),(pn 758708 119553766539494729),(pn 535180 543144751113452234),(pn 680650 10129346301559056)]) else (proofWord80 [0x1c3040,(pn 14185 762646939735687168),0,0,0x14100002800400,(pn 152891 249157295457697792),0x10410000000,(pn 19189 378715479152075270),(pn 309407 238387982521106436),0x5901089010,(pn 607716 482880764538781696),(pn 869210 580757592387134676),(pn 616514 491213882250820766),(pn 1000006 449010422420247756),(pn 721692 138770878165558548),(pn 739397 546710699440152099),(pn 700912 634859234513165586),(pn 160933 756701863282100285),(pn 28935 162750824785723207),(pn 1043534 551625609089508668),(pn 337592 574581409049379277),(pn 270486 689609650971528601),(pn 832114 647022484673422604),(pn 649587 205380183781736031),(pn 55662 342726205492863694),(pn 420494 206184917794723106),(pn 747665 725252274822880915),(pn 767058 63191837564505232),(pn 84157 92173564375720944),(pn 576406 699039423342124099),(pn 587603 563475875470559256),(pn 769900 195381446474760333),(pn 81499 750812468159202160),(pn 505533 135109802436334850),(pn 265615 28368114785988101),0x880e00c00c00217f28,(pn 913453 587322787587818850),(pn 116086 38187881893504168),(pn 363296 51005008354962482),(pn 359063 615167281136558151),(pn 24964 249269816473954890),(pn 628930 572524222166608223),(pn 192495 112432595880195609),(pn 541159 812618284620813506),(pn 794602 31466582776300185),(pn 1144198 997782044982874713),(pn 34043 849142419530854700),(pn 200814 111610726806279217),(pn 278799 13329875238295813),(pn 950710 49392129790208776),(pn 919243 14090987833464130),(pn 146138 288042327734804371),(pn 462594 10863814057856442),(pn 199243 732216470376375624),(pn 160250 376480540453833721),(pn 331072 26248273648562411),(pn 209602 307693127853708548),(pn 620575 17840574791423433),(pn 694715 268495185310128804),(pn 872052 29717485449725264),(pn 340984 825174607901376902),(pn 1012321 102680406275639598),(pn 657121 883549418556512501),(pn 229073 897800636404696084),(pn 866874 894154292923845411),(pn 8147 304606321157371281)]))
def g237H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa
def g237D6 (j : Nat) : Nat := if 11 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then (proofWord80 [0x987d4a30,(pn 321930 711767520014858613),(pn 1004148 820737595269497104),(pn 754258 923306556380796242),(pn 661445 906964200571552636),(pn 439569 248258006257583664),(pn 322260 390458792766067587),(pn 398505 319310113562476816),(pn 903011 106504845453301025),(pn 661445 906964149031945148),(pn 421805 33715053485131312),(pn 321857 498475435742059395),(pn 440711 469891497468674320),(pn 1122598 918394993632478565),(pn 359214 166662546391843646),(pn 421900 437969427143971120),(pn 321856 925919049228679558),(pn 1006214 856067255818830096),(pn 902416 832608640763829588),(pn 359214 436296848023241468),(pn 1059383 19668743539477808),(pn 322142 828496044031728514),(pn 400571 354918497088225552),(pn 753669 203675474834103122),(pn 359214 301205899484873468),(pn 455508 99828444009154864),(pn 322142 829585660055050597),(pn 361611 831296270056866064),(pn 1053518 145163962370871633),(pn 359214 560673600136037340),(pn 401790 28164698176046384),(pn 322002 764293633972621618),(pn 398210 171404937380282640),(pn 902420 810413011905140001),(pn 359214 524100493321716604),(pn 439513 619795434209051952),(pn 322292 669956070508060994),(pn 341541 773471961113723152),(pn 1053532 21299771800428133),(pn 944787 749583981650395774),(pn 1066486 727504774527555360),(pn 322000 458473147567044999),(pn 1005606 113517220375855376),(pn 902416 832028098624363859),(pn 944787 682597041034511222),(pn 438391 232696170528983840),(pn 322000 459578156753217907),(pn 399962 612368462718992656),(pn 900059 646857233264137522),(pn 944788 28755151862121340),(pn 440750 110094460842231584),(pn 322149 744897505318892371),(pn 398782 20716909588939024),(pn 1199871 154425618030184785),(pn 944787 751838749286482812),(pn 440713 216606579123865376),(pn 322292 669974195269599111),(pn 422393 852809702224462096),(pn 826269 269218776422126961),(pn 944787 892520231268270717),(pn 1066463 669074551935158048),(pn 321999 882552255473215826),(pn 1002064 338657266088313104),(pn 1018100 395961897990834512),(pn 944787 752397334479389564),(pn 436026 590689883655100704),(pn 321856 342176214234561408),(pn 440693 22798335242961168),(pn 821548 55094461294578021),(pn 340324 915198469792351038),(pn 441928 972333159125696800),(pn 322149 760698861799469429),(pn 397896 576539078464211280),(pn 675159 302224982635302242),(pn 116086 169278718446748374),(pn 457018 465350544943858002),(pn 397340 425659037910622083),(pn 441930 414194646865756704),(pn 862277 869335055153106034),(pn 397011 648289657143460570),(pn 1061741 933113528823400784),(pn 341073 761899469119191397),(pn 1039311 503545566327295008),(pn 970856 590528535199060336),(pn 1006473 720280013184975662),(pn 420715 849685431098917713),(pn 624401 936064397962000740),(pn 400608 536533634353807888),(pn 1074749 772293408937054546),(pn 397288 565584787115885462),(pn 421862 391840901130738514),(pn 321775 639923844767964003),(pn 1005071 158110572789448976),(pn 1088913 989437981118565750),(pn 396993 96275865467372492),(pn 401790 46178822394824240),(pn 322179 705095692848419155),(pn 398210 171672579341074704),(pn 1015753 88592389707013457),(pn 38093 495196609830732652),(pn 439568 653782743271162912),(pn 322145 135409685513199989),(pn 341228 179088222840717584)]) else (proofWord80 [0x15495044,(pn 281673 230325234588616656),(pn 703711 184298626768769199),(pn 719811 71611520226574932),(pn 80491 900957614961580628),(pn 775155 321178671381303364),(pn 207306 330009979601900112),(pn 703711 184368789354516639),(pn 719884 858587815064650324),(pn 80491 900816877473166944),(pn 926271 48630499893923908),(pn 207306 397563973946410380),(pn 703711 282237277120565439),(pn 113794 23615995609428564),(pn 80491 900882848170882776),(pn 997106 545933455670726724),(pn 291113 342597756263429340),(pn 401479 764859729645474015),(pn 109753 898433553825231188),(pn 80500 547107762588581020),(pn 864585 136509575401656388),(pn 223981 335190808428642844),(pn 401479 827896449252790495),(pn 261081 763442221546361172),(pn 80500 547028597751397464),(pn 779582 539817921712312388),(pn 263526 533791624075633492),(pn 401479 818893983052009719),(pn 100152 368143128020472148),(pn 80556 22298438956989528),(pn 704024 676092007321784388),(pn 243165 950434841196462685),(pn 703711 200482210374291623),(pn 1172725 331942018108449364),(pn 80518 845088187937954648),(pn 704319 823900717556781124),(pn 169970 418223131198846297),(pn 547873 104295987276484781),(pn 1172135 463973664662582224),(pn 80531 374670107304475993),(pn 411380 916390149665275972),(pn 188269 582714751497373524),(pn 547873 153127767198470387),(pn 402679 110563585458000336),(pn 80528 789875775443793500),(pn 1006103 945330676553957444),(pn 263383 5263370349414233),(pn 472315 314597716882952367),(pn 869608 789107201506235536),(pn 80528 790017543724268640),(pn 553863 567611367924056132),(pn 225751 638064328599111000),(pn 774546 735579790386991263),(pn 720110 898756712417415824),(pn 80528 790016993968454752),(pn 553273 271739578837516356),(pn 207306 334579549894440276),(pn 774546 770477460523913439),(pn 110187 464473280544592272),(pn 80565 97614702486420704),(pn 704093 851373491934609476),(pn 207305 331050889147417753),(pn 396757 416884798566240491),(pn 870199 12860030530708816),(pn 80554 302210349541340704),(pn 1012154 477334768492298308),(pn 207452 472657914650394969),(pn 396757 394577082028200125),(pn 869903 864954786820874832),(pn 80519 566649286440709857),(pn 104574 668890530399207492),(pn 207306 478624369226118612),(pn 698988 849340134172201151),(pn 113877 29460710629659216),(pn 80528 789876187760590433),(pn 1157367 246696067449045060),(pn 225605 288176043942966676),(pn 396757 434401731414921439),(pn 261303 119867489258131792),(pn 80569 866926639152360481),(pn 99557 154598812282863684),(pn 296500 377049358016795732),(pn 396757 398517451455533279),(pn 260712 824057156447588688),(pn 80565 97333158790233312),(pn 704020 64397334535290948),(pn 221620 431168152511534164),(pn 396757 398377319557566687),(pn 110247 344333917343064400),(pn 80569 709357826799008861),(pn 387621 510045069098696772),(pn 282264 377030049943081544),(pn 396757 469286130102898859),(pn 1172430 467763621721892176),(pn 80560 774158991491267680),(pn 552609 188970379771723844),(pn 225751 636868059931313245),(pn 467592 914338949539893485),(pn 869903 932508815582655628),(pn 80464 231479831026646625),(pn 856090 410802072110903364),(pn 188417 157436999376401493),(pn 165361 440856289952469151)])) else (if j<3 then (proofWord80 [0xc1524433,(pn 1121994 409049151259401237),(pn 171231 785112589418143640),(pn 291630 504981379167573137),(pn 65864 233720514363547767),(pn 24959 642504639747867699),(pn 1104359 321714684929170453),(pn 171250 104418867421962007),(pn 140514 777529517452842129),(pn 55368 198472160205234375),(pn 24959 660447518461936675),(pn 1199877 11762402966920548),(pn 171227 245694531453095928),(pn 555288 665087849804435601),(pn 50756 529710567811178710),(pn 420457 848814241656751155),(pn 1046399 740781182090304612),(pn 171249 868015156182683640),(pn 480892 946242942400811153),(pn 42455 747061385451790806),(pn 401568 373630167828022307),(pn 1162281 160231519981425812),(pn 171227 281548540482996200),(pn 480874 499509898569912465),(pn 63632 69934356453351926),(pn 382678 914980926539842595),(pn 1200023 324707092718639428),(pn 171243 385293739821936120),(pn 253020 316704600330932369),(pn 60789 325651228686244183),(pn 231563 189744580201432115),(pn 1084178 564557731185122723),(pn 171231 820825085718073336),(pn 555287 512166345197587601),(pn 51346 753462232975891861),(pn 192603 661477684469449779),(pn 1008620 807792329047039075),(pn 171227 281548556589109240),(pn 329849 852859098124930193),(pn 42492 604519636340269526),(pn 400387 782009450415670307),(pn 1200023 269537997283350803),(pn 171236 216477874109063064),(pn 442743 926576972383145105),(pn 61268 904773734547579222),(pn 364822 457746625813038131),(pn 858463 250293879537425525),(pn 20116 21456144836906838),(pn 178404 245741764312601617),(pn 64811 794577923308838997),(pn 345933 3003914978608167),(pn 1086429 374564682086604053),(pn 20134 360078814916165400),(pn 140809 781314561833718801),(pn 56401 36277640383357079),(pn 327043 532234242829337647),(pn 972908 111535060738562325),(pn 20122 975241740202589592),(pn 271855 451225773836620817),(pn 68336 348783408194707606),(pn 327043 530316899635184683),(pn 1086629 982906482754360597),(pn 20133 386349118334484280),(pn 100669 666201923596014609),(pn 56437 911681020544835894),(pn 251485 681789431396189227),(pn 1086354 362609277983708373),(pn 20140 880268460815333304),(pn 176153 742975594661106705),(pn 65438 911730874477598933),(pn 251485 659818163268764711),(pn 1086720 991647740813824213),(pn 20116 75847988630576567),(pn 250531 15078212578530321),(pn 56437 908303320828371047),(pn 175927 804975859375293486),(pn 1105337 143125036755066005),(pn 20124 704449037325098647),(pn 159551 673293862887117841),(pn 51826 476667903647079734),(pn 175927 802829903661909039),(pn 481946 720976603405703317),(pn 20136 792267667350269880),(pn 328376 275061021692023825),(pn 51863 262069660015580374),(pn 175927 816337249390314555),(pn 820684 282402133729499285),(pn 20123 11252807596562359),(pn 364974 615309857470960657),(pn 68352 452389038278467829),(pn 175927 816373566560027705),(pn 1084065 741365052270892181),(pn 20136 807853244673994648),(pn 497200 876816981235487761),(pn 70418 325595707164876901),(pn 175927 811871100804023353),(pn 1121881 566716156818248853),(pn 20123 11110970596583350),(pn 251637 819720951525430289),(pn 72817 537232395518483605),(pn 175927 816373463480812605),(pn 800613 71928435293705365),(pn 20141 295584720232445720)]) else (if j<4 then (proofWord80 [0x50843ae5,(pn 686280 281917116703364360),(pn 315197 324745747097949765),(pn 950680 930481551495667982),(pn 583033 887980421585114405),(pn 311988 527744200284060389),(pn 686833 684236038582326536),(pn 319614 706881309073937941),(pn 327328 555024275968631052),(pn 1187792 575633908312381268),(pn 916445 745661326674635750),(pn 129058 907218521984668424),(pn 319762 298882931869874245),(pn 960508 431584188679409932),(pn 1050779 348925624508004149),(pn 703942 582004889797538686),(pn 16294 910956573512488532),(pn 312845 301843903015401485),(pn 969953 162421230508790024),(pn 1197209 585368328258516773),(pn 703942 595251788709114737),(pn 979639 226715708449396308),(pn 317429 43009050381317929),(pn 951063 696463385106927882),(pn 1178241 720774538299512613),(pn 703940 132073063607184254),(pn 63500 129041204618499668),(pn 317415 203447395469719573),(pn 951063 696489751911158028),(pn 1055211 161174934785132325),(pn 703940 406801402610068454),(pn 72907 968520978341566036),(pn 319757 948916771469604637),(pn 913284 766755234478903565),(pn 1036575 355988869218367237),(pn 703943 838210067131544446),(pn 63564 656612405227124276),(pn 312854 570243105684977733),(pn 960471 538096049908666632),(pn 1206608 282222022998677085),(pn 363932 208194911471937518),(pn 6840 630356454569424180),(pn 312845 301896370333808693),(pn 1026289 516588166261559564),(pn 1187681 913795197743978069),(pn 363934 64187899415636862),(pn 63259 997104804353316148),(pn 313988 981944173069309965),(pn 950731 658429886662758664),(pn 1206645 157959648927635277),(pn 647273 756130758669642622),(pn 63264 879008939240941092),(pn 317419 562953773455235133),(pn 1007676 755758223938064650),(pn 1159370 755577552532723541),(pn 647271 999938280810623477),(pn 1003306 345319082267334180),(pn 312845 355887046998087757),(pn 969897 823895266507919626),(pn 1121609 982228294673454677),(pn 647271 891886799247911870),(pn 44370 801391442232677924),(pn 312854 552298783861897269),(pn 1035715 807172711169691916),(pn 1041343 902048062107866989),(pn 345039 392113110051726326),(pn 148253 352410031201006884),(pn 312845 382653283190691653),(pn 695705 418224648162939144),(pn 1197264 664057519464896061),(pn 345042 733537450898237942),(pn 110437 527063289719977252),(pn 317530 225372756000602165),(pn 941268 477620321541984524),(pn 1158812 678237455306495773),(pn 345039 410180216399868909),(pn 686824 492390426959688996),(pn 314016 679055475942078005),(pn 922379 11697639037374732),(pn 1187128 412376198769849945),(pn 345040 436983145980767166),(pn 44375 124849317405025572),(pn 317530 243382756462549069),(pn 1026271 69835322228773128),(pn 1197135 870115379689903973),(pn 345038 275255612605739902),(pn 63573 573743915160147236),(pn 312854 498246792244590613),(pn 1026271 74330065633579273),(pn 904413 711781716851480421),(pn 345040 292885837853764478),(pn 63573 573741789142668580),(pn 315068 143265367244863525),(pn 705150 149000237860294921),(pn 1159375 348967695452337733),(pn 345042 598455858946124726),(pn 53796 799380601441948964),(pn 315778 297577141624100973),(pn 969602 673131567610892552),(pn 1197264 655050324378973749),(pn 345040 500024706016225782),(pn 110428 303689973488981284),(pn 314007 410656238906615917)]) else (proofWord80 [0x483dadcd,(pn 388784 879472263904429186),(pn 1184739 50143636159608137),(pn 379121 926244502168801129),(pn 391298 461456932014593345),(pn 155664 374832895492058637),(pn 535178 239458324065354883),(pn 576656 106423444653286853),(pn 379121 926239137754648299),(pn 542340 401933290256602433),(pn 154502 459569464042956106),(pn 459620 375609277257417859),(pn 1031036 234389463099795781),(pn 379121 926241199338950505),(pn 388789 704262649834116417),(pn 154354 889909367761380682),(pn 232946 785519835848967299),(pn 1031036 18216682179265865),(pn 379121 926442414261799549),(pn 627426 102421754710799764),(pn 155390 185563367227520531),(pn 544718 664612087265112194),(pn 868345 265185838671070677),(pn 467664 989722664698514653),(pn 554234 24616641860947276),(pn 154048 193945723873719837),(pn 476161 339734391877087363),(pn 223668 378918074130580879),(pn 392106 583310804776519935),(pn 625078 673173167423833420),(pn 154802 76254948348328477),(pn 473800 157548488215048323),(pn 790421 529900908121900433),(pn 392107 702382662806277369),(pn 636856 919265326050772300),(pn 154945 34000327783998939),(pn 530468 555830963289272451),(pn 823337 492900629695577537),(pn 392107 150764207560067831),(pn 624917 327212917235860886),(pn 78211 334468176081288717),(pn 535276 165396574483400770),(pn 828192 467951423258637781),(pn 474674 716424289424313023),(pn 629787 283341637240436114),(pn 78730 151388248588613077),(pn 535271 554273371785349187),(pn 223594 650495101758356953),(pn 399116 348304017156278525),(pn 636870 761008347601122642),(pn 78501 852672865483290003),(pn 535197 766518745110759490),(pn 299316 96284452447599953),(pn 469952 415241273614601405),(pn 639165 70297884951727438),(pn 79318 64739355819500945),(pn 532831 971314232131401794),(pn 301661 291676840857464273),(pn 394394 263285120511315134),(pn 639162 764455906530182478),(pn 79871 534613362493291985),(pn 473802 391263388674369603),(pn 223594 650486306604735941),(pn 389672 693816226719272173),(pn 466856 335245044172133706),(pn 79387 323396798576584087),(pn 530466 177508220587026499),(pn 747784 240858466073587137),(pn 389671 613106114697169653),(pn 613106 801501701213070726),(pn 79318 150307740149937685),(pn 476154 351203219756357698),(pn 752656 363283546629358931),(pn 384950 255277968497642685),(pn 473946 797994778799058246),(pn 79373 395955573010458001),(pn 532822 749063548937508930),(pn 755008 397462337039658449),(pn 384950 328610933746764989),(pn 639162 755449120657655110),(pn 79760 863156110901302789),(pn 473793 167963983954909250),(pn 752658 666874756029369681),(pn 384949 681214020546267773),(pn 634366 601989954962015558),(pn 78211 343470891390596503),(pn 539906 298721893451372610),(pn 596793 37931934849191361),(pn 384949 532568986230787261),(pn 554160 86698912011076870),(pn 78727 849921145330062741),(pn 383994 418365051895552067),(pn 969654 621361660623343065),(pn 380227 452080090444270329),(pn 617995 112119765713765698),(pn 78799 331195232866774537),(pn 549346 420560305749035075),(pn 823478 95269932333274513),(pn 380228 532875753982856889),(pn 473806 137067615007749442),(pn 78799 331190834820998545),(pn 544624 54006927701903427),(pn 750221 386306019543893325)])))) else (if j<8 then (if j<6 then (proofWord80 [0x23f61f64,(pn 700478 860534258767053627),(pn 437817 997717265477109329),(pn 397487 418084858279033700),(pn 435141 778126750253401424),(pn 972645 910065113741495635),(pn 398247 476559011833528958),(pn 457903 907940322634482001),(pn 397414 784046285844216146),(pn 1039309 539713378804930080),(pn 679285 52380413284977012),(pn 422099 45714627395093055),(pn 459085 675229062479856997),(pn 642905 208233217579613569),(pn 1046396 782389926937580064),(pn 977385 15305419928503670),(pn 402028 988164630408364847),(pn 421309 30068754372742484),(pn 643195 747825680179326309),(pn 1041674 415972476619412000),(pn 1051170 257714401861032818),(pn 402029 397954812029993535),(pn 461446 839330137143362900),(pn 643268 935258075600321927),(pn 1006273 961239496196722208),(pn 829218 999259023871445332),(pn 419737 930587389749133887),(pn 462022 722495978395767635),(pn 643199 167744996872355204),(pn 1046395 629468423404473888),(pn 679290 816968144979368817),(pn 399667 804924261825020605),(pn 455510 461139683996684641),(pn 643051 49951431142077825),(pn 1003910 472162745518491168),(pn 829808 716354631369623924),(pn 1002950 123110326945219375),(pn 439591 479450650829738833),(pn 642905 212152423555856740),(pn 435437 160183943037535776),(pn 679288 513374736556626294),(pn 398487 493084759952229047),(pn 1061783 439694696465420625),(pn 643182 468383832540069220),(pn 401790 298782423333553696),(pn 1093029 936099318109131105),(pn 398487 499821445147034302),(pn 459091 416192694450248016),(pn 643051 627012498540657542),(pn 439568 77860766698783264),(pn 1112528 129947430634260820),(pn 397306 765233449125577630),(pn 421272 132077317089742160),(pn 643309 848177000315804003),(pn 400608 554587614207099424),(pn 829815 668767864629614961),(pn 397306 828280543226397502),(pn 1044050 352906816010421584),(pn 643309 827926195155431777),(pn 398247 370929501556282656),(pn 679285 51254238500227443),(pn 421804 41356738362114623),(pn 457905 83327013954635109),(pn 340820 170695991085424515),(pn 436050 226053862208673056),(pn 979136 9229458995549040),(pn 421804 325068668258255678),(pn 1041116 191039976031240549),(pn 340674 326975028904132485),(pn 436638 215881578024619296),(pn 679874 774524703303143792),(pn 1005016 158443852428247615),(pn 455549 644426759980291411),(pn 340673 756705059641093506),(pn 1044034 157996065353452832),(pn 750121 699147196866614629),(pn 719313 128652710847218463),(pn 1045530 722977418313045345),(pn 340674 329227908902092167),(pn 1024552 90516770879522080),(pn 754255 498636815772782960),(pn 1002655 262833004256723806),(pn 400645 790743470122845009),(pn 340819 19168920625674113),(pn 422155 215940156519695648),(pn 745990 210562738632920438),(pn 398192 207255174489866941),(pn 1059402 656506208349703505),(pn 340673 757812265702973299),(pn 1023961 794739393229309216),(pn 792626 438240939789388656),(pn 398192 65958602960306751),(pn 1066486 458432091950782001),(pn 340812 679789460788671862),(pn 398506 490038214370575648),(pn 900646 557702315588323172),(pn 397011 815466828881494778),(pn 1060599 387902226709974352),(pn 341143 550226851643222402),(pn 400608 266286889208987936),(pn 900057 989022414277005170),(pn 397011 936240482463810522),(pn 1061741 933113597039561040)]) else (if j<7 then (proofWord80 [0x1e303cc0,(pn 14098 782990802357514699),(pn 912279 745350344741563864),(pn 858932 558932283648815806),(pn 51524 894271413101964586),(pn 569800 514567332581647954),(pn 706184 32782844840053286),(pn 190603 366252560955988127),(pn 11663 664145058840604105),(pn 836569 686696581112604056),(pn 705741 608230278933996105),(pn 949807 20109360276240163),(pn 588184 969423044750904050),(pn 178426 718053651485247582),(pn 156290 287431515428095103),(pn 840489 569407313295569031),(pn 845864 818966186137886040),(pn 544581 15530499308790204),(pn 939236 400709435606352666),(pn 1154239 413802245978876113),(pn 742710 166908746993796668),(pn 117328 385907041465020511),(pn 989294 701136493486897093),(pn 1025178 115777750902249016),(pn 417954 673440186722279763),(pn 931654 315987697576250643),(pn 1172603 115437440551373473),(pn 193702 202927463317554202),(pn 76374 154942968811671609),(pn 230824 350114031869149762),(pn 1180806 941686646734916212),(pn 187724 931013023490904186),(pn 310975 738546265232865797),(pn 982653 466654575011040928),(pn 226685 697486892253577288),0xc001800023f60f7458,(pn 854914 174476646369869665),(pn 260717 872675464877531860),(pn 207452 188377688540284124),(pn 406958 394650850788855982),(pn 1020801 699970723654824280),(pn 854946 601096826245496672),(pn 1167707 97061240228372948),(pn 207009 827089089799488732),(pn 1011126 156552711682085007),(pn 1021466 70706244283232856),(pn 552717 307710158466628960),(pn 487096 27748576778609108),(pn 202804 761510868517094236),(pn 104431 791982615131148431),(pn 1171549 501206623197164504),(pn 703798 590999130737360865),(pn 109159 279250816966812244),(pn 243165 949173168848274268),(pn 557926 582067687148048541),(pn 1172138 932325921084502424),(pn 703871 226737891746167776),(pn 406742 154734897505526356),(pn 188415 147860164178969048),(pn 779877 843908186356666550),(pn 1171839 600576662814814292),(pn 703844 276216471857912536),(pn 864290 583009740489577044),(pn 216824 790842835490930972),(pn 99857 17044932311470239),(pn 718938 887073810105200724),(pn 703826 118196596486354784),(pn 1092296 663207636395843924),(pn 169969 269532839334871645),(pn 255399 945482128710783119),(pn 1171844 360599951421567704),(pn 401567 136658148250828512),(pn 109454 138995507070722388),(pn 207452 188236538735069076),(pn 859862 891035661265359054),(pn 1021908 864480946098107032),(pn 401639 761987145484696160),(pn 109380 351983959405125972),(pn 179267 715942163753562836),(pn 784305 72200740757655766),(pn 1015996 683005279773352344),(pn 401636 307792683025479520),(pn 1087426 722805567290433876),(pn 243083 371592338970076380),(pn 1010978 670279027495096525),(pn 1162915 992353154352051032),(pn 401647 836791949937039324),(pn 1006851 344717991837000020),(pn 243161 477239201480012696),(pn 708747 198764425001914573),(pn 1167412 97990678407832152),(pn 401599 346609253951647585),(pn 29026 334797094361588052),(pn 243161 261066419309545428),(pn 708747 206646063652229333),(pn 1167407 486304736277779032),(pn 401656 771941582099412508),(pn 1166526 361342651378196820),(pn 169970 417739638114320985),(pn 28726 371895471803551887),(pn 1173314 984036747589538328),(pn 401640 348294711609636320),(pn 1010909 628389335517913428)]) else (proofWord80 [0xf027b19e,(pn 823927 994710391810586121),(pn 1003046 508906667579893519),(pn 737398 112697960147644011),(pn 423461 631197684359077670),(pn 560075 604892061917944162),(pn 477725 934506955723970952),(pn 784108 251389680320632727),(pn 332276 116195742018853401),(pn 485915 815958960532268395),(pn 706405 772101518187874898),(pn 270450 382565575861287588),(pn 1079417 448092285074576082),(pn 351099 754536332910078232),(pn 1078425 580178272887782544),(pn 1030712 476632055597645929),0x23e88f8a3ca8f123b5,(pn 672756 857144290210345526),(pn 1024008 980588666895781731),(pn 262326 982250344256670714),(pn 221816 919150027749517490),(pn 163983 110049518179223177),(pn 879060 607323802742694744),(pn 649954 276335861144281572),(pn 639772 65506111818973720),(pn 795107 806569727325131873),(pn 356632 494065135675212982),(pn 87221 421450701216704573),(pn 1062099 205057702730448514),(pn 897434 686519330802632552),(pn 132822 934751053251010588),(pn 605459 67762230297604605),(pn 1019802 863685583942182623),(pn 663457 468609335645207993),(pn 1164207 912392926449289161),(pn 751289 500717456392376955),(pn 65730 912897075273918343),(pn 739610 924781221113372226),(pn 571145 988951080978368992),(pn 942141 942774842851292381),(pn 970279 848763471572465233),(pn 1024299 428121407185672023),(pn 742877 271978767948787316),(pn 764177 649627007633182599),(pn 275610 97436696534424752),(pn 540817 731136344760133064),(pn 260225 653128192917442652),(pn 280698 466580799922139109),(pn 902986 234732875123336947),(pn 130998 308280096467424110),(pn 83672 620138524647994694),(pn 999283 143457615041190677),(pn 511153 475036046485582253),(pn 484962 215418060752725274),(pn 587523 441124990227278021),(pn 765734 81617864431769214),(pn 1029280 454384860440152934),(pn 1140956 948005118486354118),(pn 460901 152620719243139369),(pn 473519 779609853496041866),(pn 180129 613371553690818584),(pn 341797 812161030219784217),(pn 604573 488927981619246580),(pn 112181 480836909562826333),(pn 1196954 304526764106675301),(pn 972054 87275118688540414),(pn 433229 753046943294746987),(pn 480091 977726882994299286),(pn 563615 1708456842189049),(pn 469977 829099068501095810),(pn 103769 262231938680608855),(pn 176418 132517719657764549),(pn 412420 150268204054910244),(pn 398252 550909321930827084),(pn 780095 854856202506019924),(pn 657923 107596633625547153),(pn 327412 689411864474596617),(pn 397090 395905145722629199),(pn 553640 179776923986639284),(pn 1082963 330567183173227365),(pn 365267 718738746742135086),(pn 551153 173129822289045842),(pn 752226 24863002332383533),(pn 166251 934562706450736250),(pn 84288 301332891345984838),(pn 439642 719842161197913572),(pn 406442 391776974695272735),(pn 322321 117817524122252556),(pn 1077581 587591179561868368),(pn 421492 610902278640976001),(pn 5091 179743237052875761),(pn 678844 704928087868935486),(pn 136792 108933526563386595),(pn 981351 813776460497489670),(pn 282695 133501448208978155),(pn 1075187 981520044785115470),(pn 558299 420746208524253356),(pn 1066139 197387330662937467),(pn 65637 504720085577478966),(pn 684040 102163043731429043),(pn 411091 254988057140907263),(pn 243733 191434681390893257),(pn 921471 104391936913640268)]))) else (if j<9 then (proofWord80 [0x80010302,(pn 4944 882691161821809956),(pn 37778 932006181503283232),(pn 454537 299230154876322860),(pn 42576 238244184735879169),(pn 1060480 332538325641463840),(pn 913796 380329561528213570),(pn 114556 606842717243245696),(pn 155994 968102277478491140),(pn 23907 280125778054874161),(pn 155914 200302460709408833),(pn 85039 490224337713104388),(pn 614058 680293013953020944),(pn 609194 554555442328768518),(pn 690365 145562735117934624),(pn 312123 683613278956881158),(pn 37782 408660575165087744),(pn 455708 365597196480020740),(pn 75557 899864680826539028),0x201042008010040001,(pn 1060171 348594360725307425),0x810406080002900100,(pn 306981 635617895444123777),(pn 456916 935848740578656516),(pn 75578 661350096387999746),(pn 85225 335757346203242641),(pn 227006 236066068505313536),(pn 9703 280116751332278337),(pn 609185 294342929288028225),0xb04100002020c04100,0x2000000000c30104,(pn 604536 777848540161409536),0x100440800004020810,(pn 28629 346873455331574657),(pn 613963 217478328702615608),(pn 458671 969518207524542536),(pn 198653 860636907609801776),(pn 190151 391117508264600088),(pn 321429 351018977225871880),(pn 633099 247340242263344164),(pn 59400 328652517987733640),(pn 306965 946255951452576916),(pn 160860 808310210985855110),(pn 80428 174868317304266792),(pn 302825 794959697260884032),(pn 154811 424096919916927008),(pn 77331 926207996568830980),(pn 44936 415357163618435593),(pn 623389 954902223747156356),(pn 9620 266061048132222324),(pn 1132549 908045958831067939),(pn 359733 357726044269452580),(pn 852623 640726931286287057),(pn 544352 830835840764560221),(pn 56450 49891630147941384),(pn 982459 739949965778051901),(pn 212270 412419545860727283),(pn 570477 609205877672168739),(pn 246389 644185907510815945),(pn 241408 820617219396531403),(pn 883930 845648260560530124),(pn 790749 69096518951203446),(pn 952795 564919409051507492),(pn 59217 658613116897622257),(pn 962312 963295244706891375),(pn 117106 808779808120835154),(pn 836961 399060366057603011),(pn 1091137 321330544136096636),(pn 209862 537163725300658287),(pn 914497 786711510924441346),(pn 585729 93556678156876719),(pn 1099122 367529238632906538),(pn 1188780 637428807418657765),(pn 224584 363139223807555261),(pn 750673 809389333400449915),(pn 954787 529513006813949697),(pn 887490 64437128422180588),(pn 206251 797351661842440814),(pn 622060 448234314873878898),(pn 1083406 241597581961608071),(pn 519731 825812286328399031),(pn 410189 542961006336989787),(pn 490786 53650138309569903),(pn 857825 889406571695626963),(pn 53323 566668173284163052),(pn 1141402 291276218020377314),(pn 959436 554922952929872672),(pn 814381 216262878042807217),(pn 409757 171006888989344203),(pn 26785 226305616146541533),(pn 828161 754915833620922043),(pn 731614 852385087451490027),(pn 706846 858790570475826546),(pn 856718 814517306632321735),(pn 505563 871753486832688043),(pn 409314 421492554130172362),(pn 771710 218615300744538663),(pn 794512 718351519042691738),(pn 49075 942057495065417065),(pn 248599 172707118544430026),(pn 671649 295834102712814111),(pn 493166 892951935109310880),(pn 162914 292913480096185449)]) else (if j<10 then (proofWord80 [0x20000100,0x2000410006080,(pn 14240 888676704661307392),0x100000040800100,(pn 28481 786430978533687297),(pn 38369 245699267838869825),0x2a08005040a0800,(pn 681201 365154085107417216),0x42208000001000008,0x1c1000e0800000000,0x406080010000080,(pn 306953 821421711310979072),0x100020404,0xa080010002000040,(pn 302277 715935147954537025),0x2a08601210209042a0,(pn 606825 268735232201335041),(pn 312285 363090591420809537),(pn 56746 958622906208371207),(pn 47372 973793185926486064),(pn 265190 410994519260793864),(pn 151339 755505659734263896),(pn 76298 61921203020825610),(pn 10625 758340495374877184),0x101020204000020191,0x100810004080810002,(pn 9518 664066018299609090),(pn 380150 741335851466358784),0x400080010000000,0x200065041a00,(pn 40177 585053566601527296),(pn 75559 89267963190050816),(pn 37780 102800509579034634),(pn 19279 738868262131204128),0x410000002008810182,0x40208000001000000,0x802204001800201,(pn 333554 603936405430747136),(pn 302231 457208303458713608),0x64a08041001a0,(pn 619829 47620759774729232),(pn 7864 114034415981594753),0x120801504120c94102,(pn 613909 664892176161640705),(pn 311759 306869826791936104),(pn 151115 727451828646887684),0x8084010002000410,(pn 189494 467009033975889984),(pn 35482 458595014549047296),(pn 75560 170555185604604928),(pn 305782 507469165632688128),0x802060c021004,(pn 75594 793242876680962822),(pn 103965 851860091661193288),(pn 170014 416755378442387712),0x282000010000004080,0x40008000040008000,(pn 56963 545701814121808032),(pn 604462 932395681636679681),(pn 307553 484970533489741824),(pn 11842 809695334618370048),0x410002000c10782000,(pn 4722 510598057721331712),(pn 152005 782994122957651968),0x8101000a080010002,(pn 37782 444706951484932098),(pn 304758 731328163504230424),(pn 179894 981142618103365888),(pn 4796 153565267355513024),(pn 306953 822530019031816264),(pn 151115 885289203301884160),(pn 609203 867994987706810499),(pn 10934 326067048636006400),(pn 104040 514813108462616960),(pn 613935 565376616872812672),0x8820010101020d04,(pn 47372 107976153852084224),(pn 38373 857374287945728833),(pn 18889 520115416010722836),(pn 76454 900059836468215937),(pn 306954 544214336925073680),(pn 151138 881163399445626888),(pn 14278 77156171570022402),(pn 38149 21952922309624866),(pn 19113 718541052927836354),(pn 614000 164776714747052802),0x2001400200080,(pn 19074 514987753369372676),(pn 75560 192161965498434606),(pn 37778 937778364082028608),(pn 1059592 817306059596140640),(pn 378972 252193574288163840),(pn 37779 22226335407031297),(pn 37964 14891761904194052),(pn 151855 903128432046048256),(pn 40994 2097341410312360),(pn 157318 448105678513901568),(pn 610390 151888561412510288),(pn 305192 274473857782415681),(pn 11861 257288231170342912),(pn 604481 393149182650352646),(pn 37853 871769011534959112),(pn 151115 799652410737043616)]) else (proofWord80 [0x10200000,0x4000000000800404,0x82000010000000004,(pn 37778 932711780138352664),(pn 757962 950989089428488961),(pn 531314 689604082607784960),0x8200,(pn 18889 475079471242723332),(pn 29074 374503261370581024),(pn 37964 570313476219601419),(pn 380224 314320856803577856),0xc02102c105820b0,(pn 494096 76045856278059520),(pn 245567 713973644550604820),0x42008000041018042a,0x200001001a00215908,(pn 302233 42152081918525440),0x80000000010,0xe08000081038])))))
def g237H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [(pn 94482 567413141491235880),(pn 798180 533742452236550144),0x2a2344010000,0x3048c0001c09,(pn 755795 386510916009856018),(pn 906694 364710972294135808),0x2008b812348db888,(pn 1190706 207129039171223552),0x4270000081a,(pn 1104134 478222434829860864),(pn 113681 306752204417269760),0x1e9c00a81fc000,0x40f,(pn 801885 162389968066914331),(pn 491212 315175325201219584),(pn 75628 336826940418651337),0x300b2c0c0c1e,(pn 548578 501661867518738432),0x142310014cc9fc11,(pn 302232 38823496614362142),(pn 906698 118039049368247433),(pn 774942 262012345200145667),(pn 840654 482887674262499598),(pn 1171286 756370837512805380),(pn 963896 860025341169490979),(pn 302231 780579187681096727),(pn 190274 428949118857847825),(pn 708458 756560077600068645),(pn 305015 474354902635118730),(pn 19498 208543121672209701),(pn 850173 835023740410265670),(pn 189572 577225529513623552),(pn 95030 134741927633764352),(pn 65220 517322857902358528),0x141600002d806413,(pn 230796 438504684069696768),(pn 745232 325988058262413331),(pn 888040 94766433367274526),0x2c489420ec01,(pn 604462 909868979045241897),(pn 906696 464303192850183193),(pn 114115 378596138738254933),(pn 22579 681153868598560342),(pn 340466 81647885971374080),(pn 189200 204514241934991428),(pn 576622 161314068446576640),(pn 191662 932153662983159808),(pn 269520 804344789494412322),(pn 1001601 172251624790376448),0x1410cb81a4,(pn 590335 898205504591114250),(pn 604465 793879156301854733),(pn 1114603 5541355317182464),(pn 43757 431868950325641216),(pn 99238 871440197873161258),(pn 439649 332514564224166920),(pn 906697 14023822383856678),(pn 625856 17799149263155650),(pn 302231 454903657293682701),(pn 94636 419480197542182912),0x250e80002414,(pn 869588 739065090903382053),(pn 1039343 228451297663860736),0x44e0000201d7421,(pn 604462 909807314587356194),(pn 604462 909829589361494058),(pn 906695 20125455557179421),(pn 99225 36372484486042628),(pn 24878 466269265710435367),(pn 474777 691563588719754261),(pn 906694 364710972151169024),(pn 246081 928507985311563776),(pn 226899 563856210354503680),(pn 80948 924743392589516034),(pn 321436 831741972624730385),(pn 302231 454960840488255813),(pn 141678 508130740179610624),(pn 1197174 388030581429051424),(pn 759267 416409073755855146),(pn 604466 91257404913604620),(pn 850073 237679078511751184),(pn 1063018 134708373531145813),(pn 1176327 6376722399098131),(pn 248150 212965559315726336),(pn 39116 70458444996714003),0xd01c000,(pn 81551 45325955004366848),0x248480000000,0x81c400025104000,(pn 56719 126341198416991259),(pn 114099 169459440940594179),(pn 869660 222705980703003930),(pn 906694 436857626702759428),(pn 5904 728101874099164162),(pn 325844 452365133922189442),(pn 38479 911679071671550724),(pn 228003 801394094157278242),(pn 629334 903757534282646147)])
def g237D7 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (proofWord80 [0x33eb2aa6,(pn 77548 258093907302976152),(pn 310335 976627800324450913),(pn 32896 568320553277403268),(pn 131522 214081113409372688),(pn 526344 804898476286216257),(pn 299237 682692068441989382),(pn 1050206 881662738851464219),(pn 1008360 210262064093073487),(pn 1017176 824120352721879479),(pn 721730 51800322105476853),(pn 459623 833955303866635261),(pn 969957 772996266921847783),(pn 404095 589309356106166108),(pn 1011919 447427910813941110),(pn 1006473 774716069587969475),(pn 399116 635871605550995301),(pn 387544 740449341946158517),(pn 265692 972824783895815380),(pn 1062781 114108222432985939),(pn 624089 935499971356222798),(pn 79388 781677761258919224),(pn 318145 386492607242392801),(pn 47130 109655991509799556),(pn 254770 767043206465800720),(pn 902822 463647792598689858),(pn 598470 767068179841982733),(pn 589274 989030960796959799),(pn 505637 146920434553983183),(pn 815688 226996201050358622),(pn 842540 85297558778350842),(pn 957031 69310046823527915),(pn 163567 883103690963343276),(pn 651910 367189376539229626),(pn 198644 266100887229560550),(pn 794577 64399150872517274),(pn 760457 194546622466305098),(pn 623977 174915659794786602),(pn 78029 256044910264634008),(pn 312255 336479596913339969),(pn 40113 970725663101836074),(pn 157016 151810323968011432),(pn 636863 704164439221908130),(pn 94405 925044800440158856),(pn 443740 289703616821533217),(pn 299219 318067494696675462),(pn 592174 266563469534405143),(pn 1085025 39636087668377679),(pn 1017177 468135099437031863),(pn 419501 172691808641647869),(pn 551789 460385662475834365),(pn 1007676 752941018778193879),(pn 516085 765543488890437212),(pn 250954 297851726027683185),(pn 701585 737628596967831001),(pn 388491 878685906012460897),(pn 345041 145821781734415621),(pn 171239 880424467866153236),(pn 684963 555234287663307330),(pn 322000 279207398438560009),(pn 78800 933422066078401572),(pn 316079 881974173559427217),(pn 47130 69088401367642692),(pn 188520 132238419004016912),(pn 900463 581183085841286210),(pn 1193472 782743024883208461),(pn 1146449 589337195835049015),(pn 1034837 16665292525342911),(pn 521425 44973211844100988),(pn 838995 428555929808867058),(pn 787014 346979939983833035),(pn 87963 909270930138918698),(pn 351855 645536491072124984),(pn 802959 672021990352347810),(pn 793986 196715201299987338),(pn 758094 156393608038493754),(pn 10062 581064162793534152),(pn 40250 323975176197424416),(pn 161146 524603788513979008),(pn 644300 262828104198408706),(pn 160497 361613778737211400),(pn 641985 987690601122013218),(pn 112854 167409810748498056),(pn 451415 516717871489188385),(pn 1191371 654157820573911174),(pn 1177737 856561345721803295),(pn 478382 892037357504071807),(pn 99552 542920416956653950),(pn 441283 318816879833286633),(pn 390924 629842609764966341),(pn 335883 233894665688735575),(pn 134607 89374062849392221),(pn 311754 872695571219808115),(pn 421490 375604635308389851),(pn 392033 946189681491179365),(pn 359206 506960125115193685),(pn 227917 499374428084860628),(pn 609424 708942824891865426),(pn 19625 872767854029722952),(pn 79647 9060002005816580),(pn 620339 947802555445369169),(pn 51704 642912620406382660),(pn 220984 518177734043664656)]) else (proofWord80 [0xff4a8a8,(pn 161148 833560614791781024),(pn 644595 473854047611153026),(pn 160538 614867840494316040),(pn 642157 846178281799591970),(pn 150632 171531278904107144),(pn 602805 387286221763019297),(pn 1202221 942553962904946823),(pn 1186537 529949662441120287),(pn 1081593 729091736359176319),(pn 770432 954766231439811070),(pn 1040488 906844656907093757),(pn 478509 769627624364186613),(pn 686223 792964320981708758),(pn 175927 818682597766192980),(pn 703711 291336864934788469),(pn 982566 830427494565213523),(pn 303490 421136522670478605),(pn 5035 919071414058898724),(pn 20143 676004181258883728),(pn 80574 570456848586347840),(pn 322297 698611242602931457),(pn 80264 830715153152250884),(pn 321060 439753320232472593),(pn 75311 327712616287387716),(pn 300655 15040174604484880),(pn 1204978 937559124044612675),(pn 1193177 346608577177719055),(pn 1145858 140614126465991743),(pn 956913 358029649736700159),(pn 199695 381653427075695613),(pn 240324 796526377741389814),(pn 791293 992721894500216811),(pn 822882 190952240042278314),(pn 420329 959670166877109672),(pn 472394 20190838728686314),(pn 680649 977512109170190994),(pn 304749 387360042198444553),(pn 10067 264651971025353004),(pn 758068 764843547301694121),(pn 614423 420143831345736356),(pn 39254 42445459374369558),(pn 761479 25545956556418106),(pn 628064 606999387207676138),(pn 94259 647302002253153448),(pn 377035 130443762517611169),(pn 527079 261251765755726469),(pn 1050488 506100463629838875),(pn 857264 175933992183572575),(pn 411169 373260457444548959),(pn 441045 889179727851849209),(pn 531645 904997915374001633),(pn 912935 430516462955548631),(pn 366081 445696653865623508),(pn 1162094 381908561511120242),(pn 1021599 988356135146468810),(pn 459623 91158070106912565),(pn 629563 996604784770373702),(pn 100414 540839147640811668),(pn 401621 854632707324495202),(pn 95474 268242452564878724),(pn 380739 539818352981366360),(pn 616263 686476048954217762),(pn 56426 404261661037384840),(pn 188520 151528303065649696),(pn 896922 968847501216790659),(pn 296087 135673284444873225),(pn 1203846 751174719817615411),(pn 1110542 924968033172463823),(pn 815688 812410014546821950),(pn 843723 18792279302343162),(pn 1122314 39459472067799035),(pn 843589 228629669240168108),(pn 200926 673918334639209914),(pn 198653 489472924101243590),(pn 794614 104183917504088730),(pn 760604 777488819480898122),(pn 624565 129909744483350764),(pn 798172 129735575762559666),(pn 774836 876335345246634698),(pn 681493 585030114211412762),(pn 308122 718624124042308201),(pn 28213 202042869588470180),(pn 94259 935237709290185360),(pn 451411 230434112528616001),(pn 301596 561215569460340997),(pn 1045765 832528634810246163),(pn 1161004 729651577076355167),(pn 714723 792097169788518846),(pn 1025141 233650061028165499),(pn 393507 245824512111157165),(pn 950676 608536686753773493),(pn 175928 975368830188649044),(pn 703715 867847307374689654),(pn 397011 681326767028417865),(pn 379121 229960586442823477),(pn 699515 518235528405146710),(pn 380196 598936274940686681),(pn 311929 608430359443527011),(pn 38792 35394255978982732),(pn 154946 649903014602159408),(pn 620376 859393620615353538),(pn 47203 824647234312033032)])) else (if j<3 then (proofWord80 [0x82ffbb2a,(pn 193746 42197741961669800),(pn 774983 880560591830198946),(pn 682083 806451914769328778),(pn 310492 773921643783891497),(pn 35368 412903724464384164),(pn 150405 910971872422044304),(pn 453181 541404573780052545),(pn 601463 229999189407967495),(pn 1158484 85732517743207447),(pn 1160656 475317591810805887),(pn 865470 584737618110595582),(pn 401788 858052039708051449),(pn 544622 973557815734706157),(pn 950676 608686220335153079),(pn 100371 112210126426209884),(pn 401484 448559030728129121),(pn 397011 975149259319142725),(pn 379122 80841670613509141),(pn 307562 503189103325908053),(pn 21324 190889984298673492),(pn 85295 52755028680754512),(pn 341041 934794585751885204),(pn 154651 637105824334689584),(pn 620967 785707927689843906),(pn 56648 269382631805768456),(pn 301558 339603073646019616),(pn 1056272 853804482362234947),(pn 598443 268089405091963149),(pn 1184773 465762298407978031),(pn 1112387 741240996513583327),(pn 815394 808420792499979007),(pn 872061 793907469520539134),(pn 796636 629865944626507755),(pn 786994 50356772829454254),(pn 956798 153375713377583034),(pn 200415 154657866474844896),(pn 801660 330460459080084402),(pn 779346 102348440959708714),(pn 699537 346595783092185388),(pn 229145 271595448546281896),(pn 916691 730817439289284259),(pn 39841 953523675276552844),(pn 158196 761097994465585712),(pn 639868 288273277409339586),(pn 113295 961877900795486984),(pn 452596 992451359793613857),(pn 1130215 10634134568054919),(pn 1178015 138691200269697567),(pn 1085209 308944618582247551),(pn 713764 629029406915174910),(pn 436026 285267649752500217),(pn 308505 730282650412916709),(pn 383406 653918740518301687),(pn 253035 204341273624428508),(pn 709909 362601624936578418),(pn 421785 810051341490060737),(pn 478217 931758090584061733),(pn 703946 159513759177989301),(pn 246808 120901457944601940),(pn 987195 876096260763402579),(pn 322004 899970985401670025),(pn 79688 685513889755780644),(pn 318736 295311485280016529),(pn 66092 860377230698439236),(pn 226593 662567470492649744),(pn 1056272 892612572045780035),(pn 598304 888234355255972107),(pn 1184901 899420903159252023),(pn 1110468 955580564691816671),(pn 1116739 522642021395481471),(pn 837819 448201348388031482),(pn 1065652 415096566873075691),(pn 815282 132429042254667692),(pn 843276 907233847149789115),(pn 199677 285196182936353516),(pn 798709 139658831839099690),(pn 776984 919107001842134666),(pn 690088 73157177302233642),(pn 342509 872267888103696553),(pn 161003 23895378028862116),(pn 644304 865586088216644242),(pn 160479 221431139004656200),(pn 632786 828271980663449890),(pn 150336 735958605571990664),(pn 603116 678344264917881377),(pn 601465 684390067967641733),(pn 1196927 406345445322072603),(pn 1159751 574925351420463199),(pn 1017172 568201121252909503),(pn 1026305 666356419211331327),(pn 469000 473616032850911157),(pn 345955 151763210785808343),(pn 382678 921759709894655833),(pn 321789 831123000789237093),(pn 663807 227899421071766933),(pn 237376 732092601303291725),(pn 307265 86718756442299573),(pn 20134 526978921642939092),(pn 80574 416921044883688016),(pn 322298 892100328227292481),(pn 80265 137100665298687236),(pn 321069 195313945761829905)]) else (proofWord80 [0x6030be0,(pn 110757 588686690538579266),(pn 911516 966324298991644754),(pn 229662 53581271848651168),(pn 89801 447888017588035138),(pn 250366 58467614395568193),(pn 1135756 880250457776392056),(pn 68550 141169766775182913),(pn 779250 63098217558994992),(pn 228407 637265470223222128),(pn 49955 264680345705945665),(pn 212548 790803509074268192),(pn 1134539 358548729247761264),(pn 31065 222270522090346816),(pn 816993 253294986456780816),(pn 831726 813754768955212160),(pn 12765 502692929830918464),(pn 174731 523130608196825088),(pn 831137 508358372915410381),(pn 466706 656783524621702933),(pn 657900 798477085685292310),(pn 138193 691515982582739800),(pn 552774 909053218499971425),(pn 1002173 235633892894395785),(pn 381915 515221279495714341),(pn 318736 169212890458675349),(pn 56574 412501569520493140),(pn 226296 352969585938762064),(pn 906370 38724602096919875),(pn 598295 665425276852540687),(pn 1165846 991500881726428219),(pn 1110321 390661557985824959),(pn 822624 671194522681951167),(pn 839000 184359404063493886),(pn 1060930 626763192018417659),(pn 125818 927270222378360782),(pn 732162 927422379628134073),(pn 1115262 980231290866760933),(pn 834274 462217615384769174),(pn 919246 209078253234138779),(pn 50202 768105275551298028),(pn 200838 733530013481231792),(pn 803318 345750781394360002),(pn 795568 92747357722940170),(pn 763839 979077424234712106),(pn 637508 132965259101417642),(pn 141621 13911516090778280),(pn 453186 171157905750559393),(pn 904795 941323634576730757),(pn 1206331 193711197074532895),(pn 537416 8391451715217519),(pn 1011573 711211805960479199),(pn 400627 919860818076403455),(pn 464421 357632301300325365),(pn 648759 610896983840552949),(pn 177186 808895261989011164),(pn 104284 271749092098899300),(pn 114905 632088313055409544),(pn 459623 392762905699014473),(pn 327335 162276591358139557),(pn 100414 829210261306299028),(pn 401659 317263257690262865),(pn 397563 909262808983151941),(pn 382210 361235749163767061),(pn 318736 259397587242801506),(pn 66018 929745343644263816),(pn 226297 642239327943348768),(pn 1056312 61016938279946370),(pn 1207628 391398978864095755),(pn 1203662 319775904758532151),(pn 1183594 337345127211475135),(pn 824543 826097602806973310),(pn 883865 440023307259874302),(pn 1098720 654932474929360875),(pn 673620 937740540522315758),(pn 201074 248143058006933162),(pn 208688 519918099001899684),(pn 834753 789341883927358246),(pn 770049 519505755667934810),(pn 662344 133935917535509290),(pn 231524 897218099201108136),(pn 926099 587746497098850979),(pn 77768 394037095704709772),(pn 311646 1657832175970833),(pn 37658 114959105491118148),(pn 150632 171606045812236560),(pn 602527 533502678640002113),(pn 601445 17442300732418310),(pn 1196886 531956702679573531),(pn 1179510 560961743379140719),(pn 940149 57551531686642047),(pn 1040513 136211749568579069),(pn 551720 357223333689039861),(pn 1026289 810427293769687031),(pn 327266 63859494915506140),(pn 402369 820923007779405157),(pn 719313 202796453145868693),(pn 459401 743772969420707693),(pn 326447 395240205644454133),(pn 96877 591900649057903060),(pn 387455 43695923684563537),(pn 340894 365865114949015877),(pn 155241 795541002282886420)]))) else (if j<6 then (if j<5 then (proofWord80 [0x95d52b5,(pn 176559 169495084397908852),(pn 781722 884990100753225875),(pn 1157707 447830175844225627),(pn 173238 651975795337217908),(pn 668382 630533358066108560),(pn 1157599 70042052672967173),(pn 169991 923684738365275188),(pn 564487 397274930045718669),(pn 1006368 46921218755088801),(pn 166302 464528506948825140),(pn 448785 815459365503993994),(pn 1006255 57165593589403965),(pn 162613 5372069367653172),(pn 326000 539795512057129095),(pn 703906 609180027605205),(pn 158702 174027610760287796),(pn 200854 8830430659364996),(pn 477117 113692058746966123),(pn 154791 344935020688181556),(pn 80430 60529797382060161),(pn 250323 615018554589925383),(pn 151175 675006883927817651),(pn 1178376 953042107811971198),(pn 401333 270454896239988653),(pn 147928 948967695493231219),(pn 1072120 248311868750149755),(pn 401222 586612651179659083),(pn 144313 274535752934483123),(pn 944612 606162946567708792),(pn 98871 224213228404100833),(pn 140476 236923126049527987),(pn 828911 24338585731633268),(pn 1156563 714793643555507839),(pn 136639 197058561907739443),(pn 701403 238076674563696753),(pn 778649 876982288029273625),(pn 132949 733398662144442227),(pn 588062 983611135582224494),(pn 400742 956699957996375469),(pn 128965 117329639788884403),(pn 462916 380588460213639274),(pn 1156197 74636577685327169),(pn 124980 496756949084382067),(pn 325963 573119438017511527),(pn 249362 49068673295011005),(pn 120110 405446297902486259),(pn 170120 867357979648843875),(pn 627017 624792573984590925),(pn 115978 210921086245242163),(pn 40251 753726251040247903),(pn 1080226 452415624491650013),(pn 111846 18647605680109490),(pn 1121669 715021375009091676),(pn 777877 395859208782170995),(pn 107861 393571246626662770),(pn 987078 306970968064309337),(pn 248847 830455280677899005),(pn 103434 39881306775574962),(pn 831235 385025731861575764),(pn 777582 238946553140693607),(pn 97973 639249154393851762),(pn 661224 931281924583340112),(pn 248511 167172160473287139),(pn 93177 339418535122778098),(pn 519549 613203849214314572),(pn 475044 97492973082069349),(pn 88454 828816010497304434),(pn 363706 835384796673495112),(pn 399338 655310729863973087),(pn 83584 739757296572241714),(pn 210225 168742987713364036),(pn 96948 92524589227329623),(pn 78493 283013955081536818),(pn 40214 859116567467135039),(pn 1079048 130537646690682841),(pn 73844 561639731276871345),(pn 1109826 543894556229636155),(pn 1078900 552081317796071251),(pn 68826 894124553155437745),(pn 939816 162208342788003895),(pn 474269 310597255512934077),(pn 63440 278216758359282353),(pn 769805 780522129480591411),(pn 96323 189928209766565435),(pn 58570 191409844243710449),(pn 611601 675337657612730414),(pn 851740 413180372581959081),(pn 53183 575502049447554993),(pn 439230 110407810325235754),(pn 398231 816958650153714975),(pn 48018 331782550559694513),(pn 281026 77287529833512998),(pn 322524 68792660233766049),(pn 43443 397384552871661361),(pn 132266 921250375798439970),(pn 397936 660045996659917857),(pn 38868 467490086085230384),(pn 1194794 840126879664384030),(pn 171106 266688037776933791),(pn 33924 589203277504081456),(pn 1024784 386378674205423641),(pn 850967 932198037265990411)]) else (proofWord80 [0x40c11a5,(pn 75857 929654452998967553),(pn 24811 178154302442049172),(pn 326143 65146051335881028),(pn 321178 932283631712355386),(pn 382828 801651821840171282),(pn 80668 765961297502228497),(pn 156152 68157646027428622),(pn 708433 679660051446416512),(pn 322358 370412780688519370),(pn 156028 400437510408639760),(pn 68847 882014846357668104),(pn 630509 975069916975355988),(pn 151435 167987185490363426),(pn 99465 726843620723609872),(pn 935125 698445710074121288),(pn 397936 725876045135561796),(pn 14481 849377012669550721),(pn 154754 493106883498479630),(pn 699205 981916507050001411),(pn 104279 877723451758217280),(pn 416755 858907701897921538),(pn 75857 917194855950406224),(pn 302840 307098405369562789),(pn 39338 299926879173411201),(pn 4731 878970458367082528),(pn 302840 251858093992252038),(pn 80577 688473886969106512),(pn 306972 665926213157078564),(pn 765024 965928876579001408),(pn 605959 478765181338846211),(pn 108836 946371663862243586),(pn 21421 589138635047899908),(pn 342745 426216855364764164),(pn 648223 486967973608955924),(pn 341269 413396272973482244),(pn 324683 818724202345697348),(pn 360384 978025991476151364),(pn 37872 323592357058463809),(pn 77038 287282058039657494),(pn 170688 880392500802502913),(pn 153500 294511748963241360),(pn 651688 323791890717672259),(pn 7106 902333199589217344),(pn 228167 814964441804973328),(pn 58227 742197142942413057),(pn 629339 11890060652381714),(pn 120717 246304164419524864),(pn 191426 764577754679739941),(pn 114966 166417929089929472),(pn 1065802 505591796960071312),(pn 643425 986702566708478483),(pn 75890 795293270589096192),(pn 630744 980910614398906444),(pn 303142 992686959256928774),(pn 921213 253929841029300561),0x84840216a264101020,(pn 341194 545837473895023116),(pn 160930 552829974914605329),(pn 4826 748949123368751376),(pn 85004 347527617420800288),(pn 7171 424107650605930500),(pn 114743 445674918156698376),(pn 23908 281943658210603264),(pn 926857 35149576102023316),(pn 379047 322977299157238293),(pn 94761 812729926264111376),(pn 950455 825546841562354192),(pn 325922 276325777226138948),(pn 379053 210255342930233344),(pn 699284 381739977833251113),(pn 460468 999174896423612672),(pn 626968 132768499154302374),(pn 657761 790689831551546341),(pn 488521 517498046050885420),(pn 828060 556589607921595789),(pn 52376 514967524842451125),(pn 457825 216596481198650667),(pn 1035814 704961931477415283),(pn 51417 255001383807528341),(pn 428899 839156438783332651),(pn 110202 50402230771561819),(pn 655013 141940728710081173),(pn 401155 89367010377021226),(pn 469076 538070735371040069),(pn 49701 656009535327348645),(pn 372820 7737876456723753),(pn 752389 703108070043186475),(pn 653242 199338873478751301),(pn 341533 374995506545321256),(pn 884583 681841097559536911),(pn 652209 149581636297334997),(pn 307885 486953558017570599),(pn 1073446 634864500178351348),(pn 46713 191142984434883957),(pn 276008 558403028524438311),(pn 110054 471945902950855898),(pn 650253 735598239674047061),(pn 246492 867137129382358822),(pn 393369 366471051944588485),(pn 44997 592151187496409045),(pn 224060 959790412114092837),(pn 884472 997998853036225712)])) else (if j<7 then (proofWord80 [0x5c188834,(pn 81767 590149925862981904),(pn 123161 240622908932571913),(pn 309389 234474399347253505),(pn 380261 471155322264326208),(pn 189196 763170349731095105),(pn 58403 841056701596893384),(pn 623523 226305298324128792),(pn 643153 830202694796091481),(pn 19581 292618139138541618),(pn 387973 146629141932049445),(pn 609299 59757877231157381),(pn 629564 426023953238865408),(pn 95408 960874213552423686),(pn 604629 514283287306077761),(pn 614591 326364448908792385),0xc944022481060c6604,(pn 680468 688147508218659620),(pn 28488 154521056351125601),(pn 40168 110361510117396544),(pn 817786 557382357608923670),(pn 56779 968016672817725536),(pn 646992 25768771991381008),(pn 909083 299767728973551696),(pn 229478 942179002379608705),(pn 307121 140325119854420042),(pn 918523 420991392131330424),0x60d0e040830280060c,(pn 113780 824634889180061764),(pn 108633 477377494081368608),(pn 457636 176878949865378852),(pn 157321 941420150496433420),(pn 397197 609372668783510661),(pn 925657 694486771698237532),(pn 303119 204850336474170372),(pn 18944 812374102362048577),(pn 378971 140020532165017792),(pn 633185 792165181645931584),(pn 609799 860348978666342418),(pn 99484 470046815796928768),(pn 916222 487528181692961040),(pn 436008 704419394087882949),(pn 323560 720389508695856212),(pn 341270 627981622430286016),(pn 618727 220865662104654912),(pn 157332 317857726869848134),(pn 930602 645502217131409745),0xb144020fc510111058,(pn 302846 34317293199234368),(pn 104151 778528823084122337),(pn 323556 108071249753673796),(pn 397864 5918474083811397),(pn 323557 409337737618933825),(pn 378675 996614429889498116),(pn 76818 313246771192579077),(pn 322357 145448511761027140),(pn 303436 334719470164771601),(pn 175060 485183599560184081),(pn 155944 470227849928052752),(pn 39333 83632478179099969),0x8404c205a41010245c,(pn 397588 520835387672956949),(pn 80506 226542564367991057),(pn 20167 228087560332972082),(pn 39333 88084399413592132),(pn 316824 344650172132230216),(pn 435716 810589447534166789),(pn 75890 795799062308471905),(pn 539845 173769742577828113),(pn 113632 252065604458004528),(pn 86506 43850385041592332),(pn 75785 579886093919373636),(pn 14520 258233869765980529),(pn 162055 873149346790900808),(pn 397936 716815999332598851),(pn 114020 553507544743629072),(pn 931570 466827780844818704),(pn 340157 980022579522506949),(pn 931491 725893072988474516),(pn 341268 676776534869367072),(pn 623427 681290232500338736),(pn 340624 966272057455371394),(pn 477255 429754447829815496),(pn 155856 617386492849046037),(pn 75872 686332019483093585),(pn 5479 883555451449776144),(pn 77108 617529653815681281),(pn 195112 402148279818784784),(pn 106567 435060491235401753),(pn 325924 388843868822192532),(pn 256505 507405773207241829),(pn 474635 882534337468518705),0xd010c4e944a513100e,(pn 700316 820115147402331332),(pn 14555 854688076314725450),(pn 383415 629972332190302482),(pn 99466 16199879854985505),(pn 382969 414258587634712850),(pn 83013 826307152436863233),0xc0454484a381a51210,(pn 20444 194144091803551040),(pn 907958 256497546769731652),(pn 397864 65080993392447748)]) else (if j<8 then (proofWord80 [0xc605440,(pn 229772 680568556582543893),(pn 66114 319782357319748900),(pn 39108 277522443935236642),(pn 4879 745900086716549379),(pn 62571 950439291446920580),(pn 10100 27048160241267713),(pn 383766 141982655706567008),(pn 463396 191787257286035588),(pn 321790 818051231657890054),(pn 39408 304989998334222688),(pn 14188 2077333781620740),(pn 4782 535207300342751260),(pn 236782 501734463442195747),(pn 302417 93299410385814024),(pn 680117 925222323905234176),(pn 232947 844265897327269127),(pn 58220 525178195160335746),(pn 99502 319070788223864832),(pn 607709 687918828159263828),(pn 340909 688217370181911298),(pn 118060 32445288763392208),(pn 24849 493658752893718529),(pn 456996 181525080464952368),(pn 94893 623081188230005271),(pn 28482 377458265035411713),0x1708141c21543060c0,(pn 377886 386475957191448624),(pn 264753 516697648780806229),(pn 38667 947307005494051096),(pn 174881 212583356652356161),(pn 614313 796624648682636353),(pn 4796 446510968123441429),(pn 33205 617674921464414727),(pn 104044 541295083917547537),(pn 39551 846303438611694088),(pn 29017 598893856054609349),(pn 312119 416404234791305537),(pn 916177 506661421196337281),(pn 907912 354513386844205056),(pn 104558 670835235842716240),(pn 79131 938992021148802188),(pn 416602 443846760224203013),(pn 57186 226324410582007938),(pn 37890 213588874243899457),(pn 47299 494224119653024281),(pn 85157 396706477459505761),(pn 380226 28662875569326129),(pn 379864 956068226271812116),(pn 322310 182027837370271269),(pn 33353 877301585126654471),(pn 614057 380740964819518785),(pn 921553 219347139016085648),(pn 629283 153705485001200673),(pn 380456 37545617877374988),(pn 454014 738543649545666721),(pn 99397 123454475037917634),(pn 104280 94475737836304448),(pn 6507 306624744064093284),0x219000864544830c05,(pn 42725 281532496728113922),(pn 99336 296957214544117760),(pn 935070 285826041267899392),(pn 416477 937226217024590592),(pn 108845 661960799139545090),(pn 59712 715193745673339216),(pn 8321 84899448384935992),(pn 82065 7111784882274568),(pn 368713 534180765231743509),(pn 61542 90943141089837507),(pn 118455 770539539872973136),(pn 914978 619735613629798448),(pn 396983 156755310794253329),(pn 538949 696028457151255561),(pn 19793 406075823970126600),(pn 397862 425743653570380304),(pn 28562 195934030615282200),(pn 28488 708430008559077698),(pn 921009 400377131645608192),(pn 381368 78322916707812416),(pn 153485 147989499093984546),(pn 57263 891075722429940505),(pn 85114 147758302759495704),0x5146018206a5081440,(pn 170306 133128737267455240),(pn 151634 646310243046294083),(pn 28371 964984319616847938),(pn 109281 37313707441414176),(pn 683590 255410079836442880),(pn 434905 631337337201037833),(pn 58367 241250237298509250),(pn 307064 865543098259759301),(pn 906732 917845976773304412),(pn 233535 784705735990132998),(pn 160784 135106497029194114),(pn 9555 994691418936451140),(pn 927982 340905173175558275),(pn 645811 507340345090777216),(pn 531303 250531920256307212),(pn 699224 716828633418719424),(pn 1059000 129839687787096064),(pn 833613 192975267872136216),(pn 152600 731024554460775948)]) else (proofWord80 [0x1917,(pn 85230 901120253780067461),(pn 932724 383842363040174432),(pn 632898 854889425758607393),(pn 384301 74813486990690440),(pn 397270 328168424413627160),(pn 99484 180404478138257536),(pn 631699 678039986081636624),(pn 329542 454849739107868804),(pn 397591 975100974744405512),(pn 42507 951342597367187586),(pn 311770 96942382990766417),(pn 78018 238752509588410452),(pn 157332 317715616401459284),(pn 188918 907293336497366037)])))))
def g237H7 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (proofWord80 [0xf40767c1,(pn 940784 367447396839329027),(pn 635754 640594225172987969),(pn 340161 573003307836506226),(pn 618789 559909402569343008),(pn 303746 915052367558739586),(pn 845303 600611609209415948),(pn 1133367 955888871732936704),0xf56c16f88a20c,(pn 5614 764477573194842352),(pn 565619 129538152461561856),0xa0364000000000820a,(pn 160592 751422609253728625),0xda04159298cb00001c,(pn 23883 961199761689674048),(pn 779708 746594588648910852),(pn 324960 244332917835169792),0x5823523448309c9,(pn 916498 817109327746170881),(pn 124847 563890866749233350),(pn 65526 915006906731998239),(pn 717860 305832892269707316),(pn 152126 416444554306928956),(pn 646827 168294118117867522),(pn 244825 288783962992638849),(pn 627208 952214908278065197),(pn 165404 955789443743941008),(pn 303478 791753216243017408),0xc01b9015888036c0,(pn 175908 152121510466590469),(pn 179449 926349046518120448),(pn 132490 280545318448726480),0x34c8000000000018,(pn 48337 463669152286994050),(pn 223428 691924005670313984),0x631a7c054d68b1,(pn 699222 538160836993486081),(pn 341819 330595464872748028),(pn 336488 247691621970601729),(pn 1025989 809079107577701401),(pn 767580 280041380040540408),(pn 472364 480739452628767973),(pn 877210 741048653407670953),(pn 209504 325336643271604224),0x701e2807820009b837,(pn 401412 608375077630509145),(pn 1059222 285945237105803276),(pn 18024 837585754868762962),(pn 253754 174706503892223620),(pn 926174 638201666001617013),(pn 689508 543085093057266448),0x5a32ec010be,(pn 642768 735387402608224302),(pn 525290 632381689592020992),(pn 9473 736147386825753092),0x780ec360009010e,(pn 335306 973430989392642333),(pn 85094 830699020836798469),(pn 37926 588896848801891594),(pn 33852 227312592480043523),(pn 5312 664274733240159751),(pn 4728 635501333442463744),(pn 5146 715424437148061188),(pn 127858 277720061030564352),(pn 37840 703803189315371524),(pn 14222 656438626637712640),(pn 47408 205461835289928961),(pn 10127 769995849553421569),(pn 47247 13477313725597187),(pn 108616 233086824327748610),(pn 14204 788390573262307331),(pn 14167 966954629210898438),(pn 85002 671003267999597059),(pn 198339 538084575920198913),(pn 203066 82221236936376323),(pn 1025343 828222575547187488),(pn 146448 848977763402122245),(pn 75687 208234212258940703),(pn 19407 202857362926797573),(pn 66113 418990572726658825),(pn 118079 411665248285229058),0x70b15010e01011c04,(pn 80280 734897845457259526),(pn 42521 406376108095963137),0x200131801000518,0x80104030003100002,(pn 122801 633209520249440021),0x3e0605040102030401,(pn 14314 677631290460602884),0x101040200000c8d00,(pn 9481 700202585918670085),(pn 118209 480126103552395264),(pn 9445 454949067455079939),(pn 9464 482389199574533384),(pn 151503 543395464702591744),(pn 29367 216577440603770113),(pn 18889 473532402682036242),0x2b0503000d00010608,(pn 66187 353480684670615814),(pn 28815 41201401157452033),0x3030034000105090d,0x1a2500010001000807,0xd0804010105000402]) else (if j<2 then (proofWord80 [0xa180b500,0xa1186000008c84b81,(pn 1076118 151270316355096578),(pn 269791 297483112881061888),(pn 477259 355571674486407547),(pn 99181 524493738235758164),(pn 52280 525550199253553234),(pn 1113305 734617222151667712),0xd1800000000072173,(pn 1058663 254076209607478770),(pn 313502 443539454079851008),0x239b600001801,(pn 18889 499718852427188768),(pn 359470 621758241723911913),(pn 305644 102557293560759696),(pn 63689 166214034758828497),(pn 11805 916207178022468621),(pn 241455 671004041824617559),0x5f510800003c10a8,0xe2021e235694c000,(pn 110680 905232071808386051),(pn 521821 956437597657854348),(pn 788667 196210983590934835),0x1a024f81d00,(pn 37775 350266874206100004),(pn 467339 145821785692308592),(pn 813438 582839112318648320),(pn 10079 164538052489708046),(pn 302634 689694792863987467),(pn 175034 325545509346274278),(pn 462645 124907530290077219),(pn 210673 22277640819458156),(pn 192674 770048446241964035),(pn 7713 778952559088778904),(pn 102859 44955004527952000),(pn 1050293 107355938692530199),(pn 1095589 64563130269927595),(pn 40352 901387397636297604),(pn 624090 245502324076258712),(pn 10281 925295616555164291),(pn 715022 850680333451264000),0x140998c18d090d0,0x14642008ce800000,0x2e073c821289,(pn 190998 41043021909196800),(pn 8343 10669804251943043),(pn 756902 749698888560742666),(pn 211440 332795936722915012),(pn 73169 29367929864454606),(pn 365983 402422399387500544),(pn 9452 902787473963622643),(pn 340399 497774764206334795),(pn 95632 837244086627860520),(pn 32466 269569728810844488),(pn 538349 782537384597919819),(pn 1074371 602511732271219013),(pn 907506 311070514317367320),0x8110600002c0c700,0x224bee08b55004781,(pn 292204 603550621563981830),(pn 694197 961045072359718912),(pn 454281 48774217486565388),(pn 231597 632103778403708832),(pn 425345 512366254680718883),(pn 406123 517526789488398469),(pn 906694 601255264948400528),(pn 502301 383794171468340490),(pn 347232 395905603959203328),(pn 605643 503543119533900424),(pn 521255 700128774488252423),(pn 321360 152048031053516890),(pn 916728 250598618227071148),(pn 158494 425169590151545728),(pn 608320 542943239959744515),(pn 377845 434740075849580544),(pn 76163 508655379313071308),(pn 611689 874550690352231296),0x14635c0000600,(pn 85002 596691662229897216),(pn 66431 868719489035507891),(pn 907615 135582283720310822),(pn 156818 78776128314540064),(pn 297848 810703278900772871),(pn 235540 733554397873901600),(pn 577368 160106299315914332),0x2046f00000b5617e,(pn 493662 579267749391126214),(pn 226821 877130882004739584),(pn 87392 55804055045226765),(pn 585672 850695923055890016),(pn 910452 326446578933853324),(pn 107482 274262237724141185),(pn 910993 490293177506199835),(pn 528905 95621382925100086),0xc03eac108400001,0x50000006640bc0bb30,(pn 196256 218551269060475081),(pn 881074 980742970052595979),(pn 99276 341379559200621431),(pn 709715 854038537730010544),0x5ce4d0a880d7d2,(pn 133739 167152081902900992),(pn 1134567 535070779993223209)]) else (proofWord80 [0xce431320,0x1e412800000000070,(pn 340600 682722629998338048),0xc0eb5818cd00fb2065,(pn 1152283 417171359895257944),0x3c0e2000002221cc,(pn 168949 118587030724411840),(pn 761555 609950243335661124),(pn 654060 750775814200516803),(pn 491175 690930781643866115),(pn 158801 695832272172793772),(pn 94899 561415959900062025),(pn 239300 988204565288466449),(pn 103931 334639154249072640),7,(pn 610088 15505053873864704),0x1ccd53c19fa82,(pn 963362 762505407623593987),(pn 114599 676982220839976960),0x1c45f00000610bd0,0x12623088241821e88,(pn 316988 850162624934969344),(pn 7099 6078225603375150),(pn 255151 246914506648781383),0x98c00000000000001a,(pn 61598 314715640366154752),0x2c84380000e206e000,(pn 14204 675307000974147584),0x2087d0000088141,(pn 915600 698063419148088896),0x22b66000000000194,(pn 273897 257981876892237824),(pn 4787 218934710139092992),(pn 227910 675952186118382086),(pn 683710 152745766208143400),(pn 761942 854285208348905122),(pn 264452 525310391246567477),(pn 1024871 124776251716731199),(pn 604847 988681687749003554),(pn 15476 976607516713549984),(pn 276960 632620476386280965),(pn 1043053 274515952122951716),(pn 19188 865649222055580397),(pn 759596 285080998147784708),(pn 39080 99774374009548384),(pn 949195 663056800575774720),(pn 16567 23837358047092808),(pn 434652 144085563221213187),(pn 80709 133650097743608628),(pn 7849 189456703040372800),(pn 1047077 908172029929278553),(pn 1060357 553436686989295916),(pn 680267 859811397919840931),(pn 195836 421635884365383704),(pn 47703 370143446852051843),(pn 141670 994486089356411059),(pn 463411 424331415684644864),(pn 718031 95523961850560512),0xd6448e740152d2,(pn 125818 486773494040231936),0x8491fcd0e6110b523f,(pn 661152 625926048651034759),(pn 908339 591517772549483630),(pn 77384 683428026882457600),0x2883b00000540b8a0e,(pn 245563 57109221551203428),(pn 340321 567764643689005056),0x302de9482bc0f99c,(pn 105238 716550709409919936),(pn 1111823 242825333167683610),(pn 42544 699617598697359455),(pn 38270 365646609008821643),(pn 17256 939882561614651792),(pn 675282 421321241970850562),(pn 1065194 494730196138395668),(pn 1081529 407523740747793295),(pn 185338 969737159889140928),0xc0cfbc1e5b02e2e0,(pn 542417 388089948468412416),(pn 4732 244146696127103042),(pn 736757 140148992116523008),0x40645011fb056c0,0x9175b041920,(pn 765134 168630188392936706),(pn 443922 186432212151042048),(pn 151325 126829886956143034),(pn 625510 644802505846868632),(pn 19887 16116826637598720),0xc040400001c04,(pn 651738 311988530271748096),(pn 194315 697628025996450949),0xe0621560905e8805c0,(pn 90227 792887669886603264),0x3050244a0800005126,(pn 925639 179992320724042222),(pn 1133849 877080444388808871),(pn 378121 360031745303990338),(pn 169821 675367581509224961),(pn 604462 924479857181982720),(pn 963482 954572782811639964),(pn 607977 885280257114636294),(pn 10035 28776098105447232),(pn 314855 921456091479676549)]))) else (if j<5 then (if j<4 then (proofWord80 [0xe870524,(pn 609259 930675617626003254),(pn 56968 288642087136674600),(pn 108172 830476111937951811),0x85248071d02d9c0c7,(pn 1114540 792841498018318502),(pn 907755 128049529232961672),(pn 110902 449031788112384705),(pn 1203613 512057522476040263),(pn 352011 872411979091254505),(pn 794339 8886688547342333),(pn 233741 17580013218728961),(pn 115812 236912128144969603),(pn 935920 609047736861610051),(pn 1124516 14906859312810215),(pn 304343 321762269539336203),(pn 35016 603055756893344518),(pn 249068 95617571374546179),(pn 358395 573403866910699594),(pn 916366 601770059274338412),(pn 608495 309783769882435680),0x20831800009005600,0x24454f88eb00000000,(pn 12041 425253125388132904),(pn 265720 736695767665215520),0x2186c446a72076e0,(pn 619515 452989370287582401),(pn 18745 555377529310609408),0x1c90480000,(pn 529565 526654655958615440),(pn 606713 412597553436353177),(pn 884115 736864136807557120),(pn 526839 627809997497254162),0x1c0cf00000,(pn 153505 752903922589641244),(pn 33430 138760053970280496),(pn 469360 112511453990225168),(pn 122781 534327596602090508),(pn 151115 966413194153690420),(pn 76051 314129886059311356),0x3f41f480000424e9e0,(pn 459250 141307131469496320),0x382ec006c28266,(pn 245959 915018669952354793),(pn 739502 299798905372571456),0x60989800aa000030c,(pn 750856 273068701112259614),(pn 49621 669500684656066595),(pn 1034866 31548349638770688),(pn 151795 959918073695174656),0,0x320e8408a2c1c3d317,(pn 931610 475615464758051509),0x349c63114052602c60,(pn 81829 756768212721074176),0xe10f0005af990ab42,(pn 292786 725340604506301049),(pn 785126 233213065497223814),(pn 651760 424090966867059630),(pn 29769 104487659140773288),(pn 213987 173256140847464456),(pn 103912 387441262603010048),(pn 135890 246062472660254720),(pn 377845 815319326772957924),(pn 325788 144435085882031744),(pn 781551 655784703170969600),0xb40582858c0000,(pn 196555 822714153607364610),(pn 604518 270516840271708160),0x8049e00000488a000,0x942abc06a400002924,(pn 771875 572506485251805470),(pn 303091 699161036072433940),(pn 18675 34886584433604753),(pn 109281 753358489065545219),(pn 409666 589437179277082624),(pn 39822 611735282644091216),0x1c0cd00000602bb4,(pn 370286 737538663701312336),(pn 125659 307749551448633344),(pn 455857 822104304339230832),(pn 189449 759751069594436841),(pn 913849 404011870387489009),(pn 973604 883311747924122500),(pn 935213 56387251803538449),(pn 963367 333772828858204282),(pn 264856 45567451942898330),(pn 687879 86529267437142120),(pn 21898 855434108604022784),0xf045680c5b8934bb85,(pn 392632 231639367316668416),(pn 379633 993036942579247104),0x14085c00005c11490,(pn 489724 438640218259587076),(pn 726670 31485374707864666),(pn 217403 778239339645847257),(pn 152321 759988311740404704),0x2001600,0x2b700000803,(pn 698910 239464707491686940),(pn 906694 446677364709917436),0x602456021a000000,0x15a3033a000038c]) else (proofWord80 [0x7e22e71,(pn 604833 550004403361021955),(pn 342598 708193238592782336),0x582a8000000000000,0x2c04,(pn 625757 153824620937216000),(pn 114161 134466591516525734),(pn 608666 494360982787194940),(pn 81998 379961505231554560),0x40a3000000000,0x148778000022112,(pn 473066 463737585052353904),0x2f8e0,(pn 217266 96225524337758208),0x15c9d8108e101f,(pn 643541 240824215426646087),(pn 29226 867864301874586416),(pn 628960 185942404224778246),(pn 233757 142037600709407232),(pn 585573 443875900510044160),(pn 135915 574616357237821080),0x38,(pn 90462 832937472010294725),(pn 44300 820507820425872390),(pn 75557 926820653260328038),(pn 605618 427243346421089984),(pn 11381 641124336589865016),(pn 148533 790141559852943490),(pn 930345 927881246757734414),(pn 472374 629777603533733888),0x240ef02413a,(pn 319963 719741603093466417),(pn 98176 53445316385558017),(pn 207784 141020077781995642),(pn 302231 565363585410671816),(pn 305047 538349933313681216),0x3415000000305e600,0x181edb923e4227004b,(pn 76747 312681735997195311),(pn 4920 668982420022756536),(pn 913517 355315442382540681),(pn 322153 938503263620753408),0xa0019a05bd901,(pn 1194768 871414300618982504),(pn 954329 190946267498841558),(pn 615273 82467875298002688),0xc4222c0ede90f2800,0x7206a0000000000000,0x32ee800004b932,(pn 151173 373527058989850256),(pn 332336 897797088329415168),0x160fa301b5e3824943,(pn 972807 495471147342667881),(pn 349513 362574666889166848),0x303fe000000,0x301be00,0x12c9,(pn 170005 222668062059495975),(pn 302231 454903657293676546),(pn 308653 414519106265974784),0x610e3b32078079240,(pn 92086 150361040161865728),0x1428900000,(pn 385111 236256370437984034),(pn 14110 638270921693993056),(pn 256299 324472930846357249),(pn 935028 568128887647141888),(pn 47552 823918401603582269),(pn 379088 375944560026073072),0xa0,(pn 311824 722214607639569412),(pn 1038920 629610430416851077),(pn 453604 932421861507232745),(pn 803331 514500594664744512),(pn 217823 914749381098754276),(pn 347093 936931337754641446),(pn 428861 935350031247786055),(pn 775076 357568627584009324),0x2d15052c00001c,(pn 17616 784952382403379457),(pn 730051 735274980399628288),(pn 18909 642057921987694829),(pn 718734 724737281835401216),0xb02e800000000069,(pn 185648 32780542005192864),(pn 235239 423186977547129096),(pn 906772 619258355934529741),(pn 227010 716387381136588800),0x8054da23530,(pn 579820 824240363296261187),(pn 870693 168039776367935488),(pn 94492 654445069253869894),0x2813d2008e921c28,(pn 23261 418441393966153728),0x100c320c,(pn 1040428 148679298628723955),(pn 151679 400935717469159427),(pn 311390 263343966400946940),(pn 641781 891890311395199425),(pn 620706 392739098956660736),(pn 28402 270842067252697520),(pn 529218 605028429276388070),(pn 11613 390465531292174865)])) else (if j<6 then (proofWord80 [0x2841c,(pn 809903 361807513671286898),0x306a3aa936409c7,(pn 153882 739073942720387920),(pn 646226 473393591402607491),(pn 547794 512090858418903955),(pn 951328 711955578559103849),0xc07f34039684156,(pn 12979 634420066482651186),(pn 329975 359046855094750736),(pn 1171146 887751672013013043),(pn 577384 530659265604944595),(pn 956856 543660741167942912),0x4a3330000104,(pn 264452 523748210094643776),(pn 1057810 92162800527952417),(pn 604804 364619964541963668),0x95100000000030,(pn 631616 517227074755232192),(pn 560339 907320656038993950),(pn 528905 46081503603300623),(pn 1142891 953765363709116416),0xf00ea00000000020,(pn 313151 927571654303548545),(pn 1105033 762070281850544150),(pn 1092056 472535695048048640),(pn 832186 384234394645696923),(pn 173161 913402157653032960),0x1e42c990f1888f4031,(pn 558576 50743243865112661),(pn 190106 451986327966187712),0x390b35003c9053ce,(pn 351963 877032110407548928),0x1902f8000030508000,(pn 9673 451097735550730240),0xd05f2e4927,(pn 63466 22991114094510080),0x58331000006868c00,0xa018a00002408,(pn 302394 449181379793535022),0x341ea0000281995,(pn 615999 120245426135081856),0xf468000001c1c9601,(pn 179449 930859672711999514),(pn 670675 102342752709542375),(pn 911822 559567089882432405),(pn 5681 597189397369988352),0xc0570816a00000000,0x8bf1028e0000,(pn 9714 516598004585070592),(pn 455966 628845230098554310),(pn 36335 595736379445886976),0x81b88822e904938ec,(pn 923228 297195511649722578),(pn 94993 311092024617110710),(pn 611712 639825776056729609),(pn 975159 708196433291117529),(pn 739643 836435789657759756),(pn 415568 304836449404307506),0xc1670c80b5087be,(pn 609587 672037280496800752),(pn 723721 290810209109379842),(pn 853113 952325831512574247),(pn 491476 872695241406383023),(pn 908594 379350563964846093),(pn 40043 343655555173613032),(pn 66417 901671360200028965),(pn 664712 477717014693150720),(pn 31324 915635777125643187),0x43b15b100000000004,(pn 23907 285438402407928320),(pn 967495 423432923214782464),(pn 10704 707574705482940673),0x6807d6143e00002,(pn 309333 451373145443281653),0x58163301dc0000110,(pn 221509 934981793354301440),(pn 14489 486092729491603958),(pn 718914 580491177589473280),(pn 8904 41193714230535208),(pn 706584 85175651105288128),(pn 484932 861973789383381059),(pn 321445 873838351706260416),0x180b4c8c69401c9b,(pn 7821 419487252875129879),(pn 256778 678568135126157655),(pn 1048365 367090036514758727),(pn 812307 653839364674630001),(pn 907540 902832083690323992),(pn 6253 536071278375627072),(pn 946834 479815363865348672),(pn 226673 604737057802944512),0x40d34,0xa05300000e0794c,0x898206000010422900,(pn 1159527 755814323875741766),(pn 479379 429353679846988041),(pn 426138 308889020419014662),(pn 8047 403537076720762889),(pn 35122 601033191313637376),0xb07ee0000000001221,(pn 302231 536143110999147287),0xa825c0000083f44]) else (proofWord80 [0xa0f0f854a,0xd006f64a94c1484,(pn 691509 655889147052027753),(pn 662016 751317289000958081),(pn 335288 23815398983401472),(pn 9785 790845345767596513),(pn 765339 270718247531546468),(pn 27965 264042991623864340),(pn 144479 861426184410898432),0xa01f904911043a073a,(pn 982331 781233672118208038),(pn 966042 152082113938076308),(pn 16652 804713027719345636),(pn 709558 646689396326056065),(pn 747318 360568549529624788),(pn 643624 989645238264662673),(pn 361383 261838058507600628),(pn 128435 741820500428314624),0xc02b4811,(pn 609528 846975841318109700),(pn 567180 816202867207569412),(pn 170493 459552642539716682),(pn 211437 20975865710194688),0x102002080c4836c824,(pn 234106 900668248307892353),(pn 757568 147886557150325731),(pn 306177 362386179298689024),0xe8c8640fda0113a00,(pn 783912 850938332868300911),(pn 850330 914654504650211504),0x1887d182f5500a40,0x70bdd001bb40,(pn 299907 965137468138717184),(pn 9480 338462515449298944),0x2204081260671,(pn 982897 864483262320082992),(pn 945589 335849387574855680),0x238570000000002407,(pn 264510 601461494702031013),(pn 198746 599713980240887813),(pn 795561 25314018755216128),0x10100000014862902,(pn 322745 558371920284184603),(pn 680020 773533228910903755),(pn 153247 345163841835207715),(pn 233715 799890520877039680),(pn 287364 437246937560778243),(pn 122784 14541622281039921),(pn 378097 148883404505294009)]))))
def g237D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (proofWord80 [0x56122003,(pn 87661 101478490036409489),(pn 5361 455488172012147232),(pn 199861 555808668627403846),(pn 165378 24283501852134418),(pn 318781 519298452927949844),(pn 607493 544137465293546130),(pn 161230 471070529612227236),(pn 331345 616757911735388296),(pn 755615 677770140475786530),(pn 156440 208072290380939909),(pn 152447 397679485598327364),(pn 321324 452295681159200937),(pn 82653 313161376572182800),(pn 193949 392587619788981029),(pn 171264 228712389269869152),(pn 5018 967010327183117440),(pn 473418 763320970984359444),(pn 458401 735755364442391557),(pn 171190 443001473537433988),(pn 340126 273692126377820224),(pn 458090 670764942825097236),(pn 760633 190732689014081797),(pn 161971 683788159107224640),(pn 87660 445571425547473049),(pn 160609 37439641823351072),(pn 189190 98133169431693824),(pn 171555 373332492514251328),(pn 342519 720511980794151056),(pn 387281 466055315020779812),(pn 96817 772305323446657025),(pn 75854 178068637662843137),0x820050404009901098,(pn 10054 54870445432396262),(pn 950194 142423038260106202),(pn 620169 633455659601425447),(pn 175734 751022161343980179),(pn 437125 883346040106926636),(pn 1138727 312676475449518105),(pn 302932 21248066954763812),(pn 1124648 823202446108159835),(pn 531764 928028501675973196),(pn 667686 464152439092531757),(pn 1121145 480455713484773030),(pn 175127 57649072018874976),(pn 390233 13360366500235382),(pn 314665 591753986518490680),(pn 1121697 19671554530110611),(pn 394794 679632830541691851),(pn 728909 454492795868091687),(pn 987971 394156797879191684),(pn 1076794 16855127974408611),(pn 59331 602235717614650584),(pn 172976 814780295998999752),(pn 434503 838316083031053856),(pn 675361 246550308210867593),(pn 382504 233079980092882712),(pn 703927 270086329089986557),(pn 629568 899311762741219583),(pn 114905 919862530750305551),(pn 1196273 730892797482716704),(pn 1205769 269150823177213090),(pn 75507 576813212992010645),(pn 155826 83415022643511124),(pn 991991 642377099555246077),(pn 326451 999563368943132927),(pn 95961 113557887393485327),(pn 1195960 136242376189234208),(pn 1205766 963307788193715266),(pn 75508 437000745024224590),(pn 80267 899652059748695892),(pn 760595 955196347306545141),(pn 28647 764643677319008511),(pn 1004998 213789785347625231),(pn 1159508 217172504457333008),(pn 1205763 432472507402129553),(pn 75355 602843496105375945),(pn 80267 300673309157424980),(pn 80575 162241344930385916),(pn 609498 819166801951985919),(pn 400240 158323593658532107),(pn 1159549 704195812026062416),(pn 903607 204575786907457685),(pn 66063 73495871180766597),(pn 381319 25265246496407385),(pn 463012 524747928130161653),(pn 652290 658324449350262975),(pn 1026267 21555628796072459),(pn 1197214 514628282204635424),(pn 903618 517618075826608194),(pn 56476 296962719781483918),(pn 79087 578242888580005460),(pn 156131 278852076530109437),(pn 703941 541993602601521343),(pn 419424 484001342622830863),(pn 1101511 653381999405105424),(pn 1200958 55631925855276049),(pn 75198 229056981251650964),(pn 79087 587250087868283800),(pn 628290 737200366549797845),(pn 624839 615560423941873847),(pn 721379 199466664665563659),(pn 1008301 386338461426225680)]) else (proofWord80 [0x420090,(pn 387921 637124998810584642),(pn 399414 821126636914680484),(pn 336072 441504948173015212),(pn 95143 699350196742328576),(pn 152672 363186254849016041),(pn 80677 573886463883625472),(pn 610698 676118008855831560),(pn 11033 623295790074888456),0xa6c347050a52431909,(pn 66301 356816613796549796),(pn 24498 870461918606270986),(pn 85764 176321188695459986),(pn 142303 392558248810779785),(pn 458366 764478819813983529),(pn 161192 570185683826841736),(pn 66302 509737565561094722),(pn 175024 477986529240222988),(pn 188928 279281016852578605),(pn 80948 91691606759748164),(pn 389948 41295121116370220),(pn 323561 82864347790984491),(pn 23759 740909358283765833),(pn 340238 677680245616812096),(pn 97487 9553017838290956),(pn 85486 258883627799819369),(pn 456042 578360962950783020),(pn 304169 700917437836904712),(pn 435198 229879729416192265),(pn 340201 348420730368630852),(pn 399704 524052904867828368),(pn 118688 991610513380877385),(pn 340275 571168425237695040),(pn 693768 862594972604695623),(pn 61693 416466502851830020),(pn 325923 855084008904205384),(pn 614078 928482436714365969),(pn 118837 443022905480468642),(pn 38445 479337589598196900),(pn 399713 890982989543327754)]))
def g237H8 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (proofWord80 [0xb1d92c89,(pn 831396 525423989025144834),(pn 916249 778150642353700928),(pn 986680 223910968546870001),0x281e360a8e00ce00,0xd2614027fd16320b5,(pn 83926 275092044179840680),(pn 149437 464368352928176175),(pn 930375 156545388632932779),(pn 162106 143786279002153737),(pn 796951 491295749624299520),0xe2005d44179d493c82,(pn 219593 322335337666069208),(pn 324190 310480861798633654),(pn 574674 879181732603879477),(pn 1116148 571202126975343500),(pn 224552 803121069656637440),(pn 6344 888039208946249730),(pn 38074 79768137521941767),(pn 919702 53070852990965298),(pn 96500 863363276278731456),(pn 638709 936493689938608761),(pn 756674 822955541620685013),(pn 689320 633639637303713924),(pn 945392 33117869281915404),(pn 103302 197258874240515101),(pn 1181315 961741091840726396),(pn 188530 490895642257646339),(pn 1119279 665102231277273718),(pn 304927 10494290743133897),(pn 829665 601752282571260047),(pn 906963 860969199334167552),0xc60b00001414c6043,(pn 604462 909808696975443072),0xb6a1cc0711049b925,(pn 718537 647572970263023472),0x50c6801cfc05,(pn 887804 904419461325389824),(pn 140415 632324699001345281),(pn 269174 903400299873124936),(pn 1134054 565029793636441824),(pn 457554 134379001169342651),(pn 57048 861894257559997184),0x401e066bcf24b2083,(pn 528905 301233934442430476),0x8000000003527f408,(pn 949388 849466522112894516),0x82764525e106b686,(pn 1091467 963649486308278863),(pn 229350 757876218409631604),(pn 478142 539648884905209881),(pn 626424 642193269993766956),(pn 63751 947613371224825857),(pn 808903 586971217495331614),(pn 34292 907150843264236800),(pn 765026 946242140964913152),(pn 46624 178490965386854850),(pn 377789 327642199763847792),(pn 304296 943210887712342209),(pn 523371 49880885300687120),(pn 1058229 180924128106910184),(pn 199856 745066982887527433),(pn 377789 373042546980973728),(pn 181686 894226618677892870),(pn 1088553 248690534653430175),(pn 12082 780770911677082632),(pn 179449 941022531742273636),0x12b549eb1300072217,(pn 215017 415450349151717844),(pn 5246 622360492201934894),(pn 132467 582684382736968965),(pn 411381 782302485152485120),(pn 9741 466717512069647107),(pn 756305 770741872004833921),(pn 88581 338791739119465220),0x101382a8625000000,(pn 14185 570698885574230019),0x1e0340081507003907,(pn 14670 936565103360687111),(pn 89727 851179253270970624),(pn 642598 454724752245416198),(pn 37779 96528077714965003),(pn 5406 628520763314601992),(pn 61411 379223124767473667),(pn 67644 715809946802854150),(pn 1001364 857630178668524346),(pn 19442 869386238451000858),(pn 406143 284438003854915154),(pn 90002 817326420408140820),(pn 623389 559154967054386464),(pn 113375 427752830052621058),(pn 4925 281240573253648657),(pn 9565 286727991502898433),(pn 392197 170291258479879174),(pn 203100 316057950803723020),0x4d1b043a04001e0002,(pn 51964 910683782870728778),(pn 14168 326126457364022272),(pn 5165 888307920616883968),(pn 250414 550820402668964106),(pn 75559 16932199035443467),(pn 14333 266797222721320452),(pn 51946 754990332635512832)]) else (proofWord80 [0xa2283102,(pn 1033933 601508308435861504),(pn 833206 884164439463793553),(pn 167146 915863953576427520),(pn 113947 522678575427784712),(pn 94337 494391958717241937),(pn 1133367 955888786210035424),0x9cc20fa264bc69b309,(pn 455727 773991388409824753),(pn 916069 970096443481659984),(pn 612863 401019106423587281),(pn 937891 574748843541021696),(pn 76223 822832108182790218),(pn 1102240 808044696818417664),0x64588411d000000e1,(pn 453347 291969098648387597),(pn 43534 316013954541814278),(pn 560090 68712141764975483),(pn 1047994 157386493467070406),(pn 1125118 203548320731284070),(pn 564047 326593566013128727),(pn 551336 289464153368318268),(pn 170174 672848068295177262),(pn 509130 136787889354017095),(pn 378385 885792447068657647),(pn 15495 265047670862361126),(pn 33384 550251450524175117),(pn 13644 855764852589150657),(pn 439180 88858739604455424),(pn 998349 318640382940711330),(pn 38225 68911859460927491),0x704b03700000803dac,0xe00000802ea224ec0b,(pn 147644 497659306640157967),(pn 21882 502864219852099591),(pn 730814 675973722578958548),0x63aeea0f4e009982,(pn 210449 445577796007249987),(pn 153274 99147934970093520),(pn 909591 404012888278679661),(pn 491740 479069791870517264),(pn 152591 467973546061990990),(pn 1185527 839909781681510320),0x2c17a51850c974d09,(pn 49634 58927440860679124),(pn 309903 43272989225767113),(pn 428855 466273756145392722),(pn 908929 322427818482678784),0x24bb033383210041,(pn 983135 303408833928433980),(pn 708945 268240807636826137),(pn 401476 919715585723731648),(pn 309076 368252053409719818),(pn 995423 474779283535656508),(pn 347069 199265318448771456),(pn 195094 11725316518707298),(pn 918625 673235196017806752),(pn 756911 922872653329789014),0x1bd510b3030eb63f54,(pn 68511 797613380367289822),(pn 675429 181035859931063495),(pn 16897 217748282932929033),(pn 256195 862180690032003913),(pn 919773 106259251934884353),(pn 1143116 304683533485850690),(pn 682185 685452128583241665),(pn 554584 416700975992848511),(pn 566922 869319604117962984),(pn 409850 326823505086383114),(pn 186365 889395758737466948),(pn 27435 916937153840836353),(pn 1053142 737645933352714984),0x80ba74000676f654,(pn 1192703 853855809651196188),(pn 384230 444806125643696384),0x209a581979c0a5b0bf,(pn 949371 773965382660915228),(pn 232281 402291687377615907),(pn 1105224 512181892047437834),(pn 12604 133432961472049152),(pn 18049 922903504905702104),0xd2609009a100b400,0xb179940e60775fc65f,(pn 529419 601274625732028160),0x422d366c5424c5764,(pn 586104 149919091375976101),(pn 147543 171855893508747277),(pn 713201 279557467575534966),(pn 156905 542433680996173057),(pn 1001141 758615376475654186),(pn 347739 572566092560368384),(pn 821691 782698142095376384),(pn 1133746 126452385022879696),(pn 285703 173064200174895104),0x30a75825b801544,(pn 190665 547100050491392000),(pn 19494 749722300563890330),(pn 23685 619413123597029634),(pn 1087549 562839203103508040),(pn 317006 234718824992100296),(pn 284311 794146224867525147),(pn 237784 877135308723004048),(pn 557173 536972850889551953)])) else (if j<3 then (proofWord80 [0xb4ddd4a0,(pn 686312 870834084665806935),(pn 1058336 979553486204336349),(pn 228336 159513703850317975),(pn 137172 873998063749824516),(pn 53510 114714480950643973),(pn 132240 470486919995064721),(pn 608539 640314159194856732),(pn 381041 370183943985217985),(pn 304809 701084131580805424),(pn 753292 146535430303567979),(pn 188907 344943134141364617),(pn 336028 770803100209108055),(pn 181092 11659829660189078),(pn 386182 591774756190906628),(pn 582657 53550699737194679),(pn 921016 325121171448823561),(pn 916740 994759761585701131),(pn 1022512 559954631455808180),(pn 260910 751851264671831468),(pn 906694 869991032451504448),(pn 22763 993968062056528142),(pn 528905 46082363455702553),(pn 15721 413647077487001610),(pn 335440 504498223333507172),(pn 66350 168037697830092800),0x50b464069e026cc283,(pn 917764 455385189459317200),(pn 722819 285810874449056433),(pn 604720 444345298486188260),(pn 106401 475303130576175139),(pn 831136 720597527348910896),0x301490000001da171,(pn 457064 183376209507385722),(pn 388752 523888125677702482),(pn 1171190 381830153600926068),(pn 228934 515320594781752737),(pn 57113 748922544383451783),(pn 57018 21400968592409084),(pn 55782 954872030342520837),(pn 118386 357981578914434062),(pn 5165 89256283759448064),0x208a039311ade20d6,(pn 945229 613098603468086232),(pn 1185611 79816246361899069),(pn 682526 148113848233787904),0x349c30000,(pn 59805 497208470982668228),(pn 640180 657836715672469504),(pn 66196 573606767450922848),0xd47860de9826,(pn 66131 502280577437468492),(pn 614304 504002352446100880),(pn 461022 939707086253195337),(pn 99678 489197892809567120),(pn 762294 780612056736112746),(pn 189754 976116564636509568),(pn 15167 980011694954358930),(pn 869520 325988132189115666),(pn 19507 545662178674007817),(pn 1170156 568900298183082532),(pn 347683 154181951020073281),(pn 74083 252394322347774195),(pn 461460 870271045849841872),(pn 770336 618961370392576189),(pn 1081543 343645664895611180),(pn 116528 651484130073228366),(pn 831136 683978915544094787),0x77821250218c81ae0b,(pn 768893 462144450969993217),(pn 83996 125241845820214214),(pn 1191354 170083926243903838),(pn 688312 309728343579522912),(pn 362589 724230462971934572),(pn 948697 388103088326746784),(pn 97952 659449617559195664),(pn 156341 961414963829674378),(pn 43954 147624426554888192),(pn 6053 351403276833785177),0x900ab30d73c003c81,(pn 1070810 140072649980116992),(pn 755717 354333341934069809),(pn 56099 221182215362757155),(pn 1190844 767980492219781076),(pn 711456 819920382652533005),(pn 75558 122011918463926283),(pn 28865 702466956180851011),(pn 357061 177174246465538843),(pn 1001741 763623233835274240),0xa04c3c222c076c0000,(pn 985129 920523656365080768),(pn 253319 957760143393947648),(pn 123486 834421738804084736),(pn 615257 108194118000970765),(pn 359125 665810142672758570),(pn 203620 418193746928746791),(pn 623456 823273733306057273),(pn 1089708 8585455229988617),(pn 687496 242265972387139717),0x10d8300121411721,(pn 165138 359599850025498006),(pn 925644 72867774746335769),(pn 341191 727559667283423267)]) else (proofWord80 [0x3497aa89bc000,(pn 29586 542395244431802368),(pn 30854 496161003130056496),(pn 839428 961156333853962612),(pn 612985 305613405589545282),(pn 899618 609595653536497916),(pn 535095 374008863227581984),(pn 237225 516097472787644578),0x2813200002c,(pn 186054 367665236627349526),0x3caa32438bd26e9,(pn 203764 777790759821856768),0x8122707d4,(pn 177462 622589633254033296),(pn 925586 739995727727318538),(pn 682645 689896586583350274),(pn 567793 558219110043095206),(pn 43179 666883653282202464),(pn 27448 755746282814491693),(pn 892997 675434606078197766),(pn 120227 813584198653395460),(pn 793357 623857225254117695),(pn 650297 355843002297444672),(pn 7092 427490031114405244),(pn 304661 239732262517498448),(pn 514811 838602618676253765),(pn 609445 45017861541726588),(pn 439182 414875319267524608),(pn 37985 363459752734245729),(pn 47993 943585660324574720),(pn 800453 766176540572341284),0x70000038294d2b2c00,0xb0386c9d4a012e41bb,0x380e3a407091dac0,(pn 66558 963578528506675387),(pn 360691 62240687754906704),(pn 76573 645297619323342277),(pn 525740 495382662803881997),(pn 42281 417008120230586371),(pn 30742 476769238781531693),(pn 347766 126531147435351040),0x321ee126f2279f898c,(pn 78174 421239192950407312),(pn 89724 965432906345205946),(pn 1190303 47982223664911000),(pn 17708 874808075432764521),(pn 1045033 199897347797836075),(pn 327678 881905578750824993),(pn 229077 738773487418345968),(pn 307031 286334863372419394),(pn 444209 125384372984807679),(pn 697325 842207868684093120),(pn 262091 343239136900792404),(pn 757193 880290473921245604),(pn 633387 404657066670571520),0x64c000000000807c5,(pn 188862 521547137962586921),(pn 330567 144496184256979266),(pn 608895 911006926659431625),(pn 552516 886672782297252595),(pn 1058341 599276677022770562),(pn 783716 159457042817081414),(pn 623649 331824109672493816),(pn 1016674 437220480419389583),(pn 700815 10254741377127034),(pn 12092 330247948012290054),(pn 99178 221756431489633145),(pn 609941 641057616102368642),(pn 962776 950392004003184954),(pn 851657 940109058349299906),0x3815b000000000d0be,(pn 302231 690225847304750636),(pn 426156 723253707703962752),(pn 840606 636552944028221440),0xe0859c2ba000,(pn 10652 382882895490711679),(pn 911785 666119488015296960),(pn 605952 378699823880061536),(pn 1058717 158627719866640793),(pn 673981 137667096961765390),(pn 1153064 611657454643608696),(pn 175471 235131788857661464),(pn 972946 244888343512363582),(pn 357202 752455561660769800),(pn 74406 127811467241818519),(pn 28533 701936338505568384),(pn 225817 480820971496177842),(pn 1138338 498254951659728849),(pn 423168 421365972628144128),(pn 77594 646160387248053941),(pn 9098 914639404624356898),(pn 91104 240308376806999386),(pn 350935 473759019579873035),(pn 262428 136993889274365852),0x904bb80cae1b3d40,(pn 155846 980697542544253518),(pn 762232 151565770023786980),(pn 264621 157234709505056776),(pn 982737 399375096541627684),(pn 69014 552605864134586753),(pn 840699 228280688337002594),(pn 21204 734587741445456201)])))
def g237D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [(pn 76452 602960766758322453),(pn 170007 805684414880826432),(pn 916233 926878476782022785),(pn 344733 407468527783547168),(pn 382567 385794263009005616),(pn 610531 891163108185736199),(pn 341504 791760594807002843),(pn 119544 861190595102639102),(pn 764992 313024165978293279),(pn 991989 877765685351939088)])
def g237H9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (proofWord80 [0xe1380,0xa46f0000f74e0000f,(pn 310975 757960053186887680),0xc05800000,0xe06900004,(pn 27781 260445822021009409),(pn 313447 75300472701059072),0x801700000,6,(pn 175022 707771356225732608),0xe25a00000,0,0x6111e24800006,(pn 80870 526019142674284544),0,0xf059517ee18181164,(pn 303412 46524434888327264),0xe,(pn 105948 9896282583728128),0x53790000000000000,3,(pn 17655 925489946552434701),(pn 303707 194429554057805824),0x663603c000000000,0x1028102e0000b,(pn 83547 925004813688897536),0,0x5253655d0000b11e1,(pn 555763 507498019157903466),(pn 81460 823874867885506560),0,0,0x945000000,0xf082102a10576,(pn 306658 676577847207788544),0xb,(pn 170890 637387158508273664),0x30551039545c0,0x706d0000000000000,0x2007000000000,0x501f000050320,0,0,0,0,0xb3460000000046780,0xe2470,0x512e0000000000000,0xf26c00000,0x695fb74f00002,(pn 20660 353362554698671344),(pn 156428 389745056998302976),0,0x5065000000000,8,(pn 306953 821386526938890240),0x306f0000000000003,(pn 35122 600716342986276864),0xa068724e00000,0,0x57820000000000000,0x91809013000062620,0x685ab,(pn 14167 103745431657512960),0,0,0x96700,0x8029000000000,0x11370000e74b00000,0,0x61848056f13600000,0,0x705d0,0xd04d4015000000000,0x94665,(pn 113173 137319853547607360),0x5542000000000000e,(pn 6090 42135707655091696),0xf2400,0x7d0000c12c0,0,0,0x465d0,0xc,(pn 38831 789988953781698560),0x813d0000000015780,0x84380000000000007,(pn 16713 119425950298144768),0x70800000b4750,(pn 551336 286875033038487565),(pn 27393 729714417668456448),0xa,(pn 18723 512792848248501504),0,0,0,0xc13400000000707c0,0x703dd0365,(pn 314332 519016010759536648),(pn 13282 847499231531763744),(pn 632944 756562995756270512),(pn 605145 446234204542075394)]) else (if j<2 then (proofWord80 [0x56300000,0xb0516072b6640,0x317269000000000,0x800200000,0,0xc75c60010,0x155e0000121600000,0,0,0x1000000000001,0x800000000000000000,(pn 78214 194872528498851840),0xc,(pn 5352 262444751819636736),0xb06b0000000000000,0x2249327400000000d,(pn 172956 672435101874782208),0x22100,0x9511f00a00000,0xc0430,0x373f000021650,0,0xe04e0,0,0x717d000000000000f,(pn 113927 91399290337099776),0,0x610a000067510,0x1960000000000,0,0xd0210000000000000,0,(pn 30105 86328293988237312),5,(pn 87658 927838267789279232),0,0,0x90810000000000000,0x607f000000000,0,0x945b806e000000000,0xb049000000000,0xa440000000000,0x14640000000000000,0x218600000000644e0,0,0x9062701e0,0xc7380000000000000,0x8677000000000,0x10840,0x326a00000,0,0x7258000000000000e,(pn 19333 597415930977517968),0xf5550000000000000,0x20440000000000000,0x7360000000000,0,0x702c0,0,0x5025f,(pn 481091 85442345106145280),0x607b277600000,0xa261307a3,(pn 335288 24246247277723648),0xa859517b00000,0x117cb06c0000e,(pn 15347 694173549517472368),0x501a000000000,0xd66f0000000000000,0x90050000f0030,0x4040b02fe0640,0xd0260000000000000,0,0x208500000000f,(pn 171185 785004024639067041),(pn 81755 973752639818039310),(pn 34532 305756112927335714),(pn 78936 31820843507384592),0,0x4820000706000003,(pn 21361 674450867920568324),(pn 92971 590131496140144644),(pn 173842 116150660696049056),0x800e0,(pn 37341 269537204679475200),0,0x102b387460715,(pn 413028 478983400974188544),0xd03e0000000000000,0x8467000000008,(pn 635158 291945967398682624),0x611f00780000244f2,(pn 26858 459371321107818170),(pn 410845 884327787389517824),0xa00bd018520f6,0x9897a0000000000000,0,0x602200000,0,0xb01c8211b,(pn 407304 112251063165255695),(pn 314037 374214958890352640)]) else (proofWord80 [0xc00d00000,7,(pn 20955 501267734394568704),0,0x50540000374a00000,0xe1080000000000000,0xb042000000000,7,(pn 638404 920628348784214016),0,0xd0200000000000000,0,0xe128000000000,0xe,(pn 410809 229212291966108125),(pn 21840 947799555587440651),(pn 10629 179667791813279744),0,0,0x37a0000523f00000,0xe217e02360500,0xf])))
def g237D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g237H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (proofWord80 [0x5a35838000000145,(pn 113680 695452658912827779),(pn 501751 450362966582368881),(pn 340010 386787505260724227),(pn 924445 539297355884111872),0x223f41000604b1,(pn 265428 657206914762997762),(pn 47223 664956446370432769),(pn 604491 368965417186175088),(pn 302846 215437933728665604),(pn 268753 150669494135918592),(pn 201256 496256056705286676),(pn 799326 857367046408933473)])
def g237L : Nat → Packing
  | 4 => (1,6,5,0,0,0,0,g237D4)
  | 5 => (174,5,5,0,0,11,0,g237D5)
  | 6 => (1091,4,5,0,0,14,0,g237D6)
  | 7 => (804,3,5,0,0,15,0,g237D7)
  | 8 => (135,2,5,0,0,13,0,g237D8)
  | 9 => (10,1,5,0,0,9,0,g237D9)
  | 10 => (1,0,5,0,0,0,0,g237D10)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g237H5
  | 6 => lookupWord 77 461 6 16 8 4 g237H6
  | 7 => lookupWord 475 2591 8 19 11 4 g237H7
  | 8 => lookupWord 360 1657 8 18 10 4 g237H8
  | 9 => lookupWord 76 1129 3 16 8 4 g237H9
  | 10 => lookupWord 15 79 5 12 4 4 g237H10
  | _ => fun _ => none
def g237 : Forest := ⟨237,10,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P4_0 : block g237 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B4 : block g237 4 0 1=true := g237P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_96 : block g237 5 96 78=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 174=true := (@block_merge g237 5 0 96 78 g237P5_0 g237P5_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_2 : block g237 6 2 47=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_49 : block g237 6 49 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_145 : block g237 6 145 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_241 : block g237 6 241 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_337 : block g237 6 337 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_433 : block g237 6 433 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_529 : block g237 6 529 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_625 : block g237 6 625 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_721 : block g237 6 721 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_817 : block g237 6 817 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_913 : block g237 6 913 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_1009 : block g237 6 1009 82=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 1091=true := (@block_merge g237 6 0 433 658 (@block_merge g237 6 0 145 288 (@block_merge g237 6 0 2 143 g237P6_0 (@block_merge g237 6 2 47 96 g237P6_2 g237P6_49)) (@block_merge g237 6 145 96 192 g237P6_145 (@block_merge g237 6 241 96 96 g237P6_241 g237P6_337))) (@block_merge g237 6 433 288 370 (@block_merge g237 6 433 96 192 g237P6_433 (@block_merge g237 6 529 96 96 g237P6_529 g237P6_625)) (@block_merge g237 6 721 192 178 (@block_merge g237 6 721 96 96 g237P6_721 g237P6_817) (@block_merge g237 6 913 96 82 g237P6_913 g237P6_1009))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_7 : block g237 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_103 : block g237 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_199 : block g237 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_295 : block g237 7 295 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_337 : block g237 7 337 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_433 : block g237 7 433 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_529 : block g237 7 529 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_625 : block g237 7 625 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_721 : block g237 7 721 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 804=true := (@block_merge g237 7 0 337 467 (@block_merge g237 7 0 103 234 (@block_merge g237 7 0 7 96 g237P7_0 g237P7_7) (@block_merge g237 7 103 96 138 g237P7_103 (@block_merge g237 7 199 96 42 g237P7_199 g237P7_295))) (@block_merge g237 7 337 192 275 (@block_merge g237 7 337 96 96 g237P7_337 g237P7_433) (@block_merge g237 7 529 96 179 g237P7_529 (@block_merge g237 7 625 96 83 g237P7_625 g237P7_721))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_12 : block g237 8 12 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_63 : block g237 8 63 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 135=true := (@block_merge g237 8 0 12 123 g237P8_0 (@block_merge g237 8 12 51 72 g237P8_12 g237P8_63))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 10=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P10_0 : block g237 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B10 : block g237 10 0 1=true := g237P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact g237B4
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
  · exact g237B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 11 := lower_forest (g:=g237) (i:=0) (hints:=33555715) (before_sound K231 V231) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_49603.ForestCore

namespace PEqualNP.Outside.L_meta_49603
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds ForestCore

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def coding : Fin 8 → Nat := ![1, 4, 0, 2, 3, 5, 6, 7]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def roots : List Sig := List.ofFn (fun i : Fin 8 => inputs.getD (coding i) zero)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def codedGraph : Sig := 0xfffffffffffffffffffffffffffffffafffffffefffffffcfffffefeffc0eec0fffffffffffffffffffffffffffffffafffffffefffffffcfffffefeffc0eec0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wholeBound : Lower true roots codedGraph 13 := by
  have h := lift_ok (u := true) (ms := fixRows 18 0) (raw := roots) (T := codedGraph)
    (xs := [(inputs.getD 1 zero, 4, 6), (inputs.getD 4 zero, 8, 24)]) (by decide +kernel) (proper_of _ (by decide +kernel))
    (proper_of _ (by decide +kernel)) low237
  have count : (([(inputs.getD 1 zero, 4, 6), (inputs.getD 4 zero, 8, 24)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by
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

def upperGates : List Gate := [⟨.or, [2, 1]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [7, 0]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [15, 1]⟩, ⟨.and, [9, 14]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [20, 19]⟩]

theorem upper_shape : ∀ g ∈ upperGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem upper_sem : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upperGates, 21⟩ (List.ofFn x) = graph x := by
  decide +kernel

end PEqualNP.Outside.L_meta_49603

open PEqualNP.Outside.L_meta_49603 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_49603 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
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
