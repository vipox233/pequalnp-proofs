import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28118.Model
open PEqualNP.CircuitLowerBounds
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
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

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

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
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

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
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

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

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

end PEqualNP.Outside.L_meta_28118.Model

namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d 7 k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 48,swapRows 33,swapRows 84]

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) 7

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
def g0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g0K5 : Nat → Nat
  | 0 => 0xe000001480044952028055a51c0061900207802c9d1034854d004c6cf915028b8b46006863a1029042243800060f1348621a1083001838800f521fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10f441fc41fc31fc21fc40fc30fc20fc10ff40ff30ff20ff10f741ff41ff31ff21fe10ff42ff32f621fe21fe20ff43fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g0K4 : Nat → Nat
  | 0 => 0x541558000e35000049104e0016134f040d002e00002f480000001a192900022300004a59561f53001801201d46004211000051403d242c470c2a3e00142b360727430857002230520600034b0938123a50391c4d001741344c3128550a0b2526370f5a3c33443f0521322d1e1b3b450100230e0040040101945ac3804805021824561c210011f795010af2a0195e54041f8a80837905d0fca42a15949441ba92c437525106eaa2215d115219a22a43b445486eaa2195d49741bba2c4375150c2ea2a105d45720ba8ac65751590eea2b215d45640b6928836d250c2ba6a21574d441ae9a8415d35d027a8a194f514309ea28413d45cc67a8b084f11521ae1aa413f458427e8b98dd14543ba28a857451502ee2b205dc5642bb8ac87e525107aa6a20ed50c41daa00837715907688420ddc5632bc282655f35d02f60ba1f64c030bb8ae413f45082be6a104fd1430da20e817b504cade4a185dc5420bb8a861775150eeea2a15dd4540bba2883b441d06be6a20f5cd441b792883e725106f4a020fc940419fa28655f3510aeca2195d94442f290c437715086e88b10de94032bd280857615d0b6883a1d78d520db22a433e45487ca43216d10642
  | _ => 0
def g0K3 : Nat → Nat
  | 0 => 0x2936010d431534719000b0003c2205000597392444000240442428c02017316011521d85412510751504d441d2495300c2b16010841cc41441d0f45254d441c9495431072525500419949845887256211521c54d8454863756915218d11915c82344645632a54d842107153510740a949841d034525cd441d849650107173611521cc98045486a52610743a94984190aa44648642
  | _ => 0
def g0K2 : Nat → Nat
  | 0 => 0x40200311885816211521c22c09b08a90e210549841d0f02b126c22a43814d52610740
  | _ => 0
def g0N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0
def g0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g0K2 (i*49) 49
  | 3 => packedAt g0K3 (i*38) 38
  | 4 => packedAt g0K4 (i*27) 27
  | 5 => packedAt g0K5 (i*16) 16
  | 6 => packedAt g0K6 (i*5) 5
  | _ => 0
def g0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g0K2 (247+((h/2+packedAt g0K2 (245+(h % 2)*1) 1) % 7)*4) 4
  | 3 => packedAt g0K3 (995+((h/9+packedAt g0K3 (950+(h % 9)*5) 5) % 32)*6) 6
  | 4 => packedAt g0K4 (2643+((h/31+packedAt g0K4 (2457+(h % 31)*6) 6) % 111)*8) 8
  | 5 => packedAt g0K5 (779+((h/15+packedAt g0K5 (704+(h % 15)*5) 5) % 54)*7) 7
  | 6 => packedAt g0K6 (6+((h/1+packedAt g0K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g0Pos : Nat → Bits
  | 0 => 0x0
  | 1 => 0xaece7b755af916ec7996a9694bdcbfc678527b
  | 2 => 0x9b5aaddaba1b2b751a2be2bb15f3f2d08bce3c
  | 3 => 0xd7af5753ef6dcdbaaccd34ddff55556b14afc9
  | 4 => 0xe5cb9e7cf3b1f1dcf171bff1a69a698de1f492
  | 5 => 0xf9f3e79f3c3e7e1f3e7fc71e38e38e31ff0924
  | _ => 0
def g0Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x1fc03f80003f80000000fc0fc038003b
  | 2 => 0xfe03f81fffc000000001f81fc0fff00001ce3c
  | 3 => 0x3ffe0000000000000001fff000000000fc0
  | 4 => 0xfffc00000000001fc001ffe000000001c1f000
  | 5 => 0x1ffffe000000000001fe0000
  | _ => 0
def g0Atlas : Atlas := ⟨6,rawDecor 62 g0Pos g0Neg, 0xfffcfff0ffcccc00fffcfff0ffcccc00fffcfff0ffcccc00fffcfff0ffcccc00fffcfff0ffcccc00fffcfff0ffcccc00fffcfff0ffcccc00fffcfff0ffcccc00, g0N, g0R, (fun _ _ => 0), g0I⟩
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
def g1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g1K5 : Nat → Nat
  | 0 => 0x553920e3ce1f126942a06982a03c380a1000000d4850b8a30000002c18e84004c00032015a92240400188c580048929b03222820c0018510401f521dd43fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41fc31fc21fc40fc30fc20fc10ff40ff30ff20ff10ff41ff31ff21fe10ff42ff32f621fe21fe20ff43fe32fe31fe30de43fe43fe42fe41fe40
  | _ => 0
def g1K4 : Nat → Nat
  | 0 => 0x31188914011000007c4ca15c00000000d0cc013c58d56c6cdc9098bc10008000016428c9002cd8b15401210c54784008f065307084f48c001c00a8f8a49c3d3850e1454c18c4047524e838684908e52cfc21501534b4b91ced48446000002400ac94354128000c5d59616904c090d0c2a00d0308001850a0002a0404c922a0010500140c2421c406bca808579500caf2a020f948542f290a41d52150eea4b10dd54442baa8865e5210caea2a205d45430ba8a8417515c82ea2b195d45643ba8ac856d25106da4a205b49430b6928216d258c73a86a16750d40aea2c875d3510aba6a20d74d440ae9a8415d35042ba6ba0574d741ae9ae855d358867a8a194f514309ea28413d450427a8b98d70d520af9ac436f258c6be6ba14fd1731ba28a81771590aee2b21e750c41bb8ac655f35d06be6ba05dc57209fa28215f35042de4a084fd1420af9a8413f450c33a87a057cd440b7928616f25103ca43905dc5420bb8a8617715102eea2a057cd441b7928837a501067e8a196750f42af9a885e521ccaeca2195d94442f290c43d543887aa6b10ddc5421eb9ac437a500caf4a021578d520ea90c87d51590f3a8721d7cd443eb8ac87d62190fca43216750e41
  | _ => 0
def g1K3 : Nat → Nat
  | 0 => 0x10b0340e7952a31c830898f6b001d8541210cb195050c41e14854350b25215143299498515026526c5643d1484354834525cd621c3495431061d460d5208751b35887154314540c55171590e556588643a551b35886c526c5643
  | _ => 0
def g1K2 : Nat → Nat
  | 0 => 0x40098c0a42a306a906052551b35887029328628a818151526c5643
  | _ => 0
def g1N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 16
  | 4 => 92
  | 5 => 44
  | 6 => 1
  | _ => 0
def g1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g1K2 (i*49) 49
  | 3 => packedAt g1K3 (i*38) 38
  | 4 => packedAt g1K4 (i*27) 27
  | 5 => packedAt g1K5 (i*16) 16
  | 6 => packedAt g1K6 (i*5) 5
  | _ => 0
def g1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g1K2 (198+((h/2+packedAt g1K2 (196+(h % 2)*1) 1) % 10)*3) 3
  | 3 => packedAt g1K3 (632+((h/6+packedAt g1K3 (608+(h % 6)*4) 4) % 19)*5) 5
  | 4 => packedAt g1K4 (2701+((h/31+packedAt g1K4 (2484+(h % 31)*7) 7) % 109)*8) 8
  | 5 => packedAt g1K5 (779+((h/15+packedAt g1K5 (704+(h % 15)*5) 5) % 55)*7) 7
  | 6 => packedAt g1K6 (6+((h/1+packedAt g1K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g1Pos : Nat → Bits
  | 0 => 0xb77aecf9ededbe45bb296acb4b2cbfcb92525f
  | 1 => 0x0
  | 2 => 0xdb19b55ab6bc86cadd42be55d957f2d0a5ce31
  | 3 => 0x6dad7a6d5c96db736e94d326eefd556548afc2
  | 4 => 0x7ece5c4e78d8ec7c771f1bbf8c9a698671f484
  | 5 => 0x8f0f9f8f9f1f0f9f87e7fc38f0e38e387f0928
  | _ => 0
def g1Neg : Nat → Bits
  | 0 => 0xfe00000000000000fc000000f
  | 1 => 0x0
  | 2 => 0xfe00fe01ff00000001fc0ff03f00001ce30
  | 3 => 0xfffe0000000000000fffc0000000fc0
  | 4 => 0xf00ffff00000000007f81fff0000000071f000
  | 5 => 0xfff000000000000007ffe000000000007e0000
  | _ => 0
def g1Atlas : Atlas := ⟨6,rawDecor 61 g1Pos g1Neg, 0xfffafffaffaaaaa0fffafffaffaaaaa0fffafffaffaaaaa0fffafffaffaaaaa0fffafffaffaaaaa0fffafffaffaaaaa0fffafffaffaaaaa0fffafffaffaaaaa0, g1N, g1R, (fun _ _ => 0), g1I⟩
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
def g2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g2K5 : Nat → Nat
  | 0 => 0x9007460300142241421025563479646009a252400190084e1f007801b0e0489a1c0138b0c60baa4c480005054114140029a100040000c00f510bd43fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41fc31fc21fc40fc30fc20fc10ff40ff30ff20f710ff10ff41ff31ff21fe10ff42ff32fe21fe20ff43bf43fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g2K4 : Nat → Nat
  | 0 => 0x15251788a2192a99939c0780a8ad1d8c050a858e89a40c9626928a0014a11d10ac8d821321a62b2498299bad82800023270f1f00000d0f801a28112000000018841e802b9a95892288000b0ba0a38016801ca5ac1f80291711802783818600070000002a121b00030e14048681101e0012203000094524001831d5c146a080000002357040010f888261f110482f2a0215e54032bca80637950086f20b20dd54442baa8865b51050eea2b085d45440ba8a8617515082ea2b105d45743ba8ac617515902da4a18db49440b6928619d434caba6a21574d421cea1a615d35102ba6a10574d7419ea2c873d450ca7a8a18cf514219ea28613d450827a8b984f517109ea2e633d45cca788a904fd17329fa2e637715902e8a2995dc5630af9ae837715d0f3a8618ddc56209fa2e213f45cc2f60b20fc440409fa28415f350827e8a187c44340af9a8819d43cc2de4a185bc9440bb8a84177150c2ee2a207c44310daa1e21b545c42ee2a086dd17109fa28435f350867e8a18ddd4532b7928637a50086f4a018cfd1432af9a8859d43ccaeca2195d94442bd280657a5010be221106d44343da8ae879d35d0e7e8a21edc5743db886879d438c7e221184f91520
  | _ => 0
def g2K3 : Nat → Nat
  | 0 => 0x4703800005e4594c05306043520595a0d849510103911050d30d44d5101033110115209c580514ca7160c5743c6541430c73105d1710c3495430c61d3611520874db45c43154314532c54d715d0e3565c4343a54db45c42b160c5743
  | _ => 0
def g2K2 : Nat → Nat
  | 0 => 0x58080c22209b08a90611054db45c4308b028628a65844d560c5743
  | _ => 0
def g2N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 16
  | 4 => 92
  | 5 => 44
  | 6 => 1
  | _ => 0
def g2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g2K2 (i*49) 49
  | 3 => packedAt g2K3 (i*38) 38
  | 4 => packedAt g2K4 (i*27) 27
  | 5 => packedAt g2K5 (i*16) 16
  | 6 => packedAt g2K6 (i*5) 5
  | _ => 0
def g2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g2K2 (198+((h/2+packedAt g2K2 (196+(h % 2)*1) 1) % 6)*3) 3
  | 3 => packedAt g2K3 (632+((h/6+packedAt g2K3 (608+(h % 6)*4) 4) % 22)*5) 5
  | 4 => packedAt g2K4 (2670+((h/31+packedAt g2K4 (2484+(h % 31)*6) 6) % 111)*8) 8
  | 5 => packedAt g2K5 (779+((h/15+packedAt g2K5 (704+(h % 15)*5) 5) % 53)*7) 7
  | 6 => packedAt g2K6 (6+((h/1+packedAt g2K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g2Pos : Nat → Bits
  | 0 => 0xbb6e56d7b55b7d05bb4b42cb2fd4bfd29291e7
  | 1 => 0xd8f6aa6adab90d6add173555576bf2c52e22f8
  | 2 => 0x0
  | 3 => 0x6dbb3d7e93edb7b36ea599a6fd4d5569c54f29
  | 4 => 0x7eddce4cfcf1d9dc773e2e3f9a72698e787452
  | 5 => 0x8f1e0f8f1f3e1e1f87c7cff8e3838e307f8884
  | _ => 0
def g2Neg : Nat → Bits
  | 0 => 0x1fc01fe00000000003fc0fc00000e7
  | 1 => 0xfe000001fffe0000007f00003fff0000e00f8
  | 2 => 0x0
  | 3 => 0xfe000000000000000fc000000000f00
  | 4 => 0xf0000ff00000000007f8003f00000000707000
  | 5 => 0xfffff0000000000007ffffc0000000007f8000
  | _ => 0
def g2Atlas : Atlas := ⟨6,rawDecor 59 g2Pos g2Neg, 0xffeeffaaffeeee00ffeeffaaffeeee00ffeeffaaffeeee00ffeeffaaffeeee00ffeeffaaffeeee00ffeeffaaffeeee00ffeeffaaffeeee00ffeeffaaffeeee00, g2N, g2R, (fun _ _ => 0), g2I⟩
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
def g3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g3K5 : Nat → Nat
  | 0 => 0x24549401f4c4c7961c5cf0906000190288e9c000052016a0c0836009004ea508d2a00604341439146508000419580096901ac035480015a2f510fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41f431fc31fc21fc40fc30fc20fc10ff40ff30ff20f710ff10ff41f731ff31ff21fe10ff42ff32fe21fe20ff43fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g3K4 : Nat → Nat
  | 0 => 0x422b402a340023582f00332d28101e2603000a444100140c1355190022001c3e32470017494f24000b3c4b0d0e0005003f4a27464d0037023d00080004150f092c54533a00070051004e252e43111d0020161a563900520136004c5a501238350630291b3b595731482118451f0651f39e08408010020200838208258a000002782284189f1104c2e2a018de54042bca8063f1500c6eaa2215d45610ba8a88175150c2eaa018d50d510ba1aa21d435442ea2a105d45620ba8ae8775158caea2b185d45640b6928636d25102da4a185b49643ae9a8855d35102ba6a10574d741ae9ae433d450c67a8a184f514209ea2e653c454827e8b995b14940b792c87ad4210ab86a8857cd721ba28a877715902e8a2995d14530bb8ac6177158cabe6ba0ddc5743f292863d5430c7aa6418ed51431bb8ac637715882ea0b98ddcd710ea188613f45082be6a104fd1430af9a8816f250c2de4a205dc5420bb8a8617715103e221885dc5410ba1ae213f450c76e8a18ddd4543bba8a6577514c2ee6a18f50c731b792863e7250c6f4a018fc94031bb02e636f52502be6a21750c732bb288857a5010bac6a88578d510f888461d4318c3a86321cf91520
  | _ => 0
def g3K3 : Nat → Nat
  | 0 => 0xf4555c24000c14d814000000b48958628d20c507384006830032107615049431d4541430c751504c831cc541450c6715694031d458035443295050842c9495450c745260d510c55183544257568d510950d915882543645640d1494310c345250c643c5514310c315450c732cc543450c76150c9431c5d183544347260d510b458031ccad1600c630b40d9108c2d1600c643
  | _ => 0
def g3K2 : Nat → Nat
  | 0 => 0x324001590581260d510c824ab006321e11605183544308a2ac018e6581499460d510
  | _ => 0
def g3N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0
def g3R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g3K2 (i*49) 49
  | 3 => packedAt g3K3 (i*38) 38
  | 4 => packedAt g3K4 (i*27) 27
  | 5 => packedAt g3K5 (i*16) 16
  | 6 => packedAt g3K6 (i*5) 5
  | _ => 0
def g3I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g3K2 (247+((h/2+packedAt g3K2 (245+(h % 2)*1) 1) % 7)*4) 4
  | 3 => packedAt g3K3 (995+((h/9+packedAt g3K3 (950+(h % 9)*5) 5) % 31)*6) 6
  | 4 => packedAt g3K4 (2643+((h/31+packedAt g3K4 (2457+(h % 31)*6) 6) % 109)*8) 8
  | 5 => packedAt g3K5 (779+((h/15+packedAt g3K5 (704+(h % 15)*5) 5) % 53)*7) 7
  | 6 => packedAt g3K6 (6+((h/1+packedAt g3K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g3Pos : Nat → Bits
  | 0 => 0xaede7bdaadfd16ed5a2d596a97ecbfd64a52f7
  | 1 => 0xd74aad6d5c8dab74b95662bb2bb3f2c8b8ae78
  | 2 => 0x9baf5749f6b74dba2c9bccdefea5556315cf91
  | 3 => 0x0
  | 4 => 0xe5cb9e7e78d9f1dcf1e377f34d3a698de1f42a
  | 5 => 0xf9f3e78f9f1e7e1f3eff871c71c38e31ff0944
  | _ => 0
def g3Neg : Nat → Bits
  | 0 => 0xfe01f80000000000001fc0fc0000077
  | 1 => 0x3f80fffe000003f00001f81fff000380e78
  | 2 => 0xfe03fff0000000000003f81ffe00000001cf80
  | 3 => 0x0
  | 4 => 0xfffc00000000001fc003ffe000000001c1f000
  | 5 => 0x1ffffc000000000001fe0000
  | _ => 0
def g3Atlas : Atlas := ⟨6,rawDecor 55 g3Pos g3Neg, 0xfefefafaeeeea0a0fefefafaeeeea0a0fefefafaeeeea0a0fefefafaeeeea0a0fefefafaeeeea0a0fefefafaeeeea0a0fefefafaeeeea0a0fefefafaeeeea0a0, g3N, g3R, (fun _ _ => 0), g3I⟩
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
def g4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g4K5 : Nat → Nat
  | 0 => 0x5a780284c0c0004a18e9f5230d953240e121a680133058000002400004bd6225c291a4082002b0e8108e4e5058f2ea80910a82c410012910426a0801f541f510ed32fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41f431fc31fc21fc40fc30fc20fc10ff40ff30ff20f710ff10ff41f731ff31ff21fe10ff42ff32fe21fe20ff43ee32fe32fe31fe30fe43fe42f641fe41fe40
  | _ => 0
def g4K4 : Nat → Nat
  | 0 => 0x501a820e4000000000021d08400620d03c004a43058ce611d87400120c970ac15231dcd68305a043e0c1f9d4566e2989c287b16a10fe33261f80c131a1b06c7d019bc407435000ec4b3c0400039148f0548202060621736914b23e3188cf2402d1e84c4d02960005214070aa871915c004424894825b0d80090691c0f43c65002149c6439800e06000834a85e089088e5f3e0000000111440e00120006009001745e71000008600070dc000000000142c00000cc8000000d04f1719a41008000156044f00386b75200212701801284401800e0828001012f88826171500c6f2a021de54042bca8063f1500c7ca82996d505439aa28637551502ea8b20dd51431baa2e217545cc6eaa221dd14d41bb9ac83755110bca20995d45610ba8a88175150c2eaa018dd0d510ba8a8417515d02ea2ba15d45620ba8ae8775158caea2b185d45640e699287cd324c2da6b195b54843b6928636d25102da4a185b49730b692e636d2590eba6a21574d440ae9a8415d35c867a8a18cf514309ea28416c52502de4b21d7cd721ba28a877715903c8a2995d14532ba28a6177158c2ee2b195dc5743e299063e5320c7ca4a18f54c831daa286377158c79a6418ddc5620b792e637715d0aea0b98ddcd710ba82c83b940102de4b985dc57409fa28415f350827e8a185dd4141af9a881cd32cc2de4a185bc9440bb8a84177150c2ee2a207c44310f2996217715042e86b884fd1431dba2863775150fcea2995dd4532bba8a61e532cc7ca4b98ddcd431ea18e63e725cc6de4a18f9c9431bd28063f2500c6ec0b98dbd4940af9a885d431ccaeca2215e94042daa0e876e5210fca83197944232f28ac65cd328cade4a1979c5632f218c65e7108cbce63195d94443e6994637a5010fe22118734ca43bb22a21e5329076a8320ddc5441f3194837435906ec0b20dd85643
  | _ => 0
def g4K3 : Nat → Nat
  | 0 => 0xa9c0004a0cb22041000002640282e00a8b624c029000160d482402f107838a46b478038308065460e8024acf946000d804c68711000170040843481618bc4008003000409c58053507c1104c930d0541320c761504c831d8541250c751504c831cc541450c6715694031ca49540103193550040d2541320c7c1504c8319c4183590785414c943c1515320c745454c831c9515320c7453214d41c9495450c715454c8318d5183544235460d6418d51835c42546354540d1541320c745320d51099594318cb0d454c831934d852503453214543d14c8514c34535c5632e14c9450c747154ca31d149431cc745320d710cc543450c78532d1431d1d95320c66565cc632b1d95320c76150c9431c9517250c7314594031f04ca500c6d1600c732a551831ccae1600c632a9518318cb45320d641
  | _ => 0
def g4K2 : Nat → Nat
  | 0 => 0x403300e01140441f1905813214d41e02a09928a18e4135580318cb20832641ac8381519320d510c0a8c9906b20e05464c835c4380a8265a2863c05153294031
  | _ => 0
def g4N (k : Nat) : Nat :=
  match k with
  | 2 => 9
  | 3 => 50
  | 4 => 136
  | 5 => 48
  | 6 => 1
  | _ => 0
def g4R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g4K2 (i*49) 49
  | 3 => packedAt g4K3 (i*38) 38
  | 4 => packedAt g4K4 (i*27) 27
  | 5 => packedAt g4K5 (i*16) 16
  | 6 => packedAt g4K6 (i*5) 5
  | _ => 0
def g4I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g4K2 (450+((h/3+packedAt g4K2 (441+(h % 3)*3) 3) % 12)*5) 5
  | 3 => packedAt g4K3 (1985+((h/17+packedAt g4K3 (1900+(h % 17)*5) 5) % 66)*7) 7
  | 4 => packedAt g4K4 (3902+((h/46+packedAt g4K4 (3672+(h % 46)*5) 5) % 166)*9) 9
  | 5 => packedAt g4K5 (848+((h/16+packedAt g4K5 (768+(h % 16)*5) 5) % 58)*7) 7
  | 6 => packedAt g4K6 (6+((h/1+packedAt g4K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g4Pos : Nat → Bits
  | 0 => 0xebb79ebb555fa8b7545a596a97ecbfcb2492f7
  | 1 => 0x35d2ab2dab48ad5bd2ac62bb2bb3f2c4e12e78
  | 2 => 0x66ebd5a93e6b3a6d9936ccdefea555514b8f91
  | 3 => 0xb972e7cfcf8dcf8ee3c777f34d3a69a693f42a
  | 4 => 0x0
  | 5 => 0x3e7cf9f1f3f1f3f0fdff871c71c38e38fe4944
  | _ => 0
def g4Neg : Nat → Bits
  | 0 => 0x1fc01fc000000000001fc0fc0000077
  | 1 => 0xfe01fffe0000fe00001f81fff000e00e78
  | 2 => 0x3f80fffe000000000007f81ffe000000038f80
  | 3 => 0x3fff0000000000000007ffe00000000003f000
  | 4 => 0x0
  | 5 => 0xc000000000000000fff8000000000000fc0000
  | _ => 0
def g4Atlas : Atlas := ⟨6,rawDecor 47 g4Pos g4Neg, 0xfffafffaeea0eea0fffafffaeea0eea0fffafffaeea0eea0fffafffaeea0eea0fffafffaeea0eea0fffafffaeea0eea0fffafffaeea0eea0fffafffaeea0eea0, g4N, g4R, (fun _ _ => 0), g4I⟩
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
def g5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g5K5 : Nat → Nat
  | 0 => 0x3001b50000000c496004a4c69f160000e0000b1e4c6020a545caae2874783481441c0045589349c122001c029200001940b518000000af425800d1600b02a4000804f510ed42ed32fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41fc31fc21fc40fc30ec20fc20fc10ff40ff30ff20f710ff10ff41ff31ff21fe10ff42ff32fe21ee20fe20ff43ee32fe32fe31fe30fe43ee42fe42fe41fe40
  | _ => 0
def g5K4 : Nat → Nat
  | 0 => 0x702f854a4300e000066d1a800001108000a24b1311c26001ea04183e0c924c837370587400158189477110b8c2330400000040f9e05062429bce6320e9d4c05820884b6841f8008000151705231078004e5e352010c0d2a800cc4c0c05c0000001ec000000000006334800767e048280e56270e04a2c0006cd87a000000268119fc007600174780e27800e83923000a0820914cd6242b920ce712a1085a143e8bcb4020f0d10e4d05a0c0a7922000f865101c86c430d1648a14660220082a54508838120002a1004809001802c308200004104008808300c000240f888281f1104c2f2a021de54041bca80637905886eaa221f944142f2882657515842ea2a205d45430ba8a841e425442ea2b105d45630ba8ac81cd324c29a6a106b5094096a28416d5250eda8b215b51420b6a2c416d458cada6b195b54843b69a8416d35882da6b215b49441b6928636d25102da4a185b49740b692e616d25c42da4ba0db49731b692e876d2590eba6a20d74d440ae9a8413d450c67a8a184f51420cea18876c52502de4b21db14930b792e876c25442e8a2a1ddc5640bb8ac617715882de4b98dbc9741b792e216c5050ade0b215b14132b782c657b05886de4b985bc9740f088041f110083d220107944020f28a841cd350835a8a105bc16209fa2841af45082be6a1073cd4209fa2861ad42d02be6a20734cb30b7928616f25103e221905dc5420f38a84177150c2ee2a207c44310f2a1621e532c43ca4b885dc5410f392e21e420c427e8a18ddd4543af9a8836f250c6de4a20de94031bd28083e820842dea4a05bd4930f312a216e25443ca21107945620b782841e715883d0411079c4220b7a9a856e5210fca2119734ca32b792865e7108caeca221de94043f8884616c258c2dc4b185b91532f288485ad4290ade4a2179c4242f8884816c25902dc4b205b8d642
  | _ => 0
def g5K3 : Nat → Nat
  | 0 => 0x17225218000142c00022681270e2142b00b02011c000242cc0600004049e1e48020000c0180054e8d0014000265d2a34c700143ebd5315a650803602e00c1910a032105f0441324c3413544020e844142503214544020d851510083613544020d44d510083314544020d8440525036110149309c5805150f195050c43d24d510083294544020d841725c43155150c43d14d510083254544020d14553508325155142099d95108824d3614142c34d5450824d3609630934d8259022d46141328b518259022d46096309a1815250f611014142d8440504cbc1104d420e844145083630544220d8454208830d35d1420e8443450830d45cd420f0443350836365440209959710882e36544020d14d7150832545c5420b14d820c42a54608310b24d820842a94608210d8440258c3611009640
  | _ => 0
def g5K2 : Nat → Nat
  | 0 => 0x238c80018a00810059904d91014142e026a8828a1064136440258c3209b22012c81885191014132c428c8804b2062146440258c3809aa21a2841c051510cd420
  | _ => 0
def g5N (k : Nat) : Nat :=
  match k with
  | 2 => 9
  | 3 => 50
  | 4 => 136
  | 5 => 48
  | 6 => 1
  | _ => 0
def g5R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g5K2 (i*49) 49
  | 3 => packedAt g5K3 (i*38) 38
  | 4 => packedAt g5K4 (i*27) 27
  | 5 => packedAt g5K5 (i*16) 16
  | 6 => packedAt g5K6 (i*5) 5
  | _ => 0
def g5I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g5K2 (447+((h/3+packedAt g5K2 (441+(h % 3)*2) 2) % 13)*5) 5
  | 3 => packedAt g5K3 (1968+((h/17+packedAt g5K3 (1900+(h % 17)*4) 4) % 67)*7) 7
  | 4 => packedAt g5K4 (3948+((h/46+packedAt g5K4 (3672+(h % 46)*6) 6) % 164)*9) 9
  | 5 => packedAt g5K5 (848+((h/16+packedAt g5K5 (768+(h % 16)*5) 5) % 64)*7) 7
  | 6 => packedAt g5K6 (6+((h/1+packedAt g5K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g5Pos : Nat → Bits
  | 0 => 0xebb79eadaabfa8b7565ab2d52f6cbfcb2493e7
  | 1 => 0x35daab36d5a8bd5b98acc57e57b3f2d4492ef8
  | 2 => 0x66e3d5a49f2b2a6dd33699b5fd255541e38f21
  | 3 => 0xb972e7c7e7cdcf8ee1c7efe69a3a69a693f44a
  | 4 => 0x3e7cf9f8f9f1f3f0fdff0e38e3c38e38fe4894
  | 5 => 0x0
  | _ => 0
def g5Neg : Nat → Bits
  | 0 => 0xfe01fc000000000003fc0fc00000e7
  | 1 => 0xfe00fffe00000000003f03fff000000ef8
  | 2 => 0x3f80ffff00000000fe07f03ffc000000e38f00
  | 3 => 0x3fff0000000000000007ffc00000000003f000
  | 4 => 0xc000000000000000fff8000000000000fc0000
  | 5 => 0x0
  | _ => 0
def g5Atlas : Atlas := ⟨6,rawDecor 31 g5Pos g5Neg, 0xffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0ffeeeea0, g5N, g5R, (fun _ _ => 0), g5I⟩
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model
def g6Hint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x8e
  | 8 => 0xcb
  | 9 => 0x209
  | 10 => 0x249
  | 11 => 0x24d
  | 12 => 0x289
  | 13 => 0x28c
  | 14 => 0x2c9
  | 15 => 0x409
  | 16 => 0x40a
  | 17 => 0x40c
  | 18 => 0x449
  | 19 => 0x44c
  | 20 => 0x589
  | 21 => 0x5cb
  | 22 => 0x749
  | 23 => 0x74a
  | 24 => 0x74b
  | 25 => 0x74c
  | 26 => 0x94b
  | 27 => 0x94c
  | 28 => 0x94d
  | 29 => 0x94e
  | 30 => 0x98a
  | 31 => 0x98c
  | 32 => 0x98d
  | 33 => 0x98e
  | 34 => 0x9ca
  | 35 => 0x9cb
  | 36 => 0x9cd
  | 37 => 0x9ce
  | 38 => 0xa0a
  | 39 => 0xa0b
  | 40 => 0xa0c
  | 41 => 0xa0e
  | 42 => 0xa4a
  | 43 => 0xa4b
  | 44 => 0xa4c
  | 45 => 0xa4d
  | 46 => 0xb09
  | 47 => 0xb0c
  | 48 => 0xb0d
  | 49 => 0xb0e
  | 50 => 0xb49
  | 51 => 0xb4b
  | 52 => 0xb4d
  | 53 => 0xb4e
  | 54 => 0xb89
  | 55 => 0xb8b
  | 56 => 0xb8c
  | 57 => 0xb8e
  | 58 => 0xbc9
  | 59 => 0xbcb
  | 60 => 0xbcc
  | 61 => 0xbcd
  | 62 => 0xcc9
  | 63 => 0xcca
  | 64 => 0xccd
  | 65 => 0xcce
  | 66 => 0xd09
  | 67 => 0xd0a
  | 68 => 0xd0c
  | 69 => 0xd0e
  | 70 => 0xd49
  | 71 => 0xd4a
  | 72 => 0xd4c
  | 73 => 0xd4d
  | 74 => 0xe89
  | 75 => 0xe8a
  | 76 => 0xe8b
  | 77 => 0xe8e
  | 78 => 0xec9
  | 79 => 0xeca
  | 80 => 0xecb
  | 81 => 0xecd
  | 82 => 0x1049
  | 83 => 0x104a
  | 84 => 0x104b
  | 85 => 0x104c
  | 86 => 0x124b
  | 87 => 0x124c
  | 88 => 0x124d
  | 89 => 0x124e
  | 90 => 0x128a
  | 91 => 0x128c
  | 92 => 0x128d
  | 93 => 0x128e
  | 94 => 0x12ca
  | 95 => 0x12cb
  | 96 => 0x12cd
  | 97 => 0x12ce
  | 98 => 0x134a
  | 99 => 0x134b
  | 100 => 0x134c
  | 101 => 0x134d
  | 102 => 0x1409
  | 103 => 0x140c
  | 104 => 0x140d
  | 105 => 0x140e
  | 106 => 0x1449
  | 107 => 0x144b
  | 108 => 0x144d
  | 109 => 0x144e
  | 110 => 0x1489
  | 111 => 0x14c9
  | 112 => 0x14cb
  | 113 => 0x14cc
  | 114 => 0x14cd
  | 115 => 0x15c9
  | 116 => 0x15ca
  | 117 => 0x15cd
  | 118 => 0x15ce
  | 119 => 0x1609
  | 120 => 0x160a
  | 121 => 0x1649
  | 122 => 0x164a
  | 123 => 0x164c
  | 124 => 0x164d
  | 125 => 0x1789
  | 126 => 0x178a
  | 127 => 0x17c9
  | 128 => 0x17ca
  | 129 => 0x17cb
  | 130 => 0x17cd
  | 131 => 0x1949
  | 132 => 0x194a
  | 133 => 0x194b
  | 134 => 0x194c
  | 135 => 0x1b4b
  | 136 => 0x1b4c
  | 137 => 0x1b4d
  | 138 => 0x1b4e
  | 139 => 0x1b8a
  | 140 => 0x1b8c
  | 141 => 0x1b8d
  | 142 => 0x1bca
  | 143 => 0x1bcb
  | 144 => 0x1bcd
  | 145 => 0x1c0a
  | 146 => 0x1c0b
  | 147 => 0x1c0c
  | 148 => 0x1c0e
  | 149 => 0x1c4a
  | 150 => 0x1c4b
  | 151 => 0x1c4c
  | 152 => 0x1c4d
  | 153 => 0x1d09
  | 154 => 0x1d0c
  | 155 => 0x1d49
  | 156 => 0x1d4b
  | 157 => 0x1d4d
  | 158 => 0x1d89
  | 159 => 0x1d8b
  | 160 => 0x1d8c
  | 161 => 0x1d8e
  | 162 => 0x1dc9
  | 163 => 0x1dcb
  | 164 => 0x1dcc
  | 165 => 0x1dcd
  | 166 => 0x1ec9
  | 167 => 0x1eca
  | 168 => 0x1ecd
  | 169 => 0x1ece
  | 170 => 0x1f09
  | 171 => 0x1f0a
  | 172 => 0x1f0c
  | 173 => 0x1f0e
  | 174 => 0x1f49
  | 175 => 0x1f4a
  | 176 => 0x1f4c
  | 177 => 0x1f4d
  | 178 => 0x2089
  | 179 => 0x208a
  | 180 => 0x208b
  | 181 => 0x208e
  | 182 => 0x20c9
  | 183 => 0x20ca
  | 184 => 0x20cb
  | 185 => 0x20cd
  | 186 => 0x2249
  | 187 => 0x224a
  | 188 => 0x224b
  | 189 => 0x9c953
  | 190 => 0x9c955
  | 191 => 0x9c956
  | 192 => 0xa0953
  | 193 => 0xa0954
  | 194 => 0xa0956
  | 195 => 0xa4153
  | 196 => 0xbc451
  | 197 => 0xcc255
  | 198 => 0xcc955
  | 199 => 0xcc956
  | 200 => 0xcc9d2
  | 201 => 0xcc9d5
  | 202 => 0xcc9d6
  | 203 => 0xccbd5
  | 204 => 0xd0294
  | 205 => 0xd0956
  | 206 => 0xd0a16
  | 207 => 0xd4454
  | 208 => 0xe8591
  | 209 => 0xe8592
  | 210 => 0xec5d3
  | 211 => 0xeccd1
  | 212 => 0xeccd2
  | 213 => 0xeccd5
  | 214 => 0x104294
  | 215 => 0x104752
  | 216 => 0x104953
  | 217 => 0x104a13
  | 218 => 0x104a52
  | 219 => 0x104cd2
  | 220 => 0x104e93
  | 221 => 0x104ed2
  | 222 => 0x12c955
  | 223 => 0x15c955
  | 224 => 0x15c956
  | 225 => 0x15cbd5
  | 226 => 0x15ccd1
  | 227 => 0x15ccd2
  | 228 => 0x15ccd5
  | 229 => 0x15ccd6
  | 230 => 0x15d052
  | 231 => 0x17c451
  | 232 => 0x17ccd1
  | 233 => 0x17ccd5
  | 234 => 0x1b4953
  | 235 => 0x1b4954
  | 236 => 0x1b4955
  | 237 => 0x1b4cd5
  | 238 => 0x1b4cd6
  | 239 => 0x1b5053
  | 240 => 0x1b55d5
  | 241 => 0x1c4953
  | 242 => 0x1f0294
  | 243 => 0x208cd2
  | 244 => 0x209053
  | 245 => 0xcc9c95d
  | 246 => 0xcc9c95e
  | 247 => 0xd0a095e
  | 248 => 0xecccbdd
  | 249 => 0x104a095b
  | 250 => 0x104eccda
  | _ => 0
def g6K9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def g6K8 : Nat → Nat
  | 0 => 0xc84b0000168000022003c389002299629400d7b64629c007c14e9c16098c2806c0c534fca0f4418b3b2ea9e801a9caae79050b43220c00484c61050e80076610f9c605680004010488ac008028a5b67000807b48c03faa801fd4300fea1007f50403fa800bfc5400fe98007f48403fa4001fd1002fe28817f1040bf84203fc5001fe2000ff0c007f84003fc1006ffa902ffd0813fc4605fe2101ff10037fd4c17fe8601ef2303ff91817fc4c07fc600bfe5404ff2981ff9480bfca203fe50
  | _ => 0
def g6K7 : Nat → Nat
  | 0 => 0x5b2301fcc0d1001fec0d5001fe8c14001fe8c11001fdc0d103efb8c12301f78c13052ff8c1544effc0d5346ffc0d523affc0d5101ffc0d5001bfd8d034aff8c14342ff8c14236ff8c14101ff8c1403effc0d2332ffc0d1301ff8c1302eff8c12101ff8c12001ff8c11001fdc0f1073fb8c32373fb01b2305bfd193024ffd193002bf9853022ff9853002fd8db1006bfd591335ffd591305bfd191334ffd191303bf9891333ff9891303fb85b2301bfc191332ffc191341fbd592306bfd592341ffd592340fbd192305bfd192340ffd19233ffb9852302bfc59233fffc59233efb9812301bfc19233effc192300bf9594300ff9594300bf9594200ff9594200bf9594100ff9594100bf9594000ff959401cfdd151040fb9512305ef9514305ef9514205ef9514005df9515405ff9515451ffd155349ffd15523dffd15512dffd155005bfd954505ff9514305ff9514205ff9514105ff9514040ffd152334ffd151324ff9513030ff9512120ff951201cff9511089fdd171075fb9532300fb9592300bf9592300ff9592300bf9591300ff9591300bf9590300ff959031bfd94d1004f394d2304fb94d2304f794d2304f794d0304df94d5355ff94d4504ff94d5348ff94d523cff94d512cff94d5004bfd955304ff94d4344ff94d4238ff94d4128ff94d4004ff94d2304ff94d1304ff94d032fff94d121fff94d201bff94d1088fd94f1004fb94f2300bf9591200ff9591200bf9592000ff959201afd9491003fb9492303fb9492054df9494503df9495254ff9494550ff9495303ff949523bff949512bff9495003bfd95524cff9494303ff9494237ff9494127ff9494003ff9492333ff9491323ff9490303ff9491203ff949201aff9491087fd94b1000fd9591000bf9591000ff9591002fd9451302fd9452102fd945103ffb9452302df9455153ff945544fff9455347ff9455202ff945512aff9455002bfd95514bff9454343ff9454202ff9454126ff945403fff9452302ff9451322ff9453002ff945211eff9452002ff9451074fb9472301fe9413001fe9412001fd941103efb9412301df9415052ff941544eff9415346ff941523aff9415101ff9415001bfd95504aff9414342ff9414236ff9414101ff941403eff9412332ff9411301ff941302eff9412101ff9412001ff9411001fd9431073fb943232dffd195005bfd19502cff98d5004bf98d502bff9895003bf989502aff9855002bf9855002fd95b103dffd195105bfd19513cff98d5104bf98d513bff9895103bf989513aff9815101bf9815149ffd195205bfd195248ff98d5204bf98d5247ff9855202bf9855246ff9815201bf9815251ffd195305bfd195350ff9895303bf9895303fb95b234fff9855302bf985534eff9815301bf9815353ff9855402bf9855452ff9815401bf98154
  | 1 => 0x303ffd091203ffd09201cffd091000bfd891300ffd891300bfd890300ffd89031bfd88d1004fb88d2304f788d5304f788d0355ff88d4504ff88d5303ff88d523cff88d512cff88d5003bfd892304ffcc94303ffcc94238ffcc94128ffcc94003ff88d2304ff88d1304ff88d0303ff88d1203ffcc9201bffcc91000fdd891000bf8991000ff8991002fdc495102fd885103ffbc492302fb8852153ff885544fffc495347ffc495202ffc49512affc495002bfd89124bff8854343ff8854202ff8854126ff885403fffc492302ffc491322ff8853002ff885211eff8852002ff8851001fec095001fdc09103efbc092301fb8812052ff881544effc095346ffc09523affc095101ffc095001bfd89204aff8814342ff8814236ff8814101ff881403effc092332ffc091301ff881302eff8812101ff8812001ff8811005bfd192130ffd192101bf981212eff9812100ffd8d4500bfd8d4500ffd8d5200bfd8d5200ffd8d5100bfd8d5100ffd8d5000bfd8d501dfdd4d1004fbd4d2306f7d4d5306dfd4d4506dfd4d5106dfd4d5006ffd4d4504ffd4d5306ffd4d5206ffd4d5106ffd4d5004bfd8d5304ffd4d4345ffd4d4239ffd4d4129ffd4d4004ffd4d2304ffd4d1304ffd4d0331ffd4d1221ffd4d201dffd4d1000bfd8d4200ffd8d4200bfd8d4100ffd8d4100bfd8d4000ffd8d401cfdd0d1004fbd0d2305f7d0d4305efd0d4505efd0d4105efd0d4005ffd0d4504ffd0d5349ffd0d523dffd0d512dffd0d5004bfd8d4304ffd0d4305ffd0d4205ffd0d4105ffd0d4004ffd0d2304ffd0d1304ffd0d0330ffd0d1220ffd0d201cffd0d1000bfd8d1200ffd8d1200bf8d92000ff8d92000f9443231afdc8d1003f34db2300fb5532304fb54f2303fbc8d5200fb5472300fb5432303fb55b2303bbd8d2304fb50f2303fb8c94200fb5072300fb5032303fb51b2375fb1532303fb4db2304fb4c72304fb4c32303fbd5b2303fbd1b2304fb14f2304fb10f2303fbc8d1203fb8c92003f7c8d2354ffc8d4550ffc8d5303ffc8d523bffc8d512bffc8d5003bfd8d234cff8c94303ff8c94237ff8c94127ff8c94003ffc8d2333ffc8d1323ffc8d0303ffc8d1203ff8c92000fb443231aff8c91003fb45b2374fb1472374fb1072374fbc5b2374fb0c72303fb41b2373fb1432373fb1032373fbc1b2373fb0c32373fb0432376fbd432375fbd032300f9c432374fbc432376fbd472375fbd072304fbcc72373fb8432304fbd4f2304fbd0f2303fb15b2303fb11b2300fdd8d1000bf8d91000ff8d91002fdc4d5102fd8c54102fd8c5103ffb8c52302f7c4d1353ffc4d454fffc4d5347ffc4d5202ffc4d512affc4d5002bfd8d134bff8c54343ff8c54202ff8c54126ff8c5403fffc4d2302ffc4d1322ffc4d0302ffc4d121eff8c52002ff8c51074fb8c72374fb
  | 2 => 0xd145103ffb1452302df1455153ff145544fff1455347ff1455202ff145512aff145504bff1454343ff1454202ff1454126ff145403fff1452302ff1451322ff1453002ff145211eff1452002ff1451002bd1854300fd1854302bf185434bff1854302bf1854243ff1854202bf1854026ff1854002fd1055102fd1054102fd105103ffb1052353ef1055402ef1054153ff105544fff1055347ff1055202ff105512aff105504bff1054343ff1054202ff1054126ff105403fff1052302ff1051322ff1053002ff105211eff1052002ff105103ffb1852302bf059233fff0592302bf1853022ff1853002bf185201eff185203ffb0492302fb0852153ff085544bff0854343ff0854202ff0854126ff0854022ff0853002ff085211eff0852002ff0851052ff1815401bf181544eff1815301bf1815346ff1815201bf181523aff1815101bf1815101de1415001fe1415001fd141103efb1412301df1415052ff141544eff1415346ff141523aff1415101ff141504aff1414342ff1414236ff1414101ff141403eff1412332ff1411301ff141302eff1412101ff1412001ff1411001bf181434aff1814301bf1814242ff1814201bf1814136ff1814101fe1014001fd101103efb1012301ef1014052ff101544eff1015346ff101523aff1015101ff101504aff1014342ff1014236ff1014101ff101403eff1012332ff1011301ff101302eff1012101ff1012001ff101103efb1812301bf019233eff0192301bf0191332ff019133efb0c12301f70c13052ff0c1544aff0c14342ff0c14236ff0c14101ff0c14001ff0c1302eff0c12101ff0c12001ff0c11001bf181212eff1812101fe0812001fd009103efb0092301fb0812052ff081544eff0095346ff009523aff0095101ff009504aff0814342ff0814236ff0814101ff081403eff0092332ff0091301ff081302eff0812101ff0812001ff0811001fe0411001fd041103efb0412352ff041544eff0055346ff005523aff0055101ff005504aff0414342ff0414236ff0414101ff041403eff0052332ff0051301ff041302eff0412101ff0412001ff0411000ffd894500bfd894500ffd895300bfd895300ffd895100bfd895100fbd895000bbd895000ffd895000bfd89501dfdd491006fbd495245fbd494241fbd492306dfd495006ffd494506ffd495303ffd495206ffd495106ffd495003bfd89524dffd494303ffd494239ffd494129ffd494003ffd492335ffd491325ffd490303ffd491203ffd49201dffd491000bfd894300ffd894300bfd894100ffd894100bfd894000ffd89401cfdd091005fbd094240fbd092305efd094505efd094005ffd094551ffd095303ffd09523dffd09512dffd095003bfd894205ffd094303ffd094205ffd094105ffd094003ffd092334ffd091324ffd090
  | 3 => 0x10000301000c49040003180001010400000c12006100010700000103230201000003021202011a010b00030e060004047c06010103040a06120900100005000f05020000051303130006030b000900180c0a010902040010130208000d000605060401050d040a00040c0200010602011301a103022805252b03021506020a0500010b000200030a2903010107090c3b02020000000002054a150081000101360a000302060201014804030000180201020107110000010c010106060612000a04000900151902040f0310020201010403070010010003055e00000000060d09070b0a0f07000008050400f94412300f348d5300f348d0300fb48d4500fb5592304fb48d5300fb5492300fb48d5100fb48d5004bb4db2300fb5192304fb4c94300fb5092300fb4c94100fb4c94040fb1512300fb5852300fb5812341fb1592340fb1192304fb48d1304fb48d0300fb5091200fb4492300fb5492000fb5092000fb4092300f754d2300f750d1300f754d0300f750d0300f740d2300df5155300df5155100df5455300df5155000df5415300df5415200bf5594100bf5594000ff5855400ff5815400bf5192300bf5191300bf5193000ff5594305ff5514300ff5414300ff5894300ff5854300ff5814300bf5192100bf5192000ff5594205ff5514200ff5454200ff5414200ff58d4205ff50d4200ff5854200ff5814200bf5191000ff5594105ff5514100ff5494102ff5454100ff5414100ff58d4105ff50d4100ff5894105ff5094100ff5814100ff5594005ff5514000ff54d4000ff5494000ff5454001ff5414000ff58d4005ff50d4000ff5894005ff5094000ff5854005ff5054051ff1195305bf1195349ff1195205bf119523dff1195105bf119512dff1195005bf1195005df1515405ff1515405ff1514305ff1514205ff1514105ff1514000bf4d91000ff5513000ff5193004ff50d0300ff5090300ff5053001ff5013024ff1513000ff5853005bf1193024ff1193000bf4991000ff5512100ff50d1200ff5192103ff5091202ff5052100ff5012130ff1512100ff4c12100ff5812105bf1192130ff1192100ff5512000ff54d2000ff5592003ff5492000ff5452001ff5412000ff50d2000ff5192003ff5092000ff5052001ff5012020ff1512000ff4d92000ff4c52001ff4c12000ff5852003ff4852006bf1592021ff1592005bf1192020ff1192000fb4c91000ff5511000ff54d1000ff5491000ff5591002ff5451001ff5411000ff50d1000ff5091000ff5191002ff5051001ff501101cff1511000ff4c91000ff4d91002ff4c51001ff4c11000ff4991002ff4851001ff4811006bf159101dff1591005bf119101cff1191053ff1855402bf185544fff1855302bf1855347ff1855202bf185522aff1855002bf1855002fd1455102f
  | 4 => 0x9fb5cb0a9f059caf18f3c5245516d9b05678215ab3fccde95e61c1a6412355855062132133a44c4ad9e1a9edae6495e26a175f3ea35bdcd08f327bdc431c1358428e03194352c0629545f25b171526759642900660f38383b68c6e788c939b8d65f0f318024b37038c644dcfcc10258bb017420a82d5306e4816b09c6929a5b657aeade58fa000b15ff429290583846f62a0fab875fa63179a963bf7a80011860cf080011c7bd0a951c4055b6f0001e33e6001d5862000000001770004e22a4530005f4fecac13834e3cb86753168005db12d73d112b300033f3405200025e538001665400065200007000000cf35621a45011226c0680043d8ab120004970527aa3c1792770d36f1060000054400133d344e2001451a424c97f418399ca8c7341b080c278825f6cfe87b448c38fb8733d19c22c5f802e9a00000135973c2d3d9a7f1665668f815a30ca89c002ba80055f51cdc619660002246923a91aa1c4af7f200160daebd13b8768a319970086ba50da07d449981034eeaf2472e223a3a5be098fa08548a0014624d3ec1696928b54bd5e1faa62d69f8f8e1fb5580f2ad69c49cbf7d437049b4078141425cdb6c54db2e3746896b85e20c14da5669407a6eea1582d8809fea9f8ff67a0e86c6271f82b63b4497fa6d0e4cc50397f3b6c6c54c2a2565daa005925d2bfa4e7637769b20a399db2ac19499a7647103e6f0e335c7909a3737fc0f4772234915014f246a9c7d27232d99a990182745c2d95d6c652a32401f52324983e6eb5fc888c03853800e9631a5d871757c674327280268c90308604a592b91fe8b515a7d0014e6a7b3fa7e3c42035d1f58761162100c3acc995b87c001fc343bd8656f21b26a31140000073b02ca467a000bc800329bc61ea610000008fc003a10014da0500045c001270699cd361294b1bb49a521e1760200247000000002f588a424003363a8a55a0eeb09a02095b6200c5295a03103b000e0902020100080015404000003402150b0006023100ca001f060018050053035a16080e020501920d029a100a1d081d040c0d04220000001207000e0110010d1f350502010005003106090e0b070700050015050804126f510b0502030f020320000500150100000000460004010008361a0102011208000b0800ad110a0d160f023003040f010003000025200113010a6a250312e20a1434bc010203312c30000a040d00220035020a6f70250b0d010800000c000b10000b0c0609080f0000010108011e38002c07723a041e0101271500130002720a0577080029000206270200030400000e0c052801030d25030e0508020a00120db1cd050902200115040764011c0b01010007150311000000000100266601020804330200080206000f04090122a80a04150143020d030e030e000603120200010a0a200b000e0100
  | 5 => 0xd5af40e9f2af41fb22d0d1785440172d9e9b36bd4259e56f017d63800c8c5b51c97231515ccb62653b55ca268564752402392c36745d65dcb85a42f341c1092e23688d60e002b4b7a0015ee5b3f251f68747000286525550004c2000004b7945011541270005300050e862a2800000000928000000009e01fcea120d62ce12a000e79753425be388df27e6f80000d08cba0bedb11cfc86000004429a40380020ed0d54410d2490200000000b70758000c60010325d3413ee4100013602b40f3e42894147b03eb00019d03c0000004c8006aeac1475d10008ec00149960382000e13fb0013e400417c5368819d7c6dcccc8d39fb2c19d08000000904002b85d60025e8340d0000d2233082610000353460016e846860000000591beb65c8d6372abe9e4e495649e552d5c596a864fb79000000002c57e362a859990006f400000000518004990766180000051b2203890777f386599ee484f9e32369604dca3406b0949c2a43f41e1112c4e59c11a888a800b47849df48c2a94b0e94462aa001619ab88e3d4de30c5c65d5c1324172a2c101194eb50ced010c6191d0ebc88e4f4400507b20f828fbf3000000c8800bb38440014f000bd8ef013692002f380083796027a0868ae69050af0000006b800b066835302a630ffdfd0000280019b89400182dea057000002fe33134f5b62e38a8f41beb63a7d188deb42e2552e8d24da82e691460bcd2c7a073e85d21c6b0be44aba2021c780004800315a0f0008c63dc4b001668d40876d40012fab40000f2b0c123f1610760008271780000063800197800000001dadfab8d1a4bf000000000000002b93e09d64c000f61f26760fa285ad0008b2002814438569340015dc945847c32a71a0002ad0d23f8f19a22f17b620acd1a4aa9807a00086c0031d2110007d80058b84200000000a020000034c5fe000000ae3109ac001c98cf5c047800001a700000028b39c003a6cc29c40041f000002bc800749431cb62306c6bc5c28377b0ce970004a235000000cfc000006049a8d01ea87cbbd2b5c718d8aa378138283438240e850774b2aa5167ca8097019b0bbf130778a57b37c1e3b5e21132f28ea944222c864933f4c51c64c50e416b00db636e31317559226dd0b4cd198ef4217baaaa54403bd94608dd9b3698644c7e95a283c574db18d9a5e8a9e05bfa6563c51592688f0f4f3dfb563175502c27e19b17d915ef305532929988d3304809d0d673c6106ff4f2c2e4e4b93568ad1176e3205b8dba0b59ec153d2976e8f3beb277a0b3396b81a39660197d2b2a27fae840c442bb6a8d5836ab310f58d65716b5c403160abbdd7b45c066d331a3606aab6b01e900ffd464dc5d271dc39be6cebb86ad1193d3947591e2eca704764aaacb31a53257a44f0865a467cf5aba15b6e449e7f54e2aafa0f7a1595de58fc
  | 6 => 0x4bbb40e9fc4c48722e47b354eb3812940053700020942dcd0010600047700000000000b90000000004db674ee00080505800000a27a4400265000501d91fb2caa048a580260000004ed000000000008f8e40001cc0004fad4d93976000000001484a00056200167c002cf0000031169685c2021e641a411b15b29792f9948b426c0c002379aa8740017264d36ae7000000334002f7000823001ed8006fcd42f7800730001d756b000af40002342a000e2250037862488000004980059857c002028002c8d82bf0002b4001869689881ec003280000000030e1ec000002c80000028dcc91ba0025cbf60014a25aae6d292a5e50002a565e121c809d5fc00226c14db0f333b3d02ae7da3b946398c0578d6432dfba18376da0e761c4df6c8e3dc525ac9eab352088a19c0526606be05381e0007634525b158b52b8e1631e7409194d14cf063c061beeed0c1399000f84001d53295964349b1c066e90ca1a1f61ab21a6d3a001480d055cc552a3e69091c35066464c000178008a4064e5912938f4cf7d8db6a122049b65c1a681897b8325e89ad30b8e6b56c1b1c1d056949b40140e6535045dcc284c99eab700d4e4bc8cc002f98004393cc004ca0000881b800004f5c6abc64c6000001ddd320032120b8dc00000000c502c5d99fc4198dc793bc622c58a3c3b02d17c001029618519b5af00000080000624640001310018f4ce3d223a00200a2792aa82790ead1a9df47ba000230e7b3ceb58fb9f10e10000000067b7eb568002731740034380044bac6c71d937e7172d1f118e0015d800c620000025900036226d6f0019c815800d56001102c97d20004f800ba4003004c60012d00000052246c1482d696afc740000b8b42ee9eacd66268e56ead41fc000175d2d4c001096ae718006a3001105b85f62dcad543800562d38002c08acbbe8024f9a60010caf1000000b56380019d4004237e16a9f5000a122459930b0003598ca62d16dd568a363174f84ad8cb6f372de8452720030626cca64824480000000095a993e4003520b6000370808005086e684496b4cbe59f18153000267142001882c3d7442d0dd9aa1f0e8ceb2e54d3c209a300799e18fb0f09d83c1d9441a9600cac000c2bc40033ba95000001a79d3aa6bc02db9395cb3693a35634f3d0d8587725bf1f8beb6080274e800005fe311794bd976fe875aa89f10bcefce6e269685176327888a29a62df44427b0004153d6ad064e1642acca74b71610647accf5022da9297312d35bbe48cafc0001ceb10300bfce2b94210009af022913b8ccd8e51d45dcbc42ef89410c7a9c90e97c4ee6ef03ef5484b91ecaa8c294d8ee636439013536d3fc8f8e1b091f3a26e0976c044f692dbbb32c3e9adad56ee224c61330b2496f371022ce509a8ca85695334e0bf6e0494c2c25f576e539714075d4a2
  | 7 => 0x40aab2418fe760d9000000b9d1c47
  | _ => 0
def g6K6 : Nat → Nat
  | 0 => 0x6480af77316c4a8015f6715411302bece2a8242df7d81e56440ff7730a46a837cfe079591000ddcc2312a07ff995923c40ab7b30ec2a8006ee61d895074bdce2a8646e9f995b23c40027f0bcaca1806f657d8543009fc2f2b284013f85e5650072fba3aa288206ee6448d5105d7e8ca1aa20b5f95f61552127f0bcaca0badee74547233dd7e8d232a2017b85e5648c027f0bcac91804fe179590304bec2f2b226377d9cd51440137731a46a88257e57d8553809fc2f2b22679b798f6354412f739aa391804fe179592003bec2f2b224357d9c9514400ef7392a291aa67e62515517a9fc2f2b22477bb98b6254406fd382a29800df617959103eddcc091aa2033f85e56440eb7d306c0a8b9dee70547231cbee8eab2200b3fd1d564406efb39aac88024fe73559101abece4ab220073f9c956440027f13caca1804fe2795941009fc4f2b28039bdd190154902f73a2a49182dbe7454940859fc4f2b285137dd1d52c41275fa348ca9004fe2795913009fc4f2b20637bd98d0154812f713cac91825de7354903819fc4f2b247117d9cd52c41236f31ec6a9005f62795910009fc4f2b220057d9c552440fef738aa491814fe279591247decc3b0aa403bd98101548faf7382a49180dee279592001afcafb12a0033f89e564811b7d306c0a900df67054b10aeedcafb12a15dbb95f62540167fa3aac90024fe7355920029fce2ab240057d9d952c40167fa3aac89024fe7355912019fce0ab224013f8de56508027f1bcaca0804fe37959401cdee8c80aa7abf39912354c16df3a2a6a002d7e57d8d45869fc6f2b287137dd1d53c41475fa348ca9804fe3795912009fc6f2b24035bd9890154d43e7392a69181dce379592303bdc6f2b246077b9c9534800eef1bcac91aa67e6251553039fc6f2b2470f7d9c953c414377316c4a98d7e6564432354edcacaa6470ff995b10c8e07e71bcac91805f63795910009fc6f2b220057d9c55344353e730a46a98157e57d8d51029fc6f2b2269fbd9876154c077b30202a9e9fce6048d5301bbc6f2b206035f95f63540067f1bcac81a76fa60d815301bece0a9e200b3fd1d5640c0e7f392ac8181dee7654323029fce2ab206057d9d953c40167fa3aac8981cfe725591303bdceca8e46033f9c15644d02f73a2ac9182cff47559233fbdce2ab246053f9c55648cfaf7382ac9180cfe7055923009fc8f2b206013f91e56448027f23cac90005f64795910009fc8f2b220057d9c54544c0afb38aa8881feee6148d4502afcaf232a2053f91e565054f7b30ec2aa3a5ee715532301bf4e0aa26003bd98110550fb7730246a280dbe479594001afcaf232a0033f91e565014b7d306c0aa00df6705171073bdce0aa646093f9cd465480a7f38a8ca900cfe7051952039fce4a32a6077b9d954c8c0a7f38a8ca980cfe7051953
  | 1 => 0x2795941039f84f2b280073f09e5644c0e7e13cac81807f1409591000fe2612b22001be4c256440037a9b4ac88006f5319591000dea4d2b22001bd4865644003f2994ac8800775579591000eeaa32b220dfdd54256441bdfa884ac880eef7679591000de88d2b220dfbd45e564400376994ac880067d569591062cfaa32b220df9f54256441be7fbaaac88316f7179591062de8832b220dfddd4256441bf3fa84ac88317f310959106fdee212b2203bbdd465644077bba8cac883167f519591000dee832b2203bbdd5a5644077bbab4ac880ee7f569591000dee8d2b22001bd89a564418b7b10cac88007e6329591000ddc652b22001bd8da564418b7b18cac8837ff230959106fdf4612b220dffc9025644072fa23cac8802cfc47959101bbe86f2b220093f0de564406afa13cac8801cfc279591026fe4a2a022045fc94530440fff328ac291a1fe651509123ffcca28924697f59454344cff7b28a2c91916f6514d91002eeeeaa8a26057d05e5644c7b7b28a4c8801777755452102be82f2b2247ff9945324400bbbbaaa28837df41795910d4f9ca291aa791f39452340cffb728a46a89feef6548d516f9f82f2b2211dbd9460644e2f7b28ec090a9ef651d85544fdeca3b0aa68fbd94761548ab7b28ec2a825ef651d854343deca3b0a844dbd94761501777728ec4a853ef651d89135adeca313220e9bd94763449d3f328a2191ba76e515472374bdeeaa8e46bdbd946364400a7e0bcaca1814fc1795942029f82f2b2807f7b05e5648c0a7e0bcac91814fc1795903029f82f2b2407df29412340cfbf5282c091a37ea505492042fd4a0a12407dfa9410248d3bed282a681a57da5050d033efb4a081a467dbe9410648c07bdbaaa09800df8079590301ef6eaa8240037e01e56480fbf3282209180df40795910d3f9ca091aa67df39412340cfbb728246a81f6ef6548d50019f80f2b22025db940625404b77b28c4a8296fa50d81544edf4a1b02a68dbe94360548eb7d286c0a89f7e65048f1000deca1b0a875ddb94362542bb77286c4a8536fa50d890373df4a11b240e7f994110c8dcfb7282a191b9def755432373fcca18864601db9425648c033f284ac9180cfc0795943019f80f2b284033f01e56504faf603cac9180cfc0795923019f80f2b226033f01e56448027f03caca1804fe0795942009fc0f2b28281bb9912354016df3a2a0a182dbe745414205afcafb02a9073f81e565000377a30c4a8006ee64d895075bdce8a86465bafd1a4654002f703cac91804fe0795923009fc0f2b226097e81e5640cb3e731a46a8026ce6348d5004ddcc691aa009779cd5048c12bf2bec0a9bfcfe079590300ddcc6312a001bb98f62540b36f31ec6a8025ee7354323009fc0f2b224077e81e564800ef7392a091aa67e625155003afcafb02a4f33f81e5
  | 2 => 0x3bbd5a5648d07b7ab4ac91a0e7f569592341edea92b246839fd525648d02f623cac9182cfc479592300becaeb1a20013f95d3644003baa8cac89806f5109591371dda652b226019f55a5644dc73ea9cac89c067d5195913809feeaab22701bdc425644e033fa8cac89b8e7f539591371ddc652b2266b9fd5a5644c167e23cac89807f1109590300ef2a12b206ffbd4425640c0366994ac81807cd329590364dda652b20601b74ca5640c03aea9cac818067d569590364cfaa72b206ff9f5425640dfe7fbaaac8192e7c52959037fcfea12b206ffbdc425640d936f994ac81b267f539590364ddc652b2064b9fd5a5640c167e23cac818dfd25344130c1fe4a68828037fc94d104c0b3ed29aa098147da53501301bfb4a69822037f194d234406ff329a46880dfd653405231beeca680aa6ffbdd950154c13a7b2a46a9aafce5348d4548f9ca6ab24609f3d952354d23e729aa4919e7ce5348d512cf9ca691aa009730de5648d13e729a8c91a27ce535092338f9ca69928251f394d32500bfe729ac2918ffce535812304bd86f2b2465ff394d1248c7fe729a04918fede534192304ebeeaa9a4703770de5648c13afbaaa681bfddc37959037f9f86f2b20637f394d3244233e729ec091c66de538192388f8ca691e2111f994d23c4223eb29a4788447765354f107fbeeeaa9e2141bd94f6150e6be729ec291aeeee53d89505bdbca7b1206abb794f63515236f29ec6a91e6de53d8d512cdbca7b1aa037f994d10c8e23f329e47883dfcc3795923049f86f2b284093f0de56504127e1bcaca0005f65758910009fcae9322001dd54656448037a884ac89006ed329591200cfaa92b224019f55a56449c33ea94ac893d67d51959127a9feeaab224f5bdc4256449eb3fa8cac893867f529591231cfead2b224e1bb8ca56448c73faa4ac8902cfc4795912049f86f2b22401de54256481e77a884ac90006ed329592000edaa52b240019f55256480033eab4ac9031e7d529592000cfaa32b240f39f54256481e67fbaaac9010e7c539592079cfea12b240f3bdc4256480873fa8cac9031e7f529592021cfead2b240c7bb8ca56480873faa4ac900067e5395920059f88f2b240093f0de5648303f929220a05eff252441302bfd4a4a824035f99490148f63bb29220aa0d776524055279deeca80aa4a1f39495348c8fe7292069191eee524192354edca4a2a4607dbdd55248c0ef613cac91aa76e525512003edeeaa9240f37b09e56483739f292a8a1aa73e5255142d9e7ca4aa280a99fd9546549e67e13cac9047eee528192387fcca491e21dfdd94945c421fbb292a5883cdf77554b1000deca5b0a86a9db94b625155377296c4a2aa67e52d894550ddca5b12a677bb94b62544af77296c4a82feee528d920bccfecb232a4019f94a5640c0e7e13caca181cfc
  | 3 => 0xa1806dd309594300e7aa92b28601af5025650c033eab4aca1c167d549594386cfaa72b2870d3fdd54654e1bce21caca1806ef279594300de8c32b28705afd025650e1b6f984aca1806f7109594300deec32b2870d9fd4e5650e1b77194aca1804fe5751921009fcaea324001bd442565080376994aca1006ed20959427cdda4f2b28401cf55256508035ea04aca10067d56959427ccfaa92b2850b9f54a5650a167fbaa8ca942eef27959427cd7e812b2850bbbc8256508037b884aca122eef529594245edea52b2850b9fd4a5650a1777194aca1005f77551910009fcaea322001bd4c656504037a884aca0806ed329594100d7a872b282019f55a56505cb3eaa4aca0c267d5195941849feeaab28309bd10656506135e20caca0c26f7109594184cfea32b282e5bdd8656505cb5fa1caca0806ee329594184dec632b28201fc44256500037c984aca041ef5109594000dda652b28001af50e56500035ea14aca00073d549594000cfaad2b280cb9f552565020f3ea84aca041cff755594083cfea12b28107bdc4256501975fa14aca032ebf439594000ddc652b28107be8c25650073d9a2a20a00e7f34544140befe68a8826049eed15404c073dda2a8088637e654441231cf6e8a8828639edd151050873bba2a20aa41ef76544154d5f9ca891aa793f39512340d03d72a28c91a07ae545092340f5ca89928081db951235161b77b2a46a2987ae545091220f5ca8a124069e79514344c93cf2a28681a06be545192324d7ca8a32600bcfdd55450e1ade23caca1906be545192005e7eeaaa2850b6f11e56508179fbaaa8a041dbc4795940839f88f2b28017ed9506150e435fa2ec0a1c6ebf45d8142edfce8a91e2113edd1543c4227dba2a858844f77455171083beeeaa2e213bedd176150e777ba2ec2a1aeeee54d8950a8d7ca9b1286b9af95362501d75f2a6c6a1306be54d8d40dffcca888646ebeb95140c8dd7b72a2a991c2def7555323f0fcca988646a3afd164654d275fa2c8ca91eebf45919512dd7e8b232a0017b95d6148c027f2ba2c91805ee575812300adcaeb024601db95d6048c027f2ba0c918047e574192300cfcae83246015f95d0648c02bf2bac4818057e574d92000fca212b24601bd4425648c03a6a9cac91a0fcd539592300f9a612b24601bb5825648c03b6aa4ac918076d57959237bedaa72b24601db54a5648dedf6994ac91a0eef679592300dda412b246f7bb49e5648c03aea9cac91806dd309592300cfaa92b246019f55a5648def3ea9cac91c0e7d5295923819feeaab24703bbc9e5648d07b6284ac91a0e7c509592300ddec12b246f7f3cc25648def6f984ac91c0eef209592300fce212b24601bdc425648d0777a94ac91a0f6f529592381cfea52b246f7dbd4e5648def3fa9cac91c0fce329592381ddc652b2468
  | 4 => 0x70324665bec0e0644cfbf381a4788516fb03d8550a0dee07b0a873dbec0f61502bbf5186c4a8576ee30d895066fe461b1220e7f88c110c8dcff5182a191b9fea305032373fd46088646e7f98c110c8dcff31862191b57f007d8d10019f80fb1a8a033f01f63548067e03ec6a880cfc07d8d42019f80fb1a82033f01f63449cff20322191b9fe406c4323009fc0fb1a8a013f81f63508027f03ec6a0df7f3464413005bf40fb1a8193f3d192340c16ef1bec0a182ebf4655130b29fc0fb1a80013f81f634480af903ec688117f2714c11002bf40f1b22005bd985514c00b7b30a8298355f607d8d10c8f9cc291a06d53f81e36440fff31b24788116f661d853074fcc6d91e20bdfc81f63441d3f23b62191804fe17d8d45009fc2fb1aa4013f85f635401afb0bec6a88edf7574c51006cfeaca2a276f3f85f63544027f0bec6a1004fe17d8d403ddee8ca8a260b7d85f6350472fba3a628802dde37d8543b39fc2fb1a833bf58df6150e837b1bec2a1804fe178d9201abece498a2007bb9894244c0ef71bec291ba4fe17d8d1233ddcc5b122635f985910c8c077d832808980df6178d910019fc2f1b22065bec1a0644c0377b3a46a2804fe27d8d4500ddece91aa2013f89f6354402f713ec6a8004ee27d8d5000ddece91aa0013f89f6354003771bec4a8006ee27d8d50c7fceae91a203bbdd590148d07e7aba46a9e57cf5748d0341ddeacab2460d7b89f635480377ab28c91a2eef565092341edeae91aa1617bdd95248c1aef1bec4a98367f5654123b89fc4fb1aa5ddf9d5d23c422afbaba47883b6ee27d8d5200ddece99282013f89f635040377b3a64a0004fe27d8d40c6fce8e91a2039bdd190148f57e7a3a46a9e4fcf4748d0340dde8ca32460b7b89f6350903d7a3a46a2a07af474c940acbdeeca12460bafd194548c175fa328091da4fe27d8d42edfce8e91e21137dd1d23c41d77713ec6a1007e6674412300bec4fb1a2001bb9d932440027f13c6c881ffe67148d5102dee2ca8a467ff99c5324400afb38a64886a7ce7148d53c8f9ce291a067fbb9856148cfef733a2491815ee27d8d12029fc4fb1a247ff9c5b6148cff7b8b42c919feef16d852374ddc4fb1a247dfa9c123540077d832a0919f7e6604412301dee0c80a47a7f39c12354cfbe738246819f6ee60581233ebdcce81246037b89e3648006ef1bec48180cfe278d9203efd60db02467dbec1a0648cfb77836c0919f7e70748f1001bee0e91e20e7bb89e3648106f7abac091834ff574192340bde8eb02460b3fd1d0648cfef738ac091814fe71419233ffccec91e20057d9d923c4106f7abac291834ff574592340bde8eb0a460b3fd1d1648cfaf7382c29180cff074592300bdcaea3246013f95d4648c027f2ba8c89804fe575193000dea212b2870dbb4ca5650c037693cac
  | 5 => 0xf7b8a8391ce7cf23859239cdde470b246afbbc8f614c06ff398a2191ab6ef23d852073fd420a0646e7f984110c8dcef7b8a2191aa6ee32d894550ddc65b12a677bb8cb62544af77196c4a8266ee32d894337ddc65b12824fbb8cb62500cf77196c48991eee32d89031afcc65b122035bb8ca2644156f7b9aa991dc6ec27d8d523cbdee6a8e46597bdcd50c8c6ff3a9a2191aaf6f53553233cedea6a8e4659dbd4d50c8e23f3a9e47885a6ec27d8d4238bdee6a0e46517bdcd40c8c6ff3a1a2191aafaf435532338f5e86a0e4651ebd0d40c8e23f3a1e47883a6ec27d8d1273dd84f1b240073f09f635140ef63b2a99181cfc27d8d5103bd8eca8e4657bb1d950c8c0e763b2a19181cfc27d8d5000dd84fb1aa0077b1d950c8c6bf22b22191aa76c565532387fc8ad88646073f09f635040ef63b2839181cfc27d8d4003bd8eca064635f911910c8e1ff22362191807d130d8d1000fe281b1a2037fc4c363440037ca046c88007d9308d91000deaadb1a2001bd54636440037aa36c688006f5418d9101bfca65b1a2001f54df6344003ea98c6c88357d530d8d106a7ea211b22037bdd9f63441ab7a8bc6c880deed328d91000dba6d1b220bdb74c636441ab6e9846c88354ff734d9105edee2f1b220bdfcc4236441ab7b8846c880def7318d9101bfae631b220bdb7cc6364406ff3196c6880deee328d9101dbe8afb1a200d3f15e3644072fa23ec68802cfc478d9101abe84fb1a20073f09e364406bf23b2219181dec764432326fe626a022045fcc4d30440fff318a46a89ffe6314c94102faec6a8a2605f5d8d4144d2fdb89a86a0a9f7631515514feec62a8aa6a7bd8c556504ab7b89aac88015f417d8d5126dec62a3220057d05f63504fff318a6488017d7734c5106abe82f1b220d53f05e36442577b89ec0a8c8ef713d81414fdee27b0aa697bdc4f6150cfff389ec2919fef7138592322dee27b0a6001bb8c762541d3f318aa391ba7e6315072374fcc6288646053f05f635140a7e0bec6a9014fc17d8d50029f82fb1a84053f05f635000a7e0bc6c903a7e4164432374fcced886467df88c11048c07e9b1a2098297f303441544efe60680aa68dfcc0d01548ebf981aac881d7f3035451001be00fb1a2095fcc0d1050d0bf981a20a11b7f3035191036fe606a0a207dfcc0d0148ccbf981ac688197f3034c51001fe6c6882605dfcc0d62440bbf981a42881f7ea3048d503efd4609928003f6d8d504c007edb1a8098297bb03551404af7606a1a8085eec0d425014bbd1828aa82777a305415346ef460a82a4a5be8c156500eb7d81aac8800df807d8d5036df460a3220037e01f635004bf5818c4a81f7ea304c91001fb6e698220037e01e36440fbf3182209180df407d8d10019f80f1b2209dbec0f6054d2b7d81ec0a19f7eb03d81233edf60
  | 6 => 0x33bf9a6ca8e4657f34d950c8d33e791a8c9181fcf635092337f9a6ca0e464ff34d940c8ccfe791a2c9191fcf234192355f5a86aa646a9ebc8d54508e3d6a1a8391807ad545032328f5a86a06464febc8d4250153d6a32a99193fad465032355edaa6aa64601db55151c8cf3b6a9aa3918076d54543232cedaa6a864657db8c950548afb6ab2a191aaded735532354dde46a32a4017b55d41c8c02f6aba8191aa5ed765532354bdee691a8aa1bbc8d5648cf2f6b9aa391965ed73543233bdde46ab22457bbc8d564800ef613ec6a9005ed57443233bbdaeca8e46e97bdcd23544aef6bb2a191b9def7348d50739d84f1b24099bb8c94648ce2f6b9a8391945ed735032337ddc64a32424fbb8c9464800ef613ec6a1005ed474432337bdaeca0e46e97bdcd32505daf62ba839193ded765032373bdee699280ed7b15d40c8dd6f63a2a391badec745432375f58a8aa646ebdb15154c8ccf7791a2c9191eef23419231bbda6e88646a97bdd954c8ceef7bb2a39195def76543232bedeaca86466f7bdd941c8c9ef7bb28191aa7af465532327f5e8ca0646097b1cd54c8c12f639aa391825ec735432304bd8e6a0e46097b1cd40c8c6b771924c8801fcf634492374bd84fb1a2407f3d8d0248dcef613c6c9039cfc278d9201abdaec8864635f34d910c8dcef7b9a64883b5ec574432375bd88e88646357bdd910c8c12f61ba2191ba5ec715532374bd8e2a8646e9f914551c8dd3f228a2191ba76c51547230dfcc6430a86e97b1c540c8dd3f220aa391ba7e4415072374fc88288647cdeb10554c8dd3d620a8391ba7e7165472374fce2c88646e9f90c510c8dcff28322191b9dec705532373bd8e0a8e46e7da14150c8dcff4282a191b9fe4504432373ed8a0a8646e77b1c141c8dcff42028191b9fe4404432373f5880a0646e7fac1950c8dcff38322191b9fe4304432373fd02088646e7f904110c8c02f7b82a991cbeef23d815396dde47b02a4017bdc151c8ddbf5a82a191b9fe7504432376edea0aa646e77bdc150c8e4f7791ec0a1c96ef23d814200bdee0a0e46ebfad0140c8dcff3a022191bafaf405532373bdee0a064711bbc8e0644e1f7791ec090c3fc536c432300fcaa988646e779dc110c8e23f2a1e478843fe72350b1074fce20a0e46e7f950310c8dd3f2a36478843fe546c4323f0fc8a988646e7f94c310c8e1feb91a478839fe506c8f1073bdee088646e9f9d5b23c41d3f3a36478839fe506c432373fc8a188646e7f910310c8dcff38362191b9fe430c432374fcaed88646017bdc554c8e937791ec2a9d1eef23d855200bdee2a8646edf9d4551c8f83f3a8a2191bb76f515532374bdee2a8e4741b9c8f6150e83f391ec2a1d06f723d8543a0dde47b0a873fbbc8f6150802f7b8a8191f0fe7415472375fce82a0e47bff9d0510c8dd2
  | 7 => 0x63508037690ec6a1006ed20d8d4200dbac7b1a84ebb750f6350ad36e996c6a1006bd54d8d4200d7a81b1a85693fdcd4648ed376296c6a15a6ec42d8d4275d7e81b1a8569bbc87635080377a96c6a13aeef62d8d42b4dbe65b1a840d3f15f6350802fbb9a8c88004ff735191000faa63b1a8201bd443635040366996c6a0807cd32d8d4138dda65b1a8201e750f63504036eb1ec6a0b66dd43d8d4100dba65b1a8367b74c763506ce7fb9a8c89d9edf31d8d4138dbe65b1a820d3f15f635040378886c6a0007f110d8d4000fb261b1a8001be44363502cb7a886c6a0146ed32d8d4000f3a87b1a8001b758f63501836ea1ec6a0596dd30d8d4000d7aa9b1a81653fdcd464c2cb7d086c6a0034fc57d8d401cf66868828039fcd0d105006ff9a1a2098147bb43501301cf7686a022071edd0d4144c6ff3a1a46880e7d743441431cf6e86882a839edd0d4644073dba1a8288596f7634414355f5e8691a8a71ebd0d32504a3d7a1a64a002f9f635514305f3ee6a1a820be7dcd43501579fa1a8aa99ef3f43515512de7e86a2aa07bafd0d56504b75fa1aaca02adbc47d8d451cd7e86a3221676f11f63506cade23ec6a0594fc47d8d400bfae8630a8767bdd8c6150e635fa1ec0aa44ebf43d8141a5d7e87b0aa93bf5d0f6150e837ba1ec2a1ac6bf43d854000dde87b12a00b3f11f63548167e23ec6a882cfc47d8d5000beee6b1220013f8dd26440037aa8ec689006f510d8d1200d9a65b1a2401f3dcd6148c0376a16c68917eed32d8d1200f9a65b1a2401b74db63449af6e996c6893a6dd31d8d12749fee68b246e9bb08763449d36f98ec68935edf32d8d1274ddec5b1a245fb7cdb634481a7e2bec68902cfc47d8d1200df2a11b240e7bd4423648003669946c90007cf735812300ddaa51b24001bb50a364807f769946c90007cd328d92000dba6d1b240bfb74ca36481cf6e9846c9039cff734192373dd8411b240bfb7cca36481cf77b146c90034fc578d920059f88f1b24001f844140c8c6ff09822191e07f32344140bdfe6468826059fa4c150c8ca3f4982819195feb235412000fd2808864637fa4c110c8caff4832a1919e7e5315472338fca62a0e4677f9c8d514846be29b22191807e510553231bfcaa68864635f9c8d0154803f2aba2191807e5514432373fca20a864635f955910c8dcf7283647880dfe543443231afce468828401f951d10c8c03f2a0a2191b9fe510503231afca8c88647bff915110c8c6bf29b221918dfe537443231bfca6288646e7f94c110c8c6bf3ab221918d7e746443231bfc8a68864637f910d10c8c6bf391ac4880d7e723485101afae4680a46e7bdd8d0148c6bf2bb22191f07e45744323dffc88e8864635f9dd910c8c6ff21ba21919dfe516547231afca2c88646a9f34d954c8d43e791aac9181fcf635492
  | 8 => 0x7178991000fcea5b122001bbd4a2644076fa2bec488034fc57899101cbe88fb12200b3f11e264406efa1bec488024fc37899102bfce2e312a04dfcc49404408bf989260881ffe7125452302fcec4a8a42a7dd885455453fbb10aa2a9956f7125591002be82fb12a27ff9885324400bf3b924288335f41789910d4f9c42a9a4791f38850348cff77b12c689334fc178991047dee25b0aa497bdc4b6150d0f7b896c2a11ffe712859233fdee250b2467fbbc4a1648c7b7b896c290006ee21d8950029f82fb128a053f05f6254c0a7e0bec4a8006ec17d8950029f82fb1286053f05f625000a7e0bec4819f7eb025412301fd6c4a8240a5de881455413bbd102a0a9a377a205415201bf00fb12a025fac1c62540fbf3812029180df407d8910d3f9c40a9a467df38810348cfb77b126c9000cfc078991000dee05b0a8601bb883625140377106c4a9806ee20d8951aefd441b12a15dbb88362540067e03ec4a280cfc07d8953019f80fb12a2033f01f6250c067e03ec4a080cfc07d8913009fc2fb128a013f85f6250c037b13ec2a1804fe17d89403ddee8ca8a42397dd1d2144016f713ec2a1205ef4744923ab9fc2fb1282013f85f6240c06fb0bc4c881f5ee7044923019fc2f13220013fdcd46548027fb9aaca0804ff735594000dea21b1a8aabbb4cb6351403cea1ec6a28075d53d8d4500dba6fb1a8b6bb754f63516e76ea1ec6a2806bd40d8d4500cfaa3b1a8a019f54363515567fb9a8ca9dae7f51d8d45009fee6ab224013fdcd56480037a886c6a9007cf735592300f9a65b1aa401b34cb635492376996c6a9006ed20d8d5200dba6fb1aa4edb754f6354ae36e996c6a90067d50d8d52b89fee6ab24771bb14b63549db77a96c6a95c6df32d8d5200beee6ab220013fdcd5644003ea98ec6a8806f510d8d513cdda65b1aa201d754f63544036e9bec6a8b6edd53d8d51b7dba63b1aa2019f55363546de7fb9aac89dbedf31d8d5100fb261b1aa16dbd44363540b376996c6a80075d53d8d5000dba6fb1aa0c3b754f63542db6e986c6a80067d54d8d50b69fee6ab20601bb18b63542dbbc286c6a8006ef62d8d50c2fe6a68828037fcd4d104c0b3bda9aa09810f7b53541203ceeea6a8a2663ddd4d514846ff3a9a46880efd753405531deeea6882a83bddd4d5644077bba9aa2885b6f7634055355edea691a8a79dbd4d23544b3b7a9a46a80375f635155306ebec6a8aa60dd7d8d5054d579fa9aa8a1a2f3f535514229e7ea6aa280739fd4d56504a73fa9aaca02ad7c57d8d451dcfea6ab2216f5f15f63546dabe2bec6a85b4fc57d8d5007edea6312a1299fd4f60552873fa9ec2aa2ce7f53d8550a0deea7b0a86bbdbd4f625417777a9ec4a8004ff7351921009fee6a324001bd443635080366996c6a1007cf735192300f9a65b1a8489bb4cb
  | 9 => 0x1bb45f62540037630ec4a82eeec51d895000dd883b12a001bb0c76254003778bec4a815eec21d8950aedda0fb12a15dda14362542bbf4286c4a85777850d8950aeed8a1b12a15dbb14362542bb76206c4a8576ec30d8950aedd841b12a15dbb043625430bf9a9220a05fff3524413025ef6a4a826057ded495048077f3a9202a966fe75244142c7fcea480a475dbdd890154907e7a92a691e57cf5240d2345f5ea4aa2859debd49425001bb7b12a0a922eef625195241ddec4b1aa401bbd494648d17b7a92a0a120f6f5254123aeaf8afb12a15d3f15f62540afb7ab8c4a8006f752d8543aeedea5b12a15dbbd4b62540027fb928c89804ff725193000dea21b128601bb58b6250ea376a16c4a1d66ed32d894300dba61b128601af5536250c035ea06c4a1a64ff7251923acf3887b128601bd1876250c037bb0ec4a1834fc57d894300beee4a3220013fdc946440037a886c4a0806ed62d894168dda85b128201bb4cb62506af7690ec4a0d5cff7251921069f8afb128201fc44362502ab7a886c4a0007ad42d894000ddac5b1280b9bb50b625000376996c4a0556ed20d894000d7aa9b1281553fdc9464809f76296c4a0006ef52d8940069f8afb128057ebd1c6254073d9a1220a00e7f34244140befe6848826049eed09404c073dda1280880e7e74244142c6fce8480a4639edd0910552ab7bb1220a16afcf4254d23c9f9e8481a460bebd895450817d7b9284a0206ef6258d4240f5e84a2a4681ebd094048d479fa128aa99ef3f42515512de7e84a2aa05bafd095650152de23ec4a2d55bc47d8940aa9f88fb12813bbdd0b6150c0377a16c4a802cfc47d8953059f88fb12a20b3f11f62540037623ec4a8005f77258d10009fee49b22001bd5476244c037a886c489806ed62d891367dda65b12274fbb4876244e9e7fb922c91834fc57d8913059f88fb122601fc4436240c037ca86c481d36f510d890300f9a65b120601bb58b6240d6f76996c481d36ed20d890300dbaa7b12074d3fdc90648c8f76296c481806ef52d8903069f8afb12060b3f11f6240cafe7398c4a80dfd22344130c1fe4468828037fc88d104c0b3ed11aa098147da23501301bfb4469822037f988d0148c6feb11a02a9d36f7624052304f9ec4a9a4609f3d890348d57af9928aa99e75f32545532cebe64a82a659b788d5640d42ee1bec4a9d35dc37d8903a69f86fb120741bd88f6150c0377996c4a8024fc37d8945049f86fb12a2093f0df6254003761bec4a8024fc37d8941049f86fb128001fc5036244003f8986c488006f556d891000deaa31322001f94cb6244003f293ec488007e5218991066fca41b1220ccfd442264406bf2296c4880d6f767d891066dea2f1322001bb4ca2644003769344c882d6ed218991066dda4113220cd3fdc9264406b762944c882d6f
  | 10 => 0xc8869fcc4048d533ef988091a067deb10132500067f83c8c981f5ec7058523019f80e8b2467df21c12340cfbf4302c0919f7e860409233efb0c081a467dbe0190648cfbf2302209180ef40640523d3f98e091aa67df31c12340cfb76302c0919f5ef67d812301dd8c08124603b71810348c067fb3c0c91997f0074c51032df00c83226037d01d31440067fb3c0c8980cff07d8d12049fe6fb02a2093fcdf60548067f83ec6a880cff07d8d52019fe0fb1a8a7df90c11048cfaf79bec09180cff078d9102efe00e90a205dbe1816048406fa03a42881f5ec7044923019fecfb0242073fc9e0644c067f83ec48981cff27d8141019fe0fb1282073fc9f6050c067f83ec4a181cff27d8151019fe0fb12a2073fc9f6054c067f83ec4a981cff27d8154019fe0fb128a7df90090148c06fb83ec48869fcc2054d233ef984081a467dbb0090648cfaf793c0c9180cff27819233fbde2fb0246053fc5e0648cfaf783ec29180cff0785923029fe2fb0284033fc1f615080a7f8bec0a180cff07d8543029fe2fb02a4033fc1f615480a7f8bec0a980cff07d8553029fe2fb02a8033fc1f61550fbf408264881f7e4104c910d3f982091aa67df30412340c067f8bc0c89804ff7251953009fee4ab28201bbdc95650002f7b92c0aa005ef7251950009dee4ab280017bdc956500027fb92aca0006f510d894500f5a85b128a01bb49f62516b776a96c4a2d8eed42d894500dda65b128a01af50362514033ea86c4a2aa67d57d8945549fee4a32a4a99fd5f625155376106c4a2804ff725591300ddee4ab206017bdc96054c02f7b92c6a8004ef725590300bdee4ab206013fdc95640c037a886c4a9807cd32d895300dda4fb12a753bb54b6254c0376a16c4a9d86ed32d895300dba61b12a6019f5436254d427fb92ac91a86ec20d895300fcee4ab2200179dc95644002fbb92ac88006ef725591000bdee4b02a2017bdc9615400277b92ac88004ff725591000bdee4ab22001f948762544037a886c4a8806ed27d895169ddaa5b12a201bb50b625440376996c4a8d7eed21d8951af9fee4ab22477bb0836254403f4986c4a8007e920d8950aefca21b12a15db944362542bb7a886c4a80076d54d895000edaa7b12a001db54b625400376b26c4a82eeed54d895000ddac7b12a0bbbb54f62540037693ec4a82eeed52d895000ddac3b12a0bbbb54762542b9f6a86c4a8576ed57d8950ae9dece312a001bb50f625400376a16c4a8006ed41d8950aedda81b12a001bb51f625400376326c4a82eeec54d895000dda65b12a001bb4c762542bb76986c4a8006ed37d895000dd8c7b12a0bbbb14f62540037621ec4a8006ed21d8950aedda41b12a15d3fdc956480af76316c4a815eec52d895000dde8fb12a057bb10b6254003779bec4a815eec32d8950aedda21b12a0
  | 11 => 0xfb0a86013f41f6150c027bbb28788006f77650f10009fa0fb0a853d3f41f6150002f683ec291804fd07859239b9fa0fb0a61333f41f61480027e83ec4a2804fd07d8953009fa0fb12a35d3f41f62540027e83ec4a1804fd07d8941aa9fa0fb1280013f41f6244e9a7e83ec481b35f507d8910669fa0f132200d3fd5f60484167fa3ec090804fd07d8d45009fa0fb1aa4013f41f63546da7e83ec6a8004fd07d8d42009fa0fb1a83653f41f63500027e83ec68939cfd078d9206abea0fb1a20d53f41e364401a7fabc0c8982cff478191341bdeafb02460d3fd5e0648d02f7a3ec09182cff4781923009fa0f232a6013f41e46548027e83c8ca8dd4fd079195000bda0f23246013f41e4648c027e83c8c89becfd0791930009fa0f23242ef3f41e46481bafa83c8c88374fd0791910069feafb02820d3fd5f605081a7fabec0a1804fd0795943009fa0f2b284013f41e565060e7e83caca0005ed0795923009fa0f2b246013f41e5644dfe7e83cac81804fd0795912799fa0f2b240df7d41e56441be7e83cac8800cfc7051953019f8e0a32a4033f1c1565054bdc382a8a029778705155001af0e0a2aa0a5be18160550077a30220aa1f6ec6048d4501b78e0aa280035f1c145540067fb3ec0aa1f5ec7055923019f8e0ab246033f1c15644d3bec382a681a7778605415301cf0c0a82a69dbe1816054c077a30202a9e9fcc6048d5301bb8e0a9a06039f1815054c067fb3ec0a980cfc705591246fe0c080aa403bc181015491bf4382a49023778605415201cf0c0a82a48dbe1816054806fc382a48800ef460405523ebd8e0a9246037b1c152480073e302a0a900cff67d81523afe0e0a8a2075be1816054406fa382a2881f6ec6048d51019fecfb02a2033fc1e56448067f83cac899f5ef0795923019fe0f2b246033fc1e56504067f83caca100cff07959433eed0a091aa07dfa141235414bbc2828ca8277785058d5046ef0a0b12a075de141615412bbc282a0a1a1778505414236ef0a0a82827dde1415048ccbbc282a08997778505412112ed0a0312a025fa14062540fbf2282209180df70795910d3f98a091aa67df31412340cfbb628246a800cff079591012ed8a0312a07d7b1c14648c067e3828c9180cfc70519134afb0e0a1a0695ee1c1435012b7c302c0a180ef4604414301bb8e0a1a06036f1c143500067fb3ec0a1806f46018543019f8e0a324285fa1c1424810bdc38284a0216f8605814201de8c0882847d7b1c14248c06f6382849000dbc7050940019fecfb02846dfc1c141440db7c302c0a080df470505103edd8c099282033fd9f60504067f83c8c9080cff07919133ebde0f23246033fc1e4648c167fa3ec0a882cff47d8152059fe8fb02a6033fc1e46544067f83c8ca900cff07919533efd080992807df91011048c06fb83c8
  | 12 => 0xefa38a8ca9814f471519534bbe8e2ab286053f1c54654c0a7e38a8ca9014fc715594053ee8e2a2aa2a7bd185615500afa38aa8881feec6148d4502af8e2a2aa2053fd9f61550fef638aac91814fc7155923029f8e2ab2069fdd1855154d3f7a30ac2a9815f47154d10d4f98c291aa6059f1855154c0a7fb3ec2a9814fc715592047de8c2b0aa4057d1c552440fef638aa491814ff67d85522ade8c2b0aa07fbb185235403a7fb3ec2a8014ff1795920029fe2f2b2067f7bc5e5648c0a7f8bcac91814ff1795940029fe2f2b284053fc5e5650cfff228a46a8956f451559103ffc8a2992201d7dc5e5644353e628a46a9e47cc5148d033fed8a291aa21d3fc5e56440fef238a8c91807e47151923029e8e2a324601bd1c54648d2efa38ac4a1a1df47158d423fbe8e2a32467f7b1c54648c0a7e38a8c91814f4715193000de8e2a3260977d1c56050c9afa38ac6a0115f47151930029f8e2a32601bf94c86150d2ff2938c2a1a5fd47150d134bfaa6e30a8601f54c06150d4f5a30aa8a1807b554185434bf68e2a1a8297ed51c6150c03daa00c2a1806f5561854347be8e2a1aa4057d1c543544ab7a30aa0a1814f767d854300deac430a8697bd1856150c037ab00c2a1a5f7557185434bbeecfb0a8601bd1586150c0afa38a86890f5f47150d2000de8c430a86057d1c5434400aee38a8689a9ebc615514302b78e2a1a82053fd9f6150c0a7e38a8c9021fe4715091202de8c2a8a8487bd185615080afa38a84881fdec715092302bd8e2a1224a7af185545080a7fb3ec2a1016f4615454026de8c2b0a807fbb185325014f5e30aa8a0064ff67d8540029fe2f23240053fc5e464c0fef78bc8c91814ff1791923059fe8fb0aa00b3fd1f61548167fa3ec2a9955f71791950029ee2f232a0053fc5e465400a7f8bc8ca9014ff17919533ffc88291aa27ff9105325054f9a20a8aa8a9fb4415855453f6882a32a2a7dd105455453fba20aa2a9a9ef441559412ade882ab220057dc5e465449b7a20a8c881ffe4414c91053f6882aa220197dc5e4644353e620a46a9e47cc4148d03dbf588291a8a7feb10532507779e20a8aa9a9f3c4151551dae7882a2aa0a7af105565054edfa3ec2aa064ff17919133fbd8e2b0246053f1c50648cfff230ac2919ffe461449233fde82c8b2467ff91c5324400afa38a64886a7cc7148d53c8f98e291a067fbb1856148cfef7b3ec291816ec6144923029fecf0b24645bd185614c323e630a4681854ff67d85301ede8c2b0a407f7b1c50248c267fb3ec290014ff17d8903039fe4fb0aa0053fc5f625400e7f93ec2a9814ff17d8953029fe2fb128a7ff90853244353e610aa691e47cc2140d233fdd8248b2467f7bc9e1648c267f8bc4c88004fd07d8554009fa0fb0aa6013f41f6154a8a7e83ec2a8004f507d854300bea
  | 13 => 0x52009fa8fb1aa2013f51f63541567ea3ec6a2804fd47d8d12009fa8f1b240073f51f63508027ea3c6c88014fd47d8d41019fa8fb1a80013f51e5648c027ea3cac89804fd4795903049fa8f2b286013f51e56448027ea3cac9001cfd4795942009fa8f2b220053f51e56504067ea3caca002cfc4755923059f88eab2260b3f11d5640d479e3228aa9a8ebc465195305cf8c8a2aa6333fd9e4654c167e23aac8902cfc475592049d788ca32a4313fd9e46548167e23aac881ef3c64515513dd788ca32a20b9f191455445e7fb3c8ca896f3c64515502dd788ca32a00b9f191455405a7fb3c8ca802cff4795910059fe8f2b2400b3fd1e56448167fa3cac8182cff4795913059fe8f2b2462d3fd1e56500027ebb26488194fd378d910069f8ae9b2200b2f11d36440167e23a6c88006bc474d91024b788eb0a60013f1d9544c0027e3b28481804fc765053024d788ca3260293fd9e464c0ba7e83ec090834fc5749910059f88e93220013f1d954484027e3b28689004fc765012105d788caa24261af11946484427fb3c8c90804fc764c12121af8ae9b240013f1d954480027e3b2a690004fc765452006cf8acaa240439f159564801b3e2b2a290094ff6795920009f8eca1a40013f1d941480835e2328c9007cff6791920009f8ec98a40a1f31c95348c0eee392a69195fcd731895050f98a4a9a4647f31490348d43e6212a69191fcc4240d2323f98e481a4607771c90348c03e6992a6881f7cd304c9103edda6c88646396f11d36440027e3b2a888004fc7654d10009f8eca922083bb15932440773e2b2ac88074ff6795910009f8eca1a20013f1d9424410376232648802ebc46551101cd788ca3220193fd9e4644003763b26488004fc764c910009fa2fb02a8013f45f6054c027e8bec0a91d4fd17d8151009fa2fb0286013f45f60508da7e8bec0a0805ed17d8123009fa2f03246653f45e0644cba7e8bec090804fd17d8945009fa2fb12a6013f45f62542be7e8bec4a8804fd17d8943009fa2fb1281573f45f62504027e8bec481d3cfd17d8913019fa2f132200d3fd5f61480167fa3ec290004fd17d8d45009fa2fb1aa4013f45f63542de7e8bec6a8804fd17d8d42009fa2fb1a81673f45f63504027e8bc6c903a4fd17d8d12019fa2f1b2200d3fd5f614c0167fa3ec29820def57d8523069feaf0b246817bd1f6148c167fa3c2c91804fd1791953009fa2f232a4013f45e46542ee7e8bc8ca8805ed1791923009fa2f23246013f45e464c1fa7e8bc8c89804fd1791920789fa2f23242033f45e464401a7fabec2a0034ff57d8542069feafb0a86013f45e5650c027e8bcaca1004fd1795940849fa2f2b282017b45e5648c027e8bcac91804fd1795903809fa2f2b226013f45e56481ea7e8bcac8900cfd179591000de8e2a32a6a77d1c5635153
  | 14 => 0x9424480a7633a24919fdec674492302dd8ce8924601f34c953480fbe69020691807ad425512042f5a04a12808ddb4815054802f6b92a890005ed7254d2000bdae4a1a408dbb1d95248006763b2a49000dec765492006dd8aca92408bbb1594248106f62ba049190f6c5654920019d8eca124085bb1d94248006f63b2849002eec465092040bd88e8124641eb11942480067633a04919f5ec674092301dd8ce812467d3b49e0648cfaf693c0c919fced27859233fbda4f0b246093b49e4648c12f693c8c91804ed279594300bda4f2b2860b3b49e5650816f693caca1024ed279592304bda4f2b24601b74d95348003aea9a8a918075d535452300ebaa6a824601775cd5048d436e3b2a69181cdc7654d2303bb8eca9a460d971595348c1b6e2b2a691a0f5c5654d2300dba6ca1a2001e750d4544d2fce89a86a08079d4350113029b8eca1a2697b71d94344c0aee3b2868982e9c4650d1305db88ca1a2669e71194344c03cea1a8a818079d43505304af3a06a1a8001d754d4540c03aea9aa2982775d305415300bbae6a2a0601775cd5240c02eeb9a8481a76dc7654d03019b8eca9a0603771d95340c1b6e2b2a68192f5c5654d03019b8eca1a0695b71d94340c06ee3b2868182e9c4650d0305db88ca1a0649e71194340c066e33a06919f5dc6740d2301db8ce81a4601cf5515050c039eaa2a2a10073d545414200e7aa8a9a8001cf551515014b9ea028aa80067d565151300cfaaca2a06015f5d54154c02bebaa80a9aae7c765155304af8eca2aa6091f1d94554c033eab2a8880067d5654d1000afaeaa1aa2a79f1d9455440abe3b28aa88147c76515514faf8cea8aa6059f19d5154c0a3e33aa2a98057d7550d5000cfaaca8284019f5595048d4b3e3b28aa800d7c7651550018f8eca2aa09d5f19d5054c073e33aa0a980c7c675415346af8cea82a4039f19d50548063e33aa0a92a57d57d8945548faafb128a013f5d9544c0027ebb2a890804fd7655120009faecaa220a73f55e565054a7eabcaca0004fd7650523009faeca0246993f51e4648c027ebb2868825cfd47919134a9fa8f23260013f1d95050c027ebb2848821cfd4791921429fa8f23240013f1d951508027e3b2a0a11b4fd4791910009f8eca9282013f1d950504027e3b2a6a0004fc7654940009f8eca8a80013f51f6054c027ea3ec0a9004fd47d8151529fa8fb02a8013f51e0648c027ea3c0c89a54fd47d8143009fa8fb0242853f51f60508da7ea3ec0a0804fd47d8553009fa8fb0aa4013f51f615414e7ea3ec2aa004fd4785923009fa8fb0a60973f51f6150c027ea3ec29021cfd47d8542019fa8fb0a80013f51f6254c027ea3ec4a8804fd47d8950549fa8fb128a013f51f6244c027ea3ec481a64fd47d8943009fa8f13220053f51f62504067ea3ec4a0004fd47d8d
  | 15 => 0xd54358d1000faa62a1a209df54415340d2bea88286819f7d50340523c7fc8ae882478df911d1048c03f233a20918074d325155300e9a64a8aa601d34c95054c036691aac81807cd235195341f9aa691a8a83f348d6254c03e691ac2a9807cd235815341f9aa4a9a4683f354d2354403e691ac6a820fcd5348d5000f9aa6a324601f348d4254c03e691a82a9807cd2350153d5f98c891aa7abf31512354c03e6a9ac291807cd535812300b9ae6312a083f319d2354c0f6633a46a9a0f4c5748d5341f98ae91aa7abf311d2354c03e691a8a81807cd305592300f9a46ab20601f348d5240c03e691aa2981f7cd3048d5000f9a60a324601f34c9464c003e69928481807cd32505303ef9a609928193f31512340c03e6982c2919f7cd2358903caf98ae91a0793f311d2340c03e6992c298657cc5648d03c9f988c91a067db31d92340cfbe63b24681806ed465852300ddac4a122601bb5596048c0376b12a481806ed465812300ddac4a120601eb5514648d57d691aa8a1807ad425152338f5a46a1a8201eb48d5450003d6a3a64a0147ad2350d4000f5a84a0246abdb4c94554c03b69928aa89e76d325455300eda64a2aa001db55d23540b3b6992a0a98076d525412300bdaaea3246abbb48d4654c02f6b928a91806ed325594100dda64ab280abbb4d954c8c02f6abac291805ed575812348bdaaf2b24679bb48d5644cb37691aac81805ed725452300bdae4a824601bb55932440ff769b2a3919f6ed365432300bdaafb0246017b55f6148c02f6abc8c91805ed475852300bda8eb0246897b51e4648d06f62ba8c919c6ed325191328dda64a3260017b5c94148c02f6b928091a0dec575092300dda8c992207fbb4d941c8d07762b264a09f6ed365032341dd8ac99280017b51f6048c02f6a3ec291a0def579192300bda8f2b246817b1d15648d02f63a2a491a06ec6448d5140dd8c891aa0817bd1e5648d03d62a246a2a076c5448d4500ddaec992207f7b45f6148d06f62bac291a05ec47585233ebda0fb0246837b15d6048d06b62bac0918076c575812340bd88eb024601bb19d2351402f6b98c4a8246ec7654923049d8eca9246097b1d95248c037633a46a8805ec6748d50009d8ce91aa001bb19d2354107362b2ac918366c565492341dd8acab2460dbb1595248c03762b28c91a2eec565092341ed8ae91a8a83db1595648d07b62b2a49189def6795923049d8eca124689bb1d94248c12f63b28491806ec674c94100dd8ce9928081bb1194648c17762328491a07ac465192340f588ca1246237bd9e4648c6f769b26488006ed265091000bdae480a4601f348d5344803e691a0689007ad425151200f5a84a0242017b5c94344917762b2848920dec5744923029d8eca122487bb1d9424480af63b2848902eec465091240bd88e8924661eb11
  | 16 => 0x4000014181450606014088c289c4c040408040464201400400004086c040000b000200404182c00105c204c001c08083800011c0024040820000c008400003078941c440008a02008642000a404080000001014240c740400106404044000003044484c04000850081c1c0c4c8ca4081000080800040000003420540004504c04000420002018047c2804040804082098a40c142438081c000c3004204800442c00002008a0640c08540000104c0438043814a420084c74009c1c040018840060000004240c040800bc002c30301038003828bc700c288c041c100c000004000008d800700c240008001c0c4000000c0c002020041824542010048c180428082c0000100808080000041c3c002c140004040c304c1848a00038001c0004381828a84c18000c1818040c0400103c04000c000064140c142020040c001c1440140014f8540014140c340000280060283028001830000c30100c0838241c0c70400024100400042478101c00300018082008404c0408300020000010000804003c20042830185068043408040414380018181c00544408301c2c240044040000001008a8800460080c300814000400200c70480414286000500420241c001c04640040182cac3c0c5424040410040428040008001c1800200408002c144800280c1008201004480c08081404082000104c0024000428000000101c001c4040143c640c1008040000003040080000000000344c041448002c0400a80814140008102c5434940048201018140000340420181438001c00041404101448000c0854703c140808900c0020140008003c00601800002c900000000004041c000898100010000c504c0800143404241004040c00001c10000018206c20182c0438042c04208c041c0800000c0000000004100404384408403404103c0000240818143c00100018384c00144c18301804080028080c040400000028081400180810001400200018180018000400343010000000200004245c0000002c0800101c3c1800041c1c040018044c000c400804001008780c00002c0000280844000000381cbc400c040808080008002c3c2814080c08041408083810281c0c0c04040800000814741000102003e08824681807c9235413000f9246a026001d64c15054c03ec982a0a1807d93054d4024fb280a1a0601f24c13244003ec982a688007d93050d1000fb2609922001f94855150803ca89a86a0807d51350d5134faa82a1a2601f148d0154cfbe28824681807e51048d453edca6c8864601f94414648c6ff291a20a1807e5424052300fca46a322001f950532440fbf288264a0637e4544412300fcace8824637f948d63440fbf29822091807e5425891000fcae480a4601f94854244003f290a6488237e5105492042fca20a12407df94090148c03eaa9a0291807
  | 17 => 0x400480808080000080008402c345038b0040004502014003c140064481050740008ac04009c141ca4100c00100000000000a42c00044c20643010f0343ca80400803194a82404d0502010089c000818601804a034541000bc54816c4014000015ec04008c481c0154000cd400441000180014240800340000a8001c0450001c582030ac58109008381464050005ac283008250800088c0c5c08f8d02c287c04003c2128201c28180410001c5c040864481830049c0c14500d2000b02804040808080424002158103c806c145434101c04249408980410d40804080810000c38e8102405e428344c00003084406000c40008200000641c004c00108c38083024000458041528901c0010a80c78180010e49950c01c000c000c00a08d0410141c008420482408380468001c403c0144ec002c6e183c0800499c14004858706800101c000038a820500c0800109450280805f96c140044288cf400141c0004482c043410140c1070005468940000011c00241800f41010001c54c800195d38400034080cf4081030003408082840c4100c00300c000458cc7004101c20540e8530048db424000044044084040014a81c08e8b089000c009400040014041c34005418001080101c0400008028481014a800005414e4184404047074740004040018a0d80c0d202c80046800300c0418046404000004003c00681c1000200004b84050405c503c0c0814281884281410101004100c4c406420344c31142c2050000548140c2800008910381c340c2c0c04000cd40c0814183008040c241c2c0028650c2428083824041c841010741400104c0c107c086810000c00c0002018081404ac180c8468100444001c144414245400141c100c54880800640c00300c0840483000906c242000140c3cf4004400500000000400080de0700890780c080c041000541c0408484458180c001d045c280ccc00600405140c0c192de01c0c1c1c0010f80c0414806c241028180c000034040000007008241410302c18280c2404182c30348c080c18000c040c30689c100454080030040400e80060080c00ac380039f00004048409440c64084454ac3010600000100400408410045c0028343058180008089c442414002400804cf8001c0c400010182814041c582488145808240c00145c30006028001808105800682c003094000c586800384e0c0808200c007c002c2c2000000c040000000804000c08000c1c080c1c1410701c082011e01004046c3c00741c4d345008143884140800604814a83c346820040030641c0008005014040454009c3c181400402034d408140c0c0810b828240c2824081818088830a84c046c00000c3c780c2c0404107c281804002c040004002008001c000014241820a8000400580000000034040c0430001c880000003000284008045010d
  | 18 => 0x283e5c96d09b5bb15cc1ce000a77aea21528737e303a9858000000210696e6d10001946a4edb80002b35e310b967d8fc00e651f6bc8b5255ad93a0ac2c9dae0d54109ca976c8695e580b4e5e6e56da877155698d1061b694068157d7833198653a0eed7f202302d99992c8ece40701603250cd236462bd29980bd3770c6bc50f1ff817203c0508b293eb4b9ab27214e83bb52186e358fab0608c4d42b231da40d4257e24784fa2000142b13922091e2f92c9515465a37612bd43f420741cc100012b63860ae4976a1270140616d15c30005251050bb9477b04680e6d03f580003709fa079c368af2b390004a71b98fb40000000e823b28580000dd600036f00000001c20003b0ac240000bdcb967b13222809aa800000094108852592bb6a0870cbc122564a3d725e2140363c9c15091f876fc864aa15e91621c46856d406b981b0ed51072eb23f182681f9e137f9836c5c0004c44000b4fad713261e25fe000299c0012c587ab054f4091a00030bdbb6a7f992afba468000ab0a5a9fd55f524e9d41ab86a45d3b0e206e000000459800051d50208459cc38c154159d4d06290a34e68000749a368dc876c2ee01fa5d44ea1741493ae00005a90000001730a4565f3a15d2e00096f46da42c690479ccdd326a1da47b80c7c05406ee1df094907f994bbedfb4668ac144c8208c6a85bb6a9fc46cc1871646548d74783d6b190d16b0005306268392a6f92e00008de46a412d7f6d2b00011819ed33a546b8fc1e2ccd21822e91769b612db0982e2bc58661a1514ae9d2cd9460b6737153c43d9e5a32a38715791483260c419149f47d6633259c70a5b115f93bdce0b2c7aecbfcd3b2b08218769eac4ae94d449456098e2a2d4b880c9a713ecf88d915370a5ba7ca2e4d86563be58f60006c918e8436fd0791a3d4fb4a18392a9f6762dba9633870000f5e0030000c7e4ec7c5172c2d65ff2350db400130d814c07d9095803059830000000793d4e4930d3d20fa5187e8000a382a1800052e5e24e8a5c800030151862de000831238dc2d56b961456585b485a1cae76360000ab480007223931e3d12198c4167de96856932df85e168114055d74a8ba40010168058001c9c00045bb36df7829000054e91c40ce6e9441295e000398c0e5a8a4bd00003e800098c17dcc3c000fe5615d7d29a911f2c798040b95ba861d42000083993a41a4000157ae38000000adc4bcb0c812ace9a5f1fb15c659850a20486849a26cd470e0cf38e2092af962016f2b5541846f4e5063c5a492ed87a27527d65525c4d81e8a9900001594049dc000055c25ed79b20a1041e7407d42798f00005fa000118000aabcc348cb999a69d476607824de72e88000187da9a000000158c1864100058692c0400001c241c004c54381030042c28704804848c504c0154086c1800740408091
  | 19 => 0x1f60e90000000000000343bd0000000044d800084e000000000083a089ac3b7c0104f7745c2ba8c4a4ea00006d85bc62200006c927a5f69af8002382d7d88e3a100000005c2275881000033539b4ce2ad81869f1a3d2e772060001d791ec8559129dcd1de0000000b685c67ebb2025565b900054608cb60ca0db8c659277400049580008a710a0000dd00005aec7ec0000000e536daaad0cb00018d1decd03633c77165ed4f0003d9abf2fa67feacc93ee0000004ba9ec2f1b6bd00029314ec1ea026000062332900000002e1138302cc54000350827d320000622c1e8000d1f48108f8000f8c000141cc40bd907e2df51b95dc1cc2a62a6a78a18b16c8edd02557611b4608000115297c000566aeb4ae0b8324549ab89c3660003920f759d1433268a574cae0003b1be15b7d4d01661ab98b20009c400011b01e09eeb73c00126e0002c624040008bf2840f2ab2249e21ca1ab310669b480a56f455eabc90e6e07983cc1f9008d557ee8d1813a8c11721fd0afa4756728b06b1274a572800053ecb05d9bdba6d4b9c8a5493113ca0b00d9fd667caa01b051d60d80003598fd672800046fcef07e200000048d40010890002f6c00100e5eece41774ad29a4000099e0000004c000007720000002524000000000000000033a00017a80001fc0cacafc00000038740000003f334380010c6134b70c41cfa06b48001000bef5439cd44c06312bc0778def16502799dd786a440005451c8b0a0467a1b6b0ab532c007e0d7ebe46510acc2033e00003a70090c5b00005e1d860f0949892e0760743311f140387985cd3bd109a809ad54d0cc90c1210cb9f26814575a951761d55a5944227457b2656c492e5e8ee946b2a415bd27734114cca5a01b0326a4cc000aa66a91741a5a0810f09be9a94fad7aa4a409000e40001c08000000aa31ee0000dc800015240001bf51f99c18f89ff0004520000a6b4163b006ec00051ccaf0954d1a8ed458d8468c400031180005e50000001f96000088d48800054d00045c000000073000010160001ebcf702ca5e2000319640e0009250000000000a948001eb03d20001701ea65818040001f04a1a41b2bc2ab679a7edc30887aaf73db409c62e0002e70001a514a00002192b3e0006b3316010f42e1ad8ee1192000084d31000033059800008ec1603990000dd3218a33a85dd5200056cc879be858e4468cfd6f0d0a330000000004c463270c000113aa8181a580ead36680027d0de6182cca8752d7b7babc048c452806cd4b4f4e067304b2a5aec3e8ac6991094a4e75bd8528ccec6365e4c245270f95d246755b51ed0001d54430f3a74056ddcf414e658c304fc120930f0fa800000056400013e158c170560df2d37f132d794e905575874d540002fc7234d640010e713f000108f5166b82e0400000033651340002d19
  | 20 => 0x3da15a9730db157c480e2f51b11135bc548000a9d85e9bf2bdaafda9465eead142142ba0382c80000000000dda17c2ff8214000015800180083d7c790689cb33402a8d3cb2e5c7085b6bceca7a834c384271a92189d38f21da3898aac5f637e0000002e2ca90c3d00042b63e14ea749b48dbd6eb22cfa72cef444ea5440260289ad3a349e0d92e54345837a18acc71ae938121e2bb500aa9cbba3ca9a3d2f6a236070442130b1b3e98c2c065fd20f8378344e68d2a18f92ac97d6ecd782973e4754698204b34b9a5fb815283217008c28301aa228b46527491d130394639d32db7a8300efaab5dd85036808a04ab6c308bccfc65d281e911948987d08c95d3c083fa94b3ca0401526fc5621a76e804acc6c33b494502524db9f3cfce47c724277262a8f2a40a438d3c8b994f0e4044c2e574894445ef25e1b99814008fce9470351dd51301604b74bc74e15f82819d5e220510a8658def088e143c19272277db4a9c02696e870aebd120fd34b127060eacdd79ead96062065867a974c92fb93210900b0afe11e101e9be4c6b0000001920b31a87bbc947d4f1662cd619fe54688333327562468f886001ba24c1a82461a048619a53521c16b3675188e944f1372471a5d19495c86b9a0d0c69b50d2400e73cd580002101ed80009d69f421484e288dd7c2aaad3e00036210d6464a671c4a34b2039541f6d1c2b64a3ca148c1d13f061ce8c5eb034a0b327ddfcffca7804be58e244029d0a96b8000000410a0008dd84500000000000000000000ba30000000001020542d27ab021cc0fc8d50000000875acfc0011ae3ab8002a2a00000016a074e22305c327a004c9101339129f43835fa80b8f5e38f7b00001a1e00060400001fb09e58323e44140006da4ac8f772f50a10d7800024a1ab23fd7e6da1000579d4e72e8575a0ad84ea0508756aca4afc30918514000d423e74c9a05610306d390ca34ff80744a5800000029a296cd604372a21a509f65376ad8562300da226b8001550ede38d4c7e81950c00053819d84240779e4d8e31b27c9cbc13173687a12a0c2a48a86704f2e25b39398e48a13781af04f08053de00085fa4bc6e2f5f6d8096135e88e86a49e47ac779a63890602145c4371cf4cbd42604029d89020089352f30334c8c63fbd9202ae1f73aacfa49c22e82b0d648aa41e0d6d5348af41f5294b854d20001839d722120fb827c702484d304fe3f24000c1d36ece9175d2e2071a6703c50dfa462419a8628e44c80019f01245942a2e3b200057f1fb9b081023c5ae6c6f88e63f9d00ea5634a40b0d620a400018937fcb112d300007e800031f94c00e106eb3d000000031c000838c85c89b0e64a400024020c2781b37ceccde300000004d74e3907352c000ef800000022d4d3a64740d972c832943511447eedc20ca50a6c022c3e48001
  | 21 => 0x19728fd9ddb43034a4221938002706c253489b5501c91478cb77ccb2fb5698858542d18c18320a84163b00000d840015429b5b98a0dea531324cb80acb5000680006f400017f00000014c5a3d800283cd9ba9e801c001301af33eaabeef517a785c1df89d90dca73592f0e85c90475e8346498dcdd40000b46e9800036ab910000ebc0fe74d53bbcda78e0003d93add6473522691401f3307300010e0000f7e00015bd8905f300000021e83a29ae26100000000000000000049313000000040000000002c604d000248c000000360b0a68fb492294a2200012576a60119904ff58b70688d5a7fb1efd5817f0e138798db90b810f0001e7e6e4e202dc0ce88800009aa56cc638ab60003e044dea97a099ffaa343db8c5c7ac4d43f90002c54e78000000149833f46260512debbc00053ab254516ae810138ad04ebbb0004181abefac7c7367a8e45e437ec8cc9114ad319c3ea5730dc495d2d80001877e500000002ea54e2dddb38e53484cb703d245f5ca28d8fa65a637c2a416de3ef84bc2d5138fc078d371d240b7e9c604e94e94050e9451a6e72ed717b98c0006cf6074b8191ef1400000000000b39e2000000146c377a1680012d88d24f28cca00010a8322a143c6657000000077500000018dd5d1000529d64c000249b29e920343443854c7ce0b50001c88000e292ce93900000007b6800185d0ba4a71875a5932d189a8dc0011446ab8c0ab36000906a7e5d026568efca30452ba224b1f88958b091d04e744f42050000c2c0000b219e8001fef1783519d5107f0b36fb1bee7fcfa1aec3995baee6697f0b4c8467c13e9453dc0cdbb33693d03a20001b4a3b18420006c6009e29210ca714af5e68c24038000071c00000034e5d68000a83bfcdb950810000000000135130cce0000000ada11b99383c08d000014814462240198000cbd3e2253196673b00053184e6b572ee00029629e2000313163476f8dc563938e59001080001ca00001b00003fc4ad2f70eee9a4cd70688002a24e6a00036900005620000002250bbc00010d40005699c50000a2528d86990040006b50000000000a7ca05204dcc889600006a80014bc3c90efa1065d4816000000003da29373400000029500000008555588000b7f3f000004e59a20000f191e00010725c704d01ee5368642de94d90011421d09f3af6f158b75873b1bd677d504edb0e543d00c586e5c26323c4920ec5d961cb6c000d5341c4edc00132b33213164c74cdace9ee8001596a079548b5600083b09ee08f47843f966466cdc14c795d6092b336b900024ee87b0004456c155b00003fbe07000000026e6280000a191840ab800071b1f5e0444850e80001cfc31a5f1a7d87725fd48233ada0112f84589b626705f0003f788080004e12e409840000005161a08a0a3474221e4044392e9dfd52269a
  | 22 => 0xe936547923873e0ffd254f914a561883b6b8a67b9171a6c23e00059e000243e10700046e800005468eae025c74ac00001e1463501220b9a40d750d655800000014459dcb3e33cac237539400000004be80028bc54e000278c0015743ea2739250cd2a6558403d8abd5a1c31dc1c54a4748d7d27c479000025a28a00045480002ce3b440cb0e5222000066aea9fb017264c40842521830dd2174f9915116506714b091364b4aba8e81a828caf000961918bd03b0920da39d52b0c2b6c19a18b67cfda1197f31cd270cfec0b4b275902e0d8de0dd6464cbfa6e23a1c944778ea26449eb47a98280022ec08a4f70002b929a18cc4ad023cf673839eba6105095b5cdd1db200044526b0ae943e5c6c4ee23111e1b80000e36a70000208d3fd3b219f4b0400002a12b0cb43570d9866a7cc2acd3c8dd90e5fe95b914b16e88def949fd3e78816ed65dc4b552bf2412f52a01e160006ca48a99c24ff726c37a12c9e1af73fed9ee96d00000000005d837100000002b71fd96502820160000002150000212bdf53cc0000001b7d13ebaba058000b5a55160b906d70c9a50e39a240000000000002adabe80004c4d2e686049907cd22c0007b414bc0000000003ec8e386ac5b68290d0d1225793fe8d5e23926e96de26359e61009b9d749a31311ff2838d461f18efe0ccd8b03b05248a900715a8ff40000000000000000c9978e000138cb0438a904e47e00000033d0fc82135bf88352cc61378eb9ed8a0c616ec8b3c8fecc268c2f385f483b0e4804a72ccd872892249954638fb2a6dae2b0f1b33f51cec38b2190a6820c50e6fdb49645a1bba214a74b581a98cdccf48ce0b663ba6d215e57b5154e54b6a209254522a90c9034222b511da99f000455ab82b2d4a8ca1273f37c1d8b14a4e6059abb02713d2a616a753b59175a0291800000075f737550115a0006c50ef66f08e79c79905a52d3b7898001e86dc5906517e008000579d141c223e600037188e0a7b0000000000d153f49755f8ed8d4382b56abe15c35f24b97c04b064289208e740da9c3365948f723ce4e820a0e5b9f98edcd0494a832469d8da03b00aa6b832f4de2debfacf12bd215c4338250884aca0002b233036ad1fdea6159300046567f2bac38c4b9de4a7707a833d4530c8a1e880001c400072000010391e60580002a469e706c4e60d7423800038ddb4d54e79f8000000eee8d5369d5286723c0a4980007605232d699370230000ff20fa00081e2e5c00042a3c2d5e10671e365a000112ee7150041142908262cd00004bc000011d5248e4495877a8812620006c7805290f06b88847e8e1296000050fc000243177a60a090c02006205c000e3341e3b884688f70002c4de503c4549495425a7bd492d2c25d800032055b1d142331683fd80010e00002ff0001601ae40000000584000000
  | 23 => 0x2df360007d40b249ec00000013a53f6e4b000000110c00000000010e2000116be7cd8b51c00002b9a0f4534a81766642b0b97e27251e12721b522b16034fc000172800155351125615724b191b8311790d108e80000000eeb0ead2d49b757d2052ace1dc000136216c8895a3ae68e8dfc840e79c4badd8e00047f00001331e0000298965334d0b9b5b0a3945a5e53311ee26157434f5829a7ff69fd331bfa288099d42c630d616bf311ce0146a4dd07d8ad75f65a8bd5549a14f02d8a0a18074e3d9aa391a731444021f1113536a1e94b400063622e37110c50133a59f548b60008e72854e3a8148964b3085d07c95553f4e70c553e195500ee678000349c9f20000e5848191b5cc1e295943823874c4cf45c580001f580026b41ae00037b5d98000703c0f641673323f52e800097a9da0001adaa425f0c15400000097d00001772d96d9539c80665ba1d8fa400022431dd00210e8461548000e7e7c200000013b10419f080015340000004c66820d2449b0000d18ac4000536000137924dc8691047a313a023c46501b194893d07ce5aa4d130c8693fc1e64d98080e1e1a0b7aa8ef16d192c69aa692007c4a846398ce34cb9f00b2b3997888cd62153b04a78246298198699103cef06a75efba662f6f92034b024000000786079211b4ab2012d8ab3508f7570001ef428d10d1aede4c19b2edbe8e1d2ddeafd04aa91319f5e3afb573cb69a46a7a86ee3f20000b09eaea6639180000014415b0adc4659513686abe8000eab107b5adbb157f0002cdc49aa5e9f5817897cb473e527e0d412ac2c1300cf5ad8300038892526d72ce1b700000340de0000fe47396d44391beb57946cb0f06caef50fd9284a2c0b7a5940796bd40882999284a0879186276875117233b2b2cd811db058887487c9a9355c8224a357030dba68e8e53f6978289c2439f4bb27d63e80002a382a5cd11d39090fb17e352f58a4536624db100047e63951365eb5415fb875a33e800278d3f50004c6a2866b94461d7555270a3824b2d2d926703f010cec453285ebede234ea13cf1fbc000f0a7efcc9c000d191ef12716d530209fa98c14e1d31c02cd5356c6ca98c41400001912a8fce21c53544d49a10d82c58050000000ad71a7152c6d0e2500047489dc00021e1ca16e8f2c3a9cca074d4b82a7898e22c7cd40dae4e3df2e650db8e930a000a92526ccfe9c05699f858b49e56d980000000009fb94b251418c96b80020bc89105eac6eade0006ea43f80000001a581bc0000008a0aab0ab000057a00013e26cb30d0a447822e700011980db2437e780003460000000e5400000000000027cad9800000000000009b6000000000000025fa366000000000000000017cba0a34637f00041d000044f14e0a8c0000000003338000c181030000000000a1200021ac4712fa44f6b5efb
  | 24 => 0x739a280029807eaa37a48959354a0c929c48b49d30773486104aae0003051bc00bf00033c84b855a29850500009eb18cb3f1fa40000000a9824ea890000ab83b00001551e6cd2b53ea1b82e95d20000000002c1ab994558d46206ef72e99072926c797adc1457b04d06db80e40004dc000000196e0006a83cbd96ac3f5cf800000000000017bda2e0005b60d49a6876b00042d949741d9bb88018f544a78fd7aa7c816a0000001fe40004d8b32539e5e186900a400060a028800145c00048414f0e893622dd9800b3ce52a4180000000007a40000f8e38d0003c3c4d05d10003cf80004e39500a020f6a3c55798e0ffb4b46dfcd5800000036da2f80000006cec60c0009a625598dd6ad43a4753a2d3bced800008f15cc81a0003810a0b3700004a1d22a56d968ab3859b23b3f81212536eb3a3fce1e4e2c539e404ac29819963012ea7a13cf1141eb1cba16e93db93c5d67f631f326a80c87897c31e0646bb5a77288c82160020bb8c12b6e8c59051658e52a99b74711f7154c47892462d07bc4d03ec5faa64f5e1444981a7035b3a8c0e5613e0e28e11fda94510180f277a63d2d395c01e41ee9a0931c03cd09a4e98bd0115e3947804547af333404949494000000215e9ed397a47111512800006f814800115270ab2c8d4a0a582cc4a4304000378a22df440006340938000a2d86c18b000000000000000009712862b76b2f39100013c1332000000000000100f00000000000000001bd516000006dc964000a336ea9d6cd6edec00000007ec00030a00000007a42e426542ba0004eab07c4a2c1e2868000001221a420f4c86734f9dc83fdcae5ed5b90d5d5455ad09bcc91cf05ae638342ec055ec97985f01ec1f18c48286bb400e5ef3ff9efe3b35a6a6ce9167050004cec000000321b6669ad0920005102480ae06c01a64f42fc12bd2f3de784b519117dca28447437ac5d7ef1824a3c3c857c82d49f943c70534ca57554822492d0babd1220503e8f2358a66a80c22ea9b42fb2146f2c1dd4ac628275a77ea3a47a7a723446fa1851e4028e320426ac41e38a26ca82a10f8548e132a410bc14681bd5124f9cd64797a6d540e9c95001aa8002a86a6500000000000000003b3897915b00038502d00dc7bb255a4f90175868d327dcbdcac93f656113c03bd81f42a28cc909d05da454f946141c116c4a341d57ad00b4bb5a500000005cc210000008a1540000000000a6a0000002a78d3557a80000000008aa3dae70a4592c5c4863e63632b609e044e0e05d82fb00001649f5239558e9774d936e685a4429d2b3420743530003d3115e9dd3900d6802f5e0ab540d52d6dc24a9121c6226462c53640dc8cf90fe0b6439e000a440000000000a8100000008a200030300dcde40002125388ab05fa511c07536f4ebd28558c00013f800209924d48bd6
  | 25 => 0x57537714b7d3d595cfa2470c54afcd084c09f635a80009740002005c1091d2c32f9c0000004a980026ec2a762581c80000000df55eda24df8a9002400003a1ab207100008c75ac8000b46000020ba497a129424f80009248f64981160456000365000151ec3657e3cacee200000000026da0a00429e3dc307be000000000092712ec9680006f60bb48aea551004cc3c5cbe316100021da1591c86f7be01acefae3efcd8e1d8b5b0f40c3d5744fd0f5ba802cceaa0d380048989873a782349347f947a14ede420000000001ad00005d900024dae736252b165f35b241aa128f6905475450d9a381a14df29bd6066ee3df9c640007de0004465aff55991e9ad86f6786aa880024a757722b513c22ab1d87e28387363748bb942241e4e1768549a36b389000000000000000004145be00087dceb000045396233790226172e2c96087629b81345b0df8000840395a3227995bca4dcc090c4337017582109fa00aa7411600000016308d600088b8a30bcc6c25f2b8a843c63c4dfbe415791a90002bd843e00000047a139438198ec43d70705b9e94b6a4491113c156c4c574ffaaa00003d478c8bacc5a8c15fea96329647c0000000e1a824983ace3d95c4342178b38d69ea4df17b0b99124e3eaae0b0dbd112e0e6bcd47746699b49ddd5dd25f84c8b1974d0847120328000c7d8c7b0a80000009df0b600007a97e1194c302e9b0002f5e79a000a0c242daa21c600001891aa71000003998fcc221ce453a4c48ce000246600a000506ac9c30d47e52d1b60ac223542c132195b4a943432bc172c5f0002bfc830cbb1fd4856b9c7680001015086dfa5ac00012c2032449be2e4580000002391bba934769b99cd7a1dbab90c506df5e40e01278c60b0769349a4000000000510ce531f50000000000000940c6a00484a032f8a0cbd928312a508da8e48f234ae3dc1e000204cce400068aa6e92fe194f637d2ab0177c5925280000d9d5cf02717780011c900034156560001d629219820224b18c424c06197d9863e9e68038032e85d6c2e300013559e6aef0000002c0c000000365a4611a276dadf01084f10002179dba4f70d64f6cd8800000000021a13d70f39b9e79285028f52703080000f29d607b0fe800056180000000005144000fcc62a10b40000005440000bf80005c400000003315410000000d38208a3411ac2bc51d9fa00000001daca9abe60009db00012714a2a1aa7b47fec160000000001164435336989e0000000654b8800033cd0f000021700048419e20009dd00007a00009ce046930033b7d232e9abd2f2885d3ad29b3ce145220c000bc64c92871de2a7246db7de614f0979d93c8c9868f8ccbbcc000b824fa0ca12a90a3509bf80000616a2b0cd061425959d0ccd88476133d559800114274f214e12ae79b0430100000af08e2932202f
  | 26 => 0xd5d84300013c05b07262904a040000002d8c73c2978d68000cb8000a4b8000640000711b0cc6715b59e99a885fe1968ec000024a0007dd80000013490001da5c4d1a13fd0bb59242e2a3400024625318c536560b509c60315066a08eb893ab9de20ceea7ba286ac63448d598ca75135e5714b2239ec3b47c2954f560eb84c4c5e30e242034075214e3a527c0025aeb2d24cead152e02d77052e242bf1c606b00016a86ff8aba9b80013f2266034a17c986a88002c0a12ca6e89a99fdd1d78fe24049cc4b33960fba8332448be4578a860000f6800138a3c371eaade44c1267be0000ec84820a846683cd22f6c2ad227aa332000290ca98e7f065800024545b5854ffc22d40e00000000009b829cd4a0001044385a254000589000135a060ee31a40f34610fe3650ae31f0e71f85dd12666d1e750407dcb7ce4164403e4000000a2a8000000661a7400000005bc514a28c7934f2ae10000be0aa509e80000003038ca48f03e0a7a84d00000012498da39840007dda53000000000076415d9c0a0000000001d9e0009ec8001f2ac5e3ec39d00005964129f7000143018f00000007438f10002256d1e007bcc865c0003f894e0bae9e8772bba1200e590980e2ab2b3c105e0001dcf246230bca9c3305c7830b39b934117b538d1da91c70005641546a3a2af8c05946000000000000144c1d5b65c001567acc2fea724d5497719f9c022123fc0f6587460f97dbb192d10c98484fd975261200024ee3fc6c60495292c080e120a3e19cd80000000000000a640000ea8f9718e1ee4e099071eaae24bf4e98ebb15110d99c8a49578cd84b5e92493d00424233cc5deaad0d5251b77ec07694747100005dcefc4a2adb2edd994a5c743afd9af0c895d29b4c98d21da32a2f412e53e4d42b92438d8202fb2a8b26e2e628bb28d7036437cabe1f3915a310b91e80810827e0b1d5335cb019acb932d34474b4e0000036c92798e4968bff43f55a2adc0000003954000e179f7a66d09676c3f2c74611ca8c58e0002246be2ae90002a134bf88417d69aa3cb948845c00b1961d70190b554cf253ab85facdac0002f4606475e2b8a4e834cf2e6438000a432994aa922e74360300022c400016200e8f54e2cdcb206bcc2a1caed0220a958935339d39c99d300472b4000168800000009d980e0000005719180f1e9d79860c1a000210c5fc000000000369400153faa38000858b8a69b80027f028f54ac921cd64748c6b8c9de0057ac23d4831306500005652b295e66439080007366715111cb89d42669e416847877b49e0c00101a80651ad9ce4994bc15f27a813611e980e61710c000145661c0d032a1c3423031b1503c00ab205882b8001bdced10004bd80355d71ed412a3962678d61555f30a4f418b2e21c4b3851925f17e4cd416b15c94fc6d4589198e38aea71434
  | 27 => 0x630002aba000ade000000029e00056fe1a30b11a2a1d00006e156810ae7175d44b280012932d49c20b48d6222f4cd4cf1ac07068429ea85332f458c8dfa9a2c690000000da4627a730001b1d21b59087217920000002336a3246895bbfc685e8247470c753e425f15d0d880012be46bc0a1daa1d78ce3efd1870dd96746c6858000ad389c528881800025fc2772af14a4a013985da62235b8e1e6758934fec9180032f4000000027c2142bed272f790004a5d604000067800101ae4900000005b94fb8afd4c9a880a8376818c8bc18d32a97498af438ae50ef10fa3f728838a22b86b4a111d49d8260813b8000220a817d8283d5ac7b78528002662d7c269a08222665824a4620eec36ba61318a4d6751260a2b961802f52a530d1b457787ed6a0e8042f35430d58e95d5396adba60c66f1ccb9bd9b83ed9513ffc1eaeefaabd5cc10754f0004cfdbe616c01034d9a291e51390000aacc0100000005e95a63a281853c8c4d849b8e43e827993081f25171d63f18ce6b140ab48fbe352371f7aa5ceb82ff5c0830ad019ac8cb93300000002ecafc000094d54800003f9c5a1901ae3d2cf6a060000142c0844d9a7f51f15be2ac62007392140007513eadd8af91276c0fce754dbaecaaec0002ad0000a74000de2794bac2afc77d4e41c9da540255aaa0a5834d11397191d3028063ac9c4d47057f0f93c393a29947e8d742122cedb08c2885e45e94081ec624812c6c0d48627282e5b9d5f19fc6962efd6fa2e903375323495f27088b3d199a3648d4f60c25fe15a121d3d667cca2faf41975e1aa0200c3f9c00018b54b2028a493814d556a666126426f25040006e06d6bdc0d38e0036c80007482498f757b44cc6932fd43fd0686359fa3a248f690d9bd3cc4a413b87e43d69b40b95a0d2d828131812fc850d7f24524642e1509d55a2e4a6f5d96d7708db32d3fab5f056bea6ab10b40b6b8ec7c52389ada6792b409b197a164de41b47cd568970f4969a141b9db51626a4d691ba08480551938d0278d04323b800019e0001a4a04800042a53e0000210144ac0143ce387392b3e440a793169e9842ce8d9da895dd1e00033596941284cb3ec800095239a33e379c000f84000121a8e6000886c5c4de6cf00000e2111e00016da621412ee40000001cb05e79cdb7c42fd60f0002f988a234722800011f4c56000289400102f9d300005e219440e83062a113e0004815a6621ca3702f9b22cd542fc4f201a5f8174373908a2cb79bd24444a23659a2ad6af40c51f201c42f28855038001b562f36fe035eb7ad562c1c580f10f74236255e852796150cc8ec1c4f33d80cf0d1104d4b246e4a1446345e5494863599958875814cf7ba821c040000009f680001e91dd72f80005aa00054fac4499c9120000eb6766000a74b590000d6360e0d2596c
  | 28 => 0x3012552295d8d0a1d626076e041613148810001af2a8912a55f9d5a4a8ba087195826403ce78aaa85166075401051cde85eb31700022704feac7992c40e587af94df864847d45fb4580010aa5b80de26c8aca190cf7e868a260003fe5df48e00004cb1c19078262547c0003fe57ead0489200045a111a7534d75520c55dfec287a4b868000a608e6cf6a3aa12e8db8de6966a590d8894d2873e33dc9e1162cf04752ac1400129f5b308ed7d271493b341a9934aa6de58147ca61100009162a75dd2e1be0c2435e26d4cd4665f11d21f989011c00084a43e26963400c9cd9e324bc1650149c36eca65a71411d480ac086868000109d0251cc19f527e98c4811d592857a6b824f231472db3d8891504e93ac1763faaaa15596885693fd5a5905406019dadc49fc52a00016ea95c000b24835026800000026d496c00061c45304e15bd1933c025c94593077c410a4f4b1841cb2501c3611400031d62e653d76225bdb5d5624e90001e4413c098aa280014d37bc0b6963c8b5a8b912e37cccf8c300281a6eb50f7bee89d015e96b19417d4ebf2d23d197faa9e241d364a6680787b8001d932220aa800066f48038f00000010a189a9b98408553620c5619d405aa2a4bbcdac231602a5a56eacfd515ca8e89682f12d55d456c34d4d23ba40001d956d8d9e0d0e5e00fad300000008533f35bc2e9000000024966c31e7d2640003001cb85683eaebe9ef55c400000051ad3d000154537f0000adcd080004c300000000002ed0000000000
  | _ => 0
def g6K5 : Nat → Nat
  | 0 => 0x340f1be8d15104c940bef93454414340efbacd1510519301cf3375405545020f6c11d109594000db3455c06150f27e2951235013000cb74519d1050e132d11c6195943e4e8e544cb6350b7bac95110d8d40dffa25444140c8c02d99616748d1000a76585d90148c029b961764c9100087e585d90148c035354e575852300d711095d6240c0359442575812300c751095d0648c035354e575812300d4d3295d6240c025b5e250959230087d789425648c0353cc2575812300d671095d6048c031dc42574192300d4f7395d6048c03538ca574192300c6e3295d0648c03f0441309592300ed1104c25648c03d1441539592300e4d535825648d0793219539592341e4f6754e5648c02d34e2509592341a6c585825648d069b161209592300ec930d825648c039354f609592300f4553c425648c02d3e0d529592341e4f8654e5648dc753dd5235855300fc1104ca5640c03d4441539590300f49504ca5640fa3b1441329590300e4d3255a5640d9353dd52358153e8e4d504ca5640fa333dd52355903cae4c584ca5640c029b2095695903e7a6f8558c625432b931493295903e8e4f504ca5640fa3b1c41329590300e4e584ca5640fa33321d3295903c1fc253441325006fd4dd51054d037fdd0374425640c6fd1d952340553e8dc4374425648c135321d5395923e89cc3895d6048c033394c6748d5088f477548d53c43a3710df109592300dc653dc54648c033394e27d8d5000d4c3895d6048c13330dd329594100e4d3294e56480021f9612791930bdfc25240d0148fe7cc949015514000e4d3294a5640c03f04c1329591062af18011a5644003ac500469591000ec9304ca5644002b94a0469591000ad53811a5644002ad121369591000b73805465644003b44c236959101cdb047502564406f740dd3095910c8fc2514c1324438fb194532d8d123ef4b7548d504c0fb7201d329590300d4e505cc625418f33d95731895000c6e5019d235434fb294123d8153e2eca504ca3648003d24c2509592300e69609425648c039a482509592300e59309425648cfb7201d309592300ccd37d186254003724c2079592300d4d5381e5648c137281d329590304d5a0754e5640c135395d23d8153e89cc3881e5648c03334de631895000cce8319d2354003338de63d895003d6a0754a5648003334de611895000c775795f6150c035354e179592304d4e5748f6154cfb729c123545301cdb347441525006f749cd015490301d6a275425648003334ca379594200ccd328de56504736cd1d1054d4000ccd328de5644803334ca379592000d4e3895d6048c6b718dd109592354d4e375525648c0f3395d32d8d5287dc637c425648c03744c2379591001dd2374425640c07568dd5095903039ce3881e5648c036c502479591001db24744256500fb729c12351503
  | 1 => 0x404432373ce42744363449ce7921d514432300ce72319d1050dce7921d4144323dfda44751d10c8dd76911d414432300ce517c8e46543873945f239195173ce517c8e46441cf3945e3295910e2ccc874ca36481ce6b21d5450323e69ad48dc554c8dd25b21d54547237396c8755150c8dce3b0a2374991074ce717c8e465439bc9105545472300ce63241f6150c03398cb7650f1073b688055150c8fc7b8c8d01d815200de110dc151c8c03784437050723ebee3234060644fabb8c8d01d8121739e418dc141c8c0339c8f715195300dc723dc54648c0339c8f715192300ce723dc5464c30778dcd1050323c1fa34344140c8c0e3b21957503231aae48655d10c8c0e3b219574432354c6c7655150c8c0e3bde227d8d5003ccc274cb635046e3d61f63919101b8f5878da5644003b44c156d8d1000ed13051b634406fb421930d8d101bed3674c36344002f4e01318d9105e9f08750363440736c11d40d8d101ccb44751b63440172d11d418d9106b9ce3845f6048c02b9a0443d895000ae71818c6254002b9a0463d89506b9ce3845e5648ebabaa0043d89505f9ce3841e5648c077421d30d8d10019f008dcd62440033cc0c674414300cf30345e4654003728c1731895000cea3019d23540033ac0f765432300de230dc956440071e01d50d8d4501cf00744363548071e01d50d8d5201cf0074436344803334ca07d8d4200cf11081f6350403334ca07d8d41f5fc3464412340c176681d43d8d4000ccd238df604840a3da047655130c8fc2814c132441ab3c8dd018191305d961750f63504023ba1c43d8950008ee28dcd5650002798a37355910008ee28dcd5644003724c227d8d5000ce51089f63540035354e27d8d5000ccd3789f63540033354e27d8d5000ccf685cc6254003334c227d8d5000ccd378df62540023bde027d8d5000ccf378df62540035a14227d8d5000ccf3089f635400339c4227d8d50f6fc35848d104c32bd2d61235413000d4f585cc62540031bd5c6748d5040aaf481594648d02abd206748d5000caf4819d23540162fd207654123f5fc34848d104c31be8d1d104c9401ceb3464054048f27e2d212350130d5f0f484c94554c03f04c2674412300dd13089f63440feb9a046748d5000ce68119d235400a3dc607654123c8fc2714c13244353d1a0532545533efc36848d104c007748dd10d8903d3f4a804c95054c0372a01731895000cea7019d23540031bdd857581233eecb8640f6048c025b96147581230087e585d94048c035354e575192300ed1104c25650c03ac441409594300af1801865650c03a64c1409594386d4f7548d4654fa6b34e3279594300e35541865650c03ac441409594200cb446dd54644003a54c5439594172ab4484425650403cc441549594000ec9304ca5650003a64c14395940f5fc2544412
  | 2 => 0x78255e46440023be095791910ae8ef8255e46483dbf0d490340523f7fa352405425032bd2d49035412300c6f521d950508031bd48765412300ed1104c36250c03ac44140d894300af1801876250c03a64c140d8943f2e94431876250c03e844142d894000aad48d4b62503678b14954d8940008ef8251f63540023bde243d89509dab74814b6150fd7f0d0903405231cfa372405425031be8d090150123aadb0474436250327e2d090350123d5f0f4254d4548c03f044132d890300e595054f6240c029b16162d890300e6950d4b6240c1b1e15d50d8903a0ad68314b6150c6ff0d890340523a6dd0374436240c6a3d61e269591000fc1304cb624406ab920956d89101aae48254626440736c11d40d89101bdd0374c362440023b8a117d8d50008ef78cc76254323f0885304c910d4f462154d5148c023b8a107d8d45008ee2841f63545763b8a107d8d5200af30814b6150f4fd2881535412300ceb021d95048c039a54220d894500e69508836254c071e01d50d894501c78075436254c023ba1c31d8950008f68714b6150d769bd6043d895000ccd32dcd465480275e0d4755910008df835d95444003334cb735594100eb1105036351403334cb735591200ccd32dcd56480039a48150d8d5200ec5104cb6354803934c950d8d52e5e4c56dcd5648f979316132d8d5200dd130dcd56442db74dcd015590300acd3809f6354002b34e227d8d50b89cf8355f6048f0bccd4d015514000c775345e465400353d4d731895000c6f5319d23540031bd4f765432300ccd32dcd4648403334cb735192000eb1105036350803b144132d8d4200e8d325536350803a34c940d8d42e4e8c484cb6350bd38b14954d8d4275aaf48d4b6350803711c77351923e4e8f404cb635080371dc7735192306c3c575536350803744c3735191000dc532dcd4644003334cb735191000ec5104cb6350707b84c910d8d4000f911050f6350003b444163d8d40deed14344363502cb74dcd105193000eb11055363502cb3cdcd1051930b49cf8351f6048c02abd20631895000aaf4818f62542d273e0d4795923c1fa3434413250073e4dcd0150d40b2db047443635000374d0d7018543b3cf3635c06150fb3acd0d01d814100dd130dcd6244003714cb735891000ccd328dd2644003b154532d8d1200ec5104cb6344b8fb120532d8d1200dc771dcd6148dd23b21d42d8d1273dd3734056240c03b2541328d92000e695054a364838bb1441328d92000d4c57dcd6048f8bb2201328d920738ec8754a364801b1e15d508d920738ec8750a36481d63ba1f52d8d42c0fc13644140c8c03e84415450323c1fa14344140c8f03e8c8d0150940c0fa14644140c8f07785cd105032373de3734413250303e8d19105032300de3235c06150dd3781e11050323dffa04844140c8dd27a21d
  | 3 => 0x23d61c02d854300ccd074cb63548033341d32d8d4200ccd074cb63504033341d32d8d12e2ccd074ca36480023be1d56d8123078ef8754a0648c035341d5395923e8ccd074ca5640cfa7a2015751923018f8805d94548c065e2017550d5001cf07040546548069e20156541423ed68704c945540071ed9d50d815412b688051462540fb781c1105592301af0805590148cfb721c130559233eb688055d23540069e2015654123d3f48604c95054c071ed9d50d815312b688054c62540067c20171549103ebe0805490148c067cc2227959103eb68805495048c071ed9d50d8152019f08055f63440067c201579191001cf3074425650c035c1411791950d3f485048d635400352141731895000dc8505cc62540035a141731895000d685019d23540035a14137d895000e6850dd950c8f139a141611895000d4c505cc62540031b1406748d503edc8704c14648cfaba2014658123019e8805c943480033c5c0601854300cf1071836150c067c20147d8d103edc8704c16148c2333e1d23d81533edcb6740f6048cfb3ad9d07d812301ceb6740a0648fa2730e107959233ebe08048532441ce3b0a107d8d12038ec2841f635140e3b0a107d8d51019f00849f63440067c021279191001cf3074436250c0f33c9d23d815301cf3074076150c023d5e302d8543008ed7890f62540023b5e264d8950008ed7898f62540023b5e261d8950008ef825d94540c0279e094755910008ef825d9544400378443725594000ce510dc956500023b5e220d894500d6850dc94654003ac44140d894554a6c82543625140279e095758d10008ef825d9534400378443725590300ce510dc95640c023b5e220d895300d6850dc96354003b444130d895300e59305436254c0378503725591000de130dc956440027961f52d8910008ed7888362544035a143725855000f493054f6254176ba60063d89505db68584c36254002ba60043d89502bae8684836254176da16120d895000ae9801076254002ba60031d89505dae9080df6254002b960463d895000ae58110f6254002b946037d895000ce517d8a4654002b946247d895000acd381076254002ab52063d895000aad480c76254002ab52037d895000a6d5810f62540029b56041d895000a6d580c762542ba9b56064d8950aea6d5818f62542ba9b21952d8950aea6d5811f62542ba9b56037d8950ae8ec68dc96154003a350c43d89505da6f580df6254002abd2037d89505da6f5811f6254002b920543d895000ae71891f625400339c5f629195000ae7180df62542bada20154d8950aeb688054f62542bada20152d8950aeaeb080df62541769bd6031d895000aaf480c76254002b9e0543d8950aeaea800c762540023be0957d8d40009e78255f63440023be09578d910ae8ef8255e36480023be095791930009e
  | 4 => 0x950008ed2881e5644c123b4a20795923028ed2881e56448023b4a21795943058ed2885e56508123b4a21795923058ed288de56508123b4a25791923068dd381d9534801a971613654d2000c5c7654d4548c0e3760c765412354a5c8654d4548c031754c765452300c5c7654d5048f4b17d9d5395923058dd381d94344016a71213650d1000c9d431d94544d4ea7219435151300c9d431d94044f4727d9d4391913018dd831d94540c032750c7651503018dd831d95240c063760c765090300c9d431d9414c34327d9d4391930038dd3885e4648c030f550765454200c3d541d95050b770f51d53d85540587d581d94544c161f56076515030487d851d94154c121f61476501530087d581d943440161f56076551100487d581d9534400a1f6147650d510187d851d943540061f56076541420187d581d95048c021f56227d81410587f87552564800a1fe1d51959200587f8755256448161fe1d5495923010ff8755a56440162f1217654d10d7c3f6751646544162f121764c910058bf7891d364401a1fd6227d8141008ed78984625400f33c9d329590340aaf48d494648c172bd1d42d8950008ed8710762540035345d53959233f9e48155d4648c0a3d2057651523028f4815d9544c353711c52351953028f778dc54654f53d11853254553d4ec46148d6154c03335cc6118950018f48155e0644c0a3d20557d81433f9e48151d6048c0a3d2057650123d4dc47154d4648f23711c53051923dbda4715514648cfe79de3715192353ab4815194548c0a3dde37151923008f5789806150f23711c5325193053ab481519544c00a3dde37151930028f7188de464800a3dc623791950028f7188de4654802b94a0601854300ce5271865650c2eb54e060185430bb94484c06150f16b54e2621854353d3471515435476b8d185545414353cb7675176150c36ad61056185430dab5481806150f5aad5235618543ccab5489886150c029d5606018543028f7188de464840a3dc62279195053e3461551515094f8d1855454540018f48151f604840a3d20547d81533f9e48151f6048c0a3d2054781923848bc4845e56500162f121179590305c3f4751761540170fd1d45d8553028f48151e56440fe792054795923028f48151e5648c0a3d20547959033fce71748e465436b4dc5d4591950028f78745e465400339c5c629195002c77175464654f53d11053254553dbf24414c9455476b8d105565511053d371751646544032d10547d8151faf0c414c94554f23b11853258530748ec2845e364800e3b0a117d8d50008f508dc54654c023de194754f10009e508dc54648c023d423715192300ae78651d23c40023de194748f1000ce53241f6150c023d42217d8143008f5871436150c03394cb7650f1000cd530dd943c40032d5037650f104b8f5871836150c
  | 5 => 0x4d4648d075315d535192300ccd231d94154c035351d5395923d5f0c644c94554f57a31912351953419cc8754d6148d075315d5358523419cc8754d6048d075315d535812300e4d5319d2351403535cd451895000d4d585cc6254003535cd531895000ccd735186254003335cd6318950509cc7848d6054c03335cd61189502b9cd8319d235400e3360c6748d5000ccd73118625400eb360c6748d504cacd831594648c0eb31a1235095354e4c684c94554c039354c6748d5100c4d5319d23540035354c6748d5000ccd6319d23540033354c6748d5000e4d5319d23540033360c6748d5015ccf874ca5640c039354c565192345b4c5848d4254c4f53d9d53959233e5cf8740f6048c8e731e1235590300ccd3019d235432b931593055923c9d8c474c9614c0fa731e130559233e9cc784c14648c03334c87650530c9e8c464c9464c0fa731e1305852300ccd3748f6154002b34e36748d4500acd38d9d2354402b34e36748d5000acd38d9d3250402b34e3674c94000acd389d93244003334dd2391950039cd3885e4648cfe3b21d4658523058ed821d94244d032b11d465852305aac485894244c023b60876515033e8ec875596048c1a3b6087654903008ef875825648d071b15d565812306a6c585895240c031b15d465812345a6c585894240cfa3b21d4658123058ed821d94240d023b61d329594200aad4819d2354106ab5206748d4541d2c575514648c0e6b1e1425152341b2c585094548cfb2b1d923551403eaad4819d32500fa6b21d4250123dbcad4748f61550ff1b1d932515513ec6c764c945540fa9b5606748d503e96c875495048d531b55d32d89454096f875525648cf87be1d42919234196c5851d6048d069b161764c91040aac485d932441065bde25758123048ed821d94548c023b1e13255940038ed8319d23540123b6087654523048ed821d95048c023b21d564c91000cad4819d23540031b5506748d5000c6d5719d23540031b54c6748d5000c6d521d95048c031b5606748d50008ef6881e5648d023b61c569192300e2d541594648d178b159425152300c6d571594648d171b1597251523cfc6f6755e5648c571bd9d529592300c6d5715a4648c123b6087650523048ed821d94048d02abd235651923008ed281d943440163b4a07650910048ed821d90148c033348c7654d1245e2c56509454480a3b6087650d1253aac8650945448033348c7640d12018ed821d954480063b6087654d20128ef874825648c4a3be1d209594245e2c5650954480063b6087650d20d3ccd2754e0648c123b4a2178192304ccd2740e4648c123b4a20791923048ed2885e4648c033349d309594300cad275025650c023b4a2279594305cad2750256508133349d3095923008ed2881e5650c023b4a20795941058ed2881e56508023b5e34618
  | 6 => 0x20004060400fc11048d4054c03f0441235150300fc1104c14648c03f0441325193000fc1104c94240c03f048d035191000fc1104c9414c3d7f01511048d0300fc13059d1048c6ff04413258530f5fc0464412340c03f048d035891000fc11048d0344bdbf01611048d03f5fc0484412340c03f04c067441231bfc0684412340c03d2541535812300dc9805cc6254003e248d405513000f893051d3250003e248d405090300f4923541544c003d24c15748d5000f49235415240c037248d705513000dc9235c1514c0037255d03d812300dc9235c1414c0037251d03d812300dc97340c6254003724c06748d5000ec93019d2354003b24c0674c94004dc87648d504c32bd2159235413004dc87648d404c327e2119235013000f49235415348003a6581435011300f19305515050c03c64c15454d4000d59305d54054c03964c15654d1000d59305d54354003964c156541234ed58674c15054c079619d30541534ab987840d4350007661e10350d4004a986840d43500a2e61a10350d4004e986840d4350003b24c0764c91000cd9301d93244323b2219304c91000dc91740f6048f23f0145304c91000f91305006150f23f0105304c910c8fc0714c13244323f0205304c910c8fc0214c13244003d1545535852300ae5821195644003d1485535452300f2521551515080ab91a1215454200d957351d1050c03a5585435053000ad5831195644003c544d4550d5100e95135194354403a544d4650d104be947644d435040b651d91350d414bb947844d435040a751e11350d5102d947844d4350412a51a11350d4138b946844d4350413a51a11350d413db944844d4354403d148d105155300f452355d0154c03d15453254d10d3f45104c95054f4fb14412355903d3ec50648d53c40037144173189501aec46848d0154f1fd1161234055300bc53899d1048f1ae9121674412300ae58219d1050c72b96086744142029e478485424406ab521953405231de545654d0148c72b560c67441431cd944750d634400a751e13150d101cb94484c543440fab9219514c910009e4784414648c033948c674414300ce58219d1050c02b52194358d1000cd58319d1050c03354c47650d1000cd50319d1050cfab9219414c910c6ea44648d4644103a9119414c9103eae5811d932440fab9219214c9103ece5174ca26440fab9462764c91000ce51748e465432f3945d23919513ece51748e46440fb3945d329591000f0d535514648c03c348d455095300f0d235154054c03934c9565150300d4d325d54154c03534c9755015304d4c764c94554c03935593254d10d4d4c674c95154f4f5319d3254153d3ccd574ca5640f4d73e1d5395923d3ccd5748f6054c033355d32d8d4200ccd574cb63504033355d32d8d1200ccd574ca364800f3355d32d8d52419cc875
  | 7 => 0x5f9216cac2452decdff1cb1b000002e3c4e0004511af26031d72c49362ce5b800000ca24e00038f5eb647bb01f29ee400da63c955b4c8292285e6b002607692a8450e40cf2ccfe710bc2d5efc5957b07a36a0fae9c0013b102820ed80067f61814ebfa989f009789c679517a223091206c142b063a20000df47897e5d6cd5a38f28af41db5b72a1de5ea13beef83f000e5e00000000000000006eb4acb029daa98cc9bbbc89b00000397000b40f3c000008a6731c39799832e896000ba0b6a15cf42a8585e9c39b4c3a40033024d725935de5dc6b400000ce581b5230e266ded4545d0012d88c0000018d5d280000016e5cd3992283a769b52975d4000d70575be53132d6862fad324c0f890dc8629e257000002070474000b40345f82e5e000080cc790d000c08005db388000a662d3ce4b8000bb68c5d9b6ac8b61ae1dcbf4d46648e8000c98e52aba5c498c2800500ad12c8000005c18602af90d80d4c67800eb7065c5800365e8c4e8009d6fe1a4a6b3de6e8003dd030a140d2d40050e0301360a03010b07003b150d37101002000f1201010804040c000213021800011c020e07270f01010e450905010006087d01031d0409020301030d010401000103030e078a071b2417030d2b01160a0a0206510a07110c03000d4505062101004c250a000021030038000000000119000219110c5315010f2f2e1b17000300662c08000003006a02000209070f08010b040d00220202042200030c030800110b0601780303002d000b00031c061301020103020704780608070307060300210107000002031c01011f0c01010800010000000800020101130002511703064200070209011e54040002050200000200000a3d1a05020001081305050100020f0500001070320400090304001d0803012d0008170002062e2a070300051d0303030929080b0108030700030401003c030000010709000e4000050a02050020010005150d02000b2608050f010d00000220070402020401091d0d00020f05004b060301090505000006000804010e0003290b071c0452003f00010103030200010b000609080a0400020301220c010d0208015e0317160600010b08000f0f110409000201110c08010011181301080001000005030401050106000a00010106110d0007230300060000070201040400000001010006300014190a030a06011d00000300090221030009060015010703000704020000000a000018000001010e05004d06000617020302040002020002020f0a010700070017000101161600010200020003000d00130008070b090100012c081c020009190b06002f063000070f000608082d00000104000205000110030206180629080700003100090304200200001005000500030d0708021000042f02060e0400010a07040c0001050102030302
  | 8 => 0x38d3024a0cd2af000002bc668ec4000005cae020410cf2b65fe84f1e98db84d484b44c16bd24cce2d595496713428856f5435a960c1e92cfcb33df8002308665358a5a4824003665ea01f5ad6503c9e0dae71e5b726003b885a000378f6fb09ac000003ba8e9aa800000968fe631e17000003bbcf3000b58666260000020d450ce0376ebc855a3286df000166000000003b923de374416cbf90d000cda00230d62000120002be001a6a3b80036800100e6927a057741d50000039e84b67c036dda50e1856a05901ca00028d5cfa2a000000d8000000001539817f0000000009bc005c44ef6bb718ec000e56818005e4d60bb800479336eaf7f43a6c6e8d73000423a7e339a3bf6560965ba91df5b2a00103f06800c06f68000000018d3016430000000036940e000006480607ea3eac111a484cb71d3c3006ac1d4761ca93e8009bd31005f15cc31c70eabc7fd8f1b7737000194f6000754d9b238606fc11362bd2900f8fc722c7da6fec7ab82d5121c16dbc53b81a19c1a440537fc1dca8e1712af70cdaf465168e94996013ee2e1a9e99b3aae93a85703369e1b97c64b26f6ea4ded37c13cae97869074a98ce6af1f231c41b007e76ce4428c342f0fbaef6461b04beed7329d58362e5b1d4bae94723e9fe704b11d781400429e0cce723436ac8dca17cd3c3d2d4f14c77b8d8e8fed827db48000d00016d3503a4b20920abbe1bd8cb57cb5211e627314dcbee7f83b8cb81b0ee451ab001eb0e9e1f224001eb17a7569efc001dbf6e81e4504b593ea92160cdfc731d59350bcc9adda8e5310db1513395b0ec660e29c13544c2ea641f66ea0c953c09cf673abe6393e3b2a291b91d7517cb67c1d615e75dedc32106e060e9e6199cfbc3a4a0220e10388d27ef014758d4e6b324e80f6313204919f1bee5db998abf585ec96968f6e62f4c04a44c86aaf6f35880b2c542ed0526d8fb3f71586603b69de7e024e4baedaae3ac966e6300887a41778f1c2be920d4d6bc6e0aff5e107bee7e786f9a0a5728f9180707058ff7049cf164e810ecb6963875c2394e82bf24ac4052577d15c012b110965df930d5f0f9e6548f283511bf389cd99b751823e10933b9a4c58897456912933a4005eb0006a400000e3d4d9171eed7dc838a45b9b0001461170010dce3849b0342ba186d7c97d6568a480958c006da7de8f8002d77f4184006570006bf921da6a3b40a55a7000af54b8000000015a222545be9661f4dcbb7e810e256600349f4d7b33189549f5d93522c5da1dee880041b63c0c68e5df09e77992d17b9d6f0002881dbb93c4cccf0afc75b039038d970b1514aa2fc8af81505078001565540000071887b601f1000141bc90c228a71030acb817e49069ff07a5e1427aecb6d16092ebb733d41f635dc309d5e6fdb352330dbd4458b33f800379520e84000
  | 9 => 0x44d39d0000036099f5e0879b3acdb7a89063d86b8dc0e5035e0a8fa2c1a2ae4703a410827ec003cc1d6ddc07aa9a3f5e307c91800d024b4230002dad07b800e62d9c6b8cc86a896d93d971ea0036896651ecda5c00010a001fd8005be8980050f3cc000ac000557a7af76892d3d848d585e01e7731fb32c8279a6b831f379fafc8437ade32a9aedad1e9946c87b6ff00034a000000002817fe6ec6cd770000036498800000172800126000000008a82e0d4579c187cb189c0678b1d08a3984eb10bc0007d5d1b986f8bcc2f80000090db28000e6812bf3d329a82746fc431d000200f9a000008a5a427e9a4001a744f001cb5390000019ac3c0fc52c000005660000012d638238e1000279be71695215ec1e21c4a74800a21310644dd82ab1bae7e4ea9fc66f9778000620008595f035a69d389ead5e12b6e9b19ff8abbb33db658bd84b0d51bd4f541bec52575bcddc001e50019f38436f99ca0db000033a5040010b4ce0010afb189341b7305de68a03b5036bd38f44afb63271b77a6366213dbc1b9a48c002100004843e1430000010e80067aa5928a5dcc9c20f7c006b0823a08001d2ef43ca0c00000022fb622ff57df10999b10264790bfd15a021c90000bdb787b46a0f99ef6bf6f0017e75e49653926000119af66954da271bf21c6d32b73834c0002d2f9239574d022d67ab52093979b24a3e9f25da61e2f34409e181800c9b3848280062b0ab85800622d5a9a3c14dacd58202693b8fb46eef0000eeb764e39ca7c13800001422057643c03257b68000000000000000003b6d052e5bf0fa9484c35da030005fbeb94abe7cce166ad000d6638e8f73c7aa0012941659200145d4c7e6294000690011b26ce7d05d4f4fc8c0de72dd24e14f4b0c52c1250e3d4fcda847af2725e6326421a19a6ab02d74e6568589b8ab4fe4f0320b356eb24a7c3f624c5eb394e347a0e3436fd15b12786e23a9f840d97185ee2806ad46118cad2c695c84a9b6f3bb313ba836a72b1a2e8fe1e20eba20101c870b99b50e01ed4dc5fe93928b71ff57575de21ad5780658df2ce9e5704ed6e26000000000a373c31fd323480021654b0ca108a3a24e99388178af700003f5a975431580076295294d4f1e3aa4495f01ee000000c3ab73913451976b12c2132cdfc542e2800000c733a000f238a000000000001b0986b98002ec8c855b221d1ee1bfc84a95883d0d4fa579955cd79763f049fe000b58008d6d574dc51dd2dd80035058cea4e28000d5d60cbd599f2ebeaac62602adeec1878deb1767690d0e5ec005f200042aff8a7db2d0800000000ce017ae8378f45b2000a6fae5dc6420006b3a80000003358918a8888dadb2fa2bba2216bd00f2443ba24e61a6739633b2a520653c9e001d0400308644e60005511752f80017d237394822d3165515e5000001d800
  | 10 => 0x4760005cc002e908f5855b731000a39f605782a23a458ee2ab5524bdf15a18059b800000dab08a73a60ac41243fbf4001722b0bfa92ed2ecf8cb46284cf711208599bc00c8e5ece565deeca4f21a7c615034befbd249295402006e00087f54a6b97c000000006dfd6a234be82c001c2946d2c0048d3420000018d15297b9f0000001318be7510c93c0023b001ad6cda0ac808522b6048e6a79c8cbd00000150000a94288001dde33870000005d4b8cb10008bc001189061fd50b3b6dd0688715302aaac85d169270143454cd5c19c3ee18652488ece003de469a8ae597434075c118b1ed04a4728001395123df285ab974007b4346000ec000bc81ec001eba74b64d9d6c274001026650010d2fa6798ab12928a66a3abec4870d2fe4fe612dc000b85de9eaa50e7e7762324830400422a1d446d6c2600000009ef5b900010ff42e3f650a074cc1158265945d16001cb2080510223231340b96b30074c120038bf0e39a00156340b44114005475fe58c0075e1e7e7b1091300196000d21ee63c1a2f6bc1400167f9c2cb096b38a1000000002e2000d7c00000000354b88c5001c2b22f8216bb9c00756b9b518001d188550c1a800a1800286800000002fb07300000277a93934c0003000161ea1078000015eb4a00000135c0000000048b13d315a8319ba5b8698915f8194000df0000e13b361ed5739001e11c574049a988000000004bd3800000142c3929467b78dbec4cb844c4a1e5ef2e0035fbc2000ccb66b5c4800014ed2078869b52d9d119aec006590b0eb1cda1b38c1ea02e64eea5bdc4800c378fc004a52180f8004350009ab4aba86ea6144f80000001000320000003aa87fb434ba2e68c465c89e2bc9d08c3c8f5c300125757000957638a3641001e2f9b41c41a90e349fb847a38530039d8884004fb0007a4003bb1fa0011c0003e28f784832a4c664005bfafc73db8b2ee24e3008abaf1aeb709d9800f1f8744d50005b27eb091ce1c0000eaf2a2ad590000ebe4e23911c920000052dde37bc005d6c44a84000005b717e8b5d4c76001e69fd68f22
  | _ => 0
def g6K4 : Nat → Nat
  | 0 => 0x1e513515435440292a7220a8fb02a2098958150c76501131ac62c1a2033a46a80065154c7848d564400388a20a98ce91aa001c451748d539195000c628bb063148ca87c71145d2354e465440229b12282e6312a00184f8754d609592300d06a9a9033a46a820e835215319d2351506a192ea9aa8a3247f5c0d4748d53d855404c26ac2463b282a98061354c784c9565000311b06a40ce91aa00188d485cc631895000a86a48a0b98c4a82a61360d5419d235400309ab0b988c312a00184d835606748d5000c26ac2e6318c4a80061356137d18625400309ab09bcc2312a0070cd89a0c6748d5000e06aa2e6230c4a86e68360d541594648d52c18d291a8aa12a60144d9314957d8d4200c26a990eab2648800513da7585cc625400381aa6a40ce91aa00144d935606748d5000c27b42a703cac91805135668319d235400289a72280ce91aa00144d39d5c6748d5000a269cca033a46a80041b6245019d235400285a92280ce91aa1f5d047154d5451923c5a62c9e4e30caca180631c5d8318a465400384e2ea28c5232a0014689055c565192300ca4402e6a28c4a80051a2415419d2354002a9120ac2e6312a001948805cd531895000ea0880a0b98c4a8007184405019d2354003a8232282e6312a00194989141731895000e84a48a0b98c4a800712584505cc625430ea9613282e6312a0018688015d465812300aa49c8a1b928ca8005524e450dc96354002a9272286e4b0aa0012e19020543d8950ae9a444a60a9ec4a8006a26014310f625400350b02a1887b12a0019c130e0957d8d1000cd0a0704abc8c88006a410d801876250c03892a7810eca824601d135910d701854300ac9b4886b80c2a180534da4435c06150c02966d221ae030a8601c936910d701854300f4088264a06c6a1006234df4818c62543cf986c691ae030a86e786887541528d92000ec194886b80c2a1ba6386032319d1050c03b008791ae030a8601cc130c8c674414300e5191a8033a20a180664e24435c06150c0318a6f8c0c6312a0011978910d07d85430094bc4887bb287880071254e3019d2354002a90b3182e6312a001cc1104ca07d8d4100e60882471bec09080465a6043dc55650c0232d3021ee2b1286011969810f715814300866cc46f31ec4a800513e615319d235400338261146e6ab22001cc1104c227d8d5000aa49c8a113ec6a80062360f4819d235400381aa7a40ce91aa0018c583a046748d5000e22a9d0233a46a80071254e7019d2354002a90b3402e6312a00116a9814227d8d5000d18c02a830caca1805254e446dd5464421316301a28ce8828601b41309616748d1000ea0882652bac481a0c93261535825648c0249a72412ad2b2060144e594c06748d5000d50a0250234ac88006a45013811a564400389261280ce91aa00146b975825095923
  | 1 => 0xc0495c1e126115243284f9ec6a6700334b28824802ab5b003e1de4d411dea95f5fcf801668ebbaf06b1e016c13744852240005a9200fb302623281b64e876c3003a51a000017c01329e0d8008713cfc0096a29b1e4b6490380cad46385bc0d6f8b1a211818beeb4b5f14aa264062ec60c66a3748002a52a444732841da17204002c577004b2169d2b530012d239e4aad864c9c0ed58fdaed485ad409b51b190a240b50fdd27251343a0bb571fc3800eb00595eac0582f5560000541ec0013591e80037bf6880a53d269acc9996de2692554e771a698e1c10c84c3490e6220b400003e8fa0a4254002b0b85e1391c780000001136507400001a002e31125801c8c55618690dc37105435e11c20421a718a474ed57584010f33501656e578cecf79b9cd5321b002ddae100021197590000d3ca02150d08104038096304b1c08c63869008c742a8820030af8410441810c5ce0088042120aa080002006208f9a74e00030218078a68400218008658a10020408008c00200601238439a680f880022806801162060001001804840064080801807c0441235154054fd770090982ce88246379c07848d035191000d609830433a20a1806704c0784414648f22b80f288264a3261ebe804648d03519103ed60c0a603b264880073045d2340e46540fb9822e91a07232207dcc1174c1329591000ca4c02b0b98c4a800452624505cc625400239312282e6312a001a498054c565192341ca443aa0a9ac091a0e926015319d2354002a9312282e6312a0018c98060c6748d5000aa42cb00b98c4a80069254c865416048c0389300a98ce91aa001a89305206748d503ed44a426033a64a01f6925613019d23540031926043aac9922001c493055c6748d5000e24982a633a46a81f4d22253055d2354002a9272282e6312a001549391406748d5000c64842e6318c4a8006521617340c625401319300990eca0a6001c89274c1409594300ac48488693caca182d2664c76501434401713300a18eca0226098998050c765150300e0ca82863b28a8182626601431d9414c036721129828030a86015910910d07d854300e4898281bb28788005a442443dd943c4003192109bcc2312a001a458154c565192300d22c0aa633a46a820e916055319d235440318b02c18ce91aa001c458154c6748d5000c628c2e6318c4a8006196095819d1050c0344b04a288cab220a762469485545454200872c4e2e3148ca8005614644349e5650c6e52a9243286b1a20018958150c765150300d0ac1a8a232ac880062560d47119564407312b06a38ce882860189583520674414305c4ac1a823b286880062551d3811a56440030ab06ac0ce8828637194895cd4744143008cac4886b80c2a1804656244319d1050c1712b02a18eca0a6009895484c47650d1004c4ac0a863b28a89a9d45
  | 2 => 0x1695d9b4c172c70e0007b4f4a45000f900001fd049a172d31e3a0020cd27f802569c00002844f0000040a372c6000000c915ad380048c00e200011ceea36c29635c000000168458004a7f419c15400530b800ce60ca944658845aa4d900000a691230c52741b1bc0e400b6cb8b49b0022800ec79b3d667192538007e2180000000b5c0540100002447aa19f28cfc43061888f6dbeaf6633b282f8f7bd2559147bb17934978bc9921299eae848800f1623817ab054001331002de2b8ac9662a5809a800003a800724
  | _ => 0
def g6K3 : Nat → Nat
  | 0 => 0x3601c381100000b9154ed4c0be057814992eca8405ac68c20af2aa314636a201ee474a5206c8064365e005700500009ab444184051a0c500c5062510141731895000c5046589141731895000d405652310d701854300d404a55910d701854300d204252310c674414300a306831760c629195000852668805cd451895000c4262549141731895000c126256114173189500085262859a01731895000e02601535206748d5000c12601935606748d50009124e8905506748d5000e01605535206748d5000c216252310c674414300a0962b175146291950008256688311d5658d1000d015652310c6744143c5b0168f27550619594300e01c5d835146291950008a46a44360061d894300c446635910d701854300d045676910d701854300c606632910d701854300a606a043c8d7018543
  | _ => 0
def g6K2 : Nat → Nat
  | 0 => 0x11005801b0c5d835146291950
  | _ => 0
def g6N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | 3 => 25
  | 4 => 191
  | 5 => 988
  | 6 => 2826
  | 7 => 858
  | 8 => 35
  | 9 => 1
  | _ => 0
def g6R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g6K2 (i*91) 83
  | 3 => packedAt g6K3 (i*80) 72
  | 4 => packedAt g6K4 (i*69) 61
  | 5 => packedAt g6K5 (i*58) 50
  | 6 => packedAt g6K6 (i*47) 39
  | 7 => packedAt g6K7 (i*36) 28
  | 8 => packedAt g6K8 (i*25) 17
  | 9 => packedAt g6K9 (i*14) 6
  | _ => 0
def g6H (k i : Nat) : Nat :=
  match k with
  | 2 => g6Hint (packedAt g6K2 (i*91+83) 8)
  | 3 => g6Hint (packedAt g6K3 (i*80+72) 8)
  | 4 => g6Hint (packedAt g6K4 (i*69+61) 8)
  | 5 => g6Hint (packedAt g6K5 (i*58+50) 8)
  | 6 => g6Hint (packedAt g6K6 (i*47+39) 8)
  | 7 => g6Hint (packedAt g6K7 (i*36+28) 8)
  | 8 => g6Hint (packedAt g6K8 (i*25+17) 8)
  | 9 => g6Hint (packedAt g6K9 (i*14+6) 8)
  | _ => 0
def g6I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g6K2 (93+((h/2+packedAt g6K2 (91+(h % 2)*1) 1) % 4)*1) 1
  | 3 => packedAt g6K3 (2085+((h/17+packedAt g6K3 (2000+(h % 17)*5) 5) % 59)*6) 6
  | 4 => packedAt g6K4 (13941+((h/127+packedAt g6K4 (13179+(h % 127)*6) 6) % 449)*9) 9
  | 5 => packedAt g6K5 (62536+((h/654+packedAt g6K5 (57304+(h % 654)*8) 8) % 2314)*11) 11
  | 6 => packedAt g6K6 (147774+((h/1869+packedAt g6K6 (132822+(h % 1869)*8) 8) % 6617)*13) 13
  | 7 => packedAt g6K7 (35416+((h/566+packedAt g6K7 (30888+(h % 566)*8) 8) % 2004)*11) 11
  | 8 => packedAt g6K8 (1007+((h/22+packedAt g6K8 (875+(h % 22)*6) 6) % 76)*7) 7
  | 9 => packedAt g6K9 (15+((h/1+packedAt g6K9 (14+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g6Pos : Nat → Bits
  | 0 => 0x2c958964562592a25fed897ff92c44891117cf
  | 1 => 0x552612a8984af7c4af767fe25850bc1222f3f0
  | 2 => 0x9bf4a4ddd2937ebff92492a4aa050978f0fc41
  | 3 => 0xe238471efdffa4c9324724c9349a1224ff2092
  | 4 => 0x3bf7ff0e11c4711c4784711c0e3e07f444124
  | 5 => 0xffc0781f01e0781e0780781e0703ffc0888a08
  | _ => 0
def g6Neg : Nat → Bits
  | 0 => 0x7ff801ff80000000003cf
  | 1 => 0x7fe007ffffe000003c0000f3f0
  | 2 => 0x3ff801ffe007ffff800000000000078f0fc00
  | 3 => 0x1fffff80000000000000000000ff0000
  | 4 => 0x3ffffe000000000000000000003c07f000000
  | 5 => 0xfc00000000000000000000000003ff80000000
  | _ => 0
def g6Atlas : Atlas := ⟨9,rawDecor 63 g6Pos g6Neg, 0xfffefffaffeeeea0fffefffaffeeeea0fffefffaffeeeea0fffefffaffeeeea0fffefffaffeeeea0fffefffaffeeeea0fffefffaffeeeea0fffefffaffeeeea0, g6N, g6R, g6H, g6I⟩
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_2_0 : Interval g0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all0_2 : Interval g0Atlas 2 0 5 := b0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_0 : Interval g0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem all0_3 : Interval g0Atlas 3 0 25 := b0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_0 : Interval g0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_32 : Interval g0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_64 : Interval g0Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem all0_4 : Interval g0Atlas 4 0 91 := (concat b0_4_0 (concat b0_4_32 b0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_0 : Interval g0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_32 : Interval g0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all0_5 : Interval g0Atlas 5 0 44 := (concat b0_5_0 b0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_6_0 : Interval g0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all0_6 : Interval g0Atlas 6 0 1 := b0_6_0
theorem all0 : ∀ k ≤ 6, ∀ i < count g0Atlas k, checkRow g0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all0_2 i (by omega) hi
  · exact all0_3 i (by omega) hi
  · exact all0_4 i (by omega) hi
  · exact all0_5 i (by omega) hi
  · exact all0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_2_0 : Interval g1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem all1_2 : Interval g1Atlas 2 0 4 := b1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_3_0 : Interval g1Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem all1_3 : Interval g1Atlas 3 0 16 := b1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_0 : Interval g1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_32 : Interval g1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_64 : Interval g1Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem all1_4 : Interval g1Atlas 4 0 92 := (concat b1_4_0 (concat b1_4_32 b1_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_5_0 : Interval g1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_5_32 : Interval g1Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all1_5 : Interval g1Atlas 5 0 44 := (concat b1_5_0 b1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_6_0 : Interval g1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all1_6 : Interval g1Atlas 6 0 1 := b1_6_0
theorem all1 : ∀ k ≤ 6, ∀ i < count g1Atlas k, checkRow g1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all1_2 i (by omega) hi
  · exact all1_3 i (by omega) hi
  · exact all1_4 i (by omega) hi
  · exact all1_5 i (by omega) hi
  · exact all1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_2_0 : Interval g2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem all2_2 : Interval g2Atlas 2 0 4 := b2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_3_0 : Interval g2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem all2_3 : Interval g2Atlas 3 0 16 := b2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_0 : Interval g2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_32 : Interval g2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_64 : Interval g2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem all2_4 : Interval g2Atlas 4 0 92 := (concat b2_4_0 (concat b2_4_32 b2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_5_0 : Interval g2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_5_32 : Interval g2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all2_5 : Interval g2Atlas 5 0 44 := (concat b2_5_0 b2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_6_0 : Interval g2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all2_6 : Interval g2Atlas 6 0 1 := b2_6_0
theorem all2 : ∀ k ≤ 6, ∀ i < count g2Atlas k, checkRow g2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all2_2 i (by omega) hi
  · exact all2_3 i (by omega) hi
  · exact all2_4 i (by omega) hi
  · exact all2_5 i (by omega) hi
  · exact all2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_2_0 : Interval g3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all3_2 : Interval g3Atlas 2 0 5 := b3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_3_0 : Interval g3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem all3_3 : Interval g3Atlas 3 0 25 := b3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_0 : Interval g3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_32 : Interval g3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_64 : Interval g3Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem all3_4 : Interval g3Atlas 4 0 91 := (concat b3_4_0 (concat b3_4_32 b3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_5_0 : Interval g3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_5_32 : Interval g3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all3_5 : Interval g3Atlas 5 0 44 := (concat b3_5_0 b3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_6_0 : Interval g3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all3_6 : Interval g3Atlas 6 0 1 := b3_6_0
theorem all3 : ∀ k ≤ 6, ∀ i < count g3Atlas k, checkRow g3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all3_2 i (by omega) hi
  · exact all3_3 i (by omega) hi
  · exact all3_4 i (by omega) hi
  · exact all3_5 i (by omega) hi
  · exact all3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_2_0 : Interval g4Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem all4_2 : Interval g4Atlas 2 0 9 := b4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_3_0 : Interval g4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_3_32 : Interval g4Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem all4_3 : Interval g4Atlas 3 0 50 := (concat b4_3_0 b4_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_4_0 : Interval g4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_4_32 : Interval g4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_4_64 : Interval g4Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_4_96 : Interval g4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_4_128 : Interval g4Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem all4_4 : Interval g4Atlas 4 0 136 := (concat (concat b4_4_0 b4_4_32) (concat b4_4_64 (concat b4_4_96 b4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_5_0 : Interval g4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_5_32 : Interval g4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem all4_5 : Interval g4Atlas 5 0 48 := (concat b4_5_0 b4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_6_0 : Interval g4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all4_6 : Interval g4Atlas 6 0 1 := b4_6_0
theorem all4 : ∀ k ≤ 6, ∀ i < count g4Atlas k, checkRow g4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all4_2 i (by omega) hi
  · exact all4_3 i (by omega) hi
  · exact all4_4 i (by omega) hi
  · exact all4_5 i (by omega) hi
  · exact all4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_2_0 : Interval g5Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem all5_2 : Interval g5Atlas 2 0 9 := b5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_3_0 : Interval g5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_3_32 : Interval g5Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem all5_3 : Interval g5Atlas 3 0 50 := (concat b5_3_0 b5_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_0 : Interval g5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_32 : Interval g5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_64 : Interval g5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_96 : Interval g5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_128 : Interval g5Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem all5_4 : Interval g5Atlas 4 0 136 := (concat (concat b5_4_0 b5_4_32) (concat b5_4_64 (concat b5_4_96 b5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_5_0 : Interval g5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_5_32 : Interval g5Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem all5_5 : Interval g5Atlas 5 0 48 := (concat b5_5_0 b5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_6_0 : Interval g5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all5_6 : Interval g5Atlas 6 0 1 := b5_6_0
theorem all5 : ∀ k ≤ 6, ∀ i < count g5Atlas k, checkRow g5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all5_2 i (by omega) hi
  · exact all5_3 i (by omega) hi
  · exact all5_4 i (by omega) hi
  · exact all5_5 i (by omega) hi
  · exact all5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_2_0 : Interval g6Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem all6_2 : Interval g6Atlas 2 0 1 := b6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_3_0 : Interval g6Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem all6_3 : Interval g6Atlas 3 0 25 := b6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_0 : Interval g6Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_32 : Interval g6Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_64 : Interval g6Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_96 : Interval g6Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_128 : Interval g6Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_160 : Interval g6Atlas 4 160 31 := block_range (n:=31) (by decide +kernel)
theorem all6_4 : Interval g6Atlas 4 0 191 := (concat (concat b6_4_0 (concat b6_4_32 b6_4_64)) (concat b6_4_96 (concat b6_4_128 b6_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_0 : Interval g6Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_32 : Interval g6Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_64 : Interval g6Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_96 : Interval g6Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_128 : Interval g6Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_160 : Interval g6Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_192 : Interval g6Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_224 : Interval g6Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_256 : Interval g6Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_288 : Interval g6Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_320 : Interval g6Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_352 : Interval g6Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_384 : Interval g6Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_416 : Interval g6Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_448 : Interval g6Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_480 : Interval g6Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_512 : Interval g6Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_544 : Interval g6Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_576 : Interval g6Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_608 : Interval g6Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_640 : Interval g6Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_672 : Interval g6Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_704 : Interval g6Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_736 : Interval g6Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_768 : Interval g6Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_800 : Interval g6Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_832 : Interval g6Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_864 : Interval g6Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_896 : Interval g6Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_928 : Interval g6Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_960 : Interval g6Atlas 5 960 28 := block_range (n:=28) (by decide +kernel)
theorem all6_5 : Interval g6Atlas 5 0 988 := (concat (concat (concat (concat b6_5_0 (concat b6_5_32 b6_5_64)) (concat (concat b6_5_96 b6_5_128) (concat b6_5_160 b6_5_192))) (concat (concat (concat b6_5_224 b6_5_256) (concat b6_5_288 b6_5_320)) (concat (concat b6_5_352 b6_5_384) (concat b6_5_416 b6_5_448)))) (concat (concat (concat (concat b6_5_480 b6_5_512) (concat b6_5_544 b6_5_576)) (concat (concat b6_5_608 b6_5_640) (concat b6_5_672 b6_5_704))) (concat (concat (concat b6_5_736 b6_5_768) (concat b6_5_800 b6_5_832)) (concat (concat b6_5_864 b6_5_896) (concat b6_5_928 b6_5_960)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_0 : Interval g6Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_32 : Interval g6Atlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_64 : Interval g6Atlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_96 : Interval g6Atlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_128 : Interval g6Atlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_160 : Interval g6Atlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_192 : Interval g6Atlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_224 : Interval g6Atlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_256 : Interval g6Atlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_288 : Interval g6Atlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_320 : Interval g6Atlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_352 : Interval g6Atlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_384 : Interval g6Atlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_416 : Interval g6Atlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_448 : Interval g6Atlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_480 : Interval g6Atlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_512 : Interval g6Atlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_544 : Interval g6Atlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_576 : Interval g6Atlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_608 : Interval g6Atlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_640 : Interval g6Atlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_672 : Interval g6Atlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_704 : Interval g6Atlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_736 : Interval g6Atlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_768 : Interval g6Atlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_800 : Interval g6Atlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_832 : Interval g6Atlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_864 : Interval g6Atlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_896 : Interval g6Atlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_928 : Interval g6Atlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_960 : Interval g6Atlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_992 : Interval g6Atlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1024 : Interval g6Atlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1056 : Interval g6Atlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1088 : Interval g6Atlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1120 : Interval g6Atlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1152 : Interval g6Atlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1184 : Interval g6Atlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1216 : Interval g6Atlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1248 : Interval g6Atlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1280 : Interval g6Atlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1312 : Interval g6Atlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1344 : Interval g6Atlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1376 : Interval g6Atlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1408 : Interval g6Atlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1440 : Interval g6Atlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1472 : Interval g6Atlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1504 : Interval g6Atlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1536 : Interval g6Atlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1568 : Interval g6Atlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1600 : Interval g6Atlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1632 : Interval g6Atlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1664 : Interval g6Atlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1696 : Interval g6Atlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1728 : Interval g6Atlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1760 : Interval g6Atlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1792 : Interval g6Atlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1824 : Interval g6Atlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1856 : Interval g6Atlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1888 : Interval g6Atlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1920 : Interval g6Atlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1952 : Interval g6Atlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1984 : Interval g6Atlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2016 : Interval g6Atlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2048 : Interval g6Atlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2080 : Interval g6Atlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2112 : Interval g6Atlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2144 : Interval g6Atlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2176 : Interval g6Atlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2208 : Interval g6Atlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2240 : Interval g6Atlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2272 : Interval g6Atlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2304 : Interval g6Atlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2336 : Interval g6Atlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2368 : Interval g6Atlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2400 : Interval g6Atlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2432 : Interval g6Atlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2464 : Interval g6Atlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2496 : Interval g6Atlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2528 : Interval g6Atlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2560 : Interval g6Atlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2592 : Interval g6Atlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2624 : Interval g6Atlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2656 : Interval g6Atlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2688 : Interval g6Atlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2720 : Interval g6Atlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2752 : Interval g6Atlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2784 : Interval g6Atlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2816 : Interval g6Atlas 6 2816 10 := block_range (n:=10) (by decide +kernel)
theorem all6_6 : Interval g6Atlas 6 0 2826 := (concat (concat (concat (concat (concat (concat b6_6_0 b6_6_32) (concat b6_6_64 (concat b6_6_96 b6_6_128))) (concat (concat b6_6_160 (concat b6_6_192 b6_6_224)) (concat b6_6_256 (concat b6_6_288 b6_6_320)))) (concat (concat (concat b6_6_352 b6_6_384) (concat b6_6_416 (concat b6_6_448 b6_6_480))) (concat (concat b6_6_512 (concat b6_6_544 b6_6_576)) (concat b6_6_608 (concat b6_6_640 b6_6_672))))) (concat (concat (concat (concat b6_6_704 b6_6_736) (concat b6_6_768 (concat b6_6_800 b6_6_832))) (concat (concat b6_6_864 (concat b6_6_896 b6_6_928)) (concat b6_6_960 (concat b6_6_992 b6_6_1024)))) (concat (concat (concat b6_6_1056 b6_6_1088) (concat b6_6_1120 (concat b6_6_1152 b6_6_1184))) (concat (concat b6_6_1216 (concat b6_6_1248 b6_6_1280)) (concat b6_6_1312 (concat b6_6_1344 b6_6_1376)))))) (concat (concat (concat (concat (concat b6_6_1408 b6_6_1440) (concat b6_6_1472 (concat b6_6_1504 b6_6_1536))) (concat (concat b6_6_1568 (concat b6_6_1600 b6_6_1632)) (concat b6_6_1664 (concat b6_6_1696 b6_6_1728)))) (concat (concat (concat b6_6_1760 b6_6_1792) (concat b6_6_1824 (concat b6_6_1856 b6_6_1888))) (concat (concat b6_6_1920 (concat b6_6_1952 b6_6_1984)) (concat b6_6_2016 (concat b6_6_2048 b6_6_2080))))) (concat (concat (concat (concat b6_6_2112 b6_6_2144) (concat b6_6_2176 (concat b6_6_2208 b6_6_2240))) (concat (concat b6_6_2272 (concat b6_6_2304 b6_6_2336)) (concat b6_6_2368 (concat b6_6_2400 b6_6_2432)))) (concat (concat (concat b6_6_2464 (concat b6_6_2496 b6_6_2528)) (concat b6_6_2560 (concat b6_6_2592 b6_6_2624))) (concat (concat b6_6_2656 (concat b6_6_2688 b6_6_2720)) (concat b6_6_2752 (concat b6_6_2784 b6_6_2816)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_0 : Interval g6Atlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_32 : Interval g6Atlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_64 : Interval g6Atlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_96 : Interval g6Atlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_128 : Interval g6Atlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_160 : Interval g6Atlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_192 : Interval g6Atlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_224 : Interval g6Atlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_256 : Interval g6Atlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_288 : Interval g6Atlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_320 : Interval g6Atlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_352 : Interval g6Atlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_384 : Interval g6Atlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_416 : Interval g6Atlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_448 : Interval g6Atlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_480 : Interval g6Atlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_512 : Interval g6Atlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_544 : Interval g6Atlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_576 : Interval g6Atlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_608 : Interval g6Atlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_640 : Interval g6Atlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_672 : Interval g6Atlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_704 : Interval g6Atlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_736 : Interval g6Atlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_768 : Interval g6Atlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_800 : Interval g6Atlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_832 : Interval g6Atlas 7 832 26 := block_range (n:=26) (by decide +kernel)
theorem all6_7 : Interval g6Atlas 7 0 858 := (concat (concat (concat (concat b6_7_0 (concat b6_7_32 b6_7_64)) (concat b6_7_96 (concat b6_7_128 b6_7_160))) (concat (concat b6_7_192 (concat b6_7_224 b6_7_256)) (concat (concat b6_7_288 b6_7_320) (concat b6_7_352 b6_7_384)))) (concat (concat (concat b6_7_416 (concat b6_7_448 b6_7_480)) (concat (concat b6_7_512 b6_7_544) (concat b6_7_576 b6_7_608))) (concat (concat b6_7_640 (concat b6_7_672 b6_7_704)) (concat (concat b6_7_736 b6_7_768) (concat b6_7_800 b6_7_832)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_8_0 : Interval g6Atlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_8_32 : Interval g6Atlas 8 32 3 := block_range (n:=3) (by decide +kernel)
theorem all6_8 : Interval g6Atlas 8 0 35 := (concat b6_8_0 b6_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_9_0 : Interval g6Atlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem all6_9 : Interval g6Atlas 9 0 1 := b6_9_0
theorem all6 : ∀ k ≤ 9, ∀ i < count g6Atlas k, checkRow g6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all6_2 i (by omega) hi
  · exact all6_3 i (by omega) hi
  · exact all6_4 i (by omega) hi
  · exact all6_5 i (by omega) hi
  · exact all6_6 i (by omega) hi
  · exact all6_7 i (by omega) hi
  · exact all6_8 i (by omega) hi
  · exact all6_9 i (by omega) hi
end PEqualNP.Outside.L_meta_28118
namespace PEqualNP.Outside.L_meta_28118
open PEqualNP.Outside.L_meta_28118.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem bound0 (cert : Complete g0Atlas) : Lower true (roots g0Atlas) (target g0Atlas) 7 := by
  have ready : Ready g0Atlas (asRow g0Pos) (asRow g0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 32, 36),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound1 (cert : Complete g1Atlas) : Lower true (roots g1Atlas) (target g1Atlas) 7 := by
  have ready : Ready g1Atlas (asRow g1Pos) (asRow g1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound2 (cert : Complete g2Atlas) : Lower true (roots g2Atlas) (target g2Atlas) 7 := by
  have ready : Ready g2Atlas (asRow g2Pos) (asRow g2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound3 (cert : Complete g3Atlas) : Lower true (roots g3Atlas) (target g3Atlas) 7 := by
  have ready : Ready g3Atlas (asRow g3Pos) (asRow g3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound4 (cert : Complete g4Atlas) : Lower true (roots g4Atlas) (target g4Atlas) 7 := by
  have ready : Ready g4Atlas (asRow g4Pos) (asRow g4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound5 (cert : Complete g5Atlas) : Lower true (roots g5Atlas) (target g5Atlas) 7 := by
  have ready : Ready g5Atlas (asRow g5Pos) (asRow g5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound6 (cert : Complete g6Atlas) (ss : ∀ v : Fin 6, Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD v.val zero)) 7) : Lower true (roots g6Atlas) (target g6Atlas) 10 := by
  have ready : Ready g6Atlas (asRow g6Pos) (asRow g6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip g6Atlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xffffffffffeeeea0fffefffaffeeeea0ffffffffffeeeea0fffefffaffeeeea0ffffffffffeeeea0fffefffaffeeeea0ffffffffffeeeea0fffefffaffeeeea0
theorem fullBound (cert0 : Complete g0Atlas) (cert1 : Complete g1Atlas) (cert2 : Complete g2Atlas) (cert3 : Complete g3Atlas) (cert4 : Complete g4Atlas) (cert5 : Complete g5Atlas) (cert6 : Complete g6Atlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 0 zero)) 7 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound0 cert0)
  have s1 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 1 zero)) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound1 cert1)
  have s2 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 2 zero)) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound2 cert2)
  have s3 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 3 zero)) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound3 cert3)
  have s4 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 4 zero)) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound4 cert4)
  have s5 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 5 zero)) 7 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound5 cert5)
  have allCuts : ∀ v : Fin 6, Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD v.val zero)) 7 := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := bound6 cert6 allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,32,96)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  exact lift
def roots8 : List Sig := [inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 1 zero,inputs.getD 0 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def word8 : Sig := 0xffffffffffffeeaaffffffffffffeeaaffffffffffeeeea0fffefffaffeeeea0ffffffffffffeeaaffffffffffffeeaaffffffffffeeeea0fffefffaffeeeea0
theorem liftFromL_meta_10856 : Lower true roots8 word8 12 := by
  have low := fullBound all0 all1 all2 all3 all4 all5 all6
  have h := lift_ok (u:=true) (ms:=fixRows 128 0) (raw:=roots8) (T:=word8)
    (xs:=[(inputs.getD 7 zero,1,129)]) (by decide +kernel)
    (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  exact h
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (roots8.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r word8 := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => roots8.getD i.val zero) = roots8 := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs roots8).getD o zero=word8 := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = roots8.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r roots8 (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true roots8 word8 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper word8 := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs roots8) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_28118.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 word8=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs roots8 legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : roots8.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (roots8.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.or,[5,7]⟩,⟨.or,[0,1]⟩,⟨.or,[3,5]⟩,⟨.or,[2,10]⟩,⟨.and,[12,9]⟩,⟨.or,[5,10]⟩,⟨.or,[4,14]⟩,⟨.and,[7,11]⟩,⟨.or,[13,8]⟩,⟨.or,[16,17]⟩,⟨.and,[6,15]⟩,⟨.or,[18,19]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
end PEqualNP.Outside.L_meta_28118

open PEqualNP.Outside.L_meta_28118 PEqualNP.Outside.L_meta_28118.Model PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_28118 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower liftFromL_meta_10856 gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,20,monoShape,by change 13 ≤ gs.length; omega,monoEval⟩
