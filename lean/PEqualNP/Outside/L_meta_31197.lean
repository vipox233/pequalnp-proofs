import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31197.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 256
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 8 => inputs.getD j.val zero) = inputs := rfl
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
  m == zero || m == d || pool.any (fun v => masked d v == m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => masked d v == c)))

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
  simp only [availableB,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
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
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

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
def fixRows (z o : Nat) : List Move :=
  (List.range 8).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 256 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 256 d)

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
  let rhs := c.bound + (z :: rest).countP (isMaskedConstant c.domain)
  if k + c.paid < rhs then
    let extra := !(availableB u c.domain c.wires z)
    ((k + c.paid + extra.toNat < rhs) &&
      rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)
  else false

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  unfold scalarPoolCut at cut
  dsimp only at cut
  split at cut
  · let extra := !(availableB u c.domain c.wires (choiceVal op))
    apply valid_exclude valid k rest op extra _ _ _ nd
    · simp only [Bool.and_eq_true, List.all_eq_true] at cut
      exact cut.1.2
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at cut
      cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at cut
      exact cut.1.1
  · contradiction

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
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[dbin ((bits >>> 10) &&& 3) a b])
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
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 8 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem input_coords : ∀ (j : Fin 8) (r : Row),
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 8) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 8 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<8 ∧ a=inputs.getD j zero := by
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
  let n := v.toNat % 1000000000000000003
  ((n*n % 1000000000000000003)*(n+7)+971*n) % 1000000000000000003
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
  by_cases hj : j<8
  · let i : Fin 8 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 256 ≤ 2^j := by
      change 2^8 ≤ 2^j
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

end PEqualNP.Outside.L_meta_31197.Model

namespace PEqualNP.Outside.L_meta_31197
open PEqualNP.Outside.L_meta_31197.Model
open PEqualNP.CircuitLowerBounds

def decodeBankChoices (n : Nat) (bits : Nat) (ws : List Decor) : List Decor × List Choice :=
  match n with
  | 0 => (ws, [])
  | k+1 =>
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    let op := (bits >>> 10) &&& 3
    let res := decodeBankChoices k (bits >>> 12) (ws ++ [dbin op a b])
    (res.1, (op, a.1, b.1) :: res.2)

theorem decodeBankChoices_fst (n bits : Nat) (ws : List Decor) :
    (decodeBankChoices n bits ws).1 = decodeBank n bits ws := by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeBankChoices, decodeBank]
    exact ih _ _

def autoPoolStep (u : Bool) (d : Sig) (budget : Nat) (paid : Nat) (pool : List Sig) : List Choice → Nat × List Sig
  | [] => (paid, pool)
  | c :: cs =>
    if paid < budget then
      if availableB u d pool (choiceVal c) then autoPoolStep u d budget paid pool cs
      else if choiceOK u d pool c then autoPoolStep u d budget (paid + 1) (choiceVal c :: pool) cs
      else (paid, pool)
    else (paid, pool)

theorem autoPoolStep_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank budget paid pool} (hp : Reach u roots paid bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) :
    ∃ next, Reach u roots (autoPoolStep u d budget paid pool cs).1 next ∧
      poolSupply u f next (autoPoolStep u d budget paid pool cs).2 := by
  induction cs generalizing bank paid pool with
  | nil => exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [autoPoolStep]
    split
    · split
      · exact ih hp hs
      · split
        next hok =>
          obtain ⟨next, hr, hs'⟩ := pay_choice dom hp hs c hok
          exact ih hr hs'
        next => exact ⟨bank, hp, hs⟩
    · exact ⟨bank, hp, hs⟩

def autoBoundPool (u : Bool) (raw : List Sig) (cs : List Choice) (budget : Nat) (spec : Sig × Nat) : BoundPool :=
  let res := autoPoolStep u spec.1 budget 0 raw cs
  ⟨spec.1, spec.2, res.1, res.2⟩

theorem autoBoundPool_valid {u raw T cs budget spec} (slice : Slice u raw T spec.1 spec.2) :
    ValidPool u raw T (autoBoundPool u raw cs budget spec) := by
  obtain ⟨f, roots, dom, base, nc, lo⟩ := slice
  obtain ⟨bank, hr, hs⟩ := autoPoolStep_sound dom (Reach.start (roots := roots.map observe)) base cs
  exact ⟨f, roots, bank, dom, nc, lo, hr, hs, trivial⟩

def activePools (u : Bool) (raw : List Sig) (cs : List Choice) (k : Nat) (vs : List Sig)
    (specs : List (Sig × Nat)) : List BoundPool :=
  specs.filterMap fun sp =>
    if k < sp.2 + vs.length + 2 then
      let lim := sp.2 + vs.countP (isMaskedConstant sp.1) + 2
      if k < lim then
        let bp := autoBoundPool u raw cs (lim - k) sp
        if k + bp.paid < lim then some bp else none
      else none
    else none

theorem activePools_valid {u raw T cs k vs specs}
    (h : ∀ sp ∈ specs, Slice u raw T sp.1 sp.2) :
    ∀ p ∈ activePools u raw cs k vs specs, ValidPool u raw T p := by
  intro p hp
  obtain ⟨sp, hsp, hsome⟩ := List.mem_filterMap.mp hp
  simp only at hsome
  split at hsome
  · split at hsome
    · split at hsome
      · cases hsome
        exact autoBoundPool_valid (h sp hsp)
      · contradiction
    · contradiction
  · contradiction

abbrev Atlas := Nat × List Decor × Sig × List (Sig × Nat) × List Move ×
  (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def slices (g : Atlas) := g.2.2.2.1
def mirror (g : Atlas) := g.2.2.2.2.1
def count (g : Atlas) := g.2.2.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.2

def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g - k
  let v := record g k i
  selectLive (v >>> (12 * d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) (mirror g) then ws.map (movedWord (mirror g).reverse) else ws

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
  let d := top g - k
  let v := record g k i
  let dc := decodeBankChoices d v (first g)
  let ws := selectLive (v >>> (12 * d)) dc.1
  let vs := ws.map Prod.fst
  let pools := activePools true (roots g) dc.2 k vs (slices g)
  decide vs.Nodup && !vs.contains (target g) &&
    testAll (k, ws.length, ws, preCov true ws, pools, links g (k - 1)) ws

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ sp ∈ slices g, Slice true (roots g) (target g) sp.1 sp.2

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow, decodeBankChoices_fst, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    by_cases hk : k = 0
    · subst k
      intro n cap run
      have : n = 0 := by omega
      subst n
      have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
      exact h.1.2 (List.mem_toFinset.mp hm)
    apply node_sound (raw := roots g) ready.1 _ h.1.1 h.1.2 (activePools_valid ready.2.2) _ h.2
    · intro a ha
      exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
    · intro tag xs hx
      simp only [links] at hx
      split at hx
      next le =>
        obtain rfl := List.mem_singleton.mp hx
        exact variant_ok (ih (k - 1) (by omega) (fun l hl => good l (by omega)) _ le) _
      next => simp at hx

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start + n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n = true) (i : Nat)
    (lo : start ≤ i) (hi : i < start + n) : test i = true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment, Bool.and_eq_true] at h
    by_cases eq : i = start + n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n = true) (i : Nat)
    (lo : a ≤ i) (hi : i < a + n) : checkRow g k i = true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start + n → checkRow g k i = true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a + m) n) :
    Interval g k a (m + n) := by
  intro i lo hi
  by_cases mid : i < a + m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true

theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs = true) (names : xs.map Prod.fst = roots g) :
    Lower true (roots g) (target g) (top g + 1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

end PEqualNP.Outside.L_meta_31197

namespace PEqualNP.Outside.L_meta_31197
open PEqualNP.Outside.L_meta_31197.Model
open PEqualNP.CircuitLowerBounds

def u0T : Sig := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def u1T : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def u2T : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def u3T : Sig := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def u4T : Sig := 0xffffffffcccccccccccccccc00000000ffffffffcccccccccccccccc00000000
def u5T : Sig := 0xffffffffaaaaaaaaaaaaaaaa00000000ffffffffaaaaaaaaaaaaaaaa00000000
def u6T : Sig := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def u7T : Sig := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def u8T : Sig := 0xffffffffffff0000ffff0000ffff0000ffffffffffff00000000000000000000
def u9T : Sig := 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0ffffffff00000000f0f0f0f000000000
def u10T : Sig := 0xffffffffffffffffffffffffffffffffffffffffcccccccccccccccc00000000
def u11T : Sig := 0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccc00000000
def u12T : Sig := 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000
def u13T : Sig := 0xffffff00ffffff00ffffff00ffffff00ffff0000ffff00000000000000000000
def u14T : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0ffff0000ffff00000000000000000000
def u15T : Sig := 0xffffffffffffffffffffffffffffffffffffccccffffcccccccc0000cccc0000
def u16T : Sig := 0xffffffffffffffffffffffffffffffffffffccccffffcccccccc0000cccc0000
def u17T : Sig := 0xffffccccffffccccffffccccffffccccffffccccffffcccccccc0000cccc0000
def u18T : Sig := 0xffffffffffffffffffffffffffffffffffffaaaaffffaaaaaaaa0000aaaa0000
def u19T : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaa0000aaaa0000
def u20T : Sig := 0xffccffccffccffccffccffccffccffcccccccccccccccccc0000000000000000
def u21T : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def u22T : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfccccccccccccccccc0000000000000000
def u23T : Sig := 0xfafafafafafafafafafafafafafafafaaaaaaaaaaaaaaaaa0000000000000000
def u24T : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f000000000f0f0f0f000000000
def u25T : Sig := 0xffffccccffffccccffffccccffffcccccccccccccccc0000cccccccccccc0000
def u26T : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def u27T : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaaaaaa00aa00aaaaaaaaaa00aa00
def u28T : Sig := 0xffffffccffffffccffffffccffffffcccccc0000cccc0000cccc0000cccc0000
def u29T : Sig := 0xffffffaaffffffaaffffffaaffffffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def u30T : Sig := 0xfffffcfcfffffcfcfffffcfcfffffcfccccc0000cccc0000cccc0000cccc0000
def u31T : Sig := 0xfffffafafffffafafffffafafffffafaaaaa0000aaaa0000aaaa0000aaaa0000
def u32T : Sig := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def u33T : Sig := 0xffeeffeeffeeffeeffeeffeeffeeffeeaa00aa00aa00aa00aa00aa00aa00aa00
def u34T : Sig := 0xffffffffffff0000f0f0f0f000000000ffffffffffff0000f0f0f0f000000000
def u35T : Sig := 0xffffffffffff0000f0f0f0f000000000ffffffffffff0000f0f0f0f000000000
def u36T : Sig := 0xffffffffffffccccffffffffcccc0000ffffffffffffccccffffffffcccc0000
def u37T : Sig := 0xffffffffffffcccccccccccccccc0000ffffffffffffcccccccccccccccc0000
def u38T : Sig := 0xffffffffffffaaaaaaaaaaaaaaaa0000ffffffffffffaaaaaaaaaaaaaaaa0000
def u39T : Sig := 0xffffffffaaaaaaaaaaaaaaaaaa00aa00ffffffffaaaaaaaaaaaaaaaaaa00aa00
def u40T : Sig := 0xffffffffccccccccfcfcfcfc00000000ffffffffccccccccfcfcfcfc00000000
def u41T : Sig := 0xffffaaaaffffaaaaaaaaaa00aaaaaa00ffffaaaaffffaaaaaaaaaa00aaaaaa00
def u42T : Sig := 0xffffaaaaffffaaaaaaaaaa00aaaaaa00ffffaaaaffffaaaaaaaaaa00aaaaaa00
def u43T : Sig := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def u44T : Sig := 0xffffaaaaffffaaaaaaaa0000aaaa0000ffffaaaaffffaaaaaaaa0000aaaa0000
def u45T : Sig := 0xeeeeeeeeeeeeeeeeaa00aa00aa00aa00eeeeeeeeeeeeeeeeaa00aa00aa00aa00
def u46T : Sig := 0xeeeeeeeeeeeeeeeeaa00aa00aa00aa00eeeeeeeeeeeeeeeeaa00aa00aa00aa00
def u47T : Sig := 0xfcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000
def u48T : Sig := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00
def u49T : Sig := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00
def u50T : Sig := 0xffffffffffffff00ffffff00ffffff00ffffffffffff00000000000000000000
def u51T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffff0000f0f0f0f000000000
def u52T : Sig := 0xfffffffffffff0f0fffff0f0fffff0f0ffffffffffff0000f0f0f0f000000000
def u53T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffcccc0000
def u54T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc0000
def u55T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffcccc0000
def u56T : Sig := 0xffffffffffffccccffffccccffffccccffffffffffffcccccccccccccccc0000
def u57T : Sig := 0xffffffffffffaaaaffffaaaaffffaaaaffffffffffffaaaaaaaaaaaaaaaa0000
def u58T : Sig := 0xffffffffffaaffaaffaaffaaffaaffaaffffffffaaaaaaaaaaaaaaaaaa00aa00
def u59T : Sig := 0xffffffffffffffffffffffffffffffffffffffffccccccccfcfcfcfc00000000
def u60T : Sig := 0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcffffffffccccccccfcfcfcfc00000000
def u61T : Sig := 0xfffffff0fffffff0fffffff0fffffff0ffff0000ffff00000000000000000000
def u62T : Sig := 0xffffffffffffffffffffffffffffffffffffccccffffcccccccc0000cccc0000
def u63T : Sig := 0xffffffccffffffccffffffccffffffccffffccccffffcccccccc0000cccc0000
def u64T : Sig := 0xffffffffffffffffffffffffffffffffffffaaaaffffaaaaaaaaaa00aaaaaa00
def u65T : Sig := 0xffffffaaffffffaaffffffaaffffffaaffffaaaaffffaaaaaaaaaa00aaaaaa00
def u66T : Sig := 0xffffffffffffffffffffffffffffffffffffccccffffcccccccc0000cccc0000
def u67T : Sig := 0xfffffcfcfffffcfcfffffcfcfffffcfcffffccccffffcccccccc0000cccc0000
def u68T : Sig := 0xfffffafafffffafafffffafafffffafaffffaaaaffffaaaaaaaa0000aaaa0000
def u69T : Sig := 0xffffffffffffffffffffffffffffffffffffeeeeffffeeeeeeeeaaaaeeeeaaaa
def u70T : Sig := 0xffffffffffffffffffffffffffffffffffffeeeeffffeeeeeeeeaaaaeeeeaaaa
def u71T : Sig := 0xffffffffffffffffffffffffffffffffffffeeeeffffeeeeeeee0000eeee0000
def u72T : Sig := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeeeee0000eeee0000
def u73T : Sig := 0xfffcfffcfffcfffcfffcfffcfffcfffccccccccccccccccc0000000000000000
def u74T : Sig := 0xfffafffafffafffafffafffafffafffaaaaaaaaaaaaaaaaaaa00aa00aa00aa00
def u75T : Sig := 0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeaa00aa00aa00aa00
def u76T : Sig := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeeeeeeeeeeeeeeeaa00aa00aa00aa00
def u77T : Sig := 0xfefefefefefefefefefefefefefefefeeeeeeeeeeeeeeeee0000000000000000
def u78T : Sig := 0xffffffaaffffffaaffffffaaffffffaaaaaaaaaaaaaaaa00aaaaaaaaaaaaaa00
def u79T : Sig := 0xfffffcfcfffffcfcfffffcfcfffffcfcfcfcfcfccccc0000fcfcfcfccccc0000
def u80T : Sig := 0xfffffffcfffffffcfffffffcfffffffccccc0000cccc0000cccc0000cccc0000
def u81T : Sig := 0xfffffffafffffffafffffffafffffffaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def u82T : Sig := 0xffffffffffffffffffffffffffffffffeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def u83T : Sig := 0xffffffeeffffffeeffffffeeffffffeeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def u84T : Sig := 0xfffffefefffffefefffffefefffffefeeeee0000eeee0000eeee0000eeee0000
def u85T : Sig := 0xfffefffefffefffefffefffefffefffeaa00aa00aa00aa00aa00aa00aa00aa00
def u86T : Sig := 0xffffffffffffaaaaaaaaaaaaaaaaaa00ffffffffffffaaaaaaaaaaaaaaaaaa00
def u87T : Sig := 0xffffffffffffccccfcfcfcfccccc0000ffffffffffffccccfcfcfcfccccc0000
def u88T : Sig := 0xffffffffffffccccfcfcfcfccccc0000ffffffffffffccccfcfcfcfccccc0000
def u89T : Sig := 0xffffffffffffaaaafafafafaaaaa0000ffffffffffffaaaafafafafaaaaa0000
def u90T : Sig := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def u91T : Sig := 0xffffaaaaffffaaaaaaaaaa00aaaaaa00ffffaaaaffffaaaaaaaaaa00aaaaaa00
def u92T : Sig := 0xffffeeeeffffeeeeeeeeaa00eeeeaa00ffffeeeeffffeeeeeeeeaa00eeeeaa00
def u93T : Sig := 0xffffeeeeffffeeeeeeeeaa00eeeeaa00ffffeeeeffffeeeeeeeeaa00eeeeaa00
def u94T : Sig := 0xffffeeeeffffeeeeeeeeaaaaeeeeaaaaffffeeeeffffeeeeeeeeaaaaeeeeaaaa
def u95T : Sig := 0xffffeeeeffffeeeeeeee0000eeee0000ffffeeeeffffeeeeeeee0000eeee0000
def u96T : Sig := 0xfafafafaaaaaaa00fafafafaaaaaaa00fafafafaaaaaaa00fafafafaaaaaaa00
def u97T : Sig := 0xffffffffeeeeaa00ffffffffeeeeaa00ffffffffeeeeaa00ffffffffeeeeaa00
def u98T : Sig := 0xeeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00eeeeeeeeeeeeaa00
def u99T : Sig := 0xfefefefeeeeeaaaafefefefeeeeeaaaafefefefeeeeeaaaafefefefeeeeeaaaa
def u100T : Sig := 0xfefefefeeeee0000fefefefeeeee0000fefefefeeeee0000fefefefeeeee0000
def u101T : Sig := 0xfefefefeaa00aa00fefefefeaa00aa00fefefefeaa00aa00fefefefeaa00aa00
def u102T : Sig := 0xffffffffffffffaaffffffaaffffffaaffffffffffffaaaaaaaaaaaaaaaaaa00
def u103T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffccccfcfcfcfccccc0000
def u104T : Sig := 0xfffffffffffffcfcfffffcfcfffffcfcffffffffffffccccfcfcfcfccccc0000
def u105T : Sig := 0xfffffffcfffffffcfffffffcfffffffcffffccccffffcccccccc0000cccc0000
def u106T : Sig := 0xfffffffafffffffafffffffafffffffaffffaaaaffffaaaaaaaaaa00aaaaaa00
def u107T : Sig := 0xffffffffffffffffffffffffffffffffffffeeeeffffeeeeeeeeaa00eeeeaa00
def u108T : Sig := 0xffffffeeffffffeeffffffeeffffffeeffffeeeeffffeeeeeeeeaa00eeeeaa00
def u109T : Sig := 0xfffffefefffffefefffffefefffffefeffffeeeeffffeeeeeeee0000eeee0000
def u110T : Sig := 0xfffefffefffefffefffefffefffefffeeeeeeeeeeeeeeeeeaa00aa00aa00aa00
def u111T : Sig := 0xfffefffefffefffefffefffefffefffefefefefeaa00aa00fefefefeaa00aa00
def u112T : Sig := 0xfffffffefffffffefffffffefffffffeeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def u113T : Sig := 0xffffffffffffaaaafafafafaaaaaaa00ffffffffffffaaaafafafafaaaaaaa00
def u114T : Sig := 0xffffffffffffeeeeffffffffeeeeaa00ffffffffffffeeeeffffffffeeeeaa00
def u115T : Sig := 0xffffffffffffeeeeeeeeeeeeeeeeaa00ffffffffffffeeeeeeeeeeeeeeeeaa00
def u116T : Sig := 0xffffffffffffeeeefefefefeeeeeaaaaffffffffffffeeeefefefefeeeeeaaaa
def u117T : Sig := 0xffffffffffffeeeefefefefeeeee0000ffffffffffffeeeefefefefeeeee0000
def u118T : Sig := 0xffffffffeeeeeeeefefefefeaa00aa00ffffffffeeeeeeeefefefefeaa00aa00
def u119T : Sig := 0xfefefefeeeeeaa00fefefefeeeeeaa00fefefefeeeeeaa00fefefefeeeeeaa00
def u120T : Sig := 0xfffffffffffffffcfffffffcfffffffcffffffffffffccccfcfcfcfccccc0000
def u121T : Sig := 0xfffffffffffffffafffffffafffffffaffffffffffffaaaafafafafaaaaaaa00
def u122T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffeeeeffffffffeeeeaa00
def u123T : Sig := 0xffffffffffffffeeffffffeeffffffeeffffffffffffeeeeeeeeeeeeeeeeaa00
def u124T : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffeeeefefefefeeeeeaaaa
def u125T : Sig := 0xfffffffffffffefefffffefefffffefeffffffffffffeeeefefefefeeeee0000
def u126T : Sig := 0xfffffffffffefffefffefffefffefffeffffffffeeeeeeeefefefefeaa00aa00
def u127T : Sig := 0xfffffffefffffffefffffffefffffffeffffeeeeffffeeeeeeeeaa00eeeeaa00
def u128T : Sig := 0xfffffffefffffffefffffffefffffffefefefefeeeeeaa00fefefefeeeeeaa00
def u129T : Sig := 0xffffffffffffeeeefefefefeeeeeaa00ffffffffffffeeeefefefefeeeeeaa00
def u130T : Sig := 0xfffffffffffffffefffffffefffffffeffffffffffffeeeefefefefeeeeeaa00

def u0K3 : Nat → Nat
  | 0 => 0x227
  | _ => 0
def u0N : Nat → Nat
  | 3 => 1
  | _ => 0
def u0R : Nat → Nat → Nat
  | 3, i => packedAt u0K3 (i * 3) 3
  | _, _ => 0
def u0I : Nat → Nat → Nat
  | 3, h => packedAt u0K3 (4 + ((h / 1 + packedAt u0K3 (3 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u0Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffffffffffffffecf
  | 4 => 0xffffffffffffffffffffffffffffffffffff73
  | 7 => 0x1bc
  | _ => 0
def u0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffff05
  | 4 => 0x92
  | 7 => 0x68
  | _ => 0
def u0Slices : List (Sig × Nat) := []
def u0Atlas : Atlas := ⟨3, rawDecor 146 u0Pos u0Neg, u0T, u0Slices, [swapRows 116], u0N, u0R, u0I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u0_3_0 : Interval u0Atlas 3 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u0_3 : Interval u0Atlas 3 0 1 := blk_u0_3_0
theorem cert_u0 : Complete u0Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u0_3 i (by omega) hi
theorem b_u0 : Lower true (vars 146) u0T 4 := by
  have ready : Ready u0Atlas (asRow u0Pos) (asRow u0Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u0Atlas, u0Slices, List.not_mem_nil] at hsp
  exact frozen ready cert_u0 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,2,18),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u1 : Lower true (vars 145) u1T 4 :=
  lower_map (ms := [swapRows 16]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u2 : Lower true (vars 137) u2T 4 :=
  lower_map (ms := [swapRows 16,swapRows 67]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u3 : Lower true (vars 98) u3T 4 :=
  lower_map (ms := [swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u4 : Lower true (vars 98) u4T 4 :=
  lower_map (ms := [swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u5 : Lower true (vars 97) u5T 4 :=
  lower_map (ms := [swapRows 16,swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u6 : Lower true (vars 82) u6T 4 :=
  lower_map (ms := [swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u7 : Lower true (vars 82) u7T 4 :=
  lower_map (ms := [swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
def u8K3 : Nat → Nat
  | 0 => 0x14f
  | _ => 0
def u8N : Nat → Nat
  | 3 => 1
  | _ => 0
def u8R : Nat → Nat → Nat
  | 3, i => packedAt u8K3 (i * 4) 4
  | _, _ => 0
def u8I : Nat → Nat → Nat
  | 3, h => packedAt u8K3 (5 + ((h / 1 + packedAt u8K3 (4 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u8Pos : Nat → Bits
  | 4 => 0xfffffffffffffffffffffffffffffffffe33f3
  | 5 => 0x1cd9c
  | 6 => 0xfffffffffffffffffffffffffffffffff1fe1f
  | 7 => 0xe0fe0
  | _ => 0
def u8Neg : Nat → Bits
  | 4 => 0xffffffffffffffffffffffffffffffffe250b1
  | 5 => 0x16d594
  | 6 => 0x92a0a
  | 7 => 0x1daf40
  | _ => 0
def u8Slices : List (Sig × Nat) := []
def u8Atlas : Atlas := ⟨3, rawDecor 240 u8Pos u8Neg, u8T, u8Slices, [swapRows 100,swapRows 117], u8N, u8R, u8I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u8_3_0 : Interval u8Atlas 3 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u8_3 : Interval u8Atlas 3 0 1 := blk_u8_3_0
theorem cert_u8 : Complete u8Atlas := by
  intro k hk i hi
  change k ≤ 3 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u8_3 i (by omega) hi
theorem b_u8 : Lower true (vars 240) u8T 4 := by
  have ready : Ready u8Atlas (asRow u8Pos) (asRow u8Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u8Atlas, u8Slices, List.not_mem_nil] at hsp
  exact frozen ready cert_u8 (by decide +kernel) (by decide) [(inputs.getD 4 zero,64,80),(inputs.getD 5 zero,64,96),(inputs.getD 6 zero,16,80),(inputs.getD 7 zero,16,144)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u9 : Lower true (vars 228) u9T 4 :=
  lower_map (ms := [swapRows 66,swapRows 67,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u10 : Lower true (vars 226) u10T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 128 0) (raw := vars 226) (T := u10T) (xs := [(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u3
  have hc : (([(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u11 : Lower true (vars 226) u11T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 128 0) (raw := vars 226) (T := u11T) (xs := [(inputs.getD 7 zero,2,130)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u4
  have hc : (([(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u12 : Lower true (vars 225) u12T 5 :=
  lower_map (ms := [swapRows 16]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u13 : Lower true (vars 216) u13T 4 :=
  lower_map (ms := [swapRows 83,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u14 : Lower true (vars 212) u14T 4 :=
  lower_map (ms := [swapRows 82,swapRows 83,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u15 : Lower true (vars 210) u15T 5 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u10
theorem b_u16 : Lower true (vars 210) u16T 5 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u10
theorem b_u17 : Lower true (vars 210) u17T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 64 0) (raw := vars 210) (T := u17T) (xs := [(inputs.getD 6 zero,2,66)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u0
  have hc : (([(inputs.getD 6 zero,2,66)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u18 : Lower true (vars 209) u18T 5 :=
  lower_map (ms := [swapRows 16,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u10
theorem b_u19 : Lower true (vars 209) u19T 5 :=
  lower_map (ms := [swapRows 16]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
theorem b_u20 : Lower true (vars 202) u20T 4 :=
  lower_map (ms := [swapRows 65,swapRows 66,swapRows 83,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u21 : Lower true (vars 201) u21T 5 :=
  lower_map (ms := [swapRows 16,swapRows 83,swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u22 : Lower true (vars 198) u22T 4 :=
  lower_map (ms := [swapRows 65,swapRows 82,swapRows 67,swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u23 : Lower true (vars 197) u23T 4 :=
  lower_map (ms := [swapRows 64,swapRows 65,swapRows 82,swapRows 67,swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u24 : Lower true (vars 180) u24T 4 :=
  lower_map (ms := [swapRows 66,swapRows 67,swapRows 84,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u25 : Lower true (vars 178) u25T 5 :=
  lower_map (ms := [swapRows 84,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u26 : Lower true (vars 177) u26T 5 :=
  lower_map (ms := [swapRows 16,swapRows 84,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u27 : Lower true (vars 169) u27T 5 :=
  lower_map (ms := [swapRows 16,swapRows 83,swapRows 84,swapRows 117,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u28 : Lower true (vars 154) u28T 5 :=
  lower_map (ms := [swapRows 81,swapRows 115,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u29 : Lower true (vars 153) u29T 5 :=
  lower_map (ms := [swapRows 16,swapRows 99,swapRows 116,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
theorem b_u30 : Lower true (vars 150) u30T 5 :=
  lower_map (ms := [swapRows 81,swapRows 114,swapRows 115,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u31 : Lower true (vars 149) u31T 5 :=
  lower_map (ms := [swapRows 80,swapRows 81,swapRows 114,swapRows 115,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u32 : Lower true (vars 141) u32T 5 :=
  lower_map (ms := [swapRows 80,swapRows 81,swapRows 114,swapRows 99,swapRows 116,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u33 : Lower true (vars 139) u33T 5 :=
  lower_map (ms := [swapRows 80,swapRows 113,swapRows 82,swapRows 99,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u34 : Lower true (vars 116) u34T 4 :=
  lower_map (ms := [swapRows 82,swapRows 83,swapRows 116,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u35 : Lower true (vars 116) u35T 4 :=
  lower_map (ms := [swapRows 82,swapRows 83,swapRows 116,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u36 : Lower true (vars 114) u36T 5 :=
  lower_map (ms := [swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u10
theorem b_u37 : Lower true (vars 114) u37T 5 :=
  lower_map (ms := [swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
theorem b_u38 : Lower true (vars 113) u38T 5 :=
  lower_map (ms := [swapRows 16,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
theorem b_u39 : Lower true (vars 105) u39T 5 :=
  lower_map (ms := [swapRows 16,swapRows 115,swapRows 116]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u40 : Lower true (vars 102) u40T 5 :=
  lower_map (ms := [swapRows 81,swapRows 114,swapRows 115,swapRows 116]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u41 : Lower true (vars 89) u41T 5 :=
  lower_map (ms := [swapRows 16,swapRows 115,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u42 : Lower true (vars 89) u42T 5 :=
  lower_map (ms := [swapRows 16,swapRows 115,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u43 : Lower true (vars 82) u43T 4 :=
  lower_map (ms := [swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u44 : Lower true (vars 81) u44T 4 :=
  lower_map (ms := [swapRows 16,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u45 : Lower true (vars 75) u45T 4 :=
  lower_map (ms := [swapRows 64,swapRows 81,swapRows 66,swapRows 115,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u46 : Lower true (vars 75) u46T 4 :=
  lower_map (ms := [swapRows 64,swapRows 81,swapRows 66,swapRows 115,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u47 : Lower true (vars 54) u47T 4 :=
  lower_map (ms := [swapRows 65,swapRows 82,swapRows 67,swapRows 116,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u48 : Lower true (vars 27) u48T 4 :=
  lower_map (ms := [swapRows 64,swapRows 81,swapRows 66,swapRows 115,swapRows 100]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u49 : Lower true (vars 27) u49T 4 :=
  lower_map (ms := [swapRows 64,swapRows 81,swapRows 66,swapRows 115,swapRows 100]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
theorem b_u50 : Lower true (vars 248) u50T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := vars 248) (T := u50T) (xs := [(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u8
  have hc : (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u51 : Lower true (vars 244) u51T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 128 0) (raw := vars 244) (T := u51T) (xs := [(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u34
  have hc : (([(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u52K4 : Nat → Nat
  | 0 => 0x118a38d807599858e986f402a415e005482af0ca8835c1951067c42a104f085420
  | _ => 0
def u52K5 : Nat → Nat
  | 0 => 0x1999999999999991999599999999859981892d98399878b999820fd20bf481fd187f441fd103f420
  | _ => 0
def u52K6 : Nat → Nat
  | 0 => 0x89f
  | _ => 0
def u52N : Nat → Nat
  | 4 => 6
  | 5 => 6
  | 6 => 1
  | _ => 0
def u52R : Nat → Nat → Nat
  | 4, i => packedAt u52K4 (i * 31) 31
  | 5, i => packedAt u52K5 (i * 18) 18
  | 6, i => packedAt u52K6 (i * 5) 5
  | _, _ => 0
def u52I : Nat → Nat → Nat
  | 4, h => packedAt u52K4 (189 + ((h / 3 + packedAt u52K4 (186 + (h % 3) * 1) 1) % 18) * 4) 4
  | 5, h => packedAt u52K5 (117 + ((h / 3 + packedAt u52K5 (108 + (h % 3) * 3) 3) % 50) * 4) 4
  | 6, h => packedAt u52K6 (6 + ((h / 1 + packedAt u52K6 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u52Pos : Nat → Bits
  | 2 => 0xfffffffffffffffffffffffffd21e01e3334cf
  | 4 => 0x25e01e04dc8fc
  | 5 => 0xfffffffffffffffffffffffffca01e1f8e0f0f
  | 6 => 0xc01fe1f00ff0
  | 7 => 0x31fe001fff000
  | _ => 0
def u52Neg : Nat → Bits
  | 2 => 0xfffffffffffffffffffffffffe8264aa1114c5
  | 4 => 0x186226605485c
  | 5 => 0x14c8a548e090a
  | 6 => 0x23155897006a0
  | 7 => 0x799911eaa000
  | _ => 0
def u52Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,4),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,4),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,4),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,4)]
def u52Atlas : Atlas := ⟨6, rawDecor 244 u52Pos u52Neg, u52T, u52Slices, [swapRows 100,swapRows 117], u52N, u52R, u52I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u52_4_0 : Interval u52Atlas 4 0 6 := block_range (n := 6) (by decide +kernel)
theorem all_u52_4 : Interval u52Atlas 4 0 6 := blk_u52_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u52_5_0 : Interval u52Atlas 5 0 6 := block_range (n := 6) (by decide +kernel)
theorem all_u52_5 : Interval u52Atlas 5 0 6 := blk_u52_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u52_6_0 : Interval u52Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u52_6 : Interval u52Atlas 6 0 1 := blk_u52_6_0
theorem cert_u52 : Complete u52Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u52_4 i (by omega) hi
  · exact all_u52_5 i (by omega) hi
  · exact all_u52_6 i (by omega) hi
theorem b_u52 : Lower true (vars 244) u52T 7 := by
  have ready : Ready u52Atlas (asRow u52Pos) (asRow u52Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u52Atlas, u52Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u35
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u24
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u9
  exact frozen ready cert_u52 (by decide +kernel) (by decide) [(inputs.getD 2 zero,32,36),(inputs.getD 4 zero,64,80),(inputs.getD 5 zero,4,36),(inputs.getD 6 zero,16,80),(inputs.getD 7 zero,4,132)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u53 : Lower true (vars 242) u53T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 160 0) (raw := vars 242) (T := u53T) (xs := [(inputs.getD 5 zero,0,32),(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u6
  have hc : (([(inputs.getD 5 zero,0,32),(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u54 : Lower true (vars 242) u54T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 144 0) (raw := vars 242) (T := u54T) (xs := [(inputs.getD 4 zero,2,18),(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u3
  have hc : (([(inputs.getD 4 zero,2,18),(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u55 : Lower true (vars 242) u55T 6 :=
  lower_map (ms := []) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u53
def u56K6 : Nat → Nat
  | 0 => 0xa1f
  | _ => 0
def u56N : Nat → Nat
  | 6 => 1
  | _ => 0
def u56R : Nat → Nat → Nat
  | 6, i => packedAt u56K6 (i * 5) 5
  | _, _ => 0
def u56I : Nat → Nat → Nat
  | 6, h => packedAt u56K6 (6 + ((h / 1 + packedAt u56K6 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u56Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffff7d3e30789307f
  | 4 => 0xffffffffffffffffffffffffe8e47c1896c993
  | 5 => 0x10880e3670e1c
  | 6 => 0xe0f00fc780fe0
  | 7 => 0x10301f007ff000
  | _ => 0
def u56Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffe02c0000001025
  | 4 => 0x12110429824892
  | 5 => 0x1e420d6ba70a18
  | 6 => 0x180b294580540
  | 7 => 0xdc05bd67da000
  | _ => 0
def u56Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,5),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,5),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,5),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,5)]
def u56Atlas : Atlas := ⟨6, rawDecor 242 u56Pos u56Neg, u56T, u56Slices, [swapRows 100,swapRows 117], u56N, u56R, u56I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u56_6_0 : Interval u56Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u56_6 : Interval u56Atlas 6 0 1 := blk_u56_6_0
theorem cert_u56 : Complete u56Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u56_6 i (by omega) hi
theorem b_u56 : Lower true (vars 242) u56T 7 := by
  have ready : Ready u56Atlas (asRow u56Pos) (asRow u56Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u56Atlas, u56Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u37
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u25
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
  exact frozen ready cert_u56 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 4 zero,2,18),(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u57 : Lower true (vars 241) u57T 7 :=
  lower_map (ms := [swapRows 16]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u56
def u58K4 : Nat → Nat
  | 0 => 0x38982e2eb56312c6118c0b0da63188e303c01353e1f0c602664f16c86100974660054829d4260054828f48600544197466005441978664458809d8264858408f886425840978664854409d826485440978664458208f88644542097866445420
  | _ => 0
def u58K5 : Nat → Nat
  | 0 => 0x737e383c76c93e5af0f5a093709b7d579d9d1acb997527407483046b46f074575d2ab552a3d29d0c2f413b17461e1dd1f4d7410800218008a5078001063006df805482be00a9057e015106f802a20df445880de904901be215202fc22a407d825480bb04a9017e216102fa42c205f425840f6904881ed105102fc42a205f485440ef0ca8815e195103dc22a205f825440bf08b0417d116083ea20a106f8854209f10a8417e115082fa22a107d825420
  | _ => 0
def u58K6 : Nat → Nat
  | 0 => 0x8f06420f228d0680b08220e70fd20bf441fe203f480fe103f440fe083f420
  | _ => 0
def u58K7 : Nat → Nat
  | 0 => 0xa1f
  | _ => 0
def u58N : Nat → Nat
  | 4 => 12
  | 5 => 29
  | 6 => 8
  | 7 => 1
  | _ => 0
def u58R : Nat → Nat → Nat
  | 4, i => packedAt u58K4 (i * 44) 44
  | 5, i => packedAt u58K5 (i * 31) 31
  | 6, i => packedAt u58K6 (i * 18) 18
  | 7, i => packedAt u58K7 (i * 5) 5
  | _, _ => 0
def u58I : Nat → Nat → Nat
  | 4, h => packedAt u58K4 (552 + ((h / 8 + packedAt u58K4 (528 + (h % 8) * 3) 3) % 43) * 5) 5
  | 5, h => packedAt u58K5 (1001 + ((h / 17 + packedAt u58K5 (899 + (h % 17) * 6) 6) % 67) * 6) 6
  | 6, h => packedAt u58K6 (152 + ((h / 4 + packedAt u58K6 (144 + (h % 4) * 2) 2) % 19) * 5) 5
  | 7, h => packedAt u58K7 (6 + ((h / 1 + packedAt u58K7 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u58Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffd70c3f0930ff
  | 3 => 0xffffffffffffffffffffffffc0e1f00336cc93
  | 5 => 0x30a03ccc70f1c
  | 6 => 0xc0c03f0f80fe0
  | 7 => 0x3030fc00fff000
  | _ => 0
def u58Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffc0280000001025
  | 3 => 0x351030d7124c92
  | 5 => 0x1c44554d470518
  | 6 => 0x2382aab2b80ac0
  | 7 => 0xac1cf28eda000
  | _ => 0
def u58Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,5),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,5),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,5),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,5),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,4),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,4)]
def u58Atlas : Atlas := ⟨7, rawDecor 233 u58Pos u58Neg, u58T, u58Slices, [swapRows 101], u58N, u58R, u58I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u58_4_0 : Interval u58Atlas 4 0 12 := block_range (n := 12) (by decide +kernel)
theorem all_u58_4 : Interval u58Atlas 4 0 12 := blk_u58_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u58_5_0 : Interval u58Atlas 5 0 29 := block_range (n := 29) (by decide +kernel)
theorem all_u58_5 : Interval u58Atlas 5 0 29 := blk_u58_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u58_6_0 : Interval u58Atlas 6 0 8 := block_range (n := 8) (by decide +kernel)
theorem all_u58_6 : Interval u58Atlas 6 0 8 := blk_u58_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u58_7_0 : Interval u58Atlas 7 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u58_7 : Interval u58Atlas 7 0 1 := blk_u58_7_0
theorem cert_u58 : Complete u58Atlas := by
  intro k hk i hi
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u58_4 i (by omega) hi
  · exact all_u58_5 i (by omega) hi
  · exact all_u58_6 i (by omega) hi
  · exact all_u58_7 i (by omega) hi
theorem b_u58 : Lower true (vars 233) u58T 8 := by
  have ready : Ready u58Atlas (asRow u58Pos) (asRow u58Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u58Atlas, u58Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u39
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u27
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 96 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u2
    · exact slice_correct (ms := fixRows 136 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u5
  exact frozen ready cert_u58 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u59 : Lower true (vars 230) u59T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 132 0) (raw := vars 230) (T := u59T) (xs := [(inputs.getD 2 zero,32,36),(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u3
  have hc : (([(inputs.getD 2 zero,32,36),(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u60 : Lower true (vars 230) u60T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 132 0) (raw := vars 230) (T := u60T) (xs := [(inputs.getD 2 zero,32,36),(inputs.getD 7 zero,2,130)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u4
  have hc : (([(inputs.getD 2 zero,32,36),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u61 : Lower true (vars 220) u61T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 220) (T := u61T) (xs := [(inputs.getD 2 zero,128,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u13
  have hc : (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u62 : Lower true (vars 210) u62T 5 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u10
def u63K4 : Nat → Nat
  | 0 => 0x2857865440
  | _ => 0
def u63K5 : Nat → Nat
  | 0 => 0x53f440
  | _ => 0
def u63K6 : Nat → Nat
  | 0 => 0x89f
  | _ => 0
def u63N : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0
def u63R : Nat → Nat → Nat
  | 4, i => packedAt u63K4 (i * 31) 31
  | 5, i => packedAt u63K5 (i * 18) 18
  | 6, i => packedAt u63K6 (i * 5) 5
  | _, _ => 0
def u63I : Nat → Nat → Nat
  | 4, h => packedAt u63K4 (32 + ((h / 1 + packedAt u63K4 (31 + (h % 1) * 1) 1) % 3) * 2) 2
  | 5, h => packedAt u63K5 (19 + ((h / 1 + packedAt u63K5 (18 + (h % 1) * 1) 1) % 3) * 2) 2
  | 6, h => packedAt u63K6 (6 + ((h / 1 + packedAt u63K6 (5 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u63Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffe6e9f031f1130ff
  | 3 => 0x543c0069cccc
  | 4 => 0xffffffffffffffffffffffff9767c0e38e0f0f
  | 6 => 0x187800fcf00ff0
  | 7 => 0x1e180ff00fff000
  | _ => 0
def u63Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffe91600505011055
  | 3 => 0x1fa545d6f294ccc
  | 4 => 0x289848220a050a
  | 6 => 0x14605b2d8f00aa0
  | 7 => 0x402a290d4a000
  | _ => 0
def u63Slices : List (Sig × Nat) := [(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,5),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,5),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,5),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,4),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,4),(0x3333333333333333333333333333333333333333333333333333333333333333,4)]
def u63Atlas : Atlas := ⟨6, rawDecor 218 u63Pos u63Neg, u63T, u63Slices, [swapRows 65], u63N, u63R, u63I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u63_4_0 : Interval u63Atlas 4 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u63_4 : Interval u63Atlas 4 0 1 := blk_u63_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u63_5_0 : Interval u63Atlas 5 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u63_5 : Interval u63Atlas 5 0 1 := blk_u63_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u63_6_0 : Interval u63Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u63_6 : Interval u63Atlas 6 0 1 := blk_u63_6_0
theorem cert_u63 : Complete u63Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u63_4 i (by omega) hi
  · exact all_u63_5 i (by omega) hi
  · exact all_u63_6 i (by omega) hi
theorem b_u63 : Lower true (vars 218) u63T 7 := by
  have ready : Ready u63Atlas (asRow u63Pos) (asRow u63Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u63Atlas, u63Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u28
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
    · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u15
    · exact slice_correct (ms := fixRows 136 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u7
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u20
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u13
  exact frozen ready cert_u63 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,128,136),(inputs.getD 4 zero,2,18),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u64 : Lower true (vars 217) u64T 6 :=
  lower_map (ms := [swapRows 80,swapRows 81,swapRows 50,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u59
theorem b_u65 : Lower true (vars 217) u65T 7 :=
  lower_map (ms := [swapRows 16,swapRows 83,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u56
theorem b_u66 : Lower true (vars 210) u66T 5 :=
  lower_map (ms := [swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u10
theorem b_u67 : Lower true (vars 214) u67T 7 :=
  lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u68 : Lower true (vars 213) u68T 7 :=
  lower_map (ms := [swapRows 16,swapRows 50]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u69 : Lower true (vars 211) u69T 6 :=
  lower_map (ms := [swapRows 80,swapRows 82,swapRows 83]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u53
theorem b_u70 : Lower true (vars 211) u70T 6 :=
  lower_map (ms := [swapRows 80,swapRows 82,swapRows 83]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u53
theorem b_u71 : Lower true (vars 211) u71T 6 :=
  lower_map (ms := [swapRows 64,swapRows 81,swapRows 66,swapRows 67,swapRows 84]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u54
theorem b_u72 : Lower true (vars 211) u72T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 65 0) (raw := vars 211) (T := u72T) (xs := [(inputs.getD 0 zero,16,17),(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u0
  have hc : (([(inputs.getD 0 zero,16,17),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u73 : Lower true (vars 206) u73T 5 :=
  lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
theorem b_u74 : Lower true (vars 205) u74T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 68 0) (raw := vars 205) (T := u74T) (xs := [(inputs.getD 2 zero,128,132),(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u2
  have hc : (([(inputs.getD 2 zero,128,132),(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u75 : Lower true (vars 203) u75T 5 :=
  lower_map (ms := [swapRows 96,swapRows 33,swapRows 98,swapRows 67,swapRows 100,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u51
theorem b_u76 : Lower true (vars 203) u76T 6 :=
  lower_map (ms := [swapRows 16,swapRows 33,swapRows 99,swapRows 100,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u60
theorem b_u77 : Lower true (vars 199) u77T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := vars 199) (T := u77T) (xs := [(inputs.getD 0 zero,64,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u22
  have hc : (([(inputs.getD 0 zero,64,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u78 : Lower true (vars 185) u78T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 40 0) (raw := vars 185) (T := u78T) (xs := [(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u1
  have hc : (([(inputs.getD 3 zero,1,9),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u79 : Lower true (vars 182) u79T 6 :=
  lower_map (ms := [swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u60
theorem b_u80 : Lower true (vars 158) u80T 6 := by
  have h := lift_ok (u := true) (ms := fixRows 12 0) (raw := vars 158) (T := u80T) (xs := [(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u0
  have hc : (([(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u81 : Lower true (vars 157) u81T 6 :=
  lower_map (ms := [swapRows 112,swapRows 82]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u78
theorem b_u82 : Lower true (vars 155) u82T 5 :=
  lower_map (ms := [swapRows 96,swapRows 33,swapRows 98,swapRows 67,swapRows 84,swapRows 101]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u51
theorem b_u83 : Lower true (vars 155) u83T 7 :=
  lower_map (ms := [swapRows 64,swapRows 81,swapRows 66,swapRows 115,swapRows 100,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u56
theorem b_u84 : Lower true (vars 151) u84T 6 :=
  lower_map (ms := [swapRows 48,swapRows 65,swapRows 82,swapRows 67,swapRows 116]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u78
theorem b_u85 : Lower true (vars 143) u85T 6 :=
  lower_map (ms := [swapRows 16,swapRows 33,swapRows 50,swapRows 67]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u80
theorem b_u86 : Lower true (vars 121) u86T 6 :=
  lower_map (ms := [swapRows 83,swapRows 84,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u78
theorem b_u87 : Lower true (vars 118) u87T 7 :=
  lower_map (ms := [swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u88 : Lower true (vars 118) u88T 7 :=
  lower_map (ms := [swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u89 : Lower true (vars 117) u89T 7 :=
  lower_map (ms := [swapRows 16,swapRows 50,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u90 : Lower true (vars 82) u90T 4 :=
  lower_map (ms := [swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u0
theorem b_u91 : Lower true (vars 89) u91T 5 :=
  lower_map (ms := [swapRows 16,swapRows 115,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
theorem b_u92 : Lower true (vars 91) u92T 7 :=
  lower_map (ms := [swapRows 112,swapRows 97,swapRows 114,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u93 : Lower true (vars 91) u93T 7 :=
  lower_map (ms := [swapRows 112,swapRows 97,swapRows 114,swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
theorem b_u94 : Lower true (vars 83) u94T 5 :=
  lower_map (ms := [swapRows 112,swapRows 114,swapRows 115,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u10
theorem b_u95 : Lower true (vars 83) u95T 5 :=
  lower_map (ms := [swapRows 96,swapRows 113,swapRows 98,swapRows 99,swapRows 116,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
theorem b_u96 : Lower true (vars 61) u96T 5 :=
  lower_map (ms := [swapRows 112,swapRows 113,swapRows 98,swapRows 99,swapRows 100,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
theorem b_u97 : Lower true (vars 59) u97T 5 :=
  lower_map (ms := [swapRows 96,swapRows 33,swapRows 98,swapRows 67,swapRows 84,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u51
theorem b_u98 : Lower true (vars 59) u98T 5 :=
  lower_map (ms := [swapRows 112,swapRows 97,swapRows 50,swapRows 116,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u77
theorem b_u99 : Lower true (vars 55) u99T 5 :=
  lower_map (ms := [swapRows 112,swapRows 97,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u51
theorem b_u100 : Lower true (vars 55) u100T 5 :=
  lower_map (ms := [swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u77
theorem b_u101 : Lower true (vars 47) u101T 5 :=
  lower_map (ms := [swapRows 64,swapRows 33,swapRows 50,swapRows 99,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
def u102K2 : Nat → Nat
  | 0 => 0x898014a450a0294a0447066480
  | _ => 0
def u102K3 : Nat → Nat
  | 0 => 0x219422206222220a10c054a44e90284a0066480d014a40294a044706648083150a0294a0447066480e014a44a8428447066480
  | _ => 0
def u102K4 : Nat → Nat
  | 0 => 0x3e30a41064071c724308464b9b6721e321a4842e904d20900697ad76e0b487b21f480322448912240291224488a0e42b6d2241e4255514522d1a789206407e99aac8ee643a912242230464482014248912128690d242815b0930573200404001028c628d081088f84d1494662a502111f09a29318a34214223803252631c694480274a6880c628d289004e94d1010e51240a129d19a20233234804253a40a4046a4490084a74814809948920109489409013310a402129128120318a14a24633e532406318688288474a64808670929d19490cc901c0d29229911c19920298c14a532238332405310294a644706648086721294c88e0cc90198922102111c19920338214204223833240631428cc8447066480d0a9480509400cc9010d53a40a128019920381a522502238332405318294a0447066480a6205294088e0cc901c0d2912a111c19920390a526142238332407214a4428447066480c6295085088e0cc9018c50a102111c19920291c44a042238332406234a4448067486820c628528900ce90d0410cd1241a121e29908311a52224033a43210631429448067486420
  | _ => 0
def u102K5 : Nat → Nat
  | 0 => 0x22036cc808274a6880a5d1a329129a2028f488ca34a6880cb720209d29a202b94480274a68808e512009d29a20237468ca74868808f60a129d19a2023d0284a74668809d91a001d2912027a4480074a448099d1a001d2912026b4480074a44809b50a001d2912022fcc80074a4480b991a001d291202ea4480074a4480c3d29331f28d202378684c7ca14808ee12131f2852026e0084a74814809b50a321f281202ce0084a44a04809cd12319f29920233448c67ca64808bf32221e2992023b8484a78a6480c3e29e21d299203398288474a6480ce40a211d299203358678274a6480ce611e09d299203358670274a6480cd419c09d299203398470274a6480cba21e01d2992021f8e84a60a64809b50a321c2992030f4a04870a64809b60a129e219202a7488ca3866480c5f28d29e1992023b8484a78664808f60a129e1992023d0284a7866480b950a2292199202c74a8c81866480ace12129a199202b58284a6866480ad40a129a199202374e8ca4866480e5b282282199202b58284a0866480ace12129e199202b58284a7866480ad40a129e199203174a70a7866480a9f22029e199202a74880a7866480e1d292298199202b38484a6066480ad60a1298199202b50284a60664808de3a1298199203634a4447066480d8d20511c199203338a6447066480ccd29911c19920363488447066480dc70a111c19920371428447066480dcb02111c19920372408447066480ccf32111c199203874a44a0066480ad60a1280199202b50284a0066480c8d29111c199203334a1447066480ccd28111c199203334a8447066480cc70a111c19920333428447066480cc50a111c19920333408447066480acd12019a099202ad488ca1826480c7728529e099202b34480664264808df3a019909920273448067426480c9e19e31d200203278688c7480080a760a101f2982023d8284074a6080e1e1a12012982029d8284074a6080ad60a1283198202b58284a0466080c9e3a1201198202b98284a0446080e8e1a12011182023d8e84a0c260808f63a1281098203a58684804260809f102209d29208237c680c74a48208dd1a031d2920823b4480c74a4820b720a1291282082378684878a6820a760a129129a0831dca14a7886820ab60a129121a082378684a74868208dc1a129d21a0823b8484a7486820cd728619d21a082b3448067486820c9d29019d21a082334480674868208f432129d205083cc4a44814a0420b712a1205281083d44a34614a0420b712a1185281082734480674804208de1a121e299082370684878a64208f60a129e219082734480674864208de1a129d219082370684a74864208ee12129d2190823d8284a7486420acd12019d219083274a40674864208cd12019d2190823d8284a78664208de1a121d19908275868487826420
  | 1 => 0xc3f74ba5d2e91cba5461824ba1e8086cba5d024755082a9974ba0e5d7744d8e89b478c1fe66d8070a8ceb6712be1b32935d2e8ccba5158374ba392e8662f402e974595d2e828addd03a76ba5d2e974ba5d1ad74ba32602cfba5d2e8f5ba020d174ba196e845ba4a00b0523cf6e974205d0348e4bd6a048a414eee8a32d5d2e9646d51a7059a1818ee8dba5d2e8b445dd1fec5b1a185371ba0b63774ba1d2e81bba0b1530b3edd2e871224292a3baf5d2ab74ba5d196a20ac84ac806f0590a78950c0c8efba18ae974ba55ee9742993ae974ab586e8fbba5d2e974a85d00374ba0c46d3aba045e574ba5d2b8aeba49dc27bba5d2e974ba5d2e974ba5d2e8cdba1ca6f40ba5d1cc35ba5d2e97435ba5089055438aaadb654ae974ba5d2e9744f5d2e930ba5d0db74ba232e92510ba1a974ba5d1a0d22a5d2e97409dd00f2421b4ee974ba5d2c174ba4ae5c4b7f5384f74ba3a81e9a500f22770aa5d2e8b339a4926388f31029031f2d49904583ccde602c4b046ac5c8ca0e5f61c502e205edd2e974a6dd2e974ba5d2d6fc4b2ddc13c1fc898139005d2bf74905d2e92fac5d1faf71b94a0c6e54296e87c20872e96fba5d2e96a7720ee91a4faf8d4f6ba5d2e974ba528a174ba5d2e974ba5d05e4fba276cce72bd21d9683f176e974ba036e9744e5d2e974ba5d2e8a6385d2e974ba5d2e9741a3085c992e5d2e869538888498ba4a40661ba5d2e974ba5d2e8bcba0cee974ba4f9bf0f135d0931d9fcb66d41642e212f06e026e974ba5d2e974ba5d2e974ba07ae87968862e888ba33ae83d43809b342255d04b74ba5d2e974ba5d2e9088bdd18f1f88bc6e8f847cd6e574ba3d2e9745d250c7746da46e810058aec57428be426085c2010012006911c65004811804001cc13940000c20300c01008028c43383400002010022188e900525044600006000ca608c600800320c44128e300c22380010804d0022008c04cc51a111f09a29339c08447c268a4ce502111f09a2923b448cc78064a48f70a331e0192923e8e84060064a4ce901911c0192930f4a74870064a4cad21d11c01929339c284470064a4ce50a111c01929335c67c270064a4ce511f09c0192931d4a74270064a4cb521d09c01929335c674270064a4cd519d09c019293394474270064a4ce911f01c01929237468007486ca18ed12001d21b28637868487c06ca18dd1a001d29b2063b4480074a6c81c7b01e01d29b2069d8284074a6c81a3d22001d29b206974680074a6c81a6d12001d29b2069d4280074a6c818df1a001d299206374680074a64818ed12001d299207c54a44a348146187f2a001d2191861f4a80074864618ed12001d219186674680074a4c809ad12001d2932026d4280074a4c80b3b021293283202764680074a48809e912001d2922026e808487ca3880d9a1a131f20
  | 2 => 0x19ba5d28974ba5d18d745dc495774b7442e8d5ba16ee974ba5d195749a5d2e974ba5d1f5748cdd2e974235d091498a8314959b9a2697748b2f
  | _ => 0
def u102K6 : Nat → Nat
  | 0 => 0x27e90e14c9012f4870a64809fe038532404fd01c299202de94f10c901e7483866480dbe51c332406dd28e1992036e8c30cc9013f8a78664809fa53c332404fd09e199203cf1490cc901e74a4866480f3e40c3324079d2061992036f94d0cc901b78a6866480dba534332406dc29a199203cf10d0cc901e7887866480f3843c332406df2921992036e9490cc901b7ca1866480dba50c332406df2821992036f1410cc901b74a0866480dbc404332406df29e1992036f14f0cc901b74a7866480db853c332406de21e1992036f04f0cc901b7427866480dba03c3324079d290199203ce9020cc901b78a6066480dba530332405cd11c199202ef98e0cc901a74a4066480dba508332406dd2801992026688e0cc901ed481826480dbc334132406dc19a0992035e94904c901bdca18264809fc53c132404fd29e0992027f0cf04c9013f467826480dbc332132406dc199099202ef0ce84c901770674264809fa63e500405f609d2802027f18e940101e7867480080d7c63a400404be31d2002033e80f94c101af4804a60809fa03a5304063d2012982033f00e94c1019f4074a6080dba506330406df2811982036e9408cc101a7480466080dde502230406ed2811182035690088c101bd4a0c26080dee502130406f52810982035a90084c1013fca7c060809fa53e030405f609d2920827f98e9490413f8c74a48209f863a524105f501f286082f880f943041ddca14a0820ef25225041077928d282083b9942941041fc8274a0820bbc33a404104fd21e29a083bb94294d0417d8274a6820cfa5225341067d28d29a0833b94294d0413f8874a68209fc33a534106f609d29a0837b94310d0413f4a7886820bbc33a434106bd29121a0835e90690d041bdca14868209fc53a434104fd29d21a0827f0ce90d041b78674868209bc33a434106dc19d21a0826e0ce90d0413f487866820dba51a334106dd20d19a0827e94e8cd0413f4874668209fe63a522104fe31d2910827e18e9488413fcc74a34209fe63a41a107b5291205082fa94e902841f54a3461420bea53a30a105f521d185083f8903140841fc4618a0420eea50a50210779291281083bc946940841dc4a14a0420fe240a502107f1185281083f904e940841ed481480420bbc33a402105dc19d201083ea8c28c08419f4a48a64209fa43c532104fd19e299082fb04e94c8413f8874a64209fc33a532106f609d2990827b04e94c841bd4618864209fa53c432104fd19e219082ef0ce90c84177067486420bec13a432106bd2912190837a8c290c8413f8a74864209fa53a432104fe19d2190836f0ce90c84137867486420db833a432104dc19d2190837b04e90c841bd4818664209fa53c332104fd21e1990837a9028cc8413f8874664209fa43a332107f1282099082fa94f04c8417d487826420
  | 1 => 0x49fa33c132524ff01e0992927e80f04c949bec068064a49fe63c032524fd09e019292f708e80c9497d8274064a4be813a032526f9018019292df90e00c9497b4470064a4bee138032525f509c0192935e90e00c949bb4470064a49da238032526f709c0192927b84e00c9493f4270064a4dea138032524f509c0192937d80e00c9493fc07486ca19fc03a43650cfc01d21b2867e90f80d9433f887406ca1b7c03a52640cff01d29b2067f00e94d9033f0074a6c81cfe03a53640e7e01d29b2073e80e94d9039f0074a6c819fa53e03640ebd29101b2067f14e80d903ed8274a4481b7c03a52240f3d29128d206fa80f9429033f8674a6481dec13a53240cfe01d2992067e00e94c9037d8274a44619fc63a52230fb5291205187ea9469028c33f8a74864619fa53a43230cff01d2191867f00e90c8c33f007486461b7e03a526405bc01d2932035f18e949901cf4a4ca0c809ba33e5364067f28129b202ee8cf9491017ec07ca4880bf203e524405fa01d292202fc00e9491016f487ca38809fa63e51c404fd31f286203dd9419011016e4c7c80880f764065344067d29329a203dd90094d1017d8274a6880cfe5225344067d29129a2033f94694d1019f4a34a6880cfe50a5344067d28529a2035f90094d1013f8674a68809fc13a534406f609d29a2027b04e94d101bd0274a68809e813a534404df19c29a2026e8ce14d1013b4470a68809ee138534404f509c29a2027f94e90d1013f0a7486880dba51a334406dd18519a2027e94e8cd101bd4a1426880dea30a134404fd29d09a2027e8ce84d10177467ca4480bf603e522405bd29e291202da84f1489016fc078a4480b7e63c522405f801d291202df0ce9489016f8274a4480f7403a522405bc01d291203dc00e948901af0c74a4480e7a52651a405bd21f28d2027f98f9469013f4c7ca3480e7a52251a4079d28f20d202de94f9069016f4a7483480b7a43e50a404ff31f2852027e98f9429016f4a7c81480a7a53e40a407b7285205202de94e902901ed481461480b7a43a30a4073d293281202df90f940901deca08a0480e7a522502405bd21f299202ef8cf94c90177467ca6480bf203e532404fd21f2992026f8cf94c90137467ca6480e7a5245324067f29a299202df10f14c9019fca48a6480cfa524532406bf2062992035e90314c9019fca08a64809fa53c532404fe21e2992027e8cf14c9013f4278a64809fa03c532405be21d299202ef0ce94c901770674a6480bdc23a532405f609d299202fa04e94c9017e8074a6480d7e40a532406bd2052992035f10e94c901bb8474a64809dc23a532404fe09d2992037b04e94c9013d8274a6480de813a532404f409d2992027f00e94c901be8074a6480e7a5205324067d298299202df90e14c9013fcc70a6480cfa5205324067d28029920
  | 2 => 0x256d5b56d5b56d3c07098b189556d5b56d00441db56d5b53a87f6d5b56d5b5395b56d5b47b406d820f434156d0cb6d5b477db56d5b56d5b56d5b56d48f6d0eae5341245b56d5b4a5db56d3b76d5b56d46f6d5b415db56d35a22db56d292f0db4c9db56d5b56d5b56d22204d8cf944f6d4ed2adb56d4596d06ac580b6d5b56d5b56d5b56d5b56d5b56d2b56d2e56d5b56d5b56d5b56d5b44adb56d5b56d5b5145b56d5b56d0776d4444353212db56d1d1205b56d5b56d5b56d5b56d368dd5b56d5b47654b6d5b56d1016d5b56d1bd681ff6d5b56d5b56d5b56d1726b5b56d5b48f5b56d5b56d1e76d4696d5b56d5b56d5b56d344a95b56d5b56d5b56d5b56d5b446d88c94ce9edb50edb4665b56d1cc27db50a547335b42c2df6adb56d5b56d5b56d5b56d5b56d1795b5b448db56d2a96d5b4985b4a65b56d5b4811a8605b56d5b56d5b56d5b56d370f281aaedb5545b56d5876d164655b56d5b4c41276d364b0db5610db1aa6cc138b6d5b56d0536d0616d5b56d5b56d4b12ca5f6d5b4ecdb543db56d5b545db53edb5489d76c4302a0656d5b4272416d5b56d5b56d5b4b4db409a4f6d5b5065b44b5b430c096d5b56d5b5345b4b6c3d6d5b4c85816d5b52d5b56d5b56d5b526db56d5b56d5b56d5b56d5b40c5b50faff6d47d6d5b56d54d6d5b524db56d16d6d5b56d01f6d5b47bb85275b56d2896d5b56d5b56d5b56d5b478db4e9db56d5b56d1636d5b51b5b56d2a16d5b41bdb56d53f6d5b56d5b56d5b54e15d6d5b5482776d5b56d5b56d542a2db5253e2295a853db56d5b56d1534f0d8dcb4d6d5243ddb4395b56d01d6d5b4a99356d5b44edb5575b49e4f76d5b48bdb4cfdb56d3b4f99af6d10b6d5b56d5b55d5b56d1c4fd1bb6d26ae05b4c0db53f5b48209a105b49fc356d5b56d5b4dfdb49c5b465d040588d6d5b56d5b46d3c8315b56d3c56d5b46aa8d6d400635b40a5b56d5b56d5b56d5b5095b56d26308a4273ae0125b52b1596d5b45f92f6d5b56d308255b5155b43e3a2eedb4a0db56d42f3d1756d53b6d5b56d092a545e4d9a76687d2ddb43edae3f5b4704ff585b56d5b56d5b56d1e56d44d675b56d54f6d5b564a4c87db56d5b512db56d5b56d110005b4ab0e8ee14d6d5b4a45b56d5b4ccdb56d5b56d5b44fdb43fdb56d1156d5b4e5db56d5b56d5b54ddb56d5b4a75b56d5b56d5b56d5b56d36617db56d2bf6d5b4485b56d151294e36d5b511db56d5b56d5b56d0d76d5b4de5b56d5b56d3156d5b56d5b56d5b4480600662202600200000000420006200000088000200000024200201004022202004a2640a040200201006220064004022020422a0020606066402000400044a020000000242806044002294046680220004000000020400020202600000020220000424020c4620c2200202048024060206086c00139447c268a
  | 3 => 0x6d5b4875b56d4d56d4436d3d36d5b56d5b485ab16d0f36d5b56d5b56d5b56d4a76d5b56d5b56d5b56d5b50da0af55b56d4a16d5b56d5b41a5b434a596d3821135cb8db56d5b56d5b56d5b56d5b56d1296d5b56d5b4645b4fc5b56d5b48ca036d0473100e355b4c6db4f74536d5b56d47b6d0ef6d2556d5b4f3b2b6d5550adb56d5b56d5b56d5b56d5b56d5b4c35b56d5b56d5489f5b56d5b56d5b56d038c05b56d5b56d4bf6d2736d5b56d5b48e5b4d4200174e9265b4cf4676d04d6d5b56d5b4df5b56d5b5560a76d5b56d0036d5b56d5b56d5b56d5b56d5b56d2d16d5b56d5b5465b56d5b56d5b56d5b56d5b56d5b41d4cb6d5b56d4bcc7db56d3fe5adb56d5b4a3db5325b4f1c136d5b4bedb56d5b56d5b56d5b56d5b56d5b531db56d5b47f5b5655b56d5b4c75b56d5b56d054d1889645b56d2c96d5b56d5b56d5b56d5b48b24b6d5b4c2db56d5b56d5b4e85b4213e9015b500db420cf21c2ef5e2cd6d570fbdb43c5b56d3f8dadb56d5b56d5b56d5b4f84bb6d5b56d5b56d5b56d5b4505a706c8a585b56d41d548dd6d5b40cdb56d5076d5b56d5b56d5b56d5b56d5b56d58e2adb56d39ad65b56d2c11ddb56d416f69f56d5b56d5b49b8b6a1b48e232d6d230414406da656d5b56d0096d328b61d36d5b55ddb56d1db6d5b56d19e19db56d0bd6d5b56d5b40ddb56d1eae3478c1db56d5b56d5b56d1f87ebad6d5b4bd1a36d5b56d1316d0bb6d5b4145b5121b36d5b56d4336d2456d5b56d5b56d5b56d5b56d5b56d19ad88b4755b56d5b56d5b56d5b56d2e76d5b50e5b56d5b56d3316d5b56d544515b56d5b56d1185dbf76d5656d0a16d5b4085b56d5b56d5b535db56d5b56d3a52a5b5082a36d5b534db5195b49d0a244db56d5b56d5b56d5636d5b56d5b450db56d0b96d5b4f7cf16d5b56d5b56d5b56d4716d1336d510835b5375b56d0bf6d2aa4202a6fdb56d5b56d2ed6d5b520cda675b547db4b15b4325b56d21a775136d2134025315db56d1696d5b54d5b5210076d5b56d0ec9a5b56d5b56d5b56d5b55f5b56d0196d2076d11d6d5b56d5b56d5b56d5b56d5b56d5b4cedb56d02ee1d2c055b438db41e9f0b1a9a895b56d5b52e460ae5b56d5b56d5b56d5b56d5b56d5b52bb4321db56d5b56d4756d0b36d3fd6d5b56d5b56d5b56d5b56d5b56d5b56d2e8d7db56d5b4fadb56d3a96d5b56d5b439db56d090b5db4a15b559db56d5b56d5b56d5b56d22b6d2676d5b472db56d5b56d5b56d5b56d5b56d2b2f65b56d5b459db56d5b56d5b56d5b4fedb56d5b56d5b56d5b4d4d1b6d42d6d5b56d5b56d5b4a7db56d5b56d5b56d45caf5b56d5b56d5b5385b56d5b56d080d583e63db56d5b41c9f7695b56d05b6d5b56d5b56d5b56d5b4be5b56d5b472338db41ecb8ce925b452db557d7f365b56d5b56d3376d5b56d5b56d5b56d5b56d5b56d1
  | 4 => 0xa05b4945b56d5b56d5b4695b451db56d5b408ca2035b495db56d5b4095b4e75b502db56d5b56d5b4cd5b56d5b556db5425b56d5b56d5b56d2150983a8ed2f6d5b4b55b56d5b56d5b56d23f6d5b56d5b56d5b56d5b46818247d687832291db56d5b440db56d5b56d5b527baf6d5b56d5b56d5b445db56d5b56d0df6d15b6d5b56d5b56caaf6d5b410db413db56d5b525c896d5b56d45a7a5b56d0356d5b56d5b54adb56d5b56d5b56d5b56d5b56d5b56d06d6d5b56d5b56d5b56d2b76d5b56d5b56d57b6d5b56d5b56d5b56d5b56d5b56d5996d08f6d5b425b916d3d16d0c6b73bc4f2376d5b4fcdb4c65b54717d6d5ac61db56d5b56d5b56d5b56d5b56d5b4045b56d3936d5b4265b56d5b455db56d3ab6d5b443db56d5b4ef9f36d5b56d2fd6d5b496cc0f5acf6d47e5edb5455b56d5b56d2116d5b56d5b56d3ed6d5b56d5b56d5b56d5b56d5b5035b464db41e5b488540345b457db56d5b56d5b540b6f6d0cd03db489db56d5b4d52295a8e0e61b1235b51cdb56d02d6d39f6d03d4a5b4623776d5b43d0624e3b16d25d6d5b56d4116d5b56d4f96d5b4305b56d5b56d0ac1637a865b4523cc8d5b56d5b56d5b56d5b56d5b56d5b56d5266e5b471d302bdb56d170badb56d5b4615b56d5b56d16f6d2f16d5b5
  | _ => 0
def u102K7 : Nat → Nat
  | 0 => 0x908f4783b1e8aad918bc8f3d1a20c8f47a3d1e8f1281683640cd3e8e1eb4a24dc8f3799e6101324d11e6b3ee3c928f045231e8f2823ca13ac7a3d1e8f47a3d1e218fa3cf24c1d01b1e59c7a3d1e4b478c6328b0a454c38f2c4366d26991970a6e8ed52b544838a6e48f479d8d08f4363d1e4391a10666d179d0fa1612d76358f3323d1e8f0ddf2048f1663c971387e3cfc8f478e6218f15c569c8f4783d1e771b88ae98f47a3d1e78c797cc28f0223d1e7bc5e3c228f478348f8f2e148ad54478fb1157c79c2a645040e50688478f26c209453c77220da3cc104aca32d42fb10ce868f0d04cca8646208548f3541e954ea08603c7188d8d028f3605d1e27c79ccef0cc79d46f240e814ed4a38916142d101a6428d2c07e7009a680a7b8f125271e8f47910b78f47a3c6a8704a1f1e51c70a0848f47a3d1e70478fd1e2b2f63c808f09098c50bb6e3cf31cc78a4ba80171ed1e8a2d23d1e6691cc51e8f0bcc0fe8f3ac307f553663d1e8f1ac62203281a26581447a3c002ec799c1c78294d2163d288025b4c9e23cac5f9f10a2520121000619b582404081048120c67201c1180a011c630900010862008e46802000a27b80000c0a108883200c529010080241180030003cfca48a4bf4a68a4bdc268a4bd4268a4bfc068a4bf4068a4ff8264a4bf8264a4ff4264a4ffc064a4ff8064a4bf8064a4ff4064a4ff0064a4bf0064a4bfc060a4bf4060a4bf486ca1bfc06ca1bf406ca1ff4834a1ef4a4c819fca6c81bf4a6c819f4a6c81bfc06c81bf406c81ef4a4481ff4a3481fdca1481bf4a6481ff4a4461fd481461bf486461ef4a4c80ffca0c80bfca6c80bf4a6c80ffca4880ff4a4880ffca3880ff4a3880ffca1880ff4a1880ff461880ffca0880efc80880eec80880ffca6880bfca6880bf8a6880ff4a6880bf4a6880bf0a6880bf486880bf466880bf426880ffca4480ef8a4480ff4a4480ef4a4480ffca3480ff4a3480efc83480ef483480ffca1480ff4a1480efc81480ef481480ff461480ffca0480ff8a0480ff4a0480ffca6480bfca6480ff8a6480bf8a6480ff4a6480bf4a6480ff0a6480bf0a6480ff886480ef886480ff866480bf866480f7866480b7866480ff466480f7066480b7066480ff826480bf826480ff426480ffca0080ff4a0080ef480080bfca60809fca6080bf4a60809f4a6080b7c66080b7466080bb446080bdc26080bd426080bfc06080ff4a4820ff4a3820ff483820fdca1820fe8a0820ff4a0820fe4a0820ff480820bf8a6820ff4a6820bf4a6820bf886820ff486820bf486820bf866820bf466820ff4a4420ff4a3420ff483420fd4a1420fd481420fd461420fe8a0420ff4a0420fe4a0420ff480420ff460420bf8a6420ff4a6420bf4a6420bf886420ff486420bf486420bf866420ff466420bf466420fd826420
  | 1 => 0x11e7c47a3d1e0393a3d1e63c7a3d1e55c78711e8f478ab1e8f1c63d1e57479ce768f47a3c9b6029e3c
  | _ => 0
def u102K8 : Nat → Nat
  | 0 => 0xc4de7e7389e176be583ce0d5c34b9ce701cd3a8281228655c100a8300bfc527f4a4fe149ff287fa50ffc81fe903fd187fe407f880fe901fc203fc107f420
  | _ => 0
def u102K9 : Nat → Nat
  | 0 => 0x143f
  | _ => 0
def u102N : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 36
  | 5 => 186
  | 6 => 365
  | 7 => 143
  | 8 => 14
  | 9 => 1
  | _ => 0
def u102R : Nat → Nat → Nat
  | 2, i => packedAt u102K2 (i * 97) 97
  | 3, i => packedAt u102K3 (i * 84) 84
  | 4, i => packedAt u102K4 (i * 71) 71
  | 5, i => packedAt u102K5 (i * 58) 58
  | 6, i => packedAt u102K6 (i * 45) 45
  | 7, i => packedAt u102K7 (i * 32) 32
  | 8, i => packedAt u102K8 (i * 19) 19
  | 9, i => packedAt u102K9 (i * 6) 6
  | _, _ => 0
def u102I : Nat → Nat → Nat
  | 2, h => packedAt u102K2 (98 + ((h / 1 + packedAt u102K2 (97 + (h % 1) * 1) 1) % 3) * 2) 2
  | 3, h => packedAt u102K3 (338 + ((h / 2 + packedAt u102K3 (336 + (h % 2) * 1) 1) % 17) * 4) 4
  | 4, h => packedAt u102K4 (2644 + ((h / 22 + packedAt u102K4 (2556 + (h % 22) * 4) 4) % 99) * 7) 7
  | 5, h => packedAt u102K5 (11378 + ((h / 118 + packedAt u102K5 (10788 + (h % 118) * 5) 5) % 607) * 9) 9
  | 6, h => packedAt u102K6 (17369 + ((h / 236 + packedAt u102K6 (16425 + (h % 236) * 4) 4) % 1914) * 10) 10
  | 7, h => packedAt u102K7 (5016 + ((h / 88 + packedAt u102K7 (4576 + (h % 88) * 5) 5) % 389) * 9) 9
  | 8, h => packedAt u102K8 (306 + ((h / 8 + packedAt u102K8 (266 + (h % 8) * 5) 5) % 38) * 5) 5
  | 9, h => packedAt u102K9 (7 + ((h / 1 + packedAt u102K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u102Pos : Nat → Bits
  | 0 => 0xfffffffffbdffc21fe0018007ffc1041801fff
  | 3 => 0xffffffffe0000cc006c3e208089c69a6599293
  | 4 => 0x4207306397c040f90e08e3861e31c
  | 5 => 0x18018c18007f01f030fc07e03e0
  | 6 => 0x83e001f000007ffe003f0007ffc00
  | 7 => 0x17c003e001fff8000003ffff800000
  | _ => 0
def u102Neg : Nat → Bits
  | 0 => 0xffffffffe000014a0000000000000000800425
  | 3 => 0x1ec692944bc4e65ab9bc28a2599292
  | 4 => 0x194a02b54bcc26299ae40a2860a318
  | 5 => 0x19bc26944bd94eb91fc90fc06a03c0
  | 6 => 0x601d800902291466012f000155800
  | 7 => 0x316c00243319844403d555000000
  | _ => 0
def u102Slices : List (Sig × Nat) := [(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,8),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,7),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,6),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,6),(0x0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff,5),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,5),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,5),(0x000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff,5),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,5),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,5),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,5),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,5),(0x000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff,5),(0x5555555555555555555555555555555555555555555555555555555555555555,5),(0x0055005500550055005500550055005500550055005500550055005500550055,4),(0x0000000055555555000000005555555500000000555555550000000055555555,4)]
def u102Atlas : Atlas := ⟨9, rawDecor 249 u102Pos u102Neg, u102T, u102Slices, [swapRows 83,swapRows 118], u102N, u102R, u102I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_2_0 : Interval u102Atlas 2 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u102_2 : Interval u102Atlas 2 0 1 := blk_u102_2_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_3_0 : Interval u102Atlas 3 0 4 := block_range (n := 4) (by decide +kernel)
theorem all_u102_3 : Interval u102Atlas 3 0 4 := blk_u102_3_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_4_0 : Interval u102Atlas 4 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_4_32 : Interval u102Atlas 4 32 4 := block_range (n := 4) (by decide +kernel)
theorem all_u102_4 : Interval u102Atlas 4 0 36 := (concat blk_u102_4_0 blk_u102_4_32)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_5_0 : Interval u102Atlas 5 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_5_32 : Interval u102Atlas 5 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_5_64 : Interval u102Atlas 5 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_5_96 : Interval u102Atlas 5 96 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_5_128 : Interval u102Atlas 5 128 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_5_160 : Interval u102Atlas 5 160 26 := block_range (n := 26) (by decide +kernel)
theorem all_u102_5 : Interval u102Atlas 5 0 186 := (concat (concat blk_u102_5_0 (concat blk_u102_5_32 blk_u102_5_64)) (concat blk_u102_5_96 (concat blk_u102_5_128 blk_u102_5_160)))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_0 : Interval u102Atlas 6 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_32 : Interval u102Atlas 6 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_64 : Interval u102Atlas 6 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_96 : Interval u102Atlas 6 96 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_128 : Interval u102Atlas 6 128 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_160 : Interval u102Atlas 6 160 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_192 : Interval u102Atlas 6 192 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_224 : Interval u102Atlas 6 224 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_256 : Interval u102Atlas 6 256 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_288 : Interval u102Atlas 6 288 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_320 : Interval u102Atlas 6 320 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_6_352 : Interval u102Atlas 6 352 13 := block_range (n := 13) (by decide +kernel)
theorem all_u102_6 : Interval u102Atlas 6 0 365 := (concat (concat (concat blk_u102_6_0 (concat blk_u102_6_32 blk_u102_6_64)) (concat blk_u102_6_96 (concat blk_u102_6_128 blk_u102_6_160))) (concat (concat blk_u102_6_192 (concat blk_u102_6_224 blk_u102_6_256)) (concat blk_u102_6_288 (concat blk_u102_6_320 blk_u102_6_352))))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_7_0 : Interval u102Atlas 7 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_7_32 : Interval u102Atlas 7 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_7_64 : Interval u102Atlas 7 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_7_96 : Interval u102Atlas 7 96 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_7_128 : Interval u102Atlas 7 128 15 := block_range (n := 15) (by decide +kernel)
theorem all_u102_7 : Interval u102Atlas 7 0 143 := (concat (concat blk_u102_7_0 blk_u102_7_32) (concat blk_u102_7_64 (concat blk_u102_7_96 blk_u102_7_128)))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_8_0 : Interval u102Atlas 8 0 14 := block_range (n := 14) (by decide +kernel)
theorem all_u102_8 : Interval u102Atlas 8 0 14 := blk_u102_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u102_9_0 : Interval u102Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u102_9 : Interval u102Atlas 9 0 1 := blk_u102_9_0
theorem cert_u102 : Complete u102Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u102_2 i (by omega) hi
  · exact all_u102_3 i (by omega) hi
  · exact all_u102_4 i (by omega) hi
  · exact all_u102_5 i (by omega) hi
  · exact all_u102_6 i (by omega) hi
  · exact all_u102_7 i (by omega) hi
  · exact all_u102_8 i (by omega) hi
  · exact all_u102_9 i (by omega) hi
theorem b_u102 : Lower true (vars 249) u102T 10 := by
  have ready : Ready u102Atlas (asRow u102Pos) (asRow u102Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u102Atlas, u102Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u58
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u65
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u57
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u86
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u78
    · exact slice_correct (ms := fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u19
    · exact slice_correct (ms := fixRows 80 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u27
    · exact slice_correct (ms := fixRows 96 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u29
    · exact slice_correct (ms := fixRows 72 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u26
    · exact slice_correct (ms := fixRows 136 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u38
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u39
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 160 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u42
    · exact slice_correct (ms := fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u12
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u50
    · exact slice_correct (ms := fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
    · exact slice_correct (ms := fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u13
  exact frozen ready cert_u102 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u103 : Lower true (vars 246) u103T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 128 0) (raw := vars 246) (T := u103T) (xs := [(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u87
  have hc : (([(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u104K3 : Nat → Nat
  | 0 => 0x50cc04a44090284a3482462
  | _ => 0
def u104K4 : Nat → Nat
  | 0 => 0x35dbe50fce2c1c08924e2b8fe611ce325628e1ce6b9c3560d80aa8e454a24203813251c3c409c288a7866482ca894881004e9468c59c112502009d28d18ac1864a52251a412316c14a40284a34824629e08120509469048c50f10240a129e21918278204814251a3122045a4a90e846248044093881205094714c88174212528e2891810825a064a542312302106344620c84a7460420
  | _ => 0
def u104K5 : Nat → Nat
  | 0 => 0x6400bd00804005d007d40047000390cd8b35f9f1429e343500900800c51cfe2a8e5a1006f0c8c21980400f054700022088014146108000580019686008c053002102021294e208003088202810211c400006c0140111801380201081c08524cf212101c09928f3c4484070264a38f60a111e01928e3d0284478064a3c5d28d31f20e28a3d408c27c864a28f50a101f21928a7c4080274a34828f70a229e19920a3d4288a7866482a5c32129128d18b554a40274a34629d502009d28d18a744080274a3462aac32129120918bc34a44a3482462bc40a128d20918a3d4088274a6462c7529009d29918a3d4080274a64628f60a201d29918a3d0288074a6462aae12129221918a3d8284a78864628f40a129e21918a3d8284a74864628f40a129d21918a3e8084a74864628f802129d21918a3d8284a78064628f40a129e01918ad38484a38a24608be22131e2891822f0884c78a2460cd518809d299182a7468882886460e8e20918a2191823d8284a78864608f40a129e2191823dc28c478864608f50a311e2191832b8824478864609f10a101f1191822f0884478464608df1a031d291102374680c74a44408f70a031d2911023d4280c74a44409f102009d28d1023dc28cc74a34408f50a331d28d1023dc28cc74834408f50a331d20d102ea4088a4482440bc40a128d189103ca4a44824a0440b692a1209281103d24a34624a0440b692a11892811027a0e84624a0440d6928a21d281102ea4888a2480440ba9222209201102ea868482480440ba9222189201103e2483462480440ba92211892011027a0e8462480440a740a128e2991022f8884678a64408bc22119e2991023dc28c874a64408f50a321d2991021f4a80874a644087e2a109e2191021f0a84278864408de1a109d21910237068427486440ea9209202199103a6483480466440ea92092011991022f8884a74664408bc22129d1991023d8284a74664408f40a129d1991022fce8087466440c9d28c21d1991023d8c84a7462c209f102211d28d082d98484a38a2420a7432128e2890827c8084878a24208f732321d2890827c8084878824209f11a201d2090827c408cc7482420be202120a1890827c808487862420ad432128d189082f88084824624208f432129d1890827c808487462420f5129128d181082f48884a3460420bd212128d181082f44a8483460420f5128e289181082f44688a2460420bd11a22091810827c8e84824604209f03a1209181083f0882462460420fc1209189181082f48a8462460420bd12a1189181082f4888462460420bd1221189181083744628a7460420af032129d181083744624a7460420cf032129d1810823c0c84a7460420bd11a311d181082bccc8c47460420bb222111d181082ec0884474604209752a321e1190827c408c87846420
  | 1 => 0x1007c942010057820c500258856f0080400670012a9e00dd8028e00898040201006629600943dc0200a880402010080401f6f443c02009080024e48b80402005a8040201000040200466ca18ba1c38a760100511b92ce68039c250080401b5002d9cc6b00183f4c100800f5d8b26e389ae63134002e3f3fc012b0080402009b7c04e00b07aaf8ca2f8014d802c55992009c368e9483b72401cb00804017a7e80402010078144fafc05b6c36b5800e201004c34a010027a290a1f804020100802a89d005b0a986c82c269fece8040200298001533008016490498040200974fc020100804018ca9801e4aea680402010060c0002880a40200ba802ece091774020100494020100751aa010080401e7006fc02002447c0201000ec0200b18006a00b46b1d2010001110f4d56889d724c8020201008040200ad800b46d008000e00698024e010080400d7006240201000f402002b80402010046314ce75203da001657400950079402000a5e32841008010a0015804007c7626a35046f142b06847503a0ac5f67b607822031dc208142044a4661bae200c22e0601d0
  | _ => 0
def u104K6 : Nat → Nat
  | 0 => 0x27f98e9488813f8c74a44409f863a522205f609d28d102fa04e9468813fcc74a34409fc63a51a204fc31d28d102f788f9068817b447c83440bf203e41a204ff31f20d1027e98f9068817bc474834409fe63a41a2076d28e289102f690f1448817b4678a2440eda522512205ed21e209102f68cf104881eb8a4482440f5a522412205ee29d209102f694e9048817b867482440fd403a412205ed21e189103e69468c4881f3483462440bdc53a312205ed29d189102f710e8c48817b487462440afe53e40a2057d29f205102f688f9028817e407c814409fe63e40a204fd31f205103bc948940881de4a34a0440ed2512502207e9209281103f48c49408817e8874a0440fd4512402207e9289201103f5104900881ee482480440f52412402207ea189201103f48c49008819f4a38a64409fe43c532204fd21e2991027e8cf14c8819f4a44a64409fe43a532204fe21d2991027e10e94c8813f8674a6440bda23e432205f901f2191035e94990c8813f4a7c864409fa23e432206ed18a2191035f90310c881af4818864409fa53c432204fd21e2191027e8cf10c8813f427886440bf403a432206ee189219103768c490c8813f8674864409fc13a432204fd09d2191037d00e90c8811fca70864409fa5384322047d29c2191026f8ce10c881374670864409ee138432204f509c2191027c80e10c881bb482866440df2404332204fd29e1991027e90f0cc8813dc278664409ea13c332205be21d199102de10e8cc881b74a3466440dba41a332206ee209199103769048cc881be4804664409fc53a332204fd29d1991027f10e8cc881af88746644097c43a332204fd21d1991035e10e8cc8812f0874664409fa43c1322057e29d099102be14e84c8811f8a74264408f853a132204fe21d099102fb08e9478413d8c74a3c20bec33a416107d528d18b083ea9068c5841f9482462c20bec53a316105f529d18b082fb10e8c58417d487462c20bf403a412104ff31d2090827e18e9048413f487846420bec23a51a107f101d28d0827a18e946841dd4a38a2420bee43c512105f521e289082fa8cf1448417dc874a2420f4e414412105f521e209082fa8cf1048417dcc7882420bec33a412107f201d209082f900e9048417dcc7482420be863a412105d719c209082ea8ce1048417c407082420bee638412104f731c2090827a98e104841f9482862420bea43c312104f731e189083ea9468c4841f5483462420fcc412312107e5209189082fb14e8c48417d4a7462420bec43a312105f521d189083f89488c0841f44a3460420fa241a302107f2289181083f89448c0841fc882460420fe2412302107d1189181082f914e8c0841fc4a7460420be253a302107f121d181083f988e8c0841fc447460420bee43c232105f521e119082fb90e08c8417d487046420
  | 1 => 0x2a4a92a40549577ea46a46a9901ba92a4882a4a926827aa4a92a4a92a4a928730ea466ea4276a4a92a4994441c094080044c10c8c00c44c00000014c000004004004100c04000c0004049000880804404810800c10400082c040084444c0000401c4008010c8005480c188f01241404c4008188c48002008840c00c04501844800418b00042400410000014480042658001c027e90f08c9473f4078464a3bec13a23251df409d11928e7a80f04c9473d4070264a39e203813251cfd11e01928efb04e80c9477d0274064a3adc23a51c5175d28f20e28a7e98f9071453f407c868a2cfa51a434514fe19d21a28a7f00e90d1459f4a34068a29fe43a0345157d29f20d28a7e98f9069453dc27c864a29ea13e432514fd01f21928a7f00e90d1057d8274a3482be813a51a414fe31d28d20a7e18e946905b74a38664829fc53c332414fd29e19920a7e80f0cc9053f4078264829fc03a132414fd19e01920a7f04f00c9053f4278064829ea03e130416f109d01820af700e9050c53f8074868629ea03e134316ed20901a18a7a84e80d0c53f8c74a44629f863a5223175d29128d18aef10e9468c5750274a3462bbc03a51a315ed01e20918bd69489048c5f34a3482462f9c33a412315ee01d20918a7e90f14c8c53f4078a6462bec13a532315f409d29918b3e94894c8c53f8874a6462dec13a532314f609d29918b7a04e94c8c53d0274a64629fc03a532316bd29221918a7e94f10c8c53f407886462bbc33a432314fe29d21918a7e94e90c8c5b78674864629fc03a432316dd28e01918b6e90700c8c5bb4828064629fa53c032314fd21e01918adf10e80c8c56f0874064629fc03a43620cff31d2911827f18e9488c13f0c74a4460eba52251a305de21d28d182ef08e9468c1774a7483460eba51c512305dd19e2891827f98f1448c13f4c78a24609fe63a512305dd19e2091827f98f1048c13f4c78824609fe63a412304fe31d2091827e18e9048c1f3882462460f9a412312305de29d189182ee94e8c48c177887462460bba43a312306dd18a2991827e90f14c8c13f4478a6460bec13a532305f409d2991836e8c494c8c13f8474a6460dec13a532304f609d2991837a04e94c8c13d0274a6460d7a524432306be20a2191836e8c510c8c13f4a78864609fe23c432304fd11e219182ee8cf88c8c17dc27c46460bea13e232305f901f1191837690588c8c13f487c464609ee13e232304f509f1191836e94708c8c1b74838464609fa53c232304fd21e1191827e88f08c8c16f887446460b7843a232304fd21c119182f688f9078813f4c7c83c40bdc33a416207cd20d18b102f690e8c5881bb462486c409fc33a436206dd20d19b103769048cd8813f487466c40bda23c522205f709e291102fa84f1488817e4078a44409fe63c522204fd31e29110
  | 2 => 0x42aaa4122a4a9088a92a47d6a47044371d98a922d958ad6dd065ccdb34e328850b3c988a92a4a91770a2a4a92a4a900aa92a4a92a404a333b2a4998509e82b47009a926aa32a4a92a4a92a462ea4a92a482aa4a90a98fc3979ea4a92a4a92a43a6a45fc0ba92a4a92a43baa40aaa4a92a4a92a4a91d15b6a4a92a487ea439ccea92a4a904ea92a4a92a4a92a4a92a4176a4a9159a92a4a92a4a921ea92a437aa4a91c6a9176898afa92a4a92a4a92a4a92a4a92a4a920ba9145a915fa90a5a9258a92a4a92a4a91b8a92a47e14da92a4a92a4a91610cea4a92a409aa4a92a4a92a4a913aa909ba905ba92a4a92a41c6a4a92a4392a4a92a4a92a4a91cd44c9970e5aa92a08510885cf4a90b5a9182a92a481ea4a92a4a92a4a9168a92a44f9e3846a4436a4a9079a92a4a92a4a90fe03679a92a4a90ba9c2a4a92a4a92a4a902fa92a4a92a4a92a4a92a407858980a8a9193a92a4a92a48dea47bc68a92a4a92a4a92a4576a4a91f7394c8866a4a7405a3ea4a92a49fa438d6a474a82640ae2312fa916aa909200aa46ae896f0fca92a4a9105a9094a90d43aea428ea4a90a1a92a4a926c0dea4a92a4a90fd7eea400ea4a90f3a92a4a92a4a92a4559a3a9100569d4a91b04f6a401ea4666a43c6a452cb6a90da50a38a92a4a92a43011b32aa4a92a4a92a4a92a49d2a42d025a917da5aa4a92a47c6a4332a457116872a4a92a4a92a45c2a4a924d49563a91d5a92a479a2ea923c6b290a9133a92a4a9130200c56d87aa902d80949632a4a92a47d88f74152a92a4a90a0a92a43b557a92a469811a02a4a92a4a90c6a92a4a92a4a9228a92a49a624a92a4a9275a92a4a92a4888067a6258bea4a92a4a9096a92a4a92a4a92a4a92a4a917ca92a4a92a4a92a4a921686c8418920a9208546a4a918145ea4a9001a92a4a923d7aea4a92a4a92a4a92a4a92a4a8ea4a92a4a22a4a92a4a92a4a92a47b5a1a9008a92a4a92a4a92a41005f040f9862a430487a92a4a92a4a92a4a92a4a91cb14a44a9223a48df22d365c98320c450127b4d6a4452a4a92a4a9252a92a4a92a4a92a4a92a48741fa91b2a92a45bea43fcb0065d95faa4a92a443ea4835fea92989f2a4a90d83a2a40c2a4a92a4a9051a924ba9251a9129a919ca92a4a92a4a92a47aaa4a92a4649dca92a4a90f5a90d221814a90efa9018726a4a92a4a92a4a910a73148341867f6a48a903a9162a92a4a918aa9119a92a4a903e0d2a49daa45e2a4a92a4a92a4a92a4a92a4a92a4a92a427ea4a92a4a92a483ea4a92a4a92a4a90750f2a4a9038a929ea92a46698fa92a4a92a1a9013a92a4a900ea9165a7ea473ea454ea4a92a4a92a4a924fa92a4635aa8b2a46eaa4a92a4a92a4a92a477a4c8313ca19f92b2a41fc5619c4c49ea446a63a92a4a9017a911f75d22a90f0a92a4a92a4366a4a9
  | 3 => 0x1e4a92a46bc2ea92a47eaa4a92a46d6a4a912378aa465aa4a9128a92a42dea41c10e072a42e6a4a92a4a9082a92a4a9078169943d8e28267d51d4ca92a4a92a4a92a4a92a4a92a483816a92a4424c9a92a498a8aa55a2a90dca92a4385ffa907b4456c5186ea92a46f85e0a6a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4a921aa90535ea3463aa4a92a46c6a4a92a4a9073a92a4a908aa92a4a914fa92a4a92a4a92a4a92a4298d7a92a4a9085a9020412a413d41a90eaa92a410aa4a92a4a92a4a91caa90e0a92a4a92a44d035a92a4a92a4a9064a92a4a91a4a92a4a91122caa2542a4590a7a92a4a92a4a92a4806a4a9091a3aa4a92a4a9137a92a4a92a4a92a489ea4a92a4a91a8a90ab7d03a9e2a4a92a4462a4a92a4a92a4092a4226a4a92a4a92a4800215d066971690b101a929c38cd5928c769d4a2608d182a4a92a444294a92a4a92a4a92a4a92a4a92a4a92a4a924067ea4a91442f031a91d89246c701911189c8c5978197ba92a42faa4a908e240bda92a4a92a4a92a4a92a4a91327ce855d47c8c1ec456a484aa409ea4979b4a92a453aa49de835e6a406aa44300ca92a4a92a456ea4a912d55587a911da92a4a927230aa43ee42a90a4a9167a91f0722a43dd43a9184a92a4a92150da9a0764ea92a4a92a45baa4a92a4a92a408ea4552a4166a45c6a4a92a4952a4a90faa91b324d39a919ea92a4a92a47f2a4578d6a90446963e4b25da92a4842a4a92a41d0b1a9236a92a412aa4a9195a928476ea41dea47a2a459aa4a92a4a92a4a9180a92a4a925050000171d3a92a4a91c5a92a4a92a4786a44b8d1a923a775e5a0605a9076a92a44eea4a92296b454a9185a92a4a92a44e1028ad891f960a913f561ce2e2a41866e91aa4a91f2a92a4905d6a9239a9032a92a4486a4a9124a92a47b91e6ba53a92a4a92a4a927f922a426aa4a90225ad9da91312fea4682a4a91c2812a4a92a44aaa4a92a476aa41f5c4a92a41caa4a92a439869a92a4a92a4a92a44ad26a92a43e0a2a92a480c972cde0a92a4a92a4a90c
  | _ => 0
def u104K7 : Nat → Nat
  | 0 => 0xa45228741929454558a34a28d78a45228c08a330251461c5085140017229148a0308d148a148489f8a3dd645e8a45229148a45229145d45041148a45228b628c00ee434145229148a1b189148a4506c6b3023c94986f0e9c0f48a4512a04871a959148a28a280144bca26188a219344f8a45228718a266061f8a3f8af148a4522914050d5b4dc8a01d67148a23a28255dc5228818a45229148a450cf148a4517cf68a165011446c52291464c5228d004452283d62c515ed407198a1148a18cac7e8a45229148a450f1145bba1948375298a6e924451d6148a451151437bba291442452291419a7a29148a452291411c5229143430a2802814505a588a45229148a45229148a45228b08a45229148a451df14028458f14520edd88b27429f11443a758cb18a4060d148945228fc7eab9426d22b89c84d3e0e20e471e26d68fa5005888d6784502714180a19cd85c95229148a07a29148a45229148a272282b554522914113ee29148a25e29148a45229148a446291401c5034398a0f8e6a98a451cf148a45229148a2a208e68a45228ad8a09e29148a450fabd51c5229148a2d611142045038119003088600000110001000850000040846280062042228083080600800000421004202f40118c02004003016d5988740001bf8464a3ff4464a3bd8264a3bd0264a3bf8064a3ff4064a3df4a38a2ffc838a2bfc868a2bf4868a2bf4668a2bf4068a2ffc834a2ff4834a2bfc864a2ebc82882bf486882bf466882bf406882ff4a3482ff866482bf866482ff466482ff826482bf826482ff426482bf426482ff806482bf806482ff406482b7c66082b7466082bdc26082bd426082bec06082bf406082be406082fb482862bf486862bdc26862bd426862bf406862ff4a4462f74a3462f7483462fb882462ff482462fb482462bf8a6462ff4a6462bf4a6462bf886462ff486462bf486462bf806462ff406462ff482461bf486c41b7c66c41b7466c41bf406c41ff4a4460f74a3460f7483460ff8a2460ff4a2460ff882460ff482460f7462460bf8a6460ff4a6460bf4a6460bf886460ff486460ffc46460bfc46460bf846460ff446460bf046460ffc83c40ff483c40fb482c40fb462c40bfc86c40bf486c40bf466c40ff8a4440ff4a4440ff4a3440ffc83440ff483440fb8a2440fb4a2440ffc82440fb882440ff482440fb482440fb862440ff462440fb462440ff4a1440ffc81440ff481440ff461440fe4a0440fe480440bf8a6440ff4a6440bf4a6440ffc86440bfc86440bf886440ff486440bf486440bf086440bf866440ff466440bf466440bf826440ff426440bf426440fd4a3c20fd4a2c20fd482c20fd462c20ff482420bf846420fd4a3420fd8a2420fd4a2420fd882420fd482420fd082420fd862420fd462420fc460420fd846420fd046420
  | 1 => 0x7fa4629148a45229148a45229148a450c91404c5229148a4511029483552c758a4502f148a451267f8a452286e5396c5f14170dd705f8a4522914380fde2498a45157148a45229103d0981f14081ee285d3c994d25a8a1c983148632229143145129148a451242c0dc5228bc8a4511914031da29148a450c24c1a12e29148
  | _ => 0
def u104K8 : Nat → Nat
  | 0 => 0x1108c3511a42cdb87131225443c5120ebf00c5a861f10112712a93c11a01a041a7f4a3ff145fd28bfc417f482fe105fe18bfa317f461ff883fd107fa307fc40fe881f7083fa107d420
  | _ => 0
def u104K9 : Nat → Nat
  | 0 => 0x53f
  | _ => 0
def u104N : Nat → Nat
  | 3 => 1
  | 4 => 14
  | 5 => 128
  | 6 => 338
  | 7 => 138
  | 8 => 17
  | 9 => 1
  | _ => 0
def u104R : Nat → Nat → Nat
  | 3, i => packedAt u104K3 (i * 84) 84
  | 4, i => packedAt u104K4 (i * 71) 71
  | 5, i => packedAt u104K5 (i * 58) 58
  | 6, i => packedAt u104K6 (i * 45) 45
  | 7, i => packedAt u104K7 (i * 32) 32
  | 8, i => packedAt u104K8 (i * 19) 19
  | 9, i => packedAt u104K9 (i * 6) 6
  | _, _ => 0
def u104I : Nat → Nat → Nat
  | 3, h => packedAt u104K3 (85 + ((h / 1 + packedAt u104K3 (84 + (h % 1) * 1) 1) % 3) * 2) 2
  | 4, h => packedAt u104K4 (1018 + ((h / 8 + packedAt u104K4 (994 + (h % 8) * 3) 3) % 37) * 5) 5
  | 5, h => packedAt u104K5 (7819 + ((h / 79 + packedAt u104K5 (7424 + (h % 79) * 5) 5) % 406) * 9) 9
  | 6, h => packedAt u104K6 (16042 + ((h / 208 + packedAt u104K6 (15210 + (h % 208) * 4) 4) % 1450) * 10) 10
  | 7, h => packedAt u104K7 (4821 + ((h / 81 + packedAt u104K7 (4416 + (h % 81) * 5) 5) % 487) * 9) 9
  | 8, h => packedAt u104K8 (359 + ((h / 9 + packedAt u104K8 (323 + (h % 9) * 4) 4) % 37) * 6) 6
  | 9, h => packedAt u104K9 (7 + ((h / 1 + packedAt u104K9 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u104Pos : Nat → Bits
  | 1 => 0xfffffffffff1c3bf47f00700e0fc111300f33f
  | 2 => 0x200401440f8001f00629c4ccdcc
  | 4 => 0xfffffffffffc0c07987f000f001c8ce08f0e0f
  | 5 => 0x3078208000f01fe30f00f00ff0
  | 6 => 0x3f803f0000ffe003f000fff000
  | 7 => 0xfc000c00fff000003ffff000000
  | _ => 0
def u104Neg : Nat → Bits
  | 1 => 0xfffffffffff41400b800090021240011005115
  | 2 => 0xd7499144139256b2c20944cc54c
  | 4 => 0x2e18845031013065804a0850e0a
  | 5 => 0x28b020206425214d10f00900aa0
  | 6 => 0x9007500d8a4acc802f0006aa000
  | 7 => 0xa66002cc6c89083db4a000000
  | _ => 0
def u104Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,7),(0x3333333333333333333333333333333333333333333333333333333333333333,7),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7),(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,7),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,6),(0x000000000000000000000000ffffffff000000000000000000000000ffffffff,5),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,5),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,5),(0x000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5),(0x000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f,5),(0x00000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,5),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5),(0x00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f,5),(0x0000000033333333000000003333333300000000333333330000000033333333,4),(0x0000000000000000000000000000000033333333333333333333333333333333,4),(0x0000333300003333000033330000333300003333000033330000333300003333,4),(0x000000000000ffff000000000000ffff000000000000ffff000000000000ffff,4),(0x0000000000000000000000000000000000000000ffffffff00000000ffffffff,4),(0x0303030303030303030303030303030303030303030303030303030303030303,4),(0x0000000000000000333333333333333300000000000000003333333333333333,4)]
def u104Atlas : Atlas := ⟨9, rawDecor 246 u104Pos u104Neg, u104T, u104Slices, [swapRows 100,swapRows 117], u104N, u104R, u104I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_3_0 : Interval u104Atlas 3 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u104_3 : Interval u104Atlas 3 0 1 := blk_u104_3_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_4_0 : Interval u104Atlas 4 0 14 := block_range (n := 14) (by decide +kernel)
theorem all_u104_4 : Interval u104Atlas 4 0 14 := blk_u104_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_5_0 : Interval u104Atlas 5 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_5_32 : Interval u104Atlas 5 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_5_64 : Interval u104Atlas 5 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_5_96 : Interval u104Atlas 5 96 32 := block_range (n := 32) (by decide +kernel)
theorem all_u104_5 : Interval u104Atlas 5 0 128 := (concat (concat blk_u104_5_0 blk_u104_5_32) (concat blk_u104_5_64 blk_u104_5_96))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_0 : Interval u104Atlas 6 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_32 : Interval u104Atlas 6 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_64 : Interval u104Atlas 6 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_96 : Interval u104Atlas 6 96 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_128 : Interval u104Atlas 6 128 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_160 : Interval u104Atlas 6 160 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_192 : Interval u104Atlas 6 192 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_224 : Interval u104Atlas 6 224 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_256 : Interval u104Atlas 6 256 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_288 : Interval u104Atlas 6 288 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_6_320 : Interval u104Atlas 6 320 18 := block_range (n := 18) (by decide +kernel)
theorem all_u104_6 : Interval u104Atlas 6 0 338 := (concat (concat (concat blk_u104_6_0 blk_u104_6_32) (concat blk_u104_6_64 (concat blk_u104_6_96 blk_u104_6_128))) (concat (concat blk_u104_6_160 (concat blk_u104_6_192 blk_u104_6_224)) (concat blk_u104_6_256 (concat blk_u104_6_288 blk_u104_6_320))))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_7_0 : Interval u104Atlas 7 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_7_32 : Interval u104Atlas 7 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_7_64 : Interval u104Atlas 7 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_7_96 : Interval u104Atlas 7 96 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_7_128 : Interval u104Atlas 7 128 10 := block_range (n := 10) (by decide +kernel)
theorem all_u104_7 : Interval u104Atlas 7 0 138 := (concat (concat blk_u104_7_0 blk_u104_7_32) (concat blk_u104_7_64 (concat blk_u104_7_96 blk_u104_7_128)))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_8_0 : Interval u104Atlas 8 0 17 := block_range (n := 17) (by decide +kernel)
theorem all_u104_8 : Interval u104Atlas 8 0 17 := blk_u104_8_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u104_9_0 : Interval u104Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u104_9 : Interval u104Atlas 9 0 1 := blk_u104_9_0
theorem cert_u104 : Complete u104Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u104_3 i (by omega) hi
  · exact all_u104_4 i (by omega) hi
  · exact all_u104_5 i (by omega) hi
  · exact all_u104_6 i (by omega) hi
  · exact all_u104_7 i (by omega) hi
  · exact all_u104_8 i (by omega) hi
  · exact all_u104_9 i (by omega) hi
theorem b_u104 : Lower true (vars 246) u104T 10 := by
  have ready : Ready u104Atlas (asRow u104Pos) (asRow u104Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u104Atlas, u104Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u88
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u52
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u56
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u67
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u79
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u55
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u60
    · exact slice_correct (ms := fixRows 96 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u30
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u40
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u25
    · exact slice_correct (ms := fixRows 132 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u37
    · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u17
    · exact slice_correct (ms := fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u16
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u36
    · exact slice_correct (ms := fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u11
    · exact slice_correct (ms := fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
    · exact slice_correct (ms := fixRows 130 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u35
    · exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u9
    · exact slice_correct (ms := fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u22
    · exact slice_correct (ms := fixRows 164 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u43
    · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u8
    · exact slice_correct (ms := fixRows 66 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u24
  exact frozen ready cert_u104 (by decide +kernel) (by decide) [(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,32,36),(inputs.getD 4 zero,2,18),(inputs.getD 5 zero,2,34),(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,2,130)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u105 : Lower true (vars 222) u105T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 222) (T := u105T) (xs := [(inputs.getD 2 zero,128,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u63
  have hc : (([(inputs.getD 2 zero,128,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u106K4 : Nat → Nat
  | 0 => 0x1a324a26702a042282a8a12a28a14a28a28a16a28822a28a06428a28a28a18a00a287a8a28a28a28a28a0e806d0d29201d28d18ab8808426c064629642a109d01918a71868427406462cc518a01d19b28639868847406ca18e51a211d01b286c64680074a44a0b2912001d291282398484c7ca18808e612131f286182a30c84a4462460bc202109d18918370462407ca1460cc518931f285182398484c7ca1460f09291189281182720e84624a0460e0d2911892991822d4e8ca1886460
  | _ => 0
def u106K5 : Nat → Nat
  | 0 => 0x3414288272526ea0a0a0a084a0a0a01c9698a0a0a0a03c309a16a00ea0a0a0a0a05a2a2ea0a0a0a0a08660a0a0a0a026561a4a7ea09e90684c0492a0a0507848a03e5422a0a0a03646a0a018a0a0a0a0a0a074a08c124e5c1ea076a00200a05e0832649c0670382ca0a010a0a044a0a08ea0a0a0a0a0a0a0a0a0246c8aa08858a0a00c6a3aa0a07ca0a07aa0a0a0a0a0a0a080a0a0a0a06662a00aa042a0944020010002030005060bb0212212629ba338032524ed11c0192935d80d00c949678674064a4b3833a032525ae11d019292cf8ce00c949674670064a4b5a2380325271e19d29128f1e94900c9472f4870064a39da23803251f8e19d29118b869489468c5738074a3462bcc03a132316e509b01918ae68cf80c8c579427c06462b5c43a032315e509d01918b7298e8c5943b1462466ca19ec03a33650ee518901b2867b0ce80d943b9847406ca19cc23a03650ecd18919a2825f10e8cd141ce8074a44a0e7003a5225063c31d291283969488c4941d34a34624a09d863a3125063d2921992839694908c9413b8678464a09da33c232505ba01d2922027a98f9431018f4a44a68809dc23a5344063d2922992026f0ce94c9013b8474a6480be203e50c304f531f2861839c9489410c18f4a44a68609dc23a534304bc31d2911838e9489468c1e34a4462460f8a13a312307c518b285182ea8cf9428c17c407ca14609ea63e50a307c918a2811839c9489408c1d64a34a0460f92312502306cd18a2991831e94894c8c1b34624a646097c43a532304ee11d299183c68c510c8c1adca188646097c53c432304bd29e2191835a84f10c8c1f1462426460d6c432132306e731d189083e28c48c08416d887460420
  | _ => 0
def u106K6 : Nat → Nat
  | 0 => 0x1f2560bcf3e283c8a6161c13e7885f130ccd52d182593430dd23e7cf9f3e7c40fbe76a4e120069735025d3967c2903e44f8c8846115bd7c14da82a75f3a6cc47037cb06b872094211b04b00427a896241820bfc064a4bf8064a4bf0064a4ef8664a4ef4664a4efc064a4ef8064a4ef4064a4ef0064a4cf4a44a3bfc064a3bf8064a3bf0064a3eb4a4462f34a3462fb4a6462f9426462fbc06462fb406462f9462ca1bd466ca1bd406ca1fb4628a0bf4868a0bf4668a0df4a44a0cf4a44a0df4a34a0fb4624a0bf8864a0bf8664a0fb8464a0bb8464a0ef4a4880fdca1880bf4a6880bd426880ef4a4480fdca1480bf8a6480bf4a6480ef4a4860fdca1860fe4a0860bf4a6860bd426860ef4a4460f74a3460f3462460fdca1460fe8a0460fe4a0460bf8a6460bf4a6460ef886460af886460fd426460bd426460f9462420fd480420fd460420bd866420
  | _ => 0
def u106K7 : Nat → Nat
  | 0 => 0x609ce4b9c35b427739ce2b940321ce2284177c527f4a4de949fd28fda317dca1fa8c3fe283fa507f880fe901fe183fa307d420
  | _ => 0
def u106K8 : Nat → Nat
  | 0 => 0x143f
  | _ => 0
def u106N : Nat → Nat
  | 4 => 20
  | 5 => 80
  | 6 => 62
  | 7 => 14
  | 8 => 1
  | _ => 0
def u106R : Nat → Nat → Nat
  | 4, i => packedAt u106K4 (i * 58) 58
  | 5, i => packedAt u106K5 (i * 45) 45
  | 6, i => packedAt u106K6 (i * 32) 32
  | 7, i => packedAt u106K7 (i * 19) 19
  | 8, i => packedAt u106K8 (i * 6) 6
  | _, _ => 0
def u106I : Nat → Nat → Nat
  | 4, h => packedAt u106K4 (1172 + ((h / 6 + packedAt u106K4 (1160 + (h % 6) * 2) 2) % 57) * 6) 6
  | 5, h => packedAt u106K5 (3704 + ((h / 26 + packedAt u106K5 (3600 + (h % 26) * 4) 4) % 161) * 8) 8
  | 6, h => packedAt u106K6 (2084 + ((h / 20 + packedAt u106K6 (1984 + (h % 20) * 5) 5) % 79) * 7) 7
  | 7, h => packedAt u106K7 (282 + ((h / 4 + packedAt u106K7 (266 + (h % 4) * 4) 4) % 25) * 5) 5
  | 8, h => packedAt u106K8 (7 + ((h / 1 + packedAt u106K8 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u106Pos : Nat → Bits
  | 0 => 0xffffde1f7f8087fc0000c01ffff0201300ffff
  | 2 => 0x48034481461f0c082304d49cccb2cc
  | 3 => 0xffffc020009c001e87e0301043f718e0f0c30f
  | 4 => 0x23c08f6078e0f8003fe07c081f00ff03f0
  | 6 => 0x400f0007f0300003fff800fe000fffc00
  | 7 => 0x39ff007f8003ffffc000000fffff000000
  | _ => 0
def u106Neg : Nat → Bits
  | 0 => 0xffffc060802448000001400084100011001455
  | 2 => 0x3eebd95b76afce2f7cb9ef345494ccb2cc
  | 3 => 0x3f156a5b322fd6e23d5a73e518a0f0c30a
  | 4 => 0xc0670499524da44146079401d005503a0
  | 6 => 0x33980f92228b2598ab9f028fe000aae800
  | 7 => 0x480005021108204000aa24a000000
  | _ => 0
def u106Slices : List (Sig × Nat) := [(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,7),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,6),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6),(0x000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5),(0x00f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,5),(0x000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f,5),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,5),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,5),(0x00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f,5),(0x5555555555555555555555555555555555555555555555555555555555555555,5),(0x0505050505050505050505050505050505050505050505050505050505050505,4),(0x0055005500550055005500550055005500550055005500550055005500550055,4),(0x000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff,4),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,4)]
def u106Atlas : Atlas := ⟨8, rawDecor 221 u106Pos u106Neg, u106T, u106Slices, [], u106N, u106R, u106I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_4_0 : Interval u106Atlas 4 0 20 := block_range (n := 20) (by decide +kernel)
theorem all_u106_4 : Interval u106Atlas 4 0 20 := blk_u106_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_5_0 : Interval u106Atlas 5 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_5_32 : Interval u106Atlas 5 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_5_64 : Interval u106Atlas 5 64 16 := block_range (n := 16) (by decide +kernel)
theorem all_u106_5 : Interval u106Atlas 5 0 80 := (concat blk_u106_5_0 (concat blk_u106_5_32 blk_u106_5_64))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_6_0 : Interval u106Atlas 6 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_6_32 : Interval u106Atlas 6 32 30 := block_range (n := 30) (by decide +kernel)
theorem all_u106_6 : Interval u106Atlas 6 0 62 := (concat blk_u106_6_0 blk_u106_6_32)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_7_0 : Interval u106Atlas 7 0 14 := block_range (n := 14) (by decide +kernel)
theorem all_u106_7 : Interval u106Atlas 7 0 14 := blk_u106_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u106_8_0 : Interval u106Atlas 8 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u106_8 : Interval u106Atlas 8 0 1 := blk_u106_8_0
theorem cert_u106 : Complete u106Atlas := by
  intro k hk i hi
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u106_4 i (by omega) hi
  · exact all_u106_5 i (by omega) hi
  · exact all_u106_6 i (by omega) hi
  · exact all_u106_7 i (by omega) hi
  · exact all_u106_8 i (by omega) hi
theorem b_u106 : Lower true (vars 221) u106T 9 := by
  have ready : Ready u106Atlas (asRow u106Pos) (asRow u106Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u106Atlas, u106Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u68
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u65
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u81
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u74
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u64
    · exact slice_correct (ms := fixRows 132 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u42
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u41
    · exact slice_correct (ms := fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u18
    · exact slice_correct (ms := fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u19
    · exact slice_correct (ms := fixRows 80 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u32
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u29
    · exact slice_correct (ms := fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
    · exact slice_correct (ms := fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u13
    · exact slice_correct (ms := fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u14
    · exact slice_correct (ms := fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u23
    · exact slice_correct (ms := fixRows 140 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u44
  exact frozen ready cert_u106 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u107 : Lower true (vars 219) u107T 8 :=
  lower_map (ms := [swapRows 80,swapRows 65,swapRows 82,swapRows 83]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u103
def u108K7 : Nat → Nat
  | 0 => 0x4113dc317b462
  | _ => 0
def u108K8 : Nat → Nat
  | 0 => 0x53f
  | _ => 0
def u108N : Nat → Nat
  | 7 => 2
  | 8 => 1
  | _ => 0
def u108R : Nat → Nat → Nat
  | 7, i => packedAt u108K7 (i * 19) 19
  | 8, i => packedAt u108K8 (i * 6) 6
  | _, _ => 0
def u108I : Nat → Nat → Nat
  | 7, h => packedAt u108K7 (39 + ((h / 1 + packedAt u108K7 (38 + (h % 1) * 1) 1) % 4) * 3) 3
  | 8, h => packedAt u108K8 (7 + ((h / 1 + packedAt u108K8 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u108Pos : Nat → Bits
  | 0 => 0xfffffffffff81c678411c0180e3f081303333f
  | 1 => 0x6098086e00e0f1c0109c0dcdcc
  | 3 => 0xfffffffffff8800092484f00000f64e0ce0e0f
  | 4 => 0x7031f638fb00701f08700f00ff0
  | 6 => 0x3e003f00007fe00f800fff000
  | 7 => 0x7fc007c003ff80000ffff000000
  | _ => 0
def u108Neg : Nat → Bits
  | 0 => 0xfffffffffff981003080002812510011011115
  | 1 => 0x387214300016832d3009405454c
  | 3 => 0x67eeb0248174365ae24a0ce0e0a
  | 4 => 0x28c00c70120101240500500aa0
  | 6 => 0x4501e800aac96cc08f800aaa000
  | 7 => 0x14800568948800da4a000000
  | _ => 0
def u108Slices : List (Sig × Nat) := [(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,7),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,7),(0x3333333333333333333333333333333333333333333333333333333333333333,7),(0x5555555555555555555555555555555555555555555555555555555555555555,7),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,6),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,6),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,6)]
def u108Atlas : Atlas := ⟨8, rawDecor 219 u108Pos u108Neg, u108T, u108Slices, [swapRows 112,swapRows 97], u108N, u108R, u108I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u108_7_0 : Interval u108Atlas 7 0 2 := block_range (n := 2) (by decide +kernel)
theorem all_u108_7 : Interval u108Atlas 7 0 2 := blk_u108_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u108_8_0 : Interval u108Atlas 8 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u108_8 : Interval u108Atlas 8 0 1 := blk_u108_8_0
theorem cert_u108 : Complete u108Atlas := by
  intro k hk i hi
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u108_7 i (by omega) hi
  · exact all_u108_8 i (by omega) hi
theorem b_u108 : Lower true (vars 219) u108T 9 := by
  have ready : Ready u108Atlas (asRow u108Pos) (asRow u108Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u108Atlas, u108Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u93
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u83
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u65
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u76
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u72
    · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u70
  exact frozen ready cert_u108 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u109 : Lower true (vars 215) u109T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := vars 215) (T := u109T) (xs := [(inputs.getD 0 zero,16,17)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u67
  have hc : (([(inputs.getD 0 zero,16,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u110K4 : Nat → Nat
  | 0 => 0x90510c99c33a036514b431d291082f080f944841cc4a44a0420
  | _ => 0
def u110K5 : Nat → Nat
  | 0 => 0x21d4a328aa40d220282a5294a523ed8264a4bb466ca2bb406ca2cf4a44a0b78664a0ed4a4420f9ca2420fc4a0420ed886420f9446420
  | _ => 0
def u110K6 : Nat → Nat
  | 0 => 0x47076513721bd293fa51fbca2f68c5fd283da207d420
  | _ => 0
def u110K7 : Nat → Nat
  | 0 => 0x113f
  | _ => 0
def u110N : Nat → Nat
  | 4 => 4
  | 5 => 10
  | 6 => 7
  | 7 => 1
  | _ => 0
def u110R : Nat → Nat → Nat
  | 4, i => packedAt u110K4 (i * 45) 45
  | 5, i => packedAt u110K5 (i * 32) 32
  | 6, i => packedAt u110K6 (i * 19) 19
  | 7, i => packedAt u110K7 (i * 6) 6
  | _, _ => 0
def u110I : Nat → Nat → Nat
  | 4, h => packedAt u110K4 (181 + ((h / 1 + packedAt u110K4 (180 + (h % 1) * 1) 1) % 7) * 4) 4
  | 5, h => packedAt u110K5 (326 + ((h / 3 + packedAt u110K5 (320 + (h % 3) * 2) 2) % 21) * 5) 5
  | 6, h => packedAt u110K6 (135 + ((h / 2 + packedAt u110K6 (133 + (h % 2) * 1) 1) % 10) * 4) 4
  | 7, h => packedAt u110K7 (7 + ((h / 1 + packedAt u110K7 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u110Pos : Nat → Bits
  | 0 => 0xffff9c3f8047e0020872381fffc082932673ff
  | 1 => 0x20c001b8010c0f8dcfe01801531cdb9ccc
  | 2 => 0x20e000e0ff001f000e02663e0e3e0f0
  | 3 => 0xffffc300f001f7f0000e0000fff87c00fc00ff
  | 6 => 0x403003e1800000fffff003f8000ffff00
  | 7 => 0x7bfc7fc01ffffff00000003fffff000000
  | _ => 0
def u110Neg : Nat → Bits
  | 0 => 0xffffc30012ca200618b0582328c00291023155
  | 1 => 0x4d0727da631e2b94d8e1794053144a94cc
  | 2 => 0x7e5a6ffeff2ef92ff946faa263a0e3e0f0
  | 3 => 0x3caf6d34df78420fa288d7287400fc00aa
  | 6 => 0x30f0c8249cc1844b271c843f8000b54a00
  | 7 => 0x80010081044004100015884a000000
  | _ => 0
def u110Slices : List (Sig × Nat) := [(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,6),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,6),(0x3333333333333333333333333333333333333333333333333333333333333333,6),(0x0303030303030303030303030303030303030303030303030303030303030303,5),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5),(0x5555555555555555555555555555555555555555555555555555555555555555,5),(0x0505050505050505050505050505050505050505050505050505050505050505,4),(0x000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4),(0x0055005500550055005500550055005500550055005500550055005500550055,4)]
def u110Atlas : Atlas := ⟨7, rawDecor 207 u110Pos u110Neg, u110T, u110Slices, [], u110N, u110R, u110I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u110_4_0 : Interval u110Atlas 4 0 4 := block_range (n := 4) (by decide +kernel)
theorem all_u110_4 : Interval u110Atlas 4 0 4 := blk_u110_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u110_5_0 : Interval u110Atlas 5 0 10 := block_range (n := 10) (by decide +kernel)
theorem all_u110_5 : Interval u110Atlas 5 0 10 := blk_u110_5_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u110_6_0 : Interval u110Atlas 6 0 7 := block_range (n := 7) (by decide +kernel)
theorem all_u110_6 : Interval u110Atlas 6 0 7 := blk_u110_6_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u110_7_0 : Interval u110Atlas 7 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u110_7 : Interval u110Atlas 7 0 1 := blk_u110_7_0
theorem cert_u110 : Complete u110Atlas := by
  intro k hk i hi
  change k ≤ 7 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u110_4 i (by omega) hi
  · exact all_u110_5 i (by omega) hi
  · exact all_u110_6 i (by omega) hi
  · exact all_u110_7 i (by omega) hi
theorem b_u110 : Lower true (vars 207) u110T 8 := by
  have ready : Ready u110Atlas (asRow u110Pos) (asRow u110Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u110Atlas, u110Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u85
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u76
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u74
    · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u21
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u77
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u75
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u73
    · exact slice_correct (ms := fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u20
    · exact slice_correct (ms := fixRows 132 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u46
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u45
    · exact slice_correct (ms := fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u22
  exact frozen ready cert_u110 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,64,66),(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,1,9),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u111 : Lower true (vars 175) u111T 7 := by
  have h := lift_ok (u := true) (ms := fixRows 38 0) (raw := vars 175) (T := u111T) (xs := [(inputs.getD 1 zero,32,34),(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u2
  have hc : (([(inputs.getD 1 zero,32,34),(inputs.getD 2 zero,32,36),(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by decide +kernel
  rwa [hc] at h
def u112K3 : Nat → Nat
  | 0 => 0x1315442955554740ed55860a4a04880a7446420c249408d014e88c84198120d3a328920108324250244053a232106504a04680a7446420
  | _ => 0
def u112K4 : Nat → Nat
  | 0 => 0x2eb162c58b162c0fa4fac584cd2c58b162c582562c58b102c15a3621d8b162c3b3d3c2d8b162c58b162c03b162c580d62c58b11113c9462c39b162c0bb162c486d62c58b160cd82d56c58b162c58b162c582361914b160058b1582586162c58b1316d8b162c58b162c58b126c58b09ec58b00ac58b162c58b162c58b162c534362c5897628465eeac58aed6c58b0dd1a00362c58b162c58b05ec58b162c58b162c58b152c0a9c4ec58b162c585362c58b162c58b0c6c47b0b1558b162c5849062d8b162c58b01c41cb162c38b161ed85162c103562c33b03ac42b162c58b0fc48db030052011c1214838cd22219d01b28a338684078464a18ce1a101f299106398284878464a08e60a131f2892038a4a44464a04808e60a121f2991022b8884c7ca24208ce1a131f2890831a4a00a74464208ad22029d119082334680a74464209e102211d291082398c8487ca2420dc120d01f28908278888407ca2420dc21a101f289082698884c7ca24209c61a131f289082788084c7ca2420aa432129120908278408ca7482420f1129120d281082740e84834a0420f21291209281083e0483ca2480420ba1223289201082784e8ca2480420d9120e29d201083644834a7480420f8120d11d2010834c4a04870a6420d5128119c299083e0483480446420e61282299119082a90884a64464209e102329d119083584a00a74464209a522029d119082714680a74464209e102029d11908361483887446420da120221d11908278808487446420
  | _ => 0
def u112K5 : Nat → Nat
  | 0 => 0x42d35ba1d946cdbbd71a4034c73cb8c0aae7966d616d6d6d6d2fed6d18ed153609aced2720116d10c9aec46d2e3c526d6814ed6d13b5ed6d6d6d6d63ed3d9ded0b41b9ed6d0eed1d492b4ca658b53e973291cf48dd02d4dd8e6d6d325a68ed37ed00e1b195ed0d9926c6606d6d17a963565b6d25ed4b3a6d6d6d0b87924c5aeb6d6d6d6a1cce106d3aed649f875857cbed6d04ed6d4ac30f9f69069c6d66dcb02f6d6d6d5f2a186d6d6d65890a08c7d16b8ae2ed6c3d0c1bd56d6d6d0331211ec55fa7e66d28ed4d23141e670169ed0ced6d6d59c26096a8064381a2ed6d6d6d6d25085465391b458d6d6d3e243fdc6d046aed6d6d12b34a24ed33de023f6d6d2bceb6aded2c6223999ac86d6d502d6d6d6d0f38298505e46d50ed6d6d3b03b7136cc144806d6d6d6d6d6d225eed346d6d6d6d6d102232de0080050046654802200600886001813008022af00180a000002000a0010c538ca00884c0202258173b807426ca2b9c33a036514ee21d01b28b670ce80d94533867406ca29dc13a036514de19d01b2867680f08c9433b8478064a1bcc03a50a20ced01f2991067b04e90d9413b8478864a0d9e514332506cd1061992826e90f0cc941b38478664a0d9c334232504ed21e1192827684f08c9413b8478264a0bd203e512404ed31f2892039c948940901ba4464a04809dc23e532404ed11e2992027708e94c9013d8274a64809da238532404f509c299202f304e948881da4a44a0440f9433a502204ed21f2991027684f94c88179427ca2420bd203e512104ed31f289082f308e94284179ca7441420fc220a502106772862990837288314c8413b4478a6420dca20a532104be21d2990826f0ce94c8413b8474a642097a438532104dd19c2990827688e14c841b94a1446420dd2502232104ef29d1190827614e88c8417c407ca4420bcc23a522104f631d2910827a18e948841f1483ca2420bca43e512107e101f289082f080f944841794c7ca2420f4a522412105e729d209083b9948940841dc4a44a0420fa241a502107e3289281083f09049408417c8874a0420fa433a502107e211d281083d8948900841e4483480420fc6512402105f229d201082f894e900841f8447480420be203e532107712822990833b94d14c841794478a6420b6c43a532105b421d299082eb0ce94c841798474a6420be403a53210771280299082db90e14c8416d4870a6420baa338532105e511c299082f880e14c841e5483886420f4a414432107b1202219082f288f10c841f1483446420fc2502232107e12011190837314c88c841b94a6446420bce53a232105e429d119082f310e88c84179487446420
  | _ => 0
def u112K6 : Nat → Nat
  | 0 => 0xf5ebd3b7db2afaf473d05f5e9efa07497dbf41fd1a4feac89dd27a157344db2f5e99fa1e1080bec056b848afd00f50a428f5ebd2af5ebd7a3c67d7af48bd6fefebd7abc47d5adb1056a81ebd7af5ea67a25c3d7ad1a79cdf5e3d7af5e90d3f5eb323f5e907a1c75288c51b5fa9fea87a3187d7af4f3cfaac598e06e37d7af4b3d34269811ff4eaffaf453286f5e97759dcb8e3f52bd7a61eabd8a99fd7af5ebd5cf5ebd6453e9b0cf49000650904719002001200802160000100000020810001fb426ca2bb426ca2fb406ca2bb406ca2bf406ca1fbca24a1fb8464a1bb8464a1bf8064a1f94a1441bbca6441bf486ca0bf426ca0dfca44a0df4a44a0fbca24a0fb4414a0bf8864a0f78664a0b78664a0fb8464a0bb8464a0bf8264a0fbca2480fe4a0480bfca6480bf8a6480bf4a6480bf0a6480fb446480fb4a4440fb4a1440fa4a0440bbca6440bb486440f9ca2c20fbca2420fdca1420fd4a1420f9441420fe4a0420bfca6420bf8a6420bf4a6420bf0a6420fb446420bb446420fdca4420fd4a4420f5483420f9ca2420f9482420fc4a0420fc480420fdca6420fd8a6420fd4a6420fd0a6420fd886420fd486420f9446420
  | _ => 0
def u112K7 : Nat → Nat
  | 0 => 0x2d6b5ad6b5ad66dad6190f685ac1b5ad155a65a2c1695ac8b0ad6759f6332c01e001ef28bfe50ff4a1f6883ff283fa507f480f6881f7083fa107d420
  | _ => 0
def u112K8 : Nat → Nat
  | 0 => 0x113f
  | _ => 0
def u112N : Nat → Nat
  | 3 => 5
  | 4 => 44
  | 5 => 109
  | 6 => 61
  | 7 => 11
  | 8 => 1
  | _ => 0
def u112R : Nat → Nat → Nat
  | 3, i => packedAt u112K3 (i * 71) 71
  | 4, i => packedAt u112K4 (i * 58) 58
  | 5, i => packedAt u112K5 (i * 45) 45
  | 6, i => packedAt u112K6 (i * 32) 32
  | 7, i => packedAt u112K7 (i * 19) 19
  | 8, i => packedAt u112K8 (i * 6) 6
  | _, _ => 0
def u112I : Nat → Nat → Nat
  | 3, h => packedAt u112K3 (361 + ((h / 3 + packedAt u112K3 (355 + (h % 3) * 2) 2) % 19) * 4) 4
  | 4, h => packedAt u112K4 (2606 + ((h / 27 + packedAt u112K4 (2552 + (h % 27) * 2) 2) % 259) * 7) 7
  | 5, h => packedAt u112K5 (5255 + ((h / 70 + packedAt u112K5 (4905 + (h % 70) * 5) 5) % 308) * 8) 8
  | 6, h => packedAt u112K6 (2137 + ((h / 37 + packedAt u112K6 (1952 + (h % 37) * 5) 5) % 193) * 7) 7
  | 7, h => packedAt u112K7 (233 + ((h / 6 + packedAt u112K7 (209 + (h % 6) * 4) 4) % 49) * 5) 5
  | 8, h => packedAt u112K8 (7 + ((h / 1 + packedAt u112K8 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u112Pos : Nat → Bits
  | 0 => 0xfff0e01f800c3f8004232383fff002932673ff
  | 1 => 0x100600073c001183cdcfc0600531cdb9ccc
  | 2 => 0x1038000261fc01f00380a63e0e3e0f0
  | 3 => 0xfff201801c0007c7e000e0003ffc7c00fc00ff
  | 4 => 0xc3e01e003f8780000ffffc00f8000ffff00
  | 7 => 0xfdffe7ffc007fffff0000000fffff000000
  | _ => 0
def u112Neg : Nat → Bits
  | 0 => 0xfff60780249448800c670584ca300291023155
  | 1 => 0xe7a8389b4c9833cbd4d9c5e5053144a94cc
  | 2 => 0xfed2d5bb5dbef5feaffa9beaa63a0e3e0f0
  | 3 => 0x9f057db219377f110fa5235cc7400fc00aa
  | 4 => 0x180785249127c8200b263210e8000b54a00
  | 7 => 0x22400000000000001084a000000
  | _ => 0
def u112Slices : List (Sig × Nat) := [(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,6),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,6),(0x3333333333333333333333333333333333333333333333333333333333333333,6),(0x5555555555555555555555555555555555555555555555555555555555555555,6),(0x0033003300330033003300330033003300330033003300330033003300330033,5),(0x0055005500550055005500550055005500550055005500550055005500550055,5),(0x0000333300003333000033330000333300003333000033330000333300003333,5),(0x00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f,5),(0x0303030303030303030303030303030303030303030303030303030303030303,5),(0x0505050505050505050505050505050505050505050505050505050505050505,5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4)]
def u112Atlas : Atlas := ⟨8, rawDecor 159 u112Pos u112Neg, u112T, u112Slices, [swapRows 64,swapRows 49], u112N, u112R, u112I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_3_0 : Interval u112Atlas 3 0 5 := block_range (n := 5) (by decide +kernel)
theorem all_u112_3 : Interval u112Atlas 3 0 5 := blk_u112_3_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_4_0 : Interval u112Atlas 4 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_4_32 : Interval u112Atlas 4 32 12 := block_range (n := 12) (by decide +kernel)
theorem all_u112_4 : Interval u112Atlas 4 0 44 := (concat blk_u112_4_0 blk_u112_4_32)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_5_0 : Interval u112Atlas 5 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_5_32 : Interval u112Atlas 5 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_5_64 : Interval u112Atlas 5 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_5_96 : Interval u112Atlas 5 96 13 := block_range (n := 13) (by decide +kernel)
theorem all_u112_5 : Interval u112Atlas 5 0 109 := (concat (concat blk_u112_5_0 blk_u112_5_32) (concat blk_u112_5_64 blk_u112_5_96))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_6_0 : Interval u112Atlas 6 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_6_32 : Interval u112Atlas 6 32 29 := block_range (n := 29) (by decide +kernel)
theorem all_u112_6 : Interval u112Atlas 6 0 61 := (concat blk_u112_6_0 blk_u112_6_32)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_7_0 : Interval u112Atlas 7 0 11 := block_range (n := 11) (by decide +kernel)
theorem all_u112_7 : Interval u112Atlas 7 0 11 := blk_u112_7_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u112_8_0 : Interval u112Atlas 8 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u112_8 : Interval u112Atlas 8 0 1 := blk_u112_8_0
theorem cert_u112 : Complete u112Atlas := by
  intro k hk i hi
  change k ≤ 8 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u112_3 i (by omega) hi
  · exact all_u112_4 i (by omega) hi
  · exact all_u112_5 i (by omega) hi
  · exact all_u112_6 i (by omega) hi
  · exact all_u112_7 i (by omega) hi
  · exact all_u112_8 i (by omega) hi
theorem b_u112 : Lower true (vars 159) u112T 9 := by
  have ready : Ready u112Atlas (asRow u112Pos) (asRow u112Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u112Atlas, u112Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u83
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u85
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u84
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u81
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u80
    · exact slice_correct (ms := fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u31
    · exact slice_correct (ms := fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u30
    · exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u32
    · exact slice_correct (ms := fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u33
    · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u29
    · exact slice_correct (ms := fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u28
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u82
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u48
  exact frozen ready cert_u112 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u113 : Lower true (vars 125) u113T 8 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := vars 125) (T := u113T) (xs := [(inputs.getD 3 zero,1,9)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u89
  have hc : (([(inputs.getD 3 zero,1,9)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u114 : Lower true (vars 123) u114T 8 :=
  lower_map (ms := [swapRows 80,swapRows 65,swapRows 82,swapRows 83,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u103
theorem b_u115 : Lower true (vars 123) u115T 8 :=
  lower_map (ms := [swapRows 112,swapRows 97,swapRows 50,swapRows 116,swapRows 101,swapRows 118]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u109
theorem b_u116 : Lower true (vars 119) u116T 8 :=
  lower_map (ms := [swapRows 112,swapRows 115]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u103
theorem b_u117 : Lower true (vars 119) u117T 8 :=
  lower_map (ms := [swapRows 100,swapRows 117]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u109
theorem b_u118 : Lower true (vars 111) u118T 8 :=
  lower_map (ms := [swapRows 80,swapRows 65,swapRows 50]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u113
def u119K6 : Nat → Nat
  | 0 => 0x143f
  | _ => 0
def u119N : Nat → Nat
  | 6 => 1
  | _ => 0
def u119R : Nat → Nat → Nat
  | 6, i => packedAt u119K6 (i * 6) 6
  | _, _ => 0
def u119I : Nat → Nat → Nat
  | 6, h => packedAt u119K6 (7 + ((h / 1 + packedAt u119K6 (6 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u119Pos : Nat → Bits
  | 0 => 0xffee7c061fc412041e31c0ffff1106932673ff
  | 1 => 0x118039e0086c07e1ce7f00c0229b1cdb9ccc
  | 2 => 0xbc000338ff8000f800700cce3e0e3e0f0
  | 3 => 0xffe1000003c3f00001f00007fff0fc00fc00ff
  | 4 => 0x20c01fc3c000001fffff800ff0000ffff00
  | 5 => 0x1df3fe003ffffffe00000000ffffff000000
  | _ => 0
def u119Neg : Nat → Bits
  | 0 => 0xffe0004a2440060c2602c11943000291023155
  | 1 => 0x61cda64c0ae14e246c70bc5008b144a94cc
  | 2 => 0x1fe9daedd1ae7c44dfca37ca44a3a0e3e0f0
  | 3 => 0x1f3fb5dbbff8a189fd1446bcf0fc00fc00aa
  | 4 => 0x19c3259b3f514211b938e410ff0000b54a00
  | 5 => 0x225122e51831920208020bb544a000000
  | _ => 0
def u119Slices : List (Sig × Nat) := [(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,5),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,5),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,5),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5),(0x3333333333333333333333333333333333333333333333333333333333333333,5),(0x000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f,4),(0x5500550055005500550055005500550055005500550055005500550055005500,4)]
def u119Atlas : Atlas := ⟨6, rawDecor 63 u119Pos u119Neg, u119T, u119Slices, [swapRows 80,swapRows 65,swapRows 50], u119N, u119R, u119I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u119_6_0 : Interval u119Atlas 6 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u119_6 : Interval u119Atlas 6 0 1 := blk_u119_6_0
theorem cert_u119 : Complete u119Atlas := by
  intro k hk i hi
  change k ≤ 6 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u119_6 i (by omega) hi
theorem b_u119 : Lower true (vars 63) u119T 7 := by
  have ready : Ready u119Atlas (asRow u119Pos) (asRow u119Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u119Atlas, u119Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u101
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u100
    · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u99
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u98
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u97
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u96
    · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u49
    · exact slice_correct (ms := fixRows 1 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u47
  exact frozen ready cert_u119 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u120 : Lower true (vars 254) u120T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 8 0) (raw := vars 254) (T := u120T) (xs := [(inputs.getD 3 zero,128,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u104
  have hc : (([(inputs.getD 3 zero,128,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u121 : Lower true (vars 253) u121T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 4 0) (raw := vars 253) (T := u121T) (xs := [(inputs.getD 2 zero,32,36)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u102
  have hc : (([(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u122 : Lower true (vars 251) u122T 9 := by
  have h := lift_ok (u := true) (ms := fixRows 160 0) (raw := vars 251) (T := u122T) (xs := [(inputs.getD 5 zero,0,32),(inputs.getD 7 zero,0,128)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u92
  have hc : (([(inputs.getD 5 zero,0,32),(inputs.getD 7 zero,0,128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
theorem b_u123 : Lower true (vars 251) u123T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 2 0) (raw := vars 251) (T := u123T) (xs := [(inputs.getD 1 zero,16,18)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u102
  have hc : (([(inputs.getD 1 zero,16,18)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u124 : Lower true (vars 247) u124T 9 :=
  lower_map (ms := [swapRows 80,swapRows 65,swapRows 50]) (by decide +kernel) (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u122
theorem b_u125 : Lower true (vars 247) u125T 11 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := vars 247) (T := u125T) (xs := [(inputs.getD 0 zero,16,17)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u104
  have hc : (([(inputs.getD 0 zero,16,17)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
theorem b_u126 : Lower true (vars 239) u126T 10 := by
  have h := lift_ok (u := true) (ms := fixRows 6 0) (raw := vars 239) (T := u126T) (xs := [(inputs.getD 1 zero,32,34),(inputs.getD 2 zero,32,36)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u58
  have hc : (([(inputs.getD 1 zero,32,34),(inputs.getD 2 zero,32,36)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  rwa [hc] at h
def u127K4 : Nat → Nat
  | 0 => 0x12301827125294a5284a4892b818544a940a4290e84834c0c86244a15074a62a60240413452d3a12243a1315082d0821681498a988906841a844c44aa1094834c04208f0435c45274e612402106a1131622a1a53212010825c10d6a1598490110e84130c4ab0ea4c44c0487420
  | _ => 0
def u127K5 : Nat → Nat
  | 0 => 0xa0e94834874c0e864c54838084874c0c4d4884290e84c5480b0746a0e94c54c4480b0d42a0e94c54c4480d0e4890e94c54c0480b1646a0e94c54c0480b1c42a0e94c54c0480d864c5d094834c0480d864c51094834c0480ac64aa1094834c0480ae442a1094834c0480e864c54838084c7480d074c58898684c7480f064c54838084c7480e0e4c58888084c748099c80a4c9ce84c542099c8ca8094e84c5420a4d08a4e80e84c542085d92a4e80e84c5420ccc4084890e84c5420c4d4e84890e84c5420cd44084690e84c5420b8c40a8894c54c4420d8c8894094c54c4420b8c88a4094c54c4420d8c4c58894084c4420c9c4c54098e84c4420ad410a4094c5483420f8440a4c54c4483420f844c54094c4483420f844c54c4808483420ee0483409488cc24208f840a8e9488cc2420ee0483489408cc2420af086a489408cc24208f186a8894e8cc24208f148a8694e8cc2420b1c8ea4894c54c0420b1c0ea4894c54c0420d1cce98e94c54c0420b8c88a4e94c54c0420b8c08a4e94c54c0420b9486a4e94c54c0420b8cc8a0e94c54c0420b8c48a0e94c54c0420b9446a0e94c54c0420a9cd0a0e94c54c042099c4aa0e94c44c04209b446a0e94c44c0420d944c5d094834c0420da44c4d094834c0420ea44c49094834c04208f4d2a9094834c0420d944c51094834c0420da44c41094834c0420ea44c41094834c0420ad44aa1094834c0420cd44aa1094834c0420c74cea1094834c0420f844c54834884c0420d944c58694884c0420e944c54888684c04208f492a4888684c0420d944c54898684c0420a9c4cad094c5480420a9c8ca5094c54804209cc4aa0e94c44804209e446a0e94c4480420de04834e9cc24804209e888a4e9cc24804209f086a4e9cc2480420de0483509cc24804209f086a509cc2480420ce0483509cc2480420cf086a509cc2480420ce492a4838c8480420f844c54834c8480420d8c4c58894c84804209e488a8694c8480420e844c54834c8480420e8c4c58894c8480420e944c58694c8480420ae488a8694c8480420c9c4c08a94888c7420b0d48a0e94c54c7420b1546a0e94c54c7420f844c54834804c7420ae410a4834804c7420e8c4c54808884c7420c9c4c58098884c7420ce44808898684c7420e944c58688084c7420e944c54838084c7420ea44c44838084c7420c9c4c54898084c74208f186a509cc2887420b684eacc2480887420ae850acc2480887420f0c4c54804c7887420e8c4c54804c8887420ce44808694c8887420c9c4c58094c888742094d4aa0e94c44874208f186a509cc24874208f880a509cc2487420a9c10a4c54c0487420b2c0ea4c44c0487420c9c4c58094c8487420ad840acc28a84874208d952acc28a8487420c9c4c08c98a8487420ad880a4498a8487420cd88a8809448487420
  | 1 => 0xcdededededededededecbcf0952d91adeded2460f4f9edc9edece82859b4b0897530653c909c15edededbc5d35ec482deded218ded9c4149580dededededed64983045ed7d51d5a9a4adb1146da0b5ededec8c69ededed29eded09edec5180a9ecd4c018d1ed89eca009ededec39edcdededed6d85ec85c5eded1011edede001ece0dded79ed19e9edec3cb994c501ed4d41edecfdededec78ededede5eca47545ec0571ec7ded99edededb9ec4d601dedec21edededd1d9eded55ec255ded38d8c969ec35ec55ed0ce5c105ededdc70811c5084400880101c20080020dc240844000c4300805000c04004198786a4098884c54c4b078ea4094c54c4483b070ea4094c54c4483d074c58e94084c448399c82a4898084c54c0d074c44a90e84834c0d254c44290e84834c0c554a94290e84834c0a7440a4290e84834c0867d
  | _ => 0
def u127K6 : Nat → Nat
  | 0 => 0x102531520d083c2a62a62241a107e44094c4483420f4a989190906841f5131602120d083f2262404241a105f44098e8483420dc2906911984841be10252233090827cc74a446612106f0483408cc24209f1112811984841be122502330908378a41a746612104f98894e8cc2420de30d29d19848413c61a53a330908278a34c7424121079c8894c54c0420f3891298a980841e733a5315301083ce474a62a6021079c4e94c54c0420f381d298a9808416f33a5311301082de074a622602107944c54834c0420f489889069808417d342520d3010837a484a41a602105f41094834c0420de82129069808413d042520d301083ce262c442602107ac4c48884c0420d3898b110980841e71315221301083f2241a442602105f48694884c0420f2898b0d0980841ed13121a13010837a2444342602105f44898684c0420f9891298a900841b734253152010836e284a62a4021078c4c54c4480420bd99d29889008417b03a5311201083e2262a41a402107e48c9483480420fc91d2906900841f903a520d201083f0241e612402105e8489cc2480420bf09d39849008417e14273092010827c284e612402106e44838c84804209f99d3190900841e71315321201083f2241a642402105ec8894c8480420be90d2990900841a7131532120108372241a642402106ec8894c8480420de90d2990900841f8120d121201083da241a60463a107b48694c08c7420fc890690118e841af130122231d0826ec54a44463a1079c4094c54c7420e3b1d298a98e841c743a531531d083caa62a41a63a107a54c44834c74209ea21290698e841e7131520131d083d6262240263a107e44834804c7420d3a98b11098e841bb120222131d0827e404c44263a107954c58684c7420de89010d098e8413d62261a131d0827aa44c34263a106f44098684c7420f3898b01098e841bd21a202131d0834e262c04263a106bc4c48084c7420de890701098e8413f122602131d082fc204e61443a105794e9cc28874209f2a1398510e841e7131530221d083e6262a40443a107e8cc2480887420fd089290110e841c7531531e21d083b6240263c43a1069d4c54c8887420dd890099110e8413d61a532221d0827e404a64443a104dd1094c5487420f1a98a98890e8415b43a531121d082f4a44e61243a105f8409cc2487420af29d398490e8413e542730921d083ce262a60243a107ac4c44c0487420e7898118e90e841c7531531d21d08396a62263a43a106bc4c08c8487420d3a98a99090e8413762a532121d0827ac34a64243a104fc8094c8487420db398515090e841b713022a121d0826ec64c54243a104dd4c98a8487420db289315090e841b662a112121d082fc404a24243a104f8809448487420fc090690088e8417662a521d11d08374240444223a106e9487888447420
  | 1 => 0x928118728208624400904c0009af0d281110e98b27e3251a121d3166ec14a34243a62cde8094684874c59ba81305090e98b3760a522201d3166ba44c34203a62d8f8698884c54c4b1e8d311098a98963d026221315312c7c44a34262a6268f8888084c54c4d1f11081098a98963e225021315312cbc34a04262a6268f4c58884074c4d2e98b0d080e98947d3273a131520f87874a62a62241d578e94084c5483aae1d281098a90765d3273a131520fc3c04a62a62241f874094c54c4483f0f9d298a988907e1c3a531531120fc3a62c04262241e874c58084c4483f0e98a81098890759e3a502131120fc3a62a62403a41e63483808487cc2ec690681090f9855ce1a502121f30bb1a41a44203e61573869488407cc28e69130d080f9856760a5221315302cf404a44262a6069e8888084c54c0d3c91101098a981679226021315303cb404a62a41a607a68094c44834c0d2e98b9d0906981a9d3133a120d30393a62474241a60477d098e84834c0d2e98a1d0906981a9d3103a120d30393a62074241a605574a90e84834c0aea8521d090698195d2a43a120d3033aa14874241a607874c54834874c0ace1d290690e981a5d3161a121d3034f262c04243a606e64838084874c0f2d01298b0ce981c5d31521e19d3023bc84a43c33a606974c54888674c0d9c91081098a90147d3273a13152028fc64a74262a405578694e84c5480abb0529d098a90193d2203a1315202aba34874262a4055d4290e84c5480f1c81298a988901c3e3a531531120387874a62a6224078e4c58084c4480f8c81298a906901f1931602120d20371241a046612406e34834e8cc24809e70d29d198490198d20d3a330920339c34a746612404738694e8cc2480f1c91298a980901c7a3a53153012038f074a62a602407864c54834c0480bcda12906980901b9a42520d301202f3084a41a602406e61094834c0480f1c98b110980901e593161a1301203d32624342602406679094838c7480f0e98a90698e901a3d31622131d20273c44c34263a4069e4c58084c7480dcc90701098e901c1d31520d31d20387a62c44263a407174c58684c7480acf1130d098e901c7931602131d203b3241c04263a4066e8888084c7480bb881311098a8415763a5221315082ae874a44262a106dc8884084c5420db891081098a841772225021315083ea434a04262a106dc408ce84c5420b3a9939d098a8419773a23a1315082ee204c74262a1059d8c94e84c5420b9b1129d098a8417342253a1315082eac34a74262a105dc8094e84c5420db88101d098a8419753a03a1315082e6e44874262a105cd4890e84c5420baa8d21d098a841e36225315311083ce204a62a6221079c4c54084c4420bd9112810988841a753163a13110827e204c742622104dd4a90e84c44209ea8d21d0988841f5
  | 2 => 0x8a01248a288a0408a2283a96c8a0fc739188a2285a8888a17c351362d8a27315827a288a2283384c3612c349f01983c678a6638185409c6506e658c626a284c0208a0d68a0d017a08012281f8f88a22809a288902c53a288a06824a28139ea2514a5c9867d06270038469ca190ca5b80c330f20c9901102a1da0c58970862288a22869206420288a00e392288a080280c08a0367805674a288a228162284a2288a228601be4d228262282a9dc2f10262228660fa7ea288a0248a1fc8a03a8a2288a1e282a287e0c208a288a2208a22884a284b8862ba288a2286f0968a1844f2282c2282a2287188c8a2287414c8a19c401c48a2287c834599488a146168b270a288a15645a283d2282e0848092a2f9ba609c8411da8522848228628c8001de571101d07080140879b8242288a072151a68a0ac8a2288a2288a06a8a2288a2284f88a8a00817228580166a1aa57a283722823a288a228498e62d0607b2287a1ae4e204592288a2288a2288a2287f9068a048380460190e8a03e140826b2284c8ee37a283c1b27d8146c1768a11e4499a6890c8a1d6491d800968028da751e4888ec4293a5087a1b178510521f228870f68a2288a2105f8ba042280ba281287883a285481c3a2285517a8a18c6da287991c8995a5d1ee6d0e28a2288a228311a08a2288a01e292283fa168a228868308a0428a2286481a4522814014100010c0021450420000820141c20431010030823cd0412400071000022c00420c70430812280c004000004300004428a409c810c010
  | _ => 0
def u127K7 : Nat → Nat
  | 0 => 0x5b7e22119d3175f8878074c5d7d21e01d316df4888074c5d7e21d01d3175f4874074c5b7e22101d317d78684074c5b5e1a101d317de8084074c5e3e2213153139f8684c54c4e7d1a13153139f8084c54c4e7d0213153139f4c58674c4e7d31519d3139f4c58074c4c7d31601d3139f4c54074c4bbe22101d312f78684074c4d7f3a131520f5f0e84c5483e3d31531120fd78084c5483f5d02131520fd7ce84c5483f5c3a131520f874c54c4483f9e02131120ee78084c4483f9d02131120fa74c48c7483f5d31601d20fe74c4807483d8d20d21f30a7b808487cc2ded02121f30b73483407cc29ee22101f30b7b488407cc29ce1a101f30a73468807482d8d20e21d18b9f8884c54c0e7d2213153039e8084c54c0efa021311303974c54834c0e9d31120d302f7ce84834c0dde3a120d302f70e84834c0ddc3a120d302770e84834c0e7d31621d303af4c48874c0c7d31621d3039f4c54874c0f9d20d21d302f78684874c0bfa02121d303974c58674c0edd31219d303774878674c0bdd22219d302778888674c0ddd22219d302774888674c0f3d221315203de4084c5480d7f3a13152035f8e84c5480d7d3a13152035f0e84c5480e3d315311203ee8084c4480f1d31520d203e78c8483480f9a02120d203e3483cc2480bad223309202fa408cc2480bed3a33092027b4e8cc2480e79315301203ae4c44c0480f9920d301203ee8884c0480fda1a1301203674838c7480e7d31531d203e74834c7480bbe22131d202f78684c7480bfa02131d2031f4c54c7480d9d20d31d2036f8884c7480dde1a131d202778684c7480dfa02131d203e3483447480f76221315083dd4884c5420f71021315083ddce84c5420f763a1315083dd4e84c5420f743a13150839d4c54c4420ff1021311082fdce84c4420bf63a1311082fd0e84c4420f5531520d083e54c4483420fd632120d083f4808483420fd63a120d083f50e8483420fc520f309082f9488cc2420be1023309082f94e8cc2420be63a12090839c4c54c0420ef1311301083f44834c0420ff2221301082fc8884c0420ff1221301083f48684c0420f71315201083ec4c4480420f9120d201083f8cc2480420bf2321201083fc4c8480420bf1321201083f8448480420fd520e31d083bc4c08c7420ff120231d082fd4888c7420e7531531d083bd4c44c7420fd520d31d083fc4804c7420bf622131d083f58684c7420bd61a131d083fc8084c7420bf202131d083dd4c5887420fe730a21d083fc4c0887420fb120221d0837d4c7887420bf532221d082f9448887420f7531521d083ed4c4487420fe730921d083fc4c0487420df631d21d0837d4c7487420bf632121d082fd4c8487420f762a121d082dd8a8487420fe512121d082f9448487420fc520d11d083f8480447420fe521d11d082f9888447420
  | 1 => 0x2c9785409a98a2bc5e28578435a824aa720c06408a80a0c95c16228bd78bc5e12978bc5e2f11abc371e978bc59af178bc3faf178475e1816cbc35a489ebc329f48cbc41911785d2d2f178bc5e2f10ebc5e238c65020af046342caf178805e27d787e3e07824b90d98578bc51884ea332d9cd78b1558740cbc0827538bc47a5c0a5c5e0d574bc0e1b070bc002f108765e2f0d427089dcd0bc1da59780e5e2b178bc5e2f0f09a5e101780d2f934024e442f034bc5baf178905e2f0debc5e229782007af178a51caf178225e16018bc161e578265e224bc8554af10cbb522f02e67038f03eb45e2f15a985e1ed22bc2109016370192054294994978bc298fd78315e008daaf38af0503d4f2f04a705e2f0c80a1828178aa510e902bc5e2f1182b2baf07c6625af1786945af128bc5e2f178bc2615978bc042f178bc4caf092bc5e2f178bc5e0b578625e2f1782e5e2f178bc4daf178bc5e2e160bc4aaf14ebc5e2f02abc410d978bc5e1d17810362501408011409200000006101070151d02215010b92260000410001029b7e1a221d316df4688874c5b7d02221d317cf8884874c5b7e1a121d316df4684874c5f760a121d316dd8284874c5b7e02121d316df4888674c
  | _ => 0
def u127K8 : Nat → Nat
  | 0 => 0x1ba0170b9c88819507a0a09da0a09d09849b2091828b0da0a09f1a858c0a99071c208020839320a0968ea0942094869a160c93a09795a0a08a06181f810911209e030502009092920d0f8f0e081e9018a08419a070066008aa4394a21800d2009df8874c5efa43a62f7e19d317be8ce98bdf8074c5efa03a62e7d315313ff0ce9897f8674c4ffa33a625fd19d313ff00e9897f8074c4ffa03a625fe21d30fae98b107df4c5483f7a62241dfe31d20ef688e907d74c5483f3a62241fde31d20fe688e907f7807483f9c41e617cd20f30af690f9857b467cc2bda03e615ee19d20af700e905f3483462bdc43a3167d3153037e988981f74834c0ffc43a605fe21d303fe90e981f78674c0bbc33a6077d315203de988901e7483480fde612407f9301202ff18e901ff4c7480bfa63a407ed11d202f688e901f3483440eea62a107f5311083ea906841f9cc2420fca412107f1301083f8900841fd8c7420fea63a107f621d083fa90e841f9447420
  | _ => 0
def u127K9 : Nat → Nat
  | 0 => 0xcd6b5a7435ac48d4d6b5ad591ad695ad6b40d6b5ad105a4cdf4c5ff4c4ff4c3f7883ff483f7483fbcc2fb482fb462ff4c0ff480fb440fd420
  | _ => 0
def u127K10 : Nat → Nat
  | 0 => 0x227f
  | _ => 0
def u127N : Nat → Nat
  | 4 => 9
  | 5 => 123
  | 6 => 276
  | 7 => 188
  | 8 => 65
  | 9 => 13
  | 10 => 1
  | _ => 0
def u127R : Nat → Nat → Nat
  | 4, i => packedAt u127K4 (i * 85) 85
  | 5, i => packedAt u127K5 (i * 72) 72
  | 6, i => packedAt u127K6 (i * 59) 59
  | 7, i => packedAt u127K7 (i * 46) 46
  | 8, i => packedAt u127K8 (i * 33) 33
  | 9, i => packedAt u127K9 (i * 20) 20
  | 10, i => packedAt u127K10 (i * 7) 7
  | _, _ => 0
def u127I : Nat → Nat → Nat
  | 4, h => packedAt u127K4 (774 + ((h / 3 + packedAt u127K4 (765 + (h % 3) * 3) 3) % 19) * 5) 5
  | 5, h => packedAt u127K5 (9061 + ((h / 41 + packedAt u127K5 (8856 + (h % 41) * 5) 5) % 210) * 8) 8
  | 6, h => packedAt u127K6 (16836 + ((h / 92 + packedAt u127K6 (16284 + (h % 92) * 6) 6) % 404) * 10) 10
  | 7, h => packedAt u127K7 (8896 + ((h / 62 + packedAt u127K7 (8648 + (h % 62) * 4) 4) % 322) * 9) 9
  | 8, h => packedAt u127K8 (2250 + ((h / 21 + packedAt u127K8 (2145 + (h % 21) * 5) 5) % 83) * 8) 8
  | 9, h => packedAt u127K9 (268 + ((h / 4 + packedAt u127K9 (260 + (h % 4) * 2) 2) % 37) * 5) 5
  | 10, h => packedAt u127K10 (8 + ((h / 1 + packedAt u127K10 (7 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u127Pos : Nat → Bits
  | 0 => 0x821c004703e4707fff01002930026732673ff
  | 1 => 0x303e001b9fc1b9f8060020531c00db9cdb9ccc
  | 2 => 0x3fc00c03e0003e007804ca63e0cce3e0e3e0f0
  | 3 => 0xc000301c0001c0007ff70c7c00f0fc00fc00ff
  | 4 => 0x3fe00001ffff80080f8000ff0000ffff00
  | 6 => 0x3ffffffe0000000ff00000ffffff000000
  | 7 => 0xffffc00000000000000fffffff000000000000
  | _ => 0
def u127Neg : Nat → Bits
  | 0 => 0x1862c000b0460b098a30000291000231023155
  | 1 => 0x78ae4009b1c29b389e50005314004a944a94cc
  | 2 => 0x3be4bcbff28dff537e244a63a0cce3e0e3e0f0
  | 3 => 0xe0083d5f4511f4a475c50c7400f0fc00fc00aa
  | 4 => 0x81001460000164c620800e8000550000b54a00
  | 6 => 0x6112b964e380000410ff00000aab54a000000
  | 7 => 0x411020008200000000ab1084a000000000000
  | _ => 0
def u127Slices : List (Sig × Nat) := [(0x3333333333333333333333333333333333333333333333333333333333333333,9),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,9),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,9),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8),(0x5555555555555555555555555555555555555555555555555555555555555555,8),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,8),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,8),(0x00000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7),(0x0505050505050505050505050505050505050505050505050505050505050505,7),(0x00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f,7),(0x0303030303030303030303030303030303030303030303030303030303030303,7),(0x0055005500550055005500550055005500550055005500550055005500550055,7),(0x00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f,6),(0x0000000000000000555555555555555500000000000000005555555555555555,6),(0x0000000000000000333333333333333300000000000000003333333333333333,6),(0x000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff,6),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,6),(0x0000333300003333000033330000333300003333000033330000333300003333,6),(0x0f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00,6),(0x3030303030303030303030303030303030303030303030303030303030303030,6),(0x00f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,6),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000,6),(0x0000000000000000000000000000000033333333333333333333333333333333,5),(0x0000555500005555000055550000555500005555000055550000555500005555,5),(0x1111111111111111111111111111111111111111111111111111111111111111,5),(0x0000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,5),(0x5500550055005500550055005500550055005500550055005500550055005500,5),(0x5050505050505050505050505050505050505050505050505050505050505050,5),(0x00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00,5),(0x000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff,5),(0x0000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff,5),(0x0000000000000000000000000000000055555555555555555555555555555555,4)]
def u127Atlas : Atlas := ⟨10, rawDecor 223 u127Pos u127Neg, u127T, u127Slices, [], u127N, u127R, u127I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_4_0 : Interval u127Atlas 4 0 9 := block_range (n := 9) (by decide +kernel)
theorem all_u127_4 : Interval u127Atlas 4 0 9 := blk_u127_4_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_5_0 : Interval u127Atlas 5 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_5_32 : Interval u127Atlas 5 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_5_64 : Interval u127Atlas 5 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_5_96 : Interval u127Atlas 5 96 27 := block_range (n := 27) (by decide +kernel)
theorem all_u127_5 : Interval u127Atlas 5 0 123 := (concat (concat blk_u127_5_0 blk_u127_5_32) (concat blk_u127_5_64 blk_u127_5_96))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_0 : Interval u127Atlas 6 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_32 : Interval u127Atlas 6 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_64 : Interval u127Atlas 6 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_96 : Interval u127Atlas 6 96 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_128 : Interval u127Atlas 6 128 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_160 : Interval u127Atlas 6 160 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_192 : Interval u127Atlas 6 192 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_224 : Interval u127Atlas 6 224 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_6_256 : Interval u127Atlas 6 256 20 := block_range (n := 20) (by decide +kernel)
theorem all_u127_6 : Interval u127Atlas 6 0 276 := (concat (concat (concat blk_u127_6_0 blk_u127_6_32) (concat blk_u127_6_64 blk_u127_6_96)) (concat (concat blk_u127_6_128 blk_u127_6_160) (concat blk_u127_6_192 (concat blk_u127_6_224 blk_u127_6_256))))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_7_0 : Interval u127Atlas 7 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_7_32 : Interval u127Atlas 7 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_7_64 : Interval u127Atlas 7 64 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_7_96 : Interval u127Atlas 7 96 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_7_128 : Interval u127Atlas 7 128 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_7_160 : Interval u127Atlas 7 160 28 := block_range (n := 28) (by decide +kernel)
theorem all_u127_7 : Interval u127Atlas 7 0 188 := (concat (concat blk_u127_7_0 (concat blk_u127_7_32 blk_u127_7_64)) (concat blk_u127_7_96 (concat blk_u127_7_128 blk_u127_7_160)))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_8_0 : Interval u127Atlas 8 0 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_8_32 : Interval u127Atlas 8 32 32 := block_range (n := 32) (by decide +kernel)
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_8_64 : Interval u127Atlas 8 64 1 := block_range (n := 1) (by decide +kernel)
theorem all_u127_8 : Interval u127Atlas 8 0 65 := (concat blk_u127_8_0 (concat blk_u127_8_32 blk_u127_8_64))
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_9_0 : Interval u127Atlas 9 0 13 := block_range (n := 13) (by decide +kernel)
theorem all_u127_9 : Interval u127Atlas 9 0 13 := blk_u127_9_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u127_10_0 : Interval u127Atlas 10 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u127_10 : Interval u127Atlas 10 0 1 := blk_u127_10_0
theorem cert_u127 : Complete u127Atlas := by
  intro k hk i hi
  change k ≤ 10 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u127_4 i (by omega) hi
  · exact all_u127_5 i (by omega) hi
  · exact all_u127_6 i (by omega) hi
  · exact all_u127_7 i (by omega) hi
  · exact all_u127_8 i (by omega) hi
  · exact all_u127_9 i (by omega) hi
  · exact all_u127_10 i (by omega) hi
theorem b_u127 : Lower true (vars 223) u127T 11 := by
  have ready : Ready u127Atlas (asRow u127Pos) (asRow u127Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u127Atlas, u127Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u106
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u112
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u108
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u107
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u105
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u109
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u110
    · exact slice_correct (ms := fixRows 128 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u92
    · exact slice_correct (ms := fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u63
    · exact slice_correct (ms := fixRows 68 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u83
    · exact slice_correct (ms := fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u65
    · exact slice_correct (ms := fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u67
    · exact slice_correct (ms := fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u76
    · exact slice_correct (ms := fixRows 65 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u80
    · exact slice_correct (ms := fixRows 66 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u81
    · exact slice_correct (ms := fixRows 72 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u84
    · exact slice_correct (ms := fixRows 80 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u85
    · exact slice_correct (ms := fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u74
    · exact slice_correct (ms := fixRows 4 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u70
    · exact slice_correct (ms := fixRows 2 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u64
    · exact slice_correct (ms := fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u71
    · exact slice_correct (ms := fixRows 0 12) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u69
    · exact slice_correct (ms := fixRows 134 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u91
    · exact slice_correct (ms := fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u73
    · exact slice_correct (ms := fixRows 3 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u61
    · exact slice_correct (ms := fixRows 16 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u75
    · exact slice_correct (ms := fixRows 5 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u66
    · exact slice_correct (ms := fixRows 9 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u62
    · exact slice_correct (ms := fixRows 132 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u94
    · exact slice_correct (ms := fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u77
    · exact slice_correct (ms := fixRows 140 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u95
    · exact slice_correct (ms := fixRows 141 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u90
  exact frozen ready cert_u127 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,128,132),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem b_u128 : Lower true (vars 191) u128T 10 := by
  have h := lift_ok (u := true) (ms := fixRows 32 0) (raw := vars 191) (T := u128T) (xs := [(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) b_u112
  have hc : (([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  rwa [hc] at h
def u129K9 : Nat → Nat
  | 0 => 0x287f
  | _ => 0
def u129N : Nat → Nat
  | 9 => 1
  | _ => 0
def u129R : Nat → Nat → Nat
  | 9, i => packedAt u129K9 (i * 7) 7
  | _, _ => 0
def u129I : Nat → Nat → Nat
  | 9, h => packedAt u129K9 (8 + ((h / 1 + packedAt u129K9 (7 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u129Pos : Nat → Bits
  | 0 => 0xf1024083c6381ffff000026731106932673ff
  | 1 => 0xf020d80fc39cfe00c00000db9c229b1cdb9ccc
  | 2 => 0xcf1ff0001f000f0024cce3e0cce3e0e3e0f0
  | 3 => 0xfe00003e0000fffb8f0fc00f0fc00fc00ff
  | 4 => 0xf0000003fffff000c0ff0000ff0000ffff00
  | 5 => 0xfffffffc00000000ff000000ffffff000000
  | 6 => 0xff0000000000000000ffffffff000000000000
  | _ => 0
def u129Neg : Nat → Bits
  | 0 => 0x13000c184c0582314300000231000291023155
  | 1 => 0x71015c29c48d8e13c500004a94008b144a94cc
  | 2 => 0xa64b5e7889bf946fc224cce3e044a3a0e3e0f0
  | 3 => 0x48fff08313fa288ebcb8f0fc00f0fc00fc00aa
  | 4 => 0xf6a144237271c408c0550000ff0000b54a00
  | 5 => 0xb4a1863240410010c9000000bb544a000000
  | 6 => 0x8c080200000000082036aab54a000000000000
  | _ => 0
def u129Slices : List (Sig × Nat) := [(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,8),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,8),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,8),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8),(0x3333333333333333333333333333333333333333333333333333333333333333,8),(0x000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f,7),(0x5500550055005500550055005500550055005500550055005500550055005500,7)]
def u129Atlas : Atlas := ⟨9, rawDecor 127 u129Pos u129Neg, u129T, u129Slices, [swapRows 80,swapRows 65,swapRows 50], u129N, u129R, u129I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u129_9_0 : Interval u129Atlas 9 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u129_9 : Interval u129Atlas 9 0 1 := blk_u129_9_0
theorem cert_u129 : Complete u129Atlas := by
  intro k hk i hi
  change k ≤ 9 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u129_9 i (by omega) hi
theorem b_u129 : Lower true (vars 127) u129T 10 := by
  have ready : Ready u129Atlas (asRow u129Pos) (asRow u129Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u129Atlas, u129Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u118
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u117
    · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u116
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u115
    · exact slice_correct (ms := fixRows 0 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u114
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u113
    · exact slice_correct (ms := fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u93
    · exact slice_correct (ms := fixRows 1 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u87
  exact frozen ready cert_u129 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def u130K9 : Nat → Nat
  | 0 => 0x8a27ba34c742627674e64e4483
  | _ => 0
def u130K10 : Nat → Nat
  | 0 => 0xa5006409ca95190a113bfe22139bff4884e6dfd399393bf4e64c4bfe3a1313ff4e84c4bfd3a1313f74e6483f9d39120ff78c8483
  | _ => 0
def u130K11 : Nat → Nat
  | 0 => 0x1011110d110904ffa737fd393fe989f7483
  | _ => 0
def u130K12 : Nat → Nat
  | 0 => 0x50ff
  | _ => 0
def u130N : Nat → Nat
  | 9 => 2
  | 10 => 10
  | 11 => 4
  | 12 => 1
  | _ => 0
def u130R : Nat → Nat → Nat
  | 9, i => packedAt u130K9 (i * 47) 47
  | 10, i => packedAt u130K10 (i * 34) 34
  | 11, i => packedAt u130K11 (i * 21) 21
  | 12, i => packedAt u130K12 (i * 8) 8
  | _, _ => 0
def u130I : Nat → Nat → Nat
  | 9, h => packedAt u130K9 (95 + ((h / 1 + packedAt u130K9 (94 + (h % 1) * 1) 1) % 4) * 3) 3
  | 10, h => packedAt u130K10 (346 + ((h / 3 + packedAt u130K10 (340 + (h % 3) * 2) 2) % 14) * 5) 5
  | 11, h => packedAt u130K11 (85 + ((h / 1 + packedAt u130K11 (84 + (h % 1) * 1) 1) % 13) * 4) 4
  | 12, h => packedAt u130K12 (9 + ((h / 1 + packedAt u130K12 (8 + (h % 1) * 1) 1) % 3) * 2) 2
  | _, _ => 0
def u130Pos : Nat → Bits
  | 0 => 0x18e07fffc010100293000026731106932673ff
  | 1 => 0xe73f8030002020531c0000db9c229b1cdb9ccc
  | 2 => 0x7c003c004c04a63e024cce3e0cce3e0e3e0f0
  | 3 => 0xf80003ffc7098c7c00b8f0fc00f0fc00fc00ff
  | 4 => 0xfffffc00080e0f8000c0ff0000ff0000ffff00
  | 5 => 0x300ff00000ff000000ffffff000000
  | 6 => 0x3ff0000000ffffffff000000000000
  | 7 => 0x3fffffffff00000000000000000000
  | _ => 0
def u130Neg : Nat → Bits
  | 0 => 0x1608c50c00000029100000231000291023155
  | 1 => 0x236384f1400000531400004a94008b144a94cc
  | 2 => 0x6fe51bf084400a63a024cce3e044a3a0e3e0f0
  | 3 => 0xfe8a23af05088c7400b8f0fc00f0fc00fc00aa
  | 4 => 0xdc9c7102000a0e8000c0550000ff0000b54a00
  | 5 => 0x90104004100ff00000c9000000bb544a000000
  | 6 => 0x2082ff000000036aab54a000000000000
  | 7 => 0x3ab571084a00000000000000000000
  | _ => 0
def u130Slices : List (Sig × Nat) := [(0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,11),(0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,11),(0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,11),(0x3333333333333333333333333333333333333333333333333333333333333333,11),(0x5555555555555555555555555555555555555555555555555555555555555555,11),(0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff,10),(0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,10),(0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,10),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,9),(0x00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00,8),(0x000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff,8),(0x00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff,7),(0x000000000000000000000000000000000000000000000000ffffffffffffffff,7)]
def u130Atlas : Atlas := ⟨12, rawDecor 255 u130Pos u130Neg, u130T, u130Slices, [], u130N, u130R, u130I⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_9_0 : Interval u130Atlas 9 0 2 := block_range (n := 2) (by decide +kernel)
theorem all_u130_9 : Interval u130Atlas 9 0 2 := blk_u130_9_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_10_0 : Interval u130Atlas 10 0 10 := block_range (n := 10) (by decide +kernel)
theorem all_u130_10 : Interval u130Atlas 10 0 10 := blk_u130_10_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_11_0 : Interval u130Atlas 11 0 4 := block_range (n := 4) (by decide +kernel)
theorem all_u130_11 : Interval u130Atlas 11 0 4 := blk_u130_11_0
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem blk_u130_12_0 : Interval u130Atlas 12 0 1 := block_range (n := 1) (by decide +kernel)
theorem all_u130_12 : Interval u130Atlas 12 0 1 := blk_u130_12_0
theorem cert_u130 : Complete u130Atlas := by
  intro k hk i hi
  change k ≤ 12 at hk
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all_u130_9 i (by omega) hi
  · exact all_u130_10 i (by omega) hi
  · exact all_u130_11 i (by omega) hi
  · exact all_u130_12 i (by omega) hi
theorem b_u130 : Lower true (vars 255) u130T 13 := by
  have ready : Ready u130Atlas (asRow u130Pos) (asRow u130Neg) := by
    refine ⟨by unfold properPairs; decide +kernel, raw_faithful _ _ _, ?_⟩
    intro sp hsp
    simp only [slices, u130Atlas, u130Slices, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact slice_correct (ms := fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u127
    · exact slice_correct (ms := fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u125
    · exact slice_correct (ms := fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u123
    · exact slice_correct (ms := fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u121
    · exact slice_correct (ms := fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u120
    · exact slice_correct (ms := fixRows 128 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u129
    · exact slice_correct (ms := fixRows 64 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u128
    · exact slice_correct (ms := fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u126
    · exact slice_correct (ms := fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u124
    · exact slice_correct (ms := fixRows 128 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u116
    · exact slice_correct (ms := fixRows 144 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u118
    · exact slice_correct (ms := fixRows 80 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u111
    · exact slice_correct (ms := fixRows 192 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) b_u119
  exact frozen ready cert_u130 (by decide +kernel) (by decide) [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,16,18),(inputs.getD 2 zero,32,36),(inputs.getD 3 zero,1,9),(inputs.getD 4 zero,1,17),(inputs.getD 5 zero,1,33),(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

def fullRoots : List Sig := vars 255
def fullWord : Sig := u130T
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample8 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table8 : ∀ r, posted (sample8 r) = bit r fullWord := by decide +kernel
theorem raw8 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval8 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero = fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample8 r) = fullRoots.map (bit r) := by rw [←raw8, List.map_ofFn]; rfl
  rw [←bRead, exeBits gs r fullRoots (fun g hg => (legal g hg).1), ←e]
  exact (h (sample8 r)).trans (table8 r)
theorem binaryLower (low : Lower true fullRoots fullWord 13)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : 13 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u := true) (execute gs fullRoots) o
  rw [eval8 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_31197.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord = false)] at out
  obtain ⟨k, S, hk, run, sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord = true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, B, hr, hit, hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega
def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[0,4]⟩,⟨.or,[3,4]⟩,⟨.or,[5,9]⟩,⟨.and,[8,11]⟩,⟨.or,[2,8]⟩,⟨.or,[5,7]⟩,⟨.and,[13,14]⟩,⟨.or,[7,12]⟩,⟨.and,[10,16]⟩,⟨.or,[8,11]⟩,⟨.and,[6,18]⟩,⟨.or,[15,19]⟩,⟨.or,[17,20]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono, 21⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 13) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs, o, ?_, Nat.le_refl _, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))), len⟩
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    exact ⟨mono, 21, monoShape, by change 14 ≤ gs.length; omega, monoEval⟩
end PEqualNP.Outside.L_meta_31197

open PEqualNP.Outside.L_meta_31197 in
theorem PEqualNP.Outside.L_meta_31197 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  solve b_u130
