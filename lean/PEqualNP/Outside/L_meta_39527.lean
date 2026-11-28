import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_39527.Model
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def eqF (a b : Sig) : Bool := Nat.beq a.toNat b.toNat
theorem eqF_eq (a b : Sig) : eqF a b = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp [eqF,BitVec.toNat_inj]
noncomputable def anyEq (m d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || ih) l
theorem anyEq_eq (m d : Sig) (l : List Sig) :
    anyEq m d l = (l.map (masked d)).any (fun v => v==m) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || anyEq m d vs) = _
    rw [ih,eqF_eq,List.map_cons,List.any_cons]
noncomputable def anyEq2 (m c d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || (eqF (masked d v) c || ih)) l
theorem anyEq2_eq (m c d : Sig) (l : List Sig) : anyEq2 m c d l = (anyEq m d l || anyEq c d l) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || (eqF (masked d v) c || anyEq2 m c d vs)) =
      ((eqF (masked d v) m || anyEq m d vs) || (eqF (masked d v) c || anyEq c d vs))
    rw [ih]
    cases eqF (masked d v) m <;> cases eqF (masked d v) c <;> cases anyEq m d vs <;> cases anyEq c d vs <;> rfl
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d ||
    cond u (anyEq2 (masked d a) (masked d (neg a)) d pool) (anyEq (masked d a) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  cases u
  · simp only [availF,cond_false,availableB,eqF_eq,anyEq_eq,Bool.false_and,Bool.or_false]
  · simp only [availF,cond_true,anyEq2_eq,availableB,eqF_eq,anyEq_eq,Bool.true_and,Bool.or_assoc]
noncomputable def memF (x : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF x v || ih) l
theorem memF_eq (x : Sig) (l : List Sig) : memF x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF x v || memF x vs) = _
    rw [ih,eqF_eq,List.contains_cons]
noncomputable def subF (a b : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => memF v b && ih) a
theorem subF_eq (a b : List Sig) : subF a b = a.all (fun x => b.contains x) := by
  induction a with
  | nil => rfl
  | cons v vs ih =>
    change (memF v b && subF vs b) = _
    rw [ih,memF_eq,List.all_cons]
noncomputable def sameWordsF (a b : List Sig) : Bool := subF a b && subF b a
theorem sameWordsF_eq (a b : List Sig) : sameWordsF a b = sameWords a b := by
  simp only [sameWordsF,sameWords,subF_eq]
noncomputable def allF (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => availF u d pool v && ih) l
theorem allF_eq (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) :
    allF u d pool l = l.all (availableB u d pool) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (availF u d pool v && allF u d pool vs) = _
    rw [ih,availF_eq,List.all_cons]
noncomputable def countF (d : Sig) (l : List Sig) : Nat :=
  @List.rec Sig (fun _ => Nat) 0
    (fun v _ ih => cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ ih) ih) l
theorem countF_eq (d : Sig) (l : List Sig) : countF d l = l.countP (isMaskedConstant d) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ (countF d vs)) (countF d vs) = _
    rw [ih,eqF_eq,eqF_eq,List.countP_cons]
    change _ = _ + if (masked d v == zero || masked d v == d) = true then 1 else 0
    cases (masked d v == zero || masked d v == d) <;> rfl
noncomputable def scalarPoolCutF (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  allF u c.domain c.wires rest &&
    cond (availF u c.domain c.wires (choiceVal op))
      (Nat.blt (k+c.paid) (c.bound+countF c.domain (choiceVal op::rest)))
      (Nat.blt (k+c.paid+1) (c.bound+countF c.domain (choiceVal op::rest)) &&
        (allowedB u op.1 && (availF u c.domain c.wires op.2.1 && availF u c.domain c.wires op.2.2)))
theorem scalarPoolCutF_ok {u : Bool} {c : BoundPool} {k : Nat} {rest : List Sig} {op : Choice}
    (h : scalarPoolCutF u c k rest op = true) : scalarPoolCut u c k rest op = true := by
  simp only [scalarPoolCutF,allF_eq,availF_eq,countF_eq,Bool.and_eq_true] at h
  obtain ⟨hall,hc⟩ := h
  simp only [scalarPoolCut,choiceOK,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  cases hz : availableB u c.domain c.wires (choiceVal op)
  · rw [hz] at hc
    simp only [cond_false,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inr hc.2⟩
    simpa using hc.1
  · rw [hz] at hc
    simp only [cond_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inl (by simp)⟩
    simpa using hc
noncomputable def anyP (f : BoundPool → Bool) (l : List BoundPool) : Bool :=
  @List.rec BoundPool (fun _ => Bool) false (fun p _ ih => f p || ih) l
theorem anyP_eq (f : BoundPool → Bool) (l : List BoundPool) : anyP f l = l.any f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v || anyP f vs) = _
    rw [ih,List.any_cons]
noncomputable def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  anyP (fun p => scalarPoolCutF u p k rest op) pools ||
    (links (keySet (choiceVal op::rest))).any (sameWordsF (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,sameWordsF_eq,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd (scalarPoolCutF_ok ok)
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
noncomputable def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

noncomputable def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def M152 : Nat := 2^152-1
theorem not152 (x : Bits) : (~~~x).toNat = x.toNat ^^^ M152 := by
  rw [BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,Nat.xor_comm]
  rfl
def natBv (d x y : Nat) : Nat :=
  cond (Nat.beq d 0) (x &&& y) (cond (Nat.beq d 1) (x ||| y)
    (cond (Nat.beq d 2) (x &&& (y ^^^ M152)) ((x ^^^ M152) &&& y)))
theorem natBv_eq (d : Nat) (a b : Bits) : (bv d a b).toNat = natBv d a.toNat b.toNat := by
  match d with
  | 0 => simp [bv,natBv]
  | 1 => simp [bv,natBv]
  | 2 =>
    rw [show bv 2 a b = a &&& ~~~b from rfl,BitVec.toNat_and,not152]
    rfl
  | n+3 =>
    have e : bv (n+3) a b = ~~~a &&& b := by
      unfold bv
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [e,BitVec.toNat_and,not152]
    rfl
def natCol (d : Bool) (x y : Nat) : Nat := cond d (x &&& (y ^^^ M152)) (x ^^^ y)
theorem natCol_eq (d : Bool) (s : Bits × Bits) : (column d s).toNat = natCol d s.1.toNat s.2.toNat := by
  cases d
  · rw [show column false s = s.1 ^^^ s.2 from rfl,BitVec.toNat_xor]
    rfl
  · rw [show column true s = s.1 &&& ~~~s.2 from rfl,BitVec.toNat_and,not152]
    rfl
def covFail (d : Bool) (t : Bits) (op : Nat) (a b : Decor) : Bool :=
  !(Nat.beq (t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat)) M152)
theorem covFail_eq (d : Bool) (t : Bits) (op : Nat) (a b : Decor) :
    covFail d t op a b = ((t ||| column d (dbin op a b).2) != BitVec.allOnes 152) := by
  have e : (t ||| column d (dbin op a b).2).toNat =
      t.toNat ||| natCol d (natBv op a.2.1.toNat b.2.1.toNat) (natBv op a.2.2.toNat b.2.2.toNat) := by
    rw [BitVec.toNat_or,natCol_eq]
    simp only [dbin,natBv_eq]
  unfold covFail
  rw [←e]
  generalize (t ||| column d (dbin op a b).2) = X
  by_cases h : X = BitVec.allOnes 152
  · subst h
    decide
  · have h3 : X.toNat ≠ M152 := fun q => h (BitVec.eq_of_toNat_eq (by rw [q,BitVec.toNat_allOnes]; rfl))
    have h4 : Nat.beq X.toNat M152 = false := by
      cases hb : Nat.beq X.toNat M152
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h3
    rw [bne_iff_ne.mpr h,h4]
    rfl
noncomputable def allD (f : Decor → Bool) (l : List Decor) : Bool :=
  @List.rec Decor (fun _ => Bool) true (fun v _ ih => f v && ih) l
theorem allD_eq (f : Decor → Bool) (l : List Decor) : allD f l = l.all f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v && allD f vs) = _
    rw [ih,List.all_cons]
def opsAll (u : Bool) (f : Nat → Bool) : Bool := f 0 && (f 1 && cond u (f 2 && f 3) true)
theorem opsAll_eq (u : Bool) (f : Nat → Bool) : opsAll u f = (opsOf u).all f := by
  cases u <;> simp [opsAll,opsOf]
theorem or_ones_and {n : Nat} (x y z : BitVec n) (h : (x &&& y) ||| z = BitVec.allOnes n) :
    x ||| z = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun w => w.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hi, decide_true] at hb ⊢
  cases hx : x.getLsbD i <;> simp_all
theorem takeTwo_right (c : Cov) (a b : Bits) :
    takeTwo c a b = takeOne c b &&& ~~~((c.2.1 &&& a) ||| (c.2.2 &&& (a &&& b))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo, takeOne, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
def quickPair (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152
  else Nat.blt c.1 (c.2.1+1) &&
    (((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152) &&
     ((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152))
theorem evalMove_cov {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) ≠ BitVec.allOnes 152) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else if (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) != BitVec.allOnes 152 then true else _) = true
  by_cases hlen : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap
  · rw [if_pos hlen]
  · rw [if_neg hlen,if_pos (bne_iff_ne.mpr h)]
theorem evalMove_long {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else _) = true
  rw [if_pos h]
theorem quickPair_ok {c : NodeContext} {a b : Decor} {op : Nat} (h : quickPair c a b op = true) :
    testPair c a b op = true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  unfold quickPair at h
  simp only [testPair,Bool.and_eq_true]
  split at h
  next hlt =>
    have hl : cap < n := by simpa using hlt
    have hf := bne_iff_ne.mp h
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_long (ka:=true) (kb:=false) (by simp <;> omega)⟩,
      evalMove_long (ka:=false) (kb:=true) (by simp <;> omega)⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
  next =>
    simp only [Bool.and_eq_true,Nat.blt_eq,bne_iff_ne,ne_eq] at h
    obtain ⟨hl,hb,ha⟩ := h
    have hf : (takeTwo cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ||| column (!cov.2) (dbin op a b).2) ≠ BitVec.allOnes 152 := by
      intro e
      rw [takeTwo_right] at e
      exact hb (or_ones_and _ _ _ e)
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_cov (ka:=true) (kb:=false) hb⟩,
      evalMove_cov (ka:=false) (kb:=true) ha⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
theorem pairQ {c : NodeContext} {a b : Decor} {op : Nat}
    (h : (quickPair c a b op || testPair c a b op) = true) : testPair c a b op = true := by
  rcases Bool.or_eq_true_iff.mp h with q | t
  · exact quickPair_ok q
  · exact t
def quickPairN (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    covFail (!c.2.2.2.1.2) (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2)) op a b
  else Nat.blt c.1 (c.2.1+1) &&
    (covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2)) op a b &&
     covFail (!c.2.2.2.1.2) (takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2)) op a b)
theorem quickPairN_eq (c : NodeContext) (a b : Decor) (op : Nat) :
    quickPairN c a b op = quickPair c a b op := by
  simp only [quickPairN,quickPair,covFail_eq]
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    allD (fun b => opsAll ctx.2.2.2.1.2 (fun op => quickPairN ctx a b op || testPair ctx a b op)) bs
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,allD_eq,opsAll_eq,quickPairN_eq,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => pairQ (h.1 b bm d (opsOf_mem hd))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => pairQ (h.1 a haTail d (opsOf_mem hd))
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


end PEqualNP.Outside.L_meta_39527.Model

namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
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

def SBf (j : Nat) : Nat := [8, 8, 6, 8, 8, 8].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

def mirrorSteps : List Move := []

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

noncomputable def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

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

noncomputable def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_39527

namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x30002430050000001470000030400060416001000004c0040104fe10fd40fe20fd10fd32fc40fc30fd43ff32ff41fe41fd42bf40fd20fc10fc20ff20ff42ff21fe42fd30ff43fe31fc32fc21fe40fd21fd41ff10fc42bd40ff30ff31fe30ff40fd31fe43fc41fe21fc43fe32be41bc41fc31
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa81be50906f8a8986f8c841bf2a6437e5410afaa4206f10410dfa0e81bd43906faa0195f94040baa88617d544c2fca7a0df94b43bf29887bd43d0bea6218dfd5032bea8e613c544c77ca998ef50d40dfa9c83bc410c37882905f54643bea8c817e5290efaa5885f54910f7a1285df308c37a83a0778c531fd08021dd300c27aa8087ec8220bfa8285bc21d03be6518dfd5221df21a876e5204378a898dfd4e20dfa92817e53c437883a05fd4c21dea98837d50c87dc64905f54831fb18e217c54c827ca990ef90410bf29c417f540c6fca810df14940dea00217e53486fea8996f10e419e28a81bd509077885a06f90520dfa9883df320cb7a80186f8ca41bf2a241be410c2fca610df94341ef298217c538877c8420ef50120df192817d5444278a9886f15310f790a41ee32c82fca790df54c10f629221be41d037e85a06fd4140bfaa0617e52903baa790df94e41de21a817d50887ba8621d714d10bf294217d54c877883905f15221af298417d52902faa8195fd4543bf2a421f7314c6faa7195f14143f721465bf515037883105f14930bea96617d54c83eca2186f90f40bf29681bd4350aeca210774c832f6a12657e51ccaf8a8886f10721bea80637d510827ca320df54a30bfa8283bc41cc2f8a2906f14b40de29883f531443dc40906f10710bfa9221f7218877c83905f94220df21281bd40882faa9107ec4210fb10e21be540837882205f94242bfa8265be41882f8a090df95010dea06417f54cc77ea5a05fd5230df20e43f610442faa510fed0140df21c85bf4290afea6105fd5310dea06617e53903788298efcc841df20e61be535037e8720df548109f28883bd52502fca420df54332ee98a617c54487f681206fd0d40df20e217c54cc7be86a1ef10610dfa1c87be54c86faa521df95331dea06217d510c2f8a6904f55240bf29863be411037a80205f55242dfa80837f53486fca4886fd0f42ef99261be511077e8220fd88421de996817d5348378a020fbc8220bfaa241ee32087da64196fd0d42aea9885be540437ca5a05f54630bea9c81ed5210ef8a4a0ef90531bf28c415e530437a8220fbc8720de28a81bd53d02faa3996f10540de98a81ef52442faa690df94843be2a6617e518c27aa990ef10a41bfaa261bc544cafaa8106f90610bf28663df300c37e64a06f10421be2a041bf40082fca218f750f32dea04217c524c6eca2185f54041de18e817d52cc6faa910efd0641deaa663bd21d03eaa2106f54e41bea9e417e53d0b7c8210f74ca31dfa0a816e52cc6fea2905f94640be2a461ed328867aa8195f95030fd200817e50107788420dfd4f21bea8087f940103daa4185f54343df2a4617e53442baa6105fd4d40bea9c215f534437aa990ef14241fb880217e528cafaa2215f54620f729061bd42d037c82a0df54610
  | 1 => 0xf52c43baa6087b48520bf28e817c540c6fca1087b54810df28a81bd42107dc84995f94241f6996417d53886fca1195f94c40bf28461be410837e80985f94231bea94417d5090afaa120ef90431df20a437f54082fca4196f50020fb18a213d548437a84a06f48540df2a441bd4210bda85195f95231bf290433d540c2fca010fe4c030bf29c87ee320cafea898fb48720bea94217e541037ea120df54c41dea8e817d53082fea690770c430be28a87bd4310e7ca91077d0e43fd882217c540cb7a8520ef50f40bfa8a817c548c7788318df94042bfa9a21fb308c2fca5985fd4d41ee29a217e52082fea090df94343bf28041ef20082fea990ef90631bf28c87df314c2fca6185f54d10df20e637e5110efaa5a1df95131be29e43dd53082faa6205f55120de20e637e51d0efca4215f15132be28a65de53c87dca421df95032deaa4216f52442f8a6a16f94041bf29c437e53842fca518df54f10beaa6657d518cb786420df95310dfa0021be51d037c62a06f8cb40bfaa661bc418c3788288778c130be29e21ef324cafca6906f14841bfaa421de43ccb7aa020dfd4530dfa0061bf40482f8a4a1df54743fba0a83f621442f8a898cf55331df98a815d530437ea6a05f54642af29e437e51042daa4085f94632de21e817c538827ca9185f942409f2a0417e52cc7ba65985f14e10beaa6617d53882faa8084fd5110be2a6657d528c6fca9195f15232de19483df328cbde65196f90510ef21a657f538877c83186f0c940dea0221bd52907da6410ef50c419f2a065bc418877a81187d504419eaa461be42907ee8320df14540df994837d538c7788620fecc130df29483be531077aa420df54021db288837f53c83bc62185f55232bea8e857d5210f7c85a05f14d21f7194437c54c42fca8995f94c32b7290877e518c6fca0085fd4931bea9681bf40c83eaa2185f94f209f28e817f53043d842105f94840df20c437f544877e81105f15010de2a2437e54107dca4086f55010fb208837f5250efaa720cf54241de20a617e5390b7c42a07b48421dfa1887bf401037e43a05f94432dfa1e81ee52cc77e81985f14542ee990637c53506faa818efd0310bf284877d548c6fea4084f95040bf288855d53c86f8a0a0cfd5121bfaa0216d52cc6fca310dfd5021baa88417c540c37aa8194fd5131fb90a437d54907be6218df54830bf28c83fb20483ba6218df94830bea9843f521086faa7a05f14c10e699065f521c42fca52177d4d10df20a61f510042f8a9085f54232df292817e51c82fea70877cc831de98e81bd540837e81086f50130bea9e83ee21882f8a4886fd5131dea96817e52c43da84217bc8621bea86833c544cb7e81205f55240be29a81bf32d0378a8885f94441beaa6217f5250778a3a05f15120ef98e617e500c77886216fd0c41df90
  | 2 => 0x1a010008e40000c010005e8100e802008000188c0a088000060103000004008002c814000340322c0000e049ce098040380c530001b8241280022002000080e000ba81a0580006802028000391201800000bc09a0208004000f80180400004020000014e008040100004004858000180400804030700303c0015c0480000806118a6b9050000000340a0984c0101e000000486a5ba20020040000e038000900000802c7006000548e8000600405002090220900a090040280202000010020b00c0280c0186001978098060000009000010000000a000080011000000000000004a2584000000008c20007e000000000a01006000160000e100c201808040060009e01002001d6080363b00a04868015d000b2a01064a88040a006750320102009000070020103a000b4028100080000815728093780c0203e0601a1f81000018050020880203000028760c0020b0b2000e03003207054008560080c0e0d8000340400000012000060001200800e7006005f94030de10a817c540867ca9085f94420bfa82877e529077a82a06fd5110bf28643f9200837e8520df55021deaa4417f548837883205fd4d429e2a2217e51102fca110df54a41bf286657f524c37884a07b88420deaa461be431077ca8185f94f40f710a43bf42106faa221df55121beaa421dd5310afaa8187bc8421bf2a261be415037e63a05fd4f10ef298857e54c827aa9105f94421bf290633e54043f440105f94032bea9e43bf4210b7c80a05f95110bf29683bb505037c63a05f95220be29a21bc529077c83207b086209faa265be548427ea9885f94c20f721085bd5350378a7a05f14c20f6a96637d51c82faa5a0dfd4a10b6a9087be4390678a890df95221be29021dc318c37ea9886fd4a41dfa1281be43502fea9994f95331b6a90617e51d0b7ea890df95043fb188637e5204378a6a06fd0230de19681bf40442fca9985f94a30ee98e617d5010afaa420f7ccb30bea9c85bc4390b7c84a15fd4542b7290615e5310b7c86216fd5132bfaa6417d51102faa2195f54e30f699241bc53906fea098df94c41deaa061ef4290a7aa8106f4c841fc880217c52843bca6105f95121b6292217d54cc77aa2a07d48510ee99261be53d03be6318efd4841bea86637e54ccaf8a0a15f14132bf2a461bf53d02f8a990df55132be29e417e54082fca3985f55243be296217e50d0beca2105fd5110df10e817e510c37ca720df54f42bfaa4637d508c778a4a06f95032dfa8e81de318c3bc8621fe8c030de208417c54882faa3a05f94642de99483de324cafea2995f94c42beaa461f531c43788290df14c21de992817f548cbba86995f94043beaa2637f52502fca818cf95030bea9885bc410c67aa020df94c10bea8487ed20083ee6318df54342df29083f710842f8a098df14530de18a817
  | 3 => 0x2a0781e0280a1a80c0917402914018000100e0185407000030162780a01000048000000000000010000c8760201e000000b0640001e0000010000000000082201002100000001201854000140e81a03800008000000c04984008180000000000008020500202172088bc038000a8200001000832000000080a
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x6310c23c6454b309758c54c823f6510620ab5884310a3d650cb408f99250cc65e6394a41cd945400c23f65487408f992544863f65500109798e544423d65d00208fd95315031c5350d408f994414863c64547209d984530423d64d4c10cdd91510c26e62951108fd91534863d6494d109bd95320ca3e650ca41cb948410c2ad6294e41c794f40082b96010620b358f210863d65904409b98a539066d6214d408f99252c429d63142418f592500823c654c841cb54a410423e64141318f59441082ad6210e41add85535026f6254d108f594329066e65149109d987540831d5314d40d5546310c23e6494221cb949429063d64d45209d587548ca6e6215032cd144215027465485109d987540c2cd62cc7309b596210823e6414121cb948410423e65cc740c7d4e539065d6394b10ad586321063d65104309798f540823e6495131a798c421063c61552308f592508cb2e52d0010ab588501063d6595032ae980315034d53508428fd954310e3c61550308f19532d029e6310b40d9546210823d6595020ab988435023e64d45308f99740442ba6014c41cb551320cb3554544308fd95401031c5490d32cd144414c2cc63509328f592500c23e6494f108f990540423e64d4c208f593538826e6214c20e34c8325031e5454f219798f540423e6414f209b997214831e5494c20cb95252cc66e62141318f594410432d52107318f596410c36552440108f592500c63d6414c21ae980521063d6494f10ab58b31d025d63d52218fd94410c2ae6214041d3549300c2796014c219bd95200826d62d53319798c525023d6414a108f986540ca3d60d51328f994325023f6510420ec501100423e64942318fd9152442756114e20cb588544ca7b6544010c794c410823c64544329d984520425f654c030c7d4c414425d63d4810c754d4210a3e64148108f596540c23f6454d10d9547200825f6550c4397d8d524423e65151109dd95100431f53d0110cd946419034d544c832cd545400831e5494c108fd9151c823d60953219b19532482ac6254d40aed81525033651500208f996414423d64149308f59053c823f65906308f195325032d548c8328f994544ca5d63949108f580544872d52104108f997215036552c4010d9584524423e61151109798f54c863f6548540ab58843106b960949408fd8154cc6756114c209d987548ca3c64549109b988540432d52d00109dd85544825f654c8328f9925388755510c4309b18954443655108420cbd49404423d64148108f99254442746154d20cd94441d02e5618c8218f59250cca5c6355110ad987321072d4354843cb549400c2b960d4740cd546410c23e6495132c7551530431e53904108fd96410423e6494032ab58843d034d53480209b98b540434f654c8328f597400c29c6354540cb949400c23f6510630
  | 1 => 0xc29e6314241ae98021502766114e20ad587321074c524c930c754c410438e4390932e3191320cb2d5210841cd191510c3366194441cd546410826e62d4c10cb548521073651904209b988540c31e5350010c754f400429d63d4a418f592500863d6494032cb551520c31d53107219ed95300c32e54948108f992500826c6254d108f195315023d65906208f185540ca3c6454d21cb551520423e6414e10cbd53524431d54cc8329b58b540423c64548318f99053c863d64940108f99351483346494420ab98b51d02b46154d408fd9531d023c65487408f98654882ae6210c419798c54c865d6314940cbd4a414434e534ca218f99252086b960945408fd9151082796015021cb54a410c25e6315320ae58241c426e62d52319d984504cab960d4f40a798f215025c6550d32cd144315025e6315010a798f51d033651104308f19153c432c54d4910d354c210823d6414e20cd947400c23c65501108f99432d034d53884208f994414c69d6394a419798c528423c6454632cbd0d5210ecd62cc431e5105310c78d4350932cb94a410c23e6494d21ae580418c23c64546309758e544429d63149409b58b540c38d320c841ad185404430d544c832b358e320ca3f65500309b189518c23e6494c319bd954210b3451cc540cbd4a529071d5494c20d34c9500ca3e65cc5408f597315023e64d45329798f548863f65906209798e534433a545004097596530823e6415032b358f21886b661d4a41a758c425038d320cb40cb952520c25f6355120cb94a410423d64d4532a798c429073464544208f19531d02ae62142418f992534423d60d51218f986540c34c53149109bd95210872e5454830ad18540c434d53c80208f996414c63f65500209ed95200823e650c8418fd91510c23d6414e10d594d51082b96094d40cb548525032d5494b31c714d404423f654c8419bd89544427561d5332ae58241043565394420c795253c871d5350020ae580315023d60d5131ad984531073451105208f99353886776155130cd951510829d6314b40cd952510829f6354940c794e410823d6414132aed81535026d62150308f59250cc63d6414c209758e520863d6595010cd544410833551d00208fd954210a766114c208f19153c823f6454f10cb54a41cc7556114d10c7d53534425d6594c10d354b300c3365110420ae58053d02bb6054540cb95152042cd63c87208fd9152cc34f53d4910abd89515026d62153319b189544c23d6414c10cd947400823d65c85408fd964108277654c431c7153534432e52d0030ab98b315032f52d0110c7d4e414432f52105108fd91518c32d52d0030c754c531063d650c841a758f215031d5350010ae580414827661d4c20c7552530434d5390842cb548410c23c61550208f593538423f65904308f1915188354538c5109759
  | 2 => 0x6054d21c714e414431e5454c108f195215023f654c940b5587320c63e64d4f219b596520423d6494a31a798e529063f65504419bd89544c23f654ca418f59353082b96014841d314d320863e65d0540c755253c874f5314910cd98454c431c5414d10c758c544ca5e63150208f992500873451905408f99353882ad62d4740d914a214431e53d0010ae58041c42b661d4e41ad98740c423e65d0d42c794c410423f6454432c754e4310b2c52d01108f590534827a6014c219e580540c65d63150208f992500c63e6414c10cb148414432e5290731ab58853d032d5250010c754e410429d6314041b3d95320ca3e64940309b195424cb355110430cd547400c2b6618c841ab98843d029e63c874097997314c31d5310c418fd8154c863d6015131ce58054c434e53548109758f540426e62153318f593538863d6494d218f59053c866e62d5030e3551320cb376494420ad984539071d53907219718d524431e5310721e34c8329063d60950329e596100423e6195230cd552510c2b66114a418f191510c27b6054d218f58254cc63d6494321cb95152cc6ad6210d408f990504cb2c52509409758c540869d63c87409d584540c23d6494e219b588540c76551480208f59252c42b960085408f191530865f63551108f99250c86ad6210e428f592508863e61d5132a758f51d033551500308f992524425d63148108f185548826e6214d40cb552520423e64d4a10a7d8d515029d6310841a798c52d029e6314041d954a510c25d6315321b358b318c66e6214e10d554d100429d6310b409b98a534431e5454c208f99250043346494430cd551510833651904308f19151cc23d6494c31ab988535023e6414d20d354e520423e6414c208f593514c31d53d0020ab98a539066d658c8218fd9153c825c6355120ae580410434d520c4308fd91520c67561141328f593528433654944309b98b54cc7355494420d994a510c23d65106308f19152c431c53105108f993530431d5310420c754c53d031e5350e418f993520426e6294f10c714f404423e6510510cdd44414c2746155120ab988439074c534c9209b988540c63d64d48109798c540863d65c87409b58854cc2776154d20e3d91320cab461549408f59641042b661d4841d554f100434c534cb208fd9151cca3f6454632a718d525023f6510410ec905100423d6055010cb54852d026d6294f108f994544871d5454f21cb149404434d53548109798e520863d65106209b98a524425e6314c10cb552520c26e6214c109b58a534427b65500409b588538426d62141319d185544c27765484218fd9151cc23f6454d20cb94841cc67561d50208f592508c65e63148109758c540423e6414a109b58a544423e61950209d195314426e6215330d5545300c2ae62cc7409bd89518c26d62d5231d354a310
  | 3 => 0x92000140480000c000043a088000180408417000020000000801000120040c0dc0f05add004030181b0040c0241f0280900000004000841a02000058044240306004000180700011029568070f8090b40d37400190000807b08819008100000705c1c08801000020095200c2a0b414228050080000c9d0180d00848004946741f06c3903009000440148c00049018001c81100008000000285c01c000082005400000000000c03c53000000cc280002c0043f000050e41a0041504c1803c03034c2004200e807000311b4210f50d004040c03d0540012c970142700002048003500101c00014101c0280291a7200000c3c17800044051b00903c2503c0100c2d280000480f02400054080dc0105c1300d4005809098210002618090040150181a0a802000040580000c7d0c41e0053000c04004008a000048ed00005094040140800400140590780203057314b60080704c0900c000500d0001f0010b024430d00d028330300000f2f5414910ae58051d029e63149409b58b530427661150309758c504863e6414e209758e529063e64d4e108f990540c2b96014c4197d95310c7a441484219758f54c871d5310c42d9549510c2ac62545408f99250cca6e62148109798f520426d6215010cb14a41442b96014b40c754c43d027661d53329798c540ca3d65cc740cdd9151082b761549409798c504865d63d5020ab58853106756115020cb150524431f5350110d3d51320cb8e544c8328f594325031d53d08428f992508cab661d4c418f590504874d4354843d390d5210f1d5454c20ab58853503665254430cb55152cc69e6310940c794e41c871d544c8328f580544ca3f654cb40cd944411023e6494a3197d8d518829d6314841cb949400433751105209e980540c63d65906308f59353c86ad6214241b358b314c26d6294d21b3189434ca5c63546208f191510823d64948218f191534427a6015021d394e520434d32944328f596410829e63148418f592524423d64141318f191534827561d5030ae580414c3365454430d554d51082cd63c85208f990530865e6314c209d587530835553944208f195329065e6514d10cdd92510c2ae62d4e418f99721d023e6590521a798f529073960d53108f984544cb4e524ca31cb152424caad62cc540ad987404429d6310a41abd89535023e64150208f990524c25d6314a109798e52c423f64546209d984540831d53904209798e524423c64547329dd95411073661d53108f18454442b661148418fd9152c431f5414d10d314f524423f60550108f5964310aad62d4e41ae58352d031e53500208f597400423f60550328f994544c73451c8540d5547300c2ae6214f408fd9153086ae6214c419b588530432d5210b409b58a5390678
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x204d08064038e00000200014238044210500ca1ae829a6410e326158054c4287b82a8990658998851cc540a18e2aa2641950e73d4a5290706b1aa429281431d5320c940a48e2a90a4a060e654c83290687baa6419483435d2534ca21c48a430a8088619535804104287396a729c83435d2524ca31c1aa6b10a620e0d6354852d0286b9ca4a14838354d6210f40868e2b2864a062952580410430b318a390a81435ca5350e41e22a6a02200860d654c83250390a9280880218654d6014c41c1ac6b10a89950c76551320ca86392a629a81451c55314d40872e032a6420e3051580414c307a9ac529c83435cc5250940c1aa6b10a6a060d63548521068639aa4292818358d5210841c1aca99065a060d535884310706b1ea5294838a5496014841c1ac6a9085a05497014d3208686ba0a699641439d9544c832a1ae429a86a060d654c83210686ba0a4992618354d6214f40c28a630a808850d75951320ca86ba0a6992418c1456010520
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x1003400a0481595320c94080e87995320ca41c05631c55214940a048154d6214d4080c87595320c940906819d9544c832
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/35+packedAt s0K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/393+packedAt s0K5 (21627+(h % 393)*10) 10) % 801)
  | 4 => 2*((h/288+packedAt s0K4 (29678+(h % 288)*10) 10) % 781)
  | 3 => 2*((h/25+packedAt s0K3 (2744+(h % 25)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s0K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xe0fffe1fffffff81fe1fe1ff87fffffd18f1ff
  | 2 => 0xff07ffe07e1f87fe1fe1fe1ff870707ee73e93
  | 3 => 0xfff83fff801ff8ffe001ffe3ff807f8307cf1c
  | 4 => 0x3fffffe000fffffe0003ffff8003f80fe0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x28000204100400004402402400941420085025
  | 2 => 0x42518443242908160a20a20988212158632692
  | 3 => 0x8432a8890d5241aaa1113542d5024b0b058b18
  | 4 => 0x16a53112490352cd33541103664b0213b00dc0
  | 5 => 0x18c621dc719c64f1dd99d990440c0c63def000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcccccc0fcfcfcc0fcccccc0fcfcfcc0fcccccc0fcfcfcc0fcccccc0fcfcfcc0fcccccc0fcfcfcc0fcccccc0fcfcfcc0fcccccc0fcfcfcc0fcccccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_39527
namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x241810c14401c04c4000240000040105098084000fd43fe10ff41fd42fe31df30fe43fc31ff42ff31fc21fd20fd31fe42fc20fe20fd21ff40dc31fc42fe41fc32ff43fe21dd30ff20de31fe40fd41ff10fc43ff32ff30fd10fc40fd40fc41fe30fd30ff21fc10fd32fc30fe32
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x663de310c2bca6107dc8621bf28461dc410c7be60107710330bf2a2657d51cc3baa3987b88120dfa1887de418c7ba84987790b30efa8e61f741907bc6310db14910ae29a217f5250ef8a9085714d21bea90215f5350afca518f7d0d309eaa065f7314c6faa8197754231dea10857c53083be60187794f21bf28c637f54086fca210dfd4c20bfa92217d508c6faa910df55130ef98441f510042baa7087794a31fd88221dd434cafca220ef50940eea9c21fb20882fea9985754031ef18a63de31443b8a5985fd4143efa12615d53c87ba8621df54742efa8a617d510c2fea0a0df14f10bea9c637d5310afaa6905f54e41efa18657c54482faa998f710831ee18a817c544877e84a05f54610eea1c637e51d0bbaa818f7cc310eea0863dd320c7bc6210f794f41bfa82657e54042faa1215f552439f2a0217d520c3f66098778c831bf280657d51083ba60086b50842dfa1085f721486faa6085f54a21deaa0217d53106fea708778c720bfaa021bd41d02bca7105f54843bf29041ed4210bbaa2987b54b41f799265de21cc3bc86987794e10bf28c817c50487bc83985f15131dfa08837d53486fca321778c521af29c21be41102daa4085bd4910ef29c81bc54442faa190f74c730bf28043df414c2f8a4a1df94621f799465dd428c7b863185f54c20f6a12657d53882fca39977cca31bf29c837e548c2fca3105f95032bf2a2617f54887be4298778c740bb288417e530cadaa421dfd4941bf28e87dd43cc3dc42104f95020ef982217e53103da85195f94a10ee192617f5150fec6218f7150319eaa6437d51ccbec8220f790831ef290637e54082fca5185f15232fd080217e53c42fca9995f55321f610841dc514c2fca0217b90a21bf292217d5490afca8215fd5320dfa0081f541c43bea690f70c520bf29661dc520c7b8a6885f54b10bfa8243bf41503bca7107b88620fc980617e53c86f8a2a15794631bea8c87be54082fca3987b94810f690a41dc31842baa118df54a30efa1c63dd21cc2fca821f7cc320f6292217f51483b8439877cca32bfa8a617651103be8518df94c42bf288617f548c2fea8905f94f42bf296637e54cc2fca9885f55121fb28841dd500c6f8a4a0f7ccb30efaa6617e53086fea9086fd0a42aea9821de514c2fea710f754831ee18841dc318837883205714f10df212857d53102faa0215f95040eda82615d5310afaa120ef50d42bea9e81ef20082fea098dfd5332be298217c5050bda84907794c42bf2a241dd42cc2faa221df94f41be2a6217c54cc6fea7105fd5232bea9c617e50c87bc809877d4831be2a661f541443bc8621f714d21bea9e85df548c7b863887794c10beaa4417c54042f8a708778c410bea9a217e510cbdc85905fd5231f721043ed320cbd8431077d4a31bfa9a417551103be87985f94b40
  | 1 => 0xd30842fca710df15130beaa4817f54c86fca218f794231aea9c61dd53102f8a2905f94f40efa0863dd420c6f8a4a05f55310bf28087bd540cbec82887750631efaa2617f53506fca6185f14d42bfa9a817f53486fea7906f90d43f6a1043dc41cc2faa8107b50b20ef20661dd53903b8a6a0df94231bea8465f7415077a85a05f14143bea8c81f5310c7bc62a07710a31eea1e657d53c42faa9197bc8621f729087dd328c6fea818efd5110ee21c657c54c87be8418f74c020beaa0637d5110afca5217d88510ee21e615f53443ea43885f54e32fc900417f524c2fca2215f55241be28265ed52042fca5a0ef95010ef98e61df310c7bc6518db94810dfa1e857e54887bea818f794031be29c433d54082f8a910f78c730ef21261df53506fca110df54e40ee28063dc31d02fca7905f94d21beaa6615f53c43ba61105f54032beaa2637c52042fca690774cb30ae29a837d53d07b880985f15320bea9c43de510c77e85a06f55020bea8c85fa300c2faa520f78c630be29e43ef4250bbe86a1f750330fb108437e52c42faa7085f15230beaa061be41902fca521df55320bea86837d52842fca0185f54620bea86657f524c6fca6105f54a31ee98621f7318c7b885987754a31dea0081de324cbbaa918f70c721beaa463f541106fca5a1df54021ef21863fb10842f8a7107750730ee980617c524c2fea2a05b94b41ee18821de414c2f8a818d794c10fd100415c514c37aa990df94831fa90a217d51d02f8a690f70c530aea9c81de32cc37e8721f788530f7908437c53443baa9985f54342ef18a41ef21c82dca421dfd4d42af288637d52883ba6298778c610bf28c617d52cc2fca2105fd5132fda04817d5390b7c82a0df95021bf29087bd4310efaa790df94821bfaa2615c5350bea4210efd0740bf280217c53087b86418f7d4b30bf28c657d53c82fca1205f15021beaa221de544c2f8a9995f54632bf29c81df308c3ba60885f14540f721085df53c43b862205f54031bf2a641dd53043bc621057d4d41bea9081ee424cbbaa8987750d30bf28665de548c6f8a9105f54831bf284417e51c82fea5885f94440bf286877e52106fca198f748530be29a81dc31cc3dc851977cc120afa9a437e500c6fca6887794b30ee28e613c54442fea8185f14910eea9261df404c2fca918f7d4d10bf29c417c54442f8a8185f94e42bf290857e548caf8a2a1df94342ef18c417f54c43b842985794c30bf29c21dd52cc3bc62205fd4810fb88021dd30c82fea2a15f94041f7212417e50082fea790f70c640ef98421df320cbf640907754f41eea9885dc5350afaa2207ed0140ef298417c53c82baa7a0ef50841ef99261df4390e7ca8196fd0240bf288217c504c7bc63885f94341df2a643ed5210fb88618df14532dfa1083ed20082fea9105f94241bf2a
  | 2 => 0x1d82012056000001e8104a822098120402a008360000004814210094e00217808280681880000022000520080430082398020007a0102200014040000283003850000000180020830298120281a1d820af0c6008040183203080b00621223c0b80e0080402806008080a922000694e0040000003000000001c004048381b800029de018a803008008760000c01802000080001c000061e24e058000e80000000178025301c00004008100000226000000000001c00898010520002a020081785e04840000380502e00008000182500a02001280000180e0d16014898f200217006028080cb72c90300730201814000de33002db20005212690007a80002000018360000a0a800078040000e008580300609048000404d00a000000380a009000601ae8014029be0100000002088c4000000d81003002050008401e010000000e0c8480081c01800042b80c800000080383c0000cdf03800056398013081e17000040987082800800150341500416808005f55210ee21a617c52843de41106f50a41bfa8a657d50107b882987790e31bf290817d52443be859877d0631ef28e61de410c7be6298778c721aea9c415d53083ee21086f90140bea96877e50843dea488778c530efa06617e54106bca6207d94440bf298877e5090fbca998770c430bea88657e54c86faa9185f54a43ee284637e540c3b86518dfd5020eb288637c54083bc86995f54a40be29a41dc54cc2daa4205fd4c10efa9a85ee320cafea5085f95210af29c81bd41107b86310f754c20ee29463ef4290abca6214fd5110bea84877e53107b8a918df94443bfaa221fb308c3f220085f94a41bf29465ee21487daa4205fd4d10beaa0437d544cbb884985fd4c21eea02617e52903bca4985f54b41faa8881df524c3ba6498774c431eea0a617e51d027ca990fe90040dfa1483df504c2dca4205f94643bf28465de43cc3b8a898770c510f7290815e53c87bca6205f54630ef19261df21cc3bea118f7cc010eea9c41f610443de42907750c31bfa9281ed42887b8a78877d0730baa88417d52cc6fca890dfd4f10dea1e85dd320cafaa1a1d754c40be2a463bd41502faa110d794730ef21e65df438cb7ca8195f15032bfaa0657e544c7b886197b94b41bea98437d52d02f8a6a0df54841bea86637c52c42bca7a0f7d4031ef18c81de304c2fea890efd0d42bf284857c544cafca02077149309eaa021dc32cc3b88318f795031ee18e41f551082fca888770c521fb10e217d5010fb86210f710e31eea9e437e53042fca9105b54b41bfaa663bc41102faa8085f14530be282837e520cbba60907b48421f690e417d51d0efca721df54720ef99063df318c77e8320df94c31bf290617e52042fca320dfd4142ef214637f544c7ec83885f55332fca00817c524c6fca818df55120efa1863d
  | 3 => 0x38fe1f862000c6040265b00008006008000000c032fe0980a008040b11014586018420296e0180002000
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x6539025f6550b309798e54c4355518c44097d8d544427561d50209b98a524425f6355121a7992528c6ce6215031b3588430cb1d5494c2097994404c32d548842097997314c354510c540b5586420c6d76155130b3988508c65d6394a419b58a544c72d5290440b3588500c65d6394242b6580214c34d5394810c795153c86ce6210d309b98a534426d62153318f99053c86ce6215130b5584404c36652944409758e54c425d63d52219758e508863d64141219718d519025e63d45409798e50c8755510c440e3d0d428cb2d52104409b98a544c6ce6210c31b6580540c6d6611033097594318825f65509308f593520426e621502097597300426e6214810d5947300825f655043197994314869d6494a31d598753c423e6414c21b6980520c65d6094f219758f514829f6454530e3508420c65f6354910b358b41cc31c548c510d954951102796014c21e3508424c35451d0530d350d5210ecf625513097d81530423e6414f209758e50107655244010ab58b41d03555394440b3988500c6d96095130a799321cc30d5350842c7150314423e64d4c20d3d4f524425d65c8730a799032cc2d9608c4109b58854cc25f63547209798c548834e5394810c715130442ad64c8720d518d511035653944409718d51c826d629531097d8d540865f63546209718d5110a3d6414c109758253d066e62952318f992528c71d54cc8329d584548825d658c420d914a214431d54153308f596411025d631481097195434c2cd6295231c7552310826e6514910b6d81514c25e63d521097d96319025d639402197d8d54c826e6295110d5144214c25f658c410a7593528c65e63150309b98a54c425c6550530c7551300832d54084208fd95401029e64149309719521cc27b65480208f596540cb1d53508429bd89544425e6314810d5d44315025d63948219758f528434d528c410cd551510831c63550329798f54c865f63546409b98b540425c6354b10d594e510825e6394d10d658353c42d4614c1109758e50d0aad62d0540d314b304431d540c4208f59252442cd6215031b6580414c25e6314c208f99353c867761551208f59053086da60105308f59353c865e6394341cd546411026f6550842b398b51cc34d524c010d35885350a5e6590130d9547200826e6215030ab58b411074d520c4109758f54843546354420b5987520c65f650c64097583535072f435484397d94318826c6254d109d984548c29f6454930d3548520c65c65507309758c528423e64d4e21d5144314838e53508429d98453082d76154930cb951520425e61d4d42d394b300431f54d4d109798f540825c6154e2097597410c6ce621033097d95414c356518c630ad5874210754518c530c755153082d960148319b59642086cd62151309758e544865d6590c31a7990500c65f654c431
  | 1 => 0xc23e6414930975835350ace62d0431c755231c865c6154c208f99252c427661d502097d8d544c65c63553209b58a548c65f6354740c795231082cd6210c319758c540425f650c4108f993520432c54508218f59353886d661d083197d95428c6ad64c8421d9949511025c6354420b3d89514c23e6414c209d58453082776548421d354e4210a5e6114d42b398b548c65e63d50309b588505071e544c0209798f514826d65948109d5845050ad66114a31cb151424cb355110440b5987548c71d540c721b658051cc25e63d5010b398843cc2756115230b6980540c6d56110330d5546310823f6454d209798c54c825e658c510f48c5100434e535481097d95214c31e540c420b518530c43365454420d5d8e51082d661cc110c795231043355150040c7d52548c71f548c510c714f4350a5e63151209798f548825e63150209798f520425d6510c31d518e510826c6255110d354a311031f544c110d5986510c755514c020d9544210829c6454930f44c1100431c54cc11097d96310825d63d4540975973008355535444097580534865d6510930b658052cc31e544c0109718d518823e65d05409799453442d66115231cd152414425c635491097d94310825d65d0c32c7950310426c6254640b3588404c35653544409d984540c3355444010d5544310825d6394b109758f54c871f540c5109759431042ce6215330e350842cc27661150109758c54086d9600c640c7553300834d520c44097994314423e6414121b658231c425d6594c109d984520425f6550831d354d4210a5e6510b3097195428c65e6314a108f990530426d62152308f992520865e6395121cb5095010ad46154930ab1894350ad46155130979865310a5c635512197d8153c863e64150329798e5090a7765504419e580540865e6395110a7990508c71e5494f21d554d510827661150209e596100425c6154c4297d815310a7b654c03097597214c25d631494097d8d510825d6510c3297195420c71d5410c31975825310b954110431b318d428ca6c655093297997414c38d43509329758e50d066d62d4c10d3548524c25e6394b10c7552310425e63948219798e5010a7661d52329798c530432d5448020cb153524434f5314910d394e52d065e63d45429b189544c26f654842197d954310e5d63d5010d518e511029d641493097d95300c25f650c440d354b300425d650c4409b58a5448756510c7309758c505066e6214141c755043cc23d6494b108f191534425d651083197580535071d544c01097994428c6d661d4a3197997304431e5450e31b6980214c31c5414d10d3548320c66d62150309798e534865c65509309758e548865e6590d32abd954210b2c5250940c7550310425d6394020cb50a5110ace6210e319718d52d038d4210a318f593530425e6194c409798
  | 2 => 0x6115030c7952530426d65884209b58a544425d6315210b658031c429e64148319759431902ce62d07309758c54c874c524c11097195434ca5e63150329798f528425d6315120d394a310425c65485309d587548ca5d658c4109b588548425f654c832d314831442cd62d0431b358843cc34e528c440e3d8d4210a6e6215230c7551320ca3c6454910c755153042ad64c8520d314f524423e64d4c109d986544cb656114910b5587420c65e6394221cbd50524425f654c0109b988540429e64d4730b5984540c65e65109309798c525025c6354740cb54b401025e6314141a759321cc23d6414930d3948311025e63141219759442cc34e524c010c795330082ce62101309d185544c32f65508429758e509074d520cb308f596540426e65c85209758c548825e63940109798f548866f654c8329bd95200825d63141429798e500874e520c4108fd954210a3c645462097994420c65d6014d42b398a548c72e54948109758e5244275619513297d8d54482cd6210e329ed81544865d639404297596310c25f6354841d694d300c2d661d503197d8d5110b2d548c83297195304434e5354b419719542cc279601503197986538826d6214c10b6580318832d54c80209d9845050b2e5450a21c755153c865e6194c20c7d53304435551cc020c795330042776155130a759351cc2ad64c8621c7153534435763944409798c5050b1d5494c10b358840cc3655148020d3d4a314426e62150329718d544829d641403197594428c67465505109b988544c26e6214c10c7550540c6d6611483197d9521cc27a6015021cb54940102cd62d4730a7590328c67a6014c21b6580314826e62d4c109718d51d0a6f6255130cd547401034e5354840cbd53524431c5450d30cb150524425f655073097583534863f64546208f590520426d6215130a759052cc25e65c8530c795253082ad62d064197597414c34f524c110d354d521026e621503197d9631102786055121a7590324c25c63548419798e524425d6314121d3d48314425d65d07308fd91534425f6354b109d185544831d541513097596311025e6315021c7550430cb4f5294a319b588540438d5350842a7993528c71e5454c20a7590320c63d6494a31f10c5210863e6495110d954621082ad6490842d354e52d065c63546428f990520432d544c8329b58b540431d54d0c32b398b418c72d54948109798e501072d4354843e318d4210ad960d47309b988548429d641483197d8d51103565354420d954b10042d9600c410c7d50534425e6315010b3588434c34e4354843b3588438c6cc62545309798e50906cd62d523197d8d5190a3d6414a108f992524426f62546409758e544434d5354810c755330042ce62d053097d8d54c433554944209dd85534826e62153309b588540c756510c43097997434
  | 3 => 0x1004160983d1ec2805804020000080e03013184140000901599000002c49a0001200400384059340100006008042740000033010070042a10125000ed034012d81e1040a00000000005302d01006018070041e01414024054d000000000300d0300301c22020040344205006100070080200803074010184700c100781111800000065580c000051180500c6c0940201c0b6ec084743d008050800104c02014950840a0000005005008030a4010e80300c0403c0100c0d00000230750783b0401c00c28000d90181d0084d01c0000d590143e0000000c0110c120180501002008001640001446018b21ec1b00007000040080000400034030140b02c0000007028000000a0080b0300002408004020000005400028f5014080141d01c153ec1f000020680001811000b50040602000040674341a00400044000185e6e801004130300409000544130b80e060140000b008001640103c070680401418150000c06768c02864010001300000000000603702c157801e000030025c6355110b3189544c25d6054c10b9586420872c5450920b6580315023f645491097185531034d5214b3097596319025d6315020d59463110356518c42097d8d544ca6d62d52319758e544c73654944208f596540827661d4c209798e529066f6254d10d354e52102cd62153308f593530829e640ca319798e50d0a3e6494d108fd95411069e6414b308f592520871d53d0842b5984404c26e6215331d314c5244277654c4319718553903566114f1097984534434e53948409758f540823e64150209758f5204357510c520b5986420c71e548c721975963188356514c020cb949429065d631532097d963188356510c440c755253c865e6394020b658352cc2cd62142319d984548826e62d5231d5944310831e5454c10b6d81544c2746548510cb15142c827b6544010cd584544425c6114d108f59053c869e64c85309758f548832d535084297994534865d6394321a7990324c25e6315321d3149324c25e65d07309e980540c74f52cc1108f19153483655294440b598730c429d640cb308f994544425f6354742d5d8d51102776544010cb551520423e6415010c795031c872c5450a32d5d8d510825f6054f41d5147214c29e640c831b658354cc2cd62d05309718d54c426c6550920d554e510834d5354b419d584540834e524ca318f592534427561d4c209799721cc26d6294d1097d8d52d025d6394010b6d81524c25e63952218f590530829d6414231d658053c429c6454530b358b418c74c528c51097996314867b6550040b6582514c2d9601533097d95300823d6414f208fd954310e5d650c4209d185534825c635444097596530823e6414a109758f5150a5e6315210cd553100425c6355021a7593214c2d96094930d5144414c275
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x280c1440c1d55c501a50f300018a1ae52a28718e0d6454852cc286b9ca4a1483835954210b30a1ae92926518e0d64548524c324a92c029063435d0524c930c1ccaa108518f11544c110042873a6a52946383591520cb30c8cc428e8298619545803104322290c298221431d54350932a1ce5aa4a918d0d731514208686b90a8a1a61835915214831a1ae62a2859061454185304430b320a390a6192549600c410c1aa8b10861960d65508424c306b22a419063835516210f30a18e2a9a84216505158031482a238aa4292614a5c05450821a18eca9a842150d731494250306b2a8421063835516215031c1ac9a94a518d0e7654d4210b07aa2c52a463d05493044010ca0a2b0062a050c72550544c306aa2c42a661865516015031ca4c2b00a78850d73151424822cb80caa106343dd54210a31a18e8a90a49851471550544c286b9ca8a1443431d54210930c1aa8b10a89845471594424c306aa2c42186343dc15350842
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x1020a04815954210930906819d9535084280e879954210a31a0481551621513080c875954210930c05641c55214930
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s1K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/330+packedAt s1K5 (21627+(h % 330)*10) 10) % 801)
  | 4 => 2*((h/302+packedAt s1K4 (29678+(h % 302)*10) 10) % 781)
  | 3 => 2*((h/18+packedAt s1K3 (2744+(h % 18)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s1K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xe1fffff07fffff81fe1fc3fffc3ffffd18f1ff
  | 2 => 0xfe07e1ff83ff87fe1fe1fc383fc3f07ee74e73
  | 3 => 0xfff801fffc1ff8ffe001ffc03ffc7f83078f9c
  | 4 => 0x1ffffe000fffffe00003fff8003f80fe0
  | 5 => 0xfffffe00000000ffffffffffc0000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x202080110001000022020048880492100810a5
  | 2 => 0x44914222194a08160c20c41114412168634652
  | 3 => 0x8852554428d441aac1116a8226a84d0b058b18
  | 4 => 0x1d659989528752cd77542204bb320633b80de0
  | 5 => 0x1186110e631864f19999b32702200843d6e000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaa0aaa0fafafaaafaa0aaa0fafafaaafaa0aaa0fafafaaafaa0aaa0fafafaaafaa0aaa0fafafaaafaa0aaa0fafafaaafaa0aaa0fafafaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_39527
namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x150600030008060dc31be40bc40bf41dd30de31bd41bd42dd32df30df32bf42
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x280000135511025aa4205354b3096a968359500c71a84995354831
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt s2K4 (192+(h % 18)*4) 4) % 12)
  | 3 => 2*((h/9+packedAt s2K3 (189+(h % 9)*3) 3) % 7)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 3 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 3 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 4 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88eeeeeeaaeeccee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_39527
namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0xc02006400000000003420000800100402c00420031830c0000fc30fc10fc20dd30ff40fe30fe40df30fd43fc42ff42fc32fc21fd10bf41fe43fd42fe32fe41ff43fd31ff20ff32ff31ff21ff10bd41ff41fe31fe42fc40fd30fc43fd32fe10fe20fc41fc31ff30fe21fd40fd41fd20fd21
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4435e530c3f440886f50630eea9c813e54106fca990efd4341ce29a837e52c42baa7086f95020bea8e817c528437ea89077d5130fc980617c50506f8a4886f50610bf28843bf41c83f240107790c43be2a221bf414877884205794c20dea0881dd54cc3de4310fb8c921bf2a463be42102f8a2986f10c40df21283bd41c87bc43985f94c30f7a1285de514c2faa5a07d48710be29a21b541c43be6318ef95010bfa8265bd32506bca7205f55330bf284637e51083bc6518df54c41bf29e41df30882fca9185f940209e2a2419f41cc37884a0df54041dba8a83dc52cc2dca4205f94321be29e417f52c43eca2207710530bfaa2637d52443ec6218ef94d41beaa0417f5150b78a6a0fe88210f7212417e51102f8a998df94430f6a90817f538437886a0f64c110be2a6657e520c2fca5185f54d20bea9c217d538c6faa9187dc8621dfa0c43df40cc37a85a05f95131bea86877f5250ef8a6107ecc230bfa9c437f53042faa3905e94031bf2a081dd30c83f240886f55010be2a4437d52903ee6298fe54031fba0c83ef21086faa5a1cf55310faa8841bf41882f8a2995f94a40ef29661bf32507bc42985f95032fb208837e539037ea4a0df54231dfa0e61f5214437ca810df94b30be282637c51502f8a690dfd5031ee98e61ef214837ca9195754e30ef192657f53482faa221dfd4c20bfaa2417e5090bb863985f94631bf28e87d930842fea4885f54810bf29a43df53507be60906fd0240fb20e21bd52506f8a9885f54840bfaa665be50506faa121df54a20dfa0e815f53486fea6885f94910bf29841bf53d07baa6205f54021be29c417e518cafea2997e4c110bfa9261bd54082faa3105f15210fc90421dc21cc3b8a2985f94621bea9443bc53d0778a890774c220bf28e85de53042f8a6905f55130f790441b541442f8a8194f15130bea8c81bd42d07ba6218efd0531eea8e619f414c2faa2185f54e41bea8e617e52843b88718efd0431dea08837f548c7ba43987754930dfa16817c54c83bea9985fd4940bf2a663bc32506fea9986fd0530bea84837d50d0b7c86a0f7cca32dfa0a417d544c6fea498f74cb31df2a463df504c2fca198df54e21bea9c617d540cb7aa818fb50842dfa08437d52107bca6205794c219eaa063df404c3be87985f94f21dfa1c87f64144378a1a0df95043bfaa4617f50487f261085fd5321bf28443bd41c83ee20087e94031df21a857e508cafaa110df94043bea9a43dd53042fca810dfd4d21be29263bd42503eaa2205f95330dea0e61df41cc3bc83985f94732bea8c6176510827ea8987750b30efa1a61f7415073a8398774c530bf28e813d54906fea6a0770c530bfa8a617d5490af8a5885f15132bea8841df514c3b886995f55120ee29a83dc214c2daa4205b54810ee29a437e53087ee4290fb94810
  | 1 => 0xd54c42eaa2205fd4141f7190657e5190efca4086f50941ee21661dc51cc37e86a0f714930df19683de320c6fea8194f95221cfaa2617d54442f8a7887710330baa8841f5310c6fca890df94c31ef29c415c53506faa621778c531ee98621dd30083de40106f50f41dea0c817d53903be61185b94831dfa0a21df424c2f8a6a0cf95231bea9483df31cc37e84a07754e20bf28061bf418c7be6108774cb30df2a4437e50902fca0087e8c210eea0e617e500c7da4210df54c21bfaa021be43102fca7106f90942deaa043dd30042faa920f754e10fd98261bf4310efca4215f54321bf29e817e50906f8a898f750130f6996437f52842fca6205f94a41bf29083ef324cbbe6218efd5130bea9c413d540837ea5a0dfd5030be2a063dd514c2fca899778c530fa90843dc43cc2f8a9105794c10bf296877c52042fca521778c930ee98221bf41c87baa610df95310f6a12417d54cc6fea998df54a31dfa0c61bf41cc77e82205f14132bf29883bf418437c85205f94e43eea1a617e5290f7ca818ef94941be2a0437e50d0efaa910df54f41ee99263df32cc3be86a1efd4541b6a90637e52087f2a010ef50430bf2a421be42d06faa9906f4cb41beaa061bf42506bca7087715130aea98217f548cbbe43985794e42fb10e217f544c2fea79077d0e31ef2a2617f52506fca6086f10a40bea9e81bc42d06fea910df54432bfaa2437c50486faa3a1df94c32dea0e217e52d037887205f54f10bf29c21dd4310efaa890df94630de21e833f54483ba82985fd5210dfa1485dc430c7da641967d4d41f729081bd41082faa810f7cc530de292836e52043dc85904f55231ee984217d5390bb880987b94831ef18261bd41502fea9887d94420bea94877d5210efea810f754b30bf28887bd53d07be86995f54b30bea9e85bd40102fea7105f54742bf29c857d518cb7a82085fd4d42de21a85be54c42fca8105f54442ef21261bf4210afca80877cc931bf2a441dd324c2fea790efccb41be28287df51cc3f681205f94d10bf28487ed20082faa9997d50441de21e85fa20083b883985f54c10bf28c837f5050afca3205fd4f10f6a90217e528caf8a2a16f8c941ee212617e548caf8a0a16f50842beaa4417e54ccafca818f70cb30be2a4657e538867aa91977d0f32bf29885bd548cbb8869877c8530dea1a837e53d0afca8186f50510bf28085f621442faa7195f54830dfa9a83bd418c6faa8995f94021be29e437c54486fca4205f15010be2984379500c6faa818df95110beaa4637e510cafea2a07b54831dea9a83df30c827ca810df54043f790e417e520837e8220f794930beaa0217c548c7f680a07754c20bea8065bf505077a8621ef54141be298215c53486fea9907b4c921bfa8263dc320c77a8398f7cc930de196837e53907b864985fd5132bf2a
  | 2 => 0x530a82f030010b416000009ec000002d858030000002400050000f4220440e050470c0010a0068d40204c00000001940608808009d6000020201000000004020bc0007d010040309c020041500058014041ac060000200000010ed2c1af0000103c0ac1c02000000880002c2500403008020003a13806049250640108401000020fd1b0b0000001b06c0200000084124269a0701a00010014000002c03881010010080a000080052d3e006018940040100009000360000a0201707000004010001e084a70000a0180000000124080182a18039448000050e01005000050000001c004dc060000304021002dd0100d0001402c051c000028030000000007010161040001c7212806000000040100008010000082a010ae0a8020000002802030010040015c1009c0000c0805c220f010beaa643bc50507be61887790f30beaa465dd30483f6411077d0c31bf29887bf43d06faa790f7d4b30dea0c437a500877a83105f94720ef996637e511067ca9886f90e40bea8085df524c2fca820df94040bf288857d51103f460185f14d42bfa82877d50cc77e8020770ca31eeaa2617f51483de85215f94b419eaa4437e50d0af8a8185d94440bf28c417c540837aa910fec4110ef20661f510042fca518e715130be2a2417d508cafaa5187794730f690e41df300c2fca3985fd5220bf280657d50ccafca1187748530ee21e65df42cc2fca1107754e42fb884217d5090b7c87a0fb88120f710a43fa40102fca99057d4d41bea8c85bd548c7dc8421778cb30fc880217c53843bca610df94041efa9a437c548c2fca418efd0640bea8e65bd41d02f8a2907794e10bf2a085bd410c6f8a4a05754c20dfa0c837d52c42f8a4985f95120bf296637e510427aa810fd50710bf29e21df300837c80a05f55310fd902417c5250f78a8985f94332eea12617e53482fea8886fd0b41f6a16417d50d073a82986f94341fd88421de5390b7e82185f15321dea0a63be43d0a7ca8105f54a10ef29c817f5150ef8a4a0df94f41bf286837d54843be60085754c409f2a0217e50843ba64195f54b31df29683bf41502faa9207750330bea9e41dc54cc3be82985f54b41dea0a41f541442f8a9987790530efa1c87de434c27ca818fe84010bca80437e5210fba87985fd4810bea9a21bf41c437aa5a0df14e21dfa0841f940102fca4195754e40f719643bd41087ec4210df14d40bea90637e5190afaa3085f94431fb082217d5490fbe60885fd4d41df21a87f7318c6bca7107794c20de296837d5190fbca9985754c21f799465dd300c3f460886f94f41dfa08217d53082baa7215754e20ef20261de31cc27ca9196f54341be2a2617f53087f4a010ef50521bea8063de42cc2bca6205f14543eda82617d53103da42906f90541ef990657f54082fca8984f55010dea0a61b
  | 3 => 0x9c100600017c0500c02006cd178070b4025580206c080cc3c0249f3b014000000000502c0b054150000900000048025f4651141d0480a05c2002c06020000040915009158140ac0201c003c80100400000c400c12650045bc270f16c000680e0040d424038150680009c542e00002c000000702c010d40047c6b0707c000360e400000010
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd520425d6314a10a759051cc23e6494d2097596530425e6315010cd551510833b41940318f191500cb9854d413097d8d54c429f6354941ad58753d069e648c8319e580540ca6c654c9218f590514823f6550420c794f410832e5250440ced06500863e6414910d6d95304432c54909209758353506da6088530cb553200833664944209e98053042ce6214530a758e505065c6354b108f590514cada600c530f450530442db6055130ced05500865d6394241a7994535079941d41308f992510871c53141418f592510871c5414530ce551500871e53d0610ce505500866d62152308f99051483695284010cd551100425d60d4d219719521cc25e65101308f59251cc31f6454e10c754f410863f6454d10b6d95308429e6488530e5d4f515066e6214530a7d91514c23e6414b10a7592214c2786548110da48550086cd620c730c798f54482d960085309798c540832d5454831a759021cc23c6454910ab189505063e64944309758f54482d960153309e98354ccad96388210cd991510831d5410e31a718d411023c6454a10cb952520426e621481097d81530425d63d52208f992510ca5e63d50209758e52d0798644c110cd547410836a52940319798c540874e524c010cb54852d072d52d0440c7953300435a6354021d9549100425d6590b308f99252cc74e539484097195434c34d6214d218f593530429e648c932cd109511023d64944308f99353c823c645433197994534876b2154021e6505304431d53d0410c755330082b560d4541cb549410427a60150219798e534869e6390a409e980540cad960d4b309d987530839453d45418f997425023d6595031d698d500c6766114c20c7d8d54886b86054941a7590314c23e64d4e21cd95141c423e64d4f109798f540423d6494832a7992324c26e621501097596530829d648c930e5507304423e658c941c7953328ca3d6414f10a799251cc29c65d0530a7992514c3d2214c110a798e535067661d50209798c52c432e4354840a758e425063d6414a10d994a511031d5350610e6500404c2d960951308f59252cc65e6590b30cd909511023e64948329718d544423d64d4b109bd89544429e6494930b398831cc23c65d0530d3548320c63f6454e208f993520432d62151208fd954310f1e5494c21d68c9500c6da6010530c7191538823e6494730c754d418825e6394341b658051cc25d65087309b588514c25f6354720b3588314c31c6454e10c794d410434d52cc4319e583540863d6494b3087195414c31e53d0430ad185325073651506309758f520431d5454c20cb552520c6b7614c941a758e52d06ae62141419d185534831d53d04408fd95401023d6595021cb94b410425e63d5320b6d81424c2d46154930cd952510832c435484097d95300c27960d53328f992518c27a6015031
  | 1 => 0x23e64951309798e5090bc93048020da549500c63f61550208f992510c74f43548318f5905308758654c1109e19530443e121481109758c505063d6494630e9505210866f6548020b6980214c2766114810a759352cc31d53d06109798e52d0356514c020c754f418823d6414c20a7992544c2d661103309718d548865e6314121d354832cc29e6390941c794f410434d5214b30cb549410c66f6548421c7552530869e6494b30a758c50d065e6315220d554e511026e6214c10ab98a4350a3e6494732cd552510833551d07408f99632d067a60d4c2197997434ca3c6454e20cd547411023d61550108f191534829e6394141cdd45415035551cc02097596424c2cd6210330b6d81514c25e63d48108f191538423d658c941d310d520c74d53948109758c5050b365450441a799352cc23e64d4d218f994544834d5354840cb548525069c6454930c719541cc3b36050510c7d51304829e648ca3197597300825e63150309798e50c866f6550842a7d8d505079761505309758c540433a54540319798e500829e63141419dd85534831c53d0d419798c530875931540318f99353086d76154930c714d52506776544010e6d05308426e62d5010cd947410836a52540318f59053887976350710cdd9541c423c6454d1097580534872e52d0431d354a320c63f6550842c794d419029c6454530a718d525071d5350640cb55152043d3614c110cb54b410c6d960087309758f54c863d6494420d3548524c25e6314c20c755153086756115030ad584325072e52504319e5835308755535442097195414c29e6488730ce552500863d65d04209bd95320ca3f6454a10ad58453d06b56488710ce552500c71c54d4930cd90d511025e6314a10ced05500c6766115030a759221cc2d96014b30c794f411023f64549109e980520434c524c930da549100433651504309b988540c65d6394021a7592524c26d6215030e6d91308426e62150309d984548831d5494c209e980538865e639401097594214c23d64d4f20d394b30042766115010d354d210866d6215031ab58850507b141c41108fd91500ca7b65500408f990504866d6214c10c7552530423d6494d20a759251cc2cd62101309e580514cad66110130cb54842d06d960d5330e518d41c425e6314910ad58452d06d960d47309758e50887344354440dc545200827561951328f99252cc35832540319758e50c869d63d4b419758e50d0a9d648cb30d9949511025e6394342ad58752d06d96388110c7951530435a6394021b6d81524c25f6550530c7d50434c31e53d0421a759031cc2746548510d5545300826c65509209798c514834e53548409dd95310c65e63d52209758f54c825f6354442d6d95308429e648cb30c794f418825c6548530ce952500c77121540219b58b540c63d64d4e21d394
  | 2 => 0x621013097596320c65e63d51209b58b540423e6550530cd545410825f6054e428f592510c73551504308f990530829e63143419d584548829e6550530a7592314c31e6514d418f596540425e63940418f593530866d6215010b558440cc2ad6214341c7953300831e54cc310c754d410425f6550c43e5d8d414431d544c010d658d500866d6594810c714f425066d62d4c10cb551200831d53d06408f99741483355150620a7195414c32e5494831b9185324863c64543219d584540832e54548109b98b54cc23c6550520add85535065e63951218f99251882da60087309758f540829d60d4d418f99052043394194031ab98b53d06b5619494197d95300831f6454e20a798f52d063c65505309798e52d067561d5020d658e50086b5648851097d81530863d6414121b5584430c71c6355221d594d51082d9638c1108f99254482e86050920b6580424c25f6548530d654e500871f54cc120c7151304823e6414a1097597300429e648c7308f586548cad961d41309e980530863d64d4f109e181544874d524c010d5947300826e62d4c10a7592514c31c53d49418f990530871c54d41309718d5110b1c54549309b98853c426d6295131b6982414c31f53d45419ed95300c2ce62d0d32e6d07504c23f6550431add85525065d63152109798f540865d6314121ec506304431d63d51308f592518cb1e53504308f990514ca3d6414910cb94b411033651504109ed9510043946350510a798e52d071c5350521d954a51102766114142b6582214c32e52504109758e500426e62152309758c540871c6355310ce551500c65d63940209e580530871e5454c209758c514834c538c921d694d500871f53505219b58853c431d53504408f990514c23d64d4f21c714f515065e6314c10c7553430c7976150730a7990514c31e5494c10b3588514c32c52509418fd91538435a6094e108fd9541087b14188110ad984325067b6055121dc885500879b54d41308f593530825f63549109b988505071d5310e4097580535063f6155232a718d505065c63549108f99251c832d52d0040d554e510832d52d04109758c548823e6414c109d584548c23f6454331cb549401023e6494410c795130c43b1414c110e6d05304436551c80209e983540871c544c9309e580538869e6390840c7993534865d6594c219bd89534423e6415020c7593534863d658cb4197d9541cc29c63506409d195414439b644c110b3d89514c2776548421b5584404c2af6254141c714d425063d65d0421c754d41082b96010c40c7951300825c63547208f592510cb5a504c010d654d50086d960949308f587544823d6414b108f595410831c54cc930ab58b53d06796015021c7d4c435071f6355231c794f4290a9d6490530a7992314c31c5394141a758e42d065d63951219758e52d
  | 3 => 0x10c754f410825d6054c10a7587544c23d6590840ad592414431e6515130b398b54cc399414c210c7152434c31f54d4130d6d0d500c65e6314142a798e50d06da608c530a7580535065e6314141e5505310c75a534c2109798f54c869e640c7308f586540833651504208f593520425e6508730c7551300823e64d4f219d984540cad960905308f590514c31d5390c409798e508865f63551109758f540863d61d51309d986544cb595344010a758c505067a6014532a7590514c2766115230d3549310c7715188020b6580414c3394154031d594d5110395414c1109758e5010bb141481109758c540834d53548109718d544865f654c0109798f540c25c6354740c7952530825f63552219798e500865d6394242a799051cc25f6354b10a7997414c31f6550530b6181424c31d54cc310a798e42d073765505109b988530869e6408530b398840cc29e6390942d610d500c66c6254d10b3988314c31d63d51209e580540c65e63d4a1097994214c29d648c730a758e50d06cc62545309b98a544c73554c4010d354e521023d64947209ed95200825d6314b10cb552520423f6454321cd945418834d53c8421b6582514c27561d4c208f593534871d54cc0108f99352c423e64d4c20cd98654c425f63551319719541cc3356494420cd545419023f65d0420a798e52506ae62143418fd85540425d63940419798c520429e64105309b588548423d649473297d95320ca5d6314810c794d410875653944208f990540865e63152108f592518833a54540219718d54c423d6115120c794d41883355150040cd991511031e53504409dd95411065f654c4319b58b54cc23d65d0410b398851cc23e65d0530e550530c426c62551109798e509071c54cc1209b588505071e53d06408f584544c36552c4010cd547401031c548c5308f590530431e5350420a7584544c3365454420d954951103356454420d354b300431c6550530cb951520c69e64087308f597410c65f65487309d5845308391414c11097997434c23e6515130ec181414427a60d50319b988540829e6515130cb54a4210339419402197d8d51d025d6510c31da54a500c65d6314910f4185304439541cc310a759252cc25d63d5010d654e100431c6355031a7990314c2766115020f4905304431e53506108f990540c63d641481097d8d544865e6590930d6cc5500c63e65505209d584540cb1d53504219758f528431c540c53097997324c6da60109309758f548431d63151309d5845050b365150440d594e511025e6590130cd545418c3d1214c1109e583540c63f65504418f99251082cd62147308f990538863e6414f10d694d300c25d6394341d394e520423e64d4c10cd945419025d6094e428f592510432d5250440d694e500865d6094c21d554d511029d6394941c755130c42ce
  | 4 => 0x4c010601c0000c008000501f0186c00c3b0080d0440d0000007c13010200006e01c010bc0b00c010100400002008011003d00000010d2024a50cc010001300020004e06540300400150006740000422000051c8c800c0103c03000000000d0000500c040a0000cc0300c010082f004025d848008270005f3a8370080301403004020040400032000150001b2100d054010b800008106cc000b40201c1d00814039a1004200000601400020120e002058010080101c06028001b82400005004010080400400004057e81200805024027b0000000801c2300881070680004c09401008080007b01c06860010045b000050000001000b7c261982b36800038250140d06472084000049b000b50001440c0201400364030740c13800012872940b0440e0000604809000940d02100c000041105004074350bc0003db9008001d61c02c020007d00000038500140001400008030080215001068010e0f0324000b15804c01000580180b0000b03c00010290140001422004220182c000040641e00c010007f0300a084c80381a078200104a0000c138020080019413028000258d05c07028000100e0040e0080300401004000108d028000181a064f19798e5010a5e63d5032a7d91524c398644c2108f19741483d13084110c7d4f41486b76550710a7590214c31f63553108fd9541042b56194d41c7152514c23f6454d20b358b54cc26e62d5031cb548421023e64946328f99054043655148020c714f414871d5454c10c7d9541cc3346550510ce952500871e5454c218f596540827965840109b988548425e63d5210aed81525071e544c
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x64005010020080026180300a0b80001001b04b4385265ce02b22e920a608860c54588314c307322a519063645cc6050510c30a6302a4a0e9163506204430631aa4a088186194644c110a2ce7212a2204d07650530442c93b28298221455c4540c530b42e430282886146518d4144270b88c0a12414c5c04354440c18a8b10a29841e75995414c20e3b2a6a0c41465c05314141aa2e221aa018cb076505304424cb80c6a0881071d56488530b22e910a60884b170185325070629ac428283c45053154031c1cc6a9484204d171181424c20f3b6a898241511c5521493092ae33246418c997098e421024c3b28298421645c4644c110b20eca0a608849076505304420ebb0a818a61c85052154021e0aa4a0a6218c98765053044294382a429283a2589401013086ae2322a0195917418530442a2b8886a9063071d9544c310d26eca0a608869063181414422cb80c6a8885645c06350510838eca9a83084e1701853248782a9a8290843c25513048020a34e9192a018c947650530c43a0a8a6090041851506154930b82e430a608869064185304428ab88a828a614a5c0435484083ceda9a8290c947650530443483b28298221a45854010130
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x40036308000000060911819d23254031911809ce4254440890865d2214c110a098014d6214141892869d9414c110a0581991528c8318908758d4188110a0581151620c530a098098d5290840a098018d5250440c10655c06350510c80635c86050510c80645c8614c110a05811516214530c10655c4644c110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/35+packedAt s3K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/350+packedAt s3K5 (22140+(h % 350)*10) 10) % 820)
  | 4 => 2*((h/354+packedAt s3K4 (33972+(h % 354)*10) 10) % 894)
  | 3 => 2*((h/29+packedAt s3K3 (3332+(h % 29)*7) 7) % 68)
  | 2 => 2*((h/19+packedAt s3K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87f8ffff07f1f1f878e3e3ffe3f070fe0cf70f
  | 1 => 0xf87f078ff8fffe3f80fc7c707c7fff0e3349f3
  | 2 => 0x7ff80fff01ffc7ff007f807f807ff1c38e3c
  | 4 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 5 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x90081101100222000820809120911024041305
  | 1 => 0x2104012204080410044242204242408114052
  | 2 => 0x652222244225400ab100490449024ac0c28c28
  | 4 => 0x3106b54894a06494daa90009724b02656c0f80
  | 5 => 0x4644c600e6c9892764d2724e000c0c89bbe000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaecece8e8fefeeaeaecece8e8fefeeaeaecece8e8fefeeaeaecece8e8fefeeaeaecece8e8fefeeaeaecece8e8fefeeaeaecece8e8fefeeaeaecece8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_39527
namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x1177410003010020850005c00c068000004d1c001dfd10fc40fe21fe30fe42ff32fc32fd30ff42fc20ff30fe43fd20ff20fc43fd21fe41bd41fe32ff43fc10ff41bf41fe10fe40fc41ff10fc30ff21fd31fc21ff31fd43fe20fd41fe31fd42fc42fd32ff40fd40fc31
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x287ef4290afaa4085b94a43fca8043df32cc6faa018df54610df2a0617d519037e8218efd0521be2a4657d53082fca7886f90941fb288817c52502fca5a0ef90942bf2a063de434c37a8298ef55332bea88417f5448778a8985f94a31bea9c857e52843f460886f50430bf29465ef4250afaa7197e90040fd90241df314c2faa6085754e42de29e83be42d07dc40905f15332dfa0861dd530877a82985fd5131bf296637c535077aa5a0df94030dfa00817d53d0bba86987790f30ee996637d520c37a64a0df94642bfaa4617c51482fea8105f54f10beaa0635d53082fea9986fd0721b729061be540c7dc6490cf55031dea0e617f54042faa1a1df14931dea0e43bf32d07f241087bd0932aea9821bd40102fca7085f15310fb90a437f524c2fca21077cc730dfa0e617f540c6fca890dfd4941dfa1c857e53482fca9195f54b10fc88021ed21c82fea5085f14532dfa0e813e548caf8a6106f4cb41bf2a2633f544c3f2a018fec4210eea98217f524437ea8905f94f20bb288617f53c42fca1215f94831bfaa2617d52106fca8986f50b40bfa90217e54cc2fca1086f50940beaa4617e518c6fca5886f50710f721641bd43503da40106fd0520bf28c65bd41d03ee20087754e42f729061f940102fca1186fd4d41bea9081fa20082faa510ef50540df2a4637d508c6faa3986f50520be29221bf41503dc6590fe4c110deaa4637e50102f8a8885f15032bea84657d50ccb7a8220efd0710be29a21f6510c3de43905f54b41bf290857d538c7bc60985f94021bea8c41bc43d0bbe87995f55120f721085f531c43ea43885f15330f7290817e53042faa7186f94941dfa1c877e5110afca790df15331be294217e52086fea9997e8c030beaa665be535077e86a05fd4143ef99065ed32c82f4a010efd0f40f6a9081fb20882fca190df94c32dfaa261de530437aa9195f55020deaa4437f504cbf661185f54042fb98c637e53d0b78a0a0f7cc230bf298617c53c82faa518cf55020af298217651103dc64906fd0842dfa0c417e51887ba6419774c931bfaa0437c54086faa221774c030fd104217d518c3d885195b54831fba0c837f514cafaa9106fd4141bfaa4417e5190ef8a790dfd4142bf28c61dd310c7d884995f95020df21e857c53482f8a090fbc86219f2a0417e5010efaa3195b54810faa88417e5210ff240885f54221be2a2657e53d06faa920734c832dfa16837d52d0efca8207794c20f6a90637f5350bec82886f90a40bf28861fb10442fea7107b54810df29e83bf53d06fca118df54e20bea9c837d528837aa0a0f74c730bea96637d5290efca7a05f54241be29c417c548c77a83105fd5331dfa1283bd418c7ec628877cc631fc980617e50906faa898df54a41bea90637d53c82fca2085f15010bfaa6436d520c2dca4205f54643
  | 1 => 0x5414427ca918fed0240bea94817e501077a8210df94031de21e837c524c37ea1a0ed50510de21683bd4310b7a83085f55330bf2a6437e508cb7ca810df94342bf28e877d50cc6fea498fbc8020eea1887dd53082f8a818df55210bea8e65bf418877a84215f14142dfa18877e54c82faa5185f94740bf29c437f504c6fea918dfd4543beaa021be43506faa1a14f55010bea8e877e531077884a0df95132bea8e41ee32c82f8a8905f95210bf284417e5390f7c86a14f15120df296837e50d06f2a010fb94a43be2a461be4350f7a82205f55030bf2a665bd41887f680a05f94221deaa0217c52042fea6905f149419f2a6657e52906fea7905f54b30beaa043bf411027aa9195e94031df21e837e52cc2fca6215f54e21dfa18857c54c827aa810ef55310bea88617e53902faa3a17794c40bfa9841bc52d07da6490df94820bf290657e53906fea910fe94031bf284877c5150f7ca9196fd0731bea80435d53102daa521ef95310dea1283f710842fea4a05fd5210bea8683bc50d06faa1216f54941fb20883ed21482fea690df94830baa88817f50487ec83887dcc531be29821bd435077e64a0df94c20dea1683bd43d06fca4205f95221beaa643f7218877ca8105f54d21ef298437d53843de64995f54443bea8487f631c42faa3216fd4541bf28021ee52042faa8194f95221bf29c857c53502fca3997d88421f699643ee424837e86a0df14542bea9883f510042faa190db94810eea98817f54c42fca02177d0e43bea9e817d53443f461087bc8520baa8841bd540827aa9996f54f41bea98437e5290afea610d794c20dea0a21bd41903ea4210efd0940bea8087bf42d037e828877d0d32fa90a217c54486fea2a05fd4520af29c857e54cc6fca1205f94443dea1e81bf418c37aa6a0df94b439eaa0617e548c37e8298fd4c510efa1a877e510876a83886fd0f41bf298877e54106fea6a05f95043bfa9821ed42c82fca5205fd4d10deaa063ed32482f8a9086f55021aea98437c54c877887207d88710de192837651082fea710df55130dea0a437f544837a83186f15120de29a83bc32d06faa921f78c531dea0e637e52d02fca8185f94c31bf28665fa10042faa3a04fd5120be2a0617d5490b7a8218df54f21bea96813c544c2f8a8985f551219f2a0637c53887be65195f54843dfa92837f54c83bca7215fd51329f2a061ee320caf8a7887b885219f2a0837d544cb7e83204f55241bfa8a617e500cafaa920ef90840f6a1085dd314c2fca8905f54432bfa8a85bf52d06fca3a1778c932eea1e61dc43ccafca198df14530de214817e54442faa998dfd4e10bea8881bd4390bea8220df54d20bea9e83bf414c3f261085f95220bfaa061f541c437e82086f55030dea0821be43903b886997bcca32bea98817c504cafea4a1fe48020be29
  | 2 => 0x2150160d00a008f0000222f1a8160004480403822020140b80a05024003ec640ee25828050340001003920153a80080c058024a02a0f010150060100c0503e064b4008060201a1aa4800000318623381a0e00ef001a0181275824130129902e0019600000058e64d85c0b0040017202806098cac88000b00c46a862810e0400020806068160180c0abb40000a058000008c008462a00603002081dc008001780a030020000401068008080c8100600001800a0802008520202e001f930004238000018800802000002189c0000000004d380800000060002c5940400c01800038122701c1002a148000380c0601e1280a0080604010000040121a002fe032009e018ab4820f802028040687202814000000600203b8c088083d8081c0000d8280480003800019140000cd08000102a0835402002020422081e080040c30806000028037e51907ec20887d94420be2a4437e5290efca420efd0441ef992637f53506fca810df55310bf29a213e54086f2a018df15220ef980617e510c7bc8621df94c40bea9c813d54c43be649877cc431be296217e51883ec6218fb48421be282837e53882f8a690fb54a43fd98261f5310c77ca9995f14143beaa64175510c2faa5085f94343bf29021f551102f8a098fb54830bf2a6217e51106f8a2a0774c930fd280437c53086fea0a0ef8c941dfa0481ed42482f8a8105fd5032dea0841df32cc2fca2197d885109f2a6217e51102faa020df15131dfa08417c538437886206f95221dfa1485bc525077c65a0d794c40bf28e41ef428cb7c80a05f95010b7290637e528c3de41105f54032ee99661ef21086fca8194f95010dba8a837e51902fca610ef10d42dfa0843fa20442faa6216f10840df218816d521037ca0a0fdd0541df2a0217d548877c82a0df94d21bfaa465bf418c6fea790df55231bf29221bf41906fea5884f55221f729063be50d06fca0105fd5110dea8683ed320cafaa9197d54430be29a85bd4310f7a83906fd0720bf2a4633d548c6bca610df54910bf28e617e5410b7e83086f10d41beaa221f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3524c7b141c41109e583530863d6195232c754f40103366454440cd551510832e54948318f592534869e6314341d594e511023d6414e20ce551500871e5350e42cd945411023e6494420ab988505063e64150319d98753083e121481109d195314426e6214c1097d8d544434c534cb218f195414826e6214f108f59052042b76550710ec505304434e544c832cb949410426e62d50319bd89544425d63141429798c530427561152208f597410436952940318f590534423d6414c20cb549410c63d64d4f108f592510c69d6314141c754d410432d5250410ad58753d06ac6254141d994a510c3b1418811097d95310c677654c431ab98a439023d64d4e21cb549410c23e641481097195434c23e64946208f584544c26d6294f40ec181414426d6214c109b588538431d53504219d587540c2ad6290d418fd91524427865481109718d544426e62d50308fd954310aae62d4f41ad592414425d6315020cd545418c35653544408fd91528425d6315021a798e421023d65504208f586540c3395494031cb94b410436551c8020cb189548cb344354440c754f410423f61550309b58b530433551d0040cb54b410c23c64543319b98b54cc2b7614c941cb54b410c72c43548408f993530871d5454c208f993520423d64944328f990540432d52d04109d195414433941540318f990530873651504309798f540827561d5020cd95141c429d6314341cb552520c6b5648c7108f59052442cf654c8329d98453882756115020cd947410832e5454830c754f410876552544409798c548427960d50218f595410c23e6510d429b588505063d6595020cd592510825d6594c109798c54083365494420cb548421027a6014e218f5963250755514c030f44c530442ad6290f418f99252cc23d6414530cd545419023d6414131c714d435063e6550520ad58452d065f654c8328f992510c73664544308f593534874d524c4318f587544c2ae64cca329ed95100432e5250430d654e500865e63d5021cb551520c32e52504408f59052c425e63149108f990534423e6494c329e580538867a6014532b358e42c823c6454e20dac85500873651d04309798f54c823e64150218f99252cc66e62d5331d354f200831d5310c40b358a43cc26e62145309b58a53d066d6214530cd952510c32d54480208f59253c823e6414a10cb94b410c31c54cc9309e580540863e65151308f597410c371518c030cd591510c23e64944309b189544425d6314910cb952520c2766115032d64c5500c63f64543318f195414c23e6414520d354b300c2b56488510a758e525063e6515120ce95250087b360505109b98a544c66e62141419758c514831d53108409d984540423d61950208f596421038d320cb419d984548c34c534c921a798e425072e52d0440c7552530826e6214810
  | 1 => 0x823d6414f10d34c9500cb2d52504409758e52d06746154d20c754d401032d5214b418f590504cb4c524c9309b98b530427a6015021c754e431023d6494421d354e521036551480209d98454082b4614c9418f990504c67661d5020c7553300c2b5610c94197d954310f375150540d6cc5500c63e649513097997434cb5953440109b98853442776154d20cb54b41103695244010cdd9541c423f64543219d984504ca5e63150308fd95410826d62d53308f992518ca3c6454e108f99050486af6254141d594d510831e5494c208f59053842ae6294f41c794f410823d6595030cd545410c23f6454d20a7d8d505065d6314a108f592518833a5494031c754c43d063d6414c218f99251087366195310d3149324c63f6550c438fd95411067b65480209d5845050b4d5394810ab59232c826d62d5331dc485500871e53504108f59353c867a60d4c219d587530823e65d09409798e52d071d5314d419758c504863e6414c10cd545401034d3254432d354d52042b564887108fd95410c32c548c9208fd91500cb1d53504409e583540c76652544408f59251cc23e64951209b988530863f6454e10cd90d511029d64cc9309b588548427965840108f59632d078d320c941a718d505063e6494832b398f424cb5553440109b988540c23e64d4c10cd992510c3394154021b358e424829e6314141d954910042b56194d419dd95411073551d04308f590514cb5a53540219798f520423d6494b31cb553428cb2d5454831cb15242483713154031cd951510c25d6594c208f99251c823e6414e218f99353c8395414c4319798c548823e6494f218f99253c823e64d4c20c794f410423e6494d20d954a510c3695254031ced05500c63d6590c408f191528c23d65cc9419d984548825d6394b408f587544832d54948108f59741086796015031c754f411026d6214f109798c528431d54d0f32cb54b40103346550510cd592510c34e53548408f59252cc26d62150309e980540c65e63d5321cb548525078c43d09328f993538871e5454c21cb58854482756114132ced05500872d5454810c7551300c31d5454c10d354d200826d6214131cb14942507722154021d994a511032c544c920cd591510825e63d5010ab588505065e631501097d8d524423e64d4d21cd551510c25e6314c20dc54520083395454031b5185324c6e4614c921cd551100429e6390a409758f540826c65509209dd95210863e6414b10c7952530871d5454c218f197414c31e5350421cd547411025c63549109798c52c4371514c030ab98a535071d63151308f597410c63f65d04309d984540c33651504208fd91534425e63148108fd95410872d5210b419e580540caad6294f418f592534826e6294f418f99632d063d64d4c20ab98a431034d5354840b398b434cb5551cc0308f99
  | 2 => 0x6115120b358a4310eae6290d42cd545410833551506209b58b540c31c63553328f99251ccb1e53d04218f992510ca7a60d50219d984530427b654c0308f996325074e53948408f990514cb4c534c920c794f4290b5653944209e980530865e6394b40d954a511029e63d4b418f592518ca6d6215031c754e421023e6414f10d314d32c823d6494732ad58453d066e6215010ce506500863d64d4f20ab993324cb3651506208f596540433654504418f19153482ae6290f419e580514ca9d6390b41cd945419029d63d4b41ec505204425d63d5010a7992324ca3d64d4b109b988504c78f4310932d694e500873554c4010ab98850d063c6454321cd547410823d64141218f99353c874d53c8421b358e320cbb341440109798c50507376550510a798e525066e62150208fd85540823d6494720ad984325063e64946309b58a544c67a60d50319b988530823d6494630ab98a43d0a6f6548020cd951510823d6494f21a758e425063e6414910ced06500873642544408f590538863e6414530ab58a535066f6254d10c794d411026e6294f409b588548c32e5454831d394e520426c6254d10a758e52d074d524c030c755253086756114c209b98b54043723154031d9549510c3555394440cb952520423e65d0530cd992510827661d50309758f54c874e53548108f992534872e52d04319758c52c432e5250431a798e52d076a52940318fd97410825d63148109758c548826d62150108fd91538825e6314121ad58752d073954940218f593524c6cd6290d309798f540cb3551d07409bd95210866e62141439d984530823f6454a309758f54c825d63141418f585540427a6014c10ce951500c63e65d05209ed95401031e53d0440cb549401023d6195332d654d500863f6550431c7152434c25d6315010d3151320ca3c6454032ce951500872e4354840cd945410425e6314c218f191524427661141428f99743502766114143c754d410834f4354a43cbd0e5290e9d64ccb309798e544874d52cc4319b58b540c66f654c8329d586544ca7561150308fd95401023d6595021d354d210863f6155010c795153043715188020add85525065e63145208f99053882756115230cb951520426e62d50329798c540866e62152108f592530cab76154d418fd8554cca3e64d4f10ab58850d063e64150309b58b540431e53d0e429d986544ca3d64d4c21cb553200827a60148108f191528426e62152309d195214425f654c030c7552530429e6390942ad59231442cd63908428f590530423e64141328f59251083555354420ad583515065d63951218fd954210a3f6155232c754f410823d64d4810d654e100436952840108f990540831e5350420d9949510c25d63d5021cd945418c23d6414a10cd552510823c6454d108f99352c425d63d4810c7951530
  | 3 => 0xf8000001d07000020000400001c020380000400034f200800010000c0177fc1800000008e000404008020040189806000080c4020200a108073e80004c08014d80004a011390180002c3e300050440830004008070149c014a90080601804008270040a00028000200001e0080a00c00028d50140113082000020000104000000010141849c010b8d3350030440400c0a0002a00c0e01401001160181f004040540700012000180003400094270020304d000360205302805058000940d0241300404028690600000406420000141200000010180343000c000dc9200000014080007b0000200c020e0030000200055000060343e0340d03d3d0040405c0600002068310011c0100a5a001098620000103406072810000612c04010120242f0a40400023018030100102c0000025004000080d0840506000008011441009005014010343800000000170106705c01048000100004c4e638014540704c010000c018100140124c090196800000002ab0f80f0002100001004430001200003d354f4290aad62d4f418f990538426e6215031d554d511023e6414c20ce506500c65e63141428f593530426d6214d109b195324863c65d05208f592510423d64944309dd95100423d64948329b596520425d6594c21cb54a421023e65cc941d554f100423e6494410ced06500c66c654c920cb552520c25d6315210cd552510c26e65d0932d954b10042796014c219d984520434f654c832ec506304436921540219b988538423f6550410c7151324c2f06050510ad586525063d65d0420d554e510826f65508429e980540ca756114143cd991510831e54cca329d584540cb1e5494c10ab98a435071d5314f418f99251cc29e6390b418f99732d063d65950318f995414c2ae6290d439e195304423d6414520da949500c6ad648c9209b5885050e756114e20cd109511023d65ccb41e9505210863d
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4000000000802310a000020500000100000000380000030731aa5210810d5c46454032c1aa731486207055350521086d0b90c0a0a212c1d9414c110a62eba0a200859173181414429339486a8881075d854cc93085aec2a4649054571151320cb062a2c721241831913254032e428290aa010cb0765052044390a968288021385c0614c921d0a64b0864a0cd170185324c788a9e8288021439d3654c832e0aa4a0a6218cb17018532506a4b80a899065459ce42544409c2e43028288711414c5500c7062a2c521a61345cc6050510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x40905819d3654c832a05811913254032
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s4K6 (672+(h % 28)*6) 6) % 42)
  | 5 => 2*((h/259+packedAt s4K5 (19845+(h % 259)*10) 10) % 735)
  | 4 => 2*((h/307+packedAt s4K4 (27056+(h % 307)*10) 10) % 712)
  | 3 => 2*((h/38+packedAt s4K3 (1470+(h % 38)*5) 5) % 30)
  | 2 => 2*((h/7+packedAt s4K2 (120+(h % 7)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xcf1fe3fff0fe3f8fc38c7c7ff1f87e1f04f4cf
  | 1 => 0xfe1fc38ff1fc7f1fc0f8f8e1e3f8fe31b4b33
  | 2 => 0xf001ffc0ffe007fe3ff00ff01fc00ffce38c3c
  | 3 => 0xfffe0000fffff8003ffff0001ffff000fc0fc0
  | 5 => 0xffffffff000000003fffffffe0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x41002000100040100000101200480200001045
  | 1 => 0x2208410122080a020804848442120482094112
  | 2 => 0x80d48892444495005590092094812958628c28
  | 3 => 0x4441aa488940124a6a9200119256048b40e80
  | 5 => 0x289913300ed926493b4e4e49c0064192dfe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8feeafeeaeee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_39527
namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x440000020000021470c00009c0047044057202fe30ff31fd10fd32fc31bf40fd41fd30ff40fc40ff42fc32ff32fd31fc21fd20fc20fe21ff30ff20fc43fe32fe42fe40fd21fc10fd42ff21fe10ff10fe43fc30fd43ff43fc41fe41ff41fe31fc42fd40fe20bd40
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x61dd530837c8420db94831ef98461de5390af2a018fbd0a429eaa0437e5190fde85197bcca32be2a465df32cc2faa5a1f710d32bea9885f9300c2f8a7085f94c10bf29687bd32503de41105f94e42be29a41bc43d03ba64985d94420b7290617e508c3daa41877d0d43df996817d54886fea5885f94820bea9021f7314c77e81185f94720fc984217e528c3de4310df54a31dfa1681f5210877c64a04f95210be29221bc41502fca3195f94220dfa12833e54103de42905f14f20be282637d511037c86a1df54d20f699243bf401037aa7a06f55030dfaa263fb308c2fea098dfd5130aea9c85bc42502fea0995f54841be29a85bd53502f8a810778c932bf29e437d518c2fca0086fcc540bea88617e508cafca110df94432bfa8a817c54c83ee21087e90040bf2a4437e5390f7aa9106f55210bf2a0653e54086faa690df54743bea88657c50506faa7105f95041eea1a637d538cafea2906f90540ef98a61ef20083baa610cf55020bd280637e539077aa4a05f54e31bf290853d548c2faa7185f94a40bf298637d53082faa720f74cb31dfa1a817e540437aa9185f94a32dea1e837d540cb788720df14d21dfa8e81f6310c6f8a2997b8c921fca80837f54886f8a2a15f54843bf2a241be43502baa610fb90921f790843be54082fca3187790c43dfa18877e540c6fca4205f94832dfa00217e5190678a890df543419f2a665be54ccaf8a998ef8c540be2a2637d52d07ea20085fd4931bf29061df434cb788420df15032bfa92217d52d02f8a8885f94c21faa08837e520c67ea890f754c41bfaa063be53502fca3a1df15132bea84857d540c37c8520fd4c431bf29485bf415037e80886fd0220de29e81ed32c82faa9087e90110de90e813d54042fca221fb8cb20bf29621be540877e87217b548319eaa665bc51d037862a05f54221dea1e81bd31502faa8905d54430bf29a217d53106faa5885fd5121be2a6437d508c6fea0a15f94332fb288617d53c837c8620fbd0942bfa8287bd32d03be60186f50330deaa0217e53c837e81906fc8540bea94817f540cafca821dfd4d41dfa1885ee520c2fca220efd4d40bfa9e21f521443ba62985f94c43ef21e637f54cc3788520ef90140df292817e54083daa420df94242df2a4617f54483ba6498efd0030bea94835e53083be6318cf95230bf284877e53882faa2105f54442bfa98217e510c6f8a5887e94021de29281ed320cafca710ef95031bf294837d540c6faa918efd4140bfa9e41f651082baa6085fd5230fb18e217e5010efea2987e48110dca02217c548c2f8a7105f14520dfa00417c53c437865a06f50d41df2a421bf4110778a5a06f15121df21c83be42d02fca318efd0210de2a263fb10442fca690dfd5210fd204217d500c7dc64195f55220be292637a50086fea50877cc431
  | 1 => 0xe510877a84216f90f40f690a417e544c6fca421df54640bf288217e500cafca9997e8c030fb108436e52042fca198efcc940bfaa0217e51d02faa3905f14c20beaa4617c54882f8a910df14e21bf294877e5190afaa021df14d10bea84837d540837a81185fd4940bea9461bf42502f8a918cf55240bf294637d544c6fea090dfd4532ee21e65bf4390f7ca9107b90b21f699643be31d037887a14f95031efa1c877e51d0b7863a07b8cb21bea8c417e52443f2a018db54831bfa92877c54486faa521f78c130ee98e61bd54ccabaa6106f90541ef298217f53482fea8106f90d42bf28885df324c37e85215fd5232beaa0217e52d06fca5987b94831dea0081f910043be64195fd4e20fd184217e53103bca6105f94f40dfa0e817c53502faa610ef4c740bf284637c5050efaa3a07d8c510f690843de53086fca310df54643f690041bf4210af8a2a1df141429f2a0217e54c437e43a05f54042ef994657e5310bee8320df55332bf28c817e5410afca9184f55232dfa1683fa20442fca1a0fb94810bf284837950107f280205f54732ef996637d538437a85a0dfd5321bf280437e53d06fca5a06f50010bea8c657e500c2fea810df94f10dfa04817f548837e81985f54d10fa98a217e52106faa3a15f94c32bea9e81f721486f8a8086f95030deaa4657d52cc2fca9984f55210bfaa0615d53106f8a2a05f95021bea94215e53087da64905f943219eaa0617e52042faa9195b54841b6a90617c524c3da84216f50110bfa9a43bd40882faa9905fd4141bf2a2617e50902faa198ef48540df28a817e53082fca598fe84010fd90441fb40903be87997e94031f719241bc43106faa998dfd4c20bf280837f52506fea4987d54420dea1a81fa50106fca0217e50110bf288617d53042f8a2986f95010be298437d520c6f8a6087750c43bea8c856d52042faa4205f94420ef298837e531067ca8105f54041fb98c63be43d0afaa990ef50c43fd10421bd51503f440106f50b40df2a4657e50842fca6906f88740bfa98437e54442fea2a14f55031dfa0241cd320cafaa7a0f7cc931bfaa2657d54903de84997d90441bfa8a87bd400c2fca9195f15130dea06417c5350776a0a05b54a43fb88021bf40c42eca2185f94730eea1e63ee52107ea43885f95220f729487bd41d02fea918df54a21df28e81f621442faa8985f94a10be29283bc32502faa1995f95030ee98061f9304437a87215fd4d109eaa4417d52443de64995f15330bea96637e500837aa810ef50020beaa243be42502faa3086fd4540beaa265bd40842fea898df55110bea80437d5090f7a80985f14132bea8643bf53d02faa6206f10d40dea12837c54c42fea988774c832dea1885ed520437ca7a06f54740beaa6617d5490fda43906f08740beaa621f940843daa521ef94b40bea9
  | 2 => 0x142183c0180200810184300383e46810130160800e0002201012010040e0280486605988029c4b0800000040500d1780001864128000083c04b5c000001407a000061080250000110000600c022b8080040d80e1400a3f8020001c3b80002800008080100c008300304e001d80b0000780e000780280000048050308d81a0001c03838020060a8780d0286000a000020380c0101a0481c0002a07008008400003402b400681a0d02a66000010260f896020000b06811812030002f8220005e0c1941b0160402e1680c0280000880a08b28503201006010240180800034000020080ce70060d0542600200824000100201409006088320000201800020020901c0480600804480881982208016020000000603060000300b8000500004000078000f0080d04e028583b00011036000940203a6300c0000a0003e23806bc0360c0000800000834000484c82e0000403000148020d019bc41d02f8a4a1fd84110ee996617f54cc77a80907dc8621b7294877e52086bca620df15210bea9e21f531c43ee82a0df54e21dea1281fb20482f8a090fe48020bd280837e54486faa790df14940dfaa243be21502faa7a17b10932fda0281bf404c37ea5a05f94440bfa9c43bd415027ca9195f55021bea9c817e53d0b7e8320df940409f2a441ee4210b7886a15f14a10be2a2413f544c6fca990fecc130bea8887bd40c43d885195f54232df19681bf43d06fea6a06f55020bf2a6637f53c86f8a4087790d31dfa1a83dd53042fea7084f95030ef98e617551082fca8205f94e40bf29861bf52502fea6a15f94732bf29c21dd5390afca9906f54b40ef18a637f52043eaa2187e54021bf2a421bd411077aa818fbc8720fc904217f54c837c84a16f14540bf286857c54086faa7215f15031bea8e61bc215037885a06e50210fd88421bf31d02bca6085fd5332bea80657e50d0f78a6a06f90740beaa485fa30442fca918df95132bea86857c54cca78a898df55241ee988637950086fca018df54343bea94417e51883da8490fb88120fb10e217f54442f8a8185b94841dfa1e81ee21486bca7217b50b21be29e437
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xa43d033a54502109b98a544c23d6414a108f992500c29d63085409d587540c23e6414e21d394d520427b654c030dc48550086786054d219b189544423d65ccb40ab98a43d02ae62147409e980540cb395494031a798f52d031e5494c209bd95320cb71315403197d8d544425d63d53218f592534827561d5020cd545400c33b6550210cb551210873954540318f58054486ae6290e419b988540c31e5454c10cb94b400c36a5294041cd551510c23e64940318f19151c825d6594c21d314d32c86766114e20c754f40043715188020cb151324869d6390b40cb15232486f061501109d987540832d52108418f59353c826d62d5031d394e520423d60952328f99052c429c6354540ab58831d025d6314a10b358e4210ab960d47409e583540873651d00209d984540826f65484219b58a53d02b960087408f992534823d6414e10ab98a4350eae6210740ae980415023e6494b30ce991500866e6214131ae58031503b231501109798f540cb3651d00309b19532482796015031ce591500871d53500208f994315025e6314a108f590514c27965840109d984530827561141328f597400832e54948308f580544c6796014e218f582540875551cc030d3d0d5290e3c6454e21d954b100426d62d53318fd91538871d5494c21b3d95320ca5e6394b41ba18132483365494430ae980315023d6494021ab98a4350b1d5310f409ed8153486cd6390921d3d95320cb1d54d0f32ce55150086ad62d4f40c794f40082ae620c7409d584540831e54cca328f590514829e6394b40c795253086b961d41408fd9540102ae6290f42d3149324c63d650c5409e580548c63e65cc9408f593530834d53548108f99431d032d5454810ce592500c63e64150209b588514c23d64d4d209b58b53042ad648c9219b195424863e65ccb40d354f20083695254031cb552520434c544c83297195434c6b96014b40da549100425d6314121d554d100434d53948108f592500429e63949408fd9153c432d5210b40ea501200833a6494021d3549300c25e6314b108fd9541106b96014f408fd95400c25e6314910d9549510c23e64d4c21ce99150106ce62d0d328f592508873a5454031da949501063c6454b10ce195404423d64d4c109758c52c425e63d5021d95452008274654c510cb549400436952940319718d544433954940219b18953442ae64cca329dd95310c63e6515121d694e500872d5250441cd552510823f65500209b98b530434c524c9308f990530834c534cb209bd95200825d6315010aed8152502b8604c9408f59250c872e52500108f59253487b140841109b98b540423f6454a318f590530873a54940319b588540c66e6214c109e5805150f6a52540318fd954210aad6294f408fd81540c66e6294f419e98054042b960949408fd8154042ad6294d40
  | 1 => 0x423e6415021cd552510c26e62152318f992500cb8d320cb40cd945400c26d6214f108f997425063d64148108f596540c65e6314c10dc545300c3565394420d6cc5500c6776548421ab988315023e64d4e208fd9531d027661d4c209bd954210a3d65d00309b988538431d63151318f590524425d6314540d394d521065e63d5321e3d0c424caad6290d40ce95140102ad621454097d95300c27960145329b98b54cc27661141328f582540c6cd6290c43d354b310c66d6214131a798c41d02af62545408f195315031e53500208f990504ca3e6414f10ce98254843692154021cb553210871e5454c21c7551530863d64d4f21ae58231502756115032cd547400832e54948318fd81540871d5314d409e98052042ad62147409ed95401035553544208f992508863f6055332d694e501072c52509409758c548869e63087408f992544863e6414e10d3549310c71c544c9319758c540823f654c540dc8c5500c63e6494332cb90d521066e65d093297997434cacd6290f31ab98a43106ba6088540ec485404423f6454d21ce592500863d64d4e10d9549100433843540418f592500c77221540219b98b540ca3d6494832ab189515023f64547309b98854c432d52d0441a7d8d515026d62d5010cd95251082cd6290d318f59352842ae64cc932d954a510c23d60d51318f59250cc6ba60905408f590504869d64ccb319d984520425e63951209b988530829e6390841da54a501074d32540328f592508c63d65950108f992500825d6594c109758e52d03b36150110ce552100435953840109798c52043b06150110cb588544863d6414b10d9949510c23d6494030f44c5304425e63145409b988540867b65440108f590504c67865481109e58353086b9648c2109b195324863e6414e20d314d324863f65485409798c51483595394021c7952530423c6454a31a758c415026d62150109d984530432d5454830cb549400c23d65950308fd91510caad648cb218f596431067a6014c218f581540423c6454d21c714d435027a6014532a7593324c73a50500109e582544ca6e62d53318f990540c6cd6390b21c794f400425f654c832d34c9510ca6d62145409d584530823d658cb408f592530ca3e6414131ecd01100423f64547208f59253c86ad62105409e980540863e6494c32cd551510835a5354041c794f4390a5e6314c209b58a544c29d6394b40ae98021d025e6394b40c718d54cca6f62551109e983540866d6214d108f59252cc31c54cc931d554e510834d53480209e5805150a5d63d4810ce90d501063c6454f108f191510ca7661150308fd954310a6d6214c10d354b300c35953540218fd91534434d5394841dac85500867a60145429718d524427a60951328f593524c23e64d4f208fd95400423e64148109758c5150b4d5348421ab58
  | 2 => 0x63141218f590538871e5350e428f990540c23d64141328fd9521d029d6394940e6501300c25d6315310a758c41d026e6214543a798c41502796014c219e195304425e63d53208f992508c7715148020ae59220442786550110da54a100426d65948108f99353083565354420cb152424869e63909429b988520423d64942328f59421d025e63d50208f596421072d5290841d5545300c26d6294f419ed95200823e6494d219b98853c425e631531097d954310ead62107409758e544827a60152218f596540827765504418f99253c863d60953329b58b54cc23f6055232cd547400c26e6294f408f99052442bb6054d40ce951500876551c80209e980530423e658c940c7552530427a60d50318f993530427960d5031c794f4290a3e64942328f994544c67a6015031dc546300c27561d4c209dd9510042b96094d40a7992324cacd638c8328f583544863e6414532c754f411063e64145208f593530873a6454031c754c53d023e6414a108f99053443b131501109798f540432d52149409b588540c23e6494f20b398f424ca5f654c4318f99250cc63e6494321c754f400831e5350010ab588315023d6414e209d584538835953540419b988530872c6255232cd951510c23e6494832ae58051d023e65d0d418f191534425d63145209e580540ca3d64940329e9805150e3e64940219b98b540c63d65cc9408f990504867960150219d987540c25e6314c21ab98a53d02ae6294d40c7152434c66e62145408f191524423e64d4810aed81325029e6390940ce591500c63e64d4f218f590530432d54948319b98854042bb6054540ae582215038c43d0932d554f10042b9600c740c7553310c63d64d4e208f593520427465485109798f520426d62153108f993534823e6494b319e580548871d5454c10d3951320caba60085408fd954310f6952540419e980548c65e63150218f992500433941540418f59053c425e63150318f19151cc35953440109b988514c25d63d5320a758c51d025e631454297d8d52443395444010ec885404432e5454810aed95408432d5494830ce109501063c654c740a758c515023d65d0010ab98a435033a4254041d994a510c23d6414c20ae580325023d6494b31ae592304423e658cb409798c548863d658c9409e980538872e5494810c754e431074d53d0a42a758f52d032d52d00108f59654087365454420a758e425032e5250030b6181324c32c4354841cb553428ca3e6510d42ae98031d031d5350010c7551310c66f6254d10cb54852d032e52d0010ab988415033b41540418f990530432e5454831cbd0e5290e7a60d4c21a798c515026e6214d10f848520442b96490110ae580215025e63150208f592500826d6215231c7551530831d5310c41ae58353d023e64d49308f590514cb365150020ae592208
  | 3 => 0x341106406074000280b004240bc720240204141010390840002c0c0000e035610300900c5c0281901c032940003c1100004474000041e0000002c050382331c19000376c8065000003839020b7038000047a00406004240000a03c09124070415b22805644010701300c063380505c02000024081200005018140c00001803070001a4150700c410050140c000030005e054172e42b0280000400000000280100007054000407f0001217c4000422298000ec4c0406501805018050a41600000000360c80100c15000120002f0b491061a00403800c520442800807004016a4000001e000120d0060f40600405000190100a158000380a098080380c200200040406c00000000411c0480000805000101140109c000301600004005db014000bc1700c553205001c01018050100f190091640001802004f70180a05405010010481e8f993538423c6548740e34c8325023e6415010d654e501069e6390b40cb54b400c34e53948418f990530863f6454910da94a500c65d6594c20ce992500c74d53c8421c795153082756115030ae582515029d6308740ae982315025d63d50218f99421d033b6550110a798e42906ae62d4f409758e52d071d5494c20d314d324823d6494332a798c215031d53504418f594215023f6454b109b98b540c34d53548419758f540427661150328f59431d025d6314910d694d500865d63d50208f992544c7355150020ce95250086b960d4b408f19521502ae6214540cb551520c69e63147409758c520423d6494f209758c540875931540318f590534426e62150318f994215031d53108419b588538431d53908419798c540423e64d4a10ae980325032e54548309b5885150e6d62d50308f990514c25e
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x22004701466004c0034200000010060008400029539486a8083a24c9600c940e22a7a022008591731854044216bb0a9192438319132544329c2e2302649041d76153324c6d0b90c2a02212c1d93150110c1cc6a948420d4571151320ca8d39c84a8083c85454048020a1ce9b2a641970952501300c3062a2c721243525c0544c832960ec90a8088709535012008258b88c099281345cc6150110e42a5a02200860c5458a434c788a8a80980610e5c06454432a62eba02200860d5398a4310668b88c099261385c86150110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa09801913254432909809d3654c832
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | 2 => packedAt s5K2 (i*60) 60
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s5K6 (672+(h % 28)*6) 6) % 42)
  | 5 => 2*((h/273+packedAt s5K5 (19845+(h % 273)*10) 10) % 735)
  | 4 => 2*((h/258+packedAt s5K4 (27056+(h % 258)*10) 10) % 712)
  | 3 => 2*((h/31+packedAt s5K3 (1470+(h % 31)*5) 5) % 30)
  | 2 => 2*((h/7+packedAt s5K2 (120+(h % 7)*1) 1) % 2)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xcf0fe1f8f1fe3f8fc78c7c7e11f8fe3f0dc4cf
  | 1 => 0xff1fe3ffe1fc7f1f80f8f8ffe3f0fc3127b33
  | 2 => 0xf001ffc0ffe007fe3ff00ff01fc00ffce38c3c
  | 3 => 0xfffe0000fffff8003ffff0001ffff000fc0fc0
  | 4 => 0xffffffff000000003fffffffe0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x6140280110484210010414124048421204c045
  | 1 => 0x2004000200008020000808402100400001112
  | 2 => 0x80ac8492448495005a900920948229a8630c28
  | 3 => 0x42415a489140124aca920011926a088b80e80
  | 4 => 0x28c919300dd92649374e4e49c004c132dfe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8feeceee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_39527
namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xf802812950013b702708858460100500220004024d00ffcc005fc5100ff04003bd4001ffcc8057d5100efd00057f51017f54403fd4001ff54c07ff4300ff0c005ff3100ff94005fe21027fd0807fd3200ff88005fe31017f0840bfc52017fd0403fe40027f10807fc53017f10403fe1002ffd4803fe3001ff8c803ff2001ff90c07ff5302ff94803ff50017fc8405fc3101ff50c09fc54017f90409fd42017fd4407fe53027f95003fc5002ff54803fd2000ff54009ff5400ffd0003fc40017f4c409fe4200ffc4007fc43017f48403fc20027f55005fd4101ff0c803fd3000ff44005fe51
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/28+packedAt gbK8 (1664+(h % 28)*6) 6) % 64)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x861f8fff1e187e3f023f07f83fc8304f0dc4cf
  | 1 => 0x7e1f1c0e01f87c7ffc7f83fc1d0c1b4127b33
  | 2 => 0xf801fe00ffe007f803f8003ffe270e38e38c3c
  | 3 => 0xfffe0000fffff80003ffffc000380fc0fc0fc0
  | 4 => 0xfffffffffc000000003ff000fff000
  | 5 => 0xffffffff0000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2024204080a09080901080880100104c045
  | 1 => 0x2209084000080424042401201004094001112
  | 2 => 0x880124086a200490129010a5b4030628630c28
  | 3 => 0xd5540010b35550002324b68084380b40b80e80
  | 4 => 0x41100022dd9e6724b800230118bdb000dfe000
  | 5 => 0x6799c93c01044000c000c406213eedfe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_39527
namespace PEqualNP.Outside.L_meta_39527
open PEqualNP.Outside.L_meta_39527.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 6 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 56 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 781 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 bs0_4_288)) (concat (concat bs0_4_384 bs0_4_480) (concat bs0_4_576 (concat bs0_4_672 bs0_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 801 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 6 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 56 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_768 : Interval s1Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 781 := (concat (concat (concat bs1_4_0 bs1_4_96) (concat bs1_4_192 bs1_4_288)) (concat (concat bs1_4_384 bs1_4_480) (concat bs1_4_576 (concat bs1_4_672 bs1_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_768 : Interval s1Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 801 := (concat (concat (concat bs1_5_0 bs1_5_96) (concat bs1_5_192 bs1_5_288)) (concat (concat bs1_5_384 bs1_5_480) (concat bs1_5_576 (concat bs1_5_672 bs1_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 44 := bs1_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 15 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 68 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 894 := (concat (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 (concat bs3_4_288 bs3_4_384))) (concat (concat bs3_4_480 bs3_4_576) (concat bs3_4_672 (concat bs3_4_768 bs3_4_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 820 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 bs3_5_288)) (concat (concat bs3_5_384 bs3_5_480) (concat bs3_5_576 (concat bs3_5_672 bs3_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := bs3_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 2 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 30 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 712 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 bs4_4_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 63 := block_range (n:=63) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 735 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 bs4_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 42 := bs4_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 2 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 30 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 712 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 bs5_4_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 63 := block_range (n:=63) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 735 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 bs5_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := bs5_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 1 := bs5_7_0
theorem alls5 : ∀ k ≤ 7, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := bgb_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_8 i (by omega) hi
  · exact allgb_9 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8fefefeeafeeceee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_39527.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[2,6]⟩,⟨.or,[0,4]⟩,⟨.or,[1,5]⟩,⟨.or,[3,9]⟩,⟨.and,[3,9]⟩,⟨.and,[8,10]⟩,⟨.or,[7,11]⟩,⟨.or,[2,6]⟩,⟨.or,[12,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_39527

open PEqualNP.Outside.L_meta_39527 in
theorem PEqualNP.Outside.L_meta_39527 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
