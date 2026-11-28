import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_39357.Model
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


end PEqualNP.Outside.L_meta_39357.Model

namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
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

def SBf (j : Nat) : Nat := [8, 6, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_39357

namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0xa3c50c005190000001210008a08024f003fc42fe41ff42fd41ff40ff43ff30fd10fc21fe21fc20fc31fe40fd30fe10fc30ff20fd20fc41fd32ff10ff31fc43fc10fd42ff41fd43fd40fc32fe42fe43fd21fd31fe30fe20fe32ff32fe31ff21fc40
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2417d544c67aa9985f94430be2a063f910042faa620df55241faa8e657e544cbbe61185fd5021bfa8a41bd43103ba63986f10440ef29e817e50103f240106f95032bda8263df300c2faa3996f90140be2a0217d508c7ea62886f55020bf29861ef21086fca320df54331de2a2417d53d03ea6390df94621fda0641de53043f621085f55330ee29a855c53442bea6a15f54243fd904417d52887be63985f54f42be29c217e51cc3bea6905f54a31bf29e217d54042fca418df14141dfa1a85f9300c3f4401077cc832be2a6656d52102bea6885f54810bf28663bd43902faa7195f94a319e2a263ef32087b8a6885f94342bfa92817c52502fea8995f54d21beaa4877d521027ea8905f94832dfa1c817c53503ee20085fd4931bf28483fb504c6fea9087dc8610af298217e5190afaa718df54032bf2a463df53442faa7215f54b31ef298837e5090afea5885f14c20bf28643bc43907f061885f15232f799265f610442faa5185f54c40bea80637e52d02f8a898df94c31bea8c61f8504c6faa2105f95021be2a4617c54cc3ea4210fdd4542fa208437d54ccafea690ddd4542be29c437c544cb7a8420fb54840be2a061f7419077aa990dfd4a10df210817e52082faa9887754e21eea1e637d510cbbe62985f14f10beaa6437e50043baa6087ecc010be29a857e51d02f8a2a05f54a43f6a10437f504867aa990df54343bf28e87df328ca78a8885fd4542bea9c61fb40082faa5885f54a40be2a2217e521067ca8195f54d20dfa10857d52882fca021778c130ef29c437c5050fba62985fd4c21bf29883bd54cc2baa6085794f40bf2a243bc41903e8a2905bd4931bf29e417e51c82fea80877d4d42faa08837e508c2fca5887d8c431bf29c877f54886faa998df54e40f7190657d52106dca4205f94020de2a2217d51d0ef8a690fd4c421bf2a0657d54487ba8621fe50040efa1865dd430c3da4210d714d20df212857e538827ea898f7d0e32bf2a0417e528caf6a0a15f94a30bea8e41bd41106f8a790df15220fb288617e53486fca8905f94f42be2a6633e540837a86a17b90821bf29a41f4218437c85205fd5120f790c43745150afca2085f95230be29a217e500c6fea7085754e21bf288437f53042fca9195f55230be28a657c52443baa7a05f54e10fba8a417c52506fca021ef90e41fb18e437f544c6fca8085f55210be2a2437e52042d8a4885fd5020faa88617d54c83f420085f94843be29e415d53107bc63187bcca21fb18a217f514c37e8520dfd4810bea88877e51ccbba60185f15032bf284633e54cc3dca5a0fdcc531bea9e21ed42c82faa610df95131f6a12417e54cc37884205fd4141bf28c617d52d02faa9197b14910bea96617f548c2fca218df14542bfa9a21bf4190778a898df95110ef18a637f54c82faa010df95040
  | 1 => 0xd5210fbc65187790d31bfa9e437e508cafaa5087ed4142bf298877e53086fca4207d88421ee192637e51882f8a098ef10c41ef19263bf4390efca6105f94632bfa9a857c54843bc8798df54632f6a14437e5410e78a890774c832bf29061785050afca5984f55020ee196637e5410afea4987e10020ae29a857d51d0bb886197b08620ef196637d54082bea6907dc8410f7a92217c514c3ea20085f94b41bea86857d508cbdc85905f95331bfaa261ee21486fca820fbcca32bfa98417f5250ef8a5885f95332b7296837f54ccbe8a2a17d4c710dea16817d520c6fea910778c430fc206417c54482fca0197b90920f7290817c548c6baa7a07bd4931dfaa263f631086f8a810df15130f7900417f54c42fca1996fd0c43af29c437d540c3bc86186f50c43bf2a443bf40902fca521f70c630f721443fb308c37e87a15f54620bf28c63de4310efea7887dd0541bfa9221bf42503ba6218dfd5232bf28421ed20082dea488770c830bf28883be54c86faa6087ec4110ef190617e53d02faa321df15221bf288857e52cc6faa190df95310bfa9c41be54cc2f8a6905f54d10be282857f5050bee210877cc431beaa2617e540c6f8a4a1df15320dea108576510c2f8a0995fd5330bfa8a877d52d0efaa0215d94732bf28043be41102f8a5085f54c20eea1a637e50d0efca410cf95321bea9e837e5110efea7905fd4941af298837e53c87da84216f10a40bea84437e52907de84a15f55120f619043ef20882fca8984f55032b6292637d51d03ee6318fdd0421df218837c53042fca4885d14520df2a0417e5090fdc40905f94341bea8483bf42106fca2207b54b41bea8083bf54482fca3205f95321bea8c217e53842fea8187ed0240bc282637f504c7ea6218df94b43bf280837c524c7b8a6907d94732f619443dc310c2faa8196fd0b40bfa82657d51902fea8195fd5231bfaa643ee21082fca7207ecc130bea92217d54887f0a0a15f15020bf284437e5210b7e8220ef50a41bea90617e500c2faa6217d08410fb90c43fa300c2fca9905f54642efa1c877f514cafca5205f94240bfaa0637e5390afca9105f94a10beaa2657d548c77a87a15f14e20df20c817c514837c86a1fbd0a42bea88817d5090bec8220df94420f710c41bf4290afea2a07b4c832f7210857e5310afca1106f90541fd986217d53907ec63885f552209faa2217c50486f8a4087754c41bea94837f54cc7f680a07b14931baa8e657d53c86eaa2185f14930beaa4817f53507f480205f14c21bfa9c43bd42502faa3985f54442bf29c43bf54442fca6195fd4d20bba8a41dd438c2fca6205f54332bea9c43df4350edaa5a0df54e20be2a621bf43102f8a2a1df54f20bfaa2217e510cafca9085f55242fb90a437f53503e88390ef50040bea88617d5010efaa5a0df94643fd90
  | 2 => 0xb0020640601c004542c000002b40001002010100340008c58000030485f7580c0a0030001a09cdf02406080010199b0c0070001b028020001422c060742600002498000141d00035114333ac0606c06020040c8000006e014ac00024030000001f00c000082f08c090080144486120330842e001810000528c00000003d8030000003c0d1c4000040101c2e0a462060010000001c0410892334000080e0b01b15c03000010a0000500104de20081d000000880700a360c8910080100000434271a8900040b274040041f06c12028630b82f03078168030040003803024000b4060000002c00004000801d36c09010022dc3502cc41f4030080c000050180839cbc070002a4000184905c0d048000101d01c020000a19c8bfc180217d540c6fca7a0f790e30ef98c63dc438caf8a990df55021bea86837c53506fca5216fd0040f6108417d54442fca6885f94742bf29c83bd540cbbc64995fd5121bf29821f741c87b865185fd4143bf2a0617
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x142502776548421ab593218876b52d4131b6181314c3543254430d314f52442796014c21d68c8504c67a60d53329d185544ca5c6354242cdd8554c865e6394910cb150524433854c81209798c540872d52904408fd91534823c6454732cbd53524c7686054840b5587320ca7561d5030ce9085050a7960d5221d6d4f5050a3e6515131cb150524c74f6354b419758c54886d8604c431dad48504c63d6414c21b318d428867b6054d109798f520425e6394421b558c41086e7624c4219e582544c63d64148109718d544871c53d0d42ae583431034f63548409798c530425d63d52219758c54c429d640c830ab590328863e64951108f59253443386055020d314c52442756194d209758e5190a5c6354b419dd95100436561d49319e594300426f62546409b98854cc63d65908409b596420865c63549109798f548865f63551109e583540c65f63540218f997425026f6548020ae1814210a6c65509208f990530866c6254643b958732086e76150821d514f5150a74654c5108f99053c431d53d0b409718d500872d5250040c755131cc25c6354a109b189544c2796015021c715353442d56388421bc18131c872d54c80208f993538425d63d52209e181544c65e6394720b5185434c6776155120d5d4f5150a766114c109758e544c2b96010440c754d42d02756194d219d987540c31d54d0c329b98854042b86050a419798c540426f62544309dd85544866d62951219b98a544c66f6254d10d354c328863e6414f219d58454ccb1c548c9319b594320866d62951318fd91510c25f63551209758c54c83676254430cb588544825d63951209d587548833b54d41319d984538831c635503297d95320ca776154b43d5544310c25e6394d109e58354cca3f6550c43c755331cc27761548409d986544826f65508429e980548ca3e64148109e181534863e6494a319dd85544ca9d63104408f99352c423d64948218f191500863f65508429e58353c865e6514d20d9908514823d6414f218f592530c3d2310c3109d984530832c5490920d68c4504c66d6294d1097596430c2d96090c30d614f5050af0604c71097d8d528431c5414d10c754e431072d540842097d8d52d072f54149319758f52c42ad62d0441c7d50534423f65504419b988548c23e64149309d1855210355518c430ab590320863c6454232a759032cc69c63508419798e5444354538c510d558453443346454732a718d429067b6055120d554f21042d8604c7309b588540c2f0604c421d550d510c29d6310640d690c504c65e6314540ba18142c829d640c9318f596540823f64542329b98a54c434f53d491097d954310e3f64542319758e54442d863440109b58854cc7646154840d5545300c25e6314810d590d510c23d6494b10da14b504c65d6594c109ed95100435453d4520
  | 1 => 0x872d43548409d185534825d658c4308f990540cb5b53141429d586544826e62d4e10b9189100423f645462097d8d521027965100208f992524425f654c030d9d8552d071d63151319d584530825e63d52209758c540865c63551209b588548423c64544309798e548431c5414d209758e51c834f6254e21cbd0d52102ad64c84219ed95401023c64542319dd85544c2766194f208fd91534866d62d4e10d3d48324c764524c5109bd895190e3e6414c209b58a54c423d6414f109bd95210873454d45208f593538436452841108f593530823f6454d10cd55041c866f62551109dd95310c63d6494910ab1894350b586054c10d554f218867661153328f990540825d63150109e181544ca6d6215230ad19131c873764544309ed81544877051141429e982544c6746154b43b318d420867661d5332d3d4c524431f54d4d208f992544c6b86050b409dd85524423e64951208f99053c83d131cc3109ed81544c65f654c431b5587328ca776154a309d185528c32f54d491097d8d544863e64d4f21d58c9510c26e62949109b189544425f63542418f592528c63c6454d20c754d421066c62551318f59053c832d54884209b189519023d64d4f219e580548cb7351d41429b189534435553084109d986534827765504419b988540c25d6394910cdd53514823e6494d209ed8153487394314142a758f401025e6315310cb54b40103a54210421add854210757531452097195434c76761548408f99253442d56310721d318d521026f6254d21c7d50534827a60d4f218f191534425e6394d2097997314c26f654c8329b98a534435553c40108f191524425d63145408f99052842e9621032097994534432f54149108f592534823d6414c209758e510863d64149309b588540425e6315221d914a314423d64d4b109798f52c425f6355132ab58b419066f62551308f992530c33764547329e980540863f6550040a758f40903345414520cb54a42102e86050a219dd85534825d63148109ed9520083645188120ced0c5050a5d63952109798f54042756115030a7593308c33854d4131d9189510c27965840108f99252c42f1610c3108f992538823e6515120d514c514827a6014c2197d8d5090b5853141429d58754ccb5853c41109ed95300c334645443097594430cb735114142d514c5150b1d53d08419758f540423f64540218f992520872c54d4910c7152434c72d52104409b98a54442d9600c830ce150504c63d6494e20cb548421027461551209798c540c75953cc01097d8d52442b860508419758f520426f6255131d5d4c5150a6d62951108f993530823e65151109e181544871f54d4d10b9185200829d640ca30cb551200823c6454d219d594210433b54141319d59441087594314131ad19131087375414520a7593300c3654214520ae18
  | 2 => 0x54009001c1c0f010600810358d0121b0000005490082800410c80816e04381402270900400040003004080003806ca151680401248000603048080002010021a002081004450f0040030038012010038000a030281562000408c020300000042504800b0290003972090281c040503cb80800000143d8903830d20602840100a1d1b8fcad4e2c4068fd2019705e043a0462c0486410000280c060a0adec08c803818d279000781601094f00a000180002145d02c4a051214c2a2c3d8100003d785c3405690bc004e43130ac18008129a1702800c805018023d6595032ae191200825e63946429d185544c35551cc030d554d100425c63548409d984540c25c63542418fd91524427a60d50319e98354887a942d0320b958b410871c54d4d20c7150324c67661d5220dc181510c2756194f208fd9151ccb7051d4142d60c8504c6e860508219798c54c823c64546209798e54482756114e20da148504c7aa42103209b988548426e6514910ce553400825c6355110f10c9310863d6414a10cb153524c74c6354b41d5d4f514827b60551329b988540826c62544309d596310
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40800680806ac2a000081000106814a5c34354840b08e6a108210e60611815210254bb48420641a1190324c421aa2e0192a21860d6354b40102c2ba064988438654c6050b40c2ac8a8e60186c0321813108714a92c02088186550604c730a2ae8192a2185287250c5050b12aa0c290041541c54314131c48c8312a218685635084108730310c0a8861545c24354430c1ac6a90822041d76150324c70ca98c0a1083465d03214131c88c630aa4205a0705084108668bb462186219154c6244010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc81631c1421042188587190324c421a81840c8604c421
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 6 => 2*((h/27+packedAt s0K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/224+packedAt s0K5 (17064+(h % 224)*10) 10) % 632)
  | 4 => 2*((h/192+packedAt s0K4 (17974+(h % 192)*9) 9) % 473)
  | 3 => 2*((h/23+packedAt s0K3 (1421+(h % 23)*5) 5) % 29)
  | 2 => 2*((h/15+packedAt s0K2 (180+(h % 15)*2) 2) % 3)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffc07ffe03ffff03fffffe07ff81ffcff1e3f
  | 2 => 0x1ffffffffc07fffc0fc07ffffffe07f31ffc7
  | 3 => 0x1fff80fffffffffff0007ff81ffffffc1e3ff
  | 4 => 0xfe00000fffff80fffffff80001ffff83fe03f8
  | 5 => 0xfffffff0000000fffffffffffe000003fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc2530a2238912300b2ca9642a590ce4570e1b
  | 2 => 0x54a8514444872452c05522a8ccab24293076c5
  | 3 => 0xa910a26a891248a5550284d521345952c1a16e
  | 4 => 0x31a2c58d12240ed9a69b301849c79623ba03b0
  | 5 => 0xc1c3060e1c3870ee38e3c71e70061843edd800
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fc00c000fcccf0c0fc00c000fcccf0c0fc00c000fcccf0c0fc00c000fcccf0c0fc00c000fcccf0c0fc00c000fcccf0c0fc00c000fcccf0c0fc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_39357
namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40004010000000014ef20ed20ee21bf43de43bd43dd43ec219d43
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x3000000c6a1e418f5250f1a869063149438eaa4878d438871a8610d914520
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x50083d9543887054314520a19875250e0c6550d20
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/17+packedAt s1K4 (144+(h % 17)*4) 4) % 9)
  | 3 => 2*((h/9+packedAt s1K3 (216+(h % 9)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s1K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1fffff83ffffff81fffe0ffff83ffffe71f1ff
  | 2 => 0xe0fc1ffc1f83fffe1c1ff0f07fc3c1ffae4e4f
  | 3 => 0xff001fffe003e1ffe01fff007ffc01c1cf8f8c
  | 4 => 0x1ffffffc01ffffe000007ffffe01f00ff0
  | 5 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40080088010000002022011108044444009095
  | 2 => 0x8a312910ca2550960d0c90a2324288b8a6464a
  | 3 => 0x465a5229474a832ae2172a055ca8150d4b8b8c
  | 4 => 0x94a39c429460d5cd5741888867333811f00d60
  | 5 => 0x18c31873187319f19b99ccce06222021fd6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0faaafaaafaaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_39357
namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x101a20300600100440500811a0800c2001341011001fc32fd43fd40fc30fe31fc40fe20fd30ed20fe41fc41ff30ee42fd31ef20fe30ff10fd20fc42ff40ec21fc21ff41ef32fd21fc10fc31fd32ff31fe32fe40ff32fe42fc20fe10fc43ff43ee21ff20ec32ed42fd10fe43ff42fd41ff21fd42fe21
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x165e0400074400004008004f87c29842c09704c9c01543814013c481c4c0c1c0028006004101c000c11240ca80000344c006802d8a7905b94432b728e655e531027ca810db94642ba28a616d52d06dca610cf15110b7296872d540875aa8195d547439eaa0616e52042d8a2a15b54a30bba8a616c524c6dca5a0db551209f2a663ad421027aa8087394c329f2a0616d52103cca210db94720b6a90873f544c2dca518db94e21bb28e876e520c2daa0195d94430d6a12836d52106d8a2905b14d42b6aa6416f52442daa9215bd5320b7aa0432d540cadca420dbd4931b7aa4436d528c67aa8195b14e21b6a96876f524c2dea5885b54a10b7a92836d54ccadca310dd944409f2a021ad42902d8a4885b94b40b7294216f540cb5ca8197ad4120b6a80436e52082eaa2205bd5120b6a94416e5210edca6195b14943b6a8443d5310c6d8a4a0d794c10d7aa2856d52042daa5205b54242d6a1a856e510867ea8884f95032aea9e836e52cc6daa810cf95320af29e836d50cca7aa998db948429eaa4636e53c82dca7215b94d20b6aa0656c524c2dca5185714d10b729081ad42d06dca5196b95320d6aa641ae54086baa62057d4d10d6aa043af4350a7ca918dbd4142b6296216d520c2daa910cf15130b6298436f54ccadea4a1db94a40b6a96632d54c827aa9904f55021baa88616d52d02d8a6905754c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x130025302a05840190000800a08bd9150ccb0c5350d428b59052c42696014c218b590534822d64947328b592520822f64542219998754cca2d6494e218b596540cb0d5350b418b592528c22d6414f208b590514832542544409398f548864c6355120a9185425062d6494a108b59053086a561d0d428b59654086646155120c354d421022d6414931
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s2K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/51+packedAt s2K4 (3618+(h % 51)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s2K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffc1ffffff81fc1ffffff83ffffe47f1ff
  | 1 => 0xf07e0ffe0fc3fffe1fe1e0f07fc383ffba4e4f
  | 3 => 0xff800ffff003e1ffe001ff007ffc03c1c38f8c
  | 4 => 0xffffffc01fffffe00007ffffc01fc0ff0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10040044008000002002211108048844009095
  | 1 => 0x25189488650550960d20c8a2324112b89a464a
  | 3 => 0x432dad14a3aa93aae3117a855ea82b0dc38b8c
  | 4 => 0xa514a214a20c54d56541008653270116c0d60
  | 5 => 0x8c618c398c3319f19b999cce06204221f76000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_39357
namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x14225700210004b0010005003030430031c024cfc43fc42fc41fe10cd32fc30ff21ff43fe20fe32ff20fd21fc40fc31fe21fd30fc32fd32fe43ff32fd10ee32fd40ff41fc10fd20ff40fe40fd41ff42ff31fe42dd32ed32fd42ff10fe31fe41fd31fe30fd43fc20df32ff30fc21
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x20d8000000780810200000192818b9b8392818f0800878084800819800309000411008606048a800685800282800002800901000080131b000680008983028b734cb419eaa021cd325079a6598db94a43b6a90636d5210f9a6498734c921b7296636d52cc6bca621734ca31a6a9c65ce544cb6a8220d754e41aea9e43cd32d027aa990f34c920e699421cf544ca7ca8085754c10e7a9a656f524439a64885b54e32afa9a8175510839a6510db94840aea98853d540c39a6418d794c21e699281755190f9a65207394132af29e416d52cc39a6520f34c841e6990416e520439ea0995b54b41e7a92655e53c879c84995b94b30e7a12656e520cabca7a0dd546429eaa0415d5310398a2995d54440b6a9487cd32042dca520cf95331baa88616c52502e8a2a05d94643e699081cd32cc39a86995754c21b6a90613e540839a65907394532e621a65ce434cb9884994f95321af298655e531027ea888734ca20aea9e413d54cc79e86995794c20ae29a215e5390a7ca8185754c20b6a9483cd544cab8a6a05dd4540e7a8a65765190b9a6498f315132e6990656f52502dca421f350932e6a8a655d5390b9a6590f354132afa9a215e53042dca5a0dd94440aea9e8376510c39a6518734c821e6282653c54442eca2105b94830b6a9021cd32c42d8a4885b94831e6990615d538cabca720db54840
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8804001820000f060a0400300000070c948800e0408b000000500012290204000000c002001000010587809358e520424f654cb41c3d51324424e654c9409319532443453294420b1984504cac66195132d14cb515024d6214d40d14ca510c30d544c820d1544514ca4d6294e4193589530830d544cb319358e52d068e6414132b1587544ca4d654c8109358c524424e654c910a3590504cac6619093293d95320430e544cb21b1586424ca8e64d4532b1586544cac661d5132b1185504ca8c6454132d14c9510c24f654c840b1986434cb0d5415132c3951320c28e6494532a3592514ca4d6394840b1584504ca4d654c8409358c525024d6214d109358a531024d654cb41a3593514ca4d654ca41d14c951082c76154132c355132c87453254440c395132cc70c544c910e14c9411068f64541329358e529064d6294c10b1586434ca4d6294f41c3951320424f654ca41d14c851503453294440c3551320c30d544c810c3951320824c654c940
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s3K5 (720+(h % 29)*6) 6) % 45)
  | 4 => 2*((h/64+packedAt s3K4 (3483+(h % 64)*8) 8) % 129)
  | 3 => 2*((h/50+packedAt s3K3 (2584+(h % 50)*7) 7) % 68)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfc3ffffffffffff03f07f07fffffffff223fff
  | 1 => 0xffc1f0f83e0f83ffc7f87f870e0f0f0fddd293
  | 2 => 0xfffe00ffc00ffc3ff8007ff80ff00ff0e1e31c
  | 4 => 0xfffff0003fffff80000ffff000fe03e0
  | 5 => 0xffffff000000003ffffffffff0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4000008000000000000800900110100000425
  | 1 => 0x2894611194551512c3283282268a2a2e4cd292
  | 2 => 0xb10caaa28d6a517558a45b504ba84ce2e16318
  | 4 => 0xa3a94cc5294359b9adb50a408dcce844f603c0
  | 5 => 0xc2318886318c622e36c66c64e1008088bbb800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8eeeeeaeaaaaaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_39357
namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x80c10042800040400c50521471400020010012806ca003000500fc40ff30dd30ff40de32fe10ff43fe20fe21ff42fe31fd40fd41fd21fc41fc10fd20fc20fd43fd31fc30fe30fe40fc31fc42fe43ff32ff31fc21fd10fd42dc32fe32fe41fd32fc32df30ff20ff10ff21fc43fd30ff41fe42
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4857e51d0efea7885f54231beaa4617c540c6faa9887dd4520afa9a417c544cbf660985f94640ef19441f521442fea7105f94031be29c437d5110adca4085f54743f7a12857d54042bca70877cc110bf2a6617e54442fca4087794730bf29861dc42cc3bc65887d90421de216837e520c2faa710fd44010bf2a0637f54043be80987754232be2a441bd42d02f8a298778ca21ef19683de214c2fca118df54021ee98441dc324c2fea6a15fd5330be29a437e50107daa4087750f31bf286857e51907f220085f94620be282657e5390bbea1194f95020efa9a85dc32cc77a86a0df14520bf2a0217d510c2bca6087710e32baa8e853f54482faa899778cb30bfaa2617f514caf8a8907794930eea1c657f54883be82987bc8621bf2a665f610442fca9195f95021ef98e61f621c42f8a6905f54c21df212837c53c82bca41977d4432eea9821dc438c6faa598770ca31dfa1e837e5084378a8907790a32bfaa065de53082faa018df55021bf28887dd30c43de41107e8c030ef18e617c53083bca7a15fd4b10eea1a617c53842fca8986f50040be29821f651102fea4a1df15010be28243dc434c2fca2105f94b41bf29c817d54443ea6218f78c921eea9881f541086fca010d754e30be2a6615d539037e84a05f95121bea9663de424c2fca5185f94d20beaa6417c5050afaa198df94a43beaa4815f53487bc8798df55221bea9e41be41506e8a29077d4130ef190837651082fca621f795232bea94437c524c6f8a9085f94243bea9a217e500437aa818f794530bfaa2217e51ccafea2985b94840ef192657e50103ea8298dfd4810bf29043f6414427aa8107790b30bf288857d53483bca0195f95042bf29e43de434c6f8a998df54321ee19681fb40902fca4205f94b10ee19441df40cc3b886195f54a41f699065ed4210afca4105794c40efaa261dc414c2faa9085794b30fda02817e53907dc85905f54243df212857d538caf8a7885754c41bea9a437e50d07bca898770ca21ee28c657c54c83be611077d0730ef194817e540c3bc64a07b88120bea98855f53c837a82a07794b30f799465dc32d07dca4085754232ef29c21fb10842faa020d794c30aea9c21df540cafca8997788730bfa82657f53c86fca5087714432ee196217c5150efea5085f54f10bfa92615e53107ba6218df54e42ee2a0657e54882fca310df54e41bf29c417d5290fbe8721f750c43eea18657d50d07b8a298774c930ee90a617c52c43baa2985f94220efa1c635e528cbec8318df54440bfaa421dc43cc3f641107750130ef2a661de420cb7a84a05f95321bf28883f541443baa620dd54443ef986217d53083be42985f14810eea1e617f53083bc6590df55130ef19421dc32487bea690f754930efa8a61de32c82faa2195f55231ef202617e50903bc87195f94f42
  | 1 => 0xc54486f8a2a15f94632de21081dc51cc2fca52177cc210bfaa265dc53486f8a6a0f70c530be292617e5310afea8186fd0842ef19461df30c82faa5a0df14143beaa485dd32cc2fca898df54610ee98a61ee4210afca5a1df54831bfaa463df30043ec8390df94730bfaa4653e540c7be65197dc8521fba0a837d51ccb7e86a0df94e109eaa0217c54887bca7207d90441eea9e85dc32082bca7105f94742f790843de304c2faa1a15f54720bf296817e5090bf420084f95010bfaa6637551082fca198df94f41ee19081f721042eea29077cc631faa0e21bf40903be60105754c20efa1c65dd510cbbe64987dc8610beaa263f651083da4010770ca41eea8c65bd54886fca421df95310bf29863df52cc37e82a07790c32bea8c417d53d03b8a7905f14943bf298437f540c7ee6318f790c43fa28a417f548c278a89077d0832fd98461dc324c7b864907794632fca00817e53c42f8a2996f10941ef20e61ee320cafca418f7d0d30bb28881dc31cc3b8a4985f95221bf288637d538c2fca3a0778c910bea94617e53043ba85197710a32ef21e617e520cbbe85987e90040eea9c417d52d02b8a6a177cc120bf286877c525037c852077d5232ee19061ef324cabca6107750930bfa9a217c54c427aa910df95120bf29e81dc424c3b86410dfd4d20efa8e61f621443ea8220dd94742ee21863dd30442faa9995b54810bea9021fb10442faa119770c831ef19663df300c3b8a9195f14f21eea1a637c54442fca9905f54a31bfa9a437f5050fbca1195f95032beaa065de510cabaa6087755330aea80657c52507b843985f15032e7290657e510c2faa120fec8120eea0e61dd31cc2faa920f70c941fba0c837d50d0f7e80207754032dea10857c50506fea090df54f41ef98a617f54486faa5205f54742eea8e617e50ccbbc6518df54830ee29a41dc328c2fca518df94020fa90843bf42d02fca6205f94f20f6a16417c544c7be64197dcc531be2a4657e5190efea9885f95040dfa0c837e52cc2bea6a0d754e20beaa4417f5150abaa7a17794e21df2a0637d50886fea810f7cc230bf29a437d51d03f240105f55121efa18657f505077a8220df54c41efa1a87f421843daa4205fd4c10bea8c87de314c2fca820fd90531aea98817c51502fca4886f55010bf296637d540c3bc64985f94421bea8085df32cc2faa8905fd4543faa88817d54cc6faa7205f15030f710a437d53843bca4195f94c41f6a12417f52507e842085f94221bfa9e417c530877ca8085794e21bfa8a815c524c3ea8390dfd4131beaa487dd420cb7c86a1ef90840bf288217e5210afea610df54f21efa1e615c53507baa6105f14910bea9083de32d03eaa2107750b30bfa9a81bd41d02fca721fd947429eaa063dc420cafaa021df94a32ee192217d5110f7c80a05f15230dfa1
  | 2 => 0x7002051181287e0180601800000100003200040330076682e0006808c4207806001d000002100f00002801000018140000205188042680000001802019be030ce3b80011cc80a00006908078160e0002f03c1111e088000180801046018624880a140340d0062780814a0a0793621818159520889806842e380014006058122e142010071b9140a024000100684c29808031ba0001c028020280803802000000001c008c2298021000004000060220700405800018090681a0b91801800160d6068125f2820f8beb49ae0600e0100a1183e008000212e00002018000101c0e82e3f0420a800038300002a178104886e05aa2000080b8080181c00030033cc000024ca663a80a000000f00008802018060606a1200034800019e237052080260007c00826269244d00408002000d40001612002000041001c0e0140683c040060a0000401e0700c0300005008b680eff80801016030fc0001c1284217000278080a80008814070fa000024400e0100000f70cb30fa90e21df53506f8a5087d94443eda8261dd53887de85217794c41bea86657d52882eca221fb90920ef190217e518c3ee4310ef95020daa08837e52106fca1197794c10fd100417d548cbba610877d4632beaa063be54887be8618fd8c431ee98641df424c2fca6886f10a40bf28061f9300c2faa7105f15130ae29a43bf41d02fca6105f94230ee196437f54c87ba60087b48720ee190837c504c6faa4887d90710afa9a857f544c6fea2905fd4e10fb88021f710842f8a810f78c820bea8e617f54483eaa3a15f14e20bf28087df524c3de43905754e21bea8c817f54c82f8a990df95210efa80655c53c82fca3905f54420bf28c63dc41cc3bc6520d714d20dfaa241dc5350afaa1215f94032bf288657d53042f8a6a17714d41bf2a041de32102faa718cf95221ee280656d52102f8a6887d50631ee980417e548c7b8a1195f54b10ee296617e548c2faa421df94a41bf28643dd53903baa5985f94a40ee98241df428cafaa99877cc431be2a665de32482bca7206f50f41bfa82857e51103baa9197710130eeaa065dd544c2fca998f790530ee192817f54ccb7c85a0dfd4940bea9687dd40cc2f8a918dfd4910be29a81de434c3baa7087715130f690a417d500cbbea6905f54630bfa9a83bd54083bc64185f94c32bea94217e5190bde40105d54440ee194817d52103bca710774c030ee10a617d53d0bbea7906f50c43bfa9c43de32086faa620778c831dfa1c87bf4310fba4398774c832ee20661f55110ebca7a177d5330ef19283de540cbb8a9987790330ee194217e5410fdca4205fd5020bea8c65f621086fca710df55321ef18a63de324c7de42905f94241be2a041dc32c82fea910f7c8730bf28085bf41106fea498fb48421bea8c85dc32042faa8107750530ef298817
  | 3 => 0x2028020000083a0005a0000800012
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x153042d960d53309d984544c2756115230d5544514c29d640c5309d58654c829c64549309719541cc39543505319798e5010a5f63547209d584544c2cc6254530c7550328865e65cc9308f992544825e63d4941b3988404c3365250441d314a214c34e528ca31b5984438ca5e658c920b5984544c25d6395321b658032c834e6294832b658032902776548421d398853c823c6454a1097997304825d63942429798a53042d56114232b558440cc25c6354b419758e54c823e64d4f21c7951438ca6f6550842c7552538865d639442197594320431e54cc010d9549511025e63d522197d95300c26d62150109718d528434f6394840c7150324831d5494c10cdd0d5110e9e6414232d954b100423f6454d10a799221cc29d6414530b5584320c65e6395320d3948320c25f65487309718d54c825f650c8419dd85524435960d4f20a7990510cad66110d30c754f41107ca3248020d398b53c825e658c9418f990514c23e6414c20b3988540ca5c6550d319758e544865f635512197d9632106b56488510ad592411074f6354840c755032042746154d2097988534825e6590d3197d95420cb1e5454c20b358840cc25f658c820ad592210871d548c831b598752cc3596014f20d314a324c25f6054f42d394a328c25e6394021c7551300825f65509308f99053086cc62551309718d51c82b561d0842b598443cc31c635503197d95320ca3c6454910a7990500cb6551480209bd95320cb3554c8621b318930c82d96010930cd5502104335549442097994325065f6355320d554e510825d6510c31e50c9411071c5414d20a759352cc2d56110e319718d524429e640c73097d81531065e6395321b3988548cb4c52d09309b988520435451cc1208f990540827a6014c219758253886ce62cc1209b988530425e63148109758c54c426d629513197d8d52902d9608cb2097d954310ed56110f309b988540c31d5410c3297d8d52d033454504219d185544831d5454e219758e500865d63150109758f540423d64947209798c515036652544409d98454042d561d0a329758f520433454d4520d5547300826e62152109798c54086776154a40c7552530823e651512097994414c33554440109d984520431e540c820d554e51d0b5653944409d586534825c6354a4097581530425c6254c4197d96320435453d45209b58b548c65d658ca109719542cc25f6354b419e580540ca756114c209798c530827661952329b189544423d64d4c109dd8553482756590421c7d5032483364254440d354d520429c6454530d50ca511023d6414a108f99742502d56114032cd55321042b564887109718d529074e5394810b6582524c25d63d4b109758c5050a5d631502197597430c65d658853097195214c25d63942419798c544425e6314a10d50ca510831d5410c31
  | 1 => 0x65d6394720b658351cc31e548ca2197594321027661153329798e508867561153329d584540c31e548c8109718d54c42d561d5232d5d46518cb3454507109e980540cb4d520c8109ed81544878d4210832a7590508cab561d0a429d587530836552944409798c540c65c63548409758c548425e63943418f9905304277654c43197d8d524434d520cb418f590530874c52085309d58454cc27b65500408f596540823d64d4b109719521cc34d528c8409b189544c25e6214d419d984540c69d64144329758353506ce62d503297997434c27661951329758f54082d561d4b309e59610042d56110130979943248335544c4319d584540825e63141418f990528436551c8020b598440cc34d539481097d96329027960150218f593538865e6315020b3d89544c2766115030cd15141442cf6254530cb952520425f654c020c755032083355150040a7992214c23f6454910b5984430cb1e548c8319b588548c3976350441d314a324c71e544c01097d8d529071d540c8319718d52043563214520d5947300823d6595031b5584434c25d6314a109b98b548c6d56110e329758c548871d548ca21c7953300827561951328f99053c434e520cb319798c53043655244010b6d81544c25e63d5321d954821043563254420b398b30c83365450721cb54940102766195320d5584535065e65d0b30b3588404c32d5210b41cd54740102756115220b598742cc23e64d4c2097189531034d524c0109759621cc34e52cc010e5d0d418c67b654c030d5145304829f6454930975835350b575314520d3948329065d658c8419798c540c23d64141219b98b540425c654c1209b588505065f6355120d954b210425c6214d209798c5050b3654544209d5845050ad66115330a7990314c2d5619523297596320c31d548c820d50cb514832d545481097596430cab46150d41b5185544c25f650c8108f191534427761551209758c548835653544209b18953442b76550441c7550540ca6f6255110d394a3210396535044197594414c25e6394242a7992518ca5e63944219798e51c825d6094c41c7d53304825f655073097d8d52c42746154a409758253d0b2d52d00409d996214425e650c9219d986544827b65440109e9805408675619512197597300425e6394d209798e534865c6354740d394d521025e6590130d5545300825e658c9219758f525023d6414f10d554d51d0adb6054930cd50d5110e3c6454d2097994534823d65950108f993530425d650c8208fd9540102d561d08329718d52107375414520d354a320432d54c80208f592510863e64d4b109798f540425f6054e21d994a511025f6355132d594d51d0a5d63940429dd85544c29d6414730b518d418c65c6550d3097994534865d6314810c7553430c65d63d5210b398b548ca5e6588730c795
  | 2 => 0x5494c10cb552520429f6454530c7952538865d6510c32d5d45304831d53504419d9845050a5d63145409798c54886d4615493097d9542cc25e63141219d587548ca5d6394321a7990514c25d63942219b58b53043355454420d50c9511029e641473097d9432902da60109309718d544425d63d49109d584540cada6015032e5504414c25e6294c4097d81530423f6550842f10c9210869d64140329798c548431e540c8108f59353083563294440b5584540ca3d64d4f219798b535063f6454a109799441cc23f6454d20d590d5110e5c6254e409758c544423e64150319798e5090715535044197597424c23e64d4810b958a4108675650841097d8d54c433754d45208f593520434d520c8408f99251c831f549523297d8d52103563294420d394832d063d6494d209759632082cc624c120b5987428ca5f654c4319d986534827461551309b98a544c65f655053097597420cb4e528c810b6980214c25e63d52208f990504875551147309798f520425d63141219758f5284274654851097d8d5110ad6619523297d8d544c66e62150209758c5408355535444097d8d544425e63d503097d8d521065d63943419b988548c26e621414197196325065c6354b109798f52c42d9608c820b5987548ca9d6488730d354d521025e6315220cd10951102d661101309798f5284335548c431c7551310c7543214520c7d52324831e544c020b5984540ca5f6548530b5584430cb365494420cd145415025c6355120cd151418c65d63d53218f590530425e63d5210b558742cc356514c020d318e52102db605453097195414c2d9600c910c7952530825d65cc020a7592518ca3e6494632d3d8e52042776550441c7551530425e639432197580534874e524c010d3948320c63d641481097583534874f520c940cb58854482d76154930d3148424c355510c7309798f52502756195232e554d411063f6550c43c7151434c2766115032cb548421025c6254c1097d8d51d03554354443c7d53534825d650ca40d5145314c2d661140329d987540825e6588530d318d520435a534c03097594321071c53d0d41c7153304825c6355121c7951538865f658ca1097580535065e63951219d984530831d5410f30d3d48324431f544c1209bd95210875751cc120d594e510825d63940109759742cc34e520c840cd505501075453145208f590514c34e5394840b6582544c33765504419798e50043355350441e550441cc25d658c8409d984540827661152209758e544831d54cc01097594328429d64d4632c7551530826d65948109b58b540431d54153309718d540867860551219d984548c34e53548109798e50d0ad6618c931d5544510ca5d6014d42cd150514825e639402097d9530042d9600ca108fd9541106d9600c940d58c951102d661142329798a531
  | 3 => 0x400200c26044031301f000a2000081101e00c03155d81184501003464340041c020bc01c470c80000cb504d370cc0106c79058071240004c010591f0686b000d60305a1b41a0000a0040301400000000650e0141804000018c80740400058078210200500401548390000400c0c0000500800694060542428c000480c0260600006008650a81200c0407471274010042405c3b058000280000c130287f00031008b60000400002004230081a1100d11ca90b405078110001000800010126ac424384913c21000440006d4fc0004c1c6e4082fa4c01000134000b40a354540000a01800000080a01d008140180402c0c05c1e0780605cb5000030a4000dc5181c0e02d1700e900144102c005f404088402402d0100e0051f04c000dc00004020840208088361b504801000000442b06c1c02c2b040b8034050314e05c0204c050040009c0b03c4b04401030338234e520c8108f99053886da6014432d58cb514825e6394642b398840cc25e6294e409e580530871d548c81097d9632102d661d0832f24c120083565354440cb54a421032e5454810d9147214823e6494d209b588540c31c548c920cb551200825c6254e10d594e51d0a7561d5020d318e520425e65101309798c540425e63d5020b558454cc23d64946329758c505065c63544429758f54887345450531b6580540cad96014432b658052cc25d63d494197596320429d640c7309ed95200825d63940419b588548425f6355021d354b300427565c8410d554d411065e6315310d3d8d520432c5490920b5587424c31c54d4d20a7993518cad56110c31d554e511025e6395120b6580214c2d960d4b3097d94328429d648853097596530825d6395132b658051cc23d6590840ad587425029e64d4b308f590530826e62d4c10d554e41106d76155130d9185520439632504419b195424831c544c120c7553310c67561951209798f524425d658ca409758e50d0b1d54151309dd95100431d54cc0209b58853042766115330d554d510823d6414e21ad986425065f650c820d318d521027661d5232e518d41106d56115130b6580320834e520cb3097d8d520434d53948409798e501075753d452097195424c23e64944219759653042d661d09309d987530826f6548020b6582514c26e6215010c7952320825c6354b409758f5488354325442097d8d52842b561d0b409798a53842746550510d354832906d9601533097194325074c520c940c7d50534834c520c9109758e500823e64d4e219759441cc25d6394642c7950320c71d544c01097d94321033554c40109bd89544c23e64148109bd895344274655053197997424c23e6415010c7950328871e
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x8004100304e20000008600000000000000000100304e00404200000156a0c00000001410000d202e000081a2ae22a2869854472544514c384aa2609004192149600c910c2aa8b088618e4852580325030caa2c019041455c65450e32a18e4aa0a89849574986324c68aba0a298a619114a61d0930a28eaa1a8298e1564544510cb0ab2a8220a61459c75495232a28e4a9a8220d15750c9411070aaa2c219063855516110f30a2ae628a82a06156454431cc28a3a2a228a6185d516195232a28eaa08829851674d46518cb0ab26a328c65165c0650c941a2ceca9a8220c4c72594414c322310a298241259da3250441a28eca9a8220d157315141c428bbac64a0883855516115130ca2a2b00a21951573151414430aaa2c22186583150624c120e82a2982401060e6414a214c28a38aa82a261255ce6190941aa2e0192a21053170151410870aaa2c22a661929896014f20c2ac8a88a3986156550441cc28bb82a6a0883855516115032a2ae72a28390e1954580540ca8ab98a8a0843855915114530
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2906829d95350441814875954110530a04825954110530c05641c9511453081686dd63250441a04825516115130
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => 2*((h/35+packedAt s4K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/309+packedAt s4K5 (21627+(h % 309)*10) 10) % 801)
  | 4 => 2*((h/267+packedAt s4K4 (29678+(h % 267)*10) 10) % 781)
  | 3 => 2*((h/60+packedAt s4K3 (2744+(h % 60)*6) 6) % 56)
  | 2 => 2*((h/2+packedAt s4K2 (360+(h % 2)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe1fffff07fffff81e1ffc3fffc3ffffc38f1ff
  | 1 => 0xfe07e1ff83ff8ffe01e1fc783fc7f07e274e73
  | 2 => 0xfff801fffc1ff0fffe01ff803ff87f83c78f9c
  | 3 => 0x1ffffe000fffffe00003fff8003f80fe0
  | 5 => 0xfffffe00000000ffffffffffc0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x202080110001000020220088880892100810a5
  | 1 => 0x44915322194a189610d0e4511645216a234652
  | 2 => 0x8852444428d4012ac201490224904d08c58b18
  | 3 => 0x1d65998952872acd75742044bb260633780de0
  | 5 => 0x1186110e63184cf19999b26702040843b6e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfaeafaeae8a8e8a8faeafaeae8a8e8a8faeafaeae8a8e8a8faeafaeae8a8e8a8faeafaeae8a8e8a8faeafaeae8a8e8a8faeafaeae8a8e8a8faeafaeae8a8e8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_39357
namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x440000020000021c10c00000c0055044057202fe30ff31fd10fd32fc31fd30fd41dd30ff40fc40ff42fc32ff32df30fc21fd20fc20fe21ff30ff20fc43fe32fe42fe40fd21fc10fd42ff43fe10ff10fe43fc30fd43ff21fc41fe41ff41fe31fc42fd40fe20fd31
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8417f54886faa910df95121ef992617c540c6faa8885fd4810bf298437e50d0efca198df94f10af29861de434c37886a0dfd4f10bf286437e548c6fea818f74c832beaa021de214c2fca520dfd4d41be2a6217e500cafaa5a0f7d0130be29e41f651103de65195f94441bea9e217e510c398a4985fd4c21be28a65bd42502fea790df94a43be282657e508c6f8a5087710130bea9e837e5210bba81985f54b31be282877d5290fb8a2987d54743bf29e85f741506fca02077d0b30ee292617d5390bec8310efd0740efa1e617f5050fec8220df94a10ea28a61df300c3d8a4985f55131bf2a0837e544437a82a05f94332f721243ee52102fca010df94342bf2a643ed42c82fea2997748730bfa8a85de524c37c87a0df54e40ee98e617d52c437e8621df54432efa9a857f54c87ec20885f15230bf29485ed320cbf621085f14931bfaa2637e53486faa1994f95232ef98e61df300437ca9195f95042de21e85ef20882fca4195f54231bfa9a43bf41107ec8218fec4110bea8881bf42507bca7107e90040f799265ef21482faa3a1df94c30fb20e217551d0efaa998db54b43bfaa02175518ca7aa918dd54440efa18637c54487bea690df94030be2a043f4514c3bc63985b54840be2a4213d54086faa5205f14f10bfa8a417f525027ca8087d88510bea9c837e51082fea6885794e20bea96877e52086f8a7085f94743fda0481df54cc2eca2107b48720ef28a6176518cbb88618df94843bfa9c417c53086fca4106fd0940ee21c657e51882bea6a15b94841beaa4617c51483b884987790930be29287f7314c6f8a918df54840bf296837d540c2fca218df94220bf28485bf4390fbaa3987794c40be292217e5190af8a9987e500409faa2615f53486fca8107d94442bf2a0437d53d0abca6085f54f40bfa94217d54482fca4187d50441f721241dd53103dca420dfd5331fd98461bd548c7be82987dc8521ef98241dc5350afca310fe4c030bfaa6657e548837ca8085f15120bf29c41df504c2fca5986f10c40b7290817e51907ea83885f94042ef10e617e53907b8a3985f54d21bf28c817d54c8778a8986f90e40bea94837d54083de6590df14540be29a81f5518cbda4210f74c431bf28e417c52c43be61087b90832f290843df32cc2faa021f70cb30fb98c637f5050bf420085b94810deaa043f5410c7bc60987d90521f619643df438cafea6a17b90b32bf29c21be4250bbe608877cc431fa908437d50d06faa819774c320fc88021de53043f680a07d90731ae29a857e54cc3eca3195fd5030bf29e837e53c83be42985f95131dfa04817e53042fea4a1fd54442bf29663dd43cc2fca7205f94410fb90c437e518c6faa9985f54632ae29a437c53883ba65987710330bf290213d548cafca5185b54810bfaa461df30c82faa620f790f30
  | 1 => 0xe42cc3ba84985f54331be2a2637e530c6baa7087bcc820bfa92617f504cafca1085f15020be2a4437c544c3be6519778c531dfaa261dd53082fca710dfd4540bea86437d5190afea8107710d30efa1a87dc430cbda84905f95030dfa1681ed42c867ca918df94442bea9061f621086baa608774c220bb288857d51c837ca810df55332f6a1065bd42d06fea498cf55010bea8443ee4210af8a090df54243ef19265dd53882daa518f790c43ee216617e518c2fca790fb94a31df2a0417d5210fdc40906f50842bea8483bc43d07f460185f94c42eea18875d538c2faa6905f54a20f619441dd300c3e863087b90b21fb98a43ee320cbeaa2105794c20bea94217c53082faa1a1dfd5130fd10041df308c2fca018d754e20bfa9c217c53507ba80985fd4d20bfaa621ed52106fca620f748530efa1865bd54083b6a0985f54a31efa1a617d51842faa3185f94f40bfaa241ed42ccbbe43985fd4b10bea9221ee42c83baa6086f55010ef2a2617d53842fca3a17b48520bea8885be41506faa3985f94341bf29081d7514c37e82a07d0c621efa1261bf4290aeaa2215f54031ee98a61df514c2fca5205fd4543beaa2657d53042faa7905f54c42beaa6417d50d0bb86518fb94b43ef29c817f54c83be62985f14941faa0a21dd30042f8a4a05f14131bea9c65bf42d06f8a0a0f3d4930bea9c41dd544c2fca6195fd4d40ef20e617f54842fca008778c530bea9c617d54842fca5195f94c20fd902415d53083bc81986f95231bf28865df4390efea9987b54a31bea9a21dc54cc3b843986fd0842eea9c817e52443bea4987794b30bea88617c53443be60105f54242efaa261dd53843b883987b0c921faa0c437e52d03bca7087bc8720eea92617c53042fea9195f15331af298813e54086fea810df55243bf28843de32cc2f8a6906f90d43fba8a616c524c2baa6207bcc921b7296877e54c83bea6a0db54841bf298877d54c42faa3a04f95020fba0c83be405037a8220d7d4d41dfa0081ee21486fca1205f15220eea1a61be431037887205f55031bea8e65de54cc2fca221df54b40fa90a217e52d0efaa5186d50441fd98261ef524c2fea6105f14930eea0e617d50087ee63085d14530f6a10857c514c3b863985f54232ee19261dd30483be61885f15110bfa82437e544cafaa420df54c20fa880217e54102eaa2105f94e429eaa0417d50106faa810df94d20f7908435e53902faa0215f54420f7a14857c53c87f240105f95210bea96617c5150afca1197794730ee99261bd42507ba85985f54443ef19063dd54cc2faa919774c210de21a857c540cbee6310f715130ef98441dd514c2faa890df54831bf29a21dc43cc3de40107b54b43bfa9e417f53886fca6205f15132aea9c817d53102faa3105f15321ee98221df320caf8a2a1dfd4910fb28
  | 2 => 0x200ea88000ce000041300004816098e40006000000008000100645006000000402690032008d65e044678000d06c9980048800008860b8020203c00200010423505a0f000000009a0580600204006800e21d8940181a0195c57aac0983000096018d8010241c0160001200a7c0a016000000190a06000000885300000000048001704200298000101c1827316c01010108220500c0800a0016625814030e8068a4000060e8020000e060000e80403072008000e8000d8320218216864260044380a378160ebf0038020b89a0100c028000001200004002560503016800050181c0121581800020100b40b004060080000a010322087a0081611174d08321481c0180e088012daf40184a39002038e01101224ad000a9e000004584a010060a81e251e408000029740101401036098120d8020291000804058000280200002000480b84e9adf15010f6a12433c544c2fca319770c530b729463bd4310efca3985f94043df21e857d500cafea9105f55242bb288817e5190f7c86a15f95331fb28e877f540caf8a710f790530dfa0c837d52042faa9105f14142bf288817f50506fca721fd4c431f729021dc214c2f8a9195f55241ee29a437e50083b882987d48710ee98041df41cc3de84a1778ca31f619041df40cc37c86a0dfd4131fa18a437c54c82fca121df94732dea16817e548cafea918f710e31f6900417e50887bea5985f94241fa188219f544c2f8a6a15f54640bea9843bd548cafaa3a17dc4010bf2a2417e548c2faa321f7d4730f6a90215c53506f8a690f74c310bea9443de404c2fca420fd88710bfaa2437e548877a83a05f94230bb28e877d538c77a80205f95332d6a10857e520c7bca6105f55240f790c437e52c43be8718fdcc410bf2a0637c540c3ea8290df14810bfaa265dc53506eea2987ec8220bfa98217e5410efca020fb54840bfaa2215e53843eaa2205f55130ee190637d53c86faa918df94a31fb18863dd414c2faa710df95032ee296616f524c2fca8085f95310ef98c637e51d03baa5987d50731ce2a261ef32882fea4a0fdc4210bfa8a617c54ccafca8987d90510ef19261d
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2518cb55530c6109d584525032e5454810d314d42486cd6210330d994951d0f2f54d4930cb153524c31e5494c10cd553310426e6214810f1d4b514c36653484219dd95100438c6350842c719153882d56195330c7553300836452d4530cd551518cb3554cc631c7d4c435065c6550d30cd551100425e63d5210cb5095010b4e65149308f994544c27661951309b58a544cad561103309b98b540434e53548409d584548835561d4d21cb151420cb37425444297d95320cad561d0c31cb149425071454145309e980540c65d63940219b588540425c65485309d584540ca5e63942429d98753c825d63d5020b5587434c23e6414520b398a54cc2d6618cb308f990524431c5494930e5153514c2d960951309798e50042ce62d0f30d398b53507a652504418f590530825f65507309d984540c25d63951219dd85534432d54cc820ae58043102766114142d954b318c66e621503097994534863e64d4d21d594d511025c6354b409798f54c865f6354b109b189539027561d4c209d195414871f6454e20c7d9153843c52108530a7191514c27665cc5219718d540869e648c530cb54941107c75214530d994a51102da60109309bd9520082d960949308fd95411071c5414930d994a51d0f676548421d9148514c31d5390c40d354e521025e6394241b658054cc23f6454d10d954951102ad62d0e439e980530871d5454c1097580534874c6254e10cd151418865e65d0d30b5185544c31d64d4d21d5185538823d6494b309b98854442d5618cb30b3d89544c38d4210930e9549411067661152209b588505072e5494a319758c528425e6394042c7150324c3664254442d358b534875651cc0209798e50d0a5f654c020d558753506ce6295130d5d0c514c2ce628c7309b98b53507345450521a759021cc31d54cc010d3d4c32486e9600c820e955121086cd62101309d58654cca75650c4108f990530436752d4530cd151414425d60d4d419719542cc25c6550730c7551300825d60d4d4297d8d54c83945414530ab592320cad661d0d30b358b43cc2766114940b3189544c2cd6294530cb90d521027561951319ed81544863d6494b31cd5494110735540c410c9551210872e5454a31c7951300827a60150329b588544423e6414b10e5d53514c27661153208f592520ca5f65509309758c52043355488421d9949511023e64944319b98a51cc23e64947309dd8553482cd628c730a759231cc2e462505219758e5090a3e64d4f21b598442cc25d6314121c7d50434c25d6594c10c7951530434d62d4d42d9cc9518ca5d63d4a108f19153882d76350431d314b504c25f63547409e580530867661d4d42cd95251082b5648c43197594430c6d76154930c95095110ba54294442d354c328823e6415020c714d425066d62150319d58453082d56110130
  | 1 => 0xc29e648ca31b398a51cc25d6394241b658352cc23d64d4810cb553210874d53548409b588515025d6014d42c7550438c67765504418f59050486d56194930d9549411074c53909219e181544869d6494b30b6d81544c23c6454d20d5d8553882766115020d5147314c32c54509209b988548425e6315010cb10d521031c5494530c7152314c2766115230b9185424863f6454d209d5845050a5f6550c43d954520082db6054530d310e528c69e65151309b988540865f63550219bd95320cb5451d41308f99053087c76348421abd954210b555354440d90c9510827661d4c20d5d8d5110b57530c5219d98654ccad661101309b189534427465485109b195424867561153209798c530823f65508429bd89534829e6494730cd551210865d6014d41d3d0c524c31c5490d30a799231cc34d520ca319d986544ca796015032d554d510829d648cb308f990504865c6550930b658351cc27b65480208f590530425d63d522097d95310c66e6215020ad185425074e524c0109b98850507954110530f114b514c32d52d0441b5986544c2d761551309d584544825c63553208f19153843545390521e3153524c32c54149309dd95310c6756195130b558743cc25f6548530add9541107546154e40d310c524c34d524c010d58c8514c29f6454530cd5095110acd62d0d30cd10d511026d6215210f4d47504c23e6494b31b398b438c66e62951319798e50c863e649483297d8d544866d62951308f59251cc23e64d4c10cb55252042756115232d3950524c25e63d5221d9149214439b54d41309758e50106d463506219718d54c42776154e40b5986524c2b66190d419798e50886d66514530d594d510826f6548421c755253043c521087309b58a51cc23f64549109798e544878c43508328f992544c23d6414910b3d8d420ca3e6494b30cb15142486d661953309798c548427561d4f209758e50d0acd62953309d984548ca5c635472097d9521cc32d54548109d98454482d661d0e329ed95300c32e5450b3297d8d544cb4f520c930cdd95411065e63d52209ed95401038d4210b30cb553328cb976350441b598652cc36452487109d18554483c452145309b98b530426d62d4c10b6582514c2776154e20cb553200827661150329bd89544425d63152108f19152442796015031c7994544c27761551309798c504866d6214c109798c5050b2c5450b21d510e518ca5e63141418f59353086766115010f4147504c2756194a439718d544871d63151309b58b540431e548ca31e3d53524c2d661d0f309b596520432f5414930b558652cc2cd62947309d98652cc33554c4010a7592324c23f6550c439758e50d07c46348421d5150514c32e5494810d3d89539025f65505309718d51d02b56490441c795330082776548421b5986514c25e6314c10cd55
  | 2 => 0x61109309d19541443a54254442a7592514c2776155120b398a514c2cd628c5309798e534863e64d4f10b518d414866e6214c109798e501071d63d51309d9865290e6d6590832c7552530826d62d5231d394e521029e648cb309b588548c74c5294530d9549100431e5494c208f593534865d6054c10b358841cc337541453097583534865e6314a10b6980414c3c852d41309d98753086e5618c832cd951510826f6254d109758c540429e6494b30d314a314c32d5250040cb94d4210b365454632d358b535066e6215231c7191538425c6355120c7153504c23e64d4e21cd145415026d62152309b18953843673254420c7951300435743946329b98a54cc6756115230cd551510825f654c030f24c1200832c5250940d3189539031e540ca31c3150524c25e63d5010c754c439023e64d4f20bc580310435561d4d42a7d91524c23d64d4e21a7592524c2b561d0c439718d544438f6350842cd90d511023d6414b10d354e520431f6355231d694d300c25c654873097d8d54c42d66110330d3d89538831c5414530c7152324c2d661d0c32d954b100426e62d4c21c718d540879463504419b58b535069e64085309bd8953902766114810d314b324c2cc6350b219718d5110b555394420d354d520426d629464397d8d544823d65950219d587540823d6595010c7993534865d6315220cb551528c65f6355131a7992320c6ce6210530d9145214825f6550b308f99251cca5f6355110d3150524c32c5450b20b6580414c2756195132d394b300425e63d4810b3189514c365520c410b658354cc29c6454930a718d425079541107309758f54c86d56195130d594e511026e6215031b3988404c2db6054930b6580424c26e6215310c9549411071c540c530d5545300823d64944319ed95100431f6355021d354b300425e63d4a10b6980214c25e63d5020c7d53504c29c6350b419798c52042ce65149309d18553482766115021e9509414865d6394042b6580214c23d64d4f109798e500865d63d52109798c540834c6254c209b594320827661d5020b5584424c35653944209798f540c23d64d4c20d954a51103cb52d4130cd952518ca3e64d4c219b997324878c54149309b58a54cc75751d4130b358a544c3655254743d554f310426f6254e109b98b53c433454504319758c5408336535044197994404c23e64150218fd95401025d6314141d318d521065d63141428f5935304394435043197597300429e648c930f10c8314863e6414c209b58a544c65d65cc020cb55121087576154e10d914d210863e6415010e995121087445214530ab98a4350a5f6354720d3d0e528c76552947439759653082796584010e3d50524c2756115030b3588414c25e63152209758f54043566514530d5185530425f654c01097996404c23d64d4f20a7992544
  | 3 => 0x406018070040f42c0306004084080000d0000015001174001c80300cd902000504000406b580640c800000190bc050100139405008120040604006000230001501402124030000401800b40000ac4a0b81000001018a1600000440605850000f1048469540a0481100c404700700019014041b8100e40c05404030021041a004080a40400c0a00c00080080000204c7607c020805813804008550a8000000908c1d138010c95e000022a24f5584c030040000a0b0020085f00c894b0023f8010040000c0e00085078020000d01403040000082c0500d02800000001fc1503c8e004ad164291e0040200000c0b0382c074000080706c0f01c240043d01c0006974070287dc6b0019f0000202c001f009004050500c0000c04801148000144200d7454c1f73800018021180148c000000726c2e10c0900c3504c1803c00054040802903c038f1915344354535052197d8d52442cd62d0c329798e50082ce62d0c318f99352043555394440cd552510826e6294643cd153514c26e6215230cb54b40102e5628c4319b988515023d64d4f21d9d48514c2ce628c530b398b434c23d6414a10d3d8d52107576154e40d3148514c2d6618c930c795330042e662cc521b958a210865c6354910ad5874390e766195330a7590214c25f6054c1097195414c3655290441d9d51210879854d41309758e50c874e53948109b58a54cc3975414530d9551210871f5310d42d954720082cf6254530cd54740102746155130cd95141cc65e6315030ab5924210b6552cc4109b988540435652145309d987548cb4f6254e109bd954210a5f6354841d394d52043652154021b5586324c26e6295130cbd954210b2d5448020b5586320c74c520c530b658051cc23e6414810cd505501069d64947309bd89544c3345414530d59875350b994010130f44c1100423d64145209d5875350a5c6354b10a7992514c356514c0209b58b53c42e765484219b588540c2ce621073097d8d52d027565904319758e508866c65509209758e50043544314530c7951530831d5410e328fd9153882756194b309b189544c27561150208f59654083545214530c7d8d548ca7561d52329798e50d07654254442d5547300826e62d5231a7992524c2766114c20b9987324865d6510c32cb550320831d544c010cdd53514c35654145309d185538832d42544429758e500826c6255110d5d44314c3543214530cb552528c63e6414a10cd15141c42d96014b308f59251cca746154e40d354f320834f52d4130b398a524c2d56110b309758f520423f6454e10c7551530823e64d4c20c714f425067561953309758f54886ce62103309b58854c42ad62d0c43b318d42487546354442cd545401023d6414c219b98a54cc29d648c53097d8d5110a3d6414810a799021cc2d461549309718d52106d6
  | 4 => 0x51c0702e409f8d2058020280202c01038180184a01c040
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xc6330800e800000680040c08a0200080060860262000a30000001080c100200028200001000000003164c18028280050230070763549411068b3a46428a61831526294530a4ae32a2859945475584424c30a320c2a9c4183152628c530d0a84b088498514735494110652b94c321a83495c45450832c1cc8294629852970151420cb822a0a5a8a61495d05248510e82a4982200854672948514c2873a4a829261495c45450920e08e6a12a221525741452148330a92c018821495d05248710a18eaa10849868962500404c2a33968628a618318d4254442e08e6aa24210d297010d5210382aa0c690843c1d505214530a28eaa088298704635095110b42b128220e61b04856008530c52a8b00641068942580424c342b128220a61c25513048020a2ce9290a29852572151410c6b0b80a690843295d262cc521e08a9a90a29870454148514c20e3aac810a61495ca5450731a4ae22a28590644621855390348a0ac020a6185152618c930d08c6a128290c4c75588414c342b224210e61459d25414530a48eaa128290e8564484214c2a239aa890843495c85450510a4ae428a82a053170151410c692b88a4a1281511d52108530e08a6a128290f41514c12008348b0a8020261295d261cc921e0ee6a928220d61700c95108298b8086a8881c45513044010a8ce52a0a29854671950524c382aa6c690843295c66290d42c1cc8294a298631545803104292baca890843495c85450710e0ec6a12a22161454986524c38231aa4a0883c1dcd5448421c48caa128290e854258442cc306320c4a9c21c11cd5250441e0ee6a12a22154671d0c524c292ba0a690843611cd4250521
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x7083500000a04855894110530a0485509611093090787553634842190687d8d4254442c04755912108530a0686dcd5250441a0686dcd4254442c04755096110930a0485591210853090687d8d5250441c04755894110530a0686dcd5448421
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 5 => 2*((h/261+packedAt s5K5 (20007+(h % 261)*10) 10) % 741)
  | 4 => 2*((h/278+packedAt s5K4 (30172+(h % 278)*10) 10) % 794)
  | 3 => 2*((h/58+packedAt s5K3 (4459+(h % 58)*7) 7) % 91)
  | 2 => 2*((h/11+packedAt s5K2 (720+(h % 11)*4) 4) % 12)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffffe0ffffff81e1e1fffffc3ffffc07f1ff
  | 1 => 0x3c0fc3ff07ff0ffe01fe38783fc7f07e394e73
  | 2 => 0x3ff003fff83ff0fffe003f803ff8ff83c18f9c
  | 3 => 0xc00003ffffc000ffffffc0003fff0003fe0fe0
  | 4 => 0xfffffc00000000ffffffffffc0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x44100220002000020204088880912100210a5
  | 1 => 0x8922a6443294989610d21c511642a16a194652
  | 2 => 0x10a4aa8851a889aad2102d422690cd0ac18b18
  | 3 => 0x82cb1112a50e224d65648004b92406316e0de0
  | 4 => 0x230c221cc630ccf19999366702008843b5e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8feaae8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_39357
namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x80141580142000b007042012b600031004dcc00c00007c2185027fd5009fd43007f4c409fd4200ffc800bfd5300ff08005fc32027fd0403fd1000ff8c007fc4300ff84003fc50027f10403fc4001ff94c09fc5402ff94403fd3000ff88009fe5400ff54003dd30017f08409ff4302ff54801fe21017f90807fe4300ffd4003fd4000ffc4001fd3200ff04003fc30027f55009fd4102ffd4c03fe4002ff14405ff21027f90405fc4202ffd4407fc3100ff94007ff32027fd0803ff30017f94803fd20007f48405fc52007f8c40bff5202ff54407fc5301ffcc403df30017f8c803ff40
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2c420bff54221017fc411081aff62484057fb126406bf18a31037fc631085ffe604c805fe10a6406f7cc63104fda8490827ff414842b7eb246202bf98a310a7fca51880ffd434c80dff3146219ff19532057fea29080bff204c80dfe3146202ff5492109ffe8118803fd624c41dffa9c4212ff9953101ffc649882fff308840def18a620affd95210cffaca99006fe6048423ff3226203ff4c231037fc8290827ff5448405fe902420dffd0e21035fec11884fdd308c40fff2824209bfd9121055faca9080bdc324c805ff9044205bf99521037fca29883ffe204c4037e3044200ff98532017fc849900ffc434c40dfeb044206ff58a3103ffac090803dc634840d7fb244215ffd0a310b7fea51880aff614841bfea1c4203ff54e31037fe209880fff314c423ffaa26213ff10231037fc2110803fd6348413fea0a4203f7cc131097f8ca9880ffe438c40dfe18c4218bf591320cff8a29903ffc504c42bfe2a46217ffd4132005fac51880bfc324c821ff312620aff1952101dfcc710806fc604c411fe31a4206ff146210bffac09903ffe404c40dfeb246214ff14a31017fc8510827fe544840ffa8824206ff0423101ff8609901fff6048407ff29c620fffd8131025fcc890823ff314840dff90c6203bf98d2101ff8a71881bfc418840d7e3246218ff10532017fe849901fed204840dffb1c4206ff19231037fe831881ffd4048401ffb126206fd0c63103ff8a09085ffd404c8097e3224202ff8c921017f8651080bfd3288425feb2a6215ff50a3105ffea11083efd604c407ff1826212ff54531047f8869081bff1048423feb226206bf18e21017f8851080bff324c805ff2926417ffd01320bfba609900fff438c407ff21a6402ff94a2101ffea69881bf7108842bfeaa46202fdc8521037fac11881bfc214c4077eb1c620abfd9521017fe429903ffd504c405f61926403ffd0d310bffa2099002fd638840dfe3046204bf1913107ffcc09881bfe314c405fea144206ffd463107ff8409880ffe328c40fff2024202ffcca2102dfcca99047ff644c40d7e30a640eff54e21057faa29081bfe514840fff1824207bfd8121017fea49900ffd304c813ffa1a420bffd0221015fac51081bfc214842ffe2026400bf58d2101fee629881bfe418c405ff1024206f70c5310b7faa51881ffc6048405fe2926407ff5412109ffa411881efd6048407ff9826204bf9922109ffca118863fd644c80dfe884420bf74c22103fbe6090827fd64484057e3126206ff8c52109ff8a11881bf4218840dfe3044203ff54d320affca91880edc6348405ffa944203fbcc9320c7f8a89900bfc204842ffe0826403ff50d3100df8c118806fc604c827fea04620affd4d21037fa8318837fc5488417fe2044203ff14d32037f86298833fe438840dffb24420fff84131
  | 1 => 0x3ff634841d7eb2c420dff55221087f8849880ffc438c42bffaa46213ff88231017fc8490863ff414c833ff32a6406bf19221017faa49901bfc4148405ff9024206ff9963104dfac89080bfc324840dfe98c420dffd52210c7fa829904ffe408c405fe9026402ff4c921037f8829881bfe518c42fff2826406bfd962107dfec098863fe414c80dff20c4203f7cc23102df8ca99012fc644c807ff9926212bf59531015fcc49880bff324840dffa8c4204bf9913209ffe411884bff654c40fffa824202ff1092103ffcc090847fc544c40dfea8c620fffd013100dfcc11881bef2188401feb0a6406ff982310bff8c09901bff418840dfea0c4206bf19621037f8431880bfd52884037e3024207fdc412107fba609881bfe214840d7fb044200bfd8532017fa4110846ff644c40dff3244218ffd913205ffca11080bde324c81ffe8826206bfd8d31097baa69881bfc658c4037f302640aff99521097fea49882bfd654842ffe2826418ff95132035f8cb1885afd658c4177eb044202ff94921037facb18847fd424c427fe1046202fb9092101ff8611880bf7218840fee9824207ffd012101ffea71880bfe324c805fa10a420fff1013101fbca698867ff514c81ffe3026211ffd093101ffc869881bfc6388405f79024211ffd053101ff8869900fff308c405ffa124203fdcc631025fcc91884efd608c40d7f30c6203ff0c13103ffa209081bfe648c41ffea026210ff14931037f86318802ff624c41bff2a44208ff90d21087fe429880bfd4248417fa8844202ffd49210bffe209900ffd534c42f7eb026400ff18532037f82098827ff64484016fb1a4218ff9913201ffca69880ffd438c40ffe2024206ff5922101ff8651880ffc534c40dff98c4207ff4c121037fc211881bff6588407ee1946218ff19132017fe429080ffe304c8017fb1a4206ff1922105ff8a11080ff4314c40df710a4207ff0c1210bffc809901bfe6588405ff1944219ff9453208ffaa89880bfc5248427fea84620cff10e2107ffac098853fe428c429fe2146206ffc4221037fca310867fd514c813fe2a24206bfd8e21057faa690843fc624c40dfe0824206bfd9231037fec51881bfe608840dffb246208ff94d21037f8831880bfe204c801ffb0a6408ff14d2108ffa829885ffd504c807ef9826403ff4ca31017c8429080fff304c80dfea8c4206ff1463108ffca898823fe6348431ffaa26403ffd4d3205ffc811084bff514c417ff1844209ff19121017f8411080bfc204c827ffa846203ff0c532037fec11880ffe534c813ff3224209ff55121037fc829885ffe104c825fea926203ffcca31037fa211881bfc658842fffb02640fff481310cdfeca9901bff6088423fe322620fff94131017f8849901bfc2188401fe98a4203ffd0d32095feca9882fdf308840dfeb
  | 2 => 0x8c3002008100a1a00000ae06070035222058e44800038880a00008a80204128d044680b01854002903027bf000940a14089408a00078440a040604c0006068140e06060d814082617c060317800183f01b680e0007a3404000480005057f010020e1886c48001b908005b018506a2a042c40a6306804005d0000006070517c76001c3d4161000854002b0e80012002982c0800078300021029ccf21111804c60b000b13e0000888000700034020102818cc0f01004684908bb81004240082207cc014cc01000cc164001ffc6118812fe644c4237eb226203bfd853107ffe409882ffd3088405fe2944205bf1952103ffe6090862ff644c829ef194620bff0c22102dfcca98816fe6588405fea126405bf99631017fe851080efc634840fff0824206ff98e21067fca710843fe424c40dff98c6219bf5953204ffa869081bff658c40dff90c4206ff145210c7faa899003df634840dff8846206ff0422101ffe6299006fe608840d7f30c4206bfd963105ffa811081bfc314841b7eb244203ff4c131067f8a71081bec2148407fe1926203ff4c9310bdfec099016fc654c40dfe28a6210ff94931015fec699067ff654c81fffa826206ff58e2100dfcc09880
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe764c5210a6de52d8d21046de7618d2101cde76d8d21006dc6018d21045df7018d21036df7358e21005dd70d8d21004ff70d8532006dc70d8d210efcc21d8d21006dc74d8d210a6dd20d8d21004fd7558e21006df75d8d21004fd70d89310eedf72d8d210a6dc3258a31006df6018d210eedc41d8d21006dc64d8d21034fd7158a310a7c421d8d21006dd30d8d210a6de3258a3102cfe75d8d21004fd7058d21004ff7458a31007d71018d21086ee62d8931006dc40d8d210eedc21d8d21086ee42d8931024fc74d8532004fd7458e21046dc53d8d21036dc3158e21006dd75d8d21066ed32d8931014fe76d8931004ff7458e21004fd75d8931034fe71d8931004ff74d89310a6df21d8d21006dd3058e21036ee2158a310a6dd72d8d210e4ff7158d21034ff72d8d210d7d42118d21006dd50d8d21006df65d8d21006df50d8d21046ed3258a31034fc7158e21006df70d8d21046de43d8d210eedf10d8d21006dd74d8d21084ff7258d21006dd10d8d21004fd7058a31014fc764c5210a6ee4258a310a6df32d8d210d7d72118d21004ff7558e21006de6418d21087e42158d21024fe74d8532004ff7558d21006f76198532006df7358d21024fc74d8931034fd72d8d210a6dc42d8d21006df6418d210eede71d8d21086df3258e21006dd65d8d21036f66118532006ed4258a310a7cf20d8d210a6dc52d8d210dedf6218d210eede41d8d21006dd60d8d21006de65d8d2101edc634c521006df53d8d21046df30d8d210f6f631d8532006de50d8d21004fd74d8d21024fe7458d21007d51018d2100cfe70d8931006de10d8d21015ec724c521014fc73d893100cfc70d8d21007cd20d8d21006dd41d8d21004ff70d8d210e6f621d8532004fd75d8d2101cfd71d8931004ff7558a3100cfc7058d21004fd7458d21036ef7258a31006ed2058a31024fe7458a310a6ee3258a310a4de7618d21034ff7158a3101cfe76d8d21005ef724c521006df51d8d210a6ef2058a3100cfc7058a3102cfe75d8931024fe74d8d21084fd764c521066df3058e21034fe71d8d21006dc60d8d21066dc4358e21004ff70d8931086ee52d89310a6df52d8d21024fe7458e21034fe7158e21086dd3258e2100cfe70d8532006df74d8d21006dc75d8d21006f56118532004fd70d8d21006de70d8d210d7ce4218d210eede51d8d21066df30d89310dfce2118d2102cfe75d8532006dd30d8931006df64d8d21006ed42d8931006df60d8d210eedf63185320a6de20d8d210a7d721d8d21005df70d8d21006de6018d2100cfc70d8532006dd54d8d21034fc7158a31007cd4218d21006dd6418d210d5de76d8d21004ff75d8d210e5f77158d21006de40d8d21004fd74d89310eedc51d8d21006dd3058a31036ec2158a31046df3058a310a6df42d8d210a7d421d8d21
  | 1 => 0xcd290000609001e03211260848c0100268350c0588800000d0905e3102969d8120001c0000008003e087495c64080014402040c86800100100000000200884030680802010185404036a804005e228eca049630000e0206851b00b00c30ce01008200a38478b0000300000f2000383484070004882010310c02440688c240005004002f0d0940003004ff75d853202cfc75d8d21046dc43d8d21006df43d8d2100cfc7058e2102cfe7558e21086ef21d89310a6dc72d8d21005dd7018d21004ff74d8d210a7e421d8d21004ff74d853200cfe70d8d21007d710d8d21007d510d8d210a6dd52d8d210a6dd71d8d21037e4214c52101cfd72d85320f6df30d8532046de63d8d2102cfc7558d210a6df71d8d210f5f77158931004ff7058a31006de30d8d210efce21d8d210eede21d8d210a6dd32d8d21014fc72d8d21004ff75d89310a6de42d8d21086ec625893100cfc70d8931004df70d8d210d6df6118d21006df6518d21006df54d8d210a6ec5258a310eedc71d8d21006df634c521006dd3058d21034fe76d8532006de64d8d21024fc7458e21034fe7158a3100cfe7058d21006dc54d8d210a6dd42d8d21006dd53d8d21004fd7558a31006ef7258d210eedc10d8d21006de54d8d21004ff7058d21006ed52d8931004fd75d8532004ff7058e21004fd7458a31006dd30d8532006dc6418d21004ff7458d21006df4358e210a6dc20d8d21014fd71d8d2102cfc7558e21034fc71d8931006dc6518d210a4ff7358d2100cfe7058a31004dd70d8d21006de74d8d21034fc71d8d210a6de72d8d21034fd7158e21036de3158e210d7c42118d2102cfc75d8931006dd51d8d21034ff7158e21006dd70d8d21024fc7458a31006dd6518d21006dd5358e21024fe74d893102cfe7558d210a7ce42d8d21006dc50d8d2102cfc75d8532046dc30d8d2100cfe7058e210d7cf2018d21006dd64d8d210dfcc2118d21004fd74d8532086ee32d8931046dc6358d21046de53d8d21014fd73d8532006dd6018d21004fd70d8532024fc7458d21006dc65d8d21034fd73d8931046df3058d21004fd7558d21007cd42d8d21006ee20d8931014fe72d8d21007cd2018d21006de6518d21006dd43d8d21006de60d8d21024fc74d8d21004fd7058e2101cff764c521006dd40d8d210a6df20d8d210a5de7618d21006ef5258a31006f77158d21086ec20d8931006de75d8d2102cfe7558a31006df41d8d21066de5358e21006df40d8d210eedf6398532046df31d8d2102cfc7558a31014f
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa5c8558063484295ab02386c690802a761050d8d210046f43ca1b1a4200c5d75d4f6348409958e8a12c5188023761e50d8d210046fc1ae0b1a4200dc421dc3634840153d09baec6908023761e6518d210052ec2cc9b1a4200acd8299463484011ef0eb08c29900237e1d6518d210046ec38c031a42018dc874c1634840117b09baec69081a3b21d4258a310052ec28c1b1a42008bf845c1634840d1e902baac710803365c36018d210054f420c031a421dacc8650b63484011bf0fb00c69080297a146018d2100566c14c831a4200dc4215c363484091df0ea16c498803365c06018d210046f43c81b1a4200a5d851c3634840917d09baec690876b5a0470d8d210052fc2ac031a4214ace821c3634840d1b90ea9ac710802a7a1050d8d2101c6f438c031a4200a9d8499463484355a90c880c69080237e0d7558d210ed6b40881b1a4214ccc72d8d314840153d09a8ec69086ef12054218d210ed66c16ebb1a42018ee86dc9314840153b08306c690852b3a0840d8d210052f42cc831a4200acd83d49628c43599ceca16c69080237a1c50d8d210ed66c10e1b1a4200a9f84580634840159f04b00c69080237e1d6418d210046ec3cc031a4200cdb805c36348401b8842b80c690802a721160d8d210074632285b1a4204cae7450b624c4014bd0a386c690802b560450d8d2100c6e43a60b1c4200cdb704c1638840153b09a8ec69086eb32192018d2100c6fc3a61b1a421dad783584614c82978904886c6908023761c50d8d2103476c16ebb1a4200a5e859d363484011bb0f320c690802a7a1265d8d210245e422e0b1a4200a5d85d076348401c3ea92a6c6908021fe157058d210062eba8ebb1a421bbc482c4063484019b2e0986c690802b560440d8d2102c3e42ae0b1a4200a5d85180634843778902900c69081a37a1f4358e210054f420e1b1a4200a5d85990634840159b04206c69086ab3a086418d210043fc2ae0b1462008bf845c1638840153b0932ec690802b360850d8d210dd664328431a42018dc83dc1634840153d08306c6908029761674d8d21034f340ee498a421dbc48148363484295ab03baec6908122f2117058e210076430241b1a42018ec87481628c4051eb03baec690876f120b10d8d210046fc3ac031a42008ef825c1634843bd2882a0ec690876f120542d8d210052f428c1b1a4200a5c8558363484014bd0a206c690852b3a0b75d8d210054ec20c031a4214ad486443634840b0f90ab82c5188223761c60d8d210ed6b408a1b1a4200a5f8558363484019b6e0982c6908023761e10d8d210ed6b40eebb1a42008dd879c363484019b2e0306c69080297a1664d8d2101c6f41ee9b1262058df8754f6348401da0c0886c6908163be1d52d89310054fc22c1b1a4214ace821d363484014bd0ba0ec6908029761440d8d21
  | 1 => 0x1004131e00160000000e41431101030701000300021f1004000007000c11010e1703000505030a17033c2736017b00022d49020711000c050100030a011b002900250100030705000b0046f43881b1a421dacc8648363484291bd0f086c6908023761c40d8d2100747b228431a4200a9e849946348401d18c8a10c69081237e1d43d8d210d5e24122031a42008dd87903634840153b09baec690802a72116018d210ed66c10e9b1a4200a9d841c363484011bf06ba2c690852b3a0850d8d210066cb86c1b1a4200
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x15c1900857018d21006266117018063484015c19008770d8d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x2
  | 7 => 0xb09
  | 8 => 0xb0c
  | 9 => 0xb0d
  | 10 => 0xb0e
  | 11 => 0x1409
  | 12 => 0x140c
  | 13 => 0x140d
  | 14 => 0x140e
  | 15 => 0xb49
  | 16 => 0xb4b
  | 17 => 0xb4d
  | 18 => 0xb4e
  | 19 => 0x1449
  | 20 => 0x144b
  | 21 => 0x144d
  | 22 => 0x144e
  | 23 => 0xcc9
  | 24 => 0xccd
  | 25 => 0xcce
  | 26 => 0x24b
  | 27 => 0x3ca
  | 28 => 0x16cb
  | 29 => 0x15ca
  | 30 => 0x154c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 496
  | 6 => 301
  | 5 => 156
  | 4 => 3
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1612+(h % 34)*6) 6) % 62)
  | 7 => 2*((h/179+packedAt gbK7 (18352+(h % 179)*9) 9) % 496)
  | 6 => 2*((h/121+packedAt gbK6 (14448+(h % 121)*9) 9) % 301)
  | 5 => 2*((h/73+packedAt gbK5 (9204+(h % 73)*8) 8) % 156)
  | 4 => 2*((h/8+packedAt gbK4 (210+(h % 8)*2) 2) % 3)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fff03c0f03ffffff07fffff0910e3c07f1ff
  | 1 => 0xf8781fc00ffc383c0ff8ff03f36e89d2394e73
  | 2 => 0xff801ffff0003fc00fff0ffc0c70f1e3c18f9c
  | 3 => 0x1fffffffc0000ffff0000f80fe03fe0fe0
  | 4 => 0x1ffffffffffff00000000fff0003fff000
  | 5 => 0xffffe00000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8840040100404422011110400002040210a5
  | 1 => 0xa85092c086641a2845c8aa0ba12688d2194652
  | 2 => 0x3501155990202ea089520ce824703162c18b18
  | 3 => 0x804249ae2bca80012ea4c030cb80de016e0de0
  | 4 => 0x24041e33ccb33733c04008410efb0003b5e000
  | 5 => 0xc667800300c20402008080820fddedb8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_39357
namespace PEqualNP.Outside.L_meta_39357
open PEqualNP.Outside.L_meta_39357.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 29 := bs0_3_0
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
theorem bs0_4_384 : Interval s0Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 473 := (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384)))
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
theorem bs0_5_576 : Interval s0Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 632 := (concat (concat bs0_5_0 (concat bs0_5_96 bs0_5_192)) (concat (concat bs0_5_288 bs0_5_384) (concat bs0_5_480 bs0_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 40 := bs0_6_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 68 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 33 := block_range (n:=33) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 129 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 45 := bs3_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := bs4_3_0
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
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 (concat bs4_4_672 bs4_4_768))))
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
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 12 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 91 := bs5_3_0
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
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 794 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 741 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 bs5_5_672)))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 156 := (concat bgb_5_0 bgb_5_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 301 := (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 496 := (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := bgb_8_0
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
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8feeefaeafeaae8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_39357.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.or,[2,6]⟩,⟨.or,[4,5]⟩,⟨.or,[1,8]⟩,⟨.and,[1,5]⟩,⟨.or,[3,10]⟩,⟨.or,[2,9]⟩,⟨.and,[7,9]⟩,⟨.and,[11,13]⟩,⟨.or,[0,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_39357

open PEqualNP.Outside.L_meta_39357 in
theorem PEqualNP.Outside.L_meta_39357 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
