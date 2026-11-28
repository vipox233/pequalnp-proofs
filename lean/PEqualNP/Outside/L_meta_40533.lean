import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40533.Model
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


end PEqualNP.Outside.L_meta_40533.Model

namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 7, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40533

namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1003800716300081200d002000180005c1912428a85000850000000044000000000400444d50c80200089004c000020020e013d53102bea6884f553329f2a0615e53d067ea890dd946329eaa0637b504877080186750c31da28a873e50d0eb8a6906750e31cf29881e521086bea6904fd5130af2988178504867aa9986e14143ba28a413d54c827ca818cfd51109e2a2211d531027aa8185b54a31b7a92613f54482dca518cf550329f2a6413f548c27ca9995b94810ba28a876c52442bca7a14f55243bc2828775518cb5ea4a1db54810b6292613c54482baa7a14f95330cea1a619d438ca7aa998edd45439e2a24377514833ea6a1dd94420afa9a437551082eea2a1eb14943ba28a615d53d0678a9185bd4943bda82879d43cc376a0a1e754c409f2a0873e54cc6b8a690e750c32aea98813d539027ca0205714d109f28481ba501027ca9884f141439f2a0653d54c437081985dd4530b7a9221385050e78a8985b14943
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa15880014430100032f2b5214143a6181430c6986050c32a6181438ca986050e31c3189531021c6550d30c550c514c2996310330cc1445050f0f6254c40b818121087146154c40ccd445050f0d4314930c91485150f0d4394a31c550e518cb176154c40ca1485050e1d63953108758e54c83186054c40a618143cc2396510030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x400005811886154c40a10e0a1ca518d107050e518cb04310c0a9881841846054c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s0K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s0K4 (2457+(h % 58)*7) 7) % 91)
  | 3 => 2*((h/15+packedAt s0K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s0K2 (245+(h % 8)*3) 3) % 5)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffc07ffff03fffffffff01ffe3ffe3f
  | 2 => 0x3fff01fffff80ffffc0fff01ffffe07fcf1fc7
  | 3 => 0xc07ffe03fffff01ffff03ffe03ffff81f3e3f8
  | 4 => 0xff800003ffffffffffffc00003fffffffc03ff
  | 5 => 0xfffffffc0000001ffffffffffc000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x429114288471224500b2cb4a94b08aaa156e1b
  | 2 => 0x13224c514890e48b2c0555295956a24ccb16c5
  | 3 => 0xb244289a512241d3555026ac526ad30963a368
  | 4 => 0x2470b163a244891c9a6980c1838d1c71bc01b6
  | 5 => 0x3878c183c3870e1ee38e38f1e00e1861fed800
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40533
namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1300000130000000000000300850000bd42bf41df30de31dc31be40bc40bf42bd41dc32de32dd30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xc0008041425aa5a0cd547429aa888195410c698a4985514530a72946356518cb1a84194b54840
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/32+packedAt s1K4 (192+(h % 32)*4) 4) % 12)
  | 3 => 2*((h/10+packedAt s1K3 (270+(h % 10)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 3 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 4 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 2 => 0x48a65910ca5138658321a3445642a85a694652
  | 3 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 4 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40533
namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x850c108000000110500038f0021420021563c0380ff40fe31fe20fe41dd43de43fc42fc10ff32fe21ff41fd21ff21ff20fd41de31fd10fe10fc21dc31fc43ff30ff31fc41fd31fd40fe30fd43fc32fd32fc30fe32fe40fd42ff43fc31fc20fe43fd20fc40fe42ff10ff42fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x5140c00002822400b182c286004820038101834008582040c0801e0eb195005580020418a008ab8a690d7d4d41ea18e213e54082bca7084f550209f2a0655d5310ab8a6887514543ba28a655d538433a86a15754f42af28c875e53102baa6105d14520b6292215f548c6bca7a0f510431b6a96833d54c86baa7a057d4d21cf2a0635e53d0abaa790ddd4532cfaa287d4310867ea8905d54742af28c635c5150f3a86205dd4520ceaa06375518c2baa6206750f42b7290815e53106baa918f50c5109f2a6615e5310eeca3185794c429faa2215f53482bea818f594431ae29a835e510c63aa818cf95321af29e436d52103aea2a1d794c20bb288416f52442baa818f50c721cea1c817651d0b3a87a0d794f40bba8a873d54cc3ae8218d754c419e2a2413e540c6baa7a0dd94440ba28a877551082eaa2205714d20cea1a835f53442baa921cf55032aa28a873d540c678a8885b94b41
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x700100000f000e23382c080b3702946150f41b198b410c695640c721c5185540c695640c710c595031c87154354440c350d521021d6414d21a518543902946150c40951855310a946150f42c515031442546154f4087596540c695640c421a5590314425565104318759253843154354742d1148314431554d0431c350d52d06946150d42
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20180302aa4c5a0863411c54354b4182aec2a062884157695031c868238a86a908181590520c510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s2K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/44+packedAt s2K4 (2430+(h % 44)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s2K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s2K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe03f07ff81ffc3fc3e0ff8781ff87f034ece7c
  | 3 => 0xffc007fffe0fffffc00fff801fff87ff8f0f8f
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x428400230400800046110088c50089281050b5
  | 1 => 0xc98a4a451ca5052c1a8748514b48521946c65c
  | 3 => 0x5129488286a2255810a9502129504d28b0b0a
  | 4 => 0x962ce7125143ab9aeda0c4449ce66063f00de0
  | 5 => 0x1830c61c618c33e331cce66700c44083eda000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40533
namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8300030000f0000c4a41003181282500381480147fc30ff42fe21fc32fe32fe43fc40ff10fd42ff40fd30ff32ff43fe41dd43fc31fe31ff21ff41fc41fd32fe42de43ff20fc10fd41fd31fd10fd20de31fe10dc31ff31fc21ff30fc43fd43fd40fc42fe30fc20fe20fd21fe40
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x130614011060419214140010200e1a120440d1e0028b101c0022400400000038052000054e000000430088000278a8905754f41ba28a87d4310873ca818d794c43ea18e435d548c6bca6105754c20bb28c615e510c6bca321e750d42af29c2175510833ea8a1cf550319faa2413e54cc2bea6885714d209f2a0653d54c87a8a2a1e750f42ae29a83d6510c6e8a2905dd4532afa9a433e54082bca6205754f42af29e856d52102baa70857550319faa221d4410c6bea818d714543aa28a875e53d033a86205d544409e2a2216d52d06eaa3a15754f219eaa6617651d0a7ca990d754c42afaa4637651082eaa3185794c418eaa0637751482b8a6885794c42bb2888174514cb3a86a0d754c40ea18e21d4314433a87205b94840bba8a875e53c86d8a48875d0431aea9e815e53d06b8a690cf55020ceaa0635d531073a87a0db94b41afa9a416f52442bea6a0cf55032eba8a873e540c6baa921d794631
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x7143318200014000008938006102c662d043187590534870d43548409518553d0295640c71087596540c716540c72195594410c6946150c40875925384344520c510c51503144295640c721951855310a95640c421a559031442946150e40c350d52d06946150f41c550d51d0a946150d42c5185540c71554d0431c550d51102946150f42
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x28238a86a9081411c54354b41c0ac8290628841576150314420abb4a818e438155262d0431
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s3K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s3K4 (2430+(h % 51)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s3K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/16+packedAt s3K2 (294+(h % 16)*3) 3) % 6)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe03f07ff81ffc3fc3e0ff8781ff87f034ece7c
  | 2 => 0xffc007fffe0fffffc00fff801fff87ff8f0f8f
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x428400230400800046110088c50089281050b5
  | 1 => 0xc98a4a451ca5052c1a8748514b48521946c65c
  | 2 => 0x5129488286a2255810a9502129504d28b0b0a
  | 4 => 0x962ce7125143ab9aeda0c4449ce66063f00de0
  | 5 => 0x1830c61c618c33e331cce66700c44083eda000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40533
namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2100004140f510f710dd32cd32ee32df32f741ed32f441
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x40001000000a6a9c65c532d078a6588714c841e299221345444388a29971d4532
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x10911953244304544c910a1993514ca47654cb41
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s4K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/30+packedAt s4K3 (216+(h % 30)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s4K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf07fffffffffff81fc1fe0fffffffffe447fff
  | 1 => 0xff81f0f81f07c1fe3fe1ff0e0f0783c1bbb2cc
  | 2 => 0xfffe00ffe007ffffc001fff00ff803ffc3c30f
  | 3 => 0xfffff801fffffe00000ffffc01fc03f0
  | 5 => 0xffffff00000001fffffffffff0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x11040008400000000402201221088844001455
  | 1 => 0xa32c6111ca2a8a961ca0e50467451a8c99b2cc
  | 2 => 0xc418aaa286b529aac29156a08ad42339c2c30a
  | 3 => 0x8e514cc514a1adcd6ad414810ce67211ec03a0
  | 5 => 0x861888618c63171b31998c9c0804021776800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaaaa0aaa0eeeaeeeaaaa0aaa0eeeaeeeaaaa0aaa0eeeaeeeaaaa0aaa0eeeaeeeaaaa0aaa0eeeaeeeaaaa0aaa0eeeaeeeaaaa0aaa0eeeaeeeaaaa0aaa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40533
namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x30430000032000031800c00003d359d044064202fe30ff31fd10fd32fc31f741fd30fd41ff40fc40ff42fc32ff32fc20fd20ff43f441fe21ff20fe42fc43fe32fe41fe40fd21fc10fc41fd42fe10ff10fe43fc30fd43fd31ff21fc21ff41fe31fc42fd40fe20ff30
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe63755190afaa998df94e20ef99263ed32483dc6590df54e31fba0c437c53482faa8905f94742be28a417e528cbde4210df94c42bf284437f53487ba6598df94b43fa298837c5250efca5085f94332beaa465f441886baa7217dd0c41beaa061f631442fea8995754c20bea86637e50d0bbe86995f94f42de20a8176510c2f8a2985f15230be29e417e53c43daa521fd44010bf290877e5010efaa7087d4cb41bea88656e5290fee82105f14931fba0a83f6310c6fea6a05f94020bea80837f53082fca598df94c439faa2637e528c2faa9105f55230dea00817e5290efca1a0df94343beaa487f7410c7eaa420df94c32bf2a263dd5390abca6105f94632fba1083f642106faa3a15f54e40ef992617f54086f8a710df15021bfa8a857d538c2fea9197d88510faa88617e54cc7be64197d10420bfaa041f542d06f8a6105f95110de20e81f5411077a84215f54232dfa0081de5390bbaa610df14532fba1683f442106f8a6a16f50c43faa88417c52042faa790df54032bf29683bf544c6f8a0a0dfd4c10fba0e61f55190fde84a16f151319e2a2437c53086fca0087ed0240bea9e83745150fdaa4185f14910be282437c524c27ca9085f551109e2a263f442d06faa4887d50841bea9461fb10442fea5085fd5010bea8c87f521087ea63885f948209eaa0417e53443ba65987b50842fba0e43ef21886fca790df94040bf280837f52c43e883987b94831bf29883f443d06fca118fbd0820bf29021f910042faa3a05f95320af298437e51d02fca42077cc431bf2a461f532106faa1a16f95020fb98a636e520c6fea990df15220fd904417d52d07e8a7a0dfd4131bea9c85f441c87bc60986f90c41fa218837d52d0feca820df94030f6210417e52902fca4195f15321bea9841f752d06fea9907710d32bea94417d53482fea8197dd0440fb28841f55190bea6310df94621bf29e837e53886fca418df14542fa28a877e53102fea0a14f55030ef18a637f5050ef8a9907d0cb41df21483bc42906fca6105d94642bfa9a837c54c43e8a1a0fd94c41fb218837e530c7ec6290fd94841bf284617e50c87ea4388774c030f7904417d53102fea918dfd5131df20a837451502faa3215f54341bea84877d53487dca521fd94432bea86437e54482fca518df54a41bf29661f441103ee82885f94430db21083ef424cbbc64995f95020bf288657f524c2fca9985f15110bfa82837c54482faa4205fd4810bea8c417e540c7dca4187d54c41bf288637d54842faa518df14132bba8a817c53c8778a890dfd5332f710a43f710842faa010df14143fba0c81be540c3d884997dd4540dea1a81f451502faa3197dd4f41fc980617e51042fca420df14d10fa20a217e51882eca820df94440be28263ed32c87dc64195fd4e21baa8841ee20482f8a5085f94210
  | 1 => 0x621086f8a4a0fe88020bfa82437c54887f621085fd5120fa20a637f54886daa418df55310ee99263fa10042faa920f7d0e30bea9087765190efca221df54f10df20e817c548c7e883a04f95020bfa92877c52503daa418fb8c920bea9c437651082fca8217e50040fb18e213d54843bca610fdc8521bf280857f53883eaa020df54242fba90837d540cbeca5a0df94642fb88021be4350efca3997d10640faa1e83bf4210bea6288734c832fba0a617c5050af8a2a05714d40fa20c417d52c43eea1a0df94a42fb98c637d53d02fca6185fd5210bea9c837d520c6fca1207d90f41ef996617d508c7ba64986f90841bfa9c21df308c3ec43887d0c841bf29043bd41106fca721dd54430bf280437d518c3ee6420fd10521faa1883df430c3ec6310fd10530fba0e417d51d0ef8a8185f55320faa9e837d52cc3ea6218dfd4540bea8443dd53082fea6907750c43fa29083dc43cca7ea890dfd4f21deaa061f741843e8a2a17714d40bea9e417d5010efaa3995f95132bfa92837e54ccbf6609857d4d40bf2a083f65190fe883905f94e42ee990657d51cc2faa810fdd4543b7a92817d53106fca018df95030ef98c63be415036882a05f54440be29e21f550d06eaa2195f94442ee98863ef42883eca7a0fd48510bf294835d53087e883087794c20bf29c83f452d06faa3085f94641be2a2616d520c3bc8621efd0d40fba0c617c54cc2daa521ef10841bea9821f632d06faa3905f54640beaa4637e54487de40105f94032bfa92817d52843d885107d8c841f7a92817d50906faa898ef10c41fc90041f741483eca020df94640fb28c817d51082fca7905f54830dfa1e817e548cbe88210df54f42da20e817d544877e8220fd84110fba0861775150afaa521dfd4d10bf2a021f4418c2fea2a1df55031bea86877e548837aa8105fd4532bf29c817f51482f8a6a06f50940f6992437d544cbe882907bcc932ef98061dc438c3f661185f94242bf286637c54842fea4885d54643bf28e877d54ccbde85215d94432bf28c87f750106faa9987b4c832ee21861ed32c82faa990fd4c521deaa421745150be882187b48020bea94437e50907bea6a05f95032bfa9e217e544c3ee83887dd0631bf28c637c53486fea8887d10710be2a665f642d06fca3907b90842bea9c41f741042fca9085fd5331bf28e61f741cc6fca7a05f15032dfaa2437f5350be882085b94830df21c837f53086f8a890efd0940bf29681ef428cbf680a07e90040bfa92637e51083e88318df15131be2a0217f54cc3ee8320df95040bea80637d510c37a85a05f55221beaa0417e520c2fca990fd54432fb28c85f743d06fca3184f95030fb90c437e53486faa9205f54c21bf2a463b643107d885196fd0b40ef99465bf4390fec8220df94b10faa96837e54086fea7905fd5230fa20
  | 2 => 0x3e0a03001868168040681c0500c0b02ccf004000000080e6001e058020d000068000888a220000080200000b70020000802004068208400609038700020b80a0001c000c00b8240101e010080003c02006000000b01c0dd16008020f93e012080001a070000d05c00006000121d80846000000087d314998080197e00000070dc8000c0b80600800028000603a011c8044160106c00800000061180038026040040002603000260000083407000000002902e0016a000100300402866070000000a008041311ae88420100a0500c0282002800000040102e070020000206ada0080200000198180006808008008040700c06804000100313c1600c00004108080c40ca900004004002f2048b053848048360122a2e80201806180000f038290000980400006088703481e000040000c01b60000040001e0002e0380c15000008a40f000a88000e8bc01808010280081002814000262f85200048029a6000083581a0400800032068057e508cafea0995f14e20da210837e5090efaa4085f94910f719243ef328cafca220f7d0e43beaa261fb20482fea818df54e32f6908437e53086fca60877ccb31be28a87df4350ef8a818ef50f40fba9883f6510c3788720fd10431bf29a417d53442fca7085f95043bfaa2437d52cc6eca320df15232be2a6637551903ee65a0df14e10fba0a63df43ccb7e8320fdd0540bea98857f514c2eca3205fd5030bf28843ee32c83688620ef90942bea8665f7414876ca820df54a40dfa18877d52d03eaa3205f95310df20281bf4290af8a6087d14041af29c857c544cbee8210df94842bea9083be54842f8a8107dd0620bba8a877f54c42d8a4a05fd5220fba0e81f441502faa0217dd4542bea88877d5490bf460185f95221bfaa2617c52c42fca1107b14940bea8885bf40902faa8087d94341be29a83f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5210865d63148108f59052043645210540d354f4290b2c548c9219b997424cb3461550209dd855404365528c4319b98b540cb3453105409ed95401025c6355220bc983414433754105218f99250043565354642d9548410c6786054d21cd552510c33454d05319d18554cca6e62d5331d3951320cb4f53149409bd95320cb4d5348020cd587544c71c54cc9319dd9543106b6648c8419d98453083375410730ad986415031d54d0c30ad191214427461550329d984504ca6c6255130cd95041c427561d50329d987548cb4d3254032cd950418c3653254432d954a510c25d6510c30ad98640502b66395041cd950410873654105108f994544c71c53d0d40cb14b42502cf654c8329b98853842b565908419d58754c82b4644c431cd596421065c6355120add9132106d66394b41cd550418436632544329d58653d0ba75210540cb952520c33454cc5319d58453c82756510430b558e421073454d05219d185534827561d5232cd186540c34c534c921cd94c41d026d6214e109dd85548ca7561d5132b558c52106b662108419d99741442d663908419798f540826e6214c20ad580431067461551329b189548c34c53d4940cd148415034d5348421c9148415033654104409dd94410c23f64544328f59353c876552d0431d9149214427661d5021cd99254106756510410bc580531076752145408f99053043655254643b9988531067661d50209dd8554486766194b43d554f41082b46454432d914b41502ce63d0932cd151314866d62d53319d98453086746155130d99495190f2c52905409b588534434c534c9209d987530832d5454830ad185435035753d45409d987540ca5d63d53219d997414c676650cb41cd150414c33654d07319b98853442b56010841cd950418c6766194342d310d520c3944310430d354f200823e64d4f21cd550418c26e6214c109d587530831e5494c20ad18543d027661150209d185548c31c5310540cd551510c3a66290c41cd94740903a56290c419d584530834c5314940d9549310c65f6550c439758c52442766494432d3d95320ca756115020e9148415025e6314c20d3149324c66d62150309798c530874d3254432b558e42d0675650cb419d185548cb6652104318f990540c27860551329b58853043675294b418f990540823d64942319758f540825e6315021e9108410827664944209d98754c823f65504419b18953443355494420ad582541074c524c9309e580540873654544209d99441503573254432cb55342082b4644c521b958850106776155131ad98c421067965840109758f54c826e62d53309d987544cb3461950209798f54c434c544c8329d984540c35553884219758e52d067561d53309d984540ca7661d51208f191510ca3e6495131d9549510c34d5310820d914851503565354420
  | 1 => 0x42766194343d554d21087376115131d9d4b515025e63d53208f596540c354534c510e598c43106b66390841d9948410c3665254430ba580420839753105408f593528427665d05219d587544835553d04219d58653d02e66294f418f59250886766114c108fd954310e3e64141329b98b540c25f654c8329d994321067661d53309b988540c2b464484219d98652d026c654c920d14c9510ca5e6314b10ad190321079443106309d58652d0e3e64d4e109d58650d0ee66290f419d584534826f6254d10cd95341842b46150c43d514f415023c6454d109798c54082b464487109d984520423f6454d109d18554cc27b6055132d5d4c51503365410410d594c41086e66290c41c7552530835653944209bd89548c26d6294f41b598c521067561d5230b6580430c25f654c431f14ca510ca6e6214c21cdd4441502e8604c9209dd85548c23e6414a109d987548c2e56290c41cd95251082756194b40cd550418c6746454420d54c9510cb6452d45409b58853c427561d5020bc580521067765440109b58854043345410731d9d4841503365410420b998b41487345410520ad58243107565310420cd15041cc33654106219b18954443356590c418f593538423d6494d21c714e415023d6595020e594c43107655294643ad98a421067565908418f990520433654104308f992508c67461151109bd954210a3e6414c209bd89544436652d0430cd951510c2756115030ad586421074f4354a438f19151c82346454432cdd50414c32e5454830e554c431067765504419d987540c27561d50309b988540427661d50319dd9542106776155132cd185540c2766114d209dd85540cb945310540cd95341c867665d0540cdd85540823e64942218f593530829e63908419d98653d0a3d6414c10e510d32107376155210cd150414863f6550842e954842106b46150b40975965308674654c510f14c9314867761553309798c52043355454420ad98a43107c532544328f1915348337615503097d8d52443364214542ab98a4390677615513097d8d544c2b5648c841d9d4b41503345410720cd15341442cd638c832b598f414c6b66210c419d584504cbb041d01409ed95100425d63d5310ad98c43106e56290f41cd95041882d663140419718d524427661d50109d18554483555354642cd152314873561d51218f19151cc2766494430cd953410c3545314540d594f410823f6454720d354f420826f6548020d594f410866d62d53309dd8554c82756114930cd953410826e6294f41d554e510831d5454c20cb151324863f6454d20cb18954082b4644c510e9948421066e6214f1097d8d548823d6414e108f99053883735094341d554c41083365410431e998842107355410430bc980531066d62150319e980540874f53d49409e980540cad563140419bd9
  | 2 => 0x141782b0b02a000001c0100001d0001b0044d1c803000090180000007400021140300825004290100d10c0203c14140000000b1d00608c77000060040300008000020000c000000582d05c0f4940600003048c500c280a4250000403c2f2740e00803cdd91510cb3554104209dd85544826d62d5310cd953108423f64549109dd9441082ba6090540ad593321067b6054d21ad98e43106a66290c419bd89544833554d0430d954852107376115121e598e42107555394642ad993321067661d5332a598e421067761550209d58754cca7465485109758c52c42ae6290c41d514f515034d524c431e558e42107a4424c841b598e42d06b4644c8419798c54043655210430e510f321065e6394b41d354b300c2b66295041cd150414c66d62d50319dd8553483375410720b998850106746155220cb552520c2b56190c41cd15041c867565104318f99254486d56310431d554c41086cd63908429e580540ca6f6255130bc58041043575394f41a798e42907c5320c841d314d32c82e56294f41c718d540c33554106208f993528433643145439798f54087366510540d5d4c415025e6314910c7951530836652d04319dd85548825f63551108f590538825d63150109d987544c34f4354830cd550418873761950309d587548823c6454d219e980540c6776155030ec58041d0274654c5218f993530825d6594c209b594420833454c85218fd9153486746454430b958853106756590c418f191524427461550209d597410c23f6550040cd553410826c654c921b358a4310f4d52cc4319d594410874d53c84218f990538427765484219758c528433761950209758c54083a442106209d185540c36652944309d98653d027565104209d584538833754105209d98453c83b341500409b58b540c3346454432b9588410867765d04308f992534873652107409758c540867765d0420ad994415027b654c030ad185425035753d05409d59741083b260107409dd95310c736549443097997434caf26014841cd95041842766114e209798c528436552d0430d554d51083715014041e910a321063d6414c20d594e5190a756115032b558e52d06766114930c514c415025d63d5021ad1854210a3d6494010c7151324c63e65151219dd8554ccb4d524c0309b98b540c63d64141329b98a53d025e63d50328fd9151cc35453105409798f54c86d8604c930cd550410427761551109718d54442b4644c7109798e52d027661d5220f14c832d067b654802097d8d544827461553209d58650d0a5d6394b409b58a53d02b4644c621ad59643106ce62d0d32add90321066e62150319d59432107375410531cdd86548432c5210540ad582421066e62d531097d95300c3555314c41d994a5190e7960150319d587544c2746454432d314d32c86b664841108f590528
  | 3 => 0x601c6b0800505c004f0fd02c04008000401901c09034760000600c2509c5e0001e0641a00000088051b803000130380800007070020540055c02040020942105407004480c8020000801c01000050081d000c50040000800004030c80e0142104c260480806c0e015542380d000020bc03000121d46701c01030310106e5e4730043b144c0000080284c5cc8c00446024060000f0b44f1240022c0912c000400505c160600b1ac060000000408014010340c2240c00c0c0005106c
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x3400f00080805600000160000002088060e00000120008000240002601700000850000000000204001021410b00b80060e9c0d167394841d021a3a2c229e41299ca6395041a8ae629242886146414d314421a3a2c229261515c4544c832c28c630aa8184c57398b414874232264a8865525c04354830c8ac7a94a5a0f07531484150312b288420841c1d91325443292ce7314a820d857298c43106a2b88a499261315ca63d0531b42e021082106156510c410c28b39ea820e41891905248510c48c8992a21970453148415032232264a8865315c663d0932a4aea2108210661525805210728a9ac0298839158d5214841962e03206420e145498f414c730b12a02808391595320c841c28c8992a219684644c8321064b39ec819083c114f5210540e08a89926290e1464cc9510ca62b8cc5a1a65451cd5410620a92e02a2641952472550418c30a322a690843455d44310430a4ce5aa08398645535884108653396c819083c110d5210430a8ae229a659064563548410c78232264a886591195324c521868ec2a26290f0553108410821a3a2c229a41891886155020a8ae229a6490651635405010723a9ac529e83811913254432c18c8992a21964953580420831232464a886591995320cb41b0ae73108420d917010c410c293394a620e8189191524c431a8ae429a62886245498b4148722a9ac429883a1191324c521
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x10000040300040022a0486151324c521c04545ce62d0521904845c4534cb20c21655c04210420c11655c04310430c04645c8534c510904845c4534c920904845c4524c930c04645cc5248510b018010d5210430d01535c04210420a8180191320c841c04545ca63d0531
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 5 => 2*((h/289+packedAt s5K5 (18873+(h % 289)*10) 10) % 699)
  | 4 => 2*((h/229+packedAt s5K4 (23788+(h % 229)*10) 10) % 626)
  | 3 => 2*((h/60+packedAt s5K3 (3675+(h % 60)*7) 7) % 75)
  | 2 => 2*((h/18+packedAt s5K2 (780+(h % 18)*4) 4) % 13)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe07ffffffffff03c3e1fe1ffffffff80c7fff
  | 1 => 0x3ff81ff01f87e1fc03fe3fe3f8781e04739ecc
  | 2 => 0x3fffe0ffe007fffffc003ffc7f801fff83e30f
  | 3 => 0xc00000fffff801ffffffc0007fffe007fc03f0
  | 4 => 0xffffff00000001ffffffffff80000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x829040124401000080a04a04888a4290042c55
  | 1 => 0x9432c621c92a4b2c116a16a13c50d4343196cc
  | 2 => 0x18418a4483348955540824c85541196582c30a
  | 3 => 0x116514891220cd9a5a4c808066659046d803a0
  | 4 => 0x2186180e1c4710e3a3913912000601836f7800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0fee8aaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40533
namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c009ff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08407fe43027f54805fc52007f10409fd5100ff08001ff4101ff14c03fe2000ff90003fc3001ffcc409ff51007f50801fd4101ffcc807fc43007f44009fd50007fc4009fc5400ff84009fe51007f8c401fd40007fd0c01fd20027fd4809fc51027fd4001fd43007fd0009fd54007fd0807fc31027f95005fc32007f4c807ff30027f54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x262003f7cc93002ff86310823ff544400bfe32c421fff5953113ff840a08a3fe325040bffa8c6205ff94621007fa6290027fc4390405ffa924033ff94132097fe62a003bed5248065fba8e8205ff58841007f8c290007ec2048011feb2a2005ffd971002ff8a320806fe604c8017fb222009ff10341015fcc5a0007dc304c0017fb226005ff5471001ffa6518827fc65d0c67ff3026403ff0c343157faa4a08e3fc30d083fffa92621fffd9531007fcc890027fd43d040bfe10e8203ff8ca3104ffca9a1826fc65d040bff32c4209ff9534202ffe6388003ef424c8057e3126213bfd9540005fac420812fe65d0c55ffa828201ff9011002ffc83188affe509040bffb10820affd4f100077ec898816fc6388401fb10a2000ffd894017ffc61a080ffd534c079ff90a8600ffd812109ffea6a0003fd41500017fb1a8401bf1814204ffac3a1017fe6488401ff30a4009ff1094102ffcc118812fc654c003fd2068005ffd8e210d7f86110903ff52d0c05ff992842aef95141007fe8690083fc208c40fff31a2009fdd064102f7e822080fdf304c813fe3168222ff54a311b7f862a100afe6244013fe21a8005ff5071009ff8a2a00abfd5050405f71968407ffcc910017e8429080bff4248001feb1a8001bf9834102ff86288016fc6488405ff9028409bf19743005fac1a0817fe6388445ffa846203ffd0d3102ffca288063fe4348401fe3224001ffc811001df8c68800ffc53d0c81ffa868619ff1952100dfcc1a1007fe204c001ffa126201fd0411002ff8cb1880bff52d0801ff18a8000ff485301e7fca4a1817fc51c4013ff21e8028ff9894100ffca0a0073fe5488403de2068021ff10a3102df8c2a00d3fc654c8137f3226201ffd0130005fec6a0803fd6048401ffb028409ff1014302ff8cb88017fc64c407bfe32a860cff10f10025f8caa18f7fd5050c13ffb068400bf59131017faa5a1002ff6048445ffaa4623dff99543117faa11880bfe2148013fe2a2862aff9954113ffc80a080aff6450801ffb0a6005ff8c7100c7fca690807fe50c400bfe98c4203ffcc1431effea0a1827fe4310413ff32e8209ffd0f42187f8a5a080bff5288403fe1822000ff58d42077faa890003bd43d0027ffb2a8000ff991211aff860a1003fc414c00bdfa0c8230ff0cb4104ffca8a100fde43d0c057f3128600bf5824101ffc60a180ffc534c0077fb228636ff18d421e7f842a18f3fe4250c6ffeaa28405ff0c54101ffa6498077fe604c451ff9028200fdd071017ffc21a080bff5250811faa8a201fff551310177c84a1012fc654841dfeb2a4001ff04120017f864a10b7fe4390453ff9928209bf197421affc80a1026fc644c465fea9e8205ff945411a7f8a899057fe53d0005ee1926410ffd4530005fec498803fe6444041ff2046203bf98d41
  | 1 => 0xbee42d085bde21c8219ff545211e7fcc4a1863ff3148401ee9926002fbc813202ffc831080bfe20508077f31a802aff54d4101fde6499027fd42104037f3028401ff901201b7f8a6a10ebff50d081d7eb2a4009ff10b4304ffec5a085bfd51d0003ff1022002ff8ca2102ff88288012fc6544005fea944215ffcc740007fac4a0817fc63c40397eb2c4205ffd8b1003ff8a6880bbfd5490413ffa128000bf58743087fcca9800bfc42d080bfb18e2033ff04132007fc42a00eafd65d0801ffa1e2005ffd8c41017f84110827fc62d0003ff9826003ffd4d321bffea2a1017fd64c400bff3008240ff5434300ff88098006fc60d0c0bfeb1e2009bf9913002ffc21188d3fe654c80bfe084823aff5434207ffcc498006fc608c401fe992823dbf59543187fca5a0802ff6050401fea0a4200ffd0b100e7fea110806fd60c4005ff9924003ffcc931017fa8499017fd628c407ff21a860eff9452001ffaa718817ff3110413ffaa68609ff10c4101ffa8698027ff54d0803ff9024001bf98041006feca88003fd3244069fea8a6402ff10a2102ff8629889ffe2050433ffa9a4205ff14521207fca3a1816ff65c4039fea844205ff9453104ffa83a0003fd429040bfe314621effc813104ffc81a1866fd6548425ff31a8029ff14d4102ffc828800afc62d00017eb046202ff8c9420b7fea7a004ffd545000b7f30e8600bfd913104ffcc5a000ffc31d0c0bff10e202fff1434100fdc4090017fd519041ffe10a6018ff10d2100ffc609800bfc20508077fb0a6209ff18f4002ffc629081bfe3244005fea928405ff504410e7fea910807fa10c404bdf2188200af19131007fec690027fe63d0403fe1022017ff9412100ff820a0027fc43d0007ff98a6408bfd9510007fa84a0027fc61d0015feaa62000fb4c920137fea62080ffe5350c077e31a4005fd0c631007ea6288003fe31d0011fea922002bf98a4108ffcc4a000fff32d0c0bfe2888201ff9434000ff86090017ff319046fffa82841aff90221187fe43a0817fe6290405ff996842aff19541007fec098802fd644c00bffb2c4200bfd8940017f884a1007ff504400bffb008201ff04310037f8848800ffc304c4557eb248239ff0c742157fea8a0816ff634c405ff906840fff9093004ffc85a08ebfe51d08217eb2a6001ff5011000df8c110817fe648c447ff2808200ff50b10107fc4118826fc644c879fe3128609ff1534102ff88318807fe104c003fea822002fdc8521077fca890002ff6250427fea8a8005ff905411bffea8a100ff7314c407fe21a6402ffc822113ff8c0a0827fb4050005f7192402def90e41015fcc5a180ffc538c405ff9944205f78c53101ff864980c7ff30d04057e3168601ffc411007ff8a498017ee214840b7e32e201fff951311a7f8a29900efc63d000b7e3
  | 2 => 0x10147f8c4a0817fd608840bff90c6226ffd4841147fca4a0807ff205000bfa2888200ff5893102ffac91080bfe425080bdea088203ff14d31007fc43a0003fd315001dffa8a4009ff9974001dfcc7a001bfe4244013fe32e8200ff98540007fa86a0817fd6290469ff2a26400afd91310e7faa71080afc625000bfe18e2002ff14942067fe6588012fc6550813ffa168005ff9471002df8c918803ff434840bffb1c8202ffd092102dfec91880fbe4350c0bfe3108201ffc8310007fac69000bff524c853ff9828213ff59540087baa69800bec424c803fa0862002ff4c92002ffccb20826fc644c00bf790c4204bf9953204ffe87a000bfd524807dff1068606ff14910015fec4a1016fc6148003fe1828020ff1023110ffca518812fe6544027deaa28005ff085410b5facba00f7fc5150c13ff3068200bfd893001ffa649880ffe324c45dffa9c8206ff0c91004dfcc890003fe4148005ff1924003ff94d30007fec890002fd64c400bff10a4203ff10d43147fc84a0803fc644400b7e3108222ff1523102ffaca208dffd6550805ff1068405ffd931002ffc8298807f8304c013ffa188209ffd0841025fccba0017fe628c477ff2828604bf995401affc20a1016fc63c4013feb068609ff58f40115facb1880fff434c80b7e30a6001ffd412000dfcc38800fff308c40b7fb16201fff549310eff84098807fc30c4003ff0822001ff081200077a84a00e7fc53d0833feaa24200ff5854204ffca8a00dffd5350813ffa1c8226bf59441005fac788017fc10104697eb2a6405ff08631207fea3a1816fc61508077fb1a860afd54710047faa688027ff63d0405de2128403ff8c2311d7fea3a1027fd54d0013feaa08234ff5953200ff080a0007fc10d0013de2188202ff8822102ff88310817be415040bbf328820dff0c52002df8c2a1817fc1048403fea024002bf989400fffaa098803fe614c005fe212400affd4b1002dfec49087fff504c413ffa1a8009bf19120087feca980127e6510415ff2a6200fff189300b7f8a3a0027ff42904017eb148213ffd4940007fec2a101bfc6244013ff21e8209ff50b4007ffe42980a3fc5250403fea82401eff10931007fa4288077fc604c403fe282600effd512002ffea310802fd63d0005fea124228ff0c94100ffa4188047fc6250043ff2146205ff5444101ffc65a1867fd654840bfeb1c4200ffd0530017fc65a10237c6544053fe31a8208ffd451002ffa63880d3fd544c803ffa022002ff4ca21157fecaa0817ff658c4057eb16841dff9013107ffca498006fe604c413feb1e8410ff15130207faa5a1803fc644c811fb28a2009ffd8f4004ffc81a104ffe6550055ffa8a823eff0834300df8c0a180bfc20d0801feb0a861fffd513101ff8651889ffe1050477fe2828621ff14a31025fccb2080
  | 3 => 0xf20a801eff1493101ffe61a1817fc3148469fea826435ff141420f7fc84988e7ff30d080bff28a4200ff4cb1004ff887a0806ff6450001feb028203ff90e3101ffca718807fc5044013dfa1e8009bf19121045faca88057fc31d0007ff1868601ff08140017f8a4900fffc21d0c07ff18a6005ff196411a7fea899007fe504c001ffa0a2002ff08742017f8649006bfc4088467ff2026405ff9071001df8c690816fc658c427fea928029ff94d4100ffe41a000afe625046fff32a8401ffd4140017fe42a100fbc4350c01fe30a862aff59541037fe428802ffe32c4039fe2a44201bf1813102df8c5880a7fe6350405de2168409ff1014204fea822085bff52d002ffe1824205ff0c44112ffe6420803f52144007fe1926203bf993430dffe611087eff654c40b7fb2c420eff54d20005fac918827fd60d0813fe2128000ff581431bffaa0a102bfd52c4049ff9008201ff0831000dfcc09080fdf324c403ffa862001ff84120007ea6388017fc21884077f31a2031ffcc7410d7fc611084fbe5450017fe216201dff8413104ffc85a1827ff65d0c2ddeaa68001ff54140007e882880bbff5290457ff2048202ff90b42007da6490803bd42d00057fb126419ff995211dff820a180efd638c40b7e32c4203ff54d3102ff8c620816fe618c40bff3188202ff14a2100ff861a009ffc5050403fea062009ffd054100fbc60980b3ff209047ffe2968605ff0c641017fe6499006ff604800bfe28e8200bfd8131007fec2a1802ff6150c0dff2922000ffd8d10005fec69004fff545000bffb28821fff99531107f8a11880bff204c83fffa8a6202ff90a2100dfcc0a180fdf32d0c03fea862019ff9512102df8c62080bfc52d0813ffb0e8000ffd891000ff88088003fd31d0001fea1a8403ff0cb4304ffca9a008ffc301047bfeb2a8610ff19530017f865a1023fc544400bff28c8205ff84221017dc6490803fd434406dff9828402ff08542147fe42a089ffe3050405fe90a4001ff90140057fea98804bff3250013ff31e8003bf18d4200ffc818804bfc3150003ff9822000bf5874202dfeca2080efe631040b7fb262002ffd49211f7fc21a1817ff608c4097f32c4200ff4c52102dfec710807ff40480137f3244209ff1514104ffca820807fe3044007ffa9a8600ff105201c7fc21a1017fc2144007fa18a623dff5454302fec4388077fe204c40bffa0c6200ff58530005fac899017fe658c401ff30a6413ff94540017f8651084efd6550007fea9e863aff54f4217ffca1a080efe639040bfe3162005ffd82410fff8ca9880efe6388407ff98a8603ff0c132007fac899012fe6548405f72924001fe0411000ffc409000fdc434c801dfa1a8009ff5974004ffec5a0003bf425003f7eb2a6205ff1053101ffc8698037fc5348057fe1848209bf991
  | 4 => 0x82ffc32c40017fb226405ff14631087faa8980e7fe53d08017eb1a4200ff4ca41007fe8298803fd6250c13fe32e8032ffd4b4104ffc83a000fde534c00bffa8c8200ffd91320b7faa5a0016fe6190427fea9a8009ff9834301ff88718803dd324c43dff90a6202ffc852000dfec490007fc104c005ff1924202ff881321b7fca6a1027fe63d0805ff2924000bfd894302ff8429886ffe53884017eb068600ff4c84100ffc2188002ff6350041ff2846205ff58b1004dfcc918803fd614c8157eb2e2032fd147410a7fc65a000bfc2048405fea924205ff9822104ffea9a0012fc6550433fea824200ffd852001ff860a183bfc654806dff21a840aff54f1001ff8a699017fd6590405df2168401ff90340007fa42a008ffc2010401fea1c4209ef9534002ffc8220807fc20d0001fea12601dff1013103ffc8688067ff5048413ffb2e842dff14e4100ffa6088002ff6448413dfa168005ff58041005fac71080ffd434c469ffa8a6400ffd8d21127fc6420827fe5450c01ff322603dffd4943017f8849089bfd521047dfe2868601ffd4340137fea0208027f654406dff31a8438ff14342175facb20802ff6448021fea8a6001bf181411a7fca299002ff6050801feb12201aff1422100ffe80a003bff6548003fe2024009ffd0b4118ffca7a083bfc5448071ff1868409ff10b40007fec6a0816fe6110401feb1a2005ff48710195facba0803fd6350401fea1a4000bf58b43197faa3a0807ff3048001feb222000bf58d20007fac890002fd63d087fff90e8601ff54340015fec69900fff314c005ff90e8400ff9854304df8cba0006fe608c403df202801fff151310cffea890817f651c4013fe20a8001ff8c12000ffe8188007fe2050025fe29a8000ff1912104ffa85a080bfe324c813fe2108200bfd8d2103ffca688017ff51c400bffa0c4209ff50f4201ffe6098863fc6348405fe10a4015ffccb40007fec6a0003ff644c06bff302843dbfd95430bffc8090817ff6488407ff1826202ff0813201ff86299007fe20c4007fea1c6209ff99742167fc652080bfd524c84dfea808237ffd954214ffc86a0803fd604c87bfeaa28605ff1071004ffea820817ff218840bfeb2e2013ffd454004ff8a8a100fdf314c81dff32a4000ff4c940007fa8298027fd63d04037eb068002bf9934204ff8c1a10d3ff504c85dfea94822bff0824102fb86298833fc53c4037fe29c4202fb0c93200dfec0880bbff5090405ff2968402ff94a210bffcc0908bbff5490407ffa9a6016ff94740087f8a298027fc40d0c05fe2126401fd84110007fac0a1043fd654c04fff3028205bf1964102ff821a080bfe4248007fe21a6009ff10342007fac898027fc54d0c05ff992422eff5424101df8c7a080bff2048413fe2028203ffd0d4308ffc64a0027fc54d0801f
  | 5 => 0x4121007f8c898803fd6148011ffb2a2009ff98342005fac7208f7fd5250c13ffb2e80009f59740004faca2080ffe43d0c017eb0e8001ff8c14002ffca3a0802fd6488401ffb224205ff18241007fa84a0803ff624c0097f32e8200afd912100ffc21a0026ff65d001bff31a4002ff9093202efaca20803fd4144059ff2148219ff54d2101dfcc7880dfff5350813fe30e8401ff1014006ffc8690017f441c40093f32e8008ffd4d10005fec0a1803fd6448401fea1a8005ff042310b7faa7a0007ff305000bfeb1c8201ff4c1201bff8a2a1027fc4250c17ff2962000ff58940007fec0a0803fc644c005fd9024003ff90d3101ff66098003ff624c405fb90c4201ff10310157faa2a0817fc5144013ffb0e8631ffccb41087fea498017fe1010413fe21a8403ff4c530187fe41a0817fc31d040b7e30a6433ff8413202ff8ca2082bfc54c40137e3222000ef1912103ff88688003fd43c4001fea146211ff085400c7fcc690827fd54d0453ff98a8235ff94142197fea7a0817fc608c40bff18a2002bf98b410077882a0016fc6390413feb068201ffcc310017f864990aaff6550403ff2822000ff58131007f8c2990f7ff5450c13ff2a4822cff14a4104ff885208effe4050c05ff2928405ff1923104f788420802fd6448401ffb222005ff087101aff8c0a1027ef4250801fe90e8001ff8c31000dfec288003be4150001fe30a600dff94d2002df8ca20802fd62c4059fe1948209bfd97410dffc87108b7ff3290457ff1048200bf58a3101fb886a1802fd6088455ffa9a8203ffcc94302ffaa31882ffe42c400bfeb046209ff19742007ee8288047fe42500057eb144200ffd8d4201df8c6a08cbbd54d0413feb168005ffcc631017fc4090827fe43d0807ff29a6203ff54d3202ffcc588016fc628c4037fb028005ff105210c7f8a69080fff434c001feb1a4211ff1494002ffc2120803ff424c003df206802fff0c34104ffac5a187bfe624c4057e3122009ffd8f4204ff883a00127c6544003ff1068009ffd8b4302ff8a2a0817fe6390401ffb128209ff9874202ffcc788002fd601040dff3122009fdd0541177faa720803fe214c00bff2888200bfd853004ff886a0817fd418c413ffb0e8403bf98d2101ff862a1817fb1044013ffb068215ff14f400cffea290817f421884017fb0a8400bf58b4102ff8c020847fc325000bffa888209ff9534100df8c0208b3bc429047bff28a8607ff18d10025fcca98817ec2148405f790a6401ff1412004dfecba189ffe5050479ff9028623ff880410b7fea3a0002bc6448413feb2e8609ff9004104ff8c7a100bfd32484017eb168004bf1953105ff8a58800fff538c43dff292623bff981431fffe41a1877fc504c4037e3068225ff14c41007fe8290007fe1050001fe9968003ff94f4302ffc8290
  | 6 => 0xbfeb188201ff4c310025fccb8800bfd42884057e3126024ff1484100dfec698003bd4350001feb0a8010bfd953002ffe42208ebfd51d0855ffa92823dffd454304ffa8620803fd414c4697fb2a6405bfd964100778c89880bfe5248481fea8e8603fdcc63101ffea69883bfc51480077f31e8200bfd85400cdfeca9088bfe548c4077eb1e8604bf99541015fec290827fc54d0013ffa1a823fff94b43017fe4299017fe62104097e32a800dff10d20025fccb18853fe52d0069ffb2a6405ff1453101ffe63a1803fe314800bff10a2012ff94d40005fac620867fc544840bfe1088239ffcc74204ff8c1a1817ff6590401fea1a4205ff9944104ffa87a0007ff30d0003ff2824022ffd4a3100ff881a000ffc434c40bffa0c8218ffcc12100ffc61a0007fe404c007ff9826405ffd923104ffcc3a1807f8204800bfea8c4200bf58f41047faa888077fe504c40bff18a6209ff59741127fca42080afc625042fff1824200ffd0a31067fca788016ff658c40bfe10a4202ff94932025fccba1017fe64c4007ffa9e8609df59740187fc65a0817ff21904017fb0a4004bf1952004ff8a8208effc6050c01ff30a8409ff100410a7f843a000fbe43d0c097f3288205ffcc62100ff8208809bf75110413ffa128205bf18a4101ffe64980ebff53d0801ffb0a6409ff908411dffc40a188ffe3010465fea96822fff0834112ffe6020806fc60d0811fe32a2003ff0c530017bc6499103fc51d0c01fea12202cff94a41087fca29806bfe5088407fe29a8601ffc8130015fcc4208ebfc51d08097f32a6009ffd054004ffcc5a1827fc43d0813de20e8005ff5963102ffa8310807fc5050001ffb128601fd84310015fcc498002ff604c807fe21e8600bfd891004ff885a0827fc62d0c037f3268000efd9121007fec2a000bfe42484037fb02601eff1893102ffec78800afe628c40bff32e2003ffd0e311f7fca1a1827fd61d0067fe2026400bfd8d1002ff8c520827be54d04017eb224013ff1954000ff8a188027fc63d0413ff2168024ff0c84102fec82208e3fe50d0807ff192860ebfd952001ffa8699047ff215006ffea8a8436ffcc54202ff8a3108affe309040bff18c4209df99740137faa6208abfd545040bffa0e2005ff18e41047faa288012fe6550c7bffb2a8601bf18241017f8a490816fe6188437fe21c4202ff085321bdfacaa1027ff54d0401fea1c8209ff1524104fbe86a180afc62d0401feb226205ff0414104ffccba181fff3144005fe1924203ff8c132017f8a4990b7ff3090403fe1826001bf1813202ffe4388053fc52d0001ff3226222ff55231017986499027fe40d040bfe3044214ff0cb40025fcca90047fe5250001df20e8009ff151401dff840a1803f521c40057f3162033ff18132005fac1a1017fc6488421ff2a26017ff8
  | 7 => 0xb81201e1140000001657c030060100000500b00000802288008000020000840000d0020060040202400400001001050228058060020784380800067c020000140980200600034c010040060000582d03401c56000014294a88db061864088000060040300201c0a80280000c0200300a07802000009004c140f0070081001780200004c070031960440205d002074000121320222e0350740ac038040000000081709e000010090001d00000400800c0f8020980342583200202d2c80100211c0080200402c009c502600006806108104000000040d41800005a03c1302604c0401281302a0042c014000000168de00200003005000008460120024f4048010e40041800107600c0100004a020048000000d0020000060000200100c0fc0a0f700e1befb0190000b00200802c2d80703e00045006a010600080080000601c0203c0122240589204e74c29001002028ab839020064080360a80456a81e0b61080000ffe434c813ff3168200f7d0d3202ffac120817ff608840bfe0826209ffd97410bff8c090823fe54440137f3226437ff9454202ffac918817fc318c4077f31e8405bf98742017fe8499027ff43d04017fb0a6437ff1954218ff8a7a080efe63508017eb122002ff50920197fea1a0803fc6150007de21e8609ff18341017fe8510803ff4388407ff994622dff94e4112ffca620807fd2044057fe2848200ff9053002ffec520887ff208c401ff3226400bf58d10007fec0a1803fd424c4037f302823eff0434301ffaa6a180bff21484017eb222009ff98740087faa498017df318c407fe1928603bf98d20007fa6288023ff524400bff28c6209bf9912101df8c7a100efc63500097e32a6440bf5974304ffaa9a180ffe324c06bfe0828409ff553421577aa8a089ffc305042ffe282420eff54520097fc86a00f3fc5250c65ffa8e8204bf99542017fe84a1023fe6544033ffb2a4209ff58b410e7fea710803ff4148405f6212840effd4d201677c8520807fc204c0137f3262009ffd0d4200ff8a1a0003fd624c01bff98a4024ef90841155facaa087ffd514c4057e3128601bf9822101ffca699017fc2190413ffa0e8000ffd91310a7fe43a00e3fc10d08057f3126232ff5434104ffac3a18deff6550821ffaa26001ffd4130007fa65a080fff314c413feb2e8405ffd0441007f8c2a1006fc60484037f3048209bf9904100dfcc1a1807fd404c001fb18a2009ff187430e7faa9108effe1050c13ff2a2820fff1093002ffec51888ffc5010413fe2048203ff0c23100ffaa09804bfc635006bff1828400ffd813202ff82110826ff65d081bfe31a402fff8834102ffcc120817fc638842ffe2024200ffd0d10007fa8290033fe43c4013ffb068601ef1014002dfec9108cffc504c801ffa122005bfd8f1002ffacb10816fe61d000
  | 8 => 0x140180080380e0780b00300702e0000102100202c0000c0220069680009737411836044d6c0280200c0000a00100a208008031740480002000e0000180e01c0301303802801c0182d00a178028010020180380b0b60f01cc56000050000820020092a80900200c000140000d80001b0640a45300000c0080200700000c0d00000419991828036000038010040080780800403c0080317012c000040000140480004a1f00c8ea01c01eae26d03804800004014024000000500007f00000a0524a0650000040c00600a000020b00100780000000a034058020020a0880104020100000b000000040060001401e82100406d5e85606e0781181404a04c0311501a000008ac0642781702a02a0080f80d00005408809002048040110c206401000016000030004761580500202201803808016000008020000a87d80900000c0a81100405c028070140d01600200a0100001b1560480000509e15c010ac0041b012801018010010081480000480100203c0100501a138008010001800880053a018018000041d4108730101500381300c0203f0030200000e03e1680080100605c0080084306e0300100301caf40000700a000a100102404c028ea0b80e80b8080140000f1c30000040000303a08c0e83a0d009cbd8010480a82
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf755824102ef71058c410067e43d9510014fe7458f42136f46510510024fc75d8131004fd75d9130004ff70592210067c32d951001cfd74d814312e9f321913104cfe74d8930006bd72d913101ef4638c510004ff7258f40006bf5119121005f573d0710024fc75d8121004fd75d813101cfc7358742006bd51d912104e7e435944116ebc6390540024fc7558b41014fe72d8143004fc7648540004fd76d0a310a5fb705912000cfc70d852000cf47159310005ef7250d42024fc75587400067d74d9510004fd73d9110036ec32d8910006ef725891002cfc7650b10006dd32d853004cfd71d8d410067c325944117df6741051004cfe74d8d21024fc7558a31004ff7558c41004fd7650f10005bc744853000cfc70d8d210ecff7058d10004ff705874302cfc715913000ddc704c9304179c3119131006bd641913104dbc7488540004ff72591100067d7159740005bf7458532006f431d854220df4744c510004ff755913201cfe7358041024fe7558a31006bd54d9131024fc7558f40006be50d913100ddc764c930004ff75d85300247c7558d2002cfd70d8d10006bf7458910016f66248510006be42d9110005f7714cb411d67c65d09102af7410d9510024fe75d911004ebf75191313ee7c3059740006bf531912100777658c51002ef6611854004edc4358c411a57e75d8532024fe75d913102df4714cb41005bc7458d200067c735974002e7e715944104ebc7019121006be1019121004fd71d81430067f6519110004fe764c94001cfe7358b40035f9709852004edc4358f411cfcf30d093200cfc70d85430067f65d9110006bf64991321dddd739913002efb1058231166be20d91212a5bc715094002cfd74d8d41005bf74485300eefa10d8131006bf51d9121004ff7650e2112ebc6310540004ff7258231024fe7558b1001cff7650e410fd7e751913100dbe7090540136f66510510004fd7650d10024fc755834201cfc74d8d4001cfc73d8142004ff7558a411c6fa205834206ede63d8d2004e7c4359441014fe72d912043edc43d913201cfe73d854204cfe74d812115ebd40d911002cfc76d0f100eefa30d8131024fe7559131004fe76d09102c6f564d0710014fe72d8d10024fc7558f4200cfc705922121df77548510126bf52191210057f755852004cfe76d912104ebc6450931024fe75d8d2104cfc76d053000cfd715822100cfc70d8d10184ff7159121004fd75d813238dbf7550940006df7359110004ff75d912100cfc7158f1001cfe73d814101edf614c9312fef621d8520004ff764c94004ebf60d0d40005bd729054014cfd765053104ebe641913103edc6358d1000cfc72d812102ff360d051001cfe7359221007b474487101cdef725913200cfc7058e21004fd7558a41127ac424c841004fd70d85430067c43d9510
  | 1 => 0x9131006bd50d913104f3e6550f40016f4624851041ebc31d9131014fe7259310005bc745853016fb731d9131006be761913102df4715094138dbd755094002efb705824102cfc7158c41006be62d913104ebe7519121004fd755824103edc32d8d100067e42d9510004ff70588410067f21597402c5f4744c7103bdbc7150f40024fe75583420067f7558241006f7615054004ebd73191210067e73d951002e7c4159441014fc76d0521166bf71d91212b67c41d9510006bc7458d2104cff76d0d21004fd73d9121024fe75d8530014fe76d8940006f5611853015dbe7110540006bc70d913104e7e42594410f5ec7258131007af424c940004fe764c91001cfc73582210067f654c510016dc764c93100df676d0510416bc3119131004ff755834302ebf7459231004fd7558f10004ff75d894104ebf701913101edc6350d413febe511912102ebf7459310004fd7650b1000cfc73d81310457e759911001cfc7458b43014fd74d8142014fe72d911002e7d3159441004fd768854004dbe71905402cdf7754871009d7c7558540245f5754c510024fc755874202ef760d05103f6f621d853208eec21d89400067d654874043ebd43d913241dbf7450e41006bf50d9121004fd7558f40006bf70d912100cff73d9130006bd53d912102cfe71d813202edf7358e41006df7358910016dc624c93000cfc70d8532006bc30d912101edc6350d4000cfc7058c410067f32d9510014fe76d894304ebf721913104ebc64d052104dbd769074001eee634c920006bf53d9121005bd73d094001cfc735834216ebd43d91312ae7d40d9510006be70d913104ef7415874204cfc7458d10306dd64d0d32006bf6499130006bd511912104edf7358f4202cfe71d913208fac6250940014fc725823102fe7724851002df7724851001dee73d09320067f74d9510006be5019131005df735911002cfc7650a31306ee644c92012ebf301913102ef6611853000cfe769054003edc43d8d10006f721d853001cdc735891000dbe7050f40006ec725911004e7d405944104cff76505310073d751912101ebe6350f40004fd7558341016bc6250b4002ef81058221235f6768851004ebc6490520014fc7258f1004ebc6410520007b56410510004ff7650530036ec62589100067f65589100067c705944102efb705804100cfc71d812103fd4634c510024fc75d8d2002ff3608851000cfe70d894104ebc64d0931005bf7350940004ff7058f4104ebf60509401c5ef7259120005bf7458d10016ef614c921126be2019121006ef32d891001cfd71d8931024fc75d8d4004cfd71d8941005bc745893100dbc70d094018cff71591310457c7558d1012ebe32191310067f755911002cfc7158f40024fc75d8930004fd71d8930014fc725923102cfc764cb1000cfc70d9110004f
  | 2 => 0x24fc7559130006bc70d9121004fd7558e410247c7558241006bc60d91210c6ed3258a31005bf745852004ebc64d053104dbc748c5402ae7f71d951008fae32d09402af7810d951001cfc73d911004cfd72d814214edf31d8d4100dbc709074004cfc76d0931024fc755884102cfc7650f10004fd76d0b1004cfc76d0d201a57e7519132006df634c510005bd721054002cfe7158a31004fd70d8d21005bd72d0d40004fd71d8d2000cfc7058f412fef521d8520024fc75d8d2116cbe761913104cfe76d913204cfc764c740004fe76885302ddf5754c710006bd54d9132004fd75d894302ef76088510127cc324c841144fd765052102cfc7158343006be6219131004fd76d0e2102df77510510024fe75d9132017cf63d0932004ff7650a312a6bf6190540166bf21d9121004ff7558a31366bd40d91300057f7558910316ef20d89301dfb87050d4001dde731053002fe7724871013ef8605814102ff01050510035ec725911002ef4615054001ede634cb102a5bf7488540024fe7558c4100cfe705922107fcc424c93004eef7258b40006bc7458d1001cfe735912020ef764105100bef86058121126bd2119121004fd755884104ef8405834100cfe705913104e7c745974004cff7659132006ed52d893118edf3158f41005ed7210520014fc72d8d200067f32594411ffce72d0d320057f755813204cbe76d9131004fd7558b40005df7350531016be62509401e6ee32d8943004fd764cb1000cfc705874302cfc76d0e2108fcc324c94001cfc7358740004fd7558b102a6bf6110540186f621d8542005ef725814102cfe71d91301967c65d0510016ee624cb10006bc20d913100dec764c92000cfc7058b4301dee76d093214edf32d8d41005bf74581323a5bd7550d40036ee62d8910014fc74d894004ebd7319131005fb7050540014fd7458b40024fc7558b43004ff715913004dbe744cb40006df6350d4202cfe764cb10004ff7558b10096dc6358d40406bf649854202e7f3159441405bf7450a410067c65d8d102177465485101ee7c6550d102ae7e70d951004cff7650521024fe7558f400057f7559110004fd70d853201cfe7359110004fc765093101cfc7458343066df3258f10165be761912100cfc7059131005dd73d053119fcf204c930004fc764c540005fb7048510004fd76d0930024fe755912001cfc7359221006bf64d0531015ef734c921006f651d8532007cf624c9310067f31d9510006f4715913204ebf60d09402b67e41d951000df670d05100e67e658874004ef7415874313df57199110005bc745891002cfe76d85320247e76d9510024fc75d8d42006ed624ca4102e7e415944122df57588510006bf501912112edf3258c41024fe755922114ede43d8d41024fe755931004faf725094004cfe7688740006bc52d
  | 3 => 0x451d854202ef66118520004bf7458d2116ebd73d913104ebe76d0d40406bf6418542004fc7650530014ff7650a412b67c21d951016cfe761913119efa20d8132005df7358520166ee3258a41005f77158d4200cfe7058d21005bd744c94000df87050940004fd70d8931006bf6450521166bd72d9121024fc75d8d4102e7c21594411defa30d814302ff36048510004ff725824101cfc7358a4104e7c435974014cff7359131004ff7558d21306ec644c920006bd6419110004ff7058e2100cfe70d894302cfd73d813133ebd42d91200067f65d8910006bf51d913102edf7358c4100cfe70d91310befa10d81210bcff705891002cff705804102cfc7158e21004ff7059131006bf72d913102eef7258b10006bc20191310079f6350d40006bf745911016ebd30d9131006f751d8543004fd75d814301ebc6350f402d6f7764871002cfc7688540004ff765091011efa2058041006bd5458341004fd7558b410857e7599130014fe72d854013ef7105874000df8705051002cfe7650b10006bd5458740024fe75591301ceee76d093200df670d0710004ff7358740006be54d85402ae7d20d951000df4704c51001cfe7359310035ec7258d10005bf744c7402af7610d9510004ff764c910004fe76d053002ef4415824116ebf53d9131166bd71d91210247e75d8532016ec624c941005f97010530007eb704c920016be62d0940306dc644c930006f5611852006fcc434c920005f77158d20004ff7058b4100cfd73d89300057d7510520006bf64905301aefa60d8142434fe761913200dbe705094000cfe70d89310deed32d893102fe42150521006be42d913035eed32d8930006ed52d8941004ff73589101967465d0510024fc75d9121004ef7258d1004ebf4058c41004fd7650a31006bc3019121355fb705893000cfd72d9120126be425884102ef66118542006bd501913100dde704c93032edf32d8d20014fe7258e4104efb4058041004fd7558d100067e62d9510004ff7650931024fc755923101edc634cb41004fd71d8943006bc5219131006bc60191210cd7c7558121015ce72d0d32004fc7650d203ddbf7550f4002df47150a41005f4715813201cfe7358341167cc324ca41004ff7458e2112fb73119131126bf2119121005f77159132006bd75d913120fb442105103ee7d7059740006bf641053000cfe71593101acfd769912041ebe51d913130ded754c920006f551d85320079f64d0d3203edf31d8d10004fd72d913101cfe7458b4300cfe70d85420d6ed20d891001fcf724c9310857c75589300057f7558d1000cfe7158b1004e7d415974000df4708c510004fe76d0d2002cfe71d8d1041ebe21d9131146f62158742006bd5319121004ff75d8520006ed6250a41004fd75d8121006f751d8542006bf52d913102eec2158841
  | 4 => 0x52002ede3158c4133ebf42d9120004fd70d8d4100cfe70d89101ffcf21d0d32024fc7559310346f531d8530004ff7358b40005dd71d0d320067c71597401e7cc3259132004fd7559121004ff7158b40006bf50d9131004fd7558d2116edf3258e4100cfc70d8d41006bc60d913110eee3258a31004ff7650d2104edf7358f4031cff7358d200ce7e65487401aefa40d81420057d751913216ebf71d913100dfa7090540014fe72d85301dcff7059130096de43d8d40004fd7650910014fc725913116ebc30d913101eee634c921004fd75d891004edc4358f40006dd32d8131416be511913102cfe76d0b1000df470485102ae7c40d9510006bf73d912101cfd70d9130004fd73d912002ebe4159221006ef624c94004ebc75191311defa40d814304ebc6450521005ed70d093207eee32d8930185f771591210757e7510520006bf6458131006bc43d9121024fe755874302ebf7459221126be521912106fcc634c920004ff764c74016ebd53d913100df270d05100067c6599110004ff7358241006fb7058d20004ff755834102ef6768c510004fd75d8d4001ecc634c92101ddf724c93000cfe705912102cfd70d8910006be73d9121014fe764c52100dfa70d051002cfc71582412ae7c10d95100067c755911004ebe64191301c6ef20d894001eec634c92002e7e31594412b67e71d95100067c7558d202b67e31d9510006bf521913104cfe76d9131004fd72d8d4143eed72d9132007cf424c93041ebf73d913100df87050d40006be54d9130004fd72d814116f9c434ca4102e7c1059441024fc7558341004fe7650530016ec6250941004ff7258c41004ff75d8d4102cfc7159221005f970d051000cfe7058f41006ef624c94102cfc7610520004ff725834301cfd72d8132006f7619854300cfe70d853200df6704c51004e7c40594413f5f77158d2116ede4358e4100cfc70d913104ebd7519121006bd65d9131166be52d912102ebc4159221007cf434c921004fd75d9110004fd76d052041ebf64185431feec42d8d4200cfe7059231024fe75d8d10004fd755874304cfd73d8543006ed624c910014fd73d853212f9c434c8410757e75991200067c62d951001cff764c51001edc634c5213079f434cb4002cff7159310006bd51d913100dfa7010530006be72d9131196f665d071004dbc744c7400067e74d9510004fd72d8143004fd7610530004ff7358041006bd6519131004ff7058f42104ff7358d10004ff735874201cfc7358841006be20d91310f7cc3258532004fd75d8d42004ff755931004ef84058343416be2119131005bc74581320cd7e7519121004fd73d8520004fe7650d1000df476485100bdf57288510004fd71d89400067d7359441004fd74d893001cfd7458f40004fd75d8542004ff755823104efb7058342006f
  | 5 => 0x2eec2158b1012ebd531913113ebd4059310014fc72d8143096df3258343036ee325891001eec764c920004fd75d85401b5ed729913200cfe70d9132006bf64d8d21014fe725923101cfe73583420047f7558d2017efa1058341004ff7058b4302cfe715923120fb464d05100c5dc7358121004ff7258f41004fd75d8530004ff7458d21007b7744c510004ff764ca4104e7e4259740024fc7558f41004fe7650910004ff7558f1000cf676d0510004fd72d8540006f7619853202cfc7690530004fd73d8540006be60d91310067d654c74000df8704c51004fbb6010540126ef2058841006bd54d814100df6704c710016ee624c9100457c7559110004fd76d053001edf604c930006bd54d9120006bc42d911004f3d6590740004bf7458d2006edc6358d2006fcf314c9200f6ee32d8931024fc7558f10327cc32d813214ddc7358141005bf7458910024fe7558740014fc72d8d4004e7c4159740006ef625094000cfe76d0510005ef7258530006bc645813102ef46190540007b764d05100c7cf304c92102e747159441004fd70d8d4203df970985300beed2058b10017eb604c920004fd75d8d41004fd764cb4001ebc63d0d401cedc43d894302ede3158f10146ec6258941166bc32d91210067f3259740006bc62d913102cfc71d891000dbe7010540006bd5119131006bf7459120004df7359110005bf744c52102df7738851004cfc76d052000cfc7058a4101cfc7358341004ff75d913004fb67190740006be201913102ef76048510005f970905402ae7d71d951001cfc73d814102e7c7159441014fd71d8121005f57388510306de644c931017e7614c9210c6dc30d8d2100cfc74d814101cfe76d8d21014fc72d913002cfe71d894301ed4634c510014fe7458342014fe725913004ebd7019131096df32d8d40166bc4258a41145f5719912101cfe7458343024fe7558742004ff7259131004fd76d0d100067f73594412ae7f70d951002ef66118543006bf511913112ebd3019131006fb7059110004bf7458d100979f32d0d4004ebf7219121004fc7650910004ff7358a41024fe75d8543006dd53d8d21006ef625094103edf3258d10004fd7558343024fc75d8d1004e7d4059740006f76190540377b75110540024fe7558e410247c7558d10004fe764854002cdc764c9312a6bc415911002edf7358e210c6dc6358d210067c6558d1001edc634c510007cd324c52017ff270d051000cfe7458f40004ff73592211defa60d8143004fd7558b431dcfd7699130024fe755824100cfe76d814100df4704c71020ff170d0510015dc72d0d3200cfd74d89401acff705912001cfd72d853204cfe74d85300067f6559110005f47159132005ef72585400067c325974001cee76d093241ebf649854304e7e435974004e3c4259441004ff765
  | 6 => 0xf7359130014fe72583430067e72594410077765d0510004ff7558743006f7619852002ef67688510004ff764cb1004e7f435944102cfc7158b43006ef725912104cfc76d0910004fd764c84100cfc7059121004fd768c54002df47488510406bc71d912100cfe70d8d4201cfe735822102ebe415931037dbd751054000df470d051034ddd754c930006be63d912104eec4258b41017ae74d0932004ff7458a31024fc75d813202ef71058e210067e3059441406bf72d91210047f7558d1004dbc74485400ecfd764c51001ef4764c510004fd7558a31014ff70d912004ef74158740166bc72d9121307ac64d09320067f73597400047f755891004dbf7350d40024fe7558f10406be71d91210067f205944101cfe76d8d10005f5728c51002cfe71d8930014fd73d9132004fd7650d200067f715974002cfe7159221126bf32191213bdbf748c740007f370485103d6bf7650b40385bd759054000cfc765054008eee32d8940014ec725911002cfc7158d2023f74654c510024fe7558e2104ebc649053020df775d051002cfe71d894001cfc7358b4025df6768c51008eee3258342005df735891004cfe74d8d20004ff7458f1002cf47158d2002cfd73d9131126bc3219121006f771589100069c644c93102ef66118532146ee32d8941005fb7050510006be43d9121024fc755834302cfc76d0b1016ebe6390540024fc7559221166bf32d9121446ef42d8d42024fe75d891002ebc4159310006bf644c521005f771589431f6fa3058343004ff7258f10006bc64d8d21006fb7058d10004ff7650d200d6ef20d891002cff70d8d1004ebc6410530014ff70d8d2012ebe631054004ebf6050d40006bc6458121004ff72583410047f7559110006ef7258d1004cfe74d8d1004cff765051000575751051000cfc70d89102b77b10d951002efb1058221004fd75d9131004fd73d814202efb7058231015ee72d0521004fe7650931006be5459110004ff7558e2117ef676d0510006be54592212ae7d10d9510024fc755913100cfe70d8d41024fc755891001cfc735912012ebf53191310ce7c654851004cfe768c7400067d7059441005bd73907402a6be415911004ebc7219131004f77159132017cf734c921004ff7558f42006bc601913112ebc30191310067f31597402e6f7764c71004cbc745891002e7d1059441014fc72d8d41004fd76d09103ee7c705974000df47048710024fc75d913001cfc73d891004e7e4159740004ff7358841014fe72d9131006ed624c84104cfe74d813202fd4314c521005bf744854004cfd70d85402a7b66110540006bf21d913116ebd71d9131065fb705853004cfd71d814104fbb6090540006bf6458121006bf70d9131006f721d854302cff7688740005f47158d4202fe4214c521004ff715913201edc6350d42
  | 7 => 0xcb10007f3704c510126ee32588410eefa60d8131006ac644c9212c5f775d071000cfc705913202cfe7158e21346f631d853004cfe74d853201cfc735931019efa60d8132004ff7558221004ff75d8132004ff705913204eef4258b43006bc53d912102ede3158e410067e7059441336bf40d912002e77105944102fd431505311feee3258b43006f7715911002eee2158a31014fd71d8d2104ebf731912113efa10d8141006dd634cb10005bf745853042fcc321913204cfd73d81430f6df3258e2104e3e75191310067e7359740004fe7690530005f77348510024fc75d89430067c21597401b6de63d8d4201dde73d05312ae7d70d95102ae7e40d9510004ff7158b4300cfe70d85430979c6350d40006ef725912004f9f7350f4001ebc7650d4000dbe769054039dbe76d0940006bc6458d21006be601912102cff70d91102ae7f10d9510006be54d9121014fe765052119cfd73d8d202ae7e10d9510004fc764c941006bf31d9121004ff75d814300cfd71d8910006bc54d9121006fb705912000cfe7058b43006f451d8540016cc624c93104e7e4059441007b7744c710096dc53d8d4002e7f1059441004ff7258d10024fc75d8520006bc62191311e4ff725913204edf4358c41007b4744c51000dbc701054004cfd70d8d40006be52d9131004ff75d9120006de30d8d41004ff7458d10006f731d8520005bf7250f4002e7e105944104dbc744ca41006bc5019121004fd75587402ae7f20d951004cbc7458d2004edf4358f41277746510510006be60191313ee7d205974002cfe71d8142006df7359131006bf211913102df4715091004ebe711912101ef6634c710004ff7648540006bf3119121024fe75d812100cfe76d8131006bf6450531006f421d8530004ff764c540014fc7258341005bc744c521005f7724c510007db704c93000cfe70d8d1004ebe7219121024fe75d8d40024fc7558e2102cff73d913100cfc705923100cfc70d894304cfc764cb41004ff75d8930427cc321853201cfe765053102cfe715823102ebc415923120ef5641051004ebc7119121016bc7650940006bc50d9121306df64d0d3200cbc7650d40004fc764c940004ff7159120167b721d912100cfe7158f1004cff76d0f1002eee2158a4103fd7324c510014fe72d81410067f654c91000cfe7058e21006df638c52001cfe73d812104dbc744c8412ae7e30d951004ebd7519131004fd7558221245f7754c510014fc764c52104cfe74d8520036ec42d8910037cc324c910006be631912100cfc7158b100f6ee62d893102cfe71d8d4000df87048510005f7715813201cfe73587400067f65d0d1002cfc7158a4102fb674105100067c75589101e6ec42591320057d75d85320067d654c8410067c42d9510005f77150941006bc644c521014fe7258f101f4f
  | 8 => 0xc7cc634c921004fd764c9100befa20d81210067e32d9510166bc629054004dbe744c94017df77159110006fb705913002cfc7158e4104e7f74594411cfcc43d0932004fd755913102e3f4159441015de72d0d3200cbc7650940004fd7650d2104ef7715874007eee62d893012edf3058c41014fe7259131004fd755834200cfe7058a410067e3259441005f7714c84104cff7659120306dc644c9310beef2058b1002df4714c841006bd70d9121005f77150d41126bd201912105fcc324cb10024fe755834104e7d4259441406bc21d9121146ec20d8941014ec7258d100067f70594412c6f741d814102df47150b10014fd70d8520004ff7458d2001fcf62d0d3220df6748851004dbf725094030def754c92004ebd7219121004fc764853000cfe765051004eef4258b4108eec52d8940005bf7458d21006ef62d0910006ed32d8520004fc765093002cf47159132006be54593100067e735944116f9f32d9131126bc621054000cfe76d812104ebc645053102cff7158b10005f471589431adbd72d09400f7cc424c93102ef44159310006bf64d893102fb674d071001ede634c910407ac21d9121005f7724c71000cfd72d8d20024fc755804102df674d051001cfe76d053102ef81058241005bf74589303adbd75d0d4015ebe76905400f7cf204c93104cfc7458910006bc72d913104ebc425884104edf7358f4102cfe71d8d422af7471d951002cfc715823102df471d0b100857c7558530006df638c54002ff360105102a5bc7150d4014ede53d8d4102df47150d41006bf65d9131004ff74582310073d751913102ef764d07102ddf7754c710006bf7458d1001dce73d0932255f5758c510004ff75591202ae7f30d9510006be54592313ee7c1059740395bd75d0940004fd755874204eef7258b4102ebe41592310067d658c740006bc5319121015ef734c920004ff75d813101fd7614c9310067c7558d1011fb74010510014fd74d8d42006be70d9121166bd20d912104fb441505400067f305944120fb654d051000cfe76d813200df470d071001cfd70d893002cfe76d0e2108df97099120067d7324c710024fc7558d2102ff3604c510006bf5019131024fe75d89401a67e654c841006df634c94104eef7258b430057f7558930004fd74d813102cfd7158b10005bc745813100cfc70d894102ef71058a311aded7299120014fc725874300cf4764851013cff705911004f3d751054002dde714c931004fe76d0d2102cfe71d912004eef4258841006ef6288530095dc73585400067f655091004ebd7119121007776588510006df63d0d1000cfc7648510024fc75d853016ebe73d9131016de624c931024fc7558d201e6ec625894313efa40d81411567c6550510004ff75d891002cfc764c841015ec724c5213f7cc32d853202df6714
  | 9 => 0x465d0510004ff7648740006de32d8d1040df77158931005bd7310540024fe7558841006bf6519131006be42d9131166be6290740307cd72d0d3201cfd71d813102eef2158e2141ebe71d9131004ff755923102fd7734c51000cfe7059132006ef52d894002df4748c510004ff75d913216dbe7619131096de63d8d40004fd75d854300dbc7050b40004fd72d8d10005f572105100adfb70591303febc1019121306ec644c92100dbe7050d4002ef7604c51002cfc7159231006bf64d0510126ae321912118df7715913129df77158d1002cfd715931001cfc73d8520004ff755884101cff72d91323febe3119121004fd75d8940016ef604c920004fe764c54001cfc73591102feee32d85203febc511912102e7c315944104ef44158743006bc75d913104ef4415874204cff76d0e2102cfe76d0f103a5bf7550d4004ebe7610540004fd768874000cfc70d8d42006be651912104e7c42594412b67c31d951004ebc64d05102c7b654d0710006ef725911004ef84058342004ff75d8940014fe7258d1012f9f321913104e7c4059740024fe75d8542006bc73d91210067f7558d200edf5738c510004ff735834101cfe73d854004cfc76d0d1000dbc7090540006f5611853201cfe73d8910005bd729074012ebe4358c4104ebc4358c41006bf7458d20024fc75d891004cff76d0b1002dee714c921006be5219131005f77150a41006bd6419132196f665d0510005bf744c540006f77158d2101cfd72d913224f74658c510004fd75592210067c651911001f9e74d0d32006dc735891001edc634cb4002cff72d8d2100cfc7058b4120fb6641051002edd3158a3102cfd73d8931024fc7558c41005f4715893004ebc731913117ebd74d8540024fe7559121006ee20d89312ae7c70d95103bebd7690740106df30d8d100057f7558530006be60d9121004fd76d0d20006bd75d912100cfe70d8d2100cfe7058841004fd768c7403febc2119121004fd764874000cfe764c51004edc4358f42406bc10d91210047d75d8532006dd634c84100cec764c92004f3e751054016fb431d913136ebf43d9130006ed624cb10406be31d91210067c65d9110004fd75d8930005f77348710004fe765093028df575d0510406bc51d9121004ff71583420067d7259441006be65d91210eedf3058f1001ebc6350d40005f5734851002cfe715822101cff7658d20004ff7158f4204e7f4259441024fe7558b43014fc72d854004ebe731912100df6704851000cfe7058e41004fd764cb41024fe75d89310067f65d0910024fe75d9130016ec62d09103ffac2119121004fd75d8520024fc7558b10014fe76d0521014fd73d813200cfd74d8d4000cfc70d9121306ed64d093232edd32d8d2017dbe761054000cfd72d8520334fe7619120006bc42d913016ebc32d9131
  | 10 => 0x8931005bf7448510014fe725823104ebc745874002ff3608c510006bc54d91310067e63d95100047f75582410067d654cb4004fbb60d0d4012ebf321913100cfc76d05100067f65d05103cdbf7550b40014fc72d854304eec4258841007cf424c93129ef710d85300057d7519121014fc725834304fb67110540006dd634c91002e7f415944115ebf40d9110307cd73d0932004fd75d91200067f65d8d10004ff75d8542037e4624851000cfe76d814300cfc765094001cfe76d8d40006ec7258d1001cfc735824101eec764c92100777654851001ddf724c9313ee7f205974010edf32d8d21015de76d0d3202cfd72d8d21005ed71d09321fede76d0d32004df7358910004ff764cb400d6fa205822100cfc70d8931006bc40d9121004ff7058a4104cff765913001fdb604c9301fedf32d8d42004fe76d0d10006bd65191210067f6550d100fe7c654c510006bd54d854012fb43119131007cd324853002cff72588413ee7e3059740005f57348710024fe7558f42004fe7650d21314ff7258d20004fd70d913204ebd7019121006bf645893100dbc7050f402f5f575d071004e7d435944101cfe73d9130004fc764c5200c6de63d8d21004ff75d854300df67048710006f5611854204dbf7650b40005bf744ca41024fe75d8d41005f572d0510006f5611854002eed2158e21006f76198542006dd634ca4100cfc7458740005bc7458121004fd72d9130006df634c521016de624c930005bc745853202edc3158f10007cf434c920006bd641912001edc63d0d10004fd72d8131004fc7650d210757c755852004dbc748874017ef710d8540007e76248510004f77158d2031edf30d8d2004cfc7458d2004ebe7319131007b4744c710006f47158d20024fc7558241004ff75d81423bdbf7590740006bc50d91311ddbd73d0d400067d75d85321aefa20d8142005ef725911004e7d7459441004ff7158d20006bf6458d21127b72119121014fe7258241004fd768c52007dec725853004eec4258b4341ebc71d913112ebc3219131024fc7558b40006ef6288540004ff7558f4001cfe73d91210fe7e654c740006ee20d8941006bd65d91211ffcc329913204efb405834104ebc75191210067f7558d10004fd74d891004dbf75d0d4014df5719913100cfc7650d4016ebf32d913102ef7601051001ddc7350531004ff75d8d10024fe75d81431cfce73d0932004fd73d8910005bc7458930024fe75d8d4202cfd72d91213ee7d10597401b6de43d8d42005bf744c84100cfe705874300cfe76d814204e3f4059441004fc765052004f3e6590740004fd7558f410247c755911002cfc7158221004fe76905200067c655891016ebe6390740004ff75d8d40006ef7258d20004bf745891002df576d07100067c72d9510024fe75d8943006bc64d8931196f
  | 11 => 0x24fc75d9120126bf201912104cff76d0910004ff75d854004fbb60509401167e658c740015ec7250d42004fd75591321e6ee42d8943004ff725874004ebe721913104e7d4259740307af424cb40015ee7210520024fc75d894112ebf311913101cfc73d8121346df32d853002cfd70d9110166bd32d91210bcfd7648510325fb7058d2019fcf304c92001cfe76d8d20024fe75d8d20005bf7350b4004ebe641911004edf4358f402ae7c20d9510004ff745891002df7758c510006bf649911004cfc7458231004fd74d85323ee7e105974002efb105824104ebe7119131295f77158910014fc7458f4240ef631d85323ee7f105974010cff7358d2104cfc7458d2101cfc73d8941166be72d912100cbc7458740004fc764c910006f410d8532005bf744c520166bf20d912115efa405824102df47150e41006bc5019131024fc75d85321b6dc4359132005b47448510007bb7050940024fc75591200f6ef21d893120ef764d0510005df735814144edf43d894316ebc4358e4107fcf214c930006dc73591100bff07048510004fd7559231004fe764853001cfc73d9130005dd70d0d3200dbc70d0d4002cfc7688530146bf425922102ef6761051002cfc768c540024fc7558221146ee62d8941007b76190540006be30d912104e3e75191210067c205944102df7758851004e7e4059740005bc7448510024fc75d91310057d7519131004fd72d9110004fd75d8d1001ecc634c92001cfe73d9110004fe764c520126bd5219121014fe72d8d2001cfe76d8d41016ec624cb41014fc7458742004ff725874306edc31d8d2004cfe76d9120004fd74d8d20006bf75d9121004fd7610520006df6350d4112ebd3119131016ec624c940004fd73d8121004fd76d0931014fe7258c41006bf649912001ebe63d0d40005ef724c52102cfc7158841024fe75591320079f434c94002df471d0f10006bd54d913015cfe761911004eec4258b4001cfc735891016ebc53d9131006bc7458d2002ef7105884141f9e31d9131014fe76d894102fd7734c71004e7f435974004ebc711913101cfc7358041024fe75d853200df4764c510014fd70d9120006be54d9132004fd755823100cfc7058f420067c7558241006df7358d2104efb70583410057d759911013674651051002df7734c510014fc7258740004ff7458b1002ede3158e2100cff72d8d20014fc7259110004fd70d8943004fd75d8941014fc72d9131006f731d854204e7c42597400757c7558d2004dbc744c5401aeef2058b400057f755812100dbe709074004cfe76d91101cfcf31d09323e6bf7650f4002eee21588411e6df3258f42014fc7258041006be54d9131006df634c94008eee62d8940004ff75d8d200067f72594410067c7359441004fe768c52005eee3258b10166bd52d9121004fd74d
  | 12 => 0xd71d913202cfc7458341006bf64d0d210067e205944104fbb60d09403febf1019121014fc7258e41004fd76905302ae7c71d9510306ee644c92104e7f4259740014fc72d911002fb44150510004fd7558e2104faf7250b4002e7f715944101cfd74d89432ae7d30d9510004ff7059121005f77158930005bd739054004e7f7459740436ec42d9132014fe72d8d4104ebc4158341006be40d912100cfc7458f40015ec725052114ebf435923115fba7090540006bc65d9121166bd42d912101dec73d09320067e325974001ede634ca410057d7510530004ff7648530004fd72d8d400067d73d9510007d4714c93102cff7158f1002cfc71d91103cdbd7550b40005bc7458d1001cfc7358b4116ebf31d913102cff72d91210067c65d8910004fe76d093102cfc7158b4004cfe74d8910024fc75d8931007cf624c930006bc40d913202cfc7458b410067e72d951000cfd745804100df67010510005bf745893141ebc10d9131016ec625094001cff764c521005ef725052102ef7608c510014fc7650d42004fd75d8142014fc72d912004ebc629074004ebc6390740024fc7558d1012ebc531913104ebf6090540006bd5459221095f9709913018ef631d8543146ef21d8941006bc651913104f3d6550b40006bc40d913102ef81058041006f451d85433bdbf7488740007d5324c5103ee7f3059740024fc75d8540006bc651912100dbe70d0d40017cf734c92034ddf754c930004ff755913002cfe71d9110016f47648510004ff755922116ebe4358e4104dbf7650f4004ef840580411c4ff725912004cfd70d8940146bd425922102cfd7158f10004fd71d8132006bf745913214ef63158743014fc7258c4101edc638c54006ddc735852036ebd43d9130004ff7558b410f6ec20d8931024fc75d8940004ff764c8411f6df30d8d4002e7e2159441024fe7558041126bd321912100dfa7010520006bc65d913104ebf6010540024fe755823104ebc64d0d21024fe7558b4102cff70d8910024fe7558b40146ee325874201cfc73d8940016ec628853002df7764c710006be53d912120df6748c510007ac644c921004ff75d91102ae7f40d951004ebc7219121016dc764c9302a7b46190540005f97010520004fd7690520005ef7258131014fc73d893002cec764c921006be65d913104ebf4058f42024fe7558343006bc645893104cbc7458d2102cfe7650e212b67e21d95100067d7359740004fd74d852021df57548510006f421d854302cfe7650f1003ede63d8d10004ff7058e41014fc7258d10006be75d9121024fe75d852002cfc764ca411fcff7359132007af62509400457c7558910016dc624c93100cfe7458b4001cfe735912141ebc21d9131005f572d071004e7f4059441006be301912102eef7258a31004ff72593100067c74d9510
  | 13 => 0x814304ebe5458341416bc1019131004fd755931002cff7358c412cdf57548710366bf40d91301ffcc42d0d3204cfc7458b10136777159441146ee52d8941005bf7458131004fe76d093004cff76d0a31166be62905400067c65591100857e75105302a5be71d0940016ef63d0932364fe7619130436dd73d9132106dd30d8d10024fc75d8143007d5324c71002edf7358f1004cfd72d8d42005f77150910004ff7059231004ff755911000cfe70d9121144ff725912127df57510510024fc7558231014fc7458342004fd7559120005df735854002df77648710007e53248510127b4211912102ddc764c931167ae32d9121014fe7258f40006be5319121004fd70d894104ebf4058b43126be6210540024fe755891004e7d74597401ffcf20d0d32166be32d912102cfe76d8540007b56110540004ff7359121024fe7558221004fd75d8141096dc31d8d40004ff75587400067c73d951020df4744851004dbc748c740004ef72591102a7b4511054000cfd71d8d100eedd3058f1001cfe7358841024fe75d854002cfc715912001cfc7358b10006bd54591100067f6558d100067c315974004ebf4058841004fd73d894019fe8704c920004ff755874201cfe73d8142004fd75d893120fb44310510006be6519131014fc7259130006bf75d913104ebf711912100cfc7058e41014fc7258f4104ebd711913104ebf6190740006ed32d8121416bc2119131014ff764851001cfc73d85402a5bf748c540006bf7458d21004fd73d8141004ff7158f40006bf649912129cff7158d100f6dd3258e21005dd7310530004fd7558d20024fe7558d10014fc765052104ebf701912104eef4258b40024fc75d8142004ff74582210f4ff7258d2102cfe76d8520024fc7558a4101cfe73d8940024fc755874302e7d7159441145ec725814141ebe31d91310067c63d95100c6df31d8d210a7cc324cb40007af644c92104cfc76d0d210067e71597401dedf3058f40005b47448710006bc43d912001edc638c52004cfc764cb4004efb40583430f6ec62589313ddbd7550f40006bf7459130004fd76d0f10167b421d9121004ff7558f41014fe72583412c6f576d07102a6be41583413bebd61907400067f65991104179e311913103ddc735911002ef47159310024fe75d8941406bf10d9121006df73591323ee7e7059740006bf30d9121004ff764cb4115ef571d9110004ff7558d200f4fd764c5210067e725974004dbf7510540004ff735931001ef6634c5100f6ee52d893100cfe76485100057f7558141004ff75d89312a7b9709054002edc3158e41004ff7259231004fe7688540014fe72d8131296f710d85202ae7e20d9510014fe7258041006be10d912117cff715911004ebf7319131024fe7559110004fd75d8d20005bc744c52004ebc4158740004f
  | 14 => 0x2cfc71583423febc311912107fcc32581322c5f4744871016ebe30d913108dec7258540024fc75d85423bebc41d8141024fe75d893016ebc73d913100cfc7058a31016e46248510036ef21d89100067f7558910006bf20d913101dde74d0d3204ebe641912011fb54010510166bf42d91210eff0704c510006bd70d913101edc634c940005bd744cb4004cfc7458a3114edc30d8d4104cfd72d8542306de644c930306ef64d0932014fe76d891002cfd74d8941416be31191311e4fd76991320067f6548510004fd73d8542004fd75d8d2111efa30580411def86058143016be6250b40004fd7559110004ff7058a31006bf7459131016ec62485100067f72d951004f3d6550f40006bd54d912114ede63d8d410057f755854000cfc7058742014fe725911002ef81058231006f7715913101eec634c9211a67e654cb401a57c755813231edd30d8d20024fe7558d200c7cc434c92101cfc765053119ef8605813220df6744c510004fe764c941014fe76d893102e3d415944104ebe6419132007d7714c931006bf54d9121006df7358d10004fd74d813201cfe73d894101cfe7358b1004fbb6050d40006be75d9131016cc624c93002cfe71d8910004fd71d8d42004ff7258e41006df6350d400fd7c7558131006bd6419121024fe75d8131006f610d853204e7d435974003ddc7358910004fd74d8121004ff7558910006fb7058910004ff7558b4326fb643105100067d7259740004fd71d9130004ff75d8141336bd40d9120005bf744c51000df47010510004fd74d8530004ff7558041006bd52d913101cfe735891002eef7258a41005ed72d0521004fd72d8530005f77150d1004ebf7519121004fd71d814202cfe71d8d20006be76191210d4ff7258910006bf3019121406bc31d9121016f6624871000dec704c92000cff72d912004f9f7350d40024fe7558d21006ef624851000dbe7050b4002ef4624871001cfe73d8520006bc7458910006f77158d200eef8605813104ebe6419121024fe7558f41126be321912107eec625893004e3d751912101fcf724c93001cfe73d9120006bd73d9121004ff7558d10006ef7259132004ff7158343004ff7650b1002ef465d0710014fc72d8d1001cfe7358241004ff7358221005bf7458121166ee4258a41024fc7559121004fd74d8d10004fe7610520024fe75d9120006dd6350e41006be43d912004ebe54587400067c3059441004ff7559121416bc51191310079f644c931014de76d0d32024fc7558e41004fd74d8d21007e7714c921127ae3219121004fc7650d103bdbc7150b402ae7c30d9510004ff7358b10007bb7050d4002eee2158b10007e4714c921006bf7459121004fd7558c41004ff7258041005bc7458d2141ebc51d9131006be50d912108eec6258940005bf7250d4002cfe71d
  | 15 => 0xc654c910006bc43d9110006be40d91322af7771d951002ef4634c71000df6708851002cfc76509410c6de53d8d2101ef6638c510004ff75d8532006be10d913104ebc6450d2100dbe70d09402067c65d0d10004fd764ca4110edd32d8d2100cfc70d9132014fe725874302ddc714c93102cfe76d853001cfe73587422877465d051013efa60d8141016bc62d0940014fd70d8d2004e3c4359441004fd72d8543187cc324cb4100cfe7058c41007cf634c921005df7358121005f77150e41005f77150f1013cfd7650510006f751d854004ebc701913104e7f415974041ebf10d9131006bf64d052100cfd73d8530005bc744c510004ff7358b41024fe7558a41004ff75d8d2101cfc7359121006bc64d81210befa60d8121024fe75d8141005fb7050d40006df7359130014ff73d913201cfe7358a4114edc6358d4102efb705822120ef74158241006f5611854302efb105804101edc634c941006bf641052001cfe76d8d4204cbe76d91213bebe41d8141004fd70d9131006bf6450d21006bd5459310004fd76d0d2102e7d215944104ebe701913100dbc7650d40294ff71589103ee7c2059740024fc75d8543006bf64d8131006de30d8d21004ff75d8943004ff7359110037e6324851019cff7058d2004cfd73d894302cfc7650d4100cdc764c9300067f21d9510004fe7610530186ef2158b4104e7c7459441007b77448510004fd755913005eee32d81210057f755813101cfe7358b4100cfe70d8520024fe75d8132014fe7258f410067c7259441024fc75d911002edc3158c41004ff764c52004ebf711913104ebe76d0940004ff73591203b5be76d0d4004ebc6450510006bf6490520007776510510267b642105100057d759912020df6744851000cfc705884104f3e6550b4016ebe53d9131014fe72d9130016bc6250940004ff7650d10004fd71d9120006bd545923101ef4634c51002cfc761053016ebd32d913143ebf43d913202edf3158a3102df47150d101e6ee62d8943024fe75d8142006bf64d812104cfe74d893100cf4764c510024fc755913200cfe7058b4102e7f2159441004fd75d912104ebe75191310079c644c93104cfc7458221006be5019121006bf64505102bd7e76d95100057d7599130016f66288510004ff75d8d423ee7f7059740005f77150b1002cfc71d8d1000cfe70d911000777654c510164be761912116ebf43d9131287b554d0510004ff7558e4102f757510510014fc72d8131007e5324871004ebe7019121006dd53d8d4104dbf75d0940004ff7559131014fe76d8930004fe7650d20016ec624cb4001ebe6350d4001ede634c84100cfc764c510006bc75d9121014fc7258f4001cfc73d91212a5be71d0d40007cf634c92004ef44158740004fd73d894104cfc7458f10006f431d8520004fd70d9121
  | 16 => 0x9740006be43d91100067e75d853207fcc624c930005bf744874005fe63248710106fa3058231004ff7058c41005f57310510006be10191311be7c655091002cfd74d81410053d7510540005f573d051001cdc7359110006bc64d8131006bc6319121227746588510004fd7558f4200dee704c92002cfd72d81211aef8605814210fcc329853205dfb7058520407ae21d912113ebf405931004cbc7458d10014fe72d8543126bc2019121006f77158d10024fc75d814104cfe76d913001cfc73d85421f5df73591302c5f67448710005fb70509400067f73d9510005fb704c5103ee7d3059740126bc521912100cbe7690540004fd755891002df47150f100c7cf314c9211b6dc6358d42406be21d912102e7d41594412efb554d07101afb87050940004fd75d853212ebe531913104cfc7458e2104efb405834200df6708c510166be4258a41005bc7458520006bc63d9121014fc72d853002cfc7458f410067f6550510166bc52d9121016ee624c84101cff70d9130016f46288510004fd70d8542024fe75d912114edf325874304ef771587420067f72597400057f7558d200073e7519131006df53d8d4011fb7101054002cfc769052001cfc76d053112ebd3219131006bf65d9121006f7715912104ef771587431e5dd7399132066df32d813100cfd73d913002cff768c7403079c64d0d3200dbc7050940004ff755834202cfc768c520016ee624ca4116ebf30d9131006bf2019131004ff7058742006bd5019121004fd75d91320f7cc624c931005ef7258d10004fd71d8d4001cfc73d912041f9c31d913100df47088510146ee42d894114ebd4359231014fe7258740007cd324c52104edf4358f421557c7558141166bc20d9121006bd641913002eef725884101ede6350e41006bd5219131016ec6288540006bc42d913120ef564d0510007d7634c510436bd42d9132006f7619853019fcd304c920437cc32d913201cfd70d85300063e43594410067d72d9510004fe76505202c5f6744c710004ff764c94102f76751051004cfc76d093002eec2158a4100cfc7458b4012ebe301913102dec764c92100cfe705874202cfc7158f420067c7259740024fc75d91320247c755891002cfc7159132006bf6450931006ef7258d2104cfe74d8131015ee74d0932014fe72d8d4004ebc73191210067d6588740005bf7458d2000cfc7058d2101edf62d0d3202cfc7650e21006df7358d200467e76d9510004fd7650e211fddf7359132004ff7650930006be40d913104cff76d0d20006bf651912100cfe7058f42006be54d8141006bf6499131007af64d093202edc3158e21006be54d9120307cf43d093200df87050540006bd50d912115df67610510005b4744c510004fe768c540004ff75d913104e7f4059740007b474485100073e75191211a67
  | 17 => 0x180020000060c002300002400100100600f00200601200f0270010070000000040000048ba00c0600280341d700008d05a01900100300300000009206305c01501c20000000202100204200000600a00b01800800f00808a0010020271810140331850000030e50070c300100000b00d00f00910c0067f142a09b00d00a00b00000800500004501701300300000000400700002c0a903f01200000b01400500d02305400e00300411100f01b01101001a01100000000b02f05b01201d00000000002b01701613e00236d00c00400000001200802500d00000004003504902501721606e0100000c32d400300702f0c00100030380030010010170011d500b01900402605e02302a00000200301d17709200700302308000400100100b09608d0481ca00700000201b00a03c03801500f00201e02e07300302100004602001805905b0030093c800c02100f0000060140090400120980010001ab00308401200003401000c12c00100d04200002c00000401c04c0c200900600221900000003200800000004000106f0a70f500006500100200900005900f01601800002d00d00002106c07d01502a02902f00302504600500001701100609f00505406401400401502500302490300b01e09305a00000c0bc00002403709500003600403514f00c0873440000000000010ec00001a0000040d20080272810030160400032d702f0020010cd00001000109703701900201700903100001c02607f02202502612402e00d09600b00200a02701801101001800000700b01504300201a00800200500800203801801802101c00300a00c00003800805504300101e00000800300209303a03701200500500102902500b0010052b800f70a01300200900b008031043132024fc7559110164fe76191213c5bd7590740406be51d912108eee42d894001cfc7458743436bf42d9132004ff75d8121014fc72d814119fd8704c930006f7715913204dbc7448740005b4744c71000cfc7159310014fc72582413f4ff7158d2100dbc7050d40004fe76d0520147cc324c9413febe211912100dbc7650940004ff7650f1004cfc7648740006bf54d9131004ff735834204ebd72191310063e4259441004fd75580410f7cf214c931006bf64d0931007b77448710004ff7558b40016ee6250a41166bf52d9121004fd764c740004ff7058d2102eec2158a3102dec714c921416bf101913104efb705834304e7e7459441006f761985403ffae211912104cff76d0d1004e3d751913119efa30d8132167ac424ca41315ef7258d20014fc725931016ebe32d913102cfe76d0a3100cfc76505103ee7e2059740024fe75592312c6f441d814107eec21d893000cfe7058a3100cfc70d85422a5bf759054002cfc7158a31004ff7259130005f47158d20004fd768853004e7e745
  | 18 => 0x5c17111300300000601b00900303601100001400900000000806c13e14000500900000000100000400700901e01b0000330090000010a70dd00c00001400b00108400f00200e01904d02600003f00000301e00004c08a0020070c200c00f0230090b202700601403c0000030098ab00101300000f01e0070010350b507501300000e00000007e00001c00600001104547501601900b3b50020100490df00600b00000517e00313d0ad01b00103400000703902c01f01d02d0150040ba09303403f00201100100803a05d0170050010010fc00a00000f0010cb0020080ca02800d17f07105100806800c00c00034600206400001650335501c02c0710000f204000d0090da03f03d00406400a0cf01a0010060130e900005f00e03c0010050020130010000000023f00000bb01e02b0bd00309600001000f00000007601101700e00700100300801b01c00600803e01500000500900000010304701100500000802e00c00100004800e00101900a01200601a00911e04c08206c01d0ac02066c00001400201e01601508300900f00100b01601a00200100700100000200001301b1c002808801700001002f00502100009300300114400203f1a402201f15900002509d00b00201606400e00b00338b01a09d00000700000200500300a00100300000a00400400515700700200a00300300f00004400302407c04c00000303701000000902f01005507103700103655d0320010000160130e21530000070010d300a00400e02702000200d02400c00100202401300000e00200f0740184fc00003500000500c00002e0000f511c1af00303c00602a00d00208903e01401500408302a00000100700c00800002b00700008207f00400802900000500005d00608500200308401c1b310a00400e00a00401100000300000306600702e00700c01c03a01403b0282420000040030030a50452f401900e07504a44d03506400a00101c00d00000c01d00100f02a00092f0000040040270050090280170023c402321000001600201301600206700200151401e65801700301300800700203915902b00700105500001e12700e0090070140000000260040000f800b00200e00c03903100000201100008c00b00100200800700200200001021704c00200100005c03f05d0020054bd
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa3e849c965d00055cd0db1242880022fa1c64589310051ec2062b2e8000c3c651d1314400117d0e322c0988023be0976509100061f32ee890e8000a5e8318b654400317908bb463a0016ad20554592210045fc3ac83224200ccc73dc962440090fd0bbb284880121f21576905200051f41486b28822c8bf865ca41d00015a906b08c2900270f19175105300051f42e623224200ab5810c364484010ff0abb286880028f60242594410051fc2064b288200c3f65dd163440014dd0431eca88002aba0a65191310243f43eeab1a4060e2d851913248401a6a80ba88288002a7a0c50d912130747c18c899242018be86dd1215001317908baac690003330c8764c9103bdd9c02c820a2089e1c43cc96510401878ca3a2c4880023be09768c54000726192ca996808dcac72951644400147b0a216c8988163da0775d91324071b88484b288209c3c645d4644840153b07908c89880a2f21176d09312655ac0cc03224200a3e85988644c4af8eae232ec88820b271d8644c9310069a328e898a2000c3c75191604c40159d0da1a64908028f616621913104d1f42440b288294ab78159464484011ef02baac8880123de1d51d853202477c3aa5b1282018f4865cd21440091df0ea96c4988169da06305944104c5e422eab188200ab58194c644840147b0810acba01feada0430191210061eb2ee89908200a75819c965d00018b8ebb9ac888002ab20964191102ac3e436eab122080ab6811436448521b4c643a24388092aba0b31191210064fb26e6b02427fab68194064484011f700baac8990031d1977150d100043ec3e63b2a2000ab581080644c4011bf06baac8902868fe11735944100636b90e4b2e8000cac74d8921440011bf06baac4880023de0574d81320061e3aee8b1a40008ef825d5644c083a6b0a3a242880270f1d1654c74002c7a40aeab244200c3c751d16244001878ea3a2c6880029b60870594413759a42ac220a8000a3e85cc7644840b1d90eb126588003271cf645812101e6639a65b0242008be87d91624c4071db05baec8990029b60863d951000556c10a03226200ad4864c931440018d8e5b2ac68800297a0c72d95100045fc3ac83226293cb77119163484031ed0db8a86880028f61332594413054e422c69922000c5f751cd644400759d07b1264a0892aba0b511912112d4f41e423226200c6c65dc9634400559d0db1264988262f2117558d100054ec184032262008be87083644c401968e838ac6900030f9d9751912104e563a2c49908200a3c845cb65440ab0fd0f90eca880029d6063059441006d23a6c490a2009a3e84dc965d01414ef02b9aca208023de1d61185200051ec2464b288280ab6810c364484011df04baac8880063d60676d0d10006e2190e2b026400c6c72d9564440031eb033b68488002a760c50d9131
  | 1 => 0xd0fb2286908121fa1b755891004c5f43ea43226200ccc731c9644400117b0f086c8988062f219744c94002c7c432e020a602cea462dd121440014bb06102ca208262fa1c301912120e9ac28e898a2060e8f82191324c40b4ed03382ca2080f331cd32d85200062e3aee6b122024aae8214064484090f90abb482980262fa12764c5200166639265b026283ab681143644c4018deea392c88800b331d9324c5210071aaa6a3b0a8005c77605d441440010fd0e102ca208268fa10705944101c76c16ec996820087f855c3644c40147b09102ca208030fd947458d1001d6641ac49962000e8c644c93148483a6d0a3a262880163721d634ca4100556c16603224200a3e85c87644c4019c8e5b8ac6880029ba0a43d95100047bc3ac230a80098be87dd163484018bae639acba00034dd9474485100045ec3ea7b224200c3c751d163480011df04ba6c6880030fdd764581310146e41ae9b1260008df835d943440018beebb9ac4882038d94751d912102e6a38ac69908260e2e851913248401b60e9b8262880031b1c86558d100070f41c84b28828aa7686d94414400147b0b31ec890803631d1324c5210146e43ac69922000a9e8314064484090f90ab86c8990021fe1571d894016d4f41841b226209a3e841c565d010756f08b08c2a1802a7a0e42d91100047bc0aeab226205a74815cd651040147b09192cba000a3d60775d912104e1e3a2ca90e8000ab5810c0644840187ecbba2428820eada0420d91310045ec3841b22620097787d94414400153b07290c898983a3193424c93104d1f42040b288200ad5830876150c090fd0fbaac4880932b18874485100046fc1aeab2260419b4845cd214401317d0e280c8988163da0775d911004c5e422eab122009a3c845cd651044b53d07290c8989074da14744851004d1f426e4b288225a9e83148644c40155b09a96c4a0002ab60850d91210063a3aee2b1a4000a5d831cb65440010fd0e32ac8880262fa12764853041c5fc22ec98e8000ccf731c964440014eb02182ca20803930cb654c9100052ec18e0b288200d94744c931c400117b0e186c890802ad606521913102d3b40ce4b288200cac72d91604c40117d0fa9ec8908262fa1e10191314071a38c84b28820087e871d56244001938e6322c0908031b1c8655911001d6641ac499082008be87d9160484010fb0e21eca880030f59774487400045f438a1b22422d8be87843644c4031e902baac9880022fa1c30d912116557410a1b224226c77865d44144001d48c9b8a64908023d60775d9132266d2310e890a2000ae4864c921440ff56d03180c8908023be097650d100062e3a8e6b222000e374119464440014db0521eca88002ad60650191310051f42887b2242058f4815d563104018becbb9ac488002ad60450191310061f3b4ea3224209
  | 2 => 0xc744c5100045fc22eab2242028dd83dd7644c907938edb226498803710cb71591322a61fb0aea20a80018f4815d942c400117d0e322c09080317dd473589104055b408e1b22420487f875d7614c80b8e8e2b2a6420803331d9324c5200045fc22eab1a42018bc845d561d000117d0e322c6908023de057558d2001476412eab2220778bc8755161d00ab8e8edb2a6288002ad60450d91210065a3a6e2b1a4200c3c65dd1214409d4eb03382ca20a638ddc642594410061f31aea20a80058f4815d9321051f8eee232ac8880932d1d874485101353ac08e0b2882008f7875846150c01b28e9b1a62881522f61e54d854004c5f43c2032242098bc871913148401b48e899243880962fa1f644c5214664e39aa8b222000c3c75d91604c40153b06280c898a7b8ddc643594410043f43887b2a2005a76811c165104010fd0e3aac8880029da0673597400051ec2887b22420087e8710b654400317908bb243a0002a760c52191310043f43e62b2e8000c6c751c9644400b1b90eb1a65880021fe15769052016d5ac0eebb22620487c855d9424410147f03212ca208121f21576d0910005674368499260028de87d8d32500051d904baac89800327dd373589101655ac0eebb224200a3d85c87644c40187cc4ba882a00021f61776509100051e42ae1b2262018bc845da21d00014db0539acba0017391c5624c84112752310e890a2000d8c321d1614c80147d07212ca208131d9d651d853204e9db02ea20a80018f581dd7644400187eebb22c09080e37a1f73591100063a3a8e2b1a40018be84dd932d0001d28c838a64988b2ad60470d91210062e32ee6b122000c9f741cd64440010fb0bb8ac5a0016f1205324c5210066bb98e2b1a4000c3c75d91604840147f08b9eca88202ade1161185420055a40aa9b2260008bd87d4b644c4ff96ec03a242880063d20574d81214471621464b2882008bd87d48644c413878c8ba8c89880e3720d765091000747980c8992420487e851d932500091790eaa2c8880029da0672597400062e39ecab1220008be87d9163484011ef02bb286908030f1977458d101665a3b6e890a2000c3d751d764484011bf06bb442a00062f211764c74000656326e4b02629ca75819c965104018e8cbb8a8488097a518c744c51000572c1063b0a4000c3d75d904148123b2e643a263880029d60420594410076299643b0a60038dc835d562440011ef0eb08c2980022fe1176509103751ec24e0b288200e8f31191324840156b0828ec2a00030f189751054004c5e422eab1a4200a3d8598c6448413c5d05212ca208122fe1d54d91200063abaea3b0a8682ab681880644c40187eca3a2428800a37a1f634c9410047dc02eab1a42008bf865d132d00011ef0cb9a43880030f5d764991200043fc2ae3b12605687e871d5609040717
  | 3 => 0xc992208bcac7255164440c155908b1264880039918b65485101351ec26e4b288258d35851d121c40010ff0ab86c8908032bdd0725911004c5e420ec98a80018f681dd932c4001d18c7b226490803530c975d85323fd5b40ca63224200ce4621c5624c001d1e4232264988023de0575591210045fc22e3b0264008bd87994644c483a6884ba882880169da06205944100673b90e2b1a4000aae82143644c4090f90ab8ec4980268fa1270594410064fba0e6b122000d8c32dd1614c8f747b0939acba01de6d205744cb4016e5a3b6e898a20018f4815d943c400155b04286c89880333dcc7258d1000746326c49926200cac72191604c40717908bb686908022f61c50191312a6d820ae1a0a2000c3e65dd131d0001b18e899262900130f9d554587400062ebaea7b1a8000c5c7319562440ad4ed02396ca8800ab3a1b624c93020e9b322ea20a2000c3d65dd131d0001d48c838a64908262fa1f745891000637b2ee4b222079a3d849c965d00014dd0418acba02028f60642594411351ec26e6b288280ab681dd764484031eb03ba2c1109066da1f744c5100052f418e0b28820087e870c165104071d90eb1264880270f1d1654c8410053b42e43b0a86039ce835c7424c89f2e90cba882880b2aba0830d91210045fc22eab1a2000ab481553644c8c1c3b0a32264988163d20575580410051e422e7b2a200487e87dd5644405b53d06286c8988022f61e651912100637baee4b1a2000a6e820c1651040b1b90eb1a6420802ad60650191210051fc22e5b2a200487e85dd932c400195ee9b92c68800387d4e53191210055ac08a03224200c3c651d1214400156b09a8ec2a0002a7a0e65d91210051f428603224200a3e85080644c40117d0fb22c0988268fa1332594411645f430e898a42098bc845d93244001d1e403226498a0b6cd80744c51002c7643ac4990829dc7471dc9651040155b04280c8908022fa1f52d913100556c14a6322420087d87c8565d000117b0f080c89080e3720d76885400055a40ac832264018f8805d56348401878ea322c09085a8f610715974012e4e318e898a2000c3c651d16344001c3b07212ca208b6ad60470d913104d1e42064b2882018bd849da2150001a68ca3a2428800e3720d75591200043ec2eeca1a20008bf875906448001b886438ac89920e8fe06435944100c7b436e2a12200087f855c763500018b8ea39ac4880022fe117558d2000556c16623224203ad686d8d314400117f08bb28690803271d3634c510134bb42ee299082008ef825d9324400559904b1a65208030fdd4645812101d67436c69924200ace86d0d3248001c6ecbb2682880028fa1430d91212a6d820ae120a800087e8719563441251ef02baac9881063d61f619054000477c12eab1a2009a3e8408565d000117b0e180c8909376518
  | 4 => 0x4484adc6883b2a82881626d21173487100047ac0eebb224000c3c635d441500011ef0eb08c299003651d1324c51000556c16a232242018fa86dc1214400b1d90eb1265208021fe1576d0d1041f1a38c86b288200caf741c9634405b17f0cb9c83a00028fe1570d91210061fb2ee8b122009a3e84cc965d000987ceaaa6c0a09634da14744871041f1b88486b288200aad8214c644840199ee7b92c88800ab3209634cb102a69a40aea20a80098bc845d5621040b56902aa2c9188270f19175991200054ec1841b2262048bf87553644840b1e902baac69000a3ba1f7258d1000716c1486b288209e1e8390d651040759d0db1a649000317dce73597400046fc1ae9b12204dab581980644c4c1c3d0a322649880287a0e42594410061fbaee8b1a4026a3d841c165104c1c5884b2a64209530f58575105400065bba6e2b1a4083e3651d47644c4051bb07bb265a08021fa1f65591100053ac0ce6b2e8000a6d821cf654400153b06280c8908022fe11755891012557414a6322422d8be8719131484654ed0db2e82880b22fa1e10d912104d1f42060b288200e8c64d8d32484014bd07216ca880030fdd464581310062fb2ee6b222055a75811cb65440051dd0fb92c888092aba0b30191210047bc0aeab226000ae5820c761508018d8ebb92c6880022fa1c50d91310066a39ee2b122054ab48155160d0401d18c632264908022fe117650d200051ec2e63b224200d36425d4414404995ee632264908121fa17764c941006a6192ea3226400a5d8318b654400196ee838ac89900297a0c215974000c76432e420a4000a3d85083644c40117b093b242980122fe1d54d91324fe3a38ae6b288200cac74dc96344001a6aeab2082880163d20574d8132006c63a26490a6009a3e82909651040b1ed03baec8900268fa12325944101ce741ae1a126402acc8258d32104010fb0e216ca8815a9da0774d95102a69b882ea20a80058f4815d5648c4abae4e1b2e82880122fe1d54d91310243f42eec99482008bf845d5644c40155b0532ec8988021f61c20594410045ec3c21b224200c9c74dcd62441338e8e2b92ca208034d90d75105102ae3a3b6ca90a2000c7475dc5644400117b0e286c8988030fd97744c510266d3190e890a2000c3d751d7644c4010fb0bbb2658800b331c932d853004d1f426e6b2882018bd849da315000317908b8ec0a10030f5d754d913102d3a40ae0b28820087f855d9434810556d02100c8988022f61c201913100746316c89926224aae820c06448413938e8b1a6420802a7a0e65191210051f42e4232262038ed82dd932d00090f90abb28688002ad61051d85420070fa9ca7b224200ab681903644c80559d05b1a64a0802a760c50d91210052ec1842b2e8080e9431d9131484010ff0ab8ec6900169d207705944100666194e
  | 5 => 0x80032718c7458d100061fba8e8b1a40008f7815d564480010fb0f90eca88093a3dcc644c9210052ec1c85b2a2000cb474dc5634800b4ed02102ca208262fa1f53191210054ec1e4032262008bd871436448401a9865baac099152ad20554d854001566412c69922000ad583087614c1478e8e3b9aca208062f61375d8540014e7412e1a1a6405a74815c9651049bb2e643a262880036c1c374485100045fc22ec9922009a3e848c965d001347d0721aca208031b197725911004c5f43ee8b1a407fcac761913248401c5d0521aca208163d20575591300061e3aee8b122000dc432dc5604c80147b09992cba01634da14744c71000572412c230a6000ace86d09324c40155b04186c89080a3b20974d8d100043ec2eec9948200a3d859cf64484ad8e8e3382ca20a0eada0470d9131194bb42ee2996827fdb3601d1214410155b0439ec8908030f197744c5100051ec28603224200c3f75dd162440c1d18c9a1a64908121fa17764c9100055ac08a1b226209c3c645d4414800187eebba2c6880268f21172594410051ec0486b288200a6d820c16510401998e7b92c88825aade0565191310055ac0c403226200c3d75d92644c00136f0eb0882a0003331d932485300064e3a0e6b122041d34435d4414404917d0dba262908021fe1570d91324155b408a03226200ab48155364480090f90abb686881634d614744c710006c6196e8b0264018be86dd1315000145d0521aca2081237e1d53d8d210043f438eab1a4078a3f845c565d000155d0532ec89880eb320d624ca410045fc22eca1a2000c5c73d95644409b72906b2082880021fa1f65589100063bbaee2b1a4000db074dc121440010ff0abb2848805a8f61372597400046fc1aec992209ba3f845c96510401938e9b9ac68815a9da0473d951016656396c8a0a420487e87dd560904090f90abb264880121f21570d912104d1e422e2b2e8060e8c82191324c4ab4eb03ba6ca880268fa1373597400045fc3aca3226200c6f751c963440051d904baac68820f69087744c5210055b42421b0a6400cac74dc9624404b53d0db2264988163d20575591200051f42cc5b226200c5f739cd651044b53d06100c8988028f61721191310051ec2885b2260038dc835d36244101958edb2264908028f61443d91200051ec2cc5b226283ab681dd7644c40117f0eb20c8992572ddc464589310043f43e42b2e8016a3d84dcd65d000147b0b988c8908021f614764c94002c7a40aeab108225a9e83d44644c41347d0818acba00262fa1c20191310047bc0aec99220058f8865c0414800117f0eb20c8980167321d324c52100c7c402eab2264008f7815d5644c80bae6c0ba882880021f61e75d853201476412ed18a8000ab581083644c41347909982ca208029760e72597402a4da40ae899280008bd871406
  | 6 => 0x4d1f424e6b2e800487c855c763480031e902bb68588003171cc65591100052f41840b288200a7685cc7615080187cecba8c898816b3219324c52104d1e42640b288200aad82994644c50747b0321aca209074dd0175105100063ab2ee29908200a9d84d4f63500014e90ab08c2a00b7a518f744c5100061fb28e898a2000a6e829cd65d0001938c9b9ac0908163d2057650d2000537410e0b28820087e8719562440011ef02bb286900032bd93725813101476412eca1a200087f855da414c0010fd0fb2ac6880028fa1672d91310043fc2aeda12202da9e831cb644c4011bf06bb284880163da0775d91300243e42aeca1a4000e4c32595321040559d05b1a64a020aada0650191310061fb28e8b122000c3d75d90414c0a917b0fb26828800eb320d624c9100062fbaee6b222000aad820c064484018eeea38ac6900029b60831597400043f438eab1a20038de87dcd624400539d04b8e8699002a760e651912100557410a0322628ec9c73951644404d8e90cba882880034dd94744c5100054ec1ea23226200c3c75dd1634404b53d07900c8988162f21d54592310243f42eeca1a202dc9c73d91414c40187eea3a2c6880028fa1442d91310243f43eeab1a207fab681140644840147d0b31ec8908b22f21f644c5212ae3b3b6cba0a200487c855c3644c401d18c432264988028fe1570d913102c5e43aa8b262000c5d731cf654400147b0a100c8988021f617764c91004c5f438a03224205a76819cd651048336d0fba242881bb4de0575105400061eba0e9b2a200487c855c76250001d28c9b8a64988030f5d754d912112557436c89924200d8c321d1604c8ab0fd0f98eca880029ba0873d95100055ac20a3b0a86248bc865c84150013179083b242a01569d60473d951012f47b90c899262058f687dc563480c1d19063226490802ad60630191210245fc3aa9b226000e3765590414401347d09182ca208030f1977458910006d23a26490a2000ec532cc761480018d8ea392c6880022f61e1019131004dbc3ac820a2000c6f75dc964440051bb07bb265a022b1d1c4705944101c7ac0eebb226200a3c855c3644840117b0fa98c890896a7a0c501913141d4ec18e5b2262098be87dd1634404b93ee432264988023d60775d91300072a31eca98a20038dc835d5644400147b09182ca20802ad21161185320054e41ac8322200087d85dd932504051d904ba6c6900021f6177158f4001c7743ec499280008bf87590644400b1e902baac8990028f61672d9131006563a0e4b1a2000a9d839976448401b60e1ba262880262f21171d81320043ec3e62b2e800487e85dc562d00031e902bb6878800237e0d75591100065bba0e2b1a4000cac621d1624404d0e90cba882880022f612764c52000637b2ee4b1a2000aae8290f64440018b8cbb9ac88
  | 7 => 0x5000010e01880002010000121d0048e00004000688000300c4e800050000084609038038060d8100203e0001201804018020681612000045780b04a0c00005008100020080c0103e1080012976b2800000020109c068261500a08818008200783e080000380000066010da0502025802000961a82c0d8020a802050040d860060220001a3401a1f0040080e019367e80c1780e06008008040b0040d028000080094f26022050181604e0214a0188a0000052806040066281a36846050a80099a000360100c00068002ea378880100615000008000a1da0418a008008a8002280001812340fe0001a0513c03828348020202e0f80a3305405088000040081c070060000e018000007059010160020001c0016c13004090021901e000020a000151108700e0001403a24058021080003800000081902c0898200000020260483e3980400d820388203004058121a80000000028085f8000d84e0590855802000025f0380508c000223a00015002e51040c800000000016c0381405016248200800c018000104208dae01000100000003c0003c038cc0480c0680297802000087e068008020480e2b88c058a6008220809e170840087707010138710f03007cbe05826060007a80e0006408004028001f98204806008041c800000222d8031d5d751d85420261e3aca8b222000a3e859cf644840147b08102ca20962ece0161105400053ac0c40b28829aa77815c9651040b4ed02182ca208270f19175991300246fc3aa7b1a8282cb7601d1314400187eea3a2c4880038d104659911000c6e432e620a600487c855c763501454eb0339aca208021f61c3059441265d2412c820a200087f855d9324401387ec0ba882a00062f61371583423070e21aca9908200a3e85083644c4014bd07392cba025e9de0570594414155b40ca43226225cb4761d1314400517d0fb2284988023be09755912001c7743ec499282008f787584615084b1790cb9882a00031b1d772591100066a318e2b1a4000a3d850c3644840147b08182ca208b2aba0873d91210051f42cc6322420487e85dc563d000759d07b1264a00030f9da751913112557410a632242008bf87594644840b1790eaa2c910a022fe1176487400
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x500300008014700000f0801001c10003160010040840000400400030000000c000507a4e625d4415011321e93e1032594414f60d21a435d44144001a1710a0e42594410064520d7559041440c160c940c9654c84100523648631d1634404d0749760630594410060de1f65590414400123598104659911000549a4a435d4414400113598194744c51037e0d219405d4414400103d98194744851000629218744c9214404948c97191324c5214c60d21a425d44144001c2462194744851000625218744c9314400105f985cc735974000433660321d932440018547160c705944100689dc68290d651040103d97a1731191210048da6365590414400103d98194744c5104541da5b87d94414404d07798597714c84130683a0983909651040142e9298d751054000545a4e425d44144001a2710a0a43594414448ba4b840c96510401c1463194744c510006851c68390965104c1a0e8360a43594411341d25d8188165104014c5910c8764c9103be4ce01755904144001924825d56410510006191c5821c165104011359819474485100040f65e85c84644c401a1771a0e42594410052364c621d16244001a2471a0a4359441
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2042004200c096606219474485100050a34038b06382ca2080302486a4a435d4414400180acc0c6328e898a2000a1868071608705944100490948c88643b2648800301486a4e425d44144001602d18c4328e890a2000b0168863194744c510
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x100060059868863194744c5100060059868c621947448510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x94b
  | 7 => 0x94c
  | 8 => 0x94e
  | 9 => 0x5
  | 10 => 0x138e
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x98c
  | 14 => 0x98e
  | 15 => 0x9cb
  | 16 => 0x9ce
  | 17 => 0xa0b
  | 18 => 0xa0c
  | 19 => 0xa0e
  | 20 => 0x180b
  | 21 => 0x180c
  | 22 => 0x180e
  | 23 => 0xb09
  | 24 => 0xb0c
  | 25 => 0xb0e
  | 26 => 0x1409
  | 27 => 0x140c
  | 28 => 0x140e
  | 29 => 0xb49
  | 30 => 0xb4b
  | 31 => 0xb4e
  | 32 => 0x1449
  | 33 => 0x144b
  | 34 => 0x144e
  | 35 => 0x289
  | 36 => 0x28b
  | 37 => 0x28c
  | 38 => 0x28e
  | 39 => 0xb89
  | 40 => 0xb8b
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x1489
  | 44 => 0x148b
  | 45 => 0x148c
  | 46 => 0x148e
  | 47 => 0x1849
  | 48 => 0x184b
  | 49 => 0x184c
  | 50 => 0x184e
  | 51 => 0xcc9
  | 52 => 0xcce
  | 53 => 0xd09
  | 54 => 0xd0c
  | 55 => 0xd0e
  | 56 => 0x1889
  | 57 => 0x188c
  | 58 => 0x188e
  | 59 => 0xe89
  | 60 => 0xe8b
  | 61 => 0xe8e
  | 62 => 0x18c9
  | 63 => 0x18cb
  | 64 => 0x18ce
  | 65 => 0x94d
  | 66 => 0xb0956
  | 67 => 0x94b16
  | 68 => 0x140956
  | 69 => 0x95416
  | 70 => 0x209
  | 71 => 0xb4956
  | 72 => 0x94b56
  | 73 => 0x144956
  | 74 => 0x95456
  | 75 => 0x249
  | 76 => 0x28953
  | 77 => 0x28954
  | 78 => 0x28956
  | 79 => 0x94296
  | 80 => 0x184956
  | 81 => 0x95856
  | 82 => 0x1549
  | 83 => 0x16c9
  | 84 => 0xa0a
  | 85 => 0x14c9
  | 86 => 0x134a
  | 87 => 0x2c9
  | 88 => 0x138d
  | 89 => 0x138b16
  | 90 => 0x4b
  | 91 => 0x138b56
  | 92 => 0x4c
  | 93 => 0x185396
  | 94 => 0x139856
  | 95 => 0x124b
  | 96 => 0xccd
  | 97 => 0x98cd6
  | 98 => 0x1709
  | 99 => 0x15c9
  | 100 => 0x168b
  | 101 => 0x12cb
  | 102 => 0x1609
  | 103 => 0x130b
  | 104 => 0x124c
  | 105 => 0x9ccd6
  | 106 => 0x150c
  | 107 => 0x128c
  | 108 => 0x1789
  | 109 => 0x130c
  | 110 => 0x28a16
  | 111 => 0xa0296
  | 112 => 0xa1496
  | 113 => 0xa0d16
  | 114 => 0xa1896
  | 115 => 0x409
  | 116 => 0xa0e96
  | 117 => 0xa18d6
  | 118 => 0x589
  | 119 => 0x180a
  | 120 => 0x181496
  | 121 => 0x180d16
  | 122 => 0x10b
  | 123 => 0x180e96
  | 124 => 0x10c
  | 125 => 0x1049
  | 126 => 0x16cb
  | 127 => 0x40a
  | 128 => 0x160a
  | 129 => 0x154c
  | 130 => 0x58a
  | 131 => 0x178a
  | 132 => 0x24b
  | 133 => 0x58b
  | 134 => 0x178b
  | 135 => 0x160c
  | 136 => 0x15cd
  | 137 => 0x170d
  | 138 => 0x14a
  | 139 => 0x104b
  | 140 => 0x104c
  | 141 => 0x194b
  | 142 => 0x194c
  | 143 => 0x2d851
  | 144 => 0x29393
  | 145 => 0x29394
  | 146 => 0x19cd
  | 147 => 0x296d3
  | 148 => 0x299d3
  | 149 => 0x29554
  | 150 => 0x299d4
  | 151 => 0x29256
  | 152 => 0x160296
  | 153 => 0xd4a
  | 154 => 0x29556
  | 155 => 0x29616
  | 156 => 0x28b16
  | 157 => 0x1a0a
  | 158 => 0x178296
  | 159 => 0xeca
  | 160 => 0x296d6
  | 161 => 0x29796
  | 162 => 0x28b56
  | 163 => 0x1a4a
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1695
  | 6 => 2965
  | 5 => 1017
  | 4 => 46
  | 3 => 9
  | 2 => 2
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | 3 => packedAt gbK3 (i*81) 72
  | 2 => packedAt gbK2 (i*92) 83
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | 3 => gbHint (packedAt gbK3 (i*81+72) 9)
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/600+packedAt gbK7 (62715+(h % 600)*11) 11) % 1695)
  | 6 => 2*((h/988+packedAt gbK6 (142320+(h % 988)*12) 12) % 2965)
  | 5 => 2*((h/381+packedAt gbK5 (60003+(h % 381)*10) 10) % 1017)
  | 4 => 2*((h/43+packedAt gbK4 (3220+(h % 43)*6) 6) % 46)
  | 3 => 2*((h/10+packedAt gbK3 (729+(h % 10)*4) 4) % 9)
  | 2 => 2*((h/7+packedAt gbK2 (184+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff03c07c0ff81fffffffffc13c88f80c7fff
  | 1 => 0xf01fc007ff0ffe1fe0f01e006d37764739ecc
  | 2 => 0xf001ffff8000fffe1ff001fff8e3878783e30f
  | 3 => 0x1ffffffff00001ffffe003f03f807fc03f0
  | 4 => 0x1ffffffffffffe00000003ffc0007fffc00
  | 5 => 0xfffe000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110c0080140128022211242480040028042c55
  | 1 => 0xa152c022d505aa14e8a0d41825133643196cc
  | 2 => 0xa021555a804094d415a8119b18a3858582c30a
  | 3 => 0x80419a6b4a6a008019ccd9022d03d806d803a0
  | 4 => 0x888e3b4738ce7198000600c37fc00036f7800
  | 5 => 0xccf0003803080611010080103ffaeed0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40533
namespace PEqualNP.Outside.L_meta_40533
open PEqualNP.Outside.L_meta_40533.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 90 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 9 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 13 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 75 := block_range (n:=75) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 75 := bs5_3_0
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
theorem bs5_4_576 : Interval s5Atlas 4 576 50 := block_range (n:=50) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 626 := (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat (concat bs5_4_288 bs5_4_384) (concat bs5_4_480 bs5_4_576)))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 699 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 bs5_5_672)))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 9 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 46 := block_range (n:=46) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 46 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1017 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
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
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 85 := block_range (n:=85) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2965 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat (concat bgb_6_672 bgb_6_768) (concat bgb_6_864 bgb_6_960)) (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 bgb_6_1344)))) (concat (concat (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 bgb_6_1728)) (concat (concat bgb_6_1824 bgb_6_1920) (concat bgb_6_2016 bgb_6_2112))) (concat (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 bgb_6_2496)) (concat (concat bgb_6_2592 bgb_6_2688) (concat bgb_6_2784 bgb_6_2880)))))
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
theorem bgb_7_480 : Interval gbAtlas 7 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 63 := block_range (n:=63) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1695 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)))) (concat (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152)) (concat (concat bgb_7_1248 bgb_7_1344) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
  · exact allgb_3 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 36, 38),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0feeaeeeafee8aaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276660896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40533.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[2,3]⟩,⟨.and,[1,6]⟩,⟨.and,[4,7]⟩,⟨.or,[0,9]⟩,⟨.or,[8,10]⟩,⟨.or,[2,3]⟩,⟨.or,[5,8]⟩,⟨.and,[0,13]⟩,⟨.or,[12,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276660896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276660896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40533

open PEqualNP.Outside.L_meta_40533 in
theorem PEqualNP.Outside.L_meta_40533 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276660896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276660896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
