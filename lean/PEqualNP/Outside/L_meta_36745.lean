import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36745.Model
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
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d || anyEq (masked d a) d pool ||
    (u && anyEq (masked d (neg a)) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  simp only [availF,availableB,eqF_eq,anyEq_eq]
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
    (links (keySet (choiceVal op::rest))).any (sameWords (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,Bool.or_eq_true,List.any_eq_true] at h
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
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (fun op => quickPair ctx a b op || testPair ctx a b op))
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
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


end PEqualNP.Outside.L_meta_36745.Model

namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
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

def SBf (j : Nat) : Nat := [6, 4, 6, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36745

namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x284c1a40128080018076a1601806bf43bd43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x180028810020025aa5a1c754f428ea98832d52107a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s0K3 (170+((h/2+packedAt s0K3 (162+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36745
namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f80ff03f81fffffe07c1f07c0fc1ffff4923f
  | 3 => 0x3fff0003ffe03f81ff801ff800ffe0f818e3cc
  | 4 => 0xc0000003ffffc001ffffe00000ffff001f03f0
  | 5 => 0xfffffffc00000001ffffffffff0000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80840a000800810001842108461421094124d5
  | 2 => 0x1552946594d52a68f059164688a91ad694922a
  | 3 => 0xa64aa6aaa553b42b76c21bd212cf48e0d8e34c
  | 4 => 0x346cd8d3469a274dbb6f508424f39c431f03b0
  | 5 => 0x3870e0e3871c3871dc739ce7388210841ed800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36745
namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1804821c25000c200ef32de32dc32ec32cc32bf41bd41be40bc40
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc20684a0e002a7294658e540cb1aa819630cb41c6192838c329031864204d54440
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xa0180a1586540ca0d650cb418359432103043254440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (156+((h/3+packedAt s2K4 (144+(h % 3)*4) 4) % 14)*5) 5
  | 3 => packedAt s2K3 (224+((h/2+packedAt s2K3 (216+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 1 => 0x81fc0fff83ffffff0783c1f03ff87fffd24e3f
  | 3 => 0xfe000ffffc0fc1fff803fe003fff8781e38fcc
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8828002300208000188442118a0088940490d5
  | 1 => 0x24519644194530cb032191a214c85568d2462a
  | 3 => 0x149aaa8928ea13556842f484a755060d638b4c
  | 4 => 0x59634d125283a5a6b5e8210939a66031bc0db0
  | 5 => 0x61838e1c630c39f8c67339ce01c44441fb6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36745
namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x161860028208048000bc0a31e4410d0068b94102801b42ac59c00b510048003ac00941954c4c29d4e0092a3e107005278c865c00000340008202074a004106ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2d860fa4e36000d24c088487e2f3d0acf242000c04a6b1d0b00c710e8b8800002204ce833f000004f148a8ec002095470620b9283433010c84c820c9b8c064000008e50000e4da661e9242c5f1b1c0a2220f9190845308001a0c05000001400000781c2c8d46e0b001c806103a9f0e800398a0a400000d0fe482b12cd0003c0009a133d800001b32854b43e2c110120800000ba540003886002e000427707878c66a378c4485e42800ae201180500271d81ca60516824240014000408080c00340408c4202c0000405844040004102828140400240420282834083c0010000400debaa921d794a43af28c875d5090f3ea8a1d714943ae28a875f5050ebca621d794f42aea9e859d43d0aeca3a15d54742afa9a855c5350b3a86a15794c42aea98855f548cabaa9195794a32af28c655d508ca7ca8194f55032afaa0659e540cabaa81967550328eaa0655e520cb9ca4195794432aea80655e53d06baa7a0e750f41b7296836d52d06bea6a0d714d41cea1a835e53106baa620d7d5231aeaa4635e528c6bca318d7542319f2a0633d540c6bea818e795031aeaa0639d540c63aa818d794831af28863d6510c6baa018cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710d7d4d21ae29a435f53086b8a610f948421af29e815d53d02bca7205754e40cea1c815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc2bea9986795330aeaa6619d54cc23aa9985794b30af28e615d538c2bea8985755130ae292615c514c3b6a0985794c30afa9e415c53c82bca7105754e209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xb8e018c88b0048000c01a926296c00aa041e1a270409402800084480a3c550d51d0a8c6250d4295987548ca1d649463287d91508ca1d6595032c350d52d06946150d419398b548c61d6494a3187d91508c61d659503187590534861d6414c2196580530870d4354840c550d511024c625513095185544c21d641493087590514c21d6494c308759053c821d6494e208759053c421d6494e10
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (864+((h/16+packedAt s3K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s3K4 (3970+((h/44+packedAt s3K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s3K3 (1028+((h/8+packedAt s3K3 (988+(h % 8)*5) 5) % 32)*6) 6
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffc1ffffff81fffe0ffff83ffffe78f1ff
  | 1 => 0xe07e0ffe0ffe1ffe1e0ff0f07fc3f83fa74e73
  | 2 => 0xff800ffff07fe1ffe00fff007ffc3fc1c78f9c
  | 4 => 0xfffff8001fffff000007fffc001f80fe0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x20800440004000022100111100449080810a5
  | 1 => 0x49149488652830960c8690a22a4290b4a34652
  | 2 => 0x85252910a351032ac10b2a044ca82685458b18
  | 4 => 0xd659ce254a1d55cd77a1888977330319f80de0
  | 5 => 0x18618c398c6199f199cdccce06220421f6e000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36745
namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2a00007060000a54717862c002a53c98f91304c02d4000010005c00018b918010a000242006842404000000122b3201480007401b0000000446802c0000000002c48f0000a2700000001c1200282000000104180810600002ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2e82c2034068d49a0a0920cae001d1900069170ecd46117a0090202200c36230616870223386000003c0f88c150010ce8004084c008500000a800001a0006500000e65e18958f600001300a6d038a0a40241000b67a1f804cc790c8e422623e18ca600049bc1c0f2a9b0fe5c03078b02b1b09400303b9ac0004139c83800248002e292721096423e9c0664a04098647100144a041239803421200f0001d3a8a8fc5f279d87a00370005a160a07c58450009000591b80c08000c081c0c08000c380000280c0418102410500c48100008086060b0001c64300000140808203428202abaa921d794a43af28c875d5090f3ea8a1d714943ae28a875f5050ebca621d794f42aea9e859d43d0aeca3a15d54742afa9a855c5350b3a86a15794c42aea98855f548cabaa9195794a32af28c655d508ca7ca8194f55032afaa0659e540cabaa81967550328eaa0655e520cb9ca4195794432aea80655e53d06baa7a0e750f41b7296836d52d06bea6a0d714d41cea1a835e53106baa620d7d5231aeaa4635e528c6bca318d7542319f2a0633d540c6bea818e795031aeaa0639d540c63aa818d794831af28863d6510c6baa018cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710d7d4d21ae29a435f53086b8a610f948421af29e815d53d02bca7205754e40cea1c815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc2bea9986795330aeaa6619d54cc23aa9985794b30af28e615d538c2bea8985755130ae292615c514c3b6a0985794c30afa9e415c53c82bca7105754e209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x320160002aa01a024000818394312706b22108a0078042e980c020c91530cc015c550d51d0a8c6250d4295987548ca1d649463287d91508ca1d6595032c350d52d06946150d419398b548c61d6494a3187d91508c61d659503187590534861d6414c2196580530870d4354840c550d511024c625513095185544c21d641493087590514c21d6494c308759053c821d6494e208759053c421d6494e10
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (880+((h/16+packedAt s4K5 (768+(h % 16)*7) 7) % 90)*7) 7
  | 4 => packedAt s4K4 (3970+((h/44+packedAt s4K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s4K3 (1036+((h/8+packedAt s4K3 (988+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fffffc1ffffff81fffe0ffff83ffffe78f1ff
  | 1 => 0xe07e0ffe0ffe1ffe1e0ff0f07fc3f83fa74e73
  | 2 => 0xff800ffff07fe1ffe00fff007ffc3fc1c78f9c
  | 3 => 0xfffff8001fffff000007fffc001f80fe0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x20800440004000022100111100449080810a5
  | 1 => 0x49149488652830960c8690a22a4290b4a34652
  | 2 => 0x85252910a351032ac10b2a044ca82685458b18
  | 3 => 0xd659ce254a1d55cd77a1888977330319f80de0
  | 5 => 0x18618c398c6199f199cdccce06220421f6e000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeae8a8e8a8eaeaeaeae8a8e8a8eaeaeaeae8a8e8a8eaeaeaeae8a8e8a8eaeaeaeae8a8e8a8eaeaeaeae8a8e8a8eaeaeaeae8a8e8a8eaeaeaeae8a8e8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36745
namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea98817e52102faa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec42887d48510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0x101001016028400201c000260680c01800085f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f7d0c31ee218637e520c6faa418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9
  | 2 => 0x2011946e8a88000000011ca3f42e5ac8207c0e472ce78da2861dcaaa1d0623b01d8493600000f8cd256000c20d11c6840e891a36a2752b0eb000000000000008f11e9f8212118b00000180012215e0945001625549c22c4b009000260001081fe0000011417c850000000002dc5e0dd000000aa0d52e456c5487427a680000000000007b0a741c0011083242c1b43d1101bc0749b8830de000000e70060fd169860985fcd1a5823e5bc2d8f30ce3f8001382c40004a800000290679c3390094b0814358178fd0a646a6d0fa1494440001a0bb404898d994a0e2218028552a07c00025107c0bd2b9f53de0000013f0004c4ab0bf342000de8fd0000009a1e44480000000011827114a3a0000010fa273724bd18800272000a900425c0001523b0900cc6c82e00000000000000940000004a46244a0a30007185b12a09a000f197a0ea69000000000830a11e74a63dc001ca1a8575259991c83b4001dd248934b8a0b2da1489113c1083a43d98d2900f0a71da2408c8ca98c03c04c91a341908c05c0aa19c3c4111ab0246a8eb1cc06e924d71fc0608b9141df4363801023326c138bf182180000569851ae918e08a006a5cc938f512009c8e22b3d8220f0a1a10a1b025a380b888ca58630567dc5e8394263406100047c000001633d0530ee06b33e5e5090930007f8928a806c00045181232001050df0822e4009ce42a000ba8002ae6780004f02e238d111336436c2c0603785640c0c33ca00000000230000000f23a85e0d305041e5347800003493c3c81b266878af8231de6f8000f90706e08383d0000a0168000000000680028c000000590002680013a0322651b22f204864bb1912d8054e390300060c00000000001018003383580888d3289040e0000c42c8be0002f63a89413532031c8e9d929e27d160e62022b0350541603245990f3aa7b91b9f92601b83e8fa0849143f19d2dc1e0a3a041c2478120650ba224321a7174100b28000be90cd88f43e474c33180102900d41321d07d84b9212d43e02b03a3163306e029412000dd906000201251fd18a6bc0589b35a660ff80a31c000869ea31e11c828e222282003000010184038000002d100000010040020000003814040000200401812000000380c000120e00416004020060000c01000030160207000000000000081a0b8000100803020010120280401860008121c808000000002e028120002a0c02c0080c2004201006038100200208000048000c800138640b800048140e0320100e020020001c00022038040181e0783e02000070000200011002000280b0020080001028020040000600000010040082201800008040f03200002000060283a0000a008100b800000080180016816058060001010802030000f8100c0001e87c03800050000082a0d0100100a070080083001804008
  | 3 => 0x1088002528184790e3ae6688d8003c0894f681038a084a200016a4482200039a1d8f300f4907a4b21c42fa4ecdb9db41a1cccb1662e0294a09eb25a5a0c41003f6788630fb28a7406213e48e248b39872ee880f884522a058ad0e52d22b8f990a3526fccd9c010e278a985a1dc6d8ba1a501c4302b802162208e90d80868603f916000000931970a22880024c22e81c7e1d8392000578533148701300012200096254484000c90cb2b034834a2a40a000ef15c0e034c5590b00028460868000000c980000070800
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd415029e639014097d8d511025c63544408f596411023f65500409ed95401026e62153309b58854cc31d5410f30b358843cc29c644cb30a719131cc31e548c630c7950318c31e54cc2309bd89544c26c62551309dd85544c274615513097997434c31d5410d30b3588434c23e64149308f590524c29c644c930d3149324c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23f64544308f191510c25d658c4308f992500c23d649403097d95300c27b654c03097d8d54c825c63553209798c54c825d63153208fd9153c823c6454f208f99053c823d6414f209798f548825d63d52208f993538823d64d4e208fd91518823c645462097d8d518825c635462097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d209b997214825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020d9545200827b654802097d8d54c425c63553108fd9153c423c6454f108f99252c423d6494b109798e52c425d6394b109798f548425d63d52108f993538423d64d4e108f990528423d6414a109798c528425d6314a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524436452885109d19521442f060485109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520436552c40109e59610042776544010d9549100427b6544010
  | 1 => 0x2640000000801000210180300006000000000200002000000280600800014080240f0180000800004030240e0240708c09028000100000002014160180001005014010341301c0001415028070240500400000000180200408000000080100400010090201204c070180002400000030000100c150000200c070240003801014050000400c000000b00003018040580805004038030000d00c000000b0000400400000030040ea75924310e3f6550c4397d954310e9f6550c43c7d954310e9c6250c43a71854310e9f6050c43e350e5210f1d4354843e350d5210f2f4354843d390d5210f2d4354843d350d5210f0d435484397d8d51d0a5c63547429798e50d0a5d6394342ab5884390b4d6214d428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310aad6210c42c754f4210b4d53908428fd954210a9c6350842c754d4210a6f6550842d354d4210b1c5450f328fd9151cca3c64547328f99250cca3d64943329d987548ca7561d5232c7d50438cacd6210e32e310e428cacc6350a32e3d0d428ca3e649513297d8d544ca3e6515132c758c544cb2d621513297996434cb1c5490d3297195434cb1c5450d32cb152424cb8e43909329b195424cb8d4350932c7152324ca3d6595032c718d540ca3e64150329798c540ca6e621503297597430cb1d54d0c3297594430cb1d5410c32b3588430cb1d54cc832cb552320ca5f654c832a7191320cb1d544c8329bd95320cb2d544c8329798e50d065d6394341ab588439065e6394a419758e529069c6350a41cb949429071c5390541c754c43106ad6210c41a718d421063f6550441a718d411067765504419b98854cc66d62153318f99250cc63d64943319b98b548c66d62d5231c7d50438c6cd6210e318f992528c63d6494a31a7191328c74e524ca318f992544c65f63551318f994544c71c548c5319b988540c66d62150319e980540c679601503197594430c71d5410c31b3588430c69c644c83197d95310c69c644c4319dd95310c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c865e63d52219758f548863e64d4e218f593538865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e64141218f590504865e63141219758c504865f63550219718d540865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520866f65484219dd95210871d5310f40ab58843d029c6350b40a718d41d031e5390640c794c419031e53d0240ab588435025e63149409758c525029c6350940cb149425023e65d0540a718
  | 2 => 0x238ba1800021c2e9b4a80000604e000006b1441c9f2002b2002183a2d46525224000408da17800548c60027a5186456276a1b065d0007e0cc000000003a6a000ad800000a60192a181d27c1dc719c000000b6a6c4daeabd8887d1542190c6101cb22ee6e0004e0e60080a2d9e6000003726aab000000a8839a60000088af03c9401a1ae0000076ae00009a1c250a2000001d400000c325c0003200062a7016590c08116a002a20015652800000ac7e8b40000c96ae60008a00000000ea9a23e53af8c38000015e000000a00030800141aa000ca0023c0000091800aea84908000017689ac0340580d0008d800002b46e94200124a000077a0292abe448004c86c422405b86a5f206b72de12b0066a94aaaec000ce068e2a600000000050c4bc87a2882a3821a5990aaf0040011a151000020a4d036282d825b10003027580000000b10fc2b80808000000000027e0000000000000fa9e0009c8004586e64000690d463800390001300079000000001080000000bd00091000b1a4e1d000002a600000820009c06600000118d6a480000000bf92624800000985ca82a2b0a092fa002b07f2107f91cb3a2e67b12a431672ad00000016800bf1186d8004531400000000400012c9d1be0019c98810921c8000002f0484a05c078000b00000130958005b14c158002093e2c93c1d8007600e0000000000000000000073920001928d000849b27aa32412ae9f030479e2418128e9b057230680f6710d861800a3996830c81f89c6f2c21e198002e4000f8ae28c000fe252607b13a08a5478214348005425e5e88c801604b8261498a3d17e0f10e0029a001f6200002c00000038998ee0000000000a59ee000be3c1688a8aa2780052000c11cc000000000088000002580f8b8112d6b48000021e002247088e740ec001101f24c0029e001a29b80085800621785c0000baca000003788400228aa0000022c293080018200000632e20012256800b3000a90007a1620
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x120000110c00404c00005c008038c00d2801c000069060510655c0166492143c06cb0c01600201a305431c94354843a18eca1aa421d0c7150d5210e87b8286a9087459c75410e32c1ea8b10871948e76d0d428cb06b1ac42a265439d64390932c18caa1a849960d54588430ca0e3b2a899065435ce5250a41c18c72928520e0d535884310687396a821c6383d516210e31a1ae92926518e0c64949328c706aa2c4218638354d6210f40a1ae629284a060c631494250306aa2c421e61431c95410d30a28e2aa0869860d54588434c286ba0a49926183190524c930
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x200b0a0681d516210e3280d87192524ca31a04815516210d3080d87190524c930
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 29
  | 2 => 4
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (18227+((h/200+packedAt s5K5 (16227+(h % 200)*10) 10) % 722)*11) 11
  | 4 => packedAt s5K4 (16368+((h/132+packedAt s5K4 (15048+(h % 132)*10) 10) % 575)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 45)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc1ffff07ffffff03ff0ff0ffe1fffffa38f1ff
  | 1 => 0xfe07fff81fff0ffc1ff0ff0ffe1f81fdc73e73
  | 2 => 0xfff81fffe07ff1ffe000fff1ffe3fe0607cf9c
  | 3 => 0x1fffff8001ffffff0001fffc0007f80fe0
  | 4 => 0xffffe000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x5020811104120000a50120124024a8a01850a5
  | 1 => 0x84914220c924102c0a105104a2090550c32652
  | 2 => 0x85254424348835540889aa135425416058b18
  | 3 => 0x2d659894920ea59a73aa0881d9901867680de0
  | 4 => 0x318610e71c70c9e39cccecc811006187b6f000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8eee8e8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36745
namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5005fe5401ff55005fc5401ffd4c03fe5301ff54c03fc53017fd0c03fe43007f50c03fc4301ffd4807fe5201ff54807fc52017fd0801fe42007f50805fc4200ffcc801fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fd0401fe41007f50405fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0001fe40007f50005fc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200cff9951001dfcca88033fd65440197eb2a200cff1951001df8ca880337c65440073e32a2000ffd9110005fec888003bf64440015fb22200bff99110015fcc888003fd64440017eb22200bff19110015f8c888003bc64440055e322200cffd511005ffca888033fd5444017fe2a22000ffd8d10005fec688003df63440016fb1a200aff98d1000dfcc688003fd63440017eb1a200aff18d1000df8c688003dc63440036e31a200cffd4d10057fca688033fd5344015fe29a200bffd0d10057fc8688003fd4344015fe21a2000ffd8910005fec488003ef624400177b122000ff9891004dfcc488003fd62440017eb122000ff1891004df8c488003ec624400176312200cffd4910067fca488033fd5244019fe292200bffd0910007fc8488003fd4244017fe212200affcc910007fc6488003fd3244015fe192200cffd4510067fca288033f65144019fea8a200cfd54510067f8a28802fff4144001ff20a2000ff5051005ff8828802bff3144001ff18a2000ff4c510057f86288003ff2144001ff10a2000fd88510007fa4288003f52144001fe10a200cffd4110027fca088033fd5044009fe282200bffd0110027fc8088003fd4044009fe202200affcc110027fc6088003fd3044009fe1822000ffc8110027fc4088003fd2044009fe1022000ffc4110007f62088013fe1044009fb0822004ffd9410025feca08013fe65040077f3282004df9941001cfcca08013fd650400f7eb282004df59410004faca08013fc65040097e3282004ffd9010025fec808013fe64040057f3202004ef990100157cc808013fd64040017eb202004ef590100057ac808013fc64040097e3202007ffd5010037fca80801ffd540400dfe2a02004ffd8c10025fec608013fe63040037f3182004f798c1000dbcc608013fd63040017eb182004f758c10005bac608013fc63040097e3182007ffd4c1002ffca60801ffd530400bfe2982006ffd0c1002ffc8608003fd430400bfe2182004ffd8810025fec408013fe62040137f3102004fb98810005dcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481003ffca40801ffd520400ffe2902006ffd0810007fc8408003fd420400dfe2102005ffcc810007fc6408003fd320400bfe1902008bf9841003ffea20801ffe510400ffea882007ff14410037fe8208003fe4104001fea082006ff1041002ffe6208003fe3104001fe9882005ff0c410007fe4208003fe2104001fe9082000ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x3fe4108001fea084013ff10420097fe6210003fe3108001fe9884012ff0c42004ffe4210027fe2108001f71084009ff4842004ff84210027ec21080097f3004004ffd4020027fca010013fd5008009fe2804004ffd0020027fc8010013fd4008009fe2004004ffcc020027fc6010013fd3008009fe1804004ffc8020027de4010013fe2008009fd1004004ff48020027da4010027f92008011ffb2e2008bfd9710047fccb8800efe65c4011feb2e2008bf59710047f8cb8800efc65c4001ffb262000bfd931008ffcc98800afe64c4001feb262000bf5931008ff8c98800afc64c4011ffaa62011ff95310047faa988047fc54c4001ffb1e2000bfd8f10087fcc788006fe63c4001feb1e2000bf58f10087f8c788006fc63c4011ffa9e2010ff94f10047faa788043fc53c4023ffa1e2010ff90f10007fa8788043fc43c4001ffb162000bfd8b10007fcc588026fe62c4001feb162000bf58b10007f8c588026fc62c4011ffa962008ff94b10047faa588023fc52c4023ffa162000ff90b10007fa8588047fc42c4021ff9962000ff8cb10007fa6588043fc32c4011ffa8e2008ff94710047eca388023fd51c4011faa8e2008ff1471008ffe8388003fe41c4001fea0e2011ff10710087fe6388003fe31c4001fe98e2010ff0c710007fe4388003fe21c4001fb10e2000ff48710007ea4388003fc21c4011ffa862004ff94310047faa188013fc50c4023ffa062004ff90310007fa8188013fc40c4021ff9862004ff8c310007fa6188013fc30c4001ff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800efe6584009feb2c200fbf59610027f8cb08012fc6584009ffb242004bfd9210027fcc90800afe6484009feb242000bf59210027f8c908012fc648401fffaa4200eff9521007ffaa90803bfc5484009ffb1c2004bfd8e10027fcc708006fe6384009feb1c2000bf58e10027f8c708012fc638401fffa9c200dff94e1007ffaa708037fc538401dffa1c200dff90e10007fa8708037fc4384009ffb142004bfd8a10027fcc508026fe6284009feb142000bf58a10027f8c508012fc628401fffa94200fff94a1007ffaa50803ffc528401dffa142000ff90a10007fa850803bfc428401bff9942000ff8ca10007fa6508037fc32840197eb0c200fffd461007ffca30803ffd518401ffe28c200effd0610007fc8308003fd418401dfe20c200dffcc610007fc6308003fd318401bfe18c2000ffc8610007fc4308003fd2184001fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9042004ff08210027fe2108013f71084001fd884200cffd9510065feca880037f65440013fb
  | 2 => 0x2004ffca51006bfd5288013fe2944019ffd0a2004ffc8510003fd4288013fe2144018ffcca2004ffc6510003fd3288013fe1944004ffd8620027fcc310002fe6188009feb0c4000bf58620027f8c31006bff5188035ff28c401aff546200d7f8a310067ff4188001ff20c4000ff506200cff88310063ff3188001ff18c4000ff4c6200c7f86310027ff2188001ff10c4000fb88620007fa4310027fc2188001f610c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef2088013fd9044017ffd95200bdfeca900037f65480013fb2a4017ff9952001dfcca9005ffd654802f7eb2a4017ff1952001df8ca9005f7c65480073e32a4000ffd9120005fec89005bfe64480057f3224000ff59120005fac89005bfc64480057e3224017ffd51200b7fca89005ffd544802dfe2a24000ffd8d20005fec690057fe63480037f31a4000ff58d20005fac690057fc63480037e31a4017ffd4d200affca69005ffd534802bfe29a4016ffd0d200affc8690003fd434802bfe21a4017ffd492004ffca49005fee524802ffea924017fb5492004ff8a49005bff4248013ff2124000ff5092004ff88490057ff3248013ff1924000ff4c92004ff86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a4017ffd45200bffca29005ffd514802ffe28a4016ffd0520007fc8290003fd414802dfe20a4015ffcc520007fc6290003fd314802bfe18a4009ffc8520007de4290003fe2148001fe90a4000fb4852004ff8429005fff5048009ff2824017ff54120027f8a09005bff4048009ff2024000ff50120027f88090057ff3048009ff1824000ff4c120027f86090027ff2048013fd9024004ff88120027dc4090013ff65080097fb284004ff9942001dfcca100137e65080073f3284004ff594200a5faca100137d65080013eb284004ff19420025f8ca10013ff64080097fb204004ff99020015fcc810013be64080055f3204004ff59020005fac810013bd64080015eb204004ff19020025f8c810053ff5408027ff2a04014ff5502009ff8a810013ff63080097fb184004ff98c2000dfcc610013de63080036f3184004ff58c20005fac610013dd63080016eb184004ff18c20025f8c610053ff5308025ff2984014ff54c20097f8a61004fff4308025ff2184000ff50c20097f88610026fe6208013ffa904009ff9482004ffaa410027fc5208013ffa104009ff9082004ffa8410027fc4208013ff9904009ff8c82004ffa6410027fc3208009ffb084004ff98420005fcc210013f661080017b3084004ff58420005fac210013f561080017ab084004ff184200a7fea210053fe5108029fea884014ff1442009ffe821000
  | 3 => 0xf9846004f7cc23000ff66118013fc308c009fc184601fffd95300fdfeca9807ffe654c0077f32a601fff595300fdfaca9807ffc654c0077e32a6000ffd9130005fec89807bfe644c0057f3226000ff59130005fac89807bfc644c0057e322601fffd51300f7fca89807ffd544c03dfe2a26004bfd8d3000ffea698007fe534c003ef29a6001ff54d300ffbaa698007fc534c003ffa1a601ef7d0d3000ffc8698007fd434c003fe21a6001f710d30007fec498002ff624c001ff3126000ff58930007f8c498026fc624c03fffa92601fff949300fffaa49807ffc524c03dffa126000ff90930007fa849807bfc424c003ff9926001f7cc93000ffc6498007fd324c001ee9926001ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c03fffa8a601fff945300fffaa29807ffc514c03dffa0a6000ff90530007fa829807bfc414c003ff98a6001f7cc53000ffc6298007fd314c001ee98a6001ff0c530007fe4298003fe214c001fe90a6000ff0853000dfec09807fff504c009ff282601fff54130027f8a09807bff404c009ff2026000ff50130027f88098007ff304c003fd9826004ff8c130027bc6098013fc304c009ee1826001fe0c13004ffecb90026ff65c8013ff32e4003bf9972004ffacb90076fd65c8013fe32e4009bf1972004ffec990026ff64c8013ff3264002bf9932004ffac990002fd64c8013fe3264009bf193200effea990073fe54c803bfeaa6401cff1532004ffec790026ff63c8013ff31e4001bf98f2004ffac790002fd63c8013fe31e4009bf18f200effea79006ffe53c803bfea9e401bff14f200e7fe879006ffe43c8001fea1e401bff10f2004ffea590027fe52c8013f72964009ff54b200efdaa590027fc52c8013ffa164009ff90b2004ffa8590027fc42c8013ff9964009ff8cb2004ffa6590027fc32c8013ffb0e4009ff98720005fcc390027fd61c80017eb0e4009ff187200effea390077fe51c803bfea8e401dff147200e7fe8390003fe41c8001fea0e401cff107200dffe6390003fe31c8001fe98e401bff0c72004ffe4390027ef21c8013ff10e4009ff48720007da4390027fc21c803bffa864004ff943200effaa190013fc50c8039ffa064004ff90320007fa8190013fc40c8037ff9864004ff8c320007fa6190013fc30c8009ffb2c4004bfd9620027fccb1000efe6588009feb2c401abf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000afe6488009feb244000bf59220027f8c910012fc6488035ffaa44019ff952200d7faa910067fc5488009ffb1c4004bfd8e20027fcc710006fe6388009feb1c4000bf58e20027f8c710012fc6388035ffa9c4018ff94e200d7faa710063fc5388033ffa1c4018ff90e20007fa8710063fc438802f7eb14401affd4a
  | 4 => 0x97fe529004bfea948025ff14a40017fe852000bfe4290005fea148002ff10a40127fe6520003fe3290001fe9948024ff0ca40027fec320013fe61900017f30c8004ff58640005fac320013fc619004bffa8c8025ff9464012ffaa320097fc5190005ffa0c8002ff906400077c832000bfd4190005fe20c8002ef10640127fe6320003fe3190001fe98c8024ff0c640007fe4320003fe2190001fe90c8000ff08640025fcc120013ff5090009ff2848004ff54240027f8a120013ff4090009dfa048002fed0240027f88120013f84090009ff9848004ff0c24011ffecaa008eff6550047ff32a8003bf9954011ffacaa008efd6550047fe32a8003bf19540025fec8a000bff5450005ff2a28002ef95140017faa8a008fbd5450005fe2a28000ffd8d40005fec6a008bfe63500037f31a8000ff58d40117f8c6a0006fc6350047ffa9a8022ff94d4011ffaa6a008bfc5350005ffa1a8002ff90d401177c86a000bfd4350005fe21a8002ef10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0026fc6250047ffa928023ff9494011ffaa4a008ffc5250005ffa128002efd0940017fc84a000bfd4250001dea128002ff10940117fe64a0003fe3250001fe9928022ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150047ffa8a8023ff9454011ffaa2a008ffc5150005ffa0a8002efd0540017fc82a000bfd4150001dea0a8002ff10540117fe62a0003fe3150001fe98a8022ff0c540007fe42a0003fe2150001fe90a8000ff08540015fec0a008fff5050009ff2828023ff54140027f8a0a000bff4050005fda028004ff901400277c80a0013fc4050009de2028002fe10140117fe60a0013fc3050009ffb2c6004bfd9630027fccb1800efe658c009feb2c6021bf59630027f8cb18012fc658c009ffb246004bfd9230027fcc91800afe648c009df3246002af99230027fac918002fd648c009deb246000af59230027f8c918012fc648c043ffaa46020ff9523010ffaa918083fc548c0037eb1c6001ffd4e3000ffca718007fd538c003fe29c6001ffd0e3000ffc8718007fd438c003fe21c6004ffd8a30027fcc518026fe628c009feb146000bf58a30027f8c518087ff528c043ff2946021ff54a3010ff8a518083ff428c001ff2146000ff50a30107f88518007ff328c003ff1946001ff4ca3000ff86518013ff618c009ff30c6000bf98630027fac318002fd618c009fe30c6021ffd463010ffca318087fd518c043fe28c6020ffd0630007fc8318003fd418c041fe20c6001ffcc63000ffc6318003de318c003fe98c6001ff0c63000fb86318003ff218c001ff10c6000ff48630007f84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009f
  | 5 => 0xc621007fa63108b7fc3188413ff90c4200fbc862104fee4310803ff6088401ff3044204bf98221007fac110802fd6088401fe3044229ffd422114ffca1108a7fd5088453fe284422effd0221177f881108b7ff308845bfe184422cffd9521165feca908b3fe65484077f32a422cff59521165faca908b3fc65484077e32a4200ffd9121005fec8908affe64484057f3224200ff59121005fac8908affc64484057e322422cffd512115ffca8908b3fd5448457fe2a24200ffd8d21005fec6908abfe63484037f31a4200ff58d21005fac6908abfc63484037e31a422cffd4d21157fca6908b3fd5348455fe29a422bffd0d21157fc8690803fd4348455fe21a422cffd492104ffca4908b3fd5248413fe292422bffd092104ffc8490803fd4248413fe212422affcc92104ffc6490803fd3248413fe192422cffd4521167fca2908b3fd5148459fe28a422bffd0521007fc8290803fd4148457fe20a422affcc521007fc6290803fd3148455fe18a4209ffc852104fee4290803fe2148401f710a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c0908b3ff5048459ff282422cff54121167f8a0908afff4048457fe202422affcc121157f86090827ff65084137fb284209ff9942101dfcca10827fd65084517eb284209ff1942104df8ca10827ff64084137fb204209ff99021015fcc810827fd64084017eb204209ff1902104df8c8108a3ff540844fff2a04228ff5502113ff8a810827ff63084137fb184209ff98c2100dfcc610827fd63084017eb184209ff18c2104df8c6108a3ff530844dff2984228ff54c21137f8a61089fff430844dff2184200ff50c21137f88610826fe6208413ffa904209ff9482104fdca410827fd5208451f6a904209ff1482104ffe8410827fe4208413fea104209ff1082104ffe6410827fe3208413fe9904209ff0c82114dfcc2108a3ff5108451ff2884228ff54421147f8a21089fff4108401ff2084200ff5042113ff8821089bff3108401ff1884200ff4c421137f86210827ff2108413f79084209ff8842104fec4210827fd2108401f69084209fd4842104ffec010827fe60084097f3004209ff58021005fac010827fc6008451ffa804228ff94021147faa0108a3fc500844fffa004227ff10021137fe601089bfc3008409ffb2c8004bfd9640027fccb2000efe6590009feb2c8025bf59640027f8cb20012fc65900057eb248002ffd5240017fca92000bfd5490005fe2a48004ffd8e40027fcc720006fe6390009ef31c8001b798e40027fac720002fd6390009eeb1c8000b758e40027f8c720012fc639004bffa9c8024ff94e4012ffaa720093fc5390005ffa1c8002ff90e40017fa872000bfc4390009ffb148004ff98a4004dfcc520013fd62900017eb148004ff18a4012ffea520
  | 6 => 0x5ff3226202bf99131007fac898802fd644c465fe3226202bf1913100778c89880abc644c467ffaa26232ff9513119ffaa8988cbfc544c4037fb1a6201ffd4d3100ffca698807fd534c403fe29a6201ffd0d3100ffc8698807fd434c403fe21a6200ffd8931005fec498803fe624c401feb126200ff1893104df8c4988cfff524c467ff2926233ff5493119ff8a4988cbff424c401ff2126200ff50931197f88498807ff324c403ff1926201ff4c93100ff86498806ff614c467ffa8a6233ff9453119ffaa2988cffc514c465ffa0a6200ff90531007fa82988cbfc414c403ff98a6201fdcc53100ffc6298803de314c403fe18a6201f70c53100fe86298803ff604c4017fb026200ff98131007fac098803fc604c4097e3026233ffd413119ffca0988cffd504c467fe2826232ffd0131197f88098807ff304c403ef9826201ff0c13104ffecb90826ff65c8413ff32e4203bf9972104efccb9080e7e65c8413feb2e4231bf5972104efacb908027d65c8413fe32e4209bf1972104ffec990826ff64c8413ff3264202bf9932104f7cc99080abe64c8413feb264200bf5932104f7ac990802bd64c8413fe3264209bf1932118ffea9908c3fe54c8463feaa64230ff1532104ffec790826ff63c8413ff31e4201bf98f2104fbcc790806de63c8413feb1e4200bf58f2104fbac790802dd63c8413fe31e4209bf18f2118ffea7908bffe53c8463fea9e422fff14f21187fe87908bffe43c8401fea1e422fff10f2104ffea590827fe52c8413fea964209ff14b2104ffe8590827fe42c8413fea164209ff10b2104ffe6590827fe32c8413fe9964209ff0cb2118ffea3908c7fe51c8463fea8e4231ff14721187fe8390803fe41c8401fea0e4230ff1072117ffe6390803fe31c8401fe98e422fff0c72104ffec190827fe60c84097f3064209ff58321005fac190827fc60c8463ffa864231ff9432118ffaa1908c7fc50c8461ffa064230ff1032117ffe61908bffc30c8453ffb2c4229bfd962114ffccb1080efe6588453bf32c42039f9962114ffacb108a6fd6588401beb2c42009f5962114ff8cb1080efc6588401ffb244200bfd9221177fcc91080afe6488401feb244200bf59221177f8c91080afc6488453ffaa4422eff9522114ffaa9108bbfc5488401ffb1c4200bfd8e2116ffcc710806fe6388401feb1c4200bf58e2116ff8c710806fc6388453ffa9c422dff94e2114ffaa7108b7fc538845dffa1c422dff90e21007fa87108b7fc43884597eb144229ffd4a2104ffca5108a7ee5288453fea944229fb54a2104ff8a5108bbff4288413ff2144200ff50a2104ff885108b7ff3288413ff1944200ff4ca2104ff86510826fe6188453ffa8c4229ff9462114ffaa3108a7fc518845dffa0c4200ff90621007fa83108bbfc418845bff98c4200ff8
  | 7 => 0x2080bbc4390401ffb148200ff98a4104dfcc520803fd62904017eb148200ff18a411cffea5208e7fe5290473fea948239ff14a41017fe852080bbf4290405ff2148202ff50a410077a852080bfc4290471ff9948200ff8ca41007fa65208e3fc32904057f30c8239ffd46411cffca3208e7fd5190473fe28c8202ffd06410177e832080bf74190405fe20c8202fd106411c7fe63208e3fc3190401ffb048200ff98241025fcc120803fd60904017eb048200ff182411cffea1208e7fe5090473fea848239ff14241017fe812080bfc4090405de2048238ffcc2411c7f861208dfff655046f7fb2a8237ff9954101dfccaa08dffd655046f7eb2a8237ff1954101df8caa080aff6450405ffaa28202ff95141017faa8a080bfc5450401ffb1a8200bfd8d41007bec6a0802df635046dff31a8201bf98d41007fac6a08dbfc63504037e31a8200f718d4100db8c6a08dfff535046dff29a8237ff54d411b7f8a6a080bff4350405ff21a8202ff50d41017f886a0803ff62504017fb128200ff98941007fac4a0803fc62504137e3128237ffd49411bffca4a08dffd525046ffe2928202ffd0941017fc84a080bfd4250405fe2128236ffcc941007fc64a0803fd325046dfe1928202bfd85411bffea2a08dffe515046ffea8a8237ff14541017fe82a080bf74150405ff20a8200ef90541017f882a080bbc4150405fa20a8236ffcc5411b7f862a0803ff60504017fb028200ff98141007fac0a0803fc60504097e3028237ffd41411bffca0a08dffd505046ffe2828202ffd01410177e80a080bfc405046dff9828236ff0c1411affecb188d6ff658c46bff32c6203bf996311affacb188d6fd658c46bfe32c6203bf19631007fec918802ff648c469ff3246202bf99231007fac918802fd648c469fe3246202bf192311affea9188d3fe548c46bfeaa46234ff1523100dfac718807ff538c403ff29c6201f794e3100ffaa7188d7dd538c403fe29c6201ffd0e311a7be8718807fe438c403fea1c6201ff10e3100fb88718803ff628c401ff3146209bf98a31007fac518802fd628c401fe3146235ffd4a311affca5188d7fd528c46bfe2946234ffd0a31007fc8518803fd428c469fe2146201ffcca3100fbe6518807fe328c403fe9946200f74ca3100ff86518806fe618c46bffa8c6235ff946311affaa3188d7fc518c469ffa0c6200ff90631007fa83188d3fc418c403ff98c6201f7cc63100fee6318807fc318c403fa18c6200ffd8231007fcc118812fe608c401feb046200bf58231007f8c1188d7ff508c46bff2846235ff542311aff8a1188d3ff408c469fe2046201ffcc23100ff86118807dc308c467ffb2a6233bfd953119ffcca9880efe654c467feb2a6233bf5953119ff8ca9880efc654c401ffb226200bfd91310077ec898802bf644c46
  | 8 => 0xf0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1002fc615087fffa8a843fff945421fffaa2a10fffc5150805ffa0a8402ff105420177882a10fbff315087dfe18a8400ffd8142005fec0a1003fe6050801feb028400ff18142025f8c0a10ffff505087fff282843fff541421fff8a0a100bff4050805dfa028402ff101421f7fe60a10fbfc3050813ffb2c6409bfd963204ffccb1900efe658c813feb2c643dbf5963204ff8cb19026fc658c813ffb246409bfd923204ffcc91900afe648c813feb246400bf5923204ff8c919026fc648c87bffaa4643cff952321effaa9190f3fc548c8037eb1c6401ffd4e3200ffca719007fd538c803fe29c6401ffd0e321e7be8719007fe438c803fea1c6401ff10e3200fb88719026fe628c813ffa946409ff94a3204ffaa519027fc528c813ffa146409ff90a3204fdc8519027fd428c801f6a146409ff10a3204ffe6519027df328c803f79946409ff0ca3204fd86519027ff618c813ff30c6400bf9863204ffac319002fd618c813fe30c643dffd46321effca3190f7fd518c87bfe28c643cffd06321e7f88319007ff318c803fe18c6409ffd823204ffcc119012fe608c813feb046400bf5823204ff8c1190f7ff508c87bff284643dff542321eff8a1190f3ff408c879fe2046401ffcc23200ff861190efff654c8777fb2a643bff9953201dfcca990effd654c8777eb2a643bff1953201df8ca99003ff644c8017fb226400efd91320057ec8990ebfe644c8057f3226400ff59132005fac8990ebfc644c8057e3226400ef1913201578c8990efff544c875ff2a2643bff551321d7f8a899026ff634c803ffa9a6401ff94d3200fbca699007fd534c877eea9a6401ff14d3200ffe8699007fe434c803ef21a6401ff50d32007ba8699007fc434c8037fb12643bffd493204ffca4990effd524c813fe292643affd093204ffc8499003ee424c801fea126400fb5093204ff88499007ff324c803f79926409ff8c93204fbc6499027fc324c813ee1926401fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c877ffa8a643bff945321dffaa2990effc514c875ffa0a643aff1053200ffe6299007fc314c803ee18a6400ffd8132005fec099003fe604c801feb026400ff18132025f8c0990efff504c877ff282643bff541321dff8a0990ebff404c875fe2026401ffcc13200fbe6099007fc304c873ffb2c8239bfd96411cffccb2080efe6590473feb2c8239bf596411cff8cb2080efc65904057eb248202ffd5241017fca92080bbe5490405feaa48239ef55241017f8a920803ff6390471ff31c8201bf98e41007fac720802fd6390471fe31c8201bf18e411cffea7208e3fe5390473fea9c8238ff14e41017fe872080bfe4390471df21c8202ff50e41017f887
  | 9 => 0x1000800406c01000000000801400400c00401400000400000000000000000000402c02002800000002400404c02800000c01c00000001c02400400000401c01000000001401003000800402c04801002400400000000004800400800000000000003c00800000000800000000800400400800c00003804800000000c00000800000400000801c00000400c00800000800401400085ffb2a8642bfd9543217fccaa180efe6550c85feb2a8642bf59543217f8caa180efc6550c037fb228602ffd5143017fca8a180bfd5450c05fe2a28601bfd8d4300ffea6a1807fe5350c03fea9a8601ff14d4300ffe86a180bdf4350c03ff21a8601ef90d4300ff886a1807bc4350c03ee21a8601e710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1826fc6250c85ffa928642ff94943217faa4a190bfc5250c05ffa128602efd0943017f884a1807ff3250c03ef9928601ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a1802fc6150c85ffa8a8642ff94543217faa2a190bfc5150c05ffa0a8602ff1054300ffe62a1807fc3150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028604bf18143217fea0a190bfe5050c85fea828642ff14143017fe80a180bfc4050c03ff9828601ff0c14304ffecb21026ff6590813ff32c8403bf9964204ffacb21106fd6590813fe32c8409bf19642015fac92100bff5490805ff2a48402ff55242017f8a921027ff6390813ff31c8401bf98e4204ffac721002fd6390813fe31c8409bf18e4220ffea721103fe5390883fea9c8440ff14e42017fe872100bfe4390881df21c8402ff50e42017f8872100bbc43908137f3148409ffd4a4204ffca521027fd5290813fe2948409ffd0a4204f7e852100bef4290813fe2148409fb10a4204ffe6521027fc3290813ffb0c8409ff98642005fcc321027fd61908017eb0c8409ff1864220ffea321107fe5190883fea8c8441ff14642017fe832100bfc4190881ff98c8440ff0c64204ffec121027fe60908097f3048409ff58242005fac121027fc6090883ffa848441ff9424220ffaa121107fc5090805ffa048402ff10242207fe6121103fc309087fffb2a843fbfd95421fffccaa100efe655087ffeb2a843fbf595421fff8caa100efc65508137fb228402ffd5142017fca8a100bbe5450805feaa2843fef55142017f8a8a1003ff63508017fb1a8400f7d8d42005bec6a10fbfe63508037f31a8400ff58d421f7f8c6a1006fc6350801ee31a8401b718d421fffea6a10fbfe535087ffea9a843eff14d42017fe86a100bbf4350805ff21a8402ff50d420077a86a100bfc43508057fb12843fffd494204ffca4a10fffd5250813fe2928402ffd0942017de84a1027fe4250813df2128409ff1094204f7884a100bec425087dff9928409f
  | 10 => 0xa000000000033e859407966c0004ab00006ac0001c640a80009ee4ca000000109a3ec00000000007233b9800000074d00000000003c224c00000004200000ef4f5628e3c515609421c340a1490000000394000000000000000000000800c00001000805400000000401802c01800800000400001400000400000000005000000c00000802800000802805000c00400c00800001000001000000000c05800000000800400c00000002400002800000400400000800006c00801002c00800000400004000400401400001c00000400401800000404400804c00000401000000400002001800402800000c00000400c00004c00400001000801400000403400400402402000400400401000000c00c00000000000c00000000000001000000000800400c01800401400000001400800400c00001000400c04002000000400000800000800400001000800000400400001c00000c00c00000800800000000000800403c02c00400400000001000404000400000001800006000000000c00000001802000001800000400400000c01c00000802000400000001c00000801800800802001400800000401400400000806001000800400002001001400000000001001c00002001400407002c00002800c00001000401400800000c00002000400800c00400002c00401001800001002000000c03800801c01400000000002800400400003c00400001000000000001000000000402400400c00003005402802800801800800400000402c00c00002800002c01000401000c00000400c00000003000801401000c01001000400002000800c00800800400c01001003003c01400000001c00801002c00000400002801402000000c08400000000003801400804800000400000800000800801001800002000000000000800800400000400400400c00800400000000400002000000000000000000c00401801402c01800c00800400001000400000000000c00401400801000005400800001000001400001002001c00003000000c03800800403000800c01002c00400c00402000c00c00400c00400400002800000c00000c00804000400000001c00400800002001400803000c00000001000400800003406402400006c00000800801403403800000000800400000000800401800000400000800000000400000803800004000400401000000001801000c00000800000000800002401400000807c00000000000001401801000401403c00001003000000000400800000801c00000400800401000000400400400000c00400402000401c00800001c00000000004004800000401000002800400c01000401000c09c00000000001800c01c00000c00401003800000001000002806400004400001c01000400c004004000000024020014028004024000014000024
  | 11 => 0xbf00000001fe0e3e000000000031e3bf4350000b000000000000a304770001cc46224473518c78000000000000000000000017485ae0000000000dfc0000000b50c626b100021f000049f0000000c5c348000000000082e05200000001050000000000000000100c90000020f8000f02000000135c0ea19300000008223d2305000000081000000000000003b080007720000000d600000d102b00000000003d2800000000024e0ff021074c000000067080b36c0890e8a3b30ad848055a4461029bc80cc7a32c28560262796110800000059920e0a2800000019f108840c0000000000bd2000082102c57684436a17fcce200000000002fc00000000001920003c3000000080a42400000f00000001ee4df80000469aa800050c3af92800000002ab0000bca00000000008940001f8984800000000000000000002301c9c00036913d0000000000000000079272900000008ec0d4000146826800000002b40002b00001104d6c0003db09c06c850628a0000e1c13634b00005d60003b30000bee000000000000069b437a14c0ec08203a0000d0a023000104c000737000138096603624600801665311c6027c23251e3fa97444b206c4178e241a07d83b881708024100661a38bac3a619403049a68690001d0800000038a00000000000fe8000b4a000000000000000036711140000000000360000803000000018829a00008e03fc0000000000f3c00036780007786cc0000000c220000001b6450876a1ee0424b5234c1d21aa0acc2922928f442fe6c40fb800000000000000001e452c0001edc00082536113e4a9c0000000280bd41f82bd8cbc0000bf3c49a88e8c877000000012e06f0000008cc80002a6800000085d0000000b9e0000279de8f684ea0e604c06a400000000000f60000000ed80001dd00004188704f200006fc0000c72259b580004423e2168066e0000001f2800000000016e800036b17c14a000042d15081c4a8a0000af92f800000500000000005e700000007c45b30001018000813000000000000000000004b40002db0428cb87e700009a40006da0001f1800067040d8e1800000000007a4fec2e4000000000084338d1010c7466522417ac5ec0000000000caa1ea000146c0005000000000ea65d500001ccae60004320000d2634a0000d40a0200024709b47fe2db15198d4b063251fa800000051f4020000230000000000000033923f11306760f70000be4d4071500014d00000000630000000000000000000087500009bcfc8164382984046278e2ad00004867ad05605f000000000000003e265d00000007b252f0000a5c0000003b2000000000000000000005530f91e11054508345150ce780000b080000002282191ce4000182000018c00051d00000000004d239680ec00029f2ce00000001cd4428e9c38
  | 12 => 0xbc3b21fa04b0dfe15c1e08894aa248240600009260001779aa43ac38532200c400000035e88e8c0272e17e80f4df2011005800064c6042278e7c000000000068088071100005b836c00000000005c00001b915d8d161970701310f1a3bb43b1ba00006a11bc1df4000000183834c000769356000000000000015b000061423795f400034d3a70a647b40000001fc0b7c72530b0c4c02c68700005b50aa0e111e1ca80000000140000d300000000000000520363849087628f1500df49060cb09f033d0fa19c315a0808aa6fd2b11cc856c0240428b480f85983f884ac11c7580ec959400000016e00003540003bd951c3de1e539780000000000e80000000000000000000026206b8e34c062860f80798b1203800016448ca36f061800000078b000000000000000000009de6b700000000003c52a78000a544ff10080000003ea2d892940000002aa0000f5e36031605040002021050000000156237000043e0003720ab800016f3ea80009d8113179000006864e0018b1c0000b529e18801e8000174000000000000000007441d131f8d700000000df00000bc682003932c00000005a000000000033980000000000001068cfa0dc000000000059f33f15bc3463930000000b8c00009f8144d1828c42f211820000041c016854c1ed0a59b4064e7d61df03f4df05f5293947047e0000bc1b341447e500000000002bc3738850f7e64f18f8dc4bc25020b408d40008262b880000000002e28d64bbc2e900004cc0140003200b689684da31a000000001e3ff80f87b62c00000974000000000000052085c3448000fd200000009988c8000000000070e43d0000f4c00000013900000003b800010e4cb430229700000000000cd15d4a56000000000000085705800000000002b0965800000027801f40000002b51d286a285f3469d6c2d21ec11b02ac2c05b5048889c0e400616599200107df000000000006514680007da4d540e081c6660c52dc093c08608c24f0dd028820d1a18050edc18e2ce80bc6cc80e3b0000096200000006206f63ab00000001744053aa800000000000000000004ed0508db441239d0000000a2260b07100005223e724d1f2c0f23672628f2096e835299952cb1a69935d08600fe3f6000044800000000000000000000001bb400030141c8000cb21c9043064800000000000000000003879cacbb474300000005c2000000140cc920001ad9f80b827ae2789d484bc1f30180c40fa60843c8829c04c5bd0001b5400038f1a79f14d103400000000c342791cf07d000075d01a8000f20135000000000000000686ec00000003580000ae40e00009383701c0000184c30e86702d800081a09309b86b80000000000000fba0520990ae40003b40e39ce89860000000c701ba3ef0001b78000000000000000078726f20d00001c800
  | 13 => 0xdd9c5c4d400000006bc0000000db83fc0000000d200000007071250000000088051972c55812a2f0000000042337d80001f44f43f710744ca0000f393acb6e00000c800000036a29f901c000000000000054e000233814c21c78c3131b80c0480612982d83d06661c0000084e6af000000007e0e8077019c17c2bd312942cd762ca2219ddc0000003dc21e800000021e0000bde4350001dc83b67822488b4c8d82c100011b4c5a00030e20ecb9009a43c00001b40002439e840007de000118c8d0000260800032a0db000000000022a000076800045000003ccd867c100019480000000000000000000000000000042400000000004141fc1740556000000000000000000000000000003f60000000000311989c42e14e34d083820215733380004400000a2874cc7058f17a1b440004ad3ca0b380dc00023f896c0000003f415e08306512421f1c0006752511fdc62e00021721690127a72851fecbc42f33bf00003fe00019f880000065000000000000000000d680007a93631a0cc5200000000010a2000000000000073d15400004a867f088800000085000002bc8cc08b217963066a00021f05e87e42ec02500000002411b60694f4801710d9b8c78c47320619080006b2000000000000000002e4eea82828909001c87062f91e882f23c000c128c3740002a91264b206462ae80008c42823b1195cef201f0f580387d200043589fc6fe7bb3cd9a9000041613a909904e4cc0da8000bec3880000000f923750001410f104531bf00003a44bd0fd86601783ba00000002d62390001ec483600033000006962c207d87f03422fa27400001200003e102c8c3a0000d3800000079202a00000d04e512e039c154300244a0785ac66a0001a9c08000031814b50b0000000000072200000000000000002ee0000cb02a40000114f9000000006b05a200032380000002b2290976ce583042b4800045a094000000075a0000220000e882ea00000000ee6410000000fc4223438051841e00015f0d050923ac390800030c61b0001f302b4000162038c6420e5239000086c6153308bec37800036284707c87fc09292f078824d01b83c4ddc6ab30b80c8b9200000019acd826c81458000218155000087810e5a236e86587e65c21ea80009b03a02a5000059283300019e0bf616a31108dcb9c0000000000000000000000067800000017b42843051058000a6e19902e88442905a63e780008426a50002074a8000016c18c85f814f3aa1fe88b84b821607547245aa1c19fcc4e84c643000000000ce08196bceda00f00011380003f0176877c8ac3420001b7c000000000220021a2df1830ea029a00010b07809b60043698ac46ec0220000dcc000059000098400000000000000000001e3800045c0550750c4892c5ee1c58000000000400979000000000e8000a
  | 14 => 0x4d817223c9a44adc862426170000065323516e400000020400010800003360788b783d40730bd400043a2930a0506000022d8fdc00000036d80000001493f308480002aa00000000000001b189f10d804818500001ac57000004e02a21164010d508f64920b613444760000000b8c68a5443fe80306686391878a5476057a33a00001ec8471321acc25081f2739fa800026823a000000000000020447d60003bf89b86305090bd8000000242000198c000636101800045817500018189c435f00000007d03f93b28000b0e85234206d0aae01000013d44085603f6800105270b0000000000584000058c00000024680004e623026780000003771529bd895e0001858000862000000004856800039f0acc00024720c9c4000000000003200000003be0000c307332570f3400000000000000000000b98de40664c200011e000083d1419c2400000000000009ac00001d02ec27800034a00007420000000b40000865353012ce0262a00000000007f40000180f0600000012980000000231e001527680dc876000000000000000000001af0955062000000000066c00000000000004e91d70000652000000000000008a403a2040007bd39a0000000000391095c0007203f0800079e02a00000000000000000a60ace000040855035a12718a8ff800021d0001e74f7817020b8e6000000016e80000000000000678000812000000000053d1b710a4e9247c00000005aa87e05315400008081788da0c5e0003d99524c9a000000000000000000003d49f00eb000000000049507e00000000000001b2cd7850f29c89200000000d81fe4ed84bb0c21bd400033a3568000000529000000000000000000009205a40588000bba00000017280000000000888000000000099c00000000012909b8000198825400027d0ac80005bc0000bb88f800047a0000cb800000004f1a740000cd1cb10c045642521b99c90e201c000063108a00012b16a0cf20002440000d1e000000000104800008f00000000003a40e10eb86f0271992c7ca2cc144000000070812489603620001f0057400080508e92040000003141bbceb250d10405000005fd000000000000041100000001710001ae00000001389e6481e29c036800000074f00017f0000000000000056e0000000a4c17049700020e8eac5b222200000007cd2eb9a4021e85434311790e46e103d008494e000263a1846c20df0a80000432000026000008400000013ec00053e22e948c30a5f000000008d20001c500000003aa28a935024c19427980004520000001638e480492be0675104000358000000000043d81f9030000000000000000000016780000000000000a7400000018905284511579c748240001429d78ec65d82548024d0055900003b0bcc18d37a1c70b166be29d8c8c1005a100000000000002
  | 15 => 0x85a1fcdb80001be102400034700000000005e3000000000056d17f983c0000002c41fad0da18100000009cc71b27d000015c6e624e9a5ce180002f600002a43c301488689b245a0fa80000007183b800000003973d51f443dc1f61258450a9830c0000feca4456315d025800243f2269d0400076f28c968c00054140d170c00000000000000000000001820a0a5f400020fc4ee000016862ccee1210001bcc18451318d8c642440000000000b2e0003e18e6c00067a000013400000000003a4b4e4aa000115c66000000000000007b20001800e04740195000000035d00006cc60600000016ac0000002aa996c7c20001e700000002520000000ad00000001cfca7000000020b000030d0d49440a840003a883b4fc63460000f8c8c200000d1ef90d000024782940000003378c58000000000026c82a0c000000004f000018e8e0400006205b80000002891ee9afc0000000001cd81de55c00004ec3200001fd0000d6a0001228624d2a0001280b3c0000000001ba4130582000044000000026497306443ca371000000024c0978000eec00000000007a04dd16300003ae88332a20d8c3e00038c8d94c1c0000e79f500000002f8800000030841b9c580007a008f800037a6f138695f88a8730287125085439410e00000005b02df92b066467c1eb1b94cda84f000210400000000000002a60000001148bfc00030681a8000000000000000000008396680000002bb97ccdae0000000000ba62130a500000005920000000ab674700000005e064c00000007cc56b000000000000000017a00b045f000000000000037d1d2ca2c2760000b64ffc34e13f0704c6626b39a80005ce3090001cec76a7a61a4a0b4c7c3ee0ef00003840001d89c2800000034f80010e87a800000000000002248644000000000068800024600021cc7984cd2c9800027200034f045c00048a2e202702ec00011e93907fa00000000009a00000000c5009c58a41191c450e08300d800000016723584a4e4c15e1131c4854479f00019a0cac00025c8698a0e0131c108d08040003b59a4853c41e07ca18c3f22f74068f5cd947d93d81de0b5c5d40001e6800013a31d8000b8e0001bd0a74f9c1fa15f82650641a82b21c786567da29a9764a64000000000000079333b181cb68000000000025c03900000004c600027ea16cdee0000ea11d400000000012d400000000012140be00000000000000000000a582fa2c33ba13f0c1871321a02750842440208f788501dc0ba12fc0000000000000cdc0003348000f800bd09e986428632c07f0000c8a3a91060000dd83203e80094d0211b39c20ac58a38e1a98364000795017187861c0001caa1e46886ae22c93d8ece84b0001320b5a00041e072c5dc5df00000007380892fd190d1080002bf8000dd47ef3310dc05522100a38784
  | 16 => 0x1e3cf744fe0000e940000000001e15094000000000000000012f82a038802b0e5165400007000000001240471cc800000065e0280d88336856172800000008f31e1d5c00000000014d8d6812d1d780009dc00016400010427003cc188476e0270000000000546000000000000033d800109c1ce00004540000000000000f6a0001c8000000060525900001bc0000000000000000000000000032400000000007dc0000000000000171192800000000000002ca00031b8cb46341232ba00004640000c00000fb65483ce060c0000002380530c1200007c000042a000267161893627b1d18000d7265f40b800000070338216b000035741f1fc80000f0173200036458128b8f600c26c0000000000063d00000007be22f0000f2c00075a3e9078cd382b8000000000000006912e8b285720c51e5c2c40d517f0000b9a1e419e8ad49c20003a8000000000000011f400000013000000000002198d58000000000116091686e000000102c000000000000000000012a09be6c900010ac6aa00000008cc59a0002af85984a24b6433100000000008d14c00582800001bac0c829b000032890c1022bc80f00000000001f5c02a40a2581eb0734000000000000006940c9b480000002fc8000980000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe65508100067d6550810016be6450810006bd6450810005df735081002ddc73508101f6de6350810006dd635081004eee6250810006ed6250810005f77150810005f4715081004cff768c810024fe768c810004fd768c810024fc768c8101ee7e658c8100067d658c8101e6be648c810006bd648c81000ede638c810006dd638c81004eee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c8101de7e654c8100067d654c810005bf744c810035bc744c8101d6be644c810006bd644c81000ede634c810006dd634c81004eee624c810006ed624c810005f7714c810005f4714c81008cff7690410024fe7690410014fd7690410024fc76904101ce7e65904100067d6590410016be6490410006bd64904101c6de6390410006dd6390410006ee6290410006ed6290410025fa7090410005f9709041008cff76504101be7e65504100067d6550410016be6450410006bd6450410005df735041002ddc73504101b6de6350410006dd6350410006ee6250410006ed6250410084ff768c410024fe768c41000cfd768c410024fc768c4101ae7e658c4100067d658c4101a6be648c410006bd648c41000ede638c410006dd638c410006ee628c410006ed628c410025fa708c410005f9708c410084ff764c41019e7e654c4100067d654c410005bf744c410035bc744c410196be644c410006bd644c41000ede634c410006dd634c410006ee624c410006ed624c410004fd76c841003d7e75c84100057d75c841018e7e65c84100067d65c8410035be74c8410005bd74c8410186be64c8410006bd64c841002dde73c8410005dd73c841017ede63c8410006dd63c841004eee62c8410006ed62c8410004ff768841004cfd768841003d7e75884100057d758841014e7e65884100067d6588410176be6488410006bd648841016ede6388410006dd638841004eee6288410006ed6288410236f66188410025fa7088410005f97088410004ff76484101667e65484100067d654841015ebe6448410006bd6448410156de6348410006dd634841004eee6248410006ed624841022ef6614841004cff7608410024fe7608410004fd7608410024fc76084101467e65084100067d650841013ebe6408410006bd6408410136de6308410006dd630841004eee6208410006ed6208410025fa7008410005f97008410025fb7644010006fb7644010004fb76440100077b75440102277875440100277a6544010027796544010007bb7444010007b87444010027ba6444010027b96444010007db7344010007d87344010027da6344010027d96344010007eb7244010007e87244010027ea6244010027e96244010025fb7144010027f3714401021efa6144010027f26144010007f24144010007f14144010007f23144010007f13144010
  | 1 => 0x8c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff7650c10024fe7650c10004fd7650c10024fc7650c102167e6550c100067d6550c10016be6450c10006bd6450c1000ede6350c10006dd6350c1002f9c4350c1004eef759881004eee759881004eed759881004eec759881004eef749881004eee749881004eed749881004eec7498810006ef5498810006ee5498810006ed5498810006ec549881004eef739881004eee739881004eed739881004eec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881004eee719881004eec7198810006ef5198810006ee5198810006ed5198810006ec5198810006ef4198810006ec4198810006ef3198810006ec3198810026ef7098810026ee7098810026ed7098810026ec7098810026ef5098810026ee5098810026ed5098810026ec5098810026ef4098810026ee4098810026ed4098810026ec4098810026ef3098810026ee3098810026ed3098810026ec3098810026ef1098810026ee1098810026ed1098810026ec1098810004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810014fc7458810004ff735881000cfe735881000cfc7358810026ef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef4258810006ec4258810006ef3258810006ec325881004cff715881004cfd7158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f51058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef4158810006ec4158810006ef3158810006ec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef4058810026ee4058810026ed4058810026ec4058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026e71058810026ee1058810026ed1058810026e51058810026ec105881004cff7690810024fe7690810004fd7690810024fc769081020e7e65908100067d6590810016be6490810006bd6490810206de6390810006dd639081004eee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc76508101fe7
  | 2 => 0x267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267710594100267e10594100267d10594100267510594100267c1059410004ff755901001cfe7559010004fd755901001cfc7559010026bf7459010006bf5459010036be5459010006bd5459010036bc5459010004ff735901000cfe735901000cfc7359010036bf4359010006be4359010036bc4359010004ff725901004cfc7259010036bf4259010036bc4259010014ff7159010014fd7159010034fc7159010036bc4159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006bc3259010036bf7159010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006bc3159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026be1059010026bd1059010026bc1059010004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10014fc7458c10026df7358c10006df5358c1002ede5358c10006dd5358c1002edc5358c10006df4358c1002ede4358c1002edc4358c10004ff7258c1004cfc7258c1002edf3258c1002edc3258c1000cff7158c1000cfd7158c1002cfc7158c1002edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006dc4258c1002edf7158c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006dc4158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc205
  | 3 => 0x7628851004ef6628851004ef46288510007e4628851004ee46288510267e65288510267e55288510025f67088510025f4708851025fe6208851025fe42088510024fc76485100067f65485101667c6548510006bf644851015ebc6448510006df6348510156dc6348510006ef624851004eec6248510005fb7048510025f87048510025f4764851004ef47648510024f47648510255f77548510255f5754851000777654851024f746548510007b76448510007b46448510007d76348510007d46348510007e77248510007e7624851004ef6624851004ef46248510007e46248510007f37048510025f67048510025f47048510007f07048510004fe76085100067f65085101467c6508510006bf640851013ebc6408510006df6308510136dc6308510006ef620851004eec6208510245f67108510007e52108510014ff765011005cfd7650110014fc76501100067f655011011e7c6550110006bf6450110016bc6450110006df6350110116dc6350110006ef6250110006ec6250110005f77150110005f47150110027f0105011000cff764c110054fd764c11000cfc764c1100067f654c1100fe7c654c110006bf644c1100f6bc644c110006df634c11000edc634c110006ef624c110006ec624c110005f7714c110005f4714c110027f0104c110004fe76c81100067f65c81100ee7c65c8110006bf64c81100e6bc64c8110006df63c81100dedc63c8110006ef62c811004eec62c8110005f671c8110005f571c8110007e521c811004cff7648110004fd764811004cfc76481100057f75481100657c75481100067f65481100be7c6548110006bf64481100b6bc6448110006df63481100aedc6348110006ef624811004eec6248110005f77148110005f47148110007e521481100067f65c41100467c65c4110006bf64c411008ebc64c4110006df63c4110086dc63c4110006ef62c4110006ec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c411023f7865c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c411023ff251c411023ff151c4110007f221c4110007f121c41100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067c42594100067f32594100067c325941003e7f71594100067e715941003e7d715941003e7c71594100067f41594100067c41594100067f31594100067c31594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d4059410
  | 4 => 0x891004eed711891004ee57118910006ef5118910006ee5118910006ed5118910006ec5118910006ef4118910006ec4118910006ef3118910006ec311891004eef701891004eee701891004eed701891004eec7018910006ef501891026eee5018910006ed501891026eec5018910006ef401891026eee401891026eec4018910006ef301891026eee301891026eec301891026eee1018910006ed101891026eec101891004cff7690910004fe7690910004fd769091004cfc76909100067f659091020e7c6590910006bf6490910016bc6490910006df6390910206dc6390910006ef629091004eec6290910005f67190910005f57190910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101fe7c6550910006bf6450910016bc6450910005df7350910055dc7350910006df63509101f6dc6350910006ef625091004eec625091004cff768c910004fe768c910004fd768c91004cfc768c9100067f658c9101ee7c658c910006bf648c9101e6bc648c910006df638c91000edc638c910006ef628c91004eec628c910005f6718c910005f5718c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101de7c654c910005bf744c91005dbc744c910006bf644c9101d6bc644c910006df634c91000edc634c910006ef624c91004eec624c910074fe76905100067f65905101ce7c6590510006bf6490510016bc6490510006df63905101c6dc6390510006ef6290510006ec6290510024fc76505100067f65505101be7c6550510006bf6450510016bc6450510005df7350510055dc7350510006df63505101b6dc6350510006ef6250510006ec6250510005fb7050510025f8705051006cfe768c5100067f658c5101ae7c658c510006bf648c5101a6bc648c510006df638c51000edc638c510006ef628c510006ec628c510024fc764c5100067f654c51019e7c654c510005bf744c51005dbc744c510006bf644c510196bc644c510006df634c51000edc634c510006ef624c510006ec624c510005fb704c510025f8704c510024fe76c8510024fc76c85100657e75c85100057d75c85100067f65c851018e7c65c851005dbe74c8510005bd74c8510006bf64c8510186bc64c8510055de73c8510005dd73c8510006df63c851017edc63c8510006ef62c851004eec62c8510025fa70c8510005f970c8510004fe76885100657e75885100057d75885100067f658851014e7c6588510006bf6488510176bc6488510006df638851016edc6388510006ef628851004eec6288510005f67688510006f67688510245f77588510267767588510245f57588510007757588510005757588510007776588510267746588510007b76488510007b46488510007d76388510007d46388510255f57288510007e
  | 5 => 0x7e551d891025fe610d891025fe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d891025eef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ec41d8910006ef31d8910006ec31d8910006ef70d891025eee70d8910006ed70d891025eec70d8910006ef50d891025eee50d8910006ed50d891025eec50d8910006ef40d891025eee40d891025eec40d8910006ef30d891025eee30d891025eec30d891025eee10d891025eec10d89100657e75989100057d75989100067f65989100067c659891005dbe7498910005bd7498910006bf6498910006bc6498910055de7398910005dd7398910006df6398910006dc6398910006ef62989100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910055dc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc631891004eee6218910006ed6218910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e57118910007e65118910007e5511891026fe6101891026fe4101891004eef751891004eee751891004eed751891004eec751891004eef741891004eee741891004eed741891004eec7418910006ef5418910006ee5418910006ed5418910006ec541891004eef731891004eee731891004eed731891004eec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec431891004eef711
  | 6 => 0xf74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006dc42d8d1027edf71d8d10056de71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df70d8d1027ede70d8d10006dd70d8d1027edc70d8d10006df50d8d1027ede50d8d10006dd50d8d1027edc50d8d10006df40d8d1027ede40d8d1027edc40d8d1027ede20d8d1027edc20d8d1027ede10d8d1027edc10d8d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10056dc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10014fc7458d10006bc7458d10014bc7458d10054ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1004cfc7258d10006ec7258d1004cec7258d1006cff7158d10006f77158d10084ff7058d10006fb7058d10005de7618d10056de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10276df6118d10007d65118d10007d55118d10277d61018d10277d41018d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d102167c6550d10006bf6450d10016bc6450d10006df6350d1000edc6350d100579c4350d1004cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d891000cfe73d8910004fd73d891000cfc73d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef42d8910006ec42d8910006ef32d8910006ec32d891004cfe71d891004cfc71d8910024fe70d8910024fc70d891004cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891025fe771d8910007e651d8910
  | 7 => 0x91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110007b651d9110007b551d911028fb610d911028fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006bc32d911028ebf71d911005ebe71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006bc31d9110006bf70d911028ebe70d9110006bd70d911028ebc70d9110006bf50d911028ebe50d9110006bd50d911028ebc50d9110006bf30d911028ebe30d911028ebc30d911028ebe20d911028ebc20d911028ebe10d911028ebc10d91100057f75591100657c75591100067f65591100067c655911005ebc6459110005df7359110055dc7359110005ef7259110005ec7259110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c755911005cff7459110006bf7459110004ff7359110006df7359110004df735911000cfe735911000cfc7359110006dc735911000cdc7359110004ff7259110006ef7259110004ef725911004cfc7259110006ec725911004cec7259110074ff7159110006f7715911008cff7059110006fb7059110005be761911005ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110286bf6119110007b65119110007b55119110287b61019110287b4101911000cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10056de63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df53d8d10056de53d8d10006dd53d8d10056dc53d8d10006df43d8d10056de43d8d10056dc43d8d1004cfe72d8d10004fd72d8d10056df32d8d10056dc32d8d1000cfe71d8d10024fd71d8d1000cfc71d8d10056df31d8d10024fe70d8d10054fd70d8d10024fc70d8d10056df30d8d10055de76d8d1000cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10007d651d8d10007d551d8d1027fd610d8d1027fd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006d
  | 8 => 0xcfe7358a1000cfc7358a10026ef7258a10006ee5258a10006ed5258a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a1004cff7690a10024fe7690a10004fd7690a10024fc7690a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10016be6450a10006bd6450a10005df7350a1006ddc7350a10005f77150a10005f47150a1004cff768ca10024fe768ca10004fd768ca10024fc768ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca10005bf744ca10075bc744ca1000ede634ca10006dd634ca10005f7714ca10005f4714ca1005cfd769061028ebf6490610016bc6490610014ff7650610024fc7650610016be6450610006bd6450610005df735061006ddc7350610005fb7050610025f87050610054fd768c61027edf638c61000edc638c61000cff764c610024fc764c610005bf744c610075bc744c61000ede634c610006dd634c610005fb704c610025f8704c61007d7e75c86100057d75c8610075be74c8610005bd74c861006dde73c8610005dd73c861004eee62c8610006ed62c8610025fa70c8610005f970c861007d7e75886100057d758861025eef628861004eec628861004cff764861004eee6248610006ed6248610005fb7048610025f8704861026eef620861004eec6208610025f976c4210006f976c4210027f271c42100657e76d95100667e76d951001c7e76d95100067e64d95100067c64d95100067e63d95100067c63d95102977771d95100677471d95102977610d95102977410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f32d95100067c32d95102967f71d95100667e71d95100667d71d95100667c71d95100067f41d95100067c41d95100067f31d95100067c31d95100067f70d95102967e70d95100667d70d95102967c70d95100067f40d95102967e40d95102967c40d95100067f30d95102967e30d95102967c30d95102967e20d95102967c20d95102967e10d95100667d10d95102967c10d9510014fe76d91100067f65d91100067c65d911005ebe64d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d911005ebe54d9110006bd54d911005ebc54d911000cfe73d9110004fd73d911000cfc73d911005ebf43d9110006be43d911005ebc43d911004cfe72d9110004fd72d911005ebf42d911005ebc42d9110014fe71d9110024fd71d9110014fc71d911005ebf41d9110024fe70d911005cfd70d9110024fc70d911005ebf40d911005dbe76d9110014be76d9110006bf65d91100073f65d
  | 9 => 0xc6450b10005df7350b10085dc7350b1004cff768cb10004fe768cb10004fd768cb1004cfc768cb10005f6718cb10005f5718cb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10005bf744cb1008dbc744cb10006df634cb1000edc634cb10024fd7690710016be6490710006bd6490710025fa7090710005f97090710034ff7650710006bf6450710016bc6450710005df7350710085dc7350710024fd768c71000ede638c710006dd638c710025fa708c710005f9708c71002cff764c710005bf744c71008dbc744c710006df634c71000edc634c7100457e75c87100057d75c871008dbe74c8710005bd74c8710085de73c8710005dd73c8710006ef62c871004eec62c8710024fd76887100457e75887100057d758871004eee6288710006ed6288710025fa7088710005f97088710025f5768871004ef57688710024f576887102a5f775887102377675887102a5f5758871000775758871000575758871004ef66288710007e66288710007e5628871004ef46288710237e65288710237e55288710025f67088710007f27088710007f17088710025f4708871025fe6208871025fe42088710006ef624871004eec6248710005f77648710006f7764871029df7754871029df57548710007e77248710007e7624871004ef6624871004ef46248710007e46248710025f67048710025f47048710024fd760871004eee6208710006ed6208710007e52108710025fa7008710005f97008710014ff7650310014fc7650310016be6450310006bd6450310005f77150310005f4715031000cff764c31000cfc764c31000ede634c310006dd634c310005f7714c310005f4714c31004eee62c8310006ed62c8310005f671c8310005f571c8310007e521c831004cff76483100057f75483100457c754831004eee6248310006ed6248310005f77148310005f47148310007e52148310004ff755921001cfe7559210004fd755921001cfc7559210026bf7459210076be5459210006bd5459210004ff735921000cfe735921000cfc7359210006be4359210076bc4359210004ff725921004cfc7259210076bf4259210076bf4159210024fc7059210026be4059210026bc4059210004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10014fe7458e10014fc7458e10026df7358e1006ede5358e10006dd5358e10006df4358e1006edc4358e10004ff7258e1004cfc7258e1006edf3258e1006edf3158e10024fc7058e10026de3058e10026dc3058e10004ff7650e10024fe7650e10004fd7650e10024fc7650e1006f9c4350e10004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10014fe7458a10014fc7458a10004ff7358a10
  | 10 => 0xc42004dec724c420006f6614c420006f5614c42004ded7688420006ed7688420004ed76884202af6e75884200076d758842004eef658842004f6e65884202aeed658842004f6d65884200066d658842004fae648842004fad648842004fce638842004fcd638842004dee718842004fe6718842004fe66188420006ed618842004fe56188420006e5618842025ded708842025eee608842004fea608842008ebe64d9310004ff75d931001cfe75d9310004fd75d931001cfc75d931008cfd74d931008ebe54d9310006bd54d931000cfe73d9310004fd73d931000cfc73d9310006be43d931008ebc43d931004cfe72d9310004fd72d931008ebf42d9310006f671d931008ebf41d9310006f970d931028ebe40d931028ebc40d9310014ff765931008ebc6459310005df7359310085dc7359310004ff755931001cfe7559310004fd755931001cfc7559310006bf7459310004ff7359310006df7359310004df735931000cfe735931000cfc7359310006dc735931000cdc7359310004ff725931004cfc7259310024fc715931008ebc415931008ebf4059310086de63d8f10004ff75d8f1001cfe75d8f10004fd75d8f1001cfc75d8f10014fe74d8f10004fd74d8f10014fc74d8f10084fd73d8f10086de53d8f10006dd53d8f10006df43d8f10086dc43d8f1004cfe72d8f10004fd72d8f10086df32d8f10006f671d8f10086df31d8f10006f970d8f1027ede30d8f1027edc30d8f1000cff7658f10005bf7458f1008dbc7458f10086dc6358f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10006bf7458f10004bf7458f10014fe7458f10014fc7458f10006bc7458f10014bc7458f10006df7358f10004ff7258f1004cfc7258f10024fc7158f10086dc3158f10086df3058f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100879c4350f100457e75d8b100057d75d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10014fe74d8b10004fd74d8b10014fc74d8b1000cfe73d8b10004fd73d8b1000cfc73d8b10006ee52d8b10006ed52d8b10006f671d8b10006f970d8b1025eee20d8b1025eec20d8b10004fd7698b100457e7598b100057d7598b1008dbe7498b10005bd7498b10085de7398b10005dd7398b10006ef6298b1004cff7658b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b1000cfe7358b1000cfc7358b10006ef7258b1004eee6218b10006ed6218b1004cff7690b10004fe7690b10004fd7690b1004cfc7690b10005f67190b10005f57190b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10006bf6450b10016b
  | 11 => 0x6f4439842004ef6729842004ef5729842004ef4729842004ef7529842004ef6529842004ef5529842004ef4529842004ef7429842004ef6429842004ef5429842004ef4429842004ef7329842004ef6329842004ef5329842004ef43298420026f67098420026f57098420026f47098420026f75098420026f65098420026f55098420026f45098420026f74098420026f64098420026f54098420026f44098420026f73098420026f63098420026f53098420026f43098420026f72098420026f62098420026f52098420026f42098420004ff755842001cfe7558420004fd755842001cfc7558420004ff7458420014fe7458420014fc7458420004ff735842000cfe735842000cfc7358420026f77158420006f75158420006f65158420006f55158420006f45158420006f74158420006f44158420006f73158420006f4315842004ef7215842004eec215842004ef4215842004ee42158420026ef2058420026ed2058420026f61058420026f41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f4435842004ef7725842004ef6725842004ef4725842004ef7525842004ef6525842004ef5525842004ef4525842004ef7425842004ef6425842004ef5425842004ef4425842004ef7325842004ef6325842004ef5325842004ef43258420026f77058420026f67058420026f47058420026f75058420026f65058420026f55058420026f45058420026f74058420026f64058420026f54058420026f44058420026f73058420026f63058420026f53058420026f43058420026f72058420026e72058420026f62058420026f52058420026e52058420026f42058420004ff7690420024fe7690420004fd76904201ce7e65904200067d6590420016be6490420006bd64904201c6de6390420006dd6390420006f66190420006f56190420004ff7650420004fd7650420024fc76504201be7e65504200067d6550420016be6450420006bd6450420005df7350420095dc73504201b6de6350420006dd6350420005ef725042004dec7250420006f66150420006f56150420004ff768c420024fe768c420004fd768c4201ae7e658c4200067d658c4201a6be648c420006bd648c42000ede638c420006dd638c420006f6618c420006f5618c420004ff764c420004fd764c420024fc764c42019e7e654c4200067d654c420005bf744c42009dbc744c420196be644c420006bd644c42000ede634c420006dd634c420005ef724
  | 12 => 0xf3159020006bc315902004ebf215902004ebe215902004ebd215902004ebc2159020026bf7059020026be7059020026bd7059020026bc7059020026bf5059020026be5059020026bd5059020026bc5059020026bf3059020026be3059020026bd3059020026bc3059020026bf2059020026be2059020026bd2059020026bc2059020026bf1059020026be1059020026bd1059020026bc1059020004ff7558c2001cfe7558c20004fd7558c2001cfc7558c20004ff7458c20014fe7458c20014fc7458c20024ff7358c20026df7358c20006df5358c20096de5358c20006dd5358c20096dc5358c20006df4358c20096de4358c20096dc4358c2004cff7258c2004cfe7258c2004cfd7258c2004cfc7258c2004ede3258c2004edc3258c20004ff7158c20004fc7158c20096df3158c20096dc3158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c2004edf7258c2004ede7258c2004edd7258c2004edc7258c2004edf5258c2004ede5258c2004edd5258c2004edc5258c2004edf4258c2004ede4258c2004edd4258c2004edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dd5158c20006dc5158c20006df4158c20006dc4158c2004edf2158c2004ede2158c2004edd2158c2004edc2158c20026df7058c20026de7058c20026dd7058c20026dc7058c20026df5058c20026de5058c20026dd5058c20026dc5058c20026df4058c20026de4058c20026dd4058c20026dc4058c20026df2058c20026de2058c20026dd2058c20026dc2058c20026df1058c20026de1058c20026dd1058c20026dc1058c20004ff7650c20024fe7650c20004fd7650c20024fc7650c202167e6550c200067d6550c20016be6450c20006bd6450c2000ede6350c20006dd6350c200979c4350c20004ff759842001cfe7598420004fd759842001cfc7598420014fe7498420004fd7498420014fc749842000cfe7398420004fd739842000cfc7398420026f67198420006f75198420006f65198420006f55198420006f45198420006f74198420006f44198420006f73198420006f4319842004ef7219842004ef42198420026f61098420026f41098420006f77598420006f67598420006f57598420006f47598420006f77498420006f67498420006f57498420006f47498420006f75498420006f65498420006f55498420006f45498420006f77398420006f67398420006f57398420006f47398420006f75398420006f65398420006f55398420006f45398420006f74398420006f64398420006f54398420
  | 13 => 0x85200057d75885200067f658852014e7c65885202bded7288520006f76188520006f46188520025fa7088520005f97088520024fc76485200067f65485201667c6548520006f76148520006f4614852004fe42148520005fb7048520025f87048520024ec76485202bdef75485202bded75485200076f65485202b76c654852004def714852004fe77148520007e76148520006ec6148520007e46148520007eb7048520025ee7048520025ec7048520007e8704852004eef604852004feb6048520014ff76501200b4fd765012004cfc76501200067f655012011e7c6550120006bf6450120016bc6450120005ef725012004dec725012000cff764c1200acfd764c12004cfc764c1200067f654c1200fe7c654c120006df634c12000edc634c120005ef724c12004dec724c1200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067c435942004e7f725942004e7e725942004e7d725942004e7c725942004e7f425942004e7e425942004e7d425942004e7c425942004e7f325942004e7e325942004e7d325942004e7c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067c41594200067f31594200067c315942004e7f215942004e7e215942004e7d215942004e7c215942004e6c21594200267f70594200267e70594200267d70594200267c70594200267f40594200267e40594200267d40594200267c40594200267f30594200267e30594200267d30594200267c30594200267f20594200266f20594200267e20594200267d20594200266d20594200267c20594200267f10594200267e10594200267d10594200267c1059420004ff755902001cfe7559020004fd755902001cfc7559020024ff7459020026bf7459020006bf545902009ebe5459020006bd545902009ebc5459020004ff735902000cfe735902000cfc735902009ebf4359020006be435902009ebc435902004cff725902004cfe725902004cfd725902004cfc725902004ebe425902004ebc4259020004ff7159020004fc715902009ebf415902009ebc4159020024fe7059020024fc7059020026be4059020026bc4059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc535902004ebf725902004ebe725902004ebd725902004ebc725902004ebf525902004ebe525902004ebd525902004ebc525902004ebf325902004ebe325902004ebd325902004ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc5159020006b
  | 14 => 0xaedc31d8d2004cfd70d8d200aedf30d8d200057f7558d200bd7c7558d200067f6558d200067c6558d20005bf7458d200b5bc7458d200aedc6358d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20014fc7458d20006bc7458d20014bc7458d200acff7358d20006df7358d200aede5358d20006dd5358d200c4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200dcff7058d20006fb7058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d202167c6550d200af9c4350d20024fc76509200067f65509201fe7c6550920006bf6450920016bc6450920005df73509200addc7350920005fb7050920025f87050920024fc764c9200067f654c9201de7c654c920005bf744c9200b5bc744c920006df634c92000edc634c920005fb704c920025f8704c9200067f65d85200067c65d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d852000cfe73d8520004fd73d852000cfc73d8520006f741d8520006f441d8520006f731d8520006f431d85200bd7e75985200057d75985200067f65985200067c6598520006f761985200057f75585200bd7c75585200067f65585200067c6558520005bf74585200b5bc7458520005df73585200addc73585200067f65185200067c6518520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520014fe7418520004fd7418520014fc741852000cfe7318520004fd731852000cfc7318520006ee5218520006ed5218520006f74118520006f44118520006f73118520006f43118520024fe7018520024fc701852026eee201852026eec2018520004fe7690520004fd7690520004fc76905200067f65905201ce7c6590520006bf6490520016bc649052004dee7290520005ed7290520004ff7650520004fe7650520004fc76505200067f65505201be7c6550520005df73505200addc7350520004fe768c520004fd768c520004fc768c5200067f658c5201ae7c658c520006df638c52000edc638c52004dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200067f654c52019e7c654c520005bf744c5200b5bc744c520005ee76c852004eee76c8520004ee76c852004def75c852004f6e75c85202cded75c852004f6d75c85200056d75c85200076f65c85202c76c65c852004fae74c852004fad74c852004fce73c852004fcd73c8520006ec61c8520025ee70c8520025ec70c852004eef60c852004feb60c8520024fe76885200bd7e758
  | 15 => 0xc724c6200d57e75886200057d7588620006f66188620006f56188620025fa7088620005f970886202ef6e75886200076d758862025eef65886202eeed658862004dee718862025fe66188620006ed618862025fe5618862025fea708862025ded7088620007e9708862004eee6088620006f66148620006f56148620005fb7048620025f8704862026ded760862004eed760862026eef65086202e6ed650862004fe67108620006ed610862004def700862026ded700862004fea60086200bd7e76d95200be7e76d952001c7e76d95200067e64d95200067c64d95200067e63d95200067c63d95202d76f72d95200bf6c72d95202df7b20d95202d76e20d95202d76c20d95202df7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d95202d67f72d95202de7e72d95200be7d72d95202de7c72d95200067f42d95202de7e42d95202de7c42d95200067f32d95202de7e32d95202de7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067c31d95202de7f21d95202de7c21d95202de7f70d95202d67e70d95200be7d70d95202d67c70d95200067f40d95202d67e40d95202d67c40d95200067f30d95202d67e30d95202d67c30d95202de7f20d95202d67e20d95200be7d20d95202d67c20d95202d67e10d95202d67c10d9520014fe76d91200067f65d91200067c65d91200b6be64d9120004ff75d912001cfe75d9120004fd75d912001cfc75d912000cfe73d9120004fd73d912000cfc73d9120006be43d91200b6bc43d912004cfe72d9120024fd72d912004cfc72d91200b6bf42d9120004fe71d9120004fd71d91200b6bc41d912004cfd70d91200b6bf40d91200057f75591200bd7c75591200067f65591200067c65591200b6bc6459120005df73591200addc7359120005f77159120005f47159120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c75591200b4ff7459120006bf74591200b6be5459120006bd5459120004ff7359120006df7359120004df735912000cfe735912000cfc7359120006dc735912000cdc73591200ccff7259120006ef7259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f471591200e4ff7059120006fb705912000cfe76d8d200067f65d8d200067c65d8d200aede63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df43d8d200aedc43d8d2004cfe72d8d20024fd72d8d2004cfc72d8d200aedf32d8d20004fe71d8d20004fd71d8d20
  | 16 => 0x720005df73507200dddc7350720004ff768c72004cfe768c720004fd768c72000ede638c720006dd638c72004dee728c720005ed728c720004ff764c720004fd764c72004cfc764c720005bf744c7200e5bc744c72004def7648720006ef76487202f5ef75487202f5ed754872004fe7714872004fe76148720006ee614872004fe46148720025ee7048720025ec7048720014ff765032004cfc7650320016be6450320006bd6450320005ef725032004dec725032000cff764c32004cfc764c32000ede634c320006dd634c320005ef724c32004dec724c320004ff755922001cfe7559220004fd755922001cfc7559220026bf74592200cebe5459220006bd5459220004ff735922000cfe735922000cfc7359220006be43592200cebc43592200cebf4259220004ff7159220004fc71592200cebf4159220024fc7059220026be4059220026bc4059220004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20014fc7458e20026df7358e200c6de5358e20006dd5358e20006df4358e200c6dc4358e200c6df3258e20004ff7158e20004fc7158e200c6df3158e20024fc7058e20026de3058e20026dc3058e20004ff7650e20024fe7650e20004fd7650e20024fc7650e200c79c4350e20014ff7650a20024fc7650a20016be6450a20006bd6450a20005df7350a200c5dc7350a2004fac4250a20005fb7050a20025f87050a2000cff764ca20024fc764ca20005bf744ca200cdbc744ca2000ede634ca20006dd634ca2004fcc324ca20005fb704ca20025f8704ca20004ff759862001cfe7598620004fd759862001cfc7598620014fe7498620004fd7498620014fc749862000cfe7398620004fd739862000cfc7398620026f67198620006f65198620006f55198620024fe7098620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620006bf7458620004bf7458620014fe7458620014fc7458620006bc7458620014bc7458620004ff7358620006df7358620004df735862000cfe735862000cfc7358620006dc735862000cdc7358620026f77158620006f65158620006f55158620024fc7058620026ef2058620026ed2058620026f61058620026f41058620004ff7690620024fe7690620004fd769062028ebf6490620016bc6490620004ff7650620004fd7650620024fc7650620016be6450620006bd6450620005df73506200c5dc7350620005ef725062004dec7250620004ff768c620024fe768c620004fd768c62027edf638c62000edc638c620004ff764c620004fd764c620024fc764c620005bf744c6200cdbc744c62000ede634c620006dd634c620005ef724c62004de
  | 17 => 0x4ff7650530004fe7650530004fc7650530005df735053000ddc7350530024dc764c5302fddf754c5302fddd754c5300079f744c5300f5de744c5300f5dc744c5300079c744c5300f59c744c530005df724c53000ddf714c53000fd7714c530007d7614c530006dc614c530007d4614c530007db704c530025de704c530025dc704c530007d8704c53000edf604c53000fdb604c530004fe76c8530004fd76c853004cfc76c85300fd7e75c85300057d75c85300f5be74c8530005bd74c853000dde73c8530005dd73c8530006f761c8530006f461c8530004fe7688530004fd7688530004fc76885300fd7e75885300057d758853000dde7388530005dd7388530006ef628853004eec6288530004ff7648530004fe7648530004fc764853000dde7348530005dd7348530004fe7608530004fd760853004cfc760853000dde7308530005dd7308530006ef620853004eec6208530006f76108530006f46108530025fa7008530005f97008530014ff765013000cfe7650130114fd765013000cfc7650130006bf6450130016bc6450130005df735013000ddc73501301179c4350130004ff755932001cfe7559320004fd755932001cfc755932004ebf74593200e6be5459320006bd5459320004ff7359320006df7359320004df735932000cfe735932000cfc7359320006dc735932000cdc73593200e6bf4359320024fc725932004ebe425932004ebc4259320004ff7159320004fc71593200e6bc41593200e6bf4059320004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20006bf7458f20004bf7458f20014fe7458f20014fc7458f20006bc7458f20014bc7458f2004edf7358f200dede5358f20006dd5358f200dede4358f20024fc7258f2004ede3258f2004edc3258f20004ff7158f20004fc7158f200dedc3158f200dedf3058f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f20016be6450f20006bd6450f2000ede6350f20006dd6350f200df9c4350f20004ff759872001cfe75987200067e759872001c7e7598720004fd75987200067d75987200047d759872001cfc7598720014fe7498720004fd7498720014fc749872000cfe7398720004fd739872000cfc7398720024fe7298720024ee729872004eee5298720006ed529872004ef6719872004eef219872004ef7219872004ef4219872025eee209872004eec2098720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff735872000cfe735872000cfc7358720024fc725872004ef7715872004ef7215872004ef42158720004ff769072004cfe7690720004fd7690720016be6490720006bd649072004dee7290720005ed7290720004ff7650720004fd765072004cfc765
  | 18 => 0xd73d91300f6dd73d9130024dd73d913000cfc73d9130126bf43d91300f6df43d9130126bd43d9130126dc43d913004cfe72d9130004fd72d91300f6bc42d9130126df32d9130004fe71d9130004fd71d91300f6bc41d913000cfd70d91300f6bf40d91300f6bc64591301179c4359130315fb7059130004ff755913001cfe7559130004fd755913001cfc7559130124ff7459130006bf7459130114ff7359130006df73591300f6df4359130116be4359130116bc4359130116dc43591301169c4359130004ff725913004cfc72591300f6bf4259130116df3259130004ff7159130004fc7159130314ff7059130006fb7059130004ff75d893001cfe75d8930004fd75d893001cfc75d8930014fe74d8930004fd74d8930014fc74d8930024fd73d89300c6de53d8930006dd53d89300c6ee32d89300c6ed32d8930004fe71d8930004fd71d8930006ef62989300adf970989300057f75589300fd7c7558930005bf74589300f5bc7458930005f77158930005f471589300ddfb70589300fd7e75189300057d75189300f5be7418930005bd741893004eee6218930006ed6218930004fe7690930004fd769093004cfc7690930006bf6490930016bc649093000dde7390930005dd73909302079c4390930004ff7650930004fe7650930004fc7650930016be6450930006bd6450930005df735093000ddc73509300f79f4350930024dc764c93030ddf754c93030ddd754c930306df654c930306dd654c9300079f744c9300f5de744c9300f5dc744c9300079c744c9300f59c744c930006df644c930006dd644c93000ddf724c93000fcf724c930007cf624c93004ede624c93004edc624c930007cc624c93004ecc624c930007ce424c930007cd424c930005df714c930007db704c930025de704c930025dc704c930007d8704c93000edf604c93000fdb604c930004ff75d853001cfe75d8530004fd75d853001cfc75d8530014fe74d8530004fd74d8530014fc74d8530024fd73d853004cfe72d8530004fd72d853006ef631d853006ef531d8530006f76198530055f970985300057f75585300fd7c7558530005bf74585300f5bc7458530005ef7258530005ec7258530085fb70585300fd7e75185300057d7518530006f56118530004ff751853001cfe75185300067e751853001c7e7518530004fd75185300067d75185300047d751853001cfc7518530014fe7418530004fd7418530014fc7418530024fd731853002ede5318530006dd5318530006df431853002edc431853004cfe7218530004fd721853002edf3218530006dd321853002edf311853002ef6311853002ef53118530276de3018530276dc3018530004fe7690530004fd7690530004fc7690530006bf6490530016bc649053000dde7390530005dd73905301c79c4390530
  | 19 => 0x9230026bd7059230026bc7059230026bf5059230026be5059230026bd5059230026bc5059230026bf3059230026be3059230026bd3059230026bc3059230026bf2059230026be2059230026bd2059230026bc2059230026bf1059230026be1059230026bd1059230026bc1059230004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30014fc7458a30026ef7258a30006ee5258a30006ed5258a300aeee3258a300aeed3258a30004ff7158a30004fc7158a300aedc3158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a3004cff7690a30024fe7690a30004fd7690a30016be6490a30006bd6490a30004ff7650a30004fd7650a30024fc7650a30016be6450a30006bd6450a30005df7350a3000ddc7350a30004ff759863001cfe7598630004fd759863001cfc7598630014fe7498630004fd7498630014fc749863004cfe7298630004fd7298630026f67198630006f65198630006f55198630086f63198630086f53198630024fe7098630026f61098630026f41098630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630014fe7458630014fc7458630004ff725863004cfc7258630026f77158630006f65158630006f55158630056f63158630056f53158630056dc3158630024fc7058630026df3058630026dd3058630026f61058630026f41058630004ff7690630024fe7690630004fd7690630016be6490630006bd6490630004ff7650630004fd7650630024fc7650630016be6450630006bd6450630005df735063000ddc735063027edf658c63031edd658c6301a6de648c63027f9e648c6301a69e648c63027f9d648c63027edc648c630006dd628c63000dde718c63000fd6718c63027fd6618c630006dd618c63027fd5618c63027fda708c63027ddd708c630007d9708c63000ede608c63000fda608c63004cff76c8630024fe76c8630004fd76c863010d7e75c86300057d75c8630105be74c8630005bd74c8630186be64c8630006bd64c863000dde73c8630005dd73c863004eee62c8630006ed62c8630004ff7688630024fe7688630004fd768863010d7e75886300057d7588630176be6488630006bd6488630006f66188630006f56188630004ff7648630004fd7648630024fc764863015ebe6448630006bd6448630005df734863000ddc734863004eee6248630006ed6248630006f66148630006f5614863004cff7608630024fe7608630004fd760863013ebe6408630006bd6408630025fa7008630005f97008630014fe76d91300f6be64d913000dde73d9130025dd73d91300f79f43d9130004ff75d913001cfe75d9130004fd75d913001cfc75d91300f6be54d9130006bd54d9130024ff73d913000cfe73d9130024f
  | 20 => 0x4cfe72d8540004fd72d8540076f641d8540076f541d8540006f7619854005df970985400057f755854011d7c7558540005df7358540115dc7358540005ef7258540005ec725854008dfb705854011d7e75185400057d7518540006f56118540004ff751854001cfe75185400067e751854001c7e7518540004fd75185400067d75185400047d751854001cfc7518540024fd7418540036be5418540006bd541854000cfe7318540004fd731854000cfc7318540006be4318540036bc431854004cfe7218540004fd7218540036bf4218540006bd4218540036bf4118540036f64118540036f54118540286be4018540286bc4018540024bc7650540325bf7550540325bd75505400079f7350540115be7350540115bc73505400079c73505401159c7350540005bf7250540015bf7150540017b77150540007b76150540006bc6150540007b46150540007bb7050540025be7050540025bc7050540007b87050540016bf6050540017bb6050540004fe768c540004fd768c540004fc768c540015be748c540005bd748c540006df638c54000edc638c5401179c438c540004ff764c540004fe764c540004fc764c540005bf744c540015bc744c540004fe76c8540004fd76c854004cfc76c854011d7e75c85400057d75c8540015be74c8540005bd74c8540115de73c8540005dd73c8540006f761c8540006f461c8540004fe7688540004fd7688540004fc768854011d7e75885400057d7588540015be7488540005bd7488540006ef628854004eec6288540004ff7648540004fe7648540004fc7648540015be7448540005bd7448540004fe7608540004fd760854004cfc7608540015be7408540005bd7408540006ef620854004eec6208540006f76108540006f46108540025fa7008540005f97008540004ff755923001cfe7559230004fd755923001cfc7559230026bf7459230006bf5459230106be5459230006bd5459230106bc5459230116bf4359230116bd4359230004ff725923004cfc7259230106bf4259230106bc4259230004ff7159230004fc7159230106bf4159230106bc4159230024fe7059230024fc7059230026be4059230026bc4059230006bf7559230006be7559230006bd7559230006bc7559230116bf7359230116be7359230116bd7359230116bc7359230116bf5359230116be5359230116bd5359230116bc5359230006bf7259230006be7259230006bd7259230006bc7259230006bf5259230006be5259230006bd5259230006bc5259230116bf3259230116be3259230116bd3259230116bc3259230006bf7159230006be7159230006bd7159230006bc7159230006bf5159230006be5159230006bd5159230006bc5159230116bf3159230116be3159230116bd3159230116bc3159230026bf7059230026be705
  | 21 => 0xd6290640015be7190640017b6719064028fb66190640006bd619064028fb5619064028fba709064028dbd7090640007b97090640016be6090640017ba6090640004ff768c640024fe768c640004fd768c64000ede638c640006dd638c640004ff764c640004fd764c640024fc764c640005bf744c640015bc744c64000ede634c640006dd634c64004cff76c8640024fe76c8640004fd76c864012d7e75c86400057d75c8640015be74c8640005bd74c8640125de73c8640005dd73c864017ede63c8640006dd63c864004eee62c8640006ed62c8640004ff7688640024fe7688640004fd768864012d7e75886400057d758864016ede6388640006dd6388640006f66188640006f56188640004ff7648640004fd7648640024fc7648640005bf7448640015bc7448640156de6348640006dd634864004eee6248640006ed6248640006f66148640006f5614864004cff7608640024fe7608640004fd7608640136de6308640006dd6308640025fa7008640005f9700864000cfe76d8d40015be74d8d40116de63d8d401179e43d8d40004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d40024fd74d8d40024bd74d8d4000cfc74d8d40116de53d8d40006dd53d8d40116be43d8d40116de43d8d40106dd43d8d40116bc43d8d4004cfe72d8d40004fd72d8d40106bf42d8d40116dc32d8d40004fe71d8d40004fd71d8d40116dc31d8d40014fd70d8d40116df30d8d40116dc6358d401179c4358d4033dfb7058d40004ff75d894001cfe75d8940004fd75d894001cfc75d8940024fd74d89400cebe54d8940006bd54d894000cfe73d8940004fd73d894000cfc73d89400ceee42d89400ceed42d8940004fe71d8940004fd71d8940006ef62989400b5f970989400057f755894011d7c7558940005df7358940115dc7358940005f77158940005f471589400e5fb705894011d7e75189400057d7518940115de7318940005dd731894004eee6218940006ed6218940024bc7650940335bf7550940335bd755094032ebf655094032ebd65509400079f7350940115be7350940115bc73509400079c73509401159c7350940006bf6350940015bf7250940017af7250940007af625094004ebe625094004ebc6250940007ac625094004eac6250940005bf7150940007bb7050940025be7050940025bc7050940007b87050940016bf6050940017bb6050940004fe768c940004fd768c94004cfc768c940015be748c940005bd748c940006df638c94000edc638c9401179c438c940007ad428c940004ff764c940004fe764c940004fc764c940005bf744c940015bc744c94000ede634c9401179e434c940007ad424c940004ff75d854001cfe75d8540004fd75d854001cfc75d8540024fd74d854000cfe73d8540004fd73d854000cfc73d8540
  | 22 => 0x8021014fe7458021014fc7458021004ff735802100cfe735802100cfc735802104eee5258021006ed525802104eef215802104ef62158021006ed215802104ef5215802104efb7058021006fa5058021006f9505802104efb205802104eec205802104ef82058021004ff7558e4001cfe7558e40004fd7558e4001cfc7558e40026df7358e40006df5358e40126de5358e40006dd5358e40126dc5358e40126de4358e400f6dd4358e40004ff7258e4004cfc7258e40126df3258e40126dc3258e40004ff7158e40004fc7158e40126df3158e40126dc3158e40024fe7058e40024fc7058e40026de3058e40026dc3058e40006df7558e40006de7558e40006dd7558e40006dc7558e400f6de7458e400f6dd7458e40126dc7458e400f6df5458e400f6de5458e400f6dd5458e400f6dc5458e40006df7258e40006de7258e40006dd7258e40006dc7258e40006df5258e40006de5258e40006dd5258e40006dc5258e400f6df4258e400f6de4258e400f6dd4258e400f6dc4258e40006df7158e40006de7158e40006dd7158e40006dc7158e40006df5158e40006de5158e40006dd5158e40006dc5158e400f6df4158e400f6de4158e400f6dd4158e400f6dc4158e40026df7058e40026de7058e40026dc7058e40026df5058e40026de5058e40026dd5058e40026dc5058e40026df4058e40026de4058e40026dd4058e40026dc4058e40026df2058e40026de2058e40026dd2058e40026dc2058e40026df1058e40026de1058e40026dd1058e40026dc1058e40004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a4000cfe7358a4000cfc7358a40026ef7258a40006ee5258a40006ed5258a400b6ee4258a400b6ed4258a40004ff7158a40004fc7158a400b6bc4158a40024fc7058a40026bf4058a40026bd4058a40026ee2058a40026ec2058a4004cff768ca40024fe768ca40004fd768ca4000ede638ca40006dd638ca40004ff764ca40004fd764ca40024fc764ca40005bf744ca40015bc744ca4000ede634ca40006dd634ca40004ff759864001cfe7598640004fd759864001cfc759864000cfe7398640004fd739864000cfc739864004cfe7298640004fd7298640026f67198640006f65198640006f5519864008ef6419864008ef54198640024fe7098640026f61098640026f41098640004ff755864001cfe7558640004fd755864001cfc7558640004ff735864000cfe735864000cfc7358640004ff725864004cfc7258640026f77158640006f65158640006f5515864005ef6415864005ef5415864005ebc4158640024fc7058640026bf4058640026bd4058640026f61058640026f4105864028ebf6590640346bd65906401c6be639064028f9e63906401c69e639064028f9d639064028ebc6390640006b
  | 23 => 0x6df634c92100edc634c92104fcc324c921005f7714c921005f4714c921184fe7690521016be6490521006bd6490521014ff765052115cfd765052104cfc7650521006bf6450521016bc6450521005df7350521155dc7350521005ef725052104dec725052117cfe768c52100ede638c521006dd638c52100cff764c521154fd764c52104cfc764c521005bf744c52115dbc744c521006df634c52100edc634c521005ef724c52104dec724c5211657e75885210057d758852104df6718852104ef761885213776e75885210076d7588521376ef6588521376ed658852104dee718852104eef618852104fe76188521005ed7088521004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d812100cfe73d8121004fd73d812100cfc73d8121006fb60981210057f75581211657c7558121005bf745812115dbc7458121005df7358121155dc73581211657e75181210057d751812115dbe7418121005bd7418121155de7318121005dd731812125eef6218121026fa6018121006f96018121004ff755902101cfe7559021004fd755902101cfc755902104ebf745902113ebe5459021006bd5459021004ff7359021006df7359021004df735902100cfe735902100cfc7359021006dc735902100cdc735902113ebf435902104cfe725902104cfc725902104ebe425902104ebc425902113cfc715902113ebc4159021004ff7059021024fc705902113ebf4059021004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21006bf7458c21004bf7458c21014fe7458c21014fc7458c21006bc7458c21014bc7458c2104edf7358c21136de5358c21006dd5358c21136de4358c2104cfe7258c2104cfc7258c2104ede3258c2104edc3258c21134fc7158c21136dc3158c21004ff7058c21024fc7058c21136df3058c21004ff7650c2104cfe7650c21004fd7650c2104cfc7650c21016be6450c21006bd6450c2100ede6350c21006dd6350c211379c4350c21174ff769042104cfe7690421014fd769042104cfc7690421016be6490421006bd649042104dee7290421005ed7290421174ff7650421005df7350421135dc735042116cff768c42104cfe768c42100cfd768c42104cfc768c42100ede638c421006dd638c42104dee728c421005ed728c42116cff764c421005bf744c42113dbc744c42104def7648421006ef7648421004ef764842136def754842136ded754842104def714842104fe77148421366ee614842104fe6614842135fe6514842135fe55148421357e74148421357e4414842134fe7314842134fe4314842126dec7048421004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff745
  | 24 => 0xf76506211be7e65506210067d6550621005df735062116ddc735062100cfe768c62104cfd768c6211ae7e658c6210067d658c62100ede638c621006dd638c62104dee728c621005ed728c621134ff764c62119e7e654c6210067d654c621005bf744c621175bc744c621005ed76c862104eed76c862104def75c862104f6e75c8621385ed75c862104f6d75c86210056d75c862137f6e65c86210076d65c862104fae74c862104fad74c862104fce73c862104fcd73c862104fe661c862137fe651c862137fe551c862125dee70c862114d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067e65582210067d6558221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff735822100cfe735822100cfc7358221006ee5258221006ed5258221006ef215822114d7e75182210057d75182210067e65182210067d6518221175be7418221005bd741822116dde7318221005dd7318221026fa6018221006f96018221014fe76d912115ebe64d9121004ff75d912101cfe75d9121004fd75d912101cfc75d912115ebe54d9121006bd54d912100cfe73d9121004fd73d912100cfc73d9121006be43d912115ebc43d912115cfd72d912115ebf42d912104cfd71d912115ebf41d9121024fe70d9121004fd70d912115ebc40d912115ebc6459121005df7359121155dc7359121004ff755912101cfe7559121004fd755912101cfc755912115cff7459121006bf7459121004ff7359121006df7359121004df735912100cfe735912100cfc7359121006dc735912100cdc7359121174ff7259121006ef7259121184ff7159121006f7715912115ebc4159121004ff7059121024fc705912115ebf405912100cfe76d8d21156de63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21014fe74d8d21004fd74d8d21014fc74d8d21156de53d8d21006dd53d8d21006df43d8d21156dc43d8d21154fd72d8d21156df32d8d2104cfd71d8d21156df31d8d21024fe70d8d21004fd70d8d21156dc30d8d21005bf7458d2115dbc7458d21156dc6358d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21014fc7458d21006bc7458d21014bc7458d21154ff7358d21006df7358d2116cff7258d21006ef7258d2117cff7158d21006f77158d21156dc3158d21004ff7058d21024fc7058d21156df3058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d211579c4350d21014fc7650921006bf6450921016bc6450921005df7350921155dc735092104fac4250921005f77150921005f4715092100cfc764c921005bf744c92115dbc744c921
  | 25 => 0x96210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067c435962114e7f725962138e7e72596210067d725962138e7c72596210067f425962138e7e425962138e7c42596210067f325962138e7e325962138e7c325962114e7f715962138e7e715962114e7d715962114e7c71596210067f41596210067c41596210067f31596210067c315962138e7f215962114e7e215962138e7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067c305962138e7f205962138e7c205962114d7e75d92210057d75d92210067e65d92210067d65d9221176be64d922116dde73d9221005dd73d9221004ff75d922101cfe75d92210067e75d922101c7e75d9221004fd75d92210067d75d92210047d75d922101cfc75d9221174fd74d9221176be54d9221006bd54d922100cfe73d9221006de73d922100cde73d9221004fd73d9221006dd73d9221004dd73d922100cfc73d9221006ed72d9221006f671d9221024fe70d9221004fd70d9221014ff76592210067e65592210067d6559221176bc6459221004ff755922101cfe7559221004fd755922101cfc7559221006bf7459221004ff735922100cfe735922100cfc7359221006be4359221176bc4359221176bf425922104cfc7159221176bc4159221004ff7059221024fc7059221176bf405922114d7e75d8e210057d75d8e210067e65d8e210067d65d8e21175be74d8e21005bd74d8e2116ede63d8e21004ff75d8e2101cfe75d8e210067e75d8e2101c7e75d8e21004fd75d8e210067d75d8e210047d75d8e2101cfc75d8e21014fe74d8e21006be74d8e21014be74d8e21004fd74d8e21006bd74d8e21004bd74d8e21014fc74d8e2116cfd73d8e2116ede53d8e21006dd53d8e21006ed72d8e21006f671d8e21024fe70d8e21004fd70d8e2100cff7658e210067e6558e210067d6558e2116edc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21014fc7458e21006df7358e21006df4358e2116edc4358e2116edf3258e2104cfc7158e2116edc3158e21004ff7058e21024fc7058e2116edf3058e21004ff7650e21004fe7650e21004fd7650e21004fc7650e212167e6550e210067d6550e2116f9c4350e21014ff7650a211fe7e6550a210067d6550a21016be6450a21006bd6450a21005df7350a2116ddc7350a21005f77150a21005f47150a2100cff764ca211de7e654ca210067d654ca21005bf744ca21175bc744ca2100ede634ca21006dd634ca21005f7714ca21005f4714ca21014fe769062104cfd76906211ce7e65906210067d6590621016be6490621006bd649062104dee7290621005ed729062113cf
  | 26 => 0x6bc315932104ebf215932104ebe215932104ebd215932104ebc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006be5059321006bd5059321006bc5059321006bf3059321006bc305932104ebf205932104ebe205932104ebd205932104ebc2059321004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21014fe7458f21014fc7458f2104edf7358f21006df5358f2117ede5358f21006dd5358f2117edc5358f21006df4358f2117ede4358f2117edc4358f2104cfc7258f2104ede3258f2104edc3258f2117edf3158f21004ff7058f21024fc7058f2117edf3058f2117edc3058f21006df7558f21006de7558f21006dd7558f21006dc7558f21006df7458f21006de7458f21006dd7458f21006dc7458f21006df5458f21006de5458f21006dd5458f21006dc5458f2104edf7258f2104ede7258f2104edd7258f2104edc7258f2104edf5258f2104ede5258f2104edd5258f2104edc5258f2104edf4258f2104ede4258f2104edd4258f2104edc4258f21006df7158f21006dd7158f2117edc7158f21006df5158f21006de5158f21006dd5158f21006dc5158f21006df4158f21006dc4158f2104edf2158f2104ede2158f2104edd2158f2104edc2158f21006df7058f21006de7058f21006dd7058f21006dc7058f21006df5058f21006de5058f21006dd5058f21006dc5058f21006df4058f21006dc4058f2104edf2058f2104ede2058f2104edd2058f2104edc2058f21004ff7650f2104cfe7650f21004fd7650f2104cfc7650f212167e6550f210067d6550f21016be6450f21006bd6450f2100ede6350f21006dd6350f2117f9c4350f2115cfd76907211ce7e65907210067d6590721016be6490721006bd64907211c6de6390721006dd6390721014ff765072104cfc76507211be7e65507210067d6550721016be6450721006bd6450721005df735072117ddc73507211b6de6350721006dd6350721005ef725072104dec7250721154fd768c7211ae7e658c7210067d658c7211a6be648c721006bd648c72100ede638c721006dd638c72100cff764c72104cfc764c72119e7e654c7210067d654c721005bf744c721185bc744c721196be644c721006bd644c72100ede634c721006dd634c721005ef724c72104dec724c721004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321014fc7458321004ff735832100cfe735832100cfc735832104ef6215832104ef5215832104efb705832104efb205832104ef8205832114d7f765962114e7f765962101c7f76596210067e64596210067c64596210067e63596210067c635962114f6e72596210076d725962138f77215962138f7421596210067f74596210067e74596210067d745
  | 27 => 0xd6218931004fe7690931004fd769093104cfc7690931006bf6490931016bc6490931004ff7650931004fe7650931004fc7650931006bf6450931016bc6450931005df735093100ddc735093139cfe76905311c6bf6490531016bc6490531014ff765053100cfe76505311b4fd765053100cfc7650531006bf6450531016bc6450531005df735053100ddc7350531396df658c531396dd658c5310079f648c5311a6de648c5311a6dc648c5310079c648c5311a69c648c531006df628c53100dde718c53100fd6718c53100edf618c53100fd7618c531005dd708c531006bf64d8131006bc64d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131014fe74d8131004fd74d8131014fc74d813104cfe72d8131004fd72d8131086fa30d8131195be7498131005bd7498131006bf6498131006bc6498131006fb60981310057f755813119d7c7558131005bf7458131195bc7458131006bf6458131006bc6458131005ef7258131005ec7258131006bf6418131006bc641813127edf6318131026fa6018131006f960181310067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067c435972104e7f725972104e7e725972104e7d725972104e7c725972104e7f425972104e7e425972104e7d425972104e7c425972104e7f325972104e7e325972104e7d325972104e7c325972118e7f715972118e7e71597210067d715972118e7c71597210067f41597210067c41597210067f31597210067c315972104e7f215972104e7e215972104e7d215972104e7c215972104e6c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067c40597210067f30597210067c305972104e7f205972104e6f205972104e7e205972104e7d205972104e7c2059721004ff755932101cfe7559321004fd755932101cfc755932104ebf7459321006bf5459321186be5459321006bd5459321186bc5459321004ff735932100cfe735932100cfc7359321186bf4359321006be4359321186bc435932104cfc725932104ebe425932104ebc4259321186bf4159321004ff7059321024fc7059321186bf4059321186bc4059321006bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf5359321006be5359321006bd5359321006bc535932104ebf725932104ebe725932104ebd725932104ebc725932104ebf525932104ebe525932104ebd525932104ebc525932104ebf325932104ebe325932104ebd325932104ebc3259321006bf7159321006bd7159321186bc7159321006bf5159321006be5159321006bd5159321006bc5159321006bf3159321
  | 28 => 0x823101cfc75582310067c755823101c7c7558231004ff7458231014fe7458231014fc7458231056de5358231006dd5358231006df4358231056dc4358231004ff725823104cfc7258231056df3258231006dd3258231056df3158231056fa305823127edc30582311ad7e75182310057d75182311a5be7418231005bd7418231005ee7218231005ed7218231026fa6018231006f96018231014fe76d9131196be64d9131004ff75d913101cfe75d9131004fd75d913101cfc75d9131006bf54d9131196be54d9131006bd54d9131196bc54d91311c4ff73d91311c4fd73d91311c6bf43d91311c6bd43d913104cfe72d9131004fd72d9131196bf42d9131196bc42d913100cfd71d9131196bf41d9131024fe70d9131004fd70d9131196bf40d9131196bc40d913139dbe76d9131014be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91311c7b731d91311c79c31d91311c7b431d91311c79f30d9131006bf75d9131006be75d9131006bd75d9131006bc75d91311c6bf73d91311c6be73d91311c6bd73d91311c6bc73d91311c6bf53d91311c6be53d91311c6bd53d91311c6bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d91311c6bf32d91311c6be32d91311c6bd32d91311c6bc32d91311c6bf71d9131196be71d91311c6bd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d91311c6bf31d91311c6be31d91311c6bc31d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d91311c6bf30d91311c6be30d91311c6bd30d91311c6bc30d9131196bc64591313a5f77159131004ff755913101cfe7559131004fd755913101cfc75591311c4ff7459131006bf74591311b4ff7359131006df73591311a4df7359131004ff725913104cfc72591313a4ff7159131006f77159131004ff7059131024fc70591311c5be7619131196be76191311c4be76191311973e75191311973d7519131006bf6519131006be6519131006bd6519131006bc651913139ebf631913139ebf611913139fb7311913139f9c311913139fb4311913139f9f3019131006bf64d8931006bc64d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931014fe74d8931004fd74d8931014fc74d8931006ee52d8931006ed52d893116eee32d893116eed32d893116edc31d8931024fe70d8931004fd70d893116edf30d893119d7e75989310057d7598931195be7498931005bd7498931006bf6498931006bc6498931006ef6298931155f57198931005bf7458931195bc7458931006bf6458931006bc645893117df77158931006bf6418931006bc641893104eee6218931006e
  | 29 => 0x6bf6290541015be7190541017b67190541016bf6190541017b76190541005bd7090541006df63d8141006dc63d8141004ff75d814101cfe75d8141004fd75d814101cfc75d814100cfe73d8141004fd73d814100cfc73d814104cfe72d8141004fd72d814108efa40d81411b5de7398141005dd7398141006df6398141006dc6398141006fb60981410057f75581411bd7c7558141005df73581411b5dc7358141006df6358141006dc6358141005ef7258141005ec725814128ebf6418141006df6318141006dc6318141026fa6018141006f960181411a6be64d92311c79c43d923139df671d9231004ff75d923101cfe75d9231004fd75d923101cfc75d92311b4fd74d9231006dd73d92311a6df43d92311c6be43d92311c6bc43d92311c6dc43d92311c69c43d923104cfe72d9231004fd72d92311a6bf42d92311c6df32d923139cfe71d9231006f671d9231024fe70d9231004fd70d9231014ff76592311a6bc645923100ddc73592311a79f4359231004ff755923101cfe7559231004fd755923101cfc7559231006bf74592311a6be5459231006bd54592311a6df73592311b6bf43592311a6df43592311b6bd43592311b6dc4359231004ff725923104cfc72592311a6bc42592311b6df325923100cfc71592311a6bc4159231004ff7059231024fc70592311a6bf40592311ad7e75d8a310057d75d8a311a5be74d8a31005bd74d8a31135f671d8a311ad7e7598a310057d7598a311a5be7498a31005bd7498a31006ef6298a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31014fc7458a31156de5358a31006dd5358a31156ee3258a31156ed3258a31004ff7058a31024fc7058a3104eee6218a31006ed6218a3116df67118a3104cff7690a31004fe7690a31004fd7690a31016be6490a31006bd6490a3100dde7390a31005dd7390a312079c4390a31004ff7650a31004fd7650a31004fc7650a31006bf6450a31016bc6450a31005df7350a3100ddc7350a311a79f4350a3104cdf764ca313b5df754ca313b5dd754ca313aedf654ca313aedd654ca310079f744ca311a5de744ca311a5dc744ca310079c744ca311a59c744ca31006df644ca31006dd644ca3100ddf724ca3100fcf724ca3104ede624ca31007ce624ca3104ece624ca31007cd624ca3104edc624ca31007ce424ca31007cd424ca31005df714ca31007d7714ca31007d4714ca3100ede614ca3100fd6614ca3127ddc704ca3100cff7690631014fe769063100cfd7690631016be6490631006bd649063100dde7390631005dd73906311c79c43906313a4ff76506311a5df735063100ddc7350631006fb60982310057f75582311ad7c7558231004ff75582310067f75582310047f755823101cfe7558231004fd755
  | 30 => 0xc75582410067c755824101c7c755824105ebe5458241006bd5458241004ff735824100cfe735824100cfc7358241006be435824105ebc4358241004ff725824104cfc725824105ebf4258241006bd425824105ebf415824105efa405824128ebc40582411cd7e75182410057d75182411c5de7318241005dd7318241005ee7218241005ed7218241026fa6018241006f9601824100cfe76d8d411b6de63d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41006df53d8d411b6de53d8d41006dd53d8d411b6dc53d8d411b6de43d8d411a6dd43d8d4104cfe72d8d41004fd72d8d411b6df32d8d411b6dc32d8d41014fd71d8d411b6df31d8d41024fe70d8d41004fd70d8d411b6df30d8d411b6dc30d8d411b5de76d8d4100cde76d8d41006df65d8d41006de65d8d41006dd65d8d41006dc65d8d411a7d741d8d411a79c41d8d411a7d441d8d411a79f40d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d411a6df74d8d411b6de74d8d411a6dc74d8d411a6df54d8d411a6de54d8d411a6dd54d8d411a6dc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d41006de52d8d41006dd52d8d41006dc52d8d411a6df42d8d411a6de42d8d411a6dd42d8d411a6dc42d8d411a6df71d8d411b6de71d8d411a6dd71d8d41006df51d8d41006de51d8d41006dd51d8d41006dc51d8d411a6df41d8d411a6de41d8d411a6dc41d8d41006df70d8d41006de70d8d41006dd70d8d41006dc70d8d41006df50d8d41006de50d8d41006dd50d8d41006dc50d8d411a6df40d8d411a6de40d8d411a6dd40d8d411a6dc40d8d411b6dc6358d413cdf77158d411a5de7618d411b6de7618d411b75e7518d411b75d7518d41006df6518d41006de6518d41006dd6518d41006dc6518d411c6df6418d413a6df6118d413c7d74118d413c79c4118d413c7d44118d413c79f4018d41006df63d8941006dc63d8941004ff75d894101cfe75d8941004fd75d894101cfc75d894100cfe73d8941004fd73d894100cfc73d8941006ee52d8941006ed52d8941176ee42d8941176ed42d8941176bc41d8941024fe70d8941004fd70d8941176bf40d89411bd7e75989410057d75989411b5de7398941005dd7398941006df6398941006dc6398941006ef629894115df57198941005df73589411b5dc7358941006df6358941006dc6358941185f77158941006df6318941006dc631894104eee6218941006ed6218941004fe768c941004fd768c94104cfc768c941006df638c94100edc638c941004ff764c941004fe764c941004fc764c941005bf744c941015bc744c941006df634c94100edc634c9413bebf65905413bebd65905410079f63905411c6be63905411c6bc63905410079c63905411c69c6390541
  | 31 => 0x853204cfd73d8532006f651d8532006f551d853217ef631d853217edc31d8532024fe70d8532004fd70d853217edf30d85321dd7e75985320057d75985321d5be7498532005bd7498532006bf6498532006bc6498532006f76198532005bf74585321d5bc7458532006bf6458532006bc6458532006bf6418532006bc6418532006f56118532004ff751853201cfe7518532004fd751853201cfc7518532014fe7418532004fd7418532014fc741853204cfd7318532136de5318532006dd5318532006f65118532006f55118532136f53118532024fe7018532004fd7018532006bf64d8132006bc64d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132014fe74d8132004fd74d8132014fc74d813204cfd73d81320dede53d8132006dd53d8132004fe71d8132004fd71d81320defa30d81321d5be7498132005bd7498132006bf6498132006bc6498132006fb60981320057f75581321dd7c7558132005bf74581321d5bc7458132006bf6458132006bc6458132005f77158132005f47158132006bf6418132006bc6418132026fa6018132006f960181321c6de63d8e411c79c43d8e413c5f671d8e4100cff7658e41015bc7458e411c6dc6358e411c79e4358e41004ff7558e4101cfe7558e41004fd7558e4101cfc7558e411c6de5358e41006dd5358e411c6be4358e411c6de4358e41196dd4358e411c6bc4358e41004ff7258e4104cfc7258e41196bf4258e411c6dc3258e41014fc7158e411c6dc3158e41004ff7058e41024fc7058e411c6df3058e411cd7e75d8a410057d75d8a411c5de73d8a41005dd73d8a4113df671d8a411cd7e7598a410057d7598a411c5de7398a41005dd7398a41006ef6298a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a4115ebe5458a41006bd5458a41004ff7358a4100cfe7358a4100cfc7358a4115eee4258a4115eed4258a41004ff7058a41024fc7058a4104eee6218a41006ed6218a41175f67118a4104cbf7650a413ddbf7550a413ddbd7550a413d6bf6550a413d6bd6550a410079f7350a411c5be7350a411c5bc7350a410079c7350a411c59c7350a41006bd6350a41015bf7250a41017af7250a4104ebe6250a41007ae6250a4104eae6250a41007ad6250a4104ebc6250a41005bf7150a41007b77150a41007b47150a41016be6150a41017b66150a4128dbc7050a4104cff768ca41004fe768ca41004fd768ca41015be748ca41005bd748ca4100ede638ca41006dd638ca411c79c438ca41007ad428ca41004ff764ca41004fd764ca41004fc764ca41005bf744ca41015bc744ca4100edc634ca411c79e434ca41007ad424ca41006fb60982410057f75582411cd7c7558241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cf
  | 32 => 0x206bf72d9132416be72d9132206bd72d9132416bc72d9132006bf52d9132416be52d9132006bd52d9132416bc52d9132206bf32d9132416be32d9132416bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d9132206bf31d9132206be31d9132206bd31d9132206bc31d9132416bf21d9132416bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d9132206bf30d9132206be30d9132206bd30d9132206bc30d9132416bf20d9132416bc20d91321d6bc645913240def7259132004ff755913201cfe7559132004fd755913201cfc7559132204ff7459132006bf74591321f4ff7359132006df73591321e4df735913240cff7259132006ef7259132004ff7159132004fc7159132004ff7059132024fc7059132205be76191321d6be7619132204be76191321d73e75191321d73d7519132006bf6519132006be6519132006bd6519132006bc65191323f79e73191321d79d7319132406bf63191324069f63191323f79e53191320079d53191323f7ad72191323f6bf62191323f7af32191324079e32191324079c32191323f7ac32191323f79c31191323f79f301913204ddc7650d32016dc7650d3204cdc7650d323fddf7550d323fddd7550d3200ddf7450d3200f9f7450d320079f6450d32016de6450d32016dc6450d321d79c6450d320169c6450d32007cf7250d3204dde7250d3204ddc7250d32007cc7250d3200edf6250d3200fcf6250d321d79f4250d32005dc7150d32005df7050d323f5ee769093204eee76909321f5ed7490932207af6490932016ee6490932016ec64909321d7ac6490932016ac649093204fcf739093200dee739093204dec739093204fcc739093204eef639093204fcf6390932207ce53909323efcd5390932207ae4390932207ce43909322078e43909321d7cd4390932207ac4390932207cc3190932207cf3090932014ff765093200cfe76509321f4fd765093200cfc7650932006bf6450932016bc6450932005df735093200ddc73509320079d435093204fac425093204fcc325093200dec7650932016ec765093200cec765093204def745093204faf7450932007af6450932016ee6450932016ec64509321d7ac64509321d7ae54509323e7ad5450932007cf735093200dee735093200dec73509321f7cc735093204eef635093204fcf63509321f7ce53509323e7cd53509321f7af43509321f7ce43509321f7ad43509321d7cd43509320078d43509321d7ac41509321f7cc31509321d7af40509321f7cf3050932006bf64d8532006bc64d8532004ff75d853201cfe75d8532004fd75d853201cfc75d8532014fe74d8532004fd74d8532014fc74d
  | 33 => 0xf6398142006dc6398142006fb60981420057f75581421fd7c7558142005df73581421f5dc7358142006df6358142006dc6358142005f77158142005f47158142006df6318142006dc6318142026fa6018142006f96018142004ff755923201cfe7559232004fd755923201cfc755923204ebf74592321e6be5459232006bd54592321e6df73592321f6bf43592321e6df43592321f6bd43592321f6dc435923204cfe725923204cfc725923204ebe425923204ebc425923204edf325923204edd3259232004ff7159232004fc71592321e6bc4159232004ff7059232024fc70592321e6bf405923204def7650a32426ef7650a3204faf7450a3204faf6450a32016ee6450a3204eec6450a3204fac6450a321e7ae5450a3241fad5450a321e7cf7350a3200dee7350a3200dec7350a321f7cc7350a3200dcc7350a321f7af4350a321e7cf4350a321e78f4350a321f7ad4350a321f7cc4350a321e7ac4150a321e7af4050a32004ff759863201cfe75986320067e759863201c7e7598632004fd75986320067d75986320047d759863201cfc7598632014fe7498632004fd7498632014fc7498632006df439863216edc439863204cfe729863204edf329863204edd329863204ef6719863216ef5319863204ef7219863204ef42198632024fe7098632004fd7098632004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632014fe7458632014fc745863204cfc725863204ef77158632156f6315863204ef7215863204ef42158632004ff7058632024fc7058632004ff75582320067f75582320047f755823201cfe7558232004fd755823201cfc75582320067c755823201c7c7558232004ff7458232014fe7458232014fc7458232006df43582320aedc435823204cfc725823204edf325823204edd3258232004ff7158232004fc715823204efb70582320aefa305823204efb205823204ef82058232014fe76d91321d6be64d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132006bf54d91321d6be54d9132006bd54d91321d6bc54d913204cff73d913204cfd73d9132206bf43d9132206bd43d913200cfd72d91321d6bf42d9132004fe71d9132004fd71d91321d6bf41d91321d6bc41d9132024fe70d9132004fd70d91321d6bf40d91321d6bc40d91323f5be76d9132014be76d9132006bf65d9132006be65d9132006bd65d9132006bc65d91324179f73d91322079c73d91322079e53d91320079d53d9132207af72d9132207af32d91324179e32d91324179c32d9132207ac32d91322079c31d91322079f30d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132416bf73d9132206be73d9132206bd73d9132206bc73d9132206bf53d9132206be53d9132206bd53d9132206bc53d9132
  | 34 => 0x8d42006dc65d8d4243f9f74d8d421e79c74d8d421e79e54d8d420079d54d8d421e7cf72d8d421e7cf42d8d4243f9e42d8d4243f9c42d8d421e7cc42d8d421e79c41d8d421e79f40d8d42006df75d8d42006de75d8d42006dd75d8d42006dc75d8d4243edf74d8d421f6de74d8d421e6dc74d8d421e6df54d8d421e6de54d8d421e6dd54d8d421e6dc54d8d421e6df72d8d4243ede72d8d421e6dd72d8d4243edc72d8d42006df52d8d4243ede52d8d42006dd52d8d4243edc52d8d421e6df42d8d4243ede42d8d4243edc42d8d42006df71d8d42006de71d8d42006dd71d8d42006dc71d8d42006df51d8d42006de51d8d42006dd51d8d42006dc51d8d421e6df41d8d421e6de41d8d421e6dd41d8d421e6dc41d8d4243edf21d8d4243edc21d8d42006df70d8d42006de70d8d42006dd70d8d42006dc70d8d42006df50d8d42006de50d8d42006dd50d8d42006dc50d8d421e6df40d8d421e6de40d8d421e6dd40d8d421e6dc40d8d4243edf20d8d4243edc20d8d421f6dc6358d42435ef7258d421e5de7618d421f6de7618d421f75e7518d421f75d7518d42006df6518d42006de6518d42006dd6518d42006dc6518d421f79e7418d421f79d7418d42406df6418d424069f6418d424279e5418d420079d5418d421f7cd7218d4240edf6218d42427cf4218d424079e4218d424079c4218d42427cc4218d424279c4118d424279f4018d4204dbc7650d4200ebc7650d4204cbc7650d4242dbf7550d4242dbd7550d42015bf7350d420179f7350d420079f6350d4200ebe6350d4200ebc6350d421f79c6350d4200e9c6350d42007af7250d4204dbe7250d4204dbc7250d42007ac7250d42016bf6250d42017af6250d421f79f3250d42005bc7150d42005bf7050d42006df63d8542006dc63d8542004ff75d854201cfe75d8542004fd75d854201cfc75d854204cfd74d854200cfe73d8542004fd73d854200cfc73d8542006f651d8542006f551d8542186f641d8542186bc41d8542024fe70d8542004fd70d8542186bf40d85421fd7e75985420057d75985421f5de7398542005dd7398542006df6398542006dc6398542006f76198542005df73585421f5dc7358542006df6358542006dc6358542006df6318542006dc6318542006f56118542004ff751854201cfe7518542004fd751854201cfc751854204cfd741854213ebe5418542006bd541854200cfe7318542004fd731854200cfc7318542006f65118542006f5511854213ef54118542024fe7018542004fd7018542006df63d8142006dc63d8142004ff75d814201cfe75d8142004fd75d814201cfc75d814204cfd74d81420e6be54d8142006bd54d814200cfe73d8142004fd73d814200cfc73d8142004fe71d8142004fd71d81420e6fa40d81421f5de7398142005dd7398142006d
  | 35 => 0x6f761985431b79c43585432157e75185430057d751854339f9c4318543006f56118543004ff751854301cfe75185430067e751854301c7e7518543004fd75185430067d75185430047d751854301cfc751854300cfd7418543014fd73185433c6df431854339ebe431854339ebc431854339edc431854339e9c431854304cfe7218543004fd72185433c6bf421854339edf32185433c6f5411854339ef53118543024fe7018543004fd7018543024fe76d81432157e75d81430057d75d81433179c43d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d814300cfd74d8143014fd73d814333edf43d8143316be43d8143316bc43d8143316dc43d81433169c43d814304cfe72d8143004fd72d814333ebf42d8143316df32d8143004fe71d8143004fd71d814333efa40d8143316fa30d81431279c4398143006fb60981431179c43581434479c4318143026fa6018143006f96018143004ff7558e4201cfe7558e42004fd7558e4201cfc7558e4204edf7358e42206de5358e42006dd5358e42206be4358e42206de4358e421d6dd4358e42206bc4358e4204cfe7258e4204cfc7258e4204ebf4258e4204ebd4258e4204ede3258e4204edc3258e42004ff7158e42004fc7158e42206dc3158e42004ff7058e42024fc7058e42206df3058e42004ff759864201cfe75986420067e759864201c7e7598642004fd75986420067d75986420047d759864201cfc759864200cfe7398642004fd739864200cfc7398642006be4398642176bc439864204cfe729864204ebf429864204ebd429864204ef67198642176f5419864204ef7219864204ef42198642024fe7098642004fd7098642004ff755864201cfe7558642004fd755864201cfc7558642004ff735864200cfe735864200cfc735864204cfc725864204ef7715864215ef6415864204ef7215864204ef42158642004ff7058642024fc7058642004ff75582420067f75582420047f755824201cfe7558242004fd755824201cfc75582420067c755824201c7c7558242004ff735824200cfe735824200cfc7358242006be43582420b6bc435824204cfc725824204ebf425824204ebd4258242004ff7158242004fc715824204efb70582420b6fa405824204efb205824204ef8205824200cfe76d8d421f6de63d8d42004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d4204cfd74d8d42006df53d8d421f6de53d8d42006dd53d8d421f6dc53d8d421f6de43d8d421e6dd43d8d42014fd72d8d421f6df32d8d42004fe71d8d42004fd71d8d421f6df31d8d421f6dc31d8d42024fe70d8d42004fd70d8d421f6df30d8d421f6dc30d8d421f5de76d8d4200cde76d8d42006df65d8d42006de65d8d42006dd65d
  | 36 => 0x8002000001800800a00000080000000000010024002007001000c00000e009000801c002001800401600602180040000020020000000045000002c012006001801802600500080ec000000000000c00000400080b80000000038074068000019004000c0010008000006001006800c00400000d803c004002002801000001c00500040620000018000014005003801402600100500bc0080000048000000004007002801c000006004000200300580000000560090080000035000801c004003000000804600000380e8012010000000000200d000001c02a00f014806000601e01d803800c0000000004010007008800000800001a0010020000020000000000100100000040440000008010006005805c00400101200200020060000000004006004801c016000005000005200100780300000010040000000001006000000200000000080b600101100a400800100f000000a05e0018040000030000803000000c000000401400200080840040010008000000006001000400a00500a800000000f00b8000000029005800000400300000a400a00a000000c00200300c80080000010000034002000002800c03600000200080360010010008000001022800c006003007007800c00000000080020000000018000036005001000000b000002802a005008000004c00a00700c00240010000004010006003803401200300e80300140120000014056002003800001001200200380ea03f00600340000000098004036007000001800c0010070024000005001001000600500000080000000000020014012000804000e002001800002000600f000c02001a0000000000000015003c0060020000008000002000000400200500c80b8008015005005000a005000802c010001002002400a003003009803601e002801400000c000002801a0030088008044000000002c00a00900a000002600e0000004000009000000401600e0028000004012000001004800e02d8000000000002800800e007007800c01a007004000400e00200000e001e001000001400000000000340820010008000000003004000c00e00d000000400401004cfe76d894340f9c43d8943004ff75d894301cfe75d8943004fd75d894301cfc75d894300cfd74d8943014fd73d8943436ee42d894340eee32d8943004fe71d8943004fd71d8943024fe70d8943004fd70d8943416bf649894343edf63989432079c4398943006ef62989431f79c43589432157e75189430057d7518943416bf641894343edf63189433f79c431894304eee6218943006ed62189433a79c43d8543004ff75d854301cfe75d8543004fd75d854301cfc75d854300cfd74d8543014fd73d854304cfe72d8543004fd72d85433cef641d85433a6f631d8543024fe70d8543004fd70d85431c79c4398543
  | 37 => 0x11004005400c028004000400a02e001800002000000400140020090048004004010001800400001900080600000070008004008005003802c01201c01b00140260000090000008000000000000a001000801c002000000001000e0080020058010000000801c0180000010000000004000801002a01e000008802800000200300140020168014012000001804800400400080080700090018020000003001007c00e009008002801201800680080180500048018076000000000000400000d002801006c0020030006003000009c00a01000b000c008000000002c002001006800007601a000000c004000000001c010004000802c0040070018000002024000801801e0030050000010002000000802a000001800800400300200d407000e0058018020006000807400000d008000001e00d00680540000210050020002001000005002c00000000080000000090018018003011001002a015000005000c012002801000000a006800000a00300e002800c009000800000000701e000400a00e0018004016001001001c00201e003800000000f0008014008005000802807800100c000800a002001000c00000000000000040030000024008000016001c004010006000000c00e00a0000092008000800003e01f001805003602a0198000000001002800000a00000380a801e0070010000002003000800c00200f000801001400500100080000090020014000000008000000000f000010400000400000f8036002004808c0000110000000006003000802c014001007001001c000003000000e00001300180100010010004000001001802400e00001080200180020010000028009005800400000c00b800002c001001800000800d0070008024001000800401200c003802c00000101280080080030010030004000000002800a0020000040010006006801801400a00a8038004002000000800a0010000014000000000002001200a005000000200300380580540140038014046016002801400000400380140080020018004006006003009001c00d001800c00200a0018030014008003000c06c0000048008006012002000006600a000000000001d00280500040070068064046000000000800200a001804000000a0018008004014000000c09e0090088010006003012801800a00000000000000040018000014022004800400000000380100000000030040006003005800c0040060010014006003002800000604b01000040080010000000032003000800801400e000002400a007001000000400d00e0038018000000000000400a00a001400c000002001c052006001801800000000080000020330250010008001005800402c03600a805400c013000002400400d00000080020000298018002013000000001c012001800800400c00000
  | 38 => 0xc00001500a80000040150000000000029003000001600a002000000e0170050004018024000800000000000a000c0000020060028000000002002c00800900a0018002005002001c0040010008000004028000000801c0020010004004001000801000800b0020008006004005801c01c00000a006003c00a003000c002000003801800400100a000c00c00f000800402a000000802c002001021000000600f00980140320030018024008013000800c000000000000000800c00000b000000001200100140010220030006002000803c01a000003800400e017002000000a000001800000601d0008058026004000802800a000019801400000001200ac01c001002003c00400c0000004014002001009000000000480080180000090004002003001802400a005004800001c005003800003400f003804400e004003000c00a00300b812400802501800000000030088018024002002802c00001100180080020140000010004015021000000000200000a000200700000440000000020030000033002001c048011000000000404500a000402200000b80000000280038000004005002004800a0010028020000006000004800e00c002800800a003000800000000a00580040360000000000006010008000800201c0020030024003001803c00e00300100380060030008060020001000000000200301480300000000010038018000000000405c0010020020000031001001000601100280040060020010004002001001800000400a008000800e009000003004401400100000080010048008002002001000c010000005005800c00601a000400001f00201000040020008018032002001004003200e003000001600101d00040100050148000016001007001404800a00d0000006014000807000a00600f80f4002011002001003a00100000000060020008010000001000002405a0110090000008000005000001e00b007000c00800100380040080040030050004004001000403000100180080180020340064016000000800001401c00000000120110000010004000003000c04600700c00240000080008030018001001003400c014001800000600000480b80380120000028002004005800000c0080000000010002002000000e0320168000008007001000000802500d8034000000009801802202900e0008012003001800800200b003000407a00a003804802e00000200040080080080000000009014809000a01f000005401a004000000000a0090030000002001000000000e003000001c004003000000c036002001805c01803b00d002800e03b0060034004000005800c00200b0008028002000029802000e0000060000028001000005800a00a001800800000100c803c0180000010058054003004003000000000000040220
  | 39 => 0xfe32b17ee5b84c6f5fcd29f43f5677050051243a88352efcfb237b46530afd159071c3105440a7a3fad39707192b020b43651c0486c39f13414784d163c68ae1549967d22a42df0214b3a58a92542d317f50de517d259905b1fa08b62f30d9f33040001f052f50000c5140ec98f1720694143434413492ff50c4be648a8a4f426049830480004214a6200004c30a200005f812aa4ae43f80cf80002b8c0003c5437513993745cb40000c20f991bb0a030000f2b4f4cb3f53c94744f3455855091e96088eb430287a8472c9aa2e00dfb2ea041f0d980b500c84ab5f1cb7e35850e03eec22742680c9032c4975a64ffb0679419133813440d512c50e51ec01183fa4318c2b580c4aa49d11da0680c931021413090106c43507b112d98175e7967a3f7cf7a5178a1d5f483f442813b8200d26410048e850b40404fa472542dd1e71ab8a2b4c854583af0d140af49cd33e09322fec9d3533c3c50f505cf47f83af07e4ad42bb82b3526c271303c000356461118105fc4a14b824e090c30f3900d27ac5754b592ae4a184d801800c429c55c91b006871ac485403401553f68e14394153c1d9c3b106952c61d6127b23b432b37e8d472ac913d37d006245e85c716c4db72858672518ca1c1b140001011384000095000016a15c88f14554d6685334ee042f1155000025a02196f90000606257d66a0000b5e38713623da800e0008000002001002000000601c0020000008006004803002c009005800800200000200e4014000000004400601d008803802c004002000000201901a001400c030000800001e008000001800a004000800400c00900000c00360000090008000024002801000006b0128030016009004801401c003008000c004015000800c00203800000340120000008004002007000800402200000000000140020068000000005001000c000003005000000c00000a802c00800400180000060030000000002001017000c02001400000040080000020000000000006003800000c000806c0b0000009002000e01e0000008006001004001810601b00080340080000010000002006002800000006d001000803a004000003c0000000018090012006000800c016011003000000000a000808400a002000000000000701e00080000010050010004000007000800200a000800403600c0020004000009001006c00e00600d8004004001000006000400300000f800000200280640100010000020004020011003800802201f00c0002007003810003a005000006c008003001805c014000005801c0000000008020038002005000400401c000006c014000009003c006003000016c00200b00880000060070000078000000013800001400301d800400000603b80000020060028000004002015802001e001003801001800d00700380080040010
  | 40 => 0x5468c0800011010000c835c543fc39b0fa6538c000015c00055110694a2066b4b411f1341c793106caf6138092d2294d6c13943a80528c6508f00eb0edcdec2df09523b8c68e2ab11624914c3f473d4081aec83022f8000476c0002d642af0000b8616b0000583d0520000ed0496083b12f8b410000a095608000127d3224d7cb2219dd07447355d3000146400006421a54a5614e8dee00000000001802316c68a0000aa70000531073000043fc00030d00e600006a204dd1aa01314b3512d7e82e617314bf14d63e7000009ed6001ef847b00006890000b393718f7c1f10000401d449000000000000004bf897900002e300013860d1d5a21269352401400035d90845704e9a42751dd0e780003e397df3354000357c6c955d019324789193c890cf5b8cb06093c7ae058d27a43449df5f54d3545f0e5e35d4d57000069c3d814ea2a691ea369c23a02e41e319518150278adc14080004a08f0231300003a709304fe12cb0b0c1d3345547d37d42173080e8300012b501e0fc8133cce45168b5436e14bd1fc04b72d88ade0b9132f15c418f1f0818a0e4c08c2410bbc45195ec24e8d18605890f3b703d93bbd24416050c25afcb65359853616f0bc918e471e06d41bf5a4ce7617a562c40d080e570d7014a910102ca8e3a2a98ed35be0ef429690411a940412acc38754e81f349f96d652907cb3b1c6701fa8bca2de90b16078241000071329245a04d5165b59cd5c53094ffc2fac00024d800017c400000002c42ea47b74b3885200000001b60000000152442a087140e44341f8c8a6607168a21a40000000d7d000000000008b0491963700005a30000000394cb445eccca60b416ed26290765d9512d22280002a6c29200014943cecd05541c0003e9019b00011fa00009352048c482128000000142e00f00002904b092ff4eaf0d00000425c00023595f855e800033bc000180162f4ce0ef6312892957ccbf82a4c41648095003bc54cb00012d754611ca0a68dc72cf810f15a975e02e044609080004e9960b593800028b400058ed41c1918053383803517841501d70fb05d8846038d91793ae8f3221cca5c0e007a30d2121e35613983d486344adc6822aa529e0154dd95d2d1a83d3935653b81dc28bd1724e7800005a40000a080004810f8b0bf80003bdcb91174400030d80005faca2414400005ee400000017c81d1147030f00000b30d5d4064ee700006b33c8d0460000bad06e50f8000058718083d04d2947828b0dc015dce6a55302000000a4747ac00000007d716ac77e16ec9ff5f0459f4c50000538007c0ef11441b042012044e690a14a0232a010528a16f539ecc2f0000a8456717ae170400000016a519f84ad0018b64497800033e88da00012f7392400028a880b08a076049249dc4d20f7d03840002e7cbef000040f00016
  | 41 => 0x8394ba964542283051a496b654ac00016d8b1736397a520857ab1a4c45f4dc000908b13b11f016310000000000000021a09ba5edc54b000000000000000001198000052526649d554a863c19f05e85924e2a5bd06634f9c89c0e680000b940000f91432122141a4ad0fa90a0409232fccab16b4e860d60af411a94e40410c522e74dba5ef916844e519734cc00043a0c7b315048a1584ae700012410000bb248f4a37485cefc22609f53e9c32503700610cb12e31924dcd41c8000000123b000122c44a09765a255f54dbc00000000000000269098c543242cc8e2944000025078751b977f10bc34b08cc2483fa836b3fb8bab374d6965e3162e4c9932932b93283b98d3134b52903261700209c0a820e0a864d7037e380581f4418496609ca7e217d0cb43b825c2d60fad45f839d279933409502f51d3d4f7349801f1314eff35816c34a885f6468c7bf174012d1e552e04fbc3e75e044545a815c41e6c0d34ab441d2db12ed0e800a03610900465937d578099d090c8fb15fccdf43b50575214afc5bdd6ce559103a0640fb31dc4000157c00030dcec601c4d373acccba3698e8217007b910e016f0000837244cab000855dd154106133d40002b2c000573042019000000f6d78000011920000c77585c1df5c146432ad82610000000294847d000000019680134bb08d5537800026c440d000182107c8d2215513733920d0817314ed0001698000000000009e9000078e000000011712e9330123a4e7c0003058e111ce80000b60621540ca32412400000006da5d280005585810347812f25a09a8000159815580114e9d3430000000431420b34b85e40a011a444d5270085114b600caef39606ee04086a71d88b6d265cd90016c6140d4420c29616d51f757102c6963523340002bccc8b11341f6000028f0001679075ca4308396615b480001674f355b3d76a3b484ec4a5c0000c5c55a4dfca0f000126e3f480001f4d75d4aece950170000049860e601858e5f644791a3016b31983603c94f045c952e5000109503b44ee567c06e1c88f8c469d4251e1000000011472c4511f0000fd55cd4000000000023fd2651de89bc592c6d60000b9302602d90a280000000c730000c924130ddc00009730000f2e1304000385c000000108d000129d13889c7377d63400000001b2105f48909e138bc000089507c27f800015d8aa851e942c0000b5148c10db071064f50a8bc50000d6e2fc17af4cf562b00b03e1000069600008872b547de40287d2534c90152c076b0000000000136e092569d15f4dca417800031d0cc54610be0012d55a41b575700b853840180000b080000364000023d27d0a8095e37c46565878000144c00016943a61ed8a6950bc00032240190000219000140300007e510f0a3f000007752290792d80ff53410fe0000000038f0d920
  | 42 => 0xc8d13644184c18bb43d24b782fa80e032048154f6c00000000001d7400033a497a21d0e075940ccd4ad80b02f942b41cd915a0e193d200011b03f610b5065caca56294020000b4924b05d32b1d15329d05b54484574101cd7128504f90b552ab31f42354b4475a51886974500466000062a2cd0b4000001ca4850723424c44b000067b0d84bb754ec000000000055f50da45096150000000100c205521808703542700fb4a0a52d0927276ca7603685265308f75298490d30c8f8f0000d0e35909c80001111043958618b4a6b26391df09e061d5e88bd8022400031652750000e942580de03868000000000000000cc000000000000000e5d70200008571ce48e300001f4000131c180c00000000000000ae05aa03c701292f60ce5021208cffa46ed113488c2e1202010d1ac920016e87d4514477838e4f10057ceb205756fa3f6c0ff1ac041539bc31c4724f9a13d4c0c11c8000000165702852353544d4f08d16694d90dc406bc769583453706b464a48bcdef03c90cc25a858a08c80002804000536c2890fbc88e380074e4f2154800000002eb006a4d681390dfd12702acff923981335da0279421888930652790b68ad00ccd57e20a808100006455fd16b500004222cf0000547099b137110b5f3914f0758000260d017309d74c57655eb06b10fb3f0016423c88f606690f50561724219c8013ccc599284110402004d001515ae17dcd4e4e657fa2110d4a21694d525b459501981a8300157b314cc7f39d40004830cd000003c317bcfb8317c33700013cf04a119e000154f34ed5ca14787614c4553e1b892c401d12f44e8c78627b40f750a00b40001154000143f36a4f2951801d0206c3f5000000045d16ab1b9800010387f3047d7bc54f55ff11852cc4fb41f551b46120000c6c546c0004668d2b00000005c74008251d71f26015923bcc0003d40000000113a196d6c5082982540c40004b7c6d32514d004d1565527047683984bf652751051bd800032c40002a3c00000002972eed2d433c94dd23049c33d3c70719400a232c92e24d3950d46e4000001c8bd4c3531611a0ac21da800000016e528200005eb0e252f64d0b55941fc0000a3e0001347000000000000003760000569ce780000ced33d8d6b393800000000003a8575b523447c40f502c2e88e0a4fe971831f069b024c6cc22105c90000c1000007880000000000053e00008b401ad560000000000012520000469453400023c578a25c822217740001778c4e590d7e9141ca343a6c0001aa8c505874efb2cb06ab36ac8de0000c8813581d8591c0fc4b6c5470a612e85198cfb07ec88b000000033686e55ddcb8b2e5875313a4a8c3014a380ba889d00002a95d4c000247cbdd14b16ac498c36a15e887851480002c7893c0b04000137c9fd57f573d1e4089f49fd6d0175c
  | 43 => 0x80004fdc0002fd40005224f2f2d9970617180001ff87c50b88d95565403600007d83ef8f5600000001278e370a4c00008a46d740c0b2e000027a5b1000011781ec5e80f5b01e40001eed0e953158201e04de310e8cf94ea4fa84dd929301ecbcd0fac7635074c283d608cf492c83d000110d11fcc8719bc3b31ae895616a08af3d74ed80080938515121944f94a11a356720d150530d0d531297d5d400010e6000120807c44a904b8d3819b13e608209d9140c7162fa4000000133256042ad159c671000060c4fb0a6e101944c1e653fd418800037a8bda38190780c0d2d35a1099c2dad2915f99231080c05d5de9317000167029340001240e291a780005430b553ec444c606112307bcbd74f1c22a00009f21d6475147d09e34c94c15516cbd60a18b5726ec1114da03f946c50ae094483e1cb11773364dd20cfc14e19891c116d072e51714064205770509cb0f58113dc0318c090f54d5532680c740f8d8f5e095aa50cd01f019512532d9721332046c0f4c1362e40e7708548b83d7d25a346d13f4f089214c8cac1000021f4c046b429f00002c1c076499c14213f57294684e2c2c541dd1b8113038583720b35366223cc960a78bb814c8d7a00016511eb0b2630ec0370000da15a3c7120fdd033320102f1cc46e35e4451951095e91d34eea449046d45ad72f57dd4f800016bd000006800009b80000bd30e4400043acaf741281870f3c0000124f942d2d7ea02448414e7465c24fc49c0948000000163a040cb7d40487ca2064667422d30e382079e602157713a00005d18c3d26880000db029900015b450156a205fc0005c0ccd8000000000002133f34138252c00034b00000000000000030c0000000406056539a178752c800057407f70000000000002d3c800000000000440800028f400000000000000b6101d466000016b402bc03313217fd000000000a00000000fd62f5000000004320000000000151300005b9252169512b8cee4b245a91528ea32a603aa16b9571079cf7e579922e01609f804643b92bb16f613d97cf13ecf92365d5580468e5746555413a452fa1dfc0f64cccf6b000000059f80002e851bd3228f3a0eb02663f2ce2d46c80002b94f4d50ad167201c00005840002790eae4d74f6457a80000e24000000065529fc3c21dc80002868000000059758a540f4094b27022c000117563035d00004638fe937a06bc55d4cad2f9cbc12f0d2d83c4d120488547557bc37821ed74d5a8d0de0af8f3100009d7211800020d8c2c1ca0f3634e4000000059a45947521c9c09d0bf142928800000000000418131937e13ff1f20bfe01a476614c00010fd886a0dd05ec54c14bb131d1880000586163d61b0000ab9155d3f21f5912200002b200ec8e500009af027d7e13958d021f400000000c1b46051e61ff4000000163d14616d9
  | 44 => 0x815f8617060426208c57b0446878a4edd47640808bc4ce40d64e3cdf760642584f2d4fa58fd46558500c0413d0a7598119f297507d4154b815f883363db887725e096b0519255292cfaa2cccea834c0e1d3350492181d6650488b36234d3cc21995e4556c204193872a2920a5b49e17d43e8c72002082fa00008094958f8307b881400000005bad80c5e3c4f031d4b835acc80550553be21c94e112c4a3a3cd048b5d1051f1fb46fa094cc8405cd62446acf422708b7752e81fd091454f0e7d21b3d986e84a1d4302a2c1473174177508091718c893b1b2849953a021d56253b058c8bed3c853244d448331dd11a93e54b6f5becd6a295c47a1b10d870334ff1006c1c355cc3214634fdc49b569056153d55ce82d33f04c82596055129509411d152c715bc0500f18de95c301495f117a300000004fd800000008490001447561c00051185b7188d2cf3fe116c15a131a1fc537e3904d2947a0eac0000500000028e2ac4a213e856fc59d905437ad60c46011d73810afb0b2c0de1d585091b48e852a057bd5004ca300002f13424a9f18ac00000014d000011ed46985e559513200000c234a2955704a55ac00016c71b083a92610f543c20165044c9064a0cc85390163e579c2b61e0d109000000004ac0005894d7f00000000768c5556792e6282c00000000005ec8000027066d5f71509000000000000002ecc000490c0004ed07c7000116112f07dc0eb88554ef44f83dc87e93ca8ddb1fad43651857394c9ce9f5d9136d310c0ae5e38d9336714da183d7e7000156800017e42c913023f9c1071c64de6003ce6d18715661e8980a59fc7ef5d481e60108000000024d00fc4c000005490a315bb13850800000c7a22d40000068000000000027000004bc57d100012530001776261c0001c84cbd604c0005174d681f813353f0950247b896729184c211587152c5800021bc95a00001713118fb436c8ae44f391601f906152f6c05a2a20fa0245568030047322b20000080800000012dc13f800000001c116e0000000109e508543e3a40db9006142258d97473a6000000000002aec0003b08000383400047e52ee0c54a9502b013100017272ae16ca00004b4036cdc2000029000000006074a18543d4983afc00036b937a17c0f435ee08ca43292203a3000000000000e913495b7c000000000000000005d809cb46187555dad0244f8c00057c452d39b8b3843f0f4c00013630000a26000000000000003f78a9008ecde40d7052f56fc00022e80003b3133642900002a9512b3c640bd218c7c63e1d2a3000125c000000009fc4ea5b690dd5db955d1ae13d156945f35de4a8520c519d2b4cc6a5a690013dd03b43dcceb55ae555e1894ac616444531bdcc624160000000000036f44a70ddc467173543c010d276000098d3af928000001db5cdca440c0
  | 45 => 0x149ae2134a2918b977c00017a65e7d472515538100011165fc151f00000005f4cc42000010c1a4570802fd2b3000036d2e681120000000515cde55b200001b654d71c5c17645b8bb1602cd9821e55125cd03570350000217957658080000f10000228928f042c30e36c419643bc0902b6c8cc40a92dd19e13df50492d219e80e900006db0c44bf33a3c00035c12da0e3800042481c9287cce600008a13e6c0000a9c00043c54cc5500e0356f50aa36f09e72d1d1176098f470308b01411c00027d9554000000044cc0000d5106406753b3571c0643c9caff0a9000000012fd3f0cf6845715cf000042600001f70871495592106300007b053480000b70540059c26e5794000356c34d00000004d3d0941219229194400032e02d45ba08291df116300008b90f98dfe06dd80430e50ad3840000058000000000003eac0003548fe45928a3623f80c13bb4dce2b6802455c16ef5d44c991e7108c4df0e1b57855d500006dd00010400e6c0003e88d2551acc0e354d5df06c1337000000045c45ca5e411ff5868ad8287943d13dd20b30a417e31a4cb029e42aa27d000021e80002f08f550b58910244416e360c64c2350ec03f3902312d50ec1a140a31274dd118f949c0764428495d76754fd4a34ea93e51e501f8077861352b812742943dd1e596c000000a75d64000529c000000146f1dd944d000051c54b05f824dcf5c319c9165cad8115abc9b704f0e2e03cce094e50681225cf57204000015c955000000002bc8adf435d6ee57792391abd29937883313cf55da01b14ad42cd7324ec93f014385e75ba5597045484e3890cf400013804fad18a53880002cc0aea19cccb3145518501c000011ad002000000000006f00000ccf00000000000ceb389d0c811bd6814f0472900f87d952bd0c15f6078f18980001e2ced744f16d107fd7bb2d3507f167972000007340ba569c00004840000a1754555be1bcc00040fd1760000bee000149704fc38c000147f34845a6311c000363411428ecdbf00000005f6941b58cc30b04b00001091733284971150614372d1400c33a971442b111d2ee4e454d354a000402301c685f400007065664d9e5ea964f3de4d4051b06200000f033f1d5b2230061f3c154fc5050ebb1ad51193e59149480d2f919e4d961d6d70b00000000000000000092e4f6102819750700418031366800034e8dde4fa065856347541b90e5d5af16921611728551c3042dec0f11608ebd49854c82208bba406c09b2648e470be4e2b0a582f3110898c242825927140bc286c22b401018d1574c0722ac088156d2422e705ee2f3d24d0b9c90e3c24097091c9a70254efe15b500e37044d51becfdd39d10d844a8e54507cf9041991265860d655b80ca51280af500014c02660a3c5dc413e527c329478c94d083c8a0060c0f0471cba452f80d
  | 46 => 0x9c0000f8d423c84735115f200017d60ec83222ad1536052134c068854830b898b3608edd284c2ac0c3ccc71bac5c3293800048749d24079588396d4694560a91529400031c034f3bad79c514cb75000165e59191414714cb5086164c02394b7153081616fc6b61c144a12100bdc18406d03eb8e55269914c17f5583340c99e20b829d2408f7f1fc8fca000113200e08db3f3d7cd05d00000d18ead0fa8c180dc15a921315c8497cf1b33311991cccbfc000053d2b00ae800e90be4b14dbe05152404470f6c00000000d4c0005d0d6cd2f385e0134c39526417c63b0c207546400056e0a630ec0e8827740f859ad5f41dec21003952593715037000102b00000001cf508700000000c7981b000000017646e7000070246b400049c46a323191af4fd4fe859b50440000f440f7c50a48188dc0f691b51ecd47c30f832337d981245298054f5c3ff5674fe33aad5ad23389582e8126644488a836816752d1960e0e40e920d78000186d55c1e0850c19a51fb0000000492051a00003d615700004000000146c000000151e26242ee281852b0a6d21335b4a8e35e421a4840bc40000000149d5691fec15a5bcc59c03888f84e8414410d89571f6c8f915b015b355000027400002c500ec35f126b10845dc2fe4a0d42fc1b20754ca2399c8004d94acc0c7cbe849a83b85a7825b38cc661450c000400c000589824b0000ec14070000242026525242c9531c38413d00000000704000074812000000000a87000152f4d2c000000138e3c3000027e800014e48d900280000e9cbe30001407175525d01644310000000000000054cca332594b4f0d7c3881d2800000006015b88000300d21f00011c30bbc300000101414a51a005c80001650000000000037542d24d016381ed53da11008d2207497536950fa52b0bdf2854c440e297ed44010a335a42ab14d40be22481c203d095d0000cce000032a00000003e785cb000177e4c484d102c46275df460d49dd7930000517104d4ce3ef0a05403c0000000c790000dfd5bb0ece00000000dcc291439400018c55d634d15e300002fb29eccaa558c9125ac08dd00003125c68b2900009cc10b96940df171b1f690b434a9723151400b37e570a5f4150802cc4b031b930513f0e344be169f105cc4d229c45a0000a2e04d49a052d565c0000b2341708f000005410a0c737000000001e924700000002c281574d60ad210649e800011fc39ccd49000152d0000986609139100000002bb40000000edf2d4c96900001a72c0078500000003d780001fe4cd35ac55b73dd840237507142cdc4c6556531f3a9c000067c5165c58dcb0000a312dcc8bb2a2895500003c90000c1d508d66400000005ce15cd29993960af1797502c4e4346840b4c2d0ab0000a7d0c4d26200014b94d811915e90ce80000c1f5ffd38d0b80f1e2b
  | 47 => 0x241390212cb5f09d0441111577201f93b53394c2147896ff305038d039c04711d06981f7c74626ac4a53c2cc5826d83fb27c06f4584d09b4ead50a485933e09cc6ad1b3c89909803a51c206fc541400059f0ecd2db96dd0bdce8146b11d348f079d38546590e8891c0000a001a640c8396428d05a03203910eca252893d0a8d32c055016a54a53c006e175523b02a53570fe2088c68f21d53b9482579d38d51b737f0c0d3518bb61a80d5e069094240a46a85f793f91c009204d842ba06e96bb000053c3a880a41710023608cb84383cb1247cca6c1768fb53bb863056c0a425b1800008489ce2b650081b856563e44a975328533511017c0bc116a09ac0003cfc48e000107e000023e0000341331001700016a457ec9be26b000031a137747d4199063069f00000002794a5e5fe41b117c800012ed6db253056e201000000016272e4806d12e5749557d1be00000005f2d4a90480c6b3ef4d1f00002a111947a646fcc2d25f45233e210d32d40ff32ab52cd59644514a24c8f12f40df5c4800023107ab00000003328b193bb0000330c0005700bd200008c73d84e234fc4ede522cee1000019414806b704e837d003826c00000003b155a11c6c0004f24000461cac9207d28e47c8455339d72c47e11f043c86d42a5832824695ba153543a1aa4eaa5dd40002fc83d13d4c3193b9000d30c572e13c8dd7362162132184575e6811b079000000017070000000000000010c0000000148f000048f55a8fb91fb048d07852eb0cb80e320d04b3410d09602ed44043d088d000000000000ba00000000000000000000000000000348000239c00000014a84afc00347505691f304a800016b81e01567000000055343141ae553803a0e2100006441fd121c0000000000027e11257fb1030f981fd50c0564c0003ac0e6056394aa00011941748bec1cd4ef02dd8f1d0110425335cd9d16c89440d254910000ac4240c0003db430d5d710f957e40964da803012bcacd4ae959b3ce40481a9866e3878a6a00015ab43d90a23d004ff37416121c2912e06cd0d20000c061e9c1325934d3e389839c00017425548f6f48b529b4284886332c0001db459221f432f390cbaf585892f33f40005f5c91400a44ef22b139b3ee89771c0d7501bc551710f965f2250d77264d1dc040532b22b80005ff156f510c0001a10cec40440003a940002e340002dfc00000003d744548c82190f7b1e9065e000056b0000000594d54906495b1246104b0eec000000051453ec0002564b3d548d367584046e09f11d235cc2b15b311d50788e303c291d015640005b90d3639489e012b0a0c0d6c8455d8c4ca3ac44933de13c510e400038081104164125000065738c85b3529931d26e447008e400027581525ea04953169268281c41c16216cb3fdd72625b0d1023a8954000013b2b3d0
  | 48 => 0x7895b2400000000002add4670000aeb32a53c65d202875d14b69000005f59000000001193000086500000003ae40c500001d21b4400046cccd61b2d0d5000150100014100000abe1ffd3870000000000000246305eb5f0077515080005a6c17d09b510300009883c70da8512174e21440000000083089000000012a010a8000603d2c141582751b541cd241cad135e0f841be0f7000005a72f546330f8160100003ad48d800000017f63b4482405994f908dc0000f888c255c83c000000005fe126c1fb814c3f84d804dd493151f8e79524074c06f400034043a105e94c9203d54a4dc46f92964f18417400023d0fd02a70d8b0000d412eb94f050387af000129507a8d4c19a800000013ae062c1621c3c1fe1b34dc832445f5000012131801aa1128e3b55e55ed31593d60d654960cd436700017c200001fa4030b051b7cdbb3a1d07a3eb000019a000000000003bf400019d4dad000000050e0000135cbff41a0c021590e8b0001164000148852e0686341882c224c57b248c00007814eb3ad800014146ea2180d860c285db42393ca578800023cd76155b13d41f3901518dc0fd530d66652680002fd0a6f5c4c18400005c2000000000003301ab00fb3ff40001cb41180000d1d5558d4b0000000073c0005ca800006a53f40ba0779513c51d57f822f03a931000000000000fed5f6c7970000749000115755f000003295800fa00b20b18da3199000041dc00000000000000000000000000005850000000249000053b11c429b40005d0106b00010755f7406f00000631d90e280000482326d4df2d39480030d6112c0879f4c0c7a02a48f3c366c9ef34a000003e4000582000045389ec51a115f4ebcc574334c7e5028e42209472623f47e637fd5cb40680003690e8a17f8bb05dd0a53402c7e74e8899600940000000742468938b47012e14d409ee00004eb5948368537161c166ce63154c3061d012bd0000de72af035603bc76c564400005b0d325a9cfd72930f0e44ed1d900d0f1f4bc0ee2095c2c74bc914518200004c781e50000b5d2cbc22d0000246498000000004dd5ed8f065d689a41df4d1746952182cd436f31c40003d68d3d0390c632499110517cc2a49308322c4c0ee5ee801c5ac858c3f4c2a22e500003ba0d815708ed630ccc900ced19c3178abf27a95373d147bc2160b7455547fa0000ba32d208d014a158f5a38ca71ddc0004fcd2ef062080a5c3954e256c000393c13d0000fb74ce81f055891c63c5811d48496ba238527228c031d5f24a9900016073e7558c2200e7d5c256a60f94b673c5cb1043413570000e99136cea422697bf00007f64e0c4cc3464000312c9954fec04f045893e43f980916413444d651360000b0430d4be221b82b932bc47700004912bf4327258c000000000043c0000441c25540b8df057d83fe2
  | 49 => 0x36c0a825a14e8e06244cb19fc59839ad16f0490b25386518336d11b84a684870000c640d9166e5cfc0fa42ec02f254430937c8000511494e21ad3a52d6d53526c11ba0000f8a33c0000097472f000166f524d30737740004c6d5434c28be4573977b3d94cc60001424216d17f16f4db659b000010d52bc250c00021701ed3a5850f00013150000000000000022fc00034340003a4c0000a5073c0000c1e5e1000024e4e895e6400000000005e0cea64b6580e5bc4392370d19b2ed527300004b2483c3de5e195840000000416933f42e000048cc0004d08000000051100000004b902d11c60b8a2a00ba73098f481c4570d0000aba5458c49457833d1dc0b850fcca750000e4d0e8c34a5cd80002d280005e1537b00007a927c55b511cc084208089141bc50b2bc16d41350f5132f102d601c383438cfb65480f4b0e055af4c3025e42246ff4d188aa36b02843ce0676427c2ff3614afe01497f25248566492800027cd74f208804e3c987100dd82c800008e000003854b001ce1b0c47518696c147800aa2ba400010cc0000000000000000043cca70344cf4652085960001205204c00030114bf0000ef81ba45a4000052a42e800027107304ac93ac00012a5011442b04a8e1338c4b95000000029803cd4efd29c3b6896f531146a000000014d14f40ce0f893e4ce0c0be0bd03cc048142c8412142159616884c901cd48e366457835c95061510198000000035084635128aae0000a781a907921290410000071f27dcee90dec000443c0005ed4ac34a30cf3072cb8f2e78fe63a0141732301c522dcb1f10514b610156dc16bc791394567b5d502fd00002a800011b408794001160971050561f5e84b2000000000000b8c2c606f548d0fd121f0ec93d04a04000026a01787b23e7cfc429dca7326f40005698000111000003d55c60000aa05394000420c00018908023a80000131120d1cf80150000000000042744e0e3e0b015fa0000000000036e0de8000000065f000000036a80000000000452092b1afc91d53c449b000000000000001bbc8eb2500000000000000011f7054c0000000b0b445000000005ea0000c780000000092814343914c610295b335149941e94cb924891de08fc1bb068c00000002dd4a0400000000003e155fc3e18000000170400014fe00000000aed1373970000000151d2e6c00002dd4d1000000000017692dc4aa3000000010a4a942ef4cf73c0031a01587240ff475702688620f8c3bd033852e3f9481a38f476f3c045935e240395450ff64ff82d71e842ca5b097b4102471d2b38afa30e8c386050a6518d97301078d942bc421646f09532f4466556816860d400002a7894f20bd47b000014f57440000d4823637842a654b88d809c80005204cdc12e80002f189a1289c58032f800000013c4000008d489cca14ef0
  | 50 => 0x801e000000034917a9000115059c49f9562d7ec1f5553950246c749392de3428c41464145615549285ec4cd227602b70c0414b3fd12c24e552150bd024e494096225856194624f6305355d72f1cb5a4fa847e16a91b62da003d1b18933304cc9528388b212e0f77278884200a865205e13e018b168b067152743706a1210cbf723911cc2da845056416ea4114e7f25909bf3b510e236246181138ce242f4e663f188b307a179b59e069d57b895c4de041132dd697288c38f2f795f051c53a856a03181cac452494564413b56be0570c2423e97ca45b4a55481c89e11e0bc850d08e248047b44d5559a3558c4f4db177860341b4327cedb2e2400043240000a2c00053d820900492b8000000000004f1267c8c51f3c86141c474300014ff2aacf8158f0b03033d7c33730ab5543879a00011f64194d1215496831f4579515c0ba6338c859475835d2614c3006190b013346fd41b8ff04c1089b393144148ac00013cc2f21af9178284517b18285ed0ef80000bacbc000000002078cdb0000000000000000000004f6521100012254b0ca722888000129864d122400032744e30000abd56f000011205a1203506700016e62ca08b100001952c74316000085d09f541e000000045d40005cf800000005624eec000000045b3e00e650b14e72299c9da1f880004549027209882b17500000000d6f42e40002b8800056e40005f30798072048c00ad0a600000004f4043d00880dd2914b704e800003add0b658a083f5c70eb8116518b308800031c800000003ec273c443343c0004f0c00000000000b3c33c5f14000368800055ac8d700003ab009c0003c3c00000003ba53a4000000169132ec9824f74000034508250440000ac13093be8000509910e000135e1eb47e11ff0f110b7968803f8573455800018e87734cb8000392c1513d9d1ce05b48e950ec5011db89053e5c0001d04635397c0001760000424423d350d15b000000035680b602941a1000087e05e41b624944a23fb0b0d00000004abc26700017e300011ae3290db53628226325cdd62fe8c40317162007a50ce27195e800005fb3c480050c6d7665e2064b0001051000109922154841c3843b3aa5687237cb1b0f2800044c4a354da43cc398912f305c221539c42d54954a23b94af8599c00054857583ebc23827ed39a0e60000472000000000004c0000000002501f2400000003b6542cfa5386053b1d786f24c4c000582800055b911e0ab8f692fc535b229050445986dc0000aa232700001c2c07d28640000bb073b48fc97b18f520a53d529204c02680e50f2818e01bc53609464b54170074560638e043f214c6475b4c9d417e829c5ab56f21b784a31ce0d67347042c09d952207005e30e64cc921200514b9cd0c4a10baa1a0175f3990fc92b980d733fd04802991291ea82950d3936b
  | 51 => 0x3b20b0c4ed80004744a83514074749a400023243423520e9e4c2000048c83bf4e1510a4e28a400698d3c5cecf2c30695a44cc05e252ad02600010385ab8b5200011513ffc000535053f4e90e055c5c00000011fd5bf4d203a74e7e338568d598cff2045d3ba2f2cc1c3b10123000117300009ad0fc4b080000ad759747f85aa4fef42200005b781594ff12a623dc0000000f6239c00000818000220c0002a7506a00000000000ecb4420aa4075000000005830000d7b2cc56e70dc4b9755b505052c40003250c0b26690e7000178d596976f4e4863f5010c61163400010dc60949bc54e3e085790c1d01d3be43d20000e5a08456224358aaf25d0b2d58b4628000149902a56d81878f070fb8332539822e0d6938c4cc52a714197983f315a32aa892a182c9de00009342dc896e2e200003dc4000000000045a53ee1c34b5c0000ffe1ee1222019cb212728ad66068b322a2408a1f3533b5770af937cd54614890d900012982c717ad11c5016554407204288502cad15d48dc52442bd13421b48ee4aa000011905d657613795c3c76550d4000000040036bc000000062217fd182111c4fa3a34b8718a48953b556aa47904de4aa4396000078d00016390001473000132d2a3400053cc000000103c0001719000097e000034c00009a32de51705bc00000000b560ce800027f068b0001623576d800443000024303e9063953211d8000274566252f130f06f94872d8d39c431c9b441cc6903848d63148436354d15785fc4b3b2e94a50095890933082e625fd48322049a51e30cd1387cd2728e417b00513de120d479503071c5e2c02601fc6ce4311459246d7f70cb57fe1068d8c185815e38883c14838f0d0ad41eb00753e434448fc5814dda5fbc04d56510df4cf0369157911b35400042e381ae000073f04005be06152fb000104d28940003efc8960001609348c0001d7d4fd3374f2420e97560f2c8f5162c70906093880c985c54d4d67448e10130f60d4d0f7000057481091a0cecf4bcc80606ad7e5230c589424122600003f226cd68c40d861900000001188a4a0000add000009932d000050348a31d2cb4239c50e10000000000125b4e240005e480005db173c51dcce05364c451a689815e5838b392968231b48cb12fd04260042641c30000552c2f643dd32a1a20666086d1ef463c244213c4e74a84000042088c00000005add6d748f89704c614c1541000029a00003f146ed372400020a01754e4c0001814f2d1ee83b532800003bd548c26a552821d8d7e0ae05ce0000cfe00017414b2000036cd3e14ac4d3f00000004a51296108cf4a55fc0000001641000128b02b4cfc0c900005c797a72d0c75019f425f15f0a642060d914b28b994024ef21af41800000e4634bc38212149913f6400018ed3ad00006413880f37005904e2c395b6527
  | 52 => 0x25f05df22b50a9000083c083524f327844f3a5c000151885647080004f8800053bc00030452282f848880645372205d5450d542204460bbe21c081c000024c4a34d624088cf126c80004af85f9382c2db5e504da0f20e8418bd1e5513887f203064809dc7c30fc11d8272564216c05630bb4aa1544400031d8ed90a7c26f047011e373c00000007bd0d88fd439e92ac000000049f000017989b55db42ce00000003d6449419d107b23bd032055921a50597731580e3f3cf88d10cd0cde1bf800
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f5861c542040018eaca38a84080033958871508100246fc3ac719020028bc84dd932040091b907bb264080022fe11764c8100145e422ec9902000c3c74595320400117b0dba264080030f997744c8100061eb2ee89902040c9e63dd1320410595cc5ba264080022fa1d644c8100045e43ac899020048dc8758d320400193ee8b1a6408003271d1634c8100247643ac49902000caf745893204001958e8b1264080031d597714c8100066ab1ee29902000ce562dc532040011eb0c38a64080031d594714c81000672b10e29902000cb9645c241040018b8e6b2a8208003271cd64504101b46ec36e6a082000c5e65dcd41040018bacbb9a82080d32799373504100064eb26e6a0820008de8758d410400b1b90eb1a820800333dce62504100066639cc4a082000ccf735894104001998e6b1282080033658d708c4100061e3a2ca98820328bd86dd1310400187ccbba262080030f597744c4101c64f31ee898820008be87591310400d1790eb22620800327dd1634c4100064e3a2c69882000caf749893104001958e931262080032bdd1624c410006563a2c4988200387e855db210400517d08bb6420800637a0d76c841018c3fc32eb9082000c3e645d721040018bcc6bae42080271b98975c841003c3fc3acb908200087d87597210400187ce8b2e4208003179cd65c84101845fc32e99082000c3e655d3210400187acaba642080032798d74c841004e57312e990820068bf87593210400117b0eb2642080030f9d564c84100061ebaac99082000c9e73593210405f1bf0cb9e42080031799573c84100062eb2ae79082000c9e645cf210400193ac8b9e42080273398973c841002c6fc3ac790820008dd8758f21040018bceab1e4208003175d563c84100064f3a2c79082000c9d7458f21040018dceab1642080031b5d562c8410006573a2c59082000cad7458b210400199ce6b164208003335cd62c841001c3f42eed108200087d85dda21040010ff0cbac42080030f99175884100062f31aeb1082071c6e625d6210408d8ecc2bac42082261fe1d658841038c3ec3acb1082000c3e75592210400187aeab244208003179d563884100062ebaac710820048ef8758a21040018dceab1442080031b5d5628841000674b12e110820048ec82dd921040091db04bb042080131e9c165084100265d382c81082004cda7058c21040018f2cab8042080032e59170084100066cb1ae01082009cea625c021040018f0ebbb220080031ee1776440100063c42eec8802000cbb84dd9100400197109bb2200800336e0f76440100066c41eec8802000ceb82dd910040019d105bb220080031eddb75440100065dbb6e88802000cbb761d110040019b6edb9a200800336dd8734401000675bb6e48802000ceb761c910040017a706a0a2008002ece113144010
  | 1 => 0xd0a392c608002976147258c100054f420e4b182000a9d841c963040011bd0e292c6080023761c5258c100054f420a4b182000a9d8414963040011bd0e212c6080023761c4258c100052f42884b182000a5d8510963040014bd0a38ac608002976147158c1002c6f43ea2b1820008dd87d45630400153d09a8ac608002a76135158c1000567416a2b182000acd82d456304001caea328ac60800297a144158c100052ec2882b182004ada8010563040015b30020ac6080032710f7650c100064e21aeca182000e1c4359543040091790eb228608006a720d6450c100246e43ac6a182002a9c8458d430400159d07aa4c408002b360f549881000717aa4a93102000aae84d4e620400155b09a9cc40800393d4e539881004c774388731020008ed8710e62040014dd0a21cc4080029b614439881000746a188731020098ee87d4662040011db0fa8cc408002aba13519881000556c26a33102000ace83d46620400159b07a8cc4080029ba14419881000536c28833102000a6e850c662040014db0a18cc4080123ba1f52588100247643aa4b102000aae84149620400155b08292c408002b3a0c525881000566c18a4b1020048ee87d0962040014dd0a212c4080029b61442588100056741884b102000acd8310962040091dd0f992c4080029ba14325881000536c2864b102000aae840c9620400155b08192c408002aba10755881000556c20eab102000ace831d5620400159b063aac408002b3e0d74588100056641ae8b102000ae4815d162040014dd0a3a2c4080029b614745881000567418e8b102000acd831d1620400159d07aa2c408002b360f545881000717aa4a8b102000aaf845cd620400155908b9ac408002b9205735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881000557426a6b102000aad84d4d6204001c9ea729ac4080023ba1c435881000476c3886b102000a6e8510d62040014db0a21ac408003a350c43588100053742ce2b102000a6d859c562040011dd0fa8ac4080023b61f515881000557426a2b102000aad84d45620400159d07a8ac408002b360f515881000733a8ca2b102004aea8014562040015d30028ac4080029ba14415881000536c2882b102004aea8010562040015d30020ac4080029ba14315881000536c2862b102004aea800c562040015d30018ac4080122fe1d64908100245e426eca1020018dc83dd942040011bf06bb284080063720d76508100062e39acaa1020048bc875914204001938e6b2284080023761b73508100062f32ee6a102000c5d65dcd420407993cc9b9a840800327593735081043e67316e6a1020008de8758d42040011b90eb1a84080123b21d625081000667b9ac4a102000ccc7358942040018eacbb8a84080032d593715081000672b16e2a102000
  | 2 => 0xd210851000672316e2a022000975851c5404400196ec838a808800339188715011000672316e29822000975851c530440019aec638a608800339188714c110004bac2ce39022009ce4629c720440973cf0e90e4088012b921921c81100043fc2aec902200387c855d9204400117f08bb2408800a2f21176481100046fc1aec90220018dc835d920440010fd0dbaa40880030f19375481100062e31eea902205bc6c62dd520441170fd0fb2a408816e1f21f65481100061fbaec89022000c3c75d9120440018beebb1a4088003171d7634811000637baec49022000c6c75d892044001968c9b8a40880033518f71481100065a320e29022000cd4631c520440019cec438a40880127921d214811002572432429022004be08048520440a58f4edb2e20881472e9db64c41100165d3b0c9882204fcda76d8f10440039b4ec31e208812f3a9db62c411004e753b0c58822000b718588710440014bd07ba2ca080029760f74594100061fba4e8b282000a3e84dcd650400147b09b9aca0800317dce73594100043f43886b28200087d8710d65040014dd0421aca080029b60843594100051f420e4b282000a3d841c965040014bd06392ca080029760c72594100043f43884b28200087d8710965040014bd06212ca080029760c42594100043f43864b28200087d870c9650400147d08192ca080028f61032594104553cc04e2b28200087e8710565040010fb0e20aca080021fa1c31594100043ec3862b2820048be87d51640400187eebaa2c808002a7a0f54590100054ec1ea8b2020048bc87551640400917d0f21ac8080030fdd675590100054f41ceab202000a9d839d5640400147d0a39ac8080028f61473590100064eb98e6b202000aae821cd640400155b0439ac8080022fa1f53590100045ec3ea6b202000e1f5394d640400153f06b92c808002a720d72590100055a40ae4b202000a3e851c9640400147b0a392c808002a7a0c72590100054ec18e4b2020008be87149640400117b0e292c808002a7a0c52590100054ec18a4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000a3e851c5640400147b0a38ac80801a2fa1f51590100045ec3ea2b202000a9e83d45640400153b07a8ac808002aba0b515901000556c16a2b202000e3751945640400147d0a18ac8080028f61431590100255d40062b202000ab9800c564040091bd0fa9ac60800317dd75358c100054f426a6b182000a9d84d4d63040091b90ea9ac60801237a1f4358c100062fbaceab182000a9e849d5630400153b093aac60800297a147458c100052ec28e8b182000c9d741d1630400159d043a2c608002b36087458c100046f43ea8b1820008dd87d516304001c3ea92a2c608002a7e117258c100054e422e4b182000ad4815c963040014b
  | 3 => 0xc992200087d85dd9324400517d09bb264880022f613764c9100145f424ec99220008bd849d932440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011df04bb264880023de05764c9100145e420ec9922000c3c74d95324400117d0dba264880030fd97744c9100061e32ee89922040c9c63dd13244105958c5ba264880022fa1f644c9100045e43ec899220098de87d8d324400193ee9b1a6488003271d3634c91000c7743ec49922000caf74d893244001958e9b126488003171cf65505100064e39ec8a0a2051cb870d91414409d1bd0db9a828800317d9773505100062e32ee6a0a2000c9f64dcd4144069938c9b9a82881e237a1f635051027c6e43ec6a0a2000ccf73d894144001998e7b12828800333dcc625051000666398c4a0a2000c3c74d9531440a117d0dba262880030fd97744c5100061e32ee898a2038c9c63dd131440e717d0fb2262881462f21f644c5100064fba6c698a2000c9c74d8d314409f9b0e1b1a62880032bdd3624c510006563a6c498a2000caf741893144001958e831262882321f21975c85100061e322eb90a2000c5c635d721440138d8c4bae428814a1fe1f65c85100043ec3ecb90a2000c3e74d9721440018bce7b2e42881422f21974c85100061fb2ae990a2000c3c655d32144001938c6ba642880272b18974c851028c5fc3ec990a20008bd87d93214400187cebb2642880030f5d764c85100064f39ec990a204e8dc865cf21440018becab9e42880031719573c85100064fb22e790a2000c9c645cf2144013998c4b9e428813e37e1f63c85100046ec3ec790a2000c5e75d8f21440018baebb1e4288003279d363c85100064eba6c790a2000c6e75d8b21440018daebb1642880032b9d362c851000656ba6c590a2000cce73d8b214400199ae7b16428800e1f216768851014c3e432eb10a2000c3c645d621440018b8c6bac42881c71b18975885100043fc3ecb10a200c87d87d96214400187cebb2442880030f5d764885100062f3aec710a2000c5d75d8e21440018dcebb1442880031b5d7628851038f32312eb10a2048974865d621440012ef0fb2c42880034d5d764885100065b3b0c910a2000d35751922144001aaaebb1c4288003359d86388510006aaba8c710a2009ae686d8a21440019ccedb144288003595d76288510006b2ba8c510a2000e676518a2144001cc8ca3144288003a9d90628851000752320c510a2000ec76318a2144001d88c6314428812f3a1c362485102963a3b6ca90a2051cb476d9121440a1968ec322428813f351db63485102766a3b0c690a2009ce476dc921440979c8edb124288027391d8624851000733b28c490a2000ea4641892144001d88c6312428812f78dc8704851004d724324210a2000e676548421440d5d48c890842881a7b118
  | 4 => 0x24400159f06b28c488002b320d6518910006373b0ca3122000e6581194624400195cedb20c4880038bd9764189100071632ec831220008ed8799062440014dd0b320c4880029b61664189100056741cc83122000acd8399062440011df0eb20c4880029be1564189100053642ac83122000acf83590624400159906b20c4880032b9d8641891000717b28c83122000e2c65190624411dd4c20320c48823ba90406418910006673b6c63122000e4f65d8c6244001c98cbb18c488003a3d93631891000746326c631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891046f63080c6312208dec41018c6244001ccecab88c48800399195711891000753b22e23122000ea4645c46244001d8ec6b88c488003b118d71189100073232ca23122000ea4649446244001d88c7288c488136b9219511891000752322a23122000ec463544624400159d07aa0c488002b360f54189100057340ea83122000ae581d506244001c5ea92a0c488002aba13531891000556c26a63122000ae681d4c62440015cb03a98c48800393d4e531891004c774388631220008ed8710c62440014dd0a218c4880029b614431891000746a188631220098ee87d4462440011db0fa88c488002aba13511891000556c26a23122000ace83d44624400159b07a88c4880029ba14411891000536c28823122000a6e850c462440014db0a188c4880029ba17401891000536c2e803122000a6e85cc062440014db0b980c4880029be1510189100053642a203122000aaf84440624400155908880c488002b3e0d10189100056641a20312200087f855da42440070f90abb4848800237e0d769091000c6e41aed21220098ec825da42440012eb0b38c84880032dd92719091004e72314e321220048f4865c642440139c8c4b8c848800e1fa1776509100043ec2eeca1220018de83dd942440011bb07bb2848800637a0e76509100046ec1ceca12200087f855d942440070f90abb2848800237e0d765091000c6e41aeca1220008ef825d942440011ef02bb284880063720c76509100062e39ecaa1220098be87d914244001938e7b22848800237a1b73509100062fb2ee6a122000c5c65dcd424400193ec9b9a84880f327193735091043e66316e6a1220008de87d8d42440011b90fb1a848800a3ba1f625091000667b9ec4a122000ccc73d8942440010ff0abb4648800e1f215768c9100045fc22ed19220028bc845da32440131d904bb464880025d616718c9100066bb1ce31922009ce4629c632440091e90cb8c648802739189718c91001c3f42ee
  | 5 => 0x80029b61673d891000557424e7b122000aad849cf624400155d09a9ec488002ab61353d891000727a9ca7b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b122000e8d4310f62440014df0ab8ec4880029b21571d891000557c22e3b122000aac845c7624400159f06b8ec488002b320d71d891025c7743ea3b1220008ed87d47624400155d09a8ec488002ab61351d89100056741ea3b122000acd83d4762440014dd0a20ec4880029b61441d89100053742863b122000a6d850c762440014dd0bb86c4880029b61770d89100053742e81b122000a6d85d0362440014dd0b986c4880029b61730d891004e36312eb3122000c3e74d9662440018bce7b2cc4880030f9d065989100062f398cb3122000c3f655d26244001878caba4c4880272b18974989100061f3aec93122000c3d75d92624400193ce7b24c4880030f9d464989100061eba8c93122000c9e7319262440018becab9cc4880031719573989100064fb22e73122000c9c645ce6244013998c4b9cc488003179d763989100062ebaec73122000c9e74d8e624400193ae9b1cc488003179d463989100062eba8c73122000c9e7418e624400193ae831cc4880031b9d7629891000636baec53122000cae74d8a624400195ae9b14c488003339cf629891000666b9ec5312200387e86dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc65589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d063589100045fc22eab1220028bc845d562440011bf06baac4880063720d755891000477c12eab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6f75dc962440018d8ebb92c4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880032d1d371589100066a39ee2b12208cc757119462440011df0eb10c4880029be1562189100053642ac43122000aaf84588624400155908b10c488002b3e0d62189100056641ac43122000c6e76d9462440011db0f328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac845946
  | 6 => 0x62fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1004c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d100062f3b6ca31a20008dd8799463440014bd0b328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100052f430ca31a2000c5e761946344001cab02328c688003279db6418d100070fb2ec831a2000e1c65d9063440011bb0f320c68800297a166418d100052ec2cc831a2000a9e84990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000a9e86190634400193cec320c68800387d946418d100070e328c831a2000e5465944634409d5a90ca88c68800e1fa177650d100043ec2eeca1a20098ee82dd943440011db05bb286880032710e7650d100043fc2aeca1a200387c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20098ec825d94344001938863b286880038710f6550d1000c5f43ec8a1a2001a9e83d9143440051bd0fb1a868800aa7a136350d1000572c0ea5b1220038ef8754b624400155d08296c488002ab61052d891000567418a5b122000acd8314b62440014dd0a216c4880029b61442d89100056741885b122000acd8310b62440014dd0a196c4880029b61432d89100055742065b122000aad840cb624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc835976244001ccb0232ec4880038bd9764d89100071632ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec4880039919651d891025d72432a3b122000aae849d7624400155b093aec488002b3a0e75d891000566c1cebb122000ae6811d762440975cb023aec488002b3a0f74d891000566c1ee9b122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce9b122000ace83d53624400159b07aa6c4880038bd5254d891000557426e7b122000aad84dcf62440014dd0b39ec48
  | 7 => 0x5c751cd644400193ee839ac8880263ba1f725911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440019c8e5b8ac8880030f9db65191100045ec3cca3222000a3e85994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c8880028fa1865191100061f3b0ca3222000e3581194644400147d0b318c8880028f616631911000557414c63222000aad8298c6444001c68cb288c888142ad21951191100062ebaea7b1a2000a9e84d4f634400153b09a9ec688002b560753d8d1001c6fc3aa7b1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000e55811976344001c3ecbb26c6880038719764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c651936344001ca8cb28ec68813eb521951d8d100062eba8ebb1a2000a9e841d7634400153b083aec688002b5a0475d8d1027d6ac08ebb1a2000a5e859d363440014bb0b3a6c68800327dd274d8d1000567414e9b1a2000acd829d363440011bd0faa6c6880023761f54d8d100070faa4a9b1a2000a9e84dcb634400153b09b96c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c68813eb560472d8d100046f438a5b1a20008dd8714b634400153d08296c688002a761052d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d1027c6f43ea3b1a20008dd87d47634400153d09a8ec688002a761351d8d1000567416a3b1a2000acd82d4763440014bd0a20ec6880029761441d8d100052fc2ae1b1a2000a5c855c363440014bd0ba06c6880029761740d8d100062e31eeab1a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880032718f7458d100045f43ec8b1a2000c3f75d916344001878ebb22c6880022fa1c6458d100061fba8c8b1a2000c3c7519163440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc96344001998c7b92c6880031bd947258d1000636328e4b1a2000caf641c96344001958c8392c6880033318c7258d1001c3f43eeab1a20008bf845d5634400517908baac68800237e0d7558d1000477c12eab1a20098ec825d563440010fd0e3aac68800a2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100
  | 8 => 0x8bb265080123721d634ca100064e3a2c69942009acc8258d3284001938e6b228308003271d1634c61004e37312eb90c204d8ef8758b21840018daeab1643081331d58575886100052f41cc9b2a2000a5d8399365440014dd05326ca880029b60a64d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100052fc1ae9b2a2000a5c835d3654400187ae83a6ca880028fe1173d95100051e422e7b2a2000c5d731cf65440010fd0e21eca880021f61c43d95100053741087b2a2000a6d8210f654400147d09396ca880028f61272d95100052f41ce5b2a2000a5d839cb65440914ed02396ca8814a9d60472d95100043f43885b2a200087d8710b65440014bd06216ca880029760c42d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100043f43883b2a200c87d8710765440010fd0e18eca880321f61c31d95102253b40ee1b2a200087e87d0365440010fb0fa06ca880021fa1f30d95100043ec3e61b2a2000c3d75d53644400153d07aa6c888002a760f54d91100055ac0ea9b2220038bf87553644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400153f06b2ec888002a720d65d911000557c12cbb222000aac825976444001c6b0232ec8880028fa1663d91100051ec2cc7b222000aae8298f644400155b0531ec8880038d19651d911028d5a432a3b222000c3d751d7644400153d063aec888002a760c75d91100055b408ebb222051ab5811d7644400147d0b39ec8880028f61673d91100064fb9ce7b222000aae829cf644400155b0539ec8880022fa1f53d91100045ec3ea7b222000e1f5394f644400153d07b96c888002a760f72d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d911028d5ac08e5b2220008be8714b644400117b0e296c888002a7a0c52d91100054ec18a5b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b2220518be87d47644400117b0fa8ec888002a7a0f51d91100054ec1ea3b222000aae82d47644400155b05a8ec8880028fa1431d91100051ec2863b222000a3f855c364440014790ab86c8880028fa1730d91100051ec2e61b222000c3c64dd564440010fd0fb2ac888003171cf65591100043f438cab222000c5c7319564440018becbb9ac8880031719773591100064e326e6b222000c6f65dc964440018d8cbb92c8880032b193725911000637b28e4b222000c6c651c96444001958c8392c88800e1fa1f75591100045fc22eab2220008df835d564440031b906baac8880023be09755911004c76412eab22200087e871d5644400187eebba2c8880030f1d7745911000c6f43ee6b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fba8e6b222000c
  | 9 => 0x764c4200145e422ec9884000c3c7459531080138d8e4b2a62100022f61b744c4200061f32ee89884000c3d65dd1310807193cc7ba262100022fa1d644c4200045e43ac89884000c9f7458d3108001938e8b1a62100031b597724c42000666b1ee49884000cb7749853108001968e930a62100123d21d614c4200065bba2c29884000cb47458531080019cee4b0a6210027391c9614c420006373aaed1084009ce6715da21080018dd0abb442100031b615768842004e7340aed1084009ce5815da21080018daecbac42101569be1d658842000536c3acb1084009c6e715962108013ccce2b2c421012f1bdc1658842025e36b82cb108404be67105962108097cca20b2c4210003999d5618842000732baac3108404bce77058621080979cae0b0c421000e2fe1d54d93100046fc1aeab2620018dc835d564c40031bd0fb9ac98800327dd0735931001c6fc3aa7b1e20008bf845d563c400517908baac78800a2fa1f7458f100064e3a6e6b1e2000c9c439d943c400117f08bb2878800237e0d7650f1001c3f428eca1e200087d851d943c4001938863b2878800f1b9d652d8b1001c77c3aa5b162009c6c625d662c40018daebb14c5880023be1d6218b1001c3f42ced216200087d859da42c40091eb0d38c85880025d6167190b1001c3f42ceca16200087d859d942c40031bd073b285880023760e7650b100046fc1aeca1620018dc835d942c401317d0fb228588003271cf6450b1004d57416c8a16200387e859da32c40010fb0b3b465880123d61a718cb10004bac2ce3196200387e859d932c40010fb0b3b2658800a2fa12764cb100045ec24ec99620008bf845d932c400517908bb2658802637a1f634cb100064e3a6c69962009ace82d8d32c407153906b2483880122fa1f64507100064e39ec8a0e2034a9c8458e31c40091bd0fb1a6388003271d3634c71004e36312eb90e2000c6d75d8b21c40e38eaecbac4388002d96166288710006b8baae110e200097585dd921c40017c301b12438800279a1c624871000477c3ac410e2000de1215c021c404553906b2281880025d61471503100f54e422c69862000975851c530c40971df0eb1641880025d61671c831025cf3c3a4390620049e48748520c40091790eaa2c9080122fa1e43592100246e43aa6b1c20048de87d0d63840070fd0bbb287080021f6177650e100064e21eeca1c2000c9c435d943840070fd0fbaac50816b1dc437558a102d63a886eab14205a87e871d562840078d8eb292c5080123b21d5258a100043fc2aed214200387c855da42840010ff0abb2850800e1f2157650a100046fc1aeca1420018dc835d942840091790eb228508003271cd6450a1004d56412c8a14200087f855da32840070f90abb465080021fe15764ca1001c3e42aec99420008bf845d93284005179
  | 10 => 0xb184000a9c845c5630801359904b8ac61000297a147158c200052ec28e2b1840008de87d4563080011bb0fa8ac610002a7a135158c200054ec26a2b184009ace82d45630800159b05a8ac610026b3a0b4158c2000566c1682b184000a5e8510563080014bb0a20ac6100032710f7650c200064e21aeca184000e1c4359543080091790eb228610006a720d6450c200246e43ac6a184002a9c8458d43080011bf06ba4c2100063720d74984200045fc22e730840028bc845ce610800156d09a8cc210002ad61351984200056b41ea33084000ad583d4661080135cd05a8cc2100123d61e51984200247ac38a33084000a768510661080014eb0a20cc2100029da1431984200053ac28633084000ab6849d6610800156b093acc210002b5a0e75984200056ac1ceb3084009ae6829d661080015cb053acc210002b5e0d74984200056a41ae93084000a76851d261080014eb0a3a4c210002b5a0f54984200056ac1ea93084000e3754952610800156f08b9cc210002ad21173984200053b428e73084000a75851ce610800156d09a9cc210002ad61353984200072ba9ca73084000a768510e61080014eb0a21cc210003a550c439842004d73410873084000ae58210e61080131d904baac2100123da1f51584200055b426a2b084000ab584d4561080015ad07a8ac210002b560f515842004d73416a2b0840048f48754561080135c904a8ac210026b9a0b41584200053b42882b084000a758510561080135cd0598ac2100029da1431584200053ac2862b084000ab6849d5610800156b093aac210002b5a0e75584200056ac1ceab084009ae6829d561080015cb053aac210002b9e09755842004d72412eab084009ae6829d161080015cb053a2c210002b5e0d74584200056a41ae8b084009ae4825d161080014ed0a3a2c2100029d61474584200056b41ea8b084000ad583d516108001c6ea92a2c210026b9a0a735842000572c14e6b084000ab7845cd610800156908b9ac210026b920973584200053b428e6b084000a75851cd610800156d09a9ac210002ad61353584200072ba9ca6b084000a768510d61080014eb0a21ac210003a550c435842004d7341086b084000ae58210d61080091eb0f30c82100122f213765042000c6e41eeca0840008df835d941080031b906bb28210003171cd655042004e36392caa084000c9c7359141080011bb0db9a82100031799773504200062eb2ee6a084034c9e64dcd410800193ac9b9a821000237a1d63504200046e43ac6a084000c6d65dc9410800195ac9b92821000335dce61504200066a39cc2a0840048f48758541080019aee6b0a8210003351cd615042000673b92c2a084009ce47258541080091eb02bb462100123d61e618c4200145e426ec98840048dc83dd931080091e903bb262100022fe11
  | 11 => 0x48001878e9b2a64900030fd97744c9200061e32ee89924000c9c74d8d32480070fd0dbaac29016a1f21b75585200043f43ecab0a4000c3c74d9561480018b8e7b2ac2900021fa1c65585200061e3a0cab0a4000c5c73195614800187ecbba2c2900030f19774585200062fb2ee6b0a4000c5c65dcd61481218dae4328c2900023de1d61185200055a422c230a4000ad48358461480011bf06ba0c2900063720d74185200045fc22e630a40028bc845cc61480078dceb290c290002bc600411852000578c006230a400087f855da41480070f90abb4829000e1fa1776505200043ec2eeca0a40018de839d941480011bb073b28290003171cf65505200062fb2ee6a0a4000c5c65dcd41480010ff0abb4629000e1f215768c52001c3f42eec98a400087d85dd9314800517d093b262900022f612764c5200061e3a6ca98a4000c3f65dd13148001878cbba262900031b19676c852000637c2ced90a4000c6c859db21480b32d90cbae42900271bd8175c852004eb5b02eb90a400096f87d9721480018dcedb2e42900031b5d461c85204843e432eb10a400087d87d9621480b7cc843b2a429016b1b1db654852000733b28c290a4000a5e83dd165080014bb07ba2ca100030fdd274594200051f426e6b284000a3d84dcd65080018bee739aca100021fa1c43594200043ec3886b284009a6e8210d65080014db0421aca100028fa1371594200051ec26e2b284000a5e83dc565080014bb07b8aca100269ba0b71594200a536c16e2b28408fa6f825c565080134d904b8aca100269ba0b415942000536c1682b28400087e8710565080010fb0e20aca100269ba0b315942000536c1662b28400087e870c565080010fb0e18aca100122fa1f54590200061fbaea8b204000a9e83d51640800153b07aa2c8100122f21d54590200245f43c86b20400387e851c564080010fb0a38ac8100030fdd675590200054f41ceab204000a9d839d5640800147d0a39ac8100028f61473590200064eb98e6b204009aae821cd640802755b0439ac8100022fa1f53590200045ec3ea6b204000e1f5394d640800153f06b8ac810002a720d715902004d56412e2b204000a3e851c5640800147b0a38ac8100022fa1f51590200045ec3ea2b204000a9e83d45640800153b07a8ac810026aba0b515902000556c16a2b204009aae82cc5640800155b0598ac8100028fa1431590200051ec2862b2040048de87d4d63080018beeba9ac610002a7a135358c200054ec26a6b1840048dc8754d63080091bd0fa1ac61000e1fa147158c200043ec28e2b184000c5f759d5630800153d093aac610002a76127558c200052f428e8b184000a5d851d1630800193ae83a2c610026b3a087458c2009566c10e8b1840008de87d5163080011bb0faa2c61000387d525458c200054fc22e2
  | 12 => 0x123d21d51586200043fc2aed20c400387c855da41880010ff0abb2831000e1f21576506200046fc1aeca0c40018dc835d94188001938e6b2283100021fe15768c62001c3e42aed18c400087f855d931880070f90abb263100022fe11764c6200145e422ec98c4000c9c7458d31880018eaeb30c43100031d5d5618862000537c2ac310c4000d69755c221880014df0ab08431000297e0d74d95200052e41ae9b2a4000c3d741d3654800147f08b9eca900028f21173d95200062eb98e7b2a400087e8710f65480010fb0e21eca9016e9ba0843d952000536c1087b2a4000a3f845c7654800147908b8eca9000297e0d71d95200052e41ae3b2a4000a6f825c765480b74d904b8eca9016e9ba0871d95202d536c10e3b2a400087e8710765480010fb0e20eca900021fa1c31d95200043ec3863b2a405b87e87d0365480010fb0fa06ca9016e1fa1f30d95200043ec3e61b2a400387e859c764480010fb0b38ec8900021fa1f65591200062e39ecab22400087e8719564480018b8e632ac89000317d9773591200062e32ee6b224000c7765dc564480018e8cbb8ac8900031dd9471591200063a328e2b224000cb4641c564480070fd0fbaac89000237e0d755912000c6e41aeab2240008f7815d564480011e902baac8900021fa1c755912001c5e43aa8b224092c9c7355164480031bd0fb9ac89000317dd773591200062e3aee6b224000c5f751cd64480018b8ea39ac89000327dd073591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf71591200063bba8e2b224000c74751c5644800196ee838ac89000335dcc71591200066a398e2b224000ce7721c5644800196ca838ac8900032d550715912001c3f42ce3b1a400087d859c763480010fd0fb2ac6900030f1d36558d200043f438cab1a4000c3c74195634800187ecbba2c6900030f1977458d200063bb2ee2b1a4000c7465dc563480018eeca38ac6900031d1947158d200066a318e2b1a400387e87dd5634800117f08baac69000a2f2117558d200047bc0aeab1a40008f4815d563480010fd0e3aac69000a2fa1f7458d200061fbaee8b1a4000c3c75dd1634800187eea3a2c6900030f1d47458d200064e3a6e6b1a40038dc8754d6348123938e8a9ac6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000cd6531c563480019aaa638ac69000e1fa177650d200043ec2eeca1a4000c9c439d943480010ff0abb2869000e1f2157650d200045fc22eca1a40008df835d943480011ef02bb286900023d2057650d200064e218eca1a4000e1c43d9543480018b8e7b2a8490003271cf64509200062fb2ee6a124000c5c65dcd42
  | 13 => 0x46f43ec8992601ec9c74d91324c0131b90eb22649807b271d1644c93004d66412c89926009ace86d89324c00171b083126498026b321a424c9300f6c63a4849926000e8f64909324c0033990ea126498002b3219424c93000746b2284992604e8de86dc5324c001b30e9b82649800366dd0704c9300043fc2ae5b0a600387c855cb614c0011ef0eb08c298002b9209611853001c3fc3aea30a6000c5c435d4614c0018be64ba8c2980032710d741853001e2f3aaa630a6000c5d75d0c614c0018baea990c298002a721132185300056bc0a6430a600087f855da414c0070f90abb4829800e1fa1476905300043ec28ed20a60018dc831d9414c0e733d0fba2629804237a1c614c5300064e3a0c298a6000d9874dc1314c0131b9073b64298003355cc61c853001c3f428ed10a600087d851da214c0070fd0a3b242980021f61476485300246e432e690a601e99c845cd214c0010ff0abb0429800e1f21576085300045fc22ec10a60028bc845d8214c03d33908b98429802733189730853004c7c432e010a60008df835d564c80031b906baac9900262f21d54593204964e39aa8b2640018de87dcd64c810193ee839ac9900022fe117558f200145e422eab1e40028be87dd163c810193ee63a2c7900263721d5358f2048e4e3a2a6b1e40828bf845d943c810f1bf06bb287900262f21d6450f2000d4e41ac8a1e40098dc8758d43c800553908b1a87900123ba0b759872044e37394eb30e400387f875d661c80e38dce4bacc39000e1fa1776907200043ec2eed20e40018de83dda41c80011bb07bb483900123ba0b76907201c54e41ac920e4009cae7259241c80011bf06bb283900063720d765072001c3f42eed18e400087d85dda31c800517d09bb463900022f613768c72002477416ed18e4034a9c8458e31c801399ce4b1c63900022fe11764c7200145e422ec98e4022a9c8359140c8013958e4b22819007aa7211634c32004e66392c698640048bc87551648800917d0f21ac91000e1fa1471592200043ec28e2b2440048dc8754d63880091bd0fa1ac71000e1fa147158e200043ec28e2b1c400387e85dd943880010fb0bbb287100032710f7650e200064e21aeca1c4000c9c735914288001938e8b1a651000237e0d749862000c6e41ae930c40008bf845ce618800517908b9cc3100123d61e519862001e3b3aca330c400387e87dd561880a58de41baac31014b1b48375586200045fc22eab0c40028bc845d561880011bf06baac3100063720d75586200145f43ee8b0c4000c3f75dd16188001878ebba2c3100030fdd474586200061e3a8e8b0c40018de87dcd61880018beebb9ac310003171d773586200064fba6e6b0c4000c9c74dcd61880018beea39ac310003171d473586200064fba0e6b0c4000c9c741cd61880078e8eb28ac310
  | 14 => 0xc8350a3250001d1ec6a1464a000a2f210764c9400064f218ec99280029ac875093250001958eca1264a00021fe1572d854001c3e42ae5b0a80008f78758461500015c904b08c2a000e1fe1d75185400061e21aea30a8000c3f425d4615000787ceaaa0c2a00032710d73185400061ebac8630a8000c3d75508615000153906a10c2a0002ade054218540114cf43ee6a0a80118be871854150001938e630a82a0003661cf70505400043fc2aed18a800387c855da31500070fd0a3b462a00021f614768c5400145e420ec98a80098bc849db215000196ae830e42a000e1fa1476885400043ec28ed10a800387e851d921500010fb0a3b242a00122f2197448540114ce41ae890a800087f855d821500070f90abb042a000237e0d760854000c6e41aec10a802299c835d02150013958c4ba042a00263e21970085400245f43ea8b246000c3f75d51648c00153b07aa2c9180122f21d545923001c3f428e2b24600087d851c5648c00187eeb3aac91808aa7a0e75592300054ec1ceab246000a9f835c9648c00147d0a392c9180028f61472592301154f418e4b246000a9d831c9648c00195ae4392c9180022fa1c52592300045ec38a4b246022a9e83149648c00153b06292c918002a7e0d71592300051f428e2b246000a3d851c5648c00117d0fa8ac9180022f61f51592301154f41ea2b246000a9d83d45648c00155d05a8ac918002ab60b51592300247643aa4b1460028be84dc5628c00117b09b8ac51808b271cd6450a3004d56412c8a14603cc9e64dcd428c0091eb0f28cc31800f1d9d651986300247a43aa2b0c60048bc84dd9418c045938e6b2283180d32799373506302746fc3ac318c60028be845db218c00187cc8bae43180271b98975c86300045fc32e990c60008bf87593218c00117b0eb2643180030f9d564c86300061ebaac990c6022c9e73593218c00193cc8b9e43180032759173c863000636baac590c6000ccd7358b218c0070fd0bbb443180021f61776886300061f322eb10c6000c3e75592218c00187aeab2443180031d5d661886300063abaac310c6000c9e64dcd218c009974e0b2043180032e59170086300246ec1eebb2260038bf87553644c00193887baac8980032710d755913000477c12eab2260098ec825d5644c0011ef02baac8980023d20575591301154f426e6b22600387e851c5644c0010fb0a38ac8980032710c715913049f4c21ee0b22600087f855c7624c0070f90ab8ec4980022fe1171d89300145e422e3b1260008ef87588624c0015c902b10c4980021fe15769093001c3e42aed21260018dc831d9424c00193e863b284980262f21d64509301164e39ac8a126009aac82591424c0fd33d0fba2649820b271db744c93041746316e89926080c9f761d1324c101938ec3a26498203a3188744c93040
  | 15 => 0x9b1a64908262fe1d64905211c54e41ac920a4200c9c73d9141484131bf0eb1c62908d2a7211638c5210064e3a6c698a4271c6e765d621484e3acce2bac42908263b219708852125e74302e110a42008df835d360484031b906ba6c0908022fe1173d81210145e422e7b02424bc6f625d460484011f70eb00c09080237e0d755902100c6e41aeab2042098bc875516408525938e6aa2c81080637a1f73590214064fba0e6b2042008bf845d5630840517908baac61080a2fa1f7458c214064fb98e8b1842098dc8754d6308523938e8a9ac610a0a2fe117650c2143c6fc1aeca1842098bc87591430840353906b2286108263721d6350c210154e422c6a184238a9c83592410841395ce4b2482108d2a7211638c42104e67392c71884200c6e85dd921084018db0bbb2421080339947764842100672a8eec908420387e87dd560084b78d8e5baac010a2f1b1c8755802126c7643aa4b00424d8ec87485600849b5d10090ac01080f1e1d650580212df35294a0b0042098f8875416008401cd2a4a82c01080317dd75358e400054ec26a6b1c80048dc8754d63900070fd0a38ac7200021f6147158e400062fbaceab1c801ea9e849d5639000153b093aac720002a7e117258e400052f428e4b1c8000a5d851c9639004953d08392c720002a76107258e4000666b90e4b1c80008de8714963900011bb0e292c72007aa7a105258e400054ec20a4b1c8000a9f845c563900014bd0a38ac720002976147158e400046f43ea2b1c80008dd87d45639003d53d09a8ac720002a76135158e4000567416a2b1c8000acd82d4563900091d90ea92c52000637a0f7158a400046ec1ee2b148040c9e63dd1329003d938e8b1a6520026b3209634ca400247ac3ca330c8003c767594661900091e90ea8ac3201422fe1d61906400246e41eec98c8038c9e63dd1319003d938e8b1a632000637a0d76c86400062f31aeb90c8009c6e625d7219000193cc6ba6432000237e1973c86400046fc3ac790c80008dd8758f21900018bceab1e4320003175d563c86400f64f3a2c790c8000c9d7458f21900018daeab1643200032b5d162c864001c3f42eed10c800087d85dda21900018bcc6bac4320003179d563886400062ebaac710c8000c757598621900018eaeab0c43200032798f74486400266d382c610c8000cd9635c021900071bf0ea9ec6a00021fe1571d894001c3e42ae3b1280008df835c762500031b906b8ec4a00023be1d62189400057240ac4312802299e87dcd425010f938edb9a84a021fa318b73509404064fbb0e6a128080c9c761cd4250101d18c439a84a02022fa1f63509401164e39ec6a128009aae86d89425000171b0631284a01422fa1b7150940006cc39ee0a128000d9b731c142500010ff0abb464a000e1f215768c94004e563b2851928022b8
  | 16 => 0x596210052f418e0b2c4200a5d831c165884e34dd04382cb108029b60870596210053b408e0b2c4229a75811c165884010fd0fa02cb108021f61f40596210053b40880b2c4200a758110165884010fd0f982cb108021f61f30596210053b40860b2c4200a75810c165884010fb0f32ec910803179ce65d92210043fc3acbb244200c5e7359764884018bccab9ec9108031759573d922100c6f41eebb2442008dd83dd764884010fb0f3aec91080e1fe1d75d922101c5fc3aa9b244292c9e7355364884018bceb39ec910803175d673d922100c6fc3ae7b244200c5e755cf64884018baeab9ec9108031d5d671d92214ae72b94e3b244200a9e83dd164884070fd0bb82c9108021f61770592210043ec3ccbb1c4200c3e7499763884010ff0eb2ec7108030f9d165d8e210061f32ae9b1c4200c3d655d3638840517d09baec7108022f61375d8e210043ec3cebb1c420387f875d7638840187ceb3a6c7108030f5d674d8e210145fc3ae9b1c4200c3e755d3638840187aeaba6c71080e37e1d53d8e2148e4f3a2a7b1c4200c75759c763885299cae538ec710802a7a137358e2101c3f42ee0b1c420087d85dc1638840193887bb2871080e1fa167650e210043ec2ceca1c42008bd849d943884011bb073b287108032710d7650e2101c3f428eca1c420087d851d94388401c3886b2a8710803171cd6550a210064e39ac8a144200c5e65dcd42884018bacbb9a85108031d5977150a210063ab28e2a144200c3c74595328840187ccbba265108030f597744ca210064e3a2c69944200c7565dc532884018eaca38a6510803171cd65506210062f32ee6a0c4200c5d65dcd4188401878e8b2a63108030f997744c6210061eb2ee898c4200c6e655db21884e12df0cbae43108271b98575c862104eb330aeb90c420096d8759721884018daecb2e4310a271d9c6659822100c6f41ee8b0442008dd83dd1608840517d09b9ac1108022f613735822125c7743ca4b044203c6c7594960884971dd0f90ac1108029b617215822125d7540642b04420387f865d460884010fb0f328c1108030f9d265182210062f39cca304420087f87594608840187ce8b28c110803179cd65182210061f32ae83044200c3d655d060884018bccab98c1108031759573182210047dc3ac030442038bf8755364484010ff0ab86c89080e1f21570d91210046fc1aeab2242018dc835d564484011f700baac8908123e201755912100c6f43ee6b224200c9f741cd64484071bf0ea9ec6908021fe1570d8d2101c3e42ae1b1a42008bf845d5634840517908baac6908023ee017558d210247c402eab1a42028be87dd16348401938e9b9ac6908032710e7650d210045fc22eca1a42008df835d943484070fd0a3b286908021f6147650d210064e218eca1a4200c9c73d914248401938e
  | 17 => 0x264200a9f835c564c840153906b8ac9908022fa1f51593210045ec3ea2b264200a9e83d4564c840153b07a8ac990826aba0b515932100556c16a2b264209aae82cc564c840155b0598ac9908028fa1431593210051ec2862b264200a3e85dc164c840147b0bb82c990802a7a0e70593210054ec1ce0b264209aae829c164c840156f02b82c9908022fa1c50593210045ec38a0b264200a9e8314164c840153b06282c990826aba08505932100556c10a0b264200ab68114164c840156b02282c9908028fa1730593210051ec2e60b264209aae820c164c840155b04182c99082637a1f5358f210062fbaea6b1e4200a9e84d4d63c840153b09a9ac790802b56075358f2104c6e43aa6b1e42098de87d0d63c84070fd0bb82c7908021f6177058f210062fbaceab1e4200a9e849d563c840153b093aac790802b5a067558f210056ac0ceab1e4200a5e851d163c84014bb0a3a2c790803275d07458f2104d67410e8b1e422facd821d163c84011bd0faa2c7908023761f5458f210070faa4a8b1e4200a9f845c563c840153908b8ac79080237a1f5158f210046ec3ea2b1e4200a9e84d4563c840153b09a8ac790826b3a0b5158f2100566c16a2b1e4209ace82d0563c840159b05a0ac79080297a144158f210052ec2882b1e4200a5e85dc163c84014bb0bb82c790802a7a127058f210054ec24e0b1e4209ace829c163c84015af02b82c79080237a1c5058f210046ec38a0b1e4200a9e8414163c840153b08282c790826b3a085058f2100566c10a0b1e4200ad68114163c84015ab02282c79080297a174058f210052ec2e80b1e4209ace8210163c840159b04202c7908032710f7650f210064e21aeca1e4200e1c4359543c84131790eb228790806a720d6450f2104c6e43ac6a1e4202a9c8458d43c84018b8e6b2a83908271b1c965507210064e39ac8a0e42008dd86dcd41c84018bccbb9a83908031759773507211a64f326e6a0e4200c9d64dcd41c84691bd0eb1a83909e23721d635072100636b2ee4a0e4200cad64dc941c8401878e8b2a63908271b1c9654c7210045ec36e898e4200c3e65dd131c840187acbba263908e32798f744c7211c45f43ac898e42738bc8759131c840193ee8b1a6390803271d1634c72100636b2ee498e4200ccd63dc931c84031bd07ba2c1908023760f74583210145f426e6b0642008bd84dcd60c84534df0cb92cb1080297a0f74596210052ec1ee8b2c4200c3f749d1658840147d09b9acb108028f61373596210062fb9ce6b2c420087e8710d65884010fb0e21acb109c69ba08435962100536c1086b2c4270a77815c965884010fd0e20acb109c61f61c41596210043f43862b2c427187d870c565884e34ed03382cb109329d606705962100537c12e0b2c4271a6c825c1658840147d08382cb108028f6107
  | 18 => 0xc40153908992c1188023ee1d60182310061ebaea9b226200a9d83d53644c40717f0eaa6c8988021fe1570d913101c3e42ae1b226200aae82997644c40155b0532ec8988030f5d475d91311c54f418ebb226200a9d831d7644c40153b07b96c8988028fa1672d91310051ec2ce5b226238a9e839cb644c40153b07396c8988032bdca72d91310045f438a5b2262008bd8714b644c47153d06296c898802a760c52d91311c45f43ea3b2262008bd87d47644c47153d07a8ec898802a760f51d913100557416a3b226200aad82d47644c401c6ea328ec8988028fe1570d91310051e42ae1b226200a9d831c3644c40117d0e286c8988022f61c50d91311c54f418a1b226200a9d83143644c40155d04286c898802ab60850d91310055b408a1b226200ab581143644c40117f08baac89880237e0d75591310045ec3cca3226200a9d83994644c40155d05328c898802ab60a65191310045fc3aca3226200a9f83594644c4071df0ea96c4988271b18975989310061f3aec93126200c3d75d92624c40187cea324c4988030f5d4649893100636baec531262008be87d91624c40117d0e322c4988023be1d62189311c64e39ec8a126209aae82d91424c479938c9b9a84988e3271cf64505311a64e326e6a0a6273a9e86d92314c4031b90cb84629880327191708c53127e6c302e118a62388bc86dd1604c40117d0fb22c0988030fdd764581310061e3aec8b0262008be87191604c40187eea322c0988030f1d4645813100657b26e4b026200cac64dc9604c40195ec8392c0988032b190725813139e4f398c830262008fb87580604c4014bd07ba2cb908029760f74597210061fba4e8b2e4200a3e84dcd65c840147b09b9acb9080317dce73597210043f43886b2e420087d8710d65c84134dd0421acb908029b608435972137d37c12e2b2e4209a6e82d0565c84014db05a0acb908c61fa1c41597210043ec3882b2e4209a6e82cc565c84014db0598acb908c61fa1c31597210043ec3862b2e4209a6e829c165c84b14db05382cb908028fa1070597210051ec20e0b2e4200a5e831c165c84014bb06382cb908269ba08705972118d36c10e0b2e4231a76811c165c84014eb02382cb908021fa1f40597210043ec3e80b2e4209a6e8210165c84014db04202cb908021fa1f30597210043ec3e60b2e4209a6e820c165c84014db04182cb908262fa1f54593210061fbaea8b264200a9e83d5164c840153b07aa2c990802ad607545932104c5e43aa8b2642098be8790d64c84070fd0bb82c9908021f61770593210061fbaceab264200a9e839d564c840153b073aac990802ada0675593210055ac0ceab264200a3e851cd64c840147b0a39ac990803275cc735932104d57410e6b264230aad821cd64c840117d0fa9ac9908022f61f53593210070fa9ca6b
  | 19 => 0x26abe196250a4115c5ec36e2a148200d94731c542904070fd0b3b465208021f616768ca4104e57bb2851948238b8c8350a3290401d1ac6a1465208032790f764ca41014d643a849948200caf7650932904070fd0fbaac1208030f10f75582410061fa16eab048203c3c75551609040193887b9ac1208030fdd643582410061fbaa84b048200a9c8350960904011f70eb00c120803175d753d8d410054ec26a7b1a82038df8754f63504010ff0ab86c6a080e1f21570d8d4100567414cbb1a8200acd8299763504018baea3aec6a08d2a7a1075d8d410054ec20ebb1a8200a9d84dcb63504014bd0b396c6a08029761672d8d411b54f424e5b1a8200a9d849cb635040199ee5396c6a080237a1c52d8d410046ec38a5b1a8234a9e8414b635040153b08296c6a08d237a1f51d8d410046ec3ea3b1a8234a9e84d47635040153b09a8ec6a0802b3a0b51d8d4100566c16a3b1a8200e575194763504014bf0ab86c6a08029721570d8d410054ec20e1b1a82008de8714363504011bb0e286c6a08d2a7a1050d8d410054ec20a1b1a8200ace82143635040159b04286c6a0802b5a0450d8d410056ac08a1b1a82008dd87994635040153b09328c6a0802b3a0a6518d4100566c14ca31a82008df87594635040153f08b28c6a080e3be1d52d894104e36312eb3128200c5e75d8e62504018baebb1cc4a0803179d463989410062eba8c73128200c6d75d8a62504011bd0fb1ac4a080237a1c635894100477c3ac43128240c9c63dd13250469938e9b1a64a0826b3a0b634c9411c54f436c720a82028bc865c24150401938c6b8482a09472e18170905411b46e436e6b0282008de87d8d60504018beebb1ac0a0803171d763581410046f438c6b028200c5f7518d60504018b8ea31ac0a080333d8f72581410066631ee4b028200ccf631c96050401998c6392c0a098b279d063181410047dc3ac03028200c9c43dd7648c4131dd05baec9188023b60b75d92310064e21aebb246296e94439c7648c4010ff0ab86c91880e1f21570d92310064e21ae1b246238c9c73dd1648c4071790eaa2c9188023be1d6218a3101c3f42ced214620087d859da428c40193e87bb285188262fa1f6450a311c64e39ec8a146209aae82d91428c4fd33d0fba26518a0b27ddb744ca3141747316e89946280c9f761d1328c501938ec3a26518a03a3988744ca3104c6f43ec89946234c9c74d91328c41359d05b226518a023721d644ca311a64e3a2c89946200b8d84989328c41359f0cb126518826b3e1a424ca311a6c63a4849946200e8d64909328c4033990ea126518802b3e19424ca3100747b2284994622a8dd86dc5328c401b28e838a651880e1fa1f75582310062e21eeab046200c5f32dd5608c40193887ba2c11880f171d553582310062fbae86b046200c5f754c9608
  | 20 => 0x6a318e2b028462c9e7418c60508011f70eb00c0a10262f21d545923201c3fc3aeb30c6400c5c435d6618c8e38be64bacc3191c7174c975986320064e21ae930c6400c5d75d0e618c8070fd0fbaac1190031710f75582322de2f996eab04645bc5d32dd5608c80193887ba2c11900317dd743582320061ebaea9b226400a9d83d53644c80717f0eaa6c89900e1fa1671d91320043ec2ce3b22640087f855c3644c8070f90ab86c899002ada0665d91320055ac0ccbb226482a9c8654f644c8fd93ceca9ec8990030f5d475d91322054f418ebb226482a9d831d7644c905c5ca5a96c89920aa760f71d91320051f42ce3b226400a3d859c7644c80117d0fa8ec8990022f61f51d91322054f41ea3b226400a9d83d47644c90555d05a8ec899002ab60b51d91320051fc2ae1b226400a3c855c3644c90553b06386c8990022fa1c50d91320045ec38a1b226440a9e83143644c80153b06286c89920aaba0850d913200556c10a1b226400ab681143644c80156b02286c8990022fe1175591320046fc1aeab2264008bd87994644c80153b07328c899002ada0665191320055ac0cca32264008bf87594644c80153f06b28c8991faa7a0c65191324054f432a63226480a9c8654c644c801c3ecaa98c89900aa7a1b6450d324164e3b6c8a1a6482d8f741c9434c8012bb0a38a86991e3271907150d32004aec2ee0a1a6467c9c64dc1434c881938e7b2284990f327193735093204cce43a86a126409a9c8650d424c803938eca1a8499026e32094350932206563b6c8a12643eccc76dcd424c8137190ea1a84990076321d435093204dc743286a126409b8c8650d424c805d190ca1a849900ba3dd9435093200ec73b286a126401d8c7650d424c805d18eca1a8499007231d943509324bdc7c2a86a126497b8d8550d424c80171902a1a8499002e3e01435093201c7bc3aa3b0a6400c3e75d92614c80187aebb24c2990030f9d464985320061eba8c930a6400c7575d86614c80117d0fb22c2990022fa1c64585323f64e398c830a64008f787584614c8078bceaa98c29900e3d61e511853201e3b3aca230a6400e5553544614c8010ff0ab80c29900e1f21570185320045fc22e030a64028bc845c0614c8078bceaa9ec09900e1fa1671d81320043ec2ce3b0264028be849c7604c80117b0938ec09920a2f21b74581320045f43ec8b026400c3f75d91604c801878ebb22c0990022fa1c64581320061fba8c8b026400c3c75191604c80196ec9b8ac0990032d19371581320065bb20e2b026400cb4641c5604c8fd93ce6320c0990023ee1d601813201c6e43aa6b1c82008ef87588629047133d0fb9a8520a1f27ddb7350a4143f47316e6a148280c9f761cd4290501938ec39a8520a03a39887350a414045e43ac6a148238c9c7358d429040171b0731285208
  | 21 => 0x635d46250c01a3886ba8c4a18023be1d621894341557c22c43128687acf835886250c01a3886ba8c2a18023de1d61185434b55bc22c230a869aad7835846150c0193887ba8c2a18021f61e75185430070e21cea30a8600c9c435d46150c070ff0eba8c2a18038710d75185430062fa1aea30a8600c3e435d46150c0187886ba8c2a18031710d75185430060e21aea30a8600c3f425d46150c018be64ba8c2a18032710d70185430068e21aebb028600c9c43dd76050c010fb0f3aec0a18038710e75d81430064e21aebb02860387f875d76050c01c3886baec0a180317d0d75d81430061f21aebb028600c3c435d76050c018b886baec0a18030710d75d81430061fa12ebb028600c5f325d76050c019388738ec0a1a4f2e5d360981434ce6cb9ec130286008fb875806050c131b90ea9ac72100e1fe1d75986420061e21aeb30c8471c3f425d661908e387a84bacc3210032710d73986420061ebac8730c840387e87dd5609080187887baac12116f0fd0b75582422de1ea16eab048400c9c43dcd609080187eeb21ac121003175d753d8d420054ec26a7b1a84038df8754f63508070fd0b38ec6a10021f61671d8d420043fc2ae1b1a840387c855c363508015ad0332ec6a1002b560665d8d4243d4e432a9b1a8492c9e7655363508018baea3aec6a10f2a7a1075d8d4243d4ec20ebb1a8487e4e52d4b635090f53b09b8ec6a100297a1671d8d420052ec2ce3b1a84008de87d4763508011bb0fa8ec6a10f2a7a1351d8d420054ec26a3b1a8487ace82d47635080159b05a8ec6a100297e1570d8d420052e42ae1b1a8487a9d841c363508011bd0e286c6a10023761c50d8d421e54f420a1b1a8400a9d84143635090f59d04286c6a1002b360850d8d420056b408a1b1a8400ad58114363508011bb0f328c6a1002a76126518d420056b40cca31a8400ad58199463508011bf0eb28c6a1002a7e116518d424c54f420ca31a8480a9e8655063509015390caa0c6a100387d955418d4200d4f436c6a1a8487c9c76d8d435090fb1ee639286a10024f6147150d4239e4e318e2a1a840093d85dc143508c5938c7b8286a100e3de1d51d85420062f3aec730a8400c5d75d8e61508018bcea31cc2a1003175d463985420063abaec330a84008de87d8d61508011bd0e31ac2a11cf271d063185420047bc3ac230a8403c3e7555061508071eb0f288c2a100f1d9d651185420071aaa2a230a840087f855c061508070f90ab80c2a100237e0d701854200c6e41ae030a8403c3e7555360508070fd0b38ec0a10021f61671d814200c6f41ce3b0284008dd839c7605090f1b90db9ac0a100237a1f63581420062fbaec6b028400c5c75d8d60508011bd0e31ac0a100317dd463581420062e3a8c6b028400cd763dc560508019a8c7b8ac0a100335d8c7158142006
  | 22 => 0x200008a00900300000200500900000a02200000000000000100105500000400900000600002600000600b00000d00500200000c01e00003f00300000600000000200100200000100300100c00100000000100300100a00000200200401000401100b00000000b00100300000200200100a00200900300300900200000900200100803603800300300000500100502200100000801100905d00400200000500601700600000300000100100001a00400500c00501901700400800001100000500c00600901c00300e00000300000000300800600300000d00000100900000100000100401000c00100b00b00700a00300800200300100000000300100400f00100a00000103001a00100000001200000400300000800300300e00a00800800300001900701b01500600300d00000503b00000000801000000400000800500000200000d00101600100500300001100800000200200200001500900000d00300800000000002e00601700300300400000300100600000900200300000000000700d00300700000100000000000000100100500f00200100600500500100800000800001400000900d00400a00a00304900200101100300600400600000500100300f00000700400500600300200100200000100200804000000200f00900200800000200500600201200500801900000000000d00801400000000b00200c00000600100600700a00200000400000c00100901700105400000000400501304400900f00200100300100100200000000200000000300400800000000000500500000000400100400000400600100000200500000201200300100200400000101b00300000100000000200000100000200000e00000501b00000700100100900400000100000402500400202100000b00200000302100100000800000700100800700300500301701700201d00200d00600001d00000100200300e00100500700400000000c00000401700300a00000000000800000300e00000b00300700100300300000200800100300900000600200400f00200401100d00000200e00700101f00200002b00000d00000200800001501e00e00000400a00100000900b00800200005d00a00200a00001600000201f00a00500500a00200400000000000100000000400000200c00000603b00700000400201301600300100000100100600000001400100100a00000700000000f00300000000000000000800000500000201400000000500100200100000201202800200000800001101100300200600000300100000400000200600000000000000200000000100100300300b03100000300100800900100000000300d00c00800900300000500000001001900800000200000200300800000c00000200001c00000400000000c0004161fb22ea3128687c5f
  | 23 => 0x3a5e979019e0002eb0000000336800000092f507ae6d5705ab23f9d7430a31b3a3a98800095748c800000004d253800000016b0001a6400045e453ac203d86062580b7870ca751160000ada54523280001a000000000000008a80000000c6a0005bca4948fa0415a7012c00019a442a6e48f07410002eb8f927bc00000000008fc5e5097d22098650e26408e28e443596c90dc1a501fa61034e39c00000000005554e598b94b20001db13d40002c4000000000057948a2bc14ce0ab0000000000bcc21d1bcc97698d46e10b40008d52e2800171e00000000014400005b12aa00001ac478147000026c17b000000000016d266532442a52e1ff82e8a344c0a1c824848439f00e0940a724571b402386da0741e3800055c1da2cb450093c49b8000000bd007d976800000000017789ac00058b0f817b40005080001068aaa112aef858266a5baa03c72263a074adbd7a28ed439a06126c00032324981167f7000231c9dc02346f25216c082d0001614bf20004f88850e300002a9a3403ba77722bab08b3c8220e280008a6000000000099e00007b00009e69313ca00000006be0da88ec000bdd008056913c00046d05201260002bbac1d61e000449000058e0005f3000147400048d0c480000000dc00014b63e61c7aa3913ab4116dacf9176a823ca9659672676335849928858341e0ae10ca016589ac30da4640275989d6d000900700600100800100000200100300100200803200100100000102200000c00000300001000000100000200000600600100f00d00101300104a00800100b00100100000f00c00100002300700000100600000000400200500000000600101003600200500600200000300a00200200003800000201900500100100200400a00001200100800400900a00100702300500000000000800000000500100000c00200000d00100100300000e00300303900100200200000100500100000002200300400000000000900300401200200100e00000000000300100700100100700500000200001700c00100400402200000000900a00300500000100200000000000000400100102c00300601200300401c00603d00800300000001900200b00100400000500001e00700400800000000400200000500000800005100000600300600500301c01100200000e00200100102800d00104400800500500800700a00500300002200a00001900700000000000500600300400001f00000001200000500b00000500100300101000300500801301500000000000000401901d00100400104c00c00d01b00100000200000600700300000101100102000000a00800700000200000602400300500400300100000a00000b00000100000400000200300100000f01400101001000f00500000000100100800400800d005016009015001004002
  | 24 => 0x5178b8ccf800000000014820000000e0c000360267233c44472314a940d7a600011180000000000001be4bee0005e6acb80004d10001e74c3c000000000000000049380003be22e306a25c0ce0da15490052d896a5c1a9f80001be1cc800171400000000000006a200000940000c55758560aa023d41294b4abc2291fe9e6ca126890000facbd63ba28d182174cba005da22c2004680002a505c02fc51900012d000000028cc0000002550d200000ee00002854ac90100010cc00006d00015c543e00000000008c624e5ca24a43c282900028d46c271e1808afd3ecbc04b4a3741a85cd3900a4cf4a35c42597649fc45f3dd9e7c47e5ea59d9908e447a70fc22bcbd8a6f34b18c080025513ba50ccb854929e1b18d6e1cb3e1976d04253337c186d45c0f13258c4d62a3cf0a2894d5bc2d00892718c4c75e4e72af11e88204559f116603d20ec00011eabe105e95994c89063d002a019c1bf55b2a911342eb5de2cf000015c59ea7082b66df00000006d46603a51fbc0006c40fe148875c4115bc09f86208742ce800054c3c52b909d00bc00059f8ba000000000000000001e84a61220000bbd4d987300865c90002928b88b0e2fd80004e676223998dc04c33e078000011c32b3a89be96c600027f800000001305a000081c8c31d516d072458057bab203c80cf1fc88485da0005f41164c005c723a1b6cce80000c42978000b0d20c00008cc0d200025680003510302fbc30e6ea00010f07b2a891728e980000000cc1784000000426800000057416e23ec6a80005af281116a53b20380002108410000000fd00005ec945d7ac00008221bc000000000057c0001f24d200008c20003f72d24000b650000d696a472f0001304000a1a484062c00000000000016361db000000000061a30a00000008702b0000087e0003c115d8dce0001b7199d7b63455a5aadd1180000001c4400000006480000003895c7000000005707e2834a6ca0c24c80000001ae0e180004087c70001cc4000000280ab700000641bc80000008e501c8000000b6e37b800156a89c5ef80000006783e080000005cf06d80016980022488465174a740eb2b040005ef2b700005a20004008001508000000025015c3b74b0800000085b27e00003943d500025cc00000045e15ac0000003299ac40004db2ca000035e7aa58c86ac000569025000023a8d400000000000000000000b940001d98001432561000000102035d0000000b267e120419740a600000013280006b52120cccf243fc4fbaca477800000000000001291bb130c00000031c2a0c000000000175cafa39d121285d6429b22fc2ab51101ef00600007a20c3187000000000000022f4dd8b8d5239ff400098540400011f20005f6abb8e5221e39e00b44609a23591dcc000b2a0000000202a0a47f076410c7301f
  | 25 => 0x9c11092b2b4d12a13b000011e02d02b0000bab5720684e0629e473a9e0d74595000000000000056c2a5d32e0000000000a044723548beccac000331131c4de00000000000000000758f0070e2a236c81fd1083064218c780009a3000287400000000000000000000001c248b00612740000e00000000061839099d29f000091c2ca2ab845cae07b73a1ae7800036f3248e0025cae55778ad400077915202753c263c5151e0c79848c0000000000000374aa4c000a800002c940007e224d16b4dba0f7000000000000000020194d4435475a1e10cc40d26411b464084945a0b7549c9424170600f7270c150956c96468012c14c4d762c237892f02ac2a738d87a43d661d0ea834439ab592099e6002466c19880006ae1522939a6100a00019088d4ed6000015000000000010688bcb7aabf0c18000d5400033485b417c00006080013b000029596040007d90000a612a68f859a800000008c0000000fc873a17f16940000003219f495185b318b93d00005f50332b1c3269982a613d800000000010f80007bd0000a200009451358000d8078443d8000b6a00007380016ae90a1370000e8400000008293ca69a000000000000035810c40000004e4ad000004033bfa9c4462ae240e000097a9b700000006f033732500000000001e5001c00077846b06a461496f45887d40006fb1840ab97c496054781c46ea055099af700000002ff800000079e0c800011142470000a5c00090e000000110678a4ae22384183344388000ab26f60000540cb00b806408d00009cd00009e506e4442cf9cc9326bc95aa1fad21a8a928d83cc00000025b93551603a50021d0114677205180000008bf00400002c44692cd2db53d046e41caed04220004b6a5f948024f4652808e260003fa00003ae0000002090be80003c3a7a83088c200007180000171b18000000791292800000000055a173000082a00006340000000002e0800004437a0000000000000009d05889058f136800043d000083954ab0b16180015e4aec00000000006192ea00002440000001a4400000000026bc0008f25bd91d87300002ac00017d6000528a18c0000004640000ec67280001558332000553a54400044b4f58b90d9ea3904f800028cb950002d58baa0215c90b656560001be0c8cd9800049c8d54acaaba03a0d9800063919f8419456af80c797c4000a6b0b319c000052a00000012ac68a3c40c30a8043b3852df4000000000000000000040d05f85e85a753e223c0000003e100000002810001c6464e1770002d9d50c0003a91f816586ca00024b4000000044a2a96b600056500003dc63659b0a18f56b221d1800028625a15d2f4800092a000244c93c16f4eb20440004dc1f720386d63db092a1f8222588210849ca0e3b942007700006e8000126c00a32850422800000002d193300
  | 26 => 0x36051e000292c000adb4958f7cd48bb225d15e0338ad64ea80002800004600ff888e2333b3127c00050e3b4aa15294a2758127749e2aab02eaab1600b903110f4cabe48351e242ca709fd514a8580002e101a8bdd4ee907262133474215428602f06fea2d178a73c00084e0002e100000005e39e157d20000000ad0000b451f09ea12763040d69ed000000000029145220004ba0f743685410481eb00000000951ec800000000016a87ea7540622fa90b268d3ea13c02d8afe0000000cc80003688818514000132988d79e70f29604e0f70082070853c0009d4000000000086c4eb88ad4e654a2bfadfc00032554d1f4c000b323a2800d34094b48da44967400004000003e8a7a548800000056359a1518ad007004906d8e580310d88000ac816438a078c00069d000106800072e1e18164000a00000000153000043200006323ff101260cfca0001c29bf8d100005ac000095c00041b048110c4d333f1ad962491c058859c00000000001b8fc65872e100011260000001eb8448bc54818970d026501c0996d0b069c0000000dc85a818699383fe60b00000008de9280bd138cca264f24c06380001ed2c680012ca0993f9046029a0cb17980000000001eb85940000000000000b861a600015100000001a92be45cc00037a942c000b10421000088657a20b800083c0000cbad4000000000000000000000000a340002b000000013f20002f00000000b370000d3474800007c85f570a4ea5131350784add0000e1136a0003e30cc95da000000000128e14200001cc5c400027b9444e2c1d40001774ffe4851920000440000000000000021b1fc15096d239013199351587072f41c9c0001941282e2400067d4f9a2cd2aa8ea415a0340000c257da29909497900a04d45660000000a3c0000002268001536b063f890e40004e4254892059c759125af5c71cb310d900017342b215b000000072d00023bd520000362831c0009d200000013100003120000f120200fd00015f45470000fa44fa532409800000000000003d40009875d12b9d6ecb1430b8cb400013b413a4740e4ab958d2ec4b4c00012480651fa2780452e8538a3534f800000007860791829292a5f205a82400087600000000000000000001130000165800000081556980014d0a524e8800127e2f52d219301105be249a9b8c02b18000000000000000000008a00bf00016b0000000000000000000048f80003a2000000000000001d0000f8d442000247800000076e0000000ef62374de8a700b825609d0b7c0000000002a1ca2a5245b605780000f81792548000420297947c48a0d53150000a6e8791c52accba01cf13416b87ca5043a980ac5ce0e4000206c00021700000f90f49ee08aa59c0008a40001964c5a8e82f98af4000526000000131685f443a444824a4f36700010bc9051
  | 27 => 0x56295a890e00009880006169e200000016be000486130000000015cac91688000518800068800044a102400000000013ec0000004ada2e112c00047498c5314bba42600003a4738000000000007c3adadf80009750002c051b006c53e8eb0e687995c3282d12aba436693b4000bb80cf806d5a230f0290000c38b9c4ec8000000a635cb13840ea82808a15d57ce39400000004ec8670bfa0280009da014800110095f000000116c847000000000000042b19500920002909688aa80005a9800050450800001bd4a000000021d45d85055f70b34ca4a99418178c2dc3bb331a98517c3bd3d11c08e240002a92540e9e6930630c449c46ed2a71df08982134dc267000080216b2e9c9c032e0a71e3d49250622305c0402ae35ec2a34e723e428c0000130b270f100000008e238e286116400025f80017007b33d88bc103a0ff582a244e340a24568000c500d30000000000173000000149086120b0ead33e4a10000f50eb401a29482a8c646e13e6ab5c06c7360908000a3a0001268f2073e13d4c610dcc5e4670e0a0654ec2d341e91900005730002538eea0a401d1fd80a053f2432a2111a0003c610d000087c25680000000000000ddc00003712024100120954d7000032262c57f80ec00072428b1f30c820000ac800127cb6b00000000000004fd0000000be500002dc000a072f4a00c0007a304b02444e42210538eb4e168264298d043bc6941d91de8a1e9e92c480000003ec3aa9535450ad92400798000b482dd80016ee0dc2ff08f0d200000001ab40f4bb538b9d80fd81570db944d42812c0838874cf400010380000005f60000b1927a8db2e01e5c0000005a300013740004091fcd07cb430000000eb00003ab8160f2600015626fc4d22a512ca01d248b2f3d0972d07000037286e8bca0005ba274c000683072af780000003f81d24caabe0086a38c3e09714f38000e565980002ba966600013fae0400009a2db9eb4406000164a730000a5a0d2211522c58636411588149db081aaa42048001ad96fc8a44f2000018c6048d94da174884a50d31f20bd608acb4cb22954a6315558116867824124ea6ec43e5625b825ad37841c4f32b553c094d4cf0d28ee22ea18f82794366a12940fc079c04e3791fe80f289f02a2a04ebea223ba13f551452e5a8963937c7a40e994489ba3301bf13e4bb0748005ab30c40b2353492d95d294618e98451d8a3e4caa120cfe368252a598b244c63b2097933404f0e22f515802ab2682b982941f327388e04864260c117b4c8a5ee11ca3348526731c61b6022039b2880cec0000000c900000000a90000658c265824058630000a373e70000000a9d3158d2c000a6625c985400045c551a9c0968ae10569998000acf0002c2527469e5df800000079c2190000000b1c00000000ec25b1f90000fb02600000000
  | 28 => 0x94ae0000001efcd3e2265a7a35d0a0a924bf8000000920071191082a5c813aa2255ea19500010a0000462046a05c000000000000176600008280001ba9ed0bc02c8000acd09a1ad05543222e09c8488a44f197899d342bc40e125dc05e0005cc00000006c72778a1c0001360ed00006b011654f00001c6bb7041800000000027d1f6965093224b26a4be000057b1a8c0002c80000a646e8b470a9a8546e25e70001cecd580002659ff00001a32e700013826772b39f414fe0000e485d4e08809347a8f478eab10bc85a919c346220800129e0e0570237cbf86b84c725f451200e26f9744c1828417e9ed492a9c72eb2fb0e0238d4b1800015e00019e8000e6a81e0a0a0c808068b1a4a3851728993199a084988f1343870124424a52a8e5955c455105965c98a3d054e00914268d311905c81801691bea30547eb383b398ed1444b152c27015a09b014d8c60d72a423dd048c41e833228a3145dcba923da7d45280110bd88a8f1648b01621dc0a23e241daabc0301f646228b0b747702de16e082880c37fa8c06c40df55dae4c2c611a213823d6aa00053d86ed7c80000a20000000ac45b20001266329334015800000054f80000004e65301f9c2a25000002dc491260423809ec1d463458180a0f7c3a700000000003a033c9fe10d410a23520fcde03c64f18d910888fa022912563a3160b013793beb171290d4108c6720001bad3fe2a81fd9b5d0c40b600024088d618118000000004be0a5aaf46caa065d5226c46c8cc08d99697102105018cd86805fa4290738db80a053689a80680002f31838d783970bb27bd6cc8232728398c7a4753ef269c0d648a10b00010fe2194658a14e3ab200428c1c6f68b751c1afc0fa0ef09f25d8e3e90f4a0aa2cb167465b083600780001b9a5e13501bc2c80204fa274c0000000a28b995cb9abc000a053fc9af55a428304b9bf072a22756a00013fc0005dca5011e63d625c1770000adf2029251448ace0b0821cede3da26b8e788900000000000a6067b1491e4038e23a37327ecc1e36916621f433a06830810110b448222a1d940009824962a580007db018000091a66f0aaa6b4ed80003a68ab4c249c436189f01e800018a01a4d1c00000016a40000000dead28aba0001d78000c9035f0669204430000464a66cda80003609790d2e6a71ec215d2b0bc115e0f700004a4104895c0000003880e088440004f228480005c60001074b1e0002b60000be40001e2000004432c00017880007cb37194e40000003c02c451ee53a0031da80002fa08f8be52c847709f800125cbaf03c00003fa000006a284afc5204341aac5b03352612eb4000000332ac295920001f69e3477c0005ea88f80001e032fabf549a81f3e507dcf8a73d0000000c3097c14b02d4dac27a4801ca94a835e57429b0a4644a3149f591dc000
  | 29 => 0x1f986da1f91b38ca92e42715532e7563e2e9076ad7492e6ee182a6ad75049057e026d2603ef1e0966c2d0a791a38d393e40fa25318fd38640f1f8906c9d242c3f491e472631a2bd9644820bc33610e2c92468441aa838b421e730390d97c62000239a3040a14721785c531258443685755e210c3d30d08f34869019007d062a6522e91e8ec2a0104e2e8cdc07af3832f095e61fe55f02e85804302a19d40e4a47c15790303407b60328c0d3e896e0000974d5c6921c427f0eb8b4240a06e52a822822028d841076800084acd0c9801da9a1426ea4c1221d10dde00027c00000003cd1308de87e81a200aa844b38a2516a1a94f0283a563000000075600000007447fb0000ac43e251944100009926a02dc8db131e5b024e0000b5e28e0260000000000000000025a0003658000000b7c40209896b40d626c887005cac3042062978c01c3389d395426d305cae1ce4c6e200010e0434ada00003f8000000330a7b00000001ef1f000007ed0c4a3d85ae7dc29aaf2c734970427ae300000004db2180fba0002560a413a02be03b80005406753bf1628b180002e9a7786748c600000012f600048babd00000003ef800067213c0000a680000001458c240009624848fa803c2515e72eec7523bf25994f50a2a5d1a603287d012802f9a54cbc1b34730f2c576000251ad70d509b10001b544e00000000794e7e3fa25786a03a07b0076153d0ba00052224847500d70000dc83f62b7000191d43c00005300000006b32010d642929235b986a922a07b0211c153589aa3faa344aa2b9f3ea866c21e04836f0000bbe3261dc01187e64603d499b926a05b4ae90ace107151368ec49568d208581891fe57c48c00000006211fb88b53f03f600000016e4855000247827261f3be800000041f254195c00000054a8000166ba52d89f3c1fabb03010000a964d8000000000000000000002120004d29c34d4c29d0001bf40002f82a400013949dc52300005aaa3b3019f5c0000002fe800000095e22da6989a40001691f200004061230854a685b623f000176c56f3a58c7096a6050001c3939014c5b500000000de162ae2c5deb9149a01f853e000000000021c4190000028fd44a206c8000e6612f15180005fe13022705f0eda73708980cceec616000000000000042e24e07929912ad2650a140a542a220407ab7a1320a30c4a8e00002c98c121322d0290c0000003cb2a80198000000288cd3600000001a84cc00f0000d0c59e3b00002a880008161a782c08d80000000d586e06c92cc90b80001ea211aac
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc01c0d9210d751854300503648435d46150c0141c94cc9751854300523648435c06150c0150d9210d75d81430052364843dd76050c0121d9810e75d814300583648439d76050c0148d9210d75d814300583648435d76050c0141e9390d75d81430050b648435d76050c0144d9210d75d814300607a60435d76050c0181d9810d75d814300703a48435d76050c0141d9210d75d814300703648435d76050c0140d9210d75d814300507253325d76050c0148d9210e71d81430050b648435d6619080148d9210d73986420050b64843dd5609080148d9210f73582420060718d851c5435080181c636177050d4200513648435d6618c80148d9210d74986320051364843dd5608c80148d9210f745823200607191851c5434c80181c646177050d3239e231d88150d424c80130d952054350932316231db8050d424c80130d95e014350932404a32616350a329040142d9210f75582410052364843dcd609040181f7520d425824100623613729cb635040148d9210f75d923140623a0843dd7648c40148d9210d75d923100607e14435c3648c40148d9210d70d92314052325d64909328c41328e98d91424ca3104d23a5f64509328c47188c87d91424ca310051364843dd5608c40148d9210f745823100607dd4844c9608c40188d83dca72d91310052364843dd943c840148d9210d7650f21005836484359543c840148d9210f7650e2100523648435d9438840160d9210d6550e2100523648439d9434840181d8510c7650d2100523648431d9434840188d845c87258e40404a3a636350a325000142d9210d751854000523648435cc615000181d7520d42185400062360d721c9648c00148d9210f755913000523648435d5644c10188c8210d75591300062510c815d5644c00181d8510c715913000523648431c5644c10148e97d92424c93004ca326164509324c01348c97591424c9301162321d64509324c00144d9210d751853000523648435d0614c00181d7521132185300060761443dd9438800148d9210f7650e2000523648435d9438800148d9210e7650d2000523648431d9434800160d9210f6550d200052364843dd9430800148d9210d7650c2000583648435954308001a85436084398420006a150d8210d610800148d9210e7650f1000607614431d943c400148d9210c7650f100060761443dd9438400148d9210f7650e1000523648435d9438400188f7360a73d911000623dd1829d3634400148d9210e7650d1000523648431d9434400160d9210f6550d1000623a1d4310f624400188d8750c43189100051965c6518a2144001c25751906288510007115d46318a214400188d736087359010006235d1821d1630400148d9210f7650c1000523648435d9430400160d9210d6550c100062361d4310e620400188d8750c4358810
  | 1 => 0x18854e84a07200a8771d9948a70261080067001a8b2380c0008c003e90c00480487cd034331c904630e86c3c602b09400141001cde000d1fc324900028d80000000001111000780022184f000000dc9a581f8b40875000001e7e0005c002a23814ae24368bcba290008c4236209f0bc3a3d0f8c810288f4027635898e24f00000e6332f948384b2a9b8805c010c810030609ca6390696cf600408ac005a0b138501234818c430000b816501a8005879098ec082c101c1424000c080010040c0c00000009486c24006c0028200c00000008480004041c2400000c1c000150d9210d751894300543648435d46150c0148d9210f751854300487660439d46150c0160d9210e751854300523648435d46150c0160d9210d751854300507a4e435d46150c0142d9210d751854300513648435d46150c0181e9810d751854300607660435d46150c01c0e9210d751854300507648435d46150
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc018204800400d42001053ac2000000c036619210d751854300601b30c9086baec0a180300c766548150d424c8018063b32bc0286a126480823ea19210f75d923100601f0ac9086b86c91880300d85648431d943485010465432421aeab226000a2168843205755913000601b0ac908638ac89800300d8564843dd94388001806c2b24218eca1e2000c036159210f7650e10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x138e
  | 9 => 0x3
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124c
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138c
  | 17 => 0x138d
  | 18 => 0x8c
  | 19 => 0x8d
  | 20 => 0x8e
  | 21 => 0x98c
  | 22 => 0x98d
  | 23 => 0x98e
  | 24 => 0x128c
  | 25 => 0x128d
  | 26 => 0x128e
  | 27 => 0x150c
  | 28 => 0x150d
  | 29 => 0x150e
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12cd
  | 33 => 0x12ce
  | 34 => 0xa0c
  | 35 => 0xa0e
  | 36 => 0x130c
  | 37 => 0x130e
  | 38 => 0x20c
  | 39 => 0x20d
  | 40 => 0x20e
  | 41 => 0x140e
  | 42 => 0xb0c
  | 43 => 0xb0d
  | 44 => 0xb0e
  | 45 => 0x140c
  | 46 => 0x140d
  | 47 => 0x154c
  | 48 => 0x154d
  | 49 => 0x154e
  | 50 => 0xb4d
  | 51 => 0xb4e
  | 52 => 0x144d
  | 53 => 0x144e
  | 54 => 0xb8c
  | 55 => 0xb8e
  | 56 => 0x148c
  | 57 => 0x148e
  | 58 => 0xccd
  | 59 => 0xcce
  | 60 => 0x15cd
  | 61 => 0x15ce
  | 62 => 0xd0c
  | 63 => 0xd0e
  | 64 => 0x160c
  | 65 => 0x160e
  | 66 => 0xe8e
  | 67 => 0x95396
  | 68 => 0x94056
  | 69 => 0xb1396
  | 70 => 0x141396
  | 71 => 0x138956
  | 72 => 0x95416
  | 73 => 0xb0956
  | 74 => 0x94b16
  | 75 => 0x1409
  | 76 => 0x140956
  | 77 => 0x209
  | 78 => 0x249
  | 79 => 0x1449
  | 80 => 0x289
  | 81 => 0x1489
  | 82 => 0x14c9
  | 83 => 0x138b16
  | 84 => 0x139416
  | 85 => 0x140096
  | 86 => 0xb0996
  | 87 => 0x98b16
  | 88 => 0x154996
  | 89 => 0x99556
  | 90 => 0x1649
  | 91 => 0x134b
  | 92 => 0x21296
  | 93 => 0x141296
  | 94 => 0x150b16
  | 95 => 0x9cb56
  | 96 => 0xcc9d6
  | 97 => 0x9ccd6
  | 98 => 0x180c
  | 99 => 0x1452d6
  | 100 => 0xa0b96
  | 101 => 0xd0a16
  | 102 => 0xa0d16
  | 103 => 0x168d
  | 104 => 0x149316
  | 105 => 0xb0214
  | 106 => 0xb0215
  | 107 => 0xb0216
  | 108 => 0xb1416
  | 109 => 0x20b16
  | 110 => 0x140b16
  | 111 => 0x155416
  | 112 => 0x141556
  | 113 => 0xbcb
  | 114 => 0x144b56
  | 115 => 0x28c
  | 116 => 0x184c
  | 117 => 0xcd456
  | 118 => 0x144cd6
  | 119 => 0x148b96
  | 120 => 0x24d
  | 121 => 0x16cd
  | 122 => 0xd1496
  | 123 => 0x148d16
  | 124 => 0xd0cd6
  | 125 => 0x160cd6
  | 126 => 0x40c
  | 127 => 0xcce96
  | 128 => 0x58b
  | 129 => 0x188c
  | 130 => 0x178b
  | 131 => 0xd15d6
  | 132 => 0x3cd
  | 133 => 0xd0e96
  | 134 => 0x170d
  | 135 => 0x18cb
  | 136 => 0x10c
  | 137 => 0x19cb
  | 138 => 0x4956
  | 139 => 0x14b
  | 140 => 0x2c9
  | 141 => 0x24211
  | 142 => 0x28211
  | 143 => 0x9416
  | 144 => 0x449
  | 145 => 0xecd
  | 146 => 0x104c
  | 147 => 0x180a14
  | 148 => 0x20b14
  | 149 => 0x20b15
  | 150 => 0x29494
  | 151 => 0xd0cce9e
  | 152 => 0x194c
  | 153 => 0x1689d5
  | 154 => 0x25455
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2182
  | 6 => 6184
  | 5 => 3056
  | 4 => 131
  | 3 => 13
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
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (89458+((h/727+packedAt gbK7 (80734+(h % 727)*12) 12) % 3484)*13) 13
  | 6 => packedAt gbK6 (323625+((h/2061+packedAt gbK6 (296832+(h % 2061)*13) 13) % 7421)*14) 14
  | 5 => packedAt gbK5 (192520+((h/1018+packedAt gbK5 (180304+(h % 1018)*12) 12) % 4034)*13) 13
  | 4 => packedAt gbK4 (9514+((h/43+packedAt gbK4 (9170+(h % 43)*8) 8) % 158)*9) 9
  | 3 => packedAt gbK3 (1073+((h/4+packedAt gbK3 (1053+(h % 4)*5) 5) % 20)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe03ff80ff81fff03ffffff44f3c7a38f1ff
  | 1 => 0x3e03fc0fff07fe0fffc1fc07fbb4d3a5c73e73
  | 2 => 0xc003fff00007fff0fffe1ff80c38e3c607cf9c
  | 3 => 0x3fffffff80000ffffe0000fc0fc07f80fe0
  | 4 => 0x3ffffffffffff000000000fff0007fff000
  | 5 => 0xfffc000000000000000000000ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4218005280090011200224a1400104081850a5
  | 1 => 0x34202c053102a20a54414816a19451a0c32652
  | 2 => 0x804356a00844d5a09ab413502c28a2c6058b18
  | 3 => 0x108b9b39dad01080ef398060cec0fc07680de0
  | 4 => 0x2113e3ce6ce779cc021001830f7f0007b6f000
  | 5 => 0x39e10200708061080c2102040ffefb70000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36745
namespace PEqualNP.Outside.L_meta_36745
open PEqualNP.Outside.L_meta_36745.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 9 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 26 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 134 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 26 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 134 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_160 : Interval s5Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_224 : Interval s5Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_256 : Interval s5Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_320 : Interval s5Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_352 : Interval s5Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 396 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_64 : Interval s5Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_128 : Interval s5Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_160 : Interval s5Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_224 : Interval s5Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_256 : Interval s5Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_320 : Interval s5Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_352 : Interval s5Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_416 : Interval s5Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_448 : Interval s5Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_512 : Interval s5Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_544 : Interval s5Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 601 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 13 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 131 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3056 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)))))) (concat (concat (concat (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))) (concat (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)))) (concat (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080))) (concat (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))))) (concat (concat (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))) (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2432 : Interval gbAtlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2464 : Interval gbAtlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3776 : Interval gbAtlas 6 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3808 : Interval gbAtlas 6 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6184 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)))))) (concat (concat (concat (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)))) (concat (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))))) (concat (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))) (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072))))))) (concat (concat (concat (concat (concat (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264))) (concat (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)))) (concat (concat (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840))))) (concat (concat (concat (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936)) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))) (concat (concat (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416))) (concat (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)))))) (concat (concat (concat (concat (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800))) (concat (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184))) (concat (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280)) (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376))))) (concat (concat (concat (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472)) (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568))) (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760)))) (concat (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952))) (concat (concat bgb_6_5984 (concat bgb_6_6016 bgb_6_6048)) (concat (concat bgb_6_6080 bgb_6_6112) (concat bgb_6_6144 bgb_6_6176))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_128 : Interval gbAtlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_160 : Interval gbAtlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_224 : Interval gbAtlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_256 : Interval gbAtlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_320 : Interval gbAtlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_352 : Interval gbAtlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_416 : Interval gbAtlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_448 : Interval gbAtlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_512 : Interval gbAtlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_544 : Interval gbAtlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_608 : Interval gbAtlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_640 : Interval gbAtlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_704 : Interval gbAtlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_736 : Interval gbAtlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_800 : Interval gbAtlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_832 : Interval gbAtlas 7 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_896 : Interval gbAtlas 7 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_928 : Interval gbAtlas 7 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_992 : Interval gbAtlas 7 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1024 : Interval gbAtlas 7 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1088 : Interval gbAtlas 7 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1120 : Interval gbAtlas 7 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1184 : Interval gbAtlas 7 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1216 : Interval gbAtlas 7 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1280 : Interval gbAtlas 7 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1472 : Interval gbAtlas 7 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2182 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)))) (concat (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016)) (concat (concat bgb_7_2048 bgb_7_2080) (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8eeeaeaeaeee8e8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 4008241320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36745.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[1,5]⟩,⟨.and,[0,7]⟩,⟨.or,[2,8]⟩,⟨.or,[0,4]⟩,⟨.or,[3,5]⟩,⟨.and,[3,4]⟩,⟨.or,[9,12]⟩,⟨.or,[10,11]⟩,⟨.and,[6,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008241320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008241320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36745

open PEqualNP.Outside.L_meta_36745 in
theorem PEqualNP.Outside.L_meta_36745 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008241320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008241320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
