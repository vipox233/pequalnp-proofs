import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37437.Model
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


end PEqualNP.Outside.L_meta_37437.Model

namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
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

def SBf (j : Nat) : Nat := [4, 6, 6, 7, 8, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 84]

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

end PEqualNP.Outside.L_meta_37437

namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xf83fff803fe00ff803fffc03fc07f80ff98c7
  | 4 => 0xffc1ffffc0000ffffc01fffc0007fff01e0f8
  | 5 => 0xf0001fffffffff0000001fffffff800001ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4110825924928a28a4924552d2d4a5a952ab5b
  | 2 => 0x822104aa4925145149248aa565694ad2a555ad
  | 3 => 0xd47609376239a69a63b913f0398c7318f998c6
  | 4 => 0xe843b1c473b1d8e47231dcf9b0307c7c31e0f0
  | 5 => 0xf7bde0783c1e0f87c3e1f3e3e3e6060c1fe00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37437
namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x600ad2a400a76b00030002000832803f641f541f631f531f721f421be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa802040602aaa720cd552319aaa0435553087508010720c020
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 22)*5) 5
  | 3 => packedAt s1K3 (168+((h/2+packedAt s1K3 (162+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe00fe01fe01fe01fff80fe03f81fc0ff718c7
  | 3 => 0xffff0001fffffffffffff0003ffffffff81fff
  | 4 => 0xfffffffe0001fffe01ffffffc001fff01fe0f8
  | 5 => 0xfffffffffffe000001fffffffffe00001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x9649020c121422242428b16545922c95236b5b
  | 2 => 0x2bd85554b54ce51d48fc0aad2ab1558f5718c5
  | 3 => 0x4c92d1a9292949499155581033659b2a9815ae
  | 4 => 0x711c9931b1b191911d9e6cd9a041e3c31da0f0
  | 5 => 0x81e0e1c1c1c1e1e1e1e78f1e3c79020c1ede00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00aa00a000aaaaaa00aa00a000aaaaaa00aa00a000aaaaaa00aa00a000aaaaaa00aa00a000aaaaaa00aa00a000aaaaaa00aa00a000aaaaaa00aa00a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37437
namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x19000428000180058800394016b000480030000bf41bd41df31dd31ef21ed21be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xa0195414c74a8290f14c521
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (244+((h/4+packedAt s2K4 (224+(h % 4)*5) 5) % 28)*5) 5
  | 3 => packedAt s2K3 (84+((h/1+packedAt s2K3 (81+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x3f80fffe03ffffff01f83f07ff07fffe88e3f
  | 3 => 0x3fff00fffc03fc0ffe003ff83ff83e030f3cc
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80840a022048480016284508450842a8334d5
  | 1 => 0x5155294651a92934781522a46aa46b55288a2a
  | 3 => 0xaa64aa6a94a3b215bab0433d233d2381b0d34c
  | 4 => 0x3346cd8d193223a6dcd9ea0843ce71063d03b0
  | 5 => 0xc3870e0e1e3c3c38ef1e73ce720842183eec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xaaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37437
namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a51a440001000ba8003021b0c800002498503122ce212600aa352507813400000007c3800058022309cc8000015003c74702480080500000040401007043100043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x171095169c880e1aac1985802900089c2c91862600030022280012a5ab8f022980002b238b28808d000020a00900068001249804219f190285110b962d1300159e22aa1a23142d8a1d1f97800192240c849da78d870a8009a693802700189b9000078eaa948f80038c21251e80001b0305000170d0010009080011d0040e820a0088004001000420102b7a92876c5250f3a8621d7d4d42ae29a853f544ca78a8995b94b41b6a96835f53506b8a6a0dbd4941b6292837b50506f0a0a0d794c41aea98836e52cc6daa598cfd51319e2a2636f524c6d8a498ded4131bc282633e540c67aa818cf952219eaa4435e53886baa710eb95221d6aa443ce538879aa710db94621b6a84436e51087cca210db54021af29e815d53d02bca7205754e40b7294816d52902dca4205b548409f2a6613d54cc27ca9184f55230b7294616d528c2dca4185b54830b728e416d528827ea8904f15120afa9a415c53482eea2905d14520d7aa241ac544839ea6907314d20f3a8a416c51483c8a2905914520f5a82416e52082dea5885b14b10b7294216d52843c843084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087908410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2084ca06e00000a31894310f0e5494e21c315053483275414520c915051483475314520d114c51482656508410
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2694+((h/30+packedAt s3K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s3K3 (312+((h/2+packedAt s3K3 (304+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff81fff81fffffe07fffff03ff03fffe7f8e3f
  | 1 => 0x3fffffffffffffff81f01fffffffffff88ffff
  | 2 => 0x3ffe03ffe03f81fffe001ffc1ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffe0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x84a42888c48928601652a52125213954338615
  | 1 => 0x110851110912408580a40a464a4642a88838ea
  | 2 => 0xa6149aa243a42b6aaa0a93a913a91c0d70d34c
  | 4 => 0x3459634492074db34d3cc0c21cf38831dd03b0
  | 5 => 0x386183871c3871dc71cf1cf380c210c1eeec00
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37437
namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0xb162670869c51080004a0003627f0450001ba000e99844ea94c5314b000930198000000000028a17490c268000009e0b100039c914ba90e3f62a8002032ac0800005d000111170fc3509d13f93c3884f4069540a2a30941d60324ccc8000000128df00021080035a7637292087936482554a292e1164c00017a298214048fa000824511df1907b50f95c23e000e61aa4d45a03916b1ae5c078a8822a6880000a1c65850381f2f8000b60b5106934b4a800da18c561f30000bd369b60fa2d93ea584e610c000002521e8139640007c0001b73e8948000000ca5d85b80023c3a8000d94fc3e472a3705aa24001d04be000350a80728e1430571405eca801b000a4c851214103cca399a0422ed028550840a8000003c86eccd8000b600000015000048d393f49c5807e82b506238f392b0061388205612a7e0228000760013e12d03a3086800032a698089033061f0cc8004b8769100ef0000000027b4163844b0f83821fcb6a6f2e47b12c89b0007ad07800000000af87845631c3702e1461d92f0000000010704b000000fc800000200c91583563480023a44aa385997400053cdf8cc000070e02220ce450eb89a3ec6f00008c0e20a10b8701700202e1e24aa878f313b3d40f8651b04ce2ad43986494000ad92c4cc650e780744e0007387526a2f85483d0008fcf02690000dc621fd3ba17cc2a710003613b959046a54bba3947c458248dc17a6d0d7052060358f90994182c01e25a1e8a08760003d022400000000624c5000000000ef0040040502c070180401c000042c0000302c00030130080300801010040240201000018060180107c08010000100100c0000002004030000904c000041300404000010000202c040040504000020000040b0001400c0f124050100402016010020000201c0000c030000503c0101c0001c040180201001000090080000820000140040502c020080501400018050100200801010020500f00c0c00009010030040900c0205400014020a01900003020000440307011040010180c0000907c0201c0c0300a004080000500c0702809008060880602c090000e00c1e0003a014150401c000050d40500c0d0100001807008010c00601809008010041000007010080100302c02008000040000803054080000107800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0xb190c00078d232400006d4000000008701d0ce0006cc000612700013200010e2bc780910007dd009ad0bc0586d9e12f011849a961ec88c209274768a0ab99d20a1988004010c8690b0a5348018020d31ee2f0cf05809e64c8883435e8502610b50a8d01895307e3c8b2a924a232cde85409076c0022d000350e32351921ec000000484f9198004048f00007900068ca6a6c0fc0000014400086407218000925178362dc71ce6a4f52e000af12f00046c89a0d24c4d02825d284818c42940d87e8a714000014ca528d1c82908809802e27c5f8002a47c53001a212840748a7232a04c69324585e4008ae3fe5207597e3005a87716622e234b9a362de8c4b393a19a5f52b15d2549409194651e96c2c9e515a98d3d0b9342000ea00b10450c8e89c1fea2c839c81b47d4600001bc84ce198b0041cd3819f5225c4341814244184b92011e2d007a2444265cbf80018a63934000384660e58d13fc8f4d00001da745420c64881d049000026000e4800000854001d84140000000048e000c78cf2484dd131121424c434996000088dd000202304700000c8000c127239486d358350ee2402391c3d2950e90d50006b0ad0fb1c40c8910c300a95cf702c1025044e9490b41806f8e6000030000000de0007a8623708a40000004a495191512342201326e4846c8c8a1d13c98414a1123000000279000694080fe3b88a9020b2000000ea81800061c1c0005203a09c8142048c1310004ca7640f1ef318000d4a4
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x52fa0009e9cd2566a06019028e3540001b3be340499b53560007986021e440010000be2bc1c2053da0001c8eb29e59cbc043408000419ee0006b86492a1c2414000000006e90609c04e2747b87b1fe548548000005e40ca023e4468ea0072d21703f9d5066068b307637e28c042130aa0005a12f4324888e0e407a5905296c19a000000fb00002cd9800000000000952244dc6901e0004440018c1d0000001ff0004cccc93b31c3d82083e0ca430000000006484f1db2a819c000003fa000e3800000000a61080000c50b0aa2c4000a4000000054a693a1bc3c82d90d1d8000001600927645a9732e05f02d0003762f00298f1ea000531590500b4c380016c824bd9142da1c8618ce038044f515c18a78c068000005083080007e3300004a000004090081300c08008180000a0000f01c0f0000e0000007803004050280300c0700024000000001c0080400008000020000002c00000020180201007000040540800c0400005000150440b0040001405000000040100c0e0100d0040a06805020000080201004004010000500407004020640b000030400001400018080780000c0700000044010600500003018010182f0100700400004000100000002000050081401003028050200000c0300000010050080d0180404c020081100c0000417000000040b00c050140100c0303000024010140201c010180000805018030326f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0x749681d400010800382000001cc3b8860cf15a0002a0cb0000001783e000000000f81001322390380013034ca080005e0c84002930c08cb880012c000431d20d87380005024c000000871907cc639b222c27cfc0570a67dc59a110ba2b400094310318771941428542692e2a0190e11ec3d66b4000002b60501b177134038af0542320000000006a6f42b000054000001a900000000000000000050001128683a801000090d8800196000001c31c03e4081810000009c03a0f085c0000038847c4b800414244340000001880000015c0600195f0e61301a1b8344398899981740000000000000000000000000000003145fc001d61ae6d0fe214000000b08a43de8180011e35e74000000000000ff0000a2000b916f1ac800001e21e25d4c007427c4c8949581a86144106f3ea07cec0002920006898b3d222c83816312000db19d17a1a4021741be000000000a45f90782020c778e40003e2374bd1d1000514091462963943719a420098fa10210a000a51a012050c719830005b80019321c074000002ca42400130000000460001024a05d9aa0f4574ee8460007d88b9273081dcaaa0e0f248c5b8003ca12c7d12038a6dcd800000029cd28000004d4fd9150004d8d08001b082c4d93c2064c40014e2ae23c220000806f0d30001fc328001e8000474001ac08e46c679be0fc4282406a0001c4d186b0000f0000001082b0160db3361608594000065c380001f04d0ab1b932269c061cf2023880002525a39c0008d09e4fceb800000108f380041a0000008a1407903e8b20da0010900000072c00006380634920fc0cc310000ab0004945c982012000a20ed1843bd018a21b4728000fd1e87249c96b0006900983b09c2c0319213c07182c9da1702f8000302a28206c99c05c3045f9041b805ccaa013a6460bb03712458cfd02233e0ac000b13c254c9616a3cc000078001e0220fc84
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x60000735600000254e44901200800f0005130403045ca2c31404001818400e4000098318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x5a080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 797)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 2 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 3 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 5 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37437
namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x1c0000003c230000000009f8b208225a0f000240000000bc80000022c7c8004ba000000003e00001a800000000078004102686800000048800000000001218002940012d0001d459c1a1242aa00007000000710001a70246bc000001680000000021a8f4c680002e0004386a1480011a80015c845180000007a0000000003f8000160c80007d0004a06c0000000000000000046c68126a1c2902dc6a8000000000000000077c00224000160cc0000000005e9a8130589020901225b85191a00026c730000000012b0dd19a000a093900054c0000000041415800000000e4a8523a00000000184904fa800000000180004be32c0a9022aca40990f839e23c8b27f0181cc000ff000000ad0000000011b8000b20000007f29e524000b6000000000000160000000033c000001b80003d000000000000000cc4da68400000000001029920003582a0000000010692f3f8798001a930c2100026c43c0000014c00091c240000000010c85a000000470e5000918650ad0340013980a0f60013e17e000000f28fb304320001a50da45400225000000002922fa9e4db00036483811000080000f200027c000000000c6780198004ee084000d20000009e9732387503e97012c0012480000080800000000000af16a00000000110000000fd800000000fa000000880f706e182460001c808c000000002101e8000000007fc000000ec0000010c224000000000000006280000000000000001002000000000020000000000e0040400000000000802002000038010000000000300401000001000000000020060000000000000000000000000000000020040000300000000000006000008000000000100000001c000020000100000000200400001004000000000000040080000600800801000020008000020000000200a0000000200000400000004000008010020000200700200c0280100000003002004028018070000040000100000000800004000008010000080100000000c00803002008008040020000000400000000800008004000010000000000100801001003000000008000080040000100000001801000008008030000040100100400c0000000400000000000000008000060000080700000002001000010000020080100080300a00000800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x1740000000000000000000106000000000262bc00075000000000000000000000000000000000000000128503686f0490004b600000000000000dd267000390d5000000a500000000000012000286858000e8000000000001fa8ed1f2690000000000000081c8380000059400000000000000620000000020300000000000000001388002c600000000000000000003980006480000024c000000009d4788000002c4290004203a40016d00054800032000001090000003647b000000000d58b82d6000000001a6650000431e0624000310060011c8002ba001460000009540000013ca2c000000d02ac00000000001288000000000000052a2fc002334a80000023c09c9e92280024a9980004c1c4000da8004dc000000000000000022700000000000000000bf800000000000000bc71c8a28a0006b4000060005e000000000000c80004540010d80050415c00000000000000002a2664001880008b05099f0222c8000c02843b800000000888002230001c0000000ba000250780b88a400000000000000ce000000001ed4121f8000de0323454428700008c759691143800028f000000e18003588c8ed8003ba000800000001d02280038c0000000000000143000000770001d000012c0024a3b08680001845c000000000000000001d35c4d80008d0006141da440005e8c6056000000001b9232668222960ee674000c600013400000000000000004a49bc448000ce754e59613b2000002580004ec5a80049c74c301ca2b0000000000000000000000000000000000000002780000007794617600000000000818002010006049514b1c6254001f23ac0000000000000000000000250c00001ae800cb02d12e1ac3c8000006f81524c3f0000000001f8000f3a0b0007140000004c0b0000000000000027b052a0c0022622240c178000002b0981292ee000fb0001ce000790000005380000008e000000005222049d0384fa908000000be93c000004c400132000000000c2000000000000a600000000000000a04000004b2000a2000256000599e94428ac000be000000f9a6800036cf58f71400a000000000000fd20f000000cb9ea0a600000000000218c89280005b03e000000000c50000020008f000000021468aa0008e0000b000000093a172e4000b78000000f40000000048c000000cc7382a9a300037c00000008708289c10000008d80026a0012e0004301c8000004e8438000003f200000000000830c3a312ec000a68004d400000000000000f109c3c6000cd8005260000028913a0000000022e00000000000000000000004b8762534bc4180006c0003ccfe8650000006a000000000001b32142e5240000000000004f2400000000000084c000690000000000000042c0f8002120000000000000080a760007dcd200006e0000489f00
  | 4 => 0x34c000000882780000021d474124001952b6000000000009c12b80000a0006c10f31c5f00e1de3a4384308da074000df800000000001f1000000a2a0a3068b40d8000000002083e28e0001c9740005c40000014e4cc00261000000e68020000000013f5080000003f338000001210002a000157000000ff000000000e001032649800000000001140003a2a00af8000005000000000000089a6b000000ed000000000b31e12f60002d8002a8540f6000270200002630000011f8002d00010a21f45e688000c452e00063800000000000000009c86e10400000000000000000001593ae000000a249609c0000042a4c40000000000000000000000000a5000000000001786dc000000000000000000000042820000000001b100000000160000000000000de000000000847bd1a11f000001300000003d4000000004b000000152000000002ea62c618000004d09b80001a000de8000000d87680019e0b947071000994000000000000000000000000099000000000142b8000000000006ec0018f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x3240b01a20f17a530001d90d079cbf093000000608de1c0000ac8b9200000280001a00cc000aa3a25807e000246000000003982d47a94f19a0005b0df3a40a0221b330e6185c0a62b455c2b024038014fc8250b032840800000620f7800312538001172a0710b480000043c10800000798ec1c20c27707d0991886583e1242f042cb58000008383708e000690000000005dc0000020e0000000038e450a981a25e270bb086158258fb08d0520000000037a74c7580021c70c0006c3e814cb887e0b2314ff89f000000bd8000000000004d3ea0002a000208000e58360281dc8619e01c268e504a000220001153600001a8000000000000021a000dc00018e0000507538200000a13000758169a30004cce31da00052c0000017e040000000000141700001000000200001004000060100000c04000000040d0040102800010050480000c0b0b8050140501c00000100140a004200040500808000000480400c010240100c00000100000501c2500000018010502200005000000000400c0103002014110280004000010090040b0100406c0f01401004000140c02c0500804020010800500800004090180300c0002c000040b03c06008000000300002024010381a014030005d00001018100440100808004020000d008010900000400008000000700800010000000203c140080e0540101002000020180007c060380d0026f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0x4b800000000c0a0b15a77cca15f316000000d30002400c0033d64582b80000038426000000560000ba1ac000001e5000474000000000006013b000260000002c27f4000000003f8000ae1da7a4a09ec256000760002e4000000cc3145e48194842a788000003006f8000000000000000030a6ec002111a21906d20223258c2d08b2dc6b4b99983364f4af1b6250170069ea0a4188021b907e7c48c0dd33a5b49b9db23836cc800028c2903182603e000841391ca38c000003a06a0a194a08a1240007d000000cd01d0000006e1640f0000001700007cc0000017c804f08f6000000781931b02dc2fa060006bc4618411e000000461c4000000000007910c8004100010c0670003fc950f90000bc4d80016656c5d800304810488303407008f1300de1d0f69a90464e8d8905222000111a723e29c618af0e2000fe2102248306a8f726406c420322342488083c08e5001506b2847810299140621cee9c54005f10698f1ce2ac2799742e694200002ca174f7042128000a29b41140010a0003441c8002070006dc7998d0004fc030550004f0000a5000198048b20f459c4490a0e64f8000000d40005114409c7e8380001407782416c2a22c0ce03a0263c86787f02e1441d8f42b8180158822ea4d8ff12c3ee031049211a80dcca9d70d2000000f835678ccf9ac1908683c80f2d4574e7126162524901133062f09497428e5fc0a97a27084800000364588000c23906d4b78ee02c3187d9680044b8939bf0004d49105e3a86e8f80001de3f4000430004401c17d3540008491b000000038003786b813925106000d3012192044000b41b2064a90e91cc0c40007b0da6840000039e858b31d520c2746b8080ec55051800000390fc18e000724058000000f4549022620000005b1a4284ab09503c3a0968a839a630cc8851967a0f902e19c19420a0a13c0e4a683e268200788ea096554fd82
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1802c055100100a00001300001600000000039401730000024300000548000000f207000000000602350100020001020058318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x21a080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 4 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 2 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 3 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 4 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37437
namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x210058018c300c831c3b38d8401027a0007800020026b83f2a0c9242843a8a01b8000b800200000472c3260029400241d49a5544025806a6643c660222861513187cd8d2a00000000000000011830e06085010000102140008e0214000000405fe54017f55005fc54017fd0c03fe43017f50c03fc43017fd0805fe42017f50805fc4200ffcc801fe32007f4c803fc32017fd0405fe41017f50405fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc21017fd0005fe40017f50005fc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2001bf98e10007fac708002fd6384015fe31c2001bf18e10037fe870802bfe438400dfea1c200aff10e10007fec508002ff6284001ff3142007bf98a10007fac508002fd6284001fe3142007bf18a10037fe850801bfe428400dfea142006ff10a10057fe6508003fe3284001fe994200aff0ca1004dfac30801bff4184007ff20c2006ff5061001ff8830802bff3184007ff18c2000ff4c61001ff86308003ff2184001fb90c2003ff88610007fa430800ffc2184001fa10c2003bf98210037fe810801bfe408400dfea042006ff10210057fe6108003fe3084001fe984200aff0c210007fe4108003fe2084001fe9042000ff0821001ffe2108003f71084007fd8842009ffd911004dfec888003bf64440015fb222009ff99110015fcc888027fd64440137eb222009ff19110015f8c888027bc64440055e3222009ff9511004ffaa888027fc5444001ffb1a2000bfd8d10007bec688002df6344011ff31a2001bf98d10007fac688002fd6344011fe31a2001bf18d10007b8c688006dc6344013ffa1a2008ff90d1004ffa8688023fc4344001ffb122000bfd8910007dec488002ef6244001ff3122007bf98910007fac488002fd6244001fe3122007bf18910007d8c488002ec6244013ffa122009ff9091004ffa8488027fc4244011ff9922000ff8c910007fa6488023fc3244013ffa0a2003ff9051004ffa828800ffc4144011ff98a2003ff8c510007fa628800ffc3144001ff90a2003ff88510007fa428800ffc2144013ffa022009ff9011004ffa8088027fc4044011ff9822000ff8c110007fa6088023fc3044001ff9022000ff88110007fa4088003fc2044007ff8822003fec4110007fc2088003f61044007ffb202003bfd901001ffcc80800afe6404007df3202002af9901001ffac808016fd6404007deb202000af5901001ff8c80800efc640400bff2a02005ff5501002ff8a80800fff63040077fb182003ff98c1000dfcc60800fde63040036f3182003ff58c10005fac60800fdd63040016eb182003ff18c1001df8c608017ff4304009ff2182005ff50c10027f8860800fff62040077fb102003ff9881003dfcc40800fee6204001773102003ff58810005fac40800fed620400176b102003ff1881001df8c408017ff420400bff2102005ff5081002ff88408013ff3204001ff1902000ff4c810027f8640800efe6104007ffa082003ff9041001ffa820800ffc4104007ff9882003ff8c41001ffa620800ffc3104007ff9082000fdc841001ffc420800ffd2104007fe1082003fd08410035fcc008017ff400400bff2002005ff5001002ff88008013ff3004001ff1802000ff4c010027f86008003ff2004001ff1002000ff48010007f8400800fff1004007fb8802003ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3bf64480015fb224011ff99120015fcc890047fd64480237eb224011ff19120015f8c890047bc64480055e3224011ff9512008ffaa890047fc5448001ffb1a4000bfd8d20007bec690002df6348021ff31a4001bf98d20007fac690002fd6348021fe31a4001bf18d20007b8c690006dc6348023ffa1a4010ff90d2008ffa8690043fc4348023ffa124007ff9092008fdc8490047fd4248023f6a124007ff10920087fe6490043ef324800fff1924000ff4c92003ff86490043ec3248001ffb0a4000bfd8520007eec290002f76148001ff30a4000ff58520007f8c29000efc6148001fa30a4000bd1852008ffe8290047fe4148023fea0a4011ff10520087fe6290003fe3148001fe98a4010ff0c52003ffe4290003ef2148001ff10a4000ff48520007da429001ffc2148023ffa024011ff9012008ffa8090047fc4048021ff9824000ff8c120007fa6090043fc304800fff9024007fec8120007fc4090003ee204800fffb204007bfd902003ffcc81000afe640800ffeb20400ebf5902003ff8c81001efc640801dff2a0400eff55020077f8a81001fff630800f7fb184007ff98c2000dfcc61001ffd63080017eb184007ff18c2003df8c61003bff430801bff218400eff50c2006ff8861001efe620800fffa104007ff9082003ffa841001ffc420800fff9904007ff8c82003ffa641001ffc320800fffb084007ff9842001dfcc21001ffd61080017eb084007ff18420077fe821003bfe410801dfea08400eff1042006ffe6210003fe3108001fe988400dff0c42003ffe421001ffe2108001f71084007ff4842003ff8421001fec210801f7f300400effd0020077fc801003bfd400801dfe200400dffcc020007fc6010003fd300801bfe1804007ffc802003fde401001ffe200800ffd1004007ff48020007da401001ff92008007ffb262003bfd931001ffcc98800afe64c4007feb26200cbf5931001ff8c98800efc64c4019ff2a6200cff55310067f8a98800fff63c40077fb1e2003ff98f1000dfcc78800ffd63c40017eb1e2003ff18f1001df8c788033ff43c4017ff21e200cff50f1005ff8878800fff62c40077fb162003ff98b1003dfcc58800ffd62c40017eb162003ff18b1001df8c588033ff42c4019ff216200cff50b10067f8858802fff32c4001ff1962000ff4cb1005ff8658800fff41c4007ff20e2003ff5071001ff8838800fff31c4007ff18e2003ff4c71001ff8638800fff21c4007ff10e2003ff4871001ff84388033ff40c4019ff206200cff50310067f8818802fff30c4001ff1862000ff4c31005ff86188003ff20c4001ff1062000ff48310007f8418801bff648400d7fb242006ff99210015fcc90801bfd648400d7eb242006ff19210015f8c90801bfe548400dfeaa42006ff15210007fec708002ff6384015ff3
  | 2 => 0x30007fec318003fe618c0077f30c6000ff58630005fac318003fc618c02dffa0c6016ff906300b7fa831805bfc418c003ff98c6001ff8c630007bc6318007fd318c003fe18c6001f70c630007fe4318003fe218c001fe90c6000ff0863000dfcc11805bff408c02dff2046016ff502300b7f88118007ff308c003ef9846001fecc23000ff86118007f8308c02bffb226015bfd91300affcc89800afe644c02bfeb226015bf591300aff8c89800afc644c02bff2a26015ff551300aff8a898006ff634c003ffa1a6001ff90d3000ffa8698007fc434c001ffb126000bfd8930007fcc498003fd624c001fe3126007bf189300affe8498057fe424c02bfea126015ff1093000ffe6498007fe324c003fe9926001ff0c930007fec298002ff614c001ff30a6000ff58530007f8c29800efc614c02bffa0a6015ff905300affa8298057fc414c003ff98a6001f7cc53000ffc6298007fd314c001ee98a6001ff0c530007fe4298003fe214c001fe90a6000ff0853000dfec098057ff404c02bff2026015ff501300aff88098007ff304c003fd9826001ff8c130007bc6098007fc304c003ee1826001fe0c13003ffec99001eff64c800fff3264002bf9932003ffac990052fd64c800ffe3264007bf193200a7fca990053fd54c8029fe2a64007ffd8f2003dfec79001ffe63c80037f31e4007ff58f20005fac79001ffc63c800f7e31e4014ffd0f2009ffc8790053fd43c8027fe21e4007ffd0b2003ffc859001fee42c800ffea164014fb50b2003ff8859001fff32c8027f79964007ff8cb2003ffa659001ffc32c800ff61964007ffd872003ffcc39000efe61c800ffeb0e4000bf5872003ff8c390053ff41c8029ff20e4014ff507200a7f8839004fff31c8001ff18e4000ff4c72009ff8639001fff21c800ff790e4007ff8872003ffa4390003ed21c800ffe10e4014ffd03200a7fc8190053fd40c8029fe2064013ffcc320007fc6190003fd30c8027fe186400fffd922007dfec91003ffe64880057f324400fff5922007dfac91003ffc64880057e324400fff9522007ffaa91003ffc5488001ffb1c4000bfd8e20097fcc710006fe6388001feb1c4000bf58e20097f8c710006fc638801fffa1c4012ff90e2007ffa871004bfc43880237eb14400fffd0a2003ffc851003ffd428800ffe2144012ffcca2003ffc6510003fd328800ffe1944000ffd8620007fcc31000efe6188001feb0c4000bf58620007f8c31003fff418801fff20c400fff5062007ff8831004bff3188001ff18c4000ff4c620097f8631001fff2188001ff10c4000fb88620007fa431001ffc2188001f610c4007bf9822007ffe811003ffe408801ffea04400fff10220097fe6110003fe3088001fe9844012ff0c22003ffe4110003ef208800ffd9044011ffd912008dfec89000
  | 3 => 0xf3244203ef992210157cc91080ffd64884397eb244203ef592210057ac91080ffc64884077e324421cff952210e7faa910873fc5488407ffb1c4203bfd8e2101ffcc710806fe6388407ef31c4201b798e2101ffac710802fd6388407eeb1c4200b758e2101ff8c71080efc6388439ffa1c421bff90e210e7fa871086ffc43884357eb14421cffd0a2103ffc8510873ee4288439fea14421cfb50a2103ff8851086fff3288437f79944207ff8ca21007fa651081ffc3288437f61944203bf9862101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fe98c4203ff0c62101ffe431080fef218840ffb90c4203ffd822101ffcc110802fe6088407feb044200bf5822101ff8c110873ff4088439ff204421cff502210e7f8811086fff3088437fe184421affd91210d5fec89086bfe64484057f322421aff591210d5fac89086bfc64484057e322421aff951210d7faa89086bfc5448401ffb1a4200bfd8d210cffcc690806fe6348401feb1a4200bf58d210cff8c690806fc6348435ffa1a4219ff90d210d7fa8690867fc4348435ffa124207ff909210d7fa849081ffc4248433ff9924207ff8c921007fa649081ffc3248435ffa0a4203ff905210d7fa829080ffc4148433ff98a4203ff8c521007fa629080ffc314840fff90a4207fdc852101ffc429080fee2148401ffb024200bfd8121007fcc090803fd6048401fe3024200bf181210d7fe809086bfe4048435fea02421aff101210cffe6090867fc3048407ffb204203bfd902101ffcc81080afe6408407feb204218bf5902101ff8c81080efc6408431ff2a04218ff550210c7f8a81080fff63084077fb184203ff98c2100dfcc61080ffd63084017eb184203ff18c2101df8c610863ff430842fff2184218ff50c210bff8861081efe620840fffa104207ff9082103fdc841081ffd4208431f6a104207ff1082103ffe641085fef320840fff1904207ff4c82103ff8641081fec32084077f3084203ffd042101ffc821080ffd4108407fe2084203ffcc42101ffc621080ffd3108407fe1884203ffc842101fde421080ffe2108407fb1084203ff4842101fda421081ff52108407ffb004203ff98021005fcc01080ffd60084017eb004203ff180210c7fe8010863fe4008431fea004218ff100210bffe601085ffc300842dffb246016bfd92300b7fcc91800afe648c02dfeb246016bf592300b7f8c91800afc648c02dff2a46016ff552300b7f8a918006fd638c003ffa1c6001ff90e3000fbc8718007fd438c02deea1c6001ff10e30007fec518003fe628c00f7f3146000fb98a30005dcc518003fd628c0017eb146000fb58a30005dac518003fc628c02dffa146016ff90a300b7fa851805bfc428c003ff9946001ff8ca30007bc6518007fd328c003fe1946001f70ca
  | 4 => 0x86ff644c843ff3226402bf9913210ffac899086fd644c843fe3226402bf1913210ffca899087fd544c843fe2a26407bfd8d3200ffe8699007fe434c803fea1a6401ff10d3200dfec499087ff424c80fff2126421ff5093203ff88499007ff324c803f79926407ff8c93203fbc649901ffc324c80fee1926401fb0c932007fec299002ff614c801ff30a6400ff58532007f8c29900efc614c843ffa0a6421ff9053210ffa8299087fc414c803ff98a6401ff0c532007fec099002ff604c801ff3026400ff58132007f8c099002fc604c843ffa026421ff9013210ffa8099087fc404c803ff9826401ff0c13201ffec91880eff648c407ff3246202bf9923101ffac918882fd648c407fe3246203bf19231107fca918883fd548c441fe2a46201bf58e3100ffe8718807fe438c403fea1c6201ff10e3101ffec51880ffe628c40f7f3146203ff58a31005fac51880ffc628c441ffa146220ff90a31107fa8518883fc428c403ff9946201ff8ca3100ffa6518807fc328c4077f30c6203ffd063101ffc831880ffd418c407fe20c6203ffcc63101fbe6318807f7318c407fe18c6203fd0c63101ffec11880ffe608c4017f3046203ff58231005fac11880ffc608c441ffa046220ff90231107fa8118883fc408c403ff9846201ff0c23100fb8611887fff644c43f7fb22621fff99131015fcc89887ffd644c43f7eb22621fff19131015f8c89887ffe544c43ffeaa2621fff1513101dfec698807ff434c403ff21a6201f790d3100ffa869887fdd434c403fe21a6200ffd8931005fec498803ef624c40177b126200ff98931007fac498803fc624c40f7e3126200fb18931005d8c49887fff424c43fff212621fff509310fff88498807ff324c403ff1926200f78c93100ffa6498807fc324c403ee1926201bfd85310fffe829880ffe414c43ffea0a6203ff1053100ffe6298807f7314c407ff18a6203f78c53101ff8629880fdc314c403fa18a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c09887fff404c43fff202621fff501310fff88098807ff304c403ef9826201ff0c13103ffec99081eff64c840fff3264202bf9932103ffac99087afd64c840ffe3264207bf193210f7fca99087bfd54c843dfe2a64207ffd8f2103dfec79081ffe63c84037f31e4207ff58f21005fac79081ffc63c840f7e31e421effd0f210effc879087bfd43c843bfe21e4207ffd0b2103ffc859081ffd42c840ffe2164207ffccb2103ffc659081ffd32c840ffe196421effd072101ffc839087bfd41c8407fe20e421dffcc72101ffc6390803fd31c8407fe18e4207ffd832103ffcc190802fe60c840ffeb064200bf5832103ff8c19087bff40c843dff206421eff503210f7f88190877ff30c843bfe1864203ffd922101dfec91080ffe64884057
  | 5 => 0x3910018a9821e080009480000fcc600e0001c70001e74628890ff810c0180b00401000002006014000000040040100000c0380180600003012802004000030010400080280001a048000000460000080d0000000480300409401001000090028060260080800d0000180080001a0040500f0040880480300600c0480c00e060000000060000400500404c018040000140b00e00401801003000008008010020040500000600c01002002018000010040040000000c0000500d0060041281200804c038000020040280b00c0080300b0c6004038110100180f02300005c0800200e004020030300980201d0500141280200000c1300a0560000700100200c0381000a00c008220060000281501c0680080700004c1500301a0040080001e060000070020603000101c0400080004010400012026014018000020000a80003a0100100000401003800008048008270080000380000c0000100008e0100380000001403004006004018080000000380200c00c0880001e00c0400000a034000010140080000202e0540000001002c048000120340000204600c048000140080000200a000040020180080980100001800010008000000010480180980400c01c000000080240500103e000000040000081f0060000000400101a00401801000004010000260ac0a00500a0700202300602400800014000028080080000780d0240080480000a0140000f00c0b8068000020280680e016000000170000680180000000c000070000400280300003c000000340480600e00008401802004020128310040980d00c02200001001004070058200060000702800e0180100b01c0403201703c018008150100b40000c006014068260040c4010020060580581103c174000000020000580600a00400814028000010000080000880700e060048020180080080100000408003020000038050800040080101c02401001000004030040140080181103c0080080d0000100401e008090018120140ac0900603a004018000000001e8010060000080200e0100000100a0500681d0120440880300e00402000028000140020300080800203ffec91901eff648c80fff3246402bf9923203ffac91908afd648c80ffe3246407bf19232117fca91908bfd548c845fe2a46401bf58e3200ffe8719007fe438c803fea1c6401ff10e3203dfcc51901fff428c80fff2146407ff50a3203ff8851901fff328c80fef9946401fbcca3203ff8651901fec328c80fffb0c6407ff9863201dfcc31901ffd618c8017eb0c6407ff18632117fe831908bfe418c845fea0c6422ff1063200ffe6319007df318c803fe18c6407ffd823203ffcc119002fe608c80ffeb046400bf5823203ff8c11908bff408c845ff2046422ff50232117f88119007ff308c803fe1846401f70c23210ffec899
  | 6 => 0x1904270fac0009680011c53101300007884b098a2093a5dc96101682583c80000023c0000228fa9adc0017140000004c8000cc96a23905806c8c89bd8000001e6e0a00009612100018d5ab0a900012010409b4002109fa1129aa9e183180000004a0000d78010001b10000d698780014d20c8001e00df00013e064dd00b581c8001c94a69af8804c98001a545922908147e8000ec9be851d0f1ee0499548d9c0004ec3a0000201894aad2808c96714c1448d08970de1b61b48af11c95e63d1739c405f043c0017803f0000f9983000129c9ac001ef4000e482a12adecdee5b7217d279bacddca281cc4622d9f00eea0182ea18c001d3a0dd6f83b9f98bb1138bf1500ac1521db1e71f19b9850894e3d59d4278f4a2a045823086a0c1f1c13d2b84fc1705c0dc2438000000001fc9a183853f0001ca8000000fdc001b8800243c84c6a0000001b64111d80db40003300000d80000011d80019d0bc04c081229639c6e8e200000006380010c1a51d50cd47f9c807c174800113c000000001edc002041a00000c19759e490a80011a00f5315768000001590001061b6d0fcb0220e1711ce3e0e312a9f68c51eb1f38fda0d50b1fb032d9a99ce37034a142189330f1524897929148e3258b947c2b8d5174dab5cb8c794619691b00006b02a850cf793984c5a98000be9e90d8c8f9e608b4e9213074e00889c924000f600097042603290c98519c5fd8851690b21e1438107c158cf0d19d35d29870b30a7223c8f1bb8419eba2260055e86b5f10dcdb9cb709d0b403e9d25668cb92c997136c001518f887a1354030a61c21ff42f0325379f2cad0e69cbd8e131a2480000000002196d1faa2112397b073800227c001e999bc000000f3064471ced9329ac48296ad541505488061ad9a484e5372050b643b1221c8c2d88c0dd17f9d94000000000f022689a800000211926800031c0001200008a4d014285e1471978500000001a09c30000000000000000000000000a48000000001fc00015780000012f1f14000771e100019803140008421e1d9110400000222c00135e0fe0445fc2e03789b80d1c4c00116800189cfd1ef8d04529dd1f28268a9c90880c3cc000f422014a2001d6188170d58cda87b8a181615658acff1fe90d8b3557d789309b78b6a3081488812b11a95990b9508438001d8d4b80021b8000000cc40000000015e0000001d842202b0420c097711b895a3812a63a88e0070c41e59da138a185aa0f45d68000b5c00029000094400140105924209c0680010e89f2084e9c0000011196e00007b4fb472e1a8c902a6258da5b5890e2b0ab9b94c264160f4f0c5380007d1f45539760000fb0a884d60aa1a20494e1a70568dbc000029258000000001689fb8e819e18e5575d59d7c749ac87b11e0b45b21235891ae800212c808d31f79
  | 7 => 0xa1215c86ace59ba0001ee930d805db84a83746495c63fd8fa0f82c23314c97ddf56204da0cea2d0fba28102408cd712898ed7a8558a50919b91898526168bb91bc4f40587ca28d589051d48f51c9026d8615b5aa4a2dd1860ca3e058690718b801a161e2a8898a1119cf91c5deecfe97b5df03f81390208320120b22ccf4c2100413ce398f35631089838de96804693f8001250f21351b74084b3c002098001a7a1485b0e28fd5cd0000001e5c0007104ce0ec000510ca87300000000022200011517ae2c52f956c7445064260f17d901e1514080a161a1f14d8000cfc07c04859dc111dd6b8d494fc2c93bcb4d114eb9a20aa4000154af8178ec1e791792c13c0b88c82429bf48a90f8000cd8ef800139df700f8cd1e0597ce40001bc11a5a890314690145d0714a21ba49e1ab81c0a38d615f16142f9b8dd562bc398c3536195a3b5ed1d1d98632971cf3cd800c000059a3523ba401bf00014b0002230bd15c19b1f806097023c8a59c588ad5593b0000000df8dd8515bc8254d28f116598b1f2160e03e1914300000020e400100c00112400000000035000083c000001fe15600010822645951e9909bec7fceadf24560001ce13480000013657c8ad4000bcd1306c0abe234aa97e54e80000003c0e507e0548b18000640fa000000000000172d6059f0001c893ac000bf8d840000016b1800859305531a4c4e800058c001be4001a5c001a321fc18242cdac3093a1740000000bc9cf80000009b0d90240914668dba081270038300c31bf83d1cf11588d0e3de39b804d8c680005a80005840020ce300f70550001f420298115817bce71f48ac5e2011a3f21c065cb61295bdca822858de379c08fa5e29dda175510b90601ca4fc4bc5d4e2e0e39c51d31b7d888c701d240800025d5d8cdc188ea8000bbd180cc11006a9cb14a80017a037c360910b545c8f81abe09158400170838d931e68000980a996c93c4721a58bd80023d8001ec00011ac000699190001938000078000d11a40e00e340019e8ed08700000000018594f57790d1b298f0a360c46e0000001491f34000001d700013b40022989da218f08428b791c22b9140518000000001ba94518c9f58250b29988780000000471528e2ccecbb6094000000088820000000001fd00e80003c5394000000144c28cf96d8001b5000229d475bbd2e9991048371009c19f90481aee368619b32035ad555120999e2c892cfc8001751569ac09c4388001998dc87da3a4541de80019c1e0c7089f90983395ec0019a4e24b09d5c0001923195d1e1cf25f31d101f8950b2d900f38ea167a1619a0849600000001019d20ad89c17ed1d00ba2e8620000fc1160001c6910e1c92619d8a30400000001340001fedf4c6ba43000000044c0001b9648f58435071a821e90a1cc1b0a138000790ee09be4340000
  | 8 => 0x16f233e32d620de5721230001de138cacd4fa3101e8001ed80000002d225c0012d80021287ad8280019b80014852a04b8779a120200014980021800015f8390ac80022619f9d3e3422786805d87560d879dc28d9a100ccddc076208d7b8838b121262f14202989386f22759c86515dcfcd5a87a563990d08522c8e86718f51711f1068449095aac2958e995198e038ae1c980f14140017c42ac00132093ca9599400000014dd2dd405a092969930241c000b997e0741a39bd01a9224fe457a1f8ca238810a411ffd3d16b47681d96c431180861472611e241e800b11f9b01439b845723ac4900006d04f0d5996e3220780008ba0b8854a080015ac800001412338c58d941f0000000000000000d4131cc017919408a00018c0e09f8e0d1441f0994997548111cef04e000121c320000530fe1e88001e303d8cb1ad1ea8ab18fc3bc36a116215c54a24dd5c650901d5298604ce21781bc238e604500005e93d9ef1359c39039a9027428107940c150000729af18da229bb0e78000002288f697260bc0015ba3dc000ba80000023c40015d5f89ff9cc8000000001a613e98a400029d4f0ba1b400023e96aa3b00000816c1bc4d20f18001c9e2fa35873dd794041b0341b38001921660000001b688d887a1b1961e400000002862c1f600000001c5ae1144430000000e1912c0001e1122406159f8592812a0711880011b4000610654758000001c60735ea13383a8e11df809a419628c113fdd88c2d730c3e0304789023cd7d550de6452181d2d1f7c819ed45f94780520e98685b97d1755010fbd459ae573c751f51c49964d88000db027d5cc1417980017289e9570991a44940a78001381cd88b18184104896412e08884400182880003e20680018a2251a9cea55bd0e0105ff17cd148eb6238e89d0a3a0264c497ea27160a361d998151d40aa1d14193b9a295b13c9f7604c799135ec8a002486bc6897f04446586a6335369111cc44de0e0701a69cac199b18ce4861910208f2a198931ca06f840a088b511080016ea11028c0023f8000000a40b48b3a26cc38678aa1219e50dc40004f99180018d0be0c209a009574491c5887a800108c9362d580c660d38001be1da9ce80200003b60600ca40c8461d9199718f1d8415a1029f3c9201017104d24207f09c824c090eb0ae9bb49997c0630000b6d84800035a349d44d0d3a9651c78e98cf5cb5c016bc6d922
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf705881003cfd7058810006ef7458810006ee7458810006ed7458810006ec7458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef4358810006ee4358810006ed4358810006ec435881001eef715881001eee715881001eed715881001eec715881001ee4715881001eef415881001eee415881001eed415881001eec415881001eef315881001eee315881001eed315881001eec3158810006ee7058810006ec7058810006ef4058810006ee4058810006ed4058810006ec4058810006ef3058810006ec305881001eef105881001eee105881001eed105881001eec105881003cff768c81001cfe768c810004fd768c81001cfc768c810116be648c810006bd648c81000ede638c810006dd638c81003eee628c810006ed628c810004ff764c81001cfe764c810004fd764c81001cfc764c81010ebe644c810006bd644c81000ede634c810006dd634c81003eee624c810006ed624c810005f7714c81001df4714c81001df576c8410126f576c841001fb664c841001fb564c841001fd663c841001fd563c841001df672c841001fe672c841001ef762c841001fe662c8410126f562c841001fe562c8410006e562c8410005f570c8410146f660c841001ff260c8410054ff768c01001cfe768c01000cfd768c01001cfc768c0100b6be648c010006bd648c01000ede638c010006dd638c010005ee728c010005ed728c010006ee628c010006ed628c01001df6718c010005f5718c010054ff764c0100aebe644c010006bd644c01000ede634c010006dd634c010006ee624c010006ed624c010027d8304c010004fd76c80100a6be64c8010006bd64c801009ede63c8010006dd63c801003eee62c8010006ed62c801001df471c8010127e721c8010004ff768801003cfd768801007ebe6488010006bd6488010096de6388010006dd638801003eee6288010006ed628801001df67188010005f5718801013fe42188010004ff7648010005bf744801002dbc744801008ebe6448010006bd6448010005df7348010025dc7348010086de6348010006dd634801003eee6248010006ed6248010005f7714801001df47148010007e7214801003cff760801001cfe7608010004fd760801001cfc7608010076be6408010006bd640801006ede6308010006dd630801003eee6208010006ed620801001df67108010005f57108010137e4210801001df77644010006f77644010004f77644010007b7744401012fb4744401001fb6644401001fb56444010007d77344010007d4734401001fd6634401001fd56344010007e77244010125f67244010125f47244010007e47244010005e4724401001fe6624401001fe5624401001df7704401001ff3704401011ef6604401001ff26044010
  | 1 => 0x9010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006bc325901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315901001ebe315901001ebd315901001ebc315901001ebf215901001ebe215901001ebd215901001ebc215901002ebf7059010006be705901002ebd705901002ebc7059010006bf5059010006be5059010006bd5059010006bc5059010006bf3059010006bc305901001ebf105901001ebe105901001ebd105901001ebc1059010004ff7458c10014fe7458c10004fd7458c10014fc7458c1001edf7358c10006df4358c10026de4358c10006dd4358c10026dc4358c10004ff7258c1003cfc7258c10026df3258c10026dc3258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c1000cff7058c1000cfd7058c10024fc7058c10026dc3058c10006df7458c10006de7458c10006dd7458c10006dc7458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df4258c10006de4258c10006dd4258c10006dc4258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c10026df7058c10006de7058c10006dc7058c10006df4058c10006de4058c10006dd4058c10006dc4058c1001edf1058c1001ede1058c1001edd1058c1001edc1058c1003eef749881003eee749881003eed749881003eec7498810006ee5498810006ed5498810006ec549881003eef739881003eee739881003eed739881003eec7398810006ef4398810006ee4398810006ed4398810006ec439881001eef719881001eee719881001eed719881001eec719881001eef419881001eee419881001eed419881001eec419881001eef319881001eee319881001eed319881001eec319881003eee709881003eec7098810006ef4098810006ee4098810006ed4098810006ec4098810006ef3098810006ec309881001eef109881001eee109881001eed109881001eec1098810004ff7458810014fe7458810004fd7458810014fc7458810004ff735881000cfe735881000cfc735881001eef7258810006ef4258810006ee4258810006ed4258810006ec4258810006ef3258810006ec325881001cff715881001cfe715881001cfd715881001cfc715881001ef4715881001cf4715881001eee215881001eec215881001ef4215881003cf
  | 2 => 0x3eed741891003eec7418910006ee5418910006ed5418910006ec541891003eef731891003eee731891003eed731891003eec7318910006ef4318910006ee4318910006ed4318910006ec431891003eef711891003eee711891003eed711891003eec7118910006ef4118910136ee4118910006ed4118910136ec4118910006ef3118910136ee3118910136ec311891003eef701891003eed7018910006ef4018910006ee4018910006ed4018910006ec4018910006ef3018910006ec3018910136ef1018910006ed1018910136ec101891003cff768c910004fe768c910004fd768c91003cfc768c910006bf648c910116bc648c910006df638c91000edc638c910006ef628c91003eec628c910004ff764c910004fe764c910004fd764c910004fc764c910006bf644c91010ebc644c910006df634c91000edc634c910006ef624c91003eec624c91000cfc764c510006bf644c5100febc644c510006df634c51000edc634c510005ef724c510005ec724c510006ef624c510006ec624c510005fb704c510005f8704c510004fe76c8510006bf64c85100f6bc64c8510006df63c85100eedc63c8510006ef62c851003eec62c8510005fa70c8510005f970c851003cfc7648510006bf64485100d6bc6448510006df63485100cedc6348510006ef624851003eec6248510005fb7048510005f8704851005cfe768c110006bf648c1100b6bc648c110006df638c11000edc638c110005ee728c110005ed728c110006ef628c110006ec628c11000cff764c110044fd764c11001cfc764c110006bf644c1100aebc644c110006df634c11000edc634c110006ef624c110006ec624c110005f7714c11001df4714c11001cfe76c811001cfc76c8110006bf64c81100a6bc64c8110006df63c811009edc63c8110006ef62c811003eec62c811001df671c8110005f571c8110004fe7688110006bf648811007ebc6488110006df6388110096dc6388110006ef628811003eec628811003cff7648110004fd764811001cfc7648110005bf744811004dbc7448110006bf644811008ebc6448110005df7348110045dc7348110006df6348110086dc6348110006ef624811003eec6248110005f7714811001df47148110004fe7608110006bf6408110076bc6408110006df630811006edc6308110006ef620811003eec6208110006bf6484110036bc6484110006df6384110056dc6384110006ef6284110006ec628411001dfa708411001efb608411001df6768411001ef6768411001cf67684110007b7648411014fb46484110007d76384110007d46384110007e76284110146f66284110146f46284110007e46284110006e4628411001df6708411001ef7608411001ff36084110006bf7559010006be7559010006bd7559010006bc7559010006bf735
  | 3 => 0xf7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10054ff7158d10006f77158d1005cff7058d10006fb7058d10005de7618d10046de7618d10004de7618d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10156df6018d10157db1018d10157d81018d1003cfe76d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff74d8910014fe74d8910004fd74d8910014fc74d891000cfe73d8910004fd73d891000cfc73d8910006ef42d8910006ee42d8910006ed42d8910006ec42d8910006ef32d8910006ec32d891001cfe71d891001cfc71d891003cfe70d891003cfc70d891003cee76d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891013feb10d891013fe810d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891013eee71d8910006ed71d891013eec71d8910006ef41d891013eee41d8910006ed41d891013eec41d8910006ef31d891013eee31d891013eec31d891013eef70d8910006ed70d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910006ef30d8910006ec30d891013eef10d891013eec10d891004dbe7498910005bd7498910006bf6498910006bc6498910045de7398910005dd7398910006df6398910006dc6398910006ef6298910005bf745891004dbc7458910006bf6458910006bc6458910005df7358910045dc7358910006df6358910006dc6358910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004f77158910004ff7058910006fb7058910004fe7618910006bf6418910006bc6418910006df6318910006dc631891003eee6218910006ed6218910005ee7618910006ee7618910004ee7618910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910137eb1018910137e8101891003eef741891003eee7418910
  | 4 => 0x8210005f57188210007e42188210005bf7448210035bc7448210005df7348210055dc7348210006ef624821003eec6248210005f7714821001df47148210007e7214821001cfd760821003eee6208210006ed620821001df67108210005f57108210147e42108210005f576c421001ef576c4210145f672c421001df472c421001ff260c421004dbe76d911004ebe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110167bb10d9110167b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006bc32d9110006bf71d9110166be71d911004ebd71d9110166bc71d9110006bf51d9110166be51d9110006bd51d9110166bc51d9110006bf31d9110166be31d9110166bc31d9110166be21d9110166bc21d9110166bf70d911004ebe70d911004ebd70d911004ebc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006bc30d9110166bf10d911004ebd10d9110166bc10d911000cfe76d8d10006bf64d8d10006bc64d8d10046de63d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10046de43d8d10006dd43d8d10046dc43d8d1003cfe72d8d10004fd72d8d10046df32d8d10046dc32d8d1001cfe71d8d10044fd71d8d1001cfc71d8d10046df31d8d1000cfe70d8d1001cfd70d8d1000cfc70d8d10046df30d8d10045de76d8d1000cde76d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d1015fdb10d8d1015fd810d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1015ede71d8d10006dd71d8d1015edc71d8d10006df41d8d1015ede41d8d10006dd41d8d1015edc41d8d1015ede21d8d1015edc21d8d1015edf70d8d10046de70d8d10006dd70d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d1015edf10d8d1015edc10d8d10005bf7458d1004dbc7458d10006bf6458d10006bc6458d10046dc6358d10005ef7258d10005ec7258d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10044f
  | 5 => 0x5ee728c310005ed728c31000cff764c31001cfc764c31000ede634c310006dd634c310005f7714c31001df4714c31005fd8304c31003eee62c8310006ed62c831001df671c8310005f571c831013eef628831003eec628831003cff7648310005bf7448310065bc7448310005df734831005ddc734831003eee6248310006ed6248310005f7714831001df47148310136ef620831003eec6208310056de63d8e10005ee72d8e10005ed72d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e10054fd73d8e10056de43d8e10006dd43d8e1003cfe72d8e10006ee72d8e1003cee72d8e10004fd72d8e10006ed72d8e10004ed72d8e10056dc32d8e10006f571d8e1015ede31d8e1015edc31d8e10006fa70d8e10056df30d8e1000cff7658e10056dc6358e10004ff7458e10014fe7458e10004fd7458e10014fc7458e10006df7358e10004ff7258e1003cfc7258e10056df3158e1001cfc7058e10056dc3058e10004ff74d8a10014fe74d8a10004fd74d8a10014fc74d8a1000cfe73d8a10004fd73d8a1000cfc73d8a10006f571d8a1013eee21d8a1013eec21d8a10006fa70d8a10004fd7698a10006ef6298a1003cff7658a10005bf7458a10035bc7458a10005df7358a10055dc7358a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10004fd7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a10006df7358a10004df7358a1000cfe7358a1000cfc7358a10006dc7358a1000cdc7358a10006ef7258a10006ee4258a10006ed4258a10006ef3258a10006ec3258a10006f77158a1003eee6218a10006ed6218a1003cff768ca10004fe768ca10004fd768ca1003cfc768ca10006df638ca1000edc638ca10004ff764ca10004fe764ca10004fd764ca10004fc764ca10005f7714ca1001df4714ca1000cff764c61000ede634c610006dd634c610005ef724c610005ec724c610005fb704c610005f8704c61003eee62c8610006ed62c8610005fa70c8610005f970c8610146f576c861001df672c8610146f762c8610147e662c8610146f562c8610007e562c8610147f270c8610005f570c8610147f170c861001ef660c861003cff764861003eee6248610006ed624861001fe42148610005fb7048610005f87048610005f5760861001ef5760861001fe67208610146f76208610007e76208610146f56208610147e46208610147e64208610177e5420861016fe73208610147e43208610005f5700861001ff2600861000cfe768c21001cfd768c21000ede638c210006dd638c210005ee728c210005ed728c21001df6718c210005f5718c210024ff764c210006df634c21000edc634c210006ef62c821003eec62c8210147e721c821001cfd768821003eee6288210006ed628821001df6718
  | 6 => 0x4618c12000cff764c120084fd764c12003cfc764c120006bf644c1200aebc644c120006df634c12000edc634c120005ef724c12003dec724c120006f7614c120006f4614c120087d8304c120006bf648812007ebc6488120006df6388120096dc6388120006f76188120006f4618812003dfa708812003efb6088120185ef7488120185ed7488120007af648812019fac6488120085ee7388120085ec7388120007cf6388120007cc6388120005ed7188120007e7618812013eec6188120007e46188120006e4618812003dee708812003eef608812003feb6088120004ff7458c20014fe7458c20004fd7458c20014fc7458c2003edf7358c2003cff7258c2003cfe7258c2003cfd7258c2003cfc7258c2003ede3258c2003edc3258c20004ff7158c2001cfc7158c2006edf3158c2006cfc7058c2006edc3058c20004ff7458420014fe7458420004fd7458420014fc7458420004ff735842000cfe735842000cfc735842003ef7715842003ef7215842003eec215842003ef4215842001cff705842003eef205842001cff768c42003cfe768c420004fd768c42001ef6618c420006f5618c420004ff764c420004fd764c42003cfc764c42000ede634c420006dd634c420005ef724c42003dec724c42001ef6614c420006f5614c42003ded7688420136ed7688420004ed7688420137ae7488420137ad748842003eef6488420196ed6488420137ce7388420137cd73884200deee638842003eec638842003dee718842003fe6718842003eef6188420136ed6188420005ed708842013eee608842003fea6088420094ff768c02003cfe768c02000cfd768c02003cfc768c02000ede638c020006dd638c02003dee728c020005ed728c020094ff764c02003def7648020006ef7648020004ef7648020007af744802018fac744802003eef644802018eed6448020007cf7348020007cc7348020086ee634802003eec6348020007e77148020135ec7148020007e47148020005e47148020006ed614802003def704802003feb7048020186ee604802003fea604802017fea504802017fe95048020004ff7458f10014fe7458f10004fd7458f10014fc7458f1001edf7358f1005ede4358f10006dd4358f10004ff7258f10006ef7258f10004ef7258f1003cfc7258f10006ec7258f1003cec7258f1005edc3258f1001cfc7158f1001ede3158f1001edc3158f1005edf3058f10004ff7458b10014fe7458b10004fd7458b10014fc7458b10004ff7358b1000cfe7358b1000cfc7358b1001eef7258b1001cfc7158b1001eee2158b1001eec2158b1003cff768cb1001cfe768cb10004fd768cb1001cfc768cb1000ede638cb10006dd638cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb10044fd768c31015edf638c31000edc638c310
  | 7 => 0x8520005df7358520085dc7358520006df6358520006dc6358520006bf6418520006bc6418520006df6318520006dc631852001ef66118520006f56118520005f67618520006f67618520006f76418520007b76418520006b76418520006f66418520006f56418520006f46418520007b46418520006b46418520006f76318520007d76318520006d76318520006f66318520006f56318520006f46318520007d46318520006d46318520007e57218520007e64218520007e54218520007e73218520007e43218520127f32018520127f0201852001ef7741852001ef6741852001ef5741852001ef47418520006f65418520006f55418520006f4541852001ef7731852001ef6731852001ef5731852001ef47318520006f74318520006f64318520006f54318520006f4431852001ef7721852001ef6721852001ef47218520006f74218520126f64218520006e64218520006f54218520006e54218520126f44218520006f73218520006e73218520126f63218520006f53218520126f43218520006e4321852001ef7701852001ef57018520006f74018520006f64018520006f54018520006f44018520006f73018520006f43018520126f72018520006f52018520126f42018520004fe768c520004fd768c52001cfc768c520006bf648c520106bc648c520006df638c52000edc638c52003dee728c520005ed728c520006f7618c52001ef4618c520004ff764c520004fe764c520004fc764c520006bf644c5200febc644c520006df634c52000edc634c520005ef724c52003dec724c520087cc324c520006f7614c52001ef4614c520005ee76c852003eee76c8520004ee76c852003def74c85201bded74c8520007af64c85201b7ac64c8520085ee73c852003dec73c8520007cf63c8520007cc63c8520007e761c852001eee61c852001eec61c8520007e461c852001ee461c8520005ee70c852003eef60c852003feb60c852008dbe7488520005bd7488520006bf64885200e6bc6488520085de7388520005dd7388520006df63885200dedc63885201aded7288520006f7618852001ef46188520005fa7088520005f9708852001cfc7648520006bf64485200d6bc6448520006df63485200cedc6348520006f7614852001ef46148520005fb7048520005f8704852001cec76485201adef74485201aded7448520007af64485201a7ac6448520085ee7348520085ec7348520007cf6348520007cc634852003def714852003fe77148520007e7614852001eee614852001eec6148520007e4614852001ee46148520007eb7048520005ec7048520007e8704852003eef604852003feb604852009cfe768c120006bf648c1200b6bc648c120006df638c12000edc638c12003dee728c120085ed728c120087cc328c120006f7618c120006f
  | 8 => 0x86ce72d8d20006dd72d8d20006cd72d8d201cedc72d8d20006df42d8d201cede42d8d20006dd42d8d201cedc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d201cedf21d8d201cedc21d8d201cedf70d8d20086de70d8d20006dd70d8d20006df40d8d20006de40d8d20006dd40d8d20006dc40d8d201cedf20d8d201cedc20d8d20005bf7458d2008dbc7458d20006bf6458d20006bc6458d20086dc6358d20005f77158d20005f47158d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d20084ff7358d20006df7358d20094ff7258d20006ef7258d20086ef3258d20086ec3258d20004ff7158d20006f77158d20004f77158d2001cfc7158d20006f47158d2001cf47158d2009cff7058d20006fb7058d20005de7618d20086de7618d20004de7618d20006df6418d200079f6418d200069f6418d20006de6418d20006dd6418d20006dc6418d200079c6418d200069c6418d20087cf7218d20087cc7218d20007ce4218d20007cd4218d201c6df6018d201c7db2018d201c7d82018d2000cfc764c920006bf644c92010ebc644c920006df634c92000edc634c920085ef724c920005fb704c920005f8704c920006bf64d8520006bc64d8520006df63d8520006dc63d8520004ff74d8520014fe74d8520004fd74d8520014fc74d852000cfe73d8520004fd73d852000cfc73d8520006f741d8520006f641d8520006f541d8520006f441d8520006f731d8520006f431d852001cfe70d8520006f764d8520007b764d8520006b764d8520006f664d8520006f564d8520006f464d8520007b464d8520006b464d8520006f763d8520007d763d8520006d763d8520006f663d8520006f563d8520006f463d8520007d463d8520006d463d8520007e772d8520007e642d8520007e542d8520007e732d8520007e432d8520147f320d8520147f020d8520006f774d8520006f674d8520006f574d8520006f474d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f743d8520006f643d8520006f543d8520006f443d8520006f772d8520146f672d8520006f742d8520146f642d8520006f542d8520146f442d8520006f732d8520146f632d8520006f532d8520146f432d8520146f770d8520006f570d8520006f740d8520006f640d8520006f540d8520006f440d8520006f730d8520006f430d8520146f720d8520146f420d852008dbe7498520005bd7498520006bf6498520006bc6498520085de7398520005dd7398520006df6398520006dc6398520006f76198520005bf745852008dbc7458520006bf6458520006bc645
  | 9 => 0xe738862013fcd73886200deee63886200deec638862003dee718862013fe6618862013eed6188620007e5618862013fea7088620005ed708862013fe9708862003eee608862001cff764862001ef66148620006f5614862003fe42148620005fb7048620005f87048620005ed760862003eed76086201eeef64086201eeed64086200beee63086200beec630862003fe67108620007e7610862013eed610862013fe46108620005ed700862003fea600862000cfe768c22003cfd768c22000ede638c220006dd638c22003dee728c220005ed728c22006cff764c220097d8304c220005ed76c822003eed76c82201e6ef64c82201e6ed64c822009eee63c822009eec63c822013dee71c8220006ed61c822003fea60c82201dfea50c82201dfe950c822008dbe76d912008ebe76d9120014be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006be63d9120006bc63d9120007af72d912008fac72d9120007ae52d9120007ad52d9120007af32d9120007ac32d91201d7bb20d91201d7b820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120006bf72d91201d6be72d912008ebd72d91201d6bc72d9120006bf52d91201d6be52d9120006bd52d91201d6bc52d9120006bf32d91201d6be32d91201d6bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006bc31d91201d6bf21d91201d6bc21d91201d6bf70d912008ebe70d912008ebd70d912008ebc70d9120006bf50d9120006be50d9120006bd50d9120006bc50d9120006bf30d9120006bc30d91201d6bf20d912008ebd20d91201d6bc20d912000cfe76d8d20006bf64d8d20006bc64d8d20086de63d8d2003dee72d8d20087cf32d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df43d8d20086de43d8d20006dd43d8d20086dc43d8d2003cfe72d8d20084fd72d8d20086ed72d8d20084ed72d8d2003cfc72d8d20086df32d8d20086ef32d8d20086ec32d8d2001cfe71d8d20004fd71d8d20086df31d8d20086dc31d8d2003cfd70d8d20086df30d8d20085de76d8d2000cde76d8d20006df64d8d200079f64d8d200069f64d8d20006de64d8d20006dd64d8d20006dc64d8d200079c64d8d200069c64d8d20087ce72d8d20007cd72d8d20007ce42d8d20007cd42d8d201cfdb20d8d201cfd820d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d201cede72d8d20
  | 10 => 0xc530004fe76c8530004fd76c853003cfc76c8530006f761c853001ef461c8530004fe7688530004fd768853001cfc76885300adbe7488530005bd748853000dde7388530005dd7388530006ef628853003eec6288530004ff7648530004fe7648530004fc7648530004fe7608530004fd760853001cfc760853000dde7308530005dd7308530006ef620853003eec6208530006f7610853001ef46108530005fa7008530005f9700853020edf648c13020edd648c130007ce728c130007cd728c1301cedc628c130005dd718c13015edc618c13000dde708c13000fda708c13000edf608c13000fdb608c130004ff7458f20014fe7458f20004fd7458f20014fc7458f2003edf7358f2009ede4358f20006dd4358f2003cfc7258f2003eec7258f2003cec7258f2009eef3258f2003ede3258f2003edc3258f2003eec3258f20004ff7158f2001cfc7158f2009edc3158f2009edf3058f20004ff7458720014fe7458720004fd7458720014fc7458720004ff735872000cfe735872000cfc735872003ef7715872003ef7215872003ef4215872001cff768c72003cfe768c720004fd768c72000ede638c720006dd638c72003dee728c720005ed728c720004ff764c720004fd764c72003cfc764c720206df634c72000edc634c720005ef724c72003dec724c720207cc324c72003def7648720006ef76487201fdef74487201fded744872009dee734872009dec734872003fe7714872001eee614872001eec6148720005ec7048720084fd768c3201cedf638c32000edc638c32003dee728c320005ed728c3201cfcc328c32000cff764c32003cfc764c32000ede634c320006dd634c320005ef724c32003dec724c320096de63d8e20004ff74d8e20014fe74d8e20004fd74d8e20014fc74d8e20094fd73d8e20006ed72d8e201cede32d8e201cedc32d8e2001cfe71d8e20004fd71d8e20006fa70d8e2000cff7658e20096dc6358e20004ff7458e20014fe7458e20004fd7458e20014fc7458e20006df7358e20096df3258e20004ff7158e2001cfc7158e20096df3158e2003cfc7058e20096dc3058e2000cff764ca2000ede634ca20006dd634ca20005fb704ca20005f8704ca20006f76198620004ff7458620014fe7458620004fd7458620014fc7458620004ff735862000cfe735862000cfc735862007dbe7418620005bd7418620095de7318620005dd731862001ef66118620006f5611862001cff768c620004fe768c620004fd768c620004ff764c620004fd764c620004fc764c62000ede634c620006dd634c620005ef724c62003dec724c62007dbe7488620005bd7488620095de7388620005dd738862001ef66188620006f56188620005fa7088620005f9708862013fae748862013fad74886201f6ef64886201f6ed648862013fc
  | 11 => 0x6ef4158a30006ee4158a30006ed4158a30006ec4158a30086ef3158a30086ee3158a30086ed3158a30086ec3158a30086ee7058a30086ec7058a30006ef4058a30006ee4058a30006ed4058a30006ec4058a30086ef3058a30086ee3058a30086ed3058a30086ec3058a3009dee7218a3003eee6218a30006ed6218a30095fa7018a301cddf748ca30225dd748ca3000dde728ca3000fce728ca301cfce628ca301cedd628ca30007cd628ca3015dde718ca301cfda708ca30005dd708ca301cfd9708ca3000ede608ca3000fda608ca30005ee72d8630005ed72d8630006ee62d8630006ed62d8630025fa70d8630006ee6298630006ed6298630006f76198630006ee6258630006ed6258630004ff7458630014fe7458630004fd7458630014fc7458630046de4358630006dd4358630004ff725863003cfc7258630006de3258630046dc3258630046f63158630046f5315863015edc3158630046df30586300b5be7418630005bd7418630005ee7218630005ed7218630006ee6218630006ed621863001ef66118630006f56118630055fa701863015ddf748c63021ddd748c6301cdde728c630007ce628c630007cd628c63000dde718c63000fd6718c63015fd6618c63015edd618c630007d5618c63015fda708c630005dd708c63015fd9708c63000ede608c63000fda608c63003cff76c8630004fe76c8630004fd76c863000dde73c8630005dd73c863003eee62c8630006ed62c863001cff7688630004fe7688630004fd76886300b5be7488630005bd748863000dde7388630005dd738863003eee6288630006ed62886300dfcc3288630004ff7648630004fd7648630004fc7648630005df734863000ddc734863003eee6248630006ed624863001cff7608630004fe7608630004fd760863015ddf730863000ddc730863003eee6208630006ed62086301cfcc3208630005fa7008630005f97008630004ff74d8930014fe74d8930004fd74d8930014fc74d8930096ee32d8930096ed32d893001cfe71d8930004fd71d8930006ef6298930085f97098930005bf74589300adbc7458930005f77158930005f4715893009dfb705893003eee6218930006ed6218930004ff74d8530014fe74d8530004fd74d8530014fc74d853003cfe72d8530004fd72d8530056f631d8530056f531d8530006f76198530045f97098530005bf74585300adbc7458530005ef7258530005ec725853005dfb70585300adbe7418530005bd741853001ef66118530006f5611853001cdc764c530216df644c530216dd644c530007cf724c530007cc724c530206dc624c53000ddf714c53000fd7714c530007d7614c53001ede614c53001edc614c530007d4614c530007db704c530005dc704c530007d8704c530005d8704c53000edf604c53000fdb604
  | 12 => 0xe7418121004fd7418121014fc741812100cfe7318121004fd731812100cfc7318121126f72118121136ee2118121136ec2118121126f42118121004ff7458c21014fe7458c21004fd7458c21014fc7458c2101cff7358c2101edf7358c210bede4358c21006dd4358c2103cfe7258c2103cfc7258c2103eec7258c2103cec7258c210beef3258c2103ede3258c2103edc3258c2103eec3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c21004ff7058c21004fc7058c210bedf3058c21004ff7498021014fe7498021004fd7498021014fc749802100cfe7398021004fd739802100cfc739802101efa7098021006fa4098021006f9409802103efb209802103ef8209802101efb109802101ef81098021004ff7458021006bf7458021004bf7458021014fe7458021004fd7458021014fc7458021006bc7458021014bc7458021004ff7358021006df7358021004df735802100cfe735802100cfc7358021006dc735802100cdc735802103eee4258021006ed4258021006ef325802103eec325802101eef215802101eed215802101efb7058021006fa4058021006f9405802103efb205802103eec205802103ef8205802101efb105802101ef4105802101ef8105802106dfa70d8a30006ef6298a30006ef6498a30006ee6498a30006ed6498a30006ec6498a301cfcf7398a301cfcc7398a3009fce4398a30007cd4398a3009fcc3198a3009fcf3098a3009feb3098a3009fe83098a3003eef7498a3003eee7498a3003eed7498a3003eec7498a30006ee5498a30006ed5498a30006ec5498a3003eef7398a3003eee7398a3003eec7398a3009eef4398a3009eee4398a3009eed4398a3009eec4398a3003eef7198a3003eee7198a3003eed7198a3003eec7198a30006ef4198a30006ee4198a30006ed4198a30006ec4198a3009eef3198a3009eee3198a3009eed3198a3009eec3198a3003eee7098a3003eec7098a30006ef4098a30006ee4098a30006ed4098a30006ec4098a3009eef3098a3009eed3098a3009eec3098a30004ff7458a30014fe7458a30004fd7458a30014fc7458a30006ef4258a30006ee4258a30006ed4258a30006ec4258a30086ee3258a30086ed3258a301cedc3258a30004ff7158a3001cfc7158a30006ef7658a30006ef6458a30006ee6458a30006ed6458a30006ec6458a30007cf7358a30087cc7358a30087ce4358a30007cd4358a30087cc3158a30087cf3058a30087eb3058a30087e83058a30006ef7458a30006ee7458a30006ed7458a30006ec7458a30006ee5458a30006ed5458a30006ec5458a30086ee7358a30086ed7358a30086ec7358a30086cc7358a30086ef4358a30086ee4358a30086ed4358a30086ec4358a30006ef7158a30006ee7158a30006ed7158a30006ec7158a30
  | 13 => 0x9221006be5059221006bd5059221006bc5059221006bf3059221006bc3059221236bf2059221236bc205922101ebf105922101ebe105922101ebd105922101ebc1059221004ff7458e21014fe7458e21004fd7458e21014fc7458e2101edf7358e21006df4358e210dede4358e21006dd4358e210dedc4358e210deef7258e210dedf3258e210deef3258e210deec3258e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e21004fc7058e210dedf3058e210dedc3058e21006df7458e21006de7458e21006dd7458e21006dc7458e21006de5458e21006dd5458e21006dc5458e21006df7258e21006cf7258e21206de7258e21006dd7258e21206dc7258e210decc7258e21006df4258e21206de4258e21006dd4258e21206dc4258e2101edf7158e2101ede7158e2101edd7158e2101edc7158e2101edf4158e2101ede4158e2101edd4158e2101edc4158e2101edf2158e2101ede2158e2101edd2158e2101edc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df4058e21006de4058e21006dd4058e21006dc4058e21206df2058e21206dc2058e2101edf1058e2101ede1058e2101edd1058e2101edc1058e2100cff764ca2101cfc764ca2110ebe644ca21006bd644ca2100ede634ca21006dd634ca2122def724ca21005f7714ca2101df4714ca21004ff7498221014fe7498221004fd7498221014fc749822100cfe7398221004fd739822100cfc739822101cfe7198221146f7219822101ef4219822101efa709822101efb109822101ef81098221004ff7458221014fe7458221004fd7458221014fc7458221004ff735822100cfe735822100cfc7358221006ee4258221006ed4258221006ef3258221006ec325822101cfc715822101eef215822101eed215822101efb705822101efb105822101ef8105822100cfe76d8d210cede63d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d2101cfd72d8d210cedf32d8d2103cfd71d8d210cedf31d8d21004fe70d8d21004fd70d8d210cedc30d8d210cedc6358d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210ccff7358d21006df7358d210dcff7258d21006ef7258d210dcef7258d21206de3258d21206dc3258d210ecff7158d21006f77158d21004ff7058d21004fc7058d2101cfc764c921006df634c92100edc634c921005f7714c92101df4714c92103fe4214c92100cff764c5210ccfd764c52103cfc764c521006df634c52100edc634c521005ef724c52103dec724c52101fe4214c521004ff74d8121014fe74d8121004fd74d8121014fc74d812100cfe73d8121004fd73d812100cfc73d8121006fb6098121005bf74581210d5bc7458121005df73581210cddc7358121006f96018121004ff7418121014f
  | 14 => 0x3eee711893103eed711893103eec7118931006ef4118931246ee4118931006ed4118931246ec41189310beef3118931246ee31189310beed3118931246ec311893103eef701893103eee701893103eed701893103eec7018931006ef4018931006ee4018931006ed4018931006ec40189310beef30189310beee30189310beed30189310beec3018931246ef1018931246ec101893101cde768c931205df748c93123ddd748c93100dde728c93100fce728c931206df628c931007cf628c931207cc628c93101dde718c931207d6718c931207d5718c93101ddc718c93100edf618c93100fd7618c931005dd708c931006ef62d8131006ec62d8131004ff74d8131014fe74d8131004fd74d8131014fc74d813101cfd73d813103cfe72d8131004fd72d8131006fb40d8131006f840d813105efa30d8131005ee7298131005ed7298131006ef6298131006ec6298131006fb6098131005bf74581310fdbc7458131005ef7258131005ec7258131006ef6258131006ec6258131006ef6218131006ec6218131006f96018131004ff7418131014fe7418131004fd7418131014fc741813101cfd7318131026de4318131006dd431813103cfe7218131004fd7218131006de3218131026dc3218131156de3118131156dc3118131006fb4018131006f84018131026df3018131026f93018131004ff7458f21014fe7458f21004fd7458f21014fc7458f2103edf7358f2101cfc7258f2103ede3258f2103edc3258f210eedf3158f21004ff7058f21004fc7058f210eedc3058f2100cff764c72103cfc764c72100ede634c721006dd634c721005ef724c72103dec724c721004ff7498321014fe7498321004fd7498321014fc749832100cfe7398321004fd739832100cfc739832101cfe729832101cee729832113eee219832103eec219832103efa709832103eef209832103efb209832103ef82098321004ff7458321014fe7458321004fd7458321014fc7458321004ff735832100cfe735832100cfc735832101cfc725832103efb705832103efb205832103ef82058321006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf5359221006be5359221006bd5359221006bc53592210e6bf7259221236be7259221006bd7259221236bc7259221006bf5259221236be5259221006bd5259221236bc5259221006bf3259221236be3259221236bc325922101ebf715922101ebe715922101ebd715922101ebc715922101ebf515922101ebe515922101ebd515922101ebc515922101ebf315922101ebe315922101ebd315922101ebc315922101ebf215922101ebe215922101ebd215922101ebc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf505
  | 15 => 0x66118532006f56118532004ff74d8132014fe74d8132004fd74d8132014fc74d813203cfd73d813209eef32d813209eec32d813201cfe71d8132004fd71d813209efa30d8132006fb6098132005bf745813210dbc7458132005f77158132005f47158132006f96018132004ff7418132014fe7418132004fd7418132014fc741813203cfd73181321c6de32181321c6dc321813201cfe7118132004fd711813206ef93018132004ff7458a31014fe7458a31004fd7458a31014fc7458a3101eef7258a310ceee3258a310ceed3258a3101cfc7158a3101eee2158a3101eec2158a31004ff7058a31004fc7058a31004ff7498231014fe7498231004fd7498231014fc749823103cfe7298231004fd729823101cfe719823101efa7098231056f9309823101efb109823101ef81098231004ff7458231006bf7458231004bf7458231014fe7458231004fd7458231014fc7458231006bc7458231014bc7458231004ff725823103cfc725823101cfc715823101edf315823101edd315823101efb7058231046fa3058231046dc305823101efb105823101ef81058231004ff74d8931014fe74d8931004fd74d8931014fc74d893101cfd73d8931006ef42d8931006ee42d8931006ed42d8931006ec42d89310deee32d89310deed32d8931206dc32d8931004fe70d8931004fd70d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310dfce73d8931007cd73d89310dfce43d8931007cd43d89310dfe731d893122fce31d893122fcc31d89310dfe431d89310dfcf30d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ee54d8931006ed54d8931006ec54d893122eef73d89310deee73d89310dece73d89310deec73d89310deef43d89310deee43d89310deed43d89310deec43d89310deef71d893122eee71d89310deed71d893122eec71d8931006ef41d893122eee41d8931006ed41d893122eec41d89310deef31d893122eee31d893122eec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef40d8931006ee40d8931006ed40d8931006ec40d89310deef30d89310deee30d89310deed30d89310deec30d893122eef10d893122eec10d8931006ef62989310cdf571989310edf7715893103eee6218931006ed62189310ddee7618931006ee7618931006ef6418931006ee6418931006ed6418931006ec6418931247cf7318931207cc73189310bfce4318931007cd43189310bfe73118931247ce3118931247cc31189310bfe431189310bfcf301893103eef741893103eee741893103eed741893103eec7418931006ee5418931006ed5418931006ec541893103eef731893103eee731893103eec73189310beef43189310beee43189310beed43189310beec431893103eef7118931
  | 16 => 0x8002003001801c00001a005800402600200700280000110000000000001000001c00600f000001800a001006000c00000900200080000000008000030000000002400a00000b80480000000000010014006001000c00000a0000010000001001800c01c0070020008014001001800800401800f00080160020000078000000000000400c008000800000400d0020000008016006000800000000080500000000070000000001002000000e0030020000022004006800000200000000180180070000018024017000805000a001009800001a000005001002c0000008010008001000801400e00500f800c0240020040008012001000001c03600700500040040000008004030001000802000c00a009001000400300080000000000040004014017000000000202b00200040040080000050004002000800402c019000802001000500100440080040008000010005003000c008001000804c000000013002001c00b0008018072001000001400000100c8000000000000000c0060000000014006015000002000a002000000802c000000001000c0190018000016008000800c00c001000804c0040010010010028000004000002400000080000060090000000000001001801c000004003802002e01000080000000010058004002010002005801000000900100020010000090022006005805c00c000000000c000005006001800c000003800000a00400a000c014000006003c004001004000000a0070008000000000003800000a0030000008004017000000000e000000803001c0010000000004009001803c0040000070014002003000000000a0030000000002005008002c0000270158004000002005000001800b000015c02a003003800400c002001805001200800000080060090000000016005001802800400a001800002c007000000c01400b0000000030005004ff7458632014fe7458632004fd7458632014fc745863203cfc725863203ef771586320cef6315863203ef7215863203ef42158632004ff7058632004fc7058632004ff7498232014fe7498232004fd7498232014fc749823203cfe729823201cfe7198232004fd719823203efa7098232096f9309823203efb209823203ef82098232004ff7458232006bf7458232004bf7458232014fe7458232004fd7458232014fc7458232006bc7458232014bc745823203cfc7258232086ef325823203eec3258232004ff715823201cfc7158232086df315823203efb7058232086fa3058232086dc305823203efb205823203ef82058232004ff74d8532014fe74d8532004fd74d8532014fc74d853203cfd73d853224ede32d853224edc32d85320eef631d8532004fe70d8532004fd70d853210dbe7498532005bd749853222eef6298532006f7619853222eef621853201ef
  | 17 => 0x50038024008003003000000000300a8014000007000800c04200700000000020000038008008003000000001000200c002c00000b00080040020020000014030001004800800400100180080000080028014014001002800400c001002800400000000080000000010118020000000002001800400400100080180040000004014000007802c004001005800000000100300000000040000000022009004803800001800600000000080000014002015000801400200100080300000080130004000002000003800400600100240100030038064004003008001400a001003804000c004004000801c013005000000a003000002c028021001806c0180000048018002008019800002c0000010010000000001001c000002001802000a00000b800000000000480280000000010004000001000000000600a0008010002001015000000600a000001c00e00000380000040010000000008010013000000a001000000c004000003802801a000003800400000c0018004036000002000804000200880200080010000028020009003800400001d000801400400d0050018000000005000000000000200000180010000008000001008000400601b0008004008005000005400000100d80300540020000010000015000800000800100c8000008002002000400a0090008008004000000800001400500000040000010000040000001005800001400200200040120010020008000024000800000600000400040020000000018000008003000c008004000000803800d000000800c000000000003a00300200b001c00100080200120000028000000007002009c000001007004c00a002001800000200000080000020080000004000000001003c0020170000014002000001001c000001000000000c000001004400600800f805401801c001800001e000004801c00400000d006803000000080080020000038000000000000001c0000000000010000002001000c000003001800000e003000000400e00000d803c0140000090004004002000000c01802800f801c006012001800000a031000800000000400700180160000008014008000000000400000000080000340000040000006005000002802c015001800c05e0000000000004002003006c00000000380240440160018004006002002805400000a000004000a01800100000040030000054004003008000800801900100000240000000000010002000000000c011000002c000003000002800200000180000100010050028002001001800803400300000080040000000010000014006000000200a009002c006001000001005a009000000c0000000008000002000000000c048001001000000e000005000c01601000700a4006003000002800000100000040000010070008000001000800
  | 18 => 0x38b8ad0048b00017b80381203001528db26c91940ea4ae462f36a88445f14e3418071ce1e6ed5384b9c6d4a8a164000084e3453b78a5824835c01aa5940465f2c085b9066a58656722d90a049916d47755ab0a22292a78d9b4eda01a49e24a60928a27dc8143950002b5200062a239951229484dc934a8d3e100050ea2260008162d6c0000000001c900000000000000ca43c600012400000e2a95d2700014bc88e48600012272ef000000000042839d00043025162f1a07ca72831b7c07d0a0a0001fe000000000000000000009418731662b80000000015b1aa0000000000c7a442000000031800017a1928000000000297cfee32b00000001ab2c03308b7800000000013d8ec80004ae087000000049e800042681caa102400005a280025dd4300003268000cb04c314563900006cd124e2764739f40a21b9c2683404be9ae0cdeaca800000000000000002788ca5200320000edd1721200d6549100028a92bc0000fc507800159e0000b30a9513d47f282d4d427c805c431cac0004d3112000059f0f30ac91d8f4823a3af8000000440444682ee3c237caf0c540000ed95b4b3aa64aa6ab090854f281053b01cb5197830b840013754e75542765064210a930a980000a8cda99ad07e8ae15f40012223f813c22e000086714f0000dc680c3581864da62e00001db81b98ea17a4000b810003ac13554055e7c1492d546f2424cb15e2c0f0f83b7c7b81f492b3d0c1008ae493092cd9800089f45be2f80001731c000000000000002158be008a00016c400024a1c280000000003dc8a220003f5000000000003244cc0009945cf3370000df877700029420006c3000000000000032d17980000003908000be40000000d4419ca6e0000001410429800000061c75a34d1b7d10891280016f800081d8000a680d825f03a8c983677fb2ce8df49ca0f7487a0815c534d21829a400079455b4aa074a1f30e3000098960800008307a200017c9d0c6f0000249e020f5e25e43017794f00a051c184c76a8b680011a811c3b0800241e000a3eb15db2a0000000002a3a000000000183c0000000000c3ce78946a8680000009b034684b07c3934002403e006003000c02c000000800001a0000028000000006003000c00a0010010018000012000001c0080080070004002005000003000c0000098008000000006801400000b01180300000040130014002000012003401000400780000200010040000002007001000401200000f000401000800d000405e008003002800a00600500100060010008014006001000000401200c003000000201900e80000060030000004008000005801c00e0060018010008000001800c012003001801400200a004000000a001000001800400000200600100090088048002007000801c000028005002001a004004000000001
  | 19 => 0xde00014c00000001b6314a737086000000290c00000000000000000001220000fe544a45863046a01d70c10044254a200000000dbb10a8e7811910a15b4599ba400048c48724ca7c250600025e531650c3a286180006eb8f89fa849254faa88518d2eac680ec7d60082a001748140ee5f506dd64000000043b61eadba0b9cf62b410c451abff0dbc4647fc31763a44b461e1dc95de7a6a47b860168183aa8ae721d0de87b53024a84978872385a9d485e9edc9403d523d9830b48ea8532a714e19f880000003670000000000296292c0003e452a00012c20e24451041178279000000016a000147906c00000000000000006394cf839d0991e800024942bc9f93e7d8e828257e33600000000002ad8000ba80001d726b41d1878267013464a9fb356848cf96000000083e0000004908000e0800000000000007a61c78000a68000026042800069580012e4000000523a1708eb77fc1e8b642ed5253c444a00628d44630000846000379000057600021dc000e4690b00009da69634829d28f6000000000107875887605e1cf4904ab053b98dcd280d121fa4b453698730202773b00f891580012240004dbc4c882800008b176600076b3cc89e800043a364000047c7ef2cf01645c499b100a91000000012a198000000019d250803e63296800002a8000000000110600016354f8eba32e412271151252daf840000008d83bca63000015730900000006f3421000070c00000022d54e504300020a281600000000004cc20a42aa308c86000133800000002002d814c0002cd0002b5011e0a935895ac45200014c400000082b988a2d73d41350000000000553338000000053c00003601154cb0000b8c4f6000000298ea9880b34794a00003dc80009c91480001168bec4b287480024b92067a024b27000004b039f9da60008fa3b18ae922aa3300000000002900000000000605263e57c94c122b9427801968ff80016ec0000000001bff4822410a5a24c0000000000af4e9c000000000081e000000000106564f33c15a400094880006989d037100014b51ce00054d800069e2f545c41bc000654309400140c45a052e10a000aa74701b85540973141e480db65ff08e08e256f000000077d42e80789e129a2427dc14153740009d716d26c2e995300259f135820000002a8873e0101e5cec05289065664b94a884c4000092ac7e35832820b0fcc8d010b16c939207c00021b44e86712780000d6a0cf14713cc0000003d8000042000012cc0008c087f3510e5cba0000000000158c4853dde85800000051607b20000003c208fc8aa0f4000060a232000340e968000a049329c94dd05ad2b8a73a0007fa02aa1cd28261020685d60fc00040f5780cb84aa00003ea5f3818a66ab2d572789000000000055a3fae2a0aaa000186213a4fa09b800029a5b08e501
  | 20 => 0x14000000015f4719f6155f0004588d54f0fa483b41ff34533abacc155e6302552af87a8bc453b4b5a82862c4d006c90c522c26b12dd6500001c54f180010282f210480015529348caa0d800000007791445bf8d90000e0ca5d0000000ec72d80004b80bf49b78e096704c071c4fd5075a2cc2933643d8a1546c50e2ac11d5377a3435e9fd8b2b62cd42000000061610c10ac00000038282d0bd29208002b2e9099cc05629c82fc000118c000fe084819893a459e9f9af1411cb5e5e480019f82fa6fe1270584f9e01d2c1d8688e0199368200cb2c1bc3c81280fd6078049c000150275bdb84b4abf7e80029c915764d083980b844c3761c9953c7a04c10c50bb48ad50fbbc55185b609d1e72a728496462b70d24f686dc284845c000000242c00155620190d22415af99c3901a747ac000000000080c0002768794d40748204899a9bc00000027acb8900047c80000000000000230e1c9782b9c8b6b523b20000000d24000000074923619f41540000007763e800008dcab14119dfc8e9214121dad92870004c800002c40000ec0000ade5522590000832a88000004800000000000001ca3f752480010b48d5a258000f6c4263df887cea415614bd65a000a26000151a59100004000011dca6285f4000bbb4001e11c20000a520d5800145e7be18faadf0226cb2a42970e5b7591381d70e4c0003c70000ec01c04b014400006ca34621b28763302761d5896e00049d1e040ac1d0303007a6360001ec03772aa9b4106de8a000a964ed29832cc00000007640008093390ebf3a8a854f291a52d044f254a9d0af32e641f281c974264b44ab886b442d5201a8c0006320000cd10d70002595bdc5b30003ff400000081b10e96d0aae4860430000cbe42a5168ffc0005c2000298800017a00008d8000817843e01ce572c4087a22d1360cb8000000eef0000001e086860003f08bda000a053bd0d7417f5cc16c461d3fa4ecbad9880a7e9bc00003413cc0000bba7ee64e85908041143287cd41527c4000531d46ab10000994000152d41a4ff2f60e5831c03e529a42307724504880000005db03922494081223a1024c73c8b4469ce70ad39172da4000000560b211b440001f80000198c9ca3fc43cd9c21200000000000000000000000b852cb0b197e20006680000fba00000054b40000d20002c208aef7564813b0c409a4a303aa8f060002e1800228475b0001295e341f25c414206ecdd86654d7c000d5e0000000000000a150000000e701eecbf9df4c060e10000000ed411f1841c292ec98f0000000f18000029000154a59480008c065a0990000000744589000261903c3b4800174c2202931408bee98000055f83ad4640002f8846000078a80000000008e200000010628a300017746d200014e28b2bb760e534162833c7f113ba6c8176415cc726791
  | 21 => 0x4f2c00007626f00000000004c5540e50a000000000000000006751a428d1e933215c00000000000000000fb420cc79c00038d4e62dd4fb05352b98000d94be6422000165e8e80000d500007ae1bd2dcc8ec7025244e080512b4718c5eab4d2d46010000000000092000000078a0001fc800125e00000005bc00006e233985400000000008a00008decb220cc000000455cf0333a5084650474000ae1d4007db2ac09c2b6a9940000003eb8000aaca272c6000141b84c000203e7188808b2c6030ee083000000096c483262cb441420000000eba79900000021f831788c00000000000004e815709b600000000a4a44068ae5a05440028d313aaf4864940000213e93c24b2ca920e0000001b9000006e00008a800039c7d141ba884fdca9c11d61502053fb2a026d847800010dcf2a3d26070892490a9a10197ada14c2b0a4b9b9254000a63478d5d0ad89043559ba704b1b20a198b61a940840951520c675008226ac79602a0f2d686aad58807503bf394a5b4561de143e5fa800169a000000354a99cd7c00006e914c00072aaf4d1640005790002b345aa11d8000a207101842c297e730088100020340009e91ea0580e4e3a404ba9e887a098145e62f1280000e0a18d1a40aa2a38000634a1b8000c345fc4ae00005fc000a39000000114100028ed5d45c97fd139c00121247127cc00000028237d189e0000003e98ceca370003b60c509203f00001a20e9a62e31c11c94de00055c00000000000000291432a3a05325492a2000158a9085068064c100000000003804e24000a093e863e086ea978bd8d84ca252333b8b6f4f86c6800245000041200028db3660001760000000a3f00002ccecb00000000000007cebd1985a3401c40a69f0812a7061b0187d3f41881f990d83f4158102151e76c77980002460000000001b7a000000533000052b52e0000ecc42a0171f2927244e3af0a41b5047a5d78002526bfaa030001f1d28e94f0000f2901d5c6437800107b73528f43b428e5a8800226871400000029900004020638000352739088a48916e51cd28aadccce9d480007d200012e0001ab0c447c60001f8c24e0004d660282ba0c88be00000003d52b294425987410bc05708b004f053848e29c00052c80002c95e70776524acd3523781ab8eda0003caa4983f6254a91c624000858d4d170c0002acd0569ff2ba3e71bf000057e4a23c9a3b20008ed800242803607f0002928bd15132c0c2bd5640d2086c864f3c0d44a300000009270b516b8e8c0001f163fa9b203f30a29c07621054c205483b459f2400c10bca212cc556840cf6bb2ff158d55887901ea5e860a8448e68fb8a9138d367a03800000045d1790d669db23600f00006a700000000002ac2e1d5a865e00038cc00068c2aec6426606ee9ae19c8d4ae964e40368ac64443745
  | 22 => 0x800000000000049acb8f51e0002038000e2a0000fb000018c0002e49b6811180480000012ce00029845d526648d1bd99880000003d4800021d0002e0c00058a0002b200009bb2c700000008b60000001d24f58570b3a8e6d15119300012e158001925409065225ac85884e13df25ccd542c95b86b5800000000094c00009752589353c30e8730a2e080000003848ad3de1e00ca685bc19ce827b283804f87fc00040407182940003e634f26bce80a01b8c9949251294ad4d4be88e93254ba4060009888000c8860665d0000000afe8558000000f62875000000000000031e060c00047856406e81a60bf511000000000016e800000028e800000068200010f0c7127e00000000011c3a2532c9e5c1d87cd9279680ee84578ff4000e3400000a8000b480dc196000000086b000092e0005870c680006e67288000dc14af36d000031139a08905715e000000026ba37e0007f200000014bb8532824db3420000409a1b12b622f1f6a2aac1934c3be2400000427b05de02c0b1e12aa0daf1220f98ce96354daa55081a29c3c502ca248f6c0006764cd662662e00000007594f6947c4340383076f137ca9151522ff3c4c6b088ca350000392d1c9449dda7440000388e3e4e492b9a3108d21ccda85982227b4fc07f3b8e8798b011002c59e2c5d25a62c897ec6540c020d17c743c8c43620b4288217011b8ad88c6445384a10ed481eb396109497662b00007b466674c3e4064078200042ba00800000000000005b84014108000b1e00051f2984778000178835d50100018c97e041d00025f8e2c1d264044fe755154ad1426a6e0000181b9d80012c44cc135156400018c800090d2760000000f893dd8a515c80009be0ee000245200000010e51751b454e16f50f8000000394aa400000652c253e492547e29b496a36ea144a288b80566cc1f04d5c7301291a3a66623c8491579a11434003101a69110361707214df0eb1971f4291a8be63b16900000005f700017a000014c3fa090200005731a8f802aa0004d4d60078c2f7bd086ccbae3cf55a000000089c000000108071b800000000000000000009d400031400010568d306966f87989a02bd800000064c0ff19e427a9bb00000000003dd00009840000001d4000137900028f9ae91769ba4f78aa8db70002cfc668b2e8193ef8a300000e680f25c800042024e105d0b500053f14e04fc6263b09cb43a6a1b41c8ae24f15b0000001c00049400000013b872c95fcfac00000033a2ae68c290728d195859237535658340004238002b24eed08516100010dc29f0608f246885da82810e60d649721c076d48c9e4b1f23ec0000000001110000000400800062471b36c0000000126255800016d5810002a4400000000008080004c212800000000fb01200007be0000000000ec950f0002abc0004f4098a6a4
  | 23 => 0x90500004a99c44ffb22a2ac483cb501013a20000f0aa3cac724140128e127c096078594e2950dfc19a52f0001d1d232000000274e17429d23e10700000c80ca40014b07690fee92600092308120940004d61f9177d53a4ef54f9bab0b65f93cd8a1c5372561595f9c05000038b06a09687d2d53dcc4acc3ef0001ba8cd4ab8ce999a48510001f50ac000000019f8000000000143010400000025f000086a9fa81b10eb15e7de418684ca361332fd29da1936862e3800000084f1c106b828073e49501455939e23d106ee000511219a0bc0004da085da093960df000169eacf00004a247eb586e880d293030a60a3cd00002a604e2cc9fcc342000323926c61600000023c00000000001ad00004729129588a3a944320aa76000000000286a0003a3000118800074f535ab7c35a805053dccc000000000195c2840000fe90e40003ef923873155d232953aa4c20e83a4f39f29495a2946720f00004893af092233d6f534880001f70000ebc4e4c272b256b00000002899830000af867f31600180000004f7090a0004f20f5e3984ef0001d64268e3e482c3c45d91b60003bd80000003540000aae02359980000bcbe75505530990000000024a80800000028e0001053000515432800025156c000073a908129ab6c4cf1912b41e9ca08000161966c0f48a054a003039000017800008bc3901fe80b040ca5044cab480002e5a8f000000000047a0b1e0000002072698000274d61a958a144182c1931800000039922605330b8d5e0000000038356e85634662419f26f41ec00005bc000a664bd24c2ae855672f4761ffc00011f95861f45ee2eb3f4822714c8dc26c043405f09ad3fa870a0e018041192c8a000037015428ab4c7184804c0100000dc09a4f5c28f83410313ab82cb7323b5433aad23e8f0f05c00000024dc0000003639a7000010e570000132a033488ce44324592314c000a8ba7354c4000000000000000000043c0000000000a110001d4d456000000295c000ad714b5a842269fc00008841cf0005570000f54000000160a00047a000230c6d00de22a04fc9ee414a3b87240000000001e2033600000000b745c00020ea4740008041569249332000319a47c0000398001bb8f74ab3005198cee491017722883a829230d80003b81b940c211cc60230800000000000000000000001be4a8129600000000000000007b30000add56c0001be08e0e353aa80023cc00071835300002ce00000000015058d114250f20005cd4134000db98fd43e02f52da72e30c28043440003b3209e0009740000000d8426800007bd20420b479529d1be18f0ce16dc500a0e02e04d956a9c217412682b491c30e97b470842c3fa673c10e7140a8084e7bc2bcb19cfe910034e46387b706a4d41e007446841bf546c694f56845a938754b8a272cac907c01a525
  | 24 => 0x883095f4f2ca6022e28d6000263b9bc00149e5674c8a7cc00000037780001b6000000149a33070747e21ef2fc00041a23d83c800000024c00004241599fa676e36b175104caee6d2251982c6784ac26f6a2ec1f81bd2e85b40006b6b9100b40003b58000c008f60000000000353a5680019cc9900004fe58300004054dec934c5a4cfc8f06bd5c29691b616fc52e84b01ca2ac6be000000250cf300002649cc0f8299756a86d00000544e91a54f5000001112774460002f0de74c922df09d2435429806d430b04d326c04e30d4d19848f2af5a7cfba05e13193f91fc12f08f4000000aaa362c000a23a821b1a0eb4544344cbc0008da8b200021440000003a5c0013e48b92989b180008c93c900006dc4c6b18a196eca207166e2240000428b41f10b7fa3d11613c55c162888d8e500004269df000154210b018085cfc81cd91a800021000000027fc3605931e19a600009b73fc035518a931b4161df0d08f52d50b59407000128c0000005a200000011049ab95a00000000703011fb4ac0866268aa48000a6480013ec8cc0003b8000036a0001449e1c58c5363e629469dd7b83f6150713500026e1f6d1e289e3e4975b12ca991361dd46f22ca000235832c00032d9a6c6705d22cd00008ac06048d2b080000000000bd938b00027025bd49a00029b86565fb3a600027d4348a5580003c547600016be5b892900007fab141085dc1de80002dc000389aa900008ff27700001b4529341988c02c79c1ee21e65f8954000000000094b2bb18d091488d505800000070d000000082d0004ba93729634a1547012b4e79a517099100744914988ab8cc8502457c0015948f734b18710e29c544aa8dca7a3230a7a2fc1982d42cd403e0f798d0de40001727c004948343ff9de3aa25f000077329240014cb1e0275c00074e0e03d69aa80009c69c38000df66b23b891e4e7180f00011bd23b8b042700000000000000000bb9ada0d39bd81e43b440e87280000002b94abe0000b61262a3000000035f97d01958462e414ad10ea812b8e1a8c11ac756441a8d260c30001e3c1e01b1432436b1530002da9ca8d02568cd3867f54b933b1285e4b723f62d9c7f0b7ba3c43097d84f88dd48c04920000003d90fd000085d00020f20001d880962741020002bb425800010c3d29c5cf3e00042c000159885480029b063c9aa422a7f93105ba03a000017c76a9cc8bccdfa80012b89fc1101ec18ea6044e200024228625ae5ea38127740be0d600000003ea3df8e5a5202764640000c1cf8a0001ff0000b4a89713ccc0491c09b52fc5ac69425399e9b2f4d47030000ab60000000001eec0000002cde6240009a2192297a5480000001e287b40004949aae8e74a5162e0704100fd12e0ee00000000000396e4f000515dd9d0f40000001aa03867914329ef40003644f4176
  | 25 => 0x4dc57bc2569bf19099784daac79e416d83e02234d4059416e8d70f91df87747624c900005789f8000232c000adf8000000300610824000134250e82ad76538e6c1000088066e55d4ef80000005558059784cf67d904582e12264cf2af1a415164e254c01e546210ccf0862c0006450000f1004c239362a17c0000000f26a8cfaa5a31070778ac300020a8000a2400025227380009b10001d29278042000086c3e72bd881c000000add01a0f37044265800142c9667f54eb0000ba288f2fe05d00007ce4a68f760003c736f08cc8226110000000dfe6eb0001f58000000000175856a11a1f89af0640a874e4000000005d2d3a1485a6900a0be1780009d2c16a66816059c23597ee355a77cc99f0e9f844e038c79ca8a16fb7280000002008000000e00000480a334000ade4320000dac00040b950426e62100000006142e44bd8000e029f0500258c6f452137100080004e102c0000f86273357400089a0000001b327a4000000000000061183b00001297f92261c7000024600011a0000abe0000000a850004250000bc70000002b6424139a00025c4a300c515f0be904c00000027d80005ab00027910d200000000010760438250a074fa000469562b5069988740fa40005d83ea00000006a50e7510cb130ab1d692c51d062aa80a1c14e949f4138788459ac5c6f000001e00052a66b00f6696800252895a2620000000a2e7122149f490888f20d94085023500538e6e49100d3b6ba33c3ee2955090000a860004ac00004629381b11204b705a0b03452415a09cb4393acae642e08a230075600003100004a400018101f400081a1f183c2a3f67a00003f8000a0c8f1d3e8000a952f5ab5b1100001df96f028a57a2ea99f00000001d01704000000000096c2e22fe93708d0ae000027aa4f8a3235b3450aa400000028197ab4487363ab80002d83cd0fca12e2c85b34c50be0b7a73417d4a8800000000024d8742a0c2a1dadc626000224030802135e32a97620000c0b3e9ffe45d04bbf2a55ce2022f9a8d6fa6ac08d13a96085166364759728a9202553ad0591a91514208324fa328a109249620c75124ea048d7207cb3309809f57e
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaad84cc262040071e902ba2c40800e3ba1f425881025e7238c84b1020038ec8750962040959c8e2a12c40800e3ba1f325881001d7340e64b102045ce471cc9620400155d08192c408002ab61032588102467238864b10204bce471dd162040075cd033a2c408002b9606745881000573c0ae8b102003ae4815d162040959c8e2ba2c4080038bd52545881000716aa0a8b102000ace83151620400159b062a2c40800eb9a06735881000572c0ce6b102045ce4719cd62040075c902b9ac408002aba10735881000556c20e6b102048ce4711cd62040014dd0a21ac4080029b614435881013e7238ce0b102026ce4711c162040014dd0ba02c4080029b61740588100056741e80b102000acd83d0162040011dd0e202c4080023b61c40588100055742660b102000aad84cc162040075cd02182c408002b9604305881001c6fc3ac719020038dc83dd932040071e902bb2640800e3721d634c81001c7643ac49902000cd563dc532040019cac5b8a640800eb9e1d62c841000476c34e51802000cae649ca300400195ac9394600804f3398e728c01000666b1ce518020008ef865ca300400195cc8b9460080032b591728c0100866731ae51802000ccd635ca300400f1df0f31460080423b61e628c01009c77c3ac518020108ed8758a30040019aac6b8c6008012b6201634c01000764182c498020038f4815db20040499ce42bb6400800e3be1d628801013d7240ac51002000ce5625c6200400517909bb240080063720f764801001c76416ec90020288f781dd9200402317b0dba240080030f99774480100064f31ee8900203acae62dd1200400117d0eb2240080162f21d64480100061fbaac89002000c3c755912004001938e6b22400800f2d1c564480100846ec36e69002000c9e64dcd200400193ac9b9a40080e73398b73480100046f43ac690020048dc8758d200400193ee8b1a4008003271d1634801001e6a38ac69002000caf745892004001958e8b12400800333dcd62480100066639ac49002003ce471589200400196cc9b8a40080032d59371480100066b31ee29002000cd563dc520040519ccc5b8a40080033958b714801013cf343e429002028ce776c8520040071db04bb0400800f359c563080101357240ac41002000cd5635c4200400f9ccc4b8840080032d1d376440100065bc26ec8802000cb484dd910040019af07bb220080033520f764401000673c16ec8802000ce482dd9100400196eedba2200800335ddb73440100066bbb0e688020269e687dc910040019ceedb92200800339dd87244010006d3ba0e48802000da4741c91004001b8ee63922008003711cc7244010134f3c30e488020269e5861c9100404db4cc8392200809b695907244010136e3318e48802026dc5631c910040519ccc0392200809b789807244010
  | 1 => 0xc9b8262880032e190704c5100066db18e098a2007ce8629c321440019d6c438242880032bd92728c11000656324e51822000ccf639ca3044027998c739460880032bd91728c11000656322e51822000ccf635ca3044021998c6b9460880023be1f628c11000476c3ec518220078ef8718a30440011db0e31460880af351c7634c11013672388c49822000ce462dc5304400f9c8c4b8e40880022fe1176481100145e422ec90220008df835d920440031b906bb240881422fa1b74481100061e32ee89022000c9c63dd12044075958c5ba2408813e2fa1f64481101645e43ec89022000c3f75d912044001878ebb224088003271cf64481101665a38ec8902202a8de86dcd204400193ec9b9a40880032719373481101ce66316e690220388de87d8d20440571b90fb1a408800327dd363481100064e3a6c6902202bcd471d8d204400195ee9b1240880032b1d3624811000667b9ec49022000ccc73d89204404f9c8e3b1240880032dd9371481100065a326e29022000cd763dc520440019a8c7b8a40880a33918b71481101665b3b6c9082202bcd676d8e10440039acec31c208809f399db628411003e733b0c50822000ea76418a1044001d48c83142088003b1d8c628411000762318c50822000c3f759d5640400187aea3aac808002a7a0c75590100054ec18eab20204eabb805cd640400157100b9ac8080028fa1473590100051ec28e6b202000e1f5394d640400117d0e29ac8080022f61c535901026d5bc0ae4b202003ab4815c9640400756d03a92c808002ad607525901001d5b40e64b202000ab581cc9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640409956b03382c8080162fa1f50590100045ec3ea0b202000a9e83d41640400153b07a82c8080038ed42505901000557410a0b202000aad82141640400756d02282c808002ad604505901002c5f43e60b2020008bd87cc1640400147d0b982c8080028f617305901001d5b40860b202000ab5810c164040011f100ba2c60800e37a1f4358c1001c6e43a86b182000adb805d163040015b100ba2c60800297a147458c100052ec28e8b182000e1f5495163040011bd0e2a2c6080023761c5458c100070eaa0a8b182003ad4815c9630400153d08392c608002a76107258c1001d6b40e84b182000ad581d09630400159d05382c608002b360a7058c100246f43e80b1820008dd87d0163040014bd0ba02c608002976174058c100056741080b182000acd8210163040075ad02202c608002b56044058c1000717aa4a93102000e2d54152620400159d062a4c408002b360c549881000537428873102000a6d8510e62040014dd0ba04c4080029b61740988100056741e813102000acd83d02620400f1dd0e204c4080023b61c409881000557426613102000
  | 2 => 0x464989100061eba8c93122000c9e73192624400193ec8b9cc48800327191739891003e66312e73122000c9e74d8e624400193ae9b1cc488003279d063989100064eba0c73122000cae74d8a624400195ae9b14c488003339cf629891000666b9ec531220028be86dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c73191624400193ec9b9ac4880032719373589100046f43ec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100064fba0c6b122000c9c7418d624400187eebba2c4880021fe15745891028c3e42ae8b1220008df835d162440031b906ba2c4880023be0974589100047bc0ae8b122000c3f751d16244001878ea3a2c48800327dd373589100064e3a6e6b122000c9f741cd6244001938e839ac4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880032ddd371589100065a3a6e2b122000cd773dc562440019a8e7b8ac4880023be1d621891000557c22c43122000aac84588624400159f06b10c488002b320d6218910006573b6c83122000e2f65d9062440011db0f320c4880029ba16641891000536c2cc83122000ace83990624400159b07320c4880023be1d641891000537c2ac83122000a6c85590624400159f06b20c488002b320d6418910006573b0c83122000e2f651906244001c58ca320c488003339db631891000747b26c63122000e8c64d8c62440011db0f318c488002aba12631891000556c24c631220008ef8758c624400155f08b18c488002ab2116318910006673b0c63122000e8f6418c6244001d18c8318c4880038bd52541891000716aa0a83122000ace83150624400159b062a0c48809ab9a04541891000572c08a83122000a6e8510c62440014db0a218c48809ab9a04431891000572c088631220078ee87d0462440011db0fa08c4880029ba17401891000536c2e803122000ace83d00624400159b07a00c48809ab9a07401891000572c0e803122000ae781500624404d5c902a00c48801e3ba1c401891000476c38803122000aae84cc0624400155b09980c48809ab9a07301891000572c0e603122000aaf84440624400155908880c488002b3e0d10189100056641a2031220008bf845da324400517908bb4648801e3b209768c9100145f426ec99220008bd84dd9324400117f08bb2648800a2f211764c91000477c12ec99220008f7815d9324400f1bd0fb1a64880063ba1f624c91000477436e498a2000caf64dc93144001958c9b92628800333d8f724c5100de6631ee498a20008ee861c9314400195ec839262880032b190724c51000667b18e498a2017ccc631c9314402f1dd0fb12628806e3b21f624c5100dc77438c498a20078ec87189314400197
  | 3 => 0x1b222000a9d83d43644400155d04286c888002ab60850d91101645f43e61b2220008bd87cc3644400147d0b986c8880028f61730d91100146fc3a87b1a2000e1f65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc825936344001c3eca326c6880038719464d8d100052f42ce9b1a2000a5d859d36344001c3ea92a6c68800237a1c54d8d100046ec38a9b1a2000e1d54153634400153d09396c688002a761272d8d1000567416e3b1a2000acd82dc7634400159d05a0ec688002b360b41d8d100054fc22e1b1a2000a9c845c363440571bd0fa06c6880023761f40d8d100052f42e81b1a2000a5d85d03634400159d04206c688002b360840d8d100064e31ee8b1a20008be87d91634400187eebb22c6880030f1d76458d100045f438c8b1a2000c3f751916344001878ea322c6880032bd937258d1000656326e4b1a2000ccc63dc9634400195ec8392c6880032b1907258d1000666318e4b1a20028be87dd1634400187eebba2c6880021fe157458d1028c3e42ae8b1a20008df835d163440011df04ba2c68801e3b2097458d100047dc02e8b1a20008be871d1634400187eea3a2c6880030f1d47458d100064fba6e6b1a2000c9c74dcd634400f1dd0fb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000ce472dc56344001970e9b82c688003279db6418d100070fb2ec831a20008dd8799063440014bd0b320c688002976166418d100054f424c831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100056dc02c831a2000a9e86190634400193cec320c68800387d946418d100070e328c831a2052e9b1019063440a5d3020320c68800a3be1d42d89100055742065b122000aad840cb6244001c5ecbb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000e8f64d8f6244001d18c9b1ec488002aba1263d891000556c24c7b122000aaf8458f624400155908b1ec488003a3d9063d891000746320c7b122000e2f549536244001c5aa82a6c488002b3a0c54d891000566c18a9b122000aae849cf624400155b0939ec4880029ba1443d891000536c2887b1220008ee87d0762440011db0fa0ec4880029ba1740d891000536c2e81b122000ace83d03624400159b07a06c4880023ba1c40d891000476c3881b122000aae84cc3624400155b09986c48801f2b18974989100061f3aec93122000c3d75d92624400193ce7b24c4880030f9d
  | 4 => 0x480019cae430c6090003b10c8618c1201ce66396c69824000ce77218530480499c8e430a6090003b40c0614c1201d6573b6c91024039cce76d8e204800399cec31c409001e3b219718812013e7230ae31024000ea7641862048001d48c830c4090003b1d8c618812000762318c31024027ce58718620480019cee830c4090003395d0618812000673398c31024000ce473186204800f1d904ba2c2101163be09764c42003c7a43ac29884000cac74dd920080019d4a1bb240100033a543764802000657bb6e89004000ccf76dcd200800199eec39a401000339ddb714802000673bb0e29004000da7741c52008001b48e838a401000371dcc7148020006e2398e29004026ce6861c5200804d9cb0c38a401009339d90714802000672b20e29004000ce6631c520080499c8c638a40100937898071480201347643ac29004026ce47158520080010ff0aba2c7881461f2157458f1000477c12e8b1e20078ec825d163c40071b90ea1ac78801e3ba1f7258f100066741ee4b1e2045ccd83dc963c40071bf0eb1c65881163be09764cb1013477c3ac59062003ce47158920c40a30fd0bba6c7080021f61774d8e1003c77416e9b1c20008ed82dd363840051bf0ea1ec70801e3be1d72d8e100066641ae5b1c20028be87dd1628400187eebba2c5080021fe157458a1028c3e42ae8b1420008df835d162840031b906ba2c5080022fa1c7458a100061fba8e8b142000c3c751d162840031bd0fb9ac50800327dd37358a100064e3a6e6b142000ccd82dcd628400193ee839ac508003271d07358a10016563a484b1420028ec87509628400155b08192c50800333dcc3258a100065bba6e2b142000cb474dc562840019aee7b8ac508003351cf7158a1000477c3ac431420008bf845da328400517908bb465080023b60a764ca100045fc22ec99420028bc845d932840011bf06bb265080033658c704c61013c77c3ac590c2027de0219c321840491ef0cb8643080027961f6208610135f1406c410c20038de87d8d30840013cd0f90a41080023be1d6208210144f2412ed88420008bd87997644400147d0b32ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec8880022fe1d65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100051f430cbb222000c3e76197644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400187eeb3aec888002a7a0e75d91100054ec1cebb222000c3d751d7644400147d0b39ec8880028f61673d91100070fa9ca7b2220008be8714f644400117b0e29ec8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c888096aea0371d911000557416a3b222000aad82d47644405917d0fa86c8880022f61f50d91100054f41ea
  | 5 => 0x3b118f3218520005734306430a4000ba5840c86148001d4ec8190c290003a9190321852000763b186430a4000ec4630c86148001c6ea92a0c290092b9a0a541852000572c14a830a4000e355415061480015ad062a0c290002b560c541852012573410a830a4000ae58215061480495cd05a18c290002b960b431852000573c128630a4024ae48250c61480014ed0a218c2900029d6144318520125734108630a4000ae58210c61480975cf0f210c29012eb961e421852012573c2c8430a4000ae5859086148097d4ce9210c29012fa95d242185200057341c8430a4000ae6809086148049d4884a10c29012ab9e1d421852000573c2a8430a4000ae5855086148049d4f08a10c290002b920d421852000753a1a8430a4000ea54350861480015c900a10c290116b961f321852000573c266430a4000ae584cc861480015cd01990c290122b9e1c321852024572c386430a4024ae7840c86148049d4d08190c290002b9610321852012752c206430a4000aa5840c86148049d8d06190c290123b19cc321852024762b986430a4000ae6800c861480014ed0ba00c2900029d61740185200056b41e8030a4000ad583d0061480495cd05a00c290002b960b4018520007532148030a4000ae78250061480495c904a00c290092b9a08401852000572c108030a4000ea642100614800156d09980c290002ad6133018520125734166030a4000ae582cc06148001d8864180c290002ade1120185200055a4224030a4000ad78348061480015a906900c2900022fe11768c5200145e422ed18a40038f4815da314807399ce5b1c629000f39185728c5200145f426ec98a40008bd84dd9314800f1d9043b26290003330c8764c5201d656396c898a4039ccc72d8d314800195ec9b9262900032b193724c52000667b1ee498a401bccc63dc9314808b9c8c3b9262900063da1f614c52014672396c298a4000cac649db21480019cf033b642900032b9db64c8520006673b6c790a4000cce7618f21480019ccedb0e4290003a9d9061c852000752320c390a4000ec7631872148001d88c630e429009f3918670c85200045e432e910a4000c3c655d22148001938c6ba4429000f2d18574885200045ec3ec910a4000c3e75d92214800187aebb244290003279cf64885200046e432e710a4000c9f645ce2148001938c8b9c429000f3518573885200046ec3ec710a4000c9e74d8e214800193ae9b1c42900032d9d361885200065aba6c310a4000cd673d8621480019aae7b0c429000f3c186708852000679b08e090a4003ae686d852148001d4ec830a4290003a9190614852000763b18c290a4000ec4631852148049bc6e238242900eb2b9cb648c12000656b96c91824039cce72d8e304802199ae5b1c60900a3399cb618c12000672b96c31824024ce6721863
  | 6 => 0x55ac2063b0a4000e3765d9361480014ed0b326c2900029d61664d85200056b41cc9b0a4000ad58399361480014ef0ab26c2900029d21564d85200056bc1ac9b0a4000ad4835936148001c6eca326c2900038d19464d852000752c10c9b0a4000e9764d8f6148001d28c9b1ec290003b160b63d85200055b424c7b0a4000ab58498f614800156f08b1ec290002ad21163d85200074bb20c7b0a4000e946418f6148001d48c9216c290002e961032d852000763b1865b0a4000a76859d361480014eb0b3a6c290002b5a0e74d85200056ac1ce9b0a4028ae6821d361480015cb043a6c2900038dd5254d85200071aaa0a9b0a4000ad68315361480015ab062a6c290002b960b73d85200055b424e7b0a4000ab5849cf61480014ed0a21ec2900029d61443d85200053b42e81b0a4000a7585d0361480015ad07a06c290002b560f40d85201457341081b0a4000ae582103614800156d09986c290002ad61330d852001e5a30ae930a4000c3e75d92614800187aebb24c290003279cf64985200061f3a8c930a4000c3d75192614800193ce6324c29000327d9173985200064e322e730a4003cd4615ce614800193ce9b1cc290003275d363985200064f3a0c730a4000c9d7418e614800196ce9b0cc2900032d5d361985200066b39ec330a4000cd573d86614800517d0dba2c2900022fa1f64585200061fbaec8b0a4000c3c75d916148001938e7b22c2900022fa1c64585200061fba8c8b0a4000c3c751916148001938e6322c29000327d9373585200064e326e6b0a40008de87d8d614800193ee9b1ac290003271d363585200046f438c6b0a4000c9f7418d6148001938e831ac2900023de1d61185200055bc22c230a4000ab48458461480015af06b08c290002b520d61185200065b3b6c830a4000e3765d906148001d4f05b20c2900023d61e64185200053b42cc830a4000a758599061480015ad07320c290002b560e64185200047bc3ac830a4000a778559061480014e90ab20c290002b5e0d64185200056a41ac830a4000cb6761906148001c6eca320c2900038d194641852000752c10c830a4000cd676d8c6148001d2ec9b18c290003a5193631852000762c16c630a40008f58798c614800156d09318c290002ad61263185200047bc3ac630a4000ab78458c614800156908b18c290003359d863185200074bb20c630a4000e946418c6148001d8f04318c290003a9d91721852000752322e430a4000ec7635c86148001d88c6b90c290002b9a1a421852000733b2c8430a4000e64659086148001d4ec9210c290003a9192421852000763b1c8430a4000ec4639086148001ccecaa10c29000399195421852000753b228430a4000ea4645086148001d8ec6a10c290003b118d421852000753b266430a4000ea464cc86148001d8ec7990c29
  | 7 => 0x3d859c7644800153d0738ec890002a760e71d912000557c12e3b22403aaac825c7644807555d0438ec890002ab60871d91201d557416a3b224000aad82d47644800117d0e28ec8900022f61c51d91200054f418a3b224000a9d83147644800117d0e18ec8900022f61c31d91200051f42863b224000a3d850c7644807517d0fa86c8900022f61f50d91200054f41ea1b224000a9d83d436448001c76a1286c8900eaaba0850d912000556c10a1b22403a8be87cc3644800117b0f986c8900028fa1730d91200051ec2e61b224000cad7219363480011db05ba6c69000a37e1d43d8d200070fb2ec9b1a4000e8e72d9363480014bd0b326c6900029761664d8d200056b40cc9b1a4000ad58199363480014bf0ab26c6900029721564d8d200056bc0ac9b1a4000ad4815936348001c3eca326c6900038719464d8d2000746c10c9b1a4000e8e72193634802199cecb96c690003a3d9172d8d2000746322e5b1a4000e8c6490b634807359d05ba6c690002b360b74d8d200052f42ce9b1a4000a5d859d3634807359d043a6c690002b360874d8d200070faa4a9b1a40008de8715363480011bb0e2a6c6900038755054d8d201ce67c3ae5b1a4000acd82dc7634800153d0938ec690002a761271d8d2000566c10e3b1a4039ace82d07634800159b05a0ec69000237a1c41d8d200046ec3883b1a4000a5e8510763480014bb0a20ec690002a7e1170d8d200054e422e1b1a40398de87d0363480011bb0fa06c69000297a1740d8d200052ec2e81b1a4039ace82103634800159b04206c6900032718f7458d200045f43ec8b1a4000c3f75d916348001878ebb22c6900022fa1c6458d200061fba8c8b1a4000c3c75191634800196ec9b8ac6900032d1937158d200066a31ee2b1a4000cb7641c56348001968c838ac6900033518c7158d200145f43ee8b1a4000c3f75dd163480010ff0aba2c6901461f2157458d200046fc1ae8b1a40008f7815d163480071e902ba2c6900022fa1c7458d200061fba8e8b1a4000c3c751d1634800193ee9b9ac690003271d37358d200065bba6e2b1a4000cb474dc563480019aee7b8ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac6900e733a0a7618d200064f3b6c831a4000e1f65d9063480011bb0f320c69000297a166418d200052ec2cc831a4000a9e8499063480015ad03320c690002b56066418d200046fc3ac831a4000a5f8559063480014b90ab20c690002b5e056418d200056a40ac831a4000a9e86190634800193cec320c69000387d946418d200070e328c831a4000e8d821906348001d18c9210c690002b32194218d20007463228431a4000cdb631c132480051ef0ea0ec2900029da1441d85200053ac2883b0a4000ad68310761480015ab0620ec290002ada1031d85200
  | 8 => 0xb3a2c5180029b6167458a300856741ce8b146000acd839d1628c0015cd033a2c518002b96067458a3000567c1ae8b146010acc835d1628c001c5ea92a2c5180038b5505458a3008567418a8b146000acd83151628c00155d0938ac518002ab6127158a3000566c1ce2b146000acf835c5628c0019cae238ac5180023ba1f4158a3000476c3e82b146000a6e85105628c0014db0a20ac518042b3a0c4158a3000566c1882b146000a6e85d01628c0014db0ba02c518042b3a0f4058a3000566c1e80b1460008ee87101628c0211db0e202c5180023be1d6218a301c46fc32e1194600099f845c2328c0011db0f310c3180032b9d2621863000656ba4c430c60008ef87588618c00195ce8b10c3180032b5d162186300047bc3ac230c602a8df865c2318c00133f08b84631800e3ba0a76c863000666192ed10c6046cae625d2218c08199cc4b9c43180032b9d1628863000656ba2c510c6010cce7358a218c00199ae6b144318043331cd624863001d7240ac490c6039ccc325d8218c0071f30d38043180067620d700863003e75312e010c6039dc8325c0218c0011df0eb10c498002b920562189300045fc22e5b0a60028bc845cb614c05793ec6ba0c2980023de1d611853000572412c230a6045ccc76dc9314c091998ec392629802a37a18704c530006e5b90e098a6000dc8721c1314c0153b50c382629800336a18704c53001c6e41ced10a6040ccc625ce214c0013b100b9c42980022fe1176085300145e422ec10a60038f8865c0214c00f99ced3946098043339d9728c130086e5382e518260018dc865c6304c0579a8c2b8c60980021fe157458f2028c3e42ae8b1e40078ec825d163c800f1b90ea1ac79001eb32094358f2001c6ec1eec98e4040ccc32dd931c80a30fd0bba6c7100021f61774d8e200043fc2ae8b0c405187c855d161880011ef0eb08c31006f3398f724c6201447bc3ac310c4027de0219c221880013cb0fb084310092f8a0361086200866731ae518440278ef87587208804f9cce2b0e41100022f61e65d91200051f42ccbb224000a9e83997644800153b0732ec890002ada0665d91200055ac0ccbb2240008bf87597644800153f06b2ec890002a720d65d91200055bc0acbb224000ab481597644800147d0c32ec8900030f9d865d912000716c10cbb224000a3e8598f644800147b0b31ec890002ada0663d91200055ac0cc7b224011aae86dcb6448001c58cb296c8900026ba1c32d912000596c2865b224000c3f759d7644800153d073aec890002a760e75d91200061eba8ebb22403aaae821d7644800155b043aec8900eaaba0b73d912000556c16e7b224000a3e859cf644800147b0b39ec89000387d4e53d91200045f438a7b2240008bd8714f644806357501b96c8900eb8b94b52d91200051f42ce3b224000a
  | 9 => 0x755922100557c12e6b244246aac825cd648840147d0a39ac9108028f61473592210070fa9ca6b2442008be8714d648840117b0e29ac91094eade05725922123717296a4b244203ab681d49648840156b03a92c91080eada0732592210055ac0e64b244200a3e85dc1648840147b0bb82c910802a7a0f70592210054ec1ee0b244200aaf825c1648848d55904b82c91091aaba08705922100556c10e0b2442008be87d41648840117b0fa82c910802a7a0f50592210054ec1ea0b244246aae82141648840155b04282c9108022fa1f30592210045ec3e60b244200a3e85cc1648840147b0b982c91080eada0430592210055ac0860b2442038de87d0d63884071b90ea1ac71080a2fa137058e210045ec26e0b1c4240ace829d1638840159b053a2c710802b3e097458e2120566412e8b1c4200a5e851d163884014bb0a3a2c71080387d525458e210046f438a8b1c42008dd871516388401c3aa82a2c710922b3a1f7258e212066743ee4b1c4245acf825c963884075ad03a12c710802b56074258e210054f426e0b1c4200a9d84dc1638840159b05382c710802b3e097058e210066cb80e0b1c42008de87d0163884011bb0fa02c71080297a174058e210052ec2e80b1c4240ace82101638840159b04202c7108033558f714ca2100556c2064b0442008bf845c3634840517908b86c6908021fe157458d2128c3e42ae8b1a42008ef825d163484011f700ba2c6908023e2017458d210de6631ee498a42008fb8758060484a30fd0bba0c0908021f61774181210043fc2ae8b18425187c855d1630840f1d904ba2c61080e3721d4358c2103d6641286b1842038f987902600840517d0fba2c0108030fdd774580211d656396e8b00422ccb471dd160084010ff0aba2c0109461f21574580210046fc1ae8b0042018dc835d1600840187eea3a2c0108030f1d4745802127e56390e8b004250cb4711d1600847399865b9ac01080637a1f73580210064fba6e6b004200c9c74dcd6008473998e5b9ac0108af351c773580211ce67416e6b004200ccd82dcd600840193ee839ac010803271d073580211c666390e6b00422acd4711cd60084015d501992c01080b2e1d240580211d75521480b0042038f88750160084014dd0bb24c5180029b6176498a300053742cc93146000a6d85992628c001d1cc8a1cc5180038bd525498a3000716aa0a93146013ace83152628c00159b062a4c51801e3ba1f4198a3000476c3e833146000a6e85106628c0014db0a20cc51804eb3a0c4198a3000566c18833146000a6e85d02628c0014db0ba04c51804eb3a0f4098a3000566c1e8131460078ee87102628c0011db0e204c51800a3b21d4258a300047743ec8b146000a6e85d91628c0014db0bb22c5180029ba166458a3000536c2cc8b1460008ee87191628c0014dd
  | 10 => 0x800000200600000800000000600200000200e01200600000200a00400400000000600000000200000000000e00000000200202600200600800000000000400400c00000600000e01000800000602000600000000e00000000800000001201600000200800800000a00c00400000c00000400000001200000201000200800000000000a00000402400c00000000000200000200000c00400402600000a00000c00000000000c00400200000200400600200000400000400000001400000000400800200000401400c00001000001400000a00000000600e00200200000000200000200e006002002000008000000028be87dd1608c80187eebba2c11900327cc774582320064e186e8b04640087f855d1608c8a30f90aba2c1190030fdd474582320061e3a8e8b0464008f787584614c88b5cf04b08c2991533a5cb609813222e73b10e2b0264008fb87580604c80117f08b94c11880a2f21172982310145f43ee8b046200c3f75dd1608c45993e63ba2c1188b3274c774582310064e186e8b04620087f855d1608c4a30f90aba2c1188030fdd474582310061e3a8e8b0462028ef8750b624c4014df0ab26c4988029b21564d893100575c02c9b126200ae880593624c4014dd0a326c4988029b61464d893122d6643287b12621bace83dd3624c48b59b07ba6c4988029ba1474d893100536c28e9b12621bace831d3624c48b59b063a6c498916b9a0474d89310dd72c08e9b126200e2f54953624c401c5aa82a6c49886eb3a0c54d893100566c18a9b12621b8ee87d07624c4011db0fa0ec498802aba1370d893100556c26e1b126245acd83dc3624c4375cb03b86c498916b360c70d89310053742e81b126200a6d85d03624c43759d07a06c498802b360f40d89310047743881b1262008ed87103624c4011df0eb10c498922b360e761893100476c3cc831262008ef87590624c4014df0ab20c4988029b215641893100575c02c83126200ae880590624c4014dd0a320c4988029b614641893124566432863126200e8c6450c624c401c5ea92a0c4988038b55054189310bd67418a83126200acd83150624c40f1dd0fa08c4988023b61f41189310053742e803126200a6d85d00624c42f59d07a00c498802b360f401893103c774388031262008ed87100624c4551b90cb84649880267e11708c9310053d42e81b0262008ee87d89604c40195ee9b12c0988032b1d3625813100477438c4b026200caf74189604c401958e8312c0988b739dc462581310047dc3ac03026200ab884580604c4015b700a18c0988029ea1740181310056cc1e803026200ad983100604c401d3286200c09880a2fa137058f210045ec26e0b1e42038ee82dd260c840187eeb3aac91091aaba0a755922100556c14eab244200c3d751d5648840153d063aac910802a760c
  | 11 => 0xa91680dc04000149d5681903a60000000000000000000000006880010d0000000000001214000000016c0c00159d0783454d4000aac73cf3d1145be5dc0000014def9c8e400125d65524005c24d20545c0006380008676c80cad58dbd1bca31344bdea9029026c8403e5610001530f5858800111000079c0000016f800000000000000022c0006800000000007ec00000000100ce545df1fc8e8f04e7d2d85d569c9b5105414e80000af9080804d24f670d43cd4f498c64cba42e86fb15402d3c000025d6f52f87a26a8e59170000b843dc000000000bb8ce000000175025494400000007000000000000000139c0009d8000000abd69e240c5d0742f85365d60009b2e3edb4dd81f95103c47fa6f20007cc0000013214c80000000940008b4000b4861a62cb0c000000194bbac54ba20004775d4fcc00048c0004c8af0000846e5b36c60519d724cbc0000000000010040010485496d4388c9015adf0c8c00000002800000a01000200401a00000800000800000000600000000000400200200e00200000e00600e00800000400000000200000e00002400000e00600200601000201200200000000200000600000000200200400200400000400400000400800c03201800000400600400400000a00800001400000600200000000600200c00400e00200200002200002800800600200600200000400401400000001201e00000400000801000001200600000000400200000000202600200200e00600000200000200000000200000000400000400600800001200c00001601000800800e00601400400000000c00201800001000000200000401000000a00000000600000000200000200200000800000000a00000601000400601c00800200000800600002800600e00000601800800400200000400800200201600200000400601400e00400800000400000200000800a00000000000000e00400000200200200200a02001e00000401000001000000000600600400000200800200a00c00000000e00801a00200000400600801800600000800a00c00000800400400800400001800800201c00000400400000e00200202e00200000000400600001600000001200200800c00000401000000000c01c00200000600003400800200600400a00003c00400200600001600000400200401000e00000002000400201a00200600400200000000400e00600800200200000200200000000000400a00000600a00000000000000e00200800000000400000601200000000001800200200800000000000000e00200200000000200000801400000e00600000601402e00801400000600200800000800400800000c01200c00c00200a00800200000400400400000000800000400c02600800600200000c00000000a000000000002008000000000002002008
  | 12 => 0x600d2ac4c6ba10689ac781688000fb00007352d4b746f0244000e4266a000fc0000d3e0007980000002a434d400544cd8000000a60000000000a94000708000e240000000c00006bd5c948cf30000bd4324000486000e4e00002061400074c58c0000f40000b73e0000914000f50da8791290977070411504bf31442006fc3b93d8b2d6046341887e00002202c0e3c0002511080000010153b42b4bf6dce00111914c8d1000000000ec8000000da40008d878852d5224bc9703c81420006161bf0c47967b800087c9f4000000114000fec0007b66c0a140005ea3da17971901b4e443e00094c75400000123c4a0bad2b56b40000fc0009c96640004d711c0010c047cfbea3ce02000000ee869800109c000000d873780004da001649150cf45980008144200015940000006dc000b980000000000006c8fb8150374e38000000b3d2c4664a98d542d84906f8fa80008d513c8a86d80804ec00170c000b6c9fc000ab4a5ce849a60000006d000000000000126c3a00000000000014490d80011dc0000006ac0014993dc434e9c2a0f0c645364898b7c000000cf20000013240000000002fd35c2bc9bc8fc000000ffc90d1e4a68a1c9204744190e95e483056ec85354be2fd47647f2d492e13410506100007a4aa000000000068400000000141ca1800079200000000000007cac8000000000000bc55780000009b09f8c652c00006181746e8870ef842ea5800075c0e5650bc0000af4000b1c71c0008bc1e4f9ed1800000054c044000000ac4000670000000f62f38000000d70bce92c8640000009dd27cab142c00005e0000000009c40006595b400000000000113800026400013c000000000000000000000000a560000006d420400098053c2881200002c8ef6098e1c10cacc0b4c1cb640000000d4f2d130f203661a8ba6000000000000000000398000000e661a536115c2d0696000dcc0000001b8da042498800000000000096e00165c0000971d80016e80002d400000000122c0a11990c800121069a00000068b0a54dd1e87256214460012c800144400034866c0000b200000000000103e0002c455e000000000000000000000ed80000000001d44f88580008b80000011e0000e00f48000000000000f24104d9a6410060000004a2000d840014daf710f52a4d10b508f420635d6bc552000000001614c3e000000164000000304001684000b4400000000000000000000000000049400100f4c4000390000c5e00078350130c0010cce14b0000007446c5e8f451a0b24000000000dfe0000000010a20000009d4642359124000000d8364d66c184fdd5b93101340012942494bcdb8b34590000f4104c0000004ab458000000f1c4f05bc00000000000000084d2dce5c0006ed50cbe153c0000013b0000624000000b720000000000000000011
  | 13 => 0x4ae5f0a811f8000000d7c6f7644d974307fc5c4c3b6029ec284f6d088d0e0006e400078ca8800163c00000000089d3d496d2cf3cc56c1100000000011896280008ac00061c9040016d80009a0d3c000eec00000005972d0b6000c2942800095099400072c000334000cf00d0000b586ea0000000cc97842c394000000000fc93980000009cc000472000001190d2a01091c00000000125457d7393f80006b11f53e4000000498a7157053ab68eeed6c0008060012620f0ad40c4a200000016355f8a000010a8001548000c1439c000ebc8cc7315ce0000008ec000e9000020ceb845932918400000000054e0000000000000005fc0000012380634f0dec000000000000ae400009200120cefc6cc365440c4d1ec00096a000c943b2a3e7380002f000000108c0000016c091000000000000164030c00046800000019800120800000072ee1e000000000000a28a55740338001574001704ef535893d5d0f18000202e9400000016000098b0bc000001100d14000000456000000d74000ed0371220f5c000000de05080006e6b14000c10e74000ce85f80017442cd4ec0015800000000000002a8be403ce3742efae000000000e520015593ec00174c000a8c0012507e6001560154000bf8924000270e0c000f080b16f0000000eb03d40011ac0001000000000014380000000012d2ea8228000d76e11630000000fd8742a353680e00008c0cb011cd98000000000e880000000000000000000012e65ece184a60002140000001480000000015a00013d000000068c0000000008a4d0c1e8808d8c0e6bc87f13840004ae280710a0ceea0000049a438e8b0012c6c2b0940550000e2d058a406e3175298ee7164d34000cc143cdfd278000000ea0c58a4c0000000000009e0000d800000c60004b5314514cb415c884e32db07610ac000000000ee0574000d0a000000cf86ee08c000fe8000b3103c1080840011285654106234507c04dcbf4f954b460e29c000000000e04000000000000000000000000afc001390d394c063c000000000000000140dea000001464ead33cd9c0001300000007c9658384750cf75a4000518000ce40000004e4c42000000000001274908000000cd4000068000d614ac000000e46580c385e4bdd5c48f0301723480b18c200000003b0000f14000e720000004d800109106c000000000000000cb975867707c0002b80014b000129ee7752000053502137499c0000000000011c9702156f10000d728c4d260003414e902c55cc9cf64b0853065f624298bb0d6a0010e00005289da000f9802b0940000000000016a40000000007d43ae41432d5840000000000000004fd51ec08a10000fe0d6400000000129c954e50e0e3c2f556b94684520000014a5564fc6000a5a76cefb54c0000013896b08280000000014cd7430e541
  | 14 => 0x5e26b80000000014d8aaad5cd52429180000000001270000ee4328000774000701062030000bd0bec5844b04cd0191b514132cbf0c4724c3ec5b8bb46c51d40015fcc401c4e60f2960d5f6000fba2ad52d4d0000f84c2d1c0000000ca85da000001478000cc8b54c4a5f51211600000001fc04ce652f52d0000d5ab1e00056b5346300010f84420eced4c755ac00000126400000088c3600008245b5404000b4c0e92b0a515394a000000142134c00000000038c1bc0004d40011cc3100007c5370fa00ad508ddf6d138c00000000128083c0000000000000000003202680005040003e8000000000f8d4740000014f82740089c20000006a16a00004d0934eb40000000009f0b5c0000004e82f4f68000e780aa0000007ee000b40000df6000000000e8c5386213510ec001720000bbd424000e34a387860000000000000011a56789beec0996d697010f12e45af29b4b867c7a000006cd88000000000000000834000000850e09518000dd400059e000001042000dc8000d0800000045c000f900009300003806280000015bc170860000650478001288000001540fc52fe000168000bd2ea5302000000ff83b47484328f8000000000d30000000000000001352662dd00010dc7e80002787b4402be894895cdf8e30b463d082a0000007f819d6a80000000354545a5224714b26000000890b80cdc0000000000006080000016612580000f90988952a80000000000283511f0a6ca840000000000012e8a24ff614c918000000aa8de55e8001412d5000067e7024a81c2b220000004ba0003c07e4450bfc36a001708000fd05a000135655a000ae0ed31c4c2485454001c96860a000768a42000b8a000e203f86940004c40007286cb5440000004b81f40000001ac1cca7abd8000de68190243ac0000000000000016a2000000238000050000aa6d4e44960054728d030d015e0408000fbc9aea44e443152f6484000000000bbeb10f06ef0c78124cd12f24615507473a83f4000c983542e0d227d8d2850065c0000000000016067b09d06e0f6000028c000648000000000632838000b947f556c3bc7ad4080000000000005d2000000e6c000ccd6c555c00084400168c000000001158139418e4c4a41188800900a92610fc82ec5b7341f14844b7668c6899957c0003e03d800043cfe4000521524b9d3f40000005240bc0180000380006692bce40d3a00000000000000000000000110c00000000000097c001554d40adc000848000000000ad8cfa554ab800140c0015c00000002dc00060d5eaa496ac0000000000007580a60000000000005c800027c0013b8a2c001670b2a36c0000000000000000000001280009a8542de800000000121901c001494656740778000ae8000c48000fb50080000006757493488a0000000a92000000d12889
  | 15 => 0x868c30f880000013a0dda0003190340000000005c00014fc720000c7c4888c8ca0000000f3505d5285a81c000171c0001d000151c0009900008dc00004600085d44c9e400000000040c46437c000000000000601044000ededf29592cc80cd950a0000960558800001002d78c000000000005701ec49c5e0770b216e0000000d04259331690cc479e7d05aa000c18e3a510000000000000667694ff4b70e28000d2c9283f03fc05400161266000000000044000137c234b0600017c0007e30b4b90595028e9a9847a800109f3803a4718ec422a0b8001727084210ca400000000006474405b5dcb88e980005d8000000078b3a23022e7953c8000cac1b0000fb2a789380000015d83ff228aec0152b86904f4c3c000000000000000000000146000d4caa47af67c0000016ecb6e0003a80d8209590000fac000000ad0000f788100000c877c3a2000c60000ddcf2e024ee368081d488843268ac130800000021c0006df0540007dc7bcd1c0013c51ee00128546c00173cf740000000001b52fc00000000090000044c0009c0330c88d5e0000002ed1b000029459c000000392fce000000df482000065a000b8c0000000000004c0f3200018c0000000017300000009e8000ff12ed234f00e49061588d160005785ac0000016180004310b80013ac1060015ecd210645cc00000069c00000050c00086c0001e0f7cb28480626b600000005686b400121c000000b7912c1d800082ca977540000000013380006f44e0a7d6dc000a640000a4000d441a0000379134704296000ecc000000000a9c00000015916c7aa5cee9e5b033d1b88e0000a753f04004ac0013a4d2ebcc260000672c5160914831c98e0000000015cc0014903682e5728d66edccfd5f441cc040000de97b47d4aa936438dac4715140014342253353056cd318001698000e716e5710dc04040009a32f00015b00000013bc0006780000000000000001c800016c878c70c340015fb1946546a40000495f0a04000fc20000006c60000003091d051cb049b8000000f4c219244edb47023cc4402e96400130000072b30b62cd9000012c0000000000600008740000003c75a931cb382934e10380001dc000000000ffb7140015d2000000000000000ba93e8e6800000044525e1805c20014a60893fcc816740000014a8a0809c001248fa40004cb0b0f80b02000000cec78517d58c00118d61cb3600018a000000b8320056163814542b4605d1040001011395178000000454000000000dc418f6fd06670c000a6e0012a000000097523000048b5980000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x5442060512c36cb4ea67660ba1afb9260de5260000b71742bc40394e6549e1214d84317c00e1a9129a6459c2c547058f00a00b700cc30014d40000400022004518042ac9100e0000026e820782048c0a20e00283040028016e8880161818d0048be6154153624c401a0d5460c54d8931005836546450c624c40122f9855054189310068355183150624c40103f985d47559221006075d5831d5648840121f985505458e210060761d54151638840160d959914398a300048be6154152628c001a0d5460c5498a300048be6154151628c001a0d5460c5458a3000523650325da218c00181f7560e75d91200040fe61751d7644800128d989c864d8d2000487e6154153634800181e8755054d8d200048de61541536148001a155460c54d8520004a9e63640c86148001a2585d903218520004a9660640c86148001a25851903218520006a1613630c86148001a858418c32185200048de61541506148001a155460c5418520004b124d8550861480012659520d4218520006a120d435086148001a86736103218520006a15cd840c86148001685940c8301852000523650321d931480494e290e0676c8520005a16503218630480014a5949cc618812000607dd5839d7644400103f985d475d911000487e6154153634400181e8755054d8d100048be61541536244001a0d5460c54d89100048be61541506244001a0d5460c54189100068955181150624400103f985d47559010006075d5831d5640400121f985505458c100060761d54151630400122f985505498810006835518315262040498a47161032588100048be61541516204001a0d5460c5458810006291c5841cd62040490e4976043058810
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa816948350d4218520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x2
  | 4 => 0x4c
  | 5 => 0x4d
  | 6 => 0x124d
  | 7 => 0x3
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x124c
  | 11 => 0x138c
  | 12 => 0x138d
  | 13 => 0x8c
  | 14 => 0x8d
  | 15 => 0x128d
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x128c
  | 19 => 0x150c
  | 20 => 0x150d
  | 21 => 0x9cd
  | 22 => 0x12cd
  | 23 => 0x20c
  | 24 => 0x20d
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0x140c
  | 28 => 0x140d
  | 29 => 0x154c
  | 30 => 0x154d
  | 31 => 0xb4d
  | 32 => 0x144d
  | 33 => 0xccd
  | 34 => 0x15cd
  | 35 => 0x95255
  | 36 => 0x4b
  | 37 => 0x94055
  | 38 => 0x8a
  | 39 => 0x128a
  | 40 => 0x124b
  | 41 => 0x124955
  | 42 => 0xca
  | 43 => 0x12ca
  | 44 => 0x130a
  | 45 => 0x21254
  | 46 => 0x21255
  | 47 => 0x98096
  | 48 => 0x99295
  | 49 => 0x98095
  | 50 => 0x140095
  | 51 => 0x128995
  | 52 => 0xb0995
  | 53 => 0x98b15
  | 54 => 0x154995
  | 55 => 0x99555
  | 56 => 0xcb
  | 57 => 0x12cb
  | 58 => 0x130b
  | 59 => 0x151296
  | 60 => 0x151295
  | 61 => 0x21295
  | 62 => 0x141295
  | 63 => 0x150b15
  | 64 => 0xb4b
  | 65 => 0x12c9d5
  | 66 => 0xb49d5
  | 67 => 0x12d455
  | 68 => 0x12d5d5
  | 69 => 0x170a
  | 70 => 0xb8b
  | 71 => 0xb55d5
  | 72 => 0x3ca
  | 73 => 0x16cb
  | 74 => 0xd0a
  | 75 => 0x160a
  | 76 => 0x4955
  | 77 => 0x5555
  | 78 => 0x5695
  | 79 => 0x10b
  | 80 => 0x10a
  | 81 => 0x6
  | 82 => 0x100d2
  | 83 => 0x141555
  | 84 => 0x150994
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 1160
  | 6 => 2787
  | 5 => 1495
  | 4 => 60
  | 3 => 1
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
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (48926+((h/546+packedAt gbK7 (42920+(h % 546)*11) 11) % 1966)*12) 12
  | 6 => packedAt gbK6 (149363+((h/1199+packedAt gbK6 (133776+(h % 1199)*13) 13) % 4748)*13) 13
  | 5 => packedAt gbK5 (95477+((h/606+packedAt gbK5 (88205+(h % 606)*12) 12) % 2905)*12) 12
  | 4 => packedAt gbK4 (4361+((h/23+packedAt gbK4 (4200+(h % 23)*7) 7) % 85)*7) 7
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff807fffffc03ff80ffffffce7f3f8cfe31ff
  | 1 => 0xfffff80fc07fffffff01fffff588c8ff23fe3f
  | 2 => 0xf03ffff0007ffc0ffffe0f8039f0f0f3c3cfcc
  | 3 => 0x3fffffff80000ffffff0003e00ff03fc0ff0
  | 4 => 0x3ffffffffffff0000000003fff0003fff000
  | 5 => 0xffc0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x824800b14494209280521caa803313844e10d5
  | 1 => 0x1c92580a882947252901a1551488483920e62a
  | 2 => 0xa22cad50144ea889d2f40e01a970b0d2c34b4c
  | 3 => 0x437366cf900c10e7ca9c0063e00ed03b40db0
  | 4 => 0x83fc78f3e73f3c0183084183fdd0003fbb000
  | 5 => 0xcf0604082003020060c108603feefeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37437
namespace PEqualNP.Outside.L_meta_37437
open PEqualNP.Outside.L_meta_37437.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 3 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 14 := bs2_4_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 bs4_4_224))) (concat (concat (concat bs4_4_256 bs4_4_288) (concat bs4_4_320 bs4_4_352)) (concat (concat bs4_4_384 bs4_4_416) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 60 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1472 : Interval gbAtlas 5 1472 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1495 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))))))
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
theorem bgb_6_2784 : Interval gbAtlas 6 2784 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2787 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)))))))
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
theorem bgb_7_1152 : Interval gbAtlas 7 1152 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1160 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888eaeaeac8eac8e888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264072 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37437.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[4,5]⟩,⟨.or,[3,7]⟩,⟨.or,[4,5]⟩,⟨.and,[0,8]⟩,⟨.or,[6,9]⟩,⟨.and,[10,11]⟩,⟨.and,[2,11]⟩,⟨.or,[0,13]⟩,⟨.and,[1,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37437

open PEqualNP.Outside.L_meta_37437 in
theorem PEqualNP.Outside.L_meta_37437 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264072 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264072 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
