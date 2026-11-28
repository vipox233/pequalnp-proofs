import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40411.Model
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


end PEqualNP.Outside.L_meta_40411.Model

namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
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

def SBf (j : Nat) : Nat := [6, 7, 6, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_40411

namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x404dc31be40bc40de31
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/8+packedAt s0K4 (64+(h % 8)*2) 2) % 4)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1fffffffffff01fff03fffffffff807f1fffc7
  | 2 => 0xe03fffc07fffffffffc0fff00fffffffe3c7ff
  | 3 => 0xffc03fff80fffe03ffff03fff01fff80fcf8f8
  | 4 => 0xffffc00000fffffffffffc00001fffffff00ff
  | 5 => 0xffffffffff000003ffffffffffe00000ffff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x81454a450a211c48b00b2cb4d4a58a350d5bc3
  | 2 => 0xb91190931452249152c055524acab2c662c55d
  | 3 => 0xc9b5230a2694483a7555026ae2935b14b4e8e8
  | 4 => 0x12263a2c58e89123a9a6980c8c1c6c78df00b6
  | 5 => 0x1c383c3060f0e1c3ce38e38f0f007060fbb600
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000fcc0ccc0f0c00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40411
namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x20000071a0000001c310000810000300200028600200fff32fe40fc20bd41bd43fc10bc40bf43ff31ff20ff42fe43ff41fc32fd40bc42fd21fc30fd42fc40be40fd30fe20fd43fd41fe42be42fd20ff30fc42ff43fe21fe30fe10fe41fe31ff10fd10ff21bf41fc41ff40fc31fe32fd32fc21fc43fd31
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x48006898002c341030008cd8dc600c4c01f804142c74add42000280010004c08000400040404802c0c3404d05000343801b444000000303c7806dea4a0cf552419eaa6613d54cc6eaa2184f54f41afa9a21af525067ca821cf55131dd280813e544c6dea4884f55031d6a94815c534827ea9194f950219f2a4413c548427aa7204f550329f286876e529027aa8184f552219faa0413f548427aa6205bd49309ea88855d5304278a4a1f54c431af298216d52042dca4084fd51329f294853e501027ca5204f950319f296833e52d0ed8a4a1db149109ea8c812c52506daa5204fd5321bba8a415e538867ca8194f950109fa8a8776510c27aa918cfd51109f2a6613f544867ca820db548309eaa4413e5010adea4a1cf553109f28485ac5250e7ca1a0cf150209eaa4873e54c8278a0a0d7d4d209eaa6659f5350f5885904f952219e2a2212e529035ea4a1cf141439ea88815d538867ca4204f151209f284815c53442eea2985b14930d621443ac52506eca3995b54b319e2a2613d540867aa9906b10920d6216653e548c6e8a2905b149419e292833f544c3588410cfd52309ea8c856d528c678a990cf95331dba8a837551cca78a8994fd5120d7290853d5390a7aa3a1cf55010d6210653f5350678a9194f54c429f290853e54c4258a4a1cf950309f2a6656e52cc678a9185d145309e2a2436e520c35ca5205b94a31
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe40002508c051002000012009608d584548ca2c62551318b189511022c6255031c910a51cca2c6254c408758c54c872442145208b98a50d062c6255330a358c420ca2d65108328b98b548423860551318b98b540822c62553108758c540830e5310a21a9584420870c53109208b98b548c22e62943438b18951d0e2d65108218d584540822c6254f41
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/58+packedAt s1K4 (3618+(h % 58)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s1K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xe0ffffc0fe0fffff0783e0fffe1e07ffd23e4f
  | 3 => 0xff03ffff000fc1fff803ff07ffe00781e3cf8c
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20080888240200002904a108802290a404d095
  | 2 => 0x4a3191064894b0cb02a148d332142558d2264a
  | 3 => 0x865aa2921d29135558427a45d540560d634b8c
  | 4 => 0x14a344249181a5a694e8108669996011b80d60
  | 5 => 0x18c38738e1ce39f8e7739ce071118461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40411
namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x4001060002dc30ef42bc42ec42dd31de30ac42df31be42
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x200088040aaa88618c424c71885186394c42c6210618c42cc65ca5216354c42
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc02083594420c3044254430a15865310a0d6510b31
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
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s2K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/16+packedAt s2K3 (216+(h % 16)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s2K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc0ffffffffffffc0ffffe07ffffffffe3c7fff
  | 1 => 0xff07ff81fc0fffff0783ff87f83e07ffd38e4f
  | 3 => 0xfff81ffe000fc1fff803fff87fc00781e3f38c
  | 4 => 0x1ffffff001fffffc00007ffff801fc03f0
  | 5 => 0xffffe000000001ffffffffff80000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x52004090480200002904a008884290a4043495
  | 1 => 0x8451890c9154a8cb02a14a8532342558d18a4a
  | 3 => 0xa32d2243a690b55584273505e90560d62d38c
  | 4 => 0x2ca51c492341ade694e81a4467396411f80360
  | 5 => 0x30c61871c38e31b8e7739c6604218061bf6c00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaee88aaaa8888eeaaee88aaaa8888eeaaee88aaaa8888eeaaee88aaaa8888eeaaee88aaaa8888eeaaee88aaaa8888eeaaee88aaaa8888eeaaee88aaaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40411
namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2c18a0400000000cb000100100541000000185180000fc41fe21fc30fd31be41bf40bc42fe31fd40fc40fd42fd30fd43fe43ff30be42ff21ff43fe30ff10ff31fe32fe20ff20fd20fe41ff41fc42fd21fe40ff40fc10fc31fc43fd32bd43fe42fe10bd40fc20fc21fc32ff32bc41bf43fd10ff42fd41
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8000048080814001420a81400740c00c4240c000800200000000058540408301c083c540004380408006820000000080400000000180804002008584400141130180448000801cc0000000800144a78a4a1cf55020cea1e639d5310a7aa9204f94642cea1c613e540427ea8994f150219f2a0815f53442b8a6904f94b439e28a873e5210a7aa910cfd41438ea98853f544c67ca9994f15310af29841b6511067ca9185d94430baa88615d530827aa8184f151319f28e873f54c42bca6214fd52329f2a0416c524433a86185d14520afa9a413d50d0e7ca9104f950439e2a2215e53042eca3995b94b319f294853d54cc2dca4185754f21bba8a419d434c73ea6a1cf15232cea1e655e53886eaa2106794c41aea9c433d531063aa7a04f550109f2a6633c544827ca320d754c419f290833c548c67ca220cf94a419f2a063ae5210abca790cf540429eaa4873f544867ca9984f54241aea98859e5310a7ca990cf553319ea80833f548c67aa720db548309f2a2613f544427ca8194f55332af29e813d540ca7aa6215714d109e2a2439e53d03ca4210cf952109fa9a819d434caeca2104f94b40dda82816f524427ca2215b948108ea98835d53042daa4084f55321af298833e5488678a2a05754f409e292813c544ca7aa7a04f55031b6a96633d5090a7aa9084f552209f28e817551ccb3aa7a04f153209f2a0613f54c827ea8904f552309ea9c853d544c33aa620cfd5021
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x100800040200048000224000487d8d5090a1d63952208758c525031543547328758c51502946150d318758e5190a1d6394a418758c54c821c6550d318758c544861f63542418758c54c430d43548308d987548ca1d63150218e5805408634615513087195434ca2c62551308b98b548c68c6250d328758e548430d4354b31c550d510c21d6395130
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s3K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/79+packedAt s3K4 (3618+(h % 79)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s3K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 1 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 2 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 4 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 1 => 0x2519221924a430960a854853485090aca32692
  | 2 => 0x432a44486949032aa109950595012585458b18
  | 4 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40411
namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x30c00029c00020c00000061d17c0000000ac40425c3040000080ff41ff30fc40fe42fd30fe20fe32fe10fe31fd31ff43fe21fd40fd41fc20ff40fd21fd20fc10fc41fc30ff42fe40df32ff31fc31fe30fc21fd10ff32df43dd32fe43fd43dc43fe41fc32fd32ff20fd42ff21fc43fc42ff10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x900004200206020030100bc98056100260639b001c190a8000008800004828804a89061ca0d06a000004080001c15180140010008100150056d8a4a05d54642aea98411c544ca7ea8885795332e699441765190adaa4085b14910af298215e53082dca4085794f20afa9a813e5408278a888734c820b6a90875c535033887215bd4940aea90875e530cabea6a0cf55010b6a96613e54042baa7195754e41af29c87cf524cb9ca421d714d41bba8a815d53902bca821cf95230af29c836d52906bea6885354843e6992435d5390b3886216710f40cf2a0875c534427ea8995754b43afa9a853c544c6baa610d714d42aea98855e53902dca421f34cb21e7212653c544cadea4884f55321cfaa2655e544cb388720db94831b7294835d53c86eaa2106710c41aea98215e530873886a07350932bb2884174515039aa421db94b30aea9e415e53c867aa9184f55020ae2a6656d520c6bca7214fd5131ae2a2653e54c8738a8995794c42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x240000048000004400016000040080030028d6210c41c310e529064d6214d41b1586424ca8d6210e42a358843d030d544cb218719153087144394642a3588435028d6210e41d14c9510828c644c82087992544ca1c6454f20c510c515030c5490932a3191328830d6215132a3191324864d6294e4093195424ca8c644cb21c3551320830c4314940
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4900022063b2a899041411d13254420818ecaa26590e0454586424ca82b908728c85415c84314540
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/35+packedAt s4K5 (704+(h % 35)*6) 6) % 44)
  | 4 => 2*((h/65+packedAt s4K4 (2430+(h % 65)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s4K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s4K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf07fffffffffff03ff07f83ffffffffc8e3fff
  | 1 => 0xff81ffc0fff83ffc1ff87fc3f83fc0ff71ce73
  | 2 => 0xfffe07ff03ffc3ffe0007ffc7fc3ff0381f39c
  | 3 => 0x7fffc0003ffffff80007ffc0003fe03e0
  | 5 => 0xfffff800000003ffffffffff80000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1408204820900000a5009004904454500614a5
  | 1 => 0xa12450864921512c0a2829412a2a82a930ca52
  | 2 => 0xc21495121a45175540a44da84ea32a0b816318
  | 3 => 0x8b59662490759b9a73b5052077320c33da03e0
  | 5 => 0xc618438e38622e39cc67632040030c2edbc00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40411
namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x484010000c1c10030270830000001c008000002b68408124004145ffe32fd30dc32df30dd30ff30fc31fc41fe31fc10ff43df43fe10dd31ff21ff10ff42fe21de32fd31fe43fc40fc30fd32fd41fc42fe20fe41ff31fc32fe42fd43df31ff40fc20fd20fd40fc21fd10fe30fe40ff41fd42fd21dc43ff32fc43ff20
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc6811c83c440024380004004001d41404081000640c0004040000001c00401c5134240808a8007c00640020001c256c5000000044000000042808a414440840186410a804000002daa4085794c40ae2a0655e53906daa4205794832af2a2615d53902baa620f590531ba28a4176511027ca8085794f42ea98c435d510cabca7087594443af29c875e53042bca819754c610aea8465755190abca9194f55010afa9a855d5110eeca2195754e10ae2a4657651082eca321754c5219f2a0415e52cc6b8a898db14940aea86633e54886b8a790d794c30eaa88656d52906bca620d794c21eb28e619e5410ebaa710dd94730bb288875d538839ca4195d54440aaa8e613d54886b8a8985715331aea9e855e53442eea2a06b50842afa9a835f504c6bca898d554432aea8c65d6510caeaa3a15714d42aea9a215c53506baa7187550531afa9a815c53482baa6207554730aea80655c524c6eaa398754c4109faa2415d5390abaa718d794c20aea98435e530c6baa6085715330aea9c835c53502dea4a057d4f21ae29e415e52cc2bca9985794b43b7290215e5410edca4205d54420baa88655d51d0ebaa78857d4530afa9a415e53902bca710dd54443af29c853d54082baa3985554443afa9e415d5010ee8a2a05754343ae292615e53883b6a0985dd45209e2a241d7514c6bca5195714d21af2a6637651d0abaa61057d4d21b7294835e53c42bca421f554443
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6069c20300003000302c0031c489398a544c657615434393189534425561150328799353c865465505319558454cc315544c6219558652d0e556194e20955845350a55611493096580540cb145450531b118931486556114f20955865390315544c41095586548ca1c6454d10d154931042556194d1095d85508ca54654c521b158a414c6556115130
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/37+packedAt s5K5 (768+(h % 37)*6) 6) % 48)
  | 4 => 2*((h/72+packedAt s5K4 (3618+(h % 72)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s5K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf87fffffffffff81e0ffe0fffffffffe0e3fff
  | 1 => 0xff81f87c1ffc3ffe00f0ff1e0f0ff83f89d273
  | 2 => 0xfffe007fe0ffc1ffff00ffe00ff07fc1f1e39c
  | 3 => 0x7fff0001ffffff00000fff8001fe03e0
  | 4 => 0xffffff80000001fffffffffff0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x80820040008000020110022221089080204a5
  | 1 => 0x512454c8ca51699614687514458d50b588d252
  | 2 => 0x6214911146a10aaac500a64089a46684b16318
  | 3 => 0x475966629439adcd76ba14112ece4319de03e0
  | 4 => 0x8461844318c2317198ccd899c00804216db800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfaeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8faeaa8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40411
namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5001fd31027f14001fe5200ff04001fd2100ff88401ff21007f4c009ff53007fc8007fc40007f90803fe41007f8c807fc42007f94005fe5300ff08405fe43007f54809fc5200ff10401fd51007f08007ff41017f14c01fe20007f90005fc30017fcc409ff51007f50801fd41017fcc805fc43007f44001fd5000ffc4007fc54007f84003fe5100ff8c401fd4001ffd0c01fd20027fd4803fc51027fd4001fd4301ffd0001fd5401ffd0803fc3101ff95005fc32007f4c805ff30007f54c01fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24005ff10130025fcca98017fc304c001fea1a4200ffd8d4204ffe8521003fe3294009fe292a601bfd8d311b7f8a098827fc618c801fea0ca005ff0c220027fea6a8013fc5454429ff32a4002ffcc9530bffca910003fd32940075e3224000bf5972102ffc4088013df5354c13f72164000bfd8d54007faa518002ff6454413fe294a409ffd872002df8c0a880bff3150c01feaa24000ff54720017fca69894bfc3055001fe98a8026ff1464002dfec8a00dbfe654c427ffa024018ffd522001ffca8aa017fc6308001fe98ca000ff5093102ffcc320003fd3048033fe20e4005f798c20027f8a0a9003fd5444005fe194600bffd0a10007fc64a0917ff3090801fea9c4002ff8c5430f7fca8980a3fc52900137e31c8405bf1864003ffe8088026ff64c8441ff28c6001bf9854202dfcc120027fe63c8401fe9822005ff58a40026fea8a9003fc62440077f3226400ff54940007fe432800fff54550017eb0c6009ff8c93201ffc8721027fc328c80b7e31ca002ff0c143257fc8329013fd5454c01fea928419ff0c72004ff8a410006fc615500b7f3046000bfd85540fffea898002ff614c805fea9a6005fe1425004ff864a1013ff53544a1ffa02a604bf9962002dfcc110003dd434c003fea0e4205bf19630097f8c690003fd548c013ff1964201ff9052111ffca2a0002fd6288007feaa28024ff0c94000ff8a288017ff3084007fda048000bfd91520057ec89000bff328c0037eb0c2009ff18e5202ffac918002fd6308007fe2028600fbc852020ffca2a1002ff62504077fb2aa809ff086421cffcc6a8827ff65c8013ff1084001bf1865204ff8a490007fc1048401ffb02a416ff10e2004ffa4390017fe6590015fe29c201dff98530007fac6a800bfe324c413ff3246400ff5855208ffc42900ebfe64544077f3264000bfd9521007fa809800ffc43550037f30c6000ff50c2002ffc611000eff645500bffb184001ff5053100ffc4288023fc5244007de2148001ff08610007faa4a080ffe4190001ffb026209fdc852101efca8aa003fd4348001ffb1aa424ffcc940237fea121017fc508800bfab084004ff54a50017f8869800bfd324c485ff9928400bfd9532157fe60a811bff5190807ff2a2863fffd023204ff8859000ffd5450401fea1a202fff18d21017b8a6a9817ff408c0037f30ca40aff90e1004ffac129007fd31c8413bf32e4205ff14130027f8a0aa017fe304c001fe312a200ff54932007fa851000bf7314c42dff29c4000ff5954102ffa8110027fd528c809fe29aa004ff9465004ffcc321003fc6254c0bff32c6005ff04120004facb9092bfc109480bfe084802dff0ca5012ffccaa000fff5450c01ff2142009bf19320297fcc6aa0afff4254023ff20a4005bf1842002ffea10800bfd5350c09ff29aa801ffd4610
  | 1 => 0xffc415505fff9924200ff50a3023ffc62a900efe6494009bfa92a835ff10131007feca98012ff6254805fe192a600ff4c910007faa6a080fff54504077f3264209ffc85200f7f8849800fbc545500bfe282803dffd513201ffa84a0003ff63540017fb2a4002ff54e3221ff8a0a10cffe54c84037f30c4000ff50d51017faa69913bff5250c5fff31a422dff10e50007fa6290027fe5254801fea864001ffc8510007fa8528006fe6148037ffa1e4000bf59220016fca6a980bfc3150c49ff29a8003bf1913102ffe8010016ff638800bff314a000ff58121007fa6210003f52144001feb1aa805ff9414004ffec990003ff63440137fb2e4034ffd532101ffe82a1803fd6055093fe202a427ff0ca40207bea719002fd6494805ef9926000ffd95321affca898817fc6284005fe21c6448ff0c152007faa790827ff648c809ff28ca426ff94640007fec4aa002ff654c005fe1826203fdd054100ffa6288002fd6348413fe194a400ff48620207f8a119003ff6048401feaa24209bf98a4202ffca118007fe2148413feb246416ffcc620007fa8499003fd6148007fe2128609ffd9721017fe629800ffc4350413fea904046ffd4e4202ffac9100dbff544c403fe082a204ff94d5204efca4a900bfd534c4017fb028404fbd495203ffcc888003fd6550c13beb2e4205fe0c23008ff8c29001bff3244007fc2028005ff4c020007fa8318003fd214c01bff2884005ff58640297fe62aa017f81084009ff2a2a444ffc424204ffe652909fff3290061ffa024215ff8c620007fec498002fd6550c017eb0c6404bf19532027fca728003fd52440037b3084038ff14141017fca71900bfd328c065fe21e4203ff10154007faa8100dffe5350403be28aa202bf98d4100dfcc2a000ffc4150c01ffb0a4003ff50540037f8c688047fe5148001bfb2a2000ffc863028ffc62aa016fc6484001ffb12623dff1413222ff8a72100ffd42504017eb222000ff8c940027faa6a9002ff6348403ff28a2009ff94a20005fac328003fc625500bfeb1c201fff99530007fca498133ff4094801ff3028209ff99252037f8648804bff3248013fea146400bfd8553017fca699007ee2148407feaa48000bf58642005fac190817ff4090069fe2864209ffcc820007fec6aa013fd549480bfe2044005ff19250005fec498017fe6408019ffa9c2030ff1912100dfac390803ff6254409ff28aa603bf19153007fe42a000bfc434c401f6a124005ff90130005facaa000bfd318c00bff8842001bfd85310077c84a0803fd6244065ff29e4200bfd895400fe86298817fe2008025ff31a4009bf98a5001df8c8a8807fc5148401feb12a009ff1492104ffccb90817fe658800bff3242009ff50b2102ff8c810007f44150401feb1a4009ffd4b2002ffcc518013fc519480bff1
  | 2 => 0x21017fc62990a7fe4154001ff2928005ff9014001ffa8520017ff640800bfe1846037ff98d410d7fe61900fffc408c86bfe2126235ff1913102df8c310017fd6194073ff992a209ff19642007fcc090803fd219400b7e32c8022ffd523002ff880a0017fe5090043ff2a46005ff8c120037f88688017fc5044083ff30a840eff94c2016ffe6328003fe52504057fb1a8609ffd8f2004ff8439000ffc405080bfea004005ff0421004ffc6490817fc1054005fe21aa605fe102400d7f8a790027df328c80b7e3028405ff8c110167fc6328017fc5048003fea0a4209ffd0b2000ffc42a8827fc64c8425ff29a4004bf1954300ffe62a0816ff648c053ff882a005bfd9610007fec888003fe32900137fb2aa409ff58321027fca528007fe3150405fe21c6006ff94d10005fac890027fd42080013eb2c6003ff95140007fa6490803fd4048003ff90a421fff19530017faa718003ed2148005ffa1a8605ff0c14004ff884a900bfe318c805ff98a6400bfd8d41006f8ca99003fd42480097e32a6001df9455104dfec99010bfc30508037f30aa61cffd4720007fa8088003fd5188007ff2a2844bdf94e52007fac299016fe6090835ff21e401cffd43200077c8520013fc5054c03ff28a4200bf5913200ffe6390803fd4244001ff3028603ff50640277f8caa1857fc318800bfeb084003ffd514004ffcc721027fe52c8409feaa2a22bff9915002ffcc310003fd654840bfe204a009ff90b200c7fea51005fff4188013ff32c8400f74c93004ffca519007fd3148405ff29aa63affd0151027faa728147fc3155007ffaa28400ff54d40007faa6a1003fd514c001ff312a801ff8c721007fec48800afe6394005ef9926205ef59020247f886a9003fe6250401fe9948005ff9412001ffe82aa00bfc314c007fe202820bff15210027fea4aa017fe5008013fc9004000ffc864000ffe6298817fc639400bfeb14a001ff14551005bec6a9003ff6250413df2128409bf9891004ffcc39007bff414c007f62128409ff58e521e7fcc89900ffc435000bff904203cff101320fffea498017fc3094001ff2926209ff59721027f8a8a8016fe608c8017fb028204ff9525002ffca088002ff6348001fea084009ff8c82004ffec9908cffc40c8413feb0c6405ff1423004ffa6410016fc6584005ee29c6401ff8c531007fac498923ff315486ffe1828200ff5492104ff8649000bfc308c83bfe20a6009ff8c920007fa64a0002ff624c407fe212a840ffd5232007fac4a180ffe5450413fe2144002ff8ca3002fda40100fffe548c885ff29a8401ff0855100ffa828800ffc435082bfe20c4002ff94e30007fc6488003fd324800bfea046002bf18d54247fcc6a90c7fe6548413ff908404fff18553007feca880cbfc30c84037fb0a8200ff54a40007ba629800
  | 3 => 0xfa0ca005ff9011004dfec8a1003fd5348401ff292202aff18d50015fcc6a0013ff52940137e3246405ff4c21002df8c09080efc6454801feaa42005ff9002004ff884a1143fc6454c097fb02a009ff9492000ffc628800bff3154c09ffaa4a005ff0c24004dfec790813ef5294807ff2a48003bf99121007fac899017fe4048013ffb064205ff10020007fec0a0927ff4354805fe18c644bff0c25226ff842a180afc6354859fe18ca001bf18543017fc62a9812fe6550c0bee1826001ef9054101df8c898006ff61544037e30aa003bf9915204ff8c390016fc63840077f3226005ff9925002ffaa110003fe3254405ff21a862fff94d2104ff8a521017fc4048001ff302a803ffd524000dfcc32100ffc4150813ef1926400bf5951000ff862a08b3fc4194047ff30a8009ff8864200dfcc210017fe6584009feaa2a003efd064202ffac610003fd3254401bea92a03fffd0632277fea2a1817fc4044057ffa02a004ffd525200dfcc39000bfc314c801feb2a8004ff54e52007faa7200f7ff524c813ffa946405ff4802017ff88690873ff53c8009bfa82a805ff0c02001ffa872103ffe5408029ffaa24009bfd964202dfec2880f3ff414c80b7e31c8001ff5472102ffcc318003fd530809dff32a8605bf18650007fa4318067ff10c80a1fe202a600bf59531007fa8729017fc204400bfe1824001ff14610177f88528033fc5284027ff2a24001ff0c721006faa8a8003fd6150003fe18a6231ff1412100ffaa29880afc6350497fe21ca400efd912004dfcc508043ff5408001fe9022001ffd072102ff8608800ffc4390001efb1aa409ff9865204ffac721027fc320800fff2a22000bfd8540127fe62a000ebe6408013ff3264202ff8c63004ffec3290e7fc3254485ff98a8409ff10a3202ffec708003fd53480017eb2c6012ff10d200bffe871000fff435501bfe2884000ff50e1002ff8a120017fc6188007fe2128209bf1895002dfecb20003fd2150001ee9926205f78c13002ffc811800bfb304c00bfe2046000ff54d101f7f88319012fd6594011ffaa22004ff9515300ff882a0802dd6308003ffa0a6205ff1963002ff8a0100a7fe2154007ff20c8400bf58e40025f8ca90806fe614c801ffb12a004ff54951017fe869800fbc4090889fe0848405ff18a4000dfcc3190dbff524c409fe28aa023ff8c540025fcca880effc414c809fe292a005ffd864002ff8c210003fd6454401fea1aa009ff8865204df8cb19013fc5094813ee1926405ff98e1020ffc62a1016fc604c409ffaa2a627ff94e401eff8ca99027fe5250801ff3028400bf58e2024ffe82a9002ff6050c0bfeb0c6000ff58141297f8c6aa11ffc41548017fb02640eff10c2000ff88390803ff6055003fe20a6201ff94551027fea4a9017fe3008003ff20c2000bf591
  | 4 => 0x6ff6044013fe214a409dfd4a52025f8caa0147fe6155013feb1e4004ffd515101ffe86a0002fd6408007ffa1a8401ffd0510047fea4880177c50540077f322a200ff5814204ffca410003ff6348413fe1948402bf98d50027fea2a9003fe3254001feb128249ff99152027fea0a9003fd625000bff31ca001bf1853204ffcc3190ab7e5354013fea948400ff59531017f862a985bfc5388007f7a128402ffd4d4308ffcc290006fe6155013fe2104000ff98940017f8a698027fd6590837fe2a64016ff90e20287fe82a9813ff5254c01deaa28209ff1092000ffc62908bbff4394003fe98c2003efd01411dffcc299037fc4108013fe32c642bff19150007fe42a800efe648400bff31c4000bf58e10247f8c6a9137ff1050ca5ff982a805ff59610227fca321003fe62544097f32c6400ff58d21024fcca10003fd654c0097e32a8200ff54a1004ffa659080fff4255005ee21a6404bf19510017fe6098027fc424c823fe20a4003efd0940017f860a98e7fc4354409ff29ca405bf1813201ff8a921013fc535509ffe20aa609ff0862018ffea890802fd618809dffa828647ff0c55202ffec32801ffc42440017eb1a2002ff0c630007fcc49800afe6308015fe1942004ffd515213ffe6320007fc414403dffa126002ffd0d3204ffe6521017fd6388001fea8c6000ff18930007faa2a0003ff604c8017fb02a801bf1864204ffca49087fff504c0a3fe10aa805fd98420007fec8a808bff528c097ff98ca402f7cc530027fca6a880fff435040bffa844002ffd0e3200ffca308143fc4254c13fe32e4005df94150027f8a0a880afe6388043ffa0c6000bf59530027fea0aa00bff318c061fe202421dff0853004df8c498016ff6588003f610e4200ffd8d41257fc6329002ff6150801ffb1aa21eff1913001dfec4a100aff604c001fe3028420ff1063004dfec79000efe644c4017fb12a600ff94a30017fc86980037f654c801fea12a204fed4250007fac888063ff5188013fe9084029ff98550007fec2a810fff5250809bfa82a403ff1054004df8c4a0803df635500b7e3028203bf1913217ff860908c3fe544841dff9884000ff9093001ffaa921017f61044009ffa8aa80affcca10027faa328013f85054007ffa0a8041ff0c542007fa429000bfc304c801feb22a603ffd0242007feca9080ffc4250013fe30ca412ffcc52002ffec518013fe515400bfe204801eff991300fffea29800bff3050c017eb04842aff0c950007fec0a1003fc604c403ff10c2001ff4851008ffc6290003ff6050c1bff1884000bf58a101c7fea4a0803ff6154c0bfe30c8001bf98b21027fca929003fd42484017fb22a605ff8821000ffe62880137c535500bffa042000ef19120004faca10087fc428c0093e32a2000ff98132015fec8a180bff434c45df
  | 5 => 0xa5004ffc84a1017fe308408fff882a405ff1415004df8c4aa067fc51c800fffa1a2009fbc872002ffc8110027ff64948137e324a443ffd454204ff8a59003fff4308005ef98a6409ff8872004ffe851900bfc538c813ffb0464049f19532007fac2a18dffc5350403ffa0a4200ff1815109ffe8690027fb20880057e31a8403bf991201cff8c6a8807ff3154405ff9826209ff08532007fec2a0003fd5248001fe302863cff1913200ff84298827fc648c805fe29a6402ff90e3202ffacb18017fd508c001ee31aa832ffcc321007fa879002bfe5384001fea8a4000ff58131157f886a80f3ff424c867ffa1e4201ffd454102df8c918003fd428400bffb2c4011ff1452000ff842a0817fd4084075fe322a200ff505200cffc839000afe6354407ff21a8209ff08632005faca10013fe5354065fe29e4200ff5912001df8c8880f7ff504c80bffb242002ffd0d5302dfeca100c7ff524840bffa84a009ffd0b2100ffc62a8827fe428c801feb1a8403bf1912000ff84390816fc6284001ffb02a203f7d0d43007fc8528003ff6548083fe30a8400ffd9130027fea328027ff618c8017fb2a8423ff0c540227f8a321027de63908017fb226448ffcc15202ffe2110002ff62500057f31ca438ffd4141007faa320063ff538806bff3226200bf58a3009ffcc890027fe424c80b7fb244004bf1952000ff8829092bfc3194807ffa0c8001fd0852101ffc84a0813fe5254413fe2124202b798e50026fea8a8016fe60c846bffa126214ffd4920197fc8790803ee424809fff30aa605ffd8a1002ffca108003fd50500097f3284009ff18f20137f86320127ff4254809ffa9aa803ffd094302dfecb1800bfb308c001ff302a400bfd89431d7f880a8803fe62440097f32a8428ffd4a401effea299133ff4194869ffa864209ffd8f21025fcca99147ff1055005ffa9a600fffd042004ffea52900ffe4355013ffa904000ff5442000ffea390817fc619400bfe0864037ff18d41005fac790803ff6348013ff2164205df5963001dfcc8a9803fe424c4017fb226004ff54950017fc8698807de314c407dfa028401ffcc52102ffac310002ff6054c03fea0c2005ffd9230007fc650800bff438c001ff3126201ff54541007fac4a880ffc42900017eb2a4049ff19152005fec890133fc4094801fe98aa001ff0c510005fac928037fc3108009fea9aa200bf58e50007fec4a18e7fc305440bff9844000ff4ca10007fac29800afe6344009ff2a2a201bf9865004ffec129026ff658c8057f31aa811ff0c52000ffe4308006fc61c806dffa826209ff0855200ffaa288017fe505400bffb24a026ff8c64002df8c318017ef2088001fea0aa013ffd0520247fc86a9016fc6508007fe20c8001ffd453102efea12805fff4288095fe20ca402ef10d4304ffac390
  | 6 => 0x1feb12a805ffd4020007fac890827fc60c84037fb228200ff48550006f8ca88093fc6350013f62148419ff9472002ffc8108017fe619400bfe31c80049f19531007fca508027fc3248455ff98aa005ff59250087fea2100127e658c001feb22a02dff90e5004ffcc190826fc63c8001fe302a805ff58e5004ffc8490017fc509409ffe10aa600bf58252027d8a4a9027fc32c8003ffa0aa205ff1021018ff8ca9080ffe54908077f322a002b718d52027fea728027fd63c8401ffb22a604ffd515002ffcc210007ff51440057f31c2005ff54240007fc8488007f621c8409ffa82a604ff54d50007fa84a8017ff308c013ffb2c6417ff1522002ffe2128016fe6084009ffa8aa600bf595321c7fea6a0807ec2148405fe29a6202bf18d20157fe64a8003ed42c8009ffa92a200bf5964004df8c729016fc6055001fea9c8405ff0821002ffecb2000fff54908017eb264205ff1015002ff86108013fe5254005fe29c600bff9521002ffac720027fd64948017eb2a843effc423200ffe20a080ffc5455043ffa146005ff4821001ffa872000bff534c801ff2948000ef505401effcca99003fd3190003fd8822002df14d5304dfcc52009bfe2190001fe90c8001bf98543015f8c69087bfc544c0017eb046430ffd0d21107f84318017fe1044077ff8826403ffd0942127fe60a0017ff2088001ffb1a8034ffd4f2126ff820a180afc6350085ff9828403ffd094000fee2090802fd61c8049fe29a8000ffd854202f7e8120017be64080137e32c8401ffc432112ffea4a000efe648c019ffaa42000ff59510007faa990013fc53548017eb1e4038ff19541017fc871806fff40c800beeb184000ff4c95001ff8872110bfc5350801fea9c2004bf1954202ffaa010026fc65c8403fe18a4200bfd812100fb86298827dd639080b7f304a400ff4c3201dff8c299097ff5150001fea82404dff9854302fbe6118027fc42c840bffa846004ff951501d7f884a888bff518c005ff18a6002bf98e42027eea2a8817fc3054009dfaa2a804bf9954100ff882a8817ff6390047fe10a8000ff54130007fc851800bff534c4137e32e403cff95132007faa08800ffe4350003fea8a4200ff1813202ffe6128003fd6054813fe3048409ff085420effe2098027ff63908037e30a801bffd072001ffe8720017ff6294099ffa1ca402bf98e4002df8c910093fe6350007ff21a8405ff19220237f8a121027bf4290859fe10ca005bf18143005fac329023fe654406fff9828205ffd9220025fccb2100ffe425000bfeb24200aff10e1004ffcc790097ff5050005ff9826400bfd8d50027fea6a900ffc5450c017fb2a8203ffd0941007f8c0a0817fc508408bff29c8405ffd8e20027f8a728026fe62080057fb1aa643ffd414204ffc8510002fd644c405ff984642effd
  | 7 => 0x8800efe648807ffe2a46401fd8851001ff8832110bfc635085ffe29a4200bfd8530005fec6a0017fd628c0137e312a205bf98020026fea0a880afe6348081ffa846401ff04131027f8a4a8817ef2008003ff20aa203ff15141025fcca90012fe6550053fe18aa000ff9895325ffe612900fbf41550017fb2a8001ff085210077a84a011ffe4154805ffa9aa600f718d52027fea4a8013fc525502bfe28c4009ff4cb20017fc86a98f3fc544c80b7e3204009df1495204df8c4880afff415400bff2864005df9942027ffe20a9823fc65440077fb028000ff4c720026f8a2a900fbe545040bff9848038ff99541005fac69002ffc42840057eb1c6005ff5942023ff820a9013fc5155013ffb0c8405ffd9630007fecaa10bffe4348403fe20c2005ff98c2004ffc6590147fe2155001fea1c4001fb8872119ff8a990816fc6308001fea0e4000bf5913001ffe80a1877fc514c0056f3184000bf5923002ffacb2007ffc524c001ffb128009bf18940007fac8a9027ff429483bff10a6009ff90921187fcc89089ffc53900017fb02a204bf99610017b8a698017fc6590007d62128403ffd0a4021ffccaa10ebff4354401feb1a8231ffd4121097fe60900affc42540057f31e4000ff9895001ffc8720003fd63440097e32a6204df14e5202fbcc728143ff4254c03ffa8a4202ff50d3004df8c4a9807f64144013ff90e4005ff18a5004ff843290d7fc544c4097f32c6045ffcc64202ff8cb10017ff3008005ff982a600bfd953102ff8c908077fc614c005ffa9c6003bf1912100df8c29809bfc219000bfe30c6000ff98151007fac0a18f3df434c889ff18c8429ff1055002ffe2118057fe4188013feb2e4004ff1515204dfcc529017f41044097ff21ca405bfd8e10017bc8698006fe619001dfe2984000bd5842000dfec490807fd21840017fb12a009ff5864204ffe841004bfc5348001feb02a613ffd092004ffca52100afe635080dff9822005ffd424000ff862a88037d51540017eb1c8400bf58a4004ff84290013ff509480b7fb184000ff1894120ffe20a1027fc210800dff21a2051ff0415402ff82110097ff5350001fe9928203ff9055404df8c79080bdf3050c03ff98c2005ff5902001ffc852001bfc534409bfe28a864eff14943027fea32910fff5350851ffa8c8023ffc414003ffe8488007ff415044bfe32a801dff90530007fec89900f7c5455007ff20a8605df59420026fea4a8027fc6390829ffa8a400eff90c2002ffec728003ff6254c07fe2048400ff5913126ffc42a1807fe3184011ffa822012ff90d20017fea719007f71050413ff99640009fd9531007fec890812fe65900017fb0aa414ffd412004ffaa5900a7fe3154003ff8826209ffd4b2100ff84288002ff644840b7e32c4005ff0413004ffc8410016fc6054c0
  | 8 => 0xf1932004ffcc1210137f5154005fe98a6009ff8863204df8c990817ff6584007fea1a8249ffd015204ffec1210effc514c80bfe0828000ff909510e7fea990002ff604c40bfe31c400bffd0e1002ffec52000efc645402bff28c402bffd0d5000dfec290802ff6350813ff32c643bff88532017fa8699012fe6548401fea9e4002ff50e32007fac2aa013fb5054013ff3264009ff14b2100ff8a390817fe648c001ffb02a600ff5493004ffacb19017f710840017fb1a2003bf99232005faca9094bfc3255001feb2a8400bfd913102ffeca10103ff518c805ff98c6409ff0ca20005fecaa1807fe21c846dfe32a6239ff90d5101ff680a0007fc514c405fe1926005bf1815223efca2a9027ff65908013fb2a20049f9972123ffc42a9006fe615482dff9944007ff1911000dfcc2a8007ff1048409ff28aa800ff50d5204ffec729007fc1050413fe31e422cff90650007fa8790807fe214c4017eb2c4013ff191200effca298087fc548c00bffb084001ff90541017de6519026fe628c0017fb0aa002f7cc13101f7884a0803fd644c0017fb0a8600bf5954100f7882a0802fd65c80017fb22a009bf98a3201dfcc88800ffc5450077ff20a6405ff99420027fea0a88dbfc524c403ff20e4209fb0ca3221ff8caa10137c5155001feb2a6402f714d31027f8a729002fd658c801ff302621aff10f20026f8a3280fbfe418c805ff9926005ff04250007f8c498807ff51544097eb2ca452ffcc954017fa8698817fe648800bfe2864002bf18d1002df8c71007fdf534c029fe32a4044ff0c64202ffc6190002fd6590801feb1aa428ffd4e40007fec29900bec324c809ffa9ca403ff1514200dfecaa880fff4190801ffb0a8604ff145520affc4310027fe608c847fe30a8009ff149521f7f82119002fd6190013ffa948401bf1852002ffe2120002ff6148095ff884a402ff90d32007faa910017be4050001feb126002fbcc93200ff02088017fc648c00bfe9844000ff5513004ffac119017ff4088001ffb2a8609ff997201dff82099007fc31840077f3204001ff5461004ffac990003fd60544017eb2c2002bf98d21007fa8190003fd6548001f690e401aff94f20006faa8a9017fc6584001be32a6200ff58d51017f88699017bc40500016eb1ca002ff0c943087fea610002fd6244013fea164000ff98153007fec89000afc6354003fe0864203ffd015404ffca4990037f654c40dff31a2000ffd9541067fea5081477e5155003ffa0c2005ff194200f7fe8098027fd64c84057fb126414ffd4d2002ffe2010137fe5150ca1ff322a609ff10a42027f8a928003ff615485fff9824201ff90531007fec8a8826fc624c413fd9024002bf18d5108ffe2090007ff1044005ff9928600ff18121005fec4a8813fd5154013fe2944000ffd8530047fea6
  | 9 => 0x805ff29a6001ff9472101ffaa8a1007fe515047dff28c6400bf59232005bac721037fe410800bff3148030ff1512101ffe80a00effe514c80b7fb204005f758e5004ffaa590827fc32548037f30a6003ffd0142007fa84980b7ff3294053fe10aa009bf1894302ff8c708002fd6484055ff21aa005ff58a10005fec888003fe4254001ffb0aa805bfd8d301bffe64a0827fc324c809ffa8aa000ff18940107fc4318007fe4144061ffa12422aff98d5002ff82010017ff61880137fb246400ff58d40117f8a518007f45154441fe28c6009ffcca32007ea8288067fe31c80016fb1aa805ff9422011ffc42a0016fe6094005ff9926409ff0cb21015b8c6aa006fc615089fff20aa602bfd955300ff62108003fc6054835ff98e4003ff1524002ffec318002ff6354405fe21a8604ffd415023ffcc2a9003fd524c40bfd1004000ff5062000ffe20a8803fc6054c017eb264029ff1855002ff820880027f654c8097f32e4009ff58242007f8c4a188ffc515000bfe3146003bf59240027faa92800bfd438c0077eb248404ff1525202ffcc508027fe3288027fe2a24005ff9413020ff8a2a1097fc525000bffa04a000ff9894328ff8c2aa016ff6484003ff28a6241ff8854227ff820a9827ff32c84137fb1a6400bf58e5204ff8a4a1027fd619489dfe2828600ff58553007fa6510003fd6254c01feaa46402ff0c931027f8a2a9817fe40c8059bf28ca003efd0540005fac210017ee2048007fea1a8400ff5513227ffc42a980fff4050401feb026442ff98d42017fa649800bf8304c0a5bf29aa802ff94d43007fa82980137c5354013ff2964002ff8c930017fe6498817fe63900017fb02a404bf9972101ffa86a0017fd5084013ff90c400fff1502001ffc82a100ffd5450c0b7e324a002ff14d43005fec4880f3ff404c8057f31e4204ff94552007fac2a8012fe654c4015eb204009ff18232247fe64a9027fe6094805ee21a8636f7d4d3100df8c319137fc6150c0bfe2064005bfd9550007fec8a9003fd3188001feaa64200ffd9531015fcc6a9016ff6284041ff20c6000bfd8d52005fac5280177e658c013fe30c8433ffd032104fd8a529006fc6154c05fe29aa609ff1493222ff8612101ffc5444001ff90a6004ff14a501f7f8a31900fff4390863ffa9a4209ff19252027f8a328027fc65c84056f31c8402ef90d4302ff8211800bdf304c80bff9004005ff5962004ffe409000fef4290801fea944041ff04142007fac2a10b3fe2194013fe304a403ffd054204ff8a519013fc5454c01fe312a009ef1094200df8c2a900afd638c809feaa2a405ff0c3201affe809886ffe54c8007ff20a8000bfd95101d7fe84a880efe6494801feaa26239ffcc15100ff8a2a0807fe2150409fe29aa200ff50e501c7f8a4a0827fe6394801ff9022009f
  | 10 => 0x1000004ad303f8260a381380d81a80000082780e8002f900002616500700080280482080c01380300000080501b80000280480382b00100300008280603012a00204380e81c80081a000a8c00a00901400205800780200780000700003b04100b10500800280c00500100081e80693100180780b80e20501380600380000006902200000115200002203780480081c80100700b80381c00289e81f28f8182d31a60008018000028a000e00600e80b80382200480300009780703402b8000158050000060e002e1f300500000403380000000280181080080001182900100535d01980006102a00600500080500080000000000f0091af00a8080000c500180302084e81e0000a380500001083800001300680400e80100300680280400000001403083e00801a00000000200e11c80202593800080500a01182a00402a8008088140021ba80500000000a04d8070000038240050168018000298b407b80e00b00283f06d0100038000bc85c00600000180381280001281080123781900681900b80010f80000800380280400601298586502d40a80301300383d87b0178090050ef80100500e83280000080203480025100c80280283000880f00000001280201480100080000029e02c80001380081206080005700300880180483085b0010b800000000180080000a00800900c96700b00090c02000380900c00021f3cb04580400700080300880800a8190bf80080492aa9c80027c81f8200008338009e100280100180184800400181680010b0008040008050119748118098be00000080280000087e80400602301901280800580b00000500000080c81280000a05f07698d02300406400a8038000008018128020040de39080001c0028d580000000980300c80280a00080001e00200006e02702304501580000080a05200280d00000680f00105800b00a00200700102416800d80100e834801000020800000008800000018ad8008021804991800000800971809003a2600580681002b00000e8710cb81902984a00c80300a80380000000280000380480000500001406280210090e80000381b0000039978018a917780080000380480793d84e00000906f80700400180080582000c81601400001480400e00180380040a04580001d00180000d801800003007ae780080114700182282202380280a8010188090088000010018022c5800a6e80380780000b81406681b0521d480080680180000280281600000b80001804481880300080082901900300080400700580000a00400100081100282380384a00b06a01182780102f80400400000300180000680280080025080128d80200780100780b13200024f80305002680e00600380100300881900081c08d00e00200381b0a90040dffc3250401ffb226200ffd954004dfecb9091ffc6154
  | 11 => 0x7802a2706780a8368168e480282f00400e02e00f0138018af0980198168298b48070000003c9a2d80405103280800100000000f80e0030092d780028000f00225a80000f04e80601202a00000780300e8128310088dc0811fa00500c00c80b81000300000b82680500000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd63506502f6df32d81310057f754c640004fd7654a40004fd72d915302ede4058e50004ff765463015ebc64541204367f20d95320067c641953101cfe7458f2004ef72158652005bf745494138e7d51d9531004ff735891002eed2059220005f771549412ef9e7390941014fc735954201cfe74d89300067d655521000cfe7159232005bf7454a40004ff7650a10014fc73590200067f7559542024fe75d91321667f10d951040e7f50d9151004ff7654f21014fc735972000cfc71d89303fedd53d8d51006dc7358910006bf545902015ebf4159540004fe7650d522e79e7390a400067e4159420004fd73d894000cfe7159220004ff764854002cfc768ca10006bf644c920004fc765052002ef52058420006ed621895402e7f705963004e7c525963211cff715911022ede4358e42206df5359632007b7645051000cfc7259321006f56148620004fd764ca40005fb7054920315fb7058d40244fd7654932014fe7359110007cc624c93002ee52058420014fe73d953000cfc71d915309fad72191201667f70d951004cfc7650f211567e31596300067c6518910005df744c530006bf7459130007cf624c93004e7f2059721304ff705953000cfe765092102cfd7058e102c67f65181510fedd5158e5001cfc7458630005df735492102cfe70d915102ebc4059250004fd7654f2104cfd75d9152004ff7648550014fe735925004ede3258f2100ef6615042000cfc71d8d5204cfe7258e5204eef2058642004df73591100067f658c91002cfc76552301a5f771589510067f65d893101cff7650110006df4258e5001cfe76d913002ebd5059020006bf74591210067f655492104ef8205825200cfc7158d20014fe73d95210067d6554620246de53d8d5204edf7358f20004fe765513000cfc71d9532024fc75d9130005dd73989413a67d32d9531004fd72d913025f5f30d953204ef5325842001cfe76d912002e7c405942018d7c7558d2102ebe7059020305fb705953002e7e505942001cfe74d95211f6f71058632496dd52d8d5418e7e65d95210067d6594a3001cfe76d9131026bc765514107ebf4359020006bf75d9120004ff7358a100457c7558910004fe76949401bede63506500067f6554920006df63d8154005bf705514138cff7559531005bf745853000cfc7158a50005df714c93000cfe7159230024fe7558e420067e51d9532026be65551410067c7459630004ff715913018e7c6559521004ff7158a301aebe644c4200267e65546200b6df3258e2002dee709092004cff76c865001cfd71d8d41014fc73d814202ef41058630004fd70d8d420067d70597210057f754c92034eef21d895108ef461585201567d735963000ef661544200065f735972101ebe645502002edf7358c200067e725963004cfc725863002ef77158640
  | 1 => 0x912130dfb7058540076de5358c2002cfe70d8543006df5358c20014fc7358720014fc7359541004ff76509310067e5459630006ed6218941006df63d8152006f761c855004e7c525972102ebf4058640004ff765493004cfc7690910004ff7358720006de7158c2002edf7358e10005bd749494001ebc645011004cfe7650f21004ff7650720006de3158e50474df7359543445ef7258d42004ff7558e10005fb70509200057f745495038e7e31d953100cfe71d9510005df73585540267e6554f2100fb7745051002ddc704c930014fe73d895401cfd75d8954344ff72591210067e54d953104e7f2159721416df30d894301cfc7459520014fc73d8542014fc7359721004fd7650720004fd71d894304e7e525964201cfe745832104cff768ca101cedf30d8d5104cfd70d9120004fd7655110006bc73d91200057d75989102edbc7255141004ff7158e2002ef7205842002e7c2059420015df7450d30004ff72595300067d6554a30005df735895004def74c8520006df6318954004fd72d8d50476dd42d8d541567c5359530014dc7358910014fc73d95210257f7455152006f574584200067f65949310067e735942002ddc7050d30004ff7259510004fd76551201667c31d95100067e73d951004fcd7390920004fe7654d400067f6554d100fede5458e5002ee7205842025f6c32d9532007eb7050920024fc75d8941005dd7390910004fd70d95411f6df31d8d2102eef20592203aeed42d894102cfe70d855235edf31d8d4100df4715092104eee624865002cff70592100067c65581320fedd7558e5002cfc7059131024fe75d8931004ff7258e1000eec7648520007f3705051009faf4190920006df10d8d5204cfd73d853224ebe54d915200df77248510006dd634ca2004ef5215832103fb46450510005f77158154136bf41d911000cfc71d8d2002edf7358e4002cfe765521004cfc7259541005f77159540006bf6450d20004fd74d9510004ff7158e5038e7d41d9531007af6450920006df5358e10006bf6450110004ff75586401b6dc654c5300073f64551500fede5258e5004cfc7259640014fe73d8141006bf3159020004ff7459532024fc75d852006eef76487200067c72d9531005be7619120006ef72591100267e6554a100fedf5258e50006be51d91200c67f5259620004fd72d9543004ff75586321b67f52d95312975f7518d54004fd769491004def7148520005bd744854001cfc74d9531014fe765413000e7c6154550186bc40d912106ef6515842023e7e5159521004fd72d9531024fc755923001cfe765494200ef6615065042cff7259532196df3058f211c67c53d954102cfe70d8d42004ff7359540206dc75d8d52006f54358420466dc72d8d5246e7f50d895402ebe105902004efb705823204cfe72d8d50006d
  | 2 => 0x75c754c93104cfe7258e4221e7f50595420fedd5258e5001eec645092000df6718c9100f6bc644c12002dec705092017edc53d8d2102df470505100867f5459420036dc5358d10014fd72d953204ef7215842000cfe7159520004fd70d954301cfd73d954302e7d70594200067d6554a2004cfc72592322767c6550d10005bf745815204ef452584200a67c654811001ebe6090a4004e7f7559720014fe73d911001cfd73d81431bedc53d8d4134e7e51d895111df471595400d4ff7058d20004fe768c950004fc76549100067d70d95311ee7e65d9532024fe75d8d410067c70d9532006ec21d894025edc4358e5204ebc215902001ebc6490910004ff7158e5208df47158d2004cff7690a5025e7d43d953204ede3258c201ddf4715813201cfc74d952028df4715815401cfc7458650006f4715952038e7f73d9531006be73d9120024fe75d853202cfd74d954002ebc40592300d5fb7058930356ed32d8931004fc7650d1004cfc725913104ef4215864204cfc76c85300067f435942004cfd75d815208ef621d8520006de7458c2002cfe7694a40006df63d855204cfc7258e10005df73589101b6de654c5300267e6554a201667c41d95100247e76d9532004fc7650d2026ef46158543004fe76949100067f7059721004fd75d814202ebd3059020014fc73596420267c6554932006ef7258d200057f7558121004ff7650530004ff755923204dee725072019ebf405932100cfc7158242006dd6350e201e6de4158e422975c535513104cfc7259020007e521481101467c5359640004fe7654540004fd7650e5002e7d5058a50206dd53d8d52024fc7558e10004fe7654d21006be6119120004fc7650950006de7058e420067f30d9510004fd7655210004ff7459610007b870505400267c655412017ddc73595211ee7c654c91000cfe7158a30394ff7359531024fe75d89430067e74d95101b65f53d9531006dc639815401cfe74596104367f21d953201cfe74582521def631d853204fe761487202fefa30d814304ebf7459252004fd71d8d52004ff764c550004fe764c95009ebc64591201567f7359630096fa3058232004fd72d815302cfe76c864000cfd74d8d410067c75591320057f7558d10414ff725913201cfc74d8d2121e7c6550932006bf64909102eebe4259121096dc535823204edd2158c20004fd74d853004eef60c852002cfc765502004cfc72586422367f50596424367e72d953215dbc74589501febf40592320067c7558d21004ff764c540014fd75d8153246dc31d8d521e6dc4058e4202efa60181511567c435963004cfc7259230005df7358954004ff7059232004ff7459632006dd32d813100cfc71d81520eef421d85302e6bf20d912002edf5058e5002cfc705923001cfe745842001edc7650d30186bc645
  | 3 => 0xe21d953200ef6614863000ff3604851004cfc7258d1000cfd70d911004cec7258d1004edd2158e42017cf724c930006bc51590203f6df53d855300cfe76d855304ef42158720006f561486300b4ff7258d2011ebf415921004cfd75d8d520257c7550d50004fe76949413a75f32d9531286be54d9153006ef6298910076dc3158c200e67c65c81100067e43d95101c57e75989412b774101951000df67194931014fe7650932005ef725512102efa6018153016de6354e42005bf74581211567c53d8d50244ff735953201cfc7459632004fd7690a300067f6598910017d7714c53028ef410d8554004ff7558e4204e7e525972000df4715494100cfc7159020015dc73545301ee7c50d953202eee2058a5002df8704c920006dd6354c2002dec7050b2004fac425494204cfc7258e401e6bf42d9132005f57118142004ff7358321246dc30d8d5200cff73d91310067d745963000cfe71d8d2000ede614c530216de6350a5004cfc7258c20014fd71d813104e7c42597210f6bc41d9130006bc73590203875c3119531016df604c5300067e715942004eee621895101cff7650a2016edc4358e5038e7d71d95310067f6554931006dc41d8d5204e7e215972101cfc7458e2002e7d5058650004fc7655130024fe7558c2004edc2058e42006bc535902023e7c615495025e7d73d9532004fd73d854002ebf705902002cfc764c6402667d54d9542007e7614852001cfe7458a3001cfe74d8d210fedf53d95302e6bf21d912000cfc765092101cfe74d8d503a67c43d9531486df6518d54004fd7654a30004fd769493104cfc7258640004ff7650e501bddc73581410276f6255152006ef6298943004ff7648650006df53d8d40006be75d9120096ee3258a3008eed2158a10014fe735962002cfe76d8154004fd71d912002cfe7059640224ff74591211167c5459630004ff7459721014fc73592103367c53d8154004fd72d9530024fe75592201a67c5059721007e521c8110246df30d8d52006ef725912000cfd70d95101557e735455004eee6290a3002ef771586300267e6554c200257c755065002c7d75d8d500067f315942002df4765051000cfe7158e520067f7558d1002e7e1059420014fe765013000cfe7159640004fd764c4200267e65551200075e73d9510014fe73595100067d7159420006f7715913101cff73d9543006bf73d9120004fd75d854201cfc7458a5004cfe72d9541006bf745954304e7f7559632004fd764863017ddc73549212c67c30d9510476dd75d8d54024ff76595432e6bc52d912004ebe4259252006f5614865001cfe765414002edf1058c20296dc32d8d541e79f43d913201cfc76541400067c7559131007ac64c852002dde704c930004fd70d9542006ed6248630004fe7650930006dc6118d540067d6550a30
  | 4 => 0x8a303cebf41d91510267f625515204e7e52596320077870545500067e71d953204ef772584200267c655513104cfe7258c20006ed621891004cfc72d912038e7f71d953102e7d305942004feb609092002ebd40586401b67e761953104cff769091000ef461c8550014ff764ca2040ebd54d915101cfc745863201dbc7454140004ff764c95000cfe76d8530024fc75d8d4102cfe7690a10004fe765494002edf30592300fdde754c530004ff71595300277b605515021e7c65595422cebc50d9120136f62158640024fc7559131006dc4158c2004cfc768c91012e7e65d95400067e5359252005ec725954038c7e76195311e6df5458e4204ef44258420004ff7558630024fc75d8530004ff7650d2104edc3258e52006bd64552320867c535942001ebe6450c2004cfd75d855202cfd74d8d40476dd74d8d5402cdd73d95300fedc5458e5002ef41058650007b870509400fe7c52d95301b67c54d95314367f73d953221ebd54592520067f42d95323e67d54d9541004ff7559020004ff7650a30004ff7654d2002e7f50592501657e76195100067f65d911002edc3058e1002df87048620016dc634c120005dd739095011fb461505402e6bf70d912002edf7058c200067e51d95300e67f505972004ebc7259020024fe755923219fac42d8542024fc7558d20126bf4359230004bf7459520006bc7458d2000cfe7158252024fc75d8542004fc7654d20006df7359130376bd43d913102cfd73d8530014fe73586200067f65d891004eee6218954017db604c530006dd6350a5001cfd70d9540006de31d8d2002ef45058420246de43d8d52005f7714c94124cfd765494204fac425092100df4715521000cfc7159520004ff715954004fe82054920006ed6218930004ff7159632004ff745963002cfc70d8910256f65158652024fe75586420067f655093101ef464505101567c325963000cfc74d8540014dc73595400067f74d9532004fd72d853018df571989512967e63551520a4fd765412002dbe70509402c67f71d9510004fe764c5201b67f50d9531004fc76549300067e74d9532004ff764c42004cfc7258e42014fc73584202567f51d95210079f73551410057d751894004cfe72d81533eeee52d8951006dc7058e4204dec7250420005bf745494201cfe74d9531004fd73d912104e7f4259721004ff7559130004fd72d854003dbc7458910004ff7258630004ff7459720024fc75d8132014fe73d815100eee6148520006de7158e4201cfe76d912104e7c215942004cff71d8d2102cfd7059210006f475584202967e5359543496df51d8d5425e7e30d9532005df7150d30007b77155141005bf7458131005f5718c910006dc10d8d540067e5359540005bf745891004dec7255220006df735954004cfe72d91301e6de7458e420067
  | 5 => 0x6bd64550200075f7355150306fa30d8153287ac4254d422367c6590931014ff71d913100cfe76d855002cfe70d8532066f551d8550004fd75d8141007af64485200067e63d951002cfe76d8151006be41d913002cfc764ca400076c6254950014fc7359521006df7358d200267f605515001cfe745963204e7e525972104cfe76d89100073d5450550006df6358554024fc7558a10004fc764c94028fb7105514101cfc74d813204cfe72d8530006be65d912009ebf42d912000dde714c931006dc40d8d5211fb7105054001ebc64909500257f715455000ef4614852001cfc74d8d2002e7f405942004ebe425923202cfc76546202067f5059632206de50d8d521e7ac4258d4243ebc42d854201cfc74d95300067c65d9132226f45158642006df4358f21004ff72592300077b70551501bdde7398941004fc76485500076f62549500257e7548550006df735953004cfe72d8540015df714c53023e7d41597211c57c7558d41014fe73d814204cfc725963016edc3258e500067f6558d10024fe75d8d421667e41d9510004fc7655120006df53d8530004ff7058e520057f754c9510057d75c8640256f63158652006f7715954104cfe72d8151006be4258640006dc7458c20004fc7650d513b5f77158d41006dc61d8d5204edc2158e4202cfe70d8d54056de4358e100257e75c865000cfc71d814301cbc7458d20004ff7158e4202eef7258a5020ebf4159321007d7714c931004ff7650e5211ef661d8540004fd75d8132006be71d91201167f515963004cff76c863002cfe7654a1024f3c645515204ef7425842025f5f31d953201cfc74d852002e7c1059630015dc735013033eef21d893104cff74d9542014fc735922002efa601814312d7c754c5402c67c40d951002cfe76d81310267e6554640014fc73d89510067c65989310c57c754c62012e7c6559540005bf744c941004ff7650d522367c51d9152006fb609814137f5f30195310075f654c93102ef7715862004cfc768c9400067f7559540004fd73d855202edc3058c200257e75d8552004fd74d895100cfc715954025e7f72d9532004ff7258640024fc75d8930005df73549100067c631951039df771595312c67c70d9510005bd74c854001e7c7655150006dc63d85522cebf6290a400067c64d9510005bd748c940005df73591501a67e65c863004c7c7655152014fe735864225cff7559532005bf744ca4023e7d515972102cfc76506503aebf40d8941126dc31d8d400047f755864004efb205823238edd73d953115e7d54596402e6be72d9120007af6290941024fc75583212065f535963201cff765032022edf3158e4200cfd70d8d10005dd7390a10006be21d91203857e76d9531004ff7655232006dc63d81540fddc754c930024fe75d8d40006dc63d815202edd305
  | 6 => 0xe7390910006bf7459540017cf724c93104fce7390920004fd764ca500867c5159420006bc7458a10015dc735093203ef541586404765d75d8d54006f5615042001cfe74595200067e53582520057f715515001cfc745891000774654851002edc7058e50004ff7458e1038e7c10d953104ef752584200257e75509500dfac42d8142004ff7058f21004ff7558321004ff7654640024fc75d89310067e53d95210057d755055003fb74050510006dc7558c20004fd73d8154004ff764ca401f6dd31d8d21006df71d8d520067f65d813138e7f51d95313a6dc53d9531014fe7359521004ff7458910296de53d8d5414ef631d8550005df735512102edc1058e501dedf3158f210047d75d854223ef410d855200ef66148640024fc75d854002ef64058420004fd74d952001cff7650130024fd71d8951006bf6454520005bf74581320067e53d9520227b7109094102cfc7058a40014fc7359520024fc75d8d2100cfd75d91512c67c20d95104867f53d95430067e54d9532004ff7458a1004cff7258c200c67f5159620004fd72d8143056f531d8530024fc7558e40006bf7559020476dc75d8d54006f9601815308df4715952001cfd70d8d4035ddf735913116cff7559530006dc63189540067c65181310076c7255152006bd651912017ddc735812101cfc7458a1000ebc615054022edc5358e4202edc7058c2023e7e3159721004fd7650e10006dc64d8d52005f771551213eeed52d8951004ff755823204cff7690a301aebc644c5200075f754c930014de76d8d5401cfc74595101575c5358d50006df43d8d51004fd75d812102dee70c85200cdfb70589104367c72d953201cfe7458620004ff7655321006fb609812102ebe205902000cfc71d954304fe4214852001ebc645013002eed205862001cfd72d954226ef631d854302ef82058a20004fd74d95320aef6415862002cfe70d8553006bc715902023cfd765492101ebc6450120004ff765513201ebc6455130004ff764c62007ebf4159020006f5615442042eee32d895304cfe72d9131004fd75d8d4201ebc645512024ebf415964201cbc7458d10004fd7694a1000cfc7648110004fd75d8520296de635502004e7f7259721006de41d8d52076de4358c2000fe772485101ee7f52d9532006fb60981430057f754ca400067f7559132014fe735864009eed4258a400067e74596300067e5459721005dd7390a50014fe76d8d5202cfe7059420014fe735912004ebe4259321014fe735932102ebd705902001cfe74d9530006dd74d8d52126df30d8d40006bd644c42002cfc70d8d10006df63d8554004fd76c8650005f7715893020ef46158542004fd71d815201cfd73d8543016de634c420306dc53d8153004ff764ca50004fd7655020014fc73d9510024fe75d8131006ed6290a50
  | 7 => 0x862001cfd71d81411def410d853202eef7258a10006dc6118d521567f535963002cfc7650920004fe764c941024fe76d95100467f54d9510006bf6550540126de43d8d400057d75181420fe5f53d95300057d75d8d40014fc7359121024fe755921001cfe74586500067f65949300067f7559530004fd764c720014fc73d8950006de4158c2002cec7650920005bf725054000cfe765492104cfd7258c20006de71d8d5200cfd74d8941014fc73592520defa40d81424267f631953209df970989400267e6554a40016df604c9300075f43d95321c57c755814100cfc71d8940035dc735491002ef7505842002ede7058c2004eec628c940004ff76551310067f6554110006df43d8d521e6df4058e4200df4714c941014fc76509320067c7558d20004fd70d89511cdde739815101cfd70d8540156dc43d8d50004fd74d8d10004ff745865001ebe6450630005ef7258540006de7558e4200cfc715823209ebe54d912001dbf7555141005dd7390930016df6050d30004fd7650d21004fd7655321006df10d8d54004fe7655120006df7359520004fc7654520004fd73d891004e7d7259721014fd71d913104efb205825206ef6315842027cff715953116dde7390a5004d7e7255152024fe75582320057f754c941345ef725912125e7e31d953204cfc725954302edc4058c20396df31d8d51006f654584200057f75591311c57c754c941416ee32d8943005f7715092100dbc7190941006f7715891001cfc74d8d51005ee76c852009ebf415824213ebf43d913002ede5058c2002cfe70d8d412e6be52d91200273f74551520057f755853001cfe74d815202ef77158650014fe73d8520004ff7559110006bf7459131006bf52d912004cfd74d81420247e75d8d40004fd74d893001cfc74596203a67c32d953101cfe74d893118d7c754c921014fe76d8d410fedf5158e50004fd75d8d10004ff7059531466dc20d8d5201cfc7458e1002cff71d91102cebc70d91201ee7f50d9532014fc73d954101ebc649093002cfd72d9120004ff7458a300067f43d95102debf6219120005df735523202eef20586202975e75d8d54006bf7458a1004cfe7259252005bf7458d20014fc73d89411c73c5355141024fe7558620014fe7358a50006f96018131015de73d9530006bf6450520016de634c52001cfe7458e1001eac649092002ebf7459210476dc54d8d54004ff7258d1000cfc71595320c67f54d89501667c5158650024fc75d9120005fb704ca200067f655911004ebe4259020004ff735842004cfc76553200057f7558910024fc75591100d6df31d8132024fe76d9521124ff735913002edd1058c20004ef7258d100a67c5158a5004ef652584204367c42d95321a67f505972100cfc7159250016dc638c950014dc7359110005ec7259110035d
  | 8 => 0x2e7f1059630004fe7650d210b6df31d8930014fe73d91500067c74597210079c735514102cfc7648640004fd7694a400047f7558e420067f6554140004ff7650c20004fd73d89511d6bc645915102ef610586200057d7518141014fe76d8d5004ef55258420014fc7358620004fe7650951006ef72591320067f72d953102edc2058c20005df7354a10004fd7655132004df7359721246df31d8d52005bd7498931004fd74d815302e7c5059610004fe7648540004fd75d8941004fd768c9511667c21d95100067d654c420004fd76c8550014fc73d91202eebf629094118e7f5059521004fd7654d10005df7348630176bf41592500067f415942002e7e2059420006bf6450932166f6415865004ebf325902004eef605092001cfc74d855017ede634865002df8704852028f3c51551414975c51d8d54005df7350630004fe7654910024fe75d8520017db6050d3004cfc769491001ef664505100067c65591320fe7f50d953004eee62c86301567e325963002cfc7650a501b6df5359531004fd73d855001cfd72d8542446df43d894312ebd545925001eee6450b20206df54d8d520067f71d9532006df70d8d54014fc7358a403067e53d8153004fe7694930004fd75d9121004fd769093001eec7650920004fd765042002eef7258a300267e65546301aebf42d91310ecff7158d10495df7359153014fc7358a5025e7c43d9532006bd7559020004fd71d814304cfe7655321004df735972004cfc7655232004ff73591101575c535953002e7d405942000ddc764c9310057d759894102ebe3059020016dc638c91002ebc405922004e7e725972100ebc765054025ede5358e52004fe765453009ded749092000cfe71d9540004ff7650910005dd73c8530296dc31d8d540067f6558132006ed6218950106f641586301667f31d95100067d65550201b5dc754c93125f5c5394930004ff7650e10206dd50d8d5201cfe7458a501e6dc4158e42024fc7558d102d7b8201912002cfc7654a3002ede7058e500067f7359721005dd7398954004fe7690930006ef72595200beee42d8940014fd74d8143004fe76505500d6fa30d813204cff768ca50024fe7558a4000cfc71d9510006dc73595420a67c65595202c67e10d9510006bf50d91204867d53d9543014fc735864200ef7604851002ff01054110017db604c93002cfd7058a100067d654863004ef42158632004fd7654d2047cff745954302cfc70586420067c75586400067f6554932014fc73d8552004ff7358242004fd7650d2001cfc74d8d520057d75d8542004fd71d9530006dc5158e421e6de644c931006bc7459520004ff755862013cff7459130006bf64d8d2002cfc70596200267c6554130006be31d91200257e75c85504779c54d8d540067c43597210067c74d953200ef6614
  | 9 => 0xf7458232005df7359110004fd7654f2002cfe7654e10006dd638ca5000ddc714c9310067c65d853200cfe71d8953014fd74d85430067f6598131005f7714c921005bf744c640156dc32d8d500067f6550932006bf6458520024fd73d915347ebf43d9153004fd70d8552004fe7654930296dc30d8d54296de63d8d54004fd70d8953294ff73595430057d7598143004fd70d85540075c7355150004ff7655120006dc73597202767c52d9543024fe75d89300067f654c1100067e64d95100efd4614c53004ebd3259020004ff73593202757e75981432cfad6290a4000cfd73d813127ef4615855301d7d75d855402cfe76552200267c6554921014fe73d912004eee76c85201567c31596301d6be645442004e7d52582521ee7c54d953202cfc7059220004fd73d91521567d53596300467c53d9510004fd73d95210eedf3158e1025c7e7619532024fc7558f2004ebc4259252007cc624c93100ef461c8530177ac4250a5000cfc71595421567e735963004d7c765515204eec6250931004fe7654d4204edd3258232004fd768c95003ebc42d9110006bf6458d20024fc755863238e5d73d9531004ff7655210024fc7558720004ff7559321024fe75d894102eec2058a3009ebc43d912004cfc76503201767f54d954002cfc7650630007b541501100067f755954318d7e75181210fede7558e50004fd764c910014fc7358910004fd72d8d54216bd43592320067c655853201cfc74d891038e7d21d9531006dd6348650006ec7259110466df63989530267e6594a30014fc73586403a67f53d953101cfe74d8d1017edf32d8d210debf4059320006df4358c20007b5545051027ef651d8553005f77154921296df30d8d5400cfc7159530476dc41d8d5404e7e4259420004fc764c5200e67f54d815200ef66148650226bf41d9121006df7458e5004cfd71d912104cfe76d893116ede5358e5038e7c73d9531004ff735865202cfe70586500fd5c754c93001cfe74d8131036df3258d10006de70d8d521a67c5459721004fd7650e52006dc7458e501bedf32d8d41006dc7158c20466dc21d8d522eebc42591211bede63d8d4104edf325823203fac425091004ede7258e420267c65949100a57c754c5200247c7559131016de638ca50006f44358420006df735954301cfc74d895304c7d75d85520067e535962002cfc764863038f7431d9531006ed621895104eec6450b200267c6554140024fd71d8151006bf6454920004fe765091004cfd71d8121014fc73d9520015dc73486300b6ee32d893002cfc7059542005df7354530024fc75d8d421c67e6550630004ff715964204e7d425972102cff7058a10006dc6418d5204ede3258e52024ff7654110004fc764c95100ddd73d95310247c7558d20005df7250d3001d7d75d8d54006f77458420
  | 10 => 0x8e52006df70d8d5200cfc71d8954006df6350d2100cfe71d91324367c32d953202cfc764ca50004fd76c8640006dd64d8d52006bf645092000cfc7258f21024ff7654932004ff7654e20004fd7654d211557e735515004cfc725865204cfe7259232006df74d8d520067f755862000cfe71d8d40024fc7559321004fd764ca10005df7359540016dc634c921006df635815402cfe7650e2001cfc74d895102cfc7650e5010ebf4159230007ac6250940004fd70d855301ebf6155141004fc7654530006f47158d2000cfd75d89510267c655491009ebc54d91200067e61195320067f40d95101677621d951004edc7258e4200cfc7258321004ff764c910007d87050d30015de73d9531005df7354930006de7158e50004fd75d891000cfe71d894304cfc725863204cfe72d9540024fc75d85320067d74d9510015de7350930006dc63d855402cdc7650d3014e7d515961027ef66154c200057f7558931296de43d8d54006df634c92100cfe765011004cfc768c94102edf1058e50006df735953201ebc6450d2005ef541d8540016de634c9100ccff7058910006f45458420014fe76d8d1002e7e305942028ef661d855404cfc7654120024fe75d891002e7f3059630014fe73d912100cfc7159120316fa40d814304ede2058e42006dd634c910007b64250510006dc71d8d52006f751d8520005ef725502000cff764862004cfe76d89430067d75d8d4002ebf745922002ede1058c2000df47148110004ff7654c20006dc635855438e7f10d953102e7e705942028e7c5159541024fe75d8540005dd739093109dbe76d912028e7c51d855400cfc72d8520024fe755913100cfc71d9132076df3158c20006be5159020014fc73d915104cfe72d8554014fc73d91520067c651893102cf4764851000cfc71d8d422af78101951004feb60c8520006bd715902004f6e75c85201e6df4158e42005fb704c920006df634c9410067d745942000cfe71596203a67e32d9531006bd6450c20004fd7654630014fe735912104cfe725865202cfd74d894004eee62189531e6dd4058e42004ff7159720004ff7059543014fd75d9153016de6350c2002edd5058c20006de7458e5015cff745954001cfe745953000e7c765455002cfd75d855001ebe6450420004fd7654c20004fd75d913200cfc715964202ead20590200e57c754c72001dbf7150540187ac425854204cfe72d9520004fe7650d20007d8704c9303ee7f50d89511eedd5358e5209fac6450920014fe735961002eec2058a10006df5458c20006bc65d912004ef54258420004ff7259640366bd41d91310fd7e75c85300067c70d9531024fe7558f21006ed62c865000cfd73d893104dec725532102cff73d91300cefa10d812100cfc71d8d54005ed7218141155de7390950006df7558e42004f
  | 11 => 0x15dc735523201cfe7458d1033cff7258d2122edc43d9132006f960181320d6dc4358f2002cfe70d954104cfc7650e520fdde7550d300075c754c5301ee7f51d9532014fe73d954025f5c5394931004ff7259250004fd74d8552006df53d8d20006ef6250931006fb6098131006df73591320047f755911002cfe7059610024fe75d9110076dc5358c20004ff70596322e6bc32d912002cfe70d95100057f715495027cfd75d953100dbc765514102cff73d95300067e51d91520067c10d953200cfc76c81101dedd3158f2104eee62189430067c71596303875c73195310057f7558543004fd73d9110006bd6550540346bd74d894100cfe71d813200cfd72d95210067c651813200eee614872001cfe745972001cfe74d953200cfc7159220004ff7158c201dfd4714c931004fd74d89100067d75d8542014fd75d855323e7f515972102cfc7650e10006de61d8d540057f755893002cfc76504202965e53d8d5404eee6290a10004fd71d9542036dc43d8d10004fd764c620006df535863200df47150110004fd73d812123e7c10597212cfae4090920004ff7358620004ff7654520006fb609815304efb7058321295dc7358954004fe764c54002edd30592300067c65589100179f7450d3004cfd73d953226cfd74d913100cfe76d85542e7bb20d9120055dc7354a101467f52d915000cfe71d915201cfe74d8d52024fc7558420004fd73d8542136bd41d9110024fc7559120005df7359151007ae4250520004fd74d9530005df735952000cfc715942002cfe705963002cfe7650a1004cfe725902002ebd2059020016dc6350d210fedf5359530005df7355110246de75d8d52006de72d8d54005ef72501203a65e73d9531014fc765493204ef4325842017ddc7355121006ed62486400247c75591102d6bf601912004cfe72d9543004dd73d9510006fb705954002e7c305963002ef6105865002ebf2059020006df40d8d52024fe75d912002efa6018142014fc735954004edc2158c200667f52596101e6bc644c920006df53d8d42007db7050d300067c705972104cff71d912138e7c31d95310075f73549501667e71d9510004fd7650a50155dc7358950246dc535963201ebf619094104ede4258e42005df735815404dec7250620056dc5358e10017d7614c93109faf40509200057f755813112d7e7518940035dc7358910004fd7654e4216edc3158e5004e7f325942002ef6105863000cfe71d8143006df7359521006ef624c9403a67d53d9531004ff705972104ef66248510014fc7654130006ef725912104efb2058242055de7390a10024fe75d813200cfe71d8d4202eaf2059020004fd764c650004be7619120004ff7459620024fd70d91500fedd5358e50006de64d8d523bedd43d8d4100dbe715514101ebe6450a3025edf305
  | 12 => 0x96018142356df30d8931006df7258e50016df614c93124f3f415515201dbc7454941006f77159531015dc7354930016dc634c940007776550510004fd7654e40006f761c8530004fe764c9402efae425072004ef7715863204cfc72586502cebc10d9120024fe7558720005dd739815203ebc425864002edc3058e5002edf4058c2001cfc74d952102d7e705455000cfe71d91200067e64d953104cfc725964217df571989310257e7550550015de735053004cff72590202cfac20d912012e7c51d95401b67c6559531014fc7358a10006dc7359721264ff7559542004fd765512102e7d10596300247c7558d101667d70d9510004fd73d815220ef710591211bedf3059131006f77158d21004ff7558a100067d74d95310067c6559131004fd7654910014fc73d9542004fd70d953101cfc745862004cff73d9532395df73595310067f65d91310047f755862005fac4250a1002ef4105864002ebd4058a4002cfc705902002ef41058420014fd70d853008df970989100067e5159420004fd71d81420067d6550c20024ff7654120004fd76949403a67c30d95311c67c50d954102ebf4058a40004fc7655132004ff725954302e7d2059420006dd71d8d540257c754ca50004fd75d91300f6bf40d913000cf47158d20004ff7359640004fd76c8530006f7515842004dec725412000cfe715963002cfe705923004e7d325942005ebf42592104af9c5418d5404ebf215902002edf7058e5001cfe7459420004fd7694a3002cfd73d95300067c4159630004ef7259540005dd7390a3002efa601815404ebf7459321005f7715895001ebe6450620004fe7655132006df7359110024fc7558e42004fd70d8d21206dc51d8d52004ff7259540014fe73d915104edc764c93102ddc704c5300247e76d95102cfaf2090a400057d759813121e7e6550a30006f96018141004ff7158a4002cbc7650540004ff70595413a67f30d9531007cf624c931024fd74d8154007f07048510005df704c931004ff7654540005ef725032038f5e31d9531005ef7254120266be5459252006dc73595400067e5158a50006f771591210267e6554a3000cfe71591202af76411951004cfe72d912004ebc52590200057d751812104edf7358f21016dc634c920015de739093028ef641d855402edd7058c2015fac42509500057f754865000cfc71d8910004ff7158f20004fd75d854000cfe7159250004fd74d895321e7c6550910476dc40d8d542967c53595430457c754c910496de50d8d5404def7650b20006bd6450320004fd70d8d5400df4715492130efa40d8141295dc73585540dfaf4050b20005df73595410067f6558931004fd73d81421567e4359630006dc4158e500bfac4298142004fd74d8550004fd70d913109dbc745952000cfe76c8110004ff7158d20
  | 13 => 0x9531476dc74d8d5400cfc715913204eee62c864002cff755942028e7e615515004cfc7258232036dc32d8d10006df7158e4204ebc42592322af7b1019510007ad42501200067e5359721005df735502004eef60485202075f54d8d521a67f5359721004fd71d8953004ff7159250004ff73590203d4ff755954121e7f52d95420a6ee5258a5001cfe74582320067e72d953111ebd41592102c67e20d951003ebc43d9110004ff764c94002ebe405921039edc53d8553005f77158d20006df5358e400067e4159630004fd76909500075c735495001cfc745972001cfc7459532004ff7655121214ff73591322cfaf72d91200067f65d913204ef7215864201cfc74d853002cfc764c420206df7359632096dc31d8d20004fd74d8d50014fd74d8943004fd7655320004fd7690951024fe75d913102cfe76d814100eec61c8520014fe73d812104cfc7258e52004ff7650930004fe7690951004ff7358a50024fd74d895401dbc7454a40006bf6455130004ff76546202975c7518d54004fd73d894100cfe71d9520004fd71d815300cfe71d8950156de53d8d50006de6418d520267c65551300267e655532102cff74d954004cfc764c12002e7c405963004ebe725902020ef641d854204ef7215872000cfd74d814115ebf40d915002dbe70505402e6bd6290a40006dd6418d521aebc645913102e7f205942016edc53d953038e7c41d95311667f41d9510004ff725953104cfe72594203a67e43d9531015df724c930476de41d8d54007d7614c53004cfc725951000cfe7158a500067f6550110005df735013000cfc7158e5208ded71c85200067f65551101667e51586501667d31d9510006dc5158c20005f7715813209f3e7519120466df6318953014fe73d854216ede4358e50005ef7250420006ec52d89401b57c75589310075f754c931014fc73d815104e7c325972123e7c51d855204efb7058242006bf645093102cfc70595414a75c5118d540057f7558141004ff7359420004ff74583211b55c754c93141f6f3219532126dc53d8d400067e70d95312467f5359632007e87048520286be64d915334def725952104cff7694a101def661d8532004fe7650d50036dc6358d1004dec7254320004ff7650d1000cfe71d815404ebe4259320006f761485200067d6554a1004edf7258e42005dd7318910004fd764c640004fd75d8d410a57c7558520004ff7059521004fc76485400067f645495001cfe74d8132006bf51d91200067c659813234cff7259521005ef7150920336fa50d8154004fd73d8151004fd7650650014fc73d954002cfe7058e4025e5e5358e52006dd71d8d52004ff7650d2002e7c505964004cfe72d8143005ef7254320004ff74586320067c65d8931246dc6358d5200cfe71d95320277771545500067d54d8950006f
  | 14 => 0x4ff7458630014fe7359220024fe755912001ebe6450320006bf74591320067d6554640004fd7650c2001edc6450d3023e7f105972100cfe7159532216dc4359132006be65191200067f655412024fac425954204cfc725963201dbc744ca400eedd3158e10014fc7359110006dd7158c2002cfe705863014ef661d8550226be769094104faf74509200267e6554320004fd7650d10004ff7458e5204cfd71d8d21004fc7655121004ff725913004cff769491002cfc7059632007ad425032028f7651d85542b776101951004ebf72590200067c40d9531006bf64909302967d75d8d54096df30d8d20006f751d8540024fc755823202edc4058e5008ef431d85200065f7558e420057f754c6500067d54d81520067e7459721005f77155210476df54d8d542075c51d8d5209fac425814223df47158152006ef6298940014fe7654932016de634ca10004ff7650f20006bc71d912004e7e32597211e6dd4358e4201cfc7459630004ff7654a4024ebc40d915221e7c535925204ef771586420277b6054550014fd75d895302e7e5059620015de7394930004ff7654e421e6dc644c93002ebc7059020006f67358420006de5158e420057f754c92102cfc7059232154fd76541301767d54d954004ef82058321004ff764853004e7c52594200057f7558532014fe7359320496dd50d8d5401cfc74d8553024fe76d953101cfc74d8d50216de43d8d420057f7550d50014fd72d853204cff7694a3004fe42154921004fd7650e2008ef710d852023d7c7155152006ec7258d1004cfc72d952002cfd75d9150006bf645013004eee621891000cfc7158f20004ff7358642004fe76c853002cfe768ca1004edd2058e420067d73594200f7ac4250930014fe76d8d5425e7f53d9532004fd72d855401cfe74d85533d67d51d95410067f6590910005df7354a2004cfc76949314575f5418d5204cff72594200057d7598931005df73591522cebf6490a10014fc73d854002edd1058e50006df624c530004fd73d915112e7c5359540006df638c950006ef7259542006df73591310067f74d953138e7d10d9531005ec725815449ebd54d915300cfc71d894304edc3258f20004ff7654a300067e641953204ebc425902000cfe7159642004fd72d951002ddc764c530005df73549400247c7558f2002ebc505902004ebe2159020004ff7059121005ec7258d1002cfc70d911004efb705825204e7d215972102e7e5059630024fd71d9151004ff765065000cbc765514104ebc4259321024fc755824211ef4615854002cfc7059132256f710586521e6dd5458e421e6dc644c931006bc61d9120005df7354931005ef7150b2001cfe74d8950006df41d8d52004fd71d8d4202c7c7654550006f77159510206dd54d8d5202cfc70594201557c735455001cfe745
  | 15 => 0xe7458f21296de7618d54466de42d8d52006bf73590201d6bc645452000cff73d9531004fd71d8940004fe76545200057f755913202e7d705963004cfc72591302eebc42d89410067f655494228ef651d8554005df7358520004df735954202ede2058c20004fc7650d5000778705495004cfc725824229dfb7058d100a6ed5258a5004ddd73d9132004fd7654e103a77731d9531015de73c8530004fd71d8954024fe755932004cfc725825200cfd72d8d21256f44158652024fe75d8542006bd6454420004ff7159120024fd72d8d5216e7f53d95300267c6594931006df4358e520067f10d9532024fc75591301cede6354420024fc75d89101555c735495023e7c31597211157e75c863041f5c431953204faf7450b2004ef632584200257c754c9500267f60545500257f7455150006dd634c420015de73909313cdbf7459541005df735954203dbc7458d1002cfe70d8d21006df4158c2002cfc705862004eee6290a500067d6554f210657c754ca10006dd5458c20015dc735413038e7e41d9531014fc7358242006bf6448520116dd53d8d5002edd4058c201ed7e75981321d6be54d915101cfc74586521def641d853204cfc76c855002e7c70596301febe5459232005fb7048620296dc6358d5400cfc71d813204ef4764851001dbc744c9411467f5259640006be53d912000cfc7158e40004df7359541006f47458420006dc21d8d5401cfc74d9540014fd71d953101ebe6450a20004fd76909312c67e30d951004cfe76d8953006bf53d9120006de6118d540067c6419532004fd73d852004cfc7650120006ee21d894001fae7290a40006dc63581542467d53596321567f435963001cfc7458f21006bf7458d2012d7e75c8540006f561486401b67e654c42002d7c705515002e7f75596400067c73d951020ebd415932128f3e515514104edf2058e4202cfc7059521004fd7690a100067c65d8d1002cfc7059610014fe735925215ebe64d9150004ff7650951006dc7258e50006fb705953001cff71d954102ef71059210006df6358152007ac6448520335fb7059150024fc7558620056dc53d8530126bd43592300075e51d8d540067f6518910004fd75d913104edc7258c2002cff7059610006df63d89544367e32d953201cfe74596201457c754c640006f6535842018e7f54d952102e7c2059630014fc7358652006de4158e5014ef710d8550094ff7358d2002cfc7654a100267e65550200067f6558131006f75358420006de7558c20016de6350e10006dd7058e42024fe75590200067e735972102ede5058e5048e7f54d9543007b761505401c67f52d9541005df73552101cedc6358d5123ef641d8552004fd73d8141004f77159540296df31d8d540067f75591313f5f77158d5104e7f21594200067f715963000cfc71d8d10
  | 16 => 0x954202ebf745923002cfd73d9130006bd7359020004fd74d8d20004ff764c951006df53d813125e7f30d953228e7e51d8554024fc7559232004ff765491008cfd76481100067c215963014e7f5159610014fe73d913004ede7258c20006fb7058d10004ff70591311b67e65d953107ebe54590200067e745942000cfe7258f210067f65549410075d54d8d52154ff7359530007d8704c53033def7258d2101cfe74d8550024fd70d8550005bf7454140004ff715962014ef441d855006ef43158420006f5535842000cfc71d952004cfd70d8520227b6719094100cfe76d8542004ff7459520004ff74586200a67c5358252006df4358e50006bc7458d10004ff755912004edf2158e4204ebe5259020007db704c93002cfe705921024cff745954204cfe72d81310067f655853204edc5258e42005df7355130004bf7458d2004ede4258c20004fe768c951014fc73d9150004ff755913100cfe71d95301567f315963018e7c53d952123e7c4159721006dc70d8d5402cfe70d9521006ed621894302eee2058a30035dc7359110005ef7258d10006ed6218940004ff745842008efa1058321004ff73591210067c7159420246df32d8d5204e7c425942002df6704851002ef71058a10015dc7354931004ff7359721125dc735494001cfc74d812102cfe70d895400cf471595402e6be32d9120005f57448510014de73d9510004fd7650a1000df4714c92104e7e21594200bebf4159220006bf10d91200a67c53d9520094fd764c12025e7d53d95320067f7259630155dc735915025e7c31d953201ebc6450520004ff70593211bede6350420005dd739894004e7e625495001dbc744c640006ef72595320057f755894304ebf525902002e7e1059630024fc7558a30035dc7355110004ff7458d21246de7618d5223e7f7159721006bd645042027ef631d8553006df5358e20006ed6218931005ec725854002ebe405902002cfe765502001cfc74d85521575c538c950006ec42d895001cfe7459521006ef32d891000cfc71592300f6be64d9130004fd74d852002e7c5059420004fc7648530024fe75d81420057f754c42002cfc7258f2031cff7059540006dd73d951001dbc749494101cfc74d953209efa4058242146bd54d915001cfe76d91510057f7255150156df30d8d5002ef7705842001cfc7458f2004cfd7259420126de63d8d40036f5315863002edc2058e5000cf4715952000edc614c530006df6358552004ff70595321167f545963004ebf4258242014fc73d8152006df63981521d6be64d915101dbc7454942024ff7654921004ff73597200057f745455000cfc71d91300067f6559132024fe7558630006f7755842004cfe72d95103867f63195310067f32d9510005df7354a3002cfc7058a5004eee6250a3002cfd71d891001cf
  | 17 => 0x38e7f31d953104cfc725925202e7d3059630004fc7654d4206ef4415842004edc624c93013ebd43d91302767e6550f210a67c51d9520004ff7259131005f77154a1004e7e725942001cfe74d954013ede4358e4000cfc71592522767c51d954300cfe71d91531ed7c7558532006ef6298954004ff7655110004fc764c550004ff7558f2138e7e10d95311567c73596300067e61d95321afac4250931295de7398154004ff76505500fdde754c93016edf3158e5001cfc7458d20006dc74d8d52014fc7650130014fe735865200cfe7159530005ef7258141006de61d8d52006ed6290a10004ff7558e40004fc76551312067c658c91000cfd75d8151015de7390a30014fc735825200edc764c530005bd709094125e7c30d953202cfc7654e20007f0705051047e7e53d915302ede1058e500fe7e65d9530004bf7458d1001ebf60505400f79c6450d304275c321953204cfe725863203fb4425051002ede3058c201667c71d951002ef7305842016e7d53d95300eef631d853002dee7048520004ff715932000cfc71d8d40006ef7258d100067f6550d1000df77450510006bd75d912001fba6090a402cdbd7090a4001cfc745972124e7f5459642005ed7448520005ef7255220006ef52d8940014fe735832104cfd725902004feb60509200067f735942004cfe76d895402cfc7058e10014fe7358242006ef624811018e7e6548630185f5719894102edc3058e4004cfc7259531006ef6298950006dc73595210257e75d8d50016dc634c110176bf42592500277b60549500067c7558f20004ff7458c2004fe7714852014ef46158550004fd71d915301cfc74d895002df87050a20004ff755912102eee2058a10004ff7655020014fe735964202cfe70d8951004ff7654e40004ff7159132006ec21d89300067d6554a400267c6554931006bc64d8d200c67f54596200467e7619510004ff7558a40014fc73d8154006bc31d9120014fe73d91520057d759095002ebf50590204575c5118d52006ed6290a3002cfe70d9543006bd6450a100057f754c55002cfd72d9520006bf6454d20007bb7050940006df635895402cfc7654c2004cfe72d915302cfe70d85420067c41d95323367f52d8154006f960181210067c30597210067f654c910015df724c93120ef661d8542006dc7359520006bf64909500067f65d853202dec709092004e7f4259420006be755902000cfe71d8152006ef42d8950024fe76d9520004fd75d8d40006dc635815201cfc74d8d10286bc6459153004fd70d8d52004ff7158a50006be3159020005bd759094100cfc7158a30006df631815400cfe725972100cfc764c1100b5dc7354a2000eec61487200467c6559510014fe7358252005bf745852002ede3058e10006ed6250a5004cfe72d85500067f3059721024fe76d
  | 18 => 0xf20d8d5202ef43058420006ef7258d2104cfc769494102c7c765515019ebc435932104ef67258420056df3258e102c77410d9510024fc7558910006bc6458d2002eef7258a4002df87054a201e6bc40d91320067f6518132006dc6318154006dc7359110006dc63981522cebc30d91201565e53d8d50005f77154110006dd7558e420c6ee52d8950006dd634ca1002ebe405925004e7e52594200267c6554d1004efb2058a200067e51d954004cfe72d8d20006bd6450650004fd75d8530004fe765511001dbf7250940004fd70d9121005df7358951006dc7558e42004fd71d915202cfe705864002fe820541200247e76d9531004ff7359220005df7354932004fd7650f200067f65c811001faf725094001eee649092021d7e751814204e7f7259420004fe765053007ebc43590202367f50d91520067f6548110004fd70d8532006fb7058d2002e7e4059420004ff76552202eebc6250540024fe76d9543005ec7258530004fe7690910004ff7159420004ff7558e200fedf5458e500067d71d953202dde7050d30476df40d8d5404cec7259540015dc7354a300067d6550420024fe755923001cfc7458d10004ff765062004cfc725954002dbc705094044eee42d8954004ff7650d5021e7c655093102e7c7059420005dd744c53004fac4250a2025e7e43d95321cedc53595312757c755894300cfc71d9152004fd72d8d40014fc73d911002dee70487203067c53d815301fb77150540024fe7558910004fd74d8121024fd72d9152004fe765093102eec2058a4002cfe7650c2002cfd71d951024ebc6454920207cc52d8d52024fc75d9110005dd7394930004fd72d9150005ed744872004edc4258e42006ef62c81101ee7c65595321def46158532004ff715824247dbf7459543004ff764c941005f5719491004eee6218941005df73549200067c65d813201cfc74595300467e65d951001ebc645093201fb7615514104fe77148720006f7715952002e7f755942001cfd75d8d5411ef710d8540096de63d8d2002cfc705925004ede624c931005f7714ca1037f5f3219531006dc2158e50006df638c91002ebf7459250206de51d8d5238e7c21d95310057d7550950004fc7650d21004fc764c941006dc5058e4204edf7258c200247c7558e42004fd765523000cfe715925209ebc41d91200067c72d95100057f7558132007bb70505400267f6054950004ff7558c200067d6554420005f771481102ae7f60195101b67f54d9531004ff7459530186bf42d912104cfe72d814104eee6218950014ff71d9531004fd72d8d410067f72d951038e7d73d953102dec70c85200067c7558620024fe75d8d20075dc73550201ed7c755913202cfd71d8d10006bf30d912009dbc74585200067e4359721496dc51d8d54006dc7158e50014fc73d8954
  | 19 => 0x8a40005dd739095125e7c73d953207ebc545902048e7d54d95430e67f54597200067c63d951000cfc75d855002cfe70d8520006bf745954204cfe72d8d510267c655494224ebe64d915202ef51058a100057f754ca5010fac4250a3000778705515002df47648510015dc73506300257c7550e52004ff76506302cfae20d912001cfc7459420006dd6350c2004def76487200067d72d9531024fc75d8543004fd7654e200067c40d953202ef6705842004cfc769095002cfc705972102e7d505925004cfc7654f20006dc63d8954356ee32d8931006de5158c2002ef7715842001ebc645092002edf30586301b75f53d953102edd2058c2001fae72909411667f21d951004fe4614872001eac645092002eec2058a200247c75586200075e5118d54004fc765093101cfd75d855426ef641d854346e7c51d8954024fc75d8121004ff7654a10006df6350d52006f96018152006be43d9120005bf7458950005df724c530004fd76949300aeef21d891002cfc7654a40035de731891002e7f7059420004ff7558d21055dc7355210006df7158e5001cfe7458a1004ebd72590202767e6550c20006bc6519120014fc73d855401cfc74582320067e535961000cfe71d95420075d5418d520467c52d9510126df32d8d4001ebc645093102edc3058e20014fd70d95303ce7c51d9151024fe7558f2001cfc74d951002cfe70d915310ebf4259230476df74d8d54004fd7654640346f710d8941005bf744864001e7c6455152005df735815204e7c7259721006df7359541004ff73592500067e315942001eec6490920176be5459250005fb70485201167c5159630226bd41d9121004ff705954229efa10d813147edf6418d5404ebf74593203a67d30d95310067c405972101cfc765494201fb761909410057f7558d41014ff764c92101dbe749494002cfc76546400057d75c865004edd7258c2016edc7558e50004ff755864201cfc74d815202ddd73d9530004ff7558f2001ebe645055002e7f5058a50006bc6458520006f643584200067c6119532476df75d8d54004ff76553200067f7558640014fe73d8554004fd73d951002cfe7654c2004ede624c93001cfd71d89410057f754c910004ff745951001cfe74586300075c654c9310057f7558d2004ef72158632004fd72d8d510057f7055152004ff765052001cfe7458d2101cff76509212767e65d954302e7f40596300067e545942002cfd73d893004ebd5259020005df7358540006fb7059130024fd73d8153004fc7654d21006dd6350e10014fe7359720006dc70d8d52024fe75d814300cfe715932001cfe74d8d20004fe76c85503a67f43d9531014fd74d954304ede3258f2002cfc7654a202967e53d8d54024fc75590200c67c5359620004fd76c863002dec764852002ef51059210466d
  | 20 => 0x67c65d81310073f65551410057d758c950006bd6450630006dd7458e50004ff765494004eee624863002eed20584202cebc60909410067f70d9531095dc7354920004ff7654f20007e870509200457c75591100267e655521022ebf43d9132005dd731814202ebe405923006ef64158420016dc6350d5204ebd425824225e7e5358e52005dd73d9510004ff7654d4038e7e71d9531166f65158650206df72d8d522cebe50d9120024fc75d894304dec724c4200fedc5158e5012d7c754c94002edf2058c2000cfc76501102367c5159642006dc6358552014fe735952004d7c72551521e6de644c93004e7c2059721004fc7650d52004ff7159220014fc7359320014fe73590200beed42d89404979f54d8d54014fc735912031dfb7059540104ff7358d100065d73d951001cfe745963004cfe7655232004fd71d89300267c6555132024fd74d8d5401cfe74d853204ede5258e4204edf4258e4200cfe7158232004fd70d894104e7d7259420006df634c9403d67f51d95412975c535523204cff73d9132004fd74d813200cfc7158e20096dc6358d2004ebf7459232024fe76d9541004fe7650d51006df735953107eef7650b2000dbe71909410067e705972128e7e515954102cff7358c2022edf30d91322debf6418940245de739815204edf5258e42005df735522002ef4405842002edd5058e5002cfe70d89310d6df3058f2002ef65058420004ff7558d100067e53d9150004fd70d9153024fc75586420067f659813224dbc7458152024fe7558d210067e41d9532004ff7654d420067f755952001cfc7458321006bd73d91203a67e73d95311e6dd4158e4202cfe70d9542004ff755932002e7f50586501e6de4058e42006de6118d520e6fa50d81520f5bc74589300065c73597210067f655512100df47154a1002dbc7050540004ff7458f21005ef725062002cfe7654e201e6be64d9132007af64909200247e75d85420267e6555320466df21d8d52015dc73549320c6ed52d89501bdde7318141024fc75d912104cfc725953002edf4058e50286be6454c2003fb65450510005bf744811004fac6450b20005df73551310067c74d953123e7e4159721476dd40d8d54004fe768c9410067f40d9531016dc634c550014fc73593210067d6554320014fe73d8154004ff7558a30004ff7159520006bc755902001dbc7448640004fd765091000cfc71593200267c6554920475de7618d5404ebc4259320036df30d8d100057f75585200076f725515221d7e75d8542004fd71d9150466dc52d8d5200cfc71596402d7bb201912001cbe76d912002cfc7058e500b6de4358e2023e7d105972100cfe71595432cebf641814202cfe7650e10014fe7359542096ed3258a3000cfe715972029cff7058d10006fb705951025edf3158e5200cfe715
  | 21 => 0xe7358420206dc50d8d520067c65d911002cfc76549202c67f6598151004fd72d915104ef4215865204eac62509400c4ff72595201cddc73591512ad7e76d9510006df634c120004fd70d8d410067c755891002e7e205963004edf2158c2002ef4205842000cfe7158e4000df471541100067f7459630004fd71d8d501ee7e761953202eef20584204775e54d8d540057d75c855000cfc715825200cfe7158d202e6bc4258a4028cff7159541096dc53d8d20005ef72585301b57e7598131024fc7558e20006dc63589540273f745515021e7c51595421aebe64d9131024ff765494202edf7358e2000cfc71d81530067c65d8910125dc73595401567d315963025e7f43d953200cfc71d89530fddc754c530296de74d8d541b5de754c93100cfc71d9120004fd70d913200df6715091004edc5258c20476dc42d8d54014fe7358650004fe76509500067f415963001e7c645515002e7d40596300a67f545952002efa6018141024fd74d85540067d655523004cfc769095100cfc71d8d5002cbc7650940295dc73581540067c42d9510006dd7158e42004fd768ca50004ff73591202f5fb7058530006ef6298951056df32d853001f3f7555141006de74d8d52006de71d8d5401cbc7459520005ed74c852004cfc76c854038f5c31d9531006dd7558c20004ff72591100f5bc7458530216dc53d8d4217edc5358632004ff725921028df67198954006f96018143006bf64d852028e7c61551521667e21d95100057f755911002cfe7058e50004ff7458e200067c64d953102cfc764c620006ec42d8910006ef725954001cfc7459521446ee42d894321e7e65d9542004ff7159252006f731d852023e7e51d8552004fc76549410047f755913102cfc7259320006de73d951001ebf605094002dee7050920004ef725911002efa6018152007776548510004ff7458652006de3158e420257c7548650156dc535953004cfe76d8951004ff7654d41226f710d91210067f4359721006be41d91202c67e70d951004cff768c91000cfc7158a40005df7358552007e7624851000cfe7158f2002df8705092001ebe6450a1000cfc71595430067e64d953201ede6450d3000cfe71d8d541c73f5255141015dc73551301adbe74989314975f52d8d542965c635515201cfe74d8d510bcff725912004cfc7650f200c57c754ca2004ebc3259020476de42d8d5410edd43d8d401467f51596400067c6598910006df6398954095dc735952000cfe76d85202cebe70d91200067d72596302067f5459632136f6415864022cff74591321e6de5458e42457cc5218d52015de7394931476df41d8d540067c4359420004fe7694931004df73595203aeee42d894102df4704851004eee62c86502965e75d8d54004fd72d8141006df43d8d5004cfd73d81322edbf7590941
  | 22 => 0x93200047f7558f20004fd764864014ef421d85500067f6598931124fd765013001cfc7458e5202dec704872001cfc7458420006ef629893042def725953200df671909100067c6558d1004cfe72d9151006f6755842004cfc769493038d7e76195310e5fb705895004cfe72d8543296df32d8d54004fd74d853202df8705492004ef621583210067f755954124ebf41d9152296de75d8d5400cfc7158e42014fc73d953004eee621893000cfe71d895402cfc76552200fedd5458e50004df735952100cdc764c931004ff7058e420057f754ca10014fe735921000cfe7158c20024fc75d8142006de70d8d54024fc755864004cfc769093001c7d75d8d5402d7c7054550006bc63d912001e7c765515200cfd7258420004ff7654530004fd71d952002cfc7058632006be7359020004fe765494100cfe7159130236bd54d915202cfe7655230006df42d8d52006dd32d85300067d65552200067c64d9532005dd739493100777615455004feb6048520006ed62c8630164ff7559510014fe73d8951006bf74595410067f7559521006f743584202dfac201912001dbe748c940004ff7559132004fd768c940014fd72d913204ef46248510466df75d8d521ee7f54d953200cfc71d954202cfe7058e10004fd74d8d2108ef661d852004dec72551210067d6590a3004cfe72d8d100067f7558e4204eef205932100cfe71d8d5001ebe645523202cfc7694a10006df72d8d54014fc75d8d500067c641951001cfc7458e503a75f30d953102eed2059020004ff7059132006bf65d912004ef77158652004fe7654931004fd72d913114cfd765411000ef6614c42001cfc74d81310267e655522004edd5258e4201cfc74d89311a67f54597210047d75d8d40004fd768ca40004ff7654d210457c7558d1028ef6615502028cfd75d95411bddc7359541004ff715953200cfe76d854023e7f3159721004fe7654d1023e7e1059721005df735523017ede63d8d210057f754c9500067f42d95102cebc20d912031ebf41d8154005ec72581314367c20d953204cfe72d8553005f77159520004ff7654720004fd7690a500867c545942013edf3158e4002dec704852001fbb60505400f6bc42d9130004fd73d9150004ff764ca10004fd76547200aef62158620096df3158d2001cfe74d9520006bd6450a50006bf515902004faf6450b2002c7c765495004ebc6250940006df5058e42016de634c650006be63d912002dee7050b2001ef47650510006f77158d201c73f505514104e7d42594204975f50d8d54466dc42d8d5201cfe76d915304fac425092002ebc1059020004ff70586520067e53d9542005f77150110006ef42d8910006de21d8d5215f3c645515004cff76c86404367f6598953024fe75d814104cfc7259420014fe73d8552156df31d8d50014f
  | 23 => 0x6df71d8d540067f7559110024fc75d8d40006f771595400e4ff7059520156de63d8d5002efa6018132006fb60981420457e759891004eee6250a10004fc765055001cfc7459531004ff7258e40024fe76d954000cfe7158e500257e758c95041f5f3019532004fd7655220006dd6390a5000cfe71d954300eee61c85201457e75c8640024fe75d8530006bf31d912000e7e61545500fd7c75589301f6f631586321a67c53597211aebc40d9131004ff735954202cfc70592521567e5359530216de63d8d42004ff7558d2001ebc6450921006be43d911001c7d75d85540067e5359640004fd75d814304edc4258c20006bf54d9120004ff715902004cfe7654f20024fc75591210075e5118d5204edd4258e4204e7f755964202ef61058420004ff7359642004fd75d91100467f52d951004cfe72d815402cfc764ca10004ff764c5201667d41d951004ede2158c20206dd51d8d521555c735515002e7e3059630005df735413041e7f62195320067d70d953200cfe7158e202967e635515004cfe7654f21014fe73d8152036de63d8d100247c7558910004fd71d9130005ef72553210067d72d9510006bc61191200067c61d9532004fd75d894304edc624c93101cfe74586322c67e40d9510014fc73d8141006bf64509214367c21d9532024fc755913202cfe76d8153006f73158420004ff7458e5001cfe74d852002cfc7650a2004cfe7650f20014fc7358321005ef724c42001cfe7458e50216df3059132024fe7558242016de634c64000cfe71d894001cfe7458c20004f77158d2025f6f32d9532006df7358d10006bf645412002edc5058c2022ede6390a50004fd70d8543004ff7158252004ff735954100cfe7654110006f5755842001cfe745972112e7c515925009f3d7519120016dc634c9413877431195310067c7558d100067e74d953100cfe7259321245dc73591520065c7558e420057d75485502cebf72d91200067c7259630246de63d8d5200cdd73d9531006f75158642006ed62486500067c7559110007f370485100257e75d8d540e67c51597201557c735495004e7c325942011ef641d85400057f754c620024fc7558d21216dc6358d4202d7e705495002cfe70d894101cfc74582520067f7159420006dd634c650004fd74d9521006f7545842001cfe74d85300067e6319510004fe768c910005f77250510004fd75d853202cfc764c650006df7158c200067f65551310067e53d954108eef2158a10006bf7459520006df4158e5002cff71d8d101667d51d951004cfc7259210005dd739815400cfc7159720024fe76d953024e7d545964202edd4058e50014fe73597210075f7355152004fd71d8d2009cff74591204675c52d8d5209ebf43d912038e7f41d953102ef5505842020cff7159121207cf52d8d52024fc755
  | 24 => 0xe31d8d52014dc73597203a67e30d953104cff768ca400267e6554420006f77159521004fe76c8540006f45358420196df30d853204cfc7654f21006df43d8d10004ff7654420004fc76509104375c32d9532004fd72d8543015dc73551310057f754c540014dc73595422bdfb70595101dcfd764c92102edd3058630005dd731812104cfe76d894104ef4215842004dec725012002e7e50596100057f72545500067f65541300067c71d953204e7c62549504775c54d8d54024fe7558e2023cff715952104cdd73d9132004fd768c941004fe7648530006bf535902002e7f75596200047f7558d100079f6450d3015ebc42d915002cfc7650c201c67f5059541006bf71d9120006bd6450a3004ebd2159020004fd74d8131196dc4358f212cfae6290a40295de76d8d542e7b97090a40014fe7358720186be64d9121004fd73d895404eec624c940215dc735954202cfe764ca1000cfe7159020006dd70d8d52006be5359020215de7318142206de54d8d52004df735954004cfc769494002cfe768ca50004fd75d9120006dc72d8d54004ff73596100467f50d9510005f77448510166f62158650006df5358232004ff7655130024fc75d814101ebe6450650006df7358910004fd74d815100cfc715962004cfe72d95301575c53541300057d75c8530004ff7359620006fb6098151475df735954301cfc7458a300fe7c655953001cfe745953200df4714ca100067f75595321adbc745813141d7e76d95322efb5719094101dbe74c854002cfc705865204cfe72d8d402067c51596320f6be54d913008ef451d8520006f7715911002cfe70d91522e6bc21d9120466de52d8d520067c74594201667e31d95100867f51594200b6df3158e20004fe7654d2025e7d30d953200cfc71596320067f651813102e7c1059420005df735512025e7e73d953204e7f75597210067e51d9520006be61d912013edc5358e4004edf4258c2002ef47058420024fc7559210004ff764c65001cfc74d893017edf3058d21014fe73d95100067e51d954302cfe70d894302cfc7258720206df52d8d5204e7c21597210ff5f53d9530004ff7159232024ff765413000cfe71d8d10007eb7048520095dc735852001e7e645515228e7c61551504275e3219532024fc75586300257e7590950004ff725961004f6d75c8520005df7354941415ef72591320067c65981310067f6594910005df7354a4002cff70584200267c655494100dbe7690941014fc73594200267c65949300047f7558d2102cfc7690a1002e7f75596100067e54d95104067f50d85540075e51d8d5225e7f31d9532004fd7650a302cebe10d91201e6dc5458e420067f6590931004fd74d8d510067d7359721174ff7559540006df6318152004fc7654d10004fd72d8550214fd7650932004fe768c940
  | 25 => 0x522004ebe325902017dde73181210067c43d9510014fc73d8520005ef744852002ebf10590200067e70d953202ef7405842000cfe71d893004dec72503201e6bc64591323ce7e51d915101cfc74d8532004ff71595430047f7559132006bc74589101567d43596300067c6558931364ff7459131006dd7258e50035de73d9510014dc7359721016de634ca5002cfc7058e40006dd63504200077b705495009eee4258a401567f3259630004fd72d8154006bc53d9120014ff74d9543004fd72d813102ddc7650d3002cfc70591211ee7c51d9532005ef7259150005df7355132004ff764c64002cfe70d8d10004fc76509303875f7319531006bf745891002ede4058c20206dd72d8d5202e7d20596300b6ed32d893028fb4715514102cf476505100065e73d9510004fc76505300057f7558d42007af64c85203a67f32d9531006f67458420004fd7650f21004fc764c950376bf43d913109ebe7619120006dd72d8d544367f6518953006df4358f2000cfc765492101fbb6050940024ff7659541006fb7059120024fc75d8d100fd5c754c5300073f6455152004fd73d954102eee2058a400067f6554910014fc73d894004cff7690a104275c5218d52004fe764c9510067d7459721006bf644c120006f471595402cfac409092016edf3258e500fedd73d95300067d6555320014fc73d9121004fd70d89432b67f61195100fddc7550d30125dc735854001ebc6490a10326fa50d815104ede2158e4214f74615455000cfe71d91100067e72d951041f6c321953222edc7458e42106f6215863000cfe764c1100f6bc645913004ef82058232005ef725813102cfe7690a5025f5c43d9532006f96018154496de51d8d541cdde7390951024fc7558f210067e75d8542014fe73d9520294fd75d9543024fd73d895301cfe7458d20006bf74591200067e53d8154004fe7654d411bedc6358d411e6df43d91324a79f5418d544775d75d8d54006dd63544201567d32596301dcff7158d21376df30d91310067f40d95321c67e655042000cfe71d8142006f561506202a5fb705911001dbe7448540005df7355320416dc43d894304edf7358e4202cfe7694a10004ff7358252457cf5218d520067c73597210dcff705912002eef2059020004fc7650951006df735972002cfc7058650004fd7654a10206df50d8d521677810d9510006df5358d10014fc7358650006df53d8d21014fe73d891004cfc7654e420267c65541101cddc735895102cfc7059321004ff7558910195f771589310073d545494125e7d72d953202ede3058e50004df7358910004ff755842002cff7058e100067c655911002ef53058420024fe75d812102cfc76486500bebf425922000cfe7159132024fc75d9132006df53d8d4101cfe74d9510186bc64485200a57c754c920006d
  | 26 => 0x2cfc7058c201677641d951002cfc7058f2104cfc764c320014fc7359640024fe7558a1002cfe7058a10007af6250940004ff7648630014dc7359541005bf745952004dec724c32015ebe54d91500867f5359420004fc7654940006bf74591100edf4715893001cbc745891000cfc7159630015dc7355230046f55158650014fe76d8d4202cfc76544200067f74597211cedc43d8d5142edf6218d52267ac42d954202eee2058a20004ff7458720226f7105864202cff745902000ebe615054002cfe76d8143004fd74d8950286bc6454d2000cfe71d815302cfc7058e2002edf5058c201cede63d8d51004ff7558720004fd71d953204cfe72d9531014fd71d89313875e3119531005f5719493113ddc7354a404a75f5018d54006f56150650006df64d8d5215cfd7654140006de3158c20006be71590202f6dc53d81310cef710587201bddc735494104edc3258f21004ff7258e5002cfc7655210024fe7559321016de634c32004cfc725961026ef66150c20216df32d8d42004ff7459521006dd634ca504a75f5218d5402ef6105864004cfc765072000cfc71d8142026bc6555141246dc43d8d5204cfc765532104e7c725942006ef45158420024ff7654140004bf7458910014fc73d9130006dc631815204fac425093200cfe71d9150006ef628c940005df7355321005ef744872000cfc71d81540067e51596300fe7f54d95300067d655523202cfe768ca40006bd6450620016dc638c95112d7e75d8d4023e7c715972102ebe4059220016de6350e500257e75d855402cfe70d953101ebc6450720004bf7458a10004ff72586501c67e65d9541006f56150630004fd769494104cff764811002cfc7058a301febc415923204cfe7655320004fd76c8540346ef21d89410d6df3158f20006bd70d9120006dd7458c2009ebf40d91200067f655891002cfc7654e40006bd6454c20496dc52d8d5407fac4218142006bc315902004efb205832102cfe76c86500b6dc5358e2002cfc7650e20006de5458c204779f41d8d5402cfe70d8554016de6354c2000df4714c110006ef7258910004ff7458f20004fd7654620004fd72d9540205de7618d5209ebe64d9120004ff745942023e7e6154950006dc1058e4204eee6248640006df5158e42015de7348530004ff7650d514af5e5418d5401cbc7458a1019ebf40d854201cff76591310067f65d8132005ef724c12004edf5258c20006dc71d8d540067e51d8954005dd73181410067f7558f201567e53d8d500eef710d853000cfe764c92104cfc768c95104cfc72d8d2012e7f50d954001cfc7458c20004fd74d95310067f4059721004fd75d8940024fc75d913104eee769092004dec724c120004fe764c91004ede5258c2001e7e645515000eec6148520006bf7159020106df31d8d100b5dc735
  | 27 => 0xf105942028ef621d855402cfc7058a100057f754c520126dc6358d4025e7d31d953202ebc30590200057f754c720004ff7358a40006de31d8d4002cfe70d91101575c534c5500eef661d853002cfc7058e5200cfe715963204dec724c62004cfd70d8d2002cfc70d9510006f741d85500067f6555132004fe7650d1012e7f5259540005df744c9302eebf64507201667d71d9510006ef725952104e7e2059721005f571989542fcff7059130006ef6298953006f7614c55004cfc765432046eee52d895404cfc768c950014fe735891017edc6358d21005df735093232efa50d8153206dc54d8d52024fc7558c20006f5735842002cfe70d8d5200ef66150630005df7359521004fd71d913204edd5258c20004ff7358640204df735953218d7c7558121006f74158652004fd765063023ef46158552006df634c110024fd72d855228e7d75d855404eee6218931005ec7258141004ff73592100067d7159630006df73597210075c735515223e7f4159721006dc6398954004ff735932102ebc40592100667f5459610004ff76486401e5bc745813204e7e325942000cfc71d9150006fb705911015ebc645915002e7e705963004cfd74d95422cebf649894000ff360505101b57c7559131004ff71582320057d75c854002efa60181210fd7c755853023e7d3159721004fc765493102edd2058e5002e7f20596300eef46158530125de7398940006df7358d211cedc32d8d510067d655532100cfe76d85521c73c655514103ebc6459110005df7354942006dd634c5200067c65d9131004fd73d912001cfd71d954104edc3258e42014fe7358a4002cfe70d8d5104def745092004cfc764c720006dd634c64002d7c76545501ffac42d8d4200df671c8110024fc75d8940005ee72181412ef9d7390941006ef62989412e79d7390a4015f3f415515028ef46158554004fd75d8d20016de634c62001cfe7458e2036df7715913102cfd705842007ebc4159020024ff7654a2004cfe72d8d54134ff74591100acfe7618910004ff7058d2102cff71d891047e7c53d91531e6dd73d91320067f7558d2002ebf305902001cfe74d81510467c54d9510426df6518d52004fe76909310fe7c51d9530006df634c55002cff7158420004fd73d9542006dd6350e500067e51596421647e76195100067e53594200247c7558640185be74181211e6bf41d913220cfd76509210067e6419510106f6315863000df6719491038e7c71d95310fede5158e503a67d43d95310fe7c654c11002cfc764c920006bc51d912023ef651d855202cff71d95100067e64195310067f6550910005bf7458d10005ef724c32004e7d215942026ef661d8543016de634ca40024fe7558e400067d655512023e7c5159521004fd74d893100cff74d954104cfe72d8d41004fd71d9540
  | 28 => 0x895320ef621d8542004ff7458d202dfae20191201677b10d9510004ff7359520095dc73551202fdfb7059130006bf645512004edd32586324367e42d9532005df73581410067f755891004eac6450b20006dc7158e421b57e75989310257c754c650005bf7150940014fe76d8d5114df47158950005fb7054a2002ebf7459020006f5614c42004e7e4259721004ff7458a50004fd71d954304cfc7259250004fe7690950014ff764c120006f9601815102cfe76c86300067f70d95320067d73d9510006f4735842002cfe70d895300cfd73d91310247c7558d2102cfc705864022ede5358e4202eec2058a5004eec6290931466de72d8d520067c74d95100075f4319532006f74158420006df7458c20014fe735954000cfc71d8950004ff7654e100067d6554c2000cfc765411002cfc705953202ef54058420245de76d8d5202cfc764852011ef451d854002df6705051008cff7158910006f5545842001cfe76d91520a5f970989500067c315942001cfe745951036edf30d8543006be4359020014fe76d8d210a67e65d952004cfc7258e50024fe7558d1004cfd71d95211bedc30d8d412befa10d8151014fc735925002cec7648520325fb7058550004fd73d954000cfd75d8d51095f97098930004fd72d8553014ff764c1100057f755065002cfc725972001dbe7290a401167c525963000cfe76d8543006dd634c3200077b705455001cfc7458720196de63c8650004fd71d8d5402ede2058e50004fd73d895001ebe6450a501d7ac4250951076dc4358c2017edc30d8d210067d65c863000cfc71d911008fe461485202af762119510004fd768c910024fe755912109dbc7458d20006dd70d8d5400df47155121024fe7558e100067e75d8d400067c7359420004fd75d89300067c32d951002cfc7650620024fe7558a3001cfe76d91101f4ff7358d21004fd72d8151004fd73d855418e7c50d952101dbe72909410ecfd764c1101c57e751814100ed4614c5300057f754ca2000dbc715514134e7c51d895102cfe7058c20006de21d8d54004ff7650f2104eef609092001cfc74596100067f74d951004eec62481100067f6518931004fe765513104eee6250a5032edf53d8153024fd73d8553014fc73596201a67f50d85521e6df4359132005f7715915035cff7359131496dc50d8d54096df32d8d200047f7558d2001cfe74d812127ef661d85532f6fa30d8131006fb705891001cfd73d8943006ec32d891002cfe7690a30006bf7458d1002cfc705964000cbe769094104eee6218940014fe73596402075f50d8d520067e5159542006ec725954002edf2058e500067f41d9532004fe765512104edf32586322efac62909410247c755913202cfc7059531014fc735951000cfc7259721006dc61d8d540057f754c94038f5d73d953102e7
  | 29 => 0x9fac6490920176bf41d954023f7651d855202ede3058e4000cfe71d8d5204cfd70d952000cfe7158e42006dd7158e5004ef642584204275e5218d52006bd6450a20004fd769091002cfc7059642004fc7654540006dc735954100cfe7159542005f7714c110004fd70d915141f5f3119532245dc73585520ddfb705894001cfc74d8151014fc74d8d4002cfe7059250024fe75d8d2102cfe70d91320d5dc7355320014fe76d8d20024fe75d8d10004ff7458d10006ed6250a300067e5159250004ff7654d10006dd634c62012d7c755854043ebe42d8542004fd765523223d7e7155152006df6398154156dc6358d50004fc764c540004ff715963000cfc71d95400a4ff7559520004ff7654941006df1058e4203ebe64d91100067d655494002cfd74d854023e7d7159721024fe75d91300067e515972000cfc764c921005bd7418121004fe764c55002cfc7654e10014fe73d89400067e215963011cfd76501103a75e73d953104cfc725911004cec72591100067e7159630405f771591510067c41594200047f75589104675e52d8d5214cff715951003dbc74481102c77610d951004ef77158720004fd70d9521006be43593210267e65552321bede43d8d41006bf645012014df471591500667c5359610006df5358e42006dc5458c203c73e5355141024fd70d8d50024fe7558d200267c6555121024fe75d8543014fc73d812102e7f3059420004ff765042001cfe7458652014fe73d95410067c6558131004fd74d8d521667f51d9510004ff70596420067f6555130014fe73d8941006fb70595201467c53d915046def725915202e7c50596302a4ff705911026cff7159131004ff764c72001cfe74d815301cff765093202ebd1059020004fd75d893104ede3258e422975e53d8d5401cfe74d8951004fc76551102cebe20d91202c67c10d9510014fe73d895002cfe70d8910006bd65d912002cfc764ca2002cdc764c9304af5c5418d5421d7c7558d42484ff75595434375e32d95320fedc5258e50006df6418d520267e6554940006df634c92023ef661d855238e7f21d9531006df7058e42005ee7690920014fe73d9542014fe7359420006dd63c8650004fd71d8132006bd71d912017ede43d8d2104e7f52592522a6fa10d8141004fd70d8d51014dc7359521476df42d8d5404edd4258c20295de7398954004ff7159640004fd75d8d2101cfc7458d2109ebf41d912002e7f755963004eec62c8110014fc73d85501c67c655954104e7c5259642006be4159232245dc735815204dec7255020006bf644c5202bcff705951002cfc7058d2104cff7694a4002efa60181312967c53d8d5402e7e5059640004ff7654931004ff70586321b6df53d95311b67c52d95311fedd43d8d4201cfe74d85520057f7558d2102ef6205842001cfe74d
  | 30 => 0xc7558e42004ff705864200cfd73d953138e7e21d9531006de2158e501575e53d8d50004fd73d95200067e435942002e7c505962002cfc7059210005ef7259110266bf4059252006f77158d10006df7558c201457c754ca40004fd764865023ef621d855200cfc73d8530476de40d8d54476de54d8d54004ff7650950015de73d913231efa40d8154005ef7259540004ff7359252005ef72581540267e655523004cfd74d8d4204e7f5258252024fc7559220014fe7358a1022edc3158e42005dd744c93002cfd75d8d5002edc5058e501557e7354950014fe76d8d4002d7e705515012e7c655011002cfd72d852044def725954201eee64509201b67c50d9531004ff7359521004fd7654420006fb609815200ef4614c55002ef6305842001cfe74d8910004fd74d8553216bf43592320276f725495025e7c5358e520067f75595314575f5018d5202cfd71d9110004ff7158e4004edf7358e52496df52d8d540267c655511003ebf40d9110014dc7359520014fe73d855018e7f52d952125e7f32d95320067f7459420005f5719091001cfc75d915028e7e615515200cfc7158e5008fe7104852002cfe7694a30004ff715923000cfe715824202cfc7059543206df51d8d520067d74d9532004ff7650a50004ff7655230005f571c8110006fb609813204cfc765472004e7d52592520257c754c951186bf405912104ef4725842000cfe71595400057f7550e52006dd6354e4202cfe70d912102cfe70d95320857c754c4203ddf77159541014ff764c32002edf7358e500a67f52d9520024fc75d8d200067c425963002dec7650920004fd768ca10004ff725963002cfd7059610024fe755842004edc3258c20016de634c720006be4159020006ef6298931004ff725954102dbc7650540004fd7655130476dd41d8d5401cfe7458e52014fc73596100075f754c53001cfd72d8d4232dfb7058d50014de76d8d52006dc10d8d52006ed6250a100057f75585400067f4259630004fc7654d4102cfe7059020004fd72d95410075d73d9510005f77158152006fb6098154004fd7650620024fe7559132006ed621895337f77311953102e7c305942045eee52d895302dde704c53002cfc7059630014fe73d8540004ff75592301e6dd7458e420a6fa50582522967c635515213edf3258e40024fe76d9532024fc7558a40024fc75d814300774655051002cfd72d8d2002ebc405902004e7f32597210067f65d8d10215dc735494202edf3058a3000cfd72d912102ebe50590200057d75c8630005fb7050a2002cfc7058e42005df73581212975c5355130024fc75d8131024ff765953100cfc71d9530006ee21d893000cfc715923202ef410586202567d51d95212e6bc72d9120004ff7558242496dd51d8d54004ff735865000cfc7158c20024fe7558640
  | 31 => 0x8e4202df8704ca2004cfd73d9132014fd70d913002cfd75d8950366bf41d91310aeed21d891002cfc7058630006f77358420024fe75d8940006bc75d9120024fe75d91213867f611953100cfe76d853204cfe72d915014ef651d8550004fd74d815202cfc7650a300067e53d95102757c7558543004fd765513104cff71d95210467f53d95104af9f4118d5423e7e71597212367e6590a30004fd71d8950004fd72d911015e7f5459640004fd70d89540067f755951000ef76050510006bf32d9120006df638c951024fd71d8d5125d7e7619532004ff7359510024fe755832104cfc769093102cfc7650a10004f771595200067f73d9510005dd73485300067d6550f2102cfc705842002ede3058e200067d65506300067f42d953102e7e405963004e7d2059721005bf7458930004ff745953102e7d105942002d7c7655150004fd75d8543005ed71909202767c655954324ebc64591520a57c7558d20226f641586422367c659091000ef66150620004fd70d8931006bf6519120004ff7650e20005ec72591500f6dd4358e40004ff74582520cfe71048720185bc7458121006df5158c200057d75981320257f7254950004fe765052001cfe76d915004cfd74d854204e7c52597201557c73551500257c754c550014fe7359541004ff7159542004fd70d9532006bd72d9120006ed62c8640004fd71d8d40004fd72d8d1002edc1058c20016de6350e202967c6355150007db704c53024ebf42d9152006dd634c720024fe7558632004fe76485501def621d85324265f6518d5202ebc205902000cfe71d891001cfd75d815404ef732584202cfba7090a40496df50d8d5402cdc764c530006de7258e50004fd75d813145def7258d5204cfe72d911004cfe72586422cebc405824200cfe764811000cfe71d9130024fe7559130004fc764c91001cfe76d91320067d65546300a67f50d952022ebd43d91320075c754c930004fd70d854204fcc325493222edf3058e4200cfe71594202767f50d95433ccff745954102d7c70549501ed7c755813204ef8205824200cfc7159130006df73595423e67f54d9541006be631912004e7d3259721024fe75591100067f7558d21006ef6290931004fd71d815401cfc74d815301cfe7458720006de31d8d54005ef724c620106dd31d8d10254ff7559521024ff76543201b57c75581312e7b820d912002cfe70d91311cede53d8d51004fd70d9152006dd634ca4044cff7259542195dc7355321014fc73d89102cebe30d9120496de52d8d542667f54d954204ebe6250940004ff7559210006bc64d8520015dc73551320067c42d953104cfe7259632004ff755922020df6711814202cfc70d8520004ff70592520067f655913119df77158941005dd7398151006dc4258e50004fc7654d40016de634ca200067
  | 32 => 0x700c00e000001780c000203702f005c00800000180480323dd00381180be02100300481aa04000000000003100500008016005005803c05e000008028c04a005010805437400400000e000000008b004c08e00800200f402a01b00082e4006000010000007e01300004f00000430000000012005122003800000000197e0310022016801c000e060128030008002019001000000b0010010010008034800411e014041000400000e0d0800820808600980dc04400200180041a200000205a40a2013000801001c00300080580ca039000000c00603c00281f800400f003000400e039054804c00800100580240de002018002c000000001801400000f06400040ca00600000d412401b001000c27c004002006000016e0238050002007006800000c00000400040001480000068000011043010000c02900b802402c0f502a800400800e00a00a802e07a005804808e01b004802402402d007800007806200300101260220060104008000006000c00a099000807400e007013000c046000039000012e1f3059802005805a010003400c114001000400002400e001c00c0101528050002011009808c03200000000b000002604f818c00000014680640000010230434b8e007004014800002a010002800800000080242a0007067000400805100b003c00000a000000800411b026ab8005c00207206b000001604f833c00000400100000e601f0000010000a7d00180ac024008002000c086000011800443e01200300040ec01a000000006a000025002000e000045005800006e003804001a167016000401000007b803800600f004000401c06700c80880a600000a80040000090000000000242001003c0b801000000140a002f013000400000204e8018018003006807c006002000002c23e08d01200000160370020560008002005036c57e0d100181b400000201a004c02607a002801000012500486b002008407c8004022026000800c0de00001e01e8036002000001407c00801880001e200d001834c0000b300f015800002200c0024000034047004402205002900600060120080038004001000802018000e005801000400200102cc02800300280040040030000010024003009003040e0200000abc002083121047c00e009001000005c00000000283300860000000006003000000001200100b800c00400700000101600060cc00045ea023000806800e014006001002a00302b8278002029000000c006009005001405c004003801800001402a80108240100010000000001000000000801f00b802009a01109d021c01803204cfe725964202cfc76546301167f525963001cff7650120006bc63191200067e51596321667d21d951009cfd7650120007e4624851021e7c53d954201cfe74589104265f631953200cfd74d954122edc305
  | 33 => 0x201b000018c02a00900c800808600d002831c00603300380006f402e0308000016017002017003200100780048fa0020d904b80000ea003010c02b0fa019006800811e00680fc02e00501400000000000400000010000000010c00400d114800400801c022002000604600315f802a0470c0006402201202f80001cc08401180140160180be80dc00a0c3015001800401a005010c00201100a0004000004040801c0040010030078016002004000409200400000000e20010010060002024061802c00200310200003fa126000802813808d0000ed00100020028024080006003800008e032000816000009a000008000a068001001400600000180040000001fd006011e02900480000061f700280040ec278011006006000001b00040be02c0368170002000000000819600900680a8004004000800000600100580100100740008070002006001002403600102580740000d600a800c00203700080001a6097003800000200d00180040fa13300580080ce00601d80c857622100000a044800403500100880070020000084000000805c000091005026402801b043803000600b01f00bc01007b00600f0c3e027264020c01c00900e043c03c00400e00603b2008006013000400d001000800201f00980241bc01933280a477a198001805001a11800683f8024019051002010cbaf00e800000e0010000004008003002003c1444ff03881a40a80200008180bca05500002a0020006000005800012000082e400401900d000c000021019806400201c073000003619500003d404600b000018c0e4019105000022a003002804c00000002586cc3d800201a80680260370bc85ec0b800401500bc2600010000000002002008804801008700f000c04612c000000000203300000d836800a03a8030014003010802800000200201b401000205f8708012001000000002e003000000416800f01f01b801a0eb02a007400000f004000409c011000009807401b016806c028009018036803600900100000000020170010056000004000020a01b000822000a005016005415000000c014c000014002800001400f105800805800f011001400000001c801407a023000807c0020200030144000000018000403205301f80ac00202c011000800003e01b00003c400100000fc02200000000d400605f0018128176013000808000a001024802c00035700801a001000100183e800007d001800000400110883fc02a21000f800016a043009000403205900680e400001b00000a40081130418a8006400000c051401e00707802382f400600400540fa05501000bc0ce002015000019603c000002c078006000000c01c0560008010022004006800000a0080048bf400200100100dc01e000000013807413b00f01f400c009002001801801000180b80140080
  | 34 => 0x91801804a015038000003200f00280000ae00c1a580f802600500908cc03a0080048150000014004803000a00004a027818e00b01d024c01401c002000c00400b00481080e600d009000c024024017825c00a00000100081b8006081000800416000000543b200000a84f401001c002803800006d139804400a0000ac000c060000003800c01c020002810c0a600400800200bc00501a1da40e00050020010004006001801c01801900d8084016005001007c034000005804c16e003095803c06a015002805803c0dd01b009400200d0008044000016014001400013f0008054018001001800046200100a0080000006003806c024017006004c0040000000018020006005829003400200180bc00400c011800400001a000000001a000001810809e03100680a000000101b80945c600301f824000000700001581d0001046007014e0000c5003401a0010b4804000000d02680000040ae0138054004091006008409600000100c002200100e800001805900000f0202009007806806607008c000004800100205f400200200100740b2021005801805c000000800004202c096800001c00010a804400400e008854000009d00d800000c001018002c00006500482a40120000008088030003002800800a002000000004c06100380d802e006000002c016002010001002200e00700cc22a000006804801201604e808008a01c00280040040251268000022013007001400600304a00080000b00298000004007007807404a0f60328e0400002a000019400000004f00040080000de00b0052000000021809035303a845c0001210090038000038019001c04403f00007e00000040bd813803a022001801c02a01900200200000150000004000b3d00e0010008009000000000000d0cb010403a14000000c801801700301e800600a004809c086008002006800000700400e8050006001013000e09900680080200000008774006124009003419e000000021400002900a8020030000032004c0180b000a0058010000000003c03001603880ec01c01b012804002406a01706d400600200800800020040198278006005001005400000900080400002060090e1000804c041817c1ac024038001c0000050041320882feb001814c01c00200080ec078005003000800000003a000001a00200a000002c00500c01f80aa000000033800c012001804c06e13c000070800000000a00c401801e0aa002003c0b001b04d400a00a00a816c02c001000000c078002012006c01000e00e80000a403800381b400e01200a80003fa0000000018004040000806800c00d00d820802a00f005801c00802f01500207500000150178084000000800000200401701a80580ac010801400002f002802005e020000000c00400000900c409001905300040000190150048
  | 35 => 0x8009001c02000a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c85dd9310800159b04086c6aa002a760e515902050e2eba8c7302a851c7461dc554541198b8edb9aa4a810297a1474d8d520043f438cab1a20038f686dc5325040147d0bb9ac810003171cc65591100062fba8e6b2a820587c865d5415400193ec9b9aa8900028f61251596420063bba8e2b2a40058dc8758d31900018e8ebb8ac88824b1799773552320243e42ae3b2260058f48758551080051b906bb2a9901c71d1c653595400046f43821b1aa403aac8458a42840014bd063a6ca8800317dce53597210046fc1aebb028400a5d8504363548014bd0728eca900121fa17764c9103a52f418e9b2a6200c5c73595548400717d09bb2629007e97a167458e504962f3a0eab1c84038bc845d931880011bd0e082c7210163d21971949100063bba8e2b1a4000c9c74dcd62440018bce7396ca88213171c873597214fe6cb9ec1302a62cc7671d9652440b18e8edb2a82880121fa1f75591320046fc1aeca92200087e87195604c40755d0db2484900121fa1f75589100061fba4e8b2e4200a6e82103654c4011df0eb10c4a80021fe1576549100052ec18e5b2a20008de8708563940015ad02206c6a9003171cc65589100045ec26eca9a4000c3f749d1650800199ec7b92c0aa00a3720d76506204262eba8c7b0aa400a5d83984654c80159b0610ec49823b2719373551300062ebaea7b1a8400c5c7558d31080019cee5b8acaa00f2a7a127158e4238d2ec18e9b2a6200c3c75d916348001caca3b1ec2aa00297a141058e4201c5e422eca9a4000a5f835d165c85098b8ec39aa4a8232b3a0840d8d5202c7a43ac2a0840058dc8758d31080018bae139eca8800317dd4735952125d2f418e3b2a6400c5d83dd561880010fb0bb8ac81000a37a1f73595213a62e39ecaa926200c5f65dcd54441078b8e632ec29900237e0d765502001c6f43ec6a1aa400c5f65dcd524c801b1884b98c0a100317dc273d95100043f43ecab026200e1c6455363548014bf0ab8ac72100297a167058e420062ebaea7b1a8200c77751c565500018bee729acb10002976144258e5002c7a40eec9884000a3e84043654c8018b8ebb8ac72100317e1d73d95103a62f3b4a3b1aa809acc825c563908090fd0b3b262900023ee1d60181210046f43ec6b0aa874c5e73d96424c4051bd07ba2c52800a3720d75d85400062e3aac698c40059ac8750940c80018e8cbb8ac09900eaba13625093100666318e4b1a20058ec8758921940018e8ebb8ac4880aa9720d65543200047dc3ac030264008bf845d942440010fd0e206ca9900a3720d7654a104262e3b0ea992620087e87109658c0014bb06206ca99183179d4631815400c5f43ec8a0a4000cd473dc565500135cd0521ac210003171cf655512138e3a30eea98aa000c3c741956244001878ebb226490002976167458e50
  | 1 => 0x906ba6c4a8002b5e0d545842000c6f43ec698aa000a7685d0d610800b0f90eb2aa3180032b1d362481100243f43eeab1e40008bd8799464480090fd0fbaac3100031760f7558d1037e2f38ce7b2a208ea5d851c763551098bae632ec899253271d873551414954ec26e1b1aa800cac429d942540ad0fd0db8aa4a80031720d75d8d400061fb2ee8902201fc5c7558d32940011df0eb10c4a08021fe1571d89300053ac0ca7b2a4209cac7650940c80011bf06bb286880269b20965549402cc5fc22eca142000c3d741d3654c53999ae7b14c4a1803271d373595200146e41ae9b12a292c5e65dcd54c840153b0930ec6a90aa5720d75505500243e42ae3b1260008df835d9544800717d0fba2c508026aba0b64509202ce5c386c8a124000c5f65dcd544c0131d904bb4849880675a0773549310061e32ee8b02620487e85dcd64081258b8cbb9aa898826b32097158c200061fba8e8b1a4000a5d858c763550018bd0e3aac7210031bdd472591104752ec2ee5b1aa81f95e85dcd404c0010ff0abb4848800e2f21076505200062fbaea6b1c8000cd471d8d60548019cee438acaa00021fe1576551100055bc0acbb224000a3d84984654c8011bf06baec29000a2fa1f6450d202c43fc2aeca8c400487e85dd9424c40b1dd05bb28390002a7a0c611912000536c14c832a6209aae86d89425000199ee6392c6880023be0976509100052ec1ca2b2c6000c3d741d3654c8014bd0728aca101c795187754c5300045fc22ec9942000a5d839c5658c0014bb07ba6ca880033518d71989540047bc0aeca1a40008bf845cb6154001878cbba2c48800237a1f63581540072b28ec7b0aa4058f487585419400147d0910eca991c69da0440d953104d3741080b2e420087f855d9534840b3690ea0a8088016ea20142501200052ec2e83b1aa4058dc8758d43080090fd0bb9ac1908030f5977454a400043fc2ae7b224271a5d831c3654c4014bd0b3a2c6100aa97a0f655411025e2e39ecaaa26400a5d8310165c85198baebb1ec2a9003171d57158e4201c5f426eca9a40058dc8758d3284001ab6ea38264980038b1096550a300146e41aeca948000a5d85d0d630800195cec326429024a97a1471d8d540243f43eeab0c8051a748159554480019a8e231ac0a90121f215764c9100054ec24c231aa400a5c835d165080010ff0abb2869023aa7a1071d8d544952f42821b1aa884c5c721d5639081355904b228508002a76122158e500043fc3acb90c6000c9f74d8d6054807968ed21282880031d1d77158d2023d3b40880b2e4259cac76d9121480011bf06bb2a8880023761b73550200046ec1ceca9280038be87dd165480018e8e3b2ac09900317dce73d95100054ec26a7b1a8400a5d83953654c40717d0fba2c69000a3720d75d812100666b9ec53128004
  | 2 => 0x165551200052fc1ae8b2840098ec825d95444001878ebba2c6900038d19365505100043f43e87b2a200087e87195644c4090fd0fbaac88800a37a1f73595420061fba4a8b2e4200a758198c654400159d05308c6aa0028f612215963000666318e4b02a8008bd8788764480b14f70ab00c0a88161f21d65550200062e39ecaa928201ad48158d319000187aebb2484a80029761743d8d5000ceb40ee6aa26200a7581993654c80b1b907bb263280031b19772591100046fc1aeca0c4000c5f759d563908014bb073a2cb9080a3720d76509100061fba8c8b1a40008dd8708763550018becbb9aa4988063721973949310062f438e6b2e4200ccc73dc9655000147b0bb9ac8100162f21d64550200063a32ae32122000c5d749cf654400b5c90c90a4088002ab60a63191200062f31eea90ca000a9e840436354801958843b284a80034b10b7558d4204c3e43acaa928000a5d83945658c8071dd0fb12849880297a0e745972100536c2e85b12a0059ac87509404800755908b1285180021f61c10d95324752ec28e5b1aa800c5c75dcd62440014ed03326ca9900237e0d75d85424de36baec5312a209a6c825d165080010fb0bb9ac91027b0fdd774595430146f41ceca92820487c855cf64484011f700bb2a89087e57215744c53002c5e432e890a802a95c835d721540090f90abb2652000317dd773589100243e42aed19220028dc835d954440071bd0fb1a86908030f5d754d91200047bc0aecaa240008bf845d9434412b8baea31ec2aa0032bdd07258d1037caf43eea98a6000c3d74953654c8094790caa2a4a080317d9773551312b43f436e2aa2a000ccf731c964440011bb073b2a4a08030fdd564506500054f42443b1aa400c5c7359554080070fd0fb2aa8980167c20174485100046ec1cecaa24274a75811cb654c4090f90ab8ec4a0003171cd65553210043ec3e86b284000a6d82103654c83f4bd0ba0ac72800317597735523000c7a40aed192a0008dd839d953440011df04bb2a8880032dd937158d2000c7a40aeca1a4000c9c741cd62440018b8eab1a652000327dd0635815200667b98e4b2a800087f855d931c800196ee838aca900023de05765522004e56392c8a0640038bc845da524c0090f90a3b264a8002b920562189300054fc1aca3224000c3c75dd16344001c6ea92a2c2100030fdd77458d100052f41ce0b2e420987e8794d65c840193ac9b9aa8100269b20974597210064fba6e6b122047a76819d165c84018bd07baac3200263721d6354e420061e3a6cab1a2000c5f75d4d6308001878e9b2ac0990023be1d621895302d5643284a02400487c855d942440e38ecc3baa62100030f197745813200477c3ac43126200caf74dc963440010fd0e216ca881d31718f754c5500146f43ee6b2a400087d85dd942440051b
  | 3 => 0x1b2a626fc5e7518f61548031e902bb265200021f61c40597210062e39ee0b2e4200c9c64dcd614800195ac9b9262100261fa1f65549100045f438c8b0a400587e8794d65840011bb073b2a8881c3171d8654c9310062eb98e7b2a20008f7815d9524400717908b96c2a8003651c473551410062ebaec7192a000c3c64dd532480010fd0fa1acb9080317dd473589100065a3a0e2b1a4000a9d84d4d63900018b8e6b2aa5100029da1741584200051e42ae3b224000c3d74953654c50d0ff0abb2a79000317a0f7558d1000656b26e4a084000a9d8414563080010fb0bbb284989631d1db65485104362ec1eeab1c8400ce77258541080051bd07baac3200032b19072591500062eb9ca7b2a4200c3c65dd163440010fd0e32ac299002a761010d8d540043ec2ee6b204094c5c741d563909258b8eba1ac7900269ba0a43594200043fc2ae7b028200cac641c964440018beea39aca901d3171ce51595420062f3b2e7b2a200587c8759551080018bce7b28c488003561d7704c9301e64e326e8992600487e85dcd64840014db04202cb908162fa1f54590200062fb9ce6b284000a5d83947654c8131d904bb286880023ee1d601815104d37414e0b2e4200cad74d8a624c51f4bd0a320c6a900a3720d7655121006363a8e4b222000cac421d942440015cf04aa2c2100029ba0a64d95310061e3a8e8b122000c5c53dd931540090fd0b3b2648800327dd0735891000c3f436ea992a200c5d65dcd548c8010fb0bb8ac919002976167158e4200656b26e4aa04000c5e755c36355001ca8c3288c6a900237a1f63585520064e3a6c6b02a48ea9e84043635500159d04086c6aa003171d57058e420062e3aec6992828ec9e64dcd540803f8b8eab1a63280163d21971909100047bc0aecaa22000a5f855c5630810dc5885b2a84990028fa10715963002c3e432eaa12a0018f687dc565500070f90ab9ec8a80030fdd4745891000477c3ac4312a200c5e655ce428c08f8e8c3b8aa4a80021f61f4159420154af43ee6a92a0028dc835d954840018b8cbb9ac88821b171db754c93002dd840282a022000a6d82103654c40155908b10c4a80121fa1f7558d200143f43ecaa9a20058bc8759141940018becab9ca4980029760c40d95314d61fbaee8b2a8200a3f855c764480131bd0db9aa8991d3171cf6555131004b6c16eaa1ca400c5c73d955250801878ebb2262901bf171c473597210146f41cecaa24000a758194d658400b0f90bbb2a3180121f21571d91320062ebaea7b1a4000a5c854cb604c4018eae328ecaa1a831e5d760981532946e436e6b02a800a9d83184644800159b04206c6a90261f21d6554f210146f43ee6b2a80038bc845d952840b396ec8b88c0a110297a1410d8d5201c3f43ecaaa26200c5c535cf64540131790eb22a91900e8f21
  | 4 => 0x58c0010ff0abb2a8989031719773549320fcae42ae690a600487f875d76350013958c4ba464a00023de05764c91051e2fba8c6b12a800ab48159464480051b906bb2a3900030f195749893100477c12ecaa420048be87d91544c0e34bb07b86ca98802a7e0d65d91201e64e322e7212608c8df835d953c80014eb032a2cb9080327dd073595200065bba6e2b1a4000ae58290d610800153b0638ec89000317a0f7558e420061e3aee8b1220058f8805d9544840187eebba2c4880163721d6350e200243f42ee6b244000c9c7418d605480b1b907bb2621000317a0f75586200243e42aec98c402cc7471d95504400117f0eb28c8900029d60440d9532006563a0e4b1a20008ef825d9544810d4bb07ba6ca99212972195418d520066639ee4b222000aad829cd64080090fd0abb643180030f1d47458d100052ec1ca2b284000d8c42dcd65508051b906bb642a80163b21d6250a1001c3e42ae3b22a000cd7635c662550018deca392c688002976174158c2001c5f43ee8b1a2000a5e859c5639080b1d90cba242900269ba0830597210043ec2cec9922000ccd73d8a424c4014eb032a6ca988028f61071594204ad8f424a231aa800a5d85d0d6394001d48c232242901621f21b7558910006363aec49928084c5e731cb654c40187ae92a6ca88003171cf64549500062f32ee6a0c6009ce47258531080018becbb9aa89900335dcf71595200043ec3e86b2e42018bd849da52504b31790dba2c29012f1798f754ca500052f41ce2b284000e1f5394f64480019c8c2392c29828b17dd463585540062e3aec69928000c5d7394f654800187eea3a2c6880121fa177650d102b63a3b0caa0a2000a5e831cf6544001878e832ac098a4b1719773551100065a3a0e2b2a401fc5e7558f21940014bb0a206c6a900237e0d7654d211b4ae42ae72126209cac7259131080bb958c5b9282a000297e157158e500062fbaea6b1c20008df835d760484010fb0e216ca880030f193754c52000716216caa1262058dc865d1314c00117f08bb2a68800317d95739091000566c1020b1c84028f687d8531541098beec3aa64980031bd977258d100062fb2ae63122000a9e8318764480018b8ebb1a6490a0f179db43d95320062fbaac69884086a5d831c7654c8011bf06bb2a3900023ee017650d21006563a6e4b1a2000acd8298463550018beea39ac8880161f21975485500054ec1eebb2240008de87d8d60548014bb0ba1ec6a8a336310b73549420043ec2cec992828c8df835d953c840187ae83a6ca881d3179cf65949314652ec2ee3b1aa400a5e83dcb654400717908bb2a48800237a1e5158e424262fb98eab1e40008bf845d95244001938c9b9aa4900121fa1773593212952e41acaaa24000c5c751cd624400b5690ca0a808800339dc9614c4200062f39ae
  | 5 => 0x1c71d9c765949310043f43ecab1a200487c855da42441098beec3aa6498802976167058e420052f41ee9b2a200987c859db21540010fd0fb2ac0990031b19472581310043fc2ae3b224000c3f749d1658c00155908b10c4880028f61271d95320046ec1eeab0c4000a7581103654c4011bf0eb20c6a90022fa1f64585200052ec2e86b1ca46fc5e7518f61550018bacbb9aa9908121f214764c5500052ec2cc231aa400c5f75d8d31540b355b0438ec890002a761221d8d520146e41aec90c8009aac8259142940010fd0e32ac488176ab2096550540006aa38eea99262028de87dcd65c80010ff0ab9ec0a100237e0d74d89100056ac0881b1aa40087f855d942440552b906baa42a80262fa1e43593212c43fc2aeca8c8000ab6841d561080014eb0ba1ac210026aba0a73590200063a388cab026400c5e73d9642440010ff0ab8ec8980023ee1d601814102c6e432e89926000c3c65dd1204400199ae6b1485180023de05768c9500051f424c3b2a6400a6d82043654c80193ce7b248488257171d873551500061f3a0cb312620487e859d932504018bacbb9aa81000353dcc72551520062f31aeb90ca000c5c7558d319000153b0630ec8900031719573909310052e42ae2b1840008fb87580604c401c38c9a18ca990023ee1d60181520062e39acaaa440008bf845d931880010ff0ab8ec89900297a1b73551520243f42cec9928000c6c65dc9604c40b3d100ba2429000eab2116250a500046fc1aecaa4400587c8759552840e34ed023a6ca988021f6177650d100062fbaceab18400087d87d05658c0e98bcc7baa63280029d61741586520053ac2ce8b084009ce4625c662550014bb0a086c6aa0023761d6390a50006aa3aee29926200ce7721c563480018deca392c8880030f1d5644c4204764f326e6aa4640087d85dd94254413958c4ba4c4988029b60a64d953100657ba0e4b2a8000cd4731c565480019ace231cc4aa0021fe1576506200052ec2ce8b1840018f4815d952900090f90abb28310002a761353d8d410064e398c8b0a4000c5e85dcd65500011df0eb10c4981d29d60474d95310043ec2ee6b24200087d859d953500090f90ab8ec4a1a3a37e0d75d81430043ec2cec98a401fa5e8510963940019aee338ec6aa0029760c74d95104652e432a9b1aa4008df835d9529000b1b90eb1a87280021f61b754c420154af43ee6aa2a000c5e65dcd218c0018bee839acb908021f61f41d95320046fc1aebb0a8071a5d831cb654c40153d0828ac6100032d1c46458d2002c7643ac4a14a000a3d84887654c80195ee8392c8880063d20576552202e656396c8a024000c5c63dc154548134dd0521acb90806b5205634c52002c7a432e890a2092c9c76dcd54504018e8eab0a62100030fd9774581310043ec3885b2a6200a5d830856
  | 6 => 0x45ec26ec98a4098c5f73195644c4010ff0abb265200033518f71581540061fbaec898a40008be8719163480010fd0fb2ac4880022fe117650d203a53ac0ee1b2a62058dc8758d53080018beebb9ac8880031bdd47258d100054fc22e0b1c84008de8718d60550090f90abb484980029d60653d954104d72412a8b0840028df875cf654407953908b1a64880031d1d47158d200062e3aac69942000c5c75dc163908018d8ea392c688026b920974584200046fc1aed90aa00087f855d953440090fd0fbaac688002b360a61d8d540046ec1cecaa24000e1f43d97644c8011bb07baac12107e57215739093001c7b436e2a928200cd7731c565500010ff0abb4849800237e0d76553200061e3a0cab0264008be87145640800187eebaa2c8100021fe157650d100064fb26e6a9240028de839d952440131d904bb464a0026ab209715902004c6e43ac699220008de8794563080010fd0e32ac88800237a1c63589540065bba6e2b2a4000c7765dc5604c80117f08bb4a49823aa7a1221d8d5400477c12ec9922000a5f855c163908051b906bb2a9908021fe1573d812100637baee4b1a200087d85dcd60c85338beebb9aca98a1b171db754c9310061fba4a8b2c60008df835d954840011df04bb2a6880028f21573d91200062eb98e6b2e4200ce4721c565500018deebb92c8880023be097650d102ce5a886e8b142000c3f75d91324811d4bb0a386c6aa002972157058e420064fb26e6b0a4000acc8358862441098beea39acb900162fa1e435902023d3a40acaa9280008dd879906354801998e6392caa0257171d873551520062e39ecaa9220018be86dd132504019acc3b9aa8100021fa1b754c9103a62e39ca2b2e400487c855cf605040153b0938ac7210021f21d654c4200043fc2ae7b222000c6c75dc963440019cec4b8cc4aa0030f1d464585200066bb9ee2b2a80008de8718d605480195885b92c32000637a1b73551313c68e39aa8a92820487c855c764480051b906baec290026b920973584200062e3a8e6b222000c9c73d9152480014bb0728ecaa18021fa1f41596300072ba9ca6b08400087e87d07654c8019aec7b8ac0a90031d19771501100055ac20eab084000c5d655ce428c11d8baebb1ec2aa0030fdd464585200052fc2ae4b1ca000acd8204363548010fd0e206ca98a3297a1c73597210063bbaee2b1a4000e1f5394d64080019a8c7b8ac0a90028f61071596300043f438cab12620087e87d0d650800199ec6392c0aa0272b1c964550200062fb9ce6b2e42018dc8758d31c80010fb0eb2e431800637a1b73549310053ac0880b2e42008fb875806054c018b8a7b9ac9290121fa1f75591310061e3a0cab1a200487c855d9434400187eebb22c69024b1799773550200047bc0aec9948000a5d83990654c80717d09bb2a29
  | 7 => 0x5c655cc62440011bb0f28ac72100a3720d74d8910294af43ca231aa809cac7259141080011bf06ba6c4a88021fe1576551320051ec24a3b2a8086a5e871d563908090fd0bb8ac9180162f21d64506300063a32ee29022084c5c761d5324c0018b8e7b2ac48800eaba1b6450920006563a6e4b2a4097c5f73195624c4018bf06baec6a021b1b1ca53595400064e39ec8b0a4000c3f759d564080018b8e6b2aa5200162f21d6450a100052ec1ee5b2a2000a3e849c7654c801968e3b22c6900261f21d65552320062e3aac6994400487c855d943484014ef0ab9ac210003171cf655911002c5e426eca084052a5c8359554c800b1b90eb1a6310002ad20565d91200054f424c3b1aa400ccf73dc965500010fb0bb9ac9908031798f75506501e54f42020b1c84018f4815d9544c0011bf0cb9c8528002a720d65191200046fc1aecaa24200c3c751d1634800b1e90cb8c64880ab179cd6590a300064fba0e6b222084c5e721d563908131dd0fb92c888002976174158e500046fc1aeca9a400087e87d95624c40153b08082c72101637a1f5358c200052ec1ce0b2e42008fb875806050c014b906b82cb908028fa10715942001d56422c4a142000cae76d9242480010fd0e202cb9081637a1f5358e203a62e38ce7b2a2000a3f855cf644800717908b96c298003179cc65189102b63a3b0ca90a200587e8794d658800b1b90cb9a42980029d60664195320046f43ec6b12a874c5e63dd5310800b1e90eb0a83100121fe1d75d854204c3f43ca8b2e42008bf845d953480011bd0e086c6aa0028fa17715902002c6f43ea6b1c20008bd8714764480018baeba9ec6908021f617764c91004d67410a0b1c8400a76859d1610811d63d0928ec6aa003175d753d8d4000477c12ec98c8000ccf73dc96444001878e9b2ac4880161f21d655521004e563b284a024000c5d7558f21940e30ff0ab9ec8a880335dcc7158d2000566c1843b128000a9e84984635491d938e9a9ac68820f179cc651813200477c3ac4312209dc5f75dcd6550c012bd0fb2a649892e97a0c10d95320053b40cc832a6400c5f7394d65840019c8e5b8acaa0003171cd65549400243e42ae7b028400c9c741cd65480e18b8ec3aa62980062f61376507200062e29eecaa2600487c855d943c800117b0e28ac8100023be0976551300054f41ca3b224000c5f7558d31940010fb0bb8ac99012e97a0f65949100062e3aee6b226283c5e73197644c81359d04082c72101637a1f4358c200243f42ee2b2464028de87dcd65504131dd0fb92c68800297e0d725963000c7a40aeca9a4084c5e721cd65c840b1ed0db8a40880031b59772550200043ec2cec992800087d87103654c40159d0530ec6aa0022fe117654a100043fc2aec98c4040a5e85d0763548018becbb9aa4880263b20976551300
  | 8 => 0x63b2a4980029761743d8d52004aec3ca3b1aa8008df835d954c840b1f100bb286908032d1d371595200043f43aca988400087d87103654c8018bacbb9aa518002a76105158e420062fb9ca6b284000c3c75191634811959f06b10c4a9803355c47158e504762e3b6e6aa2a000a5d85990635486d4b90ab1a62900021f21f654c9100061fb2ee8b122000ce472dc563440051bd073b2a8908263da1b71551213872a308ea98a6000e1f5495163080018b8ebb9ac8881d3179c473597210146f41ceca928000c5f655ce524c41355904b22851800a37a0d7690a502952f41ecaaa220008df835d952840e94bd06206ca98802a7a0c71d9120006ac39ee0a92a000a9c835d5640800b1790eb22831000297a174358c204746fc1aebb0a8600ad581993635486d4b90ab1a6390003171d773591320066b38ec7312a88687c86dd5604c80117f08b96c298213179ce72d95310043fc2aeca1a421f95c855d1324c0054bd07b2aa6880021f616764c54025d2f41881b2a6400c3f75591310811d938c9b9aa8900aa5720d755095000733b28c490a200487c855cf64440018bae839acb9080e1fa1f655513202c7643ac490c800487e85dc564080018b90ab9eca880261f21d6555320006363aee4b2220058f487585418c00187ecbba2c0990023761e5158c200243e428eca9220008df8755163080011bf06ba6c4a80161f21d6554c200053bc0ae0b2e4200c3f65dd152509072bd0fbaa64988121f214764c91000536c1486b2e42059e48748520440018bae729ecaa08031b59772553210054f42442b1ca000a5d83043654c9098bcea396c6aa00e2f2117654d1000636328e4b1a2086c5d73d97644c8558b8e6b2aa51800a37a0e76551100046fc1aebb02820587e8794d65080090fd0fbaac6909031719773549310062fbaac6994a000a6d8290d65080018bb07baac32000317dd4735954200c6e43ac698a4000a5e8310165c84015ab03320c6a90032b19372541200061fb2ae9312620087e87195604c8010fd0fb2ac29900317dd75358e200043fc2aed2126200ccc63dc960550018b8a63b2a8989c7171db654c9310043fc2aeca9a4009ce472585410800187ecbba2a4a08031719573909100070fb22a831aa4098dc839da424c0018b8e7b2aa888003179da73d95100046ec1ee8b14a000c5f65dcd62440018bee729acaa000a37a1f73597210245f43ec8aa240008f7815d9544c0594ed023a6ca8821a9be1562189532052f42881b1aa400c3f75dd163480018d8cbb92c68800a3720f765502000cdb43c84a0a200087d85dc5648c0014bb0728eca982129721a5118d520051ec24c3b2a64028dc835d7605040b0f90eb2aa3200030fdd254594202ce5b886e8b142092c5c65dcd544c001938e7b22a8900121f21576486400061e3a6cab026200c
  | 9 => 0x76551320047dc3ac0302a80487e87dd5639080187ecbba2a0a001637a1b73551304b62eb98cb302628ea5d85dc7635510d0ff0abb2a72100335d8f71581540062fb9ca6b2c80018bc8759541500019a8e7b8aca9000e2fa1f745891002c7643ac4a146009aae8290d64c840117f08bb2a89000a3720d765502000c6e41aebb0a600087d85dc5628c0014bf06ba2cb180021f61c42596300043f43e82b284000c5c835d761508051b906baec0a10023760f75586400046ec3821b1aa800ad48355161080090f90abb484988021fa1c10d953202cdc402e890a8000ad68199063548015ad03326c6a90263b209765521002c3e43acaa8c4009ace829c1639080156f02b28c8900162f21d6450c204656741021b1aa48ec5c76dcd5454801938e6b22a81000e2f211764ca100062f398e5b2a20008ef8758862550054b906b2aa7908021fa1c65591324252f42ceab1c8484c5f761cd5254119998e5a9ac6880028f61010d953200637b28e4b026200c5f75d4d63440031b90cb9c8498816f820121481100fd2e42ac69864071c5c76dd5314c0e30f90dbaac0989d3179da51d8d520052ec2820b1c84008de87087635500117f08bb264880021fe1576486400243e42aec9942001ad48158d31880014db0a216c4a81676add070509200052e42ae2b1c8400a5f835c165c851d4bb0bb86c6aa0023de057654d200065a3a6e2b1a400587e87951658c0018daeab16432816f2b1d864485200046ec3881b1aa458a75811d3654400187ce9b2cc498983179d463181521552f41ce2b2c600587c8759554880014b906ba2cb90a323721b735815228e9a38aa8a928252a5c861cd54548018becbb9aa0980121fa17765091001c5e422ec9922058a75811cb654401359904b1a648800a37a0f75582420062f42ee6b2e4209aac825d5640800159b04282c7210aa97a0c215963001c9e43aa8a928200c5f655ce424c4010ff0abb2879000237a1c40d8d5201c3f43ecaaa220058bc8759141080b3958edb2284900030f5d475d91200062e39ecaa924200c5c735c165c84090f90ab9ec8900031bd97725813104d57416c8a126200c3f75d91614800b1b90eb1a8708002b560f75584202062f32ee6a94600487c855d943480010ff0abb2621000317dd273d95104352ec18e1b2a64008de8718d61549194bb0a3a6c6a90023761c1058e424962e32ee6aa26400a7585d0561080018d8ca392c8880121f215764c7200243e42ae7b024200e546194463550014eb033a2cb909c69760f74d953100696212ea3028484c5e759cb63551198bb0bb9acb908163b21d624863004c3e43acaaa642008df835d93244001878ebb22c290002a7a0e51590203a43fc2ae3b12a6028dc835d952440011db0db9282100029b60830597210043fc2ae3b128600c777558531080051b9
  | 10 => 0xa122000a7681103654c801968c9b8ac6900029d60654d951000c7a40aecaa24084a5c86d0c654c8131d904bb2a688003561d7704c53001c3f43ecaaa24200ccc731c964440051b906baec2a10029721532d85304252f41ce6b2e4200c5d7394f65508a58bcecaa6c6a91bf179cc65181310046fc1aec90c80008be871476448001b4884b88c0a10163d21d614c4200062eb9ca7b2a20028dc831d9544c10d4dd04206ca990062f21172d85400043f43ecab22208ca5d851c363548014bb0f39eca880121fa16764c5404954ec20e5b1aa800ccc73dc962440010fd0fb2a64880161fa1e54594200045ec26eca8a4040c5c65dcd52440010ff0abb26320002a720d65d91200146f41eeab0840028dc835d954480131d904bb2a8100273318973989400146e41aecaa440018f687dc565480978b8e7b2aa4990030f993754c420006ac39ee0aa2a0018ec825d954c841355d0520ac91900335dc671d8d5241caf43eea9926000a9f835d5640800199ac7b92621024a37e0d74d89530045f43ec8b1a4000a7585d0761540090fd0bb8ac99021a9ba0810d95324954ec20e3b1aa800a5d839c565080018b8e7b2aa49000237a1c635855400746212c6a14a00487c855d931900011f70eb00c0a100e1f21d65551200243f42ee2b1460008dc8755163080014bd06396ca8800317e0d75d85420062fb2ee6b222005ae486487204400193ee9b9aca90006b5205634c6500146f43ee6b122000a5e85d0563080010fd0e216ca9880317dd75358e4200537414c832a620087e87d95644c40317d0dba2a4a09c61fe1573d815102c3e42eeca8840028de83dd561880011df0eb10c4a0003351cc71595400054ec1ca3b224000a9d8488763550018b8cbb9ac4880038b10b65509100046ec3821b1aa400a3e84885658c0b717d0db9282a000a37a0f75586420065bba0e2b1a40008dd839d952440131e90cb8ca4988021fe1573d91200053a42ae6b0840008dd87085639400147d09308ca990031719773509320061e3a6ca9022000ad683dd561080051bd0fb9ac8880023760f75586420054ec2021b1aa40087f855c762500010fb0fa1eca880f2a7a105158e4200637b2ee4b222000c5c75dcd63484010fd0fb2ac899003351c76358154384ae438ca9926200e4f65189324c401938e9b9ac6880ab171cd655523023e3a30aeb90aa071a5d83dcb654c4010ff0abb2648800237e0d76551300062e3aec699240058dc8758d3194001958e9b92c48802637a1f4358f200047bc0aeca948052a5c8359554c84019a8e231ac0aa00237e1d6390a500046fc1aecaa26292c5e65dcd548c0e90ff0ab8ec8a9803171cd6554a100062e3aac699220028ee87d8932500011bb07baac2100023be1d62189430066a39ee2b12200087f855da32440035ad0db0a629800237e0d
  | 11 => 0x96098200300180045903f0120340c84600605841802194010870080660005e826022980f802000c7a42b81200401c09031096048728060000002c8090822342f01301003c0200000c02c0280001a00000002018145e70100320180e0010340802b80007a104000040000c0000150340380000d0020202480003a06013805044058000000081150380b0302f42000300404c0780e0881b00080702400c150080840900581500c0794080100001c040500dc024001042580980901e0000680203106605c298c702a004030790100441c8020000880a883032000198040d004001800002818060000320a00007700204c0184302c040248390020000502001e0480500406e0a40180c0000080580210c1040c802000014400001f00101929202a018008000080e0030090800140180100a45495013008060058004340080083917e0f00282e012034078750000140f0001640002a86c008094058230240000881d0200981500a0140000180c00c024011ba0220640704a0000a40002900006c020360080580000400006c00000026008048170000003500601c0280180101601c0001e1920000180e00600c060000360000b0190000440321d270054030021c80040980302a02c0001a0060fc0200a17e0140226200201415011004025dc010058004008011200ac158011400040000800a0080501200000c048e00160000385e0060002200101c0100c000004008000060160040500002201017013092024440000000781985101c010068041b8000040000000000a80005c00004002000034000140580fc0001735401c02c260741200781a05c02c2380404a0400504a0060602a00900c0005d82505e02c090250020180000a01e00c0b01303c1f8008010320400001b07004c2a0000801093f0010441540501900e6544b0090c2018020010080540580100208c3600b002028000290000080a02809e35806018004008058b82d201408000064048028098dc2481106e0000000001701c00c5c75dcd634800b0f90eb2aa9180032b1da42505200054f41eebb224009aae8290d64080131bd0fa1ac7908021fe15764ca100051ec2ee2b2040098ec825d931900010ff0cbae43180030fd977458d100066bb98e2b2a4084a5e8655063548031ed0fb8ac690172aba0871d912000696212ebb0a84008df835d942440031dd0db92a8908121f215764c42000656214ec
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc02c0c420c1000000000105f985cc735972100417a63655cc62440014a9901087650910006072107558d324400105f985cc73d9510426132087558d32440015899010973181420061520473595525010944e97d94624c93142513a5b731c9545490984c821cd655494042513249741cd65c850984c821d57158e4200568640425c4605080105e98d957390910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x124c
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0x8a
  | 14 => 0x8c
  | 15 => 0x8d
  | 16 => 0x8e
  | 17 => 0x98a
  | 18 => 0x98c
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x128a
  | 22 => 0x128c
  | 23 => 0x128d
  | 24 => 0x128e
  | 25 => 0x150a
  | 26 => 0x150c
  | 27 => 0x150d
  | 28 => 0x150e
  | 29 => 0x9ca
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12ca
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xa0a
  | 36 => 0xa0c
  | 37 => 0xa0e
  | 38 => 0x130a
  | 39 => 0x130c
  | 40 => 0x130e
  | 41 => 0xa4a
  | 42 => 0xa4c
  | 43 => 0xa4d
  | 44 => 0x134a
  | 45 => 0x134c
  | 46 => 0x134d
  | 47 => 0xb0c
  | 48 => 0xb0d
  | 49 => 0xb0e
  | 50 => 0x154c
  | 51 => 0x154d
  | 52 => 0x154e
  | 53 => 0xb4d
  | 54 => 0xb4e
  | 55 => 0xb8c
  | 56 => 0xb8e
  | 57 => 0xbcc
  | 58 => 0xbcd
  | 59 => 0xcca
  | 60 => 0xccd
  | 61 => 0xcce
  | 62 => 0x15ca
  | 63 => 0x15cd
  | 64 => 0x15ce
  | 65 => 0xd0a
  | 66 => 0xd0c
  | 67 => 0xd0e
  | 68 => 0x160a
  | 69 => 0x160c
  | 70 => 0x160e
  | 71 => 0xd4a
  | 72 => 0xd4c
  | 73 => 0xd4d
  | 74 => 0x164a
  | 75 => 0x164c
  | 76 => 0x164d
  | 77 => 0xe8a
  | 78 => 0xe8e
  | 79 => 0xeca
  | 80 => 0xecd
  | 81 => 0x104a
  | 82 => 0x104c
  | 83 => 0x168a
  | 84 => 0x180a
  | 85 => 0x14a
  | 86 => 0x2c9
  | 87 => 0x198a
  | 88 => 0x14c9
  | 89 => 0x1609
  | 90 => 0x10b
  | 91 => 0x409
  | 92 => 0x130b
  | 93 => 0xb8b
  | 94 => 0x138c
  | 95 => 0x180c
  | 96 => 0x198c
  | 97 => 0x138d
  | 98 => 0x168d
  | 99 => 0x198d
  | 100 => 0x138e
  | 101 => 0x168e
  | 102 => 0x180e
  | 103 => 0x170a
  | 104 => 0x188a
  | 105 => 0x1a0a
  | 106 => 0x140c
  | 107 => 0x18ca
  | 108 => 0x178a
  | 109 => 0x184c
  | 110 => 0x148c
  | 111 => 0x2cc
  | 112 => 0x5ca
  | 113 => 0x17ca
  | 114 => 0x1a4a
  | 115 => 0x19cc
  | 116 => 0x14cc
  | 117 => 0x140d
  | 118 => 0x16cd
  | 119 => 0x144d
  | 120 => 0x104b94
  | 121 => 0x1a8a
  | 122 => 0x194a
  | 123 => 0x19cd
  | 124 => 0x14cd
  | 125 => 0x140e
  | 126 => 0x16ce
  | 127 => 0x144e
  | 128 => 0x184e
  | 129 => 0x148e
  | 130 => 0x188c
  | 131 => 0x44c
  | 132 => 0x5cb
  | 133 => 0x1a0c
  | 134 => 0x17cb
  | 135 => 0x184b
  | 136 => 0x170d
  | 137 => 0x1a0d
  | 138 => 0x3ce
  | 139 => 0x170e
  | 140 => 0x1a4b
  | 141 => 0x188e
  | 142 => 0x1a4d
  | 143 => 0x1a8c
  | 144 => 0x194c
  | 145 => 0x17cd
  | 146 => 0x18ce
  | 147 => 0x178e
  | 148 => 0x58e
  | 149 => 0x5cd
  | 150 => 0x5c9d2
  | 151 => 0x5d5d2
  | 152 => 0x5d8d2
  | 153 => 0x1a57d2
  | 154 => 0x1a9952
  | 155 => 0x1a0d52
  | 156 => 0x170cd5
  | 157 => 0x1a57d5
  | 158 => 0x1a9954
  | 159 => 0x1689d6
  | 160 => 0x198a54
  | 161 => 0x5ca55
  | 162 => 0x5d4d5
  | 163 => 0x5d655
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2219
  | 6 => 5475
  | 5 => 1547
  | 4 => 15
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
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/739+packedAt gbK7 (82103+(h % 739)*12) 12) % 2219)
  | 6 => 2*((h/1846+packedAt gbK6 (262800+(h % 1846)*13) 13) % 5475)
  | 5 => 2*((h/529+packedAt gbK5 (91273+(h % 529)*11) 11) % 1547)
  | 4 => 2*((h/19+packedAt gbK4 (1050+(h % 19)*4) 4) % 15)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff81e01ffe03fffffffffffc09e471e0e3fff
  | 1 => 0xc1ffe001e0ffc3e03c1ff01fc769b8e789d273
  | 2 => 0xfe1ffffe00fffc003fe0ffe03871c0f9f1e39c
  | 3 => 0x1fffffff0000003fff00003f81ff01fe03e0
  | 4 => 0x1fffffffffffffc00000003ffe0001fffc00
  | 5 => 0xffe0000000000000000000003ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x220020021000428882114890002030a0204a5
  | 1 => 0x41596028c86d4341151aa0568328986588d252
  | 2 => 0xb40aacca00b1a8022748cb409851c0b0b16318
  | 3 => 0x101cd76d7a050104bb9c81832d81ed01de03e0
  | 4 => 0x211719b19cde33970010020437fc00016db800
  | 5 => 0x398001c01018221802000c183eff76de000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40411
namespace PEqualNP.Outside.L_meta_40411
open PEqualNP.Outside.L_meta_40411.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 4 := bs0_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
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
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 134 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := bs3_5_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := bs4_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 26 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 134 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := bs5_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 15 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1547 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672))) (concat (concat (concat bgb_5_768 bgb_5_864) (concat bgb_5_960 bgb_5_1056)) (concat (concat bgb_5_1152 bgb_5_1248) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)))))
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
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5475 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)) (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 bgb_6_1248)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536)) (concat (concat bgb_6_1632 bgb_6_1728) (concat bgb_6_1824 bgb_6_1920))) (concat (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304)) (concat (concat bgb_6_2400 bgb_6_2496) (concat bgb_6_2592 bgb_6_2688))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976)) (concat (concat bgb_6_3072 bgb_6_3168) (concat bgb_6_3264 bgb_6_3360))) (concat (concat bgb_6_3456 (concat bgb_6_3552 bgb_6_3648)) (concat (concat bgb_6_3744 bgb_6_3840) (concat bgb_6_3936 bgb_6_4032)))) (concat (concat (concat bgb_6_4128 (concat bgb_6_4224 bgb_6_4320)) (concat (concat bgb_6_4416 bgb_6_4512) (concat bgb_6_4608 bgb_6_4704))) (concat (concat (concat bgb_6_4800 bgb_6_4896) (concat bgb_6_4992 bgb_6_5088)) (concat (concat bgb_6_5184 bgb_6_5280) (concat bgb_6_5376 bgb_6_5472))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2219 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat bgb_7_864 (concat bgb_7_960 bgb_7_1056)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344)) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632))) (concat (concat bgb_7_1728 (concat bgb_7_1824 bgb_7_1920)) (concat bgb_7_2016 (concat bgb_7_2112 bgb_7_2208)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8feeaeee8faeaa8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4209682600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40411.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[4,6]⟩,⟨.or,[0,1]⟩,⟨.and,[5,8]⟩,⟨.and,[2,8]⟩,⟨.and,[2,4]⟩,⟨.or,[3,10]⟩,⟨.or,[9,11]⟩,⟨.and,[12,13]⟩,⟨.and,[0,7]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209682600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209682600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40411

open PEqualNP.Outside.L_meta_40411 in
theorem PEqualNP.Outside.L_meta_40411 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209682600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209682600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
