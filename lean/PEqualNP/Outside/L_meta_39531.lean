import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_39531.Model
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


end PEqualNP.Outside.L_meta_39531.Model

namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
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

def SBf (j : Nat) : Nat := [8, 7, 6, 8, 8, 6].getD j 0

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

end PEqualNP.Outside.L_meta_39531

namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0xa3c50c005190000001210008a08024f003fc42fe41ff42fd41ff40ff43ff30fd10fc21fe21fc20fc31fe40fd30fe10fc30ff20fd20fc41fd32ff10ff31fc43fc10fd42ff41fd43fd40fc32fe42fe43fd21fd31fe30fe20fe32ff32fe31ff21fc40
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x8436d52cc77a84215f15131be2a44176510c2faa3996f90140bf294617f52506fca3187750f32df208817e52d06fca518fbc8421f6a9087f721486f8a4085b54830f7102417d53482fca621fe48110bf29a21f6310c6faa1215f15032be2a2417e540c2b8a6a05f94c20f610c417d548cbde8510dfd4f20f710a43df438c27aa998df94842be2a0636f52442fea4a1dfd5332bf29c873e54cc6dca598df94e40dfa1c837c50506fca410df55331bfa9a437d538cbb886187e50040bf290617d54c82faa6885f94e10ef988637e5310a7ca8197794f20be29c417e54cc6fea9105fd4543dfa04817e540cafaa0215f55132faa08837c53506fea0a15f94742bf28e65dd320c2fca1996f95032bf286837d53486fca3905f94020bf28421f641107b863187750d32bf298657a50087dea4885f94b43f6992417e54082faa71077cc830bf2a441bc544c2fea610fbd0821bfa92817d5310afaa120fd10421de2a243bd43d0b7e85a0df14520fb98a63ee520c2faa890dfd4542df20a837f52042bca6216f550329eaa0657c52443da84215f54343beaa0417e509077c83205f95043be282857f53502faa5885f54c41bf29c836f525067aa810fec8120bfaa6617d540cafca5985f95021beaa0217d53d02fca9185f94343bf2a0857e53882fca8995f55021fd10421bf41106faa9985f54232ee990657c52c437a8620fb8c832bfaa4437c54082fca3987794c42be292815d5310afca4086f50d40f7108413e54086faa3105754c21fa98e21fa10042dca4185f14e10ee98863df308c2fca890dfd4b10fda02817c54ccafaa3206fd0842bba8a85dd4310ebea6a0778c430bf286857d510cbf480206f90942bf2a4653c544c2fca320fb50a329e2a2437e5010bea6218df54041bfaa043dd32cc6fca1205f55110f7210857d50cc6fca318df55240be2a2617d51d0efaa118f78c130bfaa4637f524c7baa6215f14d21bf29083f621087d842106f50840beaa063f510042fea6885f54342bfaa643ed320caf8a890df94c31beaa4617e53c42fca220df95332fc206617d528c7788420dfd4f21be28a657e53c86fca3a05f94040bf2a021de324cbee8390db14910ef21887f75150afca0185fd4d20bf2a4437e538877aa9905fd5020be28a87f710843be65197b10a21bf28c657e51042faa5987e54021bea9e857e54c87da84995f55231bea88817e50882faa121dfd5132ef21a65de43ccbee4310dfd4f10bf29483ee428cbb862186f50f40afa9a21df430c2faa7a0f7d0e43bfa9c43ed20083d8a4885f55332bf2a421ef328cafca690dfd5210bfa9c21de53086fca610df94243bea9e21fb308c3be86a1efd0a42beaa241f8400c2faa4087d8c510dea1c833e54c83f681206f90841dfa0c837e51087ea4210df94f42f7196417f50506fea6105f95320
  | 1 => 0xd518cafaa1a0f7d4d10de21881ed52cc6faa3985fd5331fc880217c5050f7c86205f94232bfa9a83ef4250bb8a6a07e8c030bea9c637c544cafca020dfd4520be292637d53086fea8905fd4530bfaa0637d5210efaa910efd0d42dfaa261bf43d02faa5a07b94b31bea94817e51886fea7107e48020f690843fb10842fca5085f54f20bea9063df300c2faa9085f94321be2a421fb40cc2fca421df54321b6a9087f741506faa7187b4cb20df2a061ec525077aa998cf95030bf2a261f85050ef8a9185f94c30de21483bd425077aa8185f14943fba0c83ef324cafaa521df54430bea94617d52d0efaa110dfd4540df2a6633d54c83de41105f54642bf29481bd42903be64195f95120fba08437d52886fca7905fd4143bf2a463ef4290afca3105f14540ef18a637e510cafca620df94642be298417d5110beaa2186fd0e43bea9c435d53c82fca418df94010bf290417e5010efaa5105fd4132bf290657e510c6faa8985fd4930beaa2637e540c6fca321efd0c43ee98061ef20082f8a7887ed0030bea8c87f441c86fca5885f54a41bfa9821bf421027ea8985f94d20efa9a817c53c86bca610df15221bfaa261fb20882fca8885fd5010df2a641f7318c77ea890fd4c510be29283dc438c2fca1215d54430bfa82637e508c2fea090df14e21df21c817d53102f8a2985f95131fd98261df32cc6fca7a0f7cc631beaa6437f540c2fea9885f14542be2a641bc43902faa2105f14d10b7290877e51902faa488774ca30b6292837e541077c8520df55243bf284437e50cc7da6410ef10440bda8287df328c37a80205f14c21be2a6637e51102f8a5085f14c10bf28065f920842f2a010df15021bf29c857f548cafaa598de14143bea90837e528cbf620885f54720beaa0617d52842faa4205f54c209faa221bd4350af8a8185f54740beaa441bf54443d88410cf15110af29e417d500c7dc6510df54830bfaa221bf43d0afaa221df94031bea9c857c54c42fca521df547429eaa061f610442b8a6885f94743ba28a857d518c2fca010ef50b41bfaa641fb5050ef8a090dfd4910f729087de318c3ee20087754f20bf29663fa50086fca2187e4c030bea9c21ef52506fea890efd0941bea9c817d518427ea890dfd5230dfa14817e5290afea508774c931beaa6217e52102f8a0997b8c821fb288617c54442faa6085f15231dfa18837c54c86fca118f7cc931bea9e437e524437e86a05f14f20f790c437e53d02f8a9195f55242bea8065bf40103dc84996f55021ee29a21fa20082faa720df94443bfaa263ed32886f8a6907b54830bf28885f45150afaa021df94b40de2a2217d52d077a8621dfd4532bfa9a857c5350bdc43105f54332f7192417e54cc37a8220df15330df21a877c54042fea8195f94420fb18e21bc419037ca810df94c10eea9
  | 2 => 0x80c00c0229c6201c8b44c550000b05c4104800240000143401c020042d150070100506c01011030e02802000018214940005c030e0123501404001000040000000401000000c81f0900200103158740080006c051142f0000301d23028000280802866038a1098460140800c170500b11c084040b7940d008e603405000031d49e028000002200024014045cc092c40b018b5080070057d0700000002000210549c01d1f28cdc00405010a109808000000500200c7c0c07b04c0e020027e82000001010000342f0190c86c000080d02401010052e01f000020300a0040300c0a004031c45a008610d80e018040040c04000000095640200000000060082927821008030400847417019910012d1cc2f01428028050000b4205f03001440003240700000020000018800102be292617d50086f8a6a05f95040bf298817e54c42faa920df14131fd102217
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xb410863e64d4c21b618143cca7865481109b588540c66d6214c1097d95320ca6e6214c208f59053c866d6214e10d350d5210f4d53908428f990530823f6454d109e980520432d544c8218f990524c74d63149418f191534832f54d49109718d544831d544c832ae580411035853d0140d394932cc65d63150109d9845308354538c510d994a510c25f63551108fd954310f4c53d49109bd9520082b86050c439d594410867b65500409758e524425e6394820cb552320cb655254430c755332cc7355110440c7d53534433554544309b98a544426c62551319b988530427761551329e181534863e64951218f990540cb2c52d09419758e529026e6215330d398a530863e64951109b58a53442776550441ab588431023f6454d219b189534423e6414810c7952530863f6550441cd553410867a6015021d3d4f524423d6494d219e583548c6ac62504419b18951d0f2d548c821c714f43502b46448421cb152214865c6354221ae18143d026f62546309798e544431d54cc8328f59353086b46150b41e610c400c23d6595021ce952500874e6294f20c795253c827b6054d219ed81544ca3e6494a109718d54442cd6210c308f992534863e64150309798f54c433860550309dd9521086776154d20d694e500863c6454d10ab588439031c53901409e983548ca5f63549109758f54c823f64546309b58b548433454c85219b58b54cc66e62150318f99352842756115030cd952510c26d6294e41d914b415073954540219b58b540c25d6594c219e583548cb8d43509329d185534832e54948309b988540431c63550308f992534426e6294910cb95252cc6b86050d409ed81544c65e6394910ce552500863d6590c408f191524432d5454830cbd0d5210f4e524c8309798c530866d6510821ae18143d0a3e6414c109e580540863d6414c218fd95401023e6415021cb149425067960d50218f59053042e96008620cd185540875953540218f990534825f654c4318f596421071d53d08428fd9150ccb696014910ae181431075b43141439b98854cc63e6494f109b588540c26e6214e10cb55132c827b6055130d694d50086766114e20b61814310e7561d5030a758c4210674654c5109bd8951d0f3a54540219758f54c434d6214d409d58453882b46150941d654e500871d5454f20cdd0c5150a3f64544209798f540865d6315020b9586320872e5454b318f592528c25f63551309798c520423e65d0d409b98a534432d5494b319b98b54842ac644842197d95300c23e6515110da14a204426f654c8329bd8953442766115020d3988535023f6454d208f992528c23e64d4f208fd91524436652544308f592534426d62951109dd85544839b43d00309798e534432c54149108f191508867561d533297d954310e796510030b6583320c25e6314941
  | 1 => 0xd140000043010080002093a80002050001000000141201010506a040081000000981416003880c120c0000952100101416020380c0a00030112800010000c071a81c020106000020d000080200158280200c754d4210b2d5454b319b99452442746155132e9108410871d5454c219758c540866d6215010cb551320ca5f6354342ad185421027561d52209d987540c25d6395110cb14a415071c5350d40cb50d5210e3c64546308f191500c65e6514d109b58a53c433642145428f59253c4355518c43097d8d544823e6494c31cd552510c25c6550d32cb189540865e63150109758c54c866c654c920b3588438c277654c4318f592538863d65950309d984540c25e6314b109b98a53c426c6254630d390d5210e3d6414d20c7552530863e6515130cb55232c823c6454420b91854210a3d6494c31b358c428865e63153208f592520831e5350e419b58854cc29c644c0308f593528427b65440109758c520426c62544409e181544ca5c6354041d954a510c2b461508428f59053c827661d52209758e528426c6550932b6580310c31e5454c218f990530873654544309758e520826e6294e41c7150534425d6510c30cb153524423e6414b10c7553430c26d658c8218f99053c832d54948309758c52c423e64949109e580530867765440108fd91508863d64d4f209b98853502b86050d42d54c9510c27860551319798c54c874d53508428f590520431c54d4d108f191518ca6f62551319b98b54cc67b654c0309b98b540c2e46150a328f191534867960150319bd95210871e5454f208f99053882b86050e418fd91518cae461509328f596540ca3e65151218f590530826d6214d409758c54c825d631494197d8d501066d6215331c755132cc65e6394a109b58a534867a60d52319dd8554486d86050d328f592528436932540219718d50d0a9d6310a41cb949429036742145428f590524c63f64540319bd89544872f54149109d185544827a60150319e98053086d863500408f59052c431d5494f209e983530866f6550842cd50c5150a7960d4c219bd8954442b46150a40d5cc9510c23e6414e10d314c524423d6414e209798c540863d6414e109798e529027b65480209b988540ca6e6215030d954421082756114c20c7152304c23e65d0941d394d320869c63500408fd954210b2e54548309d584540823e64d4f109b189544434e6314941c7d5053442b8644c0308f992544c25e63150329e596100425d63d5021ce153304c2cd6310821d3d4c524425c6354910da8c9500867661d533297d8d508874e534cb20c7551320c25e63d5320d5584534432d54d08218f992538871d54cc8308f19150ccae462504418f992520825e63150209e983540863d64d4f10ce90c5050e6f62544409d984530423d64949108f99053c873954d0030e9d0
  | 2 => 0x1920a090381c1100000140100805ba83018408802060c43a490500400000a815ea0000808320507000a2260a938b800068b80c360499c38000081000000880c041f048040000010100000af06ce60023000020002838007c30024ec01099b818090000000070401c1588019600200150002c00008007c030698054001305000001d0000001018142c3
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x110c800002078000400800000e1800400040001200041a150c6150932a1ae529a8720e26521854290286b98c4aa043615cc4210421a1ae729285205897210c400c24c39ac020881435c86355030a48e4a8882205287050d5210e86b90a6a1a81491d15108420a60e0a18a2a149874583320c30d298c0a1c83891886155021930e8b006218615531854210a86b98a4a1283291d1618c821a90e0a1aa421e45531854210ac438286a12658618c6055030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x8001000a098294c6050e41a05831886155021a05839486150a40a808050c6150932a098218c6055030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 5 => 2*((h/240+packedAt s0K5 (16632+(h % 240)*10) 10) % 616)
  | 4 => 2*((h/194+packedAt s0K4 (15732+(h % 194)*9) 9) % 414)
  | 3 => 2*((h/36+packedAt s0K3 (1225+(h % 36)*5) 5) % 25)
  | 2 => 2*((h/15+packedAt s0K2 (300+(h % 15)*3) 3) % 5)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fff81fffff841ff87fc3ff87fffc0233f3fc
  | 2 => 0xfc1fffe07e1fffe0ff87fc3ff8701ffdcc7ccf
  | 3 => 0xffe0ffff801fffff0007ffc7ff801ffe0f8f0f
  | 4 => 0xffffffe007fffff80007ffffe007f00ff0
  | 5 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x984208c5140408052809c0498094c43011b15c
  | 2 => 0x29441143202900a05882441288214950c454c5
  | 3 => 0x508aa2880d52454b0444aa85550292a60a8b0a
  | 4 => 0x6294c4124903567295502206664b00c7600ea0
  | 5 => 0x8318871c719c679ce6673320440c0307bf6000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcfcfcc0fcccf000fcfcfcc0fcccf000fcfcfcc0fcccf000fcfcfcc0fcccf000fcfcfcc0fcccf000fcfcfcc0fcccf000fcfcfcc0fcccf000fcfcfcc0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_39531
namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x860003d500048030104108f24f0000440020c108030cdc43df43fc32fc31fe42ff31fd21dc31fe43ff40fd32dd30fc30fc40fe30df32ff21fc10fe21fd40fd30ff43fd41ff42fd10df30de31ff32ff41fe41fd20fe20bf42ff20fe32bd42ff30fe31fc42fe10fd31fe40fd42fc20fc41fd43fc21fc43ff10dd32
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x4920f89800201c80200000480998300030488800012858182838000000301800483088180138c368807820001000000028619898036af098784d02e00020598800086019a000516019406806750831aea90633f54442bca9995794c40af298415e510c6daa421dd94420bd280439f420c738a89857d4d42cfa12619d42cca7ca810d7151328f2a4635d530829aa421e710f42afa9a438d424cabaa7205794e20cfa1a859f42ccb3aa918cf55231aea96615e5390e78a8886710d42af29e433d540867aa990e7d4f42aea9a413d548cb3ea8984f55010ae29a219f5350b38a7a16b509209f2a4655d539075a8410e750a31ae2a0635c54cc2bca7215794e41ae29a85ad428cb3e87a14f55320b6a90815d538cab8a6a0d714f10ce21c816e52d06eaa2105b948109f2a6415d50ccabca6184f55020afa8265db504c2baa6205714530af298855e530427aa9215795130af288875c514cb3a84995794f20ce29a855e53902baa790d715231e6a12655d53086dca4205754c42af298655f53c42bca39867d0a31aea80635d5210ebea710d7d4d40e6a90873d540cb3a85984f95032afa9a83ad424cb3886a0cf95231ae2a2615e548c678a89857d4930af2a0633e5410abca610d754e30baa88815d538835a85904fd5130af29a415d508c6b8a690d795330b7290876f524433887a0e7d0932aea86875d5390abaa6085754f41b6a96831c544c3aca218d795132cea12615e518c73ca918cf95020af29c215e51ccb3e859857d4d10ae29a815d538427ca990d754b43aea80875d53c82bca821d754a319f2a0215c538875ea4a16b50a21bca80436c52442daa4085794743e7a9265ce424cb3ca821dd94440af29e83ce5210eb8a9996710c40
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x273f3084240340300043d8e24200b00004301f01100600b0002c0003640000000001040c354d420868d6210e408799251cc28d629523193588540c61e64d4e2187993534861f6550a3187992544c3294254021c3588544c21f65d0a31c39915210f0c655093287191538821c6550930a598753d0a1c6454d2093588544c21c645433293195424ca1e6494431c310d521030c4354b4187197424c2546154d20a358853d0a1c6454e10c3d95424ca8d6210f41c398a548c61d6295231c3d4d428868d6210c408b58a548c70d5250b30c350b504cb0e62151308799353c42566195132c3549420c62d621513083588544c21c6454031a3588544c31443544408799251ccb0d4214532a3588435061d621513096580540c70d5350b20c39515210f0d62952318358a548c64d6215330a3592424cb0d5350920a358b53d0a4d6295231
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc0081068338ecaa1265415c8435444081ae4322a018c0d7299353c428238aa6a1241035ca64d4d2181ae4322a70840c7654d4248282b8cc8a9087035ca6494730
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s1K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s1K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s1K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf0ffffe0fffc3fc1fe1f87fff0ffc1fe8cf3cf
  | 2 => 0xff07c3ff0fffc3fe1fe1f8707f0ffe1f734cf3
  | 3 => 0xfff803fff0fffc7fe001ff807ff1ffe1838f3c
  | 4 => 0x3ffff00007ffffe00007ffe0001fc0fc0
  | 5 => 0xfffffc000000007fffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10108022000840002202009110124044041145
  | 2 => 0x224104442450040a0c20882221049418314492
  | 3 => 0x44222a8842a220d4c11155044aa12981828a28
  | 4 => 0xeb5b312aa3aa967775444097cc80ccddc0fc0
  | 5 => 0x88c6221cccc332799999e64e08803111ebe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_39531
namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xdc31de31
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/1+packedAt s2K4 (32+(h % 1)*1) 1) % 2)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffffe07fe1ff83fc3fc3fffe1fc07fd31f3cf
  | 1 => 0xc07c3ff83fff0fc3fc3fc381fe1fff02ceccfc
  | 3 => 0xff803fffc01ffffc003ffc01ffe007ff0f0f0f
  | 4 => 0x3fffffe00fffffc00001fffff803f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8510023080220004c044048ca02451281051c5
  | 1 => 0x9308445194081141441c41146209321846c45c
  | 3 => 0xa2aa8830d548ad8222aa8215540a4d30b0e0a
  | 4 => 0x2c5331242906acaeaa8220499992c063b00ba0
  | 5 => 0x306221c63198cf333333327011030083eda000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00eeeeeeaaeeccaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_39531
namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x863ed4210afaa4187b8c832fd200817f54086fca110df54241ef298417e528c2faa1a1df95032bea8465df53506fca1a0df54841ef21e617f53503daa418df14d10bea8e81df318c6fca118f54c431dfa0c835e53102fca4215f54221bfaa463ef52502fca3905f94332bfa82637f53c42f8a0a17790d30dea1681fa30442fea4085f94442beaa2637e50882faa3185f54242be28287fb40902f8a8995f94621beaa0437e5010efaa718d754e10fc982217c548caf8a2997d88421bfaa0657e5110fbe8721f78c932bf290877c53506fca420df15032beaa221ee520c6fca720df15020fb98e217f53082f8a2905fd4d42fa988637f54042faa7a057d4d21bea9a41bf54482fca5207e8c210bfaa2437d54482faa5a05f15310bf298433e540c6fea7105f15030bf294837c54cc6faa610fd84110bfaa221ee42c82faa818df14d42bfa9e43be540c7e8a299774cb30bf29c87ef21086fca8216f90840bf2a4637e50106fca990dfd5031beaa2657d51ccb7e87a0df953209f2a0416d520c7ba8621fb90842f7900417c53883f261086f95020fda82857c54486fea6085f94d10bf288637d52902fca6087d94420bea94637c50486fca518df94343be2926177514cbd884105fd4d20df20281dd300c2bca7085f95121be29c437d53c86fca618f714d41bf286637e52042f8a690df54810ee194637d5010efaa6205fd5220be2a2417e5010afca998ef90942be29283f741cc77a8220dfd4c21ef21887f5518c2fca320df55210bfa8a877d5310b7885205f15210faa0a217d51cc2fca2206fd0b40bb288417c53842fea5087dc8621fb884217e50907ba649877cc030bf2a2657d548cbbc6418fbd0a20bea8e417c544c6fca5885f54e41ef182617d53082fca6207d94440df21a877c52443ec42885f94020bf29e437d520c7ea20085f55240bea94837d54486fca710df15130bf294857f53442faa2197e88020f710a437f544c2f8a7905f94a32bf290437c548c2e8a2a1df94820bea8c817d54882fea990f7cca32bf28e617e53082f8a6905f54610beaa041f641107dca4205f54442beaa2617d53843e86210df94321ef984617c53042fea9195f55320f7992657d508c6faa598fd48421bfaa421f9300c37a86a0fb54840deaa063df430c6fca3a1ded4142bea8e85ef328cafaa8085fd4d21beaa48774514cafaa198df94632bfa82436e520c7baa7085fd5131f699243bf41106f8a6105f95021ee18a617f524c7eaa2105f94010bea8643dc31cc3f460185fd4930be29421f541c42faa2205f95130bea98833f54482fca9985f94040fb188637d5190efca621dfd4530baa88417e54443da84905f95220bea9c857e53d077a80205d54630fb10e217d54ccafaa121fdc4010fa208637d53902f8a2a15f54f10f621441df32cc2faa910df54743
  | 1 => 0xc4300c388e00109c01000010000014000054000d8000149d0042f02c4e1c805100060740004c030d04407c0100073004232749604801068120f83d0541f08c1a00c0b0c808003eea2a1ef50940be296217f504cafca690dfd4143bf28487df324c35a84215fd4142de210817e5410fdc84907d54440bea96617c514c2fea8105f54c10bfaa6417c54882fca5a1df54341bfa8a85bd43d0778a89057d4d41f7192437d549077e81205f94410bfa8a417e518c2faa3107d90510bea9683bd4210afea9985f95131dfa18877d53886f8a0995fd5332bf29c21f431c87f660985f94421fb98a63f840082f8a4085f55331bf2a6657e520c7f661185f15321dfa14853d540c7ba6218f754c40fb98843ef20882faa5085f95310ee218637e53106f8a9985f94c42bf28e817c504c7ee4290fd0c510ef19463de53842f8a6a05f94210fda00417e548cbf4a018df94242fba0a837c52502f8a7887ec8220bea9a437d540c3ea42884f15120bea8c657f54886fea8185f14931bfa9e417c54087b8a690dfd5331bea86657d53d06f8a8087794c40bb288817d538cafaa6885fd4b10bc28285ed20082faa990df54b10bf29c81f45150efca8905f94430b6292817e50086fca3995f54430eea1a61f85050afea4885fd5132bf29c41dc438c6fca8107e54031bd28063ed32c86f8a0a0df54910bea94617c53087be6218dbd4940fc900417d53882fca120778c730bf29065fb10442fea9185fd4943bfa9c436e52102fca5a05f94640bf294217e51106faa421f78c530fb98c63f641c42fca1185f95041f790c43f6518c2fea2995f15332be292877d52d0efca598df55032bf2a021ef4250b7a8621f7d0e31fba8a657d538c2fca8205f95230bea80837d5010bba64195f55230bba8a87f441cc7e863885fd5120bf2a061fb10843f680a05f15320b6a90817c540c6f8a918fe10320beaa661f910042fca318efd0d41bea94417e53c42faa7a15f15110bea86857e50d0afea2a05fd4141f7a14857c5150fea43885f55242ae29a837f53506fca2105f94840deaa0417e500c6faa9887b48421bea806376518c37c82a0dd54440bf280617c54886fca5a0df54021bf29e817e53d0b7e8721df54642bea88877e53c83f280205f94032bf29c8579500c7f640905fd4e10bea9487fa10043bc6298df95221aea9841ee20483ea8220df95031be29e437e520c2fea4a05f94232dfa12813d540837c85205f94c30bf292217c51502faa510df94642fb98a217d51083be64195f54f20fb98e43bf40102bca6105f95210bf28c417e510cbba87985f94a43f629281fb40c83be86a1fb4c832ae29a43ee32c86fca69077d4d21aea98817e5190fde8410770c831fba0c837f525077e84215f94c32bea80657d548c7baa6105f94b30bf28e857f54c42faa4207b50b20fba0
  | 2 => 0x10002a1800c040125b80d008180800a0f84c12035010021f4200440108c020100501c00004a003405000110001400407010570741d00000020010ec2b05402130050d8470940211c040040a02c03000290206e1c4123d45b0106706011000000000b0f00004c360d4a500409000082741e00004078252bc08004020280006c0100c6901c10004060181a154020002000c3a0080002c0102c0f040811100006dfc008051b4030300002812004002080004c0000000038000000a0000000c0308c200d9120000013
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x951102d463484219d587530823f6550441ea90840c834d528c831dc5845050a5d63d5020d5d4c31c873654544209e580540ca3e64d4f219b996424826d6214c10ba1814210aaf65508429798c540c35553544409e980538863e6414c219dd855310a5e63940109bd89544827561943329798c520425e6394d21f40c5304423f64549109e580540c66e62150209718d51c82ac644802097d8d544425f63549109b58b54c434d5354840cb552520c72d54480209b189544426e6215030d554d51082ac62500409dd85534826e6215010b5d95310c6d4614cb30d594d510827965100208f19153442d463507108f990528427461551308f99053c427661150329d584540823e64148109798c54083a860508429d984520423d6414c209b58b540c6cd620c530cb152424825d63d52109ed95100426e62d53109718d524427a60d5332b6980314c27661d4c109e980530875453d054197195434c25e6394241cb189540831c53d0d41b958831c425e63d5210cb55320082b864480208f590530865c63551109d9865090e3c6454910e5d0f410c63f6550c439d587548c25d6394221cd952510833954d00208f590538872c52509409b588548c2766115030cb548421026f65484219e58053086746154c428f592534825d6314810d554e510825d631501097994534863e6495120d514f21486776155132ce181540823f6454d209d986544cb355494420cb54b401027a60d52218f997425034e5354840b5185320caa86050842d698c5050a7661152209798f54c867661d4e20d658c5050af2600c5109b98b540c6796014e21d594e510827960d5332b51854310f2c5290140ae181425032d52908409b58854042b5640c7109d9845050b4c538c921d5d95310c6ac60508429758c540827561951328f59052042e4614cb21da181521026e6295131d554c31c42cd620c730d58c8514ca7a60150319758e50906756115032d9185520c72f5410a209dd9510042d46150f308f59642102d4644c4319ed9540102d4624c431e5951310c755510c7309e980540ca766115230ba181424827661150108f59053c425f635512197d8d5110a5e63d50209d594310876852d0140da549500c6b46150f41b5185434c27a6014c109b98b54cc27561d52329b588548425f63547409758c548423e6414c10a759031cc3d13154031b558e310c67661943329d987548cae962103209d18553482d463504419dd95310c63e64d4b109758e500425d63150219798c540427860551329798e508872c5488120da54a500c7ab42d00208f59353c872d62151209e583540c67a6015021a7590314c2786055121ba18142c837261141429d195414425e6314a10f1549310c6b86050842f1949310c66c62551309b58853c426f62551309dd95210873a54540319d987540834e5394840
  | 1 => 0x20330cd1ab60480c0c0600018080000000322d060000414141a4ac03113a55a012c3ac00020901004040404000d7278200200000100c000000018041100c16fb00815f037018301e130084c040007838000b0d0fc0e0943370045b080004437038640205090e40200098d02c01028242206010b802021500804020580006070180c2400140006e7e030140c0002004086b048106a62078f0300f07358000b00008280c7982a6f6548020cb14b425023e6415031ce9085050ad463487109d18553d025d6314a108f990538863e6414c20dad085050a5e6315210ce552500c6e5620c5109b98853c4278654c110d594f108425e6315220b518d414432e5454831e5551310c65d63951219718d51d023d6414c10ea108400826f65508429e596100426d62d53308f191534826f6254d109b98853042776154d2197d8d544c67a60d5031da949500c74d53948408f593530826e6215210f44c6500c7a942d0320cb550420825e63150218f590528425c6354442ad590314425f6550c439d98753083655294440cd553410c72c5450b209d984540826c654c9218fd91534426d6215031d5d0c5150e5f654c431cb551520c75651cc2309758c548825d6510c318f990540827565104319b988530873a54940319d987548c31d54d0c319b59742082d6644c431da94a500c7c6320c7219ed9520082756115220b5d81310c65e6314c20ab5924210a5f654c030ce551500c65f6354720ba189401027561d5020b5584320c76552544408fd95401023e64d4c208f596540823d65950319d5845050a6c6254d1097596530825e6314142d3588534867b60551209758c5050a7b654c0309d584540c2746154f20b5986304c31d5454c209dd8553d025c6355121b5185324c33854c81209758f54c867b60551329dd85544c67561d4e209dd85544c26e6215230cbd954210a6c65509209e5805408755530c421d554c314432e5494831c718d540c75a6094e109798e54486756114c20d594e511025d63d4a10ae18142d023e65151209d997314431e5454c209b58a544c6766114c20c795253083665294440dc982518c27461551329b594420827561942439ed81544873461550319e583548872d4254042b958831c863f6550842cb553420827765504419bd95320cbab60508429dd8553c832d52500409d19521442d66384110b558c410c65f654c832b518d214435a534c210bc98630442d56110c31d594d511032c54509209798f528423d64d4b10cd551510826d6215030d554e511031d5494c209b988540c67561152308f992534826f6255110d994
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x810007001c270294bae85a00419458d6114142b82e418a6088591740c5304428b3a6a618e43c45513154031a88e4a98628842c765512008263394c898863c1551524c431e82a498aa018e29651084008314ba8c0a1085a89c46050842a28e8a9862886a1711814210b142a0c0a16418a1886055020952ed2108190689731814210b45398c0a10858a1506050920
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x10c81735c46050842c21755c46050842c09755cc6050842
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
  | 2 => 3
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
  | 6 => 2*((h/27+packedAt s3K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/216+packedAt s3K5 (15822+(h % 216)*10) 10) % 586)
  | 4 => 2*((h/147+packedAt s3K4 (14402+(h % 147)*9) 9) % 379)
  | 3 => 2*((h/14+packedAt s3K3 (1078+(h % 14)*5) 5) % 22)
  | 2 => 2*((h/8+packedAt s3K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf87ffff03ff1fe0f1e3f8ffff1f80ff831f3cf
  | 1 => 0x7f80f8ffc1fff1f01fc7f1c0fe3ffe00ceccfc
  | 2 => 0x7fff00fffe01ffffe007fe00ffc00fff0f0f0f
  | 4 => 0x800000fffffe01fffff80000fffff007f00ff0
  | 5 => 0xffffff00000001ffffffffff00000007fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x90a201184022001060882465048a2501051c5
  | 1 => 0x112611228ca082500a43908a3212643046c45c
  | 2 => 0x22145244186540b620052410a48149a30b0e0a
  | 4 => 0x658a4892140652b54900024c92580c5b00ba0
  | 5 => 0x4460c00e318989cc9926493800060106eda000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeaececa0a0fefeeaeaececa0a0fefeeaeaececa0a0fefeeaeaececa0a0fefeeaeaececa0a0fefeeaeaececa0a0fefeeaeaececa0a0fefeeaeaececa0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_39531
namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x73c0003a400400c0081002311a000010000002000c0080000356f441ff30f741fe31fc40fe20fe10fd30f510fd31fe40fe21fd40fd41fd21fc41fc10fd20fc20ff40fc30f710fe30fe42fc31ff42fc21fd10ff31ff32ff43fd43fd42fc42fe41fe43fc32fd32ff20fe32ff21fc43ff10ff41
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x83f721c43de84a15f54440fb288813454443de64997dd0630bea8c21f640443de4310df14142fb88021f65190efca5197bcca32fa98a21f440c43eca1a0df95321fd184417d510c2fea8905f95032bf29081f740443f64090778c130bf29e83f552d06faa910dfd4f20db2a083f652107ee87885f94630fa29a217e53087eea2a1df14d41bea9e83be54cc77e8220fd14540fba82217f540caf8a7105f14d21bea8c657e54c437c82205f15120bf284437e530c2fca8996fd0841be29e21be4350efea098fbc8421dfa1a857d54c43e865887b50842bea96817e544c2fca2197d10521bea90877f54887f460185f94e40fba8a817d548c6eca3187dd0631bf28c85bd54cc7e8a1a0fdcc310bea8885bf43907ee82107d50841bfaa021f654c43ec4210fd4c110ba28a877d52887e6a0887d55310fd100417d54907f660985f94720bea8c617d540c6eaa2205f55242baa8c217c53483dc4290fdd4532bea9a21f741443be65987d54420f721641bf42d03e86210df95030be282657d54ccaeaa2187d94f41baa8683f721887e883907dcc531bfaa041be540cafca018fb48421fba9221f453c43ee82207dd0721df2a041de53083ee82085f14e10fba1e83de324cbea43885fd4941f7904417f54487ee63885fd5320bea86437e52082f8a998df54e10faa16217d51d0feea020dd95310bf290837e54043dca4205f14c20fba0e61755190afca220fd88110fa20e63f742443ea83887d8c621fa212217d50907ec6218fdd4542bf29863ee20483ec84886f50040fa19683f550d06faa890df54021fb906217c53c82eca2195f54043dfa1a817e548c77aa8105f54a43bb28c857e5010feaa7a0efd5110be29e43f641c43ea6420fd10610bf296617c5350bba8621df14540bfaa421ee42482f8a4885f94f20bea80857e544c77c82a0df55243bf2a441f632106fea0a15f94831fd88421bd429077e8621ddd4542bea8e816d520c3eea6887d10c41bfa8a877e54082fca0087ed0140bf28e877e53442fea918fd54642de2a221f621443e882a05fd5110bea9c657f53886f8a990df94b10bf29e85f652c437e85215f14943faa1883bf4210bee8290df94742baa8c617f514cafaa8105f54a30bf290217e520cbea81887d0c510fa18221f421442faa1997d94642bea8c817e5090fee21085f54730fba0a83f542d07ea65885f14d40beaa481f5510c3e86390df55220fb196217e500877a86a15f94e43beaa221f552443f681207d10f10fa20a41f550106f8a5885f54e42fa28a657d52842fea6087d90d10bf296637c544c7ee8320df15110ba28a81df4390fea87887754c40bf28e613d540cb6ea8886dd0c41be2a243fb308c3f641104f55321fba0e41f630442faa110ef10440bfa98437c54082fca88877cca32bfaa2657e54cc37e8620fd48421
  | 1 => 0xe5210bee8298df94d21bea94637d5090b7c83205f94042fb90a437d53906faa9185f54341bb288817f52442faa7a17d54d10bea9c817e510c3ee8420df14810fb98c63bf42907e88420dfd4d41fa986217c544c3e883105f14930bea8e657d53483e8a620fdccb41be2a0217d50cc7ea84885fd4f21fca00817e54106faa6216f90140bf28c41f752107dca41877cc930bf280417e5410bee83205f942309f2a0617e51086fca518fd94b41bf2a243fa30483ee6390df94a42be2a6217551902faa1a1cf95032be2a063f720442faa5a1df94640bfaa0437f53c42fea5087d90c41bea88877d51d0af8a910fe84010fb28083f742c43da65905fd5230dea18837c5150ae8a2997d10b10ef98c637d51082fca0187dd4c41dfa1c87f930883dc65907d10621fc980617f5250efaa7907790c43bf2a46176510c2faa8985f94e21fa20861cd320cafca7217d90b10bea8c417f52503e8a4887d50441fba16837f53442f8a710df94041f6a1241f731443f240105f15231fba9683bd4210afca5a06f90942fb106217d548cafea7085fd5131fb08221bf41906faa9905d95041fa20863f7414c37a87a05f94342bf294877d53103e8a3a05f94f10fa992217e5310bec43887d94d10bf29887f5318877aa8195f94331fa20843f454c42f8a9185f94740faa8c877f53482fca318fd10630ef18a637651902faa598fd14543be2a0657d540caeca3107dd5110faa02213e54083ec64887754c20bea92215e53083eaa5885f94f40bfa9a81b543107eca3104fd5110fa18621f5434437883207d94f10bf28c437c53042eaa2105f54b41bf2a641f443442fea4985f94732beaa043f642d067aa8107d15110deaa643f5310c6faa7107d94c41fa216837e50d077ca8185f54840bf29e43f441cc2eaa3107d0c710bf2a6637454c43eca2105f55030fa10e21f554443ec87887b54840bea8865f654442fca1195fd4121fb208837e510c7ec61885f54231fa20c636e52102fea9195f145209e2a2217e5210efca2217d48110f699241dd320cafca1215f54243efa1a87dd32cc2faa3907dd0620fa20841f552106fca7105f54032bf286437e508437e81205f14143bea90837e53106fea0a1df94a40fb99221fa500cafca1a1efd0940beaa241dd310c6f8a9107e90040be292817d54cc6fca5a1fdd0621beaa643f6510c2fca1106f50f42bfaa621ee32482fca5187d94910eea1e617d53c87e88390df55132fa208817e50ccbe882085d14542dba1083f743106fea2905fd5031baa8865f7410c37ca990fd8c710fa20a217f524c6f2a019774c030bea9c437e53043bc86987794c40be2a421f741086faa5207d54620bf29043f754c42faa9085fd5321bf29a417f504cafca3195754c40fb21e837e50903ee8218fd08310be28a87fb104436883207d4c521fa19
  | 2 => 0xa048bd0d8080140e00405000060d8111680009401044082085102cc3000002100005c030f0210081300073010220b4030084202c0d018300c837014020642d0f0250640911417018460080b08d130400a018001cc24008002e01002c056e40e0000001004034781102700c120883200001020040d80709c5f0380a0000403800010012ac000a0081a403049ad0141000006060c3004231781600c130080016826000120140e08400000000287c12800039590c0110245b018430180b0041505823058030001a0d8050040800c00040000002f1d8060001001c030000102c070646c0003e09c1e0304808467008000840200cdc0140a000040081d034070d03100402030020340c07c050342c20000000070a01300c390843405c00128005300c0704a024640682c0681d05c000012600401128060080b13863000001040902c0600800008030045759815028010201e004300081205afca818ddd4543bea9843ef20083eea3a04f95331bf29221f6518c2fea690dfd4540bea9841bd42502faa5105fd5030da2a2217d50107ee8398df55131bba8a81f9500cafea998df55010fa29e837e531027aa8185f54830bfaa6617e54842fca118fd14542faa88657e510836882207d4cb41dfa0081f553107eea7a0df54b30bf29421f520c42faa520ef50e41fba0c217e500caf8a498f7cc030fb18a21f743443f220087b54830bb28c87f452c42faa9987e4c120bf28c83bf43d03e8a5a0dfd4810fa20c81f732106faa321dfd4c20fa102217e530cae8a8887d8c521ef21e61dd324c3dc84215f15132bf2a08777514ca7aa998db94830fb20a21f443d06fca720df94b41fa20e817d50d0be88298fd8cb41bea9e817654443be61187dd0540faa88817e54102faa418df15330be282437c54c82faa7887d44010dea10837e54887ea87a0de94032fa20221f441c42fea9995f94440fba8683bd43502fca9197750d30bf280817550106fca9995f54e31fb90a217e54482f8a9995f14141f6900417d53042faa620fd54630fa20a61f730442f8a5086f50441fb996217c53442fca4185fd4141bf288217d5190beca2197bd0a42bfa96217651082fca7087d90310dea1681f651902faa018fd54f10fa98e217d52c43e864885f94a41daa10837e5190efea2987b4c832fba0a41df320caf8a810fd54640bfa9c417f5150aeca320df14530fba0621755190ebaa6106f55030bea9a433e54c87dc64195f14941bfaa441f752c43ee6210df15232dea1887bf43d0bda85905fd4d42fa290837c504c7e8a020df94241af298817c540c2fca810df54e30fb210837d508cbee83a05f14c21b6a90817e5110efaa4087dd0710fb2a083f541443eea7885f94c20fa90a217f544c2f8a29977cc431bb288217
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x504ca6f6254d10cd153314426e62150319dd95210865d6315010ec58041102776510620add8542106756590910cd950410871d5310440ad59253442e66214341ad591321075b3254032ad59321c43493254032d954852107675294b419d58453482e662d0521ad99252c42f160d4b10ad98342106746550b10cd150534433564d4532cd153414c73554944209758e54486746155230cd98c54442e562104218f191524433a5454032ad99032c427561d5320bc582544436a32540329e583540ca7a6014f21c755253082756510630d594e511027661d4c108f59053c82d563d4b41d954951102756510431b598c20c42f1600c841b958b53d06b5640cb41b9988531074e5354840cd19151882f1600cb418f99353082756590841ad59242107c53294432d554d5108277654c4319d99731443d1300c110b558c50107365494420ad59252c42756194232cd50d501066c6254d10cd95041cc73a5494032e950841c8276650c110c795253082f1600c910ad992321063d64141329758c52843355410731cd15153442e76254d10cdd86540c33454481109d997414c7365410631ad993314c67561141429b988548c2776054643c754e411027565d0410cdd0a5190b34540c110b6181434c2756114132cd544419033654d07219d99643c427661d5021ad594419027a6014c219d98652d02766494410bcd81524426c6550920ad99030c425d63150219dd85544433562151108f59353082b464549109d594418825c6355120dc546500ca3d6414e209d984540433765508418f59253c433454d0d10f24c9500ca7765504419d587548827561141439d98653d0a6d6214c109d584538833454d01109dd85544ca7565cc421cdd85540c23664d4532cd186540827561d50209d19532c427b6055132f24c9304825e6315210d594e510833563151109d18554ccaf160105309758c52042756094643ad99331c433743145429d191510c335521044097d8d52443365410621ec10640102f26010910d994951103345450f108f99053843954310f419d99432c42b460508419d18553c82d66310310f1185320ca766510540d5d4e53d066e6215210b9189534423e64948219e58054086776155020d954841102b562950418f990528433754d41109d587544c369524c030bc58052c425d6315220bc58353c427761550329d987520427661d5232cd150324423d6494d219e98054086746155120cd15142443665294440d954b411023d6414c219dd9542c423e6494f10cd153534427765104109798c520423f64549109dd9741082766590d10da4c9500ca3464546209dd97410c39543107309e983540cb7251540329b98b540c3a552d0841b9588404433454cc910ec980411033554107308f59053c873761550329dd85544c63f6550441cdd0c51502d66314341
  | 1 => 0x433454d0910cd546411036652d0440d554f41083345410610ad993214875653544209d99721443345408510ad593314427a60150319d5825190a5d63150209798c54087355410430cd15241443355410421d954b410c25d6314142cd15132443655210430cdd50418c2b76454d10cd54c41902d56308110cb55120082e5620c110cd553410c27561d5120cb54b40102e662101109b988540c279601503297195434c26c62551309d584548c275650cb10ad590304433664950419b98a544c674654c510ad99321c435553d04409dd9532d067761553309d984540c2b66494910cb552520c27661d52309d18553d03555314c419e19530482776155121e950842d06746154d20e994841102f160104409bd952108734544c5108f191518833761953219d1954344274654c521cd950414c677654c9109d98754083376215110b958840c42776054432bcd8154443365450310cb551520c2b56494f10ad9864350ed66314841cd552510ca3f6454d20cd99054c433454d0f10cdd08515023d6494910cdd50414c23d6414c209d185540c2b46150d42e554f431067464546309b58b540c23c6454d109ed951004274615533097d954310e3d6494d10cd1533044276650cb419d994204426d6214e10cd152404426e6214e10cd551510ca7561d5232cd58754442e662d4f41cdd8554082756590d109d992510c3356510640e3551320cb34544c110ad990421067661943439b588540426d62150319d584530836652544309d987544ca7561150329d9865090e6f6255130cd15210442746454432b958853106ac6250d429bd95320ca766510110cd10650102756590c419d58653d02f160d0440cb549401035553104409d98754883c5320c8419d185544ca756194b439dd8554482b664c86219d98753882d56314341ad19151882746154b40ad99253c423c64546309798c540423d6414e10cb553200827665d0510cd55041c42b46454d109d984524c3374254041add8943106b56408310cd18c544434c524c930bc58041882d56310110b3d95320ca756194243f14c8324435953880209dd8552d027561149309d986544cb3454106208fd954210b345490d10cd551510c2b56494910b958850106756194f429d98754043355210640d9549510c2d56310431cd150424423e6414c209d9865010e7661d5031e950841482b664d4532e554c411033654d06109d195214427461550209dd855210f4d53948409758c54842796014c219d580514ca776155232ad99020c42f2600cb10cd153524427561943429e181544cb3461550309d99630442b560106409d98650ccb36540c7219d987540c2d66314041cd15142c42366495110dc586500ca766114f208fd91518c27661d5332cd14640503346155032cdd86540825e63d50209e980540ca7761550308f99
  | 2 => 0x6515110cdd91518c33554107209d996424432e54948309d98653d03354314542dc946500ca6d6215210cd95341cc7976350c41d954a510c23d6414810bc58053c427b654c0309b58a544c67661152209ed9540103356115110d314d32c82d56310310ad99331087c5320cb109d984538836652944308f992538867461552329d9845050b7160153109e58053c86f36054d109dd9543c42776550d109dd9542442f160109109dd9741882766494420d594f41102766590510cdd50414423e6494a318fd954310f3454101109e580540c6b56395041dc945100432e54548309b98854082f160d5310f24ca500ca796584010ecd0540103345490310ad993314433654cc721ad191100427565104309d185544c3376454620bc58054c43345410530ad592431071d53500409798c5050a6e6215010b598c40443b14010110cd188544423d64d4532d64c9500ca3d6414d209d986500cb3554944309d59441082f16010630cd952510ca756194043b998850107b054d4110ad99454443355310440ad59032107374394643b958850d063d65950329d987544c25f63551208f99254442766194242ad58b43107965310440cd153214427561d4c209d59441042746115110da54a300c38e544c8329d59741882f16014c419718d52443376115110cdd8554c874e53948409d1855210e756115220e9d89421063d6414c10cd951510c23d6414a109d584540c33554544209dd85540427461553209dd95100437261540329d59432d06776154c42cd150418c27661943429dd95321073654544329d99432106776155130ad9864250a746550110cd150204433461950309d586500431e5350e419d59432106766590110ad185401027461550329b988530825d6594c20cdd50418827561d5030ad191518c33454105109d5865010b345488110cd185540827560d4542cd15141442b76550c41bc58032c42756194242dc582544426d6214143cdd86540cb3454d0510dc585500cab66190440f14c9510cb365454420c954841102746154b309dd97418c23e6414930cd15252442b5640c910f14c832d06b56010440cd95041c827561d53328f99353c86b664951109d992518c23d65950308f592538875553104209b19532482746550f10bc9805310674654cb41b518d52442776154d208fd9153442756590f109d19532107356015110ce551500ca756195132d9948410c365529444097d95300c27561d4e208f990534823e64148109d987544823e64949109d583514ca756095110b998830442b563d08419d99741503345494d10cd550410c76652d04309d984540839653d0c419d990514ca7765104309d98652d0e3e64d4532cdd8c54442776154b309d984540ca7464546209bd954210b665210440cd95340c427661d53208f19153482b96010440cd150434
  | 3 => 0x310cdd5041482f16014841add8d4210676658c5219dd8554c827661d4c20bc980521063e6494d109d984530866e6214c10ad993214423d6494821ad98254107365410410bc98032106776550110dc545500ca7a6014c209d597418c33743540419d99620442e86050920ad59032c4276650c9109d1855310a3e64150329d587544cb3454d4110c554c41102776154d21ad18543d0b34548c110ad59020443366215110cd55041082756114f20cb548411027765106309d984548c37261940329d586500cb3554d04209d58652d02756510421cd9504148675650c421cd952510c33954940329d587548c3a652d0841ad99253442b160104409dd9542107366415110cd152214427561943329d5805150f4d52cc030cd15052442776155332b558c521063464546309d58650d0e3d64149308f992534866e6214143cd550544423e6414f20bc98043442d663d0531cd95041082746550910b998830c42b664cc631cd95041cc33454105209dd8553c827560145429d99642c42b664cc841bc98032442766114810bc98032d073654d04208f99252c425e6314c20cd151524427661d5330d354f200833761953319bd95200831d5454c20c7553300c27664944329d987540cab46050c41bc58041482b66408110b558c20c433543145409798c52842766114c20d354d52102b564cc710d554d51102766494620b958830c42b660d0c41b998840c426d62152308f59252c425e6315220c7551300c35653104209d19532442776154f409d58754cc34d524c030ad59030c426d62150309dd85548c2756590b10cd15031443355410721cb54a41102766194232d654d200823d64d4f218fd95401027665d0521d594d51102b6640c8418f592528c7354214540d554e511035653d0420c714d4350b4d3254032cd152324427760546429d587540cb1e5454c20bc58041d033654d04308f99053883366515110ad593214423e64150309dd9441082766114143d554e51082b6640cb41ad99331c875653104409d191510825d63d50209dd9532c427661141329d98453482b564cc8419d984530423f6454620b598f52d067560d4543b598c20443345450d10cd186540cbe12008110cdd8554cc6b6640c910cdd9543106b6644c841add85431073654104319d185548833454d0521cd152314423d6494c318f99053c86766194042ad59232107365410430cd509501067664d4532cd15342c425e6315020cd191518c27560944328f992530c6b6640c110cd55054c433664d45329d19541443c7614c83297d95310c71d53d00409d584540834f654c8328f99053086766495110bc58341d025e63150309dd9543106f16094910bc580434427761552209ed9520082b76550841d314d32482cd638c8329d597410c3b354d4110cb9494290675650c910bc582534423e
  | 4 => 0x100502810000070000c01c06198120900010c0401812404390198d0145c074410500e390120092fb88060f0050043a03c22000020000900a0d090040024c0ac00030004743c0000f1d400058663bc0007c00004000303125c0300c0e03c010141600801018180140330000004010080002c00000000ec0107819324390000000c0901020008020801b014160040a7900902c40010017480000c010280f03806000020801d02c0000000044000082d0119704c29000020843b07c52011d7018010800100038b04cd0201304d5179c000503200c0101c0f004031140f02801000162d0780100100c2806415000010004c0001c04485008d10640f020040083e038160081401c00054000a40009409044011ec0001002044000006d00016008030280700404129cd0c42c288050580b0080b01c050002803a890340004c01008000001d05c0003422ac62602883004142a81f000be50003008030080401c00010870d40001c09000000040514401048000019100c0800008000030243fa780602c0281411034020000000c1d0500000000008472b02d00007024e60974d5348020cd153204427565d04208f59654083365410721add9152443345450110ad990431073654107108f990540837265d4110b5d8d524425f654c832cd15121443376015110e9548411025e6395121cd152424423e6414c10e550c414c3345410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x30008040002001b120000050009070b0700150b0c0102030b00070002150300110902010008034453000a0c070600001500042b0116022b061002010003320004090602a60e8b0ca019544754c8324428b39ec22a2218c1516010630d24a6b0082206245418953442c83828620a61891516210110a2ae62a0830862454d8953443a0994a2a8065499cb6115110e0aa8992a219691644c03044322b2a64190830ddd8540c910b40e0a10829043674d8552cc3122a2c4206210d9d36154d21a8ce7a94a5a0e51535805310714a92c0208810d9da545031086aec2a064886337558041103182a2c020a61495c8541063086eec2a060886a16250040443182a2c020a419158d5214841c42a4b008220625621885444292b96c22a2218c151600c910a2ae6310a88851573950414870a2a2c6202218c1526010d10992e6302849061553580411030a2a2c620621b04c9600c910e14a8992a01972054480204421a3a2c3286658654d6010440d22c6a00808851573d845444330a92c0208810d1d564c851094ae43028620c34745865004264b90c0a1a61b0589300c110c48a93108088530705095010760992c01962185150635491092ae63028420f4132545500cb0a2a4c61022151dd5320cb41c90ca99260904b375580411021a3a2c328465985496014841c60a8b0083105307050d5010790a94c0208814c5c06315110c22a6b00822043674d953244328a9ac020881c4151300c110d42a4b008220516731885444319322c02a621c454e6010440a2ce7b0ca990f05535484110318a9ac02088185153635491086eec2a6428851573150418830a2a2c610221d0dc53254032b0ce9b0a64194347559331443a0992c2a8065895486150040c60a930064886305498042442923aa8420a410d5d8540c110d22a6b00822043674d8553c82593b682a00819154d6214c4186aec2a04088721525804110350b2240102210d1d16094432c28a9318808843474586500ca58382c8990830ddd85408110a4ae4318a8886156318c5444388a9ac020881495ca5410531c4aa4b00822054672d4e53d07122a4c418221d04ca615403286eec2a662885257215041842983aa80202210d9d3654cb10a62e0310a88843474580514ca8a3aa8620a610d1d1650c910e80e2992a01953074585500cb0aa98c2a0081c25513254032d44a4b008220471701953210693390c62a221c154e5210440d8264b0065a0d2672d8654cc750a12c020a41b058d2008110d2286b00829843475590324421a3a2c3a9c4189151620c110e08a8990648863152580411038329aa420881b04c9600c841
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x200028469a10026c585a1186151300c110e01535496010440b0284dc53254032c11635c06315110c107558d4010110a21821516010630e01539496010440e02535496010440981831c14210520c05735886215110d00744c96154032c20755894010110e005458d2008110911831c14254041e00544c9600c910a21861512008110905859d3614c832c05635c86315110c21625c06215110981821c14310530a11831516010620940874c96154032a0586151320c910e0054589300c110921821c14354041a43854c9600cb41
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 26
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
  | 5 => 2*((h/274+packedAt s4K5 (21654+(h % 274)*10) 10) % 802)
  | 4 => 2*((h/329+packedAt s4K4 (33554+(h % 329)*10) 10) % 883)
  | 3 => 2*((h/69+packedAt s4K3 (7056+(h % 69)*8) 8) % 144)
  | 2 => 2*((h/15+packedAt s4K2 (1560+(h % 15)*5) 5) % 26)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fe1ffff07e3fff063c7f1fff8e0fffc11f0ff
  | 1 => 0xc1fe0f8ff803c78f83f8fe383f00e1c0eecccc
  | 2 => 0x1fff00ffffc07fffc00ffc03fff01ff0f0f0f
  | 3 => 0xfe00000ffffff80fffff00003ffffe03f00ff0
  | 5 => 0xfffffff00000000fffffffffc0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x84242001104400000041104888202448005055
  | 1 => 0x9c4ce31231c98b1381c87211b9064c9866cccc
  | 2 => 0x2080452442809404a400a482124a01310b050a
  | 3 => 0x8190a48850201294a92000424949802b00aa0
  | 5 => 0x31118c00e613264e7324c92700181023dda000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0feeafeeafaa0faa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_39531
namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x10000000003be41f441b441f741bc41
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x10003a6521072aa620ec940419b28c83a55210762a020e594c41
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x180003215254041c154d52107115354041
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | 2 => packedAt s5K2 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt s5K4 (80+(h % 15)*3) 3) % 5)
  | 3 => 2*((h/9+packedAt s5K3 (189+(h % 9)*3) 3) % 7)
  | 2 => 2*((h/15+packedAt s5K2 (114+(h % 15)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe0ff8f0fe3fff0e3c7f1f80e383fffc33c0ff
  | 1 => 0x1ff0ffff003c78f03f8fe3fffc038380ccfccc
  | 2 => 0x1fff00ffffc07fffc00ffc00fffc03ff0f0f0f
  | 3 => 0xe00000ffffff80fffff00000fffffc03f00ff0
  | 4 => 0xffffff00000000ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42a2011224502002141504922080a8a811c055
  | 1 => 0xc46630221c8891300c83210ee4191918445ccc
  | 2 => 0x804524448094054400a4824492802510e050a
  | 3 => 0x8148a488902012a8a920004892525002e00aa0
  | 4 => 0x1188c00ce13264cf324c927000606063bba000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0feecfaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_39531
namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5007fd3100ff14001fe5200ff04001fd21017f88401ff2100ff4c007ff5300ffc8003fc40027f90805fe4101ff8c809fc4200ff94007fe53017f08407fe43007f54801fc52017f10401fd5100ff08009ff4101ff14c03fe2000ff90003fc3001ffcc401ff51027f50809fd4101ffcc807fc4300ff44003fd5000ffc4009fc5400ff84005fe51017f8c403fd4001ffd0c03fd20007fd4805fc5100ffd4007fd4300ffd0009fd54027fd0805fc31027f95007fc3201ff4c803ff3001ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x20a410ff8c351016f8a2a8827fd64d4813fe30ea409ff142520e7f8832900aff6154405fe10e4208fb9092110ffe87a9023ff5448413fe286a40aff0c321017f862a8873fe5194821fea06a21eff55252015f8c2a9042fd60d44037e304a402fb885210bffc60a904bfd43d4413ffb26a409ffd4352097fc87a881bfd649482f7eb2ca405ffd8121037fca49080bff3148413fea86a219ff54d520bffa80a9027fe64d4413fe28ea406ff58321035fec72906fff1094833fea1aa409ffd8752017fa219080bfe2154413feaa6a41eff50652087fc81a881bfe609480f7fb1a4206bfd8c5206ffe80a8827fe60d4805fb18a4202ff0435105ffea99081bee42c842fff982a406bf18f21097f865a8827ff53d4405bf28aa206ffd9721017dc439085ffe405482ffea82a409ff9475202ffca090847f741d440dfeb04a421ff4c75204ffca7a8867fe435480dfeb20a406ff18652035f8c929027fe5414805ff98e4206ff0c95204ffea6a901bfc611481fbeaa2a207ff18d2104ffcc9a901bfd65c8443fe996a40dbf58151037fac99081bff63c843bfe21ca406ffcca52037fca59087f7d50d480dfe900a409ff583520cffca6a900afe6154841fe20ea406ffd9321057fca190843fc30d4433ffb1aa421df54f52037fa852907bff419482ffe082a402ff0875106fea20a880bfd4154445fea0ea409ff14c520fffe21a9012fe64d4413bfa9ea402bf18452016f8a3a8806fe604840dff31ca406ff08552037fc849081bef209480dff196a402ff0c52104ff8a92905ffd105480dff214a417ff0c152017fc429081bfd6194801ffa924206ff88052017fa21a8802fd611481fff2a2a206ffd0852037fec329027ff60d440dfe990a41aff9915204ff8c9a901bfc2094837ff084a40effd0d510cffe62a90477d54d4401dfb22a209bfd935102ffe8090877ff31948017fb2a4209ffd53510cdfec6a905ffc605481bfe902a21bff5425209ff8802903bfc635440dff292a409fbd49520affe8629027fe52d4405fe18e420ebfd8d51075fac6a8827fc52544037e302a402bf98b2104ffea8a900bff31d4405ff10e4206ff90b2104dfec1a881bfc60c8443ff996a406ffd4b21035fec02901bfc4214837fe984a409ff1445204ffca1a8827ff64d44097f322a409ff14d5110ff887a9027fd61d480dfe318a40dff88151037f8c129003fc625441fffa12a222ffd0752017e8429082bff40c84177eb264219ff98d52055fac190803bf64484057f308a406ffd8e5204ff8c7a9073fe319480dbea90a406ffd925203ffac69080bfe21d4401ffb12a21cff90652077fa64a881aff64c840dfe320a406bfd97210dffc812901bff209483bff21ca405fd4412101df8c69085ffe5054813fe2a6a406ff1095206ff880a885fff4054813ffa80a415ff4c452
  | 1 => 0xaff6554433fe992a40dff50151035f8c62900bf71054413ff298a402bf99751017fe8390837ff305440dff30ca401bf98321035f8c99086bfd4154827fe080a418ff105520dff88129026fe6548413fe286a206ffd8252037fe40a9063fe515480dfe31ca409ff58f5206ffaa0a882ffc54c8441fe18ea402ffd4521047fa8490836ff6054425ff196a219df54d52037fec02900bfe1048405ff086a202ff5075102ffa609081bfc204840dfe904a406ff90b520cdfac6a9027fc64d441f7eb22a206ff8c9520befaa0a905fff10548097f326a406bf1905204ffea6a8803fd5248413fea96a220ff88752035fec19087bfe54948117fb224202ff8c52104efea1a907fff40d480ffa98a4213ff44052047fac890832fd63c841dff29aa202ff04151037f8cb90827fd63d440dff31e4202ffd472102dfac0908677f535480fffb1a4202ff905210cff886a901bfd42c8425ff996a202fb08521007fcc4a8812fc64d4413ff2a6a40effd8d51097f887a880bfe10c8415fe986421ebf59252025fcc99081bfc20c840dffa14a409ff1835204dfccb9083bfd6354405ffa0ea20fbfd9151017f842a8817fe3048435fea12a406ffc8121007fac2a901bfd52c8433ff992a402bf58721017fc639080efc63d440dff290a402bf18652037f88529056fd631480ffea9a4209ffd515103ffa869081bfe209480bfea02421affd0552017ee2090802fd6194813fe29ca406ff18f21017fc839083ffe42544377eb04a409fdd455104ffcc7a901bff20c8419fea1e4204bf19352017d84390817ff3048413ff280a409ff98752037fcc22905fef205480bff3024204bf1915102ffaa090817fe4048413bfaa6a209ff15152057fa8190827fc62d44037e3024203bf98c520fff881a902bfe30c8405ff98aa21fff48352005fac3a9077ff439480fffa9a4202bfd8521087f841a881ffe43484257eb1ea200bf5952104ff8c1a881bfc3248413ff306a201bf982520fffc41a9003fe525440dbf292a40cff54f21037ee429083ffe6454423fea16a209ff1465203ffca690812fc644840dff210a40cffd4f2104ff8a2a9027fd62d4427ffa00a418ff18552057faa19081bfc6014815ff9864202ff0412106ffca0a8827fd60d4415ff2064202ff8c7510cff8c6a901bff5214829fe188a401bf98151037f840a9063fe415482fff082a406ff98052005fac5a8863fe615480dff194a410ff4c351037f86590806fc6054405fe10a420eff98d5104ffec1a9077fd319480bfe1824209ff14f5204ffea12900bfe41d44037e306a222ffd0b52067fc8790803ff6548413fea9ea206ff884520bffa60a901bfc42d4805fa20ea201bf98351067fca790843ff30d4405fb28ea208bf59121037fa652900bfd1048421ff906a203bf98f21017f8219081afc65c840dff3
  | 2 => 0x52007f8ca90827fc505443fff186a401bf1832102ff8809081bfe631481bffb02a206ffcc85204dfcca29023fe644840fffa1a4202bfd892110ffa87a9027ff5494805ff882a206ff88321017faa29081bff42c840dff906a41fff503520b7fe822903fff6454443ff21ea41bff0c2520a7fc622900bfc514840dfe2124206ff08452017fca29081bfe6494801ff32a4209ff94f52037fc6590806fe6054813ff2a6a206ff508520bffcc0a906ffd1094813fe2a0a417ff58152047da849087ffe40d48037f300a404bf99052037fac029027ff53d4813ffb1ea206ffd8452017fa629081bfc42c8413f7a94a41aff19152057f8819080bfd51c8413ff316a205ff581210d7fca8a9002bf644840bffa82420cffd0f2100df8c1a901bfc32d48057f30ca41fbf58352087fa41a8803fd6254405fe28e4205ff14121017fa8290823ff644841dfe21aa206bfd9052035fec12900bff41544097f3224207bf58d2103ffa649081bfe324840dffb064206ff98321037f8c99086ffe5094805fe20a4206bf18e520bffa40a907ffc10d4805ff18aa217bf581520fff861a906bff425481fbfaa2a202fd8872104ff8a5a884ffe1014811feaa24210ff8835104ff8a7a886bfd6454813feb26a204bf1915201dfcc7a901bfc201481ffe322a20dff98151077fc86a8827fc5454415ffa864202ff4c72106ff8c0a881bfd52148137fb1ea206ff58e5203ff8869081bfc3214813fe29aa406ff4cb21017fe209087ffd10d482d7eb20a417ff8815204ffaa02905fff605480dfeb1e4213ff4c052017fc20a8806fe60d4825ffa1ea214ff9045206ff860a8827ff63d48095e322a206ffd4a52017f8839081bff6314817feaa64202fd1455101df8c6a880bfe51c8413ffaa6a400bfd8951007faa4a880bfd10544237eb26a21bfb4825207ffa84a8827ff62d4405ffa8aa20dff081510d5fac8a900bfd41c840dff32e4213ff5005201dfcc72904ffe3014815fe2864203bf18f52077faa6a880bfc51d4439fe18ca406bf98a5202ff8c090847fc42d4405ff8864200ff595210cffe86a9087ff31d480fff9924202ffc852104ff8a9a8826ff60d480dff900a40bfb50b21035f8c4a885eff605480dbfa90a409ff54c5201dfcc69081bee52148057f30ea40dff4c151017fe829080bfd31d442bff988a40eff0c951047f8c89084fff3014813ffa86a213ff90052017fc82a8827fc50548095e3224219ff58d52015f8c3a9033fc43c8413ff286a418ff8c5520dffe812901bfd6114801ffb0aa406ff993210cffa62a9026fc654840dff9964212ff4cb5106ffc80a886bfd545481bff182a208ff15121005fec2a900bfe51d4413ffa82a409ffd4c52015fac3a8827fc63d441bff902a209ffd5052077fa86a8826ff64d482bff218a409ff5535106ffac0a880
  | 3 => 0x4600c0805824121460a86505000020001300b00400858040f058534073ec3002c1a01c0408c0f0000a1041f02d0207506034450000a008f809e2903c1504c0200056014030000501c2c004030000102800000250281b0150423400838100081e02c1e000f10b40400c020fc672ac0f0005f08c00000030240000007174070280801c0f01486014190000000c042ac0c00808010090680500c3101008008000144a0901800003010040040400005020036800108c01484010240005d740000f000080a84715400028c50e484000000280041431014000000d000040281807c0403085018090080c0700101802028070e00612421300e815c2b000260000802c0610c3e010020000002c008700502c2902c1b000010a0150b832160b507c0c0940175c0d0000b07800010020081201001010aa00c7c0fc000380300000000020003003c2705c110000016402020000e845fea16a404bf99252017f863a884efd60148137fb1ea411ffd0b510bff880a908afd64d480b7fb024200bf597210bfda40a9057fd4314805fe98aa208ff951210dffc612906bff645481fde322a203bf98d52017f8a2a881bff641480d7f310a404bf9915104ffcc7a881bfc6494829fe208a409ff5505207ff884a881aff63c843bfea9ca409ff9445207ffac8a8877fd4394837fea04a41fff8435204ff8a029027ff52d4427fe180a405ff4812108ffc85a881b7f52948357fb22a406bfd925209ffe202901bfd20c840d7f316a206ff8c852037f841a906fff309483b7eb1ca409ffd4952037fc84a903ffd5454431fe18aa406ff1492104ffea0a881bfd6314805fe20ea21fff4c35205ffca99085bfd4114821ffa06a220ff8c752037f84329043fc40d440dfe10ea405ff8812103ff8a69081bfc52c8413ffa9ca406ff0ca5204ffaa1a9023ff424842fbfa82a420ff907520c7fc42a900efc635482bfe218a40effcc951017fca2a880b7e51d44437eb1ea403bf98d510effca729006fc6014805fe20aa207ff98d21017fe21a8827ed52148077f31ea21fffcc35204ffaa7a903bfe3254419fe29e4208ef1912104ffea4a8802bf645440dff10ca41bff042
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd73995211373c51d9151034fe72d952101cfc7358452006f51059521136bf71d9151006bf6418951036f7215845201cfc7358652014fc71d89510067f535972111ebc71d9121004ff74d89510367e5259721036f77158452006bd70d912111ebf31d9121006bd60d9121004ff7059721024fe7458752136be71d9151014fc7654951004ff7359721004bf7459521006bd32d9151015f47154921005bf7458552005bf7459521136bc21d9151006f77159521127b721d9121105ef7259521024fc7459721024fe7458b51006bd60d9151014fe71d9521006be70d9121014fc72d85521373f75d91510c4fd76549210067f65d4921006bc53d9121006f51058452136bc75d915104cfe76d9521006bf7458452004fd73d895111ebf71d9121004ff7358b51024bc7458452006ef625495101cfe7358652004ff74d9521007b510d9121036f72158652006bc32d915101cfc7358752126be32d9121006bf50d9121006be53d912111ebc31d91210067f505972111ebe51d9121014fc7654921045be7499521006bf32d9151006bc70d9151006f510587520e6f63158652137b451d9151006bf70d9151006be20d915100cfe70d8951004fd74584520067f53d95210c67d5159721006be72d915111ebf51d9121006bc60d9121006bc75d91210c5ed72995210067c50d9521007b510d9151006bf32d9121004ff7358452004ff7458652006bf64d8951024fc745865204ef45158752004fd73d9521126be72d9121046be76d9121024bc7459521006be50d9121006bf72d91510c4ff7159521004ff7358652006f510586520a6f6415845201cfe7359521006be60d9121006be73d915100cfc7058452024be76d9121024fc74d952111ebd21d9121006bc6458951006bd20d9151036ec629495112dbe76d9121045bc7459521006ed621895104e7c6554921004fd735845200cfe70d8552136bc31d9151136bd51d915100cfc70d855211ebd71d91210067f7559521014fe7694951006bd30d9151006bf60d9151106f62158752145be76d9151006bd63d912101cfe7358b5111ebc21d9121126bc20d9121024fc74d8951034ff71d95210067e5459721006bf6454921004ff7358752006ef2058b51005bd74995211373c75d9151006bf65d912101cfe73d95210d5bc7458552004ff745952101cfc73d8552034fd75d8552004ff74d8552004fd74d9521006bf20d9151006bd32d9121034fd71d952100cfe7058752126bc32d9121006bc70d9121106f710d89510d6bc6454921004ff7058752004bf7458452006bc64d9521024fe74d8552006bc63d9151006bd53d91510e6f71058652006f741d85520e6f65158652004fd7058752014fc7259721006bd50d9151024fc7458452004fd7058b510367f75597210c67f515972111ebf10d9121136bc10d9151
  | 1 => 0x9151036ee621895101cfc7358b51004ff70d8552006bf6458951024fe74586520067e50d952101cfc7359521006ed2058b5113ebc52d915111ebd31d91210c6f441d8552136bf75d915104eef5258b5104e7c65d4921136bf51d915107ebe76d915100cfc7058652036f4215865200cfc70d9521006bf6498951006bc73d9151034fc7558752024be76d9151005f77154951006bf64d4921006ef6294951106ef21d8951005f57194951006be30d915101cfe73597210c6f4615855211ebc10d91210c6f621d855200cfe7058452004ff7059521004fd7059721004fd705845201cfe73d8552136bc71d9151036ec62549510067f6554921136bd71d9151006ef725952111ebc72d9121136bd21d915100cfe70d9521116bc64d4921137b710d9151006bf7459521006bf60d91210e6f44158652015f671d492104f6c5254951006f74158652004fd705952104ef75158752006bd20d9121006f53158652006bf63d915101cfe7358452006bd50d912104cff7654921004fd74d8951004fd7459521014fd755845204ef77158752014fe76d855201cfc735972111ebf72d9121004ff7359521004ff73d85520c6ef2158b51126be52d9121024fe74d8951004fd7458752006bf645495111ebe21d9121006ef6298951024fc7458752005f571d492111ebe10d9121006bf30d9121004fd7458652024fc7458b51004fd73d8552006bd75d9121024fe7459521006f510d89510067d535972104f74515495104eec5258b5111ebe31d91210067d6519521006bf53d912113ebc53d915111ebf21d912111ebc51d912104cfd72d855211fac72d9121006f53158452006bc50d912103dde73995210067f659952113ebf50d915100cfe705952101cfe73d8951006bc7458452006be70d9151006bc65d912100cfc7059521024fc74d8552006bd70d9151136bf10d9151004ff73d8951006be53d915111faf72d9121006bc7459521006bd65d9121006bf75d912100cfc7058b51004fd7359721104ff7259521014fc76d492111fae21d9121015f671949510e6f710d952111ebd10d9121007b531d9121006bc641952100cfe7058652006bc30d9121006bc6498951006be30d9121006bc6459521034fc72d9521006be32d9151004fd7058652034ff7259721004fd7358652006bf63d91210067d50597210d6bc6454951006bc20d9151006bd73d9151004fd7358752106f71058752034fc7258652004ff7458b51006bc73d9121006be63d9151004fd745972111fb631d9121004fd70d9521006bc6418951006be50d915100cfc7058752004ff70d89510a6f631584520367c5259721004fd70d8951006bc63d9121136bd75d915107ebe75d91510e67d51d9521037e42154921024fe745845204ef451584520067d53d9521006be75d9121006bc72d9151005d
  | 2 => 0x1e330e8000107008237018010068a4802c0202029400a410b87c1614148000a003a80816110384c121a0e8200004120040004348a400020100404850001c14000280c6005010191a065084402040003002040106902000f0400a0000808000644045bc0b0601c425b42808000202044ee1b0d0ec160000000ee0a00030ca8a3781469610c1b80a0601d18c60b031286c0827844a6230b8040634000001c30098640600000042601011fa181c015f4715495101cfe7358752136bd31d915104ef75158452006bc64d8951004ff70d952113fb751d9151004fd70d85520376c5254921004fd7458b51004ff7458452006be20d912111ebe71d91211373e51d91510067c5459721004ff7058452006f510d952104eef7258b51005bf7458951004ff7058652006be60d9151006bd63d915113ebf52d9151004ff745972111fac21d9121014fc75d85520f6bc649495101cfc73d952104e7e6519521024fc7459521004ff73d9521006bc30d9151005f771549210a6f7105845200cfe705972100cfc70d8951006bf64949510c6f651d8552004fd74d8552006be63d9121006bf73d915104cfd71d8951006bd72d9151036f42158452014fd7258452136be51d9151014fe7259721034fe76d8951136be10d9151014fc71d9521034ff7158452006bf73d9121014fc7558b510c6f71059521136be21d915100cfc7059721006be65d9121004fd7358b51136bc51d9151006bd30d9121014fe76d4921136bf31d9151006bf70d9121006bc649952113ebf53d9151006bf30d915107dbc745895111ebd72d912101cfc73d895100cfe7058b510e4fe7619521006bc60d9151034fd725972111fb421d9121006bd73d9121036f77158652004ff7058b51014fe71d8951126bc52d9121005bd7498951136bf21d9151136be31d9151024fe7459721006f54158452006be73d9121024fe74d952107dbe74989510c6f661d8552006bd53d9121126bf20d912111ebd51d91210e67f51d9521004fd7359521136bd10d915111fb710d9121014fe7654921004ff745875213ebc50d
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5f655ce654840117b0f31ec89081a3d60774d952114e5a3a220b08a400a9e839d764484031d90e902c5a88022f61c30d912100c7a43a20b0ca4008bf845cd611480117b0f31ec8a88063d21d10587520061fba4a8b2e422ba3d859cf645440117d0e186c8a88022fe1d65d91210052ec18a8b2e4200aad820c3644840153d06286c89088eada0450d91211255741061b224226ab6810c3645444d1790dba2c4a88029b60850d95210047bc0ae8b2a4200a9d83083645444756d02186c890802a7e0d60d912100c7b436e2a924200a3e859cf644844f47d0a186c8a88122f21173595210245e422e6b08a4008bd87983644840156b02286c8908063e20173595210343e42ae8b0ea4008be87083645440917d0fba2ca908269d215105845204c3e42ae0b08a423ab6811c3644840117b0e29ec890803279cc64995210245f436e8b12a209c5c655ce654840117d0e29ec8908063d21d10584521255ac0eebb224200e8d320cb6454401968c9b8aa49089ead60470d91510045fc22e0b2a42008be870cb64544078b8e6a9acb9081a3d21d315845200e7438240b16a200a3d8508364544011df0eb10c4a88022fe1d63d91511255a43263b224200a3d850c364544030f90ea82cb9088eada0775d91211255ac08e1b2242008bd87083645444d56d02196c8a88132d1d141584520045ec38a1b224200cb474dc5654840196883ba6c2a908eada0473d91210245f43ee8b08a400ab5810c364484010ff0ab82ca90802a760c50d91210054ec1ccbb22420fa3e859cf645440156b02106c8a8892ad60473d91210347a43a62b0ca400a7581143654840917908b82ca908030f5d475d91210051ec2865b22a2008fb805cd6548401968c9b8aa4a8802a7a0c20d91510043fc3aca32a4226ab681083645444f47d0a106c8a88972d9d910d912111c5e436e8b2a420387f8754f65484031e90e882ca908022fe1d63d912114e5a3a220b2a42008bf87583644840153b073aec8908022fe1173595210045ec3ccbb22420687c8754d65c840157300196c8a8802ab60830d91510055741061b22a200aad82143644845747b0b31ec8a88022fa1c74595211255a43221b224224ea820483644840d0fd0f2a2cb908022fa1c64589510065a20ae8b0ca400a3c85583644840117d0e286c89081a3d21d41584521465b3b221b22a200a3e850c3644840117b0f306c8a8893a30c932d91210045f43ec8b12a2248be871d1611484fc3ea729ec8a88122f21170584521355b408e1b22a227ab486443645444f47d0a196c8a88022f61c30d91510051ec2861b2242008df835c1654840157500196c8a88028fa1663d91211561eba8c9312a2038dc835c16548401938c8b9cca90802ad60432d91510045ec3865b22a2008bf845c1611480147f0ab06c890892aba0850d9121
  | 1 => 0x23208560c280018004c6c0e000c461cc8000000a0000411166e0000160400b800384a0c020a020c1406203e0000065404386c0202201406040616061ac6580e621806006e001200a9c83583644840153d0732ec8908029760c50d95210055ac0861b22a200a3d8598f644840147b0b39ec89080a3da0774d952113f0e29aa7b22a2048be86dd1654840117d0e186c8908032d19171949510045fc3ac1b22a200
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1a893260032d9151
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0xb09
  | 6 => 0x3
  | 7 => 0xb0c
  | 8 => 0xb0d
  | 9 => 0x6
  | 10 => 0x1549
  | 11 => 0x154d
  | 12 => 0x154c
  | 13 => 0xbc9
  | 14 => 0xbcc
  | 15 => 0xbcd
  | 16 => 0x19c9
  | 17 => 0x19cd
  | 18 => 0x19cc
  | 19 => 0x449
  | 20 => 0x44a
  | 21 => 0x44c
  | 22 => 0x44d
  | 23 => 0xd49
  | 24 => 0xd4a
  | 25 => 0xd4c
  | 26 => 0xd4d
  | 27 => 0x1649
  | 28 => 0x164a
  | 29 => 0x164c
  | 30 => 0x164d
  | 31 => 0x1a09
  | 32 => 0x1a0a
  | 33 => 0x1a0c
  | 34 => 0x1a0d
  | 35 => 0x160a
  | 36 => 0x148b
  | 37 => 0x40a
  | 38 => 0x1a8a
  | 39 => 0x148e
  | 40 => 0x74a
  | 41 => 0x94d
  | 42 => 0x74d52
  | 43 => 0x1a8ed2
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 762
  | 6 => 439
  | 5 => 151
  | 4 => 1
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
  | 7 => 2*((h/268+packedAt gbK7 (28194+(h % 268)*10) 10) % 762)
  | 6 => 2*((h/153+packedAt gbK6 (21072+(h % 153)*9) 9) % 439)
  | 5 => 2*((h/71+packedAt gbK5 (8909+(h % 71)*8) 8) % 151)
  | 4 => 2*((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe3ffe1c3c3fc7e00e380ffffc83047c33c0ff
  | 1 => 0x1fc701e03fc3f8ffffc00e07010c3bb0ccfccc
  | 2 => 0x1ff801ffc003ff000ffff007fe70c3c30f0f0f
  | 3 => 0xe00001fffffc00000ffffff80380fc03f00ff0
  | 4 => 0x1fffffffffff000000003ff0003fff000
  | 5 => 0xfffffe00000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x22090c0414054121220802512801001411c055
  | 1 => 0xe4214600c40c848ee406432180419b0445ccc
  | 2 => 0x149020a8400292024492a004d03042c10e050a
  | 3 => 0x40004152aaa80004892549a00380ac02e00aa0
  | 4 => 0x899f33332497000180c063db0003bba000
  | 5 => 0x9924f002022000180006010083eef768000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_39531
namespace PEqualNP.Outside.L_meta_39531
open PEqualNP.Outside.L_meta_39531.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs0_4_384 : Interval s0Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 414 := (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384)))
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
theorem bs0_5_576 : Interval s0Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 616 := (concat (concat bs0_5_0 (concat bs0_5_96 bs0_5_192)) (concat (concat bs0_5_288 bs0_5_384) (concat bs0_5_480 bs0_5_576)))
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 2 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 22 := bs3_3_0
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
theorem bs3_4_288 : Interval s3Atlas 4 288 91 := block_range (n:=91) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 379 := (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 bs3_4_288))
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
theorem bs3_5_576 : Interval s3Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 586 := (concat (concat bs3_5_0 (concat bs3_5_96 bs3_5_192)) (concat (concat bs3_5_288 bs3_5_384) (concat bs3_5_480 bs3_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 26 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 144 := (concat bs4_3_0 bs4_3_96)
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
theorem bs4_4_768 : Interval s4Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 883 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384))) (concat (concat bs4_4_480 bs4_4_576) (concat bs4_4_672 (concat bs4_4_768 bs4_4_864))))
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
theorem bs4_5_768 : Interval s4Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 802 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 7 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 5 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 55 := block_range (n:=55) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 151 := (concat bgb_5_0 bgb_5_96)
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
theorem bgb_6_384 : Interval gbAtlas 6 384 55 := block_range (n:=55) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 439 := (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384)))
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
theorem bgb_7_672 : Interval gbAtlas 7 672 90 := block_range (n:=90) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 762 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672)))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 36, 52),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 36, 38),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0fefefeeafeecfaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124266 * 2 ^ 32 + 4276943520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_39531.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[5,6]⟩,⟨.and,[4,7]⟩,⟨.or,[4,7]⟩,⟨.and,[1,9]⟩,⟨.or,[3,8]⟩,⟨.and,[2,11]⟩,⟨.or,[0,12]⟩,⟨.or,[5,6]⟩,⟨.and,[13,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276943520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276943520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_39531

open PEqualNP.Outside.L_meta_39531 in
theorem PEqualNP.Outside.L_meta_39531 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276943520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276943520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
