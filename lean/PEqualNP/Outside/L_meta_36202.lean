import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36202.Model
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


end PEqualNP.Outside.L_meta_36202.Model

namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
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

def SBf (j : Nat) : Nat := [5, 6, 8, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36202

namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 2 => 0xffffffff81fffffc0fc07ffffff81fff98ff8f
  | 3 => 0xfff81ffffffffffff0007ff03fffffffe0e3ff
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 2 => 0xa85108890c9122940552251992c90a54983685
  | 3 => 0x10a255122122852950284aa4251654a960c15a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831dd03e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1f6f800
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000fcccf0c0fc00f000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36202
namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40c092002b2984051c00203bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x100c0008008ea98852c525065ca5205554430
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s1K4 (208+((h/4+packedAt s1K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s1K3 (112+((h/1+packedAt s1K3 (108+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36202
namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea9441ee42883da85107bcca20f6194417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107b90820f6a1041ef32083d864105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f731043e862085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210b5a84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997bd0b32f6216657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997b90932f6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32bf29065ef420cbd8841977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83be43d077887a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41dfa1c83bd43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941f7a92836f52506f8a4a0fb14941b629283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef50c41bf29083ee52106dca420df54841f6a90836d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31f7296636e52cc6faa598fb54b31b6a96637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf29463ee528c6dca518df54a31f6a94636d528c6fca318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa98863d5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21f721243ed42487de6490fb0c921fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf29681ee52d02dca5a05f54b40f6a96816d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x3073a2822c300001720004b4000f00f84a8001a031000000000128688a70875328f10b24f0c69f5288fb4dc33538157524118e61ba06e5e9050cc0000000000039a0000005e372419048981320013a9f7430760000002cc328000002a48ec0006f4fc244d980048284d02a3300a844da9094c8400001b40729813699e11e750c114c1bc9080e2882a21e5272503fc628551ea30c08099a0414a5589003e402a583b0f83e46240002800039000000186698530000000000018d12e49d3900000019cbe04811670800000000674a280007808d01a4a18a09c001670843585d2170d20448c9f52e8888d72301589b03b9c73e22cc15984508284f98700d64c8249c61dc32c309bb1be00000008000000ae975000784000894ac0000000052e000001ab2021291c0002b2000000361260012690e0004510a00000000000173000228648160000013e1ed0ae4a4cc16a000000ed0000160000003d4b67243e9ce0e64c07280d09a4e0c022100078c000000000000018f1ba0003d90f2140008b915000268191b02787751906515e808698ec36e964db04f000900b61903d63c54280043c000d783b000000eba1d000000e08000009ac0f09b2b0798209530006b0000f44f6978000004ca3080007a4a6114ad14f47a16c5480019c28c0d00000020400000000000002450008bcf20000625a0001c31b258092000388000b806420a44c462490307ec168c74b44989586047c0006080000092d47a772fc1b12226315c521338030080600c010900000005004060040600003000000000a01401000060240000800028020080000000004000040b0080000800000170380003400014000200100059054000040b0180100000000040081e04000034000080f004010000c00c0902404008000100800c01010010001700001004070080500c0801c00000060640f0400600c0e00c0104c0e0000001800000000180a00807010020000a0080104c0304c020000f01c0000c060201000c000000400c1f00c0c0080200404008040000000c000081500803004000300201810000110000100c0205c050b40a00000038000240801001000030080202000000000201205c0f018030100d0100401c070200200000040270000603012020050580000004002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf29087ee5210edca421df54843f6a90876d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485e
  | 3 => 0x24821a1b490800520288201e04f43e4001bc4c27f4df2860005409d17f4867f09c8bd3a69bc0019f04a000001e7418000001041ea510b49a400097cb887416e3fc2aa064ba0bcd38004d01601600021611d00000000000d40003b2684000000003e803a31000000000e1472340001314464fc0011c000000b08155149d1291fa3360c0af8d84567d0121812369a4a599c0a482d4984314895400165000000ef89c0266f40521923e0001f9de3a0a44bd8880000014a00020641c001f61f8198000000180040010810c2105e0000001e07922a2ee318a50d71761640784b25c89c55928000011408000a6000f7800000000001a348c9d80024c000644be97929aa609618b3b67440016e244794000003707e4bb0000000000018c0000000019302e1111023f516000cb0003245254a8002c495ce90a0220000000720322082e09f000a1d038004364f875163230000b79d637e3ac000004c47b8e78000540000000016c838002892d6898f414123c48ca10cf0c40006a800000000ca0000008d123a780045780e8d40004f400003000970929f811c9cd1b9020e22c0281a50b4214ee0e03348b47b8e306661400258000000cb9ff0000e0642100445b4001641b650d2a20d45c7c014a822240000020f0003a0000003647209a23a0ea0000011d25e6a47f01f2aa7009da2517e998a01540ba72c3f09e0247886e0004589a8c3880000050ad8960008714028d4523bc7e9990422c84a8da3d287c288ed46a3984911a1889e4048b504c0b8c705406a3d8351350ac2e4c1a360007b10a87f000000002834e28685689d17c7280017826c2e08880628e001470002b84dc480b10002a000000000000e281b1061b8d68004fe1a0000d24108908605f5183a4ea8f301c5182703a0206c4468b432a344538000008481a0e23541
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x53c823d6414f20cb55342c832d5410b20cb55232c82ac644cb20cb55132c832d54c8720ab19121c832d5448720cb58a548823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5490a20cb951428832e54cca20ab590328832e540ca20cb95221882ad6408620cb95021882ad64c8220cb953208826d629512097d8d544825c63551209dd85544827461551208fd91534823c6454d209bd8953482776154d209d185534823e6414d208f590534826e65d09209b994424832d54109209b996324826c654c920ab191324823e64145208f590514826e65c8520ab19121482ae64881209b98b540825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f590530826e6214c209d98453082756114c208f992520823d64948209b596420826f6550820cb151420826d65cc8209b59432082ad640c8208fd91510823c64544209b59621082ad64084208f992500823d6494020ab593200826f65480209ed95200826f62553109b18954c426e62153109b58854c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c4354534c7109b98b548426d62d52109b98a548426d62952108fd91538423c6454e109bd89538426c6254e108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f992528423d6494a10d5d4c318423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c5244276658c510d514e3144274654c510d514d314435453841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043546154c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d597310435553cc4109d5943104355530c410d554f100427965840109dd9510042d46344010d554d100427b6544010
  | 1 => 0xc63d64149318f990504c63d64141319b988504c66d62141319bd89540c66c62550319b988540c66d62150319e980540c67960150318f992530c63d6494c318fd91520c63c64548318f992510c63d6494431b558e310c65f654c4319dd95310c6d7654c431d5d95310c6d4604c4318fd91500c63c64540319bd89500c66c6254031d54c5500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c872c5450b21ab59032c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f592538872f5410a21ab191328863f64542218f191508863e64951219bd89544863e6515121cb588544863e6494d218f592534866d6294d218fd91534863c6454d219ed8153486786054d219b996424872c54909219b195424872c54509219b997324872c54cc9219b99432486ad640c921cb150324872c54885218f596540872c62550218f990540866e62150218f993530863d64d4c219b98b530863e6414c218f590530867a6014c219e580530866d65d0821cb553420866d6510821cb550420866d658c821cb552320866f654c821ab191320872d544c821cb553210866f6548421ab191210872d54484219dd9521086ac6250f40cbd0d52d032d4354b40cb54a42d032d5210b40cb54b41d02ac6250740cb54941d02ad6210e40cb90e529032c4394a40cb94b429032e5250a40cb94a41902ad6210640cb94841902ad62d0240cb94b409026e6214d409b588535023e65d0d40ab189435023e65109409b988515026d62145408f99741502ac6250540ab98a405026f6254c409b189531023d6590c40ab588431023f65508409bd89511026c62544408f59641102ad6210440ab58b401023f65500409ed95401026f62553309b18954cc26e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62947309b58a51cc26e62d52309b58b548c26e62952309b58a548c23e6494a308f592528c23f64546308f191518c26f62546309b189518c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c32f54d4930cb153524c32f5414930cb150524c33754d4530cd153514c36752d4530d914b514c3375414530cd150514c3675214530d9148514c25e65cc530d5147314c354514c530d5146304c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c25d658c430d5546310c355510c430d5547300c25f654c030b5185300c355514c0309ed95300c32c62553208f99353c823d64d4f209d98753c827561d4f208f99
  | 2 => 0x683c9301d1d07dca10003440004204d1ae104d403b44c5240d06a3ae6e0a50db0980b42a9ed15820caa1c12146d00000a21000061115000000808493646f8b58004000000011b0000009686d3dc8307e92e07a000791ba240534069222f4514f605900e440211762be71400202192538000a30b8554a08a91e00380007d2ee00079a1813e00000000000000000dd3b07807690e3a02b4220380fc5c42580039a000000940660006192b3863a8e88003128500000042e63cea000320001068000006f0230001988645903f17c2582380019a3e4659752060001505b16619057205148000390180000008008070000001004058010140e00000048090040300824078050088e0001201000004050140000c0000400000050000000807000291201800400014140100000008068020000e0040608c020101800c0607c01000080240000012000090302b018180180000c06094000400a000020340406c0a00000008010040101405028000000a00c0c0340200001010000140300c010540f0140e0200000001004070143e0500003010038000c40a008480000003404000070100100409008000280a148110481300c02030000bc000200800000000020081102401028020500200e6f62547439b18951d0e6e62943439b58a50d0e6e62946439b58a5190e6f62542439b1895090f2e43149438fd954310eac6250c4397d954310f2f4354843cb50d5210eac6250f42ab5884390a3e65d0d42ab1894350a3d6590c42ab5884310aad64908428fd954210a6f6550842abd954210b2f6550842ab18d4210b2d5350842ab1854210aaf6050842cb5095110b2d42940429d98754cca7561d5332cbd5042cca3e64947328f59251cca3f64543328f19150cca7661152329d584548cb2c5450a328fd91518ca3c64546328f992508ca3d64942328f992544ca6f62551328f994544cb2d62151329b996424cb2c54909329b195424cb2c5450932cb153324ca3d6595032cb189540ca3e64150329b988540ca6d65d0832cb553420ca6d6510832cb550420cb2d548c83297d95320ca6f654c832ab191320cb2d544c8329bd8953d066c6254f41ab58843d066e62943419b58a50d066e6294e419b58a53906ac6250e419bd89509066c62542418f99443506ad6210d41cb90c525072c43149418f997425072c52d0941cb149425072c52905418fd9543106ac6250c41cbd0d521072d43548418f596421072d5290841cb548421072d52d04418fd9541106ac6250441cb549411067765504419b98b54cc66d62d53319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b319b98b548c66d62d52319b988548c66d6215231cb952528c72d5494a31cb951528c72d5454a319bd89544c66c62551319ed81544c67860551319b988544c66d62151318f990524
  | 3 => 0x18a3ec7a4821c818062cc40300006787e0110a834872186372350b61ad266340c09800de140ac0910e24581280500439c4410b13872caba09406000fd0002c256c0000000025ca01390f6000700004241d0d2a24000394000170ce494988451362885c806000000001cf0580dc608bd0000d02189d03e804b50cf1de1d4049ca17e080981c435261ccd8002fa54cca8600468286b0bb2b40004480036a000fa105114520d78ce0001890b000000874b102b22e8205d02112018cdb01618e320d191930a21d0f8270006f4bc87c2a4200361910001447d0bc0806b80021100060c001fc0907e0df8002344600000000000086000426490d392a1324700600b332000fc8da3d6370810f82122787106800014c7f00023a000000de20e05027963242354002203d07ccb21c0000318d598421a2a06c83c2e41b8a183200267c3491f11a3b0bf15d3be0000c0571a624cf89dc1cc578f79e216a1e41494c3480004a800000000ee8000005643b9940941c08793509c4f0002210003d45b99331a7f89408f2f804cb30a52887680c9ac3766dc391650f42aced93b2a28182e946296310cb07f408078e10223aa854b71370b07a80016729e16905885398540f31c74386303b16d3e0048898b614c8941b12f0ac88c399741044e0140523fe070b40002286cc130e326c0c4308001fe81cec800224000ae1921be7840d898330738e986b0cc3d0e920e000684d00af072000508a7434758cd0ee2d26c02f13405c5fc4d0f71247c8f18ca020580020fb25284080000118778000000000002f97300067400000304000458000483acf218e27451c001e727a8883280027e7f4000f11627184710600065cbc0002f62a80016f3ea7ec748782583845c1c923c218040000008788888100079468a1b18a6a8079a62e02c0918151ec4f85a0002ac360ce13224e0001d1b106a2801f02f00
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1602689e01c60000030000201a1884a000050040000028e9040000c1041c18c6a9a8421524715095110a9338ea821665495c45450a32858ecaa2641950d7315142c868739ea8214430b5d8540c921858ecaa26410c2c7655121086163b2a8996410b1d9544872085aed2a0651042d769502188216bb4a990441431cd5410920a48e2aa0849050d731514208292b88a8a1041151d95344010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 20
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20202+((h/222+packedAt s2K5 (17982+(h % 222)*10) 10) % 880)*11) 11
  | 4 => packedAt s2K4 (22768+((h/183+packedAt s2K4 (20938+(h % 183)*10) 10) % 662)*11) 11
  | 3 => packedAt s2K3 (1016+((h/6+packedAt s2K3 (980+(h % 6)*6) 6) % 40)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffc1fffffff03fe0fffffc1fffffc8ff1ff
  | 1 => 0xf83fffe07f0ffffc1ff0f83ffe1c0fff723e4f
  | 3 => 0xffc0ffff800fc3ffe000ffc3ffe00f0383cf8c
  | 4 => 0xfffffff003ffffff0003fffff003fc0ff0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x802044412020000a40128444025214804d095
  | 1 => 0x128c48832414a12c0a90522992084ab132264a
  | 3 => 0xa196d1490ea9275561889ea2f540ac1b834b8c
  | 4 => 0x8528a21248818a9a532a04032992c022d80d60
  | 5 => 0xc630c39c70ce33e39dcce730310308c3efb000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888eeeeaa88eeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36202
namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8002840830007010600cdf32ee32dd32ed32cd32be41bc41bf40bd40
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xeac26000004840a6a9c658f544cb18a899634ca41c6990838d32d031a64a04d14540
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x161000a1987544ca0f654ca418319532503053214540
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (156+((h/3+packedAt s3K4 (144+(h % 3)*4) 4) % 14)*5) 5
  | 3 => packedAt s3K3 (224+((h/2+packedAt s3K3 (216+(h % 2)*4) 4) % 13)*4) 4
  | 2 => packedAt s3K2 (156+((h/1+packedAt s3K2 (152+(h % 1)*4) 4) % 12)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe0ffffffffffff81fe0ff07ffffffffe463fff
  | 1 => 0xff07fe07e0fc1ffe1ff0ff87e0f0783fb9ce93
  | 2 => 0xfff83ff800ffe1ffe000fff8ff007fc1c1f31c
  | 4 => 0x3fffff0001ffffff0000ffff8001fe03e0
  | 5 => 0xffffc000000001ffffffffff00000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x28000241002000004401200901140a10021425
  | 1 => 0x425184324548a8960a50528268a150ac98ca92
  | 2 => 0x8432a890d6928baaa1489b50ba826585c16318
  | 4 => 0x16a53124941acdcd336a0a40dccb4109ec03c0
  | 5 => 0x18c621c718e31171dd8cec64100c063177bc00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8aaaaa8a8eeeee8e8aaaaa8a8eeeee8e8aaaaa8a8eeeee8e8aaaaa8a8eeeee8e8aaaaa8a8eeeee8e8aaaaa8a8eeeee8e8aaaaa8a8eeeee8e8aaaaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36202
namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3987d94730bb28e617d51cc3eaa3985d54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa418778c830ee190617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c21f631843ea63087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e882087d8c410fa98821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x65190aeca3215f54642faa8c85755190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631fb20c63f5418c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7bc8698f750d31bfa92637c524c7bc6498f70c931fb20a63f5414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621fba0c43f441887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fba0a43f441487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x22122200027c48e2c4e78003567d84727900051cfe1840006b927a48000000178b80000014504d00058c4b0003940011f975214000000000007ec55209000089208000885582ea2c34406c0793c506a30e01540a24a07e1d227a4dd2f04a0009e0c81ba3f09e885800188910da87147a5550010426823cae0892900007d00b43a47cbd132000298b40000427a4001a45109a8b80783b64b4cf16b1b67200000c40a455038002f8000b600049221c000730005a4561ef49c0b4000f100010d40a544da388d912b4ee0a4f82751040006aa5b3d86cd2e8672eca24000b50003e4000631ba97d1a8005047303814c0001851b11e1500d479857148a4d4301d2f6000831213c050d008b9410000210550466dceb00032e000000000b64fc00017000050d09640ac26415a803ce3a01b8000063f497800000249251f400007c001ff08a2f868000000654099af0004c4d02581f03640018300078c000ed43c6f44d27f2580013789f4aa5c8b68a71de30d058000002000015f4523303f02c0e88352e0844b41b10604b50e01cf427142a000c91f52b0349471d34460005980000052cdd80018c1ac8a1a54400784f1743786e0001f21200a83d80616c1d9232513bc1dd0e1e62763201d1e215699cad9864cc6a8ca0000b8000028000928949c9cb180000548d40008ecee03906600134a7b0be0003e9a83b24c0aca951ac45812a37478000270001be194f702e30a6c0bb8521608e84ea56000a101c0f43c800046800000000c5000484624ed00002c030f4010180100c010000a000040280302814010000800204c28004000000100c0101404014020000000001000000540003c4f000080100002c0a0380400408010020a4050000100c000080600016018100140c02017008080400800c02000070200003801018020480405000024040180100000030160080400417004080040903c040100301c0401c080400103803000020240300400000040081700c09004030180e04803008140001102000060100340401405004020000003c0d00c03030010140e00002010250ec020100a010020180c000110c8050001508c0200422000040580902411014000040c01c010181301818000010200904c0300003014030140500800054010040200c010000804c02bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf28887f65110eeca221df54443faa8887755110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c85f
  | 3 => 0x671081cc774000360000f4000e43be25c002032746b4d39b12a00253206a09e2bc7809500022c000000bc060000462f0104f98f644ca591080043449c000540008600006825435d0903c1ee13002214174400ce05821a64c181f92c08c8241072aea486394f0763c8b29b949a32481a8545670cd49c23ae8cc418004e6000000ca18a4f8001fa42e8e000000462000409ed2de525360003320400421628c2281922d48a724b724b52e578a71132fc0000011b24c4e12c8502844444e2020e428d4693300014d020dc2948381f8192804485d99a0380053000020a000a20912f2384c69192a42b94a23426c5a871a2a3109c0b315d15a45c760002188bcb38002fa335290b7000930b99231d44742c92951e9f92ba6325c0007f80d00062c0006e3c2a2cfb9c41407c4050bc2c46fc432111b0840b88022fe1883c9d05226040018e1262d00889b4726011121f39a4813400038e3041f0d137c659201fd000308748001300000a8e733a1f0e2800000000000004860000021341454467a243a89d09211014a0008086f000438db1353d463ce30bd0009401215a304865358314e44882391c3ca1fce70661b42fc878d31286985086404c94c3aa0610a000a28de4ec1807d85a0f4038b08f500050537000368494d614d4602303686944e8f814040234394c8a2843628930a0f23032d3e8fe1d68b8a98123b067c591fe4c4380e881a0000581a00000061c139a3520660e0800336754100ee3d66313290
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x153c823e6414f208f59053c82766114f209d58453c823e64947208f59251c825e63947209758e51c825e63d52209758f548827761552209d185548823e64d4e208f593538823e6494e208f59253882766194e209d586538823f64546208f191518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c715053483596014d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d91472148358538c1209e195304825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d584530827a6014c20cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d9547200835953880209bd95200836551480209ed95200835953480209798c54c425d63153108fd9153c423c6454f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798f548425d63d52108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10b558c41842b4644c610ad993218423e64951109dd85544423e65151108f992534423d6494d109d586534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524427761549109d996214433454885109d19521443345448510cd152104425e63d50109758f540426e62d50109b58b540423d6595010cd185540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c755253043566194c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109d984520433554d0410d954b41042756510410b558c410436552104109d5963104335548c410d954a31042b4644c410cd5513104356534c410d9549310427565c8410ad993210436552c84109d59421043655208410d954b100427965840109dd9510042b46444010d9549100427b6544010
  | 1 => 0x63f6550441c754d41106776550441d554d411067a60d53319e58354cc63f6454b318f19152cc69d640cb31b658032cc63e64943318f59250cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508c63e64951318f994544c71d6315131cd584544c71c5490d3197195434c71c548c931a7590324c71c540c931b5984324c6d9600c931cd152414c79643905319d195414c79543505318f596540c63e64150319798c540c6766115031c7553310c735548c43197d95310c71d544c4319dd95310c735544c4318f99353c863d64d4f218f99053c863d6414f219e98053c86796014f219798f548865d63d5221cd185548865e63152219758c548863e64d4e218f593538871e5494e21c755253887566194e21c7951538871d5454e218f990538863d6414e21cd55341886d56310621cd55231886b4644c621cd5513188756534c621ad993218865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534867665d0521b558c4148674654c521ad19131486e4624c521ad993214863e64141218f590504865e63141219758c504867661d50219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219d984530867a6014c219e580530863e64948218f592520863e64944218f592510865e63944219758e510866f65484219dd95210863f64540218f19150086b56110f409d98652d02756194b40a718d42d02766194e409d58653903566194e40d5586539031e53d0e40c794d439031e5390a40ad986429031e5310a40c794e419029d6310640c794c419031e53d02408f99443502b56110d408f997425029c63509409798c515025d6314540d598c51503556314540cd90c51503344314540cdd08515033542145408f997415033451d0540cd145415029e6390140cd146405023f6550c4097d8d521025c63548408f59642102b661908408f596411029d63104408fd9540102b461500409ed95401027661d53309d58754cc31c63553309d98454cc2756115330c755343cc2d56110f30a719132cc3365494730cd55251cc3365454730cd55151cc31d54cc730a719131cc31d544c730d594531cc31e548ca30c7950328c2d9600ca30c7953308c26f62551309b189544c27761551309d185544c25e65d0d30b5584434c23e64149308f590524c27661149309d584524c25e65cc930a7191324c23e64145308f590514c29c644c530b6181314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c25d658c830b6580320c23f64544308f191510c23e64940308f592500c25f654c0309ed95300c27661d53209d58754c825f63553209718d54c823f6454f208f19
  | 2 => 0x92a0dc000af98e26e00000139000604241fe416298000002a800006000000000f7000000000278003f626c000ad0001cc000e026821c001a9000528b99a4060000000000008503b80037e000000000000c89700007c000000aa1603b800000000000de9a2000000000000003380c9d31f4000001500002a0000633cc000000000000000018d2c2140e080004a4cc000000120200000000019486800000738001d400000000000000000000af3e23a0e01681301340004c3e00005d8000fa4b4000001c20008e0003e4000000e50860000004e2cc46c001a60e00010380000000091047180000000000002ac8100002800000000000754858001663544e8000003ec001550000000000000000200c0200800a00400005006000000010020000680500600c09800000004010040000040700000000c03805000000018000040000100200000406802000000008000000000000200c01c00000000000008000000000000101e000008000020000080100a0000280100e00000803004000010010020100100200400001008002000000040040100180a00000800001000008028070000080201100601c0080000000800805000000010020000040000100001c0000600400001801000000000030000000600000a00401000000008008020040000000100400c028000040000580000001000001002004008000000000000d00400e766194b439d58652d0e7761543439d18550d0e3f6550c4397d954310f374354443d590d5110f354354443d550d5110e5e63943429758e50d0ab56110e429798e5190a5d6394642d598e5190b556394642cd90e5190b344394642cdd0a5190a766114d429d5845350b566114d42d55845350a3e65d0d42c714f4350b1c5350d42c714e4250ab661909428f5964310ab56110c428fd954210a9c63508429bd954210a7761540429d1855010a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cad56110e328f992518ca3d64946328fd91508ca3c64542329dd85508ca7461542328f992544ca5f63551328f994544cb1c548c9329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cad56110c3297d95320ca9c644c8329bd95320cb365494432cd552510cb365454432cd551510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb5b4354032d610d500cb5b3254032d64c9500ca5f6354b419718d52d06b66190b419798e50d065d6394341ad584439069c6350a418f99743506b661909418f994425063d6590c41c754e431071d5310c41ad584431071d53d08418fd95421069c6350841c754d421071d53d0441d554e411
  | 3 => 0x16000000000001f5434270ba059000168000003a27dc821230000002b20621207800000148000fb00000025c000000004f4fe15e000224719ff01c360840000000480008b00000000000000000000000000000001727626800000000000000002f2000000003083680020a0f4714000683b00286200042a5a400000000000000000006d4000670000000000037629c9615d26c080db8d93361141c000000000000002fe7649880030c00008180330774001270000005280042c3f40008331862c008940d60006e8001e8000b02133b80c40008e000428f52190000000019a00065000055000258300b200056c50000108748390000000000000000000000000000000fa01f3ac000002171ec4580d8000005ac94800000348760000004f04080000000090a100000005f0001260000d00020a0000000000083c00000226000b50000003c8688000007880e99d33275c000001de5e8d596e218334ae1eb0d230c5b800000398001de000000001a52e479c00011000000e780013c000000000002f4000000a6538ca985132000a180016c000000000e843c000f3000000178001ae000db0000006e40020c408000288002d864c00034074128002111bc824001001740d4001871467808c91a0000000010122e0001f8710006b40000000000000000358000a48000003c46500000008833000000000890b80000004fa121ac00062800000000478f83d2000a41e5000000001c94304c80019f0000185a0850002540000f000000f20ff2f0000932010000007f01c4041008c17e0007203a8003785907a800000000001d0000058258cf0000005894c3068380000028e388000000004bc00024000318d714622a0a08f0000000009f1402ec1b42a1e3178308ab06a1b8350b38000c4000000003540009405b0d86e0929c600043801000000000000570000000000005a00000037000000000d0000000000000000840000000a00000000000000000e40000000000000008d040bf00053c000000001f86d8391ee684d8800000728ab9970c26a0d3807000124a1000000548f6000374000c400000000000000000000000000005449597d0c8450f40030005dc000b9076000000002b4710001030002d449000000000000000000001500028200074800114000000000f80001e19c12000048846056000df00018e3ac000003f20000000035e4c00000031e784001fd3401488305d3da3c000000000534000002f800000000000000d8079000108000000002847c8cc0000001e800000000000001f8000e3826248644001da082708ac00d04e218b69b4304648fd1cd000000221f80de62864962110000b8815000000570000b85c00000000000102800000000001350002084611f000000000000f6000001533980009c000000000b293a0f0658881b231239cbd
  | 4 => 0xb00000000011a00054800000000000000000ccc800b00000083800190000cf0001da514000000000000005f41a37c699593664447517506c72c148a22de000000000080000005e23a000608000005100013f0fe80c001df3b67bce19f30000b80000015804d0000000058c000000000604000024032c000760000000000029600000000346000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x28240550000030000718b3800014c05565d10120002006093401033c000010000209455c45350d42c28a730c84a15157118d540caa8b8886a8065461d1325403292ae730c84a0e1563584544c60ebb0a81926386151600c931a2ae630aa910c3476551318868ab8ca6a1c818594e6190a40a28e6a10a2a051573145415030b318a320281455c46355330838ecaa2639861a54580328c28ab98c2aa0219158d5210410868ecaa26208624645493104313322a590821891915244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xa60008158714e61909428158794e6190a40815861cd42145408158798c5190140
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
  | 4 => packedAt s4K4 (22451+((h/179+packedAt s4K4 (20482+(h % 179)*11) 11) % 1040)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x87fff83f0ffffe0f0fff87fe1c0ffffc78f27f
  | 1 => 0xf83fffc00ffe3ff00f87f8ffe00fe0fe473c73
  | 2 => 0xffc0fffff07fc3fff007ff0ffff0ff0387cf9c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa1040888121400030289011404412c50185225
  | 1 => 0x128a9106a52862708542c8ab20aa42aa432c52
  | 2 => 0x922212014004941004920249209208858498
  | 3 => 0x552cc4a4880cab29a9d0408d92cc0433680b60
  | 5 => 0x66308738ce7133cece6764c1030818c3f6f000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36202
namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x21005402c001c21840014a43430b9904a91050c986a8000c9a32058f0e3a04f9c00ac492002d6a51444400006c027003ca0300e2080143001403cb201ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3b3c54004e45006e00233d252e0c140000421b002a004a0000002f082853650026095d40000004744407580005481d0034510000000031005c4600366a4f1600005200000000293227570a181c0006001f39006c5e5600006360240070384b0049200000192b713f3e553a730068671a72000d00030002005b13112c336b59354317473700001e010b0064006d4c0030216100626f5010125f0f0e00004d000000152200002d69415a66000002800003808082010000048a858105000081808302020000820382838482018180030300025b94b43b6a96877651d0eeaa3a1cf55242bb28c85755190abea6a15714d42cfa9a859c5350b5ea4a14f95042bb28885755110b5a85994f952329eaa46576518caeaa3194f950329eaa065ad420caeca2195d54432bd2806579500cadca420db54841daa08833e548c67aa918db94a31b6a94633e54c867aa990eb50b21baa9443b7428876a8510d7d4d21ae29a43ad42487aea690f514d21f3a9243b742487cc8490ed50921f2a1243a542487ce6490f90c9219f2a0433d54086eca210d794e40aea9c817751502e8a2a05794c40aea98816e52102daa4205d94440baa88819f42cc33a85987588730ea90e615d538c27ea8984f15130b7a92616c524c2eea2985d14530cfaa2619c544c39ea4987314930cfa12619d424c3aea2987514530eb10a61d5214c3b6a0985794c309f2a6413d54c835a85905d94720baa8e41e521c82bca7105754e20ec98441ad42483ca4290764c1209f2a0413d54082bca6105754c20bb288417551082bca7085754e109faa2213c544427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x225105a4020482a987001ae31a008b04a0e00a7a60002946000006c9509510cb294254032c9549411070c5350921a959242486c46350921e1d8d42487846350921e1d4d42487845350921a959032486e1600c9219958851503854248730c3150524c21c6550930d1148514c2546548530e1509214c3254254720c955121c8389424c120f0485304822d6215110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x180500a0cebb1a8490c8676d4d42486823aa8490a61811954248530
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 170)*8) 8
  | 3 => packedAt s5K3 (952+((h/8+packedAt s5K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffff07c3ffff070f0fffffc381fffe07f27f
  | 1 => 0xf07e1ff803fe1ff80ff1c3c1fc01fc3f394c73
  | 2 => 0xff801ffffc3fe1fff001fc01fffe3fc1c18f9c
  | 3 => 0x1fffffc001fffffe0001ffffc001fe0fe0
  | 4 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x12080110040400010102044480884508021225
  | 1 => 0x25153221a99931388690e2896414a8b5194c52
  | 2 => 0x41255442a0a1134a90816a1069243285418498
  | 3 => 0xa588895020c44952b24002592590118ae0b60
  | 4 => 0x8c6110e6333199e6ccc9b33820602221f5e000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8feaaf8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36202
namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12800f028d223179d00e000000d4d1e000100956858801e045395ca53003e183b06e21a36366552458885bb0601d322a0022d28949006640b004660e172639e804e18081010638000120c4800e087012640180017fd5005fe54017f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803fe3200ff4c803fc3201ffd4401fe51007f54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842000ffd9510005feca880037f65440013fb2a200dff9951001dfcca88003fd65440017eb2a200dff1951001df8ca880037c65440073e32a200cffd9110065fec888003bf64440015fb22200cff99110015fcc888033fd64440197eb22200cff19110015f8c888033bc64440055e322200cffd5110067fca888033fd5444019fe2a22000ffd8d10005fec688003fe63440157f31a2000ff58d10005fac688003fc63440157e31a200dffd4d10007fca688003fd534401bfe29a200cffd0d10067fc8688033fd4344019fe21a200bffd891005dfec48802ffe62440037f312200bff5891005dfac48802ffc62440037e312200bffd491005ffca48802ffd5244017fe292200bffd091005f7e848802ffe4244017fea12200bef5091005ff8848802fff3244017ff192200bff4c91005ff86488037ff5144009ff28a2000ff54510027f8a288033ff4144009ff20a200cfd90510067fa8288033f54144009fe20a2000ffcc510027fc6288003fd3144009fe18a200bffc8510027fc428802ff62144017fe90a200bfd48510027f84288037ff5044001ff2822000ff5411006ff8a088033ff4044019ff202200cff50110067f88088003ff3044001ff1822000ff4c110007f8608802fff2044017ff102200bff4811005ff84088013ff1044009fd8822000ff84110007ec2088017ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff59410005faca080137d65040013eb282005ff19410025f8ca08017ff64040097fb202004ff99010015fcc808013be64040055f3202004ff5901003dfac808013bd64040015eb202005ff19010025f8c80801fff540400fff2a02007ff5501003ff8a808017ff63040097fb182004ff98c10055fcc608013de63040016f3182004ff58c10005fac608013dd63040016eb182005ff18c10025f8c608023ff5304001ff2982000ff54c10047f8a60801fff430400fff2182007ff50c1003ff88608017ff62040097fb102004ff9881000dfcc408013ee6204003773102004ff58810035fac408013ed620400176b102005ff18810025f8c40801bff520400dff2902006ff54810037f8a40801bff420400ddfa102006ff90810037fa840801bbd420400dfe2102006ffcc810037fc640801bfd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841004dfcc008023ff500400bff2802000ff5401002ff8a00801fff400400bff2002007ff5001002ff88008003ff300400bff1802000ff4c01002ff8600801bff200400bff1002006ff4801002ff84008013ff1004009fb8802005ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x7fc510c029ffa086014ff904300a7fa8218053fc410c015ff988600aff8c430057fa621802bfc310c027ff9086013ff8843009ffa421804ffc210c02d7f3006015ffd403002ffca018003fd500c00bfe2806014ffd003002ffc8018053fd400c00bfe200600affcc030057be6018017fe300c015fd180600aff4c030007ba601802bf9300c027ff9006005ff8803009ffa4018017fc200c009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2000bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262011bf59310027f8c988012fc64c4023ffaa62011ff9531008ffaa988047fc54c4009ffb1e2004bfd8f10027fcc78802afe63c4009feb1e2000bf58f10027f8c788012fc63c4025ffa9e2000ff94f10007faa78804bfc53c4023ffa1e2011ff90f1008ffa8788047fc43c4009ffb162004bfd8b10027fcc588006fe62c4009feb162010bf58b10027f8c588012fc62c4021ffa962010ff94b10087faa588043fc52c4021ffa162010efd0b10087fc8588043fd42c4021dea162010ff10b10087fe6588043fe32c4021fe9962010ff0cb10027fea388013fe51c4009fea8e2004ff14710027fe8388013fe41c4009fb20e2004ff5071008fea8388013fc41c4009ff98e2004ff8c710027fa6388013fc31c4009ff90e2004ff88710027ec4388013fd21c4021fa90e2004ff08710097fea188003fe50c4001fea862012ff1431008ffe8188047fe40c4023fea062011ff10310007fe6188003fe30c4001fe9862000ff0c310087fe4188043fe20c4021fe9062010ff0831002ffecb08002ff658401fff32c2003bf99610007facb08002fd658400bfe32c2003bf1961002ffec90803aff648401dff3242002bf99210077fac90803afd648400bfe3242002bf19210077fea90803bfe548401dfeaa4200eff1521002ffec708002ff6384001ff31c200abf98e10007fac708002fd638400bfe31c200abf18e1007ffea708003fe5384001fea9c200fff14e10077fe870803bfe438401dfea1c200eff10e1002ffec508026ff6284013ff3142001bf98a1004ffac508026fd628400bfe3142001bf18a1004ffea508027fe5284013fea942009ff14a1004ffe8508027bf4284013ff2142009ff50a1004f7a8508027fc4284013ff9942009ff8ca1004ffa6508027fc32840177eb0c200fffd4610027fca308003fd5184009fe28c200effd0610027fc830803bfd4184009fe20c2000ffcc610027fc6308003fd3184009fe18c2009ffc8610027fc4308027fd2184009fe10c2004bf9821007ffea108017fe5084001fea842005ff14210077fe8108017fe408401dfea042005ff10210007fe6108017fe3084001fe9842005ff0c21004ffe4108017fe2084013fe9042005ff08210027fe2108003f71084009fd8
  | 2 => 0x30057f88718017ff628c02d7fb146016ff98a3000dfcc51805bfd628c02d7eb146005ff18a3000df8c51805bff528c02dff2946016ff54a300b7f8a51805bff428c02ddfa146016ff90a300b7fa851805bbd428c02dfe214600affcca300b7fc651805bfd328c015fe1946005ffd8630007fcc318012fe618c001feb0c6000bf5863002ff8c31806fff518c001ff28c6000ff546300dff8a31806bff418c035ff20c601aff506300d7f8831802bff318c001ff18c6000ff4c630057f8631805bff218c02dff10c6016ff486300b7f8431802afe608c037ffa846005ff94230007faa118017fc508c035ffa046005ff902300d7fa8118017fc408c015ff9846000f7cc230057f6611805bff208c00bff1046016fe882300b7fa411805bf9208c00bfe1046000ffd9530005feca98067fe654c0077f32a6000ff59530005faca98067fc654c0077e32a6018ffd91300c5fec898063fe644c0057f3226018ff591300c5fac898063fc644c0057e3226018ffd51300c7fca898063fd544c031fe2a26019ffd4d300cfbea69802bfe534c001fea9a600aff14d300cfb8a698063ff434c015ff21a6018f790d300c7fa8698063dd434c015fe21a6017ffd89300bdfec49805ffe624c0037f3126017ff589300bdfac49805ffc624c0037e3126017ffd49300bffca49805ffd524c02ffe2926017ffd09300bf7e849805ffe424c02ffea126017ef509300bff8849802bff324c02fef9926017ff8c9300bffa649805fdd324c015fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530025f8c298067ff514c001ff28a6000ff545300cff8a298063ff414c031ff20a6018ff505300c7f8829802bff314c001ef98a6000ff8c530007fa6298003dd314c015fe18a6017ffc85300bffc429805ffd214c02ffe10a6019ffd4130007fca098003fd504c033fe2826018ffd01300c7fc8098063fd404c031fe202600affcc130057f66098003fe304c001ef1826017ffc81300bffc409805ffa204c02ffe9026017fe481300bff84098017ff650c0157fb28600aff9943001dfcca1802bfd650c0017eb286005ff19430055f8ca18017ff640c0157fb20600aff99030015fcc81802bfd640c0297eb206005ff19030055f8c818053ff540c029ff2a06014ff550300a7f8a81802afe630c015ffa98600aff94c30057faa61802bfc530c015ffa18600aff90c30057fa861802bfc430c00bffb10600abfd8830057fcc418006fe620c015feb106013bf5883002ff8c418006fc620c027ffa906013ff9483009ffaa41804ffc520c027ffa106013efd083009ffc841804ffd420c027dea106013ff10830057fe641802bfe320c015fe990600aff0c83002ffec21802bfe610c0097f308600aff58430005fac218017fc610c02bffa886000ff94430007faa21805
  | 3 => 0xfb22a020bfd9150107fcc8a800afe6454041feb22a020bf59150107f8c8a800afc6454007ffaa2a003dfd515001ffca8a800ffd5454041beaa2a003ff15150007fec6a8002ff6354001ff31aa000ff58d50007f8c6a802afc6354007ffa9aa003ff94d50006fca6a800ffd5354007fe29aa003df14d50107fe86a8083fe4354041fea1aa020ff10d500fffec4a807eff625403fff312a001bf989500fffac4a807efd625403ffe312a001bf1895001ffea4a800f7f5254007ff292a003ff549500fefaa4a800ffc525403fffa12a01fefd09500fffc84a807ffd425403fdea12a01fff109500fffe64a807ffe325403ffe992a01fff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8012fc6154007ffa8aa003dfd455001ffca2a800ffd5154001bea8aa003ff14550107fe82a8083fe4154041fea0aa020ff10550007fe62a8003fe3154001fe98aa000ff0c5500fffe42a807ffe215403ffe90aa01fff0855001dfec0a800fff5054007fda82a003ff94150006fca0a800ffc5054007be282a003fe14150107fe80a8083fe4054041fea02a020ff101500fffe40a807ffe205403ffe902a01fff08150057fecb9802aff65cc015ff32e6003bf99730056fccb9800e7e65cc015feb2e6000bf59730056facb980027d65cc015fe32e600abf19730057fec99802aff64cc015ff3266002bf99330057fac998076fd64cc015fe326600abf193300effea998077fe54cc03bfeaa6601dff15330057fea79807bdf53cc015ff29e600aff54f30057f8a79802bdc53cc015ffa1e600aff90f30057bc879802bfd43cc03beea1e600aff10f30057fec59802aff62cc015ff3166001bf98b30057fac598072fd62cc015fe3166001bf18b300e7fea598073fe52cc039fea96601cff14b300e7fe8598073bf42cc039ff216601cff50b300e77a8598073fc42cc015ff996600af7ccb30057fc659802bfd32cc039ee996600aff0cb30057fec39802bfe61cc0097f30e600aff58730005fac39802bfc61cc03dffa8e6000ff94730007faa39807bfc51cc03bffa0e601dff907300effa8398077fc41cc015ff98e600af7cc730057fc639802bfd31cc001ee98e600aff0c7300e7fe4398073fe21cc039fe90e601cff087300f7fea198003fe50cc001fea86601eff143300effe8198077fe40cc03bfea06601dff103300e7fe4198073fe20cc039fe906601cff0833002ffecb18002ff658c037ff32c6003bf99630006fccb1800e7e658c001feb2c6000bf59630006facb180027d658c00bfe32c6003bf1963002ffec91806aff648c035ff3246002bf992300d7fac91806afd648c00bfe3246002bf192300d7fea91806bfe548c035feaa4601aff152300bdfac71806fff538c015ff29c6000ff54e30057f8a71806bff438c015ff21c601aff50e
  | 4 => 0x89bfd324c415fe1926228ffd4531027fca298803fd514c409fe28a6227ffd0531027fc829889ffd414c409fe20a620affcc531057ee6298813fe314c409ef18a6226ffc8531027fc429889bf6214c44dfe90a6226fd48531027f84298803ff604c4017fb026200ff98131007fac098803fc604c4017e3026228ffd4131147f8a09889fff404c44fff2026227ff5013113ff8809889bff204c44dff1026226ff48131137f84098813ff650c4097fb286204ff9943101dfcca188137e650c4073f3286204ff59431005faca188137d650c4013eb286204ff19431025f8ca18813ff640c4097fb206204ff99031015fcc818813fd640c4497eb206204ff19031025f8c818893ff540c449ff2a06224ff55031127f8a81882afe630c415ffa98620aff94c31057faa61882bfc530c415ffa18620aff90c31057fa861882bfc430c409ffb106204bfd8831027fcc418806fe620c409feb106223bf58831027f8c418812fc620c447ffa906223ff9483111ffaa41888ffc520c447ffa106223efd083111ffc841888ffd420c447dea106223ff10831057fe641882bfe320c415fe990620aff0c831025fcc218813ff510c409ff2886204ff54431027f8a218813ff410c409ff2086204ff50431027f88218813ff310c409ef9886204ff8c431027ec6218813fd310c409ee988620afd4c431027fe4218813fe210c409fe9086204ff08431027fec018813fe600c4017f3006204ff58031005fac018813fc600c44bffa806225ff14031127fe8018893fe400c449fea006224ff1003111ffe401888ffe200c447fe9006223ff0803101dfacb28017ff64940457fb24a022ff99250015fcc92808bfd64940457eb24a005ff19250015f8c92800fff5494007ff2a4a003ff5525001ff8a928017ff6394001ff31ca00abf98e50007bcc728002de6394001feb1ca000bf58e50007bac728002dd639400bfe31ca003ffd4e5001efea72800ffe5394007fea9ca000df54e5001ff8a72808bff4394045ff21ca022ff50e50117f88728017ff62940437fb14a021ff98a5000dfcc528087fd62940437eb14a005ff18a5000df8c52800fff5294007ff294a003ff54a5001ff8a528087ff4294043dfa14a021ff90a5010ffa8528087bd4294043fe214a021ffcca5010ffc6528087fd3294043fe194a005ffd8650007fcc328012fe6194001feb0ca000bf5865002ff8c32800fff5194007ff28ca000df9465001ffaa32800ffc5194007be28ca022ffd0650117fc832808bfd4194045fe20ca000ffcc650007fc6328003fd3194001fe18ca021ffc865010ffc4328087fd2194043fe10ca003bf9825001ffea12800f7f5094007fda84a005ff1425001ff0a12808bff409400bff204a022ff5025002ff88128087ff209400bff104a021ff4825002ff8412800eff6554041f
  | 5 => 0x815117ffa40a88bffc2054415ffb2e620abfd9731057fccb9880efe65cc415feb2e6200bf59731057f8cb9882afc65cc415ffb26620abfd9331057fcc99880afe64cc415feb26622dbf59331057f8c99882afc64cc45bffaa6622dff9533116ffaa9988b7fc54cc415ffa9e620aff94f31057bca79882bfd53cc401eea9e620aff14f31057fe879882bfe43cc415fea1e620aff10f31057fec59882aff62cc415ff3166201bf98b31057fac5988b2fd62cc415fe3166201bf18b31167fea5988b3fe52cc459fea96622cff14b31167fe85988b3bf42cc459ff216622cff50b311677a85988b3fc42cc415ff996620aff8cb31057fa659882bfc32cc45dffa8e6204ff94731007faa398813fc51cc45bffa0e6204ff9073116ffa8398813fc41cc459ff90e6204ff88731167fa4398813fc21cc415ffb06620aff98331005fcc19882bfd60cc4017eb06620aff18331177fea1988bbfc50cc45bffa06622dff9033116ffa81988b7fc40cc459ff906622cff88331167fa41988b3fc20cc409ffb2c6204bfd9631027fccb1880efe658c409feb2c6200bf59631027f8cb18812fc658c409ffb246204bfd9231027fcc91880afe648c409feb24622abf59231027f8c918812fc648c455ffaa4622aff95231157faa9188abfc548c44d7eb1c622bffd4e31057fca718803fd538c415fe29c622affd0e31057fc87188abfd438c415fe21c6204ffd8a31025fec518813fe628c4037f3146204ff58a3114dfac518813fc628c4097e3146229ffd4a3114ffca5188a7fd528c453fe2946229ffd0a3114f7e85188a7fe428c453fea146229ef50a3114ff8851882bff328c453ff1946229ff4ca31057f86518812fe618c409ffa8c6204ff94631027faa318813fc518c409ffa0c6204ff90631027fa8318813fc418c409ff98c6204f7cc631057ee6318813ff218c409ff10c6204fd88631027fa43188a7f5218c409fe10c6204ffd8231027fcc118802fe608c409feb046200bf58231027f8c1188afff508c457fe284622affd0231157fc81188abfd408c455fe2046229ffc823114ffc41188a7fd208c453fe1046200ffd9531005feca988037f654c4013fb2a6228ff9953101dfcca98803fd654c4017eb2a6228ff1953101df8ca988037c654c4073e32a6227ffd913113dfec89889ffe644c4057f3226227ff5913113dfac89889ffc644c4057e3226227ffd513113ffca89889ffd544c44ffe2a26228ffd4d31057fca698803de534c401fea9a6200f754d31057f8a69889fff434c415ff21a6227ff50d31057f8869889bff624c44d7fb126226ff9893100dfcc49889bfd624c44d7eb126226ff1893100df8c49889bff524c44dff2926226ff54931137f8a49889bff424c44ddfa126226ff90931137fa849889bbd424c44dfe212620affcc931137fc6498
  | 6 => 0x7feb12a633bf5895319ff8c4a9806fc6254c07ffa92a603dfd495301ffca4a980ffd5254c67bea92a603ff1495319ffe84a98cfbf4254c67ff212a633ff5095319f7a84a98cffc4254c15ff992a633ff8c95319ffa64a982bfc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa604bf1855301ffea2a980f7f5154c07fe28aa634ffd05531a7fc82a98d3fd4154c69fe20aa633ffc855319ffc42a98cffd2154c67fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153005f8c0a980fff5054c07fe282a603df141531a7fe80a98d3fe4054c69fea02a634ff1015319ffe40a98cffe2054c67fe902a633ff0815301dfacb28813ff64944097fb24a204ff99251015fcc928813fd64944657eb24a204ff19251025f8c92880fff5494407bfaa4a203ff9525101ffaa9288cb7d5494407fe2a4a204ffd8e51027fcc72882afe6394409feb1ca200bf58e51027f8c72880fff5394407ff29ca200df94e5101ffaa72880ffc5394407be29ca232ffd0e51197fc87288cbfd4394465fe21ca204ffd8a51025fec528813fe62944037f314a204ff58a5118dfac528813fc62944097e314a203ffd4a5101efea52880ffe5294407fea94a231df54a5101ff8a5288c7ff4294463dfa14a231ff90a5118ffa85288c7bd4294463fe214a231ffcca5118ffc65288c7fd3294463fe194a204bf98651027fea3288137f5194407fba8ca204ff14651027e8a328813ff4194409ff20ca204ff50651027f88328813ff2194409ff10ca204ff48651027f84328813ff6094409ff304a200bf98251027fac128802fd6094409fe304a203ffd425101ff8a12880f7c5094465ffa04a232ff90251197fa81288cbfc4094463ff904a231ff8825118ffa41288c7fc20944097fb2aa230ffd9151185fec8a88c3fe64544057f322a230ff59151185fac8a88c3fc64544057e322a203ffd515101ffca8a880ffd5454407fe2a2a200ffd8d51005fec6a8803fe6354401feb1aa200ff18d51055f8c6a880fff5354407bfa9aa203ff94d5101ffaa6a88037d5354407fe29aa230ffd0d51187fc86a88c3fd4354461fe21aa22fffd895117dfec4a88bffe62544037f312a22fff5895117dfac4a88bffc62544037e312a203ffd495101ffca4a880ffd5254407fe292a22fffd095117f7e84a88bffe425445ffea12a22fef5095117ff884a88bfff325445fff192a22fff4c95117ff864a880eff6154407ffa8aa203fdd4551027fca2a88137e5154409fe28aa204df1455101fe8a2a88c3ff4154409ff20aa230ff50551027f882a88bfff2154409ff10aa22fff48551027f842a8803ff60544017fb02a200ff98151007fac0a8803fc60544017e302a203ffd415101efea0a880ffc5054461ffa02a230ff90151187fa80a88c3fc405445fff902a22fff8
  | 7 => 0x800200000c00601c01a00400401c00201402200000400200600a01000200000400000c00200200600401e00200200000000200000000a00000000200000603a00400200000001400400201a00e01001a00001a00400000a00a00400a00000401400a00000a03800200600602000200400001000000a00600000a00000a00000000a00200801600000000000000000e00000800200200000200e00000200001401000001800000000c00000002c00400600000000400000800c02800000200000400800000400600000600c00000200a00000200000200c00c00000000800e02000000000600e00200000601403001000000000c00600201600000400000000800a01000001200201000601200801001600000a00c00000600000200400400a00200400400000000200000803400401000a00002000e00600800000200801800600400200c00400200e00000200000001400201201001000200400000201a01c02e00000403600400200000000000c00000000c00000400400400000400200000601200400000000400200800000800000a00000200001600c00000600001200003e00003400000000200202000201002c00200200400000001000a00000a00201600a01c00400000404600a00200000400c00400200400001200000a00c01601400000202200400200800401800400002c00c00001a00000800c00e03bf59653057fec92982aff6494c15ff324a602bf99253057fac9298dafd6494c15fe324a60abf1925301ffea92980ffe5494c07feaa4a603ff15253055fcc72982bff5394c15bfa9ca603f7d4e5301ebea72982bfc5394c15ee29ca60affd0e53057fc872982bfd4394c15fe21ca60affd8a53055fec52982bfe6294c037f314a60aff58a531adfac52982bfc6294c037e314a603ffd4a5301ffca52980ffd5294c07fe294a635ffd0a531af7e85298d7fe4294c6bfea14a635ef50a531aff8852982bff3294c15ff194a60aff4ca53057f8652982bff6194c15ff30ca604bf98653057fac329802fd6194c15fe30ca603ffd465301ff8a32980f7c5194c6dffa0ca636ff906531b7fa83298dbfc4194c6bff90ca635ff886531affa43298d7fc2194c15ffb04a60aff98253005fcc12982bfd6094c017eb04a60aff1825301ffea12980f7f5094c07fe284a636ffd02531b7fc81298dbfd4094c6dfe204a635ffc82531affc41298d7fd2094c6bfe104a60abfd95531a7fec8a98d2ff6454c69ff322a602bf991531a7fac8a98d2fd6454c69fe322a602bf1915301ffea8a980f7f5454c07ff2a2a603ff551531a6faa8a980ffc5454c077fb1aa603ffd4d5301fbea6a982bfe5354c15bf29aa60aff14d53056f8a6a980fdc5354c69ffa1aa60aff90d531a7fa86a982bfc4354c67ffb12a633bfd895319ffcc4a9806fe6254c6
  | 8 => 0xcc000c9065c0010f8000000b3890000000000000046c0000000000000003bcca4000478000d60000acc0016b80554dcd0800119106d4f16018a1484d18cf871d6596a88b42b8784abcb2006461d7d810c1d84ad755950d318c40000000ac9c80014c467c5507140bc000170000000ca89c0000000000000bd40000000002b4000c98000000000ee40000d194c0a05d0f310f40f17d48c8000d80068d6c0007558283e4000b0163d1ad4518481180004457a9724e706b97f0058bbc0006807bd71d800db412535cafc8f10805741f4e0918d4103d4a84bd942c1a000181997948173c9c516d7ac000ebc0014ac8ac168b613583384c925cff4000de8000000000000f617480000006b40006e8cc12580000017888c02d45641ac1cd85400091d868b3c0003340000013148f59280003b04d40e800048c000000ff0000080cb04b00001a800168400188c9e121000029548c070c119bcd716340007e40006d57504640012d40005286cd8d8148b540000003ac7dd18800000c000000000f7c0007ec000000b954945d94294098c11655757b453864d2215a54a85896cd1cd0740013b4b44c885980003e941d58d4700fc0000040016745c85ad4495ed24c490ec11791a45410981501ec04d04c7655641894b4790d6400185d5f40000006f8c7c52c6d10c08c41549a120d18411138028d59065137c9a80485e44005f15795f01b4425488dcd98d9d933cc5d2cca5c6fd0bc30c9b02f8f35378a0ccc48080010c4a1c2a14915f83f0a597846240012e0edc80c2ccb50000000a3121c000f5d33130c0000000006000852e977c6ec9b40f42f50713a933833184c0000001e0000d380014b0001728e9d0a59a4ce418d4f40012e49a400063855955cba8a752281dca691d8d1c0000000001e4000000b9c854b1d57009c32d22490c0c054922cccc8957b992cad8888a8d4355dd59d3743294f8374c2938c00097c1395c81c03fcbb003401200800401a00a00a00200600000000000200800000002a00000a00000602c00400200800000200e00203a00000200000801200601200001000e00000400000800002c00a00001600c00e02200202200800600800400200002800001400201c00000200200a00000200200c00200400200000400e00000000203000600800003600600600c00200201002401800401800600400200000201000000600400400400000c00400201200000000000200202400a00400200000e00000800601800e00400200200200400200a00200402800a00200200001601800200600000400401600000802200001600803c00000400200000201001e00202200201200e00000000e00000600000000000200202801c00600a00400200e01200000a01c01a00000000403c00000a00c00400000c00601400200600800000000602401603e
  | 9 => 0x884000e914391c46794e58852792d1020b4000000152c000e40b81824bf8300c3c3a45a8b7401c0243a80006402f18500000000014ed90c000000674000000000000000304f84000000d553a00015d02fd840000000000000000000000000000f7156cfad4e97997640002ec0005cca6cb85329560000000bfd509768f3d76119503d920000000b780001998980000002e97dc014654a90c74a2d3e99583ed638000ab0000f6c00114450000087c7e0e54c78000000b58cec0019140000000000013017180400000000007e8c242e570c9440005a16e57e47c165004400168cb10fc080094d2fd69c0015d4000604c8147c9ec480000dc57445b45e0ea495565557ccc841417462026cf096b4e9834840c47d77463ce212ac000000000c40318b315b4b498f46880002491e8fd8b24000000000000001779630000088000000000d98ffcc184f41c57056f0344394a25580000314f404f000174c000000000000b34fc80004f80003c4000f10bcc7782b0f1d738000000000a3966cd0cd84108000d04a8953c4b8000b2880400196ca640000000017bc0000000008a000186c0007394780000a80b02ad9059601280000000000008d03f493000136c0000010b165d1e4000c4c00096cdd4eec89c7ccadc00062c819520001930000964000ca0000c04f0c4509759ad3680000001f96f4b2c000fd55300000000004580007585140317f57ec0603e18700000000000000003d80000007005199c00000004e00009f0e74e5ccd07888710240000010f00013880013fc000ad000162d5e4000ec50111590ccf14ac00010059b56e8878090000730f9d3f80017a40002a8000904000000000f88b64448000001624000b4ce44d88cbc7441d056915479498c4a40015e8000000cb40000003dc7700001800000000002a4e68a409902811800011f945407d7c41fc00000000107c0011b183c0752c005c4c1234000a4593c00000066c000000d4d05c001660c500000000003704985b8eacaa47f0c3027c6686700000005f458ca98584210000000000aa8da8b092bc9d40003f88cd4596d4000cb892c0000011b40e19180000000016bc00000000000800036d67c1614c8660ec8f4c1305fd550bd0078000000000b156a0000d44b9117cb7d6680000011f4000000000000530000504000000634fe03c0001934000000000ba400138400154c4dd88086c000a107f4a78a08cd99742d8000e6c000b180000000006992600000010c80013180000000940000018943c85703b869c360b0c000000be4000000bf45c40000006119f00000008fd78c000001094000000461585830eb0e88f2c4109acdec0000001e87f8c0c0004215bc4e800035c0007b4000000434db8bc05540000000000000000000015886e00015ac54c0015fd230e840000000000009dd5c03
  | 10 => 0x13f0cd455c000e28000000c7175d8ecd1400187c011090bc52ed4402516a51e0efc9213bd10400119d40101c0010847fd45d91ceb914d054fec0b8740fe56c18e515d1b936403c0000006c57316ed360000d10734684001414000aec000e2c000cf51713c0a04000000214f2000120400084c47400000110d1fd5a8f8c0b4dd8f044d800005146139c2c494160d1a99d027422544d7fd0e0f913056097711bc93883400028526cc8c0000016112c52b40017d00014244ed5c400172147400064800078c0002980011d050d1dd0b40000017f88e822c38cd78000e4d2d9248fb416c980a5400109c000001274fccfa40011f00007a40000002182dc000000d2c8159e02d15013c95959c531c1200ec96912470cdbd31155400000154511d3b0000310000000ee0c9c0000018b0000d7c8ec970be8000fb80009f437d56898400133400081161c000000fa8000000000000c6c0000005115040000018f0ad4001621420710db019d7908500000000000000000005bccfc0018354e02455a0594028ac55b00000012898151ec234becc1400000074800127ce8c000001398000000ecc0000010dce7d060e180e55e0868f7800151c0016645901a40018658e8524fb0ba18a54444cc4413ac66400000093c0000000003981451a176ca49394ea08a800000068d0d98892a8e1d3cc7d0000018000a0000150ce0c001714000a188580009880004b40019d4a9c20c934aac7d4ed80000000012f8ee875c470001245128000f28000fd0bdc00169061499d0897096882082c8000a1469192414d9945ed2192f58fce10184c84489944001309140430000001954000000bb93e4960001240a4d82c0000000019680340004d0000000b980019e4bac1b140424cb6c000001160d74000494f459016c94d964c864b5ce340013d400000128c0018dc001130c08000000000000dc9858be011c0000019a00000000007055989f80004fc000d294d4e24000000001780a711008bc3902682c07ac0016719cc0012a40cd0b9215038ae4428bb58a8f942880012c82588b0000830ef4fe8724340ae0c2c694ae8ff8ce079d5110a00000000000015398602bc87410000110929500c000000000e013e043c6a8001908000468f984a85d42207c472113c13433c1bc00000097949c158001268000001810000001534f7579ced0000000df800143c8810510440009155581b8f4800000002cd21418000384dac00000000022800134c13d40c00151917506826527038838172d3c58e1110e391697c8af41d4d3c0c40000f800000134800094895d0acd685080012a0958c58358af80010ec9500000018d40000000d8000d5800000077c165644fbc114191604000000608000000c940015cce58c6519829d4683559987b9498c612dcfa18d05e96e1808378290000c6823002
  | 11 => 0x10d000000008d9a93900000000000000000000000000010d58ad370001529820f396986ad6d96194bcc003257cc88c001964d5c728000d949cd3a48994c076891180597d4b84385206bcd50000000e940000007183d13d17e01411d569442c1957a0200cdd7c0ea87a89bc0002056485dc62923873c00112cf24000000000000000cf000051c000ed46c000123c0000000014300990294a4000000824000000ce80000006b0cad9dcd35048e50de1464000000000a3cc447747808d8e04c1c000561991009290d24998f191c19e84a0a513f4ddcb70838254f808453ecde51514cc0d479885d14995d4d00000000000000000016fca610780c8dc006c000000000000001984aa099503000074c00057d9700016b19c8000000000000000c3999c48400151400059c00000180c9fd9380006d856d3200013b8848000da181d4a09d02702790fc83c2e00012b98b97017100012b00000017b00001040016146c908c0008e00018b501800015c0004085350e80018458bd734000df00000000000013d8000000001874000001134df49e800100000000189c7d8000d900017589180000000001f021ca201784bc5f8350000001541121014c2053d9812648409d90647506a5549878dfd0415b90a8000000000000000578000000000dd0d00a7c00060c630000d9c34c00000000025ce3c00076c0008d5280001298f54b696c49280018c80006a11140a4000454f501c85b0e600000010e400134400045c000000f588618cc0017954fc6457400016802400005458380005a47080000005c06dc4e59ec000ac800146c00039c0000000002387b11c92849e5628ef0000e80000c54e797e9119340ab8000bc817c000000321524000000000000c352547a0b8d058af00006f40008dd91132598800044c00000000000000072cef8a356f99b0000001250658618001354000000a287c902ceb4000308b88e146e49b800031cf6400081d3dcb0423d13800000132cf69350c496ac0000004c40000008e40000dc890000d48368000000828e659487600384056d0da400000049c8a40019b994012c000000fdcf0041c000e483a1890000d8c0000000016400000008b8a95678364000000000000000a80ab400000103482c260fc4000d412095d920129c000000820000418924bf16dc5803b52f00009080000006f00000018f80008f8e30000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002ede7058c1002edc7058c10006df5058c1002ede5058c1002edc5058c10006df4058c1002ede4058c10006dd4058c1002edc4058c10006df2058c1002ede2058c10006dd2058c1002edc2058c10026df1058c1002ede1058c10026dd1058c1002edc1058c10054ff7694c1002cfe7694c10004fd7694c1002cfc7694c1001e7e6594c100067d6594c101b6be6494c10006bd6494c10056de6394c10006dd6394c100475f5394c101aeee6294c10004ff7654c1002cfe7654c10004fd7654c1002cfc7654c1001e7e6554c100067d6554c101a6be6454c10006bd6454c10056de6354c10006dd6354c1019eee6254c10005f77154c10025f47154c10006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec3158810036ef705881002eee7058810036ed705881002eec7058810006ef505881002eee505881002eec5058810006ef405881002eee4058810006ed405881002eec405881002eee305881002eec3058810026ef1058810026e7105881002eee1058810026ed105881002eec105881007cff765401001e7e65540100067d6554010106be6454010006bd6454010006de6354010006dd63540100feee6254010006ed6254010004fd76cc0100457e75cc0100057d75cc0100f67e65cc0100067d65cc0100eebe64cc010006bd64cc010056de63cc010006dd63cc0100e6ee62cc010006ed62cc010004ff764c0100ce7e654c0100067d654c0100c6be644c010006bd644c010056de634c010006dd634c0100beee624c010006ed624c01002df77644010006f77644010004f7764401000777754401000774754401002f76654401002f756544010007b774440101c7b4744401002ef7644401002fb664440101c6f5644401002fb56444010006b5644401002fd6634401002fd5634401002ef7624401002fe662440101bef5624401002fe56244010006e562440101bfb742440101bfb5424401002df77044010027f3704401002ef6604401002ff2604401002ff25044010007f1504401002ff23044010007f13044010
  | 1 => 0x9010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc215901003ebf705901002ebe705901003ebd705901002ebc7059010006bf505901002ebe505901002ebc505901002ebe305901002ebc3059010006bf205901002ebe2059010006bd205901002ebc2059010026bf1059010026b7105901002ebe1059010026bd105901002ebc1059010056df7598c10056de7598c10056dd7598c10056dc7598c10056df7498c10056de7498c10056dd7498c10056dc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c10056df7298c10056de7298c10056dd7298c10056dc7298c10006df5298c10006de5298c10006dd5298c10006dc5298c10006df4298c100069f4298c10006de4298c10006dd4298c100069d4298c10006dc4298c10026df7198c10026de7198c10026dd7198c10026dc7198c10026df5198c10026de5198c10026dd5198c10026dc5198c10026df4198c10026de4198c10026dd4198c10026dc4198c10026df2198c10026de2198c10026dd2198c10026dc2198c1002ede7098c1002edc7098c10006df5098c1002ede5098c1002edc5098c10006df4098c1002ede4098c10006dd4098c1002edc4098c10006df2098c1002ede2098c10006dd2098c1002edc2098c10026df1098c1002ede1098c10026dd1098c1002edc1098c10004ff7558c1001cfe7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c1002cff7358c1002edf7358c10006df5358c10006dc5358c10006df4358c10006de4358c10006dd4358c10006dc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c10006bf4258c10006bd4258c10006df3258c10006de3258c10006dd3258c10006dc3258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c10026de3158c10026dc3158c10054ff7058c1002cfe7058c10054fd7058c1002cfc7058c1002ede3058c1002edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026d
  | 2 => 0x5f77154110025f47154110024fe76cc110024fc76cc11006d7e75cc1100057d75cc1100067f65cc1100f67c65cc110006bf64cc1100eebc64cc110006df63cc110056dc63cc110025f671cc110005f571cc110004fe768c11006d7e758c1100057d758c1100067f658c1100de7c658c110006bf648c1100d6bc648c110054ff764c110004fd764c110024fc764c1100067f654c1100ce7c654c110006bf644c1100c6bc644c110006df634c110056dc634c110005f7714c110025f4714c110004fe760c1100067f650c1100ae7c650c110006bf640c1100a6bc640c1100067f658411007e7c6584110006bf6484110076bc6484110025fa7084110026fb6084110025f6768411002ef67684110024f6768411000777658411000774658411002df774841101e5f57484110007b764841101dfb4648411002df772841101d5f572841101cfb742841101cfb5428411002df6708411002ef76084110027f3608411002cff755941002e7f7559410004ff7459410014fe7459410004fd7459410014fc74594100467f54594100067e54594100067d54594100467c5459410004ff7359410054fc73594100467f53594100467c5359410004ff725941000cfe7259410004fd725941000cfc72594100467f52594100067e52594100067d52594100467c5259410006bf4259410006bd4259410024ff7159410024fe7159410024fd7159410024fc71594100267e51594100267c515941001cff705941002cfe705941001cfd705941002cfc705941002e7e505941002e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100063f42594100067e42594100067d42594100063d42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c21594100467f705941002e7e705941002e7c70594100067f405941002e7e40594100067d405941002e7c405941002e7e305941002e7c30594100067f205941002e7e20594100067d205941002e7c20594100267f105941002e7e10594100267d105941002e7c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf525
  | 3 => 0xf71d91101eebe71d9110066bd71d91101eebc71d9110006bf51d91101eebe51d91101eebc51d91101eebe31d91101eebc31d9110006bf21d91101eebe21d9110006bd21d91101eebc21d91101eebf70d9110066be70d9110066bd70d9110066bc70d9110006bf50d9110006bc50d9110006bf20d9110006be20d9110006bd20d9110006bc20d91101eebf10d9110066bd10d91101eebc10d9110054fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006bf42d8d10006bd42d8d10006de32d8d10006dc32d8d10024fe71d8d10024fc71d8d10006f621d8d10006f521d8d1002cfe70d8d1002cfc70d8d1006d7e7598d100057d7598d100067f6598d100067c6598d10065be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100057f7558d1006d7c7558d100067f6558d100067c6558d10005bf7458d10065bc7458d10006bf6458d10006bc6458d10005ef7258d1005dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d10006bf4258d10006bd4258d10004ff7158d10006f77158d10006f62158d10006f52158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10056de6318d10006dd6318d10054ff7694d10004fe7694d10004fd7694d10054fc7694d100067f6594d1001e7c6594d10006bf6494d101b6bc6494d1006f5f5394d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d10006bf6454d101a6bc6454d1001cfc76545100067f655451001e7c6554510006bf6454510186bc6454510005fb7054510005f87054510027f01054510004fe76cc51002cfc76cc5100067f65cc5101767c65cc510006bf64cc51016ebc64cc510006df63cc510056dc63cc510005fa70cc510005f970cc510054fc764c5100057f754c51006d7c754c5100067f654c5101467c654c510006bf644c51013ebc644c510006df634c510056dc634c510005fb704c510005f8704c510027f0104c510094fe76941100067f659411001e7c6594110006bf6494110116bc6494110005de7394110005dd739411001cff765411006cfd7654110024fc76541100067f655411001e7c6554110006bf6454110106bc6454110
  | 4 => 0x951002cfc70d951006e7f50d951006d7e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067f62d95100067e62d95100067d62d95100067c62d95100073f42d95100073d42d95100077641d95100077541d95100077621d95100077521d95101ff7b10d95101ff7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95101fe7e71d95100067d71d95101fe7c71d95100067f41d95101fe7e41d95100067d41d95101fe7c41d95101fe7e31d95101fe7c31d95100067f21d95101fe7e21d95100067d21d95101fe7c21d95101fe7f70d951006e7e70d95100067d70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067e20d95100067d20d95100067c20d95101fe7f10d95101fe7c10d951006e7c6559510005bf7459510065bc7459510006bc645951006cff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc7459510004ff7359510054fc7359510004ff725951000cfe7259510004fd725951000cfc7259510006bf4259510006bd425951007cff7159510006f77159510094ff7059510006fb70595100057e761951006e7e76195100047e76195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067f62195100067e62195100067d62195100067c62195100073f42195100073d42195100077641195100077541195100077621195100077521195101f67f60195101f77b10195101f7781019510065be76d9110066be76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007b771d9110067b471d9110007b621d9110007b521d91101efbb10d91101efb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006b
  | 5 => 0x2ede73d9610054de73d9610004fd73d961002edd73d9610004dd73d961007e7f53d961002cff72d961000cfe72d9610004fd72d961002cfc72d9610006bf42d9610006bd42d961002ef571d96101fe7e51d96101fe7c51d961002efa70d961002e7f50d961001cff765961002e7c655961002e7f7559610004ff7459610014fe7459610004fd7459610014fc745961007e7f54596100067d5459610004ff7359610054fc735961007e7c5359610004ff725961000cfe7259610004fd725961000cfc725961007e7f52596100067d5259610006bf4259610006bd425961007e7f515961002cfc705961002e7e505961002e7c505961001cfe75d8e1002e7e75d8e1001c7e75d8e10004fd75d8e1002e7d75d8e100047d75d8e1002cfc75d8e1002cff74d8e10014fe74d8e10004fd74d8e1002cfc74d8e1002cff72d8e1000cfe72d8e10004fd72d8e1002cfc72d8e10006bf42d8e10006bd42d8e1002ef571d8e1002efa70d8e10004fd7698e1007d7e7598e100057d7598e1002edf6398e1002edc6398e10054ff7658e1002edc6358e10004ff7558e1001cfe7558e1001cfc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e1002edf7358e10006df5358e10006dc5358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e10006bf4258e10006bd4258e10006df3258e10006dd3258e1002cfc7058e1002ede3058e1002edc3058e10054ff7694e1002cfe7694e10004fd7694e1002cfc7694e1001e7e6594e100067d6594e1007f5f5394e10004ff7654e1002cfe7654e10004fd7654e1002cfc7654e100067f6554e1001e7c6554e10005f77154e10025f47154e1001cff765461002cfc765461001e7e65546100067d6554610005fb705461002df87054610056de63cc610006dd63cc61002dfa70cc610005f970cc610054ff764c6100057f754c61007d7c754c610056de634c610006dd634c610005fb704c61002df8704c610044ff765421002e7f655421002e7c655421007d7e75cc2100057d75cc21002edf63cc21002edc63cc21002edf634c21002edc634c21002df576c4210026f576c421002ef764c421020ef564c421002ef762c4210206f562c4210207b742c4210207b542c421002ff260c421001cfe76d951006e7e65d9510006bc64d9510004ff74d9510014fe74d9510004fd74d9510014fc74d951006e7f54d95100067e54d95100067d54d951006e7c54d9510054fe73d9510004fd73d951006e7f53d951006e7c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d951006e7f52d95100067e52d95100067d52d951006e7c52d9510006bf42d9510006bd42d9510024fe71d951006cfd71d9510024fc71d951006e7f51d951002cfe70d9510024fd70d
  | 6 => 0xe7359430054fd7359430054fc73594300567e53594300567c5359430004ff725943000cfe7259430004fd725943000cfc72594300ae7f52594300067d5259430006bf4259430006bd4259430004ff7159430024fc71594300ae7f515943002cfe705943002cfc705943002e7e505943002e7c5059430004ff75584300067f75584300047f755843001cfe755843001cfc75584300067c755843001c7c7558430004ff7458430014fe7458430004fd7458430014fc7458430004ff725843000cfe7258430004fd725843000cfc7258430006bf4258430006bd425843002ef77158430006f64158430006f54158430056f73158430056f43158430006f62158430006f52158430024ff7058430056df305843002ef6105843002ef41058430024ff769443002cfe7694430004fd769443022e7f659443001e7c6594430026f66194430006f56194430004ff7654430004fd765443002cfc765443001e7e65544300067d6554430026f66154430006f561544300dcff765403002e7f655403002e7c655403002ddf764c030006df764c030004df764c0300cede654c03002edc654c03002edf644c030226dd644c03002edf624c03021edd624c03021f9f424c03021f9d424c030006dd614c03002ddf704c030057db704c03002ede604c03002fda604c03002fda204c03021fd9204c0300267f7559710004ff7459710014fe7459710004fd7459710014fc7459710004ff7359710054fc73597100967f5359710004ff725971000cfe7259710004fd725971000cfc7259710006bf4259710006bd4259710024fc71597100267e51597100267c51597100967f5059710004ff7558f100067f7558f100047f7558f1001cfe7558f1001cfc7558f100067c7558f1001c7c7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f10026df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f10006bf4258f10006bd4258f10024fc7158f10026de3158f10026dc3158f10026f62158f10006f52158f10054ff7694f10024fe7694f10004fd7694f10024fc7694f102167f6594f1001e7c6594f10056de6394f10006dd6394f100975f5394f10004ff7654f10024fe7654f10004fd7654f10024fc7654f1001e7e6554f100067d6554f10056de6354f10006dd6354f1006cfd76943101fe7f659431001e7c6594310005de7394310005dd739431001cff7654310024fc765431001e7e65543100067d6554310005f77154310025f471543100957e75cc3100057d75cc310056de63cc310006dd63cc310025f671cc310005f571cc3100957e758c3100057d758c310054ff764c310056de634c310006dd634c310005f7714c310025f4714c31007cfd75d961002cff74d9610014fe74d9610004fd74d961002cfc74d9610054fe73d9610
  | 7 => 0x953000cec72595300ce7f52595300067d5259530006bf4259530006bd4259530004ff7159530006f77159530004f77159530024fc7159530006f47159530024f471595300ce7f51595300f4ff7059530006fb70595300ce7c505953001cfc7654d300067f6554d3001e7c6554d300cddf7354d300575c5354d30005fb7054d30005f87054d3001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d8530006bf42d8530006bd42d8530006f751d8530006f451d853002cfe70d8530006f761985300057f75585300cd7c7558530005bf74585300c5bc7458530005ef72585300bdec72585300cd7e75185300057d7518530026f66118530006f56118530004fe7694530004fd7694530024fc76945300067f659453001e7c6594530055de7394530005dd73945300cf5c5394530004ff7654530004fe7654530004fc765453001e7e65545300067d6554530005df7354530055dc73545300cf5f5354530005de76cc530056de76cc5300cdde75cc530055dc75cc530006df65cc530006dd65cc530055df74cc530275dd74cc530055df72cc53026ddd72cc5302679f42cc5302679d42cc530026de61cc530026dc61cc53002dde70cc530056df60cc530057db60cc530267da20cc530267d920cc530255dd738c530006f7618c530026f4618c530005fa708c530005f9708c530024fc764c5300057f754c5300cd7c754c530006f7614c530026f4614c530005fb704c530005f8704c530024dc764c5300075f754c5300cdde754c5300cddc754c5300075c754c5300cd5c754c530006df654c530006dd654c53025ddf744c53025ddd744c530255df724c530255dd724c53024f9f424c53024f9d424c530055df714c530057d7714c530007d7614c530026de614c530026dc614c530007d4614c53024fd6214c53024fd5214c530007db704c53002ddc704c530007d8704c530056df604c530057db604c53024fda204c53024fd9204c5300f4fe769413001e7e65941300067d6594130055de73941300cddd73941300cf5f53941300cf7b509413001cff76541300ccfd7654130054fc76541300067f655413001e7c6554130005df7354130055dc73541300cf5c53541300cd7e758c1300057d758c130055fa708c130056fb608c1300cdde758c13002f5e758c1300cd5e758c13002f5d758c13002ddc758c13002ddf748c130245dd748c13002ddf728c13023ddd728c1302379f428c1302379d428c130005dd718c13002dde708c13002edf608c130057db608c13002fda208c130237d9208c13002cff755943002e7f7559430004ff7459430014fe7459430004fd7459430014fc74594300ae7f54594300067d5459430054ff7359430054f
  | 8 => 0x67e71596300067d71596300067c71596300067f41596300067e41596300067d41596300067c415963027e7f315963027e7c31596300067f21596300067e21596300067d21596300067c21596300de7f705963002e7e705963002e7c70596300067f405963002e7e40596300067d405963002e7c405963027e7f305963002e7e305963002e7c30596300067f205963002e7e20596300067d205963002e7c205963002e7e105963002e7c105963001cff7654e3002cfc7654e3001e7e6554e300067d6554e30005fb7054e3002df87054e30057db3054e300067e65986300067d659863002ef7619863002ef461986300067e65586300067d655863002ef46158630004ff755863001cfe755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff725863000cfe7258630004fd725863000cfc7258630006bf4258630006bd4258630006f64158630006f54158630006f62158630006f5215863002cfc705863002ef6105863002ef41058630024ff769463002cfe7694630004fd769463001e7e65946300067d6594630004ff7654630004fd765463002cfc765463001e7e65546300067d655463015e7e658c6300067d658c630026f6618c630006f5618c63002dfa708c630005f9708c630024ff764c6300057f754c6300dd7c754c6301467e654c6300067d654c630026f6614c630006f5614c630005fb704c63002df8704c6300acff765423001e7e65542300067d655423002ddd76cc230056dd76cc2300575e75cc2300575d75cc2300f6de65cc23002f5e65cc2300f65e65cc23002f5d65cc23002edc65cc23002edf64cc23028edd64cc23002edf62cc230286dd62cc2302879f42cc2302879d42cc230006dd61cc23002fda60cc23002fda50cc230007d950cc23001cfe76d95300ce7e65d9530055de73d95300cf5f53d9530004ff74d9530014fe74d9530004fd74d9530014fc74d9530054fe73d95300ccfd73d95300cedd73d95300ccdd73d9530054fc73d95300ce7f53d95300cedf53d95300ce5f53d95300cedc53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d9530006bf42d9530006bd42d9530024fe71d9530004fd71d95300ce7c51d9530054fd70d95300ce7f50d95300ce7c6559530005bf74595300c5bc74595300cf5c5359530005ef72595300bdec7259530005f77159530005f471595300ccff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300ce7f54595300067d54595300dcff7359530006df73595300cedf535953027e7e535953027e7c53595300cedc5359530004ff7259530006ef7259530004ef725953000cfe7259530004fd725953000cfc7259530006ec725
  | 9 => 0xc7258730006bf4258730006bd4258730056f77158730006f74158730006f44158730056f73158730056f43158730006f62158730006f52158730024ff7694730054fe7694730004fd769473001e7e65947300067d6594730055de7394730005dd739473022f5c5394730004ff7654730004fd7654730054fc765473001e7e65547300067d6554730005df7354730055dc73547300f75f5354730055df764c730006df764c7300075f754c7300f5de754c7300f5dc754c7300075c754c7300f55c754c730056df654c7300575e654c730006dd654c7300575d654c7300065d654c7302addf744c7302addd744c7302a5df724c7302a5dd724c73029f9f424c73029f9d424c730057d7714c730026de614c730026dc614c73029fd6214c73029fd5214c73002ddc704c7300ccfd769433001e7e65943300067d6594330055de7394330005dd73943300f75f539433001cff7654330054fc765433001e7e65543300067d6554330005df7354330055dc735433027f5c53543300dcfd75d963002cff74d9630014fe74d9630004fd74d963002cfc74d963002edd73d963002cff72d963000cfe72d9630004fd72d963002cfc72d9630006bf42d9630006bd42d9630024fe71d9630004fd71d963002efa70d96300047d769963002e7f64996300067e64996300067d649963002e7c649963002e7f62996300067e62996300067d629963002e7c62996300073f42996300073d429963002e7f619963002e7c619963002e7e60996302977b309963002f78309963002f7a209963000779209963001cff765963002e7c655963002e7f7559630004ff7459630014fe7459630004fd7459630014fc74596300de7f54596300067e54596300067d54596300de7c54596300de7f5359630004ff725963000cfe7259630004fd725963000cfc72596300de7f52596300067e52596300067d52596300de7c5259630006bf4259630006bd4259630004ff7159630024fc71596300de7f51596300de7c515963002cfc705963002e7e505963002e7c505963002d7f76596300de7f765963001c7f765963002e7f64596300067e64596300067d645963002e7c645963002e7f62596300067e62596300067d625963002e7c62596300073f42596300073d425963002e7f615963002e7c615963027f7b305963002f78305963002f7a20596300077920596300067f74596300067e74596300067d74596300067c74596300067f735963027e7e73596300067d735963027e7c73596300067f435963027e7e43596300067d435963027e7c43596300067f72596300067e72596300067d72596300067c72596300067f42596300063f42596300067e42596300067d42596300063d42596300067c425963027e7f32596300067e32596300067d325963027e7c32596300067f7159630
  | 10 => 0x8550005de7318550005dd7318550026f66118550006f561185500247c76545502dd7f74545502dd7d745455027d7c73545500067f63545502d57f72545502d57d72545502cf3f42545502cf3d425455001d7f715455001f7771545500077761545500267e61545500267c61545500077461545500077b705455002d7c705455000778705455001e7f605455001f7b6054550004fe76cc550004fd76cc550054fc76cc55027d7f75cc55001d7c75cc550056de63cc55027f5e53cc550006f761cc550026f461cc550004fe768c550004fd768c550024fc768c55001d7e758c5500057d758c550004ff764c550004fe764c550004fc764c5500057f754c55001d7c754c5500075e534c550004fe760c550004fd760c550024fc760c55001d7e750c5500057d750c550006f7610c550026f4610c55002d7f74941502c57d749415027d7e739415002f5e73941500055e739415002f5d73941500067f639415002d7f72941502bd7d72941502b73f42941502b73d42941500057d71941501fe7c619415002d7e709415002f7a709415002e7f609415001f7b60941500567f7559730004ff7459730014fe7459730004fd7459730014fc74597300f67f54597300067e54597300067d54597300f67c5459730054fc7359730056dc7359730054dc73597300f6df53597300567e53597300567c5359730056dc5359730004ff725973000cfe7259730004fd725973000cfc72597300f67f52597300067e52597300067d52597300f67c5259730006bf4259730006bd4259730004ff7159730024fc71597300f67f51597300f67c5159730056df31597300f67f50597300067f74597300067e74597300067d74597300067c74597300567f73597300f65f73597300567e73597300567d73597300567c73597300565c73597300567f43597300567e43597300567d43597300567c43597300067f72597300067e72597300067d72597300067c72597300067f42597300063f42597300067e42597300067d42597300063d42597300067c42597300567f32597300567e32597300567d32597300567c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067e41597300067d41597300067c41597300567f31597300565f31597300567e31597300567d31597300567c31597300067f21597300067e21597300067d21597300067c21597300067f70597300067d70597300f67c70597300067f40597300067e40597300067d40597300067c40597300567f30597300567e30597300567d30597300567c30597300067f20597300067e20597300067d20597300067c2059730004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc7458730004ff725873000cfe7258730004fd725873000cf
  | 11 => 0x75d6354e500567c6354e5030e7f6254e5030e7d6254e5030f3f4254e5030f3d4254e501fd7c7154e500057f7054e500077b7054e50007787054e5001e7e6054e5001f7a6054e50006de6398650006dd639865002ef7619865002ef46198650006de6358650006dd635865002ef46158650004ff7458650014fe7458650004fd7458650014fc7458650004ff7358650054fc735865006e7f53586500067d5358650004ff725865000cfe7258650004fd725865000cfc7258650006bf4258650006bd425865006ef6515865006ef551586501fe7c5158650006f64158650006f54158650006f62158650006f5215865002cfc705865006e7f505865002ef6105865002ef410586503067f64946503067d64946500057d739465022e7e63946500075e63946500065e63946500075d63946502fe7f62946502fe7d62946502ff3f42946502ff3d429465001d7e719465001f7671946501ff7661946501fe7d61946500077561946501ff7a70946500057d70946501ff79709465001e7e609465001f7a6094650054ff76cc65002cfe76cc650004fd76cc65001d7e75cc6500057d75cc650056de63cc650006dd63cc6500075d53cc650024ff768c65002cfe768c650004fd768c6501fd7f758c65001d7c758c650056de638c650006dd638c650004ff764c650004fd764c65002cfc764c6500057f754c65001d7c754c650056de634c650006dd634c6500075d534c650024ff760c65002cfe760c650004fd760c65001d7e750c6500057d750c650056de630c650006dd630c650004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500de7f54d8d500067d54d8d500dede53d8d500dedd53d8d5027e7c53d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500de7f52d8d500067d52d8d50006bf42d8d50006bd42d8d50024fe71d8d50004fd71d8d500de7f51d8d500de7c50d8d50006df6398d5027f5c5398d500cdf97098d50005bf7458d50105bc7458d500cf5c5358d50005ef7258d500fdec7258d50005f77158d50005f47158d500f5fb7058d50056de6318d50006dd6318d5027d7f7494d502f57d7494d5001d7e7394d5001f5e7394d5027e7f6394d500075f6394d500065f6394d5027f5c6394d5027d7f7294d502ed7d7294d502e73f4294d502e73d4294d500057d7194d502167c6194d5002d7e7094d5027f7a7094d5027f797094d5001e7f6094d5001f7b6094d50004ff74d8550014fe74d8550004fd74d8550014fc74d8550054fe73d8550004fd73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d8550006bf42d8550006bd42d855007ef651d855007ef551d8550006f741d8550006f441d8550006f621d8550006f521d8550006f7619855006df97098550005bf7458550105bc7458550095fb705
  | 12 => 0x85098e50056df7598e50056de7598e500565e7598e50056dc7598e50056df7498e50056de7498e50056dd7498e50056dc7498e500f6df5498e500f6de5498e500f6dd5498e500f6dc5498e50056df7298e50056de7298e50056dd7298e50056dc7298e500f6df5298e500f6de5298e500f6dd5298e500f6dc5298e50006df4298e500069f4298e50006de4298e50006dd4298e500069d4298e50006dc4298e50056df7198e50056de7198e50056dd7198e50056dc7198e500f6df5198e500f6de5198e500f6dd5198e500f6dc5198e500f65c5198e50006df4198e50006de4198e50006dd4198e50006dc4198e50006df2198e50006de2198e50006dd2198e50006dc2198e5002ede7098e5002edc7098e500f6df5098e500f65f5098e500f6dd5098e5002edc5098e50006df4098e5002ede4098e50006dd4098e5002edc4098e50006df2098e5002ede2098e50006dd2098e5002edc2098e5002ede1098e5002edc1098e5002edc6358e50004ff7458e50014fe7458e50004fd7458e50014fc7458e500cede5358e500cedd5358e50006df4358e50006de4358e50006dd4358e50006dc4358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e50006bf4258e50006bd4258e50006df3258e50006de3258e50006dd3258e50006dc3258e50004ff7158e50024fc7158e5002cfc7058e5002ede3058e5002edc3058e5002ddf7658e50006df7658e500cf5e7558e500075d7558e5002edf6458e50006de6458e50006dd6458e5002edc6458e5002edf6258e50006de6258e50006dd6258e5002edc6258e500079f4258e500079d4258e5002edf6158e5002edc6158e500cf5c5158e5002f5f5058e500cfdb5058e5002fd85058e500cede7558e500cedd7558e500cedc7558e50006df7458e50006de7458e50006dd7458e50006dc7458e500cedf5458e500cede5458e500cedd5458e500cedc5458e50006df7258e50006de7258e50006dd7258e50006dc7258e500cedf5258e500cede5258e500cedd5258e500cedc5258e50006df4258e500069f4258e50006de4258e50006dd4258e500069d4258e50006dc4258e50006df7158e50006de7158e50006dd7158e50006dc7158e500cedf5158e500cede5158e500cedd5158e500cedc5158e50006df4158e50006de4158e50006dd4158e50006dc4158e50006df2158e50006de2158e50006dd2158e50006dc2158e5002ede7058e5002edc7058e500cedf5058e5002ede5058e500cedd5058e5002edc5058e50006df4058e5002ede4058e50006dd4058e5002edc4058e50006df2058e5002ede2058e50006dd2058e5002edc2058e5002ede1058e5002edc1058e500547f7654e503167f6454e503167d6454e5001d7f7354e5001f5f7354e500567e6354e500075e6354e500565e6354e50
  | 13 => 0x813102cff721813100cfe7218131004fd721813102cfc7218131006bf4218131006bd4218131024ff75594310267f7559431004ff7459431014fe7459431004fd7459431014fc745943112e7f54594310067e54594310067d545943112e7c5459431054fe7359431054fc73594310567e53594310567c5359431004ff725943100cfe7259431004fd725943100cfc725943112e7f52594310067e52594310067d525943112e7c5259431006bf4259431006bd4259431024fe7159431024fc71594310267e51594310267c5159431026df3159431026dd3159431004ff705943102cfc705943112e7f505943112e7c50594310067f74594310067e74594310067d74594310067c74594310567f73594310567e73594310567d73594310567c73594310567f43594310567e43594310567d43594310567c43594310067f72594310067e72594310067d72594310067c72594310067f42594310063f42594310067e42594310067d42594310063d42594310067c42594310567f32594310567e32594310567d32594310567c32594310267f71594310267e71594310267d71594310267c71594310267f41594310267e41594310267d41594310267c41594310267f31594310265f31594310267e31594310267d31594310265d31594310267c31594310267f21594310267e21594310267d21594310267c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067d40594310067c40594310567f30594310567e30594310567d30594310567c30594310067f20594310067e20594310067d20594310067c20594310267f10594310267e10594310267d10594310267c105943101cfe7598031004fd759803102cfc759803102cff7498031014fe7498031004fd749803102cfc749803102cff729803100cfe7298031004fd729803102cfc7298031006bf4298031006bd429803102cfe709803102efa709803102efa4098031006f94098031056fb309803102ef8309803102efa2098031006f92098031026fb109803102ef81098031004ff755803101cfe755803101cfc7558031004ff7458031014fe7458031004fd7458031014fc7458031004ff725803100cfe7258031004fd725803100cfc7258031006bf4258031006bd4258031026df3158031026dd3158031026fb7058031006fa4058031006f94058031056fb3058031056f83058031006fa2058031006f92058031026fb1058031026f8105803102edf6398e5002edc6398e500f75e7598e500075d7598e5002edf6498e50006de6498e50006dd6498e5002edc6498e5002edf6298e50006de6298e50006dd6298e5002edc6298e500079f4298e500079d4298e5002edf6198e5002edc6198e500f75c5198e5002f5f5098e500f7db5098e5002fd
  | 14 => 0x2167c71d95310067f41d95312167e41d95310067d41d95312167c41d953122e7f31d95312167e31d95312167c31d95310067f21d95312167e21d95310067d21d95312167c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d953122e7f30d953122e7c30d95310067f20d95310067e20d95310067d20d95310067c20d95312167f10d95312167c10d95311467c6559531144ff75595310067f7559531004ff7459531014fe7459531004fd7459531014fc745953115cff7359531006df7359531004ff725953100cfe7259531004fd725953100cfc7259531006bf4259531006bd4259531174ff7159531006f77159531004ff705953102cfc70595310057e76195311467e76195310047e76195310067f64195310067e64195310067d64195310067c64195311475d731953133e7f63195310067f62195310067e62195310067d62195310067c62195310073f42195310073d42195313367f611953133777311953133f5e311953133f5c3119531337743119531007762119531007752119531005de7694d31056de7694d31145dd7594d310075f6594d3101ede6594d3101edc6594d311475c6594d3101e5c6594d3132f9f4294d3132f9d4294d31025de7194d31025dc7194d31056df6194d31057d76194d312175e5194d312175c5194d3132fd62194d3132fd52194d31005dd7094d311475f5094d31024fc7654d310067f6554d3101e7c6554d310575c5354d31005f77154d31025f47154d31057d43154d31025dc7654d3101edc7654d31024dc7654d31055df7554d310575f7554d310075f6554d3101ede6554d3101edc6554d311475c6554d311475f5454d313275d5454d311475f5254d3131f5d5254d3131f9f4254d3131f9d4254d31007d77154d31025de7154d31025dc7154d31007d47154d31056df6154d31057d76154d311475f5154d3131fd62154d3131fd52154d31005df7054d311475c5054d3101cff7654531144fd7654531054fc76545310067f655453101e7c6554531005df7354531055dc73545310075d5354531027d431545310067f65d81310067c65d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d8131006bf42d8131006bd42d8131006f621d8131006f521d81311457e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311457c75581310067f65581310067c6558131005bf745813113dbc7458131005ef7258131135ec72581310067f65181310067c6518131006f9601813101cfe7518131004fd751813102cfc751813102cff7418131014fe7418131004fd741813102cfc741
  | 15 => 0xd429833102efa709833102edf3098331056fb309833102ef8309833102efa2098331006f92098331004ff755833101cfe755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc7458331024fc7358331004ff725833100cfe7258331004fd725833100cfc7258331006bf4258331006bd4258331056fb7058331056fb3058331056f83058331006fa2058331006f920583310267f7559631004ff7459631014fe7459631004fd7459631014fc745963115e7f5359631004ff725963100cfe7259631004fd725963100cfc7259631006bf4259631006bd4259631024fc71596310267e51596310267c5159631026df3159631026dd3159631004ff705963102cfc705963115e7f505963101cff7654e31024fc7654e3101e7e6554e310067d6554e31005f77154e31025f47154e31057d73154e3101cfe7598231004fd759823102cfc759823102cff7498231014fe7498231004fd749823102cfc749823102cff729823100cfe7298231004fd729823102cfc7298231006bf4298231006bd4298231024fe719823102efa7098231026fb109823102ef81098231004ff75582310067f75582310047f755823101cfe755823101cfc75582310067c755823101c7c7558231004ff7458231014fe7458231004fd7458231014fc7458231004ff725823100cfe7258231004fd725823100cfc7258231006bf4258231006bd4258231024fc7158231026df3158231026dd3158231026f62158231006f52158231026fb7058231026fb1058231026f8105823101cfe76d95311467e65d9531004ff74d9531014fe74d9531004fd74d9531014fc74d95311467f54d95310067e54d95310067d54d95311467c54d9531024fd73d95311467f53d9531004ff72d953100cfe72d9531004fd72d953100cfc72d95311467f52d95310067e52d95310067d52d95311467c52d9531006bf42d9531006bd42d9531054fd71d95311467f51d953102cfe70d9531004fd70d95311467f50d95311467c50d95311457e76d953101c7e76d95310067f64d95310067e64d95310067d64d95310067c64d95312175f73d95310067f62d95310067e62d95310067d62d95310067c62d95310073f42d95310073d42d953122f7731d95312175e31d95312175c31d953122f7431d95310077621d95310077521d95310067f74d95310067e74d95310067d74d95310067c74d95312167f73d953122e7e73d95310067d73d953122e7c73d95310067f43d953122e7e43d95310067d43d953122e7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310063f42d95310067e42d95310067d42d95310063d42d95310067c42d953122e7f32d95310067e32d95310067d32d953122e7c32d953122e7f71d95312167e71d95310067d71d9531
  | 16 => 0x8251004ff7358251054fc73582510067e535825106e7c5358251004ff725825100cfe7258251004fd725825100cfc725825106e7f52582510067d5258251006bf4258251006bd4258251024fc71582510267f51582510267d5158251026fb705825106efa505825106e7c5058251026fb1058251026f81058251024fd75d8d51004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d5115ede53d8d5115edd53d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d51006bf42d8d51006bd42d8d51006de32d8d51006dc32d8d5102cfe70d8d51004fd70d8d512167f6598d51006df6398d51145f57198d51175f77158d5133e7f6518d51056de6318d51006dd6318d510247c7654d5135e7f6454d5135e7d6454d5101d7f7354d5101f5f7354d510075f6354d510567e6354d510567c6354d510075c6354d513567f6254d513567d6254d513573f4254d513573d4254d51007777154d510257e7154d510257c7154d51007747154d5101e7f6154d5101f776154d510057f7054d51024fd75d8151004ff74d8151014fe74d8151004fd74d8151014fc74d8151054fe73d8151004fd73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d8151006bf42d8151006bd42d8151096fa50d8151005de7398151005dd7398151006fb6098151005bf7458151185bc7458151006f96018151024fd751815102cff7418151014fe7418151004fd741815102cfc7418151054fe7318151004fd73181510467f53181510067d531815102cff721815100cfe7218151004fd721815102cfc7218151006bf4218151006bd42181511f67e51181511f67c511815102e7f501815102efa5018151046f950181510567f7559731004ff7459731014fe7459731004fd7459731014fc74597311767f54597310067d5459731024fc73597310567e53597310567c5359731004ff725973100cfe7259731004fd725973100cfc72597311767f52597310067d5259731006bf4259731006bd42597311767f5159731004ff705973102cfc70597311767c5059731055df7654f3112edf7654f310575f7554f310575f6554f3101ede6554f31056dc6554f310575c6554f311775f5454f3134f5d5454f311775f5254f313475d5254f313479f4254f313479d4254f31025de7154f31025dc7154f311775f5154f31005df7054f311775c5054f3101cff7654731054fc765473101e7e65547310067d6554731005df7354731055dc73547310075d5354731027d6315473101cfe759833102e7e759833101c7e7598331004fd759833102e7d75983310047d759833102cfc759833102cff7498331014fe7498331004fd749833102cfc7498331024fe7398331024de739833102cff729833100cfe7298331004fd729833102cfc7298331006bf4298331006b
  | 17 => 0x56fb309825302ef8309825302efa2098253006f92098253004ff7458253014fe7458253004fd7458253014fc7458253054fc73582530cedf5358253056dc5358253004ff725825300cfe7258253004fd725825300cfc7258253006bf4258253006bd4258253004ff7158253024fc7158253056df3158253056fb70582530cefa5058253056fb3058253056f83058253006fa2058253006f92058253054fd75d8553004ff74d8553014fe74d8553004fd74d8553014fc74d8553004ff72d855300cfe72d8553004fd72d855300cfc72d8553006bf42d8553006bd42d8553176f651d8553006f641d8553006f541d8553006f621d8553006f521d855302cfe70d8553004fd70d85531a5be7498553005bd749855319dee7298553005ed7298553006f761985532167f6518553026f66118553006f56118553054fd75d8153004ff74d8153014fe74d8153004fd74d8153014fc74d81530f67f54d81530067d54d81530f6df53d81532967e53d81532967c53d81530f6dc53d8153004ff72d815300cfe72d8153004fd72d815300cfc72d81530f67f52d81530067d52d8153006bf42d8153006bd42d8153024fe71d8153004fd71d81530f67f51d81530f6fa50d81530f67c50d8153006fb6098153005bf74581531a5bc7458153005ef725815319dec7258153005f77158153005f47158153006f96018153054fd751815302cff7418153014fe7418153004fd741815302cfc741815302cff721815300cfe7218153004fd721815302cfc7218153006bf4218153006bd4218153024fe7118153004fd711815302efa50181530aef95018153004ff7458e51014fe7458e51004fd7458e51014fc7458e511467f5458e510067d5458e51026df7358e51146de5358e51146dd5358e5122e7c5358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e511467f5258e510067d5258e51006bf4258e51006bd4258e51024fc7158e510267f5158e510267d5158e51026de3158e51026dc3158e51004ff7058e5102cfc7058e511467c5058e5122d7f7494e513757d7494e5101d7e7394e5101f5e7394e512167f6394e512175e6394e5122e7d6394e512175d6394e510065d6394e5122d7f7294e5136d7d7294e513673f4294e513673d4294e51217767194e512157d7194e5122f757194e51005757194e5101e7e6194e5101f766194e512175f3194e510057e7094e5102cff7498251014fe7498251004fd749825102cfc7498251054fe7398251004fd739825102cff729825100cfe7298251004fd729825102cfc7298251006bf4298251006bd4298251024fe719825102cfc719825102efa709825102efa509825107ef95098251026fb109825102ef81098251004ff7458251014fe7458251004fd7458251014fc745825106e7f54582510067d545
  | 18 => 0x40200068008000000001003c00a00c0010038008006003801000a000000004c0040000050040002000000802002600000100000000010078014000004013800402a0000010014000000000000000001200000180000070050004006002005000801001b00080000080020000004002004003800c0080180020000004003015000001c003000800001000000d80240080020040000004001005800400e000001803c014007001800801600000000040060060000008004000002801c00000c0078000054043001800002200100500000040180008000016002006800c00601500c8028018000004000800a0060008038010005001001000000c00f0000018013009001000e000000000400a001005000001201c002006401e0010008014006003000000400200300a80140040040000018004000000807c006001000000400000000000a0000007003802000800a000000401e02c000001401202900980240000100000000014024002800000e00100100480000370000010032000000800801e0000000000000007000800805001d00000040000000008004000000007800000a00300080180000010048058008005000002c0060010020000006019000000c012008006001802000d0010000000000005000003000100000040360090008010000000000000002e01300180000000020000000000001006802801a00900480000040010000070026003000005c002002003800000600300300080080020000024000003001001400e000006802800e0010048000002002000000802e00200c00c0014020005800400800000000100000110018000000001000802800200700000140000000000014000005000808404202600000040020400000000002000000802000000f0010004022000000001002000600580040020010080000000000000000c00c0080000008004001000000001000000100000020050048004008001000000000400e0010018006001002800000600100080000140010008024008001001000000a001002000800e00300a8008002001004ff7458653014fe7458653004fd7458653014fc7458653054fc73586530567f53586530567d5358653004ff725865300cfe7258653004fd725865300cfc7258653006bf4258653006bd4258653056f77158653146f651586532167c5158653056f73158653056f43158653006f62158653006f52158653004ff705865302cfc70586531467f505865302cff7498253014fe7498253004fd749825302cfc7498253054fe739825302cfc73982530567f53982530567d539825302cff729825300cfe7298253004fd729825302cfc7298253006bf4298253006bd4298253024fe7198253004fd71982530de7c519825302efa709825302e7f509825302efa50982530def95098253
  | 19 => 0x79c000000091800110c000562207963c60922e1c3cdc400200000003149a10000f30000a370002a557701ce19aa4b14f435900017d56e814000000000c462b468833833482b3eb13b84a65f04a51ffc19e7080ce80f48c6000087aa494800001d900000040060004008001001001408e00000000140080010020090026006000005003e024000800003e005000000001a00700000000000010008070002001000801401800c0018010004002003800000a0030020004014000000800c03a007004002801001d002000c000005000000004a02d0000000006015001802400000000200000020000018000012000001000c010007004800c000002006800000400100900000020020070000000001007006004c001001002800c00b000000001a0000010018002001002802400600c000006c02c0010060004004001002000000c00000200280000000000028018005000002400a0090010054016005002801c00200100a80180000030000010002000003800000a0020010024006002002804800000a0000000012006001800402a001000000800a0000028000000011008800400600d004800400a000021000800200f000800000c000002802c044004000000800000400000340060030068004004002000800c01a00100000000020070058030024000009800800000100f002000a004000801c0140000100014000008002801400401400180000000000008000000001001803c0000010030000000001004001c006001002002c01e0020020008008000000001001a00600080040040000008028002000001003c01c005001802c016004012801400401600480340240090028004000003012000801c001004801800200f000000c002039002800000c0000038004000005016800400c000000805400200800080080020000020020010000000000c000019000008400e001000000000200c00400000120030010038002001001000000000000500000280010000004000001004009c01000301c80040140100000030008004000801400400c000006400a00e0088040000006000003400000b00280300160010000018012000000000400c003001801c00a001007001800600400000180260040078000078000001012001e01f001801003a000000802801000a0000020000005000000000801900080240280050030000080000005000801c000007001000000200400000020010228000048001000000c00a009000000400600500c00080060000010004002020003000c01400c002003c00a05400f800800000100000040000120000000002000001001c00e0020008000048001001004c00000200000000000030010088000001002000400000300100000020060008020008006000000402e001006000800a001004000400400400000200000580
  | 20 => 0x2d3156e6693f395f87820034bc1cb4f0200000019457fa9b15f2ade8000a4e43caa7cddc4cf489000038227a153210073e15905e226124284115f2af063600011a800000066c3e7ac1d3886075710df4b66abd3c201f11c400033982f495876000f9b2c00000023b00001f40f90001cc8000000360285cd500001f5032c06a00000000010d400010c02e014ea6348709b000048307b9dc4cae4713ba80005fea0f18b04593bc63d1fc8128ade2e026d89540007f45ae9b9c000000581921cb0443c0822f88e663400a396dd01a30c35dad9c00000000025e54967405dea7296e26485030e50a40b8e0001a480000001b61f4cd7886900026d80003e6212265c0000003e0a8b5810248161072835e58d55f044d170039277a2d84360e42c6060093039d437126532a0001a11d300d054f41c1e9181c2dc4512108acc00019f800000087c40b0000000000000085800000056e000000096635b00000004860002f5c710174000103935a000432208d03e9092a8ae680d21ba44e1cd05164af0c8b01d7d22c53f814311f895533c916ca867202cf00007767fe0ed2c187b0a1c033aacc6a820e49e871570c8803de065c4f00000002b6c0666af38907b146069f28500000a67353d42d7ced68f725aaab8a4e6a40001a003266cf00000003fc0000fe07dd62ebe10000c100006dc000209c000b3e090800000048847c12f17767834ab154078a5c100013fc386b4626596e002669d3c50010024a1d6008aed7d89531911910b48be600007fcf7a0004792eb000083c51d00000003a30f9168c86ebfe49589f184eb0e572099052a1e70300b40cfe52d5d114780000000f59a2400050760c073c724bf53bb8000000b2f0000000a1a0005ea000000000025687d889eb844540000abc0005128000e5e00045509940005750000000000a0e0000bc0e204bb3a983f877e1ab00010240001f507616c4000000000000102241b0588a9c0005345d084e8afaada3e6297490473a39e8c0421c90d1fc19709c20001ea98640005352d5a21c000b883b4124ce1c8cc28e20106640001742ad800091a07310497547d54d70f9c4be54943a0000ef88564f10248e3ea2a5290f9098800033a05187a60000000000dc01d600018c4974a314cb00000de000000000000000000000014ec99a5de000051e663000000000088e0bf035480e00040580009c400034780002780000000001300ae90002fac0628bc5cf0000d1a0000000ebc0000db40003a80988a04a1a4780e8628373000036e9f523d26bd1567bb3bf000108835d60b880c24e7760648c7887016733f1a08bc41d310688a4c665df03e80007fc00041297011d45ec26720ec02aa8c27493002765ed3e3a22c1ea8ba28e893840a0000001ef80000004df00000001330001168b5200035f814543255b2051
  | 21 => 0xe2c5d60000002e800f2c155da9da4f0408143d23286e25085b122117528960000000000000391800107c1b41ffa14c04e000000000000034a53cae400006a33a907b45dab770001849640652000081c9be5ee5e680000004fa4e3a570f4c1aa0de0dc83f03935db0418e7c5d55e5a70000026108ba5786f0b1404f1268b34257000033119238e52f80004d244e3ac800144297e0002c2c88c57a1c82cdc0003b00000a60f6c2f82961b7ccc48cf2a72d78de292d4012dd8ce2b643fcaf2864600042eae9456252300000000002b53ac289049e53146f91c00006400000000000aeb59c845127647d436a3915d09060001730000b100000670000a870001000000000000000116e14403596d40000000d122b80000005e7834800064d6101e6400016e3e71b1570a4032f980009020002009a782982100000001446af645210c427c8c2613000045e6544ba000062231001c1ab447a00013a042d2be00000016f02904940a98000c70000000124918c0000002df85203f00000c3888244b000000018c0003a8800024cae3165aef8c0ac1f3e68cb40009a833425d40004bf0462d5c5326f85b9171ccc217b3cb871c0900953b2107d2c0b2538c24b93c2b11197ab306320412aeaa048cc4a43329e480000000000bc8000456061914000000023719f400060300024fd02473f39b00280006ec0000b340008e3395a7f138200051c138c48c0000000bc453e1851952cd8c0214e41817d889430737bacb0c526602b005052040003bd82bd2925a138b902c46068c54f08c4e9ac110ab07555108330b508185065283dc88ed4c865d0980034188bc756101382a00000001de042e8d43fa9df400000032306f8b6c5710d4a9283a499c00000012e4a131428000000a280000d1c0000930be0000000000453000134e6b852891f000092f15c00002aa9382de925450e54018188201c0529511150939a5e31ad1c0d09e2f331013282580105ca000109a63a5a5800000000028d1288a3238c2472054cbc57037509a89ac97037f9f65836ad315d00006d40094940f3cc2070a00000000000000002334f3a48f0000000000070614a18ce2c45d0368280732a6f37180000006ae0b42b357aa79325ca9d4e502c10000fc80003c4010800029e93700000004b0b0956b9bd0000000301000081051100014954524a900000007380000002064e7000027207a8000008000000000004f000000052eab059d151891aa473130000cc84640001968000b8d0001b400006a06030000000b8a000000136420c0000000e8c00047a000000058b22483bc8181de24508d961000000000006c2440000000000078510ca50804a03e00004280009fa00000000003a616730089465f93180000c14568017a6ec0f4000593800174c4b03b080000006d14a380000000000001aa4064
  | 22 => 0xb491b99fd872c94e1faa1500009f60a69188dca03b1468e2558ea6a000235581e6d257d8000b8678d4560000f127dc03a96d00002813f11fb8e0087e1e50d9cfbc3fa1e40018baea90185226847200055280006c000058500000000002ccab9c7e8a083a5934c4983b55c608040ae9e02119e20e92a9d0000abc0000000000000e4890c000156459ea6925024e479256300795b49e43e029596484f60000002d48a720003768e1d56290f5701e885181c65e495d800000000000004960003f2aa615400000002d1000000000023384a23260000001716bb4419000000079f0000cd00004ea2729d20b882d5570a9ac000a1f4c98d6151cb351d49a3840014a615148827a5ef0000f740003b10000ce40000fb000155000000030fa48d68e2e72f500616fa9d84e790bc20200045dafec9ec24a00022c57f232e0002a00000729438a90cd4e76c00013d0000b1600028bd6f8aab60d04d8bd63d653d99613543e918e80000008a15d80480000af40000000cce00000000b079c558527acd075a000000000083829b000110c17c00000018707be7eb59902a800034c28c29dce9c0003ea00000000003ada8cd160abf40997643061023661520f2cab840e9ea87146a241715f085c0003122aa968a132005aa504ac32b2d41d40c2c5e602d00000ee47e0e6ae246ec4a108623f800000023c1eb08a88623810bf575eaf02c204653d46d437400000000001388000000000000000000000059987e90e090020f21980f600011b869c22400000025100003b92e7000000000054889814c07bf586acb8134ad204ca23caf60d024ea76937e00056b14bd2baa781150dd4bf655a4a91cb07bc6503b7025c0007ad36c13e55144e616c11d47b20ca0e602d886caa64fc1820830b6c57c2650c445375f22ded51e0002af9fbc00000000000000009c30520000000bda10f92012141053b801fd2d8502000163d08a62d2a393509b884e0001e9477854d11215b800000000007d0000bde0f405c42e0056000000128215f3162e581e80005dd00011880b315c993000000012c9dfd33e62114905b00009c200000000000000c78000aaa00000000000008c1000000000069100022300008ee00000006d01634f319543c051f000000043c6980bca0154da00000000000004ec5dc80001e200023b8000a98a4503c1148b440000002d4c00011b16b24d87a09e300000000c6b9b5a8000161e24200008740009b930c011055c00002180003183c7000192400000048b0000000000000000000000000019ec33e2d95b1a740cd45094b2aeb8c3a6c13ab0001780a7f5411f74000ab200daa8400000038c8000e54b754b52da800000051a9f841822ca3119bec8de72200014b8000ac800e800178600034289c800065327e80000009b557b9ee078c00000023480002dd012
  | 23 => 0x110a46586c85f505882faa7215a28b105233d4e8af10b9000000028253780000000000000a555788114c5c37006e1e3d81a13752412e140070d5f685dc49200000017608f27441228000000be82398828ba615421a04340dc1d017500005d81a831c915c0001b05fd20fc62807117e036147859c0ee01a8f4678b47aaf44000459340a8b851291d562a6d014a45134d062cb2683a52a0000f1872e0002e4cb2800009480002126b5000014000098207499c000000004a00000006ef2168000fd000000000001b40000001c1400070b41b84000002251920940a944692d38000fa47b400000012b200013b800000084a174800000087b582882474ab5c3648000544b7047581614ac187068876c14202639c8000000690335a41444017a46e25fc38433100000001225f2444000059053e1f702ec27269323d80017a600019e1f6cac200000000011b21890b49d70e2a000554000000000000a000000053338d0000d4a9a44a5a2fc0000004c60b10ff8afe5ad918000062a4b7b0151a0c221358d4870253c44dac104c40003d71f209a4b435ff97d0000029264a3c41f8294572aeb54f80005c884fd0d688d40a000000000025703652dc1f3541a10d7ba16642a8174364a3243a838ca00a991e18fad0ec95419b1f9129045f2c8145517c4d915b8b18de0532000000000000000021cc0807955fe2b7c5dc02b3a08001128b800469a0c57899d5360b0cafe7f318900000000000000dbd5382143f51f8ccf06ba45380011c20005a700007849074408fcc9162df3af11540ec4f72858ad867033705b82997e263617206206f21244928000f42b83573065800042601e000000063f1aa9f400740f61b480000007af0ae80001d664a00007602c850e44880000000005449e451dea1e56592a8ac4c283dd18d4b3ab4818e2fe133c93e28d996d1ec2e239e05fc4ba9bd2612380426a3f5d98ea0ab82d260902d03805572eea7396c09b73b91a2ca964dd000306462eb590432c4d01419020eb08487a0ab109212034a3a417b0fb03f65d61909c117a41081e8817c0fc35e5bcad847de8391d614409d00e15c10fecc8a1d750097a10a46fe5650454ae832928904d03ca61a5e11e417b239b2f08b846c6be34950c18000b2921f2904c2a6b14d811b49aa08925b0db929818d1be22cc00065f1a21fecb9a89f423a6211b43a10000000f404155a78000f520004c700000000002f8ac652400001d5b0ac8d06423379b380a41250f48000df24e70c9000134a00056a286800000000000012c431a192800114677a0dc8e015b04b44f6ad2800048c0f080003c87ab307abf01a86324f60610292809000000000000000000006160000000000ff41e357aa7700008e73e004bc0009e82fe0c9d1a667230000014160000002c8400059f076ae1d67062727e0b950b
  | 24 => 0x436660e85cc2a45db2641d0c0000805e08b6c0000004309d291042f94730ed1812b5450a0a117245031201498ae47b20000f88a28bab0ad8258b9639140396ec11e41a1ad85940e42fe47292c42de0001fe8afc00000000014f4c9c730580a7b8a021a04b40e547da8211340000fb000052b8b7805cc25000111d2ec6ab4e3005c5b400033322650067f860a184442a67751e9bcce388c33fb9e6800095102e000000030f000011882c000437a90800040541303f40006fd370a7e4150b4d095a47c4641cb000069847023f08d1380c967421800e78908b5a5fb85ad3708c0000000000016100016a83b28b500000006d683d17b82d4598a2b3e50109190b122a2ae9168400021027240005c200024a41dcb230140058000aaf0000000dd237f21427d0e8a2d334b0c24d7c7665371acd3fe0005b795a4ae66bd60f0000000333594000018a0003c00d5c000a394ab96fcfae00035b89d893e1b60c09698da600e3f61b740e643f00000014cca0747e9241592b415bf9f24000000000000000004b3b39b185489330c700018464671268798000000523000000000019000000007860000000796c0c5d922944f2b8125f00017e6a74155220d4ca7543f8ab040003844e62cac0002d707fa98931a3bd05fa7487b8ad524f22554fc4174dd1a28aee6da4b589496304ed24480000003e1000280c0000005e327dca2ead102a27c80004ab00000000380000002e6532473b58f800045a8cb000000163a6861382f9d24c6c219f0f6d6e67b314e27957a04b755c80015daa052fc051547610347d17700008f925426acf8aa5344905d48bc11e0002c7172a2960cf129c1ac9690f8a3789388f358100000000002c0280844691b0ae2604c264b21239618626889000264400025a3c38ee05404fb4ad16c025a0ae1470c213209e40f79bc96369031a08fa04588352158e080005981a78ddd44eaad1e689bc1ca64727c266ce1200041008080004910000f4818e3a03371aa8b0a75f3b28000e3c91845e89b83dc79824daf584340003b6826cb227014f82764b061512599c1800000059d847474e1990fc87f48d46040000000f3c0000000000d36000000083c00000000000000000005f800000000002b50001408a1200000000000000000000b8c0005518000cecc0300016f80022c906006600001101ed06b0000c0b000000010a8685d3ab6451041018693c50580d359699f10ae000407965c00080e2098000d7200000005c8c68000266ac9901898a000144c43800039080017de000219172573899947411d128c8c54990dd01067b550c1728d320a207c10e4000a0c4fd80001ba000056105000040d3f9165817285940d08880005a00442db4000b51000000037600060210d400098b0000c7d5745b900001840000000002de0dea37a0f810b016486c09
  | 25 => 0x8f84d50209852f4989544082429f9bf00000a3000000057ac0023f80d00602c70089d3c0002ef4ac0ecc000c0a136a9702ecbb134bafd800000014329a0000000000299c00000000006d40007b744280017982a1000000000071b00000015260002950000500b660000aad18e0004d60a4cc2e84948989113a83be41b16c8ec48934eb286d2083284be071020e58e2fb88b806c4c60a120044e691508c05e15525784bb9b58f60b552688ab4b0e12a0168ea80008504781c4c0000003720000e184065ac28340000000000fdc32844c1bf2060e6e0e74f781253e65d113f8d2131e5d41a188980000000002e8d0be43b0b020896347274ea99e800000000020bc00a9271ea15ac5f4157000274c0005445798000522828403179455000015922a44fa1ae00023b4d9a9300989e392f493c26182c15f29c52d78000dbc1df54d15953d600002d856115e85e000190c0000000002f6068c7c232b10e95e40005ceaad476c5c51bd993d72e7e900023b149a00013f00003700000000000000000393206d4fa0983aead000005ac0000000860bdc2020ab094c96322692f4d4cabb48a297810ea580a1ab3cbfa00018aa16884e00036da940f382fb0d694e93ce8dd5e70d157c0922171911099800006b8cc08c200059f8d7c8325061b6aa9c0000c214111ac03ca7041a13400000001199bd87c652111e21715808b42f21c44e62a4c5ed800025c5893e893cd1d2b6e0001a1ce0e0652b600002da90b4f887241c469418107515489a3298244415aaee154a8f8bfe6b21d7022ce8e9fd4041dbc0000004d0000000000048e00017e800043e80000000000002cf55baa0a4cc0e340000002cda0c400023a000304c70c00059e17484b81bd00c8000000877054800000000000000008a66ac000072000084c00000000002b30001214aa4b224b9808ca1e3054eb8d244c64c7575173c00019519d27216ac1862ed246410404d1a9a72c000a8600006fd73e0000888000000c10459000000000044f019000000010580010b653845c9dd09ae0000eea841516a713e5884549200043296040009673d8800000060e5989878b5a1825429778f2800027a9ff47800005e42b4045006c4c1a274f8893116a0c60d6087f52d962976e0f24b6a4411fe00000000000004972e815056ca00000029680009a60062dac00e9df000023911405e3b98000000897000000000000002ca07142c61b44800001383fc5cc000144c0e860b00fd05a3b73062ab000000035a00015d80000001d8d66000046b800092c00022100000005fe336a6cc19aade57f821000071d000000044e0903440154250275000000069600000029cc6ac0001eba56c0000003abaf146b859556300000000001dd259000025e30580a98389dd1b123582b482a2fd2a34aa60374c3052c81e1e22d298dc8
  | 26 => 0x75500000012f6000000000000045813390cc00000056180017e40000001458ed400030300008426ca0000000a4856729d82291b60002ab00007440004a000000007c625283cd7dc00030a00000006eb04e8e5cc7c00038a28d96187a7262a490d888602241194af22345ef8904a0a9a221500000000002129a705a22c03ed000070a0002d71be80400ba00026a49bc6590002efc5340004a689980003f11b208f869c00031e23ec0008463069f0cdb21d152c8fd80349e91a800010f05e017a80000000000002be8000000000095156846c0001c94844a153ad2910a0819b46c000152ea1153086840000005921a849d6243011261d02e5ba3f02514c820de000000070685100026107305644be847040895058a80000000000d88a8c0cc9083bc9a54fcc0df5d425c4a6c39a36a99d45142f44b0aa6d3b647227f03c0d8e63b5420a743482e636180000000001a680015faa9626d000053c84b567027d468351480800044215e0001e6c8220005511f7cdae2a5158262445658849ab0900004454a7a4d000087200024e915a25b1b28cec00004700006ccd084c10d19fb56d28671c7ada0000b8f1f298bc9e09fe59504e019000048b93615deb000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xad4815d5630400159d053a2c608002b360a7458c100052f428e8b182000a5d851d16304001c3ea92a2c608002a7a127258c100054ec24e4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b182004ad6811c963040015ab02392c608016b6a007258c100056cc00e4b182000a9e84949630400153b09292c608012b5a065258c100056ac0ca4b182000a9e84149630400153b08292c6081c2a76124258c1000747c1284b182000e8f725096304001d18e4a12c6081c3a3c854258c103874690a84b18206fa9e84109630400153d09902c608002a76132058c1000746a1640b182000e8d4248163040018bea6bb4a6080161fe1d6594c100052fc1acb2982000e1f5359253040074bd0ab1ca6080161f2177654c100247a40aeca98200587c875955304009968e2b22a6080163721d6354c100063ab2ee2a982000cb564dc553040019aac7b8aa608002aba13755881000556c26eab102004ae681dd5620400d5cb03baac408002aba10755881000556c20eab102070aad879d162040dfd4e213a2c4081c6b9e0574588100257240ae8b102000caf875d16204001d4f02ba2c4081c3a9205745881038657b8ae8b102070cad715d1620400195ee0ba2c4080032b5c1745881038753882e8b10206faae841d16204001c5ea92a2c408002b9e0554588100257240aa8b102000aae84dcd620400155b09b9ac4080032b5d2735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881000656ba0e6b102004ae6811cd620400d5cb0239ac408016baa00735881003574c00e6b102000e4f5394d62040015cf02a9ac408012b920553588100047743e86b1020008ed87d0d62040095cd0321ac408002b960643588100053742886b102000a6d8510d62040070fd0abb660080163760d76cc0100f43fc32eb9802000c3e645d730040158bcc6bae60080031b98975cc0100443fc3acb980200087d87597300400187ceab2660080030f5d564cc0100062f3aac79802000c5d7558f30040018dceab1660080031b5d562cc01002c6e41eec9802000cb474dd910040018ef0bbb220080031d21776440100065bc26ec8802000cb484dd9100400196e85bb220080032d50b76440100063bbb6ea8802000c77761d51004001a68e83aa20080032dddb74440100055b43ac88802038ab4875911004001c6eeab2220080038d1d564440100055bc12c88802000ab582591100400b96ee0b222008013acdc1644401002f59282c88802005eb2305911004001cceeab122008003991d5624401000753422c48802000ea5845891004001d4ee8b122008003a91d1624401002e73b82c48802004ee370589100400bdc4a0b122008017b88c1624401000758b22a08802000ee1625411004001d62c89822008003b85893044010
  | 1 => 0xaebb2460880021fe15764c11001c3e42aec98220008bf845d9304400517908bb260880023be09764c11000c76412ec98220058f686dc530440018e8cbb8a60880ff1d9db658411001e3b3b0cb0822000e3464196104407b96cedb2420880123d205745941002c3f43ca8b282000c3f74951650400b0f90eaa2ca080161fa1e52594100051f424a4b282000a3d8494965040094ed03292ca080161f21d52594100061fba4e8b282000a77815d165040094e902ba2ca0800317dce73594100253a40ae6b282000a6e82d0d65040014db05a1aca080129da0643594100053ac0c86b28200087e8710d65040010fb0e21aca080028fa1272594100051ec24e4b282004a76819c965040014eb03392ca080028fa1072594100051ec20e4b282070a3d849096504001c5f04a12ca081c38bc8542594103871690a84b28206fa3e841096504001c5a85992ca080028fa1232594100051ec2464b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282000e2d420c965040094ed02192ca080029d604325941002d3d40064b282000a79800c9650400147d09902ca080028f613205941000716a1640b282000e2d42481650400187eeb3aac8081d6ade0575590100255a40aeab202000aae82dcd640400155b05b9ac808012ada0673590103a55ac0ce6b202000a3e851cd640400147b0a39ac8081bf2dc4372590103845ec3ce4b202073ab7815c9640400956902b92c8080032be0972590100065bc0ae4b202070cb4815c964040e196e20b92c8081be2fa1c72590100045f43ca4b2020008bd87949640400956d03292c808002ad60652590100045f438a4b2020008bd87149640400195ae5992c8080022fa1e32590100045ec3c64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000cad720c9640400956d02192c808002ad604325901002d5d40064b202000ab9800c9640400f17d0f902c8080022f61f20590100070faa4a93182000a9e8494a630400153b09294c608012b5a065298c100056ac0ca53182000a9e8414a630400153b08294c6081c2a76124298c1000747c12853182072e8f7250a63040e5d18e4a14c6081c3a3c854298c103874690a85318206fa9e8410a630400153d09904c608002a76132098c1000746a16413182000e8d42482630400b1bd0fa9ac60800317dd75358c1002c6f43e86b182000ace82d0d630400159b05a1ac6080163721d4358c100052f42886b182000a5d8510d630400195ee4a12c6080072b1c94258c1000746a1664b1820058de878c9630400153d09192c608002a76123258c1002c6e43a64b182000a5e850c963040014bb0a192c608002a7a103258c100054ec2064b182000e8d420c963040095ad02192c608016b6a003258c100062fbaceab182004
  | 2 => 0xc20d91100645ec3841b222000a3e85083644400147b0a106c888002a7a0c20d91100054ec1841b22203dab681083644400156b02106c888002ab60864d8d1000e5739285b1a2000cad7250b6344001d1a84196c688002b560432d8d100056cc0065b1a2000ea542487634400187ce9b2cc6880030f9d06598d100061fb2ae931a2000c3c655d2634400187cebb24c6880030f5d76498d100061f3a8c931a2000c3d75192634400155b04324c6880021fa1f6558d100061e3a6cab1a2000c6c72d9563440010fd0e32ac6880030f1d06558d1000636390cab1a20028be86dd1634400187ecbba2c6880030f1977458d100045f43ec8b1a2000c3f75d916344001878ebb22c6880032b1cb6458d100045f438c8b1a2000c3f751916344001878ea322c688002ab6086458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a2000c3f75dd16344001878ebba2c6880022f60b7458d100043fc2ae8b1a200387c855d163440011df04ba2c6880063b2097458d100061fba8e8b1a2000c3c751d163440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc9634400195f09b92c6880032b2137258d100043fc2ae4b1a200387c855c9634400117f08b92c68800a2f2117258d100046fc1ae4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c9634400117d0fa12c68800a2f21f4258d100061fbae84b1a2079c3c75d09634400195ee5a12c6880072b1cb4258d100045f43a84b1a20008bc87509634400187eeaa12c6881e30f1d54258d1000657b9284b1a2001cac7250963440018e8ebb8ac6881df1d1d62158d1000e7239442b1a20018f48748563440ed8e8ea90ac688007391c92158d1000752a1242b1a2000aad8219063440011bf0eb18c688002b32096318d100045fc22ed29a20028bc845da53440014bb07b2ca68800387d4f6494d100145f426eca9a20008bd84dd9534400117f08bb2a68800a2f2117654d1000477c12eca9a20018ec825d953440011ef02bb2a68802a1fa1f6554d100552f41ecaa9a2000c7b651c151440010fd0dbaa62880030f193754c510216b8086ea98a206687e87d95314408b0f90fb2a62880030fdd7644c5100061e3aec898a2000c5f659ce504403d8b8cb39ca08800327d9273941100064e324e72822000c5f655ce50440338b8cab9ca08800327d9173941100064e322e72822005dd0105ce504407f8e8e3b2aa0880032d19371541101f43e432eb9822000c3c645d7304407f0ff0fb2e60880021f61f65cc1100061f3aec99822000c3d75d933044001968c8b8e608800e1f216768c1100dc3e432eb1822000c3c645d6304400bae020bac60880021fe1f658c11006c3ec3ecb1822000c3e75d92304400187
  | 3 => 0x1b2a2000e2d4248365440010fd0e106ca880361f61c20d95100051f42041b2a2000a3d8408365440014bd06106ca880029760c20d95101fd3b40841b2a2000a75810836544001878cbba2ca88002ab60864595100145f43ee8b2a2000c3f75dd1654400117b05ba2ca880021fe1574595100047bc0ae8b2a20008be871d1654400187eea3a2ca880021fe1572595100045fc22e4b2a20028bc845c965440011bf06b92ca8802a3720d72595100045f43e84b2a20028bc87d09654400117d0ea12ca880022f21d42595100065a3a6e2b2a200087d8799065440010ff0eb20ca880029de05641951000537410c832a2000a6d82190654400165b04320ca880038ba0864195100051ec10c832a2000e2d82190654400145b04320ca880038d60464195100043ec3cc432a2000a3e84988654400147b09310ca880029d60662195100043fc3ac432a2000a3f84588654400147908b10ca8800297e0d62195100052e41ac432a2000a3e84188654400147b08310ca880fa9da0462195100051f4368432a2000a3c86d08654400187ceda10ca880028f21942195100061f3b28432a2000e2e625086544001c5ac4a10ca880029da1a41195100071a3248232a2000a74865046544001c68c8a08ca880038d19221195100053a4324232a2000e34644846544001ccec4908ca88003c950921195100061f3b6cbb2220008bd87997644400147d0b32ec8880022fe1d65d91100051f430cbb222000c3e76197644400117d0db96c8880030fd9772d91100061e32ee5b222000c3f655cb6444001878cab96c88800a2fe1f62d911000656b96c5b2220008bd8798b644400147d0b316c8880028f61662d911000657b94c5b2220008bf8758b644400147f0ab16c8880028f21562d91100054fc1ac5b222000a9c8358b644400195ee4b16c8880322f61c62d911000656b90c5b22200cab686dc76444001c68cb10ec8880038d19521d9110006d3b9243b222000ea462487644400187aea3aec8880028fa1673d91100051ec2ce7b222000aaf825cf644400155904b9ec8880022f61e72d911000657b94e5b222000caf825cb644400117d0e396c8880f6ada0472d91100055ac08e5b2220008be8794b644400117b0f296c8880f6ada0652d91100055ac0ca5b2220008be8714b644400117b0e296c8880032bdcb32d91100045f43c65b2220008bd878cb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644400195ee4196c8880f6ada0432d91100055ac0865b222000aba800cb644400157300196c8880e2aea0371d91100045f43e43b2220008bd87c87644400147d0b90ec8880028f61721d911000657b9643b222000caf72487644407bd484290ec8880f62fa1f20d91100045ec3e41b222000caf72c83644400195ee4906c8880022fa1
  | 4 => 0x3c400187eeaa12c7881e30f1d54258f1000657b9284b1e2001cac7250963c40ed8e8ea90ac788007391c92158f1000752a1242b1e2003a5c8558e53c40850ff0abb2a7880121f21d6554f100246e43ac6a9e2000c5f659ce50c403d8b8cb39ca18802b1798d75cc3100f52e42ac79862000c5d7558f30c40334b90ab1a61881eb279cf42d96100064eb9e85b2c2072c9e7350b658400193ae6a16cb080072b9c942d961000656b9285b2c200587c87551658400b0f90ea92cb081e70f9d742d8e100061ebae85b1c2078c3e7550b638400187aeaa16c7080072b9c942d8e1000656b9285b1c20058de87d4d63840018beeba9ac7080163721d4358e1000657b9284b1c2001cac725096384001d1a85992c7080163721d3258e1002c3fc3acb29c2000a5f83596538400117f08bb2a70800a2f2117654e1000477c12eca9c20018ec825d953840150fd0fb2aa70802a97a0f6554e100062e3aac698c2000aad82193654400187ae92a6ca880029d60654d95100143fc3aa9b2a2000a3e8494b654400147b09296ca880061fe1d52d951000e5739285b2a2000cad7250b65440014dd04326ca880029b60864d951000596c10c9b2a2000e2e82193654400147b04326ca880038b60864d951000516c10c9b2a2000e3581193654400147d09316ca880028f61262d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d95100051f420c5b2a2000a3d8418b654400147d0da16ca880028f21b42d95103ce1f3b685b2a2000a3c8650b65440f187ceca16ca880038b98942d951000716b1285b2a2000e34649076544001c68c8a0eca881db1d9d921d95100073231243b2a2000f2542487654400187ae83a6ca880029ba0874d951000536c10e9b2a203fa76811d365440014eb023a6ca8800317dce73d95100062eb98e7b2a2000a6e82d0f65440014db05a1eca880021fa1c43d95100043ec3887b2a2000a3e849cb654400147b09396ca880028fa1072d95100051ec20e5b2a203fa76811cb65440014eb02396ca880038be0942d95100071739285b2a2000e2d7250b6544001c5a85996ca880028fa1232d95100051ec2465b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2000e2d420cb654407f4ed02196ca880029d60432d95100053d40065b2a2000a79800cb65440014bd07b8eca880029760f71d95100043f43e83b2a200087d87d07654407fc6882a0eca880021fa1f21d95100043ec3e43b2a2000a3e84c87654400147b0990eca880038b50b21d951000716a1243b2a203fe642148765440010fd0e206ca880361f61c40d95100052f41881b2a2000a5d8310365440014dd04206ca880029b60840d95101fd3b40881b2a2000a7581103654400147d09906ca880028f61320d951000716a164
  | 5 => 0x80038b50921596300051f42042b2c6000a3d84085658c00b4f50010acb180029e60021596300051f42640b2c6000a3d84c81658c001c5a85902cb180038b50920596300063cb2ee0a9c6001cae72509618c00195ae4a12c3180163d21d41586300165a3a282b0c60058f487485618c001d4a8490ac3180161f21776546300043ec36ea98c606787c87595318c03dcb4caa8661180163760f74d953002c6ec1ee5b2a607ec9d73d0b654c0fdc3ea7a16ca981f7275cd42d95303ef0fa9a85b2a6000c74651c5654c001aa8a638aca9800a2fa1f74595300045ec16e8b2a60008ef825d1654c0031d904ba2ca980023de0574595300247a40ae8b2a60008be871d1654c0050f90eaa2ca981f31d1c5545953000c7743ee4b2a6000caf74dc9654c001958e9b92ca980032be13725953000656426e4b2a60008bf845c9654c00517908b92ca980023de0572595300247a40ae4b2a60008ee871c9654c00195ee8392ca980032b1d0725953000c3e43aa4b2a604fa5c83549654c0038d8e4a92ca981ef1d1c552595300045f43e84b2a60028bc87d09654c00195ee5a12ca980072b1cb425953037e5a38e84b2a60008be87509654c0011790ea12ca980032bdc9425953000e5639284b2a6070cb471509654c00196ee9b8aca980032d1d3715953000673b96e2b2a6000ce472dc5654c00196e85b8aca980032d50b71595300063bba8e2b2a6000cb7741c5654c001968e838aca9800339dc8715953000672390e2b2a6019c5f73d95534c0a5ab0a7b82a6980032bdc942d853000e5639285b0a6000ad583147614c0011ef0eb08c2980029d21561185300062fb2ae728a600487c87595514c0094e902b2aa29806657a1676cc5300cc6ec3ecb98a6019c5e75d97314c0095a902b2e62980031d1d7614c5300ccaf43eea98a6042c5c76dd5314c0cf8b8ec3aa6298067171d7654c5300246e43aca98a6000d5475d85314c001aa8ea30a6298003561d7704c530006adba8e098a600a87f87596504c09f8bce6b2ca0980fe9d20565941300062fb2ee6a82600587c87551650c00b0f90ea92ca1800e1fa1f75584300043fc2ae8b08600387c855d1610c0010ff0ab92c21800e1f21572584300546e41ae4b086000c3f75d09610c0f3878eba12c2180030fdd542584303c61e3aa84b086001cae72509610c00195ae4a12c2180163d21d41584300165a3a282b086077c7475885610c00b1e90e90ac2181db1d1d5215843000752a1242b086003a7485586510c00b1e90eb0aa21806697a17764c0300062f42eec9806000c5d85dd9300c00193e85bb260180032750b764c0300cd2e42ac298060008df835c965c40151b906b92cb8800e1fa1f7558f100043fc2ae8b1e200387c855d163c40010ff0ab92c78800e1f2157258f100061fbae84b1e2079c3c75d096
  | 6 => 0x43ec3e42b2e6000a3e84c8565cc00147b0990acb980038b50b21597300552f41c42b2e6000a5d8388565cc001c5a8490acb980028fa1021597300051ec2042b2e600aa5e8308565cc0014bb0610acb9814b171cf70597300051fc22e0b2e6000a3c845c165cc0014df04b82cb980029b20970597300053bc0ae0b2e6000a74815c165cc03d0fd0e202cb980021f61c40597300552f41880b2e6000a5d8310165cc0014dd04202cb980029b60840597300053b40880b2e6000a758110165cc00147d09902cb980028f613205973000716a1640b2e6000a5f8348165cc0154b906902cb980038b50920597300f43f43840b2e600087d8708165cc00147d08102cb980028f61020597300552f41840b2e6000a5d8308165cc0014ed02102cb980029d604205973000657b9284b0e6001cac7250961cc0151ed0fa0ac3980032d5d0415873000572c1082b0e60018f48748561cc0039c8e490ac398003a9509215873022d2e41acb28e600ac5e7359651cc0018bacab9ca39802a1f217765473002c6e41aeca8e6000c5d65dcd51cc0cd2bd0fbaa639807a3721d654c7300f62fc3aca98e6000a5e8759531cc0014b90eb2a639807b1721d654c7300f42e43aca98e6000e1f4259531cc001c3a84b2a639802b17dc5654c7300572bb8aca98e6000e562159531cc001caa42b2a639802b179cd65943300ce2f32ae72866000c5d655ce50cc00b4b906b2aa19800317597735433000e5739285b2c6000cad7250b658c00147d09314cb180028f612629963002d3d404c532c607ee1d63d0a658c0fbc3ac6a14cb180038b989429963000716b128532c6080e5963482658c001e5284904cb180161fa1e54596300061fba4a8b2c600587c87551658c00b0fd0f292cb180028fa1252596300051ec24a4b2c6000a7681949658c0014eb03292cb180161f21d52596300051f424c4b2c6000a3d84989658c00b4f501312cb181e70fddb42596303c61fbb284b2c6000e2e62509658c001c5ac4a12cb18003ca50920596300061fba4e8b2c604fc5e73dcd658c00147f08b9acb180028f211735963000537c12e6b2c6000a6c825cd658c0014ef02b9acb180029d20573596300053741686b2c6000a6d82d0d658c00147d09392cb180028f61272596300053b40ce4b2c6000a75819c9658c00b4f501392cb180029e60272596300051f420e4b2c6000a3d841c9658c00147b09212cb180038be0942596303ff1799284b2c607fe2c32509658c00147d08212cb180028fa1232596300051ec2464b2c604fa5e831c5658c0014bb0638acb180021fa1f41596300043ec3e82b2c6000a6e82105658c0014db0420acb180038d504415963002d3d40082b2c6000a7980105658c0010fd0f90acb180021f61f21596300051f42642b2c6000a3d84c85658c001c5a8590acb1
  | 7 => 0xf4875056194005968e8a0ac3280163d21d215865000752a1242b0ca00087f865ce519408b8bcc6b9ca32800395986639465022e2ec3cc728ca000e1f4298e5194001c3a8531ca32819b179c663946500f72b38cc728ca000e5563586519407d0ff0cb84a3280031798d70946500562f31aeb98ca00ac5f7654f319400b1b907bb263281171798f754c6500062fbaac698ca019c5c7558d31940072b90ea9a632802a97e19534c6500062fbb2a698ca0058dd835d831940158bcc6ba86328067179d5630c6500062ebaac618ca001cae7250b635400195ae4a16c6a800237e1d6318d500ccaec3ec729aa04fa5d87d8e53540018bb0fb1ca6a800387d0b6394d500070ea16c729aa00087c865c653540014eb0ba0ec2a80032ddd041d855000572c1083b0aa0018f78748761540039cce490ec2a8003a950921d85501fe2fb2ae630aa0008f787584615400156908b08c2a819e1fa1f635455002c3ec2ced98aa0048de839db315409f8bca73b662a800e1f214764c5500062e3b4a698aa00487c859d8315400117f08bb062a800a2f211760c5500063abaec218aa04fc5e869ce5054001a3e8539ca0a80034750a73941500062e30ce7282a005c5f609ce505403dab6c139ca0a800e1f61f639415027e2f39ec7282a00387c865c6505407f8e8c2b8ca0a80163720d74597300543f43ca8b2e6000c3f7495165cc0150f90eaa2cb980163720d72597300543f43ca4b2e6000a3e8494965cc00147b09292cb980029da0652597300053ac0ca4b2e600187c8754965cc0154b906a92cb981eb271cf42597303964e39a84b2e6000caf7250965cc003958e4a12cb980030fdd274597300552f41ce8b2e6000a5d839d165cc0014dd053a2cb980029b60a74597300053b40ce8b2e6000a75819d165cc0014bf06ba2cb9802a9720d74597300051f424e4b2e6000a3d849c965cc0154bd07392cb980029760e72597300053b40ce4b2e6000a75819c965cc0014bf06b92cb9802a9720d72597300051f420e4b2e6000a3d841c965cc0154bd07a12cb980029760f42597303d70f41e84b2e6000e1d83d0965cc105c3ee7a12cb981eb871cf42597303d70f98e84b2e6072a3d8490965cc103c3ee6a12cb981cb871cd425973000717c1284b2e6000e2f7250965cc001c58e4a12cb981cb8bcc942597303971619284b2e6072e1f3150965cc0f547d08212cb9802a9720f71597300051f424e2b2e6000a3d849c565cc0154bd0738acb98117171ce715973000537414e2b2e6000a6d829c565cc0154b906b8acb9802a97a0c71597300f52ec18e2b2e6066c5c731c565cc0010fd0fa0acb980021f61f41597300552f41c82b2e6000a5d8390565cc0154bd0620acb980029760c41597300053741082b2e6000a6d8210565cc001c6a8220acb980021fa1f21597300
  | 8 => 0xe202ca188021f61c40594310552f41880b286200a5d83101650c4014dd04202ca188029b60840594310253b40880b286200a7581101650c40147d09902ca188028f613205943100716a1640b286200a5f83481650c4154b906902ca188038b50920594310043f43840b28620087d87081650c40147d08102ca188028f61020594310552f41840b286200a5d83081650c4094ed02102ca188029d604205943100e57392853006200cad7250a600c401d5284904c0188072b9c9425803100656b9284b0062048f887501600c4091f10e902c018803aa50920580310054f424c531ca000a9d8498a6394001d1cc4a14c728003a35894298e503d70f3ae8531ca082e1c51d0a6394105c3ea1a14c72800297e154298e500f52e42a8531ca000e1f8550a6394103c390aa14c7281cb879d54298e5000747c128531ca072e8f7250a63940e5d18e4a14c728207871454298e5040f0fa828531ca01ea5e85d0663940014bb0ba0cc72800297e154198e500f52e42a8331ca000ace82106639400159b0420cc728003a55044198e500f52f42e4331ca000a5d85c86639400153d0990cc728002a76132198e5000746a164331ca084e545188663940014bf0a90cc72807a972152198e5000746a124331ca083e5451486639400153d0810cc728002a76102198e500054f4264131ca000a9d84c826394001d1a85904c728003a35092098e500056741686b1ca000acd82d0d639400b1b90ea1ac728002976144358e5000657b9284b1ca001cac725096394001d1a85992c728002a7a123258e500054ec2464b1ca0058dc874c963940014bb0a192c728002a7a103258e500054ec2064b1ca000e8d420c963940015ad02192c728002b56043258e5002d6d40064b1ca00ac5e75dd963940016a902baac728002a7a126258e500054ec24c4b1ca000e8e625096394001d1ac4a12c728002b3a0a7458e5000566c14e8b1ca019a5e851d163940014bb0a3a2c728002a7a127258e500054ec24e4b1ca019a5e851c963940014bb0a392c728002a7a107258e500054ec20e4b1ca000ad6811c963940015ab02392c728016b6a007258e500056cc00e4b1ca000e8f825096394001d1ee4a12c728003a31c94258e500052fc2ae2b1ca000a5d851c563940334bd0ba0ac728002976174158e500056741082b1ca000acd821056394001d2a8220ac728016b6a004158e500056cc0082b1ca019a5e85c8563940014bb0b90ac728002a7a132158e500054ec2642b1ca000e8d42c856394001d1a8490ac728002a7a102158e500054ec2042b1ca005ada8008563940015b30010ac728002a7a132058e500054ec2640b1ca000e8d42c816394001d1a84902c72802a97e196354e500cc3ec36e0a9ca01ed5b73dc153940cd0f90ea9ac3280072b9c9425865000656b9284b0ca0058
  | 9 => 0x43d95310051f424e5b2a6200a3d849cb654c40147d08396ca988028f61072d95312153b408e5b2a6245a75811cb654c401c5f04a16ca98a178bcc942d953142f1619285b2a6200a3e848cb654c40147b09196ca9890b1d1c571d953122c3f43e83b2a620087d87d07654c485c6882a0eca989161fa1f21d95310043ec3e43b2a6200a3e84c87654c40147b0990eca988038b50b21d953100716a1243b2a6242a5d831c3654c4010fd0e206ca988021f61c40d953122d2f41881b2a6200a5d83103654c4014dd04206ca988029b60840d95312153b40881b2a6200a7581103654c40147d09906ca988028f61320d953100716a1641b2a6200e2d42483654c4010fd0e106ca988021f61c20d95310051f42041b2a6200a3d84083654c48b4bd06106ca988029760c20d95312153b40841b2a6200a7581083654c4010ff0aba2ca988021fe1572595310046fc1ae4b2a6200caf72509654c403958e4a12ca988021f61e641953100537414c832a6200a6d82990654c4014eb03320ca988021fe1d64195310043ec3cc432a6200a3e84988654c40147b09310ca988029d60662195310043fc3ac432a6200a5f83588654c40147d08310ca988028f610621953133d3b408c432a6200c3e76d08654c40187ceca10ca988038bd894219531007163128432a6266a7486484654c401ccec4908ca9880399189211953100792a124232a6203a5e86d96534c4018bcedb2ca698867171957094d312163a38ecaa9a6242c5c76d95534c485aaeea38aa698917171cf65545310062fb2ee6a8a620495c8754d514c4094b90ca9aa298812d5205535453100657b9285b026201cac7250b604c4039c8e490ec098803a950921d81312143e436eab02620087e87d95604c401878e9b2ac0988031b1cb65581310043f438cab026200c3c74195604c4018d8e432ac0988030fd9774581310061e32ee8b026200c6f65dc9604c4018d8cbb92c0988023ee1d601813100e57392843026200cad72508604c4090fd0f2a2ca188030fdd254594310243e43aa8b28620a8dc835c9650c4090fd0f292ca188028fa1252594310051ec24a4b286204a7681949650c4090f90ea92ca1882a9720d52594310061fba4e8b286204a76819d1650c4014eb033a2ca188028fa1272594310051ec24e4b286204a76819c9650c4014eb03392ca1880297e0d72594310552e41ae4b286200a3e841c9650c40147b08392ca1882a97a0f42594310052ec1e84b28627ae1e83d09650c401c3b07a12ca189bf87cc7425943137f0e98e84b286270a3d84909650c401c5f04a12ca189cb8bcc942594313971619284b286270e1f31509650c4e1c3a62a12ca189c38bc8542594313871690a84b28626fa3e84109650c4154bd07382ca188028fe1170594310051e422e0b286204a74815c1650c4010fd
  | 10 => 0x2c0000500100a000000070000080201700000000000008000058010060040200101000000809002000000030080080300200001806003008024020060060080081200000802802018024008030020000100301000c00800000008020010140040001c00001c0000600003800006002000008010000000280700a0000300300a004000000020000180500c02c0280100c7a43a42b0ca600a77854856194c039c8e490ac329803a9509215865300e5739285304a600cad7250a6094c01d5284904c12982a3720d725825300c7c43a40b04a600ea9424816094c0195ee4a16c2a98072b1c942d85530147bc3a83b0aa602cb6745076154c031ef0e90ec2a9803a950921d85530265a30ae930aa604ce4615ca6154c0196ae9b0cc2a9803395cb61985530047bc3ac230aa6038dd83dcb6054ca54b906a96c0a98032bdc942d815300e5639285b02a686cd973d826054c858eeca38ac0a98023ee1d601815300e5739284302a600cad725086054c0195ee4a12c7288072b1c94258e5122d2fc3ac729ca267c5f8758e5394401c3e84b1ca728803875096394e51214bbc32e329ca266c77865c65394401a6e84b8ca7288034d5097194e510043ec34e129ca201cae7250a609440195ae4a14c1288021fa1e53582510046fc1ae4b04a20a8dc835c9609440395ce4a12c1288032b5c9425825100e5739285b1aa200cad7250b63544014bb0a196c6a8803a350832d8d510056ac0865b1aa200ad9800cb63544011bf0eb18c6a88fa1fa1b7054d5122e2fb2ce7302a2008fb8758060544a50ff0ea98c0a88072b9c9421815100656b9284302a20a87c8755165cc4030f90ea92cb988032bdc9425973100e5639284b2e620495c8754d51cc4f387ceba14c1988030f5d742983313c61f3aa853066200c3d7550a60cc40395ce4a14c1988032b5c9429833100754a12413066200caf7250960cc403958e4a12c1988063e21d205833100754a1240b066201cae7250a608c40195ae4a14c11880e1fa1f75582310062f41eeab046200c5d83dd5608c47f8be63baac1188ff174c775582310043fc2ae8b04620387c855d1608c4091e902ba2c1188021fe15725823101c3e42ae4b046200c3f75d09608c4f3878eba12c1188030fdd542582313c61e3aa84b046201cae72509608c40195ae4a12c1189db1d1d5215823100752a1242b046200c3d74953654c4050ff0eaa6ca988028fa1252d95310051ec24a5b2a620187f8754b654c4014dd05326ca988029b60a64d95310051f424c5b2a6200a3d8498b654c40147d08316ca988028f61062d95313ce1f3b685b2a6278c3e7650b654c401c5ec4a16ca988038b18942d953122d3a43243b2a6276c7676487654c401cc8c490eca98803c950921d95310061eba0e9b2a6242c5c735cf654c4014dd05a1eca988029b60b
  | 11 => 0xd0c70a30458b529912c1fb0e21088dba7d2338000001af184a8f88605807c8002dc09891d00028eaec127a502dba85a1b0e80daa408d189214d2718000ac26015e0378000000000000002770000799cba16ab080000020e00000014a0001009baa3eac48a6aa698b0129128000878c81b7a899c09919e782e8001b70000001c9a6a1c00001508c389685f80a9990ab81d2bb8f09c51d0004976a1ba3a9ceae307080419500000024200000013198a8e60002101309f791bac71671c81c6a7825d07e8f5206935800189a8d0531b812a18029f2952462612d58782d18002909249ee0ad8a50210002d28000e380025b9a48001a7a2d0000001cf80000019da0d9808309068000001189020738be8000030b3ab690592889c9379de06e99280026607919e2b48ed1db0000bc8000002e580010180016b8001dc10b80000000000000029a99f95bac90628000001759ae00000d0e00000000131e0000000227a5600015f1448000b00a10002ce2cda358000001561761139ccacc1938001641d7a4f1a280000000000000000000001090aa9d0001cc000000139208000000196ad39af8d380b26c8ee0f18002378f3a00a9e0ef8252171bba261ec8001ff00013385999604407d2ef9f21bd08420480023d93ca240778001931838cd8170018010060080080e00a0000980100c0080201f000008058000000280100001a07000003014004038020000080000300204008000000004000010000040200400001c0c00200202013803018014038000000000e0010040000080108e048000010160040700000407c0280500801400001002010040000080200200d00600806803040000008020a40000080600401c018010060140080a002020028000000040000302a01c0600100e00004801010000028020000240080400a0340002b0000000b80700000c008010080000000000c0240100300201c00014000000118030040080401201000006818000000078030000080c80600009403000000004040020000000c0030180000080304c0180000600601c00027020020048000000040000000201001002010000028000060000080101c0000000900001c0700d0020080100703a0240d0000040000200000200000001000000048010180200780101201c028020080000580602401c0300302e0000200600e0000700800000c01801016004000040000100600a0060100101002000c010000140080000200001c0a8090060080000d0020040180000a004010020000401380700002c028000080140400c000068020000020040200300e1180000400000802002020000030030000000c8000000580180600e014018060660340000100a0001780100005c0000000405000802000000000080020000300100a0200f0030040bc0180200e0100100300a0000000e0
  | 12 => 0x1158830000d2a9f82900024b000132a971a12d083d15717c90d0a6080a7d8868470d4a8c93696d0000610001fda258ef0001819c482600000f00025925c0000fd2ad81b00000017d07a1de8822b9a1480027b0000000a81548000001268002e6023831800234a620488002960da26195406600012082880011200013303a2ed0000000990e280014116f9c300021194817f1978c30890942812178bf1b6090123097a7883211027b9a8a3d2a30bd0e78188feac417783508813518326d9680e917909387524019a849a0b0002bd15f84d01b8f280001e9310f89dc800000000282a3c0f120b86a0f984e8a5a1390390d81680005080f8002d48000ad0001e187e0700001510000000ca95a1da00002b80021eabe00000005ea490000d69150000491530178002830cd0002c1245a7a83414e0000a726985a82f08ba53a4c9500b303b14901a98ea73061a2a9902b101380002420e9f38000fc80012c8000000000258000000001d28002bf9c600003e09287c0001091a3000000000000298187800151800000222a54800000000046ae41eb80007f15c800024a01800235186800065aaf22916c0000001600000001a508da9380024b95d8000d51db8219ea856a2baa91110d12eb9361c704a2861e680000003689b20917e0000f91302628b11a81441a21d82c5a680230228001908e7239005a39a429dd147a2117313d922a5a9b99c90740a3a70094869962215251add2dc9bc19b138aa59d910525306708101420f8931cd8bf9ae9e32b50000002ca8dc0fd98e108125a318001168ba0421582588ff0000010000002d824817812b8000e30000000000001028002ee80003f2e19b11ac8b9aeb0d89949662942e1243ac825a2bca3b84f1e0acb8f4aba000000247a2da5213f2e3800281ab200023b064ad88de1799f700009ba7927f0002a205ba8a0000e080019c8a1ac32aa17c2c00b609ea5c8e5855a748de92f206162ab1ade0b7a3600000000002c068ac22050002df2659d986d87b0419e48002e796100000ba3a0d08000279be92d00029a15d01fa552ceab92b421910f80000023683b8001ca00000026f00009600889d98c2968000cb8a0a9d87aa722cf895a2fa3e1a9aaa8f20bc1322649c4218a161b30001010000002e094887498800025791088e14f9ba2a50829e385222c0b902229218d89f94f2c79a91970eda87a6babd8819072e80381c59f0800188aa4089829a0f0f72450002b62d68000710002ec95299e80028e0000d78000000c00098000000002868b48001ab000210a801b59aa89f063800157a4322305b1461539030329ad8181ec129ad90001200ba8770101e594a84dae2027106272a762c09bd8c480c0070001b491c2e8974a6719c16c8000000002a10190110002820692159d41b0802a5e99ba55890a12a7586
  | 13 => 0x18362752e99f00df84511a09819214b26a9d88b896302f85a134a8dada80ea678f40560002cd1450c98000ce89a22984322e80000003f9639b3aae18f119a9b051207a5e00924c11e8302e51e208723f96e0d5a1c971a572cc80000022013aad993f8b4182a4d10f0000002e6a739161588000000000000001a700000000000011700000000000c80010a0000ec00000015a8000cb0b68000a423f02a86500019100000000000007326e8b1ad300020880001a00008aa130c088b1cd08d2c69c381208882a1ed8dc8000000000000000ebaea83c0cf80008e9e923c93c17b07b8000000570000000001f60f5aee0000fb00029c8000000bb0002d627c21a0ae2bc00000024689d0c91708000000b200000000000000000000000006692b0339810002cb27a0c79fe16e8dd904800249ab81aba68ac600017d80022a00023023725f8001290fe05dad21f81859842059a60ab1b68000e680000011ca309f29bf800117ab780024e8001668f62d70001fb8528000002af80000022180000006f8370002238000000001d113a1b1ab31002322c98000998000c88b70d20a7807a8c1ed1d509c02d94b86caea2a81079e40000971cf1df0038000001d72bf03e8000838002cf00000020cab70000408002642c523888c203084a850cf0001dfab59499720c11692638d02b885e24da510fa84b16f1e527ea1a8918001458002022b280004398b80019880015b1520000148cc0002442da13b0ce2a199993e9f988c80021e0001d68002911651d38729221438aa0681f10002e720c00019f00014c0000002ae8000330000f80002038e517a80000006b80015585c9f484296b0000349738002140000002a998c81d9678000402631aa00d9e2adda4e18604c0801d590ea5800222b17011318d00020d0ca0000000002beaa6054960a8800006f0001890578722e29ca9ad06b00812707180004c863000076a1d84a8000000600001eb2a71788f00001a390caa014c84f92aa841da82b1f900000003c80000000017e8eb0851e82332ca01e000000226a6e0000e40001c791f00000015c000a099a400024480021d0000001698ec9658310541fa826a1826523400e08a28712521217722e19592621f0c619d0d42919a598a20a8c4016171225140806a411c22ab0c5276af19b01f89ff80027f86e1d48858002d10119b426697a0000001bc99a1ef00000007d8209d0ab380020000000000005526929280000000008f14300000025f0609f31e98ffaac8d62a79e60910b5800035a892568000001c88000000002f100026f8b2a8b015a4f9ef919000000000161ac181c27785d00000011e23280a0002de8000df0c20000002d79568f3284946a6c13d22206200027e1871b90e10002dfa711f409a853a380002509bf0b09741b50ae9be0a904b867a19a9ba6d0d7
  | 14 => 0x460bda4a038a9028f16da70a5d8af8dd0000be2f010e10c00021fae49d32b00000002ac0000bb82d0000000002071ac1d185000615e83915511d8000001bb28085880003a8001f182c80029998f8000000001fd05c0000000001b89370000002e029e921aad11f8aa94228b8d911b00007880026081f0000000a292eac28000000200000000000000002d009e2ed8e49f50000002ef11aa542a08002a48000d30000000001728000000000002a28000001750001a08001b21099fc2598000000c6a931d629c0000c5a2f0410b81042249c10761ea283af09401341dd80028a80000000006c0c28050001b280027c95906aa798ea0a9aaba281a18db0518ac9a69f59980001ee8d9819ad50f680014182e2988000a22111821c193e0eea2ca0400003d8951182db2958482d416a96887f85f04793803982812e0cc9399141fe88f94280026b24a8001e8a28a88aa892f8150fba0a2e916a0af1fc93ba418e19d22741fa0a012daa39241cb1f694eac88d82310640a4a97a5b0f784e1e1044a470001470c1921185202a012c39c285900017f9a010b14dabb2528002ba8e9800123a948fc1281ce0e88ea8001648000a887580000022097b81c8002270fa00000021c159a488001119940001149e70
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x291f8b000e9a2fa9a50200080021851681929d8002908a06000cadac09802bab0023a42e138f979c2c9d25ad0c22842499199591a8800380942f18000da82ea6a32a0e000013089e2094b0221e9006801880058016201baa80000000049b0d15011a890a831c80110f0700211f260b878027122797000a341020308644200c043811a28001081888500001000630381080ce548c935c94258251006a1509810cb6354401a894260032d8d5100e2a21d4248160cc50fc2475509215823142e8921942487654c50fc267650921d95310058965062484654c515a2486509211953139583a4f82509650c4e5a0c83509205943144f81145424866394001a85426043258e50005a1644725096394001689901c94258e50006a450580105639400105d98186739415039583a4f8250965cc00182e8750b2159730006151cc815c165cc0e5a0c83509205973000e2921d4248561cc0cd05e97a1d654c7304160721f4259531cc10381c87509654c7304261521e2159531cc10785487485654c730007815092159531cc111e096350920996300068c50580105658c0e548c935c9425843043f091d542485610c10fc24755092158f100f4172617558f30c4001a258260464d95100058324d6250b65440016249650921d951043f099d942487654400105f985cc73d95100060b61d420cb6544001a254260432d95100068a509800cb654400182d8750b21d951000689a45821906544001a259160864195100068960981190654400142d9798942195100058964662508654400142f9758942195100058324d625086544001625921924119510005896486450465440016259219221195100058964864484654400142d929db65d91100050b64a7619764440050ae98dc962d91100062320f7258b64440010af985c862d9110007091977248764440018a77260432d91100062adc9800cb6444001a854260432d8d10006a2509800cb634400142d929d36598d100050b64a74196634400182e756086498d100060b5d582192634400182f756086458d100060b1d58219163440010ad981c86458d100042ba6064dc963440014a4975092158d1000e2921d42485634410fc24755092158d100050b64864dd5314400148d92192739411000523648645ce50440014a59219371541100050b648645d730440014a59219171cc1100050b648645d6304400162592190658411000689509810c96504001a29426003259410005a1644725096304001689901c94258c1000629605741cd62040018a9805d073588100052964874dd910040014a592213764401000549648741d51004001834871d564440100042d25d8259110040014a4976116244010004a9660745891004001c24751d16244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x28227804875092159531cc00151050322c10c832a2000c09660751d16244010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x4b
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x124b
  | 10 => 0x4
  | 11 => 0x94b
  | 12 => 0x94d
  | 13 => 0x94e
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138d
  | 18 => 0x138e
  | 19 => 0xcb
  | 20 => 0xcd
  | 21 => 0xce
  | 22 => 0x12cb
  | 23 => 0x9cb
  | 24 => 0x9cd
  | 25 => 0x9ce
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x168b
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0xa4b
  | 32 => 0xa4d
  | 33 => 0x134b
  | 34 => 0x134d
  | 35 => 0x24b
  | 36 => 0x24d
  | 37 => 0x24e
  | 38 => 0xb4b
  | 39 => 0xb4d
  | 40 => 0xb4e
  | 41 => 0x144b
  | 42 => 0x144d
  | 43 => 0x144e
  | 44 => 0x16cb
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0xbcb
  | 48 => 0xbcd
  | 49 => 0x14cb
  | 50 => 0x14cd
  | 51 => 0xecb
  | 52 => 0xecd
  | 53 => 0x17cb
  | 54 => 0x17cd
  | 55 => 0x94053
  | 56 => 0x94055
  | 57 => 0x124953
  | 58 => 0x95253
  | 59 => 0x124955
  | 60 => 0x95255
  | 61 => 0x130a
  | 62 => 0x14a
  | 63 => 0x134a
  | 64 => 0x139253
  | 65 => 0x139255
  | 66 => 0x17ca
  | 67 => 0x9c0d3
  | 68 => 0x9c0d5
  | 69 => 0x14cc
  | 70 => 0x12c9d3
  | 71 => 0x9d2d3
  | 72 => 0x9d2d5
  | 73 => 0xb49d3
  | 74 => 0x9cb53
  | 75 => 0x9cb55
  | 76 => 0x16c9d3
  | 77 => 0x9d6d3
  | 78 => 0x9d6d5
  | 79 => 0xa4c
  | 80 => 0x1692d3
  | 81 => 0x1692d5
  | 82 => 0x198c
  | 83 => 0xb5693
  | 84 => 0x168b53
  | 85 => 0x168b55
  | 86 => 0x134a53
  | 87 => 0xa5353
  | 88 => 0xa5355
  | 89 => 0xbca53
  | 90 => 0xa4bd3
  | 91 => 0xa4bd5
  | 92 => 0x17ca53
  | 93 => 0xa57d3
  | 94 => 0xa57d5
  | 95 => 0x14d353
  | 96 => 0x14d355
  | 97 => 0xed353
  | 98 => 0xed355
  | 99 => 0xecb53
  | 100 => 0xecb55
  | 101 => 0x17cb53
  | 102 => 0x2cc
  | 103 => 0x5ca
  | 104 => 0xed6d3
  | 105 => 0xed6d5
  | 106 => 0xecbd3
  | 107 => 0xecbd5
  | 108 => 0x17d4d3
  | 109 => 0x14d7d3
  | 110 => 0x14d7d5
  | 111 => 0x188a
  | 112 => 0xd0a
  | 113 => 0x5853
  | 114 => 0xd0c
  | 115 => 0x5555
  | 116 => 0x4b55
  | 117 => 0x59d5
  | 118 => 0xb0e
  | 119 => 0x140e
  | 120 => 0xd0e
  | 121 => 0x188e
  | 122 => 0x188c
  | 123 => 0xd4a
  | 124 => 0x104a
  | 125 => 0xd09d6
  | 126 => 0x1889d6
  | 127 => 0xd0a54
  | 128 => 0x989d6
  | 129 => 0xd1696
  | 130 => 0x189696
  | 131 => 0xb1696
  | 132 => 0x141696
  | 133 => 0xd14d4
  | 134 => 0x1689d6
  | 135 => 0xd0b16
  | 136 => 0xd0989de
  | 137 => 0xd0b169e
  | 138 => 0xd02d4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1661
  | 6 => 3116
  | 5 => 1508
  | 4 => 97
  | 3 => 3
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (68093+((h/553+packedAt gbK7 (61457+(h % 553)*12) 12) % 2412)*12) 12
  | 6 => packedAt gbK6 (163062+((h/1038+packedAt gbK6 (149568+(h % 1038)*13) 13) % 4114)*13) 13
  | 5 => packedAt gbK5 (94494+((h/502+packedAt gbK5 (88972+(h % 502)*11) 11) % 1991)*12) 12
  | 4 => packedAt gbK4 (7014+((h/32+packedAt gbK4 (6790+(h % 32)*7) 7) % 117)*8) 8
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff8381e07fffffe0e01fffff0918f1e07f27f
  | 1 => 0xf0ffc01ff870780ff001fe07f36e48e7394c73
  | 2 => 0xff0fffe0007f800ffffe1ff80c7070f9c18f9c
  | 3 => 0xfffffff80000fffffe0000f807f01fe0fe0
  | 4 => 0xffffffffffff0000000000fff8001fff000
  | 5 => 0xfff0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110080200808a24020822a24000830a021225
  | 1 => 0x50a9c10cc834504b90155415a1264865194c52
  | 2 => 0x6a0a5320405d4082a4a41950247010b1418498
  | 3 => 0x84ac579500012d49598020cb806d00ae0b60
  | 4 => 0x480f3799666e65c0806010410efb0001f5e000
  | 5 => 0x8cc0060184080601018101860fddfede000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36202
namespace PEqualNP.Outside.L_meta_36202
open PEqualNP.Outside.L_meta_36202.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 20 := block_range (n:=20) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 20 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 551 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 (concat bs2_4_224 bs2_4_256)))) (concat (concat (concat bs2_4_288 bs2_4_320) (concat bs2_4_352 bs2_4_384)) (concat (concat bs2_4_416 bs2_4_448) (concat bs2_4_480 (concat bs2_4_512 bs2_4_544)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 666 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 9 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
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
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 97 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_1504 : Interval gbAtlas 5 1504 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1508 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))))))
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
theorem bgb_6_3104 : Interval gbAtlas 6 3104 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3116 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)))))) (concat (concat (concat (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))) (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))))) (concat (concat (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))) (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)))) (concat (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1661 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8feeefae8feaaf8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074664 * 2 ^ 32 + 4272617640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36202.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[0,5]⟩,⟨.or,[3,5]⟩,⟨.or,[1,6]⟩,⟨.or,[2,7]⟩,⟨.and,[3,10]⟩,⟨.and,[1,6]⟩,⟨.or,[11,12]⟩,⟨.and,[8,13]⟩,⟨.and,[0,9]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4272617640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4272617640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36202

open PEqualNP.Outside.L_meta_36202 in
theorem PEqualNP.Outside.L_meta_36202 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4272617640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4272617640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
