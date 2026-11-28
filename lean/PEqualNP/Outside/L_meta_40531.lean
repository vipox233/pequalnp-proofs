import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40531.Model
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


end PEqualNP.Outside.L_meta_40531.Model

namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40531

namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
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
end PEqualNP.Outside.L_meta_40531
namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3000027bc40bd41de32ef32be40ec32cc32bf41dc32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x30c0000c6aa0658c32507186420630cb419aa88818e540ca9ca519630ca40
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x9c10c9511020d650cb418359432102856195032
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
  | 4 => 2*((h/10+packedAt s1K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/9+packedAt s1K3 (216+(h % 9)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s1K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 2 => 0x81fc0fff83ffffff0783c1f03ff87fffd24e3f
  | 3 => 0xfe000ffffc0fc1fff803fe003fff8781e38fcc
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8828002300208000188442118a0088940490d5
  | 2 => 0x24519644194530cb032191a214c85568d2462a
  | 3 => 0x149aaa8928ea13556842f484a755060d638b4c
  | 4 => 0x59634d125283a5a6b5e8210939a66031bc0db0
  | 5 => 0x61838e1c630c39f8c67339ce01c44441fb6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40531
namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1062460c000004108b200007001041003006240183fe42fe20fe41dd43ff40fc31ff43fc42fd21fe21de43ff21fc10ff20ff32fc43fd10fc41ff41fe10ff30ff31fd41fc21fd31fe30fd40fd42fd32fc30fe32fd43fe40fc32fc20ff10fe43ff42de32fc40fe31dc32fd20fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc0c0810034000060169b00340004c28780001800b0004012061c003181408486243ae06040370a0008d4e681045e00c971802bea8195b948109eaa065cf5250f3aa8195755243a6292876d5210398a4a1d755232b7a92635c5250e78a8905794f42afa9a215c53486eca3a14f95031af298877551d0abea6a15754c41ae29a855e520cabea690d794c41cea1a859d43d0b9ca4197310832cea1e836d52d06dca4205754c10bb288813d54cc2e8a29073d0832b729461cc32886eea2904f55010af29e833d54886baa6215714d20af298813e54cc2daa4084f95221af298853e54042baa8194f15110cea1c815d53886eaa2204755032e6196415e53882baa7a167d5143af298215f53482dea4a1e750c40cea1a835d53882baa7a0d754c40b7296835f548cad8a498d754f40af29e813f544439864905714d10b6292879e540cabca710d794a329f2a0656f524427ea8904f55031b6a94615e5290f986410db14910
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x80023800c08001081c100c041828c6250f41c3189540ca1d6494e20c3553420cb0d43548409318953d03154354742c550d511028d640c920a3189431030c540c920a318943d0a4d651083293189531068d640ca21c3950328861d6595032a31894390344321452087590534870d4354b41b1987420ca8d640cb20a3189435068d640c821
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x400000800206bb0a819241411c9435444081aed2a06510d047250d51d0a82ba06428a418155261d0832
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
  | 4 => 2*((h/58+packedAt s2K4 (2430+(h % 58)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s2K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/30+packedAt s2K2 (294+(h % 30)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 3 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 1 => 0x89144a441945212c0c8648510a4852d146462a
  | 3 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 4 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40531
namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x644058b00018a15608070b02a5010c72c7ff32ff21fe32de31fc30dd30fd20fd41fc42fc43fd43ff42fe20fe42fc20ff41fe40fd42fc40fc32fe30fe21ff40fd10fd31de43de32ff10fe41fc21fc10fd21dc32dc31ff43fd40fe43fd32ff30fe10fc31ff31ff20dd43fe31df30fc41fd30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8400c2844001c05644000dc000050900048081038040014000888000000102001540c700000004801640c0050008418087444181c0450080c080058000c133a86a157d5031bba8a415e53102bea78857540329f2a0415d538833a86205754c42afa9a415d53c86bea8195794f41afaa46376511027ca8195754c41baa88415d500c6daa5a0db94840aeaa0655c5250ebca5985b94b41eda82615e5310e3aa818d754c10afa98439d43d0abea8984f95221ae29a415e510cabaa7a15794431aeaa2613d540433a87a0db94810aea846574514827ea8904f55032af290635c524c2bea6a157553309f2a0213e540c6baa6205b14910af298215c53486b8a2985d94742af298855c53506baa7086795032ae29a215f53486bca7205794f21af29c433c54482bca7a179484219eaa0419f5450f3a872047550329e2a2216f52442baa7184f55321af294633d54cc33aa8194fd5110b6a90815c53c433ca818e755330af28c875f548cabaa818d754f40ae298437551d0abca7a05754e40af28e619d43506bca31957d53309f2a6615d53082b8a7907394832ae29a855d5090e3aa99857d4d10af298415c5150eeca2105755243af290653e54c867aa910d755231cf2a6615e530c2bca620d754231af28c635d548caeaa2205754e21af29c215f53506bea0a1cf55031af29c41d6510c73aa818d754f41afa9e415e528cadaa4085794a43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x80002008060080000000f0042028000000009398b548c65661d523287596540c61d64145308759253883154354742a31894350a1f6454231c350d52102946150d4187592518ca54615513087d91508ca1d6414d2187590524c21d6414c21c550d511021d6414f208759053c42596014c2187592528c61d6595032c350d52d064c625513087592538421d6494c30
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
  | 5 => 2*((h/23+packedAt s3K5 (768+(h % 23)*6) 6) % 48)
  | 4 => 2*((h/65+packedAt s3K4 (3618+(h % 65)*8) 8) % 134)
  | 3 => 2*((h/36+packedAt s3K3 (988+(h % 36)*5) 5) % 26)
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
end PEqualNP.Outside.L_meta_40531
namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3820c01c00001400010210002417490000801c4ff21fc43df32fd20fe20ff10fd30fe41dc31ff20ff32fd31ff41fc42fe43fd21ff40fc10fc31fe40fe32df30fe10fc30fc32fc20fc21ff30dd32ff43de31fd10ff42fd41dc43ff31fd32fe42fd43fe31fd40fe30df43fe21fd42dd30fc41fc40
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3538182400000000000c0068001c0400000000002138180000200000243c003008fc002c040000000054000800cc2c003c1440000000056c80002410000014006814000440000000186404003c0004001400001c0800987c5c183018eeb8a818d754c40eda82616e5210ebaa790f354b30af28e873e540433ca821d7d4d21e6a90635f53886daa520cf15110aea90875d520c79aa421d754043a6a90635d500c6b8a710d7d4930b6292215d5390abea6a0d794c42ae2a6655d538cabca8995b54843bba8a815f5350abca9985754c10aea9c417451502bea7884f55020e699243cd424cb9ca418db54810ae29a435c53506eaa210734c820ae29a815e53882bca6195794c40b7a92815d53d06dca520dd94642af29c81ce52cc2dca4205754332af28e615c54cc2b8a2985714532af298615e53082b8a6885794443e6996435e5410ebea6884f95321af29e415e53c86baa6105b94810af29c215e54ccabca318ed50441b6a96835e53086baa7085715130b6a96615e5390eeca2105794c10aea9a415d53906bca7215794f41aea98855d508c6d8a4a05754f20a6a9087d6510c6baa5a1d795031baa8c856d520c6baa610cf55321af29a416f52442baa1a1f394843af28e655e548c6bca720d754e40e6994416e520c6eca2205754a31b7296615c5350ab8a89957d4132e7212655f535027ea8884f55010af2a2613e54082dca5a0d794431b6a90814d52cc2eaa2205754e30ae2a4635c53c439ea4995754b30
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc0000040200000044000000000200080093d8950d0e4c654c92193588535061c6454d2095185534824d621453093588544c24d6214f10c355132c864f6254231c3151424ca5661951329358a51d0e4d6294d209358a548c64d6215031b118532487453254420c3551320824c6550932b1586424ca5960150319358a538424d62153309358a539021e64d4e21
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s4K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/93+packedAt s4K4 (3618+(h % 93)*8) 8) % 134)
  | 3 => 2*((h/29+packedAt s4K3 (988+(h % 29)*5) 5) % 26)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf87fffffffffff81fe0fe0fffffffffe463fff
  | 1 => 0xff81f87c1ffc1ffe1ff0ff0e0f07f83fb9d273
  | 2 => 0xfffe007fe0ffe1ffe000fff00ff87fc1c1e39c
  | 3 => 0x7fff0001ffffff00000fff8001fe03e0
  | 5 => 0xffffff80000001fffffffffff0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80820040008000022010012220889080204a5
  | 1 => 0x51245088ca50a8960c506504454550b498d252
  | 2 => 0x6214955146a28baac148b6a089d46685c16318
  | 3 => 0x47596662943acdcd776a14812ee64319ee03e0
  | 5 => 0x8461844318c31171998cd8c9c080042175b800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaa8a8a8a8eeeaeeeaa8a8a8a8eeeaeeeaa8a8a8a8eeeaeeeaa8a8a8a8eeeaeeeaa8a8a8a8eeeaeeeaa8a8a8a8eeeaeeeaa8a8a8a8eeeaeeeaa8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40531
namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x440400020400001c008000008409504c057042ff40ff31fd10fd32fc31fd30fd41fe30dc43fc40fc32ff42ff32fc21ff30fe40fc20fd20fe21ff20fc43fe32fe42df43fd21fc10fd42fe10ff43ff10fe43fc30fd43fc41ff21fe41ff41fe31fc42fd40fe20fd31
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc83dc438c3b886085f54b41bea96817e5290efea890f794443ce21a817e5310bee20085f54d20ee21e857e53c42fea8885fd4910bf29c837e5090bba6498f710c31bb28c85f940102f8a0a15f94031de21a817d518c2bca7205f94220bfa96217e53107de8490fe48020df21a81df43103eca2195f54e40bfa8a857e508877aa9185795043ef298417d5290feaa3215f95310bf29865bf4290afca418df94c409eaa0417f53483be8620f7d0d20be29e419e5410efca918dd54432eea98437e5410ef8a0a1ef90140bea84877e54843de40105f94332af298417d510c2fea898dfd5232be2a263dc5210fbe8710df14d10bea9e417d52882fea2986fd0c43beaa6617e53082bea6a05fd4940bea8065dc434cafaa5985f94720bf28c837f514cb78a89977d0f10f799465ee20483b887a0f7d0e10bf29c81bd54042f8a2986710c41bfa9a81df430c2fca021f7d0e30aea9c81bc43106fea7085f54a41bf28843f441487bea5a1f754e41bfa9e437c5484378a898efd0e43bf2a465ed32487be87995f94240dfa00817e52906fea8995f14542bf288217e508c3b8a6a05f94e42bf280617d5110fde4310df15031ee21a437c548c6fca899774c530bea90817f54c42fca7906f90c41f729063dc43cc3bea3a1df94010fb10a217e50906f8a610dfd5320efa1821df43d0afaa910dfd4520bea8c417c53483ba63987794843be282837c544c2fca020f710c42ee21a217d53887daa520fd48710bf284877c504c6faa998cf15131be29821f741886fca1195f54810ee21a61e521086bca6085f94443bfa8a87fb10843eaa2107bc8520bf28683ef4290afca1087d84110bf2a0857d51d0afea6107bd0a20bf29081fb20882faa6107b10921bf29821df434caf8a2a1df55030ee98863dc5350afea0997bd0942eea9087ee52907f460187714743dfa0c83dd50d0fb887216fd0b40bf290615c53502fea810fd44010f6a90637e5210efea8985fd5321fb20883ef42c87be8690df94e10fd984617d50086fca4085d54420be29a81bd40102fca3105fd4941dea10857e5190bb886195f95032bf2a043fa10042f8a890df15321dfaa263f651082faa5a1df54341bf29e85f741843e8a2a05f14e10bfa9021dd4310efaa518df94b40ee21c417f53443ea4210df94a42bea9c65dc438cafaa1a1f7d0f31eea98417d54486f8a790cfd5132afa9a837d5190bb887905f14532bf29861f541106fca910dfd5220ee280877d54883ee82085fd4d42be2a065de53042fea6a0df54432bfaa0617d53843be87985f54321efa1a217651083bca3a1df94a30be2984176510cb3886217b8c921beaa4217e54043b886a0efd0940afa9a85f631886e8a2a077d0c42bea98437e544c7b88718f710d42bf286637e530c6fca3a1df15120bf280435d53083b8a6a0f7d0d30
  | 1 => 0xf5050afaa6885f55332fb28c85de52d0efca9105f94e21b6a9483bf41d02fea7887794c21bba8a81f910042baa7215fd4943ef992617e51103bc609877d0e31bf290657d520c3ba6598df94b41bea9481df4390bee8290df94742bf296877c544cbdc64195f94842efa1a857c54c82fca4105b94a41be2a0617d54443be87105f94640beaa2417d51083b887a07d4c621f7a1041df50d0edaa4085fd4143bf286437d51903baa3a1df55230beaa0437d51cc2fca8205f94420bfa98217d5390bbe86a0df94231ee21a63df4350ef8a810df94442bf28687de53906faa9215fd4131bf2a661fb40902faa588774cb30beaa6437f540437ea89977d0f20bf2a0419c4390bbc8621df14e20bf280417e510c6fea918efd0540eea9687dc43902fca6904f95230bf2a2417d5310ab8a6a16f10e42beaa4837d53103be65195f55243fb98c637f54483dc6590df94432bf29421df430cafaa988774c930ef28687df43906f8a5087ec8120be29e217d54042fea690df94621be29a85ef20883bca72177d0f21bea8483bd42d03eaa2196f50740bf28e65be4390afaa021df54a30dea1887df31cc3f680a07710d40bfa82836e520437ca9185f14540bf294655e5390afaa8985f94821bea8663dd5390bbea421df15331bf28883df5350bec6218f7d4d41bf2a0613e54042faa3996f90d43bf29a437c54cc2faa99077cc530ce21c836e520c6fca2185f15221bea8c657d548cbb88798fecc130ee218417d538c6faa620df55020bea8e817e534437e8220f7cc431efa1a637d50886fca3a06f10e41bea8e877d53c86fea8196f95020dea12817d508cbb8a1a1df54442f6a90215d53043ee82a0fbc8720df21c837d508c7bc64997b10820efa1e81de5010fbca821df94f41bf2a6417d53042faa1217dc8521bfa9c43f4418877a82a05714d41bf2a643ef21086fca5985f55032ef990655e5390efaa7106710f40bf29c877c52042faa018df15110bf29663bf4210a78a8995f15020ee218837c53506fea2a04f55230bea9083f7314c7be87205f14b10ee21a417f50487ec43887b94810fba0c83ec52502fca7a05f94730b6a90637c50486fca9995f94b10ee21c435e53086faa598ef10f40bea9e857c52507de64995f15230eea8887f441842fea498df54f40ee218817e5310fee21087d4c431bf28081be54043b887887e90040beaa0637e538827ca8105f54f41ee288877f53086d8a4a077d0d40ef29c817e54486f8a9997710c30be29261ed21483ba64195d54642fa20821ee21486f8a2906f90f409eaa021bd411077e81207754c10ee21c217e53087ea6290df94a31deaa0417d53486fca790f754e40ef98c637d52842faa8997710f32bf286857f54842f8a8085f55231efa18417c5250fbe6498f754043bf2a2217d54903bea6a05f55131af29
  | 2 => 0x1a6682c150003f8b2000800c8000580800074028322b8120000000020008000280407002050280201c000702c0340300200802020440001405006010b00103e1300e050640300a000000084c1980000006018b00b8060000c9202e00008000201d8040284e000660109a088fe008020506a00008010b40009c0180618b1a00006080025281a0000001810060a0008700a80002804030360480a010060610a0d80c0009a008200283410022048061c800000040080afd000000f2028000380004acc078ee0100a0f8000a8502980c1a05c1681201282010980006000000058000200051a52000020001c8c0120286a18800000ec1886a0083a000004100c0000454810000244c0023505200800000300300e000027b812000000700409006000000080c4109a0d00c01846048003614c000000200407006120001483a1c81a1c8ec01000040000a0040e80806800000120001005824000017d51102fca818df94a40be292215d53086fca3197bd4940f6990657f524c3b8a5a1df94841ef18a63ee4210afca9185f14931efa18637d520c6fca0195fd5221bfaa0417e518c2f8a690dfd5031bea8c21ed32c87d885105f54332fb10843f751502faa7187b50842bf2a6637d52886f8a9885f54720bf28c63df5110fb88610ef90942be29281ec42c86f8a91977d0f41aea9c837d50107be60185f54342fd882217d539077c82a0dfd5230f690041bc4310afaa4885f14e21fb90c437e5190efea998df54643efa1c877f52843b88720f710f21df218857f53c82fca4884fd5131ef99663ed21c83ea428877d4043ef996617e54107f260185f95130ee980617d5210fbe8610dfd5330bfaa665df438cadea4a05f54f10f6908437e5010bf4401077cc230bea80857c504cafea7107d8c521be2a4417
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xf540865f63550209798c5308276611481097997435023d6595020e310c420823f6550842c7550430434c43548109798f540c23f6550c439758c540823e64d4e109ed95300c2766114930c718d540427465485109b58853c425e63d5031cb553420825e6314c10d954b100431e5410f219718d54c871c43944419718d544825e6314810d9151210871c5410f20a7191320ca5f65d0c20c7153434c25e63943429bd954210b1e5410e10c7550438865d6314520d354d520425d6510c21a718d42d027565104109dd9541106e4614c9219b18953442e661d09219718d548831e54d0c10cb90e529071c5390541c7551530423e64d4e21d954520082766115030d594e5190a5c63550109d987540831c43540429758f544425d6510c318f990530838c4310921c7d8d540435743d45409d98754c825e63d50209b588540c65d63d53209dd85534825f6355320979974350b4f53d494097596530439843d0140b95864210a3c6454f20d54c9510cb944354642f110d210874e53948109758c50486d56110c319798c524423c6454f10d5145314c2766194b40e510c418865d63d5121f14c9314871f5410f209758f540825d65d0c2097596530827561150309b997424876742544208f990520425e63d5210d55445110e5f6510c10b39885010e5f635501097992530839443d4540c7152314c63e6414121c710e529065e6394341c710e52d035443946429dd95310c7675214540d310f525023d64d4e10c7d91530865f6355131cb14b425034e5394a41c715043c426d6510820d35485210e3e6494332c714e4250a5e63d5032d310e520431e5410d3097d94430831c5410c21e510c51502b4644c6219d58453c825d6394b408f992544cae765484218f993530834d5394810e310e529069e6390c41c7191530866d6294743cd952510829e6510d409798e52d071c4354241d5d0e510cb4d5354a41a718d411072d5454810b55845210f1c5410d32d554e5190a5e63150108f992500c31f5310d40d310e529065d631491097594430cb5743944208fd95411076552104108f59250ccb4c43548319718d54c426d62d5310d354b310c67b60551219b988540c25e6314b109d987540865f6355220c755043ccb4f43948318f59353c87645248710e310e4210a9c644c9318fd9153c431c5410d21c7594439074d5394a419bd89544c26e62d5010c710d501065e63d5321d9d95210871f5410d219b58b540435743546429b59652042e662d0521e510c410425e6510d418f596540423e6495131d9951210866d62d50318fd91534865f65d0c10c7952530825f63551219d195314865d6394341c755343082766115020e6d0d401025c6355110c7d8c544c63c6454d10d514c515031c5410e328fd91530865f654c8329758f54c873443145409b588514c2ba6090d40
  | 1 => 0xca5f63550219dd8554443944310521a718d41d027665d05219d185548834c43948319758f548871d5410c209ed95401031d5410f319ed95100431f639501097997435066e62947408f590528429c644c730c7152324cb2e54548109e580540c75443944208f990540827960150329b58b54cc29c635054097d8d540c26e62d5330b358a51d0eac644cb218f592500c29c644c43197596530866c6255210b398b434ca766114c209718d54842b4644c521d954d210869d6510e419e580540865e63d51218f191534865e6314121b6983434c34c53d4940a798a5410f674254642d5cc9510cb1e53d02409d58754083544314540f1d0d21087c553484219d58652d027a6015031d65405010f653254432a798e405023e64150108f191524425c635512197d8d544827561d53209b189544c25d63d5310c754c4390ae960108209b588540434f4394a41c7d8e548c25c6355320c510e5190b645148520b6580430c23f6454d20cb90c52503544354420c79925410f4f43d49408719153087574354432c7950430ca5f65d0c21d554e510832c4394a4197d8d54c874f4394810bc18121442776155120b59845010f14431454097594430827b6054d219bd89534425e6394742c7d5043c431c43948429d584530825f654c431a798e435025e65d0d30c710e521071e5410c408f191534832c62550209b988540c65e63d52218fd9540102746155120e35884310a5d6394342b35885110e3e64d4f21b598652d0e3d64d4c10c7550430c25e63d5320e510c418427561150208f994544ca3d64d4c208f990530429c6454c21d3149324c34e5354a4197d8d548431e6510d409758e51d031c431494097992530426f65484218f593538872e5494810d3d0d520c75553544209718d540836752d45408f993538831c439474097d8d524425d63d52209b588530431e54d0e32979944350a9d6510e429d987548cb344394642e310d529065d63d52108f593538827561d52329e980540ca5e63d48108f19153086d56194b439798c540865d6315021e310f525035553484219798c514831c43944428f993530431d5494c10c7950438c25d63d4810e5984431065f63551309dd95100438c4310b219798e52d025e6494c219d98754cc3645214540d310c525031d5410f21d554d5190b1f63151329d584524c25f654c030b398a51d0e3d6414c10ab191324866f6548020d5d0e5190b65524c4319b988530866f654c832d394d520434c4354a419e181534865f63551329718d540871e54d0c20c7d50434823f6454910c7151324c71c5410d319d984530875453d45409798c540826c6255110b55845010e5c6315130e698043d026e62d53109758c540431c4314540cd185540429c644cb31d6d4250d0e5e6314a109b58a51d026e62d50319758e52d078e6210c429758
  | 2 => 0x10049d0381c00002038415643c004151cc3b008650540200047011c63fc01064d0014100d815004b70700537c020b0030180415406034c31f4035a400058000285d01422001d009874674130040001c2401401004000080678c3c0100200003308009b195324865d65d0c109719153086776155130d3d4a52d0ee4624c521a718d425027a601502197597430871e54d0e30c310c52502cd6214043c7d50434431f6395020c7150438c6e860485209bd895484336545442097997434c75443544329798f540867965840109b988540431e5494c10d354d210876551c8020e310c428835753145409d987530831f6355230c795043ccb5443944328fd91534435743145408f59050486d96014443b65805210f1e5410e21c7950430827561d5330d510d5190b1d6510e42c795043cc6e56288421d5d4f515034d53c84219d587530826e62d4c10d314c525034f4354a41d3d0c525032d5494810c7150434435553884218f59250cc7944394642d3549310c66e6214c10d5d4651d0e7b6548020b958a411063e6515131d9149214423d64d4810d5d0d510831d63d5131c7551530831d5310e41c718d54082d661d0d31c7550438431c63950209759443042766114f20c7150434826e6214810c7951530831e5410f30c7550438c25f6550c439bd89544829e6390c428f590530831e5410c109758f54043565354642a75825410e746154d208f990528435443d4540cb10c52503996010f409758f544825e63d5310c7d50434c71f5410d329798f544833554544209d185544c2766194b4397d8d548869c644c9309d58652d0e766115032b39885110f1c63950108f99250cc78c43149409d584540cb1e54d0e319dd85548829e6195043c7950430c25c63549109798f540431e5454c10b3588430ca6e62d5021b59845210f6552d0641d98c9510ca6f6255110cd90c515036552d0410cd90e5190a5f63553109798c530865e65d0d32c710e5190a3f6454f20d3d4c525036753484219e18154487944390441c7153434ca6d62d4c10a7992304c3c65348421c7550438834f435481097d94430865e6510d409758c52c425d6314810cd14741503644254420bc580410431c54cc931cd553410425d6314a109b98853c431e5410e20a7191314c3956110c419b98a51d0f565354420b69805110e5c6454c1097d8d544426e62d52319dd95210869c644cb308f590520436552440109b988514c2da6014843c310e529071c4354242c7953308c26d62d52319798f54883565394420d954a310c65d6510c30c7153434c7455348421d914b515025c6355221c7552530831f635502097191530831d54d0c109798f544423e64d4810a718d4210b355494420d9485500865d63947429798e51d027661d5032c7950430c71f5410c219b588540c27561d5032c758f544
  | 3 => 0xc400061be0081f004180281202c0002c100281c0380c045d2004610945703431030000280000020046080643b04838030030601d0181015000194351ec1c000001300004c000100b004d4164030001124414094a42407a08c0002c000380002c000005b0012b0389655003000143b0170043a0d80100029038c91500200004010a90800600c0c004000001011dd97d06001032604110a51e30d9302c0100520014
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2800e0c000010614b8000019810004a010210000000010404200800004593100800002001014eb8054571149324c2b0b8084a8841915496114843a18e8a9e4210e0c64149324c3822a08690843c11d15348421a2ce3aa08610d147155043882a23a2a690843451d15348421a1ce5aa08788684644c931486a2b90a298a61459c75410f20a8ae421aa219649525805210ec23a26498a43c1dd15348421838e8b18a29060c5498b434caa2b98a490a21a410d6010410a1ce5aa08610e84435864210a62b8cc5a1a65431c95410e10a2aea2188208651515805110e0e3a2c629221c110c4254420a28e8992a219519701504308706322a4988638318c625502083aec2a08610cc572987434c722b16a328e87611d15348421a8eeba1a4210e0d6510c420838221aa4208218518c6155010a8aea21a4210e45625445110ea2b98a890843c110c52d4540e0886290a2a041c7458c52c42a2b98a290a4191d496194b43e0887a90a2a0651615405010ea2b98a490e21259c66295043d0886b148220d247454d21086863a2a690843435d44310820a8aeb29a4210d457110d520c70621cc528e81451d1538842191ce530ca821d047454d21086b0b80a89084385190514c53098ae73168290e6152580410434421ac0210418510e6194b40c2aca2188208649625405010f0a2a4c3a1a63315ce61d0921
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x20100210000020000904845cc5248510c04645c4524c930d00435c04254420b01801504348421c04545c662d0d32e00435496010410904845cc5148520904845cc5248710905871504348421a118510d6010410c04545ca61d0d31c04645c8514c530a098510d6010820
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
  | 5 => 2*((h/275+packedAt s5K5 (18873+(h % 275)*10) 10) % 699)
  | 4 => 2*((h/208+packedAt s5K4 (23788+(h % 208)*10) 10) % 626)
  | 3 => 2*((h/46+packedAt s5K3 (3675+(h % 46)*7) 7) % 75)
  | 2 => 2*((h/18+packedAt s5K2 (780+(h % 18)*4) 4) % 13)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe0fffffffffff03e1f0fe1ffffffff80e3fff
  | 1 => 0x3ff03ff03ffe1ffc01ff1fe3f87f81fc71ce73
  | 2 => 0x3fffc0ffc0ffe1fffe001ffc7f87fe0781f39c
  | 3 => 0xc00000ffff0001ffffffe0007ff80007fe03e0
  | 4 => 0xffffff00000001ffffffffff80000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x281041208240000a05024049088a8a00614a5
  | 1 => 0x94248a219248a92c08a50aa12c55055430ca52
  | 2 => 0x1842924486908b554a0412c84d465415816318
  | 3 => 0x916b2c89241ccd9a6d36408076641866da03e0
  | 4 => 0x218c300e38e110e391c89d12000061836dbc00
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8fee8a8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40531
namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904002ffd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c00bff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08407fe4302ff54805fc52027f1040bfd5100ff08009ff4101ff14c03fe2000ff90003fc3001ffcc40bff51007f50801fd4101ffcc807fc43007f4400bfd50007fc4009fc5400ff8400bfe51007f8c401fd40027fd0c01fd2002ffd480bfc5102ffd4001fd43027fd000bfd54027fd0807fc31027f95005fc32007f4c807ff3002ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a8223ff19531055faca8801bfe4150403f61024023ff5493106ffc878801bfe63c4007fe29a641dffcc2210fffaa11081afc658c405ff1028406ff197100a7fea49800afc624c405ff902840affd451001ffc651881bfe628c403fe206200cff10b101affea6a106fff504840dfeb2c8200ff58d41037f82098812fe6448415fe32a2000bfd8d4101ff8649881bbf4190407ff9828614ff19530037fc6310806ff61440057f3146206ff18a41007fac4988cffc3050807ef98a6406ffd0621037fca290813ff4150c19fe1962002fbc8121007fa629080bfe214804ffea946200ef1913115ffacaa08c3fc404c8017eb1a4002fd0852101ffc869900bff214840dff3046206ff1051000ffc8090027ff4344005fb90a420dff10f10035f8c29900ffd534c401ff10a6005bf19543027fca8a106ffc6548405fe1044203ff4c931007fa848801bfc5148429fea926003f7cc53000ffe618801bff41c400def98c6204ff1514101ff8869901aff6248453ff90a8201ff04120127fc811881bfc62c4009ffa1a8000ff50d2000ffaa188013fc41500057f3128234ff18d42017f8649900bfe3248005fea924006ff08541037fe432081bfc5150447ffaa26200ff58943037fec520816fc654c003ff2026004ef9514001ffa649801afc6150009fea128000afd9132037fcc11081bfe31c402fffa8a8003ff50d30027f881208bfff5090407ff1926019ff18d21037f8a320812fc6448413ffa12201dff94e210cff8a690803ff6050803fe9062006ff0864118ffe8299016fe654c8037f3046209ff99110017d884a101bfc638842ffe32a8000f7d8d4101ffe6099087fe524c465fea826406ff98e21017fe6510803ff6250003fe9862036ff0814302dfccaa1803fe615000dff32c4201ff0413000ff841880abfc53504097e3222004ffd0940177f8a72088ffd514c40ffe3122002bf98a41037fca3208d3fc3150801feb128001bfd914011ffcca9880ffd328c40dfe31e2003ff94d430cffc869080ffc4350c05fe9924033ff94142007fec4a1813fc43504037fb022005bf1953101dfcc690803fe6150c07fea9c6212ff1893000fbc6098003fd644c8095e3226218ff10121037b8629881bff65884037f30e2002ff1092115ffecaa089fff548c471ffa8a861affd052108ffaa69000bfc5250807ff9928604ff90d4106ffca788013fc40504017eb1a4206ffd971014ff864a08cbff654c807ff98a8611ffd5120027fc872080ffd534c0037e3026402ff0c921007fac898806fc604c405ff9926400ff50531047fe628801bfd658c409fe2128202ff0812109ffcc89801bfe414c40dfeb244206ef10541027fc80a1803ff624c01bff9962019ff10d210a7fea89800afc625044bff2946206ff106211b7f820a180bfc204c801ff30a4004ff10a41
  | 1 => 0xefc635080dffb146202bf98930007fa62a00a7fe3250417faa8e2001bf18121027f884a0003fd605080dfeb146207ff0c910025fcc9108dffc6250c037f3028619ff98d21027fc8120806ff6248003fe2028003fd0c531025fcc890003f521c4005ff292642bff54941037f8c118823fc4344021ff2a24004ff50e41037fcc52081aff659042bfe1928000ff58d21047fcc688006fc608c429ffb2a6000ff5913014ffcc4a0807ff304400dfea0e2021ff189310fffea110813fc4350005ffa128406ff0414100ff080a00bbbe43904077e31a8206ff90710017ee4310807fc304c00dff90c4203f794d3000ffaa088007fd50500237fb2a4029ff189410a5feca98003ff634840dfe0848201ffd4310037fec910883fe504c407fea1c6206bf19641037fc628800bfd3248403fe1028001fe0c130027fea8a081bfc5188409dfa128003bf18d1001dfcc720807ff30500017eb146235ff1954201fbe649801aff6388407fe18a601bff54d21037f843108bffd539040dfa10c4220ff141310dffea890803fd32504037f3048201ff481100077a84a000bfc52480717fb2a8609ffd0510037e863188e3ff5050c71fe28a8602bf98b100f7f8a910883fe104c447feaa26200ff8c54008ffeca90003fd634400dff28c4204ffd014200ffa608800ffc3250c47ffa926200ff4ca41147fcc0a083ffc3148003fea024004bf9913205dfacb8801bfd64c400dfeb16202bff99541035fec91880bfe5248469ff98a8404ffd054000df8c0a18dffc2150c09fe2a28601ff50130037fac120802fd644c00dff90e2006ff04231047fca688093fe508c46bff32a8413f7d0d30004feca88013ff549040dfe28e2000ffd9132197f8a299007fc204400dffb2c6200bf58e21197faca99002ff605084defa1c6201bf58310007f8c29801bfd648c44bfe2946201bf98132035f8c2980cbff504c80dff28e2006ff085211c7fca2a181bfc21c40097f3262006bf19310017fc84a101afe618c403ff282401dff90e21037fec78801ffe624405bff2948206ff19631097f8a49803bfc54c40057e3128006ff99710005fac11081bfe51504017fb122002ff10a21017fe429901bfe108c40dfe98c4200ff5052100ffca098003dc6350457fea8a8206fd94710015fcc4a181bff648c401fe30a8611ff55120027f8a920802fd608c401feb02820dff14f10047fe6488002fd629042fffb2a8004ef10e41055feca88007fe104c00dfea8c8224ff14231037fa638800bfc3288401feb126027ffd4a31017fea49000bfc214c803ff0824014ff5513000ff8a0980c7fc544c815be32a2003ff8c931035fecb1880bfc424c8017eb246200ff58542037fc8290877fc438842dff9928020ff90131027f884a1803fd6348001ffb1a8002f78c93200dfcc0988afff505040b7e3
  | 2 => 0x42037fcc918857fe625000dff10e2006ff0c521037f821108c3fc504c805ffa926400bf5922100df8c0a08e3fd5250c05fea124013ffd0930035f8c72088bff404c4017fb0a860bff54b1001ff8a6a1803fd604c829feb2a6018ff90121037faa31081bfc1048401ffb026206ff9051010ffc8498803fd424c005f72924003ff8c943027fea8a180bff3250871ff32a8606ff0c541027fa82a005bfe535000dff3048200fb4852001fee631880ffe304c4297eb2a6004efd0540025fcc888003fd43c400dff98c6233ff18142027faa8a0816fc65500017fb12801bbfd9521037f8632080bfc5248431ff2824202bfd8942017fc84900d3fe535080d7fb262032ff94532067fc6588087ff204c405fe1028428ff84141037f8c110807fe40c4007ef9826202ff4ca2100ff82188002ff614c065ff32a6428ff14141037fcc720812fe648c401dfb226400ffd8d2001fde6499002fd644803ffea9c4200bfd8941167fca120813bf4050815ff32a2003ff0c1310c7fc20908a3fe5050437feaa2421fffd5221037fec7208cffe3050823fe32a4005bf1954200fe8218803fff314800fff90a2015ffc8540015f8c488083fe204c407fea9a8606ff14510037bc62988b7fc5290435ff3224201ffd41100177c84a1013fe4350007ff98a6000ffd912004ff8a88800ffe4350c01ffb222025ff90a3100ffc6090007ff4048005ff1926402ff54932027faa92081bfc2144031fe2824200f74c53000ffe809805ffc5150007ff1846200ff4cb1015ffea4a082ffd53c400dfe18c6200ffd8d41017fca510802ff63480017fb024201ff14120007fac2a185ffe6550061fe0826403f710e3101f7c86a1802ff604c4037f3024200ff5852019ffcc0a1007ff5050011fe29a2001bfd8d3002df8ca9004bfe424c06fff2928606ff842410aff842a000eff614c409fe2a28006ff9451017ffea520803fd614c845ff2a26213ff19130057eca2880d7ff5150803ff1826006ef90541187f8c0990b3fc50904017eb1c820bffd5310097fcc49805efd6550007ee21a6005bf9954201ff86118806ff6050071fea8a8606ff8852100dfec090002ff615000dfeb046204ff10542037fa4388093fe208c437fea8a4206ff506210bffca2a000aff645082dfe29a801aff1512101f7886a1802fd6244007ffa9a6008ff90d10017de429000efc6350021ff3224004bf1913008ffea690002ff6448407fea9a6401ff8812000ffc4098002ff6448009ff202820cff94b1000ffe4098013ff4350827ff2a26001ffc8120007fa8690877fc5388403fe1824002ff8c921005fac890803fd314400dfe18a6200bfd814301fbe649881ffc424400dff20c4201ff10110197faa299087fc524c409fea1a8204bf19132037faa38800efe63500017fb028206ff59621017f6409000
  | 3 => 0xfb024201bf18241037f86310803fc6150001feb0a6001ff901100d7fe809080bff21508015fb226200ff591211aff8a2a10abff3150407ff29c620aff54910007fa8688002fd644c813fe3222000f74c930037fccb18807fc2048057deaa28200ff98532027fe80a0853dd534c06fff3128606ff98b1002dfccb2081bff319040d7e31e2006ff58221025fec2a081bfc64c4003fa0822004ff50d4000ff8409800bfc5288405fe10a8403ff0c54318ffcc899013fe4250401ffb224203ff0c1320affc64a000ffe534c003fc1024032bfd9532027fe812085ffd5350003ff8822001ff041100a7fcca980a3fe30504057f3126201ff901401a7fcc6a105ffd525000dfeb2e2034ff14d42167fc6120813fe4290403fe0828023ffd4531007fec49880fff434c4037e302842dffc82410fffaa910813ff4150803fea062006bf18520017fe649001bfc31c40037f3044235ff94542187fcc099007f8104400dfd8822000ffd913112ffe4118816fe658c40dffb2c8206ff99310007fac4a080bfe2048431fe3024203bf98e2102dfcca9806fff5348401ffb028206ff8422101ffe64980dbfe5050c6ffe2928603ffd4d31017fe409081aff65c400df610a4200ff4c910015fcc488007fe50c400b7e32a6404af191320bdfecaa0047ed5248039fe2844228ff88141017c8429080bff5288441ff3026201ff84310037f8cb1082bfd5344001fe9928004f7d0d43117fe8498833fc52c400d7e31c4204ff90d42027f880a1016fe6588457ffa9a8200ffd852017ffea72082bff54440057fb12642cff88241027faa8a1816fe6548401fea12620fff18d20005fec6a0083fc604c405fe2128436ff841430d7fca89086efd6548463efa1a6438ff5414305ffaa988013fe54504097f3226206ffd822109ff8829801bfc418c40b3e32a200afd545100c7f86090813ff5450071ffa928603ffd0e31035fecb108dbfc5050c39fe2044202ff0c942027fc82a009ffd548c42ddf21a8010ffd0d20037fea318843fc414800fff2922001fe8431001dfcc6a081bfc628c455fe31a8206fd88710017f8a499007bc4050001feb0a8001fd84310027f886a1003ff6344051fe1828230ff941320a7fea29802bfd51440017eb1e2011ff99520017fea490802ff6148017ffa962029ff14941037fac52080fff434c003fe2862011ffd45200affca4a0016fe6548059fe1848235ff5414201ffa869880efc6348001feb222032ff551321c5facaa1816fc6544039ff2044217ff54540017faa4908a7fe525040dfe32c8200ff48510007ea42880c3fe104c807ff98a6200ff50e21035f8c91081afe6190405ff1944204ef10d40035f8c51881bff62c4007fb98a6203bfd8d43017fe8490002ff624c405fea944200ff50a31007fec298003fd6448001fea0a2000ff58d
  | 4 => 0x73fe308844dffa146202ff90a21017dc649081bff608c45dff9948202ef10942035fcc31080bfd424840dff28c6206ff1054101dfcc6a1003ff604c821fe2a24023ff59531005fac98801bff638840b7f32a2023bfd9531097f84298007fd4044005ffa124202ff50932007fac6a000fff304c40dfe20a4204ff9094308ffca29000ffc434c427fe2a26016ff0c540027fe8520807fc404800d7fb24420fff14d20027fe87208d7fd5350801ff30a6001ff10130037f8628800efc6348409ffa028600ffd891002df8ca90802ff6444007fe1926028ff1814101ff8a698043fc6448015ffb2a2004fbd09420a7fca298003ff6150803ff2828006ffcc71011ffaa09881bfc4190465ffaa26405bf9954017dfacb2086bff434843f7eb2c4200b7d8d4101ffc60a180bff2088409ffa1a8203f710d430dffea29083ffe434800b7f32e2000fb4c92100ffc618801bfe314c405ff2928425ff10a3100ffe818801aff63c400df790c4224ff10231017fc411081bfe648840ffe2922004fd10541007fec0a18dbfe2050c3fffa9c4204ff509410077ec898833fe42c4003ff2822002ff0c920117fe829880bfe424c801fe98a4002ff1092001ffc8698012fc6448001ffb1a8404ef9514101ff8651882bfd654402bfe2928023bf59531097f8849801bf44190401feb026235ff54542057faa8880dbfe6050c57ffa8a8203ff4c530037f8c72081afc6150c23feb2a402bbfd954101ffe611881bff5190463ffa026400ff1854201ff88698087fe624c441fe102621bffd9521007ba649883ffc4348003fea824004ff95143025f8c898813ff42504077fb228601ff841101bffe40a181afc65c4003ff9824003ffd4d43037f8c91889bff408c44ffea846201fd8411000ffc20a007bfe5488415ffa922001ff14110017b864990d6fd6550839fe1844203bf98f1001ffc6099013fd5450007ee21a6403bf58e31037f88298867ff3148407ff9926211bf59520007fc6290007fe20c400dffb048218ff8c121035f8cb10802ff614c807ff29a6200ef5054001ffea718807ff20c4007fd9826000ffd8941027fa852082fff53c4063fe3226401ffcc130007fac0a185fff5250003fea826001ff14140007f8c2900dfff2150c0dffa0c620fff94d20187fc809900ffc314c805f790a6406ff88510017fc849080ffc3050c07ff9946206ff58e21007ec4288003fe6150807ff18a6018ff98121087fe82900d7ff6550839ff2844203bf98d10037f8c9108e3ff6550c017fb026435ffd4142035f8c91880bfe204c805ff9026422ff9913100dfec098013fe549046dfe3028601ff0c310007fac09081afc62c4003fe982400eff95310005fac68806bfc64484017fb226213ffd0530035fec698803fd2150001ff10a8006ff58e41127f8411881ffe3244001f
  | 5 => 0x4826008520018590440342580500607c002b00000000d80401a221248010b00280000800216c030180120380600405200c778010160c02301600a000048015408206c00a0060e42e8011d600c248600000cc0100000600864024016648038140000d40001203a0040000001c014020c20080809c00b0680140000f050008000020340cc028060081b86100206e0340480d00031c0100100693c2b80bfe524800b7f32a8204ff15142017faa4a1006fc6088403ffa022004ff90940027faa8a1006fe6050801ffb0a6419ffcc1210b7fe62a00d3ff3050825ff2926003ff94d320dffaa09081ffe424405dff984821effd0e2116ff86520807fe3044003ffa028006ff54631017fa429001bfe3148467ff0828400ffd8540005fac120802ff61508017fb128602ffd494200dfcc0a0813fc43904097f3226017ff595401c7facaa1847fd5148055ff9828233ff14142015fec6990affd5050429fea8a6000ff5891001ffea699007dc304c065fe32a6403ffd0d4301ffe869901bff51884057e3126006ff58f1018ffca89905fbd5450003ff182802fff54241035fec588003ff6150c09fda028003ff50d32017fa851080bec324c843ff90a6206ff50631027f882a1803fc614c807ff98a6403f7cc1320b7f8c6a0003bc644c80dff20c6200ff48530017fe8510803fd4148003ff1028023ffd9531005fec69081bfc514c40dfe10a6216ff98d4000ffc4088013ff4150401ff20a4035ff59542027ee82a0802ff6344047ffa826202bf58a2107ffcc690016fe654c403ff9022004fdd064101db8c6a081bfc41c40017fb1a840affd4d10077fe8788002ff624c001fea0a6000bf59110037fe832081afc615083dffa044222ff1513113dfacb188e3fc6550c0dfe3048204ffd0943015f8c4a18bffd5290409fea1a842dff8ca4101ff8a6988affc6550457fea9a8200ff9053018ff8829901bff51c4003ff9028002bf989400cffca690807fc3044053ff902822eff94e41025fac92081bfe514c407fe21c6217ffd4d40147f840a081bfe65904057fb0a4203ff90e31017fe429006ffd6548405ff992422aff98d41007fec898013fc4050c4dff2a46202ff8c942027fc80a10abfe5350403ffa824009ff95110037fe4318813ff5450859fe1048206fb88521035fec8a083bff42c400dfe28c621bff99521037fec988013bf405044fffa846203bf98d20035f8c52080ffc538c401fea162033ff04142005fac89881bff3188403ffa826015ff18940117f8c898807be4050007ff21a6232ffd4532027fca8a0007fc3050003f71024006ff08631017f84290047fc51480017eb162035bfd9542157fe64a0802ff644c801bfb2a202bbf59541097fe4298023fc63440017fb226020ff1013110ff884988cafd654c829fe28a6026ff15231017fe8499
  | 6 => 0x2460002040100d014290000150500001700e010b580830f0481240300108402c2983500e9380104005002c05809000630010120200085900101e0240680c064000000150000140b04401e030020027460a00f81600a0080901d00c0000402409808441a2a01c03c1a80703c0cc0185300000c001d40ae1dc05818016004e98050024b80581d00e0541780400a07c059680160040e8120c094006805056000000000ee088420090ee0a07881200202da580001610c0080c0100f80081100200c000060020146500001a5a0010180040880400001e0084580b00813c0000500212c0180101208000002332094c709b38a0300f8010167381d04200005c45001000380030000000b80481601a0000d17501e978000000100080a8060000000082e034000018060260441a81102601800013064008000060020001b0eb66400c008020140580280001e0000d48d00000c0f00306803c002a206402000002006004108340b80001d0333a600006802008000091d1050010340020060340000f08e02c3c808012004000210020840e80394a5c03100001c074000310040040284700210800001028054009396141240280400001c0001300a6ac2600b02c4e0550170120180300707001c1
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf764cb100047f755911002cfc755922110edd3258e210067f65d89101967c654c910006de30d8d41004fd75d893100cfe70d8d21085bc7458d2002cfe75d91100b6bc4359130024be76d91320067f654c51018f3d7519132126fa30582310b6be43d8d40014fd73d85320d6bf41d9121006bf7458f10004ef725911000cfc70d8d10086be54d9120124ff7358d101fdf77158d10004ff7259131116bf42d913102cfc75d9120005df7358141036fb7058231154ff7359131036bc4159310006ef7258d21006fb7058d10016de624c930004fd7650a3109d9c744c53000cfe70d91310eedf3058e21016ef614c9210067e42d951016eef2058a41034ff70d8d1002cfe7558f1024cff7358d2002cfe75591102bdfb705913020e7c70d9510024fc74d8d20014fe7258241034fd715931001ede634c910006bc62d913119efa60d8142006f751d8540036f66118540006f76198532005bf7458d10004ff7650a3114ebd425922102cfc75d813201cfe73d8540016f66288510136df42d8d41004ff725913014dec7258141135de7618d4104ebc43582410d6bc40d9121176bd30d9131036dd3158a31006df53d8d41006bd5459310014fc74d89400aeee32d8940006bc60d9131004fd73d9120034fe71d894306dfb7058530014fe72592312167e31d9510027bb605094002cfe75d912002cfe75d8940014fe76d8931004fd75d8132024fc74d8931006dc52d8d41015ef734c921036d4614c530006f5611854300cfd72d912037ebd52d91321779c434ca41006bf6450531005ef7258540146bf4059310184fd73d8d2037ebc20d913201cfe73d9121006dc6218d4101edc634c9410cedf31d8d21357d74118d41005bf744c521004fd75d893002cfe755822101cfe735912002cfe75d814102c7c7558910036be4159221006df43d893000cfe70d894310eee32d89312cebd6550540034ff70d911037ebf52d913204ebf41d9110034fe7650b10006df7358d2001fd7614c931006bc601913200cfc7158b10004ff75d8d21014fe72d8143026bc649052002cfe7558a41024fe74d8520004fd75d85430057f755854000cfe76d8131025bc744c940034fe7158e21006bf64d89310557c7558d1002cfe755923100cfe70d8532004fd74d853037ebf21d9132264ff72591200067f6558d10396be30d9132004fd75d8142005df735052114eee62d8941014fd74d8542006ef5258a41006bf51d9131004ff75d8d10024fd72d8142014fc725923100df67088510034fc7159120024fd71d81410b6dc43591301cf746548510045dc7359110024fe7458231225f57548710034fd7158b10006be65d913100cfd74d8940204ff7159110174ff745913120e7d30d95100067f7559110034fe764cb1001cfc7359121045dc7358910004ff7558e2133cff7159131
  | 1 => 0x9131086bc64591200bd7c755854000df870505100d6be54d91210f6bc4359221004ff75d852012eee3258a31006ee20d893108d7c7558d20006df52d8d41004fd74d8121025be748c540004fd72d9130004fd74d8520036fb705824100cff72d912004ebc43d9110036bf745923118ebc54d9132004ff75d89410079d54d8d41007d4714c931004fe7688530024fc745891020e7f71d9510036dc3158e2102cfe7558241034fc7650a31035de714c93104dbc744c9101379f40d8d41136dc42d8d41004df735912101cfe73d89400c7e87048520366df6318543006be6519132156dc6358d4101cfc73d8540026bf6050540004ff7359110004ff7258f10156dc53d8d41106df3058f100d6be64d9121085bc744c520004fd75d8542004fd7558b10024fe7458d10004fd73d8141366dc41d8d41006bf21d9131004fe765093100cfe70d89100e6fa2058221346be71d9131036ee2158a31006bf72d91310c7f07048510036e4624871001ede634c52002cfe75d891002cfc7558241336df6418d4100cfc705912119cff70591200067f73d9510004fd72d8540006be6219131136dc54d8d41006dd52d8d410067c755911000cfc76485100067f65505102f6ed42d894002cfe755913000dbc7650940396bc53d9132034fd72d8d210cedc6358d2110eec6258931006dd634cb10004fd7558d2000cfd71d8910004fd75d8131006bc50d91320067f6548510004ff73592210aeec21d8940006bf54d9132086bc43d91200057f7558d2000cfe7158b10097e42148530006bc52d9131004fc7648540006df7359121006bd54d9131024fe74d8132006de20d8d41036be6150540116bc42d9131024fe76d9130036dd3158231006f410d8532034fe71d911009dde744c930004ff75593101b6fa40d8143006be70d9131014fe72d91200557c755891001cfc73d9110006bf6498532184ff7058d20005f7715813218f9f43d91320057f7558121004ff764c910006dc7358910006bd54d85402def541d8540004fd75d8141136df40d8d412bebc43d814302cfc755931001cfc73d8910025be74d8d4002cfe75d893022ef77648710006f76198540004ff7558910006df21d8d41006bf50d913201cdc7359310034ff7158b10006dd32d85303979f30d91321a6dc6358d42014dd73d9132034fe71d912035df77158d41245ef7258d20004fd75592210ceed3258a31024fd73d8143024ff7650510005ef725052101cfc73d8121176be30d9131036be41592313579e5418d41014fc72d8d1000cfe76d8141005ed7290520014fc7258241004ff7559231006ef32d891002cfc75d9121006bf7459132246ef20d893001cfe73d81213369f63191312a6dc43d8930065fb7058520016f46288510035dc764c931006dc735922100cfc74d814106edf32d8131004f
  | 2 => 0xb6dc31d8d4002cfc75d853210edf3258e2118dbe7498532275fb705912028edf32d8530004fd74d8d2137f9d73d913200cfc70d893101cdc7359221036ec2158a310c7e520485102aedf30d8d40006df63d81411b6fa30d8143006bf50d9131034fd70d8d10144ff70591100c6ef2058b10136df54d8d41014fe7259131004ff7559131024fe76d9120006ef7259120006ed52d8941037e4215052119ef86058142016dc624c930024be76d9131016e462485102167c41d951000dee704852002cfe75d8540004ff75d8530027b771505400c7e72048510035f7724851027ebd42d9120006df50d8d4109dde744c530006dc50d8d41016ee624cb1014eee42d89410d5bc74581210047f7558d2033df771591310067f21d951000cff73d9130024bc7458f10255fb7058d20034fe7650f1002cfe7558e41004ff7558b10006bd52d9131034fc71582210c6fa10d812101cfc73d912002cfe7559120106fa30d81310067e64d95102d5bd755054037ebc32d9132116bf40d9131034fc7650b1037f9e32d913203eec6258910004fd7558e410b59c735054037ebd20d913202c7c7559110036bf745922101edf604c930004ff7650b10014fd74d8d42006df634c94001ddf714c530004ff755822132ebf61191310067e72d951000cfc764c510024fc74582210067c42d95100d6bc43d912120e7f40d9510004fd75d89100b6dc6358d40036dc3158f1001dde7390530007bb7050940034fc7159132006df70d8d41014fc7258231006bf64905201bcfd74d9132067e421d812137ebf20d9132005bf72505402b6dd73d913000dbd74d8d40025bc744c540004ff7650530004ff75d8931014fc7258d1001cfd74d854301edc638c520037e4214c52100ddc704c9302b6bd40d913014eef21d8941006dd6518d41004fd74d81310067c75589100067f65d8d10006de6518d41017e7614c921004ff7458231004fd75d894000cfc7058a3102cfe755931020f7471d9510006bf74591300c6f860581213379e4118d41006bc64d8131034fc7158a31186f86058132014fc7258e4137fac32d9132004ff7258e4120f7610d951018ebe64d91321ae7c655091000cfe70d854220e7e30d9510005bf745853202cfc75d81430067d72d95101f4ff7158910006bf52d913100cbc7650940006dc20d8d41004fd7558a411a6de43d8d423a6dd43d8d4201cfe73d912000df67048510116bc54d9131004ff7058a41034fc7158e41004ff7258d103679c41d8d41004fd75d912100cfe7158f101fef710d8530024bc7458d203979e73d91320079c744c930147b87050540006f551d8532006dc63d8941006bc20d9131036ec6148520005ef7259110004fd755891002cfc7558e41014ff73d913201cfd70d9130016be62509400067f42d95100057f7559110176bc53d
  | 3 => 0xe60191310cedf3058d21005df735052000dbc7050540014fc725931023ef521d85200aeee42d894000cfc7058e2100cfe7058a3104dbc744c51002cfe7559121005bf74585200c7e72048710146bd4059310005bf744c940024fc74d8d21037e46248710396bd43d913237ebc73d9132006df43d8d2100dde704c530004fd75d8532004fd70d9121006dc7359121004ff735824100cfe70d8941036f7608851000cfc70d853200cfc705923112edd32d8d21004ff7058d2116ebd42d9121004fd74d8532004fe764c540004fd769052037cbe7619132006be62d9131006ef624851009f9f43d913007edc6358d20346bc10d913138def7259132005dd73d9120006f610d8532146fa60d8141006de6218d41006bd50d913100cfd73d853001cfc73d9121366dc10d8d4100df8704c51000cfd71d9110004ff7458d2000df47048510136dd54d8d411779c43905300cfcf314c92102cfc7559231024ff76591320067f7558241034fe71d9130006bf7458d21326df30d853206edf3258f1001ddc7350530036f810582310557c7559110036ee6148520006de60d8d41004fc7650930034fe7158221006de72d8d41027bb6050540176de4358e41014fe72d8d4100cfe765051001fd7714c530096ee62d893032fb7311913100cfe70d8520004ff75d814201cfe73d8941034fc764cb10006df65d8d4102cfc755913131ef621d8542006bc10d9132004fd70d8943006dd50d8d41014fe764c521006dc6018d41034fd74d8d4100cfc7059132136df7359231006df7359221046dc6358d10034fc7159221004fd70d8941006bc6418532024fe7458e21004ff7558a41004ff765091002cfe75d8520396bf31d913234ef641d8542137d441d8d41024fe74d8930004ff7358a41004fe7650d21006bf54d9131006bd70d9131034fd74d8941176bf53d9131004ff75d8940006be4259231004ff7259310004fd764cb1000ddd73d913020e7d71d95102edfb7058940004fd7650f1000df67048710004fd71d8d4002cfe75d8142006bf6519131006bd50d9132004ff75d81430079c744c931285df754c530004fd75d8d21007cf624c93002cfe75d8143005f7715893000cbd74d8d400067e73d9510014fe72d813102c7c7558d2003fe46248510036fb7058221075bc744cb1020e7c20d9510006bc60d9132024ff765912001dde73d9132005bf7458930004fd70d913101cfe7359110016f4764851001cfd70d8930036bc7650540004fd7650e21006bc50d913101fdb604c53002cfc75d8142005fb70485101b6fa60d81432c6bd43d913007ede63d8d2014eec20d8941006f56118542004fd75d8540005dd7318520004ff7158d20004ff7458b10006f761985200c6ed2058b10034ff72d8d2101cff7658d203779f7319132005f47158d20006bd51d9132
  | 4 => 0x81310cddc7350521016f6624871000cfc70d894102cfc75d8931006ef7258d10006bf7458d20095ec7258530155de76d8d41036bd41582410057f755852001cfc73d814211e7c654c5101a6df30d8d42075fb7058540136df71d8d41004fd71d8142004bf7458910034fc7158241006f651d8532004ff7650d20014fc72d8141014fd70d8d200067c65d8910006bd54d814101cfc73d8940004dd73d9120006bf64d813102cfe75d89310f6bf4059221007d7714c931006df635894103eec42d8910004fd764ca4114cfd7650521024bc7458d21106dd3058f10006bf75d91310b79c4358d400047f755824100cfe7058e41005bf744c540024fe74d8931006ec7259110005bf744c910036de3158e21006ed6348520006f421d85300b5be7350940006bc7458f10006f561185400c6fa60d8121006dd53d8d21024fc74d8132004fe7650d20015ec724c52120e7f70d9510004fe76905300cfcc634c921024fe7458d2010eee52d8931004fd75d81210057f755853001cfc73d81410b79e43d8d401b4fd74d9130004ff75d8930007db704c93000cfc765051000cfc7058e412c6dc43d9130007f37048510035e4714c921004ff7458e210067f7558d101beee32d8943006bd51d9131004fe768c54000cfe70d85430aeec52d8940104ff7058d10014fc7650521005ef724c52100cfe76d813202cfc75d8d21006df624c53009edf43d9130004fd7559310014fc72d8543006be71d9132006be65d913232f9f3019131024fc74d8131136dd40d8d41005ed7218530004fd75591101bcff7259132006bc72d913101ddc735053102cfc75d8141006fb705911000cdc764c530004ff7259110005dd7388530024bc7458d10004ff75d9131004ff75d812107edf3158d20004fc7650d2014ebf4259221004fc7650d1000dec7048520014fe7258d1014eec625894101edc634c52100cfe70d8931004fd74d8d10014ff70d9120004fe765052018f3e7519132006ef42d891018edc644c931005bf744c52001cfd71d8931006bd72d913101cfe76d8d20014fe76d8910024fd73d854301edc634c510036ec7648520006bf7459120007776588510034fe71592210b6bc43d8d40014fc72d853020e7e70d951000cfe705923100cdc764c930006bf20d9131024fe7458a310cedc43d8d21046dc32d8d10375be76d9132006dd70d8d41004ff735912001cdc7359121004fd71d8943004fd70d8d410b6df32d8d40004ff764c520004ff7258241016bc6250940034fc7158e21346bf6498543014fc72d9131006dd51d8d41034fd70d9110006df20d8d41006df635814107dde73185200067c6558d100c7e52048710144fd76505100d6bc6459121156dc32d8d41014ff764851000cfc72d8121006fb7058910014fe72d8d20006bc70d9132024fd72d8542006b
  | 5 => 0x4fe76905201a6dc31d8d4201cfe76d8d2102cfc7559130036f66118543006ef6348520006df638c54016eee3258a41004ff7458f10146fa10d8141096ef2158d2002cfe75d9130006ef725912100cfd73d9130025bf725094004df97098540034fc7650e21004fd70d8532006bc71d913204dbc7458d1036faf3219132005bf74589100047f755891001cfe7358910034fe71d9132004fd71d893012edf32d8d21176bc32d9131006de10d8d41016ec6288540024fc745823109ebe54d913020e7c10d9510004fd75d9110014ec7259110156de7618d4107dde73d9120016f4624851001cfe7358b10005ef7258131005bf744cb1002cfe75d91310067c72d95100067c7558d10004fd7558a3100cfc70d8520015ee7290520004ff71591320057f755813202cfc75d9130004fc7650520004fd72d9110006f771591100067c62d9510006bf65d9131036df3158a310b5bc7350940024fd72d8d4202cfc75d8131014fe72d854009ddc744c93000cfc70d9132006f77158d20034fe7158231176bc73d9131376bf631913218ebf41d9132004ff75d814120e7f20d9510006be42d9110034fd72d9121366df63985430067f6559110007b46150540016f6624851015e7c6550510005ef72585300067c755824101cfe76d8d102a6ed32d8930006bc645853202cfe75d894101dde7388530005ef704c92101cfe73d8141004ff764ca41164ff74591103379c31191310067c32d9510097cc624c930006bc651913101cfc73d913001cfe73d8520006f761985420cede53d8d2100cfe705912120e7d20d9510036ee2158a410057f75581310de7c6548510396dc43d91321173e7519131174be76191310067e62d9510005df735854000cfe7058d21006bd545923139def7258d4210eef21d8931004fe768c52001eec634c921156de43d8d41004fc7650910004fd72d8131046df31d8d10007eb7048520006ef628853029edf31d8132136bc425923102cfc75d8543136bf4059231385df735913202cfc75d9110034fc7688540006f561185320079f7350540004fd75d8d100057d7518540116be64d9131036de3158f1033ef631d8543006ed624ca41034f47158d20176bf31d9131036f8105824118ebc40d913218edf43d9132036bc4159221004fd74d8930024fd71d8941014fe72d854302cfe75d8d21006df7358d2131cff7159121006bf6418532036f4624871002cfe7558e2126cff7459120006dd73d9120006bc64d8532134df73591312e5bd7550940024fc7458b100adec7258540006bd5459221004fd75d8d40007d7614c530006be40d9121034fe71d8142136dd43d8d4103eef21d891000cfd74d8540034ec764c92100df47048710035dc714c931006ec7258d10006be10d9132006df735911001cfc7358a410079f744c930004ff75d
  | 6 => 0xd73d9132004ff7558a3137ebd72d9132027af725094002cfc7558f10007d4614c530034fe76d8543005bf7458d2126ebf40d9120096ee32d8930034fe7158e410567e76d951037dbe761913237ebe21d9132155dc7358141006be6019132205f77159110156de63d8d41024ff7650521116bc40d9131004fd70d8931006bf745891001eec764c921034ff7159310016bc76509400d6ed4258a41036ec2158a410cfcf304c921396bf43d9132004fd73d8940006bc65d913202cfe75d85320057f755891019fb8705094002cfc7558a3128ef631d8530004fd72d814301cfe7358241007af6250940014fe72d8530004df73591100067e43d9510036df315823101cfe73d8910006dc75d8d413579f4018d41136dc40d8d4101edf604c530256ef21d813201cfc7358b1031df77159121085bc7458520034fe71d8d40034dc764c93103dec7259110004ff7458d1002cfc7558231034fe76d8532034fc768c520034fc715913037edd73d9132006fb705913000cfe70d9110004ff7558f1032f9f321913101cde73d912025eef21d8d20024fc74d89300067f6550d10376bf621913220e7d40d9510014fe725931034df771589410067c65d8d10034fe71d8d2002c7c7558241024fe76d9110007bb7050540034fd70d8910004ff7058e21004fd7558f10006be75d91322addf735913002cfe75d813118ebe54d9132346be51d9131005fb7050510034fe715923101cfe7359121005bf744c510004fd71d912001cfe73d8142006f77158d1018ebe7619132014fc7258f1002cfe75d912127ebf42d912002cfc7559120014fe76d8940005df7358542006dd634ca41006f56118520004fd72d8530005bf7458931014ff70d8d20006dd72d8d41006de73d91201beec6258943006df75d8d41006be60d9131036bc4159231006bf6450510016ec624c940014fe72d9110004fd72d8d41006ed52d8931046de63d8d10004fd7559132004ff75d8d4102cfc7558b10004ff75d85430067f31d951002cfc75d85421957c755813201edc634c940176df3058e41156df31d8d41004ff7458d2100cfe764c51000cfe7058a41014fe72d9131024fe7458d21006be72d9131004ff75d853210eec20d8931006ef52d89401fcff7158d10004ff7558231004df7359221006df7359310005df735812101cfd70d85301b4ff7059130014fd70d9120316f621d8532004fc764c91001cfd72d91322cebf6550540005df7350510007b76150540005bf7458530004ff7358910177b731d913110dec7258131006dd634c91016cff74591212c6bf43d9130366de51d8d41244ff7258d200cede63d8d210b6de63d8d4002cfe75d894300cfd7158221004ff7558d100079c644c9310a57c7558530006bd5459110004fc7650931024fc74d8910034ff7158f1001cff764c510
  | 7 => 0xc521006bf64905302aebd74d8d40004ff7258231035f7758851002cfc75d8d100079f744c93100cfc70d9121034fd72d8121024fe7458910106fa60d81312fdfb7058d400079c744c530136de54d8d41187d8704c93002cfe75d8530026bc645093132fb43119131024fe76d913203df97098520034fc7650f101bfe42150d21176be4358e4101dde7348530024fe74582210c5f57288510024bc7458910106fa10d813102cfc75591210067f7558910014fe72d8d40006df4358d2001cfc7358910017cf734c92100dbc7650540036dc3158e41346bf10d9131007e4614852001cfc735911003eec32d891001dde73d9130107d8704c5301b6f860581430c6fa20d8121004fd73d8121014fc764c521004ff76509300e6ed20d8910016dc764c930014fc72d9110014fd71d91212acff735913003eee62d8910396bc31d9132004ff764c94014fe42159121016ec628853009ddc744c530004fd75591301d5f7754851010eee62d8931004fd755822116ebf42d9121004fd72d8d4037ebe32d9132004ff735822120e7d10d9510007e4714c9211edf67688510014fc72d8540024fc7458a310e6ef20d8910006dc7359310396bd53d9132014fe72d9130004fe7650d101beee42d894301fcf724c93020e7c71d9510004ff7059221004fe764c9413369f6418d41024fc74d85300067e63d951000cfe764851001cfd72d8532024fe74d8532116bc645913101cfc7359120036dc614c530005dd7348530004ff7650e2101cfe735931030fcf434c921026bc645051028ef531d8530004ff75d911002cfc75d8d41004fd74d813234ebf40d85420afe42148540116bf41d9131136df41d8d410067e74d9510006be75d9131004ff7259231005df7359110006be51d9132036f81058221006df53d8d4004ebc42d9110005bd7498532076be545931004ebe64d9110004ff7650f10037f36088510005bf745813120e7e10d9510006ed624cb1000cfd72d8d20086bc41d9120004ff7558d210eedf30d8931166bf40d91100cfcc434c921034fc764ca41004ff7559120036ee2158b1002cfe75d91320079f644c931366df10d8d41034fd73d8931014fe72d8141004ff7558e41004fe768854018ede644c930007e532485100067f65d911002cfc7558d1000cfe76d8142005f47158132034fc7158a4100cfc7158f10006bd71d913200cfe7059221006bf7458d10034fc76885300cddc735812100dbe7050940386df32d8d42034fd73d8131096ec21d8930005df714c930004fd75d9130036df7358f10396be73d91320c4fd7648510035ee714c9210067c63d95103379c4118d4101cfc735824102cfe75591320cedc30d8d21037e77248510004fc764c94109ebc645913000cfe7059132006dc65d8d41006bd54d912001cfe76505310079d5418d41015d
  | 8 => 0x57f7558930036ec2158b10004fd75591210d6bf405912116eee4258a41005df7350a3102cfe75d8d42004fd74d8910004ff75d8d42006dd53d8d4100dde704c930176df3258e4101fcf724c931036be415931000cfc70d9131037e42148510235ef75485202d5bf755054002cfe7558231004fd7688530006f731d8520004fc7650d2101ddf724c93101ede634cb10176be73d913102cfc75d8930006df634c94100df47088510007e5324871037ebf32d9132225f77548710006dc62d8d4137ebd42d9132004ff7359310004ff7559110036ef7258a3111d7c7558131004fc764c520025bc744c941036e46148520004fd73d8941006df43d8132035f77648710036df7358e410067f74d9510036f76048510006f77158d211beee62d8943006bf651913220e7f10d95102debe54d854001cfe73d91301379e54d8d41014fe76d8930137d741d8d41004fd7650d20036ef7258a41025be7488540034fc7159231006dc70d8d413379e311913124edf30d8d2000cfc70d8d41004fe764c910037f0105051037ebc21d9132016ec6248510004fd71d9132265ef7259120005bf7458d20006bc6519132005ef725814120f7810d9510004ff75d8542006f76198530046dc43d8d10005f77158d20176bd32d9131004fd75582310067f6558910007cf634c921156de74d8d41034fe71d8132004fc764c94018edc644c9300b6dc53d8d40006de6018d41004fe76509303479c31d913109dbc7458930396be53d9132004fd71d8d2025edd32d8d20014fd71d8d21014fc72d8143004fd73d8540006be60d9132004ff7648530034fe71d8d4202cfc75d8530005df7350930346be21d9131006f56118530397af32d91320057d75985320067f41d951001cfd72d8132014fc72d8d40006df43d8d10176bc4358e41176bf30d9131266ef20d8940014fd74d814237ebd73d9132007ac744c92100cbc76505400dd7c7558121004ff7458a3136f9f31191320b79c434c940176bf71d9131016ef6048520005bd748854002cfc75d894302cfc7558910024fc7458e2100cf47648510136dc74d8d41186fa60d813201cfc74d8d40004fd764c9100bd7e7518540116be54d9131126df30d8d10004fd71d8143004ff7559121014fe76d8941004ff75d913003fe63248510006bf6458532016dc624c931005fb704c510366de21d8d41037e77248710156df30d8d412e5bf755094007edc4358d201df746588510006bd54d9121004ff75d891000dec7648520034fc71d891001cfe735922120e7c40d9510066ee3258b10005bf744ca41046df3258d1018dbc7458532024ff7650531206f710d8540006bf71d9132034fc7690520004fd72d8d10006bc65d9131004ff70591210067c64d9510004fd755913100cfc71d8121006bc645893101ddf724c930006df634
  | 9 => 0xd74d9510154fd7650531034fe71d891001cfe73d911002cfe75d8121004ff7059131036f6611854237ebe52d9132366dc21d8d41014fe7259110006bc64d8132176bd71d9131004fd73d911016eec5258a412b4ff7459130016ee624ca41326f631d853201cfc7359310014fe7258f1012eef2058a31136dd42d8d41004fd74d8d20004fd7558e21024fe76d9131156de53d8d4101eee634c921006dc635894114cff7259121006bc51d913202cfc75d8910004fd71d8132005ed728c520006be42d9130346bc71d91311f5f7715891010cfd764c521006bc7458910006df63d894100cfe70d9132016dc764c931005dd7390530006df73591310067c73d951037ebe20d9132336bf6319131004f77158d2000cfc70591310067f43d9510024fe74d8d20014fd73d913200cff72d8d20004bf7458d20004fd7650d210067f654c910006be40d913202cfc7558a41024fe74d813101cfd71d9131034fe76d8542006dc63d814100cfc70d8d42014fe7258231024fc7458f10005df7359121004fd75d8d201779f32d9131014fd73d813200cfc70d8943004fd71d8d4220e7f30d95100a57c7558930034fc71d911002cfe75d8d41036f67688510004ff7059231314ff7158d212167e21d951000cfc70d8d2120f7771d9510006bd6519132034fe76d8530034fc7690530004ff764c941156bd4359231366de41d8d41036fb10582310067c74d95100067f72d9510006bc70d9131377af2119132017eb604852002cfc7558e2129edc43d81320067c6559110015ef7148520346bc31d9131034fe7158241006be10d9131176bf43d9131004ff7559132006bf70d9131004fd7558d2102cfe7558d21176bd43d9131176be32d9131004fd7688540006bc6458131014fc7259130014fc7259110014fc72d913001cfc765053112cff7358d21004fe7648540004ff76509310057f7558141086be64d9120006bc7458d210cedc4358a31006de30d8d21037d4314c52101cfe7358221006f721d8530006df6518d41186fa20d8132005df7358520024fd70d8540285dd754c530006be70d9132106f8605813100cec7648520176bd53d9131014fc72d8d20004ff7458221004fe7650910037d4315053100cfc7159310005bd748c54000df47648510024fe74d8d2102cfe75d8132004fd73d9121006de75d8d4100777654851002cfe7558d20006bd6519131366de71d8d41006be4359221067e6324871000cfc73d8131116dd4358e411173d7519131006bc6458132004fe764c52004dbc745891016fe421d9121006de32d8d1000cfe76d8121034fe71d8d10036df7358e21004ff764c5400aeee62d8940006de32d8d41024fc7458d2000dbe7050540006dc635814102cfc7558d210aeec6258940006df4358a31036fb105824107edc31d8d2007ddc7350520
  | 10 => 0x913200ddc704c53000cfe76d8143006bc6019131004ff7058a31004fd75d85201f6f710d8520136df435923102cfe7558910006bf65d91323479e31d9131315f77158d2137ebf72d913207ddc7358520016de624c931004ff7159120004fd71d9130034fe7158a4100cfe70d91210f6ed42d8941004fd75d8d4202cfc75d8121004fc76485300079c73505400d5bc744c521036ed2158221006ef7258910006bc7458d1000ddc764c53001cfd71d8131006f771589103979f31d9132024fe74d81210067f7558d20006be50d9132024fe74d891037ebc72d9132036ed2158e21006f77159131004fd7558241166bd40d911037cff7459132004fc764c540024fc74d8520396bc30d9132024fc74d8d1009dbc7458530004fd75d8530004fd73d854200cfc70d891026ebd40d9120035ec714c921034fe76d8520004fd73d814235ef641d854301ddc7350a31006bc75d9132004ff7648540036f66118532004fd75d81430067e32d9510396be31d9132006bf70d9132396bf30d913201cfd74d8143384ff7359132005df724c530016ee624853000ddc764c93001cfe76d8d41004fd70d8d21046dc4358231176bf32d9131366df74d8d41006bc64d89313779c32191322167c31d9510034ff73d91310079f744c530004fd7650910007e7714c9211957e759853218dbc745813201cfc7358221004ff7558d20006ef7258d20006bf64d853202cfc7559110006bf645052102c7e76d95101c67c6550d1000cfe70d8d4220e7d70d9510005bf7150940004ff75d9120005f47158930357d44118d41036f66118530006be6519131034fc7158d20006bf7459110006df53d8d42177b431d913118e9c644c931004df73589102def641d854001ddc735093015d7c755814102cfe7559221346bc21d9131006df72d8d41325f77158931004ff735912100cfe7058e21006dd65d8d41007cd324853002cfc75d9132006bf6450931005bd74485401e5f57588510004fd70d8542006bd70d9132156df32d8d411779f30d9131006bc7458d203679e41d8d41004ff75d9121004fd7559120004ff7159130006be4358241005df735894132dbe76d9131004ff7650d10004ff7559221014fc73d8930004ff7358b1002cfe75d85431a6dc4359132396bd30d913201edc638c540006de65d8d4137f9c32d9132116be7619131036de3158e41176be53d9131006bd75d913125edf32d8d2002cfe7558a3129dfb7058930295df754c93001cde76d8d410067c43d951009ebe64d9130006bf7459131006fb7059120024fe74d8d10025bc744ca41034fe71d814301cff764c521004fd75d9131034fc7158231004fd7650d1000cfd74d8d4019efa20d814218edf435913203fe421581212a6df31d8930004fd74d893100cdd73d9130014fc72d8131006bf64589310067
  | 11 => 0x2cfc75d8d42306dd43d8d40034fc71d8d100057f7558d10006dc6518d41006dd634c520097cf214c930006bd65d9131006bf6458131004fd768c540034fd73d9131006bf6458132006bd54d913009edf4359130004ff745891001cdc7358910155dc7358941004bf7458f10006df638c520006de62d8d4138edc43d8943006fb7058d2002cfe75d8d20034fe71d8930034fe7650e21006bf7459121004fd73d8910014fe725913033edf6118d4123ef621d8520006ee20d8941126dd30d8d10005df7350530026bc6450531024fc7458d21006bd75d913200cfc70d8542006df7358d10014fe765052101cfc7359221024fc74d8121024fd70d8940006be52d9131026bc6490530034fe76d8540006df5358e410f6be54592212b6bf40d9130036dc764c530034ff72d9121024fc7458d10104fd764c5100067f32d9510026bf60509403779c7319132156dc4359231006f77159121004fd70d9132004fd75d8d410b79c43591300f6bf40d89411d5f57548510006f761985431a6dc53d8d4239edf43d8943045f97098530004fd72d814137ebd21d913224edd30d8d20115bc7458131035ec764c92137ebc52d9132006be43d911002cfe755913109d9c744c930004fd72d8543346bc51d9131004fe765053001cfd74d8943156dc30d8d41034fd74d8141006bf51d9132005bf744c941295dd754c930036f6611852001cfe73d8542004fd75d894100cfd72d8520006dc60d8d4121d7e76d951004ebc6459110006de52d8d4102cfe75d8d1000cfe70d8d10014ec7258d1002cfe75d8d40006bc64985320b5dc7358540006df7359130004ef7258d102167c21d9510004fe7648530007e76248510034fe7158a3101fdb604c930005df735891001cfc73d8941004ff7650d21006be40d9131036ef7258b1000cfd73d893002cfc75d8d40146fa40d8141004fd73d8520007cd324c5211a6de63d8d421a5dc735854200cfc7059221004fe764c940024fe7458f1001cfc73d85420067c7558d20024fe76d9121346bf73d9131366dc51d8d41136dd71d8d41034fc768c54036f9f30191320067f6550910006be43d91202167e41d951002cfe7558d1002cfe75d8542004ff75d894319cfd74d9120136de40d8d4102cfc75d8941006df435823118ebc6459132006ef72591320067c65d91100b6be4359130014fd71d812100cfc7058d21007af744c921006bc6219131004ff7059132004fd75d8943006be20d9131006dc7359110004fd72d913100cfc70d9110004fd75592310b5bc7350540036fb105822137ebf73d9132004fd71d89400047f7558d10024fd71d8d41045dc7350510004ff7650520017e7714852000cfe7059131007cf624c93102cfc75d894000cfd71d8d102bebe43d814302cfc7559132004fd768c52002cfc7558d20396bd31d
  | 12 => 0x1300004b03816e01d0750b100701a01001b00700006700100100b00d00001c01500000007c0ee00200500000200003701c00000800b0ad00101518ebc41d9132176bc30d9131024fe7458b10004fd75d913220e7c30d9510004fd70d85430afac6250940015ee728c52002cfc75d8540006f431d8520014fe72d8d10006f451d8540006be43d912101cfe76d8d40005bf7458121146f86058141004fd7690530346bf641854304ebe545911001cfe7358a41096ec625893010cff7258d21036bf7459310025be7448540006ef7259110005bf7458132005df704c931006df51d8d41014fc72591313969e73d9132176dc5358e4137e9d73d913210fe42158d21004ff7558241006bf64d81320d5bc7458d2120f7410d9510175be7619131006ef624c940004df7359310037e76248710005ef7258d10004ff75d8d20006bd54d9132006bc75d9131004fc7650530004ff75591302167e71d9510024fc74d853214eee52d89410e4ff7258910004bf7458d10004fd70d8d4210fcf214c93100cfe7159310026bc6450521014fe76d8943004ff75d8d4018ebf40d913237ebe72d9132036bc6150540024fe74d853020e7e40d9510186fa30d8132006ef6288540015ec7250521006be42d913100dbc7050940006df634c5100c4ff705891002cfc75d9131014fd70d8520006be50d91312bedc43d814302cfc7558221156bf435923100df87048510166fa405824102cfe7558b1019efa40d814201cfe76d8d420067c6558910004ff75d813200cfc7058a41006df7358910006de70d8d4103dec7258d10006bf75d91320eeed32d8931005df7350531025bf715054002c7c7558d1037faf21d9132034fd7158f10004fd7558d10346be31d9131024ff7659130136be5459231006bd65d9132024fd70d8d4000cfe70d8d41006dd75d8d4100cfc70d8543036de614c530004fd75d912001cff72d9132377ac3219132176bd73d9131235ed754852018ede644c93101edf614c93110fcc624c93112fe421d8d21037f36048510006df7359132014fc72d8d41006f47158d2008d7c7558520034ff70d8910396bf53d9132024fd73d8943006dc72d8d412fedf43d8143006de50d8d413779e3219132136de42d8d410b5be735054020e7e20d9510036ef2158e2101cfc73d8520014fe7258e41036ef21582210067d73d9510115bc7458931014fc72d91200b6de43d8d40004ff75d854001cff70d9130034fe71d8940036bf415824101ede634ca41004ff75d91320b79c438c54002cfc75d8d2001cdc7359110076be54d8141095ee721853037ebf42d913209ebc42d913009ebc41d9130007db704c530004ff7058e412177b10d95100cddc7359121004fd7650b10366dc71d8d41006dd32d813102cfc75d8520007e76148520016cc624c930004bf7458d21
  | 13 => 0x801a00003a0000b004e0100010020db00b00600101c2aa59a00400500100302c01208200312506b00000000000300202101900000701401b00000e00200100103300a05101c0bd00300901902c02a00500601001d08c02f0a70e102900711f00400001e03100133800400400001b00800b01900001001902e0000100280e40090010110f200c0420050090000060100bc00007b00302b00102c02800000401701302400400600707b00100200010201101000000a09301c03d0440040000030060d600302400e02b02b0000041a104c0ca04100000731518000401200a00100400003c00500300602400e0030320eb0080030110010d10460a301108019401d0061b309516d0e200e00b00501903300e00900b01000100522f08c00c01f00000300100000502400302401900f00403a1b700200b00004700004415700303d00101800c01200213e00104a00700c00800101000400012d01e0650090a402a00200500c00300f00400009c00000800100600500e00007600401500e03800002100000802b02204937700000000401801500e00001900009500002101000200c01e00007400e0290000392b100600a00300002d0111a902a00503901802702c03500200000f00000a00503601a00700907705c0010000000160d80080000030000000bb00800000003200100b01300603200e00c01100008f04800b01702004702301604901e24600102f0450000fa0950121e203502a00f00309b08e00400e00000000400000100e00000000b18100301700100f0000380480e102901500300200200000001309d06300000001b0060f700004905c00801e08502600600000900e00800b00002400000d00702500000304906701f0001b513600c00300000300600000000002f0000160080241030a803805900200400002003700b0210180093ee00f0450cf00301102a00f0070040fc06300001602600302705302a00300000000000204f01500900000700700608208a00102403f00209100100500e00603100200000f00026b00100200b09500100d1cf00201e01c1ae00000000003d0060f801700100b00005501a00800900100500000902800e0bc00e00003b02001e03502100003000101903838e09e00800500c00200701a00a00223c00300000f0120150100970150380340200290090120000740000130030280060bb01600300a02500000b09a0662200100260750010032440000140001b600000a00000106d10118900102900d01c0180591610090151cd1d20051be00a04000000003507d00e01a00c03b01201800000a00e06701900300700100001800000802a00100000101a05907800700901605507605000d1a606800000601201b02701056637000002300900b0d804302803d1300050100190020000010050cf0140050030460160050
  | 14 => 0x3600004301001606e00302501f00800100108c01602
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8de87143635040917d093b264880021fe15765091002c3e42aed20a60008be87043644c80156b0332ec8990037108773581210045fc22eca1a4000ccc7218d6050401b30e1ba264980030fdd4645813100656326e4b026205c3e7555360504031b90cb9c4298003171d4735911000666396c6b028200c3c74d9563440018deea392c68800365dd0714c9310043f438eab122000c6c75dc963440031bd0db9a8498002a761353d8d4200657ba6e4b1a2000a3d85988644c4031f100baac69099b27dd8744c5300245f43ee8b1a4206ae48158d21480df95cc5ba26520803271d073589100147743ee4b222068ab7845846150c010fd0e3aac6901caa7a0c70d9132006d210ee8b1a4200a3e85083644c42733908b9a4298003171cf65591100052f42e43b1a8200a9f84594635040156d02286c89900e3720d75593100046fc1aeab224200aad82994644c4011bd0e31ac0a081a3da1f7158d200054ec1cc03226200cac72191604c401968e838ac6900031bdd772591100045fc22ec99220058df8754f63484019aee638ac6900122fa1f7458f1032e4e398c9b126200cd4631c563480018beea39ac88801a2fa1e43592210061eba8c930a6466c9e739c7644c82d33906ba242a00030fdd764581310043fc2ae3b1260008bd87994644c8010fd0e3aac6880023de057558d200043fc2aeca1a40048be84dcd60884df53b07b86c8990031719773591100047dc02eab1a42008df835d564440031bd0db9a82980023de0575591103656b408a1b1a8200a9e8390b644400153b07aa6c8990161f21570d912100c7c402eab224200ce4211d9214c00117f08baac6900028fa1721d91310045ec24ec99220008dd83dd7644400b1ef0ea8ec2990033908676485300045fc22e7b024206ae4864c921c400d7890299262908030fdd464581320046fc1aeca12202ea9e83083644c4014bb0b90ec6a08028f61410d91320046fc1aeab262066a9e8655063504010ff0ab86c8908030f10f75582410052ec18c5b2a20018dc835d3604c40196ee838ac690003271d37358d100043fc2ae3b1280008df835d5624400b0f90ab86c899002b960810d85320363a30aeb30a6400c5f65dcd624400b1df0ea96c4988028f61721d91310051fc2ae1b226400e8c64d89324c4071b906baac8881a2ada0450d91310346ec1eebb226272a9e83143644c801d8a6590ec2980122f211764cb100061e3a8e8b122000a9d83994644c4dd5390c3a26498802b3a0a6518d4103476c16ebb22422ea9e831c3644c40155b0532ec8989b3271db73505400066639ee4b122078c5c75d0d63480018eaebb0cc29900237e0d76885400062e3aee6b122000c5c7319562440071bd07baec8880023be09764c9100045ec3cca3226200ace829976350401878ea322c09910a9da0472d9510
  | 1 => 0x8e5b22c0988022fa1f64589310052ec2841b1a8200c9c74dcd634845d53d06396c8988023be09755912001476412eca1a206faae821d7644c80d3990e992629099b27dd873505403764e3b0e899260038de83dd764484838e8edb2a42880023761c50d8d4101c6e41ae9b1220028ee87dc963440018eeebb8ac6900161f2157650d1001c6e418eca0a6000c5c75dcd644400147b0b396c89881a3b21d634852032ccf43ee898a60008bf87594644c4018bae639eca881bf271db744c9300245f424ec98a406f8bf845cf6050801968c838ac0990c6a7211634cb100051fc22e5b2a2000a3e859cb644c40155b09a92c52090b9908765485100046ec3841b1a82008bf845d5644c80187aea3aec899003710877359121396563b6e89924272aad821c7644c80117f08bb284880033918871589300046fc1ae9b024200c3d75d92614c80117d0fa96c89880327dd073591100063632ee4b1a2000c9d83dd1634800b1790eaa2c888003175d753d8d410245e422eab1a4200c5c751cd624400117d0fb22c2990021f61c43d951037d4ec1ee3b2264008bd87143644c80b0fd0fbaac1209d72b1c954591100052ec2cc5b1a8200a5e8318b65440031f50db8242881a3271db644c9310054f41c81b224200c5c73d9562440019c8e5b8ac6880023be097650d100046fc1aeab2240008df835d5644c001938c9b8264988031d1d77158d200347a40aeab244200c3f75dd1634400153b06106c8988028f61420d91313964e31ee899280038de87dcd64884051d904baac8880022fe11764cb100346e43ac698a40068ec8758932904011bf06ba6c4880023761e6518d411764e39ec8a0a627ca9f83594644c8d11790dba2c0988063b219728c52000c6ec1eebb226000ae482584614c0df958c5ba264a00baa7a0f649052003573436c290a40048be87dd163480018d8e432ac8880baa7a0f75d9131006cc39ee0a0a8000a3c855c3644c80196ec838ac099002a761353d8d410051ec2cc5b226200a74855846150001998e7b92c888002b560c21d8530006cc3a6e098a6000a5e831cb65440051bd0fb1a64a08031b1d772591100047bc3ac230a64008ef825da31500015cb0418ec29001a3d205755913000637b2ee4b2220008dd839d9434800b17f0eaa6c8988122f2117558f100052ec18e5b2a2000a9d84d4d63904011ef0eb08c2a00021f61476485400245e422eab122000c5f75dcd644400187aebaa6c8990028f61671d91320064e422e7b224026a9e841d763504010fd0e216ca880162fe1d54d91210347a40aeca1a406cad7835846150c0153b09310c6a08030fdd774589100052ec1c85b2a20038dc835da21500071bd0fb9ac89090a1fa1c75582410064f41ee8b1a406cc9d84dcd648840156b03328c8990162fe1d54d91300045fc22eab122000
  | 2 => 0xb54d91320146e41ae9b126000a9d83143644c80117d0e322c2990022fe117558d210245f43ee8b12200087f855da414c0d91bf06bb287108030f9d764985323654ec20ebb1a82038df875cf6448001878cbba2c68800ab3209634c91000636390cab1a2066c9c761d1314c0071b906bb285880062fa1b744c9400047bc0aeab22606fa9d831d7644c80156b02286c899002ada0665d9132006363a8e4b22200087e87d95644408587e83baac1208023be0975591300051e42ae1b2262008be87191604c8cd93cec32264988122f21173d81213666a38e86b1a4000ccc731c964440df55d04086c89900237e0d764c9100345e43aa8b2462008bf845d9434840195ee8392c6880022fe117559131006363a8e4b1a2002ace86d89324c00117b0e28ec8990030f5d754d91313be3bb88cab2220008dd839d941480d1938edba26298002a76126018d410043fc2aeca1a20018bd84dd76350001938e8b1a62900063721973905300061e32ee89922000c9c43dd932500011bd0e31ac4a080637219734853002c3f42eeca1a20068dc8758d329040187eea3a2c6880161f21571d894001573436c490a2000c9e735c3644c80117d0e322c0988062f21974485400062fb2ee6b22206c8dc86dcd60504051b90eb1a6488002a76126518d4100c5e422e7b028200a9d83143644c40153b09a96c6a0803271d3624c53036ccf43ee89926068a9d831c3644c40155b04286c8990021fa1f6558d103454ec18e5b2262048bc845d5634800b0f90abb482901be2f21b745813200667b94e5b1a82008be87d91604c801b30e1ba262980030f5d475d913100637b2ee4b1a2000ad583043614c8014bb0b310c6a0802b560450d8d410046f43841b1a8200a5d83dd3654400d3cd0fb8a64908161fa1f7558d1000746316c8992620587e86dd562440e555b05b86c8991b7271cc64d813200557414cbb2262008f787584615080117f08bb286880030f19774589101364e3a6c69928279a9e84194635040b0fd0bbb2848800a3b209768c5401354f420e1b1a8200c6f751c964440df53b06386c8991bf271db744c9313764e3b0e89926200c3c75d91604c40153d0dba2649880237e0d75591310043ec2eeca1220008bd87043644c80153b09a9ec6a009b2719373505310062e32ee6a0a2041a75811cb65440014bd0b316c6a0802ad60450d91310051f42821b226400a9f83594644c4cb938e6326c0988032b1d37258d100045f438c8b126200c3f751d162440014bd07ba6ca8800a3760f75d91320043fc2aec9922000c3c65dd131440018beebb9ac48800333dcf72591100045f43841b226200a3e859c7644c8014bd0b310c6a09b72b1d8744c9210054ec1cc43226272c9c63dd132504031d90cb9482900122f210764c54002c5fc3aa9b224076c9c73551648840195
  | 3 => 0x499280048bc845d932440071b906ba6c0908022fa1c50d91320061e3a8e8b1a4000ab58414761500018d8e5b2ac6880033318f72581410056a41ac230a40018bc865d221500e593cc7ba265208032b1d07258d100346e43ac6996200587e85dd9324400159d04286c6a08030f5d074d95103954f41821b22646ce5651d47635040117d0e28ec8991caa7a0c75d9132006b210eeab024200c6f75dc9634400d5990c99262908030f1d774589100043ec2eec99220008f787584614800117d0e286c8988021fa1c6558d1000566c14cbb1a8206ad686d85314c0018beea39ac4880030fd977458910006cc386e6a0a8006ad48158d314800d1790eaa2c9108032bdd072591103b64f39aa9b224068e9461dd1314c0011ef0eb08c298002b9219324851001c6e41aeca122000aae82143644c4018becbb9a828800317dd75358e4102c3f43eeab122000cb774dc563480f753b07300c8990163be1d52d89410245f43ee8b1a2000aad84d4b6250001968e9b8ac6900031ddd47158d2000566c14ca31a8268e3651d47644c4011bf06bb286909061f21b755891000477c12eab22200587e87dd5644402d33906ba442a0002aba0a65191310051e422e5b2a2026a9e84d4b6350401878ebba2c6900122f2117558d1000556c10a1b2262008bd87143644c4018b8e7b2a82880028fe1173d95100047dc02eab224200a9d8408363504071bd0fb9ac88800b331c932d853001c6f41eebb226000c9c74d8d31440e553d07baec89900a3b209755913037d4ec1eebb226400c3f65dd131440af938e831ec0a08023de057650d200061e3a8c8b026200a9e848c3634840b1bf0ea9ec6a080333dcc7258d100047bc3ac230a867ac9f73191614c801b4ee838a64909bfa318b744c9303354e432a831a820087d8710b654400b0f90abb286900030fdd764581320062e32ee6b1220688bf845d943c40018e8ea38ac6900022fe117558f100046ec1eebb224000ab584d476150001878e832ac48800e37a0f75d91203454ec1eebb22626ee8c621d1324c0d95390caa6c6a080e3720d7559120006663b26490a60038de839d941480ed93cecaa6c6a0803175d753d8d420046f43ec6b02826fa9d831c7644c8010fd0e21eca88196a7a1b644c9310061e3aee8b1a20008df835d942c40010fd0e3aac8880122f210764c94000636396cab222000c9c74d8d3148401958e9b92c48800a3b2097558d100062fbaec6b028200c9e84dcd64884015ab02106c6a080327dd373589103364e3b0c8992620587c855d9424400117b09b9ac1108161f21570d91310054ec1821b226466c9e731c7644c80517d0fb228498803175d475d8d4130ec63a26498a4200c9c73d914148401b48e838a6490802ada0665191320043f438cab2220028f581dd7644840187cea324c299002ab60
  | 4 => 0x9201a2a01c050bc1c18824000192804617c245082d000000044c5ec000000701417001c10b000034020040c0400d07400044290e899000480f00b0c48800c026edb4008240003200c400001b01c9701c1a1bc1f0000200c16100312240a15c060102f044470100104c000845103834008990ac040e800034010002707c1700c0e288020001303031018810000003016000820dc0712c0207400018000081d000000043c0041100c1f0000539c08014000f00147908b9eca8801a3d20575591203b64e39aa8b262000c3f65dd16344001878e9b2ac4880162fe1d54d913200657b26e4b026226a9e8414363504cd938ec39a82a00161fa1476485400045fc22eab1a20008df835d5644c8051bd0fb1a64a01b2a761372d8d410046ec1eebb2242008df835d943440071b906baac8908036908774581210061e3aec8b026400c5c75d8d60504014eb0a086c29901a3d2057558d200054ec20a1b1a8200c3c751d1634400187eea3a2c6901b2b5a0420d8d410054e41aa8b2442008f7815d932440d9b8843b9a82908062fa1b744c5400043fc2aed20a40008df835d564884010fd0e32ac4880039918b65485103455b40841b226200a9c8355364484018d8cbb92c8880161f215764c9100357340ec490a20068ec8758932c40019a8e7b8ac48800327dd073589100061fbac86b0482008be87d91604c40193886ba6c4981b237e0d7650f100043f43ecab122000ab581083644c46353908b1a64880028fa1662191310043fc2ae1b226400c5d75d4f63500071bd0fb9ac4880032710f7458a310045ec24ec98a40008de87d8d625040559d05b1a64a09a369087744c52101c6e41aeab244200aad82043644c80187eebba2c69000387d955418d4101c6e41aeab122000cb464dc5604c8010fb0bbb28688003271cf64505100062e398cab222042c3d41dd560904df55d04286c8990031d1d771591103b64e39aa8b22202ea9e83143644c40117b0fa96c8988022fe1d65191323374a308e898a6026a9e8408363504014bd07216ca880021f61f21d95100051fc2ae1b22620587c855c7624c001878e9b2a64880032dd9371581320046fc3aca31a8266c9f731d163c4001c6aa9a8ec2a0002b360850d8d410061e3a6ca98a206ca9d841c363504cd93ee839ac98800327dd0735912100667b98e4b2220068bc8755164c40014bd0a106c6a08161fa1f7558d2000673b90e2b1a401699e87dcd41500e555b043aec8990023be097558d100047bc0aeab224000c3f65dd132440018beea31ac0a080333d8f7258141006cc3a6e0992604187e87c876544001878e832ac688002a720d54d91200062e3a8c6b0282018bc865d23150001938e9b9ac4880028fa1662d913100477c12eca12200087f855c3644c40117b0e106c89880e37a1f735931001c7743ec
  | 5 => 0x81b0a818014020140e3080200c150000505c010181000c025282900428024000000c0140700000000240008c01c06188090988000c6700848028073b4000041201c88a2c2a014150680a134100047c05429050000001c32c1f094000001401002108020002d0181a02401654066d0000200100281
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2033525a5b741c5324c4cd894811d1634c520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x2
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x138e
  | 12 => 0x138b
  | 13 => 0x138c
  | 14 => 0x138d
  | 15 => 0x98c
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x9cb
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0xa0b
  | 22 => 0xa0c
  | 23 => 0xa0e
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1409
  | 29 => 0x140c
  | 30 => 0x140d
  | 31 => 0x140e
  | 32 => 0xb49
  | 33 => 0xb4b
  | 34 => 0xb4d
  | 35 => 0xb4e
  | 36 => 0x1449
  | 37 => 0x144b
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0xb89
  | 41 => 0xb8b
  | 42 => 0xb8c
  | 43 => 0xb8e
  | 44 => 0x1489
  | 45 => 0x148b
  | 46 => 0x148c
  | 47 => 0x148e
  | 48 => 0xcc9
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0xd09
  | 52 => 0xd0c
  | 53 => 0xd0e
  | 54 => 0xe89
  | 55 => 0xe8b
  | 56 => 0xe8e
  | 57 => 0xb0956
  | 58 => 0x94b16
  | 59 => 0x140956
  | 60 => 0x95416
  | 61 => 0x209
  | 62 => 0x1549
  | 63 => 0x16c9
  | 64 => 0x1849
  | 65 => 0x14c9
  | 66 => 0x134a
  | 67 => 0x2c9
  | 68 => 0x138b16
  | 69 => 0x4b
  | 70 => 0x98b16
  | 71 => 0x124b
  | 72 => 0x1709
  | 73 => 0x15c9
  | 74 => 0x168b
  | 75 => 0x12cb
  | 76 => 0x1889
  | 77 => 0x1609
  | 78 => 0x180b
  | 79 => 0x130b
  | 80 => 0x9cb56
  | 81 => 0x124c
  | 82 => 0x9ccd6
  | 83 => 0x150c
  | 84 => 0x128c
  | 85 => 0x18c9
  | 86 => 0x1789
  | 87 => 0x180c
  | 88 => 0x130c
  | 89 => 0xb8a16
  | 90 => 0xa0b96
  | 91 => 0x124d
  | 92 => 0xa0d16
  | 93 => 0x150d
  | 94 => 0x128d
  | 95 => 0x168d
  | 96 => 0x12cd
  | 97 => 0xccb15
  | 98 => 0x16cb
  | 99 => 0x184b
  | 100 => 0x154c
  | 101 => 0x28c
  | 102 => 0x58a
  | 103 => 0x184c
  | 104 => 0x178a
  | 105 => 0x154d
  | 106 => 0x24d
  | 107 => 0x16cd
  | 108 => 0x18ca
  | 109 => 0x40c
  | 110 => 0x58b
  | 111 => 0x178b
  | 112 => 0x18cb
  | 113 => 0x188c
  | 114 => 0x160c
  | 115 => 0x170d
  | 116 => 0x15cd
  | 117 => 0x104b
  | 118 => 0x104c
  | 119 => 0x2d851
  | 120 => 0x18ce
  | 121 => 0x194c
  | 122 => 0x59453
  | 123 => 0x589d3
  | 124 => 0x59a53
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1295
  | 6 => 2209
  | 5 => 670
  | 4 => 2
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
  | 7 => 2*((h/445+packedAt gbK7 (47915+(h % 445)*11) 11) % 1295)
  | 6 => 2*((h/736+packedAt gbK6 (106032+(h % 736)*12) 12) % 2209)
  | 5 => 2*((h/237+packedAt gbK5 (39530+(h % 237)*10) 10) % 670)
  | 4 => 2*((h/7+packedAt gbK4 (140+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff03e03e07f81fffffffffc13c8c780e3fff
  | 1 => 0xf01fc003ff87fe1fe0ff01fc6d373a471ce73
  | 2 => 0xf001ffffc0007ffe1ff0ffe038e383c781f39c
  | 3 => 0x1ffffffff80001fff00003f03fc07fe03e0
  | 4 => 0x1ffffffffffffe00000003ffc0007fffc00
  | 5 => 0xfffe000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110c00a00a00900224111285000404080614a5
  | 1 => 0xa112c0114a82aa14a8aa05a825131a430ca52
  | 2 => 0xa021554d40204cd413a8cd4098a382c5816318
  | 3 => 0x80459a75a73500801dcc81832d03dc06da03e0
  | 4 => 0x888e39a39c677198000060c37fc00036dbc00
  | 5 => 0xccf0001c01840611010008103ffaeb70000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40531
namespace PEqualNP.Outside.L_meta_40531
open PEqualNP.Outside.L_meta_40531.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs4_3_0 : Interval s4Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 26 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 134 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := bs4_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2 := bgb_4_0
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
theorem bgb_5_576 : Interval gbAtlas 5 576 94 := block_range (n:=94) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 670 := (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576)))
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
theorem bgb_6_2208 : Interval gbAtlas 6 2208 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2209 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208)))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 47 := block_range (n:=47) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1295 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)) (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 bgb_7_1248))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 34, 42),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8feeaeeeafee8a8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40531.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[3,4]⟩,⟨.and,[0,6]⟩,⟨.or,[1,7]⟩,⟨.and,[1,3]⟩,⟨.or,[4,5]⟩,⟨.or,[2,10]⟩,⟨.and,[11,12]⟩,⟨.or,[8,9]⟩,⟨.or,[0,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40531

open PEqualNP.Outside.L_meta_40531 in
theorem PEqualNP.Outside.L_meta_40531 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276660392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
