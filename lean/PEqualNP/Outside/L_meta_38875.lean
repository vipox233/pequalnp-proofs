import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38875.Model
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


end PEqualNP.Outside.L_meta_38875.Model

namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
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

def SBf (j : Nat) : Nat := [8, 5, 6, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_38875

namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x4000100a0000c000004d0c908100200e001240015fc41fc40fd40fc31fd10fd32fc32fe32dc32fd42fc10fe10fd21fd41fe31ff42bc40fc21fe30fe40ff31fc30de32fe20ff10fc42fd20fe41fd43fe21ff43ff32ff20ff40be40ff21fd31fc43ff30ff41fc20fe42fd30fe43
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa43dc324c37c84a15f15232ef19621f741506fca890df14121f7994417e5210efaa810fd48421bf29063dc320c3ee21086f94a40de21083dc420cafca3a17714d42afa9a437e54106f8a6107715032bf29663de32906fca4206f90a40ee98a615d538827aa810df14d42bf290857f53506fca198ef94840beaa0415d53d077c63206f90120bf284657e520cafaa518df94e42bfa8243be54086fca1215f55110bfa9261df328cafca910df94431bea9c4374514837ca2205bd4910be29263be42102fca220df54232deaa6637f54cc77ea5205f94443de294817d51d02fea2905f54a20ef19083de430cafea2a15f54d21bea90877e53083bc64887d84110ee196417f54883d843105f54420bf28c877c515037880905754e21fd18061dc32887b865a077cc730be29e417c5050bbaa1196fd0941bf29481de324cbee630877d4632bf2a4415f53442f8a7886f50f42ee19421be54cc2f8a4a05f54440ae29a85de328837aa2205f95231bf29a417f524c6faa7885f94b40be2a463df438cafaa3085fd4540fb90c21de32087baa7a17790e31ef19081ec52443de85216fd5120bf288817c544cafca3195f94430df28c817d53042fca618dfd4c20bea9c83f721486faa121ef8c840bfaa2617d5290fda4210fe50040be2a661bc51903de4010778c921bea9e857d518c37a87207ed0320bea84837e51903f24010778c831df206617c5250efca8907d14542bf29083dc438cbb8a688778ca40be2a6217e530c37c80107714632ee194617d53107bc62186f10330b6292217e52442fca1105fd5221dfa1c839e32902fca4087e14121dfaa2617f54042fca990ded4142fa18c21ee210837c80085f14530bea8687bc54442fca3995754c109faa2617d5310a7aa8197d08610be282877e528cabca41977d0832bf28421be40c42fca5987b50842bf28885bc40082fca2085f54442bfa8a87bc40042baa7a16f90110cf19081dd53886fca2105f54b40dea8c817e54086fea4886fd0c41df2a6637d51902faa5987750c32bea8485bc40c42fca1a0f78c830bf28087f621086fca0107dd4530de20c81de438cb786320770c940ee29a417e540c2f8a0a0f78c9309f2a043de318c37882205d14542eea8c65f7514837e85217ed0140bfa9c41fb50486fca818f710a32be2a2217d508877c83207d50441df2a065bf32902fca7085f54a41bea9843bf31903bea9197bc8220be2a2617d54887f040086fd0d42ee192837e50902fca6196f101109f2a641ee320caf6a090dfd4132ee192637f53c437c82205f94641dea1481be408837e64207dcc531de99481df510cafaa1a15fd5320ef2a065f820c43be60185f54643be29a21de32c877e62206fd0e40bf29e217e518c2fca7a05fd4f21be29a817d53482fca80877cc431f7908437e53c8678a8887790f30
  | 1 => 0xe52083ba87986f90210bf298857e544caf8a818f790c31ef192637d520c6faa8985fd4e21beaa665de32d079865106f50c41bf280217e50ccafca190fbc8621de20641bd540cbe8a2906f10210bea8683775150afca5885f94642be2a0217c540837e81205fd5031bf2a4217e54103b865987790c43beaa0215e53d0afea8997794e20bf2a041bf40102faa3a1d714d20dfa1e85bf53103bea119770c810bfa98437e50d0abca6086f50e41de288813f54487ba63986f95310fa88021dd548caeea2907dcc410ee19041dd500caf8a9187ec8010dea12837c54cc6fea0a0df94021bea8085bd41106fca5a1f755032fba0e437c53507b865885f15021bf29c41bc53103bc86986f88640bf28061f6411077e82205f15032dd280819d540cafca998efd5110de204617d540c2fea4085f55032be2a0617d549037e85205f94421fd98461fb20c43f420085f94d10ee2a4657e5010b7c42205f95232eea14657e53486faa9905f14c10bfa8a617e5410afca7a0f70ca20f799465be40502faa4187b88120bfa8a657e52843b863187ec4210bf2a261de32cc7be64195b14930fd20081fb40082faa9884f55320dfa10817f53483bca1195f55330bf28865f4514c2fea4a0cf15120ee194837e50d0fde64105fd4d219eaa6617d548c67aa9885fd5231ef18261dc32107e862085f94e41ef194637d54483b86598d794e20ee19221f421042faa4085f94041dea00817d53103d8a498778c920be2a4417c544c7ba84195f55243bea9e417d54486fca521ef50c43bf28487bc329037a83205f54041eea18633f54442bea6905fd5110be2a643bf4210afca520df55241dea18817c54482faa8994f95032bfa8285bd41102faa818df54e42ba28a617e54443bca710f7d0c32fd904417d52103bea6a16fd0441bf298437c53c877a63205fd5030de190819c32102fea6a16fd0641bf2a621bd53103ba8621ef54840bea8e61bf521037c8520df95043beaa4657c54ccafaa718df54c20bea96837d52442fca8196fd0b41fc980617c53487bca9197714232f7a92215e53d077a62205f14c21bea9c41be311037ea7207bd4930bea8e65f441087b86490f70ca40bf28e41dc320c6f8a4986f90841efa9a437f5050efea098cf95310bfa9a81dd53882faa708770c821f721085de320837aa9907710c32bea80877f525033aa6206f50b41ee29a43bd540873865205f14131ef196617d53d07bc64086f8ca40ee19081dd53103bca7a15f95332bfa9e415d53102fea8195f14543af294657d50ccafaa221dfd4e10bea9421f721042fca9186e10320efa9a217f548c37ca7205f54231eea88657e500cafea6887794632ef98c63be4350ff081907b08420be29c43dd434c2fca120fd10721dfa0c817e53903f681207bcc932eea9821dc32c86fca7906f14e40ae29
  | 2 => 0x740708804384211542003400364060286201c8b0040f0861b004030100400007014030042c3260609c0a00c0407c0d0196600032099880880611802010000dc230000302420000000340b0c800014470003c00400154045343403cad000000b4002301a038020701e00460008000080008001544006780000c110082c080070607f001090016eba03d40825008000f403164200000d1ac100007a0ec362500714c006700911000000081a8240003b078301393d0440c0542600011000070e00c00c0207c2132c120000d0b0031082a254010a13c31c150000b014010180004cdb0243e294c243402020ff024100645e0300503c0201c1482c000000a00001010920000402c0100c000500b33805004000c409010320540b0000001c110180d0001b000060080000408000012981102c14bea9c657f54c86fca6205f54031de18881bd4350afea898df953309f2a661de32c8278a8985f14532de99081bf4310f7842206f10a41bf2a64177514c2faa510ef10220beaa4617c54c83bc65086795032bfa98217e5390f7a842077d4d20f710c41bf43102fca5a0fb0c820f710a437e528c6fea8105f54720bea9e813e54cc79ca4196f48440df280817f54cc2f8a4a0f78c531de90c817d51883f0a0a15f54b43bf2a263df540cbbc65a05f55321de2a241de428cbbca7a0f78ca30ae29a21bc21902fca020778ca21de21c817e53106fca318fe44010be28a417d500cb78a8985f94621ef29821df314c2fca621f794032bf28443ef4250afaa998fd4c431ee28065bd4210bee8320fec4110fb90c437c52042f8a5084f94040df298813d54cc7f440106f10c40be2a4217f54c42fea4a1efd5121bea8e85dd438c6faa92157d4d42e619041de32502f8a7105f55220fda82857d50cc7da64194f94240dfa8881dc32d06faa898d794c40bf29c43dc328c6f8a4885f94230dea9c81f7318c6fca3107794432df20061df4350efaa790df54a30de2a243df428cb7c8098774c832bf294617e52086f0a0a15f14b10de214817d510cbbca6205fd5120bfaa043df308c37aa9985f94743bc282437d510c37e8721df94740bfa96219e53103d865105f94a42ef210657d538c3b864905fd4a10bf29061be43902f8a6906f101309faa241b8400837880187714432bea86437c53842f8a910ef54a40fc200417d529037884205f15121bfaa4657d52c437ea3205f55210bf29e85bf21902faa598f70c430bea9a21bd54c43ba871977d0e43bfaa6657d5190bf640905f94031eea9e837c504cb7ca9905f94730bea8c657d53903bc64a0df54021df20a83f741087eea2a17b48020af29c43df500cb7c81905fd5210df204616f524c278a890f74c431bf28463f7100437e42205f94c10df21881de520cb78a4205f14542fb18863fb304c2fea890df54841ee980617
  | 3 => 0x420100103c000080e09c4246c13060270f0440082b06c1f0440f00010148352ac0a120940
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x2520ca5c635464297994324871c548c9219798f540429d640ca31a7596321025f6354840e359032883375190130d5d4f514829f6350a40ce50c5050b1e548cb31a7d94321023c6454321a759032cc3345110130d5d4f5150aba60d4440c7152434c37051141428f593504871c548c930ce994400825c6354b40b5584320c6b8604c4409d586544c25d6590c31d50cb514c27561d5030ced53504865e63d49109758e5090b4e528ca30b5586430c63c6548440a7988321035632d453097d8d52d025f63540219758f548831e6395021d3d48324425d650cb41cdd46404832c5210130d914b514c29f6454232c7994321034e528ca31c754f42d063e6414e108f181540871e5450f309758f525036752145308f59052c423d6494c319798e53483c83210020f8084200431f540c910bc580310431d548cb309d185500caba60146408f992530c2756508410c754c400435632d4520ae18132102b965103208f994329038832100208f99353c829f658c840d354832c43345414530e3990320823d6414931ae583421027b6055132c755032cc2bb604c440d354c32883a83210020c798e54c823d6595021c758e54c82d661d42328f980544869d63d06409758e500825e6514d20c7d4e404423d6414f20c755032cc69e6314c409ed95401025e6314141a7d8d519034d520c8419e181544c65c63548109718d500865f6354a40d30ca500831e53900108f59252083543214520cb150524c26f62551109dd85534834c528c931e3508420caf06148020cbd50524431e650ca409dd8554486b86050941c794d43d0b1f5414d21c714c404431e639503297d8d544823e601511097d8d5108276619513097988534829e6294c40d614c504871c53d0d42e68c840082d46154032c7550320863e65d09418f99053c8675650c4109bd89500c69d64d40328f593530866e62152319e582534873a5210020ba181210863d6414e10c754e501029e6388440c755032c834e520c831c7552510ca3f6550842ce593504872c54d49108f191510823d6414c20d590c514c25d63d4b109d58654482d86050d308f996404425c6354b10c7553500cb3b4314142a7593310c6ba600c440b5d85420cb983210320a7d8d42102b46150b419758e544866d650c820b5986324c63f6454221e3952520cacc6348020b9185200825f650cb419758f540439a3294040d358f524431c32940408f593528439a6310020d50c8514c29c6354640a798f429035453d4542d390c524c3375110130a7590500ca3d6494e2097194324431f54d4d208f993504cb5553cc410d68cb504874c5388120a7993510cabb604c8409758e51c825d6395021a7593510ca746155132a718d521025d6594c1097d96320423e6494910ced5050487375110120a7d8d21902b761548409758c540823d6494620
  | 1 => 0x29f6354a408f99052c423f6454632c7150324423d6494910ab58851102766115232c7552320865d6395120d5544510cb1d540cb1097d8d544871e540cb309758e544434c53d491097196324431d53904408f99053c434e520cb31add85421025e63950218f993504c71f53901209798e50c863e64948208f992510423c6454632c754e408825f654c431c7551500ca3e6415021ae580311039a32103208f592528425e63152209d584548cb1c5310120c7d50534425f6354a10c795032c42b76150a409798c548874e6294832ea084400831e32940408f191534831d548cb208f19150cca766195120a759331cc33754d4520c7594321031e6494e21cd945419031c540c9209e594200438c32902209e181544867a60d52218f191508ca7b6054d21d6d4f5050a9d63d4440ce59440c82b46448421d58c8514c2d76150a32c7950320863e6590130a7590518cb2c5290130c795032c83735114142ced905050a7561d53328f994544c32c5414910c7553430cb645214530d314a304c2db6050a32d5d46518ca9e64146329758e510873b6414121cbd4840443c832d00209bd89544c26e62150109ed81544825e658c910dc147204823d6414c21ad587529035b53141219758c540434c528c930b3988548ca3e6510120a7993508ca9c64542329798e500829c6055032c754e400431d5354840c7952520cb1d541443297d8d52d07546154c10ea98840082b86448020d314832503583214121a798f41102ce6388620ce95020c42756510421ea884400823d64d4132c794e501034e520cb30ad185425065e63953209d584530826d6215010d914a104439a631032097996324863e6415032c7d50324c2746154840d3d48325065e650c920b6d81420ca5c6354a40c754e511034f6314910a7590510cb4c520c9418f993528423e65151208f98254cc75853d4121c7592538823c64543319b588548c67b60551318f994544871d53508408f990524c71f540c921ae98a501037321141219798c54c863c64542218fd95411067960951218f59353c833451101208f990530831c53901108f191500865d650c8109718d54486ba6014c408f59053c42776155132d614f5050b4f53d4910a7990540ca3e64d41218f992534835453d4520b5584500cb5a3214121b5185420ca3e6414c21b958841087545314542ad984539032f54d4930c7992538825e6294c108f592528c25c6354420ce9085050b1f540c9209758c54842ba6014e409e983540c71f54d4d10ae983519038c32102209798c520423d6494d21c754c411025f654c832c7d95531023e6494620c7d53534869c6254c40a798f521027761551309798f525029e64140328f992538871d5310220a798e219025d6315221cdd4651902ba60148408f994321026e65149108f994544431f5310120c755
  | 2 => 0x60d5221cbd48404c3395410320ae980529034e63d491097d8d5190a796014c21c758e540863e65101309d185544833a60940409718d52d069d640c9308fd91518c29d63d48408f195219026e6294910ba189100434d520cb3097188534839832100208f993530869e6314840d394832d02b46150a40ce15320482da60144329bd95320ca9c6354a40c7594329029d640c8319b98a544425c63546409e181534865f6550c43d514e10442766114c2097594430cb4e520c8308fd91534823c6454031cd146404c23f6454910b5984500cab86048440e60ca501032c54d49309798e544825e63d4a10d3d4c52442d86050832f20c820c42d46150a32a758f419071f548c920e3990328829e63d44408f992528c23e64951109ed95100429d650c840a7593508cad96014432b398a320823d6414810c758c544c29c63484409799453487545314520d3d4a324431f548c92197d96321038d5494832d354832d025e63d48109758f525065d658c430c798e54c423c64540329dd95411066f6254d20e658c400825f63546408fd9153442756115020ae983539027761540329758e524431e5390220a758e211029e63d084097189530426d62d4f10c7992530427b6054910a798c519025d658cb41a758e219023f64544208f593504c6ba60cc840c794d431025d63d4a10f10c9210869e63d06409e594400835b53d41218f592534432f52901108f997311023f64542319798c540423e6095021e3988321029d63d08409b98b53c42ba60884408f992530425c63551109e181521065d63152209bd89544c6b46150842d3948321063f6454031f20c8200423f64543318f59353c425c6550d30b398b548ca3f6550c43cd153514831c54d4d109798a53d063e64951209718d54482d76154032a7191500ca3f6454d21eacc8400833754d4530d60cb50486b56114e4097996324834e520cb109758e54c836451881209b189500c7c9600c820c715053486cc624c0308f191524423c6454231c7d52324425e63951108f983544871d5350b418f992534875853141429798c54082ae6214440d3148324427765440109798e544874f520c9309bd954210a9d63d4a409d18553482bb6050840c714e40483575314520c754e431029d6314640c758e54c4354518c130ce150504863c64548108f5925104398404c0308f994404425e6315210cd146404825f658cb418f597319025d639432197594321026f6254d109758f524425e6394d2197596321025f6355110ae980511027561d4f20c755232cc67661d5220c794c408829d63144408f191518c29f63548408759432102d4614c03097596430ca5d6395132d58c8514833a64d41219e58354cca3d650c84097d95300c23e65086408fd91500865c6354910b9189100429d64cc631ad18542103575314542ad185521
  | 3 => 0x130cd50c5150ad86050a328f99352c43b040440109798a53102cd650ca20d3d48325029d6314840ea103200825e63d4941cb14a404434f6254e20f20ca20082ce62150329bd95210869e6095032a7593314c27a60951218f596421063f65500409718d528434d650ca20cd153514c23c6454d218f596540ca5c6254f418fd95211026c6255131cdd50514c31c5414d20e658c40c825e650c91097d8d520429d63d0440ad984521034c528c91097d8d524425e65cc530c7d4c40442ce62d50329718d521023e6494c3197596320426e6294d10c794c40042b960884409dd85544823e6494d109798e54c43345414520b5584548cb1c5414d10e30ca40082ba60d4c40d3d8c524c23f64540329e583540c65c63548419798e51c825c6254c4097d8d52c427a6094d2197d8d529065e6214d109798e510863c6015110c795232cc2ac6250d429798f52c433864141218f18154cc65d65d08328f990520425d6314141c754c511031c548c910c7592538873b60553208f594329033461550218fd9150ccab960cc8408f994211025e63d5220d5145314c2776154d10ad987529029e63d4a409d185544c33551144409bd95200834c524c5309758f54886b860508428fd91508cb9953940409798b534434c63149108f594219036752d4530a7596540cb1d548cb109798e524425d6315321c795032cc63e6495121a7990510ca6c6254d10c7153534825e63d52219b189544c27765484218fd91520427761548409b58a54442b561d0c419dd85524423f6454321a758f429023c6454d10b518d100431c63550328f592530c23d65cc440c7592530426d6295130a7d91518cb1e548c8219718d529071d53d4840b5587508ca9e628c840a7d91500ca786055132b3982520ca3d65084409758e54c429c63508409b98a544c34c5314910d350c524c27661d5332e3988329031c548c920ae983521023e64951309758e544c75432d4520c795232c823e65901208f592530431e6395330c7150324867661d4f20cd54441103396510020cdd0c5150a3f6548640a7191518ca9f6348440b5984548ca5f65508329d984540829e6314440c795232c42b86050b419798e5090a5e6514d10b398e210833454c8521cd553410865d63148109ed81521067661d5030a718d219031f5414d20ae98240082b86048640cdd50514825e6314c10c7153534863e6414f20aed812110277654c431ad584521035451cc530d6d4c5050a3d64d4b10dcd475050b5543145309e98354cca7a6014c21e30c8400827b6055121c7d52324c38d640c820c7150324c25f650c8109b189544432f54d4910ce153504871f6555032a7596531036852c4110cb148404423e6494e209d986534825f650c8408f181540ca5f63548419e596100429e64d4032d314b314c23d6494e21cbd50524c279
  | 4 => 0x70002101c0013c0103c002600003259030000001c0004f090471641166c197a42d000570085b52c6204019004dd0da8a008010000619c13001861ec02000e818c240247c111e317012010140100800003000000100707c0001c034a4031c8340365d57c170040109c08000011dc0007431008d80024200c020000500400824082518e854009a4040f8000e477010016700404c0605c13014020000001c2000049008040205e02000064220140400803830130040f060fd0000442c4001c040080003e0907c01000261d001088030a000078060b0d3000000000c03c012c030030040040400800018030881604c1d0440f000ab06818060660740000801464d7004190331c00c50008026c8005c80e6d0107b4270040509de200071004036185a1c80c00344078254fc000056b0e0120440f008040b80101801000079e00e0885c0740d04015000009ce560002500002000200500b00800000725420c6800401400c28008f000000890000016823c78040280c0d80317a2f3600d2100102c190582401c0a1cc15008055f40b004000000514c0e9840104c000000002c0054404a718d429023e64d4f10d3594320823e65cc6408f982540cb364214542dc1475050b1e5450c329798c540c31d53d0840da884504867561d52209758f52042f06048421a758f41106756194d20e694e50102ba60d4a40f2980320827b65480209b58a53442bb6048640ce95320c423d6494d209ed95300c3a962100208f992528425f6355132d3994320823d6414f219798e534432f5290
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x9c10d0008eb400142a21a005000001a8300205860610e02000c0000078c8a5a0000a02040b6a48e4a18a2a158870508420cb44b22c019041865516014432b10e0b206410515740c8514c2c539c42200410e1c16414931b08e2a10841949870593314c20ebb4a819043075da5310010d08c81924210e5151580510cac5bb06420041075da650c840c2aa630a8420499760c840c82a43828629261a418c4044010aa0e0a18a29841d7695032c820ebb4a6204412a1c9600c440d12ec190801068a760c8400820ebb0a8192612a5d832100209c0e4b00620858874580320820ebacc710881a8188404401091aec1908110489760c8400830ca98c0a16838554c6154840b14e51908010588735884008286392a6a90818354d6214440932ec1908010589760c84008264bb06420041a2188404c03083aed2a0658861554185500ca26392c6282838359052cc530c2aa630a85a0d887258c4008286392a6a1683a258d6210020a50e4a18a0a16256254451102e038ac01904183595640c820a30e0aa2a0195a071588400824c382c819261c29503208310a90e0a906420e196558c400834830880980618559051cc53091aec19080106c0321812108686392a6a1081381c16210421
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x101000b0000617889869ce2110020a108059051cc530a10805506154032c09651c1640c820a048254c6154840c81641c5600c820889879d83210020c09651c96310020c81631c56210020910805d03214530a048254c6150840a088254c6050b41909879503208310a088059052cc530a048254c6150b41
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
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
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/273+packedAt s0K5 (22140+(h % 273)*10) 10) % 820)
  | 4 => 2*((h/333+packedAt s0K4 (33972+(h % 333)*10) 10) % 894)
  | 3 => 2*((h/43+packedAt s0K3 (3332+(h % 43)*7) 7) % 68)
  | 2 => 2*((h/19+packedAt s0K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffff01ffffc0fffffffff80ffe3ffe3f
  | 2 => 0xfffc07ffffe03ffff03ffc0fffff03fcf1fc7
  | 3 => 0xf03fff80fffffffffffc0fff01fffffff1e3ff
  | 4 => 0xffc00000fffffc07fffff00001ffffc1fe03f8
  | 5 => 0xffffffff00000007fffffffffe000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x904a450a211c4891402cb2d14a588652166e1b
  | 2 => 0x8492931452243922cb015548acab9234cb16c5
  | 3 => 0x2c210a2694489244955409aa213528a961a16e
  | 4 => 0xc93a2c58e8912077669a6030c9c6cf11be03b0
  | 5 => 0xe3c3060f0e1c387b8e38e3cf0070c21fdd800
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fc00c000fcc0ccc0fc00c000fcc0ccc0fc00c000fcc0ccc0fc00c000fcc0ccc0fc00c000fcc0ccc0fc00c000fcc0ccc0fc00c000fcc0ccc0fc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38875
namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
def s1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x140400076906f32d843b8877906c32
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xa441482310d208e43886990732
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*4) 4
  | 3 => packedAt s1K3 (i*15) 15
  | 2 => packedAt s1K2 (i*26) 26
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s1K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt s1K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt s1K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 3 => 0x72ff81cffc070f8c
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 2 => 0x142322862122c64a
  | 3 => 0xd49751b48546b8c
  | 4 => 0x38241ac92608d60
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 29 s1Pos s1Neg, 0xfaaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_38875
namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2a007260010be42bd43bd40bc42bc41ec21ef20be41ed20bf40ee21bf43
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x128ea98831d53d02c8a2904b14943
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => 2*((h/11+packedAt s2K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s2K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 1 => 0xfffffe07f03ffffc1e07fffffc1e07ff93fe4f
  | 3 => 0xf81ffff8003f07ffe007ff07ffe00781e3cf8c
  | 4 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x9044444122084100a4494848812294a4261095
  | 1 => 0x218888324452822c0a8291932414215890e64a
  | 3 => 0x52d51490eaa44d556144ea45cb40560d634b8c
  | 4 => 0x651a21248c06969a5390308672996011d80d60
  | 5 => 0x861c39c70f38e7e39de73ce063118461ffb000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaacc88eeaa8888eeaacc88eeaa8888eeaacc88eeaa8888eeaacc88eeaa8888eeaacc88eeaa8888eeaacc88eeaa8888eeaacc88eeaa8888eeaacc88eeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38875
namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x20201001000000000000000be41dd31de30df32be42bd40bf40df31bc41bc42dd32dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc0400408eaaa3994b94a41ca20a63365190a9aa598cd1454096292818c424caaaa2185354830
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt s3K4 (192+(h % 25)*4) 4) % 12)
  | 3 => 2*((h/10+packedAt s3K3 (270+(h % 10)*4) 4) % 10)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x83ffffffffffffe07fffc0ffffffffff1e3fff
  | 1 => 0xfc1ffc0fc0fc1fff8783ff0fe0f83c1fe9ce93
  | 2 => 0xffe0fff000ffe0fff803fff0ff003fe0f1f31c
  | 4 => 0xffffff0000fffffc0000ffffc000fe03e0
  | 5 => 0xffff0000000000ffffffffff00000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa00004820020000011048011010a0508021425
  | 1 => 0x94648649548b46582a1550a68d0a85668ca92
  | 2 => 0x10ca9121a69285aaa84266a0ba4132c2b16318
  | 4 => 0x5a94e249341ad6f34ce83488dce5a084fc03c0
  | 5 => 0x6318c38e38e318dc7773b8cc10860318dfbc00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8aaaaa8a8eaeae8e8aaaaa8a8eaeae8e8aaaaa8a8eaeae8e8aaaaa8a8eaeae8e8aaaaa8a8eaeae8e8aaaaa8a8eaeae8e8aaaaa8a8eaeae8e8aaaaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38875
namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x20001c008014400105800018c78c000080684ff21fc41fd30fd20fe20ff10fc10fe41dc31ff20ff32fe43ff41fc42fd31fd21ff40fe32fc31fe40fc32df30fe10fc30bd40fc20fc21ff30ff43de31fc43fd10ff42fd41bc41ff31fd32fe31fd43be41fd40fe30bf40fe21fd42dd30fe42fc40
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x65dd53103be62986f54940fd906217e54cc37c84a17714a31ef20863f651082dea4885f95210bfa92817e51902faa0196710431f710241bf54442d8a4887790530af29e839c31d03f640085f94210aea9e43be41087f6a090dfd4e10de2a2437e5390efaa3205f94232bea9c85bc32d02fca8205f55021bea9421bd540cb7c8398df54b43cf18e81be43906baa7a0f750b30ce20c637f504cbbca8984f55210f7904415d53042fca9184f55010be29e217e548cafaa020f790c31be298217d52103b86288770c421fb88421bc41503f6611877906319f2a041bf43503bea418f78cb30de190837c53c83be6110778c421fb90c437d548c7ba83985f94d21bf29881de314437c82885f55110bea9a21bd40042f8a498fb4c832aea9c817d53486fca3986710530beaa061ee21883baa018e7d0130ef21661be52906fca2086fd4140ef98641bf52502bea7885f94221bf288637f548c37e80185f54f40ee18e433c544cbb863186ed4140be29c437d52886f8a4a0f790d32be29a415d53083be86a1ef10621de20e433e54cc6bca6186f10d409f28e81bf21d03bea818df94021ef21a61bf53906fca418f708530ee98221bd548c3f44010778c630df29883be418c2fca9106f50441df21681d6510c6faa010df94841afa9a85de21cc27ea8996f14e41efaa4637f544877a81886f54a41ef29c21bd540c2faa7186f4c940bf284417e544c6f8a2a1f754c10deaa0215f53442bca790df54f10bea8887de31cc2faa3196f8c540dea18833f54c43baa70877d0831eeaa261dc31cc2faa32177cc831de20a63df410c6faa021f7cc120bf2a021bd43d037a8621ef4c740cea0661de304c3be8518dfd4f20de296817e52042f8a4086f14a41dfa1483bf4350afaa5986f55020bf28081bd51502f8a09977cca31bfa8263fa300c2fea9905f94c20bfaa021bc53503b8a4986f8ca41df292817d54c87be8318df95130df99483df53486f8a6a05f15031bfaa261df43cc2fca1a0dfd4543bfaa4417d5090f7a80986fd0320dea00417c548877aa9105f94743dfa0c83f920083be60085fd4141dea10837c514c3be84985f54910efa8a61bd42d027aa9106f90610ef28063be51d03bc63085f14940bea8085df40cc2fea90877d0530ef29c81ef20083b883985f94442bea8685de420c7b887986f90140bfa98437e53d02faa5a05d54420ef992617f544cafca4206f90c42be2a2217e53887b863085f942419eaa643f741906f8a9196f8cb40dea0e817d54cc2faa1217714730df190837d51c83f040086f10720dfaa621f5310c77e81106f55331de20c415c53443b8a5987710831de90a81de508c7bca9986f90841bf2a2417d50887be86195f94a30be2a021bc52502fca9995f54c41de21483dc320c7be61885f94343ee18a81bc4390bb862206f95020
  | 1 => 0xd404c37ea620efd0a42dea8e813e540c37e63a077d0c31ee98241bc21d03b8a6885f14532bfaa263dc42cc37ea8995f95320be29a21f521c42fca4186f50030bf29421dc534877864a06750c43bc28243de52cc3be8718efd0e41df28883be43d02fca620d794c209e2a2437f5050b78a7a077d4031be2a663bc41087b88218f754730f721085bf40442faa910f78c410beaa487bf50106fca3185fd4c20ee20661bc41442fca910dfd4f21df20e81dc430c7f6210877d4a31ef18e81dc418c7ee82a0df14141ef990657e52d0fb8a018d714530efa96617e5090afaa8085fd4121bea8c87dc53c42fca0105f94443dea10857e52442faa9085f54e31de28e81df434c3788720df15020ee20a617e54082faa920df54c40be29621f510043d842105f14520bda8243bf52907da4210ef15131bf29e417c504c77ea890dfd5020bfa9263dc31c43f48020774c010bea9c437e52c42baa018df94632de20c61ee320cb7e811877d0130ef288637d520c77e87a1778c710fb98c63be410c77ca9185fd4520beaa641dd40cc2faa1a1f754f21ee99063fb40502f8a9906f90710efa9a837d5210efea2995fd5331bf28e817c544c37c8318df14910ee21a617651082fea9995f54d20dfa10837d510cafaa1996f4c540bf294877e5190afca918fecc130dea1a817d5490afea4985fd4d40dfa08837d54ccafca6214f55331ef29063dd514c37e85a0770c530bfa9221dc310833c83986fccb40ee29a857e53d0afea910f755231bf290657e54cc7b86598774ca31bea8663dd30c42fca0216fd0740ef18a61bd32907bc62105fd5310fd904417e52902bea6a0df14d21df990837d5110bbca6216f15310df20a617e5210b7c82105754c42bf28665dd43ccbba64985f54231bf29041bd41502fca7105fd4540de21083dc31902faa7195f55232df19281bf544c7de43907bcc932bf288815f534877ea6a06f50940bf29483bc31502f8a6a16f54841ee29a83de31903be60187715031bf29681bc42d037ea3a07754e20ef29261be41903ba63985f54b41bea94617e5304278a898f70c521de284833d54902fca810f7d5130be2a463dd30082fca210f78c521bea9e85be548437ca2a05f94631dea04417e53087be43987bc8621bea88417d544837a81906f90940ef21c63f9300c37e81085f94041fc282437e540c6fca320df54e41df20a437e53842fea710efd4540eea1e617c54086faa521ef10610ef20261fb204827aa120f794f21df10a815d53883be8721f7cca32be2a265de530827aa81077cc631fa90843bf40103ea428877d4d42ef988637d53842faa5105f55220db28883bf40cc2bca7206f15110f790a41bc41cc3ba42986f501209faa263bc41103baa6216f94241de21885bd4350bb8a2987715231beaa065bc410c2f8a9105f950439eaa
  | 2 => 0x83b862185f14540dea84837f540c6fca0185fd4941be282857d529077842a06f50110de20c637d53882f8a990df15032dfa00217f548c7788208778c540beaa2617c5150ab8a6a15f54b10be2a621f621c437c82a06f10c41bf2a061bc31d03de84a16f10740df20861ee21486f8a790df15210ee990655e530437ca990f790f32ef29c417e53903788218d794c42eea1c633f54486fca3106fd0310bf29a21bd50106fca8217b94810bf28e41be41c87bc6390f754831bfaa661bc51502f8a6105fd5120bfaa6437d51cc3d8a4887750130eea18877f514c2fea7104f95010dea0461ed214837a65a05f95310bfa8287dd300c37aa6a05794e20fc880217d53902fca6196f15132bea9e437e54106fea6905f94f41bfaa465dd310c7b8a418f755330eea1863bd53d037883885794e10efa1c657c540c3eaa2106f95030df18e817f5150b7c86a1ef50a41bea9e837e51083d843105754e10ef90a617d53043ee6298efd0940ef18a637f5250efaa3a1df54a40bea9e41dd528c6f8a9187dc4010df20a637e544437a8720e710730ef98e61de428c73e81987715330beaa6217e53c437a80205f94b30df29a81bf32502faa120f708730df29083dd314c3bc87987750a31bf29c836d52042faa3997ec4110ee21c657e500437ca998efd0540dfa02617e50cc77e80105f54321eea1063bd32106fea4086f109409e2a221bc414c2fca6906f10420eea1a61de41cc3ba869977cc110df20a833e54c87bc63907754930bf28463dc31882fea5885f94f219faa2217e52d07ba8218df54c20df2a0217c5050efea7885f54841ef190637e5290b7e81205f95132bf298617d54cc7bca6085f15120bf28643de328c778832077d4d10beaa265dd418c7be61185f94240bfa9a85dd508c77c8721770c720ef29e83be429077c83105fd4c10dea1e85de31883ba84985714f10bea98437c5250e7ca8197715130dfa8483bc53106fca021df54341eea0a61be41c82fea6887bd0a42de20a435e518c6faa898ef48740dfa90837e5210fbaa7a0ef50210df20c437e510c3de65197b508429eaa461bf4390fbca918df14a10efa92617c53843bc64985f14121bea84657c544c7bc6310f78c932bfa94215e53103b86310df943429f288835e510c77a81985f14c21df29e817d52cc77aa5a0774c220bf29463de424c2bca3985f14d41bf29465de540c6faa818f7d4730deaa421ed520437c82907790c43dfa9e81df42cc2fca410f74c320df21883df54cc3ec8220f70c740fb10a217d5310b3862a06fc8540bea8c61dc31483be65985f55240bf28c875d538c2f8a9996f90410bea9463bd53906fca1185f55020dfa9681bc41cc778a020f70c410fb10843fa10043be61084f15310beaa243bd53107be839877885309e28a819e31503b88718df94243ef18a419
  | 3 => 0x2b80600802000100481c1f0000080040a00280262b800010362cacc00002018001080e00012020280b806058b42406a0200a0030601816000160500c04018260b20002000010000ea01804008006f96e21102018040084a000400401200800170000d0aeca800000fa3d810099203985e1581a1580e0f0360000a0d08c030000185a0b0180d8223d0161087e0384c018000281408024078e02580c000528104c2bc183104c2a02e3eb9405812000542c1c2288001b8102100a0789c0001a04808020000b82803022040003b0140181c260020083600a4e0001d6002c00016008a0008040700c06800018020900a26004001122302a020400180024870008203f996008020601a0500c03b44010100900000876000da03004ab8840101c000100881418802270a4ed8040580405800008000311002872070244804c0f80a030160192e0d01607800102ee060024a80a09058050022982a018000483800010028660000e008000100c2b80a0280007826060ff7903a128521e0060000a0201804000130020000000804178082188e000020580606008001e808ac00980009802000149901e03092008784c018000000400a0a0000c062020000000c02084258680680a108601602a23802007710a31deaa6437e51d0afea8885f94432ae29a83de31103bca3985f54740bf29863f5411067ca320fed02409f2a0817d520c37c83986f90440bfa9a83f610442fca0194f95230efa9e21dc508c6fca8194f95210df296817d51883b884985754c40ef29881df504c37c43a077cc020bf298877c54486fea8197754c20efa8463dd308437ca8195714d219ea8083dd53903b88619774cb30de21e817f540c2fca990ef14841fc106217d51842fca310ef94041de20a417c54cc3bc62186790431df98a81ee21082dca4085f54810eeaa063dc404c3de4210fdc8521bfa9a43be43502fca220e790530bea88617e54486faa9186fd01209eaa061dc324c37ca9106790631ee90e61de528c7f280205fd5021df29c837d51d0bbc81985f94732bea8063dc328c7b6a0985f54440aea8463de514c3da43907754b30bf280637c538837e87a04f95220fb18863bf4210b786520efd0c43be292617e5390b7e8620fbd4910bf29663ed200
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd525025e63150208f99050487375110520ad98740c4354510c5409e580540c71f5495231ad185525034f524c110c755231042b960d4b40c755330042b96010710c7953308c25f650c420c7950318825e63153219758e544423d64d4f218f994414872f5250110a798c52502b96008540cb548521063e64150328f185540ca9d64148318fd954310e3e6414e10d60c7504865e658c521c7952318c31d544c030ab988501071e53d00109d185544c23f6454432b3189514c35451d0530c754e419027a6094d21a718d515029e63d4a41abd89515025e63d50209e980540c63e6414a10b6580319039661106318f994544423c6454f20a759351cc25d63d48108f19151cca5f6354b408f592508c65c6548730b6580214c2ad6214f40a718d415023e6415020d614f504865e6395310e60c750502b96094d40ad987529065f63551329718d521063e6515121d594e510831c540c5109758e50c873854d41218fd95315023e64d4a109d98753082bb6048540e598441cc31e544c2208f986540cad9600c6209758f515029f6350441c7550434c23c654c940d5144414c33b5414121a7993528c72f52905108fd91510831c53905418f19531d029d6314041cd14641502d4614c3109798e548871e54cc0108fd9153442ba6014841e5144315039b6050130a798e529063d65c87408f992538865e65d053097596318825d6395310e6980414c2d9608c410971855310a9e6310841c7952310427860551219758c544825e6315220d314a314431f531071097d8153c872c5210510b6d81214c23e6195020c7952538823d6510430b6580540c72d54948109798f514829e63d47408f990504c63e64d4e10ced93504871d5494c20cd547400829d6310b40c7151304431c5390942c794740cc29e63c8740c7151434cb3960d5310c7553308c29f6550c43a7d8d425023e6494030ce907504865f6354420ad987404425d63949108f99353082ad6214c418f59252442db60545309dd85534825f63550218f593520431c4154031d518e51082b96094940c794e410823d6595010a7d9152cc25d6014d21b398b51cc23d6494321b5987528c6da6015031a758c525027a601533297d8d524429e640c8319b988540423d6494e21c7552318c29c644c832f888420c423d64943319798c505063d6510420a758f41d031d5310f409718d5190a3f65104208f592534439960105309758e500863f654c740aed81535035960d4f10c754c418823d65106308f19153482b46154d408fd91524431d5454c10c7d5231c42ae6214f408f5905348356518c630c7d5330c423e65c854097d95320ca9f6348740c7d50314425c6354742cb952520429e648c1308f994325031e540c42097d8d52c425c6354720a719131cc25e6194e20a7990324c2da6010530cd986511071e53d0030
  | 1 => 0xc31e5390440c7551308825d6094c4297d8d51d0adb60487308fd8154cc73a54500408f590504ca5e6315320ce10750486b960d4740c794c410835a31d41218f992534431d5410f30c714d40c436552c4010c7153534423e6495121c7153304439b6050330975805350a5f65508318f996414871c540c710c7153534869c644c930c7152314423d650c841cd951510825c635532097d8d521065e63d522197d9542cc29f645493097994404c25c6355120c794d408823d60d51218f593538829d63148418f596540c2d66114a318f992528c63d64141319758e50042b96014c41ae58051d0399404c320c794e41c871c5450f3097d9521cc31d53500409798c544827561d4c208f19151cc23e65d0540b3988540c65d63150209758e50d065f6355120a7592528c65e6194e40ab588509063e65c87409dd9541106b960105208f590530825d658c4409d185544831e53500208fd96418825f654c431ad986321071c5390710b6580315025d6014d41b5987540c66c6254d109798e529063c6454b308f987544ca5d6094f41d5d8d510826e62d4c108f992508c7c930480208fd9521d023e64940209d987548ca5f6354642d3d4c524425c6550a31c7552530431c53501109b99452442756114c20f10c5210865d6315021b3d89514c31e5454e10c715130c429f63507408fd91534831e5390620cdd91510829d64d4530c7152314c69c6150c438f59053087a94048020ad185404423d650ca41a799032cc31d5494e209798c525031d5390440b3988500c66d62d5231d3d48314431d54cc832c7d5353c429e640ca318fd9151cc23f6454831b658351cc2ba6008540b59873044394410c52197594430c6ae6214241a758e509065c63551109ed95100431d5454e10c7150314863d65c8540a7592508c63d64d4c108f191510829c6354841cb548525029f6350841c7d53304432c52d0110c715053486f06048710c754c53106e862440109ed81524431e548c420975835350b1c5414f10a798c42d031e54cc020c7d53534434c52cc110d6d4f504869d600c74097597300434e524ca318f992544423f6550040c7d52314425e6314c2097994424c29f6448730c7d5353486da60085308f992500ca9d608c7409dd95100423d6494a31b658052cc25f650c4409bd89544429c6354940c714e414431d5390610c754d408429960105309758c525029c6354b40cd144414835b63d41219718d54c431d540c430c7d4f40c431d53d0240a7582414c31f5410e31ce990504865f6354640c795253042d66114831cb551520423e64d4f218f594418831f5394e41d9584524425f658c6208fd95400429c6448530b6580310423e6494f10d9549100432e5454810b6d81524c2ae62d4740c754c4310b1d53d02209758e508865d63152108f59052843365110740a7d8
  | 2 => 0x6054c108f59654082d9600c710c7950318432f54149109798e50886786054d218f597400829c63547408f185548c2766115020a7d8d515023e65cc54097996404c36952c80108f99250ccab76154940d598453c425d658c420ba18121482b5618c8419798c504869d6394a419798c540c31f5390521a718d41d029d6010530c7550318435451c85308f993514cb1e5494f21d694d300c33864d4121a798f411063e6414e20c7145404c23f6548540ae980531063d60953319718553882cd6215031d5944310c2bb6048740d3548520c65e63948218fd94410c3a441484218f592500829e6314041e5104318871c5310510a7590500c756510c4208f19532d025c6354910c5144315031e53d00208f992544ca3f6454630a7582410c71d5390410a718d215023e6494331a7984410c65e6394041c7944410c71c5390521c7951308429d6090730d554e510826d62d50109719542cc29e64d47308f195329065e63d5321a718d425025f63551218f59731d029e618c54097d96310823d6095321c7551308423e6494221a7582418c63e641481097d95414c25c6354440a719121cc29f6354841cd94540082d96095130a7d8d52d029f644c43197195434c23f6590430c7152314865f650c41097597410c63d6494d219718d51d032d5214b40c7d52314871c5190530b5586420c63d650cb40cd191510825e63d4542e5144414c29e63d454097d8d51c825e63940208f580544cb56535442097583535071d53106409719541cc25e65cc530a719151cc34d520cb30c5144414c31d540c420c754c418423f6510410cd552510829d63d4740d5d44315032d52108419bd89534429e6494231a7592404c31e5350040e5984315029c6454b30d5945300823d64d4530c754d400826e62d5010c7553300c39b5050130d3d4b304431d54153309758e509069c6350a419b988540c6d9608c710ab189515031d548c430cd946410831e548c6209758c5488338541412197594424c23f64547329758f548429f6350b4097594319029f644c53097d8153d065d65d05308f99432d031d540c620bc58420c42ce62142319d587540825d65d0c32b5987520c71d5390420aed81525034f53d49109798f528439a600c5409758c520432f5210510d3d4a31442b46150310a7993514c31d5454c20b598730c429c644c831c7953308831d544c0208f996414439a41d41309798e524429e63c8540e6501300831d5410c319798f548825f6054c428f986540c25d63153209718d52c425e6394d10e68c7505025d63d45429b58a53443965190431ae580414c23e61151328f9974044397510c540a7992528c65f658c4408f994414c65e63150108f19153c429e6110530a7d9151cc2d960d53309798e500869c6350441a7590508c66e6214c10cd944411035763944208f597400
  | 3 => 0x842b5984540c63f6055321c794f408836551c8020c754f401026d6214c109798f540c356518c420c714c414869c6350841a758f215031f548c5318fd91518833651104208f593528423d6414f208f185548835651cc020a758f415023d6590410b5185524c25e6394342ced53504871f535011097994534863e6494821c794d400c25d6394a419e596100434d5394810a7984315025e650c510a7d814310f1d53104208f195215032d5290410c754e4310a9f644c730d3549300431e5350210d5144214c29e64149308f99250c863f6454c21979875350b1c5450f32d658053c429f644c8319ed95200825e6114d42e658031502b86048540c7553300823c65501108f596418829d63d4a41a758e501065d6395221a798f419065f650c620b6580314829d6490c43c7553430cab661d4e419718d544863f65508428f191520c65d6594c10e5944410c76a2114121a798e509071d53d08428f992508cb34510c540d60c4504871d548c420c794e418431c5350d42c754e41c865d650c420a7d91324c2d86048530a758c52d03585314121c714f404429d6494031c794e410c3365190640d594431cc36551480209718553902776155120e6107504c31e5310440c7d4e414425c635444297185531029c644ca318f992500425e63141428f19532106cd62d5231c7946410c66d62d4c109e58253486d960945308f19153486da6014831ad987521063c6454620ae582410425d650c4108f191530863d6494010d3948310431d53d0210c7553308825f6355110a6580315025c6548530c7552318823e641413297d94319029c644cb30cd144414c32c5414910aed8151502d96014831c758c544ca3d60950328f191510ca5f6355310c794c41c86cd6214031d698c504866d6295110cd98754c432e5250010c794431d02cc62551309759721cc33a41141218fd81540ca3f65500308f992534871e540c7219bd95320ca5c6114d109e58254487e121c831097594430ca3f65106309798e50d072f5294a41c7951538825e6394d2197d95214c29f63485408f59053042cd62d473097d95410c74f5294a31a798e405031c53107109d9845204354518c5309758e50d0a5d63951218f993514c2796014c218f986548c3566194431b6582524c27a60951218f581540436852c4110a798e501063f654c841a7580410c63d65cc5409758c504874e524c010c7550544c25d650c4409758e501071e53106208f994544c69c6454831ba18121c829e61d013097195420c6ad62d4e41cbd4b404423d65904308fd96418c25f63547409758f540831c54cc3109798f51502b66114e41c754c535031d5350010d354852cc31d5310440cb94a410423e611511097596530826c6255110cb54842d029e64c8530c715231c431e5390640ab988531063d65906308f994414425d
  | 4 => 0x5986420c6cf6255130b618121cc23d6494f108fd9152c431d53502209758e52c425e63d4810a7d91328c6b960d4f40b6983424c23d64d45208f195315025e63152108fd9541106b96014b40ad984529063f65904209798f548423f6454f20cbd53524423c64546309dd95310c71d5410c32e5d44414c31f53907109798c54086ad62d4740abd89535027765484219758c54c863d6414e10d394a310425d63d52208f19152c423c6155030c7950311031c548c932a718d21d025d63d5321a718d42d025e6114d10c7d954310e5e6194c4297d8d511025c6354420c7d5130c429d640c8318fd95329069d6314241cd947400829e64140319d1855348396610c7409b596520431e540c43097994428c6796015021a798c509065d65c85309758f514831e5350010c7551538825e65c8730c795231c874e52cc010ce590504871d53d0020d5544310825d63d522197594428c63e6494031cb94841042b9600c5408f19151c82d960d09309b98854cc31e5454f21d9546210831d53906208fd9532d025e6394241ae582515035661d4f109758e544c65d6394821c754c53d029e61d0330a759052cc23d6494c319759741cc31d540c721c794631d025f6054c10ae580418834d53548108f99053c869e64cc431c794c419025e6514d1097195424c29d608c5409798e5010b1d544c832a7990404c27561d5232e650130843355150020d554d510823c6115110a7d8d51d023e64d4c10a7185404c29d640c9309798e500425f658c640add85535029d631094097596319025f6550730c794540cc31e51907309758f528425e6590d32d618f504863c61550208fd94418829d601073097d954310f355454420c715353c425e6394321cd147215039b50d01308f597400429d6010631b5984548c71f5414f10d3548320c6b661d4c41c714f4350b596314121c754c410425e6394242ae98332502b661148419bd9521086cd62142318f994544ca3d64141219718d518831e54cc210c7152434ca7b6054d219ed95401031e41542318f99731d025f654c010c7550540c69d64c8530d314c524426c6255130b5d85544c355514c020a7993314c29e61905309e594200423c6454632c7952530823d64d4c20cdd92510831e548c610cd546410829c6350842d6d4c504869d6310a41c7552318425e65c85309bd95200831e53904109ed81544871e5494e108f580544c69d64cc5309799431486766114c208f994321071c5110530c7951300c31d54cc210d3548310431d5494f21a7986410c69e64940318f592500c69e6314b40a7593310c67a6014c218fd95325026e65c85209798c520431c53d0310c7552538432c5250940a798f415032d5250010a758f419063e61952208f992500866d6588420ab98b53906b960cc9408f59252c426e62148108f593538431d5350
  | 5 => 0x314829d640ca31c794f401031e540c630c7d51304423d6414810c794f408423c6454d10a759321cc34e53548108f99252c431f540c521d3149324c23f6454b30c7550310431e5454c109798c528425e65d0730a718540cc2ac6254d4097d95424c25f658c410e5104318425c6354b40ce10450486db6055130a799052cc31d5454f21c7d50534871e5450e319758e5090a5c65505309758c528431c518c54097d8d54c831c41542318f994329065d658c430c794c41042d96014730d5547300823d6494032c755231c87346494420c794441cc25d650c6209718d519023d649403097195304429e64cc730c754c4310735511042097994420c6b860487409ed95300c355518c420cdd44414c29e64cc63197996314425d63d501097997434c26e6295110c7150534425c6355021e5984410c6d960105308f594325025e63d50108f590538826f6550842a7593528c73451cc540a7990520c63f6590410b658352cc2ce62d52319b98a534431e54cc030c7551300425d65cc020cb949429069f6448530b5d85524c31e548c4309b588540425d6394020a7590524c29d64cc730d3148314423e64951319d584540826f62551308f990540c31c510c540c7d50438cb1e5310610c7151430c71d43944439758253c871d4354043a798c521063e64d4e20a7d8d415032e52d00109798653083396015310c7950310429c645493097596430c63f64547208fd91518cad960153309b58854cc37060544209759442cc23c654874097594420c74d52149308f592508ca5f654c0208fd9153c423f6454430cd144215031d540c63097583534869f64548318f596540ca3f6550020c794f409029e6310940e5984414c23d6494221c7d4e415072c5250110ae58241c423d60d5132c750d5210f94410c410d354b300431f53503108fd81540429d63d044197185530834d528c410b5987548c72d521041097d95428c63e65d0d428f191510c34e5394810ae980315025e63951218f990530423e64d48108f580544869d648c130cb153524431c63550328f993514831e544c010c7d50534423e6414930c754c41c871f5310510ae580410429d64cc6318f5964310ace621533097997304423d6510410d3149304425f63544428f596411031d53d00108f99053c831e5310430ba181210863e6414c2097d8d5188399404c1109758c505065c6550d328f59353886776155130a7580315029e64142319798c53043366115310a7191514c23c6454910a7d9132cc25e63951108f592520871f540c7109d195214429c644c5308f992530c63d65904208f992524431c51d0130ae580521072c5290510a7191310c69c6250c43da181520425d658c410a799321cc29d6390140a798c429063e6590531c7905500c63d6414f21ad984531076452885109b98b548c75a3114121b
  | 6 => 0xf43180d0000080780004e00000002042638050e3000000a404701a0000000c01c0042a81009e710023270020880002000e082608000221180701b1e8000002730020002280304a0181280103801001807074810020190000341482f07400400008578000410110020004a1fb0063f992000014020018760000300100800c0340082b002064180089e447008001014f401a00315c9900a8050280880280e002010008060000140100104e01c2800000026800022050000000140000100601e29c0040002804c0080280100e0202880400e0950081b0120000600301a0081304e0160701304f63c084b60110020c00000607c018000080480057b1180020100002e0020588402c1d4010001cd002000140000007600083b0240940002101e0003400f002004138007d60cc00824018014069590160102d0480060100100a0001ec1000101e0400200f0220080a8001da02c128100460d40d8510c61380281a008284000002c04b13000304e0100106d0044380100e00a05c0484a02e0500700d0073250f0082aa0200100500c0e41304e1480080a02e02012c000000000a0048040020ac0580b0040000400d0880240480a0400100602c0760040bbe60000001580001805007800002028010130160300000005a05c04804000004088d300008c0106300206000013008004040110040400d004002d0021800004088260040300000000c0000000101700201000008028008068691bc00429806000068000010025a48e00b0520300280c0920280a80408c0000b0000342b8008231580080192d008048028450000811c357008004000040c40040201c00c00401334012028098178f64dca080105e03c0180602403419800026004428090000202f0080040107f0070020001f81f00000813820006028238010ce00c0a0000940080000102c00829800006020018180200965e6510b308f990530873654944208f593514ca3d60d5131a798f41d029d63d4540ab588501069d640cb309798e52c432d52d00109758e5010a5d631501097d8d544c6cd62153308f990534823d64940219b98a524429d63c8740d514431482d461551309e58054cca7661d50208f590524c31e5350e41ae580418c34c53d49108f59250cca7a6015021c714d43503546354420a7d91514c2d4614c110c7151434c25d6314142a758c421063f6454d21d9544210823e641501097d95300c31e544c0209798c540cb1f5310521ae58053d031e5454c208f993538871f53d0110a7d8d429065e6194c409b588540c71e548c440d5d44
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1c61540003404045000800004000100604284000000702000050ebc0010002c0100041000008034002c1040218000082000000140000400682141c00104081810000291c18c72928520e10515803150287396a729c83925496014831c1ac6a90a5a060d635485210706324a499463461d5404c110c1aa8b10a99851970105500c68b38ea821c65435c85450f30b22e0208620850e72d52548c6a238aa429261a81046048421c28c228a809845471594424c314a92c0290830d1c5650c940a18e4aa0a89869061501304430b318a390a81265c264c8530ca0a2b008298439701953210686392a629a81835915214831e82a2982401050e72d50438c706320a49926183591520cb30c1ac8a906418e1051580414c28cb80a8a186385594410c4108b2e032a8418d147150e5110f12290c2a0221431c95410d3092ce3b22a418c997098c525030a298c2a0621439d35294a31c32a6b00831071051980414c31828ac018a81431cd5214940c28a2b0062a060d6354842106c838a8098221c1548410c410a28e2a98832061865501304434828ac018a81c4146600c540a28e2aa0631063051580414c34820ac01882185150614c110e42a2a02401051575104310428739ea5294838654d6014c41a36e0a1aa021e1664147214c30c28ac018a8186d4d6010710a1ae42a28618e19535804104306b22a4296618a5496010410c1aa6b10a620e935158031503882086228243c2149404c110932e131e42a061451580414c24cb84c9a8a618514c6150110c28a830a618849671d8d5210706aa2c42a06392549600c4109c2ed1084188644521853044306318a4a128186551600c410a28e2aa0a89861954580540c749a8ac020a61431d15214930e22a2a02601049970990524c29238aa4292818354d6214f40d80623024210f1051580315028a38aa629a81265c263d4540c1ac6a9085a061b5458031c430caa2c018c41861456010530ca0a2b0062a05197015143cca8a38aa818c61c41456010530a28e2a98831069051580414c20e3b2a899065451c55410d30
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x608000100030e0152105600c410a118098c51c8540a108154d6010620c11655c0410c410a1185105600c410d01525c0410c410e0052185404c110a1081551600c620a118099051c8530d00521c5404c110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => 2*((h/30+packedAt s4K6 (768+(h % 30)*6) 6) % 48)
  | 5 => 2*((h/367+packedAt s4K5 (27459+(h % 367)*10) 10) % 1017)
  | 4 => 2*((h/497+packedAt s4K4 (51110+(h % 497)*11) 11) % 1345)
  | 3 => 2*((h/79+packedAt s4K3 (5488+(h % 79)*7) 7) % 112)
  | 2 => 2*((h/17+packedAt s4K2 (600+(h % 17)*4) 4) % 10)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffff83fffffff03ff0787ffc3fffffdc0f1ff
  | 1 => 0xe07fffc0fff83ffc1ffff83ffc1fc0fe7f3e73
  | 2 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x208888820922100a541026481325450c050a5
  | 1 => 0x491411064920402c0a0a8809440482a81b2652
  | 2 => 0x852522121a4406554084d4826a412a0b058b18
  | 3 => 0xd659c4a49076ab9a73d04623b3980c33e80de0
  | 5 => 0x18618738e38733e39ce76730231030c3f6f000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38875
namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
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
end PEqualNP.Outside.L_meta_38875
namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x100241800e00000000408300102000204000000000a160000004200b6040000000040850e1000504680001200000063408200ff0c0077c51007f8c807fe53007fcc407ff5201ff14c03fd10017f50c05ff4300ffd0001fe3100ff08007fd5200ff50001fd21017f90803ff5000ff48001fc3201ff54c01ff3201ff94403fc40017f95003fe10017f50805fc4300ff88003fd50007fc8405fc42005f94403fe4001ff14403fe50017f50403df30017f55003ff30007f4c4037f50017fd0407ff5100df54003dd30007f4c805fc41017fd0807fc52017f90c03fd30007f88403ff20017fd5003fc1000ffc4007fd51017f90405fc5401ff94803fc5001ffd4c01fc3100ff8c001fc21
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x864200ff4ca31027fc831882bff32cc42dbea84622cff54b320dffaa31881bfd60c840d7e32c6406ff880210a7f8a818857fd520c40dee9906403bf99431057faa61881aff60c844bffa126406ff18f2101dfccb1880afc644c417ff1024200ff58e210bff8c09882bfe620c4557eb066416ffd42310bffe80988837f41944277eb006200df4ca51037fa4190806fe6008411fe298420aff9903108ffa879081bfe208c84fee9846404ffd8e21077fea91084ffe200c43b7eb26622aff8833207dfacb1089aff654c815ff3266214ff50431005fec71083bfe4388431feb22620affcc231037fc8510813ff108841bfe29a4216ff48231037fac01081bfc658c819fea0a4206ff5803210ffea019003de314c42f7eb026220df10e5105fde409081bfd6308401ffb126229ff54e32015fcc9990437d50c840ffea08420cff50d21037fcc01902bfc538c80ffea184204ff9463100dfcc19085ffc404c435efa1c620aff14f320fefa412882bfc530c439fe2066207ff5502100dfcc0908a2fd648c8013eb286417bfd8131057ea6218833fd5448421ff986420aff99731127fa40990a3fd418c801ef98c6224ff8c132087f8219082aff60cc451fea1c6416ff9423101dfccb9087f7f3094431ffa126206bf98621027f8831081bfc528c815fea186209ff4c22115ffa839909bff524c809be288420aff9833104ffa2110813fc108c449ff3026407ff150210c7fec898806fc600c815fea1e6406ffc8321126faa0990377c5148443ff0806414ff5503102ffc8010817fd5008431ff2a2620fffd462101df8cb1082bfe530c809be2886212ff14f2115ffaa999033fc5448417fea82420aff8c032037f8a410827fc508840d7f3106428ff15232005fcc319027f71088415fe3266224f7cc132037f8a49082bff530c8177eb144201bf1803105ffc80908027d65cc421f69064218ff509310befea098877ff42cc44ffea84640bff5812109ffaa018877fe54cc423ffa1e4211ff90721026f82128877fd42cc42bfe2906206ff14b32057fac418817dd3008455fea86642aff903320b7fac11882bdf300c827ff2006206ff94832005f8c29902afe618c415fe21a6400ff58a3105ffa8090827f51088409be324a20aff0c331015fcc89089bff534c815ff98c6217ff98131127fc209901bfe524c801ff10a420bf74c121147f8831902bfe534c801fe98e4206ff10a2102ffa801082bfd62cc42dff904620fff596210d7fe8718823fd530840dfe9906404ff14621057f8609882bff64cc427ee9806222ffd0432027fc421088ffd510c801ffb0a6410ff9432100df8c09881aff6308439bfa866200ffcc72100df8c09900efc654c8057f3264206ff54b21037facb9085aff608c441bfa1ca200ff8c5310ddfecb1881bfe3288401beb14a204df90651
  | 1 => 0x3fc650840dffb2c6420dfd0a510b7f84118893ff404c801deb246213ffd4031027fca21089bff654c833fe32a620bff481210c7fea898877ff54cc41dff3244206ff48232015f8c89902bfc430c401bf31ca20fff14e21037fec79082bfc43cc80dfe3264200f70ca3101cfccb90827fe608843bfe20e622adf54332035fec81902bfe434c43fbe104a21aef9923106ffca290863fc424c40d7e312620eff506210e7fa219884ffd200c419ffb224205df540210c7fc849881bee320c829efa18622aff48332037fea590877fe42cc4137fb04421bff59631167fca399092fd604c817bea8242039f986510c7f8c89885fff604c401ee988620eff50e2105ffe609081bfd650c80dff3046401bf18321127fec099013fc1008409fe3004205ffcc02101df8ca9886fff528c401fe31a4227df54232057fa6198837fd654842dff184620af7cc431117fca819002fd620c415ff9866413df54031137fcca9901bfe610c815feb26620affcc232037fec99085ffd304c44ffe0846416ff84231147fe8719013fc6308409ffb04420eff55221135faca99063fc414c40dfea1064039f1953208dfac99082ffc10484357fb24620affcc03110efea019027fd5088409fe3106212ff94f21007fc649881bfd528c825fea8e420afbcc932087fc21908027f654c81d7eb24420bbf581210cffea29885ffc504c415feb2e621cff14331026f8a3108a3fd548c835ee21c621effd4731027f8201882b7d65cc40dfeb1e4209f74c221057facb9901bfc5288401fe98a420dff995210bffac09883bfc5488455fe0866419bfd9531087fc619082bff60cc425ffa9e4206ff5823205fda4090813fc658c449fe302640aff0c032027fec81882bfe32cc441bf324a209bf98421037f86590827fe4088409ff2084225ff95132057fa621883bfd648843fbf184a225ff50932057fca71882aff64cc80fffa18420cffd0d2113dfac119097ff644c80d7f310620bff9412106ffaa49086fff538c40dff9046406ffc8021067fc82908a3fe418c801feb1a4213ffc8031057f8651881aff64084055f3204206ff94b21026f8c52881bff2048421ef98642039f997310eff88598803fd31084017eb1c4206ef592320f7f8a39881bff420c84fff284640affd0c3101dfcca19013fe410c401ff9884206ff0803202ffca01082bfe60cc815fe1826400ffcc521006f8652880e7c6548415ffa1e6406df597210b7be6118833fd6448437ff2946223ff94432037faa410847ff41c8457ff20e6424dfd41320e7fe819881bfd32c8413fea044206ffc8332057fe60190137c609440dfeb284211ff10f210febe612881bfc204c835ff324621affd0631037fec21904ffe500c425ff28e420affcc4310157cc91902bff324c415fe21c622aff9433207ffaa7108137f6094421ffa
  | 2 => 0x32057f8c199006fc600842dff3046200ff185320cef8a29887f7f409440df79084206ffd482112ffea89902bfd300c815fe29e620dbf5952106ffea49081bdf320c8597eb2e6400ff189310c7faa89881bff618c815fe29a620afd8c4310c7fa8698843fc40c840d7e3184217ff90131027fca3108a7ff538c839ff886620aff90d32015fcc89901bfe64c8415fe2186406ff90932117f8821902bf7314c4157fb2e6220df50a51037fec11905bfc408c413bea84421dff507310d7fca918863fd414c443fe280640abfd903111ff8a219013ff658c42bffa906206df59432005fac219002fd628c40dfea164224ff1013201dfcca9081bfe640c80dff32c6404ff18231026f8c72881bfc65c8459ffa966416dfd4231027feca10813ff600c413ff9844206ff586320effaa99882bfe65cc849fe2826406ff180320fef881288027f654c44fff184640aff8c031037f8c919097fc414c849fe9826404dfd8e51007fcc299006fe60cc83dfe2966206ff98f2108ffca99082ffe1048409bfb14a204ff04221055fcc61881bff42c8441beb24a206ff0c921027f8ca1889ffe108c80bff0804206ff0c821027f8c81080e7e650c831fe2a26208ff94c21057b8861881bfc420c82ffea826205ff8c02106ffca69089bff514c833fe292621dff153310e7faa19882bfe43cc411ffa98421aff50a3113fbe611902ffe3048415ff29e64039f19531005fac69085efd638c40dffb2e4202bf99131065fac890873fe40cc40d7f316620af7cc03106ffea69082bff53cc81bffb2a422aff8433209ffc2018873dd30cc4337eb2a6210ff0c3210bffa209882bfd61cc815ff2986206bf19432057f8641882bff530c421bfa864206ff8c83205fbe6090867ff654c44b7eb226401bf98221045faca1087f7c309440bef9804200ff4c921037fca410813fe418842bff2906200f718d210bfba609880afc6488401bf28e4209ff94221037fca49089bfc514c801ff18e420aff0c231015fcc918872fd60cc40dff9044204df94631077fe871081bfc424c8057f3206200ff98d21007fe631081bfe528c843ffa006404ff19231037fea419003fd3188411fea884207ffd04210d7fe851881bfd320842ffea02620dff545210e7fa819883ffd5288417ffa82420cffd05210cffaa69882bdf30cc817ffb02421abf59231037fca59901bfd20084257eb2e4202bf99221037fcc61087f7e109440dff324640adf99731027f8c91082bfc438c80bffa804229ff54632147fe831902bff61cc80dff192640aff54f31037f8419082bff65cc829ffa086207ff10c21057fa641882bff324c813ff104420cff10d210affaa21881bfd6408401ff314622bffd073210ff88019016fd6008409ff288622affd4332005fac61085fff104c459fea8e6406ffd9432037facb1901
  | 3 => 0xe2046404ffd802105ff8809080efe658c845fe2a0640aff8c332157ba6199043fd10c8409bf884a20affcc331007bc651881aff648c843fea80640aff59031087fa619081afc6408441bf21ca20fffd4a21005fac31901bff640c82dfe8846201bf18332057f86119047fc41c8425ffa8e4204ffd9431006feca9082bfe61cc827fe2006206bfd9421005fac79082ffc6048421fe286420cff19121057fe6098813fc418c42dfe984622aff10332037f8a419013ff628c41b7fb2a4225ff1913212ffa869909bfd654c849fe882641fdf4425110ffc8019087dd300c80d7fb2c6406bf98a32006fac72881bfd4208415f79946402bf99232067fca890833fd424840fff2a04206ff997210bff82098897fd544c82dfe284620affcca310a7fca818873fc10cc43fbe984a206ffc85210dffea318877fe41cc413ff1844224ff901320d7f8851888bff540c8013eb2e4203bf19631057fecb9881bfc42c8429ffa106224ff5413215ffa859909f7f508c8016e31a4204df10651035f8c91909b7c514c80dff3064206ff50a3212ff8a89903ffe5388401bfb2a6400f94842105ff86090863fe644c40dff3204214ff50831055fcc690863ff434c409bfb24a22bff95332127fac099003ff6348409bf30ca206ffc8421097f8a39081bde324c80dfe2926405ff0c02109efea0188177f500841fffa9c4221ff50032006fcc528892fd638c80dfe194420aff19732057fcc01881bff32c8417bfa824217ffc8131027fec11882bfc64cc80dffa146417ff941310cef8ca988037e5148409ff1884204ff14631055fcc61081bff4208401fe18e4218ff9053104ffa4110803fe3148409bf2884224ff5013203dfac81081bfe32c840d7e31e420aff0c031057fe8798842fd60c8439ff9066200ff5893105dfec090827df308840dff3286406ff94a21027f8c818833ff4248415fe1866429bf59632057faca188837c4294455bfa866406bf19421055fecb9909b7c654c815ff98a6219ff54931127ba6099003fe328c433feb2a6206ffd92320e7fca19887e7d60944015eb24640effd06210f7faa598813fe310c415ff3166204df94431037f8401082bfc61cc801fe9944221ff44032057fac99903ffd5188415ff29c6410ffd0321037fc841901bfc208c843ff8806406ff08121057fa8798806fe608c80dff3284200df8ca51065fec89081bff528c815ff2186406bf19032137faa69901bff320c809ffb10620aff5833114ffca31902afc6348413ffa84420af70c83114ef8a31901aff600c847ffa886400dfcca51027f8c51881bf7214842dffa04620eff10e2109ff8401885ffe204c44fffa846416bf58231037f8c11909bfc654c839ff106621edf14731127fe209909ffe408c80dfe106641fdf9825101eecc328867fc514c4157f3186422bf590
  | 4 => 0x3de320c435fea1c620aff94f31055f8c998817fc5008409fe208421aff55231027fecb108137c518c415feb066408ffd44210377cc91909ffd308c819fe20a4212df1472100dfcc01884ffd100c415ff328620aff4c031057fa6199096ff644c81bffa8a4218bfd9131106fa872885ffe104c441bea0ca20aff0c931037fac919002ff6348413feb04421aff15231057fe609901aff65c8417fb882420abf19332015fcc8108abfd10cc853ffa8c642aff14332037f8a59089ffc508c857fe20e640bff98121037f8c19083bfe5488421ff2064213ff140310affea21880efe654c83fbeb04a200bf58b31037fac219093fc104c8477eb28640abfd9331057fcc99902bfe534c459ffa8e6416ff54231037f8859903bfd4288415fe196620aff8c331037fe401908bfe410c837fe2946206df994320b5fcc21881bfd64c8409fe2884216ff902310e7fc219885ffe304c40dfe210420affd0c32055f8cb9880afc648c43d7eb2e6219ffd4d31027f8a218802fe610c80dfe2124206ff19432007f86290837fc514843bffa0e6204ffd9231055f8c710856fd650c40dfe908420affd4f3100dfcc09882bfc530c825fea9e421fdf5025115dfac999043dd30c843fbf204a210ff50321037f8851902ff5104840dff90c4225ffd0d3214ff8a319027fc3088429fe2106218ffd0531037fc64108277f508840dfea906406bfd8232035fcc518867fe524c40dff1924217f7cc13100dfcc198813fc3108437fea9c6225ff905320f7fca59885bdd308c441bf214a20af7cc331037fe641082fff4048433fea8a6216ff50231027fc631081bff204c819ff3224203bf99421057fe6418803ff32484077f32c420aff4cb31057fec59885ffd204c40d7e3264206ff98632057fc641887bfd51cc41dffa14421bbf59631037fc401907f5d309444bfea0a6400ff58532007fa64988137e5188449ff1026406ffcca32035fec790897fe644c80bffa004204ffd8c21057fac01882aff600c439bea866202af9923112ffac899013fc638840dff216422bff1533207ffccb1082bfd53cc857ffa166427ffd02320bffea098847ff54c8427ffa006226ff54932037f84110843ff10c8409fe300621cffd4331147fca91901bfc618c815fe21e620aff10d3101dfcca9886bff548c4037f302640aff14d3210dfac019002bd648c437ff32c6206fd4842108ffc87908b3fc51cc859be28e640aff18b31055fec19900efe65cc801f6908422affd0332005fac39901bf7218842fbea826222ff50432006feca98813ff108c415ffb066400f7d8d210e7fa4198837fc654840bfe2004223df1443200dfcc01901bff60c8413ff0844206bfd9321057fc871886bfe428c40ddeb204200bfd8532055f8ca18803ef21884037e3046419ff94531117faa81907bfe51cc44ff
  | 5 => 0x4400800000000003d700400003800008038018000c40002801d1260847f8020000781e81707000c0000000200801018006018000000181a80000a00e0000105b00203c0483510e0140800001c11c0000f2382446417f0000100c80c6f262c00800024000138070220002e8020000080f8060060301b8030a696c0000003400c010070000100e001084000088040040d40102801800c1d80004400001000000020158040000e80100303c054000020000e86580200a1b0000150840100306501e0000980201c008108160040000800302a00c0000000006c11824040100008a70e00082880101800c0680200c0202f0110040001380300c000398060120440900004a084020390002241d37904a500010050460cc1c0a70780040282490c04c000010b00080104600c0000080a00a004008dd000074000370c80344e00600009c000700000000001b0aa020028040000a4018060003ac02034070054000b30060440c0050000380681807e4b80f80002a0001301f036080ac8070321944580501c0280000b0440a07e8050080601f01a0260000600d028104038000580040000201cd480087b00400002806030000000030160e42b8020323c0a580301400c828000044381a11f0180000600000802c0983d0bc08c250b90265a8157f31c4206ff88321157fa819901aff650c84ffea04640dff54d210377cc81080afe64cc41d7fb244207ffd502109ffa8018813ff6488437fea946214ff90831027f8631087f7f2094413fe2044200bfd893104ffe8110847fd54c844dfea8a6417ff081310e7f84198803ff3288401bf28e620affd9332027fec810802df63484497fb026401bf98231006fca29881bfd200c809fe32c4206bf1972106ef8ca9081bff600c8317eb226201bf1822112ffe829901bdf328c815fe32e6214bf590310a7fea81889fff108c809ff8804203bf99731067fea890806fc60484015eb20420abfd943101df8ca9083eff658840dfe3206428ffd523203ffc861082fff104840df79064206bfd80210b7fc4118887fc100c819ff21a421aff59231127fea099006fc60cc401ff31c4206ff90821055f8c818813fc410c40dfb108420aff50c3210efaa01902bfc538c40dff2146406ff9092100df8c1188afff54cc817fe9824200bf98732057fc879900afc644840dff300420aff90c31057fc8719013ff100c43f3fb04a200ff9893104dfac11082bfd530c83fbf104a206ff59032157fe2199047fd41c840d7f31042009fd952102ffa2010843fd50c8423fe2a64202bf9903213ffa2119013fc6088415f69906406ff1843205ffa209081bfe42cc815fb98c620aff1833102ffa601082ffc5048433ffa92620abf98f21036fccb90803ee2148433ff32a620abf19732137fca29907bff52cc435fea0c6224ff9413210ffca019
  | 6 => 0x580a038000010010081742f8000320080005617609801800048000110030521a00400004400405806000268058000440a4018000200580100900e1300000002800c000ea0cc0240581601a0041e001008004050cd01e114708040000684200d0c43d40801d016060018ef01a0003601903c0040028700a0d9338450000000500004a9cc098b20120480680105a0202401a0061fc0b0000004a823800014000090020120
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7598a31056de7218d21036bf20590210067c51587320067d5058732056de7018d2100cfe7058b3116f6f50484210067e70597210067d74594321eedc21d8d2100cfc70d853216fe55048421005f571cc9210047f7059721006dc6018d21056df3098732014fc74d85321cd7e728ca5135e7c20d95321eede52d8d211bf6d20945210067e70d9531007cc63885210067d63945210047f75584320067f65d8532014fe7458b31006ed5258831036bd52592321057e7498a51004ff7458a3101cfe7558d21004ff764c4210067c6558d210267e6198e511e79e748c831036bf725902101c7c7558432056dd7018d2116fe65048421026ef6298a31014fc74d8931056dc63cc921006df3058c21007cf20d8d210079f30592312075d30947210067d10d952136ebf30592320ce7c71d9531056dd76cc6313676c32d95321ce7c42d95210067f6558532004ff70d89310067d7259731004fd70587320067c60d95310067d40594320067f705973100cfe7058a310967e71597210267c5198632006dd305883101c7c755863200cfe7058d211cf3d748ca51004ff74586320267f6298a510067c7159432036bd2159021034fc72586322475c518c8311367c654c931027e460484210367d20594321ce7f60947210057d7498a51036be72590210067e74d9532006bd53592320069f3059232187e45348421004ff70588311f7cf30c86211d67c73d95311eddc748ca310267f6398e510367e3259432054ff764c721007cd628ca310067f5058f211d57c7358a5101cfc75d8d2101cfe759873201cfe75d85320267f6098a513667e43d9532006be7559232006dd60d8d21006f610185320367c7259721005ed72cc52135e7e72d9532036bc20590211367e614ca510047d70d95320067e40d95320367f3259432005ef724c521036be20592320067f73d9531056de634c721006dc10d8d21024ff749843216fe670484210957e75cc721026df60cc63100cfe70d8d210267f61945310065d30d95321eede32d8e211cf6e620ca510067e64d952119f6f5088521006bf10592320067f7558d21004fd7598632014fe74d8532004ff70d85320067d5058831027e76548421007d510d8d21027767194521006df638852117fe654484210f67c65cc5210067f50d853216fe750484210057f7058e51006f541185320067d60d953100cfc70d8931056dd7218d21006dd10d8d2101c7c7558c2101cfe7558f210067d42d9521006bc5059231004fd75d8d210057d70d95320567c7359432006dc6418d210257c76cca511eedc628c5310257e71947210257d7698a510067e10597310057d710ca51004ff7558c21027e641484211eedc42d8d210967f715972101cfc7558b311ef9e748ca310065d30d9521197e57548421004ff755843201cfe7558c211057e744ca51
  | 1 => 0x8632026be31590210277671945313057d740ca5124edd608c531027e464484211d67c43d9531006df10d8d210067c40d95310067e64d95311b77451cc52135e7f20d95320ce7e71d9531006bd65592310067c764ca51056de618ca310267d76947212667f60945310057d7598d21027e431484210067c71d9532006df70d8d212ee7f600ca512a75e510ca31034fe72986320067e40d95310367c3259721006df60d8d21006df30d8d210067e4059721006bd50590210267f6098e51004ff75587320067c4159731004fd70185320275c6398e511ce7c72d952106d7e76d9521034fe72d8d2101cfe7598632006de75d8d210367d32597211ce7c21d95210067c74d95320247c71d9521007e473484210567e43597310067d4059731006bf52592310f47e76945310257c7158e511ce7f649472116f6d504842101c7e75d85321f6ed60c86210067c64d95310257c71d95210067c5158432014fe74984320257e71947310067e41d953201c7e76d9521006df6398d210067c40597210076f20d9521007e53148421026bc6259231006dd2018d21007cc7348421054df7018d2135e7f73d95320067d2059731006be5059021005df7018d210067d4159721006df65d8d211d57c74cca510067f42d9532006bc53590210057d75d85322cebe73592310367f2159432036f72158632004df764c431036f721984320567e32597311d57e7398a51027d651cc631006bd2059231014fe7458c210267451986320067f43d95310267e6158a511eede42d8d21006df3058e210067f64d95310267f6458e510fd7e7058e510075d30d95320367f72594320067e30d95310067e3059721005bd74989310d6bf76592310067f40d95320257e768ca510057f754c921006df5218d210275e3198e5116f6750484211efd421d8d2106d7e7598d21006dd5358c211e5dc724c43119fcd3088521006bc50592320276f6298a51006ed6218931006bd648ca31024fc7158e210047f7558c21004fd70584320567f32597310067d41d95310067f654c931056f731584320057d7098e51006dd634c721006be1059232006dc4118d210067f4359721146be648ca310067d70597210067d5058f2130e7f604ca510567e43594320067f5058a310057f714ca511053e748ca51027e631484212fe7e610ca51006dd4018d21006bf5059021006bd70592311e5dc748c8310067d60d95210067c10d95210267e75d8e211d67c6494731006df53d8d210047f7558d210077510d95210067e74d95210067e75d85320057f7558d211d76d320ca512cebf32592311eede618c8311cd7d7694721004ff7458d21034fd7258c21014be7498732006be75592310067f658852100cfc7098732006f541d85320075d3098a51004fd7558a3119f6d50885211d57f74cca510257f7258a510dd7
  | 2 => 0x57f754ca310067f65589310067f70d95310057d7598e21004fd75d85322cebe53592312c79e648ca3127edd60cc631006f77158d212d75d30947310047f7558732025dd76cc631006e77648421006bd3059021006bd70590210067f10d95210267e51d8e212a75c510ca31006dc50d8d212b75d508ca310067f74597210367d72597210057d75985320257e710ca510067d6498a513557d74cca510567f43594320067e20d95210275651cc6310047d70597211d67c32d9531004fd764c5211d67f31d9531006dc30d8d21006de10d8d2100cfe7058f210075d3058a51004fd7518532006dc6518d21026bf65592310367d3259432006de5118d210065f65d8d2136ebe73592320075f65d8d2101cfe7598432006dd74d8d210967c7159721026bc31590210257e7298a510276c6298a51006f54198432006df5118d2102776219472117fe67448421036bd2059232006be6458a31004fd74d8e21027ae6448421006bc75592320067f30d952136ebc305923233e7d60cca5100cfc7058f21006dd6418d210067f60d9521036df7358f21006bf72592311cd7f740ca510067f65d8d21004ef76484211cf6f2098a510057d75cc721296dd600ca310fd7c7098a51036be32592320067c70d95312ef5d300ca513275f308ca51006dd3058a310067f659853201cfe75587321e7d72118d210067c6558931006ef7648421014fe74d8e211cd7f708ca51057ce720ca310067d5058a31225dd704c431007d710d8d21014fc7458f2119fe510885210067c51d85320fd7c7058e5116fc53048421006dd43d8d21006ef20588310067d65cc721006ed624ca311d7773194531005bd748c72117fe74148421006be7059232056df628c8310247c7159432024fc749873200cfc70d8d21034fc764c521006bd644c421004dd70d8d211057e74cca51005dd70d8d213267d608ca510257e7198a510067d74d95210267c7518532006dd53d8d21056df608c831036bf32592320067f6598d210067f73597210067e72597310057f7458e511ce7e62947312a75c310ca511d75f30cca5130f5d304ca510fe7e609452100cfe70984321efd5718ca312b75f508ca31054ff7158c210067c5158d210ce7e76d95311ce7e42d9521056de63cca210075d3098e51035ec724c521056dd760ca310063f50590211cf7421d95211ce7c63947210267f6058a510067f50587322e67d64947310f67e65cc721006df30d89311cf6f2094721056df3058b310275e51cc631037e6634842116f6550484210076d620ca510067c4159432006de20d8d2116fe53048421006ec5258a31007c47348421006f75158632006dd3058f213667e73d9532004fd70d8d210257c7198a5116fcd30484211e6df2118d21006bd6458a31024fc75d8e21037e5644842121edd604c431014fe749
  | 3 => 0xd74984320067f60d9531034fc76cc521006dc4018d210567e3059731036f761885210067e73597210367f4259721004fd7458b310067f41d9532004fd7498632004ff7058f210567f3159432006bd10590210065c6394521024ff74987320257f70947310367c72594320065c6518d210067c60d95320075c6518d210057d76cca510057f754c521056dd7518d2108dbe748c7211cd7f7498a510067f40d9531006be74d8d210567f43597310d5de740ca310ae7c650c521004bd7498732005dd710ca310276f6258a510067f4059721006be30592310277631947310367d21597211d67c63945210257f7094521035ee76885210057d7458e51006bd644ca310257e760ca510067c20d953100cee7688521037e56348421006ef6298931006ef2058a310d6bd7159231004fd7058f21004fd74d89310267c6258a510057d718ca51014fe74d8931014fc74584320067d30d95320067d50986323157d704ca510067d74d95310067d6098a510069e74d8d21056de7418d21036bf21592320057d75989310067d75d8532025df764c4312375d508c8310057d7058a51006dd63cca21177e57048421027e410484210067e10d95211367d73d95322075f3094721055dc740ca31055de728ca31005f7714c921056df30588310079e74d8d21004ff7058e210067c6518d210367c3259432014fe74d8d2112ebe644ca31027e661484212bddd708ca310067d43d9521056df7018d213667c31d9532026be51592310057e7694531027766158e510067c74d95310067d64d9531006bc7059232005f6718c9310ce7c654c5210067e4059432004ff7458f210067c30d95210567c43594320367c20597210067f50986320d6dc648c531004fd75d8931036bd72590210257e7398e51006df74d8d211eedc32d8e21006dd4118d2128fd551cc6310275c51cc631024ff7518532037a66448421006ed42d8931056dc634c921056f43158732006dc74d8d210257e76cca510069d3059021006df764c4311eede32987320fd7e70cca510257e7194521026df7358c211cd7f7098a51006dc64d8d210067c70d9532057ce728c831014fe745873220d7d70947210275f6358e510fd7e7098a51006dd30587320275c319473116fe510484210067e74d9531006dc54d8d210fd7c700ca510077710d9521004ff7158d210067c405943203ebf71590210267f6394531036bf52592320067c73597211e6de321853206d7c754c521024ff70987320079d648ca310267c6398a510067c4359721057d6618c8310057f754c931004fd7458e210247e71d95210067c70597310de7c658c5210063d50590210067e72d9531036de3258c21004fd74185320067c75588310057f75589310567e30594320065f30d9521006bf51592311067e64947210075f30d95212375f508c831
  | 4 => 0x92320de7e658c7211ce7e760ca510c5be748c931005f7714ca310fe7c60947211367e76d95320067e73d9521197e775484210067c60d952106d7e75cc521036be52590210257d7698e510d59e748ca31007cd2018d210cd7e76d95310067d10d9532007e7734842135e7c42d9532027e651c8621006df5418d210367c2059432006dd72d8d21007e67348421055dc74cc631034fe76cc521024ff7598632006dd20d8d212cebf3159231004fd70d8532006bc5259231006bf70592321e6dc3218532024fe7158c210567c43597310067f65cc9210067c7459731056dc7218d2130f5f304ca51025df714c431006f76198532007cf73484210257e7194531006dd5118d21014fe7458e210075f30d95320067d64d9532006dd3058432056de634ca210067f5058432036f77158432006dc5118d211cf5f328ca51006f45158632005f571cca21026be749873200cfc705883101cfe7558e21006de5358c211e6dc5218d21004fd7458d210067451586321067e64945210047f70d95210fe7c60947310067f74d95210fe7e60947210d5be748ca31006ed42588310de7c658c531056dc63cc5210d69c735923130e7d604ca510067d70d9521056f431584320fe7e6094531004fd76cc42101c7e76d95311d77731d9531006df3058f210f67c7159731056dc3158432027e463484211d67e73d95310247c764ca511067e649473100cfc70587320067d60d9532027e710885210567c32597311bf5d3094521004ff7558e210067e40597312cebc3259231004fd7558f210575e75cc631006de43d8d21187e753484210276c6258a510067f5058d2119fcf3088521026bc1059021004fd75d8e21006dc41d8d210257c71d9531006dd40d8d210067d50584320257c714ca51026be2159021006bf5159232006be51592320075c63945210a5de744c431007cf6388521026bc51592310067d42d953236ebe535923223ddd708c831006dd30986320057f7058a511ef9d748ca31056dc7518d210257c7158a510067e41597210567c73597310067c4059731035ee72cc7210263e51592310367e72597210fd7c704ca51056dd7118d211eedc72d8d21004fd7598432055de728c8310f67e71597310067f20d95310067d735972101cfe755883131d7d744ca510fe7e60947310367f2059721037e565484210067c51586320067f42d95310067e71d9532006de4018d210067d70d95310267c51d8e21005bd74d8d210075f3098a51026df618c5310267c51984320067e41d9531006dc60d8d210067c7558c2101cfc75d85320067c64d9521026bf6059231024fc74d8e21006be7059231006df6418d21006df63cc921056f7618c5310047f70d95310067f74597310067f6518532004bd74d8d210a5dc744c4310567d32597310267e63947310067d4159731004f
  | 5 => 0x4fd70588310257e71cca51006f561185320067f7259731056f7715873201cfc75586321d67c31d95312af9e640ca311bf6f20945210067d650c7210276651c862135e7c21d9532006bc2059231006df4018d210276e2198a51006bf3059021026ef60c8621006df51d8d21006dd30d8532054de76d8d21006dc75d8d211ce7e32d95210247c7598432006de70d8d210053d748ca51006dd2118d2116fe43048421006f510584320067f73d95210057f70d9531004fd7058c21005dd760ca31006de53d8d210267d76947310067f72d9531024fc71d8d21024fe71d8d210367f20594321e6dc2018d21006dd64d8d21036e760484210067f40594320067d7159721027e764484210075f3058a5136ebc73592320367d215943200cfc7058b310057d764ca51006dd3058d210267e5158c210076f75484210ae7e650c7210257c768ca510067e41594320d6de648c5310273e5159231006df52d8d210277451cc621006bf53590210a59e748c83100cfc7058d2127f5f50cc6311efd721d8d2124edf608c531054fe76d8d211be7d60945210367e72594320067d40d952117fe54348421004fd7458a312dd7d7094731006bd52592310257f70945310067d654c7210ce7d31d953102774510c5210367f4259432006bc51592320263c5159231026f6419843216ee56048421036bc72592320067d50d8532036ee62189310267f6294521036bc32592320047d75d8e210067e70d952106c7d76947211bf75109452100cfc7058a31026ee21588310eebe64cc4211d75f300ca5116fc7304842107e7c6588521006df3058a31054fd7158c210fd7c70cca510067d6058a510ce7e654c7210067f658c5310575d750ca310067c41d9521187e55348421026ed72d8e2100cfe7058632026ef6048421056ef7258b31006dd75d8d210067c10d95321a5ed708852101cfe7558a31006bc7359021006dd5218d21005f7714c931006dd5418d211e79d748c831056df7518d21004ff75d89310067c74597210047d7059731024ff7598732004fd7058b31006bd5159231036bd32592320266f6298a511eedf21d8d210067e43d95210257c71cca51027e710484210067d658c721177e770484211d75f3098e5101cfc75d89310065c5118d210047d70d9531006de6518d21007c773484210067d71d9532006bf7559021004ff7558a312975f500ca310067d5058d210075c5118d210057d7458a510067e7059731006bd70592320067d20d9521006bf70590210047d75d8532006dd6318d210057e71d95320057f754ca2116fe730484210076f6588521006f510986320067f7558c21026bc21590212ee7d600ca51006df75d8d21014fe7458f2116fcf30484210067c74d952116eed60484210076d4298a510057f70d95211ce7f6394721026ef7258831006be305
  | 6 => 0xd760ca510ce7d71d9531034fe7258c2107d7c754c6210273c51592311357c7558532006bc5059021025ef76484211c57d7094521057d7714c431036de3258f21014fe74586322cebc5359231036bc2059232024fc76cc921006df30986320067f10d95320067c2059731056f73198732006dc40d8d21014fc745873200cfc7058c21006be1059021005f4714c9211d57f7498e5106e7c71d952135f5e32d95320067f20597310067d70597310247e760ca511cd7f700ca510067f63945210d69f7359231026f421986320fd7c7098e51024fc75984321d67f649473106e7e76d9521027d661cc6311e5df708c831025ed76c8621006dd41d8d210276c51c86210575d75cc6310067d42d953125f5c658c5311d67f60947310063c51592321ffe551c8621006de30d8d210067c65d8d211ce7c6494721006bf50592310065d3059721005f5718ca310067d64d95211d67e63945210067e60d95313667f30d9532006bc3059021004fd7098432005dd718ca31027742194521006df5018d212cfb731592310067d73d9521006bd60592310067f4059731004fd7558d21006bf20592310367d42597211057e748ca510067f425973112dbe74985323667f72d95321cf7721d9521006df634c921004ff7458831006dc65d8d2101cfc7558e211357e76d95320067f5058632056dc630c7210067d6358a51006df43d8d2117fe474484210067f50d8e210065d30d95310275c518c5310067c65989311cd7c7498a5117fe454484210d6bf73592311cd7e7298e510257c710ca511d57c7498e51006de6018d21004ff7058d210067f41d95310057d75cc5210067c75587320067f75588310279e64cc631024fc7158c210276e51c862127f5d50cc631056dd7418d211cd7c7258e512675d30945310067f4159721225df704c43116fe610484210267e6294721034fe7398732006de5418d211cd7f760ca510069f30590211d75f3094731006de4118d211e6df2018d2135e7e42d9532056df3058732014fc7458632006df4218d210057f764ca51006ee42d8931056dc3298732006de51d8d2135e7c72d9532006ee20d8931005bd748c5210276c2194721037e66548421065be748c521057d7618c531056df7118d21006bd53590211d57f70cca510067d30d95310267e6158e510067e7459731026ec21588311e6dd628c831055dd768c83100cfe7058c2116fe45048421006dd634ca210067d30597211ce7f21d95211edde72cc631014fe7458a31007677548421006ee52588310079d640ca3100cfc7058e21036be2059021006be6559231014fe7498732014bf76592310275e514c43136ebf3159232014fe74584321eddf708ca31036bc5259232006dd6518d210067e7459721036dc3258c21026bf1059021006bd7359021056dc638c721027743194531
  | 7 => 0x95210267f7598432026f671d8e21005bd748c5310067e30d9521006dd70d8d21006dd51d8d210067c65d8532025de718c5310067f41594320067f50185320067f64d95210067c725973114f76618ca51004fd7458632006bc70590210067d41d9521005f7714ca21026bd74987320276c2198a510257e7158e510279d64cc631004fe768c5211367d72d9532006bf50592322f57d700ca510cd7e7598931024fc75987320063f5059231026ec2158a31024fc7158a31004fd74588310567e3159731036bf20592322975d500ca31037e76188521006dc70d8d21037e77648421006f641d8532026f710986321eedc52d8d210fd7e7098e51004ff70587320457c754c4210267c5158e210276e2158a51027e441484210067c65585321d57d76947310d79c73592310067d50d8e210567d3059432026be31592311cf5f320ca510067e60d9532004ff74d8532027e7634842117fe64348421006df63cc5210067c105972116fe540484210247e71d9532056dc634c5210067c10d95310075d3058e510c5be7498931014fc7458831036bf72592320067e10d95320067f70d9532034fc764c9310067f74d95310367e21597210067d7159731014fc7458a310376d75c8621005bd74985320266c6258a51006dd30586320075f5018d210567c3159432026ec6298a310277710945211eedd628ca31004fd7558432025bf7659231006dd30d8e21006dd30984320065f5018d210267e5158e21006f410d85320267d75d8e210275c3158e51035e776484210067d505863201cfc7558831024ff7498632036bd21592323667c30d9532026ef6188521004ff745873216fe470484210376e75c86210067e4159731006bd50592310067c6598d21026ee7688521024fc74984320067f43d95211bf5f3094521004fd70d8931026f431984320075f658c5310567e31594320067d74d9532026bc71592310067f654c9210067d1059721056dc638c5211be7f6094521036ee628ca31006de5018d21006df64d8d211eede72d8d210275c514c431006be7259231006dc43d8d210267c5118532006be7559021006dc51d8d21006de40d8d21037e421cc921006dd5018d211cf5e324ca510067c42d9531024ff7598432026de614c431004ff7058c210067d43d95320267f75185320ce7d73d953100cfe70d85320567d3159432004fd75987320267c5198732054ff7658e210267c5158c210057d7398a510067f65989310067e20d95320275c6358e510065f63945211cf6e4298a51255dd708c531004fd70986320275e3158e510075f63945210075c65d8d21026ee2158a31026f641185320065c65d8d210067f764ca5101cfc7558a31004ff7058b31056de7518d210267f6058e51004fd70987320267f6498a51005f5718c9311cd7f748ca510067d62947310057
  | 8 => 0x277671947210067f41597310076d20d95210257e764ca51006bc7259231054ff764ca21056df30584320067e70d9532236dd608c8310069d30592311cf3e748ca51026bc60592310cc7d7694731025f6718ca31025f4714ca310057d70d9531006df30d85320067c51d8931056dc32588310fd7e7058a5100cfe70d89313667f32d9532027ad6448421025df708c5310076e4258a51057d6610ca31005bd748ca310267e7694521006bd755923201c7c75588310067f70594320d6bf71592311eedc20d8d21006f71058432056df7418d21006de6418d210067d1059432026df604c431054ff764c5210067f50984320057d7598a3100cfe7058e211eedf638c721004fe7618d210c6be644c4210367c42594321d67e639472126d7d70945310067c7558d21006dd4218d2101cfc7558732036bf52590210267e51588310067d5018532006f510984320067e42d95310067f74d95320075c51d8d21006bd72592310367e4259721026bf62592310457e75cc421004ff7558632006f510586320fd7c708ca510567f31597310067d5098432036f42158432006bd505923201c7e76d9532036f77158632006bd30592311ce7e72d95210063d50592310267f6258e510067c65d89310257e7158a51006bd75590210567c3159731005f4714c931006df3058d21037e77148421006ee42588310067d10d9531026df6398e210067c64d953201cfc7558d210067f65cc52100cfc7018532006dd54d8d21035f671885210057f70d9532006df4118d2106d7c754c921004fd7698e211067c64945210067d6098e51026bc31592310067e7059432024fe71984320367c42597211677661cca51004fd70586320065c51d8d21036bd205902100cfc70584320276c2158a51036be725923207d7e75cc6211ce7d760ca510367c21597210fd7e704ca51024ff7098432037e66448421014fc7458c21034fc7258f21006be50592310067c7558632005dd718c831036be32590210067f629453106e7d72d95210067c5158b310065d5018d210075d5018d210d79f73592310057f7258e51004fd7058a31006bd51592320075d30d9531006df7358d210057f754c421006bc7159232005f671cc9210d5de74cc63106e7e71d9521006dd52d8d210567e73597310567d31597310057f754c6210367d4259432024fe71d89311d76f328ca510067c40d95210075f754c431025ef71484210065f30d953236ebc5359232004fd70d8e21006de65d8d21007cd20d8d210067c51d8d2122f5c754c4311d77431d9531035ee72cc521056dc630c521004fd7058d210067c43d95210c5be748c531006be7059021006ef628c9310065d3059432036bf32590211ce7c32d95212d67d60947310275e518c531055f6718c5310575e750ca31006df54d8d210267c75984320067e40d
  | 9 => 0xf5159021027766198a510067f30597210076d2098a51026f67198432014fc7458d21006bd73592312cebc73592310067d5058c21036ec628c93116fe63048421014fe741853235f5c32d953206e7d21d9521006de60d8d21004bd74d8e21026df7358e21006bf735902100cfe70987320279d748c531036dc3258f21037e56048421006bd305923224f5f508c5310067c305972117fe54148421025ef7088521006dc4358f21006bd73592320367c2159432006dc53d8d21006be7359021006f610d8532006be505923217fe743484210257c718ca511f76d50c86210063d5059232027d6614c4310267c51588310067c42597310067d10597310057f7358a51037e4214c921007d51018d2106e7d71d9521036f421586320047f7558632006dc1018d210279e748c53101c7c7558d21006dd6018d21004fd75588310076e62cca51004ff7458c210067d6394721004ff7058a31026f421984320067c72d9531006bd10592310067f71594320067d43d95311ce7c20d9521056de63cc72101cfe75584320067d435972100cfc7098432024ff741853201c7c7558732006dc63885210067d6458e5106d7c7558d21036ee624ca3124f5d508c5310067f5058c21004fd7558e2136ebc31592320257e7198e510065f30597210065f30d9531006ed2058831006de74d8d212076d2094721004fd7458732006de54d8d21006df50d8d212b6df608ca311e6df630c721024fc74185321357c75185320079d74d8d21004fd74584320047f764ca511eedf20d8d210067f50987320067c7059721004df70d8d210069d74d8d211e6dc4218d21006bf705923101cfe75d8d210067c73d9521006df42d8d211cd7e720ca51005df70d8d21006de41d8d210067c41d9532026de3158c21036bf21590210276e51885210067f10d9531005de7618d210067f70d95211cd7c748ca51056ef32588310fe7c60945211057c7458a510367e2059721024ff74d8e21005bd748c931006df4358f210067c1059432004ff7258d2101cfe7558632037a564484210067f71d95320067d40d95321d57e730ca510067d20d95320067f65d89310073f5059231006dd1018d210067f10597211af6c6588521027e65148421005ef724c721006df40d8d210067d7159432006dd65d8d21187e475484210067f6558d21187e751484210367e2159432187e65348421004ff70d8d211667c65cc921056df7218d210275f6398e51004fd7458c212675f30945310567d30597311d67f30d95310065d3059731006bf75592320067f72d9521004de7618d210257c7198e51006bd74d8d2118fe57448421004ff7558f211efce628ca31014be74d8e210063f505923235e7e32d9532004fd74987321ce7c6294531006dd30185321f76f50c86210047d7059432006bc7059231005ed72cc721
  | 10 => 0xc721006bf75592310a5de748c831024fc7518532146bf7359232006df6518d21006de7618d210067d7059432065be74d8d210057d7098a51006bd6498a310075f50d8d210067c10597310067f755863211f76610ca510257f7658a511cf772194521034fc7258c21007e7314842101cfe75185320367e20594320067c5158f21014fe7458831006bf535923114e7c658c9312067d6094721026dc3158e21056de6318d210076d4258a510057d75cc421006df634c521004ff74584320067f10594323357d748ca511e6de4218d210076f2058a51006bd1059232006f71058632004fd7458f21006be6498a31014be74d8d210065f50d8d211d57f76cca51006be30590213667c73d9532026f710984320067d5058e210567f30594321e7d42118d2100cfe70588312667d60945310069d3059232034fc73587320057d7298e510067f50d89311057c7458e510075f3058e510fd7e708ca51006be52592310257c764ca512fe7e618ca511057c744ca5103ebd71590210067d4259731004fd7558b31027766198e510067e41d952121f5f504c4310067e20d9531055df700ca31026dc6398e210067d5098732006df3058632036bd3259021026f410185320067f64d9532027e451484210057d75cc621006dd3098732026f671986320067f50d8d210276c5188521025f4714ca2134e7e61cca51006df30d8e210067e60d9521006be6059231054fc764c9211eedd620ca310267f61945210567e73594320067d6058e51027665148421055df70cc6311d76f324ca51014fc74d8d21006dd63cc7210057d768ca510057d7498e510067c65189310067d745973117fe4434842116fe64048421036bd7259232036f721986320079d30592310067c659853218fe77448421026f431987322167d64947211e6de5218d21006dd71d8d211876475484211ce7f20d95210367e4259432006ef624c931026be71590211e6dc2118d210567f7359432027e76048421006dd50d8d210067f5058e21004ff74d8931006dd3058c2113776614ca510d5de748ca31004fe760c5210067f40d95210267e5158a31024ff70d8e210cd7c754c9310f67f71597310047d760ca51004ff7558b31006df72d8d21026be74d8e211d67c30d9531004ff7458b310067f42d952100cfc70d8e2116fe44048421027b43159231056ef3258b31004ff74d8d211357e75985320265c6358e51004fd7058e211057e7458e51026de3158e211cf5d320ca51026bc10592313676f32d9532007cf2018d211f7cd30c862135e7f21d95320067e1059721006de50d8d21026dc3158c210073d50592310067e10d95310dd7c754ca31006be5359021026be5159021006bd75592311ce7f71d95211876c7548421004fd74d8d210276e5148421004fd75586320267c6358e51026be2159231006b
  | 11 => 0x257e718ca51006de64d8d21025ee71885210067f5058b310947e769452100cfe70986323667c43d9532025f671cca210277671947310957c754c7210067e1059432004fd74d85322475e518c8310367f72597210067e6398a510069f30592310067c40d95322767f64945310567f305973121f5d504c431006dd42d8d2100cfe70185321367c654c9210067f6518d2133f5d30cca510067f10597310067e42597310067c6518532026ec6258a310067d70d95320076d2058a512cebf30592310067c41d95310067f75584320067c7558432056dc7018d210fd7c7058a51036bc52590210257f7358e51285dd70cc631006be20592310067d4059721006dd30d89310567d435943217fe55448421004fd75587320067c4159721027645148421026be7159231006bd64cc421006bf7159232007d71018d210067e435972100cfc70986321cd7f768ca510067f654c521006dd3058b31036f72158432006df41d8d210057d70d95210067f658c931004ff7458e21006dd30d8d21026bc71590211e6dd768c8310047d70d95211357e75d85320067d745972101cfc7558c210067f65189310067d20d9531005dd7018d210367d2059721024ff7358c21024ff70986322475e518ca310cd7c7558931006bd715923201cfc7558f211cf6e320ca510567c30594320067e30d9532004dd7018d213457d70cca51007e573484213267f608ca513157f704ca510367e3259721034ff764ca310065d50d8d21056df3098432056ec3258b31006de2018d210067d72d9531006f64158432006ef5258a310076d62cca510067f658c5210257c760ca510067d41d953201cfe75d8e210075d50d8d210367f3259721037e660484210267c5158a3100cfe70584320067f43d95321367d32d9532026bc5159021027766158a51034fc72d8d211057e740ca510047f70597310067d5058b31187e675484210fd7e700ca51006df1018d21004ff70586321d67f32d953117fe7544842129ddd700ca310067c70d95210267c6298e510276c514842133e7f60cca51004ff75d853201cfe75d8931036bc32590210075f30d9531006bc1059232026ee61484210263e5159021187e551484210267e76945310275c3198e51006df630c5210565f30594321d57f7098e510057d71cca51026bc21592310057f75585320567f7359731034ff7258c2131d7f744ca510fe7c6094531006ed628ca31006ed2058a31036be2159232006df6018d21056dc7418d21024ff75d8e211efd6718ca310567d73594320067d50d8d210067f60d95321d67f71d95311d67e6358e51006f751986320047f70d95321de7d6494521026bd74d8e21024fc7498632006dd3058e21014fc7458b3100cfe70d8e21006be7159232006df638c521004ff7558831006bc7559021036bc7259021035ec724
  | 12 => 0x1b0240220b80030000000000140080ee03b00500000802b01200001700300000600500000000101700a00006301100d00200912501203100000000706a00200000b00201e00800000002605e00800400700100700131701e01500f00021400208d00f00800201500500204a00438001700001814b00e00a00301506300104400300003500800b00000500000701e00000100001200200001800f0133fc00800602d00103d00004307b0000000100001de01935100b0873d30292820050055b40020320050510000030020050070016530100451500a301d00500000d5f701d00700503a00300005c01900000500000e00000e07800529c01801631700206500104100704d00a0261d300900800704302000100000003208000000002500a06100d01702304f00f00000801100500100401a0190a002f0000140040e700400002600000501e01d00100600000200007301b00200201f0000d700005200101c00009800400500000c0150f700e01303201b0020060610a500000500500707900d5590d804400316704200a00101600000f00003639000d02500200e07e01c7e75d8e210075d30d9521006dc5418d211de7f64945210057f754c7210367f21597210067f74594320257f7094721004ff7558d210367d7259432006f541584323667f31d95320067f41d95210257f7658e510567c3059731024ff7018532027e46548421014fc7458e210057d7058e511067e64945310057f7458a51006be10592310263c515902100cfc70586321eedf71d8d21004ff7058432296df600ca31034ff7158831006ec20d89312475c518ca311ce7e6258a51056ec325883100cfe7058732014fe7458d2132d7d708ca510067e74594320067f705972116fe740484210065f6518d21035e671885210267f6358a510267e6198a51026f451986320067f75587320067e7159432004fd7558c210067d4159432024fc7598632036ec624c931036be5259232027e661c86210047f75588312cebc30592310067d30d95212767d6494531006dc5018d21036bd52590210567d43597310047f70594320067e64d9532026bf10592311057e7458a511057e7498e510067c70594322b6dd608ca310067e205973107d7c754ca21006bd5359231006bc7559231026bc6559231004fe76cc9210067f650c5211357d738ca511067c6494531006bf5359232004ff75d8d21036ed76c8621056f73158732006de1018d2101cfc75584320075f6518d211d67e43d95310565f305973107d7e7598e2101cfe7558b310067f50588313275d308ca51006df30185320247c75185320067c7459432006ef7258d21036bc2159232026dc6358e210567d73597311cd7c740ca51006bd5159021056f731984320067d40d9531026f6719873235e7c32d95320057e76945210067d50d8931
  | 13 => 0x122df03400c00307900100200000f01a00000103814600000d0160f000802900600900035402700003000203f0040030a700302404c0200101920920020100a50700050070e201601400001400902204b00000200406600b03700200c01000600700100100000306900158401200f5750010000070190650a302b00010b02000b01300201300a00002a00102905c05e01d63100100200500b04f00000000100914e02402600900506e00700d0030010110ba00000a00f00300000b02300100900000400000004a00003172b01c00201803201001d00600437b0250100c00000010005a10071b604100a0e60a902505300a12950f00b5e80060010830031160030060200d000003400007800900f0010f400645100200f00000000000100500005a00000f01462700000424400f00000000000000100e00d02013302f00200056400500000c00e02c00b12009500000300900007200500b01300100504b10b01601b0030020780000150bb00f09400e00700800303600200800503e00005100300208f00700f00800300b0070a900005903b00200914003c00200500f00e00002801d00000000002400701d00100000401b00000301e00000015c0000030130050a903e00227301301b0060000e00370a20040010010000cd3ba04200102303a00000e00104000400600000001900600706000300c00000400044500109f0270010280000011a201f05d08800000500b08100100000100005900402500c00000205f02a49c00001700002e00800000201700201500d01100600f00200e0010370010dc00a05e00000900800000e0070020000ea0000190100005cf00800000800000105e00600104c0580000030020040030ab0000080060000b601901306101503802000d00000100401903501107200c00402a0130090070110420070010386132ba00a00400208400f00c00f00301f03b00b00005d0040110496d600414501700200300004300600000801700c00e3ea00401505d0040450040044110700
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa5c83507654840d5c904882c2190021f61c40d953248d5bc0ae6b24623ac5c73dd5610c8754bd07086ca9880297a0c405972100536c1020b2e6273e5451cc2618c8010f90ea82c69082ab520d41984320cc3ec3821b2a6200c3c655d231484010fb0f326ca9900297e0d71597210052ec06cbb1a4200a5f8558c634840147d09392cb988023761c4018d210043f43c20b2e620087e87043654c4330fb0e306ca98802a76106018d210251e40ea0b20420ae5b804c165cc4014bf06b26ca90803a65813059231026373b2c5994a2028bc845c1620c44147d09b1ca29080e1f215764c521006adb8260b1ca2008dd8794363484070f90aba2c3990032b5c872592310243f434ed28a4200a5f80d8e51484014bf06a0acb9080297a0c10597210054ec18e0b24646da9e83141648c8015b700b26c6909df179db30d95320070f42ce9b1a420087e871c365484918bce3b1ca2908029760c60d95210062fb2ae031a426be6820483654c8730fd0e28ac31900319ddb754842135eb210eea9924200ad581d0863484015ad02200c6908f637a1e10d8d2117dd3426e69084200a5e85d0b63484018baea3aec690803879d350d8d2100536c10e1b2a420087d87883654c4010fb0e082cb988e799d8765885210546e41ae8b10620087f855c163084018bae0986ca990030f5d564cc4210052e436a031a4200a3e8584164084014bf0a880c6908030f9d3658c5210070fa8660b24646ec5e764c3654c401c3ea0982c9188023761c40d8d210043ec3c41b2a4200a3f855cd64084b3d3700982c9189c78794530592310066cb826130e6400a6d82103654c4014bd07202cb908f637a1f3058a310043ec3e85b2a620087d87d4363884014bd06206ca9080317dc350d8d2100762b00e69084200acd8210363484fb87ce9a86c6908021f61e70d952103656312e91926230b64854c521084098dcecb1065288129b21b2058a510243e40eec994a23cad48644063484010fb0f202ca1900e1f21570587320062ebae61b0a6480a5e830c365484014bd0a386c69080396e015018d211d62e31eea98a420487e815d83294401c6a8220acb9880317d43764c4310070f3a0a3b1a4200d1f305d2329440147d0b392c918802972195018d210262f28eec98862048ec825d563c84010fd0f082ca190024f6137358a512470ec20a3b1a4200a5f8350765484014bd06086ca908029d60672597310054e41aeab204200a3e841836548401b88e039a4210a4a6721d30592313fc3e43a20b2e4200c5f704c165c84014bb07386ca98802976174218d210047dc02e8b1a420387e85dc3614c80187ceab266210803d1dd773484210243f40eeab1a4200cd970d8063484014bd0b186c6908129da0750185320062e28ee1b1a4239b6482443654847b5a90c886c690803275d170d8d21
  | 1 => 0x8e8a14c5288021f61e60d95321343ec3ecbb0a6448e1e8414763484014bb01b28c6909b297a0c70d95320045fc22e0b1c420aa5e83101650c80147b0b182c91900336dc13058f2103d5ac08e0b204200a6d8204365484014bb0b086c6908063720f7058c21005e3c06e6908427cc3f76541648c4bf8eae228ec6908028fe1130597210043ec3e82b28640087d878c165c84070f90aba0c29906a37e0d74584320043f43ea0b0c642093e84dcd629447959d052a0c6908028f61430590212472b38ec728a420a8de87900634840187ecaba4c2990028f61020d95314545e43a60b246200c3e64dd5328c5134bb07186ca9880387d9574d8d210061f3aac93146254c5e7118e51484014b90aa0ec690803175d530d8e210055ac08e0b24643dbc6871cd21084015b700b20c6908030f5d074d95313ac3ec3ce0b2e4273e1c51cc1648c4b353d07392c9189b6a720d75592323652f41881b2a6400a3e859c1648c8010fb0f086ca908038b508425973135d2e43261b2a640087f805d7614c8010fd0e102cb988021fa1c43597211d52f41c41b2a6275c6c825c1650c87bb8eedb9a42108021fe1d50d853200477c12e0b1a4248d56515c6328c4616cd0b39a42109ef279d330d8d211d43f438a2b0e640087e87d95624c4734eb03b9eca908029d20550d85320061f322eb988420a8de8794063484018bceda80c6908029be096498a510043ec3820b2e4200a5c8350565c84018bae1986ca991eb279d130d8d210051f42c40b24620387c855c2610c801878caba4c2990038d50441d95210257343eec908426ca5f804c3654c8015b100b26c690803171d77358d210051f426e7b2a6200a3e851c1648c4d94bd06086ca9900297e0d41d95320262fb1ced28a6200c7b805c3654c8d94bd07206ca990030f9d1658c7210043f43880b286400c5d70cc3654c4014bd0ca86c6908021fe1570185320051fc2261b2a4273e1e51cc1648c401e8aa1b9a421080399ddb754842100566c1ea4b146248a5e8618e51484070fd0bb8ac69080317dc330d9531007c3426e69084200ec8604836348409c6ca3a8ac91880297a1674d8d210066cb828031a4206a6e829c5650c8014790ab8ac9190031e5c360d95311d62e39ac6b14a20aa5e83901650c921c3ee7a82c9188028f61070d952103557410e0b20423a87c87507654c4a9c3b08288c69082b3518e71cc9210070fa8660b24626c87e87d0b654c8015390e982c9189bb171d5305843200537416e7b2a620087d87d43614c80159b04200c6908121fa1f50984320054ec1820b246400aaf8254d648c8010fb0f082cb909a61f21d654c7210070f426c728a4200c3f655d3634840d958c4ba4c4988021fa1c1059432007a3ba8e69084204ce687dd921084014bb06202cb9880317dc330597210043e43a20b286400
  | 2 => 0x16098e513f43e43a82b2e4200a5c855046348475caec3b2c62988030fdd274597310052fc2ac9b1a4254c5c315d832944014bf06a0eca988129d20750986320046f43881b1a4200a5c864c36548491aa8a2b8c64188030fdd675592322452e40aa1b1a4200e1d859d363484090f90f886ca90803279d3638c52145c5fc3a60b246400c3d87145648c8070f90fa82c6108e61fe1f65cc5211d43f43c21b2a620087f855c161cc8015cf01bb24210966a720d75592310064eba087b1a4200a3c8458365484031bf0e986c71087e1fe1d10597213a43f438e0b28640a8de878806348401ce0c0886ca90802976161018d210045ec24ec31a423aa5f804c3654c47978d0739a42108021fa1d50586320061f3a0cb30a640087d8790165c8401cb0c0986ca990022f61c20592310347ac0eebb1a4254c5e315d8329440193ae9b86c6908824f2117058e510552f41840b2e622687d87183654c80153b09b96c690953959c463945210043f438e1b2a6404a5c864c16394479b8eec39a4210803d14c375484210072ab88a3b1a4259a9e83141648c401ccaa1bb24210802a760c70592310063cb82c1314a200c5f754c1610c8018baeb986c7108021f61c40d95210051fc2261b2a6439a7687145618c8018deedbaa42108029760c40d95210243e40ae1b2a640087f855d0614c8014bd0b386c69080297a195018d2100537414c9b2a6200a9e8418363484a34bf06b8acb988ea97a0e40d95310255b40c60b246200b67855cd210840153d06382c8109fa1fe1d41d95210053ac00a2b0c647e87c8750565cc4014bb00288c6908028fa16105923200536c1020b2e4200a3c85c41648c8014df04b06ca98966a720d705923102637b14ed28a420087f855d1610c9054ed02386ca9080237a1e40d8d211ede241221b1a4200c5f754c16348401e8aa039a42108030f5d150d8d210043fc32eb98e4200a3f84583654c8018bae731cc5288029760051d8d210052ec28c1b1a4200a9e8414463484bf0fd0dbaa62908032761370d8d210064e422e031a42008df835d163484010fb0f186ca908121fa0770d952101c3fc3ea1b1c420487c87d42610c8010fd0e086ca990121fa077558c214545e43a60b246404c6c7698b32944010fb0f082cb98966a7a0c20592313643e43eca99242048f4815d563884a94bd0db1ca29087e1fe1d10597310043f43e82b286478a5e8514063484154b906a0aca190029b60b73d95211cd37410e1b2a42008bd84dc363484010fb0fb2e62908028f21573590210051ec2ce0b246400c5d705406348401c6a8220acb908063721d3058d21006e3438e690842008df835d563484011bd0f106c6908021fa1f42d9521005b3c2a629084200c5c65dc063484d94b906a0eca990028f61670592310062e32ae1b1a42008dd878436348473a5
  | 3 => 0x31a420ae5b804c1650c80147f08986ca98803175c063945213ac3ec3ce0b28643aa5e831c3654c4750fd0eb2a63908029721510d8d210043ec2ee9b0a6400a9d83941640840187ce832ec6908029760c10d95210165b3a283b0a640d87d8704365484014bb0a206c690812d9a0775484210054fc2261b1a420387e87dd5620c4014bd07326ca909b3171cf75588310061ebacc9314626ec5c754c163484734eb02386ca908028fa1410592320051ec2ce0b204200c3d7454261cc80187ee93a2ca190123b60b75d8d210062f3b6c728a4200c9d849d863484018f700b86ca9080297a1460d8d210052e42ac631a421fc5c714c365484016cb01baa42109a7179db30d95310045fc3a60b204200a5d83101650c8eb47b0b282c8108121f20570d95210063bc0ae0b2e6200a5d8398365484018eae238eca990021f61d50d85320054f420e1b1a4200ec776dcd21084014bb07102cb9880e1fa1f7558c210552f418e0b28640387c855c1620c4014b906b8acb908028f61420592312452f40ea1b1a4200f4730dd521084f987ce8a86c7108029760c40d953200c7643a40b106200c5d70d8e51484014bf0ab8ec690802976146018d21016563a284b106200e3684145618c8758be61baac2190021fe1570984320045fc22e0b106204a3c81d41648c4918bee1b1ca2908028f61630592311cd36412c6b14a23987c8758d62944018f6e0b02c5288021fa1f65585320062eb8261b2a4204a7681194614c8010fd0ea82c219002a7a106018d210552e41ae8b28643cbc48244063484754b906a0eca988023761c1018d210054ec1ce0b204200a9e874c1648c4bf0ff0cb8c65288021fa1d5058c211ed6ac0eebb1a4200a5d8310165c84d90fd0f106ca991c7171d5301853200536c1021b2a6400c3e74d96614c8e38b8ea984c2190030f9d3658c5310043ec3aa1b1c4254e545190463484010fb0f086ca988031ddd451586323fe2f38a61b2a4200a3e85841648c40153b083aec690a6e9b60a71594320061e3aac89884200a5e839c165c84d9cb700986ca990028f61271d95321cf1621285b2a4200a9d83881648c4018daa1bb2421080297e156418d210062fbae60b1a4200e3541105650c8151b906ba0c2990029b60810594320052f42e8431a420087d80dd5618c801cb700982cb9080371dd073484210043f43c41b2a4200a9d84dc36348401c3f08982cb988029761674d8d210045e43a60b204204a5c86cc163944092d904b9cc528802ab61020d89310051ec26e7b2a626ca5e83883654c8070f90aba4c2190021fe1574586320052ec1841b2a620087d87d07654c80153b07082c8109cf9318b3058a510043f436e1b2a620087f87583654c4754bd06206ca9895387a105118d210071aa0883b2a6406ce581dd9210840147908986ca908031e5c
  | 4 => 0x3484018bcec31ca2908029760063945210fc3fc3ac1314a200a5c8544063485159390e982c918803b418110d8d210043f43860b2e4200a5e8599363484015cb01bb24210802976144018d21186b343eea9084200c3c655d2624c4018bae1a80c69080297a164018d213652f41ce1b2a6400a3f855cd648c80199eedb9a42108f637e1d63cca210043fc2ae0b10620387e87dd5618c8010fb0f106ca990030f5d350d8e210056b4362031a421aab5811c1648c4d74bb06386ca990824f2117058a510056bc0a4031a4254a5e81d406348491e8ca3b9a421080297a146018d210053b40ecbb0a6400a5e831c365484078b8eb29ec6908021f61c20d95310070e42260b2e6200ce575dd9210840147f0a882c81081a3d21d41584323ad1ec2ca0b24640387e86dd5634840178902906c690803875d150d8d2100573c32e69084259a9c835c9648c4070f90ab80c299003b1dd873484210043ec3c81b2a640a8dc835d5620c40117d0e102c9188021fe157458d210051ec28e6b204200a5d8304165c84791bf0eb1e6390802a76127618d210070fc2261b2a4204ce651dd92108401c38cb3a6c69080237a1f3058d210355741460b246404c3c515d36388401e8ea1b9a42109672720d74987320052ec1cc9b2a4200c5c515c0634840187ecaba462908021fe157058d210071dc02a0b204254c5f7018e51484dd8bcea986c299002d920520d95211d43e43ac8b1ca200a6d82043654c40153d09b96c690803175c330d95210043e43a82b28643dace82dd763484010fd0fa16ca988023761c6018d210052f42887b1a4200ae581083624c40159b05baec6908031719770d8d210061fbaac89884200e954110763484038f4e0a80c2990023761e20d8d212cd4f41ceab24628b8bf874c1648c40d4dd053a2cb908028fa14205923100566c1021b1a4200a5d8599363484ff8bce3986ca909fa1fe1d41d95310054ec18a0b204200ae5869cd210840196ae9b0cc29902a9720d71594320051ec2cc0b246273c5c75cc0614c80147d0bb8ac9190029761640d8d210062ebaec731a423aa5e83043654c4019b2e0306c6909af8b10942d95323c43f438e0b2e620387c855c163484e3c98c4982c528802a721160d8d210056c402c831a4270a5e830c165c84014bf06a0aca19123d11477348421005b3c06ea908420087c87541620c53d4bb07186ca9900396e0130d95210061eba2a1b1c4200acf82440634840153b07082c9190e69ba0b73d95210043f43887b2a4200a5e8590363484010fb0e186ca908c2d921573484210043f43880b2e6200e3541107654c40147908986ca991a7171cc75584320556a41a82b08643987e87d07654847959904880c6908029d2055058632025b240eea908421a8df8750463484014bd0b306c69082a37a1e1018d212a52e40aa
  | 5 => 0x8803275d130d8d210052e42ac1b1a4207aad821c16408401ccea1bb24210803719c073484210070fc2260b286404e6651dd921084014bd0ba08c6908023761c10d8d210251f42ea2b2042048ec87509620c4010fd0e32ac4988032d5c471592320043f43e82b2e6200a3e851c164084014bd0b320c690802a7a0e10590210062fb8261b2a647f87c8744165cc40155d04382c918802b960810d85320062fb2ae1b1a4200e1d7414763484011bd0e086c6908030f1d5644ca310063a32ce31926200a5e85d0763484010fd0e3b26528802976166418d2100566c102031a427f87f8744365484090fd0ea84c219002f160073484212fc3e432eb98a4200a3e859c1648c51dc38e6a82c9188028f61272597311cf92b26ea9084200a3c84583654c4011bb0f200c690802f12052018d211ee66396c698a4200a5e86147634850d4df04b9acb908030f995748c7210052ec1c20b2e62008dd87994634840117b0e082c9190029760e40597310fe3d382c1314a204a6e8650a62944014bd0b106c690802a7e0d7559021006e2ba0e690842028bc845c1630840187ae9a86c6908021fe1d50d8e210267238ac49946200f47501cd21084011bb01bb26218812ad20553592310074aa088231a4200a9e841d763484014b90ab8ec690802b560e10185321043fc3a82b2e6200a3d84dcf654840187cc9baa62109df171cc755883137e2f3ae61b0a6400a9d83941648c809cc8a3bb2421080637e1d30d8d210052ec00cbb1a4200e1f5495363484078b8eb29ac61080333dd8734842100537c12c1314a27ac9f764c1648c401878caba4629880267e1d648ca310052f43661b2a4200a9f835c1648c4092d90e902c52882a97a0e70594321d6ad982e131ca200c5f65dc063484014bd06382cb9080297a1440d8d211061e3a2c8b1ca23de8c4250b634843f8f4e0b04c728803174c1760ca510072a28a60b0c640ac5c635d663484010fd0e32ac690802ada04705923200637c12e0b286404c6651dd921084018f2e0306ca988029da0750d85320054e422c031a4200a5d8590063484014bb07106ca9080297e0d60d95210064eba261b1c42028ef8750b624c40153908982c790953d114473484210043fc3ac1b2a6400c3c655d2324c40193f0eba6c6908028fa1630590214d52fc1ae2b28640087e87883654c40153b07082c9188021fa1f50588311d52e41ac8b1ca200a9c844c363484f987ce8a84c39900387e1130597210051ec28e0b20427dc3f76d41648c40147b0838aca190130f94574d8e210052ec1881b2a620387e87dd561cc8014eb02202cb9880a2f2117058f210061eb2ae918e420087d8790365484014bd07386ca9080297a166018d210062f3b0ca31a42008be87145648c8018bae0982cb908029d21510586320051f426e7b2a4200cd970d836
  | 6 => 0x70e42260b2e42008df835c16348475cb700986ca98803275d330d8d2114556c10e0b246400a5d831c365484014b90ab00c690802376027618d210043ec2ee1b0a641f87f8758263944dd8b8ea982c61097e1fe19710ca510943f43820b2e4200a3d85841640840159b05a08c6908021fa1c10d9521007c2c26e690842008bf87592328c4018bee1986ca9900327e1d30590210064eba6c718a420d87d87183654840187ce832cc4988028fa16305923237e2e3ae60b1a42008df8758c63484010ff0aba2c61080317dd53058732026b210ced28a4200a5e83983654840159d0d900c6908029b20960d95310257240a40b106200a6e829d165cc40193f08b80c69081b39189718c9310043fc3ac9b2a4200ad583d45618c8014bd0b100c69080297a185118d213954ec1c60b204204c6e51dd921084010fd0f102cb988022fe117058c210fe2e38e61b2a4284a76811d365484fb87ce9a86c7109e61f61e70597310052ec1821b2a6279c5f705406348401cb6c0986ca98802a760e50592310052ec18e1b2a6271c5c714c1650c8090ff0abacc2190029da0420597310056b408e1b1a42028be84dd7634840117f0cba46518803175c150d8d210062fb8661b2a4200c6f50dd92108401c3ea92a0c69080297a144018d211cc3f438a2b086400e1f5394d640840187ecaba4c4989b317cc375588310051ec2021b2a4200a5d80194634840187ae83a6ca9080317dc130d95210043f43ea0b1a4200c9e745c363484019390e982c810a4f27ddb30592310053ac0881b2a4200cdb704c163884010fd0db86ca990030fd95748c9310043ec3c81b2a6200a3f84583654840947f0aa8ac8108021fe1570586320043ec3e83b2a620087e86dd5324840147908982cb908038754130590211cf93326ea9084200e2d6450a62944014bd0a186c6908021f6037558c211e7462128431a4200e1d84d8e51484014ef02b82cb989d28fa1450590210043fc3a83b2a643ac5f305d832944014bb06082cb988ea97a0e70d95310051ec2c40b2462008dd8799063484011bb0f280c6908028f6136394521005d2c26e69084200ec530dd9210840147b0bb8ac919003275d330d8e210052ec2cc1b1a4200e1d74d4363484070ff0fb06ca98802a760c505923235c3f43c61b2a647f87f87443654c40d1b906ba2c399002b360870d8d210062fbaa60b106200c3d741476348401c3908986ca90a2f27e1d30592320052e42a4231a4204c6c51dd921084070f90aba2c319012ada04205923103476412e0b184204a6c86509629440d4dd053a2ca1900317dd530586320071dc02a0b246400a6d82993654c4094dd0c904c5288038b50842d95310546f4388031a4200c5d70cc165c840517908b82c71080e1f21f50588311cc3f43c21b2a4254f46511cd210851f47b0b282c91
  | 7 => 0x7f87593654c40187aeab24c5188e68fa0451592320145e422e0b1a4271e4f624c262944010ff0e886ca990029b60b73d953100636b90e5b2a626fc5c75cc1630840199e61bb2421080e1fa1774d85322fdb343eea9084200a3e858c1648c40147b08082ca19002b560c10d8532024ba40aeb31c420aa5e831c165cc401c3aa0982c9190ea97a0c20d95310052e42ac831a4200a9e839c164084018bee0982cb988021f61c40d95312ce4e31ae918a420087e87103654840147f0a882c918a569760e70597310053ac0880b286400a7581103654c80193ae8984c3990063e2017458d210052fc2a8231a423dad5811c363484e153d06182c810966a721f30592310051ec2021b2a6400a758108165cc4018f700b82ca190eb17cc375587320043fc2ae93086400c6c75589328c4014bd0da86c6909bb179d930d95212452e42e21b1a420087f87583654840d55d04082c91906aa7a13638c5210052ec1c41b2a64008df80dd9310c4014bb07106ca988021fa1f6558d210052ec1c80b2e4200c3e87145648c8010fd0e186ca909ae1fa1c7558c211efc2b26e69084200e1c844c1650c9159390e982c919002a7e0d75592320061f3a6cbb1a4200c5f75cc1618c8010fd0f082cb909bb171d530588310051f420e1b2a4200a5d8384165c840147b0bb92c9188121fa0770d953200c6e43a60b18428bc9f874c1648c5074ed03b9eca908063d21d10586320261e28ae930e646da9e83841648c8010fb0e202cb9880327e0d74d8d210f52ec18e0b2e62008dd87143634840153b07392c9188f2b3a0b4118d210052ec1c21b2a42018dc874c163c8401c3f08986ca988021f21d10d95320052f42c21b1a420087e87d0965cc4014db043a6ca9080a37e1d43d8d2101c6fc3aa7b1a420387c855d163484014bb0ba0ec6908038721130d95320052ec2cc031a4200e3b80541648c401caea328ec69082a37e017018d210052ec2887b1a4200ec730dd921084010fb01baac3990038754330590210043f43aa0b0e642087f8759262944014dd04082cb988029760c10594320051fc2a20b2464008bd84dd7634840156b02102c9188121f21f105943201c3e43ea0b0c6400a6d8298e62944019caa3bb242108121f2077558c210052fc2a83b1a4200a9e84dd763484010fb0dbaa6390803175c130594320261f28ae930e640087e8714563484016cb0b39a4210803179d763cc5210046f436e031a420087e871c3654c4018f2e1b06ca9900335d8c714c9210f43f43820b2e6200a3e851cd640840147b08082cb9080e1fe1f60d95320073888021b2a6200ccd30dd921084014dd04202cb989eb279d130d8e210243fc3e21b2a420487e81dd932944ed55f04b82c8108030f5d350987320046f43ca1b1a4200a9d83141648c4f18be61b82ca190029760e40d95210
  | 8 => 0x7382c9190132d1d141984320043fc3acb98e4200a3c844c3654c40153f08b06c6908029da0465d85320053ac0880b2e4200e5451cc1618c8070fd0dbaac4988029760e10d95323a43f438e0b2e420387c855c1610c8014e90b882c319003171957018d210056ac0881b1a4200c5d75d4f63484011df0eb10c4988128fa0750590210052ec1c20b28640387c855d1620c4614ed03b96ca90803174c3764ca510045fc22e0b1e4200acd83083624c4f987ce8a86c69080297a0c60d95210051ec2c20b246400cd9704c36348521c38e7a82c9189eb279d130987320062ea86ec9886200e1f659d3634840947d02a82c8108038721130d95310043ec3c61b2a6200a3c855cd648c8092b90e982c7289bf179db30d95210070fc2261b2a646987f865c732944010fb0fa0eca908029760e70d95212a52e42e2031a420087e87103654c87bf0cc9b9a42108029da0664d95320051f42020b2e6204a6c86481629440947d0ba8ac918802a761375d8d210052ec1c80b2864048dc8754d6308479f0ac839a4210966a7a0e10592310043ec3ce1b2a620a8dc8750463484fb87ce9a84c3991c71718d7058e510051ec20c1b2a420087e87083654c40196ac9b8a6518802a760c7059021007a23aee69084200ab5818c1648c40195ae9b14c4988e69ba0810d952101c3f436eab0a640087d87101650c8014db04202cb989cf1718f7058e510054ec1ce0b246400c9f835d261cc8734dd04206ca90a1e9b60a74597210043f43ea0b1842008bf845c1610c8014bd0da80c690803171d7764c4310052ec2ce1b1a4239e6760dd521084010fb0fa16ca9916727cc174987320052ec2e8231a4200a5e85dcb63484e553b07182c91900297a161018d210043ec3c20b28646de1e53d4d648c8158b8c6bae62908028f61010597313a51f428a0b246400a9e8394164084090f902bb065288128f20550590210043ec3e85b2a4200cdb805c363484010fb0f202cb988029761630d8d210046ec3c81b1a420387c855d163084010fb0f306ca908030f9d365989310556641a84b10620087e8790165c84011bb0e280c69097f0f985748ca510052ec1c81b2a646ec5c754c161cc92f4ed033a2cb989e317cc370597310043fc3ac9b2a640487c815c1650c8011bb0f080c6908021f6177158d210051f42ee4b246200aad828c1648c8092df0eb1665288028fa1010d95210066cb848031a4279c5f305c1650c8d30fd0fb2a62908028f60051592320552f41ce0b2e6200a3e851c1648c8e78bce3986ca9900317d9770d8d210062ebaec798a426ec5c754c1618c80187ecaba462988021f6037558d2100656ba6c5192627bc9e74cc363884019b2e0986c7108028fa1020597311ce3ac0eeab0c6471c5e714c3654c80147d0b302c9188021f61f41597311ce373b6cb10a42008
  | 9 => 0x74d95211d52fc00c728a429ca5f835d1650c879f0cc839a421081a9ba0a705972136d4e41ae2b246400a9d8414763484011bd0e286c690803179d95018d210145f426e1b1a4200c5f75d8d32484014bb01b1ca2908030f19574d8d210061eb02e9194a200c9e84dc363484f18bee1a80c6909b6a7a0e505923200536c1081b2a4200a9d839c1648c4015ab02200c69080327a127618d210043fc2ae8b106200c5f30dd93294401cc8ebbb24210803175c130597310072a28a8231a4204c76711c7654c80127f08b82c5288021f60375588310062eb86a1b1a4200c7970183654840d4dd04202ca191ae9ba0810d95320247643aa4b106230b6685cc52108401c3ea0982c8108063ba1b724c5210043ec3821b2a6400a5d8504063484010f90ea82c3190031b0cb764ca510043ec3880b2e4200a5f854846348409b4842ba462908028fa1020d953138f0f28a60b2042008df87d8063484291bf0ea0ec6908028f61610592310052ec1c81b2a6206aac825c164084010ff00bb065288029760c705972138e2fbaa613086406a6e8204165c8401cb6c0986ca99003171d7634c5210054fc22c031a420087e878c36548401c3ce8a86c690803d11d4734842136d4f418e0b246400e9b804c164084b353d07102c9188021f61f42597310052ec2821b1a4200a768110165cc40147d08082cb909a717dc05118d210043ec3ce1b2a640aa5e8384165cc4151bd0e280c6908063b21d2058a310fc3e43a21b2a6200a3c8544164084018bae639eca908021f61c43597210061fbaac89946200a5d850c363484010fd0e202cb909c2a7e0130592320265a38ac89946245a7681dcf654c40147d08082ca190021fa1b754c9310043ec3cc9b2a620387c855c1630840187ae83a6ca99002b5a074218d210054fc1aeab246204a3f85545648c40517d093b0c6908021fa1f50584320049fc22e0b1ca294a74815c165cc40187eeb3aac8108028f610205973136d4f41820b246459e1e53d4d648c40d4dd04202cb908028fa1010d95320145e422e0b086400c74815c165cc401c3aa1982c9191ae1f21b75585320064f3a6e1b1a420087d87041650c8010fd0f202ca1900317dc150d8d210255b408e0b204200a5c8559363484010fb0f186ca990029d60440d95311043fc3a82b2e420087f855d161cc8e3c38a2982c8108028f61010d95310062e3aec699242008dd879806348401ccac1baa4210802b5a0775d8d210043e43a83b2a6400a9d8404363484750fd0fa0eca988031bccb764ca510052f42821b1a4200c7b805c3654c4010f90ea82c3991bf171d730586324ed36c14e8b28640087d80dd9329440147f08b06ca98a368fa1450592311cd3a43221b2a4220c3e7459262944010fd0f186ca988021fa1c65585320070ea8260b246200c5e76d9463484db53d
  | 10 => 0xb24646ec5e754c3638840593ce921ec690802a761060d8d210054ec20e1b1a4200c3f749d165c84014db053a2cb98802a7e0d72592310054f424ec31a4279a5d8594063484154bf00982cb988021fe1d41594320265a30ae930a646cc5c63dd5324840147908b06ca99166a7a0c70592310052ec1ce1b2a640487e87540614c92d4ed03392cb988029760c10d953201c3e42ae0b0c6404a3c81541648c4094ed0ba8cc319002a760c20592311ed6741081b1a4200a3c85441648c80153b08288c69080387d4330590210054f426e1b1a4220d2c7450962944010fd0f206ca908f63721d41d8d210043f436e1b2a4200ab78154d648c4014bf0ab06c6908038714530592321d62f3b6cb18a627787e87d9532484070fd0fbaac2190f7b1d8373484210056bc1a8230a6498a6f825c1650c8018beea982c6108029da0440594320051ec28e0b246400c74655c6324c401cb0c0986ca988028fa1010d95310043f43e83b2a6471c5f754c0614c8070f90fa82c6909cf8794730590210052e41ac9b2a420387f87d43614c80d4d904b82ca190029da0440d9532006363aeec908420087d87843654c8090f90ea84c2190021f6037558432005e3c00e6908420387c87d4161cc8014ed02106ca988029b60840597210052f41c21b2a4259a9f804c1648c40147f0ab8ac9190031714570d8d212cd4f41ce0b246200d36615d232944010fd0f206ca99002a76101018d210d54fc1ae6b246200a3e81d41648c8014bb0b106c690802ad61010d85320243e43ea030a6439a75811d365484d74dd04206ca99002f160373484210043fc02ebb1c4200a3e859c1640840956d02382c9188123d2057058c210243fc3e21b2a643dcce76d8e2148409968e8a08c2990129d20550986320243e43aa030a641aa9e87cc1648c4010f90ea82c610802a7a1010d8d210061fb02e9194a23fa6f825c565c84018f2e1b06ca908029da0440d952142d36c14e0b2e420aa5f804c1650c8090fd0fb8aca192669760e70594320062fb8260b286400a3c81541648c801c38caba6c69080317dc130d95310061fbaceab24620aa5e83041650c8010ff0ab82c21908e9760c70594320063b438a2b0c648ee1f73541648c4016cb0b98a4210802ab60870592310070ea8660b24620087c87541610c8014b906b06ca9082a97a0e20597310566dc02e031a4200a5e8504063484e7c38a3982c8108131d9c471594320053a40ac1b2a6400c5f76dd5310c4754b906b02c728852a7a13630c5211ed67410e1b1a42068de87d0d63c840d4dd04082ca19002b5a065418d210052ec1ce0b2e4203c6c75949620c4e7c9ec5984c528a32a760e30592310053b40880b2e420087d870c165c840153f06b8ac9190063721d3058e210061f3acc9314620087e8754163484010ff0eb1ca2908e69ba08
  | 11 => 0x4c4df8bceb986c7108030f9d3658c9311e46e43a60b106200a5e8388365484730f90ea0eca9082a3720d70588310063cb82a030a640087e87541620c4011ef02b82c6908063d21d10584320053bc0ac1b2a6471e1c514c1648c4011bb0f100c69087e1f21d10d95210043f43c21b2a6400a3c85441648c4014bd07082cb908f2b3a081018d210062fbae60b18420087d87d0565c84e54bb07182cb908021f61e20597310056b40881b1a420087f87441650c8011bf0eb28c69080297e156018d210063dc02e0b2e4200c7970183654c8014eb02106ca9882a97a0e10594320051e42ae6b2462008f787584614c8018bae0986ca988f2b3a084018d213762f3b261b2a64008df875906348401d8ac1b9a421092395147630c521016573a285b126200a3d859c9648c43f0f90eb02c7289fb0f9d051d8d211e763b00e69084273c5f75cc0614c8015a902900c69081317147764c4313652f41c21b2a640aa5c8350565cc4070f90fa82c2190028fa1071594321cd36412c0b14a204a3e81d41648c40153d0828ec6908029721b50d8d210051f42860b20423987c87d9531484018f700b82cb9880297e1510d8d210062ebaa61b0a6400a5f8350565cc4019b2e0300c6908029d60664d953203536412e6b2e4200cdb704c163084151bd0e080c6908021fa1e40597310043ec3840b2e6200a9d839d5648c473acce3b2c42908128fa0550592310066db8260b1a4200a5c8654363484014db04202ca190029d60674597310fc3e43ac0b14a23dace8204363484a9aa862b8865288029761772d8d210052ec2c4031a4200a5d83843654c4018f6e0b02c728802b56065418d210045ec38a2b246400e5b8054363484090fd03b82ca190e759ddb75484210045fc22e0b1a4200a9e84040634840147f0ab9ac9188029b60840d95320043fc06ec994a20acce7618e21484014bb0ba16c6908021fa1f50587320045f43820b246400d1d305d232944010fd0f182cb9080e1f21574584320054f418a0b204200c5f75d8d314840d55904a9ac9192069760e30d95214443f43eca992620aa5e8310165cc401d34c0982c918a7eabe0973592320070e28e60b246400a3d851c1648c4014bb06102cb988021f61e60d95310073430241b2a4259a9e83941648c4014f700b26ca908029e20164d95210053741021b2a6200a3d85041648c8010fd0fa0acb909b7a6e0130592320070fa8260b246400acd8295063484e3ca8a2984c31900b2d1d141584320253a40aa030a640087e87903654c4014e90a884c3190021fa1c40d95310063b30aed194a200a6e82103654c4018bee739acb908129da0765185320071ac20a2b0c640aa5e8390165cc4010ff0abb262908121fa1f50185320062f3aec731a420387f87d8365484154bd06082cb989e717cc1705973100556c1020
  | 12 => 0x460141202b99a0ac07006022094120340ce30c0400001c0102085508c0080c0160020fc338010240500709b0000a93b80208c1604e8270140f4b300118a0001580902e0281281502201c0000a0c816c091240bcd52848010040100006704c00e5f85301e000970030000ac0004800609b269160420000c00604b10c3801900a1640481d4140f00681106c01402004008000000040060100080a02e0000f8049c21e40220f00800012018090028a4801056008000130000001d80202e104030072400400000a0100001080200007019800088034051e80401681480033c0000080a06c0081482f07e020048060040343bd50218004b180501e0140991d0dc0ac008350720180880202e0203480001806400011010000031bb000060090a000e0a0a801b01c1ac000030080a8038500540000200602e0980183800403c000062c6160098090b8d38038000d00802e0030020006b01e0147a02a0060000000044c09e034000e802013c8600200811c0000100ad34058006980080008400c0400a80610607002001024000040270080000040f00407dc28050600000001000c18000002000000000010140f46580501800000002000000028010100080380d2503440d00407e008000061000b81c801016000000061f2004000280028303a91930e0000081e0060700081c19e0580280b00a0a003a5900a2146d2040180480200005e3c80d01902061c060130120bc009970ec000000020120700301402800c8700f0060680194d2980000000a0840000280401a018df86e00200800b180020240c8030040000f01f07e02c1706918c0bc960010021ac02b350140000d80002a2846a0000221cc000090001040015300e1741f05c0040001200800b3c80d8f011c0100000009e001e2800004024008191581c43880003000c000100160640080000e0008b0a60640140901313a00127017a443f801800000018060070126681d8550020094a04602c0480a80d026000008051040c80200702c0000101010e0084d0000000040080f01e11802020000aa40385328615c4b17640a4089400d01208c3e0000d407c058000260580a80237e1d6018d210043ec3887b2a4200c5f75dcd63484010fb0f326ca908f79394b52d8d2100673baeec9084200a3d858c164084014bb0a386c6908021f601760ca51024b643a84b14a200a3e849c7654c8014bd07206ca9080a3de1d41d853203557410e0b246400a768110365
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x6c621944000f34109b0000da00500110110014000004000000551a5f501cd210840121d989d051d8d210051664051dc36348401899845c06018d2100516640515c063484e7c4651cc376484210055125d501cd2108401c4776cc3754842100594640514c1618c891c4651ddb73484211cd19a5c75dd92108401cc07058073484210055125d30dd521084011c5981c0734842100570241741cd2108409078985c1501853202515a4750dd9310c401ac180580734842100519a5f50dd921084014c4974c37648421005a165a84dcd2108401c4776dd7734842100670600701cd2108401ac380583734842102519a4750dd92108401e4160543734842100561652871cd21084014c497580734842100698e0160dd52108401c47764c3754842138f1194530dd92108401e4160540734842100561650701cd2108401c4776dd473484212a711947761cd210840986481ddb75484210079058130dd52108401619901453059232
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80000200d1025d60540734842100518350382c039a42108034409758130dd521084018604bb00b00e69084200c60651801c07348421
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x209
  | 6 => 0x3
  | 7 => 0x20d
  | 8 => 0x20e
  | 9 => 0x1409
  | 10 => 0x4
  | 11 => 0xb09
  | 12 => 0xb0d
  | 13 => 0xb0e
  | 14 => 0x140d
  | 15 => 0x140e
  | 16 => 0x1549
  | 17 => 0x154d
  | 18 => 0x154e
  | 19 => 0x249
  | 20 => 0x24d
  | 21 => 0x24e
  | 22 => 0x1449
  | 23 => 0xb49
  | 24 => 0xb4d
  | 25 => 0xb4e
  | 26 => 0x144d
  | 27 => 0x144e
  | 28 => 0x16c9
  | 29 => 0x16cd
  | 30 => 0x16ce
  | 31 => 0x14c9
  | 32 => 0x14cd
  | 33 => 0x3c9
  | 34 => 0x3cd
  | 35 => 0x3ce
  | 36 => 0xcc9
  | 37 => 0xccd
  | 38 => 0xcce
  | 39 => 0x15c9
  | 40 => 0x15cd
  | 41 => 0x15ce
  | 42 => 0x1709
  | 43 => 0x170d
  | 44 => 0x170e
  | 45 => 0xb0211
  | 46 => 0x20b11
  | 47 => 0xb0215
  | 48 => 0xb0216
  | 49 => 0x20b15
  | 50 => 0x20b16
  | 51 => 0x140b11
  | 52 => 0xb1411
  | 53 => 0x140b16
  | 54 => 0x16cb16
  | 55 => 0x14cb11
  | 56 => 0xb14d1
  | 57 => 0x14cb
  | 58 => 0x14cc
  | 59 => 0x14cb15
  | 60 => 0x24b
  | 61 => 0x144b
  | 62 => 0x155411
  | 63 => 0x155416
  | 64 => 0x14d551
  | 65 => 0x1554d1
  | 66 => 0x14d555
  | 67 => 0xb4251
  | 68 => 0x24b51
  | 69 => 0xb4256
  | 70 => 0x15c251
  | 71 => 0x255d1
  | 72 => 0x15ca
  | 73 => 0x144b51
  | 74 => 0xb5451
  | 75 => 0x144b56
  | 76 => 0x14cb51
  | 77 => 0xb54d1
  | 78 => 0x14cb55
  | 79 => 0x16d451
  | 80 => 0x1456d1
  | 81 => 0x16d456
  | 82 => 0x3d451
  | 83 => 0x1443d1
  | 84 => 0x3ca
  | 85 => 0x3d455
  | 86 => 0x15d451
  | 87 => 0x1455d1
  | 88 => 0x15d455
  | 89 => 0xb8c
  | 90 => 0x14d6d1
  | 91 => 0x16d4d1
  | 92 => 0x14d6d5
  | 93 => 0x3d4d1
  | 94 => 0x14c3d1
  | 95 => 0x2cb
  | 96 => 0x14c3d5
  | 97 => 0xcd4d1
  | 98 => 0x14ccd1
  | 99 => 0x14ccd5
  | 100 => 0x15d4d1
  | 101 => 0x14d5d1
  | 102 => 0x14d5d5
  | 103 => 0x1714d1
  | 104 => 0x14d711
  | 105 => 0x2cc
  | 106 => 0x14d715
  | 107 => 0x17cb
  | 108 => 0x164c
  | 109 => 0xd0c
  | 110 => 0x9ce
  | 111 => 0x168e
  | 112 => 0x168b
  | 113 => 0x9ca
  | 114 => 0x9cb
  | 115 => 0x168a
  | 116 => 0x198b
  | 117 => 0xa4b
  | 118 => 0x21295
  | 119 => 0x44c
  | 120 => 0x198c
  | 121 => 0xa4c
  | 122 => 0x9cd
  | 123 => 0x168d
  | 124 => 0xa4d
  | 125 => 0x198d
  | 126 => 0x2cd
  | 127 => 0x2c9
  | 128 => 0xb1696
  | 129 => 0xb09d6
  | 130 => 0xb1396
  | 131 => 0xb0256
  | 132 => 0xb1496
  | 133 => 0x154996
  | 134 => 0x155716
  | 135 => 0x154d16
  | 136 => 0x5cb
  | 137 => 0xb49d6
  | 138 => 0x589
  | 139 => 0x1789
  | 140 => 0x1449d5
  | 141 => 0x145995
  | 142 => 0xa5455
  | 143 => 0x144a55
  | 144 => 0x199455
  | 145 => 0x1456d5
  | 146 => 0x144591
  | 147 => 0x184c
  | 148 => 0x16c056
  | 149 => 0x16c9d6
  | 150 => 0x16d416
  | 151 => 0x16d496
  | 152 => 0x3d296
  | 153 => 0x3c9d6
  | 154 => 0x3d456
  | 155 => 0x3cb16
  | 156 => 0x3d8d6
  | 157 => 0x3cd16
  | 158 => 0xcc9d6
  | 159 => 0x15d715
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1226
  | 6 => 2150
  | 5 => 1681
  | 4 => 38
  | 3 => 5
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/57+packedAt gbK8 (1716+(h % 57)*7) 7) % 66)
  | 7 => 2*((h/464+packedAt gbK7 (45362+(h % 464)*11) 11) % 1226)
  | 6 => 2*((h/765+packedAt gbK6 (103200+(h % 765)*12) 12) % 2150)
  | 5 => 2*((h/567+packedAt gbK5 (99179+(h % 567)*11) 11) % 1681)
  | 4 => 2*((h/33+packedAt gbK4 (2660+(h % 33)*6) 6) % 38)
  | 3 => 2*((h/8+packedAt gbK3 (405+(h % 8)*3) 3) % 5)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc0f01e07ffffffc1ffffffc18f703c07f1ff
  | 1 => 0xfff001ff8383e03fe0ff01fc6749fce394e73
  | 2 => 0xf07fffe0003fc003fff0ffe03878e1f3c18f9c
  | 3 => 0x7fffffffc00003ffff00003f80fe03fe0fe0
  | 4 => 0x7ffffffffffffc000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x948010020240428880991489008130140210a5
  | 1 => 0x94b010cc81a34115202a056823406ca194652
  | 2 => 0x20556720402e90227520cb409858c162c18b18
  | 3 => 0x8426ba571680004ba9cc01832d80fa016e0de0
  | 4 => 0x878cd99e537397010008204377e0003b5e000
  | 5 => 0xce000e018604218021880c183feffdbc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38875
namespace PEqualNP.Outside.L_meta_38875
open PEqualNP.Outside.L_meta_38875.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 15 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 68 := bs0_3_0
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
theorem bs0_4_768 : Interval s0Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 894 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384))) (concat (concat bs0_4_480 bs0_4_576) (concat bs0_4_672 (concat bs0_4_768 bs0_4_864))))
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
theorem bs0_5_768 : Interval s0Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 820 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 10 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 112 := (concat bs4_3_0 bs4_3_96)
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
theorem bs4_4_864 : Interval s4Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1345 := (concat (concat (concat bs4_4_0 (concat bs4_4_96 bs4_4_192)) (concat (concat bs4_4_288 bs4_4_384) (concat bs4_4_480 bs4_4_576))) (concat (concat (concat bs4_4_672 bs4_4_768) (concat bs4_4_864 bs4_4_960)) (concat (concat bs4_4_1056 bs4_4_1152) (concat bs4_4_1248 bs4_4_1344))))
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
theorem bs4_5_768 : Interval s4Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1017 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 (concat bs4_5_288 bs4_5_384))) (concat (concat bs4_5_480 (concat bs4_5_576 bs4_5_672)) (concat bs4_5_768 (concat bs4_5_864 bs4_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := bs4_6_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 38 := block_range (n:=38) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 38 := bgb_4_0
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1681 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)))) (concat (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152)) (concat (concat bgb_5_1248 bgb_5_1344) (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632)))))
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
theorem bgb_6_2112 : Interval gbAtlas 6 2112 38 := block_range (n:=38) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2150 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248)) (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536))) (concat (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)) (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112)))))
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
theorem bgb_7_1152 : Interval gbAtlas 7 1152 74 := block_range (n:=74) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1226 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 66 := block_range (n:=66) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8feeaece8feaae8a8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38875.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.and,[1,4]⟩,⟨.or,[0,6]⟩,⟨.and,[2,8]⟩,⟨.or,[0,3]⟩,⟨.or,[1,4]⟩,⟨.or,[7,8]⟩,⟨.or,[2,12]⟩,⟨.and,[10,13]⟩,⟨.and,[11,14]⟩,⟨.or,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38875

open PEqualNP.Outside.L_meta_38875 in
theorem PEqualNP.Outside.L_meta_38875 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4272613544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
