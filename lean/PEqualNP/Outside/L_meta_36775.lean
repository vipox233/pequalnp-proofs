import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36775.Model
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


end PEqualNP.Outside.L_meta_36775.Model

namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
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

def SBf (j : Nat) : Nat := [4, 6, 8, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36775

namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
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
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36775
namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3200c5000100c076904b024a19080bf42bd42df32dd32f621f521be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x400218d424cb4a8490f14c921
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
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
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s1K3 (84+((h/1+packedAt s1K3 (81+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f807ffe01fffc0f03f83f07ff07fe0289e7c
  | 3 => 0x3fff80fffe03fffffc003ff83ff83fff0e38f
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x808504022420480014584508450842a832cb5
  | 2 => 0x595534a651d4a915782aa2b46ab46b41a8965c
  | 3 => 0xa264a52a9491b234baa0432d232d239530c30a
  | 4 => 0x3346c6cd191923a6dcf36a0843ce71063d03e0
  | 5 => 0xc387070e1e1e3c38ef3c73ce720842183ef800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36775
namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c3eca3185d94630bea8c61f5518c2eaa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ee62887d0c510fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x1e0000c04e08e0531ea42a6f02e24e244841158501b83105d1d010e0044c1031108c42a8aa02240800000104000e98001920a14b8b84884f8588000003a4002263826f8000922940dcbc20407c9852c2371442f8000d2000380001f200054cc500040a3b8dc9180ea2d0310001c29503f1f3030788420a04d0a243ca8e18c0002f9633b4504068f62b69e8b38d1366798598ed2ec0011a9070967848f8ab0604543e2244f64a80006c402000000ad25a690000002de000b1240000000be00000071c0000041e1783019a24c2fcd916a04823d1e80004c8cc00207394904002190ec125328fd0003e9261403860009e0831f83dc670124ee0014923b3ae000ce935354600b709a0000000000052c30c001130287d40d00018419c00000000578c28000006d83ea1e0a4185360002cc000da9f10006c4001c54540011913f4d43acd40ae000000000000007f4001790000000024523c000000f8000000002663de27400000000000bf92b3a869cdfa3f4c0a00000570003943219502035c000d637a28cfc8000000cc8e8bc34094c00243000558740002ae745058000000009b8460000000013200062c0024a0b44b01799c16a698971934fa42c638471382586f9ff31c284f3a360360805e8d342e3ed0020c00e0550d1241027b8520941dea3d438dd04e8c0bd8294b487c37a7432805d089f71223210987435c8f82e96d52264832981000001468f50000004c90c068000d29cb4a26e0ec8002be874000003a4a20cb0000000e8aa000000070d0080100000000014010040203c030340000c020000c00400044110140900c04000130680304404008150042f00400018070000600405008080000500802018010000101000000070b800018080000109c0900400010070100f0540100803000070041600c000200101c020000903802030040080100000000030001c038000600102c070140002800000000380a00000000010040201c010080600c0002003004030040501c0502403000030000204c0301c08000030181f0000100402018040000000004008030080700401034020200300c02000010300b00c010400706c000040004c01014050000504800000030681305800044080000100801004020080401008000080400201c000280c02004bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857
  | 3 => 0x230188b4000000a20012d9060000000000014a4a0000002c04488889036e4cc278d95260b41aa830622a4298440003b0f58004bc9f90c0da0cc51c000001e64a4211381aa000cfa2519e120d8221000000350044c61b4c390a3baa10ba1cf11c5542a0f424068d4a8de4447f0738e41141393992f388464562850b02d8201084960b0a28cb4721e8f01861a800000000398688001d601e0000000027484809800528548001652e6660358c1260570000000006307f2780007e124800000000da08d00076c1c14d3808f0b21a152002c15800000000000004fe858a20562421b85b9e50e446cc49684361dc1ea50000908b084d26c819409ba00045c0010e2e400135a8612e934ef80000099c0128b0647549290119a000000002d27d1040f9000360880af452540b5a2e000000342594ae001460004de0fc002520002ec001340985f49e9de0fe544cf1992d89b84297739c50cc681f412084718001163980c8b943880cf42621b68e9231bb30600ccd80048e000001710004c527a2800000000182384410a413b03c49cad0000009c44a81644e720e695901400012a2c0e050910264000000b825541410c349463087900025f198771410094b80000000008a3c81c8051d4a28001e94287ecd68000000013915d2127c0070000000000014b1642788d14c2386a41b2694ba2c091a7c000018f608022c0000002a05c65c801ac0f6328388001fe000000000825d4ff25631e224ec0002925e8829581e09e4040e20000ed3a93929e644e327610c074a709f0002a0001901368d02d800000000000000006207880021a0f0d797e3929b51190f18a1646808c3da0000000009478d179fa0e618c000a7000808fb0003564501109303800107000490001068000000000000
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x153c82776154f209d18553c823e6414f208f59053c823e64947208f59251c825e63952209758e548827661152209d584548823e64d4e208f593538827661d4e209d587538823e6494e208f592538823f64546208f191518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614f204836451881209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c755153083586054c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420d654f3008279650c0209bd9520082e461480209ed9520082d863480209798c54c425d63153108fd9153c423c6454f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10b518d41c42b5640c710ad59221c425e63d52109758f548423e64d4e108f593538423e6494e108f592538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452443345490510d914a41442746550510b518d414436452505109d997314433454cc510d914b31442b5640c510cd1503144357530c510d914831442766588510ad592214436452885109d19521443645248510d914a104423d65950108f990540427661150108f993530423d64d4c109d987530423e6414c108f590530426e6214c109b588530423e64d48108f593520423e64148108f590520425e63148109758c520427661148109d597210433554c84109d59421043355408410cd553100427965840109dd9510043355444010b9189100427b6544010
  | 1 => 0x63f6550441a718d41106776550441b518d411066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc67a60152319e580548c63e6494a318f592528c69c644ca31b6181328c63f64542318f191508c63e649513197d8d544c67761551318f994544c73454cc531c7152314c63d6595031c718d540c73461550318f990540c71d54d0c3197594430c71d54cc831a7191320c71d544c831b5d85320c6d8604c831cd553410c79743d04319d594410c794431043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d5321cd58654c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c87576154f218f99053c863d6414f21cd95241c86d46350721cd95331c86b5640c721cd95031c8755530c7218f993538863d64d4e219e983538867960d4e218f990538863d6414e21cd5532188675619512197d8d544865c63551219ed81544867860551218fd91534863c6454d219dd85534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f59251086756590421b518d4108675650c421ad59031086e5620c421ad592210866f65484219dd95210863f64540218f191500865f63540219718d50086776154f409d18553d03576154f40d518553d031d5390f40c754c43d031d53d0b40ad58742d031d5350b40c754f41d029c6350740c754d41d02b46150e409dd8552902746154a40a758c429029d63d02408f994435025e63149409758c525023e65d0940ad587425023e65d0540a718d415023f6550c40ad185431023d6590840a758c421025f63544409718d51103576354440d518d51103374354440cd50d51103364254440cd109511023d6590440cd54641103355110440a758f401033551d00408fd95401033551500409ed95401031d54ccb30c755132cc2d8604cb309d987548c27561d5230c758e548c27661152309d584548c31e5490e30b5185438c29d640ca30cd952518c3355494630cd951518c3355454630c7952318c29d640c630c7950318c355510c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d641493097997324c2d8604c9308f990514c23d64145309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2d46150c308fd91520c23c64548309dd85520c274615483097596320c29d640c8308fd91510c23c6454430a7590310c2d9600c4308f992500c23d6494030a7593300c25f654c0309ed95300c27661953209d58654c825e63153209758c54c823f6454f208f19
  | 2 => 0xd38e370920000004d80016c000000d680037e5bca006607403c5e0002e27a4002050007140611d2f02610680000024c948003901b0c81330be0bc139fe306824000fc0000002a10e4027a0571eb000230a60003700010a07931c214bc8d433456c349e4000000001d31de2486b9740003a4240004044ec8f8333a44b43107e006000700f70586bc4c9d41708288b1ec00e0000005d0525784102e00a430000003947246d80027a1dc000000000209f93a2c0650790370001c4b31120004c49015c2fc2680018a2360000580042a658551ac17684868802000000888ca0007840005842e000000001ca0000020332a000000000005b8000002601bc339f541c1c8000000000589b8003385a4500000006a8001933304bc470001e0000000000000580101400000000000a0040301c0000c0000401004040000200403000010480200400000020080100c030000300000008030000000800008000040000402004030280800402000010080800c14000000040b0140000c0a01c01008010100100004000100000a00000004050080100c0400c0000800008000041200c000000402000000000000800001000000040100000000050000000400010040080500401004050000102c010100100808000060080000002008150080000801018030080002000008090040e00000000060000400000000010000801c01010020040000e776154a439d1855290e7661942439d5865090f574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310eb46150f4297d8d51d0a5c6354742d5d8d51d0b546354742cdd0d51d0b354354742ad5874290a5f63542429718d5090a3e65d0d42ad1854350a7661141429d5845050a776154c429d1855310b576154c42d51855310a3d6590c42c754e4310b1d5310c42c754f4210ab561d08428fd954210b1d53508429bd954210a7661153329d58454ccad46150f328fd9151cca3c64547328f99250cca3d64943329d98650cca7561943329d987548ca7561d52328f992518ca3d64946328fd91508ca3c64542328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132c758c544cb1c5490d3297195434cad46150d32cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d690c504cb594314132d68c8504ca3d65950328f990540ca5e6315032c7553320ca5f654c832c7551320cad8604c8329bd95320cab46150f41a758c42d065e6394a419758e52906b561d0a4197d8d509065c63542418f997435071c53d0d41c714d43506b46150d41c714e425063e6510941a758c425071c5310941d514f415071c53905418f59643106b561d08418fd95421
  | 3 => 0x65196690679590645c00001f0006d80004d1160000008130250c600003f440411a0441e000840001742cc560ee258144d58c3324000000341a01800009b24e110000000000707382b05400006800000000000000006dc8f1020ac414000552a22a0000000000f0e09030ea000c586b000000001b10001700009707e548000e6000324000a40005f44a000000000000001d05b4d380022a700000000ec0d80008d000000000000444b90c0d200073c000b13b038cdc8c700000000000000140c69320003c40a8000005a02d8000007400000000082c00000014630000003ac3fce718f000000a48f30007f00d896032000ed9ef000000000002a60001f0001c800090800042000001bc3e85046c0000001782b90026866c911351f62e4be0102c85a8248d63d4298d02072e6464a800633e6ec5b84f3840006f8831ec000001a2000000239da120000000000003f4000000000000890f1446d0f10000000003e8002aa61c000000000f400000000000668002340005a80013e000000000003d08500013a5e800000000674001452ca0c438139220000b1042000000000004261e8001be1fc30400000000000f30950001ec950eb03a0006f1e024641000189000000ef0000000000c0f80000000000000078c5b14e000000000000000000000400023c001463dc000440000000001d9f70501d10416b32200000000000618001f320e000001ba0c80000018819c0003407f00070c000200005c85e9583f6000000590c6000cc9260008440a000000734000cc034858c28a1122000a69a6278000001dc048004a100032e000000000000002d1c423000000109000000001d5000098000000000000011700000000000000000000002ce000000ad27c2108980018c00000000000494000000000000000000060000000296000438002b4000000000007e4001bd0000000021a000000000003660000000014e00000000000000000ec02400000000000000000003080009c1b000000000043146118d90bf18472c0f0002ba434000000002f800210000000000ab3da774699f6000000098c4000000001560000000002d000000d400001c000f80000007300019e000000c10000003846d00000000000017000374f8800000000578000000e0e30000001a8250b2000094940b02885d4000003fe7e0271a90da000400fa0000003714a0a6000001e520c1e0398c8000550b18000c20002589c1b2800200ed000354448002fe6d42900035c7c80017700000000000000000af8c500000000000082000000003420d41c8003b20008a04c00000000030152818710001ea42c4311c1683e40009e28e69400161000000000003a20000000000055c0008a3ae2940000900077cbb0000004acf38ea0f8000000004185eca7a19346520229f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x3475022d520001600414040060901344600e5d204000000a0cc3c000080506200001451c55310c42c2aa6b0e84215147158c544caa838a862826586550604c832928e6b0e8420e1463185540c60e3b2a89906386550604c831a28e6b0ca990c357695031c868a38aa621e818554d61d0b40a2ae6212a22051473544411030ab1aa3a008186550604cb30a28e2b1ca91841d76950318c28a39ac22a2219118c525051086aec2a06288625641483144312b20a510a21895506244010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x65008148754d61d08428148754d61d0b40814865cc42544408148758d51d0040
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20138+((h/221+packedAt s2K5 (17928+(h % 221)*10) 10) % 876)*11) 11
  | 4 => packedAt s2K4 (22272+((h/179+packedAt s2K4 (20482+(h % 179)*10) 10) % 946)*11) 11
  | 3 => packedAt s2K3 (1273+((h/8+packedAt s2K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s2K2 (243+((h/1+packedAt s2K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xff80fff80fff83fe0fc0ffe0ffc3fe0363ce7c
  | 3 => 0xfffffffff03ffffff000fffffffc1fff83ff8f
  | 4 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x290a22312209208052c92909280532a82e10b5
  | 1 => 0x43266450e492259605585b285a43541962c65c
  | 3 => 0x8414888241a4422aa020945294a80952816b0a
  | 4 => 0x1658d12489074b4d39b20610e7328063d40de0
  | 5 => 0x1860e1c70e3873f1ce3ce79c06231183fbb000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee00ee88aa00eeaaee00ee88aa00eeaaee00ee88aa00eeaaee00ee88aa00eeaaee00ee88aa00eeaaee00ee88aa00eeaaee00ee88aa00eeaaee00ee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36775
namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x3a9400029f0030008285c00148ac0212c00509269802846a8ca5009c70020000002a3c00000b41a2161800258446980878e9c2468d8108b049207002041140102ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd801418400781d4444049000008495656c3c880c9c24000150010d28000000002cb534002120a449191558ac7098000000e500f189795c00dcc068305ce83960506408d5397d3c0000b8c800101800002854ec00e000fd247568f9314c5880a0607d74157000cd1d0401118000c400b08d546d08f44cbc004034a800d12d480202140c0c0c00020206400002021a00000602100018040000060c0e10060c14057b5050ef0a0a1dd94742baa8e855e5310abaa6214fd51329e2a26577514cae8a2995ed4132bc282653e540ca7aa8194f943419eaa483b75150678a0a0cf950419f2a4633d548c6f4a118de542319f2a0633d540c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af29e815d53d027aa3204f94240afa9a815c53502eca2205d54440db288813d511036aa2204d544409f28081ba501027ca9984f55330dc206619f418c33a83185794230cf204619c408c27ea8984f15130dc200619f410c33a82185794030ed28061db400c33c80186710030ec2006198400c27ca9904f55320af29e415d53c83b061904fd51209e2a2415f53482b8a6905dd4520ba28a41d8300827ca9884f55310af29e215d53c436a83884fd52109e2a421d8308427ea8884f15110afa9a215c53442dea4885b14910daa0a21d8304427ca8084f55010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8c012000188a0400052479602602028e69c41800088000000108008302586054c42cc50550086b16110330a5584408c2b16110030a6181410c29a6090030a5584400c2d16110030e4984400c2996110030e4584400c29161100308d58654c831a540c320c615030842346550510c91494144318540c110d21483044391410c110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1085117195030c82883aa8218221c0149410c110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (826+((h/15+packedAt s3K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s3K4 (2937+((h/33+packedAt s3K4 (2673+(h % 33)*8) 8) % 130)*8) 8
  | 3 => packedAt s3K3 (840+((h/7+packedAt s3K3 (798+(h % 7)*6) 6) % 33)*6) 6
  | 2 => packedAt s3K2 (149+((h/1+packedAt s3K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc07ffc07ffff0383fffff81ff83ffe00fe73fc
  | 1 => 0xff81fff81ffffffc0fc0ffe0ffc3ffff638c7f
  | 2 => 0xffffffffe07ffffff000fffffffc1fff83ff8f
  | 4 => 0x1ffffff8003ffffff0000ffffe003fc0ff0
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x530c447145122480b2c93909380532182e31bc
  | 1 => 0x8524c890c824619405584b284a4354a9628455
  | 2 => 0xa111122034882295020945294a80952815a8a
  | 4 => 0x2c59a244920ecb4e69b20610e7328063d40f60
  | 5 => 0x3061c3871c70f3f38e3ce79c06231183fbe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0eaeae0e0e8e8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36775
namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2126119001801d2000b95102a3cb06127071b020129e16895a72815c2d480de35001d63330f8fb76035fb65ee5a1722a40190420000000130000c519d00f5d8a5068012000a08203000000128082010aa804400c0105bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 3 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36775
namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8435e53086faa610f754c21aea98437c53086fca410fbd0821f621043ee32087da6410df94421fba0843f441087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d02fca3a05f54740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c52502fea2a05f14540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa41877cc830ee990617e510c3eca2185d94430bea8861f5510c2eaa218778c430ee188617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f719641ed32c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f719241ed32482fea2905f14520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53906faa720efd0e41dea1c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331bf29663ee52cc6dca598df54b31f6a96636d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef42887d88510fb8ca21f6994437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef29
  | 2 => 0x200374f699c0960bc000b04b25d8220b921c4200013710e0a4cd8e906e000768001100649007916a000021320400005a14b000000e200017a7b000000048000000000007cc000df1666441e97b1025f0de0bf3cc1c42820225e7c0891700ce528181d142281076117038000000ca000001139fc0001f400000000924570003ba2a8f38c91de858e61461c25e53216d308000fc9562482912b2140a44f40300a11c3fd220002c67d40004a3d26fcf080000050cb58001ca56ca20000008cc0003841e980001f626220cc597341023c240cd250000ce89134e728850561502ac201a222839c7c86b26c3a8c312336675c3b251454248c412211285ce080c1361fc9725b30e0fcf119e0dc01c6a8d407c7bcd600d1a063c002221701909d80003c1ec002134a030400035258000e3800000229029940000000880e21e9941120b126000002571903451c8630000200021d000000ad25402660ce10002fe0000000035e268be83b2d0000eda5512a000369923ac494000003421947d070218838c69161305343a2122a21a06b00518a8601601a47a08d3085d04c86c4c8001ae000a393e2b2998e900045a0b8461b23c0591211d50c01f10014c030560fe9d446c434c8000330368002103f05e85e1b02020a0b29bd406638002240007684597423a0e8f200027817c0012b0002008287a36e1389c0f44ba3c0e289f2a07ec3f1574806e8d00003d474c228a30028046e1b13965390f904300424548690008d0fb96a19c000000322540009816c000000e80de1867fc000002687e8ae8d20360090c8fe0921e000000000000ae0000000006c89d14e3b80006a0669682a80002c9146604c32633cb380002e5780024f3803d8000e44868c4d2181350000000002be000dda1a4766e06000000000c002062d2580c623a238468001de0825200f80000097c52a4639c001178e333e4e92f0fc08e524309be2aa0012700000031c89800000198db0e644c88c390d317c91c210a2372084219fe3048713382a01e8300001c0000a00405094030400300c07000010000503405020000540201004030030400200403004000000601c030001a008000040e004120281109400000090040100c1b07c02000230080400002000000080100414000000340a0000a0002f01c0000c0802c1b010010d4070000500019098010240f0080100400018000080302c06004000100700c0e00c08028000000500000010090380001401004010000303803000020000600400000000040901801000170000b004080100001c0300c090000100011000010040101005024000080102c0d01c030000d000010040100c0500403028010340b00400014080040702405018000001600004028150040e05419bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x1d947c934881e303a8dc5d0000008a0000000009289380022a000001772a81cc4212d26638000000000050000002cc724000002fc000048000000005b000242000410a03523cc0000038665c001a515e3c510800232664090103903e0810150001691483624c988d6a35000000f88250ee6d1319cf0001602b91f1b058506a2b4a60001690610a46ce311e0006acca8004a402c0022c1640001a00000058800054272278000004600002d9a6000615190000000e4bc00049642cf42380a20c4fa0db25200027941000000000002e20000010700000056189000000000591760000006f000880b70000000010500009a0000000014c3ac65a5c2a668ca11aa1384fc4a05e0002587b9752220007e80047e3082e1dc16e81c001402a4000f71e545c6282993518c460a28004121b0568c436a2340021e3be000000001e46b80019a08c5c9128001d07ac000000009304b8004900f0000863b00003aa41056734a7a58000388000b1206188cb16f478240000a10007c8000f504e3ed0a8
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x7435031c53d0d40c714d43502b86050d40d614f405031c53901408f59643102ad6210c40ad185421026f62544409b18951103355110440ae580411023f6550040a718d401027b6550040b618d401026e62153309b58854cc2cd6210e308f992528c23d6494a308fd91518c23c64546309bd89518c26c62546308f992544c25f63551309ed81544c23e6515130ce153304c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c6355030ce181540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b3588430c32e5494830cb552520c32e5454830cb551520c31d54cc830b6583320c31d544c830d3949320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3573254430d54c9510c355518c430b6580310c33954d0030e6d0f400c2796510030e610c400c25f654c030a7191300c27b654c030ae191300c25e63d53209758f54c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c834e6294f20c795153c831d5454f208f99053c823d6414f20cb55232c832d544cb20d394d32c827661d52209d587548823e6414e208f59053882766114e209d58453882e9600862097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b195324825e63150209758c540827661150209d584540823e6414c208f590530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208fd91510823c6454420d9544210826f65480209ed95200825e63d53109758f54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6414b108f59052c425e6314b109758c52c426e62d52109b58b548423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da5805244354538c5109d195314436852881109e195204425e63150109758c540426e62150109b588540423e6414c108f590530426e6214c109b58853042766114c108f990520423d64148109798c520425d63148109e980520427965840109dd95100427b6544010
  | 1 => 0x7018000000028082c00070440c00018040a03058000e0e07808160005858120201818181300800120307888021f020140200030003e0f038100a0807014080000874020108034020e03008080e0180812049bd8951d0e6c6254743d6d0c5050f3a43141438fd954310eb86050c4397d954310ed86050c43cbd0d5210f4e4354843cb50d5210f4d4354843ae18143d0a5f63543429718d50d0ab86050d42cdd0c5150b354314542d9d085150b364214542c754f4210b4d53908428fd954210b1d5350842ad1854210a6f6550842d354d4210ae461508429d98754cca7561d5332b618143cca3f64543328f19150cca7a60d52329e583548cae46150a328fd91518ca3c64546329dd85544ca7461551329ed81544ca78605513297195434cad86050d329b195424cb8d4350932b9185424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320cab46150b419b98a539066d6294e41c794d43906b86050e41a758c429065e63149419758c525074e6314941d358c525063e65d0941cb14b425072c5250941ad185425076452d0541cb14a41506b86050c418f596421069d63108418fd9541106ac62504419dd9541106e4625044197d8d501065c63540419b98b54cc66d62d53319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b31c755332cc71d544cb31d394932cc67a60d52319e583548c66f62551319b189544c67b60551319e181544c63e64149318f590524c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863e6414f218f59053c863e6494e218f59253886cd6310a218fd91508863c645422197d8d508865c63542218f992544866f62551219dd85544863e65151218f992534863d6494d219b58a534863f6454d218f191534867b6054d219e181534873454c8521cb152214865e63d50219758f540867a60d50219e583540863d6595021cb189540873461550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cb553420866d6510821b358c420866d658c821cb55232086e5618c821cb551320874e534c821cd55341087a742d04219d59441087a442104219bd9521086ac64484219dd9521086b46448421ce95250087395494021d694e50087595394021ce95150087395454021d694d50087595354021da8c950087693254021ae18143d02ad6210e409798e529025d6394a40cb94942902b46150a409b988535026d6214d40d3988535034d6214d408f99
  | 2 => 0xa129cb1ae0b019ca209c268bc519668b94a27ae2260000e8c4a3a72bc216001f055800000de320007f33860818b22d0a02427b24ec6908660ee002ae0510a002783000020ada0016c120225c80074800478023a00032a0e0802e0024a7b9c0911385724c6e800ada5a000e28e03413800001b203a104daa41127c96214b602499a2276b024d000c00ac0a000000002404c00000c281e2a84636a044a152001bc688001d1f62cae6600fa61ade89afe31900af25c9b0561b0886399046ae48a0e0002001ca0200000001b63b25400178b5916000a4000ce002a6a821a1f150b2800a6af84494e7e8002886a5f9f89423466a06ad000caaa8002ee879aa0026e16904002f400212000000019461248bb00075992872ba0692c2e224001e07d00079aac88000a7a3200000cb1ca00000c330e9ea766b80000124752d24e8700b01017240bcb16cb92602000bd8f0a2a3a0ca74000ba258dcc8336a315a0f8f2101fe5532495a0c1f80067ad430b182c0f68b1dc430009f91000000b38005d0007400000304249e8ac000000003d102978d0002c40c170001c4030fc1913015298658ea1812e2f8840031c00262000000006e00264c498acd1a401268358007892a00000cc1be6c1180004aa418c9c05235162188cc298e421800b720a7916e018fe160b42392073aa2c781c6207a2d9a6a514020148142fc71876cca3e7600082132512be1790e4fae8b30e6b09c2048a0c980a00078a0894aca2a109cc681b4c8a30be826a4964509b8948164f310ba97a41b140d88a6b3083e32857a608f0007cb062a2465a968450664717c5802a2b8d85d8680e08c34922ce9a800296562360003caa9c8779ea532869aab8860160c020001600028240002000302a0000804002105814000001804200b0200802001083c02150400400040280000020903402000303404140580802020c81424080580016010280c080
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x730d0000010000005c001855318f00000040000b01638524a5040c2200012440000003920080014a1c14354843a90e0a1aa421d307050c5150b0aa98c2a10859154c6150842b10e0a1a849968543185424ca86b94a6a1c838694c6050e41a1ae629284a0d0d731895408712310c2aa043291d1618c821b0ae62108210d0d739494290313290c2a1481435c85350d40a48e4a888220498735804110286b90c6aa0618618c6055030930e8b06641849874580310c2c4b908620061491d15108420
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2406080000a808050c6150932a098294c6050e41a05831886155021a05839486150a40a098218c6055030
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 814)*11) 11
  | 4 => packedAt s5K4 (16974+((h/138+packedAt s5K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fff81fffff841ff87fc3ff87fffc0233f3fc
  | 1 => 0xfc1fffe07e1fffe0ff87fc3ff8701ffdcc7ccf
  | 2 => 0xffe0ffff801fffff0007ffc7ff801ffe0f8f0f
  | 3 => 0xffffffe007fffff80007ffffe007f00ff0
  | 4 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x984208c5140408052809c0498094c43011b15c
  | 1 => 0x29441143202900a05882441288214950c454c5
  | 2 => 0x508aa2880d52454b0444aa85550292a60a8b0a
  | 3 => 0x6294c4124903567295502206664b00c7600ea0
  | 4 => 0x8318871c719c679ce6673320440c0307bf6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0eee8eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36775
namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54027f55007fc54027fd4c05fe53027f54c05fc5301ffd0c05fe43007f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803fe4200ff50803fc4200ffcc803fe3200ff4c803fc32027fd4409fe51027f54409fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc3100ffc8403fe2100ff48403fc21027fd4009fe50027f54009fc5001ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x4200aff48210057f2410802bfc208400bff8842000fdc421002ff6210803bff654401d7fb2a2000dfd9510004feca8803bfe65440097f32a200eff59510075faca8803bfc65440097e32a200edf19510024f8ca88003ff64440017fb222000efd91100057ec888037fe64440077f3222000ff59110005fac888037fc64440077e3222000ef1911001d78c88803bff544401bff2a2200eff5511006ff8a888003ff63440017fb1a2000f7d8d10005bec688033fe63440057f31a2000ff58d10005fac688033fc63440057e31a2000f718d10015b8c68803bff5344019ff29a200eff54d10067f8a688037ff4344019ff21a2000ff50d10067f8868802fff62440177fb122000fbd8910005dec48802ffe62440037f312200bff5891005dfac48802ffc62440037e312200bfb1891000dd8c48802fff5244017ff292200bff5491005ff8a48802fff4244017ff212200bff5091005ff8848802fff3244017ff192200bff4c91005ff8648803bff514400bff28a200efd94510077faa28803bf5514400bfe28a200dffd051002ffc8288003fd414400bfe20a200cffcc51002ffc6288003f63144001fe98a2000fd4c51002ff8628802fff214400bff10a200bff4851002ff8428803bff504401dff282200eff54110077f8a088037ff4044001ff2022000ff5011006ff88088033ff3044001ff1822000ff4c110067f8608802fff2044017ff102200bfe8811005ffa408802ff92044017fe1022005ffc411002ff62088003fe1044001fb0822005ffd941002dfeca08017fe65040097f3282005df99410024fcca08017fd65040137eb282005df59410004faca08017fc650400b7e3282005ffd901002dfec808017fe64040077f3202005ff59010005fac808017fc640400b7e3202009ffd5010047fca808027fd5404011fe2a02005ffd8c1002dfec608017fe63040057f3182005ff58c10005fac608017fc630400b7e3182009ffd4c1003ffca608027fd530400ffe2982008ffd0c1003ffc8608003fd430400ffe2182005ffd881002dfec408017fe62040037f3102005ff58810035fac408017fc620400b7e3102006ffd4810037fca40801bfd520400dfe2902006ffd0810037fc840801bfd420400dfe2102006ffcc810037fc640801bfd320400dfe1902005bf9841002ffea208017fe510400bfea882005ff1441002ffe8208017fe410400bfea082005ff1041002ffe6208017fe310400bfe9882005ff0c41002ffe4208017fe210400bfe9082005ff08410055fcc008027ff5004013ff2802009ff5401004ff8a008023ff4004001ff2002000ff50010047f8800801fff3004001ff1802000ff4c01003ff8600801bff200400dff1002006ff48010037f84008017ff100400bfb8802005ff8401002ff42008017fd1004001fa8802005fe44010
  | 1 => 0x2ff614c001ff30a6000ff58530007f8c298016fc614c031ffa8a6018ff945300c7faa298063fc514c02fffa0a6000ff90530007fa829805ffc414c005ff98a6002ff8c530017fa629800bfc314c02dff90a6016ff885300b7fa429805bfc214c0057fb026018ffd41300c7fca098063fd504c031fe2826017ffd0130007fc8098003fd404c02ffe2026002ffcc130017f6609800bfe304c001ef1826002ff0c130017b8609800bf8304c02dff9026016ff881300b7fa409805bfc204c00bffb2e2005bfd971002ffccb88012fe65c400bfeb2e2015bf5971002ff8cb88016fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb262000bf5931002ff8c988016fc64c402bffaa62014ff953100affaa988053fc54c400bffb1e2005bfd8f1002ffcc78800afe63c400bfeb1e2000bf58f1002ff8c788016fc63c402bffa9e2013ff94f100affaa78804ffc53c4029ffa1e2013ff90f10007fa878804ffc43c400bffb162005bfd8b1002ffcc588006fe62c400bfeb162012bf58b1002ff8c588016fc62c4025ffa962012ff94b10097faa58804bfc52c4025ffa162012ff90b10097fa858804bfc42c4025ff9962012ff8cb10097fa658804bfc32c400bffa8e2005ff9471002feca388017fd51c402bfaa8e2005ff1471002ffe8388017fe41c400bfea0e2005ff1071002ffe6388017fe31c400bfb18e2005ff4c710007ea6388017fc31c400bff90e2005ff8871002ffa4388017fc21c402bffa862015ff943100affaa188057fc50c4029ffa062000ff90310007fa8188053fc40c4027ff9862000ff8c310007fa618804ffc30c4025ff9062012ff88310097fa418804bfc20c4023ffb2c2011bfd961008ffccb08012fe6584023feb2c2011bf5961008ff8cb08012fc6584001ffb242000bfd9210087fcc90800efe6484001feb242000bf59210087f8c90800efc6484023ffaa42010ff9521008ffaa908043fc5484001ffb1c2000bfd8e1007ffcc70800afe6384001feb1c2000bf58e1007ff8c70800afc6384023ffa9c200fff94e1008ffaa70803ffc5384021ffa1c200fff90e10007fa870803ffc4384015ffb14200abfd8a10057fcc508006fe6284015feb14200abf58a10057f8c508006fc6284015ffa94200aff94a10057faa50802bfc5284015ffa14200aff90a10057fa850802bfc4284015ff994200aff8ca10057fa650802bfc32840177eb0c2011ffd461002ffca308047fd518400bfe28c2010ffd061002ffc8308003fd418400bfe20c200fffcc61002ffc6308003fd318400bfe18c200affc861002ffc430802bfd218400bfe10c2005bf9821008ffea108047fe5084023fea842011ff14210087fe8108003fe4084001fea042010ff1021007ffe6108003fe3084001fe984200fff0c210057fe410802bfe2084015fd1
  | 2 => 0x400f7fea6a0077fe535003dfea9a801dff14d4001ffe86a000fbf4350007ff21a8003ff50d400077a86a000ffc4350039ffb12801cbfd89400e7fcc4a0006fe6250039feb12801cbf589400e7f8c4a0006fc6250039ffa92801cff949400e7faa4a0073fc5250007ffa128003ff9094001ffa84a000ffc4250039ff992801cff8c9400e7fa64a0073fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8005bf185400f7fea2a007bfe515003dfea8a801eff1454001ffe82a000ffe4150007fea0a8003ff105400effe62a0003fe3150001fe98a801dff0c5400e7fe42a0073fe2150039fe90a801cff0854001dfec0a007bff505003dff282801eff541400f7f8a0a000fff4050007fda028003ff901400077c80a000ffc4050007de2028003fe101400effe60a0077fc3050039ff902801cff881400e7fa40a0073fc2050037ffb2c601bbfd96300dffccb18012fe658c037feb2c601bbf596300dff8cb18012fc658c001ffb246000bfd92300d7fcc91800efe648c001feb246000bf592300d7f8c91800efc648c037ffaa4601aff952300dffaa91806bfc548c0057eb1c6002ffd4e30017fca71800bfd538c005fe29c6002ffd0e30017fc871800bfd438c005fe21c6019ffd8a300cdfec518067fe628c0037f3146019ff58a300cdfac518067fc628c0037e3146019ffd4a300cffca518067fd528c033fe2946019ffd0a300cffc8518067fd428c033fe2146002ffcca30017be651800bfe328c005fe9946019f74ca30017f86518003ff618c001ff30c6005bf98630007fac318002fd618c001fe30c601bffd46300dffca31806ffd518c037fe28c601affd0630007fc8318003fd418c035fe20c6002ffcc630017fc6318003de318c005fe98c6002ff0c630017b86318067ff218c033ff10c6019ff486300cff8431800afe608c037ffa84601bff942300dffaa11806ffc508c035ffa046000ff90230007fa811806bfc408c005ff9846002f7cc230017f6611800bfc308c005fc1846019ffc82300cffc4118067fd208c033fe1046018ffd95300c5feca980037f654c0013fb2a6018ff99530025fcca98063fd654c0317eb2a6018ff19530025f8ca980637c654c0093e32a6000ffd9130005fec898003bf644c0015fb226017ff9913001dfcc898003fd644c0017eb226017ff1913001df8c898003bc644c0075e3226018ffd51300bffca898063fd544c02ffe2a26002bfd8d30017fea69800bfe534c005fea9a6002ff14d30017fe869800bfe434c005fea1a6002ff10d300b7fec49805aff624c02dff3126001bf989300b7fac49805afd624c02dfe3126001bf189300b7fea49805bfe524c02dfea926016ff149300b7fe849805bfe424c02dfea126016ff10930017fe649800bfe324c005fe9926002ff0c930007fec29800
  | 3 => 0xfb046205ff98231005fcc118817fd608c4017eb046205ff1823113ffea11889ffe508c44ffea846227ff14231137fe811889bfc408c405ff9846202ff0c231017b86118897ff208c44bff1046225ff4823112ff84118893ff654c4497fb2a6224ff99531025fcca98893fd654c4497eb2a6224ff19531025f8ca98803ff644c4017fb226223ff9913101dfcc898803fd644c4017eb226223ff1913101df8c898893ff544c447ff2a26224ff5513111ff8a898816ff634c405ffa9a6202ff94d31017faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c445ffb126222bfd8931117fcc498806fe624c445feb126222bf58931117f8c498806fc624c445ffa926222ff94931117faa49888bfc524c445ffa126222ff90931117fa849888bfc424c405ff9926202f7cc931017fc649880bfd324c445ee9926202ff0c931015fec298893ff514c40bff28a6224ff5453102ff8a29888fff414c40bff20a6200ff5053102ff8829880bff314c405fb98a6205ff8c53102fbc6298817fc314c40bee18a6202fd0c531117fe4298817fe214c445fe90a6205ff08531007fec098802ff604c401ff3026200ff58131007f8c098802fc604c449ffa826224ff94131127faa098893fc504c447ffa026223ff10131017fe609880bfc304c445ff9026222ff88131117fa409888bfc204c443ffb2c8021bfd964010ffccb20012fe6590043feb2c8021bf5964010ff8cb20012fc65900077eb248003ffd524001ffca92000fbe5490007feaa48021ef5524001ff8a920003ff6390041ff31c8002bf98e40007fac720002fd6390041fe31c8002bf18e4010ffea720083fe5390043fea9c8020ff14e4001ffe872000ffe4390041df21c8003ff50e4001ff8872000fbc439003fffb14801fbfd8a400fffcc520006fe629003ffeb14801fbf58a400fff8c520006fc629003fffa94801fff94a400fffaa52007ffc5290007ffa148003efd0a4001ffc852000ffd429003fdea148003ff10a400fffe652007ffe329003ffe994801fff0ca40007fec320003fe619000b7f30c8000ff58640005fac320003fc6190043ffa8c8021ff9464010ffaa320087fc5190007ffa0c8003ff906400077c832000ffd4190007fe20c8003ef10640107fe6320003fe3190001fe98c8020ff0c6400fffe432007ffe219003ffe90c801fff0864001dfcc120087ff5090043ff2848021ff5424010ff8a12000fff4090007dfa048003fed024001ff8812000ff84090041ff9848020ff0c2400fffe412007ffe209003ffe904801fff082400f7fecaa007aff655003dff32a8004bf995400f7facaa007afd655003dfe32a8004bf1954001dfec8a000fff5450007ff2a28003ff5514001ff8a8a0003ff63500017fb1a801dff98d40015fcc6a0003fd635003bfe31a8002bf18d
  | 4 => 0x8b3fe539045bfea9c822cff14e4101ffe872080fbf4390407ff21c8203ff50e410077a872080ffc439040bffb148205bfd8a4102ffcc520806fe629040bfeb14822bbf58a4102ff8c520816fc6290457ffa94822bff94a4115ffaa5208affc5290407ffa148203ff90a4101ffa852080ffc4290457ff994822bff8ca4115ffa65208affc329040b7f30c8205ffd464102ffca320817fd519040bfe28c8205ffd064102f7e832080ff7419040bfe20c8205fd1064102ffe6320817fc319040bff90c8205ff8864102ffa4320817fc219040bffb048205ff98241005fcc120817fd60904017eb048205ff1824116ffea1208b7fe509045bfea84822dff1424101ffe812080ffc4090407de204822cffcc241167f861208afff2090457ff104822bff4824115ff841208abff65504557fb2a822aff99541025fccaa08abfd65504557eb2a822aff19541025f8caa0816ff6450407ffaa28203ff9514101ffaa8a080ffc5450401ffb1a8200bfd8d4114ffcc6a080afe6350401feb1a8229ff18d41015f8c6a08abff5350453ff29a822aff54d4114ff8a6a080fff4350407ff21a8203ff50d4101ff886a08a3ff62504517fb128228ff9894100dfcc4a08a3fd62504517eb128228ff1894100df8c4a08a3ff5250451ff2928228ff54941147f8a4a080fff4250407dfa128203ff9094101ffa84a08a3bd4250407fe2128228ffcc941147fc64a08a3fd3250451fe1928203bfd8541157fea2a0817fe5150455fea8a8205ff1454101ffe82a080ff7415040bff20a8205ef9054102ff882a0817bc4150407fa20a8229ffcc54102ff862a08a3ff215040bff10a8228ff4854102ff842a0803ff60504017fb028200ff98141007fac0a0803fc60504017e302822affd4141157fca0a08abfd5050455fe2828203ffd014101ff880a08a7ff3050453fe1828228ffc8141147fc40a08a3fd2050451fe1028205ffd963102dfecb18817fe658c4097f32c6205df99631024fccb18817fd658c44f7eb2c6205df59631004facb18817fc658c40b7e32c6205ffd923102dfec918817fe648c4077f3246205ff59231005fac918817fc648c40b7e3246227ffd5231137fca91889ffd548c44dfe2a46202bf58e31017fea71880bfe538c405fea9c6202ff14e31017fe871880bfe438c405fea1c6202ff10e3102ffec518816ff628c40bff3146201bf98a3102ffac518896fd628c40bfe3146205bf18a3112ffea518897fe528c44bfea946225ff14a3112ffe8518897fe428c44bfea146225ff10a31017fe651880bfe328c405fe9946202ff0ca3102dfcc318817ff518c40bff28c6205ff5463102ff8a318817ff418c40bff20c6205ff5063102ff88318817ff318c40bef98c6202fdcc63102ff86318817f4318c40bff90c6205ff8863102ffa4318817fc218c40bf
  | 5 => 0xc00000e00400000000a00400001600400000800a00400c00001800201600000000000000a01600000000400000800000000000000600000000c00a00000000e00000200600200e00200400a00000000000000600e00000800000200200801200800000000200201000600400a00800000000c00000000000400c00200600000200000000400000200000400200200400000000000000800400000400000600e00001400000800200600801c00001600600200400000200000000200200600200200000800000c00600200800800000000000000600800000c00800000800000200a00800600000000200600800200202e00002800200e00200800a01400000600c00200000000200600000400000601400400400200200600000201200200600200200000000e01400801c00000800a00000800000000800000400000000000000200400200400800400000600200000200600a00000400400000000001000400000001800800000000200600600000a00200a00600a00400200200000000000000000400600000e00400400000000000200600000600400200200400401000200200400000200000400400000600000000000001400000400000001200600e00000400002000000000400200600400a00200200200200001600000000000600200600400e00000000000200000200600000000000000801400000000a0060000040002fffd954317dfecaa18bffe6550c097f32a862fff5954317dfacaa18bffc6550c097e32a8602bfd914301ffea8a180ffe5450c07df2a28603ff5514317f7aa8a180ffc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d4301fbe86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c5dffb12862ebfd8943177fcc4a1806fe6250c5dfeb12862ebf58943177f8c4a1806fc6250c5dffa92862eff94943177faa4a18bbfc5250c07ffa128603efd094301ffc84a180ffd4250c5ddea128603ff10943017fe64a180bdf3250c05ff1928602ff4c943177ba64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8605bf1854317ffea2a18bffe5150c5ffea8a862fff1454301ffe82a180ffc4150c07de20a8602ffcc543017f862a18bbff2150c5dff10a862eff48543177f842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c017e302862fffd414317ffca0a18bffd5050c5ffe2828603ffd014301f7e80a180ffc4050c05ff9828602ff0c143177fe40a18bbfe2050c5dfe902862eff0814302ffecb20816ff659040bff32c8204bf9964102ffacb208b6fd659040bfe32c8205bf1964101dfac92080fff5490407ff2a48203ff5524101ff8a920817ff639040bff31c8202bf98e4102ffac720802fd639040bfe31c8205bf18e4116ffea720
  | 6 => 0x105ccd004ca140004c0000fa40000000000008140000000010e8000001044514f484bc8e0c307fc4fc5c492c8bc6086fce0c4100000000000000000000009104190acdac000000e1c0000000004ac0000000000000000000000001910b40000001f8304cc4c78120000d3059067c8ac0000002c129c000f3000125c00000000006c000ac9268f40c88000ee4000000fec000bf835c6f4f00aac0000000008c400000000016c00000000000091c000f84f0c00005c0d8bf0934000000f08230dd0cb00001f00000000000000002ac0000000001b800000000011919000000000093c000064e346901041cc3c823c4680290c474c1c80005ec000000000ed86780000a403c00000106c7740012fcdb0488f8c038960a280007b88b8c2c7849440000000000f0000450000000ba8000000000000d1c0006204a40dc000b6c000014c70000b785a8718001088338ce42443780000000000012c800015c000000000000fc84c80ac000f7883880c00118d2a800000000000000050c4c4000908000cec000000d55248000000de4000000000aa0000fb80000005a4fd40000003bc9000000011a80002340004606010ec0000000000000003c4cd4a8c0000000008488fcd580000985fc545070ebca00810000480000510000000000a08268000000000d4c0000000011f400000123cddc000e812bc320b04860d983e80d01c4000000d50000c64dd41a11fc564da8000000e2012cc24000000bec7a112c0347a8000000da5184cc92040180002c9278001090bb80000000000010a46880008d462cfccd640012145352c40012ac5b8c04928370000000ef000000000000000000046c000ab80007b400000000044c000c54000000000000e2800076c000d683b4414000d24d089a50103140000000000000006bc90400000000076868d1a4604000bc909c14c8e88f0af8a7c000ffc86ce5c6e05cc65d1411bc41d1e4d0c3250591eca445d4b01300e14cf09190d92644ccb1d1dc6d41c1068000000000001060930000000348000000000950b10000000440850404030000ba0000000000b2c54d26c000000e4c1749392e40000000e45e800074000000000000000000116000111483c0000000003980010e014400000000053800000122899800000124c000a60000484a589408b4000d100000000009a0000000dc82d8ab43740000003fc000000000000fa077113879c000000000fac2007a4bb000000125400122c000754000d14af027400000075c000000000b747d50cc9c4ad40007e8ec8a980004d84e9240a9025400400a00800000600000a00400400000200000000000200000a00000000000000600000000600001200800600200000000401200000000000200000601000000c00600600200200001e02200000000c00400000200600000201a0080
  | 7 => 0xb20000000001040001168050b14aecf1cb9c0002f4000e48920694c747c8000000d28000c345980ecd000000000000010dc0000000002180009482f0c4095813cf7c1e4340cc0000001284f68eec000000c3c00040c52d1109f8138fc00000842d0d0400005400043c2703347c000082c79847c3a107c00049c0002380009ac000fdc000000bb400000000113c5dc0009b800000000000000089c00925809c9b0580180b28e58ccc8a4000000000000000000000000588208ad80000011c429c000000000fc466c0000000000010240000000000000000011000000000f4000000000428000000ff00000000000000000003c073c000000ff8000000000cb40000000008751180000003500000000007242f8db431c000b944347602b0639039260eb00a00009d9064000000cf40002b80001409c0000f6ce9d1f800072c000a34108b8900c4b49782c4dc4618000f550308340003b8110e98530458c08b6800116400037ce000000000007c4000db81587082208f83f8000000000d9c390adc7100005545f8d5caa838c000001294ec48dcbd800008c0005c07bc88d1f00000012b4e1820c0000011ac000e60000000360e68d740000000000012391b9234794000078d607dcf04000ef51b4d7cdf44e11e0001074630400be48cc000000e70f94000000b70298000000000d789fc8f4000000000000000000afc0000002e08c0344a24824000d8117400088097c0001a452060c8ec9141bc000000f512445d0000000edc831170f646ac00107824c01c0003ec02c528f5cea0000000000000000738000000000000e84b4ca3c0b4764000000000000af442c00016821072085821ce8cbc10d110c748abc4242142d42905590b8e54f3807c8c80000012187d0acc000088000b5000000099c388364ac4be8128080e08ed0000df11286500007280000000011585d8000000000000ad00000012740000000000007d91984b8000000f2c0000004dc000000000000f70000c84f108d80000000004a8b5881c6a05bceb80003300007580000008a0995178518584a50000000000ce06a8954310000000000000000ce82251440001889e800000000000096800096c0006241d914cea495c8a800000087009000058c0005ac000000000000000d8c6ccda0048b3097400000000000000000000000000000000000090c000e300000008900010c00000000003840005740000000010b0b849f0000c58f24358000000e90000000e04000000df8f9cd6c00000112400000080028430064cc20dfc000a48000000c80500000000000f14c5c8780007440000012e00000002802e800077869800070c000000250884c0c788b8c7cc9c84a000056d2d4d3c000000000000000000d700001dc0b8000000000000000000000d200000000012cc86515504cbdc71400000
  | 8 => 0xfc7012f40009f4000000000aa40005e40002a4550d18804134000000000000194000000000504ae834c0012ec0006b40fcc6cf44d880006c00009707f0bbd2e8615048000e381b46b8000000c18000000000e40000000ff4000000a74000000000000868024d48000e50f4c0000000009ec000154000d2c000b810343a4f600000000000000000001f4f58000000000eccc10d342b4000f80000000000000000000000000ea8f740681fc64400000100849010c001120c943088989883d902c57c48c4711c8d38000070000a6ca4cca86e8000000eb47800008080003a86c800000000022cba400115cde85080006800000000000000000012d8ef919cc903f01980002940950f00007e4000000000a110f8bd12d00006d8fe0e951500011cc1711d42dcf3c0000000000000104d4000fa8000000e780008180000000000001ac000001224b440000004480000000000007ac0002a000121c8280000200000000001ecc28000fb0524000258000d94964c380000000f8000000000000cbc164060ae0cd928d0280000000000000c000028c1250d47052a0000000000f90000000000494260b99004000000bfce88c98de00e06850bcfd845d2f8cf85b0820ca40c88e455c00051c0004645c8c9cb187e0a64ded2f0f34f98160bf44e424865800116c5f4ae47f887c0000012dc0005687f4924cfc4f91340000012b80b00000004f4ee83e032c000f8818459ce100012c0b341d4000980b40664a9c00000000030c0000005e0000a9477d0540006a43cc00000004400047400000000098ca300001b0240d90790000888a84000a1d20c000570000f209b4610baca800000000000a8cacfd0fe80000000000000000000000010a0000984c44000000e75148000000000000000750130dd89d4b910a90841e8355280e3c69c9cc1d02a885c6e4369014654380735188000560c00dcc000fb4058000000000bc42fc6f0674000408100640c1c041000e450c86700000008b0000000bcc0000000002e427c3180011d8594a383d00000011a0264a211b0000000ed40000003dc0004389e400063c0004f0e2c4783d52500cc000000c14000b24498000000000329194150cdc0006f800000000000c00105000000061c000001200000000000c480001a8a89130b08000000000000001180000000ec1209098a5400000000018d0f400000000000000108ca5ca78be011c000000000000e240000000000000000006d10940000000000000000001780e8000000bd40010fc0002bc78c000000000dc03e40009bc00000071c0001490800d4ab0f1843039c000ac00048d10e4c7cdbcb480006340000000000012a4b600009a8668e7c000000000000a700004b01140004ec2792900000010212100000001e0000000000b0c7ec00101c0007311c00005f0000001230
  | 9 => 0x25c0003aceac0005a0000894000000e64000578e6c4543940000000000bd104b7c000000c4ca180c4c8c6c400000000000000111c000000b3884084c00000127d17c53c33c94d03c5400000011d05488446b0000000b5c420d440012b06ec19ca402cc000000a2c00000026d220f280009d0990a04000d40ca03f4c50000b3cee0a680011080005b417c000000000000000b64000fbd0183b0c604d09dc00036c0000012700012880006dc000a0c000000000cb8fe4000204000444000000000628b55298648660000000000000288000000d851e8074c680002ec8549e02287b0e
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067d32594100067c325941002e7f715941002e7e715941002e7d715941002e7c715941002e7f415941002e7e415941002e7d415941002e7c415941002e7f315941002e7e315941002e7d315941002e7c315941002e7f215941002e7e215941002e7d215941002e7c215941004e7f70594100067e705941004e7d705941004e7c70594100067f40594100067c40594100067f30594100067c30594100067f20594100067e20594100067d20594100067c205941002e7f105941002e77105941002e7e105941002e7d105941002e7c1059410004ff7559010024fe7559010004fd7559010024fc755901002ebf7459010004ff7359010014fe7359010014fc7359010046bf4359010004ff725901000cfe7259010004fd725901000cfc7259010046bf4259010006bd425901002cff715901002cfe715901002cfd715901002cfc715901002ebe415901002ebc415901001cff705901001cfd7059010044fc7059010046bc4059010004ff7558c10024fe7558c10004fd7558c10024fc7558c10004ff7458c1001cfe7458c1001cfc7458c1002edf7358c1003ede4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c1003edf3258c10006dd3258c1002cff7158c1002cfe7158c1002cfd7158c1002cfc7158c1002ede3158c1002edc3158c10014ff7058c10014fd7058c1003cfc7058c1003edc3058c1002ef71058c10004ff7650c1002cfe7650c10004fd7650c1002cfc7650c1017e7e6550c100067d6550c1001ebe6450c10006bd6450c10016de6350c10006dd6350c10084ff769001002cfe769001001cfd769001002cfc769001010e7e65900100067d659001001ebe6490010006bd649001002df67190010005f57190010084ff76500100f67e65500100067d655001007cff768c01002cfe768c010014fd768c01002cfc768c0100de7e658c0100067d658c010016de638c010006dd638c01002df6718c010005f5718c01007cff764c0100057f754c01004d7c754c0100c67e654c0100067d654c010005bf744c010045bc744c01002df77644010006f77644010004f7764401000777754401018774754401002ef7654401002f766544010186f5654401002f756544010006756544010007b77444010007b47444010007d77344010007d4734401002ef76344010006f56344010007e77244010197e4724401002df7704401002ff3704401018ef6604401002ff26044010187f25044010187f15044010007f24044010007f14044010
  | 1 => 0x891005eec70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ec40d8910006ef30d8910006ec30d89101e6ef10d891005eed10d89101e6ec10d891001cfc76505100067f65505101567c6550510006bf645051001ebc6450510006df635051014edc6350510006ef6250510146ec625051002fb44150510005fb7050510005f8705051002ff01050510005f6768c51002ef6768c51002df7758c51002f76758c5101ddf5758c51002f75758c51000575758c51000777658c5101d774658c510007b7648c510007b4648c510065f5738c510007d7638c510016f6638c510016f4638c510067d4638c510016d4638c510007e7628c5101cfe4628c510005f6708c51002ef7608c51002ff3608c510067d4308c5101cff2208c5101cff1208c510014fc764c5100067f654c5101267c654c510006bf644c51011ebc644c510006df634c510016dc634c510006ef624c510116ec624c510005fb704c510005f8704c510065f4764c510016f4764c510014f4764c5101c5f7754c5101c5f5754c51000777654c5101bf74654c510007b7644c510007b4644c51002df7734c51002fd7734c510007d7634c510016f6634c510016f4634c510067d4634c510007e7624c5101b7e4624c510067d7324c5101b7d5324c510007f3704c510005f4704c510007f0704c51002ef7604c51002ff3604c5101b7f2204c5101b7f1204c5100a4fe76901100067f659011010e7c6590110006bf649011001ebc6490110006df6390110106dc6390110006ef62901100feec629011001cff765011006cfd765011002cfc76501100067f65501100f67c6550110006bf645011001ebc6450110006df63501100eedc6350110006ef62501100e6ec6250110005f7715011002df4715011006fb8405011009cfe768c1100067f658c1100de7c658c110006bf648c1100d6bc648c110006df638c110016dc638c110006ef628c1100ceec628c110007d6318c110014ff764c110064fd764c11002cfc764c1100057f754c1100757c754c1100067f654c1100c67c654c110005bf744c11006dbc744c110006bf644c1100bebc644c110006df634c110016dc634c110006ef624c1100b6ec624c110005f7714c11002df4714c110067d8304c1100067f658411008e7c6584110006bf6484110086bc6484110006df638411007edc6384110006ef6284110056ec628411002dfa708411002efb608411002df6768411002ef6768411002cf676841101adf775841101adf575841100077765841101a7746584110007b76484110007b46484110005f77384110005f57384110007d76384110007d46384110007e7628411019fe4628411002df6708411002ef7608411002ff3608411019ff2208411019ff120841100067f74594100067e74594100067
  | 2 => 0x6dd50d8d10006dc50d8d10006df40d8d10006dc40d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d101f6df10d8d101f6dc10d8d100057f7558d100757c7558d100067f6558d100067c6558d10005bf7458d1006dbc7458d10006bf6458d10006bc6458d10066dc6358d10005ef7258d1005dec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10064ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d1007cff7158d10006f77158d1009cff7058d10006fb7058d10005de7618d10066de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d10067d57118d10007d65118d10007d55118d101eedf6018d10007da2018d10007d92018d101efdb1018d101efd81018d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1017e7c6550d10006bf6450d1001ebc6450d10006df6350d10016dc6350d10176ec6250d10005fb7050d10005f87050d1005dee76d891005eee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e651d8910007e551d89101e7eb70d891005fe870d89101e7eb10d89101e7e810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d89101e6ee71d891005eed71d89101e6ec71d8910006ef51d89101e6ee51d8910006ed51d89101e6ec51d8910006ef41d89101e6ee41d89101e6ec41d8910006ef31d89101e6ee31d89101e6ec31d89101e6ef70d891005eee70d891005eed70d
  | 3 => 0xc7359110005ef725911005dec7259110006ec6259110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c755911006cff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec7259110084ff7159110006f771591100a4ff7059110006fb7059110005be761911006ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110006bf6219110006be6219110006bd6219110006bc6219110007ac6219110006ac6219110007b65119110007b551191101febf6019110007ba2019110007b920191101ffbb10191101ffb81019110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10066de63d8d10006ec62d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df53d8d10066de53d8d10006dd53d8d10066dc53d8d10006df43d8d10066de43d8d10066dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10066df32d8d10006de32d8d10006dd32d8d10066dc32d8d1002cfe71d8d10064fd71d8d1002cfc71d8d10066df31d8d10014fe70d8d1002cfd70d8d10014fc70d8d10066df30d8d10065de76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d10007d771d8d10007d651d8d10007d551d8d10007da20d8d10007d920d8d101f7db10d8d101f7d810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d101f6de71d8d10006dd71d8d101f6dc71d8d10006df51d8d101f6de51d8d10006dd51d8d101f6dc51d8d10006df41d8d101f6de41d8d101f6dc41d8d10006df21d8d101f6de21d8d10006dd21d8d101f6dc21d8d101f6df70d8d10066de70d8d10006dd70d8d10006df50d8d10006de50d8d10
  | 4 => 0x95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951020e7e71d95100767d71d951020e7c71d95100067f41d951020e7e41d951020e7c41d95100067f31d951020e7e31d951020e7c31d95100067f21d951020e7e21d95100067d21d951020e7c21d951020e7f70d95100767e70d95100767d70d95100767c70d95100067f40d95100067c40d95100067f30d95100067c30d95100067f20d95100067e20d95100067d20d95100067c20d951020e7f10d95100767d10d951020e7c10d951001cfe76d91100067f65d91100067c65d911006ebe64d9110006ec62d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110006bf54d911006ebe54d9110006bd54d911006ebc54d9110014fe73d9110004fd73d9110014fc73d911006ebf43d9110006be43d911006ebc43d9110004ff72d911000cfe72d9110004fd72d911000cfc72d911006ebf42d9110006be42d9110006bd42d911006ebc42d911002cfe71d911006cfd71d911002cfc71d911006ebf41d911001cfe70d911002cfd70d911001cfc70d911006ebf40d911006dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d9110007b651d9110007b551d9110007ba20d9110007b920d9110207bb10d9110207b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110206be71d9110006bd71d9110206bc71d9110006bf51d9110206be51d9110006bd51d9110206bc51d9110006bf31d9110206be31d9110206bc31d9110006bf21d9110206be21d9110006bd21d9110206bc21d9110206bf70d911006ebe70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006bc30d9110006bf20d9110006be20d9110006bd20d9110006bc20d9110206bf10d9110206bc10d91100057f75591100757c75591100067f65591100067c655911006ebc6459110005df7359110065d
  | 5 => 0x5f4704c71006cfd7690310206bf649031001ebc649031001cff765031002cfc765031001ebe6450310006bd6450310005f7715031002df47150310064fd768c3101f6df638c310016dc638c31002df4718c3101f7d6318c310014ff764c31002cfc764c3100057f754c3100ad7c754c310005bf744c3100a5bc744c310016de634c310006dd634c310005f7714c31002df4714c310086be64d9210004ff75d9210024fe75d9210004fd75d9210024fc75d9210084fd74d9210014fe73d9210004fd73d9210014fc73d9210004ff72d921000cfe72d9210004fd72d921000cfc72d9210086bf42d9210006bd42d9210006f571d9210206be41d9210206bc41d9210006fa70d921001cff7659210086bc6459210004ff7559210024fe7559210004fd7559210024fc7559210006bf7459210004ff7359210014fe7359210014fc7359210086bf4359210004ff725921000cfe7259210004fd725921000cfc7259210086bf415921002cfc7059210086bc405921007ede63d8e10004ff75d8e10024fe75d8e10004fd75d8e10024fc75d8e1001cfe74d8e10004fd74d8e1001cfc74d8e1007cfd73d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e1007edf32d8e10006dd32d8e10006f571d8e101f6de31d8e101f6dc31d8e10006fa70d8e10014ff7658e100057f7558e1008d7c7558e1007edc6358e10004ff7558e100067f7558e100047f7558e10024fe7558e10004fd7558e10024fc7558e100067c7558e100247c7558e10004ff7458e1001cfe7458e1001cfc7458e10006df7358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e1007edf3158e1002cfc7058e1007edc3058e10004ff7650e10004fe7650e10004fd7650e10004fc7650e1001ebe6450e10006bd6450e10005fb7050e10005f87050e1001cff765061001ebe6450610006bd6450610005fb7050610005f87050610014ff764c610016de634c610006dd634c610005fb704c610005f8704c61001cfe769021002cfd769021001ebe6490210006bd649021002df67190210005f57190210044ff7650210087b84050210014fe768c21002cfd768c210016de638c210006dd638c21002df6718c210005f5718c21003cff764c2100057f754c21008d7c754c210005bf744c210085bc744c21007fd8304c210005f576c421002ef576c4210216f765c4210216f565c4210006f763c4210006f563c421002ff260c4210217f250c4210217f150c42100757e76d95100767e76d95100247e76d95100067e64d95100067c64d95100067e63d95100067c63d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100077771d95100777471d95100077a20d95100077920d951020f7b10d951020f7810d95100067f74d
  | 6 => 0xf7359130004ff725913000cfe7259130004fd725913000cfc7259130004ff715913002cfc715913024cff7059130006fb7059130105be76191300bebe7619130104be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130246bf6319130006bf6219130006be6219130006bd6219130006bc6219130246bf6019130247bb30191302479c3019130247b830191300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d853007ef631d853007ef531d8530006f721d8530006f421d853002cfe70d85300c57e75985300057d75985300067f65985300067c65985300bdbe7498530005bd7498530006bf6498530006bc6498530006f76198530065f970985300057f75585300c57c75585300067f65585300067c6558530005bf74585300bdbc7458530006bf6458530006bc6458530005ef72585300b5ec725853009dfb70585300067f65185300067c6518530006bf6418530006bc641853002ef66118530006f56118530004fe7690530004fd769053002cfc76905300067f659053016e7c6590530006bf649053001ebc6490530004ff7650530004fe7650530004fc76505300067f65505301567c6550530006bf645053001ebc6450530244fe76901300067f659013010e7c6590130106bf649013001ebc649013001cff7650130014fe76501300ecfd7650130014fc76501300067f65501300f67c6550130006bf645013001ebc6450130005df7350130015dc73501300075f658c13023f5c658c1300079f648c1300079c648c130236df628c130236dd628c1301f6dc618c130015de708c130017da708c130016df608c130017db608c130004ff7559310024fe7559310004fd7559310024fc755931002ebf74593100a6be5459310006bd5459310004ff7359310014fe7359310014fc7359310006be43593100a6bc4359310004ff725931000cfe7259310004fd725931000cfc72593100a6bf4259310006bd425931002cfc715931002ebe415931002ebc41593100a6bf4059310004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f1001cfe7458f1001cfc7458f1002edf7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f1009edf3258f10006dd3258f1002cfc7158f1002ede3158f1002edc3158f1009edf3058f10004ff7650f1002cfe7650f10004fd7650f1002cfc7650f1022ebf6450f1001ebc6450f1002df7764c71003ef7764c710225f7754c710225f5754c71002fd7734c710016f6634c71002ef4634c71009fd7324c71021fd5324c710
  | 7 => 0x95300067d74d95300067c74d95302567f73d95302567e73d95302567d73d95302567c73d95302567f43d95302567e43d95302567d43d95302567c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95302567f32d95302567e32d95302567d32d95302567c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067c41d95302567f31d95302567e31d95302567d31d95302567c31d95300067f21d95300067e21d95300067d21d95300067c21d95302567f70d95300c67e70d95302567d70d95302567c70d95300067f40d95300067c40d95302567f30d95302567e30d95302567d30d95302567c30d95300067f20d95300067e20d95300067d20d95300067c20d953001cfe76d91300067f65d91300067c65d91300bebe64d9130004ff75d9130024fe75d9130004fd75d9130024fc75d9130006bf54d91300bebe54d9130006bd54d91300bebc54d9130104ff73d9130014fe73d9130104fd73d9130014fc73d9130106bf43d9130106bd43d9130004ff72d913000cfe72d9130004fd72d913000cfc72d91300bebf42d9130006be42d9130006bd42d91300bebc42d913002cfe71d9130004fd71d91300bebf41d91300bebc41d9130014fd70d91300bebf40d9130245be76d913001cbe76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130006bf62d9130006be62d9130006bd62d9130006bc62d9130107bb30d91301079c30d9130107b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130106bf73d9130106be73d9130106bd73d9130106bc73d9130106bf53d9130106be53d9130106bd53d9130106bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130106bf32d9130106be32d9130106bd32d9130106bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130106bf31d9130106be31d9130106bd31d9130106bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d9130106bf70d91300bebe70d9130106bd70d9130006bf50d9130006be50d9130006bd50d9130006bc50d9130106bf30d9130106be30d9130106bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d91300057f75591300c57c75591300067f65591300067c65591300bebc645913024dfb7059130004ff75591300067f75591300047f7559130024fe7559130004fd7559130024fc75591300067c75591300247c7559130104ff7459130006bf74591300ecff7359130006d
  | 8 => 0x6df970985400057f75585400f57c7558540005df73585400eddc7358540005ef72585400e5ec72585400a5fb70585400f57e75185400057d751854002ef66118540006f56118540004fe768c540004fd768c54002cfc768c5400f57e758c5400057d758c540006df638c540016dc638c540004ff764c540004fe764c540004fc764c540276bf6590140276bd6590140005bd7390140106be6390140106bc639014026ebf629014026ebd6290140206bc619014001dbe709014001fba709014001ebf609014001fbb60901400d6be64d9230245fa70d9230004ff75d9230024fe75d9230004fd75d9230024fc75d92300ecfd74d92300d6be54d9230006bd54d9230006dd73d9230106be43d9230106bc43d9230004ff72d923000cfe72d9230004fd72d923000cfc72d92300d6bf42d9230006bd42d9230106df32d9230006dd32d923002cfe71d9230004fd71d92300d6bc41d9230244fe70d9230006fa70d92300d6bf40d923001cff76592300d6bc6459230004ff7559230024fe7559230004fd7559230024fc7559230006bf74592300eebf43592300eebd4359230004ff725923000cfe7259230004fd725923000cfc72592300eedf3259230006dd3259230004ff715923002cfc7159230014fc70592300d6bc405923003dfa70d8630006f761986300057f75586300dd7c7558630005bf74586300d5bc7458630005ef72586300cdec7258630004ff75586300067f75586300047f7558630024fe7558630004fd7558630024fc75586300067c75586300247c7558630004ff7458630006bf7458630004bf745863001cfe745863001cfc7458630006bc745863001cbc7458630004ff7258630006ef7258630004ef725863000cfe7258630004fd725863000cfc7258630006ec725863000cec7258630066df3258630006dd3258630006f65158630006f55158630066f63158630066f531586301f6dc315863002cff70586300dd7e75186300057d751863002ef66118630006f5611863007dfa701863002cff7690630004fe7690630004fd7690630006bf649063001ebc6490630004ff7650630004fd7650630004fc7650630005df7350630015dc73506301f75e758c6301f75d758c6301f5df728c630265dd728c630015de718c630017d6718c6301f7d6618c6301f6dd618c630007d5618c6301f7da708c630005dd708c6301f7d9708c630016de608c630017da608c630014ff769023001cfe7690230014fd769023001ebe6490230006bd6490230015de7390230005dd739023024cff7650230006bf645023001ebc645023025d7e76d95300c67e76d95300247e76d95300067e64d95300067c64d95300067f62d95300067e62d95300067d62d95300067c62d95302577b30d95302575c30d95302577830d95300067f74d95300067e74d
  | 9 => 0xe75181310067e75181310247e7518131004fd75181310067d75181310047d7518131024fc751813101cfe7418131004fd741813101cfc741813102cfd7318131004ff721813100cfe7218131004fd721813100cfc721813103edf3218131006dd321813103ef571181311eede31181311eedc311813103ef93018131106de63d8e402a5fa70d8e40014ff7658e4001dbc7458e40106dc6358e401079e4358e40004ff7558e40024fe7558e40004fd7558e40024fc7558e400bebe5458e40006bd5458e40106be4358e40106de4358e400bedd4358e40106bc4358e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e400bebf4258e40006bd4258e40004ff7158e4002cfc7158e400bebc4158e4001cfc7058e400bebf4058e40106dc3058e40045fa70d8640006f76198640004ff7558640024fe7558640004fd7558640024fc7558640004ff7358640014fe7358640014fc7358640004ff725864000cfe7258640004fd725864000cfc725864006ebf4258640006bd4258640006f65158640006f5515864006ef6415864006ef54158640206bc4158640006f72158640006f4215864010d7e75186400057d751864002ef66118640006f56118640085fa7018640205bf759064029dbd7590640105be7390640205bc7390640006bd6390640205bf7290640295bd729064001dbe719064001fb67190640207b66190640206bd6190640007b56190640207ba7090640005bd7090640207b9709064001ebe609064001fba609064002cff768c640004fe768c640004fd768c64010d7e758c6400057d758c64001dbe748c640005bd748c64002ef6618c640006f5618c640004ff764c640004fd764c640004fc764c640005bf744c64001dbc744c64002ef6614c640006f5614c640014fe76d8d400eede63d8d40004ff75d8d40024fe75d8d40004fd75d8d40024fc75d8d40014fc74d8d40006df53d8d400eedc53d8d400eede43d8d400d6dd43d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400eedf32d8d40006dd32d8d4002cfe71d8d40004fd71d8d400eedc31d8d4001cfd70d8d400eedf30d8d400057f7558d400f57c7558d400eedc6358d4028dfb7058d400edbc7650d40016bc7650d40014bc7650d40286bf6550d40286bd6550d4001dbf7350d4001f9f7350d400079f6350d40016be6350d40016bc6350d400ef9c6350d400169c6350d4027ebf6250d4027ebd6250d400ef9f3250d4027f9d3250d4022ebc6150d40007bb7050d40005bc7050d40007b87050d4001ebf6050d4001fbb6050d40004ff75d8540024fe75d8540004fd75d8540024fc75d8540014fe73d8540004fd73d8540014fc73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d8540086f641d8540086f541d8540006f76198540
  | 10 => 0x963102e7d415963102e7c415963102e7f315963102e7e315963102e7d315963102e7c315963102e7f215963102e7e215963102e7d215963102e7c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067c40596312b67f30596312b67e30596312b67d30596312b67c30596310067f20596310067e20596310067d20596310067c205963102e7f105963102e77105963102e7e105963102e7d105963102e7c1059631004ff7559231024fe7559231004fd7559231024fc755923102ebf745923114ebf435923114ebd4359231004ff725923100cfe7259231004fd725923100cfc7259231136bf4259231006bd425923102cfe715923102cfc715923102ebe415923102ebc4159231004ff7059231004fc7059231136bc4059231004ff7598231024fe7598231004fd7598231024fc759823101cfe7498231004fd749823101cfc7498231004ff729823100cfe7298231004fd729823100cfc729823102cfe719823102ef6719823102cf6719823102efa7098231006fb4098231006f8409823107ef93098231006fa2098231006f9209823102ef7109823102efb109823102ef81098231004ff7558231024fe7558231004fd7558231024fc7558231004ff745823101cfe745823101cfc7458231004ff725823100cfe7258231004fd725823100cfc725823102cfc715823102efb7058231006fb4058231006f84058231066fa3058231066dc3058231006fa2058231006f9205823102efb105823102ef8105823101cfe76d913111ebe64d9131004ff75d9131024fe75d9131004fd75d9131024fc75d913102cff73d913102cfd73d9131166bf43d9131166bd43d9131004ff72d913100cfe72d9131004fd72d913100cfc72d9131166df32d9131006dd32d9131014fd71d913111ebf41d9131004fe70d9131004fd70d913111ebc40d913111ebc64591312adf77159131004ff7559131024fe7559131004fd7559131024fc7559131164ff7459131006bf745913114cff7359131006df7359131004ff725913100cfe7259131004fd725913100cfc725913111ebf4259131006bd425913114edf3259131006dd32591312acff7159131006f7715913122ebe415913122ebc4159131004ff7059131004fc705913101cff7650531014fe765053114cfd7650531014fc7650531006bf645053101ebc6450531005df7350531015dc7350531004ff75d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813102cfd73d8131004ff72d813100cfe72d8131004fd72d813100cfc72d813109efa30d8131006fb60981310057f75581311257c7558131005bf745813111dbc7458131005ef7258131115ec72581311257e75181310057d7518131006f96018131004ff7518131024f
  | 11 => 0x2cfe7158e4102cfc7158e4102ede3158e4102edc3158e41004ff7058e41004fc7058e4122dbf7650e41016bf7650e41014bf7650e4122ebf6550e412d6bd6550e4101dbf7350e4101f9f7350e41016be6350e4122f9e6350e410169e6350e4122f9d6350e41016bc6350e4122ebf6250e412cebd6250e411679f3250e412cf9d3250e4122dbf7150e41007b77150e4122fb47150e4101ebe6150e4101fb66150e41005bc7050e41004ff7598241024fe7598241004fd7598241024fc7598241014fe7398241004fd7398241014fc7398241004ff729824100cfe7298241004fd729824100cfc729824102cfe719824102efa7098241006fa5098241006f95098241086f94098241006fb3098241006f83098241006fa2098241006f9209824102efb109824102ef81098241004ff75582410067f75582410047f7558241024fe7558241004fd7558241024fc75582410067c75582410247c7558241004ff7358241014fe7358241014fc735824106ebf4358241006bd4358241004ff725824100cfe7258241004fd725824100cfc725824102cfc715824102efb7058241006fa5058241006f9505824106efa405824106ebc4058241006fb3058241006f83058241006fa2058241006f9205824102efb105824102ef81058241014fe76d8d4114ede63d8d41004ff75d8d41024fe75d8d41004fd75d8d41024fc75d8d4102cfd74d8d4114ede43d8d41136dd43d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d41136bf42d8d41006bd42d8d4101cfd71d8d412c6be41d8d412c6bc41d8d4114edf31d8d41004fe70d8d41004fd70d8d4114edc30d8d4114edc6358d412bdf77158d41004ff75d8141024fe75d8141004fd75d8141024fc75d814102cfd74d8141014fe73d8141004fd73d8141014fc73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d81410a6fa40d8141006fb60981410057f75581411557c7558141005df735814114ddc7358141005ef7258141145ec7258141006f96018141004ff7518141024fe7518141004fd7518141024fc751814102cfd7418141014fe7318141004fd7318141014fc7318141004ff721814100cfe7218141004fd721814100cfc7218141046bf4218141006bd42181411febe41181411febc4118141046f940181410067f74596310067e74596310067d74596310067c74596312b67f73596312b67e73596312b67d73596312b67c73596312b67f43596312b67e43596312b67d43596312b67c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067d42596310067c42596312b67f32596312b67e32596312b67d32596312b67c325963102e7f715963102e7e715963102e7d715963102e7c715963102e7f415963102e7e415
  | 12 => 0x200e00000000100700000000a00100300100600100000300800000400000000300f00200000900000500400100a00400100a00000100200200100100000100100200900f00600000800200100000200300400200400300000000000000000000000000300000100000000600100100f00200800400200900300000000000500100300000200000000700900c00700000100200000100000300000000700300000100600c00000100700300100000800400700000100000000100700000000600400200200400900200600001900c00800100100500000101200100100000300000200300300b00000400000200000000800100200000200600700100300700100000900000000700000000e01500000000000100000000700000500000000700000900800100000400100000000400000000500000600000000100300101500400100200300000100100300000000000400500000b00200100100100000000000000b00000800300200000200200200000000300000800200200000400000000100100201500000400000300200000d00200300400000000500000300100f00000000500000200000000a00100000000000000c00600700200000000000100300000000100000100200000002cfe76d8543004ff75d8543024fe75d8543004fd75d8543024fc75d8543014fd74d85432aebd74d854301cfd73d8543004ff72d854300cfe72d8543004fd72d854300cfc72d85432bebf42d8543006bd42d85432aedf32d8543006dd32d85432bef641d854322ebc41d85432aef631d8543006f721d8543006f421d8543004fe70d8543004fd70d854317d7e75985430057d7598543006f76198543005fa7098543005f9709854302ef66118543006f56118543004ff75d8143024fe75d8143004fd75d8143024fc75d8143014fd74d814301cfd73d8143004ff72d814300cfe72d8143004fd72d814300cfc72d814302cfe71d8143004fd71d8143006fb50d8143006f850d814328efa40d814324efa30d8143006fb20d8143006f820d8143006fb60981430057f755814317d7c7558143006f96018143004ff7518143024fe7518143004fd7518143024fc7518143014fd7418143246bd74181432a6be5418143006bd541814301cfd7318143246be4318143246bc4318143004ff721814300cfe7218143004fd721814300cfc72181432a6bf4218143006bd4218143246df3218143006dd321814302cfe7118143004fd71181432a6bc4118143006fb5018143006f850181432a6bf40181432a6f94018143246f93018143006fb2018143006f82018143004ff7558e41024fe7558e41004fd7558e41024fc7558e4102edf7358e41166de4358e4111edd4358e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e41166df3258e41006dd3258e41
  | 13 => 0x1840001110000000ab81761bd000000000000000000000923f596ecebc2f604a9ab0f567990001bf035a314423953c0005c600009d44404763aa17500000bc0000000d1a01500002180006500398d743b2000000183498c53c186922ccfa00018e01f008a6160001950b406550b780000a64d308c203c7462a41b300006d260b0000000cbc00035a80000000000000000da86390000070fc649e17680003aa0003b11d0037a5222c687300004ba36a800071a22f2cd000000072a2f8147c00035400017880002832ef8000f5c0f132999b400000000003e000027e2ca9b040004670e3903400000000000000003b10000498c226970000b8800028b27f90a40006ec3de000000018b0000c580004c000000000000003e521740000002a700000003193d9800000067800016940004322be00000007680000000adc5611a80db01be20806108382ba51900013c8ef269a1f197d0e9a2882220e449ae11f3fe95e0ae278314b8a50000000000031424a09b1188a000000000000f5c2ac00000000000001d20f99270c2e1781bb00000001103c690700001a8000027097600200400b00100500000600000400300000000000000202900100400300700000000600000500200200600000800000300501400200000000800000100100100300100400000300300c00000900000000800100300300000200200200000f00900f00200300000000300000000200000000200000000000000900100000100100100000100a00200000500000100200100e00100000800b00000100700400100a00300200100100000600000200300001600000200200c01f00300101500900300300000600400100500100200000800000800000700300200000500200000600b00100300000600100200000000401400000600c00200f00600400000300800400000100600700100100200a00900000100100000000000100300b00000000000301700000000500b00000400000001400700001e00200200800400100000400d00200600600200c00700200200000000100300000800601900400100200400400200000800900000000400200000000600d00000400200200700200000000300000602800200000700500300000000800000000500000c00300400000500b00000100600100400000000100100a00000400500a00800100000200000000800400200800100800000600000500000300c00700200700200000000100000100000400000400e00100900100000000000000100800000700300b00301600100400500000000300000200000000500500200000a00100100000600300700700500000a00700301100603000500000000500d00000200000000000200001d0020020000000000090080090010000010000010080030020010010040030030020070010000
  | 14 => 0x40900006208702701f5000000034b26f80000001360000b80f6e3de1839ccc0001a616c1a7d03e0784109404cbe00008b02fc00076c00010dc5140031c80ce400000029f800000062f00000000007a936b11000003bf17810640ee0004201f902d00000000e382a000500f000000000005700000a4457230064c0000002850000e3e61e00012948505201ee8c785460000b890c465a4d2375865450a70e00000005a4000000000071050b0001bfc00000042c0000000274000000014214540f154400000000000000000001b09674eb44580000000ac03f70001bdc0001b508a8a4000000000016c060c32a000129c0000001b0000109244a000000000074b1c60dec85803941b80000005cc00000000005ad197094800067a39f9e6009c0000001c2811c3ec1f91c8800030a02e8ad84160e11be80004aa000000000010e000036987400072100018fc1140003a10000c485f32701ec45b816e0761fc00005883f407e00000000000e4c0006950001168d722f822380000008562489e5c2e646e3bc1c20e5a00035000000005561f8000005e000000000000000031f04a44f400029d800000000031a95accb000041f800012e00000012400002cc0aa800001418e344109c9301a53b280000006c400015f83f22c23e600000005fa0000000000204017000000011b0000de000024d2798304fe200037d800000000028480000000001b800000000000000000da621d0a207b400026e1fa04200007c422491c0bf642e21811b4ec014941500002f27280958c0815e0000001364324000000196400060101c1f540000002b18000c9a3a907280241fc76118f9f8468233a235068049408000006bc95e4dd23ea1504a62e900000009e05f10000000000000288036506245207b8c94000000000113c0004820001b180000003600000aa453e00016b0578000000000000037c37299005903720ec00000000000c300000000000000000f746ed39e0000cae0003c8025000028200018500005e100012580c40ce01f817c7282eb2f319a064c0003cf89404bc40829a00008be4fc28d943097e00000000002cc00000000007423b01549ed80920e804080010181a40ea000083c10e0460000000124000139c4681b200003980b015c1550ef80000000000000a944120001c700000000660000000000000000056e0000000000000000000000096800000000000003e21d9842ce0a6d820580000002f42889b2c62e2f90001ff02263a50000a982a47c00be1060ff418d0001d7cb9a4720c08cfc000000377214000042b00000d0d200ed266131c0000000001e840005382588000df20003dd98182406d91c209c8c6060c2b39f6c0004231daa0600863f527a853400000000020001b400000007240006f200000006202b91ec1f640000000000000000000000
  | 15 => 0xa80000000003498644dae0002f00ea8e4a00000013e4c524ce02f1724b706700001248ef40000000000b047e028f10e4a0a81006b09240007181129fc87723db000210c0563712749948fee4cb2648000b6e25c0ff0bfcec843500000007d07841200b14c4c00014919ac00000000020b40007c32ca000016c21f000000000024200000000002ab2fe9bcc806000000000000072c34100000001322450a640003c5000000000000000000000000000000000bbc76a3f9952c000000000136c0006df38f00000000000000000b8e0003ff00006d432906d80886da04839b1c4c0007f939da0e48b65f8000000052666702880a000080417b80004664f6000000000029635206400003a80000d8c0004330000000e40000000000025a0000000000e740004119f4037657706002780000000a09cc40003c924e800071619f1a9000091852d0001d980003002448000eea81c03b075c3182ca256189c44e69436d06e476e00032b1af80005a31108cbc0004c80000d300003204128e5c0586e300000c80001b800000005805c20001c50a5400018d9af05c20004100ad47128412bd0abc00048e0f60000f8483d0001b88e6e00011d8000000000000000000010236680009ca2e60000bd45b200008e8000ab24340b58f201a60000001d4cb000001538000e0e0000000000262089000000000068e000000032e74c09f0fc4ee20002d89d3c218000000000000000038b88fc00028f0fb18b000035c0000000e9078c3faa05ca062673d40000000000268188c73e4ee2d9859c0000000000b50156591207800050242622e8e2801a7bd1f291882c466228e000000064f0b81218f5e5a102600000000003f51d7000000000000002fa5870338f1cc5000000007284560000001f3508c8150ef0e6000000000000005c608d0001c18aca03300000000000000e580004a20c300001a06102e7000014000082200000007fe5c40000b1c0000000001fec5365f51d10d9107c29128a0e650603092b61c44a1c00033490044b60b20701abc0000002d38000cd8000417048400037e2a08000a527d43b7000014a1283811ed407453a0a99c48c640000001e28c900000a3082839c0003a280010ae000069057c9aa11229181accea3220000fcc00026200018ec000000000166443627f08080005f600000018c489026600000008ca4ca0000ac90981820000000ef6000000005867c0f30000c6897c2262c788004747be0000d240000003e587a0000000000179c00e0000001a1c5aa000000074480c5c011c0f086a25242508d6cd3236f0418f548ee00000010f819679b2438000a1001a2ed810029824b0001e700006031b107d446e6370001d1800067342595a800075100011acc84000000128054025700000010b40000cc05d00000000000000b3c0a437f000000
  | 16 => 0x920002c58000d8e0f92999c00f486fa33f16fc23266625591a429c0131d31f981bc0e917e1dac04e0002419d5cd1234436401189660ba1ab02a0ab48270108400c8c45030d9e3c5ba1e019e9f7c79e1850000ba103271b23c0000000000005800068a42a000129800007f06a800000000000000000000000000018e1800021b000089a5620d7000085e0003229848428000000164000064100000000003df39a80003e2834000016c0005c805612343d2228419800077a27611b0000000000000000000078107e800029e6610390b900003e100018cc00000002e056453a7a70001f7063069e15d0c90b2606411e8000d680000001334e161b112b135000063d000000015400000017bcc420000950000a1e8380000000ad02fa3e4800108414300015d46fe773000157c0000002000eb80ac79a000105c73800000c0c4400000034900004721231808000cc068a3418000f685b2000000000000000011f909e5eb0ee80000001da3e710746785a42f190847d60000cb0a180000000001eb4000527000000000000027780009521c60fd885cf4061c0000000d74000268955c1901e738199d8eb200012605dcbb80001388000686065000199000025f0000000000000000000000000000002e448800035495a40006d00b084f06be58601280001300143fb02440005ae1f6a03400000000013dcae61e30001b78d7a000297059106405716999fc9c607a3550d94a9a4e80e0983cc267390aa13acaa01a32978d085580371779caca1a48f2d7992400013d0e18000000000000081c00014700000000000000ca07d059a0000678fec0006a233c9df80de04b23a9f780e06ae1dc04b8e0228c000000000028400000000000000001824c3200016f01ec00005a160979014000023d800058884a000176400000020200003146e0075000027400012c0000e9c000000000000057b1a306d0a343821941310bf20002b687700000003a518e0d940000001a18c0822e3eb1eb07fa81a2288000000000000000000000023a00000002d02f28080e3278b27e831ca904d824404cc0000000000000a9265a2ed080404c00031a011c0005121069aa075e1f00001bbcf640962f41f4c73c79100000009f63870bf000017064300019440003c1000000000000000000002bc0003a915d04601a724d206c2907d800007a800021e000000000033338ea00c0000000de084cf040000000000f1c04d000000000037422989e505011c2fe0d2800000000000006d600000000009f000000012c833c5be11914d800000000016f07f22be0000000b9c000000080cdce59800004240620003cb00000008520cd137884a76d07a9080e8e22220d91043802a81a78d4c0000000a5800048a000000007c0000e74240d604d483a1e600000cc7ee2f48000fe800000000310b852120
  | 17 => 0xcba0983f81c240a0e90f4600005b80000000000001a940001e23df84d4000000000120400047c25209384d60000001e7800000040b00000004e42af1ffc1526b138d0000ece3bc378125c00015a1ba8e3cb0a6f801697b40aa2cf00000000fc6ce06e141c0000000c4838890884d00018140000000000d00c965ba3aa80000000000000f4c000000000000000072f0001a3c00019b0001c24f7200035b00000000740f90f380d2000398188800067200007f42340f21319cc80003e91080108ba216c0000000a261ac000000000081214f04ec5b67dd00000002fe0002a2055c00000000004bc9b84c100009688862b00001c403b65060838da07f80000519b98000000000151500c00007d800000000000000005dc0002bf92f0d9e7440000000e6878021d92000e232b0e9800000000041a800000000000003740100002c7000092600000000000000000a89dd800066330c000031e69b2ec0e1439024300013880001751ed0000000000000000000019c00019f0de21b023f9a0466045c00000007024853b792f43323ee07781040003b20000000ee04730000a380001bf0000ed80004b700000002ca000000000000020f20b05a400000002200000000000000000000000000000000000039391080001aa0000e0000000019617a8e523ab19b0000000000000081400000000000002060000000000e086964089fa40001fa35f80000000000000000d2203537b000020c00000004e000000004f83102680001fb00000000001908c549b4543000000000034700003440001270000000e2c6e925c01287ac5a80f78904ab0583258000016600000000005340001f38000d080000db89e00000001c180000000120000000542000000058c11613003a82b41fe367036000000074323091e861c8362028a2437c2ea0d98674eba5001859d5843200000000009cc4ad0000000b540002b91b70b360000000000c740fa36e9adc1626b02db1cf50b200000000000001422a11df4b960000ad907c0007da2fb0000fce0ee0f0845078c16d351915002200001b00006621ba04202f817a26829e85600007ec3e900000000001160854d8a5f700000007880001378b94e4820c1648c9c0000004038f5058682f1528ab4e7c445231951cbae0000d4969842c54628b04e496a4ae2da00000006c309f9714dfa36e00010306aa0d723314980000103c30bb0a2a5ec18900007de000327000000042240e875853e1c52789b300005550000000c10414182000079a00000013f8fda1ee000028800000042a80000000001239e1c0c000000000000000000000f4400045500018b800000034580003ee00000000001206d20e680000005c33fc1ddc4e62c63ad94090b61a21320bf874e0001349a30dea80811f1aec51a2981e599100005172a608687585f22b216301
  | 18 => 0xe930c7242d700000000dc14000000000000003b180006465d600007ad01240a1ac80000000002c51e15004277127803c07c00000006d8c9461a07e0000000000000000000044600000000000000001ea80000002342028b4410a000000000000008296e4c563ba14381e40007583e4214400000030f8000f82211124000000085329c80000003ad1798001048805000000000000033d9ba000000000016104c05322e9800067640219a0f28a6a0d41511d240000001ec8000000000000000000022d00011c46f24d600019c4fae44c0000c3c0000000000b7c6b4000326196c0003772aa000062656600000000007743c4000061843a11200000000002360b2c00003b08f00000000000000000a8042d34c1d043421222e808a45ac00028c0994b6a7953d31fbccb85ca1e19038b1226d2c91c3413429c25419d047810f22b17fcc401ff111956c22e6a106c1f448de16a15d8cdc1e800000000000004103e300000000001a700000001040000000000000227039048c4cf30520a4a3a0a70070794f443e431e000000063600012880002f203180000000000000974c547e20000bf4b9e0000000264ed22b800016ac00043f10e0bc49720002ea80000006b20478e18000530000006ca560592098000740000086800000000013e9e500000000000f0000035734e15e40000000000000d840002cf8298000792075800000039d3168318000000000203800460e0001e24efe0000000150e1e0000c20000da200000000000000002cb1e9507864705a81f4cee00024f925000009d0001090000000000000000000000000000000000000afc00000021e8f7072a0244220ab8de800010c00000000000ef80000000003dc18080000000000a549da000000000000052c11a800000000029b80000004aa0000c1400000000c80009d80000000ff82e400000000007f012c3be0000d3a4643f2941000045e1048af47a41871a6800000080b38a95bc000004000116407800000000004d82610001b2440c7b0353154c11027c10920ac2f66152709ba8d0000000000000000000001e74ba400032e8e680000002de805c4f61c43a805281043bb1fd0b443000e30651f3cd4e3030f2131426e83b2bb1b84f8a0000bd000039e00007b126c0003e623c8e6c0000002088acc0000001e80c741763e000009500000000001ab4cca4073351acc09e1d00001ce0c2072624c8000bdc5812ce000108a3b400013080000b00000000db60003c980000001ab40998940522ce303800000008527a03340000232518000dc81600000d78e5c66f1cb01a80002b42988000f8e2022e0824c6e66854271ae0e465dd000096487877235593e8a4a00024a860c96c44b000000005433841616a500200030017f81a033519903c000000001e80003cc57000019b80605282
  | 19 => 0x20001a415745620b42be800000000011510685b40002750000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd6575d8a3144001d88c7b1462880163da1a708c5100066db18e098a2000c7476d953144001ca8c7b2a62880032d1db644c5100065a3b0c898a200ccd476d8d31440019c8edb1262880025d614704c5101eee9b98e098a2040cb471d91404407b9aced18c60881721fa1b754c1100061e326ea982204ac5c63dd530440018d8c5baa608812e1fa1f654c11020c3e43eca9822000c3c74d95304407f17d0dba260880030fd97744c1100061e32ee89822020c9c63dd13044001958c5ba260881222fa1f644c1102045e43ec89822000c3f75d913044001878ebb22608800317dd7634c1100062e3aec69822000c9f74d8d3044001938e9b1a60880fb351c7634c11000637baec49822000c6c75d89304400195ee9b1260880032b1d3624c11000672316e29822041c7676d961044083ce6c1b2c20881032d9db648411001e5b3b0c908220028f686dce10440012ef0ab9c20880fb359db63841100166b3b0c70822000ec46218e10440799ccedb1420880030fdd274594100061eba0e8b282000c5f739cd650400147d0839aca080028f610735941000537410e6b282000a6d821cd65040010fd0e21aca080021f61c43594100053741086b282000a6d8210d650400147d08392ca080028f61072594100052f418e4b282000a5d831c965040010fd0e212ca080021f61c42594100052f41884b282000a5d8310965040014ef02992ca080169d20532594100043f43864b28200087d870c9650400147d08192ca080028f61032594102dd3ac0ce0b28200987e87d0165040010fb0fa02ca080169da0440594100053ac0880b28200087e870c165040010fb0e182ca080028fa1030594100051ec2060b282000a6e820c165040014db04182ca080169da0430594100053ac0860b28200987e87c8165040010fb0f902ca080028fa1320594100051ec2640b282000a5e83c8165040014bb07902ca080169da0620594100053ac0c40b282005a768108165040014eb02102ca080162f21d425901002c7a40ae4b1820058dc874c9630400b1790eb2286080163721d6350c1002e3b38acb2002005cb67159240040018eacab8c80080171d9c5658c01002c6fc3ac718020008f7865c630040018eacab8c60080621f61b754c0100043f43aca980200987c875953004001878e8b2a60080030f997744c0100061eb2ee89802000c7475dd910040019c8e5bb220080031de1776440100063a42eec8802000cf250dd910040019e2a1bb220080031dddb75440100053b43aca8802030a74875951004001cc8e4b2a20080171ddc1654401002f39b82ca8802000cb776dd11004001c6acbba220080032ddd874440100071ab28e88802000cd776dcd1004001caacbb9a200800335dd873440100072ab28e68802000dc4721cd10040019ceedb922008003995977244010
  | 1 => 0xf0abb286880121f2157650d100045fc22eca1a20008df835d943440011df04bb286880063b2097650d100145f43ec8a1a20038de87d8d434400b1f50db8286880031e1977050d1000674316e0a1a2000c78651c14344001976c8382868800336d8c7050d1000674310e0a1a2000c6e76d9762440011db0f32ec4880029ba1665d891000557424cbb122000aad84997624400159d0732ec488002b360e65d891000477c3acbb122000aaf84597624400155908b2ec488002b3e0d65d89100056641acbb122000a6e8619762440018dcec32ec4880039960465d8910006573b6c9b122000e2f65d936244001c58cbb26c4880023b61e64d89100053742cc9b122000a6d85993624400155d09326c488002b3a0e64d891000566c1cc9b1220008ef8759362440014df0ab26c4880029b21564d891000567c1ac9b122000acc83593624400155d0c326c4880032b9d864d891000717b28c9b122000e2c65193624400199cedb1ec48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec4880023b61e63d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d89100056741cc7b1220008ef8758f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f624400159d0c31ec488003339d863d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000762c08c7b122000e6465947624400155d093aec488002ab61275d89100056741cebb122000acd839d762440795cd023aec488002b960475d89101e57340ee9b122000ae581dd362440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d36244001c5ea92a6c4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec4880f2b9a0473d891000572c08e7b122000e4f5394f62440011dd0e29ec4880023b61c53d891000557420a7b122000aad8414f62440011dd0e21ec4880023b61c43d89100053742887b122000a6d8510f62440655d501b8ec4880023ba1f31d891000476c3e63b122000a6e85cc762440014db0b98ec488002aba1331d891000556c2663b122000aae84d43624400155b09a86c4880f2b9a0450d891000572c08a1b122000a6e85d0362440014db0ba06c4880023ba1c30d891005c76c3861b122000a6e850c362440014db0a186c488002aba1030d891000556c2061b12203cae6810c36244083c6883b2a82880032ed90705051000672314ed18a203b974865d631440bbaa8c6bac628800359189758c51002e3bb02eb18a2005d73605d63144001ae440bac62880035c481758c510004bbc3ecb18a2000e5463d963144001a6aebb246288003a518f648c5100069aba8c918a2000e946319231440055ad0db1c6288003359db638c510006aabaec718a2000
  | 2 => 0x740d8d100052ec2e81b1a203e8de87c8363440011bb0f906c68800297a1720d8d100052ec2e41b1a2000a9e84c83634400153b09906c6880121fa1b7558d100062e31eeab1a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c9c63dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440031dd0db92c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880033318f7258d1000637ba8c4b1a2000c6c75189634400195ee8312c6880032b1d06258d100243f43eeab1a20008bf845d5634400717908baac68800237e0d7558d1000477c12eab1a20018ec825d563440010fd0e3aac68800e2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440010ff0ab92c6880121f2157258d100045fc22e4b1a20038bc845c963440011bf06b92c6880023de057258d1000477438e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac688003179db6518d100072ab8eca31a20008dd8799463440014bd0b328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100052f430ca31a2000c5e761946344001cab02328c688003959c46518d100072ab88ca31a2000c9e76d906344001c3ecbb20c688003871976418d100074ab8ec831a20008dd8799063440014bd0b320c688002976166418d100054f424c831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100054f430c831a2000c9e761906344001c3eca320c688003871946418d100074ab88c831a20008dd8798863440014bd0b310c688002976166218d100054f424c431a2000a9d8498863440011bf0eb10c68800297e156218d100052e42ac431a2000a9f84588634400153908b10c688002b5e056218d1000727b28c431a2000e4c651886344001d1ec8310c688003a31906218d1000763388c431a2000ec5711886344001d9300310c688003951965118d1000762314a231a2000ad4865446344001d88c4a88c688003b218a2018d101ed6c4324031a2000ec86248063440090fd0bbb286880021f6177650d1000c77416eca1a20008ed82dd943440010f
  | 3 => 0x6b222000c5c75dcd644400193ee9b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440031dd0fb92c8880031bdd77259110006363aee4b222000caf74dc9644400199ee7b92c888003331cf72591100043fc2ae4b22200487c855c9644400117f08b92c88800237e0d72591100146e41ae4b2220008ee871c964440018deea392c8880031b1d4725911000657ba0e4b222000ccf731c96444001998e6392c8880030f9db65191100045ec3cca3222000a3e85994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c8880028fa1865191100061f3b0ca3222000e3581194644400147d0b318c8880028f616631911000557414c63222000aad8298c644400117b0f310c8880028fa1662191100051ec2cc43222000a9e83988644400153b07310c8880022fe1d62191100051fc2ac43222000a3c85588644400153f06b10c888002a720d621911000717b28c43222000e2c651886444001d5300310c8880038d19651191100055a432a23222000ea862880644407f5710c900c888003175d753d8d100056ac0ea7b1a20048df8754f63440031bf0e996c688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec6880039560465d8d100070fb2ec9b1a2000e1c65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc825936344001c3eca326c6880038719464d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d100052fc2ac5b1a2000a5c8558b634400153f08b16c688002a721162d8d1000727b28c5b1a2000e4c6518b6344001d1ec8316c688003a319062d8d1000764c00c5b1a2000e54659476344001d90c5106c6880fab621920d8d100054f424ebb1a2000a9d849d7634400159d053aec688002b360a75d8d100062eba8ebb1a203ead6811d763440015ab023aec6880fab660374d8d100052f42ce9b1a2000a5d859d3634400159d053a6c688002b360a74d8d100070faa4a9b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000ada801cb634407d5b300396c68800237a1c52d8d100046ec38a5b1a2000a9e8414b634400153b08296c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c68800297e1571d8d100052e42ae3b1a2000a9f845c7634400153908b8ec688002b3e0971d8d1000566412e3b1a203ee5651d47634400153d09a86c688002a761350d8d100072da84a1b1a203ead68114363440015ab02286c68800297a1
  | 4 => 0x54400147b0998eca880029ba0b31d951000536c1663b2a204187e87d0365440010fb0fa06ca880021fa1c30d95100743ec3861b2a2000a3e840c3654400147b08186ca880029ba0830d951000536c1061b2a2041a76810c365440830fd0f906ca880021f61f20d95100051f42641b2a2000a3d84c8365440014bd07906ca880029760f20d95100061ebaea9b222000ab581d53644400157301aa6c8880122fe1d54d91100047ac0ee5b2220018bf8750b644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400153f06b2ec888002a720d65d911000557c12cbb222000aac825976444001c6b0232ec8880028fa1663d91100051ec2cc7b222000aae8298f644400155b0531ec8880028fa1662d91100051ec2cc5b222000a9e8398b644400153b07316c8880028fe1562d91100051e42ac5b222000a9f8358b644400153906b16c8880038bd9462d911000716328c5b222000ea98018b6444001c68cb28ec888003aa18a20d91102055c43241b222000c3d751d7644408156d023aec888002ad60475d91100055d400ebb222040ab9801d7644408157301b9ec8880028fa1673d91100051ec2ce7b222000aae829cf644400155b0539ec888102ada0473d91100055ac08e7b222000e1f5394f644400117d0e29ec8880022f61c53d911000557410a7b222000aad8214f644408156d03b96c888002ad60772d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d91100055d400e5b222040ab9801cb644400117d0e296c8880022f61c52d91100054f418a5b222000a9d8314b644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb6444081c6ca3a8ec8880022fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec888002aba0b31d911000556c1663b222000a3f855c364440014790ab86c8881022fa1f50d91100045ec3ea1b222000e3b50943644408156d02286c888002ad60450d91100045f43861b22200d8bd870c3644400147d0a186c8880028f61430d91100055741061b222000aad820c3644408156d02186c8881022fa1f20d91100045ec3e41b222000a3e85c83644400147b0b906c888002a7a0f20d91100054ec1e41b222000c3c64dd564440010fd0fb2ac888003171cf655911000636396cab22200087e8719564440018b8e632ac8880031b1c865591100062fb2ee6b222000c5c65dcd6444001938c9b9ac8880031bd9772591100063632ee4b222000cac64dc964440018deea312c8880031b1d4625911000667b98c4b222000ccc7318964440090fd0fbaac8880022fe1175591100046fc1aeab2220028dc835d564440011df04baac8880063b20975591100043f438eab222000c3f75dd16444001878ebba2c88800a37a1f73591100062fbaee
  | 5 => 0x81878ecc0651913030f0e180ca3226061e3830194644c00117b0f310c8980028fa1662191300051ec2cc43226000a9d83988644c00117f0eb10c8980028fe1562191300051e42ac43226000ab781588644c00156902b10c898182aee0162191300056ac1843b0a6000af180087614c00187ce9b2cc2980030f9d065985300061fb2ae930a6000c3c655d2614c00187cebb24c2980030f5d764985300061f3a8c930a6000c3d75192614c0bf972e0324c2980121fa1b75585300043f43ecab0a6000c3c74d95614c0018d8e5b2ac2980021fa1c65585300061e3a0cab0a6000c6c72195614c00187ecbba2c2980030f19774585300045f43ec8b0a6000c3f75d91614c001878ebb22c2980032b1cb64585300045f438c8b0a6000c3f75191614c001878ea322c2980032b1c8645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b19372585300047bc3ac230a6000ae482584614c0010ff0abb482980121f21576905300243f42eeca0a600087d85dd9414c041938e7b2280980031719773501302562f3b6cb182604ae5b60d96304c04193cedb24609800f279d8648c1300070e328c918260058bc8755164c400b17d0f21ac9880021fe1572593100243e42ae4b2620058f4815c964c400b1790ea12c9880072b1c9425931002d5a40a84b2620058dc874c963c400517b09bb287880025d614704c71000c77416ebb2420008ed82dd764840090fd0bb96c9080021f61772d921000c5fc3a85b242001cae7250b64840031bf0e996c7080121fa1f7558e100043f438eab1c200087f855c963840090f90ab92c7080021fe157650e100243e42aeca1c20028bc87591438400553906b2287080163e6187050e100053bc2ac78842000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200087d8798b654400147d09316ca880028f61262d95100052f41cc5b2a2000a5d8398b65440010ff0eb16ca880028fe1162d95100051e422c5b2a2000a5f8358b65440014b906b16ca880039a60062d95100753b436e3b2a2000e686288365440834f10c906ca880039a18920d95100061eba0e9b2a2000a3e849cf654400147b0939eca880029ba0a73d951000536c14e7b2a2000c5d731cf65440834ed0239eca880029d60473d95100043f43887b2a200087d8710f65440014dd0421eca880029b60843d95100051f424e5b2a2000a3d849cb65440014bd07396ca880029760e72d95102f53d400e5b2a2041a79801cb65440010fd0e216ca880021f61c42d95100052f41885b2a2000a5d8310b65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440614f501b8eca880021fa1f31d95100043ec3e63b2a2000a3e84cc76
  | 6 => 0x1c5f43ee8b0c6000c3f75dd1618c001878ebba2c31800327ccb74586300061fba8e8b0c6000c3c751d1618c0031dd0fb92c3180031bdd77258630006363aee4b0c6000caf74dc9618c001958e9b92c3180021fe1572586300243e42ae4b0c60008bf845c9618c00717908b92c3180031bdd47258630006363a8e4b0c6000caf741c9618c001958e8392c31800317dd532586300064fba264b0c6001ccc724c9618c0098e8eb28ac3180123d21d515863002e3b30aea30c60008f787584618c0018eaeab08c3180021fe1576906300243e42aed20c600087f855d9418c0090f90abb283180023be09765063000c76412eca0c603d8df865c2318c00517d0fb2281180021f61e62d95300051f424c5b2a6000a3d8498b654c0010ff0eb16ca980028fe1162d95300051e422c5b2a6000a778158b654c0014e902b16ca980030f5d074d95300051f424e5b2a6000a3d849cb654c0954bd07396ca980029760e72d95300043f43885b2a600087d8710b654c0954bd06216ca980029760c42d95300063ab88e3b2a600087e87107654c0010fb0e20eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca9812a97a0c21d95300052ec1843b2a6000a7a80087654c0014f30010eca9812a1fa1f40d95300043ec3e81b2a604a87e87c83654c0010fb0f906ca980028fa1320d95300051ec2641b2a604aa5e83c83654c0014bb07906ca980030f5d754d91300245fc3aa9b2260018bf8750b644c00395ce4a16c8980028fa1662d91300051ec2cc5b226000a3f8558b644c0014790ab16c898002ade0562d91300055a40ac5b226000c3d751d7644c00147d0b396c8980028f61672d91301054f41ce5b226000a9d839cb644c00195ee5396c8980022fa1c52d91300045ec38a5b226020a9e8314b644c00153b06296c8980028fa1671d91300051ec2ce3b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b226020a9e83087644c00153b0610ec898002aea0021d91300055cc0043b2260208be87d43644c00117b0fa86c8980038ed4250d91300055b408a1b226000ab581143644c04117d0f906c8980022f61f20d91300051f42e41b226000a3d85c83644c04153d07906c898002a760f20d91300061e326eab22600087e87d95644c0010fd0e32ac89819f1edc065591300243f43eeab2260008bf845d5644c0011bf06baac8980023ee0175591300043f438eab226000c3f75dd1644c001878ebba2c898003171d773591300043fc2ae4b22600487c855c9644c00117f08b92c8980023de05725913002c7a40ae4b2260008fb805c9644c0018f0ebb82c89819b0f9db65191300045ec3cca3226065a3e85994644c00117f0eb28c898002a7e0d65191303255dc02ca3226063a3e86194644c0c587cec328c89
  | 7 => 0x3f43dd5609040187881baac1209222f21d43582410061fbaa86b048200ab88050d60904010ff0ab92c1208121f21572582410263c3aca0b0482058f88754160904014f30a182c120802ae610305824100574c1060b048205af2810c1609040b1f10e902c1208072b1c942d8d410145f424e1b1a82008fb87580605040187ee93a2cb188030f5d074596310051f420e4b2c6200a3d841c9658c4ad4bd06392cb188029760c725963100636b90e4b2c620087e87109658c4010fb0e212cb1895a97a0c42596310052ec1884b2c6200a3e84dc1658c40147b09b82cb188169da0670596311d53ac0ce0b2c6200a5f835c1658c4ad4b906b82cb188169da04705963113d3ac08e0b2c620087e87d01658c4010fb0fa02cb188169da0440596310053ac0880b2c620087e87c81658c4010fb0f902cb188028fa1320596310051ec2640b2c6256a5e83c81658c4014bb07902cb188169da0620596310053ac0c40b2c6205a7681081658c4014eb02102cb188162f21d425923100e5639284b24620487e85dc1648c4010fb0bb82c9188163da07759823102c7b40ee530462058f987882608c40b1f10e902c1188021fe1570d91310243e42ae1b2262008ef825d5644c4031d904baac8988023ee0175591310047c402eab22620087f855c9644c4090f90ab92c8988023de0572591310047dc02e4b2262008f8805c9644c4031790ea12c8988072b1c9425913100c6e43a64b226200e8d424c9644c4011f70eb00c09880a3d60775181310063ab8cea302620487f875d4604c4018eae2ba8c09880317cc975181310243f42ee4302620087d85dc8604c4051eb03b90c098803175d5321813100e67392643026202cd5714c8604c40395ce4a12c720102ad20542586400247a43aa2b0c8000a7585085619000156b0810ac320002b560c21586400057940042b0c8005c76615d461900011ef0eb08c3200031d5d561186401fc5fc32e120c800093f855c2419000b1ed033b463200171d985758c64002e5b30ae918c8000c757558631900090fd0a3b263200021f614764c6400147a43ac298c8000c5d75d4f63500031bf0e996c6a00021fe1571d8d400243e42ae3b1a80028bc845c763500011df04b8ec6a00063b20971d8d400154f436c6a1a801a8be861c143500010ff0ab9ec2a00121f21573d85402061fb22ea30a80008f78758461500018bcebb1c62a00121fa14764c5400043ec28ec98a80038bc865ce4050041938c6b9c80a00023ea0375d92300245fc3aa9b24600487e85dcb648c0010fb0bb96c9180163da0772d92300047ac0ee5b2460008fa80dcb648c00317f0ea16c9180072b9c942d923000c6fc3a65b246000e8d424cb648c0090fd0fbaac31800317ccb75586300045fc22eab0c60038bc845d5618c0011df04baac3180063b20975586300
  | 8 => 0x17080018e9958000ff0000a880008e8000000000208cb867a310df8000000000001db87b1a00ef000066984148a2e83000011481c9c18000000000001bd0af8001368b68000000000000000000000002160000000000f81fb0002020618000000000000a3a2880000000000000020900000016411080010d0000001e90e884410f86220014e1f20a791f9541719e89b48311bb21405e8fb8010000000000000000e409194798119489c0d3116800188800001008000030000000000400100e0140280e00400000800008010000000080000080500000006000002008040010000100100000000801003006000020000020000380001000000001000000020000280000200000600000004000004020030020000280201e00800003012000000040080040180000401c02006000004008000020040180000e0000080100401c00006006008000010000040000600201c008000020040080200a00c04801002000010000000000080a00400800800006008000060060000000200a00800001000010050040000640780100600403005010000008010000000080c000000000010000140000100000c000000040140080200002c0100300000400801012008000000020000080100000000001000040070090020080000000002c018000000000100000003c0500000000805800008000000050000040000001600001001000000018030000000000100000400001000038000000060000080000002c02800004000008000020140080d0020100100000a00c00801000008000010000000680700c004020000140040000100e000070010040000000001000001001004004018180000000000500000400804008004000020040040000200000c0700002000c0080300200404805004000088000000040080500a014070000000000000400400000001000034030020000100000000603001001020000008010040000000500000c0517b09baec2a180a2f61372d854322d5a40a85b0a8602c9d744cb6150c0399ce4996c2a1803a350932d85430055ac2043b0a8600ad5830876150c01d8a6410ec2a18023de1d61185430063cbaea1b028600ab984d436050c015e302286c0a18029ea1720d81430047dc3ac03028600a78855806050cd157708b00c0a180a2f61375181430055dc02a830286028bd84dc86050c0157700a10c0a180b275d1321814300e67392643028600e8d424c86050c0196882b88c0a1802ae61350181430071caa0a03028600af1811406050c014f50b900c0a1802ae61320181430056cc1e403028600ec932c806050c0b1b90e992c7208121fa147058e410043ec28e0b1c820087f855ce60904090f90ab9cc1208163e61e50982410053cc28613048200ab9840c260904015d304184c1208163e61e20982410243f43eeab048200c
  | 9 => 0x270001a31f998b0c09188368eb92200000007115d1e28002109218002018bf23a8000000000000000000000000000000000001521391ba0f697d84c1329361db00011d1288001a519e07f85f11400d99300009300019990c9042269e10288ce9b8063846a238f10000000000000721698e620c02e0001d61c708200000014a18a84b1ae81d97313e00018f8000c48000000000000159230000d28000000001490000000560000422048000000001460c89430438bc8612210a480000000000000007e0001280000100000001880381ca03a00000012b0d90000001d28ee0001a280000005580013709e86b0eb1dd0001b00002220000000000e000004e0001e19720000430269a78c71df1858000ab2030001de80016c000000153000000000206049a2f8e50001588ad8000000001fd00013d00c8000000000000000d78000c909500000007d8001f60000000000d50000170001469b309980000000000000000000000004800008d9ec8658001be8001f700014b24088a86a05c800083a1486281a0020d68a99dd8a30000348001f404b87a9cb8000001f90758b30000f602c8000000001ea80000008b00000000023096f21300008c0001f30000000000550d980016000000000000016280022805a0000ed80017123508f1c49970490b59570f08cc0b98d58ac23317c0b00001b280011f0000000fb0001e200000000000008000000000000000000000004c80000000000013b0cf87601ba0f9c50001f51a10000370000000ee80000000018b98788e20e8000230de0000bc0000280001c300000000000000000000016d8db1458bf8b103a80019d9b70000000000001030670f02158ba02b96908812a9af13a06300001288d1819e09680000000b080015f9de00000000023f0db9f00000000000928000000001d38001660001c993c8000000000000000002078000000000000000000000d88748320000000000001901741d91f800000000000008191b05680000000022d0140001290000970d600021b8000000000000000939d88f19338c51539d41a498c0001388000001fc9dca1f81499b00023e0799ab10384f0f88c187d0291ee80000000f88905f8741cc0002218000000000041d00000048781fc2240df0000000001ac00022780000000001a8528000000e280000000000014b8000ca11d87680014c8210001e68000d488fa0086800004d8000001578000f72070000001250248c39210c680021a22a0f98779b39799768790b38e70bb0cd91a80011503894515b0a71c91ea1ef00000004f8000001e600008680000000000000010204780017700000017ea3980009a042a3580015a80002b1481408000000000000000000f90000000000ca800224a1e00021014c00014f9b78001318f21b096d00019793000000022c9fe1b1
  | 10 => 0x1b20dc8000dc0fe8000000000000000000000aa8001a380022900000000780007e8000850000000f510480000021d8b41a204700000000009b1620018000002200a80650730a6a0593480021195a1d78359890000000000001ec20886600ba300b1a38000173a2700020b8000000001760001d31e98000000000001831310c80000001419e804601999c9e023286c930a0287b9e39f79658051f100009797880015e01e9fe92616701780021a80015d9c2a3c0350001b600000016e1eb80000002200004a80000016aa3680006883b80d22994f03d8988830c58af09423e9399868000608589f68d40411688190080e98f78e59a587012a1b521298c8fd0000cc8000000000b484a1b68d187f14100017801f8000000002190530258000488d80750d714982180011c8000001729378000000a200000000000000006980001382d8000920000001a41421bb80000000017b00016b80022d8bd00000010080000020e17781c1208b892793f0788001d212f0130d382d1ad1470000000330001d99200001bf8000001d18000000000001c380015e80003e06e97a8dd0000ec8001da0001b193b96b0c30f280000000000000005101209d1910981ff23480010900000000018700000019899a15600016f80003292287197900000002a8001aa81f0038000000da2081d815916a13406f89100000020a8001ff8000001051cd09022b000133000099144106000000023a1d0000000001b904097f8d20ba80000000018e0000000000001801be00000018d9918000000000398000001fd8509a60000000000000fc9b58000000e800019a80017000000000014e89b8000000848000000c022c00a0360aa051a0680000000001d00000000000000010020a1a99fa81800000011a0000000e900000000005a88a1618001581059181c111600010b09c9af8ef9c80bb9129bc8000a080005b0099ab8a58d121997c8001f28000000000000000000160000240000000001ba9b41ee0000000000cd00000010e15b87390100013211e82f8000001c89e709d8448000501940070001cc80006a96500000000012d00000000017f00000000000000010c11380014d0000000000001400001639820000001759968000a000000001e0c618d0ad05c0000000000a500020d8a40b51509082188be83f23d9e785485793f8000000001990001848a10000ff80f19c0000e38319a80001c400000e0000000000028000089448250188cf04d0590001a6a2f00005d0000f30339b98580da82f12b9f39ad8000000001fa0000002230001608000598fa08590b80a9860e10b91649130ce2012378e188b8640b602280c05e0000000000001ce97e1928a280003c23ba0500019d1239d116c96680014d8000000ea80005421c80000000000000000019600020c8001839100000648
  | 11 => 0x220872a2b9098000030000f593c00023900013e8001178e2129a319950a900011580000000015480019080000015100000010880000009f80002600000014283f8000001118001350000000000870000001380000000000001b8830a3b0b29c598521800000021b0d08001d487c0b709e0000000000001cf2400000000001ac80000000001b0002251c6800000052000000119800045a3603c8000000000001bd92d80000021713a98a0c103900019219f80023893d92e8e49e4a0992406ba2e00000000000000000000000015c02e80008880000000000000000000000000000000009611110d92f97b800126a1221689083b0ae0001dc1cf81190a22a8002321070001598c21528000000000000000c40000c78000000810000e68ac92c9dfa2600000000000000000000018980000000000011e00091700023719f0090000000000001f480016100000010a9550000000001828001e58000000fc00020d0ea0001ed00006e19e97500000021f0001068000e79d58828000001f580004011207ca228c98001c600018f08600b0000002339c78539ce19386c00000000e99b86d00689a80012c000151a178840a61e51f882a06923c9bf1a71a1974a139191da84506f10790f0000001aa0001d51ed80000017d1d720f0ae96e80007a1cd8be08c9568058001a900000000000000007080023a00023d13595f0a18968298000000000001cb21c0000000000002038000570600000000000000000001d68f39e41ca9a88e0a340340000001ae0001c080000000000000008980022580000000012589480005d8ec0000de8000000000000000000000001028ab8001d083d0b803ea040001a080000002782c0001f18000000e310e8000001efa1500023f8110000000000fd8418958000001438f480000000000004e9019f08c28378000fa89f1248000b780011b9c00001270000000000000000000cb15000000015c80000000000021e8000201e300017a0001eb1679c2000000000000000077000000198000000010887a0b0168000dd80016300606d8000001fb80008080000000000000014a8000000000d01558001bc0000f40000bd8b21808150000000000000000ed11c05b92e0fe21100000000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x75218009920034ab10c81880534da1245424cb6150c01a85844c821d8543005a2e41424c86050c01a31546045018143006a261132c806050c0103f985d074596310061360d721c9658c40388c87509325913100e23e1d424cb648c00188d83dca72d913000495662711946344001c4463189758c5100040fe61741d16504001c45651c87344010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x4b
  | 7 => 0x4c
  | 8 => 0x4d
  | 9 => 0x4e
  | 10 => 0x124b
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124c
  | 16 => 0x124d
  | 17 => 0x124e
  | 18 => 0x138b
  | 19 => 0x138c
  | 20 => 0x138d
  | 21 => 0x138e
  | 22 => 0x9cb
  | 23 => 0x9cd
  | 24 => 0x9ce
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0xa0b
  | 29 => 0xa0c
  | 30 => 0xa0e
  | 31 => 0x130b
  | 32 => 0x130c
  | 33 => 0x130e
  | 34 => 0xb4b
  | 35 => 0xb4d
  | 36 => 0xb4e
  | 37 => 0x144b
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0xb8b
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x148b
  | 44 => 0x148c
  | 45 => 0x148e
  | 46 => 0xe8b
  | 47 => 0xe8e
  | 48 => 0x94056
  | 49 => 0x95253
  | 50 => 0x94053
  | 51 => 0x124953
  | 52 => 0x124956
  | 53 => 0x95256
  | 54 => 0xb4953
  | 55 => 0xb4956
  | 56 => 0x94b56
  | 57 => 0x144953
  | 58 => 0x144956
  | 59 => 0x95456
  | 60 => 0x128a
  | 61 => 0xca
  | 62 => 0x12ca
  | 63 => 0x10a
  | 64 => 0x130a
  | 65 => 0x134a
  | 66 => 0x139256
  | 67 => 0xb5393
  | 68 => 0x138b56
  | 69 => 0xe8a
  | 70 => 0x12c9d3
  | 71 => 0x12c9d6
  | 72 => 0x10c
  | 73 => 0x180c
  | 74 => 0x134c
  | 75 => 0x14c
  | 76 => 0x12d453
  | 77 => 0x130a13
  | 78 => 0x130a16
  | 79 => 0xe8a13
  | 80 => 0xe8a16
  | 81 => 0x168d
  | 82 => 0x131493
  | 83 => 0x131496
  | 84 => 0xcd
  | 85 => 0x184c
  | 86 => 0xbcc
  | 87 => 0x16cd
  | 88 => 0x18ca
  | 89 => 0xe9493
  | 90 => 0xe9496
  | 91 => 0x4956
  | 92 => 0x14a
  | 93 => 0xbc954
  | 94 => 0x95296
  | 95 => 0x10954
  | 96 => 0x11514
  | 97 => 0x14114
  | 98 => 0x15314
  | 99 => 0x11354
  | 100 => 0x11994
  | 101 => 0x10154
  | 102 => 0x135314
  | 103 => 0x15814
  | 104 => 0x11314
  | 105 => 0xcce92
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1217
  | 6 => 2142
  | 5 => 1154
  | 4 => 14
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (49889+((h/405+packedAt gbK7 (45029+(h % 405)*12) 12) % 2137)*12) 12
  | 6 => packedAt gbK6 (111384+((h/714+packedAt gbK6 (102816+(h % 714)*12) 12) % 3421)*13) 13
  | 5 => packedAt gbK5 (72310+((h/384+packedAt gbK5 (68086+(h % 384)*11) 11) % 2026)*12) 12
  | 4 => packedAt gbK4 (1000+((h/4+packedAt gbK4 (980+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f81ffc0ffc0fffc1fffff80127ec73a33f3fc
  | 1 => 0xc0fe07ff07ff07ffe0f007ffedb179c5cc7ccf
  | 2 => 0xfffff80007fff83fff0007fff1c181fe0f8f0f
  | 3 => 0xfffffff800003ffffff8003e01fe07f00ff0
  | 4 => 0xffffffffffffc0000000003ffe0007fff000
  | 5 => 0xff00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x900294009c00a4c019534818016431811b15c
  | 1 => 0x480a02d10251069420a0552a84b05940c454c5
  | 2 => 0xb2d5580844aad02b5a00a255314180ae0a8b0a
  | 3 => 0x10e794aad00840339c4ac0063a01ac07600ea0
  | 4 => 0x20f9e73ce73ce501080300183fea0007bf6000
  | 5 => 0x3c41003080308602108c04603ffdf7f0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36775
namespace PEqualNP.Outside.L_meta_36775
open PEqualNP.Outside.L_meta_36775.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 3 := bs1_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
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
theorem bs2_4_512 : Interval s2Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 bs2_4_224))) (concat (concat (concat bs2_4_256 bs2_4_288) (concat bs2_4_320 bs2_4_352)) (concat (concat bs2_4_384 bs2_4_416) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512)))))
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
theorem bs2_5_640 : Interval s2Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
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
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 14 := bgb_4_0
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
theorem bgb_5_1152 : Interval gbAtlas 5 1152 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1154 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152))))))
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
theorem bgb_6_2112 : Interval gbAtlas 6 2112 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2142 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))))) (concat (concat (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280))) (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568))))) (concat (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824))) (concat (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)))))))
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
theorem bgb_7_1216 : Interval gbAtlas 7 1216 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1217 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)))) (concat (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056))) (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0eeeaeee0eee8eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373984 * 2 ^ 32 + 4008241856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36775.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,5]⟩,⟨.or,[2,3]⟩,⟨.and,[4,6]⟩,⟨.or,[4,5]⟩,⟨.or,[3,8]⟩,⟨.and,[7,9]⟩,⟨.or,[10,11]⟩,⟨.or,[2,11]⟩,⟨.and,[0,12]⟩,⟨.and,[1,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008241856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008241856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36775

open PEqualNP.Outside.L_meta_36775 in
theorem PEqualNP.Outside.L_meta_36775 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4008241856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4008241856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
