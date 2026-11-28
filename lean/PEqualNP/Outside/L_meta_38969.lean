import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38969.Model
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


end PEqualNP.Outside.L_meta_38969.Model

namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
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

def SBf (j : Nat) : Nat := [7, 7, 8, 6, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_38969

namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x14f8060020004400000800900c2200300009380000001fe10ff42fd41fd40fd30fe42ff32bf41fe20dc32bc40fe32ff41fe40de32fc40fe41fe31fc41fe21ff20fe30fd42fc32be40bc42fc21ff30fc42fd43fd31fd20fd10bf43ff31fc10fd21fc43ff43bd41fd32fc20fc30bd43ff10fe43ff21be42fc31ff40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1030000000300000200002d0501848d00000000000181808181028000830300080000060080000200010003808000079d8a800080010100028000808f858100ba008001020517838081030000030015840084821b001d980000071cb00080014f94840ae29a855c534827aa2216750c319faa2413e540cb3a87195b94a319e2a2413c544427aa918db14943b7290213d5390abea6884fd5020aea98813e509027aa898e7550329e2a6435e538827ca1a0cf953319eaa4433e548833884194f14941bba8a413e544c67aa998cf552439e2a4216c524c27ea990cfd51219e2a4653f548427aa8185b149109eaa6659f5350e7ca1a1cf141439ea9e83cc32486e8a290678ca40ce190813f5150e7ea6a0cf940429f2a063cc32c8678a4a1e750d309e2a2653f548c278a8985754f42af29e839f430ca7ca5204f95010cea1865cf420cb6ea2a0cf55310e6190419e53102bca419678cb419f296833e54c827aa6215714d109f2808178504867aa810dbd49309e282835e53d0b3c64a0d714d21d621065cc328831884194754f419e2a0413d5490774a0204f5532096292873e54cca78a890d754c10cea98813e548c67aa3204fd51309ea88815f534867ca820ddd45309faa2213d5190a7ca5a1e7d5232aea9c419e428cb3865204f950219f2a6613d531023aa6205794e21d621665ac5250e7aa818ded4121afa9a419e53d067ca910e7908329f284853d51d0f3a8798670cb41af29465af5250edaa518d7d4d42cea1c639c428ca7ca4214f54e40b6a90213c548c27aa9105bd4943aea9c433f544ca7ca821dd145309faa4659c3250738a9194f55032af298813d540433ca8194f95310e6210653d54cc39ca419678c8409f2a0615e53042dea4885754f41cea9e839f438cb5ca4214f94a42
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40a005410000000440020800c010102108408800000e04010016400301200201d011c318953d068c6250d30a3189438c68e6010832c3150320820c6254c40a398b548ca1d6395310c3d8c5250f0c520c941c550c514c30f6254f4187189531030d4394a318758e5090a1d650c8408b189531021f6354642a5584548cb0e520ca40c3189531028d61108328758e540868e6290832a3988548cb0f53149438e181544c62d6510832a3d94420cb4832141218b18953d070c540c9218758c540824c6254f41c3950328828c6254f418758c54c861d63141418b189544c70c540cb21a3189430c61f658c8408758e54c823561152328318953d070f6254c4093189531028c6250f30a3594420ca2e62d523087195434c21d6315210a3189531021f658cb418759432d063561150208758e544c70d43149308718953d061f6354640
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x814400228338ec629287215c7651083281aec2a064105047250c514c282b88a819041031c96314141818e4b18a90840c7258e54c4206392c72a043039cb6354640
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/30+packedAt s0K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/97+packedAt s0K4 (4455+(h % 97)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s0K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 3 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1105108c412248100594a8a25012915414d0d5
  | 2 => 0x248a29103244942960294454a6412aa8ca262a
  | 3 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 4 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38969
namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x153010414401c01c60000c90000402c508f10e000fd43fe10ff41fd42fe31be40fe43fc31fc21ff31ff42fd20bc40fe42bf41fe20fd21ff40fe41fc42ff43ff32bd41fe21fd31ff20ff30fe40fd40fc20fc32fe30fc43fd10fc40ff10fc41fd41fd30ff21fc10fd32fc30fe32
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x87069df83260c000243c1833218005001421100001ce020400014800004a080444001c817a08206001c499af29c815c534427aa2205dd4530bba8a415d5308278a8885714d42b6292615e53c86dea4a0dd14530af298213d54c827ca0205b14910b62928378505075ea4a0ce141419faa2619f53506bea6a14f550109f2a6213f54442f6a0a0db94a319eaa6215f5348338a6a0e794e40aea9c433e50d0678a8994f55221b6a94636f5244374a0206e14141aea98215c534827ca8085754e40b7290213e54cc27ea9084f952319f2a4436c5250e7ca9905b94830b7294816d520427aa3205754f21cea9c813d5490678a0a0d794c209eaa0433e50902bca710cf55231d729481cd320cadaa5206e100109eaa6616f5250ebea6884f15130b6a9061bb50506b8a6a0d7d4d419faa2653c5448358a4a0edd45419f2a063ad52902dea4984f950219faa241b840c4278a9085d145209f2a0836e52cc6daa598cf55031
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1058003ca148505071b53141418e59440043185314141a3191320cb0e5394a40c314c525072b5214141
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => 2*((h/28+packedAt s1K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s1K4 (2484+(h % 51)*7) 7) % 92)
  | 3 => 2*((h/9+packedAt s1K3 (304+(h % 9)*3) 3) % 8)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x84882808c489082016514a284a212954133615
  | 2 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_38969
namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2876f5250efea8985f14532f719065de53106faa6105f15220eea9e813d54886fca790f794f21bfaa0617d54907b865185f54c21bea9663bf41907bc631877d4d20bf28665ee52043de85216f95221dfa1881bc42d06fea8907b48421ef29c437e530cbe843085f94c41bf28e41fa300c2faa121ef50f41f690e41ec21083b86498dfd4910f6a90217d50906fca9085fd5221f721085bf4290b7e83a07bc8020bfaa2637d53486b8a6a15714d10f7102416e520c37c80a06f90942bf294817e509027aa9985f54321fc88021f721886faa021df14d10be29621dd53887ec6218f710c31df20a837d51d0efca821df54e42bf28021bd435077884a0fe88020fba0a835e53042fca318df54430bf298217d54483bc879957d4d20f6990437d511037e8220ef15110bea96877f54082d8a4a0fbc8421b7290217f54087b8a6a0df95120bea8043ef21c837c82206f50740beaa0417e50d06fea69077cc030de20c817e5210fbaa790fb94b31bf28e87ed32c82fea7085fd4121be29c417d53103ba86995754f40bda82836d52043b8a6905f94232df2a6613f544cafca521774c030f6a9663f5310c7ec4210df95010be2a4437d51c82fea2a17bd4941beaa263bd54043ec20887710e32de210817d544c2f8a8985754c42bf2a0817f5150f7a8620778c830dfaa2217f53c82f8a9085f14530beaa061ed320cafca2185f94640be29e417c53043d885997754c10eea1887bf40102f8a0a0fdc8521efa1c637f52043be64196fd0540f7a16657d508cafca8885fd5310dfaa2657d53c83be86195fd4540beaa487fb10442faa4885f94421beaa621ef42886fea710df94432bea9e83f7210437a82a05f95042bfa92617d53c42faa7a05f54032beaa485bd4210af8a8195f15231bf29e81f710042fea990d794f40aea9c81dc43cc2b8a6905f94442ef994637c534827aa8085f95031fd904415e53886fea9105f94e10fca00817e52842baa6085f95310bea9481dd324c27ca910fe10010bfa9283ec21883f420085f94e20bea9c61dc434c2fca221cf55031bf298617e5010b7887215f95331bf284857e540cbbe6218df15331bf29c43f751482faa6085754e21b6292217f52842fca890fbcca32bf2a4657d5310b7c87215f54643bea8c65dc53442faa710fd08410fba0c83ef20883d88510df94831ee99661ef4250bbc8618778c932bfa9281bd411077e84215f942309f2a6617e520cbda84215f54830ef21a655d53c86faa3205f54b40dea0081be540c6fea2985f55230bea9c81f521086fca898df54443bfaa465dd310c7b863185fd5331bea94417c54c83f6a0a0f7cc730bf29687bf54482f8a9195f54843bfa92636d52cc6f8a8885f14143beaa2657d53c86fca1085f94231af29c81df53506faa8885f95020b7a92217d54902fea098df14943
  | 1 => 0xe5390efca621df94b31ef98a61ef42483ba8698df14f10beaa4637e51083baa620f7d0c31bea8c857e50c86bea688778c430bf280437c54c86f8a790f70c830beaa4657e508877c85205fd4c20ae29a837c50487de64995fd4d10f7108417d50107bc65184f95010ef196637d54887bc60985f95030beaa6637e52086f8a898df54841aea98837e51042faa720ef15120be282657c5150afca3105f54740ee98e617e5090fba62985f94343beaa4217850507d8a4885f54c41ef29c817e54087baa7207b54830bea80637f5250efca9185f15230efa9a857e5390afaa6905f54221bea8885ed21482dea4a0ef50c43bfa98217e50906fca720df14d40bf29a41bc4310afaa890f78c931ba28a417f540cafca4886f90d43f7192417c53486faa1997710c32df218857c51502fca820ef90b41bf28c617e51887d8a4a1df94830bf29661df320c6faa521df55330fd20081fb40c42fca3215f54840bf28081ec52507b88718df54331f729481ef21886f8a2a1df94820bfa82857c54486fea2905f54732ef298416d52903da6510efd0e40deaa4437f53086fca7905f94840bf29e837f548c3ba87995f54420bf288637e52042fca3985794c42fc90041ef5250ebca620f790f31beaa643ef52442fca198df15030bf28c65de434c6fca8987dcc631be290217f54ccafca6105794c20beaa0657c54083ea8220df14930bfa9c417d50d07be86a1df14d41bea9021de314c6fca621774ca31b6a9061ed20082f8a6a15f14c20bf298637f548c6f8a4a0dfd5132ee29a857e54c86faa5085f14142be2a6217f50506faa3987bd0821bfa9e43ec42087d88590774c832bf298437e53486fca0105fd4132df212837e51d03bc87187b108329f2a063be41902fca4217754c42bea9461ef42c837aa818dfd4b10f7a10657e500c2fca3a15f54432bf290837e52c42faa5885f94b40bf294613c54442faa3084f15120efa1e617e500cafaa718df14e10bfaa4217d54087f681205f14520efa9a217c54087ee6298fbc8520efa1a61bd54cc2f8a508770cb31dfa1e837e5344278a8997ec8120bf29881ed32482faa518ef50e40ef996617d54c82fca9105f94643ef29e817d54042fea690efd0240de214815f5350bbe87195f54831df21081df324c2fea6a04fd5110bea9e855f53507dca4185f94440bf2a4437f5350bdc43105f55332be2a6616e52cc7dc6410df55031bfaa243df328cb7e86a0fe14141de2a2657c540c7ee43085f54630ee188617e5290fdc659077cc631bea9c21ed52903ba6418fd90441be2a6657e500c6faa1a15f95330fb884217d51882fca220df94041be29221dd430c2faa0215f94a41bf296837c53886fca1a17754c20bea9a217d50d0fbe8721df94043bea84856c5250efea7887794c10aea98415e53c87f661185fd4d41bfa8
  | 2 => 0x80740b0000100c0b02011004030e0090082c040100080407c1b000011644a000000f8011f02310c46004300e40b0440002003014380000100c8b50c4b004010300800c0c1b80c2cc3d0000c0000a0200200c160700200008000000041f03800008000200103cc6000010005700001018001949d0040c1140000000058370644b10800038180440500c000003a000190ac0204823008000e003040410601400026004060101201c00000002d0000680301800578a903c0301c11000000100e012320140304800008540000017808078000400d050d100808854cf01c1902c0a000010601903c0a0004400400018020000500410000030041100802000191380a1203f0100101c0e0280000017240141340b010010900000002004020880b018010000f004040140120c0000c020001917400030010080e058000440800002a282f0080000c0707002be28263fb304c2fea818df95332be2a2417e53902fca9905f54e20de208817f54cc2faa9107794c42dfa18877f54042fca7a17750f31df2a0216e52902fea9905f54a41bea96837e544cb7e8721df15132bf294637751483f680087b8ca21bf294657f514cafaa118f7cc230be2a0217d538cafaa510fec4210bfaa2217e50882fca320fe10310eea1c613f54482fca3997b88521fa880217c52502fca918df54742fda0281f9300c2fca7885f14c21f6212417d52cc3bc8621fd14520be292637
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x8538423e6414c108f99253842ac644c832d3d0c5250e5e63d5010b358b31cc2776154910d354e529026e6294343ce181540423e64d4e21a758c42d074d528c8309b58b54042cd62cc431a7593308c25e63d5210c755132cc25f654c8318f993530429c644c832d6d4f505072f54d4910ab191328866e6295110c7952530425d6594c20b9185200838e4310b3297596530426c654c9209798c54c825f6550c438f590520425e63150109758e548826f6255110d3548320c23d64d4e20c755043cc26e62150108fd91534863d64d4e219b189540c65d6315321c795153042e46244010d394e328871c53909419718d528426d62d52109d58454cca5c63551109b98b54cc66e6215030c7551320c69d6310a40cb18954cc2cd62cc6319e58354cc71f54d4d109b98b548c66e62d52109758e529066e6214131c7d53534825e6314c108fd91500876852141419b98b530426e62148109758f540429d63d00409718d54c425e63153218f590514c26d629434397d95310c69d63d0240a7191328c65c6550d31cb550428867561150208fd91534831d53d044197996434ca3c6454d209d586534834d5394810cb9525204277654c4319798c544865d63d4b10cd153514826d6294f108fd91528425c6354b419b98a534423d6494d109798e51086756115030c7551538867960d5321d9d0851482b860504419798c515034f53d4910d918552042766194d209b997424829d64cc0309b98b548c25c6355021a758c419026d629511097997434c25e6315031c718d540c63e64150319b58a534866d62d4c109798e529066e62d5010b358c42cca6e65c8520a719132cc2cd6310821d954b210427b6054d219b988530423d6414c10ce908505063e6414530d5d4c514825d65d0c31a7191324c25e6314121ab18943d066c62547439ed81544425d6590c3097994534831c53d0d41b358c424831d5350740cb548429033943141419b189544c66f6254d109758f548865e63d5220cb951520434f5314941cb191520c25d6314540b358f210874c53d0920c7551310c66c625463097996434c74e5394810d394e52902cd6310b208f191524426d65948108f191520c31d54cc4319b189544425e6394642d3d4f525063e65151109e181544865c63551209e98354cc65c63540219798c548869c644c831d9145214834c53d09429718d5090a5d63152219dd95411072f52109419e181544c6cd62cc530d354c210831d631513297d8d51d0b1d5454c109b588504c65c63548408fd91534434c6254c429758e544c25f6354840cb150524423f6550040d354832cc65e63d48108f592518ca5d63150208f596540431c548c9329d185544827a60d5032ab1894310f2f5410920d354a32cc65c63544409758f548823e64951329b594420cb4d5354810b31894310ecc6250c30
  | 1 => 0x874e5310a21a758c42506786054d219798c540874e43548309799453442796015021c7553430c65f63551209798e548823e6414c218fd9152cc71d54cc8319758e52c42796014c21b358c428865e6394821c754f41d032f62552219b58b540c27b6544010cdd50514835b5314141d514c514825d6314121d914a104423e64d48108f596411031d544c730b9584420866d6215331cbd89540c65e6394d208f992510865e63d50309798c54c423d64944219b18954c423c6454021a758c421035853d4141c794e42903384214141b358f218863c64542329bd95320caac6250c40ab191320866e6214e10a7590318c25d63944218f993538823d64d48108f994544cb1d54cc7309798e524423c64542319ed81544863d6494e109b988530826e62d502097596320c34d52cc0309b98854cc72d54548109bd8954cc31d5410c319758e544426f6255132c794c429034d4354830b3189434cb4d5388420d314f525065e650c9318f994544826c62544409ed95300c23c6454d10c718d54cc23d6494910cbd8954cc26f62551218f992534826f6254630b3189438c23f6550c438f596540c69c63508429758f548426e62d50309e98354c876852d4141ab191324825e63149408fd91508c676611503097d8d5090a5e63d4b108f593530425e63951209bd95200825e6314a10d350d52cc65d6510c32d94c8514827765484218f590530863d6414f108f592530c25e63d5020d3548310c26d62d5230d354a310c2ac644cb209b18953442b96010840c7951538871c5414d208f99352c434d6294e219b58b54cc72c54cc932ae191100427461551309758e520873a4114141d394f428865c6354241ae18141d025f63544409b98a50d063e64949109758c544876b5214141c7d50534423e65d0540a7590310c34d524c030d3588534825f63540219798e52c426e62949109d594210425f63542419758c54c425e6314c20cdd53514825d639434297597430ca3e6414e21cbd9152cc63f65508429758c520425c63549109798e51c826f6255031d394d529033954d0010d314c525063d6494720d390d52cc66d658c8219718d51d0b1c5414d10cb189540c676619512097d8d524425f6550c30cb19152cc734541452097d8d52d075453d45208f992518ca6e6294f108f99251c825d63947209d185534823e64150108f992544831d5494e219798e548425e63150209758c528426d6215010d314f524425e63951109798e50d0b1d54ccb30c754d411065c6550d32cb90c5250ecc6250d31c7151434ca9d6310440c755343cc26c6255330c7152434cb2d62d5120c7153534425e6510d308f99053c427965840109758e524426d65884209718d54c827761551309e583540ca5d63d481097d8d544c63c6454d218f99053c832c54d4910b318943cc66f62553109b58
  | 2 => 0x88c004260000b5a0316c41104c000608e0380156c010800800423028000d00165c0b0000301c1824004004000080a0000001c0901c0b00c001f40500047134000300400c0f0041b11c6e239bc0040640d1817c085b8e30340e0c0003b8445d451180a018c000242101000220ac0040b1484012c1100400348002c4000040100000124540447e050000f0000481004400008002ec02000000002d2083d42c00000000101e0240500c00008050940b05c8c0981b0000318c0203c2707c170fc03034810403c0f85e1a8002b8320003a1811d000a60695a044000001111996008050615460800078240ec00000b30202f01000008060644231c000ed1e0100b5fc000032f5414910d914620482cd63c87208fd95411074c53149109758c540434c538c9209e980540867b6548020d9147214825d63946429b58a534431c54d4d209bd95210865e63d53218f990520423e6494c3097d8d54c423e649511097d8d540865e6314810ced0c505065d6510c31d354d529026f62551309dd95100423f64542329bd954210acd63c8520d314c424826d6215030c714c425063c6454a10b318d4210b4e53548109798c540cb4d53c80209dd85534827b60551319758e548425e6394d108fd91524426c625513097d8d54c831e53d0e409758e50d066f62544409b594420874d5348020c714e4250a3f645483097997314c36632145209bd8951d0e7661150209b994524433854c411097d8d528431d5390c42d9108514825d658c4309d98454cca6d6214c10c7d50534835753d45209d586544825f654c0308f59253482cc6250f329e980530865f63551328f19152cc65c63551219758e54482b86050540e310c420ca5f6355110c7552530423e6494d109798f548865f654c8329758c540865d6314940d3d4c524436b52d41419758f540832d54948108f59352c425c63546209758c54c823d6414e219b58b548c71e5494e2197d8d544872f64548308f59053c825f63546209e594400427b65500409dd85544826f62551319798e50d065e65cc9309b58a50d06ac6250e40ab189435075853141419758f54c
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x11411110200010c00419158c51c8520c1aa8b166218c4d7614c4248306b22a418861135da5310a21838ecaa265985287250c505070ca98c0a08838359152cc030a18e8b14a710c1c76551320c722a98c2900418318c6255330a8ae6210a29060c54189434ca923a26428a41431c95410f30a18e8a90641850c7454832cc706318c4aa0638654c6050740a18e4aa08618e0d5458b31cc28cb988428283431d16214d20
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x101080c8755162cc73080c8759152cc03080c87591520c43080c8755162cc431
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
  | 7 => 2*((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s2K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/263+packedAt s2K5 (17928+(h % 263)*10) 10) % 664)
  | 4 => 2*((h/207+packedAt s2K4 (20482+(h % 207)*10) 10) % 539)
  | 3 => 2*((h/15+packedAt s2K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s2K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf03ffff81fffff81fffff83fff03fffcfc7e3f
  | 1 => 0xffc0fffffffffffe07c0ffc1ffffffff238fff
  | 3 => 0xffff01ffe03f83fff800fffe1ffc1e03c3f3cc
  | 4 => 0x1ffffc003ffffff00001fffe003fc03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x94841408c48910805945280a252132a84c3615
  | 1 => 0x2112289109124116029052414a4645512188ea
  | 3 => 0xc28a4d2243a416aaa8249cac13a9181ac2d34c
  | 4 => 0x8b2cb1c492075bcd34f606291cf39063f403b0
  | 5 => 0xc30c1871c386371c738e73180c20183bb6c00
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88cc888888eeaaee88cc888888eeaaee88cc888888eeaaee88cc888888eeaaee88cc888888eeaaee88cc888888eeaaee88cc888888eeaaee88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38969
namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4c00804010042df43bf41bc40be43dc30de30bf42dd31dc43dd329c43bd42bc43be40df32bd41df31
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x80000080000000601000001800247151318ea90871e548c23aa221c714d428e2a6631c540c238a8994794e408f280871e5390e38a9994714d41
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x148558454cca0d621533183588540c2156115030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
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
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/12+packedAt s3K4 (272+(h % 12)*5) 5) % 17)
  | 3 => 2*((h/32+packedAt s3K3 (351+(h % 32)*4) 4) % 13)
  | 2 => 2*((h/8+packedAt s3K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 1 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 2 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8108111084820000a5090089008902940c5145
  | 1 => 0x24112209091030940a42485248525028a12492
  | 2 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38969
namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5000240030bd429c43df43dd32be43bc43df32dc43bf42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x100a00040018e5210e3ca721cb548438e29a851c54ccb1aa421c7151328ea90878d424ca1aa421d354843
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x20c6550932
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 11
  | 2 => 1
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
  | 3 => 2*((h/10+packedAt s4K3 (297+(h % 10)*4) 4) % 11)
  | 2 => 2*((h/1+packedAt s4K2 (38+(h % 1)*1) 1) % 1)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe0fffe0ffff87f83ff0fe1ff87fe0ffd1cf3cf
  | 1 => 0xff07fff07fff87fc1ff0fe1ff87ff07ee33cf3
  | 2 => 0xfff83fff83fff8ffe000ffe3ff8fff8303cf3c
  | 3 => 0x3ffffc0000ffffff0003fff00003fc0fc0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2810822210908000a5012024809205280c5145
  | 1 => 0x42410441212008140a1042090824a050612492
  | 2 => 0x842228840a4441a94088954255094a03028a28
  | 3 => 0x16b5b129487552ce73aa1103e640631bb40fc0
  | 5 => 0x18c621ce738664f39cccf99044018c63dbf000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeee8eee8e8e8e8e8eee8eee8e8e8e8e8eee8eee8e8e8e8e8eee8eee8e8e8e8e8eee8eee8e8e8e8e8eee8eee8e8e8e8e8eee8eee8e8e8e8e8eee8eee8e8e8e8e8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38969
namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3000407020bc43dc439c43bd40bf40dd30df30be43df43
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6000031595010e72a021e6940438ea8087995010e38a8984715330cca0261195010e38a6a04794e43
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2186550130
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 11
  | 2 => 1
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
  | 4 => 2*((h/10+packedAt s5K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/10+packedAt s5K3 (297+(h % 10)*4) 4) % 11)
  | 2 => 2*((h/1+packedAt s5K2 (38+(h % 1)*1) 1) % 1)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe0fffe0ffff8ff83e1f0e3ff8ffe0ffe20f3cf
  | 1 => 0xff07fff07fff0ffc01fffc3ff0fff07c3f3cf3
  | 2 => 0xfff83fff83fff0fffe00ffc3ff0fff83c3cf3c
  | 3 => 0x3ffffc0000ffffff0003fff00003fc0fc0
  | 4 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2810a22210918880b05822648992052a205145
  | 1 => 0x424104412120101400a144091024a0500d2492
  | 2 => 0x842208840a4001294200888222094a00c28a28
  | 3 => 0x16b5b1294872aace753a0223ccc0631b740fc0
  | 4 => 0x18c621ce7384ccf399ccf33008818c63bbf000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8fce8e8e8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38969
namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x403403850310010c00800000064417410000000803820c00200000000c200000254700900ff10001fc43007f50c01fe53007fcc007fc32007f950077d52007fd0005fe2101ffd4807fd32007f55003fe20007f4c005ff1001ff94801fc54017f14407fc5201ff10801ff5101ff8c801fe43007f54001ff53007f14c03fe5001ff50805fe51007fd0401ff4300ff84007ff32007fd5007fd2100ff08001ff3101dfd4801fd51017f08401fd3101ff54803fc5000ff8c003fc1000ff0c001fd10007f54c07fe42007f50407ff21017f10405fe3101ffd0805fc31007f50007ff20017f90401ff5000ff90007fd20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x86a800ffd0d31005feca98807fe504c00dfeaa08600bfd915100df8c0a181bfc425047b7eb2ca803bf98b5002ffac12980bfc314403ffe906a215ff5093103ffcc7aa00efc62cc40ffe292a802ffc434100ff8a0a8003ff65500057e30e6032ff0425300ffc6088002fd65d0c03fe9822003bf98953017fca2a881ffe62d400dffaa68600efd51400fffc85a889bfe5090c75ff900a801ff04330037fec7a0007f610440037e306a806ffd874302ffcc22181ffc52d4c23fea12a03dff18954107f8a021803ff435400b7fb2e6206fdd0541037fac7a08abfc51d0c01ff21a2000ffd85301b7fe21a9802fd6195003fc2028000bf584531fffca32a00bff4150429ff282623fff0c65400ffca0a8007ff5050001eea1e6001ffc4330006f8caa181ffc5115001feb1aa839ff8c45400ff86098007fc4054005fe10a8205ffd0c43007fec0a085fff20cc451ffa948602ff4c5101bffc65a981bfc62d00577eb168600efd9153005fac3a98e3fc101500fffa96a007ffd4953145fac521802fd6590c013e32a8602bf986530cffaa4a081bff41d000ffe282a62eff4845302ff86121863fc205042bffa926207ff94354037fec42a01bfd65d000bff18e6025ff48143176faa429826fd624c001feb22a202f78c73100ff8a1a8017fd6110c33ffb128233ffc425306ffec4a0003fd635440dfe32e8205ff0c13120ff861aa003ff544400ddfa1e8000ff58154037f880a08dbfe31d4c03fea82200ddfd494012ffc84a18037d51d401fdea168007ff55351017f883a0817fe6294c077f312a006ff9974102efea62981ffc50d44037f3028205ff8cb30107fca02180efc62d400d7fb168000ff10d100f7fc41a880efe62d0005fe0826200ff54f4301df8c5a8827dd324c001fe322a23dff9495403ffea4a8007fc3054003fe906a000ffd4d4102ff8c3298c7fd6254c05fe28a2006ffd8254007fac6a00c7fd4254c73ff880a806ff10b40015f8c221806fc605506dfe20ea601ff84330007fa839801ffd63d500ffe316a006ff10454037f8a8a0803fd605047dfe084a810ff905501effa42aa017fd61cc00fffb06a237ffc8353057f88398073fe60544077f3128005ff8c65309ffc85a800bfe10d0405ff882a214ff08131037fc83a00affc52d0c23ffb12a000ff94d41007f8c6a008ffc2050c01fe29a8000ff9953002ffc65298bffe5054c0dfe30e8000ff55143007fec2aa017fc6294c01ffa1ea219ff189411affc21a98ffff109500dff2068205ffd8a53037fac5a0803fe644c005ff90a8201bf9805400ff881a0007fe20d003ffea16a20fff54b4000ff841a00ef7c505503dfe106a206bf9933002ffac229803fd534400ffe280a60dffcc9400bffaa59880bde314c40fbe2a0a600bf58d10035f8c8980ebfd321500dff204a817ff10b31
  | 1 => 0xfff5354401ff2a6603cff0c554007fec2a0007be405000dfeb00a800ffd8d5103ffac1a98b37e5014c01ee98e6000df5455003ffcc3a8027fe424c001ffb22a600dfd9543037fcc62a04fff32d400bfe196600aff88730015f8c3aa01b7f541500dfe21a8002bf9865401dfcc4880ebff21150037f304a804ff8c91019ffc43298a7fe10d0c33ffa928200bf594431effe40aa01bfe62d0409fc9022006bf99053017fa43a881ffc5494c017fb22a628ff90a43037fc842181bff42d0405df20e8200df19510037fac3a180bfd414400fff306a200ffd0f50004facba0003fd5350057fe9968600f714f4303ffac1a8802fd60d5005fe20a2006ff90343205fac52a01afe6444005ff18a8200dfd515100fe82088003df5310c2bff2126200ff55331017fe42a88dbfc21d4c0bfe326602bffc834302ffacb21803bd545040dfea168007ff1835102ffcc929903ff219500bff300a637ffd0b53036fea92a0027f6550c0dffb168618ff0c14103ffcc3a990ffd20d5001ff2a4a600bf58653057f84398016fc6590c03fe902a0009fd953002ff8cb2181ffc63d502dfe2866203bf18b5403f7ea8aa047fe4254001feb0a6002df14551007f8a998803ff6454001feaa2603bff8c15421ffc85aa0ebfc3215003ff0822007ff1515100df8c02a01bfe5415063ff312a622ff4804303ff8c1aa01ffc5414c0bdfa1c8606ff508431a7fe8529813fc62440037f302a619ff5894103ffca3a9836fd6250001feb2a8022ffd484319ff84329877fc32544037f306a200ff5524312ffa42a1837fc52500037f300a607f7d4d53207f8652a05bfe50cc403ffa022001ff9011002ffe642981bff63150017eb06a203bf98a43027fa6488017fc3010c05ff10aa21dff58951007fea2a00977d5250c2ffea166205ff5973014ffc61a1803fe5454415ff28e6000ff5813100ff8a098003fd544c40bff320a605bfd9331006fca7a88fffe219500fffb0ea639ff0845407ffea5a0047fc625400bfe18e8606ff90f4103ff8c5a8817fe6210c51dfa148600ff50d4002ffec598817fc6110c19fe30a8000ffd0d30137f8a12181bff421500fff288a801ffc8110005fec098807fc30d00015e322a601bf18351017fc2198817fe64cc40fffaa2a802ffcc51002ffe872181ffc62d4c05df20a8209ff50930007f8c89804ffd21d4001fe31a8200bfd815401dfcc4aa01eff62d50017eb0e8000ff1913101df8c4a8006fc6095031ff1028200ff5515000dfac1a0053fc504c40dff32e8006ffd0a5409efaa5a80cffe5194c0ffe28aa805ff59253007f8ca9800bfc21544077e310a802bf987300bffea598803fd5454c01ffb0aa005ff0c3310effe84a88d7fc10d4c7ffe10ca81bff8cb4104ffea498002fd64cc001fe322a019ef50941015fcc2aa08ffc6050c0ffe2
  | 2 => 0x5300ffc80a0027fd214c035fe106821aff8834103efea5a88f3fc615500bfeb00a607ff58354037f8c1a0837fd32500037f306a611ff989501bff885a9867fd205043f7eb16a200dfd953003ffaa5a981bfe42d0037fea968200ff5815100ef8a1a8063fe605040bff992a63dff8c954007fa87a80dfff21d4c0bfe994a60bff10b30037f8842a02bfe41cc00bfeb288606ff5974304efaa498002fd65cc401ffb02a601ff9434002ffea721817fc6414c037fb02a001bf1804302f7a8621816fe6394c0fffa96a801ffc814006ffca4a0003ff53d0401ff322a228ff48643037be86a1817fd6210c0d7e322a029ff0434305ffe859800bf6214406bfe106a600ffd07301affc41a98d7fc40d4c0ffe29ea207ff18b54037f8a921847fd2154001ff98a8005bfd8a43157fc63a182ffd52cc005fe90a623cff8c554015fecaa882fdd32cc003fe206601fffccb5103dfccba1817ff64cc403fea026000bf5951000ffc41980077e50d400dfe20ca83eff8825401dfcc498817fc65cc419fe18a8005ff98a430aefaa498802ff6350469fe214a607ff94853007fec6880a3fd4290c4bbfa928605ffd80530affcc498817fc62cc40bffa9e6002ff08741157fe21a18f7fd325500b7e31aa801ff4834021ffa43aa00bff21d0401ffb026205ffd97311edfec4aa01bfd63950037f306861dffd8951035f8c8a980afc615405fff302a605f790f3008efaa4a80a3fd2090c01ff21a8034ff54a5302ffccb9808bfd2110c03ff1828006ff98b40007faa8a090f7d52d5001ff29e821dff1095106dfec4a0006fe605440dff208a805bf98d10037fec5a0016ff6510c0ffe326a632ff08253197fc412981ffd63d400ffe30ea00cff9854000ff82088003ff654c40bfe29a8605f7cc73003ef8a029806fe6094c05ff20aa2009f997401c7f8402a00efc6214c03ef1866005ffd864305ffe439801bfc54d040fbfa96a006ff10054017ec83a08e3fe2015045bea908600ff94d51005fec0a981ffd5215047fe2828600f7d4d300e7f880a8807fd505000dff3068207bf19510007fecaa081ffe54d4c01feb028605ff94f3018efaa4a9803fd315000dff2a6823bff8415400ffe20880affe32d0c0bff9928600cfd52540bffa4198873fe20544017eb22601bff0cb41037fec52a01ffc54d4c0dffa1a8201ff14340017faa3a0803ff545000bffb048600ef1915300ff481a000bfe21d043bfe312a21dff54951015f8c3a8027fd624c033fea128200ef5054002ff8c429873fc2054481fea94a800ff15330037f8812a016fc635000dfe20e863eff082541dffc80aa01bfd54d0003fe9026007ff14f5002ffac52187f7d52d4463fe90aa60cff1454003ffac5a880afc61d4c6dff10ea600ff547300c7fca0a08d3ff2194c0dffa1e8005ff0cb53017fc628801
  | 3 => 0xe2a68605ff14f3100ff820a001ffc52d44057f32ea205ff8c05300778a8a00eafd62150077f3128206f7d0e43187fcc2a9802fd6115003ffa82a000ffd814303efea429802fd63150377eb168205ff0c45302dfcc7a0013ff62440037e306a606ff98454036facba0017fc30d4c17ffa966000ff9954002ff8a69800bfd2150483bf286a805ff58a5300efca0a800efe6250c017fb028605ffccb3102ff865a181ffc51d4003ff8828015dfd4931197fca12981bfe63d0401feb22602bff94b4300ff8619800bff2144001fe21ea028ff54a43007fac2a8003fd5350c55ff10e8606bfd8b43037fcc02a01bfd429500fff296a21dff50951007fca6880677d525040dff2a68600df55351037fe86a1897fe5250c01deaa68200bf5954303ffca02a0c6fd6594c0bfe29a6223ff98143115fac421817fc5390c0dff3168607dfd4b54177fa4029817ff324c0057e30aa605ff1804308efea4a8002ff6154c077e3148607ffd4b51037f8cba1803fc544400fffb26a207ffd4a53027f86488017fd6010c0dfe206820dff8c94012ff8a4a181ffd53d4045ff9088602df94751037fec72a0d7fe30d4c0ddfa168201f70c13002ff861298c7fe4254c0ddf2a68210ff1855002ffe6521897fe6250c01fea1ea207ffd48541e7fca2aa073fe505440bffb288600bf59540157f843a181bff62d0419ff18a801bff4cb411f7fca12a00aff6154405ff18e8206ffd0b43007fec6a0037bf4250071fe180a802ff0c74105dfac59800bfc10d040fffb06a605ffcc931017faa28803ffd21d00277eb16a002ff8851015fbe65a181fff529500dfe20a8007ffd5053037fca8a0803fe544400bffb166007ff14853037fcc52a01ffc535401fbea968005ffd88530cffc84a0803fd415000fff316a607bf99541007fcc6a080efe62cc00ffe296a000bfd854303ffea4a8867fc3250405fea8a8206ff98854005fac1a080bfe4150405ff10a8207ff1445321ffe65aa063fc50504057f30aa611ffcc950037facba081fff51d4037dea168205ff14c430e7f860a88027c654c00bdf21a8600ff58554005fac02180afc615000dfe216822aff947431effac4aa016ff6590c7dfe184a831dfd495302ffe8798816ff62cc40dffb00a817ff90b310bfba6598803fc6454c0b7e32e6002ff5473100ffc20a000bfc21440077f3166202ffd0731005fac1a1896fd6490c77fe082a802ff947410b7f84198807fc20cc02bfeb126217df54b3102ffe6421813ff424400fff296a003bf18a5403dfec5a981ffc60d4c29ff1026202ff907410affa4098802ff65500013fb2a2000ffd9110017fa43988f3ff105500bfea98a601bf98243037fac3a000afe61d400fdeaa0a800ff18d5103ffac5a8017ff5394c0bfe194a607ff18f50005fac7a800bfe5144003ffa028033ff906
  | 4 => 0x8677f5250401dfaa68006ff95140005fec6a0007fe10d4043fe2888606ff10154006fca6a8803ff6150c0bff30ca631ffd8953037faa9a0807fe40d400bff3166234ff482531effaa4aa003fe6354401ff32a8605ff8c45303ffac7a88037e5494c33ff3128200ff90f5102ffc6429803fd434c0017eb1ea20dff1894003ff8a2a9803fd535400fffaa2a613ff4cb5001dfcc4a881efe6550c0dff210a83bff081541a7fc8529833fc215000bfea1e6201bf1825316ff8822981bfd61950057e308a815ff94931037f8c3a18bffc6054c0ffe282a205bf1944307ffe65a001bff42500237eb12a01aff143411d7fa402a01bff60d0c0dfeaa0a831ff1895303ffaa9a980efc624400dfe2168607bfd8b5100df8c0a980aff614c401fe29a8225ffd89430077e82a001ffc5254001feaa66005ff54c4302ff862a1877fd205440bff3266001bf1815103ffcc7a8817fd6414c057f30a8001ef10140207fa412a01bfe41d0c47ff1828625bfd894301dfcc5a1817ff6590c01feb22a007ffd535100dfac19800afe63cc47bff90aa839ff8845415ffaa5a1867ff325040fffa8aa000ff5515107efea5a001bff43d040bfe3288605ff5973100dfec69800efc62cc0017fb02a22cff9005302ffc86a1877fe4254401ff98ea00cff94540037f881a180bfe4144053fe1068600ff59153037fa85a08b3fe1014c037f306a807ff59353005fac02980efc62d040bff3048606ff90a5400ff8a198003fc53d000b7fb2e6005bf98c43007f887a8816fc635400b7e31a8200ffd4f43017f8a3a8847fe5254005ffa0a2000efd5243097f863a8003fd434c409fe2122000ff18d10036fccba00c3fc6154c01feaa4a606ffd095400ffc61a8016fe63d440d7f326a000df1953000ffea098003ff6154c6ffea16a601fe8c3300befea598817ff43cc01f7eb16801bffd4b41015fac39886bfe50d0401ffa1aa205ff4c853116fea421803fd4354003fe1022022ff9484303ff8a12982ffd42cc00f7f32e6206ffd974103ffec3aa01bfd60950637fb12a607ff54f5103dfcca2a003ff5450c01ff21ea007ff9935303ff8a4a981f7c50d500bfd9826036ff9075304efea4980cbfc4094c57ff90e8601ff94330007fcc8a98077c5054009fea922001ff1011000ffc408801afe644c40b7f31c8600ff4c750007fea68806bfc30d040bffb066202bf9874000dfac1a801ffe64d40017fb0aa801fe9435001df8c4aa017ff64cc00b7e3266205bfd88531eff864aa002ff6150001feb2a8606ff9515402ffec52181bff61d0005bf28aa205ff94f4303ff8a02a003bd43d000bfea188634ff50a5301df8c4a9893fc5150c0bbf29aa607ffd5350015f8c32a01efe6510c01dfaa08631ff9495300ffe60880c7fd2054c01feb222007ff14254007fec6aa01fff52d4c0df
  | 5 => 0x533102ff861a181bfc425005dff900a600ffd474005efaa59801bfe6195049ff8828606ff98f4002fbe6421803ff315400bfe3266231ff4c953035fec5a080efc6294c01ffb2a2002bf18554017fea2a0807fc10d40037fb022001ff08140005fac99881fff62d4403df2068022ffc8043067fc82a000efe6294c5fff082a600ffd0d10005fac02a007f85054001ff32a2006ff9874303ffca229813fd424400dfeb14a805ff90d31037fac1a1803fd53d00037e300a600ef90d4102ff8c02981bff4150021fe18aa007f754c5300ff880a0017fd64cc003ff102802fff9015306ffaa4a000aff634c401ffaa26019ff9494115ffea5a181fff64d4069fe90ca600bf5873020ffc61aa017fc43cc449ff18a8601ff54130015fcc9a0826ff624c049fe30a8601ff8c150017f8a398813fd624403fff906a206ff90654007fc86a800afe61d500fff306a800ff4c55000ffa8198017fc3110c01ffa9a8040df54a5400ffca088017fe61cc005ff086a200bf587541d7fa422a0fffe319500bfe21a6025ff8c9430fffa65a8803fe6354001ffaa4860fff14b4000ff060980177f5394c63ff902a63adf54854037f8c1a1803fe655040bfe30e6000bf5825413ff8a32187bfe40d4459fe080a608ff14530035f8cba0803fe635500bff1808606ff10543005fac121803dc635500dfe20aa812ff8c750007fcc898803fd615000fff326a240ff486541effec4aa003ff544c405fe90aa2009f1951002ffc862181ffe52d50057eb0e8200ff1911007ffca5a0016ff6294c017fb226213ff8cb50015f8c2a1817fd53cc409ffa922000f7d4f3003ffac3a9802fd6414c017eb1e821ddf54951007f8caa001efc6550403ffa868000b718d540dffa41a0837ff2150053ff1068606ff18854035fcc929807fc304400f7f32e8200bf5953002ff88698817f7314c479ff10aa806ff90b41037f8a8a0017fc3154c01ff29a8000ef10d4101df8c4980dffd20d4c05fe28a6207ffd51501e7f842aa017ff6110c2ffe2966212ff107501dffcc0aa003fd41d4001fea9a6026ef9024317ffc60a988ffe1050c0ffe28aa002fd0c53102dfcc7a8017ff6194c05ffa8e6209ff94930006f8a92981ffc50d4c037fb0a2037ff90b53007fec8a8817fe6510c0dfea1e8022ff1484301df8c42181fdf5394c4bfe992862dffc405311ffc80a181bff5410c0bfea9c8601ff48330007fac2a18a3fc5290c0ffe296a800bf58743007f886a800bfc105442bfe2926202ffd45310377ca82a007ff20d400b7f31ca809ff1493000dfec8a0017fc6290c037fb028002ff0c751005fac89881afe64d4417ff2166025ffc8143037fa842a01ffe63d4001fea9a6206ff1825406ff864a00effe205502fff2966200ff54540007fea298083be4010c19ff10a801eff8c351147fca521
  | 6 => 0xbfe190a621ffc404302ffc652180efc6250003ff9068006bf19743047f88298017fd6090c03fe1828005ff14f300057ec89801ffe54d4049fe10a8612ff887501a6fea52981bdd4310c0dff2168642ff90754037f881aa01bff4250c79ff20aa807ffd8f5102fb8a62190bfe31d500dfe21a8207fdd45510affc6498817ff32d4c0b7e3266000ffcc740017fa82988bffc1054c0dff31ca809ff1893003ffcc5a881ffd61d5009fa90a2000f7d8d54077f863a001bfc629500bfe9966207ff58b53007b8a69805bfe40cc40dffb0ca805f7ccb31005fac321817fe6094c0bff9966005ff5885302ff8c92981f7f51d4029ff1826202bf98753007fec89881bfc601500dfe2088607ff98754005fac7a0007fe104c021ff18aa02effc845303ff8a0aa00efe62d0449ff28a8611ff8c95021ffc65aa017fe65cc403ff1868002ef1054100ffa4088002fd6494c0bff298a626ff90243007fea8a081bfe43d0025fe10ea01ddfd4951005fec888007fe404c005fe28a8201ffd013004ffa6498003fd4154061ff18aa605ff8c443137fc21219037f5295061ff882a602ff0435109ffe85a8013fe424400dfe214a806ff10754035f8cba0003fd6354061fe20aa601ffc435000df8c098802fd65cc021fe20aa007ff94353037faa9a1817fe3210c0ddfa108611ff4c950015f8c321827df324c001fe98e8002ff8413102ffec229802fd6094c0bfeb0ca605ff4ca43015fcc2a801bff65d0c57ee9968606ffd5340177fe84298a7fe50d0c0fff2a0a605ff90f3100ffe4098057fd324c40f7f32a6234df54a53007fac898806fe6055005ff18ea207ff14d511d7fe642a017fd3210c29ff2026202ffc4351037fa85a180efe624c001fea1a8203bf1893103ff8c9a8877ff3254403ff182602dff88453017f8639881ffe51d407b7eb12a800ffd8d41037f8c72a10ffd32d500dff30e8002fd9475101dfcc5a880bfc41d4451ff9048601ff841500afbe6498817ff314c00b7fb108600efd0d400077a83a000bfd21d040bff186623bff94154005facaa0803fd63440017eb2a6200bfd8d1020ffc81aa0c7fe3254c51bea948601ff901500affe409881fff525500bfe18a6040ffcca5403ff8c9a8007fd50d000f7f32c861bdf54b41037fac5a0003fd5444001fea9a8211ff58950037f887a008ffc1050c41ff080860bff4873002ff8c421857fc624c41bdea128000ff58153037fcc12a01afc644c403ff902a007df14f51035fecba0017fc3190c0dff2008601bf1824300df8c0a087ffe32d441dfe28e8037ff487531befaa5a98b7fc2114c0d7fb10a806ff18b4303dfccaa0056ff624c4057e30ca606bf191511dff860aa00bff314c433fe2928243ffc835403ff8a3aa017fe3090c01fe98a6007ffd8f5400ff8a088017fe434c085fe18ea800ffd
  | 7 => 0xa081ffc5454c0dfea1e8209ff9893002ff8c12984ffc42d400dfda028000bfd9530087f842a8007ff10d0061ff10aa605ff18643017fe43a881bff42d500ffe294a606ff10143006fea2a8047ff425400fbfaa6a203bf18b5303ffac3a8066ff6250401ff3222003bf1895102ff8cb98007fe20d400fff29ea22bff48743017f882a0817fc6114c0dfe318a814ff1813103ffec5a98af7d52d0c0d7f3226012ff90750146fea52180efc625040bfe192a600ffd4d43007faa6a8887fc2110c05fe0866207ff9475403ff8a9a8806fc60cc401ff2a2a600ff5953121ffa85aa017ff3294c79ff30aa834ff94a53007faa8a000bff515444bff90a8607bf99453007fcca98817fd43cc003fe206a007bf19543016f8a3a8802ff635440fff290a81bdfd4b410c7fc80a0803ff41d4003fe106a041ff0435403ffaa5a801ffc63d441dff18e8010ff945500fff865a8806ff604c00bfeb26620fff8cb400377887a0843fe6154005ff0828207ff14a5403ff8a4a880afc61d0c05ff8866202bf187400377e85a0007fc505000bff310a605ffd9253005fac888007fc104c00dde2008606df55054207fca52a012ff6244009bea922026ff04243017fa4288003fd635040fffa9ea021ff94443005fac19881bfd41d0001eea1a6007ff95351037fe86a001efc6550033fe992822ebf5885300ffea1980f7fe425500bfe3048607bf9973000778a92181bfc41d000bff29a8643bf58b54196f8a12981ffc61d5001cea188601ffc413003ffec1aa0bbfc4214c7bfe902a802bf98643017fa8398803fe635003bff292a202fd1455100ffca0a006fff32d041bfea128005bf98c53017f843a880bfe314c401beaa2a225ff58943036fca8aa037ff525002bffb126206ff1514302df8cb98807fe40d000b7f318a827ffc4243035fcc82a01efc654c4077f316a820ff04043007faca9801afe64cc405ff18e6202bf18530007f8a7a0896fd6250c01fe32a8213ffc875002ffec42181afe649500fff29ea030ff9455303efea5a987fff42d4401fe32a8605ff8cb31007bea7a18b7fe4114c01ff322a001ff84340127fc42a180bfc314c403fc0822001bf98341005fac1a980bf44150403ee1866002ffc413103ff8a9a8017fc3250c0dde2a08606ff58b4300ff820a801ffc61d4c05fb18e620bdfd4b3007ffa65a001bff60d040dff2a28632df94253047fc629800bfc41cc459fe200a602bf58751005fec6aa01ffd5214c3b7eb12a201ff50110167fc40298b3fc2014c0bffb0e6007dfd485404ffc64980effc6055001feb0aa607efd5254017f6208800bfc3150401ff21a8201bf9833103ffaa3a810bff10d5083ff086a809ffd893014ff8a1a18affd20d0c03ff882a000ff50530015fcc29804ffc32d400bffa98a63dff50954017fca3a8863fe305040
  | 8 => 0xf58f4000ffc40a8103ff209500bfe98e6005ffd825302ff8a7a181bfc63d0001ef21a6006efd0740007f8a898057ff424c40fffa9aa002ff887311cff8622a007de304c0077f310a822ff5484303dfccba000bfc31544017eb26a007ffd535302dfec59803bfc21d000dfe21e8202ff14741005fac22188bdd3210c41ff1008601bf18343007faca88002fd63d500dffa168001ff54330037f88021883fc2010c03fe186a005ff10f30007facaa0817fe534c401ffaa66001bf9804303ff6a0a810fff21d5005ff90a6200ff9533102ff86498017fe60cc409bfa922000ff15131047fcc2980c7fc4254c01ee98a6000ff5453002ffea62181bfc61150337eb128205bf98f41177fa84298fbfe309500ffe28ea605ff9845302ffcc32181ffd64d4003de2068007ff98b54187fc82a987ffc42d440fffa9aa605ffccb4303ffea92982bfc51cc04bfe3128607ff58b54047fc4298073fe3054423ff90aa000ff1953112ffaa4a181fff5214c5fff102a600ffd8151007fca89803bfe51d0005fe10e6200ff98d10035fecba080afc6114c077e3128600bfd8d5003ffac9a8803fe4354439fe302a205ff0ca4302ffca621867ff205045ffe102a618ff1814117ff880a981bfe5490c0fff280a600ff94d50017f820a089ffe2190c0bef2188605ff0c053005facba0806fe64d000dfeb10a807ffd4f510077ec89801bfc4190c077f316a608ff18530037f8a82181bfc65d0005fea8a6202ffc4141005fecaa181bff5415001ff2a26200ff14d10006bea729817fd53cc00bfe1926202ff90751017fc429881ffc5454043ff108861bff14b41047f84298003fc635400dffa148603bf18b40037fac62a10bfc21d500ffe28ca607bf99530007faa2a8003fc65440017eb2e8002ff10531017fea3a08177d5314c13ffa126000bf5935105ff8a59801bfc425500ffea96a21eff10351027fe648801bff54950077f310a600bf58e5403ffea8a8803be5450487fe196a802ff9473100ffa40a0003fc435440bff18c8631ffc8553217fc43aa09ffc2190c23fe192a00bff94b30087fc42a801bff65d0001ffa8e6000af19130005fec89806ffe52d040bfeb0c8606ff58341007fecaa1806fe604c401ff2a2a017bf58b310edfec4a881bff4210c0bff29aa606ff5845413778812181bbc54d000fffb1ea019efd094106ffc84a0017fc3210c7bbea92a800bf58750017f8429881bfc4250c0dfe30ca805bf18d10037fca821817fd62cc003fe0868007ff983530077c87a080bfc5154411ff28a6000bfd8141015fec2a0813fe624404fff28c8606bfd8a5402ffccb2181ffc5195049ff20a8602bfd914103ff8a42a01ffe52d4c01fea1aa205ffd8043007fec0aa00bfe514c41bff3128031ffd09530cffc64a0817fe62cc047ff102863dff9895400df8c1
  | 9 => 0xa80030020a100317600000009c0b320e00100024502716904900906b00000e00142d0591d12fb02902d01407800d07034d03a01c00004400701a02300119300f0620023c501400002300105007d00f00001800903d0010000000150602bc34536a00800100208900401a01400000e00000a00400000000200000003601918e218019004007021003022000017fc62a8802ff6154067fe20ca602ff10551007fea7a0003bc644c0016fb1aa83aff8c8541affc81a98c7fd5254c6f7eb16a600afd915300dfcc798027fd524c029fe2026237ff4cb530b7f88198803ff644c00ffeaa6a01bffc834100ffc819801bff611500fff286a205f714f3002ffac598817fc60cc403ffa066002ffd451018dfac4a9803bd435000bffb20a605ff0c153027f8a488003df314c00bfe9966002ff9073101dfcc421817df32cc0017fb2a2003bf18b431477a8521802fd64d4c037f3028607bfd8b50006f8a6a8823fe414c03bff192a216ff8833100dfccba80e3fe3015061fe10aa60fffc8740207fc652a0037e5414c13fe2126005efd0c43035fcc821802ff6550401fe31aa805ff94f3103ffec9a9817ff53cc465ff084a624ff98543017fe439880afe6110c4bfea12863bdf9415400ffe4198013fe524405dff210a607bf99510037f88521817fc31d4c65ff204a601ff8813002fbca6298e3fe1015001ff29e8000ffd9530015fcc2a186bfe30d04017fb22a01eff0c351015fcc22a09bfc2090c51ff90c8602ff9053107ff865a0003ff414c003fe1026005ff980431a5fac52980afe6114c0b7fb26603eff84254007fec6a8057fc424c403fe2026027ff9064303ffec5a801bfc62d043bff902a214ff9813111ffca0a1817ff31cc00f7e32a6005bf98f54037fc802a01fff62d507bbfa92a806ff15340025fac488002ff614c00bffb2e6007ffd8750137fc4121857dd324c40b7e31aa201ffcc13000dfecaa801aff65d0c01ffa9a6005ff0c730037f8812184ffd42d4005ff082a202ffd0531007fa8688057fd524c469ff904a605ff58331037fe84a0837fd625000ffeaa0a600dfd95101effe64aa08bbd4210c057f30e860eff8874000ffc6198056fd624c40dfe216a802ff8875112ffea4a180efe6295001fea8e801cff9015108ff884a8017fc62cc03bfe992a202f70c731037fc822185fff42cc40bff184a606ff95340037fccba1903fd329500bfe1828605ff0c653035f8c88801bfe60d0c0ffea96a806ff10843007fe82a8037fd215000bff21e6006ff18f41037fea9a0817fe5390c0bfe1966201ff9435002ffca698007fa2044001ffa9a6211ff5495006efaa4a0003fd53d0405de20e822bdfd4b4308dfec4a8107fc20d500d7f326a601ffd411004ffe4298077fe6254483ff106a801ff08150017fca2a081bff63d0405ee18a6206f
  | 10 => 0x11a01d00000400000000300300e07506100c0bd00300200201907400000701100f0310020002bd0d300404702f00901100103000b00500a00f06e0310000c00000090010064360020122f70000070000020110020000010063bb00410000c0eb00101010602001600001900110100000400d08900606221000f00000104d39a00505f03000001600002001600d37300c00100300311400803d00000100b01f22d27200000031200200f00050a1140050470290060150043370002750001ae00200400100200000902a01b00302300d00300502501b07800300400027a07d00106301600000301201c05e01721801400400153200302600901400b0000070010060004ad00c00600304501f00004300d1c406500001203202311500300001302f0000b000000000401200700000000000e00800806500400307101501803000700200b0120360140001e000b0001a700200200900100103b00000f31202604301d29d0000050010772ab3580010000370100000bb00900503600600e01400100e01c01100020001214701710d3a300000700000000203b00100f05100100539c61009f00b00b02b02907f00205501202938200800000b4a108a01500f00003400001e00600104125803600700300316e00000068d38100b09301400002200000002802612000001301904c00000900000100d04e01e00601304100006e06500501502c00009d08d1920060090b000602200000002e00000a00001c15600000300000008301000200700207f01d00000001901001100601100d02100300800000301312c00c00000500200500032103000202600b00902a2f609500403a00a0030000a303700a30a0082190000082f100800900401212f00604b00100200401a00600115f0020120283200000000df00a2d800000700100a00501d0160b200001901e00300200506600001a04000200200423d00002727f00300900000a69d01600600119c0c60000090c53080030000d701e00045505800315a02013002500404343f01800000000001000119103800700900900000702100000e01100533c05d00b0050530000020290000050001150040010001d201600000306b00535d02006522403303800000004f0171b303800500600406a03b01e0000270090000510000010c702000335200f09405500f00015c01000e00401d00100f36e0230190050d300502500d0270dc3200260000000de04601a35d07a00805c25f00c02e0446b701700001002b05a00e0000450060060080f000500005f2b100012a00709801400800402002900800311d03200600503d02716402b0010191
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe21d95433fdbe7550f402c75c5418d54036bf4058743006dc31d8d540067e2159740006de4118d540157e7194f5103e7f5258454016be61507400067f64d4550004fe7695130005bd73d514000cfc705935100cfe70d854313fb67190d4102ddf7650f3001cfe72d953001cfe72591311f5be76151400067c6590d1034ddd7250f3001cfe72593515df5d52d4f4303ef75158754004ff7258f54004fd76551310367d7499740036bf7219153005bf7459531106be20191300075c6550d3002edf6014d300057f7550d10006bc71d9130005df7358141004ff7058754014fc71580530067f52d954001cfe7259643006df6310d51014fe7158053006bc61d91530067f52d9543136bc70d9130034fd71d954120e7e1099740006de2118d540063d65d5340014fe7158043035be75d5140034fc745951002ef771584430057f72195101de7d10597400075f6394d511defa40d8154014fe715953000cfe705864303d7f71545500067c75591312c6df6319543035be74cc54002edc6390d4002ddc735525301cfc72d9151034fe74d8153045f97098d1002f5d60d4e53006df71d8d5425e7c31d95100067c6510d10036f84058043036bc6455153034fe7614f400367f545845402ebc6350d402675d524c530036be7695141247761019510006bf6219153036fb405804301cfc72587300067f525974002e7f755973102ede6318d400a5dd71cc53003cfc76d51100067f101954303e7e711951003ef7715875401cfe72d8153014fe735833102ebf7459331006bf2119130004ff75583430367f545865400cfc70587530067f21997400373e751514000cfe70d95102dede64d4c43004ff72d8131006de7618d540067d5258443006bf7650f4003e7f6114d5103e7e7019543016dc764c5303375c5310d51004ff7558f4000cfc7059053014fe71583431967a5058253004fd71d81540373c6555341004fd725835102f5f60d4e530067e42d951003f5d71d4e530067d21d95430057f7559131526df50d8d542dedc54d8d5403ebd5458454015be7195141006bd4259353014fc74d8540004ff715825302edf7418d5403f3c72d52540067c7558d10004fd725865303e7d7419510004fd76d0d51014fe7690d4102ebe63d0d4002cfe76d5143006be601915300cff71d8d10066f641d85400067d2159740004ff72d95413fdbc7550f40004ff7259253006df6358154036bc40580431debf405935002edf30590531e73d5155141005bc7458d50005df7358540006df21d8d5400cfd71d9510006dd32d8d54014fd7458740034fc7459530366bf3219153036f7415844324e7e411951003ef45158754004fd76d4f4003cfc755874301cfe725935327f5f52cc5300067d4219530006fb7059130036b8405804300cfe7690d4003e7e74195431de7e5059350
  | 1 => 0x53512467f301951002ebd4358243004bf7458d10014fc7159643004fd725974301cfe7258054006bf7459643126f641d854303ebc545905348ebe6590d410067c52d9510015be7110d410067c31997400067d6554f4002ddc73545300067c2019543005dd73d524303e7e721953002e7e535973002f5c60d4e53004ff7259541006bf6458553325bc73551410067f6599510006dd6218d54014fe7158c5402ddc7355243034fd74597400373f63d525400cfe76d814346dbd7210d4100cfc76545500055d7395253014fc71d8d5401cfe72584542dede54d8d54376be73d9153006df63d81540b6f710d85303cf3d5215140075fb7059110476be6510d41004ff764c74003c7c755911002f5e53d4d30005bd7510d41005f77155151275de754c53003e7e7119530004fc765055002ede6318d500067e4119530134bf7650f4002cfc7359350036de6450f30186f631d855303d7f7214d510367e42997400075f321953001cfc72d95301f4fe7619540004fd761513002cfe73d9540014fe71582531079c30191302c67f421954360f5d20d4e533375c53547301079e3019130004ff7258053004ff72d9530036bc6490d100067f52592531379e4090d30006bf745911002cfd735933002edc7418d54034bc7459443006bd65d054000cfe7654d3048dbf72d524332dbc73553410067e50597310067f65d5143006bd65505403673c53191530373c60d52540067f65d51400063f65d51400067f70d954336e7f6599153106bf501913032ebd7690f410067c6558543475bf72d5043005bd7090f413357f7294d51006bf65d91301967f30d9530006bc64d85533779e73d524356f9e40d4c431de7c30597403773e53d9153137b830d9130106be101913002ddf714c53001cfe72d85300367f7459740034fc745944303e7e73195300059d73d52430067f659511002ef8305833102cff76cc740014fc73593310067d52592530379e63d50430067f71d9543004fd72d8d540067f65d8d1001cfc725804302efb7058331034fe74d8530004fe76d0d510067d525845403e7f7219530005bc7454d5019e7e7694d51016f4614c530036bc6415130006bc71d9153006be41d9153015f67114d100057d7414d5101cfc7258654004fd76d0750004ff7158f40036bc6410d10006f76154550015f47154d312c57f7295053004fd7258654006df73595310063d52191530067f2019543004fe765055063f3e31d5254034fc76151310067e6119530006bf42586432c65c5418d540067d525865403e7d7099740006bc70d915302ef43158643004fd7690f50004fd72586430067c61195302c67c4119543036f7415845403efb70583511957c70952530067e30d9543006bd321913002cff7158443366bc53191530057d7494d511de7e30597400067d32997400067
  | 2 => 0x6f77158d1036f3c43d9543006fb7058d1001cfc725951002edc64d4f30036bd711913001cfc72d8154036fb7058343004fd76d5131004ff7359540014fe71d913003ef4515845302ebf7459330036bf6195141005bf705534102ddc7355330004ff7458d1039dbd72d054003e7c711953025e7c41d9510004ff72d8540006df6310d102467f40195100079d7150c4303e7c65d4730014fe71d8d542467c401951000cfc70d8d41004ff705935102ede6318d54004fd769513003e7c6514f411defa60d815403cff76d533002cff7694d10036bc751915302f5e53d4f434773f52d5043004ff7258754036bc6495130004df73591100075d32d95301e57d7595151005f97095130476bf501915355f9f2050c43035bc7454540036bc711913024f7b101951000cfe76d8151004fd72d81430067f659911001cfc72583430367f7559743034fc7458653126bf41593312567f20d95102df5d65d4f430067c50597432c65e5418d542f67e43195300157c7194f51004fd7654730006de50d8d54005bd74cc5404773f5410f510067f62d95100067d5259740004ff74595100067f52d8d510057d7510f5100cfd7558351004fe769513103cfe75d91100367d42597400167c76545500067d72597400057f7550d513779e43d5330015f671d4d3100cfc7058c54006bd32191531675c6514d30004ff72d9150036bf41594430373e62d525402ebe4359330004ff72584531b57e7614d51006be425905302cfe76d8d402c75e5418d5400cfc755935020f3e50d514001cfe7258f54036bc6090f412f67c4319530004fe7610d5127f5d52cc530006bf64d0d3120e7c60d5151126f461585430c7b87050540036bf60d0d40004fd72d8d4001cfc725944354f9e5050c4333d7c7355351006de5118d540057e759913001cfc725913001cfc72597411967c40d9530036f7415865401cfc725875303cfe76d95300067c72d951002cfc7358351005f97090d400067f75595300067c62d95432567f10d9510276dd6514d3002cfe73d9530014fc7158f40135be70d524303f7761d51514af3f52951410067f65d4d31004fe7610d5003e7f7019543015bc7655141006bd42d8141136bf73d91300079f6350d4002ef73158453004fd74d9531005bd7090d4103e7f60d4550005f970d5140106be4058043004ff7059541105be70d5043006bc7458d10014fe715905303e7f5158354004ff72d8d542e6bc3119130004ff72582542567c70d951003cfc7558643004ff73593510067d65d454002ebc4359330005bf7150f400067d52d9540014fe7158243004fd76cc5500057c7558d40376be53d91531967f40d9530005df73547300067d52d95430067f6554d4301cfe72583535ff5c10d4e5300cfc70d953100cfc70d8554006bf6455150006bf21191530367c645
  | 3 => 0xc74587430157c7194d51004fd7258f510065c735974003e7f729974003e7d7219510196fa405825302cfd70d9130005fb705514000cfc7358730006de10d8d5448ebd65d524311efa30d81433fdbe75507400067f52d9150184ff71595310379f6350f40034fe76d91501e6f651d855402cfc7614d4100ddc7090d300373d61d5254126bd4159331004ff745953003edc5358f512c6df4018d5402cfc735845403e7c721951003d7f721525302edf305933101cfc72587432c6dc4018d540067f6599530036de6490d300067d72d951002cfe73d814103d7e7394d5101cfe72d9130036be63d524332ebd6390f41004ff72d8d10375bd76d524301cfc72d8553004fc7650d512567c20d951054f9c2050c43006be6219130004ff7258043004ff7059743005bf7458d500073c6555141106bf101913000cfc70d853003cfc76d454020e7f10997404af3d529514100cfe70d9531034fd75d81540373e54d5141004fd7610f502c75f6514f430067f6558d100057c75585300057d711525303f7b60d4550006bf745954302efb305805303ef75158453376bf75d9153275df72d4d30006dc6218d541b4ff735953101cfc72d95410067f6454550526dc52d8d5402f5e53d4d3100cfe70597430e6f71058750006df32d85301e6f641d85540059d74d4f430057c75581430067f52d81530075f7550d30004fd764c740014fe71d9530006de31d8d4000dbc70505400067d5259053035bf7555141036bc4358f41034fc74582530373e54d51400067f7558d100373e54d5143005bd71d5243004fd72d8530034fe76d4f40006dd6318d54014fe71597400e57d71d4550014fe71d9153036bf75191300067f42d951002f9e6550c43006de42d8d540075e5018d540067d72d9530004ff75591300373d62d525403e7f5258f54004fd74d95301667e5058053036be6419130037b76195141006bd649525303d7c7015253014fc7654d51006bc52191302dedc41d8d540067e5159730065f970991100067f525944336f3e43d954303e7e7099740036bc54597400057d7195253106be50191303663e5319153006df20d8d54006bc64d81530067d52d9150006be31d9130036bc6455150014fc7158254005dd74d4d3038ebf651514020cff745954001cfc72583412df5e65d4f43004fd7695131004ff71595430065e5018d541967e6094f510067d52d8553004ff7558443014fe7359731005bf705514103e7f5258354005bd71d5043004bf74595300047d7259740004fd76d4540004ff72d8d400073c5494d40004fd73d95100067e32d9530004ff7559131376bf30d915348f3f52d524300dfa70951300067f52595400373e65d534003cfc76d4d1002cfc735874003ef77158750006df735913155f9c5250c43004ff735954103d7c7550f5002edc63d0d51
  | 4 => 0x54003f776194d5101cfc72595410073f5410d5136e7c43d95431967e40d9530036be6490f50006bc64585300067c7259740006dc20d8d5403c7c755913002cff71d9531014bc7458f4103e7f60545500057c7559131306dd624c73001cfc7259331005bc745853003e7e65d5330014fe71d8d1017efa60d8153014fc7159743476bc521915300cfc76551400367f42997400073f5490d51005bc74595310067d65545401667f6518d500367c4359740006be50191530369d73191301667f401953002cfc7359110004ff72d814300cfc75d8151034ff71d9541014fc76551410367c41997400157e7194d51006bc40593530067f52d8d100067f6594d4001cfe7259053376bf64d5330006bf64d053000dfa70d0d30004fe76545300067d5259443006df32d8131036bf6390f414779f53191530067e51d9543004fe76d0d100067f65d8530005f57114d100067f6559110034ff76d0f5047ebf6290d41035be74d4d43006bf7459541036be6410f50004ef7258d1003e7c7558f5117cff70595303667f65191530367e41597400067d6594f40006be76191303e5bd72d514000dbc76505401667c401953000dbe70d534002f5c62d4e534467f62d455000cfe70d954102edc63d0d500373d65507400067d5258243006bf6458153036bc6590f4102cfc76551535b73d52d52430047f72d95100057c7550d3002ede7118d543a5be76d0540186f661d8553004ff7058454004fd75d81416167d6215253004ff72d8530004fd74d8153004fd725825303e7f7399740004fd725873000cfe755875002fd83050d3000cfe70d91530067f659953103cfd70d9150004fe76cc5402df9e74d4f4303f5d70d4e532bddd7214d3002cfc735944311ebf4059330004fd76cc54001cfc725805303cfc76d4d4102f9d6050c4303cff7654f43004ff72d9131036bc6495153466bf6210d414467d62d4550004ff7059741004ff7158f501675c5014d3003c7f7219530036bc6410f51005bf7454f4003e7c73195102dedf42d8d546473f32d525403f5f71d4e530079f64d4d30014bc7655141226df30d8d1001cfe725864303ebc765514100df8705455003f3c5455151014fe71597430057c7558131004ff72d81410367e64d5151376be63d504302ede6318d41004fd70d9543016be6150540004fc7654d10034fe74d954020ebe76d51403ff3f54d4740006be75d913001cfe7258351004ff7258d10005bd744c54058f3d52d50430067c21d953002cfc7358253106bf201913002cfc73595100067d52d8d510067e32195100075d3219530006bc65d9130366bc631514003ef850583540067d2019543006bc40d9153037bb60d514020e7f2099740016be61d05401dcfd7655140005dd73d05300067f65d814303e7e6519543035be74d4d41035bf72d054002cf
  | 5 => 0x55f9d2050c4303e7f7199740004ff755933101cfe7259730005fb7054d5002cfc7358654004ff72d85432467e40195100063f52d913002ddc73d47302447e76d4550004ff7259131014fe76d5141006bc42d9130004ff725954319e7f51d953102f9c4350d3003f5d74d4e53006bf6495150006de52d8d541afda70d4d30006ec725911001cfe72d91530379f4390d400067f52587302567d20d9510036be7615140036bc545944336d7d73950530367c64d5151004ff7654730006be32d91530067e51d9540326bf6390d4102e7c53596430067f525974103e5d76d4e5303e7d7019510136bd40d9130035be74d4f4103f3c5455253036bf4058f41004fd74d8d5103e7c65547300079c6490d30034fc74d954002ddc7590d3000cfe70593310057c7550d3136f3d64952530373e61d52543367c5359531004fd7258750006bf2019153006df6350d4003e7c6094f510079e43505301977830d9530005bf745855341f3e5494f411dcff70595400057d7598d10224fe7618d100067c65581432df9c43d4f41004ff72d8553004ff72d8d51004fd72d8131276df6514d30216f64158754016bc76505400079e43d05300067f52586532c67f4319543006dd32d853000cfc7654d5002f9f7650c43004fd75d8d4102f9e6050c43005bd71d534041f5d7395253006bf6450d30004ff76507300067e52d9510007792019510365bd7615243036f771586545d5dd7214f4302cff7614d10036bc6455151326bf6310d4101cfc72d8530004fd7654f41014fc7458f410079c7550c431e5bd74995415ee7d6295053004ff7258730006bc545824303f3f549515002cfc76551430079e7550c430067c65d854302cfd74d8543006bf101915303ebf7459350006df5358043006bd6419150136bc50d91300067e5159740036bc701915301cfe7258343036dd43583430e77870545500067c1019543006bc62d91530067d6555243006bc425933102ddf7290d30036df4358f41006bd6219153004fe7654d40036be5458454086f651d8550004fe7619543016de614c730004fd7258f54004ff76551310067d73d954336e7e43d9543125dd73991311e6bf41593510073f7550f4020e7c2099740034ff769533002ef43158443036bc71191530073f655514133e7e53d855302cfc7558353004ff7458453004fd7610f513367e635475036e7c73d95435275c5014f430067f52d815455f9e5250c43106bc20191300373d6550f4024e7c211951000cfc70587431967c6094d51014fe71592533357c7355151014fe71d95400067d5258f54036bf42584430057d7510d510079f644c53001cfc725875403e7c65d4d4301cfe72583540057d70d5151006dc6018d540067d6519530525df72d4f430067c65d91100067e61d95433ff3f52d5340006bf645053000df8705
  | 6 => 0xf7355130006dc10d8d540373c545524302edf7518d54004ff75587430067f7559543376bf65d5243006f7614c5300067c2119530006de4018d5402ddf7414f43034fe76cc7400067d525865300cfc70d8543006be52191306075e21d4e5302ddf72cc5302dedf639954300cfe76d81410067f65d4d103f5bf725074003f3d70d52544759e7550c430067f5258d10014ff70d911002cfd71d8131035bc74d474003e7f6495053004fe7694d4100cfc71d8131004ff7058f5141e7f6594f414759c7550c4301cfc72d8554004ff7654d40034fe74d8d1003e7c7419510006bf64551300079f7150c4303efb7058353004fd7694f40034fd75d855402e7e5359443006bf745954038dbe7550d403667c321954338dbc7550d40006de6118d540073f521913002ede435804303e7c6514d41006bc201915302efb30583316473d32d52542567c10d951003e7c65551400067c65d8530006bf64d5131035be744c7400367c5459743004fd7654f4002ddd76d4f30004fd725804302edc7118d54034fc7458e543667f31195430079c6350d40095fb70595100369c6450d30004fd76d4d10014fc7158c545167d62d51510067f52591314273d52d5340004fd76d51100147c76551516373e20d525448f3f5490f51036dc7650d30004ff72d85500067f52d95310067f52d91300075f5394d106373e10d525402dde73d053001cfc72d9510034fc7459731006dc6118d54036fb705825401cfc7259530004fd7654d100057f7055151034fc76951300073c6455151005dd7114d30004ff7158e54006de32d8d51006df63d4d41006de32d8d10015f47154d511e67f5159741007db7050d30526df74d8d5403e7e6519530004ff705875300dde70d4f30004fd7614f40004ff735805400cfe7694d502eebf32d913003f5f72d4e530067e41d954303e7c6555141006bc21d91531667e6014d51004fd72d81510057f755853000cfc70d9510036bf4158043036df7358f40004fd7694f4124778101951002f9c43d4d4336e7f74d95432567d30d9510036bd70191300067e3219530006df3258343006dc3258f41034ff7650d300067c50d9541126df3158f41004fe7655131006bc6219130006df32d8d4036e7f30d954302f9f7450d301de7f30597400073e5494d416473f21d525403e7e741953000dfa7094d40014fc71594430367c7655151006be201915303cff7659510036fb40580540079f5310d412efbb30d9130005bc745813100dbe7050540036bf60d51401de7e605515120e7e209974002cff70580530067d52d8d10005dd744c7300079f64cc530004fe761513003e7e721951000cfe7058653005bf7458d510067d52d815403edc5358f500367e435974060f5d21d4e53006bd71d91536267d6295253004fe7610d10004ff7558643005fb704c530
  | 7 => 0x4750004ff7259740005bc7459530014fc745834103cfe7690f51036be6419151004fd74d855003cfd74d855420e7d209974002ede7018d541667e4019530006bf7458d10004ff7650f50016dc614c530004ff72586540067d52d9130014fc7159330004ff73587502dddd76d4f43005ef725854003e7f711953002edc6354d5103d7e7495253006be4059353006be71d91300a4fd7698d101cef7105845420e7d3099740005fb70551500073f54547400057c7558d1000cdc7650d30004ff725844303e7c5358c5401cfe72d91511f6fa3058254036bc7219153466bd6210d410367c74597402775c5414d304367d625455002edc6350d4138dbe75d05400067f6555141006bf62d913063f3c31d5254004ff7654d10005dd71d4f30247741019510004ff72597410a7d8704c530014fc71582432dddd74d4f4302f5d62d4e5303e7c6514d400057f705535147ebd6290d41004fe76d4d4038ebf54582540067d5258354004ff764c54002cfc7695330005bd71d0d4002cfe73d9541136bd50d9130034fe74d855301cfe72584430069f321913041f5f43d9543004fd76507503febc54d815403c7c7558f41006bd64507503d5bd72151400067e31d9530006df63585541e67d51597413773d65d5243004fd72d9150124fd7650d31134fe761913041e7f40d954325e7d31d9510004fe76d51300057f7558131006df6218d5419cfe761953100ddc704c730014fe7158353476dd76d4c43004ff715824302d9f7650c4303e7c7299740036f441584430057d7094f510367c405974000cbc7650540004fd7259350005f97094d40004fd74d8d5000cfc70d9541155df7359131006de72d8d5400cfc7058643006be4259331004fd74d81512dddf74d4c430063d52d91300057d72d9510007b761505400067f65d0d10006bd64d0750004fd725913103cff76d47300067d5258730006bf6499131004ff7059331005f970d0d300067e74d95102a75f5290d303bf3f52d0d40526dd65d4f4303f3d73d52540057d72195301e6f461585544775f52d4c4303e7e6555243106bd2019130014fe71d91102eebc53d91301667f30195300373f61d52544367f625455001cfe725873033e7f65d4730004fd725874300cfe705875341e7c40d954300cfc73593303febd76d5340134be7619130036dc6450d30004fd72d95430067f5258243006dc53583430067f5258740037b4415514102cfe76153310079d7050c43526dd76d4f43034ff765911003e7c5358f5102f9c4350d3102cfc7358750006dd32d813103e7f5259351006df6314d40034ff70580540367f405974002ebd4358043006bd62d91300363c7459740014fe755835101cfc7258f41035bf765074003efb505835402cff7158453014fc71d953003cff76d4f400067e70d9543036bc6495150005d
  | 8 => 0xcfe705865402ef7315864351d7d72d5151036bc64d0d3003cfe75d8540006dc32d8d5403e7e65d4f40004ff72597430067d6519540036be76d05402547f7654750006bc644c53002cfc7690d501379e30d91305579c5150c43005dc73591510067f651913001cfc7258f500067e654c740034fc76d0d100367f4399740014fe7158f54016dc61cc5302c6dc6414d30006df10d8d54016de61cc530006bd201915302cfc76d5330006bd6419130136be20d913003cfe75d8d410067d2119543136bd70d91300067c7559110004ff7358754006bd32d913002edc6314d411657e7095053005ef7258141014fe71d81432c75c5414f4303cfc7558d102a75d5290d3000cfc7059531315dc7550f3002f9f6250c4300cfe76d81311967d40d9530004fd72d8153006dd325834348ebc6590d41004fd75d8d4002fdb6050d303bf3d52d0d40006be52191530047d72195103667f641525302f9e6414f43006bf7459531105de7690d30315de7550f305775d52d4c43136be10d91300067c6518d10366bc31191530075f65d4d3000cfc74587402567f70d9510036bd72191303175f52d4f3001cfc72d954348f9c53d91530353d76d525462d7d7295253006de6218d54004ff735951020e7c1099740004fd76d5130006bc42593501967f6594d5024e7e311951041e7c6494d510067c32d951001cfe7259540036f741587405167f62d5151006dd71d8d5403cfc7558331106f850580430073d52191301677830195300067f6554d31005df735954003cfc755834303e7f5159350036f4415845401cfc72d85500067d5258740476bc6510d41006bc7459730004fc76551100067d525935160f5d42d4e5301cfe7258e540067f525825303d7f7655351006bc601915325e7f31d95100067f62d95430069c6414d3031edf764c7300067e32597400063f6519130006be72d91300067f5259331035bf7350d4001cfc7258f5402edf325844319e7d51d95310057d721954303cfc7650f50006bf21d9130036f4415865401cfc72d915302ede64d4f4300d7e705475002cff7694f400067d5258d100067d65195102d5dd72d4d3003e7f525875303d7c7550f51004fd72d95102c6df6514f430067e7619530014fe76d4d3101cfc7258454004ff7058743004ff7259730005bf7150d40156df31d8d4102ddf7450d3003f5f5394d5103cff76d474011f9f4050d30004fd72d9153004ff7650d10106bd3019130005bf73507400067d52d815303e7f62553510067f6514d41004ff7258750006bc64d4d3001cfe72d9150106bc10191300067d52d9531004fd72d8553005df73551310067f52591100067f525804301cfc725913154f9c1050c4300cfc7650540005dd7395130006bd42d9131034fd71d81411975d73d953002edc7018d54016de614c5300167c615
  | 9 => 0xf51d95103367f65547300067d74d951000cfd71d911002edc6350d403fdbf72d5340006df7650f3002edc6394d513575d52d4f3001cec7258d100067d65547406473f20d525403cff76d4d10004fd75d91100067c3299740006bf7458f51004fd74d8131275de7590d30004fe76d4d4103f5c71d4e53036be64d05504769c5319153036bf65507400067d52582530067f6550d3001cfe72d954003e7c65d514301cfc72580542e6bf3119130004ff74582531ddbd7499540006df73591102eebc31d91303673c53152430067e65cc7400067d52595401675e5014d30004fd7258f4003f5e71d4e530047d7219543005bc7458d10006fb705954003cfc76d5130006be31d91530079c5490d30036fb405834103edf5358f510067e611954300cfe76d8153036f8405834102cfc73597401867f515973103e7d739974003e7e65195403f5bd72507400079d4310f511967e70d9530005dd7315130006dc31d8d40526dc51d8d54015be7190f41004fd76151311e6f661d855438ebd65151400067d5258753156f63158743036bc74594430067d5259110004fd7650f500057f721954300dfa7094d5000cfe705844300dbe7015140004ff7059253006be42d913002edf60d4d3000cfc705913100cfd74d854025e7e71d951000cfd75d8550006df63d855436e7c30d954303ebc5459351034bc7458f5117efa50d81530067e73d95100067c21d954301cfe7258053036bc72191300067d5258043005bc74585533075f524c73002e9c6350d40004fd71d9543036bd711915300cff71d91100047d72d95301379c30d913063f3f10d52542467d40195102c73c5414f4001cfc72587500367e545974302cfc7694d400075f654c5302c5dd7614f433773e65d524302cfd70d953001cfe72d8d1000cfe70595410067c215974001cfe72d9543036be76d0d4003cfc75591310067f655053003edc5358c540057c7550d1002edf7018d54004fd75d8d10006de6018d5402edc6354d5002cfc7614d4003e7d7299740004fc7655130005bc7454d30036bc649515101cfe72587430075e5414d3036e7e639505302cff70d95300379f7350f4001cfc7258d1003cfd71d8d5102cfd71d9531004ff7258c54036bc4358c54004ff7650f51004fd7695330036df4358e5401cfc725935102edc5359730006be51d91530379f4355243004fd765474003e7f525935003e7d7319530136bf50d9130036bf65d50430067f6519110006bf4258243006bf6415130006bf72d9153006dc2118d540067c61d954301cfc725935300cfc70584430067e32d95430067f52d8540034fe74d8d50014fe7158f500057d75991100067f65d0530006dd32d8d40004ff715973001cfc72d8151186f46158553004ff7654540004fe76505300c4fd769911001cfc725864303d7e7510d51
  | 10 => 0x9730004ff7159053276dd65d4d3002cfe76d5331004fd74d8d10005df7358154004fd7690d5100df87050d302c79f4314f400067f52d9510034bc7459730006be61d9153036bf70191531967f73d953000dbc70d0540005bc7458d510067f75595312fe7f32d9530004fd75d854028dde76cc530006df73593530067f525913000cfe70d85306373c20d525403f3d72d52540047f7558f410067c6550d10006dd6318d51004fd7690d1025e7d21d951011ddd739913002f9c6450f3000cfe735973002edc6310d51005df744c53000cfc764c53003d7e7510f5100dbe70d5140005dc73585400067f72d9530004ef72591100a6fa30d8131036df4358c540067c62195433075d524c730014fe76951510067d52d854036f5e739525303e7f74195100079d4310d10034fe76d9151005bf7454d400067f52597310059c735514103e7c7019510006dd325844301cfc725825355f9f5250c4338f3f54d45400067f525954103e7c6554d43004fd75d85303375c6394d5103cfc76d4d40035bd7690f41006bc5119130036bd7019153036bc545804338dbe7550540006ef7258d10034fe74d8d51004ff755824353e7d6255351005bf74585303367f6394d5103cfe76d95434f67d6294d51055fb7058d10185dd739953100cfe76d4d300b5f77158d10004ff73597400057d7094d5102cfe76553310067d52597410079c7355141035bc7454f430059c7355341004fd7694d40136be6090f41006bd4258341006dc7359541006f76150540014fc76d5141526df51d8d54006bf64991530069d3219130004fd71d8153005bd7010d4100cfc705935302edf604c530004fe76d45400067d525933103cfd74d815403ebe6555341014fc715825302cfc76d5331005dc73551400079c73553412c75e5414f4336e7f64952530067e3119530005df735533102f9f6050c4301cfc72d9131326be63507402ff7b30d9530004ff72d8d410067e40d95430067d52591310075f65cc530014fc7650d3124e7d4119510015f47150d3102fdb6014d3000cfe7059643004ff7458f5000cfe70584540067c42d9530004fd76d0f50126f631d8543014fe71d8154365bd731524301cfe72587500367e4059740036bf721913055f9d2150c43036bc6450d312457e76d4550004fd76cc74003d7f72d4550016f461545500067e72d953000d7e70545502e6bc3219130085f97099510004fd76cc75003cff7654d43034fc76d0d51034ff7615110004fd725913003f7b60545500d4ff71591100065f7359740004ff72591103667c301954301cfe7259743034fc7458f516075e41d4e5324e7f41195102df9c54d4c4338dbf72d5140036df7358f4103edf5358c5401cfe72d8151005df7150f30015be7190d41004fd7258331285dd72cc5300067f5258743006bf745973025e7
  | 11 => 0x5dd73d51430057f755854002ddc73547300067e50d954102ef7715865302cfc7655331004ff7158343005bd74d4f41006de30d8d5402f9c4354d430067d525954100cfc70d8553005f77150d4148ebc50d91530067e60d9543005bc7454d31004fd7694d4100775211951001cfe7258254136bf10d91300067e62d9510004df73595410071f7550c43004ff7558d102567c30d95103673e4319543036be72191531967d50d9530005bf74595300379c6350f4002ef43158653006de21d8d54005bf7458131005df735511003ef45158750034fc74587500073f7550d40004fd76d4730005dc7358141036bc64507300067c65d05300067f6598d10034ff76d073011cfd7650d30005df735855403e7e65d4740006bf6410d10186df3158f51005df735915002edc7218d54315de754c73002cff7359330035bf765534103e7f721951002cff7690f513fdbc7550740004ff7059531034fc745973002edc6314d40124ff7159131006be62d91300067f65d5110476dc5018d54366bc321915302cfd75d85533367e535875302edc7359053036bc64d0730106fa205804302ebc63d0d40004fd74d8553006dc30d8d4138f3f52d514002fd43154d3100cfc70d95430067d645475000df87054d5000dbc7650d402fe7e73d9530014fe71d9543004fe76d05300067e62d954303f3f6455351034fe74d9510277d970d4d305279f54d8d54015bc71951413673c4319543005bf7454d41004fd7258343034fc7458053366bf3119153014fd70d91100067f6599540136be50d9130004ff7058f4103e7f5158053006bc64d45301e4fd7655141036bf4058c54004ff72595100055c735535125e7e21d9510526df52d8d540379c43d5143476bf5319153004fe7690d500c6fa40d81415c75e5014f43035be7494f400075c50d8d542567e30d9510004ff74583530067d5258743004ff71597400e6fa60d81510067d421954300cfe735873003ef751587500067d62d953003e7f741954301cfe72d8d54006bf649913002edc6394d50006f771595100067c42195101667d40195301947e7619530005dc73551412775c65d4d3002edf60cc53003f5d72d4e53004fd70d91530075c7355351005f97094d500067d5259350034fe74d855029ddf7250d300367e6455351034fc7458453004df7359540036f74158743006de30d8d41034fc75587540067f52d8543006bc52d91302557e761951002ebe6350f405579e7150c4303d7f7654750014fe7159353006dd21d8d5401cfc72d8d415579e2150c4300cfe7058754035bf7315243035bf72d0d4003d7c7550d510067f6555130036bc7519130034fd71d8d41004fd76551105579f1050c4311ebd40593300063c6519130035bf7210d412c6df4118d540057f7558d100167e61d455003e7e731951002cff735
  | 12 => 0xc4358f4102ef73158443005bd74d4d43004ff745973003f3f73d525402ebc7650d405ff5c40d4e53035bd76d534002e7f75594430075c65cc5301967e10d95300075f5394f400067c42195301967e20d95300057f7219530004fd75d8131035be7414f40014fc7158054006be6219153005df7355153004fd72d815403f3e74152530067e21997403663c431954302cfc7358243376bf32d91534973c5055141415bf7250f40005bf7454f41015f67190d41035bf7295141014fd74d8141006bf6410d51006bf645853000dfa7010f50004ff76505500079f6390d41004fd7258254006bc40d9131004fd72584540067e71d9530067b46150540006be211913025e7d51d9510106be30191300157c71d51510057f7558141106fa1058043006df3258f54014fc73d853002ede76cc530006be761915320e7e3099740004fe7614d414f67f6294d51006bf42d9130006bf649915003e7f71195100067d52597310075c7550d3001cfc72d913041f5c43d9543036df4358f4002cfc7359540004fd765533103ef85058353004ff7654f4044d7d72d45500067f21d95300067d2199740006bc7459531006bd425864303edf7358f51015f471551515279d74d4f43004fd71d953020dbe75151400067c6550d300067c65d814303e7c6514d1003cfc7558443006bc42d9153036bf7019130475df72d4c43004fd76d4d400e5f57199510006bc41d913024f762119510004fe761511020e7d109974001cfc7258653034fe76d91314cf3c5055341006bf52191301867d515973103ef85058053005bd74d4d41034ff70d95400067f52d8554004ff72d95431defa50d815403f5c5354d500369c4358f410067c72d9530004fd72d8d51004bf74597300067d52591300079d4310d51025ec725911014efa30583432c6dc4218d540067f6554d10005df735954126ddf724c5300067d52d951003c7f72195430067c651913003f3e72d5254005bd73d054002ebc6350f403c5bd72d0d40254fe7619510034fc7654f4003c7e76d9510006dc30d8d5403e7f73195300065f5218d54006bf6495130036bf625074000dfa70d51400067f52d855001cfe7258253476bc51191530067d62d951002f5e64d4e530067f62d95300075f5218d54034fe74d953103e7d711954302edc6310d50006be425935011ef86058143014fd735873003e7f525805355f9c7250c430067c71597400075c654c530004ff73586540067c6550530006bd2119130007bb705054002ef43158730006bf6490d1003e7c65551100157c7114d512dede64d4f30526df54d8d540067d74d9530006df6398d50004fd72d95400067f321951002ddc7355143005bd71d51402dddd74d4c43004fd75d854302f5f64d4e53005bf7454d43004fe7694d10005f97010f500067d52d8543136bf20d9130
  | 13 => 0x91100067f71d9530036f84058254034ff761513103ef850580542467e1019510034fc76151300057d7014d51004fe764c54000cfe70d85546373c10d5254476bf5219153006bf71d91300067c73d95101657c70950530067e72597403667e4319543004fd70d91311975c30d953003e7e65d4f43014fc71d91500067e42d9530036de6450d3000cfc7058f5103e7c7219543006bc6454d3002cfe73d9510014fe71580540057f7550d4003ebf54590530363f41597400a6f7105873003cfe7610f51004fd72d9531005dc735515003f3c645535102edf65d4c43315df72d4f30004fe76d453003e7f52593530167e615455003e7c6555130135bc70d5243016bc6150540196dd73d95300367d4059740036be6419150376bc53d91530075f7550f300067d52583532f77b3019530006bf7655341316dc53d815302cdc735911003cfd70d8d50004fd73d85502577a20d95100057c755913061d7d72152530065d5218d5424e7f211951002fd7714c530014fc71595301079d7319130006dd52d8d5441e7f73d9543004bf7459543014fd70d8d10004fd72594430067d5258053004fe7690d10275dc754c530327b57190d41105bc70d5043034fc7458f5003edc5358f54046f661d8530004fd76953310067f6515130004ff7258f512a79f4290d3002edc7518d54014fe71d9510036be721913001cfe72d91311967f50d9530005dd7190d300073f54951300067e31d954302cfe76d8d5102edc53594436473d20d525400cfc70597430075d5218d54006dd42d8d54034fe76d91101975e30d95303667c4319543136bf6498d400055c7550d30034fc7458331004ff70590530073f54545402f67f3219530004ff7159643006bf6455153136bf6490d4011efa40d81430067f525933003e7f731951000cfe7058f54007b77155141004ff735874002dde7395130004fd72d8540004ff7158f54014ff70d9510004ff72d915100cfc705954303f3f7455351035be744c540006bf62d91530067d32d95301addf73595300067d65d4f43004ff72d91301957e70152530367e7459740106bc3019130014fc7650d41004fc7655131005ef7258530005dd74d4f30005df735515102cdc7359443385bf7250540036bf425874020e7c30997403663e4319543006df735954003cff7654d31036bc64d51301379f6490d3003e7e7299740006dd6318d10136bc20d913003ebe655514100cfc7058f41006bf6490d512c75f4319543004fd72590530f4ff7159510106bd1019130004ff725835303f3c71d5254476bf5119153035bc75d054003e7c6515131006be60d9153016bc61d054002ebf43582430067e31597403df3d52d51400367f7499740035bc74d4f40006dd5418d540067e411954301cfe72595310067d42d95100067f52d915303e7e7119543036d
  | 14 => 0x4ff705913100cfe7058e5403ebd545875401cfe72d85401cd7e76d51510147c7558f51006bd641915100cfc7650d40006de2018d54036fb4058254004ff7259731004ff715825400cfe7359330014fc76d0d31006dd6318d5058f9d32d50430067f52583315357d7294f51014fe71593300067e42195101e4ff7159541004fd70d9541005f771551410065f6394d51036bc6415131366bc301915300cfe7058c54006be52d913033e7c63d45505579e5150c4300dde7050d300067d525933011efa60d8143004fd71d9150005df7355253004fd73d915103f5f70d4e53014fe715954000cfe76d0d304769c5418d54007bb7050d40006bc75d9130006df735974300cfe7059543034ff769511025e7e41d951011f9d4050d300067f5258f413667f301954303edf5358f500067f62195300047f7559110004fd71d8d50005fb7050540006bd42584430067c755913003cfe76d0f50014fe7159543036be7519130014fc74597410057f7550d410367d4299740014fc71d8d5001cfc725973002f5e7514d3001cfc7258443006df2118d540067d62195300067c62195104779c5418d5403e7c659513102cfd74d8143034ff76153300073f52d913003c7c7558243275de75cc530406bf765074000cbc7650d4002cfc7694d41014fc75d85500067d65553302df9f42d4c432c65f43195430067d52d855003e7c7019530005ef7258131004fd73d815103e7f5258353006bf64d8553034fc7558354014fe71591300067c5059253016bc6150740004ff7259443004fd72d8d50006df63d0d500073f521915341e7f41d954303e7e76d5151196fa5058253005bf7454d50006be211915303e7f525875432dbf7290f41006be3019153006bd211915303e7c6515110004ff72d8154004fd74d95103779c53d50430379e7390f410067f72d9510005bc7454d10005bf7350540004fd7258341325bf7290d410367f41597400067f6594d1002cfe73d9151004fd764c7500073c7550f403773c53d91530079f7050c4302cff705804336d7f7395053006bf4259110004fe7694d400063d52d915317ddd7399530004ff745954303e7f525805402cfc7610d51005dd73d073003e7c7319530036bf4258043276df65d4d30005dd739515301cfe7259350006bc64545300063d6550740034fe76d47400075c73551512fe7c31d953001cfc72d81530067d3219510006dd6318d41036be64d075002cfc735954103e7e65547402addd7290d3026ddd724c530006bd521913003c7e76d9530005fb7054d30004ff7259330006bc62d913003e7f61d515103f5c74d4e5302cfc7690d51014fe745974102f5e62d4e5303e7c5059053005bc745815302e7e53597312467e20195100055c735515103cff765514100cfe745874003e7e6554f4002cff76cc750236bf40d
  | 15 => 0xc755911003f5e6315253004fe76551300067d5258331004ff7650d500057d759913003e7c65951100073d52d91301967f10d9530006bf64d4d301675e30195302c67c401954301cfc72d8d40004fd70d8554034ff76d0f510067f3259740376bc63d51400067c65d8d10004ff7158043036bc6555341006de4218d5400dbc70d5340036bc6415330006df63d4d4001cfc72d8d50005bc7454d513279e4350730014fe7650d313367c6354550004ff7258343006bd73d91530379f7350d40136bc10d9130006de41d8d540067d6519541005f571d51410067d5258754005bf7454740004fd7650f51166fa105805303e7d719974038fb970d5140014fe76d8540006ec7258d102e6be531913002edc735944302e7c535973002cfc735825402cfd70d85301667e2019530034fd73d8543035be74d4f4303e7e6594f406473c32d525432f9e43d07300367d545845400cfc70d8d1002f5e7514f43006be40d9131004ff725824303cfd71d91510067f52d8141006bd32d9153036bd75191301667e10195300067f6590d10036f4415874003ef7515845441e7c42d95430067c52d953003e7f6394f511b67d75d8d516075c21d4e5300cfe705925348ebe75d9153135be76191300367d54586540067c74d953003e7c7019543036f771587400057f7558d4048ebf50d9153006be61191300067e62d95300373c54551400067f6599130004ff7558730006be20d9153006de51d8d540367c4259740006bd52191530067e3019543006bc6119130006df6398d51005bf7458d100157e7114d5102d5d76d4e5303e7e731954314ddf73591300147e7694d5102cfc73586530a6f860581311967c70d9530156bd74d8d4101cfe72d814103d7e75d81541de7c70597400067d651954301cfc72d91102c6dc5418d54034ff76d0750006bd5319153004ff7159530476df5018d54004fd72d85430367d4359740036be6450750034ff76d0d10006df6390d41006bf42d8540004ff71595400067f211953001cfc72582540067f6510d1002ebf7459053006bf21d91530079c6450d30006dc6358154006f5215844303e7d73195430373f60d525402ddf74cc53001cfe725954313ef641586432577610d95100c6f860581410067d52d91530057e761954300cfd7358331004ff7058e540053c7550f4002edf325873024e7c31195100057c75591100067d74d954302cff7610f500067d5259353006dd3258f543eebd6250740006be10d9153136bd20d913000cfc7058f54086f461585500167c61d45500063f52d915303d7f72d515117e7d505973038ebf65d51402df5c54d8d5401cfe72591100067c50d95433779f32d5043005f77154d310c6f7105874055f9d5250c43004ff71593303febd65d53400067f65951302567c71d9510006be71d9153006dd70d8d54
  | 16 => 0x913002cfe73d8154004fe7650d100067f6514d400057f7558143006df6398d540067d62d9543034fc745825403d7f7455151004fd7258d100373c61d525401cfc72d9540004fd76d0d5003e7e7614d5101cfe7258f400079c6414d300067d6514f400067d5258f413bf9f32d0d4036e7e73d954302cfc7610d1003e7f73195430067f65d9130006bc61191532467f1019510034ff7650d31004fd76d4f41004fd7690d502f67c31195300079d7550c43004ff715935002cfd735973048f9f53d915357ddd72d4c43036bf6110d41005dd739525302cfe73d9110006bf644c5300057f75585432c6de6414d3000c7c7654550004fd71d81430373f655534103f3f71d525400dbe7050f40005fb7050d4003e7f6194d5101cfc725845302dde73d073025f7b10d9510004ff7258e540157e71d5151034ff7459740006bf7459130006bf64d0d30005f571151100067f621954302cff7694f410057d75d0f5102cfe76d8d5001cfe72d91100067f6219510004fd72595100c4ff705911002cfc73583542567f30d95102df5e54d8d540047e76195430067f65551430373c545514117e7f505973003cff76d53310067e421953000dbe76d5140036dd43580432567f71d9510006de3258f410067c71d9530385bd725054000cfe7059741004fd71d9130006df735913002cfc761533103e7f701953002cfc76cc5400047f72d953003c7f72195100067c41d95300347d75d815402cfe7655330034ff715845410ef6215844302ddd76d4c43004fd71d8d40376bc31d915303efb505835303e7e701951047f3f5290d4101cfe72d8d4102f9f7450f30034fe7614f410073f549533101cfe72593301675c30195300057e7598d1003e7e651951000d7e70d4550015f671d51410057f7558d410073f5495131004ff705944303d7c7590f5100ddc7650d3003f3f7455151004fd73d8141014fc7158354036be7610d4101cfe725913001cfe7258f410367d74597405ff5e40d4e5303f3f72d5254004fd73d9150006dd62d8d54034fc745835103ebc5459353006bf64d81531967f20d953003ebc5459350005df73591100057d7195053006df3258d1003cff76d513038dbe75d0d400079f3219130004fd7615331016f4615054020e7c50d915000cfe70d8d100067c75582433663c531915303e7c6515130004fd7650d102c67f4019543004fd75d9130006df5358343004ff70597314bf3f5290f4103e7e741951002efb705805303e7c5358454004ff72d9531006be72d915303efb505805301cfc725954002cff7658d1002ede7614d300067d321953002f9c6150c430367e4199740006be42d915302cff7690f5002f5c64d4e534673f5210d41004ff71591300067c60d954336e7f32d95430069d435804338f3c5414d40004ff7650d51005df735524303cf
  | 17 => 0x67c21195430373f62d52542dedc40d8d5448ebc52d91531de7c6055151006dd32587305457d72553510373f75551410067f21d95432775c53d4530014fc7158043036bf6190d41036f77158454036be6419110106bf301913000cfc76551500067c5059443037bb6050d403675c5315330014fc7159540006df1018d5401cfc72d814303cfc7558f4002ede7690d300057f72d9510036bc4358454326bf6450730005bf74581530067f215974003e7d721954303f776114d5103e7c721953001cfe7258c54154ff73591312eebc32d913047f3d5290d413667f62152536473d21d5254006ef725911000cfc735973002cfc7610d500057d72d953003e7c50583543673e5319153006dc62d8d5402cfc7694d104fd7d7294d510373f75553412eebf31d913038f3c65d514003cfe75d8141376bf6418d54035be7494d4041d7f729525300dde704c5300067f52d81431de7d50597404bf3d5290f410067c6599110006bc72d913002edf325804303efb5058054004fd72d8d4103e7c65951301de7c50595400067c6119543004fd7614d40006de1018d540067f52d8d5403f5e63950532dedc64d4d3002edc63d4d411967c20d95300067f755954102f9f6450f3002f9c6250c43004ff755874002cfc7690d1001cfe725834132ebf64d073013ebe7690d412567f40d95100063f65d913003e7f52584530057d72d95432567c40d9510476dc5218d5400cfc705925313dbe7310d41006df73595432567d70d9510014fc735973138ebd65d514003f77615515124e7c4119510316dd65d4f300167c61545500075f6590d304673d5210d41004fd76d533002cfc76d51430373e65507400069f7650c43005dc735954002ebc43590532467f201951001cfe725944341e7d641525302efb7058253004fd76d453001cfc7259643006bf54582430067f52d8d4102ddf764c73003e7f7019510004fd7259740366be5319153014fc71d9153005bd74995304a5bd72551410067e321954300ddc70d4d30004fd70d85434ed7d7214d5100dbe70d05400067f5258341004fd73d854002cfe76953310057f7550d500067f6558530005bd7590d411f67d50d954038dbc75505400367d4159740037b76110d41036be751915302ebc4359253006be5119130005df7355330004ff715935303e7c605535103ebe6595141004fd71d9540066f661d854003cfc75587402975f5250d3000dfa70d4d304ddbd725534102dde73d52430077771551512dedf65d4f430075e50d8d540367e74997402dede74d8d540d6f710d85400073f651913003cfe7690f500067d52d8141036be731913000cfe7058f5100cfd73d8530005bd7590f410067f42d953002edc63d0d1003f3e70d5254035be7390d410069c64d4d30036dc4358e545f57d729505300dde7090d30036bc731
  | 18 => 0xd70d9530036bd7615243014fc7158f505275c53d0f51006df73597400063c65d913040f3f5250f4002edd7018d5403f5c72d4e530067d6554f430063d649525333d7f7590f510067e4019543004fd70d8d54034fc7558f540063d65d524300cfc70597310367c4099740004fd72d91300367f409974002cfc769533141e7d64952532775f5214d300067d52d8d54006be511915303e7c6594f41004ff74587530067f52597430067e32d95100067d70d954301cfc72583533367f6314d5101cfe72d9541004ff7359350047d4614c5300067f5259643004fd76d0730004ff765453003f3e71d5254004ff7058654014fc76d4d31014fe71d8d500067f5258e54034fe74d953063f3e21d525403f3d71d52541f67f50d9540004ff74586530067d52583410379e631524301cfc7258354004ff72d95100067f52595310057f7550f5002cfc73d9530476bd65d50430079d321913011cff70591300067c62d953002cdc73597401de7f5059740006dd3258d100067d72d9543036dc4358c54004ff71597431667f101953003e7d71195100367c54597403ef3f52507404769f53191532975d5250d30036bc7458f4103e3d76d525402ddf7214d302c6dc4118d54036fb405834302ebf74592530067d525845303cfe75d9131036be731915311fd87050d3003ebe54587541de7d70597402c73e5414f41034ff765525302edf6090d3004dec725853048f3c50d52430067e715974001cfc72583310067d32d9543006bc51d91301967f70d953002edc53580430067e20d95434973e505514101cfe7259741014ff70d8d10004ff7359543035bc70152430379e7310d4102cfc7358643014fe76d8530004fe76151310057e75991100067d52d8d41036bd721915311f9f4050f3000d7c70545500067d32597400047f7559130006bc645855302ebe6350d4036f5c4395053014fe76d855302dde7315130004fd73d8554037bb60505400047f75591312467c20195100067e10d9543006fb70595100073f5495110006df2018d540067c6599130034fd70d8540005f5719515103e7e6519541005dd739533003d7c7590d51006bd62d9153004fd7258754015bc7190d4102ebf4358043036bc73191534cf3e5055341005bd71152430067e6219530015bc7110d412dedf40d8d541de7e1059740005dd7414d301de7e205974003e7e76d4550004ff745875000df8704c5300067c6558d1011ddd7490d300b6fa105833102ede7218d5435ddd72d4f3003e7e701953002f9e43d0d301667c6014d51006f9205804320e7f30997400067f4219510006bf10d91535679f7250c4332dbf7590f41005ef7258d10006de70d8d540369c4358c5403e7d7319510006bf72d9130006be50d91530067f655514033e7c53d8553004fd76d0d10037b84050d4003e7f7119543
  | 19 => 0x4f410067f42195300f6f710d8550004fc7650d5003e7e65553301667c201953000cfe76d514002ef7315873002dde75d4d30004fd73d954003e7c65d4d313679e431533003cfc7559330005bd7095141005bd7494f402c67f6514f41006bd6419110006bf4259353036bf6050d4002cfc73d913003d7e75d0d51004fd75d913102cfc7615330006dd3258043136bd73d91300067f659954102fdb604c530036bf7119153004fd725973000d7c7054750006bf6410d500067c655853048f9d73d52431967d73d9530016dc614c730014fe7158254476bd76d504302cfe769515325e7c21d9510035bc75d0d401379f73d9130006bc72d915313ebf41d91310073c6519130034fe76d4d4300cdc764c5300adec7258131004fd7259253004fd72580530373c62d5254036bf41582543ef3d52507400067c71d954302ef73158653004ff7654f41184fd7654d310067d52d855402dde73951532df9f43d4f4003e7f629505303d7d7694f51004df73597400067f65d9110004ff725835103f777154750036dc4358f40006bd72d915336f5c53953300067e50590530067d65d524302cfe73d91300c6fa10d814101cfc725974002ddc73d5330366bf3019153004fd7258f500067c3159740035be7414d4003f3f54951530067f75595401667f201953002e7c535944302cfc7359253006bc20d915302ddf7214f4336e7c31d954301cfe72d8154037b77150740006f771591100067f73d951019d7e7314d515659f7250c43004fd725935103e7e6554f430067c65d9130006f771591310367e4259740006de32d8d541967d20d953000cbe76d514003d7e7495053006bd651913000cde76d4d3020f3c50d53403b5bf7250d405579c2150c43004ff72d954002f9e64d4c4300cfe70593533bf9d32d0d4000ddc7050d300057d75d0d510067e5059253014fc71d9510036bf6050540006df6354d500067e52d9530004fe7614d400067c65591103febf54d8154006bf64d4530036bc701913003ebf745935103e7c5459053006dc2018d540073e5414d4100cfc70d915336e7f6295253004ff7259331006bd64191310067e42d9543046f421d8530014fe7159730014fd755875000df87054d3003cfc7559130004fd7614d4102edc5358253006dc60d8d540067c74d9510014fe71d915003e7e73997402dedf6319153015bc7190f4103e7f72195432c67d6495053005bd7315140004fc765453001cfe72d8d512c6df4218d540067c411953002edf624c730037bb60d05402c5dd7414f4303f3c5455150036bf60d054002fdb60d4d300367e4399740014fe71596430067d52d81431de7c50d81540047d72d954300d7c76545500079c53d0d40004ff7655130004fd7259353004ff7258f410067d525974341e7e74d95435579c7150c43014fc71d91101967
  | 20 => 0x67f65d0d30006bc645815301cfc72d8543036f8405834303e7c7399740266dd624c53011edf3058f4002dde75d4f431de7f65551500067e50d95432577810d9510004fd76951100367c645515102f5f62d4e5302cfe7359443034fc7654f41004ff75583410067c50d953100cfe7058743004fd7655330004fd70d91510067e60195432467d30195100167e615475000cfc73d8131004ff7158c54014fe7158f40005dc7359150004fd73d9541006dc63d81540067c52d95430373e75d5043004ff735835400cfe7059131006be6519130004ff7458f51006dc61d8d54004ff745953101cfe725845303cfe76d954103ebc65551410367c439974002fdb60cc530006de61d8d54006dc7359110004fd76d0f510367e545974000dbc7050f4003cfe75d8d10006be21d9130036fb705805401cfc72597430067c5259740006dc735974050d7d7255151014fe71d815313ebd41d913103e7c65d5140005bd7414f401de7e70597400075c535453003e7d701954302f9e6250c43004fd765073002cfe73d8151004ff70584432567e40d9510136be30d9130236bd40d9110004ff7259053037b76190d41006bf42d9153005f77154d51006bf6450d311f6bd74d95400373d65d534002f5d64d4e530067e32997400065f6514d3001cfc72d8131034ff76951300067c72d954340f3d5250f40035bc7454f4001cfc725925300cfe70597310067f65d4d3003e7f5258c542467d2019510136bd10d913048f3f52152430067d5258054004fd70d953102cff70d9130015f671951511fef65158654006df7358d10014fc715935303e7c65d5141004fd76551300067f52d815100cfc7058454036be645525302edc63d4d400071c7550c43014fc76551510073c7550d40004fd72596430075f5394d41015f67194d51004ff7158353006be32191303357e73d5151004bf7459531035be7414d4100cff71d95100077920d9510034fe74d813100d7c70d4550006bf6490d5003f3c73d525441e7c74d9543004bf7458f51006bc745953029ddd7250d3002f5c5354d301fe7f51d9541006dc21d8d541967c10d953002cdc735954002f9f6550c436373c30d52542b75d5214d30006bf52d9130004fd72d8d10004fd72587400075f5394f410075f5394d400067d525964300dfa7014d10034fe74d81510067d5258e54014fc7159130005be74995301de7f705974020e7e60d5151035be7414f41006bd21d9130036bf40584540073d52191530077761545500075c6590d30006df325874303d7e75d0f51004fe7690d510067d525953103f3f549515103f5c70d4e5303f5e72d4e5303e7f5258f510373e6550f40005dc7358154004ff7359741004ff7558043036bd73191531957e76195301de7e6055351005dd7315330014fc7158f540067c5059741034fe76d
  | 21 => 0xe7458341004fd7614d100367e409974003e7f741953001cfc72d9531014fc71d95400067d71d95300067c65d0d1000cfc74d81410067d52d815100cfe70d8d54004ff715805354f9e7050c430067e72d9543004fd72d954102dde739525301cfc72d8540006bc621915341e7c41d95430051c7550c43015be7155341006be3219153004fe7650d5159f3d521524302edc6450f30366bf6415330006bf42d8141375bd73d524300cfe70d911002ddc73551304567d6254750014fc735833101cfe7259253004fd72597410053c7550d400067f65d5141004ff7654d41006df7359541015bc71551410067d5258c545067d6255151004fd76d4d414779f54d4c4301cfc72d8d1000cfe70d95430067f7559110005bf74545400067f20d9543006bf6454d3027edd62cc5300367c4159740004fd72d8554006bd20d9153415bd7250f403357f7590d5103f3f5495253014fd70d95101de7f2059740036bf7319153004ff7458331006bd52d91300367c5459443266df624c53003cfe75d8543014fc715973001cfe72d814302cfc75593535cf5d5214f4302e7f7559730015bc715534148ebf73d91530079f5490d30036bc745974000cfc70596430157c7655151006bf649515303cff76d51310067f52d913155f9e7250c43004ff7258f50005f571d4d31036be701915303edf7358f54004fd7654d430067f5258254006bd6419153035bf7650f40035bf72152430067c7558f41035be75d5243014fe76d855002cfc74597430067f5258f40004fc7654d4123ebd41d9110037bb6015140004fd73d91100067e31195432c67c6414d510067f52d9541006dd2018d54375bd73d50430067d5258f5103ebf545935102ede6318d10004fe76951100e4ff7059510006bc211913037ebf625054003e7e71997400067f5259530004fd70d8d51035be75d504360f5c42d4e5303f77715455002f5c5354f4302e9c6450f30014fc71d8d405275f5214f4334ddf7250f30006df6394d50004fd725973103e7c65d4d10036bc6490d5000cfe7059443036bc6410d50006bc41d9153396bf62d0540087746154550004fd72d9131006bd71d913003e7c719974023ebf41d9110006be52d91530067f10d95431de7f1059740014fc7654d31006bc60d91530d6fa1058341325bf7590d41014fe73593310067c2199740136bc30d9130015f671d0d312467c1019510036bc64d0d31004ff7259350006dd6318d40005dc735954100dbe70d0d40006de5218d540067f654c53002cff7690d10006bf75d913001cfe72d8d500067c6219530004ff7358254005df73545302c75c4319543006bd75d91300067f6559130006bc64d853003cfd73d855303e7c711954301cfc725835103e7e63952530067d7359740005df744c7300067f525954303cfe76d9540006bf64d5130
  | 22 => 0x8d54034fc76d4d431667c10195300067f52d85305873e50d5043036be71191531fe7d51d95412c67f411954336e7f6518d540067d5258f4003e7c65d4d300047f725974000cfe7059351004ff71594430367e545944302f5e53d4d430067d52d913100df8705514002edf3058453005dc7358554006bc21191530067f7559510006bd4258740034ff7695131005dd74cc530316df53d815300cfd71d8d10005fb7054550006df62d8d540157e715535119f767194d511667d3019530004ff74580530067e505974303ef771587535e5dd72d4f431de7c20597400067d715974001cfc7259053036f44158743107b830191300067c20d954303cfe76d0f514ddbf7255341004fd73d81540067e73597400057c7558d410373e54d52431967e6094d51034fc76d0d5000cfe70584530067d5259530004fd7258c54015be715514103e7e65d524302ebe4359331006bd70d9153004ff7259643004ff7059643006bf65191300a5f57198d10006bf5458043046f631d8530004fd74d8530004ff72d8d50014fd75d815103cff7655243006dc63585543673c65152430157c7155351186f651d85530373d63d525413cfe7619131216bf41d915102edd7118d540373e7515243004fd72d9110014fc7558351215bf745954100cfc745974001cfe72d854348ebf53d9153035bc7494f4100cfc705944300cfc70595410067d52d954103f3e74950530067f725974003cfc7558341034fd70d954002f5d76d4e5327edf62cc5302577410d951043d7d7254550004ff7559330366bf651524348ebd651524302cfe73d855003edf5358f54006bc42d9110006bd425824336d7d739525302ef8305824303d7d76950530067d42d954303f3e73d52542c65c43195430067e211954302ebc4359331006df6398d41006dc735954002efb705804302cff7614f4141e7f42d9543014fe715935017cfd7654d3003ebf7459353006bc10d91531b5df7359531036bf7119130325be739514100dbc70d5140006bd42d91300057c7550d40034fc7654d430367f42597400373d76d52541fcfe76195414779f73d504301cfe725824320e7e50d91504e67d6214d510075c7550f3002ede7518d5403f5f53552530067e76195104773c50d504330ddf724c730006df6310d50476dd65d4c430067f6558543006df63d0d51006dc1018d544779f74d4c4302e7e535964303cfc7558043004ff75583310367e6455151006bf20d91532fe7c32d95300057d721951003c7f72997401667d2019530036be701913024e7d31195100075c53d0d51006bf6454530004ff72d81513367e535953102cfc73597412fe7f31d953020ebf40d9150005bf7454d3001cfe725875400cbc7459740036df7358c5400cfc70d9151006dd3258743004fe76d4d1003e7e651953103cfc7558f41014f
  | 23 => 0x5f57194d5102fd7714c7300e6fa10d8151004ff705845345d7d72547500067f52d85530079f32d9130004ff764c750004fc764c540004ff72d8153006be41d91300c5f57199110005f97095150106bc6010d410067c65d0d30004ff76553300067d5259543004ff705865317efa30d815302edf32583312eebe53d9130006de62d8d5403ebc659514102cdc7359541005bd74d4f43004fd7259110006bd42580433279c6390d41004fd71d9153004fc76505303673e53152430067c651911000cfc705845317ef8605815303e7c7119510006bd42591100067c654c530006de31d8d5402ebe4359053315dc754c73001cfe7258f5003cff7654d3002cfc745834303e7f6254750005f77150d310067d431954302cfe73d915001cfe72d8554004ff7258341004ff72583540077b7054550014fc71d81530067f65d45300073f5495330014fe76d0d31004fd76d533160f5f21d4e530379c4350d40004ff735834103c7c7558d1002cff7614f40004fd70d8553036bf7519153005bd73d5340006bd72d91300067f75591315457f725535100cfc7059741036bf731913002edf3058643006be61d913002efb30582430067e505944303e7e721954303e7d741954302edc6314f4003ebf54593503673c4315253006bc42d9151036bf425834133e7d7694f515067f625515103e7c505935002f5e75d4c430067f74d951003e7c6594d40035bf7510d41036bc6490d5100dbc70d0d4000dde7014d30004fe7654d1003e7d711953033e7d6394f5102cfc76507301aedf30d8d50006bf7459530005bf7454f43485bd7290d4102cfc765533002ef4315845303ef45158753034fc76951100067d71d9543036bf601514002f9e4354f4302dde7395330004fd7259330005f97010d10004fd7610d1000dde70cc530025ec7258d10006dc32d8d515af3e50d5243034fc76d0550004fd72d953000cfe70d915102efb705824302ef7715873002f5e61d4e53036bc6410d51006f771595311de7e5059540005bf7454d31035be74cc7400067f6518d1002f5c61d4e53035bd76d50430047d72d951002cfc7614d1002edf7118d540067c51d953002ef7715864303e7c6594d4125e7e31d9510005f571d0d31006bc61d913001cfc72d814103cfe75d8530004fe76d0550226dd30d8d10005f970d4d304c5bd7290f4103cfc75593310057c7550d41136bc405824301cfe72595410067c3219510004ff735911000dbe7050d400079f6450d3003e7f70997400373e75d534001cfc72d915003f5f5394d50014fc7159543004fd72582434a5bf725514102ddc7355131004fd7610d501967c5058253034fd73d8143004fe76d5131014fc715905324e7f3119510004fd75d81430067f52d911000cfe76951505779d42d4c4300cfc70d8d542a79d4290d3002ede741
  | 24 => 0xc73d91301acff735953003e7c655514302f5e75d4f3002cff755944303e7f5258f5011f9d4050f30004ff725954060f5e42d4e53006df72d8d5425e7d41d95101967e30d953002ebe435925302cfc765473020e7e50583540067e21d953002cfc735964303e7f52587500379c4350d4137f3f525054002cff7610f510067f7558f41106bf6418d4002cfe76d07302eebe73d91300079f6414d300067e76195430067f52d95300073f65d9130036de435834303e7f6294f510057c7558543006bd42d85402f67c321953003e7d721953001cfc72d8d511de7e50d81540067d20d9543006de60d8d54004fe7614d100067f65995430067e72d9510015f47155141476dc5118d543973f52d0540004ff7259531004fd70d8d41036bf6290f41014fe765514125e7f41d9510036be6495253014fc71583431967d10d95301de7d205974003cff76d4f41004ff735835101cfe7259530006df6390d40006dc63d85542f67f3119530034fe7694f40006be3119130004fe764c5500067e31997404779c5319153034fc7459531005df73551400067f651513102ddc75cc530005bd74cc7400067c601954300df8705515017edf3058f5003e7c53587530067f52d8131004fe76d0d50014fc71592533667f3219543326bc435913103cff76d5110007db704c530006fb70591100067e621954302ddc7355331007d7614c53003e7d7615253195de7614d300a6fa60d813103cfc7558730004fd76153300067e52d9543004fe76cc550036fb70583412dedf75d8d540367f755974102ef8305825330ddd724c7300079f735534100dfa709515022edd31d8d1002f9d6150c4301cfe72d8d40376bc32d91530067d52d853003ef850583510067d52d91100067e525974002cfe73d8554006be51d91303657d731525303f5f74d4e53006bf6455151004ff72586530067c7359740004fd725845302e7f7559643014fe76d855403e7e65d454003c7c755913100cfc70d8d510055c7550f3001cfe7258653006be40d9153006df63d0d1036f5c7395053376bf31d915343d7f725455002edc7359730034fe7694f41006bf70d9153006be70d915303e7f5258351004ff76553312dede64d4d30136bc6090d4102cfc7358341006be10191530067d21d9530005ef7259110004ff7458730004ff7655110004ff7650530006bc10191530367c545974100dfa7010d10015f47150d41004fd7615110006bf64151310067f525864301cfe72d953103ef751587532c67c42195430067f52d8d50036bc54582540067f52d915102ef8305804324e7f76547504e67f6214d512567d40d951002f9c6050c430b4ff7158d10234fe7619110034bc745953103cfc7650f51014fe76d854303f5c53951531cdbe76951415ff5e10d4e531e7b471551410067c65591305ff5e20d4e53
  | 25 => 0x813101cfc7259350014fd73d813102edf7218d540067d52d953020f3c50d514003cfd73d8153004ff72595302467e301951003f5e7394f510067f6554d30004ff72d85540c5bd71d054003ef45158454004fd72595306473e32d525424e7e211951002cfc73580540067c42d951000dbc701514041f3c5494f400d5f77159110004ff7558f4103e7c6554d3103d7c7550d50004ff7159253004fd7258054036f84058054036bf65d534003cfd71d81510047f755824314edf30d8d40006be62d915301cfc7258f4045d7f7254750004fd7259543036df7358e5448ebf51d9153034fc761511000cfc7059331136bf30d91303657d76152533af3f5250d400067e505974102dde735073000cfc76d5140006fb70595300367d4099740004ff7258643034bc7458d10004fc7650d1001cfe7259510006f771595410067f7159740004ff7654740035bf71505402c67d769505303cfe7610f5020fba70d5140006df6398d4002cfc73587540079c64d4d300373e60d5254004ff71580540067f765535102ef771584530067f65d4d432dedf41d8d541df7a50d81540067c10d954355f1f5250c4302cff7610d10476df5118d540057f7550d30034fc74586540067d5258351036be711913000cfc7058e540067d52d915100cfc70586530373d60d52540057f72d9543005f57190d410067d6219543004fd7258e5403cfc764c7500067f6550d100067d65d4f400067d52586430a4ff7058d100067e71d9543004ff72582530157e71551513279f3210d41006dc32d8d10036bc64d51311967c30d953002cfe76d5330004ff7258f401de7c10597400079f735514100cfe7058f41004fd7259331035bc7454740005df735514103d7f73152535bdbd72d5243595bd72d5043034fc76d0530004fd72d8550006bc651913003c7e76d9543004fe76545400067d52d8d501957e70952532567e70d951002ede6318d5101cfc7258c5406dec725854022edf31d8d1001cfe72587400067f6594d41006df6350d4102f9f6150c430075f73553510367e545974103cfe75d814303cfc76d453002f5f61d4e53136bf70d9130004ff72580540067f65d5130326be43591310157c715515124e7d21195101de7d305974001cfe72d8553214ff745954120f3e50d53401b6df31d8d510067f74d9530036bd731913003cfe76d95314bebd6290f41066f461585400073f6455151014fc71d913000cfc70d9110004fd76d055016ef710584530057f72d953002edc6310d1003cfd70d855000cfc705865402cfd71d913103e7d7019530005dd744c53048ebc51d915354f9c5050c4300dde70d4d303673f641525301cfe725875300dde7050f3002cfc7359351006dc70d8d540067c505973101cfe7258043006df73595302567d71d95101b6f631587530c6fa60d8141136b
  | 26 => 0x367d43997400067d3219543005bd7414f410057f7559130006df6314d41015be7690d4101cfc7258f51036be64191535679d7250c4302edc43590536075f10d4e53034fc764c740036bc6450d3003e7e6554540006bf6499151004ff72d9153004fd7259541005bf7454d102c75f739505302e7c53597310047f72d954303f5e74d4e53035bf721514002f5d61d4e530047f7558d1000cfe7059531014fc7159350014fc71d8143005bd744c7403af3d5250d4048ebf52d915301cfc7258e5403cfc76507500067e2019543005dd71d4d30136bf40d9130136be70d9130006df32d8d54106bc501913050d7f7255151136be6090d410067f655511036f3e6495253004fe7654d41005bd711514011fb87050d4041e7f43d95434b5bd729514102edc6390d4103e7c70997400367f435974001cfc72587404769f5418d5400cdc735973000cfe76d81540067e50d9531006dd72d8d54005dc7355110004fd7690f511def860581540067d42d95300047d729974000ddc7014d300065c5018d54014fc71597400067f32d95101e73f515514100cfc76d0d30004ff71583540067f72d9543526dc50d8d5403e7c7419530005bd7414d4001cfe725933103cfe76cc75003e7c505805303cfe76d9510036bc645053000cfc7558750046f46158530004ff7058f5400cfe7650d30476df5218d54037b7715054003e7c65d51100079c644c530337757194d510379c43551430067f21195431e73f5155341036dc6490d300065f52d8d540057f7550d314779f5418d54106be6010d410075c5018d5411dbd7490d402467c30195100077521d95100067d5258f50316dd76d4f3002e9c4359053004ff735845401cfc72595430067c6598d100367c74997400367d4199740004ff764c5500079d32d913000cfc7654d300067f65581432dedc42d8d54006dd32583310067f65545300067d654c740004ff705935337f3d5250540376be63d534003e7c65d4530004fd725953100cfe70d913119ef6515865302cfc755875303e7c7319543086f661d85500067d6219510136be4058243006dd2118d543279c5310d410075f52d8d54034fc74587300079f53d0d4000dbc70507400067f65951310067d525875000ddc704c5300067f52595100067f735974000cfe7059053194fe76195300067e62195100079f7550c430067d52d81310cdec72581410367f41997402467d1019510036bc64d0530036be6419131005df735514301cfe72d81310067f52d8d4003f5f5395253034fc7458d100067c70d95430067f5258343155be7610d41006df32d8d4103cff76551400369c6490d303973d52d0540105be76d0d40006be42d9110014fc7559351005bd7494d40004fd72d91510067c51597303673f651524354f9c7050c4332f9c4314f41004fd725844303cfe75d
  | 27 => 0xc3119543014fe7694d511967c73d9530004fc7654d400067d73d951041e7e6494f51035bc7454d41004fd72583540079d4310d500067e74d9530034fc7458353015f6711511003e7c65d513020efa405835433d7f7294f511e7747155151014fc7158e5402ddc73551531aefa3058353006dd5218d5402fdb6090d3001cfe72586540067f65d85430067e42195430373e63d5254004fd72d8141004fe7655110036bc64d5330275dc7550d300073c65d9130006f721d853002cfe76d8d100047d721953048ebd76d52430067f52597300373c63d5254526dd6514f430067f3299740006bf42d9131004ff7058c542e6bf3219130014fc71d95430067d42195106075c41d4e53126f661d8543034fc745875300ddc70d4f30396bd62d054003e7f515905303cfe76d0750136fa405824302cfe761533000cfc70d9131275de7550d300067e61d9530526de75d8d54014fc71d8154366bf64195430f6fa1058351034fc76951312c75c6514f430067d52d8d40006bf74591310067e211953003e7d74195302775f52d4d3002dde73d51430075d52d8d54376bc30d91531667e301953049f3f52551410067d5259510004ff74583510067d52582542e7bb3019130014fc71d8d102567d50d95100067c61d95300067f75582432df9c40d4c430057d7494f51004fd76d053052e7d6294f51006bd6490f50006be6119153034ff761533100cfe70d8d511f6fa505825401cfc72d8d5436e7c32d9543006de71d8d54005f97014d10376bf649954301cfc72591101379c4090d30004ff7258454004fd7614f4103cfc76d513100dfa7090d400e6fa50d81510079c64cc53000cfe76551400063f5219130004df73595430075f6550d301667d10195303475f5250f30004fd71d8d5400dbc7050d40006dc72d8d540067c325974060f5f20d4e530367f7559740006df70d8d54276df535825336e7f31d95434d73f525534103e7c741954342dbd72d5340006bd65d91300367c4299740004ff7259130006fb20d81510065d65d4f4302cfc76cc550006de40d8d54005de7618d540067e101954325f7621d9510006dd20d8d540073f52d9153476df5418d5401cfe7258d100e4fd7699510034ff7695331375bf73d50430067d65cc7400073f65d514014cff73591300067f6514d102c6de5418d5402cff71d913102edf65d4f30006df6354d51006be30d9153035bc7454d40006be42d9151004ff72d9110004fc764c550006de5018d54006dc71d8d54006bd6410f50005bd7414d41006bd21d915333f5c5310f51006be21d9153004ff7258740034fd70d8d4002cfe769533063f3c21d52540067d211953003e7c6554d10006be311915302f9c6550c43005dc735911001cfe72597312547e761951055f1d5250c43004fd7694d10005df7359151004ff7258743
  | 28 => 0x83543475d5250f300067f525865402efb305804338f3f5215140004ff75591100079d4310f500067e41d95302cf5d52d4d300057f7550f513673c6415253006dd4218d5432ebc63d054003e7c6594d105279c54d8d542567e20d9510014be7690d41034bc7459530104be76d0d4003cfe75d91300e6f8605815102dde75d4c4332ebe43d85430f5f7715951001cfe72583314d73d52553415275f52d4f4301cfc72582432fe7c43d953000dbe705074000cfc7058754006bd42d9153034ff761513002cfe76d8d4101cfc7259330004fd7610d510063d52191300157e7694d515659d7250c430067d32d951002f9d6550c4302cfd75d8153037b76155141014fe7654d3102f9d6250c4302dde731533000cfe70d8d41006bd645525301cfe72d855000df87050d4000ddc70cc530006df6398d1025e7f21d951003e7e6514f4003f5e7314d512df9c74d4c43006be65d913003e7f52590531965d73d953000cfe70d85530073d52d9153035bc7454d4303e7c6554d300067e51d9530034be76d91302e6bc531913001cfe725974020dbf745954002cfe73d85402567e10d95101adde7514d30005bf7454d5103cfc755824303f3c70d525401cfc725953100cfc7458f4003cfe75d8d401e5bd7595141006bd52d9153006bc7458f511967e5058253006be32d9130006dd32d8d4132ebc43d85430067d651953101cfc725973101cfe7258f51004ff705954300dde704c7300067c51d95432675f524c530006bf64991100067d65d533033f5c53d4730006bd6219130006bf64951514679d3210d411aede76d4d305a5bd7215243006bf71d915302f5e60d4e535ff5c20d4e53004ff725833100cfd74583410057c755854054f9e1050c43006bf6550540034fc7654740014fe7159443004ff765075003edf7358f50004fd725954002edf6050d3000ddc764c530476bc5019153005df735515002edd7218d54036bf6155141005dc73551510347c75583542477a20195100e6f820d8151014fe71d8d4000cfe745974054f9e2050c43034fe7459443326be4358743004fd76d4740004ff7258753004fd72587531967f6598d50004ff705864303ebf5459353006bd65507400075f32d9530005fb7050d30135be70152430057f75591103b5bd7250d4002ef8305805300cfc7558f500067c51d9540006bf65d05400067f5258443036bc6455130014fe71583540067f75591300067d5258343036bc43587430a6fa10d8131005be76191536373e30d52541667c3019530004fd7258f4101cec725911055f9f2150c43006bc4259053035bc7454f410075f73551513779c73d504360f5f42d4e5303efb505835100cfc7650d30014fe7158e5437ebd6250540036bf415974000dde76d4d30004ff72593510065d52d8d540067c5159740036f771587433667
  | 29 => 0x803c0100050098050010000000035006600001f800018800400302b800c01200300040480030060b180aa003001807c06e00101481041e2075020003400e004001003800000700a80046cc30f00200b43c801803d8034002398001803037005801c807000000100a8048030000003800004200201900040240e70001e1401c07b03b006000c003006000400e00a0000030096154389000000807701a805c44400501e000c00000600b012400200c07b002003600000182580f40110438000002000001004c012006008145c02a35e0040b1c016006002bb3454c267000000802800d004802886004108a002c1c40000198010000005000010c020009014801439a00308b800400000d002005800003f00d00280042ff0080000006038005881805c51500383b40002d1509884c0600030090018002171015953800e02800000e80000000008064000005003808c0000040058b0c02a01d00000000000b903c0018008000000000000a016000004403201e00b00280002a30000071c401ae00282b40021930018024112f6c000844001a02301f81e000c00400180500e6000000000c0b6016000000c00803d00181bc01c00d00400b8002004004171803e0250000001d8a418063000400401f002803803c0000000020000012015004401e00000380000260001f5003c01600000111e005c04b000003850a00200d80d4000000000800400601100000580001f519e002832603d0330008044015093801400201b002009001a02f000800401e12530f800001c002009002007800300a88a4002010004801803001d00a002000402704a01b4d0207a020037009600000b01e43dc89105c041c0620b7004800002800a00580100000010b899b0056002022000401401e002007405400000c0000008010002803413c0006fc800003600102d054c02401003080b400200002a8070006034018802447e03f16c00005b400020f000800a00e01f003806000000009fc00400003e09bc00000104b80000000024ce3490112002008818c052000017000008403d007002c0f4004004ff72593531675f731953003f5e70d4e531e73d5155341004fe7650d50014fc7158353004ff74597310065f65d4d300067d65d47400067d5259730006de20d8d54006df6394d5100ddc7050f30106bd5019130326bc635054002edd7614f430067c62d9510004fc76545402fe7e43d953003e7f615515102f9e6150c43006bf64d8530006bf62191300063f521915300cfc76d4d3002efb305825348ebe6590f4101cfe72d95100075f6514d30006bc21d9130004fd72583530067f6515110005df7150d3003e7c6554530004fe76d51102567f50d95100057c7558141037bb60d0d40034fe76d913049f3d525514103f3f70d525402cfe76d4730014fc7558f5103efb705
  | 30 => 0x800401c005013800404201200400040ba01504581b400400201f0108050018001804000602203882940240030aa804c04e011021000018e0f104e802800012200200fc68a109001000400001002d00100105d10aa817c00e01f013958000000a000000c11801902280000320c600a014406e00000000300040000000bd801002101681640020310140fd414600203b0131aa60020058000080078000012c03c068000801c002038033002402a1b6000000000607b003801802e00800500180720270168020114ca5015805800200500000300200020018040008002017800c02e000003807405c01e000809c4b0015037004000000a00f833c024000000011802809100503f402c5750020588aae000000800800a000066804407c004000003c01a0aa213004401800100a87bc000000020803006201d000101400a00a001800000000a000073548227d01288ac00e000000000cc6c00f008800001c0000060028000001000001002600510981b000221601a812c000069000802c00800200a05b80364b31b200080182050080030000019001000051a00d00000000ae06b03a09b00a644900081c003400600000b85560010cf800406200a000843400a00f001000005600303c003804e000000894c004000065001c01a004000001c03e00a00c801000000100c004405e0000010e5001012a001000001603e000000005200700300040080240380044084000049825000a014004000402200000c816000e00402a8004000002000800c01e0000310a3806e02a004004c05c0280b804bc00000000980900000010e200440300000058384026003000001c008001044800000600100a004000815e00280204ee00600300a017401401e002401e04b01f800405600000900285100060020008030007000000000600101f8c9410e010014003805a005057012406600007f146401e03900001ac04400200280849ac00100a800408603c0030060006027008000403406300b890014401300080ec000015004801002001400080f4002024000800400601e001802004a03200180040760b3001002806e10200a20a002202d46d00212f2005002801000000b00300140000de229807800000500000080fe00302900300180160d8920000001f0000144078000000003000000000280000400000050010006007064082008c03e001001802a005017805c08a01f003807c11800900e801c2e403300d804000a00601300040020000f380d471e00903700000260054e1006800a04200004f007c0021a0001807207f00f034409c02b001003c04202f0008000014000032000c61e1200018028006020002000c01000d0040000012016001889c0d40b301e803c00a000008801000200200a00f42000010240008008006081800018600700a001811200000d008c0f6
  | 31 => 0x1c80740008cb402c06104a80746b6003001800c036009001801000a01b000013000002201d055802021b000003401c2b30000000000023000007c01e00800e804801e028005801803600001b00040d2010002018000c00b01c0014000017015801401000a000889087400600d01056d8007000800000001102d80440026db001000400a028049898c64200200380340040020018014000d4501686e000400105f03d4002000039013803800700d00040120100060bd0004002006801806e05f0098be4000057015801000800000900381b201b0000048002010006803001600501513c803a036003800804e04f02080a40cc00000200240060020008000008004004800c11e00c00003f40080080190028132032006802401200b01f809805c00002400a800000500000501b800000380040620010380000004060007803000a01d000003c26401800303b40320020040004006001003860000607900001a000a20a00b804008e01200c8000000002016000400040d039002c1c600000080140260030168024058874003004127a01d009800005800a00500000d600200488a8008000004800000401000301ec01e0003ce81380080160000560004771001005006600200080f000a01b03580281f200d006800003a002010800c11c06400f000400c000003800800a05b000800800e01309103a802029d000001c13a0040230008168003000820c03c00309c89680fa057016045c00016f000348802800300681480060130158000010196001803807601700e01780520020048000018545000003401000a000022c00c003000805c0180210000054000032070000010c01d000800000200102802f8736000005800400201402180180040f301580a000400000101cc000006053800c244066000000c03e03200b007c00008100004a800000401c0010000020000013c0160b5010803c000017028807c014000005803c04e002003800000a0000030009d26022008804800000000000cc00400e00a0c3c012003005003400c0130040000106000001802407600000080040000010ff8000000002011001409800600e82740040750098184252003000003802600d00100cc00000201c806402c01100f80000a20010088bb028e00200980041800ad00b0c6c0220035b7809800a019000003403a00201b003800400300f0000000001002070c00c06101913b019808601f800009a000000803c04e02f000003000002000d82b803600100680001aa0000318004022001018009c0ac001000000400a006000800005e0010010054846000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87f825ca65d00018beea39ac88801a2f21176d45302c70fc28c829a60caa9d87cc8644c0031790cba0a6a001f1be097219510006363a8e4b222000c78655c043440b14bd09a90c6aa1b3475847550c4300c5ec26e5b2a8000c3c75d91434c40187b0fb2ea8a00021fa1f52595430054ec1842322606de1c63dd543500018bcc039aa9a88029760e41195302c70e324a829a60008df835c9654c4018dae4a96ca9800327ddb7550c4300636b90c432a2000a3d8590b645440153b06202c9a98028f61021195430045fc3ac83226058c5c761cd54544b18b8c839aa8a8a3a8f21532191532c52e432a431aa800a6d820436550c0187eea3a2ca98003871954310d100051ec2c63b22a6cbc3c745c965d00010fd0e216ca880021f61f219974000c5ec26eab068200a5c8358865440010fd0e10ecaa1b328fa145219130334ae41aea21aa200e4c6254b63550018d8cbb92c688003471d46350d4048e1e32ee8a9a86cc87e871c965d00010fb0e080caa18022f61c21d913001c6fc3a65b1a8000c6f65dc9634400517b09bb28398246a760c72d91530062f300e6aa2a200d1e501cd54d04bf4bd06396ca98162a7a101018d540054f42465b1aa2ccc3c74d496344001958c9b92c2980822f2197010d4103c3e42aeda0a60208be86dcd415000153b07202c9a98030f19774585303652f41c8432a866da5e830436550d2387ee83aac7a092e9e60072d951064d4ec1c64322600787c8719543441c3878e8a92c7a08021fa1f5259131006563a6e4b1a2000a9d830876454c01cca4210eca98003271d3735953041d1f426a4b24a658c3c641d5434c00147b09190caa18022fe1172595100062fb2ae72a26000d1c641cd545440117b0e086c8a99b31718c7550d400365c322e021a200087e87195614c0cd0fb0fb2ea6988023ee01725954100556c1020322a600ad581080635500f0fd0e194cba001e1fa1e32195100052e41ac5b2a2000e5a50d8f60550014bb0a196c6aa0038754864d4d302e54f41e42322605ce1e53193534c00147d08316ca880028f61441d915300656396c8b0a6000a5f835c565d000717f0ea16c89880a7c2057010d102c43e432e829aa25ca9e83084644c0070f90ea92cba03338e10352580432fe2f39ecb2a2600687c855c960d50018dae4990ca88327271d13258d106fe1e3a6a4b2e800087c875496090c01c3f06b2a83a016e37e0d76553300143ec2ee5b1aa200ad98008463550b753d09386c6aa0b29e20152580530052ec1821b2a8658c1c641d5434c0cb93ec239aa8a080a1f21975d0d510345e422ec2a26200c5c751cd64440b153d09288c6aa1b32718c7454d510062fb10e6aa2a2c9e98404c96010c010fd0e32ac2a197f179c073597400045ec3cc4322605fa5e83dcb654c00147d08310ca880062f21176d4740
  | 1 => 0x100b92ca9896f27a1c64d4d300054fc32e0a188658b1e84940635500147b09b2ca88820e8fa10505925302e6c31ae021a2000a3d848cb6550c0117b0f188c89800a1f2157258f513662fb00eaa1a604e95c855d1314c0b11bf0cb9ca92980e1f21d52595100058fc10eaa18860087e87d95614c00127f0ab8487a08ca1fe1576d45300043f43841b2a868ed1f801d54310c0193eec39aa9a08031bdd472591100043ec3c6432a603287e861d5434c0dd93ec839ac0aa19b17dd76354d514768fb20e6aa6a206a3e8408565d00014f300108ca9820f0f1937550d306661e3a6a4b2a6220ab8805096010c0f87ee9bb2a9a8b43171cf52597404768e2a0e6aa2a200ce472dc563440010fd0ea92c8981922f61b73507402dccfc32e9a9e8600e4c624cb654c00d17908baec098963872146414d3000637b92a4b2e8000a3d85987644c0010fb0f188caa1a3ac72154310d500061fba0eab048600a5e8308565d00010f90ea92c89881a2f21172595300074631265b2260d5e1e50190534c0d947f0aa98c8a98021fe1f62195430051ec24e3b2a6000c5f761cd54d44d987cc63aa86a01624f6187550f4003c3f43e4332e800087f855c963440b147908990caa18021f61e42195430053cc004332e8000a5f85480635500d47d0918acba023a972154218d540051ec24e4b2e80268be878cb644c0b753d08106c6aa01a2f2117654d1000637b2ee4b222006a3c84dc565d00954eb02396ca880028fe1532191530052ec1ca5b2a6000c3f651d15344001938c9b9aa29820e8fa1232d95432de4e3a6e6b2e8000c6c65dc964440db2bf0cb9ca9299baa7a0c21d91530052ec2c8431aa805c9c735915494d97c3ae6a90c89801e1f21572580532de4fb1ae9a9a866cc3c631d543500010fb0f18eca980023de0572595400052ec1842b2e80dfc5c73d4965cc0011f700b92c898a4747d4973d52430043f43c62b2e805ba9e841c7635500d47908b92cba00028f61662d91300045f438c8b0aa600c6c72d95614c0011bf06bb286880028f21952191304751f42e40322a683a3e841c36550d1d878ca3a2a68809a2fe1176d05303668e308eaa18860787e878c4654c0d9a38863aa8698003171d76350d410061eb2ee8a8e80018f4865c4534404d970e1b22869816f171db73551510345f424eca9a200287c855db51cc0d9838c63aa86a034b279d864cc5300049ec10eaa1e800787c87d496090c0187aea3aec8980028fa1632d91300070fb2a8621a208ed1d811d54310cb753d0810ec6aa0028f61020d95433668eb00eaa18868ea5e85908635500f0ff04b90ca980163720d72595100043e43aa4b1a206e99f865cf5490cb953d0db20a69801e1f2157690d100052ec2c63b1aa891c3f74d496550c018d90bb92c688002a76122118d5400637b92a4b1a2007
  | 2 => 0xc21d91300361e3a2caa9e8058a3c845496414d1d93cca39aa9a08062fa1b74545400051fc226432a8600c5f835c965d000153d07216c8a88028f61231997400052ec1ce4b2e80dfc3d74d4b65500010fd0c3aa868817f8710e50590530045ec3cc4322a6d8a9d83988644c001a3a803aa879832b2710f7258f414751f42c62322a600a3d850806454c0b4b906b2aa7a00030fdd152595303fc5e43acaa0e8000c3f749d3654400187ae83a6ca980031b5cb62d95100054e41ac8322a25de1e53d93534c0010fb0e192cba000237e0d72595100070fa9264322600087d8710b654400147f08a96caa01b21fe1d65d52430043f43ea4b0486cce1c43d4963d040b1bd0f210c6aa0021fa1f6558d1001c3fc3aa5b2a8058e1f411cd65d000147b0a20ec8980028fe1562191300051f424c232a606cd1f621d54310c0317908bb2a7a01b28fa0d52191530054fc22a431aa800a5d839c565d00050fb0bbb2a39801a2f21176951300064e3a6e6b2a620087d870846550c650fd0fa92c12996317e1d65d4f430067210ee5b0a6000e2f625486454cb7938c9b9aa8a9802972015218d540052fc1acb29e800587c855db53440010fd0fb2ac8980021fa1c655911064e4e21ae4b1e8200a3d85c846454c0187eebb22c2981621fa1e50590530345f43c6232260038ee87dc9634404d17d0fa12c1218b297219321953000666398e4b222000a9f83548644c0db4bd06386caa189aaea0054582432ff0f21ecba1a6000c6d724806550c018b8e6b92cba00028f61231d95430343e42aedaa22000a7a800846550c01c3ea5bb286218022fe1176547300062fb9aa4b2a8000c6f7254964440011bb0e10ec6aa002a760c21d913048d1f42821b22a6068bc845d8544c00187ecb3a4ca980021fe1d65195433fe1faa2eda8e800087e8710b654c1498b8cbb9aa8a180e3e21d205804302c5f43c84b2662268bc87d91534c0011ef02b92ca980021fa1d525913165f0f39aa43226000a3d84d96544c0071d904bb2a6880022fa1f64581530043fc3aca32a605ec5c731416510c0d17908b92ca988022fe1175d813133d2e41acba8e80008df835c96550c0117d0fb22c2a98021f61e32d95430043ec3865b2a20008df835c961d500147b09b9eca8801b8ddc565507400070ea96643226000c3c75dd1644c00147b0b18ec8980038719464cc5300051ec2043b2a86058dc835c965500018b8e6b8acba02a72721d43580430068fb20e6aa2a2cbc3c745496510c070f90ea92ca9801f1be09729974036d2f41c85b2a8600c3f65dd15350cff17d0e202c9a980317d9473551410052ec2ec7a9a8000e1f65d90534c04d17d0f18ec8980021fe1572591310070fbb0eaa18860087d8710b654c0b14b909a90c6aa29317dcf52595433654f41ca0322a6918bf845d943d44031f
  | 3 => 0xcaa22007a3c86d52544c0d953d06080c8a9992a720d65505400054ec1ca2322a600e1e8494063550018decbb92c2981b347d807550c430051e432a5b226071c3f74d9554500018deea392c68801e1fa1c321951036e1e3a2e9b2a860087e87c836550c018dae4a96caa180237e0d76547400143f43ecaa8a60028bc845da53d04014f50010ecaa18038714c64d453065e1e3a2a4b2e6000d3875dc143500018df04b96ca8823a97a172018d540045f43843b22a600aba800846454cdd53f08aa0c6aa00317dd87550f30007329084232a8683e1c43dd563d040f8df04b90ca98002a72116318d500062fb9ee4b2e800093d821d54350001878cbba2c6880028fa17211913002c6e41aec29a8200a5d83908654c0594bb073b0ca983861f61d52d8d5103c3e43ea4b226200a5c835c565d00b18bce839acba00022fe11725825301c3e43aa4b2a80a4e4f8254b63550010fb0e20eca9823a8fa1421191530147c432e021a2000c79709436550c010fb053b0caa19638710d421954300637b92a4b2c860787e870806550cb14bd08280c6aa0021fa1f65585430054ec204031aa800a5c83594655000b938c6ba0a6a08028f61071597402fd2f41843b2a6000e1f76dd54310c0159b04080c6aa29347d4974d4f430054e41ac8322a0008df835c9644400193ee839ac888003478407550c4300717c12a432260cdc9c435c96414c070ff0ea96ca980062f21172597400068ea90e6aa2820087d8710865440031f50fb82c6880030fdd754580430064fbb2eaa188691c3f641d56150c0147d0918eca981b297a0e10195430052ec18c432a2000c3e76d52544c0b153d09280c6aa23b472007550c432de4e322e9a9a606ca5e838806550d1da3d023aa862196e97a1c73597400046ec384231aa8d7c3e76d48644c149938edb9aa8a0a478be0952d91535252f42821b1aa800c5d87d8e535451d23f043aa8621a9237a1e42d8d540051ec246232a60cfc5c7354965500018bee7a92c8880832e1817010d410070fa90c829a6058c3f601d5435000147b04b2a83a001a2fa1c21191532dc6fc32e9a9e6000e1f65193534c001878ea322c2980029760c62d95100051f42043b2a6000c5d83dcb654c00f0f90abb686880032bd93725853002c6e41ae4b2886ccc3c74d496510c018bb07baac1218029761763d4d410351f424e2b2e8000a9e8550d6010c011bb0f286c6aa2a7a688143580430043ec3c6532e8000a5d83943654c40d57108902c0219c70f9d765d05400043ec384032a8600a5d83087654c0015390a990c89800317d9773551430068fa88e6aa6820787c855c96414c01a3ea439aa9a0a0e1fa1c6550d300052ec1c4032a8600c3c75d91434c0011bf0eb18c6a800317dcd52597401662e3b0caa1a606787c8754963d4401878ea3a2c688176a7a0
  | 4 => 0x14c0010fb0e190ca8801e1f2157258d100046f43841b1aa8008be87191614c00147b09100caa18028f61410d91530062fb2ee6a8a6000c5f7354965504014bf06a96ca980028f21162195105252f42e43b1aa858c5e641d543cc0078d8e5a92c6880028f61031597400075290842322a65bc9e75190534c00156d02106c8a980297a0f74d95100070fc1aa4322a60087f855d953440db0fd0f216caa18162fa1e425905303c3f43c6332e8000a3d848c06550c010fb0e310ca8809aa760c71d91300061fbaea8b0486008df8758c63504031790cba4a6a01638710c7558f413668f430eaa188600c3f651d1534c0658f6cab84a6a801a8fa1221597400045ec3843b22a606c9c645ce5454d9f8b8e6a92ca21b330f1d352595303668e310eaa1886028bc8759141d400117b0f18ec89813b1714e76d45300043fc3ec432a20008ef825d943440018dee4a92ca988021fa1f21d95300064e3a6c6a9aa000a9f865d54310c0153b08108c6aa01e1f21572591103654f41840322a66ec9c73d915454c015390ca188688002c760b7550c43366adb00eaa1a600787e87dd56090c0f0f90abb0a8980029720d72597402c68e328e6aa68200a9c83590644400117d0e086c8a98028f61262195300351f426caaa22000d1f721d54310c0d938c8b9e839800f331c93258d102e70e298c8a9a6000c9f76dc14310c050fb0bb9ac3a800257a1f6550d303654e41aa4322a66c99e87dd54310ccb1790cb9e82a0002976171018d540051ec2664b2e8000a3e84943654c4bb53d0638ec8980022fe1173d85500045fc22ecaa26200c3e84dd56090c0147d0b38ec89817f171ce76195300345e422e4b28866295c855cf41cc11dc3ea9280c6aa16fa610353580430072c304a031aa800a5d83d9653504018beca39aa888002976142118d540054ec2021b1aa82ca5d87d94534c1718bee632ac89801e1fa1e42195300061fba2a4b1a208ea5c85480635500193ee839acaa09628fa1210195430070fb28c921a60058de8708063550d987cc63aa87a019a97a0f52d8d513654f41ca2322a600ace82040635500117b0f280c8a997f8710f6550d306e70eb9eca322606ca5e830806550cbf4bf0ab18c6a8002a761270d8d540043ec3e43b2a860787c855c96090c018dae4316caa18032bdd072591100051f42cc4322608ec5c651cd54440d947d07a90c8a98036650d7010f5048e1fa96e8b1ea200e1c84548635500117f08bb2a68823b1719473551410061fb2ee8b1a205bc9f631d16054d1d93f0cba6a7a18062fa13764c7400054fc2264b1ea800e1c65191434c00153d0b990c89823b476087550c430063ab8ca3b2a866cc9c731d165cc00147b09286caa196f2761c64d4d300058fc16eaa188600ccf73dc964440011df04bb086882468fa1721d91530046ec1ce
  | 5 => 0x9629721a5414d300068fb96eaa188600c6c72d95644400d53d09192c7a0802976164018d5400c5ec24eda9a8006a3e8414565d012387ccbba2a7a00028f61630191536ad1f42cca322600087d8708665d00b9d1f04990c89801aa720e76191300061fbaee8b2a6006a3c8459554cc0010fd0fa92c898016a7a0f6450d300043f43864b2e8006c9c76191434c001878ebb22c29801a2f2117258d100051ec20c5b2a2058b1c8454863550e327d0fbaa86a0163175d463d81544762e328e6aa28000a5d8504363550018d8e432ac888002c76087550c430364e322e62a6604ea5d87d97534c0011bb0f216c6aa0063720d76553300051fc2ac83226058c5f865ce5494c010fd0ea92c1218021fe1d62195100147a40ae4b2a8067a5c8354963d44010fd0ea92c6881bb271cf74597300051ec246532e800387c85dc965440014e902b10ca980b28f2116514f400061e328e8b0a600087d878c665d00658f0e1b2aa698002ad60420d91530062eb9ee5b2a600787e870406550c010fb0f190caa192a9d21921d95100068f100eaa18860787e85dd9414c0d9a38a63a2a6980028fe1570d915367e2e39aa4b2220a4a9d841c763550b1938c839aa8a80028f61062195100145e432e9a9a827fc3f8759541d00011dd0e392c6880030fdd76450d300043fc2ae4b2a2000a3f8558b644c1b9c3b07b28c8981631799073551510055cc0043b22a600c3f7454965cc00147b0828eca980021f61e42195100052ec2e4231aa80087d8708565d00014bb0b196c6a8802ae60021191300045fc22e4b2a600087f855c96550c0147b0928ecaa00028f61632191530043ec384232a6007c6f825c86550c0147d09316ca981634710c7550d412453a4324232a2000c5f651cd644400f0f90a3b286a82478bd4a52d915302e4f43eeca18866cd1c601d54310c0117f0eb10c8a9802b6a0021d8d540052ec1ecb29a2000a3e849c7654c0018dae4310caa18022fe1172597300061eb2ae929e8000a9d840c3635500155904b20c8880031e5c070d95430043f43ecab0286d0c5c73d49655040193ae9b1ea6a080e3721d3258f540064fc3a86b008600e65210876550c974f10c906ca880169720f65d4d304745e432ea21a826ec9e635cf54d00011bf06bb2a89800387d9732191300054ec24a231aa80087e8708565d01978dc84b94cba001b0fdd7765534133c3f438a2b2e6000e2f8254b644c00153b08186c6a080307ddb7550c433754f41841b22a6008df835c9655040d47d09194cba001a8fa10315974024d3c4324032a206da5e830836550c018b8ca39ac8880028fa1232195300145e422e7b0a8000c9f741cd65500b147d09100caa19b347dd07550d302f72d380a031aa8208be86dd1534c0d953d07290c8a98028f21162d95100070ea1aa4b00862cc5c761953
  | 6 => 0x70ec24a031aa8008df8758863550b1c3887200caa1a3ac72154310f512dc6fc1aeca9e800087f855d843440014bb07210ca881628fa1231195430068f280e6aa28200c6f75dc963440016390ab8286218021f61e42195300052ec2865b1aa20087e870436550cb153d09290c6aa01a2f21176547302dd8f424a1b1aa8008fb805c9654c401878ebba2c8988021fa1f6550d102762e29cec2a26000c6d7294b6550c0147d0b316c8981638710e42195432dd4f42021b1aa805c9c635d053d00b953f0f990c89823b47e047550c434768fba0e6aa6a200a3d84084654c0010fb0bbb286880028f61672d91300062e3aee6b222000d1d211d54310c0147d0da90c8980063721973d05300068f380eaa1886008ee871c9644400d878c93acc89800237e0d76551100043f43c65b2a2006c9c645cf414c00147b0b216c8a9a3a97a172118d540056741021b1aa86e99f875d54310c0117b0e100c8a981a2f211725875303c3f43e4232a600087d85dc164cc4018b8ebb9ac89896e9761472d8d540053bc0ac432a6006a3e8494565d00014bb06108caa1b2e1f61e72597400051ec2e40322a606c3f7159541d000153b09280c6aa3330fd0772597400051fc22c5b2a6006a3e849c965d00018b886b90caa18030fdd474595313352e41acaa8e80008bd878cb644c0078d8e4a92c8882468fa1472d9153006cca1ae021a20038ec825d954440070f90ea92caa1b2b271d33258d100343f43ca4b2e804b87f855c36454549c9ea5296c6aa23a8fa16321915302c6f4384231aa8008be87087644c0010fd0fa92ca9823a972162018d542fe2f41eeab048600ad980087635511d47d0a100c8a9802b6a002118d540054ec1881b2262008df8758c635440187eec3aa87a0002a760e40d91310345e420eca9a800087f855d943440014bf06a10caa18b21f21d52580530051f42e43b22600787e8790865440010fb0f18acba00021f61c621953048e1e32ee8a9a6007c3e655d053d00b153908900c6aa13a57e087550d301054e4326432260cec9c73d0964440c933906ba886a08028f21162d95300043e43aa4b222000d9473dc55450401c3906b2ea9a00022f61e31d91530143e43acaa8e803287e878c7654c001a3e423aa86218cb1e9c365951300054fc1286b008666a5d87d8e535440117f08b92c688002a760c20d91530054ec1881b22a600d1e211d54310c010fb0e210ca9800637219744c5300070fb2ec9a9a6000a5d8508063550015ad02106c6aa17a97a0e42195300051ec24c232a6000a3d8510b6454cb1878c83aa869881b0f19175991304770fb26a431aa8028bd849da535040153b07290c8a9802a7e197150c432c70e3a0e6b2e8000a3d8408665d000147908b28ca988021fe1d651953102c3f43ecaa9a20208bc875096010cb1a3eea39aa8a
  | 7 => 0x1d721d54310d1d6390aa1887a817f17d9473591500051ec2843b22a600c3f65dd1614c0014f30010acba00021f60b75591310051f436a92a2600087d82dd563440b14bd09280c6aa0032bdd07258d100054ec1821b22a600c6f72d49634400117b0e288c8980021fe1572591300045ec3c643226000a9e848cb63440051e902b92ca98002a7a0e42d91100054ec1842322a603ce8724816010c01c3906a90c8980028fa1051d953065e1e422e4b2e8020c9c76191314c001a38e23aa862181a2f21172580430055cc0043b226091e37519476454c0147d0ca90c8980030fddb7550f400043fc2ae4b2a6000a9c8550d6010c018df0bb92c6881972718d73d05403658f42ceaa188600c5f739cd65d000f0fd0e210ca980029761642d8d540043f43e42b2e80008dd8708363550b1a3ec63aa87a023b47150735515003c3e438caa1a6000ec52108463550014bf06a92cba1972a7e0932191300068e3a8c8a1a6000a5f855086355001d3700a1ac0218028f61051597304751f42c60322a63287c87d95434c19d93887b92c82981e1f21573d85402553d400e5b2a2000c3c435c86550dc5878e9a92c7a08028f612321953003c5f43c84b26a005c5c735955490c014bb03a90c6aa00a2f21d65505406f62eb9aa5b2a608ed1e801d54310c018bae6b96ca9800327dd97050c4300637b92a4b2e8200a9d869d54310c0147b0910acba00022fe1176d45300351e422cbaa6600287c865d443544014bb0b396c6aa01a2fa1c511913002d2f41ca0b2e6200c5f75dcd644400d17908b92ca880022fe1176551300046fc3ac631aa8058dc835c96190d0747d09282c9299b61fe1d65d4f4300727b12a5b1aa800a9d839436454c0117b0f196c8a981a2f2117258f510062fb9ea4b2a800787c855d943440c52b90aba2639832b2710f7258c540045f438a3b22600091d821d54310d498bec7b90caa18024fe157090d4141c3f438a0b24a6a4a5e8590b635500193ae4320a69816e9761770d8d5402c6e41aeca8e806cd1e611d54310c0193ee4326a6980163720d7614d40006363a8e4b1a2007c3c655d2654c0031b906b92cb981628fa10201954303d1f42884b26a0a4c5c65dcd544c0d9a3eec3aa8621802a72194310d510052ec1c85b2a20c6c3f75dd165500596b5012a0a6981b28f219521915303c3f42ee0b266200a3f844846550cb147d08108caa1803175d763d0d512dd2e432a5b1aa800c9f641cd5454001ec242906ca8801b0f1d16554f430062e300e6aa2a200c3f74d49654c5070ff0abb2a7a0883279d864d4d300070fa90c9a9a60e1c3d7454b63504d94bd06108caa181e1fa1f21195430052ec2c4231aa803cac72d0964440bb938e7b22a898003d848520195100055741021b22a6008bd849d9534400117d0fa12c888002a7a0e42593500
  | 8 => 0x4210ccba009b271db6450d300147a40ae4b2260d3c9f73191614c00f0fd0e108ca980039918921d95103664e31ae62a280008bf845c96550c014bb0a10ec6aa01a8fa1250594432c50f424a031aa80087e87d4963d04dd53d06086c8a98023ee0172595100045fc22eca1a2000c6d72d8865440b1938c8ba0a6980030f1947458d101045f43ea8b008600a3e85188644c11dcb500280c6aa00a2fa1276d05500043ec3c6232a600087e871956050cd94bd07208caa18161f21d65553300051ec2ce3b226000d1f511cd54504011bb0e080c6aa0031b5c921195300345e422eda8e6000e646248465441494bd0b396c6aa0021fe1576d053002c6f4382031aa8a4e5751947635504d17d0c3a2a6980028fa1642d91300061ebaec9322608387f865d253d44bd8b8e039acba00028fa1232d95100043ec2eeca0a600087f875886550c6547908b2ca7a01c70fd5276d454000637b96a4b222000a3e848c865440dba3eedbaa8621a0f0f1d37558f410052f418c5b2a207f93c855d131d000147d0930eca98162a72115218d540051f436a5b226006a3c845c565d01b387cec328c898002ab60810d915300637c12e5b2a8600a3d8510b644c0010fd0f192cba00031bdc952597433652e41a8432a8626a9c864cb644c0db4bd0610ecaa18030fdd375582430043ec38c432a8605c5c7359554cc11da3cea3aa862181a2fa1376545300045fc22e4b226000d1c755c54310d53d30a0a1ac02180333dcc72591100052ec18e5b2a205b8df865cf5490c014bd06310ca881c64f21573d054000477c12eca9a20038dc874c9634412387ec9b90caa181a2f21176153300046f438c6b0aa84187c8754960d50018bd0e39acba00028fa1b521915303e2e32ae7aa28683a3e848c76550c654bb07b8eca98003271d37358d102de4f322e9a9e600387f8754b65440834f50010ccba00029760c21d95430046f43e64b1a2000a3d85084644c10747d0810ecaa1b778760f65d91304752f4284231aa800d1f201d54310cd9938c63a2a6a813b17dcf6554d3003c3e43ea4b1e828ee1f535486454cbf8b8e7b2aa8981b31718c7550d4103c3f43e4032a868ee1c54948635500117b0f188c8a980347d48735514103c3e42aec29a2032a5d83dcb654c0018dae5908ca980038719053545300345f43820322a66ca9e830846454d99c3ce7a90c89800a37a1b73551310061fbaee8b2260018dc865cc544c00d17908b9ec2a800e2fe1d42d915336d1ec20e1b2a866cc3f875925494c770fb0db82a9a89b61fe157650f506670eb9ea432260058dc835c965d000d938c8b98a8980031761f65d4d300051ec2462b2e800387c87549654c4594f500108ca980022f61c21191300074ca1a40b008658c9d87190534c0010ff0eb28caa0973271cc64545303245ec3ec9a1a6200d
  | 9 => 0x7694f410068fbaceaa188600a3d840406550c014bf0b100c6aa23a8fa14101915300636b96c432a8600a3d848c7654c00f0f90abb086880030fd977454d100062eb10e6aa2a26ec9f741cd65d00031bb073b6a2981ba8f61472d91530055bc0ac43226006c3f8759754d000d47d09192cba0353179d86590d3000c6e41aeda8e605fc5f651cd5454153d3100a1ac021963179907550d300051e422ca32a6005a9e8390964cc51da38a63a2a6a80029760f6594d400051f428e5b226000c6d7218b654400153b08106c6aa1b38710e31195430046ec3821b1aa8058de839d954440010fd0fa92c6880cb171db6550d300054e422c631a200787e87108654419747b0b290c898357871406414d300051ec16ca32260008df835d9544c4018bac439aa9a88021f61e32597400147c432e029a2071a3d87d9754500654bb0638eca9816ea7a1250d8d540054ec2264b00865ba9e841cb635509d1bb0fb1ca6a80030fdd352595300043fc2ae7b0a80008df8758c635000f0f90bb92c7a8b2a37a1c3258f410070fc1ea432260d0c5c73d49655012347d0b396c8a996f27d0d76d4f400052f41c85b2a200087f855da434411d8b8c039aa9a8802b360810d8d5403c3e43ea4b226066d1c435d053544014bb04280c6aa20e8fa1020d95430143e42aeca1ea200a3c85588644c19393886b92c62a0021f61f21195430052ec2e4031aa8068bc845c96094c0147b09b2ca898a470f1977454d102c64e3a0e6b2e8000a3d848cb65440070ff0ea96caa19b247a1f7550c4365e1e3a2a4b1a2000a9f835486454c0147d0b308c898003475cb7550c4303c3e42ae4b1e828ea5e85080635500d17d0e100c8a98030f9d764991300043fc2ae4b2220cbe38405496010c0b1b906b92c2298030f5d074d95100070e32a643226000c3d84dd56090c014bd07210ca881630f1d07558f410045ec3841b22a6058dc831d9544c001cca42108ca98002a760e70d91530052fc1ac5b2a20268be871516090c01a3aa239aa9a09b3476187550c430062fb9ea4b2e8058c9c651cd54d040f0f90abb0a88823a27e1973d52431952e43265b2a6000a3d848c865440018df04b92cba02c38e14354580430052f42c63b1a806da5f8555063550010fb0f310caa1b321fa1c52597400051ec2c62322a600e1c65191314c0830f90cb86a8a8a468fa1720d91530051fc22e4b2e8091e3b509436454d2387ea8bb487a880297e0d62195100051ec24e3b2a8600c3f651d163440010fb0f196ca88002ad20562191300054e422c631aa2dec3c7454965d00652bd0c3aa869800347a1c7550c430043fc2ae4b048658d1c431d5435000147b0b216c8981632719073551510043ec3e4032a8658a9e84c406355001c3ea5990c8980022fa1f64585300062eb98e6b2e8000e1c8359541d0001cca
  | 10 => 0xa1886038ee87dc964440011bd0e31ac0aa1b3471907550f300068f388eaa1886018dc835d951cc0018b906b92cba00038bd8952d915365e1e3a2a4b2a628ea5e85884635500f0f90a3b2a298172a7a0e51191300045fc22eda8e606ec9e435db54cc1a9c3c60328c89800637a0f765073068d3dc02c432a2000a9d83d9243540011df04bb2a8880031b10972195430062f41ee5b2a600087e87107654c0010fd0db90ca9801e1f21576151310051ec2464b2e80008dd879886355007998e5992c68800297e0d21195430043fc2ae4b1e8283c3e645d253d44010ff0eb28caa0163871524218d542de2fb9acaa9e8600a3d859cb6454ce317b0fb24a8a801a37a1e3258f410045fc22e4b0ea600a3e858c4644c19f8b8e6a92cba001a1f217765474041e1fb28e8b0aa683c3c74d955350c018becbb9aa8880028f61764d513041e1fba8e8b1ea200a3d82194644c0654bb063a6ca98162a7a102118d5400637b92a4b2a806d87e87d496395199878e9a92cb9800327d9073551513745fc22ecaa66000a3c8558b644c0071790ea12c888003475d47550c4302c6e41aec21a20008de870876355001ab0ebb8286980021fa1f21d954301c3fc3aa5b2a8258a5e84d94534c0db63d0e3aa86218034754973d52430068f880eaa188600c6c75dc9634400147b0b908c89816f2719373551301962ec3eca29a60a4a9d841cb63550014bb07216ca9801e1fa1e42195430073431241b2a200087f855d9544c0050f90eb2aa2a001697a0e50594436f62e39aa4b2e6066a5c8354b635440f0fd0f190caa19b347dd07550f305262e32ee6aa22000a3e8654b644c00147b0828ecaa180347d007550d300051ec2ce3b22a600d1e721d54310c031bb07b96ca980028f61421d91301952ec18e5b2a6000a3f8458b654411dc5f04a90c8a981e1f21572591300046ec3c8431aa800c6d72d8b6550c0517908bb6829800e1f21d52597432ee4f3b0a7a1a805f87f855da435411da3d043aa86218022fe1172595311364e3b6c898a6000c3f75dd163440012bb043aa869823a97a171018d5402d4f426eca1e600787c855c3644c4031bd0db9aa2982462fe197590f413754f41ca1b22a60087e87087654c1abc38ca320a6981baa7a0c72d91531953d406a4b04a600c6f425c86550c0b938c6ba0a6a00163720d725954102d4f41c84b20a600c6c72195614c00f878cb3a4ca980021f60b7558f410063db2ae129a806ca3c83d486454d494bd0b906c6aa0030f59571d53400054fc1a84b26a600a3f8458865440cf4b906b2ea2a000a2f2197414d415272da84a1b1aa800a9d84c4063550b7c3e83b9acba0003271d36354d513668eb10eaa18860087f855d9544400187ee8a92caa181e8fa1442590533651e41aa4322a6718bd87d974150001a38ebb22869820f0f951
  | 11 => 0x550014bd0738acba00028fe1152596430052ec1c8232a8600c5c73dc965d011da3b003aa86218021fa1c6550d105254ec26e1b1aa8038ec825d8434400317d0dba2a6a0002a760e511913000637b92a4b2a865da9f8458c635000147d0a216c89800317dd473595410043fc3acba8a806ec3f745955490d1d47d0b908c8a9a3b0f1d47458f510051f42ce5b226000a9d83c84644c001c3a87a92c02196297a0e73597400045ec26eca8a600087d82dd56090c0147d0b30ec8980ca1fe197094f510051f42465b2a6000c6d721cb6550c050fd0dbaa86a88030f90d721954364d4fc3a6432260008dd87080635500f878caba6a6a1a3b17d8873553513668f310eaa1886008bf875906454c0117b0e080c8a99972710d7614f412dd2ec28e3b1aa800c5c65dcd64440015750010ec8a98062f21176d4f403670e21a6432a8600c5f73d49655044d17f0cb8487a08028f6127159740314afc10eaa1e60008be871916054c770fb0fa96c0aa00e37e1d32d8d540054ec2043b1aa800d1d521cd54d04011bd0fb1ac0aa00a2f613735874000636b92a5b2a800087e870cb65440014ed02100caa1b330f1d372597400051f428423226000a3c85590644c40d17d0f190c89832f8710d5258f4102c6e41ae4b22200687c855db544c0dd17f0cb9ea9a00021f61f21d953001c3e43aa4b2e8258c5e641cd54d440517d0dba2a6a08031b5ca32997406862e39ea4b2886918be878cb6454c010fb0f196ca9800297a0e72597400043f436e432a8658d1c541cd54504590f90cb80a6a88021fa1f65591104768fba0e6aa2a200a3d840436550c650fd0f196ca9817f171cf65545300070ea96eca18860787e85dc164d44b1b2ec239aa8a09c64f215744c5402c68e318eaa1e8000e1c8550d6010c0147b09286caa080f391c921584430043e43ecaa1a20008bf845c963d452347d0b38ec8a98032bdd37258d1002d2e41acba9e80068be84dcd61d404157501aa2c021b2f0f1d15258f513745fc32e9a9e860087e8754964440011bf0eb18c68823ac72154310d510051ec24c5b2a6000c5f435c86550c0147d08396ca880cb1e9817094f510052f436a431aa800a5d838406550c018dee4a92c9a981e1fa177650d102463d380ca21a2000c6d72d8b654c00f0f90fa92c8880030fdd35258d103264e31ee6a0a806ce1c438c86550cb14b908280c6aa16347dcc7550f400043fc2aecaa26200a3d8408565d00010fd0fa92c888162a7a102018d543661e3b0eaa1a80008bf8759064540b10f90ea92c8298822f21973d51400061eb2ee8a9e8058a5e8454863550d91790cb98a8a001a1fa1f655513048d1f42c63b22a60087d8790b654c00f0fd0f194cba00cb171db654c5300054fc224031aa800b1c8550c43440071d904bb28688002b560420d8d543668f300ea
  | 12 => 0x21f61e42d95102c46e432e829a60058dc835d7605040153b09b1e86a80031bdd772591100061fb2ee8a9a605ce1e75190534c00717f0ea16c898172a7a0e521913000636b96c432a60008df865d131cc0014bd06396ca8800387e1543580430068ea00eaa1a6000c5d87940635511d4bd0a080c6aa23b271d8735514148c5f438c8a9a6000a76810836550cdb8b8e6b9ecaa18ee9ea00215974000c6e41aedaa66000e8f624c8644c0bf4bd07216ca980029760e50597430070fc1aa43226000a3d850406454c4d53b07baec89832f8710d5258c540045fc3ac83226258a3c844846550c0bd36e0a1ac0218021fe1f621953000636b926532e805ba9f8354c6454c010fb0e106caa18029760c20195430045ec38a3b2260008bf87594644c00147b09196ca980028f61462191300051ec242032a860787e85dcd61d000d17d0e108c89836a8fa18651913041c3f43c65b2a860787f825c865440d9c38c83aa8798002972156318d4100752908423226000a3d85c876454c018dae4316ca980028f61261d95306f61eba2a5b2a800087d82dd564440db8b8e7b2aa8a181b2719173951300055bc0ac5b226000ccf731c963440010fd0f216ca88002a7e1132d8d410145ec26e5b1a820693d85dc1545051d93f0cb9ea9218029760c21997400051fc12caa0e8000c5f65dcd644400d53d0db228698002ada0420191534770fb20a031aa891a3e850876454cd90f90ea92c62a0022f61e50d915302c5e422e4b0e8600a3e848c4654c0014eb02100caa189b279db64d4d300053a40ac5b2a6058e1c439046550dad87ceca90c89800297e0d72597406862e39ea4b222000c6f7254965cc4b953906a90c8980028fa1021195300052f4184332e80068bc845c9611500187ee9a92cb980031b5c952d95310061fb28e8b0a605cc9f72190534c001c38ca326a69836ea7e0d651913036e1e3b6eaa1a80d4e1f83194644c09d2bd0fbaa86980028f21b52191300064eb90c9a9a60018dc865ce544c00153b01bb2862180317dcd725974065e36a12e532e8000e1d52190534c0014bb06108ca9819f17d8473551513754f41ce1b22a68ec3c651d1534c4018bee6a92c8880029ba0810195432f72cb80a031aa85da9e831cb644c11d4bd0b208c6aa16347d9473553412c51f4246032a8600c6c75dc964440b763908a96c6aa0029720d65195410063ab88e3b2a866cc3f875975490c031bb07baac1988028fa1373d95100046ec3ca031aa8018bc845d951d00014f300108caa1803471d77050c430055a40ac5b2260a4a5e851c763550011bf06baec0a0a3b4719073553510043ec3ce5b2a204ba76811cb654400147b0a216c8a88031bdc952594430070fb28c8a1a600087e86dd543440014bb0a106c6aa01a2fa1e32191530351f4204332e8000a5d85c8763
  | 13 => 0x62fb2ee6aa2600187c855d943d400d17908bb086880021f6167650d100054ec1ca43226000c6d7254b655040d47d09992cba0163171d073597400051ec2cc4322600087d878c76550c0153b08080c6aa00387e115218d540052ec0ca031aa883a3f875925494c018df0bb92c8880022fe1d64191100076290843b1aa800a9d8494863550cb53906b2e82a0172a7a0c52191300361e3b6a92a2606ca3f8450c6550d1d878ca3a2a6981b7871937550f307161eba6a5b1a8200e1f8359754d00018dae4a96ca8800e2f21d42593532c68fb98eaa1a806cc1c641d543cc1494bd0a10ec6aa23b27194735514103c3f4384232a8603c6c7254963440070f90ea92ca21802a760c20191532c62e3b0eaa1a60008be870836454c018b8ebb9ac8980029d60420d954300c5e432e998a800087d82dd5644c0b18b8c839aa9a880267e0d71d504364d4ec3a64322600387c87549655040d974c8b8087a8002aba0810191530053741021b2a8600a3e85107644c197878e8a92ca9801a2f21c6454d3067f0e21aa4b20a658a9e84884635500f0fd0b3b286883830f5d764991500061e3aee8b1a2000c7b655c2544c00d47909b2ea8a00028f61072d95106a70e180ca3226000c6d72188654c0070f90ea92cb980062f21175d81410070e328c921a6006a3e8494165d04b147d09282c8298063e20172595410053cc0043b2a8600a5d839006550c0153b09286c6aa20e8fa1271d954300636396cab1a2000a5d8294063550050fd0b3b6a2a023b93e095218d5400656390c8b0a6005a9e86d8d435000153d0ca1886880028f61632d91530051f428c5b2260d4e1d73194644c0d98b8c83aa87980028f60865d91300046fc1ae4b2a80c0c5f75dcd654c51da39023aa8621882aea0021191302df0e3a6e6b2e8064a9c8359541d018f87eebba2caa080a2f2117258f410145e422eca9e825ee1c43195434c0b10fd0fb2a86980030fd947454d310043fc2aeda1a2058a5f8350c6550c0156b02100c8a98061fa1b7550d502c52e422a431aa800ea5210876454c014ef02b16ca98003171cf715974000636390cab1a2000a3d858c8644c0016390ab8a86218022fe1d64191510068e900eaa188691c3e655d643d04010fb0bb9ac3a00038754932191300045fc3ac43226000c3f7454963d44d94b906908caa1b37271cd425911002c6e41ae4b0ea803c6c72d4964440bf8b8a7baac0218034754473551410052f430a031aa800a3d84087654c00147b0b90ec8980063d21971151102f52f4184232a6006a3f8759754d0001998e7b92c888002ae60021191530062eb98e7b2a2000d1c201d54310c010fd0e32ac8980031b197725853048d1fc3acbaa48600cac741c963440014390aa1ac0218021f61f20d95430051ec20a3b2a80cbc3f415c965d00011ef02b92c898
  | 14 => 0xd83148644c0014bb07ba6ca8823b87d8f52191530054e4328621aa06cd1c431d5434c40147f08b28ca980021f21d5258f4141c3f43ea4b24a60387f8754b654c40d47d0918ccba00063720d75d81310068e3aec6a1a808ec9e651cd545040d47d0838acba001a8f21173597400051ec2e41b22a66ca5e830406550cb1878e839acba00022f61c21191530045ec3cca322600087d87087654c153d3420a1ac0219bb27d9173d514301c6fc3a65b1a825bc9f731d165cc0010fb0f310ca9800393d895218d543745fc22eca9e804e95c855cf414c001cca4210acba0003471d77150c430343f43ecaaa2208ea5e85900635500f0f90fa92c6880021f61c32997401953d40043b2a600087d879cb654c00147b0b308c8981b38710e30195433352e41acaa8a808e8be87d91534c00187ecaba4a6a00063e20172591310052ec08a031aa800e1f654c8644c0018beea39acaa0003171d76350d406fe2eb9ea5b2a6091a3e850836454c01a38a039aa8a08021fe1d621953000c6f436e6aa26000a9d848c363504b1838e839acba00038720f521913001c3e43aa4b2c8600e9461d91314c00317b093b6a2a00028fa1421d91300043fc3aca32a2000c6f7254965cc0d9a3ec83aa87980028f21b52d91300068fb28e6aa2826cd1f861d54310c590fd0dbaa86982b7279db53d0d4048e1e3aee8b1ea200c6f825cb654c00117b0f190c8a98028fa1262195300052ec182032a862c95c87195434c0010fd0fa92ca880163720d76551100051ec2841b22a65bc5d75d8f60550654bb07ba6ca980029e60021d95300061e43acaa0e8000a3d851cb644c0b78bb0bb9acba02468fa1632d91536745f43884b26620787e87104654c007958e4a12c88817a97a0e41195300043ec3e42b2e804a87f855d853440014bb0b196c6aa0028f60b65d91300051ec2ec9aa26200a3e858c7644c00147d0b190c89817e9e60074d95300043fc2ae1b2262028dc835d954cc4d9a3ec23aa86219c70f1d765505400145f43ec8a0a60068bc841d9414c0011bf06b92c688002c7e157050c4303c3e428eca9a2058e1c641d5434c0bf4bd0638eca980029760c20d95430143e42aeda8a6000e1c65cc8644c0010fd0e32ac68820f0f1d273597400064e3b486a0a6058a1c8454863551078b8edbaa869817327a1c6414d3041d1f42021b2a8606a3e8494165d0c0d47908a92ca218021f61c21d954301c3e43aa4b2e6200d1d525d353d0c010fd0ea92c7a08031b217725911000566412c631a206cc3c631d543d00031bb073b6a8980029760e42195433645fc3ac92a4a658a3e840406550c0147b09188caa18021fa1e42d95300345e422e4b04a8a4a5f8759753d0c031790cba262a009aaea0021d91300061fb2ae932a607f93f821d543d00b1a76c03aa86a0003471c07550c4300
  | 15 => 0x24800402e00605a0d60040a60400001b62a801e0140860662181f003600000a0020000c20b202c00a03e02403000004000617e00e00000800401e01216e00002a01200801000201435000e0141d621a00c01600400012209200400001e10e0cc0b6098000c2000200001a2fe01600c62a0000560006f200a02002a13800e01e00001c0700000200d600200a09c01e00000002204a0000000060ba03803c06600005600601a0140a015200a05a01e00600200602c0000180000e401010a01e00003c0ce00a3d858cb644c17f8beebb9aca980029761720d8d540052ec2c8231aa88ed1f821d54310c0153d0ca1886a801a1f61576d47400043ec3821b2a86078be87d91544c0050f90ab9ec2a80028fe1162195300052fc0aa431aa883e1c64dd5434c0010f90ea92c8981261fa1b70551510061fba2a4b2a6200d1f401d543cc0012bb043aa87980030fdd464585300068e390eaa18868ed57611cd5454401c3906a90c8a98163e21970951302c68fba8e6aa68200a3d850846454c011bf06b92cba00031bdc952595100061fc22e4b2e8058a3e848c86550c011bd0e086c6aa20e9760c70d954324c3e432e129aa200b1f855c54310c0d47908a92cba01c64fe087550d405252f42841b1aa826a9d831cb644c0010fd0db90ca880022fe1172595410143e42aed21ea20787e8708665d00d9c38c63aa86a00031b5ca32195100054ec1820322a60087d8790b6550c01a38203aa86218028f21162195300062fb28e6aa28000a3d858c4644c0071e90e90ac2218029760e50d95430068e280e6aa68200a3d840806550dbb87cedb28c89800237a1f6358554006aa39ee2aa2a26da5e83d49639500d17908bb087a88030fdd47458d100051ec28c5b226000c6d72c806550c0153d0daa48698002b5a042018d540052ec1c85b2a860087d878c8654400153d0ca1886a8803a948421d91300051e42ac832260a4a5e851cb63550014b90ab18c6a001e1f215725913167e2e39aa4b2a828ed1c821d54310c0b1b906bb0a7a001e1f2157614f410052ec1ca3b2a6000a5e8394365504014bd01a90c6aa162972125018d5400637b92a4b2a82008bf845c9644400d47d0939acba000387d946414d303751e432a5b22a600c5f735496550c01ca8c3b2a62981b297a0e40195430043ec3e4232a60008bf865d131d000f0ff04b90caa18029b60810195430052fc1aca29e8058c5c641d5434c001a38eab828621802a760e50191530052ec282031aa86cd1c861d54310c010fb0f310ca881634715073551400145e422eda0e600287d859da43544010fb0e208ca9819a1f61f52d8d510068e108eaa18865893f861d543d000117b09b9ac3a80023de057258d104770faa2a431aa8068bc845c965cc001a38ca39aa8a08031bdc9525953003c3f43c6432a6000a9
  | 16 => 0x6e600e00000404c00801002e0360441c200000a41a0000120b004e0460000d202e0040002c200206602e0000021e000002803401400c00206603e0240000008c200004600000a04e0000183b002005204e01400006801200000201406a0020e005200000006200804001602a06216805805803e00001a01406400404a23803204800001612035a00402e07e0060060002bc00002053400200805402a0b601800000209200c5fc01a05e02000000200002a00003a0f600884200e00611804c01200449e20801e0020a2000492b4c01e66000600600010808601097eebe01a01a0a6bbe02801602a00600600c01003c01005e0c400601c01000c0200000a000400001e05c1a20080060180040000360004c60700040462d601400007801000800000822c19602803018a01c07400801a0001ba12e02408400201a01e00c00600000000800e07007400218c00a00400e00025419e00a00009000201c00007c00000a43c00000010c01a01281c00c04c0200060180001da00002202a05400601402600a0020260600000780000080001024420d20380085d20660020080aa00201e05a07e08601611e0007120080040121a200a11a00600000000405208000400a03a13402601802a01601200401206000210402c15c0c600000401204800c00005e02202003803c00003a66e0000300000ce00c00200c00039228803600200608201000201400600802205211c23a0160ca01014400800024008c01608001405401801a01200407a1da01c04a05c4cc0000800ae00000215820e02824800e12e04800c2f000003203606400001601c0000040002f400200400a004000010a820a800001e00000600c02a00401800c0020160150440e007810002401207401200800001e0a004e00002e03e05000a00805a0700040160463a601a03200000002e1a80000a22560060080000100c602a02a05404226a03600400000603602a00000000c0020a800a0960000260020000080800c42e205a02017600005a19009200400251a00400000600000400200201a00a0060ca01000007a03401400205800c0002b80129ec00604a87000200e01403201801e01a004c1800004c0060060240760125e408e03045400600600200010000001600000865c0b200e00601400201605e0102b413e0140040000ba01002205005001024405c00600c0001ea06a00200e1760f00100180700001d400000a0c404800074600000a94003a04e00201611009c00e1c402e21e0020000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1aa1216002119153006862008550d6010d1d11e980847550c4300643608721d54310c956609648520d95103648724d848406550c0181f76e157050c432c50725c65191434c00103f985d074d951000447660211d54310c01c0d72d486414d300060761b759d54310c018a587484211913000546a40211d54310cd921c9361021195430064360b72dd54310c01a189021543580430060710d878c86550cd941e968407550c4300507658101d54310cd921e93e11211954347607e19525cf5490c0141d969c07550c4347447a60201d54310c01519900847550c43474872606550c434400141d9720f52191300064360b201d54310c01a612160021997402c507a5a501cd54d04b121e98e115218d54006b048580084635511d09e97e0d425935300507658201d54310cb121c9460e20195433648724d848806550cb181c841cf71597400070310f425c86550c01a1a2021543580430069848580084654c001a612160021d954300447662721d54310cff03c976133259740006862178050d6010cb141e94980735535136607a1875d8d43500d941e968807550c4300417e61731cd65d00b181c841cd725974024e9821921480654400182d845ca32997400060710c8754963d040181c8720d65507402c507259521cd54d040111d98c807550c432c507a5f65191434c0b121e94a035218d540060721c8550d6010c01a1b90215435804300507259521cd54504d921c93610101954300507e5972dd54310cdb81e87dd87550c4300543a48101d54310c0111d981c87550c4300507a4f749d3654400181c646087550d3000447660101d54310cb141c94588735515100507a5a501cd5450401c0c43109721954300516241621cd545440141f964847550c432c507251731cd65d0001aa1216002119130006861408550d6010c01ac12160021d8d5400741484211d54310c0111d980807550c432c607e1c8359754d011d41e9390d72195432c487a538588063550b141c94588735535100487261435496010cb121f986125018d5436507a58201d54310c01c186550d7010d1000487255844c96010c0181c646087550f302c487251838406550cd921c93610201954337427a63765d54310d1d11e98c847550c4300607210835c965d000121e98d954310d1047447a63201d54310c016189550d20580432c48725185c846355001aa12160021d915300447663211d54310cb121c9460c2019543004876488550d6010c015189550d7010d1036507a58211d54310c0141d968807550c43006071d0835c965d00015189550d7010f502c48725185c806355001516910807550c4347447a60101d54310c01515910807550c430042765e8650c43540b181c841cd7159740006984858008565d00d9a1b70215435804347643e49821d54310d1d11f926087550c43
  | 1 => 0x103c002c88007408001814bc381800481800003c18040000001888a400682400089434a41008040408540480383000000008040cd848044800289000001c00343c3c34000400002dc41c04000c18140c3458140004d80190d824807550c430048726143d496010c015159114073551410053864021dcb614c00141d968407550c4336607a0c75d91434c0b121c9460c10195430064360b721d54310c0141d960847550c432c487a53834846550cd941e960407550c43476071d5869d54310cb121c946085018d542c507a53651cd544400111f985d47550c432c607a1875d91434c001a612160021d953000543648101d54310c01a612160021195430061360d7218865440b141e9498073551512c487251830846550c0181c636087550d40006a848580087644c0d941c96d007550d3000526259435c043440d941c964847550c432c447a57835c75410c01a1a1021543580430060710d879086550c0121e962154310d10007035cb52193534c00141e97d4b7650c4347487a568650c4344097a608648520d951036507259401d5434c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1100000001a02cb242108eaa188600d40485900847550c430048315232a86b808688002a09a22408550d6010c01304d112aa1a40b008600a84684902154358043
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x94b
  | 5 => 0x4
  | 6 => 0x5
  | 7 => 0x6
  | 8 => 0x9ca
  | 9 => 0x9cb
  | 10 => 0x168a
  | 11 => 0x168b
  | 12 => 0xa0a
  | 13 => 0xa0b
  | 14 => 0x180a
  | 15 => 0x180b
  | 16 => 0xa4a
  | 17 => 0xa4b
  | 18 => 0x198a
  | 19 => 0x198b
  | 20 => 0xb49
  | 21 => 0xb4b
  | 22 => 0x16c9
  | 23 => 0x16cb
  | 24 => 0xb89
  | 25 => 0xb8b
  | 26 => 0x1849
  | 27 => 0x184b
  | 28 => 0xbc9
  | 29 => 0xbcb
  | 30 => 0x19c9
  | 31 => 0x19cb
  | 32 => 0x589
  | 33 => 0x58a
  | 34 => 0x58b
  | 35 => 0xe89
  | 36 => 0xe8a
  | 37 => 0xe8b
  | 38 => 0x1789
  | 39 => 0x178a
  | 40 => 0x178b
  | 41 => 0x18c9
  | 42 => 0x18ca
  | 43 => 0x18cb
  | 44 => 0x5c9
  | 45 => 0x5ca
  | 46 => 0x5cb
  | 47 => 0xec9
  | 48 => 0xeca
  | 49 => 0xecb
  | 50 => 0x17c9
  | 51 => 0x17ca
  | 52 => 0x17cb
  | 53 => 0x1a49
  | 54 => 0x1a4a
  | 55 => 0x1a4b
  | 56 => 0x749
  | 57 => 0x74a
  | 58 => 0x74b
  | 59 => 0x1049
  | 60 => 0x104a
  | 61 => 0x104b
  | 62 => 0x1949
  | 63 => 0x194a
  | 64 => 0x194b
  | 65 => 0x1a89
  | 66 => 0x1a8a
  | 67 => 0x1a8b
  | 68 => 0x1449
  | 69 => 0x12ca
  | 70 => 0x1489
  | 71 => 0x130a
  | 72 => 0x2c9
  | 73 => 0x14a
  | 74 => 0x14c9
  | 75 => 0x134a
  | 76 => 0xb49d3
  | 77 => 0x9cb53
  | 78 => 0x9ce
  | 79 => 0x16c9d3
  | 80 => 0x9d6d3
  | 81 => 0x249
  | 82 => 0xe89d3
  | 83 => 0x9ce93
  | 84 => 0x1789d3
  | 85 => 0x9d793
  | 86 => 0x5c9d3
  | 87 => 0x9c5d3
  | 88 => 0x5cd
  | 89 => 0x1a49d3
  | 90 => 0x9da53
  | 91 => 0x1a4d
  | 92 => 0x10c
  | 93 => 0x130c
  | 94 => 0x14c
  | 95 => 0x134c
  | 96 => 0xb5693
  | 97 => 0x168b53
  | 98 => 0x168e
  | 99 => 0xca
  | 100 => 0xb8c
  | 101 => 0x184c
  | 102 => 0xbcc
  | 103 => 0x19cc
  | 104 => 0xe9693
  | 105 => 0x168e93
  | 106 => 0x1a5693
  | 107 => 0x169a53
  | 108 => 0x74c
  | 109 => 0x194c
  | 110 => 0x1a8c
  | 111 => 0xb8a13
  | 112 => 0xa0b93
  | 113 => 0xa0e
  | 114 => 0x184a13
  | 115 => 0xa1853
  | 116 => 0x289
  | 117 => 0xe8a13
  | 118 => 0xa0e93
  | 119 => 0x18ca13
  | 120 => 0xa18d3
  | 121 => 0x74a13
  | 122 => 0xa0753
  | 123 => 0x1a8a13
  | 124 => 0xa1a93
  | 125 => 0xb9813
  | 126 => 0x180b93
  | 127 => 0x180e
  | 128 => 0x10a
  | 129 => 0xe9813
  | 130 => 0x180e93
  | 131 => 0x17cd
  | 132 => 0x1a9813
  | 133 => 0x181a93
  | 134 => 0xbca53
  | 135 => 0xa4bd3
  | 136 => 0x19ca53
  | 137 => 0xa59d3
  | 138 => 0xbd993
  | 139 => 0x198bd3
  | 140 => 0x58b93
  | 141 => 0xb8593
  | 142 => 0x58e
  | 143 => 0x178b93
  | 144 => 0xb9793
  | 145 => 0x178e
  | 146 => 0x104b91
  | 147 => 0x104b93
  | 148 => 0xb9053
  | 149 => 0x194b93
  | 150 => 0xb9953
  | 151 => 0x179853
  | 152 => 0x185793
  | 153 => 0x105851
  | 154 => 0x105853
  | 155 => 0x185053
  | 156 => 0x5cbd3
  | 157 => 0xbc5d3
  | 158 => 0x17cbd3
  | 159 => 0xbd7d3
  | 160 => 0x104bd3
  | 161 => 0xbd053
  | 162 => 0x1a8bd3
  | 163 => 0xbda93
  | 164 => 0x18ce
  | 165 => 0x17d9d3
  | 166 => 0x19d7d3
  | 167 => 0x1059d3
  | 168 => 0x19d053
  | 169 => 0xe8591
  | 170 => 0xe8592
  | 171 => 0xe8593
  | 172 => 0x58e93
  | 173 => 0x1a4591
  | 174 => 0x1a4593
  | 175 => 0x59a53
  | 176 => 0x1a8591
  | 177 => 0x1a8593
  | 178 => 0x59a93
  | 179 => 0x75793
  | 180 => 0x178753
  | 181 => 0x1a9791
  | 182 => 0x1a9793
  | 183 => 0x179a93
  | 184 => 0x5d8d1
  | 185 => 0x5d8d3
  | 186 => 0x18c5d3
  | 187 => 0x1a58d3
  | 188 => 0x18da53
  | 189 => 0x1945d3
  | 190 => 0x5d953
  | 191 => 0x1a57d1
  | 192 => 0x1a57d2
  | 193 => 0x1a57d3
  | 194 => 0x757d3
  | 195 => 0x17c753
  | 196 => 0x1957d3
  | 197 => 0x17d953
  | 198 => 0x1a9951
  | 199 => 0x1a9952
  | 200 => 0x1a9953
  | 201 => 0xccd
  | 202 => 0x170d
  | 203 => 0xd4d
  | 204 => 0x1a0d
  | 205 => 0xd0c
  | 206 => 0x188c
  | 207 => 0xd4c
  | 208 => 0x1a0c
  | 209 => 0x15512
  | 210 => 0x58251
  | 211 => 0x59451
  | 212 => 0x5c591
  | 213 => 0x585d1
  | 214 => 0xd5791
  | 215 => 0x1a1791
  | 216 => 0x58cd1
  | 217 => 0x5d791
  | 218 => 0x597d1
  | 219 => 0x59a51
  | 220 => 0x17c591
  | 221 => 0x17d791
  | 222 => 0xd49
  | 223 => 0x1a09
  | 224 => 0x1a9051
  | 225 => 0xd4a
  | 226 => 0x1a0a
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2184
  | 6 => 4993
  | 5 => 2195
  | 4 => 153
  | 3 => 6
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
  | 8 => 2*((h/48+packedAt gbK8 (1612+(h % 48)*6) 6) % 62)
  | 7 => 2*((h/728+packedAt gbK7 (80808+(h % 728)*12) 12) % 2184)
  | 6 => 2*((h/1678+packedAt gbK6 (239664+(h % 1678)*13) 13) % 4993)
  | 5 => 2*((h/738+packedAt gbK5 (129505+(h % 738)*12) 12) % 2195)
  | 4 => 2*((h/86+packedAt gbK4 (10710+(h % 86)*8) 8) % 153)
  | 3 => 2*((h/9+packedAt gbK3 (486+(h % 9)*3) 3) % 6)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff07c07c0e0fff87ff80fffc19f473e20f3cf
  | 1 => 0xc1ff8007ffff07ff83fff01fc668b8cc3f3cf3
  | 2 => 0xfe1ffff800fff83ffc3fffe03870c0f3c3cf3c
  | 3 => 0x1fffffff00003fffc000003f80ff03fc0fc0
  | 4 => 0x1fffffffffffc0000000003fff0003fff000
  | 5 => 0xffe0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x230144148204a482648054a80830316205145
  | 1 => 0x41428002914904908092a015022818480d2492
  | 2 => 0xb40529880092902548254a801850c0a0c28a28
  | 3 => 0x1019ced4ea00423e730060c1ad80ed03740fc0
  | 4 => 0x211e73673cfce7002201830637fd0003bbf000
  | 5 => 0x398003803018840440060c183f7ef6fc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38969
namespace PEqualNP.Outside.L_meta_38969
open PEqualNP.Outside.L_meta_38969.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := bs0_5_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 92 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := bs1_5_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat bs2_4_0 (concat bs2_4_96 bs2_4_192)) (concat bs2_4_288 (concat bs2_4_384 bs2_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat bs2_5_0 (concat bs2_5_96 bs2_5_192)) (concat (concat bs2_5_288 bs2_5_384) (concat bs2_5_480 bs2_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := bs2_6_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 13 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 17 := bs3_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 1 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 11 := bs4_3_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 1 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 11 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 9 := bs5_4_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 57 := block_range (n:=57) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 153 := (concat bgb_4_0 bgb_4_96)
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
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 83 := block_range (n:=83) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2195 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1152 bgb_5_1248)) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536))) (concat (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824)) (concat bgb_5_1920 (concat bgb_5_2016 bgb_5_2112)))))
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
theorem bgb_6_4992 : Interval gbAtlas 6 4992 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4993 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440)) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728))) (concat (concat bgb_6_1824 (concat bgb_6_1920 bgb_6_2016)) (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 bgb_6_2400))))) (concat (concat (concat (concat bgb_6_2496 (concat bgb_6_2592 bgb_6_2688)) (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976))) (concat (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264)) (concat (concat bgb_6_3360 bgb_6_3456) (concat bgb_6_3552 bgb_6_3648)))) (concat (concat (concat bgb_6_3744 (concat bgb_6_3840 bgb_6_3936)) (concat (concat bgb_6_4032 bgb_6_4128) (concat bgb_6_4224 bgb_6_4320))) (concat (concat bgb_6_4416 (concat bgb_6_4512 bgb_6_4608)) (concat (concat bgb_6_4704 bgb_6_4800) (concat bgb_6_4896 bgb_6_4992))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 72 := block_range (n:=72) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2184 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248)) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536))) (concat (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)) (concat bgb_7_1920 (concat bgb_7_2016 bgb_7_2112)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8feeaeee8fce8e8e8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4243122408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38969.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.or,[3,6]⟩,⟨.and,[5,7]⟩,⟨.or,[2,8]⟩,⟨.or,[0,1]⟩,⟨.and,[3,4]⟩,⟨.and,[9,10]⟩,⟨.or,[1,2]⟩,⟨.or,[0,11]⟩,⟨.and,[13,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4243122408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4243122408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38969

open PEqualNP.Outside.L_meta_38969 in
theorem PEqualNP.Outside.L_meta_38969 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4243122408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4243122408) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
