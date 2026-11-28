import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36789.Model
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


end PEqualNP.Outside.L_meta_36789.Model

namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
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

def SBf (j : Nat) : Nat := [4, 4, 8, 6, 8, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36789

namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
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
end PEqualNP.Outside.L_meta_36789
namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
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
  | 2 => 0xfc03f80fffc03fc07c0fc1fc0fff03f014c7cc
  | 3 => 0x3fff01fffc0007ff001fff03ffc0018f8f0
  | 4 => 0xfffc00001ffffffffffffe00003fffffff00ff
  | 5 => 0xffffffffe00000007fffffffffc000001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x14180820404484820451422c51431454c15b55
  | 2 => 0x5aa955698ca3a916be0ad1554dad536154c5cc
  | 3 => 0x535264cad52923a75eb8219b6536d94298e8f0
  | 4 => 0x6263468d1a3232346b2cb5020838e38b1e00aa
  | 5 => 0x8383870e1c3c3c3873cf39e38e20820c1fb600
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaaa0000aaaaaaa0aaaa0000aaaaaaa0aaaa0000aaaaaaa0aaaa0000aaaaaaa0aaaa0000aaaaaaa0aaaa0000aaaaaaa0aaaa0000aaaaaaa0aaaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36789
namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x3a40440725308cb88364c49a323d3803c5108008706860aa1100160000c000051f24a40002a74b264000881061831d500400810f05108cff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xe817d53d03baa7a05754f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53102faa6206fd0c40dea18817e52102faa4206f90840de210817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87986f50f30bf296617d52cc2fca3985f54730bfaa4617e548c2faa9185f15230bea9c61bf438c3bc87186f50e30eea1c619d438c2fca5185f54a30ef19461dc328c2fca3185f54630ef18c61dc318c2fca11877cc230fd984617f544c2fca8985f55130be2a261bf434c37a86985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c37e86187790c30dea1861dd430c33a86185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc65907b4cb20bf28e417d51c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20dfa1a41bd43483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20dfa1841bd43082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43ec63887d4c710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10dfa1a21bd43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec62887d4c510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c530437e86086f50c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x75150af8a2a17d14542ba28a857f5050af8a0a15f95042bf29885de5310abca6215f54c42eea98855d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65de434cb7a86997750d32cea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea96837e50d06faa1a0df55241bf29c837d539077e8720ef50e41bf294837d529077c8520ef10a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41dea1a837f52507dea4a0dbd4941be29283ec52506d8a4a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31ef21e63bd43cc7ba8798e750f31bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c77a8718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c77e8698f790d31dea1a63dd434c73a8698dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf290637d520c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c43bf438877a8710df54a21f7a1443ec42887dc6510fb4ca21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43bf434877a8690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610efd0c21dea18437e52087de8410fb10821f719043ed32086fca210fdd0421fa20843f631087ea6210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a07794f40af29
  | 2 => 0xb21d50004802c86d1b614c0028539e8dc0024432e354b4aa756a000e60001d835d47a5c1125014929b3769d0a8a1f44a8d8e9a7a42884c2891a1d22803410505c3fc7c045048a2c1a9d70280806a11c3a2610ff0df0a833452044064ae8a481b03270522929276198d6a6305021c25124194ac80000000000079000000140001e30000010085e0001e41d8220002c0000001c45dd5700057041872a762701840000047e7a02f8843ba83d1588334869d240f44ca330000002b8000a70000c69191a17d2b46347d0772825584c8002789bc5d825000574a98002660006829c31c0000027f000000ec90800051c0808b0007d0002930005e00009b0006b1060001265bcc28784b27fcf9ab1000860dc2a11f842c000000000010ca830000000005725000061a6d0ea001449af0008900000006c0006794f0004113e0f700045c9785a2b2001430002d40a52012537a00053800000000000ce0100008e8000002dca90002c68ec0009c436878212212e63f8000005524448614c1782786c9d238a5acd40093cc43c4b25a0f8820a11b149c8cc5a1de33c4c92b20435c990c00004241010b8000100180003800068241a80000004008140980800002000080380e010020181404000010000000c048000181807008168420001a0500a0305a0680c00802090080000810000008300500e0000604002040000100200808018240a0020101e00800000080000802810018060001a000180100c0b81400006018160000c0680408000000060000600004090000200c0480000000018000080000006078160081c108020381400000078000301e00012000000180e0780000012030120080803800018521b8020f00001804018000b0100801a0200201006010020b0080e80210000010000000600812038000000e0400600804018020700a000100103c0100001806000000000000800048160000c05002008040180a008001780a0580c0002000002010017e52d0efaa5a1df94743bea8e877e50d0efaa1a1efd4b43df29687bd52d0f78a5a1efd4743df28e87bd51d0f78a3a1efd4343df28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542fba8a857
  | 3 => 0x2ca000002a4534698df2940000009ba580fe43800123434000000002dc1c81182a3c4758cf8eb3224b4bd85c2be0380000026a5fd1623c2c2011558b2000000950004c216c5f2380e6408001c2000a9451000066000f7000030001569503720014f13a00094055869002000000000006080000c000000faaaa22495d540ed55846c9f24a06060cbb2a222a9f4a18004e02d4c80814d401cca1ea000000b68712fc2b0001df04e00061000000000000001882a45f80000000000121142accf09010265e540000000514f89985220000000025c35821a354a4a600023011c8a8000f3400400f586b41c56d3ba4d3f8001481cb0000006389f0001911100009aabc73a6702e5f00918a3ca64ce805d54c88c0b0e3120ac14508007c0f4a300010c000930001de374c400008e0013315e000360130005469f8000003de700528000926d920a9f09634c8a0940d46701081c4042c4f02275403d84d06c0b032d1f04c2cc4ac1618b1bc274869194ea138cd22d02a440fda6b26066cc30a638c000000e4000684378f01100012880002221521a8122c7708980b2142bd17a1c0aaa1cfb84601a81451a034227a4b12684f279125a710cea309b070414a58000c12e4909192202e20000014415a68c8fa280003455c80000076cb38001743f4da2b70009a49117a31e460fc14a38e0b4d987a12e000e19a91700280007e1147208182f5044e4dd08f4e61b8d5134000000c0a4f11801400127130750328001f600000278000000750000565d49893f004a7400000212980001602968180000623c00131199000001130912aa0fc0022e0000000000043a00000000000380b800039a69514800000000001f60007100026c41a000ab8000006fc599ca0fa7f4001bc000000ce80027a0000000001e9794b95848e8c45728809e7c9261b53243694a9c942a7e91e96842c6ad1d052000a34732723b0384f61871dca647883700094cf383c1d07b4ba1a00e80012e8aa0000007c8b951c6242b0620ec9b85b0c608297c241f90000001c00036e000002554160005410731800c0016c3b4688000000f6659080c54925347a839000ad0410d21926545ea7b000370a408d412ad86003147296ce70002a8000d903403e0004a81a0c00740f0003e0a1049000190000d80000000010383a0004b12a0000000
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe548823e6494e208f592538823e6414e208f59053882766114e209d584538831f5350e20c714d438823d63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e65151208f58c544831f54d4d20c7153534831f64d4d20c7193534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d208f990534823d6414d2097994534831f5414d20c7150534831e6414d20c7590534834d6214d208f997434823c65d0d20c7d4f434831c53d0d208f995434823c6550d20c7d4d434831c5350d20d314e324826c654c920e350d32482e8604c920cdd53514833454d4520d5d4f514835453d4520cdd0f514833543d4520cdd5051483345414520d5d4c51483545314520cdd0c51483354314520d98c851483653214520d9146204825e63150209758c540827661150209d584540823e6494c208f592530823e6414c208f590530826e6214c209d98453082756114c20c794d430831d5350c208fd91510823c6454420d954421082e960084209bd9520082e461480209ed95200825e63153109758c54c423e6494f108f59253c426e6294f109b58a53c423e6414f108f59053c431e5350f10c754d43c423e64d4b108f59352c425e63d4b109758f52c4395434c7109b98b548426d62d52109798e548425d63952108f992538423d6494e108f990538423d6414e109b988538426d6214e10c7d4d438431c5350e108f993528423d64d4a10d9d48218423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c544431f54d4d10c7153534431f64d4d10c7193534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d1097994534431f5414d10c7150534431e6414d10c759053443556114d108f997434423c65d0d10c7d4f434431c53d0d108f995434423c6550d10c7d4d434431c5350d10cbd53524432c54d4910d3d4f524434c53d4910cbd0f524432d43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524432f4314910cb50c5244354538c510d914a3144274654c510e550d3144364524c510bc181314436452841109798c540425d63150109b988540426d62150108f992530423d6494c108f990530423d6414c109b988530426d6214c109d984530431e5350c10c754d430423f64548108f191520423e64148108f590520425e63148109758c52042756508410d954821042f160084109e59610042776544010b9189100427b6544010
  | 1 => 0x863d6414f21c794d43c871d5350f21b558c41c8795434c7219798c548865d63152218f992538863d6494e218f990538863d6414e21c794d438871d5350e21b358c428878d434ca218f58f544863e64951219bd89544867761551219798c544865d63151218f994544869d6315121c798c544863d6315121c758c544861d63151218f992534863d6494d219b58a53486756194d218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f997434863c65d0d218f995434863c6550d21c794d434871d5350d21cd153214872c54885219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219e98053086796014c21c794d430871d5350c219b59442086cd6310821b9584420866d658c821b9586320878d434c8219d59441086d56310421b958841087a442104219d59631086e5628c421e550d31086e562884219bd9521086ac64484219dd9521086b46448421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121086e76348421b958d21087a74348421e950d21086e460484218fd91500863c645402197d8d500865c6354021c799153d031d53d0f40c794d43d031d5350e40a758c429029d6310640a758f409031f5350d40c714d43502b86050d40c754f43102b960d0c409dd8552102746154840a758c421032d52108409bd89511026c6254440a758c41103355110440a758f401023f65500409ed95401031f6550e30c7195438c39b6050e30e6181438c23f6454a308f191528c31d4354a309dd85528c2746154a30a7590328c23f64546308f191518c31d43546309bd89518c26c6254630a7590318c29d64cc2309758e544c26f62551309b189544c27761551309d185544c26e62d50309b58b540c27661d50309d587540c23d6595030c798e540c23f63550308f58d540c23e64150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c25d6590c30a7592430c2d96090c308fd95430c31e5450c30a7d95430c31f6550c30cb952520c32d5494830e350e520c32f4394830cb50e520c31d4354830cb951520c32d5454830e350d520c32f4354830d390d520c32d4354830d350d520c30d4354830d354a320c29d640c830cd952510c3355494430e550e510c3665294430d954a510c3374394430cd50e510c31d4354430cd951510c3355454430e550d510c3665254430d9549510c3374354430d590d510c3354354430d550d510c3154354430d5546310c29d640c430c750e500c29d64cc030e650e300c25f654c0309ed95300c39b434c0309798c54c825d63153208f99253c823d6494f209d98653c82756194f208f99053c823d6414f20c794d43c831d5350f20e350d32c827661d52209d587548825e63952209758
  | 2 => 0x801018014024000010020000100000200c0000000e0000380a02802402001004000018010120040180200a0040080200a0040000000200c00004002000000000000080000300000000000000000000030040000000300000001000000020008019dd8552d0e746154b439bd8951d0e6c6254743add8552d0eb46154b43cb54852d0eaf6254743ab18951d0f355114743ce54050d0e9d62d4d43a75875350e9e60d4d43add855250eb46154943aed815250eb86054943cb5485250eaf6254543ab1895150ebb6054543ae1815150f355114543abd895050eac6254143add855050eb46154143ce5405050e3f6550c4397d954310f1e5450c43c754f43d0b1e5350e42c754d4390a5f63542429718d5090b1f5350d42ab1894350b3743d4542cd50f5150b374314542cd50c5150b674214542cd9085150b1e6454c42c754f4310aad62d0c42c794d4310b1d53d08428fd954210b1d5350842ad1854210a6f6550842b91854210a7661d53329d58754ccb1e63953329d98454cca756115332c795143cca9f6550f32c7d9543ccb365494732cd55251ccb954394732cdd0e51ccb354394732c750d51ccb365454732cd55151ccb954354732cdd0d51ccb564354732cd50d51ccb554354732c550d51ccb1d4394332b9987328ca3f64546328f191518ca3f64542328f191508ca7761551329d185544ca7b60551329e181544ca9d6490d3297195434cb1f6550d32c7195434cb8f6250d32e3189434cb8d43cc932b9987324cb1d43d4532c750c504ca3d65950328f990540ca5e63150328f992530ca3d6494c328f597430ca3f6550c32c794d430cb1d54cc83297d95320cb1d544c8329bd95320cb1d53d0f41c794d439071d5350e41a758c429065f63542419718d509071f5350d41ad185435072f43d4941cb50f525072f4314941cb50c525076452d0541cb14a415071e6454c41c754f43106b561d0c41c794d431071d5390841a758c421071d5310841c754f411063f6550441c754d41106ac62504419dd9541106e462504419b98b54cc66d62d5331c798e54cc66e62153319b58854cc71e5450f31a7d9543cc71f6550f31cb95252cc72d5494b31e350e52cc72f4394b31cb50e52cc71d4354b31cb95152cc72d5454b31e350d52cc72f4354b31d390d52cc72d4354b31d350d52cc70d4354b31c750e50cc63f6454a318f191528c6e662cc6318fd91508c63c64542319bd89544c66c62551319ed81544c6786055131a7592434c65c6550d31c7d95434c71c6550d31e5d85434c7946150d31c750f524c79543cc531b998b314c71d43141318f596540c63e64150319798c540c63e6494c318f592530c63d65d0c318fd95430c71e5350c31c7553310c65f654c431c7551310c677654c4319798c54c865d63153218f99253c863d6494f218f99053c
  | 3 => 0xf2800000000e39390000000000005495c00012000594738243024840b00048a000d00004a62440004300000000000000000ef8000000003511700026831a0f2d082000000000000038000000011780000028c00000000001268f90000000a90320a00000101000000d2800000000000000000010287a1c859c000010ea810000000000000000043e0000008732a001152173fa38400000000208000004440006c00000000089000000000000004840010f000000000000c52de880fa86d3a20011f0000003340019b000000f50003840000000010a1bd0821b1482d8799824d83e0d3042000000b18000000010893500000043025000000000272bc61400000000000000ad17a760000003980a0000000765f4421d41685a8db0000000008f00022c000000000000007b9e7000000da800000000bc0004c40e8000000100000022700000000000000000000000001c8000000000e05a800000000000001008e0e5000000000000000000000025c000838ce800000000000000003400000046a00023035000938f400026e00003000000000cb9de0000000000000000000052000000000001a8000788003500011e8001de05000152000560000040000000000000096000000000000000004ca184728001b2001250d23e65b4001f60000006a88f4a0000c582f3dc31c002640000006f8a7152000000002c2000010000000002ea3741a5dc3a000216868001dc0000007e800000530000000060000000000000010800000000ff80003c000000000000000000010200000000000000000a60008307d057000574fc81c4be000c61bf30e000000440003f0002150e20d80026f0002b0000001c600000000000000280000008d00000000000000000486000c7800000440001a74c20000b800184000001000008ccaa800000000000003a6000000dc08a000000000000007f00000000000000000000c68050000000017f4da2c8f581d3cc234b80002fc618ac9f218c16ccf0004988fd1200032c5f1349b746486045a3b00006000000000518189d024c0003216b000000000002261cc00000000000ff000000000000000000240000041600000133000000341844620003b02619c000001a32549511280045225000000000000000cf000000d083c2c847523a6300000000000000002004008010000100080000e030000040040100080000a0000700800a0000000801600800806006000010060020040000000000000000002028000110000100000000200001810008000020020020080100d0060000080100000c0100101201402000002004000000020000000000e00001002018030008050060040180200000003001000004000000000000080100800c0100000e004000000000000100100a008000000000000000000000402002012004000010
  | 4 => 0x1d53ae08c651c80e032c4906016e4bc7494a0b481c000004027d000055290980000000008d8820000000009883e00000000000330790000a50be5407027048c034c980035e7241900000000000000000000000004ba0406f09c0000009a06e3589a02c800000598dd918248600a88fb2322e800000000434c893200035800000000000c19a200084800000332000000000005e8b70ab000000000000000287fa5b000000bb00000024c3e25a218144970003785a4e29a924e6c8760c83f614d20a160441951e2090001a40001b35c7e00014b000000000001da00000096026734000004aa2a8dc8474000006d9fa1ae470508c90005c8a0800000000000000004ec00000000000000000000000000000043800000000000001f00006ac00000000000f112b0000008d17300000000000000000ce12d2be638e78000000008d9aa06e5591680000084c0000011800000000000000100000000000012828447c0011100000000000000000000000f6000000000003c0000002b426c00000000000001942600d000090000000000000000000000000000000000000000001ba0008c000000000000b10e2246000001b401e000000000bc000000002d8570000cc000000000000005e4088300340ac001074a20003b9f700051c000004325ec0002c496000000002b6998d8a671829201c94e4726e09f99f2922e00004f20400074041188000f8a6b0b08983e8e6000418d822840c254c91c33b4000001ce1d4000f180003e6f80027111c000e007e06627ca193a186001371401628b86884924a0385f09d01812c0000000055c5714400000000000000000330000004e01700021e76d0a05622800000019144000001080000012ca0a000874000784580000009e0006200006700000057990000000001ed38c1b000000000000f00000007a49600009c000000000007f0000da0004f400000080515158992e8000e580000000000000000000d200012e2e400000160000000004a400000000000000000003c2001108000000000000000013000054000534000000b8000000290000000004800000000129130000311d621420c05800112000000c022a0000024400000000000000748000001ea6f40000000000000000000000000001ba0000000031293c000b32e200035800000580900000000012b000000000000bb0003c8452020003b800000000000000000003d0000000000b52f1c44800001f84d000000002230008e8000001781e4ee80017e0000026a000000440000005d4500003b23ac000000000000000000034cc514f3de2a10193c382488cd0003660000010935a0003f8f6000128a9936000924aa0000000000000027c000000003d88701e80000
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xb9a00179b11980e94020a9e1d07909882a4a41121a0228885838a0d991615a5199385170e070c9a88000b1f9c209c8686049ba30013238300008f0c018014801f002210000400099e80091296a10100000000000f801d950d12029a020c4821c682090c00181180ce01245808b001015247154852d0e92392a228e8725dc562d4d4391ee4b0ea6a1d24715485250e94382a429287491c95114543a60e0a88a2a1d28725405050e9838aa028287491c94314542c1aa6b1686214a47158b4310b0aa98c2a1085a150e61cc932a48e2a18a4a0e15535874310652392c3a18838354c6250441d0a873166298d0d7294d434868ab8ca6a1a43071d95350d21a30e0a9a8690d15731532148686b98a910a43291d1618c821b0ae62108210e856310841086523a2c518843235cc644842192ae63224210ca6749912108662b98c890843615cc6448421d0ce63224210ca5731912108742b98c890843215cc6448421948e8b1a4210ce07058d21086523b68690843291d94348421d0ac6a1a4210e0d63548421029238aa4210818558d5110440a48e4a88822061543d85528c306a1ec4a8c61c150d5294430e0a87292a21870543549510c28ab8ca6a1e41455c45350e20c1ac8b10a69050c7550d324830632a8699241a250c604c920e0a86990a290560704c8514820eb98c8a8841491d15108420a1ae529a878850d7214d438420eb9cc9a9421499d35208610c2ac8b08a6885147550d314430a32a8698a21c150c524c510d2286302628866052181314420eb98c8a9021491d15208410
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x10070296240c0660120014202c06c05531c562d0c42c05531c961d0c418848758d4348421a808058d4348421c05631c55210840c05631c95110440a088550c604c920d01431c13214520905831d15108420905839d35208610a108550c604c510e0143148604c510905831d15208410
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => packedAt s2K6 (756+((h/14+packedAt s2K6 (672+(h % 14)*6) 6) % 51)*7) 7
  | 5 => packedAt s2K5 (21203+((h/233+packedAt s2K5 (18873+(h % 233)*10) 10) % 922)*11) 11
  | 4 => packedAt s2K4 (26076+((h/208+packedAt s2K4 (23788+(h % 208)*11) 11) % 1327)*11) 11
  | 3 => packedAt s2K3 (3850+((h/25+packedAt s2K3 (3675+(h % 25)*7) 7) % 91)*8) 8
  | 2 => packedAt s2K2 (800+((h/4+packedAt s2K2 (780+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffff03ffffff81fffff07ffc1ffff9e3f1ff
  | 1 => 0xfc0ffffc07f07ffe0f83ff87ffe1e03e9c7e67
  | 3 => 0xfff03ffff8007ffff003fff87ffe003f1f8f87
  | 4 => 0x3fffffff81fffffc00007fffffc7e00ff8
  | 5 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x98208118912010005284b0088c02298821b0ab
  | 1 => 0x296312287244a49605a15485352142928c5665
  | 3 => 0x50c5a45120e9492ab04269505a540525168b86
  | 4 => 0x628a3882448c0dcd29680c4463999607c00d50
  | 5 => 0x830c30e3870e71f1ce738e6603111807fb6000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36789
namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x80046002a00bf43bd43be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x10270a0a1e610030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (104+((h/2+packedAt s3K4 (96+(h % 2)*4) 4) % 11)*4) 4
  | 3 => packedAt s3K3 (57+((h/1+packedAt s3K3 (54+(h % 1)*3) 3) % 5)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fffc0fffffe0c1ffffe0fff07fffe00f3f3fc
  | 1 => 0xc1ffff03f07fffe0f83ff0fff8780fff4c7ccf
  | 2 => 0xfe0ffffc007fffff003fff0fff800fff8f8f0f
  | 4 => 0xfffffff800fffffc0000ffffff003f00ff0
  | 5 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x84204628a0101005284e0113008a621811b15c
  | 1 => 0x94448a1904a484a05a1290a54850a4a94454c5
  | 2 => 0x8a914406949094b04252a0a950149528a8b0a
  | 4 => 0x294e20924c0dae729681888ce6658063e00ea0
  | 5 => 0x318c38e38e71cf9ce739ccc0c4460183ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeac0c0eaeae8e8eaeac0c0eaeae8e8eaeac0c0eaeae8e8eaeac0c0eaeae8e8eaeac0c0eaeae8e8eaeac0c0eaeae8e8eaeac0c0eaeae8e8eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36789
namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x68c20000000a003098e3274d80000079120000000aa4a064800121380140024580002e780014c00000000069f00944800000027462c0000e1000300000084400015000000101000000010100020000007ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x681df32d03ba65a05f94740bea8e817d54902fca7205f54e40df21c81bc43902fca5205f54a40dfa1481bd42903be6520774ca40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40efa9a815f53502f8a6a07714d40ae29a817f52502f8a4a077cc940ee992817f51502f8a2a07ed0140df202817e54102fca6205f54c40df21881bc43102fca4205f54840dfa1081bd42103be6420774c840bf288817d511037c82206f10440bf28081bf40103f480206f50040fca0081b940102fea9985f95330beaa6617c54cc2fca5985f54b30ef99661dd32cc2fca3985f54730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061df320c3ba64185f94430bea8861de310c3b862185f94030fda0061f8400c3be60187e8c030ee98061f9300c2fea9905f95320df2a6413e54c82faa9906f553209eaa6417c54c82fea7905f94f20ef29e415e53c82faa7907754f20aea9e417c53c83be65907b8cb20ee99641ed32c839a65905f94720bea8e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d52883be6510774ca20bf28c417d51883dc43107b08620bf28441fb40883f081107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41df32483dc6490774c920f699241cd32482fea2905f14520fda0241f840483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041df32083ba64105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10ef99621dd32c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910ef99221dd32443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52043be6408774c810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xf54ccafca9995f55332be2a665df43ccbbc87997750f32ee21e657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccbbc85997750b32ee21665df51ccbbca3997754732ee28e65df50ccbbca1997754332ee286657f548cafca9195f55232be2a4657d538cabaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65de434cbba86997710d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe84997790932e721265dd424cb9a84997710932efa8a65de514cbbaa2997714532efa8265de504cbbaa0997714132bfaa0657e540cafaa8195f15032bf298655e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e837e52d06faa5a0efd0b41dea1683df32d07ba65a0df94341bea86837d54906fca720df54e41bf294837d52907be6520f74ca41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0dfd4941f7a92836f52506f8a4a0fb14941b629283bf425077a84a0f7cc941ee99283f7415077c82a0dfd4141fda82837b50506f8a0a0fe14141bc282837e54106fca620df54c41bf290837d52107be6420f74c841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31f7296636e52cc6faa598fb54b31b6a9663df32cc7ba6598df94331bea86637f548c6fca918df55231be2a4637d538c7be8718f710e31bf294637d528c7be6518f74ca31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c6f8a498f7cc931ee99263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790f7ccb21ee996437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21f7a1443ec42887be6510fb8ca21ee99443ed328879a6510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410fbd0821f621043df32087dc6410f74c821f699043cd32086fca210fbc8421fb10843ed21087ea4210df94021fd280437a50086faa010fe54021bca80437e53d02faa7a05f94b40bea9
  | 2 => 0xb3f838d3f9f8080028000f02ca788259c93a8708a186f47a55d14273298001318000000741ba695286c80003b000000000e20000d81f00008a000078000000008f08f45e9b8730003a6000f40000000004598d46e32c000000865192f2b20e067cf71bc0000000f2a05120011fa50474608671413e696534106208638998220008ac001a943a140000000005b8cbaa34847ad4800007e7200005b00072c2792900062809083322000000000002755c0002361c50c93e0009551f0a00003102080000008d028f6000000000001b6a08001ba1e26c48f800000428270a32d87c13a00028800000277220000001ea0004007400025e0012329833a000121cd0007541ca2515c2042c95f4940304a26720e2bc46a6a000684f32b026e5a40012d0f4a9d4c8e0000248000000005f85e8000004d4010002567f80029f05e0b1098331d80000028514e0683d8000005bcc7a3c4388a9378000007949f800000000000005440d4a28000f8a1109000000790630011ba9c4a71a221a68c358f8258974a5829488358ae000574034024058060000000100000202001801002000008000000100080101000001801008000008010000000100200200800001000010018000000040100700000c0000401401c000010020100080100a0100000500600c030010040000000002400001805000028028070000080480200000c000020060000000200000000803006020028020020200b8010000440000100c01800002000000008020000040000000001003801002034018000000080080401e0000000001400001801002010008000000100000101800001800014018010020000000000f0040000280000a000040070020040000600400c0000000000402808000018018030000000700300800c00801002010000000060080180000c0200700400000c000000040000480200001c000010000080400000200003803000000020010000000000d018008028000077e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143fda82877b5050ef8a0a1fe14143bc282877e5410efca621efd0c43ef21887bd4310fba8621df94843f7290876e5210efaa421fb54843b6a90877e5110efaa221df94043bea80877e53d0afaa7a15f94742bea8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390afca5216fd0a42f7a14857e5190afaa3215f94242fd284857a5090afaa1217e54242bca84857f5350af8a6a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857
  | 3 => 0x8004fca0cdb1630002a8000000004f0848000006bd3a800280a910a0d508c0ac3a8092e65690d114000094001df0004f53c15d2500012a11d46869c4c80000000000000114000dba384b05485e05413000000297000000000001220011b000000000000790dc368ab19c00089c000000000b4400cd42a000b38000000014313a2340009a1241641d00008222e4210f0de39c4c40a9d22d62555980000011c641b30545d4cc8b92c82ccdd8000266103b0f24600013e00055c85c000000160015884d000001259a651c0000017f00083c038004c2a44bb1dc000668fc8001348b1331472b073c0000603e6552480002200000220000120000000000000000051e000000ef000000001740001a11c8d83bc000000000006302504917c17d050000fe0000000016e27d148d90009700027b0740000020c53a2d912000380111238000009680b80000033c000a2000a983ba1600000001800000000000000001f8001ab382000000e400018ceca9351864cd01b01c20000019b45c84000000000ae4001490000000000049c48800000000001219ca32c000000001e8000891c41ea001291e14624a8c80003ae0001386a136000482720fa0400015000000105800310000000f71a87bc50800000000af05c0000f4001b911c768001b50c80015698716843ceb1f11a28845210c1ceadc42800000695240002021c8e88c743e7fc3300000000000000000000a68000001e0000863982311a83c000000de92e000000399f700040c000df00074000000000000001250000000017d2aa0c4d412605c0652f8004a62a400232036000000180000012680019254c0000000044d19800000000991f4354588000882ee0000028b0003f47da5b0a400043800000001021b85004395500035a70cfa8c1444340d72ab0003e5009d84c8a946020800000000000000001118ad00000000000000544001dd1f45f0001200001848c8dc0001b0769160000000025130224c000890aca554d0d3000000000a83da9b093838000000000000000000000000000130000000000a40002b20010001c000010000005680008a80000000000000000000000ac38e4d80000001a175382402f2000b900856c4c00295b1fe9301a0d7284ab0368004d600072a6531600000000000a28748000000005315404071485a2d0002d400000000084000005507f54da410ca6788c05519859800139000000002a90640004b91c000619579053069140014a0006502f0a55026fc000000000000000052c000b68160008340017a3ec0011d8000c02e901a560002ac00000312000002b5000000000000002c0000bf00030c5d8ca000a704f00020478d0c1383e49b4000304044449d9db412000b00003f43a90da5718a0a103998000000001920000007700010819cf627600015cb89e953c6147f0e
  | 4 => 0xd2028000071fb0986b00020e000818288260009f4210b10a65a87e21151a0003494f0b40013c97b5240000024f00018890961000160002621706f80009600000000170000000c00003685e000000000898e300000000091968510a1c000000009e8798c2000001508000007804e000348000f3
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb300c25f654c030a7191300c34d524c0309ed95300c2b8644c0309798f54c825d63d53209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e54ccb20c755332c832d548cb20c795132c831d544cb20cb55132c834e534cb20b3d9532c834f654cb20d3d5132c838e544cb20d355132c838d544cb20c355132c834d329472097d8d548825c635522097d8d518825c6354620ba58021883395410220ae993208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d18553482cd638c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324834d32145209e99740483c932d0120ce55040483c93210120ae99320483c932c81209798f540825d63d50209e983540825e63150209758c540827661150209d584540825d6594c2097d89530825d6254c209798c530826e6214c208f992520823d64948209798e520825d639482097597320825f654c820d3949320834d5388420d354c210834d53c80209bd95200834d53480209ed95200825e63d53109758f54c423e64d4f108f59353c426e6294f109b58a53c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c434f524cb10d314932c433b54103109798f548425d63d52109b98b548426d62d52109b988538426d6214e108f992528423d6494a109798e528425d6394a109798c528425d6314a10d3949328434d524ca10f24c9208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109ed81544423e6515110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10cbd53524432c54d4910d3d4f524434c53d4910d3d8f524434c63d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524425e63149109758c524426e6514910cbd50524432c5414910d3d4c524434c5314910d398c524434d6314910da580524425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d314932443385488110da14a20442786548110ce15120443c93248110bc185204433854c411097d8d540425c63550109798c540425d63150109b988540426d62150108f990530423d6414c109b988530426d6214c109798e520425d63948108f990520423d64148109798c520425d63148109e980520434e524c810d354932042796510010ce55040042f161100109e596100427765440109ed9510042b86444010
  | 1 => 0xc65d6510c31c7550430c6cd6210c31d354b320c6d561cc831b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c867a60d53219e58354c865e63153219758c54c865f63552219718d548867b60552219e18154886cd6310a21d3d95328874c654ca21d3d51328874d544ca21f1d8532887c4614ca21b358f218863f64542218f191508865f63542219718d508874d325422197d8d544865c63551219bd89544867b60551219e181544866d6294d218fd91534863c6454d219ed8153486786054d219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c219798e520865d6394821cb553420866d6510821b358c420865d65cc821c7953320871d54cc8219b596320872d548c821b358e32086e5618c82197d95320871e544c821c7551320872d544c821d394d32086cf654c821d3d95320874f544c821e3951320874d544c821e3551320870d544c821d34ca51086cd63c8421f14ca210866f65484219dd9521087c73248421ce95250087395494021d694e50087595394021f24ca500875b3294021d64ca500874d3254021ce95150087395454021d694d50087595354021f24c9500875b3254021da8c950087593254021da4c9500874932540219798e52d025d6394b40d394932d034d524cb40ab588439025e6394a409758e529034e524ca40d3549329038d424ca409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d409798c525025d631494097997325025c65cc94097995325025c654c940d614f405031c5390140ab58843102b96010c409798e521025d6394840ae583421034e524c840d3549321038d424c84097d8d511025c63544409bd89511026c6254440cd54441102b96010440ae592401023f6550040a718d401027b6550040b618d40102bb6550040ced95401039b6350040ae18d40103986350040a618d40102bb6250040e6cc940103993250040ae185401026e62153309b58854cc34d52ccb30ced5040cc2cd6210e30d3949328c34d524ca309bd89518c26c62546308f992544c25f63551309ed81544c23e6515130c7d53324c31c54cc930c7d51324c31c544c930d3d49324c2d8604c930ce153304c31c548c1309b98b540c26d62d50309b988540c26d62150309d984540c275611503097594430c2cd6210c30d398d520c34f4354830d310d520c34d52cc830b6583320c34e524c830d354a310c34d520c430b6580310c36952d00309e594400c3395410030e610c400c3695210030d354
  | 2 => 0x1000000040000c0000c0002c000000001401008330080a0000600008030090440007807004110a010000140080100016010020240f01007010040100005c070040100c08000000000a004000040a01800014090040b00c020080100800154029bd8951d0e6c6254743d6d0c5050f3a43141438fd954310eb86050c4397d954310ed86050c43d398d5210f4e4354843d350d5210e5f63547429718d51d0a5f63543429718d50d0b4e6294e42d694e5090b595394242ced0a5090b5a5354242d654d5090aba6090942d354e4210a3f65508429bd954210b4d53508429ed8154cca786055332b6d8143ccad86050f32c755043cca3f64543328f19150ccacd62d5332b6d8154ccad86055332c755054ccacd6215332b698242ccad96090b32d554451cca9f6454332a719150ccb5950143329e983548ca7960d5232ba582428ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca5c6550d32c7151434cadb6050d32b6181434cace6210d32b398e424cae960909329b195424cacd6295132b3d89544cad76155132b5185544cadb6055132b6181544cb1d5415132b3593524cace61d4932b3583524ca5e6590932b6982424cad96090932b3996424cb4e6590932b3592424cace6190932f2982424cacd6090932f2582424cac96090932b3995424cacc6550932e3d91424cb8f5450932e3151424cacc6150932b3d81424ca5e6510932b3988424ca9f6454532a7191514cadb6054532b6181514cb555114532a7d91504ca9c6454132b5d85504cad46154132d6540504ca5e63d50329e983540ca7960d50329798c540ca6e621503297d95320ca6f654c832d394d320ca5e6394b419758e52d067a6094b419e58252d074e524cb41d354932d078d424cb419b98a539066d6294e419798e529065d6394a419758b535065d6214d41d3d4f525074c53d4941d3d8f525074c63d49419798c525065d6314941d3d4c525074c5314941d398c525074d6314941cb14b42506b4615094197997325065c65cc941d3d4b325074c52cc94197995325065c654c941d3d49325074c524c941e3509325075b53d4141d614f505076b52d4141da14b505075b32d4141d64cb505075b5314141d614c505076b5214141da148505073b4214141ce508505075b3214141d64c8505073a41141419798e521065d6394841d3949321074d524c8418fd9541106b860504419dd95411065f63540419718d501066e62d53319b58b54cc67a60d53319e58354cc66e62153319b58854cc74e6354b31d354b32cc74e524cb319e983548c67960d5231b3588438c74d524ca31b358b318c65f63551319bd89544c66c62551319ed81544c6786055131d3d49324c74c524c931b5185324c67b60550319e181540c66e62150319b588540c67a60150319e580540
  | 3 => 0xc5a0407e7440014e466180310004aa0007d8122cc0346189e470640fd8982783207a8000000004d8004e28ac0012d000610f100023a1e0e20963ec8f0000eb3d291822a251683992f02926c1d4f3157038374f01f029e2e485149446370da1e81b0709089df2b013c362052a079c19a1d1ca8b424a4200099c318003f86b41a8070007b8001ac00000000013000000e4000000368990cd19c668b720d32c3c81300000000000191192020000001000008e0882f011000000000065311861d40000000000081c459c700048cd51b6064000f58003aa000001760008bcd79ce2bc00000000000000610002ea625348001525cc000000000740022a37491039000000000000001ac000b48d5000240878000b8310858000004cc4690d086850000002fe6c400260242000780000004a4a08cc0000000009f0fe000000004924980006b0622dcd20003f25b4000000000d83482e082090b1117000858019cf1080000003d476001180004520004a09c35c8040024146c1ec8f9710ca0000d2034b24786009a2609c0ff8a53c6828aa0162d08e8b51d40fc3ccae8db11e650162454040004113b000044538570000004c8003925bcf28792a60801198d0004e41280016414c509d23e4388911e40001bcc41ca00a57c2d04824e2ec2f0e13c264c921de4a862930a131789600014a2e8000071d83444d0000000001600003c0007b0eb86d09631800107068000bd217000700000000002b8000ff2ee000ee0003980bc00000012454889600762e0e59c34d88b07d000140130002323b44643e80000039d2b80008e000fa0004a60a00c0004323280a9d91568180000100003ca309142a0011b9052347e80000004e0006f8004d00004e80034a16c0ba1b3242bc56061144548568c13fa0008617c05665c0000029a971081420005e52f8be4da93c3405f2625f4000a846a2a846148000000a38a616c4bce690009c001290b500044800181490890000002ce564000004c8351289284248f8ad9bd3004b85801e44458d2521f3307dd261c11ae7bc78906410450d01011d86787f25a09a364ab24727046ce98383da4209f08e0ee1900d9821d25907e0870007c50c21c174654778522c21c02a8bf00053000000000000dc9b3254100658002e05542e8001d00005198f1628c4d38730ce510000000008851c80c3ba1400019b000000898f9204028000140202c0601404000390240906c050341803403000040040700000000020b801028030240100c00000010001e00c0a0080100407010010040e0180103c0e00c09004000880900c0000c1601412024030402203404000160000305c1d00007004000240001c000240000420000030000400c000000301000000090000100c040080001c03024080500301c1200002030020580400007014010201901008024
  | 4 => 0x107151000000a593f000514e81b237c018389404163400022e37e8d0d1a562ca4609010307c7d4d41991da0dc2a0a410c6848b20c05a02c3d18c0ec1991fa3d36e3d0e287410a31c772433060085e9ea0000000224d2566708800000096c1124e36a000350003b60004480034c7188700003e758fc0d31c64106f1852124b06916b4d40e8b91350424f400000000001328000b2000498004a00000019d0001b8000000004dc7e80044000104a630002cc2b00030e975000003fc000a18462d80287c1a948025c4a8002f6248929bc3e6570000100009b8c70f6054000211bb18a9ad1393a0006c10d0e433e1f0700f73560e4bf2281141450f014094344418001028980015a4966e00020f4de0c067a6600000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x700060a8307801f001e22120008000f800b1b8e16980024801c0022800001801613801b000000048b9f919d01001d9080052393140002179712a0000a00000003a11c999e90088c949105a50421a08d000682958ea3000000240f1a0d990c00800900000000000998801a8015008600401000c00100268c10124002890204080000c05487050d5210e8c382a821e65461c15415332c1aa8b10a9995187454050ccb0c2a0c0a1a65451c55415132a30e0aa0a8994cb70593524ca47ba2c1a9265629c36450932a28e8a88a29955070544514ca8c3a2a028265541c55014132a92e129265a0e0c6550932506c238a84992834c1c54214141e1284990a0a0c4d7218d501068c382a821863835516210c31a96e0aa26510e0f644c95088686b98c4aa043525c3544c821a1aeb2a26410f09544ca50087852a264a8043c25513254021a92e429e80a050d7214e405024c39ac1a1081261cd601044091ae431a80204c97218d4010254b90c6a0081625c86350040d14e431a80204997218d4010344b90c6a0081225c86350040930ed9928020498764c9401030c2a0c099261261d160cc830c92a4b06641849874580310c324a92c018861465d44310030b12e4218801870843548400c306322a498061461cd5410220898ecaa2649054471551324832532a65a0241461cd5410120a60e2aa08090709544c840483453226590241435d2524c82089ae531ea98850d7414932c428d39ea820621435d2524ca10c92c6b00a488548754c9204432432a6490221c21513248110c60a830a40886c1321852044226b90c6aa021461cd5410010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x280b080e82a4800186c008002024a08805516215332c04651c5424c941b00815093214141a08805516210c31889821cd6010440c087454960cc830c0874549600c430908875513210120b00815513210120909829cf5410310a40854c86148110e00544c86148110909821cd5410010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => packedAt s4K6 (770+((h/14+packedAt s4K6 (672+(h % 14)*7) 7) % 80)*7) 7
  | 5 => packedAt s4K5 (21436+((h/233+packedAt s4K5 (18873+(h % 233)*11) 11) % 1115)*11) 11
  | 4 => packedAt s4K4 (25868+((h/208+packedAt s4K4 (23788+(h % 208)*10) 10) % 827)*11) 11
  | 3 => packedAt s4K3 (3850+((h/25+packedAt s4K3 (3675+(h % 25)*7) 7) % 110)*8) 8
  | 2 => packedAt s4K2 (800+((h/4+packedAt s4K2 (780+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfc07fffc07ffc183ffc3ff0fff83fc031cfe7c
  | 1 => 0xfff81ffffffffffc0ffc1ff07ffffffce31fff
  | 2 => 0xffffe07ff81ffffff0001fff8ffc3fff03e38f
  | 3 => 0x7fffe001ffffffe0000fffc007fc03f0
  | 5 => 0xffffff80000001fffffffffff0000007fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2530c30471448a80b2c0a70293a264310c6e3c
  | 1 => 0x85244089209001405440910248489506114d5
  | 2 => 0xb0a1095120d229a9502292ab096a32a702a30a
  | 3 => 0xa2c596624483adce69aac08a0e7320c7b403e0
  | 5 => 0xc3061843871c31738e331ccc40400306dbd800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8c8c0c8c0eee8eee8c8c0c8c0eee8eee8c8c0c8c0eee8eee8c8c0c8c0eee8eee8c8c0c8c0eee8eee8c8c0c8c0eee8eee8c8c0c8c0eee8eee8c8c0c8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36789
namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x46000a20810df32dd32de31dc31ee21ec21
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x202a8a299710c421
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (104+((h/2+packedAt s5K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s5K3 (56+((h/1+packedAt s5K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fffff80ffe0c1ff87fc3ffffc1fe018cfe7c
  | 1 => 0xfe07e0ffffffffe0ff83fc1c07fffffe7333ff
  | 2 => 0xfff800fff07fffff0003ffe007fe1fff83c38f
  | 3 => 0xffff800ffffffc000007ffe003fc03f0
  | 4 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8c30c808e10454031814c0a471d1321884563c
  | 1 => 0x14910111242800a068814408924244a83130d5
  | 2 => 0x28425aa243514d4d0452aac124b5195382c30a
  | 3 => 0x71659cc48a1d6e76b558228247399063dc03e0
  | 4 => 0x418610870c618b98c6633313802001836ba800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0eeeac8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36789
namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x5c3803b18914835a804800078a000c88b2536b151d00140000441eb524fc508003dd174e10fb7706800764353004600a9102f002868015b30071c8062018006c0108b5e0003e004cc190c00100010880100280010304046030000b02017fd50057f54017f95005fd54015f55005fc54007fd4c01fe53007f54c01fc53017fd0c05fe43017f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803fe4200ff50803fc4200ffcc803df3200ff8c803fd3200f74c803fc32007fd4401fe51007f54401fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc21007fd4001fe50007f54001fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42005ff08210007fe2108003f71084001fd8842000ffd9510005feca880037f65440013fb2a2000ff99510045fcca88003fd65440017eb2a2000ff19510045f8ca880037c65440013e32a200affd9110055fec888003bf64440015fb22200aff99110015fcc88802bfd64440157eb22200aff19110015f8c88802bbc64440055e322200affd5110056fea88802bfe5444015feaa2200adf55110057f8a888003ff63440017fb1a2000f7d8d10005bec688003fe634400f7f31a2000ff58d10005fac688003fc634400f7e31a2000f718d10005b8c688003ff5344001ff29a2000ff54d10007f8a68802bff4344015ff21a200aff50d10057f88688027ff62440137fb122000fbd8910005dec488027fe62440037f3122009ff5891004dfac488027fc62440037e3122009fb1891000dd8c488027ff5244013ff2922009ff5491004ff8a488027ff4244013ff2122009ff5091004ff88488027ff3244013ef9922009ff8c91004ffa6488027dd3244013fe1922000ffd4510007fca288003fd5144001fe28a200affd0510057fc828802bf64144015fea0a200afd50510057f88288003ff3144001ff18a2000ff4c510007f86288027ff2144013ff10a2009ff4851004ff84288003ff5044001ff2822000ff54110007f8a08802bff4044015ff202200aff50110057f88088003ff3044001ff1822000ff4c110007f86088027ff2044013ff1022009fe8811004ffa4088027f92044013fe1022000ffc4110007f62088003fe1044001fb0822000ffd9410005feca08003fe65040117f3282000ff59410005faca08003fc65040117e3282004ffd9010025fec808013fe64040057f3202004ff59010025fac808013fc64040057e3202004ffd5010026fea808013fe5404009feaa02004df55010027f8a808003ff63040017fb182000ff98c1003dfcc608003fd63040017eb182000ff18c1003df8c608003ff5304001ff2982000ff54c10007f8a608013ff4304009ff2182004ff50c10027f8860800fff62040077fb102003ff9881000dfcc40800ffd62040077eb102003ff1881000df8c40800fff5204007ff2902003ff5481001ff8a40800fff4204007ff2102003ff5081001ff8840800fff3204007ef9902003ff8c81001ffa640800fdd3204007fe1902006bf98410007fea208003fe5104001fea882000ff14410027fe8208013fe4104009fea082004ff10410007fe6208003fe3104001fe9882000ff0c41001ffe420800ffe2104007fe9082003ff0841002dfcc008003ff5004001ff2802000ff54010007f8a008013ff4004009ff2002004ff50010027f88008003ff3004001ff1802000ff4c010007f8600800fff2004007ff1002003ff4801001ff84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xbfe410c01dfea08600eff1043003ffe621801ffe310c001ef1886007ff4c43003ff8621801fdc310c01bff908600dff8843006ffa4218037fc210c01f7f3006000ffd4030007fca018003fd500c001fe280600effd0030077fc801803bfd400c01dfe2006007ffcc03003fbe601801ffe300c00ffd1806007ff4c030007ba601801ff9300c01bff900600dff8803006ffa4018037fc200c001ffb2e2000bfd9710007fccb88022fe65c4001feb2e2000bf59710007f8cb88022fc65c4019ffb26200cbfd9310067fcc98800afe64c4019feb26200cbf59310067f8c98800afc64c4019ffaa6200cdfd5310067fca988033fd54c4019beaa6200cff15310007fec788002ff63c4001ff31e2007bf98f10007fac788002fd63c4001fe31e2007bf18f10007fea788003fe53c4001fea9e2000ff14f10067fe8788033fe43c4019fea1e200cff10f10037fec58801aff62c400dff3162001bf98b10037fac58801afd62c400dfe3162001bf18b10037fea58801bfe52c400dfea962006ff14b10037fe858801bfe42c400dfea162006ff10b10037fe658801bdf32c400dff1962006ff4cb10037ba658801bfc32c4001ffa8e2000ff94710007faa388003fc51c4019ffa0e200cff90710067ec8388033fd41c4019faa0e200cff10710007fe6388003fe31c4001fe98e2000ff0c710037fe438801bfe21c400dfe90e2006ff08710007fea188003fe50c4001fea862000ff14310067fe8188033fe40c4019fea06200cff10310007fe6188003fe30c4001fe9862000ff0c310037fe418801bfe20c400dfe9062006ff08310007fecb08002ff6584001ff32c2008bf99610007facb08002fd6584001fe32c2008bf1961005ffec90802eff6484017ff3242002bf9921005ffac90802efd6484017fe3242002bf1921005ffea90802f7f5484017ff2a4200bff5521005efaa90802ffc5484001ffb1c2000bfd8e10007fcc70801efe6384001feb1c2000bf58e10007f8c70801efc6384001ffa9c2000ff94e10007faa708003fc5384017ffa1c200bff90e1005ffa870802ffc438400bffb142005bfd8a1002ffcc508006fe628400bfeb142005bf58a1002ff8c508006fc628400bffa942005ff94a1002ffaa508017fc528400bffa142005ff90a1002ffa8508017fc428400bff9942005f7cca1002ffc6508017fd328400bee9942005ff0ca1004dfac308003ff5184001ff28c2000ff54610007f8a30802fff4184017ff20c200bff5061005ff88308003ff3184001ff18c2000ff4c610007f86308017ff218400bff10c2005ff4861002ff8430800efe6084001ffa842000ff94210007faa108003fc5084017ffa04200bff9021005ffa810802ffc4084001ff9842000ff8c210007fa6108003fc308400bff9042005ff8821002ff44108017fd208400bfc9
  | 2 => 0x3007ffca51803ffd528c01ffe294600fffd0a3007ffc851803ffd428c01ffe2146007ffcca3007fbe651803ffe328c01ffe994600ff74ca3003ff86518003ff618c001ff30c6000bf98630007fac318002fd618c001fe30c6000ffd4630007fca318003fd518c001fe28c6012ffd0630097fc831804bfd418c025fe20c6007ffcc630007fc6318003de318c001fe98c6007ff0c630007b8631803fff218c01fff10c600fff4863007ff8431801efe608c001ffa846000ff94230007faa118003fc508c025ffa046012ff90230097fa811804bfc408c00fff9846000f7cc23003ff6611803fff208c01fff104600fff4823007ff84118003ff654c0017fb2a6000dfd9530004feca98003fe654c0117f32a6000ff59530005faca98003fc654c0117e32a6000df19530004f8ca98047ff644c0237fb226000efd91300057ec898047fe644c0057f3226011ff5913008dfac898047fc644c0057e3226011ef1913001578c898047ff544c023bfaa26011ff9513008ffaa8980477d544c023fe2a26000ffd4d3003ffca698003fd534c00ffe29a6011ffd0d3003ffc8698047de434c023fea1a6011f750d3003ff88698043ff624c0217fb126010ff9893000dfcc498043fd624c0217eb126010ff1893000df8c498043ff524c021ff2926010ff54930087f8a498043ff424c021ff2126010ff50930087f8849801fff324c021ef9926010ff8c930087fa6498043dd324c00ffe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c298003ff514c001ff28a6000ff54530007f8a298047ff414c023ff20a6011ff5053008ff8829801fff314c001ff18a6000ff4c53003ff86298043ff214c021ff10a6010ff48530087f84298003ff504c001ff2826000ff54130007f8a098047ff404c023ff2026011ff5013008ff8809801fff304c00ffd9826000ff8c130007bc6098043ff204c021ff1026010ff48130087f8409801fff650c00f7fb286007ff99430045fcca1801ffd650c0017eb286007ff1943003df8ca1801fff640c00f7fb206007ff99030015fcc81801ffd640c01d7eb206007ff1903003df8c81803bff540c01dbfaa0600eff95030077faa81803b7d540c01dfe2a06007bf98c3003ffea61801ffe530c00ffea986007ff14c3003ffe861801ffe430c00ffea186007ff10c3003ffec41801eff620c00fff3106001bf9883003fdcc418006ee620c00ffeb10600dbf5883003fdac418002ed620c00ffe3106001bf1883006ffea418037fe520c01bfea90600dff1483006ffe8418037fe420c01bfea10600dff1083003ffe641801fdf320c00fff1906007ff4c83006fba641801ffc320c00fffb086007ff98430005fcc21801ffd610c0017eb086007ff18430007fea218003fe510c001fea886000ff14430077fe821803
  | 3 => 0xfb20a008bfd9050047fcc82800afe6414011feb20a016bf59050047f8c82800afc6414011ffaa0a008dfd5050047fca828023fd541402dbeaa0a008ff15050047fec628023fe631400f7f318a008ff58c50005fac628023fc6314011ffa98a008ff94c50006fca628023fd5314011fe298a008df14c500b7fe862805bfe431402dfea18a016ff10c50047fec428022ff6214011ff310a001bf98850047fac428056fd6214011fe310a001bf18850047fea4280237f5214011ff290a008ff548500aefaa428023fc521402bffa10a015ff908500affa8428057fc421402bff990a015f7cc8500affc6428057fd321402bee990a015ff0c850047fec228023fe61140017f308a008ff58450005fac228023fc6114011ffa88a008ff94450006fca228023fd5114011fe288a008df144500b7fe822805bfe411402dfea08a016ff10450007fe6228003fe3114001fe988a000ff0c4500affe4228057fe211402bfe908a015ff084500bdfcc028023ff5014011bfa80a008ff94050047f4a028023fd5014001bea80a008fe540500b7fe802805bfe401402dfea00a016ff100500affe4028057fe201402bfe900a015ff0805003ffecb9801eff65cc00fff32e6008bf9973003ffacb98002fd65cc00ffe32e6007bf1973003ffec99801eff64cc00fff3266002bf9933003ffac998052fd64cc00ffe3266007bf193300a7fea9980537f54cc029ff2a66014ff553300a6faa998053fc54cc00fffa9e6007ff94f3003ffaa79801ffc53cc00fffa1e6007ff90f3003fbc879801ffd43cc029eea1e6007ff10f3003ffec59801eff62cc00fff3166001bf98b3003ffac59804efd62cc00ffe3166001bf18b3009ffea59804ffe52cc027fea966013ff14b3009ffe859804ffe42cc027fea166013ff10b3003ffe659801fdf32cc00fff1966007ff4cb3009fba659801ffc32cc00fffb0e6007ff98730005fcc39801ffd61cc0017eb0e6007ff18730007fea398003fe51cc001fea8e6000ff147300a7fe8398053fe41cc029fea0e6014ff1073003ffe639801ffe31cc00ffe98e6007ff0c73009ffe439804ffe21cc027fe90e6013ff08730007fea198003fe50cc001fea866000ff143300a7fe8198053fe40cc029fea066014ff1033009ffe419804ffe20cc027fe9066013ff08330007fecb18002ff658c001ff32c6008bf99630007facb18002fd658c001fe32c6008bf19630097fec91804aff648c025ff3246002bf99230097fac91804afd648c025fe3246002bf19230097fea91804b7f548c025ff2a46012ff55230096faa91804bfc548c0217eb1c6000ffd4e3003ffca718003fd538c00ffe29c6012ffd0e3003ffc871804bfd438c00ffe21c600fffd8a3007dfec51803ffe628c0037f314600fff58a3007dfac51803ffc628c0037e314600fffd4a
  | 4 => 0x6fc62d4011ffa96a008ff94b50047faa5a8023fc52d4037ffa16a01bff90b500dffa85a806ffc42d4037ff996a01bf7ccb500dffc65a806ffd32d4037ee996a01bff0cb50047fec3a8023fe61d40017f30ea008ff58750005fac3a8023fc61d4011ffa8ea008ff94750047faa3a8023fc51d4039ffa0ea01cff907500e7fa83a8073fc41d4001ff98ea000ff8c750007fa63a8003fc31d4037ff90ea01bff887500dffa43a806ffc21d4039ffa06a01cff903500e7fa81a8073fc40d4037ff906a01bff883500dffa41a806ffc20d40317eb2ca01affd92500d5fec92806bfe64940057f324a01aff592500d5fac92806bfc64940057e324a008ffd52500d6fea92806bfe5494035feaa4a01adf55250047f8a928003ff6394001ff31ca007bf98e50007fac728002fd6394001fe31ca008ffd4e50007fca7280037e5394001fea9ca008ff14e50006f8a72806bff4394035ff21ca01aff50e500d7f8872805fff629402f7fb14a017ff98a5000dfcc52805ffd629402f7eb14a017ff18a5000df8c528023ff529402fbfa94a017ff94a500bffaa52805f7d5294011fe294a017ffd0a500bffc852805ffd429402ffe214a017ffcca500bfbe652805ffe329402ffe994a017f74ca500bff86528003ff6194001ff30ca000bf98650007fac328002fd6194001fe30ca008ffd4650007fca3280037e5194001fea8ca008ff14650006f8a32806bff4194035ff20ca01aff506500d7f88328003ff3194001ff18ca000ff4c650007f8632805fff219402fff10ca017ff486500bff84328022fe6094011ffa84a000dfd4250047f6a12806bff4094035ff204a01aff502500d7f8812805fff209402fff104a017ff482500bff84128067ff64540337fb22a019ff99150015fcc8a8067fd64540337eb22a019ff19150015f8c8a8023ff5454033bfaa2a019ff951500cffaa8a80677d5454011fe2a2a000ffd8d50005fec6a8003fe6354001feb1aa000ff18d5003df8c6a8023ff5354001ff29aa000ff54d50047f8a6a8067ff4354033ff21aa019ff50d500cff886a8063ff62540317fb12a018ff9895000dfcc4a8063fd62540317eb12a018ff1895000df8c4a8023ff5254031ff292a018ff54950047f8a4a8063ff4254031ff212a018ff509500c7f884a8063ff3254031ef992a018ff8c9500c7fa64a8063dd3254031fe192a000ffd8550005fec2a8003fe6154001feb0aa000ff18550005f8c2a8023ff5154001ff28aa000ff54550047f8a2a8067ff4154033ff20aa019ff505500cff882a8003ff3154001ff18aa000ff4c550007f862a8063ff2154031ff10aa018ff485500c7f842a8023ff5054011fda82a000ff94150006fca0a8067ff4054033ff202a019ff501500cff880a8063ff2054031ff102a018ff481500c7f840a8022fe6514011f
  | 5 => 0x8231007f8c11888bff408c445ff2046222ff50231117f8811887fff208c43fff104621fff482310fff84118803ff654c4017fb2a6200ff99531045fcca98803fd654c4017eb2a6200ff19531045f8ca98887ff644c4437fb226221ff99131015fcc898887fd644c4437eb226221ff19131015f8c898887ff544c443bfaa26221ff9513110ffaa8988877d544c443fe2a26200ffd4d3103ffca698803fd534c40ffe29a6221ffd0d3103ffc8698887fd434c40ffe21a6220ffd8931105fec498883fe624c4037f3126220ff58931105fac498883fc624c4037e3126220ffd4931107fca498883fd524c441fe2926220ffd0931107fc8498883fd424c441fe2126207ffcc931107be6498883fe324c441fe9926220f74c93103ff86498803ff514c401ff28a6200ff54531007f8a298887ff414c443ff20a6221ff5053110ff8829881fff314c40ffb98a6200ff8c531007bc6298883ff214c441ff10a6220ff48531107f84298803ff604c4017fb026200ff98131007fac098803fc604c4017e3026221ffd013110ffc8098887fd404c443fe2026220ffc8131107fc4098883fd204c441fe1026207ffd943103dfeca1881ffe650c4117f3286207ff59431005faca1881ffc650c40f7e3286207ffd903103dfec81881ffe640c4057f3206207ff590310f5fac81881ffc640c40f7e320621effd50310f6fea81887bfe540c43dfeaa0621edf550310f7f8a81881efe630c40fffa986200f7d4c3103ffca61881ffd530c40ffe2986207f714c3103ffe861881ffe430c40fef2186207ff50c310f7ba861881ffc430c40fffb106207bfd883103ffcc418806fe620c40ffeb10621dbf5883103ff8c418806fc620c43bffa90621dff948310effaa418877fc520c43bffa10621dff908310effa8418877fc420c40fff9906207f7cc83103ffc641881ffd320c43bee9906207ff0c8310fdfcc218803ff510c401ff2886200ff54431007f8a21887bff410c43dff208621eff504310f7f8821881fff310c40fef9886207ff8c43103fec621881ffd310c401ee9886207fd4c4310effe4218877fe210c43bfe908621dff0843103ffec01881ffe600c4017f3006207ff58031005fac01881ffc600c43dffa00621eff900310f7fa801887bfc400c43bff900621dff880310effa4018877fc200c411ffb26a008bfd9350047fcc9a800afe64d4011df326a002af99350047fac9a8072fd64d4011deb26a000af59350047f8c9a800afc64d4011ffaa6a008dfd5350047fca9a8023fd54d4039beaa6a008ff15350047fec7a8023fe63d400f7f31ea008ff58f50005fac7a8023fc63d4011ffa9ea008ff94f50047faa7a8023fc53d4039ffa1ea01cff90f500e7fa87a8073fc43d4011ffb16a008bfd8b50047fcc5a8006fe62d4011feb16a01bbf58b50047f8c5a8
  | 6 => 0x17eb18a208ff18c51047fea628823fe5314411fea98a208ff14c51137fe862889bfe431444dfea18a226ff10c51047fec428822ff6214411ff310a201bf98851047fac428896fd6214411fe310a201bf18851047fea428823fe5214411fea90a208ff1485112ffe8428897fe421444bfea10a225ff1085112ffe6428897df321444bff190a225ff4c85112fba6428897fc321444f7f308a208ffd4451046fea228823fe5114411fb288a208ff54451006faa228823f5511444dffa08a226ff90451137fa822889bfc411444bff908a225ff8845112ffa4228897fc2114411ffb00a208ff98051005fcc028823fd60144017eb00a208ff18051137fe802889bfe401444dfea00a226ff1005112ffe4028897fe201444bfe900a225ff0805103ffecb9881eff65cc40fff32e6208bf9973103ffacb98802fd65cc40ffe32e6207bf1973103ffec99881eff64cc40fff3266202bf9933103ffac998892fd64cc40ffe3266207bf19331127fea9988937f54cc449ff2a66224ff55331126faa998893fc54cc40fffa9e6207ff94f3103ffaa79881ffc53cc40fffa1e6207ff90f3103ffa879881ffc43cc40fffb166207bfd8b3103ffcc598806fe62cc40ff73166201bb98b3103ffac59888efd62cc40ff6b166200bb58b3103ff8c598806fc62cc447ffa966223ff94b3111ffaa59888ffc52cc447ffa166223ff90b3111ffa859888ffc42cc40fff9966207f7ccb3103ffc659881ffd32cc447ee9966207ff0cb31007fea398803fe51cc401fea8e6200ff14731127fe8398893fe41cc449fea0e6224ff1073111ffe439888ffe21cc447fe90e6223ff0873103ffec19881ffe60cc4017f3066207ff58331005fac19881ffc60cc449ffa066224ff90331127fa8198893fc40cc447ff9066223ff8833111ffa419888ffc20cc401ffb2c6200bfd9631007fccb18822fe658c401feb2c6200bf59631007f8cb18822fc658c445ffb246222bfd9231117fcc91880afe648c445feb246222bf59231117f8c91880afc648c445ffaa46222dfd5231117fca91888bfd548c445beaa46222ff15231105fac718803ff538c401efa9c6207ff94e31007faa71881ffc538c401ee29c6222ffd0e3103ffc871888bde438c445fea1c6222f750e3103ff8871887fff628c43f7fb14621fff98a3100dfcc51887ffd628c43f7eb14621fff18a3100df8c51887fff528c43fff294621fff54a310fff8a51887fff428c43fff214621fff50a310fff8851881fff328c43fef994621fff8ca310fffa651887fdd328c40ffe1946207bf98631007fea318803fe518c401fea8c6200ff14631117fe831888bfe418c445fea0c6222ff1063103ffe6318803df318c40ffb98c621fffc86310fffc431887ffd218c43ffe10c6200ffd8231007fcc118802fe608c401feb046200bf5
  | 7 => 0xa8823fd52d4457bea96a208ff14b5115ffe85a88affe42d4457fea16a22bff10b5115ffe65a88afdf32d4457ff196a22bff4cb5115fba65a88affc32d4459ffa0ea22cff90751167fa83a88b3fc41d4457ff90ea22bff8875115ffa43a88affc21d4411ffb06a208ff98351005fcc1a8823fd60d44017eb06a208ff18351167fe81a88b3fe40d4459fea06a22cff1035115ffe41a88affe20d4457fe906a22bff08351145facb288abff64944557fb24a22aff99251015fcc9288abfd64944557eb24a22aff19251015f8c928823ff5494455bfaa4a22aff95251157faa9288ab7d5494411fe2a4a200ffd8e51007fcc72881efe6394401feb1ca200bf58e51007f8c728823ff5394401ff29ca200ff54e51047f8a7288abff4394455ff21ca22aff50e51157f8872889fff629444f7fb14a227ff98a5100dfcc52889ffd629444f7eb14a227ff18a5100df8c528823ff529444fff294a227ff54a51047f8a52889fff429444fff214a227ff50a5113ff8852889fff329444fef994a227ff8ca5113ffa652889fdd329444ffe194a208bf98651047fea3288037f5194411fba8ca22affd0651157fc83288abfd4194455fe20ca227ffc865113ffc432889ffd219444ffe10ca200ffd8251007fcc128802fe6094401feb04a200bf58251007f8c1288abff4094455ff204a22aff50251157f8812889fff209444fff104a227ff4825113ff841288a7ff64544537fb22a229ff99151015fcc8a88a7fd64544537eb22a229ff19151015f8c8a8823ff5454453bfaa2a229ff9515114ffaa8a88a77d5454411fe2a2a200ffd8d51005fec6a8803df63544016fb1aa200ff98d51007fac6a8803fc635440f7e31aa200f718d51005b8c6a8823ff5354401ff29aa200ff54d51047f8a6a88a7ff4354453ff21aa229ff50d5114ff886a88a3ff62544517fb12a200fbd8951005dec4a88a3fe62544037f312a228ff58951145fac4a88a3fc62544037e312a228fb1895100dd8c4a8823ff5254451bfa92a228ff94951147faa4a88a37d5254411fe292a228ffd0951147fc84a88a3fd4254451fe212a228ffcc951147be64a88a3fe3254451fe992a228f74c951147f864a8823ff5154411fba8aa200ff94551006fca2a88a7ff4154453ff20aa229ff5055114ff882a88a3ff2154451ff10aa228ff48551147f842a8803ff60544017fb02a200ff98151007fac0a8803fc60544017e302a229ffd015114ffc80a88a7fd4054453fe202a228ffc8151147fc40a88a3fd2054451fe102a208bf99451047fec828822ff6414411ff320a202bf990510477cc82880abe6414411feb20a226bf590510477ac828802bd6414411fe320a202bf19051047fea8288237f5414411ff2a0a208ff55051136faa828823fc5414411ffb18a208ff98c5103dfcc628823fd631440
  | 8 => 0xf9865303ffac329802fd6194c0ffe30ca632ffd0653197fc83298cbfd4194c65fe20ca631ffc865318ffc43298c7fd2194c63fe10ca607ffd825303ffcc129802fe6094c0ffeb04a600bf5825303ff8c1298cbff4094c65ff204a632ff50253197f881298c7ff2094c63ff104a631ff4825318ff841298c3ff6454c617fb22a630ff99153015fcc8a98c3fd6454c617eb22a630ff19153015f8c8a9823ff5454c61bfaa2a630ff95153187faa8a98c37d5454c11fe2a2a608ffd4d53047bea6a981ffe5354c0fbf29aa630ffd0d5303ffc86a98c3fd4354c0ffe21aa62fffd895317dfec4a98bffe6254c037f312a62fff5895317dfac4a98bffc6254c037e312a608ffd495317ffca4a98bffd5254c11fe292a62fffd095317ffc84a98bffd4254c5ffe212a607ffcc95317fbe64a98bffe3254c5ffe992a62ff74c95303ff864a9803ff6154c017fb0aa600ff98553007fac2a9803fc6154c017e30aa630ffd0553187fc82a98c3fd4154c61fe20aa62fffc855317ffc42a98bffd2154c5ffe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153005f8c0a98c3ff4054c61ff202a630ff50153187f880a98bfff2054c5fff102a62fff4815317ff840a9822fe6514c0fffb20a607bfd905303ffcc82980afe6414c0fdf320a602af9905303ffac8298bafd6414c0fdeb20a600af5905303ff8c82981efc6414c11ffaa0a608dfd5053047fca829823fd5414c5dbeaa0a608ff1505303dfcc62981fff5314c0fbfa98a607ff94c5303fbca62981ffd5314c0fbea98a608f754c5303ffe862981ffe4314c0ffea18a607ff10c5303ffec42981eff6214c0fff310a601bf9885303fdcc429806ee6214c0ffeb10a62dbf5885303fdac429802ed6214c0ffe310a601bf18853047fea429823fe5214c11fea90a608ff1485316ffe84298b7fe4214c5bfea10a62dff1085303ffe642981fdf3214c0fff190a607ff4c85316fba642981ffc3214c0fffb08a607ff98453005fcc22981ffd6114c017eb08a607ff18453177fe82298bbfe4114c5dfea08a62eff1045316ffe42298b7fe2114c5bfe908a62dff0845303ffec02981ffe6014c017f300a607ff58053005fac02981ffc6014c5dffa00a62eff90053177fa80298bbfc4014c5bff900a62dff8805316ffa40298b7fc2014c11ffb26a208bfd9351047fcc9a880afe64d4411feb26a22cbf59351047f8c9a880afc64d4411ffaa6a208dfd5351047fca9a8823fd54d4459beaa6a208ff15351047fec7a8823fe63d440f7f31ea208ff58f51005fac7a8823fc63d4411ffa9ea208ff94f51047faa7a8823fc53d4459ffa1ea22cff90f51167fa87a88b3fc43d4411ffb16a208bfd8b51047fcc5a8806fe62d4411feb16a22bbf58b51047f8c5a8806fc62d4411ffa96a208dfd4b51047fca5
  | 9 => 0x801000600200800800201601e00400402600001c01a02607004000200401200401600000000000600e00200400000401a00000400000000200a00c05800000000200404c00401600001e02602602201200c00a00000600201e02800200400000200000001606200200200400802000400200000000200600203a02c00000201a00003603803a00800400200003000002a00c00000200600000800400800400600200000001800200000200400001001600000200000201600205c00200a01a00000402805400404200001800000004401002800200200000201600a00600000400600c00800400a00a00801000000404000c00000800000400000800400e00401e02e00400400004600008600801000e00000800000800c00001200800200400a00200201000001201600600000400600000200e00200000000600601200001e00200801e00000000000601200401c00400000802a01000402a00400400400600800e03800002400600800200e00200001600600002a00404c01800200600c02800400800001200600800404e00200c02200000400400001c00000a00001202201607801c00000000605400000200000000001400000200200c01800000001801203c00000201a03601800604e00601400001000c00e00200400002600e00c00800000a00008ffd9353045fec9a9823fe64d4c057f326a608ff593531a5fac9a9823fc64d4c057e326a608ffd5353046fea9a9823fe54d4c11feaa6a634df55353047f8a9a98d3ff43d4c0fff21ea634ff50f5303ff887a9823ff62d4c117fb16a608ff98b5300dfcc5a9823fd62d4c677eb16a608ff18b5300df8c5a9823ff52d4c11ff296a608ff54b53047f8a5a98cfff42d4c67ff216a633ff50b5319ff885a981fff32d4c67ef996a633ff8cb5319ffa65a98cfdd32d4c0ffe196a608ffd8753047fcc3a9802fe61d4c11feb0ea600bf58753047f8c3a98d3ff41d4c69ff20ea634ff507531a7f883a98cfff21d4c67ff10ea633ff4875319ff843a9823ff60d4c11ff306a600bf98353047fac1a9802fd60d4c11fe306a634ffd03531a7fc81a98d3fd40d4c69fe206a633ffc835319ffc41a98cffd20d4c67fe106a62fbf5965303ffec92981eff6494c0fff324a602bf9925303ffac9298cafd6494c0ffe324a607bf19253047fea9298cb7f5494c65ff2a4a632ff55253196faa929823fc5494c0f7f31ca607ffd4e5303efea729823df5394c01afa9ca607ffd0e5303ffc872981ffd4394c0ffe21ca607ffd8a5303dfec52981ffe6294c037f314a607ff58a5318dfac52981ffc6294c037e314a608ffd4a5318ffca5298c7fd5294c11fe294a631ffd0a5318ffc85298c7fd4294c63fe214a607ffcca5303fbe652981ffe3294c0ffe994a631f74ca5303ff8652981fff6194c0fff30ca600b
  | 10 => 0x10e30f11d052c66849b00016a040000002c8378aec8080000000b025fc00018140000001690fa0dd851a000000048a00039f8da000000012a804431066500000000000002948ea080a12600000000002992a5961030a32e19d80001ea0a010a80800863b600000000007a63941adc0000b70d5911006600024f80000000003d181fc00000020a8000a8c2560000000e666c90000cf000000026e1640b6c0000000000000000000029c00057202597acb440002a98f60eca0ba1ae0000f3617b405114ce920b53821754ec600026912b89fc000000000092c0003ae066ca8648600b0dd05c26354150000528660000000000000000011b8cf400032b00003d272c0001ad906c3952248a0c3ac4e112e8e001444350001f9c0a64d912c830cd625fa0001a786ea000153970c5720000db0a900a03253be9f5102a63800004d82e40000001eb4f52000000116c4bc5be000189400006a35706c893c5dc00001d800000000016eceea3da3c91c5c4b40001bc13082940002521578c8c7e4000000000000006694d89ec000000000010019604c000026e5060001e40000000000011818461a0ee0000c44000000000035a0000000ef4f0e2eb1348000000180000000091e73a277099400201201001200000800000001e01400c00a00200800c00000e00801800800001000201e00000e01200800e00000000400002000a02801001800000400000000401400001600400e00000201600002c00c00000400400c00001400201000200400600403c00000602000a00400001400000201200600800800400a01603e00601e00200c00201801c00000000200203a00200c00400000600200000800004200400800600000201c00000000a01200a00000000803000000000e00800800200600001600000600001c00000801400000000a00000000400400000200000000200402800001001600000c00200000600000200600e03a00000000600000c00600a02600600c00600201200201e00600600200200000000200000000200200400000400600000c00000201e00600e00800000000000002c00200200600802000201200001400600004e00000000000800200600600200400400000e02800400201000202800200401400200200001c00001e03000000200400201400001200000000000402a00a00000600200202400000400000400e01a00000000200400600000600400403000000400200802e00001201c00001206800000c05400000000800200600006e00200000000000a02000200000000a01602c00200200000000600000400200202000800600200200800400000600804c00000000400001001200000000001600400002200000800800601e05400002000000200200004001c00200400400000000800400200000000400c01a02e01000400604c
  | 11 => 0x1a58b300005f72750564f228253f817a801e04913312a00007703ae8ff422408d4179b54f140000f70000ca46f80000000c6050a3050ca074239b0f5981c0006591e0203cacc5c433f062c5de0d70001608c7c70a10780001de4580001ec83aa75123780000004bc3e3078854046713600002266102be8a1884002c1b80b9869e61839b86f40006671528f3021a3ad00108c800027d0921dec0006aa00007100001600b31a0430e3c214a84880be5071f18d10dd27b52d30be41243710cf08a4b3668d34a000072c1040410b6082e6af3e0936800000034f9d00ea03bf36b00000700a80119f54e965d200000005865251ee800047866c09198d03286ed2fa0000f023350929ad46363b1203000000000024506244362710d703ec89a00025d164c58c03c0cc9c2c30c0000e980000004ff1011aa4e340e10001b8900c7992300e405be40b19017bc53e00021e00000002ae35e80006e42e03d614a0e280000871d805566913f491745a82090bb0bf89285031598dcc06244018f00ac9ba2ec07b97b00a45773cb83a0ad047a3ca98d88e41ca03a0428fdc6ba39a0d58b1435d19816680006b432c18c448215b3f585c442e6cb2518d2821e5a00000468b7a0000000e0ccee22f06c80000000000000f500000000000d5c18e0001541cbc72e3061bb20783780003a19f682700001658000132729214170833a0003b70e98a7244a36701500bc5dd31d9ac85e48012870c98e5a4ad2728bccdf463f3c7014492a7e831016fcbbe4760a620b873a51f3fb9ae0db420e0000c0c1da00000016f0000000000069cf766e81d715cc0002b240a1dccd8036c2aa0104000000258800000016b22284a80000cf09c891849260e1b480000000003b5849ce3838f27606e00001e4138000074e02500016d00000001fc05883a025f0f893546f40000001784a3a4d00019d980000000321fd8fb2644180937c87a6c21f3800000040f2ca80009f440a26280000000003dd00000007fb2be1350e420002d692c8a364cc000206d0243610ad1e189ce1ac32e01f41582643841afc0002441be8474000000000000027e26000c1c14000000000094400004a00020580002ca0001a98cf838b000000087c3b3155000000000036087b40000001d19ec000003606891e09da085000163049a0003be06544f642f2f70c9c28c1ea00015380005a50001ae40d20d512900000005420001fa8c5427704d80b41686fd1270fd400041e1e68550b8a72304a08342f029a076120464856406d0d382d059c0000bd8b982f70000e60ac075b1c1107c00051826400003ce6a500017280c000011c800091c1f239e129c0480000000b0400060c0000000000000000000013c7851f8169c0003c10001e9001478b00011f8e5c3ee2f98000c985090000ef861c0002188c648cc3020b6165
  | 12 => 0x86ca55a3f293f0b067240da81844260f33db0000db80a100000000007d639c151c9a60352b5953487471830e0d604a850f2ab902500e0c42789de07186c311d927422c3662ec8c8c4d48260a710a42f23e52d20000a181ba0000ddc3b400000018bcc9a04e30b000000062141100000000001d000000007611c0984ca483e933f89a080800000000010320000670000f6600024d000000005b00000007f4156000076058e42c2b695a8c1600025a8000dec00026380005ea79d3878a382784363c181c48bc2030c680000005673131c009ae096227030463e2d10d98bb47ae2f42f3837441408b0b29bc8d3042100003a40007b73fa9d608e6000000157c71a32d3951f38cda0ad27c88c06981e03fe03d042801a24482a87fc280022171c2167551a90b100003aa1e28000a820000000000000000000000000000000003180000000000aecb1c4633330fcc00048227a1a406380001a99ffcf104542db8000f8815807f87f40002073678000a640e61e704500000000b7008425c38723487d48d829e3cd1fd10164770ed801c7c80000391d48a0a2e50001d3000081f2a91b4cd8c4f229a9ba8c000000000ebc0000000d401b455a28d2c88a4c916056000024c06077226884bc68618208a9a74de607708192147a257e0e09f804501500ec81c00cc6cc01b9af000052234b86d0a601d116b993c2400843e6967c0007d33f687e400000000017440000000ba118400018a0471524000000000000044400015d0000a7433301d9e50bfa2af10d000000076c27214a8c241a51ef90301f40222ae1b14000000419800000049c1560fe453a6e11bf04840005400001f7c0008303ef18441186870000e20b2455941b8000d7c1a32461a201482bd1781b50b122ea1891fbce886bb1720a8cc0478f1d20c144ce6480a387f8fd82f11a10c4c00052d0fb0000e7a4793898724b9e6690378f5410c63c2670c34dba19f00e0a0861836b3568d2049e37b1138920fc61083cf96acb8222d08112a82527a83aa121c78c00012812842d24e60a8906c07e0002ff124814a6862b100009921c200006ec0f866129e1a0c83005d0cc0188fba00032f0c1c15e000098153c0005b20fd0c1000080425c12d084e00019d0000000000000204c00000000005100000781398000dcc2bc0ea02c86da39c00000001986890698000e0e6e023409289e612b1b50bf000036e000000061424700004a000013114c08fc71c30b143904051e1613bb9ef49087f121a05c0d8e6753a314080b81ce0f60b646de35a00905bcb581c30e4098440a1a103401f80c66a208c110400064523f989c0004030001f6000056c0000cd800000011a95a400001d38300d01be58507e0000b4669910e13e0e1228a3bd188c3060003e39fe84c47cf000186c5020c93b3800000000011b0000ce664
  | 13 => 0x1016e00bc362716200161c02600021200005a653d00019c87c21570061a00000000002000056a0003b21d34bca4331a29b78b00193000113cb3c11e17d149cb6200008288a865e0001b18000f68000015000000007510b000029a0f60000af800029728a80007b654c1ac997400072b000020c0007311b2071831e59929002acf7242a03388f412e51208b955800082708f99d80002853860000d42000032816004e38624180000000003eb8000292000000172400000000020e4c2a793232000000080022a901c0002b737197c00005f6000180ce4e000369000058a5970000000a7c0003f3002c7704470641df8a3c14f2880000c9407a410087cf5c7aa00011ec0006743dc1bdcaea2b418e9fcc0740001dd9aa03966330001f70732000000000036e0001041ff41ce000177088017e51c0ef12fc0000002ff806400000030b800069a65a01f0a7017800023819380004390f0976092075714487144ea73038687cc54c04d0001e30c280000000f48e6c5db0001e78b1a0481189d142bc6432ad83402180001ee005000000036680000007f23d39a2c8446b015b00007867103ed9efcc0c2371fd9a9c00000000000004fc79c1cf206000000000002b80003211a800007140001c991d000000000007ec4c66282f415c00000003ac8f3cc3c46b2e3006cd1c44c000000088c00600006987605583e10000524456000000000035100019ecdd67af11c1d5800000026b0a6d01c5de31b92bc2c617d2c780004f400014400002a60002971924ff069c28880002ea00016700005fe0003e918accaa0000000000e9440127415e03a40002089c74f121df3a39da40003f20148d780006790690ca8b5e07900011b41ac65f13f95404845fb38880004220002f900001e211b00000005aa46a24680000001f40000df01380002cc000000000033c207400078416006306a868f29982cd02e8323e19dbca5633102aa0e08864e91f101ac8b8000319000043031806e18645d20f81de0000000000000000074a5e940120ecddc02e1aa8d1ce406630ff89e028a7ca2aa90ec3f80002561b600000002528884df600000f800017624b00002740008341f518f4458000000041c5428052211b6c7fe49939d9520ca65d33389dc4b3a081020108c9760000001cc8d5666e3bf92dd0620012c40b583ca1b000005a80003f12ba1acc7ee41a0000f104985aa0000ea40007e10000000a6842e2d9a0b4d905862e700009c400000000006640002eb1f14a7e00005c00007284b010c94c48900f904f9700dca77600000003720000001144d885172f1133c00000030400000006620001164dde5440cd17e0ebc31016e9d045a03111841c544da30938700405bc0000001a800001cd20e0e14c5a4a228c91f00006ff0000ed000029605b0be017225320c9eac6584cb13c9a
  | 14 => 0x81c66425590ac7cc81a09e8ae0b7238930fa0440e64ca3a9a0907de5ed1489310ca826e00000005b463933400000003492098bf460000010203903087c9117179898267d41605482120003d88d808a05e021f85b4a7069b304800067052306280000007d10000a301fa60f10e84406ce1f71218d6c000000000000000076a238847096c01504809003ae00500004640000003c100000000000000000ade00034b20a0f7800000013d43de498000178cf985141b10fd00002840f413ec00000000000007bc11137380010745d0000000011000037e1db4b967fe20e8000c5c5b02a2996cef22c23498f585d00001f69d388105f50041f20e4478d16408183ba1a20000aa400000000b8000e0257f2e69be40000e50e780000000e018d15ec00041638f000062c2011a3082c09e48818b88ac8ea7034109e5837c742000000020c2e328b1c941d401e000038c3cc5133cc05f88ae3d013a078ce6a05a000172000049100004e88be5ba25480006827122181790ca268a05f023c00054a1e396a412a0003120b6c44c00002b8404c5853b28580000001730001ef87564a0000028c3f0000137896c67a00000000007442723650f240000003d28640aba56109d9b909e04373258ce4de81f00000000f445210001c984b81a410f12cc7220fe20a0ff000004c38d9c0867c3b50c9109892e0a601c8ec80000000ce000000060406009d8ee81810a11b7c8fa1cc0d482c0c52000166859c89619717d82f4f400000d019ac0000000000388268000000000000000000000f4d186fe2c5a0249c615c00006380000003e005e81a800000014b038e1770549834f0037f194811c00023e240000000000012b8cfc84a61d0658840bb428b07814000d80003210b241621353428228000000249a03087000000012e4aa200038f9a90dea0001bc9298ebe69537800009ee0000df8e7cff200019100004660000000830cae2580001d20f9600000000000000eb2eb90348ca000000000059e02831d00010380ca0990ee82865081eca0a401a4e029788d0eb46d70191a1073432b32804f8adc6d02b293bc8045f903da0f09b08030b210c8b5c2900a41188b423b700000984242b141a836c4f80f20a0855479004500004cc00052622d136c7c0596261810835e76804d0a880003923519a68ba80d800020345c45b83e810487ec4c00af8f2cae26d933815e875864109605fcfc41c019b9c641223b91af9bc4b6a3ca1e9991c0002bf0000d00e7c6ac00000003547a139c914844674f2808c5044a10000013ac0000002868c542ba69221699a8a6e5041f603b89fa12d266958c01c4de1f597c50564bd0448000ec466f0000ac000006e0000e105ce19111205f0da2601135802498c5790a0208c97c8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7694c1003ede6394c10006dd6394c100075f5394c10004ff7654c10004fe7654c10004fd7654c10004fc7654c100467e6554c100067d6554c1003ede6354c10006dd6354c1003cff7614c10004fe7614c10004fd7614c1003cfc7614c10025be7414c10005bd7414c1001dee7214c10005ed7214c10004fd76d4410004ff7694410044fd76944100467e65944100067d6594410007775194410005fa7094410005f97094410004ff7654410005df7354410005dc7354410005ef725441001dec7254410044ff7614410004fd76144100467e65144100067d6514410025be7414410005bd7414410005fa7014410005f97014410004fd76cc41001dee72cc410005ed72cc410004ff768c41003cfd768c41003ede638c410006dd638c410005fa708c410005f9708c410004ff764c41003cff760c410004fd760c41003ede630c410006dd630c410005fa700c410005f9700c410004fd76d4010025be74d4010005bd74d4010004ff7694010044fd76940100467e65940100067d6594010005f67194010005f57194010004ff7654010044ff7614010004fe7614010004fd7614010044fc76140100467e65140100067d6514010005f67114010005f57114010004fd76cc010004ff768c01003cfd768c01003ede638c010006dd638c010005f6718c010005f5718c010004ff764c0100057f754c0100057c754c010005bf744c010025bc744c01003cff760c010004fe760c010004fd760c01003cfc760c01003ede630c010006dd630c01001dee720c010005ed720c010005f6710c010005f5710c010036f576c4010206f764c4010206f564c40102077754c40102077554c40101ffd732c40101ffd532c40101e5f571840101def6618401001df9768401002ef9768401000cf976840101f77b54840101f77954840101eefb62840101eef962840101efdb32840101efd932840101e5f971840101defa6184010007f26184010004ff76440100057f75440100057c7544010005bf7444010025bc7444010005df7344010005dc7344010005ef724401001dec7244010005f77644010006f77644010004f77644010007777544010007747544010007b774440101c7b474440101c6f764440101c6f564440101c77754440101c7755444010007d77344010007d47344010007e772440101bfe472440101bfd732440101bfd532440101d5f770440101cef66044010007f25044010007f15044010005fb7644010006fb7644010004fb76440100077b7544010007787544010007bb74440101c7b874440101c77b54440101c7795444010007db7344010007d87344010007eb72440101bfe872440101befb62440101bef962440101bfdb32440101bfd932440101b5fb7144010007f371440101aefa6144010007f26144010007f25144010007f15144010
  | 1 => 0xc1100067f650c1100067c650c110006bf640c110076bc640c110006df630c11003edc630c11004dee720c110005ed720c110006ef620c11006eec620c110007d9300c1100067f65c41100067c65c4110006bf64c4110066bc64c4110006df63c4110006dc63c4110006ef62c4110036ec62c41100077b65c41100077865c4110007bb64c4110227b864c41102277b54c41102277954c4110007db63c4110007d863c41101adfb72c41101adf972c4110007eb62c411022fe862c411022fdb32c411022fd932c4110227f241c4110227f141c41100067f65841100067c6584110006bf648411005ebc6484110006df6384110006dc6384110006ef628411002eec628411004df6768411000777658411000774658411021df7748411021df57484110007b76484110217b46484110217775484110217755484110007d76384110007d46384110007e7628411020fe4628411020fd7328411020fd53284110007f3608411020ff2208411020ff12084110004ff74d9410014fe74d9410004fd74d9410014fc74d94100067f54d94100067d54d941003cfe73d9410004fd73d9410004ff72d941000cfe72d9410004fd72d941000cfc72d9410006df32d9410006dd32d9410004fe71d9410006f671d9410004fe70d9410006fa70d9410004fd76994100067f6599410044ff76594100067f7559410004ff7459410014fe7459410004fd7459410014fc74594100067f54594100067d5459410004ff735941003cfc7359410004ff725941000cfe7259410004fd725941000cfc72594100067f52594100067d5259410006df3259410006dd3259410044ff7159410044fd7159410044ff7059410044fd70594100467e65194100067d6519410025be7419410005bd7419410005de7319410005dd731941001dee7219410005ed7219410044fe75d8c10004fd75d8c10004ff74d8c10014fe74d8c10004fd74d8c10014fc74d8c100067f54d8c100067d54d8c10004ff72d8c1000cfe72d8c10004fd72d8c1000cfc72d8c10006df32d8c10006dd32d8c10004fe71d8c10006f671d8c10004fe70d8c10006fa70d8c10004fd7698c10006df6398c1003cff7658c10004ff7558c10044fc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10006df7358c10006de4358c10006dd4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c10006df3258c10006dd3258c1003cff7158c1003cfd7158c1003cff7058c1003cfd7058c100057e7518c100057d7518c10025be7418c10005bd7418c1003ede6318c10006dd6318c1001dee7218c10005ed7218c10044ff76d4c10004fe76d4c10004fd76d4c10044fc76d4c100467e65d4c100067d65d4c1003cff7694c10004fe7694c10004fd7694c1003cf
  | 2 => 0x4fe76d45100067f65d45100467c65d4510006bf64d4510166bc64d4510006df63d4510006dc63d4510006ef62d451015eec62d4510005fa70d4510005f970d4510004fe76945100067f65945100467c6594510006bf6494510156bc6494510006df6394510006dc6394510006ef629451013eec6294510044fc76545100067f65545100467c6554510006bf645451014ebc6454510005df7354510005dc7354510006df6354510006dc6354510005ef725451004dec7254510006ef6254510146ec6254510005fb7054510005f87054510004fe76145100067f65145100467c6514510055be7414510005bd7414510006bf6414510136bc6414510006df6314510006dc6314510006ef621451012eec6214510007755114510004fe76cc5100067f65cc5100067c65cc510006bf64cc510126bc64cc510006df63cc51003edc63cc51004dee72cc510005ed72cc510006ef62cc51011eec62cc510005fa70cc510005f970cc510004fe768c5100067f658c5100067c658c510006bf648c510116bc648c510006df638c51003edc638c510006ef628c5100feec628c51003cfc764c5100067f654c5100067c654c510006bf644c51010ebc644c510006df634c51003edc634c510006ef624c510106ec624c510005fb704c510005f8704c510004fe760c5100067f650c5100067c650c510006bf640c5100f6bc640c510006df630c51003edc630c510006ef620c5100eeec620c510004fe76d41100067f65d41100467c65d4110055be74d4110005bd74d4110006bf64d41100e6bc64d4110006df63d4110006dc63d4110006ef62d41100deec62d4110005f671d4110005f571d4110004fe76941100067f65941100467c6594110006bf64941100d6bc6494110006df6394110006dc6394110006ef62941100beec6294110044ff7654110004fd7654110044fc76541100067f65541100467c6554110006bf64541100cebc6454110006df6354110006dc6354110006ef62541100c6ec6254110005f77154110005f47154110004fe76141100067f65141100467c6514110006bf64141100b6bc6414110006df6314110006dc6314110006ef62141100aeec6214110004fe76cc1100067f65cc1100067c65cc110006bf64cc1100a6bc64cc110006df63cc11003edc63cc110006ef62cc11009eec62cc110005f671cc110005f571cc110004fe768c1100067f658c1100067c658c110006bf648c110096bc648c110006df638c11003edc638c110006ef628c11007eec628c11003cff764c110004fd764c11003cfc764c1100057f754c1100057c754c1100067f654c1100067c654c110005bf744c110055bc744c110006bf644c11008ebc644c110006df634c11003edc634c110006ef624c110086ec624c110005f7714c110005f4714c110004fe760
  | 3 => 0xd5418d100065d5418d10006dc5418d1003edf7218d1003cdf7218d1003ede7218d1003edd7218d10004dd7218d1003edc7218d10006df5218d10006de5218d10006dd5218d10006dc5218d10006df4218d10006de4218d10006dd4218d10006dc4218d1003edf7118d1003edd7118d10006df4118d10006de4118d10006dd4118d10006dc4118d10006df2118d10006de2118d10006dd2118d10006dc2118d1003edf7018d1003edd7018d10006df4018d10006de4018d10006dd4018d10006dc4018d10006df2018d10006de2018d10006dd2018d10006dc2018d10006dd1018d10044ff76d4d10004fe76d4d10004fd76d4d10044fc76d4d100067f65d4d100467c65d4d10006bf64d4d101a6bc64d4d10006df63d4d1003edc63d4d1019eec62d4d1003cff7694d10004fe7694d10004fd7694d1003cfc7694d100067f6594d100467c6594d10006bf6494d10196bc6494d10006df6394d1003edc6394d100075f5394d1018eec6294d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100467c6554d10006bf6454d10186bc6454d10006df6354d1003edc6354d1017eec6254d1003cff7614d10004fe7614d10004fd7614d1003cfc7614d100067f6514d100467c6514d10055be7414d10005bd7414d10006bf6414d10176bc6414d10006df6314d1003edc6314d1004dee7214d10005ed7214d1016eec6214d10005f67114d10005f57114d10005fa7014d10005f97014d1004dee76d891004eee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d89100076f54d89100076d54d8910007cf73d8910007cc73d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e641d8910007e541d8910007eb70d891004fe870d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d89100066f54d8910006ee54d8910006ed54d89100066d54d8910006ec54d8910006ef73d8910006cf73d8910006ee73d8910006ed73d8910006ec73d8910006cc73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891004eee71d891004eed71d891004eec71d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef70d891004eee70d891004eed70d891004eec70d8910006ef40d8910006ee40d8910006ed40d8910006ec40d891004eed10d8910
  | 4 => 0x8d100079c64d8d100069c64d8d100075f54d8d100075d54d8d10005df72d8d10005dd72d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d10007d641d8d10007d541d8d10007da20d8d10007d920d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d100065d54d8d10006dc54d8d10006df72d8d10004df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d10006dd71d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d10006dd70d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d100057e7598d100057d7598d100067f6598d100067c6598d10055be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d1004dee7298d10005ed7298d10006ec6298d100057f7558d100057c7558d100067f6558d100067c6558d10005bf7458d10055bc7458d10006bf6458d10006bc6458d10005ef7258d1004dec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d10044fc7558d100067c7558d100447c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d10006df3258d10006dd3258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1003ede6318d10006dd6318d10006ec6218d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d100075d5418d10005df7218d10005dd7218d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d10007d64118d10007d54118d10007da2018d10007d92018d1003edf7518d1003ede7518d1003edd7518d1003edc7518d1003edf7418d1003ede7418d1003edd7418d1003edc7418d10006df5418d100065f5418d10006de5418d10006d
  | 5 => 0x67e62195100067d62195100067c62195100076c62195100066c62195100075f32195100075d32195100077641195100077541195100077a20195100077920195100467f74195100447f74195100467e74195100467d74195100047d74195100467c74195100467f73195100467e73195100467d73195100467c73195100067f43195100067e43195100067d43195100067c43195100467f72195100467e72195100467d72195100467c72195100067f42195100067e42195100067d42195100067c42195100067f32195100065f32195100067e32195100067d32195100065d32195100067c32195100467f71195100467d71195100067f41195100067e41195100067d41195100067c41195100067f21195100067e21195100067d21195100067c21195100467f70195100467d70195100067f40195100067e40195100067d40195100067c40195100067f20195100067e20195100067d20195100067c20195100067d1019510055be76d9110056be76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d91100079f32d91100079d32d9110007b771d9110057b471d9110007ba20d9110007b920d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d91100069f32d9110006be32d9110006bd32d91100069d32d9110006bc32d9110006bf71d9110056be71d9110056bd71d9110056bc71d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d9110056be70d9110056bd70d9110056bc70d9110006bf20d9110006be20d9110006bd20d9110006bc20d9110056bd10d911003cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10006ec62d8d10044fe75d8d10004fd75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006df32d8d10006de32d8d10006dd32d8d10006dc32d8d1003cfe71d8d1003cfc71d8d1003cfe70d8d1003cfc70d8d1003cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d
  | 6 => 0x732c4210237d532c4210005f976c4210006f976c421023f7b54c421023f7954c42101ddfb72c42101ddf972c4210237db32c4210237d932c4210044fe76d9510006bc64d9510006ec62d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100067f54d95100067e54d95100067d54d95100067c54d951003cfe73d9510004fd73d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100067f52d95100067e52d95100067d52d95100067c52d9510006df32d9510006dd32d9510044fe71d9510044fc71d9510044fe70d9510044fc70d95100447e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100075f32d95100075d32d95100077641d95100077541d95100077a20d95100077920d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100065f32d95100067e32d95100067d32d95100065d32d95100067c32d95100067f71d95100067d71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95100067d70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067e20d95100067d20d95100067c20d95100067f6599510055be7499510005bd7499510006bc6499510005de7399510005dd739951004dee7299510005ed7299510006ec6299510005bf7459510055bc7459510006bc6459510005df7359510005dc7359510005ef725951004dec7259510006ec62595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc74595100067f54595100067d5459510004ff7359510006df7359510004df735951003cfc7359510006dc735951003cdc7359510004ff7259510006ef7259510004ef725951000cfe7259510004fd725951000cfc7259510006ec725951000cec7259510006df3259510006dd3259510004ff7159510006f77159510004ff7059510006fb7059510004fe76195100467e65195100067d6519510006bc6419510006ec62195100057e76195100067e76195100047e76195100057f74195100057d74195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067f6219510
  | 7 => 0x961000cfe72d9610006ee72d961000cee72d9610004fd72d9610006ed72d9610004ed72d961000cfc72d96100067f52d96100067d52d9610006df32d9610006dd32d9610006f571d9610006fa70d9610004fd76996100067f659961005dbe7499610005bd7499610044ff76596100067f7559610004ff7459610014fe7459610004fd7459610014fc74596100067f54596100067d5459610004ff735961003cfc7359610004ff725961000cfe7259610004fd725961000cfc7259610006df3259610006dd32596100467e65196100067d6519610044fe75d8e10004fd75d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e100067f54d8e100067d54d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006df32d8e10006dd32d8e10006f571d8e10006fa70d8e10004fd7698e10006df6398e1003cff7658e10004ff7558e10044fc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e100067f5458e100067d5458e10006df7358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e10006df3258e10006dd3258e1003ede6318e10006dd6318e1002dee7218e10005ed7218e10044ff76d4e10004fe76d4e10004fd76d4e10044fc76d4e1003ede63d4e10006dd63d4e1003cff7694e10004fe7694e10004fd7694e1003cfc7694e100075f5394e10004ff7654e10004fe7654e10004fd7654e10004fc7654e1003cff7614e10004fe7614e10004fd7614e1003cfc7614e1005dbe7414e10005bd7414e1003ede6314e10006dd6314e1002dee7214e10005ed7214e10005fa7014e10005f97014e100467e65d46100067d65d4610005fa70d4610005f970d46100067f65946100467c6594610007775194610044ff76546100467e65546100067d6554610005df7354610005dc7354610005ef725461002dec7254610005fb7054610005f870546100067f65146100467c651461005dbe7414610005bd741461003ede63cc610006dd63cc61002dee72cc610005ed72cc610005fa70cc610005f970cc610006df638c61003edc638c61003cff764c61003ede634c610006dd634c610005fb704c610005f8704c610006df630c61003edc630c61005dbe74d4210005bd74d4210044fd76942100467e65942100067d6594210005f67194210005f571942100467e65142100067d6514210005f67114210005f5711421003cfd768c21003ede638c210006dd638c210005f6718c210005f5718c2100057f754c2100057c754c210005bf744c21005dbc744c21003ede630c210006dd630c21002dee720c210005ed720c210005f6710c210005f5710c210007d9300c210005f576c4210006f576c421023ef764c421023ef564c421023f7754c421023f7554c4210237d
  | 8 => 0x4ff735971003cfc7359710004ff725971000cfe7259710004fd725971000cfc72597100067f52597100067d5259710006df3259710006dd32597100467e65197100067d6519710065be7419710005bd74197100057e75d8f100057d75d8f10065be74d8f10005bd74d8f10044fe75d8f100067e75d8f100447e75d8f10004fd75d8f100067d75d8f100047d75d8f10004ff74d8f10014fe74d8f10006be74d8f10014be74d8f10004fd74d8f10006bd74d8f10004bd74d8f10014fc74d8f100067f54d8f100067d54d8f10006de43d8f10006dd43d8f10004ff72d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006df32d8f10006dd32d8f10006f671d8f10006f970d8f10004fd7698f10006df6398f10035ee7298f10005ed7298f1003cff7658f10004ff7558f10044fc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10006df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f10006df3258f10006dd3258f1003ede6318f10006dd6318f10044ff76d4f10004fe76d4f10004fd76d4f10044fc76d4f1003cff7694f10004fe7694f10004fd7694f1003cfc7694f100467e6594f100067d6594f100075f5394f10004ff7654f10004fe7654f10004fd7654f10004fc7654f1003cff7614f10004fe7614f10004fd7614f1003cfc7614f100467e6514f100067d6514f10065be7414f10005bd7414f10035ee7214f10005ed7214f10005f67114f10005f57114f10044fd76947100467e65947100067d6594710005fa7094710005f97094710005df7354710005dc7354710005ef7254710035ec72547100467e65147100067d6514710065be7414710005bd7414710007755114710005fa7014710005f97014710035ee72cc710005ed72cc71003cfd768c71003ede638c710006dd638c710005fa708c710005f9708c71003ede630c710006dd630c710005fa700c710005f9700c7100467e65d43100067d65d4310065be74d4310005bd74d4310005f671d4310005f571d43100067f65943100467c6594310044ff76543100467e65543100067d6554310005f77154310005f471543100067f65143100467c651431003ede63cc310006dd63cc310005f671cc310005f571cc310006df638c31003edc638c31003cff764c3100057f754c3100057c754c310005bf744c310065bc744c31003ede634c310006dd634c310005f7714c310005f4714c310006df630c31003edc630c310035ee720c310005ed720c310005de73d9610005dd73d961002dee72d9610005ed72d9610004ff74d9610014fe74d9610004fd74d9610014fc74d96100067f54d96100067d54d961003cfe73d9610006de73d961003cde73d9610004fd73d9610006dd73d9610004dd73d9610004ff72d
  | 9 => 0xe7598430004fd7598430004ff7498430014fe7498430004fd7498430014fc74984300067f54984300067d5498430004ff729843000cfe7298430004fd729843000cfc729843003edf3298430006dd329843003ef67198430006f64198430006f5419843003ef7319843003ef43198430004ff7558430044fc7558430004ff7458430014fe7458430004fd7458430014fc74584300067f54584300067d5458430004ff725843000cfe7258430004fd725843000cfc725843003edf3258430006dd325843003ef77158430006f64158430006f5415843003ef7315843003edc315843003ef43158430044ff76d443003cfe76d4430004fd76d44300467e65d44300067d65d443003dde73d4430005dd73d443015eee62d4430006ed62d4430004ff769443003cfe7694430004fd769443013eee6294430006ed6294430006f66194430006f56194430004ff7654430004fd765443003cfc76544300467e65544300067d6554430005df735443003ddc7354430005ef725443006dec7254430146ee6254430006ed6254430006f66154430006f56154430044ff761443003cfe7614430004fd7614430075be7414430005bd741443012eee6214430006ed621443003ddd768c430006dd768c430286de658c43003edc658c43003edf648c43027edd648c43027f5f548c43027f5d548c430275df728c430275dd728c43003edf628c43003fce628c43026edd628c43003fcd628c430006cd628c43003dde718c43003fd6718c430006dd618c430005dd708c430266de608c43003fda608c430004fd76d4030075be74d4030005bd74d40300deee62d4030006ed62d4030004ff7694030044fd76940300467e65940300067d659403003dde7394030005dd73940300beee6294030006ed6294030004ff76540300c6ee6254030006ed6254030044ff761403003cfe7614030004fd761403003cfc76140300467e65140300067d651403003dde7314030005dd73140300aeee6214030006ed621403003ddf764c030006df764c030004df764c0300075f754c0300075c754c0300079f744c03025f9c744c03003edf644c03025edd644c03025f5f544c03025f5d544c030255df724c030255dd724c03003edf624c03003fce624c03024edd624c03003fcd624c030006cd624c030005dc714c03003ddf704c03003fdb704c030246de604c03003fda604c030004ff74d9710014fe74d9710004fd74d9710014fc74d97100067f54d97100067d54d971003cfe73d9710004fd73d9710004ff72d971000cfe72d9710004fd72d971000cfc72d9710006df32d9710006dd32d9710006f671d9710006f970d9710004fd76997100067f6599710044ff76597100067f7559710004ff7459710014fe7459710004fd7459710014fc74597100067f54597100067d5459710
  | 10 => 0x4530006bf6494530156bc6494530004ff7654530004fe7654530004fc76545300067f65545300467c6554530006bf645453014ebc6454530005df735453003ddc7354530005ef7254530085ec7254530004fe7614530004fd7614530044fc76145300067f65145300467c651453008dbe7414530005bd7414530006bf6414530136bc641453003dde7314530005dd7314530005fa7014530005f970145300067f658c5300067c658c530006bf648c530116bc648c530006f7618c530006f4618c530005fa708c530005f9708c5300067f654c5300067c654c530006bf644c53010ebc644c530006f7614c530006f4614c530005fb704c530005f8704c53003fd8304c53003cfe76d413003cfc76d41300067f65d41300467c65d413008dbe74d4130005bd74d4130006bf64d41300e6bc64d413003dde73d4130005dd73d4130004fe76941300067f65941300467c6594130006bf64941300d6bc64941300077b5094130044ff7654130004fd765413003cfc76541300067f65541300467c6554130006bf64541300cebc6454130005df735413003ddc7354130004fe76141300067f65141300467c6514130006bf64141300b6bc64141300067f658c1300067c658c130006bf648c130096bc648c13003dfa708c13003efb608c1300075f658c1300075c658c13029ddf748c13029ddd748c1300079f648c1302979c648c1302975f548c1302975d548c130245df728c130245dd728c13028edf628c13028edd628c130006dc618c13003dde708c13003edf608c13003fdb608c13003e7f7559430004ff7459430014fe7459430004fd7459430014fc74594300067f54594300067d545943003cff735943003cfe735943003cfd735943003cfc735943003e7e535943003e7c5359430004ff725943000cfe7259430004fd725943000cfc725943003edf3259430006dd3259430004ff7159430004fc7159430006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef54588300066f5458830006ee5458830006ed54588300066d5458830006ec545883003eef735883003eee735883003ece735883003eed735883006ecd735883003eec735883003eef535883003eee535883003eed535883003eec535883003eef435883003eee435883003eed435883003eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef4158830006ee4158830006ed4158830006ec415883003eef315883003eee315883003eed315883003eec315883003ecc315883006eef7058830006ee705883006eed705883006eec7058830006ef4058830006ee4058830006ed4058830006ec405883003eef305883003ecf305883003eee305883003eed305883003eec3058830044f
  | 11 => 0x467d70195300067f40195300067e40195300067d40195300067c40195302ae7f30195300067d30195302ae7c30195300067f20195300067e20195300067d20195300067c201953008dbe76d913008ebe76d9130014be76d91300073f75d91300073c75d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91300079f73d913008f9c73d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300079f32d91300079d32d91302a7bb30d91302a7b830d9130006bf75d91300063f75d9130006be75d9130006bd75d9130006bc75d91300063c75d9130006bf73d91302a6be73d913008ebd73d91302a6bc73d91302a6be53d91302a6bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d91302a6bf32d91300069f32d9130006be32d9130006bd32d91300069d32d91302a6bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d91302a6bf31d91302a6bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d91302a6bf70d913008ebe70d913008ebd70d913008ebc70d91302a6bf30d913008ebd30d91302a6bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d9130004fe76d4d300067f65d4d300467c65d4d30006bf64d4d301a6bc64d4d3003f5e53d4d30005fa70d4d30005f970d4d30044fc7654d300067f6554d300467c6554d30006bf6454d30186bc6454d30005fb7054d30005f87054d300067f65d85300067c65d8530006bf64d8530006bc64d8530044fe75d8530004fd75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d8530004ff72d853000cfe72d8530004fd72d853000cfc72d8530006df32d8530006dd32d8530006f721d8530006f421d85300057e75985300057d75985300067f65985300067c659853008dbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300057c75585300067f65585300067c6558530005bf745853008dbc7458530006bf6458530006bc6458530005ef7258530085ec72585300067f65185300067c6518530006bf6418530006bc6418530006f56118530044fe7518530004fd7518530004ff7418530014fe7418530004fd7418530014fc74185300067f54185300067d5418530006de4318530006dd4318530004ff721853000cfe7218530004fd721853000cfc7218530006df3218530006dd3218530006f72118530006f42118530004fe76d4530004fd76d4530044fc76d45300067f65d45300467c65d4530006bf64d4530166bc64d4530004fe7694530004fd7694530004fc76945300067f65945300467c659
  | 12 => 0xe76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300075e43d95300075d43d95300067f62d95300067e62d95300067d62d95300067c62d95300075f32d95300075d32d95302b77b30d95302b77830d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d95300067f73d95302b67e73d95300067d73d95302b67c73d95300067f43d95302b67e43d95300067d43d95302b67c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95302b67f32d95300065f32d95300067e32d95300067d32d95300065d32d95302b67c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95302b67f31d95302b67c31d95300067f21d95300067e21d95300067d21d95300067c21d95302b67f70d95300067d70d95300067f40d95300067e40d95300067d40d95300067c40d95302b67f30d95302b67c30d95300067f20d95300067e20d95300067d20d95300067c20d95300067f659953008dbe7499530005bd7499530006bc6499530005bf745953008dbc7459530006bc64595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300067f54595300067d5459530004ff7359530006df7359530004ff725953000cfe7259530004fd725953000cfc7259530006df3259530006dd3259530004ff7159530004fc7159530004ff7059530006fb7059530004fe76195300467e65195300067d6519530006bc64195300057e76195300067e76195300047e76195300057f74195300057d74195300067f64195300067e64195300067d64195300067c64195300073c64195300063c64195300075e43195300075d43195300067f62195300067e62195300067d62195300067c62195300075f32195300075d32195302af7b30195302af7830195300467f74195300447f74195300467e74195300467d74195300047d74195300467c74195300467f73195300467e73195300467d73195300467c73195300067f43195302ae7e43195300067d43195302ae7c43195300467f72195300467e72195300467d72195300467c72195300067f42195300067e42195300067d42195300067c42195302ae7f32195300065f32195300067e32195300067d32195300065d32195302ae7c32195300467f71195300467e71195300467d71195300467c71195300067f41195300067e41195300067d41195300067c41195302ae7f31195302ae7c31195300067f21195300067e21195300067d21195300067c21195300467f7019530
  | 13 => 0x9630004ff7159630004fc71596300467e65196300067d65196300467e65d4e300067d65d4e3003f5e53d4e30005fa70d4e30005f970d4e30044ff7654e300467e6554e300067d6554e30005fb7054e30005f87054e3003fdb3054e30006f76198630044fe7598630004fd7598630004ff7498630014fe7498630004fd7498630014fc74986300067f54986300067d5498630004ff729863000cfe7298630004fd729863000cfc7298630006df3298630006dd3298630006f64198630006f54198630005ef725863007dec7258630004ff7558630044fc7558630004ff7458630014fe7458630004fd7458630014fc74586300067f54586300067d5458630004ff7258630006ef7258630004ef725863000cfe7258630004fd725863000cfc7258630006ec725863000cec7258630006df3258630006dd3258630006f64158630006f54158630006f56118630044ff76d4630004fe76d4630004fd76d463003dde73d4630005dd73d4630004ff7694630004fe7694630004fd7694630004ff7654630004fd7654630004fc7654630005df735463003ddc7354630005ef725463007dec7254630044ff7614630004fe7614630004fd7614630095be7414630005bd7414630005fa7014630005f97014630006f6618c630006f5618c630005fa708c630005f9708c630286de658c630286dc658c6302fedf648c6302fedd648c6302ff5f548c6302ff5d548c6302f5df728c6302f5dd728c630266df628c630266dd628c63003dde718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c63003ede608c630006f6614c630006f5614c630005fb704c630005f8704c630005dd760c63003edd760c6302eede650c6302eedc650c6302e6df640c6302e6dd640c6302e75f540c6302e75d540c63003ddf720c6302dddd720c6302d6df620c6302d6dd620c63003fd6710c630006dd610c630005dd700c63003fda600c630095be74d4230005bd74d423003cfd76942300467e65942300067d659423003dde7394230005dd73942300077b509423003cfd76142300467e65142300067d651423003dde7314230005dd7314230005dd76cc23003edd76cc2302cedf64cc2302cedd64cc2302cf5f54cc2302cf5d54cc23003ddf72cc2302c5dd72cc2302bedf62cc2302bedd62cc230005de71cc23003fda60cc230007da50cc230007d950cc230044fe76d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300067f54d95300067e54d95300067d54d95300067c54d953003cfe73d953003cfc73d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300067f52d95300067e52d95300067d52d95300067c52d9530006df32d9530006dd32d9530004fe71d9530004fd71d95300447
  | 14 => 0x57d758c4502875c538c450006f6618c450006f5618c450004ff764c450004fd764c450044fc764c4500057f754c4500457c754c45003ede634c450006dd634c450006f6614c450006f5614c45003cff760c450044fe760c450004fd760c4502ad7f750c4500457c750c45003edc630c4502af5c530c4500457f76540500067f76540500047f76540503257f74540503257d74540500467f64540503067d64540502ad7c735405031d7f725405031d7d72540503175f32540503175d32540500057c71540500457f70540500477b705405030e7e60540500477a60540503077b405405030778405405003e7f7559730004ff7459730014fe7459730004fd7459730014fc74597300067f54597300067d545973003cfc735973003e7e535973003e7c5359730004ff725973000cfe7259730004fd725973000cfc72597300067f52597300067d525973003edf3259730006dd3259730004ff7159730004fc7159730044fe7598730004fd7598730004ff7498730014fe7498730004fd7498730014fc74987300067f54987300067d549873003ede4398730006dd4398730004ff729873000cfe7298730004fd729873000cfc729873003edf3298730006dd329873003ef6719873003ef7319873003ef4319873003edc3098730004ff7558730044fc7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d5458730004ff725873000cfe7258730004fd725873000cfc725873003edf3258730006dd325873003ef7715873003ef7315873003ef43158730044ff76d473003cfe76d4730004fd76d4730004ff769473003cfe7694730004fd76947300467e65947300067d6594730004ff7654730004fd765473003cfc7654730005df735473003ddc7354730005ef725473009dec7254730044ff761473003cfe7614730004fd76147300467e65147300067d65147300a5be7414730005bd741473003dde7314730005dd73147300467e65d43300067d65d43300a5be74d4330005bd74d433003dde73d4330005dd73d43302b67f65943300467c6594330044ff76543300467e65543300067d6554330005df735433003ddc73543302ae7f65143300467c6514330004ff74d9630014fe74d9630004fd74d9630014fc74d96300067f54d96300067d54d9630006dd73d96302b67e53d96302b67c53d9630004ff72d963000cfe72d9630004fd72d963000cfc72d9630006df32d9630006dd32d9630004fe71d9630004fd71d9630006fa70d9630004fd76996300067f6599630095be7499630005bd7499630044ff76596300067f7559630004ff7459630014fe7459630004fd7459630014fc74596300067f54596300067d5459630004ff725963000cfe7259630004fd725963000cfc7259630006df3259630006dd325
  | 15 => 0x46194550005fa7094550005f97094550005df7354550005dc7354550005ef72545500c5ec7254550006f76154550006f46154550047745154550005fb7054550005f87054550004fe76cc550004fd76cc55003cfc76cc5500c5ee72cc550005ed72cc550004fe768c550004fd768c550004fc768c550006df638c55003edc638c550004ff764c550004fe764c550004fc764c550004fe760c550004fd760c55003cfc760c5500457e750c5500057d750c550006df630c55003edc630c550005fa700c550005f9700c550045fa7094150046fb60941503857f74941503857d749415037e7f649415037e7d64941502b67c63941503767f62941503767d62941503775f32941503775d32941500067c61941500457e70941500467f60941500477b6094150004ff7458c50014fe7458c50004fd7458c50014fc7458c500467f5458c500067d5458c50046df7358c50046df5358c500467c5358c50046dc5358c50006de4358c50006dd4358c50004ff7258c5000cfe7258c50004fd7258c5000cfc7258c50006df3258c50006dd3258c50004ff7158c50004fc7158c500457d7694c502ae7d7694c502ad7f7494c5036d7d7494c500467f6494c503667d6494c500457e7394c500475e7394c500467f6394c502ae7d6394c502ad7f7294c5035d7d7294c502af5f3294c503575d3294c500057e7194c500057d7094c502b67e6094c500477a6094c50004ff7498450014fe7498450004fd7498450014fc74984500467f54984500067d549845003cfe7398450004fd7398450004ff729845000cfe7298450004fd729845000cfc7298450006df3298450006dd3298450046f67198450046f75198450046f45198450006f64198450006f54198450006f62198450006f52198450004ff7458450014fe7458450004fd7458450014fc74584500467f54584500067d5458450004ff7358450006df7358450004df735845003cfc7358450006dc735845003cdc7358450004ff7258450006ef7258450004ef725845000cfe7258450004fd725845000cfc7258450006ec725845000cec72584500467f52584500067d5258450006df3258450006dd3258450046f77158450046f751584500467c5158450046f45158450046745158450006f64158450006f54158450006f62158450006f521584500457d76944500067d769445034d7f749445034d7d74944500467f64944503467d64944502ad7e739445033d7f729445033d7d72944503375f32944503375d32944500457e71944500477671944500067d61944500057d709445032e7e60944500477a609445003cff76cc450044fe76cc450004fd76cc4500457e75cc4500057d75cc45003ede63cc450006dd63cc4500adee72cc450005ed72cc450004ff768c450044fe768c450004fd768c4500457e758c450
  | 16 => 0x8650006dd3258650006f64158650006f54158650006f56118650006f66194650006f56194650047775194650005fa7094650005f970946503dd7f74946503dd7d74946503d67f64946503d67d64946502b57e73946503cd7f72946503cd7d729465032f5f329465032f5d32946500457e71946500077661946500067d61946500077561946500077a70946500057d70946500077970946500467e6094650005df7354650005dc7354650005ef72546500bdec7254650006f66154650006f56154650005fb7054650005f870546500057d76146500467d76146500457f74146500473e74146503c57d74146500473d74146500053d74146503be7f64146503be7d64146502b57e73146500457f72146503b57d72146503af5f32146503af5d32146500477671146500067d61146500057d70146500477a601465003cff76cc650004fe76cc650004fd76cc6500457e75cc6500057d75cc6500bdee72cc650005ed72cc650004ff768c650004fe768c650004fd768c6500457e758c6500057d758c65003ede638c650006dd638c6500075c538c650004ff764c650004fd764c650004fc764c6500057f754c6500457c754c65003cff760c650004fe760c650004fd760c6502b57f750c6500457c750c65003ede630c650006dd630c6502b75c530c650005fa700c650005f9700c6500057d76d42500467d76d42500457f74d42500473e74d42503a57d74d42500473d74d42500053d74d425038e7f64d425038e7d64d42502b57e73d42500457f72d425039d7d72d42503975f32d42503975d32d42500057e71d42500477a60d425038f7a40d425038f7940d4250004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500067f54d8d500067d54d8d50006df43d8d50006dc43d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d50006df32d8d50006dd32d8d50004fe71d8d50004fd71d8d50006df6398d50005bf7458d500cdbc7458d5003ede6318d50006dd6318d500c5ee7218d50005ed7218d50006df6394d5003edc6394d500475f5394d50005fa7094d50005f97094d5003cfc7654d50006df6354d5003edc6354d50005fb7054d50005f87054d50004ff74d8550014fe74d8550004fd74d8550014fc74d85500067f54d85500067d54d855003cfe73d8550004fd73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d8550006df32d8550006dd32d8550006f76198550005bf74585500cdbc7458550005df7358550005dc7358550005ef72585500c5ec7258550006f56118550004ff7418550014fe7418550004fd7418550014fc74185500067f54185500067d541855003cfe7318550004fd7318550004ff721855000cfe7218550004fd721855000cfc7218550006df3218550006dd3218550006f76194550006f
  | 17 => 0x4ff7498750014fe7498750004fd7498750014fc74987500467f54987500067d549875003cfe7398750004fd7398750004ff729875000cfe7298750004fd729875000cfc7298750006df3298750006dd3298750046f67198750046f75198750046f451987500467c5098750004ff7458750014fe7458750004fd7458750014fc74587500467f54587500067d5458750004ff735875003cfc7358750004ff725875000cfe7258750004fd725875000cfc7258750006df3258750006dd3258750046f77158750046f75158750046f4515875003cff76cc750044fe76cc750004fd76cc750126be64cc750006bd64cc7500ddee72cc750005ed72cc750004ff768c750044fe768c750004fd768c750116be648c750006bd648c75003ede638c750006dd638c750004ff764c750004fd764c750044fc764c75010ebe644c750006bd644c75003cff760c750044fe760c750004fd760c7500457e750c7500057d750c7500f6be640c750006bd640c75003ede630c750006dd630c750006df6398e50004ff7458e50014fe7458e50004fd7458e50014fc7458e500067f5458e500067d5458e50006de4358e50006dd4358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e50006df3258e50006dd3258e50004ff7158e50004fc7158e5003ede6318e50006dd6318e500bdee7218e50005ed7218e5003ede6394e50006dd6394e500475f5394e50005fa7094e50005f97094e502b57f7494e5041d7d7494e504167f6494e504167d6494e500457e7394e502b75e6394e502b67d6394e500075d6394e500065d6394e502b57f7294e5040d7d7294e502b75f3294e504075d3294e500057e7194e502b77a7094e500057d7094e502b7797094e50005797094e500467e6094e5003cff7654e5003ede6354e50006dd6354e50005fb7054e50005f87054e500477b5054e500057d7614e500467d7614e500457f7414e500473e7414e503fd7d7414e500473d7414e500053d7414e503f67f6414e503f67d6414e500475e7314e502b67d6314e500457f7214e500476e7214e503ed7d7214e500476d7214e500056d7214e502b75f3214e503e75d3214e500057e7114e500057d7014e500477a6014e50005de73d8650005dd73d86500bdee72d8650005ed72d8650006f76198650004ff7498650014fe7498650004fd7498650014fc74986500067f54986500067d549865003cfe7398650004fd7398650004ff729865000cfe7298650004fd729865000cfc7298650006df3298650006dd3298650006f64198650006f54198650004ff7458650014fe7458650004fd7458650014fc74586500067f54586500067d5458650004ff735865003cfc7358650004ff725865000cfe7258650004fd725865000cfc72586500067f52586500067d5258650006df325
  | 18 => 0x661d4c31005de70d4c31004fd76d443103ddc73d4431004ff7694431044fd76944310467e65944310067d659443103dde7394431005dd7394431004ff7654431005df735443103ddc7354431005ef72544310edec7254431044ff761443103cfe7614431004fd761443103cfc76144310467e65144310067d65144310f5be7414431005bd741443103dde7314431005dd731443103ddf764c431006df764c431004df764c4312edde754c4312eddc754c431445df744c431445dd744c43143f5f544c43143f5d544c431435df724c431435dd724c43103edf624c431426dd624c43103ddf714c43103fd7714c43142ede614c43103fd6614c431007d6514c431007d5514c431427d7214c431427d4214c431005dc704c431044fe7598031004fd7598031004ff7498031014fe7498031004fd7498031014fc74980310067f54980310067d5498031004ff729803100cfe7298031004fd729803100cfc729803103edf3298031006dd329803103efa7098031006fa4098031006f9409803103efb309803103ef83098031006fa2098031006f92098031004ff75580310067f75580310047f7558031044fc75580310067c75580310447c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc74580310067f54580310067d545803103ede4358031006dd4358031004ff725803100cfe7258031004fd725803100cfc725803103edf3258031006dd325803103efb7058031006fa4058031006f9405803103efb305803103edc305803103ef8305803103ed83058031006fa2058031006f92058031046bf7559350046be75593500463e7559350046bd75593500e63d7559350046bc7559350006bf7359350006be7359350006bd7359350006bc7359350046bf5359350046be5359350046bd5359350046bc5359350006bf7259350006be7259350006bd7259350006bc7259350046bf5259350046be5259350046bd5259350046bc5259350006bf32593500069f3259350006be3259350006bd32593500069d3259350006bc3259350006bf7159350006be7159350006bd7159350006bc7159350046bf5159350046be5159350046bd5159350046bc5159350006bf2159350006be2159350006bd2159350006bc21593500e6bf70593500e6be7059350006bd70593500e6bc7059350046bf5059350046be5059350046bd5059350046bc50593500463c5059350006bf2059350006be2059350006bd2059350006bc2059350004ff7458f50014fe7458f50004fd7458f50014fc7458f500467f5458f500067d5458f50046df7358f50046df5358f50046dc5358f50004ff7258f5000cfe7258f50004fd7258f5000cfc7258f50006df3258f50006dd3258f50004ff7158f50004fc7158f50
  | 19 => 0x9531004fd74d9531014fc74d95310067f54d95310067d54d9531004ff72d953100cfe72d9531004fd72d953100cfc72d95310067e52d95310067c52d9531006df32d9531006dd32d9531004fe70d9531004fd70d95310067f6599531005ef7259531105ec72595310067f7559531004ff7459531014fe7459531004fd7459531014fc74595310067f54595310067d5459531004ff7359531006df7359531004df7359531004ff7259531006ef7259531004ef725953100cfe7259531004fd725953100cfc7259531006ec725953100cec7259531006df3259531006dd3259531004ff7159531006f77159531004ff7059531004fc7059531004fe76195310467e65195310067d651953110dbe7419531005bd7419531004fe76d4d310067f65d4d310467c65d4d3103f5e53d4d31005f671d4d31005f571d4d31044fc7654d310067f6554d310467c6554d31005f77154d31005f47154d3103fd43154d3103cfe76d453103cfc76d45310067f65d45310467c65d453103dde73d4531005dd73d4531004fe7694531007775194531044ff7654531004fd765453103cfc76545310067f65545310467c6554531005df735453103ddc7354531005ef7254531105ec7254531004fe761453110dbe7414531005bd741453103df6718c53103ef7618c531286de658c531286dc658c531476df648c531476dd648c5314775f548c5314775d548c53142ddf728c53142ddd728c53146edf628c53146edd628c53103dde718c53103edf618c53103fd7618c531044fe75d8131004fd75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d8131004ff72d813100cfe72d8131004fd72d813100cfc72d8131006df32d8131006dd32d8131006fb60981310057f75581310057c7558131005bf745813110dbc7458131005ef7258131105ec7258131006f96018131044fe7518131004fd7518131004ff7418131014fe7418131004fd7418131014fc74181310067f54181310067d5418131004ff721813100cfe7218131004fd721813100cfc7218131006df3218131006dd3218131006de311813103e7f7559431004ff7459431014fe7459431004fd7459431014fc74594310067f54594310067d545943103cfe735943103cfc735943103edc735943103cdc735943103e7e535943103e7c535943103edc5359431004ff725943100cfe7259431004fd725943100cfc72594310067f52594310067d525943103edf3259431006dd3259431004ff7059431004fc705943103ddd76d4c312eedd76d4c3103dde75d4c3103f5e75d4c3103edf65d4c312eedd65d4c312eddf74d4c31465dd74d4c312ef5f54d4c3145f5d54d4c312eddf72d4c31455dd72d4c3103edf62d4c3144edd62d4c31005dd71d4c31286de61d4c3103fd
  | 20 => 0x14fc74d96310067f54d96310067d54d9631006dd73d9631004ff72d963100cfe72d9631004fd72d963100cfc72d9631006df32d9631006dd32d9631006f671d9631004fe70d9631004fd70d9631004fd76996310067f6599631044ff76596310067f7559631004ff7459631014fe7459631004fd7459631014fc74596310067f54596310067d5459631006df7359631004ff725963100cfe7259631004fd725963100cfc72596310067f52596310067d5259631006df3259631006dd3259631004ff7059631004fc70596310467e65196310067d6519631115be7419631005bd74196310467e65d4e310067d65d4e3103f5e53d4e31005f671d4e31005f571d4e31286dd76d4e3103dde75d4e31286df65d4e312875e65d4e31286dd65d4e310075d65d4e310065d65d4e31285df74d4e314d5dd74d4e312875f54d4e314cf5d54d4e31285df72d4e314c5dd72d4e314bedf62d4e314bedd62d4e31287d671d4e31005dd71d4e31287d571d4e31005d571d4e3103ede61d4e31005de70d4e31044ff7654e310467e6554e310067d6554e31005f77154e31005f47154e3103fd73154e31005dd7614e3103edd7614e3103f5e7514e31286df6514e31286dd6514e3103ddf7414e3103f9e7414e314b5dd7414e3103f9d7414e310059d7414e312875f5414e314af5d5414e3103ddf7214e3103fce7214e314a5dd7214e3103fcd7214e31005cd7214e3149edf6214e3149edd6214e31005dd7114e3103fd66114e31005de7014e3103cfd76946310467e65946310067d659463103dde7394631005dd7394631007775194631005df735463103ddc7354631005ef72546310fdec725463103cfd76146310467e65146310067d6514631115be7414631005bd741463103dde7314631005dd7314631005dd76cc63103edd76cc631285de75cc63103ddc75cc63103ddf74cc631495dd74cc63148f5f54cc63148f5d54cc63103ddf72cc63103fce72cc631485dd72cc63103fcd72cc631005cd72cc63147edf62cc63147edd62cc63103fd661cc631007d651cc631007d551cc631005de70cc6310057e75d82310057d75d8231115be74d8231005bd74d8231006fb6098231044fe7598231004fd7598231004ff7498231014fe7498231004fd7498231014fc74982310067f54982310067d5498231004ff729823100cfe7298231004fd729823100cfc7298231006df3298231006dd3298231006fa2098231006f92098231004ff7558231044fc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231006de4358231006dd4358231004ff725823100cfe7258231004fd725823100cfc7258231006df3258231006dd3258231006fa2058231006f92058231006f96018231044fe76d9531004ff74d9531014fe74d
  | 21 => 0x661544510057c7054451004ff7498051014fe7498051004fd7498051014fc74980510467f54980510067d549805103cfe7398051004fd7398051004ff729805100cfe7298051004fd729805100cfc7298051006df3298051006dd3298051046fa7098051046fb5098051046f85098051006fa2098051006f92098051004ff7458051014fe7458051004fd7458051014fc74580510467f54580510067d5458051004ff735805103cfc7358051004ff725805100cfe7258051004fd725805100cfc7258051006df3258051006dd3258051046fb7058051046fb50580510467c5058051046f85058051006fa2058051006f9205805103e7f7559731004ff7459731014fe7459731004fd7459731014fc74597310067f54597310067d545973103cfc735973103e7e535973103e7c5359731004ff725973100cfe7259731004fd725973100cfc725973103edf3259731006dd3259731004ff7059731004fc7059731006ef7558b31006ee7558b31006ed7558b31006ec7558b31006ef7458b31006ee7458b31006ed7458b31006ec7458b31006ef5458b310066f5458b31006ee5458b31006ed5458b310066d5458b31006ec5458b3103eef7358b3103eee7358b3103ece7358b3103eed7358b3111ecd7358b3103eec7358b3103eef5358b3103eee5358b3103eed5358b3103eec5358b3103eef4358b3103eee4358b3103eed4358b3103eec4358b3111eef7158b3111eee7158b31006ed7158b3111eec7158b31006ef4158b31006ee4158b31006ed4158b31006ec4158b3103eef3158b3103eee3158b3103eed3158b3103eec3158b3103ecc3158b31006ef7058b31006ee7058b31006ed7058b31006ec7058b31006ef4058b31006ee4058b31006ed4058b31006ec4058b3103eef3058b3103eee3058b3103eed3058b3103eec3058b310467e65d47310067d65d473103dde73d4731005dd73d473115eee62d4731006ed62d473113eee6294731006ed6294731044ff76547310467e65547310067d6554731005df735473103ddc7354731005ef725473111dec7254731146ee6254731006ed6254731125be7414731005bd741473112eee6214731006ed6214731044fe7598331004fd7598331004ff7498331014fe7498331004fd7498331014fc74983310067f54983310067d5498331004ff729833100cfe7298331004fd729833100cfc729833103edf3298331006dd329833103edc319833103efa709833103efb309833103ef83098331004ff7558331044fc7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331004ff725833100cfe7258331004fd725833100cfc725833103edf3258331006dd325833103efb705833103efb305833103ef83058331004ff74d9631014fe74d9631004fd74d9631
  | 22 => 0x455150d7f749455150d7d74945515067f64945515067d64945510075f63945510075c63945514dd7f72945514dd7d72945510076f62945514ff6c62945514ff5f32945514ff5d32945510457e71945510467f6194551047776194551006df63d8151006dc63d8151006ef62d8151006ec62d8151004ff74d8151014fe74d8151004fd74d8151014fc74d81510067f54d81510067d54d815103cfe73d8151004fd73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d8151006df32d8151006dd32d8151006fb40d8151006f840d8151005de7398151005dd7398151006df6398151006dc6398151145ee7298151005ed7298151006ef6298151006ec6298151006fb6098151005bf745815114dbc7458151005df7358151005dc7358151006df6358151006dc6358151005ef7258151145ec7258151006ef6258151006ec6258151006df6318151006dc6318151006ef6218151006ec6218151006f96018151004ff7418151014fe7418151004fd7418151014fc74181510067f54181510067d541815103cfe7318151004fd7318151004ff721815100cfe7218151004fd721815100cfc72181510067f52181510067d5218151006df3218151006dd32181510067e5118151006fb4018151006f84018151046bf7559051046be75590510463e7559051046bd75590511363d7559051046bc7559051006bf7359051006be7359051006bd7359051006bc7359051046bf5359051046be5359051046bd5359051046bc5359051006bf7259051006be7259051006bd7259051006bc7259051046bf5259051046be5259051046bd5259051046bc5259051006bf32590510069f3259051006be3259051006bd32590510069d3259051006bc3259051136bf7159051006be7159051136bd7159051136bc7159051046bf51590510463f5159051046be5159051046bd5159051046bc5159051006bf2159051006be2159051006bd2159051006bc2159051006bf7059051006be7059051006bd7059051006bc7059051046bf5059051046be5059051046bd5059051046bc50590510463c5059051006bf2059051006be2059051006bd2059051006bc2059051004ff7458c51014fe7458c51004fd7458c51014fc7458c510467f5458c510067d5458c51046df7358c51046df5358c51046dc5358c51004ff7258c5100cfe7258c51004fd7258c5100cfc7258c51006df3258c51006dd3258c51004ff7058c51004fc7058c510457f76544510067f76544510047f76544514f57f74544514f57d74544510467f64544510473e64544514ee7d64544510473d64544510063d64544510075f73544510075c73544510076f72544514e76c72544510467f62544514e67d62544514e75f32544514e75d32544510457f71544510477771544514de7e61544510477
  | 23 => 0x6ec6298d51005ef7258d51145ec7258d51006ec6258d5103ede6318d51006dd6318d51006ec6218d51005de7618d51006de7618d51006df6418d51006de6418d51006dd6418d51006dc6418d510075f5418d510075d5418d51005df7218d51005dd7218d51006df6218d51006de6218d51006dd6218d51006dc6218d51007cc6218d51006cc6218d510075f5218d510075d5218d512efd75118d512efd45118d5103edf7518d5103ede7518d5103edc7518d5103edf7418d5103ede7418d5103edd7418d5103edc7418d512eedf5418d510065f5418d51006de5418d51006dd5418d510065d5418d512eedc5418d5103edf7218d5103cdf7218d5103ede7218d5103edd7218d51004dd7218d5103edc7218d512eedf5218d51006de5218d51006dd5218d512eedc5218d51006df4218d51006de4218d51006dd4218d51006dc4218d5103edf7118d5103edd7118d512eedf5118d51006dd5118d512eedc5118d51006df4118d51006de4118d51006dd4118d51006dc4118d51006df2118d51006de2118d51006dd2118d51006dc2118d5103edf7018d5103ede7018d5103edd7018d5103edc7018d512eedf5018d512eedc5018d51006df4018d51006de4018d51006dd4018d51006dc4018d51006df2018d51006de2018d51006dd2018d51006dc2018d51006df6394d5103edc6394d510475f5394d5118eec6294d51005f67194d51005f57194d5103cfc7654d51006df6354d5103edc6354d5117eec6254d51005f77154d51005f47154d51145ee76d8951146ee76d895100cee76d89510076f75d89511476c75d8951006ef64d8951006ee64d8951006ed64d8951006ec64d89510076f54d89510076d54d8951007cf73d8951007cc73d8951006ef63d8951007cf63d8951006cf63d8951006ee63d8951006ed63d8951006ec63d8951007cc63d8951006cc63d8951517e751d8951517e451d8951006ef75d8951146ee75d8951146ed75d8951146ec75d8951006ef74d8951006ee74d8951006ed74d8951006ec74d8951516ef54d89510066f54d8951006ee54d8951006ed54d89510066d54d8951516ec54d8951006ef73d8951006cf73d8951006ee73d8951006ed73d8951006ec73d8951006cc73d8951516ef53d8951006ee53d8951006ed53d8951516ec53d8951006ef43d8951006ee43d8951006ed43d8951006ec43d8951516ef71d8951146ee71d8951146ed71d8951146ec71d8951516ef51d8951146ed51d8951516ec51d8951006ef41d8951006ee41d8951006ed41d8951006ec41d8951006ef70d8951006ee70d8951006ed70d8951006ec70d8951516ef50d8951516ec50d8951006ef40d8951006ee40d8951006ed40d8951006ec40d8951006df6394551006dc6394551006ef629455113eec6294551045f67194551046f7619
  | 24 => 0xf7258e5100cfe7258e51004fd7258e5100cfc7258e51006df3258e51006dd3258e51004ff7058e51004fc7058e5103ede6318e51006dd6318e5103ede6394e51006dd6394e510475f5394e51005f67194e51005f57194e5103cff7654e5103ede6354e51006dd6354e51005f77154e51005f47154e51047775154e510057d76d46510467d76d46510457f74d465152d7d74d46515267f64d46515267d64d465151e7f62d465151e7d62d465151f5f32d465151f5d32d46510477661d46515277641d46515277541d465151f7621d465151f7521d46510057e70d4651006fb6098251004ff7498251014fe7498251004fd7498251014fc74982510067f54982510067d549825103cfe7398251004fd7398251004ff729825100cfe7298251004fd729825100cfc7298251006df3298251006dd3298251006fa2098251006f92098251005bf7458251155bc7458251004ff7458251006bf7458251004bf7458251014fe7458251004fd7458251014fc7458251006bc7458251014bc74582510067f54582510067d5458251004ff735825103cfc7358251004ff725825100cfe7258251004fd725825100cfc7258251006df3258251006dd3258251006fa2058251006f92058251006f96018251006ec62d8d51004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d510067f54d8d510067d54d8d51006df43d8d51006de43d8d51006dd43d8d51006dc43d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d51006df32d8d51006de32d8d51006dd32d8d51006dc32d8d51004fe70d8d51004fd70d8d51006df64d8d51006de64d8d51006dd64d8d51006dc64d8d510075f54d8d510075d54d8d51005df72d8d51005dd72d8d51006df62d8d51006de62d8d51006dd62d8d51006dc62d8d51007cc62d8d51006cc62d8d510075f52d8d510075d52d8d51287d751d8d51287d451d8d51006df75d8d51286de75d8d51006df74d8d51006de74d8d51006dd74d8d51006dc74d8d51286df54d8d510065f54d8d51006de54d8d51006dd54d8d510065d54d8d51286dc54d8d51006df72d8d51004df72d8d51006de72d8d51006dd72d8d51004dd72d8d51006dc72d8d51286df52d8d51006de52d8d51006dd52d8d51286dc52d8d51006df42d8d51006de42d8d51006dd42d8d51006dc42d8d51286df71d8d51006dd71d8d51286df51d8d51286dc51d8d51006df41d8d51006de41d8d51006dd41d8d51006dc41d8d51006df21d8d51006de21d8d51006dd21d8d51006dc21d8d51006df70d8d51006de70d8d51006dd70d8d51006dc70d8d51286df50d8d51286dc50d8d51006df40d8d51006de40d8d51006dd40d8d51006dc40d8d51006df20d8d51006de20d8d51006dd20d8d51006dc20d8d51006df6398d51145ee7298d51005ed7298d51
  | 25 => 0x8853006ed4158853006ec415885303eef315885303eee315885303eed315885303eec315885303ecc3158853006ef7058853006ee7058853006ed7058853006ec7058853046ef5058853046ee5058853046ed5058853046ec50588530466c5058853006ef4058853006ee4058853006ed4058853006ec405885303eef305885303eee305885303eed305885303eec3058853004ff7498453014fe7498453004fd7498453014fc74984530467f54984530067d5498453004ff729845300cfe7298453004fd729845300cfc729845303edf3298453006dd329845303ef67198453046f75198453046f4519845303ef7319845303ef43198453004fe7098453004fd70984530467c5098453004ff7458453014fe7458453004fd7458453014fc74584530467f54584530067d5458453004ff725845300cfe7258453004fd725845300cfc725845303edf3258453006dd325845303ef77158453046f75158453046f4515845303ef7315845303edc315845303ef4315845303ed43158453004ff7058453004fc7058453004ff7498053014fe7498053004fd7498053014fc74980530467f54980530067d5498053004ff729805300cfe7298053004fd729805300cfc729805303edf3298053006dd3298053004fe7198053004fd719805303edc319805303efa7098053046fb5098053046f8509805303efb309805303ef83098053004ff7458053014fe7458053004fd7458053014fc74580530467f54580530067d5458053004ff725805300cfe7258053004fd725805300cfc725805303edf3258053006dd3258053004ff7158053004fc715805303efb7058053046fb50580530467c5058053046f8505805303efb305805303ef83058053004ff7458f51014fe7458f51004fd7458f51014fc7458f510467f5458f510067d5458f51046df7358f51046df5358f51046dc5358f51006de4358f51006dd4358f51004ff7258f5100cfe7258f51004fd7258f5100cfc7258f51006df3258f51006dd3258f51004ff7058f51004fc7058f51004ff7498351014fe7498351004fd7498351014fc74983510467f54983510067d549835103cfe7398351004fd7398351004ff729835100cfe7298351004fd729835100cfc72983510467f52983510067d5298351006df3298351006dd32983510467c5198351046fa7098351046fb5098351046f85098351004ff7458351014fe7458351004fd7458351014fc74583510467f54583510067d5458351004ff735835103cfc7358351004ff725835100cfe7258351004fd725835100cfc7258351006df3258351006dd3258351046fb7058351046fb5058351046f85058351006df6398e5113dee7298e51005ed7298e51004ff7458e51014fe7458e51004fd7458e51014fc7458e510067f5458e510067d5458e51004f
  | 26 => 0xcfc72d8553006df32d8553006dd32d8553006f721d8553006f421d8553004fe70d8553004fd70d8553006f76198553005ef725855317dec7258553006f56118553004ff7418553014fe7418553004fd7418553014fc74185530067f54185530067d54185532eedf53185532eedc5318553004ff721855300cfe7218553004fd721855300cfc7218553006df3218553006dd3218553006f72118553006f42118553004fe7018553004fd7018553004ff74d8153014fe74d8153004fd74d8153014fc74d81530067f54d81530067d54d8153004ff72d815300cfe72d8153004fd72d815300cfc72d8153006df32d8153006dd32d8153004fe71d8153004fd71d8153006fb40d8153006f840d8153006fb6098153005bf7458153185bc7458153006f96018153004ff7418153014fe7418153004fd7418153014fc74181530067f54181530067d54181532ae7e53181532ae7c5318153004ff721815300cfe7218153004fd721815300cfc7218153006df3218153006dd3218153004fe7118153004fd7118153006fb4018153006f84018153046bf7559053046be75590530463e7559053046bd75590531763d7559053046bc755905303ebf735905303ebe735905303ebd735905303ebc735905303ebf535905303e3f535905303ebe535905303ebd535905303e3d535905303ebc5359053006bf7259053006be7259053006bd7259053006bc7259053046bf5259053046be5259053046bd5259053046bc525905303ebf325905303e9f325905303ebe325905303ebd32590530069d325905303ebc3259053006bf7159053006be7159053006bd7159053006bc7159053046bf5159053046be5159053046bd5159053046bc515905303ebf315905303ebe315905303ebd315905303ebc315905303e9c3159053006bf2159053006be2159053006bd2159053006bc2159053006bf7059053006be7059053006bd7059053006bc7059053046bf5059053046be5059053046bd5059053046bc50590530463c505905303ebf305905303ebe305905303ebd305905303ebc3059053006bf2059053006be2059053006bd2059053006bc2059053046ef7558853046ee7558853046ed7558853046ec7558853006ef7458853006ee7458853006ed7458853006ec7458853046ef54588530466f5458853046ee5458853046ed54588530066d5458853046ec545885303eef735885303eee735885303ece735885303eed735885316ecd735885303eec735885303eef535885303eee535885303ece535885303eed5358853046cd535885303eec535885303eef435885303eee435885303eed435885303eec4358853006ef7158853006ee7158853006ed7158853006ec7158853046ef5158853046ee5158853046ed5158853046ec5158853006ef4158853006ee415
  | 27 => 0xf729835300cfe7298353004fd729835300cfc7298353006df3298353006dd3298353004fe7198353004fd7198353046fa7098353046fb5098353046f8509835303cfc7558353004ff7458353014fe7458353004fd7458353014fc74583530467f54583530067d5458353004ff725835300cfe7258353004fd725835300cfc7258353006df3258353006dd3258353004ff7158353004fc7158353046fb7058353046fb5058353046f8505835303f5d76d4e5303d5d76d4e530465d76d4e530475f74d4e530475e74d4e530475d74d4e530475c74d4e5303f5f64d4e5303f5e64d4e5303f5d64d4e5303f5c64d4e530475f72d4e530475e72d4e530475d72d4e530475c72d4e5303f5f62d4e5303f5e62d4e5303f5d62d4e5303f5c62d4e535375f42d4e535375e42d4e535375d42d4e535375c42d4e530475f71d4e530475e71d4e530475d71d4e530475c71d4e5303f5f61d4e5303f5e61d4e5303f5d61d4e5303f5c61d4e5353f5f41d4e5353f5e41d4e5353f5d41d4e5353f5c41d4e535375f21d4e535375e21d4e535375d21d4e535375c21d4e530475f70d4e530475e70d4e530475d70d4e530475c70d4e5303f5f60d4e5303f5e60d4e5303f5d60d4e5303f5c60d4e5353f5f40d4e5353f5e40d4e5353f5d40d4e5353f5c40d4e535375f20d4e535375e20d4e535375d20d4e535375c20d4e53004ff7498653014fe7498653004fd7498653014fc74986530067f54986530067d549865303cfe7398653286df539865303edc5398653004ff729865300cfe7298653004fd729865300cfc729865303edf3298653006dd329865303ef6719865303ef7319865303ef43198653004fe7098653004fd7098653004ff7458653014fe7458653004fd7458653014fc74586530067f54586530067d545865303cfc7358653004ff725865300cfe7258653004fd725865300cfc725865303edf3258653006dd325865303ef7715865303ef7315865303ef43158653004ff7058653004fc7058653004ff7498253014fe7498253004fd7498253014fc74982530067f54982530067d549825303cfe7398253004ff729825300cfe7298253004fd729825300cfc729825303edf3298253006dd3298253004fe7198253004fd719825303efa709825303efb309825303ef83098253004ff7458253006bf7458253004bf7458253014fe7458253004fd7458253014fc7458253006bc7458253014bc74582530067f54582530067d545825303cfc7358253004ff725825300cfe7258253004fd725825300cfc725825303edf3258253006dd3258253004ff7158253004fc715825303efb705825303efb305825303ef83058253004ff74d8553014fe74d8553004fd74d8553014fc74d85530067f54d85530067d54d8553004ff72d855300cfe72d8553004fd72d8553
  | 28 => 0x6c00000100300380060020008000000000000802800c00800300580080090058028008000004805c00400100300200480030010000000000002003801e003001001c03200c000801c008000000000400000d002800c03400300000000300010000030002001002000005a0030018000000000000800000802500280040200050078028002009000006c006001000000002800000480740000000008020000011005003403600100580080020020030000008003000000000000f0000018000000001800c0000050000008000000001802000200400000a40020010000008022000007802002a004004000400401f00280a40040010008004002002007000000000600380140000070010018022000000000400a00a00000080000040028008014006000802401a0070000008022000000000c008000002000802600d00300080180020000008000000000001802000200000080040020058004004001001804c0000040010000016006005801400600000000180020000018038000033018801c00200e00200000000000000004000000003000400a0040008000018003000003c018006000000c02c002002001400000c001800000200d001000000800300580040020060078058018001000001c02400000000040100010058000018000000000000001100f8008016021000000800c00c0010048000000001802809e000002000000a000001000801a000004000000a008009001800e003000000400200b01000740100120038000000004000800c01c0030038004010001005800800600000700ec00200000000000000000010008012000000806003e001000001401a0000028064004000003801802600c000000c00600a00d800800a006000000400600103e0048006015000800403e00000000080460000028008000000006002800400300a800c0000010018034008000002001400001c0028014002001001000c00401a00100000180130088034004007000000401000403cfe7598753004ff7498753014fe7498753004fd7498753014fc74987530467f54987530067d5498753004ff729875300cfe7298753004fd729875300cfc7298753006df3298753006dd3298753046f67198753046f75198753046f45198753004fe7098753004fd709875303cfc7558753004ff7458753014fe7458753004fd7458753014fc74587530467f54587530067d5458753004ff7258753006ef7258753004ef725875300cfe7258753004fd725875300cfc7258753006ec725875300cec7258753006df3258753006dd3258753046f77158753046f75158753046f45158753004ff7058753004fc705875303cfe7598353004ff7498353014fe7498353004fd7498353014fc74983530467f54983530067d54983532b67e53983530467c5398353004f
  | 29 => 0x400000300200040020000028068004002000001000e009001001400200b004002c00a00400000180020000020000002003000000400400300f002001c004004800400400100180100000010018004004000000800402c00a0000004008001000000401400000380140040000018000004001000005400800c000800400000300280040020000010024056001000800c004000002001000c0000040018004002000800400000300b00080100090078004000000000000002e0010000024000008000000000202100b800c0060000020004004005004002c0000160018008000001005800c01c0000020004004007002004000401e0000028008000002801c03000300400000000030000004022000006002000800600000780000000038004000008003800401600b000000400a01700300040120020000000008000000000801401b005803401800000a00000000070000018000004000001400e0010018010000000005001c004003000803c0000000030008002000002810400a005001000000a004001000001a000000802000a002000004c0060000000008002003008006c0000060008004002000000001000401c0000014000000000800000600100080080420070000000006005000000001a0020300008000000002000c0000000000000010000000800c002002007002400a0000078000000003000000000a01c00c800000c0010038008000005005001c00a00f001000001000000e80040080020000014000000001001000200000000080020040060000004005001000c0020030000000002004000000c00000800000000000070038010000001005800c00200400080200000050050010006007005000c01c000001000000000300380540120050010008006000008800c00c0010008000002000000001800a000004001801000700700080060100000004000004001000801a0130030084000002005807400000000180340000000020014004030004801c01000100000440000090008004000006000003c00000000100000000020018024000006000800000e000000802000000f0090000000000007803c00000000e00000060000020018000004001802000c006000000000200100a800c0000080008010008013000803c00200f0070018048002001800800600101a800402a009000001401a000005803800a0050008000002000001002000a000003000800600b0030004000000014801000400000b0008008009003803c0020020008020002003000002801200d001801400000b001800000400200900b40160000010008002003004800000c007001800000e008000802800c007000000400e01700080080000000018034052000000001c0000050030000000000000000003a0000050000068000001000400e0040008024000000
  | 30 => 0xf440a0cac627eca512cec7582cd10cc000077500008fc03705e009f8000357000003410152d08cf12cf11ff3928ce216d89660000ac2023c85208fcfd027611532940bdd1d9026300010ab1f50ec7096c17d29bcebe30e11ca1ac00940abce7f3cf41c14acc1510788a6011c450015d1285005498616b864717a81762738fd702e0d5604ec8120000caa08e11e22300df101d000008443973e482d92e7c2700000001000804001200700000580040080050004012006004001400c0030010000010009001801405a00a001000000000600800080100190018004022000001000403200b000001c00600c003800000001f000000400400000280080080010060004006004000800c006001005800001e004000002400c00a006000c01a0110018000006006003800400200700300000000000158004000002002000000800c002000400a02800300580040030018000000005005800c004002002805c006001001000400800a0010004002004001002000000100000000020000000000006000008805000200d005005c006000006001c00000000080f802c0020000000024004000804000c019000802800000c0000000006000002000000e00000800000140010018000002000000803000200e006800001e001000000405c00100000dc032001002001c00400200000000080000000004006003000801c01e001001002000200000880000020020000038000000002801c00200e001803000000601580080080020000008006003001806000c0000010018004001002000c004000002000800800e002800c000007000803000200000000a00180020048000000008007800c008000006000002401a00000080000000008008002002001800004600000080080080050020008000003006000000c0000008000032000000008400200b00280000000010000000002001000000c0080000080010012000000000401a004002000c002002000000800200a003801c008000000000802e0060008020010000001001400400d001801c000007009800c00200c0018084002006007800002a00000200000000040000000000003000005400e013002800800400000280000080030028024002000000006c00001800100000120010000074016003000000000000400f80040020010008000000000000000800400000100280020020000024004001000800401800100280200040080048000006006000800000000f00980500020070038004002003000002c004000002000c00001e00d8024002001000001001c0040110018016001003800c00000c000000001a00d0038018006000001001c00000100280240160090000008014002001001c0000020010018002013001001c01000500200000020010000008006001003004c00a0000000000002001001800
  | 31 => 0x30540003278d5e39500000b944b313a835844585d74a745a03ea800014040002b7090d000095d1980e3600000000dfc000000000000000000f9c0001bcc00029d858000006d1000099908643874628c9220144af00012912b7d1f238e857f07f800013ec00000000000000000000000000000003df4b711850bc00000e6510040002744995359800000000004360bde41e0c390a4c3a00000000000000030ac00000005f51210b0545fca5349dc92819c8e8c0000b7e00000004988973002505200005b4000000000002072ab8e4b03f43893f10c0e44391640000000008113523c92a33b080d122280002eb00003af49f40354595119c00002985331ec814e1c6047e0770e241ed01ce20442db3a5cda03c9854a17d8ae000000000000000477080a0860a3606b127b3e3c2d1403400f46783b80000f1a169000000010832eb4f6600000002c109e344d0f061d78fc6452c0002a3cb7c02dd1da05580001ae837a0000efe231c16b0000000000121240ac9070c8000011188bb2b50951000000000009421d3000038a000000000000000000000059c000000040986c900005d115b8dde4a60000000091f03b493c2bd877c4074dad21cc3743e640113ff874e1c7cd0e37605721b04f0145bc64e000000000007010000c7511a081c11582690e54bff15c0000473d09e489d05427f000000000000000f2d2d28e7b00000004030000000000000000ff0000d9200004951c1cdba26246cd1a2cc0d0321160000000000000000000a69000000036ec00028c51490000091000000049c0000000010a4b242bd00006401b2031743a0afa34005dd087903b46200ea07410f20d086802b84f141f8d2ad0ea0762181000000011eb00000001040e1400001651c68f38385498e000041601544ca0c908de42302a80840b3807a0d5f3ebc00000000000000000000029a409c7f22d10b4147e006a3bd014731e49690000b17170c000000022d00001f744440da308819e36bc93b494ce3c04c87f44a5097a121830a4948c502094e32497c8b2337883a00006f400000004af111a3f8cf6241cc1603ad07a93d689de3e10fcd0000b6648bcbc210a12670000e8949ad20922b063d2b64d8d3a2cb484828cf6131d1592dad06433d4b4b01f45f403d8ea4181cec9150000000009b91eacd4e0000a4e12b528931882df00002c020600001b9c3270e8cb9b1cb8d24000041c402c9400d880032ad09d4351cc430000dca0bb45c6247056402e4000136000025dc7e70000741000127300008540ae914608100000000350000094900000002bb47eb24fcfc919d07a60d5883f3eb8eda28608132000b8f0e0c00000011301ac81311cec413103c6a3389c4ef32f0ce41e40a0140441944b40ba3459c9a31e541ee14610d63a384903e9400044e080b076cde52f28513000
  | 32 => 0x6c85d16200000f9411e28d10a415c478b000043d29105ac24580003fd8d84000087b000000017ac7b800000003fe829534d4a7b1954cbf00000000000c3a0000000164c11933f0af9297863543a4d6d29ac000000000002ed2b20000714103412f0f148480000dbc428800011dd10d3c5c1ba2d64ef819ed0e145989b833ecb722cbc6ea2b1461b3e60f9734e0e5b38d0b3a28f0ca84221217161c1f334a47ef1e94e94075d14831d0c1e34f8d0c2498d86026417506fc15018d03ab2d440dd3c8027f1cbcbfe406c000253504200003e203b127f0ac400047b06f53b441d900a467e1b8d27c0000000141c58e00580003180fe2020c2e8022c00021888e0281484a1cc4d453de88a72afcd820b4c18f080c00013b8c0c08d8b6928380461950000000013943b82d81a4ce0610c4a0945dc1822a5069743a87bb01000001704fed301c3dd33fd1a94214efc1ae0bb92b1cec800000002084000163016425fceb7000005900000000b1c7ac49c8b9014187711f2826f16ac09a0c487e022142751a0c193000018e060c0000fb400048ec5a11088b5532bc6b13178c3736b8cc9000062808a00000000000494400024840003e38a550000eef32b07ec1a503f12a5d0b000002011ebd244122849138248f617f047639841b7143009f0b8c64c000088037f0ec433203483aec09813dc44b20807091268000113c6ca1b3820e10b4000000035e0000ea300007f1037caa80f709cc47792b932c85d2000065e00001a8104442036acfd528dc13a09681263fd49300fb823322a819c37842463b40f8216d402f4400c8130a915e000000034dd1780ffd10135544700000000000000035d80003294000000000000001221aa071900000000fd80f43afcad533345520798a060008fde26d400024ccef349a8eee09050020000da54484255000000000000002f5017a0000000000124512a8d91000113722c40000000ff73cfc87f00002b802b0f4d01d8ce3145c000002d1b72fdc0000001136314400000001340000000000065a20a891d33c00db3d5cb0e2d3cbce234c5ca08312bd118443b00001242968d2828cc89a3c34aec1dcc262097cd723094e422fb863f41e40003ed4000150cac94724eb8000111b161800018d800015e09a607b00002de8f2f000061000000000000000284c68e000108a261c3cc0000b5a4830000311031331c88d748040000d68e1c0000dcc1be07cf3cf07e919fc7ce07802851ff48c83f7d1d041a105f3ecca2d16dc33b340d13a13080e72a00b7f255445505ec58d31690143eac0e1224505842f0bf2413d010379c4930c7451e31a014329b4b6517c40e4290c0001f94a7144b12c0000018a08ecb25014c3b63ad804221ac4034884ecf0000df70000bcd09b8cda12d0a581e103093a780e8000000027a8665463d0ae1fec00
  | 33 => 0x680a380002b001ff1ecd093388cd0217b488d06241c94298f8900008d91d700002af4000460cb9c2a80c210000cb90e4c00048d0d17000000040bc00435e8a792bd000000006a903d431400000003a58a9e102c2503a140003600000190c49e1bf000024402fe45cc000066841520f49092bc800000010403ac0b372e344002ea00002bf8000000000047580000000b4300000001b745b100000000df40fe03a400041640003864aaa0000e410d900004a4c00037c915d313cb8300004eb000067146e01910d6d1e1000000000000003fb030441891dd1e040001b0c5572f680001b40d673ed07470c8473e19d80de3a20fa30f2c1fc0000cb134180003dfc0003e3000000002cb41ec67500000003df068148b079c367800002cc0d20cb926823b4f1000009f90000afc01048ce0ab07fc0484f9e48001a31150ccc42a800028a4b9a0d84e3f483c7a13d580001bc8fa61e3863100010290000000356000004d8738409472a00010390000208113812b0730000254000001343c900008ef02a00000001106167c31600000004194e4800009471b2c86a3134b1947dc81000007a3000000000007ee05a8b23074c7c82348d1e00002b20b245bb2ec12cf000118b23e82dc12d80002bacbe30ca80003698d7106b4000131091a0001259000000009e48ae0000000000000000000000000000000040849b0c0000004d53d9c000000000000000000000d5b00000001af4ced2138000000000031a4d5744784b029c87631ed894421a0bed1928f8310146894048c6a00008c20000b5800000000398ef543f50e73978c94195cbd3365cca60ce10570430dce038c8ee39f8c6536504cc0a641e114ac267393c012248032b1ec502a000001f0e500003ffc4a621c8a810000a9800003db0000000156cc1900000000000000000000000003d60000000093c00001f907148b88cd0000914027005f4ac4000000000000000000000000000000014f40002c4ca674b5c00042501b3386c000000097b188ccec0000000000043e0000ccf000118d0000c830874dec3100eed40590050ea4bb31468b313fe40c33c481e9041cc1038a918147c50ca340505a24f90810a44e6f46fc2292a3403934fc47a3ba8d411644b0733b801b259087e4000cc40854a9f461112e484504921dc4e300008920a88325000000000004b83ca8beb052045b32b8f1629a80002c4528b45512262f8466c000033c26484961cfc8e405705b20334fc52ea47c90000bdc00004ba0000c244a010f028e807515240002f5c1330000ec503f056c03500004b2c31e27552740000844000007342dd0440d945e5119034a3d3c0bd158c1a50000ee31658ae747c09ac0850743188800000010b90000000185ce7a000000025947d31d3c6870a2110a4864dd11d9cc1600009810000946180c00e3e
  | 34 => 0x5ccd226a84fe000000037810362cacc280d98e450a700000000d1c36902e140c0b0f1834dc9324018445547991cac00000000000000000000090600003a53d64000000000029c085f000000027240001d4d1740294000210c96b000000025509da2b2c0000684fa147d0000419c14d1b100d62e4836e44240000f8c00000000000d7c39d000000000004a9000075520d80004674cd841bcbfc1a200000000d103ba451500000003edd18003dc2eb0000ddc0d74dcd493470c000079600011b90000cb340c855f0f5ca65110c0a00a5899f36dd127000000019e84d7000097c26ad29500000000000f801c380002c40fad37550ff43109ad441124c0000c8d000100e0ec445000000004b6108e04c09f72990d7d38981be30607c00ab4c8644f010e31fc60507689cb33947d5490427d48f8cba49410e600012a617684a514a852e208d2222798085412843200006a73e3466e00002bb206c0e207c4d344710fbd484036b0000ac13f040ca37b4c8f19080002650bc815547e60cd053c1060a8a38487ad2e1006d00009d60f60469136c00525c886044f4c0a20c060a2e18e73240d1402670801000000000000000fd4c3537d80000000000201c4bb0074dc000001803a840000bc911400003063a540003d00ee2469493d4714c7a0d2c51d00000a71d108b60000546139c27717e8a0b0000cf90000bbe330100107e05d649911393e290461ef9204335c0003c2cbea3580b77000027314340000c38888000056d2c6ceca00000000c600003bdc00000000000000ee53dc8b21000000000010ba3a684800ce41982a38e490000dd028e40b2053cb1d000000017ed0f90000650000000005d000000003b02b310770bc015700010a31bf50434530f1806e02f60e4438b3288064354800000011872efc0000000847274c000000023e47bca173cc4e58000000000010bb0000f51243000037640001ffc00012f8aa50000000000105b0000b5d3c900000000231000000043ac9960000bbc09743e61e9c00000000001e012c74248a220ea80004998bc743ec08d291cc6749d4ff300003000504000000121d341c2023f50fea2ab41a226840ee39d000047800004a6d21b025c0471dc800043200001cc800017540000a606853ab0bb4395c2521f3109523f400000000000ae4ee7000000000009e137e880f000069e00008332a40ef90cb4f7b464061936e4b5232440480fa8d3d34d800020f0710117d22900008240858419246c78c0000890000003a1b4d12f163d1202bd45af012837237ac65c02bd1a611cc9c03db03102580e30049c0000b3c00029700000000af012140c600005d30000b79000000000008bf36f4d9f00b800023ecfc747a52aa09ac6c62f9075a3a80dc60000c0b322882812c45e22b40646000068a374853f45f8dda0114edc4730a
  | 35 => 0x7850c700c94154b0b153c087216498525681622eacd4f048cb5349285c4192509b2ed83a6279c5e908707030000dd63ccc0000f040003e051961d34b0624a4f1c11d00002310000000000015bc67d27a400029fcc6f10e8baf3b04b3636d49622e08e2d40ccbe60e285650000932471c53e0000f9f4584000000000002a436d322d2693b3865202000000194355000042f19100000000ba000001013cb8aff0818000215c7353d3826d000000025780004324a412f5400027a090b2a9c0bf00cd0b50a7894500000000000d79000000000003d9480cc773f0000000000000000edb16e0a990dc03822118efd3c9cbb219985d9451c53025a000000e12332dc000026ec000087c2f42a148cc4aa0d542fd43ce1e3d283000000035f000000009b03b3125839c06be20103533eec2ec154c000000055d28c80010ad04601a6835200000002f80f0f49e094e48800001804f64492466b3544a62487c2121688eeb26447ae15d49d238d51a80000000067515c1f5c1250ccc0000ce8b2221f08a027943f024040003a70d8e0000a6611ac00002205bd00001fd33f45191f5814b3ce4c4e404c7023e2007005c800032ad0fa2b445092a8cc88062099b26cc7aa072c00021309a8281cbe21c44000232457c29f00000bfd0221d800000000000000000020c8e3845e80000d64000369c0001678482285459042d0b0a0000c873a1c9700e380000001279435cdb625d4eaf39b44b73d851c03cdce1000000003b98a1c3aa4e2512f42392bc4e0e214ce473820c3f2134f110b6910b460900400007c72d001ab1d740000000402143c0003798d8f40c52be24e45cf2448f3a18dcfa9044c0a40b3113237a058a07b43ec352c508000128d1d2400018f8000370ce4040780002e3873c0de46210a48a1d44fd2550000d2600000000ef04c10000000209cf1f0000a4a000000000000000f28db4307c10033acc8939b04f9000000002f053b47085d0000000045d4eb102b8d480a7c17c4a20a2302288790040ac84274fd80cc098239dce590554510397526d3f2902c13202d23cd50a910c0b3f40dca2a3b54b6f1f2c05d2400da100007c64208e6a2898287156406946e83da09a05c0085c462407c23525f402c3c20a951d9903a0000eba45c00001f7cfb82a1cfa40000ea6334c81539e094823e400018f0ddf2e601691c88aee30f51df00a01a63e1cc4c000029b21a47264a1c1902d509ff4b4910c1428c131844284046081e3354eaa465434003387683cb10a1083c72c02b488723c42093fa40003be81164aac475341079f3bb00000000000079c00000004a045e43b4366c000000015b198c729000000047d40001e9098b000087d0518000000078603ac2e246900000000000000122b00006530000e0500006a019cc00027cc00027d40000aa444c35a8f6f4
  | 36 => 0x22506e22c6055c110885b00d05760514f250b9c88618000b114489c43ddc0000d44d96132416e2c80db020a400817bce8d2cb05364498841149c5b03ec4b000ebceb31e0800011700ab14bc0000000d7400009df2564000000000033a0000250cdac0ff8aba2d6c74b49806590000d61468c00005286ee0184e623f080000d1000000008510e30f4847607f600000001da413703640000a84b1544f8b60334480e3790a9341f4000390cad60000aa408e804c2e006a6375c0004814b490f7cbe739543c024c445d2020f1929190fe1bc04290000aac01609c32f592a4368c11c4794ff20fa0d7820645214b207280000cbe346d22324a8acd1808186012c000162c3150000e0b27b506c069019900000002cc88dd00000001d14dbe48a11d5278000000002e02a591a73d0c0002208112160cd19128c1141a74e533284e0d46881f508bc9190204638238c82b3c1ce801e805c5248c82c0e1456222e415a089c39e31845281f600000000f633db40004a30ae44368ba409f042704b8dc20cb041d326077a21b4c8c0000cb6309c2fb1fc0ed9104800000003fb15a0000000088b31e00000000c0f0dbc7274ac09524a3c0003de4df031b50630758d9d4544451371477e0a9c9c1385c0f82ce520d49680001c6c0000288e33192092c2db90a513b12bf15f400008006eb18c0c530a0507a233c7b53a184993018af3261111000002ef0000e3934b897e07c8051000000000009ca000104e283c71d000000000006d7000068f0b40b0d2a7107200006e543640004820000000047828283a12810a73246090f00000000000b76000111500000003004000431c2ce00006e60000d12000000040f40000000afd00000000000000060400000007b700000003860d1d040cd6f4b100000ef8e5a29580000000ee40c081672764000000032f000082f0000000025400000a8ea50cd864509d09be07101bd4184756228c3f245c4f5e000031141c036a1364000000000000005f81ef49a90000e0a00000002834000401854c000120e23281b608dc1960d0500f00000000000e5040b48db3b591cb393006804f434d000000000004bf00011bb0fe88e20000a4800001d133812b816b470f27c528e289467800003460f3c78d43b062042a03d344601543bec0f328b90ed05e524009640502b2903836600003a10d850000000223800000000000000cbb00000001a0843432b425300000002dccbe501bd23000000002aec00030d80004a10e8f00007c50b98000044041e3a48000426912b000013f000024a0000000001c2bc00000003dc00002950d5011b0ad72528bfb3b78a3f2570cd922b41c32d1c967079489d0000ffb268000005782894218c1d21b8c930aa922a00008740b7929746c4df82bdc6aa3d192c146f923d326852c2edd23c108511d46f076d4084
  | 37 => 0x3c8c07136880000000e0c4a0400000006910a910b21e887c440700003b6071e1ad437329d4f95016cd42000128a050008c193c3030150ade14387890a949ee44c4b0300005f31ab40003574f853d5412000008a9309842c1d211db0a80f5d000083117b8bd24798a0000002b300005dc30c02d423a05380000479000126f01585e41bc45db349441f33a815834f087a10982be08c84d400000001534a8b39a11c120dd24b08b092b40284441be82ee31f0000279000031605cc0adca88125c0000fd051b38085f938a45e7473917b36200002270000203529a024c0000fdc0001494f5b137d1443cd0f8b1b503ad00000001289193437001e00000b031c00003ee8c5b2d84c962ba48553a44c8e31f453a00000002ca4d890cc82824994c0432140000ee80a120d4b9e000000000000000d38000000000014d499d0000c9d0000c712a0cc630000c17018c1af3500cd4231403100004380720b911ba057a23fc0004b0d24f000000028bc0002178cef1624e763f711d20dd8d652c7836726f4cb024e0381290800000003c40bf452635f849c3d041f4441440c475028d00010532cb51a1172431b16f88423b00ddd3164fee3668ab3260c0000e9cf96041448c26684e81dd0000353095f2b6813c457c0004b58db800011691afc96a46ac4652a1072037ccf6825c4839183000000004fa30c4e8a225c77623b0bdb06eca28422c31907ec1061a6c43912e4f533fc06d846f502e07611b31b848bd14c4d6400dcd460ddd14d09a8c202adc2c641f1108058c740292c33d48784c632d0f1e32dd1e8331876c03e4cf335b11720eb91b51ad068d34e4ce72a6c3783cc905143340001550e2f22a0205000000046609b20000a6e000000000005043b180003b342d534b495b00001aa43cc0000d70573169c18d170800018a899e4548fe700000002fe83d208280003da8000212c000304800027bd0de00604a748703ef1650ba521e074234512d33d2859b0b10000130026118b08d000000b50000a4c2820f090d5c8dc00007bf00000f00000000277113b000009d00002c300006a100000003cecee14b50000254c0004388dc732a48eb0124627000010f20ecc551a18b45003404e0aac0002350e790cf84e53170d1336c50f615f8d31349c3692f3c751000033f21c400035d4a4d1abc7d947e43261ea06ab00880863d5000032109f20000c820728000000118c25b4e7211350a02a74fbe000073000005a81358b2e09b0db2099849b114c234300cfbc0b2824c310400026b85a645f42f84ab00000110000000102400000001234b1f00010d10a980004670dd300006241e5ce1a0000afb20090c014e400044cc7d1425cd990000f861c4824000005f2232c89f46c92c236ccf283c280261f08ecb4a940001d941e4444c503249d1ea064800047445b9
  | 38 => 0x80e348160980b1c035ce1d40a10f800000001f8809237a87b9455916b2584def22981a923f85e32b942cd30ccce90000777325cfd93f9439a073c4d01e444f5000000000005bf0000328000000023680003bfc0003f300000ef40003e50000000000041d8c6447f84a80000fe8000127123cd1970b20aab01884e225b09b107ac6b712b8eb9000116d29b000031f8000000002717844f34abc38400000000000ff8230cb2717609a2495c81712b096e4b549a50000f6905b11281de4c9900fd15805cccfe167400c376c000000000005303f900005fe00012a212f00961becdfb1b54a2c1225074000062918bc76b1c9000041b85a50a5ccb53528d632b3c62d3280f4c000000000009c82ae0000148800013d80000000da803c8baa0000a7822d4ab22f6527a019c000147d09c2fe48e100008400000fc31db80cc0f400000000000000066733d09b73aad07e42f80004340e37000000043d492d0000fdd008c4f229f4f9d296d1252eb8000123cf910000000000000018181a0001800025e00000000000000080946505321cd84cf00002ae078c02414a4e0336a87701e0ccdf2be00002c04e043444a6300008340b08e20051000000000000000664000012d29140000000edf0df1003156800000000004ad87c342fc00037f84e021bc9021898787342c2f10e890c600000aa00003bf2d351ad2da8230000094b1b80c52075411a00003c70a8ce81393400042600002890000177c0c70000bd10068f1b4a710c11d7c2482d8c021375112231b92b402f836c1b1c0003ad502001e81613dd065b0f503354b4422e0000a7e3de10ce00008f045a0e7d0d14fd638b11ae00b438f00000b421680004b180000000000133800027f8da907c00003884104384c00022e1099295c000466ced324d108039a479803946a516e875b1b7cc2f2fd11b619b400007180000000000219099318ec0000000c47000000047cc0000a180001df43b20000a7700000000000ee82bbca1100008f51374f7305fc9bf000044948c400031b00001fe0f360000e8327d866a23a4875423cdc126208562c687fa343c4403c106132114d2127ad2760148b6d3304bef00ac1b53aa027b47ec4da00500000c147254920658290029d09c891e0c3440a2f7c00027c0b3d00009cd3fd10dd3af0d733d144f00cc4fa8000056700010c52140d16337042300652bb305094100000000708f9c48680004134000408c0002af00003a6c03e3108898263c404226400048942fa0960700000128209102b0306c00015a8197000117c25e4000433d16e088d1294978e000000b9700000003fc4704000041a0e4800000000001dfc42a10b80002f306ef00001520000000425896f05dc000329c0000000a2b18942781168eae20891c809085e6106cc80317c0001bfc000356884f0000000000
  | 39 => 0x5cb002919f061478818782b63a4c0002c086d6479cfb200009c60001124028cf9a061c0003340000070000000000002ac4fda38ec0000000e3e0000aea40d400000000000000b3e00000001af061a319800000000001bd809000007e40e6067043c40001f04000458c0001fdd03f4240000116415300001781a6506d000000000010e000000003f980002e149800000fa2000000017c013e0000e2241580003d252c52f0463a1668dfd00ec000000000000000001c846da022400048d51024668bc50000b7b000010801dc1b42cd4c6b00000c5042c00033e81df00002453e4c000000000000000002f240004a84c291778b6c12d46624b3014241ad2ca000098a45883b34350f6b4718bbb0834d30439098c0000000423400032e003d219d1aa219837b312448e1734d3a312c22b00002570000fce00006612d58a5f0e184580000ffd0000000000125d03c4d8a0000000000107f0000000411cbe92c205d430080002a840004648ae63630516092c8c614b400044a8043120c0000bcc000325400011ec3680000d6b30f0abe2b880000000b8b0fe00000000b1600010af2d9c47213b464b0000138478ca030408905424440e461494f0000000350c0000000000328c00005a007f19049b4496cad20000cf7000081f00008ab1580de22a0800000002761c1400000011d900004f8157850b39d4723000000000c83c3047c8d53918aa600000000000bd00000000000055834b07130000363427c00000000003d7044a3ac83434adc00000000002774000013d2a00000e6000006b600006ac402505e25d83cd46bc27a468000034881fa1c54e4447b80c41f6ce6b41711d727140000000fe0000000003601f601b039908800002690e5c331cb5c227869611211433dd408416049c20000000000000000008b43a7c00034140004b6c00000000002a30072273c54e015d00747f0adb00000003114000046c0001cb4cbd154000028780002e5400022906fe0afc6ec48e099729d12a71414fbf1d500002b0d0c31a400822fc4ead0000608000000005bc35449b92b52f60b781250f0500010c203810e50000000000047f4504e66000000000006db00000003f3c0004464000165c18b24bc83800000003d08b50200c000101927e327cd6927f40000000000437c5c8101c7e8245428c000114f000070d109446f24d4ae335dcf2101783801870bb82fc031a000020b4a188a20278463148c0363ec000036fd24e20b8000000000000000c100000002ba00000000b5f089007b3eb129211f52372444c0935ecc7b49f48614a645b3474d202315c7081aec7d23ee4547044522d3a40fcb10ac5ec419854500007f528803eb0a286dc099520646b030f28583b72c24b624a406ae21706842ef4000000104c1c29213000120b1260ba10000000354c079000101
  | 40 => 0x3f239503e4514f1540d114a34cd2ae04245511b30d9006c8f7e111d00824d800028ec0002d391b42a44000362c0000e200000000b8c0868be80000dff1ded189000111245080001944000000092200000000000ed7000000000000002fd91ed122d0d23c4cf7135109a71c58c5d394825430b02e43374f6000007062a24fa700000000000fef3a64edd1bb51cd13442b5288471c37203f313709db0f442490b1456b00000002490a610001165111516a03bd060000000008940003710000000000000000004a78000447ccce485024707340000000fd1000000037d48d6293c000255c0000000ca400008f413d000028e0bec1be402511b84d229245e800001ae4ae88960b7461d0000000342428b2ad4fa0308c34c3cf87e12d182fc338516c000000026d87cd06f04a4372c89535fce3d43f0ee0000000004751993d60000360c3c6286858424e922422941dd21c0cc200006d234606a4099033709344ff3bc921812045a905b4307105069f41400001fb432904d45a3000000000012cd0b043e010f0000000000019bcad819f0000000000022c0000000000000000000000013461806b0dc489b00000001d28000302000020300002abd15b115c7f31220d32000019f00000003b48b0c00000000000452398c00000010ac182cf5f00011b03358d1a2f10633330c6a214dce98218c90a31187f91cf46de28500000e70fd238045c700010d513345fd4b64f0e3dd870b197424e253125634206161f70956121c00000003e13cc0e8238ac883000105d000000047900d33c00dee0f90bf3242054100000002d30a020000b5e18480001520349304400016480004638ea2033c2212c980003a9c00038c48b70c2c00013901ea0598a1b00004c324b8035000000000000000000b9d1acd0ad057c1491a550193c08f6e30ec5244aa4e1f0e90f6513c4bf82964c4a1284e0f360463907bc3902e9cde9490c00021608d842f50cb0434000239c5820574e4e02d8ba6436ca10348c79b41a8cf222100000001157347c00047e80002ff4f504a58000399d2422ca8bb11f68d2f005cfeb1e7405a11a80000000d9c0f544b2000069c000046d14d0737000089333140003270000032cb2805f8000017000000000000000000000000030b8000258c11704b093735652da10d849d1d1879a4858c3e364d1031e50d68183873903089bc34ecc9b412000034ac8c10000904069c0000c202d709c400016143fc0c307d03bd84ab00000002cc01d40180b931b148762dd03bb3f2000005c081413a511c3b0c441152c49f20f87bc0c04b1226bc000000000000008f80000b99000021317dc8a10454a122dd4ace1de03b900000000000000000039f00008bc0000826289c31f45404171c5cd0d1d64c730c8c4922ed4b7d00001953d482801934c322c901c51178c2d00
  | 41 => 0x26c00015dc00038440783f4cac40f786e91ae51f60000000132c00000000002e5086c000000036549fa00006981e7876f04a4ccb1665263000000008f400018ac0000000000000082d2640e1e39b80002494000336c4d308a851c000023c3e400001090733000000026e923628f473a0d1d041315829000002940000222491c00018b85bc000000028c0ab91b3c8e6245cef00ba80000239069097000006e4792283088103003fd1480c483c300002e5801c2438d2a0000b881d5ce640e6ccca441c69246443963cac1c703e899833e00000f20000000000000002561b000001b090873ed86f700006770001215090c25e000056100000000000000000000035341b10ed40003480793412c06e182481a185465f4114c542c512072aa4b8933984370eb09f8287c7ba000043505c42d6000103c48c87fe2ad90b825d0aa200011fd00012461d480004a7c43313851c318c8000144400000c0ba23b5057b00001de0000d870000542443c0002194544000000019a52393c0ca860000c05429c07c2740bcb089846622e85ce13150ef15584fd37d126119a000004a85660000a3e086cb8a14502f70000000000000000007ea0000a35358876a1024d1516a9123352412838589c735c0b87397cc1c07488d13d2cfe40d3cd6e422523a187c2f906c0000000125410fc8490000000223c000275d01a1ec115a0000b57497000022f800022cc9e22e040002da0000438c4e639585ff00000000000c760000000207400000000003a742e93ca467943d000000006d900000fb222400029e83e900008ea0dd40663ff000039c40000c88b640000f22066cab0306912d373cfdb1d845022ccc28f0000bc33c746180bd400045d86e41a312ce00005790000000195800042108af3d1c3c22a69075237ce7c3bc460f378cadd13f075011f095838b800030d10b329750b1166018c09444de1cd0bba3f84e071f750f72a491173428df945380ba1f78e5105650d31e28a5228645690d8088c2f190b6000003c2b4c806244c9ec07e437e000000026348f700012
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8be86dd1304400187ecbba260880030f197744c1102a64e31ee89822000cac62dd1304415117d0fb2260881522f21f644c1100061fbaec89822000c3c75d9130440018beebb1a6088003171d7634c1100064fba6c69822000c9c74d8d30440018deebb1260880031b1d7624c11000657ba6c49822000cac74d8930440019c8c5b8a608800335d8c714c11000672310e298220018ec829d830440018dce5b2860880031b9c8650c11000657396c81822000cce72d8c304401b1d90cb9060880031bd95720c1100063632ae41822000caf645c83044001958c8b90608800333d8d720c11003e6631ae418220008ef87d8830440131db0fb10608801eb6219300c110006e4b92601822000e386419710440018ecedb2c20880231d9d865841100565b3b6c90822000cd676d8e104400f9acec31c2088003b1188638411004e733b6c5082200287f87553650400587ce8aa6ca080030f5d154d941000e6739265b282000ccd724cb65040050f90bba2ca0800237e0d745941003c6e41ae8b2820008f8805d165040050f90eaa2ca080030fdd154594100053c402a8b28200187c87549650400399ce4992ca08003335c9325941000726a9264b28200087f87594650401187ccaba0ca080030f59574194100462f32ae63282000c5d655cc65040118dccab90ca080031b59572194100161f3a2a9b182000c3d7455363040031bf0e996c608007339c932d8c1000666b9265b182002c3e74551630400187ae8aa2c60800a3721d4358c100070eaa286b1820018dc83dc963040010ff0ab92c6080221f2157258c100047a40ae4b1820018dc874c9630400199ee4992c608002b52053258c1003e2f31aea3182007c9e635d063040011bf0eb18c608003175d56318c100064eba2c63182007cce635c8630400199ac6b90c60801e1fa1676d4c1003c6f41ced29820028be841d9530400117b083b2a6080063ba087654c1000476c10eca98200787c8759553040111b90eb1aa6080230f99574144100061eb2ae8288200887e85dda31040010fb0bbb4620800a2fa13768c4100045ec26ed1882000cd9639c2310400f1bd07bb4a0080023760f769401000c77416ed28020008ed82dda50040018eacb38ca00801f3398d720c01000666b1ae418020018f5869c43004001968e9bb22008003391cb76440100063baa6ec8802000c7554dd910040019ae65bb22008003354cb76440100063bbb6ea8802000c77761d5100400196eedba2200800335ddb73440100066bbb0e68802000dc4721cd10040019ceedb9220080032e1d3764401000674396ec8802000c7b54dd910040018f2a9bb2200800336ccb76440100066c996ec8802000c7b76dd510040018f6ec3aa20080034e1d075440100065dbb6e88802000cdb76dcd10040019b6ec39a20080033addb7244010
  | 1 => 0xb0e21ec4880029ba1443d891000536c2887b122037aea80dc762440011dd0fa0ec4880023b61f41d89100053742e83b122000a6d85d076244001c5aa9a0ec488002b3a0f41d891000566c1e83b122000e2d5450762440014dd0a20ec4880029b61441d891000667b9ee1b122037ae681dc362440014dd0ba06c4880029b61740d891000716aa481b1220008ee8710362440131db0e206c4880029ba1440d891000536c2881b122000e2d54103624400159d06206c488002b360c40d89100057340881b122000ae58110362440118f0cb386a2880031b1cb655451000656396c8a8a20008de86dcd51440018becbb9aa2881431719773545100064fb26e6a8a2000c9c64dcd5144001998c5b9aa28800237a1873545100062fb28e6a8a205dc5c651cd514400193ec839aa28800327190735451000666310e6a8a205d8de87d8d51440a11b90fb1aa288003331cb63545102846f438c6a8a20078dc8718d5144001998e431aa2880023ba1b725451000637b2ee4a8a20a2c6c65dc9514400195ec9b92a2880032b193725451000667b1ee4a8a2000ccc63dc951441531dd0fb12a28828a3b21f625451000667b9ec4a8a2000ccc73d895144001970c9b82a2880031ed9470545100065c320e0a8a20028bc849d8514400187ce9b28a28809a2f21974145100061fb2ae828a2008c3c655d05144001958c4ba0a2880022fe1f64145100545ec3ec828a2000c9e74d8c514400193ae9b18a288003279d063145100064eba0c628a2000cae74d88514400195ae9b10a2880229d21951145100069aba2a228a20018ec829db31440018dce5b2e62880031b9c865cc51000657396c998a2000cce72d8f31440011d90cb9662880031bd9572cc5100063632ae598a2000caf645cb3144001958c8b96628800333d8d72cc51003e6631ae598a20008ef87d8b31440011db0fb16628801f3618e70cc5100066db18e098a20028bc849db504400187ce9b2ea0880022f21974d41100061fb2ae9a822008c3c655d35044001958c4ba6a0880022fe1f64d41100045ec3ec9a822000c9e74d8f504400193ae9b1ea088003279d063d41100064eba0c7a822000cae74d8b504400195ae9b16a0880231d19671d41100045fc22eca8220028bc845d950440011bf06bb2a08801e3720d765411000477c12eca8220018ec825d950440018eecbb8aa0880031dd94715411003e6a31ce3982200087f855d930440110f90abb260880022fe11764c1100145e422ec98220008ef825d930440031d904bb260880021fa1b754c1100061e326ea9822056c5c63dd530440018d8c5baa60880021fa18754c1100061e320ea9822055c5c631d530440018d8c43aa60881561fa1f654c1102b43e43eca9822000c3c74d9530440ad0fd0e32a60880221f21c654c1100061e3a0ca9822000
  | 2 => 0xb65d891000536c26cbb1220008ed8799762440014dd0b32ec488002aba1265d891000556c24cbb122000ace83997624400159b0732ec4880023be1d65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000537430cbb122000c6e7619762440014db0832ec4880032b9db64d891000717b2ec9b122000e2c65d936244001c5f0bb26c4880038b21764d891000476c3cc9b122000a6e8599362440014db0b326c488002aba1264d89100056741cc9b122000acd8399362440011df0eb26c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880029ba1464d891000536c28c9b122000aae86193624400195cec326c4880038bd9464d891000716328c9b122000e2e851936244001c5b0a326c488003a960464d891000537436a9b122000a6c86d53624415d8dcedaa6c4880038bd9354d891000716326a9b122000a6e8655362440014d90caa6c4882b71b9d954d891000717b22a9b122000e2c64553624400159d0db9ec488003339db73d891000727b2ee7b122000e4c65dcf6244001d1ec9b9ec488003a319373d891000567430e7b122000cce761cf6244001c9eca39ec4880039319473d891000747b20e7b122000e8c641cf624400199cedb1ec48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec48800393d5363d891000726aa6c7b1220008ed8798f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f624400159d0731ec4880023be1d63d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000567430c7b122000cce7618f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001c9ea831ec4880039355063d89100075232483b122000f255450762440135d50db86c48800372dcf70d891000557424ebb122000aad849d7624400159d073aec488002b360e75d891000567c1aebb122000acc835d762440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d3624400159f06ba6c488002b320d74d891000537428e9b122000a6d851d362441595cd023a6c488002b960474d891055d36c2ca9b122000e2f549536244001c5f08aa6c4880038bdd154d8910007163a2a9b1220aaa6e85153624400199eebb9ec488003335d773d891000667ba6e7b122000ccd74dcf6244001c9ea9b9ec4880039355373d89100066738ee7b122000ccc71dcf624400199ae1b9ec488002b3a0e73d891000567438e7b122000cce871cf6244001c9ea839ec4880039355073d891000727a9ca7b1220008ee8714f62440011db0e29ec488002aba1053d891000556c20a7b122000a6e85d0f62440014db0ba1ec4880038b55343d891000716aa287b1220008ee8710f62440011d
  | 3 => 0x831a2000c5f545c863440018baa8b90c68801e37e097218d1003e67c12e431a20078de8794863440011bb0f290c688003335ca5218d1000666b92a431a20078de8714863440011bb0e290c688002a7a105218d100054ec20a431a2000a5e85d0863440014bb0ba10c688003875534218d100056b40e8431a2000ad581d08634400f1bd0f210c6880023761e4218d1000666b948431a2000e1d54508634400199ae4a10c68801e37a1c4218d100046ec388431a2000a5e8510863440014bb0a210c68801e37a1f4118d100046ec3e8231a2000a5e85d0463440014bb0ba08c688003875534118d10005674168231a2000acd82d046344001c3aa8a08c68800297a144118d100052ec288231a20078de87c8463440011bb0f908c688003335ca2118d1003c6f4384231a20008dd8708463440014bd0a108c688002976142118d100054f4204231a2000a9d84084634400199ae4108c688002b6a002118d100056cc004231a2000a5e85d0063440014bb0ba00c688003875524018d1003c6f4388031a20008dd8710063440014bd0a200c688002976144018d100070eaa08031a2000ace82100634400159b04200c688002b5a044018d100056ac088031a20078de87c8063440011bb0f900c68800297a172018d100052ec2e4031a2000a9e84c80634400153b09900c688003335cb2018d1000666b924031a2000ad78148063440015a902900c68801e37a1c2018d100046ec384031a2000a5f8544063440014b90a880c688002a7e111018d100054e4222031a200787c855db534400117f08bb6a68800a2f21176d4d1000477c12eda9a20018ec825db53440014bb0bb1ea6880022fe117694d100145e422ed29a20078dc835da53440011df04bb4a6880063b2097694d100052ec1ecb29a2000a5e86d4e53440114b90da9ca688003179db5394d1003e2e3b6a729a2000e1f64d4e534414fc38c9a9ca68829b9318b5394d100145f426eca9a20008bd84dd953440031dd05bb2a6880023b60b7654d100045fc22eca9a20028bc845d953440011df04bb2a6880063b2097654d1003c3f43ecaa9a20088de87d8d5344005179093b0a6880063b20a7614d100045fc22ec29a20028bc845d853440011df04bb0a6880063b2097614d100061f3a6ca29a2000c6e72d9453440011790cba0a6880030fd957414d100461e32ae829a2007c9c635d05344001958c4ba0a6880022fe1f6414d100045ec3ec829a2000cae72d90534400193ce9b18a688003275d36314d1000667396c629a20008ec865c853440018decab90a6880231b1957214d1000657b22e429a2000cac645c8534400199ec6b90a68801f3318d7214d100463a32ce229a2007cd4639c4534400f1e90cb88a68801f3518d7114d100463c32ce029a2007cd8639c0534400f1f10cb80a6880031b9d
  | 4 => 0x34415b8d8e4aa2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000637aa6e4b1a2000c6d54dc9634400199f07b92c6880021fe157258d100443e42ae4b1a20008bf845c9634400517908b92c68800237e0d7258d100047bc0ae4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440011bd0f992c68800317dd73258d105a62e3ae64b1a2000c9f74cc96344167938e9992c68800333dcb3258d1000e6639664b1a20018dc874c963440018beea992c6882cb171d53258d100064fba264b1a20b1c9c744c9634400199ee4992c688007331c93258d1000672396e2b1a20008df8758c63440014bf0ab18c688002972156318d100054fc22c631a2000a9c8458c634400159f04b18c688002b32096318d100046ec14ec31a2000c5e76d9463440014bb09b28c6880023761e6518d100054f424ca31a2000a9d84994634400159d05328c688002b360a6518d100046fc3aca31a2000a9f84594634400153908b28c688002b3e096518d1000566412ca31a2000c5e7619463440014bb08328c688003279db6418d100070fb2ec831a2000e1c65d906344001c3f0bb20c688003872176418d100046ec3cc831a2000a5e8599063440014bb0b320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc8259063440014bd0a320c688002976146418d100064f3b0c831a2000e1f651906344001c38ca320c68800387a146418d100070ec28c831a2000e958119063440014bd0daa0c6880029721b5418d100062f3b6a831a2000e1f64d506344001c38c9aa0c68800297a195418d100052e432a831a2000c5e765506344001c3ec8aa0c688003871915418d100046f436e431a2000c5f65dc863440018b8cbb90c68800327d937218d100064e326e431a2000c5f655c863440018b8cab90c68800327d917218d100064e322e431a20008df87d88634400199ae5b10c6880023761e6218d100052f42cc431a2000a5d85988634400153d09310c688002a76126218d100046fc3ac431a2000a5f8558863440014b90ab10c688002a7e116218d100054e422c431a20008dd87188634400199ae4310c68800393d946218d1000726328c431a2000e8f641886344001d18c8310c6880033361c6218d1000727aa0c431a2000e4d541886344001d9300310c688003a51924118d10007623148231a2000f15545046344001d88c4a08c688003b218a2018d10006e4b924031a20afc5f72d5063441614bb0b2a0c68800387d525418d100070fc22a831a20b0e1e745506344161c3ae8aa0c6882c317dc95418d1057d2f428a
  | 5 => 0x8002a7a1052d8d100054ec20a5b1a2000a5e85d0b63440014bb0ba16c6880038755342d8d100046f43c85b1a20008dd8790b634400199ee5216c6880038755142d8d1000667b9285b1a20008de8710b63440011bb0e216c68800297a1442d8d100052ec2885b1a2000acf825c7634400159904b8ec68800237a1f41d8d100046ec3e83b1a2000a5e85d0763440014bb0ba0ec6880038755341d8d100056741683b1a2000acd82d076344001c3aa8a0ec68800297a1441d8d100052ec2883b1a20008de87c8763440011bb0f90ec68800237a1c21d8d100046ec3843b1a2000a5e8508763440014bb0a10ec688002a7a1021d8d100054ec2043b1a2000ada8008763440015b30010ec68800297a1770d8d100052ec2ee1b1a2000a9e84dc3634400153b09b86c68800297a1740d8d100052ec2e81b1a2000e1d5490363440011bd0e206c6880023761c40d8d100052f42881b1a2000a5d851036344001c3aa8206c688002b3a0840d8d1000566c1081b1a2000ad68110363440015ab02206c68800237a1f20d8d100046ec3e41b1a2000a5e85c8363440014bb0b906c688002a7a1320d8d100054ec2641b1a2000ccf72c83634400199ee4906c68800237a1c20d8d100046ec3841b1a2007c5c639d6634400f8b8c6bacc6880030f9d36598d1000637396cb31a2000c3e7419663440018dce432cc6880030fd957498d100061e32ae931a2007c9c635d2634400187cebb24c6880030f5d76498d1000657396c931a2000c3e75192634400187aea324c6880032b9c86498d100062f3aec731a2000c5d75d8e634400193ce9b1cc688003275d36398d1000667396c731a2000c6f655ca63440018d8cab94c6880032bd917298d1000656322e531a2000ccf635ca634400f998c6b94c6880031b9d46298d1000636ba8c531a2000cae7418a634400195ae8314c6880021fa1f6558d100061e3a6cab1a2000c6c72d9563440010fd0e32ac6880030f1d06558d1000636390cab1a20028be86dd1634400187ecbba2c6880030f1977458d100045f43ec8b1a2000c3f75d916344001878ebb22c6880032b1cb6458d100045f438c8b1a2000c3f751916344001878ea322c6880032b1c86458d1000c77436e4b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a2000c6f7518963440018d8ea312c6880032bdd06258d10006563a0c4b1a200087d84dd5634400187eebba2c6880030f1d77458d100061fc2ee8b1a2000c3c85dd163440010ff0aba2c6880221f2157458d100046fc1ae8b1a20008ef825d163440031d904ba2c6880030fdd47458d100061e3a8e8b1a200087e87d5163440110f90faa2c6880030fdd35458d100161e3a6a8b1a20aec6c72d5163440010fd0eaa2c6880021f21d5458d100061fba2a8b1a2002c3c745516
  | 6 => 0x74729265b222000e8d524cb644416b53d06196c8880030fdd771d91101c55d406e3b222000a9e83c87644400153b0790ec888003a34ca21d91100045f43843b22200a8bd87087644400147d0a10ec8880028f61421d91100054f41843b222000a9d830876444001d1a6410ec888002aea0021d91100055cc0043b222038ab681dc3644400117d0f906c8880022f61f20d91100051f42e41b222000a3d85c83644400153d07906c888002a760f20d91100074699641b222000e8d32483644400153d06106c888002a760c20d91100061fba2a9b1a2002c3c7455363440014bd0ba1ec6880029761743d8d100070eaa687b1a20028df8750f6344001c3aa8a1ec68800297a1443d8d100052ec2887b1a2000ace8210f634400159b0421ec68800333dcb32d8d1000c6fc3a65b1a2000ccd724cb63440014bb09b2ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec6880029761065d8d100070fb2ec9b1a2000e1c65d936344001c3f0bb26c6880038721764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100052f428c9b1a2000a5d851936344001c3eca326c6880038719464d8d100070f428c9b1a2000e1d851936344001d2b02326c68800297a1b54d8d100052e436a9b1a2000e1f64d536344001c38c9aa6c68800297a1954d8d100052e432a9b1a2000e1f645536344001c38c8aa6c68800317d9772d8d100062e32ee5b1a2000c9f64dcb6344001938c9b96c68800317d9572d8d100062e32ae5b1a2000c9f645cb6344001938c8b96c688003335cb62d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d100052fc2ac5b1a2000a5c8558b634400153f08b16c688002a721162d8d1000666b90c5b1a2000e4f6518b6344001c98ca316c688003a3d9062d8d1000746320c5b1a2000ccd8718b6344001c9ea8316c6880039355062d8d1000764c00c5b1a2000e94649076344001e2aa8a0ec688003b218a20d8d10006e5b9241b1a2000a9e849d7634400153b093aec688002b3a0a75d8d1000566c14ebb1a2000c5d751d763440014bd0b3a6c6880029761674d8d1000567414e9b1a2000acd829d363440014bd0a3a6c6880029761474d8d100056b408e9b1a2000ad5811d36344001c3ea92a6c68800387e1154d8d100070fba2a9b1a2000e1c7455363440018bea9b96c6880031755372d8d100062faa2e5b1a2000c5d545cb634400199f04b96c688002b6a0072d8d100056cc00e5b1a20008de8794b63440011bb0f296c68800333dca52d8d1000667b92a5b1a20008de8714b63440011bb0e296c68
  | 7 => 0x7d87d04654400187ae9a08ca8800297a0f41195100052ec1e8232a2000a6e82d0465440014db05a08ca880030f5d141195100053dc028232a2000a788050465440110fd0e208ca880021f61c41195100052f41e4232a2000a5d83c846544001c9a65108ca880221fa1c21195100043ec384232a2000a3e84084654400147b08108ca8800297a0c21195100052ec184232a2000e4d3208465440014f500108ca880029e60021195100443f43e8032a200087d87d00654400187ae9200ca880221fa1c40195100043ec388032a2000c3d7410065440014bd06200ca880029760c4019510005374108032a2000a6d8210065440014ed02200ca880029d60440195100443f43e4032a200087d87c80654400147d09900ca880028f61320195100052f41e4032a2000a5d83c806544001c9a65900ca88003934c920195100052f4184032a2000a5d83080654400147d0dbaec8880030f9db75d91100051f430ebb222000c3e761d7644400187cedb2ec8880022f61e65d91100051f42ccbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb2220008bf87597644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147d0c32ec8880030f9d865d91100045ec3cc5b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b2220008bf8758b644400147f0ab16c8880028f21562d91100054fc1ac5b222000a9c8358b644400153d06316c888002a760c62d911000717b28c5b222000e2c6518b6444001c5eea316c8880038b1d462d911000747418c5b222000e8d8318b6444001d5300316c888002a7a1b32d911059e4f3b665b222000e1f65ccb6444001c38cb996c888003a3d8b32d91100074631665b222000a9c864cb644416393cec996c88800387d9532d91100070e32a65b222000e8f624cb6444001d18c4996c88802aada1b71d91100069bbaee3b222000ea8628836444001f1264906c8880030f5c775d91100061f386ebb222000c3c70dd7644400147d0b3aec8880030f5d475d91100051f438ebb222000c3e871d7644400187eebb9ec8880028fa1673d91100051ec2ce7b222000aae829cf644400155b0539ec8880028fe1573d91100051e42ae7b222000c3f755cf644400187eebb96c8880028fa1672d91100051ec2ce5b222000a9e839cb644400153b07396c8880028fe1572d91100051e42ae5b222000c3f755cb644400153d06396c888002a760c72d91105bd5d400e5b222000ab9801cb644400153d07296c888002a760e52d91100045f438a5b2220008bd8714b644400153d06296c888002a760c52d91100070fbae65b222000e1c75ccb644416d53b07196c88800387dd532d91100070e3aa65b222000e8f824cb6444001d1ee4996c888003a31c932d91100
  | 8 => 0xeaa2ca880030fdd154595100161e3a2a8b2a20b0c5c73551654415b8d8e4aa2ca8800317dd773595100064fba6e6b2a2000c9c74dcd65440018bea9b9aca880031755373595100046ec16e6b2a2000c5f751cd654400193ee839aca88003271d0735951000637baee4b2a2000caf74dc96544001958e9b92ca8800333dcf72595100066639ee4b2a2000c6f54dc965440018daa9b92ca8800333e0f72595100066641ee4b2a200087f855c9654400117f08b92ca8800a2f21172595100046fc1ae4b2a20078dc835c965440018deea392ca880032bdd07259510006563a0e4b2a2000ccf731c96544001998e6392ca8800237a1f325951003c6e43e64b2a2000c9f74cc96544167938e9992ca8800333dcb325951000e6639664b2a20008de874c965440011b90e992ca8800327dd1325951058e4e3a264b2a2000ccf724c96544003998e4992ca880032e1d370595100043fc3aca32a2000a3f84594654400147908b28ca8800297e0d65195100052e41aca32a2000a6f8259465440014d904b28ca880021f61276195100043f436e832a200087f87d90654400187ae9b20ca880021f61e64195100052f41cc832a2000a5d8399065440014dd05320ca880029b60a64195100043fc3ac832a2000a5f8359065440014b906b20ca880029be09641951000536412c832a200087d87190654400187ae8320ca880030f61c64195100071ac08c832a200087d87988654400147d09310ca880028f61262195100052f41cc432a2000a5d8398865440010ff0eb10ca880028fe1162195100051e422c432a2000a5f8358865440014b906b10ca8800297a0c62195100052ec18c432a2000e2c6418865440018dee8310ca880031b5d0621951000727418c432a2000e4d831886544001cd300310ca8800297a1b32195100062f3b66432a2000e1c64cc86544001c9ec5990ca880039318b32195100052e4326432a2000c5e764c86544001c38c8990ca8800393d893219510007263126432a2000e34649046544001a6ae8a08ca880038e1922019510007343144032a2000e38644806544001e9264900ca880221fe1174195100461fc22e832a200887e87d0c65440010fb0fa18ca880030f5d343195100061eba28632a200887e8710c65440010fb0e218ca880029ba08431951000536c108632a200887e87d0865440010fb0fa10ca880030f5d342195100052f41c8432a2000a5d8390865440014f501210ca880029e60242195100061eba28432a200887e8710865440010fb0e210ca8800297a0c42195100052ec188432a20b4c5f74cc865440018bae9990ca882ca9760e32195105962fba26432a2000c5d744c86544001c9f04990ca882cb939c9321951059726b926432a2000e4e424c86544001c9a84990ca882d297a0c32195100443f43e8232a20008
  | 9 => 0x32d95100071a32483b2a2000d37745076544001c68c8a0eca880039a18a20d95100073431241b2a2000f4932483654400187f08ba6ca880030f5d074d95100053b408e9b2a2000a75811d3654400147d0939eca880028f61273d951000537414e7b2a2000a6d829cf65440018bae639eca880021fa1f43d95100043ec3e87b2a2000c3f74d0f654400187ee8a1eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca880028fa1272d95100051ec24e5b2a2000a5e839cb65440014bb07396ca8800297a0c72d95100052ec18e5b2a2000a7a801cb65440014f300396ca880021fa1f42d95100043ec3e85b2a2000c3f74d0b65440014bd07216ca880029760e42d95100061fba285b2a200087e8710b65440010fb0e216ca8800297a0c42d95100052ec1885b2a2000c5f74ccb65440018bae9996ca8800317dd132d95100062eba265b2a2000e4f824cb6544001c9ee4996ca88003931c932d95100072721265b2a2000e4d424cb65440014bd07b8eca880029760f71d951000537416e3b2a2000a6d82dc765440010fd0fa0eca880021f61f41d95100061fba683b2a2000a5e83d0765440014bb07a0eca880029ba0b41d951000536c1683b2a2000c3f7450765440010fd0e20eca880021f61c41d95100052f41e43b2a2000a5d83c876544001c9a6510eca880021fa1c21d95100043ec3843b2a2000a3e84087654400147b0810eca8800297a0c21d95100052ec1843b2a2000e4d3208765440014f50010eca880029e60021d95100051fc22e1b2a2000a3c845c365440010fd0fa06ca880021f61f40d95100043f43881b2a200087d8710365440014bd06206ca880029760c40d95100053741081b2a2000a6d8210365440014ed02206ca880029d60440d95100043f43e41b2a200087d87c83654400147d09906ca880028f61320d95100052f41e41b2a2000a5d83c836544001c9a65906ca88003934c920d95100052f41841b2a2000a5d83083654400187ce9b2cca880031b9cb65995100061fb2ae932a2008c3c655d2654400195ce4324ca8800317d9673995100462e32ce732a2000c9c649ce65440018becab9cca880231719573995100064e322e732a2000c6f655ca65440118d8cab94ca880032b1917299510006573a0c532a2000cad7418a654400199ce6314ca88003335cc629951000656390c8b2a2000c9c64dcd6544001938c839aca880032b193725951000657ba0c4b2a2000cac74189654400199ee6312ca88003331cc62595100061fbaee8b2a2000c3f85dd165440010ff0aba2ca8800237e0d745951003c6e41ae8b2a20008ef825d165440031d904ba2ca880023ee0174595100061fba8e8b2a200087e87d51654400187ee9aa2ca8800b0f1d3545951057e2e39ea8b2a20aec6c72d5165440050f9
  | 10 => 0xa86200087d87d9450c40011bb0fb18618800333d8d720c31003e6631ae418620078de83dd365840011bb07ba6cb080063ba0b74d961000476c16e9b2c20afc5e73d53658415d8dce5aa6cb0800a1fe1d54d96100061eba2a9b2c20b0c5e73553658415b8dce4aa6cb0800317d5173d96100062eaa2e7b2c20008df825cf658400f1bd07b96cb080023760f72d96100066739ce5b2c2000ccd739cb658400199ce6b96cb08003335cd72d961000637aa2e5b2c2000c6d545cb658400199d06b96cb080033360d72d961000e37396a5b2c200187f8754b65840038dce4a96cb0801e37e1f32d96100046ec3e65b2c2001cce72ccb658400199ae5996cb0800237e1d32d96100046ec3a65b2c2001cce724cb658400199ae4996cb080039354932d96100061fb2ae932c2008c3c655d265840050f90eaa2cb080030fdd154596100161e3a2a8b2c2001cce724c9658400199ae4992cb080021fe1d65196100061fba2a9b1c2002c3c7455363840110fd0bb96c7080021f61772d8e1000c6fc3a65b1c2001cce724cb638400199ae4996c708002b520532d8e100061fba2a8b1c2002c3c7455163840051b90ea1ac70800b271d14358e100070eaa286b1c20018dc874c9638400199ee4992c70800237e1d6318e1003e6731ae431c2000ccd635c863840031dd053b6a7080023b60a76d4e100052fc2ac7a9c20018ee829d953840011db053b2a70801f2798d7414e100064eba2c629c2007cce635c8538400199ac6b90a70801e3e61a7014e1003e6d31ce029c200087d87d94518400187ecaba0a3080230f195741461003e6731ae598c2000ccd635cb31840011bb0fb1863080231d995711421003e6731ae41842000ccd635c83084001b92e498061080030fdd354d95100161e3a6a9b2a2000c3d7495365440014eb032a6ca8800a1fe1d54d95100061eba2a9b2a2000a5e8394b65440014bb07296ca880061fe1d52d95100051f420a5b2a2000a3d8414b65440014bd06296ca880029760c52d951000667b9265b2a2001ccc724cb6544001c9ca4996ca880039354932d95100061eba6c9b2a2000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a2000c3d74193654400187b0e326ca880038d60464d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d95100052f418c5b2a2000a5d8318b6544001c58c8316ca880031bdd062d951000636ba0c5b2a2000e4e8318b6544001c9b06316ca880039a60062d95100052f43665b2a2000e1c64ccb6544001c9ec5996ca880039318b32d95100052e43265b2a2000e1c644cb6544001c9ec4996ca8800393189
  | 11 => 0xc00587ce8aa2c2180030f5d154584300043fc2ae4b08600887c855c9610c00f1b906b92c21800333dc9325843000e6639264b086000ad4814c9610c00f1e90ea0ac2180038d551415843003e6739ac5a886000ccd7358b510c0031d905bb2a21814237e0d765443000477c12eca8860018ec825d9510c00199cc5b9aa2180023b61b72544300047743ac4a8860008ec87589510c00199ee6b12a21801f331cd625443003e6a39cc2a886000cae625d0510c00195ce8b10a2180032b5d162144302766743ac51886000ccd8758a310c001c9ea8b14621800393551628c43003e6738ac51886007ec67158a310c00199ac4b8462180032b98974d4030006573a2c5a806000cad7458b500c00f99ce6b14a018003335cd629403003e6739ac42806000ccd73588500c001938e9bb2601800317d53764c0300062eaa6ec98060008df82dd9300c0011bb05bb2601800317ddb754c0300062fbb0ea9806000d1c741d5300c00193eedba2601800333a1d624c03025666c3ac49806000e4f75589300c001c98eab126018003a3dd1624c030007463a2c49806000e4f54589300c001c9aa8b12601801f33dc1624c03003f65b82c49806000ccd621c5300c00f1bd07ba6cb880023760f74d97100143fc3aa9b2e2002c3e7455365c400187ae8aa6cb880029e20154d971000667b9265b2e2001ccc724cb65c40050f90eaa2cb880030fdd1545971000c3e43aa4b2e2001c6c7254965c400199ee4992cb88007331c9325971000726a9264b2e200087f8759465c401187ccaba0cb880030f59574197100043fc22ebb1e200887e85dd363c40010fb0bba6c7880030f9d674d8f100061ebace9b1e2000c3e755d363c400187aeaba6c7880030fa1574d8f100061ec2ae9b1e200887f87d5363c40010fb0faa6c78800b0f9d354d8f100061eba6a9b1e200087f8755363c40010fb0eaa6c78800b0f9d154d8f100061eba2a9b1e2002c9e7490f63c40051bf0ea1ec78800b279d143d8f100070eaa287b1e200887e85dcb63c40010fb0bb96c78800a2fa1372d8f100045ec26e5b1e20b4c5e75ccb63c40018baeb996c7882cf279d332d8f100064eba665b1e20018df874cb63c41658bcea996c788003175d532d8f1058e4f3a265b1e2000c9d744cb63c400199ae4996c78800333d8d7298f1003e6631ae531e2002c3e7455163c400187ae8aa2c7880063721d3258f1000667b9264b1e2001ccc724c963c40011bf0eb18c78800a2fa127694f100045ec24ed29e2000a5f8359653c400517d093b2a7880022f6127654f100461f32ae829e2000c3d655d053c40118dccab90a7880031b5957214f1003c7ac34e229e2008c76659c453c401187ccaba0a3880030f59574147100069aba2a228e2007cda635c031c401187ccaba6a1880030f59574d43100463b32ce3
  | 12 => 0x32b1cb64545300062fb2ee6a8a6050c5c65dcd514c00193ec9b9aa29800327193735453000637b2ee4a8a60a2c6c65dc9514c00195ec9b92a2980032b19372545300145e424ec28a60008bf845d8514c00517908bb0a2980030f9d365145300045e432e828a6000c3f655d0514c011878caba0a2980022fe1f64145300045ec3ec828a6008c78659c0514c00187ce9b2ea0982a22f21974d41300061fb2ae9a826008c3c655d3504c0a917f0fb26a0980022f61f64d41302b53d436a12826000e3b64d42504c00117f08bb2a09800a2f21176541302b62e39ecaa826000c5f65dcd504c001938c9b9aa09815b179db658c1302b72db06cb1826008c5e76196304c001c38c832c6098153279db648c13003c6e41ae8b2860008f8805d1650c00f0f90eaa2ca180030fdd154594300053c402a8b286001cce724c9650c00517d0838aca180022f610715943003d6741eeab10600dacd83dd5620c00199ae7baac418003335cd755883000557420eab106000aad841d5620c00f59d063aac418036b360c755883003d6741ee8b10600dacd83dd1620c00199ae7ba2c4180029ba16745883000536c2ce8b106000ccd735d1620c0014dd0a3a2c4180029b614745883003d67418e8b10600dacd831d1620c15fc9ce7aa2c4182e7935cf545883057f2618ea8b1060afe4f30d51620c1614db0b2a2c4180038bd52545883000567c1aa8b106007acc83551620c0015d700aa2c418002ba201545883000717c22a8b106000e2e74551620c001c5ae8aa2c41800393e0d54588305872641aa8b1060b0e4e73551620c171c9ae6aa2c4182c38bd0d545883058716a1aa8b1060b0e4c31551620c001cd700aa2c4180039a201545883058727982a8b1060afa6e85151620c00f59d07b8ac418036b360f715883003d6641ce2b106000a6f855c5620c0014d90ab8ac41813ab3e0d715883003d6641ae2b106000a6e851c5620c0014db0a38ac418002aba10715883000556c20e2b106007ace831c5620c01b59b0638ac418003335cc715883000575400e2b10600dae9801c5620c0011dd0fa0ac4180023b61f41588300053742e82b106000a6d85d05620c001c5aa9a0ac41801eb3a0f415883000566c1e82b106000e2d54505620c00159f06a0ac41801eb320d41588300053742882b106000a6d85105620c09559b07382c4180029ba17405883000536c2e80b106000e2d54901620c00f59d07202c418002b360e40588300047743880b1060008ed87101620c0014dd0a202c4180029b614405883000716aa080b106007ace83101620c00159b06202c418002b9a04405883000572c0880b1060008ef825d6610c0031d904bacc21800b0f9d154984300061eba2a93086000ccf724ca610c003998e4994c21801e3d61e41984300071aaa28330860078dc835d161
  | 13 => 0x70fb2e65b226000e1c65ccb644c16393cec996c89800387d9532d91300070e32a65b226000e8f624cb644c001d18c4996c8980030f5cf75d91300061f386ebb226000c3c70dd7644c00147d0b3aec8980030f5d475d91300051f438ebb226000c3e871d7644c00187eebb9ec89812eaea0373d91300061fbaee5b226000a3e859cb644c00147b0b396c898152a7a0e72d91300054ec1ce5b226000a3f855cb644c0014790ab96c8980030fdd572d91302a54f418e5b226000a9d831cb644c0a953d07296c898002a760e52d91300045f438a5b2260008bd8714b644c0a953d06296c898002a760c52d91300070fbae65b226000e1c75ccb644c17553b07196c898153a30c932d91300070fbaa65b226000e1c754cb644c0a953f04996c898153a3e0932d913000747b9265b226000e8c724cb644c001d1ca4996c898003a354932d91300061fbaee3b226000a3e859c7644c00147b0b38ec8980028fe1571d91300051e42ae3b226000c3f755c7644c00153f06b8ec898152a720d71d913000557c12e3b226000aac825c7644c0a953d0790ec898002a760f21d91300074699443b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b226054a9e83087644c00153b0610ec898003a34c821d91300055d40043b226000ab980087644c0a917d0f906c8980022f61f20d91300051f42e41b226000a3d85c83644c0a953d07906c898002a760f20d91300074699641b226000e8d32483644c0a953d06106c898002a760c20d91302b62f29ceda9a6007a5c83d97534c0a9c3ca7b26a6980231e19670d4d300065c326e0a9a6000c7b651c1534c001970c8382a6980030fdd154d85300161e3a2a9b0a6001cce724cb614c00199ae4996c298002b560c21d85300076299043b0a6000af180087614c00187ce9b2cc2980030f9d065985300061fb2ae930a6000c3c655d2614c00187cebb24c2980030f5d764985300061f3a8c930a6000c3d75192614c0010fd0fb2ac2980030f1d3655853000636396cab0a600087e87195614c001878e832ac2980031b1c865585300145f436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c001958e4322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980023de1d611853000572412c230a6002c3e74550614c00187ae8aa0c29800387551431853000667b926430a6000ad583c84614c001d8a64108c2980022fe1176d45300145e422eda8a60008bf845da514c00517908bb4a29800a2fa1376545300045ec26eca8a60018ee829d9514c0011db053b2a29801e3720c76545302b62e39ecaa8a6000c6c72d95514c0a9938e7b22a298
  | 14 => 0xc74cc9654c0031b90e992ca9800327dd1325953058e4e3a264b2a6000ccf724c9654c001970e9b82ca980021fe1d65195300051fc22ca32a6000a3c84594654c0010fb093b0ca980021fa1b74195300043fc3ec832a6000c3d74d90654c0010fb0f320ca980021fe1d64195300043ec38c832a6000c3d74190654c0014dd04320ca980029b60864195300061ec38c832a6000e1d83190654c001c5d04320ca980038b60864195305df1d980c832a60bbe3830190654c0014bd0d218ca980038719243195300068eba28632a6000e1c6450c654c0010fb0f310ca980028fa1262195300051ec24c432a600087f87588654c00147f08b10ca980028f21162195300053bc0ac432a6000a7481588654c0ad8bced990ca980038719332195300062f3b26432a6000e1c644c8654c001c9ec4990ca980221fe1174195300461fc22e832a600887e87d0c654c0010fb0fa18ca980030f5d343195300061eba28632a6000a7b8050c654c0014f100a18ca980221fa1f42195300043ec3e8432a6000c3d74d08654c0ab4bd07210ca980029760e42195300061eba28432a600887e87108654c0010fb0e210ca9815697a0c42195300052ec188432a60b4c5f74cc8654c0018bae9990ca982ca9760e32195305962fba26432a6000c5d744c8654c0ab4bf04990ca9815793e093219530597273926432a60b2e4d724c8654c001c9c84990ca980039350932195300443f43e8232a600087d87d04654c00187ae9a08ca9815697a0f41195300052ec1e8232a6000a6e82d04654c0014db05a08ca980030f5d141195300443f4388232a600087d87104654c0ab4bd07908ca980029760f2119530007269944232a600887e87084654c0010fb0e108ca980028fa1021195300051ec204232a6055a5e83084654c0014bb06108ca98003934c821195300053d4004232a6000a7980084654c0110fd0fa00ca980021f61f40195300061eba48032a6000a5f83500654c0ab4b906a00ca980221fa1c40195300043ec388032a6000c3d74100654c0ab4bd06200ca980029760c4019530005374108032a6000a6d82100654c0014ed02200ca980029d60440195300071ca008032a600887e87c80654c0010fb0f900ca980028fa1320195300051ec264032a6055a5e83c80654c0014bb07900ca98003934cb2019530007269924032a6055a5e83080654c0014bb06100ca980028fa1b75d91300061f3b6ebb226000a3e861d7644c00187cec3aec8980030f9db65d91300045ec3ccbb226000a3e85997644c00117f0eb2ec8980028fa1865d91300061f3b0cbb226011a9e86dcf644c001a3eebb9ec8980022f61e62d91300051f42cc5b226000a3d8598b644c00117f0eb16c8980028fe1562d91300051e42ac5b226000ab78158b644c00156902b16c8982a3279db32d913000
  | 15 => 0xea96ca980071b9c952d95300051f420a5b2a6000a3d8414b654c0014bb06296ca9800333dc932d95300072729265b2a6000e4d524cb654c00517d0938eca980022f61271d95300061eba6c9b2a6000c3d74193654c0014dd04326ca980029b60864d95300061ec38c9b2a6000e1d83193654c001c5d04326ca980038b60864d95300070e32487b2a6000d1f7450f654c001c38c8a1eca980028fa1262d95300051ec24c5b2a6000a3f8458b654c00147908b16ca980029de0562d95300053a40ac5b2a6000e1c64ccb654c001c38c8996ca9800393d8932d95300072631265b2a6000c3f845d3654c00187ae83a6ca9815a97a0c74d95300052ec18e9b2a6000a6e821d3654c0014db043a6ca980021fa1f43d95300043ec3e87b2a6000c3f74d0f654c00187ee8a1eca980028fa1272d95300051ec24e5b2a6056a5e839cb654c0014bb07396ca980031bdca72d95302b52f418e5b2a6000a5d831cb654c0010fd0fa16ca980021f61f42d95300061fba685b2a6056a5e8390b654c0014bb07216ca980030fdd142d95300043f43885b2a600087d8710b654c0ad4bd06216ca980029760c42d95300062fba665b2a6000c5d74ccb654c0adc9864996ca9800317dd132d95300062eba265b2a6056e4f824cb654c001c9ee4996ca98003931c932d95300072721265b2a6000e4d424cb654c0014bb07b8eca980029ba0b71d953000536c16e3b2a6000a3e849c7654c00147b0938eca980021fa1f41d95300043ec3e83b2a6000c3f74d07654c0ad4bd07a0eca980029760f41d95300053741683b2a6000a6d82d07654c00187ee8a0eca980021fa1c41d95300043ec3883b2a6056a5e83c87654c0014bb0790eca98003934ca21d95300043f43843b2a600087d87087654c00147d0810eca980028f61021d95302b52f41843b2a6000a5d83087654c001c9a6410eca980029ea0021d95300053cc0043b2a6000a3f845c3654c00147908b86ca9815a1fa1f40d95300043ec3e81b2a600087e87103654c0010fb0e206ca9815a97a0c40d95300052ec1881b2a6000a6e82103654c0014db04206ca980029da0440d95300053ac0881b2a605687e87c83654c0010fb0f906ca980028fa1320d95300051ec2641b2a6056a5e83c83654c0014bb07906ca98003934cb20d95300072699241b2a6056a5e83083654c0014bb06106ca980030f9d365995300061fb2ae932a6008c3c655d2654c00187eebba2ca980030fe1774595300043fc2ae8b2a60008df835d1654c0011f700ba2ca980030fdd474595300043f43ea8b2a6000c3f74d51654c005878e9aa2ca9800a1f21d54595300061fba2a8b2a6002c3c74551654c001938e9b9aca980021fe1572595300045fc22e4b2a60028bc845c9654c0011ef02b92ca980023d20572595300064fba664b2a60b3c9
  | 16 => 0x45845056e36392a8b08a000a748155161140a18b8ebb9ac2281439514773584502862faa6e6b08a000c5d54dcd61140011bb05b9ac228177171d473584502ef2a288e6b08a0018ee87dc961141458d8ebb92c22800333dcf72584500066639ee4b08a0a2e6451dc961141458dea9b92c2280031b553725845000667c1ee4b08a000ccc83dc961140110f90ab92c22800237e0d725845003c6e41ae4b08a0a9c6c751c9611400199ee6392c228003331cc725845054f32288e4b08a001c6c7254961140014e902a92c22800237a1f325845003c6e43e64b08a000ccf72cc96114003998e5992c2282d39514732584500046f43a64b08a0008dc874c9611400199ee4992c228007331c9325845000726a9264b08a0b2e54514c961140114e90b20ac22800a3d21d41584500453a42a82b08a000e355450561140015e100a0ac2280229d216215845000e7239442b08a0a2e67528856114001d8a6510ac2280063d21d21584500453a42a42b08a008c76715da511400127f08b84a22817637e1d63cc45003e6731ae5988a000ccd635cb311400f5a906b0c62280023be09764c45000c76412ec988a008c747558531140ab8b8a6bb062280021fe1376540500043ec26eca80a000c5f32dd950140018ba65bb2a02801e1f21d54597300061fba2a8b2e6000a7b8055165cc0030f90ea92cb9800333dc9325973000726a9264b2e6002c3e7455261cc00187ae8aa4c39800b279d143987300070eaa28730e6000ccd724ca61cc00587ce8aa2c3980030f5d1545873000667b9264b0e6001ccc724c961cc0011df04bb2a3980063b20976547300461f32ae828e6000c3d655d051cc0ab0ff0eb2ea1980230f99574d43300061eb2ae9a86600287f87553658c00187ae8aa6cb180023da0772d96300047ac0ee5b2c60018df874cb658c00399ce4996cb18003335c932d96300061fb2ae932c6008c3c655d2658c0050f90eaa2cb180030fdd154596300161e3a2a8b2c6000a5f83551658c00399ce4992cb18003335c932596300043fc3aca32c605687f87597538c00587ce8aa4c3180030f5d1549863000667b926530c6001ccc724ca618c0051eb0f20cc3180038d551419863000477c12e8b0c60018ec825d1618c15d8d8e5aa2c3180030fdd154586300161e3a2a8b0c60adc6c72551618c0018dea9b92c3180031b553725863000667c1ee4b0c6000ccc83dc9618c00199ee5992c318007331cb325863000667b9264b0c6001ccc724c9618c0051e90ea0ac3180038d55141586300047bc3ac230c60008ef825d9518c0031d904bb2a318002b3e09618c63003e6d302ec18c6000acf82584318c0018bacab9ca1180030fdd354d95300161e3a6a9b2a6000c3d74953654c0014bb072a6ca9800a1fe1d54d95300061eba2a9b2a6000a5d8394b654c0030ff0
  | 17 => 0x8ea008c3e7559031d400187aeab2063a815a1fa1f5458e500061fba6a8b1ca002c3c74d5163940ad4bd07aa2c7280030f5d15458e500146e43a86b1ca000a5f8550d6394005938e8a1ac728003875514358e5000c6e43a64b1ca000a5f854c9639400199ee4992c7280063ba0b7158e5000476c16e2b1ca0008df8758c639400f99cc6b90c7280033358d7218e502b52fc3ac729ca000c5f8758e53940ad8bee8b1ca728003175d16394e500049fc22e129ca00097b865c253940ab8f70cb84a7280034ee117094e500069c422e129ca056d5b325c25394001ab264b84a7281fb0fa197414e500061ec32e829ca056c3f635d053940ad87ac6ba0a72815b47cc97414e500068e992e829ca056d1c315d0539401187cc0ba0a7280234e9817414e5000637b22e429ca000c6d645c853940ada9d06b90a7281f35360d7214e502b6a618ae429ca008c6e605c85394011ad4c0b90a72800b0f9d154986500061eba2a930ca000ccf724ca6194003998e4994c32800a3d61e41986500071aaa28330ca000c3f74d516194005878e9aa2c3280030f5d1545865000667b9264b0ca001ccc724c96194001c9aa4992c32800a3d21d41586500071aaa282b0ca0008f787584619400127f08b84a3281df0fa1974146500061ec32e828ca000d1f325d05194001a3a64ba0a3280230f98174146500469d302e828ca000c3d74584519400517d09bb463280022f613768c65000c77414ed18ca0008ed829da31940018baeab1c6328002c7610538c650005a6c10a718ca008978855c031940e387d0cba6a1280030f61974d42500068f992e9a84a000d1d325d3509401187cc0ba6a1280234e98174d42500061fba2a9b1aa002c3c7455363540014bb0ba1ec6a80038755343d8d500052ec2887b1aa000acd8210f63540031bf0e996c6a8007339c932d8d5000666b9265b1aa0008ef825c763540031d904b8ec6a800237e1d6318d500054e422c631aa056c6f655c8635400f99cc6b90c6a80033358d7218d500061fba2a9b0aa002c3c74553615400399ce4996c2a8003335c932d85500047bc3ac230aa002c3e74550615400187ae8aa0c2a80029e201541855000e673926430aa000ccd724c8615400117f08bb062a800a2f211760c55003e6c31ae018aa00887c855d163140ab0f90eaa2c6280030fdd15458c500146e43a86b18a000e1d5450d63140110f90ab92c6280023de057258c500047a40ae4b18a0018dc874c963140114b90a992c62800333dc93258c500049fc22e1298a002c3e74552611400187ae8aa4c22800333dc9329845000e6639265308a0028f5879066114001c6aa8a0cc2280063d61e21984500076299443308a00887c855d161140011bf06ba2c22801e3720d745845000477c12e8b08a0018ec825d1611400187ee8aa2c2282c3171cd5
  | 18 => 0xc4abcb0603aac01880a2fa1f74580310061fbaee8b006200c3c75dd1600c4a9938e7ba2c018953a60c374580310061fc2ee8b006200c3c85dd1600c4a993e65ba2c0188021fe1574580310443e42ae8b006200c3f751d1600c401878ea3a2c018aa3271cc74580315474c180e8b00620087e87d51600c4110f90faa2c0188030fdd354580310161e3a6a8b0062afe5830d51600c4010fd0eaa2c0188021f21d54580310061fba2a8b006202c3c74551600c561cb060aa2c01880b271d143580310070eaa286b006200ad88050d600c4010ff0ab92c0188221f21572580310045fc22e4b0062028bc845c9600c4018beea992c018acb171d532580310064fba264b0062b1c9c744c9600c40199ee4992c018802b620132580310165c3a480b006200e3954901600c40f5b107202c018953a690e405803103c7c43a80b006207ad883501600c40f5b107102c0188063e21d205803103d6c41a40b006200ec932481600c4015e102902c0188228fa1773593500e51ec2ee6b26a000c3d75dcd64d400157700b9ac9a8302ae20173593500451f428e6b26a01ca3d851cd64d400155d0439ac9a8002ab60873593500451f42ee4b26a01ca3d85dc964d400187aebb92c9a8002a7a0e72593500054ec1ce4b26a0bfaba809c964d400157301392c9a80030f5d572593500451f428e4b26a01ca3d851c964d400153d06392c9a8002a760c72593505a70f3ae64b26a0bee1d75cc964d4169c38a1992c9a82caa760e32593505970f3aa64b26a0bde1d754c964d4001d1f04992c9a8003a39c9325935000746b9264b26a0b2e8e524c964d4165d1aa4992c9a82cb8714132593505a54f41864b26a008a3e85dc564d403947b0bb8ac9a80030f5d771593500054f41ee2b26a000a9d83dc564d400155d05b8ac9a8002ab60b71593500055dc02e2b26a0bcab8805c564d401147d0a38ac9a80728f61471593500054f41e42b26a000a9d83c8564d4001d1a6510ac9a80022fa1c21593500045ec3842b26a008a3e8508564d400147b0a10ac9a8002a7a0c21593500054ec1842b26a000e8d3208564d40015750010ac9a8002ae600215935038d1fc2ae0b26a000a9f835c164d400153906b82c9a80022fa1f20593500045ec3e40b26a008a3e85c8164d400147b0b902c9a8002a7a0f20593500054ec1e40b26a000e8d32c8164d400147f0a902c9a80228f21520593500074699240b26a000a9e8308164d400153b06102c9a800b0f9d15458f500061eba2a8b1ea0018dc874c963d400199ee4992c7a80063ba0b7158f5000476c16e2b1ea002c3e7455261d400187ae8aa4c3a800333dc9329875000e663926530ea002c3e7455161d400187ae8aa2c3a800333dc9325875000e6639264b0ea000cae7259331d400195cc8b9663a80032b59172cc7502ac3fc32ea1
  | 19 => 0x57476157414e310064fb12e829c6200c9d625d0538c40f93cc2ba0a71881f659857414e312868e282e829c6293cce865c8538c40199b0cb90a71894333d957214e3128666b2ae429c6250d4f545c8538c401a9aa8b90a71881f339857214e3103ee330ae429c6250d4c505c8538c4018bacab9ca3188230f99574146310061eb2ae828c628fcce865cb318c40199b0cb96631880353d5172cc631006a6aa2e598c6207cce615cb318c40fb8cc2b9663188030fdd154982310161e3a2a93046201cce724ca608c40199ae4994c1188063e61e209823100764992413046200c3f74551608c405878e8aa2c11880387551435823100667b9664b046200ccd724c9608c4031f10e902c118803b24c920582310047dc3ac0304620287f87553654c40587ce8aa6ca988030f5d154d95310052ec1ca5b2a6200c6d7294b654c40147b08296ca988029760c52d953100667b9265b2a6201ccc724cb654c401c9ca4996ca988022fe1170d95310145e422e1b2a62008df835d1654c4011df04ba2ca988063b20974595310047dc02e8b2a62008f8805d1654c55d8d8e5aa2ca9880a1f21d54595310061fba2a8b2a62adc6c72551654c4a18bea9b9aca988031755373595310046ec16e6b2a6200ccf73dc9654c4018dea9b92ca988031b553725953100667c1ee4b2a620087f855c9654c4011bf06b92ca988023de05725953100637ba8e4b2a6200ccf731c9654c4011bd0f992ca9880333dcb325953100e6639664b2a62008de874c9654c4031b90e992ca9880333dc9325953100e6639264b2a6200ce472dc5654c4010ff0eb28ca988029b20965195310461f32ae832a6200c3d655d0654c4a193ec6ba0ca988023be09765453100c76412eca8a6200c6c72d95514c4018becbb9aa2989431719773545310161f3a2a9b026200c3d74553604c40199ee4996c098807331c932d81310047dc3ac03026202c3e74550604c40187ae8aa0c098807339c9321813100666b92643026200ad4814c8604c40f1b906ba2ca188023ee0174594310047c402e8b2862afc5c73d51650c40f0f90eaa2ca188030fdd1545943103d2e41aa8b2862b0c5c73551650c40f1b907b92ca1881e3720d72594310047a40ae4b28620187c87549650c4bb1b90e992ca1880333dc9325943100726a9264b2862009cf825c7530c4a19acc2b8ea6188230f99574144310061eb2ae82886200c5f54dd9310c4018baa9bb2621880237e0b764c4310046ec16ec9886200cd776945310c40f3a90ea8a621880335dd9514c431425e2412a29886200c3f74552600c405878e8aa4c018807339c9329803100666b926530062078f987902600c401c72a9204c0188063e61e209803100764992413006256c5c73dd5600c4adcb061baac0188021f61375580312b62f996eab006255c5c731d5600
  | 20 => 0x66b9264b00a2018f8874816014401d9264902c02881e1f21d54597310061fba2a8b2e6201cce724c965cc40517d09b82cb988022f613705973103d6741eeab166223acd83dd562cc40199ae7baac598803335cd7558b3100573c0aeab1662c5ae4815d562cc40155d083aac598802ab6107558b3103d67418eab166223acd831d562cc40f59d07ba2c59888eb360f7458b3100666b9ee8b166200a6e859d162cc4014db0b3a2c598b12b9a067458b3100572c0ce8b166200ccd735d162cc4014dd0a3a2c5988029b6147458b3103d67418e8b166223acd831d162cc55fc9ce7aa2c598b0f935cf5458b3157f2618ea8b1662b0a6d8595162cc401c5ea92a2c5988038be115458b31007173a2a8b166200e2d7455162cc561c9ce6aa2c598b0b935cd5458b3158717a1aa8b1662b0e2d4355162cc561c9862aa2c598abe9ba145458b3100537c2ae2b166200a6c855c562cc51f59f06b8ac5988023ba1f4158b3100476c3e82b166200a6e85d0562cc4014db0ba0ac5988038b5534158b3103d6741e82b166200acd83d0562cc401c5aa8a0ac598802b3e0d4158b3103d6641a82b166200a6e8510562cc4014db0a20ac5988029ba177058b3100536c2ee0b166200aae84dc162cc40155b09b82c59881eb3a0f7058b3111d66c1ee0b166200ccd73dc162cc4015cf02b82c598b06b92057058b3103d67418e0b166223acd831c162cc4014dd0ba02c5988029b6174058b3100716aa480b1662008ee8710162cc4011db0e202c5988029ba144058b3100536c2880b166200e2d5410162cc40f59d06202c598802b360c4058b310057340880b166200ae58110162cc40f99ce6b16a398803335cd62d473100667316e6a8e62008ed86dc951cc5451dd0eb12a398aa63b21d625473100667b9ac4a8e6207ccc7358951cc40195cc4ba0a3988032b9d1621473100656ba2c428e6200c3f7455260cc405878e8aa4c198807339c9329833100666b92653066200c3f7455160cc405878e8aa2c198807339c9325833100666b9264b0662008fa80dd3658c4011f301ba6cb1880a1fe1d54d96310161f3a2a9b2c6200c3d74553658c4031bf0e996cb18803335c932d96310143e43aa8b2c6200c3f74551658c4014bf06aa2cb188061f21d52596310052fc1aa4b2c6201c6c72549658c4a11bd0f992cb1894297a17325963100667b9664b2c6200ccd724c9658c401c9aa4992cb1880a2fa1370596310045ec26e0b2c620087f87594658c41187ccaba0cb188030f59574196312852fc3acba9c6200c5f87597538c4a18bee4b2ea718803175c965d4e312ec6fc32e3a9c62009cf825c7538c4013af0cb8ea71897735e1971d4e31286abaa2e3a9c6200d55545c7538c401b8f04b8ea7188037120971d4e312862fb9acaa9c6207cd6615d8538c4a1a3d0aba0a718a
  | 21 => 0x73d8960544011dd0e312c0a88032bdd06258151006563a0c4b02a200ccf731896054401998e6312c0a88023ee1d60181510055c422c0302a200c3f74550605440399ce4990c0a8803335c9321815100726a9264302a200a7985d006054401c72a8200c0a88228fa1773590511351ec2ee6b20a200c3d75dcd641441147d0a39ac82889a8f614735905100557410e6b20a200aad821cd641441147d0bb92c82889a8f61772590510061ebaee4b20a200a9e839c9641440153b07392c8288030f5d572590510451f428e4b20a226a3d851c9641440153d06392c828802a760c72590515a70f3ae64b20a2c7e1d75cc96414569c3ea3992c828ad38714332590515954ec1c64b20a200a3f854c964144114790a992c828802ade0532590510055a40a64b20a200e1f854c96414565c390a992c828acb879d532590516370ebaa64b20a200e8f824c96414401d1ce4992c828803a35c932590515974729264b20a2b2e8d524c96414401d2f02992c828803a520532590515970fa8a64b20a2b2e1c504c9641456953d06192c828a7a8f61671590510054f41e42b20a200a9d83c85641441147d0b10ac8288028f61621590510074699442b20a2008be87085641440117b0e10ac8288228fa1421590510051ec2842b20a200a9e83085641440153b0610ac828803a34c821590510055d40042b20a200ab980085641441147d0bb82c82889a8f61770590510451e42ce0b20a277a3f855c164144114790ab82c828802a7e0d70590510054e41ae0b20a208a3e851c1641444d47b0a382c8288030f5d470590510054f418e0b20a200a9d831c1641440155d04382c828802ab60870590510055b408e0b20a226ab5811c1641440117d0f902c8288022f61f20590510451f42e40b20a200a3d85c81641440153d07902c828802a760f20590510074699640b20a200a3f8548164144114790a902c828803a34c920590510054f41840b20a200a9d83081641440587ce8aa2c6288030f5d15458c510443e42ae4b18a2018dc874c9631440199ee4992c628802b52053258c5100c77410e0b18a2008ed821c163144018d8e5bb2a2288021fe1376544510043ec26eca88a200c5f32dd951144018ba65bb2a2288030fa1d64544514f61ec3ac8a88a200e2c725915114401c3e64b22a228803874c964544510461fb8ac8a88a208e377159151144018beedb9aa2288038759373544510062fbb0e6a88a200e1d641cd5114401a98e439aa2288031bddb725445100716b26e4a88a200c3d641c1511440187ee8aa4c02880b0f1d154980510045fc22e7300a2028bc845ce601440399ce4994c028803335c9329805100c7cc3c41300a200ec93248260144011bf06ba2c02881e3720d74580510061fba2a8b00a202c3c7455160144014f100aa2c028807339c93258051006
  | 22 => 0x100c6a88023761c2018d5103e6a31ce329aa200ce462dc553544019aec638aa6a8803391887154d5114537436ebb12a2008ed87993625440159d07326c4a8802b360e64d895100477c3ac9b12a200acf83593625440159906b26c4a8802bae0164d895100574402c9b12a2aec6e76d53625455b8dcecaa6c4a88038bd9154d895100716322a9b12a200ace86dcf625440199cedb9ec4a880353dd773d895100567430e7b12a200cce761cf625440199cedb1ec4a880393d5363d895100726aa6c7b12a2008ed8798f625440159d0731ec4a88023be1d63d895100567430c7b12a200cce7618f6254401c9ea831ec4a88039355063d89514e57340eebb12a228a6e859d362544014db0b3a6c4a8802b3a0e74d895100566c1ce9b12a200acf835d3625440159906ba6c4a8a8a9ba1474d895100536c28e9b12a2c8a6d859536254545c5ea92a6c4a8a8b8b15154d895151537c22a9b12a2a2e2f845536254401c5ee8aa6c4a88038b1d154d895100667baee7b12a200ccd75dcf625440199ee9b9ec4a8803335d373d895100727aa6e7b12a200e4d54dcf625440199ce3b9ec4a8803331c773d89510056741ce7b12a200ace871cf625440199d0e39ec4a880393d5073d895100726aa0e7b12a2a2e4f5394f62545454dd0ba1ec4a88029b61743d895100716aa687b12a200e2d5450f62544011dd0e21ec4a88023b61c43d89515153742887b12a200a6d8510f62545451dd0fa0ec4a88023b61f41d89515153742e83b12a200a6d85d076254401c5aa9a0ec4a8802b3a0f41d895100566c1e83b12a200e2d5450762545454dd0a20ec4a88029b61441d895100667b9ee1b12a200ace839c3625440159b07386c4a88029be1570d89511453642ae1b12a200aaf845c3625440155908b86c4a8802b3e0d70d89510056641ae1b12a200ccf735c362545454dd0ba06c4a88029b61740d895100716aa481b12a2008ee8710362544011db0e206c4a8a8a9ba1440d895100536c2881b12a200e2d54103625440159d06206c4a8802b360c40d89510057340881b12a200ae58110362544a1caec3b1ca2a880393188639455151733b0ec528aa202c3e74553605440187ae8aa6c0a880333dc932d815100e6639265b02a200a7985d0360544014f30a206c0a88038e55040d815100578c0881b02a200cce72d8e605440199ce431cc0a880333d8d72981510066631ae5302a200cce73d8a605440199ae7b14c0a8803339cc629815100666b98c5302a2008de87d8d605440193ee9b1ac0a8803271d3635815100666396c6b02a2008de8718d605440193ee831ac0a8803271d0635815100666390c6b02a2018ee86dc960544511d90db92c0a880333d8f72581510066631ee4b02a2008ee87d89605440195ee9b12c0a88032b1d3625815100667b9ec4b02a200ccc
  | 23 => 0xd8d510054f42043b1aa200a9d8408763544015b50010ec6a8802b660021d8d510052ec2ee1b1aa200a9e84dc3635440153b09b86c6a8802b3a0a70d8d5100566c14e1b1aa250a5e85d0363544014bb0ba06c6a88038755240d8d510046f43881b1aa2008dd8710363544a14bd0a206c6a88029761440d8d510070eaa081b1aa200ace82103635440159b04206c6a8802b5a0440d8d510056ac0881b1aa2008de87c8363544011bb0f906c6a894297a1720d8d510052ec2e41b1aa200a9e84c83635440153b09906c6a880333dcb20d8d5100667b9241b1aa2008de8708363544011bb0e106c6a8803339cb6398d5100667b1ae531aa207ccc635ca63544011bf0eb18c6a8802b3e096318d5100566412c631aa2008dd87990635440159d05320c6a8802b360a6418d510046fc3ac831aa200acf82590635440159904b20c6a8802b6e016418d510056c402c831aa200e1f6455063544011bd0db90c6a8803335cb6218d510046ec3cc431aa2008df8758863544011bb0e310c6a8802a7a106218d510054ec20c431aa200ccd72188635440199b0e310c6a8803936146218d5100747420c431aa200e8d841886354401c9ea8310c6a8803935506218d5164f63a88c431aa2c9ec45118863544014bd0da90c6a88039318b5218d51006a6b92a431aa200e4c62548635455f8bee5aa0c6a897787d525418d512ef0fc22a831aa2b0e1e745506354561c3ae8aa0c6a8ac317dc95418d510062faa2e431aa200c5d545c8635440f99f04b90c6a881e37a1e5218d510046ec3ca431aa200ccd72948635440199ae4a90c6a8802b5e055218d510056a40aa431aa25da5e85d0863544014bb0ba10c6a8803875534218d5103c6f43c8431aa2008dd87908635440199ae5210c6a8803875514218d5100666b928431aa2078de8710863544011bb0e210c6a897697a144218d510052ec288431aa2078de87d0463544011bb0fa08c6a897697a174118d510052ec2e8231aa200e1d54d04635440159d05a08c6a8802b360b4118d510070eaa28231aa25da5e8510463544014bb0a208c6a881e37a1f2118d510046ec3e4231aa200ccd7288463544014bf0a908c6a8976972152118d5103c6f4384231aa2008dd8708463544bb4bd0a108c6a8802976142118d510054f4204231aa200a9d84084635440199ae4108c6a8803b14842118d510056d4004231aa200ad98008463544bb4bd0ba00c6a8802976174018d510070eaa48031aa2078de8710063544011bb0e200c6a897697a144018d510052ec288031aa200e1d54100635440159d04200c6a8802b36084018d510056b4088031aa200ad581100635440f1bd0f900c6a88023761f2018d512ed2f42e4031aa200a5d85c80635440153d09900c6a8802a76132018d5100666b964031aa200ccd72480635440f1bd0e
  | 24 => 0xea2028dc8750d63d4401c3aa8a1ac7a88063721d3258f5100667b9264b1ea200ad7814c963d440187ae8aa4c1a88071b9c9529835100e6739265306a200ccd724ca60d4401c9aa4994c1a88030fdd154583510161e3a2a8b06a201cce724c960d440199ae4992c1a880333d8d7298e5103e6631ae531ca202c3e74551639440187ae8aa2c7288063721d3258e510052fc2a64b1ca200ccf724c96394403998e4992c72880237e1d6318e512846fc3ac729ca200c3f745526094405878e8aa4c128807339c9329825100666b9265304a2018f9878826094401d9264904c1288030fe1774582510061e42ee8b04a200c3f74d516094405878e9aa2c1288030fdd154582510161e3a2a8b04a2008bf845c9609440517908b92c12880327dd3325825159e4e3a664b04a200c9f744c96094563938e8992c12880333dc9325825100e6639264b04a2018f8874816094401d9264902c1288023ee1d60182510061fba2a9b1aa200a5d85d0f6354401c3aa9a1ec6a880a37e1d43d8d510164f3a287b1aa200e1d5450f63544014bb0a21ec6a8802b3a0843d8d5100566c1087b1aa200ccf72ccb63544014bb0b196c6a880637e1d32d8d5100666b9265b1aa2018ee829c363544011db05386c6a8802b3a0a64d8d5100566c14c9b1aa200acf82593635440159904b26c6a8802b6e0164d8d510056c402c9b1aa200e1f645536354401c38c8aa6c6a8803335cb62d8d510054f420c5b1aa200a9d8418b635440199ae4316c6a88033361c62d8d5100726c28c5b1aa200e8e8418b6354401d1b08316c6a880393d5062d8d5100726aa0c5b1aa200e4c62d4b6354401a9ee4a96c6a88039318952d8d512852f42ce9b1aa200a5d859d3635440193ee93a6c6a8802b3a0a74d8d5100566c14e9b1aa250a5e851d363544014bb0a3a6c6a894387d5254d8d512870e2a2a9b1aa250e1f845536354401c3ee8aa6c6a8803871d154d8d510062faa6e5b1aa200c5d54dcb63544018bea8b96c6a88031755172d8d5100667c12e5b1aa250a5e851cb63544014bb0a396c6a8802a7a1072d8d510054ec20e5b1aa2008de8794b63544011bb0f296c6a880333dca52d8d5128727a94a5b1aa200ccf7254b63544a14bd0ba16c6a88029761742d8d510070eaa685b1aa2008de8790b63544011bb0f216c6a880333dca42d8d510070eaa285b1aa200ccf7250b63544011bd0e216c6a88023761c42d8d512852f42885b1aa200a5d8510b635440159f04b8ec6a8802b320971d8d512846f43e83b1aa2008dd87d0763544a14bd0ba0ec6a88029761741d8d510070eaa683b1aa200ace82d07635440159b05a0ec6a88038755141d8d512852f42883b1aa200a5d8510763544a11bd0f90ec6a88023761f21d8d510046f43843b1aa2008dd8708763544a14bd0a10ec6a88029761421
  | 25 => 0xc1147d0a10ac8298028f614215905303d4f41842b20a600a9d830856414c01d1a6410ac829802aea0021590530055cc0042b20a608a3e85dc16414c5d47b0bb82c8298228f21670590533f51fc2ae0b20a608a3c855c16414d9b53f06b82c82981ea720d70590530451f428e0b20a62ea3d851c16414c0187aea382c82981ea7a0c70590531754ec18e0b20a600aae821c16414c0155b04382c829802ada0470590530055ac08e0b20a6008be87c816414c0117b0f902c8298228fa1720590530051ec2e40b20a607a9e83c816414c0153b07902c829803a34cb20590530051fc2a40b20a608a3c854816414c01d1a64902c82981ea7a0c20590530054ec1840b20a607ace83dd16214c5b59b07ba2c429803335cf74588530453742ce8b10a6cca6d859d16214c0199ae6ba2c4298229ba14745885316d36c28e8b10a607ace831d16214c5b59b063a2c4298229be11545885304717c22a8b10a600e2e745516214c01c5ae8aa2c429ac3939cd545885365f26b9aa8b10a6b0e2f435516214d61c5a86aa2c429ac3930c5545885300536402a8b10a607ace83dc56214c5b59b07b8ac42981eb320e715885365537c2ae2b10a608a6c855c56214d2759f06b8ac42981eb320d715885304537428e2b10a62da6d851c56214c0155d0838ac429802ab610715885303d67418e2b10a62dacd831c56214c0199ae638ac429802baa00715885300574c00e2b10a6008ee87d056214c011db0fa0ac4298229ba17415885300536c2e82b10a600e2d54d056214c0f59d07a0ac429802b360f415885300716aa282b10a600acf835056214c0f59906a0ac4298229ba14415885300536c2882b10a608a6e85dc16214c5b4db0bb82c429802aba13705885300556c26e0b10a607ace83dc16214c5b59b07b82c429803335cf70588533e537c2ae0b10a608a6c855c16214c0f59d06382c4298b6b360c70588530453742e80b10a600a6d85d016214c114d90b202c4298038b552405885300537c2a80b10a608a6c855016214c0159f06a02c42981eb320d40588530047743880b10a6008ed871016214c114dd0a202c4298029b614405885300716aa080b10a607ace831016214c0159b06202c429802b9a04405885300572c0880b10a602c3e745526114c0187ae8aa4c22980333dc9329845300e6639265308a6008bf845c26114c0517908b84c2298023be09709845300c76412e1308a602c3e745516114c0187ae8aa2c229ac3950c5545845300667b9264b08a601ccc724c96114c015a902992c2298030fdd154980530161e3a2a9300a601cce724ca6014c0199ae4994c0298022fe1171980530145e422e3300a6008ef825c66014c031d904b8cc0298030fdd154580530161e3a2a8b00a600a78805516014c0399ce4992c029803335c932580530061fba2a8b1
  | 26 => 0xc034005001002401200d0000024018000000001c00c0030020010000000000007402600501980500000020000010004000008005400200a009800000a008002806c014005013800800000400500000060000000000008002032800c0100380161f3a2a930ea600c3d7455261d4c0199ee4994c3a9807331c932987530045fc22e130ea6028bc845c261d4c011df04ba2c3a98063b20974587530061fba2a8b0ea6adc6c7255161d4c031dd0fb92c3a9a8b1bd53725875300636aa6e4b0ea600ccf83dc961d4c0199907b92c3a980333dcb325875300e6639664b0ea600ad681cc961d4c0199ee4992c3a9807331c932587530061eba2a9306a601cce724ca60d4c0199ae4994c1a98030fdd154583530161e3a2a8b06a601cce724c960d4c0199ae4992c1a980b0f9d154986530061eba2a930ca600ccd724ca6194c0587ce8aa2c3298030f5d1545865300667b9264b0ca601ccc724c96194c0187ee8aa4c12980b0f1d1549825300e6739265304a600ccd724ca6094c011df04b8cc1298063b20971982530145f43ee8b04a600c3f85dd16094c018790bba2c12995327ccb74582530061fba6a8b04a602c3c74d516094c014f501aa2c1298030fdd154582530161e3a2a8b04a6008bf845c96094c0517908b92c12980327dd1325825358e4e3a264b04a600ccf724c96094c0187ee8aa6c2a9807339c932d855300666b9265b0aa600a75850876154c015ab0610ec2a9803b14c821d85530047bc3ac230aa600ae4825846154c0587ce8aa0c2a98030f5d1541855300667b926430aa600ad583c846154c01d8a64108c2a98022fe1170185530145e422e030aa602c3e745536054c0187ae8aa6c0a980333dc932d81530053cc2e81b02a600a79851036054c01c72a8206c0a9802b660c40d81530047dc3ac0302a600ab8845806054c0187ee8aa0c0a9807339c9321815300666b9264302a6008ef825c46054c031d904b88c0a98029e61740181530071caa080302a608a3e85dc96414c5d47b0bb92c8298030f5d7725905303d4f41ce4b20a6cfa9d839c96414c0187aeab92c8298228fa1472590531751ec28e4b20a607a9e831c96414c5d53b06392c829acb879d532590536770ebaa64b20a607a9f824c96414c0fd1f04992c829803a39c9325905300746b9264b20a6b2e8e524c96414d65d1aa4992c829802a720532590535970e28264b20a608a3e85dc56414c5d47b0bb8ac8298030f5d7715905303d4f41ee2b20a62ea9d83dc56414c0155d05b8ac829802ab60b71590534ad4fc1ae2b20a607a9c835c56414c1147d0a38ac8298ba8f614715905303d4f41e42b20a600a9d83c856414c0f5390710ac829803a34ca21590530051fc2a42b20a608a3c854856414c0153f0690ac82981ea720d21590530045f43842b20a6008bd870856414
  | 27 => 0x300800200440010080070002000001801000c0020068020022002008800001a02b00380000060000038064002000002800c00200a007000c00e00001280d00000020050000008009003800800c00f001000400200100480040040010020000004002008005802c000008002001400d007001800c00d0008138062003001002407a001000007803200f0040004036001007800c004000005801405e007000006400000d027001800a000008802c036000012800400000300080040180110058038008000003003c00000c000000400000d00a008400601000100040200030010080002006004800004403c0000000020002001001001e004007806c01a00100e80040de003000800003e007000000001e009002000c01000100300680020030008004000001008800c03e003000803000000000c804401a02a000806402a00a00e0000000000000000000800a00200140300160000110008004009000c0000070048000002005000000c000005001000402a02300300440000000008078002000003000002c000003800c002002002001000400f0000080000010000000004000e001000000600a01380100040000010004002036001802000c002001000c03200100400040140000000004006001000000000c00400000000080050008004000002008001002c01a0090000008004008000c02a00202700ac002015010800400a003004806800800300200080000080010028022000000801c02e003001003403800200280e400400200f0000008000012800000c004010800c05e00200000000020100000008004002001003001600a002800400600300500100020010010000006000000000000001400000140020000030004000000000801000000800e801c03a003001000800a002000000000c00100280a007400b001000c00201c0028000004003000001c00e002000001800000001a803800200100280f4018003002000000000f00a00b804600200b00000400000020008008022000000800200500100180080000008000006022003001407600100480040000110000000024000000801800e01d0058134004002005807c01e01d00100040100000010028008003008802c00000b0008000000003004000000c0000028008048016012000000800f0100004004000001002400000d00080300000500040004006000002800001200d0008004000000000800003602c00a800000600000100a400001a00180580040080000000006002005802000200a0098000000009000807400e000003803002801f0030088004001004000000603c000801000a004003804400200100300340000000008034002000000001002000500d001c000000000000800000100100ac026001003802800600100000a801200000c80d0002002004002404600000880
  | 28 => 0x440000000bdd5ca9cdcb223ed0002ad434aca4319000154487b4e732cd7266ce6032e2ca4e6ef00001440005c525b1b48cae3a023f1105d12bd9640908c31841f38fa6a0d784616dd987d9dc70c288296571019334633a4000ce30002fa073608b3108d60b26a8f51d0121946000000182c000c9a00001a000a0028000026009001000000402900100700020050010044008008001011801c0080060020024005002808c004003006003800e002007000000404f0018018012007007800c00600900100440080150088058004027000800c00a001000004c01000c00b000c004003000000000a00a001004803400e00600c003c000001803001e007004801000001a0000048004028000001800400a000000c010008010000002a00a00d8010000025000800402406300400180000040040014014003000000c0000260010064010001003000000e00100000100100020018010046003025006000400300080000020000000034000002001001c01200400280d4006000000800000e0110048018000009001800400000a0088048000001019803c02c007003801000000000080080000190000008004004002000404c0260000078002001000000000600700a00300000010010004002001002803c002005007800c00200900000240060070030004006005000002801a000005805800a000002000007e000003000000c00b000002000800600000000100010058014024000002000000e008003802c000004000000401a00000180cc0a800100c800802e00c0008094004000015003002000b00a8004022003000002002c001002001801a017008802000800f01b800801a003003804c000034008801001a001002001c0140070000004016001000801c006002000000803800a0048038006000012001401200300800000140030000004002001001000000c00300200000000100000000010005014000000000102a801c00a0000000014032010001000005c005007004403e000000800401000f00180180060040030000002005031808000000801180340000070088000000017000000002c006002001000000000380440000000038064026000001800401a002003000400000300800300540070170038000011000801c0000000090008000002001805000400000e0008004017007800c000002000000000400b002001400e004001801c01c002000001000400d0000008008003010002c038001001802000200f002000000800000b80180040150020010002001008012803200100080000020160078028010000006000000e00000e801c080003003000000800701080c000c0150000018018002004800400c0250000000006002003006801200000700380000090030008000025001000404000c000800404200e00b8000018007000013800c0
  | 29 => 0x7e8b552d30b89122e5160a0b3182a7743b31ae4bce7e40ba825c4ccb9c35a800137ee84060917d5a296f4b28e8d1886795c9197004e3470c68b955260000002c246162b80670240768e1c0e9374c1109fd69195309cccb6539a7a107e3961a137b514e303483a7846ea8353930f187f02d90b0364cdae2e65090b8596ea673fa9fc98b07015eb84bdcd40cc0d92d450fcc5e5aa01259f003943b042110089d703b9bc0fa77361c3684f0453359600004ae96957580bcf6ede6297999909472f000053400005e00009d9022cc055ba5580009b9340a0a00000001ee1985478b5c0003434a740006dc80014625cd1ba095894ec730003a05b5800050a0000108a7420d297d8440006729db877e0000001f20ef006340e8f28d808050002f4466800000000000000006413144d280f869eac053b0c2738823e1a8000000007008b4d075bf0000d340000dd80010aa00035c259cc2cc40171b1859d687f0001411aa40005ee0000dfa3846fc86b5a7691954624f8ba22126512e5d62c43c37296f97aa5891b33861ce486670282c510ccb218b17fc40ad2b40096557dad1e658a9c82b48996f72fdd24c51614f266175470710d1d3001424c35897dd840cf149b8984d74434144234853845505a864123cbb426c96cc14a42e42e1aa8d684c20de23cd3742be2411b095409c11e7aef084cc28225ad5c1acddb1fb104c790aba02ba5555927fa6f3ade8126e350968bcd3ca0005f626592d072803aa371c9499e6e5a7816f80004c5302400000046f80016e490d712309483c8ae3eda0c800032a00023b8f0e11357800983f0000338ab91c561285af81e40005ea0e3a5cd7e47bf1810948998df555a10113ea68658d05d82241be5b72f813562fb00039b021281f72f93180f83af3d991114f24ad46d252ca7881b4010828db680d00020bc77806400003aca12ae114c2884170ae22788b71680df600003a18caa03000000173aa5a273ac3126a00061e80000007920001488cca1450d88c24e2e6956d42d08970e68005a81925400034d8ac4ad89a62bd000147687237fa1c00002aa17f000157200000006a57f87eb0001e5c1cae220002c71042e930e3034c0001eb2c23734000aed5261508be600047193b1ca42ec02e9f3061eb3a2b0187869c949145185d15e0006fd8000e52a221d4323c3e2e9520ea7e41da00000006a000000036680b015c9813a5b3494140000001c70000000403325800083855e00005606a600001c872485d24b29f032400000023f40009f723d89c5630842490346ce580ac08c257594c62313faea4dbebc36c8af189bcdb5614a4ed56c0032fb20e8ad24ea212a601cfa5751fe330d3c4000300aaa1270b6807d8000acec3200001d92a000038319115d0c230002dbc24086960427f10ce28405903c88243370c10000a6ebe52
  | 30 => 0x3491131806d184f89e513b80003e73105cf40a34b12974c0ecc22eb3320d1e4a03f3000068200033ea6b0df49da6ce0160c24c493719d419f800044683bc0009601b280002c272a0a0b0053a68eb31429dc0506d15269764b6c75d556918c6c00005bb1afc0006d0012000058e2b92f49d84d52823399a7a8a5c3c36df0ed5a2240b0031371cb23b371380011a85120003620000e6011d9aad60eb1100028b8f5623500027d029c20f0989224000ba400037e086a51d00008d05acdda1e080000000ad3d68000ceac16088ba2000082b2529289a2c00068804cc0007de0002a2c9fc00053e85a1956bc52f1989468675a2cf032135ea381c10c7806876c3743585942362232acf420899c6e8b4a16ca85e0da24d0f0a0ab4bd00f49a8a3043529240fc76b5bdb5349b645e74589e17f204e3229528bd60bd73b9719cf811715187f14e05d7364b6907cc15336191c000070e36ca9b01e8238504097859e90870b23e8fae45730600c5288b6766d80016bcd2c5ed14b00000b7175327d708cd72a78884e685f91c707800000140000400d7649200032549589bd025130000000000032edc3e9d05a4000000069754480018387935b32f40e8cdc720db88157ad24442353c30c6ed4a01140c6e4941970fac1146144d826d06ba9971e816508642e921439184d87f9730a18cb92452043289d89440e0002114000c0b0002b71960c34217b790c8e42d27ab60177a3686bc2824004882259205530c5065ae9be545a7136270ccc8d4cca4ffaf7dacacbc348b03441c000344900065a9420000000000162734b8d8dc06290220f8ce6031c17ab660ff62174fc11b1720de133985c80000010003a480d260d0002ebc68a5055b888f988aa432d5b3dcc8c0005e003d97e620d6df884586c75e285300837e8e704e9d5cf9a39d0ca386d8d027a16405bcba60544fd36986b61d93ce03542585771a783f11e8b202359340968adb0bfa3601fa9360000560faa0000003879922ba25bcb76592ee4200000018304eb2a701ddb348a1666234c000e112498a01d1e49d2af9468a7a5510f0b8248a8e735582f0930e4e94648318a62b64276972d91a80b3b1ad8dc525f800021440000002a980014184e23ee1b9d2866fb08a8464c540594c58e4cf882bc28992181445c851621f403297568e96fc13870d00d04f8d1ab5a48497d1266a560d31a39cecc6d31838f159c0e90ebab4c95c1ca4af2b9d64c8145080644054a1837f0001b905bb0000000b1e00024880008d02cd3c1800128c6b31f129014c20d969b9a9000073157180886f88964edaa280002721b4a9bc000d6624286004462a733d2c5c056d170002fb801a324460abe1cbc8e10000001b1c5fe00001000000d45b600004260000001ee80003891ab9ce53ded331f22f10fa4e260d19f0c43623f5db0b4c
  | 31 => 0x1178da770a91e0f9421c352b4244869ee474aaacdd435207519e04eeab26a4aaa4ed4b0859b283c698a463968000b1c39a46892040009a169c32759b4a7614ba7656ea0000000dd800003a420a719a269283a78000db44150000df5740e7131b0001874d82000167c2da42c0000000000ade3a880006ac7c14ca94ec60c0e00002e84d0056350f0c6878a27c3ef9b28f160006d7b6f4930af7387800165c00050b800002464815aab58098043000000000064a0832635198410061b38490025845f9899996e4300000000000004018000630000525000000048d000317dad4cfd6efa4f0eb8dd65f1a5e400060554300012fc6350ad977039245d71c00000000007198000000b6a3bf8245150d341ac9760b9e2a228707e8e0600048b2a648f400003f8000000c46390068954e3266321f64a56e457032a10594a80438b93c0005146c937a800000000005219142a95daa03000000016204588f27d3690b038ec800069b06e8000903000244d42cd0f56308b0dec08769299ecf1ecef0000a645860002ef96a93bc8db7190000096c545f20000c74e475c78edd63e5b500f2bf5a9011b3cf927c1fe4c5634935c0002fc0001f1c742590033ac6d446e0424e27907e243f2d4913c00866b29237ac6ee0825212e3178e77603280394b003b16eaabc56c7a30a3321400000033a15740006de000348153a5ef0002d3c57a8b50002fec58cd794440501c1e5ac58726ed93cc004ae00000000002253a5d5b492b03c0000d102f40003108000dba4bf80006003bb23b12643c62853480a905aec751d122a505ac3c21205c41c80000620b01a34386607b9100000007402450de00006f28b6c000000000000187e0000000000c8463f1aa2ecc6a258035906f44c65a24e5b9002f690a2621cf95825b932598d18fe5525640acc9cabad5650eb54a61b90f736648ac13d73c04e91685e2029b148ad01c46d891b48100004a0a520000e3a60d029c46055a40b90dc3404bd1723238a360000d7814928a94a54b0c34e3a8392f900000000003ed08a452a9cd6b116d00003b90789c01482000000000182e0000003930f34c89156800070e715198b1b120832c1461cc8f00c7d7381014ae62260f7971daaa0b346801194a2e5b45cb92d112ca544293fcf802735f487a01e09c519f1170d3abb971726449be38f6978cf44beb4459a84a87321f6192b67435ce82547399065e3df0310bc0a4297256195ad79493a3b10ac90c020c07f1ab400065051980004dace047ba194672e0a22002394b6bdb10f0a2c43a22b3290991a02d8120cb83852206147913e92364f32ad89ece1078834c9f95906afa1788be8332000308815916200067325c4806036079b1b940400048336b9b5a91d5d42d8134a5af43791d00008bd00011c9cba19821895004dc5bc20793391202ee
  | 32 => 0x59f938c000caa2c61628ccea2924b816d5f85023e2a4f495002305200019e032800014d80003831f5116c000a2f0ea8e9d1ca62231623d4fda65b5e58398ef40804a993851d012162b3130cd400010408dc7feb4a0d50c296b0ae665f8490ab2c040d20474000a8869f870d890d3c13032b47baab334b38a80aae343b00c74fb0a1c31e91906106872ab1124cb04450490b680cc7272bea2516921ed23a9d101ea11c5372710a000080f623b4fc444362a8000000c986ac31d8000b7f45db31c000b780a81bf16c4a1a0cd000000016900011350d60002bc07ec09a8781fea53516c57f1c6b18cb980002d38605b6c3153373231792d5b30d376134ebac298174904c96b004ab149b026b5d893c19ac0be5411dbd8367e30e835cd5421d408a1540b88d4560f1f09058c076c39f503d473c74808954b83ab3311c855060aa22c2745ad22d0000093db6e4ef287ab5ca502e700ba080a0e0006870c30b3a54854b8625abe83d3608000a1a0000001c699101430a10c386c6247239af58a9a95f0f391bc0008a25feb968000000046800000039168280010b484349108e55f68a061aa7c80000000003a1592080960cb14d0480255ab0fbd6141b31432834f4c41c5a3acc849a6b03f7248da181d347822dd1141f014731886b80984cd313d96a65f552365ce860001ca1b30ea68d52a48001d22270000000135208f53f3939ada0005989a4c9187561f3acacb42bc800019903383c74b6392074c0b6638058d86601c0002028a6485300015f80006ec17c00011ae13b577a8d914cd1f242286c4e872e00006595a8b0421000003c400056000000000000000060df023372e230d7983f74c805a91f234b4eb99640007ff064a7d8000da33261198ae4dff000350547a9e9143b33da96c723d38744d7c8e4253076183e5345df85e06da7f733f16609a640935402fc00000052a00000000005a700000000005cc8cac000b9f000073512e7dd50595f0c628cb105800134400016896957e88ec254b7a4000db01220ec873800071425e009e5641b50f0073e9254640000fe29be5c100007f49c92b8800174ce02000041c00000031728042e6e564808280efc40133b8f09c9a3ec04a82300005ad0001ed9c3a3294d9a4c00220000c419a00000d813f350cf626061200a080008ff000047c644ad8414ad48000e663dc00019bc89c408000109abd42199f459f4d6e5929900e6c8ce37b8dac95e2025678f389a40b021c30c56865a4104a3356989f049200019dabf056119c946a7996fa022426000064a000089cbff21c88059be00038db2e15d8755000292c2c80000000db000033c00026b8000709428319872ee0100037280003f5000201c3ba06d0000d2400061c58f01080007a800019bc7bc9590002aeda7291a0000000000144041ba34000000000000
  | 33 => 0xd46cd332090600009f355304390daa621fd800036a6d40001bc88f83800000d18000d9f00012299fe0000000001caed316a70000b2e37e0000c649967544580000cd88442e7382007e53e00000014680003dd9c10000c9300037101c20cf203b510e2838a00036a4bd04ca2e819584b87182a0a3155c039e6621b551b298f14fab487b06c54e41cac5e40200ceb5ddb1a69c40c1c444b24302b30000ef600005d00017469eb4320000a3c0000002c74000e1435130304d059b4da800112600047000018ba0005c31e312c23015c732bc0009152679b3c000587685176c8d232362c8000c0884c1081c2ccf84902d82cd1b44e96445b6e0000c57140800185e48e0e426816201cf1d60000cba8302b50001a843981bc32e800000044c000133293f31e047800003335701bc9343f05f78a4193618a39108b89068370001f1800000068caf0488ca6466e8708b5052a190b2f4e240006bda87400029b000336018ac2e63d8e2c0000001b80800d58583668249d25e0453da3679528135451b4a8b6e85f3da8ee0000010363a5ec0007e913c9934c120006b790a54487916a9a1e4b7083e0c2892118083c523b21d61e0304eb17984d255c590b6402f8d54565a021bd020436218ac6800004b68000f4439536c0c6cf1c00071d9f9daa2aac0078cc1b4a52d0712999c5adc5245b4710eea6849c92ed42600058180004280d001f0001cf6a7105a1da45eee5428ba3bc5340001d8b840d96cb43b91b4c00022006517ed2faae93319fc0a3e9774631ee400047d13a8000c7097027c1ba56e032767924b800055453000d49ba87a000190cca20816b1959513e1372b0a48560c3792088add68218e5292e2858291c2520e30524d9653586dc828000717b774000dd2591800000093219d081c0007861f4a184216acd4199e75c603f33cd8284000d8404b0c156c290c000161520a5ee4651514ffc9e70002c48cd2d0b0002ab93da37268a09a86900212599d38a4062f55fa95c00009e6ac9c291640000000b25ae46701579d6c0000000000000f423be34184a47c05bd6762d3400037156a8b500000000001bb86dc0003fb09296708de0919084000b3000003090080004de2fadb8681a6d50215a00e2c4b20a98e703c400014d42ee51134f8575cd62ab34534887d08361d2000075424963b80b8e7a17037ab3353f6b696752bb8fe85dd2c40000fac000122b75190c00017b2939a6ae503b812fdcfc00000000000a07400e0abc455c30456ea9a4134b743d9000085641732a8528a867ec5cb0bf5032b9e1880d7d4ea35e0001ec09922ce00028f948ac9257fb265696e673cc000000000037590e80006f31e496800001030002ccc00025300028dd8562c50acb7dd3107a4413aa6984c5745a9800135a000558b5743425150f9062c96e62725503e498200
  | 34 => 0x556812a4165400000000006b4bae00000005aa3b636e87f487a92d0bc9d21aecca071fa880b80bbe4c9a095cc61cb2d700007101360d5a810b743cd42b0001c1a5d56b8193ce0a000120896c00080f47e06785be7450001c8dcf213254c0bbcc3a1384d198f8c1466053fb618000000664800003aabe4372a7c0008ab0000f498fc77c36424384cac5a3fe2a147aa4fb741b41890e3326180fb82a436f5b58f44bdab9156815541f4a2b08d13dd8ce5de023a5999f6b7d4ac057cf2a63916f2fa89e4a2610c01c40009743a52089be200030d8000ff076700036250f81dc3f9b7400e6246152800113cd325a29ce9aae00000fa12522085b6983614d8c14c5a32bc8fd40d16f7ba508a2c840869704c66a2500020b93cce7454e22546227bc70917844a07bd0bd37252b6dcf0c21e788b212e59db7540002550000000000cd400026dc000cf96be9bc42ac05f6ba975000082a0a8b9b540e5395b69a2c000e1a0002c4c00006018fa98c0000005281e040000002b80cfc97c1f3329b65077ac3b00035692006a174625d8000c806a52c9d9ea87323bb80d89a16b0be8fe400eb0d28190310b26150ab98085c00004a7b4b43fcbab112000129c1ac705887d7a609454d87300004a15c49320d080000000000d6c00000000000009a427027b000058d06030e4e7e0006d909085a47af21b089ca8e9c70002608000994057800000071654ab925824d8f65f00000000005859d35ac80006bf9838bea0e700000000001c500000000000005ac80000000001ed0000000bf82300000f5400001c00000009020002e940000004ef9fbc74abe14ea30b46a081200010080008464528ced79c43e6feb9d418e000000314000056203a0000fc0c4b12d20789b4a054a3b4b9678c246890001982000128b88d7ea0004e7b8c40004064ff07394000a95920c5d5d416723388bdcdc0005368b09bc47a926b32b15988e640700007cace842b91b9454c214d88798978d3a11894605d660f467a9556a04cd50aa83960a23c3c2051ca32b375e90ea40000b922100002e81657208ad0000e176de0f300000004f180002fc47f4ad00003f261809301e965a7591e584d06a65084b52e14ebe00040003b0b940007310000962dde02d33d942200020b1979be6e3d2478c4c00018310322392a454614680009d03db6d0213da8ce0c00019fc3c84f6000349d80a00027710340189c00002ee81783642b700000001db069000115a0006ca9890000b8101e126db161f564e3171764ce226ab5795ec7d03d0223131276548c2100000c7c327168d6322ac3b88ff8a18dcc06d01b965e00000032b800010f00037e910623a1ec82ec0001951dd08b4e6a91f6632f3493c89b6ba004ce848fe2c134115e89b260800b5af8a7827e2b1d7c4874000000131ca925140a24ada6e451c80
  | 35 => 0x1760ca73098000ea40db70000000000003c488890ea0000000a0c00000000ab70136c000095a3d90a8000709a1480000cd5f301711547ac2bca21caf6d603732c510b08a41768ce153c27d4948e1562a000662885800061966cb454ef2c445519790f20139487ae1ccda56f150ae6d50e5263c5000186e3d34dc01c002c59a3cb0d355e69126ee29ed8e20ee609a0c4db8775065840849c86809faa049a25ec131037199c8ea00000000003d40001560000a4f681b709324c786bd359c98e19b1c0865d2a24ab2582b7c00000065cb60c00ad3e38129953aa834205099ccb40003002eedc727fd4960000000000605000000000015d00000000000000000214e5804fb3551741df2fe8000000099000339c000ce400009740005c24cd92e854006a66e1af40000e300015d8a96be76841eb866a47145c35ad398c6040e12e55704fd2242dcdd0c3b04ab8000000c1100000002b8c5b7108000b328c74e12e9d4880001838000dac1270a79254a7e1100002b64b623730002ca13947580000000c4016c0ef13d000002900000000000002f880000001010a4979469418f0aab7043d2d5044d2e34d3c2bf08635f8b160003708000000e8a6ab04f14900000dc00000003670d38001a8e0001191fa0000000000000000024b00000018d4a196d5800000000000001b04500003042fc400000038f000000099f190000000000000033d17060000000001a980d70000001102a8d0000000000dce3e5800047abf65812e0000009b092abd400084e45635a0f92de015daca4528b77552a614f9eb980b7205842ac2a712a3c533ad5c35037c9bd897c0eb00006f400071b8000aae000035abf80003360ff8550abcd8a39231d0e322e83169a08c769842fd2388000d29621b6313065f04099d2420a31406e90edbc60412139e35bfc5fc488b5b1124a3250f970d354e3e1d734983cac3e59c9a141bebcf2313a1dbf800014eafe908e88f37123080008be52f0b60a16db33f09abc5fe1666b890a8e4a5e037a0000b384b500000000006a759f00006883f25352ee195000061627495f276d39db6d10c407b4858a4c1bcb0042416c82bcc6b70c87dd9fce7f17cba38e8295400014e0eeec470002aa8c20a91165af792dc8b33d29618f7c00001b8a3c0000001c81604e8e4f9115080dbae12200006c03b400034c0000000b94000000000031200000000003d746b000000000047d8001ca600000db9948a6df02c90001644000000052c432236000128d5ca6545cd245c6c226f5db9da030e3550cfa1b11ba0320db00000009dd5ff02a04a8d9b63d2d6d26277d0fa1390cecca90001add076a7a2a2270cc060a6261b3cd91694c0002b10a0251c42580007ac52563c976947e4473248a58b2c96307b90886f6529291b1bd7b0cd14c60dfc0003e160e8aa1b8ce
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x18357460440195300061361d32c80654c001a0d844cb20195300050b64a76dd7644c00141e96dd773d91300050764e70dd7644c00142d929c375d91300050d64670dd7644c001c0f75dc932d913000607dd7835c7644c00182f75e0971d913000623a1d32087644c001a0d854c821d9130006a24c980087644c0a988e874cb20d91300068361532c83644c001ac13260021d8530007035cd74551620c001a488320154588300048b650855c5620c00184d855cc715883000623611731c5620c0038c9805cc71588300060b61d54d05620c001a0d5460f41588300068355383505620c001a0d5460e40588300060b61d54101620c001a0d5460c40588300068955181101620c001c0c751d1624c0300051325d54589300c00344c97549325971000507e5d5450f63c400581f8755143d8f1000d13e5d524cb658400184f8754932d96100160721d5450d6384001a498360062d951000592259324836544001649901c932d951000703dd1424cb654400181f7460f41d95100060bdd182d07654400184e874c821d951000683611320876544001a493260021d951000613a1d32c836544001a0d844cb20d95100060d61d811906544001a4983600621951000782191324806544001649909093219510007035d1424c8654400181d7460f41195100060b5d182d04654400184d874c8211951000683611320846544001a49326002119510006075d183100654400182d7460840195100060d5d181100654400184d874cb20195100068361132c806544001a898360062d911000507e4d71dd7644400142f925c775d91100050764e70dd7644400142d929c375d91100050d64670dd76444001c0f75dc932d9110005a2640724cb644400188e874c821d911000683615320876444001a893260021d911000623a1d32c836444001a0d854cb20d911000685615811936344001615911d154d8d10007035537250b634400181e8755341d8d100068355182d07634400181e8755040d8d1000683551821036344001a155460440d8d100061361772c83634400188d84dcb20d8d10006856158119063440018c9876006218d1000781550625046344001a15546074218d100070355172508634400181d875534118d100068355182d04634400184d855c82118d10006236117208463440018c9726002118d100060761d541006344001a0d546084018d100068555181100634400184d855cb2018d100062361172c806344001a258560464d891000589644745536244001c0f7455373d89100051365671dcf624400148d949c773d89100053264271dcf624400144f955c373d891000523e5170dcf624400182e8755341d89100068355183d07624400182e8755040d891000683551831036244001a255460440d89100460d21974544514400f8c8865c9300c110
  | 1 => 0x1007035537250b63544a181e8755341d8d510068355182d07635440181e8755040d8d5100683551821036354401a155460440d8d510061361772c83635440188d84dcb20d8d510062361172188635440184d876146218d510062361d84188635440144d971895218d510070355172508635440181d875534118d510068355182d04635440184d855c82118d51006236117208463544018c9726002118d510060761d541006354401a0d546084018d510068555181100635440184d855cb2018d510062361172c80635440148d949db73d895100613a1b75dcf6254401c0f7455373d89510051365671dcf625440148d949c773d89510053264271dcf625454582e8755341d89510068355183d07625440184f85dcd70d895100623e13735c3625440182e8755040d895100683551831036254401a255460440d89510068c551811036054401c0d755c9325905100685214814c96414401a0d854ca21590510062361d320856414401a0d854c82159051006a24c980085641440128d9220d70590510160d605751c1641440181d7560c70590510060b5d5821c1641440188d874cb20590510068361532c816414401a0f854c920590510050725d325915114401c0d641c87354451005896467455162cc401c0d735d15458b310048b650855c562cc40182d875534158b310068355183d0562cc401a0d54e0d4158b310061361573dc162cc40188d845cf7058b310060b61d5410162cc401a0d5460c4058b31006895518110162cc5938c78620971d4e3128507e4d655d0654c40142c925957419531006315c8814c8604c5a3c18301d47458031006160c087551600c40141c975514358031006865508050d600c4012c99220143580310050e25d54901600c401ac1322052058031005a2642724c964d4001c0d755c93259350006075d583dc564d400182d7560b71593500062361d3208564d4001a0d854c82159350006a24c98008564d400128d9220d70593500062361d32c8164d4001a0d854cb205935000683e153248164d417783b862117094e502b513e55635c8635400148c9458d7218d500060e5d08055061541a1c44511cc72584500048d6508154961140018545121d32584500061321d524c961140016449154932584500068c5508050561140014c4974ca21584500160d21d54505618c001c0f7450932d953000607dd183d07654c00182f7460b41d953000613a1d32087654c001a0d844c821d9530006924c980087654c0ad84e874cb20d95300068361132c83654c00182d7460864195300060761d83190654c00182d8760864195300050765c6450c654c001c0d745093219530006075d183d04654c00182d7460b41195300061361d32084654c001a0d844c82119530006924c980084654c00181d7460c40195300060b5d182100654c
  | 2 => 0xe91845a1dccf00c913c8fb298e50d4d913c953b8580dc5d258ce228870d0003cc05074000e8af334e0030d217cb6000c003cd80004105416000bd170ae3d00006c142a0e1010cc358081d492270460004b0008537cfc2747c39c7f01cde124300e4be16c9b044eb38cbf2ac2135056308322a8e811400028dd0788c0405322c900f8622206002ced1b84d36c98324521ccdc1107a2d480340092881911cb80042b0a4552e4693e80025c4027c70144000a8b7409013f8a5390c52b0220cca924cfd04cf50005e21871000a708c00000482c4263bcff2d01f354c40e00029000000000a08409c6b0bc81320000d81c18c25344f63b0c61a0741f4bb2088340c4c000a30383f000f719c00034f8000000f06d2c00019042000001b0f1000060b018150a1400b300066140593042e1f8000800031c002e8650b4f00003d0008d15ce600000000003a800008a00001235c001e4762389a0c40000000000000000032800264000008930cad0688f0000034c43278f91ed0432c4a2f0e21a894091051bc723684e2c8170ec780040602010242400038041e0500818020632014060e0985800000904c0a210180c0003000700e0303000002e0281418010000c020701808224a058400600108280e020002c2c000003412050380c00040000c10350386c0011008040a00048d8320100631dca81cc961d4c0183b74a03545825300691615320876154c01a195460c40d81530160760d75dc56414c0182d7560b71590530062361d320856414c01a0d854c82159053006a24c9800856414c0581d835d470590530060b5d5821c16414c018357560470590530062361d32c816414c01a0d854cb205905300683e15324816414c01c0d735d1545885300e13615731c56214c0188d845cc7158853006325cd801c56214c0182d8755341588530068355183d056214c01a0d54e0d415885300e1361573dc16214c0188d845cf70588530060b61d541016214c01a0d5460c405885300689551811016214c038c8874c9205825
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x48020200e51810600801800140ad390a40a64b20a200a066903021d5458031005093441810eaa2c018802818a75508050d600c401904aa32440286b006200a056905121d325845000508b442890e992c22800304487245524c96114001302d2122a9264b08a000a1269c832015458830
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x80005008b755192201435803100600487690915493258450
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x4b
  | 4 => 0x4d
  | 5 => 0x124b
  | 6 => 0x138b
  | 7 => 0x4
  | 8 => 0x6
  | 9 => 0x94b
  | 10 => 0x94d
  | 11 => 0x124d
  | 12 => 0x138d
  | 13 => 0xcb
  | 14 => 0xcd
  | 15 => 0x12cb
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x12cd
  | 19 => 0x168b
  | 20 => 0x168d
  | 21 => 0x14b
  | 22 => 0x14d
  | 23 => 0x134b
  | 24 => 0xa4b
  | 25 => 0xa4d
  | 26 => 0x134d
  | 27 => 0x198b
  | 28 => 0x198d
  | 29 => 0x24b
  | 30 => 0x24d
  | 31 => 0x144b
  | 32 => 0xb4b
  | 33 => 0xb4d
  | 34 => 0x144d
  | 35 => 0x16cb
  | 36 => 0x16cd
  | 37 => 0x2cb
  | 38 => 0x2cd
  | 39 => 0x14cb
  | 40 => 0xbcb
  | 41 => 0xbcd
  | 42 => 0x14cd
  | 43 => 0x19cb
  | 44 => 0x19cd
  | 45 => 0x5cb
  | 46 => 0x5cd
  | 47 => 0xecb
  | 48 => 0xecd
  | 49 => 0x17cb
  | 50 => 0x17cd
  | 51 => 0x1a4b
  | 52 => 0x1a4d
  | 53 => 0x95393
  | 54 => 0x5253
  | 55 => 0x94053
  | 56 => 0x94055
  | 57 => 0x95253
  | 58 => 0x5393
  | 59 => 0x125393
  | 60 => 0x4953
  | 61 => 0x124053
  | 62 => 0x124055
  | 63 => 0x138053
  | 64 => 0x138055
  | 65 => 0x124953
  | 66 => 0x124955
  | 67 => 0x95255
  | 68 => 0x138955
  | 69 => 0x138953
  | 70 => 0x139253
  | 71 => 0x139255
  | 72 => 0x9d2d3
  | 73 => 0x9c0d3
  | 74 => 0xc9d3
  | 75 => 0x9c0d5
  | 76 => 0x1452d3
  | 77 => 0x1440d3
  | 78 => 0xd453
  | 79 => 0x1440d5
  | 80 => 0x144e
  | 81 => 0x12c9d3
  | 82 => 0x12c9d5
  | 83 => 0x9d2d5
  | 84 => 0x130c
  | 85 => 0x14c
  | 86 => 0x134c
  | 87 => 0x1692d3
  | 88 => 0x12d693
  | 89 => 0x1692d5
  | 90 => 0x252d3
  | 91 => 0x12c253
  | 92 => 0x252d5
  | 93 => 0x24e
  | 94 => 0x12d453
  | 95 => 0x1452d5
  | 96 => 0xa4155
  | 97 => 0xa5353
  | 98 => 0xa4153
  | 99 => 0x14a53
  | 100 => 0x14a55
  | 101 => 0x14d353
  | 102 => 0x14c153
  | 103 => 0x154d3
  | 104 => 0x14c155
  | 105 => 0x154d5
  | 106 => 0x17c153
  | 107 => 0x157d3
  | 108 => 0x17c155
  | 109 => 0x157d5
  | 110 => 0x134a53
  | 111 => 0x134a55
  | 112 => 0xa5355
  | 113 => 0x199355
  | 114 => 0x199353
  | 115 => 0x135993
  | 116 => 0x135995
  | 117 => 0x2d353
  | 118 => 0x1342d3
  | 119 => 0x2d355
  | 120 => 0x1342d5
  | 121 => 0x1354d3
  | 122 => 0x14d355
  | 123 => 0x1354d5
  | 124 => 0x5d353
  | 125 => 0x1345d3
  | 126 => 0x5d355
  | 127 => 0x1345d5
  | 128 => 0x17d353
  | 129 => 0x1357d3
  | 130 => 0x17d355
  | 131 => 0x1357d5
  | 132 => 0xb4253
  | 133 => 0xb5453
  | 134 => 0x24b53
  | 135 => 0xb4255
  | 136 => 0x24b55
  | 137 => 0x1a4253
  | 138 => 0x25a53
  | 139 => 0x1a4255
  | 140 => 0x25a55
  | 141 => 0x144b53
  | 142 => 0x144b55
  | 143 => 0x16d453
  | 144 => 0x1456d3
  | 145 => 0x16d455
  | 146 => 0x1456d5
  | 147 => 0x5d453
  | 148 => 0x1445d3
  | 149 => 0x5d455
  | 150 => 0x1445d5
  | 151 => 0x1a5453
  | 152 => 0x145a53
  | 153 => 0x1a5455
  | 154 => 0x145a55
  | 155 => 0xbd4d3
  | 156 => 0xbc2d3
  | 157 => 0xbc2d5
  | 158 => 0x2cbd5
  | 159 => 0x14cbd3
  | 160 => 0x14cbd5
  | 161 => 0xbd4d5
  | 162 => 0x140e
  | 163 => 0x19d4d3
  | 164 => 0x19d4d5
  | 165 => 0x14d9d5
  | 166 => 0x1a57d3
  | 167 => 0x1a57d5
  | 168 => 0x10c
  | 169 => 0x20e
  | 170 => 0x95a93
  | 171 => 0x95053
  | 172 => 0x95493
  | 173 => 0x104b
  | 174 => 0x1a8b
  | 175 => 0x1a8c
  | 176 => 0x104c
  | 177 => 0xccd
  | 178 => 0xcce
  | 179 => 0x170d
  | 180 => 0x170e
  | 181 => 0x95715
  | 182 => 0x94cd5
  | 183 => 0x95295
  | 184 => 0x1040d3
  | 185 => 0x1a80d3
  | 186 => 0x9ccd5
  | 187 => 0x10154
  | 188 => 0x198055
  | 189 => 0xcd995
  | 190 => 0x171995
  | 191 => 0x199295
  | 192 => 0x1980d5
  | 193 => 0x16c053
  | 194 => 0x1056d3
  | 195 => 0x1a96d3
  | 196 => 0x16d493
  | 197 => 0x16c2d3
  | 198 => 0xcc2d5
  | 199 => 0x1702d5
  | 200 => 0xbd053
  | 201 => 0x20256
  | 202 => 0x5d4d3
  | 203 => 0x1045d3
  | 204 => 0x5d053
  | 205 => 0x5d2d5
  | 206 => 0xcc5d5
  | 207 => 0x5ccd5
  | 208 => 0x24216
  | 209 => 0x14114
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2109
  | 6 => 4828
  | 5 => 3736
  | 4 => 262
  | 3 => 10
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (86469+((h/703+packedAt gbK7 (78033+(h % 703)*12) 12) % 2784)*13) 13
  | 6 => packedAt gbK6 (252661+((h/1609+packedAt gbK6 (231744+(h % 1609)*13) 13) % 6373)*14) 14
  | 5 => packedAt gbK5 (236609+((h/1245+packedAt gbK5 (220424+(h % 1245)*13) 13) % 4484)*13) 13
  | 4 => packedAt gbK4 (19123+((h/87+packedAt gbK4 (18340+(h % 87)*9) 9) % 315)*10) 10
  | 3 => packedAt gbK3 (825+((h/3+packedAt gbK3 (810+(h % 3)*5) 5) % 17)*5) 5
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff03ff81ff81fffffe07f80127b1cfd8cfe7c
  | 1 => 0x3ffc0ffe07fe07803ffffffeda4e31e7333ff
  | 2 => 0xfc3fff00007fff8003ff87fff1c703e383c38f
  | 3 => 0x3fffffff80000003fff8003e07fc03fc03f0
  | 4 => 0x3ffffffffffffffc0000003ff80003fffc00
  | 5 => 0xffc0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x145003180298028a38e44c8180090c6c84563c
  | 1 => 0x281406a202a20504920912a84a061143130d5
  | 2 => 0xd83aad010a555b00925d4655314702a382c30a
  | 3 => 0x503cf6b55b010a01239e64063a07b403dc03e0
  | 4 => 0x822f38c79c679c65c00800183ff000036ba800
  | 5 => 0xe308200610061046001000603ffedbd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36789
namespace PEqualNP.Outside.L_meta_36789
open PEqualNP.Outside.L_meta_36789.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 13 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 75 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
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
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 626 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 bs2_4_192) (concat bs2_4_224 (concat bs2_4_256 bs2_4_288)))) (concat (concat (concat bs2_4_320 bs2_4_352) (concat bs2_4_384 (concat bs2_4_416 bs2_4_448))) (concat (concat bs2_4_480 bs2_4_512) (concat bs2_4_544 (concat bs2_4_576 bs2_4_608)))))
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
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 699 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 (concat bs2_5_192 bs2_5_224)) (concat bs2_5_256 (concat bs2_5_288 bs2_5_320)))) (concat (concat (concat bs2_5_352 bs2_5_384) (concat bs2_5_416 (concat bs2_5_448 bs2_5_480))) (concat (concat bs2_5_512 (concat bs2_5_544 bs2_5_576)) (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 42 := (concat bs2_6_0 bs2_6_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 2 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 6 := bs3_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 13 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 75 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 626 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 bs4_4_512) (concat bs4_4_544 (concat bs4_4_576 bs4_4_608)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 699 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 (concat bs4_5_192 bs4_5_224)) (concat bs4_5_256 (concat bs4_5_288 bs4_5_320)))) (concat (concat (concat bs4_5_352 bs4_5_384) (concat bs4_5_416 (concat bs4_5_448 bs4_5_480))) (concat (concat bs4_5_512 (concat bs4_5_544 bs4_5_576)) (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 42 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 10 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 262 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3736 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)))) (concat (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)))))) (concat (concat (concat (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272)))) (concat (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 bgb_5_2496))) (concat (concat (concat bgb_5_2528 bgb_5_2560) (concat bgb_5_2592 bgb_5_2624)) (concat (concat bgb_5_2656 bgb_5_2688) (concat bgb_5_2720 bgb_5_2752))))) (concat (concat (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976))) (concat (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)) (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 bgb_5_3232)))) (concat (concat (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328)) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456))) (concat (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)) (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)))))))
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
theorem bgb_6_4800 : Interval gbAtlas 6 4800 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4828 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))))) (concat (concat (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))))) (concat (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))) (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))))))) (concat (concat (concat (concat (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))) (concat (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))))) (concat (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)))) (concat (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424))) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584)))))) (concat (concat (concat (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)) (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))))) (concat (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)))) (concat (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640))) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800))))))))
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
theorem bgb_7_2080 : Interval gbAtlas 7 2080 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2109 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)))) (concat (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))) (concat (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920)) (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0eeeaeee8eeeac8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373992 * 2 ^ 32 + 4008364224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36789.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩,⟨.and,[0,1]⟩,⟨.or,[6,7]⟩,⟨.or,[4,5]⟩,⟨.or,[2,3]⟩,⟨.and,[1,10]⟩,⟨.or,[2,8]⟩,⟨.or,[4,12]⟩,⟨.and,[0,9]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008364224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008364224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36789

open PEqualNP.Outside.L_meta_36789 in
theorem PEqualNP.Outside.L_meta_36789 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008364224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008364224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
