import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36731.Model
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
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


end PEqualNP.Outside.L_meta_36731.Model

namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
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

def SBf (j : Nat) : Nat := [6, 4, 5, 7, 7, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 67]

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

def checkRow (g : Atlas) (k i : Nat) : Bool :=
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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_36731

namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
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
end PEqualNP.Outside.L_meta_36731
namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
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
  | 2 => 0xf807f807f80ffffffc0fc0fc0f80fffff24cff
  | 3 => 0x7fff8000fe03ffff000fff000fe07fc70c7
  | 4 => 0xfff80000000fffc07fffff000000fff81f80f8
  | 5 => 0xfffffffffff000007fffffffffff00001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x48304850508020810430c50c508e164924955b
  | 2 => 0x95529534a316552a3a0b50b50d12ab96524cad
  | 3 => 0xc6a4e4a535aa93b45ed824db6424ccc79c70c6
  | 4 => 0xe4c6c6c6c6cd1a276f6db6824848f1e31f80f0
  | 5 => 0x7070707070e1c38738e38e38e7081041b6a00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000aaaaaaaaa0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36731
namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xcc32
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (17+((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 1 => 0xe07f01ffffffffff0781e07c0fffffffe493ff
  | 3 => 0xff8001fff03f03fff801ff800fff07c0f8e3cc
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x220a100460821040188a228462884a4a092615
  | 1 => 0x491462c88514c18b0320c868853194b46490ea
  | 3 => 0x8526b55123a856d568497b2129da4706b8e34c
  | 4 => 0x1658d9a24a0e9b66b5ec12424e6ce218df03b0
  | 5 => 0x1860e1c38c30e3b8c6719c7380708420f6d800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaacc888888eeaaaaaacc888888eeaaaaaacc888888eeaaaaaacc888888eeaaaaaacc888888eeaaaaaacc888888eeaaaaaacc888888eeaaaaaacc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36731
namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x600000001b388000000000000000d002874c0d005800000007a21204000000000024000004800000087800a00000004a0000000000260c2019700ac0132a0802722140194201180500038e52000000000f9016a800003020008304040020000083ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x86601a743e20085016b2885c8e7a90923418420c849c649aac06007c224e2caa3c58a0006e488aae040a40805ea20e527630007e8c4c9400a4325a6a6c2a4a0000004626380062002e000068361c0000280066a80044a6141e02000000008224981256107200789e543a96b070260008216089804a0c7020018101020889402100040030b070802baa921d794a43b7a92876c5250f3ea8a1f3d4943ae29287cc5250e98a4a1d794c43af29e855d53d0b3a87a15d94742baa8e855f5350ab8a6a16750d42af298855d5310abea9195755232af294653e540ca7aa81957d5032cf2a0655d540cb3aa8194755032af29065ce520cb9e84197310832af29e835d53d073a87a0db94b41b6a96839d43506bca620d754c41b7a92636c524c67ca818cf550319f2a4433d54886bca710d754e21e6194435f53486b8a690f30c821af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330b7294616d528c39865905794e20aea9c413f5448278a89057d4d20ae29a41cc32482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x91a40c722b1221e38660aa2613008002ea800200000165109025261368c6250f42c550d51d0a1d6595032c3189540cb0d54d0832b1987420ca4d6510832a318943d070d4354b41a3189435064c6254c41a3590328870e540ca2187590534868d640c8219318953d028c6250e40a3189431030d4354840c550d511028d640cb2087592538828d640c920c315032483443214520
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x828102018168239286a8e858155261d083281aed2a06510d047250d5110206bb0a819241415d03214520
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s3K5 (802+((h/14+packedAt s3K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s3K4 (2640+((h/30+packedAt s3K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s3K3 (990+((h/8+packedAt s3K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (302+((h/2+packedAt s3K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 2 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 1 => 0x89144a441945212c0c8648510a4852d146462a
  | 2 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 4 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36731
namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x90380001f0018015246c00000005804aac01a0430022103930a328c000000000f26a00140861505529019600743a04e5d08900780111a300089004040000040003ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x226783a92249e6c5098742c9688442a00567c725c1a600400085e16b040aa2012aca20c1c18a800588c343e00229c0000007e28527a9a108a3206000e8e70b2862e0a1e4c4600004a6eaea694000084763c3890004800424e6830006462a03600005a005400006a6680a4148204008050210102001001a484828202000023a0020800040052a06baa921d794a43b7a92876c5250f3ea8a1f3d4943ae29287cc5250e98a4a1d794c43af29e855d53d0b3a87a15d94742baa8e855f5350ab8a6a16750d42af298855d5310abea9195755232af294653e540ca7aa81957d5032cf2a0655d540cb3aa8194755032af29065ce520cb9e84197310832af29e835d53d073a87a0db94b41b6a96839d43506bca620d754c41b7a92636c524c67ca818cf550319f2a4433d54886bca710d754e21e6194435f53486b8a690f30c821af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330b7294616d528c39865905794e20aea9c413f5448278a89057d4d20ae29a41cc32482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xb08a8018002e01810ec1e68052092609602248072831028030380c0168c6250f42c550d51d0a1d6595032c3189540cb0d54d0832b1987420ca4d6510832a318943d070d4354b41a3189435064c6254c41a3590328870e540ca2187590534868d640c8219318953d028c6250e40a3189431030d4354840c550d511028d640cb2087592538828d640c920c315032483443214520
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1802892000028239286a8e858155261d083281aed2a06510d047250d5110206bb0a819241415d03214520
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
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2640+((h/30+packedAt s4K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s4K3 (990+((h/8+packedAt s4K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 2 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 3 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 1 => 0x89144a441945212c0c8648510a4852d146462a
  | 2 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 3 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36731
namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa437c53487b8a690d714d21fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52102faa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0x40001805002070380001c000020580c018000e5f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9
  | 2 => 0x9c2402000359b81940011a94b39a85c8219722c744b58704760ecaaa1d3003b0d622a092000958cb0423a5080cd1be618001d30006c4000990009140000008c8e11c82c25a900001f801c5792a948000001270bc0fe000490004ac2507f8004280000590c17c344000001ac000340d900000052a2100046c001a028a0006d1540ce28c0000041c07c000f60000c8ada163e81b8328e30ee910000030003cc1f9820984b02580045a494bd9aa36c3f8a01622202450fa581005b45013f394094b08160006a0512570bc6c0d09fa3dc8981a22240470c7505b35e5382a9ae3e41e803a5107c7b4f982f1ea000001372b80004c0bf1fa6f400156000000001e41ce51c000f90004f11b2290006151213300089c000b636a0000302a282948982420904900002e000000a90d54a04a8000001208c4e209f0000000003309a830349c800a688a524b1da94c7b98746e730f19e70005752098d33282cb00b849a48068052152478ee93e464394ef9440f01bd172301c0298ca98c02a0c12491f0403201e0222502dc991a7028698550373b4470f513a450001198dc43648c001ce3f8138bf118180650558f13822704416f000918c080024e09c000000001e5159e13300000007c0b888ca7a130560d41c864434330fb9313740006123a2a04845e9dc33e5d447a123fc0005215706c4e40007e2c65f4000db0000005c9d0002454b895921e1042788633c0649a8bb42a161051d60346f0618003ca0008a0000008780017400083c000001e4000868000da1407813b03a070119be49e0000003845e4147783d12a00016800000000da0d201e16400000204444a117639206c14191084864b909602e0000017f26840c000000000000000033804c4195f03c8f4db8001cc000bb9512f04645913d10826c9320319231c808e20941c8ec8b04862cc9c0543d842c361f9468198389903ec4d8000dd2d86a4a6824150810ce85d0c24683e8603461006987538e754bd18b2f81887d1f01266246c23c47e390000000000001d0002d48b0eb9660526ecff8c54127f52509701a6ac000851e8668060470e8000849e831e638050de010820b41b301217c5d2001685950321100401002000060101601004090000a02400808010140000402802238040200400810000000805a0203001004008000f0240703c0280c058380b804038020603800892038780681e0506a000060000e0781a0180e0402a10008000060001c08804190060c00010000018001900e008100000000802010260000a0681801822190140181e03830028020080c00022098000300c118200183202870000000489801024038060c02a0900e0080200802068000001400824098020082a010020081400004000080600401002028101400201010010000300400006000080880201004000160701a008
  | 3 => 0xf59ad0ac230d208744a2b08b90a000474f89962524386b94c16a780091e60d47d4e7811490204a49672863e0978ae3b65cc6a000380284b210011a010000003f6610228443a43eca30c641a23923a20306310d29c63de208f115a1125b8b49061c26fccd857134168a99b21dc44cb8018020628010b10ec420ea1cb086000892181f87a40005113c14c3da4c244228c41d815a81c5780004c3a10e23e3269504592e2b0000c9107000338318730006e40000000033c0000014e305029c50003acef09d0000c4bc
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x521086e860484219dd9521086ac6250f4097d8d52d025c6354b40a758c42d032d5210b40a758f41d025f63546409718d519031c5350d40ab189435029d63109408f997415029d63d05408f596411031d5390440c754c411031d53d00408fd95401031d53500409ed95401026e62153309b58854cc31c5450f30b318943cc23f6454b308f19152cc29d640cb30d354832cc29d64cc7309b98b548c26d62d52308fd91518c23c64546309bd89544c26c62551309dd85544c274615513097195434c31c5450d30b3189434c29d640c93097997314c29d64cc5308f596540c23e64150309798c540c25d658c430c7552310c31d540c430c7553300c25f654c030c7551300c27b654c0309798c54c825d63153208f99053c823d6414f20ba18121c825e63d52209758f548825e63152209758c548823e64d4e208f593538831e5494e20c7552538831e5454e20c7551538823e6414e208f590538825f63551209718d544827761551209d185544825e63151209758c544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65c8520ba181214825e63150209758c540827661150209d584540823e6414c208f59053082766114c209d584530823f64544208f191510825f63544209718d510826d65884208f992500823d64940209798e500825d63940209bd95200827b65480209798e54c425d63953108f99253c423d6494f108fd9152c423c6454b1097d8d52c425c6354b109798c548425d63152108f990538423d6414e108f993528423d64d4a109798f528425d63d4a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427b60549109b994524432f5414910cb150524434f5314910d314c524436852c41109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436860548108f990520423d64148109798c520425d63148109b988520436952c80109e59420042f161080109e596100427765440109ed9510042e86244010
  | 1 => 0x6e291f694b0eb02ba9cadc969d40d030000000480c0409019804e4616000041e0003004050f00800010400800000081406050780c06030601c003c000001e280100412000780800020300078100004806020302c2602000280603000002a050201802000800c220b118000005010084401008701e0304040bc040084400060e8000a3e0080406000001402050081806292d004042d0600c0e000301c1602020040001090040053d3d0c5250f2e4314943a75924310e3f6550c43ab1894310e5f6550c43b31894310e9f6550c43c7d954310f8f6250c43a71894310f8c6250c43a31894310f1d4354843c750e5110f1d4354043ab18943d0a5f63546429718d5190a5e63942429758e5090a3e65d0d42c714f4350b1c5350d42ab1894350b4c53d0942c714e4250b4c6254c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f6550842b318d4210a7a60153329e58054ccb1c5450f32b318943ccb8d43d0b32b358c42ccb8e4310b32c7d50438ca3f64546328f191518ca3e64942328f592508ca3e649513297d8d544ca6f62551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32b3189434cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540ca5e631503297597430cb1d54d0c3297594430cb1d5410c32cb553420cb8f43d08329b594420cb8c4310832c7553320ca5f654c832a7191320cb1d544c8329bd95320caac644c832c794d43906ac6250e41a758c429069d63d06419798c505065d6314141ab189431065f63548419718d521069d6310841cb548421069d63d04418fd95411067765504419b98b548c66d62d5231c7951438c6cc6250e31a7590328c69d64cc6319758e544c66f62551319b189544c67b60551319e181544c63e64141318f590504c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c31c7151430c6cc6250c318fd91520c63c6454831a7590320c74d520c831a7593310c65f654c4319dd95310c65e63153219758c54c863e6414f218f59053c863e64943218f59250c865e63943219758e50c865e63d52219758f548865e63952219758e548863e64d4e218f593538863e6494e218f592538863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534873b54d4121ce153504875b53d4121d614f504873b5414121ce150504875b5314121d614c504876a21141219798c540865d63150219e980540867960150218f990530863d6414c219e98053086796014c219bd9
  | 2 => 0x680009f1f00014abdaa20000a001e800000002cc0000014800aa0f2a700000000b91243d12e9e0eeb4a84950ea22290081c6c200091a2834016530e66ea96848d22f9c8bb8e84a2642c0fe9b0a28b1e0891fe198e01618e931fc6087e8706c5e09871286048fa9d1dc1f1ca41b142d9a27b922b5ac40a1527782a0784835a0a8e1f4ac09a4131619000af2e623ae8003064c29e1aa42ad194c08069780000234168e417192139800bafa319ae4e1a6000f6542f05d21e988028592c03a6a178f85627e702ca6c29a2a826b89566b2fe6e200389261307825090822fc4da4a2321a181b6880008993a51a680226e0000075800282be618ca330005e9b200000002f8000001b8006a2f42f25856996bb014840007a8008b8000030cb0800001427389c6693c692ce4f80093a5c00000760005927a320b47b29458a56003103014e308000015ea3800219bea2800000006624800076002501c16c6f2700f18c1c8007e8008fa76831c2000805f0000300000222041340003a8d8007e07a248ce35000002f2ab9025a9400000046000ba8000003678900c0040c4856ac8fc0000000044852b68c9d0901680c908c11cc4704a9818a6710a0012ab781a8389eb5000000003c0dc2a068a01b4189848aaa08eada768de448b8a30c41181ca0a3c452ac4c8d80fa665f800369e615190b60ac7c804142c86a98847838a4a440899e44000790ba1080000082572e05c896aa8a60b1448090c45800598745c2b83b2305d95443b0a81824228004828821000b400046ac65216074aa6a6204062a4860b22b9
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1900044000000000000d00700001240804615825c0960000136cc10b3940ca01700054000000000000068000f00000992100204281835d46250c43a18e4a1aa421d0c7250e5110e8639286a8087465c05450f32c18a8312879948d7690c42ccb062a0c4a1a658318c6255032a1aeba1e841960d6510c420ca0e3b2a8990658394c6250e41a18e6a908420e0d6354842107072a0c4a1c63435c85450c31a32e02a28618e0c54189430c6863a2a41906383591520c831a18e6a9085a060d6354842d0306298c4a1a81435c85450f30c18a8312879850c7454832cc306b22a419661831506250d30
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x34080a09801506250f32a09801506250c3180c87591520c83180c87591520cb30
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
  | 4 => packedAt s5K4 (16236+((h/132+packedAt s5K4 (15048+(h % 132)*9) 9) % 476)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 63)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3ffff81ffffff81ffc1f0fffc3ffffb81f1ff
  | 1 => 0xfc0ffffe07fffffe07ffff07ffc1fffcfe3e3f
  | 2 => 0xfff01ffff80fe1fff801fff87ffe1c070fcfcc
  | 3 => 0x1ffffff001fffffe00007fffe007f00ff0
  | 4 => 0xffffe000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4841488c412250805950504c9413255180d0d5
  | 1 => 0x11228110324480160282a10128404aa036262a
  | 2 => 0x28a4d22490e9032aa8213a904ea410360b4b4c
  | 3 => 0xb2cb1c492481d5cd34f408c4733980c7d00db0
  | 4 => 0xc30c1871c70e19f1c739cce602310307edb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888ece8e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36731
namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1dac00018425600315393400400e4d20005ea0020029383d2a04e242843a8801b0000b800200000462c32600293c0241d456d54402800686243c6401ea8534d7917c4d32a0000000000000000fc30e08083040000102140008e0214000000405ff5300ff94c05fd5300ff14c03fe43007f50c03fc43017fd4805fe52017f54805fc5200ffcc801fe32007f4c803fc32017fd4405fe51017f54405fc5100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2003ff58e10005fac70800ffc63840077e31c200affd4e1004ffca70802bfd5384013fe29c2009ff90e10007fa8708027fc4384007ffb142003bfd8a1001ffcc508002fe6284007feb142000bf58a1001ff8c50800efc6284015ffa94200aff94a10057faa50802bfc5284013ff9942000ff8ca10007fa6508027fc32840117eb0c200affd4610057fca30802bfd5184015fe28c2009ffcc610007fc6308003fd3184013fe18c2000ffc8610007fc4308003fd2184001fe10c2003bf9821001ffea10800ffe5084007fea842003ff1421001ffe610800ffe3084007fe9842003ff0c21001ffe410800ffe2084007fe9042003ff0821001ffe210800ff71084001fd8842008ffd9510045feca880037f65440013fb2a2008ff99510015fcca88023fd65440117eb2a2008ff19510015f8ca880237c65440053e32a2000ffd8d10005fec688003df63440016fb1a2007ff98d1000dfcc688003fd63440017eb1a2007ff18d1000df8c688003dc63440036e31a2008ffd4d1003ffca688023fd534400ffe29a2007ff90d10007fa868801ffc4344001ffb122000bfd8910007dec488002ef6244001ff3122000bf98910007fac488002fd6244001fe3122000bf18910007d8c488002ec6244011ffa922008ff94910047faa488023fc524400fff9922000ff8c910007fa648801ffc3244011ffa8a2008ff94510047eca288023fd5144011faa8a2008ff1451003ffe6288003fe3144001fe98a2007ff0c510007fe4288003fe2144001fe90a2000ff08510047fea08800ffe5044011fea822003ff1411003ffe608800ffe3044001fe9822003ff0c110007fe408800ffe2044001fe9022003ff08110007fe2088003fb1044007ff0822003fd8411001ffeca0800eff6504007ff3282002bf9941001efcca0800a7e6504007feb282005bf5941001efaca080027d6504007fe3282003bf1941001ffec60800eff6304007ff3182001bf98c1001fbcc608006de6304007feb182000bf58c1001fbac608002dd6304007fe3182003bf18c1002ffea608013fe530400bfea982004ff14c10027fc8608003fd4304009fe2182003ffd881001dfec40800ffe62040017f3102003fb98810005dcc40800ffd62040017eb102003fb58810005dac40800ffc62040077e3102005ffd481002ffca408017fd520400bfe2902004ffcc810007fc6408003fd3204009fe1902006bf9841002ffea208017fe510400bfea882005ff14410027fe6208003fe3104001fe9882004ff0c410007fe4208003fe2104001fe9082000ff0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0xffc5088007ff9844003ff8c22001ffa611000ffc3088007ff9044003fbc8220007f64110047ff65480237fb2a4000dfd9520004feca90047fe65480057f32a4011ff5952008dfaca90047fc65480057e32a4011df19520014f8ca90003ff63480017fb1a4010ff98d2000dfcc690003fd63480017eb1a4010ff18d2000df8c690047ff5348021ff29a4011ff54d20087f8a690043fe4348001fea1a4010ff10d2008ffea490047fe5248023f72924011ff5492008fdaa490047fc5248021ff9924000ff8c920007fa6490043fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf1852008ffea290047fe5148023fea8a4011ff14520087fe6290003fe3148001fe98a4010ff0c520007fe4290003ef2148001ff10a4000ff48520007da4290003fc2148023ffa824003ff9412008ffaa09000ffc5048021ff9824003ff8c120007fa609000ffc3048001ff9024000fec812001ffc409000fee2048007ffb284003bfd942001ffcca1000afe6508007feb28400ebf5942001ff8ca1000efc6508007ffb184003bfd8c2001ffcc610006fe6308007feb184000bf58c2001ff8c61000efc630801dffa98400dff94c20077faa610037fc530801bff2184000ff50c2006ff8861003efe620801dffa90400cff94820077faa410033fc520801bff990400cff8c820007fa6410033fc3208007ffb084003ff98420005fcc21000ffd61080017eb084003ff18420077fea21003bfe510801dfea88400eff1442006ffe6210003fe3108001fe988400dff0c420067fe4210003fe2108001f71084000ff48420067f84210003ec21080077f3004003ffd402001ffca01000ffd5008007fe2804003ffcc02001ffc601000ffd3008007fe1804003ffc802001fde401000ffe2008007fd1004003ff4802001fda4010003f9200800dffb2e2006bfd9710037fccb8800afe65c400dfeb2e2006bf59710037f8cb8800afc65c4001ffb1e2000bfd8f1005ffcc788006fe63c4001feb1e2000bf58f1005ff8c788006fc63c400dffa9e200bff94f10037faa78802ffc53c4017ff21e2000ff50f1005ff88788003ff62c40017fb162000ff98b10005fcc588003fd62c40017eb162000ff18b10005f8c58801bff52c400dff2962006ff54b10037f8a58802fff32c4001ff1962000ff4cb1005ff8658801bff51c400dff28e2006fd94710037faa38801bf551c400dfe28e200bffcc710007fc6388003fd31c4017fe18e2000ffc8710007fc4388003fd21c4001fe10e2006ffd431001ffca18801bfd50c4007fe286200bffcc31001ffc6188003fd30c4007fe1862000ffc831001ffc4188003fd20c4007fe1062003ffd961001dfecb0800ffe65840057f32c2003ff59610055facb0800ffc65840077e32c2003ffd8e1001dfec70800ffe63840037f3
  | 2 => 0x3001ffc811800ffc408c007ff9846003f7cc23000ff6611800ffc308c007fc1846016ffd95300b5feca9805bfe654c0057f32a6016ff595300b5faca9805bfc654c0057e32a6000ffd9130005fec898057fe644c02f7f3226000ff59130005fac898057fc644c02f7e3226016ffd51300affca89805bfd544c02bfe2a26003bfd8d3000ffea698007fe534c003ef29a6001ff54d300b7baa698007fc534c003ffa1a6001ff90d3000fbc8698007fd434c001eea1a6001ff10d30007fec498002ff624c001ff3126000ff58930007f8c498002fc624c02dffa926016ff949300b7faa49805bfc524c02bffa126000ff90930007fa8498057fc424c003ff9926001ff8c930007bc6498007fd324c003fe1926001f70c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c02dffa8a6016ff945300b7faa29805bfc514c02bffa0a6000ff90530007fa8298057fc414c003ff98a6001f7cc53000ffc6298007fd314c001ee98a6001ff0c530007fe4298003fe214c001fe90a6000ff0853000dfec09805bff504c007ff2826016ff5413001ff8a098057ff404c007ff2026000ff5013001ff88098007ff304c003fd9826003ff8c13001fbc609800ffc304c007ee1826001fe0c130067fecb9003eff65c801fff32e4002bf9972007ffacb9003efd65c8019fe32e4002bf19720067fec790002ff63c8029ff31e4001bf98f20007fac790002fd63c8019fe31e4001bf18f2007ffea790053fe53c801ffea9e4014ff14f200a7fc8790003fd43c8029fe21e400fffd4b20067fca59003fee52c801ffea96400ffb54b20067f8a590053ff32c8019ff1964000ff4cb20067f86590033ff61c8001ff30e4000bf98720007fac390002fd61c8019fe30e400fffd472007ffca39003ffd51c801ffe28e4014ffcc720007fc6390003fd31c8029fe18e400cffc8720007de4390003fe21c8001fe90e4000fb48720067f8439003fff50c8007ff286400fff5432001ff8a190053ff30c8007ff1864000ff4c32001ff8619000fff65880077fb2c4003ff99620015fccb1000ffd65880277eb2c4003ff1962001df8cb1000fff63880077fb1c4003ff98e2000dfcc71000fde63880036f31c4003ff58e20005fac71000fdd63880016eb1c4003ff18e2001df8c71004fff5388025ff29c4013ff54e20097f8a71004bfe4388001fea1c4012ff10e2008dfac51004fff5288027ff2944013ff54a2009ff8a51004bff3288001ff1944000ff4ca20097f8651000fff6188007ff30c4000bf9862001ffac310002fd6188007fe30c4013ffd462009ffca31004ffd5188027fe28c4012ffcc620007fc6310003fd3188025fe18c4000ffc8620007fc4310003ee2188001fe90c4000ff08620007d8431000efe6088007ffa844003ff9422001ffaa11000
  | 3 => 0xf30c421cffd46210e7fca310873fd5188439fe28c4220ffcc621007fc6310803fd3188441fe18c4200ffc8621007de4310803f72188401ffb044200ff9822101dfcc110803fd60884017eb044200ff182210e7fea110873fe5088439fea84421cff14221107fe6110883fc308843fffb2a421fbfd95210fffcca9080afe654843ffeb2a421fbf595210fff8ca9080afc6548401ffb1a4200bfd8d21007bec690802df634843dff31a4201bf98d21007fac690802fd634843dfe31a4201bf18d21007b8c690806dc634843fffa9a421eff94d210fffaa69087bfc534843dff21a4200ff50d210f7f8869087fff524843fff292421fff549210fff8a49087bff3248401ff1924200ff4c9210f7f8649087fff514843fff28a421fff545210fff8a29087bff3148401ff18a4200ff4c5210f7f86290803ff2148401fb90a4200ff88521007dc4290803ff60484017fb024200ff98121007fac090803fc60484077e302421fffd41210fffca09087ffd504843ffe282421effcc1210f7f86090833ff65084377fb28421bff99421015fcca1086ffd65084377eb28420cff19421015f8ca10833ff63084017fb18421aff98c2100dfcc610803fd63084017eb18420cff18c2100df8c61086fff5308435ff298421bff54c210d7f8a61086bfe4308401fea18421aff10c210edfcc41086fff5208419ff290421bfb948210dffaa41086fed5208419fe290421affcc821067fc6410803fd3208419fe190421cbf984210dffea21086ffe5108437fea88421bff144210d7fe6210803fe3108401fe988421aff0c421067fe4210803ef2108401ff1084200fd88421007fa4210803ed2108401fa908420cffd8021007fcc01080efe6008401feb004200bf58021067f8c01086fff5008437ff280421bff540210dff8a01086bff3008435fe1804203ffd963001dfecb1800ffe658c0057f32c6003ff596300cdfacb1800ffc658c0077e32c6003ffd923001dfec91800ffe648c02f7f3246003ff59230005fac91800ffc648c0077e3246019ffd52300c7fca918067fd548c031fe2a46001bf58e3000ffea718007fe538c003fea9c6001ff14e3000ffe8718007fe438c003fea1c6001ff10e3001ffec51800ffe628c0017f3146003ff58a30005fac51800ffc628c033ffa946019ff94a300cffaa518067fc528c031ffa146000ff90a30007fa8518063fc428c003ff9946001ff8ca3000ffa6518007fc328c007ffb0c6003ff98630005fcc31800ffd618c0017eb0c6003ff186300cffea318067fe518c033fea8c6019ff146300c7fe8318003fe418c001fea0c6018ff1063000ffe6318007fe318c001ef18c6001ff4c63000ff86318007dc318c001ff90c6000ff88630007fa4318003fc218c0077f3046003ffd423001ffca11800ffd508c007fe2846003ffd02
  | 4 => 0x807ff438c403ff21c6201f790e3100ffa8718803dd438c403fe21c6200ffd8a31007fcc518802fe628c401feb146200bf58a31007f8c518897ff528c44bff2946225ff54a3112ff8a518893ff428c401ff2146200ff50a31127f88518807ff328c403ff1946200f78ca3100ffa6518807fc328c403ee1946201bf9863112ffea318897fe518c44bfea8c6225ff14631127fe8318803fe418c449fe20c6201ffcc63100fbe6318807f7318c403fe18c6201fd0c631007fec118803fe608c4077f3046200ff58231005fac118803fc608c44bffa846225ff9423112ffaa118897fc508c449ffa046224ff1023100ffe6118807fc308c403ee1846223ffd953111dfeca9888ffe654c4057f32a6223ff5953111dfaca9888ffc654c4057e32a6200ffd9131005fec89888bfe644c42f7f3226200ff59131005fac89888bfc644c42f7e3226223ffd5131117fca89888ffd544c445fe2a26201bfd8d3100ffea698807fe534c403fea9a6201ff14d3100ffe8698807fe434c403fea1a6201ff10d31007fec498802ff624c401ff3126200ff58931007f8c498802fc624c447ffa926223ff9493111ffaa49888ffc524c445ffa126200ff90931007fa849888bfc424c403ff9926201ff8c93100ffa6498807fc324c4037fb0a6223ffd453111ffca29888ffd514c447fe28a6222ffd0531007fc8298803fd414c445fe20a6201ffcc53100fee6298807fe314c401ef18a6201ff0c53100fb86298807f4314c401ffb026200bfd8131007fcc098803fd604c401fe3026203bf1813111ffea09888ffe504c447fea826223ff14131117fe809888bfc404c403ff9826201f7cc13100ff86098833ff65c843b7fb2e421dff99721015fccb90877fd65c843b7eb2e420cff19721015f8cb90833ff63c84017fb1e4221ff98f2100dfcc790803fd63c84017eb1e420cff18f2100df8c790877ff53c8443ff29e421dff54f2110ff8a790887fe43c8401fea1e4221ff10f210effea590833fe52c843bfea96420cff14b2110ffe6590833fe32c8401fe996420cff0cb210effea390877fe51c843bfea8e421dff1472110ffe6390803fe31c8401fe98e4221ff0c721067fec190803fe60c84077f3064200ff58321005fac190833fc60c843bffa86421dff943210effaa190877fc50c8443ff9864221ff0c3210e7fecb10872ff6588439ff32c4202bf996210e6fccb1080a7e6588439feb2c421cbf59621006facb108027d6588439fe32c4202bf19621007fec710802ff6388441ff31c4201bf98e21007fac710802fd6388441fe31c4201bf18e210e7fea710883fe5388439fea9c4220ff14e21107fc8710803fd4388441fe21c421fbf58a210e7fea510873fe5288439f7294421cff54a210e7daa510873fc5288441ff9944200ff8ca21007fa6510883fc32884377
  | 5 => 0xd43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1802fc6250c55ffa92862aff94943157faa4a18abfc5250c03ff9928601f7cc94300ff864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a862affd4543157fca2a18abfd5150c55fe28a8601ffcc54300ff862a1807dc3150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028603bf18143157fea0a18abfe5050c55fea82862aff1414300ffe60a1807df3050c03fe182860cffd963214dfecb190a7fe658c8057f32c6429ff5963214dfacb19033fc658c8057e32c640cffd9232005fec9190a3fe648c82f7f3246400ff59232005fac919033fc648c82f7e3246429ffd5232147fca9190a7fd548c851fe2a46401bf58e3200ffea719007fe538c803fea9c6401ff14e3200ffe87190a3df438c803ff21c6401ff50e3200ff88719007dc438c8037f3146429ffd4a32067fca5190a7fd528c819fe2946428ffd0a32067fc8519033fc428c803ff9946401f7cca3200fde6519033fc328c803f6194640cffd8632007fcc319002fe618c801feb0c6400bf58632067f8c3190a7ff518c853ff28c6429ff5463214ff8a3190a3ff418c851fe20c6401ffcc63200ff86319007dc318c819ffb046400ff9823201dfcc119003fd608c8017eb04640cff1823214ffea1190a7fe508c853fea846429ff14232147fe81190a3fc408c803ff9846401f7cc23200ff8611909fff654c84f7fb2a6427ff99532015fcca9909ffd654c84f7eb2a6427ff19532015f8ca99003ff644c8017fb226400efd91320057ec89909bfe644c82f7f3226400ff59132005fac89909bfc644c82f7e3226400ef191320bd78c89909fff544c84dff2a26427ff55132137f8a899006ff634c803ffa9a6401ff94d3200fbca699007fd534c84feea9a6401ff14d3200ffe8699007fe434c803ef21a6401ff50d32007ba8699007fc434c8037fb126427ffd493213ffca49909ffd524c84ffe2926426ffd0932007fc8499003fd424c84dfe2126401ffcc93200fde6499007fe324c801ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf1853213ffea29909ffe514c84ffea8a6427ff14532137fe829909bfc414c803ff98a6401ff0c532007fec099002ff604c801ff3026400ff58132007f8c09900efc604c84fffa826427ff9413213ffaa09909ffc504c84dffa026426ff1013200ffe6099007fc304c84bffb2c6225bfd963112ffccb1880afe658c44bfeb2c6225bf5963112ff8cb1880afc658c401ffb246200bfd9231127fcc91885efe648c401feb246200bf59231127f8c91885efc648c44bffaa46224ff9523112ffaa918893fc548c4037eb1c6201ffd4e3100ffca718807de538c403fea9c6225f754e3100ff8a718
  | 6 => 0x100023424d08a28a8b880000000016c0000000e525e8f6c2ca2d81b8000000d28001379af000061000101a5700000001d5f50000000000ab800000000193000128a691071370000ea00000000004b8000000220cd0000e100c4a59f7801401400801800002001001000404c01000400401400000401800000000000800c00000002000801000000000001400000400800800000000800402800401003401000000401800000800c00400400001c01800c00800001000000000403c00400400000403400000000000000000002c01400001800001400c00c00000000000001000800000400400000400801400800c02800400801001000400000401001800c00400400400000001800003400800400800c00400000400c04400000c02000800000001800000400800003800400c00001000400000000400000c00400000c00400c00400000800c00000000001000001800800401c01402800000803800800000800800000000400000401400401000400c00400000c00800c00c02400000000c00800400000800000400000000800400000400000800c00000000800000800c00001000000c00c00c00c00c09000400000001400000000400801000400001400400402800000401400400402401400001c00000803c00000801000c03400c00400000000001400000000c00400000801000c01800000002000801000c00c04400002400803403800000000000408c00000000800000000402002400001001800400400400003401401400000007400400800400800800000c00400000c00403002000401403000000000400004400400c01000800001401c03800c00400000800400002c03c03401400c01401002000400000000000002c04c03c01407800800801c00000001000400800400c00800000000400801400c00c00c00000c00000c00000802c00400401801400000c00000001800c00002400000000000000804c01c01401801800802c00005800002802400c00403800000404c00002000003c00000001002c02400000000c01c00003000400800400800c03800000001000c02400003400001000000800401801c00c00400001400c00c00c01403c00400400803400400400008000000401400000000c00000c03801800c01401c02400401801402c0000000a400000800000402002000402800001801000c02401800001000004000c00000000000000400000400001000000400c01001400000800002006800000400001800400c01c00001800001c00001401400400801002c00800000000001c00000402800402801c01801401855ffb2a862abfd9543157fccaa180afe6550c55feb2a862abf59543157f8caa180afc6550c037fb1a8601ffd4d4300ffca6a1807fd5350c03fe29a8601ff90d4300f7c86a1807fc4350c03ee21a8601e71
  | 7 => 0x7ccb780000012110b4000002639c2d7f113e2706fe6118503ac0011d8000c0a148a2a1500018b80000000025d000000000000000212a3500023580000000000000000021000000000011a8001815224a7800183800000000000115c8bc9ea0e9d714f12680000017cda9800007010db85db80026800017e0e60000000a4000000000181c000000000000000001f600018cc0002d98f00000012d9f68002182980000001d8cba8000f4da191987e5950c746a950523c001da950a4b8000000001bc92d10f9d4d115be8740f36991d60001c24dcc090000270001ac06a4000441d9400000005c001e064e8905ff077dc40aa1bb05dc45c8317789300023c0e080000019a0000fa9e9a8556b91b88b4bc902c000000eea3900005b8000000000000b943440000000020080000000000000000002248195280005280000d80025a80028900025800000000009a80027805393b00003d000000110c000000001180001c4c0000000000018280015a8000db1e81c90000c1887a299881d3045427989620d788000000001e799700018d93aa778739a840000012810799200000018900000000019dc0029c897800058a290bda8580012300004c1bc291dfe17c1046191da283000000000000000000147022c35dde1b78000001df18a5989df4ed1800e5800000282862c000001cb9640828000000001468770491f58500000fcdfc910400194191c1681e50b1f980001c02f41f687a8107da8a10d1d40100ea5a543a93b8f80000000001b10dbe84cec044cdc20a000127c00266a4dd368e3680909938e6297e9fb8918e495212022a1f30eadf481bc390cd80d40008d40024580018ac79961991055a671fa19b21182a8001152081811590468f66950000001c327228c00b000000000132aa01d68000cd4d580008d0000c14000001e11cc01fc0000017589286a09d81701ec0000000000000022100014988c1134000be8000030000e906bc0000000000000014a8001d897800009480000000015d0001ac9b5a6c80000027d0000c980000000005cdc8a1714620c80000003f87509f80024780025ba0891550a8fc26c00000000018480014580827c82ea46a0703a0000000000f14000001ba0000000001a80ab0b15e1903a451c722600014e0eb8002768608f003500006b4000bb9a301269a94b1fb1c6d3a0f1119000000000000000202a03a7b80013f8002060811a8c000d629cc001738000001db0000fea2899ac000000001a2c0000022e1e58000310c8ce292726884940029a5afc000b680000015385e400000227c531f000019804a00000004b4002188000000001c580000027b1110000001c10d49cf00020b08e8000050000000000000000000458000428784576518011ee80000007b13f0001a5e348628b81c5dfd2300f3a319a606ae30a3
  | 8 => 0xef8f880000000016b0eb55619980009605195e0781b500000016296d081c001fa913987e9240000000000000014f65780028b81e80000015998204c5611b18001a950e823d842419d5c138000001a529f8000f28431af4000001f18000000000b0c000c580020d19c0000d98000000a39e52090001808000001a6c7a018a3b8da8000cb000000000049d50c00076c000249580a682d05a8001d980010304a8078718002160211b81ddc0003480000000017229e00000006d8cfc0028d0510d100023880000019e0000000000001d80000ef0bb00000000024e000000197a0129987e0f0c1f000242a7000020580000005c04840000015f00000009a4001c480026e1e68001ab00016689e00007112e0418000e2c0016a00028b4191818000ac1e28000fd1221e41f2800000109c00167800090e5902f8000000f480003940000023702189380018aa1c8001baa5e1518000f40000000000000000001fd80000017d00000000008f1710000f04000000f74002431a08000988000ff1c9a940b1a051c200028818c54300008e41f8000281d91238000000d04000000000000318fbc0000017494280000024c02e4000199859141d51160700401c1e4128e8e440026f80008b0000001b7c001928000000880000708001f400000015680012f8000000002860000000001ed0a32491040aa9889d00dc66e8d6a5a29624b08ac7dc0a000131c0003595b9e140021e0eb0001f9da9c00154dbd8000000efc0007b9f8a400a7c691a59000001ca2498bd204800028a0d8668000f60994998000000a98e98a0c000000000000001de80000000000001a0000a20000b600b97b1f70000a840000000023d8550000000000000000001898001b39ec8001b085d00006f8000000000b28000000000000f24000000000000000bf80000029e9a91b293c80000008dc001600001cc80017f80000006f40018f8000000001188791bcc0003d98d04bd382758001e240000011319480022b0d71101ab80000000000008d800000000000000044800000000000000226a9200000000000008340006600000000014c9d78000578db90fcea800103e4a8614000002511d11735e2c0012504460b9f81630b40f9a362550356368e80e389c979a5680014215a1011d18001869c78a90af8332529f122c8000000000000704000000000ad9418aec5080000000023e10c00000000000000028885980000002b1588de06ecf70760ae9ced990a511c92c8564001c182b800047de001a8000000001eb00000000027e1c34a01dc972a8f000260a15a7111d0410000900000001310000000000000000000000000000001b6c8a9968fe0cc0f0915a1f921a0f8049450df88c45e27d80004724480000003080020300000000c8002408001388000000001768b30000e71449ce0f3c00000
  | 9 => 0x9c555b0d419391b1b00c39aaa87114c4f061ca8c0022f057258800056d8d62f84d97d9ce46390500025c20f14e85d65d8000000b11ae00003e00000005e8370ee0788000000624076820001a400000010a0d200a979298e000001a700003780000024380014100029b80003980001b28180020c0000001d592a26a934a740000000bac000000e88000000001409760980be0000b1cfa0000e30cc80000024f16d82c21b021623000067800000000106800131a49c0015c068a5480011e00000022007313252611c133a730058001fa44d1278000000f7a098aca69a3f12925980016f271a2212853200013e1530ae4000000000000002178001f3c0010d80021a18799d16a8000b918e00003c26411780000016ca20a07a8e18e8a04dc94d9dfc000f5c001e88002988e9c000000630000b20b70001f900f16397d46b18765f25417000001400006c4000000e78000000f44000fd8000000000000001dda3d021c6c00017a80003000006700000000007f0c30add924de8cb85205c8115830250682131a7d771a2006567072823006a85c1323f8001dd5eb80cc000001d54000000db40000007a80e0000c7c0008f9719d28a6011e969e92909b22068001b60b9cba0000ca0a1c0000000027286f13315dcc0c0000002927988ecc213c2788d2c00253a4800027c2771400000c853d8e41918000af0f56219c747c17418b5c61f200022ea85099e2aa1385f1ae84b0002142848000a8a4600000000004a4238259240ad4002678a48000619a7a2c182447a330001caa338b09578000000000b2cb588f40000021c0000000a70002168000d1c000001cf8000000001ff8fb0d786d40029f170800189c0000019c80005400000020a9a10298001b400000000010800000000000028d9ee2948001d9e89a6603681280000002059e41ddb300006ea65a9381c84e9145a65cd1298ffa6a14c000000122cd35e09a024e54f88681d8320000002440ce19a4d0cef8000001394c921a9648c619ba00c0024712f00006400019eccf400000190a0228c80c0000000001c080000027640000028fa1d98727a0cf1168990a81149020e3c338ef509188c0025c8001488000000001e20000d24c020184086cd4a0df1f3814a275490898580e18158a10d8000020c0000000017c40000000028423c80023a1b71960000000000000001dd0000000000858000000000000000001dede628384c80000000000e80007580000000000000027393409b80000000000008880000007d00001e00000016e2912521d44001884d1423400011157160939a228c6a650000c28000afc0000000011713600000017a0001af9a391f99f92b8dd9bb415228293003a648720160ae2620c789d15d92b11eda4e561ea8d0a99e9b09097dd5f8f18001de55482429c4001a489521106e29c1
  | 10 => 0x286896a958768cec4740000012c2a0a1980015e4b480000000010628b04f80011e89716600000019f4000cf8488001308389e48a0a708201b98c0692c000001555bf80027a93e8000001128000000000d500000026f0001aa40001ce4c965a1f18b00015500000014400012e80022d0809bc42a2258b51bbcb01438f5885112e1d0620b2523550056a378ec9e71be2748fd6489b74ce5e302282fd00a9d0d306d2250001b88001fc00000000280ddad0825ec00990f03285d9a889a0000000000000a747740017b8778840438000000f1c7d64d8958f2020800006c0000007e8001e38dd0b38000c1c82cf91a280000000023a8000000d01c44000121ea05900029a1a440000000023801c4000000000000fb8001620ba69bd4d00000000000004e00000009c1d382e000199d302322328108c88da03e800098d5103f0178018caa8bcf30cdd3580000000200000000012586ba5316800021ea3e95e80013500000000000000006c80027f0000c70001a680000000000020426d80027e80000000000016e9cb1a3d0e1058a192098a0549bd03c8002631c280029b6970381c69ef26d0001c7c0000000000018bdc3c000000000910000000000000001e0c001034261c390a50acf69902120fc59b56f883848d04839c008fc88b90c9aa01802ec34c4ac1193d02f08cdb683b84994828c4af67900000608c86000000000000018603600000000000003a54fd4789208fe5b16506580022b8000c500d05a04207c8f50000001fe80000019f0001aacc80b9894164e501698000001a34000000000000002929cd8000e00000000000000eda9ad542558000000c10000001dc17c80029199d800000008800026a4f9b90ad000000057e2400000022040000022480005b1e369d8000001c81e1c000000000001ad8001bb8acc870e68698e2046e6b00012a8bc1d20000b04d880000027507f8a140006e66b9d481d0001690d38c400000000000008000000021b80000000009f00000022380008206518c80000010b8000001c657300000000011083b180c000ce91223b111c560040000d1800000045250924800000046400000195a61955874911a9000011f0f2d2280020e0000480001b484619e91240000023988e0002801029f08001ce80013908627624200021098c1bf0341d85751a75c01df80019a8bf14b8001c500024a09b089172c0015ca27a7f80000f80010885f9688648000000000000000002978001ed91a00000008486dcd900026000000000000025f8c49d
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd7558810014fc7558810004ff735881000cfe735881000cfc735881001eef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef3258810006ec3258810064ff71588100f4fd715881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ee4358810006ed4358810006ec4358810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef3158810006ec315881001eef705881001eee705881001eed705881001eec705881001eef505881001eee505881001eed505881001eec505881001eef305881001eee305881001eed305881001eec305881001eef105881001eee105881001eed105881001eec1058810064ff768c81001cfe768c810004fd768c81001cfc768c81014e7e658c8100067d658c810146be648c810006bd648c81000ede638c810006dd638c810066ee628c810006ed628c810004ff764c81001cfe764c810004fd764c81001cfc764c81013e7e654c8100067d654c810005bf744c81016dbc744c810136be644c810006bd644c81000ede634c810006dd634c810006ee624c810006ed624c810005f7714c810005f4714c81005cff768c41001cfe768c41000cfd768c41001cfc768c41012e7e658c4100067d658c410126be648c410006bd648c41000ede638c410006dd638c410006ee628c410006ed628c41001dfa708c410005f9708c41005cff764c41011e7e654c4100067d654c410116be644c410006bd644c41000ede634c410006dd634c410006ee624c410006ed624c410004fd76c84100ee7e65c84100067d65c841010ede63c8410006dd63c8410066ee62c8410006ed62c8410004ff7688410004fd768841002d7e75884100057d75884100e67e65884100067d6588410106de6388410006dd6388410006ee6288410006ed628841001dfa7088410005f97088410004ff76484100fe7e65484100067d6548410005df7348410025dc73484100f6de6348410006dd6348410006ee6248410006ed6248410064ff760841001cfe7608410004fd760841001cfc76084100de7e65084100067d65084100d6de6308410006dd6308410066ee6208410006ed620841001dfa7008410005f9700841001dfb7644010006fb7644010004fb76440100077b754401016778754401001f7a654401001f796544010007db7344010007d8734401001fda634401001fd96344010007eb7244010007e8724401001fea624401001fe9624401001dfb714401001ff3714401015efa614401001ff26144010007f22144010007f12144010
  | 1 => 0x941002e7d715941002e7c71594100067f31594100067c315941001e7f705941001e7e705941001e7d705941001e7c705941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e77105941001e7e105941001e7d105941001e75105941001e7c1059410004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c100bcfe7458c100bcfc7458c1001edf7358c10006df5358c10026de5358c10006dd5358c10026dc5358c10006df4358c10026de4358c10026dc4358c10004ff7258c10064fc7258c10026df3258c10026dc3258c1000cff7158c1000cfd7158c10024fc7158c10026dc3158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006dc4258c10026df7158c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006dc4158c1001edf7058c1001ede7058c1001edd7058c1001edc7058c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ede1058c1001edd1058c1001edc1058c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c101567e6550c100067d6550c1000ede6350c10006dd6350c100279c4350c10064ff7598810014fe7598810004fd7598810064fc759881000cfe7398810004fd7398810064fc739881001eee7298810006ef5298810066ee5298810006ed5298810066ec5298810006ef3298810066ec329881001cfe709881001cfc709881001eee209881001eec2098810066ef7598810006ee7598810006ed7598810066ec7598810066ef7398810006ee7398810006ed7398810066ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ee4398810006ed4398810006ec4398810006ee7198810066ec7198810006ef5198810006ee5198810006ed5198810006ec5198810006ef3198810006ec319881001eef709881001eee709881001eed709881001eec709881001eef509881001eee509881001eed509881001eec509881001eef309881001eee309881001eed309881001eec309881001eef109881001eee109881001eed109881001eec1098810004ff7558810014fe7558810004f
  | 2 => 0x6ec5118910006ef3118910006ec3118910066ef7018910186ee7018910006ed7018910066ec7018910006ef5018910186ee5018910006ed5018910186ec5018910006ef3018910186ee3018910186ec3018910186ee1018910006ed1018910186ec1018910064ff768c910004fe768c910004fd768c910064fc768c9100067f658c91014e7c658c910006bf648c910146bc648c910006df638c91000edc638c910006ef628c910066ec628c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91013e7c654c910005bf744c91017dbc744c910006bf644c910136bc644c910006df634c91000edc634c910006ef624c910006ec624c91004cfe768c5100067f658c51012e7c658c510006bf648c510126bc648c510006df638c51000edc638c510006ef628c510006ec628c51001cfc764c5100067f654c51011e7c654c510006bf644c510116bc644c510006df634c51000edc634c510006ef624c510006ec624c510005fb704c51001df8704c51001cfe76c85100067f65c85100ee7c65c8510006df63c851010edc63c8510006ef62c8510066ec62c851001dfa70c8510005f970c8510004fe76885100457e75885100057d75885100067f65885100e67c6588510006df6388510106dc6388510006ef6288510006ec628851001cfc76485100067f65485100fe7c6548510005df734851003ddc7348510006df63485100f6dc6348510006ef6248510006ec6248510005fb704851001df87048510004fe76085100067f65085100de7c6508510006df63085100d6dc6308510006ef6208510066ec620851000cff764c11003cfd764c11000cfc764c1100067f654c1100b67c654c110006bf644c1100aebc644c110006df634c11000edc634c110006ef624c110006ec624c110005f7714c110005f4714c110004fe76c81100067f65c811007e7c65c8110006df63c81100a6dc63c8110006ef62c8110066ec62c8110005f671c8110005f571c8110064ff7648110004fd7648110004fc76481100057f75481100457c75481100067f654811008e7c6548110006df6348110086dc6348110006ef6248110006ec6248110005f77148110005f4714811001ff010481100067f65c41100367c65c4110006df63c411005edc63c4110006ef62c4110006ec62c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c41101777865c4110007db63c4110007d863c4110007eb62c4110007e862c411001dfa71c411001efb61c411001ff361c4110177f251c4110177f151c41100067f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067c325941002e7f71594100067e715
  | 3 => 0xf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e651d8910007e551d891018fe610d891018fe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d891018eef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ec31d8910006ef70d891018eee70d8910006ed70d891018eec70d8910006ef50d891018eee50d8910006ed50d891018eec50d8910006ef30d891018eee30d891018eec30d891018eee10d891018eec10d89100457e75989100057d75989100067f65989100067c659891003dde7398910005dd7398910006df6398910006dc6398910006ef6298910064ff7598910014fe75989100667e75989100147e7598910004fd75989100667d75989100047d7598910064fc759891000cfe7398910066de739891000cde7398910004fd7398910066dd7398910004dd7398910064fc7398910064fe7298910004ee7298910004fd7198910066f57198910004fd7098910066f970989100057f75589100457c75589100067f65589100067c6558910005df735891003ddc7358910006df6358910006dc6358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006df6318910006dc6318910006ed6218910064ff7518910014fe7518910004fd7518910064fc751891000cfe7318910004fd7318910064fc7318910066ee7218910006ef5218910066ee5218910006ed5218910066ec5218910006ef3218910066ec3218910104fe7118910064fc711891001cfe701891001cfc7018910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e65118910007e55118910187e61018910187e41018910066ef7518910006ee7518910006ed7518910066ec7518910066ef7318910006ee7318910006ed7318910066ec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ee4318910006ed4318910006ec4318910066ef7118910006ed7118910006ef5118910006ee5118910006ed5118910
  | 4 => 0x8d1000cfe71d8d1001cfd71d8d1000cfc71d8d1003edf31d8d1001cfe70d8d1003cfd70d8d1001cfc70d8d1003edf30d8d1003dde76d8d1000cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d10007d651d8d10007d551d8d1019fd610d8d1019fd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006dc42d8d1019edf71d8d1003ede71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df70d8d1019ede70d8d10006dd70d8d1019edc70d8d10006df50d8d1019ede50d8d10006dd50d8d1019edc50d8d10006df40d8d1019ede40d8d1019edc40d8d1019ede20d8d1019edc20d8d1019ede10d8d1019edc10d8d100057f7558d100457c7558d100067f6558d100067c6558d10005bf7458d1017dbc7458d10006bf6458d1003edc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d100bcfe7458d100bcfc7458d10006bc7458d100bcbc7458d1003cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10064fc7258d10006ec7258d10004ec7258d1004cff7158d10006f77158d1005cff7058d10006fb7058d10005de7618d1003ede7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10196df6118d10007d65118d10007d55118d10197d61018d10197d41018d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101567c6550d10006df6350d1000edc6350d1003f9c4350d100067f65d89100067c65d8910006df63d8910006dc63d8910004ff75d8910014fe75d8910004fd75d8910014fc75d891000cfe73d8910004fd73d891000cfc73d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef32d8910006ec32d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006c
  | 5 => 0x6dd634c310005f7714c310005f4714c310066ee62c8310006ed62c8310005f671c8310005f571c83100057f75483100357c7548310006ee6248310006ed6248310005f77148310005f47148310004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e100bcfe7458e100bcfc7458e1001edf7358e1004ede5358e10006dd5358e1004ede4358e10004ff7258e10064fc7258e1004edc3258e1004edf3158e1001cfc7058e1001ede3058e1001edc3058e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e1000ede6350e10006dd6350e1004f9c4350e10064ff7598a10014fe7598a10004fd7598a10064fc7598a1000cfe7398a10004fd7398a10064fc7398a1001eee7298a10066ee5298a10006ed5298a1001cfe7098a1001eee2098a1001eec2098a10004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067c7558a100147c7558a10004ff7358a1000cfe7358a1000cfc7358a1001eef7258a10006ee5258a10006ed5258a1001cfc7058a1001eee2058a1001eec2058a10064ff768ca1001cfe768ca10004fd768ca1001cfc768ca1000ede638ca10006dd638ca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca10005bf744ca101adbc744ca10005f7714ca10005f4714ca1003cfd768c61019edf638c61000edc638c61000cff764c61001cfc764c61000ede634c610006dd634c610005fb704c61001df8704c610066ee62c8610006ed62c861001dfa70c8610005f970c86100557e75886100057d758861018eef628861018eec6288610005df734861004ddc7348610006ee6248610006ed6248610005fb704861001df87048610186ef6208610066ec620861001df976c4210006f976c421001ff271c42100457e76d95100467e76d95100147e76d95100067e63d95100067c63d95101a77771d95100477471d95101a77610d95101a77410d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067c32d95101a67f71d95100467e71d95100467d71d95100467c71d95100067f31d95100067c31d95100067f70d95101a67e70d95100467d70d95101a67c70d95100067f30d95101a67e30d95101a67c30d95101a67e20d95101a67c20d95101a67e10d95100467d10d95101a67c10d951000cfe76d8d100067f65d8d100067c65d8d1003ede63d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d100bcfe74d8d10004fd74d8d100bcfc74d8d10006df53d8d1003ede53d8d10006dd53d8d1003edc53d8d10006df43d8d1003ede43d8d1003edc43d8d10064fe72d8d10004fd72d8d1003edf32d8d1003edc32d
  | 6 => 0xd708842018eee608842018fea6088420004ff7648420005df734842006ddc73484201ceee6248420066ef65084201c6ed650842018dee7108420067e67108420067e66108420006ed6108420067e56108420067ea7008420185ed7008420067e97008420186ee6008420067ea600842001dfb7648020006fb7648020004fb76480200077b75480201bf78754802001dfb724802001feb7248020066fa624802001fea6248020067ea3248020007e9324802005ede63d8f10004ff75d8f10014fe75d8f10004fd75d8f10014fc75d8f100bcfe74d8f10004fd74d8f100bcfc74d8f1005cfd73d8f1005ede53d8f10006dd53d8f1005ede43d8f10064fe72d8f10004fd72d8f1005edc32d8f10006f671d8f1005edf31d8f10006f970d8f1019ede30d8f1019edc30d8f1000cff7658f1005edc6358f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f100bcfe7458f100bcfc7458f10006df7358f10004ff7258f10064fc7258f1001cfc7158f1005edc3158f1005edf3058f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006df6350f1000edc6350f1005f9c4350f100357e75d8b100057d75d8b10004ff75d8b10014fe75d8b100067e75d8b100147e75d8b10004fd75d8b100067d75d8b100047d75d8b10014fc75d8b1000cfe73d8b10004fd73d8b1000cfc73d8b10006ee52d8b10006ed52d8b10006f671d8b10006f970d8b1018eee20d8b1018eec20d8b10004fd7698b10006ef6298b10064ff7598b10014fe7598b10004fd7598b10064fc7598b1000cfe7398b10004fd7398b10064fc7398b10005df7358b1005ddc7358b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7358b10006df7358b10004df7358b1000cfe7358b1000cfc7358b10006dc7358b1000cdc7358b10006ef7258b10006ed6218b10064ff7518b10014fe7518b10004fd7518b10064fc7518b1000cfe7318b10004fd7318b10064fc7318b10064fe7218b10066ee7218b10066ee5218b10006ed5218b10066f67118b10066f97018b10186ee2018b10066ec2018b10064ff768cb10004fe768cb10004fd768cb10064fc768cb10006df638cb1000edc638cb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10005bf744cb101b5bc744cb1001cfd768c71000ede638c710006dd638c71001dfa708c710005f9708c710024ff764c710006df634c71000edc634c710006ef62c8710066ec62c871001cfd76887100357e75887100057d7588710006ee6288710006ed628871001dfa7088710005f97088710005df734871005ddc7348710006ef6248710006ec624871001cfd7608710066ee6208710006ed620871001dfa7008710005f9700871000cff764c31000cfc764c31000ede634c310
  | 7 => 0x8520005ee76c8520006ee76c8520004ee76c85201edef75c85201eded75c85200076f65c85202076c65c8520006ec61c852001dee70c852001dec70c8520066ef60c852001cfe768852008d7e75885200057d75885200067f65885200e67c65885201fded7288520006f76188520006f4618852001dfa7088520005f9708852001cfc76485200067f65485200fe7c6548520005df7348520085dc7348520006f76148520006f46148520005fb704852001df8704852001cec76485201fdef75485201fded75485200076f65485201f76c6548520007cf7348520007cc7348520007e77148520007e76148520006ec6148520007e46148520007eb704852001dee704852001dec7048520007e87048520004fe76085200067f65085200de7c65085201edee720852000cff764c120084fd764c12000cfc764c1200067f654c1200b67c654c120006df634c12000edc634c120005ef724c120005ec724c12001fe8204c1200067f65c812007e7c65c812001dee72c812001eef62c81200077b65c81201e77865c812001dfa72c812001efb62c812001feb62c8120067ea52c81201e7e952c8120067eb21c8120007e921c8120004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c200bcfe7458c200bcfc7458c2001cff7358c2001edf7358c2006ede5358c20006dd5358c2006ede4358c2000cff7258c20064fe7258c2000cfd7258c20064fc7258c20066de3258c20066dc3258c20004ff7158c20004fc7158c2006edf3158c2001cfe7058c2001cfc7058c2001ede3058c2001edc3058c20004ff7650c2001cfe7650c20004fd7650c2001cfc7650c2000ede6350c20006dd6350c2006f9c4350c200a4ff764c820005bf744c8201ddbc744c820067cc324c820004ff7598420014fe7598420004fd7598420014fc759842000cfe7398420004fd739842000cfc739842001ef67198420006f65198420006f55198420066f72198420066f4219842001ef6109842001ef41098420004ff7558420014fe7558420004fd7558420014fc7558420004ff7358420006df7358420004df735842000cfe735842000cfc7358420006dc735842000cdc735842001ef77158420006f65158420006f55158420066f72158420066f4215842001eef205842001eed205842001ef6105842001ef41058420004ff768c42001cfe768c420004fd768c42019edf638c42000edc638c420006f6618c420006f5618c420004ff764c420004fd764c42001cfc764c42000ede634c420006dd634c420005ef724c420065ec724c420006f6614c420006f5614c420004fd76884200757e75884200057d758842018ded7688420006ed7688420004ed76884201d76e75884200076d758842018eef65884201d6ed6588420065ee7188420006ed618842018de
  | 8 => 0x67c73d95200067e43d95200067c43d95202167f72d952008e7e72d952008e7d72d952008e7c72d95200067f32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067c31d95200067f70d95202167e70d952008e7d70d95202167c70d95200067f30d95202167e30d95202167c30d95202167e20d952008e7d20d95202167c20d95202167e10d95202167c10d952000cfe76d8d200067f65d8d200067c65d8d20086de63d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d200bcfe74d8d20004fd74d8d200bcfc74d8d20006df43d8d20086dc43d8d20064fe72d8d2001cfd72d8d20064fc72d8d20086df32d8d20004fe71d8d20004fd71d8d20086dc31d8d20084fd70d8d20086df30d8d200057f7558d2008d7c7558d200067f6558d200067c6558d20005bf7458d2020dbc7458d20086dc6358d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d200bcfe7458d200bcfc7458d20006bc7458d200bcbc7458d20084ff7358d20006df7358d20086de5358d20006dd5358d20086de4358d20094ff7258d20006ef7258d20086dc3258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200a4ff7058d20006fb7058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201567c6550d2000ede6350d20006dd6350d200879c4350d20005ef7250d20005ec7250d20094fe768c9200067f658c92014e7c658c92000ede638c920006dd638c92001cfc764c9200067f654c92013e7c654c920005bf744c92020dbc744c920006df634c92000edc634c920005fb704c92001df8704c9200067f65d85200067c65d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852000cfe73d8520004fd73d852000cfc73d8520006f731d8520006f431d852008d7e75985200057d75985200067f65985200067c6598520006f761985200057f755852008d7c75585200067f65585200067c6558520005df7358520085dc73585200067f65185200067c6518520006f56118520004ff7518520014fe7518520004fd7518520014fc751852000cfe7318520004fd731852000cfc7318520006ee5218520006ed5218520006f73118520006f4311852001cfe701852001cfc7018520186ee2018520186ec2018520004fe768c520004fd768c520004fc768c5200067f658c52012e7c658c520006df638c52000edc638c520005ee728c520005ed728c520004ff764c520004fe764c520004fc764c5200067f654c52011e7c654c520004fe76c85200067f65c85200ee7c65c
  | 9 => 0xe7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e20006df7258e20006dd7258e20096dc7258e20006df5258e20006de5258e20006dd5258e20006dc5258e20006df4258e20006dc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006de5158e20006dd5158e20006dc5158e20006df4158e20006dc4158e2001edf7058e2001ede7058e2001edd7058e2001edc7058e2001edf5058e2001ede5058e2001edd5058e2001edc5058e2001edf4058e2001ede4058e2001edd4058e2001edc4058e2001edf2058e2001ede2058e2001edd2058e2001edc2058e2001edf1058e2001ede1058e2001edd1058e2001edc1058e20004ff7650e2001cfe7650e20004fd7650e2001cfc7650e2000ede6350e20006dd6350e200979c4350e20084fd768ca20146be648ca20006bd648ca2000ede638ca20006dd638ca2000cff764ca2001cfc764ca20005bf744ca20235bc744ca20136be644ca20006bd644ca2000ede634ca20006dd634ca20097cc324ca20005fb704ca2001df8704ca20004ff7598620014fe7598620004fd7598620014fc759862000cfe7398620004fd739862000cfc739862001ef67198620006f65198620006f5519862001ef6109862001ef41098620004ff7558620014fe7558620004fd7558620014fc7558620004ff735862000cfe735862000cfc735862001ef77158620006f65158620006f5515862001eef205862001eed205862001ef6105862001ef41058620004ff768c62001cfe768c620004fd768c620126be648c620006bd648c62000ede638c620006dd638c620004ff764c620004fd764c62001cfc764c620116be644c620006bd644c62000ede634c620006dd634c620005ef724c620005ec724c62010ede63c8620006dd63c862009d7e75886200057d7588620106de6388620006dd6388620006f66188620006f5618862001dfa7088620005f9708862022f6e75886200076d758862018eef658862022eed658862018fce638862018fcd638862018fe66188620006ed618862018fe5618862018fea708862018ded7088620007e97088620005df7348620095dc73486200f6de6348620006dd6348620006f66148620006f56148620005fb704862001df870486200d6de6308620006dd6308620185ed7608620006ed7608620186ef6508620226ed6508620187ce6308620187cd6308620007e67108620006ed6108620185ed700862001df976c8220066f976c822001fda63c822001fd963c822001fea72c8220067ea52c822021fe952c822008d7e76d952008e7e76d95200147e76d95200067e63d95200067c63d95202176f72d952008f6c72d95202176e20d95202176c20d95200067f73d95200067e73d95200067d73d9520
  | 10 => 0x8530006ef6288530006ec6288530004ff7648530004fe7648530004fc7648530005bf74485300adbc7448530005df734853000ddc7348530004fe7608530004fd7608530064fc760853000dde7308530005dd7308530006ef6208530066ec6208530006f76108530006f4610853001dfa7008530005f9700853000cfe7650130254fd765013000cfc7650130005df735013000ddc73501300079d4350130064ff75d8f20014fe75d8f20004fd75d8f20064fc75d8f200bcfe74d8f20004fd74d8f20064fc74d8f200a4fd73d8f20066ee72d8f20004fe71d8f20004fd71d8f20066f970d8f2000cff7658f20066dc6358f20004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f200bcfe7458f200bcfc7458f20066df7358f200a6de5358f20006dd5358f200a6de4358f2001cfc7258f20066de3258f20066dc3258f20004ff7158f20004fc7158f200a6dc3158f200a6df3058f20004ff7650f20064fe7650f20004fd7650f20064fc7650f2000ede6350f20006dd6350f200a79c4350f20005ef7250f20065ec7250f2006cff764cb20005bf744cb2024dbc744cb2007d7e75987200057d7598720066f76198720004ff7598720014fe75987200067e75987200147e7598720004fd75987200067d75987200047d7598720014fc759872000cfe7398720004fd739872000cfc739872001cfe7298720006ee5298720006ed5298720066f72198720066f4219872018eee209872018eec2098720066f46158720004ff7558720014fe7558720004fd7558720014fc7558720004ff735872000cfe735872000cfc735872001cfc7258720066f72158720066f42158720004ff768c720064fe768c720004fd768c72000ede638c720006dd638c720065ee728c720005ed728c720004ff764c720004fd764c720064fc764c72001ced76c8720065ef75c8720245ed75c8720006ee61c8720067e661c8720067e561c872001dee70c8720067ea70c8720067e970c872001dec70c872007d7e75887200057d7588720005df73487200a5dc7348720005ef7648720006ef764872023def754872023ded7548720007cf7348720007cc7348720067e77148720006ee614872001dee704872001dec704872000cff764c320064fc764c32000ede634c320006dd634c320005ef724c320065ec724c320004ff7558e20014fe7558e20004fd7558e20014fc7558e20004ff7458e200bcfe7458e200bcfc7458e2001edf7358e20006df5358e20096de5358e20006dd5358e20096dc5358e20006df4358e20096de4358e20096dc4358e20096df3258e20004ff7158e20004fc7158e20096df3158e20096dc3158e2001cfc7058e2001ede3058e2001edc3058e20006df7558e20006de7558e20006dd7558e20006dc7558e20006df7458e20006d
  | 11 => 0xaf9c4150d30007db7050d3001dde7050d3001ddc7050d30007d87050d3000edf6050d3000fdb6050d300af9f4050d30004ff75d8930014fe75d8930004fd75d8930014fc75d89300bcfe74d8930004fd74d89300bcfc74d893001cfd73d8930096de53d8930006dd53d8930096de43d8930006dd43d8930096ee32d8930096ed32d8930096dc32d8930004fe71d8930004fd71d8930006ef6298930085f970989300057f75589300b57c7558930005bf74589300adbc7458930005f77158930005f471589300a5fb7058930006ed6218930064ff7518930014fe7518930004fd7518930064fc75189300bcfe7418930004fd7418930064fc741893001cfd7318930066ee321893006eed3218930004fe7118930004fd7118930004fe7690930004fd7690930064fc7690930006bf64909300bebc649093000ddc739093026f9e4390930004ff7650930004fe7650930004fc7650930005df735093000ddc73509300079d435093001cde768c930265df758c930265dd758c930005df748c930005dd748c930146de648c930146dc648c93000dde728c93000fce728c930006df628c930007cf628c930007cc628c930005dd718c93001dde708c930007da708c930007d9708c93001ddc708c93000edf608c93000fdb608c930004ff75d8530014fe75d8530004fd75d8530014fc75d85300bcfe74d8530004fd74d85300bcfc74d853001cfd73d8530064fe72d8530004fd72d853004ef631d853004ef531d8530006f7619853003df970985300057f75585300b57c7558530005bf74585300adbc7458530005ef7258530005ec725853005dfb70585300b57e75185300057d7518530006f56118530004ff7518530014fe75185300067e75185300147e7518530004fd75185300067d75185300047d7518530014fc75185300bcfe7418530004fd74185300bcfc741853001cfd7318530026de5318530006dd5318530026de4318530006dd4318530064fe7218530004fd7218530006de3218530026dc3218530026df3118530026f63118530026f53118530196de3018530196dc3018530004fe7690530004fd7690530004fc7690530006bf64905300bebc649053000dde7390530005dd73905300079d4390530004ff7650530004fe7650530004fc765053000dde735053001cdc764c53025ddf754c53025ddd754c530005df744c530005dd744c530005dc724c53000ddf714c53000fd7714c530007d7614c530006dc614c530007d4614c530007db704c53001dde704c53001ddc704c530007d8704c53000edf604c53000fdb604c530004fe76c8530004fd76c8530064fc76c8530005df73c853000ddc73c8530006f761c8530006f461c8530004fe7688530004fd7688530004fc76885300b57e75885300057d758853000dde7388530005dd738
  | 12 => 0xd7558a30014fc7558a30004ff7458a300bcfe7458a300bcfc7458a3001eef7258a30006ee5258a30006ed5258a30006ef4258a30006ec4258a30086ee3258a30086ed3258a30004ff7158a30004fc7158a3001cfc7058a3001eee2058a3001eec2058a30064ff7690a3001cfe7690a30004fd7690a300bebe6490a30006bd6490a30004ff7650a30004fd7650a3001cfc7650a30005df7350a3000ddc7350a30004ff7598630014fe7598630004fd7598630014fc75986300bcfe7498630004fd74986300bcfc7498630064fe7298630004fd729863001ef67198630006f65198630006f5519863005ef6319863005ef5319863001cfe709863001ef6109863001ef41098630004ff7558630014fe7558630004fd7558630014fc7558630004ff7458630006bf7458630004bf74586300bcfe74586300bcfc7458630006bc74586300bcbc7458630004ff7258630064fc725863001ef77158630006f65158630006f5515863003ef6315863003ef5315863003edc315863001cfc705863001edf305863001edd305863001ef6105863001ef41058630004ff769063001cfe7690630004fd76906300bebc6490630004ff7650630004fd765063001cfc76506300bebe6450630006bd6450630005df735063000ddc735063019edf658c63028edd658c63019edf648c630006dd648c630006de628c63000dde718c63000fd6718c63019fd6618c630006dd618c63019fd5618c63019fda708c63019ddd708c630007d9708c63000ede608c63000fda608c630064ff76c863001cfe76c8630004fd76c863000dde73c8630005dd73c8630066ee62c8630006ed62c8630004ff768863001cfe7688630004fd76886300cd7e75886300057d7588630004ff7648630004fd764863001cfc7648630005bf74486300c5bc7448630005df734863000ddc7348630006ee6248630006ed6248630064ff760863001cfe7608630004fd760863001dfa7008630005f970086300bcfe76d91300aebe64d9130004ff75d9130014fe75d9130004fd75d9130014fc75d91300aebe54d9130006bd54d913001cff73d913000cfe73d913001cfd73d913000cfc73d9130286bf43d9130286bd43d9130064fe72d9130004fd72d91300aebc42d9130004fe71d9130004fd71d91300aebc41d913000cfd70d91300aebf40d91300aebc645913027dfb7059130004ff7559130014fe7559130004fd7559130014fc7559130254ff7359130006df7359130004ff7259130064fc7259130004ff7159130004fc715913027cff7059130006fb705913001ddc7650d300bedc7650d3001cdc7650d30275df7550d30275dd7550d3000ddf7450d3000f9f7450d300079f6450d300bede6450d300bedc6450d300af9c6450d300be9c6450d30005dc7250d300af9f4250d30005df7150d30
  | 13 => 0x812101efa6018121006f96018121064ff75d8c21014fe75d8c21004fd75d8c21064fc75d8c210bcfe74d8c21004fd74d8c21064fc74d8c210d4fd73d8c21064fe72d8c21066ee72d8c21104fe71d8c21066f671d8c2101cfe70d8c21004fd70d8c2100cff7658c21066dc6358c21004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c210bcfe7458c210bcfc7458c21066df7358c210d6de5358c21006dd5358c210d6de4358c21064fe7258c21064fc7258c21066de3258c21066dc3258c210d4fc7158c210d6dc3158c21004ff7058c2101cfc7058c210d6df3058c21004ff7650c21064fe7650c21004fd7650c21064fc7650c2100ede6350c21006dd6350c210d79c4350c21005ef7250c21065ec7250c2110cff764c821005bf744c8212c5bc744c821104ff768c421064fe768c42100cfd768c421064fc768c42100ede638c421006dd638c421065ee728c421005ed728c421104ff764c421065ef75c84212bded75c8421185ee70c84210dd7e75884210057d75884212a5ed72884212b6ee62884212af767588421007757588421065f57288421066f66288421067e66288421067e652884212afe55288421004ff7648421005df73484210d5dc7348421005ef7648421006ef7648421004ef76484212a5ef75484212a5ed7548421007cf7348421007cc7348421065ef714842129eee6148421297e65148421297e55148421185ec7048421065f77648421006f77648421004f77648421007d77348421007d47348421065f77248421007e77248421066f66248421067e66248421067e65248421297e55248421066fb609802101ef860980210057f75580210dd7c7558021066f86058021004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff735802100cfe735802100cfc7358021006ee5258021006ed5258021006ef2158021006ed2158021006fa5058021006f95058021066fb2058021066f82058021004ff7559230014fe7559230004fd7559230014fc755923001ebf74592300c6be5459230006bd5459230256bf4359230256bd4359230004ff7259230064fc72592300c6bc4259230004ff7159230004fc71592300c6bf4159230256dc315923001cfe705923001cfc705923001ebe405923001ebc405923001edf305923001edd3059230064ff7598a30014fe7598a30004fd7598a30064fc7598a300bcfe7498a30004fd7498a30064fc7498a3001eee7298a30066ee5298a30006ed5298a30006ef4298a30066ec4298a30066ee3298a300a6ed3298a30004fe7198a30004fd7198a300a6dc3198a3001cfe7098a3001cfc7098a3001edf3098a3001edd3098a3001eee2098a3001eec2098a30004ff7558a30014fe7558a30004f
  | 14 => 0x4fd70d8d210f6df30d8d210f6dc30d8d210f5de76d8d2100cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dc64d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21006df72d8d210f6de72d8d21006dd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df42d8d21006dc42d8d21006df71d8d210f6de71d8d21006dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006dc41d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006dc40d8d21005bf7458d212d5bc7458d21006bf6458d210f6dc6358d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21006bf7458d21004bf7458d210bcfe7458d210bcfc7458d21006bc7458d210bcbc7458d210f4ff7358d21006df7358d21104ff7258d21006ef7258d2110cff7158d21006f77158d21004ff7058d2101cfc7058d21005de7618d210f6de7618d21004de7618d210f75e7518d210f75d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d2100edc6350d210f79c4350d21104fe768c921006bf648c921146bc648c921006df638c92100edc638c92100cfc764c921005bf744c9212d5bc744c921006bf644c921136bc644c921006df634c92100edc634c9210f7cc324c921005f7714c921005f4714c92110cfe768c521006bf648c521126bc648c521006df638c52100edc638c52100cff764c5210f4fd764c52100cfc764c521006bf644c521116bc644c521006df634c52100edc634c521005ef724c521005ec724c521006df63c852110edc63c8521007d763c8521007d463c85210fd7e75885210057d7588521006df6388521106dc63885212cf6e75885210076d75885212ceef65885212ceed6588521007cf6388521007cc6388521007e76188521005ed7088521006df63d8121006dc63d8121004ff75d8121014fe75d8121004fd75d8121014fc75d812100cfe73d8121004fd73d812100cfc73d8121006fb50d8121006f850d81210f5de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581210fd7c7558121005df73581210f5dc7358121006df6358121006dc6358121006df6318121006dc631812118eef621
  | 15 => 0xc43596210e67f72596210e67e72596210067d72596210e67c72596210067f32596210067c32596210e67f71596210067e71596210e67d71596210e67c71596210067f31596210067c31596210e67e21596210067f70596210067e70596210067d70596210067c70596210067f30596210067c30596210e57e75d8e210057d75d8e210067e65d8e210067d65d8e212e5be74d8e21005bd74d8e21106de63d8e21004ff75d8e21014fe75d8e210067e75d8e210147e75d8e21004fd75d8e210067d75d8e210047d75d8e21014fc75d8e210bcfe74d8e21006be74d8e210bcbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e210bcfc74d8e21104fd73d8e21106de53d8e21006dd53d8e21106de43d8e21006ed72d8e21106dc32d8e21006f671d8e2101cfe70d8e21004fd70d8e2100cff7658e210067e6558e210067d6558e21106dc6358e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e210bcfe7458e210bcfc7458e21006df7358e21006df4358e21106dc4358e21106df3258e21106dc3158e21004ff7058e2101cfc7058e21106df3058e21004ff7650e21004fe7650e21004fd7650e21004fc7650e211567e6550e210067d6550e21006df6350e2100edc6350e211079c4350e21005ef7250e21005ec7250e210f4fd768ca2114e7e658ca210067d658ca21006df638ca2100edc638ca2100cff764ca2113e7e654ca210067d654ca21005bf744ca212e5bc744ca2100ede634ca21006dd634ca21005f7714ca21005f4714ca2100cfe768c62100cfd768c62112e7e658c6210067d658c62100ede638c621006dd638c621005ee728c621005ed728c6210d4ff764c62111e7e654c6210067d654c6210ee7e65c86210067d65c8621005ed76c8621006ed76c86212b5ef75c86212b5ed75c86212df6e65c86210076d65c86212dfe651c86212dfe551c862118dee70c8621005f576c8621066f576c86212df7665c86210077565c8621067e652c86212dfe552c86210e57e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067e65582210067d6558221004ff7558221014fe7558221004fd7558221014fc7558221004ff735822100cfe735822100cfc7358221006ee5258221006ed5258221006ef21582210e57e75182210057d75182210067e65182210067d6518221105de7318221005dd731822101efa6018221006f9601822100cfe76d8d210f6de63d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d210bcfe74d8d21004fd74d8d210bcfc74d8d21006df53d8d210f6de53d8d21006dd53d8d210f6dc53d8d21006df43d8d210f6de43d8d210f6dc43d8d210f4fd72d8d210f6df32d8d210f4fd71d8d210f6df31d8d2101cfe70d8d21
  | 16 => 0x91312fedc3159131004ff705913101cfc70591312fedf3059131004ff75d8931014fe75d8931004fd75d8931014fc75d89310bcfe74d8931004fd74d89310bcfc74d8931006ee52d8931006ed52d8931006ef42d8931006ec42d8931106ee32d8931106ed32d893101cfe70d8931004fd70d8931006ef62989310f5f57198931005bf7458931115bc745893110df77158931006ed6218931064ff7518931014fe7518931004fd7518931064fc75189310bcfe7418931004fd7418931064fc7418931066ee5218931006ed5218931006ef4218931066ec4218931066ee32189310d6ed32189310d6dc311893101cfe7018931004fd70189310d6df3018931004fe7690931004fd7690931064fc7690931006bf64909310bebc6490931004ff7650931004fe7650931004fc7650931005df735093100ddc7350931304fe76905310bebe649053100cfe76505312fcfd765053100cfc7650531005df735053100ddc73505312f6df658c5312f6dd658c531006df648c531006dd648c531006dc628c53100dde718c53100fd6718c53100edf618c53100fd7618c531005dd708c531004ff75d8131014fe75d8131004fd75d8131014fc75d81310bcfe74d8131004fd74d81310bcfc74d8131064fe72d8131004fd72d813105efa30d8131006fb60981310057f755813111d7c7558131005bf7458131115bc7458131005ef7258131005ec7258131115be7418131005bd741813119edf631813101efa6018131006f96018131064ff75d8f21014fe75d8f21004fd75d8f21064fc75d8f210bcfe74d8f21004fd74d8f21064fc74d8f2110cfd73d8f21066ee72d8f21066f571d8f2110edc31d8f2101cfe70d8f21004fd70d8f2110edf30d8f2100cff7658f21066dc6358f21004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f210bcfe7458f210bcfc7458f21066df7358f2110ede5358f21006dd5358f2110ede4358f21066de3258f21066dc3258f2110edf3158f21004ff7058f2101cfc7058f2110edc3058f21004ff7650f21064fe7650f21004fd7650f21064fc7650f2100ede6350f21006dd6350f2110f9c4350f210d4ff764cb21005bf744cb212edbc744cb21067cc324cb210f4fd768c721006df638c72100edc638c72100cff764c721064fc764c72100ede634c721006dd634c721005ef724c721065ec724c72110dde7398321005dd7398321066fb609832101ef86098321066f86058321004ff7558321014fe7558321004fd7558321014fc7558321004ff735832100cfe735832100cfc7358321066fb2058321066f820583210e57f76596210e67f76596210147f76596210067e63596210067c63596210e76e72596210076d72596210067f73596210067e73596210067d73596210067c73596210067e43596210067
  | 17 => 0x126bc425923100cfc7159231126bc4159231004ff705923101cfc7059231126bf4059231125df7650e310bedf7650e310bcdf7650e31325df7550e31325dd7550e3100ddf7450e3100f9f7450e310bede6450e311279e6450e310be9e6450e310079d6450e310bedc6450e31005dc7250e311279f4250e31005df7150e31007d77150e31007d47150e3100ede6150e3100fd66150e311279c4150e3119ddc7050e311279f4050e3112d7e75d8a310057d75d8a31125be74d8a31005bd74d8a310d5f671d8a31006ef6298a31064ff7598a31014fe7598a31004fd7598a31064fc7598a310bcfe7498a31004fd7498a31064fc7498a31066ee3298a3110eed3298a3101cfe7098a31004fd7098a31004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a310bcfe7458a310bcfc7458a310f6de5358a31006dd5358a310f6de4358a31006dd4358a310f6ee3258a310f6ed3258a310f6dc3258a31004ff7058a3101cfc7058a31006ed6218a31105f67118a31064ff7690a31004fe7690a31004fd7690a310bebe6490a31006bd6490a3100ddc7390a3126f9e4390a31004ff7650a31004fd7650a31004fc7650a31005df7350a3100ddc7350a310079d4350a3131ddf758ca3131ddd758ca31005df748ca31005dd748ca31146de648ca31146dc648ca3100dde728ca3100fce728ca31007ce628ca31006dd628ca31007cd628ca31007d6718ca31005dd718ca31007d5718ca3100ede618ca3100fd6618ca3119dde708ca310bcfe769063100cfd769063100dde7390631005dd73906310079d4390631006fb60982310057f755823112d7c7558231004ff75582310067f75582310047f7558231014fe7558231004fd7558231014fc75582310067c75582310147c7558231004ff74582310bcfe74582310bcfc745823103ede5358231006dd535823103ede4358231006dd4358231004ff7258231064fc7258231006de325823103edc325823103edf315823103efa305823119edc305823112d7e75182310057d7518231125be7418231005bd7418231005ee7218231005ed721823101efa6018231006f960182310bcfe76d9131116be64d9131004ff75d9131014fe75d9131004fd75d9131014fc75d9131116be54d9131006bd54d9131314ff73d9131314fd73d9131316bf43d9131316bd43d9131064fe72d9131004fd72d9131116bc42d913100cfd71d9131116bf41d9131316dc31d913101cfe70d9131004fd70d9131116bc40d9131316df30d9131116bc6459131005ef7259131005ec725913130df77159131004ff7559131014fe7559131004fd7559131014fc75591312fcff7359131006df7359131004ff7259131006ef7259131004ef7259131064fc7259131006ec7259131004ec725913130cff7159131006f7715
  | 18 => 0xf7159132004fc7159132004ff705913201cfc705913226dbe7619132136be761913226cbe7619132006bf6519132006be6519132006bd6519132006bc651913233f9e73191321379d731913233ebf631913233f9e53191320079d531913233ebf621913233faf321913233f9c321913233fac3219132135dc7650d320bedc7650d320bcdc7650d32345df7550d32345dd7550d3200ddf7450d3200f9f7450d320079f6450d320bede6450d320bedc6450d321379c6450d320be9c6450d32007cf7250d32065dc7250d32007cc7250d32005cc7250d3200edf6250d3200fcf6250d321379f4250d321379c4150d321379f4050d3233cfe769093226ebf64909320bebc6490932065dc739093226f9e439093200cfe7650932334fd765093200cfc7650932005df735093200ddc73509320079d4350932065df758c93232ddd758c932065df748c932005dd748c9320079f648c932146de648c932146dc648c9320079c648c9321469c648c932065de728c932067ce728c932066df628c93200fcf628c932006bf64d8532006bc64d8532004ff75d8532014fe75d8532004fd75d8532014fc75d85320bcfe74d8532004fd74d85320bcfc74d8532006f651d8532006f551d853210ef631d853201cfe70d8532004fd70d853213d7e75985320057d7598532135be7498532005bd7498532006bf6498532006bc6498532006f76198532005bf7458532135bc7458532006bf6458532006bc6458532006bf6418532006bc6418532006f56118532004ff7518532014fe7518532004fd7518532014fc75185320bcfe7418532004fd74185320bcfc74185320d6de5318532006dd53185320d6de4318532006dd4318532006de32185320d6dc3218532006f65118532006f551185320d6f5311853201cfe7018532004fd7018532006bf64d8132006bc64d8132004ff75d8132014fe75d8132004fd75d8132014fc75d81320bcfe74d8132004fd74d81320bcfc74d81320a6de53d8132006dd53d81320a6de43d8132006dd43d8132006de32d81320a6dc32d8132004fe71d8132004fd71d81320a6fa30d8132135be7498132005bd7498132006bf6498132006bc6498132006fb60981320057f755813213d7c7558132005bf7458132135bc7458132006bf6458132006bc6458132005f77158132005f47158132006bf6418132006bc641813201efa6018132006f96018132126be64d9231305f671d9231004ff75d9231014fe75d9231004fd75d9231014fc75d9231064fe72d9231004fd72d9231304fe71d9231006f671d923101cfe70d9231004fd70d92310bcff7659231126bc6459231004ff7559231014fe7559231004fd7559231014fc7559231006bf7459231126be5459231006bd54592312febf43592312febd4359231004ff7259231064fc7259231
  | 19 => 0x9232064fe7259232064fc7259232066be4259232066bc4259232336df3259232004ff7159232004fc7159232336dc3159232004ff705923201cfc7059232336df305923214d7e75986320057d7598632066f76198632004ff7598632014fe75986320067e75986320147e7598632004fd75986320067d75986320047d7598632014fc75986320bcfe7498632004fd74986320bcfc7498632064fe7298632106f53198632066f72198632066f4219863201cfe7098632004fd7098632005bf7458632145bc7458632066f46158632004ff7558632014fe7558632004fd7558632014fc7558632004ff7458632006bf7458632004bf74586320bcfe74586320bcfc7458632006bc74586320bcbc7458632064fc72586320f6f631586320f6dc3158632066f72158632066f42158632004ff705863201cfc70586320f6df3058632145be7498232005bd7498232066fb609823201ef860982320057f755823214d7c7558232066f86058232004ff75582320067f75582320047f7558232014fe7558232004fd7558232014fc75582320067c75582320147c7558232004ff74582320bcfe74582320bcfc7458232064fc7258232004ff7158232004fc7158232086fa3058232066fb2058232066f820582320bcfe76d9132136be64d9132004ff75d9132014fe75d9132004fd75d9132014fc75d9132006bf54d9132136be54d9132006bd54d9132136bc54d9132064ff73d913226cfd73d913226ebf43d913226ebd43d913200cfd72d9132136bf42d9132004fe71d9132004fd71d9132136bf41d9132136bc41d913201cfe70d9132004fd70d9132136bf40d9132136bc40d913233dbe76d91320bcbe76d9132006bf65d9132006be65d9132006bd65d9132006bc65d91320079f73d913226f9c73d913226f9e53d91320079d53d913226faf32d913226f9c32d913226fac32d9132006bf75d9132006be75d9132006bd75d9132006bc75d913226ebf73d913226ebe73d913226ebd73d913226ebc73d913226ebf53d913226ebe53d913226ebd53d913226ebc53d913226ebf72d9132136be72d913226ebd72d9132006bf52d9132006be52d9132006bd52d9132006bc52d913226ebf32d913226ebe32d913226ebc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d913226ebf31d913226ebe31d913226ebd31d913226ebc31d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d913226ebf30d913226ebe30d913226ebd30d913226ebc30d9132136bc645913234def7259132004ff7559132014fe7559132004fd7559132014fc7559132334ff7359132006df735913234cff7259132006ef7259132004f
  | 20 => 0x12025000802c0000020030088012005012800c0000000000000000007005000000000300000e00220000000000002001001800c0000000008054016004003003800000600180340000010080018000011000000000000100a0010002000000002800a01a001800400800400a002c024007001000400a0010010084004000005004c0000000000018018005001007c00200000080000220000010034000003000001c00200300880b4000037001000402000000080180420000018000006006001000400401334f9c43d8943004ff75d8943014fe75d8943004fd75d8943014fc75d89430bcfd73d8943006ef52d8943006ec52d894334eee32d8943004fe71d8943004fd71d894301cfe70d8943004fd70d894326f9c4398943006ef62989433379c43589431557e75189430057d751894333f9c4318943006ed6218943064ff7518943014fe75189430667e75189430147e7518943004fd75189430667d75189430047d7518943064fc75189430bcfd7318943066dd731894333ebe431894333edc431894333e9c4318943006ef5218943066ec5218943066df3218943066ee321894333eed3218943004fe7118943004fd711894333edc311894301cfe7018943004fd701894333edf301894330f9c43d8543004ff75d8543014fe75d8543004fd75d8543014fc75d85430bcfd73d854335edd73d8543064fe72d8543004fd72d854330ef631d854330edc31d854301cfe70d8543004fd70d854330edf30d85433179c4398543006f761985432ff9c4358543005ef7258543005ec72585431557e75185430057d75185433079c4318543006f56118543004ff7518543014fe75185430067e75185430147e7518543004fd75185430067d75185430047d7518543014fc75185430bcfd7318543064fe7218543004fd7218543306f5311854301cfe7018543004fd701854301cfe76d81431557e75d81430057d75d814327f9c43d8143004ff75d8143014fe75d81430067e75d81430147e75d8143004fd75d81430067d75d81430047d75d8143014fc75d81430bcfd73d8143064fe72d8143004fd72d8143004fe71d8143004fd71d814327efa30d81432879c4398143005ee7298143005ed7298143006fb60981432579c43581433579c431814301efa6018143006f96018143064ff75d9232014fe75d9232004fd75d9232064fc75d923226ebe43d923226edc43d923226e9c43d9232064fe72d9232066ee72d9232066df32d9232004fe71d9232004fd71d923226edc31d923201cfe70d9232004fd70d923226edf30d92320bcff7659232066bc645923200ddc73592321479f4359232004ff7559232014fe7559232004fd7559232014fc7559232066bf7459232146be5459232006bd5459232336bf4359232146df4359232336bd4359232336dc435
  | 21 => 0x6000000a013003801800801400100000020080000004004023001802c00a00000080000000000010038022012001800800600000700200380050008020000000002006c00000900500540000050008000000026006001401a00000000b800e00f002005c00000200280000020040038024036008002000c00a0000010000004010003800000e00f0008004002000006806804c00a006000c00200800080040060000000000010010000001401200a001006001c00100000000200030048000002000001007c0060090008014000015004003800c00100d0000018001002000001400100080700060000000010006006003001000200300280040b600b00780200000000008000002000005801000a001002000000000900000280080000030000002017004801400800000200000180100000034000000001800000c0070000000008006000000c01e0000060038008003000800000c0020000024000000005800800400600e803400c006000001803e001001003400c00f002000c000000005809400600300200040040020038000022013000007401a00800780040ce002002001803a00b0018000006003001002c004002002802401a00f0000038002000002000400000d00000080020190110020002000000000c004001000000800a007001003000a003000000002000b00c80000040040008000002002000000000000600200300000040008024002000001800401e0000018000000000000801401400300000800160030010000016001000000400200e00c800800200300b800001600d0038000004000000801800a000000001000400000000140240130088000008000000000c060003005802c00e00d00100500000070040014002000002800800e002000004400c0000098010008004006802000001e000801c0020000010000002001004013400e00100980c800000f000000001200000180000080030060030000000002800c000001001000401a006004000801c000002000400e00d000800006c00d000000000602f001805800c003000000000c000000000002400900b000000400200000300480050000000006001003800801201600300600020010038010000000005800c00c0020000004002004000000000000f000001002201b00180080000010230008006008004001800000e001001401200f0018024008000000000800000100280a4006004002004404c0000000058006002003800400200400100140000390090004004013001000c01600400400100060070028004000003001800400c02a00a00040000120078014000003000800001a00b0000028002006000000400a00400080dc004002000000400400500280040120000080024000003007000401000a0030008006001004800800c009003802c00a00e009009c
  | 22 => 0x80000030000000014003000000000a00500d804c006003003800001a003009800400e00d001000001600f00100040000050000008002001002800000800d000005c01e005000000000e0000010044004005003003000e00600400880220020420000000007019800801e00100000000060050020004010000001803c00000a002804c004000006000c0000050018004022015002000c0060000098010004000001001c000002005002400800300c005c000002000002403a004000000c010004000000400c000003002800000200680000020050000008002000000800401201b02f000801401100a8008000007002000c000006000800c008000001000c014008001000400003f00d801000000600300040000050000008000001000000400200d000004c01a001000002400e01400080180000030010004000005001000000000000400080000000008000002010001802c00001202280080060020018004004016001002c00402d001800400000a007000c006017000801c000010002801400400000380500000030008124002003002000001c000003000000e007000003000a001000003000a0030020000000007008801403a00b00c000001a01d000800c00000600b0070006017000800400c012023000000a00300100280100010068044004006002800000a002002800000e00100a0048000001000000402800d0008018024000001800c00800000b8010000029001000801000300280080000000000004000000002800c0000100018000008000007003c002012010002801800500c005c006004000000000000000300080120000008090002000000000c000014000001c0480000010004002007007000c01001c00d800c004002000000800800b000800402c001003001400e015000001401000000a801800000700500600020010008030000000009802000800000700000160140038014014003001802800e014008001800600700100f0000008003005800a002000000400001a0010048000002006802c088002001008c00002a002000001c00200380000120010048000000005000004c00600100000000000150048008000005000000400000200000000000010008030000016000800001a00800100000060010000004030002000000800200e00000100000000090004008001004000800a0010098008014013005801401c0010018000012000002800000001a0008000000000001006c0040000008070000009009004400200700900200220050018000002005000800004000d0008004006013001800001801d008000001000000780140020250038014012003001000400000000380000020010080078000008000800402200000080040060070000000012000003000002600d000003000200000080140040000018000012000
  | 23 => 0x60000001bad50868d3c391600000005ec8568000855000000097ecb3e3000000002d1000000000000000012dfb58c2263832fc0000005b60001b530000000000000ca4800297400019600009de3accff000131497d5452698000830dce63d81b9970000000000000000000000000003e5000000000029162a8b661bfaa02b7000000000017306b00000005fcb5300000005fb0186000cac644690c0000000001dbc7c408e000123bb10133000279c07a143384802544c12249aadc0594236800254c1707a340123886ee09fca433753b40000930000a64c3c0002b5d2b200014b8ca00007ed00027f95d8d6d5fbefc800099dc0c97345ac256536800000006480017552ca0000a4c0000000000001d4047f77e00016095d200000000006966bb38f07e0bd8290446201147653b000061caf6d9235800000000004ab1fa000087d698800093c75500000000dfb5863d2d78daac9e0bda8140000004b1800180404380000000000000000000000000000337c00000055c800000004000033d588400000000ba0002098000a4c0003265609030636d244a60cb8fb428a0808000bfa44d3f91b4a000c63600a25d587312000054d9dab3f40619527089f30e0b31419300028b22bc16800031830245be0660001824cc295c09916acec887054e827170a50014f30f8bb809040b0cd8537dd846737002ac0e10002ec67dc36b5e8800000008f85058cd34e000698205a04d258cf604f04aa00000027554fc24b0dea7e499c30d31095e70f21f4508800047ad0708c9b2d12a2cb062899e1029d600020dcce2bf30000f8c7a456ec22a8d47116ba233808085482b5d29530e0e7342c1c1d6602bb04a28000be546f0d10c4525a58d0398000d6ad4f6e7961a86597b00009017b60003ef800052827600016ddb164e3dbc0b084f8c5e1091c0e40adde60514690b394b44418381ec90a8279a9db96cd630084b54b0797000110d8a6b7180000000006750000000000039e961bfc4fa87800016cc0006f000034d86bac17d3dadc823e817000285817d00003a80009fc0000003684000caf41f33e40000005111db800000062380013666f666b800000000065a8000000000000262c13642d0000000bfe6840002e24ae40bf0499add59ca96380c00130c9646430000000000412c678000dba130b248000a4a000096c74a0000b383913ed000277706921a93a0ff59287cc00020aac302800000000000000000000210d266000646906c000012000256345e0000000c383fe0002d79b6995b000000282000025114380091c23553e700013fa000325e5d90cc000591800000081b8001e35832000000000000069733304900003170e0178800005868c2b2c00000000027e8000a7300000017ac2f9472800194613847d13fcbd47145768bcd25205e80006f22da71723c
  | 24 => 0xbc54220b4000000045480000008b31faa5e55c051e0000c90c50000213b7486850000000c1400000063c487d84c19f90d80000001fb65e811800000000026200000000000018e562ec1e985195989e227980000000001321bba6e000056187a33eeb7722370d15ee2ed2c39b10de50000000864000b3350e266c000c1f10e26f45b4000370360600000004680000008e82b12c642a8bf10000000cda00019d096b72a000211836cc86aae800192cf7452d02c85e8000000531800000004200011c800073800000000000000002b74000caa385a214000000000152db3a2bc07f0ba40007832d224bc96800000005f8000c5423300019e60004240f0b5480000000d2400000011900000007c85011f1c092000626002c1122954209d6430aa55323b70d92a080093b5888b64ca0000fbd5c655f4fb1de04feb2e47c487600000025d25f1ab60dd1cf30908c0ad3cd3cda1a703081cdaa208123250002c440000000001a30000cb923f9138f7602a0e60000fe200060a9893284445ead09aed5a2270f50d449a3b0f329306d32877a1c260a43a241919f8b74600a7711a1eb18ec44a6992ebc4760006add5aa5c2794478293d92e7630001f3133257700020e48f600000023f42d526d43b359e00065d0cbd5942ec60b1558000000000000045c204ad4da80000c5449a56d27301d00000361a61ac92170000000d320001ea40011884d0800000038e0000000000257000000000000008a4d922c9616d470001840000c0300023202c4d020002ff90c891b23492d8f4c00000009886d3b3527897bc6fc1950f216005f09b52d80880d4a8d1507187d8ee72712318ec5290700981610a7c18e69292115029110001a40cbe5c91d9c000ff4000152942c00000000000004cc00000000015fc40e39487488023f90000f50b626d8a342d7a0000000000fd053100000015404984a50001e600000001f68000d6439043e00000000300002a6d6de0b51d9ae41580493510005daca000000000000000047a9ae08b80000002d640009894bf05874480000002dd400083a589188a5c518a00000011de0220002ca886a8e60000000000a48800292c000000458a9760000000000000000a700000000bf41042f700005590000fab4e80000000000001b3e00015b056c4d2000000000100000000032f034c5c24ae8414c5b0000001fbcfac00025e8000e7954717796283530001ce98df72c1b144180005ae00036480003bc00058d40018f80000000000000b1e15780000006e7178346803461910681516508235c1b03000000034900001224d2550800000000000031e13263e94c2264800071a00000008d6000000374cd2600021311912c1abc261a73c54d00000005d6c1ac656574920cbc0001a8193062800035180456a67ec5b59c4400000000013bf8d
  | 25 => 0x9287700003d570844735fa6e4435c381319f4800066bb9c956745601f38ca2383177f654a23596ac160a492410bea7b557410f89ecd825aea4751949d221de9ad10c8e32ce8bf4e58b13510e5c40172eb00000003040004b2c000e660004ec92880009020001a8807463f058d67ca61b5b00012c82848a46cf232cd06000164000064461160680006a400027c8000790000665a8820000005d0833b67200037bb3b80000006dd91a9b9a00000018434fa00001f4000000000000000000014b800000000000004590e80003a8087a2043e50740001d50000386d0f8e9d1a30005b3890400046231c9dc4000b3c0002fd44469250000000c77000554b0e400040a274092b1255e3453a7440007240e1c6f12de96cd3c8e9800000007454385a6a696dcf2a1736d7362f9ffd0a2417000331cff0d90295a9c4843d7900016c8c5669e5e3876400071c18c0926cec0c231a960c00004a1ab8584e4a3ec3f1aa7050abde1c78d69756afc1e7adb4b2c4c11742b10d981113a6011c000090ed409d40000001b91c14000000644b15c00000000000004b87686b60b0efce00ca47348d35c5676b560c45fec3710121a4e2a2295419ddd63a90118619e51326cd00015ad8a2465ac2b03cb5a0134ec1504f2a457d0d007800064527285156e78240da855c8930642dea56754e8363500ea9122c8b2aa822bad200000032f80003f3613800000000030400008ee063374000143ac798001fe5390bdc000052c3409e53e06a007068462588000ac82fe00000000004d6524800053445160229395509eb4a50c180009ef6100bddb6408e800000000000001a8000000973000000013a4716c280000003e42182bc184a296de719b80002812bca41da6edbf9239d2a91eb49163d5b0cc1d41471ce3132aad168baa64198992e8e08dd1248f959d800115cbb26899c89858d3f0002c1911e20f860a0d00fe9a5833a96dbaa7212d3999d8204c0d37828049e91e6a427d4c3cb570002fd0588595b6114a8dde46d61880000000001bc4000e74000149006b2e1d0b6702a998b462568b2a7a0000006db2a63b7a0fb5ce80008a81590002d500000000000decb982010000bd978c0232c2e3480009c400037660004ac0002d760007cb5fbb12d026000000334400086f3d90000bd200018d2f28000b4e0000000000d1f17e000000043d1a3935a70b00055c22a899a0005a03070000038c5d0e500002ee00028fc000a7851280014d0c1d671815e954ca9344993891a799526800073e89a48d25ee0000003ee80015d4b2c0d52048062d61145d63985a6220000000000dcc38b55e02d68634d580013c063c000270cb904fd661883c0000000003709083da25f031581aaac653b107c5183c10ead27d468cd300024d80fc05664b213d5ca0005b1131a6be6ab380013a38ca2d00
  | 26 => 0xcc1b4c71c4946852ac137841a6a5b01a048d540a545fe4d38be0a209ec2c835c450ab898fc000547b29c63200029380000000000000f9d62ea004902725a423ce3689bc4b780004e700010e82000001f01b7ec6468ea8b8000c124c2ae8c0004762079f194ca7d813616480006605228000e8100055892f01bc0002b1e6314ac2ac1541f0c000be70000a18000655480083627a2d80a517b40000f758730e800000000021cc0000000000908ec0a385a088944423ea2b529449840004f898800002cd202000054ca910ba810669127753500000002a90000094f248b00002f1000067800000010020004311f280004b8d5a0f4000000000000004b45b6217000000007b00000006460cd0000000000d512c880000001d3342b54c0005fc511965c0760004d2a6291d89ea5da9ff4f381803a10000e7cac748482dc7b81940f325dc75e6e53760d6d48200032041047b6000000142857053bcff8f559ee00000022882103760901cecde800000000012ad0006a924c0582b382cfd544716bbe1d48aed54984e5b41518a12dda0f0c00190ea3900009e12861f728300006620001554000ef200029415291fe3601fba0398b20000000001b32d6f00007ae000a578002c05b90000298a0192420000002c6e0000000000001a84000000180968c00034b000039a2100f1037c568b5c000000000000031656b0a4690f00001a41192ba0001d4c00000000031a0a3e45a4a481dd0fc9b124489b868418c125d4ccc6d02d000000165625929c00006ac000442177c000d5f108aed229c4131f400015f697531706cb8d82a428e29d0000000000174400072000000014310000001715192617557e30877cd6322ba489504ca41d625b468ab6348bae6480408817d999555ca0d0003257ba00000d7800142057c000187443752f55d800000000000000012b50d300000000000006b8a1346ea93e637270455aa303c59f849eeaa59e207ac000cf256e13fa5b56f480000000000004d8050420edb852826f84ce0002703511a40364253abe035a65700000012200a88001d68f6200054f80019e0bef0002cdd29c0005a38000000000066c000000d9a0000e4cb1252200035240004af43419714fe000000368c3362f24c0234c990cdc8e11330eaf22c10b1be48201d846b879c10361b3e480016455a0000000087f00034a80000000003fe0000aae93f2102fc0f0a39a16a242c000000000020800034c00000008525a08ce0000000c520001e391122824e50000000b7f000016b5588f253386cd4ccb7a5eb89a8f024441be069da06db55c10034e5a3dd1449d5c00000027180014bca3369e080c0000006e04000a20bb700025855279839af1b912edb1f2da17aaa6aa3c6ca36199900000a8c3ad05000000019bd2c314c800353800025446c2f0000079f38c016db
  | 27 => 0x13f00027908c90001de8000000602859e8540000000832fba1a236504c215da7c9a30dd15240001bda6f8001880d7b20284f83dd607e1987c4a7eabab8af65c62cc99153ca7c94c3708000000b42bcb14e1a09b1a00046692f95e400000016ec0000e00c42b34ec29963b4b0a99f80000f9db3cca2228567b7180363c4df130bcbeed7766f1a5107605a53d032490c23f2f388d43950006748ec002c1a893b66d94a47bd183869487948b34d00009c203c23f000000026500000000000002a400000000002f5afb8b4ac66134428877eb260001d7458ad00497000000085f00000008f4bc830edb14c2f209277aff047200ac36a0786f429d090ad107c29c705297cc0a4a1221b20204baaa247b213033e4ae570aa40f7e3955a7a31496e4b913fc00077059e00008e800000000000001a800000000000005dd32230f437c0d80ae0ac12e36d726ace1865e4a95c8b4493d02586409670a9c51402803f59365c41c007131bc34d37c0830f080005d202cdaacc300242c552f939bbd528f8a0e22e3322341418ba08fcb60d0e481a2fb15c40000a45a6800135e6723210000ed600000008bc81a7965bc80015a6000000000000000013c80000000e78000000b8ed155e4b4d0606d56a6a47cc000d112f016057ba3b21aca7b47d668b494e97d76da9e00014941ca0000001b9a7ec4ea6042d68dba57337e80018b655e1478e091005443d7301ce6e0005f44edc0004d96d50ed8b99000000320c000c9800003100007fad91000026e0006a28001904967a29254405c2453870b806a65930259ab9428400611832b09298f50bd58c730654281010c950dc136f0382fb898ac2509c8f7c70c00036942afc3b6bb3441131537659000157e65b3bf400000095f000156d98c0001ef8be8adf8ed4d20c7400075e1bca0c95be71b18e08fab1e4490770b3041506abbb000000016a5ef821974e24431622d435c0002b1400000053c0002f0d7980aa658a5a4540d7531b2aac9c45d01e3a460dea29949da75d86a00000018110584a580019040009bb14e655c9ae1c50000001ae87fbeae878517e0000000050bd07a70312b137020000000000bb283c48f93d49f603231888540f043710d000058000032caecd56c3990000f0dafa0516ec85b8aa4a47000162010e0002760084000000000241800066a00023753c60499470000000000000077a3f4584800000000057012bc000863000000000096601980000000000000000000000000000146c59e21e80000015ec00048a800039900000021d40000002620001338a5c05d1cc11f3cbb0ac4da59b8815984a7d06b0c8995f0dbc000000331b6ccf78a591a87421768608b830001726dd752d075a2550c01f015611dcb514361fcd00ac690a9289cef88fc0be0d89852625d459dcc1c37a92ea15f45c49c22
  | 28 => 0x26f0001bb890539ec0007100000003284de44dc5d0321400000029b0001604c9400032e9a1860a1fdb115a764e2b3a0794b94000000349864e89813583e490a56d20e8000000c5d47535a9268962acd9e245773fe0c90ba88ac19749605f446c79d600052088a9271357580c74b643850f6e000158000000043a67f35630acbff0004ac216068022b54d219777f0bb42d2f4d20512f1075ed09b46682eb8a355f47930b01ee539aa6e559000000013943531b42680748001a1c0004380ee00010b68e280015719a4dbc02a8d3900d1cf52018186940001252e68000d4060980000000000000e80956455194b6b80007625ea000000000036d80f6000600614299088f17715715d0b322db605862c3484f81b9afed060baa1591986000d54cb38e153c28a0620a3c449da1b45d9af10b840ad650cf537e58b0970f69ae41ab56927e10bbc2e3c503cdba82de58011c0ddacae00e33f42c62dbe3cab64ff6115096000134c00063a1bec00067b41520545af44b000060c33004d5a609366568ac01a0470b8646c16a82ac10a02b54b8f300bc0b62a695d4000a6c0918e1e000b1c1a190700000001b09d397d647400000007f4d2a000000000076d6435e8800061200033400008c6350b6ac000cf467f1ba8f9e1903408001ae02840fb33c500ec7d00000013805f9321f210de651800034d5a52ce530a941001c79b5d41e3d46e0000da2e39358309dd710500000006e2a3dc0007a02790000d621121b535ba000966b3617490ac833cd024f415c85e4959bf83ae000435a5dfb3061325a93935a0d8e4efb62400097a4ea35601500004292f340009e61d8b1383085ba2f8dc10f89a8a4e583716683f06eb76c423073f56f01a062630212f29f043186720397ec9da3d80f8210908e7e50d4aaf94ae4cf2e09f5cc03cfabd68031022736460adcc776aab9a95ecd123d670a680011c9000000346400039c15457b2d9456bc860740dc4ba960b2e2072e0e9298c76c36097d0a888cc98e000432934f7165944169a991fc00052f6c58ea50003814000702b45000021000085000000000003966bf8001186d964700268acc5a8226011113abf8d9e868caa846e2842080aaccd804c9e78000000673370ac640da41ec323b1e9ee4a002f6db84cb2e786450165e624600017da0cf44f80008902c7329e3680004c601242d200060fee3add80000006e89ad8000c482bf2a1c000678c6794e891b96d8265344db275c1b317ae411248951a82554a475260ce3646f586419914135a00011896a94081fd800000190f00000000015dcd6b2ec07d2c28391562b0840ad761a75857e00063aa20663922415e049691806e00000000000000f4057b0c903e1aa80eb334ed4000323c00115ada6248800180592ade080019c8ba240e8000a2630b26832dc9040000002034
  | 29 => 0xae4c31065033095cca1866d07b5354d93ed681f0ecc1ec13d2df47921000ce9a190a61a08ae8d193423a46ab8cd010600000025a9af0bbd00000000000003f48001a086030000001926b6000000004ae0000e44001567af3389b3552fe00005300000d61bb3ff63ec96072f60c00000008b80001f9938a00053ada385366d18002f696aaaf113f000000000020880014629620002ce9246c8040780000000005f511f4000000347ae8b8f900000026040000000000000000000000282d70ed910000fc800071d1405956ea274b303800000030a0000000eea265d949d10f349dd36089d00000001618c802a550163526a40004630001d6c0007161b71d6134400020b349c66a6ee0000096000a8642015642f27866d03540f600000001108e929998000000bef5b56648a586fa00039e0000af400000019180007901ef1200b350000002950000626253400105e8542ed350cb9c3715b08684b5c0000b29f04fb2782112255400000021ec000b7281861f81e9213cf85fc2a55a1aa2293823cd966ae74481d202e072841ea3a4000809000221c79a67a32011790fe741ab8500c19691914cf4f50f400001f0000000bbb2308a216628b907e34b94c400039899413f888b00029100000d8d6b0000d8016866205af82e0005a12e70efe0003dc0001640065a4ab488664425473a2a191cceb26a8ad478a9031059e910e2c900b174b5bba1c33e34000fc06fc5f5c8be6e841e1099d043909de67e4000cbf0001eb8000500cc057f9aa98e6d8700000000004e60000000d1488a0000000000d6600000000000004d4c3c1ab25f898f89e32d00005d3343d40200040180011560001eb029f04402c02f878e00000026480015fa1490001d18f9f00065b13514e458c0002b2015865a000251cac05f26bd0f4e00074f9aa400081638a3e800000de00036f9f34efa38d10a11f0220539093f184a24b5f6df256f1e8cad17a8b0af4ac05406d14c00000063f9aa4000a9800799f991400000000001a06ce0000fe0768b9729053906c69d354722f0fbc0000b6139d47ab3214bdd7d1800d9d4484a4d3e32a3a6988c0c06a82b4aad466ec4d1feac1155e226219076a57a09e1d58d275921146d818bd5ead9c5dc11e0aa61c90e9f5bed86db4017aaa95664bb0db2f8417c4870b89831138be93b9040caf185d22f88c3901bed887148141e9822e02f08bc700017884585445210718a9cfa2d4d1a742caab430f670ad0c1f41fe13401a81600000c080a519818600026786ce0010af5082c9e9390f00b1914cb1680003a812824e46e293000044610e44240000002d4800000078c0000000000000000000173c00029e4000000cb00002e7e00069d68321800006a43149a443250000b98000c68957c4100e05571768e6eeb160adc18591db0a3a68854fc3c4f5660f
  | 30 => 0x83e2829d79e5a35151261b084dd549800057900069401c8000960000087f9b29f2169062507e18c8c9ea48ee80000ba339c396230451a84d73ea1e0002070feab6a28b814d2b411b0001654000000581b64c00064906190c40ed65300018580001b70002af4000a0a0f48000000000387a94a066c1130e1f88000d68000088893a77b000000067000041717d05b80000003268000d55449864c000b8d4a6a660ac200021c9f6c0000005cc00003f8cfa5850c54bc800031c0e849f8000660a18567c7d364788660ae2aa001acbd91508c01cafaa0003bb80000009a50e6335b3b079400048b0001bb60002c8009c3340000000000906000584000000000050b800000012a000176d6f600000008f000010a00010d000025f3630000000000000175ecac44880009805e80040000634ece9db06918f40000001d726752500004899ebc880a28559475528caef0bf401d3700000ed2df1b020001de2df951a7402eac0003c1000386ac6812e5f1000231db21ce845e98028ca6d7c721fad24c62380a968835096b04f89667e20ca5ba2c1cdc65de2868000000c94ebe7600da473232698142e415f66d853d9deaeb000002087800024b01d9a8c000006e0414320000000f0e36400009b2d48000000182c000372cca01f80017a07356070934000d2f2bb0001b514b8086000150a20a5dbc1740000005f280019d40005a43388000000170cdb11b2d1b0710e1cdac04c6d2d9de851ab7379e921b180004da00014c2c4f48a247018c00021f40000000bd03468187b2d7e56db4240001aba4e018400028300010195e86c835f00be14d63e39e94032488f8430727075a4588769abd6285bf164757986c57f0130774d3609529e8cf000016633126a084b79100017f8c4825310302363fa4814b719608580002a19454f420003eaa644256aad80005410709c7cafc000da0000339d1cc000777915128400043f412b4cd8e2125d21000171400000017940000000000c840002a580000402deaad0000f44a9e0006558000000ad42948000ab790a1e300012a43dcba38001918d7c00015016dc94f13357c0000ad53e4e8e80000001dab2880da3778898924172000000031c00043a8001498a5c00021d8434274b29eca8dcb620752000157564e2b9196800000000000000012780000000cf800000009288f90f6aba1070249b525035c90000dccc74bf502b4000b18085881d7d38eb5564b917c6db6daa541474489410202a48245c66eb2578000db391c677113c7436b21a710280003f701221e4dc45a8c0004e61df07c1cb97cc2c90df985ae8abfd46a2cb5b7580a6d6ef90298da41b6a9d40001ef00006c60005e130e654056ebfa219e672d6861800c3629adc0d764fa5f758429588ea61c0b8023b6a0a2a0fa2819ce6355458371a770cb0d007804bc115
  | 31 => 0xd2b00014d1264c4a0002084dc23b9000000164b72300019a4e24bd86ae1ca8f6e08f0050a6b52f6700001fc0a607e41bef119b6ecfb40db339b9400033e113c9105d31bf890c6a89313fbb1c94421ca0002d29a1cbb93810000a188b73b2800133486e60a000079698d59090a0e94a4195884d55b09a88000000000000381a2d028e0284c183209b02bf05883fda02ae413ac1e49e027100024391b60000002c906601ea99993007744e915ed3e8f84a534cf95084a011a316800132e4223ab000140e00025228d8276c430001c7c4106e94a20000000000000237d04e9380b4a5b0712bad31b87c977e56f4ba22595186bd212333c7f8800802800106a33b1822ffcfe8710173aa8cbfd0e72cd0a618ea23809426dc69e0000e22ef05ca9e90664001b36a295b30000eb50714bd4000a2204521580010962b5a9612400000d669c80008ba0002df32440000000000948000d1e1c90001b7200000000019ec9fb3e20000000ca537d10216960001ff9b60d663c068a08783c95683ea30192cc42f63104789467fe33b828ce02d051a091057d05245982f48ce6a035b1c00000037e80000000ca7880e8cf080000c7ddb2ec52075879509dc18880001066e3d83cb9400032d0000ab9d8f400114a04e3db256c9321b821080017aadacc132e018cedbb9bc14643dc22d25017e0b9638eb0d020292ea60287878c19f4334a0a420262b0d065c7a02fe88d103e7c0000b710002ee85b25a61eacb38566b6957c866612317862c000000008b90c0554000096313afb0142cd465303b081789b5c300001de0000c78ce563600003bcc7849949b22cb274bacda7363a4dc9b6a3242c882e9e8c8eb242e3116c97205e352856dabbb84200b2545b80e71ae58deb654e336bcedf0000000b8c00048a3bc40016120d933e833868819901b2c94f50c884c8075095a9ba1378a2d892779e280e8d99874f4b800653a0c5c59b0aa72a834
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c435d94304001c3886b2a860800e3721d6350c100bd4e422c6a1820038ec825d6620400117f08b9cc40805e2f211739881001c76412e73102000aaf845ce620400155908b9cc408002aba13539881000556c26a73102000e4f5394e6204001d1a8621cc4080029ba16719881000536c2ce3310200c8ee87d4662040011db0fa8cc408002b3a0f519881000566c1ea33102000aae84cc6620400155b0998cc4080029ba14319881000536c286331020038f8805d562040071dd0fa92c40800e3b21d525881000567418a4b102000acd8314962040071dd0f992c4080029ba14325881000536c2864b102000aae840c9620400155b08192c408002bae01755881001d74402eab102000ace831d5620400159b063aac408002abe11735881000556422e6b102000ae4815cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd620400155d09a9ac408002ab613535881000727a9ca6b102000e8d4310d62040014dd0b38ac4080029b61671588100047743ea2b1020008ed87d45620400159d07a8ac408002b360f515881000733a8ca2b102003aea8014562040015d30028ac408002aba13315881000556c2662b102000a6e850c562040014db0a18ac40800ebaa00315881000574c0062b1020038df8758e320402f17909bb2640800e3720f764c8100045fc22ec99020178bc845d93204001878e8b2a64080022f61b744c8100061f32ee89902000c3d65dd1320409b93cc7ba264080022fa1d644c8100045e43ac899020038dc8758d320400193ee8b1a6408003271d1634c81000657ba4c49902000cac7498932040071d90eb1264080032bdd1624c810006563a2c49902000c7565dc532040019aac7b8a64080033958b714c8100047ac30e29902000c75651c532040019b2c6b84620800a1fa1776884100043ec2eed108200287e855da21040010ff0cbac42080031798d75884100043fc3acb108200087d8759621040018bceab1c4208003175d56388410006373acc51082000c6d7598a21040071df0eb1442080031b9d5628841000636baac51082000ce9625c221040031b907bb2420800e3b20b76484100062e39aca908201e8dd86dcd21040018bccbb9a42080031759773484100064f326e690820008de8758d21040091b90eb1a420800327dd163484100064e3a2c69082000ccf739892104001998e7312420800333dcd62484100066639ac490820038ed825d821040078f4e0b28420800f369c163084100063cb2ae01082000cd9635c021040199d4c4b8042080031e1d776440100063dc2eec8802000c7885dd910040019b707bb220080033620f764401000675c16ec8802000ce882dd910040018f6edbaa200800336ddb73440100066dbb0e68802000ceb76dc910040019d6ec39220080035a1d47244010
  | 1 => 0xf0abb2648800a1f215764c9100045fc22ec99220178bc845d932440011df04bb264880023de05764c9100bc5e420ec9922000c3c74d95324400117d0dba264880030fd97744c9100061e32ee8992204dc9c63dd1324400117d0fb2264880022f21f644c9100646f43ec69922000c9f74d8d3244001938e9b1a64880063ba1f624c91000657ba6c49922000cac74d89324400195ee831264880032b1d0624c91019e6c386c698a200287c859da21440390f90cbac42880031718d75885100043fc3ecb10a200887d87d9621440018bcebb1c4288003175d76388510006373aec510a2000c6d75d8a21440018dcea31442880031b5d462885100062e39eca90a20328de86dcd21440018becbb9a42880031719773485100064e326e690a20008de87d8d21440671b90fb1a428800327dd363485100064e3a6c690a2000ccf73d892144001998e7b1242880c73a1c3624851000667b98c490a2000ccc7318921440018f0cbb8242880033918b714c110004bac28e29822000cd7631c530440019c8c438a60880025d61671c811006672314e3902200087f855d920440050f90abb2408800237e0d764811000c6e41aec902200287c851d920440010fd0dbaa40880031718f75481100043f43eca902200087c87d9520440018beebb1a4088003171d7634811000637baec49022000c6c75d8920440018deea31240880031b1d462481100066a31ee29022000cd4631c520440019cec438a40880d31e9db65c411019e6d3b6c78822001cda7618f10440639d4edb1620880333a9d862c411000734328c58822000a3e84dcd650400147b09b9aca0800317dce735941036d3dc02e4b282003a78805c965040014bd06392ca080029760c72594100043f43864b28200087d870c9650400147d08192ca080028f61032594103653cc04e2b282000a3e84cc5650400147b0998aca080021fa1c31594100043ec3862b2820038de87d4d63040018beeba9ac608002a7a135358c100054ec26a6b1820038dc8754d63040071bd0fa1ac60800317dd67558c100054f424eab182000a9d849d5630400193ae83a2c60800237a1f5458c100046ec3ea8b182000e1f54951630400153f08b92c608002a72117258c100056a40ae4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b1820008de8714963040011bb0e292c608002a7a105258c100054ec20a4b1820008de8710963040011bb0e212c60800297a144258c100052ec2884b182000a5e851c563040014bb0a38ac60801237a1f5158c100046ec3ea2b182000a9e84d45630400153b09a8ac608002b3a0b5158c1000566c16a2b182000e575194563040091bd0fa0ac6080023761f4158c100052f42882b182000a5d8510563040075b50020ac608002b66004158c100064e21eeca182000
  | 2 => 0x431d89100053742ee1b122000a6d85dc362440014dd0b986c4880029b61730d891006636312eb3122000c5e73d9662440018bce632cc48800317d9573989100062e32ae7312200cccc625ce62440018bcebb1cc488003175d763989100064f3a6c73122000c9d74d8e62440018bcea31cc488003175d463989100064f3a0c73122000c9d7418e62440018dcebb14c4880031b5d762989100066739ec53122000ccd73d8a62440050fd0dbaac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac48800317d9773589100062e32ee6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac48800237e0d755891000c6e41aeab1220008ef825d562440011f700baac48800317dd773589100062e3aee6b122000c9f74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440018deebb92c4880031b1d7725891000667b9ee4b122000ccc73dc962440019a8e7b8ac4880031e1d7705891000477c3ac43122000a6f8558862440014d90ab10c488002b3e0d62189100056641ac4312200c8ec825d4624400117f08b98c48805e2f211731891006476412e63122000c6e76d9462440011db0f328c488002b3a0e651891000566c1cca31220008ef87594624400159f06b28c488002b320d6518910006373b0ca3122000e6581194624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab2116318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d90631891000746320c6312206eec61018c62440ddd8820318c4880039919651189100076231ca23122030ae4865446244001d88c6a88c488002abe11731891000556422e63122000aae84d4c624400155b09a98c488002b9a07531891000572c0ea63122000e4f5394c6244001d1a86218c488002b3e0d71189100056641ae2312200c8ee87d4462440011db0fa88c488002b3a0f511891000566c1ea23122000aeb8054462440615d100a88c488002aba13311891000556c26623122000a6e850c462440014db0a188c4880029be1570189100053642ae03122000a6e85cc062440014db0b980c4880029be1510189100053642a203122000acf83440624400159906880c4880021fe15768c9100143e42aed19220008bf845da324402f17908bb464880323b209768c9100143f42eec992200087d85dd9324402f17d09bb264880022f613764c9100bc5f424ec99220008bd849d932440010f
  | 3 => 0x8b1a2000c3c65dd16344001938c7ba2c6880030fdd76458d100061e3aec8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d100066631ee4b1a2000c6f651c963440018d8ca392c6880032bd907258d1000666318e4b1a200287e87dd5634400117f08baac68805e2f2117558d100046fc1aeab1a20008ef825d563440191d904baac6880021fa1c7558d100bc5f43ee8b1a2000c3f75dd16344001878ebba2c6880030fdd47458d100061e3a8e8b1a2000c5f75dcd63440018b8ebb9ac68800327dd37358d100064e3a6e6b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d100062f3b6ca31a20008dd8799463440014bd0b328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100052f430ca31a2000c5e761946344001cab02328c688003279db6418d100070fb2ec831a2000e1c65d9063440011bb0f320c68800297a166418d100052ec2cc831a2000a9e84990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000c9e761906344001c3eca320c688003871946418d100072a32ca231a2032ad48654463440050fd0bbb286880021f6177650d1006477416eca1a20008ed82dd94344001938873b286880021fe157650d100143e42aeca1a20008df835d943440011df04bb286880323b2097650d100064e218eca1a2000e1c43d95434402f1bd0fb1a868805ea7a136350d1000572c0ea5b1220028ef8754b624400159d06296c488002b360c52d89100053742865b122000a6d850cb624400155d08196c488002ab61032d89100056741ccbb122000acd83997624400159f06b2ec488002b320d65d891000732c08cbb122000e4f65d8f6244001c98cbb1ec488003a3d9363d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d89100073232ca3b122031ae486547624400159d073aec488002b360e75d891000573408ebb122031ae5811d7624400155d09b9ec488002ab61373d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000557426a7b122000aad84d4f6244001c9ea729ec488003a350c43d891018c7743ea3b1220008ed87d47624400159d07a8ec488002b360f51d89100055742663b122000aad84cc762440014dd0a18ec4880029b61
  | 4 => 0x80051bf0ea9ec7880023be097650f1006476412eca1e200287e851d943c40010fb0a3b2878805e37a1f6350f100bd4f426c6a1e2002c6e7594b62c40051df0ea96c58800237e0d7558b1000c6e41aeab1620018de87dcd62c400193ee9b9ac58800327dd07358b100064e3a0e6b1620008ef8758862c40050fd0b3b465880021f616768cb100045fc22ed19620178bc845da32c40050fd0b3b265880021f616764cb100bc5f424ec99620008bd849d932c400117f08bb2658805e2f211764cb100046fc1aec99620038de87d8d31c40011dd0e31243880023be1d6208710004bac28e298620318ef8758b20c40012eb0b38e41880c23ba1e624831001c6e43aa6b1c200287e85dd943840010fb0bbb2870800e3721d6350e100bd4e422c6a1c200287e87dd562840850fd0e3aac50800b1b1d65258a1001c7643aa4b14200087f855da32840050f90abb4650800e37e1d638ca100043fc2aec994200287c855d9328400117f08bb2650805e2f211764ca1018477c3ac590c20318ee87989218400147d0931eca880028f61263d951000537414c7b2a2000a6d8298f654400147f08b9eca880028f21173d95100062eb98e7b2a2000a5e839cb65440014bb07396ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880028fa1331d95100051ec2663b2a200087e870c765440110fb0e18eca880b29da0770d95100043f43e61b2a200087d87cc365440018baeba9ec688002a7a1353d8d100054ec26a7b1a2000ad581d4f63440051bf0ea9ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec6880039560465d8d100070fb2ec9b1a2000e1c65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd829936344001ca8cb28ec6880ceb521951d8d100062eba8ebb1a2000a9e841d7634400153b083aec688002b5a0475d8d1019d6ac08ebb1a2000c9f749d363440011bd0faa6c6880023761f54d8d100070faa4a9b1a2000a9e84dcb634400153b09b96c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c68800237a1c52d8d100046ec38a5b1a2000a9e8414b634400153b08296c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c688002a7e1171d8d100054e422e3b1a20338de87d4763440011bb0fa8ec688002a7a1351d8d100054ec26a3b1a2000ace82d47634400159b05a8ec6880ce37a1f41d8d100046ec3e83b1a2000a5e8510763440014bb0a20ec68800297e1570d8d100052e42ae1b1a2000a5e85d0363440014bb0ba06c6880031718f7558d100043f43ecab1a2000c3c74d9563440010fd0e32ac6880030f1d06558d100061fb2ee
  | 5 => 0x29720d71d952000537c12e3b2a4011a6c825c7654807b4dd0438eca9010a9b60871d95200051f42663b2a4000a3d84cc765480010fd0e18eca900021f61c31d95201bd37416e1b2a400087e87cc365480010fb0f986ca9000a1fa1671d8d200043ec2ce3b1a40008bf845c7634802f17908b8ec6900021fa1f6558d200061e3a6cab1a400087e871956348001878e832ac6900030fd977458d200061e32ee8b1a4000c7765dc563480018e8cbb8ac6900031dd947158d200063a328e2b1a4000cd4631c563480050fd0fbaac6900022fe117558d200bc5e422eab1a40008f7815d563480011e902baac6900021fa1c7558d200bc5f43ee8b1a4000c3f75dd16348001878ebba2c6900030fdd47458d200061e3a8e8b1a4000c9c74dcd63480051b90ea9ac6901c7271d15358d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480019aca638ac6900033554c7158d200066b218e2b1a4000cd4321c563480050fd0bbb286900021f6177650d200064e21ceca1a400087f855d943480050f90abb2869000237e0d7650d200047bc0aeca1a40008f4815d94348001938863b286900038710f6550d200bc6e43ac6a1a4017a9c8458d43480015a902b1a869000e3ba1b7250d200063632ee4a1a40039ea80dc943480012db0a39286900031b1947250d2000666b18e4a1a4070d8c431c943480071bf0eb1c64900a2a7211638c9200056a40ac71924000c3c74d95324800187ecbba264900030f197744c9200064e3a6c69924000ab684cc761480050fd0dbaac2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac29000317d9773585200062e32ee6b0a406fc6d7219461480011ef0eb08c290002b520d6118520016373aca430a4000ab684cc461480010ff0abb4629000a1f215768c5200143f42eec98a400087d85dd931480018d8cb3b642900031b9db65c852037c3e432eb10a400087d87d9621480018b8e7b2a429000317d9773485200062e32ee690a4000cd473d8521480019a8e630a42900031e1977048520216363b6ca90a4000d8c741cd2148001cceca30a429000372dcc70485202163d3b6cb9024042e6b62d9720480071b90ea9ac61000a1fa147158c200043ec28e2b1840038dc8758d430802f53908b1a861000e3d61e51984200046fc1aeab0840018dc835d561080031bd0fb9ac21000327dd373584200064fba0e6b084000c9c741cd61080071e90ea8ac21000ebc201515842001c7ac3cc31884001ad483586310800117f08bb2621005e2f211764c42001c7a43ac29884000c6e755da21080018daecbac42100031e1d776480200063dbb6ea9004000bab844c92
  | 6 => 0x43fc2aed20a600287c855da414c0050fd0a3b482980021f614769053000ccfc3a8720a6017a9c8650e414c00193ceca1c829800e37219744c530004e6412e898a600b8de87185314c0071bd0db9e429800a1fa1476885300043ec28ed10a60178be849d9214c00117b093b242980063720c76485300043fc2aec10a600287c855d8214c00117f08bb0429805e2f211760853006666312e610a600c8f8865c0214c0019e0c2b80429800ea7219435013000e4e3b286a026003b988050d404c0050fd0b38ec7900021f61671d8f200646e43aa6b1e40178be84dc563c800117b09b8ac79000e3b2097650f200646e43ac6a1e4017a9c8458d43c8019998e4b1a879000b1b9d652987200143f42eed18e400087d85dda31c802f17d09bb463900022f613768c72006667392c718e4000ccf76dcd21c800199eec39a4390003631d0734872006666392c698640038de87d4d63880018beeba9ac710002a7a135358e200054ec26a6b1c40038dc8754d63880071bd0fa1ac71005e2fa137158e200045ec26e2b1c400287e851c563880010fb0a38ac71000317dd67558e200054f424eab1c4000a9d849d563880014bd0b3a2c710002976167458e200064eba0e8b1c40008de87d5163880011bb0faa2c71000387d525458e200052fc2ae4b1c4000a5c855c9638800153f08b92c710002a72117258e200056bc0ae4b1c4000ad4815c96388001c9ea5292c71004a37a1c5258e200046ec38a4b1c4000a9e84149638800153b08292c71004a37a1c4258e200046ec3884b1c4000a5e8510963880014bb0a212c710002a7a137158e200054ec26e2b1c4000acf825c563880014bd0a38ac710002976147158e200046f43ea2b1c40008dd87d45638800153d09a8ac710002a76135158e2000567416a2b1c4000acd82d4563880011bd0fa0ac7100023761f4158e200052f42882b1c4000a5d8510563880075b50020ac710002b66004158e200143f42eeca1c400087d85dd9438800193887bb287100032710d7650e2001c6e43ac6a1c4017a9c8458d438800117b0dba265101372798f744ca2026c5f43ac899440678bc87591328800193ee8b1a6510003271d1634ca200066cb1ee099440038f58794661880058eceb28cc31000e3d21d515862001c6e41eec98c4000cae64dc9318800195cc839263100033358c724c6200062f31aeb10c4000c5e7558e21880018baeab1c43100031d5d661886200063abaac310c4000d69755c221880011bb0db9a43100032799373486200046e43ac690c4000c9f7458d2188001938e8b1a43100028fa1063d95200051ec20c7b2a4000a3f845cf654800147908b9eca900028fa1073d95200051ec20e7b2a4000c5d731cf65480010fd0e196ca900461f61c32d95200051f42065b2a4000a3d840cb65480014bf06b8eca9
  | 7 => 0x9c439d943484011bf06bb286908023be097650d210143f428eca1a420087d851d94348401938863b2869085e37a1f6350d210bd4f426c6a1a42008be86dd1324849b938c7ba2649099e2fa1f644c92126c5e43ec89924200c9f74d8d3248401938e9b1a649080335d8c714c92100656326e498a4200cac641c9314840199ec639262908031718d75885210062f3aec710a4200c5d75d8e2148401d18c831c42908c63b219708852118e74302e110a4200ae98214360484015e302286c090803279d363981210064eba6c73024200c9e7418e604840193ae831cc09087a3721b73581210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d60484011f70eb00c0908029e21560181210043fc2ae1b18420287c855c363084191b90ea9ac6108323b2097650c210646e43ac6a184217a9c8458d4308419998e4b1a8610833339c9638c4210e63abb2eb1084200ce651dd921084019caa3bb2421080333ddb734842100667bb0e69084200d8c741cd21084199cca5bb242108033954b76484210066bbb6e69084200cd7761cd21084016cb0bb92421080b1b1d652580211847643aa4b0042308ee87c8560084615d50190ac0108c23b21d21580211857440242b004202c78759416008401cd4a5282c0108323e21d505802101c5e43aa8b24600287e851c5648c0010fb0a38ac91800a1fa167198a300043ec2ce331460038ec87549628c0014db0a212c518002b360c4258a300045fc22e530c60178bc845ca618c0071eb0f28cc31800b1d9d651986300045fc22eab0c60178bc845d5618c02f17d0fba2c318003270c7745863039e4f986e8b0c6073c9d30dd1618c0071e90ea8ac3180ca37e1d618c6300054fc22c318c600287e85dda218c0010fb0bbb443180022fe1176486300bc5e422ec90c6000cac74989218c00199ee731243180032b1d162486300145fc3aa9b2260018dc835c7644c0011df04baac8980323b20975591300047bc0aeab2260008f4815d5644c0050fd0a38ac8980021f61471591300bd4f436c8a1a600095d851c9434c0e5938c839286980ca37a1b7150d303946fc3a87b126017c9c7450f624c0011df0eb10c498002b920562189300045fc22e231260178bc845c4624c0010ff0abb4849800a1f215769093000c6e418eca12600199c8750d424c001938eca1a8498002e3209435093001c6f436e91926028c9c64dd2324c0073b501ba464980423761f628c9301946e432e3192600099f845c6324c0010ff0ab96c29800a1f21572d85300047bc3ac230a6000ae482584614c0050ff0eba8c29800b179d553185300be4e3a28630a60008bf845c8614c02f17908b90c298003330c972185300
  | 8 => 0xeb38ec710802a7a137358e210143f42ee0b1c420087d85dc1638840193887bb2871080a1fa167650e210043ec2ceca1c42008dd839d9438840193886bb2871080a1fa147650e210043ec28eca1c4200e1c43595438842f1bd0fb1a871085ea7a136350e210063732ee4a1c420096d851c943884018dcca392871080333d8c7250e213a6c6218e4a1c4228a9e84d8e3288401878e8b2a65108030f997744ca210061eb2ee89944200c9c7458d32884018eacbb8a65108031d594714ca210063732aed90c4200c6d7659721884018eccabb643108031d5d965c862118c7743ca4b044202c6c7594960884631dd0f90ac1108c6baa0321582210143fc32ea304420087d8799460884018bce7328c1108021fe1d65182210062f39aca3044200c5e655cc60884018bacab98c1108023ee1d60182210062ebaea7b1a4200a9e84d4f634840153b09a9ec69080a37e1d53d8d210043fc2ae1b1a420287c855c3634840153d0932ec690802a761265d8d210054fc22cbb1a4200a9c8459763484015b700b2ec690802b620165d8d210052f428c9b1a4200a5d8519363484018baea3aec690802a7a1075d8d210054ec20ebb1a4200c9f749d363484014bd0a3a6c6908029761474d8d210046f43ea9b1a42008dd87d536348401c3ea92a6c69080297a1772d8d210052ec2ee5b1a4200a9e84dcb634840153b09b96c69080393d4a52d8d210046f438a5b1a421e8dd8714b634840153d08296c690802a761052d8d210046f43885b1a421e8dd8710b63484014bd0a216c6908029761442d8d210054fc22e3b1a4200a9c845c763484011bd0fa8ec6908023761f51d8d210054f426a3b1a4200a9d84d47634840159d05a8ec690802b360b51d8d210072ba8ca3b1a42008de87d0763484011bb0fa0ec69080297a1441d8d210052ec2883b1a4200a9e849c3634840153b09386c69080297e1570d8d210052e42ae1b1a4200acd821c363484011bd0e286c6908023761c50d8d210054f420a1b1a4200a9d84143634840159d04286c690802b360850d8d210056b408a1b1a4200ad58114363484014bd0ba06c6908029761740d8d210046f43881b1a42008dd871036348401938c7ba2c6908022fe117558d210bc5e422eab1a42008df835d563484011f700baac69080e3e2017558d210bc5f43ee8b1a4200c9f74dcd6348401938e9b9ac6908032b1d37258d210046ec3cca31a4200a9e84994634840153b09328c690802b360a6518d210056ac0cca31a42008df87594634840153f08b28c690802a72116518d210056dc02ca31a4200ad880594634840193cedb20c690803879d76418d210070ebaec831a42008dd87990634840153d09320c69080237e1d6418d210052f428c831a4200a5d85190634840193cec320c690803879d46418d210070eba8c831a4200c
  | 9 => 0x70185320045fc22e030a64178bc845c0614c8058bceaa9ec09905f271d143d81320056641287b02640287e859c7604c8010fb0b38ec09905e2fa1271d81320045ec24e3b026470cad72192604c89b1790dba2c0990022fa1f64581320061fbaec8b026400c3c75d91604c80117d0e322c0990030fdd464581320061e3a8c8b026400cb764dc5604c801968c9b8ac0990032dd9071581320065a320e2b0264008fb87580604c8191dd05baec9188023b60b75d92310043fc2ae1b24620287c855c3648c4051790eaa2c91885ea7e196450e31004aec28e4a1c6272c9e641c9438c4bf1bb0db8a87189ca3721d4358a310be4f3a286b1462008ef87588628c4050fd0b3b485188021f6167690a3100cce43a86a146200c9f7650d428c40171904a1a85188a327993748ca311046fc3ac519462218df865c6328c40133f08b8c651885ea7e19439063100e4ebb28720c6200b978150e418c4050fd0fbaac11880b171d553582310be4f3a286b0462178be84dc9608c40117b09b92c118803330cb72582310047dc3ac030462028bf87553644c4010ff0ab86c89880a1f21570d913100656320e4b2262008ef825d5644c4191d904baac8988023ee01755913101c7c402eab226200ccf731c9644c40199862392c89880333cc0725913101477c3aa5b126200a6d8510b624c40159b06216c4988023be1d621893100556422c4312620087f855c0624c4050f90ab80c49885e37e1d648c53100566412c918a62018dc865c2314c4679b0c0b8462988022fe1172d81310bc5e422e5b026233c9f635d0604c4011f70eb00c0988323721d5358f210143f42ee0b1e420087d85dc163c84191b90eb1a879085ea72116350f210051f424c6b2c4200a3d8498d65884394df0cb92cb10802da20172596210051f426e6b2c4200a3d84dcd658840147d0939acb108028f61273596210062fb9ce6b2c4200a5f835c965884014b906b92cb1095a9de0572596210053dc02e4b2c4200a78805c965884390fd0e192cb108021f61c32596210051f42064b2c4200a3d840c965884ad4dd0538acb108028fa1331596210051ec2662b2c420087e870c565884010fb0e18acb108029be0970596211d536412e0b2c4200a5e831c165884014bb06382cb108729ba08705962100536c10e0b2c4200a76811c165884394eb02382cb108021fa1f30596210043ec3e60b2c4200a3e840c1658840147b08182cb108029da0430596210053ac0860b2c420087d87997638840187ce932ec7108021fe1d65d8e210061f3a2cbb1c4200c3e655d3638840187acaba6c71085e2fa1375d8e210045ec26ebb1c420087d879d763884050ff0ebaec7108030f9d674d8e210061ebace9b1c42178bf875d3638840187ceaba6c7108030f5d574d8e210146fc3aa7b1c4271c9e7454f63884018ea
  | 10 => 0x2200000c6d75d4b6250c0159b06296c4a18034710d751894300477c3ac4312867aacf835886250cf3d1886b10c4a18032710d751894306476412ea3128600c3e435d46250c018b886ba8c4a18030710d751894306636412ea312860cc5f325d46250c198ba64ba8c4a1803170c575189430663610aea3128600c5f305d46250c198de40ba8c4a18031b5d752189433c74621ea431286178dd83dd76150c01b1887b92c2a18036310c72585430068e21aea30a86008f7875846150c010fb0f3a8c2a180a1fe1d75185430068e21aebb02860087d879d76050c050ff0ebaec0a18036310e7298143006c621ae530286008fb875806050c0193886baec91900a1fa1671d92320043ec2ce3b24640087f855c3648c8050f90ab86c9190322f21d54592320143fc3aeb30c64008bf845d5618c82f17908baac31905e2fa1f74586320064e18ee8b0c6400c9f30dd1618c8050fd0fbaac1190030f5d754d91320054ec1ea9b2264028bf87553644c8050fd0b38ec8990021f61671d91320043fc2ae1b22640287c855c3644c80156d0332ec899002ad60665d91323ae4f3b6e7b226467c9e7654f644c80187aea3aec899136a7a0c75d91320054ec18ebb226400e2f5294b644c80117d0e296c89909a2f61c52d913226d4f418a5b226400a9d8314b644c80147d0b38ec8990028f61671d91320054fc1ae3b22644da9c835c7644c80117d0fa8ec8990022f61f51d913226d4f41ea3b226400a9d83d47644c80155d05a8ec899002ab60b51d913226d4f41ce1b226400a9d839c3644c80147f0ab86c8990028f21570d91320045f438a1b2264008bd87143644c89b53d06286c899002a760c50d913200557410a1b226400aad82143644c80156d02286c899002ad60450d91320046fc1aeab2264008ef825d5644c80117b0f328c899002a760e65191320055b40cca3226400ab581994644c80117f0eb28c899002a7e0d65191323bd57c12ca3226467a9e83194644c8eb53d0ca98c899002a721953191320070fb2aa63226417a9e86d91434c84d938edb22869903273a1f7250d3233ec7ba0e4a1a644d9ce861c9434c81999d0c392869903353a147250d32066a6c28e4a1a640cd8e841c9434c819b1b08392869900363d907250d3233ec6320e4a1a6476d8c411c9434c8edb1e8039286990a32719373509320654e43286a126401c9c7650d424c81971904a1a849900637219748c9321464e322e91926475a9e86d92324c8051ef0ea8ec2990030f9d764985320061ebaec930a6400c3e75192614c80187aea324c2990031d5d761985320045f43ec8b0a64008be87191614c8e995ee4322c2990023de1d61185320162f3aaa630a6417c9c7450c614c80159904a18c29900a3d61e51185320163b3aca230a6400e5553544614c8010ff0ab80c29900a1f215
  | 11 => 0xe9d60d2f70640a2000b908b911eb425482a863b6cc2a464b3a0e380e86423ce1ec486fe0c708483c4dacd210fcc5c5ea72ec488e45893dc51c5e9780b641e37d40610cc062410cb978578a08cf713fa8d43548a57a86cccfd1a15283f2f3562cacd7645e342862e48b4a4eb09946a88605fe1c53003e4e412505900749a947d6402450f81d9678c54bfec3d142ed83bc3c97bd0c82013acb3c658fcd5980060080120b201c01000200c00400200000c00800400201000000200201600200400402200001600001600600600000200402400c00c00401000400600400001c0620500040000240040c600600005401c00000000200202204600401200402800203c00c00801c00a01600200a01002600e02001600203c04802200200000001000801201e00c00a02800400402404a01a00001600200201800601000201000006e00c00000000001001802e0420a000600a00200000c04200000400400c00400202a03600200c00200600000003600800600001c00603a00800000600000000000400e00800800800000c00200c00007400201c00000e00000800800000000e0020240100c201a00000e00204c00600601e02e00602c00000200a01400000000e00200800003e00801802600800a00400e00005801801000001200e00800000001200200c02a01006001200000e00000a00200000600609e03800400a00600402e00203e00a00803200200000000400001800000003600000200800400002c00400000000000800200201800000e00000001601400e05800200600004000402601804200000600004a01603a00200800200a00801600000800000200207203600e04c05600000000200c04800400000007203c04000200003400000200400c00200002e0080200000180040020060200020b600200000400200002403200003c02a00602000801a00400a00603c01201200c00200c01600200a00000601400a01800201400200c00000400800800002600401a00800c00c00c0000000060020060e002e00002000008600c01c01005002000005a00200e00008600800200c00000007200003000001001002600400601c00001e00001400800000400200200200600e00200c00601e00002801405c00400400a01402400801a0020060060a602800600802000e00400400e00400600e01c00a0520020020200080d002c02a02400800a00000400600000202202201800000400402400e01c00800000200000204a00000001200200a00e07401c00000c00000200000a00200400200400e00e00201a00200a00006c01000400000000c00a00000a01001202200200601000001200600e02200000002000003200a04a0100080520000300000000260000080000b800801203e00001004c00005407a00a00201400400000000200002600000a0180
  | 12 => 0x33d71d0a48686700124649e97bb76d3540014f00f521c000004694ad17a6f0e001270000d1cfa8b18f8170968489552507cc7444c6922e47b95f910c000000b54000f912cc68000116c0d80000008d00008c51795702dc0008d80000011cce58170000b48f549304cf7b8bf45a10c661cb3139520d0d8b715a0c14a4568c79a2640013204840006b0584b0c35d1588e86648980005b8c306880015b00000012dd710fa40000000003153ecde09bd50200174d3104e4000cf48855cc1283f167ec88368001600573660000a6c8f023d6f40015900011200981ba07caf8d3c00090d06a6194ac89117ca20aae9e0150669620b9eb0ec9441506c3486406d9690eb8250facee88883a45fc7a265e55492c95884014c4bd07112d2140561e53d400143af180a80590bc000f0569d7a371489c0b200018852953e28d2d4f7e03b77c58cd290a8784bb93680003734fd38944c9b0c783946ea0f03247470822c17456b101400135076b53d0182593780000014695d0ad52bc0011a4158000000bc40006630280016ac566c90afca80fe818c79e3fcb1b3f4a3d10479c25d3407168ec0006ee84c6c00000003e806d0f10355514300005e12600015bd7a00005c2da06dcabc71a2d0000aa0f1400082ca38e666d4c08cac9e5734880d5e0000011fcd564356e8000000000ec522cd64001330072420f7c261664000d00001604b04e453850ef4dc9d56a800000000136c0001d0000000000254000000c8125456c001790d0c000d40000001408000c1200163c001050b8d31c2d4d3a00117ad4d2ec000000e4c0009716103aa5948195692401797cc960000000fc4df421c3516c40840011d9374cf86d13bc1640d4e508dc4d20017245cd1d000101d0404cd3f6f28e109100000000000000000007500000001a56c05044b46160009c40017b0c8ca78bb5278000000a4c77d16032ca28bc9308918b590e52e87ca6fcaf0c18000086558000ef10dd2f000161c2e15d842918c240ba269c8585d416c0000ec0000002908f834cd6d15e4d97b6934c6875896c00061f0d4160d075160947cf1a8978a2c470aa254d37c000d551380000017c14192a8000c6cced618b100000006bc965130180000e751ad79a5640002807c05d2a69460d6153559524975c00160e0fc76845955848cd354ba000f9c3dc00033897cc580005515b460c1e8ae545c0006741a0a18026ea8000870b695dc00043cf000000000005314c0562169644efc65cae00016b817c0000000010213560008b02ad50ce80ed319156493c4902eccb05b4000e86000000e8815c0c861130c468f4800000000173d4ec4d466115458e02c56f0840ad5610787ac3b05be000f1010139cce83c000000851200000019c20d1e4ed44f411c4480003070e200136aa909851661b4b79359439218318000000bd
  | 13 => 0x1c5245ac1545f0bad7213350e607e0000009c88c904c2180015b80700003d80017287d815200062800d7945a64b0e855ec6b95104e8ee4f94000d9c000494302ca013579cedc9b4cd110082470865498c4c9778ff90550d0d714106f165cb351804c123d1242087783ec86c6300bc3a610548ef5862400091c4bf4215f00003a81f0ba6ec080d5c00004a4000b254b6210e7cd8e13d48d6e4000d74000000000ccd200dc05c4000b445f90103cc0d07f95c8a9cd252d92c09fd0b88bd4b499d7d063c330bde36f6d82757012eebe8ecccc0c98810001364e304acbf17411c96881fc2c6b98d48c4123963946c8e0904295674f2cac1538ac475c3b88010481bebe000140c6d2799258d3943404460870092109534c278c0ccc56a0000a2552d4c4d04ac833ee48d08a7004c0c5324ff048813154c4f8340ab32d118873d34200032a474fb90ad548b9d5416dc0487d0064ea55740000000001c8e8b2f40013e4000000ea13c4b001dc68447c08888d19c26c364928dc95fc00138c0003980000000000000000010743e07ed5e4d5c320aec5176255ad04432f5e8000000000a7c0017aa0016d17d86d6370dd911100d630b7c70483d6b4ab54d06e8fec6c51e908cd022d942c108b5d5780010ec3ac41d7a40000017551bc3586503c7000b5a54e0b5484db950450051b65095446c87ca85588d589ecdf14e0e153b12a50e0b2c6ed1753f92b40a0c1c85d0a00352656d5668a6f70c580da4545009360834d30ef2552000ddc9f83b559c9f172cb40db040ca51150190740024000000e212c4000000ae84240000006b40016f005c000e9005312ec38a1d37072c125761500e1c6382fd03c8fd4594b20017c95440000011ec6e0ce53f07b0b094362f85ecc00b742f49507609dcbaf0309f4e793fcf2039e3101111990596bc7aa2c40180017883f567110ac20d8d5e07448200000000000006200010d36ed7d6000334000756e94fc91f4362bd92b8db50053b44fe00125cc857517706e4900bbd298fd8734a60000194738c34000cc957cb4cfd52e6356b88f400315d4d880014748a07d4c61284a08e6527558c52c3a0ba85c68e2dc4d10e6c5df20928c31c000938bf8b80bc0000001454ba15213d000156c000fe51843441140000005c04dd1d48f477437c0012e13a922a0400141f80001c0001380000fdd156fc038800122562880400045c606390c28090000000000a40000f6800064534400085135d3e16e00000002e8e016802055a87e8666e04120145758f1c41876cebc4086973a52307205aee5c5f24997480000017980016083d5038de80e48647dc70c6f4b66569404b6095cd991350b5288bdcab940000e01cd900014492a0228e185f45e55f466a5d068c59c5986ad584f09490480f507fc8b53900001f4e34df971964d4e4da8614975
  | 14 => 0xd1404e748a003e23d024cb6d06105c988b841e00512b0a0c2b8924faaa64ce0e3d51909d4657aced02bccd453c6912fc742854a9839cded7b54704a05209485bc9e6cb4d681df61494c3b26524ec0001cc66c38c39a0005d92050bef646f89445a9494000ca400149ca5cb20d84e606044d09ea00000155d4d8000508001108238001114001290000be511203c830ff4f6d3291b42b50c4a8c010c7d1c01d4aab4800a40007c6f447272c8000f60000cdc000f78378000a114bd118000000d192444400000014f8000000a056580002310b062c1b15080f97c4a74add1640007bc268000000fa042c9980000007887c4534000000de400170551526c00000013800000021430081cb62000000b395c433ca300007540004e00000000b8ab0381069488b1c00000000000064cdbc9ac000000000728000f98a55699768000000bccc044a8054ac2790431090328000000000af4000000000fb4dccef8c4c0813c87f02353cc0016fc5753b85cecf062a000fbc000000a589a0c440007b4000e28454f385b15545148cc1855a47702f07c87a1194e8c000538ad9530794000000a952ea0000002c8ba42cc00091400078c0000014a00008448290dad8114076467cf300001b84794f57cb3490e83840e0dd50249414405a4122028730c9cc2d32cfb07cc000ee13385189d8b94d6eb9210c00127c0014154e88780000b0990aa8000874e98f72aad24c36c71cd2d4c8908405498d7ce70f4d1b8a49694a884b800000071427c00114444400078006ad78000000000cbcec872551c5712686a51f86c8c6405a0cd4b09c055c33a60f06e0015801bd1dd6548142492807e067966d128c24becca8b1e30c12c50d3d8634718284dd029c304698f8c8a81a80001acd509b9304224f856a400027000022cf240000002b07236f915d14c1194251f057c0688ac438157088eecbb0ef4fd0e2c6a1648510d946125788c0f3d4a94cd29c4f0e246481962a00213192104fceac9689d09a51c513c3617740387a9634b28bfcb510f45aa60030916272b2f84f767c49d3980007a53e8f746e707e7f4cd941c000c50f0c1994d4374f5c0004c50c00012292ace55080b56a1400000000143ce0c0017380000000dd2e400116845129544400051ef8800019b1487e4000000000710000bd4d442896c8b1578d1b1314a342980000231714791e0000149220980000001450e69098dfceb44600005dc4c240009d73102caa45600c059274c1400785568381742208083f89ccffc5412354b93c05c8e08c100011
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x9d00000550a32630000020000006280000090000041479b5000f9822347220c40b964c1001d0094008007001e1200d00000038b245001900000008300040010c1828208380150d9210d751894300523648435d46250ceb88c8210d75189433ad07a4e435d46250c0144d9210d75189433ad07e48435d46250cebc0e9210d75189433ad07648435d46250c01c0d9210d751894300503648435d46250cebc0c8210d751894300507a44435d46250cebc0c2110d751894300507640435d46250cebc0f2010d751894300507250315d46250c0141c94cc175189430070310d75d486250c0181e646147250e310052365032dc9608c40109d9810f7650e210064310d851c9438840106d989947250e210070310e651c9438840105d97a146418d210048766275190634840181d8510c7650d2100523648431d9434840181c646147250d3000523650325c8614c00181d8510f7650e200052364843dd943880014959418c7158d2000515654321c56348001495940c87158d2000427660431d9434800190c436147250d200041b660651c94348001c0c431947250d2000531245631c943480014999010c7650d10
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x5000e9600000010a08000100800180302c00006009032859210d751894300481f40c9086ba8c4a180240da2250315d46250c0120cd012818aea312860090368894cc1751894300501b453230a392871880280ea610d851c94388401806cc087328e4a1c4200c036159210c7650d2100501b443230a392869800300d8564843dd94388001406d3086c28e4a1a4000c03660431947250d20
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4804b1698436147250d20
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4c
  | 5 => 0x4e
  | 6 => 0x138e
  | 7 => 0x94c
  | 8 => 0x94e
  | 9 => 0x124c
  | 10 => 0x124e
  | 11 => 0x138c
  | 12 => 0x3
  | 13 => 0x8c
  | 14 => 0x8e
  | 15 => 0x150e
  | 16 => 0x98c
  | 17 => 0x98e
  | 18 => 0x128c
  | 19 => 0x128e
  | 20 => 0x150c
  | 21 => 0x9cd
  | 22 => 0x9ce
  | 23 => 0x5
  | 24 => 0x12cd
  | 25 => 0x12ce
  | 26 => 0x20c
  | 27 => 0x20e
  | 28 => 0x140e
  | 29 => 0x154e
  | 30 => 0xb0c
  | 31 => 0xb0e
  | 32 => 0x140c
  | 33 => 0x154c
  | 34 => 0xb4d
  | 35 => 0xb4e
  | 36 => 0x144d
  | 37 => 0x144e
  | 38 => 0xccd
  | 39 => 0xcce
  | 40 => 0x15cd
  | 41 => 0x15ce
  | 42 => 0xe8e
  | 43 => 0x95396
  | 44 => 0x94056
  | 45 => 0x4d
  | 46 => 0x138956
  | 47 => 0x94d
  | 48 => 0x209
  | 49 => 0x1409
  | 50 => 0x249
  | 51 => 0x1449
  | 52 => 0x14c9
  | 53 => 0x124d
  | 54 => 0x138d
  | 55 => 0x98096
  | 56 => 0x20096
  | 57 => 0xb1516
  | 58 => 0x140096
  | 59 => 0x8d
  | 60 => 0x150996
  | 61 => 0x99556
  | 62 => 0xb0996
  | 63 => 0x98b16
  | 64 => 0x154996
  | 65 => 0x98d
  | 66 => 0x1649
  | 67 => 0x151296
  | 68 => 0x21296
  | 69 => 0x141296
  | 70 => 0x128d
  | 71 => 0x150b16
  | 72 => 0x151556
  | 73 => 0x150d
  | 74 => 0xa0c
  | 75 => 0x9cb56
  | 76 => 0x9d5d6
  | 77 => 0x160c
  | 78 => 0x9ce96
  | 79 => 0x180c
  | 80 => 0x130c
  | 81 => 0x1452d6
  | 82 => 0xb0216
  | 83 => 0xb1416
  | 84 => 0x20b16
  | 85 => 0x140216
  | 86 => 0x141556
  | 87 => 0x21556
  | 88 => 0x20d
  | 89 => 0x140b16
  | 90 => 0xb0d
  | 91 => 0x155416
  | 92 => 0x140d
  | 93 => 0x154d
  | 94 => 0x144b56
  | 95 => 0xb8c
  | 96 => 0x28c
  | 97 => 0x184c
  | 98 => 0x148c
  | 99 => 0x1455d6
  | 100 => 0x144e96
  | 101 => 0xcd5d6
  | 102 => 0xd0c
  | 103 => 0x40c
  | 104 => 0xcce96
  | 105 => 0x188c
  | 106 => 0x10c
  | 107 => 0x16cd
  | 108 => 0x4956
  | 109 => 0x5516
  | 110 => 0x24211
  | 111 => 0x449
  | 112 => 0x40994
  | 113 => 0xecd
  | 114 => 0x3cd
  | 115 => 0x1489
  | 116 => 0x41414
  | 117 => 0x58b
  | 118 => 0x3ccd5
  | 119 => 0x41a14
  | 120 => 0x1a0414
  | 121 => 0xd0414
  | 122 => 0x3d5d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 1346
  | 6 => 3551
  | 5 => 1527
  | 4 => 41
  | 3 => 13
  | 2 => 1
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
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (56606+((h/567+packedAt gbK7 (49802+(h % 567)*12) 12) % 2719)*12) 12
  | 6 => packedAt gbK6 (188414+((h/1382+packedAt gbK6 (170448+(h % 1382)*13) 13) % 5474)*13) 13
  | 5 => packedAt gbK5 (97041+((h/579+packedAt gbK5 (90093+(h % 579)*12) 12) % 2085)*12) 12
  | 4 => packedAt gbK4 (2961+((h/13+packedAt gbK4 (2870+(h % 13)*7) 7) % 66)*7) 7
  | 3 => packedAt gbK3 (1073+((h/4+packedAt gbK3 (1053+(h % 4)*5) 5) % 28)*5) 5
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff01ffe01f03fffc0fffffd19e78fb81f1ff
  | 1 => 0x7c03fe03fffffc0ffff03fffee69a724fe3e3f
  | 2 => 0x8003fffc001ffff07fffc1c03071c7c70fcfcc
  | 3 => 0x3ffffffe000007ffffe003f81f807f00ff0
  | 4 => 0x3ffffffffffff800000003ffe0007fff000
  | 5 => 0xfffc000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8439002ca10500949402524a8082084980d0d5
  | 1 => 0x684016014c2a4409291024b50628a32036262a
  | 2 => 0x8aab540213ab204eac8101b05145c60b4b4c
  | 3 => 0x2113cd9a7740218473cf38063b81f807d00db0
  | 4 => 0x4223f1e39b9cf3ce008610183dfe0007edb000
  | 5 => 0x73c081001c00c208030820203f7df6b0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36731
namespace PEqualNP.Outside.L_meta_36731
open PEqualNP.Outside.L_meta_36731.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
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
  · exact alls3_2 i (by omega) hi
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 13 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 41 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1504 : Interval gbAtlas 5 1504 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1527 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))))))
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
theorem bgb_6_3520 : Interval gbAtlas 6 3520 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3551 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)))) (concat (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)))))) (concat (concat (concat (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624))))) (concat (concat (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)))) (concat (concat (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)))))))
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
theorem bgb_7_1344 : Interval gbAtlas 7 1344 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1346 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992)))) (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152))) (concat (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248)) (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888eeeaeaeaece8e888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 3974686856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36731.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,2]⟩,⟨.or,[4,5]⟩,⟨.or,[2,4]⟩,⟨.and,[3,8]⟩,⟨.and,[2,7]⟩,⟨.or,[1,5]⟩,⟨.or,[9,10]⟩,⟨.or,[1,6]⟩,⟨.and,[12,13]⟩,⟨.and,[0,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3974686856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3974686856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36731

open PEqualNP.Outside.L_meta_36731 in
theorem PEqualNP.Outside.L_meta_36731 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3974686856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3974686856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
