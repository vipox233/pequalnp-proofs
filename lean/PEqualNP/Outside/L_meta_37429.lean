import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37429.Model
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


end PEqualNP.Outside.L_meta_37429.Model

namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
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

def SBf (j : Nat) : Nat := [3, 6, 6, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37429

namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
def s0K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (5+((h/1+packedAt s0K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 4 => 0x6ff0ffe0f8
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffff81222d295b
  | 2 => 0xffffffffffffffffffffffffffff82445652ad
  | 3 => 0x24e89b1cc6
  | 4 => 0x188ee398f0
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 30 s0Pos s0Neg, 0xc0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37429
namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa80258004180ec42406014088000df31f631dd31f531d531be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x6900000308e8204a000412aaa718d514131ca98c819531102aaa218714c620e298841a840082aea7085554c10
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x420290604c440b018131083813110020
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 10
  | 2 => 3
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
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (228+((h/4+packedAt s1K4 (208+(h % 4)*5) 5) % 22)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 15)*5) 5
  | 2 => packedAt s1K2 (116+((h/1+packedAt s1K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f807f807fff00fff80fe07f07ffc0fec47c7
  | 3 => 0xfc0007fff807ffffffff0007ff81fffff078ff
  | 4 => 0xfffff8000007fff00ffffff80001fff03f80f8
  | 5 => 0xfffffffffff800000ffffffffffe00003fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2408304850501121208b1628b08a2c92459b5b
  | 2 => 0x615552d534a328ea47c0aaa5546d558eac45c5
  | 3 => 0x4b46a4a4a5354a4c8b5581066d219b2d3068ae
  | 4 => 0x7264c6c6c6c68c88ede6cdb40849e3c63e80f0
  | 5 => 0x8387070707070f0f0e78f1c78e7102083b7600
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000aaaaaaa0aa00a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37429
namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
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
end PEqualNP.Outside.L_meta_37429
namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2516440000000aa800282190a800260e0c4212424d000000f23524c7013000000007c3001850ba21e9cb1b00715003a0868048ac8000000004050300b141102043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x179206a6059a9f282c8a2100259f8c80290d8ea416872c1108a5140003020f06078b2b90a88000800000011d80000f8005208018ad041992aa1700001b1600102d8d00180291951c8e268901a79d2300049c1ba48015a70023a299098a938c0020221a2b1e131e94a9aaa1800b880381000c044000a30000260000e06340072e1c50102004012604008b7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20e0a4c08620a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
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
  | 3 => packedAt s3K3 (312+((h/2+packedAt s3K3 (304+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 1 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 2 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x84882808c489082016514a284a212954133615
  | 1 => 0x11245191091260c580a4148694c652a8c888ea
  | 2 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaa8a8c8c88888eaeaa8a8c8c88888eaeaa8a8c8c88888eaeaa8a8c8c88888eaeaa8a8c8c88888eaeaa8a8c8c88888eaeaa8a8c8c88888eaeaa8a8c8c88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37429
namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x920018000285c0003e3000b003c01b4eac01d0434000484140a389400000200112aa4d16001150500981980e811a20084c893c000131c3c0100044040004000003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c61bf418c37a8318778c630ee18c617e508c37c81186f10230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a61f7514c2eea2985f14530fa28a6174514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea9061de320c3b864185f94430bea8861bf410c37a8218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c41bf418837a83107b88620f610c417e508837c81106f10220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2907dd4520bba8a417c51483e8a2905d14520dfa0a41bd41483de42907b48520df20241bc40483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef32083d864105f94420bea8841bf410837a82107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c437c81886f10310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21bf418437a83087dcc610fa18c21f721843e843085f94210df20421bc40843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd414437c80886f10110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea0821f731043e862087dc8410fa108217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef19663dc32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31f7294636e528c6faa518fb54a31b6a94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7bc6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87de6590fb0cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53887bca710d794e21bea9c43dd53886baa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f799243ec324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40bf296817d52d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539037aa7206f14e40dfa9481be529037aa5206f14a40df99481be329037a65206f0ca40dfa8c81be519037aa3204f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a05f14d40bfa92817c52502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206fd0c40df21881bd431037886205f94840bea9081bf421037c84206f50840de210817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10
  | 2 => 0x4000020060200040101200c000000000000080200a02e0340101600000c0080f00e00401812004000000000060000100400200000004006018000000000040000200200802013000068098020020280080c01a0040200203e02c0380000000000000000000008050000300180f002004010020020380100e0080080980000204c0000b03c03800001002000008000120000201e00a00c0280000000000008000014028010080000201600c0180200d01e0000000a0040280900b00801c000070140280080000000c0000100c0040080000006000007000000040000020000a80000600000000010004000000060940280600e018008050000140100002a0100000100000c0200101a000040010040040880006e00005008026004018070040180080000c0000600100200c03000008000000020000000001200600c00000002068048040020100100900001813001002038000030000080000100200002000006004008080000000380a00600401df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997bd0b32f6216657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cbbe86197710c32bf29065ef420cbd8841977cc832f719065dd320cbda6419734c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83b
  | 3 => 0xe72c2640002954060013f2d60001a4d32ef20e0017d0a30005d95798c5bc134e10090000010906d51ac5c000c6142000000ea05e6842318e5f679000000000bc0000ce000ba00000047a330bf000000000650df0000200022b3eeb80c92430000000000052c0001a17d3baaa8c88003e20a91880000000000057000b18000000001c8010fb000a1c140001f2000000002864912925c23a000f9122000b48801ee0a20018780006656521000140000260ef000000000003b4370d1800524b25610000007300000007a030002882620004e9fa3f0114d10000004b4002270000c09d800000994450000000016f8000003c941000000000000000ce000000f43c00b40f000528a70002ff00000176a890ac9f0259d16308b58719400007437a1957ec689099d000000490004980006f29f2564a40000059a00000000496654c523e0001290aa7a11c44580af100031000141626c0c68147000015658fa090000000000006680009800052c60206000000c48804709ec0018f000b44000000000009a09a00000000000000000000000000000012600000000104000c516e000000408ba19c608658001b117a0012520b000a2d240b12980000010a1b2bf82700014ea78002e41589909f1b4454895269f60008b80017100000000000000000001c7070215312670000000011e28ca980000016042c2e800000038e50006228888a205514468398e70b09dc78000568a8cf30123020accb8000006bd82aa16006a0000ec000001180000003a41aa51000001432a5404594979b9308600000a500c0006900003e0000000011811c00000000000f80000000000b9100220d98a800000000a1000290000001cd3e69b4558001c6b3d23800000c2c002ec000000000000004f55c8b90005d400000408000d204f316ab929aac0266ccf78000529c411249178278fe302000b5000000272154549d4508590db00027ec7c00000000a382e0e2040000001936325984996700083d74a231a80c50e1ac030000e22a9000000bb8f60be0008680000000112000000000e996d18a168002e1000000a28ff0026a86b887520420cda075b2acd3502300000000000518000000d50a0001318401285017a00048caf00010145e000e92350fa8cc000960422bc0013c000b5d5e8000001e10bb0c29a0dc479c5378904170e01760005927416e0002f01a2609a0ab9d7624271140000001883e000226000290003da7008b0240b24d9510c161a20ce0ab05486c0afa3a1f0000dd1ff30a3218411f43a000000002e00000006049c0000000035258896117174b0078ac143e34d799331acbdc9d25611a2d8a4ab500077c001f436e538d6875458a5d5c2f92a67ec9c2ad5565100d8ad0821e86697a0003f05106812000127a260001dc0000000096c002341a2000f109b4b400013000
  | 4 => 0x11b0000001c8c24b20008629b26400139800000394af232532b28e5800000b40c11a00005580006a5f84a07699839c2a07080022a000ec0000003245527516aa4c000000008600016b0003cd37ace4ae0640020c4c29e45a00000000000000000000000000005508c0710000004f800376000002502b000081a76240aa0000000007700b00f24a439099790002251089100022c1917c1c8528b42091fa0015d1fe33ebc8bda40000880cf0000001eceb270186b94a8b2000e47184800000000000003b29c8d2a9a08633c3f00046e290ea8db0007f566000000000221e8000000de9c6000000770004d68683716a00016cf0a914720018d9090a8000002f8000c28f522904a040b98004020004b8da2ba84147923364218001e914c4a92e80000018c9b9ae0d8af8bfa981d6910138bf132ac84408236a0f0df95a60e9fcb1ab748ac700031d4cc001088e84f05e0dc0794fa0000e1875002b8000003d8000faa9d20a978a800b2d8951719f95a60015d9de02a73c6582c07e69d348000a62cc020002b649c000004b0828002002e4254001e30e800163ac529ea80000425ea8f0aaaa75fa79c000493b65a575a8301a1858f1c821e5712fac31029b8638b831a8d97703a1fcad8b02da60cb746e9990e05489721650a6f8c426c1ea2f90d8d80fe70d1f86b428190b7a601ee838c32ea502b547300026ab60f59e54760290683b590820422e200000000000000000830005cc9543b066620c580196e2244640a000356bd9621d0000b6d0f1830000000003e000000001c90caac4002
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc404831c5310120cdd4440483345110120d314e204836451881209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209b594320834d530c8208f992510823d6494420cd94541083355150420ae181410826d6588420b398e210826f6548020b318d20082e461480209ed95200823e64d4f108f59353c426e62d4f109b58b53c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c433561d5210ce98354843356115210ce980548423e6494e108f592538423f6454e108f191538426f6254e109b189538423e6494a108f592528423f6454a108f191528425f6354a109718d52842ba60d0610ae18141842b56190210ad584408423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414423e6590110c7d4e404431c5390110cbd4a404432c52901108f994404431f5310110c714c404432f5210110cb14840443545384110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410435553cc4109d594310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400427965840109dd9510042d46344010b918910043b040440109ed9510043b34144010
  | 1 => 0x2ba60d4440a798c511029d6314440ab98851102ad6214440ae980511023e658c4408f59631102ae628c440ab58a3110335518c440cd54531102bb604c440ae181311023e650c4408f594311023e65884408f596211029e6388440a758e21103355188440cd54521102bb6048440ae181211023e65084408f594211033a60940408f58654cc23f61553308f99251cc23d64947309b98a51cc26d62947308fd9741cc23d65d07308fd9541cc23d6550730ae18141cc26e62d52309b58b548c23e6494a308f592528c23e64946308f592518c2ce628c6308f587544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c23d6115130cbd53524c32c54d4930cbd50524c32c5414930cdd53514c33454d4530d9d4b514c36452d4530cdd93514c33464d45308f990514c23d6414530cdd50514c3345414530d9d48514c3645214530cd990514c33564145308f997414c23c65d0530cbd4b414c32c52d0530cdd47414c33451d05308f995414c23c6550530cbd49414c32c5250530cdd45414c334515053097997314c34c52cc530d5147314c34c524c530d5145314c23e6590130cbd4a404c32c5290130cdd46404c33451901308f994404c32f5210130cb148404c3375110130cd144404c34c528c130d5146304c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c25d658c430b398a310c25f654c030b3189300c2d4614c0309ed95300c23d61953208fd8554c823e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c823e64947208f59251c825e63947209758e51c823f65d07208f59741c823f65507208f59541c82b860507209798f548825d63d52208f993538823d64d4e208f992538823d6494e20d3d4c328823e64946208f59251882ce63886208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f514833764d4520cd193514823e64145208f59051483375414520cd15051483575314520d514c51483366414520cd590514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414826e65c8520d314f214836451c8520d314d214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4
  | 2 => 0x5214941ad98732506b561cc941ad98632506b5618c9418fd95325063c654c9418f994325063d650c941e34c8325069f6354141a718d50506af6254141ab189505063f65504419dd95411073654504419b98854cc66d62153318fd9152cc63c6454b31d354832cc63f64543318f19150cc66e62d52319b58b548c63e60952318f181548c66e62152319b588548c72e5494a31cb552528c72e5454a31cb551528c72e52d0631cb54b418c72e5250631cb549418c74e52cc6318fd91508c63c64542319bd89544c66c62551319ed81544c67860551318f990524c63d6414931b5986324c6ce628c5318f993504c63d64d41318f596540c63e60950318f181540c63e64150318f992510c63d64944318f597410c63f655043197d95310c795414c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c874d530cb218fd9150c863c64543219798f548865d63d52218f982548863c60552219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e21c794f418871d53d0621c794d418871d5350621d394f218863f64542218f191508865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534866e65cc921b9987324874d530c921b398e214863e64d41218f593504863d65950218f982540863c60550218f990540863e64d4c218f593530866e62d4c218f990530863d6414c219e98053086796014c218f992510863d64944219798e510865d63944218f597410863f65504219bd9521087a541484219dd95210863f64540218f191500865f63540219718d500873551d0740c794d43902af6250e40ab189439029f6350a40a718d429032e5250a40cd54541902ae62d4e40ab58b53902ba60d4e40c7d4e53902ba6014e40a798f529029d63d4a40ae983529032f5294a40ae980529023f654ca408f195329023e650ca408f594329038d320ca40ae983519029e6314640a758c51902ae6214640ab58851902ba60146408f996319023d658c640ab98a31902ad628c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d65086408f997415033751505409bd89531026c6254c40abd8943102ac6250c40c754c431025f63548409718d521029f6350840a718d421032d5210840cd547411023d65904408fd95401027b6550040ae98353102af6254c40ab189531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d4840a7d8d521029c6354840a798c521029d6314840cb54852102b66114840ad58452102ba60148408fd95321023c654c8408f994321023d650c840e34c8321
  | 3 => 0xe50005300005b80000048c3c1873080ac6093e0ecba40000051800000001000002020060030000040000100e0240000200200c010030020040000900000000002002000000000000080080000000000000000004000050020200000000600000800016008008020000000000100e04407804008004018010020100480400c0040100201c060008030000240200700e010000120000000480400c0040000200000c0080e00000c0000100000000000000000000060040200000000003c010010220040000000401800800000004010000060000080100400c0100900000c008060020000080301000001008000004000000060000480300001c020010000080080302c00811800000014000030020000180200a00402804002014010010020000780001a0040a801000004038050000040000000400802802002014008100100040180d00200800000000020000020020080180900001c0400100202c0000000600401007000004000010000000000000401c0000000c00000005010014018000040034f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3e64947328f59251cca3f64543328f19150cca7661152329d584548ca3e64946328f592518ca3f64542328f191508ca3d61d51328f983544ca3e649513297d8d544ca6f62551328f994544ca3d61151328f980544cb2c54cc932c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540cb2c62550328fd85540ca3c60550328f990540cb1d54d0c3297594430cacd6210c32cb553420cb8f43d08329b594420cacd6310832e310c420cacd638c83297d95320ca9c644c8329bd95320caac644c832b3d95320cb4f654c832e3d91320cace644c832b3191320cb8c644c832a3191320cb8e544c832e3551320cacf614c832b3181320ca3e64944328f592510ca3f64540328f191500ca7761540329d185500ca6f6254f419b18953d06af6250f41ab18943d071d5310f4197d8d52d065c6354b41a7d8d42d069c6350b41cb54842d06b561d4f41abd8953d06ac6254f41c754c53d06ae6214f41ab58853d06b56114f41ad58752d069f6354b41a718d52d069e6314b41a758c52d072d5214b41ad58452d063f654cb418f19532d063e650cb418f59432d078d320cb41a798f50d069d63d4341ab98b50d06ad62d4341c714d43506af6250d41ab189435069f6350941a718d425072c5250941ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525072d
  | 4 => 0xf0302451545bc0000000004c0000019a52897a52124a213b0a30009e4000001640000029419e0000019b6067b09718c5a25e0000000009c0002fc2dc72d2690212a1e4f021f39aa2c2088d2088d0aa309354abc1283600000063115000538000ad2bc6bc4da6a0004d02f09a0444e80028008437c62a8d42a000d92ef0a4a845c2f40fa46d301fd4ea001270691bc4f42e9a10000000019e000348002b01a678441a1b1486ccd2ab64962211496d0f822509800000000931b5000969388000003c800000066000e227f00000088800000184c18000000001900000000000000000a58dc8005b00005e0991ea32c720004ca3b8c1000532574000f10005c000000000324000005260700000007e000000000000012a00009c47c00000000001379c84ba7dc328005560000015335a6dc7624147637000000000648c0163000000218f85c66695e2490006b017117254b795d122000000060006160013d80029a05c000e93780009c1851b27a8fc0eb57e6ac6d95b22c00000000000308ea91300011000175252864512fd00073c002a70002000e91828a0000000047c63c4381a32a78c3f9ae000000c88b5000000000730000017300057089ca11fc06eb9c0d8b65f45687b9730008a03f0ab2060006200015800000084444001770551a0000ef800000000000001742ec298001144c4310003c89902ca8e5800009b800000000a30000004d88a000032000070003ec000000000001c4000001f80000015c4b80006527407229cd3a7e000629608000000000006b1fe7580000038c244d8b070000005421e20cadd3c1fb0000000000044000000000000000002be37e0000000040e00000000000a716f9d95200540010745a17d490004029540000000000000000068005721a4118000528c800075d8315f56801c0023a3fc1594f800000000c09583765a40014f09e000cb0461b0ba80008b398001012530007c50d22c3b00012b0851aa00000000000001642bd000ac8c680024818cfc9be0000000000b11c6a02699d000000f71640602f4000000000010826c0007a14f0505f6001091b00004c8a08000f45f000000000000faaff31000049a81000001690000001b0000000000a4002ad17c000000000000000000000000000000000001412e5000000001b600098cef0005a6000002720000000020c0000b12609d000834001d20005eca60b00006e948800000c151180000000104809000000000000000000000001a3993d1ff12c00041035552a74c593923a96c14003296c016b000000000001c7014894409dd1661010402f59a8f0929a040a15c000001c63c072999000484000725f000093b0a000a681315250a000002cb37a414000002d8b5c2a19843a0208723200c0002387b2ca478000fb0001a800000000000cfa5f000ba1680000008e0
  | 5 => 0xb3d650005c2588002c94609a16100021209cc3000000000000a64a2988bd0000000010e000000284188ce000000ba0005b8001051eb3e00013e00000074c000002206500011c0008f57a84b0000001f0640cc168b39a95444fc6880015e8009814900065c000004945c8002cc6020005fa11000a5cbe9e5250c10002043b62e4000002fe50050100202a1c000582163e81e9660000b4e01890008ac4b800198000250001e895cf99563da2b83b8004063f80009411e5c424a42346a3d6e8004eeb80fa269152a8c7c800000bb0969595140016700000039c000003446e00022a000b193715709026161979000838002f10000000019057630d27aa84b0001501c152a4b00018e2ee000c984c5f246400000000000000002ec5207b0674fa0002d8c00007e8001334d69ccf780056600000000000480000d71b43a8000005b45a00010842e8cc002860309197696a0eaa2552812448084741121200911090f5fc2c4001b40089996a00000079c6b0d44c2374002350a20016caa65ecbcc0000045cb14000002aa5f9572315aa00162000000900000000008e40011a000c091300000000184000000000000000002d04e000000114000143a282c431da000000000004bc8dc0b000000bc8000000000014d94442c544b083800000000000000000002f00540000001f618000081c934c3b4000003c408d23947000ad40000000000000000000000002183cc000e28005ee044f91501de080b01d439c0ec379350040010a12b47eab1419e9000aa97593b00099c002db0d00003810d5080011b2a4278170b58e0000000709d00dc0000001e28690c1d00f18e001710e2386920850000008180000058e27c0026d000278ce06d0007708600000000000000000940000001e60003a00057283ce122f00a9107eab14b20
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x7cb803aac71a38800321e9c00a02b4f182c0002e2201a8000b0333000000b000110500844b426d9815084061b1a989250050ca310a540000a8131001c18048bdb80020200285001c00000040861200502c18c6312a81948e74991320ca46b88c899065239c0644c832918ed2a2641948c76551320ca86392a621e83431cd5210b41a18e4a98a7a0e0d5358853d068639aa4296838358d5214b41a18ea99065a0e0d654c832d0706298c4a1a838318c5250941a18e4a98a6a0d187054c535068639aa4292834a1c15214941870e0b2864a0d0c754c832506863a2a419663431d1530cb21a18e8a986490d487054c3248707298c4a1c818318e5250a40a1ce5a9ca72050e73d4a5290287baa6419481431c95310c40a18e6a90842050c7254c5310306a9ac4298818554d6114c40a18e6a90a42060d635485210312a92c2290810d5c4654c840a18ea990642060d654c83210312b12a3188818558d5188440a18e8a90641863151181410c2873a6a619441431d1530c820c62a2302821063161983548430c298c0a0a218a1486050510c2aa6b0880086255258440043483188088021a81884044010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x406000000080a00200885811da544c83280c87595320cb41a048254d6114c40a04835496114840905811d5320c84080c87595320c840
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (24564+((h/267+packedAt s4K5 (21627+(h % 267)*11) 11) % 1163)*11) 11
  | 4 => packedAt s4K4 (32538+((h/260+packedAt s4K4 (29678+(h % 260)*11) 11) % 1247)*11) 11
  | 3 => packedAt s4K3 (2870+((h/18+packedAt s4K3 (2744+(h % 18)*7) 7) % 74)*7) 7
  | 2 => packedAt s4K2 (368+((h/2+packedAt s4K2 (360+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 1 => 0xf81ffffe07ffffff81f07c1fffe1ffffa23e3f
  | 2 => 0xffe03ffff80fe0fffe007fe0fffe1e03c3cfcc
  | 3 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x882808c4122400016509421280222a80cd0d5
  | 1 => 0x924519103244986580a4291a53215551a2262a
  | 2 => 0x2149aa2490e909aaaa084f489d54181ac34b4c
  | 3 => 0x859634492481d2d34d3d0210e6998063740db0
  | 5 => 0xc6183871c70e1cfc71ce739c07111183fbb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeaa8eaa8e888e888eaa8eaa8e888e888eaa8eaa8e888e888eaa8eaa8e888e888eaa8eaa8e888e888eaa8eaa8e888e888eaa8eaa8e888e888eaa8eaa8e888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37429
namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
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
end PEqualNP.Outside.L_meta_37429
namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12ac72f000c62800880004a98b0040b0f860060a2e38011807e45f0260dc52a0a2079978e508474a40a768343803a90b927a019805a01b1000d499e76000000001c0b6200d802ac801a11000800112000821204b8000048801428d80017fd5005fe54017f55005fc5401ffd4c03fe5301ff54c03fc53017fd0c03fe43017f50c03fc4301ffd4807fe5201ff54807fc52017fd0805fe42017f50805fc4200ffcc801fe32007f4c803fc3201ffd44077f5101ff94407fd51005f54407fc51017fd0405fe41017f50405fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc2101ffd4007fe50005f94007fd5001ff140077c50017fd0005fe40017f50005fc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200cdf1951001cf8ca8802fff64440177fb222000efd91100057ec88802ffe64440057f322200bff5911005dfac88802ffc64440057e322200bef1911001578c88802fff5444017ff2a2200bff5511005ff8a888003ff63440017fb1a2000f7d8d10005bec68802bfe63440037f31a2000ff58d10005fac68802bfc63440037e31a2000f718d1000db8c688033ff5344015ff29a200cff54d10057f8a68802fff4344015ff21a200bff50d10057f88688003ff62440017fb122000fbd8910005dec488003fe62440137f3122000ff58910005fac488003fc62440137e3122000fb18910005d8c488033ff5244019ff292200cff54910067f8a48802fff4244017ff212200bff5091005ff8848802bff3244001ff1922000ff4c910057f86488033ff5144019bfa8a2004ff94510067faa2880037d5144009fe28a200bffd0510027fc828802ffd4144009fe20a200affcc510027fc6288003fd3144009fe18a2000ffc8510027fc4288003fd2144009fe10a200cffd4110067fca0880037e5044019fea82200cff14110066f8a08802fff4044017ff202200bff5011005ff8808802bff3044001ff1822000ff4c110057f86088003ff2044001ff1022000ff48110007f84088013ff1044009fd8822000ff84110007ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013be64040055f3202004ff59010035fac808013bd64040015eb202004ff19010025f8c80801bff540400dff2a02006ff55010037f8a808013ff63040097fb182004ff98c1000dfcc608013de63040036f3182004ff58c10005fac608013dd63040016eb182004ff18c10025f8c60801fff530400bff2982007ff54c1002ff8a60801bff430400bff2182006ff50c1002ff88608013ff62040097fb102004ff9881004dfcc408013ee6204001773102004ff58810005fac408013ed620400176b102004ff18810025f8c40801fff520400fff2902007ff5481003ff8a40801bff420400dff2102006ff50810037f88408017ff3204001ff1902000ff4c81002ff86408012fe6104009ffa882004dfd4410027fca208013fd5104009bea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208003f72104009ff1082004ff48410027f84208013f421040117f3002007ffd401003ffca0080037e500400ffea802007ff1401003ef8a00801bff400400dff2002006ff50010037f88008017ff3004001ff1802000ff4c01002ff86008003ff2004001ff1002000ff48010007f84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0xffd4008027fe2004012ffcc020007fc6010003fd3008025fe1804009ffc802004fde4010027fe2008013fd1004009ff48020007da4010027f92008009ffb2e2004bfd9710027fccb8800efe65c4009bf32e20039f99710027facb88046fd65c4009beb2e20009f59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262010bf59310027f8c988012fc64c4021ffaa62010ff95310087faa988043fc54c4009ffb1e2004bfd8f10027fcc788006fe63c4009feb1e2000bf58f10027f8c788012fc63c4023ffa9e200fff94f1008ffaa78803ffc53c4021ffa1e200fff90f10087fa878803ffc43c4009ffb162004bfd8b10027fcc588026fe62c4009feb162000bf58b10027f8c588012fc62c4023ffa962011ff94b1008ffaa588047fc52c4021ffa162010ff90b10087fa8588043fc42c401fff9962000ff8cb10007fa658803ffc32c4009ffa8e2004dfd4710027fca388013fd51c4009bea8e2004ff14710027fe8388013fe41c4009fea0e2004ff10710027fe6388013fe31c4009fe98e2004ff0c710027fe4388013fe21c4009fe90e2004ff0871008ffea188047fe50c4001bf2862011ff5431008ff8a1880477c50c4021ffa062010ff90310087fa8188043fc40c401fff9862000ff8c310007fa618803ffc30c4001ff9062000ff88310007fa4188003fc20c401dffb2c200ebfd9610006fecb080027f658401dff32c2003bf99610077facb0803afd658401dfe32c2003bf19610076f8cb0800e7c6584011ffb242008bfd9210047fcc90800afe6484011feb242008bf59210047f8c90800afc6484011ffaa42008ff95210047faa908023fc5484001ffb1c2000bfd8e1006ffcc708006fe6384001feb1c2000bf58e1006ff8c708006fc638401dffa9c200dff94e10077faa708037fc5384011ffa1c200dff90e10047fa8708037fc4384001ffb142000bfd8a10007fcc508026fe6284001feb142000bf58a10007f8c508026fc628401dffa94200eff94a10077faa50803bfc5284011ffa142008ff90a10047fa8508023fc428401bff9942000ff8ca10007fa6508037fc32840177eb0c200effd4610076fea308013fe518401dfea8c2000df54610027f8a308023ff4184009ff20c2008ff50610027f88308037ff3184009ff18c2000ff4c610027f86308003ff2184001fb90c2004ff88610007fa4308013fc2184001fa10c2004bf98210077fea10803bfe5084001bf284200eff54210077f8a10803b7c5084011ffa042008ff90210047fa8108023fc408401bff9842000ff8c210007fa6108037fc3084001ff9042000ff88210007fa4108003fc2084009ff8842000fdc4210027f62108033ff65440197fb2a2000dfd9510004feca88033fe65440077f32a200cff59510065faca88033fc65440077e3
  | 2 => 0x20007fc4310003ee2188001fe90c4009ff08620007d84310026fe6088035ffa84401aff94220006fca11006bfd5088035fe284401adf142200affe8110057fe408802bfea044015ff102200cffe6110003fe3088001fe9844019ff0c22004ffe4110003ef2088013fd9044018ffd95200c5feca900037f65480013fb2a4018ff9952001dfcca90063fd65480317eb2a4018ff1952001df8ca900637c65480073e32a4017ffd91200bdfec890003bf64480015fb224017ff99120015fcc89005ffd644802f7eb224017ff19120015f8c89005fbc64480055e3224017ffd51200bffca89005ffd544802ffe2a24000ffd8d20005fec690003df63480016fb1a4016ff98d2000dfcc690003fd63480017eb1a4016ff18d2000df8c690003dc63480036e31a4018ffd4d200b7fca690063fd534802dfe29a4017ffd0d200b7fc869005ffd434802dfe21a4018ffd492004ffca490063fd5248013fe2924017ffd092004ffc849005fee424802ffea124017fb5092004ff8849005bff3248013ff1924000ff4c92004ff86490003ff61480017fb0a4000fdd8520005eec290003fe6148001feb0a4000ff18520025f8c290003f461480017a30a4018ffd45200c6fea290063fe5148031fea8a4000df545200c7f8a29005fff414802fff20a4017ff505200bff8829005bff3148001ff18a4000ff4c5200b7f86290027ff2148001f790a4000ff88520007fa4290003ed2148013fe10a4018ffd41200c7fca0900037e5048031fea824018ff141200c6f8a09005fff404802fff2024017ff501200bff8809005bff3048001ff1824000ff4c1200b7f86090027ff2048013fd9024000ff88120007dc4090027ff65080137fb284009ff9942001dfcca10027fd65080297eb284009ff1942004df8ca10027ff64080137fb204009ff99020015fcc810027be64080055f3204009ff5902009dfac810027bd64080015eb204009ff1902004df8c81004fff5408027ff2a04013ff5502009ff8a810027ff63080137fb184009ff98c2000dfcc610027fd63080017eb184009ff18c2004df8c610053ff5308025ff2984014ff54c20097f8a61004fff4308025ff2184013ff50c20097f88610026fe6208013ffa904009ff9482004ffaa410027fc5208013ffa104009ff9082004ffa8410027fc4208013ff9904009ff8c82004ffa6410027fc3208013ffb084009ff98420025fcc210027fd61080017eb084009ff184200a7fea2100537f5108029ff2884014ff54420006faa210053fc5108027ffa084013ff9042009ffa821004ffc4108025ff9884000ff8c420007fa621004bfc3108013ff9084009ff88420007dc4210027fd2108013fe1084009fb084200adfcc010053ff5008029ff2804000df940200a7faa010053fc5008029be2804013ffd002009ffc801004
  | 3 => 0xe3126009bf189300fffea49807ffe524c03ffea92601fff149300f7fe849807bfe424c03dfea12601eff1093000ffe6498007fe324c003fe9926001ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298012fc614c03fffa8a601fdfd45300fffca29807ffd514c001bea8a601fff145300f7fe829807bfe414c03dfea0a601eff1053000ffe6298007df314c003ff18a6001ff4c530007ba6298007fc314c001ff90a6000ff88530007fa4298003fc214c0037fb02601fffd41300fffca0980037e504c03ffea82601fff141300fef8a09807bff404c03dff202601eff501300f7f88098007ff304c003fd9826001ff8c130007bc6098007fc304c003ee1826001fe0c13004ffecb90026ff65c8013ff32e4003bf9972004efccb9000e7e65c8013feb2e401dbf5972004efacb900027d65c8013fe32e4009bf1972004ffec990026ff64c8013ff3264002bf9932004ffac990072fd64c8013fe3264009bf193200e7fea990073fe54c8039feaa6401cff1532004ffec790026ff63c8013ff31e4001bf98f2004ffac790002fd63c8013fe31e4009bf18f200effea79006ffe53c803bfea9e401bff14f200e7fe879006ffe43c8039fea1e401bff10f2004ffea590027fe52c8013fea964009ff14b2004ffe8590027fe42c8013f72164009ff50b200e7da8590027fc42c8013ff9964009ff8cb2004ffa6590027fc32c8013ffb0e4009ff98720025fcc390027fd61c80017eb0e4009ff187200effea3900777f51c803bff28e401dff54720006faa390077fc51c8039ffa0e401cff907200e7fa8390073fc41c8037ff98e4000ff8c720007fa639006ffc31c8013ff90e4009fbc872004ffc4390027fd21c8001f690e4009ff087200effea190077fe50c8001bf286401dff543200eff8a1900777c50c8039ffa06401cff903200e7fa8190073fc40c8037ff9864000ff8c320007fa619006ffc30c8035ffb2c401abfd96200d7fccb1000efe6588035feb2c401abf596200d7f8cb1000efc658802bffb244015bfd92200affcc91000afe648802bfeb244015bf592200aff8c91000afc648802bffaa44015ff952200affaa910057fc5488001ffb1c4000bfd8e200cffcc710006fe6388001feb1c4000bf58e200cff8c710006fc6388035ffa9c4019ff94e200d7faa710067fc538802bffa1c4019ff90e200affa8710067fc438802f7eb14401affd4a2004ffca51006bfd5288013fe2944015ffd0a2004ffc8510057fd4288013fe2144019ffcca2004ffc6510003fd3288013fe1944000ffd8620007fcc310012fe6188001feb0c4000bf58620007f8c31006bff5188035bfa8c401aff946200d7faa3100037d5188035fe28c4015ffd06200affc8310057fd418802bfe20c4019ffcc620007fc6310003fd3188033fe18c4009ffc86
  | 4 => 0x827fd3208413fe1904204bf98421027fea2108137f5108409ff2884204ff54421026faa210813fc5108409ffa084204ff90421027fa8210813fc4108409ff9884204ff8c421027fa6210813fc3108409ff9084204fbc8421027fc4210813f62108409fe9084204fb4842104fea4210813ff6008409ff3004200bf98021027fac010802fd6008409fe3004226ffd4021137fca01089bfd500844dfe2804226df1402112ffe8010897fe400844bfea004225ff10021127fe6010893fc3008447bfb24a023df9925011efac92808f7c6494001bfb1ca022df98e50006fac72808b7c6394047bfa1ca022df90e5011efa872808b7c4394001bfb14a000df98a50006fac5280037c6294047bfa14a023df90a5011efa852808f7c4294045bf994a000df8ca50006fa652808b7c3294001bfb0ca000df98650006fac3280027d6194001be30ca023dfd065011efc832808f7d4194047be20ca022dfcc650006fc63280037d3194045be18ca000dfc8650006fc43280037d2194001be10ca003df9825001cfcc12800f7a6094047bfa04a023df9025011efa812808f7c4094045bf984a022df0c25010ffecb18086ff658c043ff32c6003bf9963010ffacb18086fd658c043fe32c6003bf19630107fec918082ff648c041ff3246002bf99230107fac918082fd648c041fe3246002bf19230107fea918083fe548c041feaa46020ff1523000dfac718007ff538c003ff29c6001ff54e3000ff8a718007ff438c003ff21c6001f790e3000ffa8718083dd438c003fe21c6000ffd8a30007fcc518026fe628c001feb146000bf58a30007f8c518087ff528c043ff2946021ff54a3010ff8a518083ff428c041ff2146020ff50a30107f88518007ff328c003ff1946000f78ca3000ffa6518007fc328c003ee1946000ffd8630007fcc318012fe618c001feb0c6000bf58630007f8c318087ff518c043bfa8c6021ff9463010ffaa3180037d518c043fe28c6020ffd0630107fc8318083fd418c041fe20c6001ffcc63000ffc6318003de318c003fe98c6001ff0c63000fb86318003ff218c001ff10c6000ff48630007f84318006fe608c043ffa846021ff94230006fca118087fd508c043fe2846021df14230107fe8118083fe408c041fea046020ff1023000ffe6118007df308c003fd9846001ff0c23000ff0611807fff654c03f7fb2a6000dfd9530004feca9807ffe654c0077f32a601fff595300fdfaca9807ffc654c0077e32a601fdf1953001cf8ca9807bff644c03d7fb22601eff99130015fcc89807bfd644c03d7eb22601eff19130015f8c89807bff544c03dff2a2601eff551300f7f8a898006ff634c003ffa9a6001ff94d3000ffaa698007fc534c003ffa1a6001ff90d3000ffa8698007fc434c001ffb126000bfd8930007fcc498003fd624c001f
  | 5 => 0x9221025fec910813fe64884057f3244204ef992210157cc910813fd64884577eb244204ef592210057ac910813fc64884097e324422bffd522115ffca9108affd5488457fe2a44204ffd8e21025fec710813fe63884037f31c4204f798e2100dbcc710813fd63884017eb1c4204f758e21005bac710813fc63884097e31c422cffd4e21157fca7108b3fd5388455fe29c422bffd0e21157fc87108affd4388455fe21c4228bf58a21167fea510827fe5288459fea944209ff14a2115ffe8510827fe4288457f7214422bff50a2115fda8510827fc4288455ff9944209ff8ca21007fa6510827fc32884097f30c4204ffd4621026fea310813fe5188409fea8c4204df54621027f8a310813ff4188409ff20c4204ff50621027f88310813ff3188409ff18c4204ff4c621027f86310813ff2188409f790c4209fdc8621027fec110813fe60884017f3044204ff58221005fac110813fc6088459ffa84422cff94221167faa1108b3fc5088459be284422bffd022115ffc81108affd4088457fe204422affcc221157f861108a7ff65484537fb2a4229ff9952101dfcca908a7fd65484537eb2a4229ff1952101df8ca908a3ff64484517fb224228ff99121015fcc8908a3fd64484517eb224228ff19121015f8c8908a3ff5448451ff2a24228ff55121147f8a890803ff63484017fb1a4227ff98d2100dfcc690803fd63484017eb1a4227ff18d2100df8c6908a7ff534844fff29a4229ff54d2113ff8a6908a3ff434844fff21a4228ff50d2113ff886908a7ff5248413ff2924229ff5492104ff8a4908a3ff4248413ff2124228ff5092104ff8849089fff3248413ff1924200ff4c92104ff864908a7ff5148453bfa8a4204ff9452114ffaa2908037d5148409fe28a4228ffd0521027fc82908a3fd4148409fe20a4227ffcc521027fc6290803fd3148409fe18a4209ffc852104fee4290813fe2148409f710a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c0908a7ff5048453ff2824229ff5412114ff8a0908a77c5048451ffa024228ff90121147fa80908a3fc404844fff9824227ff0c121027feca10812ff6508409ff3284203bf99421026fcca1080e7e6508409feb284226bf59421026faca108027d6508409fe3284204bf19421027fec810812ff6408409ff3204202bf99021027fac810896fd6408409fe3204204bf1902112ffea810897fe540844bfeaa04225ff15021027fec610812ff6308409ff3184201bf98c21027fac610802fd6308409fe3184204bf18c21137fea610893fe530844dfea984224ff14c2112ffe8610893fe430844bfea184224ff10c2104dfcc410827ff5208413ff2904209ff5482104ff8a410827ff4208413ff2104209fb9082104ffa8410897ed4208413fe2104209ffcc82104ffc6410
  | 6 => 0x5fe2146201ffcca3100ffc6518807fd328c403fe1946204bf98631027fea3188137f518c409ff28c6204ff54631026faa318813fc518c409ffa0c6204ff90631027fa8318813fc418c409ff98c6204f7cc63100fee6318813fc318c409fa18c6204ffd8231027fcc118802fe608c409feb046200bf58231027f8c1188cfff508c467ff2846233ff5423119ff8a1188cf7c508c465ffa046232ff90231197fa81188cbfc408c403ff9846201ff0c23100fb861188c7ff654c4637fb2a6231ff9953101dfcca988c7fd654c4637eb2a6231ff1953101df8ca988c3ff644c4617fb226230ff99131015fcc8988c3fd644c4617eb226230ff19131015f8c8988c3ff544c461ff2a26230ff55131187f8a898812ff634c403ffa9a6201ff94d3100ffaa698807fc534c403ffa1a6201ff90d3100fbc8698807fd434c461eea1a6201ff10d31007fec498802ff624c401ff3126200ff58931007f8c498826fc624c463ffa926231ff9493118ffaa4988c7fc524c461ffa126230ff90931187fa84988c3fc424c403ff9926201ff8c931007bc6498807fd324c403fe1926201f70c93100dfec2988c7ff514c463bfa8a6204ff9453118ffaa2988037d514c409fe28a6230ffd0531027fc82988c3fd414c409fe20a6201ffcc53100fee6298813fe314c409ef18a6204ff0c531027b86298807f4314c401ffb026200bfd8131007fcc098803fd604c401fe3026200bf1813118ffea0988c7fe504c463fea826231ff1413118ef8a0988c3ff404c461ff2026230ff50131187f88098807ff304c403ef9826201ff0c13104ffecb90826ff65c8413ff32e4203bf9972104ffacb908befd65c8413fe32e4209bf1972104ffec990826ff64c8413ff3264202bf9932104f7cc99080abe64c8413feb26422ebf5932104f7ac990802bd64c8413fe3264209bf19321177fea9908bbfe54c845dfeaa6422eff1532104ffec790826ff63c8413ff31e4201bf98f2104ffac790802fd63c8413fe31e4209bf18f2117ffea7908b7fe53c845ffea9e422dff14f21177fe87908b7fe43c845dfea1e422dff10f2104ffea590827fe52c8413fea964209ff14b2104ffe8590827fe42c8413fea164209ff10b2104ffe6590827fe32c8413fe9964209ff0cb2117ffea3908bf7f51c8409ff28e422fff54721006faa390813fc51c845dffa0e4204ff90721177fa8390813fc41c845bff98e4204ff8c721007fa6390813fc31c8413ffb064209ff98321005fcc190827fd60c84017eb064209ff1832117ffea1908bffe50c845ffea86422fff1432117ef8a1908bbff40c845dff206422eff50321177f881908b7ff30c845bfe1864204ffd9621025fecb10813fe65884077f32c4204df9962101cfccb10813fd65884597eb2c4204df59621004facb10813fc65884097e32c4204ffd
  | 7 => 0x19007fd438c803fe21c6409bf98a3204ffea519027fe528c813fea946409ff14a3204ffe8519027fe428c813fea146409ff10a3204ffe6519027df328c803f79946409ff0ca3204fd86519027ff618c813ff30c6404bf9863204ffac319002fd618c813fe30c6439ffd46321cefea3190e7fe518c873fea8c6439ff146321c7fe83190e3fe418c871fea0c6438ff1063200ffe6319007df318c803fe18c6409ffd823204ffcc119002fe608c813feb046400bf5823204ff8c1190e7ff508c873ff2846439ff542321cff8a1190e77c508c871ffa046438ff902321c7fa81190e3fc408c803ff9846401ff0c23200fb861190dfff654c86f7fb2a6437ff9953201dfcca990dffd654c86f7eb2a6437ff1953201df8ca990dbff644c86d7fb226436ff99132015fcc8990dbfd644c86d7eb226436ff19132015f8c8990dbff544c86dff2a26436ff551321b7f8a899026ff634c803ffa9a6401ff94d3200ffaa699007fc534c803ffa1a6401ff90d3200ffa8699007fc434c8037fb126437ffd493204ffca4990dffd524c813fe2926436ffd093204ffc84990dbfd424c813fe2126401ffcc93200fde6499027fe324c813ef1926409ff0c93204fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6404bf185321bffea2990df7f514c86fff28a6437ff545321bff8a2990dbff414c86dff20a6436ff505321b7f88299007ff314c803fe18a6400ffd8132005fec099003fe604c801feb026400ff18132005f8c0990dfff504c86fff2826437ff541321bff8a0990df7c504c86dffa026436ff901321b7fa80990dbfc404c803ff9826401ff0c1321aefec8a88d77e645446bbeb22a235df19151006fec6a88d37e6354401beb1aa234df18d511aefe86a88d37e435446bbea1aa234df10d51006fec4a88037e6254401beb12a200df189511aefe84a88d77e425446bbea12a235df109511a6fe64a88037e3254401be992a234df0c95101efec2a880e7f6154407bbb0aa235dfd0551026fc82a88d77d4154409be20aa234dfcc551026f862a88037f6054401bf302a200df58151006f8c0a88027c605446bbfa02a235df901511aefa80a88d77c4054469bf982a234df0c151027fecb18812ff658c409ff32c6203bf99631026fccb1880e7e658c409feb2c6233bf59631026facb188027d658c409fe32c6204bf19631027fec918812ff648c409ff3246202bf99231027fac9188cafd648c409fe3246204bf19231197fea9188cbfe548c465feaa46232ff1523100dfac718807ff538c403ff29c6201ff54e3100ff8a718807ff438c403ff21c6201ff50e3100ff88718813ff628c409ff3146209bf98a31027fac518802fd628c409fe3146233ffd4a3119ffca5188cffd528c467fe2946232ffd0a31197fc85188cbfd428c46
  | 8 => 0x234802000c01800001800402400000000401800000001005406001400800400000801400002401000002400001002400000802800000000401000400001800001001400003401000800803002001000000c06c0240140380a003804801402800400007400401803800c00c00400c02400800000801005c00000401400400001000801801806c01401c00800000003c00000c06000000800400c02c00008c00000000002000400001004000000401000c02800004805404001c00000000804000000001800002800400004804800001800000002003000002001800000c00000c00800401400400801006c0100140380180000a803c00000800404c00000400000805001800c00400809c01c00800009800803c00001000800001003802002803001400800000002001803c0040440080640140180000000000000000000200000080bc00400000802800004002000402000000401c00000401c04801800c02803401800801400001c05c03001c01c01c00000001800800402806c00000400801000c01c01c01403400400001c00800400002001c00402400801c00004003000000402000000400c00000402400002400800800400805000003000800000804000000806800804401402402400800001000000000001003401000000801400402800000400401000000400004000c0200040000cc00401000001c00c00000000000000400401000804402c02009401000001400800800000801400000002c00000400000400c00000800400c00400000400000801001404402002400400000800007000000002400800c04005002000c02400400000003800400800400400800002c02400000402004801c0640040000080040040040f001001c00401c00401800000c00402800000000400400002800801001c01400000c01000000c00000800000001006000400001800000001c02800c00004800403800000801c00407400800c01001400c00000001801800001001c01000000c00000001000001400401400c00000003c03402807400000c00805000000000400000003800002c00802c00001400000c00000800c00002002400400400400001800400402807803400000001404c01c00001000000c02001800c00401400800c00000004404801400c01000000400800c01802000c00400000000001002801801c00004800c0040000000140240cc00802800404804001400c00c01000000000c00409c01804400000401400000401813ffb2c6409bfd963204ffccb1900efe658c813feb2c6439bf5963204ff8cb19026fc658c813ffb246409bfd923204ffcc91900afe648c813feb246438bf5923204ff8c919026fc648c871ffaa46438ff952321c7faa9190e3fc548c8037eb1c6401ffd4e3200ffca719007fd538c803fe29c6401ffd0e3200ffc87
  | 9 => 0xeb800112052ab580000032c1721c3aa28000b88728001b60000000002fb0e81979b5868abe298b02993800273a748000000000b521d800054020a7c8e000011d3800002fc8002882c80002afa71994ab00000003588000ae8000a28001dc0cf82b0000950f211f08f00029aac6a8125b94226402c0002fe2862fe8000bc2e80001de80034d00000000029d91b3521d0a808f39750003788000001830001a988a2128122cbb17b751aa1551ea92d08c9be0bd8d289f83da9710980000000012100018e89db6b1e212e00030202c83d36a80036a0000552232422619602b52a79e000030f00023dabf8002f83671ca01280000000011701c8000a522014600506a20c80000020e80032427800020a00014285d80031c0000000000001fa287b069c930608d1cb000223a671048a722e8f4b7111c80733014c0d016280017627311a88f96136211092a25c21b080a438be9021641548000598001ccb1887f8c205300034d8002ed9a2b72b2f80021580025500014bac40000a40898001c333300024a20707baa0a51850896b418cd8f79239231daa40329b552d2ad30790732d6a118c537d30eb7fabdb2a0d1a0133eb81a588290002f2a4b92cb6d23b00011e8001209a5a0980002a0692920a5b44a6fa0012d8000002e987d8000f28f02d1a6c1db0ba2b81e897c86c8bc8002d9805853970333b4999595082196d9fd2f197f332add9cf2120001b431725a3738d714daa32d22ea8001299b102680017191633a84713022b1cf80021500034b0382ae09116600000000000020e00000032f0002d70098a48f32d00502cb2930368000ff85f0440002720060000362333139593768000bd2601692f614c8003218870ee8000002e796534ca7f04190a29400f80021815f99a2360e31a700000000003a23e0000b080000035b0001513719f90df038945a5b0000460efae10002418002c60000f90ad8001f5a208003222688b980e857b2ca14b26b1834c0830c6a9690e99d8000001ce0dc800000000000000000106800000134000000062800315b200ab01daf880000000021f85a00025d8000000001e18afaea3808e11f0aec091ae40edb0497b05ab4f20409492fb7231190526c88680000000007c00000019f9678228001d217804e2bf0001ba80000001400023c0001a0034a5931480025699c1ad911b471c9b0cb468d08111b031aa62b4a15d18098917baaa88a96588b1d71a223fb5a0d50eaa10a60921a250e1b5f9c8b16aad3780c2855a8b01a1ca84a3282efa222a016c36b82e9f480013936e80000035d0b79eb26a86d170a9d0101d6a59ae300027d86f82da7b357a0b20a94080400000024d800000000105ae4b61112ae538200900034a8002cf00026f044814a3819722bb5904d80018223922114005d00000013d0e6894082032800000000
  | 10 => 0x37300020d00a95ca8c1ec23432e18785e907aeb025015037000201ab116c8000001bb0001840003630000001b88c000000004380010a80000000028d0da8001de0002ba8402318d78a91452b2a190c8a260a300035c8198001c481919928325080000008580000021c2cd1668390f884830e33b80000033db038000c6000082a368000000600001880de80000037eada00022aa84b5623ea2a30030a8000638000610db25aabbadaaa60ad0002039da25104780018d8648000a997701e0001c624c96708b80033e1b98000e480012900008189c34bac18000000002b394810909b183b348b1875824b0793801097380032eac39ef21aa44b5b80011c0002978001569ddaeb8860e40351d3023118b5c00017107a8588001bf327b3a000235202a0ba21895a310000b132580004cb573090a3a85b77911321000175ab626800000000000023c8fa0049e50498001e58000d429519b0001258001f980000000000035f1fe8002133199b78001c79b513500000000000000033080000032b12f0000bf14a0002888000000000002b1aed0e929c0c780012705200002f87e808848aaf0668000000b602f26a2440658e615600003e0001c42d880030a0000b3061b439131ee28383317e9031b81eeb3409313f04d213a1700c89ba5e8430c99d88002d6364280000000239a472be86d9378000000000feac00003500f1a371410e505e01f2b22ca1082668d80bb8fd9a7800354aa40b20cc20f28bb37249968a740cb00bb0f8008a78002992750000b69432cf8e99281b497ab440de1c0a8ca4e1500cf0641a428415281798f144a6b8000002f08acb680c09a1b058652ae80029b219934b080f81ebaa22b789e13a00000027624d00000013c0000c5a9fa9e18b8d222897e00000012aaba0001d127f9a617436c92e80000000005b8000001f383106600289380000000000000028a2713790888000000590002fb80db7f0002a3b1903393e99a800000184b70a6e926000185364b7a0880000000000000900003089228849312bb00032bb811cd000272aa5ac12d480000020fa529491320f583b3290fe09925f9d433fb5a80000000035eb6387c8cb8000c300024f8280001e28001af80000000001700016a0000002c480037708c1e3179b112c3190305000126af7a05901ae02949c5b5409e8002f9aacad50001f7b1c93980014e86986218b263a4e9fb275a582f52c88d4a6486e1ab08db2da4680680005c0cd11396b9ab8a203c0138160d134929ba0c352b3c831a7d1813518001632c92f912200804f2530bf95b9f8ab89b199c92c14f11013b84b890aa890d94b1d5941b28800000224ace0201e9ad380022700009f336800000374a5e37980023a0f61af099b510451beb5988ea169a493094396e0750c3b4faeeb1f27909d000131b3c0002ac0748
  | 11 => 0xade9c00ff22780032491490637595f2dc01f8002578458002f4b482962570cc89a01a9a3a900000001362b7281aef04fa6d9ea1639863489182009791ce993127a9a00000032299200028da4a90b2a1a691200002fd80032515a01c0003451a8a8e8e080022c8000ed15797da898000000001ed16eadf0001729bb9eda0680000100010d0000d69db9040340af199a6d27088513b10131e9a80ef18ca2e2fa1df0781bc097a5c8b935e19d000079a4f00000038280030d087846af382a80000030b33234e00002ba771cc21e2f42db15aae89b3b7a803acc0000000000000000001868000000000002630d38000001d3ab98000030001cd80020609a85701d355ac99ae23d14ab109370001fd80016b0000ca0c10002610000681e68e2955b23160a6b0fd0a62f71571358002c79240b02cdb431469929aa90ba2f18a0000000000000000003608002ab0002463580f51e818286b82580031e0001442430a100012b8000002a800000036e0708320409a680026500021404c0001b6b3611f94880004e99b8d9aee27bb1bb531a910fb39a321c280013aac58421803569c180001b10c2789150fb8002a70000000002b0818abd0000981a30001aeb7e083abc2d818180026780000026618a8dba55ad10aa0e8961a3aac2000164af322d2778fb37c8eb248aab8718ce9bfa29a821e90b581b8b808e291aa10dd1142a4b38b618288210002909368a69c52080000000abb459f5000084152029a04ab68002958003462d4301076a8927c00026980028f80027017f8c80001fb9ef9d50a1af200000000f00000000000e00029980000000022d80000017c000000078a0880000020532d0000000001c693e01831d9e100a2e6ad79ffacc9962d097482714e119a1889898f9e42fd1e721eb0704a837b131bd11e1c202d1f1807af6a829e4b6780018731222900003591680020da339fcab400021f369a4b2bc80037ba410002dcadd000188b01a2f80015196235d80c00015e8002a6933947108839800216207a4285fb1b04b154054ae180031012483f0e728691586086c1f4298000169a911e79c82281768001328001910b421a00032a9588771583428000003239a08000710002b92c70ca80011a0412e58002e61d60000002110001b310f3209cb8001d28000f98f40e78962520000c18be2548000e3a1b8000da1b20159f10b49e392b2459909fc0c733f18987b0a89bd99800013db410001ad00000023f0003128778000000000dc3359df80008100000030d9d01b0ab491d8722268220aa8d896d24092515e14d1f61e08002e90000fc000001b53b6c2aa2adae20c9011b662c09d4800102b31153949af000018c27a9a523b80019e03f8002870002c50001fa80031d0000000000800000002e38000002cab668003040001b7128a02222a7e00013300
  | 12 => 0x6aad907380025f00006e9940260000b3ad5a561dca258000001d9000247b628001bc851800217b3780000000028e0000000510f737415d81e8eca10265a621003509f6a8f0dfa451d9a03292a328ea0d6315076300800185b691e605816f303347b350c48b71530001ac0ae00d103a1cb7dade2492f5af11d780018e0f080010087a00000014f8002939b28f106322c2a918d3390000000001d811badf9389f33141478ba9f202e0bb0d310c82391917305b3651969f71ac80005cb161b907e09c9dd30c03084916fb6595983c8000000000002799d1b260a010e2b31072a993c8000001f033b31a23037c178a388ec1f8276a7eb1fae293f8000001fe0001a115b0000ee2540000000002358fc80027a00003eb60000000000340b688f6b760920000e5a8500029f00005607d00003bafa9779918c424c03a8000000b28568e200030b8000302e0800027b6f000000089000000000067b6f87000000000000000000026e37000025000021d2ff000000000000042b4233d0000000000d92c2aa52e72eca480241f28a80000671ec998b6d8d5afc07400216a96819ea0928a95c06f1ba01697d00019532729c9c100017a0ce19f06b0a0b319c725d253b09affa2409280023089737b0133400002ce8dd9ff11787f0002db8ac29ea37b4e80b0003380000fa
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x562c8410006e562c8410005f570c841022ef660c8410027f260c84102277450c84100767f76940100747f769401001e7e76940102057d769401001e7d769401001c7d76940102067c76940102067f649401011e7e64940102073e649401011e3e649401021e7d64940102073d64940100063d64940102067c64940102067f63940101167e63940102075e63940101165e63940100067d63940102075d63940100065d63940102067c63940102067f62940102167e62940102076e62940100066e62940100067d62940102076d62940100066d62940102067c62940102057f71940102077671940102057d71940100077571940100057571940102067e619401000777219401020774219401020d7e709401003f7a70940100767e60940102077710940102077a109401020779109401006cff768c010024fe768c01000cfd768c010024fc768c01010e7e658c0100067d658c010106be648c010006bd648c01000ede638c010006dd638c010006ee628c010006ed628c010025f6718c010005f5718c01006cff764c0100057f754c01003d7c754c0100fe7e654c0100067d654c0100f6be644c010006bd644c01000ede634c010006dd634c010006ee624c010006ed624c01002fd8304c010004fd76c801003d7e75c80100057d75c80100ee7e65c80100067d65c80100e6be64c8010006bd64c80100dede63c8010006dd63c801004eee62c8010006ed62c8010025f471c80101efe721c8010004ff768801004cfd76880100d67e65880100067d65880100aebe6488010006bd64880100cede6388010006dd638801004eee6288010006ed6288010025f67188010005f571880101ffe42188010004ff76480100057f754801003d7c75480100c67e65480100067d6548010005bf7448010035bc74480100bebe6448010006bd6448010005df734801002ddc73480100b6de6348010006dd634801004eee6248010006ed6248010005f77148010025f47148010007e7214801004cff7608010024fe7608010004fd7608010024fc76080100a67e65080100067d6508010035be7408010005bd740801009ebe6408010006bd6408010096de6308010006dd630801004eee6208010006ed6208010025f67108010005f571080101f7e42108010025f77644010006f77644010004f776440100077775440101df747544010027766544010027756544010007b774440101d7b47444010027b66444010027b56444010007d77344010007d47344010027d66344010027d56344010007e772440101edf672440101edf47244010007e47244010005e47244010027e66244010027e56244010025f77044010027f370440101e6f66044010027f260440100077650440101dff250440100077250440101dff150440101df7450440101d7f340440101d7f04044010
  | 1 => 0x8810026ed7198810026ec7198810026ef51988100266f5198810026ee5198810026ed51988100266d5198810026ec5198810026ef4198810026ee4198810026ed4198810026ec4198810026ef3198810026ee3198810026ed3198810026ec319881004eee709881004eec7098810006ef5098810006ee5098810006ed5098810006ec50988100066c5098810006ef4098810006ee4098810006ed4098810006ec4098810006ef3098810006ec3098810026ef1098810026ee1098810026ed1098810026ec1098810004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc7458810004ff735881000cfe735881000cfc7358810026ef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef4258810006ee4258810006ed4258810006ec4258810006ef3258810006ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026f47158810024f471588100267f51588100267d5158810026ee2158810026ec2158810026f4215881004cff705881004cfd70588100067c5058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026e47158810026ef51588100266f5158810026ee5158810026ed51588100266d5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec3158810006ee7058810006ec7058810006ef5058810006ee5058810006ed5058810006ec50588100066c5058810006ef4058810006ee4058810006ed4058810006ec4058810006ef3058810006ec3058810026ef1058810026ee1058810026ed1058810026ec105881004cff768c810024fe768c810004fd768c810024fc768c8101ce7e658c8100067d658c8101c6be648c810006bd648c81000ede638c810006dd638c81004eee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c8101be7e654c8100067d654c8101b6be644c810006bd644c81000ede634c810006dd634c81004eee624c810006ed624c810005f7714c810025f4714c810025f576c84101eef576c84100277665c84100277565c84101efb674c84101efb574c8410027b664c8410027b564c8410027d663c8410027d563c8410025f672c8410027e672c8410026f762c8410027e662c84101eef562c8410027e
  | 2 => 0x6bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf51590100263f5159010026be5159010026bd51590100263d5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc2159010036bf7059010006be7059010036bd7059010036bc7059010006bf5059010006be5059010006bd5059010006bc50590100063c5059010006bf3059010006bc3059010026bf1059010026be1059010026bd1059010026bc1059010004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c10026df7358c10006df5358c1002ede5358c10006dd5358c1002edc5358c10006df4358c1002ede4358c10006dd4358c1002edc4358c10004ff7258c1004cfc7258c1002edf3258c1002edc3258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c100267f5158c100267d5158c10026de3158c10026dc3158c1000cff7058c1000cfd7058c1002cfc7058c100067c5058c1002edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c100265f5158c10026de5158c10026dd5158c100265d5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c10006de7058c10006dc7058c10006df5058c10006de5058c10006dd5058c10006dc5058c100065c5058c10006df4058c10006de4058c10006dd4058c10006dc4058c10026df1058c10026de1058c10026dd1058c10026dc1058c1004eef759881004eee759881004eed759881004eec759881004eef749881004eee749881004eed749881004eec7498810006ef5498810006ee5498810006ed5498810006ec549881004eef739881004eee739881004eed739881004eec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810026ef7198810026ee719
  | 3 => 0xa70941102077b109411007cfe768c1100067f658c11010e7c658c110006bf648c110106bc648c110006df638c11000edc638c110006ef628c110006ec628c11000cff764c110054fd764c110024fc764c1100057f754c1100657c754c1100067f654c1100fe7c654c110006bf644c1100f6bc644c110006df634c11000edc634c110006ef624c110006ec624c110005f7714c110025f4714c110024fe76c8110024fc76c81100657e75c81100057d75c81100067f65c81100ee7c65c8110006bf64c81100e6bc64c8110006df63c81100dedc63c8110006ef62c811004eec62c8110025f671c8110005f571c8110004fe76881100067f65881100d67c6588110006bf64881100aebc6488110006df63881100cedc6388110006ef628811004eec628811004cff7648110004fd7648110024fc76481100057f75481100657c75481100067f65481100c67c6548110005bf744811005dbc7448110006bf64481100bebc6448110005df7348110055dc7348110006df63481100b6dc6348110006ef624811004eec6248110005f77148110025f47148110004fe76081100067f65081100a67c650811005dbe7408110005bd7408110006bf640811009ebc6408110006df6308110096dc6308110006ef620811004eec62081100057f75841100657c75841100067f65841100767c6584110006bf6484110046bc6484110006df638411006edc6384110006ef6284110006ec6284110237775184110007755184110025fa7084110026fb6084110025f67684110026f67684110024f67684110007777584110237747584110007776584110237746584110007b7648411023fb46484110007d76384110007d46384110007e7628411022ef6628411022ef46284110007e46284110006e46284110025f67084110026f76084110027f360841100077650841102377450841100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067c32594100267f71594100247f71594100267e71594100267d71594100247d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941003e7f70594100067e705941003e7d705941003e7c705941003c7c70594100067f40594100067e40594100067d40594100067c40594100067f30594100067c30594100267f10594100267e10594100267d10594100267c1059410006bf7559010006be7559010
  | 4 => 0x8910006ed4318910006ec431891004eef711891004eee711891004eed711891004eec7118910006ef51189100066f51189101f6ee5118910006ed51189101f6ec5118910006ef41189101f6ee4118910006ed41189101f6ec4118910006ef31189101f6ee31189101f6ec311891004eef701891004eed7018910006ef5018910006ee5018910006ed5018910006ec50189100066c5018910006ef4018910006ee4018910006ed4018910006ec4018910006ef3018910006ec30189101f6ef1018910006ed10189101f6ec101891004cff768c910004fe768c910004fd768c91004cfc768c9100067f658c9101ce7c658c910006bf648c9101c6bc648c910006df638c91000edc638c910006ef628c91004eec628c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101be7c654c910006bf644c9101b6bc644c910006df634c91000edc634c910006ef624c91004eec624c91001e7f76545100767e76545100667d76545100657c765451001e7c765451001c7c765451024e7f64545100073f64545100063f64545101ae7e645451024e7d64545101ae7c645451024f3c64545101ae3c64545100067f63545100075f63545100065f63545101a67e63545100067d63545101a67c63545100075c63545101a65c63545100067f62545100076f62545100066f62545102567e62545100067d62545102567c62545100076c62545100066c62545100257f71545100677771545100267f615451002776415451024f7541545100277631545100277621545100077b70545100057c70545100077870545100057870545100267f60545100277b105451002774105451002778105451002770105451000cfc764c5100067f654c51018e7c654c510006bf644c510186bc644c510006df634c51000edc634c510006ef624c510006ec624c51000775514c510005fb704c510005f8704c510004fe76c85100067f65c851017e7c65c851005dbe74c8510005bd74c8510006bf64c8510176bc64c8510006df63c851016edc63c8510006ef62c851004eec62c8510005fa70c8510005f970c851004cfc76485100067f654851014e7c6548510006bf6448510146bc6448510006df634851013edc6348510006ef624851004eec6248510007755148510005fb7048510005f870485100057e769411008e7e769411008c7e76941102467f64941100073f64941100063f649411011e7e64941102467d649411011e7c64941102473c649411011e3c64941100067f63941100075f63941100065f63941101167e63941100067d63941101167c63941100075c63941101165c63941100067f62941100076f62941100066f62941102167e62941100067d62941102167c62941100076c62941100066c62941100657d71941100657e70941100677
  | 5 => 0x6ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d89101feee71d8910006ed71d89101feec71d8910006ef51d89100066f51d89101feee51d8910006ed51d89101feec51d8910006ef41d89101feee41d8910006ed41d89101feec41d8910006ef31d89101feee31d89101feec31d89101feef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d89100066c50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910006ef30d8910006ec30d89101feef10d89101feec10d89100657e75989100057d75989100067f65989100067c659891005dbe7498910005bd7498910006bf6498910006bc6498910055de7398910005dd7398910006df6398910006dc6398910006ef62989100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910055dc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004f771589100067f5158910004ff7058910006fb70589100067c5058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc631891004eee6218910006ed6218910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f51189100076c50189101f7eb10189101f7e8101891004eef751891004eee751891004eed751891004eec751891004eef741891004eee741891004eed741891004eec7418910006ef5418910006ee5418910006ed5418910006ec541891004eef731891004eee731891004eed731891004eec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee431
  | 6 => 0xf72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d10266de71d8d10006dd71d8d10266dc71d8d10006df51d8d100065f51d8d10266de51d8d10006dd51d8d10266dc51d8d10006df41d8d10266de41d8d10006dd41d8d10266dc41d8d10266de21d8d10266dc21d8d10266df70d8d10056de70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d100065c50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10266df10d8d10266dc10d8d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10056dc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10054ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1004cfc7258d10006ec7258d1004cec7258d1006cff7158d10006f77158d100067f5158d1007cff7058d10006fb7058d100067c5058d10005de7618d10056de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5118d1025edf6018d100075c5018d1025fdb1018d1025fd81018d1004cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d891000cfe73d8910004fd73d891000cfc73d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef42d8910006ee42d8910006ed42d8910006ec42d8910006ef32d8910006ec32d8910024fe71d8910024fc71d89100067f51d891004cfe70d891004cfc70d89100067c50d891004cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f51d89100076c50d89101ffeb10d89101ffe810d8910006ef75d8910006ee75d8910
  | 7 => 0x95100067d42d95100067c42d95100067f32d95100067c32d95100067f71d95102067e71d95100667d71d95100647d71d95102067c71d95100067f41d95102067e41d95100067d41d95102067c41d95100067f31d95102067e31d95102067c31d95102067e21d95102067c21d95102067f70d95100667e70d951001c7e70d95100667d70d95100667c70d951001c7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067c30d95102067f10d95100667d10d95102067c10d951005dbe76d911005ebe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d91100073f51d91100073c50d911026fbb10d911026fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006bc32d9110006bf71d911026ebe71d911005ebd71d911026ebc71d9110006bf51d91100063f51d911026ebe51d9110006bd51d911026ebc51d9110006bf31d911026ebe31d911026ebc31d911026ebe21d911026ebc21d911026ebf70d911005ebe70d911005ebd70d911005ebc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d91100063c50d9110006bf30d9110006bc30d911026ebf10d911005ebd10d911026ebc10d911000cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10056de63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df53d8d10056de53d8d10006dd53d8d10056dc53d8d10006df43d8d10056de43d8d10006dd43d8d10056dc43d8d1004cfe72d8d10004fd72d8d10056df32d8d10056dc32d8d10024fe71d8d10054fd71d8d10024fc71d8d100067f51d8d10056df31d8d1000cfe70d8d10024fd70d8d1000cfc70d8d100067c50d8d10056df30d8d10055de76d8d1000cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075f51d8d100075c50d8d10267db10d8d10267d810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006d
  | 8 => 0x17e7c65c8610045be74c8610005bd74c861004eee62c8610006ed62c86102977751c86100077551c8610005fa70c8610005f970c861022ef576c86100077765c86102977465c861022fb674c861022fb574c8610025f672c861022ef762c861022fe662c861022ef562c8610007e562c861022ff270c8610005f570c861022ff170c8610026f660c86102977450c861004cff76486100067f654861014e7c654861004eee6248610006ed6248610027e42148610005fb7048610005f87048610005f57608610026f57608610027767508610027757508610007776508610287746508610027e6720861022ef76208610007e7620861022ef5620861022fe4620861022fe6420861028fe54208610005f57008610027f260086102877450086100757e769421001e7e769421001c7e769421001e7d769421027e7f649421011e7e649421027e7d649421011e7c64942100067f63942101167e63942100067d63942101167c63942100067f62942102167e62942100067d62942102167c62942100757f71942100077671942100057d71942100077571942100057571942100077721942100077421942100757e70942100777a70942102067e60942102077b109421000cfe768c210024fd768c2100067f658c21010e7c658c21000ede638c210006dd638c210025f6718c210005f5718c21002cff764c2100057f754c2100757c754c2100067f654c2100fe7c654c210006df634c21000edc634c2100757e75c82100057d75c82100067f65c82100ee7c65c8210006ef62c821004eec62c821022fe721c8210024fd76882100067f65882100d67c658821004eee6288210006ed6288210025f67188210005f57188210007e421882100057f75482100757c75482100067f65482100c67c6548210005bf7448210045bc7448210005df734821006ddc7348210006ef624821004eec6248210005f77148210025f47148210007e72148210024fd76082100067f65082100a67c6508210045be7408210005bd740821004eee6208210006ed6208210025f67108210005f5710821022fe42108210005f576c4210026f576c42100277675c42100277575c42100077765c42102777465c421022df672c4210025f472c4210027f260c42100077650c42102777450c42100657e76d95100667e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e63d95100067c63d95100657c70d95102077b10d95102077810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d
  | 9 => 0xc30d96102067f10d96100067f65d8e100067c65d8e1006ede63d8e10004ff75d8e1001cfe75d8e10004fd75d8e1001cfc75d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e1006cfd73d8e1006ede43d8e10006dd43d8e1004cfe72d8e10004fd72d8e1006edc32d8e10006f571d8e100067f51d8e10266de31d8e10266dc31d8e10006fa70d8e100067c50d8e1006edf30d8e1000cff7658e100057f7558e100757c7558e100067f6558e100067c6558e1006edc6358e10004ff7558e100067f7558e100047f7558e1001cfe7558e10004fd7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e10006df7358e10004ff7258e1004cfc7258e100067f5158e1006edf3158e10024fc7058e100067c5058e1006edc3058e100067f65d8a100067c65d8a10004ff75d8a1001cfe75d8a10004fd75d8a1001cfc75d8a10004ff74d8a10014fe74d8a10004fd74d8a10014fc74d8a1000cfe73d8a10004fd73d8a1000cfc73d8a10006f571d8a100067f51d8a101feee21d8a101feec21d8a10006fa70d8a100067c50d8a10004fd7698a100757e7598a100057d7598a100067f6598a100067c6598a10006ef6298a1004cff7658a100057f7558a100757c7558a100067f6558a100067c6558a10005bf7458a10045bc7458a10005df7358a1006ddc7358a10004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10004fd7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a10006df7358a10004df7358a1000cfe7358a1000cfc7358a10006dc7358a1000cdc7358a10006ef7258a10006ee4258a10006ed4258a10006f77158a100067f5158a100067c5058a100067f6518a100067c6518a10045be7418a10005bd7418a1004eee6218a10006ed6218a1004cff768ca10004fe768ca10004fd768ca1004cfc768ca100067f658ca101ce7c658ca10006df638ca1000edc638ca10004ff764ca10004fe764ca10004fd764ca10004fc764ca100067f654ca101be7c654ca10005f7714ca10025f4714ca1001e7f765461001e7c765461029e7f64546101ae7e645461029e7d64546101ae7c64546100067f63546101a67e63546100067d63546101a67c63546100067f62546102567e62546100067d62546102567c62546100257f71546100777771546100267d61546100277421546100077b70546100057c70546100077870546100057870546100267e60546100277710546100277b105461002778105461000cff764c6100067f654c61018e7c654c61000ede634c610006dd634c610005fb704c610005f8704c6100067f65c8610
  | 10 => 0x97100267c1059710004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f10026df7358f1007ede4358f10006dd4358f10004ff7258f1004cfc7258f1007edc3258f10024fc7158f100267f5158f100267d5158f10026de3158f10026dc3158f100067c5058f1007edf3058f10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b10004ff7358b1000cfe7358b1000cfc7358b10026ef7258b10024fc7158b100267f5158b100267d5158b10026ee2158b10026ec2158b100067c5058b1004cff768cb10024fe768cb10004fd768cb10024fc768cb101ce7e658cb100067d658cb1000ede638cb10006dd638cb10004ff764cb10024fe764cb10004fd764cb10024fc764cb101be7e654cb100067d654cb102057d76943100667d76943100647d76943102067f649431011e7e64943102a67d64943102067c64943102067f63943101167e63943100067d63943102067c63943102067f62943102167e62943100067d62943102067c62943102057d719431020d7e709431008f7a7094310054fd768c31010e7e658c3100067d658c310266df638c31000edc638c31000cff764c310024fc764c3100057f754c31008d7c754c3100fe7e654c3100067d654c31000ede634c310006dd634c310005f7714c310025f4714c31007fd8304c31008d7e75c83100057d75c83100ee7e65c83100067d65c831004eee62c8310006ed62c8310025f671c8310005f571c83100d67e65883100067d65883101feef628831004eec628831004cff76483100057f754831008d7c75483100c67e65483100067d6548310005bf7448310085bc7448310005df734831007ddc734831004eee6248310006ed6248310005f77148310025f471483100a67e65083100067d6508310085be7408310005bd74083101f6ef620831004eec62083100767e76d96100067f64d96100067e64d96100067d64d96100067c64d96100067e63d96100067c63d96100077571d96100077a70d96102077b10d96102077810d96100067f74d96100067e74d96100067d74d96100067c74d96100067f73d96100067e73d96100067d73d96100067c73d96100067f43d96100067e43d96100067d43d96100067c43d96100067f72d96100067e72d96100067d72d96100067c72d96100067f42d96100067e42d96100067d42d96100067c42d96100067f32d96100067c32d96100067d71d96100067571d96100067f41d96102067e41d96100067d41d96102067c41d96100067f31d96102067e31d96102067c31d96102067e21d96102067c21d96100067e70d96100067a70d96100067f40d96100067e40d96100067d40d96100067c40d96100067f30d96100067
  | 11 => 0xd67e60544202576f20544202577a2054420257792054420024ff768c42004cfe768c420004fd768c4200a57e758c4200057d758c420196be648c420006bd648c420026f6618c420006f5618c420004ff764c420004fd764c42004cfc764c420186be644c420006bd644c42000ede634c420006dd634c420005ef724c42004dec724c420026f6614c420006f5614c42004ded76884201f6ed7688420004ed76884201f76e75884201f76d75884201f7ae74884201f7ad748842004eef648842004fae64884202deed648842004fad6488420006ad64884201f7ce73884201f7cd738842004dee718842004fe6718842004eef61884201f6ed61884201f76f51884201f76d5188420005ed70884201feee608842004fea60884202d76c50884200d67f769402001e7e769402001e7d76940202167c76940202167f649402011e7e64940202173e649402011e3e64940202ce7d64940202173d64940200063d64940202167c64940202167f63940201167e63940200067d63940202167c63940202176e72940200076d72940202167e62940200057d71940202067e61940200067d61940200076e21940202176c21940202c57e70940200a77a70940200d67e60940202176f20940202177a20940202177920940200ccff768c02004cfe768c02000cfd768c02004cfc768c020106be648c020006bd648c02000ede638c020006dd638c02004dee728c020005ed728c0200ccff764c0200057f754c0200a57c754c0200f6be644c020006bd644c02004def7648020006ef7648020004ef76480200076f75480202af6c7548020007af74480202bfac744802004eef644802004fae64480202beed644802004fad6448020006ad6448020007cf7348020007cc7348020007e771480201f5ec7148020007e47148020005e47148020006ed61480202af6f51480200076d514802004def704802004feb70480202b6ee604802004fea60480200076e50480202af6c50480200067f74597100067e74597100067d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067e42597100067d42597100067c42597100067f32597100067c32597100267f71597100267e71597100267d71597100267c71597100267f41597100267e41597100267d41597100267c41597100267f31597100267e31597100267d31597100267c31597100267f21597100267e21597100267d21597100267c215971008e7f705971008e7e70597100067d705971008e7c70597100067f40597100067e40597100067d40597100067c40597100067f30597100067c30597100267f10597100267e10597100267d105
  | 12 => 0xc654c120006bf644c1200f6bc644c120006df634c12000edc634c120005ef724c12004dec724c120006f7614c120006f4614c1200b7d8304c1200067f65881200d67c6588120006bf64881200aebc6488120006df63881200cedc6388120006f76188120006f4618812004dfa708812004efb60881200076f65881202f76c65881202b5ef74881202b5ed7488120007af64881202ffac6488120007cf6388120007cc6388120005ed7188120007e761881201feec6188120007e46188120006e461881202f76f51881200076d518812004dee708812004eef608812004feb60881200076e50881202f76c5088120006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc535902004ebf725902004ebe725902004ebd725902004ebc725902004ebf525902004ebe525902004ebd525902004ebc525902004ebf325902004ebe325902004ebd325902004ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf51590200063f5159020006be5159020006bd5159020006bc5159020006bf3159020006bc315902004ebf215902004ebe215902004ebd215902004ebc215902004eac215902009ebf7059020006be705902009ebd705902009ebc7059020006bf5059020006be5059020006bd5059020006bc50590200063c5059020006bf3059020006bc305902004ebf205902004eaf205902004ebe205902004ebd205902004ebc2059020004ff7558c2001cfe7558c20004fd7558c2001cfc7558c20004ff7458c20014fe7458c20004fd7458c20014fc7458c2004edf7358c20096de5358c20006dd5358c2004cff7258c2004cfe7258c2004cfd7258c2004cfc7258c2004ede3258c2004edc3258c20004ff7158c20024fc7158c200067f5158c20096df3158c20094fc7058c200067c5058c20096dc3058c20004ff755842001cfe7558420004fd755842001cfc7558420004ff7458420014fe7458420004fd7458420014fc7458420004ff735842000cfe735842000cfc735842004ef771584200067f5158420006f65158420006f5515842004ef7215842004eec215842004ef42158420024ff70584200067c505842004eef20584200067f76544202567e76544200067d76544202567c76544202567f64544201ae7e64544202573e64544201ae3e64544202ee7d64544202573d64544200063d64544202567c64544202567f63544201a67e63544200067d63544202567c63544200076f72544202576c72544202567e62544202e57f71544200a77771544200267e61544202577661544200267661544200067d61544202577561544200067561544200267c61544201f76c21544200057c7054420
  | 13 => 0x45200065f63545201a67e63545200067d63545201a67c63545200075c63545201a65c635452033f6e425452033f6d42545200c57f71545200c77771545200067f61545200077761545200067761545200267e61545200267c61545200077461545200267461545200057c70545202577b2054520004fe768c520004fd768c520024fc768c5200c57e758c5200057d758c5200067f658c52019e7c658c520006bf648c520196bc648c520006df638c52000edc638c52004dee728c520005ed728c520006f7618c520026f4618c520004ff764c520004fe764c520004fc764c5200067f654c52018e7c654c520006bf644c520186bc644c520006df634c52000edc634c520006f7614c520026f4614c520005ee76c852004eee76c8520004ee76c85200076f65c85203276c65c852004def74c852004fae74c8520335ed74c852004fad74c8520005ad74c8520007af64c852032fac64c8520007cf63c8520007cc63c8520007e761c8520026ee61c8520026ec61c8520007e461c8520026e461c85203276f51c85200076d51c8520005ee70c852004eef60c852004feb60c85203276c50c85200c57e75885200057d75885200067f65885201667c65885200bdbe7488520005bd7488520006bf648852015ebc64885200b5de7388520005dd7388520006df6388520156dc638852031ded7288520006f76188520026f46188520005fa7088520005f97088520024fc76485200067f654852014e7c6548520006bf6448520146bc6448520006df634852013edc6348520006f76148520026f46148520005fb7048520005f87048520024ec76485200076f654852030f6c654852031def744852031ded7448520007af6448520317ac6448520007cf6348520007cc634852004def714852004fe77148520007e76148520026ee6148520026ec6148520007e46148520026e4614852030f6f51485200076d5148520007eb7048520005ec7048520007e8704852004eef604852004feb604852030f6c50485200057e76941200ee7e76941200ec7e76941203067f64941200073f64941200063f649412011e7e64941203067d649412011e7c64941203073c649412011e3c64941200067f63941200075f63941200065f63941201167e63941200067d63941201167c63941200075c63941201165c63941203076e42941203076d42941200057d71941200067f61941200077761941200067761941202067c61941200077461941200067461941200076f21941200076d21941200c57e70941200c77a70941202177b20941200dcfe768c1200067f658c12010e7c658c120006bf648c120106bc648c120006df638c12000edc638c120006f7618c120006f4618c12000cff764c1200b4fd764c12004cfc764c1200057f754c1200c57c754c1200067f654c1200fe7
  | 14 => 0x22ef452d8520006f742d852022ef642d8520006f542d852022ef442d8520006f732d852022ef632d8520006f532d852022ef432d852022ef770d8520006f570d8520006f750d8520006f650d8520006f550d8520006f450d85200067450d8520006f740d8520006f640d8520006f540d8520006f440d8520006f730d8520006f430d852022ef720d852022ef420d85200c57e75985200057d75985200067f65985200067c65985200bdbe7498520005bd7498520006bf6498520006bc64985200b5de7398520005dd7398520006df6398520006dc6398520006f761985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520006bf6458520006bc6458520005df73585200b5dc7358520006df6358520006dc63585200c57e75185200057d75185200067f65185200067c6518520006bf6418520006bc6418520006df6318520006dc6318520026f66118520006f56118520007775118520005f67618520006f67618520007767518520007757518520006f76518520007776518520006776518520006f66518520006f56518520006f46518520007746518520006746518520006f76418520007b76418520006b76418520006f66418520006f56418520006f46418520007b46418520006b46418520006f76318520007d76318520006d76318520006f66318520006f56318520006f46318520007d46318520006d46318520007e57218520007e64218520007e542185200077450185201eff320185201eff02018520026f77518520026f67518520026767518520026f57518520026757518520026f47518520026f77418520026f67418520026f57418520026f47418520006f75418520006f65418520006f55418520006f45418520026f77318520026f67318520026f57318520026f47318520006f75318520006f65318520006f55318520006f45318520006f74318520006f64318520006f54318520006f44318520026f77218520026f67218520026f47218520006f752185201eef65218520006f552185201eef45218520006f742185201eef64218520006e64218520006f54218520006e542185201eef44218520006f732185201eef63218520006f532185201eef43218520026f77018520026f57018520006f75018520006f65018520006f55018520006f45018520006745018520006f74018520006f64018520006f54018520006f44018520006f73018520006f430185201eef72018520006f520185201eef420185200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c765452033e7f64545200073f64545200063f64545201ae7e645452033e7d64545201ae7c645452033f3c64545201ae3c64545200067f63545200075f635
  | 15 => 0xf7458d200bdbc7458d20006bf6458d20006bc6458d200b6dc6358d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d200b4ff7358d20006df7358d200ccff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20024fc7158d20006f47158d20024f47158d200067f5158d200dcff7058d20006fb7058d200067c5058d20005de7618d200b6de7618d20004de7618d20006df6518d200075f6518d200065f6518d20006de6518d20006dd6518d20006dc6518d200075c6518d200065c6518d20006df6418d200079f6418d200069f6418d20006de6418d20006dd6418d20006dc6418d200079c6418d200069c6418d20007ce4218d20007cd4218d200075f5118d20346df6018d200075c5018d20347db2018d20347d82018d2000cfc764c9200067f654c9201be7c654c920006bf644c9201b6bc644c920006df634c92000edc634c920005fb704c920005f8704c9200c57c75d85200067f65d85200067c65d8520006bf64d8520006bc64d8520006df63d8520006dc63d85200077751d8520004ff75d85200067f75d852001cfe75d8520004fd75d852001cfc75d85200067c75d852001c7c75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d852000cfe73d8520004fd73d852000cfc73d85200067f51d8520006f751d85200067751d8520006f651d8520006f551d8520006f451d8520006f741d8520006f641d8520006f541d8520006f441d8520006f731d8520006f431d8520024fe70d85200067c50d85200077775d85200077475d8520006f765d85200077765d85200067765d8520006f665d8520006f565d8520006f465d85200077465d85200067465d8520006f764d8520007b764d8520006b764d8520006f664d8520006f564d8520006f464d8520007b464d8520006b464d8520006f763d8520007d763d8520006d763d8520006f663d8520006f563d8520006f463d8520007d463d8520006d463d8520007e772d8520007e642d8520007e542d85200077450d852022ff320d852022ff020d8520006f775d85200067775d8520006f675d8520006f575d8520006f475d85200067475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d8520006f653d8520006f553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d8520006f772d852022ef672d8520006f752d852022ef652d8520006f552d8520
  | 16 => 0x91200bfac72d91200073f51d91200073c50d9120357bb20d9120357b820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120006bf72d9120356be72d91200bebd72d9120356bc72d9120006bf52d9120356be52d9120006bd52d9120356bc52d9120006bf32d9120356be32d9120356bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d91200063f51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006bc31d9120356bf21d9120356bc21d9120356bf70d91200bebe70d91200bebd70d91200bebc70d9120006bf50d9120006be50d9120006bd50d9120006bc50d91200063c50d9120006bf30d9120006bc30d9120356bf20d91200bebd20d9120356bc20d912000cfe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d200b6de63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df53d8d200b6de53d8d20006dd53d8d200b6dc53d8d20006df43d8d200b6de43d8d20006dd43d8d200b6dc43d8d2004cfe72d8d200b4fd72d8d2004cfc72d8d200b6df32d8d20024fe71d8d20004fd71d8d200067f51d8d200b6df31d8d200b6dc31d8d2004cfd70d8d200067c50d8d200b6df30d8d200b5de76d8d2000cde76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d200079f64d8d200069f64d8d20006de64d8d20006dd64d8d20006dc64d8d200079c64d8d200069c64d8d20007ce42d8d20007cd42d8d200075f51d8d200075c50d8d2034fdb20d8d2034fd820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d2034ede72d8d20006dd72d8d2034edc72d8d20006df52d8d2034ede52d8d20006dd52d8d2034edc52d8d20006df42d8d2034ede42d8d20006dd42d8d2034edc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d200065f51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d2034edf21d8d2034edc21d8d2034edf70d8d200b6de70d8d20006dd70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d200065c50d8d20006df40d8d20006de40d8d20006dd40d8d20006dc40d8d2034edf20d8d2034edc20d8d200057f7558d200c57c7558d200067f6558d200067c6558d20005b
  | 17 => 0x26f66188620006f56188620005fa7088620005f970886201ff6e75886201ff6d75886201ffae74886201ffad748862038eef648862038eed64886201ffce73886201ffcd738862004dee71886201ffe661886201feed6188620007e561886201ff6f51886201ff6d51886201ffea7088620005ed70886201ffe9708862004eee60886203876c5088620024ff7648620026f66148620006f5614862004fe42148620005fb7048620005f87048620005ed760862004eed760862004f6e750862004f6d750862037eef640862037eed640862004fe67108620007e761086201feed61086201ffe461086201ff6f51086201ff6d5108620005ed700862004fea60086203776c500862001e7e769422001e7d769422036e7f649422011e7e649422036e7d649422011e7c64942200067f63942201167e63942200067d63942201167c63942200076e72942200076d72942200057d71942202067e61942200067d61942200076e21942200076c21942200d57e70942200d77a70942202167e60942202177b209422000cfe768c22004cfd768c22000ede638c220006dd638c22004dee728c220005ed728c220094ff764c2200057f754c2200d57c754c2200cfd8304c220005ed76c822004eed76c822004f6e75c822004f6d75c8220366ef64c8220366ed64c82201fdee71c8220006ed61c822035f6f51c82200076d51c822004fea60c82200076e50c822035fea50c82200076a50c822035fe950c822035f6c50c82200c57e76d95200c67e76d952001c7e76d95200067f64d95200067e64d95200067d64d95200067c64d95200073c64d95200063c64d95200067e63d95200067c63d95200076e42d95200076d42d95200057d71d95200c57c70d95202177b20d95202177820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95202167e72d95200c67d72d95202167c72d95200067f42d95202167e42d95200067d42d95202167c42d95200067f32d95202167e32d95202167c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067c31d95202167f21d95202167c21d95202167f70d95200c67e70d95200c67d70d95200c67c70d95200067f40d95200067e40d95200067d40d95200067c40d95200067f30d95200067c30d95202167f20d95200c67d20d95202167c20d95200bdbe76d91200bebe76d9120014be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006be63d9120006bc63d9120007af72d
  | 18 => 0xd638c72004dee728c720005ed728c720004ff764c720004fd764c72004cfc764c72018e7e654c7200067d654c7203b6df634c72000edc634c72004def7648720006ef764872004f6e654872004f6d65487203adef74487203aded744872004fe77148720026ee6148720026ec61487203a76f51487200076d5148720005ec70487203a76c50487202157d76943200c67d76943200c47d76943202167f649432011e7e649432039e7d64943202167c64943202167f63943201167e63943200067d63943202167c63943202176e429432039f6d42943200057d71943202067e61943200067d61943202176f21943200076d21943202c57e70943200ef7a70943200b4fd768c32010e7e658c3200067d658c32034edf638c32000edc638c32000cff764c32004cfc764c3200057f754c3200ed7c754c3200fe7e654c3200067d654c32000ede634c320006dd634c320005ef724c32004dec724c3200cede63d8e20004ff75d8e2001cfe75d8e20004fd75d8e2001cfc75d8e20004ff74d8e20014fe74d8e20004fd74d8e20014fc74d8e200ccfd73d8e20006ed72d8e2034ede32d8e2034edc32d8e20024fe71d8e20004fd71d8e200067f51d8e20006fa70d8e200067c50d8e2000cff7658e200cedc6358e20004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e20006df7358e200cedf3258e20004ff7158e20024fc7158e200067f5158e200cedf3158e2004cfc7058e200067c5058e200cedc3058e2000cff764ca2000ede634ca20006dd634ca20005fb704ca20005f8704ca200d57e75986200057d7598620006f76198620005bf74586200adbc7458620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620006bf7458620004bf7458620014fe7458620004fd7458620014fc7458620006bc7458620014bc7458620004ff735862000cfe735862000cfc73586200067f51586200067c50586200d57e75186200057d75186200adbe7418620005bd74186200cdde7318620005dd7318620026f66118620006f561186200067f76546200067e76546200067d76546200067c76546203967f64546201ae7e64546203967d64546201ae7c64546200067f63546201a67e63546200067d63546201a67c63546200076f72546200076c72546200c67d62546200d57f71546200d77771546200267e61546200067d61546200267c61546200057c70546202567e60546202577b2054620024ff768c620004fe768c620004fd768c6200d57e758c6200057d758c620004ff764c620004fd764c620004fc764c62000ede634c620006dd634c620005ef724c62004dec724c6200d57e75886200057d75886200adbe7488620005bd74886200cdde7388620005dd7388620
  | 19 => 0x85301367c650853000dde7308530005dd7308530006ef620853004eec6208530006f76108530026f46108530005fa7008530005f970085303d57e76941303e67e76941303d47e76941303de7f649413011e7e64941303de7d649413011e7c64941301167f63941300067f62941302167c62941300057d71941300067f61941302067c61941301175f31941300075d31941303d57e70941300ff7a70941301167f60941301177b30941301175c30941301177830941300075f658c1303c75c658c1303cedf648c1303cedd648c13034edc628c130005dd718c130266dc618c1303c75f518c1300075d518c13000dde708c13000fda708c13000edf608c13000fdb608c1300075e508c1303c75c508c1300067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067e43597200067d43597200067c435972004e7f725972004e7e725972004e7d725972004e7c725972004e7f425972004e7e425972004e7d425972004e7c425972004e7f325972004e7e325972004e7d325972004e7c32597200067f71597200047f71597200067e71597200067d71597200067c71597200067f41597200067e41597200067d41597200067c41597200067f31597200067c315972004e7f215972004e7e215972004e7d215972004e7c21597200ee7f70597200ee7e70597200067d70597200ee7c70597200067f40597200067e40597200067d40597200067c40597200067f30597200067c305972004e7f205972004e7e205972004e7d205972004e7c2059720004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f2004edf7358f200dede4358f20006dd4358f2004cfc7258f2004ede3258f2004edc3258f20004ff7158f20024fc7158f200067f5158f200dedc3158f200067c5058f200dedf3058f20004ff755872001cfe75587200067e755872001c7e7558720004fd75587200067d755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc7458720004ff735872000cfe735872000cfc735872004ef771587200067f515872004ef7215872004ef421587200067c50587202557f76547200067f76547200047f76547202567e76547202557d76547200067d76547200047d76547202567c76547202567f64547201ae7e64547203be7d64547202567c64547202567f63547201a67e63547200067d63547202567c63547202576e42547203bf6d42547202e57f71547200ef7771547200267e61547200067d61547200267c61547202576f21547200057c7054720024ff768c72004cfe768c720004fd768c7200ed7e758c7200057d758c72019e7e658c7200067d658c72000ede638c720006d
  | 20 => 0x67e40d95300067d40d95300067c40d95301167f30d95301167e30d95301167d30d95301167c30d95300067f65d89300067c65d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d8930006ef42d8930006ec42d89300ceee32d89300ceed32d8930024fe71d8930004fd71d89300067f51d89300067c50d89300fd7e75989300057d75989300067f65989300067c6598930006ef62989300b5f970989300057f75589300fd7c75589300067f65589300067c6558930005bf74589300f5bc7458930005f77158930005f471589300ddfb70589300067f65189300067c65189300f5be7418930005bd741893004eee6218930006ed62189300fd7c75d85300067f65d85300067c65d8530004ff75d85300067f75d853001cfe75d8530004fd75d853001cfc75d85300067c75d853001c7c75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d853004cfe72d8530004fd72d85300067f51d8530006f741d8530006f441d853006ef631d853006ef531d85300067c50d85300fd7e75985300057d75985300067f65985300067c6598530006f76198530055f970985300057f75585300fd7c75585300067f65585300067c6558530005bf74585300f5bc7458530005ef7258530005ec725853007dfb70585300fd7e75185300057d75185300067f65185300067c65185300f5be7418530005bd7418530026f66118530006f561185300067f76545300057e76545300067e76545300047e76545300067d76545300057c76545300067c76545300047c76545304067f64545301ae7e64545304067d64545301ae7c64545301a67f63545300067f62545302567c62545303fd7f71545300ff7771545300067f61545300267e61545300267c61545301a75f31545300057c70545301a67f60545301a77b30545301a75c30545301a7783054530024dc764c5300075f654c5303ef5c654c5303f6df644c5303f6dd644c5303b6dc624c53000ddf714c53000fd7714c530007d7614c530026de614c530026dc614c530007d4614c5303ef5f514c5300075d514c530007db704c530005dc704c530007d8704c530005d8704c53000edf604c53000fdb604c5303ef5c504c530004fe76c8530004fd76c853004cfc76c85300067f65c853017e7c65c85300f5be74c8530005bd74c8530006f761c8530026f461c8530004fe7688530004fd7688530024fc76885300fd7e75885300057d75885300067f65885301667c65885300f5be7488530005bd748853000dde7388530005dd7388530006ef628853004eec6288530004ff7648530004fe7648530004fc76485300067f654853014e7c6548530004fe7608530004fd7608530024fc76085300fd7e75085300057d75085300067f650
  | 21 => 0xd7518630105be7418630005bd7418630005ee7218630005ed7218630026f66118630006f5611863006dfa70186300067f76546300067e76546300067d76546300067c76546304267f64546301ae7e64546304267d64546301ae7c64546300075f73546301a75c73546301a67d63546301a75e43546304275d43546302567e62546300067d62546300075e32546301a75c32546303fd7f715463010f7771546300267e61546300067d61546300267c61546302675c31546300057c70546301a67e60546301a75f30546301a77b30546301a77830546302675e758c6302675d758c630265df748c63041ddd748c63034dde728c63000dde718c63000fd6718c630267d6618c630266dd618c630007d5618c6302675f518c6302675d518c630267da708c630005dd708c630267d9708c63000ede608c63000fda608c6304175c508c63004cff76c8630004fe76c8630004fd76c8630105be74c8630005bd74c863000dde73c8630005dd73c863004eee62c8630006ed62c8630024ff7688630004fe7688630004fd768863010d7e75886300057d7588630105be7488630005bd748863000dde7388630005dd7388630004ff7648630004fd7648630004fc7648630005df734863000ddc734863004eee6248630006ed6248630024ff7608630004fe7608630004fd760863010d7e75086300057d7508630265df730863000ddc7308630005fa7008630005f970086301167f769423001e7e769423001e7d76942301167c769423040e7f649423011e7e649423040e7d649423011e7c64942301175e73942300075d73942301175e439423040f5d43942302167e62942300067d62942300075e32942301175c32942300057d71942302067e61942300067d61942300075e31942301175c31942303d57e709423010f7a70942301167e60942301175f30942301177b30942301175b30942301177830942303d57e76d95300fe7e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300057d71d95301175f31d95301157c70d95301177b30d95301175c30d95301177830d95300067f74d95300067e74d95300067d74d95300067c74d95301167f73d95301167e73d95301167d73d95301167c73d95301167f43d95301167e43d95301167d43d95301167c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95301167f32d95301167e32d95301167d32d95301167c32d95300067f71d95300067e71d95300067d71d95300047d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95301167f31d95301167e31d95301167d31d95301167c31d95301167f70d95300fe7e70d95301167d70d95301167c70d95300067f40d9530
  | 22 => 0x86502173e74c865011d3e74c86504657d74c86502173d74c86500053d74c86502157c74c86502157f73c86501157e73c86500057d73c86502157c73c86502176e62c86500076d62c86500067d61c86500057e70c86500057d70c86502c67e60c865017f7a60c86502057f76886500057e76886502067e76886500047e76886500057d76886502067d76886500047d76886502057c76886502057f748865011d7e74886502073e748865011d3e748865045d7d74886502073d74886500053d74886502057c74886502057f73886501157e73886502075e73886501155e73886500057d73886502075d73886500055d73886502057c738865014d7d72886504576e42886504576d42886502057e71886502067d61886502076f21886502177721886500057e70886500057d708865020e7e60886501677a60886500057f76486500057e76486500057d76486500057c764865044d7f744865011d7e744865044d7d744865011d7c74486500057f73486501157e73486500057d73486501157c73486500076e62486500076d62486500067d61486502177721486502076e21486500057f70486500057c704865014e7e604865014f7a60486502057f76086500057e76086502067e76086500047e76086500057d76086502067d76086500047d76086502057c76086502057f740865011d7e74086504457d74086502057c74086502057f73086501157e73086500057d73086502057c73086502157e72086502176e420865043f6d42086502057e71086502067d61086502076f21086502077621086502076d21086502177521086500057e70086500057d700865020e7e60086501377a6008650095fa70d8a3010d7e7598a300057d7598a30006ef6298a30004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a30006ef5258a30006ec5258a30006ee4258a30006ed4258a300b6ee3258a300b6ed3258a3034edc3258a30004ff7158a30024fc7158a300067f5158a300067c5058a30105be7418a30005bd7418a3004eee6218a30006ed6218a300cdfa7018a3034ddf748ca30435dd748ca3000dde728ca3000fce728ca3034fce628ca3034edd628ca30007cd628ca30265de718ca3042f5f518ca3034fda708ca30005dd708ca3034fd9708ca3000ede608ca3000fda608ca3042f5c508ca3002dfa70d863010d7e75986300057d7598630006f76198630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc7458630056de4358630006dd4358630004ff725863004cfc7258630006de3258630056dc32586300067f5158630056f63158630056f53158630266dc31586300067c5058630056df305863010d7e75186300057
  | 23 => 0x77a70d865003d7a70d86500767e60d86500777a60d86500657d76986502057f749865011d7e74986500057d74986502057c74986501157e73986500057d73986502057c73986502157e72986500057d72986502067f619865000777619865020e7e609865008f7a60986500057f745865011d7e74586500057d745865011d7c74586500067f64586500067e64586500067d64586500067c64586500057f73586501157e73586501157c73586500067f63586500067e63586500067d63586500067c63586500057f72586502157c72586500067f62586500067e62586500067d62586500067c62586500077761586502067e61586500667e60586500677a60586500067f74586500067e74586500067d74586500067c74586500067f73586500067e73586500067d73586500067c73586500067f43586500067e43586500067d43586500067c43586500067f72586500067e72586500067d72586500067c72586500067f42586500067e42586500067d42586500067c42586500067f32586500067e32586500067d32586500067c32586500067f41586502067e41586500067d41586502067c41586500067f31586502067c31586500667e70586500667c70586500067f40586500067e40586500067d40586500067c40586500067f30586500067c30586502057f741865011d7e74186502073e741865011d3e74186500057d74186502073d74186500053d74186502057c74186501157e73186502075e73186501155e73186500057d73186502075d73186500055d73186502057c73186502157e72186502076e72186500056e72186500057d72186502076d72186500056d72186502057e71186502067f61186502077661186502067d61186500077561186500757e70186502077a70186500757a701865020e7e601865003f7a60186502057f768c6500057e768c6502067e768c6500047e768c6500057d768c6502067d768c6500047d768c6502057c768c6502057f748c65011d7e748c65047d7d748c6502057c748c6501157d738c6502157e728c6500057d728c6502057e718c6502067d618c6502075f318c65011777318c65020774318c6500057e708c6500057d708c65020e7e608c65019f7a608c6501175c308c6500057f764c6500057e764c6500057d764c6500057c764c6504757f744c65011d7e744c6504757d744c65011d7c744c6502057f734c6501175e634c6500075d634c6501175e434c65046f5d434c6500057f724c6502157c724c6500075e324c6501175c324c6501157f714c6500067d614c65011777314c6502075e314c6502075c314c65011774314c6500057f704c6500057c704c6503d67e604c65018f7a604c6501175f304c6502157f76c86500057e76c86500057d76c86502157c76c86502157f74c865011d7e74c
  | 24 => 0xd72d8e500076d72d8e500056d72d8e502057e71d8e500057d71d8e504957e70d8e500077a70d8e504957a70d8e5010e7e60d8e5010f7a60d8e501157f7658e500057f7458e5011d7e7458e500057d7458e5011d7c7458e500067f6458e500067d6458e500075f6358e501167e6358e501167c6358e501175c6358e501165c6358e500057f7258e502157c7258e500057f7158e502057c7158e501175f3158e5001d7c7058e500fe7e6058e500ff7a6058e501175c3058e500057f74d8a5011d7e74d8a500057d74d8a5011d7c74d8a501157e73d8a500057d73d8a501157c73d8a500067f63d8a500067d63d8a502057e71d8a500057d71d8a500a57e70d8a500077a70d8a500a57a70d8a500d67e60d8a500d77a60d8a500c57d7698a502157f7498a5011d7e7498a500057d7498a502157c7498a501157e7398a500057d7398a502157c7398a502167f6298a500076f6298a500066f6298a502176e4298a500076d4298a500076f3298a502176c3298a502057e7198a500057d7198a502c67e6098a500ef7a6098a500057f7458a5011d7e7458a500057d7458a5011d7c7458a500057f7358a501157e7358a501157c7358a500067f6358a500067d6358a500076f6258a502167e6258a500076e4258a500076d4258a500076f3258a500076c3258a500057f7158a502057c7158a500c67e6058a500c77a6058a502157f7418a5011d7e7418a502173e7418a5011d3e7418a500057d7418a502173d7418a500053d7418a502157c7418a501157e7318a500057d7318a502157c7318a502157e7218a502167f6218a502176e6218a502167d6218a500076d6218a502057e7118a500057d7118a500d57e7018a502177a7018a500d57a7018a502c67e6018a500a77a6018a502157f768ca500057e768ca500057d768ca502157c768ca502157f748ca5011d7e748ca5048d7d748ca502157c748ca501157d738ca502157e728ca502175f328ca501176f328ca502176c328ca502057e718ca500057d718ca501175f318ca500057e708ca500057d708ca502c67e608ca501cf7a608ca501175c308ca500057f764ca500057e764ca500057d764ca500057c764ca504857f744ca5011d7e744ca504857d744ca5011d7c744ca502157f734ca501157f724ca501176f324ca502175e324ca502175c324ca501176c324ca500057f714ca502057c714ca500057f704ca500057c704ca503d67e604ca501bf7a604ca500057f74d865011d7e74d86500057d74d865011d7c74d86500067f64d86500067e64d86500067d64d86500067c64d86501157e73d86500057d73d86501157c73d86500067f63d86500067e63d86500067d63d86500067c63d86502157e72d86500057d72d86500067f62d86500067e62d86500067d62d86500067c62d865003d7e70d8650
  | 25 => 0x81211eef421181210067c50181210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067d43594210067c435942104e7f725942104e7e725942104e7d725942104e7c725942104e7f425942104e7e425942104e7d425942104e7c425942104e7f325942104e7e325942104e7d325942104e7c32594210267f71594210267e71594210267d71594210267c71594210267f41594210267e41594210267d41594210267c41594210267f31594210267e31594210267d31594210267c31594210267f21594210267e21594210267d21594210267c21594210067f70594210067e70594210067d70594210067c70594210047c70594210067f40594210067e40594210067d40594210067c40594210067f30594210067c305942104e7f205942104e7e205942104e7d205942104e7c20594210267f10594210267e10594210267d10594210267c1059421004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21014fe7458c21004fd7458c21014fc7458c21024ff7358c21026df7358c21126de4358c21006dd4358c2104cfe7258c2104cfc7258c2104ede3258c2104edc3258c21024fe7158c21024fc7158c210267f5158c210267d5158c21026de3158c21026dc3158c21004ff7058c21004fc7058c210067c5058c21126df3058c21004ff75980210067f759802101cfe7598021004fd759802101cfc75980210067c759802101c7c7598021004ff7498021014fe7498021004fd7498021014fc749802100cfe7398021004fd739802100cfc73980210267f51980210267d5198021026fa70980210067c5098021006fa4098021006f9409802104efb209802104ef82098021026fb1098021026f81098021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021006bf7458021004bf7458021014fe7458021004fd7458021014fc7458021006bc7458021014bc7458021004ff7358021006df7358021004df735802100cfe735802100cfc7358021006dc735802100cdc735802104eee4258021006ed42580210267f51580210267d5158021026ef2158021026ed2158021026fb70580210067c5058021006fa4058021006f9405802104efb205802104eec205802104ef82058021026fb1058021026f41058021026f810580210057f74d8e5011d7e74d8e500073e74d8e5011d3e74d8e500057d74d8e500073d74d8e500053d74d8e5011d7c74d8e500067f64d8e500067d64d8e501157d73d8e501167e63d8e501175e63d8e501165e63d8e501167c63d8e501175e43d8e500075d43d8e502157e72d8e500076e72d8e500056e72d8e500057
  | 26 => 0x4ff7498221014fe7498221004fd7498221014fc749822100cfe7398221004fd739822100cfc7398221024fe71982210267f51982210267d519822122ef72198221026f42198221026fa70982210067c5098221026fb1098221026f81098221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221014fe7458221004fd7458221014fc7458221004ff735822100cfe735822100cfc7358221006ee4258221006ed4258221024fc71582210267f51582210267d5158221026ef2158221026ed2158221026fb70582210067c5058221026fb1058221026f8105822100cfe76d8d2113ede63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d21024fd72d8d2113edf32d8d2104cfd71d8d210067f51d8d2113edf31d8d21004fe70d8d21004fd70d8d210067c50d8d2113edc30d8d2113edc6358d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d2113cff7358d21006df7358d21154ff7258d21006ef7258d213b6de3258d213b6dc3258d2116cff7158d21006f77158d210067f5158d21004ff7058d21004fc7058d210067c5058d21024fc764c921006df634c92100edc634c921005f7714c921025f4714c92104fe4214c92101e7f76545212567e765452114e7d765452101e7c765452149e7f64545211ae7e645452149e7d64545211ae7c64545210067f63545211a67e63545210067d63545211a67c63545210076f72545210076c72545210267f62545210257f715452114f7771545210267f61545212577721545210276e21545210276c21545210277421545210276421545210057c705452102777105452100cff764c52113cfd764c52104cfc764c521006df634c52100edc634c521005ef724c52104dec724c521027e4214c52114d7e75d81210057d75d8121004ff75d812101cfe75d81210067e75d812101c7e75d8121004fd75d81210067d75d81210047d75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d812100cfe73d8121004fd73d812100cfc73d81210067f51d81210067d51d81210067c50d8121006fb60981210057f755812114d7c7558121005bf7458121145bc7458121005df735812113ddc7358121145be7418121005bd7418121006f96018121004ff751812101cfe7518121004fd751812101cfc7518121004ff7418121014fe7418121006be7418121014be7418121004fd7418121006bd7418121004bd7418121014fc741812100cfe7318121004fd731812100cfc73181210067f51181210067d51181211eef721181211f6ee21181211f6ec211
  | 27 => 0xc30596212567f20596212567c20596210267f10596210267e10596210267d10596210267c1059621006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf5359221006be5359221006bd5359221006bc535922115ebf72592214a6be7259221006bd72592214a6bc7259221006bf52592214a6be5259221006bd52592214a6bc5259221006bf32592214a6be32592214a6bc3259221026bf7159221026be7159221026bd7159221026bc7159221026bf51592210263f5159221026be5159221026bd51592210263d5159221026bc5159221026bf3159221026be3159221026bd3159221026bc3159221026bf2159221026be2159221026bd2159221026bc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006be5059221006bd5059221006bc50592210063c5059221006bf3059221006bc30592214a6bf20592214a6bc2059221026bf1059221026be1059221026bd1059221026bc1059221004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e21026df7358e21006df5358e21156de5358e21006dd5358e21156dc5358e21006df4358e21156de4358e21006dd4358e21156dc4358e21156df3258e21024fc7158e210267f5158e210267d5158e21026de3158e21026dc3158e21004ff7058e21004fc7058e210067c5058e21156df3058e21156dc3058e21006df7558e21006de7558e21006dd7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e21006df7258e213b6de7258e21006dd7258e213b6dc7258e21006df5258e213b6de5258e21006dd5258e213b6dc5258e21006df4258e213b6de4258e21006dd4258e213b6dc4258e21026df7158e21026de7158e21026dd7158e21026dc7158e21026df5158e210265f5158e21026de5158e21026dd5158e210265d5158e21026dc5158e21026df4158e21026de4158e21026dd4158e21026dc4158e21026df2158e21026de2158e21026dd2158e21026dc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006de5058e21006dd5058e21006dc5058e210065c5058e21006df4058e21006de4058e21006dd4058e21006dc4058e213b6df2058e213b6dc2058e21026df1058e21026de1058e21026dd1058e21026dc1058e2100cff764ca21024fc764ca211be7e654ca210067d654ca211b6be644ca21006bd644ca2100ede634ca21006dd634ca21005f7714ca21025f4714ca21004ff75982210067f759822101cfe7598221004fd759822101cfc75982210067c759822101c7c7598221
  | 28 => 0x932104eac2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006be5059321006bd5059321006bc50593210063c5059321006bf3059321006bc305932104ebf205932104eaf205932104ebe205932104ebd205932104ebc20593214b6bf10593214b6bc1059321004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21014fe7458f21004fd7458f21014fc7458f2104edf7358f2116ede5358f21006dd5358f21024fc7258f2104ede3258f2104edc3258f210067f5158f2116edf3158f21004ff7058f21004fc7058f210067c5058f2116edc3058f2101e7f765472101e7c76547212567f64547211ae7e64547212573e64547211ae3e64547214ae7d64547212573d64547210063d64547212567c64547212567f63547211a67e63547210067d63547212567c63547210076f72547212576c72547210267e62547210257f715472117f7771547210267d61547210277641547214af7541547210277631547210276e21547210277621547210276621547210276c21547210057c705472102774105472100cff764c72104cfc764c721186be644c721006bd644c72100ede634c721006dd634c721005ef724c72104dec724c72100775514c721004ff759832101cfe7598321004fd759832101cfc7598321004ff7498321014fe7498321004fd7498321014fc749832100cfe7398321004fd739832100cfc7398321024fe7298321024ee72983210067f51983210067d51983211feee219832104eec219832104efa70983210067c509832104eef209832104efb209832104ef82098321004ff75583210067f75583210047f755832101cfe7558321004fd755832101cfc75583210067c755832101c7c7558321004ff7458321014fe7458321004fd7458321014fc7458321004ff735832100cfe735832100cfc7358321024fc72583210067f51583210067d515832104efb70583210067c505832104efb205832104ef820583210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596211667f72596212567e72596210067d72596212567c72596210067f42596212567e42596210067d42596212567c42596210067f32596212567e32596212567c32596210267f71596210267e71596210267d71596210267c71596210267f41596210267e41596210267d41596210267c41596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210067e70596210067d70596210067c70596210047c70596210067f40596210067e40596210067d40596210067c40596210067f30596210067
  | 29 => 0x4ff74d8931014fe74d8931004fd74d8931014fc74d8931024fd73d8931006ef52d8931006ec52d8931006ee42d8931006ed42d8931156ee32d8931156ed32d89313b6dc32d89310067f51d8931004fe70d8931004fd70d89310067c50d8931185be7498931005bd7498931006ef629893113df5719893116df7715893118d7e75189310057d751893104eee6218931006ed6218931024de768c9313b5df748c9314cddd748c93100dde728c93100fce728c9313b6df628c931007cf628c9313b7cc628c931025de718c9313b7d6718c9313b7d5718c931025dc718c93100edf618c93100fd7618c9314c75f518c931005dd708c9314c75c508c93101e7f76545311a67e76545311a67d765453101e7c76545314be7f64545311ae7e64545314be7d64545311ae7c64545310075f73545311a75c73545310267f63545311a75e43545314bf5d43545310067f62545312567c62545310075e32545311a75c32545310257f715453118f7771545310267f61545311a77731545310275e31545310275c31545310277431545310275431545310277421545310057c70545311a75f305453102777105453118d7e75d81310057d75d81310077850d8131004ff75d813101cfe75d81310067e75d813101c7e75d8131004fd75d81310067d75d81310047d75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d8131024fd73d813104cfe72d8131004fd72d81310067f51d81310067d51d8131006fb50d81310067c50d8131006f850d81310067850d813107efa30d8131006fb60981310057f755813118d7c7558131005bf7458131185bc7458131005ef7258131005ec7258131006f96018131007785018131004ff751813101cfe7518131004fd751813101cfc7518131004ff7418131014fe7418131004fd7418131014fc7418131024fd731813102ede4318131006dd431813104cfe7218131004fd7218131006de321813102edc32181310067f51181310067d511813125ede311813125edc3118131006fb50181310067c5018131006f8501813100678501813102edf301813102ef93018131006bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf5359321006be5359321006bd5359321006bc535932104ebf725932104ebe725932104ebd725932104ebc725932104ebf525932104ebe525932104ebd525932104ebc525932104ebf325932104ebe325932104ebd325932104ebc3259321176bf71593214b6be7159321006bd71593214b6bc7159321006bf51593210063f51593214b6be5159321006bd51593214b6bc5159321006bf31593214b6be31593214b6bc315932104ebf215932104ebe21593214b6ae215932104ebd215932104ebc215
  | 30 => 0xd73181510067c73181510067f43181510067e43181510067d43181510067c43181510067f72181510067e72181510067d72181510067c72181510067f42181510067e42181510067d42181510067c42181510067f32181510067e32181510067d32181510067c321815103e7f711815103e7d71181510067f411815120e7e41181510067d411815120e7c41181510067f311815120e7e311815120e7c311815120e7e211815120e7c21181510067f40181510067e40181510067d40181510067c40181510067f30181510067b30181510067c301815100678301815120e7f101815120e7c10181510067f74596310067e74596310067d74596310067c74596311a67f73596311a67e73596311a67d73596311a67c73596311a67f43596311a67e43596311a67d43596311a67c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067d42596310067c42596311a67f32596311a67e32596311a67d32596311a67c32596310267f71596310267e71596310267d71596310267c71596310267f41596310267e41596310267d41596310267c41596310267f31596310267e31596310267d31596310267c31596310267f21596310267e21596310267d21596310267c21596310067f70596310067e70596310067d70596310067c70596310047c70596310067f40596310067e40596310067d40596310067c40596311a67f30596311a67e30596311a67d30596311a67c30596310267f10596310267e10596310267d10596310267c1059631004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a31026ef7258a31006ef4258a31006ec4258a3113eee3258a3113eed3258a31024fc7158a310267f5158a310267d5158a31026ee2158a31026ec2158a31004ff7058a31004fc7058a310067c5058a31004ff75982310067f759823101cfe7598231004fd759823101cfc75982310067c759823101c7c7598231004ff7498231014fe7498231004fd7498231014fc749823104cfe7298231004fd7298231024fe71982310267f51982310267d5198231026fa70982310067c509823106ef93098231026fb1098231026f81098231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff7458231006bf7458231004bf7458231014fe7458231004fd7458231014fc7458231006bc7458231014bc7458231004ff725823104cfc7258231024fc71582310267f51582310267d5158231026df3158231026dd3158231026fb70582310067c5058231056fa3058231056dc3058231026fb1058231026f81058231004ff75d893101cfe75d8931004fd75d893101cfc75d8931
  | 31 => 0x89511657e76189512557f74189511ad7e74189510057d74189512557c74189511a57e73189510057d73189512557c73189512567f62189512576e62189512567d62189510076d62189510066d62189512576e42189510076d42189510076f32189512576c32189512e67f61189511377761189510057e70189510057d70189512557f768c9510057e768c9510057d768c9512557c768c9512557f748c9511ad7e748c9514dd7d748c9512557c748c9511a57d738c9512557e728c9512575f328c9511a76f328c9512576c328c9510257e718c9510057d718c9510257c718c9512e67f618c9511cf77618c9511a75f318c9510057e708c9510057d708c9511a75c308c9510057f764c9510057e764c9510057d764c9510057c764c9514d57f744c9511ad7e744c9514d57d744c9511ad7c744c9512557f734c9511a57f724c9511a76f324c9512575e324c9512575c324c9511a76c324c9510057f714c9510257e714c9510257c714c9513fe7f614c9511bf77614c9510057f704c9510057c704c9510057f74d81511ad7e74d81510057d74d81511ad7c74d81511a57e73d81510057d73d81511a57c73d81512557e72d81510057d72d815108e7f61d815108f7761d81510077b30d81510077830d81510057f74981511ad7e74981510057d74981511ad7c74981510067f64981510067e64981510067d64981510067c64981511a57e73981510057d73981511a57c73981510067f63981510067e63981510067d63981510067c63981512557e72981510057d72981510067f62981510067e62981510067d62981510067c62981510657d71981510077571981510657571981510767f619815107777619815103d7e70981510067f60981510077b60981510057f74581510073f74581510053f74581511ad7e74581510057d74581511ad7c74581510073c74581511ad3c74581510057f73581510075f73581510055f73581511a57e73581511a57c73581510075c73581511a55c73581510057f72581510076f72581510056f72581512557c72581510076c72581510056c72581510757f71581510077771581510757771581510667f61581510677761581510077b60581510067e605815108d7e76181510057f74181511ad7e74181510057d74181511ad7c74181510067f64181510067e64181510067d64181510067c64181511a57e73181510057d73181511a57c73181510067f63181510067e63181510067d63181510067c63181512557e72181510057d72181510067f62181510067e62181510067d62181510067c621815103e7f611815103f7761181510067f60181510077a60181510067d60181510077960181510077b30181510077830181510067f74181510067e74181510067d74181510067c74181510067f73181510067e73181510067
  | 32 => 0x4eedc32d85320067f51d853216ef631d8532004fe70d8532004fd70d85320067c50d85321bd7e75985320057d75985321b5be7498532005bd7498532006f761985321bd7e75185320057d7518532026f66118532006f561185321bd7e75d81320057d75d8132004ff75d813201cfe75d81320067e75d813201c7e75d8132004fd75d81320067d75d81320047d75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d813204cfd73d8132024fe71d8132004fd71d81320067f51d81320067c50d81320defa30d8132006fb60981320057f75581321bd7c7558132005bf74581321b5bc7458132005f77158132005f47158132006f96018132004ff751813201cfe7518132004fd751813201cfc7518132004ff7418132014fe7418132004fd7418132014fc741813204cfd7318132346de3218132346dc3218132024fe7118132004fd71181320067f51181320067c5018132096f930181321a57e76d8d510057f74d8d511ad7e74d8d510057d74d8d511ad7c74d8d510067f64d8d510067d64d8d511a67e63d8d511a75e63d8d511a65e63d8d511a67c63d8d512557e72d8d510057d72d8d510257e71d8d5101d7d71d8d5119e7f61d8d5119f7761d8d511a75f31d8d510057e70d8d510057d70d8d511a75c30d8d510057f7458d510073f7458d510053f7458d511ad7e7458d510057d7458d511ad7c7458d510073c7458d511ad3c7458d510067f6458d510067d6458d511a57f7358d510075f6358d511a67e6358d511a67c6358d511a75c6358d511a65c6358d511a75e4358d510075d4358d510057f7258d510076f7258d510056f7258d512557c7258d510076c7258d510056c7258d514e57f7158d51007777158d514e5777158d5118e7f6158d5118f776158d510057f7058d510077b7058d510057b7058d510057c7058d51007787058d51005787058d510057f74d89511ad7e74d89510057d74d89511ad7c74d89511a57e73d89510057d73d89511a57c73d89510067f63d89510067d63d89510076e42d89510076d42d89510076f32d89510076c32d89511667f61d89511677761d89510057e70d89510057d70d89512557f74989511ad7e74989512573e74989511ad3e74989510057d74989512573d74989510053d74989512557c74989511a57e73989510057d73989512557c73989512557e72989512567f62989510076f629895114d7d719895125775719895114d7571989512e67f619895117f7761989510057e70989510057d70989510057f74589511ad7e74589510057d74589511ad7c74589510057f73589511a57e73589511a57c73589510067f63589510067d63589510076f62589512567e625895117d7f715895100777715895117d77715895114e7f615895114f7761589510057f70589510057c705
  | 33 => 0x5000000800b0010038000002002000800003000180f402e005029801002a005002004c00e008001802000400000a8010038001007013c004000003800000400000500800000030000044000031000802400c003000000000200600b0044000000009002c00a0000000018004003000001800000200280100040020040008004002000004400401c000000002000b001001c000007004802000201300100180080050018004006003016802c000005013001006400100200000260040008004034003025800401e000000002c00000700a007002e018006000001000f007007402602300380000120000000008030003009002809400c015000400600f0018024000000004011801800300400040b4000000000401a00c0050018002000010000001c001000800c01e010004000001003f0000014002002002811000000000380b4000000001808c00201f0010000014011000020c00200f000800800200c0060048004002000000001e00b00280000080010018078040000000806800000c002001000000b002000800000000180d8000025006800002e008002002402c00c00200bc066004015004c01200300200000000000018004006006000800c01605f00c804c03c00100100140020190000034002006005000003e00501d000000200500100a8000000000006c0000210000000006000003800400c00400a0020012009002004402400001f803802400500300000020000010048018000002801801200100880180020000000018002001002002801a003002800001c00b00b8004000010001800400204200580480060070070050048003004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632014fe7458632004fd7458632014fc745863204cfc725863204ef771586320067f515863213ef6315863204ef7215863204ef42158632004ff7058632004fc70586320067c5058632004ff759823201cfe7598232004fd759823201cfc7598232004ff7498232014fe7498232004fd7498232014fc749823204cfe7298232024fe7198232004fd71982320067f519823204efa70982320067c50982320cef9309823204efb209823204ef82098232004ff75582320067f75582320047f755823201cfe7558232004fd755823201cfc75582320067c755823201c7c7558232004ff7458232006bf7458232004bf7458232014fe7458232004fd7458232014fc7458232006bc7458232014bc745823204cfc7258232004ff7158232024fc71582320067f51582320b6df315823204efb70582320067c50582320b6fa30582320b6dc305823204efb205823204ef82058232004ff75d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d853204cfd73d85324eede32d8532
  | 34 => 0xc00402a00000740180210060000008005001800000c0000000004006000001001800400c000800801e00800a0054064001000802400a008001801c0040000070008006000001802401c04601300200000050070000004002002001000200300080400000030040018058000019001c0060070038044006005007000001800000600f403400000000bc0220070000008000006002000402e0000058004000003002003000e0000040004008000000004800000100200a80100050020000008003001800400e000000800800c027009801800a000003800000000701b0018060001003801000e000000800001e003006000400e003005000003c001011805401400c002000002800f001001001400600300480000050010000000008000000004c00000f00040000000000054000022002801803000100a000c00400001600a000200000e80240040000058000014004015801c03a0340000080014000000000801001d0060008034000000802400201c00100000060030008020020009000000001800800080a4004004000000400400e0020004006005001000c000009002800400a038001000400c019000001003c012001000805c00a002800800600a0000024038002005800000400400400440160030000004000002000000402e000002000c01a009000005c00000200400000020010000000004003003003002c0000168024000005000000402a0000000024000000000800401e01b011800000c00000800000000010000000028003000802c00000a000000801001f00a0004004002001800805600a003000400e001000001c068003001000c000006000000000e000004000c0280090060148006000002004402000000d801400400a002000000200f000000800200e000004c01e009005800c008014007800403e007004809000a000000806000a02d0010004010001004805001a00d015000401c000008000800a007018000400e011014809400200500380500180000088078008000009804000200300d801c00000000080140160000010020000002001807400800a000800401002100e80000020000000004030006003002c032000001005c0020030018014076001003000000200800000000000080000000006000000009800200b003801c002015002000401c0010050004018000001802c004004002000800200a00380ac0080070018000024005001001008800e006000403c00000300140160000048018002000003002c02e00b000000c00200400b00100000090000084006006001009c0000030030010006003002800800400300900000020050000000002004002002c03400b000802800600200100540480040078000020003003802000e00400b80480020020000028008002009801400e009000000000c002002000400600b
  | 35 => 0x6003800c0220030020004002000000800002c013005000401601900280b400000000080d80100050028014006005000000000200400d0028006000000018400c00f00000b80000070000008000000002000000801e000005000a00200000b8006014000002c02e02100080180020110000088002005001800000401200080040100010000000000000003802c01600a01f001c00401400180040080050000000012001000002400a0000098010000006009000400a02100080b400800000c000000400e000000007e00300300000020000000044002008008000400400b0040010000001000003c00000c004801400e00601a80000a20210000034002003001801000800b001000c01c004000002000400700900040080060008014002006003000400201c00b800001000200280480080030000000012001000001c00a00400c002400201400001b400a01000600b000200800b80180060220000000006028002000c0080070008008000003004800401e005000800800000f0000044038007001800000000f0000074004008000000000800000b800801200800e002000200600a000800200a0018054016015005800c00200700000100140060010014000000000000000c0030018054008004000801c000000003001001a00300000300000000028008004003001004800400001300001c000200000000020040000028002000000000c000000009800800000a0008024000001001000800400f008804400a0020008004000000000800c00a035007808400601700080200000030078074010004002800800e001000003000c004002002c04c000000801c000000001001c004001000804802c0000030018000000000001801a002023005000800700b805c00000500d000c0000060018038014004012801400400b006801401c046000010c0340380000004000014000800405000d00480140400000030000004025008800000e021000000002e000010800804000900c8068022002015801802801700100140180090010000008001000803c00a013000000400c0050028008000020001003400c007005801000a0030000008002002005800c00401f000003001000000c800800200700d004c010000007000002a00c000803000000100b802807200000c8004006000000808c0000210018014002000001803c000009000000400200f014800002001900b006800e0000018058000012007800002c00e00380c000002b000800400800901b006400a00000180b0002017001000001a002002003c012012000001003a0030120000000005002001400000a002800400a002002000802e004005002801200b001802800600b00700140120000000000000002003800002a0050000014000005004000400002b00000080000020000084000008007800
  | 36 => 0xa463278f0158212a70f880004aa421e3f286db24f16291b9924317fc35b0000a85313815f4b8033a078400047bc00000003430000000384d5050fe91ad0f5cae00e682dd377c8e9230cd78112486a00007eb30311d90a705071f04a071ec122122a06c8275c5431340aea3b74c6a55004e338543131ef8fcd0f0d50617915480440f8f00006161720dcf0094e1b195d05625e48184238ace565c70055bc8e048a80fe4da51c62f0523b51413984d9c6dd00000002e5868c0000e831d600000b7029243654f8181c0003ed80001fb41d9117861446b913018f47452b1ce9c4220bfb23400e33e85044018800006e050a0b9961a27e138800000004e5400035cc00047311e3535c2684f246d4000000020b80000e649fa03fc5022840fa457ed4b600000000f340003114b0c00ed4ae000000000001bb0000000000029b4ebd3c208a4c6f24d93bb3cd945c20f47d100007991c9024d20fceb1000000900009a82f7c8051efc7af4c8007841a400034740a1021437424c5182020d25745840000000aaa3580000474cda4024953f3064691000000039f0c3c3ddd17900004c40000000456c00019a800045b80000001203000080f3334000000000010154e72a20000436cf8508600000078dad000000043c01770b541e70000000000014938a95590210d4b2b5424413b8688239d5562525291390960516c917f47591c0325cd593874bff0954d7214c07f305bd4da31cc61c1794c4d5580639551d2b454a40dc0390d623b312bb4284c3422b827e07d8e6c0cc55a60cbc0e50e00d6e236851930690a029e8005000000400e01201080080020130000000040004000000c0000080040020008001003006000001600180a400c00b0028004008002004008c00c0020018104064004005001000c001005000800a001000000c00200c00280b401a02300380040280130000004006006000001000201e00a80a404e003000805008a00100000a400001600080040000030030020006000000802000000d0010000012007001802000001f00c800804a001000809000e007004000000a000000000801c0030000074012006000000c0020120028000006000004000801000000e000003000001a0004004009000001400000300000000020020018000000003002000000a00000b800003e001009001c06e0010000000006000012002c0000b00010014016009000000400800800480ac00c0040010050020002001803c00800401a000000e005000000404c019002000406000500280000000070098000008000000000401a00000200b0042000003800c00c02200000180080030000004010002015801800a00c00000ac00800a00000040040310000004026001018001c000010003804c008001000016800600800d80000040060018018008004000000001400
  | 37 => 0x564800009f08953c48a0014a14d50000a4540fc0d407b111e563cac318340000c2c7d835ac000077040739480002ef800040010322f5800045c561d448c3260000a9730ec0004af438c408c19a0000c204bd4b894a58c8f527800000000002898c14403434139a0c74000036216dc0002a2c00000007a9000000007dd30a0c310be51b87de1020f69506807100007c65510e2c2860de63c2c5bb01b072504c0d704f4128808806c757b50da12ed3e925ed3cf0000fc947408de522c7482250b211d68afb55cc34d0558da63d24ff9032d5b44b3d5f6000049b37e95aa48a40004bfc18a547400032d529825bc3be000018000002fe294d12900004f60000be63944c980000a734cb4e69340808d536064f4cb923d53141e22f6c000357d3ff0f3c000000008c0000f190000042000064935bc2f646a4968056800054d800000000d719500a84664f25371cde92a842510160fe7000037735a89b03d4d00f32386134f4509c104c69045d40530000000000000044e139600006610000d55549533f228cd9052c83443d2843528a94262ea065500000191b394ed02ccab605a4b8e13c52d11a5000042c097f00000aa06e91130ec8000000000038d8f17347022337bd0d126644ca4d54f5054cc8b8084c7bc0914ae91620a83065c1ac5554af404b42e1353ce30000152300000003720dbb3f4c2561e1d47f4b512400ee14ff3308d21171076047ec00005e51fc1384e7d241898c1ca8ce63ab48c22d8518a0000565575c2a5280c814536c01b10ec7754cccd874a290eb37d0c511bcd50856e8a8f30d48c731014d12c70941000105714f4c6208343671890bc239d4d54161425a4a4d24a4425097462410710100d11388f460e18cf30f58d743924b4910905fc4f20ee60748a6315286ef4f611204fb931539a84283c4d013054002208a15c31d6c89f4f54623468035945e027b58bd56635792a445d8c152d942ea2f683881b780f101cd0140098de808cc0000b0cc9400001540000000430823222243680000000000154f521c5c23ee54ba2fd80000000cc14ca010f13cc5fa00000000a295984fa0bea1adc3d000007ca0000b5141a8a39000000024b40002c0035a30b80000000000401800018e00001114e283930000248400017000000001466399c73412180001b9ca740000a994a38a3c00007aa039d19e0000099383155100009904e7428447a0f081c0d30b5724d9435d93252c4d164174caac1a00fde05a937601686184e9c0005860f6a165d4f612752fa3c511de47b8000302c76f2b30f2c26114393d9415738802c54e5c91f06902c93ae4a1325206d336b000026c44470000dc0000000000010a23d2c0000000a2b4e8cdd00000c5b2ad0851139c00002dcdaf341c0002ab8f2e1ee81403c1039354489190a680002360000060cc5c2538
  | 38 => 0xb6d4748b0600003230b415dd14186832ae94751474bc33078317183830e328908240106253f7053c0f1c12e067d36d5358ef9096c08a077cf3d000000000008383e30fbe0618a44000087b4f990e647c8d0a1bc93820ab00243840c2d1af8fc031c84dc1ded2a200a42744f292f12808f4f334c98d47448ef28b8241445c000219400000015d30ef4c6025f83730001354406000035241bc14a502d3aa8e3251c059f3df0e14031cc03256431034ccb5d34790ba3b38e6d3e64ef52ca81992e207171220aad0fcc5552e3d0b91c6cede49e0e544620b844f1d4562d8800055694cb175c00000011af542416811d12da000116c37885760000000331c5674d4c5c726005112a40dcd000094231483540000000546d3682b6082500000003a992b60000e4b07a89a124f52f4102ce463c08c0f02f94d94d004f853387f505c0d110b8d12138e800000008dc1fa49f9055400049ccf2a0a3552d06dc015479d5cd1b3048200002e00000707421462646c0d13000000000000381088000439c000000138e261d0e951c812b48d55fd0cf15d81e0d159565148903a531400011062a1c000000009512d4e5b00013241908b05000000000000000000b16416107809840004b400000000b6335180000000bef0000280410014e000146b1a654312f5c21608e543216b40f452a80003368eea10f154218002a300007560038829505cbe2071c4172c98a253d2039051f01650000edb42a54e53fe123611b00000cccf372d4005216e0ad7591814c54552ce38711732e40a9f0000000000000054ac89e0000000000137e000000000000000000fe5486800000010de090800049982400efc8791b291cb31c0fcc3cf056836482a8094d54e29c81592d780002be800003d859556853b7448800049200004790e95000060a29f47ea0aecebe25c4905341061b1a342a03b414251af002d00000003ed53082f34dda4fd45490000fe4120ce9b2e6828856fce5d40f8000112c6681de469557d487a24109a63fd95b304605a82088f5a2b415ce52284c2416d2820af0b74586c182417c000000132f4ef543f3dc40f92954da0460ce892b591153dc120048e00bd56f4ff026e872f4aa01350000eac1e300000000000000000000000004f58000273152e0000ecf1190886142d01d1d6400048c47283a346c4000000016951bb0ab81bd0a14000000129436691700cd4b5b1c400de382c9645194d1f503cb0d00008280000d8040d40000ee94a2206c000000000028d0de72848000119d09d00011804dac5e84e1c8832cc525d477cdc5337467145ecbec00011c23be037e520c3fb47dc0003dc9072000d5ac43353ae53d432e4ff807612b8b27279536427503ce58fd2460b2108b194102517991403d081ee34f801741b8ffa2424f7b2b3c44342b88600000499421800b
  | 39 => 0x60b3963c00008681bf0cc94458004567800046f146c092ce7a51780812e1c3f900005ea0000556200c6f056d90f314fd30309d89a341e48d93a384f25530928257c1c502b419639ecf5f0000f030000cdc5300b7f0614e08393c4c318d4e3c0000d19000054f1ff070100000004a78d090f9140b1c880000c802b000002f21ffd0e80c0cac800005a139f9061197507f00006d855d4000000034c14392c057a800003dc2cb0bfceb0000061d559400023d000016a539b2dbd35c00001c30000000079111400007b435044db2ee11840000e1608980002aec7a1177076800c54bf0754000129400000014734b4945703ed3db32591ec3de40004ca8e00290804d584c72b3614fed16640893b4437f4b7c0c3122840e4bd8ee423c50b444910e1326cc801c345e33aa00d0438d4c61d4d3b54181433454920f185439d2148bd210c43b400603db5120e3e537cf1638ece9144bd48c08f88ad06d537f33bd23a2a6c16b082493b00000004b1d1d455e530f00006b22a8132727ecef70d4c6723cf920d3cd123e00002370ff02d3091c00035f4439000000000012a548980000bb4bbb096016450d164227bd3ec3b9c0002f80b01524068b4d4000051d1345339433e00000614b9862e0000ea23530e18000025f31d4ee000a8aca073d5d00a900001504d0b00000000000000000000049793a500000002dc50a30404b36164800040e09c357311080000000368d05522b000032e400032b4ddb0c00e9902194801b3c9941a6d44a454c0bb52b400004452050000000052c41d5078a2d0b6d393000017f1189264107d58e34042be25840004578ed32e2c08f461d3bc1eb0e244cf80000971549587821f42c523927f4cc44d854040fc1609000000058500004774aec2a7159100000002c5106b2fa400022380f0084122c2d80bcb4a4000000002891c6452f00000f5343400004593e5292c00000010741ac00004dc8000584862c00000002d5c7fe3dac000000128d00012414c2400000000003ba43f101a4fc500000002a2527d000000047986e055402c0501c0440c9519d1248532093d50158991a53a28a091e7cdf131fd61c23490cc5101585213cc090f14583471c9df2b9492b072956b4ec00005720000208ce8c00005d0429cf684388e774ae0eae0dbc0004a64f780000000000067d0000fbc24412ea00006ba000000000000001d39588570847b19e816e4ec8903151cb2257980f8224844f501475c406c3ad00012eb49894d4183d2d308181260000ec82fdc766458c8a135fcfcb4bb8e0a54e502f01809351b2455a00000001990f830380e800d18ee522e83bc200805d22300001c253a2212424300010620000735252c8fc09510d244692831fbc97748701610f446ed13ad4a32604c4104090dd3b885530fa4976518c1880f680005074900000
  | 40 => 0x650890d2480700008c6021d4e63ad8633312c5ba1df49be34e852c3a2ca7e402d46122115b23eb87b11028250359d2563b8458241907b611b8e1215f53f80c78e733b343d93c802fa0d5445838b88641f0d1744e048f3433c8691c984d8300485d0000f8926ec9e4000007a338800011980004da8000000104f0ad89ff43d91aa446c1843028436409828711101d033783eb273cd0852f911f24787c23efd5b049c044d4d9819818b52bf14581e83d1c3a24414ca14d60c43311c67e3d642b722acaf758d8a8d00000000810d1b2ac400024e92fe0548bf902600004ee14850c6ccb3000102900009f755c80000000000000000016f072325d000054a09010cd095b27140000a60bd054e93734254782372c00000009530a3c5cd056c4e84c840003598e1953115710ac44a7000080a57c000000004bf0000b07000000000012ed41c0c2c0f4c8712828c10000057301a80000000423320c99348800004dc40001d2c0002dc13841d50d974f18d84215099e267d5d600092b12fc956e34bc67904640660b0959d2f94a8c01f47f0481865f20654c934492c134e00ca2fc5233000000003b935d003c94d11a44ff363906653055ec000043e000119b098088853f400000440000000d0c27f835e07580000da83cb24f863615fc5f953881060dec22a25a8000204470a0694a4707e80004de8d684cc42d9010400003b00000000c3d00000002d1800000000432ae102238f4000163430640ed4fc512400045f484e2b9000012c0473000068f0000437383c000212d3fa2040207581962503e899c4e780002b347e505285423ae116d000089c146c0000a84b531324307000000013780002d1c1c800014c8000073d00012f922dc0002bf40003364446000000020856031d4400000005f722e51b700007a024c13383900c44308c438189c71c50e939f0b5800013bc0002ac800048391310000301380d2b541ecfeb1d5c05c00c04bd1be400055fc0001ec8000000079000000c1343c000320470e1ed50412c6ce3f4bf00bc059c0000000cb419f000000009d503548ff17240004f340004a0149100000000acc9de2be011f000000024903560abc5442a9438529d53f60295378119530507503cc0a18f8646395954d315a91054cd80c48c953630bb11920c7e47605fb1bb91865104b7726c835d00007e34fc51e53209304012c9f10de4551549cf551ae49e633585933eed4b742bcb283fcd2424e70f432bd4000032400008200002cb80002644dc62034000000000052f4b8a3c7904a563000011545c10f6135216d0a861884ac400015220000a23417878427041d712d80000e5ca6a551800000000003c28a6d067800030bc92a306d2d8431c9072740a6101f0f52533c3722ae42c628dc9f54298aab126000046140000000e340000d3d000039e10e874
  | 41 => 0x130e314c14d4cf400042280002c0c3483f20a713c346403d5c0000c7d5df00000003eb00003e0088f50b85c32a50f44068cf1f00012fd00000003818c6728bc3bb54686b60f8cda102ad5573ee116000003043330000559c9402df82cc4560dd43998000274d4b51e9c9a50a741de01193d33cfd39106e41fe566d14f3e3800025ad40a2e988fb03cc382000000023895c4463ca15487910a4054dbd1de886c222c1a1000032c30e8b2300013172fb89d90989237370c296003441651a51331afcf0621b930d4af8d791df03693f04c002738d4a2048000000000000010ef1f24f5e3c6800000006a240a8a500071250397872c3644aed0000f2431193921abd42d2880fb446e092921d4ffc1f5d1c319dd2513f5453700000003a1d1b34f794e11cc4ce034d06d9524d2180000c7149e43ea1aecb584f0541651a019043c40002314729000059410b42ba1788baa3e4c61034189e73b2931c491c0004f681b32a01094124003e3aa40cf4eccd2436e50ff473833204147520a4c0000f54e1a4eacade276800039d95bb43502a60000d7c2f1800004fc1ff58640000000000557800051640002865100000084420714bc37ad3dc513c8fe1a701911b044da0000fc3374c7d6234c4e656dc6174588c2734506e249d496c26f52fb36dc00004940003c54a160b687b722d8bf34b1878f3b0017619ec0004720dd237654ef2950f6d33d07cc03ac000543ccfc16400000ab40004e9083b0000000560434f3520c024520afe20d40000828000000081d00dd22e04315074a24f0c294425d4ce885f0000c3734a10d63b24ced15b4b1a1560215000121f36e11f600000000a2c74f38c4e475298cb03a115ad5328000000065144455be06d138639b80000000000468445c411c00008e88174e3c0004a847f100000000000ec20000aa90ed4000050cd1601dd29d01ec23c064d3c33c3c0001bad4d30000ba14e14b2045bd3393a9400016180005428000269caee3dd0fe13244ce712cca6c1d1056f402452d190d04d2eb94983e611f32c60a1111c8000101818c226c3a1446000000000000c281a8073476a000000035a4f9654a917c2d4847a000156a2878d2b1600c3e05211a40050000000119c25cc97d2bf0000019118b0000a8112b46034cc123f2aa0ccf06f82364de45d24a149a21254b7620c124e08750ad46600743e1cc170f7495a23504af53cc899017cae83ced0f923315f31e60c664a2c2eb19bd39a3e5ca5a40e4f4c2838b59000089014414841ae010914247e61b70fba00004dd04c80003ae800039d10670a88b7a1eac0000bf5276123505211c400042ecd9c4c7ce57000096d00009cb00000003d9c66227885a6000141904f442f0b3c01029389921f90b330d84a6224b0a3d0000000350d05d00d8051045009a3a587cb139400013
  | 42 => 0x2a515122680004ea88cb27f03ec287cac63eaced711514eb0068d9554ecf2702c931228fd29541dc1fb37a82020000d98000114a2cdc6b31af4b730d1c71f3ef468e135507d1808000405c0002244755000000000000003bc4082319400000013231dcc12200000000aacbb60000898000000000004200e509562fd456a27b5604000050304bccd552a1422514844829800000725213525c0000ca896e36245b3307c0f2000031c2cf873f000000029a40722dac29757043890000b80110100700006b142404260000fdf3940f1d09d51ea0f2000047a558b1f3400003f087d577800024e0a3b30d87bb00004791b3463a209c85723742f145dd3c5202cd8238941952a68000000000035dcb252b700004320163498c5dd1c306c23f10de533c55ef14e537006d88db024c1e61e8c78606056274598f924770e552d90bfe0af43274a7cd1028e02644c44020481d15c0c506634d78d0314b81bf1f555264a8cb9c1810398000150e4c011da4e510fd43b0801286cd88000005920d934f3db820509c14b0451467331b8cbf000000020a92bc29207c5480529c104828e00002ec00000001fd8c57000000000015f82c780002e0866c2548000388c85c47e810a4f50a5727d08f02ed4000116c0b60b34db657a512c000145329d8000432c000000109f0000bbf49b14bb19581e000010c9000072d00000001d9527710c80000000194332924f4b20000000000037e496030600001f386f43b100003d14b0e010044e345cefc09e1190000000050180ea061ccdf148c9d100000001420000000162a26cc2f34abc3a62b9c58f069897c049d2044e311cf0f250ab0ea8b0f30a488a1dfcd304f845df0b5c51714f86054d24f881f740000000b7b0000e8135690fe118000056240004fe46d724343ca326855441f080824511cd1fe44c723f514740586a60a050b20fb457e3761577000067833409ea33b11c40aa80003f5893f3ff42b42ebc41c53a4f3319b878d3c3831512b000050703910c3400021640000000153169c00000014a500005ee000053a4b1118d07f50b62d593b10bdc0a34168f292d392ca227409f1fd140d1344d513ffc54d1040bc44f2c0005664dc107e0000040c00050484591e2157b162d1370ee46931b400cd176449427287d31f10e850ebd2dd49c5471204c4a40320b9d488d21700003832930c0d34fc6fe00000000001622000109e33446601ce407507e415c0d8159f29dc6d10000738000000000005243048b751e78ab3426c00044708462bfce371d015181024178097821735340010128f6351502fc4d5d0dc00000001b145b91a9c62a15e906d00b800033f4637430c00000007f252bc096000108f1a28cc8278400014304c600012f736e90a420c40000000c4926d05334b5800036289ac000000014488001d8d51300000
  | 43 => 0x3f23bd8e86246046b36b8c0e31acceb3d90c132a9857700004d200005aa0000419143c87237c0e5653b037d4c050d82de4c262ced16504a090c3fd00080930a7c2690eec2a290df09c8e2f4b154e00000000000060650f4d310e540790670b09469d4600000eee1934d2e0cad1b64268000000000026ac3525835261194871355885000ae545550f1578146103700015af497d2b000b00004a04b2b0ff4f9c1d04f8b37f056645a4480590462f08d0df826e40001728a3158f40b94c3000025d4a29410c49f17e07020c1400017cc8b0216cba704e13902e34000000000035095d1000051334f04872ad56002e489970d14bf41ecd45a480800000000004980eff0000f3221b4b8300003c218c80003b51601322073c2bc88aa4b3000023b534a2ff44c8000113604b14c7407cb290000b780d40294000109625749510000fd72eb018e328d60b17c903009b09eb0000433000050440e888d3f8ca2215e45ce16715fc37dcf56037c13143e07624d054964524ff125182de23940003b480004adc03a48653dd37c95b50d90ef024dc00055506a8000057b249800023c80004c4c5b5000083a39200004acd27a2a4433b42f03841e2cb9312841ad415158650a82190bd48400ac94a73349253583c3e81330c7630cd0bd2cb44aa579d15538a400a18494b34a696231d1c1d1029d13c126826900187ae1820ef424cc4b7251cdfd57540c600008e622d0309027031d16d8cd73bad5a430c0d7a587c000034c00000011194a6c7d0572d3100000e3958ad13e000086700ad53800004df5750e2b4c1d351000000009207fb2ef0dec29ac61e17592dc33846592fe018f17b001652692cb13c025900000001be02f436591fe2120b97000004f22000005584aa427d8d443498021072cc5a52700000000a3a414417d1ff4b8c00000004408cbb4e0d5305284000579436b000034e000000027b151f58b8b6e1c747ad0000ab018ac79d3174f4e00009200e8c27911f83a41ba46f75854591192942c233cbe452b15312e649114038fe631f00e84cad56456c55e013dc3575548be71128fd047f46204568e5a18f007051350c02ed12e708b8a7000000003ea46d5000112a35600003b68ba32b9925212e076d0518abc263866658a019d34ed4d207094105084e971824bcc34b563b318d5c002a4eb71e4ce014cb090f3f3caa239ac000385c08000011bf3d987bd0000302048107e000127f476c4932ee400001fc9c41df8aa33f1c6e147b40003fa8470263cbb7044c35c0b451012a482ef11dcedf24391930fe00dd2bcc6df21c002318a060b3a8c4a65020f234d382c41ee10a5367c3e039fc057248d12e43d01ce492ceef37f8b320b615ab14e136f3b711ff372934619fc03c2b6cdbc32310ca1a78e88000039b0db000000d400023e855f27cc00000006873
  | 44 => 0x2ff15a70000b95362c837400c4a323e0715135d42012d09b601589aa1a851964538e722a7442e3f6c9d645c938b2a9c6a012453a00dd802f3a4cfc605e814419690ac22a401f3acc92f0000560296c0945308cff5828f9f47ad5a32830192114804908510502a78299556c0b13a74392441d630069cd1531640001f882e932246f1398c3ab2770cf5000072752a46a44f4800007941aa00003e71380f2b00000000d09302253000021850c50c5947649c8ab72c2102c000000058cccee37fc2d41f48c84416413a1c2035138141742bbc36555f4601467c6193db010436a54f21bd43192b8ccfa1478f580a450fa0c3cad231b500a0000a0d3f88c9d0ca09c600001b2585856c000000000001db48593770000000128800000005f100015e11de02304511135534104b4d68db450bc2492f8426f0438496278d2ec1518cc52d308471cdcd180d60c114850a4d49a878e0ec08d5552c5cf27b800017bc36633f8b2c281020f21690fb0e7cb350c20fd84ed000050d869f4e34f2f2904815000162126254f71fa149554f4f9046680000001458191533b3af0fe04ae8282533553c21316453f511f924e44fe1fb14a4402045129ec1f432290451d0d442000000053a0ae100007143bf4e653a686aa13580004fdd03d062563119d00501d093f4000034a2abd61000000001a140004d8c0000001462301d1a607c017b000000025c00a208014b43ebd4f40000000000000033a8000564d54332f0141368915700e400000014350b280003c443c1074d05c0000d0e2e940002f200003dd531a3fb012908b000000000002d0d29741e95b82f000483fd400014500003c152452d70a962d2cb7c21989b84354ded460526f2f3c000000000058b0cb614accf200000002d7d38a000023106aced9000120c10fd14b00ccd6d49b40004b0c2953558f00162421222cc5e111d923010c012404ec00002b88774108d29285c00038cd15f12240001a2558746e8ca60000000500d5e400001150001139047906f363c79b00000002f2462900a117e2f8d4de25715f122941a9106925529485f43aaccf70000efe336c91d2bc102b11591b551f90f22a114f128c08b12afcc923ea007e3b189c85570b91000058a17f80000ad4000000000046ac00050500000fdc00000000fd51f512b32f4000000125456f0f8d16ac80c274873248404c11db0a645748bb00eb8bb217c0ce350601f22b2433d1ba15830000a6f235891721fc63026bc000000022d00000001cec0001d7d5a24755267441116b492548e45414002c488ca4b8d0925330caa3e6c5ae30c90b517f441e230414f3a8491213b442c27741230274e5847d457406c4da50f7ca6e2b745450c8420e166d19514eca590508c221b915eb25a458c440c0ed34c873314350b729a0a5f39910e02e18ea74a1cb7d54bd
  | 45 => 0x11be00001fc000000000014b800015db078d3ac5190d993b2ca5d57a000007d40004f8c00005c479229982111bfd402339000016904cf0b9c0b51da459841395040cb456b0000c061f5064b3154a2c3de804e3158d4019955840de826e1b9534848541eb4d0c00000000004f88e412b2c86f000110b2c10c041888000147144558e937c3778ec72780de430903dc0b90c4a43d48f727a481f231086b49d0b3a2a4c0d84b240001e5c85e0fd04a91aacc6c4b900b43ec129215706cb32655ff0000cb722144b21dd005e1f3d24d4fcc00040a05f538d40001c10d25392903631dc87810051e131785d53e8161740c456911a0bce0a4160713e90201d7482020d152c4820c900448a212d349d83ce456340cc0003df8505098ca78332c4424ab48f5000064c28a00c01bb12d92018235109d50c450d1e251a94794cd49554ee933c1d245e92eb46863d508761978c4223ac41b57703b702e12f340641cc2fb4cbe44d0f7d22f0df30f494b9123d17a0710d2c378c1ed2f7491342647d928d944420e4d8322bc00048a06d6451883e3fa11543674cf820380003160e0d49b817e12783301dd88621f80c6941ccef35764ddd525026a32aca142e9001d2f708df41192e90001360000070b3a4053420915ca26d48bd0b040004dec00040400000000d6100015804030f5100003a72d98005262140c02415451dc4d931ab0a4a09dc21c3ec4000066c9833a3d4e40e70d4e2af871204d842900000000000000381cef20b1d48600000003eb56384b084c5511c4ab3c6c4f41bf49721cf803d00000000000bba1d34e5f25285af0fd40001a6108c32a10650a9c0000000d372c2d4dd08846a308bc3e51009537176800045a13fc42103291c4544b44f5306000000036f92e155f135b412063e308461105b00003a0937547e06fa04cd52032e0efb28900000fb94110000e440001430000153200000004be0dee004c173206962d35ec8b54f9ce4d00009341780000526c5d8330d3e00000526000058e4e840000000531259d5164ca467500013ea496835f0e044a812c40c23ad40005144e9f0398000000000033e4c3838885d448d02030001083000053607747700a304d44394796214d0e40890c3933a0b193f4851517140a03fecc9c2f655343594f914aa95ee3c610fc2c40d2002911923b60b3d210c5714b346c001bc4fc238521b0c44b9e10d12e80afc6ea1184f9e20cd10c0000bc73f0931e400800004e4fda000059d0000ea0000110e000000031ec71a1dac89723b80004994000283cf824c98f9a5138b554dd06da53f8a79414d59647d00003e8c789100c8bb14812ef282c000468906c209800057d07c743b914c00002b80000b383ce079a1ab408b32b8fa637112f03ec8c3135410050588375293c201313c9c72f543de4db873031912112b14daa
  | 46 => 0xd2e6d2a000014ea56a11a309e90631588cce482d481435c42141248e32510c3f34a81c03d807db054477249ad48226b880439809221d90bd816c05db2fad28f0ba0b2f34d559c2fc054c38252a632e86b447c08c93c889162d9c9960b488813b0cbab4ed915649a531607bd16a16055a510ac26d489ccaf3984644571c59a267545b0368339378063b1ab96113808fb74bc8b981b0d55357dca3e57c942410941c111f43e64d88896530c7214f30dbf329c8f902bd0712970fb31fb85a058dcb4238e0273262869a2300a4319d86c6242cdd1289c6843c404cb0c6933252208a7125d25c28cc18d3d004f5051ca65000087c00000001a592e500009273dcc00051741c60fbc3a5123095e00007770ecc9654fac5c60000000000020c0000faa2708d39463055b3708e622c7c6d2330116700013df55b082b00000002f4c7812c7400000005b14200abd357444c000000055340003b154294f65563307400025e157410a800056e48cd000000038b5024116826720780000d2c5ac1cb811a375d15d3fc897a149c7a40be463443b51f1557d3bf58c83e10ffd3f04eb48452c08b68193817555a0e1f1b8c80933ec6533dd8b4030941ae43193be0000340000141b19a466d000038a4644b48276d3d744c8791301527e341400000000004aac26620b006351e0000013000723a80e1254040000011282cd000011a8ed612380000f10f282c441f33294a060484667000047c057410b0c605a2086c0000000000047004735b00001f200000a7d126000000000004fd0994000360400059010d0000000037700002d1000000000004440475000120a00008422390adf42a9409173045f4130945375883c000000005f1492000015e2bd919448bcd45025c0db000113f38389664d2c1da00c80004894000000000012e80004e2542341d8f210000d8d46d0c610cd8a8e449557a2be47b900000000000068000124c00000001d789f00000000000110f00000000001012186887300015cf1f7d524527400000015ae134c00000000001fdc5bf00004534724c543215001523503c3f64f091584d864b78e981bd891b255151420c89c04204bd10c9111d01ad34209aca984d94986092854008ece710f504bc37ed1e05038000009cf944ab0b6c28d53190db8f8a2e045bd1520ada3e7557e0938ca02e51590000000026812591d4022b39e558d00d0b8514949434714ac23f384ec48f038722808ce000000009fcbb301951a83ff8ee313e413c262c0ef11b41451c78ba23afc00045040a6019c00051dd3a839c10ce08f521d4a18a403f74b3f3b5531d2c280e216f84be37d502e26684e900000001e54b690000816322c378527d541110400044e80003d6c9c922f93fd49f1427000041422c8f84372438f000000000000001c140003468c7835d47c00001438000
  | 47 => 0xe851f3218b3c0310d7100fd4b132c4450545c0001c80be842e0000104508d488941f01b93a60bec9cd2ce4c7a31f411d20bc2ee394cdf63f4400021605cb2420000000000000011d70000f6f0eb147a28200001d9c74c0000000519c15800004e43d7400000000001c607850e5898236cc8d10000d221f68d0039e0b72089d3ef3cc4ad4327d5e34ac92d74cd087e46b14fb2d14b6a3d3432242cd5c6359065b3938535540c1e950541d8504cc2a13349624728478210492e1548ebb08882e51e5158a2f50000434cae2576845d1970a5e43041f11d289a90ec53b9335101e13ed5101a751b9015417204f958258f8eed2fe901c045c5012f14e044310a671bed53e0ed8d535118db133d8000000103402c0d27218cb4a09c400002448e8000127b351ce111fe8641161cf352cc101a4cdd35f35700d2538cc1c4084f624cd8ca4224c76e36c8c4851311b1421d60e000146d1564457221c000003033742a00004b6d55839701a23a5000008e164451bc85600006820a78697229800004d00000000fef0bc1401589078048b5502000057055c14dc15f057538780c531a00bf0000a95369d356313055700008a21a48b4f0be12b900000004ea40000330370491021a1f84bbd14883c01210fa741d40d64fb461f26b556d4c6ca492208f3a404522b4260fe93e893ce14845644ab88f63e04bde453473a000091506804ea01b48ec56803713e5513b232000025605de3d049981a046b5000112d0000f7f17b40001300d5b31e4ea4496cdce046c0004c894990000000390c00052ac0003a780000b7c0000000000305818b0000631321c0002e7c000000000000011bd1f9c85033a4fa53fdd48f000028349a000036c0e27375510d287438b2614e59179d4ee22fd6204db0c5054455f955d951e3c1c2e228144185470a01548499b1e883f606c11c1191857254d4a320ce11b243a8ee848c8b24348c55e4d34d9b54649250420f5c50ad25855292092ea41370150ec14848d57258d2843c70f264f011422bc4000358c37c43dc1602b6400050dc00037300002d5137d27c854e424cb5a517c10d06bc0001540000590c5d114a816d02b0a7f1e993fb19c0b1733185eb32b000015b8efa00015c51270000165928c00003f24f914fa5280cf000007a81204000122c4b94c602571960a8227a00d90000c2837847060918ad157880ce3cc046f02388d7317d34757f84a0409d47b183012a2b04d3655a427d0e8047f4d100000000088449d50b26f0000510ca1a026ca1c4448000557543b41a0c8d253c4ce191c4631f714282e81380103038d000160c4f1000022909bf12140002428b4158d4bca4b540000000e921e715000f180000598a56324c78a465c0003fb891a30ac6a53d840003ac8dab00003fe000040d58e433f30214f92c547361e94a5836a036
  | 48 => 0x9025434eb4389858400482252b016020e3840f53c043d3af466b4b887f839bd39924c8aeb2154cb20114e214d641002470e4542fc000016c54b566820b000084a367809e354876108fc95721d143e18fc59e35f8ad302e871615e1091213455d0d8c99536d4000000051a3cb4eaf09485f60aa563420b43a926dc6a90ea05a31c3d22457
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6e7558b20040018daeab1640080123be1d62880101fd7240ac51002000ce5625c620040070f90bbb2400800a2f213764801000c6e41eec90020048ec82dd9200408b1ef03bb240080621f61b75480100061f326ea9002000c5e63dd520040858dcc5baa40080021fa1d654801003c3e43aca9002000c3c7459520040018b8e6b2a40080131d1c565480100bc5ec36e89002000c3e65dd1200400187acbba240080032798f744801035657316e890020008be87591200400d1790eb2240080030fdd564480100061e3aac89002000c9c735912004009968e2b22400805a3761b73480100062f32ee69002000c5d65dcd200400193cc9b9a400800327593734801034e67316e690020008de8758d200400b1b90eb1a400800317dd563480100062e3aac69002000c9f7458d2004001938e8b1a4008013351c5634801000637baac49002000c6c75589200400195ee8b1240080032b1d1624801000667b9ac49002000ccc7358920040099c8e2b1240080031d99771480100063ab2ee29002000cb664dc5200400196ac9b8a40080033598f71480100066ab1ee29002045ce662dc520040019cac5b8a40080fe79a1f214801022e73bb64290020028be845d820040091db04bb040080030f9d165080100263b38aca10020008bf865d0200400187ccaba040080030f59574080100064f31ae81002009cae625d0200407bb4842ba040080022fe1d64080100045ec3ac81002000c9e7458c200400193ae8b184008013359c56308010006573a2c41002000cad74588200407d5c902b1040080031d59571080100066ab1ae21002009ce6625c420040018e8ebbb220080032d1d376440100063bc2eec8802000c7485dd9100400196f09bb220080032d21376440100066bc1eec8802000cd483dd910040019cf05bb220080033920b76440100063a286ec8802000c7776dd510040816e101baa20080032dddb74440100066bbb6e68802000cd7761cd1004001b28e839a20080fa79a1f724401000673bb6e48802000ce7761c91004001aceea3922008003591d47244010006d3ba0e48802000da4741c91004001b8ee63922008003711cc72440101f4f3c30e4880203e9e5861c9100407daccca39220080fb5959472440101f6d3320e4880203eda5641c9100407db8cc639220080fb7158c724401022e73300e4880203ede2601c91004001ac8a039220081065da1e50440100063bbb4a08802000d647294110040836e50f282200827f5ca1e5044010205b9c34a08802040b71869411004081ae6ed28220080039cdda504401000799ba4a0880209ef30749411004081e64c92822008103cc5925044010007a9b9ca08802000f50739411004081ea4c72822008103d458e5044010007b1b94a08802000f60729411004081ec4c52822008103d858a5044010
  | 1 => 0x902ba2c4080123ba1f52588100257340ea4b1020048ec8754962040091dd0fa12c408287391c642588100247643a84b102096ce47150962040091dd0f992c408012b9a0732588100053742864b102000a6d850c9620400155d08192c408002ab61032588100053ac08a0b102041c747114162040095cd033aac408002b9606755881000573c0aeab102004ae4815d562041439c8e3ba2c408012b9a06745881000572c0ce8b102000ae7815d162040095c902ba2c40825b391c5745881000717aa4a8b102000ace83151620400159b062a2c408012b9a06735881000572c0ce6b102004ae4815cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd6204001c9ea729ac408002aba10535881000556c20a6b102000a6e8510d62040014db0a21ac4080ff391c6705881000557420e0b102000aad841c1620407d9c8e2382c408012b9a04505881000572c08a0b102041a6f811416204083ccd02282c4081069b604505881000732c08a0b102000a65811416204083cc8e2282c4081029ba0050588100053742e80b102000a6d85d01620400159d07a02c408002b360f405881000537c2a80b102000a6c8550162040011dd0e202c4080023b61c40588100053742e60b102000a6d85cc1620400155d09982c408002ab61330588100257340860b102000ae5810c162040091bf0eb1c64080123720f764c8100247a40aec99020048dc8758d32040091d90eb1264080033558f714c81000672b16e29902004ae78758b210407bd4ce8b1642080f7a95d162c841000732282c59082040c3f71592500408187ae2b24a0081070f9c164940100071d382c92802040c5f7158e50040818bae2b1ca008107179c163940100072d382c72802040c6f7198a50040818dae3314a0081071b9c2629401000735384c52802040a748158a5004081cc902b14a0081031bdc5629401020636b8ac52802041c6e7058a5004001cd4e0b14a0082831ddd97194010204bbc32e32802000c77865c65004081a6cc8b8ca0081034d5917194010206ab31ae32802040d55635c65004081accc4b8ca0081035958971940105063b302e32802040d72605c65004001ccac590ca0080033558d718c0100fc3ec36ea9802000c3e64dd530040458bcc7baa60080021fa1d654c01003c3e43aca9802000c3f755913004001878eab22600800317dd5634c0100062e3aac69802005ad88058d30040018deeb31260080031b1d6624c01000637baac49802000c6c755893004001d9060b12600800e1fa1576c80100247a40aed900203dce7215db200403b0ff0cbae40080030f99175c80100062f31aeb9002009c6e625d720040012ef02bae400801e1fe1d65c80100043ec3acb9002000c3e75593200400187aeab264008003179d563c80100062ebaac79002000
  | 2 => 0x572594100253a40ae4b282004a7681d0965040014eb03a12ca080129da0732594100053ac0e64b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b2820a9a75819c165041518f0e1382ca0801e1fa1f40594100043ec3e80b282000a5e83d0165040014bb07a02ca080021fe1d405941003c3e43a80b282000a6e8210165040014db04202ca080129da0440594100053ac0880b28200787e87cc165040010fb0f982ca080028fa1330594100051ec2660b2820a7c7870cc165040094ed02182ca080029d60430594105363c38060b282000c3f759d5640400153d063aac808002a760c755901052d5bc0ae6b202004ab4815cd640400147d0a39ac8080028f61473590100070fa9ca6b2020008be8714d640400117b0e29ac808292ade0572590100255a40ae4b202004ab681d49640400156b03a92c808012ada0732590100055ac0e64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b2020a3ab5819c1640400956d02282c808002ad604505901020d1fc08a0b202041e3681141640408347b02282c8080038d60450590100051ac08a0b202040a3e80141640400d17d0f982c8080022f61f30590100051f42e60b202000a3d85cc1640400956d02182c808002ad60430590100047c402eab1820048f4815d163040091bd0fa9ac60800317dd75358c100246e43aa6b1820048de87d0d63040091b90ea1ac6080029d6045058c105163c380a0b182000c5f759d563040015b700baac608002b62017558c100054f420eab182000a9d841d563040015af02ba2c608012b52057458c100052f428e8b182000a5d851d16304001c3ea92a2c60800237a1c5458c100046ec38a8b182004ad4815c963040014bd0a392c608002976147258c100054f420e4b182000a9d841c963040095ad03a92c608002b56075258c100256b40e84b182000ad581d0963040095ad02282c608002b56045058c1020d2fc08a0b182041e568114163040834bb02282c608003956045058c100052ac08a0b182040a5e801416304145cb6e0282c608003961c05058c1002c6f43e80b1820008dd87d0163040014bd0ba02c608002976174058c100052fc2a80b182000a5c85501630400159d04202c608002b36084058c100256b40880b182000ad5811016304001c5ea92a4c408002b3a0c549881000566c18a93102000e4f5394e620400155d0829cc408002ab610539881000537428873102000a6d8510e62040834df02284c4081069b604509881020537400a13102000a6e85d0262040014db0ba04c408002b3a0f409881000566c1e813102000a6f8550262040014d90aa04c4080263ba1c409881000476c38813102000a6e85cc262040014db0b984c408002aba13309881000556c266131020048f4815d562040091e
  | 3 => 0x89822000c5f75d8d30440018b8ebb1a6088133351c7634c11000637baec49822000c6c75d8930440018deea31260880031b1d4624c1101f672388c49822000cb464dc530440019c8c5b8a60881061f21975c81100061e322eb9022000c5c635d720440138d8c4bae40881021fe1f65c81100043ec3ecb9022000c3e75d93204400187aebb264088003179d763c81100062ebaec79022000c6e75d8b20440018daebb1640880273918971c81100043fc2aec902200387c855d9204400117f08bb2408800a2f21176481100046fc1aec90220018dc835d920440830fd0dbaa40880030f19375481100062e31eea9022042c6c62dd520440b10fd0fb2a40881021f21f65481100061e3a6ca9022000c5c73d9520440818e8e3b2a40882ba2fa1b74481100061fb2ee89022000c3c65dd12044001938c7ba240881ab2b18b744811056c5f43ec8902204d8bc87d91204400187eebb2240880030f1d764481100064e39ec8902204dcb471d9120440971bd0db9a408800317d9773481100062e32ee69022000c9f64dcd2044001938c9b9a40881a73318b73481103446f43ec6902204c8dc87d8d20440018beebb1a4088003171d763481100064fba6c69022000c9c74d8d20440999a8e3b1a40880031bdd76248110006363aec49022000caf74d892044001958e9b12408800333dcf62481100066639ec4902203fce471d8920440018eecbb8a40880031d19771481100065bb26e29022000cb464dc520440019aec7b8a40880033518f714811022e72316e290220028bc849d8204400187ce9b28408804e2f21974081100061fb2ae81022000c3c655d02044001938c6ba040880272b18974081100045fc3ec8102200b8bd87d90204400193ce9b184088003275d36308110006573a6c41022000cad74d8820440070fd0dbac20880030f19375841100062e31eeb082204197a80dd610440070fd0fb2c20880030fdd764841100061e3aec90822000c5f75d8e10440018b8ebb1c20880031bdd76284110006363aec50822000c6f7518a10440018d8ea314208800399d4462841100263b3b2a30822000e64625461044009ae4e0a8c208803a9da1b75841102063b3b6eb0822000b7280dd610440818ecedb2c20881372d9db64841102666b3b6c70822001cd67618e1044001d28c831c20880ff399db628411004e733b0c50822000e676518a1044001cc8ca3142088003a9d90628411000752320c50822000ec76318a1044001d88c6314208800399dd46284110007323a8c50822000e645018a10441594ed0d284208800f1d9da508411000732314a10822000c3f749d165040014bd063a2ca080029760c74594100062fb9ce6b2820aba7b805cd65040014f100b9aca080028fa1073594100051ec20e6b28200087e8710d65040010fb0e21aca082aa9de0
  | 4 => 0x1440014df04b1aa28812a9b20963545102652f430c6a8a2000c5c7618d5144001c3ec831aa28800387190635451025fa8080c6a8a203ea6e86d8951440018d8edb12a2880038bd93625451000716326c4a8a2000e4f63d895144001c98c7b12a2880ffd804362545101fe37b8ec4a8a2000e6771d8951440010ff0eb12a28800e1f21d62545100051fc22c4a8a2035a3c8458951440014bf06b12a2880d29720d62545100053bc0ac4a8a203fa6e8618951440018d8ec312a2880038bd90625451000716320c4a8a2000e4f631895144001c98c6312a2880fbd804062545101f733408c4a8a204ae6581189514407d8dee2312a28800399dc462545101f733208c4a8a2000e6541189514407dccc62312a2880fb9904062545100072c31ee0a8a204087e861c1514400187ec8382a2880030f19070545100062fb18e0a8a2000c5c631c151440018dec4382a2880031b18870545100072c318e0a8a204097a861c151440018f50c382a2880034ed9070545100069c320e0a8a2000d5b631c151440018f4c6382a2880031e18c7054510006ac318e0a8a2000c58631c15144001ad6c4382a2880035a188705451020e3db08e0a8a2031a748654531440698e8eca8a62880d39518d514c51000732312a298a2000c7865dc131440018f0ca382628800336d8c704c510006b8a88e098a20028bc849db214400187ce9b2e42880022f21974c85100061fb2ae990a2000c3c655d32144001938c6ba642880272b18974c85100045fc3ec990a20008bd87d93214400193ce9b1e4288003275d363c8510006573a6c590a2000cad74d8b21440139d0c538642880a69d21951485102563a3b2a290a204ae646254521440019d6c438242880035c54470485100061e324ed2822023a3e86d92504400187cedb24a0880030f5c7649411057e1f386c92822000e3a70d9250440454bd0db1ca088003179db63941100070fb26c72822000e1c64d8e50440018bae3b1ca088003179c363941100072d386c7282200087f8758e504400147f08b1ca08808e8f211639411000537c12c72822042a6c8258e50440014bd0c31ca088003179d863941100070fb20c72822000e1c6418e50440854dd0db14a0880031b9db629411000717b26c52822000e2c64d8a5044001c9ec7b14a0880039318f629411000636b8ec52822000c6e70d8a5044001cd4e1b14a0880021fe1d62941100051fc22c52822023a3c8458a50440014bf06b14a08808a9720d62941100053bc0ac52822000a6e8618a50440018dcec314a0880038bd90629411000716320c52822000e4f6318a5044001c98c6314a0880031b5c462941102c637380c52822000e6a7018a50440830fd0dbaa60880030f193754c1101162e31eea982207a87e87d9530440810f90fb2a60880030fdd7644c1100061e3aec
  | 5 => 0x8002b3e0d62189100056641ac43122000c6e76d9462440011db0f328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac84594624400159f06b28c488002b320d6518910006373b0ca3122000cae76d906244001c5ecbb20c4880038b197641891000476c3cc83122000a6e8599062440014db0b320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400195cec320c4880038bd94641891000716328c83122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e8c64d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab2116318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d90631891000746320c63122000e2f64d446244001c58c9a88c48800393d8f51189100072631ea23122000b6a80d4462440014dd0c280c4880038bd90501891000716320a03122000e4f631406244001c98c6280c4880038bd52541891000567418a83122000acd83150624407d5cd022a0c488002b9604541891000727a9ca63122000aae8414c624400155b08298c4880fab9a04531891000572c08a63122000a6e8510c62440014db0a218c4880fab9a04431891000572c08863122000a6e80d44624407dcc821a88c4880263ba1f411891000476c3e82312203eae681d4062440015cb03a80c488002b9e0550189101f57240aa03122000a6e85d0062440014db0ba00c488002b3a0f401891000566c1e80312203eae681d0062440015cb03a00c4880029be1540189100053642a803122000ae781500624407d5c902a00c4880263ba1c401891000476c38803122000a6e85cc062440014db0b980c488002aba13301891000556c2660312203eae681cc062440015cb03980c4880029be1510189100053642a203122000aaf84440624400155908880c488002b3e0d10189100056641a20312200087f855da32440070f90abb464880022fe11768c9100145e422ed19220098ec825da32440070fd0bbb264880021f617764c9100145f426ec99220008bd84dd932440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011df04bb264880023de05764c91004c6f43ec699220018ee87d89324415d47d0db22a2880030f1db645451026f98086c8a8a204dc3f71d915144001c6ee3b22a28812e97a1b63545100062e3b6c6a8a2000e1f64d8d5144001c38c9b1aa288133d404363545102662fb8ec6a8a2000e5771d8d51440010ff0eb1aa28800e1f21d63545100051fc22c6a8a2035a3c8458d5
  | 6 => 0x476c3e83b122000a6f855c362440014d90ab86c4880029ba1740d891000536c2e81b122000ace83d03624400159b07a06c4880029be1540d89100053642a81b1220008ee8710362440011db0e206c4880029ba1730d891000536c2e61b122000aae84cc3624400155b09986c4880271b18975989100061f3a6cb3122000c5e73d96624400187ce832cc488003179cc65989100061fb2ae93122000c3c655d26244013958c4ba4c4880030f9d764989100061ebaec93122000c9e73d92624400187cea324c4880030f5d464989100064f398c93122000c5f655ce62440018b8cab9cc48800327d9173989100064e322e73122009ccc625ce62440018bcebb1cc488003175d763989100064f3a6c73122000c9d74d8e62440018bcea31cc488003175d463989100064f3a0c73122000c9d7418e62440018dcebb14c4880031b5d76298910006573a6c53122000cad74d8a624400199ce7b14c488003335cf629891001c3f436eab12200087e87d956244001878e9b2ac488003171cf65589100043f438cab122000c3c7419562440018b8e632ac48800a2fa1b74589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d0635891001c3f406eab1220008bf845d5624400517908baac48800237e0d755891000c6e41aeab1220008ef825d562440011ef02baac4880030fdd774589100061e3aee8b12200087f855d162440070f90aba2c48800237e0d745891000c6e41ae8b1220008ef825d162440011ef02ba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6f75dc962440018d8ebb92c4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880031ddd771589100063a3aee2b122000cb774dc56244001968e9b8ac48800335dcf71589100066a39ee2b122000c7785dc562440018e90bb8ac4880021fa1f515891001c3e43ea2b122000c3f74d456244163878e9a8ac48800317dcf51589103fe2e39ea2b122000c7771d4562440070fd0bb82c4880021f61770589100043f438a0b122000c3f741416244161878e8282c48800317dcc50589103d62e398a0b122000c777114162440011df0eb10c4880029be1562189100053642ac43122000aaf84588624400155908b10c48
  | 7 => 0x6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880032d1d37158d1000672396e2b1a200087e87d4563440070f90fa8ac6880030fdd35158d1058e1e3a6a2b1a2000c6f72d4563440b98d8e5a8ac6880031e1d77058d100043f438a0b1a2000c3f741416344161878e8282c6880031bdc85058d102c636390a0b1a20b3c7b7014163440018bcedb28c6880023761e6518d100052f42cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440015b700b28c68800297a186518d100062f3b0ca31a207aa5c801946344165cb620328c6882cb960406518d100064f3b6c831a2000e1f65d906344001c38cbb20c6880023761e6418d100052f42cc831a2000a5d85990634400153d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc8259063440015af02b20c688002a7a186418d100064f3b0c831a2000e1f651906344001c38ca320c68800297a1b5118d100052e436a231a2000e1f64d446344001c38c9a88c688002d6a035118d100052f430a031a2000e1f641406344001c38c8280c6882cb96d805018d1001c77c3aa5b1220028ef8750b62440014dd0a196c4880029b61432d89100055742065b122000aad840cb624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc835976244001c5ecbb26c4880038b19764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000717b28c9b122000e2c651936244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001c5ec9a8ec4880038b19351d891000727b1ea3b122000e4c63d4762440016d501a8ec4880029ba1850d891000717b20a1b122000e2c641436244001c9ec6286c4880039318c50d891000717aa4a9b122000ace83153624400159b062a6c4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec48800393d4e53d891000557420a7b122000aad8414f62440014dd0a21ec4880029b61443d891000557c22e3b122000aac845c762440014dd01a8ec4880023ba1f41d89100
  | 8 => 0x6b2ec888002abe0965d911000556412cbb222000a3e86197644400187cec32ec8880028fa1663d91100051ec2cc7b222000aae8298f644400155b0531ec8882bb0f9db51d91100059d406a3b222000a3e86143644416187cec286c888002a7a0e75d91100054ec1cebb222000c3d751d7644400147d0b39ec8880028f61673d91100070fa9ca7b2220008be8714f644400117b0e29ec8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c8880eaaea0371d911026d1ec0ea3b222000a3e80d47644416947d00286c8881362fa1f30d91100045ec3e61b222000a3e85cc3644400147b0b986c888003175d753d8d1001c6fc3aa7b1a20028df8750f634400153d0932ec688002a761265d8d1000567414cbb1a2000acd82997634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc825976344001c3ecbb26c6880038719764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c6519363440978bceda8ec68800387d9351d8d100070e326a3b1a2000b5a80d4763440014bd0c286c68800387d9050d8d100070e320a1b1a2000a9e849d7634400153b093aec688003175d475d8d100052f42ce9b1a2000a5d859d36344001c3ea92a6c68800237a1c54d8d100046ec38a9b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000a5e80d47634400159d05a0ec688002b360b41d8d100052fc2ae1b1a2000a5c855c3634400153f08b86c688002a721170d8d102646f43e81b1a20008dd87d0363440014bd0ba06c6880029761740d8d100052fc2a81b1a2000a5c85503634400159d04206c688002b360840d8d100062e31eeab1a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880032718f7458d100045f43ec8b1a2000c3f75d916344001878ebb22c6880022fa1c6458d100061fba8c8b1a2000c3c7519163440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc96344001998c7b92c6880031bd947258d1000636328e4b1a2000caf641c96344001958c8392c6880033318c7258d1001c3f43eeab1a20008bf845d5634400517908baac68800237e0d7558d1000477c12eab1a20098ec825d563440011f700baac6880021fa1c7558d100145f43ee8b1a2000c3f75dd16344001878ebba2c6880021fe157458d1001c3e42ae8b1a20008df835d163440011df04ba2c6880263b2097458d100047bc0ae8b1a20008be871d1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1004c7743ee4b1a2000c
  | 9 => 0x768ca100145e422ed194200387e85dd932840010fb0bbb265080021fe15764ca1001c3e42aec99420008bf845d9328400517908bb2650800237e0d764ca105b43e43ac6a8c203fe6421d89518404d0f90eb12a3080028fe1162546101ad1e422c4a8c2000a5f8358951840694b906b12a3081071e61870546100063d318e0a8c2000c78631c1518416bae302382a3080031e197704c6100063c328e098c2000cd9631c1318400187ce9b2e43080030fd9574c86100061e32ae990c2009cae625d3218412db4842ba643080fe3be1d62c861000656ba2c590c2000e6562547218407fbc04338643080035c54570c8610005b9406cb90c2000e676558b218407b1ef0cb864308103990876548610004bac3eca10c2000c7576d9421840836e501b2843080027961f620861000733b2ec410c203ebe280d8821840f90ff0eb1ca1081021f21d63942100ec3fc3ac5284204087c8758a508400147f08b14a10808e8f21162942100052fc1ac52842022a5c8358a50840812f100b8ca1081031de197194210206b9c02e328420a0d70805c650840818ecc0b8ca108002dc6032194210004bac3843284200087e87d9530840091bd0fb1a61080025de0575c82100043ec3ecb904200087e87d952084001878e9b2a4108003171cf65482102063a38eca9042000c3f65dd12084001878cbba2410800317d9773482100062e32ee69042000c7765dc520840018e8cbb8a410800279a1f21482100061f3a6ca1042040c7671d94208400187ecaba041080030f195740821004e57312e81042045da4215d020840011df0eb1041080032b5d162082100063bb2ae21042000c74655db108408b3c904bb621080025d61f65c42100063abb6cb8842041b7280d97108408d2eb0f28621080021f61e64d95100052f41cc9b2a2000a5d8399365440014dd05326ca880029b60a64d95100043fc3ac9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a2000c3d71193654400147d0931eca880028f61263d951000537414c7b2a2000a6d8298f65440014bd073a6ca880029760e74d95100061eba0e9b2a2000a3e849cf654400147b0939eca88003175cc73d95100043f43887b2a200087d8710f65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440774f501b8eca880029ba0b41d951000536c1683b2a204087e87d0365440010fb0fa06ca8800297a0f40d95100052ec1e81b2a20b087f8750365440810f90ea06ca880029ba0840d951000536c1081b2a204087e87cc365440010fb0f986ca880028fa1330d95100051ec2661b2a2000c3e76d97644400117b0f32ec8880028fa1665d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100045fc3acbb222000a9f835976444001539
  | 10 => 0xb2c2000a6d821d365840014eb023a6cb080029ea0074d96100051f426e7b2c2000a3d84dcf65840014dd05b9ecb080029b60b73d96100053ac0ee7b2c2000a7a80dcf658400147d0939ecb080028f61273d96100062fb9ce7b2c2000c5d731cf65840014eb0239ecb080029ea0073d96100043f43887b2c200087d8710f65840014eb03b96cb080029ea0372d961000637b94e5b2c2000a3e841cb658400147b08396cb080029d60472d96100053d400e5b2c2040a7681d0b65840014eb03a16cb081029da0732d96100053ac0e65b2c200087e870cb65840010fb0e196cb080028fa1032d96100051ec2065b2c2000a6e82d0765840014db05a0ecb082a71d5c670d96100063d39ce1b2c2000c78739c365841538f2e3386cb080039c5c670d96100043ec3e81b2c2000a5e83d0365840014bb07a06cb080021fe1d40d96100053741081b2c2000a6d8210365840814ed02206cb080029d60440d96100043ec3e61b2c2000a3e84cc3658400147b09986cb081029da0430d96100053ac0861b2c20028be84dd7638400117b09baec7080263ba0b75d8e1000476c16ebb1c20028df8750f63840014eb02286c7080021fa1f6558e100043f438cab1c200387e87dd563840830fd01baac7080021fa1c7558e100043fc2ae8b1c200387c855d163840011df04ba2c7080263b2097458e100043f43ea2b1c200087e8714163840070f90e282c7080029d6045058e100053ac08a1b14200087e87d956284001878e9b2ac508003171cf6558a100043f438cab142000c3c7419562840018b8e632ac5080030fd977458a100061e32ee8b142000c5f65dcd62840018b8cbb9ac50800e1fa1f7558a1020c3f406eab1420008bf845d5628400517908baac50800237e0d7558a1000c6e41aeab14200087e871d5628400517d0fba2c5080030fdd77458a100061e3aee8b14200087f855d162840070f90aba2c50800237e0d7458a1000c6e41ae8b1420008be871d1628400187eea3a2c5080030f1d47458a1000c6f43ee6b142000c5f75dcd62840018b8ebb9ac50800327dd37358a100064e3a6e6b142000c5f751cd62840018b8ea39ac50800327dd07358a100064e3a0e6b142002cac7490962840051d90ea12c5080031ddd77158a100063a3aee2b142000cb774dc56284001968e9b8ac50800335dcf7158a100066a39ee2b14200087e87d45628400187ee9a8ac5082c70f1d35158a100062fb9ea2b14207fc5c73d4562840010fd0e282c50800e1f21c5058a100061fba0a0b1420b0c3c7414162840018bee6282c5081eb171cc5058a100053ac08a0b142000c3e74d94628400187ce8328c5080030fd957418a100061e32ae83142009cae625d0628408bb4842ba0c5080023be1d6218a1000656ba2c4314200087f855da32840070f90abb465080022fe11
  | 11 => 0x800195909bb240100031bd47764802000636286ec9004000c6f76dd5200800195eedba24010002aba1d64480202bd5643ac89004000e2f755912008001c58eab2240100032b1c5644802000717a8ac89004009caf705912008013d56e0b2240100038b141644802000667bb6e69004000e8d64dcd200800199eec39a4010003631d0734802000746b20e69004000ce776dc52008001d4ac9b8a401000339dd87148020006b3ba8e29004000d64751c52008001b4ee838a4010003691d0714802000752b20e29004000dc7731c52008001b88e638a40100fb39a1871480201f672c30e2900403ed66851c5200807dacb0a38a40100f739d9071480201eed3320e29004000ce5641c5200807bb4ac838a40100032959071480201eef1300e29004000d64501c5200807d1d90eb0a40100fb391c56148020004b643aa29004000c6f765452008001c5ac8a8a40100fb591c5514802000732b0aa2900405896e8794120080018deed28240100038b5925048020006b238ca09004000c3f749d165c40014dd053a2cb880029b60a74597100052f418e8b2e2000a5d831d165c40018bee739acb880028fe1173597100051e422e6b2e2000a6f825cd65c40014d904b9acb880029ee0173597105bd3c402e6b2e2000a3e841cd65c400147b0839acb88003175cc73597100043f43886b2e200087d8710d65c400147d09392cb880028f612725971000636b90e4b2e200087e870c965c40010fb0e192cb880028fa1032597100051ec2064b2e2000a3f845c165c400147908b82cb8800297e0d70597100052e41ae0b2e2000a6f825c165c40014d904b82cb8813a9de0570597100043f43e80b2e200087d87d0165c40014bd07a02cb880029760f405971011c3fc3a80b2e20b087c8750165c40014dd04202cb880029b60840597100043f43e60b2e200087d87cc165c400147d09982cb880028f61330597100045fc22eab1e20028bc845d563c40011df04baac7880263b2097558f100246e43a86b1e20048df8758e32c40010fb0dbaa618808a1fa1d654c3103d43e43aca986200087f865d720c40010ff0eb2e41880fa3be1d62c83100043ec36ea906204287e8759520c40b10f90eb2a41880030f1d165483100062e39aca9062004c747159520c400187ccbba241880030f59774483100062f32ee69062000c5d65dcd20c40099c8e2b1241880031d99771483100063ab2ee29062000c3e7459420c400187ccaba041880030f595740831000657b12e81062009cac625d020c40010fb0f326cb0800297a0e64d96100052ec1cc9b2c200087f8759365840014dd04326cb080029b60864d96100051f424c7b2c2000a3d8498f6584001ae2e3386cb080029d60774d96100053d406e9b2c2000a5e839d365840014bb073a6cb080030f5d074d961000537410e9
  | 12 => 0xff99a1461881201ff32c28c31024000ce77418620480019cae830c409000399140618812000536432a3102403fe646154620481774dd0d284409000399186508812021735b04a11024000c3f759d5640800153d063aac810002a760c75590200051fc2ae6b204000a3c855cd640817555f04b9ac810026ab20973590200051f428e6b204000a3d851cd640800193ae639ac81000387d4e53590200045f438a6b2040008bd8714d640801355d05b8ac81004eab60b71590200051f42ce2b204000a3d859c5640817355f04b8ac810026ab20971590200051f428e2b204000a3d851c5640800153d0638ac810002a760c715902004d57416a2b204000aad82d4564080b9c5d05a8ac8100038b60b51590202e71610ea2b204000a3e80d4564080b9c5e41a8ac81012a8f616515902000557c12a2b204009aac82545640801355d0598ac810002ab60b31590200045f43862b2040008bd870c5640800147d0a18ac8100028f61431590205c556c14e0b204009aae82941640800155b05282c810026aba08505902000556c10a0b204058e2e821416408001c5b04282c8100028f60450590202c716108a0b204042a3e8014164080b1c5e40282c81004e2fa1f30590200045ec3e60b204000a3e85cc1640800147b0b982c810026aba08305902000556c1060b20400087f855d163080070f90aba2c6100263b2097458c2004c6e43aa6b1840098ec825d561080131d904ba2c2100263d21d51584200053ac08a0b084004a7481dd951080954d904bb2a21012b1b1c976544200053bc0aeca88404ae2c7259151080b987ee2b22a2100038ddc564544202571610ac8a88404ae2f205915108001c5ac9b92a2100fb99085615442001d3b43ac2a884003a7487585510807dccf04b0aa21000399dc9615442025732392c2a88404ae6720585510800187cc8382a2100030f590705442020e3b308e0a884000c75611c1510800187cc8bac62100131d985758c4200061f3aac91884000c3d7559231080018eaeab0c62100272b1c9644c42000656b26e498840098f487585310800195d08bb442100032b61176884201f637a8aed108403ec6d515da21080018d8a0bb4421016eabe1d648842000556c3ac91084000e2e755922108001c5aeab244210003a39cd648842000746b9ac91084009cae715922108013d4ce2b2442100038bd45648842000716a8ac91084000e2c50592210800195ac8b84421010b8b9c964940202171610ac92804058c3e705925008001c74e0b24a01010b8bc81649402000716b22e52804000c3e645c6500800187ac8b8ca0100025b61e219402000536c34432804000e2d64886500801395ce4b2460100032b591728c0200061f326ea9804000c3f755913008001878eab2260100031b1d77648020006563a6ec9004000caf84dd920
  | 13 => 0x762318c390a4000a6c86547214807f8dceca8e42900034b5d151c85200273230aa390a403fce4619c321480010f90cbac42900030f19175885200062e31aeb10a4004c74615d621480010fb0fb2c42900030f9d365885200062f39ecb10a40008bc865d2214800187ecaba442900030f19574885200064e31ae910a4004cb4615d2214800117b0fb2442900030f9d764885200061ebaec910a4000c9e73d9221480011b90cb9c429000317d9573885200062e32ae710a4000c9f645ce2148001938c8b9c42900133518573885200046ec3ec710a4000c5e75d8e21480018baebb1c4290003279d363885200064eba6c710a4000c7675d8621480018eaebb0c42900032d9d361885200065aba6c310a4000cd673d8621480019aae7b0c42900133c186708852000679b08e090a4000e8c6418d21480095cd0db0a429000399d94614852000732328c290a4000ea7641852148001d48c830a4290003b1d8c614852000762318c290a4000a6c8654521480098d8eca8a4290013991855148520004d6c20e090a403dde3711c12148001878c93b4a09008e8fa1b64941200061f3b6c928240bcc3e70d925048001c74e1b24a09008a97a1b63941200062f3b6c72824000e1f64d8e5048001c38c9b1ca090003179c363941200072d386c7282400087f8758e504800147f08b1ca09008e8f21163941200053bc0ac72824040a748158e50480014bd0c31ca090003179d863941200070fb20c72824000e1c6418e50480810f90cb8ca0900030fd9171941200061e322e32824000c5f635c650480018b8c6b8ca0901031d18571941200043fc3ec32824000c7571d8650480018ecedb0ca0900038dd9361941200071a326c32824000e5763d865048001ca8c7b0ca0900031de1f619412000739386c32824000c76761865048001c6ec830ca0900038d19061941200072bb18c32824000e546318650480818eb0e30ca09000399908619412000732a10c32824000e727018650480014dd0d90ca0901631b9db219412000596c26432824040e6461c8650480e98dcec90ca090103991852194120005b440243282405887e86dd53048001878c9baa609008b1718f754c1203d43f43eca982404287c87d95304800187eebb2260900030f1d7644c1200062fbaec69824000c5c75d8d30480d3998e5b1a60900032b193724c1200063bbaec29824000c7475d8530480018eeea30a60900031d1d4614c12000673b90c2982403dce4721853048001da06030a609010b1b9db658812021735b06cb102406acae76d9220480d399cedb1c4090007339d8638812000746320c710240098ec865c6204800135f08b8c40900ff39185718812000733b28c31024000e64651862048001d4ec830c4090003a9190618812000763b18c31024000ec463186204807f9cb0e30c4090
  | 14 => 0x4825006148001d4a84a00c2900f6b9a08401852000572c108030a4000ea64210061480014ed0b980c2900029d61730185200055b4266030a4000ab584cc0614807b5cd05980c290002b960b30185200053bc2a4030a4000a7485480614800156f08900c290002ad21120185200056bc1a4030a4000ad483480614806b47d09bb2a2900028f61376545201a52f41eeca8a4000a5d83dd951480010fd0d3b2a2900030f19276545200053ac0ceca8a4000c77719d951480018eb033b2a2900028fe1176545201ad1e422eca8a4000a5f835d951480694b906bb2a2900029be0976545200053bc0aeca8a4000c3c641d951480018eee23b2a2900031b908765452000636a10eca8a4000c77811d9514806b47d0db22a2900030f9db64545200061e3b6c8a8a40bdc3f71d915148001c6ee3b22a2900d297a1b63545200062f3b6c6a8a4000c5c76d8d5148001c3ec9b1aa2900038719363545200062fb8ec6a8a4000e5771d8d51480010ff0eb1aa2900021f21d63545200051fc22c6a8a4035a3c8458d51480014ef02b1aa2900129d20563545200052f430c6a8a4000c5e7618d51480018b8ec31aa29000387d9063545200070e320c6a8a4004a7686d8551480018e8edb0aa2900038dd9361545200071a326c2a8a4000e5763d855148001ca8c7b0aa29000e9da1f615452001d3a43ec2a8a4000c767618551480018e8ec30aa2900038dd9061545200071a320c2a8a4000e57631855148001ca8c630aa2900030fd9070545200061e320e0a8a4000c5f631c151480018b8c6382a2900031dd84705452020e3a308e0a8a400387c859da31480010ff0abb4629000e1f215768c5200045fc22ed18a40028bc845da31480091e902bb462900021f219758c5200061e322eb18a4034c5c635d631480098e8c2bac62900021fe1f658c5200043ec3ecb18a4000c3e75d92314800187aebb246290003179d7638c5200062ebaec718a4069cce72d8e3148001958c8b94629001339185728c5200063b3aec318a4000c7575d8631480070fd0bbb262900021f617764c5200145f426ec98a40008bd84dd931480031ed0fb0a62900031b19676c852000656324ed90a4000caf849db2148001959093b6429000339e0676c85201fe37a8ced90a4000c6c509db21480018dcedb2e429019a6b21974c852000697b2ae990a4000d2c655d3214812d95cc2ba6429025b2b18574c85204b65230ae990a4000d2f515d3214801395ec0ba642900276ad8174c852000696282e990a40009af87d93214800195cedb264290003339db63c8520006c6ba6c790a4000cce7618f2148001b1ae831e4290003a319063c8520006733b6c390a4000da574d872148001cceca30e42900039919461c8520006d2ba0c390a4000ea7641872148001d48c830e4290003b1d8c61c852000
  | 15 => 0x9328c290002ad61265185200056b41cca30a4000ad58399461480011ef0eb28c290002ade1165185200055a422ca30a4000ad78359461480015a906b28c2900031d9d865185200053bc38ca30a4000cb676d906148001c6ecbb20c2900038d19764185200071b3aec830a4000e3575d906148001d4f05b20c2900023d61e64185200053b42cc830a4000a758599061480015ad07320c290002b560e64185200047bc3ac830a4000a778559061480014e90ab20c290002b5e0d64185200056a41ac830a4000cb6761906148001c6eca320c2900038d19464185200071b3a8c830a4000e35751906148001d4b04320c290003359db63185200072bb2ec630a4000e5465d8c6148001d2ec9b18c290003a519363185200072b3aec630a4000e5575d8c61480011eb0f318c2900029da1663185200053ac2cc630a4000ab68498c614800156b09318c2900023de1d63185200053bc2ac630a4000a748558c614800156f08b18c290002ad21163185200066b3b0c630a4000e576518c6148001ca8ca318c290003a5d9063185200074a320c630a4000e567518c6148001caaea318c29000399d9572185200073232ae430a4000ea7645c86148001d48c8b90c290003b1d8d72185200076231ae430a4000ae6869086148001ccecb210c29000399196421852000753b248430a4000ea4649086148001d8ec7210c290003b118e421852000733b2a8430a4000e64655086148001d4ec8a10c290003a9191421852000763b1a8430a4000ec46350861480014ed0c280c2900038dd9050185200071a320a030a4000e57631406148001ca8c6280c2900038dd5254185201ed73414a830a4000ae58295061480015ad062a0c290002b560c54185201ed73410a830a4000ae5821506148001caea7298c290002b9e0953185201ed72412a630a4000ab68414c614800156b08298c2900f6b9a08531852000572c10a630a403dae682d0c61480015cb05a18c2900029da1443185200053ac288630a403dae68210c61480015cb04218c2900f799149521852050d73c3c8430a40a1ae5879086148143ccceb210c290287995d6421852050f533a48430a40a1ea57490861480015cd01210c2900f7a910942185204b573c3a8430a4096e6675508614812dccaeaa10c2900f7a9e1142185204b753ba28430a4096ea4745086148001d4e86a10c290003a950d4218520005724028430a403dae682d4061480015cb05a80c290002b9e0950185201ed72412a030a4041a778714061480834eb0e280c290107999c8501852000733210a030a4000e654214061480014ed0ba00c2900029d61740185200056b41e8030a4000ad583d00614807b5cd05a00c290002b960b401852000752a168030a4000ea64290061480014ef0aa00c2900029d215401852000573c128030a403dae
  | 16 => 0x2d85200053b430a1b0a4000e37641436148001c68c8286c29000395d8c50d85200072a318a1b0a4000c76871d761480014ed003aec2900029da1674d85200053ac2ce9b0a4000ad6839d361480015ab073a6c2900029de1574d85200053a42ae9b0a4045ae6821d361480015cb043a6c2900038dd5254d85200056b418a9b0a4000ad58315361480014ed0b39ec2900029d61673d85200055b424e7b0a4000ab5849cf61480014ef0ab9ec2900029d21573d85200072ba9ca7b0a4000ab68414f614800156b0829ec2900029da1443d85200053ac2887b0a4000a77855c361480014e90ab86c2900029da1c50d85200053b42e81b0a4000a7585d0361480015ad07a06c290002b560f40d85200053bc2a81b0a4000a7485503614808b5cd04206c290002b960840d85200053b42e61b0a4000a7585cc3614800156d09986c290002ad61330d85200263a30aeb30a4000c3e74d9661480018bce7b2cc2900030f9d065985200062f398cb30a4000c3f655d26148001878caba4c2900132d18574985200061f3aec930a4000c3d75d92614800193ce7b24c2900030f9d464985200061eba8c930a4000c9e7319261480018becab9cc2900031719573985200064fb22e730a4000c9c645ce61480099a8c2b9cc290003179d763985200062ebaec730a4000c9e74d8e614800193ae9b1cc290003179d463985200062eba8c730a4000c9e7418e614800193ae831cc2900031d9d761985200063abaec330a4000cb674d86614800196ae9b0cc290003359cf61985200066ab9ec330a400387e86dd561480010fd0fb2ac2900030f1d365585200062e39ecab0a400087e871956148001878e832ac290003171cc65585200145f436e8b0a4000c3f65dd16148001878cbba2c2900022fa1f64585200061fbaec8b0a4000c3c75d916148001938e7b22c2900022fa1c64585200061fba8c8b0a4000c3c751916148001938e6322c29000317d9773585200062e32ee6b0a4000c9f64dcd6148001938c9b9ac29000237a1f63585200062fbaec6b0a4000c5c75d8d614800193ee9b1ac290003271d363585200046f438c6b0a4000c5f7518d61480018b8ea31ac29000327dd063585200064e3a0c6b0a4004c74615d461480310fb0fb28c2900029d60765185200053ac08ca30a4000c3e75d90614800187aebb20c2900030f9d464185200061eba8c830a4000c5e75d8c61480018baebb18c290003179d463185200062eba8c630a40008f78758461480014ef0ab08c2900029d21561185200055bc22c230a4000ab48458461480015af06b08c290002b520d61185200071bb26a230a4000e3464d446148001caec7a88c2900039518f51185201ff33b16a230a4000c76769d461480018ececba8c2900031d9db65185200053ac3eca30a40008f587994614800156d0
  | 17 => 0x1a4000cb4741c563480019aee638ac69000339dc87158d200043f43ea2b1a400387c87d45634800187ee9a8ac6902c70f1d35158d200063bb8ea2b1a4004c7471d4563480010fd0e282c6900030fdd05058d205861e3a0a0b1a4000c777114163480838e8e2282c690003179db6518d200052ec0eca31a40008dd8799463480014bd0b328c690002a7a126518d200054ec24ca31a4000ad68199463480015ab03328c69000237e1d6518d200054fc22ca31a4000a9c8459463480015af02b28c690002b52056518d200052f430ca31a4000c5e7619463480014bb02328c6901ea972006518d200064f3b6c831a4000e1f65d906348001c38cbb20c6900023761e6418d200052f42cc831a4000a5d85990634800153d09320c690002b5a066418d200056ac0cc831a40008df8759063480014bf0ab20c690002972156418d2000567c12c831a4000ad78159063480015a902b20c690002a7a186418d200064f3b0c831a4000e1f651906348001c38ca320c690003a36086418d20005674348431a4000e8c6490863480015990ca10c690003a31914218d200052f436a231a4000e1f64d446348001c38c9a88c69000297a185018d200070fb20a031a4000e1c6414063480019b6c638264900030f1d764d85200061e3a8c9b0a4000c5c75d8f61480018b8ea31ec2900131d9db51d85200071bb26a3b0a4000e3464d476148001caec7a8ec2900039518f51d85200053ac0eebb0a4000a75811d761480010ff0aba6c29000e1f21574d85200043fc2ae7b0a400387c855cf61480018eb0fa8ec29000e3de1d51d85200053b42c83b0a4000a758590761480051ef0ea0ec2900029da1441d85200053ac2883b0a4000ad68310761480015ab0620ec2900029da1431d85200053ac2863b0a4000ab6840c7614800156b0818ec2900021fa1c50d85200053ac08a1b0a4000a76861d7614800156d0932ec290002ad61265d85200056b41ccbb0a4000ad583997614800156f08b2ec290002ad21165d85200056bc1acbb0a4000ad4835976148001c6ecbb26c2900038d19764d85200071bbaec9b0a4000e3475d9361480014ed0b326c2900029d61664d85200056b41cc9b0a4000ad58399361480014ef0ab26c2900029d21564d85200056bc1ac9b0a4000ad4835936148001c6eca326c2900038d19464d85200071bba8c9b0a4000e34751936148001d4b04326c29000395d9763d85200072a32ec7b0a4000e9764d8f6148001d28c9b1ec29000395dd763d85200072a3aec7b0a4000a768598f61480014eb0b31ec290002ada1263d85200055ac24c7b0a4000a778558f61480014e90ab1ec290002ade1163d85200055a422c7b0a4000e576518f6148001ca8ca31ec290003a5d9063d85200074a320c7b0a4000e577518f6148001ca8ea31ec290003a91924
  | 18 => 0x80d517d0f986c8900022f61f30d91200051f42e61b224000a3d85cc364480011db05baec690003175d753d8d2001c6fc3aa7b1a40028df8750f63480014bb03b2ec690002a7a1265d8d200054ec24cbb1a4000ad68199763480015ab0332ec690002a7e1165d8d200054e422cbb1a4000ad78159763480015a902b2ec6900029760465d8d200070fb2ec9b1a4000e1c65d9363480014bd0b326c6900029761664d8d200056b40cc9b1a4000ad58199363480014bf0ab26c6900029721564d8d200056bc0ac9b1a4000ad4815936348001c3eca326c6900038719464d8d2000746c10c9b1a4000e8c6490b63480014bd0da8ec6901ff179db51d8d200070fb26a3b1a4000e1c64d4763480014bd0c286c69000387d9050d8d200070e320a1b1a4069ace82dd7634800159b05baec690002a7a1275d8d200054ec24ebb1a4000c5d751d763480014bd0b3a6c6900029761674d8d2034d67410e9b1a4000acd821d36348001c3ea92a6c69000237a1c54d8d200046ec38a9b1a4000a5e859c763480014bb0b38ec690002a7a1271d8d200054ec24e3b1a4000a5e851c763480014bb0a38ec690002b360871d8d200052f406a3b1a4069ace82d07634800159b05a0ec69000297a1641d8d200052ec2c83b1a40008de8710763480011bb0e20ec69000297a1441d8d200052ec2883b1a4000a5f855c363480014b90ab86c690002a7e1170d8d200054e422e1b1a4000a5d8114363480d31bd0fa06c6900023761f40d8d200052f42e81b1a4000a5d85d0363480014bf0aa06c6900029721540d8d2034d6741081b1a4000acd8210363480018b8c7baac6900021fa1f6558d200061e3a6cab1a400087e871956348001878e832ac6900030fd977458d200061e32ee8b1a4000c9c63dd1634800117d0fb22c6900030fdd76458d200061e3aec8b1a40008be87191634800187eea322c6900030f1d46458d200063bb2ee2b1a4000c7465dc5634800196ec9b8ac6900032d1937158d200066a31ee2b1a4000c77651c563480018e8ca38ac6900032dd907158d200065a320e2b1a4000cd4631c563480070fd0fbaac6900021f6077558d200045fc22eab1a40028bc845d563480011bf06baac6900023de057558d200247a40aeab1a400087e871d5634800517d0fba2c6900030fdd77458d200061e3aee8b1a400087f855d163480070f90aba2c69000237e0d7458d2000477c12e8b1a40008f7815d163480091e902ba2c6900022fa1c7458d200061fba8e8b1a4000c3c751d163480018beebb9ac690003171d77358d200064fba6e6b1a4000c9c74dcd6348001958e9b92c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac69000335dcf7158d200063bc2ee2b1a4000c7485dc563480018eeea38ac6900031d1d47158d200065bba0e2b
  | 19 => 0x28fe1161546201ad1e422c2a8c403fe6621585518800117f08bb4631000a2f211768c62001c3f42eec98c400087d85dd9318800117f08bb2631000a2f211764c62022c7bc3ac310c403fde0219c221880013cb0fb0843100f6f8a036108620216363b4e52844000a3f84586508804747908b0ca1100025b61e2194220005b4c0443284400096d87086508807f1df0eb0e4110002abe1161c82201fe7338ac3904400096f8754720880bd2db0f286411010ada61e50c82202f6b4c3ca19044000d69769432088085cd2ed28641100021f61e64d95200052f41cc9b2a4000a5d8399365480014ed03326ca900029d60664d95200043fc3ac9b2a4000a5f8359365480014b906b26ca900029de0564d95200053a40ac9b2a4000e2d82193654800147d0931eca900028f61263d95200053b40cc7b2a4000a758198f6548001c58c9216ca900038b19142d95200061e322e3b2a4000a5e839d365480014bb073a6ca900030f5d074d952021537410e9b2a4000a6d821d365480854dd05b9eca900029b60b73d95200051f424e7b2a4000a3d849cf65480018bae639eca900021fa1c43d95200043ec3887b2a4055a7a80dcb6548085c5884a16ca9000e1f20171d952021537410e3b2a4000a6d821c765480854dd05a0eca900029b60b41d95200043f43c83b2a400087d8790765480010fd0e20eca900021f61c41d95200052f41883b2a4000a5d8310765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480850fd0fa06ca900021f61f40d95200052f41e81b2a4000a5d83d0365481610ff0ea06ca9010a1f21d40d95202153741081b2a4000a6d8210365480850fd0f986ca900021f61f30d95200051f42661b2a4000a3d84cc3654800187cedb2ec8900028f60765d91200045ec3ccbb224000a3e85997644800153d0732ec890002a760e65d91200055b40ccbb224000ab581997644800117f0eb2ec890002a7e0d65d91200054e41acbb224000ab781597644800156902b2ec8900028fa1865d91200061f3b0cbb224000a3d81197644800147d0b31ec8900028f61663d91200055b40cc7b224000ab58198f644802f55d0db96c8900028fa1b51d912058e1f3b6a3b224000a3e86143644816187cec286c890002a7a0e75d91200054ec1cebb224000c3d751d7644800147d0b39ec8900028f61673d91200070fa9ca7b2240008be8714f644800117b0e29ec89015eaea0372d91200051f42ce3b224000a3d859c7644800153d0738ec890002a760e71d912000557c12e3b22406aaac825c7644800147d0a38ec8900028f61471d912035557410e3b224000aad821c7644800147d01a8ec8902fe8f61651d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d91200051ec08a1b2240bea3e80143644
  | 20 => 0x2fb2ae710a6000c5c655ce214c0ed998c4b9c4298002762017388530006573a6c510a600387e85dd9214c0010fb0bbb2429800a2fa1076485300045ec20ec90a600387c859d8214c0010ff0abb0429800e1f21576085300045fc22ec10a60028bc845d8214c0010f90cba842980021fe1f65085300043ec3eca10a60048f8865c0214c0810f90cb8ca0981031d18571941300043fc3ec32826000c7571d86504c0f58bcec98ca098002d620131941301162f3b6cb1826022e5b60d96304c0031b90cb8c609813335185718c1300052e432a3182607aa5e86942304c045cb6c128460980030fdd2745972004d37414e8b2e40c2a6d829d165c80014bd063a2cb900029760c74597200062fb9ce6b2e4000a3f845cd65c800147908b9acb903069be09735972004d36412e6b2e4000a3e841cd65c800147b0839acb90003175cc73597200043f43886b2e400087d8710d65c800147d0938acb900028f61271597200052f41ce2b2e4000a5d839c565c80134dd0538acb903029b60a715972004d3741682b2e4000a6d82d0565c80010fd0f20acb900021f61e41597200043f43882b2e400087d8710565c80014bd0620acb900029760c41597200043f43862b2e400087d870c565c800147d0818acb900028f61031597200051fc22e0b2e4000a3c845c165c80014bf06b82cb900029720d705972035d37c12e0b2e4000a77815c165c80014e902b82cb900021fa1f40597200043ec3e80b2e4000a5e83d0165c80014bb07a02cb9008e1fe1d40597205843e43a80b2e4009a6e8210165c80014db04202cb900021fa1f30597200043ec3e60b2e4000a3e84cc165c800147b09982cb900022fe117558f200145e422eab1e40098ec825d563c80131b90ea1ac79012a9d60675587202e53bc0aeab0e400387e85dd161c80010fb0bba2c39000e1fa1773587200043ec2ee6b0e400087d8714161c80014eb02282c39012b1b90b765472000636a16eca8e400387d81dd951c80958de43bb2a39012b1b08376547200053bc0aeca8e405c87f815d951c80018ef02bb2a39000e1fa1d61547202543ec3ac2a8e400387e855da31c80010ff0cbac63900021fe1d658c7200043ec3acb18e40048dd83dd931c80014df0ca8a4390013991855148720004d6c20e090e404087f865c650c80818ecc2b8ca1900021f61d61943200063ab8ac32864061c6d7648650c80010fb0dbaa619008a1fa1d654c3203d43e43aca98640028be84dd7638800117b09baec71000e1fa1774d8e200043ec2ee9b1c40008bf845d5618800517908baac3100032b88774586200065610ee8b0c4000c3f74d456188163878e9a8ac3100030fdd050586205861e3a0a0b0c40008f78758461880014eb033b2a3100028fe1176546201ad1e422eca8c4000a77815d951880018dcec392a3100
  | 21 => 0x841d9218c00117b083b24318012b920562486300247cc34e010c60019d8835c0218c0458beecb9ca118002d66023294230004aec3c632846000b59808c6508c0010fb0f326ca980021fe1d64d953000537c12c9b2a6000a6c82593654c0014ef02b26ca980029d20564d95301152f41ce9b2a6000a5d839d3654c00187ae83a6ca980028fa1072d95300051ec20e5b2a6000a3e841c7654c00147b0838eca9808a97a0c71d95300052ec18e3b2a6000a6e82d07654c0014db05a0eca980021fa1e41d95300043ec3c83b2a600087e87107654c0010fb0e20eca9808a97a0c41d95300052ec1883b2a602287e87d03654c0010fb0fa06ca9808a97a0f40d95300052ec1e81b2a60b087f87503654c0450f90ea06ca980029ba0840d953000536c1081b2a60008bf845c7624c00517908b8ec4980021fa1f65589300061e3a6cab12600087e87195624c001878e832ac4980030fd9774589300061e32ee8b126000c7765dc5624c0018e8cbb8ac4980031dd9471589300063a328e2b126000c3e74d94624c00187ce8328c4980030fd9574189300061e32ae83126069c9f635d0624c0011df0eb10c498002ab21162189300057240ac43126000a7581dd7614c0014eb023aec2980021fe1574d853001c3e42ae9b0a600087f855cb614c0070f90ab96c2980022fe1172d85300145e422e5b0a6000ae682d07614c0015ab0620ec2980021fa1c50d85300053ac08a1b0a600387e86dd5614c0010fd0fb2ac2980030f1d365585300043f438cab0a6000c3c74195614c1678f6e032ac2980030fd9774585300061e32ee8b0a6000c6f65dc9614c0018d8cbb92c2980031bd94725853000636328e4b0a601f87d87d94614c00187ce9b28c2980029d60765185300061f3a0ca30a6000a7581194614c00187ecaba0c2980030f19574185302664fb1ae830a60008f787584614c00156908b08c298002b920961185300043f434eca8a6000a75819d9514c0018eb033b2a2980028fe1176545301ad1e422eca8a6000a5f835d9514c0014df04bb2a29812a9b20976545300053bc0aeca8a6000a7b805d9514c0018be623b2a2980031ecc076545300062e180eca8a6000c78301d9514c001ab060382a29800395d94614c5300052e432a298a6004c5c76545314c009ca8c2a8a629803637a18704c530006ac280e098a600d9da861c1314c0019b50c382629800356d94704c530006ac328e098a6000d5b511c1314c001ab2a238262980021fe1576c853001c3e42aed90a6000c3e74d97214c00187ecaba642980030f19574c85300065b3a6c390a600387c859da214c0091b9073b442980021fe15768853001c3e42aed10a600087c865d6214c0010ff0fb2c42980021f61f65885300061f3a6cb10a6022c5e73d96214c00187ecaba442980030f1957488530006
  | 22 => 0xa02c3281029da0740586500053ac0e80b0ca00087f8750161940810f90ea02c3280029de0540586502053a40a80b0ca000a6e8210161940014db04202c3281021fa1f30586500043ec3e60b0ca000a3e84cc1619400147b09982c3281029da0730586500053ac0e60b0ca040c3f615d0619408187ac2ba0c3281070f98174186500069d302e830ca040c5f615cc61940818bac2b98c328107179817318650006ad302e630ca040c6f619c861940818dac3390c3281071b9827218650006b5304e430ca040c6f615c861940818dac2b90c3281071b9817218650006b5302e430ca000977875846194141ae4e0b08c3280025ea02768c6500063d404ed18ca040c5f315da31940818ba62bb4632800e1f201768c6500062e182ed18ca04187f865c2319400127f08b84632808e4f211708c6500063d306ec98ca02393e849d9319400127b093b263280031798e764c650214b7414ec98ca00096d829d931940012f5013b263280025ea00764c6500063d300ec98ca04095c8758d31940018b8ecb1a632810257a1e324c650204b7414ed90ca042c6e629db21940012f5013b6432810b4b98974c865061e9710ae990ca042d2c215d321940b187cc0ba643280034e98174c865021697902e990ca000d2d7458b219400187ce8b0e43280030f5d161c8650216b5904e190ca05887f865c321940012f5013b443280031ea02768865000637212ed10ca000c6d425da21940818de42bb443281031b485768865001c3e402ed10ca040c3f615d2219408187ac2ba443281070f98174886500069d302e910ca040c5f615ce21940818bac2b9c4328107179817388650006ad302e710ca04187f865c221940012f5013b2432808e4fa1076486500049ec20ec90ca00097a801d921940018dced31243281025b21d6248650205b240ac490ca02393e841c1219400127b0838243280025ea02760865020c3f404ec10ca000c7a809d821940858dc84bb043280031b50976086502063790aec10ca040c6d215d821940070f900bb0432810b1b08176086502063a082ec10ca00387f869c021940810f90d38043281061fe1970086500049fc22e010ca02393c845c021940012bf06b80432808a5720d7008650206b8082e010ca000c6f75d49628c00159b07a92c51800a3b21d4258a3004e57312e831460008ef87588628c00195ae8b10c5181a237e19708ca30004cfc22e119460008f787584618c06b47d093b2a3180028f61276546300062e39ceca8c604aa6e829d9518c0014db053b2a3180029d60676546300053d404eca8c6000a77815d9518c0018baedb9aa3180029de0562546300253a40ac4a8c604ce5631585518c0971bf0cb84631800267e11708c63002477414ed90c6009cae625d3218c00195ae8b16431800e1fa1776486300043ec2eec90c60028be
  | 23 => 0xd8e500062f31ae3b1ca000d3a749c36394001a72e9386c7283239698e70d8e50006b5394e1b1ca000d69729c363940450f90eb22c72808f0f1d16458e501152e41ac8b1ca022c5f76d8d639418f6b501b1ac72808a57a0f74d8a50004aec1ee9b14a00097a80dd362940850fb0fb1ec52808b179cf63d8a5021537416c7b14a04296c825ce629418d6d501b14c52810a9b61f6298a5000636c3ec5314a000a6d81d8a62940b14dd01b14c5280039aa036298a5021537416c6b14a04287c8758d62940458b8e6b1ac528156daa036258a5011cb643a84b14a000a6e86cc962940014dd0c192c528002cb6103258a5021697312e8314a058c3e605d06294001a74c0ba0c5280025be1d6218a5000696ba2c4314a0c5d6a7058862940012f5013b465281621fe19708ca500049fc22e1194a02393c845c2329404727d093b265280024f612764ca50004b6c14ec994a00097a809d932940012f5003b265280025ea0374d86502043ec3ec9b0ca000a5e8399361940014bb07326c32808f0f1d164d86502043ec38c9b0ca000c3d7419361940014dd04326c3280029b60864d86502053b408c9b0ca04087d87d8f619400147d09b1ec3280028f61363d86501162f39ec7b0ca000a6e82d8f61940014db05b1ec3280028fa1263d86500051ec24c7b0ca0a7c7a7098f61940458b8e6b1ec328003175cc63d86502053b408c7b0ca0a6c7a7018f61940858dce5b16c3280028fa1062d86500051ec20c5b0ca040a768118b61941896e501b0cc3281021fa1e64586500052f41cc8b0ca000a5d8399161940814ed03322c3281021f21d645865011e1e3a2c8b0ca000a6e8219161940014db04322c3280028fa1363586500051ec26c6b0ca000a6e82d8d61940014db05b1ac3281021fa1e63586500051f424c6b0ca000a3d8498d61940018bee731ac3281029da0663586502043e43ac6b0ca022c5c7358d61940810fd0f312c3280031bdca62586502053b40cc4b0ca04087c87589619400147d08312c3280028f61062586501ddb9406c2b0ca000a5e839d161940014bb073a2c3280029ba0a745865000536c14e8b0ca000a75819d161940014ef02ba2c3280030f5d074586500051f424e6b0ca000a3d849cd61940018bee739ac3280029ba0a735865000536c14e6b0ca000a75819cd61940014ef02b9ac328003175cc73586500043f43886b0ca00087d8710d61940814ed0221ac3280029d60443586500051f424e4b0ca000a3d849c961940014bd07392c3280029760e725865000637b94e4b0ca000a75819c961940014ef02b92c3280021fa1c32586500043ec3864b0ca000a3e840c9619400147b08192c3281029da0432586500053ac0864b0ca000a6e82d0561940014db05a0ac3281021fa1f40586500043ec3e80b0ca000a5e83d0161940014bb07
  | 24 => 0x242028be84dd4604840117b09ba8c0908032b88574181210065610ae830242b1c3e74d44604840187ae9a88c0908131b5cb51181211ae1f3a2a23024200c3d74544604847dcc842a88c090ac30f9d050181210061eba0a03024200a7581140604840187ee93a2ca108269ba0a745942165d36c14e8b284200a5e831d165084014bb063a2ca1080317dce73594210051fc22e6b284200a3c845cd65085954df04b9aca108269b20973594210051f420e6b284200a3d841cd65084018bae639aca108021fa1c43594210043ec3886b284200a3f845c1650840147908b82ca1080297e0d70594210052e41ae0b28426ea6f825c165084134d904b82ca109429de0570594210253a40ae0b28420087e87d0165084010fb0fa02ca1080297a0f40594210052ec1e80b28420087f8750165084010f90ea02ca108269ba08405942100536c1080b28420087e87cc165084010fb0f982ca108028fa1330594210051ec2660b2842008bf845d5630840517908baac6108263b2097558c210246e43a86b18420387e85dc163084010fb0bb82c6109069ea0375980212053d400eb300420087f855d260084070f90aba4c0108021fe15739802101c3e42ae730042048f98790260084070fd0fbaac01090b1b1cb75580212063a38eeab0042008bf845d5600840517908baac01080237e0d755802100c6e41aeab004258c6c721d560084838e8e23aac01080a2fa1f74580210061fbaee8b004200c3c75dd160084d5958e5ba2c0109372d1c7745802126e1fa8ee8b00424dc3d51dd160084010ff0aba2c01080e1f21574580210046fc1ae8b0042018dc835d1600840187eea3a2c0108030f1d4745802156e56390e8b0042aecb4711d160084031bd0fb9ac01080317dd773580210062e3aee6b004200c9f74dcd6008401938e9b9ac0109a7331cb73580212666a38ee6b00424cc5f51dcd60084998baa3b9ac01080317dd473580210062e3a8e6b004200c9f741cd6008401938e839ac0109a3331c8735802125e6a388e6b00424087e87141600840187ee8282c010ac30f1d050580210062fb98a0b00427ac5c731416008405970e9202c0109abaa90a40580210247c43a80b004200ea94250160084095e102a02c01090a5ba0b74d8e50004b6c16e9b1ca00097a80dd3639400127b0f3a6c7280038798e74d8e5011c9fc3ae9b1ca000e1e635d3639400187cc0ba6c7280034e98174d8e501143ec3ec9b1ca022a5e83d93639404787ce8b26c72808a97a0d64d8e500070f21ac9b1ca02395f8750f63940014bf0ca1ec72800387d9143d8e5064ead38287b1ca000d2e749cb6394001a5ae9396c7280039398e72d8e5021637434e5b1ca058c6e609cb6394001ad4c1396c7280034b9d172d8e5000696ba2e5b1ca000e4e635cb63940018dcc0b96c7280035a98172
  | 25 => 0x4010fb0fa02cb1080297a0f40596210052ec1e80b2c420087f8750165884010f90ea02cb1092a9ba08405962100536c1080b2c420087e87cc165884010fb0f982cb108028fa1330596210051ec2660b2c4204a76810c165884014eb02182cb108030fdd675592210054f418eab244200a9d831d5648840147d0a39ac9108028f61473592210070fa9ca6b2442008be8714d648840117b0e29ac910b32ade0572592210255b40ea4b244200ab581d49648840956d03992c910802ad60732592210051f42ee0b244200a3d85dc1648840153d07b82c910802a760f70592210051fc2ae0b244200a3c855c1648840155f04b82c910a52ab20970592214a557410e0b244200aad821c1648840956d02282c910802ad604505922120d1fc08a0b244241e3681141648848347b02282c9108038d60450592210051ac08a0b244240a3e80141648840117d0f982c9108022f61f30592210051f42e60b244200a3d85cc1648840956d02182c910802ad60430592210246f43ea6b1c4200c5f75d4d63884091b90ea9ac71081237a1f4358e210246e43a86b1c420387e85dc163884010fb0bb82c71080a2fa137058e210045ec26e0b1c4200a758114163884018beeb3aac710802b3e097558e213b566412eab1c4200a9e841d5638840153b083aac7109dab3a0a7458e2100566c14e8b1c4200a5e851d163884014bb0a3a2c71080387d525458e210046f438a8b1c42008dd8715163884095ad03a92c710802b56075258e210256b40e84b1c4200ad581d0963884014bd0bb82c710802976177058e210054f426e0b1c4200a9d84dc163884014bf0ab82c710802972157058e2100567c12e0b1c4200cd9701c163884095ad02282c710802b56045058e2120d2fc08a0b1c4241e568114163884834bb02282c710803956045058e210052ac08a0b1c42008de87d0163884011bb0fa02c71080297a174058e210052ec2e80b1c4200a5f8550163884014b90aa02c7109dab3a084058e2100566c1080b1c4200cd563dc532884834f501bacc1109029ea0075982210043fc2ae9304420387c855d260884010ff0ab9cc11080e1f21573982210053ac08a1304420387e87dd560884010ff0aba2c11080e1f21574582212043f438a0b0442048ed82dd363484010ff0ab86c69080e1f21570d8d210045fc22e1b1a42028bc845c363484014eb02286c6908022fe117558d210145e422eab1a42008ef825d563484011f700baac6908023e2017558d210043fc2ae8b1a420387c855d163484011f700ba2c6908023e2017458d2101c3f42ee0b1a420087d85dc163484014eb02282c6908031edc05058d210063c380a0b1a424ac6d761c951484096c902392a29090759084705452101c3f42ee9b02420087d85dd360484010fb0fa8ec09081e1fe1d51d81210047dc3ac030
  | 26 => 0xe1fe1d51d81311a43ec3aa3b026200a7880547604c4018f2ea286c0988029e61c50d81310063cc38a1b026200a7981143604c4011f70eb00c0988029e2156018131005b8c08a03026204c5d73d44604c4014f100a88c0988029d60450181310056cc18a03026200af181140604c4018f30e280c098a8b96a0c50181310072cc18a030262a2e5a73140604c545cb486280c0988039650c50181310072d190a030262a2e5832140604c401ce502280c0988029e604501813100738c08a03026200a7181140604c565cb462280c098acb960c450181310061fbaceab264200a9e831d564c840153b063aac9908028fe1573593210051e42ae6b2642d0aaf825cd64c841355904b9ac9908028fa1473593210051ec28e6b264200c9d731cd64c8401c3ea729ac9908022fa1c53593210045ec38a6b2642cfaaf825c564c841355d05a8ac990802ab60b51593212e717416a2b264200e2d82d4564c852d47b03a8ac990a5b8b88751593214b71610ea2b264200a3e80d4564c84b9c5e41a8ac990802abe09515932104d56412a2b264209aae82cc564c840155b0598ac9908028fa1770593210051ec2ee0b264200a9e83dc164c840153b07b82c990826aba0a705932132d56c14e0b264200a3f855c164c84014790ab82c990802ade0570593214b55a40ae0b264209aae821c164c845d55b04382c990826aba0a505932100556c14a0b264209aae8214164c840155b04282c9909638ba08505932100716c10a0b264200a3d8114164c859dc5c42282c9909638b08450593212151f400a0b264258e2f2014164c840117d0f982c9908022f61f30593210051f42e60b264200a3d85cc164c841355d04182c990802ab60830593210043fc2ae8b1e420387c855d163c84091d904ba2c7908263721d5358f2101c3f42ee0b1e420087d85dc163c840517d09b82c7908022f6137058f2125716392c8a8e4296c3f7159151c8401c6ee2b22a390a5b8b88564547214b71610ac8a8e424ae2f2059151c8401c5ac9b92a390812d920772547210061f320e0a8e4200c3d641c151c8413958e4b2263908032b593724c7211a63bbb2a298e4234e566354531c8401acee4a8a63908123ba0b759832102477416e93064204c6e72d4660c84098dce4a8cc19080e1fa1f75583210043fc2ae8b06420387c855d160c84010fd0fa8ac19081e1f21d51583212143f438a0b064200c3f749d165884954dd053a2cb108029b60a74596210052f418e8b2c4200a5d831d165884018bee739acb108029be09735962125536412e6b2c4200a3e841cd658840147b0839acb108021fa1c43596210043ec3886b2c42cda77815c965884094ed03a12cb108029d60742596212571621284b2c4204a7681cc965884014eb03992cb108029be09705962125536412e0b2c420087e87d016588
  | 27 => 0xc40286302a20087e8710c60544010fb0e218c0a88029ea0372181515553bc0ae4302a200a3e841c8605440147b08390c0a880297a0c72181510052ec18e4302a200c6d721c8605440f4eb02390c0a88029ea00721815120d3b40e84302a200a7581d0860544014f700a10c0a88029e201421815120d3b40e64302a200a7581cc860544014f501190c0a88029e60232181510053dc0264302a200a78804c860544010fd0e190c0a88021f61c32181510051f42064302a200a3d840c860544014dd05a08c0a88029b60b41181516963ab8a82302a200a5e83d0060544014bb07a00c0a88029ba08401815100536c1080302a241a768110060544014eb02200c0a88028fa1330181510051ec2660302a200a7987cc060544018f30f980c0a88038ea1330181510071cc2660302a200a7981cc06054401cb663980c0a89069da0430181510053ac0860302a200a79870c06054401cb506180c0a8803969cc30181510072cb9860302a200e5a430c06054401cb286180c0a8803968c830181510072c19060302a200e72810c060544014f302180c0a88039c604301815168f2d18860302a2d1e58310c0605440187ee93a2cb188d297a0c74596310052ec18e8b2c6200a3e849c9658c40147b09392cb188129da0742596310053ac0e84b2c6200a3f845c1658c40147908b82cb1880297e0d70596311a52e41ae0b2c6200c7b301c1658c4018f060382cb188021fa1f40596310043ec3e80b2c6234a5e83d01658c4014bb07a02cb188021fe1d40596310043e43a80b2c6200a6e82101658c4014db04202cb188129da0440596310053ac0880b2c620387e85dc1628c4010fb0bb82c51880a2fa107058a310045ec20e0b146200a7581141628c4834f501bacc1189029ea0075982310043fc2ae9304620387c855d2608c4010ff0ab94c11880e1f21572982310045fc22e530462028bc845ca608c4014eb02284c11880e1fa1f75582310045fc22eab0462028bc845d5608c40517d0fba2c1188030fdd774582310061e3aee8b04624dc3f51dd1608c49b87aa3ba2c11893727cc7745823126e4e98ee8b046200c9c30dd1608c4010ff0aba2c11880e1f21574582310061fba8e8b046200c3c751d1608c4810fd0e282c1188030fdd050582315861e3a0a0b046200c6d75d4b624c40159b07a96c498802b960752d893101477c3a85b126204c5d73d47624c4010ff0ab86c49880e1f21570d89310053ac08a1b126209cac625d2624c40195ae9b14c4988023be1d621893125c6e432e1192620099f845c2324c4698bcedb9aa298812d5a0773545310252f43464a8a6204b56818c9514c401ab660382a298802dc60450d813101c3fc3aebb02627f87f815d7604c4018f700baec09880e1fa1774d81310043ec2ee9b02620387f87d47604c4010fb0fa8ec09881
  | 28 => 0x45d9325446b27908bb264a88025be09764c951004bbc0aec992a20097b805d932544012f100bb264a88021fa1b704c9510043ec36e0992a204976811c132544012eb0238264a88029e61b30d8151005b8c0861b02a20097581dd2605446b878e9b24c0a88030f5d2649815100537414c9302a200a6d8299260544014f301324c0a88d61fe1d64981510052f418c9302a200a5d8319260544698b8e7b1cc0a8803175ce63981510053cc04c7302a200a3f8458e605440147908b1cc0a88d3179cd639815100537c12c7302a200a6c8258e605440147d0831cc0a88028f61063981510051f424c5302a200a3d8498a60544958dce4b14c0a8b529de0562981510053dc02c5302a2d3d7171d82605446b27d0fba2c0a88030fd8774581510069bb0ee8b02a20087f865d160544012bf06ba2c0a88d25720d7458151004b7c12e8b02a24a96c825d160544012ef02ba2c0a88024fa1c74581511a4af43ee6b02a200d1f74dcd6054401a38e9b9ac0a880317d877358151006abb0ee6b02a200d1f741cd6054401a38e839ac0a88034bdd37258151006963a6e4b02a200d4f73dc96054401a98e7b92c0a88031bd877258151006b3b0ee4b02a200d2f741c96054401a58e8392c0a880353dcc7258151006a6398e4b02a25cc6f611c96054401acec2392c0a88034ddd371581510069a3a6e2b02a200d5773dc56054401aa8e7b8ac0a880359dcb7158151006b2396e2b02a200d5873d81605449dae6e3b02c0a88030fdd260581510061e3a4c0b02a200c5f7398160544018b8e7302c0a88031bdca605815100636394c0b02a23587d87d90605446b87ce9b20c0a88029ba0a641815100536c14c8302a20087d8719060544014bd06320c0a88029760c64181511a43ec3ec6302a234c5e73d8c60544014f301b18c0a88028fe1163181510051e422c6302a200a6f8258c60544014d904b18c0a88029ee0163181510051f420c6302a200a3d8418c60544018bae6318c0a88be5de0572181512543ec3ec4302a200a3e84988605440147b09310c0a8aaa9de05621815100636b90c4302a2a9b718198060544010ff0eb00c0a88028fe1160181510051e422c0302a200a5f8358060544014b906b00c0a88029be09601815100536412c0302a20097b8758060544016b106b00c0a8ad6dce0560181510053cc3660302a200e5b630c06054401cb0c6180c0a8802dc60430181510053d406e8302a200c3f749d060544014bd063a0c0a88029760c741815100537410e8302a200a6d821d0605440f4eb023a0c0a88029ea0074181510053d406e6302a200c5f739cc605440147d08398c0a88028f61073181510062eb98e6302a200a6e821cc60544014db04398c0a881e9d60473181510053d400e6302a200a7a80d0c60544014f301a18c0a88029ee0143181510053
  | 29 => 0x8ac1192c70f1d351582322143f438a0b046400c3f74141608c961878e8282c1190021fe1574d853201c3e42ae9b0a640087f855c3614c8070f90ab86c2990023de1d611853201c3fc3aebb02640087f815d7604c8070fd0bba6c0990021f61774d813201c3fc3ea3b02640087d87d47604c8011f70eb00c0990021fe15741813201c3e42ae8302643487d87d93635446b87ce9b26c6a88d297a0f64d8d5117cbbc0ae5b1aa204974815cb63544092ed03386c6a88325d60670d8d510049fc22e1b1aa23593c845c3635446b27d0fba2c6a88038718f7458d510061fb0ee8b1aa200d3761dd163544012df04ba2c6a892a5b2097458d51004bbc0ae8b1aa20097b805d163544012f100ba2c6a88024fa1c7458d510070e318e8b1aa235c3c74d9163544694b907b22c6a88038790f6458d511a43e43ac8b1aa234a5c8359163544694bd0db1ac6a88d65721d4358d510052e43286b1aa200e1d6450d63545b5aaee2a1ac6a88034bdd37258d51006963a6e4b1aa200e4c63dc963544018dec3b92c6a880359d877258d5100697ba0e4b1aa200d2c741c96354401c98c6392c6a892b1b6187258d512e637b08e4b1aa200d67611c96354401a6ee9b8ac6a88034d1d37158d516ceabb9ee2b1aa2d8e5463dc56354401acee5b8ac6a8803591cb7158d510069dba6e0b1aa200d3874dc16354401cb0c7b82c6a88035adcb7058d51006b4396e0b1aa200d7371dc163544018f30db82c6a88031ed877058d51006b9b0ee0b1aa200c5c631c16354401a76e8382c6a88034e1d07058d510072c318e0b1aa200d6b721c16354401ad0e4382c6a88035cdc47058d510063dc30e0b1aa200c7b641c163544018f2c8382c6a880356d8c7058d510063d318e0b1aa200c78631c16354401ab0c6382c6a88031618c7058d51006ad218e0b1aa200d59431c163544018f6c2382c6a88035cd847058d512543ec3ec7b12a234c5e73d8f62544954d904b1ec4a88029e20163d89511acb7c3a85b12a200a6d86ccb62544016cb03996c4a88029b61832d895100596c2065b12a20c975819c36254495a58c4ba4c4a89730fd8574989510069bb0ae9312a200d2d74d8a62545afacae3b14c4a880257e0d74589511a4ae41ae8b12a200977815d162544012f700ba2c4a88025e20174589512543e43ac6b12a234c5c7358d62544954d904b1ac4a88029e20163589516b6b3b96e2b12a24a96c825cc62544012df0eb10c4a8b56d9e05621895125537c3ac4312a200c6f8758862544b94df02b10c4a880399e05621895100536402c4312a200b6581cc8625440127f08b80c4a88d64f2117018951004afc1ae0312a23495c835c0625441d2ef02b80c4a88025de05768c9510043fc32e1192a20087c865c2325440127f08b8464a88d64f211708c951004bac0eec992a20093f8
  | 30 => 0x58040000002002001400e00100a802800a006003002400e0000040000002001000000002c001000802400400400880000000010010008024002000002c00000000001680000010070010016000000000402e000001803800400f00400000160010000070004000007803c0020020000124000001002801400000f000801803000200300080080030010004002000001800406800200500240080020160008004008002000000c014003800400e00400080300020040020008008006000000400a0000010038002000000000c0020000038000004017003000000000200000140220070010008002009004000004e0040000000006000001801801a003000800000001b003000400400901c8008006000003800001600000b80a4002002004800c010005002001c02c001000800000800100100000180000000004000006004000801e0010020018000011000000c00c00f0000000024003003800000c00000000000000120000020018003001802801a00000100080000040000018000002000801c00c008006803800a00a0080004000008001003c01602e000002c00400100c000000800a00080140160000128024002004006000000000300a000800400000100000000010010018002000007800c0000030010014002000000001400c00000c00080000260008008000004008001c00400e006001800000000000080040010000000016000000800000200a005803000c0000028040000000002801400e0010020004000001000001000201d000000002e00400000100040020000004004002001801400200e00e007c000001014004800000000000600000000010004010000000003800200b010800000a016004009c006000001800001c000015801c02000000300200000150038008006000011004c000012001000000e000000802000000400000040160060010000000000005001400c00700f0018006021001800400000200480080040100000010006003018005c00000000e801c01c005000801400a00e0000000002000000001c00200a0000018004000005000400000000000080160000018000002000001006800a000009000000a00a00600180000020000008006001000003000000500200580040000048020002007000800000c00c0018000004000002802400e0040000004000005004000000000301c3f42ee0b0c640087d85dc1618c80517d08382c3190022f61070586320053ac08a0b0c64008bf845c6608c80517908b8cc11900e1fa1f75582320043ec0eeab0464008bf845d5608c80517908baac11900a2fa1f74582320061fbaee8b046400c3c75dd1608c80193e63ba2c119003270c374582320043fc2ae8b04640387c855d1608c80187eea3a2c1190030f1d474582320043f43ea2b04640387c87d45608c80187ee9a
  | 31 => 0x7000001404a00f0070024008003001001c0000020000010000002000800000000d00100000040050018000010000000804c0100000030000000000005001c00800100000000020010000014018003005000c00e0010068058000001003803c000000006000800a00c01600040000020000004006005000000000000000180200020040018000000015001001400a001009006c000001000000000200b001001800200000b0010008002000001000c011000001400a000003801803c002002000801600000f00040320030000000000002005802800201400480000000000000004006006002800c0020040038000008000005005c0000070028018012002001000800201000100000000000000020024004000000401600600000600340010010014006000002008c0000000000060000004007801c01c00000a0074000003000000000400200a802400c005008801c00600300680040160010000000000001006000c00000e00b8004026005000002c0060060018010008002000800c0100140020000020006007800801a000000001400400200080780040010048030002005000800000c00a003803000202e001001c002002001001c000002000800401e00800000080000000048000000005005001401601b0028010002003000803c00e0000008014000009000805001200d00080080000170058008010002002000800a002000000402e001001001c0060050000090004000000007802200300000040020030000010002006010001c0080100000020000004002000000a001001000c004003000000000c019000000001c001000001c01000000080000020000000000004007006803800800b0028010014004000800001a001018000401c002003806400c000000006000000300d0004000016013001c01200d000800000000300000400060010000000000010002000002a0020058010006004000800c0460090028000004003000800000c007007000c02e0040090000006001000801800a00800180040040000030024018000001001c00200600400200000000030040000001008004c002010000803800800100080140000010008000002001005803c0000020000008006001002000c00e02900180180020170010008014001001802000200400000280000140008000000003000000800800f0000004000000005800801e0010010000002004002800001200200180440020080018004002002000002c012000001800000000001980140000030010008002001005800c028009005800000600000380180140000028054010001000001c01c000003800400001a0000028000000005001401c009004801000400c000005c01600e0090000000001000801800a0010000018004003000800400000000b001400e002004000001c0040
  | 32 => 0x49a13d24348aac00000001ef0b2272718ee16b800047280003041fbc44998b20001bca000070619d8a1a60783ae00000000290a6064f077228216f61729dde068068c48286dc6038000400923a48a00004169abe2a302200000c0a03b8000000000081b9c760be942c701000000000ce4bb83203ac0b8825705e03b80f327650a1e67109f07c8800000002fe000031400012ba0000000626204e6109d6661e97761dea04a000000000000003790be27a60d3250a96ae2f612cc0410000425800051d9e6a0000c021bd85a63ce945a79d070c078000028500006aa80001a20cfe0fa05280ef93424920aa27e11c8457e9df02c2894275f800070e934000010aa000000018c96d40001cd053a0e0a3e21c6e19c8e4200009623df8d881f6997a38889c444e119a5d69aa4053208c0850ad6331112a12f9fde6871af402a91921c908366a8932c1361d12447800042319d8000055054a80000000fbc7ee07e800012b23f3861c0db80001e41b8e000088c2ce80d07ad093a6db99c600017324628ae069200000000284000000000000000e5000008005066ca9ab66768df200016dc772188e32e1a98000188000000007b582bc14d9f2836b806205e99440000eaa1a400007f5828c2ac000059d955e000095a344000081a92b00001bb00d0947263c899c3b28c7a06b969c1e806ee09c8b2e13c138409a903c2578c6859894707699a6a442a00e242089c312932a33400004fe00006a217d8000000064c0aec00007a800010de0f999a266a192a13901281da8f7202c02c26e303887849aec774044e5b0998226500000000000185000074780003169b4c2d30cd67fc93ce12a128c1a00468498851403580000000f5e44880000001c1e0000270755071e00180000020020090008020010000002800600200500080060000018008008004009800000c000000000c02400000000000000000028004000004000001000e001000802004401600000000000020068004002000007003000e00000000800040040000000016004000000000a00c0008000002002001800000000100000000020000000000002005003801406800200100000000010000004000001000000800e00a000000000000600080040000000008028000005000801c002000000002800e0040038038010001007000401600800080000080040008008000005000000c00400c006000400401600000b4000024005800c002000008800001401b000000800e001000001003200e0008010002004009800800000e005800c00000d000000000c002000000800a0090000010002001004800800e002001004800000b0000034000000004801400000000000140c2003000809000400000000140040000020004036005000800000000000200000100050018000018007002000c02a03600c8020
  | 33 => 0x18543e694c02e9000004d81e2000044c000000070a800024b800000000000071f783cf11ac8298a6a18592de2ef9702000000043e09f46fd0664333067e4e283aa3a611102c71704000119850580000048f083d18000000000069f000000000000000d1a000000000000000001b0e000003000006d800016f43d9000078997da00006b204f807a52e1f963fd91a02648fe05a7938200a0000000102852f964000600004458d2e4769fbe00000006318f1e7238352588800000000007b603de0471ce843c97d65c31f0e71b066c78009407f411e86140bc848691ea0678eac5d9175447098762fa1e8a4df9a4e16717b440b8f8e77880000ea0a04044884c26000005530ffc1081a8e14808d8000064c48b1b481320bd24430cb63e59dba48e00fe00006fc55b0000501030481a1dee13b00004c40e6248a87d821408202610b0e0b7098e306914e7970ed400180000001278000065e000000000000002310e9c6de82be46509b6000137c61c98123cb9b7e2c0191834e852a28f894e5ed8e9a00000006639a6e381800031399545f8090a6578c380000000000000000015bc082800000014ea2a29a680000000210046e1f99f380000dc02d200006ec800878a16887cb80006050000000132837083d213596a600000005db00004d681c000019be0001e0a4ae0000000000000000000001d28000000000018e06841e0e13486ce797800056d8000322955a61d00001ad947457888e83ce1db000000000f600000001fa651117f000000000731df8051800021200004db166400002260309d1c5708000000000000011a454b00000000000000154a43b1a340000fc6165800000018dc53f00007189b16000000000014665d60df43f71f321f414b200019d401710682128c7c31708a63fa09ee7360088211199203204245a387020001cc8000000000000000000e807ab839e63d00000000000000000000011cc5b41cce1b6a0280ba8aee4328000000006c55c95fe000057c06b00003fe9a5a371000000000006ab80006810e5064f8ec600008d600000005bf883e000208a56980000002056497959c000104200017066a7861824608427028cca4b69c1875d98ec7db965437290ee086000034280003d08e8e00007183801e625261e9e2be17ba38310901cc13cc47590f4452816406c99ae0a0946417e00000f11b9a4941ece28a0c144811e425d290e04c7800000000003d707e273c91966b7085c40d0db00000a4c00000004711fa02e883ea0000da67851e601b498d206d0ac050e940a4788c72480022a3c8050002c997681f0ede4480f182940c3c78a8cd472a19241b888c617c1ca002a0a8e25916bc37d80007ea066600000001ca000044c8000411800000000001ec0aa880c9d0646317800df8d9443a8c207e400000001956000000033a1242
  | 34 => 0x5800f40000282879800013b2000080c00000006308e907e899b445c800055d9f4c000000035d8000000000000005e219080005e3006413303bc42d80a651312520001ce636287ca00000000dc1bac2ea000055a800000000000001962000000010c8fba2bc12f014b00001be80004fb000000002b6000032c0000fc400012c64928000000203632a983c7df8c7e45b00e45e181f82f90556000000024500000740cea0000d1468607543d5000076d000000003da4f6817651b82ca2a094d02c48a6200000000000000000000038481980920e6e14f921e2b9936628996ea7b01af600015de4a7904a4dd138000000005790000000073c5a500246b08e5a04b190c00006683f580002c595285d70e0200006a20958000000174e4fb8000000106c32186b400009c6611802c07b8f8400780001ba097a00020201f0898a73a8c9472980000001cfc1af1da012183864688c405520ee840612d66cc9e2e6d29f10238925c119064632b06ca2f41d567f48e5e5d08c8426900000000000414800000000000000acc0e5800000003303bc0000592000055f80005689eaa6dd9d3a108853a4780eea4091d8466986046b69dd46ef205a78782d45df849074b9b44405818606096722da00007469a4c01c0c5619119e03bc83fe4c5050a80e0958100955447c031a571000022092143da8a2e0001d1800002d2445008a71e0baa00010b4563154013e80000ec80001171ea000017fc0001610000078800008985a41df627d89823e5000051000007b9926e0000a020001d500000000000000040b0b04430206c6b580006d90e86000000021f85427eb80007a2000051489ac697874e0000c220000a006ee93e806a1294315168a3ac8ea830180002259cf020a8762696000000006281989b2230480007c7826627788f222200007070000648000000016441c50ff212b95604c70bb43cc01fe3b011be67b8f241b41f7c493914432693c456296cc6fb805e6928722565a0484d19e4e35e0e401f583ce4e31afe15994cc7f98d42815100c00007ce0000d82000028e00000003e6019418080007ed201e00d94822a50fc224903f4000000000000006888dda00000004eb000078812e470400004700e080541d3e28a9f5200015f66ce9e9a0c71bae0c99c5a38d1be4000070400001be31d972e4ba121606c00000000cfa78b004c57d036c7f918565e909da7868ec857f000073b80001d003d662d9f9a45483164ce0a7a0cb910e5898ab27b780006c31950000141e279000000019fa5851be21a3800000000007d51eb26360c0e56b0d1c0000000404000000006f82af1e347150ff00769dbc6798b606ff8a7e1d713f015b89b053c163e58a0c242d395566ea02787b20bac1588b7a6d500c616a1db27b11f6827800000000e545c90000171933400000006c7
  | 35 => 0xb88b64001308617000081f80000000000000000081602fc00000000000e1815e0d26000000009b80001500d38000000000017de5dc0518000000054d9698000000040198d600020846da882e27a81d424690121539bf2000107e4a88bb275c915a2a71fcc000048c2f999d21830e846ea800000000005cb151c6568d020ff13f60811da23688bcc1b20ca03af9a3005a02385188938000160626e128602d00006ed80004b2000057402a60000000000000028880007021cc44c8804800000002cf8000000000011d8c30568132e52115025219d34616000000000002cd000062e1f2a00000000000ea2274000000000008048e2064394f866685ec00000002331fc614796423ca89d41e113e6076178a0000454738000000014e481400000000000209800029299a400001c66531f44767800000000bc7f6800072b8b1a6830e261891d40788800075318cc0000000461835833e000029384ee4ee09fc000039a0758ca20c8a0ae0001d5e37a1bde2861ee27ba0f40000139e5b60d504a020142a98000628000000000007929ec200000001c01a620000000000000045f000072497bc0000b760c3121c67c99942ec000044b1c583858000000183e45a143c0a2065824d86a46c2a02231d051054f1bb85d018de67212f63178134000067000008ec7301f341f196be6d594c8760160c55f13a8279976010ba06649d11ba5508f583961ab82e51c98625900e52298ae378800063200000001810680182c0001d0400014ec118800000000004cc000065f9d320001ca4000000021d00000000000197047a00008d400000000001ee000008fc40200001aa00003338000000000000015100000dbc7a380000000000000034882d058628c8fd400015cc00010fe50d00004f1816625a00004890f0273b05b83120f1645e80007be800037e09566339ab4000000000000000d991e4724135875b12fe4e210825c9800006408c250017ce22006102ca9dce6fd9f243f6836033810266da00ac2b280a0587163a5f9800012692a6000000061100001d599ba3d2883c77c8000561097c18980000001456034812e8201c702fa8f7c810881063d9ad80001dd60001fc40001c383d317a60000cd80a7984c000039262a9d787c695460001a5052d0b3217300006e218a61dd121042816843e18b7e50720643fd113058e0efc398157800013b03a0899e2e5942e0001a245759324116000000000002e408f835e800080b0a7c6aa00001d195ce69e000060e9eda0000b580d712d838d9d422eb82a25fb80b87fb14c268800004d7183000015b2541135e4530a76000000002f8000657054c2ba9c96660066e00006c449c123c57c00002d0800069d96927a0094a1288d6a1b18d483ae09b41259d587481256467945c1f704d40001fa40000b4a4f9000000005e80c4800
  | 36 => 0x63411aa3a5837c58680000000000000000054f80005aa000e82480007ba960a11e0262709838400013be17780004331a560478000000000047997a83b90cae5cd00006bc800040107ec7dd99b8120a03a00011b00000000180000015c065a0000000000175e000000059796181568406553825c0e8108e000000018c00001300e7c6ce1a8600000000f20686187800000000000ed80000fe00007f207660f71a446f187b200019ac60180003770b987a09c240fb9180000027c69b12020000c260b81c12000017e71f96da00000007db11546ac0000595800035c80000001fce1371c4c0f88dac7c5975245410fc243977c2ae80001cd9dfe09e918e1940e6a0b8982a75920983e708ca73e0000000000049d8f520118ed26b281c200005d249f18201068a3a5ad175000000004af000019d09aa15784565540000000025a00009b20ac899a414000053680006c1179c649893e000000005f14e0544800062212182720ed87329efc20087d47a3186a2db000011115ee80c13ea1101c647580b9a0001c28000060a28e1682606933a6e49a260001c3e02884e2000045a0000c884a800007a7000000000006e19c606d4800041f000000000007409ba278611707811f061db105e4fd125802d93f200014a46730dfc7268c8016c9e2418204e051812ae4d383100d29bce6001ae482420060a904e68058b5a3871e8664215d82a107104de82ee4a9038c366022450d9c5235b809a00000001040000094017800007320000d5e2c8184a11794e65fa152e72c922e000032481c000014313545019cbe08f96f806586e001382c84bc800045f80962dd0000000085e000018c000000023e978230300002340016000166a14094ce15b0000000065277681a671d00003b1075e4320e240e0982261989d8287123624780007639e94000000079692a80001d8c000000074280004469ef6000000064000000001ade00016e26ae8e1a27a00002518ea643382f24b99fba11995f83ee041274c15ea40898da17e9cd415a116a2bd1420000167c3919b6648f9ad442508fe2e985d656087425e69b4000000005bc0d2200004421f102f000019681ae8e3e05b90784c01ff08289b724a4043c6cd9e3636a94a6062144a3939dd23be1ac480f11fe4b80c3200003fa0ab80003ae970a000107a0000d70000156e51a175600000006a5042c699800073e800075b9f461ab17d457994184e50d445ae80000000000527863c5a58000000000052492b40000ab6000000066f1a2c2149b9e000000030d09025e10fee36a11dc0000c283299868569118856f800052b1766000083427c80000000000000000000002ce17501180001d14000054a47b1dfa7fa88080278000000196a269800000001b600018bc0001104000204612c87f0000000016900000001a367b
  | 37 => 0xd834c40285a05038a4222f033c24c883800000002530e3062780000d587d227704aa7f500e821b9b8a0000a247eb0000452126c42786d659e90d600015ae55100002d58bf80001a0e000040a02399520000000558a0a07619948000000041808464d3000051400002f2980a2b40000000000000000000d780007fd8000000000000000004f600000001f0a0001ae200000000a5800012c0d0800020625c587fa6ba174822480e6096051216f11d47c207923678ebc000196c5429c5c00010c6000167830a8e440231f887de89ec3230d2402713de5bb896c0000916393019c000050414d072029d1cde00000000001e4c16080000f18bd659c0a3c3a4937200008d2057821c000173830d94142aa89fe59b8d746fc09cc019986229b9ce26f30ab45d301140fb14d8477999040f9a801ff99864f216e0003172a2d480507921b340000c6076211062b520726679da41001e7059f858c1819bd6000000000000006c68fd200000005e8000047b867c207985e0ec1a020de0f8c0000a165ea80004c496ac0001cbc2169a740569a5c609980265c8bf037782d857b00000001cb0427151a46b9d2c7708d5622c87be0000000207000024991640000b400000000305924040c1fe80b0109a27480007e50d28000000073487763528000000000000000000000c1c7b911842f71d3c6269a325db9edc7fb861a38f10be00005727c0a0602058cb42e308786b184165c616de3d38d3c4e99f72000000000000005370ece0001ebc6c4029800012d266c0000079127e00015ca0000b5c00007500eb12ec4a480000f8194200000000002040591936a6091b9c606070e2e71d9269c135076b13e24e704a059488de17d803c0168adc1a48a4426b84b834616a05971d9644911b6410192c5b581603b585ee420000033d12980a7000064718fe10200ec000080a4580b9e52a8e7a32393ba74a99963cb09a008c17c42a5927a53893aa7aa13260248d865049b786770dec82182600109ef00908000127000000003402b9029278304521679a1212e88866fa00f662f872642b1dc46cb030626f80983731f8e16a824e68b9d0821591c64248d624da15dc1c587ea1a0824025d052611402083418e1e0caa0a839b1daa76e0508000000034f930e76f93624b018d4000116257200002581c9e055853857019362c30000009800015a97d21b90e386fb10a819a963c6b2010e82d864e6f40d1651f8cfc170202600017ac14890b0000000062d00d808d918255d192e00000005b1873877d10c43ec102038e8a3444e998817685f416b00000000c620d69e067589a1617602e47c608766b99c8003a9de62cb17e245197f235813b641b800072e9bb40000f566be9a1a0400b280ee88225cf8d1200000900c2000020503f65fd1e5604811b80c788b4000080400000007e780
  | 38 => 0x62022800000000000000000030607b82ab84da2ff800025b959231080003c280001da1c2022414580001a14000080e35910bc0000bbc20b1af800003743b0800027280001c708c033685981d6a0347a89cc600000000000ca43dc06b81708d34000000082200003348c1e546018e22b128470c023a41c84340d40ce459313a415818b00ad06120001a7a67a0000630000008300000000a7237610a241502c432e952000000004e88000000000046980007ea80000000fe46e013d05928efe6a991183de000019298a435f17c85c700005eb800075491426a487b610986e66c519b20e413e081d191a66d9c8a4ef0dbe34c0b665c49aac34d846c0ba1ff86f09ef81d1013c57c9c724578d200409fb219596807d28000173800044f1fe2337180c5ba04a465f1dca2430a0e799800020c191638c8c2e6581ba620a0ad20a692ac7f298e66b305ea00004c2652897e5498ce627e82f441393600001bdc54c16c45da8c001fd98400611e32000000000000005a18000760858400000004f59b2e00001107f81730036978e5cf1ace000067800000004af8000000000052300000949a7e00000007af800028c00006f9849856d1e8460e0f5a1210c826271c06766800036007a4705021031a8000000000000011b21628000000078a70c830213d897858c000038b80000001bc062112302190cc01b517c210a11362921ed475c04fe4130e8c1ac1a3814c913400017946bb800075101ca4f08f740000bf26f5000005a800080280004f7000024191ce33d80005f70d1e06000003bb187049180003a5000000008c86500b802a219f880905fc1ea9a2a0720fca01492d06b81eba00018a27cf87e41799abc56a0cc63bd1b3c07c8c4400009c0000006a00011bc623162a04a8708299041e4078a703fb000075f013224c057423992fc70091087fd03f26e403c25e493325549c942849c6a00016b23db82764de14547bc939a08d000072209005de80000001558000059464c95c648980004068000000156400006940001e3e5e40b460001f2c35707345118db61b7962e0b7964e57800000a81f306519f48134171e3d8940201c873a5d18e4801e09500ce06f02f114d60dd90ba3be80000001a603190f0c0001b7c0000cde38a99ca1e700000000d6c67d0d8c0418ac2000039c1278ed074983461ee8a4611c0920000074854c906a083855c8238b087a98f0026608ba000057a17100005be80002af8000000000000013fa00011663e980002a918ac43d9a08000119c1e51e1c4391fd837580003b68f7a0000000000125a00000f051e800018d95aa0b191f68071c2e021981c73684f46e903184a580000000ac882b08a26f2006073719c01a10ce252e962c0100b02791872a33c8a541d306f4365879a4e48a860000d6808b000081d9ed00000b860000dfe1
  | 39 => 0x359800036e94b600020a40648ad8000032852f024478c008417917ec51f1f406fa88b005881c46681aa0662896a0da09521eb1f583da03d4008840e1ed000026a1f925ae041c73d0c505e899fc6a580f818e9f04000014a0000de00000b300e912723738f3600019103f2000072a800000008aa00000001ba862e7670c6c47f04945178ef663e99145941c504a6824c3e402807b48c9019e968c190053024f09f843700000001f645bc917470000c42268cee80613021d603326f6008255c0f3e5a90bd43d20bde36412fa70887c81770c086e6121265c0ada2c51ffa3261f86147013a09513c058494fa000120859d19de46a043e3fa969a3c99a0a00000002709e3c000019a000125440d80005e580006228ee240703362ce0862711069c68f80565bb09e224a18320000866000190a0000ac40001e3a2a605f238b142452a00003f0149639c8000000089400000003f985ba5431058000000000004f2133812675a209a37200003671c365240bfc2a80000000000042605fe3c88ea041584b40000c4c723176843c00005109eb000000001129808776015c00000007d7000031481728040000000089e000115c1620d000c0170000000000f90fbe00014a00000000000000056e8c3a1a6075200004bc6db07ae80f97c057a01240000db825d82f631981440001f427528a066948c6e000135600000000001dcc4d280001af9efe6b0163201a0edc4a21b963c180003561ab211a80000001b26000193a7069b281c69c8610c1a280a402ac00016b0450120635380005021eb61bc855839c00000001e167f092ca65d08060a51ad067d80002de000032f00001fc877c418843a45e0bee4e61bfc0c3a00877914885d10b706a31eec0001f3c00000003e807a21bb139063f159e1e38380806944832a00006a28fb637506a039714d43ca18527e2800056600005e21d4e1e309700919e4461f80003d40000543800064a17286ef97220000fd81e7833a39a000054e82a874397c65cd9b3e2689032046800000000005c380003cd000021f18341981d9000008e47058000087887209a059015100004d49e6c2fd824a49800000ac09d62a694327dd050e23c092a19200000000a360000000000000052b800000014f415d97203e00000800198c0000bb84a7008000000001ff0bf429701220001ef45c519d612480006dd1f0c2069d6a12b1eca4dc00005fd80002c6158613280000000a780d387cc000005818d00005ec0c964c616ca4721c0e00011f23f412aa22e0a5e1b095b00001a420001e900e28dd23e790b84be132005380002f000001bf946a08c913e2d902cc0f000002d50f4463119fe5f40a563611b024c19d48084a0aa6c49f980000000748836a0001fdc7ec0b9232f800000000005378074749000000019981a68be02bf87f40b582ec7d59
  | 40 => 0x926a42900001e1994e70d124425983cc000000022f8e4a6241ca200000004db800006a8f0e00000000000d9224899124299e92513876464e1c6820c9b0064117104219f5003f0000000000000b800049901bc21ea02e4369816149009463a0000000122256e069e6818b501590d7e28b01dc4ba81ba2520faa0cf9cd609914d2803000018b0000000205c82c84c600e80c000116e4638800030f80f220494f62c180000001f666f813fe09780003270e88299800079e80000000ffe3c40dee03e8b5e0001e6e00011561638000000143042213960aa8fb46611b505ad85a25b000001a28e107e0001013115143990eb4827800000016a274e17b241102f80a1855200017786d09dae00000000000000000098c5b20e7e817800000000007950fcc18f903a08589100000b2621508a44b38a682410334670949c2c9040c1e98af6371961e72d8bb63ab8f66766130a2f19c3c5fe83540000000395820260a0da40000c787519eb8000124c00004140000e28000140c0001d104cd987858d810a25c80004a3800000009ba45d8a520000000000000000000000000818000000072d0b4475d0f6059616d25640000000000029000000000000000073e0000ace0e880e03f8803800006aa2380000188800000000007e09a64146800000017980001d7a0001a8200000004c103643c700005d88e0463916680000b720889b200001d0c36d1a547718cc87109ccc2e08000000000058116086120c9241d94944c68000000187c22a120e33c06542d880003410000557048e000000036399020150d4c37e95005f29b5871980001a9800014f01541e01f5e78e001a36699ea00000006788eb600001fa00000002a415d2032804a3a289124309a3a00002da2641ecc7ab0b8a7ce9624419859a2618c9e2831a727c01cac8010f143998e781f819066e809446ba81f6711800026f1da800008582338d2a3741d5c1b016fc44492c405c209c65986380000000000000050e070a5b990ae1a596346e50ea43569f120b992820001508288074a23d92c22ee9e684bd17fe4ed000061b87960000ade5aa9b4e11f12dc21c130c40a93a0520000042c88ae4dd983600000002fb147816d8954620800000002b838384a6000000000018ea000000066700000000000000148e00000000000000508822e656072e00016604f2857e13a9c4e5f3173a1839c7a62480006478f1200000003eb854807f17ea54d08ee6fe8f8a00013867ff9a9c2a48d4077a101400014ca77f016c00001de5dd00f40e980000000fb2715993450a086c7d3951e355179e00001b841c0f1a78400002e380000000ba075680007dc086815181ea70307703a7800000006cc7808000565000000006ae62a0000825800015501e8794800031c021a7f0165a52889965310b7c16f80006d780001181616
  | 41 => 0x58080000000f04296023c5999c4810e13ae000000039d813059b15da6dc141023690e667914266d81ce468f110232c93d43309b5a120018a45601406f698f010111d00549708474848877a9ea456398867da9cfe4999c402a0084e526958011c90d00ed1b184470ee605d020647e153857505b04d91b064830afc000110082c076054890840001b626738cec41905c82bc8cb02738eee63e18940689dec21812d410a810803883726f115067c8006e5dc84f87ff014800805d02ba007e3ea00007770000000010c4d200002210bda79910fa3010000000171a0001b8413a00ae8008dea3eb000020904fc08a14ee81e803e6138000000000029b00004361f1400000005458000000004471f1344820941a0001860035000000000000000b84000000000000000001b8224d000000000006d7011679419782000ab809b052e5f901ce02e80000001bd24c580006c907ee00016ce07d0b1e000083a38500007e31190000103800001a40e61ec618a9a9a2cd807c00ca04c5fe000000008dc0000f7674d9b466cc0620580000082503ca0001b08000186c23a847446d1f600001d0034b00cc7960a102c407de3e880dc0001e080000bc200010746bc19f036c80000fc17b80001a842fe985a000105c6489a462b88afa79d830a00011d87629e72137838e79f886a1cb000051b18ba00000002239c4a000098880a802a8110fa40de8138000092c55a000009d000081e0de607c19d01de00007cd8d0e3549e40000000041200002cf000000002ba0000000566800000008f412d9cf6056133e4b880002db9cb809f9a4079e180400000000d11fb653f801458382d048803620379f622b1933c70b1c8245b9d160a28f8200000006bf088a0001a1e44a0000000000042280004a2800000000001dfa052000138e00013fc619112e000123452c0ecc00012b679f14c639490e23e484487c987c06c7800a67b0df000017be000000000000001458592000157a47d1dc073080341db85b476d80000001f1c343196e000196439d01ec549047e5598a5a2a79bf87a59c5e3db19aa43a158853c8712050891c1118d462da800048c83b800011fa3680c46106143e60b9ad27780c5800000003fe18ca12280000000000000000007481e630b000200000007e700006a410d401d87f83f787820000bce7d6
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x401871811c05058d210052a640215d06048401c24215d151181210060d5d181140604848386572604501812100417e61731cd650840181d845cc73594214b6a820542501600840121d9898e74d8e500050765e639d3639400121d9898d74d8e500050765e635d3639404521e98d9143d8e500051365e639cb639400160d9498e72d8e50007039d2639cb639400144d9798d72d8e5000583652635cb639400141d9498d71d8e50006076137398d619400181d84dce735865000613dcd829cd619400105f985cc73586500061360f729c9619400141d9498e764c6500061698e809d9319400105e981d9634c65000507650739d9518c00185873a02765463000417e6176dcd518c001455910c0765453000554644501c1314c00145896544704c5306de169d8804c6504c00105f985cc735972000607611731cd65c8001a858350b4018520005a82414250061480012a59890840185201ed38a43819db214800142e96d4574c85204b709187515d3214808542e9614174c852067709184505d3214800148d9719063c85204b629a1974d872148001c27655d061c8520007091957418721480014a797d9061c85200052965c641872148001c8574d8c61c8520007215d063187214800182c865d151c85204b7091857454721480b182e76613219412061e8918584c8650480018a461e11718812000607615731cd640800146591141768842000623e1e73592210809542d97d4564884202e50be5d51592210800142d9714164884200058964450592210800182d8759221940200051aa4351dd9200800142e97d456448020007091c751591200808542e9714164480200052325d641cd20080014a69759071480200052925d641c52008001c27755907148020007091d5641c52008001c8564dcc714802000721590731c52008001c2685590714802000709615641c52008001c256414071480200060b21d645452008001c247159151480201f51925d6154520080018648758551480202c60ba1d649412008001c25641c6504802000417e61731cd65c400181d845cc735971000607613739cf658400145a90dce73d961000417e61731cf6584001837746045058a1000615dcd81141628407f4679758951c86100061961f65d8821841a325a96a035118d10597140407618d5144001c1b6418c705451000706190631c15144001c4863d8870545100070a190621c15144001c4863188705451068e16a0063dd6104400166290dd4628411000598a407518a1044001870706045058c1000694dc1811416304001a51811c05058c10006291c5841c16204001435919d564c8010005156467558f2004001465919d562c80101ee292057458820040814729021776440100070cddb749411004001c5376dce504401068e54a1c739411004001c6376dca5044010
  | 1 => 0xe87c358bca89a280e0980400084ce483080800001980000a4000ec003651000000012a4d5c00519e5365f00000560000000004a0f0352091500e8006c000000000230a4e235139ec960054000006d000007a000727c00230000000004500000004010828000b0010600271bc7800298140000000a000000e18c002e49188009500075427f00000d2892a800009700250003e5680000853f00002a50d9013c00000000000002c400000000000003b1791845350010c26001340087000011c00000006e5a000e40075320008200000011a000484cb200122200000000000000001e800001900030000c948160000000000000000a2471116006002da3c00000000000af00000007000068ee00328c0000000019080039855388b40ac0ac2c331e00031080000098000d02e200000000ab3e93d329d2187c22495615cba4405298d02d000300060538492ca9412a8dc00151700000000fc0072078000e0805000060101006000000800000180400000000c220000004020202010020200008020400008020500000040000000000000000000106008000801814020403000000300487a6063dd1635440141e9718f7458d5100487660631d1635440141e9718c7458d511a4872616450d635440144e9718f7258d510058365063dc9635440144e9718c7258d5100583650631c96354401c0c7418c7258d5100516a5c63dc163544016199418f7058d5100507650631c1635440145a9718c7058d5100586650631c16354401c1b7418c7058d51007061d0631c16354401c4863dc87058d510071218c721c16354401458935907058d510050e650631c163544015199418c7058d5100706a50631c163544014599418c7058d5100706650631c163544014199418c7058d510051625a431c16354401c1b6490c7058d5100516259431c16354401c196450c7058d51006161cc8058d625440181d845cc631815100586650630c06054401a5063604301815100417e61731cc605440181d845cc731815100615605731cc605440184d7360873181510061360d721c86054401865815c8721815100586652830c06054401459970c8301815100586650320c060545a3a5031604301815100694a0d810c060544838557360450d893159516a5b301c1514c483855736045018131596948c581140604c565a5031604501813100694a0d81140604c401a5183604501813100694e4d81140604c401a50936045018131006949cd81140604c401a524360450181310069450d81140604c401a52326045018131006940c981140604c40181d855cc7359321676898858114164c8
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa5a006100056a48160c07012e08001206d48e8318e4b1aa200906ea77418c7058d51004833523a0c6382c6a8802c09a418f721c16354401604d20c6390e0b1aa200a066907320163589510054234849b02280c098802a11a49cd81140604c401508d2064c08a03026200b08680215d1511812100481b533a4c7396c728002819a498e809d9319400140cd20e7404eca8c6000c0661290dce73d9610
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x124d
  | 9 => 0x3
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138c
  | 16 => 0x138d
  | 17 => 0x138e
  | 18 => 0x8c
  | 19 => 0x8d
  | 20 => 0x8e
  | 21 => 0x128d
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128c
  | 26 => 0x128e
  | 27 => 0x150c
  | 28 => 0x150d
  | 29 => 0x150e
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12cd
  | 33 => 0x12ce
  | 34 => 0x134c
  | 35 => 0x134d
  | 36 => 0x20c
  | 37 => 0x20d
  | 38 => 0x20e
  | 39 => 0xb0c
  | 40 => 0xb0d
  | 41 => 0xb0e
  | 42 => 0x140c
  | 43 => 0x140d
  | 44 => 0x140e
  | 45 => 0x154c
  | 46 => 0x154d
  | 47 => 0x154e
  | 48 => 0xb4d
  | 49 => 0xb4e
  | 50 => 0x144d
  | 51 => 0x144e
  | 52 => 0xbcc
  | 53 => 0xbcd
  | 54 => 0xccd
  | 55 => 0xcce
  | 56 => 0x15cd
  | 57 => 0x15ce
  | 58 => 0x94055
  | 59 => 0x94056
  | 60 => 0x95255
  | 61 => 0x4b
  | 62 => 0x8a
  | 63 => 0x128a
  | 64 => 0x134a
  | 65 => 0x14a
  | 66 => 0x134b
  | 67 => 0x134055
  | 68 => 0x154056
  | 69 => 0x124b
  | 70 => 0x124956
  | 71 => 0x124955
  | 72 => 0x134955
  | 73 => 0xbc955
  | 74 => 0xbcb
  | 75 => 0xca
  | 76 => 0x12ca
  | 77 => 0x130a
  | 78 => 0x139256
  | 79 => 0x135255
  | 80 => 0x21256
  | 81 => 0x21255
  | 82 => 0x155256
  | 83 => 0xbd255
  | 84 => 0x135395
  | 85 => 0x98096
  | 86 => 0x99295
  | 87 => 0x98095
  | 88 => 0x14b
  | 89 => 0x134095
  | 90 => 0x140096
  | 91 => 0x140095
  | 92 => 0x19cb
  | 93 => 0xbc095
  | 94 => 0x128996
  | 95 => 0x128995
  | 96 => 0x134995
  | 97 => 0xb0996
  | 98 => 0xb0995
  | 99 => 0x98b15
  | 100 => 0x154996
  | 101 => 0x154995
  | 102 => 0x99555
  | 103 => 0xbc995
  | 104 => 0xcb
  | 105 => 0x12cb
  | 106 => 0x130b
  | 107 => 0x151296
  | 108 => 0x151295
  | 109 => 0x135295
  | 110 => 0x21296
  | 111 => 0x21295
  | 112 => 0x141296
  | 113 => 0x141295
  | 114 => 0xbd295
  | 115 => 0x135515
  | 116 => 0xb1516
  | 117 => 0x150b15
  | 118 => 0xb4b
  | 119 => 0xbd515
  | 120 => 0x12c9d6
  | 121 => 0x12c9d5
  | 122 => 0x14c
  | 123 => 0x1349d5
  | 124 => 0x168e
  | 125 => 0xb49d6
  | 126 => 0xb49d5
  | 127 => 0x19cc
  | 128 => 0xbc9d5
  | 129 => 0x1352d5
  | 130 => 0x1452d6
  | 131 => 0x12d455
  | 132 => 0xbd2d5
  | 133 => 0x15d2d6
  | 134 => 0x12d5d5
  | 135 => 0x21355
  | 136 => 0x134215
  | 137 => 0x134b15
  | 138 => 0x141355
  | 139 => 0x135415
  | 140 => 0x135555
  | 141 => 0xb5355
  | 142 => 0x134b55
  | 143 => 0x135455
  | 144 => 0x134cd5
  | 145 => 0x1355d5
  | 146 => 0xce
  | 147 => 0xbcb15
  | 148 => 0xb8b
  | 149 => 0xbd555
  | 150 => 0xd0a
  | 151 => 0xbcb55
  | 152 => 0x15cb56
  | 153 => 0xb55d5
  | 154 => 0xbccd5
  | 155 => 0xbd5d5
  | 156 => 0x16ce
  | 157 => 0x16cb
  | 158 => 0x1349405d
  | 159 => 0x5396
  | 160 => 0x95256
  | 161 => 0x160a
  | 162 => 0x14054
  | 163 => 0x4955
  | 164 => 0x5555
  | 165 => 0x56d5
  | 166 => 0xc056
  | 167 => 0x168056
  | 168 => 0x124056
  | 169 => 0x4956
  | 170 => 0x5556
  | 171 => 0x5696
  | 172 => 0x125396
  | 173 => 0x10b
  | 174 => 0x10a
  | 175 => 0x94155
  | 176 => 0x14d
  | 177 => 0x19cd
  | 178 => 0x140d2
  | 179 => 0x15394
  | 180 => 0x95355
  | 181 => 0x5256
  | 182 => 0x24e
  | 183 => 0x1380d6
  | 184 => 0x8995
  | 185 => 0x9415
  | 186 => 0x9715
  | 187 => 0x129516
  | 188 => 0x98155
  | 189 => 0x999d5
  | 190 => 0x99355
  | 191 => 0x98bd5
  | 192 => 0x150b16
  | 193 => 0x151716
  | 194 => 0x150d16
  | 195 => 0xd1352
  | 196 => 0x138056
  | 197 => 0x99296
  | 198 => 0x150096
  | 199 => 0x9c0d6
  | 200 => 0x15354
  | 201 => 0xe80d6
  | 202 => 0x21716
  | 203 => 0x20d16
  | 204 => 0x141555
  | 205 => 0x141556
  | 206 => 0x14d12
  | 207 => 0x155415
  | 208 => 0x155715
  | 209 => 0xc152
  | 210 => 0xb8e
  | 211 => 0x138956
  | 212 => 0x125556
  | 213 => 0x21556
  | 214 => 0x155416
  | 215 => 0x140b16
  | 216 => 0x19cbd4
  | 217 => 0x16d456
  | 218 => 0xe96d6
  | 219 => 0x4154
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1798
  | 6 => 5703
  | 5 => 4188
  | 4 => 178
  | 3 => 14
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (73714+((h/599+packedAt gbK7 (66526+(h % 599)*12) 12) % 2373)*12) 12
  | 6 => packedAt gbK6 (298457+((h/1901+packedAt gbK6 (273744+(h % 1901)*13) 13) % 6844)*14) 14
  | 5 => packedAt gbK5 (265240+((h/1396+packedAt gbK5 (247092+(h % 1396)*13) 13) % 5528)*14) 14
  | 4 => packedAt gbK4 (12991+((h/59+packedAt gbK4 (12460+(h % 59)*9) 9) % 311)*9) 9
  | 3 => packedAt gbK3 (1154+((h/4+packedAt gbK3 (1134+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff00ffffff803ff807fffffce3f1ffcfe31ff
  | 1 => 0x1ffff01f80ffffffff81fffff5c8e88f23fe3f
  | 2 => 0xe07fffe000fffc0ffffe0f8039f0f0f3c3cfcc
  | 3 => 0x7fffffff00000ffffff0003e00ff03fc0ff0
  | 4 => 0x7ffffffffffff0000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa090016289282092801214aa801303344e10d5
  | 1 => 0x1d24b015105347253481a95514c8688920e62a
  | 2 => 0xc4595aa0289da889d9740e01a970b0d2c34b4c
  | 3 => 0x86e6cd9f200c10e6e69c0063e00dd03b40db0
  | 4 => 0x907f8f1e7ce6f3c00c3084183fbd0003fbb000
  | 5 => 0x1e0c081040070200704108603feefeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37429
namespace PEqualNP.Outside.L_meta_37429
open PEqualNP.Outside.L_meta_37429.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
theorem alls0 : ∀ k ≤ 2, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 13 := bs1_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat bs4_4_288 (concat bs4_4_320 bs4_4_352)))) (concat (concat (concat bs4_4_384 (concat bs4_4_416 bs4_4_448)) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544))) (concat (concat bs4_4_576 (concat bs4_4_608 bs4_4_640)) (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 bs4_4_768)))))
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
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 bs4_5_384)))) (concat (concat (concat bs4_5_416 (concat bs4_5_448 bs4_5_480)) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576))) (concat (concat bs4_5_608 (concat bs4_5_640 bs4_5_672)) (concat (concat bs4_5_704 bs4_5_736) (concat bs4_5_768 bs4_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 14 := bgb_3_0
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
theorem bgb_4_160 : Interval gbAtlas 4 160 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 178 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4188 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))))))) (concat (concat (concat (concat (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176)) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816))) (concat (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 (concat bgb_5_3072 bgb_5_3104)))))) (concat (concat (concat (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 bgb_5_3232)) (concat (concat bgb_5_3264 bgb_5_3296) (concat bgb_5_3328 bgb_5_3360))) (concat (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 bgb_5_3488)) (concat (concat bgb_5_3520 bgb_5_3552) (concat bgb_5_3584 bgb_5_3616)))) (concat (concat (concat (concat bgb_5_3648 bgb_5_3680) (concat bgb_5_3712 bgb_5_3744)) (concat (concat bgb_5_3776 bgb_5_3808) (concat bgb_5_3840 bgb_5_3872))) (concat (concat (concat bgb_5_3904 bgb_5_3936) (concat bgb_5_3968 bgb_5_4000)) (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160))))))))
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
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5703 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624))) (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))))))) (concat (concat (concat (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520))))) (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))) (concat (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)))))) (concat (concat (concat (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416))) (concat (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)))) (concat (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))))) (concat (concat (concat (concat bgb_6_4992 bgb_6_5024) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120))) (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312)))) (concat (concat (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)) (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504))) (concat (concat bgb_6_5536 (concat bgb_6_5568 bgb_6_5600)) (concat bgb_6_5632 (concat bgb_6_5664 bgb_6_5696))))))))
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
theorem bgb_7_1792 : Interval gbAtlas 7 1792 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1798 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 3 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888eaeaeaa8eac8e888
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264040 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37429.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[5,6]⟩,⟨.or,[5,6]⟩,⟨.and,[3,8]⟩,⟨.or,[1,7]⟩,⟨.or,[3,4]⟩,⟨.and,[1,2]⟩,⟨.or,[9,10]⟩,⟨.and,[11,12]⟩,⟨.and,[0,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37429

open PEqualNP.Outside.L_meta_37429 in
theorem PEqualNP.Outside.L_meta_37429 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
