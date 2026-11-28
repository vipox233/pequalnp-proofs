import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36681.Model
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


end PEqualNP.Outside.L_meta_36681.Model

namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
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

def SBf (j : Nat) : Nat := [5, 4, 7, 7, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36681

namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 3 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x104b092124851444848a8b162d545b4a936b5b
  | 2 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 3 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36681
namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
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
end PEqualNP.Outside.L_meta_36681
namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1078000003005e9000800b8bb00074e0d3e84b033064d8b12a80000050d000a453072000000048872d402960050c460052555a33c9498000000004e48080000020001000000306000051a0410aff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe426001e02a0037800001d0d80000011fa680e47470581480430604000198e43e9b0e278004e330009200210004600001280017000c4780042140b20000148009f442240083000b0008d01144522f1d00000814801048004100000003a89424001b80118581903c56a2399c0000000150f6930000032001b0693062001192861001a14605041746a00218011e11000b81c4d20000be560016800000000050712da1caa6e15000ce574e001140001800d27c2e0f4c6975080140650013cfc5332030167a1698096790004d2c38069fc00003e8c0769d000008a9536931320624024d8000800000920024400003b9ac002113905160011290d4000000000000f1d8bc44002146874000507c0001010008800087010101080582000203828001848080008200800080080000820001020000800000028000800e80048781028081000281dd94743baa8e873e52d0f6ca3a1cf54743daa8e873551d0e7ca1a1cf55243cfa9a873c5250e7ea2a1cf141439f2a0877651d0aeaa3a14f54e429f294853d5190a7ca1215dd4542ba28a853d5310a7ca4216b948429ea88853e5010a7ca9994f55332bb28e657551cca7ea9194f152329faa2653c544caeea2995d14532bda826578504ca7ca8194f550329ea9e833e52d067ca1a0cf55241b7a92836c525067ea6a0ebd49419e29283ac5250658a4a0edd45419e282833e541067ca998cf55331b7296636d52cc76a8398cf952319eaa4633e544c67aa898cf950319eaa063b5410c67ea990cf15321dba0e43b541c876ea990ed15321dba1e43b543c876c8590ed10b219f2a4433d54887588510dd946219faa2433c544867ca810cf55021d621043b7410876a8210ed95021daaa043b7430876a8610dd94821f329043e7420876c8410ed10821f221043a442087cc6410f94c8219ea9c813e529027aa3206dc8640da10c813e50902eca2205d544409ea98813e521036ca2204f54440daa888135511036e42206d084409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f553209f2a4413d54882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a2904fd50209e2a041e4210827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6824d0f2e0809560ccd880041c2a008169d0a105a374780361cb8c875ea528050018bb0085b8d6a0000c0089312380121328e489f0c00027140d62b0000c322c5000097000408b0e10f800a005802a214039918951d0e2c6254743a918951d0f2762547438d18951d0f2462547438918951d0e3561141438dd855390a3561942428d584548ca356195032c9d84525072452d4541a918941cc72652507318d586544c62c62551318e181544c6a462504318758c54c86a662d5321a558c54c86a662153218d99743c862d65108218d59743086a46250c21a998a42086a76510821a959442086a56310821a998042086a4648c821a919132086e0604c8218dd855390326520864099189511022c6254440a9189511032762544408d1895110324625444089189511023765c84408d594211023561953308d584548c2356195320c9950218821d63150208d58454083245408420a918941c422e62d52108d19541443145350510a918941443245250510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xa00004020cc0381014880212392c228287419cf611494190ae7b288410c25751923208613396c2a9c81091c96195330848e4b08a918505731502108302298c4a0a21091d85250510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (912+((h/16+packedAt s2K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s2K4 (4895+((h/55+packedAt s2K4 (4455+(h % 55)*8) 8) % 239)*9) 9
  | 3 => packedAt s2K3 (2420+((h/20+packedAt s2K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s2K2 (502+((h/3+packedAt s2K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 1 => 0x7e07ffe03f81fffe0f81f81ffc3e03fd98e67
  | 3 => 0x7fffffffc001fffff001ffffffc003fe1ff87
  | 4 => 0xf8007fffffffe07fffffe001ffffffc1fe0ff8
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x3021088c4891040805292592300529920ab0ab
  | 1 => 0x524b391439232939605b0ab0d64342b4d98665
  | 3 => 0xa486522890745252ab0413656aa80529615b86
  | 4 => 0xc614644122460364d29640418d329601b40d50
  | 5 => 0x7187871c3879c7f1ce79c780e231831ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa00eeaa8800eeaaaa00eeaa8800eeaaaa00eeaa8800eeaaaa00eeaa8800eeaaaa00eeaa8800eeaaaa00eeaa8800eeaaaa00eeaa8800eeaaaa00eeaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36681
namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xf070000d800a30088265cf9212ad3242a9d11622292805000c8046855001e0000030507000c0002d402c00300b010008a481c1a68e800520430c50110c1005041ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2b12a1a900000012060000002d0031000014003884979f0eaa1680002c378000000011000000000000001c9f800027358000000000000000000000000c00000000058d8000000013000000000120000000000038000000000017000f000000003a00000d00210006b380000000000000003000100013819b8000002e0000000019000000000c9a800008000000000000000000000000000000000000000000002ea4b2a3020000038000000000001c000000000014aab304000000003980000000118000000000a8800000000025002380000e0000003600002f830000390027800000050a000000000a80000000000000000000001b0000088000000000000022b4000000000000000000158000000015108b8000000000180b000000002f1d0000001e0000000020800000370000078280000000000036802980350900220000000018b09a0031b20000282c80000016000000099ea5a6000000003487000fab80241da699ad800010000002000000004000080c00000000802050080c0000000000000000040602008080c0100008000000db94a43b6a9487765190eeaa321dd94742baa8e853e5290aeea2a15d14542af298855d5310b3ca6216754c429f29085ae5210a7ca9994f55332bb28e657551ccb5885194fd51329e2a265ac424caeea2995d14532bda826578504cadea4a0db14941daa08833e54cc67aa998db94b31b6a9663b642c87688590cf952219eaa443ac42886eca310cfd51219e2a2435e53086baa610eb10821eb29843d553086eca410f994821f3a1043b642087688410f910821d221043e632087ca6410d794f40aea9e815f53502b8a6a05bd4940b6292817751502e8a2a05d94440baa88819e428c338851875c8630ea10c615e508c27ca8184f55030b7290616d520c2eca2185d54430cf2a0619d540c39ca4187354830cf210619c420c3aca2187554430eb90861d4210c2bca0187694030af29e415d53c83b061904f952209eaa441ac42882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a2906b10820f210841d830082bca7885754f109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x10a16800026b2e002000a8a48651e90e01a01800888000430001c0002002c0001040c9108514cb284214132a9189411070d5310821a998a42086c56310821e198c42087856310821e194c42087855310821a919132086e0604c8219918951103844208630c3551520c21d6510830d1549510c2556508430e1108210c3244294620c99502188388420c020f0084300822c6255010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x20c10a0aeb3188410c857694c4208682ba88410861815944208430
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 4 => packedAt s3K4 (3510+((h/39+packedAt s3K4 (3159+(h % 39)*9) 9) % 359)*8) 8
  | 3 => packedAt s3K3 (960+((h/8+packedAt s3K3 (912+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffe07f01fc07fff83e07ffc1f07e03fd9e267
  | 2 => 0x7fffffffe0007ffffc007ffffff8003fe1ff87
  | 4 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641230a29a20b0cab
  | 1 => 0x2a14b321c91aa4e5816c2ad50d4742b4d96265
  | 2 => 0x4c28644483a3492aac104d1a56d1051960b786
  | 4 => 0x68b1468912320db34a59019218e59611f40350
  | 5 => 0x70c1870e1c3c71dc739e71e380861821bfd800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36681
namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x843f431087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720fd98641f830c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51082faa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f721843e843085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec82887d50510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2087dc8410fa108217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xe5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a17d94742bb28e857d51d0beaa3a15d54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa9283ef52506dea4a0df14941f6292836c525077c84a0ef10941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c6faa418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ef42087d88410fb8c821f6990437e51087ec8210fd50421fb98
  | 2 => 0x4b00017200000000000464800810871500008e82827034cfa80f4da5f8002343be5285880018219821a554b422c87246434930048ee000488879d50ea3681119a3128501d26b2927fc951c637e5fc001ce000000258853c66ec000004202951b9c91fc5d4a38003ac1084921b000000000001d8490000002728bc000000e81ccf28eb00000000000000000070e316c84ce818420e664000000000000000000057028a314c44d5038003a2000c387906e11c00095454000461690000000002f0004003113d0000a8f99aa052000bb0af1662dc1380033e0003f01e4d25ac0000034a45c68202000651069814ac74cb300017856c04253000220a5953370928df1922f42c09424e19085c0b0a12207780a8b20ee2b85a2582f01693403e4668043b1133869a8cda3c34e5bcfe8782c09ccc70fc05695d0317012076c4986b1ec540970d428a0013b800000614f800009400913a2c3ce4c4028000b85e42ea3f05a0844c000378000c40303f81c0d200000000c0017700067037800000000a010d148584001fb2467c46da30072000328000000002b8e14c61580d8c23047e8448004500000026613a0007800043e000080e40004c80a00038a37400216000878d81af0009144b8000004b5118001e619cb987d0008a4ee03117a07c31a151bc7989b0a63d20d871148092380d48e8390001321183d0000001f923632d30a4200000102a2e0006d0c98c63965102c1551f008c002044861780896c3b42507298f00093cbe1cf3b031d1b24b00046400247114788b182c38e53cff0cd1d22e1049c0482595248df32a7ac4b0ac4ec728ec800000550b70e63dc2ac7d130208338000d60003ec270000002ec6c012134948000070004ed2f1e12f6569079ac16a2f8d989b1a21a45d00049a0000c10836e5d0aea1c33c698851a30080805106c2e29d47a8450be0080300000038100300105022004180ec0000001014040240300002008060000d0240801c00020020740d014000100106c0e000040000004400030020000600007030010400f00037000000040d00000010030380c00003014000040500002030090180201400048060a40106c0300000024110000001003044040340100c00008000081a0580a0400300000000070180300004030170843e000080100a00005000060980f00002008000600900c03000010580301800004000140600000014000000401004008010000000c1301004014050040100018028110001104c01000080181100804038020600a01c0b0380500800018050000700404000010040a004020000c01c0bbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877
  | 3 => 0x21100029d379d21466280000024230c000000008e4000330000013a1f441035c41000000264d887a000964000000007b000000000000662710002e467a3b3300000019d000000648aa15a5a8a721d3409443e26c1aa0009f9b64803b4000dc000090fc0001e2494488004c005c1d84d0c0218b1000278750828001406b40001d3ee48062800000891221a10e200000000090000d9222000730c693400016ca300024e6d400000252000001900006f4001f62220008080623e96c3f9c20c80000590c2868f4000004705310705222c0648a83d2ae00085800188000001c4034000001960c2000751f2000950000003440f10610617e000408004241b4a68002065f40000000039c001ab45a4481a0ca0a84787b92f09e094af8832b01ed100000008288e248000000a905000000099a0b3746440011a4be504000fd13e000000681800008a1ef45600069000000000f216801a3650c8ff0aa2a4ab0412569b8b2000000774000f21386300008d32e001109090004f8f000c4066b9380132bc1c81f83811e1a91f1d73060707c93a3720c90c1ea0dc118009cd2b27b4170402a20d53398b0888944225c26e618b69a84ba49813000000200000001e859c2988e46a3bc2600013c899328004e4940c0000474028a11c10b2
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2530c23d6494c3097596430c2d96090c308fd91520c23c64548309dd85520c2746154830cbd91520c32c6454830d390d520c34d4354830d9d85520c3646154830da181520c25d658c830d354a320c34d520c830d354a310c29d640c430d3548310c2d9600c430a7593300c34d52cc03097d95300c34d524c0309ed95300c27661953209d58654c825e63153209758c54c823e6414f208f59053c82e8604cb208f99251c823d6494720f24cb30c82e9620c320f28c830c825e63952209758e548827661152209d584548823e64d4e208f593538827661d4e209d587538825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20d3588534834c538c9209b195324833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c51483663214520d94c8514835853c8120d9146204825e63d50209758f540825e63150209758c540827661150209d584540825d6594c20d6181530825e6314c209b988530834d5388420d354c210835953cc0209e594300834d53c80209bd95200834d5348020b9185200827b6548020b618d200825e63153109758c54c426e6294f109b58a53c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c425e6394b109758e52c42f06050710ec50740c42f16110310ec90440c425e63d52109758f548426e62d52109b58b548423e6494e108f592538426e6214e109b588538423f6454a108f191528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109ed81544423e6515110cd584544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910cd152414436452905109d19541443645250510ce153104436452841108f596540433860550108f990540427661150108f993530423d64d4c108f990530423d6414c109b988530426d6214c108f993520423d64d48108f990520423d64148109798c520425d6314810cd55321042756508410cd550210433954d00109e594400433554c40109e59610042776544010cd55110042e462440109ed9510042b86444010
  | 1 => 0xcb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d690c504cb594314132d68c8504ca7a60d50329e583540ca5e631503297d95320cad8604c8329bd95320ca9d6310b419798e529065d6394a4197d8d509065c6354241c714f43506b46150d41d3d4f525074c53d4941d9587525074f5314941d314c525071c5390941a758c425071c5310941cbd48425075b53d4141d614f505076b52d4141da14b505075b5314141d614c505076b5214141da148505073b4314141ce50c505073a4214141ce108505073a41141418fd9541106b860504419dd95411066e62d53319b58b54cc67a60d53319e58354cc66e62153319b58854cc63f6454b318f19152cc72f6454b31cb19152cc7676154b319e980548c6796015231a7191328c6d8604ca31b358b318c63f64542318f191508c65f63551319bd89544c66c62551319ed81544c67860551318f596540c71c63550318f990540c71d54d0c3197594430c71d54cc831a7191320c71d544c831b5d85320c6d8604c831b358b310c65f654c4319dd95310c65e63d53219758f54c867a60d53219e58354c865e63153219758c54c87576154f21b518d41c86f06050721ad59031c8755530c721cbd89548863e64d4e218f593538867a60d4e219e583538863e6414e218f590538872d5410a21b358c42886ac644ca21ba18132886cd63c8621cd5532188675619512197d8d544865c63551219bd89544867b60551219e181544866d6294d218fd91534863c6454d219dd85534867b6054d219e181534865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530865e63948219758e52086e561d08219b59442086cd63108219b59632086ac644c821b9d8532086e8604c8218f992510863d64944219d59641086d46350421b9d8941087a44250421bc18141086e562cc4219d59431086b5640c421f14c831086cd63c8421ad592210866f65484219dd95210863f64540218f191500865f63540219718d500871d53d0740c754d41d02b860507409dd8552902746154a40a758c429029d63d02409798c525025d63149408f99741502b86050540ae583431029d6310840ae580421025f63544409718d511026f62544409b18951103576354440d518d51103374354440cd50d51103676254440d918951103364254440cd109511037060544408f59641103355190440cd544411029d63d0040cd547401023f6550040cd545401027b6550040c755332cc31d544cb30b618132cc27661152309d584548c26f62546309b189518c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c274615513097997324c2d8604c9308f990514c23d64145309b98b540c26d62d50309b988540c26d62150309d984540c27561150308f99
  | 2 => 0x1ce958003780061132001dcce004118004800007b56000aaa3280bd92e2c95aa4a00003840694c221d0000002d000e40f866af2b40007d1a2b030a5e1da5c2900025e44000b1924000003628a00000502d444800cc000a1000001685080054a44000869d8287186a67800c893600000000008e8003d000113546f800c9800aa22c3c19800302949168996c2408a001a40006e841c4c02aa000008698cc1800001d40008ee4800ac82e96130002ac0000096b16000d6b7a28b0a9e638dc7c000c423600000818000038c6e2f828000108e69c2d25f35a4380032800c3344682120000051a0cad000003b000084001b2af040001961f27cabaea0e0605803ec691c8d27e90922cd0000f2ee9a97236a04a88005a8006c00000092b991872098002667d8000000079b6600000b580060800e2000000ce09b7e6b8006a9b40529600000000000019c5da2205800e88005115600370143201b0d2001880022a003940b3780011ada8000018aac32c2dab619ab8d20003236c6d9ca000968b8c2cd8b8002186f0000000000000cab64000004200065332000becf0d4002142510ad62306b0f27e854c627409000a71de7bb4e00000952dcc52ece08004100000000e780000352000007a2f00026857396168342b13ab3b0400000002c4e1b6838a38b60567816e5fba6ea89ad3080a51261c1e47f8c41cb62020f65d14e981e2afa50d01142c20a7c8120db74c7962121ea040a803000000000000013138d2ae417accc2106bd2a4ae928600ba3f07e062645539ad08feeb9ba929c0ca24c000003a030000007f1d81ea867e1ccb6a080000000000000009e878d837c971660033a000c6000000a8005e800000a4e60680cac8a20e0008060080101006000000380b03401014070000d0000a02c00000000501901c0200000000000001700000000000280600403010050080d01c01054000340a0040500c010080a0080100407004040400008c02000000000c0700102003000000040d004010000102c060000600000008010040500000004030080008c020280100406000040040000406014040080200000004000040801401004010180207003000010080100c14024020140b020000080500c0b0140000003034010000a004020140101c050026f62547439b18951d0e776154a439d1855290e3f6550c4397d954310e5f63547429718d51d0b576354742d518d51d0ab561d0a4297d8d5090a5c6354242c754e4310ab561d08428fd954210a6f65508429d98454cca7561153328f992518ca3d64946328fd91508ca3c64542328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132c758c544cb1c5490d3297195434cacc6250d32cdd53514cb3454d4532cdd50514cb345414532ced53504
  | 3 => 0x8c0009c6438e0012a000223ea6e0033e00262d780000224b2b50000005780000000d1800ea000000eeb8800648003a80016000279a8478002992cde8e40000000000000002b8000031c003a4a095800000e2964000000026c00000003240005287aa661864b8000002402f21c341d60800e30100e7000d7298ba272000cc07000a6a4600376003808f800289a612b72521d2002484f03a000000005c8800000232002fa9e2a0c39341d20eeb28e000001d80002800000000000000000cb800002febf23c0013e001ec189500020240a4e001c23b10ce836e2094ac48000000013a1600
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xb3960001400001c05584000dc34a1884db49445a5c964f0423040002601010e013521c94314132a60e2a18a0a0d1973108505060e3b2a89906386550604c831b0ae62128210e84631094108750210c0a0843611d1320c421d0ac89906210dc0704c8310870ca98c0a0e814c5c34354440c88c6312a220515731095110298b8084a8881981886054440c2ac6a8e80206195418132cc2a4b8486a9061891906154830cc0c2302a41860d64548310c324a92c0188618359152cc030992ed1906190645531852008258bb48220621895506244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x20080a8183108605042188487591320c421c81641c1320c421
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s4K5 (19164+((h/210+packedAt s4K5 (17064+(h % 210)*10) 10) % 834)*11) 11
  | 4 => packedAt s4K4 (19544+((h/157+packedAt s4K4 (17974+(h % 157)*10) 10) % 686)*10) 10
  | 3 => packedAt s4K3 (1475+((h/9+packedAt s4K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s4K2 (183+((h/1+packedAt s4K2 (180+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffc07ffe03ffff03fffffe07ff81ffcff1e3f
  | 1 => 0x1fff80fffffffffc0fc07ff81ffffff31e3ff
  | 2 => 0x1ffffffffc07fffff0007ffffffe07fc1ffc7
  | 3 => 0xfe00000fffff80fffffff80001ffff83fe03f8
  | 5 => 0xfffffff0000000fffffffffffe000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc2530a2238912300b2ca9642a590ce4570e1b
  | 1 => 0x5488526644922462c05582aca0aa39493160ed
  | 2 => 0xa930a14889074895550224d14d354432c0b746
  | 3 => 0x31a2c58d12240ed9a69b301849c79623ea03b0
  | 5 => 0xc1c3060e1c3870ee38e3c71e70061843bdd800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeae0eae0c880c880eae0eae0c880c880eae0eae0c880c880eae0eae0c880c880eae0eae0c880c880eae0eae0c880c880eae0eae0c880c880eae0eae0c880c880, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36681
namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x3648000001c21732b011a20a4c134094a94482ce8044151861c98f0a00a8e275630011020cf801eb4b0d002140012010800050920441801812c3047ff43fe43fd43fc43ff42fe42ee42fd42ed42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe86074000120b0d80001541d84000064000000013800840150000000e50530fc6940710c44003400b810bd240cd4ed00503054c14c411d355d10f8587c006c393c14ccad15817c24004c0000000000000049291800008000d1880000016800f0f48c000000002c000000a45c009800000029481889700178000000000001092c3c0975456000009c90780000e158c4a801656cc8a004000000dcb4942000040210422218081c0008020004021e02000006000208000406161800501a00056e52d0edaa5a1dd94743baa8e876e5210edaa421db55242b728c85af5450ad8a2a15b94842bba8a6574514cabca7a0d754f41b7296836d52d075a85a0d7d4d41ae29a836f52506d8a4a0eb50941bda82837850506dca420db54841b7296636d52cc79c8518f350a31af28c636f524c6d8a498f390831e6a10635e510c7aca218f590431eaa08635e53c86baa790f50c721b7aa4436d54886dca310f38c621e618c435f53486b8a690cf950219eaa043d431086dea810eb95021b6aa043ad540865aa810db94421f328843e7310879c6210f30c421f218843c431086dca5a05b54b40d6a14815e53102baa6205b94840b6a9081ad42102eca2205d544409faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c82bca6105754c20af29c215d53842dca5085b54a10ea18c213f5444278a88857d4d10ae29a216f52442d8a488750c410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x30048614028020034445304e0872cf4090d400050400187294214141b1185420c6c46250431e1509410c6d06050431c5550310862d6595021c9553310870d548c421b1986310870d540c421c95503108747540c421e19503108745540c421e15503108705540c421c950951102546154c208b5925284346520c610
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x200868142181410c682baca818843415d2520c610
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 157)*8) 8
  | 3 => packedAt s5K3 (833+((h/7+packedAt s5K3 (798+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffffffe03fff81ff83fffffffe07fcc7fe3f
  | 1 => 0x1f80fe07fffffffe0ffc1f03c07fffff3933ff
  | 2 => 0x1fff0007ffc0fffff0001ffc007ff87fc1c3c7
  | 3 => 0xe0000007ffff03ffffffe000007fff83fe03f8
  | 4 => 0xfffffff8000003ffffffffffff800003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc48a1440238208803180a314471644a442561b
  | 1 => 0x4126288a4494511606a40d42892a89491930ed
  | 2 => 0x96144dd6890ea3aad06296da124dd473c1c346
  | 3 => 0x1458b16512283acd6b4ac09024716622ee03b0
  | 4 => 0x1860c1861c30c3718c7318e338018043b5a800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880eeaac880, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36681
namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5007fe5401ff55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe4301ff50c05fc43027fd4803fe52007f54803fc5201ffd0803fe4201ff50803fc42017fcc803fe32007f4c803fc32027fd4401fe51007f54409fc5101ffd0407fe4101ff50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0007fe4001ff50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842005ff0c210087fe4108017fe2084001fe9042005ff08210007fe2108003f71084001fd8842000ffd9510005feca880037f65440013fb2a200fff99510025fcca88003fd65440017eb2a200fff19510025f8ca880037c65440093e32a200effd9110075fec888003bf64440015fb22200eff9911001dfcc88803bfd644401d7eb22200eff1911001df8c88803bbc64440075e322200effd5110077fca88803bfd544401dfe2a22000ffd8d10005fec688003df63440016fb1a200dff98d10015fcc688003fd63440017eb1a200dff18d10015f8c688003dc63440056e31a200fffd4d1006ffca688003fd534401bfe29a200effd0d1006ffc868803bfd434401bfe21a2000ffd8910005fec488003ef624400177b12200cff9891000dfcc488003fd62440017eb12200cff1891000df8c488003ec624400376312200fffd4910067fca488003fd5244019fe292200effd0910067fc848803bfd4244019fe212200dffcc910067fc6488003fd3244019fe192200fffd4510007fca288003f65144001fea8a2000fd5451007ff8a28803bff414401dff20a200efd90510077fa828803bf5414401dfe20a200dffcc510007fc6288003fd314401bfe18a200cffc8510007fc4288003fd2144019fe10a200fffd4110007fca088003fd504401ffe282200effd0110077fc808803bfd404401dfe202200dffcc110007fc6088003fd304401bfe182200cffc8110007fc4088003fd2044019fe1022000ffc4110007f62088003fe1044001fb0822005ffd9410005feca08027fe65040097f3282000df99410024fcca08003fd65040017eb282000df59410004faca08017fc65040097e3282005ffd9010045fec808023fe64040077f3202008ff59010045fac808017fc64040077e3202008ffd5010047fca808023fd5404011fe2a02005ffd8c10005fec60801ffe63040057f3182000ff58c10005fac608017fc63040057e3182009ffd4c1003ffca608003fd530400ffe2982008ffd0c1003ffc8608023fd430400ffe2182005ffd8810005fec40801bfe62040037f3102000ff58810005fac408017fc62040037e3102009ffd4810037fca408003fd520400dfe2902008ffd0810037fc8408023fd420400dfe2102007ffcc810037fc6408003fd320400dfe190200bbf9841004ffea208003fe5104001fea882009ff14410047fe8208023fe4104011fea082008ff1041003ffe6208003fe3104001fe9882007ff0c410037fe4208003fe2104001fe9082006ff08410055fcc008027ff500400bff2802000ff5401002ff8a008023ff400400bff2002008ff5001002ff8800801fff300400bff1802000ff4c01002ff8600801bff200400bff1002000ff4801002ff84008003ff1004001fb8802005ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x7fd3248001f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148031ffa8a4000ff94520007faa290063fc514802fffa0a4017ff905200bffa829005ffc414802dff98a4000ff8c520007fa629005bfc3148003ff90a4001ff8852000ffa4290007fc21480037fb024018ffd4120007fca090003fd5048031fe2824017ffd01200bffc809005ffd404802ffe2024016ffcc120007fc6090003fd304802dfe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048001ffb2e2000bfd97100affccb88012fe65c4001feb2e2000bf597100aff8cb88012fc65c4017ffb26200bbfd931005ffcc98800efe64c4017feb26200bbf5931005ff8c98800efc64c4017ffaa6200bff9531005ffaa98802ffc54c4001ffb1e2000bfd8f100a7fcc78800afe63c4001feb1e2000bf58f100a7f8c78800afc63c402bffa9e2014ff94f10007faa788053fc53c4017ffa1e2014ff90f1005ffa8788053fc43c4001ffb162000bfd8b1009ffcc588006fe62c4001feb162000bf58b1009ff8c588006fc62c402bffa962013ff94b10007faa58804ffc52c4017ffa162013ff90b1005ffa858804ffc42c4029ff9962013ff8cb10007fa658804ffc32c402bffa8e2000ff94710007eca388003fd51c4001faa8e2015ff1471005ffe838802ffe41c4017fb20e200bff5071005fea838802ffc41c4029ff98e2000ff8c710007fa6388053fc31c4027ff90e2000ff88710007fa438804ffc21c402bffa862000ff94310007faa188057fc50c4017ffa06200bff9031005ffa818802ffc40c4029ff9862000ff8c310007fa6188053fc30c4027ff9062000ff88310007fa418804ffc20c400bffb2c2000bfd9610097fccb08012fe6584001feb2c2000bf5961002ff8cb08012fc658400bffb24200abfd9210057fcc90800efe6484015feb24200abf5921002ff8c90800efc6484015ffaa4200aff95210057faa90802bfc548400bffb1c2000bfd8e1008ffcc70800afe6384001feb1c2000bf58e1002ff8c70800afc6384025ffa9c2011ff94e10007faa708047fc5384015ffa1c2011ff90e10057fa8708047fc438400bffb142000bfd8a10087fcc508006fe6284001feb142000bf58a1002ff8c508006fc6284025ffa942010ff94a10007faa508043fc5284015ffa142010ff90a10057fa8508043fc4284023ff9942010ff8ca10007fa6508043fc328401d7eb0c2012ffd4610007fca308003fd5184025fe28c200affd0610057fc830802bfd4184015fe20c2011ffcc610007fc6308003fd3184023fe18c2010ffc8610007fc4308003fd2184021fe10c2008bf98210097fea108017fe5084001fea842005ff14210057fe8108017fe4084015fea042005ff1021008ffe6108017fe3084001fe9
  | 2 => 0x300effea898077fe544c03bfeaa2601dff15130015fec69800bff534c005ff29a6002ff54d30017f8a69800bff434c005ff21a6002f790d30017fa8698077dd434c005fe21a6000ffd8930005fec498073fe624c0037f3126000ff589300e7f8c498006fc624c03dffa92601cff94930007faa498073fc524c03bffa12601cff909300effa8498073fc424c005ff9926002f7cc930017fc649800bfd324c001ee9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c03dffa8a6000ff94530007faa29807bfc514c03bffa0a601dff905300effa8298077fc414c005ff98a6002ff8c530017fa629800bfc314c039ff90a6000ff88530007fa4298073fc214c0057fb02601effd4130007fca098003fd504c03dfe282601dffd01300effc8098077fd404c03bfe2026002ffcc130017f6609800bfe304c001ef1826002ff0c130017b8609800bf8304c039ff902601cff0813002ffecb10002ff6588037ff32c4004bf99620007facb10002fd658800bfe32c4004bf1962002ffec91006aff6488035ff3244003bf992200d7fac91006afd648800bfe3244003bf192200d7fea91006bfe5488035feaa4401aff1522002ffec710002ff6388033ff31c4002bf98e20007fac710002fd638800bfe31c4002bf18e200dffea710067fe5388001fea9c4019ff14e200d7fe8710067fe4388035fea1c4019ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510017ff6188001ff30c4000bf98620007fac310002fd618800bfe30c401bffd4620007fca310003fd5188037fe28c401affd06200d7fc831006bfd4188035fe20c4019ffcc620007fc6310003fd3188033fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310006fe6088037ffa844005ff94220007faa110017fc5088035ffa044005ff902200d7fa8110017fc4088033ff9844005ff8c220007fa6110017fc3088003ff9044001fbc822000ff64110017fc2088003fc1044000ffd9520005feca900037f65480013fb2a4018ff99520025fcca90003fd65480017eb2a4018ff19520025f8ca900037c65480093e32a4017ffd91200bdfec89005ffe64480077f3224017ff591200bdfac89005ffc64480077e3224017ffd51200bffca89005ffd544802ffe2a24000ffd8d20005fec69005bfe63480057f31a4000ff58d20005fac69005bfc63480057e31a4018ffd4d200b7fca690003fd534802dfe29a4017ffd0d200b7fc869005ffd434802dfe21a4001bfd892000ffea490007fe5248003fea924001ff1492000ffe8490007fe4248003f72124001ff509200bfda8490007fc4248003ff9924001ff8c92000fdc649000
  | 3 => 0xf20ca027ff5065013ff8832809bff3194001ff18ca000ff4c650137f86328097ff2194001ff10ca000ff4865012ff84328012fe6094009ffa84a004dfd4250027f6a128017fc5094009fc284a027ffd025002ffc812809ffd409400bfe204a026ffcc25002ff86128097ff209400bfe104a004bfd9550127fec8a8092ff6454049ff322a003bf99150127fac8a8092fd6454049fe322a003bf19150027fea8a80137f5454009ff2a2a004ff55150126faa8a8013fc5454001ffb1aa000bfd8d5011ffcc6a800afe6354001feb1aa023ff18d50015f8c6a8013ff5354009ff29aa004ff54d50027f8a6a8093ff4354047ff21aa024ff50d5011ff886a8003ff62540017fb12a022ff9895000dfcc4a8003fd6254045fe312a001bf18950027fea4a8013fe5254009fea92a004ff14950127fe84a808bfe4254049fea12a022ff1095011ffe64a808bfe3254001fe992a022ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8002fc6154009ffa8aa004dfd4550027fca2a8013fd5154001bea8aa004ff14550127fe82a8093fe4154049fea0aa024ff1055011ffe62a8003fe3154001fe98aa023ff0c550117fe42a8003fe2154001fe90aa022ff08550025fec0a8013ff5054009fda82a004ff94150006fca0a8013fc5054009be282a004fe14150127fe80a8093fe4054049fea02a024ff1015011ffe60a808ffc3054045ff902a022ff0815002ffecb18002ff658c043ff32c6004bf99630007facb18002fd658c00bfe32c6004bf1963002ffec918082ff648c041ff3246003bf99230107fac918082fd648c00bfe3246003bf19230107fea918083fe548c041feaa46020ff15230015fac71800bff538c005ff29c6002ff54e30017f8a71800bff438c005ff21c6002ff50e30017f88718017ff628c03fff3146001bf98a30007fac518002fd628c00bfe3146001bf18a3010ffea51807ffe528c001fea94601fff14a30107fe851807ffe428c041fea14601fff10a30017fe651800bfe328c005fe9946002ff0ca3002ffec318003fe618c0017f30c6000ff58630005fac318017fc618c043ffa8c6000ff94630007faa318087fc518c041ffa0c6020ff90630107fa8318083fc418c005ff98c6002ff8c630007bc631800bfd318c005fe18c6002f70c6300fffe4318003fe218c001fe90c601fff08630015fcc118087ff508c00bff2846000ff5423002ff8a118083ff408c00bff2046020ff5023002ff8811800bff308c005ef9846002fecc23002ff8611800bf8308c03fff9046005ff08230007feca98002ff654c03dff32a6004bf99530007faca98002fd654c03dfe32a6004bf195300effec898076ff644c001dfb226000afd91300effcc89800efe644c03bfeb22601dbf591300eff8c89800efc644c03bde3226003af191
  | 4 => 0x8b3fd5488459fe2a44200ffd8e21005fec7108affe63884057f31c4200ff58e21005fac7108affc63884057e31c422dffd4e2115ffca710803fd5388457fe29c422cffd0e2115ffc87108b3fd4388457fe21c4201bf58a2100ffea5108b7ef5288403ff2944201ff54a2100ff8a510807ec5288403ffa144201ff90a2100fdc8510807fd4288459f6a144201ff10a2100ffe6510807fe3288403f71944201ff4ca21007da6510807fc32884037f30c422dffd4621007fca310803fd518845bfe28c422cffd0621167fc83108b3fd4188459fe20c422bffcc621007fc6310803fd3188457fe18c4201ffc862100fde4310807f72188403fe10c4201fd08621007fec110803fe60884017f3044200ff58221005fac110803fc608845bffa84422dff14221167fe81108b3fe4088459fea04422cff1022115ffe61108affc3088403ff9044201ff0822100fd84110803ff65484017fb2a422aff99521025fcca90803fd65484017eb2a422aff19521025f8ca908a7ff64484537fb224229ff9912101dfcc8908a7fd64484537eb224229ff1912101df8c8908a7ff5448453ff2a24229ff5512114ff8a890803ff63484017fb1a4228ff98d21015fcc690803fd63484017eb1a4228ff18d21015f8c6908abff5348451ff29a4200ff54d21147f8a6908a7ff4348451ff21a4229ff50d21147f88690806ff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201ff9092100ffa8490807fc4248403ff9924201ff8c92100ffa6490807fc32484037fb0a422affd4521007fca290803fd5148455fe28a4229ffd052114ffc82908a7fd4148453fe20a4228ffcc521007fc6290803fd3148451fe18a4201ffc852100fee4290807fe2148401f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024200bf18121157fea0908abfc5048453ffa024229ff9012114ffa80908a7fc4048451ff9824228ff0c12100ffe4090807fc20484097eb2ca005ffd925013dfec92809ffe64940077f324a027ff5925013dfac928017fc64940077e324a004ffd5250027fca928013fd5494009fe2a4a005ffd8e50137fcc72800afe6394001feb1ca000bf58e5002ff8c72800afc6394009ffa9ca004dfd4e50027fca728013fd5394001bea9ca004ff14e5013ffe872809bfe439404ffea1ca026ff10e5002ffec528097fe62940037f314a000ff58a50005fac528017fc62940037e314a004ffd4a50027fca5280977e5294009fea94a004ff14a50026f8a52809fff429404bff214a027ff50a5012ff8852809bff329404bff194a000ff4ca5012ff86528017ff6194001ff30ca000bf98650007fac328002fd619400bfe30ca004ffd4650027fca3280037e5194009fea8ca004ff14650026f8a32809fff419404ff
  | 5 => 0x4551027fca2a88037e5154409fe28aa204df14551027e8a2a88dbff415446dff20aa236ff505511b7f882a88d7ff315446bfe18aa234ffc85511a7f842a8803ff60544017fb02a200ff98151007fac0a8803fc60544017e302a204ffd4151026fea0a8813fc505446dffa02a236ff901511b7fa80a88dbfc405446bff982a235ff0c1511a7fe40a88d3fc2054401ffb2c6200bfd963119ffccb18812fe658c401feb2c6200bf5963119ff8cb18812fc658c465ffb246232bfd9231197fcc91880efe648c465feb246232bf59231197f8c91880efc648c465ffaa46232ff95231197faa9188cbfc548c4057eb1c6202ffd4e3119fbea71880bfe538c405fea9c6202ff14e31017b8a71880bff438c405ff21c6202f790e31017fa87188cbdd438c405fe21c6200ffd8a3118ffcc518806fe628c401feb146200bf58a3118ff8c518806fc628c467ffa946231ff94a31007faa5188c7fc528c465ffa146231ff90a31197fa85188c7fc428c405ff9946202f7cca31017fc651880bfd328c401ee9946202ff0ca31015fcc3188cfff518c401ff28c6200ff5463119ff8a3188cbff418c465ff20c6232ff50631197f8831880bff318c405ef98c6202fdcc631017f8631880bf4318c463ff90c6231ff08631007fec118803fe608c4017f3046200ff58231005fac118803fc608c467ffa846233ff14231197fe81188cbfe408c465fea046232ff10231017fe611880bfc308c405ee1846231ffc823118ff84118803ff654c4017fb2a6230ff99531025fcca98803fd654c4017eb2a6230ff19531025f8ca988bfff644c45f7fb22622fff9913101dfcc8988bffd644c45f7eb22622fff1913101df8c8988bfff544c45fff2a2622fff5513117ff8a89880aff634c405ffa9a6202ff94d31017faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c401ffb126200bfd8931177fcc498806fe624c401feb12622eff1893100df8c4988c3ff524c45dff2926200ff54931177f8a4988bfff424c45dff212622fff50931177f8849880bff324c405ff1926202ff4c931017f8649880aff614c461ffa8a6200ff94531007faa2988c3fc514c45fffa0a622fff9053117ffa82988bffc414c405ff98a6202fdcc531017fc6298803de314c405fe18a6202f70c531017e862988bbff214c45dfe10a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c0988c3ff504c461fe282622fffd013117ffc80988bffd404c45ffe2026202ffcc131017f860988bbff204c45dfe1026200ffd9621005fecb108b7fe65884097f32c4200df99621024fccb10803fd65884017eb2c4200df59621004facb108b7fc65884097e32c422cffd9221165fec9108b3fe64884077f324422cff59221165fac9108b3fc64884077e324422cffd5221167fca910
  | 6 => 0x5ff3226403bf991321d7fac8990eafd644c875fe3226403bf191321d7fea8990ebfe544c875feaa2643aff1513200dfec69900bff534c805ff29a6402f794d32017faa699003dd534c805fe29a6402ffd0d32017fc869900bfd434c805fe21a6401bfd893200ffea499007fe524c803fea926401ff1493200ffe8499007fe424c803f72126401ff509321d7da8499007fc424c803ff9926402fbcc93200ffc6499007de324c803fe1926401f70c93200fd86499003ff614c8017fb0a6400fdd8532005eec299003fe614c801feb0a6400ff18532005f8c299003f4614c8017a30a643bffd45321dff8a2990ebff414c875ff20a643aff505321d7f8829900bff314c805fe18a6402f70c53200ffe4299007fc214c803f610a6400ffd8132005fec099003fe604c801feb026400ff18132005f8c0990efff504c877fe282643affd01321d7fc80990ebfd404c875fe2026402ffcc132017be609900bfc304c803ff9026401fbc813200ff84099012fd6594473ffb24a239bfd92511cffcc92880efe6494473feb24a239bf592511cff8c92880efc6494409ffaa4a204dfd5251027fca928813fd5494473beaa4a204ff15251007fec7288e3fe63944057f31ca200ff58e51005fac7288e3fc63944057e31ca204ffd4e51027fca728813fd5394409fe29ca239ffd0e511c7fc87288e7fd4394471fe21ca200ffd8a511bffcc528806fe6294401feb14a200bf58a511bff8c528806fc6294409ffa94a204ff94a51027faa528813fc5294473ffa14a237ff90a511cffa85288dffc4294471ff994a237ff8ca51007fa65288dffc32944097f30ca204ffd4651026fea328813f75194409bba8ca204ff14651027e8a3288e7ff4194473ff20ca239ff506511cff883288e3ff3194471fe18ca237ffc86511bff84328803ff6094401ff304a200bf98251007fac128802fd6094401fe304a204ffd4251027f8a1288137c5094473ffa04a239ff902511cffa81288e7fc4094471ff984a238ff0c2511bffe41288dffc20944097fb2aa236ffd91511b5fec8a88dbfe64544077f322a236ff591511b5fac8a88dbfc64544077e322a204ffd5151027fca8a8813fd5454409fe2a2a200ffd8d51005fec6a8803df63544016fb1aa235ff98d51015fcc6a8803fd635446bfe31aa202bf18d51007b8c6a880adc6354409ffa9aa204dfd4d51027fca6a8813fd5354401bea9aa204ff14d511b7fe86a88d7fe435446dfea1aa235ff10d51007fec4a8802ff6254401f7b12a200bbd89511a7fcc4a8806fe6254401feb12a234ff1895100df8c4a8803ec625440376312a204ffd4951027fca4a88d37e5254409fea92a204ff14951026f8a4a88dbff4254469ff212a236ff509511a7f884a88d7ff3254469ff192a200ff4c9511a7f864a8812ff6154409ffa8aa204fdd
  | 7 => 0x400402400c01404000401000400001400000403c00400000001802800800c03803402806c02c0100100f805c00c00801c00000c00004401c05c00001401002c00002003400004001c00003804800c00001003c0000600080180100000740b000801000803c05800000c0500000000040000b001400400c00003c0000000dc02001c00801801400809401000400006c01c00403400404800401c02400000001402807401001801000032001000400c0000000100300100280000a800403401800402c01c00401400001400402000805400400000000802801001000008408c0000b40000080000000580080000000700000180000b0010057fb2aa63fffd91531fdfec8a98fffe6454c077f322a63fff591531fdfac8a98fffc6454c077e322a604ffd5153026fea8a9813fe5454c09feaa2a63fdf55153027f8a8a980aff6354c05ffa9aa604f7d4d53017fca6a980b7e5354c05fe29aa602df14d53017b8a6a980bff4354c05ff21aa602ff50d53017f886a9803ff6254c017fb12a63eff9895300dfcc4a9803fd6254c7dfe312a601bf18953027fea4a9813fe5254c09fe292a63fffd09531f7fc84a98fffd4254c7dfe212a602ffcc953017be64a980bfe3254c05fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff18553005f8c2a9813ff5154c09bfa8aa604ff145531fffe82a98fffe4154c7ffea0aa63fff10553017fe62a980bfc3154c7dff90aa63eff08553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9802fc6054c09ffa82a604ff14153026f8a0a98ffff4054c7fff202a63fff501531fff880a980bff3054c05fe182a63effc81531f7f840a9806ff655487bffb22a43dbfd91521effcc8a900efe645487bfeb22a43dbf591521eff8c8a900efc6454809ffaa2a404ff95152027faa8a9013fc5454801ffb1aa400bfd8d521e7fcc6a900afe6354801feb1aa43cff18d52015f8c6a9013ff5354809ff29aa404ff54d52027f8a6a90f7ff4354879ff21aa43dff50d521e7f886a9006ff6254803ffa92a404fbd495200ffca4a90077e5254803fe292a401df1495200fd8a4a9007ff4254803ff212a401ff5095200ff884a9007ff3254803ff192a401ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9002fc6154809ffa8aa404ff145521effe82a90f7fe415487bfea0aa43dff105521e7fe62a90f3fc3154803ff90aa401ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9002fc6054809ffa82a404ff141521effe80a90f7fe405487bfea02a43dff101521e7fe60a90f3fc3054803ff902a401ff08152007feca99002ff654c801bfb2a64009fd95321dffcca99012fe654c801feb2a6400bf595321dff8ca99012fc654c801be32a64049f195321d7fec8990eaff644c87
  | 8 => 0x140002d9a3986f1aa80000024800001aae527c830222a17a7dacb215b289a528c8c79cd0002a780029c8002c91b729b2e90000072e80b30cb9dc8000002141c1803b40a4e9209f9b028000000001db078197a74000101ac0a3ba131a124e00110e03d3351d09b0b2990a28c04c1cc33399927c185aaa10c1af0d4af50550000001bc2e100026b26c9850000eb000000000304b180f123086bb1900000000013b3109548b222db0d13694f00000000000030a26a307a33a962c582d00c9d5ab889991c01a29a91b9b69f2afd02123d17204bab73162501f63499c630f10a9d82b21970000b4b128c11c3912245a9dadb0549a434200000000004594a07fa0382c32d9ecb5232185c2278000ba3139b78000431a9b490000003059110328e8a4f019a528e02368643231a69f21ac20a041a7505996700023516a8001240002591669b8800020a269912cc1f580004d85913fb0000011aad30130001eba4300000000017b0002cc93eb1d8003530003262eb110b50a548118000d080000010b9ea17800021111581088b34a21ba62249aa99e91b02a310f1731938a8800001802007c00002002000002002803800006400800400800000800000001000400411802400000c00000003800001403401000800000001400c0000140040100480501300140140000480a002801401001c00005000406000400400001c01406000800c03403c00000400400800c00c0001f000000001000405404401c00400c02402408c00c00000404000400000000400407c00001805800400400000002c01001803800000c00800404000800c03000000400001803000406800008c07801402400007400002001000403401002c00c0000040000f801001000c0100280040100000000080000540a800400400000801003c05c00001005406801400000000000c08800804400006401800000401c0c401000801400001803401800c00000000c01001000002405002c01c00800800403404c03001000000811000800c07800802004401401006800800000002400000000400400400800005c00405000c00000004c01c01400c00005004000001010400c00000007c01000c00400800800000808403400001800004800c01800003c0200000000200080000080040280540340440280a400404401000001006800802c02400000400800001000800c0100140000a800000401403004003800800404002c00800401c0000000000c003c00c09000000000802402c0dc00004000000401c12400001800805c03800000400000801411401800008800000c04802c00401005c00c02401400c00802405400800c00000802801408c0b401800000000803000000006000800000404800009400000009002400c01007008400000002815804400006c02409005c00c00c07401800001
  | 9 => 0x71e425092a33609a80c000036a8f8002489261c5b3aa380370a999e0c896088f00000b00021233c28132c90b11a1df9a922f9bc8a82c18271519c8804b2b0ec8a20be1e4902a379fc1621880a5a1f02b33891305333b8000000002fc000000000264805a86b549dc0af0819461169940c3ac280000000000014e2b98001908060ad12f880a8d0000002693348000000e28002871691409590c481f0a30003569e59442468e18ec1563501cf9481399f42bf912800137800288ab0037a551870002a5abc00035926718c9e08000a42d919f21b11634e2981808f8b3290980023b0000002e89400002b8088a438002ee35800007e9b11363018801a39081ba97f071abe8401070000002df30808d0ce1299478e60068342cd16f8651680de8e115e89c9b99a600000023412309900005688e0240710001b5a4022e2719ca097134b022b61762e731c2d11e821725e82a152b442f000030b17c0cd93380fa520920000000942850002310001da9d41b48002d59381cea281ff8000003312318000002fa96f07e00000033d88d9d719332f80024128d9d5090b1a80310030c9759580de2102f98002270a19c135aa2181b0b08490002792fe1c71660003433379afa208618b7869ac3aa21860ee0bc08ea4212d96486087b1a7a780861fa2ac2242080ff0dfa149ef96384e9531bd1d1a3732d2068000000001602c10d7892a66a758978948001cc81704ca7a8002f69618728b03358001f7a6e2830b732123c9050c28002f93342e4000000000225000ad792cb472298cf2542392bb21a05ea5d00027e0aa2600001c9b11278833a6888a21d97d97e9d2a5e2e3981000189ae78a7a1695cabe2358bf8a6086b4b06b225851aaf15885a2c48e7a802f59d126b83e0c6ac995da109188539b3846977a5633b11e311a5c82a84e1319d6a33313211a640b9303a040e4085125b2b9ad9abb270da2a289827324f9b9056078942038a5831f05295b87994300da712f7b20b088360452679e6207b0407099c01f8f7a558149f4b070000c0a2e8748d50d61ed2842d00438a001e89311f29a1f70cd33cb5882229894c8001f3b0bb4e9dd05d841344873807a0616131d17aa5783d9dba2d352ab295500508fab080020d04ab2eb578d12ad196b1e86e0f2848a8e99286d0c90d01e034d80009f0000120988003400ed1419ea9c417021fac0023085827adbb4a9d203ea5fa9eb0525a1fca40a23149b1b25d8188000ca9ef000300b1506ead180d3222c71f10f800003f8169e5343b5522a9a723a023a860000f09198000000879508938cb23da59af3ad4348a9d2b90a3829800346aab00e2d0a450001e68002b78f30e533d2ec86480001c0eaa8800000003800000000002e19aa3c0000002c4331aeb9e780f27a1f90001718b1034800199a1e8002748002e02e32b38
  | 10 => 0x2631b800000011e99d94a8fb88206020b29c1a5ad880011f80000012800021e1fe1631149640e68250288e32e208900017e00032280031407b9d307a0c70b817d2df80027f1ae33980031f81d21c8000d68d80000000440000bca389988c01cb8002b48510668002f215e04714598184607931700000000000000015d0001bf2030630000d580000006580027382f0318001558958000580fc0dc978a300000001b28000a70019ed8f41c0a0e0a52f29b51b427289da1c2fb8d9157a222199e3815013af405cb41031026000209b4c0001ec00000000019e8000000000000000001292af9060000002ffb0e2ddb0f8002920a12a507300004b0002092a728180026529988c04a1740cf8000a0abd9fbaaa826a7217a27ea70a009271329aca7b09a0bd8722a609b2d6a048b998b9182fb28b2619960e99a0868800342ac781e35a353a89942afeaa380022a1250422ed04faee8efb061708002b59a3201a612190ceae589b984282019296ac621a8d999f9f1a878000001828183248b5aa4ad50002b19f08002ec00014c1100003280002ea19585410c9ff21500000000004829e04988c9902cf00034807703a23232c17105aaae29b8002d8162a761a8b2399a26f80026e9410eea0b9570d38003308e0a8093d98b00000029299d0398001c018c1f509625c1e31e20000090200161981139fab27aa189c00b9eeace817a6c1de9278000ea1f00002cb80000034f0000f68002e19c20002238f00000000003460001de1be347aca95031994fb370db28580880004780000025ba890a488400018d31880005e27728a8b400000014500010da0fb5733210416c800336a681190002ba9248001151fd8b1ae48570dd8001920001d49140000000968ef0448003392a1000183800265a7d1309d92d20282f3015a12ac88249179ee2138fd2ca18234b93a146a089ad2e6a44aba3450fa9fd22b83b0678b38002ff12881caae86c9089c6944a462262f605f9c52dd0f73561eb1ab012af8a0e94908492aa02aa02bd02ea83a291729c4a701c30ad92691d16520aa53a6aa6980a14b17b8621c90dbaa9055911a1d0da920260aef18a903a97a9fa4d9350613122001cdae619b90f8b2a5b154050a9915f830b2f22f207266174ac8025b0696a04d06a1a204f2d48628baada8c5104a21130121a4a13f2cd857800159a628219b213d17705f0001f680004299b156aa824d25aa7f9058c18408029e1973a9120f00025f0393599d893111b3518000000000003459b19f80002ef8bb24929514d9bb9e107c2849d00001a181da05ace00029418f9918b60f985233a1320a283c8002d607d8101790d88fca798000111e88000ab0eb83c0f91aa3148001e9ab50080dd0b530c15f19496e1dd98e85d0b89d6035b3e1c292280000009d33f16c22b0002d39fea4
  | 11 => 0x6ab3fb4d1ae9950fe8000002aca47aa433e8f1ac6a3e8761a280000003b8000ab80016d8d28670228aa9472248c413e0000002dc9f313c8e58fe263b090f48880290e907d06616eb15b1b92c1d7ad280014d0001c82588c5a4c90ea3f9a4ac3293abf12114ea9488a83a8dc0bb8870702de88b80aa8b9b625312b8c3355a0c2ad86d8cc8bd26d9f8b1798f01b984af82c22188e80ca29018e02da8e2918e48901cf032257123a3498a232a3607a91db240f5aa8a8280027b96b8000000000000000001750d700993b8afb0d9890f21df0002b115b30a83f1c796d1090ed82f88109113a8759bd8ae80000014b8003380001ce29f06907f2568002da168a8a12e8e224c1a80f50a68830d200015a90105000022c8ff92207c876aa08df0001359bb20c8003202971e700eb512f12f1a0d9cb1da18015118327680020100024b2a6abcae98d30ac9ba07799ca050b692d24bab3000117251afdb2a3010000f60000ae0d42f489e96b0002bb80000002c80028f10d2778001a009185b20207432a80031c979a2000000016780017fafcb2534189e0001372e286f948943969a4aa2c139083a5134f86c2e08000002958002ed9658000000c9833138ac500017c8cc0000000c800002b9069538002441d38002dc1078000001bf8001340fd8000002ab8fa15c2d723a8353543333032429333302930ac2fa0001be9fb3098000001888c2241b16b269e28bea1621823e00010231e13c002000000187af707512b2b68829b300018dab42909008001031d997680423f00032934c8a90001caaea91c8898d1b10000325ade0638bf12e0e380000012f00030eacf85b8e71521868c60000f3b2e09fa288fb2f080015a058a6f00006831a00026d095
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd745881001cfc7458810004ff7358810014fe7358810014fc735881002eef7258810036ee4258810006ed4258810036ee325881000cff715881000cfd7158810034fc7158810036ec215881000cff705881002cfe705881000cfd705881002cfc705881002eee205881002eec2058810004ff765481002cfe7654810004fd765481002cfc76548100267e65548100067d6554810004ff764c81002cfe764c810004fd764c81002cfc764c8100057f754c81004d7c754c8101de7e654c8100067d654c810016de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c8100acff769441002cfe7694410024fd769441002cfc76944100267e65944100067d65944100aef6619441004f77519441002dfa7094410005f970944100acff76544100267e65544100067d6554410005df735441003ddc7354410005ef7254410035ec72544100aef661544100a4ff768c41002cfe768c410014fd768c41002cfc768c41019e7e658c4100067d658c410016de638c410006dd638c41002dfa708c410005f9708c4100a4ff764c4101867e654c4100067d654c41003fd4314c41009cff768841002cfe768841000cfd768841002cfc768841004d7e75884100057d758841016e7e65884100067d658841000eee6288410006ed628841002dfa7088410005f9708841009cff76484101567e65484100067d6548410094ff76540100267e65540100067d655401008cff764c0100f67e654c0100067d654c010005bf744c010045bc744c010084ff76480100057f754801004d7c75480100c67e65480100067d65480100ae7e65c40100067d65c401009ef576c401002ef765c401002f7665c4010006f565c401002f7565c40100067565c401002ef764c4010226f564c401002df570c401002ef660c401002df9768401002ef9768401000cf9768401002f7a658401002f79658401021df97184010216fa618401002ff26184010004ff76440100057f754401004d7c754401007e7e65440100067d6544010005bf7444010045bc7444010005df734401003ddc7344010005ef7244010035ec724401002df77644010006f77644010004f7764401000777754401000774754401002ef7654401002f766544010006f5654401002f756544010006756544010007b7744401020fb4744401002ef7644401020ef56444010007d77344010007d47344010007e77244010007e4724401002df7704401002ef6604401002ff25044010007f15044010005fb7644010006fb7644010004fb76440100077b75440100077875440100077a6544010007796544010007bb744401020fb87444010007db7344010007d87344010007eb7244010007e8724401002dfb714401002ff37144010206fa6144010007f26144010007f25144010007f15144010
  | 1 => 0x94100067e54594100067d545941004e7c5459410004ff7359410014fe7359410014fc735941004e7f53594100067e535941004e7c5359410004ff725941000cfe725941000cfc725941004e7f52594100067e525941004e7c5259410024ff7159410024fd715941004cfc715941004e7c5159410024ff705941002cfe7059410024fd705941002cfc705941002e7e505941002e7c505941002d7f765941004e7f76594100247f765941002e7f64594100067e64594100067d645941002e7c645941002e7f63594100067e635941002e7c635941002e7f62594100067e625941002e7c62594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067c325941004e7f71594100067e71594100067c71594100067f41594100067e41594100067d41594100067c41594100067f31594100067c31594100067f21594100067c215941004e7f705941002e7e705941002e7c70594100067f405941002e7e40594100067d405941002e7c40594100067f305941002e7e305941002e7c30594100067f205941002e7e205941002e7c205941002e7e105941002e7c1059410024fe75d8c1002e7e75d8c100247e75d8c10004fd75d8c1002e7d75d8c100047d75d8c1002cfc75d8c1002cff74d8c1001cfe74d8c10004fd74d8c1002cfc74d8c1003cfd73d8c1000cfe72d8c10004fd72d8c1002cfc72d8c100a4fe71d8c1002ef671d8c1002cfe70d8c1002efa70d8c10014ff7658c100067e6558c100067d6558c1002edc6358c10004ff7558c10024fe7558c10024fc7558c10004ff7458c1001cfe7458c10004fd7458c1001cfc7458c1002edf7358c1003ede4358c10006dd4358c10004ff7258c1000cfe7258c1000cfc7258c1003edf3258c10014ff7158c10014fd7158c1003cfc7158c1003edc3158c10014ff7058c1002cfe7058c10014fd7058c1002cfc7058c1002ede3058c1002edc3058c10004ff7654c1002cfe7654c10004fd7654c1002cfc7654c100267e6554c100067d6554c10005f77154c10005f47154c10024fe75d881002e7e75d88100247e75d8810004fd75d881002e7d75d88100047d75d881002cfc75d881002cff74d881001cfe74d8810004fd74d881002cfc74d8810014fe73d8810004fd73d881002cfc73d8810034fd72d881009cfe71d881002ef671d881002cfe70d881002efa70d881000cff76588100067e65588100067d655881002eec6258810004ff7558810024fe7558810024fc7558810004ff745881001cfe7458810004f
  | 2 => 0x57d75885100067f658851016e7c6588510006bf6488510166bc6488510006df638851015edc6388510006ef628851000eec628851000cfc76485100067f65485101567c6548510006bf644851014ebc6448510006df6348510146dc6348510006ef624851000eec6248510005fb7048510005f870485100acfe76941100067f65941100267c6594110006bf649411013ebc6494110006df6394110136dc6394110006ef629411012eec629411000776519411007f7b5094110024ff765411007cfd7654110024fc76541100067f65541100267c6554110006bf6454110126bc6454110006df635411011edc6354110006ef6254110116ec6254110005f77154110005f471541100077551541100a4fe768c1100067f658c11010e7c658c110006bf648c110106bc648c110006df638c110016dc638c110006ef628c1100feec628c110014ff764c11006cfd764c110014fc764c1100067f654c1100f67c654c110005bf744c110075bc744c110006bf644c1100eebc644c110006df634c110016dc634c110006ef624c1100e6ec624c110005f7714c110005f4714c11006fd8304c11009cfe76881100067f65881100de7c6588110006bf64881100d6bc6488110006df63881100cedc6388110006ef628811000eec628811000cff7648110064fd764811000cfc76481100057f754811007d7c75481100067f65481100c67c6548110006bf64481100bebc6448110006df63481100b6dc6348110006ef624811000eec6248110005f77148110005f471481100067f65c41100ae7c65c4110006bf64c411005ebc64c4110006df63c41100a6dc63c4110006ef62c411009eec62c41100077b65c41100077865c4110007bb64c411023fb864c4110007db63c4110007d863c4110007eb62c4110007e862c4110007f251c4110007f151c411023ff241c411023ff141c41100067f65841100967c6584110006bf6484110056bc6484110006df638411008edc6384110006ef6284110086ec6284110065f6768411002df77584110005f5758411000777658411000774658411002df77484110235f57484110007b7648411022fb46484110007d76384110007d46384110007e76284110007e46284110007f3608411004cfd75d941002cff74d941001cfe74d9410004fd74d941002cfc74d9410014fe73d9410004fd73d941002cfc73d941000cfe72d9410004fd72d941002cfc72d94100acfe71d941002ef671d941002cfe70d941002efa70d94100047d769941002e7f64994100067e64994100067d649941002e7c649941002e7f63994100067e639941002e7c639941002e7f62994100067e629941002e7c629941002e7e6099410024ff765941002e7c655941002e7f7559410004ff745941001cfe7459410004fd745941001cfc745941004e7f545
  | 3 => 0xd745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910064ff7258910006ef7258910084ff7158910006f7715891009cff7058910006fb7058910005ee7618910066ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e64118910007e54118910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100267c6554910006bf64549101eebc6454910006df63549101e6dc6354910006ef625491000eec6254910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c91007d7c754c9100067f654c9101de7c654c910006bf644c9101d6bc644c910006df634c910016dc634c910006ef624c91000eec624c910005f7714c910005f4714c910094fe76945100067f65945100267c6594510006bf64945101cebc6494510006df63945101c6dc6394510006ef62945101beec629451007f775194510005f67694510096f6769451007df57594510007776594510026f66594510026f4659451007f746594510026746594510265f77494510265f57494510007b7649451025fb4649451007f77549451025f755494510007d76394510007d46394510007e76294510007e4629451002df6709451007f745094510024fc76545100067f65545100267c6554510006bf64545101b6bc6454510005df735451006ddc7354510006df63545101aedc6354510005ef7254510065ec7254510006ef62545101a6ec625451007f745154510005fb7054510005f8705451007df47654510026f47654510024f4765451007df77554510007777554510007776554510026f66554510026f4655451007f746554510255f77454510255f57454510007b7645451024fb46454510007d77354510007d47354510007d76354510007d4635451007f775354510007755354510007e77254510007e47254510007e76254510007e4625451024776525451007f745254510007f3705451002df47054510007f0705451007f77505451008cfe768c5100067f658c51019e7c658c510006bf648c510196bc648c510006df638c510016dc638c510006ef628c51018eec628c510014fc764c5100067f654c5101867c654c510006bf644c51017ebc644c510006df634c510016dc634c510006ef624c510176ec624c510005fb704c510005f8704c510084fe768851007d7e7588510
  | 4 => 0x8d100a4ff7058d10006fb7058d10005de7618d1006ede7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d10007d64118d10007d54118d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d10006bf6454d101febc6454d10006df6354d10016dc6354d101f6ec6254d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910066ee62d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d8910006ef52d8910066ee52d8910066ec52d8910006ef42d8910066ee42d8910006ed42d8910066ec42d8910006ef32d8910066ee32d8910066ec32d891000cfe71d8910064fd71d891000cfc71d8910066ef21d891002cfe70d8910064fd70d891002cfc70d8910066ef20d8910065ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e641d8910007e541d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910066ee71d8910006ed71d8910006ef51d8910006ec51d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef31d8910006ec31d8910006ef70d8910066ee70d8910006ed70d8910006ef50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910006ef30d8910006ec30d89100057f755891007d7c75589100067f65589100067c6558910005bf7458910075bc7458910006bf6458910006bc6458910005df735891006ddc7358910006df6358910006dc6358910066ec6258910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004f
  | 5 => 0x6be53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110006bf71d9110076be71d9110076bd71d9110076bc71d9110006bf51d9110006bc51d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d9110076be70d9110076bd70d9110076bc70d9110006bf50d9110006bc50d9110006bf30d9110006bc30d9110006bf20d9110006bc20d9110076bd10d9110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1006ede63d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df53d8d1006ede53d8d1006edc53d8d10006df43d8d1006ede43d8d10006dd43d8d1006edc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d1006edf32d8d10006de32d8d1006edc32d8d10014fe71d8d1006cfd71d8d10014fc71d8d1006edf31d8d1002cfe70d8d1006cfd70d8d1002cfc70d8d1006edf30d8d1006dde76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10007d641d8d10007d541d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1006ede71d8d10006dd71d8d10006df51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d1006ede70d8d10006dd70d8d10006df50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006dc20d8d100057f7558d1007d7c7558d100067f6558d100067c6558d10005bf7458d10075bc7458d10006bf6458d10006bc6458d1006edc6358d10005ef7258d10065ec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d1006cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1008cff7158d10006f7715
  | 6 => 0x251c4210007f151c4210024fe76d951007e7e65d9510006bc64d9510004ff74d951001cfe74d9510004fd74d951001cfc74d951007e7f54d95100067e54d95100067d54d951007e7c54d9510014fe73d9510004fd73d9510014fc73d951007e7f53d95100067e53d951007e7c53d951000cfe72d9510004fd72d951000cfc72d951007e7f52d95100067e52d951007e7c52d9510024fe71d951007cfd71d9510024fc71d951007e7f51d951002cfe70d951007cfd70d951002cfc70d951007e7f50d951007d7e76d95100247e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e63d95100067c63d95100067e62d95100067c62d95100077771d95100077641d95100077541d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067c32d95100067f71d951007e7e71d95100067d71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d951007e7e70d95100067d70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067c30d95100067f20d95100067c20d951007e7c6559510005bf7459510075bc7459510006bc6459510005df735951006ddc7359510005ef7259510065ec725951007cff75595100067f7559510004ff7459510006bf7459510004bf745951001cfe7459510004fd745951001cfc7459510006bc745951001cbc7459510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc7359510004ff7259510006ef7259510004ef725951000cfe725951000cfc7259510006ec725951000cec7259510094ff7159510006f771595100acff7059510006fb70595100057e761951007e7e76195100047e76195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067e63195100067c63195100067e62195100067c621951007f757119510007764119510007754119510075be76d9110076be76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006be62d9110006bc62d9110007b771d9110077b471d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110
  | 7 => 0x9610004ff745961001cfe7459610004fd745961001cfc74596100967f54596100067d5459610004ff7359610014fe7359610014fc7359610004ff725961000cfe725961000cfc72596100967f515961002e7e505961002e7c5059610024fe75d8e10004fd75d8e1002cfc75d8e1002cff74d8e1001cfe74d8e10004fd74d8e1002cfc74d8e1008cfd73d8e1000cfe72d8e10004fd72d8e1002cfc72d8e1002ef571d8e1008edc31d8e1002efa70d8e10014ff7658e1002edc6358e10004ff7558e10024fe7558e10024fc7558e10004ff7458e1001cfe7458e10004fd7458e1001cfc7458e1002edf7358e10006df5358e1008edc5358e1008ede4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e1008edf3258e1008edf3158e1002ede3058e1002edc3058e10004ff7654e1002cfe7654e10004fd7654e1002cfc7654e100067f6554e100267c6554e10005f77154e10005f47154e10024fe75d8a10004fd75d8a1002cfc75d8a1002cff74d8a1001cfe74d8a10004fd74d8a1002cfc74d8a10014fe73d8a10004fd73d8a1002cfc73d8a10084fd72d8a1002ef571d8a10086ec21d8a1002efa70d8a1000cff7658a100057f7558a100957c7558a1002eec6258a10004ff7558a100067f7558a100047f7558a10024fe7558a10024fc7558a100067c7558a100247c7558a10004ff7458a1001cfe7458a10004fd7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a1002eef7258a10006ef5258a10086ec5258a10086ee4258a10006ed4258a10086ee3258a10086ef2158a1002eee2058a1002eec2058a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca100057f754ca100957c754ca10016de634ca10006dd634ca1000eee624ca10006ed624ca10005f7714ca10005f4714ca1007cfd76946100067f65946100267c6594610097775194610024ff765461002cfc76546100267e65546100067d6554610005df735461008ddc7354610005ef7254610085ec7254610005fb705461002df8705461006cfd768c610006df638c610016dc638c610014ff764c61002cfc764c610016de634c610006dd634c61008fd4314c610005fb704c61002df8704c610064fd76886100957e75886100057d7588610006ef628861000eec628861000cff764861002cfc764861000eee6248610006ed6248610005fb704861002df8704861004cff765421002e7f655421002e7c655421003cff764c210005bf744c210055bc744c21002fd8304c210034ff76482100057f75482100957c754821002df576c4210006f576c421002ef765c4210006f565c421002ef764c421026ef564c421002ff250c4210007f150c4210005f976c4210006f976c4210007f
  | 8 => 0x24fc75d8b10004ff74d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10014fe73d8b10004fd73d8b10014fc73d8b1009cfd72d8b1009eee42d8b10006ed42d8b1009eee32d8b10006f671d8b10006f970d8b1009eec20d8b1000cff7658b1009eec6258b10004ff7558b10024fe7558b10024fc7558b10004ff7458b1001cfe7458b10004fd7458b1001cfc7458b10004ff7358b10014fe7358b10014fc7358b10006ef7258b1009eec2158b1009eef2058b10004ff7654b10004fe7654b10004fd7654b10004fc7654b10004ff764cb10004fe764cb10004fd764cb10004fc764cb100057f754cb100ad7c754cb10006df634cb10016dc634cb10006ef624cb1000eec624cb10005f7714cb10005f4714cb10024fd76947100267e65947100067d65947100af775194710005fa7094710005f970947100adf57694710026f57694710024f57694710026f665947100af766594710026766594710007756594710026f4659471028df7749471028df574947100af77549471028775549471002df67094710007f27094710007f170947100af74509471004cff76547100067f65547100267c6554710005df73547100a5dc7354710005ef725471009dec72547100af745154710005f7765471004ef77654710007777554710007776554710026f66554710026f465547100af74655471027df7745471027df57454710007d77354710007d473547100af775354710007755354710007e77254710007e472547102777652547100af74525471002df470547100af775054710014fd768c710016de638c710006dd638c710005fa708c710005f9708c71003cff764c71000cfd76887100ad7e75887100057d758871000eee6288710006ed6288710005fa7088710005f97088710034ff764871007cfd76943100067f65943100267c6594310007765194310024ff7654310024fc76543100267e65543100067d6554310005f77154310005f4715431000775515431006cfd768c310006df638c310016dc638c310014ff764c310014fc764c310005bf744c31005dbc744c310016de634c310006dd634c310005f7714c310005f4714c310064fd7688310006ef628831000eec628831000cff764831000cfc76483100057f75483100ad7c754831000eee6248310006ed6248310005f77148310005f47148310094fd75d961002cff74d961001cfe74d9610004fd74d961002cfc74d9610014fe73d961002ede73d9610014de73d9610004fd73d961002edd73d9610004dd73d961002cfc73d96100967f53d961000cfe72d961002eee72d961000cee72d9610004fd72d961002eed72d9610004ed72d961002cfc72d96100067e52d96100967c52d961002ef571d96100967c51d961002efa70d961002e7f50d9610024ff765961002e7c655961002e7f755
  | 9 => 0xc7318520036ee4218520006ed4218520036ee3218520006ed3218520006f74118520006f44118520006f73118520006f43118520036f62118520036f52118520036ec2018520004fe7694520004fd7694520004fc76945200067f65945200267c65945200c7775194520004ff7654520004fe7654520004fc76545200067f65545200267c6554520005df73545200b5dc7354520005ef725452000dec7254520004fe768c520004fd768c520004fc768c5200067f658c52019e7c658c520006df638c520016dc638c520007cd328c520004ff764c520004fe764c520004fc764c5200067f654c5201867c654c5202a4fe769412012e7f65941200267c659412002fe82094120024ff765412000cfe7654120114fd765412000cfc76541200067f65541200267c6554120005ef725412000dec7254120117e8205412029cfe768c1200067f658c12010e7c658c12002dec728c120014ff764c12000cfe764c1200e4fd764c12000cfc764c1200067f654c1200f67c654c120005bf744c1200bdbc744c120006df634c120016dc634c120005ef724c12000dec724c120007cd324c1200076f65881200076c658812002def7488120295ed748812002def7388120005ed7388120006ec618812002dee708812002fea708812002eef608812000feb60881200ae7e65d97100acfd75d9710004ff74d971001cfe74d9710004fd74d971001cfc74d97100ae7f54d97100067d54d9710014fe73d9710004fd73d9710014fc73d971000cfe72d9710004fd72d971000cfc72d9710006f671d97100ae7f51d9710006f970d97100ae7c50d9710024ff76597100ae7c65597100067f7559710004ff745971001cfe7459710004fd745971001cfc7459710004ff7359710014fe7359710014fc73597100ae7f5359710004ff725971000cfe725971000cfc72597100067e52597100ae7c52597100ae7c51597100ae7f505971005dbe74d8f10005bd74d8f100a6de63d8f10024fe75d8f10004fd75d8f10024fc75d8f10004ff74d8f1001cfe74d8f10006be74d8f1001cbe74d8f10004fd74d8f10006bd74d8f10004bd74d8f1001cfc74d8f100a4fd73d8f100a6de43d8f10006dd43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100a6df32d8f10006f671d8f10006f970d8f100a6dc30d8f10014ff7658f100a6dc6358f10004ff7558f10024fe7558f10024fc7558f10004ff7458f1001cfe7458f10004fd7458f1001cfc7458f10006df7358f10004ff7258f1000cfe7258f1000cfc7258f100a6dc3158f100a6df3058f10004ff7654f10004fe7654f10004fd7654f10004fc7654f100267e6554f100067d6554f100ad7e75d8b100057d75d8b1009eee62d8b10024fe75d8b100067e75d8b100247e75d8b10004fd75d8b100067d75d8b100047d75d8b10
  | 10 => 0x9520004ff7359520014fe7359520014fc7359520114ff7259520006ef7259520004ff7159520004fc71595202c4ff7059520006fb705952012d7e76195200c67e761952012c7e76195200067f64195200067e64195200067d64195200067c64195200067e63195200067c63195202a67f62195202a76e42195200076d42195202a76e32195202a67f60195202a77b20195202a76c20195202a7782019520014fe76d8d200067f65d8d200067c65d8d200b6de63d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df43d8d200b6dc43d8d2002cff72d8d2000cfe72d8d200fcfd72d8d2000cfc72d8d200feee42d8d20006ed42d8d200fedf32d8d200fedd32d8d20004fe71d8d20004fd71d8d200b6dc31d8d2000cfd70d8d200b6df30d8d200057f7558d200c57c7558d200067f6558d200067c6558d20005bf7458d200bdbc7458d200b6dc6358d20005f77158d20005f47158d202bdfb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d20004fd7458d2001cfc7458d20006bc7458d2001cbc7458d200fcff7358d20006df7358d200e4ff7258d20006ef7258d200e6ee4258d20006ed4258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d202bcff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200267c6554d200b5ec764c920016ec764c920014ec764c9200076f754c9200076c754c9200076f654c9200076c654c9202b5ef744c9202b5ed744c9202aeef644c9202aeed644c92000def734c92000fcf734c920007cf634c920016ee634c920016ec634c9200b7cc634c9200b7ce534c920007cd534c920007e7714c920007e4714c9200b7cc314c920007eb704c92002dec704c920007e8704c92000eef604c92000feb604c9200b7cf304c9200067f65d85200067c65d8520024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d8520006f741d8520006f441d8520006f731d8520006f431d8520086f621d8520086f521d85200c57e75985200057d75985200067f65985200067c6598520006f76198520065f970985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520005df73585200b5dc735852009dfb70585200067f65185200067c6518520006f56118520024fe7518520004fd7518520024fc7518520004ff741852001cfe7418520004fd741852001cfc7418520014fe7318520004fd7318520014f
  | 11 => 0x1cfe7458620004fd745862001cfc7458620004ff7358620006df7358620004df7358620014fe7358620014fc7358620006dc7358620014dc7358620006f64158620006f54158620006f73158620006f43158620066f62158620066f52158620066ec215862002cfc705862002ef6105862002ef41058620004ff769462002cfe7694620004fd7694620006f66194620006f561946200df775194620004ff7654620004fd765462002cfc76546200267e65546200067d6554620005df73546200cddc7354620005ef725462000dec7254620006f66154620006f56154620004ff768c62002cfe768c620004fd768c620006df638c620016dc638c620004ff764c620004fd764c62002cfc764c620005ef724c62000dec724c6200076e75886200076d758862016eee658862016eec65886202ceef64886202ceed6488620006ef6388620006ed638862000dee718862000fe67188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862000eee608862000fea60886202c4ff76542202bcff764c220005bf744c2200d5bc744c22002edf634c22002edc634c220024fe76d95200c67e65d9520004ff74d952001cfe74d9520004fd74d952001cfc74d95200c67f54d95200067e54d95200067d54d95200c67c54d9520014fe73d9520004fd73d9520014fc73d95200c67f53d95200067e53d95200c67c53d952002cff72d952000cfe72d952012cfd72d952000cfc72d952012e7f52d952012e7d52d9520004fe71d9520004fd71d95200c67f51d95200c67c51d952000cfd70d95200c67f50d95202a57e76d95200247e76d95200067f64d95200067e64d95200067d64d95200067c64d95200067e63d95200067c63d952012f6e42d95200076d42d952012f6e32d952012f7b20d952012f6c20d952012f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952012e7f72d952012e7e72d952012e7d72d952012e7c72d952012e7f42d952012e7e42d952012e7d42d952012e7c42d952012e7f32d952012e7e32d952012e7d32d952012e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067c31d952012e7f21d952012e7e21d952012e7d21d952012e7c21d952012e7f70d95200c67e70d952012e7d70d95200067f40d95200067e40d95200067d40d95200067c40d95200067f30d95200067c30d952012e7f20d952012e7e20d952012e7c20d95200c67c65595202c5fb705952012cff75595200067f7559520004ff745952001cfe7459520004fd745952001cfc745
  | 12 => 0x75194530004ff7654530004fe7654530004fc76545300267e65545300067d6554530006bf64545301b6bc6454530005df7354530015dc7354530005ef72545300e5ec7254530004fe7688530004fd7688530004fc76885300f57e75885300057d7588530006bf6488530166bc6488530006ef628853000eec6288530007cd3288530004ff7648530004fe7648530004fc7648530006bf644853014ebc64485302e4fe76941300267e65941300067d6594130006bf649413013ebc64941300f77b5094130024ff7654130014fe765413011cfd7654130014fc76541300067f65541300267c6554130006bf6454130126bc6454130005df7354130015dc735413002ddf748c1302dddd748c1300079f648c1302d79c648c130005dd728c130006dc618c13002dde708c13002fda708c13002edf608c130017db608c130114fd75d962002cff74d962001cfe74d9620004fd74d962002cfc74d9620014fe73d9620004fd73d962002cfc73d962002eed72d962012e7e52d962012e7c52d9620004fe71d9620004fd71d962002cfe70d962002efa70d9620024ff765962002e7c655962002e7f7559620004ff745962001cfe7459620004fd745962001cfc74596200de7f54596200067d5459620004ff7359620014fe7359620014fc73596200067e53596200de7c53596201167f52596201167d5259620004ff7159620004fc71596200de7f515962002cfe705962002cfc705962002e7e505962002e7c5059620024fe75d8e2002e7e75d8e200247e75d8e20004fd75d8e2002e7d75d8e200047d75d8e2002cfc75d8e2002cff74d8e2001cfe74d8e20004fd74d8e2002cfc74d8e200e4fd73d8e2002eed72d8e20004fe71d8e2002ef671d8e20004f671d8e20004fd71d8e2002ef571d8e20004f571d8e200cedc31d8e200feec21d8e2002cfe70d8e2002efa70d8e2002edf30d8e2002eef20d8e20014ff7658e2002edc6358e20004ff7558e20024fe7558e20024fc7558e20004ff7458e2001cfe7458e20004fd7458e2001cfc7458e2002edf7358e200cede4358e20006dd4358e200e6df3258e200e6dd3258e20004ff7158e20004fc7158e200e6ec2158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e200e6ef2058e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e20005ef7254e2000dec7254e2002ef76198620024fe7598620004fd7598620024fc7598620004ff749862001cfe7498620004fd749862001cfc7498620014fe7398620004fd7398620014fc7398620006f64198620006f54198620006f73198620006f4319862009ef6219862009ef5219862002cfe709862002ef6109862002ef41098620005df73586200cddc735862002ef46158620004ff7558620024fe7558620024fc7558620004ff7458620
  | 13 => 0x9130306bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bc52d9130306bf32d9130306be32d9130306bd32d9130306bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006bc51d9130306bf31d9130306be31d9130306bd31d9130306bc31d9130006bf21d9130006bc21d9130306bf70d91300eebe70d9130306bd70d9130306bc70d9130006bf50d9130006bc50d9130306bf30d9130306be30d9130306bd30d9130306bc30d9130006bf20d9130006bc20d913000cfe76d8930006bf64d8930006bc64d89300e6ee62d8930024fe75d8930004fd75d8930024fc75d8930004ff74d893001cfe74d8930004fd74d893001cfc74d893000cfc73d8930006ef52d89300e6ec52d89300e6ee32d89300ceed32d8930004fe71d8930004fd71d89300e6ec21d8930014fd70d89300e6ef20d89300057f75589300f57c7558930005bf74589300edbc7458930006bf6458930006bc64589300e6ec6258930005f77158930005f471589302fdfb7058930004ff7654930004fe7654930004fc7654930006bf64549301eebc64549300e5dc764c93000edc764c93000cdc764c9300075f754c9300075c754c930006df654c930006dd654c9302f5df744c9302f5dd744c9300079f644c9302ef9c644c930015df724c930017cf724c930007cf624c93000ede624c93000edc624c9300e7cc624c9300e7ce424c9302efcd424c930007d7714c930007d4714c9300e7cc214c930007db704c93002ddc704c930007d8704c930016df604c930017db604c9300e7cf204c930006bf64d8530006bc64d8530024fe75d8530004fd75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d853000cfe72d8530004fd72d853000cfc72d8530006f751d8530006f451d853008ef631d853008ef531d8530006f721d8530006f421d85300edbe7498530005bd7498530006bf6498530006bc6498530006f7619853006df970985300057f75585300f57c7558530005bf74585300edbc7458530006bf6458530006bc6458530005ef72585300e5ec72585300a5fb70585300f57e75185300057d7518530006bf6418530006bc6418530006f56118530024fe75185300067e75185300247e7518530004fd75185300067d75185300047d7518530024fc7518530004ff741853001cfe7418530004fd741853001cfc741853003ede4318530006dd431853000cfe7218530004fd721853000cfc721853003edf3218530006dd3218530006f75118530006f4511853003ef6311853003ef53118530006f72118530006f4211853003edc3018530004fe7694530004fd7694530004fc76945300067f65945300267c6594530006bf64945301cebc64945300f77
  | 14 => 0x6f541986300a6f631986300a6f53198630006f72198630006f4219863002cfe709863002ef6109863002ef41098630005ef72586300fdec725863002ef46158630004ff7558630024fe7558630024fc7558630004ff745863001cfe7458630004fd745863001cfc7458630004ff7258630006ef7258630004ef725863000cfe725863000cfc7258630006ec725863000cec7258630006f64158630006f5415863006ef6315863006ef5315863006edc3158630006f72158630006f4215863002cfc705863002ef6105863002ef41058630004ff769463002cfe7694630004fd7694630006f66194630006f5619463010f775194630004ff7654630004fd765463002cfc76546300267e65546300067d6554630005df7354630015dc7354630005ef72546300fdec7254630006f66154630006f5615463019ede658c63019edc658c63031edf648c63031edd648c630006dd628c630015de718c630017d6718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c630016de608c630017da608c630004ff768863002cfe7688630004fd768863010d7e75886300057d758863000eec6288630004ff7648630004fd764863002cfc7648630005df7348630015dc7348630314ff765423011fdb3054230024fe76d95300f67e65d9530006bc64d9530004ff74d953001cfe74d9530004fd74d953001cfc74d953002cff73d9530014fe73d9530134fd73d9530014fc73d95301367f53d95301367d53d953000cfe72d9530004fd72d953000cfc72d95300067e52d95300f67c52d9530136df32d9530004fe71d9530004fd71d95300f67c51d9530014fd70d95300f67f50d95300f67c6559530005bf74595300edbc7459530006bc6459530005ef72595300e5ec7259530005f77159530005f47159530315fb7059530134ff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe7459530004fd745953001cfc7459530006bc745953001cbc74595300f67f54595300067d545953011cff7359530006df7359530004ff7259530006ef7259530004ef725953000cfe725953000cfc7259530006ec725953000cec725953011edf3259530004ff7159530006f77159530004f77159530004fc7159530006f47159530004f471595300f67f5159530314ff7059530006fb70595300f67c505953030dbe76d91300eebe76d913001cbe76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91300079f73d91303079c73d9130006be62d9130006bc62d91303079f32d9130307bb30d91303079c30d9130307b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130306bf73d9130306be73d9130306bd73d9130306bc73d9130306bf53d9130306be53d9130306bd53d
  | 15 => 0xe764c950004fc764c9500057f754c9500257c754c950016de634c950005f7714c950005f4714c950004ff74d855001cfe74d8550004fd74d855001cfc74d8550014fe73d8550004fd73d8550014fc73d855000cfe72d8550004fd72d855000cfc72d8550096f651d8550096f551d8550006f731d8550006f431d8550006f7619855007df97098550005bf7458550125bc7458550005df735855011ddc7358550005ef7258550115ec72585500adfb7058550006f56118550004ff741855001cfe7418550004fd741855001cfc741855004e7f54185500067d5418550014fe7318550004fd7318550014fc731855000cfe7218550004fd721855000cfc721855004e7f511855004ef6511855004ef55118550006f73118550006f4311855004e7c501855032d7f745455032d7d74545500075f73545500075c73545500067f63545500076f72545500076c72545501a67e62545501a67c62545500257f71545500277771545500077761545500067c61545500077461545500077b705455002d7c70545500077870545500267f60545500277b6054550004fe768c550004fd768c550004fc768c5500257e758c5500057d758c550006df638c550016dc638c550004ff764c550004fe764c550004fc764c550004fe7688550004fd7688550004fc76885500257e75885500057d7588550006ef628855000eec6288550004ff7648550004fe7648550004fc764855002d7f74941503257d74941500067f639415012e7e629415012e7c62941500057d71941500067c619415002d7e709415002f7a709415002e7f60941500277b609415011cfd75d963002cff74d963001cfe74d9630004fd74d963002cfc74d963002edd73d963000cfe72d9630004fd72d963002cfc72d9630004fe71d9630004fd71d963002cfe70d963002efa70d9630024ff765963002e7c655963002e7f7559630004ff745963001cfe7459630004fd745963001cfc745963010e7f54596300067d545963011e7f535963011e7d5359630004ff725963000cfe725963000cfc72596300067e525963010e7c5259630004ff7159630004fc715963010e7f515963002cfe705963002cfc705963002e7e505963002e7c505963000cff7658a3002eec6258a30004ff7558a30024fe7558a30024fc7558a30004ff7458a3001cfe7458a30004fd7458a3001cfc7458a300feee4258a30006ed4258a300feee3258a300b6ed3258a30004ff7158a30004fc7158a300b6dc3158a3002cfe7058a3002cfc7058a300b6df3058a3002eee2058a3002eec2058a30004ff7654a30004fd7654a3002cfc7654a3002ef76198630024fe7598630004fd7598630024fc7598630004ff749863001cfe7498630004fd749863001cfc749863000cfe7298630004fd729863000cfc7298630006f64198630
  | 16 => 0x8a5001cfe7458a50004fd7458a5001cfc7458a50004ff7358a50014fe7358a50014fc7358a5012e7e5258a5012eee5258a500c6ed5258a5012e7c5258a5012eee4258a50006ed4258a5012eee3258a50004ff7158a50004fc7158a5012eec2158a5002cfe7058a5002cfc7058a5002eee2058a5002eec2058a50004ff764ca50004fd764ca5002cfc764ca500057f754ca500257c754ca50016de634ca50006dd634ca500075d534ca5000eee624ca50006ed624ca50005f7714ca50005f4714ca5002ef76198650004ff749865001cfe7498650004fd749865001cfc7498650014fe7398650004fd7398650014fc739865000cfe7298650004fd729865000cfc72986500aef651986500aef55198650006f64198650006f5419865002cfe709865002ef6109865002ef4109865002ef46158650004ff745865001cfe7458650004fd745865001cfc7458650004ff7358650014fe7358650014fc735865007e7f53586500067d5358650004ff725865000cfe725865000cfc72586500067e525865007e7c525865007ef6515865007ef5515865007e7c5158650006f64158650006f5415865002cfc705865007e7f505865002ef6105865002ef410586503467f64946503467d64946500057d739465012d7e729465012d7c72946500257e71946500277671946500077661946500067d61946500077561946500067561946500077a70946500057d70946500077970946500057970946500267e60946500277a6094650004ff768c65002cfe768c650004fd768c6500057f758c6500257c758c650016de638c650006dd638c65019f5f538c650004ff764c650004fd764c65002cfc764c6500057f754c6500257c754c650004ff768865002cfe7688650004fd76886500257e75886500057d758865000eee6288650006ed628865012f6c5288650004ff7648650004fd764865002cfc76486500057f75486500257c7548650014fe76d8d5011ede63d8d50014fc75d8d50004ff74d8d5001cfe74d8d50004fd74d8d5001cfc74d8d5010e7f54d8d500067d54d8d5011ede53d8d5010edd53d8d5000cfe72d8d50004fd72d8d5000cfc72d8d50004fe71d8d50004fd71d8d5010e7f51d8d5011edc31d8d50024fd70d8d5010e7c50d8d5011edf30d8d50005bf7458d50125bc7458d5011edc6358d50005ef7258d50115ec7258d50005f77158d50005f47158d5033dfb7058d5000cfe76d8950116ee62d895000cfc75d8950004ff74d895001cfe74d8950004fd74d895001cfc74d8950014fe73d8950004fd73d8950014fc73d8950116ee52d89500deed52d8950116ee42d8950006ed42d8950006ef32d8950116ec32d8950004fe71d8950004fd71d8950116ec21d8950024fd70d8950116ef20d8950116ec6258950335fb7058950004ff764c950004f
  | 17 => 0x374ff7159521006f77159521004ff705952102cfc7059521014fe76d8d21146de63d8d21024fe75d8d21004fd75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006df53d8d21146dc53d8d21146de43d8d21006dd43d8d2118cff72d8d2118cfd72d8d2118edf32d8d2118edd32d8d2100cfd71d8d21146df31d8d2118eec21d8d2102cfe70d8d21004fd70d8d21146dc30d8d210057f7558d211557c7558d21146dc6358d2136df77158d21004ff7558d210067f7558d210047f7558d21024fe7558d21024fc7558d210067c7558d210247c7558d21004ff7458d2101cfe7458d21004fd7458d2101cfc7458d2118cff7358d21006df7358d21174ff7258d21006ef7258d2136cff7158d21006f77158d2136cf77158d21146dc3158d21176ec2158d21004ff7058d2102cfc7058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21364fe7694521157775194521024ff765452100cfe76545211a4fd765452100cfc76545210067f65545210267c6554521005df7354521145dc7354521005ef725452100dec725452135cfe768c521016de638c521006dd638c521014ff764c52100cfe764c521174fd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724c5210076e75885210076d758852116eee658852116eec6588521356ef6488521356ed6488521006ef6388521006ed638852100dee718852100fe6718852100eef618852100fe76188521024fe75d8121004fd75d8121024fc75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d812109efa20d8121006fb60981210057f75581211557c7558121005bf745812114dbc7458121005df7358121145dc7358121006f96018121024fe7518121004fd751812102cfc751812102cff741812101cfe7418121004fd741812102cfc7418121014fe7318121004fd731812102cfc7318121006ee2118121036ec211812102efa2018121036f92018121014ff7658e5002edc6358e50004ff7458e5001cfe7458e50004fd7458e5001cfc7458e50136de5358e500f6dd5358e50136de4358e50006dd4358e50004ff7258e5000cfe7258e5000cfc7258e50136df3258e50004ff7158e50004fc7158e50136dc3158e5002cfe7058e5002cfc7058e5002ede3058e5002edc3058e501357f7654e500167f7654e500147f7654e5034e7f6454e5034e7d6454e500257f7354e500275f7354e500167e6354e501375e6354e500075d6354e500167c6354e5012d7e7254e5012d7c7254e501375f3254e500057c7154e500057f7054e500077b7054e50007787054e500267e6054e500277a6054e5000cff7658a500257c7558a5002eec6258a5012f6e5258a50004ff745
  | 18 => 0xf7358e21176ee4258e21006ed4258e21176df3258e21176dd3258e2100cfc7158e2115edc3158e21004ff7058e2102cfc7058e21004ff7654e21004fe7654e21004fd7654e21004fc7654e210267e6554e210067d6554e21005ef7254e2100dec7254e2115def764ca21016ef764ca21014ef764ca210076f754ca2116dee754ca2116dec754ca210076c754ca2116d6c754ca210076e654ca210076d654ca21385ef744ca21385ed744ca2137eef644ca2137eed644ca2100def734ca2100fcf734ca21016ee634ca2115fce634ca21007cd634ca21016ec634ca2115fce534ca21007cd534ca21005ef714ca21007e7714ca21007e4714ca2100eee614ca2100fe6614ca2115fcc314ca21005ec704ca2115fcf304ca2100cff7694621024fe769462100cfd76946210267e65946210067d659462100dee7294621005ed729462116f7751946211bfe72194621374ff76546210267e65546211a67d6554621005df735462115ddc735462116def725462100dec72546211a76c52546211a7e7215462100cff768c621014fe768c62100cfd768c62119e7e658c6210067d658c621016de638c621006dd638c62100dee728c621005ed728c621007cd328c62136cff764c6211867e654c6210067d654c62100dee724c62116d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb6098221024fe7598221004fd759822102cfc759822102cff749822101cfe7498221004fd749822102cfc7498221014fe7398221004fd739822102cfc739822102efa2098221086f920982210067e65582210067d6558221005bf7458221165bc7458221004ff7558221024fe7558221024fc7558221004ff7458221006bf7458221004bf745822101cfe7458221004fd745822101cfc7458221006bc745822101cbc7458221004ff7358221014fe7358221014fc7358221066ee4258221006ed4258221066ee3258221006ed3258221066fa2058221066ec205822116d7e75182210057d75182210067e65182210067d6518221006f96018221024fe76d95211567e65d9521004ff74d952101cfe74d9521004fd74d952101cfc74d95211567f54d95210067d54d9521014fe73d9521004fd73d9521014fc73d95210067e53d95211567c53d95211bcff72d95211bcfd72d95211be7f52d95211be7d52d952100cfd71d95211567f51d952102cfe70d9521004fd70d95211567c50d95211567c6559521005df7359521145dc7359521375f771595211bcff75595210067f7559521004ff745952101cfe7459521004fd745952101cfc7459521004ff7359521006df7359521004df7359521014fe7359521014fc7359521006dc7359521014dc73595211a4ff7259521006ef725952116cef72595211a67e52595211a67c5259521
  | 19 => 0x9621004ff74d962101cfe74d9621004fd74d962101cfc74d9621014fe73d9621004fd73d9621014fc73d9621006ed72d962116eef52d96211beec52d9621364fe71d9621006f671d962102cfe70d9621004fd70d96211a47d76996210067f64996210067e64996210067d64996210067c64996210067e63996210067c639962116f6f72996213776c72996213767d62996213776e42996210076d42996213776e32996213767e61996213776f21996213777721996213777421996213776c2099621024ff765962116e7c655962100dec725962116f6f52596210067f7559621004ff745962101cfe7459621004fd745962101cfc745962116e7f54596210067e54596210067d545962116e7c5459621004ff7359621014fe7359621014fc735962116e7f53596210067e535962116e7c535962116eef72596211a67f525962116eef52596211a67d52596211a6ec525962100cfc715962116e7c5159621004ff705962102cfc705962116e7f505962116e7c50596213757f765962116e7f76596210247f76596210067f64596210067e64596210067d64596210067c64596210067e63596210067c63596210076f72596211a76c72596211a76e42596210076d42596211a76e32596211a76f21596211a77721596211a77421596211a76c20596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596211a67f72596210066f72596211a67e72596211a67d72596211a67c72596211a66c72596211a67f42596211a67e42596211a67d42596211a67c42596211a67f32596211a67e32596211a67d32596211a67c325962116e7f71596211a67e71596211a67c71596210067f41596210067e41596210067d41596210067c41596210067f31596210067c31596211a67f21596211a67e21596211a67d21596211a67c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067d40596210067c40596210067f30596210067c30596211a67f20596211a67e20596211a67d20596211a67c205962116d7e75d8e210057d75d8e210067e65d8e210067d65d8e2115ede63d8e2135df671d8e21024fe75d8e210067e75d8e210247e75d8e21004fd75d8e210067d75d8e210047d75d8e21024fc75d8e21004ff74d8e2101cfe74d8e21004fd74d8e2101cfc74d8e21174fd73d8e21006ed72d8e2118eee42d8e21006ed42d8e2135cfe71d8e21006f671d8e2135cf671d8e2102cfe70d8e21004fd70d8e21014ff7658e210067e6558e210067d6558e2115edc6358e21004ff7558e21024fe7558e21024fc7558e21004ff7458e2101cfe7458e21004fd7458e2101cfc7458e21006d
  | 20 => 0x6fb6098231024fe7598231004fd759823102cfc759823102cff749823101cfe7498231004fd749823102cfc749823100cfe7298231004fd729823102cfc729823102efa309823108ef930982310057f755823119d7c7558231004ff75582310067f75582310047f7558231024fe7558231024fc75582310067c75582310247c7558231004ff745823101cfe7458231004fd745823101cfc745823106ede4358231006dd4358231004ff725823100cfe725823100cfc725823106edf3258231006dd325823106efa305823106edc305823119d7e75182310057d7518231006f96018231024fe76d95311867e65d9531004ff74d953101cfe74d9531004fd74d953101cfc74d95311867f54d95310067d54d95311c4ff73d95311c4fd73d95311c67f53d95311c67d53d953100cfe72d9531004fd72d953100cfc72d95310067e52d95311867c52d9531014fd71d95311867f51d953102cfe70d9531004fd70d95311867c50d95311867c6559531005ef7259531175ec72595313a5f771595311c4ff75595310067f7559531004ff745953101cfe7459531004fd745953101cfc74595311acff7359531006df735953119cdf7359531004ff7259531006ef7259531004ef725953100cfe725953100cfc7259531006ec725953100cec72595313a4ff7159531006f77159531004ff705953102cfc705953100cfe76d8931176ee62d8931024fe75d8931004fd75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d8931006ef52d8931176ec52d8931176ee42d8931006ed42d8931176ee32d893115eed32d8931014fd71d893115edc31d8931176ef21d893102cfe70d8931004fd70d8931176ec20d89310057f75589311857c7558931176ec625893139df77158931004ff7654931004fe7654931004fc7654931394fe76945311877751945311c7d43194531024ff7654531014fe76545311acfd7654531014fc76545310067f65545310267c6554531005df7354531015dc7354531005ef7254531175ec72545311afd4315453119ede658c53119edc658c53138edf648c53138edd648c531006df628c531015de718c531017d6718c531016df618c531017d7618c531024fe75d8131004fd75d8131024fc75d8131004ff74d813101cfe74d8131004fd74d813101cfc74d813100cfe72d8131004fd72d813100cfc72d81310a6fa30d8131006fb60981310057f75581311857c7558131005bf745813117dbc7458131005ef7258131175ec7258131006f96018131024fe7518131004fd751813102cfc751813102cff741813101cfe7418131004fd741813102cfc741813100cfe7218131004fd721813102cfc7218131006de311813103edc311813102efa301813103ef9301813116e7e65d9621365f671d96211a4fd75d
  | 21 => 0xd72d815100cfc72d81510aefa50d8151006fb40d8151006f840d81511adde7398151005dd7398151006df6398151006dc63981511a5ee7298151005ed7298151006ef6298151006ec6298151006fb6098151005bf74581511b5bc7458151005df73581511addc7358151006df6358151006dc6358151005ef72581511a5ec7258151006ef6258151006ec6258151006df6318151006dc6318151006ef6218151006ec6218151006f9601815102cff741815101cfe7418151004fd741815102cfc7418151014fe7318151004fd731815102cfc731815104e7f53181510067d531815100cfe7218151004fd721815102cfc72181510067e521815104e7c521815102ef571181510067e511815104e7c511815102e7f501815102efa501815104ef95018151006fb401815102ef8401815119e7e65d9631395f671d96311acfd75d9631004ff74d963101cfe74d9631004fd74d963101cfc74d963119e7f54d96310067d54d9631006dd73d963119edf53d96311c6dc53d963100cfe72d9631004fd72d963100cfc72d96311c6df32d9631394fe71d9631006f671d963119e7f51d963102cfe70d9631004fd70d963119e7c50d9631024ff765963119e7c6559631015dc735963119f5f53596310067f7559631004ff745963101cfe7459631004fd745963101cfc745963119edf73596311ae7f535963119edf535963119e5f53596311ae7d53596311aedc5359631004ff725963100cfe725963100cfc72596310067e525963119e7c52596311aedf3259631014fc715963119e7c5159631004ff705963102cfc705963119e7f505963119d7e75d8a310057d75d8a3118eee62d8a313bdf671d8a3100cff7658a3118eec6258a31004ff7558a31024fe7558a31024fc7558a31004ff7458a3101cfe7458a31004fd7458a3101cfc7458a3118eee3258a31146ed3258a31014fc7158a3118eec2158a31004ff7058a3102cfc7058a31004ff7654a31004fd7654a31004fc7654a31005df7354a31015dc7354a3118ddf764ca3100edf764ca3100cdf764ca310075f754ca3119dde754ca3119ddc754ca310075c754ca3119d5c754ca31006df654ca31006dd654ca313b5df744ca313b5dd744ca31015df724ca31017cf724ca3100ede624ca3118fce624ca31007cd624ca3100edc624ca3118fce424ca313afcd424ca31005df714ca31007d7714ca31007d4714ca31016de614ca31017d6614ca3118fcc214ca31005dc704ca3118fcf204ca31014ff7694631024fe7694631014fd76946310267e65946310067d6594631015de7394631005dd739463119f7751946311c7d731946313a4ff76546310067f65546310267c655463119ddf7354631015dc735463119f5f5354631005ef725463118dec72546311afd73154631195be74d8231005bd74d8231
  | 22 => 0x8951006dc63d89511a6ee62d89511a76e52d8951004ff74d895101cfe74d8951004fd74d895101cfc74d8951014fe73d8951004fd73d8951014fc73d89511a67e52d89511a6ee52d895116eed52d89511a67c52d8951006ef42d89511a6ee42d8951006ed42d89511a6ec42d8951006ef32d89511a6ee32d89511a6ec32d8951024fd71d89511a6ef21d895102cfe70d8951004fd70d89511a6ef20d89511a6ec20d89511a5ee76d895100cee76d89511a76e75d89510076d75d8951006ef64d8951006ee64d8951006ed64d8951006ec64d8951006ef63d8951007cf63d8951006cf63d8951006ee63d8951006ed63d8951006ec63d8951007cc63d8951006cc63d895116f6f53d89510076d53d895116fe751d895116f6c51d895116fe451d895116f6f50d895116eef75d89511a6ee75d89511a66e75d895116eec75d8951006ef74d8951006ee74d8951006ed74d8951006ec74d895116eef54d895116eee54d895116eed54d895116eec54d8951006ef73d8951006ee73d8951006ed73d8951006ec73d895116eef53d895116eee53d895116eed53d895116eec53d8951006ef43d8951006ee43d8951006ed43d8951006ec43d895116eef71d89511a6ee71d895116eed71d895116eef51d895116eee51d895116eec51d8951006ef41d8951006ee41d8951006ed41d8951006ec41d8951006ef31d8951006ec31d8951006ef70d8951006ee70d8951006ed70d8951006ec70d895116eef50d895116eee50d895116eed50d895116eec50d8951006ef40d8951006ee40d8951006ed40d8951006ec40d8951006ef30d8951006ec30d8951005df73589511addc7358951006df6358951006dc63589511a6ec62589513d5f7715895116dee76189511a6ee76189511a76f75189511a76c75189511beef65189511a7ae74189511a7ad7418951006ef6418951006ee6418951006ed6418951006ec6418951006ef6318951007cf6318951006cf6318951006ee6318951006ed6318951006ec6318951007cc6318951006cc63189513cf6f53189510076d5318951376ef61189513cfe751189513cf6c51189513cfe451189513cf6f5018951004ff764c951004fe764c951004fc764c9510057f754c9510257c754c951006df634c951016dc634c9510075d534c951006ef624c95100eec624c951005f7714c951005f4714c9513c67f64945513c67d64945510057d73945510075f63945510075c63945511a57e72945511a57c72945510076f62945510076c62945510257e71945510277671945510267f61945510277761945510267761945510057d7094551006df63d8151006dc63d8151006ef62d8151006ec62d8151004ff74d815101cfe74d8151004fd74d815101cfc74d8151014fe73d8151004fd73d8151014fc73d815100cfe72d8151004f
  | 23 => 0x5f4714ca511df77514ca510af7751d8251097775198251006fb609825102cff749825101cfe7498251004fd749825102cfc7498251014fe7398251004fd739825102cfc739825100cfe7298251004fd729825102cfc729825102ef6719825102efa5098251096f9509825107f775158251004ff745825101cfe7458251004fd745825101cfc745825107e7f54582510067d5458251004ff7358251014fe7358251014fc7358251004ff725825100cfe725825100cfc725825107e7f515825107efa505825107e7c505825104f775118251006f96018251014fe76d8d511aede63d8d51004ff74d8d5101cfe74d8d51004fd74d8d5101cfc74d8d511aede53d8d5119edd53d8d51006df43d8d511aede43d8d51006dd43d8d511aedc43d8d5100cfe72d8d51004fd72d8d5100cfc72d8d511aedf32d8d51006de32d8d511aedc32d8d51024fd71d8d511aedf31d8d5102cfe70d8d51004fd70d8d511aedf30d8d511aedc30d8d511adde76d8d51014de76d8d510075f75d8d5119f5c75d8d51006df64d8d51006de64d8d51006dd64d8d51006dc64d8d51006de62d8d51006dc62d8d510075e52d8d5119f5c52d8d5119fd751d8d5119f5c51d8d5119fd451d8d5119f5f50d8d5119edf75d8d511aede75d8d5119edc75d8d51006df74d8d51006de74d8d51006dd74d8d51006dc74d8d5119edf54d8d5119ede54d8d5119edd54d8d5119edc54d8d51006df72d8d51006de72d8d51006dd72d8d51006dc72d8d5119edf52d8d5119ede52d8d5119edd52d8d5119edc52d8d51006df42d8d51006de42d8d51006dd42d8d51006dc42d8d5119edf71d8d511aede71d8d5119edd71d8d5119edf51d8d5119ede51d8d5119edc51d8d51006df41d8d51006de41d8d51006dd41d8d51006dc41d8d51006df21d8d51006dc21d8d51006df70d8d51006de70d8d51006dd70d8d51006dc70d8d5119edf50d8d5119ede50d8d5119edd50d8d5119edc50d8d51006df40d8d51006de40d8d51006dd40d8d51006dc40d8d51006df20d8d51006dc20d8d511aedc6358d51005ef7258d511a5ec7258d513edf77158d5119dde7618d511aede7618d511af5e7518d511af5d7518d511c6df6518d51006df6418d51006de6418d51006dd6418d51006dc6418d51006de6218d51006dc6218d510075e5218d513e75c5218d513a6df6118d513e7d75118d513e75c5118d513e7d45118d513e75f5018d511ad7c7654d510167c7654d510147c7654d513de7f6454d513de7d6454d510257f7354d510275f7354d510075f6354d510167e6354d510167c6354d511af5c6354d511a57e7254d511a57c7254d511af5f3254d51007777154d510057c7154d51007747154d51005747154d510267f6154d51027776154d510057f7054d5100cfe76d89510257e75d8951006df63d
  | 24 => 0x75418532006f65418532006f55418532006f4541853235ef773185323bef6731853235ef5731853235ef473185323bef753185323bef653185323bef553185323bef453185323bef743185323bef643185323bef543185323bef4431853235ef7721853235ef6721853235ef5721853235ef4721853235ef7521853235ef6521853235ef5521853235ef4521853235ef7421853235ef6421853235ee6421853235ef54218532006e5421853235ef4421853235ef7321853235ef6321853235ef5321853235ef43218532006f77018532006f67018532006f57018532006f47018532006f75018532006f45018532006f74018532006f64018532006f54018532006f440185323bef730185323bef630185323bef530185323bef4301853235ef7201853235ef6201853235ef5201853235ef420185320067f65d81320067c65d8132006f761d8132006f461d8132024fe75d8132004fd75d8132024fc75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d813200cfd73d8132014fd72d81322beee42d8132006ed42d8132004fe71d8132004fd71d8132006fb40d8132006f840d81322fefa30d81322befa20d81321dd7e75981320057d75981320067f65981320067c6598132005f67198132005f57198132006f76198132006f46198132006fb60981320057f75581321dd7c75581320067f65581320067c6558132005bf74581321d5bc7458132005f77158132005f47158132006f76158132006f461581320067f65181320067c6518132006f76118132006f46118132006f96018132024fe7518132004fd751813202cfc751813202cff741813201cfe7418132004fd741813202cfc741813200cfd731813202edd7318132014fd721813202eed7218132004fe7118132004fd71181323f6dc311813229eec2118132006fb401813202ef8401813202edf301813202efa30181323f6f9301813202eef201813202efa201813229ef920181321c6de63d8e513e5f671d8e5119f7751d8e51014ff7658e511c6dc6358e51187775158e51004ff7458e5101cfe7458e51004fd7458e5101cfc7458e511867f5458e510067d5458e511c6de5358e51186dd5358e51004ff7258e5100cfe7258e5100cfc7258e51024fc7158e511867f5158e511c6dc3158e51004ff7058e5102cfc7058e511867c5058e511beee62d8a513cdf671d8a5116f7751d8a5100cff7658a511beec6258a51157775158a51004ff7458a5101cfe7458a51004fd7458a5101cfc7458a51004ff7358a51014fe7358a51014fc7358a511beee5258a51156ed5258a511beee4258a51006ed4258a51024fc7158a511beec2158a51004ff7058a5102cfc7058a51004ff764ca51004fd764ca51004fc764ca510057f754ca510257c754ca51016dc634ca51005f7714ca51
  | 25 => 0x8532014fd72d853239eed72d8532006f751d8532006f451d8532006f741d8532006f641d8532006f541d8532006f441d853239ef631d853239edc31d853236ef621d853236eec21d853202cfe70d8532004fd70d8532006f765d85320077765d85320067765d8532006f665d8532006f565d8532006f465d85320077465d85320067465d8532006f764d8532006f664d8532006f564d8532006f464d853239fd673d853236fd573d853239fd653d8532007d553d853236fe672d853239fe572d853236fe642d8532007e542d853239fe732d853236fd632d853236fd432d853236fe432d853239fd730d853236fe720d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d853236ef773d853239ef673d853239ed673d853236ef573d853236ed573d853236ef473d853239ef753d853239ef653d853239ef553d853239ef453d853239ef743d853239ef643d853239ef543d853239ef443d853236ef772d853236ef672d853236ee672d853236ef572d853239ee572d853236ef472d853236ef752d853236ef652d853236ef552d853236ef452d853236ef742d853236ef642d853236ef542d853236ef442d853236ef732d853236ef632d853236ef432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f450d8532006f740d8532006f640d8532006f540d8532006f440d853239ef730d853239ef630d853239ef530d853239ef430d853236ef720d853236ef620d853236ef520d853236ef420d85321dd7e75985320057d75985320067f65985320067c6598532006f761985320057f75585321dd7c75585320067f65585320067c65585320067f65185320067c6518532006f56118532024fe7518532004fd7518532024fc7518532004ff741853201cfe7418532004fd741853201cfc741853200cfd7318532014fd721853235eee4218532006ed4218532006f75118532006f45118532006f74118532006f64118532006f54118532006f441185323bef5311853235ef5211853202cfe7018532004fd701853236df67618532006f67618532006f76518532007776518532006776518532006f66518532006f56518532006f46518532007746518532006746518532006f76418532006f66418532006f56418532006f4641853235fd7731853235fd473185323bfd65318532007d553185323bfe7721853235fe4721853235fe64218532007e542185323bfe7321853235fd6321853235fd4321853235fe432185323bfd7301853235fe72018532006f77518532006f67518532006f57518532006f47518532006f77418532006f67418532006f57418532006f47418532006f
  | 26 => 0x1de7c54d953200cff73d953200cfd73d953242e7f53d953242e7d53d9532014ff72d9532014fd72d95324167f52d95324167d52d9532004fe71d9532004fd71d95321de7f51d95321de7c51d953202cfe70d9532004fd70d95321de7f50d95321de7c50d95324057e76d95320247e76d95320067f64d95320067e64d95320067d64d95320067c64d95324175f73d95324175c73d95324176e42d95320076d42d953242f6f32d95324175e32d95324175c32d95324176c32d953242f5c31d95324176c21d953242f5f30d95324176f20d95320067f74d95320067e74d95320067d74d95320067c74d95324167f73d953242e7e73d95324167d73d95324167c73d953242e7f43d953242e7e43d953242e7d43d953242e7c43d95324167f72d95324167e72d95324167d72d95324167c72d95324167f42d95324167e42d95324167d42d95324167c42d95324167f32d95324167e32d95324167c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d953242e7f31d953242e7e31d953242e7d31d953242e7c31d95324167f21d95324167e21d95324167d21d95324167c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d953242e7f30d953242e7e30d953242e7d30d953242e7c30d95324167f20d95324167e20d95324167d20d95324167c20d9532024ff76595321de7c655953241ddf7359532425ef7259532005f77159532005f47159532414ff75595320067f7559532004ff745953201cfe7459532004fd745953201cfc745953241cff7359532006df73595321f4ff7259532006ef7259532004ff7159532006f77159532004f77159532004fc7159532006f47159532004f47159532004ff705953202cfc70595324157e76195321de7e76195324147e76195320067f64195320067e64195320067d64195320067c641953240f5e73195324075d73195324067f63195324067f62195324076e42195320076d421953240f6f32195324075e32195324075c32195324076c321953240f5c31195324076c211953240f5f30195324076f201953200ddc7654d32026dc7654d3200cdc7654d32015df7554d320175f7554d320075f6554d32026de6554d32026dc6554d321df5c6554d321df5f5454d323ff5d5454d32007cf7254d3200dde7254d3200ddc7254d321f7cc7254d32016df6254d32017cf6254d321f7ce4254d323ffcd4254d32005dc7154d321df5f5154d321f7cc2154d32005df7054d321df5c5054d321f7cf2054d320067f65d85320067c65d8532024fe75d8532004fd75d8532024fc75d8532004ff74d853201cfe74d8532004fd74d853201cfc74d853200cfd73d853236edd73d
  | 27 => 0x76198553005ef72585531f5ec7258553006f56118553014fd75185533967d7518553004ff741855301cfe7418553004fd741855301cfc74185533e67f54185530067d5418553024fd73185533e6df5318553396dc531855300cfe7218553004fd721855300cfc7218553396df32185533e67f51185533e6f55118553006f64118553006f54118553396f53118553006f72118553006f4211855302cfe7018553004fd70185533e67c5018553014fd75d81533167d75d8153004ff74d815301cfe74d8153004fd74d815301cfc74d815333e7f54d81530067d54d8153024fd73d815300cfe72d8153004fd72d815300cfc72d8153316df32d8153004fe71d8153004fd71d815333e7f51d815333efa50d815333e7c50d8153316fa30d8153006fb6098153005bf74581531fdbc7458153005ef72581531f5ec7258153005f77158153005f47158153006f96018153014fd751815302cff741815301cfe7418153004fd741815302cfc7418153024fd731815300cfe7218153004fd721815302cfc7218153004fe7118153004fd711815302efa501815344ef9501815302efa30181532e6f93018153014fe76d8d521e6de63d8d5200cfd75d8d52004ff74d8d5201cfe74d8d52004fd74d8d5201cfc74d8d521e6de53d8d52446dd53d8d52024fd72d8d5241edf32d8d52004fe71d8d52004fd71d8d521e6dc31d8d5202cfe70d8d52004fd70d8d521e6dc6358d5243def7258d52005f77158d52005f47158d5200cfd75d8552004ff74d855201cfe74d8552004fd74d855201cfc74d8552014fe73d8552004fd73d8552014fc73d8552024fd72d85523767e52d85523767c52d85523d6f651d8552006f731d8552006f431d8552376f621d855202cfe70d8552004fd70d8552006f76198552005df73585521e5dc7358552006f5611855200cfd7518552004ff741855201cfe7418552004fd741855201cfc7418552014fe7318552004fd7318552014fc7318552024fd72185523ceef5218552366ec52185523cef55118552006f73118552006f43118552366f5211855202cfe7018552004fd701855200cfd75d8152004ff74d815201cfe74d8152004fd74d815201cfc74d8152014fe73d8152004fd73d8152014fc73d8152024fd72d8152004fe71d8152004fd71d8152336fa50d81522c6fa20d8152006fb6098152006f9601815200cfd751815202cff741815201cfe7418152004fd741815202cfc7418152014fe7318152004fd731815202cfc7318152024fd72181522a67e52181522a67c5218152004fe7118152004fd711815202efa5018152436f9501815202efa20181522a6f92018152024fe76d95321de7e65d95321f4fd75d9532004ff74d953201cfe74d9532004fd74d953201cfc74d95321de7f54d95320067e54d95320067d54d9532
  | 28 => 0x2000000400601f003800801200100000000080090000000000000003801402e0020040030002000002002000a008007000800800602d8008022009001000c0380130010000024002003000000205c000800802e00c0010060002010008800401e002000802800205d00f0000002018005803000a0010008000092014005000000e00800d001802201900380680160060000020008013001805c00000b0070070002001001000400000c00700a4004019001800400600100200900080140020010000003000800c002020002807c01200901d00cc0120050010000000031003000c00202e00e803400400800180a001a00002c0000000001004001800000e000000000000600880ac01e00001100b000200c011001001001700500100000030218004004000001802800e00001a800c008002004801401000000000300040000018010002000001000000400a004000401e00000200ec0060050020090014000003802000c01000b001400400700181d004600a001800800800601c001400800300b00000220130008060006003000005800200100e006006600000180000680100008014022001001800800800200c8008012000001800000400100a000401001d0000024066002003800c000003000005c0000060000000018002003800c00600000e803000600000400340020000030004000008000004c000000001002000805400600380080000018008014000018000400a00a009800408a00a00080000060010170028000000002800400c01e0008000000000002003800800c0000010000000002801800600a001804c012002002809c00a0000050008014000000802000a0030030010002001007001c00001000a0004002002000000400602b0088094014001005008400a00000181ac03800a00d001000000200e00000000380018018006000000003402c00b000005c0040060010008024011000813c000002014000000001d0000048002000000800400601600281b4008000001000008c006000002c02000800a0000034000014806801c001000004801c024007000000201500f801000200500780100020010010000006012000000000000000cfe76d89531f6ee62d8953014fd75d8953004ff74d895301cfe74d8953004fd74d895301cfc74d8953024fd73d89531f6ee52d89531f6ee42d8953006ed42d89531f6ee32d8953004fe71d8953004fd71d89531f6ec21d895302cfe70d8953004fd70d89531f6ec20d89531f6ec6258953005f77158953005f47158953014fd75d8553004ff74d855301cfe74d8553004fd74d855301cfc74d8553024fd73d855300cfe72d8553004fd72d855300cfc72d85533eef651d8553006f641d8553006f541d85533a6f631d8553006f721d8553006f421d855302cfe70d8553004fd70d8553006f
  | 29 => 0x5800200100280040100000070000000007000800000001300000180040250030000002020001000000e016000000800000e003800000600001d003c05402600300b800000e00780780020030028000000008021000000c00a0118014000000006801c0020060270000006005002000400c00400000000060000000004002001005003801e0000080004004012008000801200000200540020000018000004002000001003e04800080400000010008000006007001800400000000080a8032002006001000000100080080000030060000000009000800404c002004800c00a006003003c008000005806400c001000000001e00900180bc004004003806401400d000000c0040030000018028000007802001000102f8090022017000800400800c004002401000800a000c00001700100140000020030004002001015000000800000980000000020038000038001006802c00400300000000100000010054000006001000c0000020028004034005000800c000001007000800600e00900500040000068010000007008007c00800f000000802000000880dc006000000801400a00600000680000030000030006001000001800000a004000000a0010040004026004000800002c014000000800c006000804000800b003808800000000080400020030070000008000000800001800000000000a4006004003000e0000068000002008000002801000900c0014010007001800800600f0040024006004001001400a00200b000807800500300bc0040060038000000008021800c0060000028030024000008001400400c0080088014000001000002200f0018060002008001800000000200d004c00000a0000030006035000000000e000003801c008000008005809c0000020044032000001002800600501000000000030020000002007017005c002001000001800e000007802000a02500a80e002e0130000008020000003000002a01c0030008014007000000000800000b002000201e0060000000011001000c03400c00000000020230000188004005000027c03200200481c804200100000180080170018014000000000003800000600080840100000018030000001008800c00201f00000000060000008000000004000801c02c00500000080020000090034008001008000002e001007005c002000009000004a001004000400001300c00580000000058010024004004001800e000000800400c00700100a802003f005003800400002a805802c007000002402a0020018014006003003000014e016000006801000d000006000e00201500a403a00602e0018002000004004c00000e015805401e000007000401200000300140000010060054028008004800401a00100f0070000007000002c01a00300081a804201000280000040
  | 30 => 0x30221c6f42540fcf33f40000000ee801480000000a391960bad00000001d3484e0000243455118a339cad200000003814a340000ff125284aa45f471d000081d3f942a138ac70b18d509a0d3867d2b2c1c033b92a5000032a34b01912518acd26d844c08440003e6c397414c1d0000000000004c215f8d06366410c00003d148fc00001acc060efc2f200006ca0000a291bb806200000db08743671878000051d074481d26112f4d3c0000000103810d3a4cf6512b8a60453c000000000014f400041ad0960354000072424101a40e42574268413cec71929034117c27502bc01902e4bfe0000f7b054800001b000c00400e0030020002002000001400601000000040120040000078000004002001c000005000003001c004000802c06403c00100bc03c0040008018022000001000407c00001c0004020000000801c05a000001000402600001c800401200a0008060010001007001001c0000090018006002003800c0300030018020004001002802800200600e0004004002000000c00000200000d400000d001800c0180060010008020003001004803a00400900cc01400b000800c00802d00a80280060060010020000033000008400200f00300040540010000054002008003000c000030001006400c0000000070000004000002c0180480030024002000004001c000003011803000c000005000c002003000803800000300180a0000000005800c00c000000000c02e0010000038002001000000001203f000000000200c007805c000005002000400000200000040140020000084006000008000c0020000060004004000000000001a018016000806200f0010004018001000000000c0010040008012014000002401c000000000800003e00d000001000000180040040060008010006057002001c00a0010020024006001001000c0020040000024002001000000000c04500000140180000098008008022001000400002a000800c03200a004801000a002008800000c0010040000002018005000c0080040000000022003000001801200d0010010004001000002804a0020000000002000000800405a003000000400c0000030020000000000801400400d00080040000170040060006000000807401201b00000080040030028018000000000011000a0040008020006000015001400e002000001000200500100300000020038004008000000802000205700100ec002000001802c00a00300480000100350060000004006009009c000012008000c0260000070000054008011000005200b003803c008016001002c0020000000014042014001800c00c0070098098014000013800800000d00200040080200070048002002000001c000001002000000200800a80780000040000018024009002800c002009001002c00a0130000
  | 31 => 0x1e490f00000000000007840d44431ebc00033d80000000000384c3941eec9ef3bc08bf3bb12762aa92a433788f41ca82b10d7c0951bc464b1e1420c00003db32303f5280c9780484a9c3044feb1afc57c49f0cae000054727940000000137111c00034a053817a51a607187b422300000824d7f43d44d1118ce53035c81310d9274146ccfb000049a2bdc512000025d467115a0e34e4e373903d44680004aa40002b5d2c03624c4e123cbab2264f3b2ef000000d419726012a800008e73d89279000c33e00000000000000493400011e92360000e5100011ab488000000011fc1578390470885409f92893244f32172d02741c4e3f0c78b2e27b0f7f2a6421c000080400000003e7014938491d007a0ff436081b91c3448b13140000000d044ac400e18d02de483c0004814a383e087820be01710000c151824b9808b8000274cc3f00000001f6400000001fc1fb87b50000000359c000165031244990240d54cb9373c6b435c027022c40bc26487f8112c5853a7022443282ad3a08e2e12408d61df4306318c54a1eb426542e0fb83c98b0616f89d416e4aab447c1181808ec434dce7129549902dcc28e03949963188328116c24a2314f7734c05dc47f4abd3e90c9344a8fad3df0000342509311d054335302cc310c00020e0fae48310193ab8ecf2cdc71735f8f1a1058cf1134c18a3c7cf031f0c4773fc8c3000008280000ded3f50522000000000004192fdc9f416c4000000066700003d41434c3c42340001114000174526946e906130e41be02890b02eb08cc184c0000000e691ab000021ac76c236400029985e61c884791350b3116a412f4868b671c0c2153a609bd42b853e187126808cc89340202e03ac85c4158c6e31df80dc275463d42cc14a2f8885e0a012bf317cf27467cf830574000380105131585c11c047de1d2400011f0f3f149d26e000042130d022d0228b66465106538ec0302488d2e33851a10a9000005900b20e88b8c0000000000019e48444c937e06184614000154400033c86db000000000000003ec40002304a410000000351839600001d80000e6740b40632f00b5d3b98b7911c8a850000748000095c3ae0949228908508d8ad12584fef1dbc7644ae919230bcbfc20a8ea30001116012cb200ccce7601688140000ede0bb86f8000000016bc4d02fc8ff625a4000187c0002b945453fe083100000003ab465a121ccc53674d9c2d6807a450cdbf2c581320000cd8339000020c02931e7c0000000fc332a405e47500000000a4305e43b606f02ce0000047309400000004cc1470282000007c36d40000000b300fd08973950e422d3524042d8dbe1fec86f0aa486722e877a21e472c4820d611eb0b4514a4d1b28d831f28b00671dc9250277cdb13820061102d22c43943c90de909026a016f0000e6e00003
  | 32 => 0xf30000039a1e4d1770000fd019cc78a000081614bca8a2f0458a2ca4b6b1248a702f9910943b496b2e48d573aac8863ea8031168862b094909f0048d3a3f387cc45c12060ca48de13b8c580da00003a905ff00000002b245c2431c00001351e4000000000008840000000000036041b80003f050542a68dbb394800003dc0001108a44473c000000000017a00002e051100db052c3acc94106984bc48349e10000e220000fe2438467e4a40dc341c0b120df10be1b04bbf2c407b3432c77725809ce4768f5046049a52f2cbc20ffced6314484a150859b2198dc61fd09421e1cf723d146d11068f4d05a4ceb0f0898e366d12d08c035a0d44dd92e7482915a907e2438e1908484671c8d0ac3d5439c4414f233c70c5703a04373f6881f02d04e528bc5794a7026d0ae033935d4fec2ce0226236907d4908540186d01d0c2062d17c4c1c0818d5027747680f2cb542d209f101b843e372400005703b40000908477425a4978d143fe86f7065013e10b4f58000064c42ecd7113cd1c90f6052032786ea396c33137b8718270cd010000bfa3c74e3729d08060a1021714902760fb4cc13850c4b2b6d164436010343f80000120ff02dc901b0360e960000000000000023c80000000000321800022e45800000a6b07d07100000000000000000001e530f87783c900000000f46106029200000003428000017c1201af0b8519986382a5c7d50c708e84a1c3fd00001f94a2cff739d047d20e46af000000004643251fdd1303d4836309ec632217129529900002240f3e4a583aa33b0ae601940002894f5e4480874276c000300800047b4000028d15e000000000010d03a5cffe000000041fc000480c24c0000000173400001f88b81cbc83f28e80001428cbf4788db918cc82708bc54433706633470af005e0d6e1d1800010d0000000000000000001e64c7a000010932f0b193098d6804f41bd0c6000032dcdae00004011274b22000008c352ce9b36782ed0d0411f058853a3c08eac3bd8c353e8432001d0000189458d0d3c00048d517c0000000000067a197800034d800032544e0179c000426c0003d28bdc27c082d2080b173bf000001708a119acf061f18a54125126542a0731443121949140002b3cedd42e824f47e516e24cc0003a88000000071b456cd813ba8de13b645870cdc00037545f818b807d0ee0b0c08f91180e812bb3e38cff4308000303082c2960b8d03c8000412ca9422590202f54dfa3d0856e1ccd12b1cd89c0449d05043700fa47e0b68389d0e71d5c85932ac78e37b07e23c1479d00005ad0000000252d1831110d8737612630000b0e1bbc0000f88d5d3e7437247ec77f0000985492cd181da4d3d05f474a25001a91cf50073a208f30000cc939dcb4322b009b0f0000035c8d492d190563abc1b72c6881142dc50726c444e0
  | 33 => 0x1b248220ed49a91834c6145480003d8c00940e85503b548d4000014449510a90568853008c5684a881dc2b683f02840f2b08fc81b3cd06a5477c80537804f710e45db3c840000000a3f1f748824a2925f2d6cb8035e065037bc34828b45c6470c70034ecb8647d02dd000055b0000f4000000002b4000045ac0004068000000041300005bd110043305b00001c5098f067000005a90f81f1c17e01301e02a6000003fc8b200004f1385889d00bc00041a8015233c5e20dccebf1148e3800001c80d0c00004d4ccb1d800b141e52bc04f00001ac474b438ca89000000000000004a5c4c331188362698bf9000010700008781ae4000000111d0000f5400000003b24000000104c06b80003d2c27c266c3700000b69180d057011059e3694d5b0e7c48040548dd13d0cd40b00cd146b86d50b106e9355869932d47411a80fb24a146b71de42e344d0f6611bd234371c2a34400fd81fe8c093290ba40f5d11333cc6981e30506196c2ab17bcfbf072c9142d251a43320684128c49f000000047b80002e54358448832e3778ced492050400002a83db043d1a6c15b011803c2b9c0ab0000bf10a50fb34800000000000028700000000e2f474435945c910e0a80765390c3343174c4d187433a1fb0eb631703ab44f09974b0497229306a92cb02d5000084b2780d8e21240973128c77083c2e416b8a5900000000000b8322a46594798c2b2c1cfa83f1442e296c0241a04a2a2b709a33f7c62a15e87522618bc333640ad1974a5c12e800047a8000000044a1e34fcd274504e4961277223916c04706d949c01c429b00a63cf400000012b91dac0001fbcf25327c273020129f39350b5000054611fc0b62ba0ed12d008ca3874b1c1e200000328c8d0f3c93700005fc31ac55400011123a38ce038543a32bf89b33a140d044c455f0b14a370000e1e3968a0420850674310d39389014d41a0f992d300000d08dcc25c46fe061400000e8000062c000198800031d0dd238d8a79100cd9f2a9c70614dc0fc18fcef90f7c92f07051952af921f377086a407903b186464300000001234000000006c0bd429e00000b829211e31ca02d64964344000087024083e42a3522204d013a0000fdb1608b580000af100003bd260c0004a0810a0b64dab0000efb0c1090f0b98218264c0f5091cdf9000088007540000001284000086e26902c23548e5d13f92553d700002ee40001f005593d241653e1400009341cd2c50000044102202480003c2920a000040f0c3ca3d13c12514a8c000249d05e1fc048814440501c14e3944944c100006f21ad4f0e00010eb3c600001b1c6690aa9232067c4560040c143f90f8f0dbd2a14a9cabb25b102302a0b7b011408226889f700011441b0c9563a18ee412a4d0326206ab2f111b4063d1c44adc0004b38af80e3113206400003148
  | 34 => 0x4fbc0ae88dc32b4cbe11608e435d876739cc3c71d8cba301284b01454e89131c2e718582870000b6f27f06d044784c0169c4081a347c807fd0992a780000e9c00f1f04bcc31792cf298cde5129522307b4d4e095c2d1000012645e893f1a5c000433400031e02284248cd71fe400023c4d1732e081717acb4f437cef239c869116ec22101cc00000000001390000211800021140000000000234472e48ec00042fc00048749f248ac0000098c1f3f780000000c4718f1184202912f21946e712fcbdf024057701c438f15c40002a441330c9c7c500009f81270d051be90e6000000026a8ae929380844660d4a22d0f41434c00024911a342041b2173051707c423a0f11135224913e023cf073458b570fb0b1800000003ed8d84166000005c8f9400011e10ded1583ead15c000000037a000007b000000a05ab0260ec517383f340081a3000000000000000000000368cda91c110d7000000016a09e200008fe32380000d3077c1288c7d23b91ec2a580003de417b3bdc9e92e285fe1bb40000dc522e2748000000000000000000000000000000000000001edc00000000000000b3c05ad0e40000000209881c08040000000ea70ba8c6d1f809123be8cf014fcc311ea908c10750d61290b471668000000089c00000000924d8a2f9048249d41ca389473e3edc92000001f617e83053aa0c7b1018cf5348c2b5191478b40244092bd825401dc1131e3c98100003644038227265064f1c0885628cc5261e9857322dc6a63ad4c1926b8059000000703180001d5468c0000c8a000062226c0b742c90cb2216c80e1d14c080000000167400000009d00910000000070a000039d2eec6df282c388219000000000000000bc8331000049244be19b8c650000eba00005161260d1a00008032590000445c0961310c763dc4ee11db889e34b46f30f28ba637f42eb0554e0c2dc000010807a341b0f67000000000010d12a385c045049454a60c594a6d07a00000000000c00469504322b4000281c52e4a982692fd00721d10000267800000000004b2800000000ef00012170000ce300011d703a8000137ce3a34780003b509110d702ac2e88000000000040cc1b400011452644e5f20b865448610142c85189000113816fc5ee249893046300001aa923a4368adf3c247ae48a891d20640003e68a6f000000017a8000114450f43dcca83a00b1d395429d030c2810d74832229c90c1c702b00d188c3392491f13e84da42ac6a400000002f24e1a38f508e33dd0f60ad8584229000007451e71908bd30620c0733a00003090e2a14d4000049000037203bc0000000000029000007d435347070becde3000097946b4d324298d3f23bc00035b400003ad13637150d400000001d0800041806411d0d00c0000a243204d33306800027fcebe38b11ac19f0bb212386fb
  | 35 => 0x2f4057f19dc3650868daa484c4e62790b4b454122f0f0d1f3119809a1ef84601f24a5a43804251f9c7d34410f760e6c3cd26289c60520e4f39207892cb4b411b5c9ea17ccfc636cd2c711ecdf622200000c986da000000027cc16d3ec02421c4c0003ac057b399800000005b60940f9f17612bd375020203249c535900ec1bf44ca3c2c29749f90e84720e0e47043110c003b906fc0000000a3b000031b323cc750cac0000000739459499d2ad12730000e7f0000b6221808fb000000041045622068000000000029dc000000062826d46e0271d1b21d64d122d8cc5b2f840001fc4aa4218873f004c8333688b2a02380002ee09151850d5a0000d0c3ed05a313a85d431980872a88e232914f442a2108614788713dbca6d23d4df2113d0880b4001a0400ec00b1cbcd210ca311dc402107d402a1bc069502b90f324100002418809244ca3500006e21b9400018900681840fb916300003c79084300cf920b500002e50b5900001b10000abf36dcce642541363e8084718dc9fb3c486882fcc50c000001b1a9c86846cca5631c06f9000124746a4eb922980002c0004f2b8d1b72ed8e402f1d0972a1cf160e490ee042cb771f7cedf2ab905a45a81600000d8c287814e253c1840000e0a3d207b206a84d222bce040000ca1365c6823adc824429d0ff49b4ffc2d80caf3dc092331a0a7e3e4c8550b4cf8719a82f101d83174274aa1328c95520ac86c3a40a534a18d2b3a30042101000042601ce1e88fe123480000000f0122f454d47606e44858ddf299c7e53fa09172c1000014ac0000f70f560001168137400032ecc820a447093e5ca652e9c3d515949a10be43f928f914e254cc9408284a000f800020dd04422cce5c11792393f58604448cc2823000000000ac0097903c00003350000d0f303c00042f4fd70018dfb19388730000000060c3b040b92380e1819800009a032584b224c43933ee872122f88ab2770d530d40000321447300000002868fcc291c7843e5918e213d2010cf400045740002f60c53000022246fc66f043d1590000b3b07a4e8b10490b949984fb10a0a52133c9c107bc000310030d0000a221e40000164440a077c92927ad0f2155493406e09570e1c0d9201cc6033e8bd435a400003f442c35ad2aa2fb088b06005b30880a7300b0900246037e2cac1fd336c3e0278d16041081770000caa000000035b000012c40000c405d600000004244000000000046a0898461c16700000002f18fdc000079b2db4bde486c5e300003470000000000000033f800039e000000009d80e2cb9f1ff4fdd3b48f310000b282cc8f682c9c0d2289c2bb1f58e4b23e01c20000000000105812d83c80000fea1fd80001b70f841a247fe08b0f3824f11fa06b405440104002ef8e26137838a1bac60c0500f6b2b7442234c471f29e89c815a
  | 36 => 0x6480225680f82c6ca71444415113d83e8000079e000000014146e6153ccca05d41153a34a8b00006ae1efc00037a80002a40bb439041c712791f00750c170000000448443f30480001d74c0a01591cd17f4d510fa4905455902a11c50212f9c9e82b19063000012244544ac46d897d2d44b1e1034c130000ab80f78c4215d067b417cab00779196495ce314ad91370c4d24e46890752b10b650cbd2330af11ff331d1482dd46613340fc732d812c165c66d06bc50300007ab454cf041040ecc29d91d30630000154d25328ac28c00009ca1b0892b2b280bb1224aea0f14eeb3b3400012e4aac4970589261ca090e6122d0abcff51f5c46d0000000057d00d004474045c4f6d2f6c1c30c2c89a0ad03a9022123d177cd10349064820ed28c2facddd05c00000ac8d413fa4e0900948aa20e8c971fccbdd37281d7162ca02000081e330800040140000000cb311ac1460000a50430d1331aed0cc49b07763dcc68e2fd91730bccf3c2c2800030e8f1b0000000016c0001cc800030100001cdccb137d48630b288c93f08ebd0000a0e049cf143ed438211a45dd231c40c18d80292c2037806d46a8369cd5f0dd000012ac92e0f64a230ce12670000e700680d112899107000031d479463900000e7362c3792c941b0000123727782d731cc4243b680003b8c55c4894bb7000058100000000000eff0000000000000000002664004596368400037ccf8a00008f901d40001db46ce0b94000000050e1f2c0000001163419015600000000000cce08c8be3472c96a00009ab046c000387124a0b6c68548c4ae40000a063c347d82ad8000180060609e8000183887d000070f36a0c7939601430000ce24060b0542252813598c4128203094b200000000f8c1c9075a0000fa3242446a4b08531000045a10084c809f4e6d4b2cff31b34f5349ace10052c6a1197c200109c9c93f8cb6100010ea32884143e44efe3dd110d442121c14012b01c803d3257d2be3554c2c2f3c8ea253400a0b608890ba42850398c553ea40000000bee23dc3e74918aef3988ad6055d1f200006c526b40003f480000000a7c000048c455c00041240001e00a212c442a700000180000000285cdbd4a68e0d24411b91bb0bf0223cd0d084d02c4730c7f3b21214457d18b4098dff47d8ce9312085143e8d351174b341150c88298504607651e00a6cb96453403800c893a0000d7402140de0000000135d13a26b06c80cc84e81e9c1ee0fdc78616c85e4003516d4320a46292874708e443509ad08a166458e3cb00000e04000391431a1b3046200011be000027700004d546c01e12c7ce1b4544e5908d104049ecef53be0de60234ed32544cdd330ccfc1504a6225e834b481090d2fb442322a067939a83953a1d167053c3852ef50e245244f5000097328c06b834085860000db427d4db
  | 37 => 0xc9033ce4408a8570237c00000cd29200001e42234aad000000019c80000a0cfcb40e0000000036a2a4c0000c90d86347c1a200000001994c9803c402219010a525b42634ab4099142436e07e00582cbcc1d4640e332280ccc285109404b878114f11620af89b426e874e293c68f2104f5a3e604c636e921204147d113b4af93c4cf883a7d0bc321084c41886213fb525a2de0bb3139c88a07acde92a802ef3a280d628a092a00000004ad443c2ccc0c710981042de83d23a54cf422d927f14406110000e9d1e84ecb2f3895414949bc00012780000000421c4641f080e200001a70a98f8b16b0000000038319d4a0c2060a6916c0bca000110200007ff0bf000041bcc9b4314000267123e00000000000000000051d11f8572303830a0000000000000000000000000c6f045c0000000f5f2c0400000000000000000010d10f3a8000000008bb217441734d08502310e323b80ac237c0000000077b3aed1c63e342b70f180000000128000000031500002acc0000000d581b781d6000013833bc18e29f434911250121fa10c126dc431081c0003db801c22f071210c0362000000026545390000815372c0001c680000000f00096c8950f5879c0000e632a7480125ec0000000bd618bc730120427f2be8ca525f926a0654f2800b400013f43fe04189a704a8dad321c37f40191420b34c2221846902b041394338ffb0000e4600007e90180c05000026a35941e636b0a4045d4936412893525d0a320000a05158498b35dc81238f0e0f26692091464240286092c16e918f349d19e2bb080b2d54a124290000463468307480003d90f2d2e948e5365809f1fb4b0f1ee48a3000070e000000007e8f4c1a6800000fcc83000000015bcdd10000513142d07b171c123375833f21f92c404ece5040d8000363c9070351072031454819a01810564e603b4107818b029842d065c054c3761e683e3087cd902510ab20000b8e10ac8e04378a492934d834b0c315194c94700005754ab8b522d702e147d4f5b38f88d31a8c295073c0bd43640f33b9c9680c8421913bc68039f4e5e148c2510ef89fd0ae4c7e21689591dd45f620d06562730ad9422c3ac3b08c503ffd2cc00005563cccb0d2764ab12bd0f0f0e848402798d4f0ee800032001dd0000cac2e410d20fbc6083ca4c9a000523034386314898c372c549c21fac4410514446246511c3ef836b1e90aa53510ad3351cde7147cd3e24ec34d3a94361005c36909bc72731305343881176319c6f50fe846c08c406448400d131b069d357836d000108213345a63f280cc032026e238c5210000ba8286cb9b17401f226bd00b0bdc8100050c490294bda43f4d2012280c232c0aa84a508ed215c71e0000b87233800000005490000b3522d412b09904931370fa7416d10b2ce4a15189cc9c366000030c8c7111
  | 38 => 0x5fc00000006150000cd500000004b1800000000003c889fa000059347644ce0df41922ff4d85172000038a0a8f1014f9e0e009d70838a7f036834a272c12d3e98dda26e010117ec2ae00010c61e807da3bbc0d3232c716000109c1f48a8c292cae147a4e6c3d0d24f29446c417c069f44a49164a0cb9e3de800807cc967078c3e103c0a75297459214a85b4099cfd502803b333a84b503810450274fe027b833647381161fc86cf0b3c62618ec7bd4a2008909c900a2df90251d3c35307dcad523e81ac2ee8e35381c15e1d9856024a02f00a2083c36f0ec3358c19d3a48c99437525d2e8045017788fd31b91f111346050bf40b32e5d0172db10f145e41ab43d006a12dcb7f44b8bea400c3ae0bb076221484fc3d452ac31151472b604d649584652c086ba47f88482bd46782e844ec34744ff08e00a9022c87f31a4b880bfc63e2a8c5782a491a718e85082bc86d301eccd63061291136c726037d28f49480373b6c00c43011aa27e50280f75103159817609191de37d039125d82a50010fc831a829622040f42908fa2365100015486711388da42a1820b1af47bc0000d93489c00033e454c15d8783412026107144b417dcbe805cc96e239890a3af025f4200e302ae8d400b88cbd0768a81420c7b021dcc271a70be9404512819191c726f819914c00270584b89000000011551bb0f400c034640b743ed16131680000000000000029a0000f602eb8340221517e0ff0f2f20bc5b5287cabc00000003cd8d6039e800034a400007a8b761408e4a05406dd126c664168066000000000000b360000000417400046c4000000000000002101e600000e945c5284d2cd1f8425500d05d229ec1b6159c1fe2b1cc9d45a41bb014cdc21d6cfe70008158235d14a235430e1ce80003110b3a26600000000c0112cc00020351390000bb021a510111840002cf51db29a8a190000872267c8d8000000000000000000afc00000000f041a528811784ad0274000000035a829c000126f0b0c00017e4f37236d1b80000e9a132c9631f90a573704d792e45229217c60f24702033c8103e43a47110000cf839f0fe60000ec11a2c3ad3bb4deb379057d1cecb5f02a800023211b51b844831e440002c2c32c2b380003c44a8015acaff423ce810be832341985ed3884e0b46747cd4668f69475831627d85c9175400042bc87b00009fe00003af2fec4113b940000000e030000e841d4cacc28580ee44f4f78081501f02fc4a818a40834154aee1f281930920d42428514b226c00509649893d1c9010530b561f6c41b1804e9410c800b173c438411c6933f10cba3a3d17445185950074036407000007302c848787f532d0ca704c4d131bfc8cd000042a2a550ef0000f61000000030e0d4303b4528000096221112c500002292f94ef14a3491a3ce800000007cf47acf
  | 39 => 0x10a470c2578000000000000002623b70e643df8725000029f40ac9d60820ba92c0c8b019c025c1a18049000041c0000564391c61200010131620453000045700010f90000e65000062008790fc0af400000008583eb060b000009c34bc33c13a40000658649152c35b00000000000607125cae2007800009b095b499011122b8baf04211af0000d9a03f83221404dd70958d5902e8c7c0000eee00f416e083519723180001684647000083e0000ef40000b8447bc00000007a812541e739f85a41e50000240c0660000ee20b68ffd0000e790000b501120142000000001fc6550000a1d00005d333001a117c8c1b3b60ea600001fb3078f4e242c617188caed12140f600006d21f70c8b00002711868bd749e880f39ece06000087c0000000404128e3ebd244000038900005a53f6453318c06d6282897048a0e910dd423b027909e045000012e0b2614601ba0000fee0468f0c0a245d907c0687209400000011820001272416493e00010c91b50ca04aac55a1c551883c6451a02d50292db80002b500161ce0dcd0174dc411a0fd14418e832f6506d0244e1f10e8d8d30a428b1c2017c24788e10edd1dc3d3cca613acfbb1ab475c00001871dd05e139bcf90129830129b86f64134982276901600012240d78dc000000000e78a68091400000011190a644994a78d92000000049046942f48ac524e43f13e940000fad1ca03752994ac82c90d504f90000bef138404e02842c6374096f3ca8ab50000000482c081000114c3bf40cb00000002f4400040dc03900000002e6864400011d50000cc600000000000b9c0000d910000f2e496cade4ae00551d604ad085094304083fb1a883a414ec0ce1670657175cdfe09e40be0b2cd451ea517f0788f3924b47d01ac87ea0c0ca0d4a009ed3454d9539589b20f98e4c0acc17f23b107308f43f2342c4d9155c5f428f0d7308ac91b00b819b446d2d02a0c9521170a0046f05900bf803b44280c42530a8438606763e24a9f2e2c27800009cd098100f4838130333416628b8f7d0e983573ba43cc3e18d8049300cd0fb87e313c8e173b190d51d5105212100a427106be1244bb140bc33b47dc1742cfceca000096615b0000208c0001538aa917b0d6f38d00000000d2230340001ad91bd00000002a6c00000001a431c8c2d06cc00023d80002adc72b2a0846e20210392ed431900005142664d213d5d13f1218b4225d4d25163c7ba39840000fd8ac33400f6a459892530d842f23085e0000119142a880012bc83d4b24d0846810b1094cb3e37dc15408d45b800012b304482df0a18b5345bcbaa35e876121d40003d6469200010ec000000040fc000000000021d898d000000037f103021e847530842042b200a7000018900008ff0ec489124c867446000c11cf0ccf000065144ed26204a435200002582
  | 40 => 0x466c98c41d8aeb00006b30000b934280e571d40d7d0b700e328048f016f075f1da800001b455839ac125283cd5449c4735058c68a1f38b13000000036e066c21b4bff015c7971574de219fc000322503200004a7000000030b89480c0860a06091c00000cdf48540003b38ae0007c3841b2c377297ccd30000f752bf400000000000894bf50c306c012840002a980004490d3814d86b001bc7192f140e1024c80c101c89f00000003844e68092c88348f0b820a345ca0e38e012d290770938a5e3a782c12c8cab901c0000308c3560618e9935700000000f5d00000001f112430000a112388fbd000000010ec5e53f4d1400000d7c000127d000000048088eb0000020107cc16000000036bd07c3aa48353f009e71e5893835ecf8125380002108b7c11e0f104abcbf800004bb1d310b234991550afc93d3620b7d1ec42f438b4079076c5aa13605f51d44b5e15b45da42880403cd4afb04fc58326e4773000023c1dc0af319492a041700000d14f8000010cf0a3c0000000e0232406961b19031125847602c03bb1cd12210474c4f35892930b4847000ad1863248f1544505c300006d80a28ff93aa8e7514b4b440d983e52560c2a34a8ce513e08d030ec0000ea0b8f0668000088c14100010ad0250237229526000001d30fe097c374cdb61a780860104eb11ee03ea1e94b7102b0ea13bcc0003c5c7b63ad0e292f807fc31903141d78da64748cda37c4c0b47a084d1cb4b6a00001a81e54c3d2594b0944b0c3326fcaaf273c00029c8c101ba08fc0c1c3ce36809bb05e82f61d580e901445b7341ced736c84e31bf07292d90ddb4a7459f1078a7845ec2e825dd199063421603e49841f98cd214c82a2436c32d03ecb99086c3b23c210a32d3810e3080921193441500011c504783da2250f950000d4805a039923a519341a4
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5f739cd65040014df04b9aca080029b20973594100053a40ae6b28200087e8710d65040010fb0e21aca080029ba08435941000536c1086b282000a3e841c9650400147b08392ca0800297a0c72594100052ec18e4b28200087e87d0965040010fb0fa12ca080029de0542594100053a40a84b28200987e87d0565040010fb0fa0aca0800297a0f41594100052ec1e82b282000a6e82d0565040014db05a0aca080029ba0b315941000536c1662b28200087e870c565040010fb0e18aca0800297a0f21594100052ec1e42b282000a3e84085650400147b0810aca080169ea0021594100053cc0042b28200987e87cc165040010fb0f982ca080028fa1320594100051ec2640b2820058dc8750d63040011df04bb2a6080063b2097654c1002c3e43acaa982000c7565dc553040011eb0c38aa6080031d5947154c100047a40ae8b1020058ec87509620400b0f90bbb2a4080161f21d65548100243e42eec990200087f855d932040090f90abb264081b63de05764c8100043ec36ea990200087e8759532040010f90eb2a64080163721d634c81002c7643ac49902000c7665dc532040018eacbb8a64080023d618714c8100063b328e29902000c75651c532040ef9acc638a64080033558c714c81035e73310e29902004a778159651040018f2cab84a208003171cd655441000636392caa882033c5e65dcd51040018bacbb9aa2080b71b997725441000636b2ee4a882005cda7058e3104001ca862b2a62080021fe1975884103743fc3acb108203487d87596210400b1df0eb1442080030f1d1654c0100061f32ee89802000c3d65dd130040310fb0dbaa40080021fa1d654801004c3e43aca9002005e7210597100400b8eae0b2e20080121f217764401007c3ec36ea880200087e8759510040130f90eb2a20080030f1d165440100062e39aca8802000c6c72595100400187ccbba220080030f59774440100062f32ee68802000c5d65dcd10040018dccbb9220080031b59772440100065a3a6ec8802000c7785dd910040018e90bbb220080173c94376440100063bbb6ea8802000c77761d510040014ed0eb2a20080029d21d65440100071a3a2ca8802005c7770595100400196eedba220080038d59774440100066bbb6e68802000e5565dcd10040019aeec39a2008003551d473440100072ab28e68802000ce776dc91004001ccacbb92200800339dd8724401000732b28e48802000da4741c91004001b88e639220080033cdd950440100065c3a6ec8802000c7b85dd910040018f10bbb220080031eddb75440100063dbb0ea8802000d38741d510040018f6ed32a20080031edd965440100065dbb6e88802000cdb76dcd10040019b6ec39a20080033addb724401000675bb0e48802000e716598510040019e6ed28a20080033cdd95144010
  | 1 => 0xcedb2ca2880038d19764945100072a32ec728a2000cd67618e5144001ca8ca31ca28800399197629451000732328c528a2000ea46418a5144001d88c6314a288003171cf655451000636396caa8a2000c9c73d915144001958e5b22a28800237a1b73545100062fb2ee6a8a2033c5c65dcd514400193ec9b9aa28800327193735451000666316e6a8a207c8de87d8d51440671b90fb1aa288003331cb635451000477436e4a8a2000c6f65dc9514405b8d8cbb92a2880032bd93725451000656326e4a8a2000ccf63dc95144001998c7b92a2881e63ba1f625451016c7643ec4a8a2000ccf73d895144001998e7b12a2880032e19370545100063db28e0a8a2000cb8641c151440098e8edbaaa28803f1d1db65545100065a3b6c8a8a2033cd476dcd51440f99a8ec39aa288003351db63545100066a3b0c6a8a2000e546518d51440014e90ca9aa2880131d1d9535451016e723b6e4a8a2079ce4761c95144001b88e6392a288003391db6254510006723b0c4a8a2000ea4641895144001d88c6312a2880035cdd470545100066db18e098a202d87c865d62144001878c8bac42880031718d75885101a636312eb10a200087f87d96214401f0fb0fb2c42880030f9d764885100061ebaec910a2000c5e75d8e21440018baebb1c42880031b9d7628851000636baec510a2000ceb621c1214401f4f301b2ca0880038ed4364941100072da86c72822015c767694650440018eecbb8aa0880033518f71541100063bb28e2a822000cd4631c5504400b4e90ca8aa088016dc20151541100061e3a6ca98220008be86dd1304400187ecbba260880030f197744c1103064e31ee89822000cac62dd130440c317d0fb2260881822f21f644c1100064fba6c69822000c9c74d8d304400195ee9b1260880032b1d3624c1100063a32ee29822000ce462dc530440012eb0a38a60880031d194714c1100066bb18e29822000ce4621c530440010fd0dbaa40880030f19375481100062e31eea9022025c6c62dd520440a90fd0fb2a40880961f21f65481100061fbaec89022000c3c75d9120440018beebb1a4088003171d7634811000637baec49022000c6c75d892044001968c9b8a40880033518f71481100065a320e29022000cd4631c520440019cec438a40880038e19065c411007e3b3b6cb0822004c7676196104401d96cedb242088037359db63841100166b3b0c70822000e546518e10440199ccedb142088007399d8628411000752320c50822000ec46318a1044001ce6cbb0420880163e201745941002c3f43ca8b282000c3f7495165040014dd052a2ca080029b60a545941002c3e43aa8b28200587e8794d65040018bee729aca080161fa1e52594100061fba4e8b282000a6e829d165040014db053a2ca080029ee01745941002d3c402e8b282000
  | 2 => 0x373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6f75dc962440018d8ebb92c4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880032d1d371589100066a39ee2b122000c6e76d9462440011db0f328c4880029ba16651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000a6e8619462440018dcec328c488003996046518910006573b6c83122000e2f65d906244001c58cbb20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc8359062440015cf02b20c488002aba186418910006573b0c83122000e2f651906244001c58ca320c488003a96046418910006673b6c63122000e4f65d8c6244001c98cbb18c488003a3d93631891000746326c631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c624400159d07318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab211631891000567430c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c62440015cd0d208c488003a919241189100076231c823122000ae4865046244001d48c8a08c488003b118d411891001c5f426eca9220008bd84dd952440051bd07bb2a4880023760f76549100043fc2aeca9220008bf845d9524400717908bb2a48800237e0d76549100146e41aeca9220008ef825d952440030fd0fb2aa4880123ba1f62549100243f42eec992200087d85dd9324400717d09bb264880022f613764c9100243f42cec992200087d859d932440010ff0abb264880121f215764c9100045fc22ec99220038bc845d932440011bf06bb264880023be09764c9100047bc0aec992200487c851d932440d71e9023b264880021fa1b754c9100061e326ea9922085c5c63dd532441058d8c5baa64880021fa1f654c9100043e43eca9922000c3f75d913244001878ebb22648800637a1f634c9100062fbaec69922000c5c75d8d32440051dd0fb1264880031bdd7624c910006363aec499220058f686dc532440018eecbb8a64880031d197714c9100065bb26e29922000cb464dc532440e79a8c7b8a648800339d8b714c91036e72316e29922000c77651c532440018e8ca38a64880032dd90714c9100065a320e29922000cd7631c532440ef9a8c638a648800339d88714c91035e72310e2992200fa7581d965144001c6ea3b24a28800395d47639451000733a8ec528a2004a7686d9651440018e
  | 3 => 0xbb122000aad84997624400159d0732ec488002b360e65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000732c08cbb122000e2f65d936244001c58cbb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000ea5811936244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001d48c920ec488002aba1275d891000556c24ebb122000ace839d7624400159b073aec488002b9a0475d891000572c08ebb122000a6e851d362440014db0a3a6c488002b9a0474d891000572c08e9b1220008ee8795362440011db0f2a6c4880038bd5254d89100053742ee7b122000a6d85dcf62440015cb03b9ec48800393d4e53d89100047743887b1220008ed8710f62440014dd0a21ec4880029b61443d891000567c1ae3b122000acc835c762440011dd0fa0ec4880023b61f41d89100053742e83b122000a6d85d07624400159d07a0ec488002b360f41d89100047743e63b1220008ed87cc762440014dd0a18ec4880029b61431d89100053742ee1b122000a6d85dc3624400155f08b86c488002ab21170d891000573408a1b1220008ee8710362440191db0e206c4880029ba1440d891000536c2881b122000ace83103624400159b06206c488002b9a0440d891000572c0881b122000a6e85cc362440014db0b986c4880023ba1c30d891006476c3861b122000c6c62dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc655891001c5f436e8b122000c3f65dd16244001878cbba2c4880032b18b74589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac48800327193735891000666316e6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac4880121fa1f755891001c5f43ee8b122000c3f75dd16244001878ebba2c4880021fe1574589100243e42ae8b1220008df835d162440051b906ba2c4880023be0974589100047bc0ae8b1220008be871d1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd
  | 4 => 0x3440011bb0fa0ec68800297a1741d8d100052ec2e83b1a2000ace82d07634400159b05a0ec68800237a1f21d8d100046ec3e43b1a2000a9e84087634400153b0810ec688002a7a1370d8d100054ec26e1b1a2000a5f855c363440014b90ab86c688002b5a0450d8d100046f43881b1a200d8dd8710363440014bd0a206c6880029761440d8d100056741081b1a2000acd8210363440015ad02206c688002b560440d8d100054f42641b1a2000a9d84c8363440011bd0e106c6880363761c20d8d100062e31eeab1a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c9c63dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc96344001998c7b92c6880121fa1f7558d1001c5f43ee8b1a2000c3f75dd16344001878ebba2c6880021fe157458d100243e42ae8b1a20008df835d163440011df04ba2c6880063b2097458d100045f438e8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880063ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440018e8ebb8ac688003391cb7158d100062f3b6ca31a20008dd8799463440014bd0b328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100052f430ca31a2000c5e761946344001cab02328c688003279db6418d100070fb2ec831a2000e1c65d9063440011bb0f320c68800297a166418d100052ec2cc831a2000a9e84990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000a9e86190634400193cec320c68800387d946418d100070e328c831a2000e958119063440014bd0b310c688002976166218d100054f424c431a2000a9d849886344001ca8cb208c688003a51924118d100056a4328231a2000e54655046344001d28c8a08c68800e2fa137654d100045ec26eca9a20018ee82dd953440011db05bb2a6880021fe157654d100045fc22eca9a20038bc845d953440011bf06bb2a6880023be097654d1000c76412eca9a20008f7815d953440050fd0fb2aa68801237a1f6354d1000572c0ea5b122000a6e85d0b62440014db0ba16c48800e3be1d42d891000557424c
  | 5 => 0x8003351cf71595100065c3a6e0b2a200087d8799065440014bd07320ca880029760e641951000537414c832a2000a6d8299065440010ff0eb20ca8800297e0d64195100052e41ac832a2000a6f8259065440014d904b20ca880029ee0164195100071ac08c832a2000e36711906544001c6ae2320ca880028fa1263195100051ec24c632a2000a6e8298c65440014db05318ca880028fa1262195100051ec24c432a2000a5e8398865440014bb07310ca880038d19241195100053a4328232a2000c3e76d97644400117b0f32ec8880028fa1665d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100045fc3acbb222000a9f83597644400153906b2ec888002abe0965d911000556412cbb222000a3e86197644400187cec32ec8880038d60465d91100051f42cc7b222000a3d8598f644400155d0531ec888002ab60a63d91100051f42cc5b222000a3d8598b644400153d07316c888002a760e62d91100755b436e3b222000aaf825d7644400155904baec8880030f5d475d91102655b408ebb222000ab5811d7644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf6444001c3ea729ec8880028fe1572d91100051e42ae5b2220008be8714b644400117b0e296c888002a7a0c52d91100054ec18a5b222041aba80dc7644400155d0598ec888002ab60b31d91100051f42863b222000a3d850c7644400153d0790ec888002a760f21d91100045f43843b22200e8bd87087644408356d03b86c888002ada0450d91100051f42e61b222000a3d85cc3644400155d04186c888002ab60830d91100045f43e41b2220008bd87c83644400153d06106c888002a760c20d91100062ebaea7b1a2000ad581d4f63440071bf0ea1ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec6880039560465d8d100070fb2ec9b1a2000e1c65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc825936344001c3eca326c6880038719464d8d100074ac08c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000e946490763440018baea3aec688002b5a0475d8d100056ac08ebb1a2000a5e859d363440014bb0b3a6c688002b3a0a74d8d1000566c14e9b1a2000ad6811d363440015ab023a6c68800387d5254d8d1000567414a9b1a2000acd8295363440014bd0bb96c6880029761772d8d100056ac0ee5b1a20008de8714b63440011bb0e296c688002a7a1052d8d100054ec20a5b1a2000a5e85d0b63440014bb0ba16c688002b3e0971d8d1000566412e3b1a20008de87d076
  | 6 => 0x4bac28e29862000cd5631c530c40018d90ab96cb08217179ce52d961002c3e43aa8b2c20058de87d4d63840018beeba9ac7080163721d4358e100143f43ecaa9c2000c77651c553840090fd0fbaac5080031ba0b7558a1000636c16eab14200087f855d162840090f90aba2c5080163ba1f5258a1002c7643a84b14208ac6c755096284007958e8a12c5080021fe157654a100043fc2aec994200487c855d9328400b1b90eb1a6508003171d5634ca1002c7643ac49942000c6c7558932840e79acc7b8a65081b73998b714ca100053bc2aed8842000c3d7495365440014dd052a6ca880029b60a54d95100053ac0ca9b2a200387f8755365440018bae729eca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca8800297e0d64d95100052e41ac9b2a2000a6f8259365440014d904b26ca880038d60464d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d95100071a32483b2a2000e3464507654400187ae83a6ca880029ba0874d951000536c10e9b2a2000a76811d365440014eb023a6ca88003175cc73d95100043f43887b2a200087d8710f65440014dd0421eca880029b60843d95100051f424e5b2a2000a3d849cb65440014bd07396ca880029760e72d95100043f43e85b2a200087d87d0b65440014bd07b8eca880029760f71d951000537416e3b2a2000a6d82dc765440010fd0fa0eca880021f61f41d95100052f41e83b2a2000a5d83d0765440014dd05a0eca880029b60b41d95100053741663b2a2000a6d82cc765440010fd0e18eca8803e1f61c31d95100052f41e43b2a2000a5d83c87654400147d0810eca880028f61021d95100043f43881b2a200f87d8710365440014bd06206ca880029760c40d95100053741081b2a2000a6d8210365440014ed02206ca880029d60440d95100043f43e61b2a200087d87cc365440014dd04186ca880029b60830d95100051f42641b2a2000a3d84c8365440014bd06106ca880029760c20d95100061e32ee8b2a2000c9c731916544001958e4322ca880031719773595100064e326e6b2a2000c6c65dc96544001958c9b92ca8800e2fa1f74595100061fbaee8b2a200087f855d165440011bf06ba2ca8800a3720d745951000477c12e8b2a20018ec825d165440011f700ba2ca880022fa1c74595100061fba8e8b2a20028de87dcd65440018beebb9aca8800327dd373595100064e3a6e6b2a2000c5f751cd654400193ee839aca88003271d0735951000c7743ee4b2a2000c6f75dc9654400195ee9b92ca880032b1d3725951000667b9ee4b2a2000ccc73dc965440018deea392ca880032bdd07259510006563a0e4b2a2000ccf731c96544001998e6392ca8
  | 7 => 0x3c74195634800187ecbba2c6900030f1977458d200063bb2ee2b1a4000c7465dc563480018eeca38ac6900031d1947158d200066a318e2b1a400487e87dd5634800717d0fba2c6900030fdd77458d200061e3aee8b1a400087f855d163480090f90aba2c69000237e0d7458d200047bc0ae8b1a40008f4815d163480011f700ba2c6900022fa1c7458d200061fba8e8b1a4000c3c751d16348001938e9b9ac6900031b1d77258d2001c7643a84b1a408ac6c755096348007958e8a12c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000ce6421c563480019ca8438ac6900032e1d37058d200043fc2aeca9a40008bf845d9534800717908bb2a6900023be097654d200047bc0aeca9a40008f4815d953480050fd0fb2aa6902171b1db754c92040e363b0ea9924000c6c76d953248001c98c7b2a64900031b1d8654c92039e723b6e29924077ce4761c53248001ac8ea38a64900035add4704c9200056b41e83b0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac2900023de1d61185200055a422c230a4000ad483584614800795ce8a10c290002b5a0f411852000572c168230a4000ea542d0461480015cb05988c290003b14c8311852000578c006230a4000a7581d9651480051bd073b2a2900023760e765452000c76410eca8a4000c5c73d95514804b8d8e5b2aa29000317d97735452019e2e32ee6a8a4000c6f65dc9514805b8d8cbb92a2900021fe15768c5200243e42aed18a4002acc864ca31480090fd0bbb262900021f617764c52012e36396caa824000c3c74d95304800187ecbba260900030f197744c1200064e3a6c69824000c6c65dc9304800b3990e9926090016b3219324c12002de4402649824025c6e76d9620480098dcec32c409000e1fe1d54d97100045ec3ce9b1e20038bf875d363c40071bf0ea1ec78800e2fa127654f100045ec24eca9e20018ee829d953c40011db053b2a78800a1f21d6554f100243fc3aebb16200487e85dd362c40010fb0bba6c58800a37a0f74d8b100046ec1ee9b1620038ef8750b62c41158dceaa16c58800f2b9d142d8b100043ec2ceca96200487e859d932c40010fb0b3b2658800e2fa12764cb100045ec24ec996200087f855d932c40090f90abb2658800637a1f634cb100147743ec499620058f5861c532c40018f2cab84a3880129de19659471002c3f43ecaa8e2009c7776dd551c40018eeedb2aa388002dc603655471045e6bbb0e6a8e2000a748654d51c4001b88e6392a38803f1d5da51943100
  | 8 => 0x9bb2a2980022f613765453000c77414eca8a60008ed829d9514c0051b9063b2a2980d29b20965545300053a40acaa8a6060c9c73d91514c001958e5b22a29800327d9373545300064e326e6a8a6000caf64dc9514c001958c9b92a2980022fe11768853001c5e422ed10a600487e851da214c0010fb0a3b442980030f19175885300061f3aec910a6000c3d75d92214c0018dcebb144298006b3219328853001c5f426ec90a60008bd84dd9214c0050ff0eb2ca0980969b20965941300053a40acb2826000e3b50d92504c0018becbb9aa098183279db648c13002c3e43aa8b2c400587e8794d65880018bee729acb100033520d71d8e2000673c12e3b1c4000ce4825c7638800b1b90ea1ac7100121fa147158e200043ec28e2b1c40058f58790661880015cb0598cc3100029d61431986200046fc1ae8b0c40028dc835d161880051bd0fb9ac3100033560773586200066610ee6b0c40058f48750561880014eb0a18ac31000335dcc315862002c7ac3cc328c4004a768598651880011bf06bb2a31000a3720d76546200062e39acaa8c402dc6e65dc951880019a8e730aa31000339dca615462002c7a43ac2a8c4000cd473585518800717d09bb463100022f613768c62019d2f42ec718c402da6e85d8e21880211df0eb0c4310002b3e0d618862009c77c32e110c4000d69755c2218800187ae92a6ca900029b60a54d952001c3fc3aa9b2a4000c5d7394f65480014db0529eca9000297e0d64d95200052e41ac9b2a4000a778159365480014e902b26ca901531b9d942d95200071632285b2a4000b688050b654800187ae83a6ca900969ba0874d952000536c10e9b2a4000c5d731cf654804b4dd0439eca900029b60873d95200043f43887b2a400087d8710f654804b4dd0421eca900029b60843d95200052f41ee3b2a4000a5d83dc765480014db05b8eca900031d5c471d95200043f43e83b2a400087d87d0765480014bd07a0eca900029760f41d952012d3741683b2a4000a6d82d07654804b4dd0598eca900029b60b31d95200043f43863b2a400087d870c765480010fd0e206ca900621f61c40d95200052f41881b2a4000a5d83103654804b4dd04206ca900029b60840d95200053b40881b2a4000a7581103654804b0fd0f986ca900021f61f30d952012d3741061b2a400087f855d165480011bf06ba2ca9000a3720d74595200047bc0ae8b2a40008f4815d165481198f6ebb82ca900021f61e641952000536c14c832a400087f8759065480014bf06b20ca900029720d64195200053bc0ac832a4000a748159065480a94dd04320ca900029b219421952000717b228432a4000e2c6450865480016d100a10ca900121fa1671d8d200043ec2ce3b1a40018ec825c763480010fd0fb2ac6900030f1d36558d200043f438cab1a4000c
  | 9 => 0x52d953000656390c8b2a6000cac64dc9654c001968c9b8aca980031d19471595300065a320e2b2a60038be87dd1654c0011df04ba2ca980063b20974595300047bc0ae8b2a60008f4815d1654c00117d0e3a2ca9800e1f21d545953001e1e3a2a8b2a608ec6c72551654c0031dd0fb92ca980032bdd37259530006563a6e4b2a6000c6f751c9654c00195ee8392ca980032b1d072595300065bba6e2b2a6000cb474dc5654c0019cee5b8aca98003391cb71595300063bba8e2b2a6000cb7741c5654c001968e838aca9800335dcc715953000673b90e2b2a6000ce4721c5654c0018ed0a38aca980031dd5071595300063aaa0e2b2a6000cd7321c5654c0018e8a038aca980022f61e65d91300045fc3acbb226000aaf82597644c00155904b2ec898002ade0565d91300055a40acbb22601da9e86dcf644c00155f04baec898002ab20975d91300061eba8ebb226000a3f855cb644c0014790ab96c898182a7a0c72d91300054ec18e5b2260008be8714b644c00117b0e296c898182a7a0c52d91300054ec18a5b226000a3f855c7644c0014790ab8ec898002a7e0d71d91303054e41ae3b226000aaf825c7644c00155904b8ec8980028fa1471d91300051ec28e3b226060a9e83c87644c00153b0790ec8980022fa1c21d91300045ec3843b226000ab681143644c00156b02286c8981822fa1f20d91300045ec3e41b226060a9e83083644c00717d0938ec4980022f61271d893000c6e41ae3b1260008be87d91624c00187eebb22c4980030f1d764589300045f438c8b126000c3f75191624c001878ea322c4982372edc064589300065bb26e2b126000cb464dc5624c00196ec838ac4980032d190715893000672310e2b1260038be84dd9524c00117b09bb2a49820b171db754c9304062e3b0ea99260018dc87595324c0015a902b2a6498003271db644c93036e6a3b6e2992606bcd4761c5324c001aa8ea38a649800356dd4704c930006e9b88e0992600087f855cb614c0090f90ab96c2980031d5d751d853001c5f436e8b0a60008be87d91614c00187eebb22c2980030f1d7645853000656396c8b0a60008be87191614c00187eea322c2980030f1d4645853000656390c8b0a6000caf64dc9614c001958c9b92c2980030f9d764185300061ebaec830a6000c3e75190614c00187aea320c2980023de1d61185300053a42ac230a6000ae482584614c0011df04ba8c2980063b20975185300243fc3aea30a6000c5f835d4614c0018b906ba8c2980031be09751853000636412ea30a6000c5f325d4614c0018e902ba8c2980121fa1774185300043ec2ee830a6000c5d754c8614c0018eaeba88c298002b560f21185300056ac184230a6000ec532084614c00117f08bb4a29800e2f21176945300053ac0ecb28a6000e3751d92514c00717d
  | 10 => 0xb044200caf744c960884010fb0f328c1108021fe1d65182212763b38aca30442008fb8758060884070ff0eaa6ca90803175ce53d95210046fc1ae8b2a42028dc835d165484011df04ba2ca908023ee01745952102c7c402e8b2a42028de87dcd65484018beea39aca9080333dcf72595210066639ee4b2a428fc7775dc565484019a8e7b8aca90803175d753d8d2101c6fc3a87b1a420087f855c363484090f90ab86c6908121fa1f7558d210043fc2ae8b1a420487c855d163484011ef02ba2c6908023ee017458d2102c7c402e8b1a4200c5c75dcd63484018d8ebb92c6908031ddd77158d210063a3aee2b1a420087f855d953484011bf06bb2a6908023be097654d210047bc0aeca9a4200c5c73d95514845b8d8cbb92a29080637e1d638c52119d2e42ac718a4200ccf63dc931484698dcecbac429080a3be1d638852116d3642ac710a42008fb87580604840b1b90ea1ac7280063ba0b7158e5000476c16e2b1ca00087d861c5539403d0fb0db82a7280023de057458a500047a40ae8b14a0058ec875096294007958e8a12c52800a37a0f7158a500046ec1ee2b14a0008f7815d932940011e902bb265282171798f754ca5041637316ea994a0058dc8758d32940018beeab1a65280125721d534ca500152fc32a6994a0058ec8758932940ef9acc638a65280033558c714ca5035e73310e2994a000ce5621c5329400b1eb0f20cc3280031b14b725865002c7a43a82b0ca000a778550561940250ff0eb0ca32804a9de1d61946500063bc3ac328ca01587f865c2519402b2f70cb84a3280031ee197094650004bcc06eb18ca00097980dd531940698dcc4bac43280031b5d562886500143f42ce3b1aa0008ef825c763540031d904b8ec6a80033518c7158d5001c77c3a85b12a0008df835c762540051b906b8ec4a80023da06764c9500047ac0cec992a00487c851d932540014eb0a18ec2a80023de1d61185500056a41ac230aa000d4c731c9515402b0fd0e30aa2a8003175d7638c5500045fc22ed10aa0038bc845da21540090fd0a3b442a80d31b18975885500243ec38c3282a000c7571186505400b0f90eaa2cb180163b21d4258a300066a18ee2b1460058f587906618c0015ab0790cc318002ad610219863000477c12e8b0c60018ec825d1618c0090fd0bb92c3180021f617725863000c7743ee4b0c6000c6e85dc9618c0018db0bb92c318003330c7725863002c7a43a82b0c6000ab584085618c0019cee410ac3180163d61e61946300253b42cc328c60008ef825d9518c0031d904bb2a3180031b1c9655463019e2f32ee6a8c6000c5d65dcd518c0019aee730aa318003391ca615463002c7a43ac2a8c6000ce472585518c0231bf0eb0c6318002b3e09618c6300a46fc32e118c600487e85dda218c0010fb0bbb443180029760e
  | 11 => 0x8c4018beea992c1188023ee1d601823101c3fc3aa9b2a62008df835d1654c4011df04ba2ca988063b20974595310047dc02e8b2a62058f8805d1654c4031dd0fb92ca9880333dcf725953100637ba8e4b2a6200ccf731c9654c52d8eeebb8aca98803391cb715953101c77c3a85b1262008bf845c3624c40717908b86c4988031b1cb65545310062fb2ee6a8a6233c5c65dcd514c4011f70eb00c0988021fe1572181310243e42ae4302626ea6e8259265884014db04324cb108029be194299621007173228532c4200e2d6450a65884010fd0f2a2cb108030fdd2545962100536c14a8b2c420387c8755165884018bee729acb108029b60a53596210043f43ec8b2c4295a7681d9165884010fd0e322cb108b71bddb72596211a5b2c0ee4b2c426ec6f765096588401c5cc8a12cb108031b1cb74596210061fba4e8b2c4234a6e829d165884014db053a2cb108029be0974596211a536412e8b2c4200c6c725d165884018bee739acb108d29ba0a735962100536c14e6b2c4200a6f825cd65884010fd0e21acb108021f61c43596211a53741086b2c4200a6d8210d65884694dd0fb92cb108d31ba1f725962116c3f43e82b2c420087d87d0565884014bd07a0acb108029760f41596211a53741682b2c4200a6d82d0565884694dd0598acb108021fa1c31596211a43ec3862b2c4200a5e839c165884014bb07382cb108029b60a70596210051fc22e0b2c4200a3c845c165884014df04b82cb1093a9da04705962116d3ac08e0b2c420087e8710165884010fb0e202cb1080297a0c40596210052ec1880b2c4234a6e8210165884014db04202cb108029da0440596210053ac0880b2c420087e87cc165884010fb0f982cb108d29ba08305962100536c1060b2c420087d8799763885298ece332ec7108021fe1d65d8e2149e3b38acbb1c420487f875d763884090fd0bba6c7108021f61774d8e210047b40ee9b1c42058fa80dd363884011f301ba6c71080e3be1d42d8e21456373aa85b1c4203cae7450b63884d79cce2a16c7108031d9d671d8e210063abace3b1c4292ad681dcd63884090fd0bb82c7108021f6177058e210043ec2ceca9c42008f6819d953884050f90eb2aa7108d31b1c96554e21404b743eea9944285c6f76dd532885038deec3aa65108b65b21e654ca2100637bb4ca994429196c8759532884018deecb2a65108039398d654ca2100ce643aa6994422e8ed86dc532884db9ccc3b8a65109b739ddb714ca21006b3baee29944277ce7761c53288401ac8ea38a65108d31b9c9659462119e2f32ee6a8c4200c5d65dcd518840339f0e994631080ab3e19328c621485a642a6518c4200bc7814ca3188401878e932ac1108030f1d165582210061f32ee8b044200c3d65dd1608840717d0fba2c1108032b8cb745822101e563a284
  | 12 => 0x802b360e70d895100557c22e1b12a200aac845c362544014db0a386c4a88b6b960470d89510047743881b12a2008ed87103625445b4dd0a206c4a88029b61440d89510056741881b12a200acd8310362544015cd02206c4a8802b960440d895116d3742e61b12a200a6d85cc362544011dd0e186c4a88023b61c30d895100666316e6b12a2008de87d8d62544011bd0e31ac4a8a7b35dc4635895100476c3cc8312a200a6d85990625440159d07320c4a8802b360e641895100477c3ac8312a200acf83590625440159906b20c4a8802bae01641895100574402c8312a290cce76d8c6254401d1ce9b18c4a8803a35d3631895100476c3cc6312a29dace8398c62544011df0eb18c4a8a72b9e0563189514dd67430c6312a29acce7618c6254533c9d0a318c4a880393614631895100727ba8c6312a299e4c7518c6254401d1ce8318c4a8803a35d063189514cf63a88c6312a299e4c5118c6254533d88a2318c4a8a6793d40631895100536432a6312a200e4c6354c62544016c902a98c4a8a171718f754c95141636316ea992a2018de87d8d32544018beebb1a64a88cf171d7634c951024ae43aa6992a202a5c8654d32544018b8eca9a64a8802d5205534c9510147743ec4992a22dc6c75d8932544091ed0db8a64a89cf3518f714c95136e72316e2992a200cd7631c532544ef9a8c638a64a880339d88714c95135e72310e2992a233e5761d8e51544f9caec231ca2a88b799d87629455100726318c528aa279e676118a51544014f30a206c0a8802bc60440d815100667396c7302a200cce7218e605440199ec6b94c0a88033318d72981510066739ec5302a200ccd73d8a605440199ce6314c0a8803335cc62981511ac6e436e6b02a2008de87d8d605440193ee9b1ac0a8803271d3635815100666396c6b02a2008de8718d605440193ee831ac0a8803271d0635815100666390c6b02a298cd77118d60544691d90db92c0a880333d8f72581510066631ee4b02a2008ee87d89605440195ee9b12c0a88032b1d3625815100667b9ec4b02a200ccc73d8960544011dd0e312c0a88032bdd06258151006563a0c4b02a200ccf731896054401998e6312c0a88023ee1d60181510055c422c0302a200a748154c60544098eae3290c0a88121f61e51181510053cc04a2302a20387f87553658c52f4ed03baacb188029760e525963101c5f426e0b1462008bd84dc1628c5032bd0fbaa6518a0b17ddb754ca314062fbb0ea99462018de87d95328c4678b8eab2a65188a23761b714ca3139e6b30ee2994626dcd776dc5328c401aaeebb8a65189af35dd8714ca31006aa3a8e29946200c5d655ce518c4050fd0fb2aa3189f29da0765546310043fc2ae5304620487c855ca608c4090fd0fbaac11880317ccb75582310043fc2ae8b04620487c855d160
  | 13 => 0x63ba8eec994a200c77511d932944012eb03baa65288125d217714ca510247ac30e2994a204976851c532944011bf06ba2c12880a3720d74582510047dc3ac0304a2038df8750f63544050f90ab86c6a8802b3a0a64d8d5100566c14c9b1aa200acf82593635440159904b26c6a8802b6e0164d8d510056c402c9b1aa200a9e8418b635440153b08316c6a8a17179da52d8d511ad2f42ce9b1aa200a5d859d3635440159d053a6c6a8802b360a74d8d510052ec2ee5b1aa233ad581dcb635440153d08396c6a8802a761072d8d5119d2f42e85b1aa200a5d85d0b63544671bd0fa0ec6a88023761f41d8d5119d2f42e83b1aa200a5d85d07635440159d05a0ec6a8802b360b41d8d5119c6f43e43b1aa2008dd87c87635440153d0810ec6a8802a761021d8d510054f426e1b1aa200a9d84dc3635440159d05386c6a8802b360a70d8d510052fc2ae1b1aa235a5c855c363544014bb0a386c6a88ceb560470d8d510046f43881b1aa2008dd8710363544674bd0a206c6a88029761440d8d510056741081b1aa200acd8210363544015ad02206c6a8802b560440d8d510054f42641b1aa200a9d84c8363544011bd0e106c6a88023761c20d8d510066631ee4b1aa2008dd8799063544014bb0b320c6a8802b3a0a6418d5100566c14c831aa2a0ad58199063544011bf0eb20c6a8802b3e096418d5100566412c831aa200adb8059063544015b100b20c6a8802a7a106218d510054ec20c431aa200e4c62948635446b8b8edb1aa6a88ce1fa187154d513e6abb98e2a9aa233976861c553544018ed0c38aa6a88031dd907154d510063ab20e2a9aa200d57631c553544f9aa8c638aa6a8a7f55cc87154d51004bac00e2a9aa20087e86dc15354401c9ca5b1ec4a8a07179d463d89510062eba8c7b12a2048f581dd362544014db0ba16c4a880e3be1d42d895101e573a285b12a200a6d85ccb625440117f08b86c4a880e2f21170d89511a6373b2ebb12a200ace83993625440159b07326c4a8802b3e0d64d89510056641ac9b12a200aeb8059362544015d100b26c4a8a43939d763d895100726baec7b12a29ae4e8518f6254401c9b0a31ec4a8a6b939d463d895100726ba8c7b12a200b648154f625445b4dd0bba6c4a88029b61774d8951006373aee9b12a200ae681dd3625445b5cb03ba6c4a88032bdd274d8951006373aae9b12a22da6e851d362544014db0a3a6c4a88029b61773d895116d72c0ee7b12a22da6e851cf62544014db0a39ec4a88023ba1c43d895100476c3887b12a22da6e8510f62544014db0a21ec4a88b63ba1f41d895100476c3e83b12a22da6e85d0762544014db0ba0ec4a8802b3a0f41d895100566c1e83b12a22d8ee87cc762544011db0f98ec4a88b69ba1431d895100536c2863b12a200a6d85dc3625440159d07386c4a8
  | 14 => 0xc845c0614c95d8ecedb28c2992b79990b65185320047ac3cca30a64aca7685994614c8011ef0eb28c29929eb5e0d651853253573c12ca30a64aba7686194614c9558ecec328c2992a795a0c65185325472ac18ca30a64a8e5773194614c951ca8e6328c2992a799dc8651853254732390ca30a64a8e6642194614c953cce64328c2992a3958c865185325472a190ca30a64a8e6432194614c953cae60328c2992a399c8065185320047ac3cc830a6400a7685990614c8014eb0b320c299296b560e641853252572c14c830a64008f787590614c8014ef0ab20c2990029d215641853200579c02c830a6400af080590614c8d75a90ca98c2990039519553185323bd724328430a6400e6765508614c801cc8caa10c299003a9d9142185323bde241a8430a6400c77759d4614c94f5af06ba8c29929ab9e0975185323bd6b418ea30a646bad5831d4614c8014ed0b3a0c2990029d61674185323bd6b41ce830a64a5ad5839d0614c8d75cd053a0c299292b960a741853235d73410e830a6477ae5821d0614c801c6ea92a0c2991aeb9a0a541853200572c14a830a6477ad683150614c8015ab062a0c2991aeb9a08541853200572c10a830a646bae784508614c8d7d4f08a10c299003a99d1421853200752ba28430a6400ea654508614c801d4aa8a10c2990029de1570185320053a42ae030a6400ab7845c0614c80156908b80c29928ab5e0d701853250d73c12e030a6400a76851c0614c8014eb0a380c299002ada1070185320055ac20e030a646bad5831c0614c8ef5cb04380c2991deb5a0f50185320056ac1ea030a64008f687140614c8011eb0e280c2991aeb9a0b401853200572c168030a6400ea542900614c8011ed0e200c2990023d61c40185320053b4288030a6400a7585100614c8ef5ad06200c299002b560c401853235d734108030a6400ae582100614c801d4a84200c29900f2b9d142d81320243f42ce3b02640087d859c7604c8015b306206c099002ba60840d813200754a1081b026400c77659c6604c8018e8cb38cc0990031dd9571981320063a32ae33026400c7675d86604c8018eaebb0cc0990031d9d461981320063aba8c3302648287c86dd5604c8010fd0fb2ac0990030f1d365581320043f438cab026400c3c74195604c9478dee432ac0990030fd9774581320061e32ee8b026400c7765dc5604c8018e8cbb8ac0990031dd9471581320063a328e2b0264008f687d85604c8018eeebb0ac0990031d1d761581320065bba6c2b026400cb474d85604c8011ed0e30ac0990031ddd461581320063a3a8c2b026400cb774185604c801968e830ac09928b35dcc615813250e73b90c2b0264008fb87580604c80157108b00c0990163e20174181320043fc2ae2302640487c855c4604c8091e902ba2c52880e3b21d4258a5100
  | 15 => 0x7a0eca9920a9ba0b41d953200536c1683b2a6400a76819c3654c8014eb03386ca9920a9760c70d953242d36c10e1b2a640087e87103654c8010fb0e206ca9921697a0c40d95320052ec1881b2a6482a6e82103654c8014db04206ca990029da0440d95320053ac0881b2a6400c7465dc5654c8018e8ca38aca990021fe1574595320047bc0ae8b2a64008f4815d1654c8011f700ba2ca990163e20174595325a62fbaee6b2a6400c7775dc5654c8018eeea38aca9900335dcc715953200673b90e2b2a640087d87990654c9674db05320ca990029da0664195320053ac0cc832a640087f87590654c8014ef02b20ca990029d20564195320053dc02c832a6400a7880590654c9014dd04320ca992069b219421953200717b228432a6481b4c83508654c9058b8edb2aa699003710847154d3200c6ec1ee9b0a64028ed82dd3614c8018eaeba8ec299002b560f51d853200572c16a3b0a6400a7685d07614c8014eb0ba0ec299002b960b41d853201c7bc3a83b0a64b2e5673d97614c95dcaae7b2ec2992bb999cb65d853259732b96cbb0a64b1e5683197614c955cab0632ec2992c7959cc65d85325572ab98cbb0a64aae6672197614c963ccae432ec2992ab9990865d85320053b42cc9b0a6400a7585993614c8014ef0ab26c2990029d21564d853200579c02c9b0a6400af080593614c8db5a90ca9ec2991ceb921942d85320073232a85b0a6400ea46450b614c8e778906a16c2991b6b560f75d853239d72c16ebb0a6400c75751d7614c80156d083aec299002ad61075d853239d6b418ebb0a646dad5831d7614c8db5cd043aec2991ceb960875d853239d6b41ee9b0a646dad583dd3614c8db5cd05ba6c2991ceb960b74d85320053b428e9b0a6400a75851d3614c8e75ad063a6c2991b6b560c74d853236d73410e9b0a6473ae5821d3614c801c6ea92a6c2991b6b9a0a54d853200572c14a9b0a6400a7685dc3614c8014eb0bb86c299002ada1370d85320055ac26e1b0a646dad583dc3614c8e75cb05b86c2990029da1670d85320053ac2ce1b0a646dad5831c3614c8e75cb04386c2990023da1c50d85320047ac38a1b0a64008f687103614c8011eb0e206c2990029da1440d85320053ac2881b0a6473ad683103614c8015ab06206c2991b6b9a0840d853200572c1081b0a6400c7675d86614c8018eaebb0cc2990021fa1f65585320043f438cab0a64b0c5f73195614c95f8dee432ac299207171cc651853240636390ca30a64008f787584614c8014ef0ab08c2990029d215611853201e573a28430a6400ad583144614c8014ed0ba08c2990029d61741185320056ac1e8230a6400ae582d04614c801d4a85a08c29900e3d61e411853200752a128230a6400ae582104614c8010ff0ab80c2990121f21570185320045fc22e030a64038b
  | 16 => 0x480480000200e80180580000200080000000000900100980580600180000580500180100380080780180600700000000080980b80480000000380a00100200600480080280080300080200200000080200480080200e80000080580000400000380380200180000480000100480000280300000000480000080500800380080280400580d00480200000100180080100700300280080300000000300081300880480080480100a80000280080000500000280d00000b00080000100180000100180f80300080000000080180200000000380000781280000d00480300000780080000800700000000000380700180100300280200080300080100080600080080100000000080000000f80000380100480000000480280180180000280000200380b80500200080100080100080700000400900280200300000000980000080000080100b00180000000080300600080080000280200000300180180a00000000380080180080d00000280500180000b00200000000200600000000000580080000d80000600181480080000000780600880d00000000000000000080381980d00200180300380300000600600180280200200080580100480100300100180180180d80180000000680b00100080400580480280000001200100180000080100000480280300100100000080000000100000100000000880000180000080000180080680680000000080480080f80400500280100080f00080581100080400000700180100080180000000080080200000800000300480100300000180000280000080000180200000500e3be1d42d89530045fc22e1b12a6038bc845c36254c019c8c438ac4a9a161fe1572d855301c7bc3a83b0aa600ab5840876154c011ef0eb08c2a9ae2b5e0d611855300572412c230aa60287d85dd06154c071eb0f208c2a98029d61641185530056ac1e4230aa600a75850846154c0156b08108c2a98022fe11701855301c5e422e030aa6008ef825c06154c031d904b80c2a980a1f61774d81530246ec1ee9b02a6008fb875806054d0b0ff0ab90c0a98023be09711815300c76412e2302a600cd4631c563548014eb0a18ec2a92df1d5d761985520047bc3ac230aa400ad483584615496d5cf04b08c2a9002b960b31185520047dc3ac0302a4b5a7b8558060548011bf06b88c0a900a3720d71181520061eba4a9b2a6400a6d82953654c8070ff0eaa6ca990029da0664d95320053ac0cc9b2a6400a7781593654c8014e902b26ca990029ee0164d95320053c402c9b2a6485a6c8650b654c9018dceca16ca990038b19142d953242da641a85b2a6400c3d741d3654c9054dd043a6ca992169b60874d95324152ec1ee3b2a6485a6d82dc7654c8018eae238eca990021fa1f41d95320043ec3e83b2a6485a5e83d07654c8014bb0
  | 17 => 0x7502a297880e28642790a000000000c100002e88d914d962042a2af3e110a11a427d2fe9c702f016f37f1a180008cd2b9986c00063e0001038abe88b309a268c8e87a3c380002664b700018489d83214299d9000026421e0a10ec453100004506868d103f13ec3ae163044042c7a47ce1308f6d10c4c810302045a4445012811c08881d3449a58c0675c29f8190c207a82038bcc91e84f0001fb839c45109708905808ca0c780000000001fa9c8ca6011f23f233c000535000000000052c28221f497a0000001a9c4da5ef2f620e114202a15b10fcc7026709422d8eb20a02c51c281f80001af06b000000028689089b20000000000d0e5080000ebc5700002bb0000ce80000000000d103862c5966000036c0000000c6a24816f1d300000172e5a2f4f2c7a400000000002520e6837c8545590530ef4ba860413c99688f226a12c8d389d42fd05f945015c53419d9db47188540001d3d1103522fb99e40001a143aa08c00082a250985067a0133af22442e463622b0de08646d50be86640004763ef88dc000000000189810600032592046d233212012450d245304f00109c20f33c31c2c7600cd46d05a00000bc0001ae0b4a0000001c80c3257f0001df853e2752fa061045400021010cc32a6d20699920e6a75200180300100d00680600400000100380680000580000000080000100980280180480000000180100100100000000800080200000000380380080280080100000100080d80100200000600280300000180000100000800000100380100080101580100080200000380080280c00100300400280381380000101001100180000c00700a80000080200100080300b80480780600380000180080280000100080200080000200c00100280e80080700000080500000300300100080c00280480000100d80180180000000000480080200080100001701400180000000200000700400000181481d80080000000000480180180100880400000200000001500200480280080200200080000500080100000380200000480a80b80080000400600000480200a00000080100000100100180880000180000080380300000000000000000000080280000100000300180a00000200280700080000300180100000080680080000000080180100080800600500100200280000081200480000000280600080200680000180080000100280080300480800200080380500600000080100080080180000000300180000200000000180080100080080080200580100600080400580200280080080100200880180100000300000000800380c80880000080102280000180000080280780100080000080080000c00600f80480080280000380300080100300100180680080380000000300b80780480100280080000b80000100180200100180000080
  | 18 => 0x3200005f1007201400000005d95c87523202d0224caf40002db16407f22a40679cb0d2276800019908d27772e28fdc1c82a200007f8e885860da946ca660110000000000000232817c744000000234c0000001e3835841244f0001ee400081e0af22243724cc3e18ff00000000d400008f0000388000073e12245a80000004be3a69fe8af01bb373952c5a004e443800027256c39900000002d90001ec40002cc0d200006be8721e2069c50c5e9026a2e048a000424000000047300e003491a0492b300000001c90b519e80008bc1c1902d0de00031c92d81e020e40a852400073f00000000000003a31fc00000001698c58c126d72ff046428855c12d87dcf1202f40200002200000cd80007c87601460000000830448027d16e318418800065c0000000e3c7d83be0000758cf022d3e8000106c38e097967053c000315800077e00040121cc000000294945c00025641406007b802e1558d8cbbc1ee221851c30c1dc22e000103066004e08800000000ed00000cc00000000000f81ef02d030d13e68e1cf1dc83020001a1000000085623d000043e76f2911314cec4250001aac1a478c0689b3086a31b11b11a800014310a18340000003981f0000000008b00000d400020a99f4000000242800018466d0000ac800063100002a900c3c227b01800363dd37585dd13c5da2251e34d9c3d00600150cdc67b457a09400058e3140d3c8466f645d000033c5d51d0800003e4b50410dc4b900001800b080008580218f2cbf82b02e983f80000a700006300004590001ab400061f3f38940c485553108ae90e22a70cc05809e03aa00000000003963288acc7dc50a2370000c7e88f12d0e50b9c8c826b868064e37b0001d44bd67420579a2d04433103a0dbcc1054f37100000007af3011c1c00087b1f8000001445a1f8965c9ac43900013bc67c83f2f2116107645d24203d111a24700015207640002571e3c0000000001ea80000000000f60000000000000088888e00000000001713ec00007da26805813781d4079305800047c04f1c08dccbba0e51490c8ccbc0002f30eb8de00001fc163c0fa5121b0903c00000000000010dc4fa2498000000000103926800050f037089c0000000000dd400000013e0000000701000000034a1ca000000034c00038c800000000000013491cc6ba32212e80001610900000b4c00035601c8d148a900018680000003c1000000043801b9cec00010843080009067a10001ef00007a50000e403d66434228aa11c639d0000c487ae8a53b703bc00055d000000041855641014740000001250000cb67562e01a50c1e0631428000c74000000219c1682a62a8895c2c882133300000006631ad9b603c824d00580986a800000000007d433f0000a74fd48aa0001ba00004a2000104090c0000c40000b503ad1640254398
  | 19 => 0x40001ba14f443605b1de2390cd45a425a0d34c520001e08c1c86e0000630000000000210a264f5c00000010b80003e100000011b68090be1fd44d8589464a2b91ac5703748000ef27db106a1006264e602e93342001ad0000000a1c0000000f6516848704d000000083e36c9f680008b000004c40004b209f229c0002ea3409d0cdcc4801159b8c6a253629d197451200036500b046a1b411e04382787b22e7a10800019c000000000031a2d698b4e7003b3f291fc1426a1042836800046741e0000000583000000000044d3700e649ce24335f893846400000003b854000025c85d80000000000e551080000000aec00000000007489ca56b11c127079a4fe043a20c00043b40d0000f4e000030800095e5b73fe91983280002c99bb4b3228e188000083424600000004300122a220340821791b294f02d25aa34f05ac0004240de17b437400000000549f261d3cd85c09943b704885ccfd082b3cea1e014a148081941428c26e0001cc46440002a38004e722702a192607cc000000000000000038204d8cac0002f08b1422e210280185cfe2000000107857c52600013442825d20001e38cb800000000000003b41ab8000fd62233e6a3000004c73b511ac8f601047380010f269c10280007347a30a609e811c1352ce8000cfc0001c00d0060277a04007fcaca4601040cd871000002b0e147ca7370dc00e00605ba01a87ccb6a8e0193000101c4402ba8000396765241000105800625580000005271a48cc0d621211ac00005ea01937700000000be0000000b7a0000000154836000173902046204a2ee0bf8e4a76c39200010a000027880000000d52159bb0a220ca000155d0cc0000001bdc0000003870e5d0fc7d100001a44e209044b00500000003b18a2885e00001f0258762817393119080662f3271ac914880c00000009c41e113295480004a73d5937c0008811791d7400030600020510d68651132318b0a1e31489888a4a19029086b850434b3659568c028012e10afc0ea82411787c46f86ea38f86ad01e8773fc1224e260501a282e0ade8a220b07f40000000001608c9440c0ec80b4f00241394a2fc7aa00005598b03d23ff1978000b8800000000000007930000000ee22e20000000f6000010100000003e927704e800000042d800077081c0000c7892828709a22f89d2519177800036c4001759d1400075329da36085800025685ec6a62c733100000000001ae1c54f081f83830f9ceb62f63f4871c0007221f00000e3a3872da17184523c94530674bce2732cd8b6c68c7ad14804341c03912e38dc066a11c1888bb86e45af2fb0f0027651c19a211c1fa83a1f916840f00003779ecc0005462238dfc46830e2d99ad492400034821a0a70000000000000071e1f1934041e7b80000000ac00000000bb4eb00ff357112c9b6542000
  | 20 => 0x800000003381c4877c00015b00000781b00003638000efa00000000000005a7000000000066f2be86280000000000b5d1647fb2a511bc38c0002959150b7e5180230498aa64882d193d4ecc00000000080000001ae80001cc00000000000006423a3847852c0003868d54a2c00000000000000000000bb032c000000000000000027a000000038a0000100a503170468000d8a159408150067460a1c585888264f716894dc1d843420b841400000028100000000000000000be07a91da80000725fa2b50ce40003ba0000000fa80002bc8e70d5480044c000000000023884b40005ca40f9f787f48940001e44d3a3560000be4d527ff46b80009480000001d54a125b843e02103ec7330959870af878a3e0994897023f0b710700f438d0990f28a5413d00006fc00063328d1e682be4e426a02dc0503f40000798f3c40d349142c3248073da0000d5e09d3229ce8e2c2930bd00000008320ef0fec5cc4aa04d8000fb80000001f30b3e1560d5000093c45b00022711ca15a417044c5827f61108514e78574000018800000000010f4efe6da1dc9c3cdf600028f9edca721c20660000df41871019e481c22693ff0ae417a8081a41ed42a84a00001f5d1006b010d000028401d00016680006530000a94000000000199c00000000000001143d30001b045ba8cb16b00f4786790000000107a446051800000029c07d204c08400041b90190aa2dc0258410e928b109c1ca888400031388a06c080a0100ab0000288000079c00000013f8000faa20a0d99b7cac47a038016f86481d82381b18c6e7120e180010686680980a8c6f2000002907400003a0f8000012400006282b05304c42a60e610a253213a2274d4c8a800010980002634450e90bc0137000000000000000009f861232a2eb226c0000dc00008cd1be0000000000000000438000c0000002c012642020004628000f3861641aa044bf667235b163055c3671419a6051a85f3e7926c31c3f31181a300d05b1047940c60600014c80006da0db000085cee847c17d90a40000001c99b24d666690f68b185fe79742e8e940000003f780003e44a500006dc0008413171f9000000003f97cc8e838435f1df08d868343f809c78c22c27c00000001d10001ef4c0e03610583b46d684b1359b4c8280993428bd049e6a40ea80008447ac3a580009588ab06f097424a0b1195800000050c0001ad00007d93788000fe868025196a40000003708000aee0000001764ac23d60001e0c0003c500000006284d50000c650884e800000001d0431014a1383622e431a1c440008e2394048cc8260646e0548fc640433584489664191c10ad03f667534d89ec61423a24b9b3c44a7bf25d9bcc5864a908d1f18db88ce28a8a502d82510de9a547766fc1659f284ee153111122cdb68a32ca064c6504c9036860cc6
  | 21 => 0x1a88000000015899800037600002c85f45ae037874c97e7e62caa31c43c00008481b05920001a50144ba044c02401ac2520000000528a823fd0a700000b010c00000000007fc0000000d3400026e9e20f300c10001e7c8a030421b09bc3b642712618c05b04c016fa0bc0684c124e8c090bc84312c1380ca07940e81c8407e8743e90634d5052d0d78da000020408a89e00442bc15b800023a00000000001ee71a442a12800030b2e48c3d0d86c326d0350bea68f0d10da874c0002eb99dcbb06a51d4091000070200000008ee40244118803340eb00008643c06f93b39d203d811b435059cc2200018e9c5000072e2b68ba010c000000195cc3c72743b02e50c40003e98000b2c67f44b81cc5ca00010e0de8de84b131e9bc842400000008441165cc178800000000000000008ea0e300000001300f632799348fa3081b71bf400002434b9e048a441f145800000000010b224847288c0ae8f88dea45532616e42ca65f31e0000b22000000000064a7d60c58cf0d7223b3c5853c7468c300490e85945130000c7cfc039b0f116acbf20001678000b767cb1312148f926230961a082044c60a011b491411136f0d10d908c105b0d90d845df36a000008a4620ab800038a35a0000b540340002a48f3c1482490a8933c21e49f0b3170420e7730188e8000e41804499b0f8811827e9fdc3d072b35b9f1504e0e73ee90c019c86329201944aa7f23e396c90160001e415c4e7c4610e2118c5c03d412a092cc543b32bd835ca206460001d0475656907c80009b00001e89da40ce74a1671c60bc62532808d887be6e41829e88d400001b30058d7814d00c21707ec3cc0bf88f4aa08572b39ed865a070342138c6ee64003d80011728de000148c9780001f7800000000000011040000523f0800015017e100055437c6c00a805b48120e242c80006fc0772fc00001e465436b1b3456209700008b89e61ea31d92405c20f1000000068e0000c28ff8a5c0ba3af80cca7c000351800000029701192a00ec2f846a9794e9c4490850df4ec28d4093976c9d60e90fe00006386dd02f1bfca0c3e839e9688e0a0001ed032400008c3b59c0d12a4fc0000000f4c8bb0000eb000054d04a0704c4a592208800089c2e30c8800068285a065803c80a5e80d90000e36600000156000021d00000000003920000000b608a000014bc0005ea0000bc081467c00000003f28e83070000dca00030a87000000b500000000000000e410481ba0000000288afc0000568f383ca7540001a64fd8520000000000030d397a1340004cb1a600000001752619c30890401000000000082d0d4961c0000000000000e8047200000000000000000bf029660c41c8084c0a65812f800074e51e32c9fe4adc2e93cc8f781882953df0b101f0329000129800069f06801310066bd3b
  | 22 => 0xa840000004709860918000346958c0001f40ac00008bc000269800000000024a800103600022f8b6891c000000057098477509f89700005f2234000108c82632a80005540002c69f889600004661cd01261b019b8000da073615499840008b32ad80305027170041aed09279545699c41f6315000141c5340000ea0bdc0000002aa000059a7c80fa800065803c186000020c58406392583ba3500e7a3411587f31db0b510666c402b8af4ef61a32a717fc4bc42d3bb0000b9a00010099cc0003eb2b2000000000026e1604000000054a30824884c06c9ee81ea333368970c6b28294620164000709436814c0b86703f689d833e8160fd0000e107bb00000c84266652b406241665bc26713fc8ae8dd3ab9a4cb5886000009c8eb42ad0cb9cb400059e000000000081215a90f80006491479de0ba27851301be103200009513b40000002af17b80
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1200630001a60289e71481028010020000e58090800600561650211c5534c801a258550b411853254e9120c65508614c801625959d142185320062961d42100614c801a258550840185320051c241641c55354401c0c755d063189514ee9118c8154c625450305c981d9534c951006151d88154d325440184c83209751853000417261754c8614c001ac13260031185200041d660651c5304400145497594734401000709594741c91004001c45651cc7244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa036a0755d06318951
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x4b
  | 7 => 0x4c
  | 8 => 0x4d
  | 9 => 0x4e
  | 10 => 0x124d
  | 11 => 0x138d
  | 12 => 0x94b
  | 13 => 0x94c
  | 14 => 0x94d
  | 15 => 0x94e
  | 16 => 0x124b
  | 17 => 0x124c
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138e
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128c
  | 26 => 0x128d
  | 27 => 0x128e
  | 28 => 0x9cb
  | 29 => 0x9cd
  | 30 => 0x9ce
  | 31 => 0x12cb
  | 32 => 0x12cd
  | 33 => 0x12ce
  | 34 => 0xa4b
  | 35 => 0xa4c
  | 36 => 0xa4d
  | 37 => 0x134b
  | 38 => 0x134c
  | 39 => 0x134d
  | 40 => 0xb0c
  | 41 => 0xb0d
  | 42 => 0xb0e
  | 43 => 0x140c
  | 44 => 0x140d
  | 45 => 0x140e
  | 46 => 0xb4b
  | 47 => 0xb4d
  | 48 => 0xb4e
  | 49 => 0x144b
  | 50 => 0x144d
  | 51 => 0x144e
  | 52 => 0xbcb
  | 53 => 0xbcc
  | 54 => 0xbcd
  | 55 => 0x14cb
  | 56 => 0x14cc
  | 57 => 0x14cd
  | 58 => 0xccd
  | 59 => 0xcce
  | 60 => 0xd4c
  | 61 => 0xd4d
  | 62 => 0xecb
  | 63 => 0xecd
  | 64 => 0x95395
  | 65 => 0x94055
  | 66 => 0x125395
  | 67 => 0x4955
  | 68 => 0x138055
  | 69 => 0x124955
  | 70 => 0x95255
  | 71 => 0x138955
  | 72 => 0xbc953
  | 73 => 0xbc955
  | 74 => 0x94bd5
  | 75 => 0x14c955
  | 76 => 0x954d5
  | 77 => 0x139255
  | 78 => 0xbd393
  | 79 => 0x138bd5
  | 80 => 0x14d395
  | 81 => 0x1394d5
  | 82 => 0x99295
  | 83 => 0xcb
  | 84 => 0x14b
  | 85 => 0xcc995
  | 86 => 0x98cd5
  | 87 => 0x168b
  | 88 => 0x198b
  | 89 => 0x141295
  | 90 => 0x12c9d5
  | 91 => 0x9d2d5
  | 92 => 0x14c
  | 93 => 0xcc9d5
  | 94 => 0x9ccd5
  | 95 => 0x150c
  | 96 => 0x130c
  | 97 => 0x10c
  | 98 => 0x198c
  | 99 => 0x1452d5
  | 100 => 0xa5355
  | 101 => 0xa4bd5
  | 102 => 0x150e
  | 103 => 0x168e
  | 104 => 0x14d355
  | 105 => 0xed355
  | 106 => 0x140b15
  | 107 => 0x24b
  | 108 => 0x2cb
  | 109 => 0x16cb
  | 110 => 0x19cb
  | 111 => 0xcd415
  | 112 => 0x140cd5
  | 113 => 0x144b55
  | 114 => 0x2cc
  | 115 => 0x154c
  | 116 => 0x19cc
  | 117 => 0xcd455
  | 118 => 0x144cd5
  | 119 => 0x20c
  | 120 => 0x14cbd5
  | 121 => 0x20e
  | 122 => 0x154e
  | 123 => 0xecbd5
  | 124 => 0x24e
  | 125 => 0x16ce
  | 126 => 0x8c
  | 127 => 0xeccd5
  | 128 => 0x5cb
  | 129 => 0x44c
  | 130 => 0x17cb
  | 131 => 0x1a4b
  | 132 => 0x1a0c
  | 133 => 0x164c
  | 134 => 0x8e
  | 135 => 0x170e
  | 136 => 0x15ce
  | 137 => 0xce
  | 138 => 0xd0e
  | 139 => 0x24056
  | 140 => 0x199353
  | 141 => 0x11514
  | 142 => 0x104b
  | 143 => 0x19d4d3
  | 144 => 0x145416
  | 145 => 0x140454
  | 146 => 0xb4253
  | 147 => 0xbc253
  | 148 => 0x19c253
  | 149 => 0xbc293
  | 150 => 0x19d4d4
  | 151 => 0xbc2d4
  | 152 => 0x25256
  | 153 => 0x24216
  | 154 => 0x25416
  | 155 => 0x21456
  | 156 => 0x216d6
  | 157 => 0x20256
  | 158 => 0x25556
  | 159 => 0x2cbd4
  | 160 => 0x24b96
  | 161 => 0x21294
  | 162 => 0x252d3
  | 163 => 0x45294
  | 164 => 0x20d14
  | 165 => 0x24e93
  | 166 => 0x21a14
  | 167 => 0x25a53
  | 168 => 0x5c253
  | 169 => 0x44214
  | 170 => 0x5d6d3
  | 171 => 0x257d3
  | 172 => 0x245d3
  | 173 => 0x17c253
  | 174 => 0x17d6d3
  | 175 => 0x45414
  | 176 => 0x5d453
  | 177 => 0x45554
  | 178 => 0x165554
  | 179 => 0x44d14
  | 180 => 0x1a57d3
  | 181 => 0x15353
  | 182 => 0x21416
  | 183 => 0x19cbd3
  | 184 => 0x25456
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1718
  | 6 => 4817
  | 5 => 2281
  | 4 => 18
  | 3 => 1
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (70430+((h/572+packedAt gbK7 (63566+(h % 572)*12) 12) % 2062)*12) 12
  | 6 => packedAt gbK6 (252081+((h/1605+packedAt gbK6 (231216+(h % 1605)*13) 13) % 5781)*14) 14
  | 5 => packedAt gbK5 (143699+((h/760+packedAt gbK5 (134579+(h % 760)*12) 12) % 3011)*13) 13
  | 4 => packedAt gbK4 (1290+((h/6+packedAt gbK4 (1260+(h % 6)*5) 5) % 24)*6) 6
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fe03ff807fffffffff00fff447cff1cc7fe3f
  | 1 => 0x80ffc0fff81f01f803ffffffbbb331e33933ff
  | 2 => 0xffffff00001ffe0003fff03fc3c3c1ffc1c3c7
  | 3 => 0xffffffffe0000003ffffc0fc03fe03fe03f8
  | 4 => 0xfffffffffffffffc000000fffc0003fffc00
  | 5 => 0xff0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1520031800a30a8a38b086690014570c42561b
  | 1 => 0x9042c06b480d21d049551cb219b131611930ed
  | 2 => 0x66f56d00c296ec40926ba21cc2c2c0b7c1c346
  | 3 => 0x24b9b6b596c04801238ecb08ec03ea02ee03b0
  | 4 => 0x40de38c6e718f165c0030010f7e80003b5a800
  | 5 => 0x7810200704008186000c0c20ff7fbdd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36681
namespace PEqualNP.Outside.L_meta_36681
open PEqualNP.Outside.L_meta_36681.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_160 : Interval s2Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 29 := bs4_3_0
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
theorem bs4_4_448 : Interval s4Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 473 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat (concat bs4_4_224 bs4_4_256) (concat bs4_4_288 bs4_4_320)) (concat (concat bs4_4_352 bs4_4_384) (concat bs4_4_416 bs4_4_448))))
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
theorem bs4_5_608 : Interval s4Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 632 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 bs4_5_512) (concat bs4_5_544 (concat bs4_5_576 bs4_5_608)))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 18 := bgb_4_0
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
theorem bgb_5_2272 : Interval gbAtlas 5 2272 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2281 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))))))
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
theorem bgb_6_4800 : Interval gbAtlas 6 4800 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4817 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))))) (concat (concat (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))))) (concat (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))) (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))))))) (concat (concat (concat (concat (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))) (concat (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))))) (concat (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)))) (concat (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424))) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584)))))) (concat (concat (concat (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)) (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))))) (concat (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)))) (concat (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640))) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800))))))))
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
theorem bgb_7_1696 : Interval gbAtlas 7 1696 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1718 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608))) (concat (concat bgb_7_640 (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832))))) (concat (concat (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)))) (concat (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472))) (concat (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568)) (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880eeeaeae0eeaac880
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372960 * 2 ^ 32 + 4004169856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36681.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[0,6]⟩,⟨.or,[2,4]⟩,⟨.and,[3,8]⟩,⟨.or,[3,8]⟩,⟨.or,[1,7]⟩,⟨.and,[2,5]⟩,⟨.or,[0,12]⟩,⟨.or,[9,13]⟩,⟨.and,[10,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4004169856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4004169856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36681

open PEqualNP.Outside.L_meta_36681 in
theorem PEqualNP.Outside.L_meta_36681 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4004169856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4004169856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
