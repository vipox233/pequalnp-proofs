import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36567.Model
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


end PEqualNP.Outside.L_meta_36567.Model

namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
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

def SBf (j : Nat) : Nat := [6, 4, 8, 5, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36567

namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xcd5306501029008003a1610807be43bc43be42bc42bf41bd41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3800221800414610004b94a438f29c851c5350658a4a0ce14141e418041b040043a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
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
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s0K3 (255+((h/3+packedAt s0K3 (243+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 3 => 0xff83fffff803ffff807fffff01fff807ffc7c7
  | 4 => 0xffc1ffffffc01ffff807ffffe03fff807f8f8
  | 5 => 0xf0001ffffffffe0000007ffffffc000007ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x21108259092492588909168b162c5b4b49db5b
  | 2 => 0x422104af424924a952522b40ab56ad95942dad
  | 3 => 0x847609325762393247644dd5819b30c6e6c6c6
  | 4 => 0xe843b1c46473b1c4644771e6cd03c6e0c770f0
  | 5 => 0xf7bde078783c1f878787e78f1e2070707bf00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36567
namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
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
  | 2 => 0x3f80ff03f81fffffe07c1f07c0fc1ffff4923f
  | 3 => 0x3fff0003ffe03f81ff801ff800ffe0f818e3cc
  | 4 => 0xc0000003ffffc001ffffe00000ffff001f03f0
  | 5 => 0xfffffffc00000001ffffffffff0000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80840a000800810001842108461421094124d5
  | 2 => 0x1552946594d52a68f059164688a91ad694922a
  | 3 => 0xa64aa6aaa553b42b76c21bd212cf48e0d8e34c
  | 4 => 0x346cd8d3469a274dbb6f508424f39c431f03b0
  | 5 => 0x3870e0e3871c3871dc739ce7388210841ed800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36567
namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x1500000005234080300000000009223a000202c1c01c009d51b3c300020c39210465c2001e0059142654263494a0a5600f9300201890a0c10010c000010000c202ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x661dc32cc2fca3985f54730ef98e61dd31cc3ee43987d08730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61de318c3b863187dc8630fa10c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef19261dc324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3ee42987d08530fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ee218617e520c2faa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa218778c430ee18861f7210c3e842185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83bc6590770cb20bf28e417d51c83ee43907d08720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53882faa5107bd0a20f621441ef32883bc6510770ca20f619441cc32882fca3107d94620bb28c417d51883eaa3105d54620fb90c41ee21883d843107d08620f210c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483bc6490770c920bfa8a41f751482eea2905f14520fa28a417451483ee42907d08520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ef32083bc6410770c820f619041cc32082fca2105f54420fb90841ee21083d842107d08420f2108417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10ef19621dc32c43ec83887d50710fb18e21f531c43ee43887d08710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10ef19421dc32842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910ef19221dc32443ec82887d50510fb18a21f531443ee42887d08510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810bea90217c52043bc6408770c810bf28821f741043e882087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe528c6faa518f78ca31ee194637e518c7ee8318fd10631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee8298fd10531fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063de320c7b86418df94431fb20863f5410c7be6218fd8c431ee98863f5310c7aa6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43de32c87b86590fdd0721fb20e43f541c87e88390fdcc721fb18e43f531c87e86390df94321bea8643f754c87eca990fd55321fa2a643f753c87eca790fd54f21fa29e43f743c87ec8790fd50f21fa21e43f742c87ec8590fd50b21fa21643f732c87ec6590f58cb21fa99643f432c87a86590fdd4321fb28643f550c87e8a190dfd5221bf2a4437d54886f8a910dfd4e21bf29c43de53886bca710df54e21eea9c435d53886f8a710df54a21f721443ed42887de6510f78ca21ee19443ec32887986510df94621bb28c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53487bea690d7d4d21bf29a437d53486f8a690f714d21ae29a43de32487b86490fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f721043ed42087de6410f78c821ee19043ec32087986410df94421fba0843f641087ea8210fd10421fb98843f631087ea6210fd0c421f790843f621087da4210fd48421bf280437d50087eea810fd95021faaa043f454087eea610fd94c21faa9843f453087ee8610fd90c21faa1843f443087eca410dd94821f329043f742087ec8410f990821faa1043e542087e88410fdcc821f399043f632087ac6410fd4c821fa19043d432087c86410f10c821fba8043f650087eaa010fd14021bf29e817d53d02fca5a05f54b40ef19681dc32d02fca3a05f54740fb90e81f421d02faa9205f94e40bea9c81be439037887205f94a40bea9481be42903788520778ca40ee194817e51902faa3206f90640de20c81f721903e843205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa9281ef52502dea4a05f14940f6292816c52503bc64a0770c940bfa8a81f751502eea2a05f14540fa28a817451503ee42a07d08540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be42103788420778c840ee190817e51103eca2205d94440bea8881f551102eaa2206f90440de20881f721103e842205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19
  | 2 => 0xc00c018010160000381000202c0001b00601c00001000010008000060040d0050000140f0050000240100600e0000080c01204c010160040040580a0100a80081000600efca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e87f651d0eeca3a1df54743faa8e877551d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a17794f42af29e857d53d0bbaa7a15754f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a177d4d42afa9a857c5350bb8a6a15714d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbdc85997b50b32bf28e65f651ccaeca3995f54732faa8e657551ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbbc87197750e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232efaa465de548cbbaa9197715232af29465df428cbbc85197750a32ee21465df518cbbca3197754632ee28c65df508cbbca1197754232ee284657f544cafca8995f55132be2a265ef324cbbc64995fd4532fba8a6577514caf8a2997d14532ba28a657f504caf8a0995fd5032bf2a0657d540caf8a8195f94c32efa1865de430cbba86197710c32bf29065ee420cbda841977cc832f719065dd320cbda64195f94432bea88657e500cafaa01977d5032ef2a065dd540cbb8a8197794832af29065ce520cbbe84197790832e721065dd420cb9a84197710832efa8865de510cbbaa2197714432efa8065de500cbbaa0197714032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0fb94b41b7296837d52d07daa5a0db54b41ef19683dc32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea9483de32907b86520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941ef19283dc32507ee82a0ef90541bfa82837c50506fca820df94c41bea98837e52106faa420f78c841ee190837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef19663dc32cc7ec8398fd50731bf286637d50cc6fea918df95231beaa4637c548c6faa718f790e31eea1c637
  | 3 => 0x6aa1c4dececed85037c040c7ace292000c31d32eccb0862d407cb2c061a9296001a40002f41ec19000324001829910326bc0000039e3d55e8000000000002c000b8c3b0000224d8e815d0006219880012c0000000037a374fb08a35a16c000000000004d0000009984810b0c00007688e03800000000000c440000029a5c000160000990000bb2bc0e14d020000495b2b161284e40036304ad7976b0d0000000005e0d0758002d25beb6c428d13844b4cab0b264ad0f809b614c259f800000001053773fa0000025654869d3f0000001f91c11a4361f46c0c36c8900003590c400000000000000fa9190000000027c00029412000000864c1a3749200000000488ba9a52dc634000000004d47f16d18225ca39138c51025ed4413453a0010085658849da2997442328478f25c46fd50b496f25b5ab27403abec89abf3c66e45501541e31d9a9b6052a40e20703c25910a1fe254abc4b91f5e61e5589c53360f4cca5439a3107ea8b15e3ec0029223c4f5130004100000002b00072c7c198646a8caa88631697cc82050007cc002fe08e5fd8c28551a518a289d4720005e29c0dad687520016aa5d1828a6d49e87432b146dbc6dac25ceb607f0fc0a829943b212fa92190009572c0da78b35601fcf41e74e60cc8d99c1e8a814c9f8512600748e754aa0cbc8e01dc6cd558e54b637c139440aa564112b53d40005b35546a10cd92e526673818ad71c2194590000009dd5615f5b2398d40375f8ae8000001e67c9a0b532e2c945824a398365212c500a76594a9b00077d4a0004c6c782900064eacd17800000a8916b462b4001a192c0780000000053eab4800c00007704580000000024800000001722c00002e04f23d5ea001ada095781855b23e000d2d099d46321b0ab9104da33435a840003780018963807814000000001b59ed48a404460781fe060a10003d8cd98700b000000008008060080140001600c0040300600201c008040020040080d00800c0100f010010018030021180100c068040030040000080080a002000058010040780a801002024050040080380000401c00401803000034000020000540080700207000007002014000000020040200a00804401001000010000020080080d80000a05003806004004038030020000000b01a0040201b05a014000060060000200101c0000000300600002001002008000050020000000503a038020050060000500400a0000000000800802001004010000050040140900d00001c0100901600002817012088000000080040400200c00c00005002008028010100080100100000c00802000000078190100180080000c0040000700e0040800100200c02001004000000000040080000000200400809006014010000000040000501c0040000100a0701101600001c030000060040000d0
  | 4 => 0xb000000077000000ce8c93b0d89b034d0ba001a894a0026dc721a348e7e431b2d2900010eaf0000b757a000474c6d092601c69e4002de100448ab0c1206598b7000000d84002a8242af895943000be800000000a05123390549055bb06610000a0800000c1d058340006ec2e1e43809414b1282ea9a49fae962e0017c8005fe12149b145e4000f88c61a4aed801a52465d10fa613f60c05107a65c14454a2551e000c62292305a0ae00e260489731846e061c050006dc12c88951000001070001d80015c0003f49a19780000000000000000bf44c000564755af80d4b020c68375000bdd0f2804fe58ca026c0002f800000604b40b0a670000003e000228a60002652760000001b000cf40f972000000000006a00846b0003289ec420003b4190520d7354704020005a20008b257262000000006ae0000000006c7191882e34456daa0000000008e0531b4108dd00047e420438ad3cc2546e1b82482ad0600009a001ae85f0000000019e46624d661f70b400000091698000aa21800000000069000000002755d684157000150658001ab3a270c1d8000009495511d3ca93148a4e0ae2648722a00041c69b47440da4001055aa1b93818a24c809388002ce5a567b420008c8000b40002f4560004d64bcbf0c26e402c0986a33e90c0017c4bc00174023000ce00010f0001bc2799a0004f91130f2a6a19020000048f125a1a1106c1b610449e3d8d884142a80db683a422c8884a622ca2c47cb1052a0000000000027c0002629ec55941770005ac0a22b63e0004e366006aa4491e250464c78b6747678033000278cf8f4b3c3023bd7b22c680bc5ae13a000110d200059a71c079c86a40007bac931c818d01b520c11969ae0270970538000009342016258e2dd2c82d30a000f70351a85399ba5d5869c844b340102b8c68e22de75cbc0751e0429773686e81ccfa2d6000d386420d2e600000000000d10000a06f0a9c0000000cc0467a3653c0000022e4fa00189800000ce8ef000368000f58003420000033207e001820673fe5401c8cc05e0000031200000123000000b8426152000000001c90000000014766600000074000c990b31d58c0000b0006ec000001026488d000000000000de000654000000ba0009680d0b9000954469ae000001862ec3a49e0b50000b2000001350006b00026e104be0000ce2b0a98b60bf2407290394c1f40014604509c944003735de775640170004340000000069911b30000dc400000000048658000002848baca5824dd142531d601c0004a42e000f78714ec454948726b
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x520082ac6448020b318d20082e461480209ed9520082b864480209798f54c425d63d53109b98b54c426d62d53109798e54c425d63953109b98a54c426d62953108f99353c423d64d4f109b98b53c426d62d4f108f99352c423d64d4b109798f52c425d63d4b1097d8d52c425c6354b10d394832c434d520cb10b558e41c4354534c710b918931c43665208710d954821c43c4320871097d8d548425c63552109798c548425d63152109b988548426d62152109b98b538426d62d4e109798f528425d63d4a1097d8d528425c6354a10d3948328434d520ca10b598f41842e662d0610d5d4c318436652c8610d914821843c432086108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544427761551108f99454443356115110c7d53534431c54d4d109798b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d109798853443556114d109798f524425d63d4910cbd53524432c54d4910d3d4f524434c53d4910d398f524434d63d4910d9587524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524427461149109b994524432f5414910cb150524434f5314910d314c524434f6314910d318c5244367611491097996324425c658c910c7d52324431c548c910d3d4a324434c528c91097994324425c650c910c7d50324431c540c910d3d48324434c520c9109d99641443345490510b558e41443545390510d914a41442746550510cd15141443545350510d91494144276658c510cd1523144354538c510d914a3144274654c510cd1513144354534c510b91893144364524c5109d997214433754c8510cd153214435753c8510d514f214436452c8510cdd5021443345408510d5d4c21443545308510d9d4821443645208510f10c821443345484110d514e104436452841109798f540425d63d50109798c540425d63150109b988540426d62150109d984540425d6594c109798a530426f6254c109b18953042cc6254c10d3d89530425c6254c10d3189530424c6254c10d5185530425e6314c109d984530425e63d48109758f520427661d481097d8d520425c63548109dd85520423e64148108f590520425e63148109758c520425f658c81097596320425f650c81097594320434f520c810d3148320427565d0410b598f410435553d0410b998b41042756510410d554c410427565cc410d554f3104275650c410d554c310435653c8410d554f21042756508410d594c21043555308410d994821043c43208410d554f100427965840109dd9510042b46444010b518d10043555344010b9189100427b6544010
  | 1 => 0xc355518c430d5544310c27765c84309d597210c27765084309d594210c3c43208430d5547300c25f654c030a7191300c2cc624c030b5185300c355514c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63953209758e54c827661953209d58654c823e64d4f208f59353c827661d4f209d58753c82766194f209d58653c82e86050b209798e51c825d6394720f10c821c82e96210320ea90840c825e63d52209758f548827661d52209d587548825e63152209758c548827661152209d584548827661d4e209d587538834f6254e209d98453882756114e20b398f42882e661d0a20b9987328834d530ca20b3594328834d650ca20d3d50328834d540ca20d30ca51883565394620d554e51883c43294620d9cca51883563294620d50ca51883643294620d10ca51883565354620d554d51883c43254620d58c951883543254620d594f218835553c8620f10cb21882ce6388620d394e218834e5308620d954421883565308620d554c21883c63208620f10c821882e56508620d959421883675408620d955021883665308620f194c21883465308620f154c218836453086208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551209ed81544823e6515120cb588544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d2097988534825c6214d209b996424832c5490920d314e424826c6550920cb151424834c5350920ba181424825e658c920c7d52324831c548c92097994324831f540c920c7150324833754d4520cd153514835753d4520d514f514835632d4520d50cb51483375414520cd15051483575314520d514c51483664214520d950851483563214520d50c8514827665c8520cdd53214833454c8520d5d4f214835453c85209d99421483375408520cd15021483575308520d514c21483c43208520ce153204832c5488120d314e2048364518812097d8d540825c63550209dd85540827461550209798c540825d63150209b988540827661150209d58454082776154c209d185530823e6414c208f59053082766114c209d584530826d65d0820b398f42082e661d08209b59442082e661cc820b398a320826d650c820d3994320834d650c820d3d50320834d540c820f298032083c9600c820d30ca510825f63544209718d51083c432c8420b398e21082e66188420f18c821083c43208420d9d5021083655408420d994c21083645308420f898021083e160084209798e500825d6394020d30ca50083642194020f20cb40083e021d00209e59440083a84210020f20c840083e02110020f20ca20083e021880209bd9
  | 2 => 0x52c8540d914b215027665085409d19421503575308540d514c21503675208540d914821503c43208540da14b405031c5390140cb14a405033451901409798a531025c6254c40c754e43102b66190c40d394e521034d5394840d3d8e521034c6394840d9d865210364619484097d8d521025c63548409dd8552102746154840d394d521034d5354840d3d8d521034c6354840d9d8552103646154840da181521032d529084097d96321025d658c840d394a321034d528c84097d94321025d650c840d3948321034d520c840e390832103565394440d554e51103665294440d954a51102766294440d58ca51103543294440d594d51103555354440d9949511036552544409d18951103563254440d50c9511029e6390440cd546411027765c84409d597211035653c8440d554f211036652c8440d954b211027765084409d59421103565308440d554c21103665208440d954821103a64208440f10c8211023f6550040a718d40102ac6250040ad185401027b6550040ba189401026e62d53309b58b54cc27661d53309d58754cc26e62953309b58a54cc27661953309d58654cc2d56190f309dd8552cc2746154b30d394832cc34d520cb30b318931cc3665208730d954821cc3c432087309dd85548c27461552309b988548c26d62152309d984548c2756115230b398b438c2d661d0e309dd85528c2746154a30d394a328c3665208630d9548218c3c432086308f992544c26e62951309b58a544c27661951309d586544c25f63551309bd89544c26c62551309dd85544c27461551308f994544c31d631513097996434c31c5490d30b5586434c25c6550d30c7151434c27661d49309d587524c32f54d4930cb153524c36661d4930d9587524c32f5414930cb150524c34f6314930d390c524c34d4314930d9d84524c3646114930c7d52324c31c548c930d314a324c31f540c930c7150324c34f520c930cdd53514c33454d4530d9d4b514c36452d45309d98b514c35632d4530d50cb514c3375414530cd150514c3675214530d9148514c3564314530d550c514c2766214530d58c8514c354321453097997314c31c54cc530d314b314c35451cc530c7151314c2cc624c530d3149314c354514c5309d997214c27465c8530cdd53214c33454c8530d9d4b214c36452c85309d994214c2746508530cdd50214c3345408530d9d48214c3645208530f10c8214c31c548c130d314a304c354518c1309d987540c27561d50309798c540c26e62150309b588540c27661150309d584540c25d65d0c30b398b430c2d661d0c3097594430c27761548309d185520c34e520c8309d98a510c3563294430d50ca510c26f62544309b189510c2e46254430d5d0d510c3544354430d9d89510c2746254430d9189510c2646254430d58c9510c354325443097596310
  | 3 => 0x421f10cb3108675658c421b958a31087c4328c421d514d31086e7624c421f10c93108675650c421d554c31087c4320c421b598e21086d56388421f10ca210866f6548421b318d21086776548421b5d8d21086d46348421f10c9210874c32940218fd91500863c645402197d8d500865c6354021b598f54086d563d5021b998b54086d66395021b558e54087355415021b998854086b664d4c21ad59353086e662d4c21d554c53086e66214c219d997430867565d0c21b998b43086e562d0c219d99643086756590c21b9d8943086e46250c21b998843086e56210c21d998a52086e56494821b998e52086e660948219d59742086d663d0821b558f42086e76590821b959642086e56490821e995242087a55490821b998e42086e660908219dd9542086d76350821b518d42086f36050821bc18142086e76550821d9d9542087a76450821f1d8d42086e46350821f118d42086c46350821f8d8142086e46050821f818142086e06050821b9988420867565cc821b9597320876565cc821b9d9332086e564cc821b998332086e6628c821b598a32086c6628c821d594a32087c6528c821f190a32087c5428c8219dd9532087c5320c821b598832087c6620c821d594832087c6520c821f1d0832087c6420c821f150832087c4420c821b9d9432086e5650c821b9d9032086e5640c821b998c32087c6630c821f194c32087c5530c821f1d0c32087c6430c821f150c32087c4430c821b998032087c7650c821f199432087c5650c821f119432087c7640c821f199032087c5640c821f119032087c7540c821f195032087c5540c821f115032087c7600c821f198032087c5600c821f118032087c432d4021f10ca50086b76454021ad19150086d76354021b518d50087c43254021ad99050086b56414021b598c50086d56314021f10c850086766194f409d58653d025f6354b409718d52d02776154b409d18552d034e520cb40d354832d025e63947409758e51d03665208740d954821d03c432087409bd89539026c6254e409dd8553902746154e40ad986439025f6354a409718d52902776154a409d185529038e420ca4097d8d519025c63546409bd89519026c6254640a798e41903a64208640f10c8219025e62d4d4097988535025e63d49409758f525027661d49409d587525034f53d4940d314f525034e63d4940d358f525036661d4940d9587525034f5314940d314c525034f6314940d318c52503676114940d9184525025e658c94097196325034f528c940d314a325025e650c94097194325034f520c940d3148325035753d4540d514f515036752d4540d914b515027662d4540d58cb515035432d4540d5d4c51503545314540d9d48515036452145409d98851503563214540d50c8515027665c85409d197215035753c8540d514f2150367
  | 4 => 0x758f525074f520c941d314832506d663d0541b998b415065e63141419758c505065f63548419718d521074e520c841d354832106d563904418fd954110677655044197d8d501065c63540419bd89501066c62540419b98854cc66d6215331b398b43cc6d661d0f31d394832cc74d520cb31b558e41cc66e62152319b588548c6d56190e31d394a328c6d663d0631b998b418c65d63951319b98a544c66d62951319d586544c66f62551319b189544c67b60551319e181544c65e65d0d31b398b434c6d661d0d3197994434c76561d4931d3d8c524c74f4314931d310c524c7676114931d314a324c6d6618c931d3d48324c67665d0531b598f414c6e662d0531d914b414c6766510531d9148414c76452cc531d314a314c65e63d50319d987540c66e62950319b58a540c65d6590c31b5586430c65f6550c31d3948320c6d5610c8319d596410c6d563904319dd95410c6d5638c43197d95310c6cc624c4319dd95310c6e4624c431b5d95310c757654c431b5d91310c6d5644c431d5951310c754544c431f1d89310c6d4624c431f1189310c6c4624c431d5949310c6d4604c4318fd91500c63c64540319bd89500c66c6254031d54c5500c65f63553219718d54c865e63153219758c54c863e6414f218f59053c86d663d0721b558f41c86d66390721b558e41c87365450721d594d31c8757530c7219798e50c865d6394321b998b54c87375495321b5d8d54c86d46355321b598c54c86d56315321b998854c86e662d4f21d5d4e53c86b66414f21ad59053c86e66214f219d99743c867565d0f21b998b43c86e562d0f219d99643c86756590f21b598f42c86d563d0b21b5d8d42c86d46350b21bcd8142c86f06050b21e950842c87c6620cb21f190832c87c5420cb21ad99350c86b564d4321b598f50c86d563d4321b598e50c86d563943219798f548865d63d52219e983548867960d52219798c548865d6315221d3d89538874e5390a21cb95142886cc6350a21d394d42886e86050a21d354c32886cd650ca21d3594328874f540ca21d3550328875653c8621d554f218874c32942219798e544865d63951219b58a5448675619512197d8d544865c63551219dd85544867b60551219e181544865e6394d219d586534866f6254d219dd85534865e6514d2197996324865e650c921d5d4f214875453c8521d314e214865e63d50219758f540865e63950219758e540863e64d4c218f593530866d6590821b318d42086e76150821ba18142086e561cc821b398a320866d650c821d3994320874d650c821d3d50320874d540c821f198432087c5610c8219798e510865d6394421d30ca51086d663d0421b558f41086e562d0421f10cb41086756590421b598e41086d56390421f10ca41087c432504219d59441087355410421b958841087c43210
  | 5 => 0x5390ace63d0a42b99874290a5f63546429718d5190a5e63942429758e5090a7661942429d5865090b4d62d4d42b398f4250ae661d0942d5d4f5150b5453d4542d5d4c5150b545314542d6d4f5050b5853d4142dcd475050b7051d4142d6d4c5050b585314142dcd445050b705114142dad085050b3a42141429d9865310a756194c428fd954210ab860508429bd954210ae860508429798e5110a5d639444297d8d5010a5c63540429dd855010a7461540429d98754cca7561d53329e98354cca7960d53329d98454cca756115332cb95142ccae46150b32ba18142ccb664294732d950a51cca7761552329d185548ca7661152329d584548cad661d0e32b5587438cad66190e32b5586438cb1e5450e32b5987328cad561cca329d986508ca756194232b398b548cb1f5495232b5d85548cad46155232b3988548cad66115232b5584548cad661d0a32b5587428cad76150a32b5185428cadb6050a32b6181428cb8d4210a32d5d46518ca9e6414632a7590518ca9e64d4232a7593508cad661d4232b5587508cad66194232b5586508ca5d63951329b58a544ca7661951329d586544ca5f63551329dd85544ca7461551329ed81544ca786055132d58cb514cb673214532d58c8514ca7661d50329d587540ca7661950329d586540cacd62d0c32b5987430cad561d0c3297596430cad66190c32b5586430ca5d6510c32c7550430cacd6210c329b596420cacf6350832b9185420cae86050832b5987320cad561cc83297d95320cad7614c832b5185320ca6f654c832b9185320ca3f64540328f191500ca7761540329d185500cace62d5032b5987540cad561d5032b5986540cad56195032c7550540cace6215032d398a520cacd6494832b3986520cace609483297597420cad661d0832b5587420cacf6590832b3596420cacd6490832e3952420cb8d5490832b3986420cace609083297d95420cad76150832b5185420cadb6050832b6181420cacf6550832d3d95420cb8f6450832f1d85420cacc6150832f1185420cac46150832f2d81420cacc6050832f2181420cac86050832b3988420ca9e64d4432a7593510cb555114432a7d91500ca9c6454032b5d85500cad46154032a7990500ca9d6414032b5984500cad561140329798a53d07556194f419718953d074e5394b41d354e52d074f6394b41d318e52d07676194b4197d8d52d065c6354b41d394d52d074d5354b41d3d8d52d074c6354b41d9d8552d065f658cb419759632d074e528cb41d354a32d065f650cb419759432d074e520cb41d354832d065e6294e419bd89539066c6254e41b3189539074f6254e4197189539074c6254e419318953907546154e4197d8d529065c6354a4197d96329065d658ca4197d94329065d650ca41b598f419075553d0641b998b419065e63d49419
  | 6 => 0xd00000112989f8e199e9419d8a9b1d8017930039a461ad80000012907a10002e93d10f84027a13fa5880f0418c30558ea80000017c92c0990bf80006087b00c29614a94480020b8a69fc16d963871a360000aba9d03210380017da348a31e213b0269af248918011a8518d9c9187a681bc942214268851801a2f17227198313793e8e4a198319b61b7819809a1f0e92991509b80959b681881f14885ba40a8c9798a98081008001790000da0000661439b503f00012a80027f104000000000809008008058030120040280000203c0502300e000008020020000100001201800014022018000010020780100c01e0200600b002028028030080100080202801c000000020500002d0060140100b000050000010100000900001c0041f00a0300580401000e00000005000070010060000600300c002004008090080000080300e09c0600d00800c0400101c00c01007000014028050080580200100c000010000160001480100200c008000120141000f00c020048000180000080500000402011014044198050000340480000800006802034018008060080380702a00003801001026020008000020280080200a0040000b01406407002004058018000180000002500201000011004000000010280680080100a0000d0050060040a0020060000000200c0000480001400413003020008098070020200000700401c000000020000400003c0200181400a04400002004010000030020240100100200408000004004010000040000200100601400005000000048000020380c80001e00c080000020440100102401c040050200380a00500005c0082f00602400000016000000070020000000a00a0180180f0200080300100c00c0380607203c038000000000b8000001a006018010014000010020301100100200000001004000018220440380001501a0081180205000409001006000088000060780201400c0080080001a00c01000000018040050300040101c00800c0400500208c0000e02000016800000018008000060100080000002400001016000118000060b4020030020180380002a0340100000602c028010000001782d004000000000000040182902e00400807d3d8e52d0f676194b43d918652d0e776154b439d18552d0f676154b43d918552d0f665294743d954a51d0e766294743d994951d0f6552547439d18951d0ece62d0e43b59874390e776154a439d1855290e7662946439bd895190e6c6254643b91895190f574354643d9d895190e746254643d91895190e646254643b398b4350ed661d0d439d9875250e7561d49439d9845050e756114143b55864310e3f6550c4397d954310e7761548439d1855210e6f62540439b1895010e7761540439d1855010f565394742d554e51d0b565354742d554d51d0a776154e429d185
  | 7 => 0x2506800000000000004424314787f880a9d8000000002081099d580000024700007f06698a0858eb000218a909f49759ec98f9218ef00009e80024992ea7e87780001c0e096ba8d24699ba2b8002788001e88001f713980003a8481328000fc9bd9fd89480021619c062000264a760b98001c829c1fba95a4284480017507d9a21d196f19a1ae1ca04a8000278531f926288912f80b800000000000102933a6f0001a526308d02da4b1988f49cd1370002400ada969840d30c01dfa4b8759b42979f68ae8f19e48699c0a7285f128952a3c1b8969032a601e29eb800000000013286a07a7d10ba0a23511b1e390d00000000022627d8000001da15c8df97e8458000df1dd8272291fb05e0b60370d485493b9082691270921e58cd000000138a3f0000ac9ee80000006b2060001939331d698e28e0110001070cf964a558d0a502151788c501d80512e25999e0c0a6100021a0b58000001468002102090000000d61c2a6b800083862873a910709c50850a016fa9182f25500016d11107aa5700021d8001850000000ed0350c299d800263a52a4c9859770561e098e80026c1051a39ac17c2411560d389c8cf21700010a96600017f1ed95a0298570b0a3e1591741b28000601158001170000dc0000000002822861a88001281df12a0ef96b0001ea06a1ab0129139568f900025a8a599029a8dd25fa1580011984e23912b2849ef821a318ca8069e197a14d25094100001005a98b8000001a59390c128822100014c0290000d800000000000026980080018d05a14e84a15e9258169a71c0251872815a178f10b90a208e1e11619780ba0000580e980028700008ba6e8a79aaa759109d91768829f605d1d28470bd888a1809a19ca2a24203d991984a132541278000b41e81571030fc08a19f1492829d083c89a8690000002791cd8000d19de03f8dd8c91da8f70d79021e703c03419080028e8e600015d97e14425b2378b209601e0500242222898001a09ab9a68000208001160000000fa15f84b00017b8d98048928138151b71979309f80a401d0db89196522d9760d91ae8002938c61ee00000000001a89f00013406c00029323ea001b30ec9e607900015e0001a180006f1f291f1c5a921cc17fa1c8ea14f8be88109417a84e9549d7a320a70089810000002120001a121106d1800280db2980f603000000026a04b8cc13f0001738818000000000d228d8e68c88001962011ed0429c726715580013c22f8f2000219281a8f2901898000001c1a8388ca030cc9ff2569188b28e2a8a91c17084108303b0391fe04d299a5b87c8670d5a6220722000019a97d01f8bca7301600c8e300e25d9700002740598a51520002779f78a1014a748e798c8308000c422b000000188800159a5204c1f98a8940a858000000000bb80027c0020000798b714b9a
  | 8 => 0x3801707c20f08ea2883b8be04221b12b8de05c853a139d48d11829869870c68f580024c14e0aa91ca8118f0001671f30978001061d2122046a0f904996a1e2228d724f00027c94d8930ce0641698001e9a988000911148109540000ff1230ee17280026e20d2679eb1f00b38001c100000025622523fa9493a9a29bb8000c99680cda018899ec1b99882512049aa27a89b0f02710a09db96280029a2591a315183e24f8f28000001839860e3a5c91fa5d00028c13a26d8fe8000bf068a4820219203309d8ac14a22c27980781200a212a3b8701981b91c79bfa7b24e8820041f39fa0000748ffa7b8200002459f40190000939d3a0080000015d0000000001d99151118000f807e8000000000a81ce9141659100509481c89a81e000a8000c5a5e8059011910000eea27a7f80f80000606502e22e8002338578001f51afa809929ce0338840e208c16e8349ba8f090c96026b06e0000002970529c39d600014706486185b1bc229a050900522709260001d51228fb26f940105a3a225a5e040a2094b056a6d1bd0001668000000fd8000000a180023d934a040b685f9c202b81a1380231358a620e0ad02d0028fba3c90b0001821940000000541641c9a2806a8c79350378b327223d0bd0c38ca2068000001a4a768000638000000001bb10f00727519b0752940972109b20000000000f30c206e8e100e9689ef1c41ba0b7a0382f8de88b0ed9611c61dd000000265a1a849a6687124d02b2309fd00d9f113698aa2a8590001de8000438b193e1b59f080012686c92d09984794303690e93d8e89cb83820c28f92ca5a29ba328d6a4a20d87b80006fa2300007884519928b8e52661fa92d80010916315c0a900027e0000732700001f19b386d81418b13c8b50b014600000002a0b10000a280010a00025309522c8000000001d30000359732538000ab09d1551d107700022e1069e782215b93623683ea6c8260f39210002439a90b823108f0e00a4a2680b17111e1a98000c489c00015305c0e72300430e41b08d289e1be00028b13111a88d8881e69078f792084f1c69948baa330001318eb90d8000000e58c71e40001ffa57876223a3588f81b00d00007e0000cea088ae29c8659be8fd1c30000389320000000001a002100018c27719d0038229452888f521fa651588002271b18740b4a2182c0000001cfa0ca4199706b8001c4a6094c8001cc880000205a3aa4d971a61a0285881ca1d24910c2580b88630248d428a01ba2409088611d8679b48fe04f8dca841cb12411229505da38a7398196c9bf2169caa449ac8aa11a0258e823995b0f99f2084a0996e1238faa1b84d92508710e00000023411d15f0d017b0f688a9999dc12f1b00180000981d41500489b111900018900024aa0ea928289db1130720001a78001ea8238768090031f895796a
  | 9 => 0x25c21c12485515111ba1e85116080002c800116a370611d011780022d1e514296a80000014f0af0a38c80cba11a47a801dc8001018878000c180004923b0d50d880000004c83d096a440000f89fea5f0001201fc81e9580af9a61459621e900026a977a4e0782781d71678002892249f582a9748460bb25483a19f89b9952640bc1932450ec0cb1958da91e96c20a85e953a0b2149809cf1e31088868310988f42830361499a415a91280000028787d2
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x10c4d76d50320866239ac5a0843315d832d0421988e6b108210e45650c84108782aa06420843515d4320c421988e4b1ca810cc473592520866339cc129043319ce6090821d80c7b028410e63651814208751b20c0a1043b0d8c6050821d80c63028410ce270d9332086e03828519043315db420c821a8aeba106410dc37050832086e03828419043295d3650c8218caebb206410d4575d0c3208662bb08619043a1590430c821b0ce9b286410d8574d9432086c33a4ca19043615d2650c821c8aca3286410d4675d9032086a2baec819043519d6640c821a8aeb3206410e856419032086633b6a819043315db540c82198ced2a06410cc5769503208782aa0a81904351dd5600c821b0ee8b006410d847458032086c33a0c019043615d0600c82198cec192a010e87640c9500874232064a8043a19903214021d0ac8190a010c647258653d02a238aa419681131c96394740a88e6a9043a0646639875250322318c229281519c7520c940c8cc4196a2a054672d4c21502a339ea410a81519d43208540a88ea19042a0646650c821503223286410a819118c6194840c88c630aa420648631815210330308c0a9081511c5520c840c1acb2106420644620c951102a2392a610881511cd5208440c4acb2104220547750c821102a2ba8641088191d943208440c8aca19042204c47258643cc2a238aa419661199cb6155230c28a8b0c86984c472586434c2a2b8c8629261519c7520c930c8cc4196a29860c54189314c322310a298a61919943208530e0ea81904298704540c8214c232392c3aa061519cb4354430c8ee6312a21864473189510c323a18c4a88619110c6254430c88c5192a218644620c9510c2a2392a318861511c9510c430c8eca190421854472547300c30a322a298061511c9514c030c88c4a8a601854671d5032882a339ea810c418a1506050920c90a630284905607050851482a33a86410a41919943208520e0ea81904290704540c821482a238aca19041511c5540c820b10e8b006410544735502108292ba0a610841681d16008420c8cc610ca010649650c84008330b284220041311c96390710c88a631263885447354821c4227396c6aa421519cb530c610a88e4b08a68854471148324430a2a2c720a21311c963905108aaec29c82886456314a41443122a0c498a219114c624c5108c8ec292628854672d4c21442a339ea410a21519d43208510a88ea1904288707540c821443822a06410a21131c963d5010c8ee2312a608644711895304322310c2a9821519c7520c81089aec290640850d74148320422bbb2a7a0821511c953d0410c8aa731682085447254c41042a2392a798821511c9530c410a88e4a9e42085447254c21042a3ba86410821511c953c40108a8eca9a20086146454d10042a2392a6880219154c6244010
  | 1 => 0x191a7e000f8960059001b0460006800b9100011ecc57000b2bf2500066005100028a13a8653e4d2bb0d921140a6400c567a69a200458a800c74e9d0da7f20000620032b18003613870f47610ae8fa5d0000050c41f9c01cc83529d94aa1d0b00079248000000001ac8800530007035158e55ebb5619d364f6e07d0c605991caa544a800823c4880000001a13844000021cac000017c003236161a00000000cc6e001ccf68a30804f0426901c16a35a11404290836cc4895b87500be26294d28813001bc0d5e024467249b5dc40c4c10d62ad0027800b00006c90e0000580600000000000021a1a81516b4c146f170dc3cdd4e3000013000000000668019690079491863122519c000424800e15c061aaa000170245300308e2005200000a900168ee000020c003d2d80000c1322ac0000002156aa8471f1b22f28ad860df6d0ed04972f05ca0bd42259ac00128000a000000e0107800082907804000000840080200810040d010441200000280a02000100203030200403010044c020080c02040301000140000014000f8040800010040c0d0003400020100000030105c000e0480800040654672d0d5190f23b98c4a8c87911cc6254643c8e86312a321c64725845050e62392c321887529cf4214142ac4e3a10a0a162a5418142ccab03828528e65319cb6155232b10e0a1085194c47158b430ca6238ac421865311c96195032988e2b24a4194c671982520ca6338cc121065b01876050832c96ca302841968b64181420cb61b08c0a1065b01846050832a88e4b0ca7a0e47711895390722388c4a9c83911886154e41a88e4a9e8320e455398b4190626392c628283311c96390441988e4b1c8398cc472586438c6873a6c629263519c74314931a4ce9b08a498e4452986324c723318a5a0a63311c96190c31988e4b1c8218cc472591310c668382c898863159da544c431a8ce52a26218e4765189310c723ba8c49886391950624c431c88a83126218e4462949310c70a32262a8063511c93154031c88c498aa018cc672d8d54c86a3396a729e43681c14210b21b80e0a106590e2a541814288725298c0a1443529c3540ca21a1ae932864
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc014ed0000149060100064000b500018005a0684dcc6254643a0684dc46254e41a0684dd4624c43184687950624c431c04641c93154031c04541c96190d30a0684dcc6254430c04641c9514c030c04541c963905108448758c5290510a0684dc46254c108448754e62d0410c04641c953440108448754c6244010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
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
  | 6 => packedAt s2K6 (788+((h/14+packedAt s2K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s2K5 (27286+((h/296+packedAt s2K5 (24030+(h % 296)*11) 11) % 1175)*11) 11
  | 4 => packedAt s2K4 (55826+((h/446+packedAt s2K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s2K3 (11798+((h/75+packedAt s2K3 (11123+(h % 75)*9) 9) % 300)*9) 9
  | 2 => packedAt s2K2 (860+((h/4+packedAt s2K2 (840+(h % 4)*5) 5) % 24)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 1 => 0xf80ff01fc07f03fffe0f81f07e03f03ff64cc7
  | 3 => 0xfffe0007ffffffff001ff8003fffff870ff
  | 4 => 0xfff00000007ffc0ffffffe000003ffc0ff80f8
  | 5 => 0xffffffffff80000ffffffffffffc0000ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x86091428401082080318a308a38b24902955b
  | 1 => 0x52a5a4c51cb239479606a8d46c49563a764cc5
  | 3 => 0x45494289a954528b2ad0416d20926cb4b870ae
  | 4 => 0x618d8b163668a0edcd6b6c0849238f18df80f0
  | 5 => 0x860e0c183870c30e718c718e71c00820ed6a00
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaaa008800eeaaaaaaaa008800eeaaaaaaaa008800eeaaaaaaaa008800eeaaaaaaaa008800eeaaaaaaaa008800eeaaaaaaaa008800eeaaaaaaaa008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36567
namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd431
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | 3 => packedAt s3K3 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (17+((h/1+packedAt s3K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 1 => 0xe03f01fff03f03ff0f81e0fc0fff07c0ecb3cc
  | 2 => 0xffc001fffffffffff001ff000ffffffff0c3ff
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2284100460821040118a211462884a4a051615
  | 1 => 0x498a72c8a39455cb06a8e8d8a5b946866cb2cc
  | 2 => 0x8512a5510528c29560415a4109529534b0c16a
  | 4 => 0x162cd9a24a0e9b66bb6c10924e6ce218df03b0
  | 5 => 0x1830e1c38c30e3b8cc719ce380708420fae800
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaaaaae0e0a0a0eaeaaaaae0e0a0a0eaeaaaaae0e0a0a0eaeaaaaae0e0a0a0eaeaaaaae0e0a0a0eaeaaaaae0e0a0a0eaeaaaaae0e0a0a0eaeaaaaae0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36567
namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x200001007118050046350bf42bd42f731de31dc31f431d431be40bc40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x80006a04c02e080ab28c6396540c72aa818e5d0831caa106394319025aa420650c440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x45800000a158a540c61565d0831855943110305520c440
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
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
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (156+((h/3+packedAt s4K4 (144+(h % 3)*4) 4) % 14)*5) 5
  | 3 => packedAt s4K3 (224+((h/2+packedAt s4K3 (216+(h % 2)*4) 4) % 13)*4) 4
  | 2 => packedAt s4K2 (156+((h/1+packedAt s4K2 (152+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 1 => 0x80fc0fff81ffc1ff0f83c1f03ff87f81d2ce7c
  | 2 => 0xff000ffffe0ffffff003fe003fff87ffe30f8f
  | 3 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8a10002304008000118442118a0088940450b5
  | 1 => 0x262996451ca512cb06a1d1a296c8550cd2c65c
  | 2 => 0x144aaa88286a31556042b48425550669630b0a
  | 3 => 0x58b34d125143a5a6bb68210939a66031bc0de0
  | 5 => 0x60c38e1c618c39f8cc7339ce01c44441fba000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeaaaeaaae8a0e8a0eaaaeaaae8a0e8a0eaaaeaaae8a0e8a0eaaaeaaae8a0e8a0eaaaeaaae8a0e8a0eaaaeaaae8a0e8a0eaaaeaaae8a0e8a0eaaaeaaae8a0e8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36567
namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c3eca3185d94630bea8c61f5518c2eaa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ee62887d0c510fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x60000018d366880d01c948c2cd1aa4d1b0248bd000000000000004c249800000000000c78000fc5ec1580028e798001680f0000001b6438000000004c63c0ac9ef12a55c238000006b08727a06a1bd0b0004a634c101b045651000000470000a0004000000001c10004b40024206c4e80004d0440000020615c000108000008b80000040000000000000000000001da3746f9063f000000000230000000003ac0004c8d5000000cf8000460000000000068c001a60005b0a123b0008982280021e1500000000000000000000761168000000000019b00076d4980000025c62800000210000154e05907428d4cc0005c8000000003b891000000be8c000000113a0b30a1a1250a5000124000c800a7c4b7800000000000000000014ba673e40005a27e276594f400028c829418830001f400000000000001970000000000000023d2e800000000bf000000000000740000e53915f27c364ba0004d6000001e70000014a8002260004ea5026e5dd4525235c4002f8004ca80c0026f21a980190c44b26d1421993e82f8cf000000000ca000000000001a515000000000344008000002081808f82c00003800000522428000000a00000e8000000000000019a514000003a60001d1f30849e0150730000009900a3bc000e0116000794001b2000000001711fe2b0000001ac5a4000000bc000000f5000820e79b920e0000025809c8fca7016000584d491d00018c000000030060280300600200c0080000a0000180002e0040100400601000002006008000000020000080600000000000006010018010060000100000000000001008000000090020000200300e00c0400300a0000380900a0000200001a00003800002000018000000100000300c00400800000000000100100200080900001c0000000001009005004000010000060080080501a00000004012000000020020000000200601c00800000000018030020040180100003c0200200402c0400100001c018000000100080300400002000004008018030020080000000800400005000014010000060040000200600400001000008000070000080600100204c0380000600c000010000380000000201400001008014008010020000001200000001017000018020250060000080000000800001bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857
  | 3 => 0x17088c7d0000000001f80005c00045a3e1560000012900053c4104c4da7c09a0000002dc002194280012380000000000000010728000004ac000c305a13e58c001fd4ee28ce294b3aa9547c91a0306e070a71000a3d150004bc420f58001760000000039a0005a871000600000004e80000000000000c000000d6000000000780000007c0ac00000000000000718000000013a8000a66f000240000000cd2304680000008e1e69fc5e9a13a8000c88aa3ea000000003020002509a240000000002b6000ef8f40ec000000002dc0003705700000023000218329120000008e8a526e4c848c0000037c9d8d59b73a2308c715235e2843d06120645433a8e1022190f01e06e85540800000000001fb3da32cb00000363f0290e23ba42c00000462930069e109e8688a05c07c844b90254d28d9228d223229d07000000000de80028293c0015e5182b4dd027000524c180004c0912da21086000000003760000014d0008e40e0001d8001351d20000000000000000000000204350002900003700000049600031000000768000000005c0001c4162a502c8000001c08d89e00000000000000000000001fa24c002880021742425c0245a8bf9781783440012a00081400000000968a80cc266000fca2f4262c92200000039000000000001288002da00033006420398f0000000001060751f60010f9103d80000006d1ee0000001a00036800179000000a60000006c544833100000c91a85244bc000001920010918714c7188e20f0f6000a98002244240015c0000640020142e0000000032a21c00000000000002020000bcb30000000002c00039878892000000000d2287000000000e947a0000f93d000000f2000000000000003ec000000af0000000020400072c9e030000924c50001ae0000021b3a05cc3618c1440e0000001b6444000000000007c00002e00018a5f13003d2712500000114896262624038000000005f800286560e18002729cc001d7000708002820260000021d4906a87915a4d00000026c0004c0049670209ec351350006d54b0002ac2a47f20919e0d00009b0005ac4680018c5883ca2502869c0009c4a8a00c80652ea0004500027ea180010537e545458444301040000000062c738de000000000001c02206380000000000000000000000000fe0005817c4c4000000000007dc779c7000000000000000308f0002ec00061928304290680000000a0000000000000000000000000000000000f1993244520288000007fc608003905740002900039400000120000c20000006713e800464000001ea25c4840003b0008a0e722c2583b8000f60002500023326c6593ca852560005000000090d1e27c16c1005d0ea3d2834808690c8000ee19d3dc000000001180007880000045c428002a8000000890e4661208000003ac0003d01
  | 4 => 0x46e0000005b0000442580035a554fe00027095c2a800444000670003100000002d3f449c001fe000000001d900081c00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x153c82776154f209d18553c823e6414f208f59053c823e64947208f59251c825e63952209758e548827661152209d584548823e64d4e208f593538827661d4e209d587538823e6494e208f592538823f64546208f191518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614f204836451881209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c755153083586054c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420d654f3008279650c0209bd9520082e461480209ed9520082d863480209798c54c425d63153108fd9153c423c6454f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10b518d41c42b5640c710ad59221c425e63d52109758f548423e64d4e108f593538423e6494e108f592538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452443345490510d914a41442746550510b518d414436452505109d997314433454cc510d914b31442b5640c510cd1503144357530c510d914831442766588510ad592214436452885109d19521443645248510d914a104423d65950108f990540427661150108f993530423d64d4c109d987530423e6414c108f590530426e6214c109b588530423e64d48108f593520423e64148108f590520425e63148109758c520427661148109d597210433554c84109d59421043355408410cd553100427965840109dd9510043355444010b9189100427b6544010
  | 1 => 0x63f6550441a718d41106776550441b518d411066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc67a60152319e580548c63e6494a318f592528c69c644ca31b6181328c63f64542318f191508c63e649513197d8d544c67761551318f994544c73454cc531c7152314c63d6595031c718d540c73461550318f990540c71d54d0c3197594430c71d54cc831a7191320c71d544c831b5d85320c6d8604c831cd553410c79743d04319d594410c794431043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d5321cd58654c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c87576154f218f99053c863d6414f21cd95241c86d46350721cd95331c86b5640c721cd95031c8755530c7218f993538863d64d4e219e983538867960d4e218f990538863d6414e21cd5532188675619512197d8d544865c63551219ed81544867860551218fd91534863c6454d219dd85534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f59251086756590421b518d4108675650c421ad59031086e5620c421ad592210866f65484219dd95210863f64540218f191500865f63540219718d50086776154f409d18553d03576154f40d518553d031d5390f40c754c43d031d53d0b40ad58742d031d5350b40c754f41d029c6350740c754d41d02b46150e409dd8552902746154a40a758c429029d63d02408f994435025e63149409758c525023e65d0940ad587425023e65d0540a718d415023f6550c40ad185431023d6590840a758c421025f63544409718d51103576354440d518d51103374354440cd50d51103364254440cd109511023d6590440cd54641103355110440a758f401033551d00408fd95401033551500409ed95401031d54ccb30c755132cc2d8604cb309d987548c27561d5230c758e548c27661152309d584548c31e5490e30b5185438c29d640ca30cd952518c3355494630cd951518c3355454630c7952318c29d640c630c7950318c355510c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d641493097997324c2d8604c9308f990514c23d64145309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2d46150c308fd91520c23c64548309dd85520c274615483097596320c29d640c8308fd91510c23c6454430a7590310c2d9600c4308f992500c23d6494030a7593300c25f654c0309ed95300c27661953209d58654c825e63153209758c54c823f6454f208f19
  | 2 => 0xf1e22142680001e548288330ec5c8d017540232c579d402005cba1c117414cc41d110e3d09113934a7bc469382686e44f87e1342c42a173316000ff0553660004a13e2d24dd05000220080000000981747313b000000d3000000758b2800094654000003aa0000000040c31cd100036e340000420ae0d509832420668761d80f6100f890503a06000000000000940002f8000000000000010497d00075c0001b078064420000007704d8c64181a0888c22b0290710691042582419f000000001c431e0007b0a836a51cec80000042c0000022600008931050524002022c48507200007a19c5f0003e0738ac9eb38609c9a800000000820ea28a000f10003d06f0001b6000140000000004bc4980000028c81000000000560000000000000000000400000020000200000024070380401c070040100c050040400000000020000002400000010440200001028050040800400008090000001001018000200200005004080000200000008030400200800004030040101403008090480404c00000000480002804010000080200404000050000500006034000000f000090100200003000000140201401000000100b018060180200800008010000200000004060340300402024000040300003000030080c0000a008000100f00400008000000304c01010010040000c060140000c050000002005000000080100c0501c06012776154a439d1855290e7661942439d5865090f574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310eb46150f4297d8d51d0a5c6354742d5d8d51d0b546354742cdd0d51d0b354354742ad5874290a5f63542429718d5090a3e65d0d42ad1854350a7661141429d5845050a776154c429d1855310b576154c42d51855310a3d6590c42c754e4310b1d5310c42c754f4210ab561d08428fd954210b1d53508429bd954210a7661153329d58454ccad46150f328fd9151cca3c64547328f99250cca3d64943329d98650cca7561943329d987548ca7561d52328f992518ca3d64946328fd91508ca3c64542328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132c758c544cb1c5490d3297195434cad46150d32cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d690c504cb594314132d68c8504ca3d65950328f990540ca5e6315032c7553320ca5f654c832c7551320cad8604c8329bd95320cab46150f41a758c42d065e6394a419758e52906b561d0a4197d8d509065c63542418f997435071c53d0d41c714d43506b46150d41c714e425063e6510941a758c425071c5310941d514f415071c53905418f59643106b561d08418fd95421
  | 3 => 0xb68a70003f00005839e83440800000448070da2dc50877012190860d60001767e45a8003a4000e11cd000000fa8001123e4ca15421c7c8f21ae29c630619210003501b0000de74cbf9973e60ec0600019404ca615c00027000217000000738661ea7dc179ed06000048000000000c10620000004e8b0000784001bf0001e48a15733a1b09995b1bc00000000034000350000000008c00000000000000000078000000000000013d0000002f0001da46cc08001000005b9081a233c000000e479c001230006a8c712e0000a8600ab370000f31762565900000111e4240680018a4300008c380578000000a4000c680000000000000000000000003be480c31de00000cd21a32ce16c591fd000000d580000076c23927000000001320000002e0002f20003800025253cd69030000006b0000002780000020e7fc10800004628d8000000000da000408000001901ee684a50781b60001c0003f4658001f800064418800396000000000f87a8c0000000000001920005a0001930001e800000000000000001b00dc0014b000000af8c10006780009241c000001c521a1384b9171f0054000ad0000000000020c000000560002f4000000001b8000d90d60e4001da05c0000013f1be5dc001190000242c90a000254aa800000000000000000006900005a468001251fa4e880800114000a400019a000001c80002840000041e12c7f0bf028800c21782802948f0a00005f8121612de71c001870002e444029192000e519c130000000a90002890a9bd0003305a02b23e8204193614c54c671603dc000001e92787d00f800000000f0189000000001830003c06a80004a0000000000078d0b1b20003cc39800000000119c90446f8000630e80002f8001666a000000000814001302c60002d0002d410c5e0002e27300000000013c1a0002f66e8bd0004060000012d2a035cd7800000000b60001d243c6220b08c0003681c010000ae9510000000580001481c001fb3f8184001414220000000022a1804c8450e20007900016c00043000154244b5877434000208fb286000740493ca0fc72800000000e3000000490719461c27741f0ef1f4000698eb22c4a88e8000ca558d39851ba0000001611c4b0001980002e1090750007d8000000000000000000022c0007d0000000000020066c000002cc3fcf6000000000001703a000002800288000000dc3760e8160070c86c48e14d0886a4ad12615c010cc82600c8647007
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x73c03095802c00020000463405c05444800146050c829140e4c0826847a4581451c55310c42c2aa6b0e84215147158c544caa838a862826586550604c832928e6b0e8420e1463185540c60e3b2a89906386550604c831a28e6b0ca990c357695031c868a38aa621e818554d61d0b40a2ae6212a22051473544411030ab1aa3a008186550604cb30a28e2b1ca91841d76950318c28a39ac22a2219118c525051086aec2a06288625641483144312b20a510a21895506244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xca08148754d61d08428148754d61d0b40814865cc42544408148758d51d0040
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 860)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xff80fff80fff83fe0fc0ffe0ffc3fe0363ce7c
  | 2 => 0xfffffffff03ffffff000fffffffc1fff83ff8f
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 4 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x290a22312209208052c92909280532a82e10b5
  | 1 => 0x43266450e492259605585b285a43541962c65c
  | 2 => 0x8414888241a4422aa020945294a80952816b0a
  | 3 => 0x1658d12489074b4d39b20610e7328063d40de0
  | 4 => 0x1860e1c70e3873f1ce3ce79c06231183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36567
namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a04000017fd5005fe54017f55005fc54017fd4c05fe53017f54c05fc53007fd0c01fe43007f50c01fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803fe4200ff50803fc4200ffcc803fe3200ff4c803fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842009ffd951004dfeca880037f65440013fb2a2009ff99510015fcca88027fd65440137eb2a2009ff19510015f8ca880277c65440053e32a2000ffd9110005fec888003bf64440015fb222000ff9911003dfcc888003fd64440017eb222000ff1911003df8c888003bc64440015e3222009ffd511004ffca888027fd5444013fe2a22000ffd8d10005fec688003df63440016fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688003dc63440016e31a2009ffd4d1004ffca688027fd5344013fe29a2000ffd0d10007fc8688003fd4344001fe21a2008ffd8910045fec488003ef624400177b122008ff9891000dfcc488023fd62440117eb122008ff1891000df8c488023ec6244003763122008ffd4910046fea488023fe5244011fea922008df54910047f8a488023ff4244011ff2122008ff50910047f88488023ff3244011ff1922008ff4c910047f86488027ff5144013ff28a2009fd9451004ffaa288027f55144013fe28a2000ffd0510007fc8288003f64144001fea0a2000fd50510007f88288003ff3144001fb98a2000ff8c510007fa6288003fc3144001fa18a2008ffc8510047fc4288023f62144011fe90a2008fd48510047f84288027ff5044007ff2822009ff5411001ff8a088003ff4044007ff2022000ff5011001ff88088003ff3044007ff1822000ff4c11001ff86088023ff2044007ff1022008ff4811001ff84088003ff1044001fd8822003ff8411001fec208800fff65040077fb282003ff99410015fcca0800ffd650400b7eb282003ff1941001df8ca0800fff64040077fb202003ff9901003dfcc80800fbe64040015f3202003ff59010005fac80800fbd64040015eb202003ff1901001df8c808017ff540400bff2a02005ff5501002ff8a80800fff63040077fb182003ff98c10005fcc60800ffd63040017eb182003ff18c1001df8c608017ff530400bff2982005ff54c1002ff8a608003ff4304001ff2182000ff50c10007f8860800fff62040077fb102003ff9881000dfcc40800ffd62040097eb102003ff1881001df8c408013ff5204009bfa902004ff94810027faa4080137d5204009fe2902004ffd0810027fc8408013fd4204009fe2102004ffcc810027fc6408013fd3204009fe1902006bf9841002ffea208017fe510400bfea882005ff14410007fe8208003fe4104001fea082000ff10410007fe6208003fe3104001fe9882000ff0c410027fe4208013fe2104009fe9082004ff0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff4004007ff2002003ff5001001ff8800800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0x3fe310c001ef1886000ff4c430077f86218003dc310c01bff908600dff8843006ffa4218037fc210c0077f3006003ffd403001ffca01800ffd500c007fe2806003ffd003001ffc801800ffd400c007fe2006003ffcc03001fbe601800ffe300c007fd1806003ff4c03001fba6018003f9300c007ff9006003ff8803001ffa401800ffc200c019ffb2e200cbfd9710067fccb8800afe65c4019feb2e200cbf59710067f8cb8800afc65c4001ffb262000bfd9310007fcc98801efe64c4001feb262000bf59310007f8c98801efc64c4019ffaa6200cff95310067faa988033fc54c4001ffb1e2000bfd8f10007fcc788002fe63c4001feb1e2000bf58f10007f8c788002fc63c4019ffa9e200cff94f10067faa788033fc53c4001ffa1e2000ff90f10007fa8788003fc43c400dffb162006bfd8b10037fcc588006fe62c400dfeb162006bf58b10037f8c588006fc62c400dffa962006dfd4b10037fca58801bfd52c400dbea962006ff14b10037fe858801bfe42c400dfea162006ff10b10037fe658801bfe32c400dfe9962006ff0cb10067fea388033fe51c4019fb28e200cff54710067eaa388033fc51c4001ffa0e2000ff90710007ec8388003fd41c4001faa0e2000ff10710007fe6388003f731c4001ff18e2000ff4c710007f86388003f431c400dff90e2006ff88710037ec438801bfd21c400dfa90e2006ff08710067fea18800ffe50c4019fea862003ff14310007fe818800ffe40c4001fea062003ff10310007fe618800ffe30c4001fe9862003ff0c310037fe418800ffe20c400dfe9062003ff0831001ffecb0800eff6584007ff32c2002bf9961001ffacb0802efd6584007fe32c2003bf1961001ffec90800eff6484007ff3242007bf9921001ffac908002fd6484007fe3242003bf1921005ffea90802ffe5484017feaa4200bff1521001ffec70800eff6384007ff31c2000bf98e1001ffac708002fd6384007fe31c2003bf18e1005ffea70802ffe5384017fea9c200bff14e10007fe8708003fe4384001fea1c2000ff10e1001ffec50800eff6284007ff3142001bf98a1001ffac50802afd6284007fe3142003bf18a10057fea50802b7f5284015ff294200aff54a10056faa50802bfc5284015ffa14200aff90a10057fa850802bfc4284015ff994200aff8ca10057fa650802bfc32840117eb0c200bffd461005ffca30802ffd5184017fe28c2000ffd0610007fc8308003fd4184001fe20c2000ffcc610007fc6308003fd3184001fe18c200affc8610057fc430802bfd2184015fe10c2003bf9821001ffea10800ffe5084007fea842003ff1421001ffe810800ffe4084007fea042003ff1021001ffe610800ffe3084007fe9842003ff0c21001ffe410800ffe2084007fe9042003ff0821001ffe210800ff71084001fd8
  | 2 => 0x3001df8c51804fff528c027bfa946013ff94a3009ffaa51804f7d528c027fe2946013ffd0a3009ffc851804ffd428c027fe2146013ffcca3009ffc651804ffd328c027fe1946003ffd863001ffcc318002fe618c007fb30c6000bd9863001ffac318002fd618c007fab0c6000bd5863001ff8c318053ff518c029ff28c6014ff546300a7f8a318003ff418c001ff20c6000ff50630007f88318003ff318c001ff18c6000f78c630007fa6318003fc318c001ee18c6013ffc863009ffc431804ffd218c027fe10c6003bf9823001ffea11800ffe508c007fea846003ff1423001ffe811800ffe408c007fea046003ff1023001ffe611800fdf308c001fd9846003ffc823001ffc411800ffd208c007fe1046012ffd9530095feca980037f654c0013fb2a6012ff99530015fcca9804bfd654c0257eb2a6012ff19530015f8ca9804b7c654c0053e32a6000ffd9130005fec898003fe644c00f7f3226000ff59130005fac898003fc644c00f7e3226012ffd5130097fca89804bfd544c025fe2a26012ffd4d30097fca69804bde534c025fea9a6012f754d30097f8a698003ff434c001ff21a6000ff50d30007f88698047ff624c0237fb126011ff9893000dfcc498047fd624c0237eb126011ff1893000df8c498047ff524c023bfa926011ff9493008ffaa4980477d524c023fe2926011ffd093008ffc8498047fd424c023fe2126011ffcc93008fbe6498047fe324c023fe9926011f74c93008ff86498003ff614c0017fb0a6000ff98530007fac298003fc614c0017e30a6012ffd4530097fca29804bfd514c025fe28a6000ffd0530007fc8298003fd414c001fe20a6000ffcc530007fc6298003fd314c001fe18a6011ffc853008ffc4298047fd214c023fe10a6012ffd413001ffca09804bfd504c007fe2826000ffd013001ffc8098003fd404c007fe2026000ffcc130007f6609800ffe304c007ef1826011ffc813001ffc4098047fd204c007fe1026003ffd943001dfeca1800ffe650c0057f3286003ff5943007dfaca1800ffc650c0077e3286003ffd903001dfec81800ffe640c00f7f3206003ff59030005fac81800ffc640c0077e320600fffd503007ffca81803ffd540c01ffe2a06010bf98c3007ffea61803bfe530c01ffea98600eff14c30007fe861803bfe430c001fea18600eff10c3001ffec41800eff620c007ff3106001bf9883001ffac418036fd620c007fe3106003bf1883006ffea4180377f520c01bff290600dff5483006efaa418037fc520c01bffa10600dff9083006ffa8418037fc420c01dff990600dff8c83006ffa641803bfc320c007ffb086003ff98430005fcc21800ffd610c0017eb086003ff1843007ffea21803ffe510c01ffea88600fff14430007fe8218003fe410c001fea086000ff10430077fe621800
  | 3 => 0xe1028003ffd944001dfeca2000ffe65100057f3288003ff594400bdfaca2000ffc65100077e3288007bf9904003ffea82001ffe541000ffeaa08007ff1504001ffec62000ffe63100017f3188003ff58c40005fac62000ffc631002fffa988017ff94c400bffaa62005ffc531000fffa188007ff90c4003ffa862001ffc4310007ffb108003bfd884001ffcc420006fe6210007feb108016bf5884001ff8c42000efc621002dffa908016dfd48400b7fca42005bfd521002dbea908016ff1484003ffe842001ffe421000ffea108007ff108400b7fe642005bfe321002dfe9908016ff0c84001ffec22000ffe61100017f3088003fd98440005ecc22000ffd61100017eb088003fd58440005eac22000ffc611002fffa888017ff944400bffaa22005ffc511000fffa088007ff904400077c822001ffd411000ffe2088007ef10440007fe6220003fe3110001fe9888000ff0c4400b7fe422005bfe211002dfe9088016ff0844001dfcc02000fff5010007ff2808003ff5404001ff8a02000fff4010007dfa008003ff9004001ff4802000ffd4010007dea008007fe5004001ffe402000ffe2010007fe9008003ff08040077fecb98056ff65cc02bff32e6002bf997300affacb98056fd65cc01dfe32e6002bf19730077fec998002ff64cc001ff3266007bf99330007fac998002fd64cc01dfe3266007bf193300affea998057fe54cc02bfeaa66015ff153300affea79803bfe53cc02bef29e6015ff54f300afbaa79803bfc53cc001ffa1e600eff90f30007fa879803bfc43cc01dffb166010bfd8b30087fcc598006fe62cc021feb166010bf58b30077f8c598006fc62cc021ffa966010dfd4b30087fca598043fd52cc021bea966010ff14b30087fe8598043fe42cc021fea166010ff10b30077fe6598043df32cc021ff1966010ff4cb30087ba659803bfc32cc01dffb0e6000ff98730005fcc398003fd61cc0017eb0e600eff187300affea398057fe51cc02bfea8e6015ff14730007fe8398003fe41cc001fea0e6000ff10730077fe6398003fe31cc001fe98e600eff0c730087fe4398043fe21cc021fe90e6010ff087300affea19800ffe50cc02bfea866003ff14330007fe819800ffe40cc001fea066003ff10330087fe419800ffe20cc021fe9066003ff0833001ffecb1800eff658c007ff32c6002bf9963001ffacb18052fd658c007fe32c6003bf1963001ffec91800eff648c007ff3246007bf9923001f7cc918002be648c007feb246000bf5923001f7ac918002bd648c007fe3246003bf192300a7fea918053fe548c029feaa46014ff1523008dfac718053ff538c029ff29c6014ff54e300a7f8a718003ff438c001ff21c6000ff50e30007f8871800fff628c0077fb146003ff98a3000dfcc51800ffd628c0277eb146003ff18a
  | 4 => 0x73fc52d000fffa168007efd0b4003ffc85a001ffd42d0039dea168007ff10b400e7fe65a0073fe32d0039fe996801cff0cb4003ffec3a001ffe61d00017f30e8007ff58740005fac3a001ffc61d003bffa8e801dff947400effaa3a0077fc51d000fffa0e8007efd074003ffc83a001ffd41d0001dea0e8007ff10740007fe63a0003fe31d0001fe98e8000ff0c7400e7fe43a0073fe21d0039fe90e801cff087400effea1a000ffe50d003bfea868003ff143400e7fe41a000ffe20d0039fe9068003ff0834001ffecb2000eff6590007ff32c8002bf9964001ffacb2006efd6590007fe32c8003bf196400c5fac92006fff549000fff2a4801bff5524003ff8a92000fff6390007ff31c8000bf98e4001ffac720002fd6390007fe31c801bffd4e400dffca72006ffd5390037fe29c8007ffd0e40007fc8720003fd439000ffe21c8003ffd8a4001dfec52000ffe62900037f3148003ff58a400d5fac52000ffc62900077e314801affd4a400d6fea52006bfe5290035fea94801adf54a400d7f8a52001fff4290035ff214801aff50a4003ff8852006bff3290035ff194801aff4ca400d7f8652000fff6190007ff30c8000bf9864001ffac320002fd6190007fe30c801bffd46400dffca32006ffd5190037fe28c8007ffd0640007fc8320003be4190001fea0c8007ff10640007788320003ff3190001ff18c8000ff4c640007f8632006bff2190035ff10c801aff486400d7f8432000efe6090007ffa848003ff9424001ffaa12000ffc5090007ffa048003efd024003ff6812000fff2090007ff1048003ff4824001ff84120067ff65500337fb2a8000dfd9540004fecaa0067fe65500057f32a8019ff595400cdfacaa0067fc65500057e32a8019df19540014f8caa0067ff545000fff2a28019ef951400cffaa8a0067bd545000ffe2a28000ffd8d40005fec6a0003fe6350001feb1a8000ff18d40005f8c6a0067ff5350033ff29a8019ff54d400cff8a6a001fff4350001ff21a8000ef90d40007fa86a001ffc4350001de21a8018ffd89400c5fec4a0063fe62500037f3128018ff589400c5fac4a0063fc62500037e3128018ffd49400c6fea4a0063fe5250031fea928018df549400c7f8a4a001fff4250031dfa128018ff909400c7fa84a0063bd425000ffe2128018ffcc9400c7fc64a0063fd3250031fe1928000ffd8540005fec2a0003fe6150001feb0a8000ff18540005f8c2a0067ff5150033ff28a8019ff545400cff8a2a001fff4150001dfa0a8000ff90540007fa82a0003bd415000ffe20a8000ffcc540007fc62a0003fd3150001fe18a8018ffc85400c7fc42a0063fd2150031fe10a8019ffd414001ffca0a0067fd5050007fe2828007ffd014003ff680a000ffe4050007df2028018ffc814001ffc40a0063fd2050007f
  | 5 => 0x953111dfeca9888ffe654c4057f32a6223ff5953111dfaca9888ffc654c4057e32a6200ffd9131005fec898803bf644c4015fb226200ff9913103dfcc898803fd644c4017eb226200ff1913103df8c898803bc644c4015e3226223ffd513111ffca89888ffd544c447fe2a26223ffd4d3111ffca69888ffd534c447fe29a6200ffd0d31007fc8698803fd434c401fe21a6222ffd8931115fec49888bfe624c4037f3126222ff58931115fac49888bfc624c4037e3126222ffd4931116fea49888bfe524c445fea926222df54931117f8a49888bff424c445ff2126222ff50931117f8849888bff324c445ff1926222ff4c931117f8649888fff514c447ff28a6223ff5453111ff8a298803ff414c401ff20a6200ff50531007f88298803ff314c401fb98a6200ff8c531007bc629888bff214c445ff10a6222ff48531117f84298803ff604c4017fb026200ff98131007fac098803fc604c4077e3026223ffd413111ffca09888ffd504c447fe2826222ffc8131117fc409888bfd204c445fe102620effd94310fdfeca1887ffe650c4057f328621fff594310fdfaca1883bfc650c4057e328620effd9031005fec818803fe640c40f7f3206200ff59031005fac81883bfc640c40f7e320621fffd50310fffca81887ffd540c43ffe2a06221bf98c310fffea61883bfe530c43fef298621fff54c310ffbaa61883bfc530c401ffa186200f7d0c31077fc8618803fd430c41dfe2186200f710c31077fec41887aff620c43dff3106201bf988310f7fac41887afd620c41dfe3106201bf188310f7fea41887b7f520c43dff290621eff548310f6faa41887bfc520c43dffa10621eff908310f7fa841887bfc420c41dff990621ef7cc8310f7fc641887bfd320c43dee990620eff0c831105fcc21887fff510c43fff288621fff544310fff8a218803ff410c401fba086200ff90431007fa8218803fc410c401fa208620effcc431007be6218803fe310c401fb1886200ff4c431007ba6218803f5310c43dff908621efdc84310f7fc421887bfd210c43dfe108621efd08431077fec018803fe600c4077f3006200ff58031005fac01883bfc600c43fffa80621fff940310fffaa01887ffc500c43dff900621eff880310f7fa401887bfc200c40fffb2e8007bfd974003ffccba000afe65d000ffeb2e801dbf5974003ff8cba001efc65d000fffaa68007ff9534003f7ca9a001ffd54d003bdeaa68007ff1534003ffec7a001ffe63d00017f31e8007ff58f40005fac7a001ffc63d003bffa9e801dff94f400effaa7a0077fc53d000fffa1e8007ff90f400077c87a001ffd43d000ffe21e8007ef10f4003ffec5a001eff62d000fff3168001bf98b4003ffac5a0072fd62d000ffe3168001bf18b400e7fea5a00737f52d0039ff296801cff54b400e6faa5a0
  | 6 => 0xfffb108207bfd884103ffcc420806fe621040ffeb108226bf5884103ff8c420806fc621044dffa908226dfd4841137fca42089bfd521044dbea908226ff1484103ffe842081fbf421040fff2108207ff508411377a842081ffc421044dff9908226ff8c841137fa642089bfc32104517f3088227ffd444113ffca22089ffd511044ffe2888207ffd044103f7e822081ffe411040ffb2088207ff504410077a822081ff5411044dff9088226ff88441137fa422089bfc211040fffb008207ff9804101dfcc02081ffd60104017eb008207ff1804113ffea02089ffe501044ffea808227ff14041137fe402089bfe201044dfe9008226ff08041077fecb98896ff65cc44bff32e6202bf9973112ffacb98896fd65cc41dfe32e6202bf19731077fec998802ff64cc401ff3266207bf99331007fac998802fd64cc41dfe3266207bf1933112ffea998897fe54cc44bfeaa66225ff1533112ffea79883bfe53cc44bfea9e620eff14f31007fe879883bfe43cc401fea1e620eff10f31077fec598886ff62cc443ff3166201bf98b3110ffac598886fd62cc41dfe3166201bf18b3110ffea5988877f52cc443ff2966221ff54b3110efaa598887fc52cc443ffa166221ff90b3110ffa8598887fc42cc41dff9966221ff8cb3110ffa659883bfc32cc44bffa8e6225ff9473112ffaa398897fc51cc401ffa0e6200fdd0731007fc8398803fd41cc401fe20e6200fd1073110ffe4398887f721cc443ff10e6221ff4873110ff84398887f421cc41dffb066200ff9833101dfcc198803fd60cc4017eb06620eff1833112ffea198897fe50cc44bfea866225ff1433110ffe4198887fe20cc443fe9066221ff08331127fecb18892ff658c449ff32c6202bf99631127facb18892fd658c449fe32c6202bf19631007fec918802ff648c401ff3246207bf99231007fac918802fd648c401fe3246207bf19231127fea918893fe548c449feaa46224ff15231115fac718893ff538c449ff29c6224f794e31127faa718893dd538c449fe29c6200ffd0e31007be8718803fe438c401fea1c6200ff10e31007b88718883ff628c4417fb146220ff98a3100dfcc518883fd628c4417eb146220ff18a3100df8c518883ff528c441bfa946220ff94a31107faa5188837d528c441fe2946220ffd0a31107fc8518883fd428c441fe2146220ffcca31107be6518883fe328c441fe9946220f74ca31107f8651887afe618c449ffa8c6224ff94631127faa318893fc518c401ffa0c6200ff90631007fa8318803fc418c401ff98c6200f7cc631007ee6318883ff218c441ff10c6220ff48631107f84318803ff608c401ff3046203bf98231007fac118802fd608c401fe3046224ffd4231127fca118893fd508c449fe2846220ffc8231107fc4118883fd208c441fe1046223ffd
  | 7 => 0xa08b3fc52d040fffa168207ff90b4103ffa85a081ffc42d0459ff996822cff8cb41167fa65a08b3fc32d045bffa8e822dff9474116ffaa3a08b7fc51d0459ff90e822cff88741167fa43a08b3fc21d040fffb068207ff9834101dfcc1a081ffd60d04017eb068207ff1834116ffea1a08b7fe50d045bfea86822dff14341167fe41a08b3fe20d0459fe906822cff0834115ffecb208aeff6590457ff32c8202bf9964115ffacb208aefd6590457fe32c8202bf1964114dfac9208afff549040fff2a4822bef9524115ffaa9208afbd549040ffe2a48200ffd8e41007fcc720802fe6390401feb1c8200bf58e41007f8c7208afff5390457ff29c822bff54e4115ff8a72081fff4390401ff21c8200ef90e41007fa872081ffc4390401de21c8228ffd8a41145fec5208a3fe62904037f3148228ff58a41145fac5208a3fc62904037e3148228ffd4a41146fea5208a3fe5290451fea948228df54a41147f8a52081fff4290451dfa148228ff90a41147fa85208a3bd429040ffe2148228ffcca41147fc65208a3fd3290451fe1948207bf9864115ffea3208affe5190457fea8c822bff1464103ffe8320803bf419040ffba0c8228ffc8641147fc43208a3fd2190451fe10c8200ffd8241007fcc12080efe6090401feb048200bf58241007f8c1208afff5090457ff284822bff5424115ff8a1208a3ff2090451ff1048228ff48241147f841208abff65504557fb2a822aff99541015fccaa08abfd65504557eb2a822aff19541015f8caa08abff545040fff2a2822aff5514103ff8a8a0803ff63504017fb1a8200f7d8d41005bec6a0803fe6350401feb1a8200ff18d41005f8c6a0803dc63504016e31a822affd4d41157fca6a08abfd5350455fe29a8207ffd0d41007fc86a0803fd435040ffe21a8229ffd894114dfec4a08a7fe62504037f3128229ff5894114dfac4a08a7fc62504037e3128229ffd494114efea4a08a7fe5250453fea928229df5494114ff8a4a081fff4250453ff2128229ff5094103ff884a08a7ff3250453ff1928229ff4c94114ff864a08abff5150455ff28a822aff54541157f8a2a081fff415040ffba0a8200ff905410077c82a08a7ff2150453ff10a8229ff4854114ff842a0803ff60504017fb028200ff98141007fac0a0803fc60504077e302822affd4141157fca0a08abfd5050455fe2828229ffc814114ffc40a08a7fd2050453fe1028207ffd944103dfeca2081ffe65104057f3288207ff5944113dfaca2081ffc651040f7e3288207bf9904103ffea82081ffe541040fdf2a08207ff5504113f7aa82081ffc541040fffb188207ff98c41005fcc62081ffd63104017eb188207ff18c4113ffea62089ffe531044ffea988227ff14c4103ffe862081ffe4310401df2188207ff50c4103ff8862081fbc431040
  | 8 => 0xfd8643007fcc321802fe6190c01feb0c8600bf58643077f8c3218cfff5190c67ff28c8633ff5464319ff8a3218c3ff2190c61ff10c8630ff48643187f8432183bff6090c01ff3048603bf98243007fac121802fd6090c1dfe3048633ffd424319ffca1218cffd5090c67fe2848630ffc8243187fc41218c3fd2090c61fe1048632ffd9543195fecaa18cbfe6550c057f32a8632ff59543195facaa18cbfc6550c057e32a8632ffd514303ffca8a18cbfd5450c0ffe2a28632ffd4d43197fca6a18cbfd5350c65fe29a8607ffd0d4303fbe86a1803fe4350c01df21a8631ffd894318dfec4a18c7fe6250c037f3128631ff5894318dfac4a18c7fc6250c037e3128631ffd494318efea4a18c7fe5250c63fea928631df5494318ff8a4a181fff4250c63dfa128631ff9094318ffa84a18c7bd4250c0ffe2128631ffcc94318fbe64a18c7fe3250c63fe9928631f74c94318ff864a1803ff6150c017fb0a8600fdd8543005eec2a1803fe6150c01feb0a8600ff18543005f8c2a1803f46150c017a30a8632ffd4543197fca2a18cbfd5150c65fe28a8631ffc854318ffc42a18c7fd2150c63fe10a8600ffd8143005fec0a1803fe6050c01feb028600ff1814301df8c0a18cbff5050c65ff2828632ff54143197f8a0a18c7ff2050c63ff1028631ff4814318ff840a183bff6510c0f7fb288607ff99443015fcca2181ffd6510c5f7eb28860eff1944303df8ca2181efe6410c0fffaa08607ff9504303ffaa82181ffc5410c617f318862fffd4c43077fca6218bffd5310c1dfe2988607ffd0c4303f7e862183bfe4310c0fef2188607ff50c430077a862181fdd4310c1dffb108607bfd884303ffcc421806fe6210c0ffeb10862ebf58843077f8c421806fc6210c5dffa90862edfd4843177fca4218bbfd5210c5dbea90862eff1484303ffe842181ffe4210c5ddf2108607ff5084303ff8842181fbc4210c1dff990862eff8c843177fa642183bfc3210c1dffb088607ff98443005fcc22181ffd6110c017eb08860eff1844317ffea2218bffe5110c5ffea88862fff14443177fe42218bbfe2110c5dfe908862eff08443077fec02181ffe6010c077f3008607ff58043005fac02183bfc6010c5fffa80862fff9404317ffaa0218bffc5010c5dff900862eff88043177fa40218bbfc2010c0fffb2e8207bfd974103ffccba080afe65d040ffeb2e822dbf5974103ff8cba081efc65d040fffaa68207ff9534103ffaa9a081ffc54d040fffb1e8207ff98f41005fcc7a081ffd63d04017eb1e8207ff18f4116ffea7a08b7fe53d045bfea9e822dff14f4103ffe87a081ffe43d040ffea1e8207ff10f4103ffec5a081eff62d040fff3168201bf98b4103ffac5a08b2fd62d040ffe3168201bf18b41167fea5a08b37f52d0459ff296822cff54b41166faa5
  | 9 => 0x200101600e00a00600200100700c00c01b00d00900100000001000100a00000700200000400c00000000c00000001400400400000000400700100000200500300001000c00b00100000100800000100201800900100300100500000500100c00300000f00100300100100000000000400200300800000100000000600400102300000200000200600100100400500100000000400b00000600c00400c00e00000000900000100000100100100100500000000000100100200100000000b00100301a00700900400000000000400600001400100b00000300000a00000200000000600000200200600100000000000000300000200100001c00000700500f00200300000a03500000200102b00300a00000300000c00102500300400000100700701100000000200800300400200900000600600000200000100b00200600000400100000800000501300100000600000200c00004302900600000100000000000100100000700100600100000000000300000000400400500200400000c00401300100000600100000200100100000000b01300701000201400b00000100000700200d01600000500c00000000200000500401600300000101000600000000801900601000000200200100100500200100000b00300600000300100300100b00000200000700500200003ffecba181eff65d0c0fff32e8602bf9974303ffacba18d6fd65d0c0ffe32e8607bf1974303ffea9a181ffe54d0c0ffeaa68607ff153431affea7a18d7fe53d0c6bfea9e8635ff14f4303ffec5a181eff62d0c0fff3168601bf98b4303ffac5a18d2fd62d0c0ffe3168601bf18b431a7fea5a18d37f52d0c69ff2968634ff54b431a6faa5a18d3fc52d0c0fffa168607efd0b4303ffc85a181ffd42d0c69dea168607ff10b431a7fe65a18d3fe32d0c69fe9968634ff0cb4303ffec3a181ffe61d0c017f30e8607ff58743005fac3a181ffc61d0c6bffa8e8635ff947431affaa3a18d7fc51d0c69ff90e8634ff887431a7fa43a18d3fc21d0c0fffb068607ff9834301dfcc1a181ffd60d0c017eb068607ff183431affea1a18d7fe50d0c6bfea868635ff143431a7fe41a18d3fe20d0c69fe9068634ff08343077fecb218ceff6590c67ff32c8602bf9964319ffacb218cefd6590c1dfe32c8602bf1964318dfac9218cfff5490c0fff2a48633ff5524303ff8a92181efe6390c67ffa9c860eff94e4319ffaa72183bfc5390c0fffa1c8600efd0e4303fbe872183bff6290c617fb148630ff98a4300dfcc5218c3fd6290c617eb14860eff18a4300df8c5218c3ff5290c61bfa948630ff94a43187faa5218c37d5290c61fe2948607ffd0a43187fc85218c3be4290c61fea148607ff10a4318778852183bff3290c61ef9948630ff8ca43187fa65218c3dd3290c1dfe194860ef
  | 10 => 0xef22fd00000000002f72381db442600e3c606440001ce39218a8ac87c2000020cb0837e3ff152402a1ee10f80001300d72f101ac8ba73928e1c800000000000d3800000000009a47603bb1b380000002540001e3800032125b0430fbe0000000000cb60000000ecc6126bb039000027031200000000f24fa38e00000003071f380008fe4c539d960c6368350019ac094a667000000000082c0000238fe406600013380860000000ec822800015019441c60cf34e8bc8aaa5723d28000b48000000000000057d00000006187a311f1e3c7884390060a7c0006fb2390e4c91e24b1c7808c00067c00000009a80b116da010ce80372e20d08bec00036a80006a219417c09ec7026300000610d3473c0001d500004861368a140000001d2102c00075c26300000003f7124043c0000700b7117094c51d24980001180000000d285246b7345800097e0000979c2400000000000000000001d310a8000000000000105e1081910728e1c5e935a811800000014a000000000035484fcca80000000f8895a0000001a5825800031b8fa00ba0eb31c908d03000000000b48d8000000000084c6b10348994ee60000001e984381f21b68000168056326973400049437086d4eea0002b3171400000200000000400001d00b00200100d00000100200000000000001d00600000c00400100000000800100000000000700000000100000000100601500400700000000200500001100000000100300500000200000500200500300000400100100200700001b00e00900900500100300100100000000400500300200000000100800300a00100400001300400300000000500000100000000300000500000000000500701900100200901900000000000c00300000800300000600000001900300000000000200500800000000000000401300801200401000000000000001401201602600000000000000000601001300901a01d00000000400400200000a00101100202d00000400000400200100000100000400200200000300800100c00000000b00000200000200800400000600000000100d01000600100a00100100400200000300200d00200000b00f01800000101a00400800100100800103800300500201b00000100000100100000000301200001500000100200400005a00000000000200500000100200500000500500300000700200300400300900400b00100000000400100000500100000500000a00400500100100000000400300100100200f01001d00d00200100000c00100000000000000000300302200200300001000700400100400300c00000900400300900600700400000000300000600800f00100200100700700300300100801100500000000500000200000000600c00200100000101100200200000500000100000000100c
  | 11 => 0x181c9641a52658000cec0000a580003060001100d04cd874500016cc2c000000009e40000000001460e8200000000000000000000000000000061151c0007102d6032505400000000006c812e0ad80249fe0641f91a8c9cc6ca36091b4c227fa0531e34f3016725a16d0b6a23f1818d742e800000795008f200037e000088c4b73f08000000437000000000073500014d400036c2ca97f80002e808d9ce800000000000108a421800002ec8407620aa800053c00000017648c066e03680000be196000000000000011b000089461803992e07a8000000000000000000000008ce00000000002ee36b38a99805ea000010928400000000000000d05fb00000000000003d380000000003e480008300000cf8f842565e8264800030e4ea0000000000000000000100e0190001e400002bc00010b44880000000000d7c0133490720ff86ff00000000000890000ce4c2c0da39e80004523a52fb904ca166123df05f4ce47f037300187f01b40001e200001002641a208f034020d1af40fa0002228000000293000103d0524621e013ecdb264637a1024b5c1e639b00000ee000156a090f9a5ff2958710c3a1cb00015c06f00000000f203c43fe39481a800000000011842740002a80ccc31a4240ee16a0e5600029900004c05c115f0000000473171000016c2393551b10f684ee00010f834e0002031f003a24f32651c085066832c000008840003d41584bde0001f217600005fc21800008a60000000000b1a0000000ea06e20000000ff07a65413f200003b400000000000002cf0b18e540003af00018fcc4c7ce16a0a580000000001afc0004550dc2070bbc79e173122858c5712490e8039e0002dc920033c5b829293bcaa26192720f700007f93f7a0d80105bd27c0000e000b81960a3c18c56a1be1f8c0004bb2d1000000055818f94340001a81118b2cf160000000000e8e6e22de06704ce1af07a800000067d304868c0002dc0001058fd44fe0001ded0322d90000068af273800001b06686144040000f04000000135400072a22b1b188e828420896180000001081cb0be059700000009366dd27803ec31c2153980000b5e74e41da0b8a4200017381146b22072739d1809081500004400545313b215587d819306d8790cb022700001fc00048e3f2800076200002097180000000001c6cb622bd09a190090400000000005a41a409b1c5c0008053799c0c2a603040e86fc22453705980003ec20c20f9a2893a38804a149c3b2000000136443c21a369a03800053b00020684ec53e00002bcdbe0c81d18000c2e7dc0668000cfe0003f7101cb9615c0d8880c0984142e50ee05225e33a41a344425140ab097013401d1141df0bf46e523896c88800071cd80b80000003fc1fdc7f630b1ba0000ee20001520000cca0002b68000eb62bf0f38a2c264
  | 12 => 0xe000000026c6bc7db35403448100000000000bc867e0aa06a8ad03800001528ffa2cd0ff9810c4420536719e87ec4030b49dac2784b329f84700282c819a9074d0a7f604a86989b60001c802c8dee55a364850cb0e1c5000012400000000007784e80e51358a00b4a000000000102255f07e00004f80000f5875829400000012d506e00033080009580000000000d4812703c19084c218938e8100f3839c000057c00033f00000000007ca0001eb842c00011a1570868000000000000028c40305ccf586cb000000007e74c14d8d840003cc06e8ea4d383d70000824f8e70d0000000000387000083892e3483e1944101423836d89280480ae0bf12e44ea00008f8d8887600030f9ef40003152f99e906cc6d0000049400000000c00e400071f00005040003ef08302b4ed80a1019207c2ba00015d80009bc7e80001574aec0003aa89fc000000000187811a66400000000000003e5800000019200000001521c220d9030986821000000006800000001ec0000003258c04ee800000000000000670000b8c5820000001f501380002a70ed8b0a330276837002070b00000009301e900000000000000001c9c00000000000000004ae151000000000d00002780001810001c780000000440000a465170000000000000000167c9f80004190fc40002ce00000006ae0050b4208800051301a8f280e8051253909c9886570000f180f800023b97d419c5eb0001a7c0e27d14079eb4000302356988000000000015300005021720a6000000025e000055600022f8908838000000000044800034b8d103fc2fc00000006b009f24180001866cd3d99ad0320259362800000000000015d000060b08100000b200022a07a8bb4000175800072400000014bc00000000000000000000000a0400032b0000000db029d00014009ba27e06c00000006800000f5441e7cf00002f46624be36e15f800000033c0c800006473e2800085600000003d05a200019f089400063607c8ea8a5c000406090c9c67e60130b000002e937f12f400029c0d01d109ac0ea0001abcf746e32dd08f40007b931f06a407000023b127c91a5bb0fc94a506024e03083406e66fa165013c4a21f70001d00de032618817b066e0e413886642c83e922b88b0b606ae2ba824400000000000008bc6e9306029c95e00036003bccb400005f80002b00fe00011b8d207973bd179ca2a6a7315977049e41532b0ce81825962278f8100234734486f496205b35c18d0c5025815607c03e81513220848ce63da3638efc9ec05e3500f1c20a4da2c58e14fd21c91150bf83fa1b3299800028c6e703f13a0d9832e2bd800026200000000000000001878000fa06a200009c835a0004130c580002043420001062000141082c0006c816b81400000f700019282806d23db8000c380000000548fea0001c6
  | 13 => 0x807505208102bf95f0d642af1eb00885985aa04104904c40003ec87b40005060001fb431600000000000004cc00000009ca2ed3ce80000007321b298bca500000000974d4c055199032c0003860d0834cf6c000000021471a44811e09cc9b87f41ba822ce9a39f00018145de6f902d0bd0000629000000000040400003e80006c2194800000028e000000047600000000009440002839f8058a37f0001da0df05e119184847a051b2fe8fcc43200000004f80000f20001c04288000131875c0003fd2ad9b788660000001a4cf5443813503b00000003f9880400020d00013a40000000000c700000df36d0f640002f00e808b860c66a00010840007a00001bacf8263c15880000000002688000a6835605f15940000000310000c6200000000000000003c28d5476e1ac1181d400005c932080000000000001720dda0000ad10bc6e07333f5881877c0000001c105465a63af10fc0ae0000001d5c1aa71a20c80000006770cc208071c000000000000003339f00004048020a7000000031331a957900027a02e13e400014800000000000000001bb800000000000000000a8000000000044b144166c4440000f88000462000000091c00059d3fd83005e67082ab911090e00a000146461a3e6000000013a17934a209c8440003ac80005b400000018006320002050c9c0004363070ee800000000000000006591ff8cf460851e00000001c25b70000000c2a00017c800000039d0dd8a98fd85b60371094bf049c32a80000000000000fe44d85440e9000104658f14680d80006f200000ec82432a000168c0000004158000304000000000000000000008740000000000d14c5c1dd3bf80000001cc0000000bba0f33ef1cb50360000178d8107000000007947b60000000000f5e75805016a400003d12d95b84983f430d1468e5c21b2329aac02435c06504780000000299b80e7e0000818c14cea0000980000c7a66b0ed910c0c01ae3b80000000379000184069611a04c800079613d2a289148d40000001d680004a30001c1800040e03b000017266336b1c8c0000000848000ab2783285192000060f00010348ea0bc0001480c42000000137c00041732f8fb457431835e0cb400017602685403c25f10001c3c30c55200000000005e52b79ef069264e3e40cf00000000001d989ae2de3369798a780001ef9dc81ec7b50f00e64ac458136a094c5841803008594a6c567185041cf620e02208b105ec75638c8d8c8001c005196fc51272500012c064a1b200f9e102f868627a03c03f62462eb0000bae16b30180c41ce82505597a880481e0e99c1c9180000000240e960ee326000070862d0001ae40007ab00013b099e0001c48000e6227012b1204f3619b3508de82460860eaa058d4a2e02b480ac4ee2d54168c200884e11330f24b8e10100018cc52
  | 14 => 0x188989c00000005a98c800017800015ac85225a282931ce28828000000000011900002000000000000d680161e3000000000016604392a83f800000000f00000000bf81d4ffe623000186c02c70a4058d5066c44d0128460c0c38a219000083c7da32f0ca075a6b60000f0c0005390000dbc9c03ce17701bc00083900000001fa1490000d3400000035d11a00002a934c80b08fa03e0408c500000003b71f4ccba1ec078a05cf2847a03d00005864493f1015000013504797d016e10b062800000025f0888d3ce427631f8190c8c87922b6114456663b2878ddc4a408a00f1bc463c3d218b91bca100000bd877cb121370001c5838c10d3348000a7a000000000012c0000ce8000226650000070c00000000000004c817a3290bc40000e900014040002872669348000000000000009c4351f5094045e599000071cf8c6d70af0000dd80e61a8000010814c00002e800036a000000000043c15c863c73000000015dcf2a3ab00010a089c4d300003787160001750000254000000043800016d252080000000000000000000002e10a68d9e00013c011c2665a73f886d800083a1638108000000000000070416f00000005c20002171e64b7c00000005648f85603a8994ce8437d33889b856c0c72a68000ccc6953ea8000eee49a24882904d063824416b428a78915a8000000000000093455c14d11902c02841390010000dde3e305612a00007cc3c000000007600000000a188330cd0148af000000000000007e71158454bdc04a3c306dcb3468c37411983182ff2b993c86707490b81c4cb38711000012cede4052d580007d60002459ca0cb848528194b0b103ae12b9e584100d23d910f41fe00000000010240c425000006d0668406800000000019d800000000001380000000001698000c4a00039100000001be29680002504fd0f41e7cb1c51600000000002ec1da1e0479e0000001a08c8a00025480000000000000000d220003b51e68a7474f000000000000004900002441880000000cf272f0000e84ef02e53c519bc0000002711d28686496180000056000023485c80000000000000e860001bb1a60c1000035600004804c00001f1000012d00000e80005c03df85886dc44c39b80004bc526000000000006500000000002c93eb1648ebe44741a1eec6d22a7187144873c2142c8800032a5482d086287065430c2958cdea78700014380000000fa98900007b811694445f612937518e80000001d618340008031378000e2400009313600007d811a80003f47341cd0760c583b93b38ed414431a08b8898c044f712093ac3f0000372053ceca4c1000000047401c1529bf48020aa3380a2800058236894105f45224099ea45b02b700000007b02a100000001c47180000000b86000105176c0000001d11d7400000034383a06a600026
  | 15 => 0x69e24800003780002e60f1400000024c800474e0003b485c4bbe43a0d58f34a485f2255825c86247e0001e844aa000000000055472614a8f7400000005280000002d000000001a83ee00000001981160000000a1267b2a798289ea5ed2788ac82d44890ba9a38b2875222c9f7485848434d86e436058a3be964c7780002f017e4a3e0001fa800028e32f0e08fe80000000000b747a20002bd018c0003de00000000000000001bd85ac4ba1430dec698000000150800019707c00000000000000d480006812a3000000000000b91ac0005d50e694c000010a1af8f9400000000000000003912e98d1857000000004ec9845533bb00000003970f9974878405814c800077a1ef2cf1b0c93c39440a193cf4400001484104222333eb800037470c13e84741b245b24a8dc8b202b4090173c72c7d21249c145be3241e09d4ca705983598000b9c2370000584a967930000aa0ba80ed2c6118c0000d60001744b406493c880808b0093404806ca542173310000ba0000000184c0001573479140efc1a23b08c7400047b00000a0f604100b600000220002aa11680000000000d6c0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf2159010006be2159010006bd2159010006bc215901001ebf705901001ebe705901001ebd705901001ebc705901001ebf505901001ebe505901001ebd505901001ebc505901001ebf305901001ebe305901001ebd305901001ebc305901001ebf205901001ebe205901001ebd205901001ebc205901001ebf105901001eb7105901001ebe105901001ebd105901001eb5105901001ebc1059010074ff7598c10014fe7598c10004fd7598c10074fc7598c1003cfe7498c10004fd7498c1001ede7398c10076de5398c10006dd5398c10074ff7298c1000cfe7298c10004fd7298c1000cfc7298c100067f5298c100067d5298c10076df3298c10006dd3298c1001cfe7098c1001cfc7098c1001ede3098c1001edc3098c1001ef71098c1001ef51098c10004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c1003cfc7458c1001edf7358c10006de5358c10006dd5358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10006df3258c10006dd3258c10074ff7158c10114fd7158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c1003cff76d0c1001cfe76d0c10004fd76d0c1001cfc76d0c1003ebe64d0c10006bd64d0c10074ff7690c1001cfe7690c10004fd7690c1001cfc7690c1003ebe6490c10006bd6490c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c1003ebe6450c10006bd6450c10005f77150c10005f47150c10074ff7610c1001cfe7610c10004fd7610c1001cfc7610c1003ebe6410c10006bd6410c10004fd76d041003ebe64d0410006bd64d0410004ff769041003cfd769041003ebe6490410006bd64904101e6f6619041001dfa7090410005f97090410004ff765041003ebe6450410006bd6450410005df7350410005dc73504101def6615041003cff761041001cfe7610410004fd761041001cfc761041003ebe6410410006bd641041001dfa7010410005f97010410004fd76cc410006be64cc410006bd64cc4101d6f661cc410004ff768c410004fd768c410006be648c410006bd648c410006de638c410006dd638c41001dfa708c410005f9708c410004ff764c410005bf744c410005bc744c410006be644c410006bd644c410074ff760c41001cfe760c410004fd760c41001cfc760c410006be640c410006bd640c410076de630c410006dd630c4101cef6610c41001dfa700c410005f9700c41001dfb7644010006fb7644010004fb76440100077b75440101c7787544010007bb7444010007b8744401001fba644401001fb96444010007db7344010007d87344010007eb72440101bfe872440101bf7b52440101bf79524401001dfb714401001ff371440101b6fa614401001ff26144010
  | 1 => 0xc110005f571cc110074ff764c110004fd764c110004fc764c1100057f754c11004d7c754c1100067f654c1100967c654c110006bf644c110006bc644c110006df634c110006dc634c110006ef624c11008eec624c110005f7714c110005f4714c11001fd8304c1100067f65c41100667c65c4110006bf64c4110006bc64c4110006df63c4110006dc63c4110006ef62c4110036ec62c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c41101f77865c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c41101efe862c41101ef7b52c41101ef7952c411001dfa71c411001efb61c411001ff361c41101f7f251c41101f7f151c4110007f241c4110007f141c4110007f331c4110007f031c41101eff221c41101eff121c411003ebf759901003ebe759901003ebd759901003ebc759901003ebf739901003ebe739901003ebd739901003ebc7399010006bf5399010006be5399010006bd5399010006bc539901003ebf729901003ebe729901003ebd729901003ebc7299010006bf52990100063f5299010006be5299010006bd52990100063d5299010006bc5299010006bf3299010006be3299010006bd3299010006bc329901003ebe719901003ebc7199010006bf5199010006be5199010006bd5199010006bc5199010006bf2199010006be2199010006bd2199010006bc219901001ebf709901001ebe709901001ebd709901001ebc709901001ebf509901001ebe509901001ebd509901001ebc509901001ebf309901001ebe309901001ebd309901001ebc309901001ebf209901001ebe209901001ebd209901001ebc209901001ebf109901001ebe109901001ebd109901001ebc1099010004ff7559010014fe7559010004fd7559010014fc755901001ebf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff7359010074fc7359010004ff725901000cfe7259010004fd725901000cfc72590100067f52590100067d5259010006bf4259010006be4259010006bd4259010006bc425901003cff715901003cfd715901001cff705901001cfe705901001cfd705901001cfc705901001ebe405901001ebc405901001ef7105901001ef51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd52590100063d5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006b
  | 2 => 0x265f57250510007e7625051025fe4625051025f77525051025f755250510007f3705051001df6705051001df47050510007f07050510004fe76105100067f651051013e7c6510510006bf641051003ebc6410510006df6310510006dc6310510006ef6210510136ec6210510255f67110510007b5411051001cfe76cc5100067f65cc51012e7c65cc510006bf64cc510006bc64cc510006df63cc510076dc63cc510006ef62cc51010eec62cc51001dfa70cc510005f970cc51001df676cc510006f676cc51001cf676cc51024df775cc51024df575cc5100077765cc5102477465cc510005f774cc510005f574cc510007b764cc51023ef664cc51023ef464cc510007b464cc510006b464cc510006f763cc510007d763cc510006f563cc510007d463cc51021df772cc51021df572cc510007e762cc51010ef662cc51010ef462cc510237e462cc51010ee462cc5102377752cc5102377552cc51001df670cc510007f270cc510007f170cc51001df470cc510004fe768c5100067f658c5101267c658c510006bf648c510006bc648c510006df638c510006dc638c510006ef628c510106ec628c51020df6718c51001cfc764c5100067f654c51011e7c654c510005bf744c510005bc744c510006bf644c510006bc644c510006df634c510006dc634c510006ef624c510116ec624c510005fb704c51001df8704c510004fe760c5100067f650c5100fe7c650c510006bf640c510006bc640c510006df630c510076dc630c510006ef620c5100f6ec620c510005f6760c510006f6760c51022df7750c51022df5750c51000777650c51021774650c510005f7740c510005f5740c510007b7640c510226f6640c510226f4640c510007b4640c510006b4640c51021df6730c510007d6730c510006f7630c510007d7630c510006d7630c510006f5630c510007d4630c510217d6530c510217d5530c510007d7430c510007d4430c51020df7720c51020df5720c510007e7620c5100f6f6620c5100f6f4620c510207e4620c5100f6e4620c51020777520c51020775520c510207d7320c510207d5320c51001df6700c51001df4700c5101ffd6300c5101ffd4300c510004fe76d01100067f65d01100ee7c65d0110006bf64d011003ebc64d0110006df63d0110006dc63d0110006ef62d01100e6ec62d0110005f671d0110005f571d0110007b541d011003cff7650110004fd765011003cfc76501100057f755011004d7c75501100067f65501100ce7c6550110006bf645011003ebc6450110006df6350110006dc6350110006ef62501100c6ec6250110005f77150110005f47150110007b54150110004fe76cc1100067f65cc1100ae7c65cc110006bf64cc110006bc64cc110006df63cc110076dc63cc110006ef62cc110086ec62cc110005f671c
  | 3 => 0xc6210d10005f67110d10005f57110d10045ee76d8910046ee76d891000cee76d89100076f75d89100076c75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891029fe771d8910047e471d8910007e651d8910007e551d891029fe610d891029fe410d8910006ef75d89100066f75d8910006ee75d8910006ed75d8910006ec75d89100066c75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d891029eef71d8910046ee71d8910046ed71d8910046ec71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef70d891029eee70d8910046ed70d891029eec70d8910006ef50d891029eee50d8910006ed50d891029eec50d891029eee40d891029eec40d891029eee30d891029eec30d891029eee10d8910046ed10d891029eec10d891001cfe76d051001cfc76d05100067f65d051016e7c65d0510006bf64d051003ebc64d0510006df63d0510006dc63d0510006ef62d0510166ec62d051001dfa70d0510005f970d0510004fe76905100067f659051015e7c6590510006bf649051003ebc6490510006df6390510006dc6390510006ef6290510146ec6290510005f67690510006f67690510295f77590510295f5759051000777659051028f746590510265f57490510007b7649051003ef6649051003ef46490510007b4649051003eb4649051028fb6549051028fb55490510005f67390510007d76390510007d46390510007b64390510007b44390510255f77290510255f57290510007e76290510287e46290510287775290510287755290510287b74290510287b5429051001df6709051001df4709051027fb6409051027fb4409051001cfc76505100067f65505101567c6550510006bf645051003ebc6450510005df7350510005dc7350510006df6350510006dc6350510006ef625051014eec6250510005fb705051001df8705051001df4765051003ef4765051001cf47650510275f77550510275f5755051000777655051026f746550510007b77450510007b7645051003ef6645051003ef46450510007b46450510007d77350510005f47350510007d47350510005d47350510007d76350510007d46350510265f77250510
  | 4 => 0x8d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10006dd6318d10006ec6218d10074ff7518d10014fe7518d10004fd7518d10074fc7518d1003cfe7418d10004fd7418d10076de7318d10006df5318d10076de5318d10006dd5318d10076dc5318d10074ff7218d1000cfe7218d10004fd7218d1000cfc7218d100067f5218d100067d5218d10076df3218d10006de3218d10006dd3218d10076dc3218d10104fe7118d10074fc7118d1001cfe7018d1001cfc7018d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d100075f5218d100075d5218d101ffd77118d10007d65118d10007d55118d10007d62118d10007d52118d101ffd61018d101ffd41018d10076df7518d10006de7518d10006dd7518d10076dc7518d10076df7418d10006de7418d10006dd7418d10076dc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d10076df7218d10006de7218d10006dd7218d10076dc7218d10006df5218d100065f5218d10006de5218d10006dd5218d100065d5218d10006dc5218d10006df4218d10006de4218d10006dd4218d10006dc4218d10076df7118d10006dd7118d10006df5118d10006de5118d10006dd5118d10006dc5118d10006df2118d10006de2118d10006dd2118d10006dc2118d10076df7018d101fede7018d10006dd7018d10076dc7018d10006df5018d101fede5018d10006dd5018d101fedc5018d101fede4018d101fedc4018d10006df2018d101fede2018d10006dd2018d101fedc2018d101fede1018d10006dd1018d101fedc1018d1003cff76d0d10004fe76d0d10004fd76d0d1003cfc76d0d100067f65d0d101ae7c65d0d10006bf64d0d1003ebc64d0d10006df63d0d10006dc63d0d101a6ec62d0d10005f671d0d10005f571d0d10074ff7690d10004fe7690d10004fd7690d10074fc7690d100067f6590d1019e7c6590d10006bf6490d1003ebc6490d10006df6390d10076dc6390d10186ec6290d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101967c6550d10006bf6450d1003ebc6450d10006df6350d10006dc6350d1018eec6250d10005f77150d10005f47150d10074ff7610d10004fe7610d10004fd7610d10074fc7610d100067f6510d1017e7c6510d10006bf6410d1003ebc6410d10006df6310d10076dc6310d10176e
  | 5 => 0x4fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10006df32d8d10006de32d8d10006dd32d8d10006dc32d8d10006f571d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100075f52d8d100075d52d8d10007d571d8d10007d651d8d10007d551d8d10007d621d8d10007d521d8d102a7d610d8d102a7d410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d100065f52d8d10006de52d8d10006dd52d8d100065d52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d102a6df71d8d10006dd71d8d10006d571d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d102a6de70d8d10006dd70d8d102a6dc70d8d10006df50d8d102a6de50d8d10006dd50d8d102a6dc50d8d102a6de40d8d102a6dc40d8d10006df20d8d102a6de20d8d10006dd20d8d102a6dc20d8d102a6de10d8d102a6dc10d8d1004d7e7598d100057d7598d100067f6598d100067c6598d10005be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10045ee7298d10005ed7298d10006ec6298d10074ff7598d10014fe7598d100767e7598d100147e7598d10004fd7598d100767d7598d100047d7598d10074fc7598d1003cfe7498d10076be7498d1003cbe7498d10004fd7498d10076bd7498d10004bd7498d10074fe7398d10004de7398d10074ff7298d1000cfe7298d10076ee7298d1000cee7298d10004fd7298d10076ed7298d10004ed7298d1000cfc7298d100067f5298d100067d5298d10004fd7198d10076f57198d10004fd7098d10076f97098d100057f7558d1004d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10006bc6458d10005ef7258d10045ec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1003cfc7458d10006bc7458d1003cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d525
  | 6 => 0xf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d911027ebe70d9110006bd70d911027ebc70d9110006bf50d911027ebe50d9110006bd50d911027ebc50d911027ebe30d911027ebc30d9110006bf20d911027ebe20d9110006bd20d911027ebc20d911027ebe10d911027ebc10d911004d7e75991100057d75991100067f65991100067c6599110006bf6499110005de7399110005dd7399110045ee7299110005ed7299110006ec62991100057f755911004d7c75591100067f65591100067c6559110005df7359110005dc7359110005ef7259110045ec7259110006ec6259110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110004ff7359110006df7359110004df7359110074fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec72591100067f52591100067d5259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911003ebe6419110006bd6419110006ec6219110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6219110006be6219110006bd6219110006bc6219110007ac6219110006ac62191100073f52191100073d5219110007b57119110007b65119110007b55119110007b62119110007b521191102afb610191102afb4101911003ebf751911003ebe751911003ebd751911003ebc751911003ebf731911003ebe731911003ebd731911003ebc7319110006bf5319110006be5319110006bd5319110006bc531911003ebf721911003ebe721911003ebd721911003ebc7219110006bf52191100063f5219110006be5219110006bd52191100063d5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911003ebf711911003ebd711911003eb57119110006bf5119110006be5119110006bd5119110006bc5119110006bf2119110006be2119110006bd2119110006bc211911003ebf701911003ebe701911003ebd701911003ebc7019110006bf50191102aebe5019110006bd50191102aebc50191102aebe30191102aebc3019110006bf20191102aebe2019110006bd20191102aebc20191102aebe1019110006bd10191102aebc10191100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10006ec62d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d1003cfe74d8d10004fd74d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10004ff72d8d1000cfe72d8d10
  | 7 => 0x610005dc7350610005fb705061001df870506102aebf641061003ebc6410610076de63cc610006dd63cc61001dfa70cc610005f970cc6102a6df638c6102a6dc638c610005bf744c610005bc744c610006de634c610006dd634c610005fb704c61001df8704c6101fedf630c610076dc630c61001df976c4210006f976c42102bf7b52c42102bf7952c421001ff271c421004d7e76d951004e7e76d95100147e76d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95102b77771d951004f7471d95100077621d95100077521d95102b77610d95102b77410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95102b67f71d951004e7e71d951004e7d71d951004e7c71d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95102b67e70d951004e7d70d95102b67c70d95102b67e40d95102b67c40d95102b67e30d95102b67c30d95100067f20d95102b67e20d95100067d20d95102b67c20d95102b67e10d951004e7d10d95102b67c10d951003cfe76d91100067f65d91100067c65d9110006ec62d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110074fe73d9110004fd73d9110004ff72d911000cfe72d9110004fd72d911000cfc72d91100067f52d91100067d52d9110006bf42d9110006be42d9110006bd42d9110006bc42d911003cfe71d911003cfc71d911001cfe70d911001cfc70d911003cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d91100073f52d91100073d52d911027fb771d9110007b651d9110007b551d9110007b621d9110007b521d911027fb610d911027fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d911027ebf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006b
  | 8 => 0x1d77752cc7101d77552cc71001df670cc71001df470cc71001cfd768c710006de638c710006dd638c71001dfa708c710005f9708c710005bf744c710005bc744c71001cfd760c710076de630c710006dd630c71001dfa700c710005f9700c71001df5760c710006f5760c71001cf5760c7102d5f7750c7102d5f5750c710005f7740c710005f5740c710226f6640c710226f4640c710007d6730c710006f7630c710007d6630c710006f5630c710007d5630c7102cfd6530c7102cfd5530c710007d7430c710007d4430c7102c5f7720c7102c5f5720c7100f6f6620c7100f6f4620c7101cf77520c7101cf75520c7101cfd7320c7101cfd5320c71001df6700c710007f2700c710007f1700c71001df4700c7101ffd6300c7101ffd4300c71003ebe64d0310006bd64d0310005f671d0310005f571d0310007b541d031003cff76503100057f75503100657c755031003ebe6450310006bd6450310005f77150310005f47150310007b54150310076de63cc310006dd63cc310005f671cc310005f571cc3100057f754c3100657c754c310006de634c310006dd634c310005f7714c310005f4714c310004ff7559210014fe7559210004fd7559210014fc755921001ebf7459210006be5459210006bd5459210004ff7359210074fc7359210004ff725921000cfe7259210004fd725921000cfc72592100067f52592100067d5259210006bf4259210006bd425921001cfc705921001ebe405921001ebc405921001ef7105921001ef51059210074ff7598e10014fe7598e10004fd7598e10074fc7598e1003cfe7498e10004fd7498e1001ede7398e10076de5398e10006dd5398e10074ff7298e1000cfe7298e10004fd7298e1000cfc7298e100067f5298e100067d5298e10076df3298e10006dd3298e1001cfe7098e1001ede3098e1001edc3098e1001ef71098e1001ef51098e10004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1003cfc7458e1001edf7358e10006de5358e10006dd5358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e100067f5258e100067d5258e10006df3258e10006dd3258e1001cfc7058e1001ede3058e1001edc3058e1003cff76d0e1001cfe76d0e10004fd76d0e1001cfc76d0e10006de63d0e10006dd63d0e10074ff7690e1001cfe7690e10004fd7690e1001cfc7690e1003ebe6490e10006bd6490e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e10005f77150e10005f47150e10074ff7610e1001cfe7610e10004fd7610e1001cfc7610e1003ebe6410e10006bd6410e10076de6310e10006dd6310e1003ebe64d0610006bd64d061001dfa70d0610005f970d061027ebf649061003ebc649061003cff765061003ebe6450610006bd6450610005df735
  | 9 => 0xf72d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100067f52d8f100067d52d8f10006df32d8f10006dd32d8f10006f671d8f10006f970d8f102a6de30d8f102a6dc30d8f10004fd7698f10006df6398f10074ff7598f10014fe7598f10004fd7598f10074fc7598f1003cfe7498f10004fd7498f10074ff7298f1000cfe7298f10004fd7298f1000cfc7298f100067f5298f100067d5298f10005bf7458f10005bc7458f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f10006bf7458f10004bf7458f1003cfc7458f10006bc7458f1003cbc7458f10006df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10006f47158f10006dd6318f10074ff7518f10014fe7518f10004fd7518f10074fc7518f1003cfe7418f10004fd7418f10074fe7318f10076de7318f10076de5318f10006dd5318f10074ff7218f1000cfe7218f10004fd7218f1000cfc7218f100067f5218f100067d5218f10076df3218f10006dd3218f10076f67118f10076f97018f101fede3018f10076dc3018f1003cff76d0f10004fe76d0f10004fd76d0f1003cfc76d0f10005f671d0f10005f571d0f10074ff7690f10004fe7690f10004fd7690f10074fc7690f10006bf6490f1003ebc6490f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10005f77150f10005f47150f10074ff7610f10004fe7610f10004fd7610f10074fc7610f10006bf6410f1003ebc6410f10005f67110f10005f57110f10006bf64d071003ebc64d071001cfd769071003ebe6490710006bd649071001dfa7090710005f9709071001df5769071003ef5769071001cf5769071030df7759071030df5759071003ef66490710007b66490710007b5649071003ef46490710307b65490710307b55490710005f67390710007b64390710007b443907102fdf772907102fdf572907101e77752907101e77552907101e7b742907101e7b5429071001df67090710007f27090710007f1709071001df4709071027fb6409071027fb44090710006bf645071003ebc6450710005df7350710005dc7350710005f77650710006f776507102f5f775507102f5f57550710007b77450710007b7645071003ef6645071003ef46450710007b46450710007d77350710005f47350710007d47350710005d473507102edf772507102edf572507101df7752507101df75525071001df6705071001df4705071001cfd761071003ebe6410710006bd6410710007b5411071001dfa7010710005f97010710005f576cc710006f576cc7102e5f775cc7102e5f575cc710005f774cc710005f574cc71023ef664cc71023ef464cc710006f763cc710006f563cc7102ddf772cc7102ddf572cc71010ef662cc71010ef462cc710
  | 10 => 0x8430006f62198430006f5219843001ef6109843001ef41098430004ff7558430014fe7558430004fd7558430014fc7558430004ff7458430006bf7458430004bf745843003cfc7458430006bc745843003cbc7458430004ff725843000cfe7258430004fd725843000cfc72584300067f52584300067d525843001ef77158430006f65158430006f55158430076f73158430076f43158430006f62158430006f5215843001ef6105843001ef4105843003cff76d043001cfe76d0430004fd76d043003ebe64d0430006bd64d0430075de73d0430005dd73d0430004ff769043001cfe7690430004fd769043027ebf649043003ebc6490430006f66190430006f56190430004ff7650430004fd765043001cfc765043003ebe6450430006bd6450430005df7350430075dc7350430006f66150430006f5615043003cff761043001cfe7610430004fd76104302aebf641043003ebc6410430004fd768c4302a5dd768c430006dd768c4302a6df658c430346dd658c43033ede648c4302a6dc648c4302a6df628c430336dd628c4303375f528c4303375d528c430075de718c430006dd618c4302a5dd708c4302a6de608c4302a7da608c430004ff764c430005bf744c430005bc744c430076df650c43032edd650c430226de640c430076dc640c430076df620c430326dd620c4303275f520c4303275d520c4302a5de710c430077d6710c430077d6610c430006dd610c430077d5610c430007d7410c430007d4410c430327d7210c430327d4210c430077da700c4301fddd700c430077d9700c430005d9700c4301fede600c430077da600c43001dfb764c030006fb764c030004fb764c0300077b754c03031f78754c03001dfb734c03001fdb734c030076fa634c03001fda634c0303177b524c03031779524c030077db314c030007d9314c0300657e75d93100057d75d9310004ff75d9310014fe75d93100067e75d93100147e75d9310004fd75d93100067d75d93100047d75d9310014fc75d9310006be54d9310006bd54d9310074fe73d9310004fd73d9310004ff72d931000cfe72d9310004fd72d931000cfc72d93100067f52d93100067d52d9310006bf42d9310006bd42d9310006f671d9310006f970d931027ebe40d931027ebc40d9310004fd7699310006bf649931003cff7659310004ff7559310014fe7559310004fd7559310014fc7559310006bf7459310004ff7359310074fc7359310004ff725931000cfe7259310004fd725931000cfc72593100067f52593100067d525931003ebe6419310006bd64193100657e75d8f100057d75d8f10004ff75d8f10014fe75d8f100067e75d8f100147e75d8f10004fd75d8f100067d75d8f100047d75d8f10014fc75d8f1003cfe74d8f10004fd74d8f10006de53d8f10006dd53d8f10004f
  | 11 => 0x67c6598530006f761985300057f75585300957c75585300067f65585300067c6558530005bf7458530005bc7458530005ef725853008dec72585300067f65185300067c6518530006f56118530004ff7518530014fe7518530004fd7518530014fc751853003cfe7418530004fd7418530006de5318530006dd5318530004ff721853000cfe7218530004fd721853000cfc72185300067f52185300067d5218530006df3218530006dd3218530006f72118530006f4211853001cfe701853001cfc70185301fede30185301fedc3018530004fe76d0530004fd76d053003cfc76d05300067f65d053016e7c65d0530006f761d0530006f461d0530004fe7690530004fd7690530004fc76905300067f659053015e7c6590530006bf649053003ebc6490530004ff7650530004fe7650530004fc76505300067f65505301567c6550530005df7350530005dc7350530004fe7610530004fd761053003cfc76105300067f651053013e7c6510530006bf641053003ebc6410530006f76110530006f46110530004fe76cc5300067f65cc53012e7c65cc53001cfe768c5300067f658c5301267c658c530006f7618c530006f4618c53001dfa708c530005f9708c53001cfc764c5300067f654c53011e7c654c530005bf744c530005bc744c530006f7614c530006f4614c530005fb704c53001df8704c530004fe760c5300067f650c5300fe7c650c530004fe76d0130074fc76d01300067f65d01300ee7c65d0130006bf64d013003ebc64d0130005de73d0130005dd73d013003cff7650130004fd765013003cfc76501300057f75501300957c75501300067f65501300ce7c6550130006bf645013003ebc6450130005df7350130005dc73501300067f65cc1300ae7c65cc13001dde73cc13001edf63cc1300077b65cc1303577865cc13001dfa73cc13001efb63cc13001fdb63cc130077da53cc130357d953cc13034f7b52cc13034f7952cc130077db32cc13034fd932cc130004ff7559030014fe7559030004fd7559030014fc755903001cff745903001ebf7459030006be5459030006bd545903003cff7359030074fe735903003cfd7359030074fc7359030076be4359030076bc4359030004ff725903000cfe7259030004fd725903000cfc72590300067f52590300067d5259030006bf4259030006bd4259030004ff7159030004fc715903001cfe705903001cfc705903001ebe405903001ebc4059030004fd76d0c30004ff7650c300779c4350c30005f77150c30005f47150c30004ff7598430014fe7598430004fd7598430014fc759843003cfe7498430004fd7498430004ff729843000cfe7298430004fd729843000cfc72984300067f52984300067d529843001ef67198430006f65198430006f55198430076f73198430076f4319
  | 12 => 0xf62d95300067e62d95300067d62d95300067c62d95300075f32d95300075d32d953035f5e30d953035f5c30d95300067f74d95300067e74d95300067d74d95300067c74d953035e7f73d95300967e73d95300967d73d95300967c73d95300067f72d95300047f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067f32d95300067e32d95300067d32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f21d95300067e21d95300067d21d95300067c21d95300067f70d953035e7e70d95300967d70d953035e7c70d953035e7e40d953035e7c40d953035e7e30d95300967d30d953035e7c30d95300067f20d953035e7e20d95300067d20d953035e7c20d953035e7e10d953035e7c10d953003cfe76d91300067f65d91300067c65d9130004ff75d9130014fe75d9130004fd75d9130014fc75d9130074fe73d9130074fc73d9130004ff72d913000cfe72d9130004fd72d913000cfc72d91300067f52d91300067d52d9130006be42d9130006bc42d9130006df32d9130006dd32d9130004fe71d9130004fd71d91300957e75991300057d75991300067f65991300067c6599130006bf64991300057f75591300957c75591300067f65591300067c6559130005ef725913008dec7259130005f77159130005f47159130004ff75591300067f75591300047f7559130014fe7559130004fd7559130014fc75591300067c75591300147c7559130006bf7459130004ff7359130006df7359130004ff7259130006ef7259130004ef725913000cfe7259130004fd725913000cfc7259130006ec725913000cec72591300067f52591300067d5259130006bf4259130006bd4259130006df3259130006dd3259130004ff7159130006f77159130004f77159130004fc7159130006f47159130004f47159130004ff7059130006fb7059130004fe76191300067f65191300067c651913003ebe6419130006bd641913001cfe76d0d3001cfc76d0d300067f65d0d301ae7c65d0d30006bf64d0d3003ebc64d0d3001dfa70d0d30005f970d0d30004fe7690d300067f6590d3019e7c6590d3003ebe6490d30006bd6490d3001cfc7650d300067f6550d301967c6550d30006bf6450d3003ebc6450d30005f77150d30005f47150d30005fb7050d3001df87050d30004fe7610d300067f6510d3017e7c6510d3003ebe6410d30006bd6410d300067f65d85300067c65d8530004ff75d8530014fe75d8530004fd75d8530014fc75d853003cfe74d8530004fd74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006f721d8530006f421d85300957e75985300057d75985300067f6598530
  | 13 => 0x863001ef6105863001ef41058630006f77558630006f67558630006f57558630006f47558630006f77458630006f67458630006f57458630006f47458630006f75458630006f65458630006f55458630006f45458630006f57358630006f75358630006f65358630006f55358630006f45358630006f74358630006f64358630006f54358630006f44358630006f77258630006f67258630006f57258630006f47258630006f75258630006775258630006f65258630006f55258630006755258630006f45258630006f74258630006f64258630006f54258630006f44258630006f73258630006f63258630006f53258630006f4325863001ef7705863001ef6705863001ef4705863001ef7505863001ef6505863001ef5505863001ef4505863001ef7405863001ef6405863001ef5405863001ef4405863001ef7305863001ef6305863001ef5305863001ef4305863001ef7205863001ef6205863001ef5205863001ef4205863003cff76d063001cfe76d0630004fd76d063003ebe64d0630006bd64d0630005de73d0630005dd73d0630006f661d0630006f561d0630004ff769063001cfe7690630004fd769063003ebe6490630006bd6490630006f66190630006f56190630004ff7650630004fd765063001cfc765063003ebe6450630006bd6450630005df7350630005dc7350630006f66150630006f5615063003cff761063001cfe7610630004fd761063003ebe6410630006bd6410630006f66110630006f56110630006be64cc630006bd64cc630006f661cc630006be648c630006bd648c630006f6618c630006f5618c63001dfa708c630005f9708c6302a6df658c63038edd658c63033ede648c6302a79e648c6300069e648c6302a79d648c6302a6dc648c6302a6df628c630386dd628c6303875f528c6303875d528c6302a7d6618c630006dd618c6302a7d5618c6302a7da708c6302a5dd708c630007d9708c630005bf744c630005bc744c630006be644c630006bd644c630006f6614c630006f5614c630005fb704c63001df8704c630006be640c630006bd640c630006f5610c6301fddd760c630006dd760c6301fedf650c63037edd650c630226de640c6301ff9e640c6300069e640c6301ff9d640c6301fedc640c6301fedf620c630376dd620c6303775f520c6303775d520c630007d6710c6301ffd6610c630006dd610c6301ffd5610c630006d5610c630007d7410c630007d4410c630377d7210c630377d4210c6301fddd700c63001df976cc230076f976cc23001fba64cc23001fb964cc23001fda73cc230077da53cc23036fd953cc2303677b52cc2303677952cc23001ff261cc23001ff161cc2300957e76d95300967e76d95300147e76d953035f5f73d95300975c73d95300057f72d95300057d72d95300067
  | 14 => 0x6bc7559230006bf7359230006bd7359230006bf5359230006be5359230006bd5359230006bc5359230006bf7259230006be7259230006bd7259230006bc7259230006bf52592300063f5259230006be5259230006bd52592300063d5259230006bc5259230006bf3259230006be3259230006bd3259230006bc3259230006bf7159230006be7159230006bd7159230006bc7159230006bf5159230006be5159230006bd5159230006bc5159230006bf2159230006be2159230006bd2159230006bc215923001ebf705923001ebe705923001ebd705923001ebc705923001ebf505923001ebe505923001ebd505923001ebc505923001ebf305923001ebe305923001ebd305923001ebc305923001ebf205923001ebe205923001ebd205923001ebc205923001ebf105923001ebe105923001ebd105923001ebc105923003ebe64d0e30006bd64d0e3001dfa70d0e30005f970d0e3003ebe6490e30006bd6490e3003cff7650e3003ebe6450e30006bd6450e30005f77150e30005f47150e30005fb7050e3001df87050e3003ebe6410e30006bd6410e300079d4310e30004ff7598630014fe7598630004fd7598630014fc759863003cfe7498630004fd7498630004ff729863000cfe7298630004fd729863000cfc72986300067f52986300067d529863001ef67198630006f75198630006f65198630006f55198630006f45198630006f72198630006f62198630006f52198630006f4219863001ef6109863001ef41098630006f77598630006f67598630006f57598630006f47598630006f77498630006f67498630006f57498630006f47498630006f75498630006f65498630006f55498630006f45498630006f77398630006f75398630006f65398630006f55398630006f45398630006f74398630006f64398630006f54398630006f44398630006f77298630006f67298630006f57298630006f47298630006f75298630006775298630006f65298630006f55298630006755298630006f45298630006f74298630006f64298630006f54298630006f44298630006f73298630006f63298630006f53298630006f4329863001ef6709863001ef5709863001ef4709863001ef7509863001ef6509863001ef5509863001ef4509863001ef7409863001ef6409863001ef5409863001ef4409863001ef7309863001ef6309863001ef5309863001ef4309863001ef7209863001ef6209863001ef5209863001ef42098630004ff7558630014fe7558630004fd7558630014fc7558630004ff745863003cfc7458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d525863001ef77158630006f75158630006f65158630006f55158630006f45158630006f72158630006f62158630006f52158630006f4215
  | 15 => 0xf5459330006bc545933001cfc7359330076be4359330076bc4359330004ff725933000cfe7259330004fd725933000cfc72593300067f52593300067d5259330006bf4259330006bd4259330006df3259330006dd3259330004ff7159330004fc7159330005f77150f30005f47150f30076f76198730004ff7598730014fe7598730004fd7598730014fc759873003cfe7498730004fd749873001cfe7398730006de5398730006dd5398730004ff729873000cfe7298730004fd729873000cfc72987300067f52987300067d5298730006df3298730006dd3298730076f73198730076f431987302a6de30987302a6dc3098730076f46158730004ff7558730014fe7558730004fd7558730014fc7558730004ff745873003cfc745873001cfc7358730004ff725873000cfe7258730004fd725873000cfc72587300067f52587300067d5258730076f73158730076f4315873003cff76d0730074fe76d0730004fd76d0730004ff7690730074fe7690730004fd769073003ebe6490730006bd6490730004ff7650730004fd7650730074fc7650730005df7350730075dc735073003cff7610730074fe7610730004fd761073003ebe6410730006bd6410730005bf744c730005bc744c73003ebe64d0330006bd64d0330075de73d0330005dd73d033003cff76503300057f75503300ad7c755033003ebe6450330006bd6450330005df7350330075dc735033003ebf759923003ebe759923003ebd759923003ebc759923003ebf739923003ebd7399230006bf5399230006be5399230006bd5399230006bc539923003ebf729923003ebe729923003ebd729923003ebc7299230006bf52992300063f5299230006be5299230006bd52992300063d5299230006bc5299230006bf3299230006be3299230006bd3299230006bc329923003ebf719923003ebe719923003ebd719923003ebc7199230006bf5199230006be5199230006bd5199230006bc5199230006bf2199230006be2199230006bd2199230006bc219923001ebf709923001ebe709923001ebd709923001ebc709923001ebf509923001ebe509923001ebd509923001ebc509923001ebf309923001ebe309923001ebd309923001ebc309923001ebf209923001ebe209923001ebd209923001ebc209923001ebf109923001ebe109923001ebd109923001ebc1099230004ff7559230014fe7559230004fd7559230014fc755923001ebf7459230006bf5459230006be5459230006bd5459230006bc5459230004ff725923000cfe7259230004fd725923000cfc72592300067f52592300067d5259230006bf4259230006be4259230006bd4259230006bc4259230004ff7159230004fc715923001cfc705923001ebe405923001ebc4059230006bf7559230006be7559230006bd7559230
  | 16 => 0x8440004fd7558440014fc7558440004ff7358440006df7358440004df7358440074fc7358440006dc7358440004dc7358440004ff725844000cfe7258440004fd725844000cfc72584400067f52584400067d525844001ef77158440006f75158440006f65158440006f55158440006f4515844003ef7415844003ebc415844003ef4415844003eb44158440006f72158440006f62158440006f52158440006f4215844001ebf405844001ebd405844001ef6105844001ef41058440006f77558440006f67558440006f57558440006f4755844003ef7745844003ef6745844003ef4745844003ef7545844003ef6545844003ef5545844003ef45458440006f77358440006d77358440006f67358440006f57358440006f47358440006d47358440006f75358440006f65358440006f55358440006f4535844003ef7435844003ef6435844003ef5435844003ef44358440006f77258440006f67258440006f57258440006f47258440006f75258440006775258440006f65258440006f55258440006755258440006f4525844003ef7425844003ef6425844003ef5425844003ef44258440006f73258440006f63258440006f53258440006f4325844001ef7705844001ef6705844001ef4705844001ef7505844001ef6505844001ef5505844001ef4505844001ef7405844001eb7405844001ef6405844001ef5405844001eb5405844001ef4405844001ef7305844001ef6305844001ef5305844001ef4305844001ef7205844001ef6205844001ef5205844001ef4205844003dbd7690440006bd7690440004bd769044003ebf659044039ebd6590440006be639044003ebf6290440396bd62904403973f52904403973d529044003dbe719044003fb6719044003fb66190440006bd619044003fb56190440006b5619044027dbd709044027ebe609044003fba6090440074ff76cc44001cfe76cc440004fd76cc44003dbe74cc440005bd74cc440006f661cc440006f561cc44023fb441cc440004ff768c44001cfe768c440004fd768c440006f6618c440006f5618c440004ff764c440004fd764c44001cfc764c440005bf744c44003dbc744c440006f6614c440006f5614c440074ff760c44001cfe760c440004fd760c440006f6610c440006f5610c440227b4410c440074ff75d9330014fe75d93300767e75d93300147e75d9330004fd75d93300767d75d93300047d75d9330074fc75d9330076de73d9330074ff72d933000cfe72d9330004fd72d933000cfc72d93300067f52d93300067d52d9330076df32d9330006dd32d9330004fe71d9330004fd71d9330076f970d9330004fd7699330076bf6499330076bc649933003cff7659330076bc6459330004ff7559330014fe7559330004fd7559330014fc7559330076bf7459330006b
  | 17 => 0x74fc76cc5400067f65cc54012e7c65cc540005bf74cc54003dbc74cc540006f761cc540006f461cc540007b741cc540004fe768c540004fd768c540004fc768c5400067f658c5401267c658c54003dbe748c540005bd748c540006df638c540006dc638c5400079c438c540004ff764c540004fe764c540004fc764c5400067f654c54011e7c654c540005bf744c54003dbc744c540004fe760c540004fd760c540074fc760c5400067f650c5400fe7c650c54003dbe740c540005bd740c540006df630c540076dc630c5400079c430c540006f7610c540006f4610c540007b7410c540074ff7598c40014fe7598c40004fd7598c40074fc7598c4001cfe7398c4001ede7398c40076de5398c40006dd5398c4003edf4398c40076dc4398c40074ff7298c4000cfe7298c40004fd7298c4000cfc7298c400067f5298c400067d5298c40076df3298c40006dd3298c40004fe7198c40004fd7198c4003ebc4198c4001ebf4098c4001ebd4098c4001ede3098c4001edc3098c40004ff7558c40014fe7558c40004fd7558c40014fc7558c4001edf7358c40006de5358c40006dd5358c4003edf4358c4003edc4358c40004ff7258c4000cfe7258c40004fd7258c4000cfc7258c400067f5258c400067d5258c40006df3258c40006dd3258c40004ff7158c40004fc7158c4001ede3058c4001edc3058c40004ff7598440014fe7598440004fd7598440014fc7598440074fe7398440004fd7398440004ff729844000cfe7298440004fd729844000cfc72984400067f52984400067d529844001ef67198440006f75198440006f65198440006f55198440006f4519844003ef7419844003ef44198440006f72198440006f62198440006f52198440006f4219844001ef6109844001ef41098440006f77598440006f67598440006f57598440006f4759844003ef6749844003ef5749844003ef4749844003ef7549844003ef6549844003ef5549844003ef45498440006f77398440006f67398440006f57398440006f47398440006f75398440006f65398440006f55398440006f4539844003ef7439844003ef6439844003ef5439844003ef44398440006f77298440006f67298440006f57298440006f47298440006f75298440006775298440006f65298440006f55298440006755298440006f4529844003ef7429844003ef6429844003ef5429844003ef44298440006f73298440006f63298440006f53298440006f4329844001ef6709844001ef5709844001ef4709844001ef7509844001ef6509844001ef5509844001ef4509844001ef7409844001ef6409844001ef5409844001ef4409844001ef7309844001ef6309844001ef5309844001ef4309844001ef7209844001ef6209844001ef5209844001ef42098440004ff7558440014fe755
  | 18 => 0xc6390d4001dfa7090d40005f97090d4001cbe7690d4041dbf7590d4041dbd7590d400073f6590d404173c6590d4003dbe7390d40006bf6390d400079f6390d400079c6390d403f5bf7290d403f5bd7290d40186be6290d40186bc6290d4040f3f5290d4040f3d5290d4040f9f3290d4040f9d3290d40005bd7190d4001dbe7090d40007ba7090d40007b97090d4001dbc7090d4003ebf6090d4003fbb6090d4001cfc7650d400067f6550d401967c6550d40006df6350d40006dc6350d40005f77150d40005f47150d40005fb7050d4001df87050d40005be7610d4003ebe7610d4003dbf7510d40405bd7510d400073f6510d403ff3c6510d403f5be7310d4003f9e7310d40006bf6310d4003dbf7210d403edbd7210d40176be6210d40176bc6210d403e73f5210d403e73d5210d40005bd7110d4001dbe7010d4001dbc7010d4003ebf6010d4003fbb6010d400067f65d85400067c65d8540004ff75d8540014fe75d8540004fd75d8540014fc75d8540074fe73d8540004fd73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d85400067f52d85400067d52d8540006f721d8540006f421d85400cd7e75985400057d75985400067f65985400067c6598540006f761985400057f75585400cd7c75585400067f65585400067c6558540005df7358540005dc7358540005ef72585400c5ec72585400067f65185400067c6518540006f56118540004ff7518540014fe7518540004fd7518540014fc7518540006be5418540006bd5418540074fe7318540004fd7318540006be4318540006bc4318540004ff721854000cfe7218540004fd721854000cfc72185400067f52185400067d5218540006bf4218540006bd4218540006f72118540006f421185402aebe40185402aebc4018540005be76d054003ebe76d0540004be76d054003dbf75d05403ddbd75d05400073f65d05403d73c65d0540005be73d054003dbf72d05403cdbd72d05403c73f52d05403c73d52d0540006bc61d054001dbe70d054001dbc70d054003ebf60d054003fbb60d054001cfe76905400067f659054015e7c65905403adbd7490540006f76190540006f4619054001dfa7090540005f9709054001cfc76505400067f65505401567c6550540005df7350540005dc7350540006f76150540006f4615054003fb44150540005fb705054001df8705054001cbc76505403bdbf75505403bdbd75505400073f65505403b73c65505400079f7350540005bc73505400079c73505400059c73505403adbf72505403adbd72505403a73f52505403a73d525054003dbf715054003fb77150540007b76150540006bc6150540007b46150540007bb705054001dbe705054001dbc7050540007b8705054003ebf605054003fbb6050540004fe76cc540004fd76cc540
  | 19 => 0x64027fb5619064027fba709064027dbd7090640007b9709064003ebe6090640005df7350640005dc7350640006f66150640006f56150640005fb705064001df870506402adbd761064003ebd76106402aebf651064043ebd6510640006be63106402aebf6210640436bd62106404373f52106404373d521064003fb67110640006bd611064003dbf70106402adbd701064003fba6010640074ff76cc64001cfe76cc640004fd76cc64003dbe74cc640005bd74cc640006f661cc640006f561cc640007b441cc640004ff768c64001cfe768c640004fd768c640006de638c640006dd638c640004ff764c640004fd764c64001cfc764c640005bf744c64003dbc744c640074ff760c64001cfe760c640004fd760c640076de630c640006dd630c640006f6610c640006f5610c640007b4410c6400cd7e76d95400ce7e76d95400147e76d95404273f74d95400cf3c74d95400057f72d95400057d72d95400067f62d95400067e62d95400067d62d95400067c62d95400073f42d95400073d42d954042f7b40d95404273e40d95404273c40d954042f7840d95404267f74d954042e7e74d95400ce7d74d954042e7c74d95400067f73d95400067e73d95400067d73d95400067c73d954042e7f43d954042e7c43d95400067f72d95400047f72d95400067e72d95400067d72d95400047d72d95400067c72d954042e7f42d95400067e42d95400067d42d954042e7c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d954042e7f41d954042e7c41d95400067f21d95400067e21d95400067d21d95400067c21d954042e7f70d95404267e70d95400ce7d70d95404267c70d954042e7f40d95404267e40d95400ce7d40d95404267c40d95404267e30d95404267c30d95400067f20d95404267e20d95400067d20d95404267c20d95404267e10d95404267c10d95400067f65d8d400067c65d8d40004ff75d8d40014fe75d8d40004fd75d8d40014fc75d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400067f52d8d400067d52d8d40006bf42d8d40006bd42d8d40006de32d8d40006dc32d8d40004fe71d8d40004fd71d8d400cd7e7598d400057d7598d400067f6598d400067c6598d40006df6398d400057f7558d400cd7c7558d400067f6558d400067c6558d40005ef7258d400c5ec7258d40005f77158d40005f47158d400067f6518d400067c6518d40006dd6318d40074ff7518d40014fe7518d40004fd7518d40074fc7518d40074ff7218d4000cfe7218d40004fd7218d4000cfc7218d400067f5218d400067d5218d40006de3218d40076dc3218d40004fe7118d40004fd7118d4001cfe7690d400067f6590d4019e7c6590d40006df6390d40076d
  | 20 => 0x4ff7558740014fe7558740004fd7558740014fc755874001cfc7458740004ff7358740074fc7358740004ff725874000cfe7258740004fd725874000cfc72587400067f52587400067d525874003ef7715874003ef7415874003ef4415874003dbf7650740006bf7650740465bf7550740465bd75507400079f7350740005bc73507400079c73507400059c735074045dbf725074045dbd72507404573f52507404573d525074003fb7715074003fb76150740006be615074003fb4615074001dbe705074001dbc7050740074ff76cc74003cfe76cc740004fd76cc740005bf74cc74003dbc74cc74023fb741cc740004ff768c74003cfe768c740004fd768c74003dbe748c740005bd748c740006de638c740006dd638c74033f9c438c740004ff764c740004fd764c74003cfc764c740005bf744c74003dbc744c740074ff760c74003cfe760c740004fd760c74003dbe740c740005bd740c740076de630c740006dd630c7402279c430c740227b7410c740074ff7598e40014fe7598e40004fd7598e40074fc7598e4001ede7398e40076de5398e40006dd5398e40074ff7298e4000cfe7298e40004fd7298e4000cfc7298e400067f5298e400067d5298e40076df3298e40006dd3298e40004fe7198e40004fd7198e4001cfe7098e4001ebf4098e4001ebd4098e4001ede3098e4001edc3098e40004ff7558e40014fe7558e40004fd7558e40014fc7558e4001edf7358e40006de5358e40006dd5358e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e400067f5258e400067d5258e40006df3258e40006dd3258e40004ff7158e40004fc7158e4001cfc7058e4001ede3058e4001edc3058e40076de6390e40006dd6390e4001dfa7090e40005f97090e40006de6350e40006dd6350e4003f9c4350e40005f77150e40005f47150e40005fb7050e4001df87050e40004ff7598640014fe7598640004fd7598640014fc7598640074fe7398640004fd7398640004ff729864000cfe7298640004fd729864000cfc72986400067f52986400067d529864001ef67198640006f65198640006f55198640006f62198640006f5219864001cfe709864001ef6109864001ef41098640004ff7558640014fe7558640004fd7558640014fc7558640004ff7358640074fc7358640004ff725864000cfe7258640004fd725864000cfc72586400067f52586400067d525864001ef77158640006f65158640006f55158640006f62158640006f5215864001cfc705864001ebf405864001ebd405864001ef6105864001ef41058640006f66190640006f5619064001dfa7090640005f9709064027ebf659064044ebd6590640006be639064027ebf6290640446bd62906404473f52906404473d529064003dbe719064027fb66190640006bd619
  | 21 => 0x7528c4314af75528c431077d7328c4314afd5328c431005f5708c431004ff764c431005bf744c431005bc744c431005df764c431006df764c431004df764c4314a5df754c4314a5dd754c4310079f744c431225de744c431225dc744c4310079c744c4310059c744c43149ddf724c43149ddd724c4314875f524c4314875d524c431075df714c431496de614c43148fd6514c43148fd5514c431007d7414c431007d4414c4311fddc704c431075f7764c431006f7764c431004f7764c431007b7744c431225f6744c431225f4744c431007b4744c431005b4744c431075f7734c431007d7734c431076f6634c431077d6634c431077d6534c43148fd5534c431007d7434c431077d4434c4310f5f6724c4310f5f4724c43148777524c43148775524c431005f7704c431076fb609803101ef860980310057f75580310fd7c7558031076f86058031004ff75580310067f75580310047f7558031014fe7558031004fd7558031014fc75580310067c75580310147c7558031004ff745803103cfc7458031006de5358031006dd5358031004ff725803100cfe7258031004fd725803100cfc72580310067f52580310067d5258031006df3258031006dd3258031076fb3058031076f83058031006fa2058031006f92058031074ff7598f40014fe7598f40004fd7598f40074fc7598f4001cfe7498f40076de7398f40006df5398f40076dc5398f4003edf4398f40076dc4398f40074ff7298f4000cfe7298f40004fd7298f4000cfc7298f400067f5298f400067d5298f40076df3298f40006dd3298f40004fe7198f40004fd7198f40004ff7558f40014fe7558f40004fd7558f40014fc7558f4001cfc7458f4001cbc7458f4003edf7358f40006df5358f40006dc5358f4003edf4358f4003ebc4358f4003edc4358f4003e9c4358f40004ff7258f4000cfe7258f40004fd7258f4000cfc7258f400067f5258f400067d5258f4003ebf4258f40006bd4258f40006df3258f40006dd3258f40004ff7158f40006f77158f40004f77158f40004fc7158f40006f47158f40004f47158f4003dbd7690f40006bd7690f4047dbf7590f4047dbd7590f4003f9e7390f40006bd6390f40475bf7290f40475bd7290f40186be6290f4003ebc6290f4046f3f5290f4046f3d5290f4046f9f3290f4046f9d3290f40005bd7190f4001dbe7090f4001dbc7090f40004ff7598740014fe7598740004fd7598740014fc759874001cfe749874001cbe749874003ebe5498740006bd5498740074fe7398740004fd7398740006be439874003ebc4398740004ff729874000cfe7298740004fd729874000cfc72987400067f52987400067d529874003ebf4298740006bd429874003ef6719874003ebf419874003ef7419874003ef4419874027ebe409874003ebc4098740
  | 22 => 0x9031004ff7559031014fe7559031004fd7559031014fc7559031076bf7459031006bf5459031006bc5459031074fe7359031074fc7359031006dc7359031076be4359031076bc4359031004ff725903100cfe7259031004fd725903100cfc72590310067f52590310067d5259031006bf4259031006bd4259031006df3259031006dd3259031006f47159031004ff705903101cfc7059031004fd76d0c31005dd76d0c31226dd76d0c31225df75d0c3152ddd75d0c31075de74d0c31226df64d0c31226dd64d0c31225df72d0c31525dd72d0c3151f5f52d0c3151f5d52d0c312279f42d0c3151f9d42d0c31227d771d0c31005dd71d0c31227d471d0c3133ede61d0c3151fd721d0c3151fd421d0c311fdde70d0c31004ff7650c310779c4350c31005f77150c31076dd7610c31004dd7610c31075df7510c31515dd7510c31225de7410c310779e7410c31076df6410c310779e6410c31226dd6410c310779d6410c31075df7210c3150ddd7210c315075f5210c315075d5210c315079e4210c312279c4210c31077d67110c31005dd7110c31077d57110c3133ede6110c31507d72110c31507d42110c311fdde7010c31004fd76d0431005f576d0431226f576d0431226f764d0431226f564d0431227d773d0431005f573d0431227d473d043123ef663d04314ffd653d04314ffd553d0431227d743d0431227d443d04310f5f672d04310f5f472d04314f77752d04314f77552d04314f7d732d04314f7d532d0431005f570d0431004ff769043103cfd769043103ebe6490431006bd6490431075de7390431005dd73904310079c4390431225f67190431004ff7650431005df7350431075dc735043103cff7610431074fe7610431004fd7610431074fc761043103ebe6410431006bd6410431075de7310431005dd73104312279c4310431007b54110431005f57610431226f57610431004f57610431225f67410431227b67410431226f76410431227b66410431226f56410431007b56410431227b654104314efb55410431227d67310431005f57310431227d5731043123ef663104314efd653104314efd55310431227d743104314e7b643104314e7b44310431227d443104312279443104310f5f672104310f5f472104314df7752104314df755210431227b742104314dfb542104314dfd732104314dfd53210431005f57010431075df75cc4314d5dd75cc431225de74cc431075dc74cc431075df72cc4314cddd72cc4314c75f52cc4314c75d52cc431007d741cc431007d441cc4314c7d721cc4314c7d421cc4311fdde70cc43149ddd738c4314bede638c431225f6748c431225f4748c431075f5738c431076f6638c431077d6638c431077d6538c4314b7d5538c431007d7438c431077d4438c4310f5f6728c4310f5f4728c4314af7
  | 23 => 0x6bd6219131006bc62191310073f52191310073d521913103ebf751913103ebe751913103ebd751913103ebc751913103ebf731913103ebd7319131006bf5319131006be5319131006bd5319131006bc531913103ebf721913103ebe721913103ebd721913103ebc7219131006bf52191310063f5219131006be5219131006bd52191310063d5219131006bc5219131006bf3219131006be3219131006bd3219131006bc321913103ebf711913103ebd7119131006bf5119131006be5119131006bd5119131006bc5119131006bd3119131006bf2119131006be2119131006bd2119131006bc211913103ebf701913103ebe701913103ebd701913103ebc7019131006bf5019131006be5019131006bd5019131006bc5019131006bf2019131006be2019131006bd2019131006bc2019131004fe76d0d31006bf64d0d3103ebc64d0d31005f671d0d31005f571d0d31004fe7690d31006bf6490d3103ebc6490d3103cfc7650d31006bf6450d3103ebc6450d31005f77150d31005f47150d31004fe7610d31006bf6410d3103ebc6410d31004fe76d0531074fc76d0531006bf64d053103ebc64d0531005de73d0531005dd73d0531004fe7690531006bf649053103ebc649053103cff7650531004fd765053103cfc7650531006bf645053103ebc6450531005df7350531005dc7350531004fe7610531006bf641053103ebc6410531006bf64cc531006bc64cc531007b764cc53123ef664cc53123ef464cc531007b464cc531006b464cc53110ef662cc53110ef462cc5315477752cc5315477552cc531006bf648c531006bc648c53153edf658c53153edd658c5310079f648c53133ede648c53133edc648c5310079c648c5310069c648c531536df628c531536dd628c5315375f528c5315375d528c531007d7618c531006bf64d8131006bc64d8131004ff75d8131014fe75d8131004fd75d8131014fc75d813103cfe74d8131004fd74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006f731d8131005be7498131005bd7498131006bf6498131006bc6498131006fb60981310057f755813111d7c7558131005bf7458131005bc7458131006bf6458131006bc6458131005ef7258131115ec7258131006bf6418131006bc64181312a6df631813101efa6018131006f96018131074ff75d9031014fe75d90310767e75d90310147e75d9031004fd75d90310767d75d90310047d75d9031074fc75d9031074fe73d9031076de73d9031074ff72d903100cfe72d9031004fd72d903100cfc72d90310067f52d90310067d52d9031076df32d9031006dd32d9031004fe71d9031076f671d903101cfe70d9031004fd70d9031004fd7699031076bf6499031076bc649903103cff7659031076bc645
  | 24 => 0xe7010e3103cfd769063103ebe6490631006bd6490631005de7390631005dd73906310079c4390631005df7350631005dc735063103ebe6410631006bd6410631005de7310631005dd731063133f9c4310631005dd76cc631006dd76cc63155ddf75cc63155ddd75cc63133dde74cc63133ddc74cc6314bddf72cc6314bddd72cc63154f5f52cc63154f5d52cc631557d651cc631557d551cc6312a5de70cc631005f576cc631076f576cc63123ef664cc63123ef464cc631077d653cc631557d553cc63110ef662cc63110ef462cc63154f7752cc63154f7552cc6311257e75d82310057d75d8231006fb6098231004ff7558231014fe7558231004fd7558231014fc7558231004ff745823103cfc7458231006de5358231006dd5358231004ff725823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231006df3258231006dd3258231006f73158231005be7418231005bd741823101efa6018231006f9601823103cfe76d9131004ff75d9131014fe75d9131004fd75d9131014fc75d9131006bf54d9131006be54d9131006bd54d9131006bc54d9131004ff72d913100cfe72d9131004fd72d913100cfc72d91310067f52d91310067d52d9131006bf42d9131006be42d9131006bd42d9131006bc42d913101cfe70d9131004fd70d913103cbe76d9131006bf65d9131006be65d9131006bd65d9131006bc65d9131006bf62d9131006be62d9131006bd62d9131006bc62d91310073f52d91310073d52d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d9131006bd73d9131006bf53d9131006be53d9131006bd53d9131006bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d91310063f52d9131006be52d9131006bd52d91310063d52d9131006bc52d9131006bf32d9131006be32d9131006bd32d9131006bc32d9131006bf71d9131006bd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d9131006bf21d9131006be21d9131006bd21d9131006bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d9131006bf20d9131006be20d9131006bd20d9131006bc20d9131006bf6499131004ff7559131014fe7559131004fd7559131014fc7559131006bf7459131004ff7359131006df7359131004df7359131004ff725913100cfe7259131004fd725913100cfc72591310067f52591310067d5259131004ff7159131006f77159131004f77159131004ff705913101cfc7059131004fe761913103ebe6419131006bd6419131005be7619131006be7619131004be7619131006bf6519131006be6519131006bd6519131006bc6519131006bf6219131006be6219131
  | 25 => 0x9331006be5459331006bd5459331076be4359331076bc4359331004ff725933100cfe7259331004fd725933100cfc72593310067f52593310067d5259331006bf4259331006bd4259331006f77159331004ff705933101cfc7059331005f47150f3103ebe64d0731006bd64d0731075de73d0731005dd73d0731005f576d073123ef576d073123ef764d073123fb664d073123ef564d0731007b564d073123fd673d0731005f573d073123fd573d073110df672d073110df472d07315a77752d07315a77552d0731005f570d0731006bf649073103ebc649073103cff765073103ebe6450731006bd6450731005df7350731075dc7350731006bf641073103ebc6410731007b54110731005f5761073123ef5761073123fb6741073123ef764107314e7b7641073123ef564107314e7b4641073123fb6541073159fb55410731005f573107314e7b643107314e7b4431073110df6721073110df4721073159777521073159775521073123fb74210731597b54210731005f57010731005be7498331005bd7498331076fb609833101ef86098331076f86058331004ff7558331014fe7558331004fd7558331014fc7558331004ff745833103cfc7458331004ff725833100cfe7258331004fd725833100cfc72583310067f52583310067d5258331076fb3058331076f83058331004ff75d9231014fe75d9231004fd75d9231014fc75d9231006dd73d9231004ff72d923100cfe72d9231004fd72d923100cfc72d92310067f52d92310067d52d9231006bf42d9231006bd42d9231006df32d9231006dd32d9231006f671d923101cfe70d9231004fd70d9231004fd7699231006bf649923103cff7659231004ff7559231014fe7559231004fd7559231014fc7559231006bf7459231006df7359231004ff725923100cfe7259231004fd725923100cfc72592310067f52592310067d5259231006be4259231006bc4259231006df3259231006dd3259231004ff705923101cfc705923103ebe6419231006bd641923103ebe64d0e31006bd64d0e31005f671d0e31005f571d0e3133edd76d0e3133ddf75d0e3158ddd75d0e3133edf64d0e3133f9e64d0e3133edd64d0e310079d64d0e3133ddf72d0e31585dd72d0e3157f5f52d0e3157f5d52d0e3133f9f42d0e3157f9d42d0e3133fd671d0e31005dd71d0e3133fd571d0e312a5de70d0e31006bf6490e3103ebc6490e3103cff7650e3103ebe6450e31006bd6450e31005f77150e31005f47150e31006bf6410e3103ebc6410e310079d4310e31005dd7610e3133edd7610e3133ddf7510e31575dd7510e3133f9e7410e3133edf6410e310079f6410e3133edd6410e3133f9c6410e3133ddf7210e3156ddd7210e315675f5210e315675d5210e315679e4210e3133f9c4210e31005dd7110e312a5d
  | 26 => 0x3fb76190541005bd7090541006df63d8141006dc63d8141004ff75d8141014fe75d8141004fd75d8141014fc75d8141074fe73d8141004fd73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d8141005de7398141005dd7398141006df6398141006dc6398141006fb60981410057f75581411557c7558141005df7358141005dc7358141006df6358141006dc6358141005ef725814114dec725814127ebf6418141006df6318141006dc631814101efa6018141006f96018141074ff7598c41014fe7598c41004fd7598c41074fc7598c41076de7398c4103edf4398c41076dc4398c41074ff7298c4100cfe7298c41004fd7298c4100cfc7298c410067f5298c410067d5298c41076df3298c41006dd3298c4101cfe7098c41004fd7098c41004ff7558c41014fe7558c41004fd7558c41014fc7558c4103edf7358c4103edf4358c4103ebc4358c4103edc4358c41004ff7258c4100cfe7258c41004fd7258c4100cfc7258c410067f5258c410067d5258c4103ebf4258c41006bd4258c41006df3258c41006dd3258c41006f47158c41004ff7058c4101cfc7058c4103dbd7690c41006bd7690c415edbf7590c415edbd7590c4103dbe7390c4103f9e7390c41006bd6390c415e5bf7290c415e5bd7290c41186be6290c4103ebc6290c415df3f5290c415df3d5290c415df9f3290c415df9d3290c414e7b77190c41005bd7190c414e7b47190c415d6be6190c4103fb66190c412adbe7090c4103dbf7650441006bf7650441004bf76504415cdbf75504415cdbd75504410079f7350441005bc73504410079c73504410059c73504415c5bf72504415c5bd72504415af3f52504415af3d525044103dbf715044103fb771504415bebe615044103fb661504415b7b651504415b7b551504415afb721504415afb421504412adbc7050441004ff75580410067f75580410047f7558041014fe7558041004fd7558041014fc75580410067c75580410147c755804103ebe5458041006bd5458041004ff7358041074fc7358041006be435804103ebc4358041004ff725804100cfe7258041004fd725804100cfc72580410067f52580410067d525804103ebf4258041006bd425804103ebf415804103ef64158041006bd415804103ef5415804103efb705804103efb405804103ebc405804103ef84058041006fa2058041006f92058041074ff75d9331014fe75d9331004fd75d9331074fc75d9331076de73d9331074ff72d933100cfe72d9331004fd72d933100cfc72d93310067f52d93310067d52d9331076f571d933101cfe70d9331004fd70d9331004fd7699331076bf6499331076bc649933103cff7659331076bc6459331004ff7559331014fe7559331004fd7559331014fc7559331076bf745
  | 27 => 0xc62d8d410075f52d8d410075d52d8d4133fd741d8d4133fd441d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d41006df74d8d4133ede74d8d41006df54d8d4133ede54d8d41006dd54d8d4133edc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d410065f52d8d41006de52d8d41006dd52d8d410065d52d8d41006dc52d8d4133edf42d8d41006de42d8d41006dd42d8d4133edc42d8d4133edf71d8d41006dd71d8d41006df51d8d41006de51d8d41006dd51d8d41006dc51d8d4133edf41d8d4133edc41d8d41006df21d8d41006de21d8d41006dd21d8d41006dc21d8d41006df70d8d41006de70d8d41006dd70d8d41006dc70d8d41006df50d8d41006de50d8d41006dd50d8d41006dc50d8d4133edf40d8d4133edc40d8d41006df20d8d41006de20d8d41006dd20d8d41006dc20d8d41006df6398d41006dd6318d41074ff7518d41014fe7518d41004fd7518d41074fc7518d41006df5318d41076de5318d41006dd5318d41076dc5318d41074ff7218d4100cfe7218d41004fd7218d4100cfc7218d410067f5218d410067d5218d41076df3218d41006de3218d41006dd3218d41076dc3218d41226f74118d41226f44118d4101cfe7018d41004fd7018d41005de7618d41006de7618d41006df6518d41006de6518d41006dd6518d41006dc6518d41006df6218d41006de6218d41006dd6218d41006dc6218d410075f5218d410075d5218d41227d74118d41227d44118d41076df7518d41006de7518d41006dd7518d41076dc7518d41076df7418d41226de7418d41006df5418d41226de5418d41006dd5418d41226dc5418d41076df7218d41006de7218d41006dd7218d41076dc7218d41006df5218d410065f5218d41006de5218d41006dd5218d410065d5218d41006dc5218d41226df4218d41006de4218d41006dd4218d41226dc4218d41076df7118d41006dd7118d41006df5118d41006de5118d41006dd5118d41006dc5118d41226df4118d41226d74118d41006dd4118d41226dc4118d41226d44118d41006df2118d41006de2118d41006dd2118d41006dc2118d41076df7018d41006de7018d41006dd7018d41076dc7018d41006df5018d41006de5018d41006dd5018d41006dc5018d41226df4018d41226dc4018d41006df2018d41006de2018d41006dd2018d41006dc2018d41006df6390d41076dc6390d41005f67190d41005f57190d4103fb44190d41006df6350d41006dc6350d41005f77150d41005f47150d41006df6390541006dc639054103df6719054103ef761905415febf65905415febd65905410079f6390541006bc63905410079c63905410069c63905415f6bf62905415f6bd62905415f73f52905415f73d529054103dbe719054103ebf6190541
  | 28 => 0x8f4103edc4358f41004ff7258f4100cfe7258f41004fd7258f4100cfc7258f410067f5258f410067d5258f41006df3258f41006dd3258f41006f77158f41004ff7058f4101cfc7058f41004ff7558341014fe7558341004fd7558341014fc7558341004ff7358341074fc7358341004ff725834100cfe7258341004fd725834100cfc72583410067f52583410067d525834103ef6415834103ef5415834103efb705834103efb405834103ef84058341006df6398e41074ff7598e41014fe7598e41004fd7598e41074fc7598e41074ff7298e4100cfe7298e41004fd7298e4100cfc7298e410067f5298e410067d5298e4123ef74198e4123ef44198e4101cfe7098e41004fd7098e41004ff7558e41014fe7558e41004fd7558e41014fc7558e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e410067f5258e410067d5258e41006bf4258e41006bd4258e41004ff7058e4101cfc7058e4115d7e7518e410057d7518e41006dd6318e41076de6390e41006dd6390e41005f67190e41005f57190e41645bf7590e41645bd7590e4103dbe7390e410079e6390e41006bd6390e410079d6390e4163dbf7290e4163dbd7290e41186be6290e41186bc6290e415d73f5290e415d73d5290e415d79f3290e415d79d3290e41007b67190e41005bd7190e41007b57190e4103ebe6190e4127dbe7090e41006de6350e41006dd6350e4103f9c4350e41005f77150e41005f47150e41005bd7610e4103ebd7610e4103dbf7510e41635bd7510e4103f9e7310e410079f6310e41006bd6310e410079c6310e4103dbf7210e4162dbd7210e41176be6210e41176bc6210e416273f5210e416273d5210e41005bd7110e4103fb66110e4127dbe7010e41005bd76d064103ebd76d064103dbf75d064161dbd75d0641005be73d064103dbf72d0641615bd72d064160f3f52d064160f3d52d064103fb661d0641607b651d0641607b551d064127dbe70d064115d7e75d82410057d75d8241006fb6098241004ff7558241014fe7558241004fd7558241014fc7558241006be5458241006bd5458241004ff7358241074fc7358241006be4358241006bc4358241004ff725824100cfe7258241004fd725824100cfc72582410067f52582410067d5258241006bf4258241006bd4258241006bf415824101efa6018241006f96018241004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d41006df53d8d41006de53d8d41006dd53d8d41006dc53d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d410067f52d8d410067d52d8d41006df32d8d41006de32d8d41006dd32d8d41006dc32d8d4101cfe70d8d41004fd70d8d41006df65d8d41006de65d8d41006dd65d8d41006dc65d8d41006df62d8d41006de62d8d41006dd62d8d41006d
  | 29 => 0x6f45218543226f74218543006b74218543006f64218543006f54218543006b54218543226f44218543006f73218543006d73218543006f63218543006f53218543006d53218543006f43218543006f77018543006f67018543006f57018543006f47018543006f75018543006f65018543006f55018543006f45018543226f74018543226f44018543006f72018543006f62018543006f52018543006f42018543006f761d8143006f461d8143004ff75d8143014fe75d8143004fd75d8143014fc75d8143006be43d8143004ff72d814300cfe72d8143004fd72d814300cfc72d81430067f52d81430067d52d8143006bf42d8143006bd42d8143006df32d8143006dd32d8143004fe71d8143004fd71d8143005f67198143005f57198143006f76198143006f46198143006fb60981430057f75581431957c7558143005ef725814318dec7258143005f77158143005f47158143006f76158143006f46158143006f76118143006f4611814301efa6018143006f96018143075bf7650c43006bf7650c43004bf7650c43075bf7350c4303f9f7350c43076be6350c430779e6350c430779e5350c436579d5350c43175be7250c43175bc7250c43076bf6250c4364ebd6250c4364f3f5250c4364f3d5250c430779f3250c4364f9d3250c43007b77150c43005bc7150c43007b47150c43005b47150c43005bf7050c43004ff7598443014fe7598443004fd7598443014fc7598443004ff729844300cfe7298443004fd729844300cfc72984430067f52984430067d5298443076f6719844303ef7419844303ef44198443076f73198443076f4319844301cfe7098443004fd7098443004ff7558443014fe7558443004fd7558443014fc7558443004ff725844300cfe7258443004fd725844300cfc72584430067f52584430067d5258443076f7715844303ef7415844303ebc415844303ef44158443076f73158443076f43158443004ff705844301cfc705844303ebf4058443004ff75580430067f75580430047f7558043014fe7558043004fd7558043014fc75580430067c75580430147c7558043004ff725804300cfe7258043004fd725804300cfc72580430067f52580430067d5258043004ff7158043004fc7158043076fb705804303efb405804303ef84058043076fb3058043076f83058043074ff7598f41014fe7598f41004fd7598f41074fc7598f41076de7398f41076de5398f41006dd5398f4103edf4398f41076dc4398f41074ff7298f4100cfe7298f41004fd7298f4100cfc7298f410067f5298f410067d5298f41076df3298f41006dd3298f4103ebc4198f4101cfe7098f41004fd7098f4103ebf4098f41004ff7558f41014fe7558f41004fd7558f41014fc7558f4103edf7358f41006de5358f41006dd5358f4103edf435
  | 30 => 0xc6290d4365f3f5290d4365f3d5290d430779f3290d4365f9d3290d43004ff75d8543014fe75d8543004fd75d8543014fc75d8543004ff72d854300cfe72d8543004fd72d854300cfc72d85430067f52d85430067d52d8543006f751d8543006f651d8543006f551d8543006f451d8543006f721d8543006f621d8543006f521d8543006f421d854301cfe70d8543004fd70d8543006f765d8543006f665d8543006f565d8543006f465d854323fd743d8543007b643d854323fd443d8543006f762d8543006f662d8543006f562d8543006f462d85430077752d85430077552d8543007b742d8543007b542d8543007d732d8543007d532d8543006f775d8543006f675d8543006f575d8543006f475d8543006f774d854323ef674d8543006f754d854323ef654d8543006f554d854323ef454d854323ef773d8543006f753d8543006f653d8543006f553d8543006f453d854323ef743d8543006f643d854323ef443d8543006f772d8543006f672d8543006f572d8543006f472d8543006f752d85430067752d8543006f652d8543006f552d85430067552d8543006f452d854323ef742d8543006f642d8543006f542d854323ef442d8543006f732d8543006f632d8543006f532d8543006f432d8543006f770d8543006f670d8543006f570d8543006f470d8543006f750d8543006f650d8543006f550d8543006f450d854323ef740d854323ef440d8543006f720d8543006f620d8543006f520d8543006f420d8543006f76198543006f56118543004ff7518543014fe7518543004fd7518543014fc7518543226df4318543006be4318543226dc4318543004ff721854300cfe7218543004fd721854300cfc72185430067f52185430067d5218543006bf4218543006bd4218543006df3218543006dd3218543006f75118543006f65118543006f55118543006f45118543006f72118543006f62118543006f52118543006f4211854301cfe7018543004fd7018543005f67618543006f67618543006f76518543006f66518543006f56518543006f46518543227d74318543007b64318543227d44318543006f76218543006f66218543006f56218543006f46218543007775218543007755218543007b74218543007b54218543007d73218543007d53218543006f77518543006f67518543006f57518543006f47518543006f77418543226f67418543006f75418543226f65418543006f55418543226f45418543226f77318543006f75318543006f65318543006f55318543006f45318543226f74318543226d74318543006f64318543006b64318543006f54318543226f44318543226d44318543006f77218543006f67218543006f57218543006f47218543006f75218543006775218543006f65218543006f55218543006755218543
  | 31 => 0x402400200b803002000d001800402c003001000803e00900000280020000008010008008000000000000400a00000000000108010006004000002c0280010000014016002000801800000f00b80080160060008018002003001800000a0070018004000001003000000000000080000160050030000008000000000800401100200000040030010020010005009001400600e00000a40080010048000000012001801000600900180000080020060010006012006002c0120090028000000006000800406a00e001001400600e0098000000001000800400600b004ff7598743014fe7598743004fd7598743014fc759874303ebc4398743004ff729874300cfe7298743004fd729874300cfc72987430067f52987430067d529874303ebf4298743006bd429874303ef6719874303ef7419874303ef44198743006f72198743006f4219874301cfe7098743004fd7098743004ff7558743014fe7558743004fd7558743014fc7558743004ff725874300cfe7258743004fd725874300cfc72587430067f52587430067d525874303ef7715874303ef7415874303ef44158743006f72158743006f42158743004ff705874301cfc7058743004ff7558343014fe7558343004fd7558343014fc755834303ebc4358343004ff725834300cfe7258343004fd725834300cfc72583430067f52583430067d525834303ebf4258343006bd4258343004ff7158343004fc715834303efb705834303efb405834303ef84058343075bd76d0e4303ebd76d0e430779e63d0e430779e53d0e436779d53d0e43185be72d0e4303dbc72d0e43076bf62d0e4366ebd62d0e4366f3f52d0e4366f3d52d0e43005be71d0e43005bd70d0e43076f76198643004ff7598643014fe7598643004fd7598643014fc7598643074fe739864333edf439864333edc4398643004ff729864300cfe7298643004fd729864300cfc72986430067f52986430067d5298643006df3298643006dd3298643076f73198643076f4319864301cfe7098643004fd7098643076f46158643004ff7558643014fe7558643004fd7558643014fc7558643074fc7358643004ff725864300cfe7258643004fd725864300cfc72586430067f52586430067d5258643076f73158643076f43158643004ff705864301cfc7058643005f67198243005f57198243076fb609824301ef86098243076f86058243004ff7558243014fe7558243004fd7558243014fc7558243074fc7358243004ff725824300cfe7258243004fd725824300cfc72582430067f52582430067d5258243006df3258243006dd3258243004ff7158243004fc7158243076fb3058243076f8305824303dde7390d4303edf6390d43075be7390d43076bf6390d4303f9f6390d43075bf7290d43665bd7290d43186be6290d43186b
  | 32 => 0x1000000800e003000002401a001000805400c008003800804a00d0048004006005003000c00200e000003804a001003000800200a0068000014004000003c01a00800180000000020010004014000000003000a00c000800800200b003801800c0020138028000000003800000600100300240480000050004004006001002800000c000800800600000400000080020008000002000000800c02c00701700300000050050004000000004000400000000000000000020000010008002010800000a016005800800400e000007c000000001000001e0030050000004000001800c028002001005c00c0020040044010000000001802000500100000020020000014008006008800c0000030090004000002000005801e0010000000000002000000000a0050058008006003001001c0100040000010008003000804002a004002803000a000000000802200c0000028000009004800408c000003003c000000000000c036001002800400c0040000000002002001000c00400f00300000000010060004000002004000000a002000800000000a0028008004000000003c00200300980040160100000000002000000003c000025000002800000200080c0000007001002c000001001000c00200e00580000040000008004004003000800001600100380280000030018014000003000801400600b0010008014000002801000400b00900040020000000000000001001806c00e00000100440100160078000016002002801c0080070058078006003006000801000b0010014046005007800802200b00000100000000000010000003000002400800301000080000060000014002003000000c03202a0080014002002004000c00200000f001c000000007800803a000002000c0120030000008006003004001000e018000002c006000000001000800c000800400e00000300080000000000008000020000800001c00101080280100020018010002003000800000000000080080000050028028012000004807800000500180140000040040000000007005801000a005005803c0000010000040002001018800000001700600300100020090004010004004800000e000006000400000200000040040000020014012000000800000000600000000020000030000004004001001000a001006801c0020000168018004007000000000a001009803800000000b000c006003002000400a01b005000000000c009800800401100100040000000000068014000000000401400b00100000000000000000022015002000000800d00100c800c00200000000000030080000006001000802c01e000002800000800000000080020000020004000000000800000a0040068000002001000002800a002001800800c00300300000000000008000002000000000
  | 33 => 0x2800001500a80400060100000004000012000800000c0040008004012000000800c000001000000000c00d0048000002000000801000c0300010000012001000000802000c000000c000009000000800601b00000d400c0000038000034005000001001205e001000c002010004000402e01f000000401200200c001000200000c0004000004000000402a00001380240020020030008000000001800000400100a8048002000005808c00000000880000160000008018000001000801000402d0020000002005002000800800c00000000000030008000000008000803c01401c004800000000000080240080000020014044003000800000800400180000000000020010000001001001c00600000000000000080020000000006000000800603c0030028022000001001000001b00f8010002052001801800800d00a800000c004001800000a0020030018012007000002000a0000000004000000005001400c01a000800400000000b0000008000000800000000a000000003a00500f0000010000000000403201400000080060040000000012005019802001000400b000802800700a000000000100400000000010008000000004004800c01a00000000040260090038000024000002000000600400f8000006003000801c0000040020054000000004000c002008001000000e001004001c006002007000c000000001800800801a00200140020080008018000004011002c01a00500d000c072012006000801e005000001c00200d006002000800100300000180000038010004001001000002c0170000000008002004001800000100a801802a00a00000040000290030000000021000005800400f0000044000002001802c008002000001001200600200080040000008000004025003800000e002000001c00400700000140020060090030002003002000801001b00180080080010000060004002000800001a000000000c028006001003c0000120020000002012008804c00c00000d0010010008007801800000f000800400c00e00580180020010040000002007001000000000000100340080120000008018002001800002a000000000000a0010008004000000001806800a000000000c00a01400300080020000050094000001006800c006000000805000601200400240060010000010002002000000000e0140000000012007004000002c00600000bc0100010010048008001001000002a018002000800200400100000020120008004008015003800800201d0018034002005000001800200200000280580040038014000002000800c01200b00300080060000058000000015015000800000900300100060060020000000003000000001c005001000c012003002000000000c00000000280040018014014004003802000200
  | 34 => 0x17f40001ca8940191000028160001bec2cf900a00020be132291205e800068f003a5de05ca8ba82742d000000001c608f4214e4b099ce62f25fe5ee0d4c714120e877800082d223e37d183c037994251a00001aea7288fd8da899c058025d1be06a7a70a00001649af84506c088847e3a4386aaa7868cf00005b4960427b9cc80000000000141e0000752047800076ba11400005068658b7c0e99f2e4599b1c0002484175000000019fc4e9261600000000000b208621b480000000058a566757845660ba6ca7d220125d719ee2b9a1687ca8d1a27317b04af032a3518bcc95b1eb6000156a2201a8088a98de1f320da2b01a100000000000077e934988c67500004191a6a06810b455118d403e991a6591d0e886000092988b61e2000049801c036b80006a18000000248820b9dcc9152672000000000000003ab20845e624966a61b64423a70446d0706691979a422a7b233085a27aaaa164f114240ba89c6000006000000a0008014004003000800004a001010800000000c010003800600100280cc000000005800000001100000dc00200200000640000030028000006000002800403e002001800000000a000801c010004005803403601c00b800800400100d801000000500000000000070000000008000001800400000200300080000000000018000003000000c03e00c000001003a00300c805401204700a002001e006000001c00c0090000014000001001003c00c000000807400a0020040000006028000000c00e002007802400201700200000120050010000000015000001c000001003800000c0000018084006004000809c0000060008000002005005001401200000100000000020000008004003002005800a0000000000028002000801000c00f004800c07200300180040000000128000000003000000000400800180000220050010008000000000000400000c0010004006002004000000201800080c0008005008800800200300000000460060000054002003001803002e01b00000180540100000008000009001000003001e002001c004000007805c000000001802000802a007800001c016000000000000000580040040000008000004000000802003400200a8000018000000000800600100a80e8006017004001400a002000000c01202b001000c002006000000000000f006008801a000004800000e00e0008000000000000000c00000d00000000020b400000b801c00f005001000e003013800002a01c002800c006002000000000800000080bc002000000000800200100680a000a000004800405000000080240060010000000000000001001400000000000040120020070010008006001800002e000000001c000000005801400a00600e800801a004000000800e01a000802803a00e000800c02a00000280
  | 35 => 0xe00017443759234a19aa547de16a062509e6255296c3c71acc6b000000000cf24788c1011986b47229d6214622303ee80005540000379019a000000000000001391cae0a8823c93b28700951e64a202a509631e944a2000030595ca0000000000000049c17129101c7c3de8ca606d019038d08ea7648b1c5260c92100225c236873803393b08aa10fa5a025984671ac21dc01ac2808dda4c2024267fa01a4a81bfa526a2624bd0a0486ba146795a7f27e1258e14f82fc4c4221a05ba02040e8628a2505d008110aa543947c32280006649726964a4fa59c00005f780f603f212e7241ea0a0f04a4000009c3d51e1a02d995689d0f965b1814c4648e562648fd0000000037f878000028f041280000000f7e20d80001d1000098500009c7804aa2aa3c28dc80008cb85769b70c8c0000000000000002e800000000000d799ea4cf80002a6800000011ae0000000835800097b0000a4605e80000000536a744487054600000003008bb8a808d1c389867813112526ef891e89682fa607145647e800000021cc00010f8054951855f090471b89244d818324bf00003859e8a74795c200006680d680009059e342eda53c2628f924d9a5c6a791ddea748c147bf11cc40c946c133169e440a3562d4800049d1c4892d800016f808c6d1057c4be91bc2cd19329728f2c96f149c9779f746901b707609c208df24c889586002dc15f85a0800087497bc86c80001181f7ca8507848e5800000000009b117f86ea0000067a9be000108289a80003118376044215e07884f44fba2fa58ea7525698e3a0ae8e4898b91d200b0000000186e1c5015a3a7a7d000005cc0e5113e3eda4828c923980001924000000092900006f7000000000ee77e800059a9e8e9a88000a5780d062a879664129640002238000924c3819922000030a000000050b8b7200012147d89ec293e0b18000000003221ea0dc800000018907b9216c0219bb0000000050080006e8103c7b314ea00009a41998000816936e29c000091b01a659d820218b80c28b80a684641d9a000000000006a21a78000a1b80003e21b8473b94f269b941000003ca8b01df475d8fd4918198209888f86f19e4c8bd106c0000f36a0a80004f1800089f0daa5f61c6c597829223f980043a00007af204227f8978903133857b871e33f0ef00d21e9e465a3ae2781e2e1ae0c1c8bb96e610b860a8d699b62ee83da2059a88198889200020b29da208c2861c2c0000000649910055d0000000108805c104071983c6000000000000000000000576000009781b087e16460000000a79a8cc000042a00000000d1028e26d0c445000cec965227882409889890fc221307206e19d007db1bc0718a4e08c60000747162e5a61e3c000207c6a105ce11720a20000c765aa2a42943278484f00003f580840281fda007111e610
  | 36 => 0x80000000259e000256a0000cac8ac80000000000a93800061602200c08a8682a800000d21340fd997612420360001bb21b70fa4815280600006a4025201e00000000001178a5b8000000000000027bc418000000018e64aa866095a05265da97eca9221a03810792056128400000009fd02c000000008e2036e48100d28db800091787e20002a108b2196295e954e4261ab66b4a3642fc01ae1ec12287b39be84ea85f832500004879e466d48cbc17c10d601300000000e700000afa63f81ba5db833400000000000c3000015b600027e87d5a3be000167ea7280001798d9a54d86743d718d067e1378000000032717d0000200e8f2080a0000000000000088d16007941ab2000000035080003aa15928faa5b4000241e0000000a8780000000000000000020c80002a79b14000049c00020de00000006d500006f69a561fd9d88765a22e62d1e149e38c64432a17880007c43fc00003c196021a2855a1f9850c4b9000091418080000eb86b58000000000000014803b9a5b6000000000000007ef0000000066c4f000000000d1284c9d90000099a000000068980009e80000a54800057a00002d6000034e80009bf285c81c243405a952827388a8000000090513a058680009db221e5088000a4f8f6e912a91e00b80003ac000019a93044c39d8c00000ae00006120000d680000092210907c0001ba424a8fae255a24a00001d27c88b1e272884680e81ee974a5ea02c1f2c3d380003538000000294c936000000000004c900006cb115000016ae9f6170e4ba800000013f68b700007a007641099d085ca0ad20000d040000f8e7d1800000000000000bec20a9ab45850000a278d2c856817800023ca91f0b4a03e00002b400000000a409e300001dd275c000000005780004f9a24600018cc1209d0c2ff80000001fac00000002c191fe8e01fae000073e0000b5654900000000000000000076180004d400003b51418000113848f80004880bda2d4000021e8eee3d98e326bb8bb2000073038600000001fa00000c2e0000000000000000000001e780006e280003d1000099800000000eb26f4186649f237a0af0aae11f80004089d04338086a6ed974a00018ae231208a866a96259122287fe8b429e5000074c9af88c8a28871380005c788706cda1c61369874651a90428f057896a2a4a26f8d0c0aa800061223306349358756093867b017c8dd801e9fea038476176c0001a382eb181e2e5aa0e99790f44e30c1261382246b70f10557205878a96740001f5c5909b3c9759fb8780a7989702112249a3a6555208812a812048692ac000190600000000001abe86c11ce79a9ba62b59564535aa0861294383dd21545320b945af00be7e4800086f053a4be14a28e18a2a0002896142a1e434a081498f996a3ad9c8e54c99b22d78624235a73656108a
  | 37 => 0xac0f9010059497a606f1c80336145a00000000000000a118000000123a8fb1f9c46226e477480000b318e40c69f10566943e5bea8b641c24c4a028b4450e80002540000443a1242f228b430e17c21c1251e71915ea5751d7e493a5280000000a188358000000000000006b885828f513da000275400000006c9a40824d000019e80003731fe8210235e6a3a20c86aa01000000000611f2600024f28ea80008c5000022f80009a1159e76000003401c9a0000dd441689c89e20c009d2800064e8000340968c3db137c8091fd83b20f8097c27347ffa9667d000008d110ce94223ac05a00002e98e92313847c6ce0a0a49d800073d898298280002178bb418080000000fb0000216e53c00004e701ce4ce800000007ce0000fcc8b08c6a00000008e480000001c9435c800000026526c6102a0001bde4a6202e82629d017080000000ff6811097200020f023d95f06f60d48277a3200000e8c00000000000000a070000783800a00000000000000000000002c80000000000720800000009d608da0c2000000000000003bf144c0ab800000015ac7cf0280000091647c935606907a42888000000063a00024d696fa79e000164c0001d2c3f18cf0424a04e1b8124484395e658385ec9d000004c18000a3e13f401985f60000c56000299e83f22943d6000096c0000000000000000001e1a5149d900001d000005840e7200015d07901a320149cce0001d54712aa5e91387b216825a03e09558491815c31a054c4ef82e81b49edc95681e809b87429351b7a1f2008a1469490a7c00005450f306c013808c0000026d838608a169ca0c80004fc95b82bb08789a9112872b0c622dd212846f9f52024229000029aa0eb281469c1da450117489b6a40645004a835daa2650d85681c3a22665401c89ea85da54e925c3d8859e13c10801021d4e57da13e62e9f600b9107aa8c18e01dda9a81e8982612da338752057a5651c707e9000021120ce79d8422a7ea95c4f3a7a27b4165a9508876000277c0cc00006ca062624190d89a4130a5c224dc104a18c0000000513820c095a6102a583a800026f492b054a00002a4a1a81fe00008ce51d00dc642854824a1a5c60b288c68e8cb8000226452e911c94a92566e405e23570e66000109429ea522993854452a10447bca7cc250032c3890b225bb840e604189a3850a8e8148c0457d29a67a4113c41d948c396a8289a71eb435d00c022e2572077958a870952603a9534446a7c04018b38583238275f1a6423c24e281323f25f68000000195a3bc8d7a0001f12000253665a000000028d476d963800006961cc86300000000a5d0000000000000000003019598000000008c0000000000077c000037e00000e31dce992282472c000016200d892fa84a5e5238e000000000016664a180000000000a178bbe0b580003b
  | 38 => 0x3996a63cd25122161fe61bf11680001f0a58b07e400000008511e4e0838e4a82f223c3c0000000016247c81b1a5a48ae860d822a6da9cc43fb235c47a25202230ce636f19c2911109e26408e462619c06628b1600021be2c48000000000068b0b14a889376000000000013b4a6e0564a6d8f5e768936a0fc9fb220b12cc111a4285d0000000009802ad80008f01a9676100007f90d204591b12325a19400000005e2800063e00007c5874a00004c00000536394a93847207482da259c676242c0de800000013225b717866829690000180415486c06bb000000000000000c9e43000000f6206e980094e96c91ee0000de020ea8c25862258a68800000000005e01c8c13980640af9ddc25f9736a9700000002468000000000000008ab0f900000000000000034b800077103ae4bd93fe1c281f6a4c000000000004ea206c65f80000000000000245a00016169230000644800046a800094900008f88dc6000000080f142846c92080000cc42de85e08e914880cc889e314a5481280f70775041430904585d4a2de2fca8640001672291016c495230600000002e1000000000000f39b1e27006d40a58de22e38240302000064325ee0000ada0999e5e702055e46285ee00022064cb275095406c22b90cea4d094b04ec98a43919ca6789a8363dd80008720000000034c0850000000236200012249fb00007da843600013a600016626f29e1600012368e780002f180469dc9c1c9aa24424c000008b19ec46bd99b011b00006a3000000000003b48000000033672c8000165275a6908b608ee9cfe0ac800034d8000000000000024989b3800072f800097a1ca09c811e434782a8494178420c06a08ca96b47fc000033d115611a1a7837a95bca77a2e296200000529c8600011a62dda80c70f88c8502a1a814c025a0768000a2902f883880005d580002a9175e8a617a02f90ed86ed0ca8000000e92f1c3000022ce36888385c2800069b0dcaa61880200020f25eb19be17c8f2270680008d0890e0c507c670d11ba7d100001979f7243f98180000000242800053380008a491c60000bfa000000000023664cb99442ca9a48676800000001b84f41f7a6a68f0c000000001a04fa2971d5c73e9730045000000000003f9a12a1d587460ef93ec00028ee5c40a3414f093c1e6891200000e8a4b935a44b833e009a458127844c08b83f498712007ac9a1448f00002060106a08a48684b26ae000112446a176428a1bfe47d80006db983e6b527c277da95699315dc000129202a800000000000001d24415855c2c92a3a00013b8000193800025a40000b900001a7c000071800000003d325c87af81fc00003404cd80007ed00a29c9a4f02389fdc50218ce0499a9c438a68008b28680001e701fb2200a08000036320683ab8cf87041fee8978af0130817626c04
  | 39 => 0x25300000000000000041e5c1000000020ae4d212ec21709ea0b8034e8478e1a4cca6220001ef410e116e000198696090daa3a290e0fa0e127c1800033f95a47348c5aa48812ea1f8000a51a7e25bb1b7800007be7e981280001c1666b95764fc1e08000144478828d2237a83a57680003a087fe9c7085a90702d01c094a453fa56e69896a409c800000000007b7800000004429968c0c00000003dc900048581b60001ea88851dc0161818824e9bea11b919a25f0a8a8321b24a5c181457f27be42f003e38f8cc084e1dd8a7c8a0e4b2198e09d9974830126e1ea9b7286609f823b915a0e59cb61289266035100c250908436228607e004ee689157016da838883a90080186f854b9c0236187bc40428fe07d14e04b10ca20369464847058442993709c4a96a83e8b641581620121a0b8164962a1478ce2379a07856c29ee6c10eba31c26461941dec3069c4c0c302d89fb861e52d28da0910000635a0801f780000001d1a68a8bce29b1f965902a006e60f789f3903030f93883bb01e084614a079b0dee34aa7702db1606a5e9f5495600001539ad84589390000154618516f20ea9b620000dba4af8f528e6938e26306848649d2294586da496a1366af26183e51b803e1098e2879d6832b8050000200c7018e68a37217ca8a813ca87214a0a104d85f3a7a6244032e4108f326fc92581e3841007ca9205f484065d697aa19c1d447ca25d44219e9c81727dc59e1aae18c8ff233d978c0b08000108177019524b800000000000a0694f88ca0f99a544e1a76a00000002d180000001b4e76380007ba9ade848888838f052e6b100000b396c8000251aa63818e000000037400280000fde7b80ca039b254a00011608ec00007028f9a00000547c3a8ac9c0800000019b4000000000008940001a2e7988000a830a80a7b1ec83338f4000000006818000016800000011727f300004450946000228a42fa94e00000009bb130c1ca0122484852840d0000a1481e6658268e7971a12819212024506765a2000000026340000000071000000000325f980004b40000000000083a9f5a01d9dc6405a18a0001bf800029d4000013e90814e296a9ef06370000a0b8cc69ab28d671d800046d89667799d2e2262172320000021d000030886bc1790f9e3328000a7100000ed07d82faa9dc3649b9e000000000022227d98000000281800000000048b8c17f912696280001ea2130000000000000008158d5a70600000000f0a00000000000000000000000001e4183048e00003385e900005dd800000004183a800000000ecc64617ae00000000429068000209200015680000000000028200000000000000a8d81f05fe8318a66a4360000b3a3a1990e0d8922e9f68f862eb97c48de24109cc95d262f8f388f9131c6108c824e89d706309bcc0658ba881ea67a4
  | 40 => 0x5ca86b612e217640790a8a7186088798694a390b2651417004e48fb41e8036a3970c3aa732928171a1fc0000000186000000013bc6c2000000016327c3000022a8a1274d821e0000c4c107274e9f92692a428000000000000026a656a09faa010c8e00000000000adc3778c28000000000008669f127fc000272487400000000000000000067200000408c7889399ba0c8245235921da863a09c3c49f6e31d1b3e28c1e4434c80000000000196a34e70105a400000000a293c200002ec99000001ac00002350056653899c8e50ebe1fa196e2361856a849b8e0000000000075064b05323261b5c0001a8a8188000000000096e000000016860438000a8b2a6093f9f8899a80003e8800098ea0ba000002a0001ef8000230e0df806e47f23e647702120000060679252676700007928b0211a96225c723de80980009fa95482120db0a20a9e2000219c27126ee0001a1e0a1a4947118000000246400007080000c1800006d03150db436b1caa3b9157a4f2a35887811c0225821049098fc4b503120000dfc4d280006c189da9ba287c05d24aa7ee89a01db0aa09f98000000000089c879800000009790d6e5f580000001e586200000129800002980006501aa861722440000de87258ed05781dac0f4800018f25e2000080e00022a48738e28a1e21608a7000089da17a959126c44b15be54409f44ff026a6b1a49a3e980001cd10ae6d4126221403640648464105800078300001cf0000a7a829a0001626a5e23da2fd86920001f9e9ae29b465b20744a0a34002094fa41210b60d40b9aa810fc81b8991c799843a00012484681a086c5a5f800008a000000006be955200000000000ea29ba80005ae84c68a0998064d17347ce8d5482a0a1c4e080008eca4726ff000000029fe709a47a000233a00000007ea1846000000089f96f86f08d44a82893615c90501870bd632405f44f903b66d6800000018280a8117a000010c0002a189d192aea3794160bd062011c8f46289a1d68c6a4ca72706a67b6000000000007dfa67400003bc9d20a7c203180a18d80000df0aea9cb12e2a7014660ce800078c001438226500e2041a00024cc3fe83261f59faa1aa9afe0689718a22894483e0b4e7540c0e2c3177487e80000000e9c8d4985290c000021a2a208fa270c4f4a6c645211a45a5292a398992e6ae972c664271a74619a67d400000001b740001bd4000147200019540e093682f429ba9308c400001fc463b87d003c80004f60f60900a24000000005e0a15247593160000fe25ac0be810d00006239d4657192b644818501670f646c889a62b81f5e8d22316240877a953a1f087700000f40000930009839b80003391db2000000000028a08ed9ae466b1078782928c00002684f580000002400750854098f00007088d980bda2f864d87940a6262a0000
  | 41 => 0x6468f106f62138000625a6c09f79b5898821a22a11f8c7878b5c12c0deca11163e00428ae8bd849639a986c4198a089a7986a86e80008890000742895a6ea8000a6b950600000000000d10892000003b26bc01f805e0000000976944a135800062a0b0e48a9ff400019489830368640813410925fc59515e21b917cc00000000e009a8415000000000002d8937a3d29d6c000000084180003ca800085626cc0001146003133c7aba474312a32600000000e3a1566d8208600023bc7bd94c400007585e591301949b4c74580003c6271600014d89a08f3e735266c00015b42db9e5a00013de842024a9a61562a16284c3f01a587f580000c118600000ad800000000fe00009f4a08e4b280001c4800059216a27c7800036e000000000000002180537000045780004ed989200017329c522a60920f8aa6081543cf024c000023e5181afc928052a02901c251028f64a7979016e83b25b029765e203d40a70e9441d207216e026c8bf1d40587000091309702189c3208700001228e0000009d45330c6c2069e9200003525fa922c7b5a7f60b782fea0090ec645203200006c652992b49a19e9600010c41f6800016c043c7f280b89589d280000000348a81e0001e2807e96c271c800044184e24899f762bf2a2e00000007890ef600027d400000000000000991100200000006c80f504740000499272a665175000016aa000056252595c43a280000000000628a6d253f0000000052c3b5951e3da00003fd000034e000070a0d0a5b61fc800022500000964a22104e8a804740000a0c2938b9e0ec02003ba2102521a5e07cd809e5e7941c3c9a75ea2fa9ac77ba5347b287f85b38ec6000286c258800000023a0a240a140001dc201c80cc1b203ba94e90d2183a2d80002174000265885a80003b8a54c2908b1a2bd890c4130eea8fd21d83882066000000000024f45a2800083d800031f8000503a02800000003fe00007e400009ac93140000000981a6fa61880005a58c882ac00000000000000279267e80000001f688a6800036280003638e4c0ac0fa007307ee4d89722555970c32a80f449a000000011946219ace9ad8208450853883400002fe165c63c07b40000710a569f300000000000243a00028741df105835400000001b9a39d1daa715203e1b995c8000000077f00005d600009c60488405226c0000000426800016c94067d299707a1a18295e277a6b21d3c1dba6d80001a3e000152a5069de26168fbe18d02ac14129d644200009b7a41a00000005c0823a0c4000000000004280000000148e0000e9674428fa00000000000000031916c7be877891ba8e680b100e63a247800003ea1aba0d290f092000000001c8868e00003b80b4812a9dd8ea46dd883c504a1ac23d00004f892307342418337000056096640000ccc9a58a7292405b4
  | 42 => 0x257611015006c31e9a9c3a9bc000136c7ac08fa4f7080047297c051ea64200008e89770fa828b1e7a0000d520000edc1840000000063e113a9c22bd1a022e01806000215c7b193545d9887c61f000067a091a3c59b4a000270889a1b1059396f082b05ae050288e1a40000000083e093800067304ea468828c000000000004480000000000000076c000000000003c1027a7000abe00008600000000912000077e000056400005618ad468a27b640a147000008b48b5000022880000001a0e3901e380001c12a14000050f2a1a35f9ec0471071c00012801d78cc80001760126872a61c848c186a2bc94080000fba84800000000000cda53a09dc5e385a800000000bc00009a80000703000018b0812000000056800007158000000000000005580002466000020692a179ca108000000252e0000500000200a46388549e59f8253d287278403c04f322f20000004000000000004e0923a0e469399e000015229958c32a76a27a42326f82789aa28061c6a55ca6aa575a216a96839a9fe1a1ca649e2c1f280003faa83e4a594940d08d3429d0cd466821c00000baa567151c753145e548266456884e84b696b27b6a19e8298000000101850a80001da04d267100004a280008c7a756000000001e954c9f808521379278992839ca28800066a91869820f9c5e890d06df0a52000067c2c290a20001aa60e6255e0002730739962880c1ab8000207656b89185249a82252864c7f500005df16cc0c587d21d31b9c72e1e360001a204560d8085fa0a001f0000a7f030e49780006980d08470a2662760ba40ff22d24d49a5a4148020a2c0e2c4318a5e1811f00a66000080a955e3ff08089a21f940861a668ac09b23d218b63528cee6e5854200000004cc00000000000724800000000000001ae023800009ff897a00006ea27400001b5896e0a21df2a658000a6284d017f2676074242a000000000000001e300008ab9d2636800002ac94c652d80009d9800000007d4000000000000001bd0e1c06a81161699ca22a515ba629a0b0a5fa2ca00002ee68d8c7243c00007ed9ea29b580007d90000000107258483fe8a016b8741913443b8000a459596000015600010b22981c9e00000000001b323c680005791036166171a0000000000163400000005c50000000049200000000001d669d80d7879226fe9582a288360000000003690880000001a4c00028f28ad044a00012b80000952a8c8000918800065e08bc4c80000096000038300000001a500db0dc400006d800000004f200004a89e7c3c80a46904800020415409ec0000738099e000000091c07e041780006578dd87f000009ee101a5ada36c38d835600023325b2a61245f9b4650500003f8129400024e8000000065e917000000006c280000000b9c3b39d6e2940aaa7039d646081eee000
  | 43 => 0x60a6e00014ee257000000000008e100002fb80002a205de0d524ee3981db81d512a600000005150a363f6805c000201450c259a0001c780001290000000000000004928b0067d9d7455994c0a2709ec16b150a1f700aca068000000151616a9e3e000169a666a65402228d000020e686d0d5e0bc95ec00016ea098013a7dc01d6a6815086cc262c374824652a9e069640f1e55b8d405b89a348a3a476a7d03c84a6a37095587f44f8070c165a40a023a040837299c9c42236a63276e94298caa320bfc45a97b28140bc40a40b542b211ac44498f615a91f059b8a9299f11b03eaaa409688b928dfa97c739034694e151a60a80000000d7010b000013c8a2000014480001d982ec103e3419b6c9e40b8800000006e50c2c0000b6a7318000a0d00003a01fde0e2800000025cc98c120a9698df2000000000002523e6000023b1cdc2c2027ea64253088488644b1a1102f824d008c800022416d6237174205420d48f625f413f174c656282635821c43ff9c382f497e03bd04ae9200000a2f03a048417720e41ff811488a61959d56a4e9b5e83110ba17012ee3608048869a8ba04629f60858cbe000081e6d99cc09519ada54116d400000009fc144660484ba04c09a2627031e2891fbe60d03062d680000b51c5200024de63100000001ea400026789099af098a00001b122208c28000334966859414528aa9ccc79d23366a5000000021001bb080600000000000a64677a85600010cc0000e9a00000000608eb4645982400000008a106de00000001771920717000045294be337a57437086cca6902a600017fe2858958a36000098c800000014d01818000000287a00000001028000457000005c95fa0000766321800000000003cb880400000000000d5800017be8d3187e3878000961a3fa274a5fa06c9f0400015780000e4e00009f290b80000001bb831729264e283a200021b69548fe479b91d41a1800039ea5962c4020a000214c0000d6ca491cf232d28b28fb9eb858d999c93f1c420000000000000049a80000000ef86f900000000000000000033e8322a1d800000021865f280001010a5410c83de317843e36d83c228e8e78000253259b00009278d308d18e42000072e7f40e6471d02c68bb13980b726621fa86ce9b4102e3b6a49247e23b840718da8bf85706321bd69a529e080111de16289e49e6a4e61150d967102164372025c516004264a91e063eaa38833283073b27228d51bf637e965812d232c5bda04800029545820f089df89009d09a7277a1bbc3691c7a7ba106a25a88d0000193014d24da606a09486e29ce20708245df879008980001a200000000000000000000013f800000004830000191135e223800000005664660d9e6888a2e971000070ea77822c27c6987856e000000093180ca00000967221dd04c08000000052
  | 44 => 0x34661236020a17e80001bc4681000092d0826a151fe228e094800000004b015b200000000000480859a6c81d39cda838210a66a193e2f6000072ea06a8509d5291a80000598f6a248a2700000c66781193c6b40000000174600022b67162602a4208f297992186688be225810eaa5081caa960378880800021c94b200000000000000000064e0001bce00011da9d617e42348000849a1628e4075c87c80003a980000000000000000061c0000961240445f20c6a6c80000e9002245d80009b0a6049ae8a9c3bf800000000000629e1c694a8b800021ec2cc9344983997214523b4711012c99b97680c914ca41f9f082de1f8a88200005ff13ea000000051b800000006f08dd1e9864018c02f9800084e93ac3cea24c3498cb22f0887e73298b86679af440107c03a40820a471b429bc96be32e9eba87a17c65fc291061117dc000102477a93d400024b23a104760001a1a000223a0f31dbe00028a6a4f00004aa269a0000e228ca026423f03660a5273e5fca0ee0000b2c00017b416314ec1721da04a7265c98da9e85ed9c7e6058af24488d9c95c034a144843006002b448c9d7a369879c98e16de922aa244b80e5048896e822080006e48000467a7ba44c800060e8000000000078c8000955177a43815806598000672a8c45e48000a3388c09742972000000001c131e1cb18e25bf9b7e00000005b10fc4556a7b411e000092703001c91fea4e5814ea38899681f956c03599d626e105c90f8d5621b800058c142600000004eba8a805f800000007621eb973e11788a477280000868698000000000000008f5800072f2a4c00004f661d8b827f38e5400000000001174a0017ba14406480000ce81d6972e00000009471ed278600007ce1a7a26194f834f09840000000000000000017a8000236a32100004d3a01c3be8e02208800073a800050800000001aa00000000a4b19dc0001e128641f346530aba00025107379dba0000000697896820d0b2e00000003770e380001be659f1ab00d7180e140a84e4b58508000000093389aa80d00008ae09bc87f8b3057f9f4e2b08000000000000016f400000000000cd063a8000411800046e00000001d1400006728e30b041aa11828059432000000064a15c0000000049007a688c8000000209a00019a49ac26e643da302000132aa6500005ce8000000000022e99e600000000000000a04000000000000001e0000013123099fc20001ae6345a93412f9d940001aac42e19d03b280000001e3a9b880000a78c3600000003701d3e00010d402f20fe0001e540000ab80000a100000000a26042851080001ce8c3c34603e20001af2000062200012d267481860dd000003c21eea540000a8d00001c6823474e82ca83b0d6a563000000000003b09a4aa5a0000001800012f05ea0f5911000006e87c691ea68
  | 45 => 0xf206fe000000000018c6000000000021160139c3c943920640e03ec2a98000408110c1fc00008f398826f21bee54b1fb00001f020c22a447a203fa4dca3c61338000051273c4dfa2c438a82e260e09ac59280406d590e40000a320001d6029980009501a6806f850e0001c8483d069a37d9462636112a43c80007a080007e898543d092e67b9991e47d0000000247e0310000a1680000519be2000000097086ee0000bc000000004ae9b8800015de00004846911f1c55f80008ea08ac00013e879c851627a0000302892e6e3000068c2506000033c79f8664000268a44da5d800000008a581987bb1802627950231f00580000f24132893e8a7984c32c000057c8ade4ba01dc3b1204600029148c30bca00001d80000000802000004e01a800000006a400789f2800000000009e2a81205800002b398f4147290ca9180307fd8b2851aa6d400001c601d173821b18783af00008cd209600014d443723fc93aa4ae9d30c2a7cc8e0a8ae9b403180f2896b24e45d8982282792fe717a0823d6a906270800076f00003c505d25ab293255800000000000000258000004982cf16e08da01047d31a92000006c35890ac00000001c99fec59ea05e8fc00008b3239c326994aa31a1a465707608328ca41558c2004da9027529b8259597200000000000000000000000000000000278000000004601d120000b860001bf0a100d7c000000053d8b4ca62252c73c04fe0000cd68f3049405080002f78f0e00000000001b3a000000000000e4665a14000000009998000000000000000007769d9e18e1988000000000000001ed8d3e9cb80005fb97e21550000000000027f18b056200001110000683000039d800031b852269f98ac91705d852124baa0380000001eac000000000000006b280000001d389bd8000418a77400000008008000000000007a800000029f84d180e000015306ee96e479e23107e18e88006135c32d80001eb00000001f24000000049ca4b03fb963c7388640544a8ca25d932816f1c988828e8e166800000000003b0231c8f494d29039f98808972469d25ba4b390c82579fd22a300007cf800000000000b6800070b87ba0000aca4099884000197c7b88bd47ff00005f50fdc00000000000e7e2df81f85278000598068200000004c99cf43f3934c6c3899445480000000000000000051e0fca116a43201880002b88aa823088b22a61e8409401484c6150c6eb0a3e00000007a9939e25b0642397a28c775939a00005fa2e8800006303601ac93faa529da8a5209980000008000058e07500000000a7e226a4f651da38a9511012000282c0001bae0001bf452b89ae02680002ef01ec000000000019c600000fe2a89154642019c7bfa9402fd000000006ac9f58a1a9d89d2a6a90000242210c8c20000707a2e86030a7800000000001b
  | 46 => 0x9e712b2685819487d83e00000a620001f14550808023312a41490c50a95800000000002e825185bf19e2a6c270666e00000b20dcea72147e0001f42a24906e0000000a3806f242900008128e443598e2e54f1d3444e8eaa79827ac3d5888a00694b8295891c442a8fc6cbaa3c97c9c145b4084a2e604ec9bc25ae8af9cf817121d4582a0e82ad0aee1da800000003dc67c12d819729602921d30192a170437aa52887006a9ea0a827b525f654e056c2968c4891182c400008862398000000000075c87b80000fac000257e0000000a6110900000384479800039f000019b8a6a2af261a1cda2f0a21931a915800079a24243450b360000000666230402d000011e82704bc8e3062c9c6863b1a76316000000013845c1a2607291fe076d14de3610d9400009f69e911042b1215000009ba02a257c5d5057e03994c200010087e6974e5b6958e00025042a4000018aa5cea3a877203881123c0aa3e0000fd284694ac8909d2066f1cfc4258fbc48e22520000e0e0ae273a628226e13e000009f0000000221000021ca1afaa06a30235004900008d287c237c298015d0f8c8fe0000730804436c81084dd24a227c11ec9ad294473611848f7003824c1dc86da1c5a77f88569ce09327909f581be8000453995275aa148a76040c000000089522d69c000004b780000888000878a91a6ba127a3fa071644600004ac00002318e98a021b2a2f700004809340573998c3ee069c86100004cd03f000002782bf91160000000957114400023fe0000d24000295831e80004a3942c0001fc64631a001b297f66f4a2e4384046299a092c1a000004531cd68b4109c5f222866228000000000000000000000000000136400000000001cb400000000001ff22e28c3400003287a304b2000078a0000000a2692dca210acc1e09d5a73a143415422a2000000016400000001da600000004ee973c3ec8f7c36f80005a387fa2d2003c1758470307954a0dc2312a4d95aa343940c8b6867e43f0a4a4bc000099f94bc70900000000af8000068c82d90c200014e67791e526ba94e470a8ac60e799f4000161e7409f1875e0000280233e5c5902c00018641c00fd800020a40000aac5209ba22d984d484128f454f8a76522a7ae8f8268c49f811c8180024227222c8e88c425a104020c704dc296061660c220461ea62677801320b98a4c00580001fca78261799f20ad8ede788800000021f4000139400028ec1960e58364188842c18680f107fc762839208e011a70da2e651726e0000000057318f29
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8be87d46640400117b0fa8cc808002a7a0f51990100054ec1ea33202000aae82d46640400155b05a8cc80801e2fa1f21990100045ec3e433202000a3e85c86640400147b0b90cc808002a7a0f21990100054ec1e433202000e2d52886640400147d0a10cc8080028f614219901000716a904332020038be87d51640400187eebaa2c80800e2f21d54590100046fc1ae4b20200e8dc835c964040011e902b92c80800e2fa1e42590100051f42c84b202000a3d8590964040071790ea12c808002ad20542590100051f42884b202000a3d85109640400153d06212c808002a760c42590100061fbaceab202000ab4815cd640400193ae639ac80800387d4e53590100051f42ce4b202000a3d859c9640400153f06b92c808002a720d72590100055bc0ae4b202000ab4815c9640400147d0a392c8080028f61472590100054f418e4b202000a9d831c9640419fc6e21a92c80833f8d44352590106851ec2ca4b202000e2f52949640400156f02a92c808002ad205525901000717c12a4b202000e37815496404001c6902a92c8083438bc81525901068716902a4b2020d0e371054964041a1c6a20a92c80833e8fa1452590100051f42c64b202000a3d858c9640400117f0e992c8080022f21d32590100055bc0a64b202000ab4814c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400147d0b38ac8080028f61671590100045f43ea2b2020008bd87d45640400153d07a8ac808002a760f515901000557416a2b202000aad82d456404001c6ea328ac8080022fa1f21590100045ec3e42b202000a3e85c85640400147b0b90ac808002a7a0f21590100054ec1e42b202000e2d52885640400147d0a10ac8080028f614215901000716a9042b202003aba8008564040015730010ac8080022fe117298c1003c5e422e53182000ad4814ca63040071b90ea9ac6080022fe117258c1003c5e422e4b1820218f7815c963040011e902b92c60800e3721d3258c1001c5fc3ac921820478f7815d943040071790eb22860803aa720d6450c1023e5b326e2a182000cb564dc543040011eb0c38a86081132d9907150c100065ab20e2a18200287e85dda41040010fb0bbb482080032e591709041001c5e426eca082067c9e64dcd410400193ac9b9a82081132799073504100064eb20e6a082000cd6611cd410400717b08bb0820801f2e99170104100143f42eed188200087d85dda31040071bf0eb1c620800f369c1638c4100045f43cc898820078bc87991310400117d0eb2262080022f21d644c4100063c3aeec8802000ce872dd9100400197709bb220080032e21376440100063da96ec8802000c7952dd910040018f6edbaa20080032eddb74440100065dbb0e88802000cdb76dcd10040019b6ec39a20080033addb7244010
  | 1 => 0x8e831a62880032bdd3624c510006563a6c498a2000e6462d9431440012eb0bba062881123d219740c5102255b436c818a2000ea462d903144001c6eca32062880038d194640c51000752310c818a2044cb687190314408996b0e3206288113a5e0c640c5102274a418c818a2047cb6731903144001d2ca63206288003a554c640c5100071ba90c818a2000e35521903144001d2e643206288003a54c8640c5106974b180c818a20d2e94301903144001d28c93986288263b118a730c5101fde9404e618a20038f587d8c3144001caecbb18628800395197630c5100074bb26c618a2000e9464d8c3144001d88c5b1862880feb561f630c5102a66ac3ec618a2044ad684d8c3144001caea5b1862880039554b630c5100047bc3ac618a2044ab48458c314403d5c904b186288002b5a18630c5100066b3b0c618a2000e946418c3144001d88c43186288112b521b430c5102274a3268618a20a3ec462d0c31440013ab0e2186288002b5a18430c5102274a3208618a20a0ec46210c314403d5cd0db106288003a9193620c51000763b1ec418a2007cb4649c7404409f36f0ea0e808800ead21941d0110005ca41a83a02200087f855d940440050f90abb2808800237e0d76501100746e41aeca0220008ef825d940440031d904bb280880021fa1b755011042e1e326eaa022000c6c62dd540441a30fd0fb2a80882161f21f65501100061fbaec8a022000c3c75d9140440018beebb1a8088003171d763501100062fba8c6a022000c5c7518d40440018deebb1280880031b1d762501100066a31ee2a022000ce462dc5404400196ec838a80880033518c715011000672310e2a0220039b48750540440075690ca0a8088002e520d415011001dd840282a02200ecd4639c730440010ff0abb2608800a1f215764c1100045fc22ec98220078bc845d930440011df04bb260880063b209764c1100143e428ec982200ecd8301d930440010fd0dbaa60880031b18b754c1100043f43eca982200087c87d95304400187eebb2260880030f1d7644c1100061fba8c89822000c3c7519130440018beebb1a6088003171d7634c1100062fba8c69822000c5c7518d30440018deebb1260880031b1d7624c1100065a326e29822000ce462dc53044001968c838a608800335d8c714c11000672310e29822056c7a76d97104409f974edb26208801f2e9d864c41102a66d3b6c7882200ecda7618f10440a79d4edb162088002f420d41c41100070fa9ca732020d0a3d8594a6404001c5ea5294c8080038be09529901068717902a532020d0e2d2054a640419f47d0a294c8080028fa1632990100051ec2c6532020008bf874ca640400f1790e994c808002ade0532990100055a40a6532020078be870ca640400117b0e194c8080028fa1432990100051ec28653202007
  | 2 => 0x475d89100053742ce9b122000a6d859d3624400159d073a6c488002b360e74d891000537c2ae9b122000a6c855d362440955cd023a6c48814eb960474d891000717aa4a9b122000aae84dcf624400155b09b9ec488106b9a0773d891029d72c0ee7b122000a6e859cf62440014db0b39ec488002aba1273d891000556c24e7b122000a6f855cf62440014d90ab9ec48800393d4e53d891000573c0a87b122000ae48150f62440a71dd0fa8ec4880023b61f51d891000557426a3b122000aad84d47624400159d07a8ec488002b360f51d891000637baee1b122037ae681dc362440019c8c53b4828801eada1b64905100065b3b6c920a2000e37651924144001c68ca3248288003a9188649051023e5a324e720a2000e9464d8e41440019acec31c8288003a5190639051000762310c720a2000ab68690e4144001d48c9b14828813f2e1c364505101fc6f436e6a0a2000c5f65dcd41440018b8cbb9a828800327d93735051033e4e326e6a0a2000ccc62dcd41440a91bd0c39a828800317d9473505100062e328e6a0a2000c9f641cd4144089938c839a82880033318873505102246f43ec6a0a20548dc87d8d41440cf1bd0e31a828803a3721c635051000667b9ec4a0a2000ccc73d8941440ad8e8edb2a828801f2d1db745051027e5a3b6c8a0a2007cb4761914144001c6eca3228288003a9188645051033e6a3b6e6a0a2044cd4761cd4144001b2ee839a828815275a187350510006abb28e6a0a2000d54651cd4144001b2ec839a82881133599073505102266a320e6a0a2000d94641cd4144001b88c439a828800355d487350510006aaa90e6a0a20009d687d8d41440a99a8edb1a82880fe7521c63505101fe6a3b0c6a0a2000e946418d4144001d88c431a828814f391db6250510006e239ec4a0a2000dd073dc1414409fb66e8382828800374dcc705051003d5a4328220a2000e3765504414400172906a088288003a518d41105105af523128220a2056c7676d973144001cc8c5b2e628800e3da1b74cc51001cf9406e998a2047cb4645d3314409f96cedb266288003a918b64cc5102ae5b3b0c998a2000e37651933144001c68ca3266288003a918864cc51023e5b438c998a2047cb5871933144001c6ea432662880038d54864cc5100072bb2ec798a2000ec462d8f314408f56908b1e6288086b920963cc5101fe6b3b0c798a2000e946418f3144001d88c431e6288086b9a1b62cc51029e733b6c598a2000ea464d8b31440ab17d0dba262880030fd97744c5100061e32ee898a2000cac62dd1314409f17d0c3a262880030fd94744c5100061e328e898a2000cac621d1314400117d0fb22628813e2f21f644c5100045f438c898a20078bc87191314400193ee9b1a6288003271d3634c5102a66c386c698a2000c9f7418d314400193
  | 3 => 0x31a2000e4d52c806344001c9aa4900c688002b5e052018d100056a40a4031a2000a5f8544063440014b90a880c688002a7e111018d100054e4222031a200087f855db43440050f90abb6868803a2f21176d0d1000477c12eda1a20018ec825db434400f968c938e868800335d8e71d0d1000672314e3a1a20038f4865c7434400f968c8b8e86880033918971d0d100043fc2aed21a200287c855da434401d1b906bb486880023be097690d1000c76412ed21a200287e85dd943440010fb0bbb286880063ba0b7650d1000476c16eca1a200087f855d943440050f90abb286880023be097650d1000c76412eca1a20008f7815d943440891e9023b2868803a2fa1f6450d1003c6f43ec6a1a20038f686dc543440018eecbb8a86880031d1977150d1023e5a326e2a1a2000cd463dc543440019c8c5b8a86880031dd947150d100063a328e2a1a2000cb7641c54344089968c838a868800335d8c7150d100066a318e2a1a2000ce4621c543440010ff0abb0868800a1f2157610d1000477c12ec21a20018ec825d8434400f968c9388868803b3518e7110d1001c7a432e221a2000a6e86dd762440018dcedbaec488003591c775d891000537430ebb122000c6e761d762440018dcedb2ec4880023b61e65d89100053742ccbb122000aae84997624400155b0932ec488002b3a0e65d891000566c1ccbb1220008ef87597624400155f08b2ec488002ab21165d891000567c1acbb122000acc8359762440014dd0c32ec4880031b9d865d891000732c08cbb122000cae76d936244001c5ecbb26c4880038b19764d891000717baec9b122000e2c75d9362440011db0f326c4880029ba1664d891000536c2cc9b122000aae84993624400159d07326c488002b360e64d891000477c3ac9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000aae86193624400195cec326c4880038bd9464d891000716328c9b122000e2f751936244001c58ea326c488003a960464d8910006673b6c7b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000e4f75d8f6244001c98ebb1ec488003b160763d891000476c3cc7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000ace8398f62440011df0eb1ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec488002b3a1863d8910006673b0c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4f7518f6244001c98ea31ec4880039919651d891029d72432a3b122000c6e71dd762440018d8e3baec4880031b5c375d89100053742cebb122000c6d751d762441a75cd023aec48814eb960475d891000537438ebb122000c6e871d76244001ccd023aec4880039960
  | 4 => 0x3440014bb0b190c688002a7e113218d100054e4226431a2000ad7814c863440018bcedb28c6880029760b6518d100046ec3cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440018bcec328c688002976086518d100072ac08ca31a2000c9e76d906344001c3ecbb20c688003871976418d100046ec3cc831a2000a5e8599063440014bb0b320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc82590634400193cec320c68800387d946418d100070e328c831a2000e958119063441a5d2ee2320c68834ba58406418d106974a080c831a20008dd8798863440014bd0b310c688002976166218d100054f424c431a2000a9d8498863440011bf0eb10c68800297e156218d100052e42ac431a2000a9f84588634400153908b10c68800297a146218d100052ec28c431a2000e4f651886344001c98ca310c688003a3d906218d1000746320c431a2000e4e851886344001c9b0a310c688003b16046218d106a763b88c431a20d4ec61018863441a9d8820310c68800297a1b5218d100052e436a431a2000c5e76d486344001c3ec9a90c688003871935218d1000727b16a431a2000e4c62d4863440014bd0ca90c688002972195218d100062f3b2a431a2000e1f645486344001c38c8a90c68800393d895218d1000726312a431a2000e54659446344001d28c9288c688003b118a5118d101fd6a432a231a2000e94645446344001d88c4a88c688002b5a1a2118d100074a3244231a2000ec4628846344001e8aa5108c6880feb52192118d100074a3224231a2000ec462484634401d8beeb3a8c688002b5e057418d100056b40ea831a2000ad581d506344001c3ea92a0c68800297a167218d100052ec2ce431a2000a9f845c8634400153908b90c688002b5e057218d100056a40ae431a2000ad681d4863440015ab03a90c68800395a075218d100072ac0ea431a2000a5d859486344001c9ea5290c68800393e095218d100052f428a431a2000ad681d0863440015ab03a10c68800297a164218d100052ec2c8431a2000ad68190863440015ab03210c68803a37a1c4218d100046ec388431a2000a5e8510863440014bb0a210c688002a7e117118d100054e422e231a200e8de87d4463440011bb0fa88c688002a7a135118d100054ec26a231a2000ace82d44634400159b05a88c68803a37a1f2118d100046ec3e4231a2000a5e85c8463440014bb0b908c688002a7a132118d100054ec264231a2000e4d5288463440014bd0a108c688002976142118d1000726a904231a2000a5f855c063440014b90ab80c68800297a172018d100052ec2e4
  | 5 => 0x80029761421d8d1000726a9043b1a2000a5e85dc363440014bb0bb86c68800297a1720d8d100052ec2e41b1a2000e4d52c836344001c9aa4906c68803b1718d7598d1000637396cb31a2000c6e72196634400187ecb3a4c6880030f1967498d100764e31ce931a2000c3f655d26344001878caba4c68803b2718d7498d100061f3aec931a2000c3d75d92634400195ce5b24c6880030f9d46498d100061eba8c931a2000cae7219263440018bcebb1cc688003175d76398d100064f3a6c731a2000c9d74d8e634400199ce5b1cc6880031bd957298d100063632ae531a2000caf645ca6344001958c8b94c68800333d8d7298d100766631ae531a2000c6e7518a63440018daea314c6880032b9d06298d1000656ba0c531a200087f825d663440018dd0ab94c6880031b6157298d100143fc3ea531a200087d87d4a63441ad87ce9a94c6880030f5d35298d1000e37396a531a2000c6d72d4a63440010ff0ea94c6880021f61d5298d106ae1f3a2a531a2000c3d7454a63440038dce4a94c6880031b5c95298d100143f436eab1a200087e87d9563440018d8e5b2ac6880021fa1c6558d1000636390cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a20018ee86dc963440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc963440018deea312c6880031b1d46258d1000657ba0c4b1a2000cac7418963440010fb05baac6880022fe117558d1003c5e422eab1a20008df835d563440011df04baac6880063b2097558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f85dc963440018d90bb92c6880021fe157258d100143e42ae4b1a20008bf845c9634400f17908b92c68800237e0d7258d100047bc0ae4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440010fd0fa92c68800a1f21f5258d100061fba6a4b1a20d6c3c74d4963440018dee5a92c6880071b1cb5258d100043f43aa4b1a200087c87549634400187ee8a92c6883570f1d15258d1000637b92a4b1a2001c6c725496344001968e9b8ac688003391cb7158d100046fc3ac631a2000a5f8558c63440014b90ab18c688002a7e116318d100054e422c631a2000acf8258c634400159904b18c68803a3720d7518d100762fbaea631a20008bf845c8634400f17908b90c68803a3720d7218d100f47a40ae431a2000a5e858c86
  | 6 => 0x716a90423222000a3e85c80644400147b0b900c8880038b54b201911000716a92403222000ab781480644400156902900c8880028fe1510191100051e42a2032220d8c757119763441af9cae2316c68800e3d60775d8d100062ebaea7b1a2000ad581d4f63440058b8eb29ec68800a37e1d53d8d1003c5f426e5b1a20008bd84dcb63440071eb03b96c68833f1d5c752d8d106863ab8aa5b1a2000a5e858cb63440014bb0b196c68800637e1d32d8d100054fc2265b1a2000a9c844cb63440015af02996c68800297a1432d8d100052ec2865b1a2000a9e840cb634400153b08196c6880029760b65d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052ec10cbb1a2000e55811976344001c3ecbb26c6880038719764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c651936344001d2b02326c68800297a1662d8d100052ec2cc5b1a2000a9e8498b634400153b09316c68800297e1562d8d100052e42ac5b1a2000a9f8458b634400153908b16c68800297a1462d8d100052ec28c5b1a2000e4f6518b6344001c98ca316c688003a3d9062d8d1000746320c5b1a2000e4e8518b6344001c9b0a316c688003b160462d8d100052f436a5b1a2000a5c86d4b6344001c3ec9a96c6880038719352d8d1000727b16a5b1a2000e4c62d4b63440014bd0ca96c6880029721952d8d100070fb22a5b1a2000e1c6454b6344001c9ec4a96c6880039318952d8d100072bb2ae3b1a2000e54655c76344001d2ec8b8ec688003a519171d8d1000762312e3b1a2000e546594763440a95a90ca8ec688003b118a21d8d10007a2a9443b1a2054ad4864876344001d88c490ec688002b5a0775d8d102a56ac0eebb1a2000c5d751d763440015ad023aec688152b560475d8d102a56ac0ee9b1a2054ad5811d36344001c3ea92a6c688002a7a1372d8d100054ec26e5b1a2000ad681dcb63440a95ab03b96c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c68800297a1472d8d100052ec28e5b1a2000ad6811cb63440a95ab02396c68800393d4a52d8d1000727c12a5b1a2000a5e8590b63440014bb0b216c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c68800395d4971d8d100072aa92e3b1a20548de87d4763440011bb0fa8ec688002a7a1351d8d100054ec26a3b1a2000ace82d47634400159b05a8ec68815237a1f21d8d100046ec3e43b1a2000a5e85c8763440014bb0b90ec688002a7a1321d8d100054ec2643b1a2000e4d5288763440014bd0a10ec68
  | 7 => 0xcf73dc96444001998e7b92c8880031be1772591100063642ee4b22200087f855c964440050f90ab92c8880022fe1172591100046fc1ae4b22200e8dc835c964440011ef02b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100043f43ea4b22200287c87d4964440018bee7a92c888003171cf525911000637b96a4b222001c6c72d4964440010fd0ea92c8880021f21d52591100062fb9aa4b222000c5c7354964440018dee4a92c8880071b1c952591100066a39ee2b222000ce472dc564441b18eae2328c8880022fe1d64191100051fc2ac83222000a3c85590644400153f06b20c888002a720d641911000557c12c83222000aac8259064441af9cae2310c8880030f9db65191100051ec16ca32220008bd87994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c8880030f9d865191100051ec10ca3222000e3581194644400117b0f310c8880028fa1662191100051ec2cc43222000a9e83988644400153b07310c8880022fe1d62191100051fc2ac43222000a3c85588644400153f06b10c888002a720d62191100051f428c43222000a3d851886444001c5eca310c8880038b194621911000717428c43222000e2d851886444001d4b02310c888367a984062191106cf52080c43222000a3e86d4864440014790da90c8880030f9db521911000717b16a43222000e2c62d48644400147d0ca90c8880028f21952191100061f3b2a43222000e2f625486444001c58c4a90c8880038dd9571191100071a32ae23222000b94835c46444001d48c4b88c8880038d196511911000752314a23222055ab4865446444001d48c4a88c888002ada1a211911000752314423222000f255288464440ab5690c908c888003a918921191100055b40ea63222000ab581d4c6444001c3ea7298c888002ade0553191100055a40aa63222000ab681d48644400156b03a90c8880038da0752191100071ac0ea432220d6e3671d4864441adc6ae3a90c8883568f616521911000717a94a43222000e2f8254864441abc6ce2a90c8883578d5c552191106b51f428a43222000a3e858c8644400147b0b190c888002ada0632191100055ac0c6432220008bf874c8644400f1790e990c888002ade0532191100055a40a6432220078be870c8644400117b0e190c8880028fa1432191100051ec286432220078be87d44644400117b0fa88c888002a7a0f51191100054ec1ea23222000aae82d44644400155b05a88c88801e2fa1f21191100045ec3e423222000a3e85c84644400147b0b908c888002a7a0f21191100054ec1e423222000e2d52884644400147d0a108c8880028f61421191100
  | 8 => 0x732ec888002a760e65d911000557414cbb222000aad82997644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147b0432ec8880038d60465d91100051f42cc5b222000a3d8598b644400153d07316c888002a760e62d91100051fc2ac5b222000a3c8558b644400153f06b16c888002a720d62d91100051f428c5b222000a3d8518b6444001c5eca316c8880038b19462d911000717428c5b222000e2d8518b6444001d4b02316c8880028fa1b52d91100051e436a5b222000e2f62d4b6444001c58c5a96c8880028fa1952d91100051e432a5b222000e2f6254b6444001c58c4a96c8880038d19651d911027d5a432a3b222000ea4628876444001e4aa510ec88813ead21921d91100075231243b222000c3d751d7644400156d023aec88813ead60475d911027d5ac0ee7b222000e1f5394f644400147d0b396c8880028f61672d91100054f41ce5b222000a9d839cb644400147d0a396c8880028f61472d91100055b408e5b22204fab5811cb6444001c5ea5296c8880038be0952d91100051f42c65b222000a3d858cb644400117f0e996c8880022f21d32d91100055bc0a65b222000ab4814cb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644409f17d0fa8ec8880022f61f51d91100054f41ea3b222000a9d83d47644400155d05a8ec888002ab60b51d911027c5f43e43b2220008bd87c87644400147d0b90ec8880028f61721d91100054f41e43b222000a9d83c876444001c5aa510ec8880028fa1421d91100051ec2843b222000e2d52087644400147d0bb86c8880028f61770d91100051f42e41b222000a3d85c836444001c5aa5906c8880038b54920d911003e1e322eb3222000c6e72d9664440018dce432cc8880030f9d764991100061ebaec93222000cae72d9264440018becb39cc8880031719673991100064fb24e73222007c9c649ce64440018becab9cc8880031719573991100064fb22e73222007c9c645ce64440018decab94c8880031b195729911000657b22e53222007cac645ca64440018dcea314c8880031b5d4629911000667398c53222000ccd7318a64440010fd0fb2ac8880031b1cb65591100043f438cab222000c6c7219564440018becbb9ac8880031719773591100062fb28e6b222000c5c651cd64440018decbb92c8880031b197725911000637ba8c4b222000c6c75189644400199ee6312c888003331cc62591100043ec16eab2220008bf845d564440011bf06baac88803a3720d755911000477c12eab2220018ec825d5644400187eebba2c8880030f1d774591100062fbaee6b222000c5c75dcd644400193ee9b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440018deebb92c8880031b1d7725911000657ba6e4b222000c
  | 9 => 0x71d0f100143f42ceca1e200087d859d943c40031dd053b287880023b60a7650f100045fc22eca1e20038f5861c543c40050fd0b3b087880021f6167610f1003c5e422ec21e20038f5869c443c400193ec839a8388113271907350710005d8c06c8a0e20009b68719141c40019aeec39a838800365dd07350710006cbb20e6a0e2044cd6641cd41c40899a8c839a8388003651907350710006aba90e6a0e2000d55521cd41c400117f0eb208388002e520d4110710006d8a0ae020e20009b7845db31c408f56908bb6638811e3de1974cc71023d5a422c798e2067a9c8458e31c408953908b18638803b3698d700c71001c7ac36e818e200097585dd031c40071eb0fb1863880023de1d630c7102255a422c618e2000b948458c31c4089d28c8218638813e2fe1d64d031027cdbc3a83a062000b948350740c40073690ea0a8188002e520d41503102a46fc3ac7986203f8de8798d30c40071790eaa2c90800e2f21d425921001c6e41ae931c2000a9c844ca63840015af02994c70800e3721d5358e100045fc22e4b1c20078bc845c963840071b90e992c708002a72113258e1001c6fc3ac7a1c20038bf8759243840ab17f0eb2683081132799073506100064eb20e6a0c203f8df8758f31840a91bd0f31a6308003271d2634c6100064e3a2c698c200087e86dcb65440050ff0fb16ca880031b5cb62d95100043ec3cc5b2a2000a3e8498b654400147b09316ca8800297a0e62d95100052ec1cc5b2a200087f8758b654400147f08b16ca880028f21162d95100052fc1ac5b2a2000a5c8358b65440130fb0e316ca880031b5c862d951000636c38c5b2a2000e658118b6544001cc8c510eca8815a9d21921d95100073231243b2a2000c3d741d365440a54ed023a6ca8815a9d60474d951022d3b40ee7b2a2056a7581dcf65440018bae639eca880021f61e72d951000637c12e5b2a200087e871cb65440018dae4396ca8836a9da0472d95102b53ac08e5b2a200087e8790b65440010fb0f216ca880021fa1c42d95100043ec3885b2a2000a5e8310b65440014bb06216ca880021fa1e32d95100043ec3c65b2a2000a3f844cb654400147908996ca880029de0532d95100053a40a65b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a205687e87c8765440010fb0f90eca880028fa1321d95100051ec2643b2a2000a5e83c8765440014bb0790eca880021fa1c21d951004c3ec3843b2a2038a7681dc365440010fd0f906ca880021f61f20d951000637b9641b2a2000c6f72483654400187aebaa6c888002ad60754d91100161e3aca9b2220028bf87553644400147d0b216c8880028f61642d911000c5fc3a85b222000a3e8510b644400147b0a216c888002a7a0c42d91100054ec1885b222000a3d82d97644400153d
  | 10 => 0xb0a6000c3f651d1614c001878ca3a2c2980031bd9772585300063632ee4b0a60008f787584614c00156908b08c298002b9209611853003c5f426ea30a60008bd84dd4614c00156d09908c298002b560f211853000732a904230a600087f855db414c0050f90abb682980021fe1576905300143e42aed20a600287e85dd9414c0010fb0bbb2829803a3720c76505300062fb2ee6a0a6000c5c65dcd414c0018beca39a82980031719473505300043fc2aec20a600287c855d8414c0011df04bb082980063b20976105300766c184ed98a6000c3f65dd1314c001878cbba262980030fd94744c5300061e328e898a6000cb474d85314c001968e830a62980031719673d01300062e32ae7a026007c9c645cf404c0010ff0abb2809800a1f215765013000477c12eca0260018ec825d9404c0010fd0dbaa80983461fa1f655013042c3e43ecaa02606bc7a76d97304c0d7cb6c7b2e609800e2f21d54590300746e41ae4b2060008f7815c9640c0011e902b92c81800e2f21d42590304e6ca218e2a186000c6f7254a610c0038d8e4a94c21800e3d61e519843001c7ac3c433086000e6552886610c00117f08baac21801e2f21175584300045fc22e4b0860078bc845c9610c00187ee9a92c21835b0f1d352584300061fba2a4b0860d5c3c74549610c0018dee4a92c2180071b1c9525843001c7a43aa2b086000e6552885610c0071e90e90ac2181562fe1d64d043003d5a422c320860678df835d9410c01d938e6b22821803b351ce61504300766a39ac2a086067a9c84586310c08953908b086218113a5993410c4304e74a32082188600e9db865c0310c0019b70cb80621800356e15700c430006ac42ae0188600ecdb625c0310c0019b2c4b80621800356d49700c430006aca92e01886000c7875dd9300c0018f6a5bb260180031e54b764c0300063dbb6ea980600087f825d764c400587ceb2a6c98800a2fe1d54d93100143f42ee5b26200087d85dcb64c401d1bd07b96c9880023760f72d93100143fc3ea5b26200087d87d4b64c40010ff0ea96c9880021f61d52d931000c5fc3a85b262000c6f7254964c40038d8e4a92c9880022fe1d64193100043fc12ebb1e2002c5e7594f63c40051bf0ea9ec78800a1fa1772d8f100043ec2ee5b1e20078be84dcb63c400117b09b96c78800a1fe1f52d8f100043ec3ea5b1e200087f8754b63c40010fb0ea96c78800637e1d32d8f1000e37392a531e2000c6d7254a63c400117f08baac78801e2f2117558f1001c7a40aeab1e20008bf845c963c400f17908b92c78800e3d2057258f100061fba6a4b1e20d6c3c74d4963c419f8e8e3a92c7880030fdd15258f106ae1e3a2a4b1e2000c6f7254963c40038d8e4a92c7883431d1c55258f100065bba0e2b1e2000cb4741c563c40011bf0eb18c78800e3d61a
  | 11 => 0x4c0018df04b96ca980021fa1c72d95300051f420e5b2a6000a3d841cb654c1b74bd06396ca981ae9760c72d953000636b90e5b2a600087e8790b654c0010fb0f216ca980021fa1c42d95300043ec3885b2a6000a5e8310b654c0014bb06216ca981ae1fa1e32d95300043ec3c65b2a6000a3f844cb654c00147908996ca980029de0532d95300053a40a65b2a600087e870cb654c0250fb0e196ca980028fa1032d95300051ec2065b2a6000a3f845c7654c00147908b8eca9800297e0d71d95300952e41ae3b2a6000a6f825c7654c0014d904b8eca980028fa1071d95300051ec20e3b2a600087e87c87654c0010fb0f90eca980028fa1321d95300051ec2643b2a6000a5e83c87654c0014bb0790eca980031bdca21d95300043f43843b2a600087d87087654c0018dee410eca980028fa1370d95300051ec26e1b2a6063a5e83dc3654c0010fd0f906ca980021f61f20d953000637b9641b2a6000c6f72483654c00153b06216c8980021fa1f655913000636396cab22600087e87195644c0018d8e432ac8980031bd9772591300063632ee4b226000c7765dc5644c0018e8cbb8ac8980031dd9471591300063a328e2b22600087d82dd5644c0011df04baac8980063b20975591300047bc0aeab2260008f4815d5644c0018deebb92c8980031b1d7725913000637c2ee4b226000c6c85dc9644c0010ff0ab92c89800a1f21572591300045fc22e4b2260008df835c9644c0011ef02b92c8980023d205725913000637ba8e4b226000c6c751c9644c00195ee8392c89800333dcc72591300043f43ea4b22600287c87d49644c0018dee5a92c8980071b1cb52591300043f43aa4b22600087c87549644c0018dee4a92c8980071b1c952591300045f43e84b226001cac72d09644c0031790ea12c8980072b1c942591300046f43e64b226001ccc72cc9644c0031b90e992c898007331c932591300063bbaee2b226000c7475dc5644c0019cee5b8ac898003391cb71591300063ba96e2b226000c7552dc5644c0018eeea38ac8980031d1d471591300065bba0e2b226000cd7731c5644c0019cee438ac898003391c871591300063ba90e2b226000c75521c5644c00196e8438ac8980032d50871591300066b990e2b226000cd5321c5644c00117f0eb20c898002ab20964191300055a40ac832260038bf87592434c06155904b248698002ad2056490d300063bb2ee2a1a6000c7465dc5434c0018eeca38a86980031d1947150d300065bb20e2a1a6044cb4641c5434c00717d093b086980022fe1d6410d3017556412c821a6000ab481590434c0038dce4a96c2980031b5c952d85300055b42643b0a6000e6552087614c0050fd0dbaac2980021fa1f655853000636396cab0a600087e87195614c0018d8e432ac2980030fd9774585300061e32ee8
  | 12 => 0x2ada1032986300055ac206530c6000c6f72549618c0038d8e4a92c3180031ddd751586300055b426a2b0c6000ab584d45618c0015ab07a8ac318002b9a0b515863000572c16a2b0c60038f487545618c0014ed0b90ac3180029d61721586300055b42642b0c6000ab584c85618c0015ab0790ac3180039954a215863001c7a43a42b0c6001ce472485618c0014ed0a10ac3180029d614215863000732a9042b0c6000c77759d5618c00156d093aac318002ad61275586300056b41ceab0c6000ad5839d5618c0015cd053aac318002b960a75586300056bc1aeab0c6000ad4835d5618c0014ed0b3a2c3180029d61674586300056ac1ce8b0c6000ae6829d1618c0015cb053a2c318002b5e0d74586300071baa4a8b0c6000a77855cd618c0014e90ab9ac318002ade1173586300055a422e6b0c6000ae7825cd618c0015c904b9ac31800395d4e535863023c7bc3a86b0c60448f48750d618c0014ed0b392c3180029d61672586300055b424e4b0c6000ab5849c9618c0015ad07392c318002b560e72586300056bc1ae4b0c6000ad4835c9618c0014ed0a392c3180029d614725863000672b90e4b0c6000e6752949618c001ccf04a92c31800399dc9525863000732392a4b0c60d0e6720549618c1a1cca40a92c3180029da1642586300053ac2c84b0c6000a7685109618c0014eb0a212c318002b5a0c42586300056ac1884b0c6000a76858c9618c0014eb0b192c3180863de1d32586300f47a43a64b0c6000ab7844c9618c00156908992c3180029da1432586300053ac2864b0c6000ab6840c9618c00156b08192c31801f2799273d063003e4f322e7a0c6000cd673587418c0050fd0bbb483180021f617769063033e4f326e6a0c6044c9e641cd418c00193ac839a831800335dce61506300066a39cc2a0c6000cd473585418c0019e4c2b84631800387d4a648c6300070ea94c918c603fc9e71992318c00117b0dba263180022f618744c6300045f43cc898c60008bc87591318c00196ee930a63180032d1d2614c6300065bba2c298c6000cb474585318c0019e2c3b82631800387d4a640c6300070ea94c818c6044e9781990318c089d29033206318153279c6640c6300074b90cc818c6000e9421990318c07fd2e2132063180ffa5442640c6300074b324e218c6000bd1809c4318c0895a908b08631800395d49610c6300072aa92c218c6044ad786d04318c089d2cc9a086318002b5618410c6302274b3208218c600087e86dcb654c0050ff0fb16ca980031b5cb62d95300043ec3cc5b2a600087f8758b654c00147f08b16ca980028f21162d95300053bc0ac5b2a6000a748158b654c0250fb0e316ca980028fa1062d95300051ec20c5b2a6000c6d7218b654c0d74b90c996ca980039318932d95300061eba0e9b2a600087d879cb65
  | 13 => 0x51f42c84b246000a3d85909648c0071790ea12c9180028fa1442592300051ec2884b246000a9d83109648c00187eeb3aac9180028fe1573592300051e42ae6b246000aaf825cd648c00155904b9ac918002ade0573592300055a40ae6b246000e1f5394d648c00147d0b392c9180028f61672592300054fc1ae4b246000a9c835c9648c00147d0a392c9180028f61472592300054f418e4b246000a9d831c9648c1a147b0b292c9180038bd4a525923000717c12a4b2460d0e2f20549648c1a1c5a40a92c91833e8fa1452592300051f42c64b246000a3d858c9648c06117f0e992c9180ba2f21d32592300055bc0a64b246000ab4814c9648c00117d0e192c9180022f61c32592300051f42864b246000a3d850c9648c00147d0b38ac9180028f61671592300054fc1ae2b2460008be87d45648c00117b0fa8ac918002a7a0f51592300054ec1ea2b246000aae82d45648c00155b05a8ac9180022fa1f21592300045ec3e42b246000a3e85c85648c00147b0b90ac918002a7a0f21592300054ec1e42b246000e2d52885648c00147d0a10ac9180028f614215923000716a9042b246003aba80085648c0015730010ac91801f2e99170d0e300047ac36e2a1c6047cb664dc5438c00196ac9b8a87180023d6187150e302265b320e2a1c6000cb5641c5438c001972c9b82871801ea7e194310e30005ca40a8621c6000c6f7254a618c0038d8e4a94c318002ada1351986300055ac26a330c6000ad583d46618c0015cd05a8cc318002b960b519863001c7ac3ca330c6002c7675946618c0014ed0b90cc3180029d61721986300055b4264330c6000ab584c86618c0015ab0790cc31800e3d61e219863000732a944330c6000a7685086618c0014eb0a10cc318003395c8219863000732a904330c6000c77759d6618c00156d093acc318002ad61275986300056b41ceb30c6000ad5839d6618c0015cd053acc318002b960a75986300053b42ee930c6000a7585dd2618c0015af06ba4c3180038dd5254986300053b42ee730c6000a7585dce618c001caea729cc31811e3de1d43986302247a43a8730c6000e954310e618c0014ed0b394c3180029d61672986300055b424e530c6000ab5849ca618c0015ad07394c318002b560e72986300053b428e530c6000a75851ca618c0019cae4394c31800ebca00729863000578c00e530c6000e675294a618c001ccf04a94c31800399dc9529863000732392a530c60d0e672054a618c1a1cca40a94c3180029da1642986300053ac2c8530c6000ad78350a618c0015a906a14c3180029da1442986300053ac288530c6000ad68310a618c0015ab06214c3180029da1632986300053ac2c6530c60218f7874ca618c03d1e90e994c318002ade1132986300055a4226530c6000a76850ca618c0014eb0a194c318
  | 14 => 0x6871cd61100899ace839ac220113351d073584402274a3a0e6b088044c94741cd611007f9aee039ac2200ffa5d0073584401ff4aa00e6b088007ab68494d611000156b0929ac22000395d4e53584400053b42ce4b088000a75859c9611000f56d09392c220002ad61272584400056b41ce4b088000ad5839c961100019a8e7392c220002ade11725844003d5a422e4b088000ad7835c961100015a906b92c2200029da1472584400053ac28e4b088000cd4731c96110001caee7a92c220003951cf525844067f1ba06a4b0880cfe3540d4961101a14eb0b292c22000399d4a52584400055bc22a4b088007ab4845496110001c6f08a92c2203578d21152584400072bb9aa4b088000e54735496110001ccf04a92c22000399dc9525844000732392a4b0880d0e374054961101a1c6a80a92c22034399c81525844068732902a4b0880cfa768514961100014ed0b192c2200029d61632584400047bc3a64b0880008f4874c9611000156f08992c22001ead21132584400053b42864b088000a75850c9611000f56d08192c220002ad610325844003e5b38aed2088000c3f525da411000187aa4bb4822001f2da05769044003e5ac0aed2088000a9c835864110001d2f06b0c8220003a520d61904400071ba92c32088000e3552586411009f96ee0b0c822013f2d5c161904400045fc32e99888007cb674587311000196ae8b0e622003ab520d618c44001c7a40eec98880008bf845d9311000196ee930a622001f2d1d2614c4400065bba2c29888007cb47458531100071eb02bb062201132d105760c4400056bc1ac2188800087f825d764cc0050ff0fa96c9980021f61f52d93300043fc3aa5b26600087d8754b64cc0011bf0e996c99803a2fa1f54593300061fbaea8b26600ea9e83d5164cc0018dee4a92c9980071b1c9525933000c5e43a84b2660078be84dca61cc00117b09b94c3980031bdc9525873000e36392a4b0e6000c3c7559140cc01d938e6b22819800387d4e53992306851ec2ca53246000e2f5294a648c001c5f04a94c9183438bc81529923068716902a532460cfa3e8514a648c00147d0b194c9180028f61632992301845fc3a6532460078bc874ca648c00156f02994c918002ad205329923003c5f4386532460008bd870ca648c00147d0a194c9180028f614329923003c5f43ea332460008bd87d46648c00153d07a8cc918002a760f519923000557416a33246000aad82d46648c00153f06a8cc918002a720d519923003c5f43e4332460008bd87c86648c00147d0b90cc9180028f61721992300054f41e433246000a9d83c86648c001c5aa510cc918002a7e0d21992300054e41a433246000a3e85086648c00147b0a10cc9180038b548219923001c5f43ea8b246000c3f75d51648c0071790eaa2c91800e2fa1e425923000
  | 15 => 0xbba262a00021fe15760c5400143e42aec18a80008ef825d831500031d904bb062a00030f195740c5400764e31ae818a800099d8710c3150001d288630862a0002ada1b410c5400047bc0ae531880008f4815ca631000f53908994c62000e3721d5358c401845fc22e4b1880078bc845c963100011ef02b92c6200023d2057258c4001c6e43a64b188000c6f7254a61100038d8e4a94c22001eada1351984400056b41ea33088000ad583d4661100015cd05a8cc220002b960b519844001c7ac3ca330880038f58714661100014ed0b90cc2200029d617219844003d5b426433088000ad683c8661100015ab0790cc22000e3d61e219844000732a944330880038f58708661100014ed0a10cc2200029d614219844000732a90433088007ab6849d6611000156b093acc220002b5a0e75984400056ac1ceb3088000ae6829d661100015cb053acc22001ead21173984400072ba9ca73088000a76859ca61100014eb0b394c22001eada1272984400055ac24e53088000ad6839ca61100015ab07394c2200029da1472984400053ac28e530880d0a758594a6110001ccea5294c22000399e09529844000733b92a53088000e647254a61101a1cce40a94c22034399481529844067d3b428a53088000a76858ca61100014eb0b194c2200023de1d32984400047a43a653088000ab7844ca611000f56908994c2200029da1432984400053ac28653088007ab6840ca611000156b08194c22001e2f21175584400046fc1aeab08800e8dc835d561100cf938e9b9ac22019fa510773584402a66ac0ee6b088044c9c741cd6110089d288239ac22003b3560473584402266ba08e6b088044c9c411cd61100899a88239ac2201132510473584401fe4fa00e6b08803fc9d401cd611000f17908b92c22000237e0d72584400746e41ae4b088000c5f73d4961100018b8e7a92c22035b8d10752584400062fb9aa4b088000c5c7354961100018dee4a92c2200071b1c952584406af1a20aa4b0880038f687d45611000f56d09a8ac220002b5a0f51584400056ac1ea2b088000ae682d4561100015cb05a8ac22000e3d21d515844003d5a422a2b0880038f687c8561100014ed0b90ac2200029d617215844003d5b42642b088000ad683c8561100015ab0790ac220003351cf215844000732a9442b0880038f487485611000f5690890ac2200029da1421584400053ac2842b088000cd4730856110001ccaa410ac22001eada1275584400055ac24eab088000ad6839d561100015ab073aac220002b9a0a755844000572c14eab088000ab7845d5611000f56908baac220002b5e0d75584400056a41aeab088067e9474dcd61100a9d2e81b9ac220153a5503735844003d5b424e6b08803fad6839cd611000f56908b9ac2201132d1d073584402a56b438e6b088000cd
  | 16 => 0x3d95400043ec3ce5b2a8000c6f825cb65500010fd0e396caa02168fa1072d95404251ec20e5b2a8000a5e831cb65500014bb06396caa00031b5c872d95404243f43c85b2a800087d8790b65500010fd0f196caa00021f61e32d95400051fc2265b2a8085a3c844cb65500014ef02996caa00029d20532d95400043f43865b2a800087d870cb655010b47d08196caa00028f61032d95400051fc22e3b2a8085a3c845c765500014bf06b8ecaa00029720d71d954000537c12e3b2a8000a6c825c7655010b47d0838ecaa02128f61071d95400043f43e43b2a800087d87c87655010b47d0990ecaa00028f61321d95400052f41e43b2a8000a5d83c8765500018dee510ecaa00021fa1c21d95400043ec3843b2a8000c6f72087655010b0fd0f906caa00021f61f20d954000637b9641b2a8000c6f7248365501b987ae832ec6a00023da0772d8d400047ac0ee5b1a8000a9e83d0b635005d17f0ea16c6a0002a720d42d8d400054ec2065b1a800087e87d9563500018d8e5b2ac6a00021fa1c6558d4000636390cab1a8000c6f65dc963500018d8cbb92c6a00031dd977158d400063a32ee2b1a8000c77651c563500018e8ca38ac6a000237e1d6318d4000566412c631a8000ad48158c635000f17908b90c6a00023de057218d400047a40ae431a8001c6e7254863500018dae4a90c6a02130f9db6590d400070fb2ec721a80558bc865c643500018eecbb8a86a00031d1977150d400063bb28e2a1a8000c74651c543500019aec638a86a00033518c7150d400061e32cec21a8001c6e7254b61500018dae4a96c2a0002b5a0f21d854000732a9043b0a800287e86dd561501090f90dbaac2a00021fa1f655854000636396cab0a800087e8719561500018d8e432ac2a000317d9773585400062e32ee6b0a8000c5f651cd61500018b8ca39ac2a00031bd9772585400063632ee4b0a80dcc3d7419461500011ef0eb08c2a0002b520d611854000572412c230a8000ab581d08615000156f02a10c2a0002ad61321185400056b41e4230a8000e65520846150001878cb3b682a00030fd4a76d05400061ea94eda0a8000c3e76d97415010bc6883b2a82a000317d9773505400062e32ee6a0a8000c5f651cd41500018b8ca39a82a01136510473505400066a39ec2a0a8000cd4731854150109878edb2a82a011365dc473505400068fb28e6a0a8000d1c651cd4150001a3ea439a82a00034754873505402264fb00e6a0a8044d9b601cd4150001b28e7b0a82a0003271cc61505400071bb28c2a0a8000d94731854150001b30e7b8282a00021fe1576cc5400143e42aed98a80038be86dd3315000156d0da0e62a00021fe15768c5400143e42aed18a800287e85dd931500010fb0bbb262a001e2f210764c54042e1e3a6ca98a8000c3f65dd13150001878c
  | 17 => 0x886244d9474105310c41d9aca7bb262188033554f764c4310063ba96ec9886200c7552dd9310c53936d0fba262188032dddb744c4310065bbb0e89886244d97831d1310c539b29063a26218a732d98c744c4314e6cb318e8988629cd96531d1310c401b2aa63a262188034dd48744c4310069aa90e89886200d9474dcd310c489b28e9a1a62188021f60b75580310162e3aca6b00623f8dc8754d600c47f5b100a9ac0188021fe1572580310143e42ae4b0062008bf845c9600c40f17908b92c0188021fa1f52580310143e43ea4b00620087e87549600c4010f90ea92c0188fe3721d32580311fd6c40264b0062018f887481600c41d5b106902c0188039a54920580310746e41aeb31e8007a9c844ca63d00015a902994c7a000e2f2117558f400047bc0aeab1e80008f4815d563d000f1bd0fa9ac7a000317dd75358f4003d4f426a6b1e80038bc845c963d00011ef02b92c7a00023d2057258f406b70e21ea4b1e80d5e1c4354963d00018dee4a92c7a00071b1c95258f400054e41a84b1e8007a9c84cc963d00031b90e992c7a001ea72113258f400056a40a64b1e8047cb474dc563d008fd2887b8ac7a011f3560f7158f400063ba96e2b1e8000c7552dc563d00899388638ac7a01132d1d07158f402274a218e2b1e8044cd7431c563d00899688638ac7a01133510c7158f402264a218e2b1e8000c77521c563d00018eaa438ac7a01132dd087158f400065aa10e2b1e8000cd7321c563d00019aa6438ac7a001f279cd7690f400055a40aed21e8000ab48158e43d000717d09bacc3a000e2fa1372987400055bc0a8530e8000c6f7254961d00038d8e4a92c3a000327ddb73507400064fbb0e6a0e8044d97711cd41d0001a3ea439a83a0003475487350740226cbb08e6a0e8044d94611cd41d0001938e730a83a000e2f21176cc74001c5f426ed18e8067c9c43dda31d000f93ce8b1c63a000e2f211764c7402264e21aec18e8000ad78158c31d000153f08994c720002b52053298e4001c6e43aa6b1c80008f7815c963900011e902b92c72000e3721d3258e400056a40a64b1c8000cd6631c543900019aac638a87201136510c7150e4000637b92a530c8001c6c7254a61900071eb0f28cc32000b1d9d6519864001c7ac3c4330c8000e655288661900018dee4a92c3200071b1c9525864001c7a43aa2b0c8000e655288561900071e90e90ac320003351ce61506400066a39ac2a0c809ce966310431900010fd0db96caa000a1fe1f62d954000636b96c5b2a800087d8798b65500010ff0eb16caa000297e0d62d95400052e41ac5b2a8000a778158b65500014e902b16caa00661f61c62d95400052f418c5b2a8000a5d8318b65500018dae4316caa02128f21942d95400071631285b2a8085a3e84dcf655010947b09b9ecaa0003175cc7
  | 18 => 0xc40156b03190c8988c22fe1d321913103c5e43a643226200ab7814c8644c40156902990c89881e2fa1c32191310045ec38643226200a3e850c8644c40147b0a190c89881e2fa1f51191310045ec3ea23226200a9e83d44644c40153b07a88c898802aba0b511913100556c16a23226200a9f83544644c40153906a88c89881e2fa1f21191310045ec3e423226200a3e85c84644c40147b0b908c898802a7a0f21191310054ec1e423226200e2d52884644c40153f06908c898802a720d21191310051f428423226200a3d85084644c401c5aa4108c89881e2fa1c50191310045ec38a03226200a9e83140644c40153b06280c898802aba08501913100556c10a03226200ab681140644c40156b02280c8988028fa1720191310051ec2e403226200e2d52c80644c401c5aa4900c89881e2fa1c20191310045ec38403226200a3e85080644c40147b0a100c898802a7a0c20191310054ec18403226200ab681080644c40156b02100c89881f2d19271d0d3103e5a322e3a1a6247cb464dc5434c40196ec838a86989132d1907150d3103e4e324e7a0a6207c9c645cf414c4cf938c9b9a829880327d9073505312264e320e6a0a6200e3752193314c401c6aa4326629880387d48648c5310070ea90c918a6200c6f7254b604c4038d8e4a96c09895327d8e74981310045f43ec8b026200c3f75d91604c401878ebb22c0988032b1cb64581310045f438c8b026200c3f75191604c401878ea322c0988032b1c8645813100657b26e4b026200cac64dc9604c4011f70eb00c0988021fe0975d90310143fc3ea5b20620087d87d4b640c4010ff0ea96c8188021f61d52d90312254e42265b20620e8dc835d5640c4011e902baac81883a2fa1f54590310061fbaea8b20620ea9e83d51640c40156d03aa2c81883a3720d72590310047a40ae4b206200c6f72549640c4038d8e4a92c8188062f21d42590310055a40a84b2062448dc874c9640c4899a8e638ac81880317d497610c310062ea92ec2186244cd7415d8430c4899a882bb0861899e37e197110c31226ca20ae22186200a9d8610e410c539b2ce221c8218912a720d64104314e6ca21aec2086244cd7435d8410c53996c86bb08218a732d10d76104312266a21aec2086200c77525d8410c4018eaa4bb082189132dd0976104310065aa12ec2086200cd7325d8410c4019aa64bb08218a72e520d641043123c7bc32e6208629cd94435cc410c4013af06b8082189136510d7010431226cb3a683988629cd9474107310c489b2ce9a1c621880317d4b764c4310062ea96ec9886200cd651dd9310c4019aaa3bb2621891267a1f744c4310064fbb6e89886200c9f761d1310c401a3ea43a2621880347548744c4314e6cbc08e89886267c9e611d1310c401b2ca23a2621880365544744c431226ca3a6829
  | 19 => 0x62fe1d42d923100c6fc3a65b246201cce724cb648c4019aae738ec9188022fa1e42592310045f43884b246200a9d83109648c4cf1bd0f992c91899ea721132592310045fc3ac83246267d94439c7438c4891ef0cb8e871891237e1971d0e312265b320e2a1c6200cb5641c5438c40117b0fb2087188026761f6410e31005cb40ec821c62008bf845d5608c40f17908baac11895237a1e53582310162e3aca6b0462548de87cc9608c4011f70eb00c1188030f5d754d91310145fc3aa9b226200a3e8590b644c40147b0b216c8988062fe1d42d91310051f42885b226200a3d8510b644c40153b06216c898802aba0a65d913100556c14cbb226200a3e8598b644c40147b0b316c8988028fa1462d91310051ec28c5b226200e2f6254b644c401c58c4a96c8988030f5d475d91310070fa9ca7b226200a3e859cb644c40147b0b396c898802a7a0e72d91310054ec1ce5b226200a3e851cb644c40147b0a396c8988038bd4a52d913100717c12a5b226200a3e858cb644c40147b0b196c8988ba2fe1d32d91311845e43a65b226200ab7814cb644c40156902996c8988022fa1c32d91310045ec3865b226200a3e850cb644c40147b0a196c8988022fa1f51d91310045ec3ea3b226200a9e83d47644c40153b07a8ec898802aba0b51d913100556c16a3b226200e3751947644c40117d0f90ec8988022f61f21d91310051f42e43b226200a3d85c87644c40153d0790ec898802a760f21d913100716a9443b226200a3e85087644c40147b0a10ec8988038b54821d91310051f42ee1b226200a3d85dc3644c40156b03386c8988022fa1c50d91310045ec38a1b226200a9e83143644c40153b06286c898802aba0850d913100556c10a1b226200ab681143644c40156b02286c8988028fa1720d91310051ec2e41b226200e2d52c83644c401c5aa4906c8988022fa1c20d91310045ec3841b226200a3e85083644c40147b0a106c898802a7a0c20d91310054ec1841b226200ab681083644c40156b02106c8988022fe1175591310046fc1aeab2262008f7815d5644c40117f08b92c89880237e0d72591310047bc0ae4b226200c5f73d49644c4018bee6a92c8988031bdc9525913100e36392a4b226200c7752dc5644c4018eaa5b8ac8988022fe1d64191310045ec3cca3226200aae82994644c40155b05328c8988022fe1d65191310045ec3cc43226200a3e85988644c40147b0b310c8988022fe1d62191310051f428c43226200a3d85188644c40187ceda90c8988030f9d9521913100717b12a43226200e2c62548644c40156d03a98c898802ad60753191310070fa9ca63226200ab78154c644c40156902a98c898b568f616521913100717a94a43226200e2f82548644c5ad47d0a290c8988028fa1632191310051ec2c643226200ab6818c8644
  | 20 => 0x2a20aa431a8200a5e8590863504014bb0b210c6a0802b5a064218d410056ac0c8431a8244e944190863504015af02a10c6a0802b52054218d410746f43ea231a82008dd87d44635048953d09a88c6a0802a76135118d4100567416a231a8200acd82d44635040153f08a88c6a0912a72115118d410746f43e4231a82008dd87c8463504014bd0b908c6a0802976172118d412254f4264231a8200a9d84c846350401c9aa5108c6a0802a7e112118d412254e4224231a8200a5e8508463504014bb0a108c6a0803935482118d410054ec24e031a8200ad5819c063504014bf0ab80c6a0802972157018d412254f424a031a8200a9d8494063504015ad03280c6a0802b56065018d410746f438a031a82008dd87140635048953d08280c6a0802a76105018d4100567410a031a8200acd8214063504015ad02280c6a0802b56045018d410052f42e4031a8200a5d85c806350401c9aa5900c6a0912a7a122018d410054ec244031a8200ad68188063504015ab03100c6a0803935492018d410746f4384031a82008dd8708063504014bd0a100c6a0802976142018d412254f4204031a8200a9d8408063504015ad02100c6a0802b56042018d412247b434e321a820ecd4639c6435041d9a8c6b8c86a08033518f7150d410066bb18e2a1a8200e1f5218e4150401c3aa431c82a081e2f21970905410064e31ae120a824fcb8605c241504018dee4a96c0a08071b1c952d814127e4fb24e730282008de87d8d60504018beebb1ac0a0803171d7635814100666396c6b0282008de8718d60504018beea31ac0a0803171d4635814100666390c6b028200ccf63dc96050401998c7b92c0a08023ee1d601814103d4e422653188200ad4814ca631040f17908baac62081e2f2117258c4100637b92a4b188201c6c7254963104031b90e992c6208030fd4b76504410061ea96eca088200cb651dd9411040196aa3bb2822080327ddb73504410064fbb0e6a088244d97711cd4110401a3ea439a82208034754873504414e6cbc08e6a088244d96611cd4110401b2ca239a8220803655447350441006cb908e6a088200d94211cd41104050fd0fbaac020a170f1d375580410043ec16eab0082d1c3c741d560104ab1790eaa2c0209562fa1e43580410043fc2ae4b00820287c855c960104011bf06b92c02083a3720d72580410043f43ea4b00820287c87d4960104010fd0ea92c0208021f21d52580412ac5e43a84b0082558bc87505601040153906a0ac020956ae201415804100c7c43a40b008200e695248160104038dce4a96c9988031b5c952d93310745e43aa8b2662018bc8750964cc53936f0eb26839883b271cd64507310045ec3ec820e629cb948350441cc47f93cc73a4c1988071b9c9525833100636b92a4b066201c6e7254b648c4018dae4a96c9188
  | 21 => 0x8758e439048f1ef0cb8c8720a73a59866390e414e55bc32e321c82448de8798d43904019acc638a87208026761f6310e41225cb40ec621c8267b968118c4390539d2cc2318872080237e0d75582410746e41aeab04824f8be879516090405878eb2a2c12093e2fa1c43582410064fb9886b04824f8be87d09609049f17d0fa0ac12093eaea0341582410047dc3ac03048200c5d75d4f63504051bf0ea9ec6a081e3d60772d8d410052f42c65b1a8200a5d858cb63504031bf0e996c6a080297a1432d8d410052ec2865b1a8200a9d840cb635040159d0532ec6a0802b360a65d8d410052f42cc5b1a8200a5d8598b63504014bd0a316c6a08029761462d8d4100727b12a5b1a8200e4c6254b63504018baea3aec6a099f8795354d8d4133d4f426e5b1a8200a9d84dcb63504015ad03b96c6a099eb560772d8d410052f42ce5b1a8200a5d859cb63504cf53d09396c6a0802a761272d8d410052f428e5b1a8200a5d851cb6350401c9ea5296c6a080393e0952d8d410052f42c85b1a8200a5d8590b63504cf1bd0fa8ec6a08023761f51d8d4133d4f426a3b1a8200a9d84d47635040159d05a8ec6a0802b360b51d8d410072ba8ca3b1a82678de87c8763504011bb0f90ec6a080297a1721d8d410052ec2e43b1a8267a9e84c87635040153b0990ec6a08039354a21d8d410052f42843b1a8200a5d850876350401c9aa410ec6a080297a1770d8d410052ec2ee1b1a8200a9d841c363504cf5ab02386c6a080237a1c50d8d410046ec38a1b1a8267a9e84143635040153b08286c6a0802b3a0850d8d4100566c10a1b1a8200ad68114363504015ab02286c6a080297a1720d8d410052ec2e41b1a8200e4d52c836350401c9aa4906c6a080237a1c20d8d410046ec3841b1a8200a5e8508363504014bb0a106c6a099ea7a1020d8d410054ec2041b1a8200ad68108363504015ab02106c6a080237e1d6318d410052f42c6431a8200a5d858c8635040153f08990c6a0802b5e053218d410043fc2ae031a820287c855c063504011bb0f328c6a0802b3a0a6518d4100566c14ca31a82008df8759463504011bb0f310c6a080297a166218d410052ec2cc431a82008df8758863504014bd0a310c6a0802976146218d4100727b12a431a8200e4c62548635041d8beeb3a8c6a0913879535418d410056b40ea831a8200ad581d5063504015af02aa0c6a0802b52055418d412274a20aa831a8200a5e859c863504014bb0b390c6a0802a7e117218d412254e422e431a8200ad7815c863504015a902b90c6a0b7b95d075218d416f72a20ea431a8200e4f52948635040153f08a90c6a0912a72115218d410056bc0aa431a8200ad4815486350401c3f08a90c6a0803872115218d4100727c12a431a8200e57815486350401ca902a90c6a0b7795d055218d416ef
  | 22 => 0xa10c2a1a72ad20d42185430074a41a8430a8644ea7825086150c01c6ea4a10c2a18038d54942185434e55bc266430a869ce9643cc86150d39d2f09990c2a1912b5a1332185432256a4266430a869ce9484cc86150c01caea5990c2a18039554b32185430074ba166430a8600e9542cc86150c014ed0b190c2a18029d61632185432255b4246430a8600ab5848c86150c431ef0e990c2a187a3d21d32185430055bc226430a8644ab4844c86150c01d2c86990c2a188735e1d32185430f66a43a6430a8600e97844c86150c895ad08990c2a1912b521132185430074a4226430a8600ec7824c86150c01caea4990c2a18039554932185430074ba126430a8600e95424c86150c014ed0a190c2a18029d61432185432255b4206430a8600ab5840c86150c014ef0ab80c2a18029d21570185430055bc22e030a8600ad7835c06150c015cf04b80c2a1802b920970185430055ac20e030a8600ab7845406150c8956908a80c2a1802b5e0d50185430056a41aa030a86008f6871406150c011eb0e280c2a1912ada1050185430055ac20a030a8600ad6831406150c015ab06280c2a1802b9a08501854300572c10a030a8600a7685c806150c014eb0b900c2a1912ada1320185430055ac264030a8600ad683c806150c015ab07900c2a18039954b201854300732a924030a86008f6870806150c011eb0e100c2a18029da1420185430053ac284030a8644ab6840806150c0156b08100c2a1802b5a0c20185430056ac184030a8600c6f7254b6050c038d8e4a96c0a18023da1f61581430063bbaec2b028600c7475d856050c019cee5b0ac0a1803391cb61581430047b438c2b028600c77751856050c018e8ea30ac0a180339dc8615814300672390c2b0286008fb875806050c1d93ca7bb286218032754f7650c430061fa96eca188600c3d52dd94310c0196eedb8a86218032ddd87150c43226cbb98e2a188644d97831c54310d39b2cc638a8621a736594c7150c43006caa98e2a18869ccb7621c54310c0196ac438a86218034dd487150c430069aa90e2a18869cd97321c54310c01b2a6438a86218031bdc9529844300e36392a53088600c6f725496110c038d8e4a92c22180a1fa1f75580430043ec16eab008600a6d821d56010c010ff0ab92c02180a1f21572580430047bc0ae4b0086008f4815c96010c010fd0fa92c02180a1f21f52580430043f43aa4b00860087c875496010c038dce4a92c0218031b5c9525804303d4e4226531e8200ad7814ca63d04010ff0ab84c7a080a1f2157098f4103c6e43aa6b1e82078bc845c963d04031b90e992c7a081ea72113258f4100e37392a4b068200c6d7254960d04038dce4a94c7208031b5c95298e410043fc2ae131c820287c855c2639040f1e902b92c7208ba2f21d4258e410046fc3ac631c82678df
  | 23 => 0xd85430053ac2ee1b0a8600ab584dc36150c8f5ab07b86c2a1802b9a0b70d854300572c16e1b0a8600ab5849c36150c011ed0e286c2a18023d61c50d854323d5b420a1b0a8600ab5841436150c015ad06286c2a1802b560c50d854300573410a1b0a8600ae5821436150c014ed0b906c2a18029d61720d854300732a9641b0a8600e65524836150c011ed0e106c2a18023d61c20d85430053b42841b0a8600a75850836150c8f56d08106c2a1802ad61020d85430056b41841b0a8600ad5830836150c011ef0eb08c2a18031bdc9521854300e36392a430a8600ab584d446150c015ab07a88c2a1802b9a0b511854300572c16a230a86028f5879446150c058eceb288c2a1802ad61251185430053b42e4230a8600a7585c846150c0156b09908c2a1802b560f211854300c7ac3c4230a8600e65528846150c014ed0a108c2a18029d61421185430055ac204230a8600ad5830846150c01ccaa4108c2a18021fe1570185430143e42ae030a86008ef825c06150c031d904b80c2a18023d61e651854300573414ca30a8600ae5829946150c011ef0eb28c2a18023d61e62185430053b42cc430a8600a75859886150c011ef0eb10c2a18029da1462185430053ac28c430a8600e67625486150c01cc8c4a90c2a1802ada1b42185432274bb1e8430a8600ea7625086150c015ad0d990c2a1912b5219321854300763b126430a8644ab684dd46150c0156b09ba8c2a18031ddd675185432255b424ea30a8600ab5849d46150c015ad073a8c2a1802b560e751854300573414ea30a8600ae5829d46150c014ed0bba0c2a18029d61774185434e74a21ee830a8644e3654d506150c015ad07aa0c2a1802b560f54185430056bc1aa830a8600ad4835506150c89d2886aa0c2a1912ada1353185430055ac26a630a8600e575394c6150c0156f08a98c2a1912ad21153185430055ac148630a8600a76859c86150c014eb0b390c2a1912ada1272185430055ac24e430a8600ad6839c86150c015ab07390c2a18029da1472185430053ac28e430a8644ab6841c86150c0156b08390c2a1802b5a0c72185432256ac18e430a8600af2801c86150c015e300390c2a1b7b95d0f52185430071b21ea430a86dee5443d486150c8956d09290c2a1802ad61252185430056b41ca430a8600ad5839486150c01ccea5290c2a1b7795d0d52185430071b21aa430a86dde54435486150c01ccf04a90c2a180399dc9521854300732392a430a8644ab6841486150c0156b08290c2a1802b5a0c52185430056ac18a430a8644e9783d086150d3956d07a10c2a1913a520f42185430071ba968430a8600e3552d086150c014ed0b210c2a18029d61642185430056b41c8430a8600ad5839086150c015af06a10c2a1802b520d42185432274ba1a8430a8644e94435086150c01d2f06
  | 24 => 0x2008800000800300080140000010018000000000000000400c00200f800400002b0000000000002000000000000f003001400e0000010014002001000000c000001000002803a00000000000060000018070026003006007c0180040008014016007000800c01800300280040180000018004000001006800000000100000040000010000004000008001800801c008002001800e006000000800200100e800400a006000800000a0000008010000004000800001400000280040020020008000002007000000400000c0008000012008002002c000002000800c00000500000200260000010010004008000800c02200300000080080020000000008001000000801a0010010008012010009000800c00000000100020030018000006000002000000000000080000000000008008008000002001400000a000002401e006000001c000000003801c000000002003800400000080000000020040000000001001800001000400080040240040018000014001001800c000001006800c00400100f801800400000000040000000020028002002000000c00200200d000800800c003800c01a0000000000000001000801c0020010050004008004008001000e000006000c00400000200080000020745f426eb30e8607ab684c8661d0c015ab0790cc3a18039954821987430043fc2ae130e860287c855c261d0c018dee4a92c3a18071b1c9525874303d5b42642b0e8600e655208561d0c1d17908baac1a199ea721132986430043fc2ae130c860287c855c26190c018dee4a92c3218071b1c9525864300e37392a5b0a8600c6d7254b6150c018eaeba8ec2a1802ad61351d85430056ac1ea3b0a8600ae682d476150c015cb05a8ec2a180a3de1d51d85430053b42e43b0a8600a7585c876150c01ccaa510ec2a18063de1d21d85430053b42843b0a8600a75850876150c01ccaa410ec2a1802b9a0a65d854300572c14cbb0a8600a768598b6150c014eb0b316c2a18029da1462d85430053ac28c5b0a8600e676254b6150c01cc8c4a96c2a1802ada1b42d854323d6a43265b0a8600ec4624cb6150c018eaea3aec2a191eada1075d85430055ac20ebb0a8600ad6831d76150c8f5ab063aec2a1802b9a0875d854300572c10ebb0a8647e3654d536150c01caea729ec2a18029da1672d85430053ac2ce5b0a8600a76851cb6150c014eb0a396c2a191eada1072d85430055ac20e5b0a8600ad6831cb6150c8f5ab06396c2a180399d4a52d854300733c12a5b0a8600e667254b6150c01ccae4a96c2a18029da1642d85430053ac2c85b0a8600a76858cb6150c014eb0b196c2a187a3de1d32d854310c7a43a65b0a8600ab7844cb6150c8f56908996c2a18029da1432d85430053ac2865b0a8647ab6840cb6150c0156b08196c2a18029da1770
  | 25 => 0x700100080080060008000002007000001001800600100040000000008004000000003000800e000001001c004002001000801e00900080340180020040048000014001800000200200100080240040038034000000004000000000000000040060000008010000004000000000c00b0000008018002000000400e000000001c0020000000000002003003800000800000000000000010010008002002000800000000100080040000030008004006010000000c0000080008008016000000000000200b000000c03c002002800800200100b800000000200480040000000068014020002005001c00c0000000018018001002000000200400380000040000040014010004000000c00400700080000100090000010006003001801802a000002001c020000000001401c000000000c00c001002009c000000000001000000100f0058002007001000801600000300000060010010008002005000000c022009004000000c000003802c00000e00180100080050038008000010000800001600a00b000400e000006802c002007000804400a0010008000000002000000c01a003005001c00200500000000000060020054000003000003000600a002000003800000280bc0060000018010002012006000002a0070028024004004003000000000000380100000000090000000001001802400400c00100000100080040008012002000000000200b0038008006000003002400600000000440100000008014014000000002c00000000180040020060010024002002006001401a0000020008044004000807c00201b00200080060010018000006003000800002000600080340000030000000022001005802c00a00f001000c00003c001000000a0000000018004002008804c00400300000040020010010000010000001800001400100100640060020008000002000000802c020018001000000000200a8010008000000001400200000300000000070000000000000000002c00e00900080080000060000020000003003800c0000020030004010001001000801a0020000000004009000801c0000020000014000000002800000401b00b0000008005005800000e00600000040020010008034000000000000800000d0000004030008001000000000200100000020000068038000001000000c00000300300000020100018010004002000801401a005002800001a004002000c026000002800801e001001003400a014004800400c0010068000002001000001c00a0000020000012000000001800000e000000800200400b0000000002000001c0080020010000004002000002c004001000005801200000100000040020008008006004001000000400c00200000060000018000010002000800000c005001800800a000001000400c0010010
  | 26 => 0x404492000000000066d0001584f1e0003a9b29800000055d33d400097b13586ac0001902a32e49a2ac9a000310d84c49a4390efc000145099a9180ba0005372fa43b4c20000238d28c4492c70a2c0001812bbb0bc00000028617fc000c3543100011d860a0000001a748f500009c008ea0f000253c00000040580000002b23e380000008c300000008bc000393b47c736bff03e32113c89742d5a4605e80002c380bd398ccb2722aa8590b4b5c2aa7959e975033800000021c00000000000000000000000000000056076c1182978000000ce63cd29399f4c2b1bf800000081864080006c2c210000000000000000000146400000682980008ca0000000000cea0d3b0cc0001010003470a8898f0ab1460000be647713f4000d0100000000000004698000000b4a01a2ee8838a590f128bc6760002a80000b260a134c1c4909a11935f2584e6840e07ab4b87d814058e00000002cf000000151a7bd00011e4604b30555af88622b510a4264c6a01a10000000c540001370c3000000069e000000000000034400005f60000b3400000065b00017a4cdb00005fd6a05ac000000000071825a2778ede8f458602d59dc000000000113400000000000000000000000e340006008f685200000002ab800000053e06f91e0b7b4ec8dc4e800003b097f95de58f23810ccb86b5360f86e0600981285979c00000000019fc02202c0001f50a1a62900d000000000000031d0dfe00043b34300008fc0001df49aa0003b31eac00076b23a02bd63288a0001f8c49c00000018e8aaa2780b325486b8c5f00000000000005eba2fce6458000000018c61320000001142801535285567a7651ef93dc4ac8aa0001c84000000000000075c0000d1061d37c3f80001b98bd286c5ab000000005134da1e514ac6f07b963465a8272c1aca0fde00080040000020000008008002000000000000500280040180000088000016000000001000000a000000000400a00000000000090000004004002003001000e0010010004004007000800000601700100000020020070004000001006800001000000380080040010000004000001000003c002000000000c00201f0020010004001000800000c00100000280020060088000000002000801400a00300680080000060000020000001000800800200100000000080000068050020000000800800400600780100020000090000002005000801403000000380040080020078000006001000002c0000000050004004000005800000001d001002800a003000801000c00000200100320020030044000004000000001a001002000c000002005800000e000003000000600000080080020020050014002003002005400200000100000000010008004004004001800000c00e000003c00a00000580100000000008004008
  | 27 => 0x3ae2043df00cc000a8c1980e9430c00064b0c4d3e01a807890b8cce00025586655e65bd263000000063030f338400000045e1d316ba9b11b596bc3e814140b1bac00057d3d9a0e8eee7680f180516de3a70000000c4856e00000008da28a0002220a562d800003200001646512f2000033c2158000bba6f4000000003600000001b4000230178a0fc6fc00024729ed150b55000000087828308705cd5a68be06d1588e0c00000000000000000001b303dc34a056000131800045820c90d28c02bf2ab11c800014e09f80000fe3a200000008ed4cca520d6c6d61e30acd2aab5a29f8b486302af14d145c3d241b3778000b4eca01dc80009fe0000000000000cc800000002de0000001804c947223450054a0a00068b24c4000363218ae50000d3e00000013d6000000000000000000012fc0002ca3e29b799845cf5d39fe000000000000015f229403894216d0b023ed073d03213c070a70d22200000000000002ac64a80007700004bba7e98000001f70c6967cb412a02e9400000000011600000006452124000000470000177800050280000007a9000325d2f482b18f1d180001c33e0983c0002f500000013ccc616960b8004a13d010a474fd0c301cf0009356000000085c4500001ab000069600036d278c0006b0659000000028820ba0d00006b32eb197c0000001c0ac440000163e7000033c0000001bc541200008e036d674b820001e053b0ba800000a0262000263800000031500000000000005ce0000bc26c2066000013666241a800069c00000000006e80005da98889b8ceb06f2c7800000000000000005e20790000000c7d34fa4246282f66a299e4b1280a4ce948c7f46bb365b13884a7c23fe1e803fa0000000f149ac15f000194000029168f00011ae0001f40551864a575b8855d45825a66800000600005790000fd6000505aee55969f713b000000017600022e875490848f9bb15b25b30812e8400000003414a41820001421b7569a7a335e949c0001d2601000058046c2f40f8557832f1e9a6a91a86ba5578f946029d43ac00000006814cda6602222bc2e0844d91a00041425b96f251a1acaa100000004f880009646d70000f6d59200030c15e55a871910193c0326ced0ef1990000add47998d518c8023c29014faa48d073000097c2be2d31dd80000000002e107660001df087d8320003c917dcc1a2a60002ba00001fb5db2cb48e22610000000810000411889d2debbb65497cc0006fd0001d899fc5a0636045126ec3e5f28b50cb63e0290ae55a90355586af111966a6000195cd8c5962b01f4cf8cae76899a180004fe05ea1b590675230419cc0004b800033900008672d4153cd26000149913d32006e0001ca4118a3d15a8000000900000315c00000000000b400065e17d000075a0000c1a2040006a70000000000920
  | 28 => 0x34e0b7849d3bc2a40662bc06562f08000cf90e31b6400014c38ab3c954c2fc42fa89c048d370002ef5766d3b404974950e98317fab709087db3cc276c0000001529d0ccea77458b9d80cde55d43c000198cb083f480009480002330f0180a38d65cb4d9888000000269c13c4fa3fd1078e7800058c283400000053880010065e63a51cb4650bf9053a56d5d230644623395806913e49fc4acca7f4f7a629454ada00000006ee0000000e540009122fe80009c291c03511fd75a8a20e103080aca8967199385f2b475bf16d84a4179000165040048907b12b81f6d40514b06836a6aa000000159032a2a1a2d5a540894669dc017055e243986432e00032e34888d0b8b0a78b7000800062eb50d5ca9ba67da50130c8d60002a0800085b160962c7ea6c32e10ee8a144e92e8a06c000000000140c6d80004a10001a7a00035598940006550000000fd80000000001502c16000000160238700000009ba0004e48000ad63e20000000000d1a2bd034198a15969c8338000000000081c00061b5fc324400079e0001a8cc5c1740000000000000102904800005e4a688580007dd3718001a9682637398305aa49100000003acb7a0000001220000000000000000000010fc00067d00000000000000000000a4c7bb0001e9400029e00006c00f29ca41e9eb000000043f80000003fd000161179a40c66b00005880000b8800139c63c3eb14016c800000019680006ca5ec00000009e0656a98c5dc7a43fa9a75770d4e69a1bb400044e63d80009e800066eb4a51cc64d00000000000000000000000b772ed84dda289bd00000000000000000000000000000272c00000022d000177c000000000000000000000780000004af00011b8bed49d11593da00031b80018b200063b09f540c6442358794fae8b904bb04168c1c53468d795a01ba3a12c1800000000000000000000000000fa200049c93a8f5a0000002e280000003ca886d41cad54c20000da236508f14c05c80000a100000003dc00025911f626538e83fc1504e83a4ae380000000f61d38000a26000242c01c85212f80000000000002fd179c7554b680000000005050290b145b21828ff0df67aa3a424a04820d71bb1d582f0054592269047a5cb0959a2c0003520001c7d2fa00044f92098bc50929604880008f800007d400000017c000011a000077800000000000000000001955b50000000a7e00025a052a1ff03d89700000000000f900000000001cdc000b4000000012a20001e631cda9414438221a0000b8c48199480003200002bf4d445733bd13452ce416681875138a34d6a61b84666c7c00007a000056c3f684a914ea3130a800000000000e0fdc00073b3b9104d99233d00000000007591b3000189846135099f11405642f9000000049613200003cc8562df306c6aeccd3e2000
  | 29 => 0x184229bc3daa5c193ca695cb1f7d1aa42166b8bb587e82532b17d15301100000784a50341451800071c1a91c018389f21db05f0000de6a1f1d31824bbc00048f28200000002d083b800040d0fca42800000000000015f4d4f38980019620001d118bd4d82673208900f0e30b19ca9350aaa681a317b52b200015c18ac84e6474951b400000000000d50d322893869c0cc067352f7a2ec000d2d49b066c5d23dd278a83000017e0000d1400013e000330092e00053b907c00015e00033d9372b1d65380000000000000bc90cc5110000000000cd166d000000000049684e8c168534103270f64000467a88421e94533198757e01a3000299800082a00000000e69d53e61a30000a3400000000003a34790000000c5100016d142200005180013fe3a13fea1440008fa3e90cb0000b3b0000bf592024500002540001f82cf00004eeabe0e884d970c00046d000066a5b100019c0920d2736a8000000aa400000014f2000000000043cc253690734000ab84808210000c344568fec00000050f207808a00069a800000028019902fc0003c83c6a7f800088f466294400028c576968c4163943df852ca1e00000000c40001621b72768a9a48500008d10d60000000d2400045c5d580007b203c00031240a0b9700003e00007d03a5a6719243364252ab456278a0ee29d8a4a3ac347a560c628fd25298c8000c2a423000188200037f2e64ece0000158001760c941c7a974a985eb64988853122c200ea0bd8760000001a419de00016f000000000000000000000000000000f860000000000d64a58000000071234800000017c6baf4112e1c00048a666000036687154e1404b8a000076afad0885b55f78001a840006598988796b2230b9a0800022a0002bad4b65a400007240000004eb00009cc87725a8000ad28980f58d6000000030900000e40005b4800138c0001bea12c75055700033e00002d600008f00001462321148b720002b80e6037a4b100000000000e700010f400000000013b84a80004e902e80000000e40c88afe45400000015647b44e8a74d42eb8054d8e6957a0003c98000000ba2477b2b80000005880000000000157000190c7cb07020cc236cc42ce800000017d53800012be9f91a1b36586e5bb65f01fc9587a14438f093dc00000012bd2340e800018d08ca39c5c8a5a400000062e00000ea4db31caed000000004a08bc00000000031080004760002c7d5be1ad622b09cb8800066fb2f42e4806050339400073900000005d06806a6aefd43800000028dd8940003b9ad2400000000021844483161d0251d87213539f17953a08f1005123d6b600066f09b48f00005282d78572000694038866813b01b80015d890f01914d525299e45b000000000000034ccc082c5262800000001210d0fc800004f3fb00016e6ad200021cc51c0b
  | 30 => 0x63595000061c2e10001e740000d8472800178600000020d92288a9000270435eac14d1a95581c8850000f9cc4c29d33d93649720744f51c3862e450000a8e0000864000251032223b4a9a7c8706a4868cab9800026f000092000024a0cb00016bec4700000004ea00018916545b20001ff9ab45ae81400000018a06c700000009529f80000124070000000000018ca010000000000b89000000124e00037e10d03e20ca24f80000000000000fc181a8b30000000000c670ad3070000000000000000000068baa440000000000fd8ea2b4f00002cc00000005b80000004bc35631d400000000031a0b746f55390e6481e4d75f500016feb2e67f9d04000d4700011a90de000000190c00000000012700000004f400000005bf35c80016069f3000305d8ac04462a092c55a59f218346cc7c0ad000079c2b800000000009c400000000000000004e10838000ca536d800000067400009a190400011126d40e0506000051da081684df82700000003979c3d83a00035b8db49a495000000000b8000482800000000030d000166a0001b10000000439000319598e1ac12813311cea20686b1c843086a40780000000000000b31a0e7ca05919c57f80003850ad00007252cc2d6488e92e37930618166d81a1000000000039b29b400000000017b04f20003c480009d64ad20ca1780a45630511378a2000044e80015100003e695d048e4c44db00003480000000228baa00000011292d4000406a9e000046007e0d900004370a491883e600000000001225c03588f3c0009f40970740000000000000019269600008740008840001df8000453695b1f90cac78037b01c3c00291f3202087020a13300000c4000000102d1ec000000128125eb480f20c740006b4000001d5b00001bcac4813056f17780019f866100011ec0000003b7351800000055d80000001df5cf80008020004d6a0f96fa00063d0000c501841e4a57000000028700002d40000002bd8bc60002d499180000d560a1ba0000c2e000042c00000029200013fa0000002948eae71100022340008a634b8000000a6b608af740006f90d30b2536800008b80001b294a00025885327b6000000174c0003ec0d3c0ae86e52f281c58e7014080000ebebc50000000000aee4c9020c0001210000000000086366800000070507ca60822a2b6092a3753ea2730001ee066ea304eeafa154e0000ee80000000000002eb17b837200000014500920002db00000001ff179000000038000000000003d826eca66938644258128675a5201f65566c1e3c1975c30a0001c224cc0000003ef000166400058d8000848a0426808ac23a11600000018d600000000001d238a00000000002db563ab2865c7e2310110088892301fb088bf0be1496000179e957540192c20eca866500019c4000066a048bb29b22e4a4
  | 31 => 0x3ec000000525800000062754917c40000001f88000000000000000000000059480000007970e5800000000000000000009ec22d9b89754a74061a980016b4462c115d7c018d042800000098d000290800087c000147c0000000001668e2c7e1000243516251d0001cc0d2a18b0000000000d490000000000000000000088297f058800008200034480014c456d49e302978e49b492800143ab3427a8ae855485c082a8fd09e21332c800000000005299d92e40004b629590180000000000c22a9a36284200006c425d87c824000000000016e80005b6800000075d62a800007c4a65c680000001434b8800000077c35f8e314be4e306b1524fe48391289fec000ab616eb400c280000000000000c090d8a1646c0000523ad854ea321000125552eb980a882645cac8b4300000000000000000000079b39400000008d244e17200005ca15f84908ea542343952022400045c19084b200000024652ec00016f9e100000000002680000ab4000000000082d599a0e08983ed1d2042976246e00007f018a36f000294c56e3ea008000011c42669284e004ebca6841f013ce40208198858f25f503bb360d9e858000063c0000003fb800007a84742089080b40005ea86200000f00040000000c8e2610c34200ae000018b05a6d023cb00000000000000e584b020c5b1ac981a422354b03ac0300004b28ed52d6aa842030188d2000131a1f58c400000000000000000001de40008b71e5018400063818faec962a0001d79be8be040a66a0eec3ec000000246c4aa0005988000000be759280006f03d605713809a8cb00000000a940000002c390e8d3210680012440000941ccd426b8f27e0000000afe2e80e497f424603b055532a24c17d8df18da00060a9b70a6495d00026840002a700000016409ae11b80000001d950d87bc02e3b1000037000000000000000008483988000000000396342400064f260224d5d4a5a12183000000005f20638000b363b1874c55200000018090525975d1a8503405383af1e20b02c4861d2be0ef67753d41ba55524c9322816400047e65aa6dd5bc22c3f993cc77842d1da04687d25d34228000cdc00044aa5cc4e4b231f1800103e000266800d47cb66055000068ec4f1db8584372ab107295f04747b102430f000048b27c00014deb396169b7d91e0cf165800000045d000047cd0879100001541c6547508000057acc100000018e00000000000d5e97c0549e380002c300010a567095a24a2b140000000000f79684bd6000000059ca001bd81340000000000c3c000d21000126485013000780006b65f95c418fd3804d81ea1ab9098bd30001230e2e00046214f57bcaa30001278246000421800000019465b9f703da00057da7d90086360f82858eda5045119470c76907000146410078b51a80011d22d169180009304
  | 32 => 0x4ec00015c41a800044a2084b04b0b2ec302101c6162a08fac3788110930a34b5c6c9047ac8445c2f01008000a6e4092b38980000214000220121c239215133c000a8346f80000fc0004a614499e6189354ab8c8646ee63895588ce2260dd800135000052480016f82b056d96dc00000000005ecd480005720000d1c0003263354000d240ea80011480000c90dd40009af00010d80009a22ed00000000004c70e14000000000000000028717b8000000ab00da01b00005aa360012897a00051b19e800055c0ff2fc49b44450328a0400000023d000000000000000000000005e4a0b903498518496700008750000000000b7013480d9542000000000000000000019202d281c000000000053955cacacff2165000000049a0d107a2fb95c40c70cd33805560001389924000d311220a58a2c8de05daa3c43217a0003284000d2625500000000000798001276ccf1a89e9944430309f9544e7420f2511d5186c87b328a73ce704512408190cd00b94b324acc0c28f37c14ec0000000001c31242cc314c1e519a6a3c00000016ceb6010480010006582608da0c46000402842557e2330ce0730c800fd6670000cd8c5a4d2a04c0000004a58528000cf12cd884800a00000000005360005d01b04ffea7a00014897be4101841f209860000002fdcb5a4a71938ec18c82ea566000145a00000028ec7864180000000f780000000a8160e35d00000000000001958001a6093d0b000012488824bf2cdd0b43235ec800004c2e21930000cd277f2ea0000c387470000000a36d0b651859ccccc60375275c1bad2f23997802c6b572f73118fca6d300025e4000a852d822780000000000000cc0000526000122600000000003940002838000000000459184cb4439167ea26590e35a00033a40000000000000364a2411c18007168ff2952d1591245f1a00000000000390000005490403e95d96ea000000000000000043d2cf00005586332458e540000000da40003f30002524000a4313d19a8000cb4276b44850a2253ce0e18e1200019c0e74ed4bd04578f410a8c4d568a3856003b204b31dd5e2082611a72010e83b2b428cc0000002ad9c788de0000002dd8000000000187d18a07865d23085240002c400000000b43d799f8d34000655000000007a3a802040006f60000001880af04dc2408f20b5851706b8a0436701aa2b944a0ea5209a7033aa3a1cb94c436c3072a5a788000b620000ea40a64420e00d7c0007820002f50d247992ad19e179803a5472cb00008f74120000000040464b3c0000a3900013200000002aa101c0007ae00030a0876c8c64d80014fa27f44715397eca86000113431465342b9f9c0008c101caa811fc83c0c12a4c0000000000000a78d1d0822a6530060567b80000004482401cfc1100002a901987206e40a995a80000000001
  | 33 => 0xa77c0000000e717380007fe0102adc00025349fa5393d24063cfadb97a2b9d445801926a35318dad502ee36a64c17ecb0a817119231c652af43e7ac58fe0a026078b9c000000097b371a0a47758d1bdd6260000001454000a1844300000005200fb800000000000000000c058628f31a400000049a071cfc8c130002f6812668519d10b162800c20e8dc0abeaff582807c9ca2ec54f9ee938e1394fe1e30116b93378000178200014f9951a824041f785497b69b30118000188000501ad3984810d04e80000006c83c004a57fc34c67428652c6b27000265949e74f61e9995586ba458492c000071c00000000008d9000000000000000000000004005fe800000000000031a84d800000029140000000000000000d0e12b8139434000000000000000000011c954a0901d594d80005c620880009468db01d8694000000601944cb20bc66258118eb612d0c0000082a022303a5517e615b61629101f42105b58001a2200027b250467e23f5d72784a7400000030a4000000000000036ea9d000016000000052533d087c43534407040be0d30002f2cd6a70248a954c9067230000000000000428093c00000056105b5818afc3501450aea443025ac105443cd4e200000000000000000000a8b23e2d94000599000000092637a0b5afb097426a1e9177029c3194d8173020cb815709c904403c7211000000000000000007aeaa226712a033072e0b71154000c3137289f0bf8c5335e171d8dc0000002498e4c72b597ac281be2d0474000000000012e932d932b9a000082090c70800007607a257b00000000000000001c400002824558000614ce725081080000000000854cee00900022b00c60005dba6500000000c600010c60000002dc80000000658001686000444800013e6334cf94f800000029a139d5ea75c339243000042325b9c6c4e8830000000050c5453d12b5c0002314c414b4000cec15424c1a0c0001ec21c11d400000009246084df000224512c84e0001ee4000000530a388000ca46090a8c46c2eb04d316c0002290000000f4e63d00000000006e03c30000000b8369000011f200015d93bc5e6890385900d5ee0005d4acfcae402e0df959535823500030100000003f324f952abf51fc8b8cd4a2e62101fd09a60e452a201c6e652e45a0f540000003f508b4d06a644d32ad569866b096217416c043035a65c2e03f4086096c40c81d0001fb91d6cbc46c32fc7886b800005d572005b0002d4885e1fa316800000000015234604f61274bc27953b8ad62c6067d4e632464f96446202a11de91658705fa40aaa2912e76456324c8d284b33a2a970b7041a5672c3c000000000000000089b0003510000b5c35413c93521aa44921f8bd4cbb38a00000000005f9105000033e56228ac88c9870a80c94cba2da36a071073e5cd5fdb215956
  | 34 => 0xc8041880642bad3f0be164817800000015648fa4881e0a20d1a25df17f2558ee238200000000002c6000000079c00000027ec52e0005cd80000001ea36705b0b4a69e21d32bc0004b648b9cf400000000026440000000000000000000566ade0e0e00000031494cad0a3b60000156c7f00032740007e00000131058cb8464000000038800022f4e9a0000000e4c29a00054a112caf023e00000000008d000021086880003db84d00000004c5b43c00031c4cd2e780d283707613280006100000000026a676691da542425e4e6
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x867a000e1858766e502e0000000288780000743a003000828400562490000000000054121c264e52428c3e004c92002a007e0022000000004a0000005c1e000000482c66006a8e0028046c200a087c3c6200000c000000705a5e004600000000003468000006441a607280648a4036321038161400080010200284002418204040040018003002c0054e4a524d84dd46150d39a144361774185434e6a1cc98290c6150c01661901c952185430078154b42cc86150c8989487211321854300781549424c86150d39c87325887150c4300709589521c54310c89194984c87150c430141b261725496010c01464915c952580436ee8510585908635053919698c84735044100545657211cd411040151595084735044100741548211cd41105bdc1443d487158f406ef0510d521c563d0001494935087158f4022525253321c563d0089494944c87158f40226259cc815da43d0001464915c95218d40004a524d81d0861501c3c1441d94735054000507259521cd4150001c17651cc61505407070510473d4961101bfc14411cd525844022625a1073c856110001c4473548215844022625a10739c961101c1c14741cf52584406ff051d0735496110001c44731c952584400068a54980085648c0894949750c4398630005986407254a618c08929698c86640c6300078154821990318c00115898549700c43000712589525c0310c00159190d9073507100056424d415c041c40016249654a21d911000685d94835c46444001a146520d7119110006a120c625c464440016249654a211911000689a1952884644400162691e095219110006895488148064440016449654a21d8d1000591259528846344001a468654a2118d100078119152884634400164691e095218d1000691548814806344001866861c775d8910005a124d811936244001c1765190735051000711194621cd4144001c8464188735051000515259521cd41440898948719063505106a63121c6218d4144001a176520d4110510006a11888350441441392949818d4110510224a5261321903144001494915cc73590100068a549800856404139494935907150c10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4b
  | 5 => 0x4e
  | 6 => 0x138b
  | 7 => 0x5
  | 8 => 0x94b
  | 9 => 0x94e
  | 10 => 0x124b
  | 11 => 0x124e
  | 12 => 0x138e
  | 13 => 0xcb
  | 14 => 0x4
  | 15 => 0xce
  | 16 => 0x168b
  | 17 => 0x9cb
  | 18 => 0x9ce
  | 19 => 0x12cb
  | 20 => 0x12ce
  | 21 => 0x168e
  | 22 => 0x10b
  | 23 => 0x10e
  | 24 => 0xa0b
  | 25 => 0xa0e
  | 26 => 0x130b
  | 27 => 0x130e
  | 28 => 0x180b
  | 29 => 0x180e
  | 30 => 0x24b
  | 31 => 0x24e
  | 32 => 0x144b
  | 33 => 0x16cb
  | 34 => 0xb4b
  | 35 => 0xb4e
  | 36 => 0x144e
  | 37 => 0x16ce
  | 38 => 0x28b
  | 39 => 0x28e
  | 40 => 0x148b
  | 41 => 0xb8b
  | 42 => 0xb8e
  | 43 => 0x148e
  | 44 => 0x184b
  | 45 => 0x184e
  | 46 => 0x58b
  | 47 => 0x58e
  | 48 => 0x178b
  | 49 => 0xe8b
  | 50 => 0xe8e
  | 51 => 0x178e
  | 52 => 0x18cb
  | 53 => 0x18ce
  | 54 => 0x95393
  | 55 => 0x94053
  | 56 => 0x94056
  | 57 => 0x25393
  | 58 => 0x16d393
  | 59 => 0xb9393
  | 60 => 0x149393
  | 61 => 0x138953
  | 62 => 0x138956
  | 63 => 0x249
  | 64 => 0x24953
  | 65 => 0x94253
  | 66 => 0x24956
  | 67 => 0x956d3
  | 68 => 0x24d
  | 69 => 0x94256
  | 70 => 0x16c953
  | 71 => 0x16cd
  | 72 => 0x16c956
  | 73 => 0x956d6
  | 74 => 0x95493
  | 75 => 0xb8953
  | 76 => 0x94b93
  | 77 => 0xb8956
  | 78 => 0x94b96
  | 79 => 0x1489
  | 80 => 0x148953
  | 81 => 0x148956
  | 82 => 0x95496
  | 83 => 0x1409
  | 84 => 0x1449
  | 85 => 0x289
  | 86 => 0x14c9
  | 87 => 0x139253
  | 88 => 0x138253
  | 89 => 0x25396
  | 90 => 0x138256
  | 91 => 0x1396d3
  | 92 => 0x1396d6
  | 93 => 0x138b93
  | 94 => 0x138b96
  | 95 => 0x139493
  | 96 => 0x149396
  | 97 => 0x139496
  | 98 => 0x9c0d3
  | 99 => 0x9c0d6
  | 100 => 0x240d3
  | 101 => 0x240d6
  | 102 => 0x1440d3
  | 103 => 0x144d
  | 104 => 0x1440d6
  | 105 => 0x1689d3
  | 106 => 0x1689d6
  | 107 => 0x17c9
  | 108 => 0x1692d3
  | 109 => 0x1692d6
  | 110 => 0x252d3
  | 111 => 0x252d6
  | 112 => 0x1452d3
  | 113 => 0x1452d6
  | 114 => 0x148113
  | 115 => 0x148116
  | 116 => 0xb8a13
  | 117 => 0xa0b93
  | 118 => 0xb8a16
  | 119 => 0xa0b96
  | 120 => 0x184a13
  | 121 => 0xa1853
  | 122 => 0x184a16
  | 123 => 0xa1856
  | 124 => 0x58a13
  | 125 => 0xa0593
  | 126 => 0xa1793
  | 127 => 0x58a16
  | 128 => 0xa0596
  | 129 => 0x178a13
  | 130 => 0x178a16
  | 131 => 0xa1796
  | 132 => 0x1949
  | 133 => 0x134d
  | 134 => 0x29313
  | 135 => 0x29316
  | 136 => 0x149313
  | 137 => 0x149316
  | 138 => 0xb9813
  | 139 => 0x180b93
  | 140 => 0x180b96
  | 141 => 0x179813
  | 142 => 0x181793
  | 143 => 0x181796
  | 144 => 0xb4253
  | 145 => 0xb4256
  | 146 => 0xb5453
  | 147 => 0x24b53
  | 148 => 0x24b56
  | 149 => 0x144253
  | 150 => 0x144256
  | 151 => 0x1456d3
  | 152 => 0x16c253
  | 153 => 0x256d3
  | 154 => 0x256d6
  | 155 => 0x28253
  | 156 => 0x28c
  | 157 => 0x28256
  | 158 => 0x184253
  | 159 => 0x184256
  | 160 => 0x58253
  | 161 => 0x24593
  | 162 => 0x24596
  | 163 => 0x18c253
  | 164 => 0x258d3
  | 165 => 0x258d6
  | 166 => 0x144b53
  | 167 => 0x144b56
  | 168 => 0x16cb53
  | 169 => 0x16d453
  | 170 => 0x16d456
  | 171 => 0x1456d6
  | 172 => 0x59453
  | 173 => 0x144593
  | 174 => 0x144596
  | 175 => 0x18d453
  | 176 => 0x1458d3
  | 177 => 0x1458d6
  | 178 => 0x296d3
  | 179 => 0x296d6
  | 180 => 0x1856d3
  | 181 => 0xb8293
  | 182 => 0xb8296
  | 183 => 0xb9493
  | 184 => 0x28b93
  | 185 => 0x28b96
  | 186 => 0x179493
  | 187 => 0x178293
  | 188 => 0x29793
  | 189 => 0x29796
  | 190 => 0x148b93
  | 191 => 0x148b96
  | 192 => 0x185496
  | 193 => 0x185493
  | 194 => 0x149853
  | 195 => 0x149856
  | 196 => 0x59493
  | 197 => 0x148593
  | 198 => 0x148596
  | 199 => 0x149793
  | 200 => 0x149796
  | 201 => 0xe8593
  | 202 => 0xe8596
  | 203 => 0x178e93
  | 204 => 0xe9793
  | 205 => 0x18d793
  | 206 => 0x18d796
  | 207 => 0x1a09
  | 208 => 0xd49
  | 209 => 0x14d
  | 210 => 0x28251
  | 211 => 0x954d3
  | 212 => 0x20251
  | 213 => 0xd4d
  | 214 => 0x1a0d
  | 215 => 0x209
  | 216 => 0x2c9
  | 217 => 0x20291
  | 218 => 0x95416
  | 219 => 0x9d716
  | 220 => 0x749
  | 221 => 0xd4255
  | 222 => 0x1a0255
  | 223 => 0x24d55
  | 224 => 0x25a15
  | 225 => 0x134255
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2108
  | 6 => 5425
  | 5 => 3408
  | 4 => 74
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (86420+((h/702+packedAt gbK7 (77996+(h % 702)*12) 12) % 3061)*13) 13
  | 6 => packedAt gbK6 (283904+((h/1808+packedAt gbK6 (260400+(h % 1808)*13) 13) % 7162)*14) 14
  | 5 => packedAt gbK5 (215840+((h/1136+packedAt gbK5 (201072+(h % 1136)*13) 13) % 4948)*13) 13
  | 4 => packedAt gbK4 (5348+((h/24+packedAt gbK4 (5180+(h % 24)*7) 7) % 116)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe03fffffc01ffc03fffffd08f8ffcfe31ff
  | 1 => 0xf00ffc0fc07ffe07ffc1ffc02f7674b363ce7c
  | 2 => 0xffff0007ffffffffe07fff07878c383ff8f
  | 3 => 0xfffffff800007fffff8003f807f03fc0ff0
  | 4 => 0xffffffffffff8000000003fff8003fff000
  | 5 => 0xfff0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x50e20052c494104940024a4a800281142e10b5
  | 1 => 0x61262c054c2db242da41d681873634b162c65c
  | 2 => 0x20956a0104ac594acb40535305858c2816b0a
  | 3 => 0x44d9b39b90060873739a0063b806f03d40de0
  | 4 => 0x488fe3ce3e7379e00610c2183def8003fbb000
  | 5 => 0x8f01020020038100382104203efd7ee8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36567
namespace PEqualNP.Outside.L_meta_36567
open PEqualNP.Outside.L_meta_36567.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 9 := bs0_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 14 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_128 : Interval s2Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_160 : Interval s2Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_192 : Interval s2Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_224 : Interval s2Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 227 := (concat (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96)) (concat (concat bs2_3_128 bs2_3_160) (concat bs2_3_192 bs2_3_224)))
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
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_736 : Interval s2Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_800 : Interval s2Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_832 : Interval s2Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_864 : Interval s2Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_896 : Interval s2Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_928 : Interval s2Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_960 : Interval s2Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_992 : Interval s2Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1024 : Interval s2Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1056 : Interval s2Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1088 : Interval s2Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1120 : Interval s2Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1152 : Interval s2Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1184 : Interval s2Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1216 : Interval s2Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1248 : Interval s2Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1280 : Interval s2Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1312 : Interval s2Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 bs2_4_192) (concat bs2_4_224 (concat bs2_4_256 bs2_4_288)))) (concat (concat (concat bs2_4_320 bs2_4_352) (concat bs2_4_384 (concat bs2_4_416 bs2_4_448))) (concat (concat bs2_4_480 (concat bs2_4_512 bs2_4_544)) (concat bs2_4_576 (concat bs2_4_608 bs2_4_640))))) (concat (concat (concat (concat bs2_4_672 bs2_4_704) (concat bs2_4_736 (concat bs2_4_768 bs2_4_800))) (concat (concat bs2_4_832 bs2_4_864) (concat bs2_4_896 (concat bs2_4_928 bs2_4_960)))) (concat (concat (concat bs2_4_992 bs2_4_1024) (concat bs2_4_1056 (concat bs2_4_1088 bs2_4_1120))) (concat (concat bs2_4_1152 (concat bs2_4_1184 bs2_4_1216)) (concat bs2_4_1248 (concat bs2_4_1280 bs2_4_1312))))))
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
theorem bs2_5_672 : Interval s2Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_704 : Interval s2Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_736 : Interval s2Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_800 : Interval s2Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_832 : Interval s2Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_864 : Interval s2Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 890 := (concat (concat (concat (concat bs2_5_0 (concat bs2_5_32 bs2_5_64)) (concat (concat bs2_5_96 bs2_5_128) (concat bs2_5_160 bs2_5_192))) (concat (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)) (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 bs2_5_416)))) (concat (concat (concat bs2_5_448 (concat bs2_5_480 bs2_5_512)) (concat (concat bs2_5_544 bs2_5_576) (concat bs2_5_608 bs2_5_640))) (concat (concat bs2_5_672 (concat bs2_5_704 bs2_5_736)) (concat (concat bs2_5_768 bs2_5_800) (concat bs2_5_832 bs2_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 44 := (concat bs2_6_0 bs2_6_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 74 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_3392 : Interval gbAtlas 5 3392 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3408 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))) (concat (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800))))) (concat (concat (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440))) (concat (concat bgb_5_1472 (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)))))) (concat (concat (concat (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856))) (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 bgb_5_2080)))) (concat (concat (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304))) (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528))))) (concat (concat (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720))) (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944)))) (concat (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392)))))))
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
theorem bgb_6_5408 : Interval gbAtlas 6 5408 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5425 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)))))) (concat (concat (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))))) (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)))) (concat (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))) (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))))))) (concat (concat (concat (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)))) (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))))) (concat (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520))) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)))) (concat (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840))) (concat (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936)) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)))))) (concat (concat (concat (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))) (concat (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))) (concat (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704))))) (concat (concat (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))) (concat (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)))) (concat (concat (concat bgb_6_5088 bgb_6_5120) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216))) (concat (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312)) (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408))))))))
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
theorem bgb_7_2080 : Interval gbAtlas 7 2080 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2108 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)))) (concat (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))) (concat (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920)) (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0eeeaeaaaeae0e8a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36567.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,3]⟩,⟨.and,[0,3]⟩,⟨.and,[4,6]⟩,⟨.or,[0,8]⟩,⟨.or,[2,5]⟩,⟨.and,[1,2]⟩,⟨.or,[7,11]⟩,⟨.or,[4,6]⟩,⟨.and,[12,13]⟩,⟨.and,[9,10]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36567

open PEqualNP.Outside.L_meta_36567 in
theorem PEqualNP.Outside.L_meta_36567 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
