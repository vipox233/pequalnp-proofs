import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38881.Model
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


end PEqualNP.Outside.L_meta_38881.Model

namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_38881

namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x70011550c33470000c00400e84c1380282bf43fc43fd41de31bd42fd40fe41fd43fe30ff42fc41fc32fe32fe21bc40ff30bc41fc31fe43ff10fe20fd31fd30ff21fd42ff20ff43ff32bf42fd21be41ff31dc31fc30bd43fc42fd10fe10be40fe42fc40fc20fc10ff41fe31fc21ff40fe40fd32fd20
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x829303900a8d8800091405ad01018406010f83802a948180029901010382aa01808022838501910780060a800c068089a117802700062d0100000600800001000201408007ab2d028c0a15cf553309faa2219d434c33aa7a15794e109eaa0653c54482bca7a14f94640dd2808176518cb3e8718d7946319e28a855e531027aa998dd544209f28e853e54c867ca8994f94441d7a92855f53482baa7a0e78c440af288633e51d0ebaa7a14fd4d429f2a6633d544ca7ca821cf548419a28a873f54487688218d794f41bba8a419d420c67ca12067152319ea90819e410c67aa7205794f219faa021b75150f3a86194f54c419f2a4653e54ccae8a2905754e109e2a4633e54086eca2104f14143afa9a433c5150e78a9104fd5221ce18c813c548867ca8195bd49309ea96873d540873aa6204f55320cf29e85b45150e7ca2204f940419f2a061745150f3862206750c319eaa6433f544c6b8a6904f55031b7a92213c548c2baa6105714d109f286859c410c73e8418cfd49439ea94813c544c678a8984f95320b6292219f5350e7ea9104f95310ceaa0633c544867aa8186795031eb28863d4314867aa720e750a31bba8a873d54ccaf0a090e7d5231cfa18633d5490abca61075d04319eaa0413d54c427aa91967d0a319e2a2213f548c7a88218d714d41db288833d53d0abaa790cfd5230ea18c433d53103288218d754c40afa9a219e531033a8718cf94241ba28a619e319027aa9084f943439f2a4216c524c27ea8986750f309e2a0213f54483a862084f54a419f2a0639c418c6f6a090ddd45308ea9e853e540827aa921f50c6109f2a0853c5050b3a871957d4d418ea98819e418c6b8a690dd546329f28c833e54cc3688398cf94040
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2338700000a2410501000001c901a0800001068010c00810121810404004c0a5987548c6946150d308758c54882546154c408758c540423565104318718553d0a2d6215231a5185420c6956510431a5185438ca966010431a5185430cb14540c62187997428c714540c521c550c514c297651043185185531031753145438758e540869661904318d18553102946154c4087185531021d65d08318758e54c821c6550d30c515031042946150f30a3588548c61d639424187d8d52902946154f42c518553102146154f42c550e518ca546154f42c5d85531021d6395310c5d8553d0a3461551328d987548c30d43149308e181544ca1f6354a41a5984548c69562104318758c5050b50311412187d963110316540c610c518553d0b1763145438758e544ca2d62150108d18553d0a1d6315221875943110316510c640
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc0c80060a38ac72a043415c8540c410a0ce5b18a2a1c1576150310420b38ec6a9481051c56314142828e2b18a9105047150c524c20a38ac72a641215cb6510431
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
  | 5 => 2*((h/23+packedAt s0K5 (800+(h % 23)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s0K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/41+packedAt s0K3 (2280+(h % 41)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf01ffffe03ffe07fe0ffe07fffc1ff01ce7e7c
  | 3 => 0xffe07ffffc0fffffff03ff81fffe0ffff38f8f
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1142108c48824810052ca8a25012915414b0b5
  | 2 => 0x24c52914392484a960556454b6412a0cca565c
  | 3 => 0x42894a209069144aaa0255112aa40ca9630b0a
  | 4 => 0xb1674492241d974d3981861cd39c031bc0de0
  | 5 => 0x8c187871c38e1e7f1ce39e780e3188c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38881
namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x3040003ce0800002c00410054420a105f00090000000dff10ff20bc43fc40fc30ff31fd21fe43fd32fe40bc40fe42fe30fc31be43fc10ff21bd41fd43fc32fd30ff43fd41ff42fd10fe21fe32ff32fe41bf41ff41fd20ff40bf42ff30fe31fd40bd42ef32fc42fe10fd31fd42fc20fe20ec32fc41fc21fc43be40
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xe8082999100808000808e00938081038380800104b48b07008280802c00800000079901058000820009000680800001818d81800403802c0000040700018702030080929481888200090182db14943d72a0653e54886b8a6904fd5110d7a1065cc320c278a0a15d14520afa9a853f54cca7ca1a0cf94c40b7294633c548427ca810eb0cb419f2a4653d54c839ca6196b90f329e2a2656d52d0f5886194f553309faa421ad52d067aa990cf151209ea88873e54c4278a8884f552219fa8a85ad540cb3ea6a14f550219ea8e853d54c427aa8086b0c9419eaa063cf430cad8a4984fd5132b7a92876d521027ca721db14931d7a16659c438ca78a898d714d429e2a6633e50d0a7ca0204fd51319e29a85af32d0678a9104f54840d6a12413d54082dca5a0eb54840b7290219c5350ab8a6884f95320aea9c43ad42086eea2986bcc941af298213e548c27ca621edd4541e619663cc430ca7aa9214f94e408e29a856e528c33ca621cfd5130b729081cc324c678a6a0cfd50309eaa4616e52d0edaa5184f1533296a9081ad420cadaa5a0d7d4d209ea888174514c27aa421f30ca309faa2413f52506dca5196710c329f2a065ae430ca7ea9106bd53329e2a2613e5410a7aa5206b0c840c6218653e5448678a8185bd4930d62a6653f54cc67ca820cf950319e28283ac32902dea4884f55231d7296833e54cc27aa3204f54b41bba8a413e53d0a7aa521cf95321b7a92633e5010e7aa9195754c10d7990813e54042f0a098cf552419f2a0416e530ca7ca121d7d4d10d621e653d5190ef6a098cf55032d6a1665ad42c835ea4a14f952319f29e836d528c65aa5a0eb94840b6292215e53886daa4084f55121d799481ad428867ca1206e94040
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x26d00204400000138100110f04000900000000125e0c01c01450001920800040400000000001c00028bd9732d070c530c9418b588505068c63508218b588540c28c6354840c314d424820c63548408b58854cc70c6354b41c315032cc70f63548408b58a54cc28c6350b209318d52d063561153328b58a54c428f6510c328718d52d070c540c9319318d521021c6354840a958454cca8d6110c32c318d521022d6215210a3980430ca8c6350a218718d544862f62546438d584540c30e530ca408b58a544868c6354b41a398f54cca2d62942438b18d52d062d650cb41a398e430ca2c6354840c3d885350b0c53d4942c3950328c22f65cc840c3d8d52d062c65509208bd89519030c540c830d20c8504c63860551218b58a540c62d650c840a3594430ca8e6315332c394d428872542145208798f548828c635092087594430ca0c6354b41
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x80000000e0868239a8428a41031cd6215210818e6b14a890c0e73d89519020639ac52a621215c76510c32818ec29a849040c735885050682b88a819061419c76214d42
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s1K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/55+packedAt s1K3 (2280+(h % 55)*6) 6) % 60)
  | 2 => 2*((h/17+packedAt s1K2 (490+(h % 17)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xffffffe07ffffffe07c0fffffc1ffffc8fe3f
  | 3 => 0xfc07ffff80fe07fff800f81fffe1f01f0cfcc
  | 4 => 0xf0007ffffff0007ffffff001ffffe001ff0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2045088c4122440805949292501229541350d5
  | 2 => 0x448a31103244983160290564a64152a8c8a62a
  | 3 => 0xa9135a2490e90cdaaa8289b13ab41c0d70cb4c
  | 4 => 0xcc2c64492481d164d34f2041cd298031ad0db0
  | 5 => 0xe307871c70e1e7f1c73ce780e3118c1fef000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_38881
namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 1 => 0xffffffff81fffffc0fc07ffffff81fff98ff8f
  | 3 => 0xfff81ffffffffffff0007ff03fffffffe0e3ff
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 1 => 0xa85108890c9122940552251992c90a54983685
  | 3 => 0x10a255122122852950284aa4251654a960c15a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831dd03e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1f6f800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88ee00cc00eeaacc88ee00cc00eeaacc88ee00cc00eeaacc88ee00cc00eeaacc88ee00cc00eeaacc88ee00cc00eeaacc88ee00cc00eeaacc88ee00cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38881
namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x421de53082fca9195714d20ee192637d51ccafaa1195f95121bc28285f45150afaa59877d0e31bf2a6437d53d03ba62985f14d41df208817d50cc6faa3205f94442bf298217f54c86faa918fd48510df2a041de32cc77e8621df94a42df2a0657c514caf8a8985f94241bf29e837e53487f680a057d4d41fa98a217d5310afaa1215f54321bea9c43bf4350afca2106f50b40f7a9221dd4310efaa998ddd45439f2a0657e518c67ea898dfd4143bea8c217d544c2fca8106f95321df210817e548c6fca1185794e21f790c437c548c3f621087794c42fba0a217e53102eca3206fd0a41bf290857e5410efaa610df54742ef21a637f505077c8720df55221fb90c43dd328c6fea91877d4d20bfa9e43f631442f8a6a17d84110bf298837e50d0afaa7a0fd8c431beaa6617f52c42f8a4885754c41deaa0657e518cad8a4885f94730bf2a0817d52442faa71877cc631fa880217e52906faa688774c431f790041df32cc2baa7206fd0c40bf29c417f54486fca610df55220bf29465bd43902faa120dfd5330ef29c437e544427ca990dfd4520be28a617c54086f8a9985fd4e20be28287bd4210bf661185f94321ee18c617d528c2faa5a1df15321fb10e217f514c2faa7196f10c41bf29687dc438c6bca6105f15310fba8a87bf4390eb8a6887d54640fca00817f5050bbaa6217dcc531bf29e43fa40102fea8996f90640f710241745150af8a6905fd4d10dfa00817c54883eca2185f94d10bba8a85ef324ca7ca8105f95220eea9e81f9300c3ec8220fd94640beaa4617e530c6f8a6a05f55332bea8463f741cc6f8a7887b08420dfaa221de43ccabca7a05f94742bea8e817e51902f8a5887bd0a42dfa0c83f521c42faa5105f94220be2a465be42902f8a6105f54041beaa0417f53c83ee6318fd8c421bfa8a85f531c43ea6218df95132bfa9a837d520c77ea898f74c730de21081bd54082faa9215f94231bea86657f5150efaa8195f94720bf29c87de438c2faa790df55030ee19061dd320cafca2085f54f10bf28687df308c2baa6085f14542deaa643df434c3d8a4886fd0842fba0e21dd43ccafea61077cc530fd882217e53c42faa6106f15110fba0863bd4350af8a090df15020efa18657d53906faa518fb88420ee218657d540c6fea818df14f21be29c43ef21087ee21085f55210fa98e437d5290f7e84a07714d42fb18e21f721486faa3105f95130beaa6435f53483ba60186f90140fda8285f710043f680107b08620f7904417c5304378a8905f14131fb10843f5510c2fca410dfd4e21dea08837e500c6faa40877d4d109eaa0657d53486faa221df54642bea84437d5190f7aa9987d14520be292817d544caf8a4085f95021bf28481f741506faa4206fd0f42ef994657f52843ba6418df54e31fba0e437f530867aa9985fd5210
  | 1 => 0x920082fea918fed0320bfa92217d5110afea6085f95320bf280657c54c83bc65185f94443be298437b5050bdc43105f14142ef994637e51086fca4085714d41afa9a857e5190e7ea8905fd5320bf28043bc43907b8a6a0df54632bfa9a857e544c77e87205f54b40bf2a0617e52d067aa990f7cc030bf29841bf54483f660987d08410bea8e41dc53483eca2105fd5020bf286837e540c6fca3215f95332fa10c21bd43d0afaa7905f95120bea88657451482baa7a05fd5032be2a221bc42902f8a690df94841aea9c43bf40902faa1a17ec8120bf280857e54c43da4210fe84010dea18877c504cb7e8220f78c531bb288617e530caf8a70877d0f30eea98217f504caf8a0a0df54440bfa82437c540c37e8420df14540bf28e873c54482f8a4a1df94243bf29081f751483be6218df94e40bfa82637d5490f7ca9984f15131ef18c613e54cc37883205f94f40bfa92877f54483ea8220fd54420bfaa6637d54443eca3995f54830fc200417e50ccbba65985f94832af29c813f54443e88398f78c931efa1c875e53106faa5085fd5130bf294617e54043bc86185f94910beaa0437d53043baa6107d10710bf290637c53883de65195794c42bfa9c21dc430c6fca3187b90842bfa8a81bd43103bca790df14930bfaa6657551ccafaa3987714d10be2a0657d500c6f8a498fb4c832bfaa6217e5310afea9195f94030bf288617e5410afaa5a0df95041ef99065ee21486b8a6a17ed0240bf28c83dd53887f440105f94041eea9883df4350efca7a17754f21bea8085f4410c6faa121df54c40be2a663df31cc2fca910df944319e2a2217e52cc7f0a0a15d94420bfa9a417d53d0bbc86995f54630bf2a461de53902fea2995d54430beaa621fa300c2fca5085f94732bf2a6637d51082fca0086f90541bf28443f840c82faa588778c830af29e437e50842fca0205f54b31eea18617e52903e88390f78c430ee21e61de43cc77c86a1ef50940ef29e817e52cc2faa021dd14543fc880217e508cbeaa3995f15132bfa90217e5010efea898dfd4d40baa8c817e52c42f8a5085fd5221bfaa0617d51d0f7a8520d7d4d10beaa021df438cbba869977d4d41bf2a065df320c6faa010df94621de2a2637d52886eaa2105f94d20bfa92617d510c3b887195fd4941bf29e417d549037882206f90c41fba0c837c54042faa5205fd5010be2a463df324c37a8420d754f21ef21887ed4210aeea2905f94a43aea9841de53042f8a2905f94441bea9c217e5090af8a818df15221fd90441f621442f8a2a1ef90942bea9c85ee320caf8a9996f50040beaa2437c52507bc60985f94740fa28a877d548cbbea6a15f94620bea86837c53c82fca9085f55131bfaa4417d53482fca2207750f31bf28865f75150afea690df94e41f690041de324cbe88210f70ca30be2a
  | 2 => 0x505c050240444c00074665180200c1e0582e0080008404028d901c140007901c06000202c825025e00502c06d36004380483015caa0605b0580f024011481704c0c0082e004bd0001b0bc0106820354662d48602dc34680002037010080000a02c25030c7068050040300403030061c8000a4044ac000446d0d809002245346809c02084000000042806000000ec00025a80180f000430802d000020200100000150273640522da200010080020b8120000000401000b3004830d8140c009014430040700c8a00c030885b0000605800014c40040b00c0f1100006000014780000504c761bd3018000000270000e01c4306c6c01dc108c0508418000000d800000760040300c003b05900809054050141403c22beaa641df430c6faa7105f94020fa20a21de53106faa0195f94820bf29c217d52906fca6187750e30bf29c437f53c43ba64987754e40bea8687ef4250af8a8907d48421bf29c857e5310fee42087d8c721beaa2417e528c6fea4a04f55020dfa16817c53443b86598df15121b7a9221f531087ba8698df94b40be2a2635d5310afea810fdc8610bf2a6617e5210eeca3997710d30af298217d5210efca418770c430beaa4837f524c6fca198df54c41bfaa221bf4290afaa420df54e40fba0843f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd51902b76150841a7191314c25f63551218f59053c865e63949109d594210425f6354a10ae1814290764524c5108f992534432f54149108f992544c76452485109d185544825c6550d32c754d42d035453145428fd91500865e6314540c7d53534423d6414c20c715053482d56388710a758c411023e64d4e109d984540c31d53d0842c7153534823c645473297d8d521027461553309798e510869d63d0040cdd8554cc2776155330d5d0c5150e5d63d53218f994544823e6494b109dd8554c823c6454021ce18154082796014c21cd587544435553544208f992534835653d0721b518543cca5f63546209758c54c831d5494c209798c54c425d63150108f990524c23d649482197d95310c63d6494d20cd551510827661d5010d614f5050a3d64d4b10d594e519031c548c5319d587548c27960d53329dd85534833454d45208f992524426c625511097d8d54c834f53d491097994534427a60d53329758f54042d46150d32d614c5050b5753145429bd9521086756114132cd19151ccad563107219b98a524425e65cc93097d8d544ca3e6415020c794e419026e6295110d594d519023e64d4c209d58653c831c5450d31d5d4c514825c63544409dd85544c75b53d4142cdd50414423e64148109ed81544ca5d6590c309ed95300c3735114142a758c429023e64951108f99053083545314520d554c210431c540c931d594c41c871d6315131a7593308c26f65480208f191510c25e6314a10cb153524425e63947209758e5190b376155321a7590328c27665d051097d8d54086766195120c754d421071c635503297996434c63c6454d10d6d4c5050b34615533097d95430c25d63d50209718d51d0a75658c4219718d54c827761551219d987540c25e650c931c7d53534823d6414810b5587328ca5d639434197d95320ca9c644c431cd153314c6756114e20c7152434c74c53149108f990530865d658c830a7590324c69c6350a419d984520423f6550842cd951510823d6414f10c755131cc3655188420c795253082776154a30c7d50534831e5310640cd55041c863e64d4f21d958452442d46150f319d984504cb7351d414297d95300c25e63150329798f540c33854c81209bd8954442746154840c7150534427561d533297997434c31e5454f218f592538833754d4520b558c414425d63145408fd9151cca3c6454d209b58a534425e6315010b5185430c27461553209d594410c73464544309d185540ca3f6454d2097997314c25e6314c109bd89544c25d63944219dd95310c65d6315321cd150514825d63949108f59353c865d6395110cbd5352443565394420b558732cc25f6355131c755343cc364528c510c755153082766114e209798e548835632544309798f54042e562104219718d5090a3e6494a31c755253c867561d5232
  | 1 => 0x823d6494b109d185544c2d463504418f99352c427b65500409d587540c2d563107319798f52c43645288510ced0c5050a6f654c832ad19131c87645284110d314f524431d54cc7309d984530431c548c9319d586534867661d52209798f520427761550329758c504875553c40109718d500867a6014c2197996434ca7965100209dd8552d0f1c53d0d429798c530823e6414f219798e534431c635533097597430cab4644c510a758f40902756115332d514f5150a5e63149409718d544863d6414c218fd954310e7465485109d98454ccb5643544309d58650d0e7561d4c20d554e510825d65d0c31cd552510826e6294d108f994544c63d6414a1097994534827565c84109d584540c2776155120d550d51cca5c6355310ad1854310e9d640cb319758e544825c6550d319798e529065d63150219ed95200823f6454232ce55340082d561cca318f596540ca5f63540219b988540c356538c7219798e534829d64cc030dc1475050a7765440109d986534825e63951108fd9152442b4644c7109e983540c65f6354b41d9146204827661d50208f1915244274654c510ae18142d02d561cc8329dd85524423d64d4c2097994434c355435443097d8d5090b1d53d0841a719131cc34f53149109718d521031d53d0b409b588540c2766114c208fd9541106b4644c4319718d518825e63d52108f191508cb1d5410f309ed81534865d6594c20d594d510823f6454d219d996214427661d53329d58754883376454430a7590320c29c635084197d8d524425d63d4810d5545300c25d6510c31c754e431065f654c831ad1854350b1e5494f219798e5190b3761550329d18552d0e3e6414f109e983548875553c86218f99052842d561cc831ae1814210b365494420d5d4f5150a5e6394b10d554e519032c54149109798f54886b96010440b9189100427561943429b5885404355518c430dc1445050b944310431c715353442776155130c7550430ca5e63141219718d509065f63551208f59642103543254430d558453442d46150e30ad185431025c6354a109758c544863f655004097d8d511027661943438f191518823e64150328f9925448277615513297d8d51d0a9d63106409798c54c825e63150209dd95411065c63551209718d524425d6394342d9148414435753d45209798f548825d6594c10d514f51482d563885109b58854cc65e63148109718d540863d6414f209e181544ca5e63151219dd952108755510c4309758e54842746154d208f590524c2d563104218fd91518823d65950209798c548873a42141429ed815448754538c5109758f54843355110640d914b414427661d523297d8d54c427960150219758c548865f63551109758e52c425d6314a10ad19131086d46150d319d185528c25d6510c329758c52502b86448020d554
  | 2 => 0x190443d0317e019d602cd80000a0ac0000833000320f80000000068180080800010000050dc0105c0001000000050f400000560343c0900013c04298470040c0300104803000015f83c0f0630140000c090000700c000c032014050400d0c45a048113880305c05000000051b01400038010141b00003000020001f00000000001e80104c220881701000000cc088040040e018040540000005018810180800404160000101501c0e01c350141c018020a8020e0170380204c076a4090801118c020181d3a412068002a00b0041704453370040043e0100b0b86d0001f018b81080300018088000a002094001501b03c080243c0280006c0207f1d5454f21c755332cc26f65508429ed9510042d563107109758e520865e63943418f994544425d63148109798e52086786054d21c754d4210a5e63d53219d98650d0a5d6394a419798e54483376454732d514c414427561d5020c755132cc39643107319d594410867661d52309dd85521025d6394720c7553320ca5e63150219758f54882b860508419e181544865d658c430c7553430ca5e63952108f191534866e65149109d584530825f6550c439d98454083364314543d514f414433461550328f992520865d63952208f997425031c53905419758e544c2d46150c438f99053c823d6494a31d558653c865d63d52219d185544cb5551cc0309798e50d0a6e62150109b98854cc63d6494910c794f439025d63d4b109798f540825e63153219d586544825d6315020b558e210875643547329e58354886756115020d5185531071f5414d109758c54c425e6315031c7551320ca7661d4c209e596100435553c84109b58a54442b46150e409e980540863e6494c308f593538429d63108408fd91534433754145209b189544c2b46150f429bd8953442766194f209d58653482b860509408fd91508c75553440109b189534433943141428f992538825c63551108f592534427960d50319718d52d071e5454c2097d8d509063f6454430b5587324c23d6494c30a718d411063c6454231b9185200835453d05419ed81544
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x584010808200000508200000000000400c00011451c55410c32c28a830a8698d15740c9510c30a318c2aa0658555161ccb30a28e8a88621849474587320c70ab22a398061451d16114d1083aec2a06498e456314a2144322b18a420a2189190524c510c32a630285a04557694c41c870a318c2aa661071d9544c730c8aa631220084557614c414430aaa2c3990654c1c54314142c32a6302842161953181421068a38aa821e61451d16194f21
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x20814865d032544308148755161ccb308148755161cc8328148759151cc030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s3K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/221+packedAt s3K5 (17928+(h % 221)*10) 10) % 664)
  | 4 => 2*((h/200+packedAt s3K4 (20482+(h % 200)*10) 10) % 539)
  | 3 => 2*((h/36+packedAt s3K3 (1225+(h % 36)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s3K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf03ffff81fffff81fffff83fff03fffcfc7e3f
  | 1 => 0xffc07fffe03f83fe0fc0ffc3fffc1e03639fcc
  | 2 => 0xffff81fffffffffff000fffc1fffffff83e3ff
  | 4 => 0x1ffffc003ffffff00001fffe003fc03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x94850808c489108052c52804a52132a82c2e15
  | 1 => 0xa19314914392159605545a42cb6514196196cc
  | 2 => 0x420a25220924422aa02094a8128a495282c16a
  | 4 => 0x8b2c59c492075bcd39b606229cf39063f403b0
  | 5 => 0xc3061871c386371ce38e73300c20183db7800
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0eaeae8e8e0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38881
namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x90600be41bf43bd43de31bc41dc31
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x268a2a1e510431
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s4K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s4K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffc0fff07ffc1ff83e1fff0ff80ffdc1f3cf
  | 1 => 0x1ffff03fffe0fe0ffffe0fff07ffe027e7cfc
  | 2 => 0xfe0ffffc007fffff003fff0fff800fff8f8f0f
  | 3 => 0xfffffff800fffffc0000ffffff003f00ff0
  | 5 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14444628849484053a0a099504c8a2a8c0b1c5
  | 1 => 0x4c208a19202010a0485620231012641816545c
  | 2 => 0x28a910506949096a0425520aa90149530b0e0a
  | 3 => 0xb14e24824c0dae539681188cce658063e00ba0
  | 5 => 0xc18c38e38e71cf9ce7399cc08c460183fde000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xece8ece8eca0eca0ece8ece8eca0eca0ece8ece8eca0eca0ece8ece8eca0eca0ece8ece8eca0eca0ece8ece8eca0eca0ece8ece8eca0eca0ece8ece8eca0eca0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38881
namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6877e520c3eaa2105f14530bf28c65f840c82f8a6a05f94040be29c43bc4390afaa521fb4c832bea8e617f53483ee4310df94e40f7a92817f548c2fca1195fd4940ef98c63bd42502f8a0a15f15332df21081ee320cafaa6905fd5021dfa0481ed4210bda40105fd4910bfa8a857e54086fea0a17e94031bf28887fb40c82fca2085f94241beaa663f830c83da6490df94c31beaa4417f54cc2f8a810778c130bea8e41bc54482faa7215f94e20fb28c617f52c43ee21087ecc320bfaa4637e52cc77c86215f94032bea80837d54cc2fca4886fd09409f2a0417c53042fca521df94720bfa9e437e53d02f8a4a0fbc8220ef1926576518c2faa6105f95120fa18e217d53086fca5185f94620de218837f524c2eaa2106f15132fb10e217e518877ca910df55210ba28a657d540c2f0a0a15f54e21dfa08837e548c2fca420df55242bf28841fb20483de8510774c431bda8285f940842faa2195dd4543be282657e53906fca110dfd4a10faa08837d540cafca518df14f20bf28c837e518c7be64195fd4931fb98a217e528cafca3a05f94430bf2a2637c544c7b88618df54342dea1887bd42d02f8a818dd14543fb20883f431087ea6218df54630bf284637f504cafea890df54f20bf29041f731c86faa4087d10431eea9841be43502fca8216f50441dfa1681f651102faa690df54b40beaa6657e540cbdc6490df55130deaa021f641c4278a8907d88421fca02217f540c2fca198fdd0731bf29e837e50842fca910de54041bfaa0217c548c6fca5985f15221be2a0617d50906fca5215f54a21baa88817f52506faa718df94831bd28443df4390efca9885f54642bfaa6417c54c87d885105fd4d41f710a43f7318c6faa8105f94732bba8a657f51482f8a61077d4d41fda02817c544c2faa3995f54e32ef18a637e54cc2faa7105fd5120ee996617f5350afca990fd50710bf29883bf544c6fca710df14943bfa9821f5100437c85206f90f40be29e217c52502fea8886f90e41bea96837d54c42faa1195ed4132bfaa0417f53503f6a0a14f95230aea98417c54842fca8085e14132bf28c817e5310fbc8621fe14142bf286877c5150afea9885f54f21be292217e53102f8a8995e94031de216837d52c42fca6215b54831fa90a21be540c6faa4206fd0e43be294217e500c6faa898dfd5220beaa641dd324c2faa1216f10840bfaa6657d5210efea998df15320fca00817d53d037886216fd5120bf29861fa20082faa3a1df54e41df21a877c53883f2610877cca32de21283ef324cb7aa8105f95232be2a4616f52502fca0105fd4e20f6292817f53442fca9907e08210df2a4617651102f8a098df94010be29843bf4290af8a090df94341bea96637c54442faa1a1df94042bea9e21be4250afea2a07b94831beaa241f950106fea9195f94c32
  | 1 => 0xf41502fca918fbc8421bf298417e50c86f8a9107e4c110fc102217f544c7e8a2994f95221f7a10417c54c42faa9207e54031bf280437f514c37e8320d7d4d41deaa443f731c4278a898df94041bfa8287bc43502f8a4985f95121bfa9e41fb10843eca2107bcca32bf2a4417c548cafca210fd84110bea8c217d5010afca818df94b41be2a0217c520437c82a0df95132bfaa421bd41502faa910cf55020bfa90217d51d0afca021ef50040bf29e217e53c87f2a110cfd5120bf29a217d52902fca610df55031ee29a83f9300c2fea098df94630fc90041bd43506fca998f7ccb30fd184217c53842faa8995f54c40bfaa2657d50ccbda6590f7d0e31beaa2217d510827ca8087d0c510dfa0e817d5310bbe60185f14532be29a43f7514cafca220df54f42bf2a0837e510c6f4a020ef10e41be29a417f5150ff660105f55010bf2a081fb304c2faa010df95110fb10a21fa40842fca1a17710e31fc180417d548c3f680105f14d41bf29081ec420837a87a0efd0f41f7102417c53c87de85215f94230beaa6437651082faa620df54640bf2a0877c5150efaa6885f94e43bea90617d52907f080107e8c110dfa1887df4350efaa2217750c43de21e8175518c2fca321df14931bf28481f7410c6faa920dfd4121beaa487fb504cb7e86a0df54620bea9661bd41d03ee4290ef10a40fc28265f6310c6faa321f7cc930dfa00817e52d03f480884f15132faa8c61dd320cafea8197d90510ee980617d52842faa7087dcc421bf288857f5250efaa221df54440bea80637d52882faa3195f94c10bfa9c43fb10443de84a15f94a41bf290857e5090efaa7185f94220bea98217d50886f8a810dfd4532fa20e63de53083dc6590dfd4c20f790c437e53842faa198df94b10fba0c837c54cc7f460185f94d20fd984617c52c43f641106fd0842df218833e540c6f8a6a15f14d10bea94617e51d0efaa118fb90842faa0a217c540cbf641084fd5132bf2a0417d510c2fca7906fd5132beaa463df310c7eaa2205b14940bea92217d54486fca7a15f54e40bf2a6657e5190afea610dfd4e10beaa043fa50107ee20084f55230df20281ed21087f681205f95210bf286657e5390bf4a110fd48710fd080217d5010efca8185f94821fd20081f45150ef8a0a1df95130dea10855e530827aa910df54243ae29a83bc544c77ca8105b94831bf29a43f7314c67ea898df54740be28a41f75150efca3985f141419eaa0633d54042fca4085f94a10fd902217d50c86fea690dfd5221fba0a837d52d0efca421df94030bf288817f544c37c87216f95010bea806579500c6faa420ef90b41bf28865ed520c6fca5205f15121fa18e43f521086faa1a0df94742bfa9e21f910042f8a8905e54221ef984617d528c77aa9185f54831bea9e83be42506faa9195f94832bf29
  | 2 => 0x10230030280110006044390402e0241c01c001180502c0304c0b0000204c030340606c01000b10240c0044502406038000011c01406004020100001400020000c806004190d8000040001477000450a0070280203c03000020000005c0300008000000040030802089b200408060000084a0001f0053f000010082a1680e5781f0180506c0700000004180344e01464020000000304c000140c000030d405054060003300003000370a00501c0800800000000000978c5b00004000000040100c000bcb74681014c0001960010310c80007c000f0011f00000016000001602d010007880500000000000010200489018240006b2c00c034000100100413000090580000ccf00c0005c306fc000082c10400000090b4040340002c040180500001175391500609c0200000020000ecc200c0314401000020140702800174be4e013020000240618c001cc3d0101000000000150000400000efa18637e5090b7aa818df14540bfaa6437c54cc2fea0a0fbc8020bfaa063b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x540442786054b419b98b54c427461551328f596431063e64145309e181534863d6590840cd547401027960150319b988540c65f654c431c714e425067661152208f59352042d463505108f99352c431e5494c209d18553d027b60548438f191524425f654c0309d594410c66d6214c10dc147504ca3d6414c219b98853c423d64940309e98054086f2618c110d5d0c5150ef2600c510cd551510823e64940309e1815210e7661150108f191528432c43149408f593530426f6548020ae18142d02786054b319e580540ca7561942439b18953442776155131cd551518c25d6314810ce55150886796014e219e982544cb365494630ced0550106746154d208f99353c873860550209b98b54cc26d62d5310e5d0f410c67a60946428f593530823d659502097d8d524427765440109ed8154482796094642da94a500c67761551309d987548c23e6494d209d984530826f654c832cd951518c26f6255110d514f41506d46150c438f993538871c5350d419d98650ccab46150f419bd8953443646154831ae1814210a9c63505409d5845050a6d62d5330bc58440082776154d21cd153514ca7465485109d584548c2e5620c7109798f540827a65c8110dc5845050b395444010ea108400823f6454830ba588300825e6314a10ce952500c63f6454f10da54a500c67b654c0308f990504873843540418f590514c27965840108f990540426d6215030dc982510837151500409758f54c863e64d4c208fd954210a3e6415020b658c208433654544209bd95210877151900409e594400835953cc020ae181425035653944209e983548863c6454d219ed95401027461551308f990530823e6414e218f59053042796014c219d987530423e6414f10a718d41d031d5310c42ba1814210a7661150329bd954210a3f6550441ae191200827665cc5109e98054042b46150c43ba18940842f26108110dc505501065f63551108fd954010355530c7108f191520c2796015021ec50540442766114142bc58440c823e64d4c10cdd53514cab5640c7108f994544ca9c63504419dd855310b1c5310941cd10951102776154f20dc9845050b1c6355031b9588314427561d5020bc982214425d63150209d587548c25d63d50209b988530433551500409e983538863e64150319d195414423d6414e21ce552500c63f6454d20cb952520c67a6014543cb14b4250275650c421ad59221c423d65950108f593538866e6215030dcd44504ca3f6454c219ed95100423d649463297d8d544c6b66190941ead0b4008279650c0208f990520423c6454b319e583540c63d6494331da14b405023e64943328f59352c42746154c42ce952508863e64951328f993520426f6255130cd552510823d64d4e109d986544cb3854141329758c540863d64943329ed81544ca3e64d4e10
  | 1 => 0x4830145609afc06002386400340002c041401204d0160180016052b0094e00300085e001385506023d0000e00018000c0706028080006074121401800500a000200a220013098010502402014183458029e181544ca7561d52329718d544865f654c832dc9805150f2e431494097d954310e3e65d0d41b658c204425d6510c31cb951520c6b9648c2108f59052042f160107318f19153c82b5640c5109e983540c76a52540319b189544433454cc5318f99251c827561d4c209dd95310c6766114810cdd50514ca7960946329dd8553d023e6495131ce15320483695208210dc144504ca7561150329e980530423d6414f10ad592214423e64951209b58b540c67b6054b41ba189404433941540418f99250cc63d64d4e20ae590208433b5414132cd185540c73a54540319d984548c27b6054d21ce551500c67a60152218f191534832d5494831ab191200837160145439758f548425e6315020c7553430c6796015221dc982518c36952540319718d54442756115220cb149415027a6014e219d58650cca3c6454d109dd85544ca3c6454c218fd954310e6c6255130cd553410c71d5454c20ae982435032c52509409d98753883365494420ad191310c67960d53328fd9153442756115030e510c410c65c63549109ed81534827561d4e209e583538873954d0020ce9085050b7351d41329ed81544863e65d09408f99053086ad6210c429798c540872d5454831cb189540833554c40109798c520432c5488120d554d510827765484219798f54842d8604cb309759653083555394420cd150514ca3f6454f2097d8d544867b6054b31dc90550107395494221cb553420823e64944218f590504867a60152319d984540833a43540418fd91524433a5454221d554c310872c52901409e5805150e7661942438fd9152cc67a60150319b988530873b54d4132ae592304433554946309e980540cab46150d41b958831c871d5494c20a7191310c6e862500409798f54c867a6014c219d987540827765504418f59251c826d6510820cd90c5150ed463507108f992518ca7b65480208f994544c63d6494d20bc580410c67661150309d987548ca756114c20c714e415073642544408f19153c427661d4c20c795153082746154f208f590528423e64d4e20dad085050a3e6515120d594d510831c53d0d419b195324873954840108fd9153486786055121ae590204433554440109e98352042776154d208fd9152842d463504419e580548c6ac62500409d586544ca3d6494421cb14b415025e6314c209d584540827a60946328f99053043586054c209b588540c67a60d53328f596540c6e4614cb219758c528423e6414a109e195304427960d5221ce153504ca6e62d5031c7152314c63d64d4f219bd89544826d6214f108f590530827960951329e19
  | 2 => 0x13c261e1980c565810810360b0181874c503010000f020000e3001000b8030314e824500004045e0a03c029e019c00009038000005030002e163285400130209c28002a8208c05010b86403448013e23160240c001280c02031c0000a00110c8c62
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6c3105406d83981895150040a30e6a0aa020e145398642506a839a82a80832c5c46050940962e030a86a0e9043580410c68a3a2a618e212c5c66090d40c50c4302a8104a8745883008254382c421885891895150040b20e6a0a80885147454c310868a38aa6218858318c5250540a50e8a9041086a0625054044298b88c0aa041a81096110020c28c630aa818d2a7090c5250258b84c3212834c5c06155031
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100921819c24314940c10635c06155031c20625c46055020c80731894150110c10535c26190941
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/275+packedAt s5K5 (16632+(h % 275)*10) 10) % 616)
  | 4 => 2*((h/159+packedAt s5K4 (15732+(h % 159)*9) 9) % 414)
  | 3 => 2*((h/15+packedAt s5K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf07ff81ffe1ffc1f1f0ff87f8fe03ff89e33cf
  | 1 => 0xff80ffe07fff87e01ff0ff87f1fffc00e3ccfc
  | 2 => 0xffffffff801fffffe000fffffe003fff03ff0f
  | 3 => 0xffffffe007ffffff0007ffffc007fc0ff0
  | 4 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x150a88c51125440507892c4a8322a5508e11c5
  | 1 => 0x2126914325084ca009985cc19149a830a2c45c
  | 2 => 0x4214220a0c52016a20009115240512a3016e0a
  | 3 => 0xa5844904803125352220006489600c5540ba0
  | 4 => 0x8c60871c719c679c9ccce66001182306fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38881
namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc8004004008001a00100200000680049102a2c000000000000e00008000210000338870100708000000000408010001df54c07fe32007fd0005ff1001ff90c09ff5000ff88005fc4101ff50c09fd52007f90809fd51007f44005fc31017f88409fe5400ff08001fd42017f94403fe5001ffd0c03fc3001ff14c01fd2000ff8c007fc43007fd0807ff32017f14401fd21007fd0405fe3101ff4c403fe10007fc8007fd32027fd4407fd30007f50405fc21027f14809fd50007f500077f5301ff0c803fc40027f94805fe41007fc8401fc4201ffcc409ff5400ff90009fc54027f55003fc1001ffd4c03fc5001ff94c07fd53027fd4807ff30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x82200bff9484205ffc859002fff6190855fe2848407ff18b4003ff885a0003fd60c84037fb024017ff1492103ffa87a004f7d53d0003ffa864001fb08120007fe43a0082fd65d040ffea1e8407bfd8f4004ffa6490007f8104404bfe98c8400ff58910007fc848808ffd531080bbfa9a202fffccb4200dfcc9a0057fe4048401feb0a8417ff9952107ffc62a0012fe65d08097f3288425ff98e4205ffc652102fff63c8427ffa9e8012ff8874006ffa659000bfc51c8421ff98a8008ff105200077ec89008bfc511085dff10e8403bf98e4216ff861a1007fe20c80077e31e8400bfd894107ff8c2a00c3ff50d0851bfa9a8410ff90d400b5fec690867fc43c84037f3164000fd485100cffca790807fe20440097e32e420bff08242145fac6a101ffe65d0021feb1a801cff0c94100ffca0a0006fc6010805ffa8e4201ffcc14000ff481a001ffe54d04093f3288400ff993200e7f8c6a0812fc65c8033ffa1e4203bf98f4103dfecba105bfe634840f7fb1e8200bf58b4103ffaa9a001bfd6544037fe2828207df99740015fcc2900027f6550405fb20a2000ef50b40007fac4a0012fc654400ffe2048407ff55342017fca2a080efc63d0405fea8a4203bf18d10007f8c88800afe61d080ffe2a48401fb08320057faa49001efc65d080ffeb188407ff58f41005fec99002fff6010801feb02822eff0c742017e882a0802fe62d042ffea824228ff4c94216ffc21a101efe64484617eb2e8405ff4c91005ffec1210777c65504017fb0a8407ff95141017f820908a7fc655082f7fb2a4212ff0c74003ffa8621017f93044005fe20a2001ff8c14003ff882a1007fe10d0047bea988427ff98542067f88390067fd43c8417ff2948407ffd534007ff842a005bed324840fffaa68401bf1834105ff8859081ffe42d0033bea9e4210ff14d40167facb2100bfd3150403fc2028018ff0c321007fe8390006ff6050003ffa868005ff58d10007fa829000efc635004dff302841eff1434103dfcc82101ffd42d040fffa148411ffd4940017fc4390812fc65908017eb064222ff8844210ff86021007bc40d0005ffa0a200dff58f2005ff8cb2103ffe4150003fa0822009ffcc52003ffcc02108fff3210811ff18a4019ffccb21005fac3a0003fd2150003ff8828019ffd4f21087fcc6a00bf7f53d0843ff0808409ff90d20017fa63a08a7fd52508077f31e4013dfd4f4000ffc41a0027fd6348005df20a8223ffd4c42077faa59007bfc20d040ffe21c842dff8834203fda8421007fe504803bfeb2a8207fbd09420e5fec6a081bfd524400ffe206820aff995200effecaa081ffc65d000f7fb1e842cbf59642007fcc4a0803ff6250035feaa64207ffd0b4103ffaa82101ffb40500093e32a2000ef5084200778c890002fd6090801fd9024000bfd9120
  | 1 => 0xffd5248437fe3028207ff90341017f8a288007fc304800ffe21a842fff4c7420d7fca990807bc4050005de20e8207ff95042005fec888037fc43c803fff29e821dffd494106ffca790002fd61908077e31a421bff8c14116ff841a1017fc434400bff29a2008ff8852003ffac5a0003bf4250015feaa2400bff19320017fc82908437f5350039ff9828213ff54f40057faca90007fe2050023ff32a8007bfd9740005fcc4880bffd53d0841fe2968207ff15342036f8ca88023fc3148013ff99240009f59740087fec6a001fff435081bffa1e4002ffd4510077fea39001eff6310841fea868229ffd4542017fa8290806fe605040bffa1a2009ffd4d2005ff8652100bfe415040ffe2a6802fdf54f4212ffa61210c3ff51d08517eb248403bf18d4105ff8859000bfd31c84017fb028426ff1814203ffec3a102fff64c8401fe2122001ff0c32003ffcc621087fc501080ffe32e8415ff94121017f821a08127c6548029ff2968002fb0872106ffa879006ffe40504013fb2a4000bf5911002ffa868809bfc3050805de20a8202bf185420effaa0a0803fd42c840ffe31e8428ff50d4205ffecb90043fd3250001faa0a200bffc872006efaa79000bfd51d0403fd1822002ffc8510025fcca8809bfe2050801fe3128228df54d42024f8caa081ffc415005fff29e8416ff90d21007f8c89001ffe611080bbea9a2002fb8852103ffe85a00a3ff535080fff3288412ff14740067fc4390007fe1048005fd8822017ff5952103ffacba101ffd65d0415ffaa24000bf5874211ffa6221047fc6550003fe186800bff08321017fc4288007fc3044001ff212400dffccb200cffaa7908a3ff3250801feb0a4007ff10f4200ffea090006fd60c800ffeb0e8003bf18e4202ffe6488027fe634800fffa0a8029ffd5142007fa82a002ffc639084bfea9c840bff1972103ffca921037ff53c8035fe2a64207ffd8f4203ff887a000afe6150027ff29e8003bf98f4002ffea68802ffe32c8401beb2e4200ff5932003ff88021063fc40c8401ffb024229ffd414203ffcc3a100bfc105045fffa9e8414ffd474008ffaa4a003bfd54c800dfeaa22029ff55142004facb9086afd65c843bfe32a8207bf1974100ffc409000efc634802dfe31a4209dfd4d201577c812100bfd515042fffa92420bff94b21017f8429081fff43d000ffe2a0841dbf5954103ffe87a1047fd655003b7fb2a8216ff14d21157fcc121002fd62d0013ffb1a4000ffd0520037fea88807ffd30d041bbfa9e4015ff8c12100ffea08800bfc3144027ff9968004bf995420e7fa60a081ffc43108077f3188426ff84142067f8639009ffc315080fffa108400bf98b40007fc84a101f7e6510803ff0864016ffcc121005f8c4a0003ff42c841dffaa64002ffc4121005fec9908a6ff6550803ff0
  | 2 => 0x4200df8c0a081f7d65d0015fe2a24001bf98321007fc8490807fc2048035fea864224ff5404204ffc6490093fd511080fffa1a8013ff0cb4017ff865a102fff6510803fe9868010ff18d40005f8c488083bd54d0405ff082422eff94742005fec29005fff5448453ff32a8407bf9911003ff8c1a1003fd42c8025ff28e8001bfd8110017e84290823fe6148023ffa8a8001ff10120005fac1a0867ed32c8405fea8e4200bfd891003ffcc1a080afd61c843bfea928229ffd9542007fac09085bfd634843bfe2928201ff14320017ec4390812fe654840f7f3264202ffcc7410d7fea190803fd644841bfe98e4002fdc4121017fc62a0803fd4244003fb082200bff14a4203ffc87a0807ff2044003fe2822000ef10941015fcc39007bfe50d04057fb228218ff14321007fcc99085ffc654840fffb2e8023ff4c04200dfec8a001ffc4250041ffa968202bf18642087fa86a000edc6350455ff204842eff147420affc4090803ff215002dbfa9a42049f99721086faa6a00a3fd3150815ff292401cbf58d410e7fc86a0802fc6250417fe30c8401ff08320017f8829080bfd3144055fe08484009fd9510005fec2a000efe634840bff1922001ff08110015fcc3a0007ff404804dfe1028400bf5844207ffc42a0007fc305000fff2a68000ffd092004ffaa69005bee32484097f32e4002ffcc52100f7c81a001ffe54d0821ff9928028ff58d4203ffcc7a002ffe32c8017fe32e4028ff8c94200ff88088017fc6344017ffb064210ffd4d4001df8c6a1027fe5348023feaa2800bffd8c42047f8a290007fc40c800dfe32a2000bfd89400ef7aa8a086ffe505040ffe2028407ff1514203ffac3a100bfc21d04297eb2e800bff0cb2104ff8869003bfc54c802dfe9924219ff4c321167faa32101bfc5444019fe28e4019bf58f210affcc0908b3fd509081b7fb1e4007bfd94420f7fc61a0873dc63504077f31a2000ef5094013ff8a2a10a7fe5250805ffa0a4207ff1034203ffa8421003ff64480037e3068400ffd854203ffa85a000bfe51c840fff32e8404bf195200fffe61a088bfe5110827fe98e800bff0804213ffc42a101fff60d0415ffa8a400bffd932008dfecaa0027ff4348003ffa06400bff94b2017ffc65a1003ff4244005ff8868207ffd8f40007fe429002aff654800dff2922002ff08541025f8caa084ffe32d0005ff18a4207bf9912007ff862a0007fc50d0023ffaa28007ffd09420d7facb90807ff4044003ff082802dff143420077c84a0803ff42c801bfea9e4028ff54d4203ffcc5a0073fd6350403fe1068021ef9004202dfec688007ff505000bfea9a200dff98f2000ff881a0003fc4248005ff20e8202ffc414104efaa6900a3fe53508037eb06802bff946420e7f8a6a0803fe4250001feb0c8409ff50d2014dfacaa105
  | 3 => 0xe9824004bf19540007fe849085bfd53484057e30e8000bf580420d7fea59085bfe5348403ff206800bff18f210effccaa0806fc609083bfeaa2820dbf58f2003ffc83a0006fc60c8401fe3128007ff98342056f8ca90003ff6050803fea06402cff54a42017f8a29082ffc609085f7eb1e842dff04342047fca29000afc61d083dff106821fdfd4f41005fac990807fc505000fff20e8429ff59542007fa84a0046fd655000fff30e8002fb8872103fde852105bfc4348403fea022023ff14c420a7f8a5a006bfe65c84057eb0e8207ffd0c42007fec88804efd63d002dffa1a4210ff4c540017ec83a085fff6548417ff1908400ffd814105ff8642100afe611080bffb1a2021ff8c0420cff8a790877ff5450401ff2128203bf98d420e6fea6a081fbf41d00013eb288410ff8c9400effea0a0867ff30c8447ff9808430ff14b42017f843908c3fd51d0817ffb0e400bff0844200ff840a000bff5148417fe1964018ff8c321017f883a081eff65d0445ff8808403bf18f40015f8c39006ffe2050401ff3122016df54d210fffa65a0812fe6590851fe1928425ffcc642147fa60a1093ff5210815ff2a24007ff18b4100dfcc1a08037f654800bfe1922001ff4c32003ffacba00b3fe6590805ff90a4201ff5434015ffc6321093ff5110803fe0868001ff4c11013ff8c2a10c3fd50d0805fb8828207efd0f410c7fcc190807fc4050055ff2848416ffd4d2104dfac690003fd6250419ff28e4002ffc43210b7fa869089ffe515080fff2088407ff15140007f8849085bff324844bff9848410bf58d4005ff8c02103afd65c8005ff28a2000ff5911012ffc8721053fd51d0001df2168202ffcc5410fdfac7a081fee42108057e30a801fff14f410fff865a0803fc6448401ffb224200b7d8d41017fca3a0812fe654802bfe1824202ff8852101df8c7908a2ff635080dff32a2000ef50740017fc839080bff41504017eb224000ff9894003ffec5a0063fe40c8423ff2928009ff18d2003ffec1a1002fd61c8003fe2824007ff90042017f8629089bfc5050805df20e8201ff48110025f8ca90812fe65c841dff2a64000af1912003ffac1a0883fd52d0403ffa028007ffd094005ff8c621007ff2048001fea12401cff4c941015f8c290043fd535000fffb2e821cff98d4100ff4419001ffd611083fdea1e8207ff951420bdfaca9083ffc5150039dea1a820bff14b2103f7885a0896ff639080dff2a22002fd885100bffaa89086b7e65c8417fe2908400bfd8121017fc63a085fff5048405fe0864203bf98d4015ffe212100bfc41504077e31e4021ff04042157fc6121073bf43504057f316420bffd8e4205ff84321027fd31480017eb06842cffd4a42087fca6a001ffc4350033feb1e4225ff14e42035feca880bffd30d082bfe3024203bf18c
  | 4 => 0x43fc3250005fe20e420effd4b20047fc8290067ee32c8417ffb08840cff9072000fdc4090057fc5048417fe10e4024ff5484203ffcc7a10b2ff659080fffa1e820bffd9642007fa849081ffd41d000ffeb288401ff90120057f8a490007fe304400ffeb1e8007ff104420f7f861a0867fd32c8447fe9908427ff08542017fea3a082ffc64c840dffb2a2005ff14d1006ff8a7900a3fc5350805fe10a202bff0c6420d5fecb9082ffc63c800fffa128201ff8c320005fac488002ff6050439fea9a8201bfd8510017f8a2a0806fc6048455ff084842aef10242137fc60a101ffc63d0001fe3122002ffd072103df8c8900b3ff5090803ff9864025bf98842097fc63a00a3ff305080dffa922004bf99740017d84290807ff1044005fe90a2001ffcc110177fc63a101ff7415042d7eb1a4207ff50f4100ff8209005ffe524844fff8828401ffc4320005fac890803fe6444001fe90e4007ff5804203ffc87a0073fe535043fbea9e8201ff4c140017fea2a0812fe65d044b7eb1c8401ff9434009ffe63a0003ff6244003fea824004bf99541085fec6a001ffe43d08077f31e422fffcc74201dfcc69001efc6510855ff104840fff9454012ffac72100bfe21d045dff886840bff1832116ffca1a1033fe61c80037fb124025ff94e4212efea72107fff32d0457fe28c841aff54b2115ffc832100bfd3148401feb264207ffd0d410e7fec6a0812fe6550039ff992821fffd4f41017fc828809bfe4050803ff2064000ff585400aff84090806fe6090815fea8a4006bf59510057f8ca90053ff52d0003ff2022016ff8c921125faca2101f7d6510805ff18e420eff9972003ffaa9a0807be4050001bfb2a2013ff14f40117fc6221007ff30d0047ff988841cdf54d4116ffc61a1003bf4290801ff3224007bf193210bff8a890807ee20c8017fe308841def9514105ff8a590007fc10c8053fe2928406ff14910017fc42a0873fd4350405fea0e42049f9974003ff884a0857fc404844dfe0828428ff18d42025f8caa1007fd40480077f31a8202ff0c54112ffa652102fff63c8025fe10e8007ff9514003ffccba081efc65d00037f302420fff985400e7fea6a08bbfc21d08137fb1a4002ff0c74115ffcc321007fd50c800f7f326402fff14f4200ffaa08806ffc30504057f30a8402ff8434103df8c8880a7fd5050801ff3224202bf99341057feca90007fe30d0005ff0828202bf9864203ff88321083ff50d040bff31a2030ffd4b4200ff8208801ffe4310851ff31a8407ff5834202dfac6880bfff30d080fffaa68202ffcc72103ffec3a003bfd51c80057e3088416ffd8d2114ffaa2a1027fc32480015fb224002bfd854110ffca021007ff10d000fff2168200ff4874001dfcc7a1067fe43c8431ff2864202ff5451000dfcc0a108ffe5310803f
  | 5 => 0xf81800e0c831c1605c0260040984e0160900580401c0002b84b01009811800004024000000640382d86f004010088000000600c8000a80840b82300e010098120000d0000790460080c80002e004998260000282580f01c00818001782030218110260540002600808c2601f012434010060000242e80103203400806004004030580000080001700c0056e840022010058000400349781900802c1c0100220311380000c004fd00201400004001006044030050320200c85e06e004000e1000020060010360002481b1c603c0d04a10c011630310000e00380200a0100081609a000010240001741ca630040b00001f0300084112c006000000320940242a024000100000005ac088040050020140c0360060cc0d0f307e0ac2301704c03c0f01906e000129210420d804804020034010010ae134fd80200421c0180100e04c50b9c0480000c0090020500c8026300501300003e0ac15002004014068024500942a8580362e0000d60020c80009d000025120200160001e00000e0040380000e01c0000103e0000584b07600006001002000040000da01cca0070e808c0081c00c000132900c81fff8cb4100ffc80a001ffc54d040fffa1c8407ffd8f4103ff883a101ffd62d0401feb048400ff59120167fea32102ffc61c805ffe9968416ff0c92103f7e85a001ffe63d0401bfb2a8227ff8c542007fec2a001ffc40504037e3028423bf58c4203ffcc5a0802ff6448401fea0e4008ff1852009ffa65a0003fd4250445fe1888402ff0c721017fca290847fc5250017ffb2e4216ff4c121017fa828800bfe10c8419ff18e4025ff50e420077e82a001ffc65d0405ff18a2001ff5414000ff04090003df635040ffe3068228ffcc54203ffea82106ffc205040f7e326401affd532103ffec5a082ffe4210813fe29a4019bfd8f21075fecb9000aff614840ffe20e800bff90b2103dfcc521002fd64c804dff2828424ffd4042107fca5a08977d5390811fe10a400dffcc720147fc86a1037fe43c800fde2008407bf1912100ff820a00affe2190803ff286401bff98141147fec6a100bff3144033ff31e4201ff8c12003ffe83a000aff624843ffea9e822aff0c242077facb9002bff5248003ff9824005ff90d10007ee4290847fd5150039ff192820bff1944211efea6210677f53c8403ff2822007ff187400c7fc4190803ff6148005fe28e8221ff8804212ffe652102afd654800fffb2e8407ff18f4100dfcc0210c3fe52d0823ffb2a8007ff1874203ff8a8a0803fd61c804bffa9c8401ffc4120007fac0a1003ff625040ffe21e8214ff54b40167fea921003fd214800fdfa108430ff54b4200dfcc1a101ffc4350459feaa48417ff9512113ffc82a1003bd415000ffeb1e8407ff903420effca4a08a7ff525080fdf2a68207ff10b410077c84a1
  | 6 => 0x2a200806413034000004030070000000080800000c018120ac15c0700000c02c000ad0040300000000c0180c8040040000000806405c038455c40000c0ed0400000580a0002901f04a03c0003d03f04e08c038000220000100c0000ac2b000006000060252140090880100200000804038108000000200040280507c070eb0000000140f01f0200000080502c01001802000040028150040dc02800022008078000000c00028201e0280204a0000000000502a0680000104e0000280000000c03bd6000060110001f802c168820020001100300c014000070302f4070000180680d00207c008100100000040080a0240
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc405974000cfe76d814205ef62118910006bd75d91202c79e41d8d410067d53d894008d7e751894003cff725932005ebc64993200067c43d95200067e70d954127e7d3159721014fc7198b400aef71058720004fd73d9110004ff7358442015f772485101867e65d0b2101cfc735912105eec52189402c7d710d8d4101cde73d9321005bf725054010dbe76d094005ebc6499321006dc65d8d412df3e41d9541004fd735932001cfc73d8121004fd70d9121156bf20d9120004ef72591100067c41d95200067f53d812110ebc2019120005bf7458910006bf64109200057f75582422273d53d0540014ff70d89100057f7559110024fe75d9120004fd75591200ee7e76d9541014fe765092100cfe7498b400067d73d9520006bc65d912001cfc735874005cff73989102df7710d95410067e2159740006bf71d9120004ff7558b41006bf32d912005eee7298b40006bc43d9120006ec52d89400067d65487400067c20d954103fbb60d09400067f72d9541014fd70d89100063d531912026e7c10597400067e73d9541004fd75d932100dbc76505402c79c41d8d41004fd755824201cfe7358b400057f73d9520024fc755932000cfe70d854203ebc7019120004fd75d89412df3c41d9541024fc75d8142136f850d81420057d73d95102067d10d9520006bd64191202879c63109412cedc40d8d410067d65c8740016bc6150740004ff76505200067f535832100cff7118910024fc75d8941004ff7559121014fe71d814205fae62d0a4201cfe73d8941014fd701891000cfe7059121006bf631912010efa3058042005f77448510015bc719094105cff73d93212e67c40d9541014fc76509210067f535824203dbc70d0a420067f535834203e7e435974000cfd74d85400067e71d952005cfc75189410067f73d9510157b820d9120006ef72591201267f7259442016be6150740006bf75d912001cfc73d911003ef74158442004fd73591100067c65d8941006bc40d91210067f6510920024fc75584422673d5350b4002ddc73591100067d53593212de7c31d9541006bc3119120004fe76d09100567e76d952027e7d7159721006bf65d91202cedf40d8d41004fd735824205ef57198910006df50d8d412f73f5390b4108d7c755894003dbf76507400247c7558910004ff75584420067f71597400067f43597210067e7059721005bd70909420067f65d89100067d5398910004ff705912127e7c7159721004fd73d891005e7e3259442156bc30d912015dbe72109412e67f40d954126e7d3059740004ff7159120024fe751894103eef4258b40006bc61d912000cfe70d932110ebf50191200073f65109410067c735944200cfc70d9321016f4614852003ebe64909210079f631094103e7e7459442016bc615054003ef84058341156ed2098b40
  | 1 => 0x87402de7c71d9541004ff73589100047d735974000df8704874000dbe70d09400067c71597400057d75991100067d74d95200247c7558242024fe7558042006bc64485200067d3159740024fe7558321006df63d814103ebc645052005e7e72594420067c6598941004ff75587420357e75109102de7e71d95410f6f710d854000dfa70d09200067f74d95102c6dd41d8d41004ff7358042006be5119120006ef321891003ebe76d0540024fe759891010ebc101912003ebe7610941024fe7558b40004ff7259110006bc64c85201e77b10d951003dbf7150540004ff755932001cfc73582420067f65d8141004fd75d85200247c7559110024fe7598b401df7a30d9510006be41d912000fea72c81200067f53d81422c6dc10d8d410defa60d81412c6de51d8d410067f65989102c6dd21d8d41014fd70d91100c5f77158910004dd73d9321004fd735874203ebe641912005fe82010920156bd10d91200067d53d9120006dd75d8d41014fe7118940014fc71591202c6df21d8d4105ef860583212873f531094105cfc75989102de7c10d9541006dc63189410067f755912001cfc73d8540014fc7498b412de7d21d9541005f570c852105e7e425972105e7c7259721014fe71d932021ebf655054003cbe76d912003e7d435944225ebf7650740046f621583210067c75587420067f6550910006bc73d9120006bd71d91200067f73d9520004fd7358b41156be40d9320006bf7650b400247c75591210067d53d8540006bc41d9120005ec725854001cfe73d8121004ff75d9110005bd7010941006dc52d8d4103ebf605094003cfc76d052005ef9709891005ebf649932003cfe7418910024fc7558642006bf621094110ebd30191201267c6510920024fc75583410067f65d091003ebf60d0940156be6090941005df73585420067e655932105eec4298b4100df6704851005cfe72189102777753c8521004fd75d89400077765505100067d30d95410067e43d954105ef82058042007f3704851003e7e42597400067e41d9520024fe755912003e7c74594422067f20d9520024fc75d852021ebd65505400067d53589100bd7c7559121006ee21d894003efb40580420dfb7405051003e7f4359740016f461487200067f6518941006bc52191200e5de7398941004fd73189100067d745972105ef4215844203ebc649091003faf72509401df7410d9510006bf64d072000dbc7050b40007b57190941114fe7690921014fe7498b410077765485100067f659911005ef4624851003cfd72593201e67f31d9510006df63189411267d725944205e7c63597211e77621d951027e7e105972105dbd76d0a4201cfe735874003ef8405804203ebc64d072003ef7415874000cfc7458740006bc71d9120004ff75583410067d535872001cfe735932103e7
  | 2 => 0x67c72597400067e73597400067e63d95100067e2059442156bf50d912005cfc769091003ebd72191200ddf5719911027e7f3159721156bf40d912001cfe735874205e7d7518940136fa30d814203cfc764874000cfc70587422de7d31d9541006ef62989100047f7558910014fc76d092105cfe72d91101d6bf41d911005e7c60597212067c40d952003fb7619094105cff7118941004fd73583212c6de21d8d4103ebf6110941006be435932103ef84058342006f7315874203fae7290b41006bf64d09210067f655891012edc6390941006dc20d8d4103e7e405944224f9c735074003ebc649092005ebf6499321005df7358141006be31d9120004ff7159320014ff70d9110136bc76509400067f6559120006f930580421df7610d9510004fb7059121005bf715094003cfc745832126e7c7059740006bc64d852008d7c7550540006bd5319120007ac6250940004ff74589102c6dc51d8d4103ef44158442006ed62189402cede54d8d410067f5359320006bf6450921154fe7619120004ff73d894126e7e1059740024fc755804205cff7398b410067e31d952007fb4615054003ef641583411de7f10d95100047f75591203273d5390942006ef62d09100067c31d9520006ef72591101f77953c812005cfe72d93201bcff764872003eec4258b4101cde76d8d410acfd7698910136f8605814226e7d7059740006bf63d9120004fd74d8910004ff73582421de7d70d95100d67f7259721024fc75589100067f6590941006df73589100073f6519120004ff735912003ebf721912000df47650510175ef7259121024fe7558b41006df63909410063d655074005eef201891026e7f3059740004df735911005eec629094000cfc725932005eec6210910156bf72d91203373d53d0a42005bd74c8740007e76248510176ef21d8941005ec7259110005bd71d0940007af62509402de7d71d954103e7f415944203cfc745872005eef2098b40024fc75583212c6dc74d8d4105cff7598b41006ee211894007ef661d85402d5de76d8d4100df670505100defa10d81410057f7558542005dd7398941015f471509410073f53191200067d32d95100067c32d9510176f710d894113cfd7699321006ef6290940006be211912001cfe735872003faf72508420079f7350740004ff75582422e67f43d95412173f5350540005f571109100067f53591200047d7598910004fd731894116cff72591200067d53d89410ed7c75581410067f3059721006bc5119120004fe76109100067e63d954100cfc71d81210557c75505200057d7510920015f47150921006fb705911001cfc73587420073f75507400ed7c75589411de7e30d951005e7e7259721014ff765864226e7e70597400acfd7198910004ff7359121004fd75d81412de7d41d9541004ff764
  | 3 => 0xe76909410067f6599120004fd71d81420067e43d9520006bf511912010efa10580420067d325972105f6e32597210067e3059721024fc75d91100047d73d9510006ee20189410067e21d952005e7e7598910116f6315844203ebf4198b4003e3f41594420067f65c8520004fd73d8121046f431d852013ebd41593210067d63d9510005bf7150842006dc50d8d4110ebc501912003ebd7019120134fd76d0b20004fd72d911003ebe731912005e7f6359721004ff715804201cfe735834224f3f5350740004ff755874005cfc751894001cfc735912001cfe73d814101cdc73591100067d71d9520006de75d8d4103efb705834103ebd76d0a4205ef8605824200cfe7259320015be7190941004ff75580420067c755912005ebe6250842017e762c8521006bd65191200067f72d9510024fe75582420757c7550720005bd7448540006de70d8d410567e72d95200067d53d9321006fb70591211a7b65450510006f870591210067c65189100067d6559321014fe71580422067d30d95200067e63d95200067c6558941024fe755874205e7f60597210067f3259442004fd73d8940024fe75d91100067c755911003ebc4258742004fd72d8540015bc7110941005bd7090b410067c3059442014fc715834200cfc7650540156be4098b4015ef71058642156bc20d912000cfd7118910006df635814103cfe74d89100067d74d951000cfe7058b41005fb705894105ebf62909422067f40d952003dbe74c854010ebc601094101cfe7358b410067c65d91102c6de10d8d41317ad3250842014fc71d894010ebe101912019fb743505100067f5358b40006ec32d8910024fe7559121006bc745891003ef441587402e77741d95411de7f70d9510007b6425051010ebf30191201ed7e76d9510024fc7558b411267c6510910024fc755912119ff130505100067d65d0b21004fd74189102de7e10d9541235be76d05400b5dc7358121014fc72583210067f6558141005bd72d0540174ff7259121156bc609094201cfc73586420f4ff7159110004fd73d8141156be70d91202777553c852126e7f70597400067c65591200067f30d954100df87050540006fb10d8142004fe76d052003e7d4059442006bf74591200067d535864210ebc40189400067d735972118ff1304851003fbb60d054013ef661d85420067e73d952005cfc7518910004fd76c87400057d7599120006de50d8d41006bc31d912001cdc7358910006ef6290941006de60d8d41004ff75d891001cfc73d85200073c6519120006fb705891003e7f74597400057f755812105cff75989100063d53d9120006bd311912003ebe6419110004fd755834101cfe73d91100067e32d95100067f53d91212067c20d952010fae20191200076d32597210067e60d95412c6de71d8d41005fb7059121
  | 4 => 0x81202067c70d9520006bd6419121006dc63d814105cff7610910005ef7258141024fe755911003f3d6550740004fd755912115eed2198b4103cff7659320006bf64c85200067f65d8520014fc74d854000efb62c81200067f535911001cfe7359320024fe75d8542005df735852000cfe705874203ebf425804203f3d6550b4005eee72d9321014fe71591200067f7059721256bd655074005ebd741894005cff70d9120006df52d8d41004fd7098b41005fb70485202a79c6390941006bc51d912005cff7018940006bd641092105ef970d932001cfe73d85400067f53584420247c7559120004ff73d8121006bf641091003e7d4159740137b87050940004ff735832101cfc7358720024fe75583410047f73594420067d5358b4103e7c41594420ee7c6550520004fd73593210047d73d95200067f7159442006bc43d9110016be6150540004ff73593210067f6590920015f671d091005fae52508420067f735944201cfe7358642006ef52189400bd7c755812105ef421587200057f7558141024fc75d9121005bf7250740006bf64505200067f43d95201de7d20d9510004fd7558910004ff7358740006be5319120014fc7259321014fc7159320024fc7558242006be51d91200067e74d951003e7f42597400be7c6548520004ff73d89102c6df51d8d41005bf7458121004fd76d0910006bc625054005cfc73d93200073f53d9120004fd73d8540154be76191200067d53d8542006df735911000df8705072005e7f2059442226bd63d054001cfe73d81420067e7359442006bf6448520006be63d9120014fd72d8121006ef52d894010cfe7690920006bc52d9120006be21d91200d67c65c8520004ff73d8540006bd6319120004fd7358341004fd7358b4003faf7250b400079f6390941135ed72991200067d43d951015cfd71d912118fe5324851027e7f1059721004fd711894023f3f535094005e7c4259442007f37050510006be43d91200067c65991200067f5358341006bf6499120004bf74589100067f53d85200247e76d95202c79c74d8d410073f65909410047f7559110004fd7558b4005f7675c8521015f67150910156be40582420557e75c8520024fc755911003dbf7510941007b4645051010ebe5019120005f970d0920006df54d8d410057d75109102473f53d09400e5dc73581412c6dc21d8d41004fd76109100073f43d9541156bd30d91200067f6550520006ef72589100067d53d9320006bf765084203ebe7519120176f710587421cebd40d91100067f63d95202adbd7390941004fd73d8142024fc75d814100dbc705054000df470485102067c10d952001cfc7359321004fd71d932003ebc4258b412cfd741d8d41014fe71d89402fdbf7390b410067f654852005fae325084203f3e7510941006bd6419110014f
  | 5 => 0x156be10d912003e7d745974013cff7159121004ff73d8141004fd73d85420067d32597401de7d40d9510305bd7590b410067f53d891019fd4735051003cfe749891003ebf60d05402de7f21d9541175be7610941014fe76d852003ef541583410be7e65487400065f65d8d41005bf7150b401beed20d8910006bd31d912005ebf7459320006ed32d89400067f3159740006ec62509400057d75189400067d5398b40136ef2058b4027e7d7259721007d7735051013ded72991211de7e20d95102df7441d9541004fd755834203ebc645092005cfc72586421de7e40d95102067e10d95200aefa20d81210d67e65c8740004fd7558321024fc75d8940006bf6290941006dc6358141005f97090940014fc711891003eec4258b400067c63d9510157ae20d9120156bf649092003ebc64d09200067c7558910015be76909410073c65d912000cfe7018910004fc7648540006df6350941024fe755874021f3c7550540016bc76505402973c65109412cedf42d8d4100cfe76d09200067c7459721024fe75d9121024fc75d85420bd7e7510921024fe75d932003ebc7119120156fa405824205cfc7258740004fd7358740014be7690941006dc73591100067f655094128dbd73109410067d53d911013ef71059121004ff755891000cfd74583410adf57198910006f7614852000cfd72d8520004fd74d81211667c659092003ebc7458b410067c7359721004ec72591100057f73d954110cbe76d09400067e73d951005e7e75d93210d67f76597210067c65d8520006dc73591213173f53508420067f53580420067d5359121016f4615054003ebf4058742046f4615852003eef7258b41156bc40d93200073f65d9120006be6119120006be54d91202e67f42d95412de7e21d954105cff71d9121004ff705932100cbc765054000dbc70d0540156be50d91200077775505100047d73d9541004fd76c8540004ff75d8141024fc7558342046f621d85200067d31d9520015f6719091001cfe73d9120006dd70d8d4105e7c2159442156bd70d9120014fe76d09212076e20d9520006ed621894105e7c6459721016f762c852100cfc70d911018fe632485100067c3259740006ef6250940004fd74d852003e7e4159442004fd73d9120006dd65d8d410dfb87050540004ff75d912114d7c7558542006be631912003ebf6550740006bf31191202de7f31d9541006bf521912013eef2158b41004ff755912003ebf731912003cfd71d8941005bc745852003cfe76c8740004fd7398b4005e7e32597210047f73d9541006be71d91201e67f41d951001cfe7358910004fd759891000cfc7059121007af629094126e7e305974001cfc7358442006bf43d9120006bd425804214e7e6550b210067f531894105e7c325972100cfe76d814105eef2198b4100dfa76c
  | 6 => 0xe75586422c6dd71d8d4100dfa709094010fac2019120006bc6458520065fb705891005e7c205944200cfc7058b4105ef421586420067e32d954126e7f1059740005fb70585421cebf40d9110156bc50d912003cfe76d9121006bf54d912005cfe729891005cfe72d9120014fc71d9120024fc75d8910024fe75d854005eec4298b400067f651912018f77534851007ef4615854003ebf75191200075c75d8d410067c65189410057d75c852003e7c74597400247e76d9510006bc631912003ebc6450720005df735891010ebf1019120005f77250510045f970989100075c63d954108d7e75c854000cbe7498b4003ef74158742004fd75d9120006bf64507201ccfe7619110005fb705094003dbe74c8740004fd7398b410067c32d9541004fe769091005cff731894003e7c405944203cff76d09102c6dd51d8d4105f7575c852101cfc7358b41006ee32d8940136bd40593200067d73d9510004fe7650520014ff7658720004fd75d9121004ff75d912000efa76c81200057f755814230fae205084203cff76d07200067d63d9520004ff7558b40136fa20d81420067f53587400065c75d8d4103fb46150740004fd73d93212c6df10d8d41004ff75591100047f7359740004ff75d8540156bc10d912005cfc725911000dbc70507400067d5318940156be6090b4100dbe70509400247c7558742024fe75593200067f71d95200067d53583210357e7599110136fa40d81420dfb7105054005e7d759891001cfe73d93210047f73d95200067f32d95100067c315944210dbe70508422de7f10d95410f5f77159110006df73591211de7c30d951003f3d751094103e7f405944205cff75189100067e71594420247e751894003f3e65507400067d5318910156bf30d9120024fe75d8910006bc321912001cfc735832101cfe735911001cfe73d932005cff73189410067e659932103ef476505100067d43597210065c63d9541226bf63d054000cf476505100067e31594420067d5358242006bd65d91200067d5398b410067c7159442154fe761092005eef21189102bdbf759094115ebe769094116cff7650b200067d32d954105cff731891010ebe3019120006bc75d912001cfe73d9121004fd7558642006bd321912015ebf41d912100dfa72c81200067d535834203ebf71191200067e30d95412c6df74d8d41006ed3218940005fb70509202a73f539094105ef4615872003cfd72d854205e7d75d9321006bf51d9120004fd73d932001cfc73d891001cfc73580420067e325974005ef571d9321006bd51191202067e70d952000cfe70d89411e67c21d9510006bf64d85201b6ed21189102c7d441d8d4103ebd73191200067f7559110006bd53d912005ebc64593202067f30d95202f73d5390b4103ef46450510014fe7158b4000cfc7258720
  | 7 => 0x95102067d72d9520157ba405824203ebc731912005e7c2159721014fe76d85420057f7359721156bf64909400067d5359120277e532c852101cfc73d912001cfc73d89400067f65509200247e76d9541005f5719091003dbe744854005eec201894103eef6290942006bf31d9120006dd52d8d412273f53d054005e7f21594420057d7510921024fe75d8121006ec20d8941006bf52d91202673f5350b400ddf8705894103ebf4058b41024fe75189400067e215944203e7e43594420067f75591210073d53191200067f65d09200067e72d95410067f65189100adf87059121014fd74d8141006df63d894101cfe735912005ef721584420067f75587422067d70d9520006ef32d8910006bd52191200067e205972105ebc42593201667c65909100acff7058910004fd76d072001cfe73189412de7d74d954105f3e65508420067c65d814105cfc73189410063f53191200067d72597400067f535932103e7d435974026e7d20597400067d7359740004fd7559110006dd50d8d4105cff7598b40014fc71d911022ebf65d0540015bc7190b41014fc7650941005bd71d0a422ed7e76d954100dbc765094001cfc73d91210557c75585201e67c41d9510117b71010941005bc7458910004ff745832101cfc7358b400067e61d95200c4fd709891010ebd50191200067e40597212873d5310941006de72d8d41016bc61d0540014fe71d9110156bc609094101cfe739891013cfd7650921006ef6250941155be70d0a420067f53989100067f53d8141146dc63509410075f65d8d4103ebc4098b400067f31d952003cfe74d85200047f7359721014fc71d8142004fd7598b400067d53d8142004fd7558b41154fd70d91200067d305944201cfe7398b400067e6558321004ff75d8142004fd71d91200067d63597210067d53d8121004fd735834203cfd70d8940004ff7359110006bf73d912005efb205824205ef57118910006df72d8d4105f76215972103cff76593210067f65d9110006be53d91200057f73d9510007b76150540006ec725911005ebe425932103dbd7690b41006ac62509400067d6550b21004ff764854001cfe731894003ef664505100067c6519120006be761912000cfe76d812105eee32189400067f6510910006bc531912003e7d425974003ebf6190941006dd54d8d4107ef641d854005cff751894103fb44150941006f53158442006bd63d912005e7f645972127e7f415972100cf870591210067e72d9510006be40d9121006be32191201de7f20d95100aff0704851001cfe73d89100067c72d9510024fc755912019f77535051005f6c215972105cfc725824200cff7658321005ec725814100df476485102173d5350540005bd744874005cff75189401de7d10d9510014ff70189100067c43d95100067e7359721024f
  | 8 => 0x2067f10d952003ebe64109210067c6558141006ef629894005e7f205972100cfc764852001cdc7359121156be30d912027e7d1059721004fd73d912105e7c4259721015be711094103fb76150740006bd32d91200067d53d9121006bd51d912015ef64158642116ed211894114d7c755814205fe632c8521004fd749891005ebc645932103eef4298b4105fae52d0a42006bd6290b41024fc75587420063c651912003eef4258b41006f731d85201e67e31d951005cfe72d81410067f53d8540004fd70d932103efb405834200cfc74d81410067f53d912000cfe70d91210067f531894005cfe72d854005eef21189410067d6599321005df735052003e7f435944200cff765824210ebd201912005ede73d93210a57e75c87400057f755052001cfc735911003e7f41597400067c73597400aef86058121017f36050510014fe7198b4003fae72109410067f535891000df4705051000dbe7050b4000cfc70d8542014fc7458b41006be61d912003e7e4059740005f571d091005ebc62d0940004ff73d8940017f3604851032fad52d0a422067e30d95200067c655911003ebf415804203dbe72909411d6bd41d911005cfc76109100067d63d954105e7e42594420067c70d95410067d5318941134ff7059120006dc735891005ef66248510015f671d092105cfc7318910004fd75d8910006dc63d894105ef62198910004fe764854014e7c6550920004fd73989100067c6519110004ff73587420067d43d95410067d535932016def72591201867c65d092003e7e74597400067f72597400067d32d952001cfc7358341004fd7318940004fd73587200067f53d894001cfc73589100063f651912005cff75d9320006bf6450920004ff755832101cfc73d81410dff230505100067d5358742006de52d8d410defa40d8141004ff7158242024fe75d89410067f325972100cfe7690940004ff725874001cfc73d854203faf62909420067f7558910014fc74583411beef20d891005ebc625094022ebd65d05400067c305972100cfe7458740136f810d814203e7d745944205e7c725944231fad5250842305bf7590b410067c63d9520006bf64d09200067e7059442006ef621091000cfe7650920004ff75586420f6fa10583412c79f74d8d411a7b55450510004fd75587402df3c74d9541014fe71593200ddbd71d0540004fd75d81420aff23048510004fd7518910004fd7358642006bf74591210057d73d95412de7c74d95410067f5358720004ff7650910006be42d85420067d7059721006be43d91100067c7059442004fd76d05200067c105944224ebd635074000dbc70d09400067f65d8941004fd75d812103e7c43594420057d75c8540006be75d91202573c7550740007b864c81200079e54d8d41156bc4058242006be52191201e67e41d
  | 9 => 0xf76597212473d53d0940006bf53191200067d315944203ebe7019120006bf745911003e7c4359740004ff7058b410067c65d9120006ec21d8940005ef7258540006de20d8d410067f6598941024fc7558b40004ff70587420067c655852003ebc641091027e7e4159721157ac20d9120004fd735912100cfe705932101cfe73d8542134fd7699320006ec62d0910004ff75d812110ebe6010941006bf64585200357c755891003dee72909420067e20d95410067c6599110006be32d91201de7c20d9510004fd735844200cfd71d8910024fc75587400dfb710507400067f70d95410067d6558321006dc639894101cfe7398b413273f5390942006bf7458910005fb7048740024fc75d8121006de40d8d4105cfe72d9321095fb705911024f3d5350740014bc7458b411f77b53c81200077930d95102bdbd7590941004ff73d854227e7c41597210053d75109412adbf73909411657c75582420057f7559120006dd72d8d41005fb7050540007e4624851003ebc75191200067e40d95410065f75d8d413373f53d0a4200cfe70584422de7f41d954105eec6290941014fe7158242136fa60d814200cfc7498b40004fd755874203cfc74589100067e74d952005ef820583210367e76d9510024fe75d894003fbb6050540004ff75593211de7c40d95100067f3059442006dc60d8d4105edd73d93210067e10594420def86058141174ff7650b210067f65585200067f65d91200067c65d89100067f53d89410067e32d952000cfc701891019fb5435051000cfc7098b410067f32597400067c4359721016f760505100067c73d95100067d715944205ef82058242006be65191200067c60d954110ebe405804226e7c305974003ebc64d05200067e605972103ebe76d094003ebf7019120004ff75d8941006df6398941005bd7090941024fe75d814103dbf7650b400e5dc735894105cff75d93210067d53d8141156bf10d91201de7f40d95102cedc54d8d410079d54d8d4105eee72d932003ef441587420357e759891010eed2018940004fe76c8540016f76048510024fe755834203fb771505401e67c31d9510004ff73d814200cfe7098b41006bc32d91202076c20d9520006f771591210b5dc735912103eef7258b402c6df41d8d410067c74d9520006bd649092100cfc70d894105efb20583210067d5358b4016fe820d092000dfa7010910015f6719094100cfe70d911003ef7715874005ef72158720006df65d8d4104ddc735052005cff73d932003e7d41594421667c6590941006bf6490910004fd73591200067c215974015ef710d912103ebe6419121134fd76509200067f63d95102e67e74d954100dbe70505402de7f71d9541006dc75d8d41006bc63d912003e7d4059740046f661d85200067c32d952026e7e2059740004fd75d8540
  | 10 => 0x9120006f930d81420067d73594420067f65589410047d735944200dbc70509402e67c43d9541004fd73d8520006be73d912001cfe73d85200047f73d95101a774655051005eec21189400067d5358341024fe75587200067e635972100cfc765092005ebc6450b2003ebf605054000cfc705864205cfc73189400c6f710d852000feb62c81201e67d41d95100067f63d95411de7c71d951013ebf41593210067d53591101867c65d09102067f70d9520005df735812105ebf745932103cff7650921014fe74583411ff7865c81201e67e21d9510006bc53d912005d7f765972103ebc6090b4100df870509200aef4764851016eef20d8940007bb64c8120006dc72d8d411e67d21d95101de7c10d951005ebf6450b20156be60909420247e75d932105fac205084204ddc73585200047d751894005eec32189100067c75591210067f705944200cfc7058442116f71058442007bb705054005eee7298b41006bf65191200067c72d95411e67f21d9510006f77158910006ee20d8941004ff735872000cf47648510024fe75d852003e7c4159740006df70d8d4100df8704852003ebd711912023f3d5350940006bf3219120197746548510154bf7650b400067d72d9541014fd72587200073d43d954110ebc30191202de7f74d954105ebf64d0b20004fd70d85420057f75505400067f535864201cfe731891007df970991100dcff7059110015f67110910006bc6119120085dc735054026e7f2059740024fc75593210067e43d9510006bd52d9120004ff73583420067d705944200cff71d89100067f32d954105ebc64d0b2003e7f7459442004ff7358b410063f53d9120005ef7259110216bd6350540014fc7158242004fd76487400067e7459721004fd7690910024fc75d854003e3f4159740004fd765072000cfe70d852005cff7690910014fc715804208d7c75585400073d53d91200067c71d952001cfc73d8142006ef629894100cfe70189412067c72d9520004ff75583420077b65c8120005df73589410067f7558242014fc72d852001cfc735834203cfd72d8142014fe711891013ef641d854200cfe7058642156bd50d9120006bc211912005eee721891005f3d65508421de7d30d951000cfd71d9110136bf405932003fb7611094115cfe7619121024fe7598b41004df735891003cff76509200aef840d8121004fd72d814100cfc76509400067d53d852003f3e6550b402de7c21d954103efb705834200cfa76c81202067f72d9520004fd7358910005f57448510004fd75d9320004ff71583422b73c659094126e7d10597400057f75585200067e7159740005df7350540004df7359121005fb7050720006bd54d91201df7810d95100075f75d8d4103cfe74d8121004fd7598b41005df735912116efa205834205cfc76507200247
  | 11 => 0x17e672c85210067f7359721006be65d912001cfe73580420067d73d95412e67c42d95410067f74597210067c30d954129dbd7510941006bc54d9120015b6719094103dbf73109410057d73d952027f6e2159721004ff7558720014fd74587401c6ed21d891005e7c2059721006fb70591200067e315974000cfc70d8520004ff7358b4003cfc76d09101c6ef21d89100dcfd7699110024fe75189100057d7598941006bc62d05400067f73d954103e7d42594420047d735972103ebf635074005cfc76c8540005bd74c854005cfc7598b4000cff71d9110004fd71d894010fb82019120004ff73d911005dbf76508420dff070505100057f7558941005f5719094103cfe76d9110006be52d91200057d759891000cbc765094005efb20580420067f53d85420067d53d891003ebe711912006ddc735072003cfd7118941176f4315874205cfc739891003e7f42594420057d7359721005f970109102c6dc41d8d4115fb6719094113ef46158542004fd7559321006fb50d8142176bd74d89410067c659891003cbc74589100067d71597401e77641d95100067f31594421de7c70d951003cfd70d854003fb441505400def7105874014e7c655091005ef771584422de7c41d9541005bf7458520024fe75d8142006de65d8d410063c65d912005eef2018940004ff7359320006dc63589412fdbd7390b410067f53d9321024fe7559321007ac6290941155be7619120006df63589410067c40597210067f65d0520014fe725932105efb7058042014fe71583420057f75591210047d75d9321006bd43d9120006ed62189100067d5358740014fe71d9120006f771591100357c7559110135f870585420067f6590910014fc71189400067f735974005cfc7598b4105e7e751894005cfe76d072003e7e415974010ebd1019120135bd7490940006f761505400047f755912105cff76c87400067f43d95101a77475505100067c63d95410067d53580422c6dd10d8d4114e7c655094101cfc73d89410067f5358742014fe76d85400c4ff7158910004ff735864201cfe73591212c6df71d8d411acfe76c85200057d75c87400057f755072027e7e315972110ebf2019120005bc74581213173d5350842005df73507200067f53d93201de7d71d9510004fd755932003ebc64109200067c73d954101cfe73582422cedc42d8d410ed7e759894103dbf725094027e7c3159721004ff7058642015f77450510006bc65191200dfb5405051001cfe73d8940005df735854015cfe76109210e6de74d8d410067d43d952000cfc76d09202de7d10d95412067d20d952010ebe2019120006bf6499110004ff73d852001cfe73584420067e72597400063f65d912003eef4298b40014fc71d932005cfc72d91200aefa60d81211e67e71d95100057f75589400557e759
  | 12 => 0xf73d91210067f74d9520006bf42582422179c73505400067f5398b40005f77150921005f7715094103ef771587420065c65d8d41004ff7650720156bd72d91200067d5358442004ff73583410067d70d954103cff765911026e7c2059740015f672c8521006ec625094105cfc7398b40004fd75580422de7e41d954127e7f7159721156be20d9120024fe75584422de7e31d954119f755350510006df75d8d410057f75585400067f32d95201de7e70d951005cfc7398b41004bf7650842004ff73d9120006bf53d91202067c30d952027e7c105972102ddc7358910004ff75d85201bcfe76189100067f53d911027e7d415972105ebf4298b400047f755874203fbb605094000cfc70d91210067f10594420067f5359121006bd7690b41004fd75189400067c61d952003efb40583410067c73d952005cff7398b4018f755348510004fd7558720006be625074027e7e7159721004fd701894105cfc75d93200247e759891005ebc425932127e7d215972105ef461586420aefa10d812100dbe70507400067c75582421de7f30d95100def820d8141006bf64d052005ebe6250b40156bc70d912015fb71090941004fd75d85420057f75589100557e751092027e7e2159721004ff7458720006bc4359321004fc765052005e7f215972103dbc745824205e7c325944201cfe735834105dbe72909420067e305944203ebc64d09210067c21d9520007bb7050940004fd755844203e7f4059740004fe7650910004fd70d894103cfd71d81410e6de76d8d410067c74d9510004ff7158b400067c705972103cfd7018940006bd73d91201de7e10d951003ebd7519120085dc735854001cfc7359320014fc7158b4005ef7215864203fb7715074010ebe4018940004fd7198b402c6de41d8d4120d7e76d9520006ef72591210067d32594422067d40d95202c6dd74d8d41005f571d0921004ff7058442016be61d0540024fc75d9120156bf70d91200067e435972105dbf7250842176f6215874205cfc75d9321024fe7558910004fd75d91100067f65591100067c65589100067d72d95100067c315974005fae62508420067d305972103e7c4259740004fd7358042005df7359110006bf64991212df3f74d95412067e20d952005ebe42593200c6fa10583212a73d53909410075c65d8d410067f651911005ebe7498b40004fd765091003dbe7448740004ff75d8542007b4425051001cfe7358321007b7645051013cfd76d0b21006dc70d8d41004ff75d894000df87050940216bf63505400067f5398b41004fd751894100cfc70189410557c755912005cfc73d932105cfc72583410067f5358b41015be7190b4110dbc70508420079f73505401e67d31d95100073f755054015ebd41d9121004fd73d8941004fc76509101067c65d05202067e40d9520
  | 13 => 0x21120042f819e02e0960230070050000db2d901a0010000070033bd02f01900001202604e00100200200001b0f00010b000201300613c00100300003700000b00b00302f00701f00c03e00001e01a09900000000000e00500002f1db06b2f100200015b00854100500201100900a00231604000c01705100010504700200e02701a07001100e02d00c00400502907000000206e00001d00000500a47514a00a00000500249700a00801000c00e00003000802400d0b706f0a900901a09702000900601b00c00200c00f0a200700000000400900700106f06701002001d02100102c00001c05a04102101101e00d00506900c10d0540920a70010040072991780020050180000860120050a100a0091160010080000860a20040f804900000501a00429000200000d0030011c70550b40cd00002b01f00002200401901c00200000000100f44400000302c00506600305f3700030000010ca00000402c2f300002100700106e00105200a00202a00407600000700000302600056b00200000000700205a00300502200c07500100415b00000f00400202e00604204500002400000100000003801000000300600500000103b00101800115801507301601a0aa00a00701402701b00c01500005900000200001f0460ff0020020000000000a700000201b02200a0060080110060040570420d600c00600001600003b02300c00901703105802300c00700000d00f1ce02002000900606200a00e00003c03100004e00000b04f08400e0000020192a500400c09b0140010712a500003f0ca00003804400100000004601502400702c00000104d01500001600403400100100101400d01600900302108800300503c0ba0080031c10001ac09c09d00b2ad00201418f05c01600602f00800e00100100001212c00001102c00001400200c00209c01601c49300003b00400500500000801f0f31620630110010010b201004002701003300005e00003200000106a3c207201d0011980330280022810320050470020640050060000c20b502300b00000100049002700007801b00a00507000a00600300100000500d07204c03e15e01205903700202e0c503001c00a06206500000101000801a01901900e01000101d02200603604700300500101900c02a00002700307a02e01e00707400401d00700405004109c53101200000c02500c00101003c00600b00328e0000090820040c800001600101708c00903100d017b7745051013ef621d854203cfe76d912000cfc7458b40024fc75587201aeed2018910004ff7258341156bd40d9120145dc7358542017e772485100067f53189102c6dc71d8d41006bc21d912000cfc7059321006be311912003ebc4058042024fe75d932100dbe70d054003ebc64509211de7f71d95100047f75582422077820d9520004f
  | 14 => 0x50310251780e30180170040d600800103601701700032201500702601d0ac05400200b01d00107500000003c0030010020190060000ed00200201100704f00600300106701f0210330262fb02f0020150001180410030000800063110000030130310640160050091640080d200106200100300501d09602103101706b05529501800202a00002f00a00001500324917a02d0160000a500200400169400706301700400000a02000301d0000622a10020254bc00802d01900000003103327500d04300045e00d01311103124629400200407101e01500000002200000000700301302800a00000600101b1140be02102
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd68205d442480b90fd0e3aac3a10031bdd472591100051ec2062b2884008be8714764480018bee7a9ac89080317dce73597400043fc2aeda122000c3d741d3654800147b0a18ec8900031e1c065589410062eb9ec7b2a822acb870d91424800147d0b318c89000317d9573989410063a40ae6b2e807fc3c7454d62d04014eb02202cb908021fe15765072005c5e422e6b0e846ac3f41dcd65108078bce6a9ec8900028fa1221d952000716a98c4a128000c5f7358d65c84014bf0ab86c6a0803171cc65581410054ec1ee3b224069a3d8594c64480774eb02396ca881ca8fa1865191200043fc2ae6b222000c3c7519161480011bb0e286c6a08021fa1f53591100061e3aec8a0a4000e59534c3605080f17908bb0848800297a0e70d95412dd3b408e1b2a8200a3d8319764481074bd0c32ec6a080e3720d76109100053a40ae6b2e800087d85dc164c840147d0b990c89002f3a18970909400045ec38c5a0a8000a3f8558c64480078b8e6a9ac8908021fe1d53d93210062eb9ec7b2a20008de871cd644400f47d09392cba00028fa1031d95200043f43e65b2a2086e1d8418f65504fd93ae831cc4a08028fa1432191200045fc22eab122000aae8718942500090f90fa9ac88801e8f21173594420043f43ecab1282588dc86dcd605040187ee9baac1210024fe1f65109410043f43aa6b122000c5f85dcd644400147b08082ca210029760c70594420043f436e7b2a200b8ec825cc62440150fb0fb2884901729d60470d95410062fc1ae7b2a2058ad681dcb63504010ff0ea9cc488003171cc65591100062eb98e7b2a4000c6c751c964440018beeab86c6a08030fe1173597400051ec286232240008de87083635040f1eb03b9ec4a08021fa1c43d95200043fc2ae6b0e8400c5f751cd64484010fd0e196caa09021fa1f32d952005e74312e02122007a3e848c5651080147d0a39ec890003174c373d95100243e42ae0312822aaba800c7644800147b0b98ec8900028fa1263d95200043ec3cc7b2a400487c855c762500018d8ebb92c8900030f5d764109200046f438e6b12207ba3f845cd65d00d18eae3a98c4880029be0963d95100061fba6a6b122000e1f8354f64480010fd0e3aac890003175cf30594420043fc2ae6b048400c3d53dd9421080147b06328c8900063d21971d09100055bc0ac7b22403bc7476d9541440174dd0418aca210021f21975109100043f438cab224000e2f65d8a425040517908baac5a08021fa1f32597400243f42ee0b2642008fb805d5644800147b07b2ec8902030f5d353d894100556c1063b224000c6d721cb655044357100b2084909b3874c153191203461f3a6a73168000ab48158f6448001a3aebb1884a08121fa1776509102cd4f426e5b1a820b8be8790d64c84794f301b96ca8800333dcc7259110
  | 1 => 0xd0da98c8900022fe1d64109210052ec2ce1b1a820b8f8874c160108090f90ab84c5a0962a761070d8d410ec3ec38c7b2a820087d87ccb65504b7a6ce3b2c84a08030f19474589100243fc3ec7b2a2000e2f5318942500010f90ea9ac8880021fe1f65109100046f438c6b028200c5d7354e62d040155d04188c8900121f21573582420052f42cebb1a8203c5c7354d64440010ff0eb1ecaa08021f61f315944203d1f42462b2e8007a3e849c56510801c38c7a1ecaa08029760c75582420243e42ae6b122000a3f8458f65440010f90ea9ac3a10030fd4f76508420062f3a8c731282078be878846448017c5b0a31284a01af2bdc86458520006363aee4b22200087e8754d64440018bae6982ca210021fe1d63d951003e5a322e22122003c5e7354f64c80018b8ea31ac0a08021fa1c31597400070eb2ee6a0e80038dc835d942440011ef02b9ac8900021fa1f53591200056ac0841b1a8200c5c73d9564440010fd0e39eca8802e3d21d315844205d37414c6b2e420087e8790f654400153d063aec8900030f5d464c852043d37c12e0b288400ce872dc164440090ff0fa9ec9908021fa1c75591100053741062b2e8000c5f65dcd62504018f0ea382c8908031d60773d95100043fc32e6b2e4200c5f7354d61c80018b8cbb9ac4880021f21f655052003d1f42620b288400c5f835cf65504090fd0dbaac2900032e18074581213ae1f3b6ca3224000a77815cd65d00078b8e6a9ac22114a8f61271594420051f42cc7b22400087e87d9564480018ed03b9eca880028f61473d91200052f42841b1a820087d87cc365504018bf06b9aca210031e54f70591210065c3a6e0b122059a9e8408363504b35ab02386c6a08031de0573597400243f43eeab0484018f4865c442440018b8e632ac29000237a1c73591210046f438a1b1a8207a3e840c565d00078bce6a98c4880034e1c375505400043fc2ae3b12800093d835d442504010fd0e182ca210021fa1d535912000667b9ee4b222000ae58108362504010ff0ab84c5a08021fa1c31594420051e422c7b2a20008bd8714464480010fb0fb28848801e8fa12715974001e2e39ea6b224200c5d731cf655040193ee9b9ac48801e8fa10105944200667b1ee4b028268c3d74d4c62500071b906baac4880028fa1732d91200043ec3aa6312800487e85dc562d000147f08982ca210121fe1f63d95200051fc2ac7b224000c3c75d9161480018f0cbb82c4a081e8fa1221597400066c398e0b2242078bc845cd62440071bd073b282900021f60f755874203c5f438a23224000c5f75dc363504010fd0dbaa82900121fa1f75591100064e3a0e6b12202a8be87887644800147d0a196c8900021f61d65c87400053cc0062b2884008bf845cd644800117b0e28ec89000297a1672d8d410062fb2ee6b02820b
  | 2 => 0xd64191213463c386a6b224258ad68108363504090f90abb484881e68f61271597400051ec2c87b224000c5d73d8f654800337100ba243a0162a761372d8d410043f43c87b2a40008bd878846448001878ea3a2c4882030f1d35358b410062fb2ee6a0a4000c7b53dc164484018b8ebb1ac4a0802ada1a42505100051f42ce7b22400087e870c7654800157300188c8900021f61c32d951001e2e39ea6b222000c5d7354f64c84010fd0e32ac0a08021f61c32d95410062fb2ee6b122000a5d839c365504051e902b9ac8900034718d75109410051e432a6322406ec3e76d4c644805517f0cb8485a08023ee0173591212dc3e436eab02823ba75811d365440014f700b92cba00021fe1576d05200049fc2ae12128200c6f651c9605040517908b9ac5a081f0f19175991200045ec3c43b224059cd476dcd41440090f90abb682900029e60031597400051e42ac83224000c5f305cd65d0001c6902b2a83a000317dcd53589100045fc22e6b1220078be870c464480031f50fb82c488002ba20162189410051ec28c6322400087d83dd560908010fd0e32ac2901f29b60a73597210054ec2041b1a8200c5f7354f60484018bd0e3aec6a08031761c63d95410062fb2ee6b0a40008fb805d5644840187eebb22c2900021f61c31594420062eb9e60b2e4258a9c86553635040187cea326429000f171cd53d81210043f43ecab222000aad84083625040193ee839ac888002ab21162189100062fba8c6b028284a5e85997635040147b0818acba00021f61f32597400062e3aee6b122000c5c65dcd605040147d0da9ec8900062f21974c85400055cc0664322403ca78864c365440014b90ab96c6a08121fe1f53189400052ec2ce5b1a82028bc845db41480090f90b3b084880031721773591210071bb28c8a0a2000c5c85dcd62440018deebb92c8880021fa1d53587420070e31a87b2a82218bc8750960108010fd0f21acb908021fa1c73597210043f43865b2a200087e87cc165c8401c38cb2a6c6a080a6de1d71909410043f438e7b2a4058c9e76d8e42504ef55f08b10c4a01ab0fd07735974000c5e432e890a806aa3e8514c64480b766902a1ecaa08022fe1d65191200051ec2063b2a403ba7a801d365440018b8cbb9ac8880029e60031d95200243e42ae1b224200c7b751c164484090ff0fa9cc48806a1fa1f32597210043fc2ae031282008dd8708363504018f0ebb82c8909db1bdc865591200046fc1aec2122021aba80cc864480171d904bb084880121f21576d09100061e32ee8b0a4000a6c8558862500014dd0418eca901b70f9d953191200063dbaee0b224200c5d30dcf65480cf8f0e0a9ac8908021f61c43597210061fba8c8b0a4088a3f845c165108010fb0e182ca2100f171cd53d81410243f43ac6b2e4200c3d75d93214800147
  | 3 => 0x4b2e800487c851d941480014bd06382cb9080317dcf53589100043ec3887b2a2040e6b62d9720480018f0ebb82c890003175cd30597210043f438cab12200087e8710f654400187cebb20849006a1fa1e63597210243e43ea6b2242028be87d9141480018bee731acb908033a18072581410243f436eab122058ad6811c3635040d0fb0e31eca880029d60420d95412dd1ec20e1b2a8200a5e859c36350401a6e20ba884a08038e19464c81200047bc0ae6b122000cd873dc164484350f90cbae42900031b194725814101c5fc3a87b224000c9f64dcd614800117b0e18ec89001e8f211305944210c5e432e02128200a3d8359541d000556d03b2282900f29da0472d95100062e3aee6b2242008ef8758862500b3938c9b9a82900031de0573594420062fb9aa6b2242018f8805d564484018f2eba86c0a11c38b880651912001c7dc3a61b028400c5f73cc365504010fb0f39ecaa08030fdd774591202de1f3b6cb21282008bf845d942440090fd0fbaac3a11728fa1020d95411e53cc00e7b2a20008ef825d5644400187eca3a2c4880030f9d764991200063a40ae6b2884028bd84dc961d00018bce7b2cc4a080aada0662507400062eb98c7b2a8200e1f5394c64480018beebb1ac4a08022fa1c64585200046ec3ccbb1a82008be870c764480b747b0839ecaa080297a0e60d954105c76412ea3128000a3f8458f65480018bf0bb9ac890803175cd53d91200243f42eeca0a4000a3e85984644804357100a90c890217179db65d8d4134e1fa0ae6b288400c6f65dc960504018bb0ab9ec9908028fa1643d91200061ebaec9322400087e870c165c84018baebb1cc4a080297a1b75d8d410043e43aa6b04840087d87d4e624400147d0a188c890002ae60031d912000cdc402e890a80008ef825d9424400147b0b39ec8900021fa1d53582420043f43ea6b122000a3e850c764480014790ca9ec8900121f21f53587420055741063b224000abb8054864480018bee739acb908028fa1443d91200061e3aee8b2240038de87dcd62440010ff0eb2e43a000317d9773591100064e326e6b0a400087d85dd9424400187eca3a2c29000a2fa1f64507200043fc1aeb3122007a3c845cd65d00018bee6a9ac3a00121f21576507200043fc1aebb264200c6c651c964440b3c3ca9aa6c6a08021f61676505200043fc2ae6b224200a5d831c165c84018bee6a9ac8880031719773589410051f42ee3b224000a3f85590644800187cebb2642900ee9ea0372d951001c6e41aeab22420087d8798f65440014d904b1eca880021f21d53591200043ec3c87b2a820487c855cd61d089b4f100b92cba00031719573989410051ec28c7b224069c3c7454d6244001cb0c6986ca88002a720d641911000666318e4b02826987d879cd65108010fb0e182cb908022fe1
  | 4 => 0x14400147b0b318c8900021f61d539891000c7c402eab168207a3e848c965d00010fd0f98aca2101e8fa1071597400061fba4e8b2e4200a3d8598f644800117d0fb22c290086ae20142580420051ec2cc2322400087d87cc1651087b8eae2328c4880031d20573597211e53b40ee7b2a2000c3c65dd1624400153d07b8ec89000f179cd5398b410245fc3aa9b22400087d8798f65504011df04b9ac4880028f61020d95410243f43eeab12200087e87cc7654800127f0ab8485a080317dce73594420043f43aa6b22420487c87d4d62440018b8ea39ac88816e9da0420d95412551e43acaa0e80038ef874cb625000187eea3a2c48800f171cd53587400051f424c3b2a400087f865d721d00df55b05318c89000a3e60375d89100046fc1aeab122000a3c86d4f64480e1c5840328c8900023be1d62189410051ec28c4a0a80008bf865d121d00018bae631eca900028fa1661d912038e1f3b0ca3224000c6f651c964440014e902b9aca210121f21f535912005d36412e0b28840087d879cf6548001c3ce6a9ec8900021f61f30597210062f3b0ebb1a8200acc8358862440014db0418aca210021fe15765091000637b94e4b2e800087d87ccb65440010fb07baac89001f2d1da42505100046fc3acbb1a8200a3e8518c6448001c38e6b2a83a01ab0f1d353589102dd1ec26e5b2a820087f855cd62440051f10cb80848802f938ca63597210243e42ae6b224000c6c65dc96444001c6f02b2a83a00021f61f315974000477c3ac431220008dd839d941480018bee7a9ac8880033adc8705912103c5e422eab12200487e86dd560504b1938edb9a82a000f171cd535872039d57c12ca3224000ab581103644840517b09baec4a08031b54c72591100062fbaee6b224200a5e871d763504e947d0b328c8900021f61c20d95410066db1ee0b1282008de8718d625040127f06ba884a08029d20563d95200066c386c6b12820ba6e829cd65c84171d904b9ac8881728fa1070d95410062eba8ebb1a8200b358510941440018b8e632ac4880021fa1c32597400051ec2464b2e80038de86dcd6050401998c7b92c0a08031b5c872d95100043ec3ea63128000c5f75dcd62440010fd0e3aac1210028f612315944203e1fb0aea2128281e1d8419763504014790da98c8900022fe1175591200243e42ae6b22420087f855da42440d50fd0e39acba000356dcd30d95100054ec18ebb224000a77815cd651080193ec9b9a829000387d4e53d91200064fba0e6b122070e382019464480071b906baac888003175cf53d93210046fc1aeca12205ac9d7418f625040187aebaa6c8900032b1d372589100045ec3cc632240008bd870c464480078bce6a9cc5a00021fa1f535874200477c12eab224000a5d8308365504090ff0fb1ecaa0803174c173597403d51ec24e
  | 5 => 0x3271cc64585201dd3d400e7b2a200087e87d9541480090fd0abb643a0002ab612211894036f0f982a7b224000a6d820c765480014790ab1ec89001e2f21970909420062e32ee6b0a4000c5f734c3655040187ee83aac121003351cf71589100043fc3eca2124000c5c85dcd64440b9878c9baa829002a1f61c32d95200043fc2aec2122000cbb741c1644840147d0ca9ec8900028f61221d952000637a98e4b222000c3c75dd162440ff87ae8a9ec4a08928f610715944200c7c402e6b2242028bc845cb61500f1c6a20b2a83a002f2b94b76508420062e39ecab12200baae86d89425000f968ec2128288003179cc659894134e1fa0ae6b2e8000a5c855c36350443970e03224290166b560772d8d410043ec3c87b2a400487c87d4d60908018b8e7b2a829000a2f21176d072003e5d3b0c9902403ca76811d365440010fb07baac88800317e0d73d952000666398e4b222007c3f7159541d00018daa7b92c8880021fa1c755912134e1e422e6b2884029b68790941440010fb07baac8908021fa1f53591210055a40ac6322402487c865d442480018b8ea31ac4a0803271d373589100043ec3e65b2a4000e2f5294b64480014bf0ab96c6a08031e19770509200043f436e7b2a8200e676518921440010fb0e21eca9001e8fa1021597400053bc0ae6b2e4207d37615d4425040536d02b8484a0803175cc73d95100062eb9aa631220038dc835d941c80774eb03b9eca880030f5d074d95100051ec2887b224000a5e8598363504010fb07baac4880032bdc862505400043ec3ce6b2e420087e87ccb655040195ee8392c8881a61f61e735974005c76412eab22200087d85dc562d00018b8e7b2ac2900022f61e65191200043f43ecab12206ce1f3054c64480018bf0bb9ac4880028f61221594420051f43acaa0e805dc3d7419762504010fb0e18eca900028f61231597400043ec3864b2e800487c855d842440071bd0fb9ac8908028f21563191202cd4f420ebb1a8203c5c7354d624400117f0eb20c8880028fa1953191200062fba8e6b22203b87c86dd562440d50fd0e39aca210028f61661d91200047dc02eab16820087d8790d65c84010ff0eb1eca900028fa1271d952003c5e422e6b0084008ef825cd6444001c5ea5290c890003171d473589100053d40062b28840087e87cc365504818f4edb2e409000336dcc70591214162f3b0cbb1a82078bc845d560108010fb0f992ca210028f61271d95200043ec3e64b2e4200c6c65dc960504d387908b9acba00121fa1f75591210062e39ecab128200cdb73dc164484010f90ea9ac4880028fa1463d912027d3a40ae6b2e4207a3e841c565108010fd0e106caa08031b5d752d89400145ec26e7b128200cad52dd942108b947d0839ecaa08121f21576509101565c302e1212845cc7476dd54
  | 6 => 0x155b40ec8a0e400087d870c365504018b8ea39ac8908031b5d752189400066639ee4b2220018f4865c642440019b0c7b82c4a08029761420d8d410062fc1ae6b2e420bc6c825d4625000147b0b996c89001f0f191751092000536c1062b2e800087d879cf65440018ef02b9acb90963659c763909410055bc0ac63224000a3d83d9464480018beebb9ac8880121fa1f75591200045fc3ac83224000c9c73d9141480010fd0e32ac4a080f171cf535891010c5f436e4a0a800087f835d462500090fd0b3b282900021fa1c32d952005f17428c4a128000a3d85dc764480011bf06bb2839000317dd763581413ee4fba0c6b02822aaba80d096090801c3b083aec6a080317dcd53d81412dc3f43c87b2a824da7a800c565d00014bb0b306c6a08032ddc671d91200043f43e60b288400e1e841d763504010f90ea9ac89080317cc373d952000c5f426ec90e8007a3c845c165108010ff0ab9ac8900028f61462d054005e72312e22122059a9e841c363504b7878edbaa82a019f0f9d15398b400070fc1aa63224000c7870d956250401763002128288003171cf655814103d1f42062b28845393c865d442504010fd0e39ecaa0802ae2016419121006b8386eaa0a2000a3d84c41651080147b0a190c89000317dd473589100064e39ec8b0a4000c7b65dc162504010fb0e18acba00921fa1f32594420046f43ec6b028200c5c65dcd41480031e90cba242880021fa1c65591100045fc22e6b222000c5d7354d609080155b04188c8900030f19474585200062e3aec6b02820087e8710d65c84031f50fb82c89080f179cd53d93210051ec2e643224000cb864dc121480018b8ebb9ac8880021fa1f65581411de3a3b6ca90a200087d8754f64c84010ff0ab86c8909029ea0031d95200061fbaec8a0a4000c5e855cf64c840187ecbba2c4880028f61021597400047dc02eca12200087e87d4d60908010fd0f98acba00021fa1c755891001c6f43ee6b222000c5d7354f64c8001998e7b92c4880028f61261d952044d1fc22e6b28840087e87d9561480018beea31ac4a080297a0c705944201e2f39aa6b048400d9870dcd41500014bb07306caa08ab2e9db64c812005d5741486b2642008bf8758c644805557100b2484909728fa1372d95412c54ec20ebb1a820487c855cd644400147b0931eca9000317cc373d951005e57438c4a12802a8be87d0960908cf8eae2a98c4880028f61221597400053bc0ac7b2a400087d87cc765480018bf06b9acba002a1f61c63d95200062eba8c73128200c5e75d8e625040187aea3aec8900030fd9774585200043f43861b2a8200c3f845cd651087b8eae2328c88801f8ddc565507400061fba2a6b122000cad7218b415000155904b20c8880130f1d654d912000637b2ee4b22200087f8754c62500f1c6e20b2a83a
  | 7 => 0x40606400008048080080800004390500400002004028080007a018123dad6008d60806a2f802150aad700003002170e002000058002700001a500000c01800038fa0403c12016020fe1602214804300200300e0a80602000d001824832210180283e0105810104460004200019864030020200e078042581e0101a0804a0b800150060000a0582c2480a1005e7b85204812428320a01e1d81c2980201032220600880e31028008140e80c00882048160080a008100587e00000008000000e38800000000c002060080001e0681e00024360120300c00816038a2000120088800016028048d808320020b80407820288660101e6c002c18060c8960780406092018020203e0b808658001f0160001e58004128043603c18860330000183a488040a01a000100a80006808020460000c0589c198600400200000000000486e000260b802140022f0000f80080000001600404627000308cc040b6230100380c0200000014070440a0000b8061e800000c202000001d81581e08020040ec000000b8020481a598a400000038ec1200005014098180006e018020280404800070b600002042d03e0001d8c60682200006108001402a020540087d87d4f64c84078bce7a9ec9908030fdd774589100043ec2eeca0a404fa768110165c840147d0b98ec89016e8f21943d954136f0e982a7b224000c5f7354d61108014bd06106caa08028f61432d912000667b18e4b0282008be8798941d00011bf06baac890886aea0031191200a51ec20e2b2e8000e4f5294b63504011bd0fb1ac4a08028f21163d95201e53cc00e9b2a2000e1d7354f64480014bd0c3aec6a082a1f61f65c852000637a9ee4b222000c5e76dd763504010ff0fb2e4290003175cc63d95100062e398cab128200c5d7354e62d00010fb0f21eca8801e8fa12215944233e1eba2a63128000a3e85cc4644800147b0b988c890003361c063589410051fc1acaa0e80008df835d56444001cb2a6982c0210021fa1b73d95200
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x5000480040f259835d442504018348420573594420060d210815cd65d000181c8618d75109410060721c7359541d000103c9760d655074000607dd1831d5609080905c985cd5358242
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x6
  | 5 => 0x94c
  | 6 => 0x94e
  | 7 => 0x5
  | 8 => 0x98a
  | 9 => 0x98c
  | 10 => 0x98e
  | 11 => 0x3
  | 12 => 0x150a
  | 13 => 0x150c
  | 14 => 0x150e
  | 15 => 0xa0a
  | 16 => 0xa0c
  | 17 => 0xa0e
  | 18 => 0x180a
  | 19 => 0x180c
  | 20 => 0x180e
  | 21 => 0xb09
  | 22 => 0xb0c
  | 23 => 0xb0e
  | 24 => 0x1549
  | 25 => 0x154c
  | 26 => 0x154e
  | 27 => 0xb89
  | 28 => 0xb8c
  | 29 => 0xb8e
  | 30 => 0x1849
  | 31 => 0x184c
  | 32 => 0x184e
  | 33 => 0x409
  | 34 => 0x40a
  | 35 => 0x40c
  | 36 => 0x40e
  | 37 => 0x160c
  | 38 => 0xd09
  | 39 => 0xd0a
  | 40 => 0xd0c
  | 41 => 0xd0e
  | 42 => 0x1609
  | 43 => 0x160a
  | 44 => 0x160e
  | 45 => 0x1889
  | 46 => 0x188a
  | 47 => 0x188c
  | 48 => 0x188e
  | 49 => 0xb0954
  | 50 => 0xb0956
  | 51 => 0xb8954
  | 52 => 0xb8956
  | 53 => 0x209
  | 54 => 0x8a
  | 55 => 0x1409
  | 56 => 0x128a
  | 57 => 0x1489
  | 58 => 0x130a
  | 59 => 0x14c9
  | 60 => 0x134a
  | 61 => 0x2c9
  | 62 => 0x150994
  | 63 => 0x150996
  | 64 => 0x1649
  | 65 => 0x449
  | 66 => 0xb8a14
  | 67 => 0xb8a16
  | 68 => 0x184a14
  | 69 => 0x184a16
  | 70 => 0x289
  | 71 => 0xd0a14
  | 72 => 0x188a14
  | 73 => 0xb9814
  | 74 => 0xb9816
  | 75 => 0x10a
  | 76 => 0xd1814
  | 77 => 0x1049
  | 78 => 0x154b14
  | 79 => 0xd4a
  | 80 => 0x40b94
  | 81 => 0xb8414
  | 82 => 0x40b96
  | 83 => 0xb8416
  | 84 => 0x160b94
  | 85 => 0xb9614
  | 86 => 0x160b96
  | 87 => 0xb9616
  | 88 => 0x18ca
  | 89 => 0x144d
  | 90 => 0x58a
  | 91 => 0x194a
  | 92 => 0x14cd
  | 93 => 0x74a
  | 94 => 0x161854
  | 95 => 0x185614
  | 96 => 0x185616
  | 97 => 0xd0411
  | 98 => 0xd0414
  | 99 => 0xd0416
  | 100 => 0x160d14
  | 101 => 0x189616
  | 102 => 0x189614
  | 103 => 0xec9
  | 104 => 0x1a49
  | 105 => 0xecd
  | 106 => 0x1a4d
  | 107 => 0x41411
  | 108 => 0xec411
  | 109 => 0xed611
  | 110 => 0x1a5611
  | 111 => 0x40cd1
  | 112 => 0x44411
  | 113 => 0x45611
  | 114 => 0x41651
  | 115 => 0x41a11
  | 116 => 0x40451
  | 117 => 0x165611
  | 118 => 0x45891
  | 119 => 0x41611
  | 120 => 0x104b91
  | 121 => 0x180b96
  | 122 => 0x180d16
  | 123 => 0x181796
  | 124 => 0x154cd6
  | 125 => 0x59312
  | 126 => 0x58d12
  | 127 => 0xeca
  | 128 => 0x1a4a
  | 129 => 0x758d2
  | 130 => 0x74592
  | 131 => 0x18d952
  | 132 => 0x18c752
  | 133 => 0x194592
  | 134 => 0x59952
  | 135 => 0x41296
  | 136 => 0x41316
  | 137 => 0x41796
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1237
  | 6 => 2241
  | 5 => 1011
  | 4 => 8
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
  | 8 => 2*((h/62+packedAt gbK8 (1612+(h % 62)*6) 6) % 62)
  | 7 => 2*((h/482+packedAt gbK7 (45769+(h % 482)*11) 11) % 1237)
  | 6 => 2*((h/754+packedAt gbK6 (107568+(h % 754)*12) 12) % 2241)
  | 5 => 2*((h/351+packedAt gbK5 (59649+(h % 351)*10) 10) % 1011)
  | 4 => 2*((h/9+packedAt gbK4 (560+(h % 9)*3) 3) % 8)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe0f81f03ff81ff0ffc01fff067ee0f89e33cf
  | 1 => 0xfff001ffc0ffe0ff07fffe0019b13f38e3ccfc
  | 2 => 0x3fffe0000fffffff8001fffe1c1c7c703ff0f
  | 3 => 0x3ffffffff0000ffffffe000fe01f807fc0ff0
  | 4 => 0x3ffffffffffff0000000000fffe0007fff000
  | 5 => 0xfc0000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x56028072192909504e4152aa021660588e11c5
  | 1 => 0x9a500096485b28310294d40608b00b28a2c45c
  | 2 => 0xb53200009452aa9002895461418583016e0a
  | 3 => 0x4129d528b20000cce52b0018b601f005540ba0
  | 4 => 0x93ce69cf2ce79c00020c1060ddfa0006fbb000
  | 5 => 0xe000700c30061008c4300180ffedfef0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38881
namespace PEqualNP.Outside.L_meta_38881
open PEqualNP.Outside.L_meta_38881.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat bs3_4_0 (concat bs3_4_96 bs3_4_192)) (concat bs3_4_288 (concat bs3_4_384 bs3_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat bs3_5_0 (concat bs3_5_96 bs3_5_192)) (concat (concat bs3_5_288 bs3_5_384) (concat bs3_5_480 bs3_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := bs3_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 8 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 51 := block_range (n:=51) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1011 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
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
theorem bgb_6_2208 : Interval gbAtlas 6 2208 33 := block_range (n:=33) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2241 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat bgb_6_2016 (concat bgb_6_2112 bgb_6_2208)))))
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
theorem bgb_7_1152 : Interval gbAtlas 7 1152 85 := block_range (n:=85) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1237 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0feeaece8fee0eca0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38881.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.or,[0,4]⟩,⟨.and,[2,7]⟩,⟨.and,[1,2]⟩,⟨.or,[0,3]⟩,⟨.and,[0,4]⟩,⟨.or,[1,11]⟩,⟨.or,[9,10]⟩,⟨.and,[6,12]⟩,⟨.or,[8,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38881

open PEqualNP.Outside.L_meta_38881 in
theorem PEqualNP.Outside.L_meta_38881 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
