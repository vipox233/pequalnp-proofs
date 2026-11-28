import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40515.Model
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


end PEqualNP.Outside.L_meta_40515.Model

namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
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

def SBf (j : Nat) : Nat := [7, 5, 5, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40515

namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
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
end PEqualNP.Outside.L_meta_40515
namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xd431
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 2 => 0x1fc07f00fffffffe0f81f01f80fffffe4ccff
  | 3 => 0x1fff8000fffc0ffff001ffe000fffc0f8f0f8
  | 4 => 0xfe0000000fffffffffffe000000fffffff00ff
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc2450a1402382180318a31a28e2c5150955c3
  | 2 => 0x5489314656449469606a0d49b125596664cc5d
  | 3 => 0xa930a26b6a890ebaad0496dca249ad94b8f0e8
  | 4 => 0x31a2c58d8d1228d4d6b6c091048e3638df00b6
  | 5 => 0xc1c3060e0e1c30e718c718e1c7003820f6aa00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40515
namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
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
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 1 => 0xe07e07ffffffffe0f81ff0780fffffff9333ff
  | 3 => 0xff8007ffc1ffffff001fff800ffe0fffe3c38f
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60288e390990c24563c
  | 1 => 0x49108a4490a208a06a0a905124a322549130d5
  | 3 => 0x842554890d44954d04952b0249548ca962c30a
  | 4 => 0x1659e7122876de76b6c18a448e79c831fc03e0
  | 5 => 0x1861861c31871b98c719cc67006100c1dba800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40515
namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0xc000300000100004018700000144028004168000afc30fe31ff30fd32ff32fc21fc20fd20ff43fd41ff20fe21fe32fc10fd21fe41ff41fe30fe10fe40fc43ff10ff21fc31ff40fd31ff31fd43fc32fd42fe20fe43fd30fc41fd40de43dd43fd10fc40ff42fc42fe42
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x881de5150efea0a1f750c21bfa9021bd4210bbca7a0df15221ee29287ef4250afca618df54032bfa82657751482fea890f790f30bf29421be54cc2fca420df54342bf2a2617e50043bc8698df55020cfaa287de430c3de41105f54241f7214437e540c6fca6195f94240dea1a837d52843baa2a1f750c41be2a0657f544cafca421ef90640bea9e437c54ccafca3105f54231ee19463de5290efca6185f15230bf284617c54083f440105f54f41de20c81de304c3ba8720e750d42bf29463de4390af8a9105f54e31bea9483dd4390afaa7196f90d43af29e81ed4210afca2197bc8621eea1a21f431086fca6207790e32bf2a6657d500c6f8a4a05f14f21bfa8a61bf43d06fca1105f54e41df2a0637c5050afea610dfd4e20bf29487bd43103f680a06fd0d41aea98837e500cafaa2197b8c832bfa92817c514c2faa8985f95232ef21c43bf4310fbaa4a1dfd4142fb20e437e53106fca3a15f54b10ee29a41ee42087bc86105f15130bf29065dc5150f3a87205fd5210ef282876e52d07bc87a05f94b41dfa1c877f524c2faa221efd0441bfa9287dd434c6baa7a16fd5120f7908437d51d0bea8220f948421bea88417e54443ea8210df54b31eea18217c53c82fca8204f95031efa9a415c53442d8a498df54843f6194437c544c77ea8887794643f619043ec52442fea6a05fd4121be29c417f515037e86a1770c630eea1a41df318c7bca7a1770ca30bea86837c548c7bca6215f94810be29263dd43d06faa121dfd4d41be2a4217e5390efca3985f95030fb188637d51882f8a990774c832df212857e52443bc86a15754c40bfa8a877e5310f7a80205f94e10bfa98417d52106eea2995fd4910bea9e416f52443de40107754243fb988437f52843ee420877d4d10bea9463dd43c877e87205f14e21be2a265de43ccafaa198efd0641bf28c65f421843ba87185f54743bf29e41de310c3ec8388778c531bf28843f7514cbec8210df14f10fd200817d5490afaa8887790c21df21481f541442fea2906f15110eea9885de4390378a8907b88620f799465de53107ba86995f54e21af29e837f54043baa6205f94b31de214817d52102fca418df54830eea1a617e53886fca0215f54d10fa28a41dd53d06faa7887ec4110bf288417d51cc2fca310f750c42bf294837d52903da85907b90920bfaa2417e50102daa4205f94643be28a817c540c7ee6318ef55032bea9681de53d02bea690fd54440dea18877d540c3ba87995f94f21bf28087ec524c6fea918dfd5321cea1e83f521087bc6418f750f20ef21c83ef32887bca4a1dfd4532bea8e65de328c7b86418f750c31bfa9263ec21882f8a8185f94231beaa6657d520c6fca110df94e41af29e85f610443daa5a0df14943fb880217e53883ee82a0f790d20fa28a65de43106faa998f7cc230
  | 1 => 0xd548cbba87887714143aeaa487be40503bc65185f54c40bf286877e54842faa5107750d40efa84875f53483bc8618fd50721bfa82637d54c86fca1087754c41bea88817e529033a87a15fd4f20aea9e81de324cafaa3a07790d30ef21c61dd310c6faa9886f90541ee18861df320cbbaa321fecc230f610841ed320caf8a098df55121dea0883dd43882fca198f7d4143fd180617e53043bc86217b88120ae29a437d52d0efea99877d0e43fd98261dd43cc6fea818dbd4931ee19061de434cbbea4a1df94030bf29e837d53487f240107750e10bea9c6174514cafaa8997714a43bf2a4417d51903ee6390df94041bea8c87de43c86fea6a17e4c030be294217d54c827ea8885f14b10be2a6637c52442f8a7085f95321b6292216d52d06fca5885f54630bf28c637e5410efaa9185754f41eea1a437f548cae8a2907dc8610afa9a213c54482fea81977d4a43bf290857e53903ec8220f750c309eaa6617f544c37882205f94a42bea9461bf43d0afca9985fd4d21ee29a21ed42086fca890efd0842cea1a837c52506faa7107754143bfaa061dc5090efca1215f95132df208817e52d0fbc87a15794c409e2a221bf4290afaa5a0dfd5021beaa441ee42c83ea83885f54442bf28c617c54c42fea710df54343ef218657e54c43dea498df54e10dea1e837d5010ef8a6085f54720bf286837e54086fca6215f95221bf2a6637e528c2fca610d794c41bf28e817d50ccafea8107d4c431bf28465f751482fea9995d94440bfaa4437e53443de64995f94021bea9c81dd5290fee4290df54232fb28e857e52cc3bc8621df54632eea1841dd438c6faa2186fd0240fb884217e548c7dea4885f55210beaa443bd54cc2fca5a05f14532f729683dd438cbba8621df94d20f6900417d50887bca6207d08410efaa287df300c3ec82885f14141eea1c817c51483bca121e750c40b7290817e5190bbc86a0f714d21fd884217e53d0afca5195f94840be29a83dc5190efca8085f14d20beaa463de318c3bc8690df55120bf2a041be540cafaa02177d4543ef21e215e5310fba87a07dd0641fd904417d5490efca2217790d409f2a6617e5110ef8a810fd94440eea9e817d530437a87a15d54742bf284877d5090bf280205f14c21bea96617d5190afaa6215f55031be282657e510c3ba8710df55010bea9843de43882f8a0a1df55241eea1a85df328cafca3205fd5331f6a1241de43c82fea6905d94742bf288217f53443f220087dc8621bfa9e217d53d02fea9107dcc531bea94877e51103bea321df15232ef21e633e540caf8a4087790e10bf2a2637c5150bdca4206fd0c40bf28063de320c2f8a6107754f42bf290617c54042faa9207d44010bea94437e52082f8a690cf55031beaa0657f53843be86a1ef10840deaa0637d54086fca0106f90840ef21
  | 2 => 0x5bee3680809824000706e000af82c020ea13000338161b8180580803a4c01810088a8191a22702e080380c00e0207a0b00802838070040016cd70300201c0004c00000000260302c001d436822098000409a8d00000800f8800338040283e3a0000080200036048200202c05a64200003f0000e3f8192a800054018000040c080780c826bc0140a81001006000040d8341882a0480601818319b01f8160080804800000260c382038140003672800038161300400000000000001a320360680e078080582c2681e03046090044e0260680000004858000401c02802008140681802b3606812000001c000200265704e0c828000020b0980d010000402101a040a89484a0f16c1781425038048120a00a0003400010078280d802010081d00a190000513400008090000400c2b86a010781702014800170080000606807dd43d0b7e80205f55131af298857e51ccafaa4085f94f40bf29841ed52102eaa2205f54e42bf286437e51106f8a9987790d10dea1a857e54482fca3904f55032bea80437e51907bc8718f750c32bf2a4617f54c82f8a4985f94342bf2a085dd300c3f640905f94241bf2a065ef32086fea898f7d4d21bfa8283ee21486fea2a15f54c41bf290435c53482f8a6a15f95320bf29e217d50107eaa3a15f54610fda0481fa10042fea5885f15321bea92217f53043dc84215f14d40bea86437e53487e86390f750c40bf28863ee210837a87205fd5110bea9e857e51d0efaa9984fd5120bf2a0837d53482f8a8905f94e42bfaa4617c50487ba87985fd5310ef218217d53082f8a8887b48421bf28665de43d06fea790d754c42fb108437c53443ba86a0fb50a21bfa9283ef4290bbe6218df14543be2a2437
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd540c27565084109798c540825f635491097590534871e5350f429758e5444315435474297195434c23f6454231c7551320ca6d6295110c350d521029d63106409718d510839543d0541d55445190f1f6550f41d390f52442f16008410c7590534871c54d4d10a79835450f8d4350920cb150524431d5450c219dd85544cb1d5450e219759643106776154a408f592524423d6494d20d3548320c34c53d49109b58854843c763484218f59053c423d6414e219719543443986050e40d550c514823e6414f109b58a534423c64540219d984548c366525444087590534865d63953109ed81544ca756115230c798c544431d5450e309d587538825e63d4a10b5d855250f1d5350842b9d95210875753d4520d390e521029d63d02409758e548866e6215331c755143487356115110c798d540cb1f5450f32a7d9543d063e6414c21d390f524c66d62152309718d524425c63546429798e54886db6054943b9591210875643944408f596540cb564314532a7590318c31e5450c42d394e521025e6315010d514f214865e63951209798c54c4395435474297d95310c66d62953109758c544866e65149108f990540c6e661d094297d95300c31c5490d109718d51902776154d208f191508ca9d63108409b58a544c71e5450c209dd85520c25d6590c309b588540c23c6454231a7593300c25e6590d21d954a51103954350510c7152434831c5414d10b3189434ca5d6590c32d350f524431d4394342a7d95431026c6255131b6d815150e6c62546409e181544874d52149439d984548827561150308fd91508cb4d43948408f990520425d6590c409798e540425d6395021cdd5351483595014243b5185320cb1e5450c31b918d210863f6550040a7590310c32d62151209798c54c825d63d4b1097994534865c6550d219798c540c65f635424197d8d5190a5d64d4d20d914a414423f6550c43cdd0d51102e662d0641c754f411066e62150209d984540427b6055131c7150534825c6550d31f10c8310865c6590d209ed95200835553944409d987538831d544c431d590f5148275650c421e350d42c823d6414c20c750e50d065d64d4d219758e54042e5620c42197d95320cb1d63151208f992544431e5450f21d350e52d067561951209b98a544c79b6050e40c7951438871d5450c329758c544425e6590d109758e54842e661d0a428f99254482cc625454397d954310f554394440d354e521026f62544309dd95210869d640c831c7951438c63e6414f20e350d42086e4624c431c550d511025f6355121d354d52d06c46348421d550c514cae56190821b518d21086776550441c798d540c65e6395220d514f514825d63d4a10c755243cc31c5450d10cdd0d51d0a3e6494e10b5586430c71d5490f31cbd0d521025d63951309798e544874c5388521
  | 1 => 0x826f6255131c7550320c71e5350c4097994534831e5450e32d590d511027661951329ed95300c2776155120c7552430c25e6550d209798e53443575314520b958432086d86054543d9d9521086e96008420c7d52434431d5490c329798c544878d4354b41c7990534871e5350f41e550d410875643d4532c754f4210b1d4354b41b998b415065c6354021c7d50534833454d4520d9146204825f6354420d9149414425d63951319b98a544423e6414c10d9d48218431d4394040d914a10443655254440cdd50514827565904218f990538865e63d4b109799453442ad640c821b9d91210871e6395330cd152414431d5450e3197d8d520431e5450c219d185529025e6550d1097d8d52902766115332c750c505066e62949108f994544827761551309758e54c826f6254640d9cc8514cb4e4354840b5d855290ecc6254643d590d51d0a5d6315310d594e51d0b554354440c7553320ca756195132d55445150f354354440b958a210867561153329798c548435543947428fd91524439943900409b594320867465505108fd954210a6f6548421d554d511031d43d49419798e548427b65500408f99252443954350710c7553310c7954394440d9544210831d5350441d350c52442cc6348421b5d855050e6c625464397d8d51902b960d0c409dd85534871d5450c20f150d21086d46150d318f99454443355190440c7d5143482766115030cbd0d52d065e6315130c794d4310e5e6394d209bd954210a3d6494d10a758f401029d640c8309798c540c34d43149319798e544429d6310440c7151438431d4354a408f99053c872c54909208fd95411065c63548109d58654486e56290421b3d895190e776154a439d98654c835543d4532b6582430c2766114c20ba181424838d4394b41f118d210871d5450f209b195424825e6550d218f59352c431f5450d10cd50d51d0b1e5450f30cb50d521039543947429b98a54c42d46154a439bd89544423d6414d21d590c514823d6414c21a7593308c25f63540219758c544825d6590c31c7d51434c755510c430ab59032887946150d41d594e511027461548309d986544835543547429d185544ca756115020a75875450f4f53d49108f59053c831f5450e20ad590310871d5450f109799643482cc624c4318fd91534429d62d5143d354d521031d43d4542d594d51d0b4d4354840bc181414431e5450f20c795143106796584010c7951430423d6494e10c7552320c65e6394d21c798e540c65f6550c4097593534431c63d51209758e524427a6015021d514c514829d6490d42c7d95431025c6354a41c7d51430c2e4614c832c798c544825d63150208f191524426f6254643b51855250e5c6355110d65405050e3d64148109d584530831d4354840cbd53524426e6215010c715353482746154a439758
  | 2 => 0x8100449100c540300311c17018050100d1ac05000031440305c001f4010440a0120b66c2c0002c094d010803545440140100c41004a5020220001e00002008a80443f0101100010040060005e03c0011c32000ba1001202c0000c3403403008019718d529035553947429758e544ca9d6310a40e350e521026c6254430c7151434838d4350a218f990540cb345414520c718f544423d6494e209bd95320ca5d63152109758e548825e6315120d9908514831d4314142c7551430c65d63950209798c54882796014c218f99352c426d62150109e181544c66c6254d109dd85524431d435444097d8d529066e62d4e10b51855050f4e5394b41e550d511023d6414f21ad59031c86776544010c7d5143cc63c6454d109e181544cb2d5290840d914b314c65e6395310e5d85435067b6055121c7d9543d0a5d6590c42b9181210874e53548409b588530431d5450f309d185544823d6414c1097d9543106e46244010e350d521025f6355110e690d401027461551309dd95310c65e63950219758c54c86756115220c7d51434c26e62150308f592530c35543d452097590534834e4354b419758c54c825f6354242c795143c426c6255110c798d54cc23e6494e209bd89534425e6314810cb15352442e66348421c7951434863f6454021b31895050f1f54d4d209bd89534876542145209b58b538425e63150219b189544c3555354742c750d51d0a5c6590d10c7151434c31d4354640b61815250e5e6315032b6181434c29d6490c409b988530429f6550f42d314a314c6e46148020d354e52d065d63152208f992534823e6494d1097195434836552084109798e54082cf62545439758c540434f53149109798e54c825c6590d21c7d51438431d5450e32d994a511026e6215210d394d52d065e631511097d954310a9d6490d419758e54c871d5490f32c755143c87563214532c7552430c63c6454d209bd89544c31d63151109e580540878c6250d429798e54c863e6414d219b58a54486cd6290c32c7d50534432d4354b419798c54887564394742c7d51434cb8f6250d429d986534825e6315321d594d511025d63152219718d544827b65440109b58854cc78d43d09428fd91534831f54d4d1097195434ca9d6414d219bd95200825e63949109758e544865d63951209e980530865f63551209718d5090a3e6414c209d586534834d5214a439758c540869d640ca30e550d41c874e4314910c7551430434d4354b41c7d8f544432f5414910c7d8f544827661150208f992530c2cf62541439718d544866e6294d109b988548c34e4394b41f190d210866d65908219718d509070d4354b419d185534834c5314910c798e540ca756195320c7951430cb4d43d49319758c520431f5490d2097590534429d640ca31d390c524c63d6595031c7151438
  | 3 => 0x27164010044200475008211007a07c140a4000087e000240380322d510840000402030000284f00010248d90a874025140100001001000001f84000495004000000a32c0000c060380010c0e22401050062140b0000a000060200002400130040ac6a134080006902469918001f80a03022380000c43601c021680903001000010004f004053840504d635f40000004326410241a254a801c010344512015098193180e224020340100c610a002044000441403c01000b300001038
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x45d8562742900a8c08a02000011c0c380380c5110278b8110054f054354a5110247b92c3aa287511c95114643d0ac81906210d0d721514384270382c890843541c15114543c28caa1a82886867418d2108642ba0c69084325dc562d5143c2ac6b08a88841d7418d5108382a1a8428a41315d06348421a90e4a80a0a1d44735442108344a18c0a1241431d54350920a28eaa1a828851571951434866239ac321043511cd5208410c1aa83126218e1564544310c2b03828428a41615d0320c421a2ae829e4290cc47650d210866239ac520843071d95450d21a8ce7a9043085157195143c8306aa2c521865075d06354810a1ae829c4290d157115143882a4382a429287461c15450d21d0ae831a4210cc67398d21086a238aa419061311cd6448421cc0a4302828860d64548320c30aaa0c299065435ca5450f10988e2b14861948d7418d21086a23928628a65311da4348421c1a87b12a3205447150c524c6a2392a228a87311c96190c31c2a87b0aa520691431814144342a1cc5a0a838358d6215120a1ae52a28690f05431494144382a1aa4a8881615d0634842192ae831a4210c1d7498f5284382a1ca4a8881a15914348421aa0e2a80a0a1e85439874250b0aaa2c321863831954350920a88e4a886218544715485290e52ba0c690843511c55214943
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x30000006300000000701809a088550c6050920c05641c9510c430905849cf5208610905841cd5108420d01431c14214520e01431486050510c05541c56290c32a108550c6050510905841cd5208410c05541c96190c31884875914348421a80805914348421c05641c5520c830
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => 2*((h/28+packedAt s3K6 (672+(h % 28)*6) 6) % 42)
  | 5 => 2*((h/254+packedAt s3K5 (18873+(h % 254)*10) 10) % 699)
  | 4 => 2*((h/229+packedAt s3K4 (23788+(h % 229)*10) 10) % 626)
  | 3 => 2*((h/32+packedAt s3K3 (3675+(h % 32)*7) 7) % 75)
  | 2 => 2*((h/25+packedAt s3K2 (780+(h % 25)*4) 4) % 13)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffffc07ffff81ffffe0fffff83ff9e3f1ff
  | 1 => 0xf80fe0fff81ffffe0f83ff0f01ffc3fe9cce3f
  | 2 => 0xfff000ffffe07ffff003fff001fffc3f1f0fc7
  | 4 => 0xffffff81fffffc000001ffffc7e00ff8
  | 5 => 0xffffff00000001fffffffffffe000007fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x30a1400470410400318460111c5804482150db
  | 1 => 0x5262894891ca289606a1a90a24aa42928cc62d
  | 2 => 0xa144d2912287512ad042d2a04934a825170b46
  | 4 => 0xc58b1ce245141dcd6b68188891c73307e00db0
  | 5 => 0x60c18c3861861f18c731ccce0062207daa000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e88080eaeaeaeae8e88080eaeaeaeae8e88080eaeaeaeae8e88080eaeaeaeae8e88080eaeaeaeae8e88080eaeaeaeae8e88080eaeaeaeae8e88080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40515
namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x400a00ee32ed32ec21de31ee21dc31
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3886210d914532
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
  | 0 => 0x83fffff80fc1fc1ff0ffc3ffffc1e03d98fe67
  | 1 => 0xfc07e0ffffffffe0ff07fc1c07fffffe6733ff
  | 2 => 0xfff800fff001ffff0007ffe007fe003f87c387
  | 3 => 0xfffffe0ffffff8000007ffffc3f803f8
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x98514808e08a24033028c0a472d122a4885663
  | 1 => 0x9308111250080a051034408914249882330ad
  | 2 => 0x30a2daa243ad4d6d08a5aac125b5053385c386
  | 3 => 0x62c51cc48a286e56aab0228246399623d80350
  | 5 => 0x430610870c318b98ccc633138020180376a800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeacc80cc80eeeaeeeacc80cc80eeeaeeeacc80cc80eeeaeeeacc80cc80eeeaeeeacc80cc80eeeaeeeacc80cc80eeeaeeeacc80cc80eeeaeeeacc80cc80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40515
namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x430000030000021810c00001053d50440570c2fc21ff31fd10fd32fc31fe30fd30fd41ff40fc40ff42fc32ff32ff30fa30fd20fc20fe21ff20f930fc43fe32fe42fe40fd21fc10ff43fd42fe10ff10fe43fc30fd43ff21fc41fe41ff41fe31fc42fd40fe20fd31
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x461f9524c3dc64195f94221bc282837c53507788420fd84110bea9a21f710043ee4290dfd4542dea0081be42906fca9107e8c310fc28a61fb318c3b863986fd0240f710a43fa50ccbf2a1995f94742fb98c637d53d0af4a0187e4c930fc98621fb314c2faa9997ed5130bd280657e54082f2a7185f54231bf28643f9528c3f261085f54810bea9c437e500c7b86418df94442bfaa2637d540c3f640085fd4f10bf29e43be4350efca690fbd0821bf2a643fa528c2faa6207e8c210bfaa021fb414c2fca720fe8c220bfaa6656c52502f8a498f74c431bfa96217c52503f420085f94441fc98441fb418c2fca6187e8c320bea9221f930c82faa30857d4d41aea9c21dd434c2fea4984f15120fc282837e5310ff680985fd4141dfaa2437c53842faa718df14d40fc200217d54482fea2995fd5330f6990657e518c3f282985fd4e10bf28e41fb428c2f8a8887ed0010fb108437e528cafca121fe14121bf2a6617f54c87f283185f54732bea9441fb408c37e8220fb48421fd2a4617e54486fea690df14d10ee18a617d53907f6a0a16f90a40be2a465f8408c3be8718df95310efa1c87fa328c3f6a0a0fe10130bf28421fa324c2fea9185f151319faa2417f54c82fca6087ed0240fd200817e5310bf0a0a17e94331bea8483be4250af8a818df94030dfa1085da434c3da84215f94341bf280657d54082faa898f754e10bf280817d538c2f2a198df14141fca86637e510c7dc40905f15330dea08837f514c3f680a06f10840bfa9a41f9218c2fea2a1df94242dfa1c87f9214c2daa521fe940319e2a243df53506fca2185f95010f799265de43cc3bc64996fd0f41b7a9283f920082faa890df14910bf29865f95010ff040085f94b43de214837f504cafca5a0fe4c020fca0081ef328cafea098df94d10bfa98437f524c6f8a5885f54720fca8c617c53c42faa3207e8c020beaa4657d5490bbe61186f95031bea9e21db534c2fca5885fd5121beaa4817d528c6fea790fe90a30bf284617c52842faa9105f55330bf2a043fa424c2f4a1995f94f10bf2a0637c514cafca8995fd4943df210837f53502faa598fe14630ed99261ef424cafaa5205f54042efa1a87da314c2faa9185f94343fca1c617e51903da6590fb54831ee218637e508cafca7a17e88530deaa6653e54ccb7e87215794c20fca1a61bd4310efca410dfd4c20bea80437c54043dea4a0f78c730ef21a61dc328c6faa3985f15230fc18c617e52902faa1a15f94021bf28663fa218c3f4a8985f95110f7a12857c5150af2a1996f50c42bf2a465f8314c2fca418f7ccb30fcaa2617d5090afaa198df94e43faa08837d5190af8a9085e54032bf28c657d5190efca5a05b94831bf296637d51102f8a790dfd5032fc10c61df300c2f0a0a15f54f21dfa00817e54483da40107d8c431
  | 1 => 0xc54083ee4310f74c030f6214657f52043f220085fd4142fd984617d5290ff483185fd5130ae29a837d53483f4a0195f94730bf280417d510cbbca6105fd5210dfa18857d5210efca4107e94530fd182217e53107f260887e08310bf28c877c53086f8a890df14142fc19461fa438c2fca5185ed4121bf28c41d9324c3f482985f94010bfaa2215d53103f486987e94630ef190637e52843bca6207ed4630dea1a837d53486fca998df54a10ee21c63f9318c2fca8217714d21ee996617e53903de41105f94f41bea9681f8324c2fca7907ed4930bea8063f9314c3f460905f94843bf288657e53d02faa8995f95040bf28481fa20083f460086f90140bea84877d54906fca4197ed4530beaa6437c548c77e8621fed5230bf29c85f5310c7de85107e4c120bf29483f930043ba8621df54c21bea80837c54c86fea810fbc8621f6210417d520c2dea4a05f54e42bf294857e53102fea2a0774c832bf2a6657e53087f6a6985f54442bfaa441be54ccbb8a6a0df94042f7210857c544cbda6490fe8c630be29c437850486faa510fe90230be282653d54ccafaa7907ed0020beaa0655f53487f080107b10932de2a2417d52c42f8a2a05f14543fba0c837f52507d88510fecca30fd18a617d51d0ff48098774c930bfa92817d510837a87217e4c030fd992617d52d0ef8a8197bd0a32eea98417e53083dca418fe50a30bd280877c54c82fca3a05f94b30bf28441ed5290f7885205f14d42bea9683ef21087f284985f94743eea98817e5210afea090df54043fd18061bf43507f2a018fe50230dfa0c83bf54482faa620df94e21fb98a63f9404c2faa921f7cc631bf288437c54882fca3995f94810bf2a641fb50486fea6887d90441bf292217d53902faa9905fd4c10bea8c617e540c2f8a7105f14941b6292837c5250efca9086b50842f7900417f54082fea4885ed4142dea10857c53c82f4a018fb14940fd90c61f95090ef8a690df54a41bea86837d540c6f8a090ef55031df20a837e5190bdc6490df15331f6210437e544c3f0a5185f54620bfa94217c54c42faa7107bd0820be282877e540cafea998df55221fd28487f8434c3f087185f94631bea9081fb214c2fea710de54243f7a14857e51886fca7085f94420bea96617d54c43f0a9185f94841b6a90637a50cc6f8a910dfd4520fda12617d53043f640907e109309faa2437d518cafca910f650d30efa9a43fb10442fea918df55331be2a261f8418c2faa8885f54c42fca8065f8414c2faa918fe10a30bea86877e5290efaa3a05f54841beaa2617e5010efca918df54c20ef194637d51d0bf265185e942439f2a0637d50c87be8618fe94930bf29a41ec52507be65195b94a43bfa9c41ef42886fca518df54831bda8283d8314c3ba87985f14930be29821f521086fca120df95043fcaa
  | 2 => 0x70000100e0882a0903c110100781a00390000060183c0a8060001b06811361560183e220460384a0c16201000071f80300e0900011000090001a800008e6070224f824043d43389a17810000000034a00842050220001c0c010018041001401ba200a36008000900600802020000082e310b01b0060293e0880a0c8080582600020028cc0914a000d6048000d010048420080c20800038000d80c00808af80203062160100e000001680105001002078220007c1b8260404a0f9a200b3800802000120108a330062e80601804020001c000110080780201004280020200815000048552b800028124a000000080b020050000000a0a8a21603200000010081300a4f02400330098005604c0000c0a00822828031880180400014008000180202000000080300000020a90840000e0181e00800000580b02e0583613055df320cafea910f78c531fd906217d50886fca320df54443ae29a437d54843ee21085fd4f20be298417f540c378a890fe15130fd88421f840c82fca820df55010be2a2417e548c2faa518778c130dea1e837d508cbf6a5185f14520ef988637e53882fca1995fd5031fc10a61fb20882fea8905e54031bfaa265ee32c86faa0195f94231be28263ec42882bca7085fd4143beaa043de53843ee82a0f78c530fc29261fb40c42f8a810df94c31fc20621df324c27aa818fd44010bea8861be42102f2a021fed0320bf29081f9514c2f8a2985f94830fda1c617e51042fca1a17bd4940bea9e817d538cabca6205f54e10bf28881fb434c2fca221dfd5310f7294877f53506f8a6905f14810ef218875d53082f8a9995f94041bfa9a857c540c37e85215fd5232fd982617e544c6faa7a0df54332fd280877
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1514c35b534c010ce552500c65d63942219798e50907cb524c9308fd954210b59538c2109b594420867a65d01309d185544c27b60551219798f528425e63150109e98053c873b544c1209e583540c6796314142ab58b4310a3f65500409758c54082cd6290f30c718d540c65f6355121d614d30442d9648c530ab5924210a7a6094c419e58054cca796094d20b698c214c2d960cc4318f9945448679658c010ae993324c23e6414e219e580540c75b53141419d185544ca786055132ce9085050b2d5410820d6183534875a650c5309e98253d07395410010abd954210a7b65506309b58a53d06e86250040da5495090e7a6094d219ed81548cb5a43540439e98053442da60cc9309e980535074f53d4941b658a314c3685214141ae590314c2796094d109758e500433854501309b98854043395494332ba988318c2796094c429e59610042da600c530d6982531023d6414f10ae191524c25e63940109e98354cca7960d503297d8d51c835b534c1209b98853042f36155130da54a500c67b60551319e583548865d6394241b658c548c3c8524c9309b988540c67a650c530da548524c34c53d4941f258a434c338548c120d3588534865c63551219e580540cadb6355130c714f435075853d4121da94a5090e6d62d50309718d5110a7a6094e219b997424ca6f6548421ba58a438c27a60d5031d6d4f50487a942109309ed95214c35860d4d41b658b534c2b964cc9309658c5050b2f5410a209e58f505071c5414d21ab19120083385414121e650d414c25e6315021d354f420827860550219e58054cc7c9620c530ad584421063f6454810ab993328cb5a6054e10bad89514c23e6414c109b58b54c42eb6250530b658c4008359538c010aa1814210a796094c41c7153534867b6550530ae19120082b86454a309758c5050a786054a319b988530863e649512097195434c2bb64549309e580534875a65cc930ae1814210b1d54d0c31bad89404c2eb6255230ba588314c25f6550c439b18954442d96314142d6996434c23c6454910c7d505348678654c1109dd85544ca6e62d5031ab1814210ad963951309ed81534867b6054a319e5825390aae6290d43ba189408c25d6314a109e994324c2796014e21b6995434c3a86050842ae191214c36852d0140cbd0e5290f5a63141429e58c50486d8614c930b6d8d414c27a6014c209758e544867b6054743d64c9500ca786055131f24c9214c26e6294f419e980540c67a6015332b6593534c26f62551319e58c50506786548530bad89544c35a6054c209e594400436a52540319ed81518cb395415230d314c525072e54548319e58253c867a6094c42e650f414c35853d41418f590538863f6454a319e983548875953100209bd89548c32d54108218f191528c2ea6290e309e195404c26d6510820
  | 1 => 0xc2b9640c630cb50c525065f654c4319e982539063e65151209b58854042d963909309758c54882d9600ca31ce951500c63e6494d209d584540cb2e54948318f992530ca7a6014d21d354c420826c654c9218f191534873b54d4121b698f424c2796094d218f19152043395454332d654d30c42776548421e6593324c27960d5321dad4b505067a60d53219e997324c2ac62504419b58b54842786550a309e983540c23d6595031ba189404c37151146309ed8152106e860508429e582544872f4314941ea508428c39b6450d309798f548426d6214f10cbd50428867860552319758c54086b964cca30d6d4f50506786054b43e6d51434c23d6414c10d614c504872c544c9219ed81540867761551309758c54842786054841cb552520c65c6354910ba189548c34f5314941d654e308836952942439b58b540c63e64d4a10bad89418c23e6414c21b658e324c27b6550930c754c42102db644c9309e980540c32d52108419e195218c2796014f218f191534825f63551109b98853c4277654c431cbd954210a5d63148109e9825390b5a6094c20bc185524c2e9620c630b6d8d418c2796014c21b658f214c23d6414c219e58354cc66f6254d10cb548421025e63150209b98b548423d6494c32b6d93324c2af6350842b618d214c35a504c030bad89408c26c6255230da14b505073954540318f99052042786054632b6d8e214c23f6454d2097d95300c2d86350530b6d8d214c2b864486309798e544865f6355131d6d4c50487c8424c9309bd89544867b654863097d95320ca6e62d5330ba98a434c355510c730b6987324c32c52905419b98b54cc65f6354910d694d300825e6394221ce952500c6f36154930b6994314c33954102309798c5050a786550930ae191514c35953900409b189548c6786054743b6d89434c27b60549109e980530867765440108fd91534875953880209718d51d023d64d4a10f24cb214c2d964cc9308f99053c427963d4142f2d89324c26f6255120b6590314c3395415130ab1854210ae862545309e997314c27b6054b43e6990314c33854c8120ba189418c25e63d5321ba189544c23e64951219e98354cc6db648c530d658053506d96310320dc544514c3594354043b258a434c25f63544428f191528c6da63c8530b698c404c27a6095121d654d300825d63d5210b658a434c2da6310d30b6580320c75b60d4d419bd89544c2d96308010aed91218c2ba640c5309798c52842f1618c0108fd91524432d5410a32b658f548c35a6014d219ed8154482786054442d314e32486d960cc631f44c4318c278654c120b358a434c2796094e219e5805350a766115032b658c20c436b5214141ce95250ccada630c930ab191210867a6094c219ed8154442d96490d309e580540865c6354720e6590314c2da63d0130aed9
  | 2 => 0x6c0d000000182800c0c010071cc0100001028000100226c0b005de0180603400008230680e04c06014012a00a00003000313309905020010063d0000300a00c00068160c802010170440a0040006a120000003002038080ac34028050000210800c7d53534866c62550109758f528423e6494d219e9805350a6f62550109e582530867661150209e195414c36b42141429d58454082da65cc930b658c424c2f061551309ed9510042796094f41b618d218c25d63150108f592534823e6414e209e18154486d863506309dd95411075963141429bd95320ca5e63d5020b6d8d218c2da6310930ba189414c2bb6454a309ed81544ca7a60153319b588540c7d3518c530b6984314c25e6315220e650e424c2d96010e31da548528c2bb64485309758f540835a534c320d698053506da6190d30ba58a300827865506308f59352c4299640c5309e58f50486746154d20ced50504866d62d5330d69825384359534c2109e58253d0a7a6014c10b6982434c32c548c9219e181548cada6590d30b6987534c35953c4210b658e10043985450d309798e5348679658c0208fd954310f2d54548319b588530426f6550842b658f424c27b60544429dd85534827b6550040f2d09324c29d640c53097594430c67a6510d3097994534863f6454a30bc185304423f6550441da9495090e3d6414e20f4984314c27b654c030da94a500c6db640c53097d8d51d02796094e41d6d8353486da618c5309798c530833a5454332d6580534869964cc930d654f40082d96010c31a759031cc32c54881209b98b54c425c63551109e181534875b534c1108f99253c863e64d4b10cb1522148759538c020ae990318c2d86150d30d694d30842da6390930cb550424cab46150d418f19153443ca620c530f298a434c2e8624c120b658c40c42796054c10ea10840082e561108219e980540ca9d64cc930da548200427b60552319798c540c25e63148109ed95428c26c62551309e59420042ae64cc9329b58b54cc6c9620c530b918532486da63105308f590520439943109309b189534439a64cc930ced52304835b3254032d654d200826c6255131cb14a40502d96310010ae993328c35b534c220b658c414c2da63d05309e983540cbd0518c5309759653083585314141ead814210b38544c1209b98b540c2d86550d30b6591324c29d64ccb309bd8954442cd620c5308f990540c6ea620c5309e58354ccb5a6054c40d654d30c826f6255231b618e214c2e96290d309e98253c86cd620c7309e98253d0a6f65480209b98b540cad9620c5309e58053506ac6250040ce153504865e63152108f59253486d963085308fd91534425d63d5321d654d40102d963d05309e594400823d6494f21d354a320c67a6015021da549500c71d53908409e980538867b65480209e996434
  | 3 => 0x120330680100800000011201900c0506000000070480a014001602d208070005404c003207f030000043b034012080c0000105c09078000001c0040107400004070b4c10500d0000132c02028bd0103a0040003c0001c120000000008044a2000010140e0d000074000580d0000305000008320180009c2e020071100602c08004160d00c0000c05007000000480303858124070f48f000020000001c270153c0105a0180001c0d018000b0000b4060f4010340101c7e0000300017024190801107400028000040207c0008420004400d4030641200c100000000412018
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x60000000040810000094004828002000000000b020800184000068264003870408000000000a0000004004400300008800010002040000404005cca76d09324c265b92c918a61581c55214930992e5b20629868964988314c32432a6490a614c1d15114530932e931e4298619639085050a643b26490a61701c53248530d12c8b10629852870550428ca9838aa82a261629d3624c930a50e4aa0a8984c9731814210b24b1aa4100214a1d15214930a50e4aa0a9185197018d540c646b98c0a1085a2590424c930c52ca2108010528725504004294382a821265341c5644c930c50a83126090499731814210a943aa84212612a1d1628c020c50a831280984597654c400830c32a86a0a61a250c6250530a48e2aa0849968a731814210a64b94c7a0a61a2991620c530a50eaa1085184a87058b4310b24b1e8428285491c54314941a54e1aa08510d28705504208694392a82046189150614c921b14e5b2286985907150d414c324a9ac518041265da640c530d10c899242985287454820042c4b98c0a10854a1d15214a30952e63028421649625805348665b92c9a9a61225cc6050842932e93186498528705484210744b98c0a1085165ce60d52218b2e6302a810f0953108400830caa2c62a46126dd1628c530d12c6210801056072544514c30c322a690041165cc6054841932e831c429864953189401024dba2c5a9a61865516310010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x90080050610909831c15410821a8081590424c930a08825516310010c087454d628c020909831c15210841909839c35410a21a08825516315230c80641c53248530a808150c6250530a098654c4210020c10651c54350530c40651c53248530c087458d5208010
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
  | 5 => 2*((h/254+packedAt s5K5 (18873+(h % 254)*10) 10) % 699)
  | 4 => 2*((h/257+packedAt s5K4 (23788+(h % 257)*10) 10) % 626)
  | 3 => 2*((h/67+packedAt s5K3 (3675+(h % 67)*7) 7) % 75)
  | 2 => 2*((h/11+packedAt s5K2 (780+(h % 11)*4) 4) % 13)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfc0ffffc07f07f83f07c3f1fff87c07e20fe67
  | 1 => 0xfff01ffffffffffc007fffe0fffffff83f1fff
  | 2 => 0xffffe07ff8007fffff803fff0ff8007fc7e387
  | 3 => 0x7fffff81ffffffc0000fffff87f803f8
  | 4 => 0xffffff80000001fffffffffff0000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa5614544712a9580ba1e0b1595c6454e206e63
  | 1 => 0x824c2089240201400245520228893100b14ad
  | 2 => 0x30c28b1120e348ad528026460b520a62c5a386
  | 3 => 0xa28b1462448a0dca6b4a80148c672c47700350
  | 4 => 0xc30c1843870c71738c733898c0043005bed800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80fce8cc80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40515
namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5005fd3100ff14007fe5200ff04001fd21007f88401ff21017f4c005ff53007fc8003fc40007f90801fe41017f8c801fc4200ff94005fe53007f08405fe4301ff54807fc52007f10407fd5100ff08001ff41017f14c03fe2000ff90003fc30017fcc407ff51007f50801fd41017fcc805fc43007f44007fd50007fc4007fc5400ff84007fe51017f8c401fd40017fd0c01fd2001ffd4807fc5101ffd4005fd43007fd0007fd54007fd0805fc3101ff95005fc32017f4c805ff30017f54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x188417bfd8f21127f864a0833fc6590829fe2984206ffd0e4200ff481a001bff62d0013ff296200cff0cb21005fcc321003be4150401ff30c842fff0c142167fca62101bfe611080ffe300820bff5492004dfacb88043be5450001ff90a4031ff945421afdc65a1002bc6448449ff98a8202bf98d4201df8cb20813fc3144001fe2162001ffd032000ff8218801bfe60d0847fe282820fffd4d4014ffca7a0802fc6250419ff2164011ffd4f400a7fe601080afc63c8001feb12201eff14721007fac12101aff65d04037f3048400ffd9110037f8812108aff6390463fea92842cff4c84201df8cb880c2ff63508073f3288401ff10340047f88788003ff41c4033fe29a4235bf58f42005fec99083ffe63500237eb1e8006bfd8f4103ff8622085fff31c842dffa9c4202bf98d2000ffa819002bfe314803bfe2864203bf99710177fac721007fc2044027ff1804201ff88320007d8851081bfd61d000ffe3048200bf59221187fc86a1002ff6148045fe9948200ff50b2103ffec810802fd6110801de3224200ff985420cff8649089bfe5090429ff9904200bfd8b10027faa688067ff3048419fe3064225ff5514100ffc219001bfc60d08557eb2e8229ff4cb410fff8602087ffc2010401ff10e4006ff5044101dfccaa1097fc52504057f31e4036ffd4742035f8c8880c3fe3150849fe31a8234ff94342007fec0a081bfc61d0003fe2028020ff54c410cffe649086ffe60884537eb1e8206bf99121067fec190816ff6544031ff1824206ffd8f40007fa828801bfe42d000bff28a2001bf18021007f88390803ff60508077f32a4006ff1514100ff8608803bff52c80037eb06401eff55321005fec810807fa10c40077f3284200ff0852000ffea190002bf6448403fd1822009ff59710055fec69000afc63d04637fb2a8430bf59242005fec4a0017fd524400d7fb188207ff9444106ffe8790002fd61c80057e31c840eff54720015fcc7a0053fd31084397fb2c4201fd0431005ff8ca9000e7c6544003ff2024000ffc851000ffe618801ffc5108465ff1048433ff59642047f8a7880afbe401080dfeb2e8001ff4c32000ffc41a0087fd52104017eb204200fb4842105ffea89007bfc54c8401dfb224201ffd0140037fcc1a081ffc65c400dff2a08217fb4cb210dff88110802bf6448001ff314821aff1492103ff8c01089fff5190401feb204200ff9094000ffc6188023ff32c400dffb068219ff4c52101dfccba001bff65d0013ff32e2000ff98540037fcc620803fc6148015fea1a4028ff94341007fa429001bfd4310429ff9884204ff8c510127f862a082bfe4348001ffa164001bf1832100fdc409000e7e6510401fea104219ffcc5210d7f8a29082ffe54480057e31a4013ff1402117ffc80a10b7ff5110803ff1028007ffd8b10
  | 1 => 0x3fe2148417fe2924000ff191210cdfec690877fc10c84057f31e8217ff10f210d7fea0908abfd52d0401bfb2a401cffd522108ffa65a0003fe4148439ff2a4422eff4ca42027fa628801ffe319041dffa8e4026ff9024100ffc218802bfc3248003fe9022031ff1494205ff8a890003ff4208429ffa184208ff98f1002ff8a28801bfc61d08073e32a4000ff18940007fe83908b7bd54108017eb06420cff8c821077dca5900cbfe509080df7a148407ffd942104ffea588083fd3110433ffb1a4206ff50f420affaa0108177c654401f7eb1a8000ff1052018ffaa8a10b3fe3110813fea8e200cffd93210dffca11085bfe5388419fe3288400bfd9121067fca410833ff65c845b7eb288400ff18941037fca9a101bfd65d080fff2084222ff90e41027fe6288072fd658840dfba0a8206ff5084103ffc438801bfe40d0433ff1924206ff950420bffe6190807fd50c400dff21e8401ff14110007f8849085fff32c840dffaa68429ff8c74100ffea18803ffd3250001feb028400ff50910007ec42108abbd54d0435fea82421fff14041035fcc820823fe32c4009fc9822024ffcc141037fec7a1042ff655000dfe2a28406ef95340007fcc4a081afc6448019ffb1e4232ef902420cffa6090897fc515040dfea188401bf98710027f86488023ff43c4025ffa8e8024ffcc941035f8c99081bbc421042ffe98e4207ffd8c4100ffca1a0007be40d002b7eb284224ff14d41036fcca208cfff51908077e32e420dffd4f201affca7a102bfc3148001ffa162006bf98a42007fac29008bfd4390447ff1828201ff08120007fac3210ceff659080bfeaa22000ffd9121005bec690803fc624402bfeb28420cff1082100ffca0a001bbf41104017fb224006bf990211777a872101bfe401080bfe2922000bf58042007fac010803fe62440017eb004201bf9814103ff82010803fd6290403fb0862006fb908420bff8a79083bfd65c802dfe994420cffd97200a7f8861081bfd541040dff21e8206ffd8740087fea2a001bfe549045dff31c8406ef953410effc6190817fc5444015fea9a401aff9492110ff8a4208c3fc31508017f310820dbfd8f20037fea821003ff410840dbeb288401ef90140007fcc810827f551c4003fe206401cffd462119f7ca921003ef4288417ff28a4006ff50f41007f8828800afc6310841fe1908200ff50941037f8cba101bfe4310831fe0824206ff9534101dfccb10803df6348403fe986202bff940421aff8a7a1033fc6090859f71908419ff10d21037fac62101bfc54104017f30e8022ff94e41007fa8290003ff414843d7fb2e4201fe04110187faa6a10d7fc31d080fff20e2000ffd854017ff840a1003ef21084017eb068401ff0c1201affa65a1033ff6390819fe2964202bf98e21037fea9a081ffc63104057f3
  | 2 => 0x4100ffe6090013fc4344001fe2122001bfd8140005fac5a081bfc5410833fe31a4207ff8c621087facaa0007fc10440017eb108221ff9484100ffc81a0003fd62c404bffb2a821effd4b21067fc841081fff65c405d7f310840affcc920057fcc690002ff64c400d7fb1e801eff54721007fe8288003fc21d00077e32a8406ff1084119dfacb210a7fc32d0465ff2048402bf98d41037fcc420833fe32c84057e31a842cfb4c842037fe8220803ff6148003ff9062030ff98d42117faa720803ff218840dfe21a8220bf58c41007fc839081afc65d083dffa864224ff4c5410b7fac71084afd65d0061ff982840cff19720047fea788003fe4248401ff30a4007ffd8f10177fa872101fff65904037fb124006bf9922101dfcca8801bff435040dfeb068202b718d21007fa43a0037fd63c800ffe3044201ff10310177fc872101bff42504057e31a2030ff14d42037fc87a0093fe325040dfea1e8006bfd974019ffea92101bfe54908037eb068034ff0c34209ffc40108bffe305080dffaa68025ff54141037faca208c3ff32508497eb1a8200ff90b1005ffcca900bffc505080ffe32c4218ff8812100ffc80a001bfe54d0001feb0a800affd8d20057fa6290003ff42c841bfe9964000ff58321007f842a003ffd4350045ff31c8236ff54b42005fac3a10c3ff6350815ff98a4010ffd51400f7faa1908c3fc635080dfeb1e822effd4e4200ffe81880c7ff655080ffe3244201ffcc11008ffca7a000afc63d0847ff3028206fd90441007fac8900a7fc31d0417fe28a4006ff98b4100dfec2880bbfe5390849fe9828201ff1412000778c89000efe659041ffe31a8019f718d21015fcc78801ffc64c40077f32a8001fd04110067f84021003fd215000fffb262027ff54a4109ffc20108b3fd5310803ff1822006bf1902107ffc86a001ffc6390451fe1068206ff9514018ffccaa1067ff43484437eb288200ff90541035f8c890813fc5344001fb90c4235ff8c742187fa62a1003fd424802bffa904216bf9842112ffca4a0833ff631084dfe1848207ff19021027fe6488002fd608842bfea88421bff902210bffa6190803bf64480017e30a8020ff14c410a7fa6010896ff6550421fe32a8001ff88310036fccba002bfc6348063fe28a840fff94d4014ffaa7a083eff635003fff1808227ffd5241037f884a0863fe104845bff288842aff9474111ff820a088afe6110419fe300841affd492105ffaa890057ff500844f7eb2c822bff0c042067f8cb9081bfe40d080fffb14820bff59520005fec48800afe63440017eb048206bf19320147f861a0807fd40c4001fe3222000ffd09210d7faa290806fe601040ffe31c4216ff50e210b5fec71085bfe4388419fe3264200ef5084202ffeca8801afe641085bfea908401ff94320067f8859080
  | 3 => 0xeb26400dff90f20047fa658801bfc405046bff98e8401ff84110005fac321002ff615000dbeb2e8034ff14342035feca208b3ff3210839feaa44200ffd8910037fe84a1073fc528841dfea964006ff58b4019ffca321003fe21440017eb048415ffd4421067f841210c3fe3250853fe29e8216ff0ca210377e842106bff5148403fe1068005ff5451007ffaa6a001bfd541080dfe2a68401fb08120005fac5880dbfc52d083bfe2064207ff188411b7fca3a106bff65484057f31c841aff19521107fa602080efe6510823fea9e8000bfd854218ffaa0a101ffc519040d7f322202eff54e42007fc8290012fd63440077e32a2006efd0f4100ffea08801ffc6290435feb2a4212ff9474001dfccb90806fe60d08037e3048406ffd8f410c7fca090803fe6250001ff2128222ffcc6410877aa8a002ffe524801bff18e4000fec8120037fcc5a0003fd429040dfeb2e820cffd9442007f8849001bff65d0861fe982840bbfd9520167fa62210d7fc32d0803ff2064006ff15341037fec3a100afc6308413ffa8e2009bfd971001dfcca20807fc30d00357fb2a4201ff0814000ff8209008afd6390465fe1848424ff98d4101dfcca90806fe608840dff3008208bf58f10015fcc6a0003ff6448001ff90e802dff1444201df8cb2101ffc6308409ffa1a2000bfd894114ffa63a0803ff4148015fe21a4000ffd0910097faa5a0003fc6448009ff1922000ef10a41037fcc3a10cffd529080dfe31e8027ff55241067fc859088ffe2050439fea944200ef90942157f8a3a08c7fe525080fff28c822cffcc44200ffaa088007fe50c40017e30a8406ffd0c4100fec20880d7ed32d080ffe18c4206ffd084115ff8a021003bf419041d7fb2e4020ff8c84100dfec090023fd63c4001fea0a8001ff0c14000df8c1a0843fe51500077f32a8207ff94621037fccba1097ff525045ffe0828406ff10c4110ffaa02081afe6448017f6a924018ff10121075facb90017f55144023ff18e8027ff14a41037f886a1013fe634403bff1064200bb1894100dfcc9a001bfd60d083d7eb2e420cff08720035f8cba08bbfe3190825deaa68001ff4c1100a7fea610812ff6344067deaa48400ffc854006ffca790043fd5250037fe1044215bfd9421175fac7210abfc52d040ffe0808222ff0ca4109ff88010802fd61d002dfea9c4234ff083420d7fcca9088ffe105040dffb168206ff58442007fc828800afc634840fff108422cff0c44200fdc4190022ff63c404dfe104820dff50f20007fa8310833fc61c80057f31e8400ff48720067f8a421077fe10c840dfe2a48203bf194211277e86a0817fe524404bfea8a8201ff8c12007ffc62a003bff54c804bffa82820aff14d2003ffec910803be421040fff2088206bf19310107fe602083bfe54c800ffe3284206ff553
  | 4 => 0x86ffc3088421feaa28027ff94a410bffa65908cffe6590819ffb0e4006ffd0641005fac99081bfc62d040dfba0c822cff4c042015fcc61086bff544840dfea168030bf58d4208ffe63a0067fe43484037fb022019ff50d21067f865900bbff31908017f3162001ff1434000ffc818804ffe5008409ffa9a2001bf181420a7fac61085bff328840dfe214820eff99720197f8a121003fe425080ffe10e200fff4c54014ffa61a083bfc54c8001fe30a8407ff042410a7fca610807fc404402fffa1e4206ff997400d7fca8908d3fe30d0841ffa98820cff94842127fac6a08c7fc655084bdf2a28214ff98c21007fec4a001bfc4390439fe2a44204ffd8d10037f880208c6fd655082dff31c4225ffd45410cffca6908d7ff30d0811fea1e2001ff14140087f8a2a0002df635040dfeb288406ff55340007fcc990007fd5048001feb26202bff0404207ff862a0047fc32d005fff1028400fb1082103ffec110803fd6488455ff296820fffcc540037f88621023fe43c4001fd8822000bf18940037fecba0803fd21c4001fea128001ff84120007fcc98801ffc62c403dffa8e4228ff0434103ff8c7880cffd5490801ffa124012ff14b40007fc8488033fe52c8413ffaa6200bffd49200cffea690893bd4350419fe2948401ff0832001df8caa081bfc549080dfeaa68401bf1824106ff86390023fe53c4017fea8a4009ff95310007ea42108027d6510403ffa022022ff14e41055fac690063fe604842dfe98c4235ffccb42067f8652101bfc43d0445ff9948229ffccb41007dc4290803fe2148001ff3264207ffd96210dff8a110833fc63108037f3024206ff1534003ffec020807fc30c80037f3068201ffd412010ffea42081bfe65d04013fb2a2014ff4c8210075a842101bfc41d000d7e3288201ff8811017ffc20a101ffc518840dff2108200ff98b10087f8a4a0017fe6544001f7a10422ebfd8e4218ffea4a101bfd601085fff302840dff54f20005fac89081bfe63108017eb008200ffd8941037f8cba001bfd63d082dff98c420affd0d2008ff863a001bfd6310445ff9848203bf1972018ffaa2a1052fd630844dff1848206ff58841037fa83a000efc6548453ff9868204ff18d100fffc402081bff435081ffe1928019ff4c92103ff8a220807fd404400ffe32c8200ff507201affa63a1003fd4288451ff186820cffd932002ffea48802bfe3248001feb128001bf9824105ef8ca9001bfc5450063ffa828406ff105400cfdc649086afd654843dff32e420eff9472010ffaa220806fe6050819ff90e402cffcc04200ffa6090006fc60d0843ffa80821fff84041035fcc990897fe6550449ffa9a82039f9974006dfac7900b3fc531086dfe28e8407ffd8e4115ffc6021003ec625042fffa9e4228ff143410377e8621003fd6448401f
  | 5 => 0x8f2018ffea2a10affe2010819ffb04840cffc84210d7fca29080afc63d002d7eb1c4207ff0c71000df8c11084ffe600840177b128222ff4c641067f86421037fc53c802bfea904202bf18f21036faca20807fe30c80057f3188224ff94d41037fcc3a0077fe40c842dfe9844201fe10140007fa8290802fe611084fffa948201bf181410c7f860908a3fe20d041bff9964020ff4c84100ff8809001bfd421084bffaa2821bff8c22113ffacb20866fd6348401bfb2a2007ffd94410bffc879089bfc5090403fe1062006ff951410e7facb10802fd62d000dfe21a8035ff54f4200ffe61a001bff43d080dffa0a8011ff4c740037da842101ffc418846bff1968408ff54f10177f8632109ffd519041bff31e401aff54921007fe4290802fd6290401fea0e2007ff9062100ffc61a00affe1010801ffb0a8406ff580410bffac79085bfc538846dfea868407ff8c4210f7fca99081bfe651040d7e3244206ffd0c4216ffea421067fe31484037e300840cff18e4213ffea1208d7fd30d0819ffb0c8406ffd0a4100ffe4090033fc611080fff28e2000ff9912012ff8caa08b7fd5110851ff0868211ffccb4009ffc8010853fe430841bfe98e4000bf59110177fe6121003fd61c800bffa8a202affd4b4100ff8618801bfb4050015ffa9a4001bf18121007f88510807fe504400dffa1e822dffd404208ff8a7a00abfd51d040ffe0844227ff99641177f8a72101bbc40108017fb024200ff582410bdfac79085ffe53c8413fea96200dffcc72010ffea22082fff654805dff9948432ff8c242077f8a390003df6350401ff90e2003bf19520007fcc39007ffe501042dfe21c4206ff10142197fcc121003ff418840fff18e202eefd0e42165fac621003fd62504037fb228000bfd81420b7fe611088bfe3290401ffb02422affd434103ff8ca2084bfc51d0019ffb008400fbc86210077e8521003fe644406dff2968415ffd5021027fac688007ff2044019ffb088401ff1432000ffe60a0002fc62c40017eb262005ff1951000ffc60a0003fd42c8061ffa9a8406ffd0842037fe82a08b7fd50108057e31c4224bfd8d41007ee429083ffc535002ff7196420fffcc940035fcc988033fe3210801ff21240009f594421b5facba10d3fc10d0853ff1968214bfd8c21005f8c29001bfd63d0049fe9928206bfd8f420cdfac510803fc41c8003fea024001ff88120177fa6321003fd64c840dff31e8201ffd012001df8cb1081bfc43d08057e31e2000ff48421157faa1a088bfd3090447ff2828206ffd0b41037fcc7a0053fd4308431ff2024207ffd8c21037fcc021003be4290441ff990820cff1864203ffec010816fd654400dfe216820eff553200c7f8c090883ff3110413fb28e201eff59721067f8a5900cffc51908077e32a8002bf18d400affca810
  | 6 => 0xdff31e8401bf5831019ffea12101bbe541082ffea9e4201ff54340005fac890007ff50d00077f32c8429ef50f41005fcc3a100afc6350461ff98a8401ff8414003ff8a38800efe65c800dbf328841dff0c32100df8c02081afe6190403ff2022000bfd8141047fe6388097fe5150409fea1a2000ff08510087fea4a0033fc3208401feb0a841cffd4221015f8c62086bfd5448461ff29a8405ffd5110177fa6121043fe655000d7f3264007ff10421007fcc89081bfc62d00077f32e821bff8822100ff8a18801bfc63d0401ff20e4006bf19740187fac6a101bfe40104077f32e842fff18142037fe85a001fff6210401fea162000bf98b41067fca59008bff539044bfea928200ff88540005fcc390003fd41c8403f6106400cff8ca4218ffacaa1013fe434404bdeaa28200ff48510037fe8521047fe32d003dff28e4206ff10341037fa85a0803fc615003bff2864201ffd4140117fac720807bc40d0003fc1024000fbd894100ff8219006bfc54484057f31a4205ff95110007f882908cbbc4090819fe2164033ff54242037fea8208b3ff5310815feb1a4006ff90c41057fa64900027d65d003dfea964229ffcc74113dfecb2086ffe1088447fe3028220ff94c410cfda6490813fe5344013feaa62002bf98f21005fac48801bfc60d040dfe2008409ff14b10125fac9208d3fe20d081bfe21e4024ff8c541067f8c790803ff41c8017f72924006ffd0940015fcc7208a7ff53d040dffa1a801cffd4a2100ffa61a001fff638840bfeb2a2000bfd911000ffaa0a001ffc3108403de2028000bf5932007ffec6a009ffd5090411fe1962001ffc41100e7faa310833ff63c801fff1928002b718d41035fec621006fe62c8001ff3244200bf98b40007fac0a081bfd61d082fff18e4207ffd82410cffcc69081bfe41d0013fe2a6201cff94a21007fac09081bfc65d0401feb044230ff4c942007fc852083bed52c800dffa1c8201bf9832103ff8838809bfe1090419ff294842fff94142067f84010893fe4350425ff296801effd53210cff8629085ffd43c8449fea1a8206fbd094212dfacaa08cbfc10908297f30c420cff908420077a822081bfc63d0803fe0828034ff843420e7faa110853fd53084017fb264006ff10b400cffac690873fe65884057e31c8236ffd4b4205ffea290006fe60108017fb244201ff0434000ffa60a009bfe2090403ff282400cffd964203ffca210842fd655000ffe18c820fff58d40037f88721007ff30c8001ff20a8036ff547420c7f8409085bfe328842dffa1c4200bf98a41037f887a0003ff4288447ff2028213ff0c0210bdfcc41081bff41d000dfeb168206ff10940007fa821081afc651080dff2168224ffd8d410cffaa690813fd3244021ffb2a8001bf9802100ff441900dbff50d0821ff292800cff1
  | 7 => 0x309a0781485f1ae0040e8cb08833c0d8420080080217f12422802802028120070100000220da030040300180008e1e44381601002c2602e00002c0f0040061e00130051c00c0f8070b22a00580e004068098020000001900000001c0002200600c0882d0140c43400200a00020000000068008000240000e0070102c80402e0300007d0000d81941683800200c0300408a0200a007000294ba83618a07c348030060040303401c0002284605c0080400000000000ad6002000078000087e43d8150061040334f2bc01c2e8f51180e40001d0001384681d02c0080b01700413c038131420bc3f800004020060060000340100301c0a66a01a00e0440000100a8a89032d0341942d83c0080180302b00e03c0580300805a1b8023b80c8738070140680080c06a27005006000098fc801000000000010220040300001a008000030000780300007801c0180d0000084300000001c04003024004048090040240180009a3ec45051036be05f0a9000000012c903c0041180c03a1885280303a05c7f8013900264400002e0ec1a80d0001342f8230203500201500201c048430000580e14f00a0100385e000094010000040d80281207216c3d817002018040000c400014833032000088000000383f800000010270030002e80200300001c3f00000c0000000b00e0980600e0020000002200e0ac278a405a038434ad00e1402a0520040605780500802c3880000025c0114902e06c0280000004000008016034230040320b80600a00000c148000380000100b0186682c80b0061397a04f00000000000006008000001300d40000101c09c018000000094680b0000c4000510000680800d1000b8000070000d80501804e17c2608919c05c0000c1180042e0001080e40080f0360300800000c0d86400a0a20441300b00e0082e82402e0340f00002e04805800000120000030940000283000e0000783a000000068a803e07405800002000010e00000200880a00a00c188040a600003002000060b980602a0480280401200c098022e60cff1932005dfaca90033fc20c840d7fb288415ff9942103ffc62208cbfe109084dff3048212ffd4b40005f8c48801bfe65108015e322400cff1482100ffaa19001bfe5450803ff086800aff94d2019ffea5210d7ff53d080dfe2048233ff54642067fc6590017f6514402fff31e4224f718d41087faa2a0063fc5048455ffa8e8217ff0c721007fa8490897fd6550447fe1028206bfd97420affaa81081bff60d083bff3064230ff50d4218ffea8a104bfd51d0059dea188408ff4c710037fe87a0002fe6244049fea9a8206ff10342004feca900c3fc3250847fe1828201ff48310007fc43a001bf541104017eb068200ff59110007fc8510857fc540840
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7558520277ae4010a21006bf6418520064ff75d9320006bc53d9120006fb50d8121227ac6210a4103cff739872003cfc75d9310004ef7259121064fc72580410067c7559110004fd73d8141006dc54d8d2103cfe71d902111cfd7699310004fd71d8940004fd755822115fb82019120064ff70189400067f73d9510006df75d8d41006ad641082100cfe7018542006ac6488521007d7734842103cfc7118910067ac4250b20006df735874003eee21988410067e7359740066fb2058021004fd759874201cfc75d8121034ff7259320006f76190540004fd735824205d7e751052003cfc73d92210057d75109201ce7e10d9510005ed7210520007ad32191211ce7f30d9510006df72d8d410dcfe761891003cff75d9310004fd7608540006ed65d8941317ad515084203ebf6499021004ff7558221005bd7408540006bc32d9120005f4715094127eed6310a21004fd7699321037b66110a411f67e205974001cfe755872022fac4010a21004ff7358b411e67c30d9520006ee30d894103cfc73d9310006bf64d0521006de52d8d41005df7350520006ec3018941006ee63d8941066ec629094003cfe71d81420067f65d8520006dc10d8d21006be5119121006be54d9320007d763c85210667e3259442325bd755084201cfc75589102aebd6390841004fd74d85202c5bd7390541006ad541894109efa3058021006bc63d912000df870485202e6bd63d064103eec2158a410067e3159740004fd7358041006bd6490b10307ae3050842006bf64c85200067d3259740006ee3258841064fc72d91201ffcc7348421005ef7250720014fc735891003fb65150441064fc7398b4101cfc755932000cfc76c851011efa60d814100cfe7058b4100cff7658241006ed71d894130faf3150842036fb7058341255ed7388521006dc51d8d21006bf7650842004fd73d9320066bf6290942004fd73d89400367d40594410067e43d9520006dc63d8141006bf6450521006bf65191210067c73d9510006bf3119120006be75d9121006bc501912113d7c7558241006be73d912003e7e7159441317ad52508420367f4259441036fb4058341006ed52d8941066be42593210067c31d951003dbf765044117ef86058142006ed6290a410067c32594412efae3210a410c6f71058720005f57190941005bf744851000cfc7650540196bd40d912001cfc7558b10006bd545804230faf3250842004fd73d8542004ff735874200cfc70d9110004fd7098a4103cff759844203cfc7598742004ff705932103cff7518520005bc7150842006f77159110004ff7058a4103cff7459021196bf6490920034fc7458021006ed43d8941064fc751894103cfe7198b40006ed31d894101cfe75d8b10006bd511912001cfe75d814200cfe70d9110006ee43189410067d63d9520
  | 1 => 0x9442036be7319120007ac6488521064fc7398b10004ff7159121004ff755874003e7c1059441125de76d8d41006ee6018941034fc745832122fae7410a21006dd52d8d21014fe7358241014fe7359221005ed7610a21005ed76d082120fe74118941037ae7210a41066f86058321004ff7650720006bc32191210367e4159740004fd735931003cfc759864220eed76d08211ce7c70d9510036bc645051003ebd74d8b10007ae521912005d7c755912022eee6110821006dd65d8d2101cfe75582420063c6519120006ec101894100cff7658221014fc73592210367c4059442064ff7598b1003e7e41594410367d4159441035bc744854003df772484210cfcc72d8d21036bc64d051001cfe7598910006bc64d8520004fd7558021066f66288421006f7619854003cff7318b10014fe735844201cfc7558242006de40d8d41006bc43d911003efb1058241004fd70d8542007b67190a411c5f973c4110006f731d8542006bd5498b412d7d441d8d4100cfc76d0510004bf7650441004ff725804100cfe7059321065ec725072101cfc75d9121006bd75d9121004fd72d814111ef850d8141036be545844200cfc7258720197ae20d9120195be70d0a42004fd755902118e7c655092022eed64d0a210057d7510a210067f65505100067f65d0510004fe7608540006ed51d8941036be6419110196be6090841036bc6490921034fe76d9121006bf52d9121006de51d8d41034be74d8b1003eee6148421006ef54d89410067d65887400def51098720006df71d8d2103ef810582210c4ff705891003cfc7158242004fe7690520006dc7358442066bf74593201f67c2059740014fe73d9120005ed7110821004fd70d9121006dc639912122dee74c862103dfb73c4110005bc7448421066f82058242004ff7558041006bf64105200069f64d8d210c6ef2058b102d6dc40d8d4101cfc755874015cfe7690920006bc64c852127eef6310a2103fe651c8621006be53d9121006bc32d912100cfd7458041006bf50d9121006be50d912103ef44198442006bc10d9121006be3219121004fd7690b100067f6599110066f76198642004ff7558442004fd75988411ce7d10d951011ebd4059310014fc7358042036bc7319121006be541894031dad7350842006ef5018941006bc6319121036be75191210067f6519110006be531912100cfe70984421ce7f70d9510006bc31191210cedc71d8d21006bc60d91212979c73504412eebf6310a41006de40d8d21007ad421092103eec2198b10066ec6208540006bc51d9120007cf63885210676e7510821005bf7448740034ff76d09100d57e75105210373d6590841007b54110521004fd74d8910064ff7158b10004fd7558720146f710d854003ebc4159021035f6719054101c7c7559110006bd50d91210057
  | 2 => 0x6ee1018941006f77159121066f77158442036be7119120036f44158442064fc7690910064fe7298910006ef30189411e67e10d952001cfe75d8542006ac6290541006f53158442004fd7648740006be65191201e67f30d9520006df7358910004fd73d89100367d4059442006bf31d9120006bc54d9120006af7650842034ff76d0720005df7350540006f761985420f57e75107210079f64d8d21004df7358910006ee43d89410067d30594410367c4359441006dc63989410367c7459441297b73150441006be4218542066de73d93210c6fa10d8121064fc7398a41004fe76d0521006ef65d8941006bf4359021004ff7559110004ff7358041006ee5318941064ff75d9321006bc43d9120006ef629894003cfc7158042036bf4398b4103df67190a412febf6590a41006bc5119121064fc73d9321006f431d852003e7c415944100cfc76505100367e4159442014fe7398841005f77150a2103ef970d9310014fe73580420067f325974003ef97018b100067d71d95200367f42594420067d6548740004fd7598b410067f7359441006bd32d91210367e7459740006bd31d9120066ec4298841006ef6250940006bc5319121004fd7559310004ff73d814101cfc75592212d6df42d8d41036fb4058041227af6210a41004ff7359110065bd76d0a420067d3159441006f53198442004fd709864203eec2158841036ef42588410667c2159442004ff75d894003fe4314842103cff7608740036bc64d092100cfe7098642006f93058042006bf70d9121006bf631912115ebe6010a41004ff705884103ebf65504410063f65191200067c31d9520005df735042103cfe71d9110035be740854000cfc7059321035bf73d0a42004fd7598910006dd51d8d21067ea52c8120005df735072103ebc4159310005e57110821006f930582212dfb551d0641014fc7358241004fd7318940006dc72d8d41006dc50d8d410067e7259740037ae6050842006dc63d89411ce7f40d9510006dd70d8d41004ff75d8941064ff7648510005bd7498520006df75d8d21006bc73d912001cfe7558042004ff7558342004fd7598b40227ae4110821006ec625094101cfc75d8941006bd54d91210057f7559120004ff7158b40036bc7119120005df7348720036be6190a41006bc64d8121034ff7659021004fd70d89410067f6550920197ac20d9120007e54248421066bf6499320196bc10d9120185dc735854203cfe71d894003cfe71d8b100667e4259442004fd7359221004ff7159120007ad54d8941006df6390941036bd7019120006ef63d8941034fd70d8940007af6290541125de739894103ebf6350441006bd631912001cfe75d894001cfe75d854011efa40d8141006be54d814122eef6410a21006bf53d91201f67f10597400067d74d95200367e405
  | 3 => 0xd7510720004fd7398b1010e7d7159441006bd75d912006ddc7358720006ec73d8941004fd76992210372e65508420fefa2058041045dc7350710006bc20d9121004be761912103ebe74d8b10037ad6350842004fd7358442034fc7458b10005ee7210520007b57190a41006bf6488521004fd7559221004ff7358442196bf20d9120006bf71d912101cfe755912003cff731854222fe741d8941006bd51d91200067f6550520007cf7348421014fc73d89400067d32d9510007e5414842100cfc765092003ef710185200857c755894020eef4118941005ec7259110006ed411894128eed63d0a21116dc6390541064fc7598b41327af75508420edf77158910006ee6250a4117eef2058b400373e6590841004ff7558b400067c72d95100067f65d052000cfc7458b4001cfe75185420057f7558021037b76190541014fc7358720007b47448421125dc7358941036bf7219120004fd7558342034fc76d0520014fe7398442004fd75d9110196be30d9120014fc735931003eec6258b102a6bf6390a411cf7771d951003cfc73987420067e30594410367e7459441006bd54d8141066ee3298841006ec62d814103ef4419874222eed7610a2102d7c7558910014fe73d922103ff251c411001cfe755804122f6d7510a2100cfc7098b41037ad6050842064fc7259110006ec30d8941006bf53191210cdde7399121006bd52d9120125dc7358141006df54d8d21186dc6350921006bf43d9120005f571d0a2101cfc7558321004ff7158042006bd5418940014fc7358341006ed531894115ebc3019120066f571d9321037b66190841006ae32191211e67d10d9520014fc73d912003cfc7158342006dc6358941064fc7398841025dc7359110006bd65d91200367d435944100cff7658021064fc725902101cfe759874000cfc7018520064ff73d9320004fd7358642006be4059221336bd6590942006be65d9121014fe73587420667c3259442004ff7650b10014fe7358b40005fb704851003cfc7159021006ec311894103cfc7598720064ff7598b41006bc4059221307ac3050842006f5611852003ef46188520006dc63d9121006be60d912115ebf5019120014de76d8d410b5dc7350621006ef52d8940006bd43d9120066ec4298b40004fd7418910005fb7050540006bd435902100cfc7650940005f77150a410079e54d8d4103ef44198740064fc731894100cfe76d8141006be31d9121065f57288421064ff731891012e7c6550520006be20d912100cfe7298720006dc63581411a4ff72591200defa3058221196bd30d9120066f662484210ae7e6508740065ec74c842101cfc7558021066fb20580420067f31594410667f2159442036bc6410521034ff7650721064ff76109100f67e65c87400067f71d9520004fd7518520007af7050842
  | 4 => 0x8120005bc7250441004ff72591100067f6559110197ba4058242006de65d8d410067c65591200057d759891000dfa71c4110004fd7558242014fc73d8520006ef7258910066ef2098b10006bf73d912100cfc7458740325bf7550842004ff755834130fae53508420073c6519120004fd76d0520006bf3119121006bd651912103cfc7688540006be43d91100067e31d9510126dc635052101cfe7518910227ac4110a21006ec70d8941066ef2018940005f571d0921006dc60d8d41006be54d932115ebc6010a41006be631912103df47150a41006bf649052118e7c6550910004ff7358241006be54582420067c705944217ebf4059320064fe72d9021007ae3219121005df7358542006ef50d89410363f41594412d6dc41d8d4103ef671d9221006bc10191210057f75589400067f6559120006bc52d9121006bd54d9320004fd76105200cddc7350521006ec63189410047f755824226eed63c8621006dc10d8d4103cff73987400063d655044100efa76c812001cfe7598841014fe7318941004fd76c85400067e7159442037af7650842005bf7448710004ff705912101cfe7558342196ed2098b40317af5050842005be7498520004fd73185400367c4259740004ff7358a41004fd7358221006f56118542006bd301912120eef4018941025dc734851003cff7318540004fd75d9221006bc3119120006df70d8d411f67d20597400067d7359740064fc73189101e67f40d95200067e63d9510004fd7358b10197b820d912003cff7598740014de73d9321066ef7018941006bf54d9120006ef7259120066f97098910004fd75984420367f745944101cfe7558341004fd7359321066f4215872001cfe7558a41014fc7358321006f46148520007b464c852109cfd7018910004fd7358b40004fd7558442006bd64d0a2102d7e75989101ce7e20d95100067f7558242036bc64509200047d75d8b10005f57190a4102d7e7510910005bd719084103cfe7118b1029fb55150441006dc51d8d41004ff7358021004ff7358221005ec7258141034ff7659221014fe7318542005df7358121014fc7358742005f77150921014fe7398740035bf75d0a4203df47150a21006bd4359310004ff75d854020eee5418941006bd311912103cff75d8b10006ed7118941005ac7150842014fe7398910066f72158720064ff7398a410067d7359441004fd74d8b100367c4159442005ec7250510004df7358720006bf4359310004fd75591211567c65d052000cfc7158b10004fd7418b10004ff755931001cfc75591210067c73594420067e3259740004fd76c8740004fd7358a41006bf74591211e67c70d9520005be72d0641006ef5218941006dd74d8d21006bf72d9121067e57110821014fc73d8121006bd5458442036ef7258b41004fc76485400057
  | 5 => 0x67c6599110006dd52d8d41004ff7650910005df73585200367d43594421ce7f71d95100067c6519110006bc75d91200067d32d952003ebf649931025fe532c852122eee54d8941006bd53191201df7865c812001cfe75d8520004fd75d9310006ed32d8940004ff7259121006ee10d8941004ff7558742014fe73591200067f7259740006bd5219121006be30191211ce7f10d9510004fd76d0910006be43d912021fae40108210067f63d9520014fe7398b1003ef71098720036bc64505200367e4359441006ee73d89412eebd6310a41036bc64d052000cfe76c851001cfe75d812103cfc7318b10004fd73d81210363e7519121036bc4058042014fe7358242066ec701894115ebd1019120064fc75189100367e425974003ef6719874003ef86058221005df7358941036ef4298841006ed6318941066ef71189410063c65d912003eec21988410057f7558141005f471509210067f31594420067f6590510064ff7598a4130faf3050842066f5719891003cfc7318520004fd755864222eec648852108ddc73487401a4ff7650b20006bf641092103ef671d8b10014dc7358740006df50d8d2100cfe76d0510065bf7650842067e67110821006ee70d8941037ad6550842006bf64d8520006bf6458121004bf7650842004fd75d8542004fd75d8540006ee53d89410363d751912120fac4010821005ac744842100df870509200367c43594420073f6519120006ed541894100cfe70590210373e7510a41196fa4058242006bc71d912001cfc7558442006df631894103ebc4159221006bd511912130fac31508420057f75591100367e4059740014fe735834114edc63d052117cff7059120006ed7018941007ac725044131faf735084200cfe7018941066ef6410821126de74d8d41064ff7398b100067d3159442004ff7359310006bf5219120034fe7418b10007cf631894103cfe7118940006df72d8d210067d74d9510006de64d8d21004fd7398442004fd73d902101cfc7559021006be5319120067ad6410821006ed3258742004fd739891005d7e7599120005be7619121006bd6419110004fd71d932027fad4310a21005ef7259110004fd76907200067f6558910006bf32d9121007ae52d912009cfe7688510006ed501894103cff701854003ef671d9021005bc7448720006ec31d8941004fd73d93100067d73d95101f67c705974003ebc645931022eef64d0a21136fa4058241036f4415874022eef71d89411ce7c20d951015ebe10191200067f6588510004fd7650b10036bf7519121006ef70d8941036be64d0a21036bc6410a2100cfc70d90210067f74d9520006be545911015ebf3019120004ff7258241004fd75d912000df870505102d6dc54d8d4122faf4310a2103cfc7398642006ef6250941006fb50d814200dfa72c
  | 6 => 0xf7518542034ff7650a21036be6450721036be64d07211e67e20d95200067c305944103cff75185400367f4359442005bf7448520006be32d91210fcfe7690510006be52d9121007ac7448421006dc735911003ebe6150441034fd70189400dcfd70d8910064ff739891001cfc75d912020dee74c8421307ae1050842005ee761894100cfe70587420cede71d8d21006dc70d8d410067f6510910036be54587400067c6519120006ed751894103cff70189100c4fd7698b10004ff73588410067c3259740006ee50d8941007ad52191200067f32d95100067d305944203e7d75d8b10066fb205832122eec4298642004fd73d91100067c6558520066ef731894101cfe75d8910006dc65d8d212cdbd7590541006be65d9120064ff73d93210067e63d9520004ff75d814230fae735084201cfe7598b410ecff7648710006bd6419120065ee74d08210e67c658852000ff271c4110006df6350921004fd75d9321014fc7358a4101cfe7559121006bd6210a4103cff73d9021036be54583410d57e75191210067e30594420367d4059740005ed71d0a21014fc73586420367e7459442006ef621091001c7e75d8b10037ac4250941006ee201894103cfc75d9221064fe72d9310005f97090940004fd7218540006bf75d912115ebd501912022eef41d8941006bd43189410c6fa60d8121006df7358720067ae741082103ded71c84210067e31d9520005bd7610a41066f72198642006bc63d9121005ed721072001cfe75582210067f6548510006dd51d8d41036be5498b40006dd65d8d41037ad6150842004ff7558841036be7019121004ff7558b10006ec6518941006bf43189410067f63d9510005df73507200667f2059442006ee75d894103cfc76905201d57e76d95101567c65d05100c6fa20d812120eed6410821005bd7110a4112e7c6550510006df64d8d21004fd72d9110006ef62485100057d7519121066ee7298b40034fe74d8b10055dc735052003cff7518b1000cfe70d9021005bf7458910006ef62d81410063f65d91200857c755854015ebe4058042006bd73d912131dbf7350842065be72909422b6bd659084103eee61c8421005f97090540006ee5018941014fe73d9320034fe7418910036be6410b10005ef7258141006ef32d891003cfe7610b10036ef4298b40005ef72505100067d65c8740004fd70d9321067ae62d0a4215ebe5019120007ad42109101cf7471d95100067d6508740006ed53d8941004fd72d9310006bd43586420367f4259740004ff75d911000cfe7058a41006ed75d8941025dc7358910006bf4358642004fd73d8540064ff7598910006df74d8d4103efb105804122fe671d0a2103cfe7690b10006bd63d9120317af5250842006bf51d912100cfe7158b100079d54d8d4103ef86058021004ff7559321
  | 7 => 0x9441006ec52d8940037ae6150842004ff7458720014fc73d81420067f6519120007ad64d0a210067f65d9110006ec62581410deed20d8910067af6550842007af72504411feed634842103eef6348421006bf63191201e67f70d952000cfe7098b411e67c20d9520006ee7518941067ae6410821345bd73d0a42014fc73593200067f659052003cfc75d90210067e32d9510066f86058242005df7348510006de54d8d2115efa3058042014fe73586420079f6390541035bc70d0a42006ed63d8941134fe7610510006be51d912103fe64148421005f970105201dfe952c8120005f57110910036bc6490a210067e72d9510014fc7358242036be64191210067c7558242196bc6090942037ae729084122eee61d0821004ff73d85420067c105944203cfc7318542006dc70d8d210367c4159740006be71d9120006df52d8d21006bc70d912130fad5350842006bc40d9121006f771589100067f7159442004ff7458b10006bf65d91210673d6550842065bf725084203cff7398442004ec7259110066bc4259320004ff735874003ef42198642004fd7298740067e44288421126dc74d8d41336bf6590942006bc50d9121004ff7358321006f76188520004ff7650821004fd7358742004ff7559221006ed321894100df870509400067f7558021006bd5459110006ec7259110036bd7610a41006ed3298a41067ae52d0a42006bd5458242004fd7518940006df63d8941006dc60d8d21006dc7359121006ed6218941144ff7650710004ff7558720006de10d8d21006ed50d8941004ff76487400057d7598520036bc7519121004ff7648421005ec7250621004ff75d8121064fe72d8141006bc73d9121066ee72d9321006ec63d89410757e7510720006ef52d89410c4fd76c87100067f65585200067f6588520066ec2018941317ac7550842004ed76108211e67f72d9520014fe73d8910066f46158642004ff73d8910007ad705084203fe77248421005bc7458910014fc7358b41006ef628854003cff75d922113e7c6590520006bd4359221004ff72593100067c7558910036f84058341006dc7358740014dc73591212debd65d064122eef40d89410367f7459442034ff7650521006f95058021004ff73d8142007e761885210067d7159442194fe7610920006fb705891001c7e76d9520006bf4359221317ad505084201cfc75d91101a6fa2058342007af4318941064fe769072001c7c75589100dcfe76085100073d751912103eee7218b10006ed6218910196bc30d9120007ad4318941067ac6150842014dc735911003cfc76105200367c4059740006df54d8d41196bf50d9120036bc64109100073e7519121014fe7359320014dc735844216e7d7259442006bd54d9321006bd631912103cff73987420ecff71589100077b65c812003cf
  | 8 => 0x67e7359442006ef7259110006bd5458341036f74158442006cf6318941006ed6250a410067d3159740034fe74d8520006dd50d8d210069c6319121014fe7358b41006f76148520036be6490b1004d7e7510b10196bf30d9120005df7348740006be5459021067e652c8621064ff7398b41066ec6210910005ec7250521004fe7619121005f97010910196be40d9320014fe7359110196be10d91200047d7598910006bd70d9121005df7358141036bf7219121006df70d8d210067e1059441004ff76505201ce7e70d9510006bf6450510005ac7250441006be6319120006be40d9121036f8405804103cfe71d9120066ef63108210067f3059441004fd7558a412a6bd6390a41004ff7059221006bf50191211ffe73248421004fe76c8540307ae7050842006dc6359121066be62508420073c65d91200067f6548520006bf64d0921036bd76d0a42006bd5498b4000cfc70d922130fad3250842004fd74987200067f32d9520036bc425884103ef81058241004ff75d891001cfc75d8520007b864c812015ebe20191200367e4359442066f72158642066f4215864201cfc7558342004fd701854200cfc7648520006bf64d0510006be31191200067d73d9520004fe76509100d67c6548520006be54d854016e7c65109200067e74d9510006df63d0521005df7359110196bf70d9120006de50d8d21005f576c862103fb43150441004fd7398742004fd7598642064fc72586421bff151c4110006dc6358121014de76d8d2120eef64d0821004ff75593200367f43594411f67c105974007ddc7350540196bc6090a4103cfc73d8b10004fd7518542004fd7610b10196bc40d9320006bd73d9120004ff735902103e7c3159441006ec62485100eef710d8520006fb7059120006dc75d8d41006ef321891003cfc76d0921176dc63909410676d751082100dfa701091022fae64d0a21006bf64909210d57c7558121004ff75d8141006bc31d912005e7e72d9520006bd3219120006df6350521236ed6310821014fe73d8520004fd7358841036bd76d06411e67f10d9520006bf7650441006ed54d8941004ff735864201c7e7598910006bf649911001cfe7558841014fe7398642227ac4110821004fd741852001cfe7598442004fc765052009efa505802100cff76582421ce7d20d9510066ec52189410067c715974001c7c7558242004fd73d9321004fd7398642036fb4058342006bc3019121067af6150842037b4415094101cfc7558a41034fc7458720006bf6450920007cf63d8941004f77648421004fd73d8520036bc6490721005ec7250710006be53d9120014fe73d91210077b65c4110004fd75d89400a5dc7350421064ff7398b4000cfe7159310006df65d8d41007ad32d91210bddc73507210057d7599120004ff71593200367d425
  | 9 => 0xf625814100cfe7059121036bc6450921004ff75d8520067e632c85210067c65589100067f65d0910006bc53d912103ef421987200067f650851000cfe76d812100cfe70185200e67c6588510036bc649052001c7e76d9510064ff7610b100067f65c85100363c4259441014fe7358041066f721987200067f6598520004fd76109100067c305944220faf4310821004fd75583210067f65d8910036fb40580420067c655911022eed6410a21064fe72d8540006bc6519121004fd70d902131fad735084201cfe75185400067e7159740036bc649091003def714842103cfc7159120064ff76c8740136bf40d9110036bd731912120dee741082115ebc201912003cfc73987400cdde76d8d21006ef62d091015efa1058042006ef6298941004fd7558b4000cfe70d91210367f415944100efb62c8120006bf64d0520007af43d8941006ef5118941014fc7358841004ff7458321136fa3058241006f77648421006bf645052020eed64d082122eef42986422d6df71d8d410067c6598520066ef7518941064fc7318940006bc645852005d7e7598520006ed3258b1001cfe75d922103cff7690720006bc75d91210367d43597400367c745944200cfe705864201c7c75580211ce7e40d95100067f6590910034ff765931000cfe70d9321006bf6490721036f74198442036ef6290942067ac6050842006ee325874203cff73d8b1001cfc75580420367f435974003cfc7608540065ee7210720005f67110910004ff7558910006df7359121006ec625094003ef67198742034fd7259320004fd7198b40004fd73d9120006f93058241064ff7690b10006bf64c852134dbd75d0a42005bf7448540034be76d912001cfc7559321014fc7358342066ed7610821007ae6290a41006be76191210073f65d9120006bc6488520064fc7398b400047f7559110004ff7558241006ee20d894101cfc755931001cfe7559310196bd10d9120014fc7358041004df7359121006bd6290a4100cfc72593201cf7410d9510006bf64d81211f67d30597400057d7510510004fd7398720307ae2050842006ee31d8941006bd53d9120006bd5458740004fe76d0910004ff705874230fae3150842034fd72d8142006bf52d91201ce7c40d95100057f75582420cddc735912103e7e75d8b10006be54d9120045dc7348710227ac6410a2100cfc705844215dbe7050842004ff72583410e57e7510a2101cfe75d931017cfd76d0b20006ec65d8941014fc73d85400067f755911032ebf639094215ebc4018940004ef725911000cfc76d09200cedd72d8d211ce7c71d9510036f74198742005bf7448421006ef3218941004fe76d052017efa60d814200cfc70d894100cfe70d8542116dc6390521004fd709874203eef6298a410067f651092001cfc755874211ef86058141
  | 10 => 0x8740006df50d8d41005f970d0920006de20d8d21064fe7218b10007b764c8521006f6315844217cfd769932001cfe75d9121004fd75987400067f659912003eee2158b10066bc6459320126de71d8d41005df735912100cfe76d0920006ec7259021006ad4318941136f51098740007ad4210b10006ec52d8941006ef629054100dfa70d0920064fc75d9320196bd50d91200367f7459740067ac5250842006bf3219120006dd54d8d2100cfe7059221004fd7358720004fd75d81421e67d20d952003efb105802100cfe70d8941005ef7250710237ad4310821007cf72d8d210079c6319121007ad52d9120006bf7459120006bf5219121004fe7690521004ff7058442014fc73d8141064fc7398910006bf53d9121066ee7298b4103fe6628842103cfe76d0b10006bc6448520034fd7159310006bd54d85400067c7359740064fc7598910004bf74589100067f3159740034fc7650521064ff70d9120014fe7359321036bd7019121006bc601912101cfe75d8941037ac4250a41004fd7608740004fd75d812100dfa7088520307ac70508421a5ef725912000cfe76909400067c65d91200ecfd7098910006be10191210067c74d9520005ef72506210367c435974020eec4218542066fb2058242066ef2098b40035ae7290942007ae715084231dbd7350842034fe76d911003cfc7518520006bd645072100dfa7010520007ad4210a210d57e7510921004fd75d8941006dc631894101cfe7598642004ff735834201cfe7558b4113e7c6590510036bf731912001cfc755912020dec7448421006bf30191210067c32d951005d7c755852011cff7059110005ec7250520034ff7650510006bd64d07211e67c72d95200067e32d952000dfa76c4110066ee5218941037b77150441066be4259320036bc7019121006ef72591210067c6599120006bf6410521004fd735912131daf73508421ce7d40d9510066f461587200367f40594410c7e82048520006bf7458910035af765084200cfc7198b10036bf6590841064fe72d93200067d7059441007ad7150842014fe7398b4017efa20d8142006f761985201ed7e76d9520006df7358442064fc75d9321064fc725824100cfc7059021006bc5219120006ef74d8941005fb7048520006ec32d891003cfc76d0b1003ef6719844203eef72588412d7d741d8d4103cff7610720196bd72d912009eed2018910004ff7458021066bf6499321006be545931015ebf1019120066ee321894103ebc6459021064ff7690910006ef62c8510014dc735891015ebe4018940036bf6390841066f82058021006dc735891000cfc7058b41005bd740874000cfc7098642067ac2050842004fe76d092100dfa70d0510004fd7498b10006bd7690841036f441587421f67e3059740014fe73d8941036bc4198b41006e
  | 11 => 0x4fd75d9121006df63d8141006be5458642006dc74d8d21036bd71191210067f6590920006ef6208540006bc6498520006bd5019121036bd73191200667e7259442005df735051016e7f7259442067e64248421006ef6290940004fe7690910066ec62c851006ddc7350720034ff7659320066ee72d932003ef81058041006bd30d9121006ec62d0910006de65d8d21006bf31d9121006bd32d9120004fd735874000df87048510034fc7650921006dd72d8d410057f7558910004ff7559021006dc20d8d21066ec6290941006ed6218940006bd31d9121006df52d8d41196be609094222eee74d89410067d3259441034fe7498910036f8405834203eef63c842117ebd405932018d7c7558142006bf63d9120006ec20d89410067c71d95200372d6550842006bc43d9121006df63885212d6de54d8d4103fe651484210067e71d952022eee648852117cfd765092003cff759874216e7c6510910006cf63d8941005bf7458121296bd635044103cfe72988410367d7459441004fd765091001cfe75d9110006df635094103ebc6499221006be50191210067e10594420067c7059441034fe7608740005ed71d08210067f305944200cff7658321035be7290a4103cff7688740196bf40d91200ae7c650852005e7e76d9520006ee63189410067f6510510005ef72505211b67c65d0920006bf5119120004fd7688540055dc734852000cfe7098742004fd7558041036fb7058342246ed63d0821066bc6499320006de10d8d41004ff73d812100cfc74d8141246ef63d0821066ec7518941004ff74582211e67e40d9520004fd7650720004fd71d9120006be75d9120064fc765072011ebf4059310006bc51d9121006ef32d894100dfa7090540004fd7318542006bd54d91200067f659891003cfc731854001cfc75582410067f7059441066f76198720007cc631894103fb651d0641036f7419874001cfe75d9021004ff7358b1003ebc64592210067f65d9120006ed7318941006bd6290841014fe7359310036bc6450521006ef6298910034bc74589100d67c6548510006ee511894105d7e7510920196bf72d912020fe4411894102e7e71d9510006bc745891019e7c65909200067d63d9510004ff735891001cfc75d8540006bf75d9120004ef764842103ded76c8621036bc4298742004fd76d0821007e74288421006bf6410a21005bc744851003eee2198a41006af4318941006dd75d8d4122fae5410a21064fc72593101e67c40d9520006fb50d8141166dc6310921004ff7559120006ef30d8941036bc6410920006de60d8d210067f73d9520006bd5319121004ff7058b41006bd71d9120004fd75d9021007b77448421006ec50189410067c725974003ebf65d064103f3d65504411e67e70d952003dbf7590541006f73118520004fd768
  | 12 => 0x860582412d6df40d8d41007ae5418941004ff7358b40006be31d9120004fd7358910006bd545902111cfd76d071001cfe7559021014fe73d814130fac7350842006be63d9121005ec72505401ce7d71d9510005f970c851000cfe705844200cfe7259320036bf711912101cfe75d814103cff7598720064ff7518910004fd74d8121035be740874001cfc75591100067d31d9510176dc6390921066f576c862103dbd76d0641005ec7258540004fd7358021004ff7648540006bd51d912101cfe75d9120004fd7358342006df74d8d211f67c3059740006dc75d8d21066ec3218941067ae3250842066f820580420067c6518520196bd70d91200067c65d91100fef5101854003ef63198442067e43248421005df73587200067c32d9520196bc4058242064fe761072000cfc701894119d7c75582421e67d72d9520006f93058041006ed3258a41006bd4398b410063d6590841006ef75d8941196be20d9120036bf7519120006ef7648421004ff73580420057f7558142317af5150842006be30d912103cfc7518542006ec629054100cfc7058841004ff7158342004fd7358b41006be63d9120006dc52d8d21006de50d8d4103cfc75984420defa205822102e7e76d9510004ff73d852003cfc739872001cfe751894003ebc6499021064fc7258341005bf7448720126dd41d8d411bf7865c4110014fc73580210067d7359442014fe7359121004fd73d8b10005df7348710006be52191201f67f205974022fe571d0a21006df635812115ebd20191200367d4159442036be6450a2103eee72d9021004ff7358720006bd5459310005f57110b10004fd7558740004df7359110007bb64c812003e7e3159441005ed72d0521067e65248421064fc76d0521066ec32189100067e2059441006bf7459110005fb7050510036bd72191210367f4159442014fe7318520006df6390521006bd52d912103cff731852020eee7418941006bd6450a2100cfe76509200367e4359740006f73118542006df73591100069c64d8d2107ddc735854001cfc7558221004fd7018941006bd65d9121014fe73d9321014fe73588410067f65d09201ce7c10d9510006bd43d91212d6df41d8d41006dd75d8d21004fd7558b4103dbe7190541014fe73d8540006bf43d9121036bc4158442006ef51d8941065ec7250421036f76190541007ae32d912103cfe7198a410057d751091001cfc7558642006be321912000cfe70d9221066bc645932103dbf71504410067f65085200f67c65c852001cfc7558041006bc54d91212f6bd6510a410067f65c8520006dd64d8d2101cfc75d814101cfe755874203cfe7650b1002d7e7510510035bc74487400067f6518910004ff75d9120067e66248421035bd7690841004ff75d8542006ed73d8941004fd75593200eefa1058321
  | 13 => 0x842064fe7259021004fd7559110006bd4358442014fe7318940007ad6290a41317ae5150842004fd7358341006dd54d8d4122fe441d894101cfe7559321005ee72d0521004fd731891003df67110b10006bf6410910006dc6319121014fe73d8b1024fcc6388521006ec50d8941036bc64909200067e74d95200067f7059442006df51d8d21004ff73d9110036bc6410721014fc735874003e7f10594410067f735974022eec40d89411ce7e30d9510194fd70d912003cfc715824101cfc75d89400c5f57198910004df735844203cfc7690b10004fd7518941006ec5318941307ac5050842034fc76d0910064fe72987401e76e20d95201ce7f20d951000cfc7498b40006dd70d8d21006bf6490520014fc73d8941007cc63d8941006bf63d9121006ee3258b100079f7350441064fe76d0720036ac425884103fb6615044100dfa70c851003fb661d064100cfe7648510064ff7318941014fe73d902100cfe7198b100dcff7648720004fd7690910287ad5410a2101cfe755911003e7c7159441134fd70d911001cfc75d854201cfc75d89100067f651852003eef7258b1003dbf7390541066bf7459321034ff76d0b10036be70191202bf9c6390541006ee32d894103ebf63d06410cedd71d8d2133fad52d0a420373d7510a4100ff361c41100deef20d891000cfc7058742004fd75d8141006ed3258442006be5418941066ee6290a4100cfe7018910064fc7518940004fd7358241006df63109210067e73d9510006ec5118941004fd735912003ebe41590210fefa3058041004fd7359021006bd321912100cfe7690540036ec4258b41014fe7398742006bf645852000cfc7058a4132ebd63909420067d43d9510006bf54d9121006de70d8d41036bc64d0521065f77648421004ff73d89400067f7159740005bf7458520036f74158740006ef5218940014fc7358b40004fd735932003def738852109cfe76c8520066ee7218910014fc7359120006ec75d8941006be761912010e7c6510520006ee60d89410067f43d9510006bf6488520006ed70d894101cfe7598720006ed3298b100a5dc73484211aedc63d0921004fd7358042014fc73584420067d7259441006ef73d8941196bc20d9120006f46150540036be6419120194be76191200067f31d95100cedd21d8d21006be5459221005ef72505200067c2059441004fd70d9221126de76d8d4120eef42185420067c71594421ce7d30d95100367f4059442006ee32d894003e7e2159441004fd709844203fb44150621034fe74d8910007ad4210920036b44158442006ee52d894115ebc5019120006ed3218940067ae5250842034fe74d81210b6dc6388521055dc7358520036f77158740006dd50d8d41004ff7558642066ef74189410067c43d951011efa10d8141196be405824203ef
  | 14 => 0x64ff731894001cfe7558910006bc631912000efa76c4110004ff73d85400067d31d952022eed76d0a21004fd765052101cfe75582410067f7558241036bc4098b40004fd75d8910067af6050842196bf10d9120006dc65d8d41006f76150540006cc6318941066f970d9320006ee6518941067ac4250b2101cfc7558720006ed3258841005ef7250421067ac42508210367c4259441066ee3298a41106dc631052101cfe7518b10006bc201912100cfc7058642005df734852001cfc75d8142004fd755834120eec541894103cfc71d9110006de52d8d21004fd7598a41267e551c86210067c31597401e67d70d9520006bc321912003ebe41593101b67c65d0910037ae6350842004ff7058642006ef62909410ae7c65085100067f755912017ef850d81422febd6590a410f67c65c8510006ee4018941004fd76d0720036bf7019121006de74d8d210067c65d8910196be4098b40004fd76905201e76f72d9520004fe761091011df57199110006bf32d9120006bc64c852000cfc7018542004fd7518b1000cfa76c4110004ff7558a41004fd7358321145f77159110064fc72587400067d325944203ebc6499310066ec7318941006bf6448520034fe76d9120006ec60189410667c7259442006be511912000cfc7648510004fd735911003eee2198b10036bf7019120014dc735872003cfe7159021126dd74d8d410cedc72d8d210ecfe7608520006be31191210667e759891001cfe75185200057d7510521067ae6250842004fd7598b1001cfc7558b400367d425974003eed72d92212efad3210a410067f3259441067ac65508420067d72d95100067d7259740064fc759884103cff73d9310004fd75588411e67c10d9520005bc74585200cede76d8d21267e552c862119e7c65909100c4fd76485100ad7c755802100dfa700854003cfc7610b10014fe739872003eec2198a41006bd63d9121005ef7258540005be71d0a4200cfc7018910005dd7398941004fc765091003cfe71189102a6be61908410067e7059441034fc7458221006bf6490a2103f3e6550441004fd73d814211cfd7650510006bd5458642006dc63d81210067f7259441014fe7358720064fc76c8540004ff7559121006ef5318941006bc6408520036bc64d0920006ee40d8941007af7448421004ff7359321006be65191210079c64d8d21034fc76487400057d7599110006be601912103efb7058041006be201912100df870505400367d74594420067c63d9520064fc7598b400067c75591200cddc7358121014fe7358a41005fb7050920014fe7358b101cf7810d9510006bc6519120004fe7610521064fe7218540067af63508420c6ed2058b10006bc52d912000cfc7059121006de75d8d4100cfc70d932103eee2158a4122f6e7510a21067e820c8520317ae755
  | 15 => 0xe73589100367d4159740006ed76c8621006ee73189410667c2059442037ae6550842004fd75d8b10006be73d912100cfc7059221006df635894103df671d0a2103eee2158841036be7519120036bc7019120034fd71d8141004fd75580420067e3259441036bc64105200067f651052015fae201912020eec41189410067e3159442006df6358141014fe73d931020fae5410821036bf4358442005ed72d072120eec4018941066bc4259321006ed52189410c6f860581211ffd47348421006ed32d89411cf7a30d95101a6ef20d8940207e55248421006de51d8d21005df7350621014fe731854003cff70d9110066ef20189100067f7558910007af7150842066bc649932112d7c75581411f67d1059740064fc73d9320004fd7398b4103cfc75987400047f75589100047f755824103ebf745931001cfe755832103cfc751854000cfc7098841007ae54d8941227ae4110a21006bc5219121004ff7358341014fc7359021006df6398941034ff7159310034fd70d8540006bf6410721006ef3118941005bc74487100367d4259442006ed431894103ef710987400c4fd7158b10034fe7418520014fc7359121014fc7359110006dc50d8d2103cfe71d9310036bd7119120006f731d8520006bf71d9120034fe7498b10006bc5119120006df65d8d2103cff7398642006dc40d8d2120eef4318941034ff7659321004fd709884125fd463c852101cfe7558021064fc7258242064fe72986420067f43d952001cfe7558b101279c74d8d41004fd7518910067ac3250842006bc5319120007ad43d894102d7c755911000cfe76d8142006af6410a2103ebf6190541006bd5459221004ff7359120005ed7110a210079f74d8d410067f31d9520006bc30d9121006ec32d8941006ee3118941004fd71d8142006ed3018941004fd7518540006bd5418941004ff73d9121006bf51d91201ce7d70d9510004ff7359320006de75d8d21004ff75580421ffe731484211e67d30d9520066ec5218940005f97008540227af6410a21014fe73d8542005ef7250540006ed311894110e7f7159441005ef7250721007ad5418941037ac4250940064ff7598b4017efa40d81421f67e105974003ef970d8b100067e20594420bedc63c852103cfc7650b101f67f305974003efb1058221005dd7399121006bd6419121006ee51d894103cfc75d8b10004ff73d91200067c43d9520006be43d9121006bc648852101cfe7518941004ff74589100667d7598910036f77158742034be76d9121006bf6499121004fd759872001cfe7559320036ec4258b40006bf641092003cfc7158b40036bc60908410077930d95100067f74d9510004fd75d8520006de20d8d410057f75585400067e735944100cfe7498b4003cfc7158a41035ee7290942126dc71d8d41036bf7319121
  | 16 => 0x8b4000cfc709874230faf5350842014fe73580211f67e705974000cfe7498740196bc50d9120004fd7398740036ef4258b4103cfc73d90210367c4059441034fe76c8740006bf5119121004fd72d8540006ec6288540006ef53d894107ddc73485401e76c20d9520004fd73d9121004fd711894009efa4058021014fe73d8940036be73191211e77820d95200067e725944100feb62c81200067c65189100e67e658874003cff70d8910006bf649912028eef63d0a21014fe73583210067f735944203eef63c86210367f405974001c7c75591200c4fd7688720014fe7359021004fd73d8941014fe7398a410067e73d95200067c7359441064ff75189410067c73d95200067d43d95200057d7510b10005f671d0921006ee7018941066f820583211e67d40d95200067c315944201cfe7598a41064ff751894001cfe75d93210c4fd719891000cfc70d8542037af7250842014fe73d8142006dc20d8d4101cfe7558642006dc52d8d41004fd7318b10006bf73d9120005bd7190a41006df63d09211ce7c30d9510006bf649091015fac2019120006df63c8521126dd71d8d4101cfe7559221067ac6350842006ae541894117ded729912029ebd6550441036bc6410921006ed651894101cfe7598b10005df7348421004fd7558b10005df735071003ebf745902122dec74c8621036f84058042006ed5118941066f42158442195be7619120004fe768854022eec41d8941066f72158442036bd751912015ebc1019120004fe7650520004ff75582420067c74d9510196be50d9120004ff7358242006f5611854003ef4311852000efb61c41100069c63d912101cfc7558841005f97088520004ff7059021004fd7398a4110e7c65105102f6bf6510a41005f67190941186dc6350941006bf6498520006df63905410057f7558241014fc7358221036be545804203cfe71d9320014fe735834220eec431894101cfe7558442317ac5150842036bc6490521066ec4298b4103eec2158b1000cfc7498740004fe7648540006bf65191201e67f20d9520006bf3219121006be52d9120006bf5319120034fe7688740005fb705094001cfc7558341006bc641852003eee7298841006ec53d8941006df63909210057d7510520207e55148421064fe72d9110006ec51d894120dee74484210067c659891000cfe7098a4103cff7598642014fc73d8542006bd2119121034fc7458910064fc7598b101cf7610d951000cfe7650510004fd7558910004fd7398841307ae5050842065ec7250720006bd6410b10006fb705911003ef67118b1030fac53508420067e43d951003cff75d9021006ee3018941004fe769092115dbc7050842006de72d8d41006be32d9120004ff7558b41006dc7358720006f431d854203def76484210367f41597401e67e30d9520014f
  | 17 => 0xcfc7098a41004fd755824101cfe7598b40064ff7598841005bc7448520004fd7558742004fe76109210057d7510721066f7219844203e7c2159441004fd7610720196bf649094022eec43d8941034ff765092003ebe4159221004fd7559321004ff75583210eeed2098b1001cfe7598742006bd5219120327ad75508420067c7558021014fe731891011ef710587400d67e6548740005df7358540006ef6518941004fd7699021004fe7610520006bf30d9121014fe73d812115eed2018940007ac6290541006be10d9121036be5498b41006bd71d91210367d745974003cff73d9221036bc7319120065ee72d0721004ff73591210047f75591200067f72d9510014fe7398b410c6f850d8121025dc735051003ebf6499221004bd74d8b10006ee65d8941005bc74581210079c63d9121006bc645812130fad3150842006ad32191210067d715974000cfc7098442036ec425884103ef431185420667c4259442066fb7058042006de60d8d41014fc73d9121014fc7358b1003cfc73984422d6dc42d8d4100cfe705884103ef46190540004fd76d0b10004df7358740006bc65d9120006ef63189410067d7059442006ee32584420367e4259441196bc70d912000cfe76885201e76c72d9520006bd651912022eec54d8941035bc7458242006cc63d8941144ff7159110005f970d0510014fe7318b1003cfc7518b10066be4259021004dd73d9321006de70d8d21005f7715094103ebf745922100cfc715931003eec6258a41035be7290841004ff7158242006ee7618941004fd7098b41036ef4298b410367c7459740004ff73d894109ef51018520004ff7359221036bd7519121006dc64d8d21034fd7018540007ac71508421f67f7059740006ec10d8941196be70d912015ebd3019120006be70d9121136bd40d911001cfe75d93200067c65d852003ef7101854000dfa76c81200367e405944101cfe7558b4000dfa70909400057d7510921066ee3298b10004fd7398b40004fd7318520014fc73d8910006bc31d912103ef81058021014fc73d9110064ff73988410067f3259442134fe7619110036bd7219120005df73589100cede72d8d21006ec60d8941066ee3218940004ff765042106ddc7348720006be51d9120006bc65d91210047f7558021006bd43d9321005df7350521036bc7519120004ff75d9121006bc6290541066bc4259021004fd76d0421004fd75d9320006df63d8121307ac105084203eef6298b10064fc7598a41004fd7498910006bf6450921146fa1058341216ed63c8421034fe7498720006bf43d9321066dd73d9321036bf71191200067e7059442006bd31191200067c7558241005df7348540064fe72d91200057f75581211f67d7059740014fe7358221006ef5418941006ee3258a41004ff7558021036ef725
  | 18 => 0xf16c00000104d03700f1a13c401300c0020010f801000001500000a03602c00613900d00b02701900918603a00002b00503600501e00000301100102901a06000100000901a0000090c411e00b01403b0920010000b301d00100f00000000f00000103d31100802000200200700000700e07200b00400002816100000100903e00005801a00707e00701400e5d60c906605a0050430006fd01b06b00a56803104000027600703600201f07801e1b100101d17400000200355955b00300b06400000223104f00001b68700100000211b1c90010a80450000550000110140250000e404238c0000080140078460310cd0e90a900500000e02607401200c0790180010000080060a900208403c21604901700800c00000a00204400800000803c06b00000802f00b11206f00102300401106e0055b701f02401300100300c00200b7cc0020020000033eb0013d200a0001d606903902800405b0c210b05600f00d01700416f02408d01907f00304d00000d02800003905c08d00900002900e00004200000e00303700100700200301e0013ed00c18901d01800000701100000100200601c05d02d11800000201d00600000000600d00a00707f01e03601b00609e00000c01200400306200007500031c00c02325a00400b04f05801308105900005101800100707c04d00000105500108f0300050050a500a06c00000100410c00001901500404c00015500003503700003f01100700000001153f00100000900000c01600d0020160ba5e40610180020000650040000130010040080020030240011720000c602000006800100000003400209e0230223be2392fe00000300b0270024f444000100701000f00000105600002403300212f02b0070da0010040020017ae00203205302800000034100800f0092306390050371450180043c900202e23501e00000200c00aa5f00507606e06500001c02601000200649e04305b00100700a0270050092f902a02804801000100000100500100002901700200001402b073299194fe7619120014fe73d911022eef43d8941064fc76109100067f6550910006bf64d092001cfe7558740006ef31d8941004fd755912030fad3050842004fd7318941006bd53d9121006bd72d912100cfe7098841036ef4258b40036f74158742004ff72587400067c63d951015ebf2019120007af6488521006df63105210067c725944123fad5410821004fd73d9221196be6090a41006ef72592210673e6550842006be521912115ebe3019120006ed329884100fea72c812003cfc715932000cfc70d912101cfc7558b41006bf65d9120006ed30d894101c7c7558241006f93058021037af6290942014fe7358740006be54d912102d7e7599110006df51d8d4103ef671d931003ef42198442006bf6408520014fc7359321
  | 19 => 0x1800c0000024561bc0070070011750000173d800f0000070d60016bb0050100060010030000000000030060050b801a00e06c00201401301506415003b00002b0000160200430020b816000f00000001000400900b11401500a06000100602c0000071af01201102a01902200d00869f0010180040bb01501601400101f0000840100040013330030210150170020cf00800200268900301000504c00326000000100006610e03900a01701200a0a001200500535003f00305603800100a0900ac08100300949b00001700d01d04400000103e0080010040120b002a02a19600200015602300900b04001c01500000501e0bd00000500a0350040002270000000030443dd00100001e00201c00000700700000000000000a03c00016f00007300000102b03200000a10c07807200500f00700100b5aa00b01304e00f2170040030090010660030f202b02800100540b01700a03632503d04003f00025e00100700402e00107100201f03b00600500c01502700000a00306215385500000600f01b1b702501532800600309a00201302a00000a00a39e0010a20040224370046eb01206a01f00714c0ba01600a0100360260000980f01630010300000030075560010100041f909c00f07c45011d00400000001408400400101300852d1c200705800d00300a00100400301001000500300a00001c05204d0000bf00000300103a50402900000202b07935301c05104600000030f00600001b17906d1680040630041420070d076900401301300506500f01a01107410c0296393b50a20a504b00400200c09e00600f00055701500500201001315200100400201d00b65809c00400f04f00104100401f37a20902003e0184c000b00c00c0000244bb0020850060c500200a01e00100103b03a04c00001939600061e00500600800100000000e03101100500500200002500934204000600700e02900100000101800000200200715201e00200f00b00800301900003102901902100100000000000e0fe07500003701f03500100600005d00700402f01100006501702f0521e600006800500502000008000b22200204f01200000405600102d01800000300201100000106201d2ad00c0462ce0000840000000010003c406a28600201101b00500001522701c01000200400000201d0001e049a16b00f0180020000000410000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9f8359464484e355f04b28c8901df8b10a32594410043fc2ae13168206a3e84cc9651040187ecaba4c2900031bd94725052000566c10a1b1a8200ae880594625040155d0439ec890032ab20943590210045f43e65b22426ac9c73551611080f1d90e992c4208037120d71108210056ac08a1b1a8200e3865193204800187aeab2085880022fe11735912100666b9ec5312822b8be86dd1214808b55d083aec4a08029ee0172597400045ec3ea7b2240018f8805d5644840159b07306c4a08032bd90725051000477c12eab222044da6811d1210840199ec7b9282908063ea1b704851001e1e3aca8b048400c5f751cd62440d593ce6aa6c990802b320d62189410043f43863b2a40068bc845d5601080f1f10e982c11080f0f1d654591100053c402e2b288400a6e85cc062504575590ca90c89001a2f21076485400043fc2ae6b048200c5c73d95624400159f06b10c4a08021fa1f30594410062e32ee690a2044aac8150c625040153d07b8ec890802b320d65189410071632ca5b224000aad82840644840155b04188c89080237e0d76109100046f43841b1a4200ad581143634841955908392c81081a8fa1031597400361f322ea216206ee2c2019464480efc5aeb190c89081a8f21131594423df63a08c631282008bf87590644845757500188c89001b8b9c965908410065bbb6e89084200aad82143644840d5690ca0882908fa9ea0273597400046fc1aeca122000c5f75dcd64440b51b90fb1a82908036950d71108210051fc2ac63224000c3d75d5364480010ff0abb6848804a8f613735974000672a8eec9084200c9c73d91414840159f06b2ec4a081a2fa1f52191200055c402ca3224245e2e54d5362504018d8ca392c8880ae2f21d545804200556c20603128200aae82d44644840147d0b31ec890106aba1351189410052f418e0b288207af0814c1600840117d0e3224290003a3d8d42109210046fc1ae231280008df835d564440018b8e632ac488002ab60a53191210045ec3e643224000a9d83103644848955902990c89081e2fe1d6490b100045ec3ea63224200e6751947625048955d032a0c4a081a2f21c64485200043f43ecab122044cad87d90428840d47d09992cba0002aea0031d91210665743eeca108400a3e850c4644800147d0a18ec890802a760e10191210061e3a8c8b0a4000aac8254464484011f700baac89080e1f215735824103c5e43a86b262000aad84cc4625040787ceaaa2c3a00030f1d7645812120e96c28e890842028dc835d8424400187aebaa6c89081b0f1d165487400061fbaee8b2240018ec865c841480010fd0f982ca2100387d4e531912100556c20e7b1282018f8805d5621040117b0fa96c890002b520d611852000566412cbb1a8241aae840c462504014bf06b8aca21112ab2055418941
  | 1 => 0xb0d38a8421002a760c50191210064e326e690a40008bf845d5624400153b07b8ec890003331cc62485100043ec3e60b288406a3e84cc9651080187cecba8c89080a37a0f71582420351f426e6b2882328be861d121480070f90ab86c890906aba13311894106716baac82104200ace831436250483b4e86b888410802abe19715084200567c1a823128200aae86508424400155d0418ec8909074b594715084222d57426a7b128244d2e651c9411046555b043aec8901429be0971594420061e32ce930a40068bc845cd621040147d0818eca900023ba1c31d894100574c0063b128262e2c6550842440018deca392c888002a7a0e10191210051f424c7b2a4006ab4844c5611080153b0828ec69080317197735052000667b98c4b028200e3751947644840153b08286c6a081e9da0470594410054e422cbb1a42419ad861c542108fd4db0539aca210021f61776509100146e41aeca0a4200aad840c4625040187cebb2082908029b60831594420054e41aca3224200aad84d4b62500014bb07082ca2100a37a1b73581410062e39ecab222000ab98094f64480014bf0ab86c690802ad20532191210062e398cab222000a9f8359064484011db0f21ec4a08f31e9db65c81200054e41ac83224200a5f855c363504018baea318c89080237e0d76505210051f42e603224200c9c73191614800195aa8392c8880021f61c31d95200070eba8c63224200a3f844c9651040195ac63a242108030fd94744852036557434a43224000c9c741cd6244001d18c7a1ec4a08022f61c31191210365b30aec2148244aac81590420840174902990c8908029b21562189400054ec18ebb224000aaf8254464484015c902992c221002b6e0175d8d410074631c643224200cad7318a415040155b0ba18c4a0802a7a0e65191210045ec3cca3224200c5f75d8d60504018bcebb1882908028f61431d91200345f43ea6322400087e87195644400117d0fb224290003271cf645812120d57426a03128200a6e820c76544001d18c6990c8908022fe1173591100351e422e0b288444da4311d12108401c5aeaaa0c4a08ca2fa1f52d91200046ec38a1b1a4200c7975d4360508018deebb92c88800317d9773485101e53d400e7b2a4000a79801cf654800153d07b8ec8900030f5d76410520224d7c3ac9a1442008dd8784363504011bd0e106c6a0803a518c64c85213771c100ca3224000acd8314062504a572d03ba6c6a09cf1bdc8655912000536c1063b2a402da3d841c1651080153d09306c69080a3720d76509100061fba6eab048400aba8094c64484b51bd0e39ac3a0002b920543189410355642264b1082008bd87cc8644840187aebb24c89000317dd763581212255740c64322420387c855c261d080153b07300c8908029b60831597400043f438eab004200
  | 2 => 0xd64d8d2120c7743cc4a148200ce552dd9210840155b093a8c4a080317dd4635812100717b2aa83128200ad88059763484011ef02b9ac4880032b50d761082100536c1487b2a406ac9c7355161d000187aebb208390802ae60031191200345f438623224200c9c73d91414400d47d09b9aca2113b2bdc8645852000566c1ce1b12825ac9c64dcd414840155d04188c89000e2fe1d54d932122d57420a3b128200aae8214064484019a8e630a4290002b3a0e70d8941226d3308e4a088200acd831436250401d4f02990c890803a3193638852100637ba8e4b222045e2d8519221484070fd0fbaac8880028fa1671d91200045fc22eab22400087f855da4244001998c7b92829081e2f21d43590210055a40aa8b088400a9e84143634840159d07306c4a081a8fa10315944203c7c43a60b048200c5c73d9541480014dd0a188c4a08063ba1b72505200054ec24cbb1a42008ef825d564484011bd0e39ac8880caaea0253d912022c77c32e22104200aea800c4625044953908b96c6a08031bd9772505100043ec2ee0b264200da7311c542108011bb0f086c6908031719773585201fd67416e3b1a42078bc87551648840153b0732ec8908031e197704851001c3f43eeab048400adb80597634840155d05080c890802ab60f6410a213ae3c3aa60b004200cac74dc962440a5d28c6a088290802ab211621891000753c0a863128200a3e84ccb654808995ee631482a0802ad60450d9121226d3c22e2210426fc3e7619464480010ff0ab9ac0108063d219711091006673296ec9084200a5c855c363504e955f08b10c4a0002a761075d8d4100556c10a63224200ace82997635040155b0418ec89000237a1c73589100063c3aee0b222000c9c64dcd6048483b4ac238a8421002ad20543189410046f43ec6b028206c3c645d442484070f90ab9ac890003a3610631894100c7c402eab204200a3d840c1651080155b06b208410987a318d42109210054f41cc1b224200caf641c9414800117d0e322c2900032dd9071509210052ec18e0b288200aad84d4f625040153d0c326c6908033518c71509210053d404e6b2884008bf845cd6008401998e7b12428801a2fa1c51191213564e39aa8b222007ae4814c9621040117f08baac890802a761352d8d4101c3e42ae1b20420387e87dd564480014bd06382ca2100a37a0e764854000636ba8ebb128200c3e75d9042480014f30018eca880032bdd8744842101c3e42ae6b222000e2f6550842440011bd0fb1ac090802bae0165d89410056b408a1b1a4200a3d840c565d008b1df0eb1485209e68fe117259441006c6398e8908420087f8758f65480011bd0db9a829080387d4e53d91200054f418a1b224200c6c65dc941440014db05082ca21003271d363581210063c32ee0a124000e2d65dc9411040155
  | 3 => 0x63128200c3e75d92614800155d0d2a0c4a08021fa1f655852000746aa0c7b1282008df835d5624400187acab8c84208021fa1c65589100653741420b288441e2e54d5062504011df04baac890002b620165d8d4100567c1ae23128200a6c855c0625048355d09980c4a08022fe1d64191200064e398c890a40008de8718d6048483958c83928288002a760f71d91210064e39ec8a0a4006ab8844c16010801c5aa8a88c4a09dba510473584423961f3b6ca322400cc6f759d4625040153b06286c890802abe09311912100746a1e603128200a6c8258f65440a55ad03ba6c6a0803a318d43189410051ec2062b288400c9f645ce644840193cedb26c690802b960831d854200557c22e031282008bf845d9424400187eca3a2c488002aba0830191210062e398cab0a406bc9c73951644400147b0b31ec8900022f61f531912003656c16eca108400a79809cd65d00015b100baec6908031b5d752d89411f53d40062b2e8000c3f7519161480014ef02b1eca9000237a1c73587200055d400623224200acd83980625040199cedb18c4a0803175cc73d95100062eb98e7b2a4000cae541c9644400187ecb3a4c29000a3720d71189400061fb2ee890a200387c855d8215000117f0eb28c8900029ee0172594410045f43ea7b224200d94731d1210840187eea3a2c4880028fa1431191210062fb2ee6a0a4000c3c65dd161480491b90db9ac0a08022f61f6410a210066639ec4b0282008f7875846150001d1a86980c4a08030f5d475d91200062e3a8c6b028241aac84544625040156902a1ac2210033958d711082100727a9ca63128245e2e75d9042884010ff0ab9ac48800317dd47359110006363aee4b224000c5d75d8c41484010ff0ab86c810802b320d711894122e56326e4a0a4041e8f8350c625040147b0818eca9001a2fa1f521912100556c10603224200a6d821c1651048935f0638a842100317d9773585200054ec1ce1b2242078bc845db414800d968c938e84908022fe1d631912003c7643a64b162000ce7621c54250479cd6c5b2e40900030f5d074d95200053cc04e6b28820387e87dd562440011df04bb28488002b320d411894122657b18e4a088200a7a809cd651040155b0828ec4a0802b3a0e10189410061e3a8c8b024202ccc738c9611080165f0ab8284210030f194745891000476c3863b128200a5e8384165108019a8e7b8ac4880cb2e9db64c81200653741060b288400a3f844c165104018b8e7b2a4288002ab60873d912120d57424203128200aae821d7644803359904ba6c690803a360863d91210043fc2aec10a8000a79809cd65108015cd02286c4a0802ad205631912006656392c8a0e4200c3c65dd1214400159b07328c4a081a8fa137259441226d2188e4a088200a3d84ccb654408995ec63a2421080237e1
  | 4 => 0x1480014dd0521eca880323b2097610910005d240a87b12820ccac625d021500199cec6b8884108028f21172d951000476c38623128200a3d84cc965104014f50018aca211dfa910632584420070f428c9b1a4200acd83083625047d4f100b8acba0003a3d8d43189410053b408e0b288400a3d8498f65480018b8ebb9ac8880028f21173d95200043ec3eca20a4019ace86dcb63484018b8ebb9ac4880030f595740874001c3e42ae6b04846ee2e2019464480070f90ab80c4a08028fe15641912000536c2863b12820087f855d842440019a8e7b8ac8908028fe1563d91200351e42260b288200ccc7318960504051bd0fb9ac48800327d9373585200657441260b004200a9d84d4b63484014bd0a326c6908023760f715824200746318c910a420387e87dd5609040159b05306c6a08029ba0831597403c75220a64b088400c5d65dcd21d00010ff0abb6829000e1f2157098b4100657c3ac82104200c9c7319160484014df0498aca21002b3e0974d8d2100578c0063b0a400387e85dd942440018b8ebb1ac0a08023b61c50d89412255740ac82104200ace8308362504f1c5cea990c8908029ba1770d894100567418a031282038bf875536448001b4aa8b888410802aee01521912000572c08a1b12820c8f4874c561108011db0f318c4a080a3720d755911003c5e43a86b24420c8ec825cd640848355d08288c4a08031b1d4625814110d1ec26e4b2882009ad831c542108f1c5884992ca2091739e1971108210061fb2ee8b0a400c8f8874c160108014790ab1ec8900032d547765044100557414a63224200a5f835c565d000517f0ea1ec9908030f5d7641092000557434643224200aaf8550c62504011dd0fb12c0a080e1f215735891006666312e731282008bd87ccb644800199ec639282908062fa1b744854000657bb0e4a08823ca7a800c765480051bd0fb9ac22100363dcc72504410062f3aec62124241da5811c941104011ef02b9ac8909af279ce54d93213b64e3a0e6b0884018ec825d941c800187aea324c2900030f1d7745912000747c26c63128206a3e84dcd65d00018f0ebb82c8900332b94b765084200556c10a03224244caf7319221484011dd0e286c4a08031719773485200355a42462b088441caf435d8420848974902a1085108033518f71509410054ec1880b2442028bf8750f644800195aa5bb284210aeae20152191202d64e3a6e6b088400a9d84143634840155b09080c4a08032ddd8744842120f17c2aa831282028dc835d5611080159f04b2ec6a08030fdd764581210043fc2aed20a4000c9c7418d604840147908b1eca880030f5d074d951000537c12c7b2a2000ccc63dc9605040147908b9eca88002ada0450d91211fde340ee5b1a4278e2d754c864484434eb02382ca2080237e1d65d8d410075240a8
  | 5 => 0x906aba1053189410046fc1aec90e800387c855da424400153d06206c8908032b1d3624851000746996603224200c3d75d9041484655750018ec890003a3d0e311894100556c24a6312820087d87d9442440191d904ba8c4a001a8fa1220594410054ec1cc1b224200a3f855c3644848355d09298c4a08022fa1c50d91210054ec1cca3224206c3c645d44148089a5aca39282208062f211764874000747a18623128200a3d850c764484015cb02280c4a08022f61c5119121224d743ee89084245e2d75d90428840153b06106c89081b0f191759912000666318e4b0282078ec874c962904191d904b9ac88801b0f9c965908410051f42863b22400087f855d94244083b4ca8b8884108030b594725044100476c38a03128200cac741892144001d4902990c89080237a1c63581410063632ee4a0a4000e8d324c064484014f700b8acba000393d4e53d894120c77c32e3a1442028de87dcd64440194dd04382ca21002aba13321891000747194623224200cad7518a41504014f30018acba00022f61c31d91210054f41841b224200aaf844c462504018b8c6ba88290906aba135318941226d220ae22104200c6c651c9414400d47908b92ca20803351cf614852000477c3ac4312200387c855d841480070fd0bb82c9108021f61e63d9510007472a0c7b128200c5c73d956148001878ebb22c2900022f61f64107210062eba8ebb1a8200a3d84881651040195ac639282208023ee01755884100557410e7b224200ae9800c462504014db0bb86c4a08b69b60870594420052e41ae2b288400aad84d4062504efc5ceb190c890802a7a0c50191210054f424cbb1a4224a9e86dd3635040117b0f318c890803271cf765044103656324e5a0a4206a3e84841651080193ee9b9ac4880028fa1663191203e537c12e0b288400aeb805946250401c58cb290c8900028fe1172d951000657baeeca108400acf83594625041955904aa2c8108028fa1271d95200361e322ea32242008bd870c4644800153d09326c690802aba08311912100667b1ee4b0282068be87140644840157100b2ec8909074ba1474484210cc6e436e6b024200ab9800c764484011bf06baac8908caab60b71d912037f16c10cbb224006cac645cb41484ef95885b9ac42081e3d20573590210055bc0ac7b2240008fb805d5640848995c82bb084108023de1d61185423171632a8421240028ef874cb62504018d8ebb92c888002ba60253d89410045fc3ac632242008df835d561d00f155b07190c890802b3a0850d8d4100667b9ee4b222006a3e840c165108011bd0e31ac4a0802b6e0175d8d2120d57424ea3128200c3f741d5609080117b0fa90c890802b3a0e65d89410043f43862b2884028dc835d5644840f9cca3bb2421091369dc874484210074631e863128200c9f64dcd4
  | 6 => 0x747b18c520a8200c5d751d763484430f90cba882880029e60031d9520226d2208e4a0c4221a3d84dcd65104b553d0828ec6a080333dcc72591100046ec3ccbb1a420caaf87590420840187eca3a2428800393d4a52d8d210046f438a1b1a4200e2f65508424808b958c9b9282908022f61f32d91210345f43e643224000c6c751c9644400147d09996ca880032bd90725052101c3e42ae1310820087e871d562440014b906b8acba00029de05325944100656aa2ec210420587d87d9441440070f90abb482900fa9e20172597400046f438a1b1a8206c9c645ce644840d968c8b88848801a2f21173580210061f3aec82124200c3c651d12144001c3ea729ec8908021fe1570984420072ba8ca3b1a82008bd87143644840117f08b9ac8900033518c71509410061e328e8b0a4044caf7518a415040153f08b2ec690803171cd65487400667210ced2124200aad8414462504011bf0eb2ec6908022fa1c31d91202d70f2a6a9b1a820ca6e820c565108015cd02280c4a08038b551521894122c77c12eca0e4000e8e320c46448401c5aca39282208032bdd072591100062ebaec62124200e1e7518c6448401878cbba2429000237e0d765072003c7c43a60b00820387e86dd5624400193ce7b24c8908038b19552191200361e322ea20e4200dc7835c442084191dd0f218c4a08023ee0175584420046ec1cec90a8000ad4835846150801d1b04318c89081e3d205735912020d5642262312820087d85dc164884071df0ea96c4a0802a7a0c75d912000536c1063b2a2000abb80597644840174902996c89080a37a1f735874000637baec4b028200ace83980625040159d05306c6a08033318c725052100556c20a1b128232aac8654b644800d95ce4bb48420802ae60253d91210045ec3cc63224000a3d84841651087f5ad03b96c69080e1f21570185420052ec28e9b1a4200aad84cc86250401d18c631482a081b8ddc565504410046f43ec6b1282008fb805d5644400117d0fa96c890802ae60253191200055a40a87b264200a3d84cc965d00018f0cbb8282880022fa1c31d91213bd57410643224200acd8384362504011bb0e286c6a080e1f215735802103c7a40ae630a406daad8298c64480011bd0e206c6908021fe1f6510910007173aaa83128200c3c75dd162440018becbb9a4290032aba0b645092000557436863128200aad84cc0625040117b0e288c890002ae60031191210055ac08a032242068bc845cd60108018deca39282880029ba0831d952001c3e42aeda0a4000c9f76dcd41104018f0cbb824290002ab61370d894100556c26a5b128200da7311d1210840155f08a88c4a081e2f21d545931000536c2e61b128200a9e83980644840147b0a188c890002ae61350d81410055742665b122041aae8414062504011df0eb10c4a
  | 7 => 0xa7311c941104194d904b82ca21002b320d65d894100556c26a63128200a7b805c565108191d904b98c4880023be1d63189411945f43e65b224045aae841cf6250401d1f06990c8908022f61c501912100637ba8c4b028200e2d54d4462504011ef0eb08c290113690c4715084200537c2ae03128200a3f844c165108010fd0e18acba0002baa0253d89410045fc3aca3224200a6e85cc3625040d974ec32640900fef120d41484212265620aec21042008ef825cd64440018bee739acba0003171cf65505100064fba0e6b122003c3c75953644800199ee7b92c890802ab615431894101e1f3aaa83128000aad83950625040159d07086c4a0802aba0853191200043f438eab048400ec6328c5611080153b083aec690802ba20165d89410051fc2262b288400aad8414c625040195ae63244290803171d76358121064f243a829084200a3c8458f65480199c8c4b8884880e69ea0073d951020d57c2e8631282008bf845d921d001995884ba0c4880021fa1f65591202d54f426a5b1a82028dc835d921d000155d0418ec8900062f21974085402255740e863128241da5811d121084170fb0fb288490002ab60831d912100656baeeca108400c6f65dc9414800147b09996ca900029ba0870594410345e422eab108200c3e75d90414800f1f10e982c010803171d473591100045ec3ea5b224200c9f64dcd214800154902990c8908022f61f521912000746aa0c63128200e2d54140625040147f08b1eca90003331cf725912115d5d404a63224000cce7618c62504010ff0ab9ac8900021fa1c31d9510224d7c30e2a1084038bc87551644400117b0fa9ec890802ada04501912101c3e42ae13088400a3e840c765440191dd0e188c4a09072b19072505200045ec38a3b224062b2c855c1421080159d04286c69080387d4e53191200046ec3ccbb1a8206a3e849cd65108b5d2e8718ac2211b28fa16651912003556432842124000a3d85cc36448401d1ec7a18c4a0803871cd655044101e1f3aaa83128200c3e769d4644842547b0838acba0002aea0253d91210051fc22c7b2a20028dc835c7605080199ec6392c0a080a37a1b73581210045f438a3b224200c5e65dcd21d00051b906baac3a0003171d473589100062fb9ce6b28842d87c865d4424800f1f10cb8084880ca2f21f644852000557416a23224039c7a76d97104400193cec326c6908023760f715834222d5742063b12820087c865d4424408935f0eb148520986e320d71508420054ec1c21b224200a5e8308165104015590ca10848800333ddb734842100556c16a23224000c3d65dd121d000f96ca3bb28220803271cf64585200064fba0e6b2220008ee8718960504014b90ab86c69080e1f215761091003d5a40a86b204200a748158f654800117d0fa9ec89000317dce73594410
  | 8 => 0x8baac4880031b19772591100055dc02ca3224200c5f65dcd41440015cb0418ec290112abe0f6410a210056c402ebb1a8200a9e83080644845b47b0838aca210028f21570d91210061fb28e8b0a4044caf651c941104011bf06b8ec0a101b2b19172105200045f438c8b02420087e871d5644400155b083aec4a080317d9773591103df62208c63128278cac425cd621040153d07086c89081f0fdc565504410051ec2063b2a2006a3e841c1651040195aca39282208031719773505100062e31aea2124244cae611d121084010ff0fb2882880323b20975591100054ec24c1b1a420587d870c765440010ff0ab80c4a08022f61c51d91210054fc22e5b1a8200d8c731c941104070fd0bb82c990802ade0532191210164f39e87b2642028de87dcd61c80010ff0fb28829000e1f2167610910006363aec4b028200e8c64dcb63484010ff0ab9ac888002b3a0e65189410052ec1c20b288200aaf83590420840153906b2ec890803a355363189410045f43ec8b0a400ccac425db42084010fb0f982ca2080317d9773589100047dc02eab122070a3e86194644806555b0439ec8900021fa1c65585200361f3a2ca10e8000ccc73dd9210840d47908982ca21002ad20563d91200043fc2ae6b04840c8ee87140625040187cebb24c8900028fa1730d912100557416603224200ba48150c62504ff47b0939aca2101e2f21d54590210053c402e4b28820087f8758f654400193ee839ac890802ae60031d91200043ec3862b288400a3d8598c64480051b906baac48800317dd773589100043ec3cc7b2a4000a9e839c3644840159b04286c6909ab279d954d8d410070eb2ee6a0882008dd8799363484051b906bb2839000327dd3735912100476c3cca312825ea3f845c565108014db0a188c4a0802ab20931191210351f420e2b2e8075c78754c1609040d17d0f990c8908030f9d4649852003c7c43aa0b004200aad82d536448001d18c7196c890802ab61031d89410053cc0062b288400a6d820c1651080159b0532ec6a0802a7a0e65d91212d54f420ebb1a82038bf8755364484018b8e7b2a4290002e3e0d71508420043fc2ae130e840387c855db42440015b700b2ec6a09072b95176108210043f438eab224000c9f74d8d604840156b0818ec2a101a2f21173580410043fc2ae030a840087e8719564480f5c70a0aa6c0a0802ab61273189412d54f420a1b1a82008ef825cd624400187eea322c09096ba310b63509410351f420e0b288400ccc73dc9644400117b0f328c8900031719773589100054fc1acbb224200a3f845cf654808355d08180c4a08029b60a43d951016d1ec26e6b2884068bc845d84244089b4882b8885108038b552501894100556c10623224000c5e7518c644848bc5d0a32442908023b61e43189410351e42264b288200d
  | 9 => 0x64109210066739ec53128200c3d651c9411040156f02b18c8900023be1d621894000557410a63224212a3d84dc965d000155b09a90c4a01bb8b608651912000657bb6e4a088200aae8290f644400517f0ea1ec8908023be0973591210046fc1aeab0e4000a6e850c762504018beea31ac0a08021f617765052000666398e4b2220068be870c4644800153d09a96c690803271d3735891022d57420a1b128200c7875dc162440010ff0fb2884900038b55352189400345e422e6b12205ac9c64dcd4148001998e7b92c4880030f5d475d91210052ec18e0b288439a7a800c765440331bb0e106c690802baa0253189410056641ac43122000e1d85193634840187eebba2c488002aba0850d912100566c1ccbb128200ae78150c6250401d18e4326c690802ae60253191210061ebaec930a4000acd8384062504014dd0521eca90002ab60b31191210047bc0ae6b224000cd776dcd210840195eedba24210802a720d641911000c7c402eab088400c5c7518d60484014f30039eca8801a2fa1c511912000747b1a643224200aad84d4862504070fd0fbaac0108021f61c31597400064fb26e6a0a42008bf845cd624400f4e902992ca2080a3720d755872001e1f3aaa9b0282008dd8710363484011bf06baac2210329ba0a73594420054ec20a3b1a8200aaf865c14210801c5aa9a90c4a0802a7a1051d8d2100637b2ee4b222000c9c64dcd6148089b4cc238a8421003a395063189410056b408a1b1a8200c3c655d261480194d904b8aca2103279e19711082122d56c3ec82144200aea800c762504010ff0ab84c42096ba5107735844200536c2e60312820087e87d956444001878cbba2c488002ab60b30191210061f32ee890e8000a9d830806448407878eaaa2c1210022fe1d64191103ed1fc22e0b28840087f855c364484010fd0e3aac120802aba0b31191210046ec3841b1a8200a3d849c7654800155b09a88c4a08028fe1173d95100052ec1840b288206c3c645d441484011bb073b2829000327d93735812100574c04a63128200c6c651c9414800187eebb22c2900023be1d651894106476412eab204200a3d859c76448089d4d03b2085108029d60470594420051ec2664b288400e2f5294b6448401c3ea92a6c69080a37a0e765052001c3e42cec20a4000a3d850c4644840717f0eaa6c99000a37a0f715834203556432842124206c3c645d442480199c8c538c84a0803a361063d894100556c20a03128202cd4738c561108ed1bd0fb1a82908022f61c31d91200345f43ea63224200aa48150c625046517d0f2a2c12101a8f21171594420061fb2ee890a4000a3c8558c644800155904b20c8880022fa1f645812101c3f42eeca0a4000c5c65dcd64440010f90cba882900028f21564191200054f420ebb1a420387c855d9424400d179
  | 10 => 0x2880000e020030000781ac020342320040e00000602c15008066a04000080521a87987d0922f80000201c4800501000c00c000040320543b800000004440470c61ac0200227c098009fa01603001062000024290060020003b8090120284c80000872e38834076060010920100b82a04800403c0000100c00000814004000038070260e03c01800c0280080e0280080003302c1c56b12c5aa4900213e00005c09001006094720020080746a02f002000188250320002f047000008238470800782c809204054079d500817c0200100c0203e8af000000870050f60197200300019004023086280000030000340400402201941826000018000bd0441980702b000010018860082340a00e2c8149388000022482908902e280a100106c0000781302019c1b8130900004b80e310040048550020802082500201c0f00600e0a4030ac5640c8018000702280700503206006826000474038fa02e0041f80a004000008781820140480200217c0009e0000101400100f5d02700002e0101680a3581c800807002000180590100c00982f01e00c0980401a0283101d01601401158246004068cc00c03c0312933a00000050144054008044f20081185900a0580504400209c0a003056004010210da03801807072004058000000100114302601c300000780002c000044050018bc00c01c0480f0000023702c000088028000da3e40480a03c018148220020000600d030085af02a06608078023012acc070010001044d80501c0000001f00005812045008000008010043404f85f0260100000a002038010170040e8390010020000087706601c2693600c0ec090050000600100705260000018002a1c0700022e04c0001a0001a0218005440981081703a0216080e0180165800000632c0100000001801b18e9b9a42108028f6173019121226d3394e321482008fb805d564480011dd0f21ec4a0802ab60853191200657241262b088400cd473dd9210840d958c9390829000333dcf62581410061e3a8e8b12200ce2e755904208401caea328ec69080297a0e1059441007472a6c63128200cd463dc542484191d9043b282900029761464d8d210061fb2ee8b122041d2e651c5421088355d09398c4a08868f61070594410043fc2aec20a4000a5e851d3634840155b05a88c8908eb1e9d930d95100351f426e4b2e8000c9f7418d604840117d0e28ec89001a8fa10715944220e56320e4a0a4200c9c73d91214800155f06aa0c4a08030f194744852006674312e010a800ca6c824c565108051df0e996c4a000e1fa1b75585201965c386c8a124003c3e7555161108d793ced2a6c6a08030f5d7
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40000c000274828c00048e3280e6006895d4814c8644840103d981947448510006895518114062504016849150f3018941006a1d8c8150c62504894a49158c7448421224a9245835904208401684914c93019121226896548150c62504f79848420d7110821224a9245849cc62504892a491615431894122529245435d842084f7a87832054318941006a118c814c864484016849150d301894100703594731c94110401c0d65dcc72504410072158d435c4420840182d875505018941226291c5869c542108898a44161c3118941006a1a0464dcb634848982e825d7641072122689a548150c6250401a26752053219121006a118c8150c6250401684914cb3019121006a1e0c814c8644840103d97a17301912122469261435c442084f7a844120d7118941
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x94c
  | 5 => 0x94e
  | 6 => 0x5
  | 7 => 0x2
  | 8 => 0x138c
  | 9 => 0x138e
  | 10 => 0x98c
  | 11 => 0x98e
  | 12 => 0x3
  | 13 => 0x150c
  | 14 => 0x150e
  | 15 => 0xa0c
  | 16 => 0xa0e
  | 17 => 0x180c
  | 18 => 0x180e
  | 19 => 0x209
  | 20 => 0x20c
  | 21 => 0x20e
  | 22 => 0x140c
  | 23 => 0x154c
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0e
  | 27 => 0x1409
  | 28 => 0x140e
  | 29 => 0x1549
  | 30 => 0x154e
  | 31 => 0x289
  | 32 => 0x28c
  | 33 => 0x28e
  | 34 => 0x148c
  | 35 => 0xb89
  | 36 => 0xb8c
  | 37 => 0xb8e
  | 38 => 0x1489
  | 39 => 0x148e
  | 40 => 0x1849
  | 41 => 0x184c
  | 42 => 0x184e
  | 43 => 0x409
  | 44 => 0x40c
  | 45 => 0x40e
  | 46 => 0x160c
  | 47 => 0xd09
  | 48 => 0xd0c
  | 49 => 0xd0e
  | 50 => 0x1609
  | 51 => 0x160e
  | 52 => 0x1889
  | 53 => 0x188c
  | 54 => 0x188e
  | 55 => 0x138956
  | 56 => 0x95394
  | 57 => 0x14c9
  | 58 => 0x2c9
  | 59 => 0x150996
  | 60 => 0x1649
  | 61 => 0x449
  | 62 => 0x1049
  | 63 => 0xb0214
  | 64 => 0xb0216
  | 65 => 0x20d
  | 66 => 0x154214
  | 67 => 0x40211
  | 68 => 0x40a
  | 69 => 0x140d
  | 70 => 0x40214
  | 71 => 0x40216
  | 72 => 0x188214
  | 73 => 0x140b14
  | 74 => 0xb1414
  | 75 => 0x154b14
  | 76 => 0x155416
  | 77 => 0x155414
  | 78 => 0x41411
  | 79 => 0x41414
  | 80 => 0x41416
  | 81 => 0x189414
  | 82 => 0xb8294
  | 83 => 0xb8296
  | 84 => 0x161494
  | 85 => 0x160294
  | 86 => 0x160296
  | 87 => 0x148b94
  | 88 => 0xb9494
  | 89 => 0xb9496
  | 90 => 0x144d
  | 91 => 0x185496
  | 92 => 0x185494
  | 93 => 0x41494
  | 94 => 0x41496
  | 95 => 0x161496
  | 96 => 0xd0411
  | 97 => 0xd0414
  | 98 => 0xd0416
  | 99 => 0x40d14
  | 100 => 0x40d16
  | 101 => 0x160d14
  | 102 => 0x160d16
  | 103 => 0x189616
  | 104 => 0x161894
  | 105 => 0x161896
  | 106 => 0x104c
  | 107 => 0x194c
  | 108 => 0x40451
  | 109 => 0x40cd1
  | 110 => 0x44411
  | 111 => 0x45611
  | 112 => 0x41651
  | 113 => 0x41a11
  | 114 => 0x165611
  | 115 => 0x45891
  | 116 => 0x41611
  | 117 => 0x9ce
  | 118 => 0x24d
  | 119 => 0x15cd
  | 120 => 0xccd
  | 121 => 0x29616
  | 122 => 0x104b91
  | 123 => 0x24215
  | 124 => 0x41296
  | 125 => 0x41316
  | 126 => 0x40cd6
  | 127 => 0x40e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1605
  | 6 => 3119
  | 5 => 1430
  | 4 => 32
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
  | 7 => 2*((h/542+packedAt gbK7 (59385+(h % 542)*11) 11) % 1605)
  | 6 => 2*((h/1067+packedAt gbK6 (149712+(h % 1067)*12) 12) % 3119)
  | 5 => 2*((h/476+packedAt gbK5 (84370+(h % 476)*11) 11) % 1430)
  | 4 => 2*((h/24+packedAt gbK4 (2240+(h % 24)*5) 5) % 32)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff07e01f03f07fff83e00f067b31fe20fe67
  | 1 => 0x7803f8001fffff81ffffffff19a4ce603f1fff
  | 2 => 0x8003ffffe003fffe0ffc000fe1c70f87c7e387
  | 3 => 0x3fffffffc00000ffffff0fe07f007f803f8
  | 4 => 0x3fffffffffffff0000000fff80007fffc00
  | 5 => 0xfffc00000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x887b01628720b02a95a320a9020910ae206e63
  | 1 => 0x508828000945548122844a6208a046600b14ad
  | 2 => 0x1115aaca002694c0b69014c61470b82c5a386
  | 3 => 0x22394d6d2a800288c739588b607b007700350
  | 4 => 0x4442e71b1cf38e71c0020600dff80005bed800
  | 5 => 0x6780001c00c00c4100401800fdf6ed50000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40515
namespace PEqualNP.Outside.L_meta_40515
open PEqualNP.Outside.L_meta_40515.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 13 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 75 := block_range (n:=75) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 75 := bs3_3_0
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
theorem bs3_4_480 : Interval s3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 50 := block_range (n:=50) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 626 := (concat (concat bs3_4_0 (concat bs3_4_96 bs3_4_192)) (concat (concat bs3_4_288 bs3_4_384) (concat bs3_4_480 bs3_4_576)))
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
theorem bs3_5_576 : Interval s3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 699 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 bs3_5_288)) (concat (concat bs3_5_384 bs3_5_480) (concat bs3_5_576 bs3_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 42 := bs3_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 32 := bgb_4_0
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
theorem bgb_5_1344 : Interval gbAtlas 5 1344 86 := block_range (n:=86) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1430 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat (concat bgb_5_672 bgb_5_768) (concat bgb_5_864 bgb_5_960)) (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 bgb_5_1344))))
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
theorem bgb_6_3072 : Interval gbAtlas 6 3072 47 := block_range (n:=47) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3119 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672))) (concat (concat (concat bgb_6_768 bgb_6_864) (concat bgb_6_960 bgb_6_1056)) (concat (concat bgb_6_1152 bgb_6_1248) (concat bgb_6_1344 bgb_6_1440)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1632) (concat bgb_6_1728 bgb_6_1824)) (concat (concat bgb_6_1920 bgb_6_2016) (concat bgb_6_2112 bgb_6_2208))) (concat (concat (concat bgb_6_2304 bgb_6_2400) (concat bgb_6_2496 bgb_6_2592)) (concat (concat bgb_6_2688 bgb_6_2784) (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072))))))
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
theorem bgb_7_1536 : Interval gbAtlas 7 1536 69 := block_range (n:=69) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1605 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672))) (concat (concat (concat bgb_7_768 bgb_7_864) (concat bgb_7_960 bgb_7_1056)) (concat (concat bgb_7_1152 bgb_7_1248) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80feeaeeeafce8cc80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4243115136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40515.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,2]⟩,⟨.and,[1,2]⟩,⟨.or,[0,7]⟩,⟨.and,[5,8]⟩,⟨.or,[4,6]⟩,⟨.and,[8,10]⟩,⟨.or,[3,11]⟩,⟨.and,[2,4]⟩,⟨.or,[1,13]⟩,⟨.and,[12,14]⟩,⟨.or,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243115136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243115136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40515

open PEqualNP.Outside.L_meta_40515 in
theorem PEqualNP.Outside.L_meta_40515 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243115136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243115136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
