import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40459.Model
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


end PEqualNP.Outside.L_meta_40459.Model

namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40459

namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1003800716300081200d002000180005c1912428a85000850000000044000000000400444d50c80200089004c000020020e013d53102bea6884f553329f2a0615e53d067ea890dd946329eaa0637b504877080186750c31da28a873e50d0eb8a6906750e31cf29881e521086bea6904fd5130af2988178504867aa9986e14143ba28a413d54c827ca818cfd51109e2a2211d531027aa8185b54a31b7a92613f54482dca518cf550329f2a6413f548c27ca9995b94810ba28a876c52442bca7a14f55243bc2828775518cb5ea4a1db54810b6292613c54482baa7a14f95330cea1a619d438ca7aa998edd45439e2a24377514833ea6a1dd94420afa9a437551082eea2a1eb14943ba28a615d53d0678a9185bd4943bda82879d43cc376a0a1e754c409f2a0873e54cc6b8a690e750c32aea98813d539027ca0205714d109f28481ba501027ca9884f141439f2a0653d54c437081985dd4530b7a9221385050e78a8985b14943
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa15880014430100032f2b5214143a6181430c6986050c32a6181438ca986050e31c3189531021c6550d30c550c514c2996310330cc1445050f0f6254c40b818121087146154c40ccd445050f0d4314930c91485150f0d4394a31c550e518cb176154c40ca1485050e1d63953108758e54c83186054c40a618143cc2396510030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x400005811886154c40a10e0a1ca518d107050e518cb04310c0a9881841846054c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => 2*((h/28+packedAt s0K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s0K4 (2457+(h % 58)*7) 7) % 91)
  | 3 => 2*((h/15+packedAt s0K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s0K2 (245+(h % 8)*3) 3) % 5)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffc07ffff03fffffffff01ffe3ffe3f
  | 2 => 0x3fff01fffff80ffffc0fff01ffffe07fcf1fc7
  | 3 => 0xc07ffe03fffff01ffff03ffe03ffff81f3e3f8
  | 4 => 0xff800003ffffffffffffc00003fffffffc03ff
  | 5 => 0xfffffffc0000001ffffffffffc000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x429114288471224500b2cb4a94b08aaa156e1b
  | 2 => 0x13224c514890e48b2c0555295956a24ccb16c5
  | 3 => 0xb244289a512241d3555026ac526ad30963a368
  | 4 => 0x2470b163a244891c9a6980c1838d1c71bc01b6
  | 5 => 0x3878c183c3870e1ee38e38f1e00e1861fed800
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40459
namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x20000071a0000001c310000810000300200028600200fff32fe40fc20bd41bd43fc10bc40bf43ff31ff20ff42fe43ff41fc32fd40bc42fd21fc30fd42fc40be40fd30fe20fd43fd41fe42be42fd20ff30fc42ff43fe21fe30fe10fe41fe31ff10fd10ff21bf41fc41ff40fc31fe32fd32fc21fc43fd31
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x48006898002c341030008cd8dc600c4c01f804142c74add42000280010004c08000400040404802c0c3404d05000343801b444000000303c7806dea4a0cf552419eaa6613d54cc6eaa2184f54f41afa9a21af525067ca821cf55131dd280813e544c6dea4884f55031d6a94815c534827ea9194f950219f2a4413c548427aa7204f550329f286876e529027aa8184f552219faa0413f548427aa6205bd49309ea88855d5304278a4a1f54c431af298216d52042dca4084fd51329f294853e501027ca5204f950319f296833e52d0ed8a4a1db149109ea8c812c52506daa5204fd5321bba8a415e538867ca8194f950109fa8a8776510c27aa918cfd51109f2a6613f544867ca820db548309eaa4413e5010adea4a1cf553109f28485ac5250e7ca1a0cf150209eaa4873e54c8278a0a0d7d4d209eaa6659f5350f5885904f952219e2a2212e529035ea4a1cf141439ea88815d538867ca4204f151209f284815c53442eea2985b14930d621443ac52506eca3995b54b319e2a2613d540867aa9906b10920d6216653e548c6e8a2905b149419e292833f544c3588410cfd52309ea8c856d528c678a990cf95331dba8a837551cca78a8994fd5120d7290853d5390a7aa3a1cf55010d6210653f5350678a9194f54c429f290853e54c4258a4a1cf950309f2a6656e52cc678a9185d145309e2a2436e520c35ca5205b94a31
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe40002508c051002000012009608d584548ca2c62551318b189511022c6255031c910a51cca2c6254c408758c54c872442145208b98a50d062c6255330a358c420ca2d65108328b98b548423860551318b98b540822c62553108758c540830e5310a21a9584420870c53109208b98b548c22e62943438b18951d0e2d65108218d584540822c6254f41
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => 2*((h/30+packedAt s1K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/58+packedAt s1K4 (3618+(h % 58)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s1K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xe0ffffc0fe0fffff0783e0fffe1e07ffd23e4f
  | 3 => 0xff03ffff000fc1fff803ff07ffe00781e3cf8c
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20080888240200002904a108802290a404d095
  | 2 => 0x4a3191064894b0cb02a148d332142558d2264a
  | 3 => 0x865aa2921d29135558427a45d540560d634b8c
  | 4 => 0x14a344249181a5a694e8108669996011b80d60
  | 5 => 0x18c38738e1ce39f8e7739ce071118461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40459
namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8624604000004809400001200b045003016440101fe42bd43fe41fe20ff40fc31ff32ff41fc41fe21fd21ff21fc10ff20be42fc43fd10fd31bc42fe10ff30ff31fd40fc21fd41fe30bf43fd42fd32fc30fe32fd43fe40fc32ff43ff10fc20ff42fe43fc40fe31fc42fd20fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1a3410000280000000a80021401b70080d700581020000010003808508001911e040013c00027260810300000800200016525b3ea6a1cf55032b629283ac424833a86994f94b43cea18613d5490e78a8995b94b319f2a0633e54882dca5206b10821d6216653f54486eca39957d4d108ea98859d434c678a8905754c41d7a92876f525067aa998cfd5232cea1c613e540c27aa9104f54c429e292877551ccb58a4a1d754c10aea98853e54ccae8a2905b948309faa2655e53106daa5204f550109f290855e5310b3aa6215714d20b6a90216d520c278a9195dd45209f2a4433e5404278a8885d94430aea9c433e54cc33a87996b10a21baa88613d54cc2bca6085714d10cf298855d53d0278a890cf94a42af29c433e54cc6daa598eb10b209eaa6655f534835884194fd51109f2a0879d43cc67aa7214b14943b7a92876c5250e7aa8184f95032af29e813f54482dea4886b948429eaa0636c524427aa910db94810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x18118400102004000000c8000004118802828c6250e30a3189430c30c5310920c550d510c22c6255031c394c428870c6254c42a358c424830d43548308b594420ca1d63151218b18954cc32442145208758e54883244294732c550d51cca8c6250f32a358c428868d6310b2087195434ca8c6250f31c350d52cc68c6250d31a358c420868d6310b32
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20200282b988528e65411c94354732a08e4a1aa21840d7614c4248206bb4a621443415cc4214520
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s2K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s2K4 (2430+(h % 58)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s2K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s2K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40459
namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2c18a0400000000cb000100100541000000185180000fc41fe21fc30fd31be41bf40bc42fe31fd40fc40fd42fd30fd43fe43ff30be42ff21ff43fe30ff10ff31fe32fe20ff20fd20fe41ff41fc42fd21fe40ff40fc10fc31fc43fd32bd43fe42fe10bd40fc20fc21fc32ff32bc41bf43fd10ff42fd41
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8000048080814001420a81400740c00c4240c000800200000000058540408301c083c540004380408006820000000080400000000180804002008584400141130180448000801cc0000000800144a78a4a1cf55020cea1e639d5310a7aa9204f94642cea1c613e540427ea8994f150219f2a0815f53442b8a6904f94b439e28a873e5210a7aa910cfd41438ea98853f544c67ca9994f15310af29841b6511067ca9185d94430baa88615d530827aa8184f151319f28e873f54c42bca6214fd52329f2a0416c524433a86185d14520afa9a413d50d0e7ca9104f950439e2a2215e53042eca3995b94b319f294853d54cc2dca4185754f21bba8a419d434c73ea6a1cf15232cea1e655e53886eaa2106794c41aea9c433d531063aa7a04f550109f2a6633c544827ca320d754c419f290833c548c67ca220cf94a419f2a063ae5210abca790cf540429eaa4873f544867ca9984f54241aea98859e5310a7ca990cf553319ea80833f548c67aa720db548309f2a2613f544427ca8194f55332af29e813d540ca7aa6215714d109e2a2439e53d03ca4210cf952109fa9a819d434caeca2104f94b40dda82816f524427ca2215b948108ea98835d53042daa4084f55321af298833e5488678a2a05754f409e292813c544ca7aa7a04f55031b6a96633d5090a7aa9084f552209f28e817551ccb3aa7a04f153209f2a0613f54c827ea8904f552309ea9c853d544c33aa620cfd5021
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x100800040200048000224000487d8d5090a1d63952208758c525031543547328758c51502946150d318758e5190a1d6394a418758c54c821c6550d318758c544861f63542418758c54c430d43548308d987548ca1d63150218e5805408634615513087195434ca2c62551308b98b548c68c6250d328758e548430d4354b31c550d510c21d6395130
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s3K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/79+packedAt s3K4 (3618+(h % 79)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s3K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 1 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 2 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 4 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 1 => 0x2519221924a430960a854853485090aca32692
  | 2 => 0x432a44486949032aa109950595012585458b18
  | 4 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40459
namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x30c00029c00020c00000061d17c0000000ac40425c3040000080ff41ff30fc40fe42fd30fe20fe32fe10fe31fd31ff43fe21fd40fd41fc20ff40fd21fd20fc10fc41fc30ff42fe40df32ff31fc31fe30fc21fd10ff32df43dd32fe43fd43dc43fe41fc32fd32ff20fd42ff21fc43fc42ff10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x900004200206020030100bc98056100260639b001c190a8000008800004828804a89061ca0d06a000004080001c15180140010008100150056d8a4a05d54642aea98411c544ca7ea8885795332e699441765190adaa4085b14910af298215e53082dca4085794f20afa9a813e5408278a888734c820b6a90875c535033887215bd4940aea90875e530cabea6a0cf55010b6a96613e54042baa7195754e41af29c87cf524cb9ca421d714d41bba8a815d53902bca821cf95230af29c836d52906bea6885354843e6992435d5390b3886216710f40cf2a0875c534427ea8995754b43afa9a853c544c6baa610d714d42aea98855e53902dca421f34cb21e7212653c544cadea4884f55321cfaa2655e544cb388720db94831b7294835d53c86eaa2106710c41aea98215e530873886a07350932bb2884174515039aa421db94b30aea9e415e53c867aa9184f55020ae2a6656d520c6bca7214fd5131ae2a2653e54c8738a8995794c42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x240000048000004400016000040080030028d6210c41c310e529064d6214d41b1586424ca8d6210e42a358843d030d544cb218719153087144394642a3588435028d6210e41d14c9510828c644c82087992544ca1c6454f20c510c515030c5490932a3191328830d6215132a3191324864d6294e4093195424ca8c644cb21c3551320830c4314940
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4900022063b2a899041411d13254420818ecaa26590e0454586424ca82b908728c85415c84314540
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/35+packedAt s4K5 (704+(h % 35)*6) 6) % 44)
  | 4 => 2*((h/65+packedAt s4K4 (2430+(h % 65)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s4K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s4K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf07fffffffffff03ff07f83ffffffffc8e3fff
  | 1 => 0xff81ffc0fff83ffc1ff87fc3f83fc0ff71ce73
  | 2 => 0xfffe07ff03ffc3ffe0007ffc7fc3ff0381f39c
  | 3 => 0x7fffc0003ffffff80007ffc0003fe03e0
  | 5 => 0xfffff800000003ffffffffff80000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1408204820900000a5009004904454500614a5
  | 1 => 0xa12450864921512c0a2829412a2a82a930ca52
  | 2 => 0xc21495121a45175540a44da84ea32a0b816318
  | 3 => 0x8b59662490759b9a73b5052077320c33da03e0
  | 5 => 0xc618438e38622e39cc67632040030c2edbc00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8eee8eee8a8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40459
namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x10934d04000100000108c000140180301043007000fc42fc30fe21fe41ff21df43fd30fd40ff10fd32fc32ff42fe30dc43fc41fd42fc10fe31ff41fd31fe32fd41ff30ff31fd10dd30ff43fc31fd21fe10fd20ff40ff32fc21ff20fc20fe40fc43fe20df30fd43fc40fe43fe42
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x421dc434cb7a84a077cc030efa1e41fa10043d884105f54341be2a2437e52087b8a5a1f754e41bf298835c5350afca7a05b54840ee28a61ed20083b887195fd4d41fba0a43dc32cc3ba87985794e20ee986217e5290b7e84a07795043bf28863dd32cc7de65195f94232ef996617d52442fca3985f54740eea9841ef42883be8798cf95010efa18835d53882bca821f794e10ee29261f940102fca6215f14141ee21c217d5210fbea0985d94642bea9441ee520c7bca6087b54840f7192437c53043ba43987bc8220fb90a43fb10443ea6290df54f40bea9483fb308c2faa620cf55010be2a6657e5290efea9885f14e21bf28461f55190bec20885f95030f6216437d540cbbe86a0f790130dfa0e817c540c6f8a8987ec8120bb28841dd52d0fbe6218f714d40bf294657f54486faa921f78c130bfaa061dd53842fca3196fd0641b729081df52cc2fca1a1f710c20efa1821bf4310f7ca8087710d31f790a417c53c86baa7205794c40ee982217d538c3b6a0985f94c32efaa261f631486fea8885f14121af29c83de53082f8a610df55331ee2a661df4350efaa6885f95043be2a241f441043be61887d50441bea96217d52887be87216f55010bf2a4617d54082faa4085f54b31bea9a417e52902faa221fd94642bea9821df404c37a82a077d0e21be28a87df5110fb887a0df94a10bf29063df514c3be8610df94643eeaa261dd4310ebea690f790530ee28087de4310fb8a690df54342aea9c83dd5110efea8107d10621be29c217d51d0eeaa2197794043fda04817e53483bca8985fd4143bfa9a85dc52cc2fca7885f15310be28a617551102f8a2a05f15330be28a41ee52906faa8885fd4540bf294635e54cc3be61187710f21faa88417e51042bca610f7d0d40bea9e83df43102dea4a06f50842bf29687ef4250af8a2a177d0d32bf2a665df30443bc81985f94440ef19265ef4290afaa3196fd0441eea12617f5050bb88718f714f40f621243f741906faa110df94c30be2a2637c524c2faa5205f54c40ee21a41df424c3ba61105f94021efa1c65dc430c2faa1196fd0842f7216417c52042faa8905f55210ee288877f54c83be8618df54b40efa90877c53882fca2217d88421be29e413e54083be81987b94840ef98c63bd40103be87085f15320f690a417c524c6faa98857d4d41be29a83de41cc3bc6418f7d0f32efa1a63dc430cbbaa421f794b30bf280817c54086fca0187794c40bfa9287f521c43e883085f54d21be2a643dd30c83be65195f94832bf29c857d500cafaa3087710e41bf28c41de328c6faa010dfd5130ae2a2617e50906fca890f710530fb20883dc43ccafca8985f54041bfa8a857c53487b886987d94432bfaa0637c5250fb88798f794c21cf2a0877e500c6faa990df55332ee286877e54c86baa7185f95040
  | 1 => 0xc5050bee4310df54742ef99263f441486fea810df54e10df2a041dd30842fca5a05f95021be29841de21cc37e85a05f55121bea8e617f50486fea610fd90510be29a817d540c7b84398774c730ee18a61dd54cc2f8a998d754343bf284217f53442faa62177d0d21aea98437e52c42fca790df94032fda0281f631886bca7207754743be29e21dc4350abca6107b14940bf288877d54906faa710f78c531bfa92837f53c86daa520f750330fba0c21dd52cc3baa021f794e42bea8c877e52107b881985f15020bf28e655d5010efca42177d0f10bf29c43dd53103daa418f74cb30ee21c417d52106fca121df95010be294217e51087b887a15f54031ba28a817751503ba60105f95110ef296877f504c6faa9195754c20bfa9e217c5350afea990fe4c030bea8865df43cc3b887907d4c431faa88657d51102faa3105f94f20ef196617c504cbbea690dfd4543beaa0215d5390aeca220770ca31f7a1243df414c2fca9105f94c10f7908437d5090bda43905f94830be2a441df30843ba62985f94720bf28481dc5210fb863985f54b30ef21a617f54cc6faa7a15f15210bea9e437e50ccafca520df54e32beaa4817e50887dc84215b54810f790c437f53c82fea898df95031bf28463df438c2fea918df94e20bea9063bd41d03b88620f754c21efa1c817e54c43be42985f54321bf290875e5390fee200877d0d10be292215e53842faa7107d8c431f721241f541c43bea6a05b94831bfaa065dc424c37c82a0df94e41f710a43dd434c2faa521fd48421beaa263dc4390bb86498778c530bf28021df51cc2fea2906f55020be296217e50c87be60105f14131efa1e81be4350ef8a4a07d88710ef29087dd30483da6590df94810ef990657e52d07f660987754e42bf2a4657e50d06fea7105754e10df20281de5110fbea5a1df95331ee29a85dd53903da64195d54420f6a9021df50d0efca8907754343f719643dd300c3be83987710c10bf29e837e51d03b886a0f790f30fb28881df21cc2faa7207795330fd10041fa300c2fca9907d50510bea8c617e54842faa3996fd0040ee2a2617f548c2fca6205f15230bb288657e53443e8a2a06f90942be2a463f751503ea20085f54720be29a21bd41107b88710dfd5221beaa0437e50882b8a6a077d0d42ef29c417d54cc2faa910f7d4743bfa8a65ed21086fea498f794e41bea94637e51d0fbaa2985fd4d21bfa9841dc42cc3b88610fb50b20dfa14857c52506fca81077d0e20bf28083df324c3baa4985f15110ef28e617e5310efaa5a1df95041beaa441df43d0afaa718f78c730fb10a217e50d0bbaa7107710c31fb884217c540c3be60907710d40bea8c817d53907b886217bcc932f719065dd214c2fca610d794c10f6992437c53482fea8995f95330ee21881755190afea7085f54442bfa9
  | 2 => 0x6a0020c80600008ac83d2042a0000e0c0260080200010020104681e022de0100805004060040380c008260a0160304413032060000702c3285c0db0a000000500c038006e800010000601e39cde5780c040020202a0083a03802048000e5181a012028020000400000100020200c2100216010038a514804000061c0f2050100800c0000201886000040200000000290140001c0482c5980001804001a8040000781a00000000042b9f2038480000a0119003800000020000001006000380000043030180380e802000000880017148000020081c000060d1dc000000b80a0200e0901010802010400900e0102a01b1e04004008000001225816018002c000000102e8000180e1182a048000286e02800008160680a0281c01002d70020080e0700811026030000081a00038b6804000080280c000060b8280b0160100a0523809800050040780603806028aa0000e0201400000018080001801002228580206e000000100414806cc848000140083e01f714743ee992637f52042faa4207d54440efa1661dd42cc2fea6a05f54f20efa1841df314c3bea6a0df54a10bfa8a617f53042faa89877cc220bea88417e518c6fca220df95132bf28e85dc43487bca3a1df94b30dea1887df524c2baa6085b94a41ef996637d50d0efca1215f94432fb28841df5350bbca7205f54c21efa1e837e51902faa0215f55030bea84837d548c2fea710df54c20efa18616d520c7ca4210df94f42bea8665df4390efea9107dcc531fa90a21ef52503be619077d4043bea84637e53903bea7a07710f10bf29221dd30042fca918f710f30be28a65df54cc37e81205715330bf2a263dd414c2fca690df95042beaa485dd310c6fca598df54043ee21c61df43c87de84105f54e42be2a2657e52103f240105794c30eea98216c52502fea8905fd5330ef212617e50083be86215b94810f6a94837d5190bb883985f95032dfa0a817e5010e7aa8105f54331bfaa421f910043bc42985f94630fba0a837e528c2faa2185754c40efa1c63ef20083bca2987708530f6a10857d5090fbe639877d0d20efa1a617d53c42fea6907d4c621bea9461fb20883ee82087710d10fb20e217e518877e8721f710130bfaa4657e52083ba64195fd5010be2a0657f52442fca0215f55320afa9a857d52d06fca320f710e40be282875c53506f8a9197dcc631efa18657d548c7dca4085f94e43eea8e61ec42883f621087bd0b21be2a021dd404c2fca7085f94642ee99261ee20483bca4985f94c20af29c857e54887be60087b50920ef286877e510c3ee8310ef50b40ee28e61dd41cc2faa89957d4d40fd200815e544c2fea9995714d21ee21e81df43906fea4985fd4940bf286637e530c6fca2105f54830bfa8283ef21c83bc64985fd4b10ee190637f504cbbc85987714d41be2a4437
  | 3 => 0x440100000000000103e80800038010060486c078600001200018158040108a09802038081e804009380000c0200e010c0028000880200012000000100c
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe500872d5454810cb18954082d56110130d594d5190b4d5354840d394d521025f65d0e20c7153404c3553254432d994a51102d96010530d3149324c25d6095130c795340cc31f6395010c7551300825d6510e10b3189404c23d641412197d954310e5c6454c109798f528425e6508530c7150414c2756114142c7152414c25d6510c2097996434c23c64549108f590530425d6510c32c7953438c65c6454c21d5d4c515034c4354a4197d8d5110a6d6215210cd550410425d63145209b58853c434d5348421c7953438cb6652544409798c540865e6314a1097d95414c2d661101309d9845050a5e63d52219b98a51d0f1e5410c109d587548ca77615511097195424c2cd6214730cd951510826e62150319b189544431c6395010c7951300825f6510c30c7950438865e6314c20d310e52906756115030cd552510831c6355010d3549310c65f6355120d5d0d51102cd6210c32b3988514c27661d5320b558450d0e7765484219798c548825f63550219799642cc25c63550109bd8953442d96010f409758c504867661d52329d984524c25f6510c109d58453c825d639474097597430863d64d4c10cd551100425c6355220d354b3004356514c0209758c548425d63d50209b98b53042cd62144439718d521065f6054e418f990530825d6510c30d510d510825f6054e42d3d0e529065d60d4d219758f520431e6415130d5d4f515025d6590930c755043c865d6094e419718d548865d6508730d354852cc25c6354442d394e520425e63d5020b6582544c34d5394810b658054cc23e6414810d3548524c2d96010e109ed95300c2746154d209798f52042766194b409758053486cd62d4743b3d89404c29c64549309758c540865d63148109b189534423d64d4c209b98a51d032e54548109ed9520083544354432b5d85544c2e56190b20b5986424c25f6355221b598652d0e6e65d0921b5584328c74f4394840c7552530435743544209d185544c27661d5020d310e521025e6394b409b58a51d027561d502097191530825e6315020c7151404c25e65d0d31d3548320c6766114f209798f544875443944329798c530425d63943419758e544867761551209758e508865d63947429d586544ca3f65500409b189544c3574394432d954b410426e6214c10c7550430825d65cc010b5d8540cc25d639401097992530826c654c9219b996424836552c4010b558452cc31f639502097d8d51c83c65348421d3588534866e62d53308fd9153483574394440c7553430825e63d5320c7551530425f6054c219d58652d0f4f4314940c795140cc2d96010d10d914851502d66114343b658051cc2d56110c31cd952510825c6550130d310c525032d54948109798c520425f635513197d94438431e54d0c209758f54c825d65d0e10b5185404c25e6394341
  | 1 => 0x27661d5330d9149214435443d4540d98c9510cad9601093097d8d548825d6094e42b558652d0e7a60150219d984540425e63d50308f990528425c6510d219b988530865d63d5310b69805110e5c6550b309b988540c26e62d53109b988548c35651cc0208f990540825f65d0c209718d52d02d96010c40d5544514c3994010130d954d210871c5410d209798f54086ce6294743c7950430ca5e63947429758c5050a796015021c7551530827661148109dd95411065e63947409b98853c42ce620c53097d8d544427561d5330d554d510825e65d0d309b588548c27860551219d584540826f654c832cb550420826d6215030d554d511034f5314940f18ca3148765524c4318f590528434f43548319d587540ca776155220d5145314c29f6454530c7d8d540425d6510c109798e500425c65485309d987540866f62551209798f540431e5410f21d954841042766195132d3d4a52d0e3d6414c209758e5090a6d62d4c109718d548434d52cc431c7951300425d63943429d587530825e63145209758e509065d6394b40b998b414874c43948109758e5010b555394440d310d520c7565394440b5d85524c2cd62905308f993530431e54cc020b558752d0f5653544409798f54c863d64d4e219dd95100425e6590930b6d81514c25d6394b41b398a414c25e63d522097d9743043c44348421b558754cc2d661103309798e50082d661d0d31c7553430434e5354a41d3d0e520425e639512197583535065d65cc02097d8d54c86da601093097d97438427b6544010b958642482d960d4b30b658343d02e661d09219798c524425f635513297997435025f6510e209799253883346155010b558440cc2cd62d53309798f54842ce621473097d8d540c3675348421c755043043c743484219758053506766114c20d154d210865e63d53109758f54442756510410d394d52042e4614c92197990534863e64d4c209d584524c25e6315010b65805210e756194b40b3988404c2cd629474397d9521cc26c6550920b3d8940cc2d66190b309718d54c426d62141419798c5050b4f4394831b9189314866f6548421d514f515026f65480209799421cc3355454420d510d5190a5f6354b40c7153434cb2d5410b21b5584324c25d63d5121d554d5190acd6214530d554e51083c46348421d3d4f525031e5410c30d354a320c71c63550209b596520431e54d0c109e580540c6d66114843b518540cc25f654c010d5545300834f4354a4197597430c39b435004097d94430834c43948319798e50d0a5f6355020b6980414c25c635512097596414c2d6610c930c7953438c25c6355321c79925410e5e63d51109b588530434d5354810d9549100425d65d0c209798f5448359609513097d8d524425e65d0d32c7951530825e6394041b358840cc25e63d50329758
  | 2 => 0x54480209d987540cad56190b30d954720083355150040d314e32486ce620c730c718e54083574354432d314c525026d62150109b588540c74e5394a41cb553200823e6415010b9d95210865f63552109758f54886cf6254530d3d0d521025e6394b4197195414c2d960d0c40d35485210f544314540c7950430c65d65d0e20b658052cc26d62d5010b398b434ca6f6550842b69805210ed56114930d554e5190a5e64951309758c505075653946429759653082d7615013097d95424c35743145409d584548c25d63940418fd95411065e659073097d95404c25d63d53219798c52c433554c4010d954a310c76552d0641d594e510833554d04109b58a544c65d6510c319d195214425c63547409758c548834c4354840b3189544c25c635532097993534865e6494c30c7153434c35551144439b59742083c5324c5219b98b54086d960144439798c50506766114c2197d9443086d461551309718d544865e6494e10d554e210872d525004097d9542cc27b65500408f593520425e65d0d41d354832cc2d661149308fd954310e5e6494c10b598754cc31f6355020d694d300c2d6610cb30c795043cc25c65487309b58b540c6776155130a7d91524c3c52108530d5584534875743546429718c544c34c53d49409e980540cadb6054930c79533004274654c521d9951210863c6454d20b358a41cc25e639422197596530866e62145309d984540c25c635502097997324c7c553484219758e500826e6215020c7150424c32d54d08209759642cc2e562904419b9885484359601533097596320c6cd620c530975835350b54538c521d9485500865f63551219798f540c6ce62907309b988505063d64d4f21d3949300426d6214530d3d0d520425e63943219d98652d0e3e64d4f21d310d520431e5494c20d9d4b515031c54d0d319d58754c825f63550109d185548833554106219758f54483645448421d5547300827b6055121a7191514c25c63547209719153842ce62103309718d54442766115020b55845010e5e6510d40d9d09510825f6354740d9109510823d65950209758f528426c6255210b5185524c2d960d4730d354e52102d96010e20b95864210b1d544c0109b594420825f654c431d914521482d960945309798e50906756115032b39885110e5f6354b108f9935204394435044197d8d54c427a6015031b3d89544c34e539484097581530425e6394042b318940cc25d6510c219718d540865d639432197997434867661d4c209d98454882756114c20b958a41c425e63152109d996414426e62150109b58b54cc27661152309bd89544426e6295131b5586424c23e64d4e21c7553300836765484219b58b54c433451d0540979944350b1f5410d209d59741042746550510cb14b425025d6315010d514c515025c6454e20d5d0f515
  | 3 => 0x1241f06802044000e8051840f034000640007c07164085b80c0380200c1e000051383b0b04c35402048041a0090200100905310b4000080140f00400008033dc000000126c02008000044e0140005002000120003903c8d00c0000831330013380500c010440102c240000a0dc161500000001298a40000f00c0b0ec1501000004200a10c0000000c1b1dc0003c024381a03c01144040080804c070122d2b8430441e0102700800008330b400390020ac00000010906f0082700127094000ec13084010b4040040082869240020800000030080121c4000a4290000011837008ee002f1000312b86f0400b0b40c028c02e0dd0b0010381b0144b00c251341d0e40504c040044b02c0b00071004c10a04a0100606c7e46c00018353e4040c0320045c10000004000240a0701119837000a4009ef0240102c1000c090e8061f00205c3c14851120000800403012064020ec1c020210025d6594c109798c504875551147309b988520423c6454d10b3588404c38c43508429798c530865e65905309b58b548c63d659501097597430433551d0040d5d4651d0e3d64148109758f548825e6315030c7d5043442d960d5330b398b51d0ed66114b309e59610042e562884218f99053043675214540b398850d0e5d65907309758c52c426f6255130b358850d0f1c5410d108fd954210a5f63553209798e534871e5410f3197994434867960150329758f540865f6354841d954a511025d6510e208fd91524426d6294743d510d511031e5410f3297d95214c354439444097996404c26e62d50109d997414865e6494c219d18554483573254432d554d210865c6354b10b358831cc2d6611404397195434c25e639424297d9541cc25f6355130d5d0e510825f654c83297197434865d6014d42b598752d0e5c6550730c795253042756115220d510e510825f654c020d354d529071c54909309758f54842d960949309dd95310c74f43d4940d914921c436551480209798e50087c76348421b398b54cc2766115032d5d0e5190b65525444097594214c2cc6254530b35885010f4d524c010d394b300425f654c030d354e529075653544209758f54043674254642b5584320c65d6315020f148421cc25f65d0c2197994534863e6414121c7553300431e5454c10d310f525031e5410c2097582530865d6314a10c799054cc2d96010d20d510e5190b2d52d00409758c524425e6510130d94c9510cadb605513097994435065f6054c10d354f21086d5610cb309dd85534831d5494c209718d52442d56114843d554431cc32e54948109b98b548c6e562905109b98b540c76452d4540b39885010e6f62552108fd91534425e65d0d42c7550438872d
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x8020000514355f0151807830000400012c50880592c34c1a28e8a88a298645625445110eb0b80a890843915496114930a8ae62a24210d457594d21086a2b90a298a61831526290530a88e8a9a4210e475258652d0ea2b98a490a2191589510c730a8ae229264984c573987424870a2a0c2a0261515d44348421d22c2a0080985457314521482a4b8086a9081915895114730ca2a2b00a221e18545804348322b2a4210a6151dd74348421c8ac4a88a29850c74548524c322b16a328e87915952108730a8ce5a8ca3a1d4475484214c20e3a2ca10a61915896114d21a8ee0a9a4210cc572987434c70a2a4c321261869916015330a88e2a90a49860c54189404c2a33b2a690843511d95348421c8aa4b08a421cc676d0d2108662b9cc5a0a4391549610cb30aa2e021aa2206455258452cc30c2a2c021a21165c06510d21a8ae6292438868962500404c262b8cc5a1a65511c95114530a8ae421aa2195457110d520c724a92c029087519c75294b43
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x11000906849d95348421a04845496114930c0474589511453084686dd74348421a04845952108530844875952108530
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => 2*((h/28+packedAt s5K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/344+packedAt s5K5 (21627+(h % 344)*10) 10) % 801)
  | 4 => 2*((h/274+packedAt s5K4 (29678+(h % 274)*10) 10) % 781)
  | 3 => 2*((h/32+packedAt s5K3 (2744+(h % 32)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s5K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff87ffffffffff81e1e1f87ffffffffc063fff
  | 1 => 0xff81f8f07ff0ffe01fe3f8e0f0ff07e39d273
  | 2 => 0xfffe00ff83ff0fffe003ff00ff0ff83c1e39c
  | 3 => 0xf000000fffc000ffffffc0000fff0003fe03e0
  | 4 => 0xfffffff0000000fffffffffff0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8082010002000020204012221112100204a5
  | 1 => 0xa51245123294549608ca1a84458aa16a18d252
  | 2 => 0x4621492451a845aaca082b2089a8cd0ac16318
  | 3 => 0x64759648a50e66cd6d6c82012ecc86336e03e0
  | 4 => 0x88461800c630887191913449c0000841b5b800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8feeaa8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40459
namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x60005801f00800800890430830030713c204214700ff84001fd20037f54c0d7f54037fd4007fe4201ff8c80bff41027fcc403fc4000ff90007ff20037fd480dfd52017f0c4017d54017f88407fc42007f48409fe43037f54009ff3001ff0c809fc4302ffd0c01fd32037f55001fd4102ffd0801fd31037fd5003fc30017fc400bff40027fcc801fd4202ff9500dfd51007f50c01fd30017f90405fc4101ff14803fe30037fd4405fc5101ff94803fe5002ff15003fc10027f94c07ff21017f94401fd40037fd4c01fd1000ff14005fc21027f14c05fe3100ff88003fc20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a8402ff8c5210e7f8a49880ff72148435fea9a4203ff8812102ffea8a08177f405500d7e32a8007ff0c910027f88699053fe62500057fb1a6205dfd0d5418ef8c4aa007ff30480097f31a4201ff0411001fdc64908abff5050807fea926421ff94d4101ff842a100bfe5148409f79926401ff8814001ff8a49080fff42508057e30a8605ffd0542007fec498817ff42500017fb0a4012ffd5130007fa8688037fe5448041ff3128206bf99530127fe2099013ff534c009ef21a6002fdc4141007fac888013fe534c007ff9026400ff5891006ffe829002ffc6148029fe1928005dfd5141017f62088007dc304c007ef1926404f7cc14300dfec698007fc5048007ff2126412dfd5130007fec498007fc1050045ffb2a822effd4943015fec2988affe1050c0b7e3224202ffc8541005fec68801afe655081d7eb2a4000ffd8940047f8a68806ffe204c407f61926400bfd813102ff880a08bbff5150c53ff9828400ffd812102ffca8a1013f7314c41bff3224000ff58540117fea6a08033d54504057f30a642eff9954301dfec499003ff6250c21ff90a6009ff19110007fec890002ff6150c09ff1928602ff04121155facaa1037fc6448003fe2026002ff0413102ff8a8a0827ff4244009fe1926203ff5092002ffa86a0002ff6350805fe10a2005ff5514100ffaa090007ff5044059fe28a8605df101540aff8a6a0097fc644c80bdfa128003fbc852008ff8a898003ff63500097e31a400bff90520007fac4a1857fc6350007fe1924212bf59530157faa0a1003fd414c027fe10a8012ff55130035fcca8800bdc314c4017fb0a8406bf99541007fac890897ff404c801bfb12a800f74c931017dc429086bfc654840bbeaa28204ff14d31015fcc2a1013fe434c803ffa828018ff18d21027f66098003ff644c401feb024200ff58d20027fe86a18037d544c009ef9926232df98d54017bc629889bfd654c809de21a8605df90154157f8caa1003fd634404ffe3028403bf9894000ffe6088002ff624c405fea8a8220ff94941027b88699013ff434c813ff2a22002ff08521067fcc690063fc5348407f79024205ff901410d7feca90813fe534c82dfeb2a801aff59521007fa8690803ff644c0037fb124000bfd894017ef840aa03bfc654800bff20a8410ff9493000ff8a08800bfc214c409fe21a8609ff9911000ffc809804bdf534c007ffa924000bfd8121025f8c690807fe1048001afb1aa802ffd05100effe849887ffc205043dffa826201ff48110137fea899017bf4150005fa18a6200ffd8910007fa84880b3fe2150c1dffa8a401dff9913101ffc64a10bbfc6550c0bff2a2801affd412100ffe60a0007fc5050005ff18a8203ffd0921007fac098807fc204c0557fb2a841abfd95210c7fe6090807fd4048011fe31a2005fed0140
  | 1 => 0xffc404840bbeaa2800cff18d20157fccaa100ffc5248017ff28a402dff9894313ffc60a1003ff635080d7f32a422cff9854301fde4299017f74150409fe29a8602ff5053100ff8408807bfd544c44ffe2828405ff909410cff8a8908167f645504dfea826403ff50932147fcc2a10037d544c429ff292801cff94931017ee2090803fd614c835feaa2421fff18141017fa829084ffe6150049ff20a6404ff4c5300dffcc098817fc4350407ff9928428ff8c542157facaa1007fe405001fff10a600ebfd95200f7f8ca9883ffc614c051ff28a8404bf18d4202ff882a1003fd214c001feb026401ff08140097feca98017ff4250c077f3128202ff54510005fec4980b3fc2150c03ff2822003ff14942177fea0a1807fe20480017fb026420ff18941006faa89080bfe215044d7fb2a6422bfd954111ffc209907ffc3050437fe1026202ffc4141015fec29080efc6250001f690a402fdf0c1540dffc8098803ff6344009fe21a6003ffd4942027be6099043fe624c045deaa28201bf181430f7faca9885bfd51500057e30a6405df10d5401ff86490002fd6448003ff1822003ff9492102efc84aa003ff6150803fe0824002ffcc510004feca990c37e215502fff2024202ff0c510107fe40a0803fd32440037f3026222ff5494101ffea499007ff104c04dffa8a6401ff9414001ff84090843fc624c009ff982860aff54d10027fc609886ffe504c40d7e32a2010ff90930047fe6488007ff204c005ff18a2002bf1854002ffe82a180ffe2050805fe20a2001ff0c13002ff884a0803fd644c807fe212641fff9414101ffc649904bfd524c007ff10a6404ff0c132017faa2988c77f2055003ff1828007ff14910017fca288087fe6350401feb0a4015ffcc54002dfcc89900fee4248001feb1a8210ff10930007fac0a189ffc105080bdfa028224ff14532057fcca8800ffc325080d3e32a2013ff0c54002ef884aa003fd4348001fe992802bff141430b7faa6a001b3f645500d3e32a6203fec8120067f8a690003f54144031ff31a4202ff54521007fec29905ffe504844dff32a6400f74c530027fa8698857ff3250023ff3226000bfd913009ffc62a004ffe515002dfe32a8005ff1054000dfcc09900bfc314c407fe10a4005ff90d41055faca88007ff404c03dbe32a621ebf5953100dfec8a000afe6150005ff98a6203fbc8142097f8ca98007ff5048007ffa124014ff14940035f8ca98803ff604c40bfea1a8417ff8c121027fa6498817ff4050405ff98a4201ff881100cff8c890813fe434c007fe9924202ff8c531027faa6988bbfd5050c0bffa1a8205ff90543017c8429080fec4250805fe18a4204ffcc931007fac2a103ffe614c00bbf21aa829ff14d42017fca29880fff3248405fe20a6204ffd0d30175fecaa180bfc4148455ffb
  | 2 => 0x2011ff820990cb7f3055023ff2a26008ff90d10017fe82a08177f5450809fe1826202ffc4121077faa8900affe5050c01fea0a401cffc81310b5fecaa00037d5448009ef98a6402bf1854202fde84a1007ff4044003fc0822009ffd0d100e7f8849887ffc5050459fe30a8603ff9092102ff8a8a1047fc644c007ff9024211ffd05300bff86090803fd6050839ff3126205dfd055400ffa609001afe6548009ff21a6203bf18910007fac898013ff3150c07fea924205ff9514301ff84299007fc504c009ff1828604f714d30017fc20a080afc614c007fe212422affd4d4201df8c4a0803dd434c009fea1a6400ff5913102ffc86a0013fc3150c257fb2a6003bf18931006fac6aa023fe534400bfe20a8622ff5414102ffaa8a1017fd4250407ff292400affd5110017fc82a0813ff3250c09fe29a6404ff8c54300ffe80a001afc6550c09fea9a8600ffd854300ffc8090017ff43500037e302821fff98141056fea88803ffe414c0097f31a8005df55142015fec49080efe624c003fea826023ff18132005fec0a1803fd424c001fa90a202cff9454302efea8a009bff504c829fe312801dffd013100dfcc0a18b7fc5250c017fb0a8003bf18930077faca90006ff604400bff2028401ff0812001ffe8499067ff4348401ae31aa806bf995320c7fc86908177e4155001ffb0a4004ffd0d31007da8490007fe5048005ff90a2003bf989310f7fea898817ff54500077fb22841affd4d210affca6a0006ff60480017eb226400ff5893000ff88088007fd3044033ffa024201ef1014001ffca4a109ffe6050805fb10a2029ffcc542055feca8802bff5344005fe28a82009fd9510097fea4980abfd5350813fe2a22012ffd4530025fcc6a083bfd5148001dea0a801aff99521017fa828806bff5448461bf30aa801bfd8140027fca69888bff5250407fe102840aff19510057faa888033ff3148009ff982641bff1013101fb86499017fc54500077e3128600bfd9110017fea2a08affe2050c017eb226200ff58940025fcc6a1053ff2150001beaa22025ff9513200ffc20980bf7e1055031ff29a4222ff59541025fcc688007fc40500077f3122020ff8c94100ffc6090013fc3250c15be32a2026ff19532035f8ca980abfd515080b7f3226016ffd4d40027fc6498017fd5450061be30aa81edfd513105ff86290097ff414c80b7e3226405ff505400d6fea8908affc1050c07fe9924004ef90d4309ff8c2a008ffc504c817ff18a4000df58554017fe4298812ff6450c1dfea9a400aff59510136f8ca9908bfc6550405f610a4207ff94910007fec89900fff32480037f302840fff14530007fec29809afd654c8057f30a6001ff90110027fea69882ffc41480097fb1a8601ef901400eff8a898807fd404c005ff90a4200bfd8142147f862a105
  | 3 => 0xf1922003ef90942005fec6a000bfe4148451fe30a8400ff58d21015fec2a0807ff20480057e30a401bff18131027fca6a18027f654c44dfea8a6403ff5492000ffc20a0016fe644403fff1028205ffd51430b7fea4a000ffc4248003fea022002ff84131006fec2aa07aff654c40b7e3226003ef10942005fec488002fd644c007ff10a841effd493102dfcc890877fc644c425feb2a6003ff90942005fec89005bff515000bbfaa28601ff88130027be6098816fe6448051ff8828420ff0c941034f8ca99017fc4050c4ffe1828400bfd913218efcc4aa012fc634405fbf102a800ffd9121007fac0a08bf7c605500d7f32a6202ff84121175facaa1813fc324c005fe98a2001bf1814218ef864aa00fff2050827fe28a8001fb88120035f8caa10bf7c1055005ffa8a622dffc8543017fa42880affc6050c03fe0826003ff5494202df8c890003fd6350801ffb128204f7cc530027fea6a181ffc6244007ffa924201f78c130027fc6099006fe6048405fa10a4203ff10942017fea290803fd31500037e3026204ffcc53202ff8a8a1813fc314c819ff21a4004ff8c93102efe84aa023fc43440057fb228201bf9814102ffc86a10c77e325500bdfa028402bf98543017f8a298803dd324c009fea9a6405ff5514302ffa86a0802fd6348003ffa024003ff8c921017fc4288093fe614c809ff18a6421ff14d410b7fecaa0037ff4348007ff9926400bfd8d21027be649800bfc5148463bf90aa830dfc415402efaa8a1813fc534c007fe2926424ff10532027fa869800bfe2148403ff9022002fd9051000ffe2088033fe5348001fe90a8001fe0c13002ffe84a0803ff6050805fe10a8229ff98d42077fea890017df4350c01ffb0a8000ff5894102df8c89884ffe2150045ffa828204bf98d2003ffc8488017ff4050803fe1822005ff10d40007fec0a0802ff6448415ffb2a200aff5491007ff842980037d6055043fe31a8206bf195200affcc6a0017be5450465be31aa81cff1893100dfec288087ff3050403ffa82602dff9494302ffc80a1847ff424c061be10aa807ff1091002ffe86a10bbfd6550c05fe98a4203ff0c932077feca90003ff63504017fb0a6429ff18d420c7f8869080bf4415040bffaa28401ffc4140076fea890002ff6250c07ff1026400dfd9510035fccaa1803fd64480457eb2a8202ffc413115ff840a1813fc434c407ff90a4005ff9094000fec208800eff634c803ff9028016ff54940047fcc688007fc3050053ff29a8405ff95141005fec29800bfe214c401ffb222007ff9891013ffca0a103bff5348007ff90a8401ff10120177fecaa1803ed324841bfe2a24000ff58530035f8caa0817fc4050803ff9826005cfd0554005fec6900bbfd5150c0bfe212801eff549310e7fc849880bbe4150401bfb02a802bf985
  | 4 => 0xc0380000000c01400406802008000048060020000601b0260440200602200006001018020000081500000600300009c3382b004004068b202815c020020040003181202607c0885c0000d80100000e0cc0d2100080040000106200c0182200207c0180600000c0200008a0040400e0a20180081003c004030070000000180904207c3d810040034010880140000200a00a080200220000040102f0001ac00000000088018080000002680101035c0885101ca200000c02e0880000802e0400280029e0042188108e728029d401e0c0000000100000081d00e0f40780e00000c0000100c004000610040880f0d401a0340001107006c0100006402c0500803c01c0281601203c0280a1000000180600e0000a01701c0bc050060000000000e3141040080000800000000002044178090201d8040040020340a01a006000038790000000300b0185280580000403c0180e002b415f00100a004000040060c00003600200059ff8828604ff0c14302ffc84a180ffe3248001ffb026403ff4852012ff8a8990bf7e6055003fc1024026dfd51320077a84a009bff654c803f61024027ff841420fffc60a0807f4104400bffa0a8001ff9413005ff8a290002ff625045bff9028616ff99540005fac8880bbfd5250c017eb122004ffcc13101ffe4299003fd6350003fea822004ffd4d32007fec69004bfd514c005de20a8204bf18d4011ff8809900bfe41440357eb2a4217ff18121005fec89880bff315043bff2a26205ff1094305ffcc29000bfc3150401bfb2a6417ff14121097fcca980abff5150851fe28a8405ff90540005fac890817fd4250037fe2826200ff58543137faa899093fc614c803ff1826003bf98943017fe8298867fe5448409ff98a6000ff4c941127fca29907bff654c441fe292820fff9453015ffcc0a1803fd314801dff32a4004ff4c930027fc86a18cb7f315500b7e3222002ff10541117faa6a080eff6250843ff992822fdf8c154027f86298007fd5050001beaa26402ffd052116ff8c4a183ffc414c009ff9926001fe1014002dfcc898802ff6050461be18aa804ff54d300cffcc890853fe325003dff32a6204bf18d4112ffcc8990cb7f3255005ff28a8216bf59540027fc629802bff52440017eb1a2003ff0813212fbe869900ffe4248001beb12a800ffd814300ffc2088033fc4348061bf18aa806bf1952102ef882aa017ff4050c037e3026400dfd95310f7faa09888ffe504c805ffa8a2010ff14930007fa849880ffe2148007ff2926401bf1812111ffcc09908ffe404c8037fb026000bfd8d41117fccaa080bfc5144005fe0828206bf9954001ffa849080bfe414c401feb126201ffc41200bffcc090802fd6348435fea824204f710d43007fec6908177f6455001bfb1aa805ff10d42035f8ca99007fc304800ff
  | 5 => 0x700a0000700600e0200100001c0141300000200c0000100a00006000000000000220000fc0800100a0180300800e0d0070000000542a018000000030282680200480b00e01c080110001080900300e0703300100207c0000202a0000087300002c0000001805c0201900a0000a80f0000900c00301a03c02004014000010220a60000700201e0000101f00c088048003700100e0000640000300101206c0100400601403037012000010d30040a0068030000000002e01a084000180042582482602400c12847000020118001900000403a00a0140102f0140181d
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd41551100057d70d855400cfe70d8d4148f6d42d895401cfd73d85321957f7358d5400cfc70d8d2101cfc74d89401ed7f745512001def734c9210067d5458d2142e7f54d8943006bf7458d20034fc75d91304b75f74d8d540067f74d9510106ec62589410057f70589541975f31d8d5449f5f4118d540067d7655121087cf214c930004fc764c520004fd75d8d20004fc764c9412167d70d95103be7f54d894118d7c7258d541975f30551320067c40d95310067c72d95312e6f541d85401a7b5545051001cff71d9121024fe73d9110004fd75d9131004fd75d8121235fb70585200067f65d9110004ff75591210057f7558d214167d32d953202cfc74d85320057d70d89540973f7455130024fc73591100c6dc6358d210067e32d951004dbc7458d10034fe7558d1024edd30d8d2000cfc70d89100067e70d95320067e71d95320347c7558d21024fc735891002cfe7458d20046dc43d8d10006f751d85400057f70585540ffb74050510006ef624c94000cfc7059132034fc7559130034fe75d8542004ff764c9400067e63d95101975f32551300a6ec625894045d7f7458554004bf7458d20034fe75d8d41005df744c930015f671509100067f65585321975f315513018e7f6255132016f76048510006de31d8d2018e7e625513100ddc704c53046f7541d85540075c73585541975e7118d540067c65d8131014fe71591301173f64585540055f7358954006be42d9130127cf314c921005df714c9304167d72d953200cfe70d8542004fd75d85201955c735855400ddc7050d30034fe75591320057f755814114edc6358d4203eec42d891008ebc645913039e7c41d953141e7e31d95320067f54d8d211857c7158954034fe75591311c6ef21d89100075f63d81540057f75585201967e6358d5436edf30d85320067c7655121004fc764c9400047d75d8d400f57c75591311867f6355131014fc71d891013cfd74d912002e7e64551200047f75591310065e6118d5401cfc72d8d411975f325513143e7f64581540557c7558d101857d71d85540075c61d8d540075c72d8d541957e7358154004fd71d81430067f54d813133d7f7455131006be42d911002cfd72d8d420c7cf304c92101cfe72d81430073d72551411877461585540067d5458d100047c765513241e7e73d953208e7d645513017f7a60d81541975c6358d541877661d8554006dc73591100075f735815402cfe76d913041e7d30d95321357c75d9132085ec725853014ede43d8d420067e765513018776215511017e7c60551210067c62d951002e7c64551310067d75d8542006ee20d89310067f654c9103a67f43d953114edf30591320067d70d95321adf771589100067d7655132024fe73591210057d74d95310047f755911042e7d54d8943024fd71d8131004fd70d8d41
  | 1 => 0x513004e7f6455110007776158554004ff764c9411877641d85540067e765511002cbc7458d10004fd74d813200dbc70509400075c10d8d54326dd31d8d211857e71d89540073f64551300aedf32d8d400067f65d913131eef21d89310076f725815402edc6450d30017f36048510027d7614c93105fe46148520025de7350930005bf71509401367e76d953201cfc72d91300ce7f64551212167e70d951000df6704851021e7d21d95102b4ff73591304b75c42d8d5402cff7659130016be61505400357f74d855408f9c6450d3000cfe70d893103dec72591100075f63589540067f73d951000dde704c530024fc73d912002cfe76d913118574715815435ebf42d9121005dd744c930006df53d8d411a774655051017d7c70d89540057f7058d540075c60d8d540075f73551310075f21d8d541857e76d8554004ff705913217d7c705855418e7f6355132004ff75d91322177410d9510004fd70d85421ed7f74551300057d70d8d540067c74d953102cfe76d91103d73e7055141004ff75d8d42006fb7058d200075f63581540067e76551200fcfd74d9110005df73585200067f20d953109fb461505400067f71d953213efa20d8142016bc615054001cfc72d85400067c76551312b6df30d8d40004fd75d893108e7f54591300cdbc74581210067c6559110006ef625093139e7c73d953101cfd73d81320347c75d9131004fd7558d20004fe764c94100cfc71d812101cfc72d8d100347c7558d1039e7d41d953111efa30d813217f6c20551200075f754c93145e7f64585540075d544c53018f6e42551200067f5458d1002ebf60509400067c765513041f5f30d9532004fd75d9130034fe75591210b57c754c540017b7745051018f6f21d89541867e61d85540075c63d8554024fd72d81320067d72d95101957e73d8154034fc75591323df3c6255141004ff7558d21006df735913141f5f31d9532006fb70591200557c7559110127cd314c92101cfe72591310067d74d951018e7c62551104b75d42d8d540067e72d95311757c7558543004fd74d8532006ef52d89400057d71d89540defa10d81313a67e30d9531007af62509400067c60d953102cfe76d91200a6ee32d8940004fd74d893125edd32d8d2002cfe7458910005df744c53002d7e74d8554324ff7358d210cebf40591211975f30d8d544167e32d953218d7e72d8d54024fc73d8121004ff7650930336df32d8d210057f7558d41007bb705054000df47648510034fc75d8543007f370505101975f7218d54006fb70591104cf3f64d8d54326df31d8d21034fe75d91300057c765513101cfe72d8d40016dc614c5301877410d855410ede43d8d411975f315513202cfe74d891039f7431d9531024fe73d85404b71f41d8d54005bf74581311b6ed20d891017f7810551101873
  | 2 => 0x4b65f64d8d54126f661d8532006bf7459131004ff75d81320dcff7058d10014fd72d81210075f754c9300075c7355110014fc72d85200363c76551414b75f41d8d5418d7e7258d5402fb771505400075e31d8d5404e7f54d911001cfc72d8d40006df43d8d1012edc644c9300067e64d95310075f635855418d7f7658954007b76450510034fe75d81310075e60d8d540075f20d8d540067e74d95311975c7418d5412ede644c931006bf745912105ef4615852000cfe70d8d424b75e40d8d5405df47158d20024fd70d9130327e421d8d2102cfd71d81410075c6218d540757c7558d20006bf745911049f5f4218d54034fe75d91311975c7018d540ce7f54d91210057d73d89540057f7558d420067f7558d2039e7f71d953118e7e62d895414ede63d8d42007cd324853012ebf41d9132034fe755911039e7c21d9531026df604c530146f661d854201cfd70d852001cfe76d894302cfd70d8940034fc75d91320057e76551314b75d43d8d541373f74551323a77731d95313df3f20551412875f544c5301975c7218d5401cfe72d8d411875e315513117f7410551101cdf77158d100067e60d953101cfe72d8d1002cff76591213a67c32d95311567c6550910004fc7650930014fe71d8d10004fd74d89104167d21d9532004ff7458d100c6dc30d8d21004fc76505200067c75d913101feb60485200347c75591102167d40d9510034fe75d893121f7641d95100567e76d951000cf476485100067d54d81210067c6559131014fe71d8d40007e7614852001cfd70d912026ebd40d912000df6705051000cfe7058d210067f76551200047f7558d20024fc73d9121034fc75d89432167e10d951001cfc7259110024fd70d89301857c71d8954004fd71d81320bfe5204851002cff7659110005bf74585303e73c73551411975f32d8d540075d544c9311975c30d8d540067e6158954034fe75591200075f7355120004ff7158d203d73e30551410075c635895417d7c705895408f5d5450d30004fd74d81310a6ee62d89400357d74d8154014fc71d8d200067e70d95313fedd73d913209ef461585400aedc31d8d401867e615513000cff72d8d20014ff70d89102167d71d95100057f7558d100067c20d95310e6ee62d8931004fd75d81311857c71d8d5401cfc73d893005fe42158121006dd32d85303ed7f74551323bebf40d8941014fc73d8530004fe7650d104b75f40d8d5400cfc73d81311975c31d8d54004fd72d81310075c62d8d5444f3f41d815408e7f6455130065dc7358520006bf7458d10005bf74589100067f5458d211957e73585540067e42d9531024fe76d8d411857e715895400cff72d91200057f71589540065c6118d544367d54d8d421967e635511016eec6258943004ff75d8142144fd74d912101cfe76d893117f5c305
  | 3 => 0xd75591320057f7558943256ef21d8132004fd72d8d4115cfd74d91300fefa40d8141095de7550d303df3c3255141004ff7558910007777158154014fd72d8d21007af645092017e7c6055132086ef2158d200067f42d95310073f7458154004fd72d9130004ff7650d100aedc53d8d40005ef72581310057d75d85420067f75d913206f3f41551200057c7655110034fc75591201767c6550d1002dbf7250940016dc764c53002cfd72d8142376ed32d8931147e42159121004fe764c5400075c73581541873e7155141004ff75d854216cff7259132006bc7458d200357f74d81540067f75591100075e6018d54006ef7258d2100737715514117d7e7058d540067f7655132004fd75d894118d7c72585540067e20d953102e3c645513003fe462485104167f73d953201fcf734c921007e53248510026df6050d30006df73591303b5f7715894101cfc72d81410047e76551321857e71d8d54406df30d894300cfc70d89310067c655853201faf74509200075f735513207df47158930095dc754c5300067f54d8121034fc75d912000cfe70d8d1006ebc43d912002ede6450d30004fe764854005ef621d8520004fd74d85204b75f64d8d5404ebe64d911017f782055120014fc71d8143014ec764c921105ec725814109ef451d854002cbc7458d20004fd73d894101cfd73d913217e7f6155110005df735854000cfe70591211877641551100067c60d953202cfc74d89104bd7f7458d54015f4714c941004ff7650530015f772485100065c63581540067e765513100cfd74d8540006be43d91200cebe64d91212f67d54d894008f5f5450d300067e43d9510004fd71d89431873c7655141024fc7359120106ef205912139e7e21d953100cfc74d814135ebd42d9121014fd73d91310057f7558121004fd75d8d1000cfc70d8d411873f415513128edf32d81314367f54d8d42004fd7558d1001cfc72d91310075d544c930004bf745891002f376155141034fc75d89303675f544c931006df735913200cec7648520344ff7259121004ff7650d2118f6c32551323d73e605514100cfc70d894301cff71d8d2100cfe76d81411975e7418d5401cfe72d91200063f645512000cfe70d8520034fe75d9110004ff765091000dbe7050540006df6350d21024ff71d91311957d73d8d54245ef7258d2001cff73d91324176c32d95320075f73551300c6dc53d8d2108e7f54d91304b75e41d8d5413efa60d81420057f754c9400067e10d9532004fc7650d103d73c2055141006f771589100557c7558910004fd75d8d41024fe76d8d4218f7b205512001cec725911000cbc76509400047f7558d101957c7358154004ff75d8d204b67f64d8d540067f65d8d1012ebe64d9132034fc75d894117f6e2055120025df724c9311975c32d8d5402cfe76d9132
  | 4 => 0xc910106ec20d89410067c62d953101ee46248510005ef7150920086ee32d89301873f1055141006bd54d913000ddc764c530005bd74485400075e32d8d5408f3f4155130026df614c931004fd71d893000cff73d913012edc644c93100cfe70d8d2102e7c645512100cfe70d853206f6d54509203d73e2055141126f621d853201cfe76d89102bebf40d913002cff765912000cfc70d8532004ff72591300bff070485100075c71d8d54004fe7650d200067d54d8910005ef725853002d7c74d8554004fd72d814340edc43d913200cdc7650d30005df735812140ebf43d9132124fd73d8d2102d7e74d8d5402e3c645512000777715512101edc624c9312aeed32d893000cec76509200067c64d95310075f2018d540071f735514101cfc72d81432de7d54d8141006bf74589100057d72d8154026df604c930004ff764c52025eef21d8d2000ddc764c9300067f41d95322167f70d95100befa10d81210ffb54050510024fe76d8d20275fb705912000dee70485201febf40d911012ede644c930166f631d85430067c71d95320957c7558930024fc73591210ee7d6455131004ff75d854000df47650510006df634c940024fd71d91310067c75591320c6df3058d2147d7f74589540057f7358954004ff75d85301ddfb7058d101975c7118d54004fd7558d211357c7558132004fc76505300d73f7455121004ff75d9120004fd73d812101eef6050920006ef7258d101873c21551411c6ed21d89100075e72d8d54025df724c930004fe76505300e6ee32d893102cfe74d893001cfd74d8d42025df714c530004ff7650520024fc73d854229f5f544c9300075c7358954004fd73d8542006f771591100075d70d8d544a71f6418d5441e7c43d9532004fd72d85433675c754c93103fe632485100dcfd73d8d10004ff75d8910004fd74d8d20336dd32d8d210f67e76d9531386bf41d91310347c7558910004ff75d89400067c63d9510024fd74d814301ebe6250940014dc764c93101ef462485101873e2155141306dd43d8d4018f5e32551322f67f54d894000cfe70591320065c63d8154004ff75d8131046df3258d10004fd764c910005f7714c94139e7f10d953100dde704c930004fd74d8d2118f6f2055121014fe71d9130004ff70591311aef710d8520014fc71d8d101955e76d8d540357d74d8d5418d7e72585540067c65d89311957e735895404ebc42d911013ef860581420067d75d8d4033d7f7455121125f47158132034fe75d8132034fe75d85200057d72d8d542b5df7359130014fc71d91100067d54d8d10004ff76509310067c6158954006df7358d21004fd75d91100067c6558d100067c43d951021e7f41d95100067f75d9110004fd71d913000cfc70d91103c67d54d854300cfe76d8121006de31d8d4041e7e43d9532004f
  | 5 => 0x3f6df32d8d420addc7358540095de754c5300067f43d9510014ff70d8d1039e7f21d95310067f65d81310067f54d89100047f7558d2131def7258d213e73c635514114edc4359132004ff75d911002cfd70d8540016f7605051001cfd70d8d200073f7458d540047d74d95324773f74d855405ef431d85202de7f54d81412e67d54d8540034fe75d8d21004fd72d854002cfc7458d2102cfc74d813211fd8704c930014fc71d894000cf47650510016ec61485200067e75d8542006dd32d81310075c2118d540075e6118d540067c755913100dbe705094011efa20d8132006ef72591321fcff745911008ebc42d9130006be40d91210075c63d8954024fe73d894106fac645092049f5c4118d540067e61d8954034fe75d89430075f6358d541965e7618d5443d7f74581540067c76551322167d10d95102c5fb7059130024fd71d893117e7e60d8154034fc75d85422177610d9510004fd72d8d402167f71d951002e7e64551320067e74d9510167e42150d210f57c75589311157c75581411957e73d8554024fc73d85200067c65d911012ebc40d913238df771591310067f65d8910024ff7658d101873c7155141166f661d8543004ff75d85321975d7018d54396bf43d913118e7c62551304773f64d8554087cc624c930004fd75d912107ef421d853016eee42d8943127e4714c92139e7c31d95310067d70d9531006be41d91300347e75d85420067d62581540075e62d8d541876c215512101eee62485301873f415855441f6f32d95320077b605815402cfc74d8930046dc32d8d1012f3f415513200dec7050920146f621d854249f5c4018d54026ec634c921006f731d8520024fc73d89411967c635511001cfc72d8d2015efa40d8143004fd72d913101eec624c9400c5dc7358121007355450510006bf745913018f6f21551201857f7158554004fd71d913208ebe64d91304ae5f6418d5434cff74591210067f54d8d10146f46158542014fd70d891005ef661d85200077610d85540357d74d895401def74509202cebd43d913017d7e70d8d540057f755913149f5e4218d540075c2018d5401cfd71d9121006fb7059130005f57448510004fd71d89403a67f32d9531004ff75d91300076f725512118f6e62d8954005ef725854002cfc74d81313df3e6255141016d4614c530025de735053049f5d4118d54024fe73d85203c67f54d854339e7f31d95311957c73d895417d7c70d8d54007e7714c92111efa60d81320047c76551100057f75591320347c75591324b73f41d8d54007776548510066de63d8d20006de30d8d41014ff73d913100cfd71d8d100067d765512039e7e71d9531004ff75d8943007cf624c931014fc71d814200cfd72d8d2017d7e70d895402cfc74d89311967e6355120106ee42d8941034fc75591311367c654
  | 6 => 0xf75591201975e43d8d54004ff71591201873d41551310067f655093101cfc7258d10034fc75d8532014fd74d89413e73e63551410c7cc434c9210067d54d85203a67d43d95310edbc7458131004fd73d9121004ff705912117f7610551100073d7055141005bf7458930004fd755912102cfe74d853217d7e705895402dbe74485400075e2018d540067c74d95102ee7d54d8142024fe73d8142026ee634c921024fe76d8d40016de614c530005df73591101cef710d8530386bd41d9131004fd73d814117f786058154004f77158d20006dd634c910106ee62d89410fefa10d8141004ff75d8d100067c65d91312167c40d9510004ff75d8d400067c73d951013faf2050940004fd73d8940007cf624c9300eebc645913146e7f64d8554014fc7158d201f6f710d854018f6f2155132024fe73d91200347e76d95311876e2155121007b76150540095dc7550d300077471581541975e43551300057f754c520006ee20d8941034fc7558d2002cbc7458910004fe7650d214167d73d953229f5c754c9300067d54d89311873c315514117f7a40d815400cfd73d89300075d72d8d5401ddd73d9132127e42158d2135eef20d91210057f7558543006ec72591100067e75d8d400057d71d815402ef464505100067f61581540067e73d95100067d74d9531005f772505100bfe710485200055f73585542fe7d54d8143004fd75d8930004ff764853000cfd72d91200073f705514101cfe72d85431773f6458d54034fe75d814300df4705051000cfc70d8d42005bf744c94109ef641d85400075e2118d541873f315514102cfe74d85201573f645895403dec7258d100057f754c9100f57c7558131007bb70509400067f40d953102eec6450920034fe75d89300073f74585540075f72d8d540aedc6358d400f57c75d913100cfc7058d21004fd74d8d1002ef476505101976f32551324b75d40d8d54005df7250d300bcff705891021e7c41d951006ebc41d912015efa60d81431955c73589540067d62d81540067e62d95310075e71d8d54004fc7650931004fd71d8d200075e10d8d54034fc75d8121014fc71d8930007755448510004fd74d893006ebe54d9120004fd73d91104176f21d953218d7d72d895401cff70d91200eebc40d9131005bf725054039e7c10d953106f6f545092004dbc745891001edc764c930034fc75d814300dbc70505401867c61551200067c755911001ede624c93102cfe74d8d200067c42d95310076c7258154004fd70d85433ce7f54d8d4107fe42148530014fd70d91102d6bf65505400075f7355121014fd74d8d41034fe75d9121005bf7458d200b57c754c9400defa30d81313e73f305514118e7e62551300067f61d81540073d54589410067c75589102bcff74591303a75f32d95310a7ac625094039e7d31d9531
  | 7 => 0x81320047d74d9531015ec714c9210067f65d85320057f7558131004ff764c9100067f65d91320067f65589310067e61d9532005ef704c9211d4ff7358d100067c65d8d100057f7558d201bdfb70589100073f72551410aede43d8d40004fd71d814241e7e30d9532006df53d8d21004fd75589100075f63d8554004ff7650d200067d7655110126f410d8532127e7104c921006ef63485203a67d32d95310075e70d8d543ce7d54d8d410957c7558530026dc634c9410075c70d8d543a67f30d95310bfe870485200ee7f5459131004fd72d8530006ed6348520004ff75d89300073d54581410075c63d81540067f62d81540079f6450d3000cfc705912100cfe76d81322fe7f54d8143004fd73d85401d6df30d8d1013faf40509201977731551310067f7655130004fe7650520436dd43d8d4217d7f765815400cfc70d8520014fe71d81421357c75585320cebc64591213e73f32551411967e635512101cec7258d100057d72d855438edf30d854318d7e72d8554014fe76d854039e7e41d95310073d545052036df771589313a67c30d9531004fe764c940004fe764853000cfd73d91300073d54d89412a5fb70589300075c6118d54026dc634c94001ebc7650940004fd75d89400067c61d8954004ff755913212f9f43d91320067c63581541965c6358d5421e7d41d951039e7c71d95312167f20d95101975c43551320067c7558d10007e762485100067f76551310067c75d9132017f36050510005bf74581324b75d74d8d54014ff70d91100067c7558d214167c73d953202ef66450510004fd73d9120034fe75d8d10007db7050d303a67e73d953117e7e605815419f775448510034fc75d853000dbc76505403df3c72551410357f74d89542ee7f54d81423a67d30d9531015f7745051047e7f64589541975d7118d5417d7e7058554004fc7650d210065e6218d54004fd70d89310057f75589102ddfb7058540034fc75d8931007f370485100065c6218d540c6de43d8d21004fd73d89100defa60d81311873c10551413d73c6055141034fc75d85400067d76551314bf3f4158d5401eec625093100dde7050d300067f70d95310057f7258d540067c75d9110006f77159121264ff72591202167e30d951003eec625891012edf43d9132006bf74591321977b305513039e7e31d95314257e76d95320347c75d91323f4ff735913202d7c74d8d5400cfe70d85433e73e73551411873f4155121004ff75d913141f5c43d95320067e40d95310def860581312e67f54d854000df47048510006f77158d20005dd73485301975f7118d5400cfd73d8530004fe76509311873f21551410057c7655132255fb7058d2002cfd73d854301dee72505200067d54d89300573f74551100067f6558131004ff7458d20024fe73d89103d73c7055141004f
  | 8 => 0x67e63d8154004fd755912018f6c72551210067c63d8154296f531d853002cff76591320073d544c94149f5d4218d541975e74d8d54126f631d85321957e73d8954014fe71d91201867e615513202cfe74d89313beed42d894110edf32d8d41006f77159131004fd75d85300ffb71050540034fe75d8d40346ef21d89410057f755893037edf31d8d41034fe75d8910004ff75d8d2142def7258d42004ff715913000dec76485203f5df7359132006f721d853017e7c6055131024ff7658d200067f54d8931034fc75d91101e6dd31d8d1002cfe74d85300073f7355141126f641d853217e7f63551303febf42d9132014fd70d8d100a6ee42d894008dbc7458530004fd75d8542005bf74585201b4ff72589100b57e75d8d404167e42d95320075f654c93101cfd71d8d214167c20d953217e7f605512002cfe76d91210067c65d89100363f7655141034fc75d8d202fdfb7058d4002cfd73d8143005bf7458d100067f74d953200cfc70d9131004fe7650910005df73581410073f64551200067d54d8d20005f7744851021e7c21d951001fe771485200067e74d95320067f65589101867c615513200cfd74d894039f5c31d95313d73c3055141005df7358910024fe73d91301febd40d911002cfc7458d10034fc75d81420067d54d8132004fd70d894302eec7650920006df7358d200057f715815417e7e60551210067c32d95100047f7558910005ef72591100fcff70591100067e765512102cfe74d81320076f62589541873e315514112edf435913204fb6545051002cfd73d8943164fd74d91311557c7558d4201cfd74d814249f1f4118d540073d54505303a75f30d95314167f20d95320067c41d95323a67e32d953134fe421d912112e7f6455132004ff7359121095dc754c93001cfc72591310067e62d95102edfb70589400067d5458d2039e7d73d9531004ff75d8d41004fd74d8121004ff7159132026de634c9100eebe64d913115ef86058143006bc74589101857e71581540aede63d8d4000dee705092000cfd72d8520266ef20d89400dfd8704c5302167c70d95101873d71551411957e76d8d540067c61d95320055f7358154024fc73d91300067c40d95320075f754c53018774315513102cfe74d8d10004fd70d9132005ed7448520004ff7058d2110edf3059131024fc73d8910014fe76d85431ed7f7455110164ff7159131004ff7359120006ef7259121095de754c9300067c76551200067e42d951002d7e74d81540067f54d8930034fc75d8d101e6df31d8d100955c754c5301bfe421d812114edc53d8d42034fc75d81321965e63d8d540067f54d8520006bc7458d1001eef60485204653f7458554015ee714c92102cfd72d85420067f655813239f5e31d9531004df73591101967c63551212167c20d95100067f65d
  | 9 => 0x4615853201cff70d8d20187347155141014fe76d852007ef631d8530006ef725912044f7940d8154006df53d8d4002cfc7458d2039e7d21d95310067d71d95320279f7450d301357c7559132004fd75d91201b6ef20d8910034fe75d8940006df7358d10004bf7458d1002edc7650d3000cfc705913118764215512101fe7614c9214167e21d953208dbc745893012f5f4355132006f77158d100757c75585200e6ec625893127ebf42d91200067f42d9510034fe75d8d20014fe71d8d200075c7355120004df73589100067e72d951009ef661d8540004fd75d8d401157c7558d41007eb7050920004ef725911001cfe72d85400067f54d8d200057d73d815406e7f645512004ebc43d91100fff070505100057d75d8d400067f54d81321857f7658554004ff75d812113efa40d81424b75c74d8d541f4ff7159110004ff75591311873710551411957c73d85540047c76551310befa60d81210067e64d95320eebf42d913110ede63d8d4102fbb6050540014fc71d913018d7f7258954014fe7159132026de634c5200067d76551300075c1018d54004fd70d8d2101cfc72d91104175e32d953212e7d64551322167e20d9510034fe75d913201ebc6250940006f77158d2118e7c62d8954004ff7458910006be43d911017e7e60551310fef860581413df3e3255141086ee62d89300557c754c910004fd73d85200067f5458d200d57c7558d2134ebf41d912100dec76509200057d71d8d5412e7f54d9132014fc71d91320063f64551300075f43d9532034fc75d8d4218e7e62551100075f73551101873f41d8554004fd72d81410ffb870505400057f755853001cfc72d81311967c63d8d54146f71059121006bf7459120034fe75d81410067d54d8530004ff755911018e7e62589540067f54d85320a6ec21d8940146f641d85420067e765513202eee645092018e7c625895413fb87050940004ff7458d214167c21d953230fcf434c9210057f7558540045dc73591100347c75591310057d74d951000cfc70d91321975e7018d54014fe71d8930045dc73589100057f75581321867c61d8554024fe76d8d1021e7e21d9510166f4615854302faf7250940004fd7650d2017d7c70d855401def71485204167c32d95320067c74d9532004fd73d81420076d544852017f78305513009fe421485403b67d54d8542015dc764c93149f5c4218d541877421551210a6ec52d8940004fc764c5401173f76551410075c6018d540ee7f645513115fd87050d301975c73551314167e72d9532024ff70d91300067f7558d101757c75589430067f65591320057e7655110004ff7648540014fc74d85400bef86058121034fc75d8131014fe71d813206dbc7458d20004ff7259110004fd75d9132014fe71d814341e7f43d95322bebd40d91300075c6358154
  | 10 => 0x51211873f415511018f6e3255121004ff75d8520004fc76509100056f725815410ddc7358141244ff7258d2010edc53d8d411957f7658d5402d7c74d8954034fc75d85204c53f7458d540067c65d813211ef86058132024fc73d89400057f755893106ebc6459120024fd70d853001cfe7258d100075e30d8d54006bf645093102dbc744c9411873d415512149f5f6418d540067c65d913206e7f54d91201975e7618d54006fb7058910026ec764c9210075f71d8d540067f5458910024fe73d8542024fd74d894337ddf73591310047d74d95102167f30d95103df3e72551411857c71d81540076d544c9214b55e7618d540067c65d853243f3f41581540347e76d9532004fd75d8943034fc75d894002cfc74d8d20004ff755913003eee62d89100067f7559131005dd744c530127d4714c931346f710d894117f5e305513002cfc74d852017e7f625512000ddc7650d301acff715891000777655051002cfd71d894101cfc72d85302257e76d951018d7c72d8154014fe7158d200057f73585540067c64d951012e7f54591320067f10d95320067c7655110024dc73591103cedd43d8d41025df7450d30004fd72d8d10034fc75d89104167f42d9532014fe76d85420075f2118d54027cf724c9311957c735895410edc6358d41007db704c9300075f1018d540067f54d853013cff70591201975c7355130004ff75d8141024dc7358910024fc73d8540004fd75d8d210067f655911001eef614c921007d7714c93102e7e64551310067d54d853247f3f41589540057f754c9410e7cc624c9310c6de63d8d2139e7e10d9531014fe71d8d424167e20d9532024fe7358910005df7150d3002cfe7458d100057f754c54007ef4615853021e7e71d95101567c6550931014fe71d894306e7d645512018777105512112dbc745813215cff705913002cfe74d8121086ec62589300047e76551100057f7258154004fc7650d2010edc30d8d4100dec704852022f6f54485203febd42d91320075f70d8d540075c63585541867e6158554166f641d8543007eb7048520004fd75d85321867f625512149f5e4118d541557e75d854200cfc70d89410c7cc634c9211975f7418d540067e635815431cff7258d211d6dd30d8d1002e7c645513020ebf41d911049f5e4018d54005ef7258141034fc7558d211867c61551300073f7458954004fd755913101cfe72d91300ee7f54d9131376df30d893100cfc70d91210067f74d953108f3c6455130406dc43d89430067f755891001cfe76d894123ef521d85200076f754c92149f5f4018d5419f74654851001cfe76d8930016e461485203b67f54d85424b75c41d8d54205fb70591104973f64d89540067d5458910034fe75d8142034fe75d8121006ee21d894000ddc704c9300057d73d85542167f10d9510126f
  | 11 => 0x67d72d953102cfd70d8d4017e7e6055132024fd72d85324167f32d953240edf30d91324853f7458954006ef7258d20034fc75591101877621d85544573f64d81541867e61551200befa20d8121004fd75d8543014fe715912002cfc74d8d21004fd70d91310347e76d95100b57c75585403067d54d8d4001cfe725913021e7f21d9510027db604c530005bf745812112ebc6459132024fe76d8d21014fc71d8d4217d7f70581540067c6558131004fd75d8141004fe764c910004ff7558d201967c6358d5407ef661d853000cfe705913102cfe74d81311857e71d81544b75c40d8d5401cfd74d8542006be40d913204f755450510004ff75d8143004fd7650d214b75e42d8d5400cfe70d91100075c20d8d54024fc73d8141004fd70d9121004ff75d85430047e765513116eee32d8943024fe73d894000cfe70d894102e7c6455110004ff7258d10024fd74d8543006df624c530034fe755891013fad4050920004fd755911039e7f41d95313176f544c921006df634c941004fe7650930004fd75d81324167c72d95320067e60d95323b6bf40d8542004fc764853040ebd43d913202dbf71505400757c754c52004e7d645511039e7d71d9531006de32d8d10005ef74485203a67c43d953106e7f545912018d7c72d8d541975d7418d5407fd4614c530014fc71d8132006df7359110024ff7658d2121e7c31d951041e7f30d953201cfe76d8940006f47158d2016eee62d894302cfc74d812132df77158d210067f655091027ebd42d912000cfd71d911021f7b10d95103a67e43d9531004fd75d89100067c7558d200067f655913118f6c20d8954006df7358910024fc74d8d40034fe75d8540046de63d8d10016ee61485200057f7158d540067f76551100bfe72048510127cf214c93118f6e42d895401cfc7259130025de73d9132024fe73591200067f62581544b75d41d8d5401ef476485104cf1f64d8d540067e64d951001cfe72d8530006de30d8d2102e7c645512021e7f31d951000cfe70d912117e7f60551100067d74d9532004ff7259131004fd75d8143014fe71d91100057e76551321857c7158154005ef7258d1037cff73591313ad7e76d9531034fe75d8543014ff72d912118d7e72581541975c7355132046dc6358d10405ef7259132004fd70d8941034fe7559130014f47158d20004fd72d9110034fc75d8d400347c7558d2001cfe72d91310067c655813202cfc74d85300067d54d8d210067f32d95100073d735514106f3c645512001edc764c9311957c73d81541857c7158d54024fc73d91101157c754c941014fe71d894048e7f64d8954014fc715913017e7c60d8154004fc764c9102aedf31d8930034fc75d913103eec32d8910034fc7558d10007d7614c530006ef72589101975d7218d544be7f6458d540067f765
  | 12 => 0xf61551214453f745815417d7e76d81540067f72d95313067f54d8d402167e40d95100075c73551210955c754c93000cfe70d891001cfc72d91204167f21d9532017e7724851002e3f61551411975f30551311f5f77159110004fd70d853204f77545051028dfb70585303c5f77158d410073d54d8d410067c10d953200cfc70d8d101955c7358154014fc71d8943004fd71d8d4002cfc74d8d102d6bd6550540034fc755912118d7c72d855401ede624c9300067c72d95100067f6550d10384ff7459131027db6050d30024ff72d913204fb4645051002e7e6455121004ff764c540014fd73d8931004fc7648540034fc75d8d41004fd7650910024fe73d8141024fe73d9121014fc71d8d400057d74d953234ef710d91212167c30d95100057f7558532066dc31d8d2004e7f545911000cfd74d8d400357f74d8d5401ef6624851002f3f6155141006df53d8d4208ebc41d91301957c73585541877471551212167d20d95100075f7358554004ff75d89410067c64d9532144ff71591210067f70d95324167c42d953204ebc645911000cfe70d91310cebc40d91210057f7559110396df30d913108ebe54d913013fe870509200e5ec725813141e7d31d95321877b105511018f7721551210067f75d9131015e4714c921066df3158d200073d54d81410075f63d8954006bd54d91200e6ee42d8931034fe7558d2100cfc72d812100cdc764c5300075f73589540073d5458d410fefa60d81410075c21d8d543fcff7459132005df724c53000dbc765094041e7c31d9532004ff7558d1002e7e645511017e7f60551300a5ec7258540024fd72d9132014fe76d853225edf32d8d2018f5c325513226ebf40d9120006fb7058d10004ef7258d1021f7621d951018e7c625513100cff71d89100075d71d8d5411cff7058d20004fd75d8d42015ec764c92124cff7358d200075e61d8d54005f77158d202a6df31d81322167f40d9510016bc765054018f6c6258954034fe75d8532004ff75d912117e7c605815401feb60509201867c615855441e7f31d9532006ef42d89104175c32d9532396bd43d9131014ff72d8d21014fc7159132024fe73591100067d61d8154034fe7558d2000cdc764c93011cfd73d8d202167c10d95100057f73581541867f61551312f6ed42d8940006f610d853202e7e64551301857e7158d5406dbc745852021e7d31d9510034fe75d8941004ff7359110016ec764852000cfe76d813101edc624c9300047f75591320067c42d9510006dc7358910004fd71d8d42014fd72d9121246ef20d8930124ff7158d2124edf30d8d2000cfe76d81430e6ec20d89310071c7355141027cf724c9301967e63d8d54014fc71d91200ce7d6455121355f7715912139e7f73d953101cfe72d81410557c75d911017d7e70d85540067c6559132
  | 13 => 0xc03100301f00000000100000300500100400600100303c04018d15a00700d1d901d00b00800020600200502850d0001ed00000200f00702100200601b00100000b00000003902400504f0100b900700701e1fa00800002e19b0060050020da03000b00400d00904400701b005005356ef20d8542024fe73d81210057f72585540773f7455120027db604c930004fe764c520014fe76d8530004ff7358910345ef725912100cfe70d91320075e21d8d54027d7714c53048f3f41d895402fbb60509400357d74d855420ebd41d91104167d42d953202cfe74d8d2101cfe72d911002cff765913102cfd71d8d414b75f42d8d54066dc6358d20006be40d91310067c70d9532034fc75589100bcfd72d89100067e41d9532006ee21d8930014fe71d8910004fd71d91202177810d95101967c635512002ebc645093100cfe70d89434167f72d9532006ec7258d101975e7218d540067c65589100067e40d9532025de734853039e7d10d9531005f7715813200cfd71d891018d7e72d8154034fc75d81410347c75d9110026dc6350d2117d7c7058d543675c654c93100cfe76d81421873e10551411975e63d8d540067c65589310ce7f54591210075f10d8d54006ef32d8910014fd74d814100cfc70d854349f5d4018d54004fd70d8d4215efa30d81432167c71d9510034fc75d8d21004fd755913041e7d43d95320075e1018d5426cff745912018d7e76d89542cebf43d91300067f755913201cfe72591100067d615815402ebf605054001cfe72d8d2018d6c72581541875c315513102d7c74d81542167d30d9510034fe75d912000cfc70d8542006dd634c52001cfc72d8543024fc73d814201cfe72d813101cfd71d81210067d54d813100cff71d8d10296df32d853001ecc624c93016cfd74d913234ebd41d91213be7d54d8941015dc714c9310067f65d8931004fd74d853018d7c72581540067f72d951021e7e31d9510007cf634c9210d57c75581210075e20d8d54004fd7650d1042edf43d89430067c70d953101cff76589104167d20d9532004fd75d81421ccff7158d10014fe71d91320047d75d85420347e75d8d40034fc75d9121006ef725911001cdd73d913200cbc765054041e7c30d9532086ec21d89300f73f74551313176c754c921265ef7259120005f77158930014fd73d81311873f7155141034fe75d853002e7c64551320067f7558d21006be41d91202875c754c53006ebe64d912002cfc74589100067f6558d100b73f6458154004ff75d8931005df704c931034fe75d8d4200cff71d91101975f7018d540067f40d95320076e20d895402d7e74d895421e7e41d95100075e6218d5417d7d70d81540067d73d9510004fd75d8540015de714c931014fc7159120007db704c53002cfe7458d2144e7f64d81540057771581541867
  | 14 => 0xa1d401802000500f02d26e00e0050000ab0060070010000010470000410000110380f12410600080070000010170000180030d700003900500003100801100300001b01002d1750eb00032000700000000204601201d01002e02405604000001102100134401500001e00055a00000200001f0003d20040000001e919b01900f0011900040050202dc0090000090c800d00d00000200500701c04900000202501c00008300000b01500002902101300003100203401408016700003706900200300001100200600b00600400400300900e01600100200538934c16700100b00001501700506205400a01a04e0000f90020050010000111c500815600402b0be1330200020060ec01000815300000000001400800a00c00019100205000300101b0eb0020ee00100200c02001d00400200f02b00000208c15b02800200100e00c0650020011c701b00000003406b02701b0130540020280000020320020030020ba00800d00b00600900300803f00a00400228b01b01201302f00209400000800100e0000060000111d000000208f0c300000002366901900600000624f00400200000f00000000100000400600d01001301401600b01002009707b0ac00000100600000101400b00303607401f00000300600600208800400100401600000103300902d00902200601300200000000200264b00500000701800d00702703500a00400001640901d0090000041620040151530000062ce00101e0b200a0050000a10000000050080010310260000450050010020030ae00200303209302500d00000802600001e0200040fb03a00000403500002a01b07a03500000000005d00000001800500f01e0974d009200500d00c0aa00c00e00b02613900304300601911702f01349600301a3ce00c01501300700300e00a00401702601a00800000900206900400a0a208000900800800217801501200400200101602300215a00000000c01d01700d0013ae00603b0040ba20b0de00000200200314300501702500700005b00100003100004101001a01203200000d00c00301200c00000205e02c01902900241401508601a01100048f0000080061770010000080030000000440170140030145d200505b2240040e40080030f50080190160b60330060050b100100e02600f0030002bf00001100400201b00100200402702500003a0023660290470aa0042471740260240800010770020010ee01000600000f04a0d200000d00505a03203700900500745a05400400600500400003002000100e00121a25c17c02c01d01d03d00800300000e0040020030010080510060060113f00390220000f804e03400301f17b00005b51d0b200d01b00001908808c02200900500e0050030550090000000fb0550031ca00c02100d0000301c900e02004200406200202
  | 15 => 0x3280370020000090120020070de00f00000000002d02400400603700e0290a800108622100000f00f07b00201d00701603200003c00001b00300004200000800000200600004a0040a21b003a00000d06c014
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87d87103654c8010fb0e206ca98a5ac7a1021d8d54006a7b9ee4b02a800a3d841d7644c4014bd02310c6aa00297a1b2118d540052ec1c85b2a2094a5d84184635500195ee9b92c688003b14cb21d85300043f438eab226203ace82d8d32504018bb0f308c6aa003179c463d81540053ac0cc9b2a640087e8755162440fb0ff08baec2a126787ddb73551414b70e326e6aa24000d5471dd5324c401e884239aa89081a1fa1f7558d215c70fa0cc231aa80087e87103654c4010fd0e32ac4880c29ba1b72551210062f988ecaa26400c3c75dd1624400187ae8326ca990022fe117558d100043fc2ae3b22640687e859d9315000195ee8392c68829b87d0463d815417e3a3b2a890a2000c3f74551634805f0f90eb0ac0aa00a3760f75d91310062e3aec69928282a6e82043654c80d0f90ab9ec0a08067c20174485100052fc1aecaa2400687e859d932500018bd073b2a89901a1fe1076551320062e3b6e6aa26400c5f75dcd644400193ee839ac488002a761353d8d4100672108ec90a600087d85dd9424407b0ff08baec6a00021fa1c65585320065a3a0e2b1a4000f178355141440018baa9b9ac8880021fa1f65589100043f43887b2a20008ef825d9434400d0fd0b3b2629000387d90735512000c6ec1eebb126094e1c761cd54505294bf08310c6aa283471d873551410068fb26e6b0aa80087e87d03654c40d0f90abb284880123720d755912117c3e43ac4b02a800a5e858c3635040b17d0fba2c488003cc55370505102153ac08e9b2a2000c6f751c96444001aa8e7b8ac0aa003178c476551310052ec3643b1aa800c7554dc563480018de423b2a8990031b1d772591100053dc02ecaa24200b1d84c4063550010fd0e32ac898a0f1b1db754c9210062fb26e6b0aa800c74751c563480031f100baac89090b1d1db65505100062e39ecab122000ccf73dc96444001ab0ebb82649800297a0c62d951000726b90c431aa830c7471d8560550019cee438ac6900c793189544c93001d73436c490a2031a6c825d9544c0018d8cbb92c8880bf171d9544c5300052e4304231aa874a5e83103654c4091bd07baec8900034dd9371581540051ec0ec8aa24094a5f8418463550018790bba2c6880031b1c865581314dcaf43eea98a6000a3e84083654c4012b90eaa26298003170c8765513202c5e422eab1a202ac3c765c954504018bd0e31ac0aa0029de0576551200043ec2cec98a8000d5471d8d605500d0fd0fbaac8988034ddd371581540063632ee4b02620087d84dd5634840147d0938eca9924ec7a101018d545f58ec24c1b1aa800c3f74d5163480018bb073b2a898ae787d046218d540343f42cec9928200c3c74d95604c4f963906b82a8a080e3b20975591100058fc1ae4aa28200c6f65dc9604c4014ef02bb2a8980021f616764c910
  | 1 => 0xd06396ca98802c7e0d70551414449fc22e1b0aa800a5e8390b65440018bf06baec6a0003171d7735913149d8f43ee6aa2820095d8704063550018e8e3b2ac0990023ee017650d210351e43ec8aa260acd1f7418d61550014bd0c080c6aa0021fe1573d91210343e43ea8b122005c3c74d5162440091bd07baec8908024fa1d544c94139d3b40881b2a620687c87d516348401878ea3a2c6900030fd0476551100068fba6e6b12a800a3f845d9544c8091b906baac890003591c7754c9210043fc2ae5b226000b5681988635500b2f50fb02c0aa0028f612765512139d3b40841b2a627cd1c73551605040d0f90ab86c899003179d970d8d540043ec24ecaa26496b1e8488763550010fd0fb2ac89881a1f61076551320043ec3885b2a2000d1f41dcd605500d17f0eaa6c8900039598763d85540043ec3887b2a200087f87587605517763b09310c6aa0034ddc770551410043ec3e85b2a6200a6d82103654c8632dd0fb92c0aa01a1fa1f7558d1017c3ec38c7b02a80087d849d95444179a3ee9b1ac6aa003561d7704c5300051ec24ecaa26200e598018f605500147d08086ca990030f19774589100052b40cc431aa80087e87d85605500d0f90abb286880021f61f42d95100068f388e6aa2820087e87107654c8858e8edb2a4288002d3a0810d8d5400726318e4b02a800d1c73dc154504010f90fb2a64880031d90476551100052fc38c231aa800c5e839d9544400147f0cb92a8a08030f5d074d95310043f438eab22200087e87195604c8014bd0c38ec6aa2ca976126218d540062ebaea7b1a4200a5e8608363550010fd0fb2ac0990021fe1573d91200043ec3841b2a6200a3f865cd54504010ff0ab8ec4a1ad3179d863d89540062fb2ee6b222000c5f7318d6055157a6ee9b0ac2aa1ef8b18954589411952f41cecaa220a9a5e8398d605500337100ba242a0003171cf65591100061ea08ecaa262038be87d91424c4010fd0e3aac488003179d873551211149e43aa8b1a82b3b1f845cb635500195ee8392c888003c5c407355141006abb8ce3b1aa80087f855c3644c4634bd0db9aa8990031ddd871581540043f438cab226400ce472dc563440614790cb92a8a080297a1630d8d2102c5e422eab122000a7581103654c401958e8392c6880023760f75d91105162fb98cab0a6400c5c761cd544400147f08bb2a888003939c86218d5400636396cab22200087f855c762500018bae639eca8800257a1c20d8d540046fc1aec9922000a9e8390b64440011bf06baac899003171db73551310052fc1aecaa26200c5e321d9544c8011df04bb28488003171ce6158954006563a6e4b1a2030d3676dc554504618b8ecaa264989d297a0c70d9531004af43ec6b0aa80087c87551634840166f02b92a8a08031719773589100052e41ac5b02a800
  | 2 => 0xa6118d540045fc22eab12200087e8755163484018beebb9ac4880c61f61175d85420052f43643b1aa800c5c75dcd6348401938e9b9ac6880021fe1572d9131004af43843b1aa8018dd83dd7644c0018bae631ec0aa0029da0664d95320072d400c7b02a83295e87dcd60550010fb0b3b262900021fa1f41d95320043ec3e81b2a640687e85dd9424c4010fb0bbb2849881a1f21573d81420147a40aeab1a4073a5d831c3654c40759904b1a6488252976106218d543df17312a9b12820087e87d0b654c40199ee6392c688273171cc65d81320052ec3465b1aa800c3d74553624c401e8843b9aa89080e37a1f634c940006aa388e6aa24231a6e82985625500147b08106ca988034bdd072581540068f390e6aa28200d5463dc56055001c3ec9b9aa89000297a086118d543e70f31aa9b1a8200d5870dd5324c0018bd073b2a898803591c871581540156b436c298a6000e4e829846355001aaee7b8ac0aa20e9b60871d95320063a080ecaa22000e1f7418d60550053cd0fb8a64908021fa1a76551325f58ec24e1b1aa80687c855cb644c40b878e8aa2c4880bf171d9544c9300043f438eab1a2000c7471d896055001e28e239aa8a0a5ac7a1010d8d5418f32312a890a202fc6c76551214800d0fb083b2a8880063760f75d85300068fb26e6b12a800e54631c560550014bd0d100c6aa0021fa1f42d9510184bb43ee2b02a800b1d8488463550e78b8edb2a64988029d60420d95310046fc1aebb0284008bf845d942440012bd0e31ac2aa00a3d20575591300043fc2ae1b226400cb7741c563480015c90c992428825ac7a1310d8d540063a388cab026496e1c64dcd544c001a28e239aa8a08170f1d154d85300061fa0cecaa2640087d859d932504091b906baec0a10029761a2118d541343ec38c9b2a643295e87dcd62551054bb0638eca99002cbe0970551410061fba8e8b12202fa78805d954484014bb00308c6aa0031ddd47158d200043f43eca9922000c3d411d9544400117f08bb2648820a9ba0840d95320043ec3885b2a624287c86dd562440654bd073b2a890003951861018d5400637aa6e4b222000c5e7118d605516dcaa82308c6aa0029720d61581540343e42ae5b22200087e861d954440018be863b2a899253071d873551410062fb26e6b12a800c5f54dcd624400d0f90abb286908163da1b714c9410052fc1aecaa22000a5e83dd3654415b4bb09308c6aa003331cf72589100351e43ec8aa24000a3d849d9544c801938e9b9ac488002c761310d8d5402e1f3a2a9b1262038dc8758d32440010fd0fb2ac8882bf179d863d85540061e3a0cab026283a5e831c7654c80147f08bb2a8900030f61276551100052e432a89926200a3d849d954440634d904bb2a8880029760e42d9531005a7414e3b1aa873c5c76dd5314c0e94b
  | 3 => 0x1b2a64008ef825d563440658beedb1ac6aa0c2d5a0773551310246e41aeab12200087e871d563484010ff0abb286880028f61375d91104b58f438e6aa2820087c8755163440018b906baec6a0002cde05705514101573436c290a4000d3784dc560550018decbb92c888003931882018d540052ec04c231aa80087d85dd932440014bd0c086c6aa0030f50676551315768fba6c6b0aa874a75811cb654c5074bd07ba6ca990021fe15764c9100062f390c7b02a800c3c76551414c16fc3b08308c6aa002d5a042018d540062eb9eebb226432a5c835d954480010fd0dbaa64880ca97a0e76551210052f414c231aa89093f845cb6355001878e832ac688002d5a0662d8d540051ec26ebb2264038f581dd7644844b938c9ba264980123720d75d81410061fc2ee8b1a200087e8710b654c40d47d0fb22a8900032d1d37158d200062e3b6e6aa22030c6c765513248401cace2308c6aa0039518763585544b46fc1aebb028600c6f75dc9644406166902b92a8a08021fe1573d81410069bba0e2b02a800a3f845d9544c1392bd0fbaa64980028fe19705514100477c12eab224000c3c65dd1634400d0f90faa2c6880021fa1f5458d200061fba6a8b12200087f855cf6050801c9d04310c6aa0021fe157650d200061fc2ee8b122000b1d848c7635504b53908b1a64881db4ddc554589410343e42ae1b224200d1f741cd615504bc38c8aa2649824ec7a102018d5400cf4402e890a4000a5f835d9544c8010fd0d3b2a898802976026218d541952e41aecaa24230b6681dc95448401878e9b2ac0991ce1f21b755813102e1f3a2a9b1a420593c845cb615500147b083aec8990030f5d154d8d210046fc1aebb02420087f855c7624c0018d8e432ac6880c297a1b73551315962fbb0c6b12a894c5d7418f60550051b90eb1a6290003171c463581540147643ac690a400687c855c762500018bb073b2a88820e97a0c10d953200477c12eab222083a5e83103654c8014db05326ca988030f1d365589100070ec24c231aa831b6682dc554484051e902bb2869000237e0d75591214b70fb0ee6aa28200a5f8718863550031b90cba2649800297a1a2118d5449f8bb08e6aa2820095e8718d60550018b8edb9aa89800353dca72d8d54006a6398e4b02a800d3484dc5605500147b093b2a89000a3da1f7158d205cf27210c431aa800c6c75d8932500014bd06396ca880029760e76551100061fa0cecaa2620687e85dd932440091bd07baec898002d3a0a6118d540061eba0c9b2a2000d6772dc5605500166d0caa2828800317553735891021d3b408e5b2a2093e1f611cd54504e94bd07216ca9881a1fa16764c91000636aa6e4b22207af30705514144001cc8c5b2a428801a1f21571d91200043ec3e81b2a62008df835d5644c00b47d0db22a89000293a0
  | 4 => 0x4504010fd0c3b2a8990123ba1f624c94017d2f436e6aa2601295c855d1314c0014bb0c100c6aa2e7935086218d54006e210ee6b024299b1d84dc3635500d0fd0fbaac6900039398b63d89540058ec204231aa800c5f321d9544c401a5ec9b92c0aa0029761a30d8d5402d1f436c8aa26000c3c85dd162440018b8ec39aa890003171cc65589104162eb9ecbb226400a5d8318b65440010fb0f3aec2a10029da0440d95321952f436c6b1aa80087d84dd563440018bcedb9aa8990c6d3a0b73551324b58f420e3b1aa899e1c76dcd545040166f02b9aa8a08021f6127655131186b238aa89924200f1710dcd54504010fd0e206ca990c34d1db71551410046fc1aeab1220008ef825d932440614790cb9aa8a08c34da1f71551415372ca00c7b02a800c5d839d9544c9358eee232ac88801a1f21573d91210043fc2ae3b22400087f855c364484018e8ebb8ac888003331cc72591100062ec38c7b02a8adc5f7618d615517f63b0938ec6aa01a1fa177650d100062e3b0e6aa24200e4c6288063550019a8e7b8ac488302c761262d8d5400637b26e4b02a8a6c5f7018d605500187eebba2c4880023760f75d912101c6f43ec69928230e5461551314c00bc68ecaa28288003c51c773551415b72b208c231aa800b558108063550010fb0bbb286880021fa1f43d95100062ec3cc431aa800c5e76dcd544c4014bd0d080c6aa2db87d046118d541859a40ae6aa282bfb1d84987635500147b083aec888277871cf64551300062e39aecaa2609cc5e73197644c80153b09a9ec6a100a79207704c92100697a0ee4b02a8058be87dd163440614e902bb2a8980023de057558d200061fba2a8b12201295c85dd1314c0091b906bb28488002d560662d8d5439d2ec1ee9b2a6200e1d84988635500163b0910ec6aa0029760c40d95310063b108ecaa22000a5d83083654c543a3d0e39aa8a0a0a9ba0871d9532005a6c14c231aa80593c845c361550014dd05326ca988c69da1b715512158697ba6c4b12a80687e86dd5604c40187eea3a2c69028f17dcc65591320053ac0881b2a645cd377155160504011bb07baec89000e3ba1f7258d1033e3a38ea8b1a40a0b1d8498463550014bb0c080c6aa003175d753d8d410058ec202031aa832b1c845cb635506563d0938ec6aa00637219744c53041d2f418e1b2a6400c5c751cd62440014bb00310c6aa01a1f61076551310063a3aee2b1a4096b1e841cb635500147f08bb2a89080317d9373581540045fc22eca1a20a8d1f7418d6055001878ebba2c69025ac7a1020d8d544cd8ec20e3b1aa800e5863d816055001a9ec7b92c0aa00327dd373589100062ebaea7b1a8000a5d83dd365440018d8cbb92c6881ce9da0472d95310061e3a0cab026400d1f741cd60550018becbb9ac48800335dcc7158d200043f4382
  | 5 => 0xa003591c772551210062a388c6b02a8aad1f74d8d60550014bb0d100c6aa0021fa1d5458d20006aa398e2b02a800a5c835896055001a3ee9b9ac2aa003171c863581540062fb9cc6b02a800a6f825d954480010fb0a3b242a020a9760f74d953200667b98e4b222030e6461551214800147b09baec8988031719773591100063a38ac4b02a8a7c5f7418d60550652bd0e100c6aa0031d197715813202e1e3a6a8b1a4030d34715513250401a6ee2b82a8a08031b1d472591100061ec24ecaa26405e37765514144001e28e7b8aa8a08030fd0676551100061fb2ee8b026400d1d54dcd60504012b90eaa264988035318f72581540046fc1aeab1a4200d5763dc5605500147d0930eca9901a1f215764c9100246f43ee6b2220038ec825d943440638d8e5b12c0aa01237a1f73589100071a326caa0a200593c84dc560550018b8c7b82c6aa0023de0575591104262eb98cbb22640087d879d763500018b8e7bb2a8980030f2177458d2000636390cab222000e5a60d8f60550018b8e632ac88829f87d0463581540343fc3aebb0a840687e87dd5644c8016ad02106c6aa0123720d75591100062e218ecaa2640087e869d954440f5c74c0aa6c0a08030f5d074d95320345fc3aa9b226000a5d87984635500b878e9aa2c68820b171db754c9314a62fba0c7b02a81295c85dd1324c001a9ee6392c0aa0021f61f43d95100043ec3821b2a640687c851d93244001a3ec9b9ac0aa0028f61010d95320043ec26eab1a400087e8710b654400117f08baac6900021fe157650d2152e9dba6c0b02a8018dc835d7604c40166b01b8aa8a0802c76102018d5400636394c6b02a81295c855cd214c0638d8e4b12c0aa0c38dd8154505100062fbb0e6b0aa800e4c63dc96055001ca8c2080c6aa0c61f61c61d89540343e42ae3b12867bd2c72551605040187cecaa282980063d219744851000537c12ecaa22000a5c8358760550fb8d8e5aa2c68801a1f21573d8121415a741687b2a6400d1f41dcd615506166903b82a8a080395a046118d5400637aa6e4b1a200087c8755163480010fd0e3aac899003471c4735514159e8fba6c6b12a800c3f74d5163440012bd0fb1ac0aa25bc5d8773551410061fb2ee8b122000c5e761cd54440051e902baac89000297e0d76551210063bb2ee2b0264058be87dd163480031d90cba2429001637a1f6350d210043f43ecab1a209fc5f73195644c4618e8e2aa2c6900170f1d154d852000626390c6b02a800c5c751cd6444001ac843baac0908ca9720c76551300043f438cab222082e4c62dd5324c0854eb02396ca88002d3a0a61d8d54006a6390e6aa24200a5f835d9544c0014bb06086ca9920a9760c70d95324961e3b6e4aa2820687c855c7644c80147b09316ca9880237e0d74d8910006563a6e4b122030a3c865c15
  | 6 => 0x52fc304231aa80087e87d95624c40d0fd0fbaac8880021f61375589100072a31ee2b02a8048dc835d362440055c902b1a4290003390867648530004aec3843b1aa800c3f65dd1634400187e823b2a8990030f1d954505200043ec3883b2a640687c855d9434800169b04080c6aa0029b60840d95310047bc0aeca1a40008bf845d943480018bb0db9ac0aa0162f2117558d200343f436eab026400b1d84087635500d0fd0bbb2848800e3b20975591300046fc1aeab22403295e870846355001938e839ac488257171cf54589100051ec24c3b2a640095d87084635505f0fb0fb0ec0aa00257a1c63589540061ea0cecaa2200087e871d5634800d0fd0dbaac48804a57215744c9300046fc1aebb028232b1e849c3635500163b08106c6aa00237e0d7650d1002c9e422e5b1aa80087e87d95644c8634dd0530ec4aa00317cc076551320054e41aa9b224005c3c7455163480014bd0c386c6aa0164f21173d89540047dc02eab22427bb2c825c15450527c38c839aa890003c520d545051000697ba6e4b02a800c3c751d1634413d8bee632ac49880359dc871581540246e41aebb0242b1d1f7418d62550018b8e630ac4aa0023de05764c9100052ec1cecaa2423295e87dcd61550014bb0d908c6aa0031ddd77158d200070fb26e6aa2600087f855cf604856b63b09300c6aa00257a1f63589540343e43ea8b1a4000c6c75dc963440071dd0fb92c888016cda1b71551413e58e41ae4aa28200c5e769cb63550018baeba9ec6a100637219734853001d67436c49926000a5d8604363551298bce63aec8990031b1d47258d100043fc2aeca122005c3c7455163440018eec9b8ac0aa01a1fa1476485400043f43ecab0a6400b55810836355001878ebba2c6880030f19774581320156a40ac698a4000c5e76dcd544c0010fd0faa2c4880be1f61175d8d400068e39ae0aa28273e5461dd5314c001a38e439aa8a0803179c863581540062f3b4e3b1aa800b4d829876355129c3eec39aa8a081a1fa1f75589100052ec3463b1aa800c5c831d9544c8011ef02baac89020a1f21b755813200c5e432e890a8000da421dd16048401aa8e231ac0aa0031d1c663581540043f43ea8b1a20a6e5a4018f605500163b08086c6aa0030fe177458d200052ec1cecaa24031c6c7255163440018daa9b92c688003956066218d54005a6c14e3b1aa800a5d86083635500d0f90ab9ec8902928f61275d85420047bc0aeab226000c3f75dd1634800187ee8aa2c68800347dd373581544849fc22e5b0aa80087e87d03654c801aaee638ac0aa0039318b63589540062e3aee6b22200095d8704363550150fb0e326ca880032ddd37158d200043ec2cec992801e87d87193654c4018b8e431ec0aa0034750773585540062e388c7b02a8008ef825d5644c05f0fb0fb16c0a
  | 7 => 0xdf835d5644400147f08bb2a8988028f60764551300051ec24e3b2a6400a6f825d9544c0658b8e6aa2c4880029b60810d95320071bc32a8a0a207ce1c6355163504010fd0faa2c6908031b1cb65581310062f3b0e6aa2400087e87195624c4018bea9b9ac8880025761c2018d540052f40cc431aa89bc5c73197604c40187cecaa282900030f1d065589100072ab88c231aa830f336055141440014bb0d080c6aa0034d553714c9410061eba0c9b2a6200c3f65dd1604c4018beec39ac4aa20b171db754c9300061fa08ecaa26274a5e83dd3654c401c3e87b2ec89910e9da0474d95100043fc2ae7b222000b4e820406355001ca8c3108c6aa0038d21954505100043f43841b2a6200d1f741cd62550012bd0e086c6aa01a1fe1076551104e62f3b687b2a6400c5f751cd64440012790eaa264a08021f21d545891002d9a436e2aa28200d6421dd56348401a98e7b92c0aa0031dd537158d204c49fc22e7b0aa800b1d848cb635500187eea3a2c6880063ea1f70589100343e42ae3b226000c5c311d9544c4010fd0fb2ac09880237e0d76509100064fba0e6b22202293c87551605040d0ff083b2a89880317dd4735891000637ba8e4b1a2000a6e82103654c4018b8ebb9ac4882eb87d066218d540043ec3e83b2a64008df835d5644c46166902b82a8a080297a1c63581540062eb98ebb226432a5c835d954440012b90eaa2649801237a0f75d91100062fc18ecaa26200c6c7218d6055007998e4996c2980029760c72d9510006663b26490a6074a5e83083654c40147b093b2a8980021fe1571d91300063aa08ecaa220bde1c63dd163550018be603b2a8989ce9760c72d95310052ec1881b2a640087e87195604c401998e7b92c8880031bdd77258d100351f43ec8aa260038dc835d3624c0014bb0f310c6aa003531c863581540052f430e5b1aa89893f845cf62550018ec203b2a888003171d7735913217d3d400c7b02a800d1f41dcd625500b27908b9ec2aa0025761c20d8d5402c5e422ec9922000e4d8298463550014bd0c100c6aa0030f61276551310343e42ae3b126000c3f75dd16344001ac8e5b8ac0aa003531cb635815401c76412eab1a2000e4c62c8463550f1a6ee2aa2c6a0a4ec7a131018d540061e3a6cab1a200687c855cf64440614e902bb2a8900c31d1c561581540062f3b6e6aa2200087e8755163440652bd0e080c6aa00a3b60b75d91210062e418ecaa26293b1e84084635500d0ff0ebaec6a00021fe1572d91100078bb9ee2aa282018f8805d9434852763d09108c6aa0029de05765511000637b2ee4b1a2000b348655141440012d90eaa264908ca5721b735815400726316ca9926200a7486551214400d0f90ab96c8980c2cda1f71551410063a388c6b02a800c3c751d162440010fd0c3b2a8988031b1cb6558d100
  | 8 => 0x280042a0000587801401c0188e00c4051700200203835802022020028110080000200d51801c0081406409c0181e00a00002000080029410170101e00b0003c20000b80c0d2000010053d62080100200000c0196403a008008040d40b404059036004000010602c4000001080000780b002028378052280003a0000021086081b15a02c020060022642289000000402002032014000170380040003d1ec028000685d20f0038020289dc03b4400a000348020a00680000600603c08842014034010030183dd6bb953aa0000a80503001c3f02205a02400004044004000010000b091861000120078060020b80b0000060003c0000bc040078037be5bca02e100207000000000034028040060004803b12a0840504302e02c328107d60342800000e06400080000c700480614a00c2c80600205c0c00001a0554b8040020140000b0020141e0020040240005c206078128fd03c10000000002010048760281540181700e028020000360000580416c000360580000f80200246c0340800400605c0b800006000019680120901114002c0040f1890060ec0009a2000501d0033c602001ae300c0000301702009c0100310e00ca580b08809c000741900001406d016004048780fe0040380f054008000400020a80200f028008000110100501980403e2a00080c00605000000000004ae0060060380000902c010eb8010440c00080000c040160000660280008801600001b340c6030010fd0e32ac68800a2fa1b744c9410061e32ee8b026200c5f831d9544c8018b8ebb1a64a000395a066218d544cd8ec20e5b1aa800a3e8498b654c40169b04086c6aa0034b55372581410061eba0e9b2a20038dd83dd7644c80d0f90ab86c8988163ba1f6250931005aac0cc431aa8008
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x20406b8b8000001a134dc004223808e0000100004800d060073c0a0c080000810d0601a0b00a0415240c4a400f95b516961c4735514160d85652811846355001454961cc715815400417e5d868c76355001a1584a066218d5400683d0682984635500184e8718b635895400515a467218d6055001259902182118d5400515a467218f605518560d949c86218d540060761073185625500185587a066218d5400515a5c61d8d6155001c16961c473551410041766276dcd544c0018546121d544c5301860d21b715c15450401a148620d54505100050d650101d9544400145a9718f60581540068561061884635512921d94e1c6118d544a607610431d9544c92941d941c463d81540071118c721c56055001a1594a066218d5400495245868806355001516919c8735514100543a4a711cd5450401855871841018d5400513258731c96055183615949c46118d5400513648311d9544c401a44626042018d5400613a0873985625500144e9718b635895400515a4f761c56055001a1694a066218d540064520473dc15450401914811cd705514100705dd0631c5605512905e98d0c765513256d07a58711cd5450401854831c5625815400613208735d9544c00184e821db735513200513a4b431d9544c801c15410c476551310055125c211cd544840144e929c463d81540049324986840635500181c6421d544c93000615a0476dcd544c40190c821cd705514100507a5a721cd5450401856871876358554007056507118d605512921d94e1c6218d5400615204735d9544c001a45821841018d5400417e5d868cb63550018547120d615815457e45a1c73dc5545040181c861cd70551414a507a5a711cd545058560d94a086218d5400703dd0631c9605500184c7220d625815400515a5c631c5605500164592a046118d5400493a4b86084635500145691dd8735895400513a4a7118d605512981d841cf76551300071118c72dc56055001a15841841018d5400705a507118d6055001c0f411c863581540050d652211d95444001515901c4735514100507a52321d9544c80184e76a0a71d8d540068361282984635500184c6221d544c93000495a4786084635500184d871882018d54006836106208063550014659204076551100071118f721c5605500164591a086218d540041725c86551324c52921c966102118d54
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x12a0d012e108e6aa24200d01649410c47655131
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x98a
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x9ca
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x9ce
  | 19 => 0xa0a
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0xa0e
  | 23 => 0xb09
  | 24 => 0xb0c
  | 25 => 0xb0d
  | 26 => 0xb0e
  | 27 => 0xb49
  | 28 => 0xb4b
  | 29 => 0xb4d
  | 30 => 0xb4e
  | 31 => 0xb89
  | 32 => 0xb8b
  | 33 => 0xb8c
  | 34 => 0xb8e
  | 35 => 0xcc9
  | 36 => 0xcca
  | 37 => 0xccd
  | 38 => 0xcce
  | 39 => 0xd09
  | 40 => 0xd0a
  | 41 => 0xd0c
  | 42 => 0xd0e
  | 43 => 0xe89
  | 44 => 0xe8a
  | 45 => 0xe8b
  | 46 => 0xe8e
  | 47 => 0x1049
  | 48 => 0x104a
  | 49 => 0x104b
  | 50 => 0x104c
  | 51 => 0xb0956
  | 52 => 0xb8956
  | 53 => 0x1549
  | 54 => 0x1409
  | 55 => 0x150a
  | 56 => 0x128a
  | 57 => 0x16c9
  | 58 => 0x1449
  | 59 => 0x168a
  | 60 => 0x12ca
  | 61 => 0x1a89
  | 62 => 0x1849
  | 63 => 0x1489
  | 64 => 0x180a
  | 65 => 0x130a
  | 66 => 0x14c9
  | 67 => 0x134a
  | 68 => 0x2c9
  | 69 => 0xb0996
  | 70 => 0x138b
  | 71 => 0x124b
  | 72 => 0x1709
  | 73 => 0x15c9
  | 74 => 0x168b
  | 75 => 0x12cb
  | 76 => 0x1889
  | 77 => 0x1609
  | 78 => 0x180b
  | 79 => 0x130b
  | 80 => 0xb49d6
  | 81 => 0x138c
  | 82 => 0x124c
  | 83 => 0xcc9d6
  | 84 => 0x150c
  | 85 => 0x128c
  | 86 => 0x18c9
  | 87 => 0x1789
  | 88 => 0x180c
  | 89 => 0x130c
  | 90 => 0xb8a16
  | 91 => 0x138d
  | 92 => 0x124d
  | 93 => 0x150d
  | 94 => 0x128d
  | 95 => 0x168d
  | 96 => 0x12cd
  | 97 => 0xccb15
  | 98 => 0xccb16
  | 99 => 0x170a
  | 100 => 0x15ca
  | 101 => 0x16cb
  | 102 => 0x144b
  | 103 => 0x1a8a
  | 104 => 0x188a
  | 105 => 0x160a
  | 106 => 0x184b
  | 107 => 0x148b
  | 108 => 0xccb56
  | 109 => 0x154c
  | 110 => 0x140c
  | 111 => 0x18ca
  | 112 => 0x178a
  | 113 => 0x184c
  | 114 => 0x148c
  | 115 => 0x17ca
  | 116 => 0x14cc
  | 117 => 0x5ca
  | 118 => 0x154d
  | 119 => 0x140d
  | 120 => 0x16cd
  | 121 => 0x144d
  | 122 => 0x104b91
  | 123 => 0x104b93
  | 124 => 0x104b94
  | 125 => 0x1a8b
  | 126 => 0x18cb
  | 127 => 0x178b
  | 128 => 0x188c
  | 129 => 0x160c
  | 130 => 0x17cb
  | 131 => 0x164c
  | 132 => 0x5cb
  | 133 => 0x170d
  | 134 => 0x15cd
  | 135 => 0xa4d
  | 136 => 0x130e
  | 137 => 0x198d
  | 138 => 0x180e
  | 139 => 0xbcd
  | 140 => 0x148e
  | 141 => 0x19cd
  | 142 => 0x184e
  | 143 => 0xd4d
  | 144 => 0x160e
  | 145 => 0x1a0d
  | 146 => 0x188e
  | 147 => 0x5cd
  | 148 => 0x58e
  | 149 => 0x1a8c
  | 150 => 0x1a4d
  | 151 => 0xecd
  | 152 => 0x178e
  | 153 => 0x18ce
  | 154 => 0x2d851
  | 155 => 0x2cc
  | 156 => 0x44c
  | 157 => 0x131054
  | 158 => 0x5d5d2
  | 159 => 0x5d8d2
  | 160 => 0x58b96
  | 161 => 0xb9054
  | 162 => 0x5d453
  | 163 => 0x5d8d3
  | 164 => 0x185053
  | 165 => 0x181316
  | 166 => 0x5d995
  | 167 => 0x5ca55
  | 168 => 0x59316
  | 169 => 0xa45d5
  | 170 => 0x18d316
  | 171 => 0x185496
  | 172 => 0x59496
  | 173 => 0x5d4d5
  | 174 => 0x18d496
  | 175 => 0x5c2d5
  | 176 => 0x189616
  | 177 => 0x59616
  | 178 => 0x5d655
  | 179 => 0x18d616
  | 180 => 0x5c455
  | 181 => 0x58a16
  | 182 => 0x2c5d5
  | 183 => 0x28596
  | 184 => 0x14c5d5
  | 185 => 0x445d5
  | 186 => 0x1645d5
  | 187 => 0x58d16
  | 188 => 0x18d796
  | 189 => 0x1a9054
  | 190 => 0x18ca16
  | 191 => 0x18cb96
  | 192 => 0x18cd16
  | 193 => 0x2858b9e
  | 194 => 0x4058d1e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1030
  | 6 => 2371
  | 5 => 1126
  | 4 => 93
  | 3 => 2
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
  | 8 => 2*((h/27+packedAt gbK8 (1612+(h % 27)*6) 6) % 62)
  | 7 => 2*((h/420+packedAt gbK7 (38110+(h % 420)*11) 11) % 1030)
  | 6 => 2*((h/811+packedAt gbK6 (113808+(h % 811)*12) 12) % 2371)
  | 5 => 2*((h/389+packedAt gbK5 (66434+(h % 389)*11) 11) % 1126)
  | 4 => 2*((h/52+packedAt gbK4 (6510+(h % 52)*7) 7) % 93)
  | 3 => 2*((h/7+packedAt gbK3 (162+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff03c0781fc0fffffffffffc13c8e3c063fff
  | 1 => 0xc1ffc007fe1ff0f01e0ff01fc6d371ce39d273
  | 2 => 0xfe1ffff8001fff001ff0ffe038e381f3c1e39c
  | 3 => 0x1fffffffe000001fff00003f03fe03fe03e0
  | 4 => 0x1fffffffffffffe00000003ffc0003fffc00
  | 5 => 0xffe0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x22004008020011444111489000406140204a5
  | 1 => 0x4152c0232a0d50a08a8aa056825130ca18d252
  | 2 => 0xb41559a808166a0113a8cb4098a38162c16318
  | 3 => 0x1019aeb5cd4040025dcc81832d03da036e03e0
  | 4 => 0x210e3346719b8ccb8000020437f80001b5b800
  | 5 => 0x398003806103088c01000c183ffeedbc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40459
namespace PEqualNP.Outside.L_meta_40459
open PEqualNP.Outside.L_meta_40459.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := bs0_5_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := bs1_5_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 90 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := bs2_5_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 26 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 134 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := bs3_5_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 56 := bs5_3_0
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
theorem bs5_4_768 : Interval s5Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 781 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 801 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := bs5_6_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 93 := block_range (n:=93) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 93 := bgb_4_0
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 70 := block_range (n:=70) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1126 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056))))
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
theorem bgb_6_2304 : Interval gbAtlas 6 2304 67 := block_range (n:=67) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2371 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304)))))
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
theorem bgb_7_960 : Interval gbAtlas 7 960 70 := block_range (n:=70) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1030 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8feeaeee8feeaa8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40459.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[5,6]⟩,⟨.or,[1,2]⟩,⟨.or,[4,8]⟩,⟨.and,[4,8]⟩,⟨.or,[7,10]⟩,⟨.and,[1,2]⟩,⟨.or,[3,12]⟩,⟨.and,[0,9]⟩,⟨.and,[11,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40459

open PEqualNP.Outside.L_meta_40459 in
theorem PEqualNP.Outside.L_meta_40459 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
