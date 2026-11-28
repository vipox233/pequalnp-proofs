import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36713.Model
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


end PEqualNP.Outside.L_meta_36713.Model

namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36713

namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
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
end PEqualNP.Outside.L_meta_36713
namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
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
  | 2 => 0xf80ff00fffc03fc07c0fe07e0fff03f01627cc
  | 3 => 0xffff01ffffffffff0007ff03ffffff838ff
  | 4 => 0xfff000001fffc0007fffff80003ffc001fc0f0
  | 5 => 0xffffffffe00000007fffffffffc000001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x82090a0804484820451628a1145249542cb55
  | 2 => 0x5565aa694ca3a916be0aaa568dab63a0d625cc
  | 3 => 0x4689494a552932345aa81065a432cb4a9830aa
  | 4 => 0x64cd8d8d9a3223a76f3cdb41093cf1831f40f0
  | 5 => 0x870e0e0e1c3c3c3873cf1c79ce20820c1dbe00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aa00aa00aaaaaaa0aa00aa00aaaaaaa0aa00aa00aaaaaaa0aa00aa00aaaaaaa0aa00aa00aaaaaaa0aa00aa00aaaaaaa0aa00aa00aaaaaaa0aa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36713
namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x5c2cd202c1002d2800024001c0002600119442000000700123c6c000589831f00012980000009144468000a539d18bc19000a0bab1e84a8e02a8005460208001020008302000021e0c880ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x23310541400001a400763b8000027000d40c1600000001f1c8000000078003a000013cac1a289302e7b3c000007f00000007028100fc6f35000e4590a11c1600160000000000fcf8002f8008c09409e8486e000f0408300000000000174cc0000104c64500084000e2409400000919cae5c00128ea37320000000368107033029840008080443213130f860311694876000e0d01a6b3c8005c000d8bc02650000004842a0006c2930000645811108883d15800004d151c45007362140074402080000060e892732a800005b29800004e2596806432f1a0fa180f0780458043060000c00180404000c0000200800045004040800000424000000341c10181000140024000424027ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xac400c80000000ba6004000a805a868000029c398022188c0c81e0240144800000800410878718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 194)*9) 9
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x44100888209000002942410900222a280650a5
  | 1 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36713
namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52903dca5205b94a40bea9481ed52902daa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f7a1241ec42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xd5090afea6a177d4d42afa9a857c5350bb8a6a15714d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa9283ef52506dea4a0df14941f6292836c525077c84a0ef10941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598fb94b31b7296637d52cc7daa598db54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131ef21a63dd434c6fea498df14931ef19263dc324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c6faa418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x29602b9ad168478c588727e7c000000000000001050dc000001bc3221f0e900000005c0017800085c0015b00000000001000000002010004b5459dc0220007725c0000010a8980001e000000000000000004a60005f0a94704c468000000001219a10000d0ec92b000120002592820000024e000658ea92200000000000000920bf0000007000000041e3d0a50000004b80026c000000000003400010e000434570fa00050202d02983000674f39b845294869278056000001df0000000000000000000123414990b600049a00000000170000000002c4594000000ac99d129de32e290dba55114000000000008d4000372f61ec000940000013909e2da00000218000060000df2a6000311fe21e000000001e2000a32792a881038800214a30dd004000000730000000000000000000000000000000a38e40000d4640000007c88706a5283fc4b08f48470c5d8cb2e07980fa542a21404128842876cfd01201c000000000008c53f00000019c002332fe8e4000b246c7e0d309b0001c0368ed0000180013e3b08809a1b124e1146a8000006cc130000006f4c78fe2ba0006d00000004c201ff4c021000085278000000000004e800000000000cc8f22c06bcb587d07c3893093727a2bc00000000000858000009cd3d80034e5bc761254180a039251368000001f70000000010d3266d4000080ba0004a8000000000d96313e18cd2086088660f980a06c0cca912900400400000000004020010060000000100300e0000180000000001007002008000010040000001500400c0580c01e0200c81200400400004002000010040140000000100400400804000000020010000040e8060020100000704c0000100201e00401800000000000020020300680600a008020030000040300100000001800000000008030000000480100000c018040060040100000400400000000000000010020040100400000000002014000000000160000000200201c0000f008004000000060000000100001c030000000300180000802401000002004008020200040080100c008010020060000180900200403002000000000030020040080000c00000806000008008030120180400000c00c018000000040000300002000001000000000080100000080000000002800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857
  | 3 => 0x370d5800000000000004220006d80000074d3b0000000e13191024c0008628a45a624be11207e00000100000000000005240000000030a0006c800258000000d4000000e380031a0004e000000598000eb52a000c09e848e10d111942be0009c16a49679400007276000fa8293ac1ac89920324000000a500048400023000790000000000000000000046cbca4f1c60010c99e0d0244fb0b909c0000b000310380001ec000000ad23d38417c8f84722a7bce50ca3760000017500068c000000de30800000162a1400000000001080c900050cb98420601f869a440003d42a800146000001dd38272481074000a34000e129e8346880051c200000003f65a4000001500080020b3b45913f8c70000b8668000007ac00286000000000003f2000f1800000718000000007300021b0000000001a3520011d8001887b8678090000000002a0ea4446302417e20400000000000000002ac00000000000000000003c29ac001a52e4000c00001ac3782d00523a5c5208dd0969b43b0001ec72c2d84c0008dcca8003600e4b70001f0a0938187400074ce04a44e2d8e722c47c299178313c00000000016a0005027a4426a80014207a000000ac000000e88002500000000c000000000e511814c0f2961d46c92e800000000598000ee00000190248578000002322aca8000230000002320000003f94d3a86f937803350000000004b495c9ca93266554cd0f34bc4d9330191426b82a0003185a1250000000000008304a000399b647841c601a21f21e46099b0008c1010fd33e524ac85c00045c5d1e2178890269d71f87a8738001de000108270000000000044c420f68002b0458552872800e8a4246000148e22501320000010945c4d4a227701e6b0191e94d4124fe80d1ee198bb83c0f4288c5000498a0c001820a20004980012e8240000040e1854b9cd39e59cbb269474001158001b0000a59bf4105301600020829c0a0002645f400000450538001fc43a0000000019c2749822a2c20000012f1866391186443e0004415720680c002561209d40009a372001370004be0000018446813c2f00000000000000000000ba0000008480008b00035c2081c000001341c84f83ec6297a17a2b5480582289d1229f10004681d8fa05e2c1488ae020000c308911a0003620e000000000001e000066000000a00001c5480a3c000000003a13e8b70b2000300654ca7403480020c0001025b124000000e90000000026240c84c0028442c8781680000000000000000088470002384042300000000144a3f4e2054a292a49
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x53c82cd6310b20ab19132c823e64947208f59251c825e63947209758e51c82cd63c87209798f548825d63d52209798e548825d63952208f993538823d64d4e2097d8d518825c6354620cb58b544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534834d6214d209b997424834c53d0920cbd5042482cd6310920d314c424834c538c9209b19532482ac644c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d9d0851483644214520d98c8514836532145209b99721482cd63c8520d914721483645148520d9146204825e63d50209758f540826e62d50209798c540825d63150209d9845408275611502097596530825e6314c209b988530826d6588420d354e210834d5308420d354f200826f6548020d354d20082e461480209ed95200825f63553109718d54c426f62553109b18954c425e63153109758c54c426e6294f109b58a53c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c425e6394b109758e52c425e63d52109758f548426e62d52109b58b548425e63952109758e548423e6494e108f592538426e6214e109b588538423f6454a108f191528425f6354a109718d528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109ed81544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524433854c4110d914a104425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210433954d00109e594400427965840109dd9510042e462440109ed9510042b86444010
  | 1 => 0xc72c6454b31d390d52cc74d4354b31d354a32cc74d520cb319b98b548c66d62d5231a7191328c6cd62cc6318fd91508c63c645423197d8d544c66f62551319b189544c67b60551319e181544c65e6590d3197195434c6cc6250d3197994324c66e62141319b588504c63d65950319bd89540c66c6255031c718d540c72f6255031cb189540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc431b358b310c65f654c431c7551310c677654c4319798f54c865d63d53219e98354c867960d53219798c54c865d63153219798f548865d63d5221cbd89548865e63152219758c548863e64d4e218f593538871e5494e21c7552538874d6294e21c7951538871d5454e218f990538863d6414e21d394f428872d5410a21b358c428874e5310a21d394e32886ac644ca21b358f218865f63551219718d544866f62551219ed81544867860551219798c544865d63151219b58a534863f6454d218f191534867b6054d219e181534865e63141219758c504865f63550219718d540865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530865e63948219758e520866d6510821b358c42086e561108219b59632086ac644c8218f992510863d64944219798e510865d6394421b358f210866f65484219dd95210863f64540218f191500865f63540219718d500871d53d0740c754d41d02b86050740c794f43902ac6250e40d394e529034d5394a40d394d529034d5354a40c794e429029d6310a40c794c429032d5210a40a758c419029d63d02409798c525025d63149409798c515025d63145408f99741502b86050540ab189431025f63548409718d521029d6310840ae580421025f63544409718d511026f62544409b189511023d6590440a758c411029d63d00408fd95401027b65500409bd8954cc26c6255330c718d54cc32f6255330cb18954cc31d54d0f30c755043cc31d54ccb30a719132cc31d544cb30c755331cc2cd62cc730c755131cc26e62d52309b58b548c2cc6250e309bd89518c26c6254630a7590318c29d64cc2309758e544c26f62551309b189544c27761551309d185544c25e65d0d3097994434c25e65cc930a7191324c23e64145308f590514c25e65cc530b358b314c25e63d50309b98b540c26d62d50309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c25f6550c30b3189430c23f64548308f191520c32f6454830cb191520c34e4354830d350d520c25d658c830d354a320c34d520c83097596310c34d528c430a7590310c34d520c430a7593300c34d52cc03097d95300c34d524c0309ed95300c25f63553209718d54c825e63153209758c54c823e6414f208f59
  | 2 => 0x411e000d99c11c22b40005017a854fb97e000050000000ee624e58000006f40000c0007b40012d000000000000000000018600000054a0b0000000000024000087000000814518d035a7380000002e488000001fa6910680020a0001209c356000000002a800025a1a3be000838eb1682906d000000000000d70004f000073000000858002a637c9787641424cb80a538e02c74a043682245b9f63407a07b0780ce718891af32c7e80880433a4b0aa9e50000004a813000000000000000000000031c568000001f800000000000000001d40865c800000082000000000007002f800000000249fe3f8000000610007ec000102b60801100000000000000280610438300006680000018a194000702945b4fa000000000001ac29e1d44fa180c4004000040200000000010000002402000000040000400008160140000c000000000005000000140300000000000080200800000070180100000000020040f0180200403008010380000c0000401004010280801001000010000402c0300400008000000100004008050040100c020040000003000020080100c03020040041400c0201c080040101c030000000001000040100200403018030000000003000000080000c010100400800000000000c00000000010080001c0100000000000000400c00004010180100000004000680001c02010000000300c03074020000000e6f62547439b18951d0e6e62943439b58a50d0f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310e5f63547429718d51d0a5e63943429758e50d0a5e63946429758e5190a5f63542429718d5090b4c53d0942c714e4250b4c6254c42c754e4310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454ccacc6250f32b358c42ccb8e4310b328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551329bd89544ca3e6515132c758c544ca5e6590d32c7152434ca5c6550d32c7151434cacc6250d32cb153324cb1c548c9329e983540ca7960d50329798c540ca5d65d0c3297594430ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41a758c42d065e63943419758e50d066e62943419b58a50d065e6394a419758e529065f63542419718d509071c53d0d41ab189435074f53d4941d314f525074f5314941d314c525071c5390941a758c425071c5310941cbd48425075b53d4141d614f505076b52d4141da14b505075b5314141d614c505076b5214141da148505073b4314141ce50c505073a4214141ce108505073a4114141c754f411063f6550441c754d41106b860504419dd95411066e62d53319b58b54cc67a60d53319e58354cc66e62153319b58854cc6cc6250f318fd9152cc63c6454b31cbd9152c
  | 3 => 0xaf0004e8000920006140002d23c0f02d90015852400159000000000001606a40017c21a4702f0cc140029008390005880f08a36436cec93400a274001521a4000e10a10b45b0000a727e0000015138a7584217523e664000d41ac790f5000000000e80a80005944d91723203c8d8a610400000000000780000c40001ec0004c0000001884f05e0380002310c43c0020e3167cc00000000000cd8003282c8000000007749b1e303e000e416112e5ec990380cc00000000192000468d9170000001a5350000001da04a75c408000c620c14800122000000001ba770000b6000000000900001900380000c0002980025600000000000000f321304c1582114520600000000314000000000d65407c87a2be000000000a822c1b94e432000df00004200078800000000000004103dd061bc000000e79f02c8609011022de000f48000aa068000a23007f4fa800000000001a7000518000003185b8830000003f87f84a40e000000000005050883b000730000ee0006c0939370007e00000015c8584c06f000000f108e0000000000008a404000004205ace9000000134ab0000004d4000002181b4000000006200003f2b01f000113000000391251106d8b18b312c70c000002bc4a4001914000009c000000000000003ce67cf09140004f4b98000900002e00000042800000000000be947000000000004282500021724c3bc001bf1cc0000011a1e630000000000230a1032000000361bb1f41b80009e1ca0000006900000076000276000018000000000000029a4440000000000000085066000b31ba0000000007e2c02f8000000007281e8000007c8000ab000000710000a25fc000473e27440019300060c0004e04e6e509198000000f60002ec1800b00006a6a8000000000003f88032a000669570000000d800000000001ee0001e49c800000688000e4050001030000d03286719235c50cff8f01e82a8f58001bc65cb50003b60005f80016a1c47405208c000008180000000000000052cc398d2b80000c800250000000000000a800000388000c7800176760cf0ba1e4160da8361b032ca405900000000000000000700b9298000849f936e2f0000003921741f1440380006a9a607460400000000484ba1ef000000000f80000007d80000000000000000000000001a20000000000000000000024000000d3000474000000586c4000c70001f4ef115000000980c8012000000001b80007180041e0008b000000000000000004407a8000001a8001d30000001a1710000009500000000000000210000002032623b40019c01a0000417a1620b80009a342000000001d4824b4978246264e68c32ce054ea81d2f21100012e27c000000e70800000000000046001133182318c80742ba5dc158572d068c610cf0006e08212
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x180c800031710201044f04d1932c700000050e0002895525850098088000400b831506250d32a50e4a18a0a0d1973108505070ca98c0a0883431d1520cb31c18c6312a818d0c72550430c60e3b2a8990638355162cc431a18e8b14a710c4d7694c428870ca98c0a0e818318c6255330a18e4aa0879841c7655132cc306aa2c598e61431d1520c830c1ac8a90621860d6454b300c2863a2c429a41135d85310920a8ae6210a290524744c85148322b18a390a419154c6148020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x50600080c8755162cc43180c8755162cc73080c87591520c43080c8759152cc030
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
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20359+((h/221+packedAt s3K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 946)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf03ffff81fffff81fffff83fff03fffcfc7e3f
  | 1 => 0xffc0fffffffffffe07c0ffc1ffffffff238fff
  | 2 => 0xffff01ffe03f83fff800fffe1ffc1e03c3f3cc
  | 4 => 0x1ffffc003ffffff00001fffe003fc03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x94841408c48910805945280a252132a84c3615
  | 1 => 0x2112289109124116029052414a4645512188ea
  | 2 => 0xc28a4d2243a416aaa8249cac13a9181ac2d34c
  | 4 => 0x8b2cb1c492075bcd34f606291cf39063f403b0
  | 5 => 0xc30c1871c386371c738e73180c20183bb6c00
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8c8c88888eaeae8e8c8c88888eaeae8e8c8c88888eaeae8e8c8c88888eaeae8e8c8c88888eaeae8e8c8c88888eaeae8e8c8c88888eaeae8e8c8c88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36713
namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa2e74027001091e26680005400025000000000000000001180440000000000001200000001d080006000c00000012a005960018008367c00556a00111a387800098a000040019488010338014838202001020e0000a1000003ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x25400349c322624200c48503c90449e7ca200048a1a36a8944c64086c16708618ac687e4e52822eb0001298107800662200580e3e4a3a0aa67a5e928406289a462a1c1e008800000000ae8c00aa8e006274000096000000000060a4806a38a05c426e5a40b22c5600727614300a002000204c8000094100a3470000146800048f17080070616327ca5a1cf55243b7a92876c5250f3ea6a1ebd49439e29287ac5250e58a4a1cf950439ea9c853e5290abca6215754c42cf298853d5310b3aa6214754c429f29085ae5210a7ca9994f55332cea1e65ac42ccaeca3995d547329faa4653c548ca7ea8994f15132cea1a653e540ca7aa8196b10832b7a92836c52506bca620d754c419f2a6633d54cc73a8798db94b31b6a96639d434c67ca818cf550319f2a4433d54886bca710d754e21d6214433f5448678a890eb10821af29e815d53d02dca5205b54a409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x18a0180004800003804020000002260000000246a2a0000000000000402c58002001ca8000003000cb9401e00000000000000000000000080020000008030c6254c42a318943cca8d6310b32c910a51ccb15435473287195434ca2d6510832a318943cc70d4354b31a3189434c62c6255031a358c428870e5310a218758c544868d63108218b18954cc28c6250e30a3189430c30d4354830c550d510c28d6310b208758e548828d6310920c314c42483244214520
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x22801800080104282b988528e65411c9435473281aed2988510d047250d510c206bb0a621241415cc4214520
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
  | 5 => packedAt s4K5 (802+((h/14+packedAt s4K5 (704+(h % 14)*7) 7) % 90)*7) 7
  | 4 => packedAt s4K4 (2640+((h/30+packedAt s4K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s4K3 (1006+((h/8+packedAt s4K3 (950+(h % 8)*7) 7) % 74)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 2 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 3 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 2 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 3 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36713
namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3a01080329c59b4060007008d20858055930088f97044130e500061a52442a554bc680142492d5c5831e1e00a940610000381840630185860003400000c5ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe41bc41c83de43907b88720f690e41ec21c837e81906f50320f7aa641ee54c83daa9907b15320f7a9e41ee53c83daa7907b14f20f7a1e41ee43c83da87907b10f20f7a8e41ee51c82dca3907b54720f628e41ef41c83dc83906b90720f6a0e41ec41c835883907bcc720f718e41ed31c83d863907bd0320d7a0641ee40c83da81906b50320f620641ef30c83dc61907b4c320f6186417f54882fca9106f952209f2a4417d548837aa9104f55220be2a4417f53882fca7105f54e20be29c417d52882daa5105f94620bea8c41be418837883107b88620f610c417e508837e81106f50220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483de84907b90920f6a1241ec42483de64907b8c920f699241ec32482fea2905f14520df20a41bc41483de42907b88520f690a41ec214837e80906f50120fd90241ee20483dea8907b95120f6aa241ec54483dea6907b94d20f6a9a41ec53483de86907b90d20f6a1a41ec43483dea2907b94520f6a8a41ec51482d8a2907bd0520f720a41ae41483da82907b10520d620a41ef31483dc62907b4c520f618a41ef50483d6a0907bd0120d7a0241ee40483da80906b50120f620241ef30483dc60907b4c120f6182417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6105f54c20be298417e52082dca4105f94420bea8841be410837882107b88420f6108417e500837e80106f50020f790041fa20083da40107e48020bfaa621bf54c427ea9885f95310beaa6217c54c4378a9884f15310bfa9e217e53c42faa7885f14f10bfa9621ef52c42dea5885f94b10bea96217c52c43d8a5885b14b10df20e21bc41c43ec63887d4c710f710e21ec21c437e81886f50310fd98621f830c43de41887b48310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52843dca5085b94a10bea9421ed52842daa5085f14a10bea8c21be418437883087b88610f610c217e508437e81086f50210f790421ed20843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df20a21bc41443ec62887d4c510f710a21ec214437e80886f50110f790221ed20443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821be410437882087b88410f6108217e500437e80086f50010fd98021f830043de40087b48010fb88021fa10043ea20087e44010
  | 1 => 0xe53086faa610df14c21bf29043ef42087dc8410fb50821f621043ef32087dc6410fb4c821f6190437e510877c8210ef10421f790843f621087da4210fd48421bf280437d50087dea810fb95021f6aa043ec54087dea610fb94c21f6a9843ec53087de8610fb90c21f6a1843ec43087dca210db94421f328843ef41087dc8210eb90421f6a0843ec41087588210fbcc421f718843ed31087d86210fbd4021f728043ed50086daa010fb14021bf29e817d53d037e87a06f90f40dea1e81bc43d02fca5a05f54b40dfa1681be42d037a85a06f10b40bf28e817d51d037e83a06f90740dea0e81bc41d03dc43a07b08740dfa9e81be53d037aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d027ca3a06f54740de28e81bf31d037c63a06f4c740de18e81bf21d037c43a06b88740de90e81bc21d035843a05f552409eaa4817e53902faa7205f94a40f7294816e52902faa5207b54a40b6a94817e51902faa3206f90640de20c81ee21903d843205f94240dfa0481fb40902fea6a05f14d40dfa1a81be435037a86a06f10d40bfa92817c525037e84a06f90940dea1281bc42502fea2a05f14540dfa0a81be415037a82a06f10540f710a81ec21503f680a06f90140dfa9a81be535037aa6a06f14d40dfa9281be525037aa4a06f14940df99281be325037a64a06f0c940dfa8a81be515037aa2a06f145409e28a81bf315037c62a06f4c540de18a81bf215037c42a06b88540de90a81bc215035842a06fd4140dda82817e541027ca8205f94c40bea98817e52103dca4205b94840bea9081ed52102daa4205f94440bea8881be411037882207b88440f6108817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc2fca5985f54b30bf28e617d51cc37c83986f10730ef98e61dd31cc3dc43987b08730dfa0661bd40cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa3186f90630de20c61de318c3b863187b88630f610c617e508c37e81186f50230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930bfa8a617c514c37c82986f10530ef98a61dd314c3dc42987b08530dfa0261bd404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861be410c3788218778c430ee18861ee210c3d842185f94030dfa0061bd400c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83de85907b90b20f6a1641ec42c83de65907b8cb20f699641ec32c82fca3905f54720df20
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0fb94b41b7296837d52d07daa5a0db54b41bf286837d50d06faa920df94e41bea9c83bf439077c8720ef50e41de21c837e52906faa520efd0a41df21483bd42907788520df94641dfa0c83f741906fca120df54241dfa9c83be539077aa720ef14e41dfa9483be529077aa520ef14a41df99483be329077a6520ef0ca419f28c83bf509077ca120ef542419ea8483bc50906fea6a0df14d41bfa9283ef52506dea4a0df14941f6292836c52507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077c8620ef50c41de218837e52106faa420efd0841df21083bd42107788420df94441dfa0883f6411077a8220fd50441bf280837d501077ea620ef94c41dea9883bc531077ea420ef94841dea9083bc521077e6420ef8c841de99083bc321077ca220cf94441db28883bf501077ca020ef540419ea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598fb94b31b7296637d52cc7daa598db54b31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631df20c63bc418c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498fbd4931b7a92637c524c7d8a498db14931df20a63bc414c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c77c8218ef10431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877c8390ef10721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f721443ed42887d88510fbcca21f719443ed32887d86510df94621df20c43bc41887de4310fdc8621bf284437d50887dea910fb95221f6aa443ec54887dea710fb94e21f6a9c43ec53887de8710fb90e21f6a1c43ec43886dca310fbd0621f720c43ae41887da8310fb10621d620c43ef31887dc6310fb4c621f618c43ef50887dca110fb54221b6a8443ec50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690df94d21bea9a437c534877c8290ef10521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437
  | 3 => 0xb0000000de454b322759e7d1a29a43e60000e8c87be00042800000331ce96a7b2d4d41000694cbc468001ba000002330000000d02e69a54c4f9897bc4eca69c0280b5c221d97cadf0782023463f0c0bca0ac03971b374069b5533441c088d9132a4fa1c175a6e520d44dd23a3962d83001566cd1dc18006ec001e38ad3407b18498364e3b922020528bfdc98d46b24853890449a03c0022b000240741ab2bae0000300322ce94c2de24c3919a0ca656000178005c4001fa000458001451942a07800036f21c00e010120000000000501d002000058040060180700e0060000180c0140040280a0000080200204205c088010040080280c0220e80600100000c01815034040048270020340681d02203800008000008028000000d80182e0100080300600c00000014000000088080000000280001a044000060040440680300e0000682b0020280180100000800004008020010840100140180d03a0101a8000460e40080000000005800018004000010020040780100a00c000000060080e8000020540000001402c0100d0000342c0040100a8008000020000181100a01c000000280081b81a00404c01800014004028020000641102a002000010310020000500201a004018000000000080000a008008000000000002900005800001014008140020020000000201e01c000070000040300400201c0900500c0080300a01e0640880000a0000300e01c0100180b00c0380580100200014009000010010010120000d8010000080d005000018020000000100080201400001000000000018090060140100f01a0b4188050020180000a05402403805034000018050160cc0301400e01000800000028028070000c0000090000300001100200002000022000000010080400080201e028000060140080000002001c09df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84216b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428
  | 4 => 0x5820a21000000000d86861a4e22d812edc13d0ce072eb95cb217c828d2d94923a42c000000aa3a8bba4866aaf40e3a5534035b636363a0dd0514c3b8ec8000f31c4f611c92f3320015c019000000000000009ac000002f2001989d116a0a8868007a24e4f80cf4c2fc1842be000bb000000450d94812781d84b5af80038e00098260000000ac800000bd000173000050b080000c001148bd648000a520b344248000000003d0000000005c00025c5e00000000003e000ee80061e000000001a0cf1a72a8506000b40bc41a0008c2377500011511457e704d9a327ba99c232c01ec0b1da0d3640db4b9000138fb5f02ac1fcb28000b1690d69b4bc930051c0c0000000008019d1d6000a28c7598000d3ac200015c003a3000e25c5aa24e0f199807262eb41e6b420000009e9db7ae57dba212422de01ab156aafd5ca80058cfbcb48aa7046292b1bb0f2fa5870b215800057000586b115d39475a24dab3ec6528c0321741049910e154062fe087a591ea9b0158f12aea851a1235b6cf54727c2c6bf811b75784aedd7aee09838cd40812b8ec140810108715cfa5e4920f9ce1923acabc399d456ab801b0741f217d9726a2508f48b2a956e3686b29c1be0000000008e9280000000062d7493f000b996ebb325656ca8ae51280c84d3bc32c620251670007ec0016f7426b18298214c304000000005d4d300029c000ce18e0006c94fbea2aa7e1892433f4000003900d6721c2a5547c75de70a934a5d9c6371408c6cef906770731c93d6192280623c14d04953f022436ee81a39821410c00000210589520711ee7f85bad178867c000c50008b4002dc426dc8580000cac590b1482f0631c7a2f5c2c684c8ff122618fba0f36e81c0f0c0000840f524e0a6e590fb9901666c6c80000036d2b9640006c0f79e65367d80d93226e8891b18f4ece68cc1975f09944416d6d6eb0971b83ce26d6b0e572e97ca93d46a4fb978aab50c7c4e735d14e048240687b6009033cb402cc9d3aaa58e7f5a09af5264159d8265a61247e96e1f6a75963dc6bc6d8e4941354ad0522ae47e150063bb000e807c08e1121dd3aba665061c2d23b0fe789070bb00000185251000e180031e722a000011e51a000003040ba2599f800000001daa4f462bece828f09a1148891f4b4ddd6a2cb05200c4614f000be945b4f2180000031800049c003da28ce6ca1a87400898f4000000f150a1ad2fea480032544a335e7b0114a000ab1336b8ce5a03ab3eae28003bd48e76800000000ac5798252f49194bba46f602428a620fabd5100a8386ad8002382cab35db887448af18e32607eb650427b5d4a810d0ef000fcc00000288a5521000000001f1000000000001710000e18a0e9000000000b40009bc003e700000000000616da055800206df99f1850f83484f0b92369dc003d20001
  | 5 => 0x7722189f09d060d900007a0008b8003a91dad505087502641c0000004244c1e8007d0d18308dc362accde9c20da4a8312ad0006e54217d31a100e916c7445ac000002b4f2131b493f87b533000000ac9290c258200031b503084d40019065a45d6288f248e11f59421a20b5e805b1cca15e0215622b48003106e6c4cd48005224e1b12c870e74c3b2051967286f2e4604c6427272498288038780bc3e802000000ac00012c02265529a503d24252c0b863e790f73e34ba000de11061af318308a7ecdb8000000006b96a8170ce0004a8422b0be50eb57202de9b383a5da7551e0832c0de5c08f2606a65cf1cd7e2b68ff8001ae6782800015e1b8bd8592624f1648083bc12d3a24b10085d838c35e41eccd2093b0b7c9a14b518e359c0e74800f0d09f252cefc0529e0b89140017e43c5790c0520d46d03f23517c71977858000a948e3e104e001208335ced30c98b3076384e78007cc469670981aa4a5539b54a8bdd519eb77c0009d1220ccd6c001e51162fc0000018c005862fc26cda81202817400027bf22f878d3cb60232e21c70056fa9cd998005fa001a58007a6ea9eaa882246f8000006ccc8d0ca89762831e19bf4fe9a5b09e1000000001f96b0ed9fb8006febd8001205d
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x21843a44108610cb94b408432d52d0210cb949408432d5250210cb953208432d54c8210cb951208432d5448210ea501208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e61151108f184544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524426e61149109b184524423e6590510c7d4e414431c5390510cbd4a414432c52905108f994414431f5310510c714c414432f5210510cb1484144354538c5109d195314426e6588510cbd52214432c5488510d3d4e214434c53885109b994214432f5408510cb150214434f5308510d314c214423e65d0110c7d4f404431c53d0110cbd4b404432c52d0110ad987404423c6550110c7d4d404431c5350110cbd49404432c5250110ad185404426e65c8110cbd53204432c54c8110d3d4f204434c53c8110b9987204426c6548110cbd51204432c5448110d3d4d204434c5348110b918520443a94048110d614f104425e63d50109758f540426e62d50109b58b540423d65950108fd81540423d60550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c109d984530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548109bd81520426d60548108f990520423d64148109798c520425d63148109b988520423f65904108f596410431e5390410c754e410432e5290410cb54a41042b960904108fd94410423d6510410c794c410431d5310410cb948410432d5210410ae580410426f65884109b596210432e5488410cb552210434e5388410d354e21042e960884109bd94210426d6508410cb950210432d5408410d394c210434d5308410e910421042e960084108f992500423d64940109b98a500426d62940108f597400431e53d0010c754f400432e52d0010cb54b400423f6550010c794d400431d5350010cb949400432d5250010d654f3004279650c0109b597200432e54c8010cb553200434e53c8010d354f200426f6548010cb951200432d5448010d394d200434d5348010d554f100427965840109dd95100435553440109ed9510042d86344010
  | 1 => 0x82ae6488120ab59220482e96095120b3d8d54482cc6355120b9d8554482e46155120bad81544832d5415120ba58253482af6454d20ab19153482e76154d20b918553482eb6054d20ab99053482ad6414d20d354c53482ea60d0d20ba583434826f6550d209b195434826e6510d209b59443482ae64d4520ab59351482e96094520abd9151482ac6454520b3d8d51482cc6354520bad81514826e65d05209b597414836451d0520ab986414832c5190520ab582414826f65505209b19541483645110520ba98041482e96010520ab98441483a66110520e9d44414832c5110520e914441483245110520ea98041482ad6010520ea58041482a960105209b997314826d65cc520ab99331482ad64cc520d9147314826f654c5209b19531482af644c520ab19131482eb604c520ba1813148364510c520ba98031482e9600c520ea90750483a841d4120ab987404832c51d0120ead43404826e6590120ab59240482ac6150120cb14540483ab6050120ead41404826e6510120ab99040483a940cc1209b99630482ae648c120ab592304826e650c120ab99030482ad640c120b998430482e5610c120ea50030483c9300c1209b98b540823d65950208f986540823c61550208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f590530826e6214c209d98453082756114c208fd91510823c64544208fd96410823d6590420cb94a410823f65104208f594410832e52104209b596210832e5488420cb552210832e5408420cb550210836651084208f992500823d64940208f597400832e52d00208fd95400832e5250020cb953200832d54c80209bd95200832e5448020cb551200827b6548020da949200833661d5310ce58354c426e62953109b58a54c426f62553109b18954c43366115310ce58054c423e6494f108f59253c426e6294f109b58a53c423f6454f108f19153c426f6254f109b18953c432f54d4b10cb15352c436661d4b10da58352c423e6494b108f59252c423f6454b108f19152c432f5414b10cb15052c43666114b10da58052c432f5290710cb14a41c42b96090710cbd4841c432c5210710ae58041c42f0604c710cbd5221c432c5488710ba58221c432f5408710cb15021c42e96008710cbd4b40c432c52d0310ad98740c432f5250310cb14940c42b46150310f44c730c42f1610c310f48c430c432f54c8310cb15320c42e661c8310cbd5120c432c5448310b918520c426e62d52109b58b548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6414e108f590538426e6214e109b588538423e64d4a108f593528432e5494a10cb552528432e5454a10cb551528423e6414a108f590528432e5290610cb54a418432e5210610cb548418432e5488610cb552218432e5408610cb55
  | 2 => 0x65cc530b6181314c3675108530d9144214c2e960085309b98b540c26d62d50309d987540c27561d50308f596540c23e61950308f185540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d54948309b986520c32e5454830cb551520c26c6154830cd952510c3355494430d994a510c3655294430cdd92510c3346494430d9d8a510c36462944308fd91510c23c64544309bd89510c26c6254430cd951510c3355454430d9949510c3655254430cdd91510c3346454430d9d89510c3646254430dc181510c23f65904308f596410c32e5290430cb54a410c3365190430cd546410c23f65104308f594410c32e5210430cb548410c3365110430cd544410c25d658c430d5546310c355510c4309bd96210c26d6588430cb952210c32d5488430d9946210c36551884309bd94210c26d6508430cb950210c32d5408430d9944210c36551084308f992500c23d64940308f597400c32e52d0030cb54b400c33651d0030cd547400c23f6550030cb949400c32d5250030cd945400c3355150030d5547300c25f654c030d5545300c399404c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59053c832c5450b20cb55042c82af644cb20ab19132c82ae640cb20ab59032c834d530cb208fd9151c823c6454720ab99321c82ad64c8720abd9121c82ac6448720d994421c82e960d5320cb55054c82ce6315320b358c54c82e96015320ba58353c82af6454f20ab19153c82ae6414f20ab59053c834d5314f20ba58053c826f6550f209b19543c826e6510f209b59443c82ae64d4720ab59351c82ce63d4720b358f51c82e960d4720abd9151c82ac6454720ba58051c826e65d07209b59741c832e5190720ab58241c826f65507209b19541c83a66110720cb94441c82ad60107209b99731c826d65cc720ab99331c82ad64cc7209bd9531c826c654c720abd9131c82ac644c720bad8131c82e8604c720ab98740c832e51d0320ab18540c832e5150320ead8140c82ae648c320ab59230c82ae640c320ab59030c82e6610c320b958430c823e61952208f185548823e64d4e208f593538823e6414e208f59053882766114e209d584538823f64546208f191518823f65906208f596418823f65106208f59441882b96010620cb952218832d5488620d9946218832e5408620cb550218832e54c8220cb553208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d09209b195424832c5450920cb550424826e65cc9209b19532482af644c920ab191324834c534c920ab99032482ad640c9208f993514823d64d4520cdd4441483345110520ae580414826e65c8520ab99321482ad64c8520d914621482af6448520ab191214
  | 3 => 0x740ab58b51d02b960d4740abd8951d02ac6254740ae58051d023e65cc7408f59731d02ae62cc740ab58b31d023f654c7408f19531d02af624c740ab18931d02bb604c740ae18131d023e65c87408f59721d032e5188740ab58221d023f65487408f19521d03a66108740cb94421d02ad60087409b986529026c6154a409bd89519026c6254640cb94a419032d5290640cd946419032e5210640cb548419026f65886409b596219026f65086409b59421902e96008640cb94b409032d52d02409b988535026d6214d40c714d43502af6250d40ab18943502ae6210d40ab588435032c52509409b98b515026d62d45408f99741502ae62d0540ab58b41503345190540abd8941502ac6250540d9d4421503645108540ba58021502ae6290140ab58a40502b96094d40abd8953502ac6254d40add8553502b46154d40aed81535031d5314d40ab98853502ad6214d40ae582525029f6354940a718d52502b76154940ad18552502bb6054940cb54852502ba608c940ae582325023f654c9408f195325023e650c9408f59432502ae62d4540ab58b51502b96094540a7d8d515029c6354540abd8951502ac6254540aed81515023e65cc5408f59731502ae62cc540ab58b315033451cc5408fd95315023c654c540abd8931502ac624c540aed8131502b8604c540cd14431502ba600c540ae580315023e65c85408f597215033451c8540ab986215032c5188540ab582215023f65485408f19521503345108540ae98021502b96008540ab98421503a66108540e9d44215032c5108540e914421503245108540ea98021502ad6008540ea58021502a96008540ea88750503a821d41409b986521026c61548409bd89511026c62544408f596411032e5290440cb54a411032e5210440cb548411033651104409bd96211026d6588440cb952211026f65084409b594211032e5408440cb94b401032d52d00408fd95401032e5250040cb549401027b6550040ce951401026f62553309b18954cc26e62153309b58854cc23f6454b308f19152cc23f64547308f19151cc26f62547309b18951cc2d8604c7309b98b548c26d62d52308f986548c23c61552309b988548c26d6215230cb952528c32d5494a309b986528c32e5454a30cb551528c26c6154a308fd91518c23c64546309bd89518c26c62546308fd96418c23d6590630cb94a418c32d52906308fd94418c23d6510630cb948418c32d5210630ae580418c26f65886309b596218c32e5488630cb552218c26f65086309b594218c32e5408630cb550218c2e96008630cb94b408c32d52d0230cb949408c32d52502309bd89544c26c62551309dd85544c27461551309b988544c26d62151308f990524c23d64149308f993514c23d64d45309b98b514c26d62d4530cdd44414c3345110530ae580414c25e
  | 4 => 0xbd89540c66c62550319b988540c66d62150319e980540c67960150318f992530c63d6494c318fd91520c63c645483197d95310c794414c431b6181310c677654c4318f992500c63d64940319b98a500c66d62940318f58254c863f60553218f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f218f99250c863d64943219798f548865d63d52218f993538863d64d4e218f992538863d6494e21cb951428872f5410a21abd9132886ac644ca21d394d32886ae640ca21ab59032886ae64c8621ab593218863e64942218f59250886ce63d5221b358f54886e661d5221cbd5254886e66115221ab99353886ad64d4e21b998753886ae6494e21ab592538874f5394e21b9984538866f6550e219b195438866e6510e219b59443886ad6090621e998441886ad6010621ab99331886ad64cc621abd9131886ac644c621bad8131886e8604c621ab99250886ad6494221cb905508872c4154221ab99050886ad6414221b398c50886cd63142218f583544863e64951219b58a544866f62551218f994544863d60151218f992534863d6494d219b58a534863f6454d218f191534866f6254d219ed8153486786054d218f996414863e6510521cbd52214872c54885218f990504863d64141219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219b596420872c54508219b594420872d54108219b59632086af644c821ab191320866d650c821ab99032086ad640c821d354c32086ae64c8421ab593210866f6548421abd9121086ac64484219dd95210863e64940218f59250086e661d5021cb55054086ce6315021b358c54086e66115021ba98054086e96015021b998753086af6454c21ab19153086ae6414c21ab590530874d5314c21b998453086ea6014c21ba58053086e66190c21b9586430866f6550c219b195430866e6510c219b594430876661944219b59741086ae6190421cb94641087a65190421ab582410866f6550421ab98441087a66110421cb94441087a65110421ab580410866d65cc421ab99331086ad64cc421e9106310866f654c421abd9131086ac644c421e910531086eb604c421ba18131087c5310c421ab99250086ad6494021cb905500872c4154021ab99050086ad6414021b398c50086cd63140219bd8953d026c6254f40abd8943d02ac6250f40c754c43d02ae6210f40ab58843d032d5210b409bd8951d026c6254740ab98b41d02ad62d0740abd8941d02ac6250740cd94441d02b960d4f40abd8953d02ac6254f40c754c53d02ae6214f40ab58853d02b96014f40ae58352d029e6314b40a758c52d032d5214b40ae58052d023f654cb408f19532d023e650cb408f59432d029e63d4740a758f51d02ae62d4
  | 5 => 0x51cca3e64943328f59250cca7a60152329e580548cb2c5450a328fd91518ca3c64546328f992508ca3d64942328f987544ca3d60d51328f992544ca6f62551328f994544cb2d62151328f984544ca3d60151329b996424cb2c54909329b195424cb2c5450932cb153324ca3e64d45328f593514ca3e64141328f590504ca3d65950328f986540ca3d6095032cb189540ca3c61550328fd81540ca3e64150329b988540ca6d65d0832cb553420ca6d6510832cb550420cb2d548c83297d95320ca6f654c832ab191320cb2d544c8328fd91510ca3c64544328f992500ca3d64940329b58252d066f6054b419b98a50d066d62943419b98a539066d6294e41c794d43906af6250e41ab18943906ae6210e41ab588439072e5250a41ab98b41906ad62d06419b98a509066d6294241ab98b53906ad62d4e41ad987539071f5394e41ab98a53906ad6294e41ad984539069e63d4a41a758f52906b661d4a41cbd4a52906b66114a418fd95329063c654ca418f994329063d650ca41ab98a50906ad6294241a798c509069d6314241ab98850906ad62142419b583525066d6014941cbd4a415072c52905419b988505066d62141419bd89531066c6254c41abd8943106ac6250c41c754c43106ae6210c41ab588431072d5210841ab98b41106ad62d04418fd9541106af6250441ab189411067765504419b98a501066d6294041ad98753106af6254c41ab189531071d5314c41ab98853106ad6214c41ad98453106ba6014c41ae58053106b661d4841a798c521069d6314841cb54852106b66114841ae98052106b96014841ad98732106b561cc8418fd95321063c654c8418f994321063d650c841cd98651106ae6294041ab58a501069e6314041a758c50106ae6214041ab588501066e62d53319b58b54cc63d60953318fd8154cc66e62153319b58854cc72e5494b31cb55252cc66d6094b31cb95152cc72d5454b319bd8152cc72e5290731cb54a41cc72e5210731cb54841cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c66e62952319b58a548c63e6494a318f592528c63e64942318f592508c66e62942319b58a508c63d60d51318f992544c66e62951319b58a544c67a60951319e582544c66f62551319b189544c67b60551319e181544c63e65151318f580544c72f54d4931cb153524c66d60d4931cbd50524c72c54149319b580524c63e6590531cbd4a414c72c52905318f994414c72f5210531cb148414c73b54d4131ce153504c76b52d4131da14b504c73b64d4131ce193504c76b62d4131da18b504c73a41d4131ce107504c63e64141318f590504c66e62141319b588504c73b5414131ce150504c76b5214131da148504c73a6414131ce590504c76a6214131da588504c73a4114131ce104504c75a31141319
  | 6 => 0xda0028f60d39c720c8a1856a71862286043005a1d9e5121a890000000001f22789c820b18487e03e9d514312727d8698850520f68000002080088001c900000000000025c8428000000000fd0000001e48338002560000001160790ab8002489448b409117b98f0cc2818d812ba4003c1cf8978db87f9a880012a12507b0000708f2299a9b0001700000002828750000108001100ba8438a38788d20f7a6f800068012000001004000090030260000080202e060000040000000f802002004088000020400080c0000000180a00200000029000000008010060000480000c0000300c00000003804002060060080040040180001e0040100500a00002001002000008010180800080e0260040000601a00c0100102e01007000026000010000a00000100600002c000240040240800c02c04c0e80f0000100280700e00001800000000000050060300000b00000000000000014038000000300101603001c0280103200c1000700a018010060020740100000c01c00007010000048160060080000504a00c0000100000004009006008080010160000200900404406001012000050060040000080000800400805000030000000020080280c01a0080500200202c0180d060054000000000100000408c0100b008000024000000040000981b00e000038010000000780f0320340000001e000010000040000080e00c0340100e00e00000002020004058020020000981f0000080000900000c190010040080001100601c0500100800000007000004038020020000902c00c0240000200600000000004030008050000000400000a0800400000c010048020020040000100400000007006008028070100780082b0020000080100401802037000000000000000040e003000004020000000000e80700a014010010060040080102401c0100401c00001800002010058080440000680301a00800001000004028000080340100001a0000001c00607c0200001400001809000008008060020140001002e0000080100000804005002018000020000000380900a004000000020300700102c0000400102203c018000000466f62547439b18951d0e6e62943439b58a50d0e6f62546439b1895190e6e62942439b58a5090e6e61d49439b5835250f2e43149439b9845250e6d60149439b98b5150e6d62d45439b9885050e6d62141438fd954310eac6250c4397d954310e6e61948439b5825210f2f4354843cb50d5210e6c61548439bd815210e6f62544439b1895110e6e62940439b58a5010eac6250f42ab5884390a3e65d0d42ab1894350a3d6590c42ab5884310aad64908428fd954210a6f6550842abd954210b2f6550842ab18d4210b2d5350842ab1854210aaf6050842cb50a5110b2d42540429d98754cca7561d5332cbd5042cca3f64547328f191
  | 7 => 0x100000000003292c0001da80005c1a78848ea08106f80000003f2070fda5117600003d8f400029280300024d04a0000001fe16f86e0451f898026680000028212005e8728000000b20000be00009f80022e82d0000000000000018000000000002710fe8001b113424e8001efa9080a8dc8469371159b516584f03a80000010d8260408a78d312d9679d61b9839177806a239e886920383b2619f29bf25389c86725b2850c3a798308e48241858631ac9171d10e10e98990668f49168b488ba3f1869ce2281f7187a4e083a4c9d387b8269a08171a50fa1510371862838002088001991f580000620fa3000000027aa9a80018380000013f0a41b20000da1e72409d710898c00021b8000000001dd24b9ed9d40c30000bd1a00e62808000000000002380000001a182f80023680021480029690a9a723d0fb94b00011c8001fa01ca5fa878001248000b881fa4188d29498e2251588001be2700000001a68d7a3f8d71b90001c100009c1b1a688000fc0000000001b7800160a389c28a6a531ec0001b297f87688f87315097e98b80002da640b797b13ca4a00000000000000022200007d8778000091db01582b0861029a20a9a4704c8aa8fe1d6900078157846134940a420c7a8d23914f8231759dc93a93386f1080ce9fc8830001bd9749208c894693e85380729411d922a6614890d0001e42092028000000000bc80000021c9790000000c48001750150e21ff8178720100208228000ef0b018325728fa411b62348f0a7c1c694e19482e16d9321e30c828412796e07f229a6e80026599e1fa8d9a2d0afa338000c20bc08c88b0988b381a10996ea3d9cb96d2971a125294207d21d13011b9e38c080004003a1262360001df00005b96417998a00025080005f90180026c00017222000000010c074000139a0306610b9c000000000006c14c8961031bb8168d400021c000000039800051845800129a188571961b311d25e00f0ab00e87394700c26081d9bc80000000000000000014a1bc0762378d89289400000002728001058000002342490e8a0e00000023a0000000000000000fca638001128001fba55016226141a7a2631df9352269c502380000000016f02f0000000968001478a028599125a93e16680008000026d9f38000001460c588e0001bd0440000d00000b500008c1d0800000000232a1904e9ee0299258508640002198ca8000929f31db8d5996a1809b99080023c9958a896100000022b02c17e09e20200000000a0cf22c00000000000000025690c800290152a1a8000080f39e59e98001280188cf80013581b04e00027b91380000004ba450002671e10de00016b255a1e8002a029828e99500008217110f1f423100000012a8880000592289e60001a819200000025a0a300000009385280028880026a936089a779459
  | 8 => 0x288f11eb19a9021f19b5a1b0ea8000002050ff0d10948000a10d51d7919a3b2751fd80022700000000025204aa2323313f8000bb0009ef00003c8aca211ed0e527e00014c0f2a1011fa920001929ea9b80d61150138a71558be800000036a2e00018d8000000002988001d180025911b1888000198001d5a75a8718b15300006104d90399c9f610b1e08002041a2a790051dea2b9809411570079fc14386d9970c513b00000007c8a280009f18d29a15503822909800400fa0110080025da62a2400020aa501c08000b281f2600829379aa00000000024b08900000018f8000000b08000001aa87a0ad96880020614980000389b10425e80b8001841450ba18800b25780016c8000000000000001940000000002730001c382e98700018900020193b9b411923094b93313c2612761b39b70808ed85a95d9268251520531638001dd84c15b9ba17190115a2258cc9978bb8099998002150db07016b9cd0b980002491a923121047a5c18c80200000005591e21685a15d00014d2709518578001c18d09429709178efa4480000016500001321280021e1079180002738000000001c78000002769e011ea8b9f481107190528820495c0cb8ce10607e9739731221681b0a0c1ac10710684d07727b2831ca8930cda2aa3aa3c088a7fa218360f31f002802ba931982679c9a4809da4c10e81813081e1582170c10001900649ae00480028d81d1f505d8a800026d2498000000448481538320000318941bb1f68e6a428a48e40b68540f02990291ff2541e690900006299b05029586b8f500008586e8f999b9a393d0000900000000001cf0e180028683497a8ec00026f0a080018e9e223580019d8cb1cc0b316906b0001290711118310000970000000758000000258950d28000000000000002580000a600017c80000013280011c0688000daa6200026b00ca650000000d180000029c8001188001c611f0af0341ba8ee15905e12fa59a9b97f15b06508d9e18140b1a2ca9501a8e7a2d80d83fa138331310ee9a31dc24a9540d4a910e925d2462078c28ad17d02a800000212090a7d20a0cd1f78faa6b923a8c28982a29da248f89120001d00f59eba1fa1f1c48001d31ad8f712e0001d90000000de80003d00028c80004180e08e80011499f06a8ed21798195c8001ec88f20d0001a9a2a02186583ba9c0000002588000001ee9d48001048799f980015019c0c41e91f100018a9d200018105d00019e976a2f96293884fa3b8000878e39cd93686399a1cc81b9fea06a80297961a0e9ab8001d280003e0c627f0191829d80b723e91100005800016711300000017416496a1108d92468bd86d07c0002001a90bf0001de21429e2132548000358eb0e00871c20eb9aea680c98ac1b6800000000000000000000000239949245a3e20d8920fb05b211a7800
  | 9 => 0x12f00020b8aa2748001770000e58000000001788000b917d8ae1d980002c86186000000029e881848a3198512414d9380001af0dd09a8ae8118c1a111bf80015fa2f1442691e28002742810000b585ca058002720001ea04100000017c0000001ad1a42228548001b4800067a8a9cea5ba0f00015a80002700021a15e8000002918f925f16600020096980015484b12d29f0149e7a648e803510e1c88221a495e1729d88609fb0a90000b614f000000296269a6e1780000000c6a8a24f01c0840c012b0dc0d6a278998749820df80013a0000000000f80000001938e70550dd8001e80420278510e28000b10000b80001c58470c91318000001a629f800156a3516c0000001ab1620000000e31af8bf95f1600868000ca03880023219186ca158378000001c421602100029380015980021080000d0f189194a9cb012a43895a8f0a219d24402012e8ff80000026a1ca16309e93d9c303027e8002519480491a580024da9d06a28b049a8485985888a0000e098997a0000ec9560df11412c96a8001b01f080009a10fa7700000011a0000a5a3710a05628e13922088a8a51bea0985f09d2431b88c707a9989931f927c81e9fd26c80000019fa4f9f824794e800
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x58027c9a24225e14a26840502e061a2aae3a6ca828d400001826844a000000523476884eb2d2000e86ccb0a400ac62007e5600c2c89c300000da3264c0d636008a00926e0000b400ca4c00c4005a0096007a000c80a000be90bc74b800544604de008e66b6dc0000387800000000009e0098ba606a001e08723caa00ce00c68c0094d82c1c00423e16705c48d00a4482201210a601000100010c050309081a030701000c0127060a0015021500000202040302010000090108a48e2a14a22152b705095010a9338ea8216654a5c05450a32858ecaa2641960e531894390687396a729c83439cf5294a41c1aa6b108620ca671d895310706a9ac4298838654d6014c41c1ac6a90a420e2952580521061cb80ca99083a4104604c431a1ce7aa08510e0c6494d328868739ea92a443439d35394e21a1ae62a28410d29701514208706b22a619043835516315021c52a8b00a810ca671d915308706b22a6298439254d6014c218d2e032a8610ea04118131086e038262188434a5c04154021c1aa6b1087a060d5358853d0306b1aa429681491c55210640c18a631286a0660515802150286392a629a81451c55314d40952e1310a6a050c73548525029238aa4292810d1c5650c940952e1316a2a04a97098b3150313310a398a818c1456008540e40a330042a062451580215039028ac010a81a8d456008540c50a2b0042a06a051580215031028ac010a81491c55210630c52a4b00831852471550218c314aa2c010c61c4545404c030a1ae62a2859060d6454c32c8306aa2c62a641835915314f20a48e2aa0431050c73550424829238aa82124183190534c920c60a2b00829050c73550544829238aa82a2412a5c26414d20a18e8a98a6905447154c534823238aca21a412a5c264d4520cc0a2b00829072051980414831228ac020a41c81456010520d46a2b00829062851580414835028ac020a41881456010520952e13266290626641473148312308a2a0241a8585400c120d82c2980609062b5258041c4315aa2c010e218914861503109a2ed18861886245418520c430a298c2a0221891486150110c48a830a40886445318520442943aa80902218a1954048110e10a6a0240885a071501204435030a80902218654d6010410c52a4b008208525751042104312b288210821c154c4108410b42e02084208629545802104324a9ac010821a81056008410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xe8000c0494040886010a218098851cc540a20815496010630a20815516008630a218099051cc520d00531c54048110e00531854048110c21655c04108410d01535c04108410a21851056008410e01531056008410
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => packedAt s5K6 (864+((h/16+packedAt s5K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (31188+((h/339+packedAt s5K5 (27459+(h % 339)*11) 11) % 1221)*11) 11
  | 4 => packedAt s5K4 (56038+((h/448+packedAt s5K4 (51110+(h % 448)*11) 11) % 1776)*12) 12
  | 3 => packedAt s5K3 (5784+((h/37+packedAt s5K3 (5488+(h % 37)*8) 8) % 148)*8) 8
  | 2 => packedAt s5K2 (612+((h/3+packedAt s5K2 (600+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ff83fffffff03fe1ff83fc3fffffd8e31ff
  | 1 => 0xffffffc0fe0ffffc1fe0fffffc1c0ffe73fe4f
  | 2 => 0xff81ffff000fc3ffe000ffc3ffe00f0383cf8c
  | 3 => 0x1fffffff003ffffff0003fffff003fc0ff0
  | 4 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2904888824822100a4092a2441252948861095
  | 1 => 0x421811064814802c0a205049840842b030e64a
  | 2 => 0x852da2921da9275561189ea2eb40ac1b834b8c
  | 3 => 0x1651442491018a9a535204033292c023580d60
  | 4 => 0x18618738e1ce33e39d9ce730230308c3efb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88eec8ea88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36713
namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c180027fd5007fe54027f55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05fe43017f50c05fc43027fd4803fe52027f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32017f4c803fc32027fd4409fe51027f54409fc5101ffd0401fe41007f50407fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc21027fd4009fe50027f54009fc5001ffd0001fe40007f50007fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200eff59510075faca8803bfc65440097e32a200edf19510024f8ca88003ff64440017fb222000efd91100057ec888037fe64440077f3222000ff59110005fac888037fc64440077e3222000ef1911001d78c88803bff544401bff2a2200eff5511006ff8a888033ff63440197fb1a2000f7d8d10005bec688033fe63440057f31a200cff58d10065fac688033fc63440057e31a200cf718d10015b8c688033ff5344019bfa9a200cff94d10067faa6880337d5344019fe29a200cffd0d10067fc8688033fd4344019fe21a2000ffd8910005fec488003ef624400177b12200bff9891000dfcc488003fd62440017eb12200bff1891000df8c488003ec624400376312200effd491005ffca48803bfd5244017fe292200dffd091005ffc8488003fd4244017fe212200cffcc91005ffc6488033fd3244017fe192200effd4510077fca28803bfd514401dfe28a200dffd0510007fc8288003fd414401bfe20a200cffcc510067fc6288033f63144019fe98a200cfd4c510067f8628802fff2144001ff10a2000ff4851005ff8428803bff504400bff282200eff5411002ff8a088037ff404400bff2022000ff5011002ff88088033ff304400bff182200cff4c11002ff8608802fff204400bff1022000ff4811002ff84088003ff1044001fd8822005ff8411002fec2088017ff650400b7fb282005ff99410025fcca080177e65040093f3282005ff5941004dfaca080177d65040013eb282005ff1941002df8ca08017ff640400b7fb202005ff9901001dfcc808017be64040075f3202005ff59010005fac808017bd64040015eb202005ff1901002df8c808027ff5404011ff2a02009ff55010047f8a808017ff630400b7fb182005ff98c10015fcc608017de63040056f3182005ff58c1003dfac608017dd63040016eb182005ff18c1002df8c60801fff530400fbfa982007ff94c1003ffaa60801f7d530400ffe2982007ffd0c1003ffc860801ffd430400ffe2182005ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd62040017eb102005fb58810005dac408017fc620400b7e3102009ffd4810037fca408027fd520400dfe2902008ffd0810037fc8408003fd420400dfe2102007ffcc810037fc640801ffd320400dfe190200abf9841004ffea208027fe5104013fea882009ff14410047fe8208003fe4104001fea082008ff1041003ffe620801ffe310400ffe9882007ff0c410037fe4208003fe2104001fe9082006ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802000fe44010
  | 1 => 0xbfe314802dfe98a4016ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024018ffd412002ffca090063fd504800bfe2824017ffd012002ffc8090003fd404800bfe2024016ffcc12002ffc609005bfd304800bfe1824001ffc812000ff64090017fe204800bf71024005ff0812002fd84090007f8204802bffb2e2015bfd97100affccb88012fe65c402bfeb2e2015bf597100aff8cb88012fc65c4001ffb262000bfd93100a7fcc98800efe64c4001feb262000bf593100a7f8c98800efc64c402bffaa62014ff953100affaa988053fc54c4015ffb1e200abfd8f10057fcc78800afe63c4015feb1e200abf58f10057f8c78800afc63c4015ffa9e200adfd4f10057fca78802bfd53c4015bea9e200aff14f10057fe878802bfe43c4015fea1e200aff10f10007fec588002ff62c4027ff3162001bf98b10007fac588002fd62c4027fe3162001bf18b100affea58804ffe52c402bfea962013ff14b100a7fe858804ffe42c4001fea162013ff10b10057fe658804ffe32c4015fe9962013ff0cb100affea388057fe51c402bfea8e2015ff147100a7fe8388003fe41c4001fea0e2014ff10710057fe638802bfe31c4015fb18e200aff4c710057ea638802bfc31c4027ff90e2000ff88710007fa438804ffc21c402bffa862005ff943100affaa188017fc50c4029ffa062005ff90310007fa8188017fc40c4015ff9862005ff8c310057fa6188017fc30c4027ff9062005ff88310007fa4188017fc20c400bffb2c2005bfd961002ffccb08012fe658400bfeb2c2012bf5961002ff8cb08016fc658400bffb242005bfd921002ffcc90800efe648400bfeb242000bf5921002ff8c908016fc6484025ffaa42011ff95210097faa908047fc548400bffb1c2005bfd8e1002ffcc70800afe638400bfeb1c2010bf58e1002ff8c708016fc6384021ffa9c2010dfd4e10087fca708043fd5384021bea9c2010ff14e10087fe8708043fe4384021fea1c2010ff10e1002ffec508016ff628400bff3142001bf98a1002ffac508002fd628400bfe3142005bf18a10097fea50803ffe5284025fea94200fff14a1008ffe850803ffe4284001fea14200fff10a10087fe650803ffe3284021fe994200fff0ca10065fac30804bff5184025ff28c2012ff54610097f8a308047ff4184001ff20c2000ff5061008ff88308043ff3184021ff18c2010ff4c610087f8630803fff2184001ff10c2000ff4861007ff84308016fe608400bffa842005ff9421002ffaa108017fc508400bffa042005ff9021002ffa8108017fc408400bff9842005ff8c21002ffa6108017fc308400bff9042005ff8821002ffa4108017fc208400bff8842005fdc4210007f6210803bff654401d7fb2a2000dfd9510004feca8803bfe65440097f3
  | 2 => 0x4001ffe84a000fbf4250007ff2128003ff509400077a84a000ffc425003bff992801cff8c9400effa64a0073fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf185400f7fea2a007bfe515003dfea8a801eff1454001ffe82a000fbf4150007ff20a8003ff505400077a82a000ffc415003bff98a801dff8c5400effa62a0077fc3150039ff90a8000ff88540007fa42a0073fc21500077fb02801effd414002ffca0a007bfd505000bfe2828003ffd014001ff680a0017fe405000bdf2028005ff1014002f7880a000ff8405003bff9828005ff8c1400effa60a0017fc3050039ff9028005ff0814002ffecb10016ff658800bff32c4004bf9962002ffacb1006efd658800bfe32c4005bf1962002ffec910016ff648800bff3244003bf9922002ffac910002fd648800bfe3244005bf192200dffea91006bfe5488037feaa4401aff1522002ffec710016ff638800bff31c4002bf98e2002ffac710066fd638800bfe31c4005bf18e200cffea7100677f5388033ff29c4019ff54e200cefaa710067fc5388033ffa1c4019ff90e200cffa8710067fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944005ffd862002ffcc310002fe618800bfeb0c4000bf5862002ff8c31006fff5188037ff28c401bff546200dff8a31006bff4188001ff20c4000ff506200d7f88310067ff3188033ff18c4019ff4c6200cff86310007ff2188003ff10c4000fb8862000ffa4310007fc2188003f610c4005bf9822002ffea110017fe508800bfea844005ff1422002ffe8110017fe408800bfea044005ff1022002ffe6110017fe308800bfe9844005ff0c22002ffe4110017ef2088003fd9044005ff0822002ff04110063ff65480317fb2a4000dfd9520004feca90063fe65480097f32a4018ff595200c5faca90063fc65480097e32a4018df19520024f8ca90003ff64480017fb224017ff9912001dfcc890003fd64480017eb224017ff1912001df8c890063ff544802fff2a24018ff551200bff8a89005bff634802d7fb1a4016ff98d20015fcc69005bfd634802d7eb1a4016ff18d20015f8c69005bff534802dbfa9a4016ff94d200b7faa69005b7d534802dfe29a4016ffd0d200b7fc869005bfd434802dfe21a4005bfd892000ffea490063ef5248003ff2924001ff5492000ff8a490007ec5248003ffa124001ff9092000fdc8490007fd4248001f6a124001ff1092000ffe6490007fe3248003f71924001ff4c9200b7da6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf185200c7fea290063fe5148031fea8a4018ff145200bffe8290003fe4148001fea0a4017ff105200b7fe629005
  | 3 => 0xeb2a4224bf59521127f8ca90812fc6548401ffb224200bfd912111ffcc89080efe6448401feb224200bf5912111ff8c89080efc6448449ffaa24223ff95121127faa89088ffc5448445ffb1a4222bfd8d21117fcc69080afe6348445feb1a4222bf58d21117f8c69080afc6348445ffa9a4222dfd4d21117fca69088bfd5348445bea9a4222ff14d21117fe869088bfe4348445fea1a4222ff10d2100dfec490807ff5248403ff2924201ff5492100ff8a490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148449ffa8a4224ff94521127faa290893fc5148447ffa0a4200ff90521007fa829088ffc4148445ff98a4222ff8c521117fa629088bfc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc604840b7e3024224ffd4121127fca090893fd5048449fe2824223ffd012111ff8809088bff3048445ff1824222ff4c121117f86090807ff2048403f79024201ff0812102ffecb20016ff659000bff32c8004bf9964002ffacb20086fd659000bfe32c8005bf1964001dfac92000fff5490007ff2a48003ff5524001ff8a920017ff639000b7fb1c8005ff98e40015fcc720017fd63900417eb1c8005ff18e4002df8c720083ff5390041bfa9c8020ff94e40107faa7200837d5390041fe29c8003ffd0e4001ffc872000ffd4390007fe21c8005ffd8a4002ffcc520006fe629000bfeb148000bf58a4002ff8c520016fc6290043ffa94801fff94a4010ffaa52007ffc5290007ffa148003ff90a4001ffa852000ffc4290041ff994801fff8ca40107fa652007ffc329000bffb0c8005ff98640005fcc320017fd61900017eb0c8005ff1864010ffea320087fe5190043fea8c8021ff1464001ffe832000ffe4190001df20c8003ff5064001ff8832000fbc4190041ff98c8020ff8c640107fa6320083fc319003fff90c8000ff88640007fa432007ffc219000b7f3048005ffd424002ffca120017fd509000bfe2848005ffd024002f7e812000ffb409000bfe2048005fe1024002ffe6120017fe309000bfe9848005ff0c24002ffe4120017fc209003dffb2a801ebfd95400f7fccaa0012fe655003dfeb2a801ebf595400f7f8caa0012fc655000b7fb228003ffd51400f77ea8a000ffe5450007feaa28003ff1514001f78a8a0077ff635003b7fb1a801dff98d40015fcc6a0077fd635003b7eb1a801dff18d40015f8c6a0077ff535003bbfa9a801dff94d400effaa6a00777d535003bfe29a8003ffd0d4001f7e86a000ffe4350007fea1a801def50d4001ff886a0003ff62500017fb12801cff9894000dfcc4a0003fd6250039fe3128001bf189400f7fea4a0073fe525003dfea92801cff149
  | 4 => 0x8b7fd519045bfe28c8203ffd064101f7e832080ff74190407fe20c8203fd10641167fe63208b3fe3190459fe98c822cff0c64115ffe43208affc2190401ffb048200ff9824102dfcc120803fd60904017eb048200ff1824116ffea1208b7fe509045bfea84822dff1424101ffe812080ffc4090407de204822cffcc241167fc61208b3fd3090459fe184822bffc824115ff841208abff65504557fb2a822aff99541025fccaa08abfd65504557eb2a822aff19541025f8caa080eff6450407ffaa28203ff9514101ffaa8a080ffc5450453ffb1a8229bfd8d4114ffcc6a080afe6350453feb1a8229bf58d4114ff8c6a080afc6350453ffa9a8229dfd4d4114ffca6a08a7fd5350453bea9a8229ff14d4101ffe86a080ffe4350407fea1a8203ff10d41007fec4a0802ff6250451ff3128201bf98941007fac4a08a3fc62504037e312822affd4941147fca4a08abfd5250451fe2928203ffd094101ffc84a080ffd4250407fe2128229ffcc941147fc64a08a7fd3250451fe1928203bfd8541157fea2a08abfe5150455fea8a822aff1454101ffe82a080ff74150407ff20a8200ef9054101ff882a080fbc4150407fa20a8229ffcc54114ffc62a08a7fd3150453fe18a8228ffc8541147f842a0803ff60504017fb028200ff98141007fac0a0803fc605040b7e302822affd4141157fca0a08abfd5050455fe2828203ffd014101f7e80a080ffc4050453ff9828229ff8c14114ffa60a08a7fc3050451ff9028228ff0814113ffecb1089eff658844fff32c4204bf9962113efccb108127e658844ffeb2c4227bf59621006facb108027d658844ffe32c4204bf19621007fec910802ff648844dff3244203bf99221007fac910802fd648844dfe3244203bf1922113ffea91089bfe548844ffeaa44226ff1522112ffec710896ff638844bff31c4202bf98e2112ffac710896fd638844bfe31c4202bf18e2112ffea7108977f538844bff29c4225ff54e2112efaa710897fc538844bffa1c4225ff90e2112ffa8710897fc43884037eb144201ffd4a2113fdea510807fe5288403fea944201ff14a2100fd8a510807ff4288403ff2144201fb90a2100ffa8510803ed4288403fe2144201ffcca2100ffc6510807ee3288403fe9944225fb4ca2100ff86510806fe618844fffa8c4227ff9462113ffaa31089ffc518844dffa0c4200ff90621007fa831089bfc418844bff98c4225ff8c62112ffa6310897fc3188403ff90c4201fbc862100fee4310807fc2188403fa10c4200ffd8221007fcc110816fe6088401feb044200bf58221007f8c11089fff508844fff2844227ff5422113ff8a11089bff408844dfe2044225ffcc22112ffc6110897fd308844bfe1844201ffc822100ff84110807ec2088449ffb2a4224bfd9521127fcca90812fe6548449f
  | 5 => 0x1e004000000010260080c80402202c0d8080020140200e000000008030060000400c006004040140020000200202203c00803000000000120240200000004200c0100002a00006009000000000440480080b80100e004040010000080002b03a0040301f05400c0180000001c040060000180580001a0040e03800804c000010001400000300400003004002014030080140040001a04a004010330000a80483f05e0380100200c0080000101408403802002078028470080340000200a03802800010000038050140040380d00404c0381806202405000028048048020020000800000200c0c02700e0140802102a030000000060001280100402000815000014008020100000000200e084000070100200700f0000080380000201401803036030098000060040100017ffecaa10beff6550801bfb2a84009fd954217ffccaa1012fe655085ffeb2a842fbf5954217ff8caa1012fc655085fbe32a84049f1954200dfec8a100fff5450807ff2a28403ef9514201ffaa8a10bfbd5450807fe2a2842effd8d42175fec6a10bbfe63508057f31a842eff58d42175fac6a10bbfc63508057e31a842effd4d42176fea6a10bbfe535085dfea9a842edf54d42177f8a6a100fff4350807dfa1a8403ff90d4201ffa86a10bbbd4350807fe21a8401bfd894200ffea4a1007fe5250803fea928401ff1494200ffe84a100fef4250803ff2128401ef9094200ff884a1007bc4250803f62128401eb1094200ffe64a1007fe3250803f71928401ff4c942177da64a1007fc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8400bf1854217ffea2a10bffe515085ffea8a842fff1454201ffe82a100ffc4150807de20a842effcc542177fc62a10bbfd315085dfe18a8401ffc854200ff842a1007ec2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028405bf1814217ffea0a10bffe505085ffea82842fff1414201ffe80a100fbf4050807fe202842effcc142177fc60a10bbfd305085dfe1828401ffc814200fde40a1007fc205085bffb2c822dbfd964116ffccb20812fe659045bfeb2c822dbf5964116ff8cb20812fc65904077eb248203ffd524116f7ea92080ffe5490407feaa48203ff1524101f78a9208b3ff63904597fb1c822cff98e41015fcc7208b3fd63904597eb1c822cff18e41015f8c7208b3ff5390459bfa9c822cff94e41167faa7208b37d5390459fe29c8203ffd0e4101f7e872080ffe4390407fea1c822cef50e4101ff88720803ff6290457ff3148201bf98a41007fac520802fd6290457fe3148201bf18a4116ffea5208affe529045bfea94822bff14a4101ffe852080fbf4290407ff2148203ff50a410077a852080ffc4290459ff994822bff8ca41167fa65208affc32904077f30c822dffd464116ffca320
  | 6 => 0xe03400015930e2d11bb20c4402b90002b02f92eb0000000002f300006f0003661971770002924750001be0703950004d60004280c00ed3be2540d00c51704832653db47d3301390922ec37500248727622246828734d3d13073d504b20328f00045810707134e4d304c0472aa0de1ad00000040a06339813140d39b0000000724351c10002b52674963834ed1bc0812281d228203205906440e4ba3332251db3722f731828e30c41413a0fa1912362a63960000f13a73150c40a724b3b02141e944b0e00000e50ce1eb3f300030b3fc04100033f1992230b94d84910000002b223c3ab2911491d63f12dc3013b11e30a602448c01936f1941322d72a43192da2a820422c1d812d09b0550780d54770380b008901c4a80a92e43bf1ed01e3b843c0000562731841f13770370f326c0002640002551c43cd0fc1ec2443d812f4de0003c63ad44d18d1b40ec0004be07b0000790000004b40000002e93114520001dd23e4631551ea48935c00045c25200000014d0692b810c23a4ad0003940003b20ac3373054180001c006a4983f50903fe0001b81404660003494aa2a005f2ea39a2fe0e931204521f2be1ba13f0001094c70600002972950261581211c63920f74481870030004734d11061ee0004692270000003232e62ff3fb19a1c521b09314f17233100047e0832214000d14822c300022d00046f10842c28a1484614db4e842b02309641533d1f90bb2802e33e80eb11e18b3650d709e12a0910cb1fd4394cd0000000000a40000001680004c500000000010b3172d44094e12c146b1bf0161e100141b1451c23d90100e14413084c948a11f15230f41d1630313714314514ac47f1653b63c80420c639c34033e2f617d0f426e44529d4e444a0482290ee3294324780e63020b72420e414748d00042d2ce1351823100003430000001fa19331a47900034c2ad45e16439904a3520a20c94ee17a46440b12e4a51372bb0004a70000000001fe00000003300030a1b642e2901b04672fc0000002261aa00019611b17631b005000000010140000241c8000020000583505000413000022000000010260040081004a000000010000000f8060120000b8040020200080100000000023018000030070000000a000004000000040020a4010110000e402008002004158000140c8078010100300001e0000000100900e000180000000340581a01a000090380000900580b00002400806000000028000000000201200e02c0d01700003401056004000008010060340e80c0000500c0060020180a00101009c0a805002048068010120280c01e000018038340380280e80600a0000080300002c008000100040b80500801400800004024008050000000300c00a0180000002e0b00100a00403000009028010010031000180180002603801801000000000
  | 7 => 0x4051434194b745b2b73c73912af00029620235b20605834f0a348f2ca00000008e25a15406e00028b35506d25338a10120727c4b021e4a931c2003dd05d3ef0f200044e3003cb4021462132f202a1041b114405e42139e3ff0ff1d336a43800042013e31d25f00a10d35e4040001ae4d911301840f00004606b35d1b90003a80274010003d32d625c00036c0002ef1a715b3063840511922bf35106c0003933c52e74843df1f01d04160293603e737f42f49403b49e30324f4302153a546a0432a92ee05222041703c27f0c100c12228644718925138b20e2b10ad4e013043b07419d15e21800002c0002c938e07e0001c81a40004b31b24e21cc37c1111e23e223504414e24330426d2f11614a43dc16f1c332e4972d532115c28325b1693a13340153880be2d33b70d913b00000000f00039d1340000070051ca11c22a44420b2c643d21a00000018e23200032642617e2742cd4491df1361034371a640839f37e0fd0000004c23740f81331cd1e03b40ca4eb23108a0fb0571cf4932a525648131311a2984994e604f1c926f4a64070823d645a25d07620d3a42402ac0500004c80000004e329f18c1710003b50002f53a224802f3631af4df44f16d0304361a92340001f72ae4341a01a108d3812414bf4463eb2c03850002f445745438f49f4724b137b2c20d43c20dc17838908421c36949000021629a1601560000bf0cf4d01530000001ef0001052104a34a03392084564b81411204853282bd07d0003790004af4da0003c40000001fb1950210000c836e0dd0f615a00046e1281d400006700000009d4b21d50004594b60002e02501023a918546c0530000000683092371f849225729c3d74bb3760544d54703aa3c32304cc4b90112930a51d13af33b07a49a0980f50b632a09a0000c308703543e0cd23841c0df43343a12b0991144ca0362493252581da4ce06507303f4d734b3a603d49504923d36724c0ef40303e1bd3971fc17c1743e34ec06648e04011d1100001624860000000af26907c3ee0b30e348031e38d13c0081233e93ea3ed2e802b3534134dd0c245d2241ab4122a209c22e2b43de29e0ae1262cf01a1253220b42f03481733351dc31f35919b15f00014b34500045f00035f0002d800000900b0000000004c32c80004e72bc3bc07f1e526a0853f436411200036d2120da0003470000771510ab1182790004bc3ba4c105b00041136127000036b38705c00041032401f3da3560003a30000001ce3d017900000037000016c00000024634a0c724d2dd19c2590003f91b51881b300017f00000022b00035742a00028c3fd27b0004a10000000003e52c53f71a23363d41a502218309f24a23318111732732b08c3382e24062724550a028932001348840c21d22f37d30d0000252e500041a3bd26802002e3cc0000002df16
  | 8 => 0x4c000016749c0b11d70a84530000000001de38610e35a3902782f800000009517b10f2fd00047b08b0882171e40004b53f80000004710393b30003ac00026600026200015000021100044c3c914a03a1420d600008f0003680003b91e623f3502393f60000aa0000000000000002470004cf0001e74ae00011600045018f0003bb2452e100027d1d937300000019010032d00035418a0003ec0000000000000004dc0000001f300043f0173ae0003421c72600001980000002de4ab3fa1380040000004cb00033c15700000023b28d33a0b53e138c16b16a2810004e90000000000f026346032f49b1f546d0bd4420970003c04c41290003622711242a10000002852b300029b00e41f1cb41e00027e1a34742940612ed0000001e848b3f00001154e53460004290002cb25e15d3a03ce0620000000004760000f909400010a0d20004d22192ab3e420a0002091f40d805a0e74430000282752fa2cc37831646501b0cc46220147a13d2050060123440004d40003580bc0004230000860002d03ca2d94ef2d20001270ea0000801ff0002a712c00014c0002fb0e81f61a82ba4c62db0b21860a147c3e64244220d33c10752993322c41ac0db3d23412613f238026b2b649d2c70b818020f19f2881f24bd3e04250e24270fe4a217501d01404d19e2a34ea37a0ba24e00d3143821b728427a11916602d32c27704e3cf
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe5258810006ed5258810036ec5258810006ef4258810036ee4258810036ec4258810006ef3258810036ee3258810006ed3258810036ec325881000cff715881000cfd7158810034fc7158810036ec215881002cff705881002cfe705881002cfd705881002cfc705881002eee205881002eec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810036ef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef4158810006ec4158810006ef3158810006ee3158810006ed3158810006ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002eee505881002eed505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002eee105881002eed105881002eec1058810004ff765081002cfe7650810004fd765081002cfc76508100057f755081004d7c755081017e7e65508100067d655081001ebe6450810006bd6450810176de6350810006dd635081000eee6250810006ed6250810037ac4250810005f77150810005f471508100a4ff769041002cfe769041001cfd769041002cfc769041016e7e65904100067d659041001ebe6490410006bd6490410166de6390410006dd639041015eee6290410006ed629041002dfa7090410005f970904100a4ff76504101567e65504100067d655041001ebe6450410006bd645041014ede6350410006dd6350410146ee6250410006ed625041009cff768841002cfe768841000cfd768841002cfc768841004d7e75884100057d758841013e7e65884100067d6588410136be6488410006bd648841012ede6388410006dd638841000eee6288410006ed628841002dfa7088410005f9708841009cff76484101267e65484100067d654841011ebe6448410006bd6448410116de6348410006dd634841000eee6248410006ed624841002dfb7644010006fb7644010004fb76440100077b754401018778754401002f7a654401002f796544010007bb7444010007b8744401002fba644401002fb96444010007db7344010197d8734401002fda634401002fd963440101977b5344010197795344010007eb7244010007e8724401002fea624401002fe9624401002dfb714401002ff3714401018efa614401002ff26144010187f25144010187f15144010
  | 1 => 0x941002e7d105941002e7c1059410004ff7559010024fe7559010004fd7559010024fc755901002ebf7459010006bf5459010046be5459010006bd5459010046bc5459010004ff7359010014fe7359010004fd7359010014fc73590100067f53590100067d5359010046bf4359010006be4359010006bd4359010046bc4359010004ff725901000cfe725901000cfc7259010046bf4259010006be4259010046bc425901001cff715901001cfd7159010044fc7159010046bc415901002cff705901002cfe705901002cfd705901002cfc705901002ebe405901002ebc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010046bf7159010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006be3159010006bd3159010006bc3159010006bf2159010006bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002ebe505901002ebd505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002ebe105901002ebd105901002ebc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dc4258c1003edf7158c10006de7158c1003edd7158c1003edc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006dc4158c10006df2158c10006dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002ede5058c1002edd5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ed71058c1002ede1058c1002edd1058c1002ed51058c1002edc1058c10004ff7558810024fe7558810004fd7558810024fc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810004fd7358810014fc73588100067f53588100067d535881002eef7258810006ef5258810036e
  | 2 => 0x7e531189101afe610189101afe41018910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100757c75509100067f655091017e7c6550910006bf645091001ebc6450910006df6350910176dc6350910006ef625091000eec625091005fac425091008cfe76905100067f659051016e7c6590510006bf649051001ebc6490510006df6390510166dc6390510006ef629051015eec629051002cfc76505100067f65505101567c6550510006bf645051001ebc6450510006df635051014edc6350510006ef6250510146ec6250510005fb705051002df8705051007cfe76885100757e75885100057d75885100067f658851013e7c6588510006bf6488510136bc6488510006df638851012edc6388510006ef628851000eec628851002cfc76485100067f65485101267c6548510006bf644851011ebc6448510006df6348510116dc6348510006ef624851000eec6248510005fb704851002df8704851001cff765011006cfd765011001cfc76501100067f65501100f67c6550110006bf645011001ebc6450110006df63501100eedc6350110006ef62501100e6ec6250110005f77150110005f4715011000cff764811005cfd764811000cfc76481100057f75481100757c75481100067f65481100c67c6548110006bf64481100bebc6448110006df63481100b6dc6348110006ef624811000eec6248110005f77148110005f471481100067f65c41100ae7c65c4110006bf64c41100a6bc64c4110006df63c4110056dc63c4110006ef62c411009eec62c411002df671c411002ef761c411002dfa76c411002efa76c411002cfa76c41100077b65c41101a77865c4110007bb64c4110007b864c4110007db63c411019fd863c411019f7b53c411019f7953c4110007eb62c4110007e862c411002dfa71c411002efb61c411002ff361c411019ff231c411019ff131c41100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067c42594100067f32594100067e32594100067d32594100067c325941004e7f71594100067e715941004e7d715941004e7c71594100067f41594100067c41594100067f31594100067e31594100067d31594100067c31594100067f21594100067c215941002e7f705941002e7e705941002e7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e7e105
  | 3 => 0xe71d891002cfd71d891000cfc71d891005eef21d891002cfe70d891005cfd70d891002cfc70d891005eef20d891005dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d8910007e631d8910007e531d89101b7e610d89101b7e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d89101b6ef71d891005eee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ec41d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d89101b6ee70d8910006ed70d89101b6ec70d8910006ef50d89101b6ee50d8910006ed50d89101b6ec50d8910006ef40d89101b6ee40d89101b6ec40d8910006ef30d89101b6ee30d8910006ed30d89101b6ec30d89101b6ee10d89101b6ec10d89100057f75589100757c75589100067f65589100067c6558910005bf745891006dbc7458910006bf6458910006bc6458910005df7358910065dc7358910006df6358910006dc635891005eec6258910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc73589100067f53589100067d535891005cff7258910006ef725891007cff7158910006f7715891009cff7058910006fb7058910005ee761891005eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d53189101aeef6118910007e63118910
  | 4 => 0x9110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c755911006cff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110004fd7359110014fc7359110006dc7359110014dc73591100067f53591100067d5359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec725911008cff7159110006f771591100a4ff7059110006fb7059110005be761911006ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d5319110006be6219110006bc62191101c6bf6119110007b63119110007b531191101c7b610191101c7b41019110065de76d8d10066de76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d101bfd771d8d10067d471d8d101bfd610d8d101bfd410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d101bedf71d8d10066de71d8d10066dd71d8d10066dc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d101bede70d8d10066dd70d8d101bedc70d8d10006df50d8d101bede50d8d10006dd50d8d101bedc50d8d10006df40d8d101bede40d8d101bedc40d8d10006df20d8d101bede20d8d101bedc20d8d101bede10d8d10066dd10d8d101bedc10d8d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d891005eee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006ef52d891005eee52d8910006ed52d891005eec52d8910006ef42d891005eee42d891005eec42d8910006ef32d891005eee32d8910006ed32d891005eec32d891000cf
  | 5 => 0x67f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95101d67f71d95100767e71d95100767d71d95100767c71d95100067f41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067c21d95100067f70d95101d67e70d95100767d70d95101d67c70d95100067f40d95101d67e40d95101d67c40d95100067f30d95101d67e30d95100067d30d95101d67c30d95100067f20d95101d67e20d95101d67c20d95101d67e10d95100767d10d95101d67c10d951001cfe76d91100067f65d91100067c65d911006ebe64d9110006dc63d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110006bf54d911006ebe54d9110006bd54d911006ebc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d911006ebf43d9110006be43d9110006bd43d911006ebc43d911000cfe72d9110004fd72d911000cfc72d911006ebf42d9110006be42d911006ebc42d911001cfe71d911002cfd71d911001cfc71d911006ebf41d911002cfe70d911006cfd70d911002cfc70d911006ebf40d911006dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110006be62d9110006bc62d9110007b631d9110007b531d91101cfb610d91101cfb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101cebf71d911006ebe71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d91101cebe70d9110006bd70d91101cebc70d9110006bf50d91101cebe50d9110006bd50d91101cebc50d9110006bf30d91101cebe30d9110006bd30d91101cebc30d9110006bf20d91101cebe20d91101cebc20d91101cebe10d91101cebc10d91100057f75591100757c75591100067f65591100067c655911006ebc6459110005df7359110065dc7359110006dc6359110005ef725911005dec725
  | 6 => 0xc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b100067f5358b100067d5358b10006ef7258b1002cfc7158b1009eec2158b1009eef2058b10004ff7650b10004fe7650b10004fd7650b10004fc7650b100057f7550b100ad7c7550b10006bf6450b1001ebc6450b10006ef6250b1000eec6250b1009fac4250b1002cfd769071001ebe6490710006bd649071002dfa7090710005f97090710044ff7650710006bf645071001ebc645071002cfd76887100ad7e75887100057d758871000eee6288710006ed628871002dfa7088710005f97088710034ff7648710006ef624871000eec624871001cff765031001cfc765031001ebe6450310006bd6450310005f77150310005f4715031000cff764831000cfc76483100057f75483100ad7c754831000eee6248310006ed6248310005f77148310005f47148310004ff7559210024fe7559210004fd7559210024fc755921002ebf7459210006bf545921008ebc5459210004ff7359210014fe7359210004fd7359210014fc73592100067f53592100067d535921008ebf4359210006bd4359210004ff725921000cfe725921000cfc725921008ebf425921008ebf415921002cfc705921002ebe405921002ebc4059210004ff7558a100067f7558a100047f7558a10024fe7558a10004fd7558a10024fc7558a100067c7558a100247c7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a100067f5358a100067d5358a1002eef7258a10006ef5258a1007eec5258a1007eee4258a1007eee3258a10006ed3258a1007eef2158a1002cfc7058a1002eee2058a1002eec2058a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a100057f7550a100957c7550a1001ebe6450a10006bd6450a1000eee6250a10006ed6250a1007fac4250a10005f77150a10005f47150a1006cfd76906101cebf649061001ebc649061001cff765061002cfc765061001ebe6450610006bd6450610005fb705061002df8705061005cfd76886100957e75886100057d75886101b6ef628861000eec628861000cff764861002cfc764861000eee6248610006ed6248610005fb704861002df8704861002df976c4210006f976c42101df7b53c42101df7953c421002ff271c42100757e76d95100767e76d95100247e76d95100067e64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067e62d95100067c62d95100077631d95100077531d95101d77610d95101d77410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d9510
  | 7 => 0x85200bdbc7458520005df73585200b5dc735852009dfb70585200067f65185200067c6518520006f56118520004ff7518520024fe7518520004fd7518520024fc751852001cfe7418520004fd741852001cfc7418520004ff7318520014fe7318520004fd7318520014fc73185200067f53185200067d531852002cfd7218520006ef5218520036ec5218520036ee4218520006ed4218520036ee3218520006ed3218520006f74118520006f44118520006f73118520006f43118520036ef2118520036f62118520036f5211852002cfe701852002cfc70185201aeee20185201aeec2018520004fe7690520004fd7690520004fc76905200067f659052016e7c6590520006bf649052001ebc649052000dee7290520005ed7290520007ad4290520004ff7650520004fe7650520004fc76505200067f65505201567c655052000dee725052002cec76485200c5ee75485200c5ec75485200076f65485201f76c6548520005ef7448520005ed74485201edef73485201eded73485201e76f53485201e76d534852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb704852002dee704852002dec7048520007e8704852000eef604852000feb604852001cff765012000cfe76501200e4fd765012000cfc76501200067f65501200f67c6550120006bf645012001ebc6450120005ef725012000dec7250120007ad42501200a6be64d9310004ff75d9310024fe75d9310004fd75d9310024fc75d93100a4fd74d9310006bf54d93100a6bc54d9310004ff73d9310014fe73d9310004fd73d9310014fc73d93100067f53d93100067d53d93100a6bf43d9310006bd43d931000cfe72d9310004fd72d931000cfc72d93100a6bf42d9310006f671d93100a6bf41d9310006f970d93101cebe40d93101cebc40d931001cff76593100a6bc6459310004ff7559310024fe7559310004fd7559310024fc7559310006bf7459310004ff7359310014fe7359310004fd7359310014fc73593100067f53593100067d5359310004ff725931000cfe725931000cfc725931002cfc71593100a6bc41593100a6bf40593100ad7e75d8b100057d75d8b1009eee62d8b10004ff75d8b10024fe75d8b100067e75d8b100247e75d8b10004fd75d8b100067d75d8b100047d75d8b10024fc75d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10004ff73d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b1009cfd72d8b10006ef52d8b1009eec52d8b1009eee42d8b1009eee32d8b10006ed32d8b10006f671d8b1009eef21d8b10006f970d8b101b6ee20d8b101b6ec20d8b1000cff7658b1009eec6258b10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b1001cf
  | 8 => 0x67d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95202267f21d95202267e21d95202267d21d95202267c21d95202267f70d952021e7e70d95202267d70d952021e7c70d95200067f40d952021e7e40d952021e7c40d95200067f30d952021e7e30d95200067d30d952021e7c30d95202267f20d952021e7e20d95202267d20d952021e7c20d952021e7e10d952021e7c10d952001cfe76d91200067f65d91200067c65d91200bebe64d9120004ff75d9120024fe75d9120004fd75d9120024fc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d9120006be43d91200bebc43d912002cff72d912000cfe72d912002cfd72d912000cfc72d91200febf42d91200febd42d91200feee32d9120006ed32d9120004fe71d9120004fd71d91200bebc41d912000cfd70d91200bebf40d91200057f75591200c57c75591200067f65591200067c65591200bebc6459120005df73591200b5dc7359120005f77159120005f47159120215fb7059120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c75591200fcff7459120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc73591200067f53591200067d53591200bebf4359120006bd43591200e4ff7259120006ef72591200e6ee3259120006ed3259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f47159120214ff7059120006fb705912002dec765092001eec765092002cec76509200076f75509200c5ee75509200c5ec755092020f6c75509200c56c75509200076f655092020f6c655092000def745092000faf7450920007af645092001eee645092001eec64509200bfac645092001eac64509200bfae545092020fad5450920205ef7350920205ed73509201feef63509201feed63509201ff6f53509201ff6d53509200bfaf43509201ffad4350920005ef71509200bfac4150920007eb705092002dee705092002dec7050920007e8705092000eef605092000feb60509200bfaf40509200067f65d85200067c65d8520004ff75d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d852002cfd72d8520006f741d8520006f441d8520006f731d8520006f431d852007ef621d852007ef521d85200c57e75985200057d75985200067f65985200067c6598520006f7619852005df970985200057f75585200c57c75585200067f65585200067c6558520005bf745
  | 9 => 0xe75885400057d758854001dbe7488540005bd7488540006ef628854000eec6288540007ad4288540004ff7648540004fe7648540004fc764854001dbe7448540005bd7448540004ff7559220024fe7559220004fd7559220024fc755922002ebf7459220006bf54592200d6bc5459220004ff7359220014fe7359220004fd7359220014fc73592200067f53592200067d53592200d6bf4359220006bd43592200e6bf42592200e6bd4259220004ff7159220004fc71592200d6bf41592200e6ec215922002cfe705922002cfc705922002ebe405922002ebc405922002eef205922002eed2059220004ff7598620024fe7598620004fd7598620024fc759862001cfe7498620004fd749862001cfc7498620004ff7398620014fe7398620004fd7398620014fc73986200067f53986200067d539862002ef67198620006f63198620006f5319862009ef6219862009ef5219862002cfe709862002ef6109862002ef41098620004ff7558620024fe7558620004fd7558620024fc7558620004ff7458620006bf7458620004bf745862001cfe745862001cfc7458620006bc745862001cbc7458620004ff7358620014fe7358620004fd7358620014fc73586200067f53586200067d535862002ef77158620006f63158620006f5315862005ef6215862005ef5215862005eec215862002cfc705862002eef205862002eed205862002ef6105862002ef41058620004ff769062002cfe7690620004fd76906201cebf649062001ebc6490620004ff7650620004fd765062002cfc765062001ebe6450620006bd6450620005ef725062000dec725062023f6e75886200076d758862013eee65886201b6ec65886201b6ef6488620006ed64886201b6ef6388620236ed63886202376f53886202376d538862000dee718862000fe671886201b7e66188620006ed61886201b7e561886201b7ea70886201b5ed7088620007e9708862000eee608862000fea608862022d7e76d95200c67e76d95200247e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95202276e72d95200c76d72d95202276e42d95202276e32d95200076d32d95202276f21d95202277b20d952021f6e20d952021f6c20d95202277820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952021e7f72d95202267e72d95202266e72d95202267d72d95200c66d72d95202267c72d95202267f42d95202267e42d95202267d42d95202267c42d95202267f32d95202267e32d95202267d32d95202267c32d95200067f71d95200067e71d9520
  | 10 => 0x64001fb671906401cfb66190640006bd61906401cfb561906401cfba70906401cdbd7090640007b9709064001ebe609064001fba6090640004ff768864002cfe7688640004fd768864010d7e75886400057d758864000eec6288640004ff7648640004fd764864002cfc7648640005bf744864001dbc744864000eee6248640006ed624864000cfe76d89400e6ee62d8940004ff75d8940024fe75d8940004fd75d8940024fc75d894002cfd74d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d89400d6bf43d8940006bd43d89400e6ee42d89400d6ed42d8940004fe71d8940004fd71d89400e6ec21d894001cfd70d89400e6ef20d89400057f75589400f57c7558940005df73589400eddc73589400e6ec6258940005f77158940005f4715894026dfb705894002dbc765094000ebc765094002cbc76509400073f75509400f5be75509400f5bc75509402673c75509400f53c7550940266bf6550940266bd655094025dbf735094025dbd7350940256bf6350940256bd63509402573f53509402573d535094001dbf725094001faf7250940007af625094000ebe625094000ebc62509400e7ac625094000eac62509400e7ae3250940257ad3250940005bf71509400e7ac2150940007bb705094002dbe705094002dbc7050940007b8705094001ebf605094001fbb60509400e7af2050940004ff75d8540024fe75d8540004fd75d8540024fc75d854002cfd74d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854000cfe72d8540004fd72d854000cfc72d854008ef641d854008ef541d8540006f721d8540006f421d8540006f7619854006df970985400057f75585400f57c7558540005df73585400eddc7358540005ef72585400e5ec72585400a5fb70585400f57e75185400057d7518540006f56118540004ff7518540024fe75185400067e75185400247e7518540004fd75185400067d75185400047d7518540024fc751854002cfd7418540006bf5418540046bc5418540004ff7318540014fe7318540004fd7318540014fc73185400067f53185400067d5318540046bf4318540006bd431854000cfe7218540004fd721854000cfc7218540046bf4218540006bd4218540046bf4118540046f64118540046f54118540006f72118540006f421185401c6be40185401c6bc401854002cbc76505400f5be75505400f5bc755054024dbf735054024dbd73505402473f53505402473d5350540005bf725054001dbf715054001fb77150540007b76150540006bc6150540007b46150540007bb705054002dbe705054002dbc7050540007b8705054001ebf605054001fbb6050540004fe7688540004fd7688540004fc76885400f57
  | 11 => 0x15eec21d912102cfe70d9121004fd70d912111ebc40d912115eef20d91210057f75591211257c755912111ebc6459121295f77159121004ff75591210067f75591210047f7559121024fe7559121004fd7559121024fc75591210067c75591210247c755912115cff7459121006bf7459121004ff7359121014fe7359121004fd7359121014fc73591210067f53591210067d5359121144ff7259121006ef7259121294ff7159121006f7715912111ebc4159121146ec2159121004ff705912102cfc705912111ebf4059121146ef205912128cfe769052101ebe6490521006bd649052101cff765052100cfe7650521144fd765052100cfc7650521006bf645052101ebc6450521005ef725052100dec72505212876e75885210076d758852113eee658852113eec6588521006ef6488521006ed648852127eef638852127eed638852127f6f538852127f6d538852100dee718852100fe6718852100eef618852100fe76188521005ed7088521004ff75d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d812109efa20d8121006fb60981210057f75581211257c7558121005bf745812111dbc7458121005df7358121115dc735812111dbe7418121005bd74181211b6ef621812102efa6018121006f96018121004ff7558a40024fe7558a40004fd7558a40024fc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400067f5358a400067d5358a4002eef7258a40006ef5258a400feec5258a400feee4258a400beed4258a400feee3258a40006ed3258a40004ff7158a40004fc7158a400bebc4158a400feef2158a4002cfe7058a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a40004ff7598640024fe7598640004fd7598640024fc7598640004ff7398640014fe7398640004fd7398640014fc73986400067f53986400067d539864000cfe7298640004fd729864000cfc729864002ef671986400a6f641986400a6f54198640006f63198640006f5319864002cfe709864002ef6109864002ef41098640004ff7558640024fe7558640004fd7558640024fc7558640004ff7358640014fe7358640004fd7358640014fc73586400067f53586400067d5358640004ff7258640006ef7258640004ef725864000cfe725864000cfc7258640006ec725864000cec725864002ef7715864006ef6415864006ef5415864006ebc4158640006f63158640006f5315864002cfc705864002ebf405864002ebd405864002ef6105864002ef4105864016ebe65906401cebc65906401cebf6390640276bd63906402773f53906402773d5390640006bd629064001dbe719
  | 12 => 0xd65d9221136be64d922112dde73d9221005dd73d922128df671d9221004ff75d9221024fe75d92210067e75d92210247e75d9221004fd75d92210067d75d92210047d75d9221024fc75d9221144fd74d9221004ff73d9221014fe73d9221006de73d9221014de73d9221004fd73d9221006dd73d9221004dd73d9221014fc73d92210067f53d92210067d53d9221136bf43d9221006bd43d9221006ed72d922115eee32d9221006ed32d922128cfe71d9221006f671d922102cfe70d9221004fd70d922101cff76592210067e65592210067d6559221136bc6459221004ff7559221024fe7559221004fd7559221024fc7559221006bf7459221004ff7359221014fe7359221004fd7359221014fc73592210067f53592210067d5359221006be4359221136bc4359221146bf4259221146bd4259221146ee3259221006ed325922100cfc7159221136bc4159221004ff705922102cfc7059221136bf4059221135ef7650a2101eef7650a2101cef7650a210076f7550a2113dee7550a2113dec7550a212af6c7550a2113d6c7550a212af6e6550a210076d6550a2100def7450a2100faf7450a2101eee6450a21137ae6450a2101eae6450a21007ad6450a2101eec6450a21137ae5450a212afad5450a212a5ef7350a212a5ed7350a2129eef6350a2129eed6350a2129f6f5350a2129f6d5350a21137af4350a2129fad4350a21005ef7150a21007e77150a21007e47150a2100eee6150a2100fe66150a21137ac4150a211b5ec7050a21137af4050a2100cff769062101cfe769062100cfd769062116e7e65906210067d659062101ebe6490621006bd649062100dee7290621005ed7290621007ad4290621294ff76506211567e65506210067d655062100dee725062113d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067e65582210067d6558221004ff7558221024fe7558221004fd7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221004fd7358221014fc73582210067f53582210067d5358221006ef525822105eec525822105eee4258221006ed425822105eee3258221006ed325822105eef215822105efa20582211b6ec205822113d7e75182210057d75182210067e65182210067d6518221135be7418221005bd741822112dde7318221005dd731822102efa6018221006f9601822101cfe76d912111ebe64d9121004ff75d9121024fe75d9121004fd75d9121024fc75d9121006bf54d912111ebc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d91210067f53d91210067d53d912111ebf43d9121006bd43d912115cff72d912115cfd72d912115ebf42d912115ebd42d912100cfd71d912111ebf41d9121
  | 13 => 0x8241004ff7358241014fe7358241004fd7358241014fc73582410067f53582410067d535824106ebf4358241006bd4358241004ff725824100cfe725824100cfc725824106ebf4258241006bd425824106ebf415824106efa40582411cebc405824116d7e75182410057d7518241165de7318241005dd731824115dee7218241005ed721824102efa6018241006f9601824100cfe76d8941146ee62d8941004ff75d8941024fe75d8941004fd75d8941024fc75d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d8941006ef52d8941146ec52d8941146ee42d8941136ed42d8941146ee32d8941006ed32d894101cfd71d8941136bc41d8941146ef21d894102cfe70d8941004fd70d8941136bf40d8941146ec20d89410057f75589411557c7558941146ec62589412cdf7715894116ebe659054116ebc65905412c6bf63905412c6bd63905412c73f53905412c73d5390541006bf629054101dbe719054101fb6719054101ebf619054101fb76190541005bd7090541004ff75d8141024fe75d8141004fd75d8141024fc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d814100cfe72d8141004fd72d814100cfc72d81410a6fa40d8141006fb60981410057f75581411557c7558141005df735814114ddc7358141005ef7258141145ec72581411cebf6418141145ee7218141005ed721814102efa6018141006f960181412bd7f765962113e7f76596210247f76596210067e64596210067c64596210057f73596210057d73596210067f63596210067e63596210067d63596210067c635962113f6f72596212b76c72596212b76e42596212b76e32596210076d32596212b76f21596212b77721596212b77421596212b76c20596210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596212b67f725962113e6f72596212b67e72596212b67d72596212b67c72596212b66c72596212b67f42596212b67e42596212b67d42596212b67c42596212b67f32596212b67e32596212b67d32596212b67c325962113e7f71596212b67e71596212b67d71596212b67c71596210067f41596210067c41596210067f31596210067e31596210067d31596210067c31596212b67f21596212b67e21596212b67d21596212b67c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067e30596210067d30596210067c30596212b67f20596212b67e20596212b67d20596212b67c205962113d7e75d92210057d75d92210067e65d92210067
  | 14 => 0x14fc73d85420067f53d85420067d53d854201cfd72d85422ceed72d85422cef641d85422cebc41d8542006f631d8542006f531d8542296f621d8542296ec21d854202cfe70d8542004fd70d85422cebf40d8542296ef20d854217d7e75985420057d75985420067f65985420067c6598542175de7398542005dd739854215fac4298542006f761985420057f755854217d7c75585420067f65585420067c6558542147ac42585420067f65185420067c651854228fac4218542006f56118542004ff7518542024fe7518542004fd7518542024fc751854200cfd7418542004ff7318542014fe7318542004fd7318542014fc73185420067f53185420067d53185422eebf4318542006bd431854201cfd721854228eee3218542006ed32185422eef54118542006f63118542006f5311854228ef5211854202cfe7018542004fd701854202cfe76d81420067f65d81420067c65d8142217ac42d8142004ff75d8142024fe75d8142004fd75d8142024fc75d814200cfd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d814226ebf43d8142006bd43d814201cfd72d8142216ee32d8142006ed32d8142004fe71d8142004fd71d814226efa40d8142216fa20d814217d7e75981420057d75981420067f65981420067c65981420ffac4298142006fb60981420057f755814217d7c75581420067f65581420067c6558142005df7358142175dc73581420e7ac4258142005f77158142005f471581420067f65181420067c65181422f7ac421814202efa6018142006f9601814216d7e75d8a410057d75d8a41165de73d8a41005dd73d8a4115eee62d8a412edf671d8a4100cff7658a4115eec6258a41004ff7558a41024fe7558a41004fd7558a41024fc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a410067f5358a410067d5358a4111ebf4358a41006bd4358a4115eee4258a4111eed4258a4101cfc7158a4115eec2158a41004ff7058a4102cfc7058a4115eef2058a4115dbf7650a4100ebf7650a4100cbf7650a410073f7550a4116dbe7550a4116dbc7550a412e73c7550a4116d3c7550a412e6bf6550a412e6bd6550a412ddbf7350a412ddbd7350a412d6bf6350a412d6bd6350a412d73f5350a412d73d5350a4101dbf7250a4101faf7250a4100ebe6250a4115fae6250a4100eae6250a41007ad6250a4100ebc6250a4115fae3250a412d7ad3250a41005bf7150a41007b77150a41007b47150a4101ebe6150a4101fb66150a4115fac2150a411cdbc7050a4115faf2050a41006fb60982410057f755824116d7c7558241004ff75582410067f75582410047f7558241024fe7558241004fd7558241024fc75582410067c75582410247c7558241006bf545824106ebc545
  | 15 => 0xb00500300200000000700401800100000200301200800100900000100000500300000800000800400100400000000100800000000500200000600000000000000000000800700300300600000701100400101000300800b00300300000400600200200001000200000000200100400e00000b00000a00100100400000100100300c00900000d00200000a00101a00700600800000200d01100100001000501500b00000000300600000100300000000400000200200f00200b00500100700301100a00900e02300202000000d00400701a00e00100100000c00600000100100800500100100300000000100000000100000100100601100100000500000100000300000300000100800600100600600200000000500000100100000000700100001800900000600000000100000702401600700100700601a00100501100300000000500e00000000800400100000001900001300000100900000801101000b00100900002a00100200300100c00000100700000500200900600001300500600100000f00100c00000000000600d00000100600600800200100100400700b00100101500200001600100e00000300500400c00600700301000400000500a00900001c00000300000000630d7e76d954217e7e76d95420247e76d95422ff3f74d95422ff3c74d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95423073f43d95420073d43d95423076f42d95422ff3e42d95422ff3c42d95422ff6c42d95422ff2c42d95422ff6e32d95420076d32d95423073c41d95422ff6c21d95423073f40d95422ff6f20d95422fe7f74d95423067e74d95422fe7d74d95422fe7c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d95423067f43d95423067e43d95423067d43d95423067c43d95422fe7f72d95422fe7e72d95422fe7d72d95422fe7c72d95422fe7f42d95422fe7e42d95422fe7d42d95422fe7c42d95422fe7f32d95422fe7e32d95422fe7d32d95422fe7c32d95420067f71d95420067e71d95420067d71d95420067c71d95423067f41d95423067e41d95423067d41d95423067c41d95420067f31d95420067e31d95420067d31d95420067c31d95422fe7f21d95422fe7e21d95422fe7d21d95422fe7c21d95420067f70d95420067e70d95420067d70d95420067c70d95423067f40d95423067e40d95423067d40d95423067c40d95420067f30d95420067e30d95420067d30d95420067c30d95422fe7f20d95422fe7e20d95422fe7d20d95422fe7c20d95420067f65d85420067c65d8542297ac42d8542004ff75d8542024fe75d8542004fd75d8542024fc75d854200cfd74d8542296bd74d8542004ff73d8542014fe73d8542004fd73d8542
  | 16 => 0x2ac9a73c718d480a4c43f7a10cbec61b051a29c00005d4188a6539e0002d1a3682805910000000000000000000113e000000000020c1fa33b00000003390c48534f900003808f400002b742a8e454ac7cd1162810c265c63dd0000b3a1cd054834c1881264a6000000056b43f96c54600001c319c93100004a0842ce287cb02798ad094000000142000097c03e89844a284200025340006f01eb800080e00400300401701600000000500000400800201100000001000000f00000000800900f00100300500000500000200400b01400000a00000101200700100700301300400000000600001000100000300001401400d00700000100101200101100400000a02100100200300100200600000100400000400300000500300100100200100002500701600300b00200200100600100500000900001400001900000000400200700600000000100000500200400000700101000300500c00000000000900300000600100700000100b00300300000000000000800000400100400000f00100400000202400000600a00400000c01900900c00200d00301900100401c00800200100000600e00200100901100000200000600f00600100100000200100300101600f00000200000700d00100100a01a00300000000400400101400000000600300200100000000300a00000100000700001700000100200100600000400800600200202701300100401700300700900600a00800000300801a01600200500600c00500a00100000100200300d00300200303200100000000400000c00500000200400000101101700500000000200001700801601900000900000100100f00000800301900000200200000200401800d00800200c00100701300900500000200c01000100100100200100c00900902500800000000d00300100400100f00100100200400d00000600100600700002300000101300700000000500900f00401000b00200100500100a00300500d00800100b00400000000000400000700100000600401400200000000300d00300200000200300200200300800002206200001600400f00701400000200001201d00200200300700400600100700700100900700c00100100a00000300300000000b00102800100000700500d00200e00b00400000000a00500000800900200000c00500500000900a00000000c00b00800200200300700600000b00301500000700500000700400400400800000500000e00000200100100400300200200000500100100002200300a00400600800001400601200200000200c00300300100901a00300000e00f00b00000100100100000300e00000000100500100c00000100100e00900100000000400100f00700100000500500100100100100200800400500001601600000c00000000202201800000d0
  | 17 => 0xfdce369012f80a7449e44f2b99a704c40000001a1cd845ad37c0000000638404000000000007702406a010e0a70000978000326800000081000028dc0004d500017048fca0500015354623c72a5851807a2ef1fa11a90a25291e99134d1000028795640004214da034031629644e8440b7a7ec48e000114413102400000006fd2ca08b547a84100025e8c0c77944180d86ca1e000001cc0ae0003011b7c0000002a191751585de13380000004520d11c483289523d4a690c4653f46b07746706012f98ff800004500694800000774331554cfe0003e881981629373ed8000eb215948586713b49003120e70000000501081c9c63572b68e10cc65fe40580f800062631d80012a8150000000003e1c20000cc01940000bf800000061515b0000af41fb05610f80000003bd0dac000013000048c0000000001c940001020001e7453c12c12b19900960f90000000fe40002cc000074c0004c0a72000815d2d980013e692a4458f6d2ae000000109800061d35d95a826a01b02d0000c1e0003b5000000038b48b0ee8a00a4e11e1d348d8000182265400059a3940208c6c47a37d86b095a0dc04ba75d3ec92921801a4d5e64a36c107800040f0000524602000000225137404919691e00000000000abcfb200000007f400073221b0000d6234e0b380c81ae7f12ff826800029b11a0000e1e00000021a80002ab4dd805d14203a04e0000aa498a1e213b800018200000000008c400009941da41a4b492b91a60002f78c34000a262f09dfd1108c10000000e7294808388480000000c2a3e024e7261e61e84000000000000141c000149a2405bc3020fb9bacf201fe2119fd4d8c7bf4680bad2640004a51c28ad263c1a200000000000001f58000a3944d1f608e23240000000cba000000000138860a09ca1392766772928ec8bcc2e932c16484082883290dd49167fa28982192b614b05fa010c9e1a40002588bd00000000bf009483b323921142400045d000000076332288fc00090628a159ca3245b000000034257f3bc26606d8523247162462a2a11bb9fec8f265e48d0d68d4c00000012cc36a21a28b88c420097451f005538a67c23685dc1ac08c13f00003a282900f115cfc80000f68a5047a0004390e8d48e0003c4094c91222800026840002d421685cc67e982063a1c0bda17231117f44c88094310aa0b3c510201800143838f5129df8000966468a14c0009c108b91fcf6a6144b68fa80c65e017a8000e8c4872871a88d860002228d500001cb4f691d4a5e48031095e140e44e362a1c4e1638a175014c23070e46683040000f625a99a035c0e14722318b6e18d00003306c25d200026e018655705a80006d23df0d5828800046139f8250d3260022f0e6c0000002938ad0f8a49536b16886560002b18000c6480308d8a8c828a5500021a
  | 18 => 0x18e463ff0001bdc0009b93198ae8fb81a6411885852416000005145c6340053001d10e965206a6800009c32c196e8d4000000008a411e0bb2b08000c5800000027591c600000c80000000002eda09050068f00005a531ea13303a7ac00051e2c38c2420265a40508380000000001b246b60001fd22540009ea1d1034449a0961e6800109618f00000000f67580001dbca645aa095000000014c33690a4ee496f00000000002a700000005ee0002450000bc6641517000145a0000000000000245000080c20a59b09e22600d002d075a3c400069b24b00000000003aa9c30d708890fc0fe53b08ad0d186808766dc49290e4e5836d3a898700004e000000009e6000000046411a99652e00000004f900013dc0f4661000248101a0003f11db930a0003d3a3fc36e8ee377800036016b18500009940a71079ba89285b925da3a8bc851845b8d14826910028216c7c82e200026c400038725109f43ce70651c222872e3e23c492e80002d30f99f753960a42709a602846d5475800057019343b800142a0000000000444a2000008d493c904315033864e1f01da054804064847d94882de7f41630a90c1a8af30ca428a1471d43ea35417432e2de00bca7c0001369e5902a7e814580000008b142e9ad134437b1248b045529b500006b429407f0b420c10fc4fe00012182b69e21768a70e4424b3ea0a9473053d0001c0c0001aa4cf0b40dfc3811b980009e46ba00000004ea3ce25300012c09fc07f162861e00000027b8000000000016c38a4dc205205000039f0c51bb8000214215a17cbce3b83ce14ac116a0105e9d253348b6376175c9548a41239c44a3632000015d518a00039500014b0736511292910c11d04502bc16c0614319cc066677d3cd973404a01c380292c49889221e077875617c30892a50ea2d116fa37532661f0ea8f08e8a00004c804000078617c04100000001f5a5e1044113484128c55489343b1424e62000489902c0007cc51f84e08f84442ad2230cd80001f40cc89ba0003b4a000bd60541b402ac0003483fe00002486cc4a9882409a4100000fd90a05da037000127800000019d03b47f30001c580007641200000792618035a2f82a600615000008cc23e05c273800097f3c5a4c4da600000015910927c124c8000000000419154c772417415a564184a102641a9143e1d24060c8d22e63420120e40828db39487a439e4c9423000000073d4b22794be857c2318000cb69ac3dd89cc10652121624fc50e5cb21c1b10700000295079878ca51000240ca8a00019d9b744b00004e120952f27ff2ba18e906e95630b1dc07f63e34370800a3476708f8c0c80c9c635813d0ee6155140a5604cc5072e61ea0ba226a474a2940009730001be465e00012c8000ab601a4b38000e3280700019410b444200010bc0003bf06a0d4c00000
  | 19 => 0x40b800000021700005b0000195000000099852818d9a292be00005ba1640ea06427f80009b096349580ecb8a298078a5248e03f546f1214ed09433ef000ccca67a5261e1085416134880a833a6f204205c00000001cf27913f08f52c79b3903233c496000052a00034d106cbd869519b8fc40009e33a5000000069212094ccd461a53e79d380002cd00000000001830051b3c00000052a000000000000023d8d6c1bb1009b48f2600000000000000001a58cd833c3880a192b00008913a9800000060329625a93a862709987ac8306664f3a2ed1a472f434a8acf6e27201315300009ef34605110d600048700852d03782daa5ac0486042d7a5c000043a3b118312320000d98ebc00000018b239cbc49d53129f18d9661a3da114070a93d074055c2c835d04012fcea00004e480012aa000000262488e21b2460d24c7c0000d380000000000000000b7000004909e09cc0000001fad0904d03ab8d1800000000000014469b2458238800022e1678d60c208df3c00bc43d00cf0001bf00000000001e5500a1af417a5187da38323b8d70a086ae22416946c64db10106113506ab44c8e411b23510f28000dd025000012812f64c03e1a0d8d4a8653172858a843a5000206000000000024488ec7e600012c916832a49f17e064c9b040f82c000039400000012963e0000000062618c4100788d2c0f42da000052071540994140008f200027985584a52b88760dec000145065c0006e610c1ec0d1245905e18b475c8060001f845b046f1701d8000036e3a2268c7664220d9064800000044b800055a7a000015780001293768878f480f00d89c2409800050e80005805ca0000000fd436f3e383800000000000e307b200000000006188bc0002320eda9210000d58e38000000000042200020b21000529e0334a83037a2b33f382810f20c53829aa85b882149c9a0c9a6244368a96d20e88235383a8bf49360000000dc200000009a4dbc0000ef962ce7692848f80000007d20dd1f4138027a2288770a06000000267084e0004db0578fdc4370ea00000003ec40f12c0a880000000000e2617a37280004e23de0002730b9248847980000007ad00009712228e63881f54b769b73d9115035077139e2004c5247b3968f00c883182869a109b26852b30b5862801145588651027ac0ba20ccd3c47428585ec3dc6d424780000004350908e68b562be1e0977400000033507c4bd25f7000000026c00000015944909990ba800000000008d000000010c0aa000000012e3fb1e145f45d348a9528e680004969e780008ce0001f083f211e072000058800035e05952a269328120f463c09109d84f83ac00b368000000000000008911940000001d3caf200029b16145d084703a135d1922212b627e8ce6922054265cffc28533701c533e25e0000c44a6217e36011
  | 20 => 0x1cd0988574d49cd400042e1359fdd19882738395bc3ec51f0eb882d0a41bf1a5253840a00017c8d80d2e06c00000012847b3209243cd727a650406581ce1b43840000e8209d37a97385980000be98a05920344a780000008263ed127c7a819150c912c5222a241f0164206000000000000000040d0000ff0a3513b94991b04b43a000009be44c06685e53f27610001c80cde5a700c1aa412a4284c18bb00000002d00000f460004169ec54480ad33580000001bc1270000f9c0001d62200f2249a0002968b500004368108ef8a3633f00014423220238bd8a5c06a2bf263400073346000001c42e60bb15c027400000006e49e23d638c1750ca69f147e000146457d0001f7d1d00001618704f8802b2e214c0d5a99215a88bc4fe0cb1d8015401801208b0e7400067050c206c0000000f5203c224268000095c0009f011309d924e1801b122a8db49fe0000cb000000900004a08a68ed000129d4ae58e3eb80c00000003fe8294bf67e515e90200000000000ef8de278f0000720af69cd0000a6910a8ec43a00007864ec3869ab0a8c0a100000009d400032a09d107e92300000009040001cb01e40000001378000752754000000000059f04f80000009753a61ed91844ed1b31f4c4847ae4df160899a5ee1bb1349482000000000054c000000000148443437d211029e2e401393185784550ae000079e1c4000000097c03700007b059430807c2490c7a0000ff80007b0a330000000000000000000025a8a835f800045400000008d8986000000247400020d0000d3000000000000000000000000dc04565881478ff50a800000028bcb2e000000000062e7524c028a08b008951e04448be8bf0f09204dfe5f502f99c43864a11e2a49916451120480000000003c91504de800000000002cc00042780507b8000000000000010806d800091a0001f780007762da2f28b753b84f600000010c800049a0bc0000a3a0001dec95635550d000047425f5031e7c49475b4502828d6e1f54f084ad2044a41a38ea8e9007800024e81aa6421b5185c18c13424180000006a800003e80003cb41410900000004c80f940ce000131847008c0000e70ca49bc8b900026fd4880fc28e89493fe35e40e9ce85901e34ce8e481c600047008c800045c000110d0b000046a0000a92246146800000068634589f09fa6e40001b1c76a0004ca0000d82a112ec0bf40005950000000d1a7213dc233c8d606d06d164c0000aa1dba47803a000000072800095022000000004c74be81bd0bc00544726b874e5bf30f00006fa40432714dcdd237900007c822a1c745488189c4a4509803254a03e106007bc05c0000000c680003210000b9c00026e4f496c000027b00002b911e00012d0cd058a2d908a06e11082552db000024a4cb0001158b522cb189000000080200008740000
  | 21 => 0x9db32f82d0f7c000000000000018e31000011b83b600000010540000001e640003dd00015500001633b301006827ca2c680000c099b1c108282a207c48c177125e0002e190f40005d550695d8c966e344f1b6c05873e34728d077a50c4d69b20b9e8fe09e8d6437c3195078ca079497249702cc86641547e80000000004c70fc8822860274219c9ca0000001e95186039359800030228c110271c98200000000010c2000000133c33638d00000009b400023202e41e419a1f980001d83722df0f540007470198148bf88e111380000004d60000000eac00000017e4c1c1200000fc00008c70911980f544e750a1b9c00063951507913661cc000000000000051398fc0000004fd99f4ee845a000000000054730403d400000040e0b840005df4ae0b4800052d000156000000016118c409c6b20d49e0c7f83d12a885210de64c3e480001029864b6070000023021882786387b933392d8f449a627480d4b328963b29ddc600742320286c4108bd0990d34e6e5862251af40b83e727a957450643234e92a0732933505a62c9de4fc1ba258530e8e541a1708bb27c03821d7c5b600025ea9253ea69447d11241ee8ae2d600003927ed4efa1340005d04c61ead43c4f02f900000000000e300000000000000001022000069000006295a439a72863a34306f8a5c2e22d524900f09a259616719ecf1a0d94c209800005502b1274000030551d91a5356493142089431030e02f0374000a4f00000013fa25d29aa5c464aa4615926bc00060900000000004c200000014006624e88ac04268f000000003b27e948680004720001b88fa400036436500000005801448000b6481611b80008187bc00023dcc0a331185a298f023ad24b80000007173231c793d07f041e000134a679108010c9d654800016044386903cba1f0cea5ae0001b64f288352311b354060000000a7c00021f07d98c016400012d800025e5f100000000000000000cf80000003fca7d0e340ef2ae110499c0c80001af8c240002008144b9047242e1dd800000020014e00004b140913e0000a5900000012ee1412af800000025400014f0f5e947074997084a74b24e803836c9d301f93905048a34a28f681363e6321a3bc57e27926280009a8000000026000000000024c01bc00000021e03e850117a05b45760ff2a79ce000000028e05a8de610f2b9000032034209b81f80003894eca6450702b13812900f046371d097a85fc8b543616841cc64924c0000ed600025b8b1c6be6b500006650583a83cd00000002ae20e05e05fe2b928917580000002b700011e872b0001e1ce86062000039400041d36b8000fc646e00001d80000585299dd4000000000235c2128560001db119675a3ae0000a4800044680013a400000000e10f400011c00000000004de800010e5c004980000000001ca9
  | 22 => 0x183a7b00caa2c0000df011c40e4598058aee9054fb8e3800016210625f88ce2f31f70000e4865113806180005603ae821417c28e1218e4cf7a0f34ef00008403d200000000002fb03800011368b8000107c0002e534116992187e00001458000a4823419640009aa00020384460001e41a851f2a2925c00008325560e9856000002800000000006e200026f00000000001e280000000ad0de8ebc1475290000c5e95e44e00003a000006c13ec972306000124067484517704350745391d88cf4476000000000000034f000169105c0220000000b380000000bc922849c000126ce4e5c700025112ec26c1b393e90f62d7007a50127031f022119400058429d00006a40000000000110008011964000007214300000005401fc297400478c23e88cc7789dd283067ca9c15f33c1954d0016e4ae8c412dc0000001a7c0001fc0c3800074000010a8e90dc049132b000000037e29d982c00056800000013e465723010fc00071f0001a0400000002b03f400010a521876ca6851509f8001412000000000542e1981bfa934000000000246c66a90900024d4f3072e2c612bc000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xace82d05630400159b05a0ac60800297a144158c100052ec2882b182005ada8010563040015b30020ac608002a7a132158c100054ec2642b182005ada8008563040015b30010ac6080023d20573588100162f39aa6b102000c5d7354d620400b1dd0fa92c4080163b21d525881002c7743e84b1020058ee87cc962040014dd0b992c4080029b617325881000726a9e64b1020058ec874c96204001c9aa6992c408002aba10755881000556c20eab102000ace831d5620400159b063aac4080029be1574588100053642ae8b102000ae4815d1620400195ae83a2c4080038bd5254588100053742ce6b102000a6d859cd62040015cf02b9ac408002b9205735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881031d36c2ca6b102000e4f5394d6204001c9f06a9ac408003939cd535881000726b9aa6b102062a6e8514d62040014dd0b21ac4080029b61643588100047743886b1020008ed8710d62040014dd0a21ac4080029b61443588100053742ce2b102000a6d859c56204001ccea328ac4080023be1d51588100347643aa2b102000aaf84545620400155908a8ac408016baa00515881000574c00a2b1020068ee87d0562040011db0fa0ac4080029ba14415881000536c2882b102005aea8010562040015d30020ac40801a3ba1f315881000476c3e62b102000a6e85cc562040014db0b98ac408002aba13315881000556c2662b102000a6e850c562040014db0a18ac408016baa00315881000574c0062b10200487c85dd9420400b17909bb284080163b20b765081000656216eca10200087f855d942040090f90abb284080032b10976508100043ec36eaa102060c3e64dd542040018bcc7baa840817f1b98b75508100043f43acaa10200087c875954204001c5884b2a84080162f21d64508100061fbaac8a102000c3c75591420400355904b22840800317dd563508100062e3aac6a102000e8c4258d420400b1d90eb1284080031bdd56250810006363aac4a102003aac84589420400196ac9b8a84080033558f715081000672b16e2a1020008f5861c542040019aac638a84080032e59170904100043fc32eb1082000c3e645d621040018bcc6bac420815b1b98975884102bc3fc3acb108205687d87596210400187ceab2442080030f5d564884100062f3aac71082000c5d7558e210400b1df0eb1442080031b9d5628841000636baac51082000ce9625c221040018f0ebbb22008003361cf76440100063dc2eec8802000c7885dd9100400197709bb220080032e21376440100066dc1eec8802000cd883dd910040018f6a7bb220080031e54f764401000675c16ec8802000ce882dd910040018f6edbaa20080032eddb74440100065dbb0e88802000cdb76dcd10040019d6edb9220080033add87244010
  | 1 => 0xee93a2ca0818e1f61e73594100062fb9ce6b282068a7b805cd650400b4f100b9aca0800317e0d73594100063dc02e6b282063c78805cd65040c50fd0e39aca080021fa1e43594100043ec3c86b28200087e8710d65040010fb0e21aca080029ba08435941000536c1086b282000a3e841c9650400147b08392ca0800297a0c72594100052ec18e4b28200087e87cc965040010fb0f992ca08003175cf32594100062eb9a64b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282067a79809c565040014dd05a0aca080029b60b41594100043f43882b28200087d8710565040130fd0f98aca080021f61f31594100051f42662b282000a3d84cc565040014dd0598aca080029b60b31594100043f43862b28200087d870c5650400147d0990aca080028f613215941002d3d40042b282000a7980085650400b17d0faa2c8080030fdd7545901002c5e43aa8b2020058be8790d640400147d0b21ac8080028f616435901002c5e43a86b2020058be87909640400187eeb3aac8080028fa1673590100051ec2ce6b202000a3e851cd640400147b0a39ac808002aba08735901000556c10e6b202063a3d8594d6404001c3ea729ac80800387e0d53590103151f428a6b202000a3f855c964040014790ab92c808002ad205725901000656b90e4b2020008be87149640400117b0e292c808002a7a0c52590100054ec18a4b202000a3e85cc9640400147b0b992c8080038754f32590100070ea9a64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000a3e851c5640400147b0a38ac8080038dd4651590100045fc3aa2b2020088bc87545640400155f04a8ac808002ab20951590100445f43e62b2020008bd87cc5640400147d0b98ac8080028f61731590100055741662b202000aad82cc5640400147d0a18ac8080028f614315901002d5d40062b202000ab9800c5640401117d0f90ac8080022f61f215901002d5d40042b202000ab98008564040018beeb3aac60818e9761e7558c103172b884eab182062e55109d563040cd5b700baac608016b62017558c100062fc3aeab182000e5b805d563040c7cb100baac60818f95c417558c1031f2a882eab182062a5e851d563040014bd0bba2c608002976177458c100052f428e8b182000a5d851d1630400159d043a2c608002b36087458c100070faa4a8b182000a5e85dc963040014bb0bb92c608003175d77258c100062ebaae4b182065ad7815c963040015a902b92c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c60800237a1c5258c100046ec38a4b182000a9e84149630400153b08292c608192b66027158c100072ba8ca2b182000a9f84545630400153908a8ac608002b3e095158c1000566412a2b182000
  | 2 => 0xe641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400155d0c320c4880032b9d8641891000717b28c83122000e2c6519062440d5d4c20320c4881aba90406418910006673b6c63122000e4f65d8c6244001c98cbb18c488003a3d93631891000746326c63122000e4f85d8c6244001c990bb18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab61263189100056741cc631220008ef8758c62440014df0ab18c4880029b215631891000557c22c63122000aac8458c62440015cf02b18c4880029ba14631891000536c28c63122000ace8618c624400199cec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c48800393a14631891000726c28c63122000ec58118c62440d3d8c20318c4881a7b1040631891000537436a63122000a6c86d4c62440018dceda98c4880038bd93531891000716326a63122000e4f63d4c6244001c98c7a98c4880029ba19531891000536432a63122000c6e7654c6244001c5ec8a98c4880038b191531891000727b1aa63122000e4c6354c62440015cd0d188c488003a919231189100076231c623122035ae4864c46244001d48c8988c488003b118d31189100243f42eeca12200087d85dd942440051bd07bb284880023760f76509100243f42ceca12200087d859d94244001958853b284880021fe1576509100243e42aeca1220008bf845d942440011bf06bb2848800a3720d765091000477c12eca1220008f7815d942440090f90a3b284880032b10876509100043f436eaa122060c3c64dd542440018b8c7baa848817f1b18b75509100043f43ecaa12200087c87d954244001c5885b2a84880062fa1f64509100061fbaec8a122000c3c75d91424400355d05b22848800317dd763509100062e3aec6a122000e8c42d8d42440071dd0fb1284880031bdd76250910006363aec4a122003aae84d894244073970e1b22828809e1f21975885100061e322eb10a2000c5c635d621440ad8d8c4bac42880021fe1f65885100743ec3ecb10a2000c3e75d92214400187aebb244288003179d763885100062ebaec710a2000c6e75d8a21440018daebb1442880db3a1c3624851000672316e2a022000cb7641c540440019c8c438a80880021fa1b75481100061e326ea9022000c5c63dd520440898d8c5baa40881161fa1f65481102243e43eca9022000c3f75d912044001878ebb22408800317dd763481100062e3aec69022000c6f75d8920440018d8ebb1240880032d19371481100066a31ee29022000cb4641c520440019a8c638a408800339d8871481101d63d3b6cb8822039cba76d931044007974ec32620880df369db63c41101b6753b6c58822001cea7618b104400187
  | 3 => 0x7b122000a6d8590f62440011dd0e21ec4880023b61c43d89100053742887b122000a6d8510f624400155f08b8ec488002ab21171d891036c77c3aa3b1220368ec87547624400155f08a8ec488002ab21151d89101b47743e83b1220008ed87d0762440014dd0a20ec4880029b61441d89101b47743e63b1220008ed87cc762440014dd0b98ec4880029b61731d89100055742663b122000aad84cc762440014dd0a18ec4880029b61431d89100053742ee1b122000a6d85dc362440014dd0ba06c4880029b61740d89100053742e61b122000a6d85cc362440090fd0dbaac4880031b18b75589100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400187ecbba2c4880030f197745891000656316e8b1220008be87d91624400187eebb22c4880030f1d764589100064e39ec8b1220008be87191624400187eea322c4880030f1d464589100064e398c8b1220028de86dcd62440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd6244001998c5b9ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200487e87dd562440010fb07baac4880022fe11755891001c5e422eab1220008df835d562440051b906baac4880023be0975589100043f438eab1220038be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317e1773589100062e42ee6b12200087f855cd62440090f90ab9ac4880022fe11735891001c5e422e6b1220008ef825cd62440011ef02b9ac48800237a1c73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200487c87d4d624400187ee9a9ac4881b30f1d353589100062fb9ea6b122002c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b12206bc3c7454d62440018bee6a9ac48800b171cd535891000637baee4b122000c6c75dc9624400195ee9b92c4880032b1d3725891000667b9ee4b122000ccc73dc96244001968e9b8ac488003351cf7158910006373b6ca3122000a6d83d9462440011db0f328c4880029ba16651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000a6e8619462440018dcec328c4880029b60c6518910006573b6c83122000e2f65d906244001c58cbb20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0
  | 4 => 0x3440014b90ab26c688002b3e0964d8d1000566412c9b1a2000a9e86193634400193cec326c68800387d9464d8d100070e328c9b1a2000e1f751936344001c38ea326c68800297a1662d8d100052ec2cc5b1a2000a9e8498b634400153b09316c68800297a1675d8d100062eba8ebb1a2000a5e871d763440018bd0e3aec68800297a1674d8d100052ec2ce9b1a2000ace829d3634400159b053a6c68800297e1574d8d100052e42ae9b1a2000e1f5495363440018beebb96c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c68800297e1572d8d100052e42ae5b1a2000c5f755cb63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b634400153f08a8ec688002a721151d8d1000567c12a3b1a2000acc82547634400159d05a0ec688002b360b41d8d100052f42883b1a2000a5d85107634400153d0990ec688002a761321d8d101956b40ee1b1a2000a5e85d0363440014bb0ba06c68800317dcd53d89100162e39aa7b1220048ef8754b62440014dd0b996c4880029b61732d891000726a9e65b1220028ef874cb6244001c9aa6996c4880029b60f65d891000557424cbb122000aad84997624400159d0732ec488002b360e65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000536c18cbb122000e2f65d936244001c58cbb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000e4f85d8f6244001c990bb1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec4880029ba1463d891000536c28c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4e8518f6244001c9b0a31ec488003b160463d891000537436a7b122000a6c86d4f62440df8dceda9ec4880038bd9353d891000716326a7b122000e4f63d4f6244001c98c7a9ec4880029ba1953d891000536432a7b12206ec6e7654f6244001c5ec8a9ec4880038b19153d891000727b1aa7b122000e4c6354f6244001d88c718ec4880dab921931d891000557424ebb122000aad849d7624400159d073aec488002b360e75d89100053742ee9b122000a6d85dd3624400195ee93a6c4880038bd5254d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000537428e7b122000a6d851cf62440015cd0239ec4880dab960473d891000727a9ca7b122000e4f8354f6244001c9ee6a9ec488003931cd53d89100053742c8
  | 5 => 0x80031719773591100064e326e6b222000c5f7518d64440018b8ea31ac888003331c8635911000637b2ee4b222000c6c65dc96444001958c9b92c8880033318f72591100243f43eeab22200087d83dd5644400117f08baac88800237e0d75591100146e41aeab2220008ef825d564440031d904baac8880021fa1c75591100061fbaee8b222000c3c75dd164440051bd0fb9ac88800317dd773591100062e3aee6b222000c9f74dcd64440018bf0bb9ac8880031721773591100043fc2ae6b22200487c855cd644400117f08b9ac8880023be09735911000c76412e6b2220008de871cd64440018beea39ac888003171d473591100064fba0e6b22200087e87d4d64440090f90fa9ac88800317dcf53591100162e39ea6b22206fc6c72d4d64440010fd0ea9ac8880021f21d53591100062fb9aa6b222002c5c7354d64440dd8d8e4a9ac8880063ba1f725911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f53dc964440018daa7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b222000c3e76d94644400147b07b28c8880022f61e65191100051f42cca3222000a9e83994644400153b07328c888002aba0a651911000556c14ca32220008bf87594644400153f06b28c888002a720d651911000557c12ca3222000aac82594644400147d0c328c8880030f9d865191100051ec18ca32220008bd8798c644400147d0b318c8880028f616631911000557414c63222000aad8298c644400117f0eb18c8880028fe1563191100051e42ac63222000aaf8258c644400155904b18c8880028fa1463191100051ec28c63222000e1f6518c6444001c38ca318c88800387a1463191100070ec28c63222000e958118c644400147d0da98c8880028f21b53191100061f3b6a63222000e1f63d4c6444001c38c7a98c8880028fa1953191100051e432a63222000c3e7654c6444001c3ec6a98c8880038718d53191100051f42cc43222000a3d85988644400153d07310c888002a760e62191100074a31c623222038ab4864c46444001d28c6988c88800297a1b75d8d100062f3b6ebb1a2000a5e861d763440018bcec3aec688003179db65d8d100046ec3ccbb1a2000a5e85997634400153d0932ec688002a761265d8d1000567414cbb1a2000acd8299763440011bf0eb2ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec68800297a1865d8d100062f3b0cbb1a2000c9e76d936344001c3ecbb26c6880038719764d8d100070fbaec9b1a2000e1c75d9363440011bb0f326c68800297a1664d8d100052ec2cc9b1a2000a9e84993634400159d05326c688002b360a64d8d100046fc3ac9b1a2000a5f855936
  | 6 => 0xd53ac08e7b2a200087e8790f65440010fb0f21eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca880028fa1272d95100051ec24e5b2a2000a5e839cb65440014bb07396ca880021fa1f32d95100043ec3e65b2a2000c5f73ccb65440018bee6996ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880029ba0b41d951000536c1683b2a200087e87107654401d0fb0e20eca880ea1fa1f31d95100043ec3e63b2a2000a3e84cc7654400147b0998eca880029ba0b31d951000536c1663b2a200087e870c7654401d0fb0e18eca88003954c431d95100051f42643b2a2000a3d84c8765440614ed03b86ca880021fa1f40d95100043ec3e81b2a200087e87cc365440010fb0f986ca880030f5d754d91100245fc3aa9b222000a3e8590f644400147b0b21ec88800a2fe1d43d91100051ec1ecbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb222000a9f83597644400153906b2ec888002abe0965d911000556412cbb222000a3d83197644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100070fb28c7b222000e1c6518f6444001c3d0a31ec8880038761463d91100074ac08c7b222000a3e86d4f64440014790da9ec8881b30f9db53d91100070fb1ea7b222000e1c63d4f644400147d0ca9ec8880028f21953d911035e1f3b2a7b222000e1f6354f6444001c38c6a9ec8880028fa1662d91100051ec2cc5b222000a9e8398b644400153b07316c888003a518e31d91101cd5a43263b222000c3d751d7644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400147d0a39ec8880028f61473d91100055b408e7b222039ab5811cf6444001c3ea729ec88800387e0d53d91100051f42ee5b222000a3d85dcb644400195ee5396c8880022fa1c52d91100045ec38a5b222000a9e8314b644400153b06296c8880028fa1732d91100051ec2e65b222000e1d53ccb6444001c3aa6996c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c888002abe0971d911000556412e3b2220708bf8754764440731790ea8ec888002abe0951d911000556412a3b2220398be87cc7644400117b0f98ec8880028fa1731d91100051ec2e63b222000aae82cc7644400155b0598ec8880028fa1431d91100051ec2863b2220398be87c87644400117b0f90ec8880028fe1570d91100051e42ae1b222000a3e85cc3644400147b0b986c8880030f19375591100043f43ecab222000c5c73d9564440018d8e5b2ac8880021fa1c65591100062e398cab222000c6c7219564440018becbb9ac88
  | 7 => 0x5d7354c61480014d90aa10c29000f2b1d1421852000573c0a8430a4000e4d534c861480015cf02990c290002b960b411852000752a108230a4000af180104614800156d09988c290002b960b31185200043fc2aed20a400487c855da414800335f0ea14829000eab2194290520006573b28520a4073b2c8550a41480090fd0bbb282900021f617765052021e363b6ca90a40058ec865d121480312d90aba2429004e3ba1c614852000733b28c290a40059ac87509404800b5590ca1280900072b1d942501203959642a84a024005ba880509404800187aebaa6c98800b179cd53d93100062eb9aa7b2620028bf8750f64c400593ce6a1ec9880022fe11755931000477c12eab2620018ec825d564c40010fb0f3aec5880121fe1d75d8b100043fc1aebb162000c6f825d762c40018d904baec5880121fa1773d8b100043ec2ee7b1620038be84dcf62c400117b09b9ec5880121fe1f53d8b100043ec3ea7b16200087f8754f62c40010fb0ea9ec5880031b5d752d8b1001477c3a65b162002cce734cb62c4001c9aa6996c5880022fe117558b1001c5e422eab1620008ef825d562c40090fd0b3b285880021f6167650b100146f41ceca1620008dd839d942c40010ff0abb285880121f2157650b1000c5f43ec8a162000c3c75d9142c400355d05b22858800e3ba1f6250b10006363aec4a162003aae84d8942c400b17d0fb2283880163ba1f624871002c5f43ea8b242000c3f75d5164840018bee6a9ac90800b171cd535921002c5e43a86b242002c9c7350d64840090fd0fbaac5080021f60f7558a1000637416eab142043c6d82dd562840870fd0e3aac5080021fe157358a100243e42ae6b1420008bf845cd628400717908b9ac5080021fa1f5358a100243e43ea6b14200087e8754d62840010f90ea9ac5080163ba1f5258a1000637baea4b1420058ec874c96284005998e6992c5080039354d3258a100043fc2aeca14200487c855d942840011bf06bb2850800a3720d7650a1002c5e43ac8a142000c3c75591428400355904b2285080163b21d6250a10006363aac4a142003aac8458942840014bd07326ca880029760e64d951000537414c9b2a2000a6d8299365440010fd0db9eca880121fe1f63d95100062eb9ec7b2a200087d8798f654400147d0931eca880028f61263d951000537414c7b2a2000a6d8298f65440010ff0eb1eca880028fe1163d95100051e422c7b2a2000a6f8258f65440014d904b1eca8803a1f61c63d95100062eb98c7b2a2000c5d8718f6544001cab0231eca880028fa1262d95100051ec24c5b2a2000a5e8398b65440014bb07316ca880039518e31d95101d53a43263b2a2000e54634c7654400187ae83a6ca880021f61e73d95100062fc1ae7b2a200087e871cf65440018bae639eca881c69da0473d95101
  | 8 => 0x5b9eca9000317ccb73d95200062e996e7b2a400087d879cf65480018dae4b9eca9000317e0d73d95200043f438e7b2a4000a3e841cf654800147b0839eca90003175cc73d952022537410e7b2a4043a6d821cf65480010fd0f21eca900021f61e43d95200043f43887b2a400087d8710f65480894dd0421eca900029b60843d95200051f426e3b2a4000a3d84dc765480894dd05b8eca9010e9b60b71d952022537410e3b2a4043a6d821c765480894dd05a0eca900029b60b41d95200043f43883b2a400087d8710765480010fd0f98eca900021f61f31d95200051f42663b2a4000a3d84cc765480894dd0598eca900029b60b31d95200043f43863b2a400087d870c765480890fd0fa06ca900021f61f40d95202243f43e61b2a400087d87cc3654800b1db05baec8900039354d32d91200243f42ce3b22400087d859c764480031d904b8ec8900021fa1f65591200062e39ecab22400087e8719564480018b8e632ac89000317d9773591200062e32ee6b224000c7765dc564480018e8cbb8ac8900031dd9471591200063a328e2b224000cb4641c564480090fd0fbaac8900021f60f75591200046fc1aeab2240028dc835d564480011ef02baac8900023d20575591200043f438eab2240028de87dcd64480018beebb9ac890003171d773591200062fc2ee6b224000c5c85dcd64480010ff0ab9ac8900121f21573591200045fc22e6b2240008f7815cd64480011e902b9ac89000237a1c73591200062fba8e6b224000c5c751cd644800193ee839ac8900021fa1f53591200243e43ea6b224000c5f73d4d64480058b8e7a9ac8900021fa1d53591200043e43aa6b224000c5f7354d64480058b8e6a9ac89000a2f21d43591200164e39a86b2240028ec874c96448005998e6992c8900039354d32591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf71591200063ba9ee2b224000c7553dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89000339dc871591200063ba98e2b224000c75531c5644800196e8638ac8900032d50c715912000673190e2b224000ce5321c564480c32dd0fbaa84901831b1db755092030716326eaa12407596e87d9542480878d8edb2a84900038b193655092001d57436c8a1240358ee86dc54248001ad0ebb8284900035add4705092001c5f426ebb0a40008bd84dd7614800156d0998ec2900121fa1b755852021c3e436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac2901d31b5c865185200047bc3ac230a4000ab48458461480015a906b08c2900063b20975185200162f39aa630a4000c
  | 9 => 0x648852113d3642ac910a42018ec865c2214846d9d0c0b8442908022fe1175d812101c5e422ebb0242058ec825d7604846d95ec4ba0c0908023ee1d601812100637baea4b1480058ec874c9629000155f08992c5200039354d3258a4000477c12eb30c80018ec825d6619000b1eb0f18cc3200023be09755864000c76412eab0c80008ef825cd61900031d904b9ac3201bf1b1cb53586400062fb9aa6b0c8002c5c7354d61900dd8d8e4a9ac3200121fa1772586400043ec2ee4b0c80018ee87dc961900018dd0bb92c3200031b617725864000637a9ee4b0c8000c6d53dc9619000195883b92c3200db2bd0372586401b656a06e4b0c80058f4874c5619007117f0eb0c8320002abe0961906400243f42eed10c800087d85dda219000195ee8b12432000317dcd53d89400162e39aa7b1280018bc845c762500019c8c438ac4a01de4fa1f75509402fe1e3b6eaa12805fe2c62dd5425000355d0db1284a00e22fa1b71509400069c3aee0a1280018ee82dd761500011db05baec2a00021fe1572d85400243e42ae5b0a80008f78758461500015c904b08c2a000e2f21175185400243fc3aea30a8000c3f845d4615000187908ba8c2a00021fe0d75185400061fa12ea30a8000c3d75d5061500090fd0bb98c2a00021f61773185400243fc3ea630a800087d87d4c61500010ff0ea98c2a00021f61d53185400051e42a8430a8000c3d755086150003958e4a10c2a0002ade0542185400055ac264230a8000ea54208461500015e300108c2a00522fa1c61505400243f428ed10a800087d851da215000735f0ea1442a0006ab2194288540006573b28510a8076b2c8550a215000b1790cba242a007a4f215744854002c5f43ea8b244000c3f75d5164880018bee6a9ac91000b171cd535922002c5e43a86b24400487e851c564880010fb0a38ac9100022fe11759862001c5e422eb30c40058f5878c6618800117f08baac31000e2f211755862001c5f43ee8b0c4000cac21dd1618807395e41ba2c3100e72b48374586200045fc22e6b0c40038bc845cd618800187ee9a9ac3101b30f1d353586200061fba2a6b0c406bc3c7454d61880018bee6a9ac31000b171cd535862002c7a43a62b0c4000cad64dc9418806b1df0eb0c4310002abe116188620006b4baae110c400087e86dcf65480090ff0fb1eca90003175cf63d95200043ec3cc7b2a400087f8758f654800147f08b1eca900028f21163d95200053bc0ac7b2a4000a748158f65480310fb0e31eca900028fa1063d95200051ec20c7b2a4000c5d7318f65480874d90c996ca9000353dcd32d95200072631a65b2a4044a6e82dd365480874db05ba6ca900030f5d074d952022537410e9b2a4043a6d821d365480894dd05b9eca9010e9b60b73d952000636b96e7b2a4000c6e82dcf65480018db
  | 10 => 0xb2c4200c5f325cd65884018ba64b9acb108021fa1c73596210043f43c86b2c420087d8790d65884010fd0e21acb108021f61c43596212b53741086b2c4200a6d8210d65884ad4dd05a0acb108021fa1c41596212b43ec3882b2c422787e87cc565884010fb0f98acb108028fa1331596210051ec2662b2c4256a6e82cc565884014db0598acb108021fa1c31596212b43ec3862b2c4200a3e849c1658840147b09382cb1095a9ba0a705962100536c14e0b2c4200a6f825c165884ad4d904b82cb108021fa1f40596210043ec3e80b2c4256a6e8210165884014db04202cb108021fa1f30596210043ec3e60b2c420087e870c165884010fb0e182cb108028fa1030596210051ec2060b2c4256a6e820c165884014db04182cb108029da0430596210053ac0860b2c420087d8799764884018bce732ec9108021fe1d65d92210062f39acbb244200c5e655cf64884018bacab9ec91080a37a0f75d92210046ec1eebb24420087d879d764884090ff0ebaec9108021fe0d75d92210243f42ee7b24420087d85dcf64884011bb0f39ec910803179d673d92210062ebace7b2442028df875cf64884018bceab9ec910803175d573d92210062f42ae7b244200c5d855cf64884090ff0fa9ec9108021f61f53d92210162f39ea7b244200c5d73d4f64884010ff0ea9ec9108021f61d53d92210162f39aa7b244200c5d7354f648840517f0ea1ec91080b279cd43d922101477c3a65b244202cce734cb6488401c9aa6996c910803355ce71d92210054f41ee8b2442008be8790d6488401c9aa6992c9108121fa1770592210043ec2ee0b24426196e87dd542884c18deedbaa85109838b9937550a213ccb643acaa144200c6f765954288401c5cc8b2a851080eabe196450a2114476c36e2a144200d6775dc54288401ac8ea38a85108066be1d429062101d57c328520c4201cad7650a41884f16590aa148310802e9e0542906210062fb9aa6b044202c5c7354d60884014d90aa12c11080f2b9d1425822100726a9a64b04420487f865d460884010fb0f328c1108030f9d265182210062f39cca304420087f87594608840187ce8b28c110803179cd65182210061f32ae83044200c3d655d060884018bccab98c1108031759573182210047dc3ac03044200c3d75d5364484058bce6a9ec890803175cd53d91210145fc3a87b22420087f855c364484090f90ab86c8908121fa1f75591210043ec1eeab2242008bf845d564484011df04baac8908021fa1c75591210061e3aee8b22420087f855cd64484090f90ab9ac8908023ee01735912102c7c402e6b22420087e87d4d64484090f90fa9ac8908021fa1d53591210043e43aa6b224200c6c75dc9644840317f0eb2482908b68f215649052100657b26e4a0a4256c6e765d621484adacce2bac429080e3be1d
  | 11 => 0x5080147b08186caa117e9ba0830d954200536c1061b2a8400a76810c365508014eb02186caa11870f5d065d85423be36b90cbb0a84018bd84dd761508071db05baec2a10062f61373d854201c76c16e7b0a846fc3d74d4f61508d98dae5a9ec2a11bb0f5d153d85420162f39aa7b0a8400c5d7354f61508d78dae4a9ec2a100a3de1d31d854200696212eb30a8400c5e73d9661508018bce632cc2a11ff8b10865985420062fb2ae730a8400c5c655ce6150801b1884b9cc2a1003355cf619854200696216eab0a840087e87d9561508010fd0e32ac2a11ff0fdd065585423f637b90cab0a8477c3c7419461508c38d8e4328c2a11f78b10865185420047bc3ac230a8400e4d534c861508051eb0f188c2a10021fe1570185420243e42ae030a84008df835c061508051b906b80c2a11f38b10865d814200726a9a65b02840487e859c760508010fb0b38ec0a100a37a0e71d81420046ec1ce3b028400d2c425d660508f587ae832cc0a11ef1b5c865981420243f436eab02845f87c86dd56050801a5885baac0a10021fa1f65581420062e39ecab02840087e8719560508018b8e632ac0a11eb8b10865581420062fb2ee6b028400c5c65dcd6050801b1885b9ac0a10031dd9771581420063a32ee2b028400da442dc560508018eeca38ac0a10031d1947158142006d2210e2b028477c3e7419460508c387ae8328c0a11871b9c865181423be36b90ca30284008fb8758060508058bce6a9ac520803175cd5358a413bc9f43eeaa14825fc3f76dd542904bfc5cc5baa8520806abe196250a4111c5ec36e2a148200d3775dc54290401a68ea38a85208121fa1f75582410061f426eab048200c3d84dd560904010fb07baac1208030fd0b75582410061fbaea8b04820087f855cd60904090f90ab9ac1208021fa1f53582410243e43ea6b04820087e8754d60904010f90ea9ac1208028f21542582410061fbaa84b048201cae7250960904011f70eb00c1208031b5d752d894101477c3a65b128200aaf844cb6250401c9aa6996c4a080e2f21970905411ce5c302e120a82058bc845d760504011df04baec0a08063b20975d81411ce57b22e430282008fb8758060504010ff0cb9acb108021fa1f63596210051f426c6b2c4200a3d84d8d658844f0fd0f31acb108028fa1263596210051ec24c6b2c4200c5f7398d65884090fd0eb1acb1080317dcd63596210043f438c6b2c4200d4d734c96588401c9cc6992cb108030fdd274596212b537414e8b2c4200a6d829d165884014df04ba2cb1095a9b209745962100637b96e6b2c420087d879cd658840147d0939acb108028f61273596210062fb9ce6b2c4256a6e829cd65884014db0539acb108029be0973596212b536412e6b2c4200c6f725cd65884018bf06b9acb108031be09735962100636412e6
  | 12 => 0x100101600001200300000000000200000200001500001500702401401403400300100300000800b00200100a00000500301e00300d00100500400000900400100400400400501501700200200100000400c00201700400500200900000901b00300200000400700200600302600004200000000204800000000700a00e00500101200000100400301501b00300100200000700000201e01201300002200d00200101400200300800200c00a00000000700100000400500200b00100e00400b00900900a00200401500b00100500000700700400300500000000101202700100800900100300e00001100700900400200200a00200704800b00100500200401a01601300400c00000600c00600000b00d00600001c00800801200500101f02e03900500b00000000505202e00000c00000e00100300600300300000000c00600900303100500000000000a00300600000001600300400200200f00400500301000005b00000500a08a00200000500001600700300300100200501700100100000500000000002d00300000000900800000e01403700000200000000f01000000900400100000500605100e00000702906d00300300e01d00f00000600103f00200000200101b00201201c00300400000600300600206400000400901000000205000000d00e00200c00400700e01c00003a00301501400400000200200e00900501100100e00000000001900900300800a00300901601300602102e01600000000000000000700000300000701300501d00001000001b00500800600400000600000000201000100c00000003300000100e00100b01000000000000100000205001100701000702400102600000001801400000800f00a00800200000200001f00000602200601801300001f0000030043f436e7b2a8400d2c42dcf6550801a5884b9ecaa10121fe1f63d95420062eb9ec7b2a840087d8798f65508014ed0331ecaa10029d60663d95420043fc3ac7b2a842f87d8718f65508018bae631ecaa117e8f21943d95420070e31a87b2a845fb2c8250f65508c14d90c996caa1182cb21132d9542006a7b9a65b2a8400e4c634cb65508018be65b9ecaa1003174cb73d95420043ec3ce7b2a8400c5f835cf65508010fd0e39ecaa11828fa1073d95422fd1ec20e7b2a8400c5d731cf65508bf4dd0439ecaa11829b60873d95423051f426e3b2a845fa3d84dc765508bf4dd05b8ecaa11829b60b71d95420063ab88e3b2a840087e87cc765508010fb0f98ecaa11828fa1331d95420051ec2663b2a845fa6e82cc765508014db0598ecaa10021fa1c31d95420043ec3863b2a8460a3e841c365508bf47b08386caa117e9ba0870d954230536c10e1b2a840087e87cc365508010fb0f986caa10021fa1c30d95420043ec3861b2a8460a3e840c365
  | 13 => 0x6a4644077eb7c4e879c522ac81321480000005700006ac0000008de000aec43e41061cba2334c405b463200034056c000aba42e0de3783e200059000067e342ac00000005921560009600ba84630cc4ed522301e4a20b5e2eaa04a1095825c75c1b8a361aa1ca00007e8ca000492a5e986b6260822277a9e0000ad065a5ac64213816c00000065c1c4000a3427800097a000000d24c9a12a9e60027fed00472d4c87a50a3844c08f483a78891c6828440007c294237c000000690000902bb8a906b0000000664bec06451cc0a31c82c26ab065ec000232b7a306c784e210c3546b220214ac36c088669b49c67f27a60bc720c8292aa3c9e830a58215e21cc46ac42b63c823a11227abc21aeb4667a4369ac8d6d2e6747d4978a7e6ec0806d8732bce1dc010b9a5fa5d88f28b21080d0c8ea9a5ae0d49102742b8a6c85c000000000000d200003500000005362500000004aa8d864a236a980b04566a8a649400c416e66cb1a40a90004e0002680008eed28b1659e5d619e25840400020a2008248961b2a2600075aaded129728aa7c8000b6c05ca220009cccea17e25e2703fcd0a00038a124a605408aeb720003be7a8b4cbee00000096a000d66afe8fa53eb2abc42e247e1c0b8e7e2d42acc2bc0000e0bfad5854cc041eecfcab03b28f00007666f280c0001e814c6560ee31e48a9f215a79612e36600000025a146c848520940420001accd445a9f6b9e704338cf635acee00044c90a000bb600c5421d45d488e0007d8000198b322c8090a4861a8c4854008ac62901a6466758016b0407698a272bea72a9a2862ce60003d60403b640095ea5cc1a45e89095627e2be9e484e5c0d0cab400005898e000c74000d0e3ce294790398d5a0003084840001069b897e7f800000066ed14c16a54a42a76574b481d609ccac50e88ab08bf6324000228adcca2000a28a6e0000000200008860008747ea00063459658c000d3a218452000b2e93e0005320007de5140003523da00018400000000000000000086c6ce000128000bfc39ccaa000a8a744d5c0000004fe83e00071405a0000c600076007058803a000000000aa80fe2e0cecc320001fe1bc00000000000000032ecd8000622000a580840003567be29e000000000d3c1b4ce201100100000800b00207500000500c00000c01000000302100003701404b00c05500500000600000000103a00701a01000200000000000007900601900b00300700600700300700601f00100000100c00700300000602c00400906600000100001000403700000900e00801400406401300900000000200100102902000100100202100100200701b00400200200000000100101800400200a00b00000000201a00100200603600b0040270080040090010000000080020140130180040160000080000010000000040
  | 14 => 0x3323620002e61f83c659c13e8ea2344267823ea31a7fc0d22644783449b28feae232ca8c18e912b681c638899679a2c21143129eaa143ac952c564acc0c00032878c06a1de9eccb81fa5b8baa6868a80e4668490b00aee216c42428af6746a1aa1e0b6c905188506ee1109e243c65e1d02ecc3ca02550a325da454ba01b687e3c209613c688c1c9ce50684a2048641225302ca512944afa5283a092800024830ec68606d2a1743d07bcab296c93c03ed26c7ec8a3b488c8e032686a76acbcb342ae58a8fc9820002400925782ce4b2000000a62cde71a0000e2000c24ae0360d566f00006ae734160d2c9b05042f02a4b660004d27ba0006bca7067c20c54a7fa4dc000526a4e3f40fa5c811841c21062400002c27c000cb2c76000950802000a9c718b429749180000003d88d0000c529dc000000c643306d4d442ee3ba9a08be9142b00000b439a0000d80000005f40002d00000000000003365e4000bf2000be000025600008e76e96e5c494e64c3bc94a47607c000438cdc000000a00756000d5e00000083c000566954aae62cd4a098000394c288e61440005a8980c06920000d1c80699e5e87ce0001ea000658bba26cb76ad40acb1836e0006fe8ac288750000a3e2200004b4014610d1a000772ac26442c4bde7168421a2320bd25106dcaa611a75205474269c784c14a88b980e67c469e33ac2a4b853a4e60007024220006b8b607e035c00002680a9d222c6e41401f01da79ec206a41825985be7cca7a4069fc64ec5a60a470ba8858c4cca00f40609f041e3e67805a4a404c4888b2000000057609e5641f4a0853829c000282310c5482a1a443455ecce1ba8e2000000ace0000305e60003583009242c65a68800c066066a35e0c299220600052e00045003894881868a89243a02a12013a2ac7ec6baa8e9a68a08d48f6bf063e3903fa60c1f6692d3ea5a5941b0740000a2c36a4242fe5ca882b88938b92000d02604b3aca46d008c9f40000004f6000ccc2387c673855a396c3a246b44d4875434c0000002f2000c7a17a0fcb4e4d63ec6c0804012998224d46c8c768462a964c66a273022a6d6c260000a277cd340e8000c800a6000000b0a33e00000000046a0006500dc15c0000000000000008b05fe2625cc89e2960007f6ae4d108e80889ee00000079400000060e0004cc0000000002b41a84b6a380000005621be3f20002f809a00000000085e56e7ca0000000005fc2086e8652cf413018a00045c3f6b5c0001d80004ecaa05ba964000722cd2000a6a96800040e6f860221e7762a0bf82d824e7b2b0e5d00003d25560003b0b248600007629364326168c637200072c8d200085ac7000000000000084057e5a081444863a694cae2fc000000000b780000002aa00003c498304878546bae8f81c2a94a82412bd60225ce4d005
  | 15 => 0x52b5655ccf242ad1646e18c000ad66fa00046c74e4be98caacb1c38c000496b86b4a000186af2acab960009c4a2e0001628dc56ad3800071c3d4500c5e48e84cce0302c860f6cc21e09b6b843c028a5020004f82660005f0b3c4fac38b523f0bccbe60864cab74a44ae82f66c42c031800051e280b5081081ea7864062033c7d6cca11e2e87b09a49da9ba0c80b2b6a00011cc34800b12c2c770000d088b8bac3cab14c1eaa2838ce8b8a0000000006e29707f46de0727f058623c62a9beb54a80d504f4c0041658ebdc0007ae06e812000a0a63800070a4f2cfe9d449e4c200037e000836af8a0e23e000748cba4588984de54e6622763aa34e49aa121026b60ec40c000b40376000bc84ce3a62a247ac502d2bbc4bc94c72e4a037062621a89c966be401ec1224cb7e5de8688bc1fc5a2bca7066e672453408a2a60002ccc101f263006ca864445205608cc2840180ce93a798000000a2a178872ce40f8ba642c0003a839269a486000242048c66000508cb60002faa3ac6c3e01040341165bcaf4000be8bb091a00064800095c52c00092e44ea529c20009949843820000009f8000a563748566a072826e0009aa10000025491e000d220aa0000009de0a4680000000904af04f0000a24614036ae64a46ccbb2c306c60048c818873e89487c7003a45f8c9e368bc0cc815490e7ee6c81366c2000bf40003e400000063c02e8208dac96000000000726bda28e0000000000000000000005b014e6964a200058000066600092c21288482238057a488430b800000001680000005c2000b90678b701640000000063462e40be19229244a4d434807400e078c6e0da41ac5840801c764c88ca6a5073cc6a2267b64027d0aead1e5ead6046800070c90cc984143b83f87aa0006be0000a093282e12629ab1e7dc00057c81c252aa4046be2066cc4b8212cad82f43eebbe6e068e2dc190c2e4c891600044224a7e6cb4180000000000000000000166ad28a68b606248004a464b6e834a841cc99c8764d800a62ecf04eea065e25684ba39ea303fe13483270e7369084aea4a3dc22ec94c7c7b4cb08ceabe9a89d801aa9e37a9ca03248c1ce2b231481ad365845d23e8628adaabc0284eac5ca4cd305aa1e69880ae6124fc9622de214cbeb3674c8c02d64828baab8cd061e0009ae0006fc4b004c1520d6cda10e78642052ac4a73ac220003cc000672636712000bd4260ba408200000036cc4481697695a7e4b30870a720b8d069fea929463645b22865dca7c808774c9c2988b4c189fa17080e386c3e89a7084743aea0c7a43227784e499ab2861810a2a81c8b100ccb5abfe710826b020244464a6afcb94698d4e07a6d26a6000d64194a188c27d26ea14217616a0009c8d32cfa1509bc6767ac7b80007a0418a6665486e6f69d6bd0b3ec604dad548a2cc6
  | 16 => 0x3de6006b4bd8b9cd18a74bb474a5f20007925f67e8d4049c9c01720000000f08ec9909d078e64605268c1587da000cf855850c19a6f40f2a160eab0c2ba78a8284a8050830c6219cd04b641a04e09228485c65542da1e2ca854817cab60001d238ea685720009266848e449453c8a40a819651a244000000930000000000d6200097c05e000cd6b580000440003c4316c4875e0005e0b2c000670a1c000c0eb26b3871eb8c0680009061ec0ca0002d476c5164605eeb227a26da93434a6ca28c5b6c92bc6c0247c59a524000000cc03a232a544aaac727c06aa20e5
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2c00003098c12a896014000028700000d0002e000380000c8069e0120009028082980001900010020c8002040182e8610b73d95420054364c42dcf655080142e9610975985420070310a73196615080142e9610b7558142007031087319560508014a696108715814200709194421c5605080103e9721542582410040fa6375509609040144f965cd325962100513e5d534cb648840584f8754d32d92210051364e85dc9619000103d9721542185400040f261755086150001624955082118540006a850980084615000144e96dcd32d95200051325d534c9644800584c8754d32591200071154d321c56448001624955084118520006a850980104614800144f9754d32d8b100051325d534c962840014a9901087650910
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x40800000300e8664c42dcf655080151052a84c004230a8000a88295426004118520
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
  | 10 => 0x138c
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124b
  | 16 => 0x124c
  | 17 => 0x124d
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138d
  | 21 => 0x138e
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128c
  | 26 => 0x128d
  | 27 => 0x128e
  | 28 => 0xa0b
  | 29 => 0xa0c
  | 30 => 0xa0e
  | 31 => 0x130b
  | 32 => 0x130c
  | 33 => 0x130e
  | 34 => 0xb0c
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140c
  | 38 => 0x140d
  | 39 => 0x140e
  | 40 => 0xb8b
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x148b
  | 44 => 0x148c
  | 45 => 0x148e
  | 46 => 0xd0c
  | 47 => 0xd0e
  | 48 => 0x94056
  | 49 => 0x95394
  | 50 => 0x94054
  | 51 => 0x138954
  | 52 => 0x138956
  | 53 => 0x209
  | 54 => 0x1409
  | 55 => 0x1449
  | 56 => 0x289
  | 57 => 0x1489
  | 58 => 0x14c9
  | 59 => 0x139254
  | 60 => 0xb0994
  | 61 => 0x98b14
  | 62 => 0xb0996
  | 63 => 0xd0994
  | 64 => 0x98d14
  | 65 => 0xd0996
  | 66 => 0x180b
  | 67 => 0x1649
  | 68 => 0x134b
  | 69 => 0x14b
  | 70 => 0x141294
  | 71 => 0x141296
  | 72 => 0xb8a14
  | 73 => 0xa0b94
  | 74 => 0xd0a14
  | 75 => 0xa0d14
  | 76 => 0xd0a16
  | 77 => 0x150d
  | 78 => 0x149314
  | 79 => 0x140b14
  | 80 => 0x140b16
  | 81 => 0x28b
  | 82 => 0x184b
  | 83 => 0xd1414
  | 84 => 0x140d14
  | 85 => 0xd1416
  | 86 => 0xbcb
  | 87 => 0x19cb
  | 88 => 0x148b94
  | 89 => 0x154d
  | 90 => 0xd1494
  | 91 => 0x148d14
  | 92 => 0xd1496
  | 93 => 0x20d
  | 94 => 0x10b
  | 95 => 0x194b
  | 96 => 0x164d
  | 97 => 0x74b
  | 98 => 0x1a49
  | 99 => 0xec9
  | 100 => 0x4954
  | 101 => 0x5554
  | 102 => 0x5994
  | 103 => 0x4956
  | 104 => 0x5696
  | 105 => 0x24211
  | 106 => 0x28211
  | 107 => 0xecd
  | 108 => 0x1a4d
  | 109 => 0x20e
  | 110 => 0xecb
  | 111 => 0x1a4b
  | 112 => 0x28e
  | 113 => 0x95456
  | 114 => 0xa0996
  | 115 => 0x148996
  | 116 => 0x449
  | 117 => 0x98455
  | 118 => 0x140a16
  | 119 => 0x44d
  | 120 => 0x149416
  | 121 => 0x140455
  | 122 => 0x74a13
  | 123 => 0x44995
  | 124 => 0x75813
  | 125 => 0x74293
  | 126 => 0x45415
  | 127 => 0x75493
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1264
  | 6 => 2654
  | 5 => 1716
  | 4 => 27
  | 3 => 3
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (51399+((h/421+packedAt gbK7 (46768+(h % 421)*11) 11) % 1517)*12) 12
  | 6 => packedAt gbK6 (138000+((h/884+packedAt gbK6 (127392+(h % 884)*12) 12) % 3503)*13) 13
  | 5 => packedAt gbK5 (108108+((h/572+packedAt gbK5 (101244+(h % 572)*12) 12) % 2060)*12) 12
  | 4 => packedAt gbK4 (1944+((h/9+packedAt gbK4 (1890+(h % 9)*6) 6) % 50)*6) 6
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe03ff01ffc07fc0fffffffd13f3c7d8e31ff
  | 1 => 0xfffc0ffe07ffffff03c03ffeec8d38e73fe4f
  | 2 => 0xf07fff00007ff83fffc003c030f0e3f383cf8c
  | 3 => 0x7fffffff80003ffffffc003f00fc03fc0ff0
  | 4 => 0x7fffffffffffc0000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x50a005200494424402454a5480130434861095
  | 1 => 0xd02c05620290c99102810ab0648518830e64a
  | 2 => 0x60756b010c4ed22eae802b01b0b0a2d3834b8c
  | 3 => 0x459b29b59008033cd32b0023b00f803580d60
  | 4 => 0x487e3ced9e73e7008600c20c3dfd0003efb000
  | 5 => 0x8e10200e10030403082300303feeff6c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36713
namespace PEqualNP.Outside.L_meta_36713
open PEqualNP.Outside.L_meta_36713.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 112 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96))
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_896 : Interval s5Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_928 : Interval s5Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_992 : Interval s5Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1024 : Interval s5Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1088 : Interval s5Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1120 : Interval s5Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1184 : Interval s5Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1216 : Interval s5Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1280 : Interval s5Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1312 : Interval s5Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat bs5_4_576 (concat bs5_4_608 bs5_4_640))))) (concat (concat (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 (concat bs5_4_768 bs5_4_800))) (concat (concat bs5_4_832 (concat bs5_4_864 bs5_4_896)) (concat bs5_4_928 (concat bs5_4_960 bs5_4_992)))) (concat (concat (concat bs5_4_1024 bs5_4_1056) (concat bs5_4_1088 (concat bs5_4_1120 bs5_4_1152))) (concat (concat bs5_4_1184 (concat bs5_4_1216 bs5_4_1248)) (concat bs5_4_1280 (concat bs5_4_1312 bs5_4_1344))))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_832 : Interval s5Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_896 : Interval s5Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_928 : Interval s5Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_992 : Interval s5Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 bs5_5_224))) (concat (concat (concat bs5_5_256 bs5_5_288) (concat bs5_5_320 bs5_5_352)) (concat (concat bs5_5_384 bs5_5_416) (concat bs5_5_448 bs5_5_480)))) (concat (concat (concat (concat bs5_5_512 bs5_5_544) (concat bs5_5_576 bs5_5_608)) (concat (concat bs5_5_640 bs5_5_672) (concat bs5_5_704 bs5_5_736))) (concat (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)) (concat (concat bs5_5_896 bs5_5_928) (concat bs5_5_960 bs5_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 27 := bgb_4_0
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
theorem bgb_5_1696 : Interval gbAtlas 5 1696 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1716 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)))) (concat (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))))))
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
theorem bgb_6_2624 : Interval gbAtlas 6 2624 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2654 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)))))) (concat (concat (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952))))) (concat (concat (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)))))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1264 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88eeeaeae8eec8ea88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 4006144648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36713.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[2,4]⟩,⟨.or,[1,3]⟩,⟨.and,[2,6]⟩,⟨.or,[3,9]⟩,⟨.and,[5,7]⟩,⟨.or,[8,11]⟩,⟨.and,[0,12]⟩,⟨.and,[1,10]⟩,⟨.and,[7,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4006144648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4006144648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36713

open PEqualNP.Outside.L_meta_36713 in
theorem PEqualNP.Outside.L_meta_36713 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4006144648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4006144648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
