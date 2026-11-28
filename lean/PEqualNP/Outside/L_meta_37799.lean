import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37799.Model
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


end PEqualNP.Outside.L_meta_37799.Model

namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
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

def SBf (j : Nat) : Nat := [6, 6, 8, 7, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37799

namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x70b00001031dc30be43bf42fb30bd42bf41bc40de30bc43d830bd41be40f830
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8004003801e650430cda08613551d0ab4a11866d0830cc2a0619b540c3328418669003096a968398430c33486186610030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x100a2588540c29161d0830a4584540c28962d0430
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s0K4 (208+(h % 11)*4) 4) % 13)
  | 3 => 2*((h/11+packedAt s0K3 (351+(h % 11)*4) 4) % 13)
  | 2 => 2*((h/8+packedAt s0K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfe03fc07ffff01e0ffffff01f07fff007fc3fc
  | 2 => 0x7ffffff81fffffff03f01fffff83ffff98fc7f
  | 3 => 0x7fffffffe07ffffffc001ffffffc1fffe0ff8f
  | 4 => 0x8003ffffff8001ffffffe001ffffe001ff0ff0
  | 5 => 0xfffc0000000001fffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x298c471451232602cb327307025390c2bc1bc
  | 2 => 0x24294890c82450a50155095294834a54985455
  | 3 => 0x485291220348a14a540a12a5296814a960aa8a
  | 4 => 0x61632244920ec5939a6c40c1ce528031d50f60
  | 5 => 0x7183c3871c70f9fce38f9cf80c6318c1fef000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37799
namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x35040202002bd41df31bc40dd32bf41dd31be40de30dc43dc30df43df32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2000a6a96634d520c270a0a0c715132
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s1K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s1K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fffe07ffc0ff07ffffc1fff03fe07e7e7e73
  | 2 => 0xfc1ffffffffffff81f03fe0fffffffff918fff
  | 3 => 0xffe07ff81fff07ffe003fff0ffc1ff81e1f39c
  | 4 => 0x7fffe00007fffffc0000fffe0001fe03e0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x48430231448521016514c0513213212c263631
  | 2 => 0x11042442091082280a41120a44644a509088c6
  | 3 => 0x28894890d2242d52a09265609a919505615318
  | 4 => 0xb2d6712483b6b79cd3d83148ef390619fa03e0
  | 5 => 0xc31861c71c38c6e71ce3b98c0c201861ddec00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37799
namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8436f5250efea0a1db54841ef18a637c514cbdca598df15220bfaa061bf41502f8a910d794f21aea98417d54906f8a818fb948109f2a043be54c83bc63185f54b31bf286657c54ccafaa6105f54243dea16837e5290fd842107b48421be2a661dc430c7ee4310df95210f690e417e51c83f460185b94830f6a9021be4250bdca518dfd4910dfa16837d50907de40106fd0740f7210857e5410fbe8721fb88120bea8085ef4290ab8a6886fd0a42fc28283ec32486fea8905714d42bf294817c53442fea0995fd5221df202817e50903f220085fd5131be296217d53487ec6218df54321df20a83ed32087ba6418df54440bf29865fa20083dc85195f94010ef988635e53043de4210ef95231bf298217d54082faa9187b0c820bf28c637d510c2fea810ef10e40de2a2217d52d0fee63085f55120b729021bd548c77e84a0df54021bea8087df300c37a84a0ef50740be29c417e50d07de43905fd4d20de20c817f54083da65905ed4141bf28e877f50486fea7085b54810beaa2617c54cc6faa7a0ef95021bea9881bf544c2faa1197dd0541beaa2633f544cafca890774c030bba8a61be41103ec4210df95010b629283ec32c87dca420fbd4941deaa021be43903ec20885f94441dfa10816e52106fea7905f94640dfaa221f5310c6f8a8987bd0b32bfa8a877d51c82fca421df14530beaa061ed320caf8a9085f94430bfa90217c53042faa7907754c10eea1887bf401037a84207b10b32bfaa4416e52d02f8a7905f95110efa1c63df320cafea988778c932dfaa2657d5490efca2195fd4540dfa1c87fb104427aa810df944219eaa6417f524c3de6490f7d0c32bf29e817d54c437e8220df95042be2a0657e508cafca898df95040beaa4857d53c42faa7a05f15231bf2a063f710042fea990fb90921f610c41f721486fca22177cca31be29a413d54042fea710db54a31fd90441dc43cc3f420087b90820bf29c217e528437a82a05f54a40bf29c417e54c42faa4885fd4941fc20021bd4210bb886985f94443bf2a065bc43d06faa6215f94042bf298615d53042fca998ef10e42bf284857d538c2bca7205f54e40bf29c437d53042faa0197e50040bfa9421ee42c877c87a0fbcca32b6292217e548cb7c87215f54643beaa2657f52503ba65986f50040dea0883ef20883d88510df94831ee29a21ef42886fca890fb50842ee99261ef4250b7e84215f942309faa2617e520cabaa7205f54830ee98863ee424cafaa3205f54b40bea9c435d53c86fea2986f55021de21a83be435077882207dd0641ee18c617c548cafaa5105fd5331f6194417e54c82fca1085b54b31be2a641dd53c86fca5a1fd48421bfa92637d53c86f8a8886f15130fd884217f54042fca7a15f94231bf29c81df53506fca8105f55110b7a92217d54902fea098fecc130
  | 1 => 0xe5390fbe62985f54843be292637c53c42faa9195f54b30beaa4637e51083be63987bccb21bea8c857e50c87bc621857d4d10be2a643df308c2faa910df54e32be29e437e50887f6a0a0dfd4943bea8e817c50487de64995fd4d10bfa98417d50106faa720cf95010f7214417d54cc6fca8187b54830bf290437c504caf8a898df94410f6a9663dd31cc2faa420fb88521bf284837e5090fdca421fb88420be28a856e5210efca5985f94343eea9c817850506fca3104f15130bea98837e54087bea6a17b50921bea8063ed42082fca9185f15230bea84437e5390afaa6905f94e41bea88857c53503dc64906f50c43ee98a617f53043d8a488778c130bf29a41bc4310af8a690df55210beaa2437f540cafca4886f90d43f6292877e518c2faa1995bd4930df218857e5188778a8995f14540be28a876f52506faa9985f94830ef29c81df320c6faa521dfd4520fd20081fb40c42faa4207b94a40bf29e417e52103d8a4a0df54331bf28c85ef21886fca4107710e31beaa6437c54486fca218df54420bfaa4616d52903da6510f794c20f6a16437f53086fea9995f94810bea86837e53d07f240107b50932bfa82857e528cbbe86a1df54743bf28e61ef5250fb886195f54343bf298417e51d0af8a8105f15030fb98c635c53507dea4885f14810bf2a261ef32882f8a4985794c20f7a10657d540cbda42907d50441bfa9c417e50103da40105f95321bea9021dd328c6f8a6105f94c42b6a96817e53107b8a6a15f14d41bf298637d528c3be65985f94a42bfaa265f4514c3ba64195f94032b6a9061f431042faa3985f14142f7a1043dc438cbd88410df94842bf29843ec42c82fca0105f94d21be2a6217e51d02f8a4a0fb10832bfa82837e518cafaa3195f54443dfa0481ef42c82faa5085fd4b10be29a85be41903da64905f94b10bf29083df53442faa5885f94b40bf294613c54442fea9085f54610efa1e616e528c6faa718df94030fda04813e54c82faa810df15021f790a41f7314c6f8a29077d0d30f7190437f548c6f8a5084f15132dea14817f53c86f8a7087ec8120bf29881f641106faa518df54e10bfa9a437d54c82fca198df55010bea90637e54106fca910770c430bf29a217e5190ebea6a15f55332efa1c653e548c77e85204fd5110bea8865df324c3dca4185f94440bf2a4437f5350afea6a07b8cb20f710c417e52d06faa818f714d41bfaa243ed42882dca598fb54843bea9e85df328caf8a0a0f794f21b6a90877d518c27aa918fb54a40b6292617d5390bd8a49877cc631bf28087ed52106fca9985f94031fb884217d51883dca5a05f94041be292217f544c2faa6885f94a41b6292875f53506fca1a17754c20dfa0c837c53886faa1217794c10ba28a617f53506fea7885f94f21bea8685ee320cbf661187dd4530bea9
  | 2 => 0x20080f024050180b02401028124ec0b00803038010000500c150180000819000000ec160707b23815004010d8040080e0800101c3600020274630bc2f0041e0ec08300115d0080580c00000000072d80206817004020000a000050001712c0000000048010000002c2a0002d0000002800020990341606c0600400058200280f000000500201c0701400000490000600c0e00d89050000340c0401b0dc4200026040090281e0240300019084010002901c002c0120380600c0101c0002c0e0840000418084060105f000000b80c028000000102caf008071bc1c01cdd00411010000588f22005004cf00400004000000001c0001c0104c0d0080f000000080004c070480f01c7305400000190b0043ac031180103000000150800e148090001c0001e00c020080203800008280002003021030190000a0ac0000c040000302c3f0440000c060a808bfa8a85ed528c6faa5a0df14143fb98821f431842fea818df15120bfaa6417f54cc2faa9105b94a40dfa1887bd54c82f8a8995f14131df2a021ef524c3de64107ed0140bfaa4657e544cafaa7107bd0920bf29463bc431037c86207b8ca21bf296637f514cafaa118df94220be2a0217e548c6faa510df54a41be29281ed428cafea8887e10310bf28c83f510043f680085f95332bf28e65ed52d02faa3a15f14943bf29887f9300c2faa3997b10920efa18637c53087bc8621df94f10bf280437
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1544c65f63550219b988535034e5394810b318d428ca6c65509218fd9541106ac644ca219b988540ca5e6394910d354f32c866e62d4c10d3d0c5250e6e6294643cb549411065e6315010cbd50524c23d64d4e219718d51102d463440109718d51d0b1c54d4d10b318d420831f6355231cb55132c826e6215031d314f525066c62551309798c504863e64951329b98a524423f65500408f596540423e64944319b597420cb2c54d49309dd95100434f53d49109e181544874c6254f21d6d4f505072d54108219e181534865e65cc5308f59353c823d64d48109798c54c86776154d109d594310423f6454f219758c520425f63553208f592528425e639482197d8d544426d6214540cb952520426d6294343cb90c5250e6e6215030d354e210823e64d4f10ab593200823e6494d109b58a539063f6454d109b189500c73a41141419758c50486756115020cb552528c677654c4318f992528423d64949109d986544c26d658c821ab58b409027b6055121a719132cc23f6454d20b358843cc25d6594c20c7d50534423e64d4e209b98a53c426e62151319798f520432d548cb209798c530436b52d41419798e52c425f6354620b358f214832d544c821ab588411025f654c832d394d529026e6294d109b58b540423d65904408fd954310e3e6415010d510c514c32d54484219758c528426c6254f419b98b540c23e64d48109798f540425f63551209b98a544432f54d49109b1895090e3e64d4c108f992544c32c4314941cb18954c826f62542439758f540832d52d07409798e544431c53909429b588530426d6294d21d354d520423e65151309b58a534426f654c8219b189544427761551209b58a548c35451cc53097997434c2cc6350a209b195324827561152329b988504c71d5494c109b58a50d066c6254e109b594420865d63d5010cb90e529025d639511097594430c63e64150219ed95401023e65151328fd91534865c6354620cd153514c26f6254f419b588540c36b5214141d314f4250a9c63508429798f540826f6255132c758f544c29c644c8319b99642486ad6210f41cb153524431c5414d109b189509065f6550c439b58b530423e64148108f99053c825d6510c32b318d42c867a6014c219b996324826e6214c209d584540c26d650c8209ed95200833843141419b58854c427965100109b98b540426c6254c40d5cc8514c2cd63c8621d514e104423d6494d10ae191100423e64949108f191538432d54d0b209b58a51cc2ad64c8220d5d0c514c26e62d4f109758e520866f6254e10ab19132c833454145309d98753c827960d53218f59252082b86050441ced08505074c53d49109718d52442776154d20a718d425066e650c921cbd53524c26d62946439b189518c32c54909329bd89500c66d62952108f990514826d6215231
  | 1 => 0x23f64543328fd91538432f5414910d354e520432d54d0821d354a310c35553cc410ae18141d026d6215131b358b314c26c62550319798e50d066f62551309b98a539074c6254c209798f548866c6255310cb951528c63d6414b109798e534434d524c030da148505067960150319b98854086ac644c8219b994524423d6414c10cdd53514c26c6255330b358f21c823d6414f20d614c505063d65950219b997214831f5410d30cb151424ca6f6254d10ab588435066f62553109bd8951d0ead62d0040d394e529026c62551319b588540426d6590820cb55042c826f6255131d3d0c524c25d63d5321cb150524c32e4314941cdd50514c32c4394a40cb150524425f63547428f590520425d6315321b5185300c34d5390b219b58a53c426d65d082197596530432e5454810c7d8d540872d6215132cb153324cb8c4390a329bd89511025d6315010cb54b411067a60d50329758e50d0b1f6454c20d354c210825c63553109b98a544c25e63d50309ed81544c66f6550820ab1894310e5e6315020ce90c505066d62d50309b594420cb2d54c8421d314b324c2ad6210c409bd89534834d53508209bd89518c23c6454221d314c52442746155120d310e528c67561951308fd954210ad56110c319bd954210a9c644c8329718d544423e64d4e21b318d424865d63150209718d540874d530cb218f590514835b53141418f191500c66d62d5331d354f320826d6214d409b98b530866e6294341da14b505072c52d09419758f548865e63d5210b358b31cc2cd6210c319798e50d0a7461551309d984540835853d4141c7551530423e6414c108f593530434d52cc0309b988520426e62943439798c520432e5494a31c7191530826e62d52309dd95210866e6215331b31894310f1d5410e31cb551528c63d6494732d5185530427a60d53219b98a51cc26e62d50209bd89509066e65909328f59353882746154d209b588540c66d6588420ab19132482cc63509328f99353086cd6210e32d3d4c525067a60d53319b58854cc32d54487209758e524423d64d4f109bd95200825e63d52208f191524426d62d52309d984540c26d62d523197d95310c63c6454f21ae181415027765504419b18951d0e6f625512197d8d544872d548c8219b18951102ad6210e409758e52c434f4394a319e596100423e6414c21d9d4b514c26e6295210d9d48514c34d5354a40a718d429029c6350b41d5146304c2cd63c8421d354d200831c6355320c7d5353442cd6210e319d984548cb2d54948109b98b548423e6494820d35885350b4d5350b218f59251cc2cd6210d309b994424826d65cc8209718d544823e6494732c7951530433854c41109b98a548c32c62550218f99052c434e52cca319bd89531026d62951309758f520425e63d53219b98854cc27561d4f209e18
  | 2 => 0x506c00010160000007801020030000006c05000000140000000004031040000023084000b8001380107c06000070040001400460020280003922014010380015c010083706c0000c0102c0001817000000240003c030200047088004011bc000d8101207e0000601c0400439010340050e01008010120003a000030000303c80000010102c0205600001004070000304c0107401060080600400c020000008dc80000200c03074000080400414028000400c000080980d0a41902c07000f5000a40240c004b40c0de008350c068018000100800c41018032c0560240d5c8684505d01806000072b01e1680507000000c73b02f00002000a5444030703101c1a02c230009e001120200001800010002a004004040141e0000000c000d4130300000066006ad64084209ed81544434f5314910a7191324c25e6514d10ab588419032e52d0a40ce181540429c644ca3197d8d524427b65440108f592510c74d53c8020c7952530426e6215231d5145314c33942141419b98b548c66e6214e10d394d520426e65cc9219b988540426d621413197d8d544cb5532145309e980540c66e65d0920b358b310c66d65948108f99353c82796014c21ae580431026d62d52109bd8954cc31c6454f21cb55321c823d6414c21ab191320ca6d62951208f191530827960d5331e310c420ca9c63508408f191534874d520c430ab590218834f53d49418f994544431d5310e40d354e420827b6054d21c7152324cb3954d00109dd85544c26f654c8328f99741502ad6210e429bd95210865c63551218fd91500c76452145309718d54c826e6214540c7d9153c863f6454c20c718d540865f654c0308f99251cc23c6454d109798c530825d658c4309b58a544434c4314930d354c320826d62d4f10c7d8d54c825d63943419e583540ca5d63d52209b189534425f63544408fd91508865f63551318f19150cca6d6214e109b58854cc65d63d5210c7d4c435065f6355310d914b514c26f6255031cb551520426f62551108f593530863c6454d209b98854c434c53149419b98853042cc63508428f992544432d5250740b358b318c65e6314a109b98b54cc63f64549109b195424ca7b654c030d354e529
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x108436101e1004201002008198318c6255320858ecaa26410d0c7454c32c86a2b908628a61831906254f21a18e6aa08410d0c7454c3208306b22a790041451d13214530c8ac428e629864552185300c306320c4a98418355163c8720898eca9a841060d6454c21082163b2a8996418a5486050441c18a831a8499518735085050706318c4aa0438a5486050740a18e6aa0859060d5458f2108694b908628283131d95350b21
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8180c8755163c842180c8759153c802080c87591530842080c8755163c8720
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
  | 4 => 2*((h/235+packedAt s2K4 (20482+(h % 235)*10) 10) % 539)
  | 3 => 2*((h/22+packedAt s2K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s2K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff81fffff81ffc1ffffff03fffcc7fe3f
  | 1 => 0xfc0fffffffffffe07fe0f81ffffffff388fff
  | 3 => 0xfff01ffe03f83fff8000ffe1ffc3e03c0f3cc
  | 4 => 0xf00001ffffc003fffffff0001fffc003ff03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x22441408c48910805940528a252252a8433615
  | 1 => 0x4092289109124116029205214a44a5511888ea
  | 3 => 0xab0a4da243a457aaa83149ed13ea381bc0d34c
  | 4 => 0xca2cb14492071acd34e560481cb31062ed03b0
  | 5 => 0xc30c1871c386371c7398e7180c02183b6ec00
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888eeeeaa88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37799
namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1055800c2010481182101002340110fe20ff42ff43fc42fd31fd32fe21bf42fd41be43fd43fe30fe41fe31fe40fd21fc10ff32ff40ff30fc21fe43fd10fc40fe10ff21fe32ff41fd20fe42fc20ff31fc31bc43fc32ff20fc41fd40ff10fc30fc43fd42bd42fd30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x180001229900020c080601402e00040009a14080621420d0804781000c00d02c40000a0004a000400c16386000e0c28270275a8590db94843aea9c813d54c833886986b50a2096a90876d5210ee8a2984f15131aea98215d530827aa8104fd5132d6a10411c5350aeca31957d4d419eaa0213e54c8278a8885714d429eaa4653e548c2eca2106710c31d6a12433e540435a85194f94c439f2a043ad424ca7ca8105b94a319faa6659f5350abca6084f953219f2a4656e52d033887195b54810b6292613e5410a7aa990cf54843baa8c653e5390e7ea8886710e319eaa4636d521067aa8196bd49429ea94873e548c6bca6105b54a31b6a96815c534427aa810e794c439eaa4853c54cca78a8994f14d429faa2637551082dea4986710c32aea9e43ad5210ebca7204fd5130bba8a613d548c35ca421db94841afa9a853c544c2bea6885b14910ce29a855c53506dea4885794f21b7290219c43cc27ca7a14f95032
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2e01000100080000202800000000015311022c655093287594430cb0c4394a31c354d42c861c6355021c510c514c28c6350a20a358843cc28c63509218718d54c83144394632a318d42c868c6350a32a3588438ca2d6215131a3588430c70d6214d42c9509510828d6210e31c310c524c3254254632c354d420822d6295230a318d420828d6210d30
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xa01002063b2a6a1041411cd4254420a08e6a12a31940c7654d42c8682b908728c65415c84314530
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/21+packedAt s3K5 (704+(h % 21)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s3K4 (2430+(h % 58)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s3K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s3K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffff83fffffff03ff07ffffc1fffffc8ff1ff
  | 1 => 0xe07fffc0fff83ffc1ff8783ffe1fc0ff713e73
  | 2 => 0xff81ffff03ffc3ffe0007fc3ffe3ff0381cf9c
  | 4 => 0x1fffffc0003ffffff8003fffc0003fe0fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2208088820900000a5009044802454500650a5
  | 1 => 0x491491064922612c0a482a29520a82a9312652
  | 2 => 0x8525a2121a46275540c44ea275432a0b818b18
  | 4 => 0x165944a490748a9a73950403a9900c32da0de0
  | 5 => 0x18618738e38733e39ce67730310230c3edf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeea8a8e8e8a8a8eeeea8a8e8e8a8a8eeeea8a8e8e8a8a8eeeea8a8e8e8a8a8eeeea8a8e8e8a8a8eeeea8a8e8e8a8a8eeeea8a8e8e8a8a8eeeea8a8e8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37799
namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xa902014be43f621f521f610be40bc40bd41f410bc43bf42bd42bf41
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x9aa88871e5390238a6a15954810
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => 2*((h/11+packedAt s4K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/1+packedAt s4K3 (108+(h % 1)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff83f07ffffe0f07fffffc1c0ffffe1ff27f
  | 1 => 0x7fffc007ff0fff007c3c3ffe00ff07f913c73
  | 2 => 0xf81fffff83ff07fff803fc1ffff0ff81e1cf9c
  | 3 => 0x1ffffffc0007fffffc001fffff0001fe0fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2080888090a000030144842804411628065225
  | 1 => 0x5159106d2949c670c2a1635720aaa155912c52
  | 2 => 0x124a21240a084a94480269054920c904a18498
  | 3 => 0xa5944a484062952994e8021a92cc02195a0b60
  | 5 => 0xc618738e738ce7cee733b38303088c61fdf000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfaa8faa8f8a8f8a8faa8faa8f8a8f8a8faa8faa8f8a8f8a8faa8faa8f8a8f8a8faa8faa8f8a8f8a8faa8faa8f8a8f8a8faa8faa8f8a8f8a8faa8faa8f8a8f8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37799
namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x144b01904928d0400ea20d08910100bfe10fd32fc10fe42fd10bd40fc42ff21fe41ff40fc30fd43fc41bf40fd30bc41ff43fc20fe20fe40be41fd40dd30df30ff41ff30ff10fe21ff31ff20fc32fe31fd42fe30ff42fc40fc43fd31fc21fd21fc31fe32fd41fe43fd20ff32
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe00100b60801b04000000005984021000004000130010580240400b02140000a002be224c70f020c1040600a8a00000020a00000019d40cc2f2a198cf55210ce20a613c544c6bca6105714d42ec984415d5388278a88857d4d219e2a6215e530c27aa120d714d21dba8a813d54042bca7085754c209f2a6435d53902bca6084f94740eda82613c544ca7aa998ded41219f2a081da404c2eca3215794e40dda82817a500cadaa4085d944329f288833d54c867aa020cf94641bba8a819f40cc27ea890cf95030bc282433c54487b260904f55030ce20e6179500cb3c83985e540439eaa441d93004368a2a06d94441aea98219d404c2eaa2104f55032aea9c213d540827ea9885d944209a28a813c51502f4a021e650130bd286635d53102dca4084f95032afa9a85b441886e8a2a05794e20aea9c61d930c436883084f952209faa2633f544cabca6206790530baa8865b9408c3b280984f952309faa2213d549027ca8106e50130cfa02613d548c27ca9086d10521da20821755190a7ca8084f95331
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x60146618c61002b06150230e4d85404c390414c010cc10450486946150130a6185404c2996010530ac185404c23461552208d59441042596014d42c6d5130c4319544c220a518540cc3906150130b4185404c349524c010a4185404c319544c010a6592404c3255210410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x510715513088288ba88298021c0548414c010
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
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s5K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/61+packedAt s5K4 (2673+(h % 61)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s5K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/1+packedAt s5K2 (147+(h % 1)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffff07e1ffffe0f0f878ffe3c0ffffe40f27f
  | 1 => 0xf07fff801ffc3ff00ffff0ffc00fe0fc7f3c73
  | 2 => 0xff81ffffe0ffc3fff007ff0ffff0ff0387cf9c
  | 3 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 4 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42091111242a220382c1099424492c52405225
  | 1 => 0x2514220c4a504070050a902a40a242a81b2c52
  | 2 => 0x1244424028004941004a20289209208858498
  | 3 => 0xaa598949101aab29a9d0088d32cc0433680b60
  | 4 => 0xcc610e719ce333cece674cc0230818c3f6f000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8fce8f8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37799
namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x403403850310010c00800000064417410000000803820c00200000000c2000002547009007f10005fc43007f50c05fe53017fcc003fc32007f950037d52007fd0003fe2100ffd4803fd32007f55003fe20007f4c001ff1000ff94807fc5401ff14403fc5200ff10807ff5100ff8c805fe43007f54007ff53017f14c01fe5000ff50801fe51007fd0401ff43007f84003ff3201ffd5003fd2100ff08005ff3100dfd4801fd5100ff08401fd3100ff54807fc50007f8c001fc10017f0c001fd10007f54c03fe42007f50403ff21007f10401fe3100ffd0805fc31007f50003ff20007f90407ff50007f90003fd20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa4a003df14153027f8428802fff31440537eb146205ff18630197f8a72086bfc2150009fe32c6227bf58931015f8c6a000bfe324c4137f324a200dfd9543007fac6a880bfc3154c017eb1c2000ff9523102ffa4008002f761500017a30a8000ff59541197fc8720827fd6295015ff90a2002ff14d3104ffe84200bffc5350409ffb162013bf58930017fc8718017fe5044085ff194a803ff54a51027faca20812fc6154001ffa1aa200bf5944002ff8a188017ff621000dff210202eff8c941007fe8308002ff634400bffb242005ff08240027fe6208027ff54d0037ff21a8035ff94f41005bac608002ff6454c057e31ca809ff58343025f8cb1880ffc539502bfe2946000ff5453004ffac3a0027fe61d00137fb2e8200ff10530017fca6a182afd624400bfeb24a000ff50e100effa6520027fc609502ffe108803bef5094302ffec3280cfff5490407bfa8aa01affd494002efea12806bfc525002bffa946005ff94010026fea328827f94010009ff9082005ff0c31004ffe85a0803fd5110013ff31ca800ff5413014ffa8518803ff4394425ffa9e200bff90d10077fca7080a3ff544c42dfe28c6005ff18a30025fcc32a027fd61d0c81fe102a804ff08410005fac728817fd6110039fe28a8000bf5825402dfcc118077fe219007bfe9068600ff191100077ec888017ff5090009ffb1c820aff1491002ffc41a0017fd6204005fb98c6215ff94a30007fca298103fd325504dfe18ca005ffd8c10025f8c528847ff30c4035ff2928014ff9953006ffe8508017ed6204001ffa1aa002ffcca30187fea8a08027d6504001fba082000ff5474014efaa518903fd6255001feb2a6007ff90c1002fec2088003ff644c015ffa922009bf99230005fec2a0027ff5495063ffa948209ff90c41017faa698003fe5110001fea1aa200ff58553007faa3a0827fc4110013ffb2e8604ff4871002df8c608013fd65c4057fea908204ff14510007fec298003fd654400bfe9008004ff88651027f8c988017fd5010007fea92a600ff19150027f8c72881bfc520400dffa902040ff8855413ffec4988c7fe20904017eb008229ff0823102ffccb08013bd4110407fea92a000bf58e4101ffca6a8816fc6210009ffa08820aff94910217fc412a043fc32c4009feb048205ff9925002ff8c808017ff408c0097e30a8003dfd4553057fe648800afe639404fff1026200ffd8d5002efcca08017fe620400bfeb108005ff98840017faa7a1803fd5184009ff18e2009bf99254027f8a208017ee62040013fb2a8009ff151540d5fec4a0027ff4050013fea188200ff5814109ffa409800efe65d0401ffb2a2000ff90630017fa6518827fe62d0c01ffa0aa005bf98341007fa8728803ff4394001fe98a8004ffd8a41177fc40a0827fc549000dff2902009ff90b43
  | 1 => 0xffe2054c0bffa048005ffd8a5002ff0a12804eff624c013fe2168009ffd9740027fcc52081bff42040697eb168205fd4401004dfecaaa0a3fe654c4097fb288201bf98b4013ff88498802fd654c0077f32c8005ff08310007fca318003fe5150001fe20c6009ffd8f41007fcc2a9802fd64944017eb1e8200bf58654007fecaa0013ff6494401fea8a2009ff10a4114ff8a518817fe6590013fe20a8023ff58950087fa658800efe654c413dfa1e8000ff54140005fec898802ff6150c63ff9048200ff55241005fac918803fe4190047ff312a005ff58c10175fac4a0817fd6194001dfa1c8200bfd815314ffea518806fc62d0c0bfeb282003ffd5250027faa208017fd628400bdfa008009bf9911002ffcc620027fc43d0001fe98c8002fd0c53104ffaa9a000f7f505440bffb0c6001bf9884104ffe862000bfe53d0c7bfea968600ff985400057ac8080bafd6490401ffb0aa609ff18f4002ff8c328027fc439040bfe2026004ff1051005ffcc688012fc6310427fea926009ff10941027fca288003fd6550001ff302a203bf1954002ffec508002dd63940017eb242004ff99231027fc4388002ff6154005ff9946205bf19210007faa8a0827fc4295005fea9c6005bf9825001efea728003fd5044013ff2a48004fe44010177fe40a08777d52900017eb28823bff5894304ffcc12a013fc3154401df2088005ff88250217fe412a00afc6354005fe21a6240df54954007fa86a8027fd62d0c01dea1c8204bf98743007fe8298013fc410402ffea908009ff5974004dfec52a027ff43d044ffa90a6204ff94410007faa6a0017de6394001dea1e8005ff4823001cf8ca88027bf41d00097e30aa601bf9894301efea6a8803fd614c0097e3146200ff1065004ff886a0813fe418c407be284a200df19543005facb20813fd418c405fea1a6000ef19151017fa6318017fd5004013fe21ca81bffcc5400d7fa40a0017fd648c02bff2146005df14150007faa688027fe6295013ff2a2a804ff0c4411ef7a85a180bff318c03bfea148004efd06410e778a8a0027ff4110013fea188031efd0a410d7fc84a008fff62540017eb2a8600ffd0e1017ff8c6a08d3fd52d0413fea1e8200ff10550005fac7a0017fc648c00bff31c8000ff5915000dfcc488013fd628c40bfe9842002ff94d30097f8a988013fd648c441ff1968024ff0c55000df8c5a08fffe6254c0bfe2042000ff1815302ffca1180c7fe329042bff90c6003f7d4d53057fa408804ffa204c043fe29e8002f714d300aff84318016fc605040b7e32c2005ff0c240007fac6aa027bf42d001bfea942009ffd0b430d7fe64a0013fe314c40bff2828005bfd8810057fc8488017fc6294081fea12a818ff94c4000df8c4a806bff2150025ffa862000ff54c1009ffe8498027fc61d0007be2
  | 2 => 0x41187f8a0a0806fe625440bff314801dff08640027fac420817ff658c0017eb246000ffd0d1001ff8a12a016fc648c00bee182603bff88143025fec5188cbff3090401fe982201dffc8640007fc62a800bff534c407ffaa2a201bf98a4015ffc6420813fe41c400bff2848039ff8ca511fdfec4a9817ff2094005ff9826205ff99010107fa43a0006fe624c487fe184a803ff14d50025fcc328053df534c001ff3028609efd08411bffec4a8816ff6304009fe98e2006bf58810027fec12880aff6450c47ff192a004ff48641007fcc2a8107ff315500bff1042005ff10110027fec020802ed620406ffe312a203ff55250007fe860800bfd438c04dfe21ca000ef5054001ffea72a083fc32d0007fda82a005ff4c01000df8c4a18bfff3050409fea0e2000ff581540d77a84a0017fc62040057f31aa02bfd4844121ffe612a00fff5494401fea1a8009ff9974302ff480200c7fc3290407fc282a005ff98a10005fac128826fc6444001ff2a62000ff55131027fe4318826fc6454401feb1a201eff90e40017faa71880bbe43d0c0dfea902004df99641015fac71880bfe538c00bff1842003fdd455102ff8800800bfc31d0c077f32c8210ff50b101bffac4a8803ff4144037ff29a8013ff18930017f86298006fe6204007ffaa2a01fff1464002df8c80800e7e6504045ffa8e801dff14a4009ffcc4980a7fd208c40bfea042002ff8c953006fca928017fa208c0077f3288000bf58640217f8652a107fe4355001fea1a202eff0c941025fcc328802bf6444031fe1888001bb98810007f8c0a880bfc5354c09ffa8c8229ff90a310affe8518016fc628403bffa948000bf5951015ffa402080efe65d00017fb22a004bf9844101dfccb1880f7c5454409ff98c622ebfd8941027fec728817fe10440137f3246209ffd0940017be60a180ff75194401ff18e8005ff5864004ffec3a1813ff410400bfe30c8004ff18a3113ffe409882ffe5344053ff294623bffd894301ff8a4aa0bbfc6250463bfa948201bf18931027fec518813ff63104056f3188000ff50c101d7fc8728803fe3194041ff906801dff94a40007feca98026fe64840057f3182009bf9904002ffecb080437d52c4001fea8c6004ff18251007faa2a009f7f524c409fe304621dffcca40057fe8488017fd508c061ffa8a8203ffd515302ffcc528003fc6050c13fe3168004ff08631005feca88013fc31d04097e3148225ff8ca50027f86308003fd6150c73ff104a203ff1455401ffea32a0affe2010407fda84a007ff94c1002ffc200800bfc3150c0b7fb202027fd8853104df8c8a980ffc539405dbfa928200ff5064002ff8c928003ff64544017eb1ca804ff14631017fc871882aff624400bff102a002ffd0d43027f8632880efe6550007ff292a805f758c4001efea52a0f
  | 3 => 0xf29ca802fe0c13002ffeca20002ff6350413feb068209ffd0954027fe43880dfff20544137e3226201bf9894104ffe86208afff5210409fe10e2004ff8854115ffa64208d3f521d0457ff9008204ff58e41007faa320013fe60104017eb0e8600ff1913002ffa2008016fc65900097fb2aa200bfd8141027fcca20827ff62d0437fe18a8014ffd513004f7e86208e3fc4354413ffaa68635ff14f4101ffea2a980fff525500bfe32c8025ff4865004dfecba1802ff6550085ff10ca822efd53401a7fc41a08d3fe32d0401ff30a6040ff48154017f66098016ff638404bfe194a009ff152411e7fea8a180afe6344007bfa92a602ff94e31007fec0a1812fe6190405ff1928609ff1534002f7ac92800efd6594023ff21e2033efd524113ffa4298827fd541044bfe214a009ff1084104ff8a8a0813fe3184009fe18a2003ff551511cff8852880bfc5350c13ffaa0801bff98d40025f8cb88043fc52c4077dfa128603ffd425404df8cba0827fc63950017eb2c2040ff08554167f8a620802fd639001bff1942009ff597411cffe4128817fc6394047fe212a000ffd8d40007f8c2aa012ff64c400bfea848033ff14241127f8c6a803bfc53840017fb0a6009ff9865402ffc609805efd6210013de2088005fdc421002dfecb20043ff52c4053ffa146204ff0c410147f8a898833fe6544001bf2a2a205ffd8a30005fec8980bbfe6250401de3222009ffd534101ffea328016fe609040bfe9048009ffd8f4002ffc409808eff625400bfeb1c8003ff55251027f8a38800f7f5294075fe21ca203bf9953002ff861a008bff50d0043ff9868005ffd964001ffaa8a800fbf5495013ffaa08205ff1434012dfac528013fe649440bff3088032ff0c241007fe831810bfd2195049fe21aa005ff18c40027fcc128813fd518c451ffa8a6209ff1525401ff8a72883fff5484021ff2962004bf1854301ef8a328006fe62d043bff2148030ffd4141017f8609880aff614c47ffe212a610ffccb1002ffc40200cfff50904097e30aa814ff195301fffe40a9806fe62c4001fea9c8002bf98e41187fea6a0813fe631046fff192a202ffd0e3004ff8c3a1827ff4150001ff30a8605ef9925002dfecaa8002fd60d0c13ff3068605ff58a30027e8631880bff434c051ffa826201bf98840007fcc0aa0837f52d0051fe2826202f710d4304ffe86a0002fd63104057f31e8005ff58630007fa809808bff53d002bfea946003bf19541067f8ca8802bfd524405dfe90a8204bfd8841027f6210800afe635440bfe3282003ff14d5117ff860a0903ff325500bfe2046002bf18f41017f886a9803ff40c400bfe3288000ef50c41027f8831887bff31900017eb2a8003ff5515301f78a8aa006fe62d0c09ff28c621aff549401bffc40a8817fd40100137e32e8633ffd4e
  | 4 => 0x27ff4390059fe1808209bfd8b4018efaa520813fc41c4079fe32a8609ffd8b431eefaa5a180bfc43d0c07fe282a638ff18d51005fec6a80f7fd21d0c1fffa8c2002ff0c34309ffe4098013fe51c4077bea928605ff0c1501d7fe61288b3ff3010441bea968004fec411016ffea6208c7fd42904137e322a005ff8823004ffac7a00377f5284007ffa9ca200bfd855404ff88420027ff4250c0bff2008000ef9064001ffea6a8002fd618c06ffe90aa201bf98a311ddfac4a180ffc54940017eb1ca03bff08143027fec52880bfc434c009ffa0c6227ff5093104ffaa9a1823ff540400bff900801dff54a4001dfccaa0803fd544c007ffa82a600ffd954304ffec52a017fe2050001feb0a8004ff19710127fe60a800efe6584079ff32a8602ff8cb431bff864a88f6fd62d0c013fb2a8603bf59651027fcc118803fd50c4009ff31ca202fdcc531015fecaa9827ff6195009ff314a200bf58d1002ffa8118027ff4190009feb14a209ff550401cff865288bbfd42504097e31ca200df9465004ff884a1816ff6484009fe9088205ff8811004ff8862000bfd438c413fe2168209ff50a5413efaa49880ffd5255001feb028605ff0834002efca0a8013fd219443b7eb148004ffcc65102ffec320083fd32d000bffb246004ffd9310017fc62980d3ff20d0405fe21a8602ffd4d53007fec2aa013fd65904637eb148200ff50e4001ffea2a888ffd215400b7fb2c603bffc814318ffa6520817ff509400bfeb148000ff9915011ff864a800bfc534c005ff982a605bf9801015ff86420817fe658c001feb222005ffd941006ff88508017fe2004007bfa92a22edf549410f7fca720027fc43d0473fe904a200ff54f1002ffe6128027fd6395013feaa68200ff181411effc41a190b7d529500bff2042002ffd0e3101ffaa4a8817fc509400bfeb2c6005ff8c11013ff84098812fc65104137e32e8004df1455104ff88320003fd404400bff9042004ffd44411bff884a8827fe43d0401ffb226204ff947411fffac4a980ffe535501dfe21c203fff48553027fcc588013ff5194421fe906203fff1895305ff8c6880037d5394021ff2162035ff0c34102ff86128083fe21d0005fe9926205bf1813101efea52880bfe324c00bef9846005bfd884004ffe8520003fe31100017eb182000ffd8d51017f8a7a180fff5394007ffa8aa02eff0814115efea42090bfd3295009ff32c8204ffcc71014ffaa518817fe300400bfe31c2042ff0825409fba6498003fd548405dfe9928202ff0c953005faca08013fe2190401ff28c8004efd0441005fac220017fe6504009beb2c8204ff98a3101efea4a805ffe3210031fe2988004ff8853102ffa8008003fd64544013eb2c8204fd88441017f86498813fd6290405fe18c6009ff5974304ffac12a017fe50c4087b
  | 5 => 0x8f4302ffcc3180bffe435040b7f3042001bf18a5402df8c0a180efe65d0c0bff2002023ffc815002dfecb0806bfd6250013fe2a08202ff0c143027fc4220813fc5190453ff104623cff1414313ffea498817fc40c4077bfa92862eff1494102f7cc808003fd43c4017fe21a2000ff55110087faa588013f45194447ff10aa004f70c53109ffa4298017ff2004001feaa02000bf591311fff840a9827fe62d0063ff2948201bf9893002ffea10800ffc529507dffa8e8605ff1963001ffea52a002ff654c405fe1968605ff14210105fac5a00bbff5250407fe2a2a203bf195301b7fea7a0817fc3084009fe3148213dfd493001dfccb88003bf4150005fe1926004ff1923112efaa528003fc6154001dea1a8017ff48440017fc631807bfc3190009bf28aa202ffd4d43027f8a2a080bff324c409fe3048202df94d5303ff8860800bff3050c05ef9926005ff08250027fe8388002bc64544015e3222000ff8c54006dfac50805ffc32100016eb188000ffd915307ffea70800afe635004ffe3126202ff8ca3004ffc83a00bbff325044bfe994a003bf9951016f7ea820803ff63504017fb1a8009bf991310d7fc64a0026fe6494029ffa8a603fff8855304ffec1a180bfc538c007ff294a809ff9514102df8c0aa10bff3295009feb008234ff4874104ffcc7a0813fd639440bff8842000bfd9530007fcc898017ff308405bfe2808205bfd8a101eefea5a180ffc5454007fe2a4a241ff0c554027fc6288013f64110437fe29a8000ff4c74002dfcc11880afd638c023ff29e2034dfd4b4104ffc872a027fc43104017fb1aa800ff181541dffa42a1867ff5110013fea0e8027ff5893101ffaa52a00ffc509440b7fb146005fe0c23004ff885a1816fc6504013ffb0e801aefd09401a7f865a0812fc659040bfeb188003ff1415101ff8a8a9812fc62c4013ffb04a80aff8c910087fe8588013fe414c4057f31a820afd48510205fec4aa05f7f52100073e32a8602ff0c9430077ec8a880bfc3054c07bfa92a800df54d5105ff8a68800efc654c409ff1882038ff0c15104ffca9a00effd5250c81ff212a80dff486100b7fea918012fc621040bff31c2009bf99010005faca98827fc619504bff10ca040ffc8554007fec6aa017bf40900077e32a2002fecc23000dfcc52880afe631000b7e3102009ff50b40027fc82a080fff535446dffa8e822dffd404101ffea128873ff545001bfe1942000f74c53004ffca92081bfe3204079ffa8a8609fd5044104ffac32a0f7ff20d0c017fb026200ff50531015fec6a1903fd215500bfb880202eff589411d7f8612881ffc5304007ffa82a004ff0c631067fea888012fc6390401ff2a26200bfd81540adfac518003fd644c0017fb0aa609bf9904118ff84120817fe404c009fea8e2013ff1093002ff8a0a8
  | 6 => 0x97fb246205ff9023002ffac708083fd20d007fbea92a604ff18c4101ffca928803f7615002dffa8c6004ff88741157fea91882bfc3244069fb10e821aff9894002ff8410800f7c53950097fb1e2015dfd4a3004df8c898016fc629000b7fb282009ff1534302ff8c52000ffe5454063fe9048205ff98a30007fec2a8027ff65d0413de2a4a80dff4ca10027fccb88027ff6395001fea9a820adfd49101cdfac528802fd65d0c81ff102a837df5495101ff8a32a0effe2150c09fe18e2004bf98440015bcc72806b7f5250013ff2168014ff15130027fa420800bfe328c413de2a68001bf98a1001ffea8aa016fc631000bfe1826000fd1854010ffe63a0013fe639040b7e302a200ff5815304ffa8420817fc6210001ffb02a614ffd4130067fea2880e7fd42944097f30c6200ff98554025fec528883ff21d0001de20c8002ff14e31027fc4308027fc425000dfe1902031ff90a4113ffa4098817ff301000bff1048030ff1954119f78a92082bfc6244005df21a8627bfd893104efea92a0037c6550073bea94a22eff90941217f8432a017fc639004fff2126200bf59110027fcc1208a7f5218c4017eb048203ff9515302df8c720013fd608c40bef3182000ff90650017fe62988fbfc50d0c41fe10e8004bf9864013ffe42988af7d5210401dfa1a8031ffcca41177fa40a0802fd658c00b7fb246037ff0815102dfec69802bf6214407dffa868604bf19231027fea208002ff655040b7e3288042ff48254027fe4320812ff6290405ef98a6023df54950205fac4aa057fc428c001bfb2a201abf5924004ffc852a012ff659045fff98a8204ff08641007fac6a00dffd325440bfe2826000ff4c65000df8c498027fc54d04057e31a203fff50953036fea408017ff6390073fe104a22bff0804121ffe632a027fe43d006dffa868204ff0853102ffe411806bfc62500077f32c6009ff1514311ff8c4a8017fe4050013ff3068204ff18b1002ffea020006fe625405dffb128220ffd4b40005fec8a8883fc52d0005ef21e8620ff94b4013ffcc498816fe60d0c35ff9028005ff14040177fe42a080ffe5494007fa28aa205ff59010107fe65a010bff2195071ff982a200ff5915301dfcca08013fe2154409fe10a8204ffd9231055fac308003fe645440bfe1808002ff10e30017fea69809ffe524c40bfe102a00fff152101cffa652882bff2044015fe2122000ff55230027fecb18816fe6090005ff9826002ff4c953027f8c52889ffc524c40b7e302a605ff90110007fa6188003ff43c4045fe28e8001bf9895304ff886a00bbfe5250409ffb046223ff4c95002f7a80200f3ff5050c777fb128600ff5514004fee82a080bde434c0017eb24a019ffd4c40027f8a298827fe65d006dfe2868206ff10810007fec0a88277c545504bfea14a002bf5
  | 7 => 0xa9827ff60d04077f32a8609bfd974001ff8a528816fc6384001eea1a6005ffd881001ffea4a800ffd5394013fe32e8005ff58a5004ffe82a0803ff6150c0b7f304a203ffd4a5104ff884aa013fc63c4009fb10c6201bf98a5402ffea118003fd5490009ffb108200ff50d4104ffa842000afc6350401fa20c203fff08553007fa6308103ff205504bff214a002ff94d3104ffe8520813ff63c400bfe904a000ff5514302ffc4188027fc60d04073e32a8026ffcc650025fcc31800bbc43d0c0bfe2846000bf59740007f8c298013fc5110409fe28ca21cffd414011ffe64a8003fd61540037e312a60cffd411001ffca72a05f7d5210077ff3128609ff10d54007fec8a800afc6355001fea0c2002ffd4e30047f8a8080bffe5350449ff31aa005ff0c23001ff8a2a8016fc658c005ff21aa602bf98c4113ffe8498827fe61d0c57ff2908209fed014002ffac908003fe54840017eb2c8005ff0813002ffacb200e7ff3294409ef18a622bffcc84102ff8a08800bfc328c007ff292a005ff0c14014ff88518802fd60d040bfe3242000ff181311eff841a190afd629504bff90ca004bfd8d3109ff24098002fd6550477fea128605ff0c01001ff8a4a9826ff62d0401fea0aa009ffd094109ffac49800bff30d0c01fea06201bffcc14002ffe6118073ff5150013ffa14a804ff54641007faa2a0817fc3044039ffa9a8009df9515402ffc618800fff5254c05fe9926000bf5874004ff883a0017ff5004001fea868005ff1401002ffcc32800bfc438c46bff9868205ff0804014ffe4118802fd65d043bff1948017ff4c84002dfec52800ffc5154c83fe31aa800ff5453106ffa8508027fc62d0401ff28e8002ef10d4301ffea0a8816ff65100097fb2e2004ff58251007f8c898802fd608c409ff3108215ff4863004f7e85a1803fd61550057f31ca81eff14e40007f8c2a9833ff534404dff21ca000ff55231027f8c928813ff6510409ff8822040ff8c9541effc43a1812fc64c4007ff292a62bbf58841027fac928816fc62940357eb128000ffd911009ffc4298013fe4110401fea9c8202ffcc95305ffe6088017fe6394009ff28a6205ff5944001ffca8a88037d515401bbea942003ff14a50017faa69886bfd21500097f30e8009ff58f41027f88298803fe4154001ffb028205ff1961004ff8a820097ff3294013ff2a08234ff0834102fbac72800ffe529406f7eb12a204bfd963101ff8a6aa00fff5294005ff21a6200ff50650047fea608002fd61940097e31e2023bf589501a7fa65a0817ff30040077fb22a841ff98d54007fa62a806bfc3250013ff31e8000ff58d5001ff8a32808ffd4254009ff98c8204ff9454100df8c4a8813ff609043fffaa48002ff4c943007faa7a0013fd4110401ffb02a80aff4851002ffe2008006fe629400
  | 8 => 0xfd8e5001ffaa6a880bff324c005ff9968600ff99131027be6318827f74190409fe10c2037ffc85510cff8a22001bfd42040077f3288217ff8844002fbcc620083fd52d0035fe9928002ff90d4300dfcc520826fe644c069bea968217ff94840007ee8308026fe64c404bfe10ca034ffd4b4102ff840a0016fc6394005fe9946025ffd0a50015bcc6080efff5250c017eb188005ff08110027f8cb2085fff3210077fe2928600bfd815100df8c4a080eff6154439dfaa28009ff99741017f86118827ff43d0001ff18c800eff90e1004ffc8220027ff41d00017eb2c6237ff9095100df8c48800e7e65904057f31aa804ff14741007f8c8a987fff5190001fea98820dff14a101c7fe62a8903fc325500dbea902003bf195431cffc8528802fd6404001ffa026002ffd4e31017fa629805bfc548c077ff2928601bf98a30085fac58800ffd5194001ff20a6000ffd8540005fec6a880bff3250c49ff21aa003ff54d501e7f8a2a180b7c5354c13de2a08200ff59531017fe6118827ff62d003bbfa948000ff50530057fa64880d3fe52d0409ff9888209ffd0e4109ffec4980bffe6350401ffb1a200dffd4a101bffcc4a886bfe21500057f31e200dffcca10067f8a8880d3ff32d0413ff2108200af9925000dfcc4a008ffe42540017eb226000ff9915311ffa40a8013fc6390409fe90c6203ffd4554017fe8698827fc62d0c0bfe100201bff18d40027f8c020802fd64c4009fe28c200aff58910087fc6588003fc645440bfe3142000bf58f10147f8ca98843f521c40037e3168003ff946500077a83a0003fd31100013fb2a2000bfd954308ff8a788093ff3154063fea948237ff5095102fbac60801bfd3204009ff10a2005bf9825402ffcc918013ff65c401bff2942009ffd0d4104ffca9a1806fc6255071ff31aa203dfd4654027fccb18817fe5054009ff9088204ffc865102ffe412000afe63900137fb168605bf9804011ffe42a806bff625000b7f3008205ff99210007fca898013fe210404ffea926202ff0ca31027fea318903fe6255009fe10ca204ff084410057cc80800efd659500bffa042003ff1495100dfcc4aa027fd43d007ffe902a609ff58b4104ffca8a1813be4150413fe2148004ffd064102ff8a0a0006fc625000bbeb282009ff5044011ff842a8027df4350c5dfea928209ff50b43015f8c7a0103fc6255041dea168013df5493004ffa85a084ffd424c013ff2a08000ff50e41017fe62a98fffe4254c07ffa92a237ffcc951097fea988003ff604c413fe2a28000ff58131007fe82988037f655000bffb088004ff58c4110ffca7a00ffff6254c57fe2908205ff18c1001ff8a4a8027ff42d0063dea148232ff94e41187fccaa0803fd6054409feb2c6209ff10e40015fcc9a180bfd434c453bfa946203ff949511fffe42
  | 9 => 0x100900415402700d04f00004d00f03300500304c03600001700c06c0153c304c01d0061530000290926ef06b0110230160d600a00406703b0030000380020120ff007fc82a0073fe6550005fe9968600ff952301bffe84a8816fc628c001fea988004ffd964115f7a8420802ff6050c69fe2968204ff14551037fe6408013ff51c400bffa008004ff88631025fec58800bff314c009ff28c2013ff9093002ff8a12002bff6244001ffa022004ff993101fdfac4a980bff31d0c59ff2988205ff98c1001f7ea8aa00ffe539440bef1826004ff10610007fecaa0816ff6290005ff21e8602ffd4f43086fea588027ff4210401fea0a8005ffd9010007fa831800eff605400bff2826005ff59610017faa6a18f7fc21d0c0bfea842004ff9051001ffca6a8027fe421000bfd0802013ffc85301effe43a1813fe5154413fe32e8604ff194411a7fa41a0863ff3110007ff294a204ff085510e7f8caa0013fc6210413fe3068604ff9464101e7ea92a003fd53d040bffa002039ffd0a5102ffec520003fd3144009fb10e2009ff9514009ff84298017ff638406ffe902a217ffc84401effea5a18effd2050c097e30a6002ff90d30007fcc0a988fff4254001ffa0ca037bfd8951027fcc788017ff3090001feb1a8209ff98b4102ffca020003fc6150c13fda048035ffcc741007fcc88810ffc319500bfeb1ca038ff90d510affa8518017ff6310009ff2082000ff50510027fac788013fd64c4007fea94a004ff90610027e882080effe4250c13ff2168202bfd8d5310ff863a000bdf304c407be284a800ff59543007fca808043fc42c4001fea9c2000ff95110017fe62a180bfe5354c07ffa82a841ff0c154027fa62080c7fc5290481ffb12a802bfd8130007fac898803fe604c4057e31aa204ff544410d7fa84a0017fe40c403fffa9c8004bf98410005fec88800ffd5394407fe282a804ff0c6411a7fe43a0817be405007bfe2968600afd915102ffa41080abfc548c407fea8aa013ff149300a7f8a298013fc21d0407ff28aa004ff0c531027fa8208017fe619000bdeb202009ff18f4104ffca9a0827fe431007fffa12a605ffd925006ffc85080037c654402bbea946010ffc8310007feca98803fd4394077ff90a8600bf59710015fcc7a0827fd62d0009fe18a8213ffd49300d6faa4a003bff318402bfc904600aff509100affc431800fff5355015bea92203bff0854304ff8c52a0fbfc51d0c2ffe290800aff9891002ffca10800afe63840057f31ca204ff94441007faa988017fe50d00015eb24a005ff082300effa4320003fe6050423fe21e202aff142310bffea420107ff305501bff90c2005ff184400eff8652000ffe5394005ee29aa600ff185401effca5a18effc6250c55ffa846209ff19741027fac58804ffe524c00bff3288005f
  | 10 => 0x30030af00500201400302d2170010060180290000005e007300000600205100729000706101d03501903404400500200504e00400000000000700000a00101d27100100000800000101753900300001e02a01202700600e00000e00603608e00901814500300d00b00803100100722100073404d0010b00f502b04200501203001303b0080010000320000260130171ac1ba05d00307000108902a0030160010083b800200601800000b00605502c00421404803902e00000800d0020050050050000053ff5e80050000e201400d0080e60127c500a00601800210b02001700100200900300601700000600300600700200300412d01205d09500204500100000400101502900100706001604700200700000502e02402717300000400d4d000300600301700500003505103d00002f02700600905801305500205500d0460200000030000000060000090410180270010002cf00c00800582800001d6ae06e02600600302200d00364500322500b02338800200c00301f0b00310170550762380000c40002e100000100601109000a00e0322d700b00000000010300200300000300000300900200000700000400114c0050020080320070000323220cd22000003c0070c600303100001672600f00704500700001c05600502d0000022a400200f01100031717000009819600f00867f00d04a00000700703a01801600300701b01a01900d10400201100001900500100b02100700834c00800a01901400e00300002e0150c800001600b02406b01e00300b01c00101122301a00a00700001b00100d5350220881970070023b500000a00400018021f01000000000000105c0000000001981ec00e00000000b00102700f00f01e00000601400208f0010030010a40170c20900010040050520020d303e00200200800300000d69f03e01800509a01103701900900100901c3a10020000010020190dd0a000205500015502248706d0010a60020023ba0ca00003e1a200403c07700500800300000024d02104c33a00000100001500f00800400300f00200300c02561b02a00400600321a02300000c00b01c03b00200300f00023000f38f76300a00713402d00221600000101c07d00200006200e00a04f0b80000010020020010160320440a702300500056113d0020010123472f90000170710000b100700004f53302200204f03c0002590050030010000061d50bd04a01c00400102600401a00500003300001d0060000000890020170000660250004f40690df06b00003300401b00102413600d06100200400100205510e00201701f1580040010280a406131000000000202003401400100703000a0f900138400228c0140060a000601403400400000900000a00000403409205400e0000240000f701500300500d01400d00d00f1b807101003
  | 11 => 0x300eb00300002000300003200009000b00500a00a00000500200002101a0006a401403b000125004000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7655130005bf7454f4021f5c43d9543004ff73582410067c2059641266bc71d911004cff76d0e1002cfc705953119ebe65904400067f72594100b67f5159630005f47158d4001cfe75d9110004ff7558e4102e7d205941002edd4058c100067c65981430267d215941002cfe76d051002ebc209925027f7a7094650007b5741854001cfe7558740016be6350e4102ebe105901007ef651d85500067f5258d100067d42d95404073e51d9151004fd7655010005bf745815104fb771507400067f5258343004ff74596301163f529925024fb76110640004ff72d913102dfa70d051000cfe7259743004ff72582540f6df3258e4000cec7258d10014fc73d81410067f72d951000cfc725825102eed705881033e7c43d95402ff3d52d0540227b740d0410006ec755881000cfc72586540067f52582310067f52591300067f6554140406be31d915102ebf405864001cfe7559130015de73951300dedf30d8d4004ebe64d0610026ed715881004ef7415874333e7f40d954004f3c5455241005fb705064004cfe74d951004ebc6450d1004dbf7010640004ff735865404ebf75191100267c51596311c6dc32d8d5104ebd76d0e41006dc7458e50004fe76545300067f6550510136dc3158e50026f66118530006bd425913004edf7358f410067d6554530024fe71d9540006bf4259250024fc71592300067e54586500b6dd53d8d5001e7e655463004dbc7454140436be5119151166de5358c4102ee510588100067d52d855416ebd5319151006bc72d9151014bf7650e4100cfe72597401457c755813116ebf521915100cfc72d855002cbc7459740006df7258c40006bd6310640026df7358e4119dbe761915127e7e20d9510024ff761065004edf4358c4102cfe76944400057f7550d100067d325964102edc2058c40024fd70d8d1027e7c10d9510026df2158c10006dd3258c4002e7d10594100067f65501100063d529901027e7c30d951002ef610586400267e51594410067c62d95400065f5258c402ae7f6254e500a6dd73d953027e7f62946500067d6554c41006be72d911004cff76d0d10006f521583411e67c50d9543006bd6219110227b774d8540004fd71d9530016de63d0e50004ff7654f4102ef4105844004ebe64d06302a6f562d061021e7c5358e5401cfe7558f41004ff7259131004fc7655130006bc42590100067c659854016fb451191510057f7550650006f7201854025ebe70d9110006f4531854001d7c7510650006f463d854001e7e6554e41004fd71d954301f7a6095250004f77159540004fd74d951004cfc7458e1002e7c5059410006bf64d8151006bc321915127d7d709465004cbc745863002e7f7559630006ec7458810005bf7454340004fe7695110227b664d06100067d525971033e7c5459250136df3258e50
  | 1 => 0x4c10006df735953102ebe5059250016de6354c41006ed53588100167c7654d51004fd7258f400667c53d95101c6de63d8d510267e515941002cfc76552300067d62d9540026dc3158e41026f44159010006dd5258c10006ec7258d10016de634c610005bc74545303367f65191502857f75106501e67c65595431153c7550f40014bc7458743005fb705451004cff7650130006bf54580410067e72d9543005bf735074017ebd435923104fb6719044002cfc70d8d10005be76d054002dbc7050540026f764d041004ebf7399010004fd74d855321cff755954305cfd764c110006bd64d06500067f62d9540026ee5158810015de73d013002edf4058e50004fd70d85430057f7558d4100cfe7259630006bc545921021e7c32d95430067f6555140004fd73d855000cfc72596400065d5258e50004ff76546400047f7259641006f7619054000cfc72d8d41006bc42d91100067f654c540006dd4258e500657f7219510004fd7694530024fe765523100cfc7258e54006f76110530026de614c53000cfc7258f40004fd725913101cfe75d8d1045e7f52d915302ebf509901002df87054530004ff705865419f3e75d915119f3c5490650006f765d854004ebd721911004ebe7119110006bd645063033e7f42d9540024ff715941002cfc7158f10004ff72d85542473e65d0e41006f52158f102867c41d95100dcfd765013004ebc719925002ebf4058c400067c32594100073d75d91510067f5258c4002edd5058e50297f040d8540136dc4358e5004ebe7399010004fd72d814104fb66150c410267e715941034f3d529064000cfe72d9541006bf54582413967e50d8d5002cfd75d91500667f53d951022f7752d0410186be545925101e7e6554c4101cfe76d95410067e63d9510226f440d8540006bf42591300067f7559131004fd71d915304ebf4258343006de32d8d540febd54d91500a57e7590530026dd4158c1004ebc7519151004ff7359250014fe73d91100e67c6559540004ff735921004cfd71d9541024fc7158e410067f65185401167f535974004ef8405804104edf4358f41024fc76551410067f655454144cff745954301f5f7354e500067c755823102efa601815324df57610610004ff72d81310067d52d9510006be6319151006bc6458d5102ede2058c100fe7f52d91500067d20d954307d7c7550e10006bc2159250004fd7650e1000cfe7258743014fe73592100067d21d9543005bf7150d40004fd74d9531026bd3199010007b461d05400267d5158251006bf73d9110007b754d8540014fc73594100fe7f525964002cff73d953002edc1058c10026f81058231005dd73905300067d5259740115bc7550740004ff725834102edc3058c10026f660d061000cfe72d953104cfd70d8d4004ebc701911004ebe6455010004f
  | 2 => 0x24fb440106100e67f50d954000cfc7258740004fd7259610016de63d0c1000cfe72597413667c64545500267f105964102cfd71d95100057d7590640015de7394530004fd761065002ebe3099250004fd76d0550194fe761913102ede4058c400067c21d954037e7f6254550026bf7199010014fe76d8d41004ff72d85430067d6219543005f77158d40004fd72d95411e67c6550d100467c5459410014fc73d913016e7f5259441006bf4358241004ff7654c41004fe7654540026f7731854002eed305881002edf2058c1002edd3059230436bc3119151245bd71d0e410067f70d954302cfc7059610005df7354130004fc7650d1001cff7654610006bd73d9110007b5431061027f3d6494650004fd76d0d10004ff7650e5124ebf64185400067d621951004ebf721915104cfc745951001e7e6555010014fe735864003edc5358c100079d43d0130004fd76d0e50004fe765511019e7c525964101f7a6094650005bc745855024ebe101911004cfc76d0d51006ec545881045ebd54d91532af3d6454e5004ede7458c40015dc73501300077552d8540005df7354530006dc5258c40007b743d8540007d7614c530016dc634c510007b87050540014fc7359110006be725925022ef562d041002cfe7610650004fd7654e400067d525824102dfa709513010edf3058f400a57c755913025ebc6590640014fe73d91511c75c6354d51006dd634c65002cfc7654e100067f755921004ebc73990100067f6354550004ff70592310f6bd43d91300057d759063000cfe72586542f5bf725054002ede3058c400067f52d8d410067f7559510006bd3299250006dc7458c1001cfc755913017ef63158743006df4258e5000cfc72d8d51406bc10d9151006f7541854033e7f70d954030f3f5250d401467c5058e51004fd70d9153006be20d915102cfc70d9110004ff755834104cfc76d0d500067d73d9510006dd7458e502b75d6395250004fd74d815102ebc2059010004fe764c54000cfe72d9150006bd325901001f5f7354d51006bc73d9151026bc2199010015de7310530016be6350d400257c719515102cff705863000cfe72583410063f5259010006bf7359010006bc30d9151026dc4158c1004ebf4358041006f543d85401e67f52d954321e7d53d954304ebc73191100267f7159641006dc7558c1001c7e76d9543006df5358c100067d52580410fcff745954001e7e6095250005df7150d300057f7550e51006df5158c4020dde739815404cfc764c740004fd7258d1002cbc7650540006bf6499150005bf74545400267c515971001cfc75586402ddfb7059530296f442d854036ebd6250f40006bc54d913119f3f52d915108dfb7058530006dd634c3100067f20d951025ebe10d9110006bf21d9151006bf32191510467f52594100067d655
  | 3 => 0xe7510550024fe76d8553004f7715911004dbe719044002cfc705963124eb640185403a57d729465001cfc75582410067d52d81430e6bf54595400067e42d954300cfe72d915302cfc7058e500067d52d954102ebe7059250006bf20d9151024fc7654f10004fd71d814301e7c659513019ebc53d91511467f5258e51006f672d854002cfc7654c4004ebe645061004cff76d065000cfc725874304ebc6490530006bc63d91510067f52d854019e7c65905402ef3d525054002cfc76d05102867e71d95100066e7558810006de2158c400667f52586500067d52d8550025f47155010024fe76d0e51006f76198543006dc2158e503d73f5250c412cfda2050d3004cfc74594410e67e7619540025f47155141006bf70d91510067c631954000cfc72d953104ebd761064002dbe7050d401167c515974002cfc715971004cfc74d954032f7840195400067c72d951001e7e6554f4016ebd501915104cbe76d91100667f54d951001e7e6594740006bc6418151026f66194440116bf5199250004bf7458d100ddbd73d0d400067f32594100067d5258251004fd75d9110006bc725925002cfc70592510a6dd5458e50156dd53d8d51225f576d061025ebc20d9110027b564d0410014fe735911001f7a6054e5021e7f73d954301cfe7558c41006bd32d91100067e32d954004ebe64506301e67c6550d400057d75105500067e4359641004ff7159110007b742185400063f52d9110024fd73d9531006dd634c64033e7f41d9540004fd76546400067d5258e50006bf6490530226f764d061004dbc7454740026dc3158f102867d6194650006bd755901004ef8405834101d7e7590550004fc7654d102cf5f5250d3002cfe76d0650004fd75d8143406be71d9151004ff7259130024fc76952311aedf3058f41004fd768c550006f6531854004ebe6150e412b77a7095250004be76191100e57e759854004f9f7350e4123ebe41591314267f629515102cfc76506300067d53586500067f52d91310a75f535453019ebf53d91510067d5259530006be715925004dbf7650c41004fd76945400067e42594100e5be755054017cff735913101cfe75d8540014fc73d815104cfc76d055002ebe509901024eb6101911021e7d30d9543004ff7258d101e67e65d954302ede7058e500067c6558143116bc5299250026f57018540005fb705524004ede4358343006be72d915104ebf6250c4102ebe7099010005ed729854302cfc764c5100067d72d951002edf5058e500067d659523001cfd74d8d5419ebd52d915101cfe7559110236f74318540005fb705051043e7f651915302e7d305941001c7c7558343026f762d0410004ff72d8d51006be3299010006f62158630026be415923101cfc7558f40006776518540024fc7158254004ff7559130166df3058c41
  | 4 => 0x881002cfe768c6500067f525864002ebe405901002cfc7058e41014fe73d95400067f655454001e7e6054e5002ebc305925002ebe20592500067e62d9540004fd72d8d40006bf5459230004ff755824102ebc1059250006f563d8540006df6350d4002dde7050d3000cfc72d911021e5e6395250004fd72d854024ebf62106400067f31d951021e7e639515102edf1058c40006bc6458d1002cfe70d95100073c7550d4001e7e6094650006f62158d10005bc745453102eef40588100047f75583431867c53d954102ebf105901002dbd74d954002cfc705921004ef44158440005fb705453004ebf6250f401eeee62d0c1002e7c70594102877b10d95101e5dd739915300cfe7259531004fd7259640005bf74545411b5f7715915117ede43d8d41006bd201915102cfe7690540006bd71d911002ede5058e5002cfe768c44002cfd70586300067f5259210006f5215804102dbc7650d4004cff76d0e50236f576d04100073c65d0d40226f420d8540026f62158231026f57218540006be75d9110006bf7459510004ff7059251006f76198530014fc735944100cfc7259251406bf6498554026f66118540006be219925021e7c31d954301c7c755823100cfc7258e10006bf7458d10004fe7654d10026be3199010006bc525901000cfc7258c4100cfe7259230076df3258e100057d72195430067d5258e41026dc5158c100073f6454d51007b46150540006dd63d0650024fc7458341004fe7650d510e73e74d95402cf9d4250d3000cfe72d8d410057f75591303667e745964102cfc7650e1001e7e6555241004fd7695110006fb6098143006bf42d9131006bd4259210004fd76906500267c3159410026f7721854001cfe7558743246bf64d0f1002e7c505963002ebe30590100047f7558d1004cfe74d8553024fc7159543014ff764c310006df5458c1038dfb7058d50004ff7559210004ff76551300063d521915104ede5458c40004fd7654630004ff7359741004fd768c6400067f72d9540016df604c530006bf6458d1001cfc75d8141026bd51990100067752d854033f7b40d9540024fc7159410006de3258e50004ff765521019ebc54596410067d5258e400067c7558343006bf645815104ebe64d031004dbc7454e410067d52583410267e2159641006bf21592501457c75591312b67c70d95400667c545865002ebf1099250026ec315881004dbc744c64001cff7654130004ff7158e540073f7454550014fe7358740006bd648c65000cfe725863002cfc7058e10006bd3219110026bf515901024ebc2019110014fe76d8d502cf9f4250d300067f659911004ebf7299010004fd725874001cfc75d854304edf7458c40006df7258e5002cfc70592300067f7559110014fc73584400063f521911000cfc7259530016de6350e5001d7
  | 5 => 0x2cfc7058c40005ef725814302edd2058c400067c70d954302ebd70990100267d2159641006f775d8540006be4359010024fe7159410004fd764c64004dbf72d05400e6bd5259250006dd2158c40004ff765501000cfe72d951000cfc7258e40006bd641915302e9d4058c4025ebe30d91100067d52d85430067d42d9543006bf51191101267d535963004edf7358e540075c7550d300b67f525963000cfe7259540024fe769531043e7f641954304ebf7399250006bd62d9151004ff70595310067d52d8d5119ebc75d9151026be2159010006bc52d91100267d10596410a6dd5158e5002ebd1099250004ff7258c10024fc765524102cfc7650650006f5651854019fb751d9151027d431545310067d5258f10006dd63d0c1002dbc7050f4019f3f50d91510067c72d954302edd305863016ebf50191510057d75d065021e7c43d95430047f75580410057f7558540406bc51d915101cfc7558f410067f75583433673c649515100cfe72d9543006de3258e4104e7f755974102ebc5099250004ff764c54002edd1058c40004fd72d855401f767194650004fd73d95400067f52d8d1004ebd7319110004fd74d8d104567f40d954325ebf6190640026df7158c10025f674d0410024ff769464001e7f6154d511aedf3158f41005dd7395130004ff7259640245bd76d0e41005dd731814123f3e6550e411aebf7650c410067d425941023dbf7150c4102cfd75d8d5007f3f5495210014fc7358650005df7354531006bd42d9131026bf21990100e6bd515925019e7c5059641006ed735881001d7e758c55002ebf505925002ef6105865004dbc75d0e41004fd75d854328ef562106100067d65552400057f7550d500057d73952502b57d70952500057d72d95400067c7558041006bf51d9110004ff72d81530067e53d951000cfc72595412767f6119510024fe7158e51006bf42592100067d52595400067d52d8d5023f9d6350e4138e7f51d8153004ff7259410004ff735825402dfa709054004ef441587430067c43594101979f3050e4104cfc7654f41006f6215864002cfc70586540067f658c540006df7358d10004ff7558c4102e7d7059410004fd7259630005f970d061005cff7358d10014fc745834316e7f505944102e7f4059410006bd645065004ebf719925004ebc641055004edf4358f400067f7558d100fd7c7550e40006f52158630014fc765453101d7f715455001cff765414002edc5058c40004ff72d8d41006be73d9110004ff75592310957c7550f1000774651854027f5d6394650024fc7158e400067c63d9510026de7158c10006ec43588102af5d6354e50006f532d8540026fb7058231006f73018540026f66118543196de639065024ebf6410630004ff74597100067f65585400067f65d0d101e67e761954302eed505
  | 6 => 0xd5299010227b540d04102d5dd7250d30004fd76506302b67c30d954001d7e7590650256bf1019110014fe74597430067f30d951000cfc7259110006bf7459130095fb705855001e7e6554340006be325925002e7f7059410024fe7655310005f97010630004ff7655231024fc7695310014ff764c610006df7158e50226f640d854004ebd739925004fb77150540006f773d8540005f77150310006bf64d0d5104ebd7199250025f770106102b67c60951512b67e20d9540006f761d05500067e63d95400073d42d9540005dd73981542b67c10d9540004fd7258f41007b543d8540004ff7655110315bd7250d400057d7095151004ff76552300267d3159410006f4631854002edc7058c400b67c5459630006bf31d91510c6dc3258c40006bd2199250024fd75d91513be7d629525001cfe755834302eef505881004f9c43551430067f655054004ebe7019110006bc7359250014fe7358254004fd74d8153004fd7258e400057e76195400067e72d954002e7d5058650006be43d911002efa601815102ebf20592503edbf7250e41006f521d8543006bd72d9151024fc71d9510005f771550100047f72d954004dbc7454741006bc64981510067c325964102df87050d400067e4259641006f452d85400a67e65d953002cfe76552100067f65181430debf435923002ebd209925004cfc745825421e7d31d9543006be3219151024ff768c44000cfe7258251014fc7359210006be62d91101867f54d954104e7c5459741005f77155141006bf75d9110004fd74d8131006bf64d05314567f42d9543004fd76d0c10006bc5219110405bf7455241227b564d061004cff765061004fb441551410e6bf54d9540226f630d854036f3d5250f4004cfc7458e500067f425941021e7f32d9543014fc73582410067c73d951001cfe76d9530006f65218540005bf7454140006bd43580410067d6555010006bc64d81510e5be75d0540016bc63d0d40004fd725911004cfc7458654004ff725823102ebc3099010006ef7458810024fe7650f1001c7e76d954002efa6018131004fd764c74001e7c6555141006bd70d9151006bd6495010004fe769513027f7410d9510004ff70597430057f75581410067d525923021e7e6395250006bd641065004ede4258c400073c7550c4124ebe301911001c7e76d95100067f659854302ebe20990100067f6595130024fc7654e412b67c639525002ebc1099010006ed545881004ebf7299250026ed31588102573e759044000cfc7259130006f751d854025ebc70d91100067f21d9540024fe7654f1003ede5358c10006dd638c650055ec7258d10004fd73d815440e7f6254d51026bd7199010006ed74588100067d70d9510266bf10d91100067d2059641004fd70d855402cfc7059543436bc211915104ebf7019151
  | 7 => 0xf40256be21191101867f525925104ef77158743025f576d0410006bd64d0310024fc715824100cfe72584402bfd9204c5300e6bf545825433e7c41d95400067f52d8d40006dc7258c4002cfc7059640006dd7158e50005bd7498151026ef415881004edc5458c40004ff7158c400067c71d9543006f621d854001c7c75591100e67f53d954004edc4358e54004ff71597430073f42d95400ce7f51594400063d74d9540004fe768c55004cff73d954304ebd759901002ebf20990100067c71d954004cfc7459631004fd768c44002ebf745925001cfe7558e41026f573185400067d5259541014fe73d915004dbf7350e410067c21d9543006bf7459531026f67518540006bc5399010006f675d854004cfe74d9540007b75418540004ff7650f1002ede2058e5020ede63d8d54006df5258c4002cfc7058c10004fd73d9541004ff7558f1002edc1058e500067d52d954001cfc75d853004cbc7459710024fc768c55002edf7058c10006bf6410550004ff71596301467f52595310167e6354d51006f643d854038efa50d8153006dd6354c40266be21d91100267c2159410116bf5299250005f9709064002cfc7059541116bd5399250024fd74d9541026fb105824102df8705061024ef44018540006bd6419150006dd6350650025f47154310116be5199250005f4715915001cfc7559010004ff72592510657c7550d1004e7c5459441006bf64951100067d5258e10115be7550f4002cfd7058c10024fc76d0110004ff7158f40005bc745815102ebd4058640004fd71d9540026fb1058041006bd435824102cfc7058f4101cff7655143026de3158e4104ebc4058041006df7359130004fd7650f10006bd75d9110006bd64d061004dbf71d0e41004fc7654d4100cfc7258c4000cfe72d8d54006df7458c1019ebe53d9151227b440d854001cff7654110004ff7058743004fd72d9130006bd42d8d400067c6558d10006bc32992500e5bc7550540024ff73d913102ebc705925004e9c4158c403ddbd7250c41006de32d8d5102ebd105901001cfe7558c10004ff7359310006de7158c40014fe76545311c4fd7654531006f6215865001d7e75d0650006f54318540024fc764c110005bf7454d40006dd634c61016ebe5019151006bf539901020e7f53597430dcff735913001e7c65945300067c6558d400067f525874002cfc7654e4002ebc5059010006bd64191301adf77159131014fc73d854001cfe7559131016de6350c1002cfc764c650004ff71594401e67f50d954302ebd4058c40004fc765454019e7f52596410067d6554e41006f52158d1001c7c7559210005bf745855325dbd7090440006fb705913000cfe725804101cfc7558231004ff7458e500067d6554741006dd6394440006df2158e500067d525974304ebe6419151006b
  | 8 => 0x6bd6390640004fd7259740024fc7650f10006bd6454c1024fb64010610004fd71d915024ebc50191100067d62d95100073c6454d5104ebf71191512ae7c50d815301cfe76d954302cfc7059441006bd4258c4139e7d62946500c6df3258c40014fe73597411367d53d95300067f6594530026de3158f101deee6250c10024fe71d8d100e53c7550d400067c65181430b73f5495230006f771592100073f52d9110006bf30d915100cfe72d815125dbf709044000cfc7258343004ff725901004cff76d0e51006dd63106500067d70d95430067d52d91511e57f72195430167e6354e5000cfe72d81410a6de7558e50005bf7454c4102edd4058e50005bf7458d100073c6550d40006bf72592500057f7550e500073f7550e41016bc63d0e410067f5259310236f44218540007bb7050d4004ebf71191100079f6350d400067d655464002ddc7650d30115bc7550f403ccff7159531006bc72d911004ebe6419130006be6219110004ff7558f41005f47158154007b77150e41004fd725923104ebe64d0e1031f3d52d0d4004ebc7599250026fb1058251004fd76506500067f20d9540004fd7654c4002edc3058e40134ff755953002ebd309925002cfe761063004ebf759901001cfe7558440006df7158c4002e7e5059410004ff7258e40026f410580411857c7558d4125fba7090640024ff768c650004fd7258c4002cfe70596300267e5159641006bc325901004cfc7458f10014fe7358341186bd545925100cfe72d8d101ddec72581430067c7259641004ff7259641005be76191104567f41d95430267f41594100077b7054e500e67c53d954000cfe72d91300e6be75592502473d65d0e4116f3f52191510e6bc5159250006e562d041002ebd205901024fb610191103ae7d6254e504373e5119151027b674d041002cfe70d954104ebc4158c4002cff7358c40024ff76506400067c7559131006bf649913002eee505881025ebc50d9110296f654d854007ef551d855004ebe729925002e7e7059410436be311915123ebf6450f1004ef8405825401d7c7550650006f521586400165e6354e500067e52d9510004ff7458e51004ff715953002e7e5059640026f46190540186f65158654006bf42d8d4023fb62150c41024fc7158c10006be4259010006b62119110006f76518540266bd611064002e7f50586503667c74596413f73f52d0e4143f5c431954302cfc7058e400067e3259410006b45418540237f04018540026bd215901001f3e7495250004fe761053025fb610d911002cfe76d0630225f770d04100057d7590530004ff7258e51227f270d061004ebc649511000cfc7258640005bf735054024ef76410610004fd7258640006dd3258c41004fc7650d50004ff7259310004fd761055016ebd51191510067e53d9541016be635
  | 9 => 0xf6450d30004fe769513102cfe76d0e1000cfc72d9543006be2019151436bc1019151004fd7258c100067c74594100063c65d91100267e3159410024fc71596312b67f651815401cfc7558343016de634c3103d7b52150c4102fd8304c310005df744c530025f47154110015df7450d300057f7550d51006fb6098151146dd5358e5100cfe72d815417edf3059131126dc5359530005f471581432dcff7059530006bc5459010005f571d0310004fd72d8d4102cfc7650e50004ff725911002dbc70d05400067d525974100775521854008cff7058d100a67c54d95300079c6450d30004ff7458630014fe73d9130014fc73d8554026ee315881004fb6711064004dbc74545400dede43d8d40007db7050d3004cfd73d8543006bc32d91100067f5258f40006bd20191100067e71d9543257b8101911002cfd7059410006f665d85400067d5259543004fd70d8d412b67f74d9540006bd211911004ebc701915104ebf4258c41026ed5158810006df5358e402e6bd6290440026bc51990100a6df5359530226f76118141014fc73d9540024ff76946300267d7159410006f621d8d100067f6550d100067e73594100057d73951512ae7c6054d51014fe76d053120ede53d8d5427e7f65181510067e6219510006bd64d0e500e57e759054041e7f52d8553004ff7655310004fd72d81310067d525925001cfe75d81430047f72d9510136dc7558e5004cff76953100267c315964102cff70590100067d525863009dec725853019e3f545964127e7c40d9510006bf31592500c6dc3158c40024fc7458f4123fb47150e41006be42d911004ebf4058f410073f5219110026f670185403857f725455016ebf5459441004ff7458251006f52158650026f67218540006bf2119151004fd75d8d40246bc41d8d41004ff7558630006dd7258e5000cfc7259531006bf32992500a67f52d95300257c7654d5102edf2058e50004fe76d0d100057f7558d1001e7c6554541004ef7259130006de5258c1002cfc705941002dfa70106300973f549531001d7c7550e51006ee7458810024fe71d8d40006f572d8540006de7258c103673c75191510067d525825404dbf7650f40006bf52590100057d7598540014fc76d0531005f771501100067f7259641006bd20d91100079d435013001f3e74951510067d5258e540a55c7550d30267b810d91100067f5258c41007b7431854004cfd73d8143006dc7258e503367f6419540006bd21d9110006bf64d8d10226f450d8540006bf74591310067c74d9510014fe735865401cfe755863001cff765434026e7f60195100075f6354d51005fb7050e40004ef7258d1004ebf7219110006dd7458c1002edf7358c40026ec7158810004ff72d8550006bd1019110006dd7558c400957c7550310006bf645053102cfc7654640
  | 10 => 0x915101e7e6554741004fd7258341006f761945401aef631d85430057d7394650006bf6450d510067d525823101cfe7558f1024ef42018540006f432d85400067465d8540006775218540277761019510006bf3259010004ff7259531004fd7258743004ff7259740004ff7158e40014fe7650531017d7714c53004ebd721915116ebd521915104ebe64d0c10004ff7558d10004ff72582510e6be535925004cfd745944002e7c5059440016de6354c400073f65d05400067d52594410e57c7558d40024fd7158c10026de4158c10004fd76952310267f2159410006f52158231006b54218540006bc6454d10006bc7459510004ff7358041024fe71d8d5002ebf7099250004fd76d0530026be5159010004fd72590100067c72d9540014fe73d951016fb751191510657e75991102857c7154e5005edc32d8d1002cfc705865000cfe72595430e6bf535925002ebe70992500057f72d95430067d425964124fb4641061002cff7358c10026bf31990100057d759055005ef53158630016be6350c410065d5258c40015de73d0530026dd3158231225f570d0410004fd76552103657f7295151016de6350e40126de63d8d50004ff7259541006ee755881000cfc72d8530066f6515865001e7c659511000cfc725961004dbe71906401d6de6394440026ef7158810005dd739453004cfe74d815304edc4358c400066d755881004edf7358f40016bc6350d400063c6519110006b521191100067e70d9543006bf52d9110004ff72d8d5004dbf765074000cfc725974004dbc7454541004ff72d915138e7f52d8153014ff7650e410debd4359230004ff72d9130006be62d915104cfc74586301467f51d9531005f77159150004fd725865404e7e545944002edd5058c40006bd645061004cfc7654f4000cfe72d8d4001cfc7558e40115fb70591500079d4310530007d8704c530004ff73596100f6dc5358e40006ef7258d1002cfe70d9531017db6050d30016de6350e410e67f54d9540006bf64d8d513373c401954004ef840583430067f52d8131006bc3219110006ef725913002edf7358e102b67f65952100e67c51d9540014fe735944021e7e32d9543015dc735413002cfe7695230004fd7258251006bc3019151266be51d9110006bc62d9151024ff768c64002cfe769463002edc4058c10006f561185300067c65d8540006f642d8540096fa50d8151006dd6350c1019ebe52d9151006f521d8540006bc75590100057f75585433667f4059641006bc31992500067f5258f41406bf75d915102edf4058c40004ff73597402867e41d9510004ff7650d5001e7c6554130004fd72d91103473f52106400067d7359410024fc715901021e7e31d954304ebc649055002cfe765523002ebd30590100167c6354e50006f520d85400e6bc53592500079
  | 11 => 0x24fc7159641004ff7558343406bc71d9151004fd7258231004ff764c650006f553d8540226f660d041002cfc7459740005f7715814301cff765524000cfe72594410067d52d915302e7e20594100063f64951512673e7590640026f6615064000777615455004ebc7519110004ff7258f4104ebd7299010006be5399010004ff7358640004fe7690550006bf32d9110004fd76d0e51024fc7650e5104fb741552410077765d854000cfe725925004ebf7019110026f661185544575f43d95430067f31d954004cff76d06302b73e649525000cec725913002cfe70d915102cfc764c44004fb84050d40006dc4258c10007787054550004ff7258c410067d5258c40227b740d0610006f763d8540006be65191100257c7154d5104edd5458c40006f521d8d1022f7552d04100067f65585430067e53d95400067f21d954321e7c30d954302cfc76950100673f54951100067e20d9543004ff7650d1001cfc7558630004fd74d853004cfc74582310057f7550c1004cfe76d91310073c7454550005f970d051020edf30d8d5400cfe7259440006bd6219151006f473d854016ebc53191510067d5258640006f92058041004fc765513102e7c10594102767f6518550025f671d031002ebc40592300067d7059641004fd71d8153005bf7454440006ec7358810005bf745853002cfe7058e5002ebf3059250025f4714c31004cfe74594400267d31596410057f7550d4000cfc72d85530657e76d95100267d415941002cff75594400267d5158e5104cfe74d815102e7c30594100067d655524100cfc72d81430657c755011033e7f43d95400067d5259640004ff7558c100067c725941001cfc75d8d10006dd634c440006b74218540026bc315901004edd4258c4002cff705941027e7e10d9510006bf7259010004fd72582540067d5258654024fc76d0f1002cfc76545100e57f721954002cfc705864002e7d40594103667f425964119f3f53d9151005bf745953104edf4258c400147f7654e50026f6611855002cfe70d8554006f7611055002eec10588100067d52d915004f9c4350d40004ff755931004ebe6450310006bf644c11002eec3058810006bc631915104cbc7458d100063d52992500067c42d95100e5be75d0d40004fd7650e51006bf52191100067d5258d1004ebe739925004ebd73191510067d5259130006be65d91100067d5258343006bc64d8d10004fd7258041006bf6454d10026ed41588100a6dc5158e50006bc54d9110024f4715901002eed4058810014fe73d854002ef61058440004ff745953123dbf7150e4104cfc745953004ebc72992500073d52d9151256be5119110004fd765513004ebc711915101cfd73d9153004fd725931000cfc72d8151024fc7159231006f752d85400a6df5458e50006f5321854016ebf531
  | 12 => 0xc71596411867e65d9541266bc31d911016d3c7550c4107e7f515961002eef705881004ebe6450e10026bc61d054002e7e5059630004ff7258740006be644c6500067f6598540014fe735951002ebc709925001cfe76d954001cfe76d951027e7c20d95100067d52d8d4104f9d63904400067f7559541026e44158810004fe76d0550006bf201915104ebe719925002ebf74592102573d7590440004ff72d8d54227b640d8540004ff7258e5002d7c7054550006dc2158c4024dbd701064000cfe72596400067d32d95104567c41d954300cfc7258f41005f97010530006ec725913021e7f53d9543026f6731854001d7c7550d500967f52d815119ebd71d915102ebf30990100067c659854301c7c75580410067f5259010004fd768c740006fb7059110004ff725804130f3d5250d40014fe7359610027f260d0410024fc7159130006bc62d911004ebf75992500267c2159641024ff715901002cfe7059410026bc71590100057f7558d40006f732d85400267c4159410004ff72d91500067c62d95430dedc32d8d40026fb705804127e7f65985502e73f529044023ebe6150c41004ff72d853002dbc7050d4004cfc769513101e7c659513104cff76d0c10006bf54d91310063d525901023f3d6550e41006f771591310467f5359410006ef5358810006bc42d9151024ff769065002ebf5099250014fc74587430067d52d95432c5dd724c530004fd765513104ebc721915117ede63d8d41006bf745954104ebe6090640006dc7258c10005f571d011001cfc7559231006bc43590100067f52d8530004fd7694640004fd72d8d50006be73592503e73f5250e41005df7350531296f454d8540006bf3219110026ec41588100047e7619510004fd74d9530007db704c5300067d5259410004ff7558f40006bc7458d1002cfc76952302a77752d061004cbc7459531027d663d041002cfc705944004ebf60d0540006bf745971002cfc7650c10005f77150d4102ebd505901026f78101951044ebf43d915302ebf4058440006dd63d0e5019e7f50596410067e7259410005f77150c1002edc3058e10004fd7650e5004cfc7458650004fd7259230136df3158e5013dec725813101cfe75d813121e5e5358e54006df634c110004fd75d91300e6bd7559250006bc644c1100057f755853001d7c758c65004ebe721911000cfc72d8d5419ebf71d91510067f655413004edc6450d3000cfc725913102cfe70d9131006f561185530267c615455002ebf7459230004fe764c550006f96018151026ee715881001e7e65545300067c75592100067f52584400067c65d8d10074ff7158d10006f7715951004cfc765474001cfc7558e100047d72d951002ebf70590101f67e65d0c10005f77158154005f7715013004ebf4258f40026fb7058251004ff7558440
  | 13 => 0xd40006be529901004ebc64d011002e7f75594100067f52d91103d73d5250c4101cfe75592100067f52d8141006bd4258f402af787054e50027e662d04100067c65d8d4001cfc75d9130024fe71d954302ebf5059010015de73d05310063d52d91100067e7459410006dd7258c4002edf5058c40004ff7458d10076dc5358e100067f6558d1000cfc725863001cfc75592100a67f50d9530006bd72d9110004fd7258343004ff7258650026bc6150740004fd73d854001f7b6054550004ff7159230004fd70d8d51025f47150c1021e7f74d9543025f671d0110005f9709523004fbb60d054021f5f30d954302cfe7058c1000cfc7259210005be7418131026f66154440025f4715031004ebe75191514073c51d9151006f77158d10004ff7058e5124ef761191100267e6154550006de3258c4025ebf62906400067e74d95102cf5d5250d300067d6595231006bd6450e50116fa50d8154006bf5459210024ff7358c41004fd73d915004e7c545944001e7c6555143014fc73596100057d7590650006f5611855427e7f6194650004ff7058e41004fe761911002ede5058c40004fd73d91510067d525865025ebf6490630004ff705911002edc2058c10006bc43d911025dbd7090640025f47150d41006dd3258c10006fb609813102cfe7654c1024ef640185400fe7c5359640006bf645411000cfc72593100065f5258c10004fd72d8530006f431d85403677571951510267f41596410067f325964101e7c6595210005bd74945400067d6554630016bc7650d4021f3e43d9543026bd31590100e5be7550d4002e7f205941000cfc7258e5102e7f7559640004ff725953024dbc7050c4102cfc7655210006df5358e10116bc54d8154007b62119110094ff70595101467c50d95310047f7559131004fd75d8d41015dc73505310067f20d9543005bf7454610436bc5119151136de5358e50006bd6455010026f62158c41026b461d0540006bf64d0110004ff72d954004dbe74d9540006bf4259010006bd725901001e7c6554d10024f47159130015dc73551430267c515944121e7e73d954304edf4158c400f6df3158e40024fe71d9530256bc3119110006f4521854001e7c659454002cfe7650e10006bc6219110226f762d061021e7e5358e540657c75591100067d74d9510007b5431854002cfc7650510006bc21992501e57e759814304cfe74d8d50005be749815302cfc705913101cfe7558c4002cfe7690650006bf649913102cdc764c53002cfc70d951000cfc7258e41006bd42590100067e7059641004fd70d954302df87050640016bc6350e410467c5359410007b621d91102ae7f6554e10026b4715901002cfe769501002ede1058c1002df87055140024fe71d814316e7f535944124ef63018540006ec535881002ddc7050d300267
  | 14 => 0x267e3159641014fc735951002dfa7010530005f970105500e5bc7550d403673c545474021e7d74d9543006f762d854001e7c6554d400267c51594100077b70545500e6bd74d9540007b521d9110005bd7418131004f77159130236f6541854016f3f501915101e7e655524004ebe721915127e7e30d951004cff769521000cfc72d854304ebe6450c10027d563d041001e7e6595310004bf745951004cfc765474121e7c639515121ede6395010196bf43d9131006bf645511016ebe531915102ddc704c53004dbe749474004ef77158654005bf7458d5104ebe64191530073c7550e4102cfe70d954316dbe7550c41026bc4159251025f471552100467f5459410016bc6350f40006dd6354c41004ff735911000cfc7259250006bc20d91513b57d7254e500267d715964133d7f75d0e500057f72d9510006bd32d915100cfc7259540026ec5158810297f340d85402af3e6454e500667f51d9510006bd649065000cfe72d9530006bf3119151296f740d85400067f5258c10004ff725974301cfc7559110006f56318540004fd769523025ebf6498540006bf644c510026bc2159010004fd72d91310063d649525024fb44018540004ff7159740006ef545881000cfc7259641026f47318540004fd7654c10006de7558c4002cfc7650540006f5611854304ef74158654026df7358f1004ebc64d0d51006f542d8540005df73501300a73f5495130004fd7258e54025f47155241006bf42d91100a5de7550d30004fd7655310024fc71d8d1004ebc64d053102cfc7654c10004ff735944127f3e6494650005be7498151004fd71d8d4000cfc72d9541004ff715913002ebc4059250005ef7258d10006dc7158e5004efb4058041004ff755804100cfc72d9151004ff735964119cbf74595410063d521911001f77619515104cfc7459410006bd64503100fe7f545964000cfe7258d10006f76154140004ff72d8540004ff7059541297b45410610014fe73d855425fb66190640004fd7258e5102dbc70d0d400a67c654c11000cfe7259530004ff72596100667f535865004ebd7399010005fb705054004cff7695110026be615074002edf7058e5001cfe75d81410a57c75501300067d52d854001d7e74952500067f7359641004fd72d8d5110dfb705913002ef77158630006f47159130004fd76501100067d5258e51006f621d8131024fe715963105ef6315863004cfe76d9110006be32992500047f72d954302ebe5099250006bc6454110006f462d85400073f655054002cfc7059630024fd715941002df87050510006f62158f41006de7258e500067f75595400ce7f5259440006bf74595403667c4359641014fe7359410006f64318540024fe7695231305bd72d0540006bd42d9110004be76d0540025f4714c110005f4715954002dbe70d
  | 15 => 0xe705923004ebd7119110006f6215844002cfe70d8d5102cfd70590100073c65191100067f5258743024fd75d8d510067d71d951002e7c5059610014fc73593100a5dc7550d300067d52d8d10006bf64d0130185f571991510067e43d951000cfe7258e10014fc73d915004cff76952304157d7254d5100cfe7259130006dc5258c10006ef43588103edbd7250e4117dde731814100cfc72594100067e62d9510025f4715011004cfe74d85300267f215964102cfe76d8153014fe7650130024fc7690530024fd7159010026ef315881004cfe74d81310069d6390440006df2158c404667e54d8554014fc765413000cfe72d95403657f75d0d510067f74d95101e67f54d9543004ff7654c100a6dd5258e50005bd73d0540006bf501911002cfc76544400defa305834304cfc76d0530004fd769055005efa305823101cfe7558f400067c6219510014fe7359441005bd744c74002ede3058c10004ff7258f40005bd7494740004fd7654740004fd75d8d10014fe7358041004ff7654d10196df3058e4120edc6358d5402ebe5059010004ff7158254006bc645815135dbd725074004dbe748c740006f673d854004ebc64106300067f62d9543026bc41593100067f6550d4004cfd71d8d41006df634c51004cfc7654340006df7359530014fc7359640004fd74d8550006f562d85400a6de5258e50005f7714c31019e3e75d915104ebf6050540004ff725963100cfc7258254004fd72d9530007b521191101c6de53d8d510067e535964002cfc7655240006dd6354440006be648c650026df5158c100067f73d954002cfc764c64004dbe748c5403373e401954004ebf405874302eec705881002cfe76d0c101aedc3258f4127e7e40d9510004fc7654530006f52158c41004ff7558e40006f554d8540004ff7258e10006f7614c540004ff735964004cfc7695130004fd70d9541004ff764c550005bd748c7402867f10d95100073c65d91104267d6295151004ff7654e40004fd76946301467f52d9531296f742d8540126de53d8d500067d72d95400067c63d95400067d52d913119e3f52d915102cfe76d0e500067f30d9540006f6761854001cfe76d9531006bf50d911000cfe7258343004fd76d0e1001cfe75d8d4004ebc6455110116bd51992500047d7259410004ff7158e5001cff7654531006bc4259250006bc644c5100067e52d9540014fe73d8154026bf715901004ebe7019151016de634c4400067f5259110004ff7459530296f443d8540027b641547410667c52d95101e67c51d9543006be32590101c6df31d8d51006dd638c44004ebe64d065000cfe72d81430067d6595310004fc7650530006fb70595100067d525921001cfe7559230016de6350e100047d7259641006bd64d0e10004ff7650e10005bf7458131024fc7459741
  | 16 => 0x954002cbd74d954002cff745901001cfc7558c1019ebc52d915101cfe755931004cfe76d9153014ff764c110004ff7259210006be321911002ebd7099250006ee535881004ebc64d051001d7c7550d5104ebe6450650005bf7454630004ff72d911028f77521061004cfe76d913000cfe725865019ebf545964104e7e5459740004fc764c5400063f65191100067f6595110004fd761053004ebe75990100267c1059641024fc7694540004ff72d953032f7b4019540005dd73d0530006be32d9110024fc7690550006f64218540014fe76d8d54004ff755864025ebe50d9110006dd6350e502ad7f7054e5000cfc7258341006f7715954102ebe40592300267d41596410a67f51595300067f6590540006bc65d911000cfe725941002ef77158440014fe7359010014fe735971002edc4058e500267f7559441005f77159540006fb609814103ede4358c100067c621954004ebd72992500f4fe7619130005fb705514001e7c6554110026bd515901000cfc7259741014ff7650e40004fd7654e41025f674d0610026bc615054028fb542106100067f52d91301167c65d0110014fe73596410067e2059641006f52018540216ee629501004ebc5459740006bf3019151126df30d8d50026b46150540007762119510005bc7458d100067c305964102edc1058c401167f52d815419ebf51d91510067552d8540004fe7650d5002edc3058c40347b5211064004ebc64d01302b67c40d9540014fe73d954144dbf7459543006bf64d051004efb4058341024fc715825133f7840d954001cfe75586402b67f64952500067f5259131006df73595430057d75905400067d525963032e7f601954004edd4158c401567f5259631256bc21191100067e53594101267f535963002edd4058c40166df3258c41006b564d04100e63e74d9540006f7715913004cff7695130005f77155241006f665185401c67d5359631004fd7259541006bf2199250014fe7654130024fc765523121e7f43d9543006f521d81312867e21d9510004fd73d951017cfd7650531006bf6490550006bf7650740247b441d0c1041ef651d8553004fe76d0d50005dd7310530006f52158f4102cfc765461024ef4501854001e7c6554e1002d7e70545500063f65d911002cfc7058630004fd764c650004fc7654d400e73f54d954002ede4058c10024ff7610630014fc73582541e67e6550c1021e7f31d9543004ff72d9510006fb70595301467c54d95310067d65d0c1004f9f7350f4004efb705834302efa601815404fbb605054002ef410586301467c6559531005dd73d01300067f5259231004ff725864002cfe70d8d10004ff7458f100067f7559531004ff735865002edf1058c10065f97098550266bc21d9110006f750d85403573f525074004cfc76d0d100267f315941002cf
  | 17 => 0x266bd619064002cfc7695210296f564d06100967f52597100047f75591100067d52d8d40014fd70d9530007752119510064fd7654110227b540d0610026f461d0550246be41d8d41004fd7695130004ff7159640006dc4258e50006f56150640015de735053007e7f5259610116bd52992500077765185400267e5159710014fd74d954320cff735954304edc4158c4002cfc7059250006bf645451002ebd405844002eef3058810004fc76551100067d6554f10006bd64191310057f7054d51196bd43d9131006bc621915102edf3059230006bc64d8d51006bd6390440006df7359131014fe73d9530006dd6350e41004ff764c4400047f755823116ebe521915124ef762106100057e761951002e7f7559440026bf21590100067d7259410004ff7654f100267c4159641024fc7159440006be73d915101cfc7558e41024fc764c31001e7c6555110006bc42d9153014fc73592501c6df30d8d51014fe73d8151006f752185400067f73d951004ebc5458041006f553185401467c654c510026f4619454019e7f535964101e7c6554140006df5358c401867f51d954127e7e70d9510004ff7654d40006ee735881000cfc72d85400267f755971001e7c65551400167c6354d51005bf7454640004ff735925102ebe2099250004ff7258630016de6354c1004cfc745825102cfd75d85500067c651854002dbe70d0540006de5458c1001d7c7550e5004ebc729901000cfe72d9151026de3158e510047d72d954000cfe7259110024fd75d815102cfe768c640006dd5258c4016dbc7550c41004ff725923000cfe7258254006dd6350e40325bd72d0d4021e7c73d9543006f465d85400073f65d0d4027f7561946500067f6219540004ff755874300cfe7258e510e63f5259250004fd76d0d51014fc75d8d50024ff73d953102cfe70d8530297b74210610006de32d8d1024ebe5019110014fe73595400057d72d9543005ef72585300067f71d954304cfc7458c10006ed755881002ebc1099250014fe76d8d510057d72d9510006f43218540406bf10d9151024fe71d9110004fd73d8151026be31590100067d7359641004ff7655131004ff764c7400067e735964104edc7458c401aedf30d85432f5bd7250540004ff75592300067d5258740004fd72d9153006bc7159250296f576d06101567c5459631026dc3158c41027f26010610006f632d8540076df3158e1002efa6018143004ff72d8154004fd72d815102dfa701055001c7c7558d1001f776154d5102ebc3099250005bf7454e4127f7610d951002ede2058c4008edf3058f1004dbf72d0d4004cfc7654140006f7715953133e7c42d9540004fe76945301e57c75585430267f5158251026de2158c1004ebc4158f41004fd73d8554004fd70d855324dbd7610640014fc7358640114ff705
  | 18 => 0xf744c44040e7d6254d510067d52593100057f7550d410067e6219540024ff769444019ebe54d91512ff3f52d0540004fd75d854004cfe768c740006bf73592500063f5299010006f7618c54016f3f5319151004fd74d8d500079d4390530005ef725913004dbf715054002cfe705944019e7c535964104ef441586540047e76195400067e72d9510004fd7258e500067c6558543006f761985540457c7550c10004fd765523101cfd70d8d50007b454d854016ebe65106401e67e6550e4100cfc72d8d10006bd3259250016de634c6500067f7459410006f662d8540006bd32990101857c7550d41004ff74596313f73d52d0e4101d7e7495151006be7619151006de7258c400073d5219151014fe73d81412867f70d951002ebf209925004ebc6450d51004fd72d9510066f55158650006f77159110116bc5399250026f7701854000cfe7258f410067e42d9510256be3119110006f763185400967c545971004ebd751911034f3f529064002ebc2099010005f471501300e57c7550d4004ebc7399250006f761545400067d6219540016de638c4400b67f51d8d5002ede1058e50006f421d8540004fd72586502b75e639525001cfe755823102ebc30590101b67f52d8554004ff72596301b4ff71595410067d70d954002cff7559410024fc76553102bfda204c53000cfc72d8d5002ebe2059010014fe76d0130006f573d8540236f4541854002ebc1059010006bd6419110004ff7654540026dc614c5300067d20d9510004fd7654440014fc73592512877810d951002edd1058c1002ef4105864017edc6358d4101cfd73d8553006bc64545100067d21d95102b67f65991500167f7654e50004fd765523002cfe705901004ebc64d0f10006be43d91510067f65d8d1025ebe6090440026bd715901004cff76950100067465185400067d74d9540024fc761055000cfe725963102ebd70590100067c7558d10004ff765444002edc5058c10004fd7258241006bf7459110004ff7650c1004cfe7458e541467c654c54002dbe7050740267b6211064000cfe72590100067d52592511f67f52d8d540667f5259510004fe76d0d5121e7f30d954302edf2058c40004fe76d0530006be621915100cfc725923004ebe64106500e63c755925004edc4358c41016df6050d30406be21d91512bf5f524c530014fd75d8153005f970106501d67d53d9531116bf5399250266be31d91102857e71952500057970952500c6dc5358c401c6de6354440006f5215844010f9f3050f40006bc651911001e7e655464002e7f305941004ebc7458743014fe765514304cfc7459710006be7619110226f650d8540005f7715521004ebc64505312b67e10d954019d3c7550e41005f7714c11004ebc7319151006bc545824101cfd73d8153004fd72d854300cfe7258c40
  | 19 => 0x9250026f5761061001cfe7558d10024fe71d9150004fd72d9151006dc5158c40005dd73981510e6bf515925002ebc205925002ebf105925033d7f7295250027b664d041019ebc50d9151006b7541854019e7f545964102ebe105925009dec725913001cfe75d8543346bd6210640004fd70d9151004ff7159543004fd7690530004ff725923104cfc7458e510067f6558d4000cfc7258e50004ff7650550004fd71d8154004fd7259440005f9709513002cdd73d953003edc3258c10005bc745855304edf5458c400067e52d9543006bf62191100067d5258f40006f960181430067c6219543004fc7650d51006bd64191510073d5219110016dc6350d4025ebe20d911004cff7650110006bf211911025ebc10d91100e6bc52592500067d6554f4000cfe725823128779709465002edc3058e501e57c755814325ebc30d911004ebf61904400a6dd7558e5001cfe75d853004ebc415844002cfe76952102ae7c505953027f76619465004ebe711915104dbe744c740026bc4159010005bf745451002ebc4059210026f4751854004dbc7454f40375bf7250f4001cfc755874000cfe7258c410067f20596410067f6554d10006df7258c10006bf64501100667f52d95100067e32596410067e52594100067f65d8543004fd72d8d10006fb6098154006bf535901002e7e5059440004fd725844004fba60106401367f53d953024df570106102867c71d951002ebe305925024fb640185403667f655474000cfe72596100067d52d8553014fc73587400067d32d954002cfc76d0e1004cfe74d8d10006bf73d91511b67c65d0510024fe71d9510004fd7654f10006de32d8d404667c54d85542673d7590640006de4258c10005bc745853002df8704c61001cfc755804101cfe75580410067d52d953001e7f6054550066fa50582510067d659474002ebf7459010004fd70d9531006bd5259010026dc3158e511feee6254c10007747154d51004ff735951004cff74594402b67c20d9540004fd7259531064ff75595100257e7195151027b67410610006f73218540006be7359010006bf62d911000cfe72d913104f3c545514002ef77158650026f57518540004fd7259530004ff72d8d40014fc73597413f6bd62d0e4121ede5358e54006f5619444000cfc72d9510024fc765411002edd2058c10004ff7654c4000cfe72597100073d52d9110026dd2158c1004edf4358e5402cbc7650d40004fd72d814301e7e659523000cfc72d9131006f772d8540006bd6450e1004f9e63904400a65f53d9530006bf745954301e7e6554f10297f170d06101473f549513102ebe10990100067f65d814304edc4358f4004cfd75d81540067c32d951002edf7358e40024ff7694740226f761991104475f4319543006bf21d911004edc4358f4104dbc7454440005b
  | 20 => 0x6bc529901001e7c65545400067c65191100067c655911001cfe75d8d41236f443185400067f71d9540004fd70d913104ebd711915101cfc75583410067c6558540004ff705913101e7c655451002ebe70590100067e62d954302df8705461004cfc7458e54004fd76d0d50006bd21d915119fb451d91510067f5258241004fd7695010006f46154140026f81058041005bc7454610004ff76546304567c40d954302cfd73d953001e7e655431024eb4101911001f777154550014fc73d9530006be72590100067f6518543246bc61d0d400067f6595131006bf53d91103473d5210640006be42d91510067f5258041004ff735971002cfc705974102dde704c530006be63d911002edf3058630004ff72d95430077752d8540026df7358e51006bf72d911002ebe3099010004ff72d8d10006bf62d9151236f740185400047d72d9543006f46218540004ff7258e540067d6554440014fe76d8d10006bd425824143f3e4319543006f472d854005edc6358d1004ebf7319110006bc7459531006dd63906503cdf7715953102e7c4059410005f67618540007b542d8540006f7615054000cfe7258f10006bd52d9110014fc74d8d401aede63d0650226f670d8540026bf7459310006ef7358810005ef72581310067f654c1100073d42d95430057f755813121edf3058e54116bc5199250006be43592500067c65d9110024fe76d01100667c54d9510024ff7158c100067d5258f4102ef7715864002dfa70906400667e65d951002cfc76d0c10226f430d8540006f663d854001cfe7558e4002dfa7010650004fd73d814121d7e761954300cfc72d953024ebe201911004ebf60d0d4002cfe70d8d41026bf519901000cfc7259510024fc7158e51006bd425804123fb44150c10004ff725944000cfe72d8131004fd7259210004fd769474021f3c43d9543006bd20d9151006df5258c1002eec405881024ebc1019110006f96018154026df31582311867c50d954100cfe72d8d5001c7c7559131026fb1058231006dd6354c10006bc535901025fb56190640024fc768c54024ebc3019110014fc73d815420ede43d8d5404e7c5459740026de5158c1002ebf20590100067d6550c1002ebd509925004ebc7459740004fd768c6501167f525974004ebc6450110006bd725925004ebc64505100e6be5259250004fe768c54004ef74158740006bf7159250006dd3258e5001cfc7559310024fc765011000cfc72d9540005bf74595102867c515865002edc2058e50006bf6450510004ff7559131007bb705054000cfe72592510073f7550f40006ed435881002cfe7694640005dd73d05310067e71d95400e73c74195400a65f5258e500057d758c55001cfe755901002ef410586500267c5159641004fd768c54001cfc7558c41024fe7158c10004ff725
  | 21 => 0x77150e41004ff7059641116be53992500a6df5158e5002cfc70592312b67e40d9540026df7358c41004fd725941000cfe7258e5001cfe7558241026bc5159010026dc7158c1004cbc7459441014fc76501302867c31d9510024fc715925103edf3258c1033d7e7494650026f4721854020ede6355010026f461d0530004ff7259441236f742185402b73c40d954004ebe6419131006f542185400a67c51d9530026f6619064000cfc725804102cfe70d9153014fc7459743004fd71d91302cfd92050d3004ebe759925025ebf641814104ebe64d0e5007cff71595100057f75503102f5bd74905400e67c52d954004cfc7458d10225f570d0610004fd7259540006bc5459230014fc73d911004cfe74594410067c425941001cfe755923101cfe75d913005ede63d8d100e5f9709915000cfe7258640015de739053001e7e6554440006bd65d911019ebf7459641014fc73d9510004fd7654e10004fd72d8553014fe7358650004fe7650530005bd748c54031ebd62d0d40014fe7358251006f753d8540024fd70d95100a67f52595300067d5259531024fc71594413967c50d8d5002cfe7655010006dc5458c10005bd71d0d400057f755814300cfc725823102edf7358e500073f6550d40006bf31992500073f65d911002edc7058c10004fd7695310006f552d8540006dd7158c400067d5258c41007b87050d400c6de5358c4002ebf4058e40026bf745925104efb4058254024fc7159743005fb704c6100e73c545454002ebe4059250006fa2058041124fd765413004fbb60d0d400a67c6559530026bf745923104ebc711911000cfe72587400067f755823100cfe72592101567f5059631006bf20d911000cfc7258440406be51d9151006bf4258241024fc7159740006be631911004dbc75d05401573f54952312b67e30d95400ddf97099130006bf5319110006bc53d91102af5e6354e504373c5119151006f721d854027f5e63946500067d52d813104cfe74d9531006b7431854004edf4358c40005f471591301d4ff75595310073f42d954302edd7058c1002cfe76906300277665d0410237f340185403857d72545500067f32d9510004ff7559010004ff7654530007b742d85400267e41594100a67f5258e500067552185400e67f51d95403667f4359641004fe769454005df970985300267f3159641005f9709054000cfe7258f4001cfc7558c40006dd3258e400067d655431043f5f301954331ebf62d0d4001cfc7558f1002ebf1099010006bd52191101567c658c54000cfc725963004dbe7494540226f620d8540004ff7259710004fd764c440266be71d9110006de7558c100e6bc5459540014fc7359010026ee41588100c6df3158c40006dd6350e10006be21592501867c655954104cbc7459510006f4715954004ebf4258041
  | 22 => 0x9110004bf7459710026bf3159010246bf62d0e410057f72d9540005bf745453002edf7358c10006bf65d911001e7c655474001e7c65545310067f65d8540007746154550014fc7359541024fd74d8d41024fc71582312e73d5290440026bc41592310067f65d011002cfc76550101b67f515974119ebd53d91510067f6554531004ff7654d4123ebe6150f4021e7d73d954304ebc4158743006bf42d814300cfc7259543024ff75594412a77552d061004cfc7459531006f750185400067c43d9510004ff7358440006bc5319110006f621d8554004ff72d81430067f5258e41004fd75d814104ebc645013004ebe64950103e73d5250e410067d52d853004cfc74594400067e21d95400967f50597101867c655054002ede4058e50026de3158c410073d421954000cfc72d814102ebc70990100a6dc5258e50005bc745813104dbc7454d401e67f5158e540067c75591100e57e76d95400067f52d8143024fc7158e5004ebe73191101867c6550510026dc3158c1017edf31d8d41004fe7654d4002edf1058e500067d65543400e67c6550110006be75590100057f7550e1019ebe75d91510067f705964102cff7058c1004e7e54597430e67f515825402e7e10594100067f52583413667f6495151296f5641061004ebc7459441006ef755881000cfc72d915021e7f659915333f797095250007d87050d30024fc7158c400dede63d8d40005fb7050d40004fe7654d410057d72195103b57f7254e50006bd4258e41026f81058251027b441506100067c62d95102ef3f52505400657c7558d100067f5258e4000cfc72d8d40016bc6350c41004ff70597410067d7259641005be76d0d4004cfe74d8550006f96018153006bc201915104f9c4350d4100cfc72d81310067e43d95400067f621951004dbc74543400a5de754c5300057d7518530004ff7650e5016e3f52191510067d5258440026f46110550004ff7650d5102ede3058e5002ebd1059250006bd6519110006dc7558c40016de638c650004ff7058c4110cff70591302857f7294650004ff7558e100e6be5459250024fd73d9131024fe715901002cfc7059743006be63d9151026be2199010006bf64501300067f6219543004ff7458c1025ebf71d911002ebc505925002eee10588100267e51596310067e73d954024ebc6510640004ff755874004cff7650310006bf5459010184ff7559541027b441545412bfd6214c530006bd42d814307e7f52d85500a5dc754c530006f56218540006bc32d9151026f4614c540004fd7259641006f453d8540014fd75d85530077621d9510004fd72d855004f9f7350d400073f6519110006bf20191104567c42d95430667f5258251004fd76d0650005bd744c5400067e5359641004fd769444002cfd73d9130006f96018131026f81058241005f
  | 23 => 0x4fd72597101c5de739815104dbc7454c4102e7c205941004ebe64191101acff71591310067e6319510004ff7258f10004ff745865025dbe70d0e410067d3259410006f451d8540006fb7059540014fc7359440006bf7559010004fd7650c1004ebc641053001d7f7354e5001cfc75d9110006fb609815300cfe725951001cfc7558d100067f6555110026f67418540024fc715834301cfc75d813101e7e65950101f5df73591531d6de5358e51006f77159540024fe7159441006dd7258c100067e73d9510406bc31d91510065d5258c1045ebe54d9153006f6321854000cfe72d85430067f73594101e57e7598543006fb7058d1000cfc725824100cfc7258d10006dd4258c1004efb40583430067e631954002cfc705964100cfe7259231256bc5119110024fc7610530006bf64105300067f7559530004ff7259543024fd73d813121c7e761954302ebf3099250004fd7610630206ee62550100067765d8540004ff725844002cfc7159310026bf415824100cfc7259631296f674d8540004ff765063033d7c7454e50006de2158e500e67f5259540006bc735901002ebd1099010004ff7258743004fd7654f40004ff725824102ebc5099010026f47159010006f575d854000cfe72d85500267e715964102fd8305013003edc4358c100b67f52d8d50005bf7150f4002c7c765455004efb705825404ebc7599010006bf6519110004fd7259441267b970906400067d42d951002edd5058c10006f96018141026f6611855304cff76505310057f754c6500073f4219540006be5359010006bf6499110006f6621854002eee7058810004fd71d8d50014fe735925043e7f631954304f9f7350c413e6bd6250e41004fd72586300067f7559543006bf4258e41004ff73594403667e5459541015dc735513025dbc7050e41006f762185400063f74596410e6bc54d9540007b761d054002edf4058c102de7d75d8153005dd744c530004fd74d8d5119dbe7550e410057f755911023ebc415913102df87050e40006bf32d915104cfc74596300057d7598143004ff745941033e7c74d9540025f47150e410e4fd7654140006f55418540014fc73d8550004fd75d913102fb84050130004fd70d8d54136de4358e500247c7654d5101cfe7558341005f77150e1002dfa7095230006f56118550124ff7359530266bc51d91100067f3059641004fd765511002ede3058e400067d525944002edf7058c4001d7c754c6500067d52d8151006bd64d0c1019dbe75d0e4104ebc6450f1000cfc72d85543d6bd6250c41006dc7158c4002ebd205925000cfe72d85540067d525901002dfa70d0610226f774d8540005f77159130006bd21592500febe54d9150026bf41580412ffb621d05400057f7550e410473f549501001c7c75591300067f6554110006bf54d
  | 24 => 0x76410610006f731d854004dbc7454640196df30d913123ebc6150d400067d5258c10006bc63191100f6de4358e4004cfd75d8d5400cfe72595410067d21d9540006bd42d91511167f50597400067d20d95400e6bf5259250116be52992500e6fa50582541867f52d954104ebc64d0d1002edc5058e500067d525911016ebc52191510067c65d8143004ff7058f41004fd72d9150004ff7654f400047f755913001cff765524104edd43583430fe7f515964004dbd769044002cfe7654e1019dbc7550e41257bb1019110006bc3299010406bf6418554025f47150e1036f3f5250f404373f751915104cff7695131004ff72597410073d74d954019cff74595410667c6559510014fd7458c4002df8705463004cfc7695110006dd3258e100067f65581430067f6598143006bc43d91510179f7450d3004ebc5458254004ff75591100e67e65d95403657c7454d5141df77158d51024fe76d0f10006dd5458c10004ff7650650006f521d8554026dd7158c10006f754d85400067f5259230006be53d9110014fc735834104ef441587400e6bd53592500fd7e759064002cfd74d8d40196de4358e41006bd70d911004f9c6350f40004ff765053016ebf5119151014fe73596400e57c755854004ebe729901002dbc7050740004ff7358251024fc7158e540067c7559130026f62158041007b45418540006f4651854021f5c5395130005bf744c6400077521d95100667f50d951004e7f7559740006df4258c101aebd74d854321e7d32d95430067e525964102e7e5059610005bf745474004dbc75d0d40005bc74546300c6bf7650f40006bc63d9110004fd7654c41006bf641815100cfc72d8154006de5258c40004fd72592500067c705964104ebf6050d400067d62d954304ebe6419150014fe73d85500067f5258f1002cfc765514002dbe705054002cfc76546301857c75581410b57e759063001cfe75d91313677671951512857f758c6503cef631d85530067d52d911000cfc7258f102bfd5214c53001cfc75d9131004fd72d9540296f770d854001cfc75d8d41015dc735453002ebd2099010024fc7650d41024fc71596400067d52d8141006bf31d9110267bb10d9110026bd2199010014fe76d8d40026be415925102cfc7058e5424ef65018540026be41593100057f7550110024fe71d815401e7e6554610024fc7654c410067c20d954304ebc64906301567f52d8d511c4ff735953133f3c541065000cfc7259010004ff7359541126dc6358d500067f42d951002e7f75596102b67e70d9540005fb70546101467e65d95310dedc6358d401c6dc6358d510e6be515925000cfe72d855301cfc75d85404157f7254d51004ff72586540df9f3050d4001cfe7558e100067f654c510014fd71d953117ede6350650076f531d853000cfe7258c10
  | 25 => 0x53004fb661d0e4119ebe6590640006bf64d0d100067f6554d403667c54d915100cfc7259441014fc73596410067f659454002cfe70d8553005df73551301e67f51d954301cff765454104dbe744c54004cff76d0f10014fc7358041006bf3259250266bf70d911001cff765474104ebe73191510067d71d95431b67c5059741015de73d9530006bd425923029fb75410610004fd75d853004ebe6450e50436be2119151026dc2158c100067f5258e1002eee30588100df9c6350d40005bf745855002df8704c5101d67f53d9531024fc71d9110006bd715925004f9f6350f40005bc74595310267f7159410184fd7654541024fc7158f40006bc745971030ebd6250d4002edd2058e50006b54318540006dd2158e50005ef7258d4027e7f71d951024eb4401854004ebc721911002ebd3059250006bf42d9151006be42d9153014fe735824125fb410d9110024fc715954002cfc7059010016bf7650e410067e32d9510026be715901002edc4058c400a57e7518530024fc715953023ebe4158f41136dc53d95300e4ff7559540006f820d81510067d52d95312b67c50582540073c65d054020e7d535974302cfc7058c41004ff764c6400e5bf7455140115be7550740026ef5158810006bc73d9110004fe765513102cfd73d85301d6df3058e5101cfc755844000cfe72d8d5100cfc725923104ef741584400067d65546102defa30d815333e7d6495250256bd7690440116bf54d815404fbb6050d4000cfe7258e4102fb840541400257e7154d51006bf5299010004fd769513102ebe4059210004ff7059543006de7458c1004edc7650d30016de634c640016be63d0e41006bf72d915101d7c75d0e500067f7459641006f653d8540006be6454c1019e7f52d9151004fd725963100cfe72593100067c735941002cfe70d911002cfe7650c10004ff72d95410067f52d85430e6bc75592501f67f52597430067d6550e41004fd7650d100057d72195401ddee729854335dbf72507400a6df53d9530026be519901004ebf731915100cfe72d8530026f46154540024fc7158c412ffb521d05400a57c7558530004ff72d91532c5df724c5300277565d04100067d73d954030ebf6250d4002cfc764c61002fba4054340005fb705061005edf31d8d1002edf5058c100057f7559131004fd76d0630004ff7459510006bf4259230006be53191100067e42d954000cfc7259710017db604c5302867c21d9510014fe7359310006bf311911000cfe72d9110014fc73d9541005f7715431004ebe75191102ad7f7654e5002ebf305901008efa30d813104e7e545974102df870505400057d7599110006df7558c10166de63106500067d745941004cff7695231024fe71d8153026be61d054004ebd7019110006f720d8540027e562d041002edd1058e5024fb
  | 26 => 0xf6bf43d9130006f663185400067d71d95400057f7550130014fe73592510067d52d9130004ff7258e41006de3258f41004fd7654f4100cfe7259131004ff7358341006bf32990100267f75596410067d52596410067f6555141006ee43588102dedc53d8153005bf7454531007777154d510a6dd5358e5004ebe64906500a6df5258e50006be70d9151026be7199010006f561544400057f7550f101c67f535963104dbc744c440004ff735954002ede5058c10024fe71592310057d759854302ede3058e103667c425964104edc4258c4004ebc5459441026bd41582410067d52d8154006bc32592500a6de5158e50004ff7458e1004fb84055140014fe73584400067d52591310057f7550e40004ff705963102ef61058630006f570d85400067c65d85430067f65d9110006de7458e5002ee7105881004e7f75597430067f65d8d40024ff768c7403667c405964124fb410106400067d52596310a6de5458e503ddbf7250c410067d74596411679f3050c41005bd7498153014fe73597400067c32d9540006f76198540004ff725834301e7e6554c1004efb705834102cfc7458740004fd7258f10006bc3159250004fd7259741006f6215834104dbf7350d400067f7559130014fc7358251006bd735901004fb441506400067f755804119ebf50d9151004fd76d0f100a75f53d953002e7e4059410026f4618c54002eee4058810006bc72590100073f7550d40315bf7250d400067c6599110004fc764c5500063d52d91510047f755921002e7f1059410004fd769063000cfe7258e40004fd7259251004fd7259510026bc7199010026f46110530004fe7690530006de3258c10004ff7358740026df4158c1017ebf435923102eef105881002cff73d91301e67c52d95432d5df7250d3000cfc7259440136dc3258e5027e7c70d9510006be525901002ebd309901004fbb405524023dbf7650e410067d5259231006bf30d91100267e415964101d7e7194650026bd41580411867f525954104ede4158c40014fc7359540014fd75d9153006df6350d41014fc73597100467c5259410024fe71d91300067d5258743004fe7650d100067c73596412b67f629525021e7e30d95433573d525074001cfc75592300067f65d051004e7c545974304e7e5459441005bc7459510006de4258e5002e7e3059410004ff7654e10004ff72d8141004fd7258e1001d7c75d0d51296f743d8540014fc735974019e3c7459641004ff7159250004fd76952100e67f52d9540024ff7690630236f564d04103c57d729525019ebd50d915119ebd54d915104ede6450d3023f9e6350e411b6f651d855424fb4101911004cfe7694740004fe761055002dbe7050f4002cfc7458f400667e7619510006f5611854001cff7654310004ff72d8151004ff7458231006f761d
  | 27 => 0xe1099250005fb704c510004ff72d953104fba609044004cfe74d9530006f55218540006bc7458630004ff7558c40006bd21191510067c65185430067e21d954302cfe70d8543014fc7650531026f77418540004fd7654d100067d659501002ddd73d953000cfe7259641004bf7458630004ff7654e4100cfe72d854024ebf61106402b73e40d9540076de4358e10026dd5158c1017df5719913104dbf7350c410067d72d954302ebd4058e4000cfc72d91300e67f5259250004bd7690440004fc76505500067f65551431e67f5258e5402ebc405901002e7c5059640005df73551430063d525925002ebd5059250004fd72d8154006f565d8540196dc3258e41006bd4259250006f5619064010efa30d814302ede7058c10004fd75d81310067f52586300067f32d9540026bc319901031f3f52d0d40024fe71d91530073d4219543006ee545881027e7c50582510073f7550c41024fc715963000cfc725865020cfd76551433373f741954002efa60181410067c6319510005fb7054630014fc73d915119ebf52d9151006be52d9110016dc634c11004ebc6590440004fd73d9110006bf64981510267f5158e5101cfc75d8d40006bc70d9151006be32d9151256bd6190440005f77154110076f631d8530015dc7354531006bc75d911043f3c431954304ebf7519151016dc6350d410267e105964104ebd701915102ede1058c40436bf101915102dd8704c5300e67f52582542867e31d9510015df714c530006f730d854033e7e74d954004cfd75d855402cfd74d9540026fb7058241004ff7259540004fd72d9543006bf745863002cfc7058e510267e215941005edf30d8d10006bc435925000cfe725824102cfc7650d401f67c65d0d1004ebe76d0d4024ef620185400075f7550d3000cfc7258c10005bc7454510007775218540006bf301911002cfd71d8d103fdbd72d0e41004ff755823102df8705451002edc7058e5004ebe76d054004cfe74d8d5102cfc70d85300067f6554510004fe765055026f7b10195100067f65191100267f75596310073f64951510067f6559110006bd6450c10297b74310610004fd7259543006bd32191510073c7550f40004ff765474021e7e43d954316ebc5019151007d4614c530004ff7359010024fc765431004ef77158740006f76198553016be63d0d40004fd72d9531005bc7458d510047f7259410007b5421854028f75521061002ebf705925042d7d729515123ebf6250e41026f47018540006bf6458d51006df7458e5004cfd70d954024ef430185400077465d8540007b7615054001cfc7559131006f5401854001d7f7354d5104cfc76545410067e435941002ede7058c4002ebc7059010006fb20d815104dbf72d0e4100cfc72d9153014fe7359541026f46150540006bd64d0630406bc21d9151
  | 28 => 0x20800000636d02280b000000a00820bc016000000803003406800380000c203801488600000810030004000000029001407a1af001803c02c008072804c00a000000002c0c806a026c2b800e0140010078030006151800001c001000000c0c2000001800000c025100017401c08000100a8000076025000000201000048c8002004000000010c0050088070020003009802c000015003800405a00100300084140c309d800c01c003026065400a041000195c0080f804485fc084487008802c014005018802c12c00207402a4006007013046000e0ef00180c800005e002801807a001017808400201a02b800c3d21ef0930000352001007000402400265088e0048007031000800601000180fc0a0001001009c00200103a000c0280c3002800001e2ee227000000401d000000c00800800a001857e0000200008000015001002800202500c000c00600000080c000202a0cc80bc004000024f4715954002cdc7650d300067d52d8d54014fc7655143004ff74596100247e769515101cfc75d814302eed10588102bf5d524c53019d7c7550e41006f75318540116bf5459740006bd73d91510e6bd5459250277741019510024fe71d8d540067f62d95100067d52595100073c655054002ebd5099010005bf7454741014fc76d01300067c73d9540006f76198550006bf6450d101e67f52595430067c31d9540004ff7258c4034ebd629064002eec5058810004bf7459531004ff7059441006df7558c40006de7158e50026f47418540006bd644c65000cfe72d8153004fd72d815304cfc74596100169e6350e41006bd7359250006f475d85400967f535971000cfe7258e540073f4219543004fd72591300067e725964102ebf7099010375bd7250f4004ebf62904400267c7159410004ff7259510006bd62d9110006f652d854002e9f4058c40004ff7058e54006bf62191511e67c5058e54014fc73586541867f5258654006dd7558c10024fc7694530026be41590100e63f54d9540004fd72d8d5420edc32d8d5404cfd73d95432b73d64952500067f21d9510006f621d8543004fd7258c4102cfe70d8d54004ff72d855338edf53d815300cfc72d81530067d52d81530d5ec7258d400067d525961019ebe50d9151004fd7259743004ff735941000cfc725974301cfc7558743004fd71d8d54026de3158c1001e7e65952311b67f52597412ae7e5059530004ff715954002cfc7058743006be521911037e7d625455002df870552400a6dc5458e503667c5459541006bd425834301cfd71d8d510067e6219543004ff7158343004fd7258e41006bf649915321e7c74d9543026be615054024fb46110640026f62158f10024fc715925043d7e76d95434567e74d9543006be4259250006bf649915101e7f61951510067f72d9543026f7751854002eb
  | 29 => 0x8003000819001a16800b000000005c001801800000001f000800000c001937807000902f800801a000002000402800000d800401001d007822000003c029805c00800700e000005c004013000c00800504082180d601b002000000235c0018098016006000800044a003000001001a005000000c00e004004800c1221f7384001c2b200200301a400a000014003400000000f80100c4017003801800000a000113c0062671cb801014600900806f001c11e00180000020b000100880060d202c809c1fe0e0070001401600200180f0042000000035c1b800000500c40440fd01d802c3987660168020014000002001428e065010827836a002001800468a04001d006c01000a00080000020010100004002028016000800000f00c006c00000000000440220080080040000000004005400002202a801002a362015800001601200b80c800000003388b408a0590048000048000033814400000002702141d6016005003c01a01f020802c5c4000006800400a0480018054008000006815d16a04a000000c0000000ae00440c002900380040427b50730298018059008000000e00300100403c402a00c003000e007000808800400400380700ba0ca1b0000c2be0000180018122100002008000408901f801000a01d088010406c004000809d33003403c818c1a000300680045bc000006800c01c2ad00106c800000101700000cc00900081a004201a0000d3c0100000070004000272054041405006001d800000013e211014c0040b300101a408a000033800014625b0040008006004002099002a03c037000404a0060000320008003000000007c51f001000c020005005801c00008a00e00040a20020018024030000005819c05000100000840b602700280bc01401a000000c04a020008000001201b00800000060110058a1500601f008022c03c7b300e0020006003027800c00201100e00502b6000019871000000242b8024042000018870800434e0000050074003110000009001a00082300024281b9824401a72707f0014198019000110007400d00008a805601571a801003a00d048000c040000014001806e0db0610040112000001000805401600f80c00160a90dd05000a60150330000000010003021000200500000fc00011c003819400a0080058018004031000007401002f12580cc02400100aab10200024002814c07c00500880d802600801781ec01203800180000040040000828000004276800c0080880000000078159000812400800200100046a202600e00380120c1007802800a00f0000118006003000003000001500701ac01200c01600e403000300c80947e2025000000000207e00280e8006001009020c006001003004c00414c00180600020070100000b4e00301080000e6004190801c00400b00b80001fa0540
  | 30 => 0xb001c09000000080000280004710178008024000007402a015220801c03600600e800401e04e005000400e01900100000da02200201b41ba00203c8004036017001001800e00100480a400403d00088440c2000007002402200000401580aa008000800400c02a000002401e00402c00bc00801600000b0006001003000001a4d8000008000c002000000001c00f002804802e0230080008010096013801400003b000000802e001003002c0500000170060000141008055404e01100004f005034f00280a41ac03b09105ec01c1310009ac000e000000a97c006007004046401c000006801c1520f804b000800400b02580000c201c000008838608a016800cd74000001820105401100982a01b000000b80040da0280050000002000004008400000f000000c01e012000002807c0f1002800001600703b002038c1050068004002007058002400a0610048010000006000002402c001000001c00000092b8d0800000b04480101320050070000034059009005015000000b8004002001036800400a00202b80441e605a110000002800001506d4000005002000000000c009006803600205680f421a000058801406404500500940006f300300200100de0110070012000000004008800200100101b606e000012c0000bd03e09d4070001033802807800701e00040ae003001800c03a008028073806000001c002800402a2b3801c0380c301b016400800c00100000560070008008004004000031800842900000380080000000118000033000800002800102f8010a4e00d0128000004014001800800003302482480f800000106a800200003f0234016015000800800002501100d401e00e001004001e0271b7855c00200800180000740000048010b3600b01b806c01000500001b400801b002000001202b08c80c400000000f00100480680010020072002022031405000501e001407e00006a0d200ec000008802026c000095815400c47f00000e422a0f430780ac00202f00b800800000000281a89040130548c8c00600700086a802400115900040021180058280018005002800404000f193803000004000401b00000030100084010000005808c00202a06f0004016018027001c00400900e805043e029002806008e000000002004004e0ed0005a00004001007400000400b801000c0010000000002000002015800000600300ec29a107000801c000004000002c01203b0cc0060000037005000001e2250138138002089000803833000a018054c0281030018000004648002800c008089000800c0040040060000002002116005003a004016800c01400001180040000010168440232044000801000002b001849c00223501800680be00900200340060150a833383f400f00100646340002f180ac000007000018805c19d000002c
  | 31 => 0x380ec00600000a000003c0000008024532002014870816801d08b825c19e00e00a800c000000005204c18c002000003400004900080000d40b100080000024fb003826c6020c1002818801400701a80f4038000002800807a2f500c032000204102497cc00a05001e803000401f001801810000501d801000027c007803400000100005e0b40002028c98400a522001000004c000003000002c000001001c0f600100281900380460030000000004021801402405305c80b40c406500880d800008000c001c00200400580c803c0b5000809c0002530010cc001e021007c07845a0d6000022400000c005806403c0040000108522337018801000607c004800801a04402a8008014081006803012a002001801000001700000002d20080070058006000022001001601f079801801400b000804c00003e000009c1360000f416180920e2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87f8759654c400156b09190c2a0012ad20564506500143e42ae1b1aa200a9c835886444143c6ca02a0c2a00021fa1e32d95400055ac18a830a80028dc835c9609500156908b08c2982539910675588100043f43aa4b046290a3f8254a64940014eb0b216c2a00021fa1c32d95100053b40cc432a8600ab5819d5640400156d0ba10c2a0126ad20354185400e61fba6caaa28000c9f645ce605440187acbba2a320002ae60032990100051ec28e4b24a000a7581909650400147b0b310c8880038d19743185400072ba9ca7b0a8000c6c75dc96344067c5f04a96c8a88262fa1f21191102555bc12423222000aba8098c64544014ed0b310c2a000e1f21f525921024d794006430a80008df835c96010401878ebba2c8880031ddd471591300051fc2a84b24a005ada801c9630400156b03a80c8880021fa1f21d95430071bb2a423222000c6f725496544101878edba2a2a80162fa13764c7400043e43ecaa1a2000c3e75d92644400317f0ea16c8a8802ae60032d915102c3f43ca6b282000e3765d0861500039cce490ec2aa0038dd9461d05400063a328e2b1a8000a768598b615001317908b92ca208b70f994745463001c3e43ea4b226267a3e84c8765500014bb0a392c6200028f61432992500053b428c430a8000c6d72188654410f8bce6328c0a18022f61c325901000636b96c432a2000a76859cf61500131bd0f192c7a08030f197745951002d74402eab102000c3c651d165440010ff0abb287080132d1c564503100053ac0864b28200087e87087655000117b0f988c8a88023be09765513027e3c386caa8a20058df8758f430400147f0aa16c8a88029760e70596410063abaec320a8001ce47248563104010fb0f902cb20926ad20342185400265a30ae918a8071d5b73dc15394001c6ea4a10c2a000317dd5634c6500051ec2cc63222000c3f651d151440011bf06b92c32000317d9573945300070faa4a8b182000a3d8510b6454d33c6c80a90c2a00031760f75583430055ac08a632220098be870c864544018decbb92c6a00022f61c30d91510043ec16eab046233ab5811cb64544018bae729ecaa0027271d1634c4403651f424e4b2c8200c6f72549654c4038d8e5a92c8980022fe117654f1004c5f426eca9a2004c74615d6615000117b0f328c88800297a144258c100051f42c65320204aab681d4064440014ed0ca90c2a00262fa1c32990100e51f42c64b24a0008df835c965c400147d0b310c8880163e201765463002c6e41eec98ca000ab5819c96404001c68caba0c2a0002976144258c100053a432a5b0a8000c3f7454963440010fd0fb2ac2a18030fdd76458d100a52f42842b1ca049cb676187415000147d09310ca880021fa1c21d95430051fc22e6b2c8200a5c855c563100015ab03aa2c6080131d1857590540
  | 1 => 0xcec328c8880162f21172597400062fbaceab182049ab68050861500014f700b10ca8800a2fa1f6450d5100637b92a4b282000c77751c565500070fd0b3b2868800327dd1634c4400255b40ce4b202000ab6819c9649400117f08b92caa08031b217725913023c5ec36e2a1e8000a3c86d48644400147b0a212c8080023de1d61185400043fc3ec432a8600a3d8590b6454c010fd0ea92c9080029d219521854000637b96a4b1a200087e878cb6544097970e1b228288002976142158e500063bbaee2b222000ae98094d6204001878ea322c68815a1f21b75585400e51f42ce6b24a000a9f8350b644c4010fb0f90ecaa180e1f21572582310072ba9ca630a8000ab68190b6454c01c6ea5108c88826b8d10352185402b61ec26eab242000c7752dc5655000187aebb2482a80031b5c952d95100243e43acaa8a600087e87d49601040187eeb322632800237e0d72594410055ac0ce4b24a00387c855c9644c001c68a8a90c2a021b8d9d454185400061ea92ed2088000cb564dc5430410f878ec3aa86a00163e20172595410043f43ea4b2260008f78758c615010f87eec3aa8720912bca0032d854000e7239442b1a20008bf845c9654c54f87ae8a96c2a192aada0652191100045ec3cc43222000c3c75d91404400147b0b980c88822a9760c70d95430051f42885b22202da3e85cc064544014bb0a10ac6200031b1d472591300051ec2885b222000a9f83509648c001b2a8638a80980030fd947458d100043fc2aed18a8099e341054864440090f90eb2aa72095a8f61071d95400051f42cc7b22200087d870c765500018dce5b2cc2a18022fe1d64191500051e422c5b2a20a787d8754b6054c0117f0eb20c898002a76135158c4016d1f42e42322a246ab485d0c615000117f08bb2a3180123d20572595404351ec2cec322a297e2d72548644408d56d08290c2a0126ada0342185400146e41ae4b04a26cc3c645d6415400147b09310ca8801aba600735881001c3e43ea4b2220008df835c9654c515878c9baa86880071b1c95258e4001c3e42ae4b242043c5e635ce5494001c3ceab1c822000339dcb71591300043ec2ceca1a2086c3c7619153544018dee4a92cb200038be0952990100055cc0064b24a066c3c76195415000747d0ab24a8080028f61321d95430045ec26eca9a20478bd87d93414c401878a9ba2c328002ada1b43185400054fc1ac4322a200c7676d9461500018eecbb8aa0880021f61c20d95430043ec16eab222049ab48015061500014ef0aa00c2a00161f21d52594102965a326e2a0220008bd87c846454439c5f04a92c9280023ba1c7258d100047bc0aecaa22049ab480508615000187aebb24c8880038754963904404b65a3a442b0c6086a3c8654864544014eb03310caa0002a7e112158c400043ec38c432a8004
  | 2 => 0xf72d953002c5f43c86b2020008bf845c96344001c6ecba18c2a02022fe1176544400052f42c84b18200087d86dd543905599b2e7b04c0a980e8f217649511048c3ec3ce4b282000a778158b655000147b0b90ec8880021fa1f525823102c5ec26e5b2a80018ee87dc9634400b9b4e0b188328122ad61f43185400061fbaac8a1ca0059da87dc1314c10187b0bba2cb8819a1f21975905400052fc1ac5b2a2000a3d8494d65904010fd0e32ac2a00039918921d951043c3e43acaa1c82058de87d4d630411587cc9baa8608002ad604521911000637316eaa18200087f855d940440011ef02bb286880ce4fa1f7550e4101c6ec1ee5b02a60387c855c9601040147d0a190c888003a9d894218540006363a8e4b1a2000c5c7558d430409356d0daa0c2a00021f61c20596410052f428e4b188000c6f655ca6150c0147b0a10cc928003171d56350e100055b430a830a800087d82dd560104014790ea92c9280023d61e42d85400071bc2a8630a80058f8805c9644c49b0fd0dbaa80880031b5c952d95430055b42e8630a80058dc874c9638401317d0f988c88800317dce53596410063632ee4b1a80098bc845c965440018e8ebb8ac908002ad60854185402374bc1a8630a800087e878c965041234bb0b292c6080030fd9774541403661f322eb20ca000a5d851c56394001c68ca30e82a025f8b9c952191100043ec38c432a2000c5f75d4d638408956d0daa6c2a00061f21d525954124d5bc0a20322200087e87195634404547d0b90cc9280021f21d6550c1000c76412ecaa26067c3c74d9551500091e902b92ca9819f0f1d365541404ed8e42a86a026000a3d85cc364544cfc3e8721ecaa00029d61642185400061fbaac8a0ca0008bf87594644400187f08b92cb208030fdd754590104551f42041b2a8600a6d85dd1620400187ea53b682a025f0f1d152595100045ec3865324a000a5d851c963940014bd0b90ac620026a7a107258c4000c7bc3a43b0a860087f8758865440014ef0ab08c2a00029d60420d954302c6e432e72a2600487c875955310401d4a42900c8880028f60b65d91100a52f42e42b1ca049ab480484644408956b09baec2a00728fa1421592500255b40ce6b202000c3f7454965440015cb0321ac408002aea00321915123d5bc3a8630a809ae3610d4864440011f700b92caa08038d19754185404065a30ee8a8a8049cb6761854150001ccd0ab1682080031dd97715814300c76412ed28a60058dc865d1314c00147d0b906c8880022fa1c64581510063ab2ee2aa4820087c8754960d0c0147d0a212c8080262fa1c301915100637c2ee4b1a2000a3d85c836444013179083b28688003175d563906501352f428e2b1ca000c3f65dd1515040156b08298c2a00ce2fa1f31d91510043f43864b2c8200c3d87d92545440187
  | 3 => 0x4b24a01ca3c855c964940010fb0e310caa18ce8fa1772d91510051f428653202000cac74dc9634400147b0b392c92800a2fa1f6450d100243e43aa4b288200a3d858c864440cd0fd0dbaa86a00030f1d77458d1022673b82c5a082001ccc724c963940010fd0ea92c8882028f61470d91510051ec24a7b2a8000a3d84d96544c40147b0a310c88824b1d1c552591300071aa1ea430a8000c74651c56050c018df0bb92c8980022f61b744c4400064f398c9302a200a5f855c5639400147b09b2ca88801eb66007258c1001c3f42eeca1a20018ec825d8414c00187ae83a6ca882af0fdd774595430045f43e62b24a000c3c75d91434400117b0f310c8a88061f21d52595310051ec2065b2a201ca3e850c964940094ed02192ca0800317a0f75582310061f3b2a432220028dc835c9601053f6390aa1882980163d21d21584400043fc2ae9b0a600087d878c965904911790cb8e86a000237e0d72597400056a41ac430a8000a3d8494965904014eb03216caa18029e60273596410051e42ac5b22200087f855d953440010fd0f90ecaa00031dd4b71591300055ac266030a800387c87d49644c0010fb0e196ca881272de0676d054000636b90c5b2a8000c3f745c965904038d8e5a92c6880162f2137650c100043ec3884b282000ab58108064544015a906b16c2a00022f61c20d91510052ec28e4b182000a3d82197644400156b03190c88800e1fa1f75592100045fc22e4b2e2000c6f725496590413938c8b9882980029de1563185400247b4386430a8000cb464dc550440018df04b96caa000b279cd43582410055ac0864322a2058bc8750964940016690aa18c2a00032d193714c11002c5e43a84b202000a3f84588654400157700b16c8a8a4b8d1c5525901019d1f42865b22a20087e87595430400b17b08bb083280022fa1c30d91510047dc3ac03028249bb280d50615008f56902b2286081b30f1d16554e410255b40ceab202049cb4109db41500014690aa18c2a00028fa10325941002d5d40065324a000a9d84c8563100095a902ba2c6080029be1543588100052ec2c84b1ca090e67109d562040010fb0f90eca880029d2154018540225d9406a9b0a8065c7b865c254940014ef0ab1ec2a015b4e59170952500059a42a87b0a8000c6d721886550c014e90ab08c2a02628fa14521911001c3e42aeca182087b1c835086550d31878e9a92c3180029b61473588100052fc1aa5b2a6087e1e631d543904014bd0b192c60800317dce53596400063a3aee2b222080a3d85dcf645440517b09bb287880162fa1f54592100246e43a64b188200a3f855886444001c6908a90c2a0012ada0432590100063b3b0ca30a80058dc874c963900095ad03212c608012ada1b61505403651f424e6b2c820087f855d8414c001c68cba10c2a00163760
  | 4 => 0x1501210fd0e392ca080061fe1d52d954304c5e422ebb026204ae4815d162040072f10ab808328007331c93258e102873210a43b2a2043c3f76dd5439040187ee9a92c68824b99105755881024d5a4328630a8000c5e83dd560d0c0187eebb2286a8a6b8d903521854001c3f43eeab06864acb47119130440014eb0b39ec2a00028f616735925025c5f43e84b048200a3d849cd65904014dd0a39ac4080730f1d564506500053ac2e4030a8004ab4815cd640400147b0b196c8a88023de0572595400255b40c84b202000c7475dc5644c00147b08192cb20913395c162d04100063a32ee2a022080ab784584615501317d093b2a298007391c92158f104be1e3a2a4b2a6200a3d8494b65500011f70eb00c0a88028f61432191100056bc1ac430a8033c3c65dd151504018f700b92ca0819e1fa1f20d95400063cb80e1b2a8600a7685c80615000147d0b212c80814aada1032d85400056bc1ac5b0a805697b865c25494001958e8392c6880021fe1572592100045fc22e4b0c6000a7585c8361500051f50db82a2980031bd49725941021e2e39ecaaa28600ab583d08615000147d0b196c8880021f21d52580412971b2a6a9b0a800087d829d86544001c6ea4b2682080028fa1263195100061e3aac8a182000c3d84dd560d0c0156b02194c9280021f61c21d95400062f31aeb20ca0028dc835c965504010fb0f212ca080022fe1171d8d504870fa06a4b18809ce3610d9464440038d8e4a92ca980072b1c942591300045ec3865320200487d859db43544091ed03bb2a6a00031bd977258d1033e1e3a6caa9a8000a5e83081659040156f08a98c2a00029da1b52d854001c5f43ec8aa22000a3e86548644409956d02396c8880029d61672d85400062fbaea6b182000a768198b6550c0147b0a18ac9280029da1b52185400e49f43eeaa1a8053b348550c418400147f08a92cb20a428fa1452990100257340ea8b10200087e87d4960d0c8d5690ba10c2a00261fa1f65551100145e422eda1e2046e3685150615014f878e8a92c3a1a030f1db6454d510071ba1aa430a8047cb4715cd640400193ee8b1aa2200029720d62195100051f42c85b222000ea46250b615000187eea3a2c68812ead60472d911001c3f438c432a8600a3f8454b65500a18e8e3b2aa0880022f61f31191100043fc2aecaa26009a9e84d45631000117f08bb2868800e1f215765011024c5e43a84b00820387c87d49634412347b0b292c80800393e095258c100061eba8ebb22200299f8750e414c00117f0eb20c8a98161fe1d65952300071bb2c423222067a3e841cf655009356f08a00c2a0016a721943d01300043e43aa4b1a204cab6810cb644400117f0eb20c8a88166721d43501300063a328e2b2a8044cf070d8541500070f90a3b2a2a019f0f1d375580414851fc12a
  | 5 => 0x812f27dc163904400051fc2ae4b24a000a9e83083645448fd4882a1ac408003391cb715913004c5f43e62322a20387e85dc163d049f4eb02396ca88113a9d0162d04100053d40064b2c8204a768190d659040187aebaa6c8880028f61032d95400063b3aec330a8000a3e8598b64440014f301318ca880021f61e72d95430051ec2c64b24a0018f78748761550010f90ea92c9080022fe1d641911000717c12a4b202005aea801cd6204001c3ea4b1c822015a9ea0073d954000717b12a4322a200a3f8754b6454401c68ca908c8880123d20576551300257240aa8b10200087f855c96344125c6ce8a90c2a00161f21d52594404371aba8a830a8086cb47115164040018beeab1a8608027271d16354c410243e43acaa9e2000c3d651d1518c0018dee4a92c8980028f61020596410145ec26e2b188004cb4615d2515000156b03aa2c908002ae60032590100043f43c84b282065c3c741d5601049f4f500196ca88003171d56350e4001c3e428eca9a20008df835c9644c00147d0a310c8882224fa1f7550c410052f41ce0b2c820087e87d95615000147b0a196c8a880e1f2157650d100053a436a5b0a80058de878c963040015ab03212c7280029d21b521854043caf43eeaa1a600087e8710b65440015ad02392c7280021fa1f52591310247a40aed18a8049ab48050c61500094ed03212ca080029da1720d854000637baee4b2260058dc874c963040014bf0aba2c7280169e20172594100043f43aa4b22600087d870c96504001c6ea8a90c2a02032d1c675590104af4a20a42b1880008be87d9163441275d700baac4080038be0952d91100051fc2a203222000a9e841c96304001c6ecaa10c2a00028fa1b521911000c76412eca1c20008bf845c9654400147b0990eca880028f616329901000c7a43a42b1a200287c8759553d00015cf02aa2c4080028f61672d91100053b42cc630a809ae3410d4864440014eb0b90ec2a00030f61375580410055ac0e603222000a9d84c8563940135390ca1c8298026a7a137158c400043e43aa4b0462008f7815c9644c0070f90abb287080163721d6354c102255ac20e7b0a80008ef825da544c14727d0fb2a86a00123e21d20580410051f42c64b202001ce67248761500014dd0bba2c4080030fdd152586302255a43287b0a8000e3484d48615000187eea2a2c9080021f61e42d95102555a40a403222000a758198f655011b56f0ea10c2a00062f21d425913021e1e3b6eaa1a8000a9f83588644400157300196c888003a9d8921191104055b40841b22a20187c8754965d0123c3a80a92c62011aada1032185404051ec2ee5b22a20087d878cb65440014ef02b10caa015a8f21942d95400e43ec38c5b2a800487c8754965c408dc6ca9aa0c2a00031b1cb6558d400043f43865b2a8047cb4615d13
  | 6 => 0x51e432a5b22a2058f48748561940018dae4396caa1862a76107258c400061fba2a4b2a62058f48748561900014f30139aca0825f0f1d152597100071a2a4a630a8000a7685908615009317f0eb2683180021f61f21d95402b53d40065b2a80028bc845db434400147b09392cb20a1aada0432191510045fc22ecaa22000a3d8590d64940014ed0b216c2a00022f61f315925002c7a43a42b0c6009a9c84485631009793e61ba2c3180021fa1f52591100147c432e12a260a8c3d74d4b6150c0517b09b96c2a1a4b995c952185400043ec3e41b2a8600c3d84dcb65500095ad03aa2c6080028f61672d915100656326e4b1a208aa3e841cb6550c1317d0e100c8a88ce8fe0952d91510043f436eaa1a2000ccd721c9639403153b09b8ac6200021fa1c65581430056cc1841b02a200c5d731cf65501214dd0a3aac4080028f61662d91102355b424a430a8097e1c415496310125ccce4a90c2a00029d60642d95100051f42e423222092c747154964040018ecebb0c82a005257215744c53024d5b402423222000c3f525da41100018d8e5b2ac6881263d21d215804100537428e8b102000c6f825cb6550c0156f02900c8880123d205769454024c5e43a86b008200c7775dc5655000147b0b21ec8a8a8b8d103651854047573c0ae8b10209487e871c9659055b972e9b04c0aa002a720d62d91100055ac0ce6b202000af1810836054401c68a9a90c2a00022f61f21d91102565a388c8a822000a748550c6150087c3cc7baa87208031be1d75588100043fc2ae4b008200ce7721c5644c0010ff0ab92caa18b70f19474545102455bc3e8630a8000c3e76d9741500010fd0fa92c9080029d21543d85400a52f42884b1ca0098be87dd1654410156d02396c8a8802976144258e5033e1f426eab068600a3f845c9659040187ecbba2a28812eaea00545824101c3f438c432a8033c3e65dd1519009f4e90c90eca880022f61c30191510063aa96e2b222000a79800c965040931ef0eb0c8320002b5a047258c402465a30ee6a0a80058bc8759143840010fb0f216caa190e1fa1d6550e4116d1f42e40322a2098be84dc5639400b1b907bb262200021f61c32d95400053a40ac432a8000a9d841c963040870fd0f216caa18021f61f30d95100051ec2e40322a2008bd87cc76454491968c2b8e86a010ec720d42d95430051ec28e5b222000a75810cb65440014bb06106caa18028f61663d91100043ec16eab068600e658558b4104001c38c7b2a86a0002ae60263191510065bba0e2b22600087e87d95635000517908b92c3a18031b19772581430051ec28653202000e3552d08615000117b0f90ac9280133518573105300055cc04a6b202000c6f7254963840011eb03bb2a6a00022fe1d621915100637b92a4b2e860587c87549658c0014bf0aba2c60
  | 7 => 0xbf845d9404400147b0b90cc9280029da1632d854016d1f42840322a20087d82dd5644c40b5d50129ac4080161f21d52596100247a40aeca18200087e87d95434400187aeab248328002a720d62191510061eba2e5b2a8000c6d7254b635054956b03310c8a88029da1663d854000667b98e4b226097c3c7454965104018eaebb0cc2a00031b5cb62d95430055b40865324a0008df835c9655040117d0e106c8a8802bc600321854002c7c402e4b282000ab584c8061500014eb03212cb208030fa1774597100e51f42e42b24a000a3f855cd640409793a61ba2c318003175ce53d95100062fb9ce6b2c82098bc845d953c40015750131ec8a880237e0d72582510045ec3e43b22a200c6f751c9644c08f968c3b8a86a0002bc60032d85400043fc3ac432a8600c6f72549654c00147b0a392c8080031bdc952597100051e436a5b22200087e870c965040cf878c9baa80880030f1d76458d104ae5a3a242b1a2048cb471dcd64040014bd0b392c6080028f61270596414051fc22e8b2c8200cb474dc565440014bb0b90ac7280029e61420d81510054f426e2b1ca000e355248464440d947d08182cb208ce8fa1730d91510047ac3c8430a8000c3f75591430400187ecbba2c688002ab610735881047e5a38e84b2260018bf8750b644403947d0a18ac9280021fe15725911001c7b43ec2a8a80008be87c85649400b3b100b9c829814aada1073d85400265bc3ac9a0820058bc865d1315000117f08b92ca98002976172158c400051ec2864b24a000a3d84c8765500031d904bb4a8980030f15176906500053ac0864b2c8244cb476d85415006747d0b90ec8a88030f1947458d100051ec24c7b2a200487c859da41540a10fd0f906ca8822a8fa1321d95430043f43aa4b226200a3d850856494001878ca3a2ca9891aada1132185403361fc3ac92a4a000a758190d65040014eb02102cb2080a3720d72586404963a38aa4b2a8000a3d85cc3644400117f08bb2a68824297a145258c100051e422c432a2044ab5841cb61500cf87d09baac0208028fe11659523101c3e428eca1aa00087f855c960d0d1f968e3b92c80800387d4e53191100063bb28e2b028600c6f75dc9634400187eebaa2c9180030f5d372d95400071a32a8430a8000c6c7219563500a556d08396c2a00023d61e65185400051e42a86b048200a76858c86150123cce20baac4080021f6177650d1002c7a43ac2a888049aba800c864440014eb03318caa000333dcc7258d1048f34402eab102046ab484548615000187eebb2286880029da1730185400054f420e4b1ca046ab684c80615006717d0e322a288002a7e0d62d91510061fa96e8b2a204ccb471d9140440015690aa18c2a014ba510d43d85400256b408e4b182000a3e85cc064440cd4790ca10caa00724f215744c5404
  | 8 => 0x8a90c2a00031b2177258d100047bc3aca30a8004a74815d1650400187acbba2a7208028fa1032d95100053ac0c85b2a8056a3d841cb655012147d0a292c808002b9e0963d85400052f42c64b188000a5d859c9630400117b0f90cc9280028fe1562d91100062fb9ce6b28200487e879496590401c6e87a90c2a0002ad611321854000637ba8e4b1a204b8be8715160904018bae639eca880022f61c32191104a63a38ea4b226000ab88058b64544ad87b093b0caa00021fe1572591300056ac08e4b1ca0008bd870c864544030f90ea92caa00038dd95431854001c3e43ea4b008200ab686d086150091d2ce7a18c2a000387d4e539901048e2eb9aa5b2a6086ab787150615000187ceda90c8880031d197715954016d1f42c64322a2008be870c964940298b8eab1a87280028fa14325901004c5f43ee8b2a6200ab581d53644c401c58c4a16caa1807399c9215834102d5d400653202000cb7641c5404c0014bf06b10ca880023da1c32d85402355b420a630a8000cb5711c5649400147d0a396c888002ad60f541854024d5a432423222056a3d84dc76550143c6f08328c2a01b30fdcb64951510071bb28c2a0a80028bc845c76350001958e4322c6880730f1d56450e5043752208a8b1020048f8865c0415400956d03aa2c808002ad60432191100051ec2e42322a267c3c54dd560104ad47b09b96caa000317d9773541300061e422e4b2c820387c855c960d0c0147b0b216c8a88029da1421d854024d5d406a8b008205aba800c9649400147d0a196c8880028fe1564191100061f3b0cba0a800487f87596548c4010ff0abb2a8988031b5cb62d95400055ac26a030a8000a3c8550d601040156d0d108c8880029d20562d95404075210a43b22a200c3d75d53644c4014bb0b192c6080162f21d42592100255a40aeab202000af18094c6150013878e8b2aa2200063de1d21d85400043ec3864b2c8200a5d858cb63544010f90ea92c88800e1fa1f755913100c3e43aa4b2a8600c7765dc563500010fd0f982cb208029d60865185400053ac0865b2a8000e678254861501118b8ec3aa86980030fdd46458d102455a40ac9a1820058bd845db4304129c68e3a92c808246976165258c400043ec2ee0b1c82098bc845d9518c00147b0a100c8a8a02ada0473d91510052fc1ac432a8600a3c86548644400147f08b2ca988003b848520580410047ac3cc630a8000ab481590644c0014eb0432ec2a01262fa1b7150d404051ec28e7b22a20087d878c965040ad47b0839ecaa00038d61365d854033d1f426e5b2a800087e8754960d0c018df04b96ca88002aea0032d91510053ac28c5b0a800087d878cb6550001c6b09b28c2a00029da0642d95430053ac28c430a8000e678254b61500018df04b92cb208028f61671592504e71a086ca322204b8
  | 9 => 0x42d95100061fba6a4b0c6026ad9801c963940095c902a1ac40823fa95cb42185404870ea06a4b188000a3f84596548c0018e8ea38ac8980123da1e42185402355b426a030a8000a3d850836454545c6c81b28c2a00029d61730d854002c6e41eeca1820058bc875914304001c68cb108c888003279cf64981510055ac0864b24a004ab787593410404547d0b194c92812f27d9173181410062fb2ae72a260008df835c964440090f90ea92cb188029de15431854004e5d322e020ca018ad9801c963100011dd0e392c89822b4e1037550d402b59c402e9b2a8000c3f751d1654400117b0e100c8a88028f61632d911002e6c302e7302a200a9d83080645440147f08b2ca8080030fd5276951100051e42ac83222046ab684cc061500011bf06b92caa0002ade0d42185400061fbaee8b2a2000cb564dc554040014bd0b392c6202aa8fe1162195430053bc2a87b0a80008f787584614c00147b0a316c8880022fe1d62191100043ec3c84b2c8200c9f739cf644400153d0990ac7281b28f61f649515100637b92a4b2e8200e1d7558e41100d947d08102cb20a1b0f1d874545500054ec1ce1b22a20087e870836550c0117f0eb20c898a032d1c754590100143f43ecaa9a200087d87cc3655000156b02106c8a88129da04205964102c5e422eca9e8000cd973d8260544010fb05baac9081429da0432d95100069a388eaa1c820087e870c765500018becbb9aa29880297a147258c1004c5e422e4b0c6000a75819886550c0117b0f98cc9280031b5c952d95410a62f3aac720ca00487d85dd951d000187ecbba2a2a0002ad60432d91510257340c86b102000ab880588645444547d0a18cc9280028f61642592500a52f42c84b1ca000ab9800c86454401878eab22870801339185729854300727a9ca6b102090e65109d5620409717d0f98ec8880023de1d61185430062fb9ca6b282000c6f7254965840019b2c6b808328026a7a132158c400a52f42ce4b1ca067c3f725925494151878e9a92c3a18028fa1262d95100043fc2ae1b1a82058be87d51648c0018dae4a96ca988161f21d65550100056b40c84b1ca0008bf845c9644409717f0eb2681880023d61c32185403651e422a5b22a2058de87d4d63840010ff0abb686880032bdd37258d100043ec3e41b2a2043c5e63dd543040018dae4a96ca980021fe1d621954002d4e43286a026049ab680884644400b37501ba2a6a021e1fa1f6550d4025c5f43e86b048296e9441885631015347d0da10caa1a470f1d152597400061fba2a4b2e2000c3f75d51648400b3b100ba262980031bd9772581430051ec2663b2a2067c3c545d841940011f70eb00c0988031ddd771592100255a40ae4b2020048f8865c0414c00156b09990c2a025f0f1d15258d1000573c12c630a8000a5d858c96394001c6f
  | 10 => 0xb1a2066c3e765d365500030ff0ea96ca9800297a147158c4003572c0ee8b102000c6d7254b655000156b05a18c2a021a8fa1f74596410047dc3ac0302a6008be870cb64544010ff0abb286080029da1432d85400053b40cc5b2a80008bd87c8464440014bf0ab8ac620002ade0572590100055ac16a830a800087f855db43840014eb0b980c2a00031d1977158d4011717c12a5324a000e346550c615000147b0a192c808003a9487201911021c3e436eab02860587c85dd953040011f700b92ca880031bdc952596300071a328c2a0a8000c5f759d5631009556d02298c8880163721d6350c100043f43c84b2c8200c7775dc5644c08d968c838a80980029da0663d95400052fc1aa4b2e86058dc8758d531000147d0b318c8880021fe15764c44004c5e422e4b2e2000e2c6250b65500cf87ce9b2ca2a02469b61e75588100056ac08e4b18800087d85dd931500010f90ea92c8980b70f194745453100637b96a4b226001c6e7254b635040b1790eb22a8080071b1c9525913019e1e32ee8a8a80098bc845c7635409556d03190c8880022fe11765513100c5fc3a85b2262008be8719163544d947d08192cb208022f61c32d91104a71b3a6a430a8000a3d8498b65440011f70eb00c0aa0021f61e62195430062ec1eeab0462048f4811d9315000147b0a196c888002ad21161185500063a32ee2b02860087d86dd5430400d5cb0239ac4080028fa1672d91100051ec16ca32220498bf8759341840135390ca1882980021fa1f205964102c5e422eca8e8000c6c721956050d1b968e2b92c8082878d100651854000637b92a4b2a82498be87d5160104018dee4a92cb189123de05765011032c3f43ecaa022000c6c65dc9634401317d0e194c9280029ee0172594100052f42842b188000cb5219db4150029c9f04a92c7282032dd9071581540051f424c7b2a20098bc845da54440010fd0e32ac8880022fa1f645815104c5e422e4b2a6249ab68015061500091bb07b96c8988262f2117654d100043fc2ae4b04629be361019464440010f90ea92c89899e8fe1d64952500063ab2ee2aa020448f68788560d051f968e3a12c8080021fe157650f100055ac0c84b24a000e3754d48615000187eebba2c688016b6a007258e500051f432a5b22202de2f8254864544010fd0fb2ac8880032719173981510146e41ae4b24200187f8754b65440070f90ab86c6a08023de1d62185402b63c386caaa28000a3d840c1659040117d0e322c68800237e0d72595100043f43ecab028609c3c645d6644400156b02194c8080021fa1c65585430047dc3ac0302860387c851d9434400147b0b192c8080021fe157650d100053ac0ca5b2a200387c855da3150001c9f04a92c62015a1fe15765521000e5739285b22a280a3d85dc3645440187ecbba2a6a00021f61c
  | 11 => 0x440018beeab1a872800e1f215725913104c5e420eca8a801ca3e851c9649408747b08396caa18028f61721191100052e41ac5b2a8005b988050d404c00147f0ab8ac9282372d1c542591300045ec3e63b222022c3c75991319409556d02290c8880028fe1573592500071bc26a430a8033ab5811cf645440153d07386c8a893e1fa1f21d95100053b4286430a800087d85dc163d0401a6eebb8a87208028f61331d95404943ec3ce4b2c824aab6810c864441158b8edbaa8698002aba1073588100053b40865b2a8000c3d85dd1618c0019cae5b0cc2a18028f21564191310053ac2cc7b0a800387c855c964440070f90abb08298002b9607545881001c3e43ea4b0686a1e3640194615006747d0b396c8a88023be097650d104b65a3a442b1a204aab681c80644400147b0a216c8a88030f54a76d05404365a388eab20200187f8754b654c40187d0bba2c31819a4f21c6550d4000536c28e8b102000e355250861500010fb0fb2c82a00028f61730191510062fb2ee6aa286008ef825d8414c00553d07b2286a88061f21d52597410051f42663b2a2000c3f751d1654c413968c8b8e8088256ad60a21191100071aa94423222056c3c76d954350001c5ec4a96c8a891b2d1d061541400051f436a5b222067a3c85dc964940010fb0f216caa02531d1c752590100051f42643b2a2000a75850c761500ad0fd0f216caa00028f21510191100247a40aecaa020098be87cc66494001d2a87980c2a0002aee0162191510051fc22e0b2c8200ab98098f6454489d4a80b1682080028fa1462d91100043f43c85b2a2005ada801c96310131c3883a92c6200163721d3258c400043ec3e60b2c8267a3e840cb655000147b0b900c88800a3720d72595102853b40c85b2a200387c855db43840018bae729ecaa080a1f6177654e100045ec3865b22a2028dc835c9651040b1ed0db8a608800297e0d525963143d1e4328432a868fea672d0861500018dee4a92ca208022fe1175d813104c5f43ee8b2e2000c6d72d886550cd947d0ab96c8a88030fd4b745953100477c12eca1c2000e376515061500014bb06102cb208032ddd061541400074bb1a8630a80a5c3d741966050cad8f0e0b86caa00028fa1720191100061f3b6ca322200387e8718865440051b906b92c88810e8f61371d95430071bb28a9b0a800387e85dc163904014eb0b310c2a008a8fa1421992500055b42a8430a800387e87dd563440a5968e9b0aa2a00021fa1f20d95430257340ee8b1020008bf845c96550c018eea5b8ac88812e2fa1f21d91100052fc1ac5b2a80058de86dcd544c091d4883a1ac408002ae60032992500054fc1ac5b222000e3752d0861500011bf06b92caa1926ada0354185400053ac2cc5b0a8004a76810c9659040b17d0faa2c8080133c185701053000657ba0e4
  | 12 => 0x8023de1d61185530053ac16cbb0a8000a6e85dcd6204001878ebba2c898a878d14054185400069dba8e0a1a8000a75850cb615000f5ab02392c6080032bdca72d915125d5d40065b2220098bc845c9654c00156b08290c2a011aada1253185400051ec2e43b22a200c3c751d16344091d2ae7a18c2a00028f215621911004c5e422e4b088000a3d84d96544c001c5ea92a2c408202ad61f54185404055b40865b22a26cc3e87dd165904011ef02b92ca9800e1f2157650f100052ec2ce4b188005a7a809cd65040014ed02106caa18028f61720d915133d1f420e5b2a8000a748558c615009b0fd0db82a6a88028f61773d91100051ec2ce4b20200187c8754965d0c0156d0339ac9280028f614425925024d5b4068630a8098a3f8254864544011bf06b92c12a1123da1e42d85400045f43865b222000a758198b6550c050fd0fb2aa6a0013a99d162d04100055ac24a630a8001ce4724856344115878c9baa86a88031d54b715954033c3f43e61b2a800487c87549659040187ae4b24a92822a8fe1564191530051f42e43b222000a75858cb615009556d03980c8880031bdc9525954300657b26e4b1a2056d59635c254940a18e8e3baac0208028fe1162d95104cf1a202a430a8000a3e85cc364440790fb0e316caa1a678d841521911001c3e42ae9b0a600287d85dcb6054c019c8e438ac8980b62fa1f64545100061faa2ed2a020008bd849d9514c0018dee4a92ca200030fd9574945400053a42ac7b0a80008bd870c9649400153b08392c7280129da0642596410053a42ac430a8000c6d72d886550001c6ea4908c8880030fdd2745941016d1f42864322a20087f855c965440010fd0ea92c688002b9e05435881000637b92a4b1c8047cb4615cf415011587cc9baa8728053171d5634c6500047bc0ae4b222000ab58194864440014e90ab16c2a0203a9107545881033d3cc00e7b2a804ea7486484654400156d0aa18c2a01b28f2117259641226d9b88e0a0a8000c3f75d516010413878e8b2aa3a08031b5ca52d95430052ec28e2b188000c3d72d9254544018dee4a92cba023ead61f42185400055a40ac8322a04bc9d7058e41100010fb0f310ca880023be0976945300052ec2ce4b1ca09eb1c8550f404c00156b03900c8880cf0f197745451002d5d404a6b202004ae6811cd62040030ff0ea96caa00161fe1d65950100043fc2ae4b226233a3e85c83645440196ee838acaa00029da1472d85404ae5a3a242b0c6000e6b805d5620400187d09b96caa0003a918921d91100069c3aee0a1a800187c85dc9650414d87ee832ac2a18031b1c86558d1033e1f424ec32a8000c6c75dc9644c0091e902b92c808002ade09431854001c3e42aeda1a2000a79800cb6544001c68a8298c2a0002976164258c100055a42a8430a8000c6f7254963
  | 13 => 0x61e32ee8b1a2000a3c8654b64440051b906b92caa00cf0f1d76450d5102c3e43acaa982049ab48088464440014eb0321acb208028fa1672590105058e42a8720a6000c9f7458d31900010fd0fa92c6880123721d6354c41006cca1ae020a6033c3f74549655040b1790eb2287280028f61020d95430043fc3ec432a2049dd0301c5404c00187ea5ba2cb880029d60662d95402b61e3a2e9b2a8000c9f739cf64544018eaa5b8ac8980023de0576551304df1a080ca3222000c7765dc540440070fd0fbaac020a630f1d35258d1000636b90c432a8000c6c72d956050c038d8e4a92c6880029d61632185402b61e3b6caa0a800387e85dd1618c0015c904b18c2a00162f21376506500064f31ee8a888005aba800c964040015c904b1ec2a019e8fa1331d95400046fc1ae4b2420028bc845db435451f56f0fa10c2a00028fa16321911000c76412eca1a200087e8754960104012eb03baa87288161fa1e52594104852fc12a4b1ca000a3d8498c654400147b09296caa18028fa1773d91100053b40c85b2a8000c5f75d4d63900012f301baa87280021fa1c6558d400055ac0ce6b24a009c3e645d741940935690ca10c2a00163e20172595310070fa9ca6b20208fea4419d1620400147b0b216c888003561d77050d304045fc22ecaa620008be87d9163544cd878ec32a86a008a8fa1432992500065a3a6e2b1a2044ab48650b61500cfa70a8b808328002a760c20d915101c3e42ae4b1a2000a5c8358b654400156b09290c2a00163721d3258e50026733a2c5a082000e346515061500891ef0cb8e81880031dd947158d400064f3b28720a6053cb771191605452f878e8a92c3180021f61f20d95400052e41ac432a800087d85dd1618c123cca20baac40800a3720d72597100056ac0c84b18200387e87dd5644c00156f08a90c2a00030fdd675590102843e43ecaa022000c3f74dc9659040147b04328c8880030fdd764501100052e42ae8b182000a778558861500014ef0ab16c2a00029b61773588102675210a43b2220008ef825d9534400156d02192c9280029d616631854002c5f43c84b202000a3d85c8564940030f90ea92ca88027271d1635444024c5f436e8a8a2046ab6848c8615011bd4882ba2c4080031bdc952595400052fc1ac432a8046ab684cc8615008d56908a98c2a010e8f61070d954300636b90c5b2a2000a768198c655008dc68a8aa0c2a00031b9c865985430053ac16ca30a8000a7a809cd65904018f6cab84a89819b0fe1d74d95403661e2a6eca8e8000c6d72d8b65440cfc3887b2a86a00262fa1f7458d103661f3a6e8b2c824dc74711d5601040147d0a392c8080028f61032594100053cc0064b2c8200e1f5394f64441214bd0a292c6200031be09725941025c5f430e8a8a2097a3d8594864440070f90fa92c118
  | 14 => 0xf87d8865500014ed0b986c2a011aad21120185400055cc006432220018ec825d953440019aac7b8a860800e1f2177650c100051e42ae6b202004a768190d650410187ee8b2aa9208029da1462d85400071bb2ea9b0a8000ab681909649400196cedb0e82a00028f616329925002c6f43c64b188091c78805c965040011f700b92ca9890e8f21942d95430043f43840b2c8256a3d84dcf65500014ed0b90ec2a00023d61e62185404051ec28e5b22a250c7471d9540440190fb0e316ca880031b5c862d95430043f43c64b2c820087e8710965040070fd0fbaac1188038d54964d04101149e42ae898e801ca3e859c9649409396c213b682a00023de1d61185540063ab88e3b2a864f87c86dd563440971790fb22a2880030f15076545400055ac0864b202004ab6810ca640400187eca3a2a29891ba9e09421854004c5e438c8a8a2049af28094c61500014ed0a18ec2a00038be09521911002c6e43ac6a1c2033a3e851cf6454523c3e80a92c6200029e60253d954002c5e43a84b246033a3e858cb645440153b09b8ac7280021f61e62195400055ac206430a801cc3e7559241940ad0f90fb2a86a02372d1c5425901026c3e432e12a2a209e967158e41100014eb0a396c2a02468f61652990102665b10ceda0a80338be87c8764544a10fd0f986ca8812ba9e09211911000e36392a4b1c200187f8754b65504031dd0fb92c8980028f614321915104c5f43e43324a0028f687d85315000156b08196c2a00ce8fa1472d91511352f428e4b1ca000a758508761500010fd0fb2ac68800237e0d7258d100043ec16eab2260008f5870cb61500975690c90ec88819e8f211525925021e2f31eeaa1ca049ab68050c6150001958e5b22c688002ad60432d91100045f43864b2020048f4815c9644c0070fd0bbb262a015b4e99170952500063632ae530a8600c5f75d4d631009356901a18c2a00023de1d61185500055bc224030a808893e87dd543d00014ed03310caa0003a518d43d854048e1eba2a5b2a800087d870876550c1317908b92c688002976163258c400053cc0065b2a80008bd84dc563940018bcc7baa83280030fdd7745911004c5f438643222000a75850c861500874bd06106caa1a1aad61c54185400052ec2c65b1aa800a9c8358b6454401c6a86a90c2a00028f616321915119d1f42841b22a201ce472487604c401c690aa18c2a00072b1cb425913019d5ac0ee1b22a286ab681080645440147b0a18cc92800a3720d72597400154f41ec8a1a2005a7a800c965040010fb05baac68800339dca72d854001c3e42aec9888000a3d85909640401353908b8ac6200021f60a76195400053b42ce5b0a80008fb805c9644c4a14ed02396ca880262fa1f211915102c3e43aa4b2c8000a768654b6150001c6ecaba0c2a00021fe15725954000
  | 15 => 0x80600080a80000029480000000681a00780000900080380a00000280f8078010033348078bba1f82980182987180181300280188181c81000480003e8048010ff82180208083581a80001f0000010161a880000a02380780a1e880000180280380403380007200101e00a00483d80101880900000000280080000a00080280100382900000000100180202380985106084c80400080b00180100306600000b8019960010028018308049888450418008062cb89082080600905800e84500282f80700e00182300000000a00000100020480e18880001000000000180980200300000201680180380e00200000604611600b80080000081d80002b00180981300080180400481a1c201300000000000280000003588200100100780181d90400280680800500b80c01400a81180500200e80600c00100004c24105e01000880180b00201d81000180080080006883a80901008380180f82e8061dd0420490000eb0ee0120070030078000f981701001100501500394300c02880b80a82804901581280680000880383e02b00e00000900b00001f0008ef80e8048198e100000180480781001981b00980800300200180000008c80284980600a01680c80980300180700002f80480582fbf505681100119702081401480e00980081c0008038000002a58011bd81983000080000e0d780980080381d00000401a00f90980180f00880500000000500580380300680700405500080001000300d00004400b80080000200980184800380380000b00101f0980008108052998038038000038048a580180780909180884400100506602880780000e00280580501501300089900d82b01e00000080180200000000500380000580006a00e81380380592e80282c80e07300002980280682e00900d80000080c8098020058030000008020019d000c81301881185384880200000f80100403580200100e88b00000087780c83401203da8e80880992900088880e01b83900400003100232400681900228780180000005805b02080b00c02b8000090bb00000000880080002901c00b00780480a8070ed8059f200683b06200281000801000080481280980605e80002185d80000680380880193802980003300283f00000200d80181080000b80584200080900580008d34380105301a20e80000000c00000014685e006005011a8b00080080300800000901301d87f00000000f80000600080000004000300680d00000300a80700080380e01c0032ec00680700002600701200d80780480f00a81100001000180001f8009109a180000200700080180480400001102100180800004500080000301680000301980282d0a300c00580100e8038dd9754185402b6ad31ae12a4a000a6c8550d620400b9b0e0b1a63080061f21d52595300054f41840322a20087
  | 16 => 0x300005100000f0058c980200882000000001a02500102d0043188060028280000698002970e101902900080005700409600280301384b80086200a80380003d82f00080000401a00e01480e0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x39c550062024040858d0060d1c4855cd64040012349850d52185400060d2047559143040016149550f30185400048d255844c861500935909050c71501305748d2606550c615000162592d0d5218540006891048550d620400162592e1352185400058564c84d4861500016259221352185400048da636550c61500932a49848520191100048d25583d0861500934949650c715013000545255431c5404c00123592215431854050e8ca005494c615015f23696215431854000546255435c0414c143a328019754185400048d25584cc861500012349850f5218540
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x4b
  | 7 => 0x4c
  | 8 => 0x4e
  | 9 => 0x5
  | 10 => 0x94b
  | 11 => 0x94c
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124c
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138c
  | 18 => 0x138e
  | 19 => 0x9cb
  | 20 => 0x9ce
  | 21 => 0x12cb
  | 22 => 0x12ce
  | 23 => 0x10b
  | 24 => 0x10c
  | 25 => 0x10e
  | 26 => 0xa0b
  | 27 => 0xa0c
  | 28 => 0xa0e
  | 29 => 0x130b
  | 30 => 0x130c
  | 31 => 0x130e
  | 32 => 0x180b
  | 33 => 0x180c
  | 34 => 0x180e
  | 35 => 0xa4b
  | 36 => 0xa4c
  | 37 => 0x134b
  | 38 => 0x134c
  | 39 => 0xb4b
  | 40 => 0xb4e
  | 41 => 0x144b
  | 42 => 0x144e
  | 43 => 0x28b
  | 44 => 0x28c
  | 45 => 0x28e
  | 46 => 0xb8b
  | 47 => 0xb8c
  | 48 => 0xb8e
  | 49 => 0x148b
  | 50 => 0x148c
  | 51 => 0x148e
  | 52 => 0x184b
  | 53 => 0x184c
  | 54 => 0x184e
  | 55 => 0xbcb
  | 56 => 0xbcc
  | 57 => 0x14cb
  | 58 => 0x14cc
  | 59 => 0xe8b
  | 60 => 0xe8e
  | 61 => 0x18cb
  | 62 => 0x18ce
  | 63 => 0xecb
  | 64 => 0x104b
  | 65 => 0x104c
  | 66 => 0x194b
  | 67 => 0x194c
  | 68 => 0x1849
  | 69 => 0x184053
  | 70 => 0x4d
  | 71 => 0xe8a
  | 72 => 0x18ca
  | 73 => 0x289
  | 74 => 0x10a
  | 75 => 0x1489
  | 76 => 0x130a
  | 77 => 0x14a
  | 78 => 0x2c9
  | 79 => 0x14c9
  | 80 => 0x134a
  | 81 => 0x29253
  | 82 => 0x124d
  | 83 => 0x29256
  | 84 => 0x185253
  | 85 => 0xec9
  | 86 => 0x1949
  | 87 => 0xb49d3
  | 88 => 0x9cb53
  | 89 => 0xe89d3
  | 90 => 0x9ce93
  | 91 => 0x198c
  | 92 => 0x148113
  | 93 => 0xb8a13
  | 94 => 0xa0b93
  | 95 => 0x184a13
  | 96 => 0xa1853
  | 97 => 0xe8a13
  | 98 => 0xa0e93
  | 99 => 0x18ca13
  | 100 => 0xa18d3
  | 101 => 0x14d
  | 102 => 0x749
  | 103 => 0x134d
  | 104 => 0x29313
  | 105 => 0x149313
  | 106 => 0xb9813
  | 107 => 0x180b93
  | 108 => 0xbcd
  | 109 => 0xe9813
  | 110 => 0x180e93
  | 111 => 0xbca53
  | 112 => 0xa4bd3
  | 113 => 0x168e
  | 114 => 0x1a49
  | 115 => 0x14d353
  | 116 => 0x1354d3
  | 117 => 0xed353
  | 118 => 0x134ed3
  | 119 => 0x195353
  | 120 => 0x135953
  | 121 => 0x19cc
  | 122 => 0xe8293
  | 123 => 0x28e93
  | 124 => 0xe9493
  | 125 => 0x148e93
  | 126 => 0x18d493
  | 127 => 0x1498d3
  | 128 => 0x1a8a
  | 129 => 0xecbd3
  | 130 => 0xbced3
  | 131 => 0x16ce
  | 132 => 0x194bd3
  | 133 => 0xbd953
  | 134 => 0x74a
  | 135 => 0x74c
  | 136 => 0x5cd
  | 137 => 0x1a8c
  | 138 => 0x17cd
  | 139 => 0x178e
  | 140 => 0x19cd
  | 141 => 0xd0a
  | 142 => 0x5853
  | 143 => 0x188a
  | 144 => 0x1a09
  | 145 => 0xd49
  | 146 => 0xd4a
  | 147 => 0x5993
  | 148 => 0x1a0a
  | 149 => 0xb0d
  | 150 => 0x140d
  | 151 => 0xd4d
  | 152 => 0x1a0d
  | 153 => 0xd4291
  | 154 => 0x1a0291
  | 155 => 0x2c291
  | 156 => 0x14c291
  | 157 => 0xa09d6
  | 158 => 0x1809d6
  | 159 => 0x289d6
  | 160 => 0x1489d6
  | 161 => 0x74291
  | 162 => 0x194291
  | 163 => 0xa0754
  | 164 => 0x28b16
  | 165 => 0x74a14
  | 166 => 0x75494
  | 167 => 0xd4c
  | 168 => 0x1a0c
  | 169 => 0x74414
  | 170 => 0x75614
  | 171 => 0x1a9954
  | 172 => 0x1689d6
  | 173 => 0x180a16
  | 174 => 0x28751
  | 175 => 0x29951
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2200
  | 6 => 4892
  | 5 => 2089
  | 4 => 24
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
  | 8 => 2*((h/48+packedAt gbK8 (1612+(h % 48)*6) 6) % 62)
  | 7 => 2*((h/754+packedAt gbK7 (81400+(h % 754)*12) 12) % 2200)
  | 6 => 2*((h/1672+packedAt gbK6 (234816+(h % 1672)*13) 13) % 4892)
  | 5 => 2*((h/703+packedAt gbK5 (123251+(h % 703)*12) 12) % 2089)
  | 4 => 2*((h/15+packedAt gbK4 (1680+(h % 15)*5) 5) % 24)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc1e07c0f07ff83c03fffffc32387fe40f27f
  | 1 => 0xffe007ffff83ffc003fe03fccdc644c7f3c73
  | 2 => 0xf07fff800fffc3ffffc1ffc030e0787387cf9c
  | 3 => 0x7ffffff00003fffffe00003f007f83f80fe0
  | 4 => 0x7ffffffffffc00000000003fff8003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10c064148202650241122b1501018196405225
  | 1 => 0x8d0e002915480ae402a540aa844c64481b2c52
  | 2 => 0xa412888009d480a89481948090e02860858498
  | 3 => 0x865354fa00223532b3801032f005683680b60
  | 4 => 0x79de72cea730020c10060c3bb68003f6f000
  | 5 => 0xce00180300c40060302118303efb7f7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37799
namespace PEqualNP.Outside.L_meta_37799
open PEqualNP.Outside.L_meta_37799.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 13 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 4 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 12 := bs4_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := bs5_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 24 := bgb_4_0
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
theorem bgb_5_2016 : Interval gbAtlas 5 2016 73 := block_range (n:=73) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2089 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960)))) (concat (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 (concat bgb_5_1344 bgb_5_1440))) (concat (concat bgb_5_1536 (concat bgb_5_1632 bgb_5_1728)) (concat bgb_5_1824 (concat bgb_5_1920 bgb_5_2016)))))
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
theorem bgb_6_4800 : Interval gbAtlas 6 4800 92 := block_range (n:=92) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4892 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2496 bgb_6_2592)) (concat bgb_6_2688 (concat bgb_6_2784 bgb_6_2880))) (concat (concat bgb_6_2976 (concat bgb_6_3072 bgb_6_3168)) (concat (concat bgb_6_3264 bgb_6_3360) (concat bgb_6_3456 bgb_6_3552)))) (concat (concat (concat bgb_6_3648 (concat bgb_6_3744 bgb_6_3840)) (concat bgb_6_3936 (concat bgb_6_4032 bgb_6_4128))) (concat (concat bgb_6_4224 (concat bgb_6_4320 bgb_6_4416)) (concat (concat bgb_6_4512 bgb_6_4608) (concat bgb_6_4704 bgb_6_4800))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 88 := block_range (n:=88) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2200 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248)) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536))) (concat (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)) (concat bgb_7_1920 (concat bgb_7_2016 bgb_7_2112)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8feeefaa8fce8f8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074600 * 2 ^ 32 + 4243126440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37799.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.or,[3,4]⟩,⟨.and,[5,7]⟩,⟨.or,[0,3]⟩,⟨.and,[1,9]⟩,⟨.or,[2,8]⟩,⟨.or,[10,11]⟩,⟨.or,[0,6]⟩,⟨.and,[2,3]⟩,⟨.or,[13,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4243126440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074600 * 2 ^ 32 + 4243126440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37799

open PEqualNP.Outside.L_meta_37799 in
theorem PEqualNP.Outside.L_meta_37799 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4243126440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074600 * 2 ^ 32 + 4243126440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
