import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36380.Model
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


end PEqualNP.Outside.L_meta_36380.Model

namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
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

end PEqualNP.Outside.L_meta_36380

namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xe50171a000194e01b80144963800689a900001b200ada1b009860000b40284a740091000a00000001800000000000030003de0442fc0066a5400000143960038fbe000119066ec58074c5e9e00bd50000d8000000000000440005c00001009011c000000000011000304040000600082021000212000030020082bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (731+((h/13+packedAt s0K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s0K4 (1875+((h/21+packedAt s0K4 (1728+(h % 21)*7) 7) % 122)*7) 7
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 2 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 3 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x309118a290425014a849d0930194d21886315c
  | 2 => 0x52922864129212816942528510a154a8b284c5
  | 3 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36380
namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x33601221586539a0040e1526800020e009011a2cb0a1c955983a500080000f804c8c000221000654154892ea111e18b47890c14e51c03c1105202080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa4383652962e5e32a246c004c4bc5abe624a4ca08cac1aba6a8a3c9a56649c00004468a60000009200981e22aa8800300086948e28c2266e00001600008066b43a006c0020902c08100042484e7600580a18007e060c9e007440600ea85054b824143e3400b2027c82840078125cb6b02a00ae7a70721c2e0cb80062800200c4c802a10380000c0053008103023c1020200407016e5210edaa421cf55242af29c855d5390b5ea4a14f95042af298855d5310b3e85996750b32af28e653e548ca7aa9195754e32d6a1465ad424caeea2995d14532e7a92659f424cb9c84996750932e6a12658d424cbaea2995714532ea28a6554514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96835f53506b8a6a0d754a31cfa14639d428c6bca318d754831cfa10639d420c6bca218f5944319f2a6433d54c86bca790d754f21ea18e435f53886b8a710eb50a21afa9a435c534867ca810cf55021af298435d530875a8410f50c421bd280437950086bea6a05714d40af298815d53102dca4205b54840bb288817551102eca3185d546309faa2613c544c27ca9904f55320af29e415d53c835a85906b509209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x258088002848c19c28068060040000000000e00001e0000002205049260030022c303254214532a3592424cb8542d4532c3508514cb854214532c5d08514cb464214532c5508514cb454214532c1508514cb0d5250831c3d4d428870d5350821955943108785420c421ca509500875031540218b588544c2546154f20c354d42c8344520c510
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x408605655083108780a1062a8043411c55350b20
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (826+((h/15+packedAt s1K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s1K4 (2904+((h/33+packedAt s1K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s1K3 (840+((h/7+packedAt s1K3 (798+(h % 7)*6) 6) % 39)*6) 6
  | 2 => packedAt s1K2 (150+((h/1+packedAt s1K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffff81fffc3e0ff87f0ffff87fe07d19f3f3
  | 2 => 0xf81f0ffe0fffc3f0ff87f0e07f87ff82e6ccfc
  | 3 => 0xffe00ffff0ffffff0007ff007ff8ffff070f1f
  | 4 => 0xfffff0003fffff800007fff0003f80fe0
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10c2008c200840011809012318092118085171
  | 2 => 0x32441114645004506883104528824b0862c4b4
  | 3 => 0x4108aa2082a222a60444aa0845509463050a0a
  | 4 => 0xe596cc494a3aab3bb550881276640633b80fc0
  | 5 => 0x861888718cc333ccc666cc9c04401843d7a000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00fafafaaafaa0fa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36380
namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4a000000000000000000b0c00000000132400014000001083106d58000600000010100004cea30000629004000000009271a00287540000e0000f802c540000001019007049e2800b9a1e880000000000222808103041418000000020020000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x190e2a9ea88f02228311180c04801981800a8029088b1a0ca8071f8690970e8126002b130d80001b1c880000242d94ad12a20d25211a8fab80269d000000a5959b89000027a98b9885802c90001602a0800516a3839180002c1200000007801f270000230017802000000000001e1c1da18a06138994152a0424800a0810107321808e1a0000106009080600380121c216000850eb7290876d5210ebca6215754c42d6a10853e540ca7aa8195794f41aea9e836e52d06daa5a0db94a41b6a94835f53506b8a6a0d794631aea84633e540c67aa818db94831b6a90637a500c6f2a018e795031ceaa063ce520c79aa418d794431eb28863da500c6baa018f654031aca80633e54c867aa990d794f21aea9e433e548867aa910d7d4d21ae29a435e53902baa7205bd4940b6292815e53102baa6205b94840b6a90817651102eaa2204f953309eaa6616e52cc2daa5986795330ceaa661ce52cc39aa5985794730aea9c615c514c3b6a0985794c30af29c415d538827ea8904f151209f2a0413d54082bca6105754c20bb288417551082bea7885714f10af29c215d53843b261084fd51109e2a2215f53442b8a6885bd4910b629221d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6000008020ca0e0402c354d4210b0d5454831c6951500c7195454031d2949500c7495254031c355152cc258654c110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc7ffff83fe1fff07f0fe1fffc3f81ffe98f39f
  | 1 => 0xf81f0ffc3fff0ff87f0fe1c1fc3ffc1f674cf3
  | 3 => 0xffe00fffc01ff1ff800ffe01ffc01fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffe001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40840088002200009010024480488488081185
  | 1 => 0x82421110940810282106208844124854234432
  | 3 => 0x114aaa218d54835b088b54116a815345858e18
  | 4 => 0x3594cc4a2906a595daa11025b3258189d80bc0
  | 5 => 0x261888733198c9e66ccd993822060211f6e000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36380
namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5873864a1d26280292078a8100acb9f00004801e8d324509400844a802722349005a00600008001a421800200b01800858d801c6028004334000c000040040104ff43fe43fd43fc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x345a001ebe063800b000420484a47c609a7ea800ac3e9690140e009c00b8686e74c020323a865e54a212aa4c0000a69400622428c48016ae6c30ba8c483c2c0cbc407a52089e2600782e0072104a00c244980aa0668e0036500000005c22b2008846b4586a76000000564e2a181c1a8202928a64b67000002c206020018024240840200009100811002400040c043001a2400a236e52d0edaa5a1dd94743baa8e876f5250ed8a4a1dd94442baa88856d51ccadca5195b94c32e7298656d510cb5e65a0eb0cb419eaa4836e52906daa520ebcc941d619283b7515067ca820db94841b6a9083b541cc67ca918cf55231b7294636d528c7986518dbd4931b6292633e540c67aa818db94831b6a9063cc320c76a8218de94031bca80636e53c86d8a790ebd0721d6a0e433e548867aa910db54a21daa0c435f53486b8a690ed50521e7a9a436e53486d8a690f314d21a629a43e7514875e8290f990521d6a0a43e5414874a8290cf950219eaa0436e52086dea4a05b14940af298815d53102dca4205b54840bb2888175511039865985b94a30b6a94613f544c278a8985bd4930b629261cc324c2eea2985d14530af29c415d538827ea8904f151209f2a6213d54c42dca5885b54b10daa0e21b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x3c00023120000c40071463535080110402ca25038028002182a5610c941c9549410c7843250431d20c9500c7314154031c514d414864e6394d21c314f41486a56490521d114e414870c5350521d114d41487875350521c994d41487245350521e114d41487045350521d10c8514c23561151209318d52c43255250710
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x22070032505500c68339ca6a0a43411cd5250710
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => packedAt s3K4 (2904+((h/33+packedAt s3K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s3K3 (833+((h/7+packedAt s3K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s3K2 (149+((h/1+packedAt s3K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffff81ff87fe0f870ffffff87e07fc0ff3cf
  | 1 => 0xf03f0ffe1ffffff007f1e1e07f8ffffe324c7f
  | 2 => 0xffc00fffe007c3fff801fe007ff00783c38f8c
  | 4 => 0xffffff803fffffe00007ffff803fc0ff0
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x110a008c0108800181022223281220a80491c5
  | 1 => 0x248499104a4222504290d1441484955212441a
  | 2 => 0x4296aa24c75526b6c88175095d20561ac38e8c
  | 4 => 0xb2844491401892b15240012624960216c0b60
  | 5 => 0x8c308871986633cc66c9999c04018443bb6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeaaaaecec8888fefeaaaaecec8888fefeaaaaecec8888fefeaaaaecec8888fefeaaaaecec8888fefeaaaaecec8888fefeaaaaecec8888fefeaaaaecec8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36380
namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8000340000e00b94007401b0000f004eac01c0038002484140c349428000280112aa4416441150600481984c240213e8cc8b40000131e6510c0004040001000000ff43fe43fd43fc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x60001e70b2649c00882000841292440068004e005ab6240a1000000066a60040008eac0090227a00007e005200001c16007200000000008096466e0000003a02b4000e26000062084a0648a85c3c0000005676500000868c00009a00000000006c006a0078000000aaa23200007400a00004365ea4148a0000344c0000000000280000940038ae00000082007c000c00002a309e00983e001ab0540042582c2e1801000801010103040a0b1803000907000000000004020001000014010000b7296876d52d0eeca3a1dd54743bb28c87755190edea4a1db14943bb28885755110adaa1995b94a329f2a0653d540caeca2195d54432bd2806579500cb5ca8196b55032b729865ce530cbcca2197954432f5280656d500cbd2a0195a54032b7290836d521076a8220cf953319eaa6633e548c67aa918db94a31b6a94636f524c6d8a498cf950219eaa0436e52902daa5205dd4540ba28a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8985bd4930b62926177514c2e8a2984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905d94720baa8e41ae54c835aa9905b94f20b629e41e651c83caa3905b54a20b729a416c53483d6a0907a8c120f4982416e52082dca5085b54a109faa2213c544427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc0008006ea40201c9551510cb2a5454032ca551500cb625154032d8545500cb255250441c955151c8268654c120
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2724+((h/30+packedAt s4K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s4K3 (312+((h/2+packedAt s4K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffff83e1ffff070e1fffffc381fffe07f27f
  | 1 => 0x3c3f0ffc01f1fff80fe3c3c1fc01c3ff3a4c4f
  | 2 => 0x3fc00ffffe01e1fff003fc01fffe03c1c38f8c
  | 3 => 0xc0000ffffffe01fffffc0001fffffc01fc0ff0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x84020088022000010004444440844844009215
  | 1 => 0x98c9910d4c2d1388721a289a41892b91a4c4a
  | 2 => 0x9096aa295065134b9102ea14e92c0b0d43868c
  | 3 => 0x2284442810044942a48002112513010ac0960
  | 5 => 0x23308873198999e6cd93333820602221f76000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeaafeaafa88fa88feaafeaafa88fa88feaafeaafa88fa88feaafeaafa88fa88feaafeaafa88fa88feaafeaafa88fa88feaafeaafa88fa88feaafeaafa88fa88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36380
namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40f7294816e52902faa5207b54a40b6a94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40bea98817e52102faa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483de84907b10920f719241ed32482fea2905f14520f790a41ed21483f460907e4c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bcc820f6190417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec62887d4c510fd20221f940443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620efd0c41dea18837e52107dca420db94841bea9083ed52106daa420ef90841de210837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c7dca518db94a31bea9463ed528c6daa518df94631fba0c63f4418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa92637c524c7bc6498f70c931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621fb18c43f531887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690df94d21bea9a437c53487dc8490fb50921f799243ec32487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29
  | 2 => 0x2080026d0001004a0b93ea0fc000000fe0c0dd9e8076991238122ca850312662e878443a4f1d41d8b21112640682a00d25887cab22821873ca597d26e6a12ba21406934190ab3aa350919ad070488920000004291e90f000000001613e019cb71f929e7806c9c822e001000c2384000700000000005d0730005e43f16c426004de16b38c9200d9f12901492d92e18a6c0cf87b3369cc64a242b08c82f1c72d228c5507a3d20f469108256128c196a2f89ac0013600041c001300009bc001dc0009d4ec9512664a5038b841a94c54026268001148c1338470d218d1180d53b26c2707007f1402ba888ad84e320001208494b22786382e3ca318f1a3102c494f50cf4408044693106e0007fa4001c0000000a00009c4d1a30007c8880040007b8df0460500a4000000004981e185224679061a04929487e1eb084398ed1534d43940884d00094400234000950bb8f025434026000106424c60001808606580c166204a823c1163342e0804768cc0c9b804a03c0026114c87002a5512416cf606f364579348714588e00016d3a43a02b8680aa0005f9461c65c0d596210c0000009c08e8544c2252069b80a9d8372390799722b208c001670004d4aa80031e0003aa4c00049c1991543c3c4cb08e1c43d4000004084810b8004be30c21856000844c4a6045c8f8f78951781dd391a70169283ca1a30242cd98d72927e08217823e3e8f39910723790e95f1d88ac9e9133cc1a4042631a62f4561ed16c83c5f10d324228c009d02e514a62431ec39c8c8512b896017a453167d06c1421645506e9df0e0538049cd2427fcbf2081126985b99d3ee6e8320603f43ac3e1c53946207a05827e66422878198824eb83a25a618ba88f3429102401d2026b8eb23f27617cc70060064602d1c907c310e810216a3280021920c72c9c85d2e66689f1c32cc414a90da1e402c030280f0180618803024081bc11008180001307c000500000c0600c160700d0380001012010430000406c0701819018030080801c080c0030741204c01034000180f00833080000180d00c00000130002d008000a4050040407402000030000500c0504c1a004070441201435064020101200403050140001b0000100c220000b00802000a7008002205701c040340a00c0200c0800400120670000200007004380004a0000000031018070086300c0300009088080140c030090140d1701d02404000350d4100100b0000603838010010000600c02000040041b0700105c1c0540002020028040040200800008010003d00c0502000000030180b014010102a0040601017bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c87f65190eeca321df54643faa8c87755190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877
  | 3 => 0x13b9971f669511888250898dfa0a1264684d8a200001cd11b103c384e60000fa5bc8704f3b60906e0b130e8d40013a000000000000286100000033082c329b50006a4220343c4000002684244580006310a994001d10da6545d8000420b4000503827f00117a4ac00057943000000000db37a000fe8000c2000748d60581b00024e108290509e42e20006a9b700029cbd8001f28587ba424b41d0db1f6454710d60b02c614c4b1760409d0000360003440c0003ba00064099000534480003268d8258000000000000000000097800000000000001f00008ea05000000aba1015c5a00980013e919280002882a51d01f2fe1a80820245a8bc0002b4725813881c168000f991b000978000910003bca398a304295070000000009e0001fa7f84b8003540002085900000033000000000001d33283b8ea26700086c000000dc6bc000721be000fd9ce0000006725c23c819381b42940c4001141402b4802303bc0a8110ed2b4975258000d689d3114146e
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xb540c27661d50309d587540c23d65950308f990540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c34d528c830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d58c9510c3543254430d5547300c369528c03097d95300c2cc624c030d5545300c27b654c030da549300c27661d53209d58754c823e6414f208f59053c82766114f209d58453c825e63947209758e51c82ac64487208f993538823d64d4e208f990538823d6414e209d98453882756114e20cb953328832e540ca20ba58032883c8328c220ba189308832e54c82209798e544825d639512097d8d544825c63551209dd85544827461551209798e534826f6254d208f990534823d6414d209d98453482756114d2097994534831e6414d20c7590534834d6214d20d598453483556114d20d6580534826e65d0920d314f42482ea60d0920d314c424826e658c920d314e324826c654c920d314d324834c53c8520ab191214834c5348520ba1812148358538c120f28ca3048278654c120ab992204834c53881209b98b540825e63150209758c540827661150209d584540823e6414c208f590530826e6214c209d98453082756114c209e980530826d65cc8209b59432082e9600c8208fd91510823c64544208f992500823d64940209bd9520082cc63480209ed95200825e63153109758c54c426e62153109b58854c426e62d4f109b58b53c423e6494f108f59253c425e63d4b109758f52c423f6454b108f19152c426e62d52109b58b548426f6254e109b189538423e6414e108f590538426e6214e109b588538423e64d4a108f593528425f6354a109718d52842f16010610ec10640842f06150210ecd05408423e64951109dd85544423e6515110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d5244334548c5109d1953144334544c510ce15240442786550110cd152104425e63d50109758f540426e62d50109b58b540423d6595010cd185540423e64150109798c540425d63150109b988540426d62150109e980540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e6214810cd553410435553d04109d59441043555310410d554f10042796584010ce55210042776544010ad191100435553440109ed9510043395444010
  | 1 => 0xcb365494432cd552510cb365454432cd551510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb6b4254032da109500cb6a3254032da4c9500ca6f6254f419b18953d066e62943419b58a50d06ac6250e41d5986531071e5350c41ab189431074e5394841d354e521074e5354841d354d521072f4354841cb50d521072d5290841ad584421063f65504419dd95411075a5394041d654e501076a5294041da54a501075a5354041d654d501076a5254041da549501073b4354041ce50d501073a4254041ce109501073b4154041ce505501071e6395331c795143cc6cc6250f31a759032cc6d9600cb319b98b548c66d62d52319b988548c66d62152319e980548c6796015231d9986528c6e56210631bc580418c74e52cc631ad993318c66f62551319b189544c67b60551319e181544c6d66190d3197195434c6cc6250d31a7590324c6d6610c931b6580324c67665d0531b598c414c7954310531b9588414c6f16010531ad993314c6ce628c5318f990504c63d64141319b988504c66d62141319d987540c65e63150319b988540c66d62150319e980540c67960150318f992530c63d6494c3197d95310c677654c4319e98354c867960d53218f99053c863d6414f219e98053c86796014f21ab59032c86e9600cb218f99250c863d64943219798f548865d63d52219798c548865d63152219e980548867960152218f992538863d6494e21c7992538871d6494e21d59865388756534c621d394f218863e64951218f994544872d62151218f992534863d6494d218fd91534863c6454d219ed8153486786054d21cb152424866c65509219b997324872c54cc921ab590324872c540c921b998432486e9600c921cd15231486e6628c5219d1953148734544c521f10c931486ce63885219798c540865d63150219b988540867a60150219e580540866e62d4c218f990530863d6414c219d984530867a6014c219e580530865e63944219758e510866f65484219dd9521086766194f409d58653d02ac6250f40cb94a419032e5210640ae580419032e52d0240ab18943502b86050d40ae982425025e63145409758c515026e62145409b58851503566314540d558c51503374314540cd50c51503666214540d958851503364214540cd108515037160145408f997415033451d0540cd14541502ae6290140cd146405026f6254c409b189531023d6590440ae580411023f6550040ad185401027b65500409d98754cc27561d53309bd8954cc26c62553309b98a51cc26d62947309b98b548c26d62d52309dd85548c2746155230b6580328c23f64546308f191518c26e62951309b58a544c26f62551309b189544c27761551309d185544c3696014930d314b314c34c524c530d314a304c26e62d50309b58
  | 2 => 0x4015a002cabb0f80d8788880e06962961c800364750003b8008a94019adea62f2d586201342a0a7897020389dcb8b9657b9eb98b4b60409d80000332b524820b8a1fafe28ba4993a6dd000c0ab8b5886000008331a0a0000022498800cf10218208000007c27c9809e661fe2e34c9404e3d944882f40509600174308008a23200010000ca001e80029a000000032e001ee0000000142dc830000002600000112001ec1290e0019a718000000000000e8800a2b382c1b8440881497c378004913400000000001700027308000002a8b2808009b86c33126451bcd19fc4b8fe6c0006a2e400268dfabaa11f846aa225070002948500019000d983e000da9c1a2d6b2a4114c8e936c7800000007900000194118001300000026c5800ab8beb19b22a14ad51d60010c0000000000ac800dba420030ee72060eaa08629ce4976000000b8004e000018ba00000cb21c358483ca5a158127da6cbc330738d21ab7c649703518a5e000c6146c4000788fc000000218e00092678003200000156c924c9c87cb234a690a06d2808b800002d261880d3a46a32bc002fc291be00108d21581a1ba5a2745cab43ab6a302ee76876229200f24ed121a7d28ec32c060150e18244e8008db141e81e59baa2b2be001ea0293084ab6841d2002b0002000b0e4d8bac4cb78523aecdada2da0a17800a7996aaa4497b942696ec98008f000088000036060b06700ae161c2710546d80095304ec3520000000000e0288a1b3400000000f46a80023aac0a9f242ad07e80046044d619c4f1600000068230db17a0000000000dc0008f842ca340a4832ba14e002e000090341ccb38000024016800381ae1bac4be800003505b00000000001d099b9a47818000000040701c0b0040b00c0a00003038170280f0240400000024040400000401008070040000c0c0040000001050020040f010060100c03c17008010000502805054040000201c050100201c0200000030040040d0040002401000020140901c12028180000001005000000000003c150000601c040800100c03004000080101402004050041600c3d0040000c000000500001010090cc040200002c02000010040201c06000000000b0c800004000600005400024020000000c0d0000a0080000c070126e62943439b58a50d0e6e62946439b58a5190f374394643d998a5190f656294643ad9864350e3f6550c4397d954310e766194f429d58653d0aac6250f429798e5190a5d63946428fd954210a6f65508429d98754cca7561d53328fd91518ca3c64546328f992508ca3d64942329e982544ca7960951329bd89544ca7661d50329d587540ca7a60d50329e583540ca3d6595032cb189540ca3e64150329d984540ca7561150329e980540ca796015032cb553420ca6d6510832b358c420ca5f654c8329bd95320
  | 3 => 0x2c29a8845937ae61a6000dcb3038070741422c00a7aa9800ea0e63a00031b843c1d8aa3904f816799ca85906b7204360c48d3824ab686b2f80000078388c8954dd800baa960024a8395c958005a8bcc4b1c898004718c8e3203b2a43380c9f928bd99054800610000021ee3800ce988e838cc00000030a000003e800cf8001c8a60029077922002522335ed717e000000d116000004b
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xe2368800006b0000000900e2ac8000000030000000000048a0000001b4000080500000b84780400000000980000000028000b180005a07000400000000008101525cc4254032a50e4a1aa020d317110950106c23928620a63a150d6210531d2286b008298c2d7615032487142a2c019243615d0324c521e08a81926290dc1700c93148715292c020c81491c94314540a60e0a18a2a06456358851502993848428a819458d6014540c4cc428c80a064462545300c3152a2c019441855916114d20ca2c2b00a690648539834248306320a690a419214c6048520a94eb194609060e6414e20482593b682a0421851915344010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4010a808250d601053190587150324c521d00545c0324c521
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 624)*10) 10
  | 3 => packedAt s5K3 (1484+((h/9+packedAt s5K3 (1421+(h % 9)*7) 7) % 75)*6) 6
  | 2 => packedAt s5K2 (183+((h/1+packedAt s5K2 (180+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe0ff8f0fc7fff0f1c7f1f81c703fffc33c27f
  | 1 => 0x1ff1ffff007c7ff01f8fe3fff80383fccc7c4f
  | 2 => 0x1ffe00ffff8078ffe00ffc01fffc03830f8f8c
  | 3 => 0xe00000ffffff80fffff00001fffffc03f00ff0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42a0111220a82003081504904108a8c811c215
  | 1 => 0x84446020191090300482210d88311130441c4a
  | 2 => 0x4824b24648194155200b4824d2580a190e868c
  | 3 => 0x81494488904012a85520004924a25022e00960
  | 4 => 0x1189800ce26264ce9a4c927000c06043bb6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88feecfa88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36380
namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54037f5500bfc54037fd4c09fe53037f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52037f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51037f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50037f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826004fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001fe8813000ff84098007ff104c003ff0826001ff04130077feca9003aff654801dff32a4006bf99520077faca9003afd654801dfe32a4006bf19520007fec890002ff644801bff3224005bf99120007fac890002fd644801bfe3224005bf19120077fea890037fe544801dfeaa2400dff15120007fec690002ff6348019ff31a4004bf98d20007fac690002fd6348019fe31a4004bf18d20077fea690033fe534801dfea9a400cff14d2006ffe8690033fe4348001fea1a400cff10d2000dfec49000fff5248007ff2924003fb9492001ffaa49003bed5248007fe2924003ffd092006fde849000ffe4248007fea124003ff1092001fd8849000fff3248007ff1924003fb8c92001ffa6490003ed3248007fe1924000ffd8520005fec29002ffe61480057f30a4000ff5852005ff8c29000afc614801dffa8a400bff94520077faa29002ffc514801bffa0a400bff90520007fa829002ffc4148019ff98a400bff8c520007fa629002ffc3148007ff90a4003fbc852001ffc429000ffd2148001f690a4003ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001fe8c12000ffa6090003f93048003fe1824001ffc812001ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff8209001fff654400f7fb2a2007ff99510035fcca8801ffd654400f7eb2a2007ff19510035f8ca88003ff64440017fb22200aff9911002dfcc888003fd64440017eb22200aff1911002df8c88801fff5444015ff2a22007ff55110057f8a888003ff63440017fb1a2009ff98d10025fcc688003fd63440017eb1a2009ff18d10025f8c68801fff5344013ff29a2007ff54d1004ff8a68802bff4344013ff21a2000ff50d1004ff88688003ff62440017fb122008ff9891001dfcc488003fd62440017eb122008ff1891001df8c48801fff5244011ff2922007ff54910047f8a48802bff4244011ff2122000ff50910047f88488027ff3244011ff1922000ff4c910047f86488006ff6144005ffa8a2002ff94510017eca28800bfd514400ffaa8a2002ff14510017fe828800bfe4144005fea0a2002ff10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017fa428800bfc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001ff4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xbff3148405ff18a4202fd8c521017fa6290803f53148405fe18a4202ffc852101fee429080bfe2148405f710a4202ff08521017d8429080bf42148401ffb024200bfd81210bffcc090806fe6048401feb024217ff1812100df8c09086bff504842fff282421aff541210bff8a090867ff404842fff2024217ff101210c7fe609085ffe304842ffe1824203ffc812101fde409080ffe2048407fe1024202ffc4121017fc209080bfc104842dffb2a8016bfd95400b7fccaa001afe655002dfeb2a8016bf595400b7f8caa001afc65500037fb228005ffd514002ffca8a0017be545000bfeaa28016ef5514002ff8a8a0003ff63500017fb1a8015ff98d40025fcc6a0003fd635002bfe31a8004bf18d400b7fea6a0057fe535002dfea9a8015ff14d4002ffe86a0017bf435000bff21a8005ff50d400077a86a0017fc4350001ffb128000bfd89400a7fcc4a000efe6250001feb128014ff1894001df8c4a005bff5250029ff2928016ff549400a7f8a4a0017ff425000bff2128014ef9094002ffa84a0017fc425000bde2128015ffcc9400a7fc64a0003fd3250029fe1928000ffd8540005fec2a004ffe61500057f30a8000ff5854009ff8c2a000afc615002dffa8a8013ff945400b7faa2a004ffc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff105400affe62a004ffe3150001fe98a8013ff0c5400a7fe42a004ffe2150001fe90a8013ff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff405000bfda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffe60a0007fe3050003fe1828001ffc814000ffc40a0007fc2050003ff8828001ff8414000ff420a0007fc1050025ffb2a6012bfd9530097fcca9801afe654c025feb2a6012bf59530097f8ca9801afc654c001ffb226000bfd913008ffcc898016fe644c001feb226000bf5913008ff8c898016fc644c025ffaa26011ff95130097faa898047fc544c0037fb1a6004ffd4d30027fca698013de534c009fea9a6012f754d30027f8a698013ff434c009ff21a6004ff50d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c025fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013fe324c009fe9926004ff0c930007fec298002ff614c01fff30a6002bf98530007fac29803ffc614c0057e30a6012ffd453007ffca29804bfd514c01ffe28a6011ffd053007ffc8298003fd414c01ffe20a6004ffcc530027be6298013fe314c009fe98a6000f74c530027f86298043ff214c01fff10a6000ff4853007ff84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9
  | 2 => 0x41107f8c4a080efc6250445ffa928220ff94941117faa4a0883fc525040bffa128205ff9094102ffa84a0817fc4250443ff9928220ff8c941007fa64a0883fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd054102fee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff98a8202ff8c541017f862a080bff2150405ff10a8202ff08541007fec0a0802ff605043fff3028201bf98141007fac0a087ffc60504037e3028222ffd41410fffca0a088bfd505043ffe2828205ffd014102f7e80a0817fe405040bfe2028221ffcc1410fffc60a087ffc3050441ff902821fff881410fff840a080bff1050405ff0828202ff041410f7feca9887aff654c43dff32a6206bf995310f7faca9887afd654c43dfe32a6206bf19531007fec898802ff644c43bff3226205bf99131007fac898802fd644c43bfe3226205bf191310f7fea898877fe544c43dfeaa2621dff15131015fec698813ff534c409ff29a6204ff54d31027f8a698813ff434c409ff21a6204f790d31027fa8698803dd434c409fe21a6200ffd8931005fec498873fe624c4077f3126200ff589310e7f8c49880efc624c43dffa92621cff949310f7faa498873fc524c43bffa12621cff90931007fa8498873fc424c409ff9926204ff8c931027fa6498813fc324c4057fb0a6202ffd4531017fca29880bfd514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017ec429880bfc214c401ffb026200bfd81310dffcc098806fe604c401feb02621bff1813100df8c09887bff504c437ff282621eff541310dff8a098877ff404c437ff202621bff10131027fe6098813df304c409ff1826204ff0c1310e7fe409886ffe204c437fe1026202ffc4131017ee209880bfe104c405fe082621affd95210d5feca9086bfe654840d7f32a421aff595210d5faca9086bfc654840d7e32a4200ffd9121005fec890803bf64484015fb224219ff9912102dfcc890803fd64484017eb224219ff1912102df8c890803bc644840b5e322421affd51210cffca89086bfd5448433fe2a24200ffd8d21005fec690863fe63484097f31a4200ff58d21005fac690863fc63484097e31a421affd4d210c7fca69086bfd5348431fe29a4219ffd0d210c7fc8690803fd4348431fe21a4202bfd892101ffea49080ffe5248407f72924203ff549210d7daa49080ffc5248407ffa124203ff9092101fdc849080ffd4248401f6a124203ff1092101ffe6490863ef3248407ff1924203ff4c92101ff8649080fec32484057fb0a4202ffd4521017fca29080bf65148405fea8a421afd54521017f8a29080bff4148405ff20a4202ff50521017f8829080
  | 3 => 0xf2028605ff10143027fe60a1813fe3050c09fe182862dffc814315ffc40a18affc2050c59ff882862bff8414315ff820a18abff65508557fb2a842aff99542035fccaa10abfd65508557eb2a842aff19542035f8caa100eff645080bffaa28405ff9514202ffaa8a1017fc5450801ffb1a8400bfd8d4214ffcc6a1012fe6350801feb1a8429ff18d42025f8c6a10abff5350853ff29a842aff54d4214ff8a6a1017ff435080bdfa1a8405ff90d4202ffa86a1003bd435080bfe21a8403bfd894201ffea4a100ffe5250807fea928403ff1494201ffe84a1017ef4250807ff2128403ef9094201ff884a100fbc4250807f62128403ffcc94201ffc64a100ffc3250801ffb0a8400bfd8542147fcc2a100afe6150801feb0a8428ff18542015f8c2a10abff5150851ff28a842aff54542147f8a2a1017ff415080bff20a8405ff1054214ffe62a10a3fe3150851fe18a8403ffc854201fde42a100ffe2150807fe10a8400ffd8142005fec0a109ffe60508037f3028400ff5814213ff8c0a1006fc6050855ffa828427ff94142157faa0a109ffc505080bffa028405ff9014202ff880a10a7ff305084fff1828427ff0c14201ffe40a100ffe2050807fe1028428ffc414213ffc20a109ffc105084dffb2a6426bfd9532137fcca9901afe654c84dfeb2a6426bf59532137f8ca9901afc654c801ffb226400bfd913212ffcc899016fe644c801feb226400bf5913212ff8c899016fc644c84dffaa26425ff95132137faa899097fc544c8077fb1a6404ffd4d32027fca699013fd534c809fe29a6404ffd0d32027fc8699013fd434c809fe21a6403bfd893201ffea49900ffe524c807fea926403ff1493201ffe849900ffe424c807fea126403ff1093201ffe6499013ef324c807ff1926403f78c93201ff8649900fdc324c807f61926400ffd8532005fec299093fe614c8057f30a6400ff58532127f8c29900afc614c84dffa8a6424ff94532137faa299093fc514c84bffa0a6424ff90532127f88299013ff314c809ff18a6404ff0c53201ffe429900ffe214c807fe10a6400ffd8132005fec09908ffe604c8037f3026400ff5813211ff8c099006fc604c84dffa826423ff94132137faa09908ffc504c84bffa026423ff9013211ff88099013ff304c809ff1826404ff0c13201ffe409900fef204c807ff1026403ff08132127fe209908ffe104c847fe0826422ffd9541115fecaa088bfe655040d7f32a8222ff59541115facaa088bfc655040d7e32a8202bfd914102ffea8a0817fe545040bfeaa28205ff15141007fec6a0802ff6350443ff31a8204bf98d41007fac6a0887fc63504097e31a8222ffd4d4110ffca6a088bfd5350443fe29a8205ffd0d4102ffc86a0817fd435040bfe21a8200ffd8941005fec4a0883fe62504077f3128200ff589
  | 4 => 0x210000000000000064a8287aa5a3e20000000035256000196220000f835f57200000201000001300006b07684500000000015000000000000e2000bd80019b486000000f40000000029e000dc9ce8e5000af85e0fc3a05dcb015b000001951eb468470541275dc5118039b1b293800000000000000000000a0d38000000edb985e520ab8b418a66a07c000a741c000d107235edfc002c576c000000003d800180800340ec40a8f14805f4000020050020000300701a0100100100000c0100200200400007014040010070000000280f002030078000000140100000401c010040040000b0010040480300000000002008000020008000000080700e00001c038010100000180b0020040000500400c0100300601c0180600c004000030100000080500000c0080b0020080200700001001005008038030010000040080101000c0080100602000000004008000000020080000100000c0080002a0000000000000800006002008008020000080280d00000c0980200c0040000200a03c000000000040000000000c0080200201000005000004008060040000680000e0200081e036020000000000000080200601000007004004008070000000900b0040480080100201c0000200000000000002000010190000000000000400001004024004028010040000780400a01400000008008090210000100200200203c0480a00000c000070280000000100400005002008000028060020200100400400c04002000008000000040140500900400c018030100080080300000c038000020000000b00001c000120000080000000001c0000000000800000002014008000020100000100c000008020002effd9543175fecaa18bbfe6550c0d7f32a862eff59543175facaa18bbfc6550c0d7e32a8604bfd914302ffea8a1817fe5450c0bdf2a28605ff551431777aa8a1817fc5450c097fb1a8604ffd4d43027fca6a1813de5350c09fea9a862ef754d43027f8a6a1813ff4350c0befa1a8604ff90d430277c86a1813fc4350c09de21a8604f710d43007fec4a1802ff6250c01f7b128600bbd894316ffcc4a180efe6250c01feb12862dff1894301df8c4a1803ec6250c0776312862effd494316ffca4a18bbfd5250c5bfe2928605ffd094302f7e84a1817fe4250c0bfe2128604ffcc943027fc64a1813fc3250c01ffb0a8600bfd8543167fcc2a180afe6150c01feb0a862cff18543015f8c2a18bbff5150c59ff28a862eff54543167f8a2a1817ff4150c0bff20a862cef9054302ff882a1817bc4150c09ff98a8604f7cc543027fc62a1813fc3150c5bff90a862cff88543167f842a1803ff6050c017fb02862bff9814300dfcc0a1803fd6050c57fe3028601bf18143177fea0a18affe5050c5dfea82862bff1414302ffe80a1817bf4050c0bf
  | 5 => 0x3480000004f3c718e1ace10000000000001a0b0a4dbbb23000000002e200000089800786c8075000000001ba0d50005c008b3c4760000025100004d9f000000001ddb4b20a001cbbc5186338000fb4e8371c6894354000000000ce000002a536e000e40ee33ce25d48ad22ae8154b6a45eb9876000398e9d76209206b05191bc46036800000172a2c0000044cdb427a8e03a545748004ce024219c92ca564000000001fc5f0a2000000970000000d1863a105cce4cf8003c4139ada8c58432cee20b12cbe0002b348cc980002217e34150000770de83d2682da115c50642980010b000000ebcbd2ff0641003bb9a2280000023e748800001ea0ae0000000059c2c92680011814800000000ab4003420002d89233600000000308310418001200000000018d11296400000000000520003f6000001123640f800000000000000000041a94e0001c20016934a0008700006965a00000121108d44000000da1113c8de386d1800000000b700000016855d158a5000000e280015646c2a8000000000000050e6b10f8350000007980030c7b80007d4e2650d7000000000fe9563a63c00000061c8408384d4ae79c318aa58e92c4c8735646900a31119a610003c4426e482b12b5943186906f570d98261f801e97d7a1414dc0000000007e000001433e61259a1740005540013c28c4200000000000000026000145c0000746460ef000000391243865f40012aab600008c1b1b32fe4e46100031caf00426b3323fdd290b07aa88800002e6ccd02800000000000003de018000000003140000000000131bbf76000000000356000a80000006e00031e0000001bb32170001b1000502ea800000000c840000079200000395000a98c385a0009d40b8000000000000063024488b56194000003ad12a0000003a720000000000180bc001470008099d0000008fcce19740e0015faba2d848d4c80000091c0004b1520000000061ae50eeaf9660995308860c4df5b4000000860000006b8c1851b96560e3d0bab40527e582000542001af000362000c0800360000000000008b568800434d307c3991fa4e985378000000609a100000184b8e1a85893c14929ab309537b588064080126920010680000064000000000000b30007789a8fe3710005487590a0004fc0015e00000181000000c88000000000000000011e000b18000000002c8000000000002d000ce0000007163f8ec9b4276669d717b5a68190e9ad57a9057a931000000660006c873976bba5c69913d00077c7f94e800466c64dc83c176e08472236866493903903c3250aaf73d0a3d6a861312c3ceda223ca001b4800396e200024500080d65a140f6cfc7b27c74400175a310002343f00053e7d000000000001468006345bc0000000000000000000d48003280002cd7435a0e2528000004ec488620
  | 6 => 0x83127ac34d809c8f2277984d9e02de03077c2511a5f692557a9a37a4c09ea69432a59a70c001600151ad860e7e800000000c7c002ef3740004da820827442e3054b80016b0ef46a89041093688ecc00024616949c208700066084b654fa015488600001d450000576eb045a040000000000000000000000000000e91856a8001311cd13a87800000722bc029a36606000000002700000037c000d059eb150001d80000034aa4800134590e4c5780000084579acf38e60c2eae7394320741d74de78d398382f843d7527f2023b4002391748b94502b512b900000020836c003986f23c94a8bd0000000000000000000000000000001485544b4fa800000f04f300000040800000000000e00000000000000024c000c10001ba00000000000c5ca0313000dd82d916790ee44181b2e40001800000000000020000d4c0000000000000000000db80683300017c00090000094003c63e400000000000000e791f00096d3b80000000000329718000000316ce000bb14b000a6000137000000000002520000039f01c000b399514c3e8e2046638ea0002dd000001160000f826000000000a0c74b81000000000000000000000029ca20000000005e4000006d800000000350000000000a83dc003705c2590eb0005e4000daa380000011034d5a8000ba80062c0000032c4a0edc589805280000008166e8e93f27b13400000000000000000000000004faa80385c436000264000c7adf000d8c003831c600c490000000000032e0004340009c0004740035005833c002976fc00000000000000bc0002bad01baa5d00000000000258001298000000017ea2100000000000000001221693820008c80054eb6cf098b454398e3000000000002e5000ef40000064e000003241a6a180b000000001e58000d000038000000001893850008f4a136f000ec8db0d73feb400013e37eb34c60b03c8d3d6d0000008a5700666ae0011e0000005f80000000000142a5800020024000250000d1ac670e3e5da1536c0a6d07b4537c69914242000ced6cb9c3ec8493680759253c6c16a4e0000ec28433a2dc3c00025e1e4aa1e01acbf1600d1556c75252080004d4000000000000002100000000361322a908bb1b4cc00000000000ed4000000005adae8006aacc4001bb74cbf8002b10e8dada38b53dab5d12800620514000501ce57042ab74ac0003715f158a004bb593d24319795a1425b887125498754052ac0080012f1611be4cc70000000000000003eef09e53ab62800195b9e08e00400193110000ea25400086c5706556a000000005e28dc0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d101cedf31d8d101cedd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d101bedf30d8d101bedd30d8d10024ff7658d1004edc6358d101b5f77158d101c5fb7058d10004ff7558d10034fe7558d10004fd7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d101bcff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d101b4ff7158d10006f77158d100dcff7058d10006fb7058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10006bf6450d1002ebc6450d10005ef7250d10045ec7250d1001cfe76d8910046ee62d8910004ff75d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100bcfd72d891000cff71d8910014fe71d891000cfd71d8910014fc71d89101aef651d8910006f551d89101aef631d89101aeef21d89101aeed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891019eef20d891019eed20d891001cff76589100057f755891003d7c7558910005bf7458910055bc7458910005df735891004ddc7358910046ec6258910195f771589101a5fb7058910004ff75589100067f75589100047f7558910034fe7558910004fd7558910034fc75589100067c75589100347c7558910004ff7458910006bf7458910004bf745891002cfe745891002cfc7458910006bc745891002cbc7458910004ff7358910006df7358910004df7358910024fe7358910024fc7358910006dc7358910024dc735891019cff7258910006ef7258910046ee5258910006ed5258910194ff7158910006f7715891005ef65158910006f5515891005ef631589100bcff7058910006fb7058910004ff7650910004fe7650910004fd7650910004fc7650910004ff764c910004fe764c910004fd764c910004fc764c91000df4764c510026f4764c51000cf4764c51018df7754c51018df5754c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c51004fd4634c51004fd6434c510007d5434c510006f7624c510006f5624c510007f3704c51000df6704c51000df4704c5100dff0704c510016f7604c510017f3604c5100dff2404c5100dfd7304c5100dfd5304c510015f8765011002ef87650110014f8765011000dfb745011000fbb7450110007bb645011002efa645011002ef86450110057b86450110057ba545011017fb95450110057bb4350110007b94350110187ba4250110057b84250110007f37150110015fa7150110015f8715011009ff0715011000efb615011000ff3615011009ff2515011017ff1515011009fbb415011009fb9415011009ff23150110007f13150110
  | 1 => 0x8520004ff75d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d852021eee52d8520006ed52d852005ef621d852021ef521d852000cfe70d852001cfd70d852000cfc70d8520196f710d85200057f75585200757c7558520005bf745852006dbc7458520005df7358520065dc735852005ef46158520215fb7058520004ff7650520004fe7650520004fc7650520005ef725052001dec7250520004ff764c520004fe764c520004fc764c52001dee724c520016f6614c52000dec7648520016ec764852000cec764852020def754852020ded7548520206ef6548520206ed6548520007af744852006dee744852006dec7448520007ac744852006dac7448520006ef6448520006ed6448520005ef7348520005ed73485200c6ee63485200c6ec634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe65148520207e5514852005fe63148520007e53148520007eb704852000dee704852000dec70485200bfe8704852001eef604852001feb60485200bfea304852001df8764c120026f8764c12001cf8764c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120067da534c1201ffd9534c120007eb724c12001dfa724c12001df8724c120087e8724c12000efb624c12000feb624c120087ea524c1201ffe9524c1201f7eb424c120087e8424c120087ea324c120067e9324c120067db314c120007d9314c120087eb214c120007e9214c12002cfe76d9110056be64d9110004ff75d9110034fe75d9110004fd75d9110034fc75d91100fcfd74d9110006bf54d9110056bc54d9110024fe73d9110004fd73d9110024fc73d9110056bf43d911001cfe72d9110004fd72d911001cfc72d9110006be42d9110056bc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d91101eebf41d91101eebd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91101debf40d91101debd40d911002cff76591100057f755911003d7c7559110056bc64591101d5f771591101e5fb7059110004ff75591100067f75591100047f7559110034fe7559110004fd7559110034fc75591100067c75591100347c75591101dcff7459110006bf7459110004ff7359110024fe7359110024fc7359110004ff725911001cfe725911001cfc72591101d4ff7159110006f771591100fcff7059110006fb7059110024fe76d8d1004ede63d8d10004ff75d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100dcfd73d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10006de32d8d1004ed
  | 2 => 0x27d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6214c530007db704c53000dde704c53000ddc704c5300dfd8704c530026df604c530027db604c5300dfda204c5300dfd7104c530004ff7648530004fe7648530004fc7648530005bf744853008dbc7448530006ef624853001eec6248530007d5314853002cfe76d912006ebe64d912001dee72d912000ded72d912006faf42d9120004ff75d9120034fe75d9120004fd75d9120034fc75d912013cfd74d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d9120256ed72d912000ced72d912001cfc72d9120266bf42d912006eef42d9120266bd42d9120266ec42d9120014fe71d9120004fd71d9120014fc71d9120006be41d912006ebc41d9120266ef21d912001cff70d912001cfd70d9120256bf40d9120256bd40d912002cff765912006ebc645912024def72591200a7ac425912025dfb7059120004ff7559120034fe7559120004fd7559120034fc7559120254ff7459120006bf7459120004ff7359120024fe7359120024fc735912006ebf435912024cff7259120006ef725912006eef42591200a6be42591200a6bc42591200a6ec4259120004ff7159120014fe7159120014fc71591200a6ef215912013cff7059120006fb7059120024fe76d8d20066de63d8d20004ff75d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2011cfd73d8d20006df53d8d20066dc53d8d20066de43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d20246df32d8d20246dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20066dc31d8d2001cff70d8d2001cfd70d8d20236df30d8d20236dd30d8d20024ff7658d200057f7558d200757c7558d20066dc6358d2022def7258d2023dfb7058d20004ff7558d200067f7558d200047f7558d20034fe7558d20004fd7558d20034fc7558d200067c7558d200347c7558d20004ff7458d2002cfe7458d2002cfc7458d20234ff7358d20006df7358d2022cff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2011cff7058d20006fb7058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2002ebe6450d20006bd6450d20006df6350d20026dc6350d20005ef7250d2001dec7250d2006faf4250d2000dec764c920026ec764c92000cec764c920225ef754c920225ed754c92006dee744c92006dec744c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920026cc634c920005ef714c920007eb704c92000dee704c92000dec704c92011fe8704c92001eef604c92001feb604c92011fea304c920014fe76d852005ef661d
  | 3 => 0xb705854000dbc7650540016bc765054000cbc76505402b5bf75505402b5bd7550540005bf73505400a5be72505400a5bc725054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb46150540016b46150540007bb705054000dbe705054000dbc70505400ffb8705054002ebf605054002fbb60505400ffba1050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540026de634c5400079d434c540004ff7648540004fe7648540004fc7648540005bf744854002dbc744854001eee62485400a7ae4248540006f76148540016f4614854002cfe76d913008ebe64d9130004ff75d9130034fe75d9130004fd75d9130034fc75d913015cfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d91302aede53d9130006dd53d91302aebf43d91302aebd43d913001cfe72d9130004fd72d913001cfc72d9130014fe71d9130004fd71d9130014fc71d91302aedf31d9130024ff70d9130024fd70d913029ebf40d913029ebd40d913002cff76591300057f75591300957c755913008ebc6459130295df7359130005ef7259130085ec7259130005f7715913007df471591302a5fb7059130004ff75591300067f75591300047f7559130034fe7559130004fd7559130034fc75591300067c75591300347c755913029cff7459130006bf745913008ebe5459130006bd5459130294ff7359130006df73591300aede5359130006dd5359130004ff7259130006ef7259130004ef725913001cfe725913001cfc7259130006ec725913001cec7259130004ff7159130006f77159130004f77159130014fe7159130014fc7159130006f47159130014f471591300aedf315913015cff7059130006fb705913001cfe76d8930086ee62d8930004ff75d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930006ef52d8930086ec52d8930006ef42d8930086ec42d8930086ee32d893028eed32d8930014fe71d8930004fd71d8930014fc71d8930086ef21d8930024fd70d893022eef20d89300057f75589300957c7558930086ec6258930285fb7058930004ff7650930004fe7650930004fc7650930014fe76d853007ef661d8530004ff75d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d8530006f741d853007ef441d853007ef631d853027ef531d8530024fd70d85301b6f710d853007ef46158530275fb7058530004ff7650530004fe7650530004fc765053000ddc764c530016dc764c53000cdc764c53026ddf754c53026ddd754c530006df644c530006dd644c530025df714c530
  | 4 => 0xc52101df6724c52101df4724c5210e7e4724c521016f7624c521017e7624c5210e7e6524c5212ffe5524c5210e7e6424c521007e5424c5210c7e7324c5210e7e4324c5210c7d7304c5210e7e7204c52100cfe76d8121006bf64d8121006bc64d81210befa60d8121004ff75d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d8121216ee52d8121006ed52d812101cfd71d812100cfc71d81211a6f651d8121006f551d81211a6f631d8121006f531d81210befa20d81210befa10d81210057f75581210d57c7558121005bf74581210cdbc7458121006bf6458121006bc6458121005df73581210c5dc73581210bef86058121024fe76d8d400aede63d8d40004ff75d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d402f6be54d8d40006bd54d8d400aede43d8d402f6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d4002cfd70d8d40296df30d8d400057f7558d400b57c7558d400aedc6358d40005ef7258d400a5ec7258d40005f77158d4009df47158d402edfb7058d4000dbc7650d40026bc7650d4000cbc7650d402e5bf7550d402e5bd7550d402debf6550d402debd6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400af9e5350d402df9d5350d40007af7250d400a5be7250d400a5bc7250d40007ac7250d400a5ac7250d40005bf7150d40166be6150d40166bc6150d400af9f3150d40007bb7050d4000dbe7050d4000dbc7050d4015fb87050d4002ebf6050d4002fbb6050d4015fba1050d4001cfe76d894002dbe74d894000dbd74d89400a6ee62d89400a7ae42d8940004ff75d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894024ebd74d894000cbd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89402d6bf43d8940006bd43d89400a6be42d89400a6ee42d89402d6ed42d89400a6bc42d8940006ef32d89400a6ec32d8940014fe71d8940004fd71d8940014fc71d894002cfd70d894024eef20d89400a6ec62589400a7ac42589402cdfb7058940004ff764c940004fe764c940004fc764c940005bf744c94002dbc744c940014fe76d854009ef661d8540004ff75d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d854001cfe72d8540004fd72d854001cfc72d8540006f751d854009ef451d854009ef641d85402c6f541d8540006f731d854009ef431d854009ef621d854002cfd70d85401d6f710d85400057f75585400b57c755854009ef461585402bdf
  | 5 => 0x6bc30d9121366bf20d9121366be20d9121366bd20d9121366bc20d912134ebf10d912134ebe10d912134ebd10d912134ebc10d912102cff76591210cebc6459121355ef725912135df77159121004ff7559121034fe7559121004fd7559121034fc755912134cff7459121006bf7459121004ff7359121024fe7359121024fc7359121354ff7259121006ef7259121144ff7159121006f77159121004ff705912100cfe705912100cfc705912134dbe76191210cebe761912134cbe7619121006bf6519121006be6519121006bd6519121006bc6519121006be6319121006bc631912133fae7219121347ad7219121346bf621912133fae5219121007ad5219121007af321912133fac3219121346bf6119121347b65119121007b55119121347b6311912133fb72119121347ae2119121347ac2119121347b42119121006be6019121006bc601912133faf2019121024fe76d8d21006bf64d8d21006bc64d8d210c6de63d8d2101dee72d8d21015ed72d8d210c7cf32d8d21004ff75d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21124fd73d8d210c6de53d8d21006dd53d8d21014ff72d8d21014fd72d8d21326ed72d8d21014ed72d8d21336df32d8d210c6ef32d8d21336dd32d8d21336ec32d8d2101cff71d8d2101cfd71d8d21326df31d8d21326dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d210c6dc30d8d21336ef20d8d21024ff7658d21005bf7458d210cdbc7458d21006bf6458d21006bc6458d210c6dc6358d2131def7258d2132df77158d21004ff7558d21034fe7558d21004fd7558d21034fc7558d21004ff7458d21006bf7458d21004bf7458d2102cfe7458d2102cfc7458d21006bc7458d2102cbc7458d21324ff7358d21006df7358d2131cff7258d21006ef7258d210c6ef3258d210e6ec3258d21124ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d210e6ef2058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2102ebc6450d21005ef7250d2101dec7250d21015ec765092102eec7650921014ec7650921315ef7550921315ed755092101def745092101faf7450921007af645092102eee645092102eec64509210cfac64509210c5ee73509210c5ec73509210cfaf4350921007ad4350921007e77150921015ee7150921015ec7150921147e4715092101eef615092101fe76150921147e6515092130fe55150921147e63150921005ef705092101df4764c521026f4764c52101cf4764c521305f7754c521305f5754c521007b7644c521007b4644c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210c7d4634c5210c7d6434c521007d5434c521007e7724
  | 6 => 0xf7450d310079f6450d3102ede6450d3102edc6450d310ef9c6450d310ef9e5450d3137f9d5450d31007cf7250d31007cc7250d310ef9f4250d31007d77150d31015de7150d31015dc7150d31167d47150d31026df6150d31027d76150d311679e4150d311679c4150d31167d62150d31005df7050d310ef9f4050d31167d71050d3101cfe76d89310e6ee62d8931004ff75d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931006ef42d89310e6ec42d89310e6ee32d8931376ed32d8931024fd71d893131eef21d893100cfe70d8931004fd70d893100cfc70d8931005bf74589310edbc74589310e6ec625893136df77158931004ff7650931004fe7650931004fc76509310079d435093100cfe76d81310defa60d8131004ff75d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131024fd71d81310defa30d81310defa10d81310def8605813102cfe76d91210cebe64d9121004ff75d9121034fe75d9121004fd75d9121034fc75d9121144fd74d9121006bf54d91210cebe54d9121006bd54d91210cebc54d9121024fe73d9121004fd73d9121024fc73d91210cebf43d9121006be43d91210cebc43d9121014ff72d9121014fd72d9121366bf42d9121366bd42d912101cff71d912101cfd71d912134ebf41d912134ebd41d912100cfe70d9121004fd70d912100cfc70d91210cebf40d9121006be40d91210cebc40d9121345be76d912102cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006be63d9121006bc63d912134faf72d912134fac72d9121367ae52d9121007ad52d9121007af32d9121367ac32d912134fb651d9121007b551d912134fb631d9121367b721d912134fae21d912134fac21d912134fb421d9121006be60d9121006bc60d9121367af20d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d912134ebf72d9121366be72d912134ebd72d912134ebc72d9121366bf52d9121366be52d9121366bd52d9121366bc52d9121366bf32d9121366be32d9121366bd32d9121366bc32d912134ebf71d912134ebe71d912134ebd71d912134ebc71d912134ebf51d912134ebe51d912134ebd51d912134ebc51d912134ebf31d912134ebe31d912134ebd31d912134ebc31d912134ebf21d912134ebe21d912134ebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006bf30d9121006be30d9121
  | 7 => 0x913200cfe705913200cfc7059132014fe76d8532126f661d8532004ff75d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d853236eef32d853232eec32d8532126f631d8532126f621d853200cfe70d8532004fd70d853200cfc70d853232eef20d8532005bf745853212dbc7458532126f4615853200cfe76d813211efa60d8132004ff75d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d813211efa30d813211efa20d81320057f75581321357c755813211ef86058132024fe76d8d4110ede63d8d41004ff75d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4110ede43d8d413bedd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4102cfd71d8d41386be41d8d41386bc41d8d41386df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d413bebf40d8d4110edc6358d41005ef7258d41105ec7258d413b5f77158d4101cfe76d8941106ee62d8941004ff75d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941106ee42d89413aeed42d8941006ef32d8941106ec32d894102cfd71d8941356ef21d894100cfe70d8941004fd70d894100cfc70d8941106ef20d8941106ec62589413a5f77158941004ff764c941004fe764c941004fc764c94100cfe76d81410fefa60d8141004ff75d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814101cfe72d8141004fd72d814101cfc72d814102cfd71d81410fefa40d81410fefa10d81410057f75581411157c75581410fef8605814102cfe76d91310eebe64d9131004ff75d9131034fe75d9131004fd75d9131034fc75d9131164fd74d9131014ff73d9131014fd73d913139ebf43d913139ebd43d913101cfe72d9131004fd72d913101cfc72d9131006be42d91310eebc42d9131024ff71d9131024fd71d913138ebf41d913138ebd41d913100cfe70d9131004fd70d913100cfc70d913102cff76591310eebc6459131385df7359131005ef72591310e5ec7259131395f77159131004ff7559131034fe7559131004fd7559131034fc755913138cff7459131006bf7459131384ff7359131006df7359131004ff7259131006ef7259131004ef725913101cfe725913101cfc7259131006ec725913101cec7259131164ff7159131006f77159131166be4159131166bc4159131004ff705913100cfe705913100cfc70591310eebf4059131015dc7650d3102edc7650d31014dc7650d3137edf6550d3137edd6550d31025df7450d310279
  | 8 => 0x166bc41d8543166f631d854300cfe70d8543004fd70d854300cfc70d85433b6bf40d8543006f610d8543166f410d8543005ef725854316dec7258543006ef6258543006ec6258543166f4615854300cfe76d8143006ef62d8143006ec62d814315efa60d8143004ff75d8143034fe75d8143004fd75d8143034fc75d8143024fd74d81432eebe54d8143006bd54d814302cfd73d81432a6de53d8143006dd53d814301cfe72d8143004fd72d814301cfc72d8143014fe71d8143004fd71d8143014fc71d81432a6df31d814315efa40d814315efa30d81430057f75581431757c7558143005ef725814316dec7258143006ef6258143006ec6258143005f77158143165f4715814315ef86058143024fe76d8d4214ede63d8d42004ff75d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4214ede43d8d423f6dd43d8d4202cfd72d8d423cedf32d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d4214edc6358d423edef7258d4201dbc7650d42026bc7650d4201cbc7650d423e6bf6550d423e6bd6550d4202dbf7350d4202f9f7350d420079f6350d42026be6350d42026bc6350d4214f9c6350d4214f9e5350d423e79d5350d42007af7250d4201dbe7250d4201dbc7250d4216fac7250d4202ebf6250d4202faf6250d42166be6150d42166bc6150d4214f9f3150d4216faf2150d42014fe76d8542146f661d8542004ff75d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542146f641d8542146f621d854200cfe70d8542004fd70d854200cfc70d8542146f4615854200cfe76d814213efa60d8142004ff75d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d81422cebf43d8142006bd43d814202cfd72d81422ceef42d814225ebe42d814225ebc42d814225eec42d8142014fe71d8142004fd71d8142014fc71d814225eef21d814213efa40d814213efa20d814213ef8605814202cfe76d913212ebe64d9132004ff75d9132034fe75d9132004fd75d9132034fc75d913216cfd74d913201cff73d913201cfd73d91323debf43d91323debd43d9132024ff72d9132024fd72d91323d6bf42d91323d6bd42d9132014fe71d9132004fd71d9132014fc71d9132006be41d913212ebc41d913200cfe70d9132004fd70d913200cfc70d913212ebf40d913202cff765913212ebc64591323cddf73591323c5ef7259132004ff7559132034fe7559132004fd7559132034fc75591323d4ff7459132006bf74591323ccff7359132006df735913216cff7259132006ef72591323c4ef7259132004ff7159132014fe7159132014fc7159132004ff705
  | 9 => 0xe00001500000e00000d00f00200400600b00400000500100b00100001900700000500100500300400700300100100001a01900500600001700300000c00600300200900200800000000000b03100000c00201cfe76d894316eee62d8943004ff75d8943034fe75d8943004fd75d8943034fc75d8943024fd74d894302cfd73d8943006ef52d894316eee52d8943006ed52d894316eec52d894316eee42d894316eee32d8943014fe71d8943004fd71d8943014fc71d894316eef21d8943006ee21d894316eec21d894300cfe70d8943004fd70d894300cfc70d894316eef20d8943006ee20d894316eec20d894316dee76d894301cee76d8943006ef65d8943006ee65d8943006ed65d8943006ec65d89433c7af74d89433c7ac74d89433efae54d8943007ad54d89433c7ce53d8943007cd53d89433efcf43d89433c7ae43d89433c7ac43d89433c7cc43d8943006ee61d8943006ec61d8943007ae41d89433efac41d89433c7cf31d8943006ee60d8943006ec60d89433efaf40d8943006ef75d8943006ee75d8943006ed75d8943006ec75d89433c6ef74d894316eee74d89433c6ed74d89433c6ec74d89433eeef54d89433eeee54d89433eeed54d89433eeec54d89433c6ef73d894316eee73d89433c6ed73d89433c6ec73d89433c6ef53d89433c6ee53d89433c6ed53d89433c6ec53d89433c6ef43d89433c6ee43d89433c6ec43d8943006ef71d8943006ee71d8943006ed71d8943006ec71d8943006ef51d8943006ee51d8943006ed51d8943006ec51d89433eeef41d89433eeee41d89433eeed41d89433eeec41d89433c6ef31d89433c6ee31d89433c6ed31d89433c6ec31d8943006ef70d8943006ee70d8943006ed70d8943006ec70d8943006ef50d8943006ee50d8943006ed50d8943006ec50d89433eeef40d89433eeee40d89433eeed40d89433eeec40d89433c6ef30d89433c6ee30d89433c6ed30d89433c6ec30d8943006ef10d8943006ee10d8943006ec10d894316eec62589433c5ee761894316eee7618943006ef6518943006ee6518943006ed6518943006ec651894316fae741894316fad74189433d6ef64189433ffae5418943007ad54189433ceef6318943407ce5318943007cd53189433ffcf4318943407ae4318943407ac4318943407cc4318943006ee6118943006ec6118943007ae41189433ffac4118943407cf3118943006ee6018943006ec60189433ffaf4018943014fe76d854302dbe74d8543025bd74d8543006ef62d8543006ec62d8543166f661d8543167b641d8543004ff75d8543034fe75d8543004fd75d8543034fc75d8543024fd74d8543166bd74d8543024bd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d8543166f651d8543006f551d8543166be41d8543166f641d8543
  | 10 => 0x20007f2c52000be05d800067649c000cc893e12017ece4000266818000000048000000000cfa67096e000000b7a62a288000b86000000d00000000a50a9c7aa000000c888fc364ab24fc506000910814b3c0dec5887ea5ca0cd0622c5700606bc000000a8e12c6182047a846a48e2c47724d28e8604aee2b498806a4d8398430a3e0000003acbbc9cc4a23b466279c2069e46b80005642440000007bea2aabcc685bc16c000b62d2eb6cac209e6e832c6b60c216000040626e102782caeae2c60560000afc2961be72abb0bf8000ba45daa4ab2a452b2c796d0c0009ee0029fab7652e0002cc8beb74b5e3d29168081d800008c08687a28c000a842486b40ca8dc6be0d800201600100300500701201100b00100500000b00000c00a00700100301f00c00100103700f00e04900200100000100000200000100100200100001000400500000000300000d00800300003700500800200000001000200900900400900000700500000200000200400b00000100700f00f00900900000001400c00200900100200900700000000100500000000e01b00001500200100000000200300000300000000000000500b00b00800200000000000500101400800000600000000600001700000100300000a01600000000300000f00601701300500900100000200000300300000000200000000800300901200200800000300400600200400400500400000300000300400000a00100000200000000700000b00600100000000000100800101e00600000000400500100a00400200000100e00100000300100301900300500300100100000000a00400b00002d00500000300000400400500400000300300500700200100200100200500400000101200900c00000a00200400200100202300200300a00000002400000100100801300300a01300501400000802d00001800200d00300100400100000703200500000600100400200200400600400500200603600400600201402000300200201e00600200100d00300001000000d04200102a00500100000001102000000201600f00a00600000000300100f00100700000800600200402300101100000000100000100000400800800200300100400000100300100000400000000100101500900100100300f00200c00c00900100000100101100100200200800500700000700200200600000000d00601101800000300600900300400000b00700100200100300000000a00700300400500000900000400000100900100400600600000e00400100800000701200100000000000100300a00000000400100500200b00601100200e00400000300000100300300000400400000000000402601000400000400001200700200102000000000000300a01800100c00000500600000000400100300101200301b0000010
  | 11 => 0x8aab44b10164290000008000c0acc0cf20000000005a4000832052898adc3ec2c011a6888aea382aa0ea80ec469262ec83657ec965004b0b42cda912684018544cb4bde3d4bac3f23a4afe4345960002f404c0000d0440000a4409854a00077009c69a97a6ca0000000000007e492c80682ebdcbfe1e87188c4b403e412e000000000bd8d0a9140008c27169c0482422890a22000a3c0008ac49ac76b58cd6638000000bfc34821651a82a3685c8aaa000000c62b9481072c986000c023460000009b4612c725e084e5f262ed1a000a6cd0e5a80005d0d1025e53612a90e3c6bd00e03502f60004f00b678a7980960006c61c636e2d469c2384aca7427a270a2446400048c000c42000a0e000a1ab7c05c0006960000000009a668e76c648c809ec5c46407ba1d0c5eb8833c95c5bec4480a6cccce8e0234a344f27481061c27841225fa0007544e00005c245e7c43d076e3b606493a0007f400055400031447200075c2740708b291a0004ee000a9a5ce21c0e411ec208b8446c1a00091cc2200032040a9e681e4860001409e0000aae9dc78cc5627888e7687b455896600000067a4201f241a86a0fc2e2cd40007d47d87b000084c0000000006305ba59207a50eb5c19a74ad2273a70a59089e4ba8585c0000a0abf6310c16c1c7385949940000000000be8880002269c8000000000480ce87325c6b8e69ecba5861fc19eb4a1f653c0ec82879ea8a8921a097e9f6ca83080e2000000000d1e6e200042c6f293c0007f62ee686ce20009b80746e0000000ba00200009020002369322560007ec0b80007d049e0002141426ac00076674c00081a8827c0c903d8ba2000000cdec7a92800019803a0000008600000000000001769c2af24e892a000ac03b2934b50b56aa60e8680ce07bc0066280008ec0ce26a1f40589ae000c12174000acecd8c940000006a81c0000b5200091e0002e86d4cb20009047fe0007866464c6182a589605805d68702ae000000ccc9068d400029acf80003b000000000000000084a9c6000a7a00000000000000000000000075a0000b400055200097c00040c0003541246c09909b6000b1875ea6a07835e546000b321ee24a000000000b1e2dca5a1861106a0b46c7e4420ae00053005eb066fe37044ea7871c88a55606e542d36208bf2000a1e9a2c50000032a065de94400000036c0009da0006a47a413e0a401c0808a48220000001f0000000756c8c000c6610023acac2f09f23be0006e40000008da000c4eb28c402809f00009b00000000000009a08c61fe3de7b2a42712cb00000006a60004f8cdc3186981cc0004aa0000c61dcc922301ea57aa7cb260006f80342c62982a24b281c416576b9e000aa43d637251c000c9e32e00047aae464cbfa7e20005b0000000c7027c53441e4046d219676a502bd60844b49e
  | 12 => 0x4a7ae1ac3ca588a30c48192846a92a723cc00048a50a0002d00008626aa0003800000dc00000000066600065a96800000000080050cb90458000000a14000000284000724c329808d855c3ea068634bca384d1c526aa276053e9ea4742923eea8c75897240e2ba8a80002fa794386a9e17000061ea563da040d244965ea00ab220009d2a1ca6e6568ea6ce000c6e6f062c0007c6c0eb600f20000467a628a0e60007504d096231aad20008e25a0414a94678cb6300824566c54816a664ec09007203c83443c000b7251e4e2820afa3823f8c3ac5a8ccd0228263c29c466b3621ac7856c6f4d0821038a4b62b24dc44c04e2944a8b661723c800068a00007c0000000006d63262ca0000000000d6396000000b040001de61a0000005b40001c8000362a9642833818060660cbee9bc3dc4608668e495218c2d25aabb48a67a0000000562a880b2000b960005080a000096467c066876b083f00ac00046e37a1b215c42eca20002647c81f87ce538000000c848fe2de582000bb272ebe6d264620002ea0f48c000033417c6168d203e00000052808e3665f6c827301469aa000a629460000a200000000000000069268c000956b30000762000954900000d280009300002fe00045c2b854ca2e936374ceacaa4cc00000073615e0006dabd40004ca000b1299244a9caa02d30baaa680760f665e5728720004f4c18000000b027d211c976c100002e04facca426bf0d181e48bc000b3a2a0000c6ca04830510276bb801a000a2c0009429ce95e4845ee4fe77a0008b4acc67e02caca036a484946446b285c85037c96c53aca6342b986208c8548410cc696a130cf656ab1c7406004de00051404a8b60002406c84902a48a0a54d3216825092eaf65b627215a8ced385f47003900000001262e6424388950328d14a5e00002ebb6ab8322a4ca405b8be2c9abf4cfe01494cba6ac8000896720982088000a007e6c8e7eec860565ae194b70000000b4c254b1600000000059a5120000001ceadeb927fc0000000000002c25e86ae000000a823165180000009d49746080003568d0b20000000000000000000000000000000ab400000028eb7e456b348f4c6a5cc00000074211473e4c0000000000b80cbc0000000003360000009f83787dc3a00ccb6470270cae09700fa00022e00066a00077eaac0003ae7f0000000000000000cc48a2d2a19029e16e1361aabcec4c0aa0000003a6000be85e60001b00000008f80001486c47ca2c800034e00000000000068234c0000000005feb3e8ee000000c3c0002287140003243aab7898eb0c00074661c98a516000000000ab0000b8c000664a907520006d8054000ad40003ba1d4a280fec1ebc820e0002a625cb489be00000000083a632a360006de0923c458a46899ec009489a48de8fa45027e90c000704000000
  | 13 => 0xa9d67ac9a88789181d600058eb546c25404bcaf85a2a20b9a57c454ac462600026843a00010e00000069000000005000034400000000000000052ac984483a82b04780c00b033e6b073c20286e15888c000000000b1a0000004a04be92059836a4f633ac0600002643e26200000077c14a8ba000000bbe000024028000000000118000000c2800088025a8689c40007de000c2a89a0007cc00000001eb4e5dc65800030cc08c4a220c8a30e1ba000710000aa000000055024224e042b6e5f8062000000000c646a200000000000006c13487c4189fc438ab613c004a64852af4000c300001b626005a00000056ebe4d163ce70e3a2ca40166d089cbeca1259e28672600085e0000004c235aa3aad01d21321287287d69b2d12a702463e2ae835c42a98c7805d25b20007c2a188260000001b82da984340c2ca4600079a58c5f0520522000000000000bc60000000004e60000000008540000000003067b860254e0ee5ec07e2ac4a499c00011252c9d0b9c6949220008f247c63e0000003e8000000abe94a99a1e034a1a417aaf0a985785ca77425802a116200812ae658466c5e2aea9fe6549580446100a87a2bc0108d04436cc239403040814c6682f8cf4c7c66063624cbea63a0003fc0006e621e26c000104ce61ca65c00000072214e3e63924d60008d65740000002be0000000005ac000a528421b493886c3f60009f41ec60e4d470822282c59c00001089400094ea087763fa64e88645aa600003303b82ce60a0f0ac6874000000b382d800031c2186502521a60c837e19c9e846c0001ae7e01a8000b8a4da00c39a532000232cbe5fc000000924d2c9d80003528e61521e66746725047642124ae1c40000004ea000cd0000000bc4000c0c0007ea6ec4020c40a67340001bc78e9ba47e08acf0150778bd26eeca0b8283c8026fa13866e8cabae9780d40ba10c09a844c3e614000000000bdab6a2b6bc25a60000da16aa4e4924b8000ad683810a18899822aad8000000c38000000000376642c140000000004a600ec2600000000094000017880c14400020c7fac34792000652804b5a0f86ba3bc5d4a7eb0071e00032a30aaa8ba8000908ada000c9cb0a412c5c2f299685a90a70671a5241fa7b6a8674431e4ceb0e1e20007da012c36cd27e855a312848c2e000000000082000000622000000094ceca8000000000044400000039c0007900000002d60003320002e4bcc0000004c8000cee3c0b1438c4709ac6ea7880000007f89de00000000055e00000000036030200000083e00056800000000020a8f0000a328f60bc18e1a23c2038162358c248563f422439e8646f6aba16638e3fe30495a1544984e474e2a86fc000840432156488a26cfc23e624aeccb8d208844c423ca104768b041cc04c741da00013a022000b68a16bbaa765e46
  | 14 => 0x184b2e6dc0d2b240004002fc2bcb84d343e018
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f687d85215000d0fd0fbaac8980023be09755913001c76412eab2260008f7815d5644c0051e902baac8980021fa1c75591300345e43aa8b2260068dc8754d644c001c3aa8a9ac89800e3ba1f725913000637baee4b226000c6c75dc9644c0018deea392c8980031b1d472591300147b43ee2b226000c7775dc5644c0018e8ebb8ac89800339dcb715913000672396e2b226000c77751c5644c0018e8ea38ac89800339dc8715913000672390e2b226000acd83d4b624c0051b90eb2262980162fa1276485300045ec24ec90a60028ee87d89214c001958e9b1242980063b60b75d91200046fc1aeab2240048dc835d564480011ef02baac89000a3d205755912000566c16a7b1a400087f855c7634800d0f90ab8ec6900022fe1171d8d2002c5e422e3b1a4000a5e858c7634800d0fd0fbaac69000237e0d7558d2000477c12eab1a400087e871d563480018b8ebb9ac6900031b1d77258d200043fc2aeca1a400687c855d943480011df04bb286900023de057650d200147a40aeca1a40038ec821d9434800195e843b286900122f21d6450d2002c6f43ec6a1a40018ee86dc943480f1998c7b9286900067aa037250d2002567436c6992400087f855cf614800d0f90ab9ec29000a3b20973d852000c77436e4a0a400687e851d931480010fb0a3b2629019e6ba1f744852034e563b6e890a4000da870dd121480d1958ec3a242900372b1d364485200147643ac890a4018ccc63dcd2148001b9461b9a42900063b219734852006cd6422e690a4000da874dc121480079d0ec90a60900faea211214c120007e098a429824000c3d75d53644400156b03aa6c88801a1fa1f75591100045fc22eab2220008f7815d564440010fd0e3aac8880030f1d774591100063a3aee2b2220008bf845d5634400b17908baac6880023be097558d1001c76412eab1a20038ee829d943440011db053b286880021fe157650d100343e42aeca1a20008ef825d943440071d904bb286880023de057650d100245f43ec8a1a2000cac72d91434400d0fd0fbaac4880022fe11755891002c5e422eab1220008df835d562440091b906baac4880021fa1c755891002c5f43ee8b122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220048de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd624400d1d90ea92c48801a3d21d515891000732a92a2b1220018fa87dc162440010ff0abb2848801a1f21576509100045fc22eca1220008df835d942440091b906bb284880021fe15764c9100343e42aec99220008bf845d9324400b17908bb2648800237e0d764c9100247a43ac498a2005cb87650d404406175104a1a8088003e450d3150110
  | 1 => 0x8e2392869880a3760f75d89310343f428eca12620087d851d9424c4011df04ba6c09880e3b20974d81310045fc22e5b0262058bc845cb604c40187aebaa6c890802ab60b54d91210055ac0ea9b2242068bf87553644840153d0732ec890802a760e65d91210051f42cc7b224200a3d8598f64484d35590ca96c89099f2b9db32d91213655a432a3b224200f2552547644840153d073aec890802a760e75d91210061eba8ebb22426caae821d764484d355b043aec8909a6ada0475d91213655ac08ebb224269aad82dcf644840147d0b39ec8908028f61673d912134d5b408e7b22426cab5811cf644840117d0e29ec8908022f61c53d91213655ac0ee1b224200cbb709c364484d955d04386c8909a6ab60870d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912136557410a1b224200aad8214364484d356d02286c890802ad60450d91210045f43861b2242008bd870c3644840147d0a186c8908028f61430d91213655741061b224200aad820c364484d356d02186c890802ad60430d91210045fc22eab2242008bd87994644840153d07328c890802a760e65191210045fc3aca3224200a3e8598c644840147b0b318c8909a2ab21952191210074631e643224267ab4865446448401c68caa88c890803c9549511912141556c14c03224269cad72d9363484cf95ce4326c6909a32b5c864d8d2101476c16ebb1a42068df8754f634840117d0fb22c6908022fa1c6458d2140e57b90c8b1a42008bf845d5634840b17908baac6908023ee017558d2100c7c402eab1a42058be87dd16348401958e9b92c6908022fe117650d2100477c12eca1a42048be87d9143484d9958e5b22869080a3ba1b7250d213ee56326e4a1a4269cac76d9142484073590ea1a8490802ab219435092102e563b286a12426ccb476d9131484cf968ec3226290803a518c644c5210056a4328698a4200f854350931484cf958e4326c0908063b20974d812100732a92a3b0242698bc86dd1604840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9c73191604840193ec9b9ac0908032719373581210043fc2ae3b1a800687c855c7635000917908b8ec6a00526ba1f7250d403c6563b6e4a1a8000da870dc94350101958ec39286a00b32d1877150d40006d9086e2a1a8000da872dc1435000317b09baec4a0052ab20943d894000c5f436e8992800087f855cf615000d0f90ab9ec2a00023be0973d854001c76412e7b0a8000ab584d4761500014ed0b98ec2a000aada1b61505400343f428ec98a800087d851d931500031790cba262a00526b209744c54002c5e420ec90a8000cae421d9215000317d0dba242a01a72d187744854000cdd406e890a8003
  | 2 => 0x4b6138fb40cf7300bf4812b1ec6648c6a0a0402e817124eb181134dc0f42132060e61d4f3144cd160793bc520b4ab000002880036d003b81c0d0f654000000c6000ec5a5010000700116344c70914d508af31006048915289f4c45e18c9017c302cc29378485b0570000030d400003a0004f2990e07958460085149d368110008b0001f26c3d000002282f1a4bb000be04cce5980041c145aca8558464c1490000d130260013a0000051cf020cf2008005bc270ec6e0140000008000214031e00605028200200060001225058001602008000a3620028bc02008000203000000000038040000000500608000008a24030080805130801803020001e01010b40806008000001018040c0c0880400010200c0a010103002040103000050000000010311c007d090080a00021540200088080402040542000018001406100041205008031b5d752d894300556c26a5b128600acd83d4b6250c0d1df0ea96c4a1802b9a0665d894300572c0ccbb128678aac865536250cfb5990ca9ec4a1803c355153d89430053742cc3b128600a6d859876250cd995ced20ec4a1802b9a0675d894300572c0cebb128600c6d751d76250cfb55d083aec4a19e2ab61075d89433c567418ebb12867dacd831d76250cf155b09b8ec4a18029ba1671d894300536c2ce3b128678ace831c76250cfb59b0638ec4a18023ba1c51d894300476c38a3b12867dacd83dc36250c019d6e1386c4a19f6aba1070d89433c556c20e1b1286008ee871436250c011db0e286c4a19f6aba1050d894300556c20a1b128678ace831436250c0159b06286c4a1802b9a0450d894300572c08a1b1286008ee870436250c011db0e086c4a18029ba1410d894300536c2821b12867daae840436250c0155b08086c4a19e2b3a0c10d894300566c1821b1286008ed879946250c015cd03328c4a1802b9606651894300477c3aca3128680aac865506250cff5990ca98c4a180393195531894300786aa2a63128600a6e859846250c014db0b308c4a1803a9186411894342556c24c03128678cad74d8b6150ccf95ce8316c2a1a032b5d062d85430245ec26ebb0a86068f7875476150c011dd0fb12c2a18023ba1c625854341e57ba0c4b0a864bcac7418b6050c01c3aa8a9ec0a18b63b21b72581430047743ec4b028600c6f75d896050c018d8ebb12c0a1803391c7625814300477438c4b028600c6f751896050c018d8ea312c0a1803391c4625814300673b16e2b028600ce462dc56050cd917f08b8ec6a10b72b1db7250d423ec77c12e7b0a84008ef825d5644c8f11df04ba6c0991a62fe1172d814100c5e422e5b0282048f581dd7644c4011df04baac89880e3b20975591310047dc02eab2262018f8805d5644c4071dd0fb92c8988032bdd072591313ee663b6e4a1a627fccc761c9434c401b8
  | 3 => 0x2a52a4b47f49d5e2145a02c0044841095145a95a000a31f4d55c8004649953800384390000050c00000002540006400000c52100000c00488e912cac0b0e357c00204000a8672300025c00001730010b52125208ad54d2c3f4aa08d0d000b0479390dc004ec000000024cc1000a5011743d4980e0d71c0ae39c4d0007129160441630003c2e0354ccff23c000010f4902e000ea430000000032cbc0002b410154755d1e8c81d8b24fc005c0963f93c4f488000a71b14659cc22853434d3855c65548cf0f962471440010545cbd1b5543f0f1394201093e1656e088b553d1b110560fc5b360333d01a201351a0092694c3301b4545047d291f8004a0d01f0001910211405380e20006b364005a086031513e94b184000840e5b4d2248c9224f9250df58410001714bc00000471289c0740a23936418000011a23555570534b8dd00111000b9154ca1d0b421c9e590d449878174e842816000001cc434246259431390d61bc001dca0150323e0b756d212c55950472004dc170363b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x16020405832595454c6250cd162496549511912133c2b25c8650d42484016849650d424c521
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94e
  | 8 => 0x94b
  | 9 => 0x94c
  | 10 => 0x94d
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
  | 47 => 0xa0956
  | 48 => 0xa0953
  | 49 => 0x94b56
  | 50 => 0x1549
  | 51 => 0x1409
  | 52 => 0x150a
  | 53 => 0x128a
  | 54 => 0x16c9
  | 55 => 0x1449
  | 56 => 0x168a
  | 57 => 0x12ca
  | 58 => 0x1849
  | 59 => 0x1489
  | 60 => 0x180a
  | 61 => 0x130a
  | 62 => 0x9c995
  | 63 => 0x9c996
  | 64 => 0xb0996
  | 65 => 0x98b16
  | 66 => 0x138b
  | 67 => 0x124b
  | 68 => 0x98cd6
  | 69 => 0x1709
  | 70 => 0x15c9
  | 71 => 0x168b
  | 72 => 0x12cb
  | 73 => 0x1889
  | 74 => 0x1609
  | 75 => 0x180b
  | 76 => 0x130b
  | 77 => 0x9cb56
  | 78 => 0x138c
  | 79 => 0x124c
  | 80 => 0x150c
  | 81 => 0x128c
  | 82 => 0x18c9
  | 83 => 0x1789
  | 84 => 0x180c
  | 85 => 0x130c
  | 86 => 0xa0b96
  | 87 => 0x138d
  | 88 => 0x124d
  | 89 => 0x150d
  | 90 => 0x128d
  | 91 => 0xe8a16
  | 92 => 0xa0e96
  | 93 => 0x168d
  | 94 => 0x12cd
  | 95 => 0xb4b16
  | 96 => 0xb0b56
  | 97 => 0xd0b16
  | 98 => 0xb0d16
  | 99 => 0x170a
  | 100 => 0x15ca
  | 101 => 0x16cb
  | 102 => 0x144b
  | 103 => 0x28b
  | 104 => 0x40a
  | 105 => 0x160a
  | 106 => 0x188a
  | 107 => 0x184b
  | 108 => 0x148b
  | 109 => 0x154c
  | 110 => 0x140c
  | 111 => 0xe8b56
  | 112 => 0x18ca
  | 113 => 0x178a
  | 114 => 0x184c
  | 115 => 0x148c
  | 116 => 0x154d
  | 117 => 0x140d
  | 118 => 0x16cd
  | 119 => 0x144d
  | 120 => 0x188c
  | 121 => 0x18cb
  | 122 => 0x178b
  | 123 => 0x160c
  | 124 => 0xe8d16
  | 125 => 0x170d
  | 126 => 0x15cd
  | 127 => 0x3cd
  | 128 => 0x40c
  | 129 => 0x41712
  | 130 => 0x40992
  | 131 => 0x41494
  | 132 => 0x40a14
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 973
  | 6 => 1693
  | 5 => 373
  | 4 => 4
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (39565+((h/324+packedAt gbK7 (36001+(h % 324)*11) 11) % 1553)*11) 11
  | 6 => packedAt gbK6 (88032+((h/564+packedAt gbK6 (81264+(h % 564)*12) 12) % 2235)*12) 12
  | 5 => packedAt gbK5 (23123+((h/124+packedAt gbK5 (22007+(h % 124)*9) 9) % 448)*10) 10
  | 4 => packedAt gbK4 (283+((h/1+packedAt gbK4 (280+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffff0f0e1fe1f8070e01ffffc8181fc33c27f
  | 1 => 0x78780f00fe1fe3ffff001c0ffd464e90cc7c4f
  | 2 => 0x7f800fff001ffc007fffe00f027870e30f8f8c
  | 3 => 0x80000fffffe000007ffffff003807f03f00ff0
  | 4 => 0xfffffffffff8000000003ff8003fff000
  | 5 => 0xfffff000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x88886030402a0484102044a14800802411c215
  | 1 => 0x34508300220521236901884ab0424690441c4a
  | 2 => 0x5d412551001748093a4ac02c185850e10e868c
  | 3 => 0x20a8ab54000124495134023802b02e00960
  | 4 => 0x44cecd998925c0006018043ad8003bb6000
  | 5 => 0x66678008110100600818020883f77dd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36380
namespace PEqualNP.Outside.L_meta_36380
open PEqualNP.Outside.L_meta_36380.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 64 := (concat bs0_4_0 bs0_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 40 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 99 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
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
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 92 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4 := bgb_4_0
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
theorem bgb_5_352 : Interval gbAtlas 5 352 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 373 := (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352))))
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
theorem bgb_6_1664 : Interval gbAtlas 6 1664 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1693 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))))))
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
theorem bgb_7_960 : Interval gbAtlas 7 960 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 973 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 bgb_7_576)) (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704))) (concat (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832)) (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88fefefeaafeecfa88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124202 * 2 ^ 32 + 4276943496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36380.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[3,4]⟩,⟨.and,[1,6]⟩,⟨.or,[2,8]⟩,⟨.and,[7,9]⟩,⟨.or,[0,10]⟩,⟨.or,[3,5]⟩,⟨.and,[0,10]⟩,⟨.or,[12,13]⟩,⟨.or,[1,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276943496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36380

open PEqualNP.Outside.L_meta_36380 in
theorem PEqualNP.Outside.L_meta_36380 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276943496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
