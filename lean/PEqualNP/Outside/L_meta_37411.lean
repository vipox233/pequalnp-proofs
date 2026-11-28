import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37411.Model
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


end PEqualNP.Outside.L_meta_37411.Model

namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
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

def SBf (j : Nat) : Nat := [4, 6, 4, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37411

namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xf83fff803fe00ff803fffc03fc07f80ff98c7
  | 4 => 0xffc1ffffc0000ffffc01fffc0007fff01e0f8
  | 5 => 0xf0001fffffffff0000001fffffff800001ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4110825924928a28a4924552d2d4a5a952ab5b
  | 2 => 0x822104aa4925145149248aa565694ad2a555ad
  | 3 => 0xd47609376239a69a63b913f0398c7318f998c6
  | 4 => 0xe843b1c473b1d8e47231dcf9b0307c7c31e0f0
  | 5 => 0xf7bde0783c1e0f87c3e1f3e3e3e6060c1fe00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37411
namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x258d500c20208702c60080a000c5bf43bd43be42bc42bf41bd41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x8602a4e26aa3a1c754c429aa88851d53d079060107808010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (168+((h/2+packedAt s1K3 (162+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe01fffc03fe01fffff80fffc07f03fff3e23f
  | 3 => 0xfffe03fffffffe01fffff01ffffffc07fc7fc7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x9642048428a224242450b162d48b458a25acdb
  | 2 => 0x2bd0a92a99651d4948bc0ab54c5522d752e22d
  | 3 => 0x4c95a2325249491d912d5819a966a845985746
  | 4 => 0x711933a3639191911dce6cd03078f3611f03b0
  | 5 => 0x81e1c3c383e1e1e1e1f78f1e3e40c3861ff800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaa0aa00aaa0a000aaa0aa00aaa0a000aaa0aa00aaa0a000aaa0aa00aaa0a000aaa0aa00aaa0a000aaa0aa00aaa0a000aaa0aa00aaa0a000aaa0aa00aaa0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37411
namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x12108144220484901058a2a288a8a2154534d5
  | 1 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37411
namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1200006002b4400f9d0018000582caa55a0938e4c101973884d161a8062f1479510526c02e0e0041400000090000280000001100000006248080000002800c099900007a3001e00000260410b00089882610000ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb81600078984f35150b49b21154f400469780044072140e9100030fa7c0ba4d08113001842002199c000000000002743914089f4700094012b0002a00001e03220132811e0012808463f1a840000000000100a000b0da393f800268602801425140a780094359ccca6f1a1f8644640241145d149203e41000bc485707a5880662c80000001e0000028280001695000cc0000018009c0000290002d0a000383b3626896494184812221b2200082291dcd0000026400473b0a8f2613917c7a3a0d8749a0d0028c009c32260349737060e8002d9a4567b318c000310000000701f22400531728800580022c6e9d00188e275490e0008c02008404000002820180800184050107800281000300800711000281010500800081870102828100840780818380848380010203800388cf94b439f28e873d50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e78a2a1cfd41439f2a0875e53d0abaa7a14f54e429f294853e5190a7aa12157d4d42ae29a853d5310a7ca4216b948429f288853d5010a7ca9994f55332d6216653f548ca78a91967d0e32cea1c659f548cb38a9195794a32cf214659c428ca7ea8994f151329f2a0653d540cb3e86196750c32d6210659e540cb3aa8195794832e729065cf420cb3c84196710832e6210658c420ca7aa720cf94a41cf194839c329067ca320cf54241af298835d531073ca620cf54c41cea98831d531067ca420e78c841ce190833e511076ca220cf540419f2a6633d54cc73a8798cfd52319e2a4633f544c678a898e750d31b7a92636c524c6f6a098de141319f2a0633d540c67ca990cf553219f2a4433d54886bca710d754e21e6194433f5448678a890d7d4d21ae29a437b50486f0a090cfd50219e2a043cc32086bca7a05754f40cf29e813d53d033aa7a04754f409f296819e32d033865a04f947409eaa4813f5350278a4a0678c940ce192813c5150376a0a04f950409f2a6613d54cc27ca9184f55230cea1c616e528c2daa5184f951309eaa2613e540c27aa8186750c309faa6413c54c839865904f952209eaa4415e53882baa7104fd51209e2a2415f53482b8a690730c920bba8a4174514827ca8104f550209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x53b408803566106b61600397644dc000000008000150042b09002a1801e003c61a3e056901260e315c018000464a294a0002800747394edda24000001b4cacb0000bd180001403a00008830004080800400681000408614280080040300c3d4c5250f0f63149438758e5190a1f63542428e580548ca8e62d5232a3988548ca9960152328b594420ca8e6290832a3d94420ca8d6510832a3984420ca8d6010832c3948329061f635424193189531062c6254c41a3189531070f6254c4187189531070c6254c4183189531061f658c84187594321068c6250f318b98b548c61c6550d31a3189434c70d4314931c650c504c61d6395321c3950328861d63150218e580540870c540c8219318953d022c6254f40a318953d030f6254f408718953d030c6254f408318953d021f658cb408759432d030c520c9408758c515028c6250e30c350e528c21d63951308b189544c2346155130a3189430c21d6315320c315032c830c540c920d10c8514821d63950208758c54c421d6395210
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1840748805310004000285386c629287225c3651083281ce5b1aa120d087250c504c606bb0a819043425c0540c821818e4b18a2a040c7258e5408206392c62a621031c96395210
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s3K5 (912+((h/16+packedAt s3K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s3K4 (4895+((h/55+packedAt s3K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s3K3 (2420+((h/20+packedAt s3K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s3K2 (502+((h/3+packedAt s3K2 (490+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf03fff81fffffff81fffe07ff07ffffe7e31ff
  | 1 => 0xfffffffe07ffffffe07fffffff81ffff8ffe3f
  | 2 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1485188c41224c180594a432503299543610d5
  | 1 => 0x210a211032449021602948c4a48122a888e62a
  | 2 => 0x42934a2490e904caaa82751139540c0d534b4c
  | 4 => 0xb2c74492481d974d34c1861ce69c031ec0db0
  | 5 => 0x8c307871c70e1e7f1c739e780c7188c1ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xe8e8c8c8e8e88888e8e8c8c8e8e88888e8e8c8c8e8e88888e8e8c8c8e8e88888e8e8c8c8e8e88888e8e8c8c8e8e88888e8e8c8c8e8e88888e8e8c8c8e8e88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37411
namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0xb162670869c51080004a0003627f0450001ba000e99844ea94c5314b000930198000000000028a17490c268000009e0b100039c914ba90e3f62a8002032ac0800005d000111170fc3509d13f93c3884f4069540a2a30941d60324ccc8000000128df00021080035a7637292087936482554a292e1164c00017a298214048fa000824511df1907b50f95c23e000e61aa4d45a03916b1ae5c078a8822a6880000a1c65850381f2f8000b60b5106934b4a800da18c561f30000bd369b60fa2d93ea584e610c000002521e8139640007c0001b73e8948000000ca5d85b80023c3a8000d94fc3e472a3705aa24001d04be000350a80728e1430571405eca801b000a4c851214103cca399a0422ed028550840a8000003c86eccd8000b600000015000048d393f49c5807e82b506238f392b0061388205612a7e0228000760013e12d03a3086800032a698089033061f0cc8004b8769100ef0000000027b4163844b0f83821fcb6a6f2e47b12c89b0007ad07800000000af87845631c3702e1461d92f0000000010704b000000fc800000200c91583563480023a44aa385997400053cdf8cc000070e02220ce450eb89a3ec6f00008c0e20a10b8701700202e1e24aa878f313b3d40f8651b04ce2ad43986494000ad92c4cc650e780744e0007387526a2f85483d0008fcf02690000dc621fd3ba17cc2a710003613b959046a54bba3947c458248dc17a6d0d7052060358f90994182c01e25a1e8a08760003d022400000000624c5000000000ef0040040502c070180401c000042c0000302c00030130080300801010040240201000018060180107c08010000100100c0000002004030000904c000041300404000010000202c040040504000020000040b0001400c0f124050100402016010020000201c0000c030000503c0101c0001c040180201001000090080000820000140040502c020080501400018050100200801010020500f00c0c00009010030040900c0205400014020a01900003020000440307011040010180c0000907c0201c0c0300a004080000500c0702809008060880602c090000e00c1e0003a014150401c000050d40500c0d0100001807008010c00601809008010041000007010080100302c02008000040000803054080000107800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0xb190c00078d232400006d4000000008701d0ce0006cc000612700013200010e2bc780910007dd009ad0bc0586d9e12f011849a961ec88c209274768a0ab99d20a1988004010c8690b0a5348018020d31ee2f0cf05809e64c8883435e8502610b50a8d01895307e3c8b2a924a232cde85409076c0022d000350e32351921ec000000484f9198004048f00007900068ca6a6c0fc0000014400086407218000925178362dc71ce6a4f52e000af12f00046c89a0d24c4d02825d284818c42940d87e8a714000014ca528d1c82908809802e27c5f8002a47c53001a212840748a7232a04c69324585e4008ae3fe5207597e3005a87716622e234b9a362de8c4b393a19a5f52b15d2549409194651e96c2c9e515a98d3d0b9342000ea00b10450c8e89c1fea2c839c81b47d4600001bc84ce198b0041cd3819f5225c4341814244184b92011e2d007a2444265cbf80018a63934000384660e58d13fc8f4d00001da745420c64881d049000026000e4800000854001d84140000000048e000c78cf2484dd131121424c434996000088dd000202304700000c8000c127239486d358350ee2402391c3d2950e90d50006b0ad0fb1c40c8910c300a95cf702c1025044e9490b41806f8e6000030000000de0007a8623708a40000004a495191512342201326e4846c8c8a1d13c98414a1123000000279000694080fe3b88a9020b2000000ea81800061c1c0005203a09c8142048c1310004ca7640f1ef318000d4a4
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x52fa0009e9cd2566a06019028e3540001b3be340499b53560007986021e440010000be2bc1c2053da0001c8eb29e59cbc043408000419ee0006b86492a1c2414000000006e90609c04e2747b87b1fe548548000005e40ca023e4468ea0072d21703f9d5066068b307637e28c042130aa0005a12f4324888e0e407a5905296c19a000000fb00002cd9800000000000952244dc6901e0004440018c1d0000001ff0004cccc93b31c3d82083e0ca430000000006484f1db2a819c000003fa000e3800000000a61080000c50b0aa2c4000a4000000054a693a1bc3c82d90d1d8000001600927645a9732e05f02d0003762f00298f1ea000531590500b4c380016c824bd9142da1c8618ce038044f515c18a78c068000005083080007e3300004a000004090081300c08008180000a0000f01c0f0000e0000007803004050280300c0700024000000001c0080400008000020000002c00000020180201007000040540800c0400005000150440b0040001405000000040100c0e0100d0040a06805020000080201004004010000500407004020640b000030400001400018080780000c0700000044010600500003018010182f0100700400004000100000002000050081401003028050200000c0300000010050080d0180404c020081100c0000417000000040b00c050140100c0303000024010140201c010180000805018030326f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0x749681d400010800382000001cc3b8860cf15a0002a0cb0000001783e000000000f81001322390380013034ca080005e0c84002930c08cb880012c000431d20d87380005024c000000871907cc639b222c27cfc0570a67dc59a110ba2b400094310318771941428542692e2a0190e11ec3d66b4000002b60501b177134038af0542320000000006a6f42b000054000001a900000000000000000050001128683a801000090d8800196000001c31c03e4081810000009c03a0f085c0000038847c4b800414244340000001880000015c0600195f0e61301a1b8344398899981740000000000000000000000000000003145fc001d61ae6d0fe214000000b08a43de8180011e35e74000000000000ff0000a2000b916f1ac800001e21e25d4c007427c4c8949581a86144106f3ea07cec0002920006898b3d222c83816312000db19d17a1a4021741be000000000a45f90782020c778e40003e2374bd1d1000514091462963943719a420098fa10210a000a51a012050c719830005b80019321c074000002ca42400130000000460001024a05d9aa0f4574ee8460007d88b9273081dcaaa0e0f248c5b8003ca12c7d12038a6dcd800000029cd28000004d4fd9150004d8d08001b082c4d93c2064c40014e2ae23c220000806f0d30001fc328001e8000474001ac08e46c679be0fc4282406a0001c4d186b0000f0000001082b0160db3361608594000065c380001f04d0ab1b932269c061cf2023880002525a39c0008d09e4fceb800000108f380041a0000008a1407903e8b20da0010900000072c00006380634920fc0cc310000ab0004945c982012000a20ed1843bd018a21b4728000fd1e87249c96b0006900983b09c2c0319213c07182c9da1702f8000302a28206c99c05c3045f9041b805ccaa013a6460bb03712458cfd02233e0ac000b13c254c9616a3cc000078001e0220fc84
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x60000735600000254e44901200800f0005130403045ca2c31404001818400e4000098318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x5a080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 797)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 2 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 3 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 5 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888eac8eac8e888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37411
namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f721843e843085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x240000c000080600a03848000060380a01000045f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131ef21a63dd434c6fea498df14931ef19263dc324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9
  | 2 => 0x9c20006290803d28c4ece687247685c8314b0ec7448d0d10d655418a1d1983c02592b35c6601d8cf042364000001c6000001d33622747780014e915270001aa8e12aa393f012089800290039200dc0001b88b15c1162044b0000002612b00000002c7f80017c000000001528508f8db1780000306844250402912156688aa1b50000000010341c07c328f80000c8dc91542c7d06f07048820cb88030820009b84c1ce610531a30008b4bd9b00f23f8af1380002547ba5814850c0000002c094ae9ca386178001ac0b695c2a9fa4447b81a20220e7c8d7a2605e538432510ce01c3a0aa080230f69f3000000000000004c4001bd17e3f4a2956000000001e4000001139341388a51b2240006dc6b92e2dc4bd0f80005c684000040549092900000094c250cb30c000a912a34a9411880028e0005193c3880cc4a13909a8dcd3189390000788000e252834a0c3ce3e4f199600056ccb9cc496631058d4248934000ae0a4000910000003aca01ea4648c0c68ac1c86a9209e11d464c420ca2461f4100733b4054111ab0280001b8004920f0ee800240000181df436380481fc4501387717e1804d8588004663d4e08a024e5cce70ba04e470af8883020000024610a0d40014f0b888d1702b0c80005e839456340fb800426000001500868e90921a33e494ee0931507f80000006c0004517d2c2464a20df000308e81750022ec00000032678ab84f0000000011142a239051bc3ac30c0d1593ca0002c1090a0654000f62305e0000f441e1b4840230383cc0e93327c0000024f43c6f8000000700001683f000000000002c06d85680000003c2c86c2040009d01b2088bc14099134864bb0172fe64400105000000000000007246d19c1d804c4697a0008f40f179368000000000000005b1282a21109a8e61921510189f19a7b08091d16890c5b8dd3b24c0879f93201983b85d0005c11a07c0f02c0a699d0488108f0611c22240000012e180d38000841fd1e00047e1887d17c0007c0ea83a1d07d8dc000264000c59d74587a06c05605282486a4a2d4208dd89b0fc6b4051fd1c40300686f0923140016c31e638ff8c74106090300001017c048002ca835001a000202004000000100405000010120081c00002010020800a040020380401000000040580609016060421b8000d8000300a0787201000030200000001806038aa0080a0503607800008340a8200001c0b854010260705800006008100181a06000020042600800000018060400a0081000004000180280a0082206052000121c80e01002008060e804060100002802804070240102e0002e0204a0000001000010220383e01800018280180a008000682a0000200802048100080c018001401e040080000a0a00406004018120a800018040500002012008160180e08004010080080000890010
  | 3 => 0x1088b83ea23ccd12121c46cb1168350780f59cf0ae440e3964172894a606a306664f32480240442312927a700631b332876cb59773a45985292d27e1e8491f12e47eca48472003ece314248e358c28c81885a4d21881ca7bcf12200202c8ad10a0a66fccd818364278a99a91e4168ba1170ea3a48600216a200ea1d808a0008a16740200000218498288931e910e098e58000a200059a074383f0001c50f64b0b18912b0000c92540003483180047c61cef0ed4540f869a05058304b798015e5b4dd10b1423391a
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc421032d52108408f596411029d6310440a758f401023f65500409ed95401031d54cc730c755131cc26e62d52309b58b548c31e5450e30b3189438c29d640ca30a7590318c29d64cc2309758e544c26f62551309b189544c27761551309d185544c23e64145308f590514c25e65cc5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c31c5450c30b3189430c23f64548308f191520c29d640c830d3548320c25d658c430a7590310c29d64cc03097d95300c27b654c0309798c54c825d63153208f99053c823d6414f208f99251c823d64947209798e51c825d63947209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c514835453145209b997214836451c8520d9145214836451881209798c540825d63150209d984540827561150208f990530823d6414c209d98453082756114c209b596210826f6548020b9185200827b65480209798c54c425d63153108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b109798e548425d63952108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d59421042f160084109e59610042776544010b9189100427b6544010
  | 1 => 0x7aa918c0d20461938ab030928b2b0170b7018008600c0100070860404810000b088b0060b008000400048140a06000043a0116800160805000020900820000e06038000403800000d00014041900810040200800080f088141a100300c020103800000005030021402810020100014400d028340600010300c0a0200c244100000062d000080412038081c0603034003202804480003060320a078080c020603c00000001c0400d3d0c5250f2e4314943a75924310e3f6550c43ab1894310e5f6550c43b31894310e9f6550c43c7d954310f8f6250c43a71894310f8c6250c43a31894310f1d4354843c750d5110f1d4394043ab18943d0a5e63946429758e5190a5f63542429718d5090a3e65d0d42c714f4350b1c5350d42ab1894350b4c53d0942c714e4250b4c6254c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f6550842b318d4210a7661153329d58454ccb1c5450f32b318943ccb8d43d0b32b358c42ccb8e4310b32c7d50438ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32b3189434cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540ca5e631503297597430cb1d54d0c3297594430cb1d5410c32cb553420cb8f43d08329b594420cb8c4310832c7553320ca5f654c832a7191320cb1d544c8329bd95320caac644c832ab18943d065f6354b419718d52d069d6310b41cb54842d065f63542419718d509071c5350d41ab189435069d6310941c754f411063f6550441c754d411067765504419b98854cc66d6215331c715143cc6cc6250f318fd9152cc63c6454b31a759032cc74d520cb319b98b548c66d62d52318fd91508c63c64542319bd89544c66c62551319ed81544c678605513197195434c71c5450d31b3189434c69d640c9318f596540c63e64150319798c540c71d54cc43197d95310c71d544c4319dd95310c65e63153219758c54c863e6414f218f59053c865e63d52219758f548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538863e6414e218f590538865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530863e64944218f592510865e63944219758e510866f65484219dd95210863f64540218f191500865f63540219718d500871d53d0740c754d41d031e5350e40ab189439029d6310a40a758c419029d63d02409798c515025d63145408f99741502ac6250c4097d8d521025c6354840a758
  | 2 => 0xbd8a4541fe9f29c0014400000000000291ebe232000d00028400208000e69c0de00800b92d29e10c148165b0888c1649d2905f0e249000081080023a289c05aa5800296002fa39000a8898199fc948b03c17e831a2880585d012819669086ca18ec98b148d2e6402d61f2e87d976ad01e5089a3e9e82d848ac02a841d0768008082861178c5a72aa0008f3067e1be239329da9e168008a146c08066b05c1a826c2260859d467954000e8001aa8d87e1380e939c49a9b6609c23a8000bac48a9800305e852e2778782aa22a6a7e72894638004eafe79800002501308c35890001cc001e4bf21e33198890000025a48956680002806053abe31800000003d000050007222c950c0690001baec872ca921e0b09520030c000001900000000002ce56194af09c7c9ae6f0005a0000000097000000009ea8e2f1eeada3e2d28ac415a6203c000ca90000628000000000190219ec309ea429ba1da94668f6001621c94c418f84f99220000499346a196500086e2f04396089810990000e95c7716e528006c9fa1e8ee24aea3c936bd3124b056002ae0db00101028b800ac920001ce829b4a0000000d8002ee0ca0e00130001043504a111128680000304068007589e000a836aa01a0dc978e08e0463f862b68c4a303e5c81c9b9d84f00032244b50be33948b2054b62663f2922e26c7c2828011c142aa01268460ac0b0820e0007491a108221d1144a24c29acc2580069aa62eae0000005780000000861e26c1164aadeae30a090844412e0029822af284a46b1ad071aba34a56a21f40030e1c0ae671
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x71b0001883801405180111d50cc10b08059324d3c140a49969700000038002000012601835d46250c43a18e4a1aa421d0c7250d5110e863928728087455c45450f32c18a8312879948d7690c42ccb062a0c4a1a658318c6255032a1aeba1e841960d6510c420ca0e3b2a899065431cd5210b41c1ac6a9085a0e0c531894350686b90a8a1e63831506250f31a18e8a906598e0d6454832cc7062a0c4a1a638394c6250e40a18e6a90842060d6354842103072a0c4a1c61435c85450c30a2ae22a2861860c54189430c2863a2a41906183591520c830
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x194000a05811506250f3280c87591520cb31a05811506250c3080c87591520c830
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
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 38)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3ffff81ffffff81fffff07ffc1ffff9f1f1ff
  | 1 => 0xfc0ffffe07fffffe07c1ff87ffe1fffe8e3e3f
  | 2 => 0xfff01ffff80fe1fff801fff87ffe1c070fcfcc
  | 3 => 0x1ffffff001fffffe00007fffe007f00ff0
  | 4 => 0xffffe000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4841408c41224000594250089402255030d0d5
  | 1 => 0x11228910324490960290a48529214aa286262a
  | 2 => 0x28a4d22490e9032aa82139504e5410350b4b4c
  | 3 => 0xb2cb1c492481d5cd34f40c44739980c7d00db0
  | 4 => 0xc30c1871c70e19f1c739ce6603110307edb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888eae8e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37411
namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c180017fd50057f54017f95005fd54015f55005fc5401ffd4c03fe5301ff54c03fc53017fd0c03fe43017f50c03fc4301ffd4807fe5201ff54807fc52017fd0805fe42017f50805fc4200ffcc801fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41017f50405fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200bff5951005dfaca8802ffc65440077e32a200bdf1951001cf8ca8802bff64440157fb222000efd91100057ec88802bfe64440057f322200aff59110055fac88802bfc64440057e322200aef1911001578c88802bff5444015bfaa2200aff95110057faa88802b7d5444015fe2a22000ffd8d10005fec688003df63440016fb1a2009ff98d1000dfcc688003fd63440017eb1a2009ff18d1000df8c688003dc63440036e31a200bffd4d1004ffca68802ffd5344013fe29a200affd0d1004ffc868802bfd4344013fe21a2000ffd8910005fec488003ef624400177b122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488003ec624400176312200bffd491005ffca48802ffd5244017fe292200affd0910057fc848802bfd4244015fe2122009ffcc910007fc6488003fd3244013fe192200bffd4510027fca28802ffd5144009fe28a200affd0510027fc828802bfd4144009fe20a2009ffcc510027fc6288003fd3144009fe18a2000ffc8510027fc4288003fd2144009fe10a200bffd411005ffca08802ffd5044017fe282200affd0110057fc808802bfd4044015fe2022009ffcc110007fc6088003fd3044013fe1822000ffc8110007fc4088003fd2044001fe1022004ffc4110027f62088003fe1044001fb0822004ffd9410025feca08013fe65040077f3282004df9941001cfcca08013fd650400f7eb282004df59410004faca08013fc65040097e3282004ffd9010025fec808013fe64040057f3202004ef990100157cc808013fd640400d7eb202004ef590100057ac808013fc64040097e3202006ffd5010036fea80801bfe540400dfeaa02006df55010037f8a808013ff63040097fb182004ff98c1000dfcc608013de63040036f3182004ff58c10005fac608013dd63040016eb182004ff18c10025f8c60801fff530400bff2982007ff54c1002ff8a60801bff430400bff2182006ff50c1002ff88608013ff62040097fb102004ff98810005fcc408013ee6204001773102004ff58810005fac408013ed620400176b102004ff18810025f8c40801fff520400fff2902007ff5481003ff8a40801bff420400dff2102006ff50810037f88408017ff3204001ff1902000ff4c81002ff86408012fe6104009ffa882004ff94410027faa208013fc5104009ffa082004ff90410027fa8208013fc4104009ff9882004ff8c410027fa6208013fc3104009ff9082000fdc8410027fc4208013fd2104009fe1082004fd08410045fcc00801fff500400fff2802007ff5401003ff8a00801bff400400dff2002006ff50010037f88008017ff3004001ff1802000ff4c01002ff86008003ff2004001ff1002000ff48010007f84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x3fe3108001fe9884011ff0c420007fe4210003fe2108001f71084000ff48420007f84210003ec21080297f3004013ffd402009ffca01004ffd5008027fe2804012ffd0020097fc801004bfd4008025fe2004011ffcc020007fc6010003fd3008023fe1804000ffc8020007de4010003fe2008001fd1004000ff48020007da4010003f92008009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2010bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb26200fbf59310027f8c988012fc64c401fffaa6200fdfd531007ffca98803ffd54c401fbeaa6200fff15310027fec788012ff63c4009ff31e2001bf98f10027fac788002fd63c4009fe31e2004bf18f10087fea78803bfe53c4021fea9e200eff14f1007ffe878803bfe43c401ffea1e200eff10f10027fec588012ff62c4009ff3162000bf98b10027fac588002fd62c4009fe3162004bf18b10087fea588043fe52c4021fea962010ff14b1007ffe858803ffe42c401ffea16200fff10b10077fe6588003fe32c4001fe996200eff0cb10027fea388013fe51c4009fea8e2004ff14710027fe8388013fe41c4009fea0e2004ff10710027fe6388013fe31c4009fe98e2004ff0c710027fe4388013fe21c4009fe90e2004ff08710087fea188043fe50c4021fea862010ff1431007ffe818803ffe40c401ffea06200fff10310077fe6188003fe30c4001fe986200eff0c310007fe4188003fe20c4001fe9062000ff0831006ffecb08036ff658401bff32c2003bf9961006ffacb08036fd658401bfe32c2003bf19610047fec908022ff6484011ff3242002bf99210047fac908022fd6484011fe3242002bf19210047fea9080237f5484011ff2a42008ff55210046faa908023fc5484001ffb1c2000bfd8e10067fcc708006fe6384001feb1c2000bf58e10067f8c708006fc638401bffa9c200cff94e1006ffaa708033fc5384011ffa1c200cff90e10047fa8708033fc4384001ffb142000bfd8a10007fcc508002fe6284001feb142000bf58a10007f8c508002fc628401bffa94200dff94a1006ffaa508037fc5284011ffa142008ff90a10047fa8508023fc4284019ff9942000ff8ca10007fa6508033fc32840157eb0c200dffd4610027fca308037fd5184009fe28c2008ffd0610027fc8308023fd4184009fe20c200cffcc610027fc6308003fd3184009fe18c2000ffc8610007ee4308013fe2184001fe90c2004ff08610007e84308012fe608401bffa84200dff9421006ffaa108037fc5084011ffa042008ff90210047fa8108023fc4084019ff9842000ff8c210007fa6108033fc3084001ff9042000ff88210007fa4108003fc2084009ff8842000fdc4210027f6210802fff65440177fb2a2000dfd9510004feca8802ffe65440077f3
  | 2 => 0x200a7f88510067ff3288001ff1944000ff4ca200cff86510003ff6188001ff30c4004bf98620007fac310002fd6188001fe30c401affd46200d7fca31006bfd5188035fe28c4014ffd06200a7fc8310053fd4188029fe20c4019ffcc620007fc6310003fd3188033fe18c4000ffc8620007fc4310003ee2188001fe90c4000ff08620007d8431004afe6088035ffa84401aff942200d7faa11006bfc5088029ffa044014ff902200a7fa8110053fc4088033ff9844000ff8c220007fa6110067fc3088001ff9044000fbc8220007f64110063ff65480317fb2a4000dfd9520004feca90063fe65480077f32a4018ff595200c5faca90063fc65480077e32a4018df1952001cf8ca9005fff644802f7fb224000efd91200057ec89005ffe64480057f3224017ff591200bdfac89005ffc64480057e3224017ef1912001578c89005fff544802fbfaa24017ff951200bffaa89005f7d544802ffe2a24000ffd8d20005fec690003df63480016fb1a4016ff98d2000dfcc690003fd63480017eb1a4016ff18d2000df8c690003dc63480036e31a4018ffd4d200b7fca690063fd534802dfe29a4017ffd0d200b7fc869005ffd434802dfe21a4018ffd49200c7fca490063fd5248031fe2924017ffd09200bffc849005ffd424802ffe2124016ffcc920007fc6490003fd324802dfe1924000ffd8520005fec290003f761480017bb0a4000ff98520007fac290003fc61480097e30a4000fd18520005e8c290063ff5148031ff28a4018ff545200c7f8a29005fff414802fff20a4017ff505200bff8829005bff3148001ff18a4000ff4c5200b7f86290003ff2148001f790a4000ff88520007fa4290003ed2148001fe10a4018ffd41200c7fca090063fd5048031fe2824017ffd01200bffc809005ffd404802ffe2024016ffcc120007fc6090003fd304802dfe1824000ffc8120007f64090003fe2048001f71024013ffd942009dfeca1004ffe65080077f3284013df9942001cfcca1004ffd65080277eb284000df59420004faca1004ffc65080077e3284012ffd9020095fec81004bfe64080057f3204012ff59020095fac81004bfc64080057e3204012ffd5020096fea81004bfe5408025feaa04012df55020097f8a810003ff63080017fb184011ff98c2000dfcc610003fd63080017eb184011ff18c2000df8c61004fff5308023ff2984013ff54c2008ff8a61004bff4308023ff2184012ff50c2008ff88610056fe6208027ffa904013ff9482009ffaa41004ffc5208025ffa104012ff90820097fa841004bfc4208023ff9904000ff8c820007fa6410047fc3208001ffb084000ff98420025fcc210003fd61080017eb084000ff1842009ffea21004ffe5108027fea884013ff14420097fe821004bfe4108025fea084012ff1042008ffe621000
  | 3 => 0xc184601effd95300f5feca9807bfe654c0077f32a601eff595300f5faca9807bfc654c0077e32a601dffd91300edfec898077fe644c0057f322601dff591300edfac898077fc644c0057e322601dffd51300eefea898077fe544c03bfeaa2601ddf551300eff8a898006ff634c003ffa9a6001ff94d3000ffaa698007fc534c003ffa1a6001ff90d3000ffa8698007fc434c001ffb126000bfd8930007fcc498003fd624c001fe3126000bf189300f7fea49807bfe524c03dfea92601eff149300effe8498077fe424c03bfea12601dff1093000ffe6498007fe324c003fe9926001ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298012fc614c03dffa8a601eff945300f7faa29807bfc514c03bffa0a601dff905300effa8298077fc414c003ff98a6001f7cc53000ffc6298007fd314c001ee98a6001ff0c530007fe4298003fe214c001fe90a6000ff0853000dfec09807bff504c03dff282601eff541300f7f8a098077ff404c03bff202601dff501300eff88098007ff304c003fd9826001ff8c130007bc6098007fc304c003ee1826001fe0c1300e7fecb90072ff65c8039ff32e4003bf997200e7facb90072fd65c8039fe32e4003bf197200affec990056ff64c802bff3264002bf993200affac990056fd64c802bfe3264002bf193200affea9900577f54c802bff2a64015ff553200aefaa990057fc54c8001ffb1e4000bfd8f200dffcc790006fe63c8001feb1e4000bf58f200dff8c790006fc63c8039ffa9e401bff94f200e7faa79006ffc53c802bffa1e401bff90f200affa879006ffc43c8039ffa96401cff94b200e7faa590073fc52c802bffa164015ff90b200affa8590057fc42c8037ff9964000ff8cb20007fa659006ffc32c8001ffb0e4000ff98720025fcc390003fd61c80017eb0e4000ff187200e7fea390073fe51c8039fea8e401cff147200affe8390057fe41c802bfea0e4015ff107200dffe6390003fe31c8001fe98e401bff0c720007fe4390003ef21c8001ff10e4000ff48720007da4390003fc21c8039ffa86401cff943200e7faa190073fc50c802bffa064015ff903200affa8190057fc40c8037ff9864000ff8c320007fa619006ffc30c8035ffb2c401abfd96200d7fccb1000efe6588035feb2c401abf596200d7f8cb1000efc6588029ffb244014bfd92200a7fcc91000afe6488029feb244014bf592200a7f8c91000afc6488029ffaa44014dfd52200a7fca910053fd5488029beaa44014ff15220007fec710002ff6388033ff31c4001bf98e20007fac710002fd6388033fe31c4001bf18e200d7fea710067fe5388035fea9c4019ff14e200a7fe8710067fe4388029fea1c4019ff10e200bdfac51006bff5288035ff294401aff54a200d7f8a510053ff4288029ff2144014ff50a
  | 4 => 0x89bfd424844dfe2124225ffcc921007fc6490803fd324844bfe1924227ffd4521027fca29089ffd5148409fe28a4226ffd0521027fc829089bfd4148409fe20a4225ffcc521027fc6290803fd3148409fe18a4200ffc8521007ee4290813fe2148409f710a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c09089fff504844fff2824227ff5412113ff8a09089bff404844dff2024226ff50121137f88090897ff304844bfe1824204ffd9421025feca10813fe65084077f3284204ff5942111dfaca10813fc65084097e3284204ffd9021025fec810813fe64084057f3204204ff59021115fac810813fc64084097e3204222ffd5021116fea81088bfe5408445feaa04222df55021117f8a810813ff63084097fb184204ff98c2100dfcc610813fd63084017eb184204ff18c21025f8c61088fff5308443ff2984223ff54c2110ff8a61088bff4308443ff2184222ff50c2110ff88610892fe6208447ffa904223ff9482111ffaa41088ffc5208445ffa104222ff90821117fa841088bfc4208443ff9904200ff8c821007fa6410887fc32084097f3084204ffd4421027fca210813fd5108409fe2884204ffd0421027fc8210813fd4108409fe2084204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da4210803f52108409ffb004204ff98021005fcc010813fd60084017eb004204ff1802111ffea01088ffe5008447fea804223ff14021117fe801088bfe4008445fea004222ff1002110ffe6010887fc3008441ffb2c6020bfd9630107fccb1800efe658c041bf32c60039f99630107facb18082fd658c001beb2c60009f59630107f8cb1800efc658c03fffb24601fbfd92300fffcc91800afe648c03ffeb24601fbf592300fff8c91800afc648c03fffaa4601fdfd52300fffca91807ffd548c03fbeaa4601fff1523000dfac718007ff538c003ff29c6001f794e3000ffaa718083dd538c003fe29c6001ffd0e3000ffc8718007de438c003fea1c601ff750e3000ff88718003ff628c001ff3146000bf98a30007fac518002fd628c001fe3146020ffd4a30107fca518083fd528c041fe294601fffd0a300fffc851807ffd428c03ffe2146001ffcca3000ffc6518003de328c003fe9946001ff0ca3000fb86518003ff618c001ff30c6004bf98630007fac318002fd618c001fe30c6020ffd4630107fca318083fd518c041fe28c601fffd06300fffc831807ffd418c03ffe20c6001ffcc63000ffc6318003de318c003fe98c6001ff0c63000fb86318003ff218c001ff10c6000ff48630007f84318006fe608c041ffa846020ff94230107faa118083fc508c03fffa04601fff902300fffa811807ffc408c003ff9846001f7cc23000ff66118007fc308c003f
  | 5 => 0xc131167fecb908b2ff65c8459ff32e4203bf99721166fccb9080e7e65c8459feb2e422cbf59721006facb908027d65c8459fe32e4203bf19721127fec990892ff64c8449ff3264202bf99321127fac990892fd64c8449fe3264202bf19321127fea9908937f54c8449ff2a64224ff55321126faa990893fc54c8401ffb1e4200bfd8f2115ffcc790806fe63c8401feb1e4200bf58f2115ff8c790806fc63c8459ffa9e422bff94f21167faa7908affc53c8449ffa1e422bff90f21127fa87908affc43c8459ffa96422cff94b21167faa5908b3fc52c8449ffa164224ff90b21127fa8590893fc42c8457ff9964200ff8cb21007fa65908affc32c8459ffa8e4204ff94721167faa390813fc51c8449ffa0e4204ff90721127fa8390813fc41c8457ff98e4204ff8c721007fa6390813fc31c8401ffb064200ff98321005fcc190803fd60c84017eb064200ff18321167fea1908b3fe50c8459fea86422cff14321127fe8190893fe40c8449fea064224ff1032115ffe61908affc30c8409ffb2c4204bfd9621027fccb1080efe6588409bf32c42039f99621027facb108aafd6588409beb2c42009f59621027f8cb10812fc6588409ffb244204bfd9221027fcc91080afe6488409df3244202af99221027fac9108a6fd6488409deb244200af59221027f8c910812fc6488453ffaa44229dfd522114ffca9108a7fd5488453beaa44229ff15221027fec710812ff6388409ff31c4201bf98e21027bcc710806de6388409feb1c4200bf58e21027bac710802dd6388409fe31c4204bf18e21157fea7108a3fe5388455fea9c4228ff14e2114ffe87108a3fe4388453fea1c4228ff10e21135fac5108abff5288455ff294422aff54a21157f8a5108a7ff4288453ff2144229ff50a2114ff885108a3ff3288401ff1944200ff4ca21147f86510812fe6188409ffa8c4204ff94621027faa310813fc5188409ffa0c4204ff90621027fa8310813fc4188409ff98c4204ff8c621027fa6310813fc3188409ff90c4204fbc8621007ee4310813ff6088409ff3044200bf98221027fac110802fd6088409fe304422affd4221157fca1108abfd5088455fe2844229ffd022114ffc81108a7fd4088453fe2044228ffcc221147f8611089fff654844f7fb2a4227ff9952101dfcca9089ffd654844f7eb2a4227ff1952101df8ca9089bff644844d7fb224226ff99121015fcc89089bfd644844d7eb224226ff19121015f8c89089bff544844dbfaa24226ff95121137faa89089b7d544844dfe2a24200ffd8d21005fec690897fe63484037f31a4200ff58d21005fac690897fc63484037e31a4227ffd4d2112ffca69089ffd534844bfe29a4226ffd0d2112ffc869089bfd434844bfe21a4227ffd492113ffca49089ffd524844ffe2924226ffd0921137fc8490
  | 6 => 0x3eea1a6401ff10d3200dfec4990cbff524c865ff2926432ff54932197f8a4990c7ff424c863ff2126431ff5093218ff88499007ff324c803f79926401ff8c932007bc6499007fc324c803ee1926401fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299012fc614c865ffa8a6432ff94532197faa2990cbfc514c863ffa0a6431ff9053218ffa82990c7fc414c803ff98a6401ff0c532007fec099002ff604c801ff3026400ff58132007f8c099002fc604c865ffa826432ff94132197faa0990cbfc504c863ffa026431ff9013218ffa80990c7fc404c803ff9826401ff0c132027fecb18812ff658c409ff32c6203bf99631027facb188c2fd658c409fe32c6204bf19631027fec918812ff648c409ff3246202bf99231027fac9188befd648c409fe3246204bf1923117ffea9188bf7f548c45fff2a4622fff5523117efaa9188bffc548c4037eb1c6201ffd4e3100ffca718807fd538c403fe29c6201ffd0e3100ffc8718807fd438c403fe21c6204ffd8a31027fcc518802fe628c409feb146200bf58a31027f8c5188c3ff528c461ff2946230ff54a31187f8a5188bfff428c45fff214622fff50a3117ff88518807ff328c403ff1946201ff4ca3100ff86518812fe618c409ffa8c6204ff94631027faa318813fc518c409ffa0c6204ff90631027fa8318813fc418c409ff98c6204f7cc63100fee6318813fc318c409fa18c6204ffd8231027fcc118802fe608c409feb046200bf58231027f8c1188c3ff508c461ff2846230ff54231187f8a1188bfff408c45fff204622fff5023117ff88118807ff308c403fe1846201f70c231177feca988baff654c401bfb2a62009fd9531177fcca9880efe654c45dfeb2a622ebf59531177f8ca9880efc654c45dbe32a62039f1953116ffec8988b6ff644c45bff3226202bf9913116ffac8988b6fd644c45bfe3226202bf1913116ffea8988b77f544c45bff2a2622dff5513116efaa8988b7fc544c4097fb1a6201ffd4d3100ffca698807de534c403fea9a622ef754d3100ff8a698807ff434c403ff21a6201f790d3100ffa86988b7dd434c403fe21a6200ffd8931005fec498803fe624c401feb126200ff18931005f8c4988bbff524c45dff292622eff54931177f8a4988b7ff424c45bff212622dff5093116ff88498807ff324c403ff1926200f78c93100ffa6498807fc324c403ee1926201bfd8531177fea298813fe514c45dfea8a6204ff1453116ffe8298813fe414c45bfea0a6204ff1053100ffe6298807f7314c409ff18a6204f78c531027f86298813dc314c403fa18a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c0988bbff504c45dff282622eff54131177f8a0988b7ff404c45bff202622dff5013116ff88098807ff304c403ef9826201ff0
  | 7 => 0x802804000058028320120300600a01201801000044004008040080180081200c0000100e0020040000302402c0d8080040000001400002801807002000020070000080000d0080180100900e0000500301c00c0400f016008188270000ac0283602403c000070040080005b0000000400505803c110010040440300500004c00802002060028020000140600002c0080000402800804001008010028020200340081101a00803001036040010060041980000008801c0300000a01400801028028000110281300d8020121280580101a058038010080000501401e0f406004006028000050540000000f02a008018000040080200a0160100080c02e0380908601a0000000100000c0301000001c0000200006c0003c01c0181d805016004118000020000200901004c0603700201006004000000048150080180381e00404c0100400a02c078050000000681f0ba0000100a000004020150040000a0010000080600002200000001000048000000000101a01800e000000340000040080000c01c08803000000038000000080c85500207c0780100c09c088010260080c00104c000058020000000900000000000801078000008070100000f0070000140000b010024000030140200600000a0040004200001400007002010010041a7fecb190d2ff658c869ff32c6403bf996321a7facb190d2fd658c869fe32c6403bf1963219ffec9190ceff648c867ff3246402bf9923219ffac9190cefd648c867fe3246402bf1923219ffea9190cf7f548c867ff2a46433ff5523219efaa9190cffc548c8037eb1c6401ffd4e3200ffca719007fd538c803fe29c6401ffd0e3200ffc8719007fd438c803fe21c6401bf98a321a7fea5190d3fe528c869fea946434ff14a3219ffe85190cffe428c867fea146433ff10a3200ffe6519007df328c803f79946401ff0ca3200fd86519003ff618c801ff30c6404bf98632007fac319002fd618c801fe30c6434ffd46321a7fca3190d3fd518c869fe28c6433ffd063219ffc83190cffd418c867fe20c6401ffcc63200fbe6319007fc318c801ffb046400ff98232005fcc119003fd608c8017eb046400ff182321a7fea1190d3fe508c869fea846434ff1423219ffe81190cffe408c867fea046433ff1023200ffe6119007fc308c803ee1846432ffd9532195feca990037f654c8013fb2a6432ff9953201dfcca990cbfd654c8657eb2a6432ff1953201df8ca990cb7c654c8073e32a6431ffd913218dfec899003bf644c8015fb226431ff99132015fcc8990c7fd644c8637eb226431ff19132015f8c8990c7bc644c8055e3226431ffd513218efea8990c7fe544c863feaa26431df5513218ff8a899006ff634c803ffa9a6401ff94d3200ffaa699007fc534c803ffa1a6401ff90d3200fbc8699007fd434c86
  | 8 => 0xa1762066d89e208a9247a00342004a85440d679aa7c00062a00014a1082e89e880400098aad2c1aa1ab380000000006f45a200000033e238426b36aacbd076a3c647686000029e4880000000008b879488ab540000004f87dc00035e83a21c032000bf88acafacf00003428d65c6b6200005c06a9fc48a1ae0005801fe0000006e453a52ca5c7ccaba000c444220007b2000afea620008a846e9e06400008147e2bfe05033c8c8c780003b8516592000a9c0008064608320000000000000c2114802aa20001bc6022724426140006d43b0000000b4600000000000016674607c0009aa0000000003d0c42ba0230ce21aa5d42aac8a66865230200050eb72278caa8b090a0a6b4a146b2e49011254e2f45088d258c0d0622bc41d8048b868629a8456b6e094042a94b0070c284baea8ecb2a82ae0338baa99e38239859a138a420ca4800002a800043a0000002dc7b487a80a4342e60000006b600012e380c700006ae39682ec3442a986000b662ce0000001e805e0066c000052e000000000aae00099c8de000000000cd29cc2c4000000a24772462b74a8aa800403dc50615884236c72a4ae68c5f071c3ae78e0984b600000000035c4be9d66760e8bb2ca8172346c02720126246a768e6b44432bbcb7886c5a88ea170120b20b0cad0c5460874aa22902b68a4823eb80a0e4f4a1c0001c02fe4ac3dea16c2467448430a9607980002bc81eb902b675625e0000000005da0000000000007120000000e40000007becbca2eabe000b125a413a4e0898c5201a188b6463e3c8bee39e2543705d00006ac65c45468a1c63ee5e820c330a5a0009f821865085c4023d82d011e40e8ce0007f09ee6f60005ca00000038e32426a76871a5c420a5224d4a44000a529ec0000008da02abec77c89a2b474c5bc4f000077694aa72000000000000b6cb22b0817e1c217a84c19ec0a30cb8c7ae0000a241e5d24c8c3aba685ab34748216000ca287669223c0001f400051ca0cc3c0003ea9229f600083666007e5fa1a28cc0020480200d0040000200003002400000000048048010040080180000001c0b80d032110098000000601800102c00c0002c0020000700100a00000024008008010020020000281e0060380080001a0400180005c0000000f0000040301303a030090060760141d000010014158000020000281b0000dc0300e00000c000120000340080e03c0000380100e0040680501000000000054074080050240040200207007c000060000140000100c0040700e02007c098090620200180e0020080700600c0041604e0020740700200a0440200700612c01003002044010350140080180010c0040001000a0041a000002028000000200000000d0280000100000c0100880000a014000070000000002b0c402807801000018020020000000000400
  | 9 => 0x952874222486c5654c1a4b16092000c6aa92c127ba3f29d2c161ee85646aa0294404a4bc348360510a960ecb400006ca938882000438af8bface8be8c902d4c9693c8dc1182e48f2b84cd88c206600043ccee00044856e26e53696aab61cab7c5ccafcaf284e5947005f432e83c22a5ce2ae38a5466da3e867c25c7fe3867da414b8ea0a1e0000000000000a2c000012000ad4790cb803e0e0504c06000838966bda9c4250404b4e350c2a66296858a92abe04e6930a9008c01050a430ca6a5612416e15658e020b5a92007a654b9a128a680440683d676e000ab845047848e3943080b2762a4eb4c4d02baaa0cec5e02fc5380d434a564ae86240000001424366349463362be0ce77a0000000000000008460001b846cc8853406449e6ce67a1be49878427eab4866000000a2a552468b580307147aa1d22d8928b7a004358000ac27241ea000b2864473e0f611c4e849acb4abc3e251a24e29a7221045ae78a2b28e09ce3bec1e6c618686eca46aa0f4adca7e00c28c38821053c0bc1220960aea6a8e828a16806cae26d6688c500223682ee560c608d818e7b8084ae40e609c1448ec15c4aa4702b898e2f6844c7c63c72c9f23fa4823c43921da70a62cc4ec8626473a75e1401984167ceb3c2dab604fc3145f82705ba5be64c0000000006fe9be57aa8c834236c5e000b96c8e0000000e20dc98c3b24520000002d63f400031cb10000a34214000a405e46e2cd400061c6bc304000bc89f400085ed02000ccc7a200090e8d00008ba0f03661d40000000000004d20001482765b8ac4cde95a3a85b282018a9bc61aba25200007b01067967101e239a7444c64da0148e282207802cbe665a4f20002dea740009c60000003840007820003106d229c8166b0c26000c9c76c32ac1c4089623227605964200006100008785e60008f60005f238cc48000000a20000000c9a000000c64942000000c309820000525265180008be73c9b2a9e000a6465800044449415e9d037c8806cc0be68e8a6b26c462e04e201c6ee22e69c000d003bc5e23761f225accac00000000aec67e6786dc182c2c9b09365681a60b6aa4000c620f8410240000b76a3a0001b4110826c7a93480000005655ebe4b067a8000a106ea57ea584a2b920000004dc840890a604ca150b9845a28e1f039c0162a63c05ea88463a268bc6a507c822899a7d89d45980000c63e460c0000009406fc02421a130152958c1840a4ea374000000a6c44ca085fc6709989fa00088c20e2c61926bacba66a100c8c7c49f041890c000000000000000cf20000006d078825200000019c91ece69163fc000586000b1e3da77ecda0000009da7f24c4296000b824b28aa60400013200000081a0000000007e46906668ee8fc318070af60fa2c87e834e07282ccae29063091424a948c08bd8c3870e4f
  | 10 => 0x2a4febb64d8cc24468a0b5223263836464eaca18c2f26a04ee9b697e3522fa27a7d0058086aa661e52854056c184a702e2926bf28f47021a8cbe0281b6b1c8128fa7545903f631268491cb94af0428a3c47295ecf49048584b4bbe0d861841c03872813612c0de896bdc92c5883b6c321ec12a154cdc2863623f0b8a0eec10b24b569506c400098497a53ec68000bb0808b1a6a62c22cc1e497c7fa2ec5a0390ad800064615a5245304cecc6502a86c0c00094c85003c0602c00007eec74ab09c84d67d234cb326f2aeebf05824961340b8c6688888e9b416256ac2e11600097800042e4640d28c00004065f68a2780196550000c14c40912acc10c26281c0ea4a46b473875c2f02ca5ee3ec0002ac000a26a3221248c8c65c89800001780009542a20c40000000007e63a0c806ec1c814cbc060e0007e05c2b9e906000848000000c3e0001cc7d68700006facac0000546dea1e75a26c00013c000a4a36e9d800011aaa89720ba68288691a0000000000a80005d82eac7e000b7e09a0827fc1dc000ba47326801943200000003289ba1b0000bd65c02442562d22b00009c09925fe000000000000a54b020cc6945d631aa143ba4580009700007a47de578000a4c9b8918b5c0da026a6e000910a460004ec0009a2400000ca0b6a37a41a73479e1d60000000005ec606bcabf6bd437e9907083ca5aa65ec6e0000009a0000b509a60000000000000000000000007663a459e0b4a2842400256600a1ac4c027caea000bf4000000ce40003f86280000004b8bba63297600022093a3ac4b04a0076bea7061b2cb08e4b18b0e9a4c6c86a0003446a26f04f674e6e800000ea003e6740a78a8424c492372000b4214e66eb482826b81f897467290047aa6610ab885b033a8f85deac0b0a34084a354726bb4792c76c363b498861682437801e7bcb3a93e8bc6984e400000008ebce9ae3a62a0bd2736000548bfcad60008b43d265600000000096e190000000000000412b5ebb8686174774bcc19a0000008d48fe3a2234c8400000000000089471e600208b042486642040188109acbc23164de55c818cc8718a1857c908852cfe9e67caa7a0000f28ca0000000000000a40000000009ea83040c00070478689e08044a64828862066c8926b222427451e5766c2c5c872000000000000b30cce89c1023aa000758a0469a74200006216a3ce00096c4665326a8ab25724c23567647301fc58447e0081d0c828b229817c7ec59c9967f8c044a6696cc49de1dec5a33271603a956500cea2f8a3e24236ab2a8281ce87ccb61807eac4c42c260af406e0fcc4a2928f0c58b9cc2032695c20269ec9e8689e41c472e9c2a125a6ac8cfcade79c1a0226a066123cc99422c6e0a308a487e3006be64a55a13e3c27f655625800030e0a080e1ba50c7d40ac00060a046a38
  | 11 => 0xd060fe626cd61e6c947f46368645b60906c88540c0c98cfa54a9ca7acada5420880007c231e1f60005acace29447cb3e00000002e6a47c632c83e306a9a5740b000056228080c7c0750474cc0ae600000000000000077810e23a0007b66f821e7705dc00000000000000035ac28cf649c96404e1fac229febe2a88bde00092e9322a4642514ce005a9dcac6000aaa52a2668b65b4b2c8c445c5540c857043e55809e3fe4cc074036b7004ca986e6cd0a3645ed044ba440512c72c0e0aaa5e3e094e3d416c78cb147a6334ba8c9216475262e44e160baccf88ae8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc768c8101a67e658c8100067d658c81019ebe648c810006bd648c81000ede638c810006dd638c810006ee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c8100057f754c81003d7c754c8101967e654c8100067d654c810005bf744c810035bc744c81018ebe644c810006bd644c81000ede634c810006dd634c810006ee624c810006ed624c810005f7714c810025f4714c810005fb704c810005f8704c810025f576c8410006f576c84101ef7675c84100077575c84100277665c84100277565c8410027b664c8410027b564c84101e77754c84101e77554c8410027d663c8410027d563c8410025f672c8410027e672c8410026f762c8410027e662c8410006f562c8410027e562c8410006e562c8410005f570c84101def660c8410027f260c8410064ff768c010024fe768c01000cfd768c010024fc768c01003d7e758c0100057d758c0101067e658c0100067d658c0100febe648c010006bd648c01000ede638c010006dd638c010006ee628c010006ed628c010025f6718c010005f5718c010064ff764c0100f67e654c0100067d654c0100eebe644c010006bd644c01000ede634c010006dd634c010006ee624c010006ed624c010004fd76c80100e67e65c80100067d65c80100aebe64c8010006bd64c80100dede63c8010006dd63c8010006ee62c8010006ed62c8010025f471c8010007e721c8010004ff7688010004fd76880100d67e65880100067d65880100a6be6488010006bd64880100cede6388010006dd6388010006ee6288010006ed6288010025f67188010005f571880101d7e42188010004ff76480100057f754801003d7c75480100c67e65480100067d6548010005bf7448010035bc74480100bebe6448010006bd6448010005df734801002ddc73480100b6de6348010006dd6348010006ee6248010006ed6248010005f77148010025f47148010007e72148010004ff7608010024fe7608010004fd7608010024fc760801003d7e75080100057d750801009e7e65080100067d6508010096be6408010006bd640801008ede6308010006dd6308010006ee6208010006ed6208010025f67108010005f571080101cfe42108010025f77644010006f77644010004f776440100077775440101bf747544010027766544010027756544010007b774440101b7b47444010027b66444010027b564440101b77754440101b7755444010007d77344010007d47344010027d66344010027d56344010007e77244010005f67244010005f47244010007e47244010005e47244010027e66244010027e56244010025f77044010027f370440101c6f66044010027f260440101bff250440101bff150440101b7f340440101b7f040440101aff330440101aff03044010007f22044010007f12044010
  | 1 => 0x8810026ee7298810006ef5298810006ee5298810006ed5298810006ec5298810006ef4298810006ee4298810006ed4298810006ec4298810006ef3298810006ec3298810024fe7198810024fc7198810026ee2198810026ec2198810006ef7598810006ee7598810006ed7598810006ec7598810006ef7498810006ee7498810006ed7498810006ec7498810006ef54988100066f5498810006ee5498810006ed54988100066d5498810006ec5498810006ef7398810006ee7398810006ed7398810006ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810026ef7198810026ee7198810026ed7198810026ec7198810026ef5198810026ee5198810026ed5198810026ec5198810026ef4198810026ee4198810026ed4198810026ec4198810026ef3198810026ee3198810026ed3198810026ec3198810006ee7098810006ec7098810006ef5098810006ee5098810006ed5098810006ec5098810006ef4098810006ee4098810006ed4098810006ec4098810006ef3098810006ec3098810026ef1098810026ee1098810026ed1098810026ec1098810004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc74588100067f54588100067d5458810004ff735881000cfe735881000cfc7358810026ef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef4258810006ee4258810006ed4258810006ec4258810006ef3258810006ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026f47158810024f47158810026ee2158810026ec2158810026f421588100dcff70588100b4fd7058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef54588100066f5458810006ee5458810006ed54588100066d5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026e47158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec3158810006ee7058810006ec7058810006ef5058810006ee5058810006ed5058810006ec5058810006ef4058810006ee4058810006ed4058810006ec4058810006ef3058810006ec3058810026ef1058810026ee1058810026ed1058810026ec1058810004ff768c810024fe768c810004fd768c810024f
  | 2 => 0x3e7f70594100067e705941003e7d705941003e7c70594100067f40594100067e40594100067d40594100067c40594100067f30594100067c30594100267f10594100267e10594100267d10594100267c1059410006bf7559010006be75590100063e7559010006bd75590100063d7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc2159010036bf7059010006be7059010036bd7059010036bc7059010006bf5059010006be5059010006bd5059010006bc5059010006bf3059010006bc3059010026bf1059010026be1059010026bd1059010026bc1059010004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10026df7358c10006df5358c1002ede5358c10006dd5358c1002edc5358c10006df4358c1002ede4358c10006dd4358c1002edc4358c10004ff7258c10004fc7258c1002edf3258c1002edc3258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c10026de3158c10026dc3158c1000cff7058c1000cfd7058c1002cfc7058c1002edc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c100065f5458c10006de5458c10006dd5458c100065d5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c10006de7058c10006dc7058c10006df5058c10006de5058c10006dd5058c10006dc5058c10006df4058c10006de4058c10006dd4058c10006dc4058c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff759881001cfe7598810004fd759881001cfc7598810004ff7498810014fe7498810004fd7498810014fc74988100067f54988100067d549881000cfe7398810004fd739881000cfc739
  | 3 => 0xc624c510005fb704c510005f8704c510004fe76c851005d7e75c85100057d75c85100067f65c85101667c65c8510006bf64c8510126bc64c8510006df63c851015edc63c8510006ef62c8510006ec62c8510005fa70c8510005f970c8510004fc76485100067f654851013e7c6548510006bf6448510136bc6448510006df634851012edc6348510006ef6248510006ec6248510005fb7048510005f87048510027f01048510074fe768c11005d7e758c1100057d758c1100067f658c1101067c658c110006bf648c1100febc648c110006df638c11000edc638c110006ef628c110006ec628c11000cff764c11004cfd764c110024fc764c1100067f654c1100f67c654c110006bf644c1100eebc644c110006df634c11000edc634c110006ef624c110006ec624c110005f7714c110025f4714c110024fe76c81100067f65c81100e67c65c8110006bf64c81100aebc64c8110006df63c81100dedc63c8110006ef62c8110006ec62c8110025f671c8110005f571c8110004fe76881100067f65881100d67c6588110006bf64881100a6bc6488110006df63881100cedc6388110006ef6288110006ec6288110004ff7648110004fd7648110024fc76481100057f754811005d7c75481100067f65481100c67c6548110005bf7448110055bc7448110006bf64481100bebc6448110005df734811004ddc7348110006df63481100b6dc6348110006ef6248110006ec6248110005f77148110025f47148110004fe760811005d7e75081100057d75081100067f650811009e7c6508110006bf6408110096bc6408110006df630811008edc6308110006ef6208110006ec62081100067f658411006e7c6584110006bf6484110046bc6484110006df6384110066dc6384110006ef6284110006ec6284110025fa7084110026fb6084110025f67684110026f67684110024f676841100077765841101ff746584110007b764841101f7b464841101f77754841101f7755484110007d76384110007d46384110007e76284110006f66284110006f46284110007e46284110006e46284110025f67084110026f76084110027f360841100067f74594100047f74594100067e74594100067d74594100047d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c2159410
  | 4 => 0x891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed6218910004ff751891001cfe7518910004fd751891001cfc7518910004ff7418910014fe7418910004fd7418910014fc74189100067f54189100067d541891000cfe7318910004fd731891000cfc7318910006ee7218910006ef5218910006ee5218910006ed5218910006ec5218910006ef4218910006ee4218910006ed4218910006ec4218910006ef3218910006ec3218910024fe7118910024fc71189100ccfe701891008cfc7018910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac64189100076f54189100076d5418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189101cfeb10189101cfe81018910006ef7518910006ee7518910006ed7518910006ec7518910006ef7418910006ee7418910006ed7418910006ec7418910006ef54189100066f5418910006ee5418910006ed54189100066d5418910006ec5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec4318910006ef71189101ceee7118910006ed71189101ceec7118910006ef51189101ceee5118910006ed51189101ceec5118910006ef41189101ceee4118910006ed41189101ceec4118910006ef31189101ceee31189101ceec31189101ceef7018910006ed7018910006ef5018910006ee5018910006ed5018910006ec5018910006ef4018910006ee4018910006ed4018910006ec4018910006ef3018910006ec30189101ceef1018910006ed10189101ceec1018910004ff768c910004fe768c910004fd768c910004fc768c9100067f658c9101a67c658c910006bf648c91019ebc648c910006df638c91000edc638c910006ef628c910006ec628c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c91005d7c754c9100067f654c9101967c654c910005bf744c910055bc744c910006bf644c91018ebc644c910006df634c91000edc634c910006ef624c910006ec624c91000cfc764c5100057f754c51005d7c754c5100067f654c5101767c654c510006bf644c51016ebc644c510006df634c51000edc634c510006ef624c510006e
  | 5 => 0x6ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef42d8910006ee42d8910006ed42d8910006ec42d8910006ef32d8910006ec32d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d89100076f54d89100076d54d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89101d7eb10d89101d7e810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d89100066f54d8910006ee54d8910006ed54d89100066d54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d89101d6ee71d8910006ed71d89101d6ec71d8910006ef51d89101d6ee51d8910006ed51d89101d6ec51d8910006ef41d89101d6ee41d8910006ed41d89101d6ec41d8910006ef31d89101d6ee31d89101d6ec31d89101d6ef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910006ef30d8910006ec30d89101d6ef10d89101d6ec10d891005d7e75989100057d75989100067f65989100067c6598910055be7498910005bd7498910006bf6498910006bc649891004dde7398910005dd7398910006df6398910006dc6398910006ef6298910004ff759891001cfe75989100067e759891001c7e7598910004fd75989100067d75989100047d759891001cfc7598910004ff7498910014fe7498910006be7498910014be7498910004fd7498910006bd7498910004bd7498910014fc74989100067f54989100067d549891000cfe7398910006de739891000cde7398910004fd7398910006dd7398910004dd739891000cfc7398910004fe7298910004ee7298910004fd7198910006f57198910004fd7098910006f970989100057f755891005d7c75589100067f65589100067c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df735891004ddc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df735891000cfe735
  | 6 => 0xe72d8d10004fd72d8d1004edf32d8d1004edc32d8d10024fe71d8d1004cfd71d8d10024fc71d8d1004edf31d8d1000cfe70d8d10024fd70d8d1000cfc70d8d1004edf30d8d1004dde76d8d1000cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075f54d8d100075d54d8d1020fdb10d8d1020fd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d100065d54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1020ede71d8d10006dd71d8d1020edc71d8d10006df51d8d1020ede51d8d10006dd51d8d1020edc51d8d10006df41d8d1020ede41d8d10006dd41d8d1020edc41d8d1020ede21d8d1020edc21d8d1020edf70d8d1004ede70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d1020edf10d8d1020edc10d8d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10055bc7458d10006bf6458d10006bc6458d1004edc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d1004cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10004fc7258d10006ec7258d10004ec7258d10064ff7158d10006f77158d10074ff7058d10006fb7058d10005de7618d1004ede7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d100075d5418d10206df6018d10207db1018d10207d81018d100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d891000cfe73d8910004fd73d891000cfc73d8910
  | 7 => 0x821006d7e75082100057d7508210006ee6208210006ed6208210025f67108210005f57108210007e42108210005f576c4210026f576c42102277754c42102277554c4210005f672c4210025f472c4210027f260c421005d7e76d951005e7e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e63d95100067c63d951021f7b10d951021f7810d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067c32d95100067f71d951021e7e71d951005e7d71d951021e7c71d95100067f41d951021e7e41d95100067d41d951021e7c41d95100067f31d951021e7e31d951021e7c31d951021e7e21d951021e7c21d951021e7f70d951005e7e70d951005e7d70d951005e7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067c30d951021e7f10d951005e7d10d951021e7c10d9510055be76d9110056be76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110217bb10d9110217b810d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006bc32d9110006bf71d9110216be71d9110056bd71d9110216bc71d9110006bf51d9110216be51d9110006bd51d9110216bc51d9110006bf31d9110216be31d9110216bc31d9110216be21d9110216bc21d9110216bf70d9110056be70d9110056bd70d9110056bc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006bc30d9110216bf10d9110056bd10d9110216bc10d911000cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1004ede63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d10006df53d8d1004ede53d8d10006dd53d8d1004edc53d8d10006df43d8d1004ede43d8d10006dd43d8d1004edc43d8d10004f
  | 8 => 0x4fd73d8a1000cfc73d8a10006f571d8a101d6ee21d8a101d6ec21d8a10006fa70d8a10004fd7698a10006ef6298a10004ff7598a1001cfe7598a10004fd7598a1001cfc7598a10004ff7498a10014fe7498a10004fd7498a10014fc7498a100067f5498a100067d5498a1000cfe7398a10004fd7398a1000cfc7398a100057f7558a1006d7c7558a10005bf7458a10045bc7458a10005df7358a10065dc7358a10004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10004fd7458a10014fc7458a10006bc7458a10014bc7458a100067f5458a100067d5458a10004ff7358a10006df7358a10004df7358a1000cfe7358a1000cfc7358a10006dc7358a1000cdc7358a10006ef7258a10006f77158a1006d7e7518a100057d7518a10006ed6218a10004ff7518a1001cfe7518a100067e7518a1001c7e7518a10004fd7518a100067d7518a100047d7518a1001cfc7518a10004ff7418a10014fe7418a10004fd7418a10014fc7418a100067f5418a100067d5418a1000cfe7318a10004fd7318a1000cfc7318a10004fe7218a10006ee7218a10006f57118a101ceee2118a101ceec2118a10006fa7018a10004ff768ca10004fe768ca10004fd768ca10004fc768ca10006df638ca1000edc638ca10004ff764ca10004fe764ca10004fd764ca10004fc764ca100057f754ca1006d7c754ca10005bf744ca10045bc744ca10005f7714ca10025f4714ca1000cff764c6100057f754c61006d7c754c61000ede634c610006dd634c610005fb704c610005f8704c61006d7e75c86100057d75c8610006ee62c8610006ed62c8610005fa70c8610005f970c8610006f576c86102377675c86100077575c86101df7754c86101df7554c8610025f672c8610006f762c8610007e662c8610006f562c8610007e562c8610007f270c8610005f570c8610007f170c8610026f660c8610006ee6248610006ed6248610027e42148610005fb7048610005f87048610005f57608610026f5760861022f77540861022f755408610027e67208610006f76208610007e76208610006f56208610007e46208610005f57008610027f2600861000cfe768c210024fd768c21006d7e758c2100057d758c21000ede638c210006dd638c210025f6718c210005f5718c21002cff764c210006df634c21000edc634c210006ef62c8210006ec62c8210007e721c8210024fd7688210006ee6288210006ed6288210025f67188210005f57188210007e421882100057f754821006d7c7548210005bf7448210045bc7448210005df7348210065dc7348210006ef6248210006ec6248210005f77148210025f47148210007e72148210024fd760
  | 9 => 0xf7558f100067f7558f100047f7558f1001cfe7558f10004fd7558f1001cfc7558f100067c7558f1001c7c7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10026df7358f10076de5358f10006dd5358f10076de4358f10006dd4358f10004ff7258f10004fc7258f10076dc3258f10024fc7158f10026de3158f10026dc3158f10076df3058f10004ff7598b1001cfe7598b100067e7598b1001c7e7598b10004fd7598b100067d7598b100047d7598b1001cfc7598b10004ff7498b10014fe7498b10004fd7498b10014fc7498b100067f5498b100067d5498b1000cfe7398b10004fd7398b1000cfc7398b10026ee7298b10024fe7198b10026ee2198b10026ec2198b10026f41098b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b1000cfe7358b1000cfc7358b10026ef7258b10024fc7158b10026ee2158b10026ec2158b10004ff768cb10024fe768cb10004fd768cb10024fc768cb1000ede638cb10006dd638cb10004ff764cb10024fe764cb10004fd764cb10024fc764cb100057f754cb100857c754cb10005bf744cb1007dbc744cb10005fb704cb10005f8704cb1004cfd768c3100857e758c3100057d758c31020edf638c31000edc638c31000cff764c310024fc764c31000ede634c310006dd634c310005f7714c310025f4714c310006ee62c8310006ed62c8310025f671c8310005f571c83101d6ef62883101d6ec62883100057f75483100857c7548310005bf744831007dbc7448310005df7348310075dc7348310006ee6248310006ed6248310005f77148310025f471483100857e75083100057d75083101ceef62083101ceec620831006d7e75d8e100057d75d8e10066de63d8e10004ff75d8e1001cfe75d8e100067e75d8e1001c7e75d8e10004fd75d8e100067d75d8e100047d75d8e1001cfc75d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e100067f54d8e100067d54d8e10064fd73d8e10066de53d8e10006dd53d8e10066de43d8e10006dd43d8e10004fe72d8e10004fd72d8e10066dc32d8e10006f571d8e1020ede31d8e1020edc31d8e10006fa70d8e10066df30d8e1000cff7658e10066dc6358e10004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e100067f5458e100067d5458e10006df7358e10004ff7258e10004fc7258e10066df3158e10024fc7058e10066dc3058e10004ff75d8a1001cfe75d8a10004fd75d8a1001cfc75d8a10004ff74d8a10014fe74d8a10004fd74d8a10014fc74d8a100067f54d8a100067d54d8a1000cfe73d8a10
  | 10 => 0xc420004fd768c4201867e658c4200067d658c420026f6618c420006f5618c420004ff764c420004fd764c420004fc764c4200057f754c42009d7c754c4201767e654c4200067d654c42000ede634c420006dd634c420005ef724c420005ec724c420026f6614c420006f5614c420005fb704c420005f8704c420024fd76c842009d7e75c84200057d75c84201667e65c84200067d65c84202c6ee62c8420026f661c8420006f561c8420005fa70c8420005f970c8420004fd768842009d7e75884200057d75884201567e65884200067d6588420095be7488420005bd748842008dde7388420005dd7388420005ed76884201ceed7688420004ed76884201cf6e75884201cf6d75884202bf6e65884200076d65884201cfae74884201cfad74884202b76f54884202b76d54884201cfce73884201cfcd73884201cdee71884201ceed6188420005ed70884201d6ee6088420004ff764842013e7e65484200067d65484202aeee624842011e7e65084200067d6508420026f66108420006f56108420007e52108420005fa7008420005f970084202a76e65084200076d650842029f6f540842029f6d54084201cdee71084201cfe671084201cfe661084201ceed6108420007e561084201cfea7008420005ed70084201cfe970084201d6ee60084200ccff768c02000cfe768c02000cfd768c02008cfc768c02009d7e758c0200057d758c0201067e658c0200067d658c02000ede638c020006dd638c020005ee728c020005ed728c0200ccff764c0200f67e654c0200067d654c0200e67e65c80200067d65c80202976e65c80200076d65c802028f6f54c802028f6d54c80201cdee71c8020006ed61c80200d67e65880200067d6588020275ed728802026eee62880202877a658802000779658802027f7b548802027f795488020275f9728802026efa6288020007ea6288020007ea2188020007e82188020004ff76480200057f754802009d7c75480200c67e65480200067d6548020005bf7448020095bc7448020005df734802008ddc7348020005f77148020005f47148020005ef7648020006ef7648020004ef76480200076f754802023f6c754802023f6e65480200076d6548020007af7448020257ac74480202576f54480202576d5448020007cf7348020007cc7348020007e771480201cdec7148020007e47148020005e47148020006ed6148020265ef704802025eee604802023fea504802023fe95048020005fb7648020006fb7648020004fb76480200077b754802023f78754802023f7a6548020007796548020007bb7448020257b874480202577b5448020257795448020007db7348020007d8734802024dfb7248020007eb7248020246fa6248020007ea624802023fea524802023fe95248020007f37148020007f07148020004f
  | 11 => 0x2cfac64881202cf6f54881202cf6d5488120007cf6388120007cc6388120005ed7188120007e761881201d6ec6188120007e46188120006e46188120007eb608812009d7f765942009e7f765942001c7f76594200057f74594200057d74594200067f64594200067e64594200067d64594200067c64594200067e63594200067c63594200067f74594200047f74594200067e74594200067d74594200047d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c435942009e7f72594200067e725942009e7d725942009e7c72594200067f42594200067e42594200067d42594200067c42594200067f32594200067c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067e41594200067d41594200067c41594200067f31594200067c315942009e7f70594200067e705942009e7d705942009e7c70594200067f40594200067e40594200067d40594200067c40594200067f30594200067c305942009e7c205942009d7e75d8c200057d75d8c200067e65d8c200067d65d8c2008ede63d8c20004ff75d8c2001cfe75d8c200067e75d8c2001c7e75d8c20004fd75d8c200067d75d8c200047d75d8c2001cfc75d8c20004ff74d8c20014fe74d8c20004fd74d8c20014fc74d8c200067f54d8c200067d54d8c2008cfd73d8c200dcfe72d8c20006ee72d8c20024fe71d8c20004fd71d8c200ccfe70d8c20006fa70d8c2000cff7658c200067e6558c200067d6558c2008edc6358c20004ff7558c2001cfe7558c20004fd7558c2001cfc7558c20004ff7458c20014fe7458c20004fd7458c20014fc7458c200067f5458c200067d5458c20006df7358c2008ede4358c20006dd4358c2000cff7258c2000cfd7258c2008cfc7258c2008edc3258c20004ff7158c20024fc7158c2008edf3158c2008cfc7058c2008edc3058c200dcff768c82000cfd768c8201a67e658c8200067d658c82000ede638c820006dd638c820005fa708c820005f9708c8200dcff764c8200057f754c82009d7c754c8201967e654c8200067d654c820005bf744c820095bc744c82009d7e75d84200057d75d84200067e65d84200067d65d84200067e65984200067d6598420006f761984200067e65584200067d6558420004ff755842001cfe7558420004fd755842001cfc7558420004ff7458420014fe7458420004fd7458420014fc74584200067f54584200067d5458420004ff735842000cfe735842000cfc7358420006f64158420006f54158420024ff705842009d7e75184200057d75184200067e65184200067d6518420095be7418420005bd741842008dde7318420005dd7318420026f66118420006f56118420024ff768c420004fe768
  | 12 => 0x54018520006f44018520006f73018520006f43018520006f52018520004fe768c520004fd768c520024fc768c5200067f658c5201867c658c520006bf648c52017ebc648c520006df638c52000edc638c520005ee728c520005ed728c520006f7618c520026f4618c520004ff764c520004fe764c520004fc764c5200057f754c5200c57c754c5200067f654c5201767c654c520006bf644c52016ebc644c520006df634c52000edc634c520006f7614c520026f4614c520004fe76c85200c57e75c85200057d75c85200067f65c85201667c65c8520006bf64c8520126bc64c8520006df63c852015edc63c8520026f461c8520005ee76c8520006ee76c8520004ee76c85203176e75c85200076d75c85200076f65c85203176c65c8520007af64c852030fac64c852030f6f54c852030f6d54c8520007cf63c8520007cc63c8520007e761c8520026ee61c8520026ec61c8520007e461c8520026e461c8520005ee70c85200c57e75885200057d75885200067f65885201567c65885200bdbe7488520005bd7488520006bf648852014ebc64885200b5de7388520005dd7388520006df6388520146dc6388520305ed7288520006f76188520026f46188520005fa7088520005f97088520024fc76485200067f654852013e7c6548520006bf6448520136bc6448520006df634852012edc6348520006f76148520026f46148520005fb7048520005f87048520024ec76485200076f65485202ff6c6548520007af64485202f7ac64485202f76f54485202f76d5448520007cf6348520007cc6348520007e77148520007e76148520026ee6148520026ec6148520007e46148520026e46148520007eb7048520005ec7048520007e87048520004fe76085200067f650852011e7c6508520006bf6408520116bc6408520006df630852010edc63085202edee7208520006f76108520026f461085200dcfe768c1200c57e758c1200057d758c1200067f658c1201067c658c120006bf648c1200febc648c120006df638c12000edc638c120006f7618c120006f4618c12000cff764c1200b4fd764c12000cfc764c1200067f654c1200f67c654c120006bf644c1200eebc644c120006df634c12000edc634c120005ef724c120005ec724c120006f7614c120006f4614c1200067f65c81200e67c65c8120006bf64c81200aebc64c8120006df63c81200dedc63c8120006f761c8120006f461c81200077b65c81202e77865c8120007bb64c81202dfb864c81202df7b54c81202df7954c8120007db63c8120007d863c8120007f361c8120007f061c8120007eb21c8120007e921c81200067f65881200d67c6588120006bf64881200a6bc6488120006df63881200cedc6388120006f76188120006f461881200076f65881202d76c6588120007af6488120
  | 13 => 0x85200077554d8520006f763d8520007d763d8520006d763d8520006f663d8520006f563d8520006f463d8520007d463d8520006d463d8520007e772d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d85200067754d8520006f654d8520006f554d85200067554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d8520006f653d8520006f553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d8520006f772d8520006f752d8520006f652d8520006f552d8520006f452d8520006f742d8520006f642d8520006f542d8520006f442d8520006f732d8520006f632d8520006f532d8520006f432d8520006f770d8520006f570d8520006f750d8520006f650d8520006f550d8520006f450d8520006f740d8520006f640d8520006f540d8520006f440d8520006f730d8520006f430d85200c57e75985200057d75985200067f65985200067c65985200bdbe7498520005bd7498520006bf6498520006bc64985200b5de7398520005dd7398520006df6398520006dc6398520006f761985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520006bf6458520006bc6458520005df73585200b5dc7358520006df6358520006dc63585200067f65185200067c6518520006bf6418520006bc6418520006df6318520006dc6318520026f66118520006f56118520005f67618520006f67618520006f76518520007776518520006776518520006f66518520006f56518520006f46518520007746518520006746518520006f76418520007b76418520006b76418520006f66418520006f56418520006f46418520007b46418520006b46418520007775418520007755418520006f76318520007d76318520006d76318520006f66318520006f56318520006f46318520007d46318520006d46318520007e57218520026f77518520026f67518520026f57518520026f47518520026f77418520026f67418520026f57418520026f47418520006f75418520006775418520006f65418520006f55418520006755418520006f45418520026f77318520026f67318520026f57318520026f47318520006f75318520006f65318520006f55318520006f45318520006f74318520006f64318520006f54318520006f44318520026f77218520006f75218520006f65218520006f55218520006f45218520006f74218520006f64218520006f54218520006f44218520006f73218520006f63218520006f53218520006f43218520026f77018520026f57018520006f75018520006f65018520006f55018520006f45018520006f74018520006f64018520006f
  | 14 => 0x6dc74d8d20006df54d8d200065f54d8d20006de54d8d20006dd54d8d200065d54d8d20006dc54d8d20006df72d8d200b6de72d8d20006dd72d8d20006df52d8d20006de52d8d20006dd52d8d20006dc52d8d20006df42d8d20006de42d8d20006dd42d8d20006dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d20006df70d8d200b6de70d8d20006dd70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d20006df40d8d20006de40d8d20006dd40d8d20006dc40d8d200057f7558d200c57c7558d200067f6558d200067c6558d20005bf7458d200bdbc7458d20006bf6458d20006bc6458d200b6dc6358d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d200067f5458d200067d5458d200b4ff7358d20006df7358d200ccff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20024fc7158d20006f47158d20024f47158d200dcff7058d20006fb7058d20005de7618d200b6de7618d20004de7618d20006df6518d200075f6518d200065f6518d20006de6518d20006dd6518d20006dc6518d200075c6518d200065c6518d20006df6418d200079f6418d200069f6418d20006de6418d20006dd6418d20006dc6418d200079c6418d200069c6418d200075f5418d200075d5418d200ccfe768c9200067f658c9201a67c658c920006bf648c92019ebc648c920006df638c92000edc638c92000cfc764c9200057f754c9200c57c754c9200067f654c9201967c654c920005bf744c9200bdbc744c920006bf644c92018ebc644c920006df634c92000edc634c9200b7cc324c920005fb704c920005f8704c9200067f65d85200067c65d8520006bf64d8520006bc64d8520006df63d8520006dc63d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d852000cfe73d8520004fd73d852000cfc73d8520006f751d8520006f651d8520006f551d8520006f451d8520006f741d8520006f641d8520006f541d8520006f441d8520006f731d8520006f431d8520024fe70d8520006f765d85200077765d85200067765d8520006f665d8520006f565d8520006f465d85200077465d85200067465d8520006f764d8520007b764d8520006b764d8520006f664d8520006f564d8520006f464d8520007b464d8520006b464d85200077754d
  | 15 => 0xc64d95200073c64d95200063c64d95200067e63d95200067c63d95200067f74d95200047f74d95200067e74d95200067d74d95200047d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95200c67e72d95200c67d72d95200c67c72d95200067f42d95200067e42d95200067d42d95200067c42d95200067f32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067c31d95200067f70d95200c67e70d95200c67d70d95200c67c70d95200067f40d95200067e40d95200067d40d95200067c40d95200067f30d95200067c30d95200c67d20d95200bdbe76d91200bebe76d9120014be76d91200073f75d91200073c75d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006be63d9120006bc63d9120006bf75d91200063f75d9120006be75d9120006bd75d9120006bc75d91200063c75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120006bf72d91200bebe72d91200bebd72d91200bebc72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf32d9120006bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006bc31d9120006bf70d91200bebe70d91200bebd70d91200bebc70d9120006bf50d9120006be50d9120006bd50d9120006bc50d9120006bf30d9120006bc30d91200bebd20d912000cfe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d200b6de63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d20006df53d8d200b6de53d8d20006dd53d8d200b6dc53d8d20006df43d8d200b6de43d8d20006dd43d8d200b6dc43d8d2000cfe72d8d200b4fd72d8d2000cfc72d8d200b6df32d8d20024fe71d8d20004fd71d8d200b6df31d8d200b6dc31d8d200b4fd70d8d200b6df30d8d200b5de76d8d2000cde76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d200079f64d8d200069f64d8d20006de64d8d20006dd64d8d20006dc64d8d200079c64d8d200069c64d8d200075f54d8d200075d54d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20
  | 16 => 0x8e200cede63d8e20004ff75d8e2001cfe75d8e200067e75d8e2001c7e75d8e20004fd75d8e200067d75d8e200047d75d8e2001cfc75d8e20004ff74d8e20014fe74d8e20006be74d8e20014be74d8e20004fd74d8e20006bd74d8e20004bd74d8e20014fc74d8e200067f54d8e200067d54d8e200ccfd73d8e200cede43d8e20006dd43d8e20006ed72d8e200cedc32d8e20024fe71d8e20004fd71d8e20006fa70d8e2000cff7658e200cedc6358e20004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e200067f5458e200067d5458e20006df7358e200cedf3258e20004ff7158e20024fc7158e200cedf3158e200cedc3058e200b4fd768ca20006df638ca2000edc638ca2000cff764ca200057f754ca200d57c754ca20005bf744ca200a5bc744ca2000ede634ca20006dd634ca20005fb704ca20005f8704ca20006f761986200057f75586200d57c7558620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620014fe7458620004fd7458620014fc74586200067f54586200067d5458620004ff735862000cfe735862000cfc73586200d57e75186200057d75186200a5be7418620005bd74186200cdde7318620005dd7318620026f66118620006f56118620024ff768c620004fe768c620004fd768c620004ff764c620004fd764c620004fc764c6200057f754c6200d57c754c62000ede634c620006dd634c620005ef724c620005ec724c6200d57e75c86200057d75c86200d57e75886200057d75886200a5be7488620005bd74886200cdde7388620005dd7388620026f66188620006f56188620005fa7088620005f970886201d76e75886201d76d75886201d7ae74886201d7ad74886203376f54886203376d54886201d7ce73886201d7cd73886201d7e661886201d6ed6188620007e561886201d7ea7088620005ed70886201d7e97088620024ff7648620026f66148620006f56148620005fb7048620005f87048620026f46108620007e52108620005ed76086201d6ed760862032f6f540862032f6d54086201d7e67108620007e761086201d6ed61086201d7e46108620005ed700862000cfe768c22000cfd768c2200d57e758c2200057d758c22000ede638c220006dd638c220005ee728c220005ed728c22008cff764c220005ed76c8220006ed76c82203276f54c82203276d54c82201d5ee71c8220006ed61c822031fea50c822031fe950c8220005f976c8220006f976c82203277b54c82203277954c822031fea52c822031fe952c82200c57e76d95200c67e76d952001c7e76d95200057f74d95200057d74d95200067f64d95200067e64d95200067d64d95200067
  | 17 => 0x26f46108530005fa7008530005f9700853034f5e758c1300075d758c13034edf658c13034edd658c130346df648c130346dd648c1303475f548c1303475d548c130006dc628c130005dd718c13020edc618c13000dde708c13000fda708c13000edf608c13000fdb608c1300dede63d8f20004ff75d8f2001cfe75d8f20004fd75d8f2001cfc75d8f20004ff74d8f20014fe74d8f20004fd74d8f20014fc74d8f200067f54d8f200067d54d8f200dcfd73d8f20006ee72d8f20024fe71d8f20004fd71d8f200dedf31d8f20006f970d8f200dedc30d8f2000cff7658f200057f7558f200e57c7558f200dedc6358f20004ff7558f200067f7558f200047f7558f2001cfe7558f20004fd7558f2001cfc7558f200067c7558f2001c7c7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f200067f5458f200067d5458f20006df7358f200dede5358f20006dd5358f200dede4358f20006dd4358f200dedc3258f20004ff7158f20024fc7158f200dedc3158f200dedf3058f2000cfd768cb2000ede638cb20006dd638cb20005fa708cb20005f9708cb2008cff764cb200057f754cb200e57c754cb20005bf744cb200adbc744cb200dfcc324cb200e57e75d87200057d75d87200adbe74d8720005bd74d87200ddde73d8720005dd73d87200e57e75987200057d75987200adbe7498720005bd74987200ddde7398720005dd7398720006f76198720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc74587200067f54587200067d5458720004ff735872000cfe735872000cfc7358720026f66118720006f56118720024ff768c720004fe768c720004fd768c72000ede638c720006dd638c720005ee728c720005ed728c720004ff764c720004fd764c720004fc764c7200057f754c7200e57c754c720006df634c72000edc634c720005fb704c720005f8704c720024fd76c87200e57e75c87200057d75c8720026f661c8720006f561c8720005fa70c8720005f970c8720024ed76c872033f6e75c87200076d75c87202c76f54c87202c76d54c8720026ee61c8720007e661c8720007e561c8720026ec61c8720005ee70c8720007ea70c8720007e970c87200e57e75887200057d75887200adbe7488720005bd74887200ddde7388720005dd7388720005ef7648720006ef76487202af6f54487202af6d5448720007e77148720026ee6148720026ec6148720005ec7048720026f66108720006f56108720005fa7008720005f970087200b4fd768c3200e57e758c3200057d758c320006df638c32000edc638c32000cff764c32000cfc764c32000ede634c320006dd634c320005ef724c320005ec724c3200d57e75d8e200057d75d8e200a5be74d8e20005bd74d
  | 18 => 0x5618c63020fda708c630005dd708c63020fd9708c63000ede608c63000fda608c630004ff76c8630004fe76c8630004fd76c86301057e75c86300057d75c86301667e65c86300067d65c863000dde73c8630005dd73c8630006ee62c8630006ed62c8630024ff7688630004fe7688630004fd76886301057e75886300057d75886301567e65886300067d65886300fdbe7488630005bd748863000dde7388630005dd7388630004ff7648630004fd7648630004fc764863013e7e65486300067d6548630005df734863000ddc7348630006ee6248630006ed6248630024ff7608630004fe7608630004fd760863011e7e65086300067d650863020ddf730863000ddc7308630005fa7008630005f97008630004ff75d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d89300ceee32d89300ceed32d8930024fe71d8930004fd71d8930006ef62989300b5f970989300057f75589300f57c7558930005bf74589300edbc7458930005f77158930005f471589300ddfb70589300f57e75189300057d7518930006ed6218930004ff751893001cfe75189300067e751893001c7e7518930004fd75189300067d75189300047d751893001cfc7518930004ff7418930014fe7418930004fd7418930014fc74189300067f54189300067d541893008eee321893008eed3218930024fe7118930004fd711893008edf311893008edc3018930004ff75d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d8530004fe72d8530004fd72d8530066f631d8530066f531d8530006f7619853004df970985300057f75585300f57c7558530005bf74585300edbc7458530005ef7258530005ec7258530075fb70585300f57e75185300057d75185300edbe7418530005bd7418530026f66118530006f56118530024dc764c5300075f754c53035f5c754c53035edf654c53035edd654c530356df644c530356dd644c5303575f544c5303575d544c530006dc624c53000ddf714c53000fd7714c530007d7614c530026de614c530026dc614c530007d4614c530007db704c530005dc704c530007d8704c53000edf604c53000fdb604c530004fe76c8530004fd76c8530004fc76c85300f57e75c85300057d75c8530006f761c8530026f461c8530004fe7688530004fd7688530024fc76885300f57e75885300057d75885300edbe7488530005bd748853000dde7388530005dd7388530006ef6288530006ec6288530004ff7648530004fe7648530004fc7648530004fe7608530004fd7608530024fc760853000dde7308530005dd7308530006ef6208530006ec6208530006f76108530
  | 19 => 0x96303a67d73596303a67c73596303a67f43596303a67e43596303a67d43596303a67c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067d42596300067c42596303a67f32596303a67e32596303a67d32596303a67c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067d41596300067c41596303a67f31596303a67e31596303a67d31596303a67c31596301067f70596303a67e70596303a67d70596303a67c70596300067f40596300067e40596300067d40596300067c40596303a67f30596303a67e30596303a67d30596303a67c30596301057e75d8a300057d75d8a300067e65d8a300067d65d8a300fdbe74d8a30005bd74d8a3008dfa70d8a300067e6598a300067d6598a30006ef6298a30004ff7598a3001cfe7598a30004fd7598a3001cfc7598a30004ff7498a30014fe7498a30004fd7498a30014fc7498a300067f5498a300067d5498a30006ef4298a30006ec4298a300deee3298a300deed3298a30024fe7198a30004fd7198a300067e6558a300067d6558a30004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a300067f5458a300067d5458a300b6de4358a30006dd4358a30006ef4258a30006ec4258a300b6ee3258a300b6ed3258a300b6dc3258a30004ff7158a30024fc7158a301057e7518a300057d7518a300067e6518a300067d6518a30006ed6218a300cdfa7018a3039ddf758ca3039ddd758ca303975e658ca300075d658ca3038ddf748ca3038ddd748ca303875f548ca303875d548ca3000dde728ca3000fce728ca30007ce628ca30006dd628ca30007cd628ca3020dde718ca30007da708ca30005dd708ca30007d9708ca3000ede608ca3000fda608ca301057e75d86300057d75d86300067e65d86300067d65d863002dfa70d86300067e65986300067d6598630006f761986300067e65586300067d6558630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc74586300067f54586300067d545863004ede5358630006dd535863004ede4358630006dd4358630004ff7258630004fc7258630006de325863004edc325863004ef6315863004ef5315863020edc315863004edf30586301057e75186300057d75186300067e65186300067d65186300fdbe7418630005bd7418630005ee7218630005ed7218630026f66118630006f56118630065fa701863020ddf758c63037ddd758c6303775e658c6300075d658c63020ddf748c63036ddd748c6303675f548c6303675d548c630005de728c63000dde718c63000fd6718c63020fd6618c63020edd618c630007d
  | 20 => 0x6f830d8121006fb60981210057f755812113d7c7558121005bf7458121135bc7458121005df735812112ddc735812113d7e75181210057d7518121006f96018121004ff751812101cfe75181210067e751812101c7e7518121004fd75181210067d75181210047d751812101cfc7518121004ff7418121014fe7418121004fd7418121014fc74181210067f54181210067d541812100cfe7318121004fd731812100cfc7318121006f721181211ceee21181211ceec2118121006fb3018121006f83018121004ff7558c210067f7558c210047f7558c2101cfe7558c21004fd7558c2101cfc7558c210067c7558c2101c7c7558c21004ff7458c21014fe7458c21004fd7458c21014fc7458c210067f5458c210067d5458c21026df7358c2110ede5358c21006dd5358c2110ede4358c21006dd4358c2110cfc7258c2110edc3258c21024fe7158c21024fc7158c21026de3158c21026dc3158c21004ff7058c21004fc7058c2110edf3058c2115cff768c821024fe768c82100cfd768c821024fc768c82100ede638c821006dd638c821025f6718c821005f5718c82115cff764c8210057f754c82111d7c754c821005bf744c821115bc744c82110fcc324c821025f77648421006f77648421004f776484213b77754484213b7755448421025f77248421027e772484213bef66248421027e662484213b7e642484213b7e54248421007e63248421007e53248421005f47048421004ff759802101cfe7598021004fd759802101cfc7598021004ff7498021014fe7498021004fd7498021014fc74980210067f54980210067d549802100cfe7398021004fd739802100cfc7398021026fa7098021006fa5098021006f95098021006fa4098021006f94098021026fb1098021026f81098021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021006bf7458021004bf7458021014fe7458021004fd7458021014fc7458021006bc7458021014bc74580210067f54580210067d5458021004ff7358021006df7358021004df735802100cfe735802100cfc7358021006dc735802100cdc7358021026ef2158021026ed2158021026fb7058021006fa5058021006f95058021006fa4058021006f94058021026fb1058021026f41058021026f81058021026f010580213ad7f76596301067f765963001c7f76596300057f74596300057d74596300067f64596300067e64596300067d64596300067c64596303a75e73596300075d73596303a75e43596300075d43596303a75c32596303a75c31596303a75f30596303a77b30596303a77830596300067f74596300047f74596300067e74596300067d74596300047d74596300067c74596303a67f73596303a67e735
  | 21 => 0xc764ca210057f754ca211557c754ca211967e654ca210067d654ca21005bf744ca2114dbc744ca2118ebe644ca21006bd644ca2100ede634ca21006dd634ca21147cc324ca21005f7714ca21025f4714ca21025f576c8621006f576c86213d77675c86210077575c86210277665c86210277565c8621027b664c8621027b564c86213df7754c86213df7554c8621027d663c8621027d563c8621027e672c86213d7e652c86213d7e552c8621004ff759822101cfe7598221004fd759822101cfc7598221004ff7498221014fe7498221004fd7498221014fc74982210067f54982210067d549822100cfe7398221004fd739822100cfc7398221006f72198221026f42198221026fa7098221026fb1098221026f81098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221004fd7458221014fc74582210067f54582210067d5458221004ff735822100cfe735822100cfc7358221026ef2158221026ed2158221026fb7058221026fb1058221026f8105822100cfe76d8d2112ede63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d21024fd72d8d2112edf32d8d2112cfd71d8d2112edf31d8d21004fe70d8d21004fd70d8d2112edc30d8d210057f7558d2113d7c7558d21005bf7458d21135bc7458d2112edc6358d21005fb7058d21005f87058d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21004fd7458d21014fc7458d21006bc7458d21014bc7458d210067f5458d210067d5458d2112cff7358d21006df7358d2112ede4358d21006dd4358d21144ff7258d21006ef7258d2112edc3258d2115cff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d21004fc7058d21006f87058d21004f87058d21144fe768c92100ede638c921006dd638c921024fc764c9210057f754c92113d7c754c921005bf744c921135bc744c921006df634c92100edc634c921005f7714c921025f4714c92100cff764c52112cfd764c52100cfc764c5210057f754c52113d7c754c521006df634c52100edc634c521005ef724c521005ec724c521027e4214c52113d7e75c85210057d75c8521025ee72c8521026ef62c85213cf7675c85210077575c85213c77754c85213c77554c8521025f672c8521026f762c8521027e762c8521004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d812100cfe73d8121004fd73d812100cfc73d8121006fb30d8121
  | 22 => 0x96210267d41596210267c41596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067d40596210067c40596210067f30596210067c30596210267f10596210267e10596210267d10596210267c1059621006bf7559221006be75592210063e7559221006bd75592210063d7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf5359221006be5359221006bd5359221006bc535922114ebf725922114ebe7259221006bd725922114ebc7259221006bf5259221006be5259221006bd5259221006bc5259221006bf3259221006bc3259221026bf7159221026be7159221026bd7159221026bc7159221026bf5159221026be5159221026bd5159221026bc5159221026bf3159221026be3159221026bd3159221026bc3159221026bf2159221026be2159221026bd2159221026bc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006be5059221006bd5059221006bc5059221006bf3059221006bc3059221026bf1059221026be1059221026bd1059221026bc1059221004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21026df7358e21006df5358e21146de5358e21006dd5358e21146dc5358e21006df4358e21146de4358e21006dd4358e21146dc4358e21146df3258e21024fc7158e21026de3158e21026dc3158e21004ff7058e21004fc7058e21146df3058e21146dc3058e21006df7558e21006de7558e21006dd7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e210065f5458e21006de5458e21006dd5458e210065d5458e21006dc5458e21006df7258e21006dd7258e21146dc7258e21006df5258e21006de5258e21006dd5258e21006dc5258e21006df4258e21006de4258e21006dd4258e21006dc4258e21026df7158e21026de7158e21026dd7158e21026dc7158e21026df5158e21026de5158e21026dd5158e21026dc5158e21026df4158e21026de4158e21026dd4158e21026dc4158e21026df2158e21026de2158e21026dd2158e21026dc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006de5058e21006dd5058e21006dc5058e21006df4058e21006de4058e21006dd4058e21006dc4058e21026df1058e21026de1058e21026dd1058e21026dc1058e2112cfd768ca211a67e658ca210067d658ca2119ebe648ca21006bd648ca2100ede638ca21006dd638ca2100cff764ca21024f
  | 23 => 0x67d71597213e67c71597210067f41597213e67e41597210067d41597213e67c41597210067f31597213e67e31597213e67c31597211667f21597213e67e21597213e67c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067d40597210067c40597210067f30597210067c30597213e67f10597213e67c10597211657e75d8f210057d75d8f210067e65d8f210067d65d8f2115ede63d8f21004ff75d8f2101cfe75d8f210067e75d8f2101c7e75d8f21004fd75d8f210067d75d8f210047d75d8f2101cfc75d8f21004ff74d8f21014fe74d8f21004fd74d8f21014fc74d8f210067f54d8f210067d54d8f2115cfd73d8f21006ee72d8f21006f571d8f21004fe70d8f21004fd70d8f2100cff7658f210067e6558f210067d6558f2115edc6358f21004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21014fe7458f21004fd7458f21014fc7458f210067f5458f210067d5458f21006df7358f2115ede4358f21006dd4358f21024fc7258f2115edc3258f2115edf3158f21004ff7058f21004fc7058f2115edc3058f21024fd768cb211a67e658cb210067d658cb2100ede638cb21006dd638cb21025f6718cb21005f5718cb2110cff764cb210057f754cb211657c754cb211967e654cb210067d654cb21005bf744cb21125bc744cb2100cff764c72100cfc764c7210057f754c7211657c754c7211767e654c7210067d654c72100ede634c721006dd634c721005ef724c721005ec724c7211657e75d83210057d75d83210067e65d83210067d65d8321125be74d8321005bd74d832115dde73d8321005dd73d83210067e65983210067d6598321006fb6098321004ff759832101cfe7598321004fd759832101cfc7598321004ff7498321014fe7498321004fd7498321014fc74983210067f54983210067d549832100cfe7398321004fd739832100cfc73983211d6ee21983211d6ec21983210067e65583210067d6558321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321004fd7458321014fc74583210067f54583210067d5458321004ff735832100cfe735832100cfc73583211657e75183210057d75183210067e65183210067d6518321006f960183210067f74596210047f74596210067e74596210067d74596210047d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596211567f72596211567e72596210067d72596211567c72596210067f42596210067e42596210067d42596210067c42596210067f32596210067c32596210267f71596210267e71596210267d71596210267c71596210267f41596210267e415
  | 24 => 0xc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d8931024fd73d8931146de43d8931006dd43d8931006ef42d8931006ec42d8931146ee32d8931146ed32d8931146dc32d8931004fe70d8931004fd70d89311757e75989310057d75989310067f65989310067c6598931006ef629893112df571989310057f75589311757c75589310067f65589310067c6558931005bf745893116dbc745893115df77158931005fb7058931005f870589310067f65189310067c6518931006ed6218931004ff751893101cfe7518931004fd751893101cfc7518931004ff7418931014fe7418931004fd7418931014fc74189310067f54189310067d5418931024fd7318931006ef4218931006ec421893110eee321893110eed3218931004fe7018931004fd7018931024de768c931405df758c931405dd758c9310075f658c9313ff5c658c9313f5df748c9313f5dd748c9313ef5f548c9313ef5d548c93100dde728c93100fce728c931006df628c931007cf628c931007cc628c931025de718c931007d6718c931007d5718c931025dc718c93100edf618c93100fd7618c931005dd708c9310067f65d81310067c65d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d8131024fd73d8131004fe72d8131004fd72d8131006fb40d8131006f840d8131076fa30d81311757e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311757c75581310067f65581310067c6558131005bf745813116dbc7458131005ef7258131005ec72581310067f65181310067c6518131006f96018131004ff751813101cfe7518131004fd751813101cfc7518131004ff7418131014fe7418131004fd7418131014fc74181310067f54181310067d5418131024fd731813102ede5318131006dd531813102ede4318131006dd4318131004fe7218131004fd7218131006de321813102edc3218131206de3118131206dc3118131006fb4018131006f8401813102edf301813102ef930181311657f76597211667f765972101c7f76597210057f74597210057d74597210067f64597210067e64597210067d64597210067c64597210067e63597210067c63597213e76e21597213e76c21597210067f74597210047f74597210067e74597210067d74597210047d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067d43597210067c43597211667f72597213e67e72597211667d72597211667c72597210067f42597210067e42597210067d42597210067c42597210067f32597210067c32597211667f71597213e67e7159721
  | 25 => 0x813208edc3218132024fe7118132004fd711813208ef93018132004ff7598a3101cfe7598a310067e7598a3101c7e7598a31004fd7598a310067d7598a310047d7598a3101cfc7598a31004ff7498a31014fe7498a31004fd7498a31014fc7498a310067f5498a310067d5498a31026ee7298a3115eee3298a3115eed3298a31024fe7198a31026df3198a31026dd3198a31026ee2198a31026ec2198a31004fe7098a31004fd7098a3115edc3098a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a310067f5458a310067d5458a31026ef7258a3112eee3258a3112eed3258a31024fc7158a31026ee2158a31026ec2158a31004ff7058a31004fc7058a31004ff759823101cfe7598231004fd759823101cfc7598231004ff7498231014fe7498231004fd7498231014fc74982310067f54982310067d5498231004fe7298231004fd7298231024fe7198231026fa7098231066f93098231026fb1098231026f81098231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff7458231006bf7458231004bf7458231014fe7458231004fd7458231014fc7458231006bc7458231014bc74582310067f54582310067d5458231004ff7258231004fc7258231024fc7158231026df3158231026dd3158231026fb705823104efa305823104edc3058231026fb1058231026f8105823141d7e76d95311767e76d953101c7e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d953140f5f73d95314175c73d95314175e43d95310075d43d95314175c32d95314177731d953140f5e31d953140f5c31d95314177431d95314175f30d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d953140e7f73d95314167e73d95314167d73d95314167c73d95314167f43d95314167e43d95314167d43d95314167c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d95314167f32d95314167e32d95314167d32d95314167c32d95314167f71d953140e7e71d95314167d71d953140e7c71d95310067f41d953140e7e41d95310067d41d953140e7c41d95314167f31d953140e7e31d95314167d31d953140e7c31d953140e7e21d953140e7c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95314167f30d95314167e30d95314167d30d95314167c30d953140e7f10d953140e7c10d95310067f65d89310067c65d8931004ff75d893101cfe75d8931004fd75d893101cf
  | 26 => 0x6bd65d9132006bc65d91320073c65d91320063c65d91320079f73d913243f9c73d913243faf32d913243f9c32d913243fac32d9132006bf75d91320063f75d9132006be75d9132006bd75d9132006bc75d91320063c75d913243ebf73d913243ebe73d913243ebd73d913243ebc73d913243ebf53d913243ebe53d913243ebd53d913243ebc53d913243ebf72d913218ebe72d913243ebd72d913243ebc72d9132006bf52d9132006be52d9132006bd52d9132006bc52d913243ebf32d913243ebe32d913243ebd32d913243ebc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d913243ebf31d913243ebe31d913243ebd31d913243ebc31d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d913243ebf30d913243ebe30d913243ebd30d913243ebc30d91320075f658c9324375c658c93242ddf748c93242ddd748c9320079f648c9324279c648c9324275f548c9324275d548c93200dde728c93200fce728c93200edf628c93200fcf628c9320067f65d85320067c65d8532006bf64d8532006bc64d8532004ff75d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d85320067f54d85320067d54d853215ede43d8532006dd43d8532006de32d853215edc32d853215ef631d8532004fe70d8532004fd70d85321957e75985320057d75985320067f65985320067c659853218dbe7498532005bd7498532006bf6498532006bc6498532006f761985320057f75585321957c75585320067f65585320067c6558532005bf745853218dbc7458532006bf6458532006bc6458532005fb7058532005f870585320067f65185320067c6518532006bf6418532006bc6418532026f66118532006f561185320067f65d81320067c65d8132006bf64d8132006bc64d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d8132024fe71d8132004fd71d81320defa30d81321957e75981320057d75981320067f65981320067c659813218dbe7498132005bd7498132006bf6498132006bc6498132006fb60981320057f75581321957c75581320067f65581320067c6558132005bf745813218dbc7458132006bf6458132006bc6458132005f77158132005f471581320067f65181320067c6518132006bf6418132006bc6418132006f96018132004ff751813201cfe7518132004fd751813201cfc7518132004ff7418132014fe7418132004fd7418132014fc74181320067f54181320067d541813208ede4318132006dd4318132006de321
  | 27 => 0x2000001800c00400c0018000000003000000002401200800040000020000004000010008004001c0030000000000008003800001400300000e400e0020008020006004007000000200c006000800e003000007002200300100000100070008010000001003003c000000005002800000500380180060000000000002005000001400c00200180000320100000004018001000001800400e0000004000000002800000000201b0034008002000001c00e0041a57e75d86320057d75d86321a57e75986320057d759863219dbe7498632005bd7498632006f76198632004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632014fe7458632004fd7458632014fc74586320067f54586320067d545863212ef63158632004ff7058632004fc7058632026f66118632006f56118632006fb6098232004ff759823201cfe7598232004fd759823201cfc7598232004ff7498232014fe7498232004fd7498232014fc74982320067f54982320067d5498232024fe7198232004fd71982320cef930982320057f75582321a57c7558232005bf745823219dbc7458232004ff75582320067f75582320047f755823201cfe7558232004fd755823201cfc75582320067c755823201c7c7558232004ff7458232006bf7458232004bf7458232014fe7458232004fd7458232014fc7458232006bc7458232014bc74582320067f54582320067d5458232004ff7158232024fc71582320b6df31582320b6fa30582320b6dc30582321a57e75182320057d7518232006f960182324557e76d95321967e76d953201c7e76d95320057f74d95320057d74d95320067f64d95320067e64d95320067d64d95320067c64d95320073c64d95320063c64d953244f5e43d95320075d43d953244f6f32d953244f5c32d953244f6c32d95320067f74d95320047f74d95320067e74d95320067d74d95320047d74d95320067c74d953244e7f73d953244e7e73d953244e7d73d953244e7c73d953244e7f43d953244e7e43d953244e7d43d953244e7c43d953244e7f72d95321967e72d953244e7d72d953244e7c72d95320067f42d95320067e42d95320067d42d95320067c42d953244e7f32d953244e7e32d953244e7d32d953244e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d953244e7f31d953244e7e31d953244e7d31d953244e7c31d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d953244e7f30d953244e7e30d953244e7d30d953244e7c30d9532445be76d913218ebe76d9132014be76d91320073f75d91320073c75d9132006bf65d91320073f65d91320063f65d9132006be65d9132
  | 28 => 0x20008008001002801c000015002003400e002000002400401e00c80040000000020000010001001800001e000000002401a001000005c01e0110010054006005000000001e01d00280a8000002002801800000100400040040070008000000012002800c000003001000001e00b001001000200001180100000040028004000000009800c0080020000034000000054000400e0020020010000004000807001600900100840000000010024004000004802c00600100e801000c0000000070006001000000400000a0030004000000001000000000000180140000120000094036007000800800000600180000040000030040002001008000400200000100000080000098018018003000000800c00701c8000000000003800c00002b000001c0080000000024000000006000000800000200040000040008000004002013815400200b001000405400300080000000000008000034002002801800600100100040100040008004000017000003c01e000001001000200f0000024004000016001001c03a002801000000700000040700040080010000005002003c006001018000c000000004001000e000001800401c02d000802001e000000800c000009000000000e0000020004008004000800400a000000000000a0000050004002003000800000c0050008004016000000002800602d002800000000b001800c0060030000008000000002802400a00f0008000008008000800c026000006003402c006000800000000700480140000020018054002000000000c01a000001802400000000080040040000058040028000001000000a000002002400c0010020000016001000003000c0020000004020009001807c0000010088000000002002000001c005003800000200300100080020000018008000002000001800000000700080140000000000002002000005800a006009800001000200d801400a00000b801801000000000700200030018000016001000003c00600c001800400c018009800400000600100000000070028010008006001000c00600200500040120080000000006018000003800200800080140000010038014006001003801800a02000300440000000000000024014000000400800100a807c004007004000000200001e8008000001006800c00400a002802400c004004001c0000000000000000002000802400000300300180120220008048000000004800c00000200b0000008008000000400c002010800000c0080068004000004002802000c0040018000010004002800400000000280000040080030014000001001000001c00000600080060090018000008011007006800000100b003400800b0038004000000001803c0040040030010044007001800000000300000280480010000008000004005800c0
  | 29 => 0x3c00000200a80340010060004010000000800001800100300000120060000000000004001002800c00300000000100140000010000002001800c004003000001400a006003006401400001780b8016000000800c01e000000000000600300180080080290008014004000002801c000018000000c016004009001401c000000802800a00100b80040040030000034010000001000000200100000100200010000020000012004801800200c007000000000500100000a2003000800c0140010010000008016002002000000200600e8004002000801001a0000058000024005001800400000a0010014008002000001c030000002000800000200b801c00a0430030010000007000003000800200000140020050008008000000010000800000b00180000040060038008002000000000001800b000800000200a004002404e000008800c00000b0008000000001006005c012000007003400000000000080040010018014000009000000403800100280040040010020010004003001000800200a002800c09800100000240000000098004034002001000000c003006004400201700300040000010010000004007000001c004019008005c004000000000800200600000a0020035001800400200000100140000010000000004005003801c00000000780b0004000001800000800400480000020000000000002006002002000400a0038000010001006800002800d0030020000000001802400002300000ac008017008001400c013001003c00c00f003800000000c0000000016001000001c0060030020000000000000000800000200b003000800100100000000010168000004004000003800800a000001400202d003800800a00000080080000020128014004006001000800000100080040080180000144000000001000c00a000001000001c001002000400200000680080000060050070000011009000400200900500240020000028004004001001001c000001000000c0000030000010012000009000c002002000000000600400080b8000000021800401a000006000400e0050020048004006000803000a00000280a0004013001800401802d0010008066001005000401a0000008020016000000000001400300080000700030000004000003003800800a001001803002201c00100040020000028000008000000001c04c000000800c00000700000100060010000004002016000001402600301580100060070018008000000000800c00200b00080040020030048004000001000001400600201880000000070010024000002002801001c0000018000000001002801c0160000000000002006000000800e0010028088008000005001c0060040010008000008006800c004002007800400000b004800400000400880000040000
  | 30 => 0xb2905d4000000081838c400017f055724f443b000061c39010010000577000062000009740fa00a118784e90ca40000ad00001aac0002ed4a4d09150ae000000000011d507a522f481802d45040001db097948040f44224bf300010c423f878400280002ca8e6c1f4800047141400d8049f3e7406036c01df1c701bc394c6c7491c6d928511253d6cb9f05f8e3435f0cb70b650ac261c518004d1b4376c57d00008e925442ee024c000102527e462119709d02c317e00be211491e168c708425499d37ec4bd0a7800000e87cf07ed1f30c74d9f000115104f45f33f4ca243d3c3b014001c32744e7a1f20665000078d12e8e270000165258000039c4e1600009da14fc1a9000116635540000000faa2cb0f2219510c1066070f25340002cd433b1db91a0184d1283b9c7b522547e403511220080f0032104a60614000382400042c418e38bc7d117580002428d8e1bc4dd3292501842143030df479243602b11d98b17428825d19f0ba7458458318b8bf12d0c2dd00007ae17c8b9214205c902ac9ae2cbc9a20ee4e3241d03c82b810e20a9923b125c1ff000052a000013e15500001b9cc063f992833ec000003ec00038b0542065c64e0000bd001144791ae8cfa13409de0000a68324054822c4caf33c4c5f1c64c68000028112c800000007d919a8e50147c17c04900ba0000000021845000000003875168109510c3b585e42abc7b900007440000dca2a8400004406703e30000193453038b427310389190000000000022f20e4000000000028707b10c680ed05108c34710bf012f800018ec0000000000294c00038ac000252cab7156c000000000000001d43bd8cef04390561cc80000000f4d000070143a4dc61cc4e511becc263204df12088000364c00000006b3000000039d400000011a940d0a370cad0f80b584f507e00001320d2122500000094032010001001000600a006001c00000d001803c0000000000010000001002006c022001000800001a02d0020064006002000003c000005001804c00a001006001c00a002000000400000800100000000020000010006000002000000a00e0000074010001004000000e002000001c000000000000c000002000004c004000005804800c0010028030010000000000800e005001800801c000000004400400600000240000000038010004002001802800000100300c00000000050008002004000000c06e001000000c0260120000004046001001001000000000580000180000058060004003000000000e000000800400000500080040040020000000000000000801402a002000800000400000080000040390000004016010001000400800200b000800000900000180060020038024022000018805000000d000002c032003000001001c00a000000400000200100080000000048000
  | 31 => 0xe354800033ec1c9000043700000002b84398000126e48b123f3144fdb403c69222f000000005a4000044b000051200010f20d1c00021c451328fc475366c00000001ba00000000000abc43dcb8e000000000010942d38d3c41500000000000000000031787b40cf447f000070c4978fab47a886022bc0000000000338c16a28c45d900011d909d40001a68ffb363c0e120143ba3eccaca09b42e20000cf0012c9c821a888a46f0c430c880000000be71c8c5cc0c18000125006a07147da418c935081c07100000001b7c15532f06a53254e7e31fc6ad258c4d30fa8d2012c4c300000b1c000059537100001bf4c0447882610000f051128538271071646fc0002879272331cea200000000000f6d4084ca3144410432a04fa000014a25d80000a40f903dc8d1a3e991cb21486c13a54a7f22fc93f303c5a71cec7ad023d26b49350a428ec4a024a0d8b37300003008ea53f7800300007060000a36331000041f838f138d025457c49c1a188f4408c000000000023b8076297c000000079e1e4c000412000000010f31a000004a18d3900d40000000000468cb5a248c2220470000000019c08e07130000ff8000112d1c2845117c426b3b452510cb4c2b2e34eb324b8b040000000000062f1d700cc07580000cbd0a02524af6108821100000003334c0b05c0b2425040000000000100ceda028847e084c7ba280c0a92e0c0001c6800000000001bb80003d30e5d1b54a21110c1310d0cf5f41f081f0000ebc01e839f2b6878500000f827bcc2f1d00eb02e28b6302d883e44d800042d40233bf48b416e87c21d58f1d39c00f1413cf6f1ccd10517d49371184b491138a2f1f5840d0d788904474b0d32b0a7830e4a222c54a2e000120014288d13d148e721d45350000a452074ab53a28ad802d4645062c07b054447b33780000f9c27131b87a414ec4e74a08ad93cb0c0900000641f04be92374cdb3c04f0b01e1011025d1aa2a9c3100f610af0000f44375c000046000030851c60000e0501dc04700000000b4908a00000002600000000000035c000000000001be800000003fb1e311de07cd0473c24a3d2844e67218d02c0000909419528419443e3000014722440ac00001b000000000000c823fcca7c00006fc122445a00005db1a1c25723b106c421cd6b000064600002e63ba0000000122836489d62200d75208cd53162c3c22d3c0e51aa50f9106cd77005ca661334cf64938e3a4234545082cb623538798012854e00009403e605ca0054a541e989aa0e70dbd432c42b3b34dad26047f1229cd5b3938c530ab0361138422d2794d4149c09a42f28a301740fa0055c12228107351bdc74f01442542354fa13e88b961bb074d2bdc77d45b8f3820e043548f90122e84db501a105b2994a7035ec4151090d470420a81346000043904122bc0d0c401
  | 32 => 0x50c3c365082a1f78000480c7512f2cf672d10ee90000d4410d800000000000000000189cdec0000e990e9c694306042e11905653eb4000332c0000e108010000000000064c0000cd90000b8734046d40f5c00037e80000e5c8553e110990000080000000042a00000000fa42398000411074e17d119a000000007a0a5e22d4c4006b4000000031f04b4a5025d4000000066c0000000000000041c800000012041da44d5000121e214c1a3000000001500001cb8000000038722e4000499c4c63aa000022ac8d4496478a0bd800000006fe437c00042450de00000000000000063cb3235900a736c47e009248eb20f04ff185041f39d0b9d000035700000003394f8f37fc000060437f0c98a2c179ce2822a8f8b48341db450cfc709090080000134199052f170cd7f0000000477c99e2a141e113cd256000069630740ce1fc800023fceba228528811acaee00000001cb40003ac879503344ef16040003d389340000000361062347940001720000434073c3e7cbd2308067b2880d2b48e8fea37345222c2c81b061cffe305c00043acbb220b868a0000d5f00000001258a69318406b000104e109c0000b8c8e3356528706452420d5903f349096a3c950e824c000000006a836240f31c98d8041142081780c5445f071b15c47f90000e3c03c80002ba47b3089c57806a006248e484320f457400000002e043a021b89e20254a192824ebe0000786165c0001a2c00026dc31800000c70000000000071200000000f288400000771200c1af0000df30000e6800001bd45dcc4a452800f3cd0a91417481c00750153c64d5d2730a8f0000f5839a924a174cdf913c8b6a2c94896000000043700000948eef00002aa3e34de933d40000000b3733210902a7829a1fb432118a400000000003444e4700005410000205100004215ac2d30b091ab0000857000000035e00000bbd16904a400026706a107643a337080002838f3007d404f2bf0992086888f087d0570000a4042a400026b4000028c89a0be83323a388b309c0c8343802fc0ffc00037ac00046310ad1910a250000b21000000000006b10000fc800000000c2ca6e124c000000000900003ac05388d700000002f4c0000450e4900000003bc8f283adcb4a19e09f24814bd612bcb3c000000012e000027e800007f819026cc00025fc00000000000000d35000039400003de0000c290000e1c0000fb100000003e5825f2684ab9104c11300005903c3c0004a140000000000000000000000001ac000003402ea00011dd3c48000000002b02740002ebca15462c17138ecbf4000000011f4bfa000020f00000000000ce423146950000f17229046f0635163000000007a8000473c7dd311c6ed0000be33d980004168739000093b2a2517127a46530000cb204d805827a918926651d10000f3a42f8df
  | 33 => 0x1d0000000440c00016b87b6234c00000000002b1800000004800000a7b13700000000e0a1c241e73b38a2b3a30000227c0001f8d224029400046c846c000057a2f9125c2bc8000000000000004d248989ce0c90bec154014f0f844c226691f71864e293aa800034fc000000108f0c9c0001ff4a6025c443817b0b393e38d723eb07813758ccc47d496b00006a6000060125940002f0cc6a257c000000007c000000012280002718089350cee40001162000116c04b8000000000000000003e6c00049540000000bd412d459d00004e8405c74637408e144810ec40088a016ac47816140000000fb90edc4331d142fe1dc00003634d7d43e857000011010e00f3c0000000470117216500c8298cd370e44cda00000001cdcb7547f44674518b1406b00001c9000045740000000000000103500000003c0cf773b485eb44a4ff724f000033149fc0b002eb000000000004e0498045f16691d614f073d2080dd1083800019f51a6339c000000080d080092505d8000126c000000000000010db3dcc0003a1c00009b82fb3355142132843c090055f27e4a8a2e2d26536a8ced3448019250883b000106e000095800012712f6052d35e50a501709b441fcfca3594f9e48486e11aec2462df0de0073c543134402530d403e35e921c431497d15a842109fc000253800000000000000e6d206866b1680fcb00002bd06fc5190000000000004d000000026d4000000000032b80001dc8883000100915540003c8c4521b8c2da0c2412b00008c133e087d243000032e902d0000b360770f350ea8aa82a185b6324495d16100002f680002140ef318e0e3d000000000010222bfcb22276c0000fb809810e8ed40000b7a03ac0001364000162057200007e10000a1349e0f620000609324cdd900005e800000000000f7f01d079c000102b00000001dfc000085cbac0000000068000010100003bf800025b4db40408ff50000000466cf850000000000000000000001b3ca5c000030e000000036f822941cc91823a0d4044acc0a29e489315f88c823dc1d50000c3e43081250d70a711ca8944342cab62784ce640cc3ae0000e0e48407591a607d032d8ddd445c0004478d9d40f400031c038b0000dbb1bacd3d3820f0219200ca14d00002a60000156067409f80000000ae607c4622145841e20b09c51d50ffc0db4000334cf1600000001ab0d9a0ae800029691f83ad0e3500000002a5800049f00f9000000000000003ab848d369c68538f8b083a009830b54ff11c74505444cf603cb50771f5cb5e288cf390d6c61f2b7c000156451d0000fd400001f7102c758203c3eb00000ee0c3c24312b8000074406f32cc0d10c1c60b2568c2345380002958a1b19dc99813d80000e68adb1178b733798018379c42f291c848000093a49480223b280004974d2c40411c71c
  | 34 => 0x9a87210a6003c42fccfe000025316a92193ef437009ec10c464100d1d042bb0b10eed10d0cfd0b2c3f20dc82b70e90afd32e0000000091b0f00be639880000d30514475c1532c7d10b46087f505dc95c18e85e30b84de80000000000008e0000289333ccff1e2d1c30f347d80ff0206111847a00001282ee8000045c00030704a7000000000000000c783851574b8c40a8ae4431838631307f30f7056208980da02d0d4d27ac1ca2b1c0003b74c2d2278bc912185d51954ba80000a0200006b70000a4a20ac59142ec0001f0060a0000304325ca3e25500001714f431ea051a10504f411b4000000121601690981e08a8b44cc61026410ed31d8fd84068000000000023cca4e0000d2d38540001700da413c112c000065f00006bd0eec06100007e70000adc48b410100000000000ca01b1800031a40940000efb346c5271818ba3064868c49d116b2138b7f157840a48ac0003030b1639b800016cc4b0000000000000001ae08040a5cc1e2e806aa4510d1f42ccca916341c20de877a251807e40c4e4200011543e4443e2a94d15433400000002ca2f000000000189000000000000000000f3721ec00041240001684710438400016582801098000000040f0f652451c7c00045f430539940000af800000000cb1e58362133047420fce4d14c90ab0000269154423f2c3022b417d1f1049914c1ad40001bc88ba0c6d066237884f29887202490000239043d0df00020000def0000000117000000000004798c8a07f000000002f3000081e3864da3467c5de49ec3b31ba0f890fcd08400000003b1cd45000000021ac6c300008c22c48e170000cd4171ce9d1c100f005e4cb41d544620020e26259c5b140a4e0b0000b413a180001894fb60000e5614e400049cca292eb484c44c4a1634c4d49000098531546b20bf476f0be40002fe0000000019b00010bc337c000000023b00011ac15a116a196c32e2a080004018fee0000bea00000003c605d400006d00000f2e43283c933e42122f791ee0000d3031c4b9100009362e1090145d01c10cd81643fb401b1ffc9fb2ac4b6511950b22d9c19501b40000000ed048d49ee334451e2194c6200011ed22940000ab876a0cd0baa4860000271cc7b0960bc202b8eb60584c9430e059f1424000163887400006993948ef41eecc7a1cbc3f70bfc9a91678268100802f0fe45fd0e880fd318c00024b40003cf40000000abf492462c00006c9000000027d00003b5c1b501a4edf00010a6120c0003c7869c0910d811f6c00036700b92b580000000000248015840b854c27f431c00002f531680004664ab809f0dbf2598f3b122c827384c8820a6c41812e47c535310ea2488e574920c2a29d116426346a221bcb1a00000003214000000000023e02b80000861200004913740001f940003a7c1480000c05236d2
  | 35 => 0x8293d70382059d04d05650b83e18000041cd25498c2e72f34a523d78e7600002653918a100000d511230ca20000a330000000000000044a8524000061b00010b7000000000002d42ddc50d1e44000000050440380003df51f643d86153be908004641b40f7cac20c8c1f6481c000316c9e60414b4513c50d44410a4805581a132707f6241c0000000a9c410450c422c00021e4000326436c414000008f409f00049e00000000000000000000000000000000000000000000000c3320388470000f072fed15607d00001ff83d537a800020c800008d8e43000000000000000a880000a1c0d925e00af2288a5d3ca80003d2452e3f3ce1e19b455c3cf923d00011121808bd13a8ce4837b50193a590593c383a131c8c1045cc3a61e5c24d3afc0004230f6b3dd8f141ad0fd100000000000b8f01300002e651a4219c0002ac0e8d18dc0000000a7509e03e03b04aea487c9320000e7c000076d10a0000000002400000c52964aae3b84d99000087a00401003064e9a08e8a5519588663b000000000b6c0790c9e04487bc28350713eb8af917e87cd000000041300001c440003d58c49000000033a80000000d6e40c8fb4212ca42395400013580360000bc80000ff62c000000000f6a000026a0694df43d9113924490d528d1179216cdd23b0ccbb44f4da022f86f319a42c830581ed1d6cdaf21dc295494c000265886800011ff03a0b7035b09c1483106f43309591768f04110854746048b20fc0ede1f8916d22b87aa0d3c2f7067c6e9412cf482ead1601d1c000388c000180c000078823515fc02713b8b1e09c847100b87bd250c0000000e9e2ce02de2cd00000f1c00039e4000148082d00004582b505bb0578315026480b00010c01e7c00011b831147f073422040003dec0003434000077800006eccf72ec06260000f1f29b40003e1c8f94790a7345fc37319281ae00000002dbc10b20940b7115cfe43aec00046b42a814540000000c8b0bc800700003282624e7247286c00d385790b3821d47e80001dd87c325e8af800004b6485000000000000a28f460000b781368000000000013f000032d4b3a4324000019c0002d54d7e079800031bc000040ca282f9469d061800045542e4000000017b860f2c1c0342cad165000022e00005440ed07870000ce031dcacf4768209360c00000c109b2a400000000000166000005b056f1ff113526e460c392c0000d9c4bc441d279000082639640002d9005502ec98a278cbbf21580002a5cd9e3a049571130145000000039dcabd05cc3e900007c731b1170021c85e2498b28497c00049d51bb000034d2a50000000000036205b80000a773ccce6b383000000000000048000473480930d0faf0000e3f1b80266000092a00003d349f4d50000033e065891c0000e663a4cce8143ce69000113e10582ab2
  | 36 => 0x12b473a2af83834a2514d01780000428364435cd103d1c3ce287502f48c8be025911a13ee11852ff86340af0fc521ccbd91120dc80000904000000029d80000fe00000000aad003126a0e2801e0bd046027545f7000000045d80003a512681b210131d7cb26361d070216441728a8000010c3d400008312a8cc8002fc0380e749c20000fa70000f50000000045711263e5115718f52330e58f4008dca672e5d1db123c14b02c474933747ea135cb7133b0b7d033c6dc43f87ee0ff91980d6486d170814d23c036315d46d60ccc22a18b4cd02b5ca7a3104c3a1924135101836b2bbc6003bc47dc245c3d003e91b106880dc3d945021940be22ad00e34440e073c4099406a82dc144024e03a51e82c60e140d74acd2724fda27cc501277c0002450876022892b1d84f61000028600003ed066494f15807ef489400000008ac000065900b000025548871af070318d4cd70bb41b93bac0002b1400015ccc7533083c62774bcf2388ad124cc2a02ff0202425836e4364e0d3584d570b35118344cdfc1dec9a349e835021681062bcc0c9400086440d8000393c000314049d30dc00017a400000005be48a40000000d86265400014ac842000000000011f2095800000004c02ab000019d40000000000000010d0270b5844b8e102eecf5a1b883bd358080c0fd4000133d1f41a0c85106e000000002e500000000000fc1389000029609910000a4400008b00000d0e00000000000220000020a228c0000000bb4000126c000038941e0e7800000000000000000117e327c06c3bf07792d742940000c3b11a0e9848c4c12048c37e27906040c04a1840ecb300b1ccb02e50a1232fc7f43a9c000000000046ccb820890c861ad86713be0000075c0aa201c37400003cf377c000000036919cc0003bfc00042d084418a8d001c8910e1bbcbed05b8e9c171057630c4c6734643130a2c5bd030428f139489c10309bc15b0fff459d1cc3b702310c3077709e42b52cf44bb05088df00007c931e118d0ef80001600083121105800000001d20065000009a3d48bdd1648000000000033d084d3120e610c010ff27b40004468c5626991a2242d1d03e043cc410881512fc6d81c1c824253026f37707434678cc61cd802822a40002620d5c00010f53b801a43b4c0000000b4b0da034105c8841000000042380001f98a9b1fe8d0314dc000420914727f8c890000b4c3b64a0b0290fbf0390d0f0000c1500000520a8c9160000000126087e380ca0520200000c28e1120d896e2944000036075a046890607401150f48000387c9ac060ce2e0e6cfcd4268526163c168262c3da0eac2f84078a8703d44ac36e40004338401352816f10b12810a6489838946392a90afe197080203dca8c33700e240f0dfd1f546893608bb93b891b83ea47d34348e83401d22a25482cc3a2c
  | 37 => 0xe361858a8e49040003f9400020bc0000000000173c00000003e20000d02000000003a800002e01dd232c9b047840732818000000000013390aa000088516b0f1c000037b1980000000000037d8000000000000003c30000cd82a105af0000000445000020841c42440582000048100000000000e302e540000000f9c03980002c64de1266ce7b00a8c25002c6dd3ac4b091014d091d289ab0480beb3700ac0000063208f0bfd348923800003b53d641cc37540000c20ecb07ac00000009bd18f8c880000d620000b5b2fd4eec0000e4a46580002da09110000000476077e0efc292456003716290e50610f4a494114840c0662221821934bca0a38ccbd51558fec10687f041a8ad50d2101b0b14902080400024bc1090034f932a5453d0000c3f00010d316b506921189a0420c0002f30f2602a04693ad4da6023078848c042d216088e247cfc40b6087c06ac6660cc052827fca1a347921a09040000000bae047499300000391c9c28200004c10000c441494b89190c2143f881fa3020fd045d46790000f92043c4912610000153417f02cca80276412c0ec858735a0ac300010da0a7d15007b893913ac2d727c113b0000db2000000000005d1000110a0000c3607e452c05407bf1ca4c73102000025f865a04e4f42306c0000000a4b176000021b00004750000000000032680000000df2000000046f4b932f380001c54000000087027600002cfc70d40581e0283c9a7307c0002db51fe204cacc018c19e324815f0fbccc90000f78349d213222c0000000000000009600010750000000000055a1d9d2570d088b61dd02832ef00003e6461136ccabb1584af100012540000000000071e21e08b80000d980000cfc00000002a20f0832f45b20000fd5049c0000000db600000000000000000118038e4ca109b0d423df0a072e000004454a0026d87ab19f80000000dbc410000046d400025bc174485c552130c9cd4090dcb2d4c6d102b453e20502632da467f3e000d62ed8d9134a8000063000000006f808c8e381fb1186000000000010a733010880000f24309c6a044d005000010ba00011e0138894a000000000002300000fa800002c1000053333c800018c000016d00000894bf70000f831fe00000000000000080600004c939ccc2823b448e00000002d40ac415b42a4000109f370c00020444aa00000003bdc8280000eaf1ebd27600010a32639262356837141ec2500cb03ec13dc35430b8903047c1d201c80001a7839305e80e734100000000000469434b274c21011c8fc00308cca00005ef38601c03388aaa1cc000000000003fa0c5711240000f10ad000000003b20764000060517a8fb720c07ca27dc423046c228402c2e01e9c00000002041b9097b0ddcf533eece0634d0aa63e545c6329126f00005b737940003a0828e06f9097
  | 38 => 0x9473b6c7893518aab00005bc0000000371c85d46c05f020e890800008a80000567372400040e4b0537900d33520c602a0c27a05183e41884453072d2462be9003319070b00003dd3b94000401400000002b61a0429d1248ae53bc01943cc820304e091d0d000a620cd21b0018fba206424b159879941451af2a7c05700000750000000254c4c4000000027b00000d94be100008720f440001670884448c5a640740dd05880001d5c00000000002ced1ce0000e4436140000a440f634280bc0000456272c000396c90d4720000293000006207c40000d63000061729850b03884c8e3be400002103db00000001e6cd1c1f505491d40fce172d01445146913d74aa000001c705ac0000bb00001f18116000033917ec00036b866144641b200002233629064232835a2484b4603f02e814189a5388844f31f920a00c80000a308c70e4007d2fc8000177400048881ef08341ec348c0000988c4e00008d9037ced841b4bc4101c000164c15d00002a53d8c00000005692170b5600000000000d560000b7e0000000279c00039fcaa90000afb0000b7b09dc0004358ebd1ca09972c28000000000000000000d1890e0ee000000006cd08b0d3e37d44ed449000000000003a6c8fd107000025f03a545786683a110670354c9d3b14bc114e8000000024a29f8a920000ffd000000000000000fd0950000000047b000030f486940dc0260000f1a00005a900000000000082490cadd3f7c6d3420423e175d15b341c4e40000000293c7781afc000000004e3c280001dd4fb2192ca722394a7d44bcb11330cb4000000002c9c0002f1d1ba246800039784323a24000000000000006842de400000004f90000f270c8072c1e80fbe04446ce2f70de3236881005ec143000000032340003b245c1273c0002fb8f8a00006ff000000000000001a3454a36a0ce1217c0001a08000173526d1860c523658f882fa106248d0e7d48242f031746721ea4cb11cf8d760768d283778d6a46b81371a9cc66432030207205fe086c2a74408586467128c23a84400d99053037836a18ad18e1b2c88c3f64ace3bb9026462868e34c89052298a261114fb50c5051c36545a52b2c0002f6c4cb0000f203260fd200001ce2740c0d18fc0002300f743fbc66f3560e41410ce2001101c6056c0003c4400003b001a0000ae20000e9100011783f084541214d0532589ca0afce6420285403df84191c5c8bb2c080db3a80f7011d800009f48cd18c41b12e4003f23d4a010d10dcf3d2d0e3464c2210ae40000000dee02400000158c143b8c00001740001fa01e50000c002ecc45b33cd1d204cc00017e4349321cd36263000000009ba0000a0c345032a1e746f423c400010e428400004b32dd0000000065d24000000000e010f9800047bcc4500005bf0001153384842901c
  | 39 => 0xac7ac2ba11e7000047000000000ac87b2480874c0abd11618389be096527700001690ba4ca6000120e0000e6f00009130d540000dbc000000000026ec64100004c5000028813f400012d00003ba80000930264000085400008c6323cb2d1e94c4634a496840e112129189e8469d25b0a70e880c646be478ce900000da541d86ae42e4d8c187459900000002348000137c1d3000000023ec000052438832b4b1001e4000000106b345d1370d485ce1e500002f5c3371074ba4004400000002a90000d901438b4d4118bc500008340f58d383c540d2000060736a51f046447df0000e632d986570fd816d0980aa2222066314c4ca50f2d0f42e20046353cfa509785033db0889000000000009150000f6818f11eb000109304c042a0000dab00003810000fe9456800026a0dc113600c32dc80001798bf64030b9e1a6c000035c000492cda1000064f45648490000b2337e060d15f054f2c3c021128400034587cb000000031940bd0ec472b3d500001d2c927490126124a47b01dccba900000003b108cf00104664648216000000004e88fc0000b9c00000000000a640e385f600002962324eac2b9c14c48805ed304cc7d0000c073c3400000000003b540000b24738000083703fc0001c3928a05040000ce91871688e921b08c0e0000c790f1428d2d1c00048551063ae4a174884000014c0003a8434534211c200000003b98f791b280002e1494500000002db80001d08b9b00001662330dba1bc01522c6c7600000000205cb422ccd0fc00011320c5800016c075d0ff40002cb80004218000010013c3ae0c7439140481b78fe7463c6e613504fe42d8c2c43740c01e84b4839800002c3895e43c49b10920b540d7cd26022d17b43c121146f89f62b20a082cf8bb70cc401433387681208031414903e1d48db708548160eb42513d44b1d26e0ad3368805b238031222b450b37140002acc0001c94c424170132312d1b6184845926c907d2d7003b1e683952ae8c7c439800000005460ef08d80000eab0bc44a41abd14928e89f128c8e54452ccee3f580411254b52287c8ef000066734e8c9b00004883fe4f5731b420c4270b5f0000f0c25b021c295cbbd439cc01020465e01b898f3960f691fac0003c183af0234d742ec400000010bd3f8109d00011111c607000278a2700012640000a99000058c00000002c18fe3237009129042330000b571378c5833a4f210cfc5e247240003e5caec1e880000ed80001d951080000d73329cb5900000000001079000021e00002670d28000270c1e317480000000430000045d000000e04fc000000000000000002048d4b44e000016246f500000002e880000000762177000047e4ea91b5d18415ecba53f2431718d813b25cd28000000000000dd8453c0002584000000000000000004434caa000101c1a9000
  | 40 => 0xdac493caeb375124c37383f1000099f2c809d7000039e1cfcb862128d973e8cead06dc0000600c4d33580001f304470000000000027600000000000bdf37dc00012400000000d710000000000052900003c1000087f00000330000ac100000002e68000424800000005b500010c30058b6b270101f0280000113505529b0d1d24e0f75224800037885640000b01000000000003922ac85e131ac3750f94ceb47ed1000ab47050954f82191d152359c25b45bc000000051700001d81a5cb763a984550b3c00018a005f12652661e0c00049111c1177c0002e6006612ac33c30880001ba800002488991398000402809b3b18bc63a5ca8d07c00001bd870204a800012dc77c2608000304494841842a10d44473000047c038047700000002ef843f06980000b4000048dcd54000122e313cba600004c730900000570000383c00038dc9f823e88973e686da0608411064c19d25580003968f7a12780850000c1a000017d25a44f81ee0e000a140001e40000000000000009d200008352b24e1b0000000449cc3235bc00006290ef00010cf38681b316a10fd3b091d319603583cbc00042780000000d6d00010d1000113c0001236129412f1e8ca35000069341e923c01fc46a0000ecc0000c5c148438c069c0000000325000076b0000000093c059148ca3c0860a3834b8db83f84aed000000000001212c4c0000000b0346a0a6f1b6c000000000046dcb6003bc0000e6495b1f380001fec7533fac4fb000075e22340000000ade03180000000000000067600008f61b489860b44bf91794bb83a1433824f913032f82df02c8ecf482c9313cac68f19006a3428400049604a900001630e34e5c00000003a3d11b07c8fbc08d048713a90600a4c0000cd40001ef801f3164c03243c00034cc15a3d04ea424b0780000102043ec03d0b1902702c0a391d8c8c440e82470acd1dc0b6c2b039306080de4d5e104025c00009f525c113a3ca4fdc3fc0e5f1be456e3dc41782fbc8f207f44a2128c55310c449a0fe83a91edc89d4424f3f055030d22dc7e9467497716e49d427705072b4927f0580376000096219b89bf1ae46c532ad05e00010ee14d854b3808f36166c6332a4d1b93f5ca2d26bc000447044423380001e3823900008d6431c69006d83a83f30000290c11e00011401080000136c0003f18f130000000158cef537c06241b94af500000000000e2a3cc400000006cc146c00047a400040a069f0001269066922300000001104a9a0000af44a2ce040000000000068800140004650000000089b19e80000000000447c0000000000296c61a0000cd200a41cd0001068190904a22f4ae3483c0000000d69489c65200000004654d660000d063fe80003fc80882d444a82188fc344fcd3b13b001c25c88d0482117a460cf6e2a7478f17fc35329
  | 41 => 0x3768fdd443c0fe0000c8c118cff41fdc00000000004968b6100000000de00003c6cf550000bff0000b31031025a32e4cc11b100
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5d7558e30040018dceb31460080031b5d6628c010006373aac51802000c6d7558a30040019aac6b8c60080123d20576c801000672bb643900203aae48158a20040019cac4b8c400800e1f21776480100145e426ec90020018dc83dd920040091d905bb240080023de0776480100c43ec36ea9002000c3e64dd520040018bcc7baa40080021fa1d654801003c3e43aca9002000c3c7459520040018b8e6b2a40080131d1c565480100bc5ec36e89002000c3e65dd1200400187acbba240080032798f74480100045f43ac890020068bc87591200400187eeab2240080030f1d564480100064e39ac89002004cb471591200402d1bb0db9a40080031799773480100062eb2ee69002000c9e64dcd200400193ac9b9a400800237a1d634801002c6e43ac69002000c5f7558d20040018b8eab1a400800327dd163480100064e3a2c69002004cd47158d20040018deeb31240080031b1d6624801000657ba4c49002000cac74989200400199ee73124008003331ce62480100267238cc49002000c6f7558920040018d8eab1240080032bdd16248010006563a2c49002000ccf735892004001998e6b124008013391c562480100063b32ee29002000c7565dc5200400196cc9b8a40080032d59371480100066b31ee29002000cd563dc520040019ccc5b8a40080033958b71480101d4f343e429002000ce776c8520040070fd0bbb040080021f617760801001c3f42aec10020048ed825d820040010ff0cba840080030f99175080100062f31aea100200087f8759420040010fb0eb2840080030f9d564080100061ebaac81002004cb67159020040018bceab184008003175d563080100266b38ac610020048ed8798820040018dceb31040080031b5d66208010006373aac41002000c6d7558820040735c902b1040080032d59171080100066ab1ae21002000ce6625c420040018e8ebbb220080032d1d376440100063bc2eec8802000c7485dd9100400196f09bb220080032d21376440100063baa6ec8802000c7554dd910040019af07bb220080033520f764401000673c16ec8802000ce482dd910040018eeedbaa20080032dddb74440100066bbb6e68802000cd7761cd10040019ceedb9220080023d61a72440101ccf3414e48802000ce7761c91004001aceea3922008003591d47244010006d3ba0e48802000da4741c91004001b8ee63922008003711cc72440101ccf3c30e488020399e5861c91004073accca39220080e75959472440101ced3320e48802039da5641c91004001acea839220080035955072440101cee3318e48802039dc5631c91004073bc30039220080033998072440101cef1300e48802000de3301c91004001bc0603922008003781ca2044010024f843a408802000b7385481100406d7610890220080d6f420d2044010
  | 1 => 0xd06212c408002b360c42588100247743e64b102004ae681cc962040014dd0a192c4080029b61432588100055742064b102000aad840c962040018deeb3aac408002aba12755881000556c24eab102004ae6819d562040015cb033aac408002b9e0575588100257240aeab102000a6e859d162040014db0b3a2c408012b9a06745881000572c0ce8b102000ae7815d162040095c902ba2c4080029ba14745881000536c28e8b102000ace831d1620400159b063a2c40822f991c7545881046536c2ca8b102000e2f549516204001c5f08aa2c4080038bdd15458810007163a2a8b10208ce64715516204119c5e82aa2c4082338b505545881045d37428a8b102004ae6819cd62040015cb0339ac4080029be1573588100053642ae6b102000aaf845cd620400155908b9ac408012b9205735881000574402e6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102000e4f5394d620400155d0829ac408002ab61053588100053742e86b102000a6d85d0d6204001c5aa9a1ac4080038b55143588100053742886b102000a6d8510d6204001d1a8621ac4080eb391c6705881000537428e0b102000a6d851c162040739c8e2382c408002aba13505881000556c26a0b102000ace83d41620400159b07a82c4080039ad4250588100053742e80b102000a6d85d01620400159d07a02c408002b360f405881000716aa480b102000a6e8510162040014db0a202c4080038b55040588100257340880b102000ae58110162040014dd0b982c4080029b61730588100055742660b102000aad84cc162040095cd02182c408002b960430588100246fc3ac719020048ed8798a32040070f90bbb2640800a2f213764c8100246e41eec990200087f855d932040070f90abb264080022fe11764c8100145e422ec99020048f4815d932040010fb0dbaa64080030f993754c81044e2f31eea990200087e8759532040010f90eb2a64080030f1d1654c8100045ec36e89902000c3e65dd1320400187acbba2640821f2798f744c8100045f43ac899020008bc87591320400187eeab2264080030f1d5644c8100246e43ac69902000c5f7558d32040018b8eab1a640800327dd1634c8100064e3a2c69902000c6f7598932040018d8eb31264080032bdd2624c810006563a4c499020048ec8758932040018deeab1264080031b1d5624c81000657ba2c49902000cac7458932040019aac7b8a64080033958b714c8100066cb1ee09902000ce962dc132040011f30c3826408012b960976c841002573c3ac59082000e667558b2104001ccaeab16420800399d5162c841000732aa2c5908200087f865d6300400187cc8bac60081d31798d758c0103ac3fc3acb180207487d87596300400187ceab2460080030f5d5648c0100062f3aac71802000
  | 2 => 0x47258c100052ec28e4b182000a9e841c9630400153b08392c608002a7a135258c100054ec26a4b182004ad681d4963040015ab03a92c60800393d4a5258c100052f42e84b182000a5d85d0963040095ad03a12c608002b56074258c100070eaa484b1820008de8710963040011bb0e212c60800297a144258c100052ec2884b182000e1d5410963040014bd0b382c608002976167058c1002c6f43ea0b1820008dd87d41630400153d09a82c608002a76135058c100072da84a0b182004ad68114163040015ab02282c60801637a1f4058c100046ec3e80b182000a5e85d0163040014bb0ba02c608003875524058c100052f42880b182000a5d851016304001c3aa8202c608012b5a044058c100056ac0880b182000c3f745526204005878e8aa4c4080021fe15739881001c3e42ae731020008bf845ce620400517908b9cc4080031bdd7529881000557426a53102000aad84d4a62040091db0f294c40800f1b9d6529881002476c38a53102000a6e85d0a62040014db0ba14c4080123b61e429881000716aa48531020048ed8710a62040014dd0a214c4080029b614429881000716aa0853102000ace8310a620400159b06214c4080123b61c329881000537428653102000a6d850ca620400155d08194c408002ab610329881000637baceb3102000aae849d6620400155b093acc4080029ba16749881000536c2ce93102000a6e851d262040014db0a3a4c408002b3a0c749881000566c18e9310208ca6d859526204001c5ea92a4c4080038be11549881000717ba2a93102000e2c745526204119c5e82aa4c4082338b505549881045d37428a93102000a6f855ce62040014d90ab9cc408002abe11739881000556422e73102000a6e851ce62040014db0a39cc408002aba10739881000556c20e73102000e4f5394e620400155d0829cc408002ab61053988100053742e873102000a6d85d0e6204001c5aa9a1cc4080038b551439881000537428873102000a6d8510e6204001d1a8621cc4080029ba14709881000536c28e13102000aae84d42620400155b09a84c408002b3a0f509881000566c1ea13102000a6e85d0262040014db0ba04c408002b3a0f409881000566c1e813102000e2d5490262040014dd0a204c4080029b614409881000716aa0813102000a6e85cc262040014db0b984c408002aba13309881000556c266131020048f4815d562040091e902ba2c40822f1d1c754588100061fba2a8b102002c3c7455162041198e8e2aa2c4080123ba1f525881000637baea4b102000aae84d49620400155b09a92c40800f1b9d652588100247643aa4b1020048ee87d0962040014dd0ba12c4080029b61742588100257340e84b102000e2d5490962040091d90ea12c4080029ba14425881000536c2884b102000e2d54109620400159
  | 3 => 0x8b28208b87e871d165040018bee739aca080028fa1073594100051ec20e6b28200087e87d0d65040010fb0fa1aca080030f5d343594100061eba286b28200087e8710d65040010fb0e21aca080038750c43594100051f426e4b282000a3d84dc965040018dee5392ca082469de0572594100253a40ae4b28200087e87d0965040010fb0fa12ca080030f5d242594100043f43884b28200087d87109650400187ae8212ca0800297a0c42594100052ec1884b282004a7681cc965040014eb03992ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca082429d606705941003c3f43e80b28200087d87d0165040014bd07a02ca080029760f40594100061eba480b28200087e8710165040010fb0e202ca080030f5d0405941003c3f43e60b28200087d87cc1650400147d09982ca080028f61330594100253b40860b282000a75810c1650400187eeb3aac8082328f61e75590100061fc3aeab20208cc3f715d5640411987ae2baac8080030f1c1755901045d1f428eab202000a3e85dcd640400147b0bb9ac8080030f5d773590100061ebaae6b20208fabb805cd640400157100b9ac8080028fa1473590100051ec28e6b202000c9d731cd6404001c3ea729ac8080022fa1c53590100045ec38a6b202000a3e85dc9640400147b0bb92c8080030f5d672590104755bc0ae4b202004ab4815c9640400147d0a392c8080028f61472590100061eba8e4b202000a9e831c9640400153b06392c8080022fa1f52590100045ec3ea4b202000e2f52949640400956d03992c808002ad60732590100045f43864b2020008bd870c9640400147d0a192c8080028f61432590100061ebace0b20208dab5819c1640400d17d0fa82c8080022f61f50590100054f41ea0b202000a9d83d416404001c76a1282c80801a2fa1f30590100045ec3e60b202000a3e85cc1640400147b0b982c808012ada0430590100055ac0860b202000c9c435d163040011f100ba2c60800b0f9d15458c100061eba2a8b1820048de87d4d63040018beeba9ac6080123721d5358c100246f43e86b182000a5e85d0d63040014bb0ba1ac608003875534358c100246e43a86b182002c9c7450d6304001c3aa8a1ac60800e1fa147258c100043ec28e4b1820028be841c9630400117b08392c60800317dd67558c100054f420eab182000a9d841d563040014bd0b3a2c608002976167458c100056dc02e8b182000ad8805d163040014bd0a3a2c608002976147458c100064eba0e8b18208ca5d859516304001c3ea92a2c60800387e115458c100070f3a2a8b182000e1d745516304119c3e82aa2c608233875055458c1045d2f428a8b182000a5f855c963040014b90ab92c608002a7e117258c100054e422e4b182004ad4815c963040015b100b92c60800297a1
  | 4 => 0x1440018deebb1262880031b1d7624c51000637ba8c498a2000c6c751893144001970c9b8262880033a18b704c5100065c320e098a2000cdb631c131440019d0c4382628800e1f21676c85100043e432eb90a2000c3c645d721440018b8c6bae42880021fe1f65c85100043ec3ecb90a2000c3e75d93214400187aebb264288003179d763c85100062ebaec790a2000c6e75d8b21440018daebb1642880031b9d462c851000636ba8c590a2000ce8629c321440019b0c7b8242880033618c704851000675b10e090a202087c865d63044001878c8bac60881d31718d758c1100043fc3ecb182200b87d87d96304400187cebb2460880030f5d7648c1100062f3aec71822000c5d75d8e30440018dcebb1460880031b5d7628c110006373a8c51822000c6d7518a30440839a8e3b1a60880e7391c4624c11000672316e29822039ce67118b20440019c8c4b8e408800e1fa1776481100043ec2eec90220028be84dd9204400117b09bb2408800637a0f76481100046ec1eec902200087f855d920440070f90abb240880022fe1176481100145e422ec90220008df835d920440031b906bb2408824e1fa1b75481100061e326ea9022000c5c63dd520440010fd0fb2a408810e1f21f65481100061e3a6ca9022000c5c73d9520440878e8e3b2a408824a2fa1b74481100061fb2ee89022000c3c65dd12044001938c7ba240880022fa1f64481102145e43ec89022000c3f75d912044001878ebb224088003271cf64481102165a38ec890220408de86dcd20440018becbb9a40880031719773481100064fb26e69022000c9c64dcd20440011bd0fb1a40881063721f63481100062fbaec69022000c5c75d8d204400193ee9b1a4088003271d3634811020e6a38ec69022000c6f75d8920440018d8ebb1240880032bdd36248110006563a6c49022000ccf73d892044001998e7b1240880eb391c7624811000637ba8c49022000c6c75189204400195ee831240880032b1d0624811000667b98c49022000ccc7318920440739c8e231240880031dd9771481100063a32ee29022000cb764dc52044001968c9b8a408800335d8f71481100066a31ee29022000ce462dc520440070f90b3b0408804e1f21975081100061e322ea1022000c5c635d420440010ff0fb28408802e1f61f65081100061f3aec81022000c3d75d9020440018bcebb184088003175d76308110006373aec41022000c6d75d8820440018dcea31040880031b5d4620811021e3b3b6cb0822042cb676d9210440839acedb1c2088007359d863841101d6733b6c50822039ce67618a1044001cceca314208800399194628411000753b20c50822000ea46418a1044001d8ec63142088003b118c628411000733aa0c50822000e655418a10441190fb0f3a2ca080030fdd274594100061fc22e
  | 5 => 0x80029b616541891000717aa4a83122000e2f845506244001c5ee8aa0c4880038b1d1541891000537428a83122000a6f855cc62440014d90ab98c488002abe11731891000556422e63122000a6e851cc62440014db0a398c488002aba10731891000556c20e63122039ae6811cc62440015cb02398c488002baa0073189101cd74c00e63122000e4f5394c624400155d08298c488002ab61053189101cd73408a63122000ae58114c62440014dd0ba18c4880029b617431891000716aa6863122000e2d5450c62440014dd0a218c4880029b614431891000746a18863122039ae68110c62440015cb02218c4880029ba17711891000536c2ee23122000a6e85d0462440014db0ba08c4880038b553411891000716aa2823122000a6f855c062440014d90ab80c488002abe11701891000556422e03122000acf835c0624400159906b80c488002aba13501891000556c26a03122000ace83d40624400159b07a80c4880e6b9a07501891000572c0ea03122000ae78154062440735c902a80c4880029ba17401891000536c2e803122000ace83d00624400159b07a00c4880e6b9a07401891000572c0e803122000e2d5490062440015cf02a00c4880e6b9205401891000537428803122000a6d851006244001c5aa8200c4880029ba17301891000536c2e603122000aae84cc0624400155b09980c4880e6b9a07301891000572c0e603122000a6f8544062440014d90a880c488002abe11101891000556422203122000acf83440624400159906880c48800e1fa17768c9100043ec2eed19220028be84dda324400117b09bb464880023ba0b768c9100043fc2aed192200387c855da324400117f08bb4648800a2f211768c91000c76c38c5192200387e85dd932440010fb0bbb2648800a2fa13764c9100045ec26ec992200387e859d932440010fb0b3b2648800a2fa12764c9100045ec24ec992200087f855d932440070f90abb264880022fe11764c9100145e422ec99220008ef825d932440011ef02bb264880023ee01764c91001c3e428ec99220028bc841d932440010fd0dbaa64880030f193754c91044e2e31eea992200087e87d9532440010f90fb2a64880030f1d3654c9100045f436e89922000c3f65dd13244001878cbba2648821f2718f744c9100045f43ec899220008bc87d91324400187eebb2264880030f1d7644c9100062fbaec69922000c5c75d8d324400193ee9b1a6488003271d3634c91000c7743ec49922000c6f75d8932440018d8ebb1264880032bdd3624c910006563a6c49922000c6f7518932440018d8ea31264880032bdd0624c910006563a0c4992200087e86dd53144001878c9baa628820b1718f754c51041c3f43eca98a208287c87d95314400187eebb2262880030f1d7644c5100062fbaec698a2000c5c75d8d3
  | 6 => 0x66639ee4b122000c7775dc562440018e8ebb8ac4880032ddd371589100065a3a6e2b122000cd773dc562440019a8e7b8ac4880031dd5371589100063aaa6e2b122000cd873dc162440011df0eb10c4880029be1562189100053642ac43122000aaf84588624400155908b10c488002b3e0d62189100056641ac43122000c3f745506244005878e8aa0c4880021fe15731891001c3e42ae631220008bf845cc624400517908b98c4880029ba16721891000536c2ce43122000aae849c8624400155b09390c488002b3a0e721891000566c1ce43122000c6f75d48624400155d09a90c488002ab613521891001c76c3ca43122003c6e7594862440011db0e290c488002ba60052189100053742e843122000a6d85d0862440051db0f210c4880038b552421891000476c38843122000a6e8510862440014db0a210c4880038b550421891000567418843122000acd8310862440015cb02210c4880029ba14321891000536c28643122000aae840c8624400155b08190c488002b96043218910006373b6ca3122000a6d84d9462440011db0f328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac84594624400159f06b28c488002b320d6518910006373b0ca3122000a6d84194624400195cedb20c4880038bd9764189100071632ec83122000e2f85d906244001c590bb20c4880023b61e64189100053742cc83122000a6d85990624400159d07320c488002b360e641891000477c3ac83122000a6f8559062440014d90ab20c488002b3e0d64189100056641ac83122000a6e8519062440014db0a320c4880032b9d8641891000717b28c83122000e2c651906244001c5d0a320c4880038b614641891000537436a83122000a6c86d5062440018dcedaa0c4880038bd93541891000716326a83122000a6e8655062440014d90caa0c4880031b9d9541891000717b22a83122000e2c64550624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c48800393d53631891000726aa6c631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000727aa0c63122000e4d5418c6244129d9620318c488253b2040631891000637bacea3122000aae849d4624400155b093a8c488002baa0075189101cd74c00ea3122000a6e859d062440014db0b3a0c4880029ba14741891000536c28e83122000ace831d0624400159b063a0c4880e6b9a04741891000572c08e83122000aea801d062440735d3003a0c48
  | 7 => 0x3e7419662440018bce632cc4880030fd9574989100061e32ae93122000c3e75d92624400187aebb24c488003279cf64989100061f3a8c93122000c3d75192624400193ce6324c48800317d9573989100062e32ae73122000c9f645ce6244001938c8b9cc488003179d763989100062ebaec73122000c9e74d8e624400193ae9b1cc488003179d463989100062eba8c73122000c9e7418e624400193ae831cc4880031b9d7629891000636baec53122000cae74d8a624400195ae9b14c488003339cf629891000666b9ec531220028be84dd6624400117b09bacc48800637a0f75989100046ec1eeb312200087f845d662440070fd0bba4c4880021f617749891000c6f41ee931220008dd83dd2624400187ceb3a4c4880030f5d674989100061f3aae93122000c3d755d2624400187d0aba4c4880030f615749891001c3fc3ea9312200087d87d52624400587ce9aa4c4880030f5d354989104b62f39ea9312200087f8755262440010fb0eaa4c48800b0f9d154989100061eba2a93122095c5e7355262440018bceb39cc488003175d673989100064f3a4e73122000c9d749ce62440018bceab9cc488003175d573989100064f3a2e73122000c9d745ce62440018bea8b9cc48800317551739891001c3f436eab12200087e87d956244001878e9b2ac488003171cf65589100043f438cab122000c3c7419562440018b8e632ac48800a2fa1b74589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d063589100043ec26eab1220008bf845d5624400517908baac48800237e0d755891000c6e41aeab1220008ef825d562440011ef02baac4880030fdd774589100061e3aee8b122000c3f85dd162440018790bba2c4880021fe15745891001c3e42ae8b1220008df835d162440031b906ba2c4880023be0974589100047bc0ae8b122000c3f751d16244001878ea3a2c4880021fa1f545891001c3e43ea8b122000c3f74d516244005878e9aa2c48825b171cf54589100043f43aa8b12200087c87551624400187ee8aa2c48800b0f1d154589104ae2e39aa8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100
  | 8 => 0xedaa0c68800387d935418d100070e326a831a2000a5e8655063440014b90caa0c688003179d95418d100070fb22a831a2000e1c64550634400587ce8aa6c4880030f5d154d891000636baea5b122000aae84d4b624400155b09a96c48800f1b1d652d891001c77c3aa5b122000a6e85d0b62440014db0ba16c4880038b55242d891001477c3a85b122000a6e8510b62440014db0a216c4880038b55042d89100056741885b122000acd8310b62440014dd0a196c4880029b61432d89100055742065b122000aad840cb62440014db09b2ec488002aba1265d891000556c24cbb122000ace83997624400159b0732ec488002abe1165d891000556422cbb122000acf83597624400159906b2ec4880029b61065d891000717b2ec9b122000e2c65d936244001c5f0bb26c4880038b21764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000537428c9b122000a6d851936244001c5eca326c4880038b19464d891000717428c9b122000e2d8519362440014dd0daa6c4880029b21b54d891000717b26a9b122000e2c64d5362440014dd0caa6c4880029b21954d891000717b22a9b122000e2c645536244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f6244001c9ea9b1ec4880039355363d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727aa0c7b122000e4d5418f62440018daea3aec488002aba1075d891000556c20ebb122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce9b122000a6e851d362440014db0a3a6c4880038bd5254d891000717c22a9b122000e2e745536244001c5ae8aa6c4880029ba1773d891000536c2ee7b122000aae84dcf624400155b09b9ec4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec48800393d4e53d891000557420a7b122000aad8414f62440014dd0ba1ec4880029b61743d891000716aa687b122000e2d5450f62440014dd0a21ec4880029b61443d891000746a1887b122000a6f855c762440014d90ab8ec4880029ba1741d891000536c2e83b122000e2d54d076244001c5aa8a0ec488002aba1350d891000556c26a1b122000ace83d43624400159b07a86c4880029ba1740d891000536c2e81b122000ace83d03624400159b07a06c4880038b55240d89100053742881b122000a6d851036244001c5aa8206c4880029ba1730d891000536c2e61b122000aae84cc3624400155b09986c4880030f9d365989100062f39ecb3122000c
  | 9 => 0x41d8d100070eaa683b1a2000e1d5450763440014bf0ab86c6880029721570d8d100054fc22e1b1a2000a9c845c363440831bd0fa86c6880023761f50d8d100054f426a1b1a2000a9d84d4363440831bd0fa06c6880023761f40d8d100052f42e81b1a2000a5d85d036344001c3aa9206c68800297a1440d8d100052ec2881b1a2000e1d5410363440018b8c7baac6880021fa1f6558d100061e3a6cab1a200087e871956344001878e832ac6880030fd977458d100061e32ee8b1a2000c9c63dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a20008be87191634400187eea322c6880030f1d46458d1000637b2ee4b1a2000c6c65dc9634400195ec9b92c6880032b1937258d100066631ee4b1a2000c6f651c963440018d8ca392c6880032bd907258d1000656320e4b1a2000ccc631c963440070fd0fbaac6880021f6137558d100045fc22eab1a20028bc845d563440011bf06baac6880023be097558d1000476412eab1a200087e871d5634400517d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f85dd163440018790bba2c6880021fe157458d1001c3e42ae8b1a20008df835d163440011df04ba2c6880023b2097458d100047dc02e8b1a20008be871d1634400187eea3a2c6880030f1d47458d100043f43ea8b1a200387c87d51634400187ee9aa2c68800b0f1d35458d100043f43aa8b1a200087c87551634400187ee8aa2c68800b0f1d15458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f54dc963440018daa9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d1000637aa0e4b1a2000c6d541c963440019c8e5b8ac6880032e1d37058d1000674396e0b1a2000c5e76d9463440014bb09b28c6880023761e6518d100052f42cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440014bd0c328c688003179d86518d100052ec20ca31a2000c9e76d906344001c3ecbb20c688003871976418d100070fc2ec831a2000e1c85d9063440011bb0f320c68800297a166418d100052ec2cc831a2000a9e84990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000adb8059063440014bd0a320c688002976146418d100054f430c831a2000c9e761906344001c3eca320c688003871946418d100070f428c831a2000e1d85190634412fd3620320c68825fa60406418d100052f436a831a2000a5c86d5063440018bc
  | 10 => 0xb222000a9c83597644400155f04b2ec888002ab20965d91100051f430cbb222000c3e76197644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400187ae3baec8880030f9c375d91100061e386ebb222000a3e859d7644400187aea3aec8880028fa1c75d91100061f438ebb222000c3f75dcf644400147d0b39ec8880028f61673d91100064fb9ce7b222000a3f855cf64440014790ab9ec8880030fdd573d91100070fa9ca7b2220008be8714f644400117b0e29ec8880028fa1672d91100051ec2ce5b222000c3f759cb644400153d07396c888002a760e72d91100051fc2ae5b222000a3c855cb644400187eea396c8880022fa1f52d91100045ec3ea5b222000e2f5294b644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644400187eebb8ec8880daaea0371d91102145f43ea1b2220008bd87d43644400153d07a86c888002a760f50d91102145f43e61b2220008bd87cc3644400147d0b986c8880028f61730d91100064e21ee9b1a2000c3f745536344005878e8aa6c688003175d753d8d1001c6fc3aa7b1a2000a5e85d0f63440014bb0ba1ec6880038755343d8d100146fc3a87b1a2002c9e7450f6344001c3aa8a1ec68800e1fa1672d8d100043ec2ce5b1a20028be849cb634400117b09396c6880029761365d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052ec20cbb1a2000e1f65d936344001c38cbb26c68800387e1764d8d100070e42ec9b1a2000a5e8599363440014bb0b326c688002b3a0a64d8d1000566c14c9b1a2000a5f8559363440014b90ab26c688002b3e0964d8d1000566412c9b1a2000a5e8519363440014bb0a326c68800387d9464d8d100070e328c9b1a2000e1e851936344001c3b0a326c68800297a1b54d8d100052e436a9b1a2096c5e76d536344001c3ec9aa6c6880038719354d8d100052f432a9b1a2000a5c86553634412b8bcecaa6c68800387d9154d8d100070e322a9b1a2000a9e849d7634400153b093aec688003175d475d8d100052f42ce9b1a2000a5d859d3634400193ee93a6c68800297a1474d8d100052ec28e9b1a2000e1f549536344001c3f08aa6c68800387dd154d8d100070e3a2a9b1a2000a5e85dcb63440014bb0bb96c688002a7a1372d8d100054ec26e5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000a9e84d4b634400153b09a96c68800393d4a52d8d100052f42e85b1a2000a5d85d0b6344001c3aa9216c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c6880038755042d8d100052f42ee3b1a2000a5d85dc763440014bd0ba0ec68800297617
  | 11 => 0x84005878e8aa2c508257171cd5458a1000c6f43ee6b142000c5f75dcd62840018b8ebb9ac50800327dd37358a100064e3a6e6b142000c5f54dcd62840018baa9b9ac50800317dd47358a100062e3a8e6b142000c9f741cd6284001938e839ac5080031ddd77158a100063a3aee2b142000cb774dc56284001968e9b8ac50800335dcf7158a100066a39ee2b1420008ef87588628400147b093a8c5080021fe117518a1001c3f42ee8314200087d85dd062840070ff0faa0c5080021f61f5418a100043fc3aa8314200087d87550628400187ee8aa0c50800b0f1d15418a1000678b8ce0314200087f855da32840070f90abb465080022fe11768ca100145e422ed194200387e851da32840010fb0a3b4650800e1fa16764ca100043ec2cec99420028be849d9328400117b093b265080021fe15764ca1001c3e42aec99420008bf845d9328400517908bb2650800237e0d764ca101d477c3ac590c2000c76755db21840018eaecbae43080035c5d570c86101cc7743cc490c2004cf2605d821840011eb0fb1043080027961f62086101cdf1406c410c203abe28018821840091bd0fb1a61080023ba1c62482101ce72388c490420009e687c8520840011df0eb1041080027920976c42100043f436e9b2a200387f87d93654400187ae9b26ca880021f61e64d95100052f41cc9b2a2000a5d8399365440014dd05326ca880029b60a64d95100043fc3ac9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a200b87d87193654400187ae8326ca880030f61c64d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100043ec3ce9b2a2000c3f845d365440010fd0e3a6ca880030f5d074d95100051f424e7b2a2000a3d849cf65440018bae639eca880021fa1f43d95100043ec3e87b2a2000c3f74d0f654400187ee8a1eca880021fa1c43d95100043ec3887b2a2000e1d4310f654400147f08b96ca880028f21172d951000636b90e5b2a200087e87d0b65440010fb0fa16ca880030fdd242d95100043f43885b2a200087d8710b654400187ee8216ca8800297a0c42d95100052ec1885b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2037a7a80dc765440010fd0fa0eca880021f61f41d95100061fba683b2a2000c3f7450765440870fd0fa06ca880021f61f40d95100052f41e81b2a2000a5d83d0365440010fd0e206ca8802e1f61c40d951021c3f43e61b2a200087d87cc3654400147d09986ca880028f61330d95100051f436ebb222000c3e76dd7644400147d0c3aec8880030f9d875d91100061f3b6cbb2220008bd87997644400147d0b32ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec8880022fe1d65d91100054fc1acb
  | 12 => 0x33a943764802000674a86ec9004000c6f76dd520080018deecb2a40100032bddb744802000667bb6e69004000ccf761cd20080019ceedb8a401000339dd87148020006b3ba8e29004000d64751c52008001b4ee838a4010003691d07148020006e3b98e29004000dc4731c520080739cb0c38a4010003599947148020006b2b28e29004000d67541c52008001acaa838a40100e63b21d61480201ce7238ac29004000c7a65dd920080018f0ebbb240100032e1d376480200063dc2eec9004000c7885dd920080018f6a9bb240100031e553764802000675296ec9004000ce952dd920080018f6edbaa40100031edd965480200065dbb6e89004000cdb76dcd20080019b6ec39a40100033cddb714802000679bb0e29004000dd0731c52008001bc6e438a401000e1fa1f7558f100043ec26eab1e208187e871d563c400147b083aac7880021fe157458f1001c3e42ae8b1e20008ef825d163c40011d904ba2c7880021fa1f5458f1001c3e43ea8b1e200087e8755163c40010f90eaa2c78800b0f9d15458f100061eba2a8b1e20048dc8754d63c40091b90ea1ac78800b271d14358f100070eaa286b1e207c87d879d662c400147b093acc58800e1fe1d7598b100043fc22eb316200387e85dd262c40010fb0bba4c58800e1fe1f5498b100043ec3ea9316200087f8755262c40010fb0eaa4c5880030fdd15498b100161e3a2a93162000c3f7455162c4005878e8aa2c58800e1fa17768cb100043ec2eed19620048df8758e32c40010ff0abb2658800e1f215764cb100045fc22ec99620028bc845d932c40731df0eb1641880ea3ba1e62483100267238cc49062004ce47158920c40010fb0f3aec7080028f61275d8e1001c3fc3aebb1c200087f845d763840070fd0bba6c7080021f61774d8e1000477416e9b1c20008ed82dd363840070ff0faa6c7080021f61f54d8e100043fc3aa9b1c200087d87553638400187ee8aa6c70800b0f1d154d8e1001c6fc3aa7b1c20028df8750f638400593ce8a1ec7080038755143d8e104c678b8ce1b1c2000c3f745516384005878e8aa2c70800e1fa147258e100043ec28e4b1c2002c3e74553628400187ae8aa6c50800b0f9d15498a100061eba2a9314200087f855ce62840070f90ab9cc50800e1fa1f7558a100043ec26eab1420008bf845d5628400517908baac50800237e0d7558a1000c6e41aeab14200087e871d5628400517d0fba2c5080030fdd77458a100061e3aee8b142000c3f85dd162840018790bba2c5080021fe157458a1001c3e42ae8b1420008df835d162840031b906ba2c5080022fa1c7458a100061fba8e8b142000c3c751d162840010fd0faa2c50800e1f21f5458a100061fba6a8b142002c3c74d51628412d8b8e7aa2c5080021fa1d5458a100043e43aa8b142000c3f7455162
  | 13 => 0x51f42062b284000a3d840c565081354db05382ca1004e1fa1f40594200043ec3e80b284000a5e83d0165080014bb07a02ca100030f5d240594200053741480b284000a6d8290165080010fd0e202ca100021f61c40594200061eba080b28401387e87cc165080010fb0f982ca100028fa1330594200051ec2660b284000a6e820c165080014db04182ca100021f61e65d8c200051ec24cbb18400087f8759763080010fb0f3aec6100028f61275d8c2001c3fc3aebb18400087f845d763080070fd0bba6c6100021f61774d8c2000477416e9b18400387f87d5363080010fb0faa6c6100021fe1d54d8c200043ec3aa9b184000c3f745536308005878e8aa6c6100028f6126558c200061fba2a8b184002c3c7455163080051b90ea1ac61000b271d14358c200070eaa286b18403287d86dd532080010fd0eb2a641004e1f21d654c8200061e3a2ca9904000c3e65dd1320800187acbba264100028f61265d84200051ec24cb3084000a3d84995610800187ee8aa2c21000b0f1d154584200147a43a82b084000e355450561080070ff0cba8c2100021f61e65184200051ec24ca3084000c3e7499461080018bce7328c2100021fe1d65184200061f3a2ca3084000c5e73594610800187ccaba0c2100030f59574184200265b30ae83084000c5e655cc61080018bacab98c2100133598573184200047bc3ac23084000cb57458461080019aae6b08c21000e1fa16768c4200043ec2ced18840048f6819da31080070f90bbb262100021fe15764c42001c3e42aec98840008bf845d9310800517908bb2621000e1fa14764c4200043ec28ec98840028be841d9310800117b083b262100021f61b754c4200043f43aca988400087c87595310800199ac639262100063d21d614c42000678b08e0988400087f865d721081330ff0eb2e421000e1fa1576884201543fc32eb108401387f8759621080010fb0eb2c42100030f9d165884200062f39acb1084000c3e655d2210800187acaba442100031799573884200062eb2ae71084000c6e655da21080018dd0abb442100031b615768842000637aa2ed1084000c6d545da21080018daecb2c42100031e59670084200063cb2ae01084039de0105c021080010ff0cbac60101d61fe1d658c0203a43ec3acb1804000ccd639ca30080731df0eb0e40100e7399c561c802009e3cbb2cb1004000e696598a20080070f90bbb240100621f61b75480200043f43aca900401387c875952008001878e8b2a4010003171cd65480200061f32ee89004000c3d65dd120080018bccbb9a40100031759773480200063b32ee29004000c7565dc520080018ecca38a40100031d59471480200063732eec9004000c6c75dd92008001958e9bb240100031be1776480200063642eec9004000c6f54dd920080018daa9bb24010
  | 14 => 0xe74d9621480018bce7b2c42900022f21974885200061fb2ae910a4000c3c655d22148001938c6ba442900132d18574885200045ec3ec910a4000c3e75d92214800187aebb244290003279cf64885200046e432e710a4000c5f655ce21480018b8cab9c429000327d9173885200064e322e710a4004cd4615ce21480011bb0fb1c4290003179d763885200062ebaec710a4000c9e74d8e214800193ae9b1c42900031d9d761885200063abaec310a4000cb674d86214800196ae9b0c4290003359cf61885200066ab9ec310a4004cf0619c221480019b0c7b8242900033618c704852000679b08e090a4000ae686dc521480095cd0db0a429000399d94614852000732328c290a4000ea7641852148001d48c830a4290003b1d8c614852000762318c290a4000de3711c121480410f90cbac60900030f191758c1203a62e31aeb182400087f87d9630480310fb0fb2c60900030f9d7648c1200061ebaec91824000c5e75d8e30480018baebb1c60900031d9d7618c1200063abaec31824000c767518630480018eaea30c609000333d8c724c12000673b90c29824000ce4721853048001da0c630e40900631b9db65881200be573b6c91024016cce76d8e204800399cec31c40900ea3b21971881201d67230ae31024000e67651862048001cc8ca30c4090003a9d90618812000752320c31024000ec7631862048001d88c630c40900eb3961c618812000733aa0c31024000e65541862048001cd6cbb0440900021fe1974594200043f43ec8b284000c3d74d9165080270fd0f322ca100030fdd2645942001c3f43ac8b284000c3f7459165080010fd0e322ca100030f5d064594200052f418c8b284000a5d8319165080014ed02322ca100029d60464594200051f420c6b284000a3d8418d65080014ed0231aca100029d60463594200043ec3ce8b284000c3f749d1650800187f08ba2ca100021fa1c74594200061eba0e8b284000c5f739cd650800147d0839aca100028f61073594200043f43e86b28400087d87d0d650800187ae9a1aca100030f5d143594200043f43886b28400087d8710d6508001c3a8621aca1026a9e602725942009c3f43e84b28400087d87d09650800187ae9212ca100021fa1c42594200043ec3884b284000c3d7410965080014bd06212ca100029760c42594200043f43864b28400087d870c9650800147d08192ca100028f61032594204dd37c12e2b284000a6c825c5650800147d0838aca100028f61071594200052f418e2b284000a5d831c565080010fd0fa0aca100021f61f41594200061eba682b284000c3d7450565080014df04a0aca100029b20941594200043f43882b28400087d8710565080014bd0620aca100029760c41594200053741662b284000a6d82cc565080010fd0e18aca100021f61c315942000
  | 15 => 0x4aa0c29000395d4e53185200055b420a630a4000ab58414c61480015cd04298c290002b960853185200053b42e8630a4000a7585d0c6148001c6aa9a18c2900038d551431852000573c128630a4000ae48250c61480014ed0a218c2900029d61443185200074aa188630a4000ae68210c61480015cb04218c290002ada1352185200055ac26a430a4000e675294861480014ed0ba10c2900029d61742185200071aaa48430a4000a768510861480014eb0a210c2900038d55042185200056b4188430a4000ad5831086148001d4a84210c2900029de1532185200053a42a6430a4000ab7844c8614800156908990c290002bce013218520005784026430a4000a76850c861480014eb0a190c290002ada1032185200055ac206430a4000ec5320c8614800156d09a80c290002ad61350185200056b41ea030a4000ad583d4061480015cd05a80c290002b960b501852000739a84a030a4000ae78254061480015c904a80c2900029da1740185200053ac2e8030a4000ad683d0061480015ab07a00c290002b9a0b401852000572c168030a4000e355490061480015cf04a00c290002b920940185200053b4288030a4000a75851006148001c6aa8200c2900029da1730185200053ac2e6030a4000ab684cc0614800156b09980c290002b9a0b301852000572c166030a4000a778548061480014e90a900c290002ade1120185200055a4224030a4000ad78348061480015a906900c2900021fe15768c52001c3e42aed18a40008bf845da314800517908bb462900123d205768c52000667b1ce518a4004ce4619ca31480099c8c2b94629000e1fa17764c5200043ec2eec98a40028be84dd9314800117b09bb2629000e1fa16764c5200043ec2cec98a400387c851d931480010fd0dbaa62900030f193754c5204162e31eea98a4081c7461dd531480010fd0fb2a62900021f21f654c5200061fbaec898a4000c3c75d9131480018beebb1a6290003171d7634c52000c7b43ec298a4000c7775d8531480018e8ebb0a629000e1f21676c85201643e432eb90a4000c3c645d721480018b8c6bae42901f31d18575c85200043fc3ecb90a401887d87d97214800187cebb2642900030f5d764c85200062f3aec790a4000c5d75d8f21480018d8cb3b642900032b19276c8520006373aced90a4000c6f859db21480018d90b3b642900031bd5276c852000636aa4ed90a4000ce7819db21480018dcecbae42901f39918575c8520006373b6cb90a4000cae76d93214800199cedb1e4290003339d863c8520006733b6c390a4000e67651872148001cc8ca30e4290003a9d9061c852000752320c390a4000ec7631872148001d88c630e42900eb3918670c85200043e432eb10a4000c3c645d621480018b8c6bac42900131d18575885200043ec3ecb10a4000c3
  | 16 => 0x3985200064e322e730a4004cd4615ce61480018bcebb1cc290003175d763985200064f3a6c730a4000c9d74d8e61480018bcea31cc290003175d463985200064f3a0c730a4000c9d7418e61480018ecebb0cc2900031d5d761985200065b3a6c330a4000cb574d8661480019ace7b0cc290003355cf619852001c3f436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac29000a2fa1b74585200061fb2ee8b0a4000c3c65dd1614800117d0fb22c2900030fdd764585200061e3aec8b0a4000c9c73d91614800117d0e322c2900030fdd464585200061e3a8c8b0a4000c9c7319161480018becbb9ac2900031719773585200064fb26e6b0a4000c9c64dcd61480011bd0fb1ac29000317dd763585200062e3aec6b0a4000c9f74d8d6148001938e9b1ac29000237a1c63585200062fba8c6b0a4000c5c7518d614800193ee831ac290003271d063585200047bc3ac230a4000a778558461480014e90ab08c290002ade1161185200055a422c230a4000ad78358461480015a906b08c2900031d9db65185200053ac26ca30a40008f587994614800156d09328c290002ad61265185200056b41cca30a4000ad58399461480011ef0eb28c290002ade1165185200055a422ca30a4000ad78359461480015a906b28c2900031d9d865185200053ac20ca30a4000cb676d906148001c6ecbb20c2900038d19764185200071bc2ec830a4000e3485d9061480011eb0f320c2900029da1664185200053ac2cc830a4000ad68399061480015ab07320c2900023de1d64185200053bc2ac830a4000a748559061480015af06b20c290002b520d64185200053b428c830a4000a7585190614800196cec320c2900038dd9464185200071a328c830a4000e36851906148001c6b0a320c2900029da1b54185200053a436a830a4000e3764d506148001c68c9aa0c2900029da1954185200053a432a830a4000e37645506148001c68c8aa0c290003359db63185200072bb2ec630a4000e5465d8c6148001d2ec9b18c290003a519363185200072baa6c630a4000e5554d8c61480011eb0f318c2900029da1663185200053ac2cc630a4000ab68498c614800156b09318c2900023de1d63185200053bc2ac630a4000a748558c614800156f08b18c290002ad21163185200066b3b0c630a4000e576518c6148001ca8ca318c290003a5d9063185200074a320c630a4000e575418c6148001caaa8318c29000399d9572185200073232ae430a4000ea7645c86148001d48c8b90c290003b1d8d72185200076231ae430a4000ae682d5061480015cb05aa0c29000399a0b541852000732c16a830a408be6672d506148001c6ea92a0c2900038de1154185204671b3a2a830a408ce35745506148119ccce
  | 17 => 0xa4000ab784597614800156908b2ec290002b5e0d65d85200056a41acbb0a4000a75841976148001c6ecbb26c2900038d19764d85200071bc2ec9b0a4000e3485d9361480014ed0b326c2900029d61664d85200056b41cc9b0a4000ad58399361480014ef0ab26c2900029d21564d85200056bc1ac9b0a4000ad48359361480014ed0a326c2900029d61464d85200071bb28c9b0a4000e34651936148001c6d0a326c2900038d61464d85200053b436a9b0a4000a7486d536148001c6ec9aa6c2900038d19354d85200053b432a9b0a4000a74865536148001c6ec8aa6c2900038d19154d85200072bb2ec7b0a4000e5465d8f6148001d2ec9b1ec290003a519363d85200072baa6c7b0a4000e5554d8f61480014ed0b31ec2900029d61663d85200055b424c7b0a4000ab58498f61480014ef0ab1ec2900029d21563d85200055bc22c7b0a4000ab48458f6148001caeca31ec2900039519463d85200074bb20c7b0a4000e946418f6148001caea831ec2900039555063d85200055b424ebb0a4000ab5849d761480015ad073aec290002b560e75d85200053b42ce9b0a4000a75859d361480015ad073a6c290002b560e74d85200053b428e9b0a4000a75851d36148001c6ea92a6c2900038de1154d85200071bba2a9b0a4000e347455361480014ed0bb9ec2900029d61773d85200053b42ce7b0a4000a75859cf614800156d0939ec290002ad61273d85200072ba9ca7b0a4000ab68414f614800156b0829ec2900029da1743d85200053ac2e87b0a4000e3554d0f6148001c6aa8a1ec2900029da1443d85200053ac2887b0a4000e954310f614800156d09a96c290002ad61352d852000733a94a5b0a4000a7685d0b61480014eb0ba16c2900038d55242d85200053b42885b0a4000a758510b6148001c6aa8216c290002b5a0c42d85200056ac1885b0a4000a77854cb61480014e90a996c290002ade1132d85200055a42265b0a4000a76850cb61480014eb0a196c290002ada1032d85200055ac2065b0a4000a7685dc361480014eb0bb86c290002ada1370d85200055ac26e1b0a4000ad683dc361480015ab07b86c290002ada1350d85200055ac26a1b0a4000ad683d4361480015ab07a86c2900029da1740d85200053ac2e81b0a4000ad683d0361480015ab07a06c2900038d55240d85200053b42881b0a4000a75851036148001c6aa8206c2900029da1730d85200053ac2e61b0a4000ab684cc3614800156b09986c2900131d18575985200061f3a6cb30a4000c5e73d96614800187ce832cc290003179cc65985200061fb2ae930a4000c3c655d26148009968c2ba4c2900030f9d764985200061ebaec930a4000c9e73d92614800187cea324c2900030f5d464985200064f398c930a4000c5f655ce61480018b8cab9cc29000327d917
  | 18 => 0x80011ef02baac6900123d2057558d200043f438eab1a40028be87dd1634800187eebba2c6900030f1d77458d200061fc2ee8b1a4000c3c85dd163480010ff0aba2c69000e1f2157458d200046fc1ae8b1a40008f7815d163480091e902ba2c6900022fa1c7458d200061fba8e8b1a4000c3c751d163480010fd0faa2c69000e1f21f5458d200061fba6a8b1a4002c3c74d5163481178e8e3aa2c6900021fa1d5458d200043e43aa8b1a4000c3f745516348005878e8aa2c6902331d1c55458d200062fbaee6b1a4000c5c75dcd634800193ee9b9ac690003271d37358d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200066bb9ee2b1a4000c7754dc563480018eaa9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000cf071dc163480018bcedb28c690002976136518d200046ec3cca31a4000a5e85994634800153d09328c690002a76126518d200056b40cca31a4000ad58199463480011bf0eb28c690002a7e116518d200054e422ca31a4000ad78159463480015a902b28c69000297a186518d200062f3b0ca31a4000a5d84194634800193cedb20c69000387d976418d200070e32ec831a4000e1f85d906348001c390bb20c6900023761e6418d200052f42cc831a4000a5d85990634800153d09320c690002b5a066418d200056ac0cc831a40008df8759063480014bf0ab20c690002972156418d200056bc0ac831a4000ad48159063480014bd0a320c690002976146418d200054f430c831a4000c9e761906348001c3eca320c690003871946418d200070f428c831a4000e1d8519063480014bd0daa0c6900029721b5418d200062f3b6a831a4000e1f64d506348001c38c9aa0c69000297a195418d200052e432a831a4000c5e765506348001c3ec8aa0c690003871915418d200043f436ea9924000c3c64dd532481138b8c7baa649022a1fa1f654c92044c3e43eca9924000c3c74d953248001c9865b2a64900022fa1b744c9200061fb2ee89924000c3c65dd1324810f938c7ba264902222fa1f644c92043c5e43ec89924000c3f75d913248001878ebb22649000317dd7634c9200062e3aec69924000c9f74d8d3248001938e9b1a649000336d8c704c9200061fba2a9b0a4002c3c7455361480071ef0ea8ec290002ada1051d85200055ac20a3b0a4000ad68314761480015ab0628ec2900029da1741d85200053ac2e83b0a4000e3554d0761480051ef0ea0ec2900038d55141d85200053b42883b0a4000a758510761480015ad0620ec290002b560c41d85200053b42863b0a4000a75850c7614800156d0818ec290002ad61031d85200053ac26cbb0a4000ab684997614800156b0932ec290002b5a0e65d85200056ac1ccbb
  | 19 => 0xe37e1d53d8d200052f42e87b1a4000a5d85d0f6348001c3aa9a1ec69000a37e1d43d8d200164f3a287b1a4000e1d5450f63480014bb09b2ec690002a7a1265d8d200054ec24cbb1a4000ad68199763480015ab0332ec690002a7e1165d8d200054e422cbb1a4000ad78159763480015a902b2ec6900029761065d8d200070fb2ec9b1a4000e1c65d936348001c3f0bb26c6900038721764d8d200052f42cc9b1a4000a5d8599363480015ad03326c690002b560664d8d200052fc2ac9b1a4000a5c8559363480015af02b26c690002b520564d8d200052f428c9b1a4000a5d851936348001c3eca326c6900038719464d8d200070f428c9b1a4000e1d8519363480014bd0daa6c6900029721b54d8d204b62f3b6a9b1a4000e1f64d536348001c38c9aa6c69000297a1954d8d200052e432a9b1a4095c5e765536348001c3ec8aa6c6900038719154d8d200054f424ebb1a4000a9d849d763480018baea3aec690002b3a0b74d8d2000566c16e9b1a4000a5e859d363480014bb0b3a6c69000327dd274d8d200052f428e9b1a4000a5d851d36348001c3ea92a6c69000387e1154d8d200070fba2a9b1a4000e1c7455363480014bd0bb96c6900029761772d8d200054f426e5b1a4000a9d84dcb634800153d09a96c690002a761352d8d2000727a94a5b1a4000a5e85d0b63480014bb0ba16c6900038755242d8d200046f43885b1a40168dd8710b63480014bd0a216c6900029761442d8d200070eaa085b1a4000a5e85dc763480014bb0bb8ec69000297a1671d8d200052ec2ce3b1a4000a9e849c7634800153b0938ec690002b360871d8d200046f438a3b1a40008dd87147634800153d0828ec690002a761051d8d200052f42e83b1a4000a5d85d076348001c3aa9a0ec6900038755141d8d200046f43883b1a40008dd8710763480014bd0a20ec6900029761441d8d200052fc2ae1b1a4000a5c855c3634800153f08b86c690002a721170d8d200046f43ea1b1a40008dd87d43634800153d09a86c690002a761350d8d200072da84a1b1a40008de87d0363480011bb0fa06c69000297a1740d8d200052ec2e81b1a4000e1d5490363480014bd0a206c6900029761440d8d200070eaa081b1a4000c5c63dd563480010fd0fb2ac6900030f1d36558d200043f438cab1a4000c3c74195634800187ecbba2c6900030f1977458d200064e31ee8b1a40008be87d91634800187eebb22c6900030f1d76458d200045f438c8b1a4000c3f751916348001878ea322c6900031dd977158d200063a32ee2b1a4000cb764dc56348001968c9b8ac6900033518f7158d200063bb28e2b1a4000c74651c5634800196ec838ac6900032d1907158d200066a318e2b1a400387e87dd563480010fb09baac6900022fe117558d200145e422eab1a40008df835d5634
  | 20 => 0x1eba0e9b2a4000a3e849cf654800147b0939eca90003175cc73d95200043f43e87b2a400087d87d0f654800187ee9a1eca900030fdd143d95200043f43887b2a400087d8710f6548001c3a8621eca9011e9ea0372d95200043f43e85b2a400087d87d0b65480010fd0e216ca900621f61c42d95200052f41885b2a4000a5d8310b6548001c5a84216ca900021fa1c32d95200c43ec3865b2a4000a3e840cb654800147b08196ca900028fa1271d95200051ec24e3b2a4000a5e839c765480014bb0738eca9027a9ba0871d952000536c10e3b2a400087e87d0765480010fb0fa0eca900030fdd341d95200061fba283b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4047a6e82dc365480010fd0fa06ca900021f61f40d95200052f41e81b2a4000a5d83d0365480010fd0e206ca900621f61c40d95200043f43e61b2a400087d87cc3654800147d09986ca900028f61330d95200051f436ebb224000c3e76dd7644800147d0c3aec8900030f9d875d91200061f3b6cbb2240008bd87997644800147d0b32ec890002a7a0e65d91200054ec1ccbb224000ab681997644800156b0332ec8900022fe1d65d91200054fc1acbb224000a9c83597644800156f02b2ec890002ad20565d91200051f430cbb224000c3e76197644800147d0b31ec8900028f61663d91200055b40cc7b224000ab58198f644800187ce5baec8900030f1cb75d91200061f386ebb224000c3c70dd7644800147d0b3aec8900030f5d475d91204ed57410ebb224000aad821d7644800147d0e3aec8900030fa1c75d912000717410ebb224000e2d821d7644800187eebb9ec890272aba0b73d912000556c16e7b224000a3e859cf644800147b0b39ec89000327dce73d91200051fc2ae7b224000a3c855cf644800187eeab9ec89000387d4e53d91200045f438a7b2240008bd8714f644809557501b96c8900022fa1f52d91200045ec3ea5b224000e2f5294b644800117d0e196c89005e2f61c32d91200051f42865b224000a3d850cb644800187eebb8ec8900028fa1671d91200051ec2ce3b224000a9e839c7644800153b0738ec8900028fe1571d91200051e42ae3b224000c3f755c764480bb55d0438ec890002ab60871d91200045f438a3b2240008bd87147644800153d0628ec890002a760c51d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d912025557416e1b2240008be87d43644800117b0fa86c890002a7a0f50d91200054ec1ea1b224000e3b50943644800117d0f986c8900022f61f30d91200051f42e61b224000a3d85cc3644800193887ba6c6900023b60b74d8d200061fba2a9b1a4002c3c7455363480018baeba9ec6900
  | 21 => 0x87550624c0010fb0eaa0c4980030fdd154189300161e3a2a83126000c3f74553614c005878e8aa6c2980021fe1572d853001c3e42ae5b0a60008bf845cb614c00517908b96c29810717d8d751853020e4fb1ae830a60008f787584614c0015c904b08c298207171db754c5300052ec28c498a600c8de861c1314c001ab6ea382629800e1fa1476c85300043ec28ed90a60048dc839da214c00199ae6314429800e1fa1476485300043ec28ec90a600087f855d8214c0070f90abb042980022fe1176085300145e422ec10a60048f8865c0214c0099e0c2b8042981d3179d9758c1300052ec28c518260018dc865c6304c0839a8c2b8c609800b0f9d154d8f200061eba2a9b1e400387e87dd563c80010fb09baac7900021fa1c7558f200051ec20eab1e400087f855d163c80070f90aba2c7900021fa1f5458f2001c3e43ea8b1e400087e8755163c80010f90eaa2c79000b0f9d15458f200061eba2a8b1e40038dc8754d63c80051b90ea1ac79000b271d14358f200070eaa286b1e4000acc8250d63c800587ce8aa2c3900030f5d154587200047bc3ac230e400387e859da31c80010fb0b3b4639000a2fa12768c7200045ec24ed18e400087f855d931c80070f90abb2639001237a1f634c7203e636bb2eb90e4000d69759c321c80099e4c2b80439000a2fa1375d8e200045ec26ebb1c400087d879d763880070ff0ebaec7100021fe1175d8e2001c3f42ee9b1c400087d85dd3638800117b0f3a6c7100030f9d674d8e200061ebace9b1c40028bf875d3638800187ceaba6c7100030f5d574d8e200061f42ae9b1c4000c3d855d363880070ff0faa6c7100021f61f54d8e200161f3a6a9b1c4000c3d74d5363880010ff0eaa6c7100021f61d54d8e200161f3a2a9b1c4000c3d7455363880051bf0ea1ec71000b279d143d8e200070eaa287b1c4000cae745cb638800587ce8aa2c7100030f5d15458e200043ec26eab0c4000a3d841d561880010ff0aba2c31000e1f21574586200043f43ea8b0c400387c87d5161880010fd0eaa2c3100021f21d54586200161f3a2a8b0c4000c3d7455161880011ef0eb08c3100021fe15768c62001c3e42aed18c400087f855d931880070f90abb263100eb780867088620004f2c3ec210c4000be280d842188075bc020b8043100ea3be1d61c82201d67338ac3904400087e86dd365480070ff0fb26ca900030f5d364d95200043ec3cc9b2a4000a5e8399365480014bb07326ca900029da0664d95200053ac0cc9b2a400087f8759365480014bf06b26ca900029720d64d95200053bc0ac9b2a4000a748159365480310fb0e326ca900030f5d064d95200061ec38c9b2a4000a3e8498f654800147b0931eca900029da0663d95200053ac0cc7b2a400087d879d3654800187f08ba6ca900021fa1c74d9520006
  | 22 => 0x212cb180021f61c42596300061eba084b2c6074a5e83109658c0014bb06212cb180031ddc671596300052fc1ae2b2c6074a5c835c5658c00147d0838acb180028f61071596303a52f418e2b2c6000a5d831c5658c0010fd0fa0acb180021f61f41596300061eba682b2c6000c3d74505658c0010fd0e20acb180021f61c41596303a52f41882b2c6000a5d83105658c0410fd0fa02cb180021f61f40596303a52f41e80b2c6000a5d83d01658c00187ae9202cb180021fa1c40596303a43ec3880b2c6000c3d74101658c00147b0932ec5180030f9d265d8a300061f3a2cbb146000c3e655d3628c00187acaba6c5180028f6126598a3000557426c53146002c3e74552628c00187ae8aa4c5180038b5504298a3000566c18853146000a3d84995628c00187ee8aa2c51800b0f1d15458a300164f3a286b146000e1d5450d628c00159904a1ac518003a350f4258a3000716aa084b146000acd83109628c13fd1c86212c51800e1fa177158a300043ec2ee2b14600087d87994628c00147b09328c5180021fe1d6518a3000477c3ac431460198df8758a328c001c9acab14651806e37e19708ca30004afc2ae1194600099f845c2328c00147b0932ec3180028f61265986300051ec24cab0c6000c3f74551618c005878e8aa2c31800b279d143586300070eaa286b0c600387e85dc9618c0010fb0bb92c31800a2fa1372586300045ec26e4b0c6000ccc32dc9618c0070ff0cba8c3180021f61e65186300051ec24ca30c6000c3e74994618c0010ff0eb28c3180030f9d165186300061f32ae830c6000c3d655d0618c0018dccb390c3180031b59672186300063732ae430c6000c6d655c8618c0011ef0eb08c31800257616728c6300072ab2ac318c60408df865c2318c0012bf0ab84631800267e11708c63001c3f42eed90c600087d85ddb218c00517d09bb643180022f61376c863001c3f42ced90c600087d859db218c00517d093b643180022f61276c863001c3f42aed90c600087f865d7218c0010ff0eb2e43180021f61d65c863000666b9cc590c600387e859da218c0010fb0b3b4431800e1fa1576886300043fc32eb10c600087f87596218c0010fb0eb2c43180030f9d165886303a62f39acb10c6000c3e655d2218c00187acaba443180031799573886300062eb2ae710c600387e851d9218c0010fb0a3b24318012b9205624863001c3f42cec10c600087d859d8218c0091f30d38043180031e59670086300063cb2ae010c60019d8835c0218c00587ce8aa6c4980030f5d154d89300043fc2ae3b12600387c855c7624c0011df0eb10c498002b920562189300051ec24ea312600387f875d4624c0010ff08ba8c49800317cc575189300062e182ea312600387e85dd0624c0010fb0bba0c49800e1fe1f54189300043ec3ea8312600087f
  | 23 => 0x58d210066c190e0b1a42048df8758e32484015b100b1c64909f31d9d975c85210161f3a2a9b024200c3d7455360484010ff0ab9ec09080e1f21573d81210047dc3ac03024200ad883580604840147b093a8c0908021fe11751812101c3f42ee8302420087d85dd060484070ff0faa0c0908021f61f54181210043fc3aa8302420087d87550604840187ee8aa0c09080b0f1d1541812101c3f43eeab18420087d84dd563085030fd0e3aac6108028f6107558c210043fc2ae8b18420387c855d163084011d904ba2c6108021fa1f5458c2101c3e43ea8b18420087e8755163084010f90eaa2c61080b0f9d15458c210061eba2a8b1842048dc8754d63084091b90ea1ac61080b271d14358c210070eaa286b184200acc8250d63084018ed0bbb242108031d61776484210063baa6ec9084200c7554dd9210840174f0899242108030fdd154980210161e3a2a930042048f98794260084091f30f204c0108038e552409802101c3f43eeab004243c7471dd56008487ce021baac0108021f61375580210045fc22eab0042028bc845d560084011bf06baac0108063720d755802149e3a388eab004293e70101d5600840517d0fba2c0108030fdd774580210061e3aee8b004242cb471dd16008485d6021ba2c0108030fe1774580210061e42ee8b00420087f855d160084070f90aba2c01080237e0d745802100c6e41ae8b004200c3f751d16008401878ea3a2c010a4b2d1c4745802149758080e8b00420087e87d5160084070f90faa2c0108030fdd354580210161e3a6a8b004296c5c73d516008517ce021aa2c0108021fa1d54580210043e43aa8b004200c3f745516008405878e8aa2c010a57171cd545802146738082a8b0042018de87dcd60084018beebb9ac010803171d773580210064fba6e6b004200c9c74dcd60084839a8e3b9ac010907b404373580210062faa6e6b004200c5d54dcd60084018beea39ac010803171d473580210064fba0e6b004200c9c741cd60084819a8e239ac010903b4040735802101e3c3aca0b0042048f88754160084095e102a82c01080b2e1d240580210071caa480b0042048f88750160084095e102a02c0108021fe1974596300043f43ec8b2c6000c3d74d91658c0014dd05b22cb180029b60b64596301043f43cc8b2c6000c3f74991658c0070fd0eb22cb180030fdd164596300043f438c8b2c6000c3d74191658c0414bf0cb9acb18003475d143596300070f32286b2c600087d879d1658c00187ee93a2cb181d297a0e74596300052ec1ce8b2c6000c3f845d1658c00187e86ba2cb180030f50d74596300043f438e8b2c6000c3d741d1658c00147d09b92cb180028f613725963000637b94e4b2c6000a5f835c9658c0e94b906b92cb180021fa1f42596300043ec3e84b2c6000c3d74909658c0010fd0e
  | 24 => 0xc4200acf825d1638840159904ba2c71080297a147458e210052ec28e8b1c4200c9d741d163885194bb0b2a2c71080387d525458e210070fc22a8b1c4200e1e745516388401c3ae8aa2c710a3387d055458e214670ea0aa8b1c428ba5e8515163884014bf0ab92c710802972157258e210054fc22e4b1c4200a9c845c963884015b700b92c710802b62017258e210054f426a4b1c4200a9d84d4963884095ad03a92c710802b56075258e2100727a94a4b1c4200a5e85d0963884014bb0ba12c710812b5a074258e210056ac0e84b1c4200e1d5490963884511bd0e212c7108023761c4258e210052f42884b1c4200a5d851096388401c3aa8212c71080297a177058e210052ec2ee0b1c4200a9e84dc1638840153b09b82c71080297a167058e210052ec2ce0b1c4200acf825c163884011bd0fa82c7108023761f5058e210054f426a0b1c4200a9d84d4163884011bd0fa02c7108023761f4058e210052f42e80b1c4200a5d85d016388401c3aa9202c71080297a144058e210052ec2880b1c4200e1d5410163884095ad02202c710802b56044058e210043ec36ea9944200c3e64dd532885138bcc7baa6510a261fa1d654ca214543e43aca9944200c3c745953288401c9864b2a65108022f61b744ca210061f32ee89944200c3d65dd1328850f93cc7ba26510a1e2fa1d644ca214445e43ac89944200c3f755913288401878eab22651080317dd5634ca210062e3aac69944200c9f7458d3288401938e8b1a65108033558f714ca210063b3aaed90c4200c75765d7218840187ee8aa4c11080b0f1d154982210061fba2a8b044202c3c7455160884070fd0bb9ac1108021f61773582210061fba2a9b1a4202c3c7455363484010ff0ab86c69080e1f21570d8d210045fc22e1b1a42028bc845c363484019b0c6382c69080e1fa1f7558d210043ec26eab1a42008bf845d5634840517908baac6908023ee017558d210047c402eab1a420087e871d5634840517d0fba2c6908030fdd77458d210061e3aee8b1a4200c3f85dd163484018790bba2c6908021fe157458d2101c3e42ae8b1a42008ef825d163484011f700ba2c6908023e2017458d210045f438e8b1a4200c3f751d16348401878ea3a2c6908021fa1f5458d2101c3e43ea8b1a4200c3f74d516348405878e9aa2c6908021fa1d5458d210043e43aa8b1a4200c3f745516348405878e8aa2c69080a3721d4358d210164e3a286b1a4200e1d5450d6348401958e9b92c6908031edd77058d210063c3aee0b1a4200cbb74dc16348401970e9b82c6908031ed537058d210063caa6e0b1a4200c7b751c163484018f0ea382c6908032edd07058d210065c3a0e0b1a4200cdb731c163484019d6e4382c6908033cdc47058d210063daa0e0b1a4200c79541c163484019b486382c6908033650c70
  | 25 => 0x40147b0932cc190a671b9ca65983210161f3a2a93064200c3d7455260c840147b0932ac1908030fdd154583210161e3a2a8b06420387e85dcd60c84010fb0bb9ac19080e1fe1975183210043ec3cca3064200a3d8499460c84010ff0eb28c1908023ee1d60183214643ec3ce8b2c4200c3f749d1658840187f08ba2cb10a2e1fa1c74596210062fb9ce6b2c4200a3e841cd658840147b0839acb108021fa1f43596210043ec3e86b2c4200c3d74d0d658840187ae8a1acb108021fa1c43596210043ec3886b2c4200e1d4310d65885474ef02b92cb108021fa1f42596210043ec3e84b2c422a87e8710965884010fb0e212cb1080297a0c42596210052ec1884b2c4200e2d4210965884094ed03992cb108029d60732596211543f43864b2c420087d870c9658840147d08192cb108028f61032596210051f426e0b2c4200a3d84dc165884014bd07b82cb108029760f70596210063db84e0b2c4200a6f825c165884af4d904b82cb108021fa1f40596210043ec3e80b2c4200a5e83d0165884014bb07a02cb108030f5d240596210043f43880b2c420087d87101658840187ae8202cb108021fa1f30596210043ec3e60b2c4200a3e84cc1658840147b09982cb108129da0430596210053ac0860b2c4200c3f759d5648854555d053aac910802ab60a75592214651ec3ceab244200e2e829d56488401c5b053aac9108030fe1d75592210061f392eab244200c3c725d5648851987ee2baac910a330f5c5755922145d1f428eab244200a3e85dcd648840147b0bb9ac9108030f5d773592210061ebaae6b244200aaf825cd648854355904b9ac9108028fa1473592210051ec28e6b244200c9d731cd6488401c3ea729ac9108022fa1c53592210045ec38a6b2442a0ab7815c9648840117d0fa92c9108022f61f525922100717a94a4b244204ab681cc9648840156b03992c9108a62fa1c32592210045ec3864b244200a3e850c9648840147b0a192c9108028fa1770592210051ec2ee0b244200a9e83dc1648840153b07b82c9108030f5d6705922100557c12e0b244256aac825c1648840147d0a382c9108028f61470592210061eba8e0b2442008be87d41648840117b0fa82c910802a7a0f50592210054ec1ea0b2442008be87cc1648840117b0f982c9108028fa1730592210051ec2e60b244204ab6810c1648840156b02182c9108032710d7458e210161f3a2a8b1c4200c3d7455163884091bd0fa9ac71080317dd75358e210246e43aa6b1c42048de87d0d63884014bd0ba1ac710802976174358e210070eaa686b1c42048dc8750d6388405938e8a1ac710803875514358e2101c3f42ee0b1c420087d85dc1638840517d09b82c7108022f6137058e210062fbaceab1c4200a9e841d5638840153b083aac71080297a167458e210052ec2ce8b1
  | 26 => 0x31b19472581310051ec20ca30262a4c5d73194604c4011f70eb00c098802ae211601813100574412c03026202c3e74550604c40187ae8aa0c09880b271d143181310070eaa2863026200adb8050c604c4010ff0ab90c09880e1f21572181310045fc22e430262028bc845c8604c40199864b90c098802b660f40181310071caa0803026200e9943100604c4015e302200c0988021fe1974597210043f43ec8b2e4200c3d74d9165c84590fd0f322cb908030fdd2645972101c3f43ac8b2e4200c3f7459165c84010fd0e322cb908030f5d064597210052f418c8b2e4200a5d8319165c840147d0831acb908028f61063597210043ec3ce8b2e4200c3f749d165c840187f08ba2cb908021fa1c74597210061eba0e8b2e4200c5f739cd65c840147d0839acb908028f61073597210043f43e86b2e420087d87d0d65c840187ae9a1acb908030f5d143597210043f43886b2e420087d8710d65c8401c3a8621acb908b21fa1f42597210043ec3e84b2e4200c3d7490965c84010fd0e212cb909f21f61c42597210061eba084b2e4200a5e8310965c84014bb06212cb908021fa1c32597213e43ec3864b2e4200a3e840c965c840147b08192cb909ea9be0971597210043f43e82b2e420087d87d0565c840187ae9a0acb908030f5d1415972100537c1282b2e4200a6c8250565c84014dd0598acb908029b60b31597210051f426e0b2e4200a3d84dc165c84014bd07b82cb908029760f70597213e537414e0b2e4262a6d829c165c84014ef02b82cb909f29d20570597210043f43e80b2e420087d87d0165c84014bd07a02cb908029760f40597210061eba480b2e4200a6e8290165c84014db05202cb908021fa1c40597210043ec3880b2e4200c3d7410165c84010fd0f982cb908021f61f30597210051f42660b2e4200a3d84cc165c84014dd04182cb908029b60830597210043ec3ccbb1e4200a3d8499763c84010ff0eb2ec7908021f61e75d8f210051ec24ebb1e420387f875d763c84010ff08baec79080e1fa1774d8f210043ec2ee9b1e42008fa80dd363c84011f301ba6c79080e1fe1f54d8f210043ec3ea9b1e420087f8755363c84010fb0eaa6c7908030fdd154d8f210161e3a2a9b1e4200a3d8499563c840187ee8aa2c79080b0f1d15458f210146e43a86b1e4202c9c7450d63c8401c3aa8a1ac79080e1fa177058f210043ec2ee0b1e42028be84dc163c840117b09b82c7908ca1f61b754cb210043f43aca996422c87c8759532c8401878e8b2a65908030f997744cb210061eb2ee8996420087d86dd531c85050fd0eb2a6390a0e1f21d654c72100666b18e498e4200a3d8499760c840187ce932ec190803179ce65d83210061f3a2cbb064200c5e7359760c840187ccaba6c1908030f59574d83210062f32ae7b064200c5d655cf60c8
  | 27 => 0xe422eab0462028be87dd1608c40187eebba2c1188030f1d774582310061fc2ee8b046200c3c85dd1608c48593e63ba2c11890b274c774582310064e186e8b04620087f855d1608c4070f90aba2c1188030fdd474582310061e3a8e8b04620087e87d51608c4070f90faa2c1188030fdd354582310161e3a6a8b04620087e87551608c4010f90eaa2c1188030fdd154582310161e3a2a8b04620087e86dd3654c4070ff0fb26ca988030f5d364d95310043ec3cc9b2a6200c3f74993654c4010ff0eb26ca988030fdd164d953100537c12c9b2a6200a6c82593654c4014f700b26ca988029e20164d95311743ec38c9b2a6200c3d74193654c5034b90ca1eca9880347dd143d95310070e32287b2a6200c3f43dd3654c40187a87ba6ca988021f61e74d95310061fba4e9b2a6200c3f845d3654c4010fd0e3a6ca988030f5d074d95314152f418e9b2a6281a5d831d3654c5054bd07b96ca98a069760f72d95310051fc22e5b2a6200a3c845cb654c4018dae4396ca988021fa1f42d95310043ec3e85b2a6200c3f7490b654c4010fd0e216ca988021f61c42d95310061fba085b2a6282a5e8310b654c4014bb06216ca98a0a1fa1f41d95310043ec3e83b2a6200c3f74d07654c40187ee8a0eca988028fe1170d95310051e422e1b2a6200a5f835c3654c5054b906b86ca98a0a97a0c70d953140d2ec18e1b2a620087e87d03654c4010fb0fa06ca98a0a97a0f40d95310052ec1e81b2a6200c3f74903654c4010fd0e206ca988021f61c40d95310061fba081b2a6200a3d84197624c5498bae632ec49880b0f9d154d89310061eba2a9b126202c9c7450f624c401c3aa8a1ec498802b320943d893100746a1e85b126200e2d5410b624c40159b06216c498a97a390c42d893101c3f42ce1b12620087d859c3624c40147b0832cc4988021fa1f65589310061e3a6cab12620087e87195624c40147b0832ac4988030f1d065589310061fb2ee8b126200c3c65dd1624c4018f6cbb82c4988031e19770589310063db28e0b126200c78651c1624c40147b08328c4988023be1d621893100556422c43126200ae880588624c40587ce8aa0c4988030f5d1541893100716aa0843126200acd83108624c4010ff0ab80c49880e1f21570189310045fc22e031262028bc845c0624c5038bcedb2c64988963761f628c93100727b2ec519262408dc865c2324c4012bf0ab84649880267e11708c9310051ec20cbb026202c3e74553604c40187ae8aa6c09880e1fa1672d81310043ec2ce5b026200e3954103604c40147b0832cc09880e1fa1b755813140c3e436eab02620087e87d95604c401878e9b2ac0988021fa1c65581310051ec20cab026200c3c74195604c40187ecbba2c0988030f197745813100637b2ee4b026200c6c65dc9604c4018deca392c09880
  | 28 => 0x5dc7644c80147d0b38ec8990028f61671d913243d4f41ce3b226400a9d839c7644c80147f0ab8ec8990028f21571d91320061fbaae3b2264008be87147644c80117b0e28ec89921ea7a0c51d91320054ec18a3b226400a3e859c3644c80147b0b386c8990030fdd670d91320051fc2ae1b226400a3c855c3644c80153f06b86c89921ea720d70d91320061fba8e1b2264008be87d43644c80117b0fa86c89921ea7a0f50d91320054ec1ea1b226489e4f62d96324c80187ee8aa6c29900b0f1d154d85320164e3a287b0a6400e1d5450f614c8070fd0b386c2990021f61670d85320145f424e1b0a64008bd849c3614c80187ce9b2cc2990030f9d065985320061fb2ae930a6400c3c655d2614c80187cebb24c2990030f5d764985320061f3a8c930a6400c3d75192614c8010fd0fb2ac2990030f1d365585320043f438cab0a6400c3c74195614c80187ecbba2c2990030f19774585320045f43ec8b0a6400c3f75d91614c801878ebb22c2990022fa1c64585320061fba8c8b0a6400c3c75191614c94b95ee4322c2990031ed9770585320063c32ee0b0a6400cbb64dc1614c801970c9b82c2990031ed9470585320063c328e0b0a6400cbb641c1614c801970c8382c2990023de1d611853200578402c230a6402c3e74553604c80187ae8aa6c0990030f9d365981320061f3a0cb3026400c3f655d2604c801878caba4c0990030f9d764981320061ebaec93026400c3e75192604c80187aea324c09927f2b5c8649813201c3f436eab02648987c86dd5604c8010fd0fb2ac0990030f1d365581320043f438cab026400c3c74195604c80517d0dba2c09921e2f21b74581320061fb2ee8b026400c3c65dd1604c80117d0fb22c0990030fdd764581320061e3aec8b0264008be87191604c80187eea322c0990030f1d464581320063bb2ee2b026400c7465dc5604c80196ec9b8ac0990032d19371581320063bb28e2b026400c74651c5604c80196ec838ac0990032d19071581320047dc3ac03026400af081580604c80187ee8aa0c09900b0f1d154181320164e3a2863026400e1d5450c604c8010ff0ab88c09900e1f21571181320045fc22e230264028bc845c4604c80147b093acc51880e1fe1d7598a310043fc22eb314627cc5f315d6628c4f98ba62bacc518803170c17598a3101c3f42ee9314620087d85dd2628c4070ff0faa4c5188021f61f5498a310043fc3aa9314620087d87552628c40187ee8aa4c51880b0f1d15498a310061fba2a8b146202c3c74551628c4070fd0a382c5188021f6147058a310061fba2a93046202c3c74552608c4010ff0ab94c11880e1f21572982310045fc22e530462028bc845ca608c4070fd0fbaac1188021f613755823121e2f98eeab046243c5d31dd5608c4018b861baac1188022fe1175582310145
  | 29 => 0x8002000000200000020008002003001c00180000018002000800a0028002000800000000040008000001000200100020008000000000e00000020000000000800e00080000000004000000c0000000000000000080020020000000800a00080000018000003800000100020010000005800c00000040028000000800200000020010004005800000000000008000000800000080000018000000000a0040000000000200080000008000000000000180280000006000000000280000010000001000800c3f74551618c805878e8aa2c31900e1fa1470586320043ec28e0b0c64008f787584618c80587ce8aa4c1190030f5d154982320043fc2ae3304640387c855c6608c8070fd0fbaac1190021f61375582320062f98eeab046400c5c30dd5608c80117f08baac11900a2f21175582320145f43ee8b046400c3f75dd1608c801878ebba2c1190030fe1774582320061e42ee8b046400c9f31dd1608c80193861ba2c1190021fe15745823201c3e42ae8b046400c3f751d1608c801878ea3a2c1190021fa1f545823201c3e43ea8b046400c3f74d51608c805878e9aa2c1190021fa1d54582320043e43aa8b046400c3f74551608c805878e8aa2c1190023ee1d60182320043f436e9b2a640387f87d93654c80187ae9b26ca990021f61e64d95320043fc3ac9b2a643287d87193654c80187ae8326ca990030f61c64d953255f0f418c9b2a6400e1d83193654c801a3ee8a1eca990038719143d9532005a641287b2a6400c3f43dd3654c80187a87ba6ca990021f61e74d95320061fc22e9b2a640087e871d3654c80187ae83a6ca9922697a0c74d95320052ec18e9b2a648987e87d0b654c8010fb0fa16ca990021fa1c42d95321943ec3885b2a6489a5e8310b654c8014bb06216ca990028fa1271d95320051ec24e3b2a6489a5e839c7654c8014bb0738eca990031d5c471d95320043f43e83b2a640087d87d07654c80187ee9a0eca990030fdd141d95320043f43883b2a640087d87107654c9134bd0620eca990029760c41d95320051fc22e1b2a6400a3c845c3654c8014bf06b86ca992269720d70d95320063cb80e1b2a640087e87d03654c8010fb0fa06ca9922697a0f40d95320052ec1e81b2a6400c3f74903654c8010fd0e206ca990021f61c40d95320061fba081b2a6400a3e86dd7644c80187cedbaec8990028fa1875d91320061f3b0ebb2264aac3e76d97644c80117b0f32ec8992a68fa1665d91320045fc3acbb2264a8a3e86197644c94f87cec32ec8990c6a7a1b73d91320068fbaee7b2264a6b8e82dcf644c80187ee7baec8990030f5cf75d91320061f396ebb226400c3c72dd7644c80147d0b3aec8990030f5d475d91320051f438ebb226400c3e871d7644c90f17d0fa96c8990022f61f52d913200717a94a5b226400c3f7
  | 30 => 0x200000000000002000800200280000020002001000400000000000008001800000080000010006000000000000040000002001000a002000200000060020000000000200100080000010000000400500000028000000800c00000000030000001800000100020000006002000000000020000000000800400080100010000000800000100080000000000000600000040000006001800400280000000000000800200000040000002000000a00080060000002002000400100020020006000000200180020000002000000200000100000000000000000100040008014000000000080000000000000000000000000000000000000000080000010000001000600680000010004000000200180000010004001800600100000000004000800200000020010000000001400080120008000000800200000000040004001000600000000008002004000000100020010010001800200000000008000001001200080000070002002800000180000000000000000a000800000000000020004000000200100060000006000000000100080000000002801e000800600180000010002000000a001800000080000008000000001200280020000002001000200080000008000000000400280020020000000000200000040000000000000000080060000000000000200280000020000000800000400000008002003000000000020000000002000400000020010000002000000000080000000000000200180000010000001000200000000000000000000400000020000000000000a0000002000800200300040000000000000000080000000008002000400080000000000000000000080080000010005000200080000000006000000000180000010000002000e00080000018002000800400080100010006000000e000000000280020010004001800200000000028004000800000100000028004000000400500000000006001801a0010004001001400400000000000003000a000800200000060010000000800200180020000000000000600080020010000001001000000140000000001000000100020008000000000c0010000000000000000040000000000000400000000000004000800000600060000000000800000000020020000001002c0008006000000000000020018004000800000180000028004000000c00000020008000002000400000000000000000000000100000000002000000e0000000000800000080000008002000000000100040010002002000000200000000000000000200200000018006000000000000000000008000800c0000000007800c0008004003800c001000000080080000006000800000000000000006000000000080000000000000800200680000000000000800a001000e00000040018002000000000
  | 31 => 0x80000000000000000180040030000000000000100000008004000002a00180060000000000800c0000004000000200000080000004001000c0000008000802a0000000002800a001001400200000008000000000400000080000004003800400180000008004000000c000000200000020010000001800000000160000000001000e0008000005800e000000600080000000006002000000080000018000001000200400000008006000000000300000018000000000000200060008000000800a004800000080000018000000000000400080020000000000000000020000006001000400000140010000000001000000000040004000000e0018004000000800200060000002003800e0000002000800c001000000100040028000005800200200000010004000000200000080000004000800000100040068000001000a001000e000800800300000000000001800200100020000008000800200100080008002000000200180000018000002800600000020000000001000000080000000000000801e0000002001800a0020002000000e000000200000000008000000800800380100000004000000200100120020002000000000480000010002000000000000000000000000000600080040000000001800200000000040016000000600080040000000002800a00200000008008001000000180000008000000000400000000000002003800000080000038002000800800000000000004000800000300000000000000800600000000000008000800000080000008000000800000100000000002000000400000020000004000800c0000000001802400000040018000000000c0020000001000200000040000000002800000180020008002006000200080060008002000000400000080000000001000000000000028000001000a000000e0000006000000400200040008002000000000180000008000000000400000000000000000800e0018000000800200000000010000000800400000000050012000001400000000010000000000000200040018000000000200000020020006003800000180000010000000000000000020000002000000000000000000000000000000000000020000000800000000000008000000000200000040000000001000400a80160008008001800000000000008008000800200000000008000001000000100040000000000000800200020020006000001a0008000000000200000020028006000000000000020000000000000200000000000000000001a000000000280020008002001000200300020008000000000000080020010002000800200000040000002000000600000000028002000801c000000a00080160000000000800c0000000001000000000000000000000000600100
  | 32 => 0x66e000055b26e400000009ab00000001bcc79a3264e6f000081d153000000f40001018000000000000008980000000000000034e40004078000000000000000003e6438200003540000d5e3d3000000005e030c8000000000000000123348bf00000d6830f0d3f000000029ac00012dc00001c0000062000008d000000007a0323ca23000000031a0be5239036704400000000822000000000000000314ce1258c00025bc0001f780d700000003fbc9061e74ffd000000000000002100000000000000000000000000000000021703250b10cc200008d109d00000000db33b3800000003ff33000003ea4563005c000000000000000000000dc90000eaa1e9c0000000c130000000000044837bc000000000000000001118462326c000000009802505060a00e590f880003c68782000000010240000000bfd3c94b1c3cc000037140003f100003e10e6800001d100000000000000000000000005d200000000800a1b00008090000000000000000000000320c9024bc0001ddc0002be450e1344000000043b00000001c387d7000057233b8bd9000000009108e200000001a54edc1a181200000fce14e00003d0ce1423ec000000000017dcbd300000000000000260094f0000c9200000000000000000000005100001abc00000000003388c6f00000002d7461233781493c2c00000005860000c6c1368fa418a455824540003018000000000000003d01774000000000032ac0003cd4000000000000000002a040002fd00000000000392800022740000000000000000000000001d9ccd900000000c6c000000025700006ed150400009f40000f800000000000158000002e9024000087628e400000000002e200000000d4a0bd46b80d4c6590000000187ccc400000000804000000000000000003c14000000000000007cc152c626241057500005ba00000000000e8f00000000000000000000038c089424acb891f147912a2ce810000606000000000000000000000296c0000000000000000000000003630000000029200000000000a6f0000d3500000002b7000000000000000000000000000000001c1000000000000000e7832e493200000000000000000000008ac000000074500000002de800000008fd07a400000000001a70aff00002d23b60d59000000000000002bf4000000000000000000002002800000180000008002000000200000000010000000800200100080008000000000000000020018002000000400500020000002001000000000080000000000000400080020000000000000200080000000000000000200080000000002001000000000060000000001000000080040000000001800200200100008008000000200100000000016000000000000020008002000800000400000000008000000000180000
  | 33 => 0xe000000a5a0000000001450f372c00000003f20000aaf0000000000000000000000000f281dcc5af000000000009d30238000000025633404e100006f50000e2d31100000000239000000035e44560000d041d2800036fcde11b5472600004c23f44e40380c000000000006b000038144c800000b3000000000000000000467000016607b824530fc00018e8449000000019087f207309db076063117280f90000000327c00004f4faf3b0cf1e000000000006cd01104bb00000000000000000000000000001f88000000000030608cd000072720500000c80d97084000014cc13e24c4851127815d1acc000335c0003bc8b3005600000ee4c4b170043505308f133242b739ac0000000e2110200000ea4cb70718000000000000000001ad4000000056f2b480002c200000000000008400000005ed2a1ca173604f2d0000ec8116c00019e0e7c00000003ba8f7b33680001ac000000000000000dea0b783f70000000236c4ed1468000000000007348f5000000000008ef24f45f900000000d2000000005170000000000000000000001efc000188c3d50000d85000000000000001d5c23319ecdc30000d0900000000f04000169000023a00000d98000000025f0000000000000000000002eeceeb0d0073840389392b840591bc0d5a3e680000808cfa0000000000000000000002680fdb212c1a53bb0794000000018e43aa00000003da000000003850000567374400008f4aaa00006f600001f82298ea70000b3120d800003bc000000000000000002158000000000024b400000000001ea090700000000000000000004700000000cdc000000000031c40000000000000000000000000000c5a0000a320000000000000000000003cac0002294b6a00008111dd80001750cbc27042c10000000000000037a4c9d14540003b24000000000000002b131c0a1c3c5c0000000ac1000000021f4000282c7860a0c7c31064a8610c80000000e0a00000000000e6c0d7455f27e4c2200000000b58000000000038f40000db400009e0e5f1bb8000000038400000000000c4f2bd800030b000038d0000404475300000003ba0ff13504000000049d19d03690000000000000000000000000000000097a27200003cfc0002ff8aa20a08baf0d0c67d05b838a288800039140000000669250ca111b880001670aa52ac84fc0c249b73538f65164043a12a0a470000aa60000b6b2c1400011d08230ee80001b040000000000223800008f06ec000000000009da000011f0000000000000036100003b1498e00000000000de6104c000000000000001ec3680003000026a32d400000000002724e5c000087a40180000000e53000087f11cc2ef2b28000000100100000000000000000000000000000000beb278c000000000027140000000000000007120000000
  | 34 => 0x2c0000000000001e80000000cce0000000191000000000000000000000031c1d444ac000000024400f2081446c310478a29f000000000000e440000000000384074e000000000000000000e272f2886300000000000000000064f000000000000001f68dc7388d000000000000004833430dc8000027703700000b8c455000000018f0dff000000030c013f10548b62358ed322d0e5500009580f2461418e0c33000093000005c900000000000e5800002bb2120000000063600000000000000000095e0000bec1c6895c2324ff200009fd2e0c0000000000000000000000000000000000000000000002d440000000000000030b3f70000185c38726c40000000dfa386800035800000000aba00007c100002f22c3ce0100000000000316000000000000003c1000000000000000e20000025025080000000664000000024f096b2bc87f70000b66333c000000040b000000000007ab000000000000001620000000000022a4000000000000000000000bb1000042f11480000000cba0000000000000000002f3000047f1b7099538240000000000000072c000000000000000144985087400000000000000bd73df00000000af329440002378d7f0000c6a1688000000000000000000000d53000068900008eb1cecc4c1fe0a6e0ad8e44000045400007ff00000c017cc0000000000000018f02d4000054092c000000001741c23040f50017cc0801e090e0000000161c4ea370819c16504b1000000000000002a3c9af045c0002f20da50000053038c000000078700000000000000000000000000000000f6d04888420000000205c38b000096c08980000000000043cc7500000000000600000000000000af000000000000000000f19000000000007071c300000000000000000000007a90fb0c2600000001fbc00000000000000d9800000000000ad000000000000000000000000006b100001140000000401c4c500008ff00000e6012892600740000000000329800000000000000000000000020600003b5400030bcb740000a2e294064601200003770ea6193400034ac000330c00000006ab0ae800000000000000f3b0a8800000000002f548b72224e8b000000000009623e0400022100000000000000000012c8548139cee336b8000000073a00000000000000000029411f4a240000000000000000000000000d3600000131e20d3100000000000da90000e9000000951d00000181c00000000000000000000032f34e000012a40000b8835e257cb1f36bc17218684b00000bae00006600da8000331c00005e00002f108b9000000028087850000000346c00000002710000e3a0000e1900000001c8400002a800000003e701980000000e79173c00021bcaa70ef0d0e23e00000a2cde83890abe2de44f3000004600000a10000b112450
  | 35 => 0x26cc00000000000000fad26b85243e942d400000002194fbe22f8c42000066a000000006ac71e000000000000003f900002dc0225000055100007bb3ed0e4634a453a00000000000000219000027c03df00004ee00000e50000000000000000005d03518f730000000000000000007100000ef516c894c2b1c0000000000000000000003fb000002b2b500002098f8c000000004f00000000a0d23648952d8449a3b9823a0a14428229c0000000867349084a37c4aa90000c3d3fccabd00005d6000089c240c8c5000057c0000554222037531401fb3de0ab400006ae3d0444700000002b1400036f895a0000f6e36c400000006763bdc8a200000000000000000007200c46fa34709903658e7e37dc00035d40001b480002eb00000000000052c7d63af0000244cdc40000c1d171415a0100892408000a00000000000b4b22b0c8a32b8000202ccb600000000000af53d1465b17c8add17c4d3e0000bb90000255000000026580ab0ae46eb00000000964ed000000000000b292d306d30000000000000000000000000ad6055800000000001078000000006b2ed84500000f8900009a4029c19800000000000000076cc28000000037901be00006350fac00000000000000000000000000b009e00d40000000c732d60c47000000026e80001390000000000000000000000ad500006a8000000013340000000000208047517d8bad23a47af096d01b0b6c000000101a4034dd200004d6000000000003cd000000009acb2700000002df0000131c0000000000000091f302400000000000000f2900009ef0294b861a8c0002f8800000000001ed40000000000000000000000000000a6100000000c04000320c0000fe44e53db08900000000000095400000000000000000000018d04ca00002a30000000000057711e0db5000073f1764d92000000000000000c44b911c2800000001ed00000000b9400029e40000000ca13c3c00005fc0001f846ad36e8cc819c82fd39cc5d7000000000000000000000000000000000000000000000004c27780003a543f623c00000338c030c3c0000000dc0000000020ec37a00008b0125c9380000000000000000001c304cc0bd0000f3a40a800000003390000000281c00000001ca1610b8e00000000000d9400d0532185490a3304a731dc87cb3574f160000a5f1070000408c71b000000000002eb00001b038c80000000000000051410f492435008390000028129c38900000000000a57105c00002c400000000002f9c0003a446bc21d0a95331400000000000000d6d0000b462804e7a2be01a330a8000325c0002538cec1df0000000000000002c60000c532784000373c0000000000082400003b4d1d34b4d71245c2760564000000010a0000000255898d1a6462f02b4f0900000000f942fe0000027
  | 36 => 0x358800000000000000f2200000000000b3d1a503be000000000007243ef4ad93548da811dcb01000000000003a02478000067c0000000b0700001942234b7b0000b8a0000c861dd489a0444caf3aa42fc000076900002352c240000000000000000000006e123e4103000036809a0000000000000000000000e8000006b200000000000cd8000101c2f74000000000000000001e482961c48b85000000004d4cb3000046d000000000003624094f0a0bc40002f2c0002f440002ef810e00000001584297000000000000000000979000000000000000000cfb00000bb0000b6f0000000000000000000000000000000000000000000000000000000000000002868f3400000000000000000000000000000000000000081c2a90a4c00000000000000218000020fcab700000000000000000000000000003e845730d6cf1d00003bb3820ac20000db700000001dfc000000000020c026315a850324841910038a8a0000a56000000019840000000a4621cc00000005f80000ed400000000000000000085e00000002124000000000000009cf00000000000000000000028142c300000002628000000000009340000000000176ce820abc42c00000001b38000024cec000003dd2f301de1a8000012240000000000380800000004e2000069f048ced60000f1808600000000000173014a000000000000000000ec1000000020f04be000000021b0000000000015340000000000000000019fc68537f05303a6cc6900000000000000000029d18f8ad11c340002c50101065400000001df0ae068100000000000e4c00003fc0000bfa0000b3a0f78a281408359125400000000000000000046cf74000000000007131fe40000000d4d000000000000001b58593000000000008580000000194c650000028f00009d53750a7400007e50000eb92acc00000003190000545151d004000000000009fc0eac99d0000000000082f000031000002d8117c00000000000000000000033400007f5000000000000001d203db26d4f4d13e058033cc0020000768000000015e400000000000000d9c0000000000000028d00002d9c00000000001ff80000d4800000000003df8000279cbc900001ff3fe00000c98dee056cec7086400035b092000000000000000000009729004cf22c82d009fc00028ec3e138e45ae16348552ce4d9b214c3e82b30e8d00000002eccb3700000000d2c0000000000000099400000000000d503cb8f1f2d800000b6800000009890000e36000010202e4f5d2700dac1f180000000000179400003100191d0409d00000002eac00000000002f3858c39741b22864d663d6800022b80000000000000000000000000000db4008809c000000028540001c243c401b80000000825044c0000170d1a01f085407d0000054c000000
  | 37 => 0xf3d0000a90000000000000003b300000000000000017911e8ad700009fe2ac44c9000000001d400000000000000000116082a2a6400028c4f36243401600000001b2800006a89d800001d90000000000000000000002fdc00000000000000000000000000004aa00006c72aa00002da4000000000000000000000e47000000012646450000fee371804125744c60e0c69000000b233d017b0fa4000000065c0000000264c000000000000000000000000000000001d8fd405f8647407c00000000001244000000000000000ca142c185000000013700002a200000838c5500008d4267cb9d00000cd211400000001c939982c000005bb342c00024440000000e1534c89cc000000000009e63064bba3e8000000000000000000000005b03585a7000000000000003aa0764090446b328c0000000000000050d0c2842e0000b341144213007869637acc9a000032a07207cf0c3400014d0000000000000001470000af1000020f0000b180000000000000000000000000000150004e3b88742042084600001922c48000000083416d4a600000e6a20408d0099c6a90b283a606244f12f7000000003af3c40d6932c41b600000000000000000000000004b900000001f200000000000000000003600000000000000031a0ab0000407400000000000000fec31789e01bfc00000003da0000f64000004b14647be1648000138c0000000ddb39b40003fd03441ce4bc63f800000000000000000000000000000000000000018703c03edc12f2010ee523dc1e61820000222cf9535f8a381944000064096e0000a83000000040480002ba485a00006d90000b6d3e785ab00000003c9833d2b181370000de2044801b0034118344100a13e42dc00006210000aab00000003bfc00015b8aa012b902904ac00033b40000000240000017000000093cbc0c300001ad0000000000000000000003facda1000000004300002670bfc0000000362800000000000000f69170c1b103e859f22ac30400000002d880001a98c580fcccff07cc00018cc76a3f18e1c00000000000a780a944c4184c8ea02dc00000000000000bc000000000000e630590000000048700000002c84e9f0000ecd3b080003be4000206c000000000014f4f8f13f40000000e38000000033e400000000000000000000000000000000000000064c5cb383c5a500004181bbcfcc2fe07aa0fb400000000000000000000000000000001460f003ea8d2131288030000000251811a2b940001e641e70000000124800014b852902288fc31acbd61dc0000000053f00001cb198ccac0cc100b12d012c3fd86a712708ec3dd80000000dbd3b480000ac0000021800023700001eb811900000000a680003f9c97c0c183d8000054405441f1000000000000242b8c2211f8000019c0000215caad000000
  | 38 => 0x9500004ad00000001578000142000000005a90000000000000000004a3000000000004d9000000000009f40ba000000000002960bb20000000000000006e000000000000000885323890500000000000b2b355cfd302d0000115c7813810000000082e29949253b6c0001a60808002cb282d38c7e0000d1900003130000e0c2c340000000bc700003920b4c39b20344f4000000000000000fe00000098000000045e238c0000000c5b000007b00004f00000be41b94000000000000000003334b2e0000a5937d40002f400001af463d000000000003882a34a2d2d4827500002e92ed0ed129b447c119800022581e2186c23205dc649217ccaa069cbff02d8000275c0000d9477a00009d01b24c7f1cf4000240000000001d300000000000e2900000422bbc00003cc0002e34c7b00000000000f8e29a46be2308000092c0000000ada03c400019f800000008b100000000000000000000000000000000000000000006ec2ff0000000000094400000001f4cd5535b8229000000000009a70000f420000000156400000000000000000367415f0000000204cd2800003cf11a000000000c92520a270000d7b0000b7500000002f800003de4c010000000000000000004402e1070809b843e23800001ae818d2b38174000000014c40000000d8d0000cfe248c00024cccd4110461e069010513acde730e44e000000000000000225c0000000eb200000000000fe521ac270000000003b8f800000000000016a000000000000001c0c00000000000b643973d00199000000000004d43e4400000004ce1fb44810b5c0000000dce000000002248070000000000000000000000cc4109041c00000001dd0000000000005e00000002848c35339000000001e43dc00000000000000058224680003958f5f1f24000000000013a0ffc2954c8401400fc1210000000000025c0cf1000000000000000000000163c000000021a00006f2000051600007f62228bd4000000000000001a68fc70000cad00008780000000000000006dcd01000014000005e81208479134cf5200000000000000000000032fcb4a0000000023c000000000037c00f7000000817700001c2c0002a24b81408400008bc0002d540000d901062c2c00000000000bd800016e088704a410b37ec00008780003640000000000019982620fa80001340d480000000000000018580002cbc00000000000000d6b000000029c46d00000a8e0000000000018200004330000372020c00025a02ce0ca07fa0000eda40307302fa829000000000000ca80c7c00000bc78c33e06d40000000034c9723664c7c00000004008be100000000230f55000000031c8431000000026f800000000001ca4a061f087f40000000000000000000000cf031700009730c9c000020400000000000000d2c361c00000
  | 39 => 0xbace9d00000000000a7a39a40001c08000049800027a00002734b2221c0f8b3c6cb15160c0c22af000000003151d980001b6087e00000000000000000000000000000dd80000000c1e0c780000b3c000000000033308520000000000000035c000000000000000f5c0000fe800000000000000000068d09846fd00000000000000000000000008b50cf88b32cc800024a053600003c30e60000216c00000004070ee0000029042a3d9800028dc00024305e4000000017600fe22f481f0a28db6293c22c021444f00000000000000000000018a0d7d13005521c5cdca000098725f4000000000030d8000000037108dc82404d071c000000000000000000bb51a1c68c3fe40000000000000000029c87a2000000000000002310b9c3f8400000000000000c6d00000003cc4cca1f44eac3514d6117fc00035dc0003dc41dc0f480000000f63108c000000011e25949352354fcd000000000000000000d8b05b40000000f9f000026500000000000000000000000001c7000045c000000037cc02a36548ee19a055a0bb071d00008620000243000000027e80000000000390c000126c1ce2b2c6f900009dc00000001eb40000ad40000000000000000000000000000000000000000006200000000000000000000000000000026cffb299c0003b78cb010340db000043c1bf0f39000000000000000000510000000000000922c0c00000002cc2d5c0001ec00e406740e9404009a0000d13315ce94251c000000000016780002544f3721f00002c68000000000007f88c81010bee0df022a37e4000000000000007162da04bd00005c6000000000000001d5800035700000000000180c00009e40003b10000184400009610140be4f860000db00000000000000000007713c5000008300003a88c522b88000000000001a868a0000299000057d00000003e280002efc000399cd43000100900000000000ff000000000000f480000000274400000000000000f510a040000000cf00000eed3d8839600000000000000339c000006800026b0000000000000009e400000000a204290a1835009080001b30000000000000000000000000000000000007a12b3c0000000000000000033a80000000a4d3f5cac3405c0000a80000000000000000002ec056b000000000000002ad4000009400000000000df4000318400039c800006186fb000087208ec00000000000000000000000024700003fdc464136000000000003e8c52c000000000001a0000000000010150d446400000000220cde0000013225d0b9f31dc0000dccc640000000000000000006c400009862df40000dec00028509dd31387552a5c7cd000000031180001824da300c0c5106cc1f50000dfd0000000000000000000000000eba00004213a5c167107c01000008a8000000000000000000b
  | 40 => 0x21c0000c34000000033980000070000000000000000002aec56800000000000000000000000010081e7cf443f24000149434d1db04fb305850705b000009a47970000162082ca3c10b40002a4452200000002db8c763344139308c0000000d4c3b7c230000000000000000000000210420330509d934880000000fde1cd829b303400022a888c1f48000000000000000001f1c00000000000000000000000003f4b503590000000017106f01f90af40002ef00000454aa10d80f7a33a4b5b0000000000074c345c0000000f570000ebb01cc00014ac0000000f5400000dd192000000000003ef044d00003a820e07e40000212000000019f0d490f080000000ef800007500000000000000000004ec24d000000007d00378000000000011b812d1dac000000006f00000000000000202800000000003ecc0000000fda2ae4e1f00000000000000000000000005ee000000000000001a8800000000000000000000024900000001428e4f2a50dcd148051e0000c212c28b7800000003c487c4000000000000001220000000025200006da15940001ba400007540000000fac0000a1e0a4c2e700000000000000000000000007f100000001facee03f580000000000000000035d00000000a4e00000003dacafa32200000000c6611d8e2a3a58e253e50000378c0000000912268c7350000b9b34200003a30cdc00000000758ba20f5c0523afc0003f0c4d700003a122bc1c400100000000b1e0ca40230000f590fc025400d8d151bd0a9e38f8e350e68d56290c39d0eb400000003bd000000016e40000000922000082d0000eee0538000299000000003330000f963bcc00000008cc1d18efb1f7043600004b300000000000f472cec000000000000000000000cbd013c000000051c0ad0b480000a6a24f800015188e70000b760d1c00000000000e780002b783c600006a5000032e00005e600000000000000000068000000000de000012980902a308281b441e3000000000002ad000000009280000000eaf000000017446e8000000000000000c1c0001adc00038c4b7f23d0000000000030906f8000000000000002cf000000000000000847109c8c10a100bc1958c871b780000000a5e0000be923d835c00000000000f723428d440f50a490000aae083419700005d32a0814200000000000d3d0000000000013b0000d540000c85100c00004a8000000000039fc0000474fdd2bb4fd9000000000000000000adb0000b2437d066d22e0c590ec4e2f3a383a50f90a4a0be0e332e1c37028e808404a000000009c3000000005048e5291400009b48df0050000000000000000000000000000000000000000000ee40000000000000024dc000000000030f899928d88ad39845c70b083dc3c8000027a8f7d000059a000000007c800000000002
  | 41 => 0x38b80003f7c2c93070000060cf9d1eb000000007740fe800000000001f749a923c8b4302fc0000000d5800000000000341000022d0000efa111044200000000cb4d5b0000154000000023000002b24b8c0000000000000000006c52d780000000000203c00000000000000d0000000000000722000000000000001f50a9f28c02ab132c0002f08866233c0000000000000000000004b500000000000000000000000000003c18000140455511bc7df0000000000000015d8ae8000000000000002ab0cfc0000c81037c000000068400000001b740003690000000081a2e9460e00000002e68000086c4700000000000000000007d800000110000be82bdc0003e9800000000000000ac400005c20000000322c000000000000000000cac000130c074358c0003a4c9e200000000000000253470100000000000c0b1000000000000000000000000f3e0000dc100000003a105130000a1f374c2f011ec00007140003878000000048d3208955100400000000000000b4100000002678000000000000000000000000000043f07d8000000094900000000000a7000000003848bf21a440000000000000000029f800032f834e00000000afc0000000b923f88c2e0000000000000000000000000ffa35bc00000000000000000000025a0000000000000000008443a18e9e226400000006f733dc00000000000000000000029800000000000ed901941a83a1cfa81f8c1a101880000000ea51720000039c0000e34e74000065419e80003620d86364400007a800030ec2df000076f03d00eb015800000000000000000000000000002a80000ae700000000000000000000000000002204000232c000000000000000000000000000065832ec0000d680003d3c000000000000000001ad092e000000000000000000000381c000000000000000000000000000081e000000000000000000000000000000000000000a6c2528f6100000000000000000000000000002df800000000003e600000000b4d1398d720c0c000010c9d20000e1833c8b72000055d18600000000000000000018fc0000000000000000000000000030000266c0003e4c000343c0002b986221c3c000000000010943fe301ceb507f0bd824740002bf00001fec7d92fc42a106e4b1300004d215c066500000003af8d25000000000000002d8c00000000000000000000000000000000000000000100300001ef0a30c370000000124c000000000000000000000000000000036b400010c06c32c087520000d053f0400007c00002b0000038980001a48953066c796000072f243c72509c85fb22f0a750000eb000000000000d7300000000000b5400000003e0c0001ff468304840000000e8524a800000000000000000000000000000000000000000058a1040c1a25140000000
  | 42 => 0xe2800000000f144b61240000000053e3bc00000000c981ca00000000f1300007b70000a0c000000000000550af00002c40000187400000000000000000000039c352c2f40000c56000000000000000000000000000000000001280000000037f0cc862d00005741afc00002b8a7f0000ba300000000ba8000340800000000000dd0000360800000000000000c652ea844e0000000000004d4088c4911c47890d7c0003174c02000084c0d180000e6400029f49b40000e1b153ca6821a800010280000000000298800000007ce0b9000000000001ee0f8813d49a600a400000002660d5400000000000000c67000000019cc00000000000000000000000000000000b840000000000000000000003b610e062c0000b2631e4ea00000dab0000f493d6cf851d808d828b000000000003d4c000000076d1e2c000000000000000003af400000000000c740583978000309c000000074900000001fc0b1b1f00000000000026487b400000000000dd514b40000000acd000000000005690000000000000000000001788bf300000001828227179c00000001ae0000000000000022ecbde02e0e06000000000000000000ae014d40000000000000000000000000000d3403ec0000000d780000b93000000005a014300008770e1800000e48312e40000000005a1b90b9818dc0003ae09752048762000017308280000000abf2ba81611974cb83f8c03309bcd8f000046932542950978f8d00005ad1d500000000eb734a80000000000000000028200000000a930000c9605d848f0aa806d00003580000000000000000000000000b5a226c0a91e94000000000000001d700000000000fc02ccc16500007a4000040e000000029741463bd80a0000000013a400000000000000fd20000a480c38e13000000003fc00000004db0000000165c00001241e83ec400000005bd00000000000fb50000379000000016d80000000e4d32902870000000000000000000001a209f6000012427fc00000000000000000000000000007783a9102700007a307dc1a62a6c00000000003188000000000000000003ec000016f00000000d5f0000df827dc0001f985ac0000394000000000007430c880f000000960000ab806305430000000224c99837f84a5000083500000f600000000000a1600000380000000000000003400000000000227c000000000000000000000c910000032146c00000008f3000082c00001e00000ce534bc58900000000d240003bbccc600000000000000000000018a847e2280bc31044000192800000005a63a700a613540000000be32c30217108000000000000d5898f000022e000000000009cb2140000084400021340000d8c1b400000000000380000000035a8b73000029e268800023f86573374f0318900003c34b041e6c4bf0000c04
  | 43 => 0x20000f0c0514630000000000000002fecca240580000000bf600000f5000037702f806c0000dcc39d4000000000034dc7630000918000036b0000a3524d80000494000310000000000000f98aa300000ea3e7000000000000000000000000025b400000000001ae4d4f0000000256400030a47232008c1b0000eab28000003c702a700007150b800001e0c00000000000000000019c9400cd81e1000058e00000000000000000072b00000000e8c48a2e780000000d93000058106040003f28e410000610000000026c81eb000000019780001cc42040c08eca01dc00027380d237c80001d1cea12ef400018b84f200003ca00000003da800039c088f000072a1c7c0001b98c0a3f60c800920312000027b3b9c9a10000dd7000041a00000000000000000044a000000000000000000000000000000000000000000260800013d8d3b137c00021840000000000000000000000000000434000000020f8a960000000000098800000000000000000000000000000000c4514001d4127c3d93a480a324246753c207932d940000000fa20000000000036c000000000006823ce000033d80000000de51030ad300000000000000000000000000000c503bf0000632354400000000000000a9a21e400012e030826c062b08fc1fd2f3ce5027100001ef0bed0ed08860ec8ca5020071416d075c1c18000000000000f00000c8401f10dc000000000030300000000833324cf6000004052874e5139900003b840000000000000000000000000000000000048b0d08000180800000000000000000000000000002fa0a90c17000065f0b14edd0000000000000000000000000e520e8800000000001684cd62e9000030ac0000000e4200000ac00000000000000173457f000073e2cb4bdb2ea4711087c1fa337cf9b237400000000002f6800000000002540000000013115284a400000000000bb80000ca0000000000000001660e760cfc0000000cfd294c000000000000000000000f1521d40000f200000000000000062700001d00000000000000000001af000096900000003044000000000031340002f98000000000012f0afe00010130628fe93450000000034f00006773ff80000000461000052700000000000000000000000002d10fb8000228423e1c14d0702647e81cf09161830b71000050500000002810f2319c4000349874429503050f4400000ec00028989c600002380e905963e1c00000000000000000000000000000000000000000000000009f33d1817c0000b823cc80001090000000000000002ed000000014980000000b562d9000015880000a382dd3094a2a00000000000c0f00008a300000cb00000000000000000000000000000000000000000000000000000000000000000005aa3b2c000000000000007e90000000112c061000
  | 44 => 0x41633f985ce0000000110ce110000000000000014bc9290000a840000f020000000360000000009c2252ca800000a21280c00000000000000000000000000000000000000000000027e00002c5cfd500000001cb8a0e2cfc000000093f0f8c00000001600000fcf18342e61a6c000018c00000000000000bd200000000000dd6000000040a0f4e19305561fa80001db8cdb0000a7700007322ac077e06680002e64c8c28ac68b000000000001043c900000000dbb0000000118c00023b44ba000000016c4000000000000000003c4400000003d6000000009f85c40000c3a34c00000000b2c3d5800000000000000ff5275838f307c00000000001fcc00029040001aa860436f05ec3ac40000000000000000008d833b00000000304b491bc4a3d10e46a115c40001e34060249caf4301400005e85be1ecc26001e402d26f4dd83ad85a312188052e84000000000015e88270ff40000150000000000000000000000000000018b00005a00000000000000000000000000db800000002a70566000000000000000fd0afb0000223000078020dc53c0c000002a488d326a8e8300000003678c6e000000026ec9bf3180b063458f3300000000aa4000340c0000d84a98000000000000000000b800114c000acc0000000bef2b6000000000001d7400000000000ab8000000072d00000001c80e0d0000fea0930f070e5400000000002d10e991784e880ec000000000000000a4b3ee8000000000000000002f0400000008060000000000000000000001814000000000005f400000000000000000148c0003234000091c000260c0000000000240874d25dcb450000175000000000009e5033038c0000000000000000002be00000000000000000000000005f50000000178c6ac00000000000251000089e2e5c6e71e40000000003e2e98a6603540003b1854221a400011143f513f859525d8f923ad01cf00000001e60152183c6c20000000031800100000000000d6522e8d76000000000000000000000000000000000000001005000000000000002b2000000007b2000029c17a8f580b2c000000000000000a21d84000347c000003c00000000000000000000000000000000bb800000005da1d940000000fb60000000000000000000003bf82fb12002143d2800001f80000ed42061d68a7b1260ba023e8e3b000097e3ddc59b15b4b8f2a14000128851f0880000000077b0000000338000000000003f2000017d00000000f6f000000003648c70ce800028fcd120000b3e000000000000000c3090b3ee4537161400000000000f300000000000000000025900000000000000042200000000000000000054900000000000000000000000000002174e5a190cd180000000000000003e0000000000000001a9031c0000000000000000039b825d2ce095
  | 45 => 0x7b1000000000000000000000000000014440003740000000000000000000edc00004580000000000000000000000001ee4efd0000000305400000000000000000000000014a86c00000ceb0000e3c0000000000000000000000000000192c0003988000000000000009df00000150000000000000000005b709e80000000000000034c000027c0000000155cfa710481300000000199c00027ece7112ac000000000029d8000153800000000000000000000000000000002828000000000000009a50000138000000021c4000297034a00000000b207ba3354578000000000000000000efc049c00000000001e100000000000000069d0000000266800000000002d70000000000000000000000000000064e1b8ce982208b7737741a2000000000000003a8c25c233800016fc6a430e00002d7c24f39f475b000000021b40000000000000000003b00000000069359c0003eacdda0000000000000000000001c60000000000000000003eb80910000c94000013a31e0000000000000006cb2bc00002e58000000079c000000000000000000000148400000dc816360cd7c3c9c00028800000000000000000031d04de0000f2108200000000d8e17bcd3c0000625000075910ac000000000000000000000000000000000000000000fff000000038dc4530000000304800017f49ad1948000000097f15705122fe432c00009eb2ad89b80000000000000000002640000ca719ac83a000000005a40001e3800000000000000000000000011744160000fb20000dde3e08b6c1e980000000f75081c0002b90000000050c00000000000000000008b1904390000002000000001e3c0000000000000003f21b86db1194ee90000ba732d0aee0000504055400014ec000000028d021c6e000002150df80e83e404593eec1d2000000039500000000e1d00000000a982b21008e57000000000007bd147400023280000000000000080119e42c70000000000098c00004af2164a182d4c00000010263a68d0d0bdc1bf18ec36f31e8b4f000021632241bd00000002d64000271c0001f5491b0000000000000000000000000000000000000000000000000385c00003800001804000000000000000000000fc505ac000000075835e800000005fe00000000000000000000000000000000843000018400000002584000000000024ec957000087b05bc1570000000000000000000000000a9d0220fbf0000000000000000000003c38f2a0190d2000009410000ca9000000009cc00000000001424d3305340000000000001c00000000003bd00000000000000000000000001b3c5e9000045a000069e31f4000000000000000000000000000000000000000000000000000000000000678fcb0000b4711a8a10000000000000000000000000083d17f0a4413
  | 46 => 0xd111fb00003ab40000000591000000000000000000000000038e00000000000000000000000000000000000000082b00004a117c07b626040000000000159000000004fa00000002038e89000077d230c99128a40000000000239856c00000000000c9e00000000400000000000006d4dec0000dd9000007f00000000000000000000000008d70000000000098b2fd410d000000000000003dfc75f00000000e7c000000066200000000000381000000000000a82c94b2a0000000318c000000000000000000c8ce22000007d000014f154c00025a800026a073716c0e2c25e0aec027c148238418737d8318377c5a807945d50f1ceb3265c9711d3c7ee1258231000026c0f2c32422fc9601f28f5e06e8ccb1ad8eae2c74cef00000001374d8920c8f3c22440d117e8c5f000057e0888c54000000000000d40e4c0000000000000000000000000000000000000004b8fc200009ed0000000000000029486fe1cd0196000000000009670000ce82cd8000000015c25ec000000000013fc000000000027a400000000000000000000011c0000e0e00008a400000000000068000066c396c00000003b31214c481a5c3ef0000b16000000000000000918000000003a000000016740000000000303800000000003c046c8283c000351c000000000000000000000b00000000027b8f4b308000013bcb231a4c2531c0000036a85c13d9c6ea00000002c640000000000284c000000000000000000000000125048c0000000000000016cc5df00000001954000000000000000003938bb727289b61de4000103c05700000000000000089095b1b182911f9c000000024e203000000000000000000000000038ac5de17ac0003fb4c9c1b5c000000000013dc00002340000000e49000000010980000cd40000000000000000000000000000e3f0000000406455032c8e7b2598d3a3b5c000000000000000002f1400000000003508d2e0fc46191cccd9f27b000000000000000adf28f83d312388c637b400000000000000000000058b00004720000e163bc40002e500000000a333698db900000da3a28000000000029089d40000000310c000213c00039dcda20000000246400000000000001018000000026f00002c380000000000000000000000000000b8b3668000000000000000000000984000000004d829f000000000000001e783a700002cd0000000000000000000001aec00027c441400b8fd0403cd2700180000000000000057b0000000000065a23488210000b200d5c18000001da02080001b7c7db00000000000000206400027c8000000000000000002f3400000000000000000369c0001d7822800008da033c868220000000000000000b421e54000000000000000000000cf52f7cce300007190638e6500000000000e6000000
  | 47 => 0x1d2c000392c289348cd1e000068f00000000000528000036e070453900000000000000000000000002d53170b40182cb351074000106c000057800000000000000db2000000000000000000000038800030c481539200000000a093ee046016649f5382c68e0000cd300007fc20a4a2f0d14a632420901006000000001c000000000000f9728940000000f2c00003ac000000000000000f3866f00000000000000113000024e8ba834180e1000000000000000000000000084e0eb8ecf30b44cc000033800000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1a85835084218520006a1611320c8614800103d94a1f654c5200040fa6075d91314800141d941d7634c5200050d65075d85314800103e989d764c85200050765275d8f214800142d949d676c85200050b650859db21480014e296dc470485200040fa6275d92304800141d949d7638c1200050d65275d863048001435949d4618c12001c0fe6174d91650800103f985d06459420006075d18319165080018357460464594200040fe61741d1650800181d7460c42594200060b5d082505650800182d74a0a40594200040f65387597630800703e98dd154d8c200050ba4b74553630800581c875514358c200040fa6265dd132080058348755141584200040f66274994610800181d849ce65184200040f662655d0610800141d9499573184200040fe5186dd5310800103d9421d654c4200040f653865d7210800103d98995748842000507652655ce210800142d9499576884200050b652855da210800103d94e19758c0200040fa6265dd1200800141d9499773480200050d65265dc520080014359499471480200050b65265dd9200800142d94217764802000549652651c5200800146596d5071480200050e65265dd9200800143994217764802001c0f2617455163c400142c925d15458f100050725d5450d63c400703e98dd15498b1001c0fa6374553638400142e92dd154d8e1000507e5d5450f638400703e98dd15418a100050d652755db218400181f7460c42d951000607dd5839cb644400181e8755042d8d100048765285dc76344001a0d5460c42d89100058364e74553624400122d9421571d891000683551831086244001a255460442189100058364c745506244001625911d154189100058aa40745506244001a854360443189100048b65285dc46244129ac01020d70189100040fa6075d91314400141d941d7634c5100050b65075d89314400142d941d4624c5100040fe5187d97214400103e989d764c85100050765275d8f214400142d949d762c85100050b6527518b214400103e989d7648c1100050765275d8e304400142d949d7628c1100050b6527518a304400103e989d764081100050765275d8c204400142d949d762081100050b65275188204400181d7460c42594100060e5d4805cd640400181d7560c72590100050e241745516304001618905d15458c100060761d54109630400121d94a167058c1000685551811016304001a0d5460c42988100058364c74552620400122d94a1470988100068355183109620400160d931d154588100048b652851c16204001a25546044058810005896527558b210400103d989d5648c010005076527558e300400142d949d6628c0100050b6527558a300400103d94e1d65080100040f66275590200400141d949d563080100050b65275988200400142d949d56208010
  | 1 => 0x25aa21369c5129418d2498e478323f9c81e1824298c2ad1c368a28427a7c5e4702c0208048184c020c8000e020180002050100010010c80400060380818000501c0200018040c020a8900404010002e130003c020e0286402061a00004000483c0e02078004e030001800030003800000d0080141e96dd143d953200507a5b75dcf644c80190e82dd773d91320050764e72dd7644c80703e98dd15498a3101c0fa6374593654c40182f7420964d95310060edd080593654c40103f985d064d953100507a5b7450f654c40103f985d074d953100607dd18310b654c40181d7361065d8931006835508250f624c55b28f9850f42d8931006835518310b624c40103d981d065589310040fa6065dd1624c4014399419770589310050e650651c1624c401a0d5460c42189310040f66074195604c40103e9819774581310050b65065dc9604c40142d941947258131006075cd84194604c40148d940c972181310068c55181100604c401a9143604401813101c0fe6174d9165c840103f985d06459721006075d18319165c840103f985d07459721006075d18310965c840182d7420941597210060b5d28290165c840103d94e1d65d8f2101c0fa637455363c840143a90dd154d8f210160721d5450d63c840103e98997744cb210040fe5186dd531c840103d989d265d8321006076127399760c840141d9499573d83210060b9c98499660c840103d94e1d65183210050764c725d5648840160c925d15458e210060761d54109638840121d94a167058e2100685551811016388401435949d576c862100526650631c1634840141c975514358d210160721d5450d6348401c195450c7058d2100526650321c1634840703e98dd1541812101c0f26174551630840142c925d15458c210050725d5450d6308401a0d542094358c210050d65285dd9210840143897552405802101c0fe6174d91658c00182d74a0b64596300040fe6174191658c00141f965d143596300040fe61741d1658c00181d7460c42596300040f66274997628c001a0d5460c4298a30006835508250d628c15928f9850f4258a300068355183109628c00103d94e1d6518a300052365032dc9618c00103d989d265186300040f662655d0618c00142d9499672186300050b652655c8618c00103d94e1975c86300040f65387597218c00103d94e1975886300040f662655d2218c00141d94995738863001c0fa6374550624c00703c985d15458f200050725d5450d63c8001a0d542094358f2000507e5d5450f638800581f8755143d8e2001c0f26174551618800141d939cb75d912000583a4b74553634800181e8755042d8d200048765285dc7634800123594a1773d8520006855518310b614800162692e115418520006895508250c6148001a8543608431852000685551831086148
  | 2 => 0xe7c461382ad75d8ecd403059ed86c1028519c1f3ca818e7d41a45281d31261a6282f84c0243211189882558cdb6160032590522e899a87565024f40000068000000345745c45ac0e829402bc00b850a2400651faf13ab6541a0104d0008800406204548772b248d80247a590eac0029c20bd5919014545f800dc700d80000000c904008d2215400002b9652e301b8d0ce2300000bc00000018a5a0721400001605cde816b0b40000470000000108006c8a3f264e66658b7134a30012c0086281281a9e67801663e662a97c7129ae462ae680e968cb12800d62a6300000046ab00b6951216040901e8700000000000c00368000012001e0926315801b0a917334ecd9138d43c60229a56ec
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x22000300e96a0b75dcf644c80140653aa841286b184200a0329d542094358f20
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
  | 9 => 0x94c
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124c
  | 13 => 0x124e
  | 14 => 0x138c
  | 15 => 0x138d
  | 16 => 0x138e
  | 17 => 0x8c
  | 18 => 0x8d
  | 19 => 0x8e
  | 20 => 0x128d
  | 21 => 0x150d
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128c
  | 26 => 0x128e
  | 27 => 0x150c
  | 28 => 0x150e
  | 29 => 0x9cd
  | 30 => 0x9ce
  | 31 => 0x12cd
  | 32 => 0x12ce
  | 33 => 0x20c
  | 34 => 0x20d
  | 35 => 0x20e
  | 36 => 0x154d
  | 37 => 0xb0c
  | 38 => 0xb0d
  | 39 => 0xb0e
  | 40 => 0x140c
  | 41 => 0x140d
  | 42 => 0x140e
  | 43 => 0x154c
  | 44 => 0x154e
  | 45 => 0xb4d
  | 46 => 0xb4e
  | 47 => 0x144d
  | 48 => 0x144e
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0x15cd
  | 52 => 0x15ce
  | 53 => 0x94054
  | 54 => 0x94055
  | 55 => 0x94056
  | 56 => 0x95255
  | 57 => 0x8a
  | 58 => 0x128a
  | 59 => 0x155255
  | 60 => 0x154055
  | 61 => 0x154056
  | 62 => 0x124955
  | 63 => 0x124956
  | 64 => 0xca
  | 65 => 0x12ca
  | 66 => 0x130a
  | 67 => 0x134a
  | 68 => 0x139255
  | 69 => 0x21255
  | 70 => 0x155256
  | 71 => 0x98096
  | 72 => 0x99515
  | 73 => 0x9295
  | 74 => 0x98095
  | 75 => 0x99295
  | 76 => 0x9515
  | 77 => 0x129515
  | 78 => 0x8995
  | 79 => 0x128095
  | 80 => 0x128096
  | 81 => 0x150095
  | 82 => 0x150096
  | 83 => 0x20095
  | 84 => 0x20096
  | 85 => 0xb1515
  | 86 => 0x140095
  | 87 => 0x140096
  | 88 => 0x155515
  | 89 => 0x128995
  | 90 => 0x128996
  | 91 => 0x150995
  | 92 => 0x150996
  | 93 => 0x99555
  | 94 => 0xb0995
  | 95 => 0xb0996
  | 96 => 0x98b15
  | 97 => 0x154995
  | 98 => 0x154996
  | 99 => 0x151296
  | 100 => 0x151295
  | 101 => 0x21295
  | 102 => 0x141295
  | 103 => 0x155516
  | 104 => 0x12c9d5
  | 105 => 0x12c9d6
  | 106 => 0xb49d5
  | 107 => 0xb49d6
  | 108 => 0x1452d5
  | 109 => 0x12d455
  | 110 => 0x1452d6
  | 111 => 0x12d456
  | 112 => 0x15d2d5
  | 113 => 0x12d5d5
  | 114 => 0x15d2d6
  | 115 => 0x12d5d6
  | 116 => 0xa4c
  | 117 => 0x198c
  | 118 => 0xb0215
  | 119 => 0xb1555
  | 120 => 0x154b15
  | 121 => 0x154b16
  | 122 => 0x155416
  | 123 => 0x155415
  | 124 => 0xd4a
  | 125 => 0x15cb55
  | 126 => 0xb55d5
  | 127 => 0x15cb56
  | 128 => 0xb55d6
  | 129 => 0x17ca
  | 130 => 0x14cc
  | 131 => 0x2cc
  | 132 => 0x15ccd5
  | 133 => 0xcd5d5
  | 134 => 0x15ccd6
  | 135 => 0x160c
  | 136 => 0x40c
  | 137 => 0x164c
  | 138 => 0x44c
  | 139 => 0x1a8a
  | 140 => 0x104a
  | 141 => 0x4955
  | 142 => 0x5555
  | 143 => 0x5695
  | 144 => 0x4956
  | 145 => 0x5556
  | 146 => 0x10a
  | 147 => 0x14a
  | 148 => 0xc092
  | 149 => 0x104c
  | 150 => 0x1a8c
  | 151 => 0x100d2
  | 152 => 0x4954
  | 153 => 0x1a0a
  | 154 => 0x8996
  | 155 => 0x9416
  | 156 => 0x983d5
  | 157 => 0x99655
  | 158 => 0x99556
  | 159 => 0x40994
  | 160 => 0x141555
  | 161 => 0x1403d5
  | 162 => 0x141655
  | 163 => 0x141556
  | 164 => 0x5ca
  | 165 => 0x41414
  | 166 => 0xcc3d5
  | 167 => 0x44414
  | 168 => 0x161654
  | 169 => 0x160454
  | 170 => 0x164414
  | 171 => 0x41654
  | 172 => 0x98414
  | 173 => 0x140414
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1668
  | 6 => 4749
  | 5 => 4139
  | 4 => 221
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
  | 7 => packedAt gbK7 (67832+((h/556+packedAt gbK7 (61716+(h % 556)*11) 11) % 2002)*12) 12
  | 6 => packedAt gbK6 (248531+((h/1583+packedAt gbK6 (227952+(h % 1583)*13) 13) % 6268)*14) 14
  | 5 => packedAt gbK5 (263507+((h/1379+packedAt gbK5 (244201+(h % 1379)*14) 14) % 8794)*14) 14
  | 4 => packedAt gbK4 (16127+((h/73+packedAt gbK4 (15470+(h % 73)*9) 9) % 266)*9) 9
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff807fffffc07fffe03fffffcf3e7f19f1f1ff
  | 1 => 0xffff80fc07ff80ffffc0fffff4c791fe8e3e3f
  | 2 => 0x1ffff0007ffff03ffff078038f9e1e70fcfcc
  | 3 => 0x1fffffff8000003fffff8003f01fe07f00ff0
  | 4 => 0x1fffffffffffffc000000003ffe0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x52000b1509403144a0110caa811a270830d0d5
  | 1 => 0xa4a580a8429480a94a40d1551444907286262a
  | 2 => 0x114ad50084e95a0274ba0601a8a961a50b4b4c
  | 3 => 0x21f366ced00c08239f2ce0063e01da07d00db0
  | 4 => 0xc1fc78f3e73e6cf0060840183ff60007edb000
  | 5 => 0xf8604083003070c0183084603ffffdd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37411
namespace PEqualNP.Outside.L_meta_37411
open PEqualNP.Outside.L_meta_37411.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_160 : Interval s3Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
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
theorem bs4_4_512 : Interval s4Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 bs4_4_224))) (concat (concat (concat bs4_4_256 bs4_4_288) (concat bs4_4_320 bs4_4_352)) (concat (concat bs4_4_384 bs4_4_416) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 221 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_4128 : Interval gbAtlas 5 4128 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4139 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))))))) (concat (concat (concat (concat (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176)) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816))) (concat (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072))))) (concat (concat (concat (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)))) (concat (concat (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712)) (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840))) (concat (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 bgb_5_3968)) (concat (concat bgb_5_4000 bgb_5_4032) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128))))))))
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
theorem bgb_6_4736 : Interval gbAtlas 6 4736 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4749 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))))) (concat (concat (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))))) (concat (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)))) (concat (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))))))) (concat (concat (concat (concat (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464)) (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)))) (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))))) (concat (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)))) (concat (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)))))) (concat (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))) (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128))))) (concat (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 bgb_6_4256)) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))) (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))))))))
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1668 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888eae8eac8eae8e888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941133000 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37411.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[2,6]⟩,⟨.or,[1,3]⟩,⟨.and,[5,8]⟩,⟨.or,[4,9]⟩,⟨.or,[1,10]⟩,⟨.and,[0,8]⟩,⟨.and,[11,12]⟩,⟨.or,[3,10]⟩,⟨.and,[7,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133000 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133000 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37411

open PEqualNP.Outside.L_meta_37411 in
theorem PEqualNP.Outside.L_meta_37411 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941133000 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941133000 * 2 ^ 32 + 3941132424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
