import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36705.Model
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


end PEqualNP.Outside.L_meta_36705.Model

namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 8, 8, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_36705

namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
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
end PEqualNP.Outside.L_meta_36705
namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
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
  | 2 => 0xf80ff01ffffffffffc07e07e07fffffff223ff
  | 3 => 0xfffe01fc03fc07ff8007ff83f03f01c3ccc
  | 4 => 0xfff000001fffc0007fffff80003ffc001fc0f0
  | 5 => 0xffffffffe00000007fffffffffc000001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x48209081404484820458a28a2845249544cd55
  | 2 => 0x95452a528ca929343a05485486aacb2a9222aa
  | 3 => 0xc6a9c954d523b216deac1267b23363c0dc34cc
  | 4 => 0xe4cd8d9b1a3223a76f367b41243cf1831f40f0
  | 5 => 0x70e0e1c1c3c3c3873c79c79c720820c1bbb00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0a0a0a0a0aaaaaaa0a0a0a0a0aaaaaaa0a0a0a0a0aaaaaaa0a0a0a0a0aaaaaaa0a0a0a0a0aaaaaaa0a0a0a0a0aaaaaaa0a0a0a0a0aaaaaaa0a0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36705
namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1e52380803000022004c6213e1c79b2c0001d009d500003411c0c41223005c200220059234654264a0000a5621014000ca890a0c10410c0004100050103ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2b29082d91000014000e9f85802587260d8b0000241583078f1f1c88820016060ca89c181a96ac0a8d1d97998e1e8f8000188011a82510002a15170005000000001a0392829d098a2c8481ad0c1b23012290a70400a9aaa3a193a6aba11900000927a220a01e24949300069b8b920002090024007060831336000800c58c80040c00414083970240188b7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8e0a0240c605a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
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
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 1 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x84882808c489082016514a284a212954133615
  | 1 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36705
namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x14a293e4be06c3c8ab29867806a7b000000000000001bc59000000000a19ba0001c0000000fe1842b287000910918350983d8d29c53fe000001cf000000f80001d067095844326638ca17848256800000264478a49603488d0979463909d8250fe222000b91b84469d0b38be306328f423e1da49c9d28e2fe8954a90b3ae40481947000a34bb8f10540ccee80000001cae8571ac464851260005984c0c01d421d1e1211665d4b09523fc710b124922c5c4318504541b127a311680acfba100105602121118661c478ac064994c2a8f4861d45128512e1b4fc21e1c010c1600332a3bd229f60006193d0c132419907a401d66ed0b85d2a017c7d28440e000d49574081951e83803c780c212e2f21d8d713f3b03186aa6941a7048c1f900a8c0ed14d08084c102504243ec392673783408791d0d00014481344c9d52a00b52e7c8c88b12288bc001cb1347180a14b29e6bc2f2833fa1f4db8a547e608000e500000013a68000000699080000ec0020e0e80008380022e32cf9a94234930fa1004f2a65199df3dc58d2ba784ba26cf786914031ca12092a6324da955530a4d009db3ce9f0e907a3622552f11507c2247c88613a47c620c537c640239cd3165109d8480f6298ab26b250365001a70306d9268000004406100043a8880000000092c000000000001a09f0a2870cb0000a8970001974cc2b4f601538e0000022900038882030142160001890007887e8004940007a8003563780020851000040a0a000000b280e0400501400010060040c0000100800004000000002401000050140a0040400800044070400005815018010000b030010001a0200800000020200380101000020000000006c1700000000000044700c020000506c00020000040a07418018040180d00003000000000600c040000d0340a000120141202c0400000028020102200014000040ec03008350240601002028010480000020014050180100c0000c0a068050a03600009044000200e02012090350000b0580003c16000000000007c2807c0002c0002407014020382300825004040240100814000040000500c020000100c1e03c000140f0300701001084060b800090050143004400004020180500800000110180a00400000000000f01c0204c0000afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x5500e2803a4810521905447806e40c8e0898294c200000129000000bf0102ec4341283a48e9186e83c1144c448a1f4fa000b68000008b400000318470579fc52056d4304d07a00000031432000000000006c8cd9f5340098418bb330000000001182a4be0371100005403f2c8330d5174104000830003f6064d6a5939c5b115a481387705d2622d21e09e12a3d69a866a360420243e125148538aa2030d69b50a19f3e282c761e13da248142704c857d1ba282720003226e45c399408004e26d07386a04408c5ca0246a9093ba961a84b0b8136380000d19a80000000b8004423482a8774a2620f28f327019c9e9d611a2c0519810003700020c4fc8e45a8000002f46d00001ea004b19d05c010010b60967550c000022000001d34346fc050002240682e1ca0b6414900b70004d08da922b85bd1da1b1b62b80000008c634c7800000000d110e0005a9488f43662fce18fc1be0d8ec90c2900b4e49b00002e079016178664c512d2121ccdca5b3a88b09aa1519ea087b97b1ae1040027f2e6360000f84d8030000000007a40008400007000000000a29398000000482488b00c4c1271de4b01c4de8001c85f40012413c240e818014e980bd0990c0a300087e4c688022a5a474a2cb594134c7a9292160b43852a99a126090671331c60e5028940a6000e10004640000004f000000fd059244000001ac000000270003c6744a5000448000ac93711c5a07701d4e42000fa534ac791139cc1fe5b9378d13cc684178622bc2
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0xe000878e226c884000cc1fe4b40000011e000720001440009c09c19a0ac8893434627caf843072104f20002501e0de0000001acb80002447a4a10000005a800189000000000420000009e83b0000000000000029cc8800354000000aa2ec4c40221b398294000002804dc0000013c7dcac0ab3522084406a220000449cf2266fc921fa3264d4d42080002a40021600e0901600042a480e114300083cca0f70fc6f90d2040a2200cb14f3bc85c8a8d5162861050db2ee000028004265e4e21c10d0000c10e82da19d0280030c100d81ae04c020560180000002c1bb3085690f000380008030000600803000000040b008000000b0000e0041e0200f00000008010240104009040010180c0100500000000000180000400008020280003402000000040001c0401400000030000a02402000050200101c01000000000500007000040340700c0501405010100040501c00014040080800004000090400d00404040130740903400000020300500c03000000000000c0400400004000000300001000000000600000004000180203003004010040e11000000020040e00001000000040000c06004050080701c030140302c1600c050000b01803088030040a0180303802008100069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0x7d8c79c83d4050468000001fc330002de3bc951680f40000000017855c64a1f0001300007c1a45c88c1010004b800000000000780e92182bc1d00021211c1a98d00021c2d9ec00035800123448000e9a093f0204b090b36a410450cb2ca370a894d200244c61e727c7647504d09603c9900d342578061ba1724381a1ab344844278003e22e0928f93c20547601e2ce7b4a089a4247f46205f3aa5981f8492b6668d311c34e00000011160000460ed18e2506b97f2d677c1c1fe13a8400e1b410a318140f60da898000de1360b8c50000002842a0d802c510000000de0005a8952c07b88f94a1be5e8e592902400511169000000000000002986021900000000000000000431d43ca67c001d7000554ec0003e640ce68b20000c8839d12f6530000e5126600e50000000a40509800078cce030140000001d60467a0b7000000874db8e0000000fd8000000000012700000000225000000b88c10d252c000002c466cca8003f8308e2836278870ff8bb27e0007e1bd3cc000380000001c83718b04a5903d8172a62f8d8800404484ed01f1a02e83c91a0123840982f28e25cd614833271cd7a0c0001f4470000008387e8d42107807d9c9036000199b8000000000000000006700028c0006e8003864481522000c1cc8c94916e0009d90600009c5f8f216c0010590d0ee2102e9141247c8c09393c465c3a8f33e8000000000944c0aa0ad1867ac0011d0c0320000201062908f05a2141903106540c1540000020a118b980b0b80000019d0041151187415c0008b1b638c7c00e800032000000e63200002705640074051837340344759ce3b6000bc0003f20f4002030bc0006c82d0204cc2801a34834ca91ad1e8000110000a45402b8f129c2586d0000ec084389632b239cd91260000009d1dd2ea770718fa40e0000012c1200f00000007c60cd986c28a61c0017d1f0000d28b330a6205a19e08800c651b915000000063000804000fe0b27d46299822e5f8001920624ac2418e000000000001323b8ae0000007bc5e9d201c5590680019e574be11b0c28500008b0000007a8002045b0298000000000017425
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2401aa0040a59c8a018009239400000422678c0000180042610c1431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20202+((h/222+packedAt s3K5 (17982+(h % 222)*10) 10) % 800)*11) 11
  | 4 => packedAt s3K4 (22768+((h/183+packedAt s3K4 (20938+(h % 183)*10) 10) % 728)*11) 11
  | 3 => packedAt s3K3 (1064+((h/7+packedAt s3K3 (1029+(h % 7)*5) 5) % 30)*6) 6
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 2 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 2 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36705
namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0xb307f0e01300022d3e000030a35488000459c406aa540018c0ae678919cf3ee214ad0b723c760f50001de110da21e30e0b12093e2646907f0002fea24678002c07fc6600025e4440000031e97cb91830943588096132c9248c8e51383b5452964d4050cf90a3ba518ae82a2066cc5e0df152a20038c44e69d4c8921466814ff14713064d4981745c5c54c97b2c4384a912622c8051d0632d00005ca650840acc900838e9a4280003706e40008f15835c0021514410c642940000004b9a600090c958030ba7182f89f3621d51fa0419a5e89d1d92a039000066292000001bf3e6000000000708f0b186544c000001670000783b1a54540cc0011d3c05f02004700001462800456000a68150006f03902013a618341844ba914002834a84fc0000001643c770000007c80021b000670dd09a4a272c2f07d0002950a1fd3040013380029e338138000004208a24b0e80000003b0000000011a0260013a12c4f07bc800321e645cf724c00026c0006920e118fa1b24f42813e128284000000004200006880035e7492e07a330254fb11523e0f8efa1d00095c682594000011228739a54c3587b4183540019032e6240000049a3980c21914c6b8881180008840016510c6dc2895505e0001a26617e6ad388b1288978e080025aa2c5680041600142a681f08e481000184284000d8462000d510c4407a47880000084c00000386794820003c49f4290a80b03f4bf20916437000151470500409130001b8070b805298469024004040801802c030280103c0e00c0101801008080003f000120380d014110042510c08040030140d024000000800c680000f0000e0000c00800024050580201c0703045004000640f04c120940002802008030040000c0604004004040000e0480c00c020000401000018000140001c0d03824000230a80d0280400c0002402020100340900025008000000400c460080300c0102c00004020100700c060080d08402000050540e04c0300013014000140b048020000e0100201c0102c1f000100a000004150840000808004070400007407098230884a018200000100c000080705c030000406c02004060240400003004010b80200c140140c0000600004000000003a0340f04824080031980a00806008000aafca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x873ac5e0c5a4004a5905ea46112368b69310784713ba2c21a56cc50d912213506a063760981d18516a4e4108f05200f4579f548e85cfe0491ea1589d9ce07e7b06382e18c68c460832ae0dd190c32125d0bb8303842a8fd80043434cb52274943805d9064909b40c9dc0005b11b0784c4058d3a280125e43e06a148861400823b4538000003e28291e9883da57cfc0283c23c8322814dc990002294ec9c00008a3aa8087c95424a2488d82d00000011822000000001e82e066921136000a44000f4180000000000004a50780000028d1b831000000000b451e8444b181000234339be36c16ced9951c612c748002b88ec6580000803d0b2822247e43b99b0005a4e981a4606847b00a1c4720571c532896c829580b87289e96f1b6008f59340000011100000093c900ec3324f13c8000004a80000045e000740000002cc0014b49c88c0003631a4387e2080005209a8730003502a8000006f46e8000009f87d0113c6000208003ce000499c93585cc9726c344638061244aa0712c05a3a0a5d280eb35a2ac0093011053038938000778b59801083a8938e70902d899a0300c1b44f0a71321811287e08a968fd21c0d85d5318ba40e240122521288385817d282a382a1b5424a10609a80a62001c9b04c02380019d1ee0014904e0b2a606f26b01a3242795926ea18e8a5647c75c0f9c0468528859cc4e4558f20ca43e4880827b0246800026f4a60007f8001f6188af1d403a6a54681b17c0003c9e62dc9fc0017600050ca286f5180
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0xc71800145032794e79061223b50e80000074c7080033060ca683709c664ec9782e8884000000aa140080d13440000005e05a3280f9110003680013f000000001aa00065c001c7000000b18aa00000040800380354da1a51507f40003c2b2158000e3000000ae0521206f4000220c6000ce8b30c85f50810c07c000000440002d00193412a6bc5ea262643e0a8194000774d906c234518a5031220208140a52147c8839881d8000001b9000000fe0000005800000001c248000000d2670ab17c0000000008b00000000000000034000340003f44e099000448000c30004f09682b11e0580b010010080c02c1d004040000000407010000080c004050000501401000040040d00001000010480402c0000006000020640900002000040280d030000040d02806008080000000c0201c0300c06024070041108000010060080004c0001c010040a05c000000000403014020000c0600000805000200940402c030180001c0000c021241e0001b0000402001000020000b0341f014020000103404010070101e02001038000080100400018130140104c040480b038030100102c08004000000805c0000000070030ac0c004010080a000030240c0041c05c0a0080800400014080029d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0x7e4c6000000000660e40e86cc902170c00e4000000f04cceb07e000838668413a257c000003621ac00000400000bc9380005d800000262000b51ce26e8180003b00048ca61ba14e618d71e923600021800000708d08893202c04b0c52b0010759b6314648558240367aced94f42201c8e90b0a84bc7882636a864161a44461a8c10db2964b06e0ee10a7e87b1471587a03b97a0903ec588c73bc2187415331a1a02d0001003244205c3ea820171180001e4c980508e8243f92206a7d033800434854001ac0001000c0002b45f8810000101b42c00000043ce08000286790688d000000cd8663460f47b8e532c4a8a480017875c001e1000890ab9a00005c0fd8000f8424b900000000000000000000a91ef2280001d0000003c87a0dd000184fb00030e2e400000000000a108a2a285000072196000258760006c062167402134c295e3340007a93a02a39c2787114803c8f83f2ba338ea8c61706440017f0247508f01102c7f9021dc1c03590795b000124f005f00037c0016c37671000000430414519f322e5aca188c1ae2d410838128164931e322c84c9a8f3152000000000380000d1ff29c22000104248364c70000001bc1519500267c94971370360938003d8108000000002bc000000005ec9c80036e78887125144000f70833be000aa93d1844d800065046748e68e613e69cf20000e644d01893256000590321de6f8000a6000378e28d2000028000253e2001028980606f00020c05e0000016203c2e8001803a0000bb98124279c5f87d10e5bc060be0a20010100027c000001a90000d8001cc17662c3809e22a1b8b4901386000749194406243d8172d00250b1643b4584b31841a03004d1303da0000001328225d0e2120003506408e4364a1110271a63c1051a61f8000f81c919e2d8260331f26b4fb89b28000000000000284a40002ca000032071f43fc0000016e080000002760008e2250b67a8e5a0b0ba000d59443f0720c79750000000000000042029954000274819730002b48000000030422a1f09472886a1e3b03a80587a2da1d4df8623cc6a0970460523f8710021400742b96e15
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1800002123000101070002913414cb00000e3c00001400000020005030090000840e000001431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20202+((h/222+packedAt s4K5 (17982+(h % 222)*10) 10) % 800)*11) 11
  | 4 => packedAt s4K4 (22768+((h/183+packedAt s4K4 (20938+(h % 183)*10) 10) % 728)*11) 11
  | 3 => packedAt s4K3 (1071+((h/7+packedAt s4K3 (1029+(h % 7)*6) 6) % 42)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 2 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 2 => 0x429291090d2206554084ca8265412a0a858b18
  | 3 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8eae8eae8e8a8e8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36705
namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x2f0000280007500000004881400d80001c00000000000000b80007011134500010000aae189401f00b530e480069e00a1600564cc1000a8ca3064800f440002916842164e00006000e0c180000410100000801000005ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x261de424c3ba84987710930efa8a61de514c3baa2987714530ae28a61df414c3bc82986790530eea0a61dc414c338829877c8530ef10a61dd214c3b8429877d4130eda8261df404c33e80987790130eea02619d404c3b880985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30af298617e520c2faa4185f94430bea8861be410c3788218778c430ee188617e500c37e80186f50030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c837c83906f10720ef18e41dc31c83de43907b48720dfa0641bd40c83be6190774c320bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3106f90620de20c41de31883b863107b88620f610c417e508837e81106f50220ef98441dd30883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c514837c82906f10520ef18a41dc31483de42907b48520dfa0241bd40483be6090774c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841be41083788210778c420ee18841ee21083d842105f94020dfa0041bd40083be6010774c020f790041fa20083da40107e48020bfaa621bf54c427ea9885f95310beaa6217c54c4378a9884f15310bfa9e21df53c42bea7885f94f10bea9e217c53c43b8a7885714f10bfa96217e52c42faa5885f14b10df20e21bc41c43bc6388770c710fb10e21f521c437e81886f50310ef98621dd30c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10bea8c21be41843788308778c610ee18c217e508437e81086f50210ef98421dd30843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df20a21bc41443bc6288770c510fb10a21f5214437e80886f50110ef98221dd30443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821be41043788208778c410ee188217e500437e80086f50010ef98021dd30043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21df20a43bc41487bc6290f70c521fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e510877c8210ef10421ef18843dc31087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f90f40dea1e81bc43d02fca5a05f54b40dfa1681be42d037a85a06f10b40bf28e817d51d037e83a06f90740dea0e81bc41d03bc63a0770c740dfa9e81be53d037aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d027ca3a06f54740de28e81bf31d037c63a0678c740de98e81bc31d033863a06fc8740df10e81bd21d037843a05f552409eaa4817e53903bca7205794e40bea9c81dd53902baa7205f94a40bea94817e51902faa3206f90640de20c81de31903b863205f94240dfa0481fb40902fea6a05f14d40dfa1a81be435037a86a06f10d40bfa92817c525037e84a06f90940dea1281bc42502fea2a05f14540dfa0a81be415037a82a06f10540ef18a81dc31503f680a06f90140dfa9a81be535037aa6a06f14d40dfa9281be525037aa4a06f14940df99281be325037a64a06f0c940dfa8a81be515037aa2a06f145409e28a81bf315037c62a0678c540de98a81bc315033862a06fc8540df10a81bd215037842a06fd4140dda82817e541027ca8205f94c40ef298815e53102faa6207754c40aea98817e52102faa4205f94440bea8881be41103788220778c440ee188817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3be87987790f30eea1e61dc43cc2fca5985f54b30ef99661de32cc3ba6598770cb30bf28e617d51cc37c83986f10730ef98e61de31cc3ba6398770c730dfa0661bd40cc3bea9987795330eeaa661dc54cc3bea5987794b30eea9661dc52cc3be85987790b30eea1661dc42cc3bea3987794730af28e61dd51cc3b8a39877d0730ef20e619e41cc3ba83987710730ce20e61df21cc3bc43987748730ee10e61df40cc33e81987790330eea06619d40cc3b881985fd5230bf2a461be548c27ca9185f55230deaa4613d548c2f8a9185f54e30aea9c617e528c2faa5185f94630bea8c61be418c3788318778c630ee18c617e508c37e81186f50230ef98461fb308c2fea8985f95130beaa2617c544c3be86987790d30eea1a61dc434c2fea4985f14930ef99261de324c3ba6498770c930bfa8a617c514c37c82986f10530ef98a61de314c3ba6298770c530dfa0261bd404c3f66098778c130efaa261de544c3baa8987715130efa9261de524c3baa4987714930efa1
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83bf439077c8720ef50e41de21c837e52906faa520efd0a41df21483bd42907788520df94641dfa0c83f741906fca120df54241dfa9c83be539077aa720ef14e41dfa9483be529077aa520ef14a41df99483be329077a6520ef0ca419f28c83bf509077ca120ef542419ea8483bc50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077c8620ef50c41de218837e52106faa420efd0841df21083bd42107788420df94441dfa0883f6411077a8220fd50441bf280837d501077ea620ef94c41dea9883bc531077ea420ef94841dea9083bc521077e6420ef8c841de99083bc321077ca220cf94441db28883bf501077ca020ef540419ea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598df54b31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7bc8718f750e31ee21c637e528c6faa518f7cca31ef19463dd328c7b86518df94631df20c63bc418c7be6318fdcc631bf284637d508c7bea918f795231eeaa463dc548c7bea518f794a31eea9463dc528c7be8518f790a31eea1463dc428c6bca318f7d0631ef20c639e418c7ba8318f710631ce20c63df508c7bca118f754231aea8463dc508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931df20a63bc414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f7d0c31ef21863dd430c7b88618df94831bea9063df320c7bc6418f74c831ee190637e510c77c8218ef10431ef98863f6310c7ba6218fd4c431bf280637d500c7bea818f795031eeaa063dc540c7bea418f794831eea9063dc520c7be8418f790831eea1063dc420c7bca218d794431eb28863df410c7bc8218e790431eea0863dc410c7388218f7d4031ef28063dd500c6baa018f714031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21df20e43bc41c87bc6390f70c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621df20c43bc41887bc6310f70c621f790c43f
  | 3 => 0xb8840ef7a62ed658000a800098242000000000000fa00000000000001a181600004c000007deef96080000000192a4025a1b8a7ac3000000648b25ae0000008e57cbf000301250cdc1e000662000f89446b2001dd000000f0c5f800000000d10000000c00000000052400000578000b901044af713f8000000000018d000000708000f445c000006de0c4003c9534000e120b33ce58d98000000000016976a00000000000001f92d107efe1a08cc000000000e00000000000000000072bad18ac14003c811600000401004000010030160020000080001600c0080001202804004006000000070000080080000000c0000d002000010060080000000000200c068060000000700600602c008080020000000600000000002000008000000000280000000000400005000028010000180280000000a0080000700000403806008018058010040100080000001000003008000000080000140100e00e01c00001008000010050000000500000400000001000024000040060180080001a0180200000200400000016000000010000080200000800c01001006000018070040000000000000400801018000000000080000180100003c0100100001400000002010028000080040180600400000800008024008040100040280600000000001004004008000040000200600000c0100300401c0000900001c008010000040000100a0080700000801800807006004030050040000000100a0100000400800404000000010000010060500080000804c0100102200800005000000010000000000180300400c0d8070080040380500800000803000000020000080000080900000c038080000000200200c0100280000400c0080200203401002000000020010040140100100601c0680000a0000480500000c0200001200802df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0xa78ac2510ce0000000055ef74000001ae000ae8001421dd3bb3b00002852a210e28540029669c0000002f0000000036b324001f82455da0000016a000001d2a0c00000000000678dc87d099000ba521ab70000e84f000588000000000000000013f0000015f807000231a216c0000007a9b8000328ed3690008d0000000000d99b16613e0009d0000000017f1ad36e000850003bc00000057000000000000000016b19679edf4268000720011c80005c4d4000003d4608000000005e0000000009c0002b21363a8bb16d0a0000c40b624600000000536e2d18000000000002a13ee0000015b66064c9980d000270f78004385409c80028e9c40000566a0015c00034ebcd3c00000477000000000d7c9d99d00000110141000641c82f94f6d34a59a8618000671037d2b21b51297c40000000000000000000000eb1cb80006a5158da84000000002f41d63c45b82c0a20002fa6b4c81597d8bd0941609c10411e00046a2e0b6310000000000000028a0003f80000073a00000000000001bb000000c1c000002c82994a80018c0000014c0cc7a41a000622c986facc0000000022b268c3d401fb7a200060a415aa0017c2600007107200000029c00000000b14000493e4000291a6700984c482d124e24000be00000160033000d20002da000000000000000000000070a6d08600010e0014c8006cc0012c000000301ba800372354f436c000340002947b4000120006520107b0f4000cd1f9aad000000000370c60016a0e336a20d0bb082fab7cd024e474000002ac6e292148800186f79dd8005d6000001d3000d804012068e07c7b80345a00049a49050eac9e8001342a543a53084f9c000000ca001f0379000000000004489a8c78080007500038a7c2000fe80022a000000006420016c0004ec8d4f180025600065ab912a000003102bc0000000000062800000000a4c000741fa7295e800000e54e80410002c109800000000b08e76da2b58a3b93b6a9c87ad30000003a968000094002160000000026d000e8c000002ea00011800000000000005ca0009127e53abd8b380975e1ac071d63d6ddd4e1143e04bc00000000ce0003c20000000000000034deb20e30c000001973ce75c1c00031647cd0878322e342d000000320000000000019f1f439ebc4cd800000000000000000000021d5e41ec24332706001c434b458d452d000000000ca800000000a9a7a000df0002ff000c640000000070c003224b600000288000001a52180000009700051a0000000008087ca5358630ca949328278b1c0026930e8a5faa19338c34d78006acb3c002117a43c9eb91e7b0001f40004aa0009f000224a19cc800648000002d2562001ad3d03a40005425f1dc2e8882894ac14dba3b36ca251b430b7440001e8000c2d70589622b2f2800ae00b2e
  | 5 => 0xe4400000000aac6e0004140007f86068c0014791320400000000520744000003064dc003c400025c000000000013e3e64e4765dc0195baf0000000574000928d9234c11ce19f1309b9ef9740002a9f50007ee81800232086ad97b8ae352000451814700009636429c0007e0cd0282ac089cb1a80000023348cd24868000000000000049e001363062e2c08109e520ae480000015e0005625e24e3a09096509c2d000000000734de80019e8ec00000000718001c9000000000000000000000065886c000002a802c003b70007b4e0000000001c080062edec0021203800000180000be99fb2b6400313120f3187b8000006ba669c30000007e0f3000540001c7b5742806923aa946ebbcb80d6566e68233cd6b60000022751c6392cb540549e58ab160000000028c402549738005066c50681700005504b3a67aa60f62de024b2876ad02aa50dbf0b90009357aa042b495db3ba1000000002ce0f8b18002c9044ac18f800040c8c4339b77a611b09562be8a00c2a40d4975e280026c0011f252330d54bfbd40de0012a0000004380024a0000014280000000177000000b89fb3aa728ec0ca275120074003c118ed319c8f8146000de37f104001970a0000ec42e281000000001bf10a910000000007e4b5bec0000008e9dd3c48fc000000000000000007c615c60a446ce7cd18007780000000000000000000000bc0000000fe7cc6c3c70001d80031e0000000025c0000002f3846dcec93e916000000eab00200c280009d4cc130369a47dc000000000004c4000000000000020068afd1d43a60000008c273000018b700040600172000000aedf88001125e5898006f4760000004ca5dc001a50e6b6c3c8625b83788e1aa3c2001510003ea5f9530006a48c4e611138e519ea800236000bd800730d89339bb43c06de612653eed92826f40e000808001d836c9502920cba88c8b835c3a4b992409e2d40000000000199bd9000520000006f05e80022a000388cc9ac5b200000000434000000005469a13a0fb7964c80000f612e90002fd420174f000061c344a6800446500392e1284d4034b8e3c80018e8dd37c0018d00000058da0000000ad4003a7000000000003fe348001ba08a98d979c10001b00009614400015a8208ec9c782b43f81540f0bc00009c0000065a001f20e61b43083228b3ec001c9800096001c11fa166fac000000000000000000000000000000000002c200000166b4f0008880008870e0002200000042d551b254a898be202606425a983b04c544001df0001c102b9e00000083be37b6739571fe2b8ed1743a9496fb47c9c85c6f940037336c1f98e03200024526081684aa00023c52ebb042363410efc340001e6000ab96078c8f40000079ce81179ab6bcb998900038adc0b7800000000d800000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3184394410c610c794f408431d53d0210c794d408431d5350210c7953308431d54cc210c7951308431d544c210e6501308423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e61151108f184544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6114d1097184534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109ed81524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524423e6590510c7d4e414431c5390510cbd4a414432c52905108f994414431f5310510c714c414432f5210510cb148414425e658c510c7d52314431c548c510d3d4a314434c528c51097994314431f540c510c7150314434f520c510d3148314436452885109d195214423e65d0110c7d4f404431c53d0110cbd4b404432c52d0110ad987404423c6550110c7d4d404431c5350110cbd49404432c5250110ad185404425e65cc110c7d53304431c54cc110d3d4b304434c52cc110b5987304425c654c110c7d51304431c544c110d3d49304434c524c110b51853044399404c110da14b104425e63d50109758f540426e62d50109b58b540423d65950108fd81540423d60550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d81530425d6054c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810da181520423e64148108f590520425e63148109758c520426e62148109d984520423f65904108f596410431e5390410c754e410432e5290410cb54a41042b960904108fd94410423d6510410c794c410431d5310410cb948410432d5210410ae580410425f658c41097596310431e548c410c7552310434e528c410d354a31042d9608c41097d94310425d650c410c7950310431d540c410d3948310434d520c410e510431042d9600c4108f992500423d64940109798e500425d63940108f597400431e53d0010c754f400432e52d0010cb54b400423f6550010c794d400431d5350010cb949400432d525001097597300431e54cc010c7553300434e52cc010d354b300425f654c010c7951300431d544c010d3949300434d524c010da54b20042796508010d954b100427965840109dd95100436552440109ed9510042e86244010
  | 1 => 0x831d544c22097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d208f993514823d64d45209798f514825d63d4520cdd4441483345110520ae5804148357510c520d514431482d9600c5209b99721482e860485209798f540825d63d50209d987540827561d50208f596540823e61950208f185540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530825e6194c20c7951530831d5454c2097185530823e6414c208f590530825e6314c209d98453082756114c20cd95251083355494420d594e51083555394420cdd9251083346494420d5d8e510835463944208fd91510823c645442097d8d510825c6354420cd95151083355454420d594d51083555354420cdd9151083346454420d5d8d51083546354420dc181510823f65904208f596410831e5390420c754e41083365190420cd546410823f65104208f594410831e5310420c754c41083365110420cd544410825f658c42097596310831e548c420c75523108356518c420d5546310825f650c42097594310831e540c420c75503108356510c420d5544310826d6588420d9546210836551084208f992500823d64940209798e500825d63940208f597400831e53d0020c754f400833651d0020cd547400823f6550020c794d400831d5350020cd9454008335515002097597300831e54cc020c7553300835651cc020d5547300825f654c020c7951300831d544c020d59453008355514c020e6501300836551c80209bd9520083655148020ea50120083c930480209ed95200833661d5310ce58354c425e63953109758e54c425f63553109718d54c43366115310ce58054c431f54d4f10c715353c435661d4f10d658353c423e6494f108f59253c423f6454f108f19153c431f5414f10c715053c43566114f10d658053c423e6494b108f59252c425e6394b109758e52c423f6454b108f19152c425f6354b109718d52c431f5390710c714e41c42b96090710c7d4c41c431c5310710ae58041c431f548c710c715231c42d9608c710c7d5031c431c540c710b658031c42f06048710c7d4f40c431c53d0310ad98740c431f5350310c714d40c42b46150310c7d5330c431c54cc310b598730c431f544c310c715130c42d4614c310f848720c42f16108310f888420c425e63d52109758f548425e63152109758c548423e64d4e108f593538431e5494e10c7552538431e5454e10c7551538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f590528425e6314a109758c528431e5390610c754e418431e5310610c754c418431e548c610c7552318431e540c610c755
  | 2 => 0x5150330e6d8140cc23e61952308f185548c23f64546308f191518c23f65906308f596418c23f65106308f594418c2b96010630c7952318c31d548c630d5946318c31e540c630c7550318c31e54cc230c7553308c26f62551309b189544c27761551309d185544c25e65d0d3097195434c31c5450d30c7550434c23e64149308f590524c29f644c930a7191324c34c524c930a7990324c29d640c9308f993514c23d64d4530cdd44414c3345110530ae580414c25e65cc530a7993314c29d64cc530d5146314c29f644c530a7191314c29e648c130a7592304c2d96095130b3d89544c2cc6255130b5d85544c2d46155130b6d81544c31d5415130b6582524c29f6454930a7191524c2d76154930b5185524c2db6054930a7990524c29d6414930d3548524c2da60d0930b6583424c25f655093097195424c25e651093097594424c29e64d4530a7593514c2d96094530a7d91514c29c6454530b3d89514c2cc6254530b6d81514c25e65d053097597414c35451d0530a7986414c31c5190530a7582414c25f655053097195414c3545110530b6980414c2d96010530a7984414c3966110530e5d44414c31c5110530e5144414c3145110530e6980414c29d6010530e6580414c299601053097997214c25d65c8530a7993214c29d64c8530d5147214c25f654853097195214c29f6448530a7191214c2db6048530b6181214c3545108530b6980214c2d96008530e6907504c39841d4130a7987404c31c51d0130e6d43404c25e6590130a7592404c29c6150130c7145404c39b6050130e6d41404c25e6510130a7990404c25e63d50308f596540c23e61950308f185540c23e64150309798c540c23f64544308f191510c23f65904308f596410c31e53904308fd94410c23d6510430c794c410c25d658c430c7952310c31d548c430c7950310c31d540c430d5944310c23e64940308f592500c23d65d0030c794f400c23f6550030c794d400c31e54cc030c7553300c25f654c030c7951300c31d544c0309ed95300c35a534c03097d8d54c825c63553209798c54c825d63153208fd9153c823c6454f208f99053c823d6414f208fd9151c823c645472097d8d51c825c6354720ba18121c8399404c3209798f548825d63d52208f986548823c61552209798c548825d63152208f993538823d64d4e20c7952538831d5494e2097986538831e5454e20c7551538825c6154e208f990538823d6414e208fd91518823c645462097d8d518825c63546208fd96418823d6590620c794e418831d53906208fd94418823d6510620c794c418831d5310620ae580418825f658c62097596318831e548c620c7552318825f650c62097594318831e540c620c755031882d9600c620c794f408831d53d0220c794d408831d5350220c7953308831d54cc220c7951308
  | 3 => 0x740ab58b51d02b960d4740a7d8d51d029c6354740ae58051d023e65cc7408f59731d031e518c740a758231d023f654c7408f19531d0396610c740c794431d029d600c7408f99721d023d65c8740a798f21d029d63c87408fd9521d023c6548740a7d8d21d029c6348740aed8121d02b8604874097986539025c6154e4097d8d519025c6354640c794e419031d5390640cd946419031e5310640c754c419025f658c64097596319025f650c6409759431902d9600c640c794f409031d53d0240c714d435025e63149409758c525029f6350940a718d425032c5250940a798c425029d63109409798f515025d63d45408f997415029e63d0540a758f41503345190540a7d8d415029c6350540d5d443150354510c540b6580315029e6390140a758e40502b96094d40abd8953502ac6254d40add8553502b46154d40aed81535031d5314d40ae582525029f6354940a718d52502b76154940ad18552502bb6054940a798c525029d6314940cb54852502ba60cc940ae583325023f654c9408f195325023e650c9408f594325029e63d4540a758f51502b96094540a7d8d515029c6354540abd8951502ac6254540aed81515023e65cc5408f597315033451cc540a7986315031c518c540a7582315023f654c5408f1953150334510c540ae98031502b9600c540a79843150396610c540e5d44315031c510c540e51443150314510c540e6980315029d600c540e65803150299600c5408f997215023d65c8540a798f215029d63c8540cd147215023f65485408f195215029f6348540a718d21502bb6048540ae18121503345108540ae98021502b96008540e68c7505039831d414097986531025c6154c4097d8d511025c63544408f596411031e5390440c754e411031e5310440c754c4110336511044097d96311025d658c440c7952311025f650c44097594311031e540c440c794f401031d53d00408fd95401031e5350040c754d401027b6550040ce951401026e62153309b58854cc31c5450f30c755043cc23f6454b308f19152cc29f644cb30a719132cc29e640cb30a759032cc34d520cb308fd9151cc23c6454730a799331cc29d64cc730a7d9131cc29c644c730d594431cc2d960d5330c755054cc2ce6215330b358854cc2d96015330b658352cc29f6454b30a719152cc29e6414b30a759052cc34d5214b30b658052cc25f6550b309719542cc25e6510b309759442cc29e64d4730a759351cc2ce62d4730b358b51cc2d960d4730a7d9151cc29c6454730b658051cc25e65d07309759741cc31e5190730a758241cc25f65507309719541cc3966110730c794441cc29d60107309799721cc25d65c8730a799321cc29d64c873097d9521cc25c6548730a7d9121cc29c6448730b6d8121cc2d86048730a798740cc31e51d0330a718540cc31e
  | 4 => 0x7191310c677654c4318f992500c63d6494031b5987540c71d5415031b3988540c6cd6215031b5984540c6da6015031b6580540c6d661d4831a7d91520c69c6454831a7990520c69d6414831d3548520c6d66114831b6980520c6d96014831b5986420c6d5619083197d95420c65c655083197994420c65d6510831d5986510c65d65d0431a7986410c71e5190431e5946410c69d609043197d95410c69e6110431e5984410c71e5110431e5944410c69d6010431a7992500c69d6494031c7905500c71c4154031a7990500c69d6414031b3988500c6cd62140319798f54c865d63d53218f58254c863f60553219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f219758253c871e5454f21c755153c865f6054f218f99053c863d6414f21c794e41c871d5390721c794c41c871d5310721c795231c871d548c721c795031c871d540c7218f99250c863d64943219798e50c865d63943219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21e5104318863e64942218f592508865e63942219758e508863d60d51218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e65151218f580544871f54d4d21c7153534865d60d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d2197580534863e6590521c7d4e414871c53905218f994414871f5310521c714c414865e658c521c7d52314871c548c52197994314871f540c521c71503148794410c521ced53504873854d4121d6d4f504875853d4121ced93504873864d4121d6d8f504875863d4121ce907504873841d4121d68c7504875831d41218f990504863d64141219798c504865d6314121ced5050487385414121d6d4c50487585314121ce99050487396414121d698c50487596314121ce90450487384114121d68c450487583114121da884504865f63550219718d540865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520866f6548421e910521087c43148421ba181210867765484218f992500863d64940219798e500865d6394021c754c43d025f6354b409718d52d029f6350b40a718d42d029e6310b40a758c42d032d5210b4097d8d51d025c6354740a798f41d029d63d0740a7d8d41d029c6350740cd94441d02b960d4f40c754c53d02ae6214f40ab58853d02b96014f40ae58352d029f6354b40a718d52d029e6314b40a758c52d032d5214b40ae58052d023f654cb408f19532d023e650cb408f59432d029e63d4740a758f51d02ae62d4
  | 5 => 0x51cca3e64943328f59250cca7661d52329d587548cb1f5410e328fd91518ca3c64546328f992508ca3d64942328f987544ca3d60d51328f992544ca5f63551328f994544cb1d63151328f984544ca3d601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64d45328f593514ca3e64141328f590504ca3d65950328f986540ca3d6095032c718d540ca3c61550328fd81540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328fd91510ca3c64544328f992500ca3d64940329758253d065f6054f419798e50d065d6394341c794d439065e6394a419758e529069f6350a41a718d429072e5250a41a798c429069d6310a41a798f419069d63d06419798e509065d6394241ab98b53906ad62d4e41ad987539071f5394e41ad984539069e63d4a41a758f52906b661d4a41a798e529069d6394a41cbd4a52906b66114a418fd95329063c654ca418f994329063d650ca41a798e509069d6394241a798c509069d6314241ab98850906ad621424197583535065d6014d41c7d4e415071c53905419798c505065d6314141c754c431065f63548419718d521069f6350841a718d421069e6310841a758c421072d5210841a798f411069d63d04418fd95411069f6350441a718d411067765504419798e501065d6394041ad987531071d5314c41ab98853106ad6214c41ad98453106ba6014c41ae58053106b661d4841a7d8d521069c6354841a798c521069d6314841cb54852106b66114841ae98052106b96014841ad98632106b5618c8418fd95321063c654c8418f994321063d650c841cd986511069e6394041a758e501069e6314041a758c50106ae6214041ab588501063d60953318fd8154cc63e64943318f59250cc66e62d52319b58b548c71e5450e31c7d50438c63e6494a318f592528c69f644ca31a7191328c74e524ca31a7990328c69d640ca31a7993318c69d64cc6318f992508c63d6494231b398b548c6cd62d5231b5987548c71f5495231b5984548c69e64d4a31a7593528c6d661d4a31a7992528c69d6494a31d3d4a528c6d66114a3197d95428c65c6550a3197994428c65d6510a31a7582418c7966110631a7580418c69e6494231a7592508c71e4154231c7105508c69e6414231a7590508c6ce6214231b3588508c63d60d51318f992544c65d639513197d8d544c63e65151318f580544c63e65905318f994414c71f548c531c7152314c63e64141318f590504c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c31c7151430c65d6510c31c7550430c63f64548318f191520c69f644c831a7191320c69e640c831a7590320c74d520c831a7993310c69d64cc43197d95310c69f644c431a
  | 6 => 0xd0ee80000023f8552638000000a80000000368a90000a39a780017e0000000000000000000650000000000f815a0000002741e1a9b0000000000001002540000000000000000110000001750b495d0720798000001470001388000d40001c30001eb80d80000006f800000000800000001400000400000000c02400004800001800000c00001400001001000400001001c02800400800c00400000800000c01800800000000000000001800400402c02400000000c00000000800400400000400000401400000001000c00003400800001402400803c00c02400000c00800400000402400400002c00001402400c00400000c01400400400000000801800001c00000003000000c00000800000000400001c02400400400c01400402400002c00000c01001000000403800000401c00400400800000400000001000000400000000400400801c00c02800400800c01001c00c00000400c00000400000c00800c02800400800400400000000c00001002800800001c00800000000000c00400800c00c00000400c00800800c00400000400000000400000800400c00000000400400000800000400000000000400001800002400801000000400400000000400000000000000800000400401800000401c00000000000400c01000800001000000801c00802c00401000c00008802000000800000000000401402400000400000000c00c00400000000800800003800401000000000403400800001400801c00000002000400400001400000400000000001800000c00002001800800000001000800400400001400000400401000000001000000400000000400000c00000c00000000000000400c00c01800000001400c00000000c00800000002800000000400400000000400000400003003c00000000400800802000800801001000400800000400800c00000407000400000800400c00800800401401000000001c01800800000000000000002c01400000000400001800000000000800400000800801000c00803000400800001000400c03000400001000800400000000c00c00000000001800001400806c0000069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750e5110f1d435404397d8d51d0a5c63547429798e50d0a5d639434297d8d5190a5c63546429798e5090a5d6394242979875350a5d60d4d42979845350a5d6014d428f9974350b1c53d0d42c714d4350b1c53909429798f5150a5d63d45429798c5050a5d6314142979865310a5d6094c42971855310a5f6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f655084297d8d5110a5c63544429798e5010a5d63940429e98054cca796015332c715143cca3f64547328f191
  | 7 => 0x80008d0001fe0000000002000d18001010000cc0841cb19c1fd8000000002308002528e89f58000000000ff84c8271c823b0000dc80026926b8000f28001aa99d0002291bf17f04b8632178b68001dc8a71f88ec9af0d680015980000000029021e0259f810380015891407b00026c0001b024b8000000000000d28000ab224a2b0000a1a3680011080021c00000000000000016d8000002298000000000058000000001782829648000d089d8f9199014a9105f0e70320000001638000000001820001c000000000001f80000007889e0f9a590cd03fa6480024f1220000eba7800000e00000007191916520d12680007ea5326b0000fb2281769c99019bb27317317b8ac0002440288002980c300016a29504e1fe800280868a0680000016b8748000000000000000000001f7800000000029a908001579329f18000518000af86d91c05600027a0ca04d8000000000001839a6235a7e086888a502679f12710fd80003b96c000249000000211000237a0c1df88c1e08000000001da8d483c8000001e70000000d300017b00002c0001a9a339d601999205e92a00023400016700000310d02080000011d8be80000011e0fa9c280000200010c29a0a62738f21b31119e50000999910090000351ae111258933a268001759a12579238bf8949d7a04a9c29da8106c1d292f21200f06a9201ce1e11b61c211c9bf9ea1180000e1a8ea0b80000000000022780000006087085e0000000c3a9f0001a292600000000019d80000000000011f95595c9498b501b84524c15da3987c8000761918b60000001528000dd00014b1fb94904618c9a08000002159139100001620000000000000000bd0be282053a7084a8000000aa8001950000000a48000e10a409b8918000f50001609900000000000000002469390540000000000640001448000001ed95100000000000018f2479a400000000000023d1889590000001ef18518f8ae00010929e9048001bba8322018401317d80c0001908bd87d89400010b000049a18a5d80004f00026880012994c82d8000768c095e8002330001eaa1ca659e60d58e68d100002a0c600014380016e00018b9058000158e38000000000000922098000b38001160000960000cb8002320240401aa00017e9c413c80000000000009d29e00000022b9a028c0a68df1b098199a0000000000002580000000678000002350780000328378001a88000001de00016d00000024e80689f0000000000000000000000000000000000000000000000001248000000000000000790bf26e800000082838a84a2e055a0b00000021024024c8578d200020e0000001d0a6f26f8399550000ff0f8800150062a1d8001c70230001611d480017a1d70000b9834854a2a1c90000210000000000b080020f9b921f92409080000000000000018
  | 8 => 0x15f9040000f00981bd19e80003d107a1b0b100027d0db2218000000000000000000000648000392381459b481007797718700010b80000000000021724618b0fb86580004c0001e7a1821a00011980000002a8c28ce00002380009280028a94b8c90c880000011680000022d9e200000000000000016f00000c9739f500000028691b18980015188080000000002d1450002a000000003707ba6198a00001093a82b93700027f80015e2778ad80000000013c0aa0001f984180000023ba0400000000026e01b2209f900027480000000000006810ea1e8000000000002128001539800001468001d51bc8c5954a3a00022580000000025b2510fe8000000000000000000002878000341828000000000000c190c94e9680772199c4a3ea771219948ee1ed14f8000001cc19580000005b80000014c00000000000000000000000002e9ca8bc8b78000eb1e980006b0000002488d9800244a410d88001cd0002288582362668000588f180019880013b8d80ef1569a18ed8000001fa03b0000001d892e0000000b31d01b21ff80000018e08326825c1270000970001ff24b0001d40000001f21a81661b406b8000000000f7a661be1dc1362348000000001700ec00e8000cf29c89e8e2a0c8001c79430a084280000000000026700000000025b80026a8000000001071ef9668000000800000000000c68000001740758000001a48001689d90278001b70001882190000000200000a280000006e24800014a0001a212d0000958950000710000001f402480023f28a0dc18629580020194d0db8b017a8900001348000448000a586d0000001cf8081b80001e40000000000000001d38b880026d8571211d110e0d9052a8d0000728001ec8359e6a2d0fc14d8002148600e426000000000009100007a9a92861f62028d0047a2c8000002038001f0a7880004892300001f0000000000001e280000005d1278000002370c12050002841de81415700000000b8e490da2e84694212c80b02f1a680019ba1682b0e580020f0e200000014120800029900006611200018d8000000e30000000001978001848188000000000f71a598680000029180000000000022406708b0000000bb0128220000001da10f0000968de9318b400023c1b39ac0bc00000000011b80019980008114f13f0000000598000000000000000000002630000000000000001ba80000001a80000024e23aa7b89c26980008900a00018780891a14883107f29ba75194148276a3021197c9d215f2890000000c78000001ee0fa1ee8038000000000000000000000d78d70a983ea1424715c00000000000000000000000012e8380000d52212261ab0000000500001f029612a80000000028599b00029a81c9970002430000002940000000000000000000870f60000ca
  | 9 => 0xf0338000078000001690000001be8000178000000000002058002408000440731b28000000e80000a78e780010880000027f00000000000000000025d1e02920000000002560001188000000291e383080fa5200000000000000280004202e0a00000000001cc80000001701c28815600000021f0268000300000000000988000000000000002270000000001890000000001fc0002968f680005102fa7b114a10920800117a7d8002428000f40001658618000000a212801900000000010988580022395827c8000c40000002391ec11292b00001200012b80000028c8000000000410000fe16f80010f84a000207a5f0ea8000000568000000000000000000000002318b90c812d9aea8194080005a17118a9930001eb0001ad80024d90a00000013d800000000000255a7e80000000000000000000019a9709e5a8f800000000000297a3c80000000000000000000000000022307400000000000020a8000000000000b80001d59d98000f100000000024d2420000000000508e52458061378f4893a5a28d93683a0000000f3a800ab99826080018318c1292131c88b280009a00006216c80700000000000004380000015080000000005a8000000002550000000a500000016980010285205d81d8f58139d19cda07059206259a98993a641e313513d1b796a8ae96325703c00026200028700000000000008a0ba8ea0001358000000aca6a0001fc88981e02500002c84b1312328000cf86c8000002839ba14184316b0229e92629dd8850692790000000000000000638001531df20908781a08b8051640001c0a6ca930001a70c48b1a5a80000000000008aa8b8b580007d22f0408da99f8001f690080000011e80020d9af8118c70000000000318001bd80000a97200000000000016784e80004fa5380000016194628882185c00000006e8000000de00000000019c8261f28dd8000000001c51f4a7184580010508f0470000001760490000000efa0897d250a6514424383d8ba28e2948000a11150001798000000002160001718001b58001fd01d1258fd0001d680003300000000000000000000001800000000008199f0001fa9e80f30001ac80025e8000000000001c38000000000c200000020300008200000013080007a00100000000015b80000000000027c1f700029fa701478001f300003f036178a220000001031cea7280022f8000000001320001db88f86117c00000000000000000011d00000000008e0da0000d3800000097800000066a6d0000c5016179241a3d8ed13980013000013a196a5488609f94295218125c80020e9b105308807380000013827a9cb90696ea021b680084d18580000000022a80000000000003e0000000000e60000000cda388001cf13b00480018e8000000002138001288d61d31130001060000000
  | 10 => 0x2610000e080005b00000000000000012f8000001b50000000002252568002151c601e8a881691700000017f80015b0280001c5a760000000001e49db0000000000000000000000c98000848151b98001fb09928f00000025f80022280020080000000000005f80000008d80027224f90a9d80e98e90ad22c21d0c006993414a80000000000000005c8000000480fc9400b200000000000019297780009320a00006a12500000028500000000007c0001c115aa4aa9700003a9ad00011599e29d0000a311a8f0a9289c92c1542898001330000bb93e80013e0001ca0000000001f390800008ca5186f07f9b187513f9a521b80d1a3a4a083a9380027988ea1a8ce80000009b25e000000162a310001600000000001c180009a9e88000000b70e000020118087e0cb1728cca498000001dd23e0001228000002999c69bc1ab80428b24500011f14e0700000002758001960000000000001b89020018df9a30000098001748000000000000a
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xa40c009a003e0032de006e386674ced800000000ca00b000927a4eb20054463406805c4c007e00184a009ecc12000096102886d040d49c002a1ebc427602263a64dc00d6680000b60400acc08abe001ca600da7c2c0070900000ae00000000b472b85a0078006a568cc82400ba00aa580800c4440a0062300022001600a8a0821a0e00520036c6948e00845e145060c23c48002e200098886c0000d2000000a20000000000080b1c020100000100050700090502020c000a0000071a0005030100000402020001a28e2a1ca221d1b7050d5010e8cb80a8a1e65459c75410e32838ecaa2641960c639494290687396a729c83439cf5294a41c1ac6a908420e0d53588531070ca9ac029883259c76354841c1ac6a90a420e2952580521061cb80ca99083439cb5410e31c18c92926518d0e72d52548c6873a6a529463435c85450c31a32e02a28618e0d64548320c706aa2c42a06386551601503192ce3b22a418e0d64548520c724a92c029063165c06550831a32e020aa018f10410c45048750208c090843b00c46048421c1ac6a9085a060d5358853d0306b1aa429681451c55310640c18c629284a0650515803150286392a629a81451c55314d40932e1318a4a050c73548525029238aa4292810d1c5650c940932e131ea2a063051580315038828cc018a8185145600c540e20a2b0062a069351580315030c28ac018a81a4145600c540c20a2b0062a04997098f215030b318a390a81435c85450f30c1ac8a90659860d5458854cc306b22a429661451c5540c630a18e4aa0869851471550434c306320a4992618c1456010530a18e4aa0a89851471550544c24cb84c829261431d15214930a88e2a90a49845471594424c24cb84c9a8a61941456010530e20a3300829861451580414c38828ac020a61a4d456010530c30a2b00829869051580414c30828ac020a61265c264c8530c2cc828e429861461145404c28a38aa620c418654d6010620a28e2aa06310619545803188388a8a8098041c85454048020e82a2982401061b5358041c430daa2c018e218514c6150310c28a830a61884e17688420c430a298c2a0221891486150110c28a830a608864452185304428c3aa809822186195404c110e10a4a02608859071501304434830a80982218654d6010410c52a4b00820851575104310430ab288218821c1548410c410b22e02086208619545803104324a92c018821a4105600c410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x49c204140200003200c00040a118098c51c8540a118099051c8530a108154d6010620a1081551600c620d00521c5404c110e0052185404c110c11655c0410c410d01525c0410c410a1185105600c410e0152105600c410
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
  | 6 => packedAt s5K6 (880+((h/16+packedAt s5K6 (768+(h % 16)*7) 7) % 82)*7) 7
  | 5 => packedAt s5K5 (31188+((h/339+packedAt s5K5 (27459+(h % 339)*11) 11) % 1624)*11) 11
  | 4 => packedAt s5K4 (56486+((h/448+packedAt s5K4 (51110+(h % 448)*12) 12) % 2362)*12) 12
  | 3 => packedAt s5K3 (5784+((h/37+packedAt s5K3 (5488+(h % 37)*8) 8) % 162)*8) 8
  | 2 => packedAt s5K2 (615+((h/3+packedAt s5K2 (600+(h % 3)*5) 5) % 17)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1ffff83fffffff03ff0787ffc3fffffdc0f1ff
  | 1 => 0xe07fffc0fff83ffc1ffff83ffc1fc0fe7f3e73
  | 2 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 4 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x208888820922100a541026481325450c050a5
  | 1 => 0x491411064920402c0a0a8809440482a81b2652
  | 2 => 0x852522121a4406554084d4826a412a0b058b18
  | 3 => 0xd659c4a49076ab9a73d04623b3980c33e80de0
  | 4 => 0x18618738e38733e39ce76730231030c3f6f000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8ece8e8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36705
namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1dac00018425600315393400400e4d20005ea0020029383d2a04e242843a8801b0000b800200000462c32600293c0241d456d54402800686243c6401ea8534d7917c4d32a0000000000000000fc30e08083040000102140008e0214000000405ff53017f94c05fd53017f14c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52017fcc803fe32017f4c803fc3201ffd4407fe5101ff54407fc51017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2004ff58e1006dfac708013fc63840097e31c200dffd4e1006ffca708037fd538401bfe29c200dff90e1006ffa8708037fc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc628401dffa94200cff94a10077faa508033fc528401bff994200cff8ca1006ffa6508033fc32840157eb0c200effd4610077fca30803bfd518401dfe28c200dffcc61006ffc6308037fd318401bfe18c200cffc8610007fc4308003fd2184019fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9042004ff08210027fe2108013f71084001fd884200bffd951005dfeca880037f65440013fb2a200bff9951001dfcca8802ffd65440177eb2a200bff1951001df8ca8802f7c65440073e32a200affd8d10055fec688003df63440016fb1a200aff98d10015fcc68802bfd63440157eb1a200aff18d10015f8c68802bdc63440056e31a200affd4d10057fca68802bfd5344015fe29a200aff90d10057fa868802bfc4344001ffb122000bfd8910007dec488002ef6244013ff3122001bf98910007fac488002fd6244013fe3122001bf18910007d8c488006ec6244017ffa922009ff9491005ffaa488027fc5244015ff9922009ff8c910057fa6488027fc3244017ffa8a200bff9451005ffaa28802ffc5144015ff98a200aff8c510057fa628802bfc3144013ff90a2000ff88510007ec4288003fd2144001fa90a2009ff0851005ffea088013fe5044017fea822004ff14110057fe6088013fe3044015fe9822004ff0c11004ffe4088013fe2044001fe9022004ff08110007fe2088003fb1044009ff0822004fd84110027feca08012ff6504009ff3282003bf99410026fcca0800e7e6504009feb282007bf59410026faca080027d6504009fe3282004bf19410027fec608012ff6304009ff3182002bf98c10027bcc60800ade6304009feb182006bf58c10027bac608002dd6304009fe3182004bf18c10037fea60801bfe530400dfea982006ff14c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004fb9881000ddcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902006ffcc81002ffc640801bfd320400bfe1902008bf9841003ffea20801ffe510400ffea882007ff14410037fe620801bfe310400dfe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x7ff304842bff1824215ff4c1210aff86090807ff2048403f79024201ff08121027fecb10012ff6588009ff32c4003bf99620027facb10052fd6588009fe32c4004bf19620027fec710012ff6388009ff31c4002bf98e20027fac71004efd6388009fe31c4004bf18e2009ffea71004ffe5388027fea9c4013ff14e2009ffc871004ffd4388027fe21c4001bf58a2000ffea510007fe5288003fea944001ff14a2000ffe6510007fe3288003fe9944001ff0ca20027fec310013fe61880017f30c4004ff58620005fac310013fc6188029ffa8c4014ff946200a7faa310053fc5188027ff98c4013ff8c62009ffa631004ffc3188003ff90c4001ff88620007dc4310007fd2188003fe10c4001fb08620025fcc110013ff5088009ff2844004ff54220027f8a110013ff3088009ff1844004ff4c220027f86110013ff2088009f79044001fec8220027f84110013f82088025ffb2a4012bfd9520006feca900027f6548025ff32a4003bf99520097faca9004afd6548025fe32a4003bf19520096f8ca9000e7c6548023ffb1a4011bfd8d2008ffcc69000afe6348023feb1a4011bf58d2008ff8c69000afc6348023ffa9a4011ff94d2008ffaa690047fc5348023ff21a4011ff50d2008ff88690012ff6248003ffa924001ff9492000ffaa490007fc5248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf18520097fea29004bfe5148025fea8a4012ff1452008ffe6290047fe3148023fe98a4011ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024012ffd4120027fca09004bfd5048009fe2824011ffcc120027fc6090047fd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048021ffb2e2010bfd9710087fccb8800efe65c4021feb2e2010bf59710087f8cb8800efc65c4011ffb1e2008bfd8f10047fcc78800afe63c4011feb1e2008bf58f10047f8c78800afc63c4011ffa9e2008ff94f10047faa788023fc53c4011ff21e2008ff50f10047f88788003ff62c40017fb16200fff98b1000dfcc588003fd62c40017eb16200fff18b1000df8c588043ff52c401fff2962010ff54b1007ff8a588023ff32c401fff1962008ff4cb1007ff86588043ff51c4021ff28e2010ff54710087f8a388023ff31c4011ff18e2008ff4c710047f8638803fff21c4001ff10e2000fd88710007fa4388003f521c401ffe10e2010ffd4310027fca188043fd50c4009fe2862008ffcc310027fc6188023fd30c4009fe186200fffc8310027fc4188003fd20c4009fe1062004ffd9610025fecb08013fe65840077f32c2004ff59610075facb08013fc65840097e32c2004ffd8e10025fec708013fe63840057f3
  | 2 => 0x96db0001bd000880000304ca001ca000000250ce30e0002b80000000000000000488f00d00000007f10380000000000000598000240008d4000000006260b117000000001ac00e2242980000000000226b0650a72000000010d9000801004004000000180240380400001003804004008000050020240180201400c0000c000004038000000000000000401000801002000010050000040380100000000017008018000020020000300100401000003000004008000000080080000400c0500c0000100000100004000000008014008000020080000600800000804022000000000000000200100000004001002000020040020000080600201c0700000000400800008004010000040080080800001c050020000100080100600000800000000008040040040b00000a0080000500000803806010018000010120080100500a0000500800000c0080300200001002000004008010000000180900000c01002000008038000060000080a002004000010020000100500200c0100801200004800000000000000020000000e00201c048060080100480000000001004000000008000000000000700c0140b8010000000000001a0000400000400c000010c7fecb10862ff6588431ff32c4203bf996210c6fccb1080e7e6588431feb2c4218bf59621006facb108027d6588431fe32c4203bf196210bffec71085eff638842fff31c4202bf98e210bffac71085efd638842ffe31c4202bf18e210bffea71085ffe538842ffea9c4217ff14e210bffc871085ffd438842ffe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe6510807fe3288403fe9944201ff0ca2100dfcc310863ff5188431ff28c4218ff546210c7f8a31085fff318842fff18c4217ff4c6210bff86310807ff2188403f790c4201fdc862100ff84310807f42188401ffb044200ff98221025fcc110803fd60884017eb044200ff182210c7fea110863fe5088431fea844218ff142210bffe611085ffe308842ffe9844217ff0c22100ffe4110807fc2088403f61044216ffd95210b5feca9085bfe65484077f32a4216ff595210b5faca9085bfc65484077e32a4215ffd8d210adfec690857fe63484057f31a4215ff58d210adfac690857fc63484057e31a4215ffd4d210affca690857fd534842bfe29a4215ff90d210affa8690857fc43484037fb124201ffd492100ffca490807fd5248403fe2924201ffcc92100ffc6490807fd3248403fe1924201bfd85210b7fea29085bfe514842dfea8a4216ff145210affe6290857fe314842bfe98a4215ff0c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c09085bff504842dff2824216ff541210b7f8a09085
  | 3 => 0x6000b10ba02e000001021962640012831c0000cc0db2b502000000000000007841d678000000004740000029c7d45e40028c054b68000000000022b800000ba0000b4694c49dd2545fc7705222d1887791e9e16524a4001d404c000003e43e06e40005000113a2e076684001cc8000004f0a605a8a8d3400000568f5dd50ee0007d0e812f748f78003d80000d0ef8000002340b800000fd8000003dc3f1a38000fe67a2195e000000001ad08e7e40030c10c68800000000000762b836600000000000da80044f00000019434000488dd8b60000004732e428641e121a0009d0000000008c9441105bc0017330800103000000000a38aa037194001fe000000000000000007e80016424b1a08e3c63b6d3c0000000000000000000000001c60005a12520b17628a19000100e3800000000999d02c84c8639a2b3a0b05214900a4d2000fc000000cbdd30000f4f895a800000ca99f8000010c0000003780000000000114c000003fa2704b0d90389f8004083184008f1bf0e6000983ee820f59e1a67000fa16c00000055965b7079b0f9b90006ea0000004e4f010141c020006a000000000002050c00000000031e486fcc00000000309e83d5000000740006a8e584381218c00041800000aea332aa0c4089b98b80000000000025a000ad8000003789400048c7800039b0000000000050839d178004c6001c0000000c348704c0000008500000000000000000ca00021263072950c1b89690213000770000000002eef216e00000000048000236368728005c8a08001d6000128000000000000007e228e70000003cc0011b1c26de0000a3207f0d70b02387fcd59ea2877b8fe8a042c0dcebc7b2ea680000b10000000016b1884ac4d8b3119420000003f05204d1f3338734f2e240001a85600000084000215800000182003ce000d11e997c001162090008780640000030eea00000073e000d320e1d4000000000009380012a6040011546c1a02c1649d8838e40003148c02a9343d187000214b1a430000bc00056edf8e01851171081a800000b391d800358411af0003d8890a11b80006c800000262000002a80000000000022e001782f50000000010c000bc87c3743ba3f88885400111c7581e0009720b341708398d8bc50409b800000000000cc0462485c80023e0480008fbd20fa92179bda5c5141850160000000000076cd25530840750b9911fb0d0000000457d8afc0018a0001b0000000002315f38a6080018796e2a0650000000000000037a0f60022f000000000f10000000000008a5480100045600000000000000ed0003460867901b3365a90e9050004c07a0003600000000044579e1ca2a8001406dcd21da5646bc4d42f6210a9778d54006d51ba4187e62d4b0562041e226186412391141a91c0000e7120764001968006481dc000006
  | 4 => 0x3716c4000000000000000008158ea68428005580000005c0000011980024e4591a417000000000000007d800000000949350002e6b821408f0000003a93a0d5089c626c540320e0abd308e746e11d0925f938000698111060e25781bcf92f46a298a02000000000e9343000c980000047e001451ba29c000000008a20000029f5600000027c6ecd69260000000003e440798cd1d7378179018d51384e4a745d0006ccdf0000bf4bc000000b200085800276226db800226462338002860008355b2fa0008e5d10001511111120875a20915800586348961ae2460008d00077c000000000002f42f00000000199464399038b50ac1ae8704f34e0003320f000062b49a9c24000001d5abb2f4519cf2c630010800000478a016103c7100000014400000083000788000e2000660000000000003ca24800230960448000000000000c544bb0030fa7e4b14003f425c0014c3f78945693d0d8882f259f15c2be000000b9000000a9000000e60d58000e0000fb8000c814890c5a1d235800414000000b8000794000002068dc000ae800404fd400002001188002f1760000000000e906495b55572d41573926d0000001265280011a800546000b61750000003329e2940006dab305000000000622000003000000001c000210879ec87907d0d8da00088c0011600000000049088304648001b0000000003bc78e6f9a4000000e080041a7c05d80000036cec5e0bf170c001d60000000017c230334bd8ac8001300680c2c185b1480e87100000000000020cb09f1890009097e1ea1e82f8002d05944540025a830bb9abac06a4000ff31
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10036df7158c10006de7158c10036dd7158c10036dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006de4158c10006dd4158c10006dc4158c10006df2158c10006dc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7358810014fe7358810004fd7358810014fc7358810026ef7258810006ef525881002eee5258810006ed525881002eec5258810006ef325881002eee3258810006ed325881002eec325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f51058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ee4358810006ed4358810006ec435881002eef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef3158810006ee3158810006ed3158810006ec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026e71058810026ee1058810026ed1058810026e51058810026ec105881007cff7688410024fe768841000cfd7688410024fc768841003d7e75884100057d75884100c67e65884100067d65884100bede6388410006dd638841000eee6288410006ed628841007ef66188410025fa7088410005f9708841007cff76484100b67e65484100067d65484100aede6348410006dd634841000eee6248410006ed624841007ef66148410025fb7644010006fb7644010004fb76440100077b75440100cf7875440100277a6544010027796544010007db73440100dfd87344010027da6344010027d96344010007eb7244010007e87244010027ea6244010027e96244010025fb7144010027f371440100d6fa6144010027f261440100cff251440100cff15144010
  | 1 => 0x8910014fe7358910004fd7358910014fc7358910006dc7358910014dc735891004cff7258910006ef7258910064ff7158910006f7715891007cff7058910006fb7058910005ee761891004eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc631891004fe5711891011eef611891011fe6101891011fe41018910064fe768851005d7e75885100057d75885100067f65885100c67c6588510006df63885100bedc6388510006ef628851000eec6288510005f67688510066f67688510117767588510007757588510007776588510117746588510007d7638851010fd4638851004df57288510007e7628851000ef6628851000ef4628851004fe4628851000ee46288510025f67088510025f47088510107e62088510107e42088510024fc76485100067f65485100b67c6548510006df63485100aedc6348510006ef624851000eec624851004fe42148510005fb7048510025f87048510025f4764851000ef47648510024f476485100077765485100ff746548510007d763485100f7d4634851004df77248510007e77248510007e7624851000ef6624851000ef4624851004fe46248510007f37048510025f67048510025f47048510007f0704851004fe7204851000cff764811004cfd764811000cfc76481100057f754811005d7c75481100067f65481100967c6548110006df634811008edc6348110006ef624811000eec6248110005f77148110005f47148110007e521481100067f65c41100867c65c4110006df63c4110046dc63c4110006ef62c411007eec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41100ef7865c4110007db63c41100e7d863c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c4110007f221c4110007f121c41100067f73594100067e73594100067d73594100067c73594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c325941003e7f71594100067e715941003e7d715941003e7c71594100067f31594100067e31594100067d31594100067c31594100067f21594100067c21594100267f70594100267e70594100267d70594100267c70594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267e10594100267d10594100267c1059410006df7558c10006de7558c10006dd7558c10006dc7558c10006d
  | 2 => 0x6de62d8d10006dc62d8d10127d610d8d10127d410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10126df71d8d10056de71d8d10056dd71d8d10056dc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d10126de70d8d10056dd70d8d10126dc70d8d10006df50d8d10126de50d8d10006dd50d8d10126dc50d8d10006df40d8d10126de40d8d10006dd40d8d10126dc40d8d10006df20d8d10126de20d8d10126dc20d8d10126de10d8d10056dd10d8d10126dc10d8d1000cfe76d89100067f65d89100067c65d8910006df63d8910006dc63d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910006ef52d891004eee52d8910006ed52d891004eec52d8910006ef32d891004eee32d8910006ed32d891004eec32d891000cfe71d8910024fd71d891000cfc71d891004eef21d8910024fe70d891004cfd70d8910024fc70d891004eef20d891004dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910107e771d8910107e610d8910107e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d8910106ef71d891004eee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d8910106ee70d8910006ed70d8910106ec70d8910006ef50d8910106ee50d8910006ed50d8910106ec50d8910006ef30d8910106ee30d8910006ed30d8910106ec30d8910106ee10d8910106ec10d89100057f755891005d7c75589100067f65589100067c6558910005df7358910055dc7358910006df6358910006dc635891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7358910006df7358910004df735
  | 3 => 0xc73d8b1007cfd72d8b10006f671d8b1007eef21d8b10006f970d8b10106ee20d8b10106ec20d8b1000cff7658b1007eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7358b10014fe7358b10004fd7358b10014fc7358b10006ef7258b10024fc7158b1007eec2158b1007eef2058b10024fd76887100857e75887100057d758871000eee6288710006ed6288710025fa7088710005f97088710025f5768871000ef57688710024f5768871013776758871000775758871000ef6628871007fe66288710007e5628871000ef46288710025f67088710007f27088710007f17088710025f47088710107e62088710107e4208871002cff7648710006ef624871000eec624871007fe42148710005f7764871002ef77648710007e77248710007e7624871000ef6624871000ef4624871007fe46248710025f67048710025f4704871007fe7204871000cff764831000cfc76483100057f75483100857c754831000eee6248310006ed6248310005f77148310005f47148310007e52148310027e82048310004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7358a10014fe7358a10004fd7358a10014fc7358a10026ef7258a10066ef2158a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a1004cfd76886100757e75886100057d7588610106ef628861000eec628861000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c4210027f271c421005d7e76d951005e7e76d951001c7e76d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067e62d95100067c62d951012f7610d951012f7410d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d951012e7f71d951005e7e71d951005e7d71d951005e7c71d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067c21d95100067f70d951012e7e70d951005e7d70d951012e7c70d95100067f30d951012e7e30d95100067d30d951012e7c30d95100067f20d951012e7e20d951012e7c20d951012e7e10d951005e7d10d951012e7c10d9510055de76d8d10056de76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10
  | 4 => 0x8620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7358620006df7358620004df7358620014fe7358620004fd7358620014fc7358620006dc7358620014dc7358620026f7715862004ef6215862004ef5215862004eec2158620024fc7058620026ef2058620026ed2058620026f61058620026f4105862015f6e75886200076d758862000dee718862000fe67188620107e66188620006ed6188620107e56188620107ea7088620105ed7088620007e9708862000eee608862000fea60886201557e76d95200967e76d952001c7e76d95200067f63d95200067e63d95200067d63d95200067c63d952014f6f21d952014f7b20d95201476e20d95201476c20d952014f7820d95200067f73d95200067e73d95200067d73d95200067c73d95200067e43d95200067d43d95200067c43d95201467f72d952014e7e72d952014e7d72d952014e7c72d952014e7f32d952014e7e32d952014e7d32d952014e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d952014e7f21d952014e7e21d952014e7d21d952014e7c21d952014e7f70d95201467e70d952014e7d70d95201467c70d95200067f30d95201467e30d95200067d30d95201467c30d952014e7f20d95201467e20d952014e7d20d95201467c20d95201467e10d95201467c10d95200067f65d85200067c65d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520004ff73d8520014fe73d8520004fd73d8520014fc73d8520024fd72d8520006f731d8520006f431d8520066f621d8520066f521d85200957e75985200057d75985200067f65985200067c6598520006f7619852004df970985200057f75585200957c75585200067f65585200067c6558520005df735852008ddc735852007dfb70585200067f65185200067c6518520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520004ff7318520014fe7318520004fd7318520014fc7318520024fd7218520006f73118520006f4311852002eef211852002ef6211852002ef52118520024fe7018520024fc701852011eee201852011eec2018520024ec76485200076f654852013f6c654852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb7048520025ee7048520025ec7048520007e87048520025e8704852000eef604852000feb60485200857e75d8b100057d75d8b1007eee62d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10004ff73d8b10014fe73d8b10004fd73d8b10014f
  | 5 => 0xc00802010054008010020300300004a0000002c0040040200200003c020000000000000100401c000050000180180200c0000000500200803801014000018150020000080b0000300000000000c008000020000280401800c0180000001c140000060040000300400000003010008020010020000200001c00402804000000068040040b00800000400400002000000000040140040000100a01800001000000008000020200100700800400000000034060020180000000200802c00005000028028050020300301600c028068000280000080b0080580680101a00801800020004220000580240200000001c040000000000380000e010000010020380180001e0080180000601400001010000000000100000000104e00006000000028008060000200080000e000030080180b0000001757f76596210c67f765962101c7f76596210067f63596210067e63596210067d63596210067c635962116f6f215962116f77215962116f74215962116f6c20596210067f73596210067e73596210067d73596210067c73596210067e43596210067d43596210067c435962116e7f725962116e7e725962116e7d725962116e7c725962116e7f325962116e7e325962116e7d325962116e7c32596210c67f715962116e7e715962116e7d715962116e7c71596210067f31596210067e31596210067d31596210067c315962116e7f215962116e7e215962116e7d215962116e7c21596210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c305962116e7f205962116e7e205962116e7d205962116e7c20596210c57e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067e65582210067d6558221004ff755822101cfe7558221004fd755822101cfc7558221004ff7358221014fe7358221004fd7358221014fc735822104eef215822104efa2058221106ec20582210c57e75182210057d75182210067e65182210067d65182210bdde7318221005dd7318221026fa6018221006f960182211676e75885210076d758852100dee718852100fe6718852100eef618852100fe76188521005ed7088521004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff73d8121014fe73d8121004fd73d8121014fc73d8121006fb50d8121006f850d812107efa20d8121006fb60981210057f75581210b57c7558121005df73581210addc73581210b57e75181210057d75181210adde7318121005dd7318121106ef6218121026fa6018121006f96018121004ff759862001cfe7598620004fd759862001cfc7598620004ff7398620014fe7398620004fd7398620014fc7398620026f6719862007ef6219862007ef52198620024fe709
  | 6 => 0x23d00030b00000284381160eb80232d02cf73c9b88000000001f635881b066b276d15efa3500000008c33e000000002e8aaf45a6200089000000674b00df308182000298002aba19df13b00046c7734c4bcd97170016434f061c3e6d4929a240009c381da804628000dcc000001026e0000004e755629000344c672e2451e0000f40001b000150d0600180800337e0af996b0005082480048622d8c8db43a205d3809000dad75bcc0df000001d94e29b000152000318aa4004bb001c0fa061ed5c8c954122000000000eeece001fc086000002ab0000000000000000000000030b714c8b9f58c09b600000096db793ec2eb7eb6714eee38d8fb0d2473e1210c41750d27580067a020a3bc9719bdd50835c1a59c37640b6aed8318415c2000ec0fd1ab0016f5ce2b2001579aa46b5416090e594ab6b480000000000361306368bd728800bd865dde136bb1bca110009cc002727000018b9c647a00093aad0000006c0000008bc000000cdde99d8033482800016862d450000de000e3600386708000002a4000d01b990c5fc31c4939504a2202eb5822ec4caf1ac00000000000000bfe0034a0ec3c921dd22feebcc461970ae7568400000000158980220000031d00000000178dd0355bf8002ecb79a78be0b87a000000000ae8738dd0000f0f0b699962087338a322b57580393facd0dc7bd93a06400000000e2e000155f6198c5f101e229000363410bb59c1df435391b4400000e48117bf000001c0908134bd474b450000005f9a13c0afda41c573e79486a040f8d6c3019a58aaa0bbd6f00eadc5c0852c4888000690000003eb6d0664cd1a226cf2b2ca991f426dd40025839e659a380c000000be8c9e7c0000004d796c246a72a2d43f82bad5198308f51f14da188327741d0511565122b48de003c08003f13083f2c75927113d0001e5350003ce0009b00066ead800156ec03d833a6743c6bc000000dbb3fb401026a1bc0028c000d2427800449724001ca0000009cba0800f0c2116d15a33da1951800b2108000328000000ab364000af800000b4e38911488dce092cc71e1b56cbaa30a8e81c06e540d660040080300202402800004008028010220040380000e0000100b01802005000002004000000040080000204205c048190000140200c002034000010020000100000004c0d800008018060000040280e8090000000000300e0000080000000000007002000000010040080600000a0f800801006000048000160040280001600c060000120100300c0000000001b00205c0001801e0040780a01403400001002000038010040380000403a0200580201e0000e8090060100100100e0000000b00800c02809020018010070000a004800014008030040000000000e0220180082602e004028010060000380300a00003002000010140010060
  | 7 => 0x9fc00048000349933360a3e20624af31529dc9abb5640008aa6e094e84000003296ac0000d883cd4160004fa9f1b71dd204df58aaf864f861dba0f256d9d789d528a8ba003624bd70d9809915cac4990003401c3d224b1266e90cf992907dd6fb5acbe8c183800456730c6a36000cb05a04ff20d6883a82764998003a226fcab749cd498ab06fc134c03501da124eeeb580364260418168c2d10d44cab273334a88c3c476980cb09431e7bbdb8c470e00001ff13d9abc11a800618000003c60005dc562465460e884b47ef82110b1e6000acdc4b5e0000665e98719a480de8002ca0018b3b9000f280019d1644e000000000383b95292f30a1d301e0380001890f4b84f3e383e9837091c3b6d4a7b576e39112a49a325f86c3d2c81824ba000cbb2004e934756b8200b6c4e086402ecc0039e73f2c5053536068fa001400001118fcf73de0008ebba54403c17b69294b80e897c7044bda71a312ed09d1acf034000fc80000044043800000efbde80058c250000160008f0002b5000074650007280000016da74000002fd000000000000006ecb779b17219489e8a77f6397297a234af1b88eb8007594e000000e60f4850e080004785241b0011f8000000d00014640c9d00002136c6fc0031dde4a6e0000000065e3414b0000014800a800b9041a8d791f08262970a87912b29dbc66c3764004d62ec92a234c61446400054c1405d225d282c01a80014a000961647226253b11498611822ba9000705696d04e095d1cc0058632a32c4071c5581713ac645703d9b6c66dc883e8f482de0ee189800001620000000002b2ff000178001b90000000012e17800129981000000b9195b18678002ea3a028d53b1106ebb9aa161800b24fc14d601bbe8f18a7162a40034aa506c1270cceec0a83535609b000f90000000015700000000091298000b530dc67efc000db9c84c894516dad7802d8844c91542845421cf56898000b7a4cc3a2cb3c300c849c5416aa1918903d36656000032de1001d6cff706aa98516c335808f835f68d91d28162e38ded20e31512af4c32f90e8973ddb28014994698f9000d98920d00966ba000004162ccc99ff0003c011e554500000017850aee00000000000199ad76464c534a9b0005740005a7607d98f1d364a6c400000000530001884f00009ef20c40d72000000fc0000001b000bf000000000000bd800535b44510000008e3d0c0000066d7100040ec331fc0013c9158f5d4000e3173ba2f5c001e400d1149a0b880000000000000000a72121bf800000000005022383aa2d0000000c400572965d8800000d2c0000030fc891b9b8040d4802800687000c5b18000001379a7000b3978e7e259ed771b705e6ad0e58000005cc00053b09e691080027c660000721aee1d85ed414cc14001fa3d68691b52d80083acc90b000d9
  | 8 => 0x52c35e0000045400000000000001de000242eba132f43241858589f35f051a455389d71c11000000a68bf00016a5b87299c2083b5e0c0061bf1f92370af25252a15b19ca75e0a1f0b61cc6f9374478387d198e36001e280000000000134634d34a70553f67d4e028700058c0000000000005cd3e883cc82951738d95139700006f02644ba02900da2151b263d9580040047154b5d000000000e127ee5dd2986e8b4b5d640022c000d28004b400000000682c38003498004ee001b1800581060f51dec06b5c004580000005f3fc0014f28e000001adef2db455d815a67156b92788d584d7000000522001e361b00000075315800000180005260380000016ea00001ec4908f82940040aa7dc6abe66235a0327b757b4c1900018ae580023b246b74000003080000001765a3b0d480005208d6900c83e000002d62af7d04810a000001291755cc8713a8b8bc485112a2c80000194c00000a55049550000012164966444c00033bb40019cba829e54ad107f67e000000002cc00163bb40006de0008012a1ac6032f6522593d3505b0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe6462d9521440499a8edb1a4288007391db7248510106723b6c490a2020de3721c121440010fd0dbaa40880031718f754811014e36316ea902202a87e87d9520440530f90fb2a408800317dd763481100062e3aec69022000c6f75d8920440018d8ebb1240880033518f71481100066a318e29022000ce7621c520440093c90e90a4088012b92192148110025f0402429022025c7a76d9710440499b4edb1e20880833a9db62c411000e753b0c58822000e686518b10440018bee739aca080038750c43594101953dc02e4b282004a78805c965040014bd06392ca080029760c72594100043f43864b28200087d870c9650400147d08192ca080028f610325941018d3cc04e2b282000a3e84cc5650400147b0998aca080021fa1c31594100043ec3862b28200787e87c8565040010fb0f90aca0800297a0f21594100052ec1e42b282004a7a8008565040014f30010aca0800317dd67558c100064eba0e8b182000e1f5495163040615af02b92c608002b52057258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c100046f438a4b1820008dd87149630400153d08292c608002a76105258c100046f43884b1820008dd8710963040014bd0a212c608002976144258c1017d6cc04e2b182000e575194563040011bf0ea8ac60801a3721d5158c100054fc22a2b182000a9c84545630400d1bd0fa0ac6080023761f4158c100052f42882b182000a5d8510563040095b50020ac608002b66004158c100346f43e42b1820008dd87c8563040014bd0b90ac608002976172158c100054f42642b182000a9d84c8563040095b50010ac608002b66002158c100247c402eab1020008f4815cd62040091dd0fa92c4080123b21d52588100247743e64b1020048ec874c962040015c902992c408002bae01755881002574402eab102000ace831d5620400159b063aac408002b9e0573588100057240ae6b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102000e4f5394d6204001d1a8621ac4080029ba16715881000536c2ce2b102000e6751945620400159f06a8ac408002b320d515881002575400a2b102000ae980145620400155d0998ac408002ab61331588100053742862b102000a6d850c562040095d50018ac408002ba60031588100043fc32eb1082000c5e635d6210405b8dcc4bac42080ba1fe1d658841016c3ec3acb1082000c5e7558e21040018baeab1c42080123be1d6288410006373aac51082000c6d7558a21040019d2c4b8442080031e1d776440100066c39eec8802000c7b85dd910040018f10bbb2200800336e0f76440100066c41eec8802000ceb82dd910040019d105bb220080031eddb75440100066dbb6e68802000ceb76dc910040019d6ec39220080035a1d47244010
  | 1 => 0xd0931ec488002ab61263d891000537c2ac7b122000a6c8558f624400155f08b1ec488002ab21163d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d89100056741cebb122000acd839d762440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf6244001c9ea729ec488003a350c43d891000537c2ae3b122000a6c855c7624400159f06b8ec488002b320d71d891000567c1aa3b122000acc83547624400155d0998ec488002ab61331d89100053742863b122000a6d850c762440014dd0bb86c4880029b61770d89100053742e61b122000a6d85cc362440070fd0dbaac4880031b18b75589100043f43ecab122000c5c73d9562440010fd0e32ac488003171cc65589100146f436e6b122000c5f65dcd62440018b8cbb9ac4880033318b73589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d62440070fd0fbaac48800237e0d75589100146e41aeab1220008ef825d562440011f700baac4880021fa1c75589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100043fc2ae6b12200387c855cd624400117f08b9ac4880d22f211735891000477c12e6b1220008f7815cd62440011bd0e39ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880031bdd77258910006363aee4b122000ccf73dc96244001998e7b92c488003351cf71589100063c3aee0b122000c6e76d946244001ccae3b28c4880023b61e65189100053742cca3122000ace83994624400159b07328c4880023be1d651891000567c1aca3122000acc8359462440015d700b28c4880029ba186518910006373b0ca3122000e66711946244001ccae2328c488003339db631891000727b2ec63122000e4c65d8c6244001d1ec9b18c488003b15c7631891000476c3cc63122000a6e8598c62440014db0b318c488002aba12631891000556c24c63122000ace8398c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488002b9e05631891000567430c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244001d8ce2318c488003b15c4631891019f63080c63122033ec41018c62440310f90cbac42880031718d758851016e36312eb10a200087f87d9621440170fb0fb2c4288003179d763885100062ebaec710a2000c6e75d8a21440018daebb1442880033518e768851016f32312eb10a2000e6462d962144001d88c5b1c4288006b9a1b6288510006733b6c510a2000e6421d9521440419d0e1b1242880031e197704851012e3a3b6ca90a2000
  | 2 => 0xb6548520146b4386ca90a400f8ee871852148001cceca30a42900127aa1f70485200043ec3cebb16200387f875d762c40070fd0bb9ec5880021f61773d8b101a45f426e7b1620008bd84dcf62c40011bf06baac58800a3720d7558b1016e3abb2eb10e20048ee87d8921c40017c301b1243880127921d2148310025f040242906200387e87dd562840510fd0e3aac5080021fe157358a1001c3e42ae6b1420008bf845cd628406917908b9ac5080133a1c162486100043ec3cc7b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200087f8758f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f6544001c38c831eca8800297a0e62d95100052ec1cc5b2a2000c5d731cf6544001c3a8621eca8800297a0e72d95100052ec1ce5b2a2037a76811cb654404b4eb02396ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880028fa1331d95100051ec2663b2a200087e870c765440170fb0e18eca880961fa1f21d95100043ec3e43b2a2000a5e83c8765440014bb0790eca880669da0770d95100043f43e61b2a200087d87cc365440018bcedb2ec6880023761e65d8d100052f42ccbb1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a20008df87597634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc8259763440014bd0c32ec688003179d865d8d100070fb2ec9b1a2000e1c65d9363440011bb0f326c68800297a1664d8d100052ec2cc9b1a2000a9e84993634400159d05326c688002b360a64d8d100046fc3ac9b1a2000a5f8559363440014b90ab26c688002b3e0964d8d1000566412c9b1a2000a9e86193634400193cec326c68800387d9464d8d100070e328c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000c5d751d7634400193ee93a6c68800387d5254d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d101b56b408e5b1a2024ad5811cb63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b634406b1bf0ea8ec6880923721d51d8d100054fc22a3b1a2000a9c8454763440491bd0fa0ec6880023761f41d8d100052f42883b1a2000a5d8510763440491bd0f90ec6880023761f21d8d100052f42e43b1a2000a5d85c87634400153d0990ec688002a761321d8d100dd6b40ee1b1a2000a5e85d0363440014bb0ba06c68800e3be1d52d891001477c3a65b122000ace83997624400159b0732ec488002b3e0d65d89100056641acbb122000e4f65d8f6244001c98cbb1ec488003a3d9363d89100053742cc7b122000a6d8598f624400155
  | 3 => 0x858001f20009f89c0361440181800004010000108c070020000c028000200002004010020082800002058000582006800060020080006000008120601c0480c0180e008140d09e02804058001101e010120280a008000400000010008000480000808058080000c0000e0000001008000260180a0100000002098460100000810028040000e018060100000016038060700e00002020080900c020000000a02812018160480000832000000801c000000200a0c80601020000100100601800078000100609800000000000401006010020481603800158000200002806120000100003800000000000e0184a000040004a04808008020200e01802008120180000004000001000002038020000087e87d8d658840147d09b1acb108028f61363596210051f424c6b2c4200a3d8498d65884010fd0e31acb108028fa1273596210051ec24e6b2c4200c5f739cd65884018bae639acb108038750c43596210051f42662b2c4200a3d84cc565884010fd0e18acb108b61f61c31596210052f41ce0b2c4200a5d839c1658845b4ed03382cb1088a9d606705962100537c12e0b2c422da6c825c165884010fd0f982cb108021f61f30596210051f42060b2c4200a3d840c165884014ed02182cb108029d60430596211763b38ccb304420387f865d460884010fb0f328c110803179ce65182210043fc3aca3044200c5e7359460884018bccab98c1108031759573182210047dc3ac0304422dc6e765d6214845bacce2bac42908063b219708852110674302e110a42008df835d760484051b906baec0908023ee1d60181210053c42ac030242008df835d661880051b906bacc31000e1fa1f75586200046fc1aeab0c40028dc835d561880051bd0fb9ac31000317dd773586200062e3aee6b0c4000c9f74dcd61880010ff0ab9ac31000e1f21573586200045fc22e6b0c40348bc845cd61880018beea39ac310003171d473586200064fba0e6b0c4000c9c741cd61880471df0eb0c43100035a5d570886200043ec3cc7b2a400087f8758f654800147f08b1eca900028f21163d95200053bc0ac7b2a4000a748158f654800147d0831eca900028f61063d95200062fb9ce7b2a4000a3e841cf654800147b0839eca90003175cc73d95200070ea1887b2a4000a5e83dc765480014bb07b8eca900a69ba0871d952014536c10e3b2a4000a3e84cc7654800147b0998eca900021fa1c31d95200043ec3863b2a402987e87cc365480010fb0f986ca9000a37a0f75d85200046ec1eebb0a4000ab684cc761480070fd0dbaac2900a21f21b75585200043f43ecab0a4000c5c73d9561480010fd0e32ac290003171cc65585201ce3db80cab0a4000c5f65dcd61480018b8cbb9ac2900e31b5c865185200047bc3ac230a4000ad483584614800156d09988c2900a31b1d
  | 4 => 0x200002da020006907521c120f215f3c9094ce0c18000007f54a3ea0005896904e000e917ba0c000381da2ea26cef51f0f24f8e418d000382bc000000776941bf2a50000012f0000009c09d00036c7885500e3e0000691f4406000000005447a05a000000000002e8518e64002860f88f40000062800202000000001e73845088e800109054ee1fb1290001f9c01c000000000000000e30723d0000438000002644a1ee000684838732b63662680010470c40111008000e98ec33e0cc2b9bb34b7a8ed5733fc210f60cfb45314e480f0173f88800005e000da1530260dcca80c2f66a4365af8786a24d0da8880908ec0035400037137082668b58030241b0938811a1778110cb22c0004a8000001e8338b9076560ae14d26202c3040003c3585a07d2d8000950190001280e8000003d8ac952000360000003de4a4bc8a0000330f0157000408bb136306594c28f73a0198cb0002120000000031c20c7e1492e4000b180000c74e6754884137c911dd4061a0cc8f2074414c59860005a02fd6400000000156000000001d100000018800373000000000002340006b0e80ba5e8460003282e0000003c0008002764c011808a80124450003360005c4be834000610003c2656000003221dc000000001580000017e0007fcbc3ed6d8d340006475eecdf102e00000000000000f45e30003cc388b7b706ace520600000000133000000000003d66aa001af1862da00000000000001c53ef814be0003206c2290a70284d0638002d5574d98a30540804994e000300000003ac498000b52822b8000af0000243f01634e6e4029d73f4260b4c0011e3a01800035a7d0d21cd2e05f2f30eebf0494591983b6520fb8e12e21bce08d9160039021e20c23702584c000624e20ab1e5694ca0292fa5dcaa95e05c7f40109786a3fc0686d9db10c0880034646e6994729e6f87d8e6288470431233b02408d5ce1b4318785b127a180000ad25a7e4754e30f94900e0000da73c5fc263ca3acf2ce72c04008f0a68000000009f0505b8001ba9582ec000651c41140000025c3385c16d0000403e0a8324000a61202f1484e58d13604b0000002cc000000cd2176208cc00208000f98a589e00000000228460530e89160000000000000085021c02678640be0000002a1b72b47362018121a45c5b9620000006480002d292000533ad4540019d00011c320b32247b4c00a394a6d4000622101a80008e000000448000005e83c0118be000510003782d8000de00072e0000000063cef9e6800000a58002fe000520d500000000000274680c10003586e8000d403e6c8000003266983dd1cafc4020009ca6a7c0050c42d420242a003ec514f91c72640006b85b1d201e2e9132c2396490963a80e0001fc010390000630005bc95897185084ec98413c43e3f95432e7a4e60000f6304
  | 5 => 0x180072e8c60ea0000f416000118000b387619e40cea91b3506b89e02b3442a84895030e3b81690ea34394ca4fd1bf108000360b232abbca11c743c1a1d4bfe4362f0391a03d4644a91ba464854001de138280581da4e464d0c37a2
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2000417e61731cd658840105f985cc73d9520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x138c
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138e
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0xb0c
  | 22 => 0xb0e
  | 23 => 0x140c
  | 24 => 0x140e
  | 25 => 0x94056
  | 26 => 0x95394
  | 27 => 0x94054
  | 28 => 0x138954
  | 29 => 0x138956
  | 30 => 0xb0954
  | 31 => 0xb0956
  | 32 => 0x1409
  | 33 => 0x140954
  | 34 => 0x140956
  | 35 => 0x209
  | 36 => 0x1449
  | 37 => 0x14c9
  | 38 => 0x141396
  | 39 => 0xb0996
  | 40 => 0x1649
  | 41 => 0x134b
  | 42 => 0x14b
  | 43 => 0x141296
  | 44 => 0x140b16
  | 45 => 0xbcb
  | 46 => 0x19cb
  | 47 => 0x4954
  | 48 => 0x5554
  | 49 => 0x4956
  | 50 => 0x5516
  | 51 => 0x24211
  | 52 => 0x5
  | 53 => 0x24e
  | 54 => 0x95414
  | 55 => 0x95416
  | 56 => 0x449
  | 57 => 0x15393
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 568
  | 6 => 973
  | 5 => 519
  | 4 => 2
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
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (23854+((h/258+packedAt gbK7 (21016+(h % 258)*11) 11) % 1239)*11) 11
  | 6 => packedAt gbK6 (51137+((h/403+packedAt gbK6 (46704+(h % 403)*11) 11) % 1599)*11) 11
  | 5 => packedAt gbK5 (32681+((h/206+packedAt gbK5 (30621+(h % 206)*10) 10) % 819)*11) 11
  | 4 => packedAt gbK4 (142+((h/1+packedAt gbK4 (140+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe03ff80781fffc0fffffffd19f3e3dc0f1ff
  | 1 => 0xfffc0fffffe07fff03fc03fee68d1ce7f3e73
  | 2 => 0xf07fff0007fff83fffc1ffc03070e1f387cf9c
  | 3 => 0x7ffffff800003ffffe00003f80fe03f80fe0
  | 4 => 0x7fffffffffffc0000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10a0052841004a480252551500830614c050a5
  | 1 => 0xd02c0530aa20495102480aa862850c81b2652
  | 2 => 0xa0556a0084d59026ac812a80b050a163058b18
  | 3 => 0x8479b39dd010c23bcf3803033b80fa03e80de0
  | 4 => 0x87e3ce6e779e70086100c0c3dfd0003f6f000
  | 5 => 0xce10200700610403082030303f7efdbc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36705
namespace PEqualNP.Outside.L_meta_36705
open PEqualNP.Outside.L_meta_36705.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 551 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)))) (concat (concat (concat bs3_4_288 bs3_4_320) (concat bs3_4_352 bs3_4_384)) (concat (concat bs3_4_416 bs3_4_448) (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 666 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
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
theorem bs4_4_544 : Interval s4Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 551 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)))) (concat (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384)) (concat (concat bs4_4_416 bs4_4_448) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 666 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
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
theorem bgb_4_0 : Interval gbAtlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2 := bgb_4_0
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
theorem bgb_5_512 : Interval gbAtlas 5 512 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 519 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)))))
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
theorem bgb_6_960 : Interval gbAtlas 6 960 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 973 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)))))
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
theorem bgb_7_544 : Interval gbAtlas 7 544 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 568 := (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8eeeaeae8ece8e8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36705.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.or,[0,7]⟩,⟨.and,[5,6]⟩,⟨.or,[1,9]⟩,⟨.and,[8,10]⟩,⟨.or,[5,6]⟩,⟨.and,[1,12]⟩,⟨.or,[0,13]⟩,⟨.or,[2,11]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36705

open PEqualNP.Outside.L_meta_36705 in
theorem PEqualNP.Outside.L_meta_36705 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3974686888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
