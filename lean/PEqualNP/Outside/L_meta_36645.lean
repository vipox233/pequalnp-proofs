import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36645.Model
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


end PEqualNP.Outside.L_meta_36645.Model

namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
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

def SBf (j : Nat) : Nat := [5, 4, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36645

namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
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
end PEqualNP.Outside.L_meta_36645
namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
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
  | 2 => 0xf807f807f807ffffffe03f80fe03fffff318ff
  | 3 => 0xfff80007fffff807ffffc000fffff80ffc1fc7
  | 4 => 0xfffffff80007fff807ffffff0003fff01fe0f8
  | 5 => 0xfffffffffff8000007fffffffffc00001fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x590848304850889090a2c59516545a95256b5b
  | 2 => 0xaf4295529533952523d02ab0aac2af2e5318ad
  | 3 => 0x3256c6a4e4a5247645756044cd9b318b9c15c6
  | 4 => 0xc464e4c6c6c646447679b3668113c5c31ea0f0
  | 5 => 0x787070707078787879e3c78f1e2060c1bde00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000aaaaaa00a0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36645
namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
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
end PEqualNP.Outside.L_meta_36645
namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a51a440000000aa8003021b0a80026000c4920e28e210000023524c7813200000007c3173450022009cc163a015003c0870b48008001000004040300c040102043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3600009c003400020000985600000076141ab600000000000000964200060000000000004808ac8e16705a72a60000380090b000ae4c006c00b200005494001c5800005c32b43a104e00248a26122c008c646a0c4a827c0062004000222e8400000000000092007400a088500000003e00000000007a0e00000004a400807e006886182800005e0a20a2a860aa9a9e7866440052000000303c1e002a000000466e000600010600010003051402010504000003000000000200020000000b00b7a92876c5250ebea6a15714d42d6a10853f544ca78a8995b94b41b6a96835e53906baa720db94a41b6a94835e53106baa620d794331aea9c633f544c678a898dbd4931b6292637b504c6f0a098e7d5131ce2a263cf524c798a498f5d4531eda82635c504c7b0a098d614131af298633e54c867aa990cf952219eaa4435e53886baa710d794c21aea98435e53d02baa7a057d4d40ae29a816f52502d8a4a05dd4540ba28a816e52102daa4204f952309eaa4616e528c2daa5186795230ceaa461ce528c39aa5185754630af284615d510c2bca0187694030af29e415d53c827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca7885754f10ec186215f53842b8a7084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa408760c010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xce00648002a000a318d4210b0c5414931c6d50504c7185414131d2d48504c7485214131c3952528c259650c010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2724+((h/30+packedAt s3K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s3K3 (312+((h/2+packedAt s3K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff81ffffffffffe07ffffe03fffffffe3f8fff
  | 1 => 0x3ffffff81fffffff81f03fffff03ffffc8fe3f
  | 2 => 0x3ffe03ffe03f81fffe003ffc1ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80a428890489204016524a41254431541384d5
  | 1 => 0x15085110c91248a580a414964a234aa8c83a2a
  | 2 => 0xa6149aa243a42b6aaa0a275913e91c0d70d34c
  | 4 => 0x3459634492074db34d3c81921cb38831ed03b0
  | 5 => 0x386183871c3871dc71cf39e380c210c1beec00
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888eaeac8c8a8a88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36645
namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
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
end PEqualNP.Outside.L_meta_36645
namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef19261dc324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea9441ee42883da85107bcca20f6194417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107b90820f6a1041ef32083d864105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dcc410fa188217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52107dca420db94841bea9083ed52106daa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331bf296637d52cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c63de438c7ba8718df94a31f7294636e528c6faa518fb54a31b6a9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f721243ed42487de6490fb0c921fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf29681ee52d02dca5a05f54b40f6a96816d52d037c85a06f10b40bf28
  | 2 => 0x1e0001f93f12d000000f88000f00f0002401b4000e29810fa7b47ca5d26a000000003e00d400000000000078004102486e00000048800000000000eaa4328c0012d00006857cfc8ca1d40386c800380000581a33a2048000000000008699502e8f4000000000003d86e4608451a800154000f4000000000001500003f8001a402c1900016a4a03e8000000000000000700000126a1c46c2cca20e1000000000003a47f0001df000890cd0580006e0000001182010217622a2044f91a00024c0000000035d2b0001140000014100055c000000000ac001030000006428523a000e480017c7d4e10000000c0001604823440a87f4be459480f83284e49a1aa0181cd3f8ff000000000002d00011b8590005145900018e53cf7124270000000000164c000000000000001b4000000000001a40006b0004da00000000000001028000003882a0000002610692f3f47980007a3149b00000043c00000148000010240000b491d0c90b000918538e70005f8050880343393987724e0013e00000000000186000894000000de3187d800000000cf8004f2000d81a6044839490000000000000027c0000000000018c198004ee084000000000006f0002380012493d10c000000004004087980031e5b80000000000000000220000001f411c00000000000721100000002ec0000008c00000000208000000000007ed01000000000a890c2240000000000000060800001006004010000020040000000400000800000000028060000000100000c010008060020040000100200402000002010010000040040100000000003000000008000000000040100000000001000004000008060000000000000000000000000000010000000000100500e000000000000000300300000400003002010000000020000000200a0000080400a0000100000001c0100300e0080000300400802000000000008010060180000c00200000007000018000000040000000000200801001000008000030000080080400201800004000000008000000000000200200c0000000400001001000000010010080040000100200400801000014000000060000180000e01800001000014000000020000200200001c000000000080200100000c000000020100100000000000800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0xf2000d78000002ac0987500000000000000000000000000000000000000012800350140de0820000012d800000000002670006e8d0000000a5000216048000f2000000534000e8000000000001fa0011f23b4d200000000000525039b20005c40000000000000062000000000000009c4658000000010189500000000000000594000003980006480000020caa0000009d4000000002b4290000003a40017506455899a100007f400000424000000001ec000d08b4246000000df000000000431e86340003133000c002392da0000028c00095432a8b1347f8000000d828c00000000000000b70008cce800052a9452a27a00000000125478264000000000012284c35a2f47326e4cc00000000000000ac2272940000000030a4280000000000000000514178001c7000000d48060000200018000000044a820000000021b0ae8a800000000000000002aa2a0000003728b00298c022274570b82843c0000000e088880a232fe000000000001d82505d0b88a400000000000940d800000000000000001048191d6375438e40005cc11a880f80000028f000000d10002c28c8001db3ba000800450001d0000000007180000000000143000000770000bc0960000024a0008680c15c45c00000000000000000000000746a8000006252203b000608c9000000158001b733a00000044000000000c209a0014b0003200009b2524de72c000000d60006a0ba0000012c17d0004ece51b149c2c4300002cc000000000000000000020c000000000000013c0000000000000016a00078a0618a00000000000000a38a510a000950000000000000000000000000000000420000000000002d00022c000000000000024c0540006800000079c7e0c441670c0000004c0b0000000000000009144c4453d829506234178a40007d8001290005ec0000000000000000000000a70cf08e00000000484a44000382649f5310000be93c00000172001320001de620438680000000000000000000000000a04000004b20000022b256000579e9442001340000007ac4e1f32d238c668f70000001400009c000f520f0000000015b0a66b0000000006d8cb800000000ba0000000000098e3c047800162000805468a2470000000cc0000000000042e000560000000f400000000000e700021000035055000000d70002ba000289bf0000000011b0e4000002184b8000000004e8438000000005e8000d3316830332314d4000a580000046400000000000f100012878c0000033600149a8912e0000000022e00000000000000001180804b8760004bc7fc002531ea450ac869000000700960000012400034e0000000000000000000240000000000000000006d00084c000000004240001f000000f28003e4000002760007dcea0000000dc0489b00
  | 4 => 0x4744f00021d000124001990005ac0000020a9c12b93121e7105480032c6100001c3ac184ef0e507400000000000000000000000000018745a001050000001040d83e07250cd59782ee6d4000000004dd30800000008e68000000000000027e00000284000000ce1210002800016300000000000000000df04f020000771d324c41d40228000590b780000044c0014000054c0026b000000001da0000000019300060caf05b2a45c8f60000004e8000004c60011fa14000000cf00052e87c6022f00000000000186000000670000013900012000000000000764000002ce0000021513c92ce080004e000000000000000000007e000be000000000000b6000000d98002b40001000000000000000000000a61a5000000001700000000000014c000000000848d0f791f000000000004c0000000000004b050800000000000000005e45f8003b0000c880d000000de8001da0d8000000e236c1728e0009940000000075c47800000000791f839e0000a1e12d8000000000006ec00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6310c31d548c430c7550310c31d54cc03097d95300c31d544c030b5185300c27b654c0308f99353c823d64d4f209d98753c827561d4f208f99053c823d6414f20cb55321c832d5448720ba18121c825e63d52209758f548832d62952209798c548825d63152208f993538823d64d4e20c7952538831d5494e20c7951538831d5454e20d3d89538823e6414e208f590538832e5490a20b318d428832e54cca20ab590328832e540ca20d354c32882ad6408620ab593208826d629512097d8d544825c63551209dd85544827461551208fd91534823c6454d209bd8953482776154d209d185534823e6414d208f590534823e64145208f590514826e65c8520ba181214825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f59053082766114c209d584530823e64948208f592520826d6590820b318d420826d650c820ab59032082e9600c8208fd91510823c645442097d8d510825c63544209b59621082ad64084208f992500823d64940209798e500825d6394020ab593200826f65480209ed95200825e63953109758e54c426e62153109b58854c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c423f6454b108f19152c425f6354b109718d52c423e6414b108f59052c426e62952109b58a548425e63152109758c548423f6454e108f191538426f6254e109b189538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6494a108f592528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427b60549109b994524432f5414910cb150524434f5314910d314c524436852c4110d514e104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436860548108f990520423d64148109798c520425d63148109b988520435553cc4109d594310436952c80109e594200427965840109dd9510042d463440109ed9510042e86244010
  | 1 => 0xc65d63951319bd89544c66c62551319ed81544c67860551318f990524c63d64149318f990504c63d64141319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c6cc6250c318fd91520c63c6454831a7590320c6d5610c8318f992510c63d6494431a7593310c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c86cc6350b21ab59032c863e64943218f59250c865e63943219758e50c865e63d52219758f548863e64d4e218f593538863e6494e218f592538863f64542218f191508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544872d6215121c7d53534871c54d4d21d358b534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534872c54909219b19542486cc63509219b997324872c54cc921ab590324872c540c921d3d4c324873b54d4121ce153504875b53d4121d614f504873b5414121ce150504875b5314121d614c504876a4214121da508504876b3214121da0c8504876a21141218f596540863e64150219b988540863e64d4c218f593530866e62d4c218f990530863d6414c219e98053086796014c21cb553210866f6548421cb55121086e860484219dd9521086ac6250f4097d8d52d025c6354b40d3d8d52d034c6354b40cbd0d52d032d4354b40cb54a42d032d5210b40a758f41d032d52d0740cb54941d029c6350a4097d8d519025c6354640ab58841902ad62d02408f99743502ac6250d408f994425026e62145409b588515023e65d0540a758f415026f6254c409b189531034f6254c40d3189531023d6590c40c754e431031d5310c40c754f421023f6550840a718d421031d53508408f596411031d5390440c754c41102ad6210440c754f40102ad62d00408fd95401031d53500409ed95401026e62153309b58854cc2cc6250f308fd9152cc23c6454b30a759032cc23e64947308f59251cc26e62947309b58a51cc29d64cc7309b98b548c26d62d52308f992528c23d6494a308fd91518c23c64546308f992544c26e62951309b58a544c27661951309d586544c26f62551309b189544c27761551309d185544c23e6515130c758c544c31c5490d3097195434c2cc6250d30cbd53524c32c54d4930cbd50524c32c5414930c7152324c29d640c930c7150324c34f520c930cdd53514c33454d4530d9d4b514c36452d4530cdd50514c3345414530d9d48514c3645214530d590c514c3554314530d58c8514c354321453097997314c29d64cc530d5147314c354514c530d5146304c23d65950308f990540c25e63150309759
  | 2 => 0xe326514e00b41e20002516226a4ecd2887000000e61d141c0001199a2a0000281030001e8001ce0003ec8681200000000000316358b38c315200019000000450000003d667000000000480000001cc12c700000e443c0009233e0003783503e000a71ef0000000a800014000159fe20a678001c500031891800122000550bf2247a89600040c680461d81dc558001cf1464d8748e211084ca8800172568d19fa1a846cc50e80000000f000000044001e7044674589424322982b00d000460000002c80009988d2f8000668000001108e9193f83609e82f06257047000132000688000000000020127e0005d0003e00000007f0f837c0014100057c0000000041c0000317c00000000290550001c8000000ca0d20ea4acc61cd354634fc8c72b00080900c02000000000602400010010000000000010010000300808018010000600c0100c090000105408000100140c0000000013000000000104c0502000004000201100c000340101c04000050540400003000000000800000034050140202402014090140d00001008000240f004000040101c0401003028000340001c00014050080001000000020080500001024000601504404018010000001406000060140a004040000302800014000100d00800000130000500800000000480703018000010000602c00000060380504000000040040b000010300200800004020026e62946439b58a5190e6f62542439b1895090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f4297d8d5190a5c63546429798e5090a5d63942428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7a60153329e58054cca3e64947328f59251cca3f64543328f19150cca7661152329d584548ca3f64546328f191518ca3e64942328f592508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320ca6f6254f419b18953d074f6254f41d318953d071d5390f41c754c43d071d53d0b41a718d42d071d5350b41ab189439069d63d06419bd89509066c62542418f994435063e65d0941a718d425065e63141419758c505063f6550c41ab189431065f63548419718d521074f6354841d318d521072f4354841cb50d521063d6590841cb54a421072d5210841a758f411072d52d04418fd95411072d52504419dd95411066e62d52319b58b548c71d63952319b988548c66d6215231c7952438c6cc6250e31cb952528c72d5494a31cb951528c72d5454a31c7952328c69d640ca31c7950328c74d520ca31a7593318
  | 3 => 0x360ec000ea0530001cc00000040000c8a0a00074000137000000148383365a0a200010a15c00000226364f18281343fc8f8003b800000000000328241a429a000570b60002acc488b0000c0f604235e0b43197325e27c808000002bc208000dc458e39a90004c904904378000cc9ed0c40002c2100920f8000000c84983d8001444e80004310c000000000000008d0c2000278001b91660006a8f61983a8949742140007f1c1408000541151962742c990000000001881f44e4411080ba0001380000000000177106100109d705c580ea825000000ad88f0000007a81332a59400152000780230000000007600042e2f4a981c212708800663bc49cf12050ce3c90612e0fa55c9285401c0003c0f0204798b094b3b6324ec8002943e41a12d35a0009c1e9330378af0000000000020b0002ec000ef01e000000e70000004a16900045cd302c3a44f0000001b8020000fc0002c8001b3000848940ad392000000243e233c0017f2806e8c91e50001b08715d000000de93e10051c4b8960000000007430406c830bc0e281c038004300005294c0000002e1c30000000000909e728f98000b6001000000ca80800000032178001b000a0006999737600000000120000a79842f40749a03c2fc000daa0f2602b00011c1c62c00002636e604f70183ee6fc0000c114000000000003042900008a5b05201707e0000106b000144d08000000000006937000000000000000ed1fd0005d400170000000fb0002da820000ed0000000000008e2dc001660004c43008100074c6209828c1e4d88e53d02e00d06d4225e4a496f2e43e000877000154720a01b65d81509c072130640d72f04a8000e10003682d0842201a00007e31c000eb180076658d616e3e83f4df0ce0000009080013663c001b43446a0c280007a340d58dd3be138be96b3e4784db0041d600000000074000000003ba0ccb885f1ee050b5095000850910000006b8001e40007190a8a10e024c00000000858bd8f4364000600003ea50d068002167110d10c3fe72c0b203248018059863065542680018a000fc0001e661c8886116a564d380014e000000370001a8001fb020224b191
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4400000175402c00ca20000e3c44cc0901c9006505601592341840020041038318c6255032a18e4a9887a0d0c735484210706b1aa5a0883431c9639523183aed2a06518d0c735885448616bb0a819243521cd4214121a52e8190a090e2954181210868639aa4216818358d52d0740a18e4a98862060d535884110306a9ac5a0081431c9631513083aec2a064985447250c514c28aba06428a618559051cc530c2aa830a60186295418121c828639ac52a4410b5da540ca20
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xd1080c8758d52d044180c8758d52d074080c8754d621044080c8754d62d0040
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffe07ffffff81ffc0fffff83ffffce3f1ff
  | 1 => 0xe07ffff81ffffffe07fff81fffc1ffff3e3e3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 4 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x220a42310489410059502a31281322a860d0d5
  | 1 => 0x49142440c91220960289510a524055510e262a
  | 2 => 0x8526a89243a426aaa8289d489ea4181b834b4c
  | 3 => 0x1658d12492074b4d34f20610e5398062f40db0
  | 4 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888eca8e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36645
namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5007fe5401ff55007fc54027fd4c05fe53027f54c05fc5301ffd0c05fe4301ff50c05fc43027fd4803fe52027f54803fc5201ffd0803fe4201ff50803fc42017fcc803fe32007f4c803fc32027fd4409fe51027f54409fc5101ffd0407fe4101ff50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21027fd4009fe50027f54009fc5001ffd0007fe4001ff50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84200fffd951007dfeca880037f65440013fb2a200fff99510025fcca8803ffd654401f7eb2a200fff19510025f8ca8803f7c65440093e32a200effd9110075fec888003bf64440015fb22200eff9911001dfcc88803bfd644401d7eb22200eff1911001df8c88803bbc64440075e322200effd5110077fca88803bfd544401dfe2a22000ffd8d10005fec688003df63440016fb1a200dff98d10015fcc688003fd63440017eb1a200dff18d10015f8c688003dc63440056e31a200fffd4d1006ffca68803ffd534401bfe29a200effd0d1006ffc868803bfd434401bfe21a2000ffd8910005fec488003ef624400177b12200cff9891000dfcc488003fd62440017eb12200cff1891000df8c488003ec624400376312200fffd4910067fca48803ffd5244019fe292200effd0910067fc848803bfd4244019fe212200dffcc910067fc6488003fd3244019fe192200fffd451007ffca28803ffd514401ffe28a200effd0510077fc828803bfd414401dfe20a200dffcc510007fc6288003fd314401bfe18a200cffc8510007fc4288003fd2144019fe10a200fffd411007ffca08803ffd504401ffe282200effd0110077fc808803bfd404401dfe202200dffcc110007fc6088003fd304401bfe182200cffc8110007fc4088003fd2044019fe1022000ffc4110007f62088003fe1044001fb0822005ffd941004dfeca08027fe65040097f3282009df99410024fcca08027fd65040137eb282000df59410004faca08017fc65040097e3282005ffd9010045fec808023fe64040077f3202008ef9901001d7cc808023fd64040117eb202000ef590100057ac808017fc64040077e3202008ffd5010047fca808023fd5404011fe2a02005ffd8c10005fec60801ffe63040057f3182000f798c10015bcc608003fd63040017eb182000f758c10005bac608017fc63040057e3182009ffd4c1003ffca608027fd530400ffe2982008ffd0c1003ffc8608023fd430400ffe2182005ffd8810005fec40801bfe62040037f3102000fb9881000ddcc408003fd62040017eb102000fb58810005dac408017fc62040037e3102009ffd4810037fca408027fd520400dfe2902008ffd0810037fc8408023fd420400dfe2102007ffcc810037fc6408003fd320400dfe190200bbf9841004ffea208027fe5104013fea882009ff14410047fe8208023fe4104011fea082008ff1041003ffe6208003fe3104001fe9882007ff0c410037fe4208003fe2104001fe9082006ff08410055fcc008027ff500400bff2802009ff5401002ff8a008023ff400400bff2002008ff5001002ff8800801fff300400bff1802000ff4c01002ff8600801bff200400bff1002000ff4801002ff84008003ff1004001fb8802005ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x3fd6148001fe30a4000bf185200c7fea290063fe5148031fea8a4018ff145200bffe829005ffe414802ffea0a4017ff105200b7fe6290003fe3148001fe98a4016ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024018ffd41200c7fca090063fd5048031fe2824017ffd01200bffc809005ffd404802ffe2024016ffcc120007fc6090003fd304802dfe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f8204802bffb2e2015bfd97100affccb88012fe65c402bfeb2e2015bf597100aff8cb88012fc65c4017ffb26200bbfd931005ffcc98800efe64c4017feb26200bbf5931005ff8c98800efc64c4017ffaa6200bff9531005ffaa98802ffc54c4001ffb1e2000bfd8f100a7fcc78800afe63c4001feb1e2000bf58f100a7f8c78800afc63c402bffa9e2014ff94f100affaa788053fc53c4017ffa1e2014ff90f1005ffa8788053fc43c4001ffb162000bfd8b1009ffcc588006fe62c4001feb162000bf58b1009ff8c588006fc62c402bffa962013ff94b100affaa58804ffc52c4017ffa162013ff90b1005ffa858804ffc42c4029ff9962013ff8cb10007fa658804ffc32c402bffa8e2015ff947100affaa388057fc51c4017ffa0e200bff9071005ffa838802ffc41c4029ff98e2000ff8c710007fa6388053fc31c4027ff90e2000ff88710007fa438804ffc21c402bffa862015ff943100affaa188057fc50c4017ffa06200bff9031005ffa818802ffc40c4029ff9862000ff8c310007fa6188053fc30c4027ff9062000ff88310007fa418804ffc20c400bffb2c2012bfd9610097fccb08012fe6584025feb2c2012bf5961002ff8cb08012fc658400bffb24200abfd9210057fcc90800efe6484015feb24200abf5921002ff8c90800efc6484015ffaa4200aff95210057faa90802bfc548400bffb1c2000bfd8e1008ffcc70800afe6384001feb1c2000bf58e1002ff8c70800afc6384025ffa9c2011ff94e10097faa708047fc5384015ffa1c2011ff90e10057fa8708047fc438400bffb142000bfd8a10087fcc508006fe6284001feb142000bf58a1002ff8c508006fc6284025ffa942010ff94a10097faa508043fc5284015ffa142010ff90a10057fa8508043fc4284023ff9942010ff8ca10007fa6508043fc328401d7eb0c2012ffd4610097fca30804bfd5184025fe28c200affd0610057fc830802bfd4184015fe20c2011ffcc610007fc6308003fd3184023fe18c2010ffc8610007fc4308003fd2184021fe10c2008bf98210097fea108017fe5084025fea842005ff14210057fe8108017fe4084015fea042005ff1021008ffe6108017fe3084001fe9842005ff0c210087fe4108017fe2084001fe9042005ff08210007fe2108003f71084001fd8
  | 2 => 0x30015fec69800bff534c005ff29a6002ff54d30017f8a69800bff434c005ff21a6002f790d30017fa8698077dd434c005fe21a6000ffd8930005fec498073fe624c0037f3126000ff589300e7f8c498006fc624c03dffa92601cff949300f7faa498073fc524c03bffa12601cff909300effa8498073fc424c005ff9926002ff8c930017fa649800bfc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf185300f7fea29807bfe514c03dfea8a601eff145300effe8298077fe414c03bfea0a601dff10530017fe629800bdf314c005ff18a6002ff4c530007ba629800bfc314c039ff90a6000ff88530007fa4298073fc214c0057fb02601effd41300f7fca09807bfd504c03dfe282601dffd01300effc8098077fd404c03bfe2026002ffcc130017f6609800bfe304c001ef1826002ff0c130017b8609800bf8304c039ff902601cff0813002ffecb1006eff6588037ff32c4004bf996200dffacb1006efd658800bfe32c4004bf1962002ffec91006aff6488035ff3244003bf992200d7fac91006afd648800bfe3244003bf192200d7fea91006bfe5488035feaa4401aff1522002ffec710002ff6388033ff31c4002bf98e20007fac710002fd638800bfe31c4002bf18e200dffea710067fe5388037fea9c4019ff14e200d7fe8710067fe4388035fea1c4019ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510017ff6188001ff30c4000bf98620007fac310002fd618800bfe30c401bffd46200dffca31006ffd5188037fe28c401affd06200d7fc831006bfd4188035fe20c4019ffcc620007fc6310003fd3188033fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310006fe6088037ffa844005ff942200dffaa110017fc5088035ffa044005ff902200d7fa8110017fc4088033ff9844005ff8c220007fa6110017fc3088003ff9044001fbc822000ff64110017fc2088003fc1044018ffd95200c5feca900037f65480013fb2a4018ff99520025fcca90063fd65480317eb2a4018ff19520025f8ca900637c65480093e32a4017ffd91200bdfec89005ffe64480077f3224017ff591200bdfac89005ffc64480077e3224017ffd51200bffca89005ffd544802ffe2a24000ffd8d20005fec69005bfe63480057f31a4000ff58d20005fac69005bfc63480057e31a4018ffd4d200b7fca690063fd534802dfe29a4017ffd0d200b7fc869005ffd434802dfe21a4001bfd892000ffea490007fe5248003f72924001ff549200c7daa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc29000
  | 3 => 0xb90c4201ff0862100fe84310803ff6088401ff3044200bf98221007fac110802fd6088401fe3044227ffd422113ffca11089ffd508844ffe2844226ffd0221137fc811089bfd408844dfe2044225ffcc22112ff86110807ff2088403fe1044201fb08221127feca90892ff6548449ff32a4204bf99521127faca90892fd6548449fe32a4204bf1952111ffec89088eff6448447ff3224203bf9912111ffac89088efd6448447fe3224203bf1912111ffea89088ffe5448447feaa24223ff15121007fec690802ff6348445ff31a4202bf98d21007fac690802fd6348445fe31a4202bf18d21127fea69088bfe5348449fea9a4222ff14d2111ffe869088bfe4348447fea1a4222ff10d2100dfec490807ff5248403ff2924201ff5492100ff8a490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148449ffa8a4224ff94521127faa290893fc5148447ffa0a4223ff9052111ffa829088ffc4148445ff98a4200ff8c521007fa629088bfc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484017e3024224ffd4121127fca090893fd5048449fe2824223ffd012111ffc809088ffd4048447fe2024222ffcc121117f86090807ff2048403f79024201ff0812102ffecb18086ff658c043ff32c6004bf9963010ffacb18086fd658c00bfe32c6004bf1963002ffec918082ff648c041ff3246003bf99230107fac918082fd648c00bfe3246003bf19230107fea918083fe548c041feaa46020ff15230015fac71800bff538c005ff29c6002ff54e30017f8a71800bff438c005ff21c6002ff50e30017f88718017ff628c03fff3146001bf98a30007fac518002fd628c00bfe3146001bf18a3010ffea51807ffe528c043fea94601fff14a30107fe851807ffe428c041fea14601fff10a30017fe651800bfe328c005fe9946002ff0ca3002ffec318003fe618c0017f30c6000ff58630005fac318017fc618c043ffa8c6021ff9463010ffaa318087fc518c041ffa0c6020ff90630107fa8318083fc418c005ff98c6002ff8c630007bc631800bfd318c005fe18c6002f70c6300fffe4318003fe218c001fe90c601fff08630015fcc118087ff508c00bff2846021ff5423002ff8a118083ff408c00bff2046020ff5023002ff8811800bff308c005ef9846002fecc23002ff8611800bf8308c03fff9046005ff082300f7feca9807aff654c03dff32a6004bf995300f7faca9807afd654c03dfe32a6004bf195300effec898076ff644c001dfb226000afd91300effcc89800efe644c03bfeb22601dbf591300eff8c89800efc644c03bde3226003af191300effea898077fe544c03bfeaa2601dff151
  | 4 => 0x8b3fc548c4057eb1c6202ffd4e31017fca71880bfd538c405fe29c6202ffd0e31017fc871880bde438c405fea1c622cf750e31017f88718803ff628c457ff3146201bf98a31007fac518802fd628c457fe3146201bf18a3116ffea5188affe528c45bfea94622bff14a31167fe85188affe428c459fea14622bff10a31017fe651880bfe328c405fe9946202ff0ca31015fcc3188b7ff518c45bff28c622dff5463116ff8a3188b3ff418c459ff20c622cff50631167f8831880bff318c405ef98c6202fdcc631017f8631880bf4318c457ff90c622bff08631007fec118803fe608c4017f3046200ff58231005fac118803fc608c45bffa84622dff9423116ffaa1188b7fc508c459ffa04622cff90231167fa81188b3fc408c405ff9846202ff0c231017b861188afff208c457fe104622affd9531155feca988abfe654c4097f32a622aff59531155faca988abfc654c4097e32a6229ffd913114dfec8988a7fe644c4077f3226229ff5913114dfac8988a7fc644c4077e3226229ffd513114ffca8988a7fd544c453fe2a26202bfd8d31017fea69880bfe534c405fea9a6202ff14d31017fe869880bfe434c405fea1a6202ff10d31007fec498802ff624c451ff3126201bf98931007fac4988a3fc624c4037e312622affd4931147fca4988abfd524c451fe2926229ffd0931147fc84988a7fd424c451fe2126202ffcc931017fc649880bfd324c405fe1926202bfd8531157fea2988abfe514c455fea8a622aff1453114ffe82988a7fe414c453fea0a6229ff10531017fe629880bf7314c405ff18a6200f78c531017f8629880bdc314c405fa18a6228ffc8531147f84298803ff604c4017fb026200ff98131007fac098803fc604c4017e302622affd4131157fca0988abfd504c455fe2826229ffd013114ffc80988a7fd404c453fe2026202ffcc131017be609880bfc304c451ff9026228ff0813113ffecb1089eff658844fff32c4204bf9962113efccb108127e658844ffeb2c4227bf59621006facb108027d658844ffe32c4204bf19621137fec91089aff648844dff3244203bf99221137fac91089afd648844dfe3244203bf19221137fea91089bfe548844dfeaa44226ff15221007fec710802ff638844bff31c4202bf98e21007fac710802fd638844bfe31c4202bf18e2113ffea710897fe538844ffea9c4225ff14e21137fe8710897fe438844dfea1c4225ff10e2100dfac510807ff5288403ff2944201fb94a2100ffaa51089fed5288403fe2944201ffd0a2100ffc8510807fd4288403fe2144201ffcca2100ffc6510807fd3288403fe1944201bf9862113ffea31089ffe518844ffea8c4227ff14621137fe831089bfe418844dfea0c4226ff1062112ffe6310803fe3188401fe98c4225ff0c62100ffe4310807ef2188403f
  | 5 => 0x40000000200400000803000020010060320140300701a0580a802004010020010001a00280104a0200400600806c0480107802c0880100002c008040000000500701200003003000000070220040040080102e000090000200100080503a0100202900601404000008008000210020100600902800c0100803e0080f0000040100180600c0082a820000094080240100140b00300203c0000c024000028160000000002f014008048070000080000c00600c098040020300200100201c0401001a0040c0010040080480000202c0280500000c0100003a010180010000e00300100400002005000028008010000000100d000010050000040cc030060060041a80100a00c0880c020008008110060900980302c0000200c02c0000100400800813846000020038000060900002100203c0380000c1480080000200003800000004040000080100101400c020088000000040080901002c000020020000700300c0100400401c0300080b05402401017038010000040060001e0140020141980701c0100180200c0180180704a014030000060040000002c0000500b000074010020080040000100004c0400502601c05000000028008040000500100000001c0680000e00c0080401a0083901000e00000809006070018500020000000501804c0380001400007003000018018000000100b80600404c1c00100a0bc0280000c0900080000a010038020000201081201000c0001202a00c0381100c0bc080bfff654c85f7fb2a642fff99532025fcca990bffd654c85f7eb2a642fff19532025f8ca990bbff644c85d7fb22642eff9913201dfcc8990bbfd644c85d7eb22642eff1913201df8c8990bbff544c85dff2a2642eff55132177f8a899006ff634c805ffa9a6402ff94d32017faa69900bfc534c805ffa1a6402ff90d32017fa869900bfc434c8037fb126401ffd493200ffca499007fd524c803fe2926401ffd093200ffc8499007fd424c803fe2126401ffcc932017de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf1853217ffea2990bffe514c85ffea8a642fff14532177fe82990bbfe414c85dfea0a642eff10532017fe629900bfc314c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099002fc604c85fffa82642fff9413217ffaa0990bffc504c85dffa02642eff90132177fa80990bbfc404c805ff9826402ff0c13200ffe4099007fc204c85bffb2c622dbfd963116ffccb18812fe658c45bfeb2c622dbf5963116ff8cb18812fc658c459ffb24622cbfd9231167fcc91880efe648c459df3246203af99231167fac9188b2fd648c401deb246200af59231167f8c91880efc648c459ffaa4622cff95231167faa918
  | 6 => 0x21a43ee34264e8520423124ae56c7f66d659a54e3f493e0d680a8bc74a6fc4f624038a00048e36e49c1ce75820625611c8fe92619c4b032673e6706e03f296642266a4de8e437600084c47a5a405c1f87e876e6d891e8c667e81c4080884383a206490e77607842605e46c0ce1347820000006f01a200000200016013c6aa6ea93030813629800000084019a00000031683637e00055e3380002d03545ac0a460640a15428800009829400059e9440007705c000036619400000019841a00000087050424821400091c1fc86c2c800027800058c6165f60140002b00766140162f60400006b664c6a889c45200000000090622a7881528be0445a802a6508ee0f06264e21924aa0f28f469a8da00011a0960a251c0ac1960007ea1484d00b86e800051427010602c1ec6ce4d46ba7ae00057e11e0000007e017018400000048c55a62800000038c00041672291414600034a78a2860000000007040e60380008582621086440008c80003d62967be64000c41000000000040031c1bc11236a79416e6b23e86b47d030e9320005c80000000000000e873c0000000b600035a25e00057800042e0002ac7f08720006b871c4bc00018c76c3188987a887a55621c3c61da87462c77400000000000000090a0008660007c45b80000007462ba4fc0505b400097263e0000000000004f803456a5fc2f253820c3106cc6b01502fc0002227800002085e03e063a0747b618a0308b010e00000027400000061e00002200024252823c54423630282441214e62a3fe10a70006667234438401282800004c0fe0000006581260008567480008ca5961a07420000008380ee17413e7100a02b42ca00067685a3d23e429a0728a65ae5640000003f031438000081663400042a7088e60002e87d20000008120004da92a0002580006c22e000019e3a49641f43ea83a7de44400000074e3002a05ba39800000000024a4fe2f417269292484e4780002685c20009186085dc5bc7ba09e03226c20e4ce3ec56647652472470a94647e50661c2ea2ee0205002326ee21674c00000063221096e69016c10c0000042d645400000000078c0e28b20fc73488096800061236296c0004a200054081e80865404880443e72c2dc7a255047c5629026644a44a87364d82840bc3861226a24140588481c641816a80e92c6f41e07267441445944664643902723a00e045c38800e6987e457a0aa37013030c1c88ac1f23602024dc7203da5988306105ea4be3aa1dc1823468625ca60c62e9420b00ba1f669e87c79a41e5327ca24e60014232e0ea1ba40e8c00007281de06893457c14c18874092e65e00077e47493a8f66ca7c67f26a058a4c028a19005267469c21e0de3302a22f00003b26422804cc3323d80364585fe5d01ea12a08e2de27e80c1401be01a0000380400001400003
  | 7 => 0x8ae1d45086c03f84c47cc1765a08c208267861a3c27980cc17e40286e4b68fc06e7d47f848a01e0be7ce25a3f64202b670645a15a1c48a49742ec0b42180000fa4e400095e4ec6da0000001fe00000000026a7186e42822aa8222242d42fa6ae3522ce6ec0000000002444048aa6ac3d40008cc00073060200037873a5700000005cc00000043067a34c26e81a3b67e260a4320ca0000000b233e00087e44c77a8b63948684a600654277c5167b095658243402470c32c00062036c4600c889e84a01a78e0006fe1e444010076a7b47fc0186c80842c48f84c60000008e000800064a0f600003e4b40000008d00008a81d23ae89615c59c0009360e40000f490c79058800060e00062211802600000000000038e2ae00055248829e4287a646a3fa65a4e004e5b691a8a01fa1020000000800c65f000052e66c00006000000000050c20a71a4fa1280009700005e65e85d23507c001002e61833c79e5d46a668000008a79213853000024c56088e0001623720000000000ec0004a05ee1c00008ce3dc25282c3ac6a449a00017c91652a0004e85360546604f23687020001b03225c65b044e07e53e65243c50a5868de6de6f22bc0c43824823042d800001c3240007bc04612c8180004f44560f828e00000020421a42c0a878676617a5e28d27383ba4ca9081ae1200000001e85f82303b45ec8144722663287d654a23841c4865da76254c3748b82502b868e3c09280005342547961b88325228ec59088800094e0004c246866e3a607c3d08922e64d252c0625e437c2f87680c22cc1ee8f20000000008543960008d40000006d41b60000a63cc95423a15875e8107ac51a35649609463049206c83413a70e64622600056e9128205d60000006565ce04a7124b275675286455c3c400093895c2a69203be24639e22c4066be7e603a84260487615607a1241d08fa0dc6e678430a89a5aa89473235c3a89482d200022851848011455800049800086a44600000068c00095200000032a6e244279c75a94000006a2be7b809c0007a48ba3922c64625f40d488a2c02e269600a37a6bc1b45927fa51049e3e67c888439a5a682a0924846dc4708a294a8023b85120000da96033a85c7788466fa5741ac00000051e0007725f21a85d86247500284b883c4247644ac1d643a57650e3202601b29581cc46e93c8001048060d222e09a6361aa7601ca6667144948dc6944d605a8c434e94c27a1f072e49005671e66227c2a43de71684425c1a67c20007ec3b04ba2901327d80005a21d844883e4ea08c68212e5be0d88782a87f44e62fe7a000000055420000066800000058e34021250200045e16445033600096231e44a5de8f075452039c75c29231a3347fe5fa35e2200001c200023486052629c6c47dc88696a8905b27aa0000d05686c66f88e24ee0003e
  | 8 => 0x68a88240c6840008d682600014a5840000000008b43fc1104f03643c853a3bc0860ae00067c43616653c88c3ce18e2b228c63c9100008d88e80000c064817890054618603c85015e18000000000034807063882e6860901166d07ee65c23e2769042c295a7b29500003062da0003584c83ca00072a5485c46d22646881681e20001e60007da6f62e45725808ea85e922
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd658c410045be748c410005bd748c410166be648c410006bd648c410016de638c410006dd638c41015eee628c410006ed628c41002dfa708c410005f9708c4100a4ff764c4101567e654c4100067d654c41014ebe644c410006bd644c410016de634c410006dd634c410146ee624c410006ed624c41003fd4314c41009cff768841002cfe768841000cfd768841002cfc768841004d7e75884100057d758841013e7e65884100067d6588410136be6488410006bd648841012ede6388410006dd638841000eee6288410006ed628841002dfa7088410005f9708841009cff76484101267e65484100067d654841011ebe6448410006bd6448410116de6348410006dd634841000eee6248410006ed624841008cff764c0100f67e654c0100067d654c010005bf744c010045bc744c0100eebe644c010006bd644c010016de634c010006dd634c0100e6ee624c010006ed624c010084ff76480100057f754801004d7c75480100c67e65480100067d65480100bebe6448010006bd64480100b6de6348010006dd634801000eee6248010006ed624801002fe820480100ae7e65c40100067d65c401005ebe64c4010006bd64c40100a6de63c4010006dd63c401009eee62c4010006ed62c401009ef576c401002f7665c401002f7565c401002fb664c401002fb564c401002fd663c401002fd563c401002fe662c401002fe562c401002df570c401002ef660c401002df9768401002ef9768401000cf9768401002f7a658401002f79658401002fba648401002fb9648401002fda638401002fd9638401002fea628401002fe962840101a5f9718401019efa618401002ff26184010004ff76440100057f754401004d7c754401007e7e65440100067d6544010005bf7444010045bc7444010076be6444010006bd6444010005df734401003ddc734401006ede6344010006dd6344010005ef7244010035ec7244010066ee6244010006ed624401002df77644010006f77644010004f7764401000777754401018f74754401002f76654401002f756544010007b77444010187b4744401002fb6644401002fb56444010007d77344010007d4734401002fd6634401002fd56344010007e77244010007e4724401002fe6624401002fe5624401002df7704401002ef6604401002ff2504401018ff15044010187f3404401002ff04044010005fb7644010006fb7644010004fb76440100077b754401018f78754401018f7a6544010007796544010007bb7444010187b87444010187ba6444010007b96444010007db7344010007d87344010007da6344010007d96344010007eb7244010007e87244010007ea6244010007e9624401002dfb714401002ff37144010196fa6144010007f2614401018ff2514401018ff15144010187f34144010187f04144010
  | 1 => 0x881009cfe71d881002ef671d881002cfe70d881002efa70d8810004ed769881002eef6598810006ee659881002f6e65988100066e6598810006ed659881002f6d65988100066d659881002eec659881002eef6498810006ee649881002fae6498810006ae6498810006ed649881002fad6498810006ad649881002eec649881002eef6398810006ee639881002fce6398810006ce6398810006ed639881002fcd6398810006cd639881002eec639881002eee609881000cff76588100067e65588100067d6558810006be6458810006bd6458810006de6358810006dd635881002eec6258810004ff7558810024fe7558810004fd7558810024fc7558810004ff745881001cfe7458810004fd745881001cfc7458810004ff7358810014fe7358810014fc735881002eef7258810006ef5258810036ee5258810006ed5258810036ec5258810006ef4258810036ee4258810006ed4258810036ec4258810006ef3258810036ee3258810036ec325881000cff715881000cfd7158810034fc7158810036ec215881000cff705881002cfe705881000cfd705881002cfc705881002eee205881002eec205881002def7658810036ef765881000cef765881002eef6558810006ee655881002f6e65588100066e6558810006ed655881002f6d65588100066d655881002eec655881002eef6458810006ee645881002fae6458810006ae6458810006ed645881002fad6458810006ad645881002eec645881002eef6358810006ee635881002fce6358810006ce6358810006ed635881002fcd6358810006cd635881002eec6358810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810036ef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef4158810006ee4158810006ed4158810006ec4158810006ef3158810006ec3158810036ef705881002eee705881002eec7058810006ef505881002eee5058810006ed505881002eec5058810006ef405881002eee4058810006ed405881002eec4058810006ef305881002eee305881002eec305881002eee105881002eec1058810004ff764c81002cfe764c810004fd764c81002cfc764c81017e7e654c8100067d654c810176be644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c8100a4ff768c41002cfe768c410014fd768c41002cfc768c41016e7e658c4100067
  | 2 => 0x3cfd73d8c1000cfe72d8c1002eee72d8c1000cee72d8c10004fd72d8c1002eed72d8c10004ed72d8c1002cfc72d8c100a4fe71d8c1002ef671d8c1002cfe70d8c1002efa70d8c10004dd7698c1002edf6598c10006de6598c1002f5e6598c100065e6598c10006dd6598c1002f5d6598c100065d6598c1002edc6598c1002edf6498c10006de6498c1002f9e6498c100069e6498c10006dd6498c1002f9d6498c100069d6498c1002edc6498c1002edf6298c10006de6298c1002edc6298c1002ede6098c10014ff7658c100067e6558c100067d6558c10006be6458c10006bd6458c1002edc6358c10004ff7558c10024fe7558c10004fd7558c10024fc7558c10004ff7458c1001cfe7458c10004fd7458c1001cfc7458c1002edf7358c10006df5358c1003ede5358c10006dd5358c1003edc5358c10006df4358c1003ede4358c10006dd4358c1003edc4358c10004ff7258c1000cfe7258c1000cfc7258c1003edf3258c10006de3258c1003edc3258c10014ff7158c10014fd7158c1003cfc7158c1003edc3158c10014ff7058c1002cfe7058c10014fd7058c1002cfc7058c1002ede3058c1002edc3058c1002ddf7658c1003edf7658c10014df7658c1002edf6558c10006de6558c1002f5e6558c100065e6558c10006dd6558c1002f5d6558c100065d6558c1002edc6558c1002edf6458c10006de6458c1002f9e6458c100069e6458c10006dd6458c1002f9d6458c100069d6458c1002edc6458c1002edf6258c10006de6258c1002edc6258c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c1003edf7158c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006de4158c10006dd4158c10006dc4158c10006df2158c10006dc2158c1003edf7058c1002ede7058c1002edc7058c10006df5058c1002ede5058c10006dd5058c1002edc5058c10006df4058c1002ede4058c10006dd4058c1002edc4058c10006df2058c1002ede2058c1002edc2058c1002ede1058c1002edc1058c1002cff75d8810024fe75d881002e7e75d88100247e75d8810004fd75d881002e7d75d88100047d75d881002cfc75d881002cff74d881001cfe74d881002ebe74d881001cbe74d8810004fd74d881002ebd74d8810004bd74d881002cfc74d8810014fe73d881002ede73d8810014de73d8810004fd73d881002edd73d8810004dd73d881002cfc73d8810034fd72d
  | 3 => 0x863c4110007eb62c4110007e862c41100067f65841100967c6584110006bf6484110056bc6484110006df638411008edc6384110006ef6284110086ec6284110065f676841100077765841101b7746584110007b764841101afb46484110007d76384110007d46384110007e76284110007e46284110007f3608411002d7f765941004e7f76594100247f765941002e7f64594100067e645941002f3e64594100063e64594100067d645941002e7c645941002e7f63594100067e635941002e7c635941002e7f62594100067e625941002e7c62594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067c325941004e7f71594100067e715941004e7d715941004e7c71594100067f41594100067e41594100067d41594100067c41594100067f31594100067c31594100067f21594100067c215941004e7f705941002e7e705941004e7d705941002e7c70594100067f405941002e7e40594100067d405941002e7c40594100067f305941002e7e305941002e7c30594100067f205941002e7e205941002e7c205941002e7e105941002e7c105941002dbf7659010046bf765901001cbf765901002ebf6559010006be655901002f3e65590100063e6559010006bd655901002f3d65590100063d655901002ebc655901002ebf6359010006be635901002ebc635901002ebf6259010006be625901002ebc6259010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bc3259010046bf7159010006be7159010046bd7159010046bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006bc3159010006bf2159010006bc2159010046bf705901002ebe7059010046bd705901002ebc7059010006bf505901002ebe5059010006bd505901002ebc5059010006bf305901002ebe305901002ebc3059010006bf205901002ebe205901002ebc205901002ebe105901002ebc105901002cff75d8c10024fe75d8c1002e7e75d8c100247e75d8c10004fd75d8c1002e7d75d8c100047d75d8c1002cfc75d8c1002cff74d8c1001cfe74d8c1002ebe74d8c1001cbe74d8c10004fd74d8c1002ebd74d8c10004bd74d8c1002cfc74d8c10
  | 4 => 0x8910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910064ff7258910006ef7258910084ff7158910006f7715891009cff7058910006fb7058910005ee7618910066ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91017e7c654c910006bf644c910176bc644c910006df634c910016dc634c910006ef624c91000eec624c91008cfe768c5100067f658c51016e7c658c510075be748c510005bd748c510006bf648c510166bc648c510006df638c510016dc638c510006ef628c51015eec628c510014fc764c5100067f654c5101567c654c510006bf644c51014ebc644c510006df634c510016dc634c510006ef624c510146ec624c510005fb704c510005f8704c510084fe768851007d7e75885100057d75885100067f658851013e7c6588510006bf6488510136bc6488510006df638851012edc6388510006ef628851000eec628851000cfc76485100067f65485101267c6548510006bf644851011ebc6448510006df6348510116dc6348510006ef624851000eec6248510005fb7048510005f870485100a4fe768c1100067f658c11010e7c658c110006bf648c110106bc648c110006df638c110016dc638c110006ef628c1100feec628c110014ff764c11006cfd764c110014fc764c1100067f654c1100f67c654c110005bf744c110075bc744c110006bf644c1100eebc644c110006df634c110016dc634c110006ef624c1100e6ec624c110005f7714c110005f4714c11009cfe76881100067f65881100de7c6588110006bf64881100d6bc6488110006df63881100cedc6388110006ef628811000eec628811000cff7648110064fd764811000cfc76481100057f754811007d7c75481100067f65481100c67c6548110006bf64481100bebc6448110006df63481100b6dc6348110006ef624811000eec6248110005f77148110005f471481100067f65c41100ae7c65c4110006bf64c411005ebc64c4110006df63c41100a6dc63c4110006ef62c411009eec62c41100077b65c41101c77865c4110007bb64c41101bfb864c4110007db63c4110007d
  | 5 => 0x6bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d1006cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1008cff7158d10006f77158d100a4ff7058d10006fb7058d10005de7618d1006ede7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910066ee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d8910006ef52d8910066ee52d8910006ed52d8910066ec52d8910006ef42d8910066ee42d8910006ed42d8910066ec42d8910006ef32d8910066ee32d8910066ec32d891000cfe71d8910064fd71d891000cfc71d8910066ef21d891002cfe70d8910064fd70d891002cfc70d8910066ef20d8910065ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910066ee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef31d8910006ec31d8910006ef70d8910066ee70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910006ef30d8910006ec30d89100057f755891007d7c75589100067f65589100067c6558910005bf7458910075bc7458910006bf6458910006bc6458910005df735891006ddc7358910006df6358910006dc6358910066ec6258910004ff75589100067f75589100047f755
  | 6 => 0xc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110006bf71d9110076be71d9110076bd71d9110076bc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d9110076be70d9110076bd70d9110076bc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006bc30d9110006bf20d9110006bc20d9110076bd10d9110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1006ede63d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df53d8d1006ede53d8d10006dd53d8d1006edc53d8d10006df43d8d1006ede43d8d10006dd43d8d1006edc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d1006edf32d8d10006de32d8d1006edc32d8d10014fe71d8d1006cfd71d8d10014fc71d8d1006edf31d8d1002cfe70d8d1006cfd70d8d1002cfc70d8d1006edf30d8d1006dde76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1006ede71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d1006ede70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006dc20d8d100057f7558d1007d7c7558d100067f6558d100067c6558d10005bf7458d10075bc7458d10006bf6458d10006bc6458d1006edc6358d10005ef7258d10065ec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10
  | 7 => 0x8e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e1008edf3158e1002ede3058e1002edc3058e1002cff75d8a10024fe75d8a10004fd75d8a1002cfc75d8a1002cff74d8a1001cfe74d8a10004fd74d8a1002cfc74d8a10014fe73d8a10004fd73d8a1002cfc73d8a10084fd72d8a1002ef571d8a10086ec21d8a1002efa70d8a1002eef20d8a1000cff7658a100057f7558a100957c7558a1002eec6258a10004ff7558a100067f7558a100047f7558a10024fe7558a10004fd7558a10024fc7558a100067c7558a100247c7558a10004ff7458a1001cfe7458a10004fd7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a1002eef7258a10086ee5258a10006ed5258a10086ef2158a1002eee2058a1002eec2058a10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca10005f7714ca10005f4714ca1006cfd768c610055be748c610005bd748c610006df638c610016dc638c610014ff764c61002cfc764c610016de634c610006dd634c61008fd4314c610005fb704c61002df8704c610064fd76886100957e75886100057d7588610006ef628861000eec628861000cff764861002cfc764861000eee6248610006ed6248610005fb704861002df8704861003cff764c210005bf744c210055bc744c21002edf634c21002edc634c210034ff76482100057f75482100957c754821002eef624821002eec624821002df576c4210006f576c4210005f976c4210006f976c421007d7e76d951007e7e76d95100247e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e63d95100067c63d95100067e62d95100067c62d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067c32d95100067f71d951007e7e71d951007e7d71d951007e7c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d951007e7e70d951007e7d70d951007e7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067c30d95100067f20d95100067c20d951007e7d10d9510075be76d9110076be76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006be62d9110006bc62d9110006bf75d9110006be75d9110006bd75d9110006b
  | 8 => 0x76f65881201cf6c6588120005ed7188120006ec618812002dee708812002fea708812002eef608812000feb608812005dbe74d8f10005bd74d8f100a6de63d8f10004ff75d8f10024fe75d8f10004fd75d8f10024fc75d8f10004ff74d8f1001cfe74d8f10006be74d8f1001cbe74d8f10004fd74d8f10006bd74d8f10004bd74d8f1001cfc74d8f100a4fd73d8f100a6de43d8f10006dd43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f100a6df31d8f10006f970d8f100a6dc30d8f10014ff7658f100a6dc6358f10004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f1001cfe7458f10004fd7458f1001cfc7458f10006df7358f10004ff7258f1000cfe7258f1000cfc7258f100a6dc3158f100a6df3058f100ad7e75d8b100057d75d8b1009eee62d8b10004ff75d8b10024fe75d8b100067e75d8b100247e75d8b10004fd75d8b100067d75d8b100047d75d8b10024fc75d8b10004ff74d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10014fe73d8b10004fd73d8b10014fc73d8b1009cfd72d8b1009eee52d8b10006ed52d8b10006f671d8b1009eef21d8b10006f970d8b1009eec20d8b1000cff7658b1009eec6258b10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b10004fd7458b1001cfc7458b10004ff7358b10014fe7358b10014fc7358b10006ef7258b1009eec2158b1009eef2058b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10014fd768c71005dbe748c710005bd748c710016de638c710006dd638c710005fa708c710005f9708c71003cff764c710006df634c710016dc634c71000cfd76887100ad7e75887100057d758871000eee6288710006ed6288710005fa7088710005f97088710034ff7648710006ef624871000eec624871006cfd768c310006df638c310016dc638c310014ff764c310014fc764c310005bf744c31005dbc744c310016de634c310006dd634c310005f7714c310005f4714c310064fd7688310006ef628831000eec628831000cff764831000cfc76483100057f75483100ad7c754831000eee6248310006ed6248310005f77148310005f4714831009fe8204831002cff75d8e10024fe75d8e10004fd75d8e1002cfc75d8e1002cff74d8e1001cfe74d8e10004fd74d8e1002cfc74d8e1008cfd73d8e1000cfe72d8e10004fd72d8e1002cfc72d8e1002ef571d8e1008edc31d8e1002efa70d8e1002edf30d8e10014ff7658e10005bf7458e10055bc7458e1002edc6358e10004ff7558e10024fe7558e10004fd7558e10024fc7558e10004ff7458e10006bf7458e10004bf7458e1001cfe7458e10004fd7458e1001cfc7458e10006bc7458e1001cbc7458e1002edf7358e1008ede435
  | 9 => 0xd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df43d8d200b6dc43d8d2002cff72d8d2000cfe72d8d200fcfd72d8d2000cfc72d8d200fedf32d8d200fedd32d8d20004fe71d8d20004fd71d8d200b6dc31d8d2000cfd70d8d200b6df30d8d200057f7558d200c57c7558d200067f6558d200067c6558d20005bf7458d200bdbc7458d200b6dc6358d20005f77158d20005f47158d201f5fb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d20004fd7458d2001cfc7458d20006bc7458d2001cbc7458d200fcff7358d20006df7358d200e4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d201f4ff7058d20006fb7058d200067f65d85200067c65d8520004ff75d8520024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d8520006f741d8520006f441d8520006f731d8520006f431d8520086f621d8520086f521d85200c57e75985200057d75985200067f65985200067c6598520006f76198520065f970985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520005df73585200b5dc735852009dfb70585200067f65185200067c65185200bdbe7418520005bd7418520006f56118520004ff7518520024fe7518520004fd7518520024fc7518520004ff741852001cfe7418520006be741852001cbe7418520004fd7418520006bd7418520004bd741852001cfc7418520014fe7318520004fd7318520014fc7318520036ee5218520006ed5218520006f74118520006f44118520006f73118520006f43118520036ef2118520036f62118520036f52118520036ec2018520004fe768c520004fd768c520004fc768c5200067f658c52016e7c658c5200bdbe748c520005bd748c520006df638c520016dc638c52000dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200067f654c5201567c654c5201edef75485201eded75485200076f65485201e76c654852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb704852002dec7048520007e87048520005e8704852000eef604852000feb60485201dcfe768c1200067f658c12010e7c658c12002fe8208c120014ff764c12000cfe764c1200e4fd764c12000cfc764c1200067f654c1200f67c654c120005bf744c1200bdbc744c120006df634c120016dc634c120005ef724c12000dec724c1200e7e8204c12002def75881201d5ed7588120
  | 10 => 0x8e2002cfe70d8e2002efa70d8e20014ff7658e2002edc6358e20004ff7558e20024fe7558e20004fd7558e20024fc7558e20004ff7458e2001cfe7458e20004fd7458e2001cfc7458e2002edf7358e20006df5358e200cedc5358e200cede4358e20006dd4358e200e6df3258e200e6dd3258e20004ff7158e20004fc7158e200cedf3158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e2002ef76198620004ff7598620024fe7598620004fd7598620024fc7598620004ff749862001cfe7498620004fd749862001cfc7498620014fe7398620004fd7398620014fc739862009ef6219862009ef5219862002cfe709862002ef6109862002ef410986200057f75586200dd7c755862002ef46158620004ff75586200067f75586200047f7558620024fe7558620004fd7558620024fc75586200067c75586200247c7558620004ff745862001cfe7458620004fd745862001cfc7458620004ff7358620014fe7358620014fc7358620066f62158620066f52158620066ec215862002cfc7058620066ef205862002ef6105862002ef41058620004ff768c62002cfe768c620004fd768c6200d5be748c620005bd748c620004ff764c620004fd764c62002cfc764c620016de634c620006dd634c620005ef724c62000dec724c62020f6e75886200076d758862020eef658862020eed658862000dee718862000fe67188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862000eee608862000fea60886201f4ff764c220005bf744c2200d5bc744c2202057e76d95200c67e76d95200247e76d95200067f64d95200067e64d95200067d64d95200067c64d95200067e63d95200067c63d95200076f72d95201ff6c72d95201ff6f21d95201ff7b20d95201ff6c20d95201ff7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95201fe7f72d95201fe7e72d95201fe7d72d95201fe7c72d95201fe7f42d95201fe7e42d95201fe7d42d95201fe7c42d95201fe7f32d95201fe7e32d95201fe7d32d95201fe7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067c31d95201fe7f21d95201fe7e21d95201fe7d21d95201fe7c21d95201fe7f70d95200c67e70d95201fe7d70d95201fe7c70d95200067f40d95200067e40d95200067d40d95200067c40d95200067f30d95200067c30d95201fe7f20d95201fe7e20d95201fe7d20d95201fe7c20d9520014fe76d8d200067f65d8d200067c65d8d200b6de63d8d20004ff75d8d20024fe75d8d20004f
  | 11 => 0x6bd51d9130006bc51d913023ebf31d913023ebe31d913023ebd31d913023ebc31d9130006bf21d9130006bc21d913023ebf70d91300eebe70d913023ebd70d913023ebc70d9130006bf50d9130006be50d9130006bd50d9130006bc50d913023ebf30d913023ebe30d913023ebd30d913023ebc30d9130006bf20d9130006bc20d913000cfe76d8930006bf64d8930006bc64d89300e6ee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d8930004ff74d893001cfe74d8930004fd74d893001cfc74d893000cfc73d8930006ef52d89300e6ec52d89300e6ee32d89300ceed32d8930004fe71d8930004fd71d89300e6ec21d8930014fd70d89300e6ef20d89300057f75589300f57c7558930005bf74589300edbc7458930006bf6458930006bc64589300e6ec6258930005f77158930005f47158930235fb7058930006bf64d8530006bc64d8530004ff75d8530024fe75d8530004fd75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d853000cfe72d8530004fd72d853000cfc72d8530006f751d8530006f451d853008ef631d853008ef531d8530006f721d8530006f421d85300edbe7498530005bd7498530006bf6498530006bc6498530006f7619853006df970985300057f75585300f57c7558530005bf74585300edbc7458530006bf6458530006bc6458530005ef72585300e5ec72585300a5fb70585300f57e75185300057d7518530006bf6418530006bc6418530006f56118530004ff7518530024fe75185300067e75185300247e7518530004fd75185300067d75185300047d7518530024fc7518530004ff741853001cfe7418530004fd741853001cfc741853003ede4318530006dd431853000cfe7218530004fd721853000cfc7218530006f75118530006f4511853003edf311853003ef6311853003ef53118530006f72118530006f4211853003edc301853022ddf744c53022ddd744c5300079f644c5302279c644c530015df714c530017d7714c530007d7614c530006dc614c530007d4614c530006d4614c530007db704c53002ddc704c530007d8704c530016df604c530017db604c530004fe7688530004fd7688530004fc76885300f57e75885300057d7588530006bf6488530136bc6488530015de7388530005dd7388530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530006bf644853011ebc644853002ddf748c13021ddd748c1300079f648c1302179c648c130005dd718c130006dc618c13002dde708c13002fda708c13002edf608c130017db608c13002cff75d8e20024fe75d8e20004fd75d8e2002cfc75d8e2002cff74d8e2001cfe74d8e20004fd74d8e2002cfc74d8e200e4fd73d8e2002eed72d8e20004fe71d8e20004fd71d
  | 12 => 0xb50d8121006f850d812109efa20d8121006fb60981210057f75581211257c7558121005bf745812111dbc7458121005df7358121115dc73581211257e75181210057d7518121006f9601812102cff7518121024fe751812102e7e75181210247e7518121004fd751812102e7d75181210047d751812102cfc751812102cff741812101cfe7418121004fd741812102cfc7418121014fe7318121004fd731812102cfc7318121006ee2118121036ec2118121006fb501812102ef8501812102eef201812102efa2018121036f9201812100cff7658a3002eec6258a30004ff7558a30024fe7558a30004fd7558a30024fc7558a30004ff7458a3001cfe7458a30004fd7458a3001cfc7458a300feee5258a30006ed5258a30006ef4258a300feec4258a300feee3258a300b6ed3258a30004ff7158a30004fc7158a300feef2158a3002cfe7058a3002cfc7058a3002eee2058a3002eec2058a3002ef76198630004ff7598630024fe7598630004fd7598630024fc7598630004ff749863001cfe7498630004fd749863001cfc749863000cfe7298630004fd729863000cfc72986300a6f631986300a6f5319863002cfe709863002ef6109863002ef41098630005bf7458630105bc745863002ef46158630004ff7558630024fe7558630004fd7558630024fc7558630004ff7458630006bf7458630004bf745863001cfe7458630004fd745863001cfc7458630006bc745863001cbc7458630004ff725863000cfe725863000cfc725863006ef6315863006ef5315863006edc315863002cfc705863006edf305863002ef6105863002ef4105863024f9e748c6300079d748c63024edf648c63024edd648c630015de718c630017d6718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c630016de608c630017da608c630004ff768863002cfe7688630004fd768863010d7e75886300057d7588630004ff7648630004fd764863002cfc7648630005df7348630015dc734863000eee6248630006ed6248630245be76d91300eebe76d913001cbe76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91300079f73d913023f9c73d9130006be62d9130006bc62d913023f9f31d913023fbb30d913023f9c30d913023fb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d913023ebf73d913023ebe73d913023ebd73d913023ebc73d913023ebf53d913023ebe53d913023ebd53d913023ebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d913023ebf32d913023ebe32d913023ebd32d913023ebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130
  | 13 => 0x8e2101cfc74d8e21144fd73d8e21006ed72d8e2125cfe71d8e21006f671d8e2102cfe70d8e21004fd70d8e21014ff7658e210067e6558e210067d6558e2112edc6358e21004ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e2101cfe7458e21004fd7458e2101cfc7458e21006df7358e21006df4358e2112edc4358e21146df3258e21146dd3258e2100cfc7158e2112edc3158e21004ff7058e2102cfc7058e2112edf3058e2100cff768c621014fe768c62100cfd768c62116e7e658c6210067d658c621135be748c621005bd748c621016de638c621006dd638c62100dee728c621005ed728c621264ff764c6211567e654c6210067d654c62112fd4314c62113d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb609822102cff7598221024fe7598221004fd759822102cfc759822102cff749822101cfe7498221004fd749822102cfc7498221014fe7398221004fd739822102cfc739822102efa2098221086f920982210067e65582210067d6558221005bf7458221135bc7458221004ff7558221024fe7558221004fd7558221024fc7558221004ff7458221006bf7458221004bf745822101cfe7458221004fd745822101cfc7458221006bc745822101cbc7458221004ff7358221014fe7358221014fc7358221066ee5258221006ed5258221066ef2158221066fa2058221066ec205822113d7e75182210057d75182210067e65182210067d6518221135be7418221005bd741822112dde7318221005dd7318221006f96018221014fe76d8d21116de63d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006df53d8d21116dc53d8d21116de43d8d21006dd43d8d2115cff72d8d2115cfd72d8d2115edf32d8d2115edd32d8d2100cfd71d8d21116df31d8d2102cfe70d8d21004fd70d8d21116dc30d8d21116dc6358d21265f77158d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d2101cfe7458d21004fd7458d2101cfc7458d2115cff7358d21006df7358d21144ff7258d21006ef7258d21264ff7158d21006f77158d21004ff7058d2102cfc7058d2125cfe768c52111dbe748c521005bd748c521014ff764c52100cfe764c521144fd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724c521117d4314c5212576e75885210076d7588521256ef6588521256ed658852100dee718852100fe6718852100eef618852100fe76188521005ed7088521004ff75d8121024fe75d8121004fd75d8121024fc75d8121004ff74d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d8121006f
  | 14 => 0x15dee7218231005ed7218231006f9601823100cfe76d8931146ee62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d8931146ee52d8931006ed52d8931006ef42d8931146ec42d8931146ee32d893112eed32d8931014fd71d8931146ef21d893102cfe70d8931004fd70d8931146ec20d8931146ec6258931285f7715893127f9e748c5310079d748c53127edf648c53127edd648c531015de718c531017d6718c531016df618c531017d7618c531005dd708c531004ff75d8131024fe75d8131004fd75d8131024fc75d8131004ff74d813101cfe74d8131004fd74d813101cfc74d813100cfe72d8131004fd72d813100cfc72d8131006fb40d8131006f840d81310a6fa30d8131006fb60981310057f75581311557c7558131005bf745813114dbc7458131005ef7258131145ec725813114dbe7418131005bd7418131006f9601813102cff7518131024fe7518131004fd751813102cfc751813102cff741813101cfe741813102ebe741813101cbe7418131004fd741813102ebd7418131004bd741813102cfc741813100cfe7218131004fd721813102cfc7218131006de311813103edc3118131006fb401813102ef8401813102edf301813102efa301813103ef930181312757f765962113e7f76596210247f76596210067f64596210067e64596210067d64596210067c64596210067e63596210067c635962126f6e72596210076d725962126f6f215962126f77215962126f74215962126f6c20596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c435962126e7f725962126e7e725962126e7d725962126e7c725962126e7f425962126e7e425962126e7d425962126e7c425962126e7f325962126e7e325962126e7d325962126e7c325962113e7f715962126e7e715962126e7d715962126e7c71596210067f41596210067e41596210067d41596210067c41596210067f31596210067c315962126e7f215962126e7e215962126e7d215962126e7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067d40596210067c40596210067f30596210067c305962126e7f205962126e7e205962126e7d205962126e7c205962113d7e75d8e210057d75d8e210067e65d8e210067d65d8e21135be74d8e21005bd74d8e2112ede63d8e2125df671d8e21004ff75d8e21024fe75d8e210067e75d8e210247e75d8e21004fd75d8e210067d75d8e210047d75d8e21024fc75d8e21004ff74d8e2101cfe74d8e21006be74d8e2101cbe74d8e21004fd74d8e21006bd74d8e21004bd74d
  | 15 => 0xa20d8132006fb60981320057f755813217d7c7558132005bf7458132175bc7458132005f77158132005f47158132006f9601813202cff7518132024fe7518132004fd751813202cfc751813202cff741813201cfe7418132004fd741813202cfc741813200cfd7318132014fd7218132004fe7118132004fd711813202efa30181322a6f9301813202efa20181321def9201813229dbf7659231166bf765923101cbf7659231006bf6559231006be6559231006bd6559231006bc65592312979e73592310079d7359231006be6259231006bc62592312979f3159231297b73159231297b431592312979c3059231006bf7559231006be7559231006bd7559231006bc7559231296bf7359231296be7359231296bd7359231296bc7359231296bf5359231296be5359231296bd5359231296bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006be5259231006bd5259231006bc5259231296bf3259231296be3259231296bd3259231296bc3259231166bf7159231296be7159231296bd7159231296bc7159231006bf5159231006be5159231006bd5159231006bc5159231296bf3159231296be3159231296bd3159231296bc3159231006bf2159231006bc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006be5059231006bd5059231006bc5059231296bf3059231296be3059231296bd3059231296bc3059231006bf2059231006bc205923116d7e75d8a310057d75d8a31165be74d8a31005bd74d8a31006be64d8a31006bd64d8a3115eee62d8a3128df671d8a3100cff7658a31006be6458a31006bd6458a3115eec6258a31004ff7558a31024fe7558a31004fd7558a31024fc7558a31004ff7458a3101cfe7458a31004fd7458a3101cfc7458a31006ef5258a3115eec5258a3115eee3258a31116ed3258a31014fc7158a3115eec2158a31004ff7058a3102cfc7058a3115eef2058a31165be74d8231005bd74d8231006be64d8231006bd64d8231006be6498231006bd6498231006fb609823102cff7598231024fe7598231004fd759823102cfc759823102cff749823101cfe7498231004fd749823102cfc749823100cfe7298231004fd729823102cfc729823102efa309823108ef930982310057f755823116d7c7558231006be6458231006bd6458231004ff75582310067f75582310047f7558231024fe7558231004fd7558231024fc75582310067c75582310247c7558231004ff745823101cfe7458231004fd745823101cfc745823106ede4358231006dd4358231004ff725823100cfe725823100cfc725823106edf315823106efa305823106edc305823116d7e75182310057d7518231165be7418231005bd7418231006be6418231006bd6418231
  | 16 => 0x500100000a00001600200400000500201600700000100100000000000c00300000801d00200500000000a01200400500100901600400500300200600000000001400000400000000000900700000400b00300600500100000000000000900000d00000501000f00200000000300600100600000400100000000000200300d00100800300200f00202200000200c00100000000001801000200e00100000000000000000100300300300400000900001902700400200100100c00000100500500000801f00b00700100800000000100000000800400000200300400300300700300000400100200400000600700000100100b01100000000000100000200100000000100100800200b00000200001901300c00000100400000200001000300000000000000100000401100800200d00000000201200000000000000200100300f00a00000600200100000f01700000003d00000400000000200000000000200300400000100900000100700100000400000000600700100200000600500000400600000500400400900000000100701500200200700100300500000000000200000900000100900000000100000102100b00200b00300100500701200500000000301a00001300900200400000700100000100002100100800100900500100400c00200200300000200200000400700300300000000000d00000200500000000d00500400300200201401300400d00a00200300200000000000700000101200300600400300600200800100000100000000000700800600000000000000000000700e00100800700101200100000200000200000a00000700700400400400400001500000000001001000200200100100300400000600400400000400400401400801700400300700300700000000000000000000400200000100000000100100700700a00200c00400900500000300001700b00000001800400000000300500100000000000100100200000000000d001025001000000015000000001000000003012004ff75d8532024fe75d8532004fd75d8532024fc75d8532004ff74d853201cfe74d8532004fd74d853201cfc74d853200cfd73d8532014fd72d8532286f631d8532266f621d853202cfe70d8532004fd70d853217d7e75985320057d7598532175be7498532005bd7498532006f76198532006f56118532004ff7518532024fe7518532004fd7518532024fc7518532004ff741853201cfe7418532004fd741853201cfc741853200cfd7318532014fd721853228ef5311853225ef5211853202cfe7018532004fd7018532004ff75d8132024fe75d8132004fd75d8132024fc75d8132004ff74d813201cfe74d8132004fd74d813201cfc74d813200cfd73d8132014fd72d8132004fe71d8132004fd71d8132236fa30d81321f6f
  | 17 => 0xb200000000001e50000e2a0002ca0000000000000000000000051d10593e42cd3d900007c00000002868d207785518f34e600003251b4c5a82711680000be01ba18790cd0966240001ae43f859948f140c14841a446878033e5c10f7283108c2762b2000002a2853559dd41b63ed3fd800000032b0ab0661428ab439a80000004d81b900003e47264c60ea44d800025f000078676546c91512585334198b880f249724100000000003f388d019a24700010fcf1c0001338f554c23e74be9d3c3061f600000005fc00012b80000000003b180000000000000000c6a4a64df0bfd370113194269c000000000187400093a0f22a1400031b1c702d4fa60000000001176a1f0001e480008fd000000070658b1f800000007f80002784db4000000087000079024b298d0780000000dbc39602c23a09d4000000206051c0000874fca36d40400043f00000000000002ae8d6e0000002304a4400012f0a3c2d62821dda764caa53602c9614b5e00036f959d41253a1b8000013e00400100000300000000300100800600300100000000200a00200000000400900800000101b00200300000001a01100100100301600000000301202600000100101a01000000000a00300000200400200000001f00200100000600300000100500100001100600000400300200000100000400000100100100100101000000000800300000500100000300601400000200100600300300a00000201e00300401600100000500400000c00200200200100000000000200000201000200000100000400900100700000100a00c00200400600600100000000500400600200000b01200000000300000100200000100500500000300000000000000d00200000000500700000900300200000600000200000300100100600000400100500f00600501d00800500a00b00000100000400300000100200500000000200000200300000200400700400000300e00700200000b00000000200600000b01000000301000000000500800100200200000e00200102900a00900500000100a00200000c00200400300100e00700500300300000000500400000d00900800000201c00000300100000000000800300402200100003100100100800100100100201f00900000100401500000300200200200000301400400100500100000200300400400100200000200a00100300300900100000200200500200200800100100000000d00000c00200100101301300800200000200000300000300100600300200200000200600500100900600900100400100800200000000000500000000100000c00000000000800001600000000400100000b00000000100300000000000001600100200500300100101700000000100500202400000400200000e00200100000500300300100300000000600
  | 18 => 0x23f034400012119396780006300d89ebc000000000000015c000000232400000038d8b60a1e25241010b40f491d09a232c0d02be031083038e6140002a482ea7493fa0c94c2a78a520000142e00048b000030a72544b8c742dc5f7000000083ea9a00000000000000c40f2429a00000000004800001870000da20000fe892d26047d1a5256c00016032f00003500000c900000000001fb94600002604291b08a826501d81470ab4a6543e0d700b026e51113f8b740000001788000905000245000000051708b51e800022c0ea14260000278000e246cb13ea818a8095400015e8000000000123c0003ff00000000005e640700001e0000000000132041b00000010b000000025b537e52b1fd00013664941d606f92b26bb18496f51287d14e88000692000000007d0b830800004b151e19100026a096451340fa5249aa57517d146cf8a7f618e2190a2800011197fc0002c507c01f4000000109a8581948a304d287060e444045a0e94be2b3000202d54a0004ed09cc00016c000000136289e3f806dd4b295708b11e0b46a720cc810c00068b00029f91ea00035aa34839826532d00009ca00047d800000000000000000005e800000000000002ce000000000029c8000b18a270d80aac00088c0d12a78fdc88300000000000000e980000002b90001965594a7726512bc6602bc06998488c6ad64ca1f4801a5da0e2005c16e00052086d02de0002d30000000602000000125a6f800000003b423b4ae115c00000040810c4602000091a16ce1070400011782bc96f2ae9040eb000017a0000ce400026d1f182be15d34a04301a4582522054149e2354d229b8c588421a40698c4203725d82d0f1e0d73af8000b8807302803553c45c300028981242ca54a0b588745292671ee513a9475620000ef23dd0000000000136000000000025900007bc00068107295f53ec92623928d417800000000000000003e400010ac14200029b080469700000000165782691e044824411be931454e90900019dcf8666e00004945f85c72f4877c00085d4a700000008235560a488600000000ef54104f22a60ad80000001181294654218081879937a39302e18a4d9e41800000000007b73ed13800000002f98130c3c49f0000a0c00050c38f861c00000013083800000000000000dd69343bb00013bea2321b093c0008210001e506e884e2de00f49589550ae1df4da854b000000000011f37e8ab81b0a300001f3842c000256a78cefe067000000000028d2e5994cb146ef000000111c3aa14898002b44f81bf0454d8815b26613e86d40000320421354413150934cdf86b30d08fcc22250a0000de8c063a00001e5413c6dd000000011e00055f80012f26a700027f8000a4d23498dd35aa7401c00015a200044400000000002230a5414e9961cb246c5080000
  | 19 => 0x30c29cc0001b3300a48503858052593dce3c495286a3e0cb07402fa9d9c000a7000000014589f447880283720c41071870000000000137000000052a80010d2a1900000015a45bf000000000044c00022640000004ec0ac40008bf00012d40000004972b155a822a135a8a49ce20d00000015625161528e6c0444914e800ad3640002ac28fc000000082294c0007f944993353d013800011a0b080002828b3833c8fc14480008029884e01ecd510a380000f100002a933600004d42392ee25c40ec0180991f6c7b8233163000ccc001c00010553d226f3db193c6846041dd0a204da6d700000180000000000000d640000000ccc00000000027fc94e7f200000000008250000eb80006fa000136d3600001df80000008a10000a8000097600000010889ed2b6a73c91a4421949cd8c864c412100000008e92a38000e9a54825a0750d180000f3a184000000160000000049d1ec80000006c920486d80009b50000000000373000039000038b500800000000000009dcebc2c82ef8000a9400000000007de9520001fb130271d34680000000000000000000000000264817600000000000000e236c80000008740001d453d4683000000115e05a074000094400031d9b840000003e20d0d336a8e3d624ac000747227a6b8eb67560000d746648801df00000ca0000000a6c5aa00033191b8bae06d000138812283d4a1264caec13d2b48da4faa07e3ea00006825c24822b08eb44ed35a279c9322ee00000000ae00000011fcdd00000001fc40000000000884f5c60c2610b9d43c33b3e1009cf9a3d31ef80012d486d0000c78e5a64400000000000003d6a1e46260000800234c9a0fa000266041276f04e132130804b22b000000019b2ec9e58fc200000000011543193bd87c4d0c00000021ec00046a3828000b1025333980003ae5354e68868cf0000000000000000001924dc0000004fc0000cb60000000000a6400000002b05cc0f54800000700786000026400000000009ed0bc7a2045151421697b3498b08b9e907190ab3400033941480000009d7000198400058143905b400036718a00453b8acf30d1b8cb8c59200027040008674fe937c9747213fba8344b0a47328a4c50100000001e3400021508c18294c03c10002530eae000061000085c1531b598fc00039d30b10882fa0002e41e00f485113aa8594e2e67b05411e800062d44f9c451d8530263800134000c350a58037a502323800130682442680006b273400017ac00000016d00010500000000eac7102e000000012820000000000bc229900000000000004798f30ffa18b37a8001204000226a1885d800034b1bfc2900003c580840000000eea97400000047c886400000020e00013046db4cc9a9800000000003cc000000000000000052455f261c2fe40a3cb9ccc00098502a0000
  | 20 => 0xcc446103a97d80001312d720150d600000000000000000000000000617533800000000017d95b00dc1514e4006d2480004f22938fb04245289e7c3580ea471987c96c4340f29cbc5c82862e88000000000000020520600006f800000021b554190840c000391226000057b30c84bcdf27a30831f894303ea00021a80000000001324d12177490018c0000004098000a8674600024cc8065681931b354400003d31d987664e34d09ad874c000000046939c8e20001bdc21491c087000121800000000001c609400000000002900d2a02800000016998200000000d58e152b047052b14b0b6e2df19a1f74e860605028a308006461da23904567183898490b1a0001a897e0000a1d00002c938a55422c8fec808a154a203f068000000000014683ec000000156c000000000117c1af4c89d08000000000160c0008504b48524000000452967c48a88a1138d68000819398a9f09b252a3630a680006841d69838c40a3e4bc286c000000000279932e59a000245444a2442f6870c9966d51882ae041030b0178e0527eace176880157625b2599074a4600000025900000bd337800000018d0001e1000027000002c400035624f19a80003904b982c0b525a55521888a3495e01992dd0300000000000000a6d0000000a9e00035180000000002af0000e168ff0001cf40005ad000229952284c51d931800000003780000009f30cb1facef48810c4800000017000009240008d5000000107276e2eea6d108e00000006fd5903bc1fc0cc484c64049388fcd0e52f4a427f040802d11c1d28b2e350000000076e0004278f84b626ac1da9a200000000000a29162a621058000ac20cb3919c5026a18c06c876ce1807b19a96c000052d13488bc98042551e01aca786694851e615723e921419588540950ca26755047b81050440d400340ba0e906bea492c4a21888064b0ec14d000059d0d4800154424e4501170e009db20887a800036d00000007fc6c04e48000000000000000053e00000020d8ee45b5000234c6c2355298954460a3d817c18ccfda3f914ea8f4bac8b30001c8000000000000000005250000ba000052000029081443530a29da471eaad4e313f407e77428fa0505e00003a08c7c00000000020d400082b32b83a41da47732084fc000078000000101e45f00008f40000001b2875800060600000000004671a59400c8a1e336417283923db41109e0c9896224587a48da13a000035009a12946a212158080203080000002b7372a894c7201333b000073430000000000002f30000668f7e0000b910c89e004a10a20590f47a73572b4d4b42bd50522680005e743180d8baa6c70001bc81061ed2ae0f18b6418f13180010ea76100016e00000004301a142ec3ee33800000000de00000006d800000000000002af000000000062600015980004d7
  | 21 => 0x17a8b0ce56000075800116c00007ca29ce3200022800007f846b1a682b53dc1c84c013447ea03a3068ae0ab20003d08218c0a50919fa68d1de000466849c00040d14c0778b9a00049c00002500004eb233c00000020bab192ea0f727ca698be81713bba8913e08bc175969154c7ab499252cfd002e3170db90a88ce53d800000015900000003c41b53c4a018f6a9510071fbc15204426814400004843852a810a27d03c288e90e04ff43e80006a87380000000b7615800005983c244752815cce985190b39c3d1be698355055ce0c53d0000155160a3318893a4a925b45661d8082476d0000c8ce2046023aa82c0000002942b1c0000002d1000008068f275a5400000770000064fbe2b5010000003a1330000ddcea400000000000008c3000000000069b0001ec000000055512c489414b0fd961cf385560001ba90ae8de00000000000000001b7000065400025f90b29080f5800154e80c54e074921c37b00002a8d783761f20ce029e8b443b22c8dc82ad03a025c39c130460001049070715121145000002a70de41103d22a680000005ac47b92615520001ed1ae00000001fe800000000033280000000001581c0417c0003b829e4a7c9d30e0069c972aa10a08ed895406a160ab046480b300029480009f73de11bc00000000020b463000000000000000524fd00000000000001474b1e00000028bc87600028928383e0084489a78000000000000011205574b18000000008162000000048e1540b302281ca00019a0be40001a9101400000000029a5596917116085d35698b05010e535e9864e3a5b144279900020c47703e31ad9c68de827e1c2011c9ea00019b8000c64000000200c2380533d4000095220551c80014fa0004868000c4e5fb00000000009651e000013e26a9225800136e9b6000000000081b4b30f2c8cc2bb12ea6240000000001db01a04870001b783ee8da54b28a89c20000001fcc3148b905d08788f25d4083a41805200014b0b1ce380000000d5d532a8d4cf00000000cc0bf0918dfc39245c15e40002933aa00000008f625faac818c000000174ccda3953948000452000374a5680000bf22407d01ac23149b0001408000000254c000000089000000000000013a800000030800000000003e58000746a5e0000000f1800000003f80a200000000d4fc68730000cf015e3d029faaad4ea67a00012f00001782311168000abc0001a5529e0002a900000005c93819740a107be1e700000000710e280000000001bf800000000000000000003164411540cfa5ef2570001464000000000148a00044e00000005e045695f8d3217b2d4028c000a5736c12245d27ff1d8800100233e000000019ca480000c34bfa00053f8001420000000000037000024d80002449250000000b2c00047413d880e2db014120c00044e000000
  | 22 => 0x1148ca45d8475149c000a6821a9b153762540a929c416c3a100d046525e59b31d1bb4b7c0002c8000134470e0000000bb66382858000ccc0000fc2750000a974700014ec4000000000000083e000000000094349113b0d3e00008f210c0006ba41a00011a07fc2361e4d27856000010f4c12501358120118a5652558000000000196000125282f132232802800000018a80000000000000f940000f413d01048850002b0c0000001eba42c000096000039c70c0cf0000000000000314043c00013e00000000001680001abc0000000000a980007fe13a119135843e0000e30e7e8fa20a00000001c100027d503400000000000003b23388b3c00094000028d894085a0bcaac00fe0001e884f000020313400000000000000000bd458627880011ca6793cf0e281cc11d000222400048a4fda518fb86c30002a0ccfc4733ae800062e0000000b840000c535200007ca0000931a88e9000031b097d45a00046403fc0007c72b88001486a5812a93ecb5419c4f780009827aa0e3135874495d07b015800000038b00005ae1f9000129000018201e293000000047309447e228e4f59ca0000000378000000000045d243c00082c00000003fe7731fb00008ca000297000000000048d00001e8000000000080c000000000000057f00000000008b544a80000000451cf800000009354d80000001810d222b8a700a64ab0198a2a0000f9a9a804c56b42003700604b80000bc8d628490771ef465e186368000155e9d551886103462d25680bdc000aae1dc80001120981330000a42a0f182000069e4cf0001d10ddc36606184a8000a5b5448000a087e5000000000000008680006c672e5422add57a3d6349299807c7913ec9c9d06022400004814c88040e89b38ec800000001212ee0001ca13bc18e6ec00017f87a80000000000b428261f124a0f9272a44200003ea96b0001078fae33648c8f9821268a000000000050e0d680012028530000fac00e06c0048000d980001a715a80000001d280000480c10090c68ae8201470964cef884a0e698bc000a034950a1d502a11246222d02a00000000012f858e000103ce788a41ba800000047100000008b618e40e89c80003c51b2000078421d00023084ac00003490390be52652311141202810000000618000000221c870ab500029e0c623913240000f9e0000000000000a863cd90f06c40001ccab6053c000420a81c0001b24880000a768ee0a618ac90a6e02e9169d3a40b853799f133424a00007540000ef2a3247c0008110000200f102f10000000e9c97a0000e5c000000213800000000027e2b54f820000000000e9689b09b95548f650709599d13522070bd21dc5480000001970000000000000000073a00000001d85b9000263403c0000000cb400057c0a1a4440000004490c0890200
  | 23 => 0x35e800000023c000000146e87f36b259c000891000000000014000015c92e04e641c01c8e5800007091f00000003e000000003150000cb8a6ea5c011800035c14600000000000000000000c22800000158800005f2b805540004511ef06ec6c027c2830ad00008e7000000137869100029d9076ad707e8000f680000000001388000000026cc3675904600013845e322a98951e40000a50000000a2800000000007830001fa40002e512e1f900002103d89cf8ea05f1476867408c3222e7000000054438480000007cc0000ab0f3a031000037400000054c000097a0393cd08f888642b00024eccfe0001af0000000000000000000029c00000000000000000c80de204e2b78000e8a000000000128a00000017e8000000000064c73c010177888134a7fa00020345285950000df15184862d59a6918e0001e424d4ed60002740000d0425a3f300000005c50e78c4937240b052800153a8712db00000000001ce000118c000244248cbbc16335f27942367f50000dc40001540cba57c000a930000b2c0005e400000000003580000a5c0000da0000000d5000000009fcf04346000000000030326a2a2c0005e540929e90f033a204199d31424d4510bd92248d70fd0ba8aa60b926ea4f919800040b845cdce0004c7800000014400020245a275301da31115056300012a107e2dc327237043e8654b0a72d0d813b0000898b667ea0e825346988f0064a1984223f441506a856470248c22b0340000249a7291ba4e42cc124150059118524f52dc7e045ba77533e0a10009bcc9245ee00026e8d3c97f000000000076a210800071a00f46b00000007de35287f800077e347000000000000001f0000000261a2f500e5fc000000086e6e23dd0000000a8709ca5a000028b2d01974554787060156c68e69c000280085e3c70de0de00003894c7000000082e0000000d3aad904280000006ad1140008c7c10200020dd38677119e8ebc8ba2791111cecc7a3e831e07b068a86f3d48000e485424ba108c9dc17c419157cd828551191eed1b01c2000277800062313d03c40000000000e9d53e00000018d070489632f80014244a30000b740000704f600a8404a901f910648924534340da14a866b2149d709e61613079ce419012d3d292689bc2a3164816c2c42375358be40820492f623f857e3064ce1730840ab33058000b80a8a00000000000004758000adc68000005380000000000000cea2e3399181c0840253eb09300000fb28b999070e81e437000048610135f9b98e1a0000ec817894200011b265552a51e45491d9456ac910797e400019539b88b879e88f10906004a00ab4138640da40f20b524e40008d10001bd939805d00005a54947a037d9b280008ab4b9098800000000004140000160000000c2600016c8ae813a2fd097000011c2de21600
  | 24 => 0x17324e1924000768000000129400000015dc0003980ee000000000000012c06880
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5e635d6210409b8dcc4bac420813a1fe1d658841026c3ec3acb1082000c3e75592210400187aeab244208003179d563884100062ebaac710820058ef8758a21040018dceab1442080031b5d5628841000674b12e11082000c3c74595300403b17b0dba260080030f997744c0100061eb2ee89802047c9e63dd1300400195cc5ba260080022fa1d644c0100445e43ac89802000c9f7458d3004001938e8b1a60080032bdd1624c010006563a2c4980201887d86dd5200400187cc9baa40080031798f75480101fe37316ea900200087e8759520040130f90eb2a40080179a08165480100061fbaac89002000c3c7559120040018beeab1a4008003171d5634801002f64102c69002000c6f7558920040018d8eab124008016ba20162480100243e42eec88020038bc84dd910040051b907bb220080063b20b764401007c3ec36ea8802000c3e64dd510040018bcc7baa20080031b98b75440100043f43aca880200987c875951004001878e8b2a2008003171cd654401000636392ca880200e8bd86dd1100400187ccbba220080030f59774440100064f31ee88802000cae62dd1100400117d0eb2220080222f21d64440100061fbaac88802000c3c755911004001938e6b2220080032b1c9644401006c6ec36e68802000c5e65dcd10040018bacbb9a20080032799373440100064eb26e68802000cce62dcd10040011bd0eb1a200801e3721d63440100062fbaac68802000c5c7558d100400193ee8b1a2008003271d1634401000666392c6880200c8ed86dc910040018dccbb9220080031b597724401000657326e48802000cad64dc9100400199cc7b9220080033358f72440100047743ac488020068ec8758910040018deeab1220080031b1d5624401000657ba2c48802000cac74589100400199ee6b122008003331cd62440100063a3aeec8802000cb474dd910040018ef0bbb220080031d21776440100065bc26ec8802000cb484dd910040019af07bb220080033520f764401000673c16ec8802000ce482dd910040018eeedbaa20080032dddb74440100066bbb6e68802000cd7761cd1004001aa8ea39a200800339ddb724401000673bb0e48802000da4741c91004001b88e639220080031e99776440100065d326ec8802000c7875dd91004001970e9bb220080031ee1776440100063c42eec8802000cbb84dd9100400197109bb2200800336e0f76440100066c41eec8802000ceb82dd910040019d105bb220080031eddb75440100063dbb2ca8802000cbb76dd11004001976ecb22200800336ddb73440100066dbb0e68802000d98741cd10040019b6ed31a200800336dd963440100074cb22c68802000ceb76dc910040019d6ec39220080035a1d4724401000675bb4c48802000ceb765891004001cd2cab122008003b258d6244010
  | 1 => 0xe20b2ac8080178d44165590100061fbaceab202056abb805cd640400b57100b9ac80800387d4e53590102ad5bc0ae4b202000ab4815c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c964040695730138ac808002aba0b515901000556c16a2b2020088be87cc5640400117b0f98ac8080028fa1431590100051ec2862b202005aba800c564040015730018ac8080028fa1721590100051ec2e42b2020008be87085640400117b0e10ac8080178e94350590100051f42e60b202000a3d85cc1640401117d0f902c8080022f61f20590100047a40aeab1820058f8805d1630400b1bd0fa9ac60800317dd75358c1002c6e43aa6b1820058de87d0d630400b1b90ea1ac60801637a1e3258c1002f2b882cab182005e5510595630400bd3420b22c60800317dd67558c100056bc0aeab182000ad4815d563040015b700ba2c608016b62017458c100070faa4a8b182000ad4815c963040014bd0a392c608002976147258c100054f420e4b182000a9d841c9630400153d0938ac608002a76127158c100052f428e2b182000a5d851c5630400159d05a8ac608002b360b5158c1003c6f43e82b1820008dd87d05630400b5b50020ac608002b66004158c100052f42e42b182000a5d85c85630400153d0810ac608002a76102158c1002d6d40042b182000ad980085630400bcb4a1a82c608002a7a132058c100054ec2640b1820058f8805d562040011e902ba2c4080163ba1f525881002c7643aa4b1020058ee87d09620400b1d90ea12c4080163ba1f325881002f35082cab102005ea710591620400bd4a20b22c408017b1c41635881002f65082c6b102005ec51058d62040015d700baac408016ba201755881000573c0ae8b102000ae4815d16204001c5ea92a2c408002b9205735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881000727a9ca6b102000a6e859c562040014db0b38ac408002aba10715881000556c20e2b1020068ee87d4562040011db0fa8ac408016baa00515881000574c00a2b102000ace83d05620400159b07a0ac408002aba13315881000556c2662b102000a6e850c562040014db0a18ac408016baa00315881000574c0062b102005e6a50d4162040014dd0b982c4080029b617305881002c6e41eec99020058ec82dd9320400b1b90eb1a64080163b21d624c8100066ab1ee29902000ce562dc532040011eb0c38a64080030f9d1658c4100045fc32e91882000c3e655d2310400187acaba4620814b2798d748c41000657312e918820538bf8759231040a517b0eb246208003279d1638c4100064eba2c71882000cae7458a310400195ae8b1462080033658d708c4100072a18aca9882007ad48158d3104001d8862b1262080021fe1975884100061f322eb1082000
  | 2 => 0x4641891000716328c83122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e8c64d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c488002b3a0e631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000ace8618c624400199cec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c4880121fa17764c9100043ec2eec99220038be84dd9324400117b09bb264880021fe15764c9100243e42aec99220008bf845d9324400717908bb2648800237e0d764c91000477c12ec99220008f7815d932440031bd0fb1a648800a3ba1f624c9100061f3a6cb18a202c8bc865d2314400187ecaba462880030f195748c5102964e31ae918a2000cac625d2314400117f0fb24628803a2f61f648c5100064f3a6c718a2000c9d74d8e314400195ce9b1462880032b5d3628c5100065c326e098a2000cb8641c131440019b6c6382628809e1f21975885100061e322eb10a2000c5c635d6214409b8d8c4bac42880021fe1f658851007c3ec3ecb10a2000c3e75d92214400187aebb244288003179d763885100062ebaec710a2000c6e75d8a21440018daebb1442880031e19770485100063c328e090a2000ceb621c12144001878e9b2a60880022fa1b744c1100061fb2ee89822000c3c65dd1304408f938c7ba260880032b18b744c1102445f43ec898220478bc87d91304400193ee9b1a6088003271d3634c11000657ba6c49822000cac74d8930440018e8cbb8a60880033918b714c1100063a328e29822000cd7631c530440019c8c438a60880021fa1b75481100061e326ea9022000c5c63dd5204407f8d8c5baa40881021fa1f65481101fc3e43eca9022000c3f75d912044001878ebb22408800317dd763481100062e3aec69022000c6f75d8920440018d8ebb1240880032d19371481100066a31ee29022000cb4641c520440019a8c638a408800339d8871481100074c320c78822000e686518b104401f8ecedb2c208803b2d9db648411006e6b3b6c70822002cd67618e1044001ca8ca31c2088033399db628411000e733b0c50822000ea46418a1044001d88c631420880030fdd274594100062fb9ce6b282059a77815cd65040014e902b9aca081629ee01725941002d3c402e4b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282057a79809c565040014bd07a0aca080029760f41594100051f42662b282000a3d84cc565040010fd0e18aca080021f61c315941004c3f43e42b28200087d87c85650400147d0810aca080028f610215941002d3d40042b282000a798008565040130fd0f982ca080021f61f30594100051f42640b282000a3d84c81650400bc6
  | 3 => 0x7b122000aac8458f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001c5ea92a6c4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec48800393d4e53d891000537c2ae3b122000a6c855c762440011dd0fa8ec4880023b61f51d89100056741e83b122000acd83d07624400155d0998ec488002ab61331d89100053742863b122000a6d850c762440014dd0bb86c4880029b61770d891000557c22e1b122000aac845c362440011dd0e286c4880323b61c50d89100056741881b122000acd8310362440014dd0b986c4880029b61730d89100055742061b122000aad840c362440090fd0dbaac4880031b18b75589100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400717d0dba2c4880030fd9774589100061e32ee8b122000cac62dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd6244001998c5b9ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200487e87dd5624400117f08baac48800e2f21175589100046fc1aeab1220028dc835d562440011df04baac4880023ee0175589100043f438eab1220038be87dd1624400187eebba2c4880030f1d774589100043fc2ae8b12200487c855d162440011bf06ba2c48800a3720d745891000477c12e8b1220008f7815d1624400117d0e3a2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440018deebb92c4880031b1d7725891000657ba6e4b122000cac74dc9624400199ee7b92c488003331cf72589100065a3a6e2b122000cd473dc562440018f0ebb82c4880031b9db651891000476c3cca3122000a6e85994624400155d09328c488002ab61265189100056741cca3122000acd8399462440011df0eb28c488002abe11651891000556422ca3122000acf83594624400159906b28c488002bae01651891000537430ca3122000c6e76194624400195cedb20c4880038bd9764189100071632ec831220008ed8799062440014dd0b320c4880029b616641891000557424c83122000ace83990624400159b07320c4880023be1d641891000537c2ac83122000a6c85590624400159f06b20c488002b320d641891000573c0ac83122000aae86190624400195cec320c4880038bd9
  | 4 => 0x34400159b04286c68800237a1c40d8d1006c6ec3881b1a2000a9e84c83634400153b09906c68800297a1420d8d100052ec2841b1a2000c5c63dd563440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd16344001938c7ba2c6880022fa1f6458d100061fbaec8b1a2000c3c75d916344001958e5b22c6880022fa1c6458d100061fba8c8b1a2000c3c751916344001958e4322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880033318f7258d100243f43eeab1a20008bf845d5634400717908baac68800237e0d7558d1000477c12eab1a20018ec825d563440011ef02baac6880021fa1c7558d1001c5f43ee8b1a2000c3f75dd16344001878ebba2c6880021fe157458d100243e42ae8b1a20008df835d163440011df04ba2c6880063b2097458d100047dc02e8b1a20008be871d1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880031d1d77158d1000672396e2b1a2000cb874dc163440018bcedb28c6880023761e6518d100052f42cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440015af02b28c68800297a186518d100062f3b0ca31a2000c9e76d906344001c3ecbb20c688003871976418d100046ec3cc831a2000a5e8599063440014bb0b320c688002a7a126418d1000567414c831a2000acd8299063440011bf0eb20c68800297e156418d100052e42ac831a2000acf82590634400159904b20c688002b6e016418d100054f430c831a2000c9e761906344001c3eca320c688003871946418d100052f42cc431a2000a5d85988634400153d09310c688002a76126218d1002477c3aa5b1220038ef8750b624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc835976244001c5ecbb26c4880038b19764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000717b28c9b122000e2c651936244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c
  | 5 => 0x80021fe1d64d95100052fc1ac9b2a2000a5c8359365440014df04b26ca880029b20964d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d95100061eba0e9b2a2000c5d731cf65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440634f501b8eca8800297a0f41d95100052ec1e83b2a2000a3e84cc7654400147b0998eca880021fa1c31d951007c3ec3863b2a200087e87c8765440010fb0f90eca880028fa1021d95100051ec2043b2a2031a7681dc365440014bd06206ca880029760c40d95100043f43e61b2a200087d87cc3654400147d08186ca880028f61030d95100051f42641b2a2000a3d84c8365440010fd0e106ca8803e1f61c20d95100061f3b6cbb2220008bd87997644400147d0b32ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec8880022fe1d65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100051f430cbb222000c3e76197644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400147d0b316c8880028f61662d91100054f41cc5b222000a9d8398b644400187aea3aec88800387d4e53d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91101855d406e3b222000aae82d47644400155b05a8ec8880022fa1f31d91100045ec3e63b222000a3e850c7644400147b0a18ec8880028fa1721d91100051ec2e43b2220008be87087644401d17b0e10ec8880c2ada0770d911000557410a1b222000aad82143644400147d0b986c8880028f61730d91100045f43861b22200e8bd870c3644400117d0f906c8880022f61f20d91100051f42841b222000a3d8508364440018baeba9ec68801237e1d53d8d1001c6fc3a87b1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000e1f65d936344001c38cbb26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c68800387d9464d8d100070e328c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000c5d751d76344001c3ea92a6c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c688002a7e1171d8d100054e422e3b1a2000ace82d47634400159b05a8ec68800237a1f41d8d100046ec3e83b1a2000a5e85c8763440014bb0b90ec688002a7a1021d8d100054ec2043b1a2000a9e84dc3634400153b09b86c68800297e1570d8d100052e42ae1b1a2000ace821436
  | 6 => 0x43f438eab1a40038be87dd1634800187eebba2c6900030f1d77458d200043fc2ae8b1a400487c855d163480011bf06ba2c6900023de057458d200047a40ae8b1a40008be871d1634800187eea3a2c6900030f1d47458d200064e3a6e6b1a4000c6c75dc963480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200045fc22e7b0a40038bc845cf61480015ad07a0ec290002ada1331d85200243f436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac29016b1edc065585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200061f3a6ca30a4000c3e74194614800187ecaba0c2900030f19574185200047bc3ac230a4000ab48458461480015a906b08c29000e2fa1375185200045ec26ea30a40038bf875d0614800196902ba0c2900032d5d341185200056b41e8230a4000ab684cc461480010ff0abb462900121f215768c52001c5f420ed18a40008bd841da314800187ce9b2c62900030fd95748c5200061e32ae918a4000c9e74d8e31480018d8cab9462900167a201728c5200243f42eec98a400087d85dd9314800717d083b262900022f610764c52009c77438c290a4000e676518521480213d50c38242900173aa18704852002eb5428e090a4005d69851c12148001ad6ca38242900035a19470485200061e3a6ca9824000c3f65dd13048001878cbba26090003271d3634c1200063632ee4982403fc6e76d96204807fcd6c1b2c40900025be15718812000c76c38c31024000ce571186204800717d09baec7880022f61375d8f1000c77416ebb1e20008ed82dd763c400117b0f3a6c78800e2fe1d74d8f1001c6fc3a87b1e200087f855d163c40090f90aba2c7880023be097458f1000c76412e8b1e200087d879d762c40090ff0ebaec5880121fa1774d8b100043ec2ee9b1620028de83dd362c40011bb07ba6c5880123be1d52d8b100045fc22eab1620038bc845d562c40011bf06baac58800a3720d7558b100243f42cec996200087d859d932c400717d093b265880022f612764cb1002c6f43ec698e20058ee87d8921c40019aac638a61880022fe117558e1001c5e422eab1c20008ef825d563840031d904baac70800e2fa1f7458e100045f438e8b1c20058dc8750d63840090fd0fbaac5080021fa1c7558a100043fc2ae8b14200487c855d162840011bf06ba2c50800a3720d7458a1002c7643aa4b14200087f855d932840090f90abb265080022fe11764ca1001c5e422ec9942005ce87058921840010fb0f326ca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca8
  | 7 => 0x3c75d91624c00117d0e322c4980030fdd464589300061e3a8c8b126000cb764dc5624c001968c9b8ac4980032dd9071589300065a320e2b126000ce4621c5624c0010ff0ab96c2980121f21572d853000573416a3b0a6000a7685c87614c00717d0dba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c001958e4322c29816f2edc0645853000657b26e4b0a6000cac64dc9614c00187cebb20c2980030f5d764185300061f3a8c830a6000c3d75190614c0011ef0eb08c2980029d215611853000572412c230a600487f875d4614c0018e902ba8c2980121fa1774185300043ec2ee830a6000c7575d44614c0015cd05a88c298002b560c51185300053b42e4230a6000ad583084614c0291bd0e30a6298003a5d90614c5300074a320c298a6014ad687185314c0019ad0e30a629800395a14614c5300072ac28c298a60008bf845da214c00717908bb442980121fa1476885300043ec28ed10a6000c3c645d6214c00187cebb2442980030f5d764885300064e322e710a6000c6e75d8a214c00717d09bb242980022f61376485300243f428ec90a600087d851d9214c08f93cedb24609800267e11718c1300146ec38c31826000cd571186304c00b1bd0fa9ac71000317dd75358e2002c6e43a86b1c400487e851c563880010fb0a38ac7100121fa1f75586200063610eeab0c4000c6f20dd561880010ff0aba2c3100121f215745862001c5f426ed18c40008bd84dda31880010ff0abb463100121f215768c6200043fc2aec98c400487c855d931880015a902b1a63100423be1d618862000537c2ac310c40138ef865c22188001ad2eab8443100021f61e64d95200043fc3ac9b2a4000a5f8359365480014b906b26ca900029de0564d95200053a40ac9b2a4000a3e8418f654800147b0831eca900629ba1b72d95200061eba0e9b2a4000a3e841cf654800147b0839eca90003175cc73d952000537c12e3b2a403fa6c825c7654800147d0838eca900028f61071d95201fd37410e3b2a4000a6d821c765480014bd07a0eca900029760f41d95200051f42663b2a4000a3d84cc765480010fd0e18eca900021f61c31d95200052f41881b2a4000a5d83103654807f0fd0f986ca900021f61f30d95200051f42061b2a4000a3d840c3654800b1db05ba6c6900121fa1671d8d200043ec2ce3b1a40008bf845c7634800717908b8ec6900021fa1f6558d200061e3a6cab1a400087e871956348001878e832ac6900030fd977458d200061e32ee8b1a4000c7765dc563480018e8cbb8ac6900031dd947158d200063a328e2b1a4000cd4631c563480090fd0fbaac6900022fe117558d2001c5e422eab1a40008ef825d563480011ef02baac6900023d2057558d200
  | 8 => 0x2202cb108021fa1f30596210043ec3e60b2c4200a3e840c1658840147b08182cb108029da0430596210053ac0860b2c420087d87997638840187ce932ec7108021fe1d65d8e210061f3a2cbb1c4200c3e655d3638840187acaba6c71080e2fa1375d8e210045ec26ebb1c420087d879d763884090ff0ebaec7108121fa1774d8e210043ec2ee9b1c42008bd879d3638840187ceb3a6c7108030f5d674d8e2101c5fc3ae9b1c4200c3e755d3638840187aeaba6c7108031b9d572d8e210054f426e6b1c42008de87d0d63884090fd0bb82c7108021f6177058e210061f3a2cb18c4200c3e655d2318840187acaba46310803279d1638c6210063732ae518c4200e5431595318840117f08b9cc11080e2f21173982210061e3a4cab044200c3c74595608840187ccbba2c1108030f59774582210045fc22eab0442038bc845d5608840717d0fba2c1108121fe1975182210043ec3cca3044200c3e7499460884018bce7328c1108021fe1d65182210061f3a2ca3044200c5e73594608840187ccaba0c1108030f59574182210062f32ae63044200c5d655cc60884011f70eb00c1108023b60b75d8d210062ebaea7b1a42038df8750f63484010ff0ab86c6908121f21570d8d210045fc22eab1a42038bc845d563484011bf06baac6908023ee017558d2102c7c402eab1a420087f855d163484090f90aba2c6908023be097458d210047dc02e8b1a42058f8805d1634849b8dcecbac4290802ba60850d81210047dc3ac03024200a788558060484018d842ba8c0908171e201751812102e37902ea3024205c6d205d460484031db0f108c0908031b5d6211812100574c04423024200c7975d40604840b1d90ea92c51800e2fa107158a300045ec20e2b1460008bf845d5618c00717908baac31800e2fa1f74586300064e18ee8b0c6000c9f30dd1618c0231bf0eb0c6318002a7e11618c6300a46fc32e118c600487e85dda218c0010fb0bbb443180022fe11768863001c5e422ed10c60008bf845d9218c00717908bb243180022f61e65d91300045fc3acbb226000aaf82597644c00155904b2ec898002ade0565d91300055a40acbb22601da9e86dcf644c00147d0a316c8980028f61462d91300061eba8ebb226000a3e851cb644c00147b0a396c898002a7e0d71d913023d4e41ae3b226000a3e851c7644c00147b0a38ec89811ea7a0c71d91300054ec18e3b226000aae82d47644c00155b05a8ec8980028fa1721d91300051ec2e43b2260008be87087644c00117b0e10ec8980038ed4250d913000557410a1b226000aad82143644c08f17d0f906c8980022f61f20d91300051f42841b226000a3d85083644c0018daeba96c49800e2fa1271d89300045ec24e3b12600087f855c7624c0090f90ab8ec4980022fa1f64589300061fbaec8b126000c
  | 9 => 0x300000040880102e01c1580000201c0280100a0080000000001c0180500408c008020020240000001400800003008038020000020040381300205c00000006000008000060000080000000c22800002028010050060200280001a0142000500a00401003004000058070040180680000403c0080000a00003005004004018140000540280501400400001002018010020000002e0030020080001300e008f787584614c8010ff0ab80c2990121f21570185320045fc22e030a64038bc845c0614c8090fd0b38ec0990021f61671d813201c5f424e3b0264008bd849c7604c8011f70eb00c0990022fa1f655923100557416cab246200aad82d95648c40117d0e32ac9188b2a7e197359231005cc402e6b246200a3e85989648c40147b0b312c9188030fdd675592310051f42ce4b246200a3d859c9648c40155d05a8ac918802ab60b51592310071ba8ca2b246200a3e85c85648c40147b0b90ac9188022fa1c21592312945ec3842b246200a3f855c1648c4014790ab82c918802a7e0d70592312954e41ae0b246252a9e831c1648c40153b06382c918802aba08505923100556c10a0b246200ab681141648c40156b02282c9188022fa1f20592310045ec3e40b246200a3e85081648c40147b0a102c918802ada0420592310055ac0840b2462008bd87993628c40187ceb326c5188030f5d664d8a310045fc3ac9b146200c3e75593628c40187aeab26c5188031bdd75258a3101c5f426e0b1462008bd84dc1628c4010ff0ab94c1188121f21572982310061fbacc8b046200c3c75991608c40187eeab22c1188030f1d564582310243f43eeab04620087f855d1608c4090f90aba2c11880e2fe1974182310045ec3cc83046200c3e75990608c40187aeb320c1188032b9ca64182310045fc3ac83046200c3e75590608c40187aeab20c1188032b9c9641823100657322e43046200cad645c8608c4011f70eb00c1188123be1d52d89310045fc22e1b1262038bc845c3624c4a593cecba46298802b660c40d81310047dc3ac03026200ab884580604c40193862ba0c0988172e201741813102e4f982e83026205c9d305d0604c4051bb0f188c098803275d231181310056cc04623026200cb974d00604c4010fd0fb22cb1080297a0f64596210052ec1ec8b2c420087e87191658840147d0931acb108028f612635962113d37c32e4b2c4200b68805c9658840187ee93a2cb108028fa1273596210051ec24e6b2c4200c5f739cd65884014bd07a0acb108029760f41596210051f42662b2c4200a3d84cc565884010fd0e18acb109361f61c31596210063db84e0b2c4200a3f845c1658840147908b82cb108029be09705962126d36412e0b2c424da6e821c165884014db04382cb1080297a0c40596210052ec1880b2c4200a768110165884014eb
  | 10 => 0x22d80020f0000002330000618be21a27ea0d21c04e8b100e8000f62228c204f927837899a5a8c79fa90b92512296e8758d51e58a70301ad1249980001318799600581c300000025f1ef1ae11380010e9931519ce17619c2632930002358780000a8a2a8cf84622718a1261ea9a08000001b280007c8001640d980022900012f80001a80000013900029c85499b97e25985b823194171aa100007e8120c40691ab15d1bd1ff87aa0702294d9c180000028f8ed01d00b91f88e8000652a6a9f2951500001210dc8e48dd29400000021980d9a182d93713480006681e0000000001c08d918c99193b8e304a140036a6199494a89e0c3922103a371bb01b9c12511e39f20719c491ca0ba7b1e9832a4988409b8e9aa3142228252a0c0000c994b83c13c9a59e30001c408aaa20ac27084d8190f8a05965138a3824e03a0d580022ba61178967a5917c0000000aba67a1895800000022d00000012f00000002c07399119e03f20d8c122c0268001a68a593d8f518099f00029e0d00b49509bf0bf8530731d2a31093262a5d033a801d61631d0000037121a7f9e627d8f3a1b04017f89e957a369de1838d60cb8b7a170d782881f9340eea87a5503902213789d00014e1b8800000000000125a8a04400000000000023a0001152a01701d580004c80000000000009191e85d0c809a00005195a00000029c24c2010af8cb0721350a18ffaaa9290889cb1921ab8f30aaa14a5697907faa727709028b22323991b0bc1ee80011003480014f0920000000280000000080002603c0600500400c0300100c0140780600000000008024010008040020000081200400c0000300602008006004004010010000140400000002803001012000000040000700300001400c0000401c010010020260140080500a0000100100c01403800002000008040020140902000e008000110160040380a0000040d00100c00001023002000008090020000400200e004000020020100081000000c0180001400801000002000128080520000280200004c0000001800001006026004008060040b4000000040080000502c00004006000008000030040180281800001800801032008000040060140180400c0080300a0060080b00502e01c00000002000008240140040080202a034008010280000d00b000004010050000200100a0080000580200c004018010040000000100e0000080000001406800004014000000040b00a807018008000010020000000400406c010010040040100100c0300081900c08c000040240080500700002c058020020a00e80400e00400802026008000050020200000100205c0000601601c0000202c00c0282e0060000800300401c0700c0a800c0200e0000300280d0080000200001800c0b000002000010020020900100000002c0180405000
  | 11 => 0x1e00009f29b97293d22780000027b9620a10ad00004b0000000fa1560890da18513e84297a2a980026c89c9a227110c03207e00000003980000012d0858001108ca0000ae08b80000006e1b79b91baa8d0181f90c280000015c85796f8ec95e212a2a0001e41f38f203c88c9188000830000000002000000000e19968cf2ab1aa1720000b00c60ff0b30002a4a9891c17b1160c19819bf8f71ba0211d922018c1270000000002048002468bb0000489a529f8560a523614498b8f816105a91a9331d980016e1ed20ca759f829a9d78ed894a7a04480015309589285c98f8002259f00e907d1880c0294a62299a7aa7c85680002d1008851cb9d3a7612a00007095b9f58cd8001a30aa00000022e8001df98701f0250ad88b2211c01c82120788fe17c887902a6922f9141dd02a1f112a89085a1f28fa8baa570000000d309501400008a0e40000c480019780009624c9c28a400000024780001c8000000000f69f600000000016900015b1ad98a800000174a1f0028c301780005b03b8b9086808a3c91922f0011b603128314c21900006d8638a60bd1d1a3e80000018d80000000000009700021d800943108a638f18388219e780000020a80000002915e8000a900004aa140479db0001d4a769be8001dd9bca43a810001af1358000000001d21079538fb26598780000001b0000001ae9428c680a0000f919d8000fe80000014800000021d06708d1f30f4881043a841e881e98106400216980c213a0b2100240001998061e800014b0b3800000196114a539e08000af21313389c1d41ac90e21b8e38728092320340b800024b1542158f58b5800202a899ed8ee0e110c8001020000a01b403b04c10a00000018d1f4973812a5d8200002118de9db84e0dc1f79859aa97a98006d0829f184096705da8090505518b0c5290a470b70002a086200020610d1a026a000000255a5c00000000000024300017323080028893b07480016280000006891980022b25404192c9899d729923781d86807d8f9a9222ca3aa8e29b0f41e492b036000165a3f0f28f011d2a7aa822380b2152698d68bb9b715f11314f90402620a25e8da80007a1ec26e07116198916f1b184d00000013fa660a282b80000010aa2505920e8001fb2458fd06600300010700019d004a462008a380026ba082789c60001a12030d281700029a2600a68db8001710000b20df00027d15501a1d8955879203a388809ac00021aa4f27280000022e0bf00000003593828c0002979441fe00000000014600020912b80000019c8000870b28001470000000000fc8001ff0589d6a9e867aa417e98409100000020e00009882582080000000029d80000008e0000000bd9bba4d0001058db07717400596c000163824a530151e18001608cc80e0238000001b30f794e8000000000d417d97f02b
  | 12 => 0x58ae81327c05f8002482641c99f69990069bd9b10ba21e8628b68000969cd9e9000190a5b8078609c51280e21a280988606c1598d80e61409c90000648a08de13203d0a9a4a1ca0eb8d3800000177146800205111a1680000d0000d0a8484f0e28000a31c71b524100028380028681498600000003f8000000fb893a448e821e00015fa3e00010019e80008c0ca800141a1c8000001cc19506f87b23526b01691b8bca9704693e0001f0958aa38000000701a90b08df88000000186a8001848000451201180002098138002a293129d07c01c1da99390998e1360118319cd11f291a179510e0800149296995a8600005425f80024e8aca1613f00000000000006f27000012e0001b3a5496d00003e112000043115a68970a26917a7417b96a2a586e8822752a60001b48000000001d30000e580000000002f0e794d211077975a72231928a4d90d8001df04907b9c78000000002aa0c08001caa301f70b50000000001ef83a8000001168001459060001928081b089f9300d70000159de80018892e9239af80025b17500028ca8ea509329eb1a796b0d89901a3a4b8839a805ea92a339b99529e505c2a92730000000298001bc1c880017d01013aa6c052a77a95a60a2193c03e9970fd8ea25785e2069d12782489fe8b61f40508ec049a938ce1399d80001ee06580026e8000001208ab0270002901cf0001240d180024511d8f115705000000020799b22998e9869dc87f0000000000002490000000000000b987425889900010186b0000000000000000000a7a9800023b80ca5a27f0000001ea00027e2670d4a2400026d800129a3b1e10538000a480024404581111702a8000001f98331c38001a600000000016480024a80005999a9f89a400f20886980000000000023fa8705580007602f800130a829ec80000005f198936977a881e724212c1fba2209a80000026d1a9876a560cc2719fc16a80000416600000006115200390f0c70ef9488188000eb07523900a80000023418f0c88a80280d22182041d0800274898030a820278001f50000000ef0001e29798b88109fd8000000001a70000001450002910ce800000154a4f9eb8881cca2080015690488192d80015a96697800000008f25e084800000210a8926f2a50a200000001625824299f90316d8b40002a1a668001be1129da0000000001c5a5180009d80006ba7380000000000000000028a800000106a2895d8898c58510002520000481fa28f0000000000002021b800000700000000010914a0978002649c686c80000023d00026f8002a8a3d8002819cf80011a02e00026a9689410351e20bea5c8e684200000000010f8cd23c279a502349829e01010e8a960fc1a4a3283d88f80002c9268001d513a1478000000e50000000001a88412400001ce83800000009419a0630000e71
  | 13 => 0x2018e000000000002e8c920fa4185715c0001dc00026510b0002409768600eaa790f080528b9fd00018216805210826800006a1831b00000000dd9b20b1943a8da8521f9e6949a2604ba2480028596b9c215914c92316c9fc8d100f8199b689b08d8471111b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8000526640315d0604c401469900857518121
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
  | 34 => 0xb0c
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140c
  | 38 => 0x140d
  | 39 => 0x140e
  | 40 => 0xb4b
  | 41 => 0xb4d
  | 42 => 0xb4e
  | 43 => 0x144b
  | 44 => 0x144d
  | 45 => 0x144e
  | 46 => 0xccd
  | 47 => 0xcce
  | 48 => 0x94055
  | 49 => 0x94056
  | 50 => 0x95395
  | 51 => 0x125395
  | 52 => 0x4955
  | 53 => 0x124955
  | 54 => 0x124956
  | 55 => 0x138955
  | 56 => 0x138956
  | 57 => 0x128996
  | 58 => 0x99296
  | 59 => 0xcb
  | 60 => 0xb0996
  | 61 => 0x98b16
  | 62 => 0x168b
  | 63 => 0x134b
  | 64 => 0x14b
  | 65 => 0x141296
  | 66 => 0x12c9d5
  | 67 => 0x9d2d5
  | 68 => 0xb49d5
  | 69 => 0x9cb55
  | 70 => 0x150c
  | 71 => 0x130c
  | 72 => 0x10c
  | 73 => 0x1452d5
  | 74 => 0x140b16
  | 75 => 0x24b
  | 76 => 0x16cb
  | 77 => 0xbcb
  | 78 => 0x19cb
  | 79 => 0x144b55
  | 80 => 0x154c
  | 81 => 0x20c
  | 82 => 0xb8c
  | 83 => 0x184c
  | 84 => 0x8c
  | 85 => 0x5555
  | 86 => 0x5695
  | 87 => 0x4956
  | 88 => 0x5516
  | 89 => 0x56d6
  | 90 => 0x15393
  | 91 => 0x11394
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1211
  | 6 => 2778
  | 5 => 1367
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (49240+((h/403+packedAt gbK7 (44807+(h % 403)*11) 11) % 1454)*12) 12
  | 6 => packedAt gbK6 (144456+((h/926+packedAt gbK6 (133344+(h % 926)*12) 12) % 4033)*13) 13
  | 5 => packedAt gbK5 (85658+((h/455+packedAt gbK5 (80653+(h % 455)*11) 11) % 1805)*12) 12
  | 4 => packedAt gbK4 (142+((h/1+packedAt gbK4 (140+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fe03ffc01fffffe03ffffff463f3f8ce3f1ff
  | 1 => 0xffffc07ffff00ffffc07ffffb9c8c8ff3e3e3f
  | 2 => 0xc0ffff8001fff03ffff83e00c1f0f0f3c3cfcc
  | 3 => 0xfffffffe00003fffffc000fe00ff03fc0ff0
  | 4 => 0xffffffffffffc000000000ffff0003fff000
  | 5 => 0xff0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x94005942055144a014a62aa0213138460d0d5
  | 1 => 0x7222c02992a08a94a404955418c848390e262a
  | 2 => 0x88b56a80513ea2276b903806c170b0d3834b4c
  | 3 => 0x10d9b34ee4030439d2e70018ee00ed02f40db0
  | 4 => 0x20fe3c7379cbcf0060c21060f7ed0003fbb000
  | 5 => 0x3c102003800c080183042180fdbefeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36645
namespace PEqualNP.Outside.L_meta_36645
open PEqualNP.Outside.L_meta_36645.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bgb_5_1344 : Interval gbAtlas 5 1344 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1367 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)))) (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152))) (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344))))))
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
theorem bgb_6_2752 : Interval gbAtlas 6 2752 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2778 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))) (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))))))
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
theorem bgb_7_1184 : Interval gbAtlas 7 1184 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1211 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)))) (concat (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
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
def fullWord : Sig := 0xeeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888eeeaeac8eca8e888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 3970492552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36645.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[2,6]⟩,⟨.or,[3,4]⟩,⟨.or,[2,5]⟩,⟨.and,[0,9]⟩,⟨.and,[8,10]⟩,⟨.or,[0,7]⟩,⟨.and,[3,4]⟩,⟨.or,[12,13]⟩,⟨.and,[1,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3970492552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3970492552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36645

open PEqualNP.Outside.L_meta_36645 in
theorem PEqualNP.Outside.L_meta_36645 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3970492552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3970492552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
