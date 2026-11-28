import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36653.Model
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


end PEqualNP.Outside.L_meta_36653.Model

namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
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

def SBf (j : Nat) : Nat := [4, 4, 7, 7, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 82]

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

end PEqualNP.Outside.L_meta_36653

namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
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
  | 2 => 0xfff87fe00ffffffffe01fe03fffffff0047ff8
  | 3 => 0xf0fffffff007fc03fffffffc07f007ffff8e3f
  | 4 => 0xfffffffff80003fffffffff80007fffff03f
  | 5 => 0xff007ffffffffffc0001fffffffff80007ffc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2010096152292428a224562c58b568b6a9b6db
  | 2 => 0x442692bb44b26a51451caf02ad5a7551a45b78
  | 3 => 0x8d4224ca6ea4529a69493b560663266b368e2d
  | 4 => 0xee84471388c763639191cd9b340c478dc77036
  | 5 => 0x8f7781c0f078383e1e1f1e3c78f840e07ed80
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000ccc0c0c0cc000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36653
namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
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
  | 2 => 0xf80fe01fe01fffc07c0fe07e07e0fff016327c
  | 3 => 0xfffffffe03ffffff0007fffff03fff83f8f
  | 4 => 0xfff0001fffffc0007fffff8007fffc001fc3f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8202142224204880851648a48a1451542d4b5
  | 2 => 0x556554ce51d4a91abe0aac56c568eba0d6325c
  | 3 => 0x468992949491b23256a81065965a22ca982b0a
  | 4 => 0x64cd1b19191923a3673cd941079cb0831d43e0
  | 5 => 0x870e1c1e1e1e3c3c7bcf1e79e410c30c1fbc00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36653
namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa80000000052380803074000004d00c3600f8f005801c0e9d52300340020c4110b425c00422000121465425009001a5600f1410981890a0880010c00011000094c3ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe801624000c040d80000083081faaa311099c86052d80270f03ab049b9e001d8b0d1f212d16a2890025a8269a998f80278028801897292a00072210028ba52b8c9a0a92a4909c0891811421a982261eac8000019b000000138e1d15951920a3a007800580068014932c18178a001201860c4c00302243070800500266c20c280000004080160210203bba8a87745150e7ca1a14f55242afa9a855c5350aeea2a15d14542bda8285785050b3ea6a16714d42d7a9285b75150b68a2a16ed41429e28285b85050a70a0a14f95042bb28e657551cca7ca9194f55232bb28c6575518ca7ca8194f55032afa9a835c535067ea898cf15131ea988633e54c867aa990d794f21aea9e435e53886baa710cf950219eaa0435e53902baa7205d94640baa8c819e539033aa7204f54a40db28c81b5519027ca1204f548409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2eca2185d544309f2a6413d54c837081904fd52209e2a4413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6105d94420baa8841b8400827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xa0e2000c60004810c514c5150b1b5314142c614c5050b335114142cc1445050a94644c431c594e51902396510020
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
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 1 => 0x3f80ffffe03f81ff83f03e0ffffc1f01d89fcc
  | 3 => 0x3fff03fffffffffffc003ff03fffffffe0e3ff
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x848a1008c489082014b14a114a2129540b2e15
  | 1 => 0x9526299143922ae58155168d96e51a0cd896cc
  | 3 => 0x22144aa20924614aa80825a4254a54a960c16a
  | 4 => 0x3458b34492074db34e6d810939b38831bd03b0
  | 5 => 0x3860c3871c3871dc738e39ce01c210c1f6f800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00eeaaaa88ee00aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36653
namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a51a440000000aa8003021b0a80026000c4920e28e210000023524c7813200000007c3173450022009cc163a015003c0870b48008001000004040300c040102043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2900001b3f210049004a3a005400004e02000f552e1a004d000109131420422a0b113c33002b00510800590005000a00032d3630105a242c4b000d3427581e06443d321c46531547382507561f0c1852434c484531390e1716003b0428371d0000350000194f0000262f233e4050570041220012000000000208100042c0850608000341428002184001214206081410101765190eeaa321d7d4d42ae29a85775150ae8a2a15ed4142bc28285ad4210aeca3995d54732b7296836d52d06bca720d754e41af298835d53106bca198d754e319faa2633c544c6dea498db14931bda826378504c73ea898e715131e7a9263cc524c7aea298f5d0531ea20a63db504c6b8a098f614131ac282635e530c67ca990cf55321ea98e435e53886baa710d794c21aea9843d531086bca7a05754f40afa9a815c53502dea4a05b14940bba8a817451502dca4205b54840aea8c615e508c2eca2185d54430eb288615d510c3aaa2185554430af28061da500c2bca7905754f209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af29e215d53c43aa6388760c310afa9c215c538427ea8884f15110afa9a215c53442dea4885b14910ea98a215e53042baa608760c010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2009ac02ec2031c10049602a39a01e50a018022a1018292802042211ea86050842c3150524c6c662d0531c6d50504c7185414131d2d48504c7485214131d4d04504c7504114131c595131c86d0604c721b418131086556194f40c5d91510c3146454430d1d89510c3446254430d4181510c2556194f20b418131c42d1610c310951953144314544c510d11493144259650c010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x81002000181509cb4114131c24a83026390e0464189510c308320c0a8861901886054430
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2667+((h/30+packedAt s3K4 (2457+(h % 30)*7) 7) % 121)*8) 8
  | 3 => packedAt s3K3 (990+((h/8+packedAt s3K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (250+((h/1+packedAt s3K2 (245+(h % 1)*5) 5) % 17)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffff01ffffffff03fffffe03fffffe3fc7ff
  | 1 => 0x3f80fffffff80ffffc0fc07fffffc07fcc7fc7
  | 2 => 0xc000fffe03fffffffff0007ffc0ffffff078ff
  | 4 => 0xffff000003fff01fffffff80000fff81ff80f8
  | 5 => 0xfffffffffc00001ffffffffffff00001ffff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x5086094c2889224500b2ca964152d4d215c35b
  | 1 => 0x52a5a145110e48b2c05522a96654c34cc1dc5
  | 2 => 0xb45494289aa249165550284d5909b9697068ae
  | 4 => 0x2618d8b1634481db9a69b301924e2e31ee80f0
  | 5 => 0x3860e0c183870e1ce38e3c71e3803041bb7600
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8a0a08080eaeac8c8a0a08080eaeac8c8a0a08080eaeac8c8a0a08080eaeac8c8a0a08080eaeac8c8a0a08080eaeac8c8a0a08080eaeac8c8a0a08080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36653
namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x16094e5001d18887183800410002830016001a5041002a245839f3678ba3008069a5aa49853204015488400056988a8003c0011c30835800400003ca700ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x268024a3000f8038800000000000000900160006002e2e8008390512a78000000000378000000eb4179f80000000143590adb0b52f802c00001d8000000000000b030013800010003680000d00001b041d31148006950e00000000002b8000000000000003803800000a9e80002d00008a2500002381800000228009800000000000001800000000002615a20780000008b72900048000000007003499a980211c30289b800039b1828000190033000013000016801733a0800f00000000329e2018b2000b8000000024000000110ca83a000000001a0000002b0000000000002a1a801f00000000000036000000000005ac918012000000020000000c27000021801c8daa8025af00010000002040001400010081000010000000010080002000000400010180c0201008040000000040000010000005005b94a43b6a9487765190eeaa321ddd4542ba28a85ad4210a7ca9994f55332bb28e657551ccadca5a0db54b419f28c836f52506d8a4a0d794c41aea98839e531073aa620cf94441db288833e54cc67aa998db94b31b6a9663b4418c67ea898cf15131b7a92636c524c7688298ded4131bc282633e54c867aa990ed10721b728c43ae41887588310cfd51219e2a2435e53086baa610ed10421e729843cd53086dca210f994421f3a0843ae41087588210f910421d220843e631087ca6210d794f40aea9e815f53502b8a6a05bd4940b6292817751502e8a2a05b94840b6a90819e418c33883187388630e610c615e508c27ca8184f55030b7290616d520c2eca2185d54430cf2a0619d540c39ca4187354830eb28861d5510c33c82186710430e710861cc210c2bca0187694030af29e415d53c827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca7885754f10ec186213e548427aa9085b94a10b6a9421b441843c843084fd51109e2a2215f53442b8a6885bd4910b629221b441043c84208760c010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1200478000002c72a5808000089a818000028008c0180000004140008a468000038000002e000000140103002a91854210b245210531cc104504c7155310421a998641086c56310421e198c41087856310421e194c41087855310421a919131086e0604c4219918552103844108630c5551510c345525443087594410c24d6508430e1104210c2346155020c994841843265408610e410430043c0210c010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x6100010a0aeb3188210c857694c4108682ba88210861815944108430
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (3510+((h/39+packedAt s4K4 (3159+(h % 39)*9) 9) % 271)*8) 8
  | 3 => packedAt s4K3 (960+((h/8+packedAt s4K3 (912+(h % 8)*6) 6) % 52)*6) 6
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffffff01fc07fff83e07fffff03e03fc9fe67
  | 2 => 0x7ffe07ffe0007ffffc007ffc1ffc003ff1e387
  | 3 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641234429a2130cab
  | 1 => 0x2a146221c912a4a581682a964d234294c87665
  | 2 => 0x4c28b54483ab496aac144d5916e9053971a386
  | 3 => 0x68b1468912320db34a59019218b39611ec0350
  | 5 => 0x70c1870e1c3c71dc739e71e380c21821bfd800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeac8eac8aa80aa80eac8eac8aa80aa80eac8eac8aa80aa80eac8eac8aa80aa80eac8eac8aa80aa80eac8eac8aa80aa80eac8eac8aa80aa80eac8eac8aa80aa80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36653
namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x41115320100000140144200da700000113e002000000000480000b00000004a2400000014801c680802eacc0000005001a000000c0041300011800000b0050495000e001800474f001800026007078080000408002000010414000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20ee20fd20fc20ec20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2b9c961b8e800012299081800000248b03ac978018a0a78aa39f231f859aa000000b90001800031b26849902800c130000001e148d2c2aa7288709940f802d8d802500240817000c92a11d810411800016ad1d07a20e290611020895198f2b1580a805229c0a092a1a259e93a62186880f0a0d209045410030002011a50102000078306401010201a80bb28e877551d0edca521db54a43bb28c87755190edca421db54843bba8a85745150adaa7195b942329faa2653c544caeea2995d14532bda826578504cb5ea8996b15132e7a9a65e7514cbc8a2997ad4132b628265e8504cad0a0995b94832b7a92836c525076a8220cf953319eaa6636e52cc6daa598cf952319eaa4636e520c6daa418cfd51219e2a2436e52d02daa5a057d4d40ae29a816f52502d8a4a05dd4540ba28a817651102eaa2205b94b30b6a96613f544c278a8985bd4930b62926177514c2e8a2984f950309eaa0616e520c2daa4185d94430baa88613e548827aa9105d94620baa8c41ae548835aa9105bd4e20b6a9c41e651883caa3105b94220b7a98416d53082dca0107a94020f598041e830082dca5885b54b109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4020a00ce860050c9150514cb2b5414132ca150504cb635114132d8144504caa46250441c99525188269650c020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (802+((h/14+packedAt s5K5 (704+(h % 14)*7) 7) % 90)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s5K3 (312+((h/2+packedAt s5K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fffffffffffffe07fe03ffffffffffe31ffff
  | 1 => 0xe03f03f80fe07fff83ffc1f81f07c07fde6267
  | 2 => 0x3ffffff0007ffffc0001fffff8007fe07f87
  | 3 => 0xffc003ffffff81fffffffe001fffff81ff83f8
  | 4 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x418108892248104014a41259230c532210acab
  | 1 => 0xca8a5990e48aa4e5816d50ab0d468574d66265
  | 2 => 0x952c332241d349aaac19213656d20a59e05786
  | 3 => 0x628a24489120d334a51a40418e32c116b0350
  | 4 => 0x1830c3870e1c71dc739e39c780843061bdf800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80eea0aa80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36653
namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x210058010ca00c831c1b505840101ea000780002001fb81f42439242843a980138000b8002000004d2c3290029040241d0da454401d804a2673c4602228611d3187cd8d2a00000000000000011830e06085010000102140008e0214000000407ff43017f90c01fd43017f10c03fe52007f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32007f4c803fc3201ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc2101ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24200cff1921001df8c908003ff63840017fb1c200bff98e10015fcc708003fd63840017eb1c200bff18e10015f8c708033ff4384017ff21c2000ff50e1005ff88708003ff62840017fb14200aff98a1000dfcc508003fd62840017eb14200aff18a1000df8c50802bfe5284001fea94200aff14a10067fe850802bfe4284001fea14200aff10a1005ffe650802bfe3284001fe994200aff0ca10005fac308033ff4184001ff20c2000ff50610067f8830802fff3184001ff18c2000ff4c61005ff8630802bff2184001ff10c2000ff48610057f84308002fe6084019ffa042000ff90210007fa8108033fc4084017ff9842000ff8c210007fa610802ffc3084015ff9042000ff88210007fa410802bfc2084001ff8842000fdc4210007f62108003ff64440017fb222000efd91100057ec888027fe64440077f3222000ff59110005fac888027fc64440077e3222000ef1911001d78c888003ff63440017fb1a2000f7d8d10005bec688023fe63440057f31a2000ff58d10005fac688023fc63440057e31a2000f718d10015b8c688027ff4344011ff21a2000ff50d10047f88688003ff62440017fb122000fbd8910005dec48801ffe62440037f3122000ff58910005fac48801ffc62440037e3122000fb1891000dd8c48801ffe5244001fea922007ff1491004ffe848801ffe4244001fea122007ff10910047fe648801ffe3244001fe9922007ff0c91004ffe8288003fe4144001fb20a2000ff50510007ea8288027fc4144011ff98a2000ff8c510007ec6288003fd3144001fa98a2008ff0c51003ffe4288003fe2144001fe90a2007ff0851004ffe8088003fe4044001fea022009ff10110047fe6088003fe3044001fe9822008ff0c11003ffe4088003fe2044001fe9022007ff08110007fe2088003fb1044001ff0822000fd84110007fec808002ff640400dff3202003bf990100077cc80800ebe6404001feb202000bf590100077ac808002bd640400dfe3202003bf19010007fec608002ff630400bff3182002bf98c10007fac608002fd630400bfe3182002bf18c10037fe8608017fe4304001fea182005ff10c10007fec408002ff6204009ff3102001bf98810007fac408002fd6204009fe3102001bf18810027fca408003fd5204009fe2902006ffd0810027fc8408003fd4204009fe2102005ffcc810027fc6408003fd3204009fe1902000bf98410037fe8208003fe4104001fea082006ff1041002ffe6208003fe3104001fe9882005ff0c410027fe4208003fe2104001fe9082004ff08410005fcc00801bff4004001ff2002000ff50010037f88008017ff3004001ff1802000ff4c01002ff86008013ff2004001ff1002000ff48010027f84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x7ec5288003ffa144001ff90a2000ffa8510007fc4288003ff9944001ff8ca2000ffa6510007fc3288001ffb0c4000ff98620005fcc310003fd61880017eb0c4000ff186200b7fea310003fe5188001fea8c4016ff146200affe8310003fe4188001fea0c4015ff106200a7fe6310003fe3188001fe98c4014ff0c62000ffe4310007fe2188001f710c4001ff4862000ff84310007ec21880037f3044016ffd4220007fca11005bfc508802bffa044000ff90220007fa8110057fc4088029ff9844000ff8c220007fa6110053fc3088003ff9044001fbc822000ff64110007fc2088003fc1044000ffd9520005feca900037f65480013fb2a4012ff9952009dfcca90003fd65480017eb2a4012ff1952009df8ca900037c65480273e32a4000ffd9120005fec890047fe64480077f3224000ff59120005fac890047fc64480077e3224012ffd512008ffca890003fd5448023fe2a24000ffd8d20005fec690043fe63480057f31a4000ff58d20005fac690043fc63480057e31a4012ffd4d20087fca690003fd5348021fe29a4011ffd0d20087fc8690003fd4348021fe21a4001bfd892000ffea490007fe5248003f72924001ff54920007daa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000fdc6490007fd3248001f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148025ffa8a4000ff94520007faa29004bfc5148023ffa0a4000ff90520007fa8290047fc4148021ff98a4000ff8c520007fa6290043fc3148003ff90a4001ff8852000ffa4290007fc21480037fb024012ffd4120007fca090003fd5048025fe2824011ffd0120007fc8090003fd4048023fe2024010ffcc120007fc6090003fd3048021fe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048001ffb262000bfd931007ffcc98800efe64c4001feb262000bf5931007ff8c98800efc64c4001ffb1e2000bfd8f10077fcc78800afe63c4001feb1e2000bf58f10077f8c78800afc63c401fffa1e200eff90f10007fa878803bfc43c4001ffb162000bfd8b1006ffcc588006fe62c4001feb162000bf58b1006ff8c588006fc62c401bff2962000ff54b1006ff8a58803fff42c401bff2162000ff50b1006ff8858803bff32c401bff1962000ff4cb1006ff8658803fff41c4001ff20e2000fd90710007fa8388003f541c401ffe20e200effcc710007fc6388003f631c4001fe98e2000fd4c710077f86388037ff21c4001ff10e2000ff4871006ff8438803fff40c4001ff2062000ff5031007ff8818803bff30c4001ff1862000ff4c310077f86188037ff20c4001ff1062000ff4831006ff84188003ff64840017fb24200cff9921001dfcc908003fd64840017eb
  | 2 => 0x4000dfcc4a0003fd6250037fe3128001bf189400dffca4a0003fd5250037fe2928003ffd094001ffc84a000ffd4250007fe212801cffcc9400dffc64a0003fd3250037fe1928000ffd8540005fec2a0003fe6150001feb0a8000ff18540005f8c2a000fff4150007dfa0a8003ff9054001ffa82a0003bd4150007fe20a801cffcc540007fc62a0003fd3150039fe18a801bffc8540007fc42a0003fd2150037fe10a8003bfd814001ffe80a000ffb4050007ff2028000ef9014001ff880a000fbc4050007fc202801cffcc1400e7f860a006fff2050037fe1028000ffd9230005fec91806bfe648c0077f3246000ff59230005fac91806bfc648c0077e3246002bf58e30017fe871806bdf438c005ff21c6002ff50e30017f8871800bdc438c001ffb146019ff98a3000dfcc518003fd628c0017eb146019ff18a3000df8c518067fe528c001fea946019ff14a300d7fe8518067fe428c001fea146019ff10a30017fe651800bfe328c005fe9946002ff0ca30007fec318003fe618c0017f30c6000ff58630005fac318003fc618c035ffa0c6000ff90630007fa831806bfc418c005ff98c6002ff8c630007bc631800bfd318c005fe18c6002f70c6300cffe4318003fe218c001fe90c6019ff08630015fcc11806bff408c001ff2046000ff502300d7f8811800bff308c005ef9846002fecc230017f8611800bf8308c033ff9046019ff08230007fec898002ff644c001dfb226000afd91300c7fcc89800efe644c001feb226000bf591300c7f8c89800efc644c001de3226003af19130015fec69800bff434c005ff21a6002ff50d30017f88698003ff624c0017fb126017ff9893000dfcc498003fd624c02ffe3126001bf189300bffca498003fd524c02ffe2926018ffd09300bffc8498003fd424c02ffe2126002ffcc930017fc649800bfd324c005fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c298063ff414c001ff20a6000ff505300c7f8829800bff314c005ff18a6002ff4c530017f8629805fff214c001ff10a6000ff485300bff8429800aff604c031ffa026000ff90130007fa8098063fc404c005ff9826002fecc130017fc6098003de304c005fe1826002f70c130017f0609805fff204c02ffe1026000ffd9620005fecb1005bfe65880277f32c4000ff59620005facb1005bfc65880277e32c4000ffd9220005fec910057fe64880077f3244000ff59220005fac910057fc64880077e3244016ffd52200affca910003fd548802bfe2a44000ffd8e20005fec710053fe63880057f31c4000ff58e20005fac710053fc63880057e31c4016ffd4e200a7fca710003fd5388029fe29c4015ffd0e200a7fc8710003fd4388029fe21c4001bf58a2000ffea51005bef5288003ff2944001ff54a2000ff8a51000
  | 3 => 0xe29c4223ffd0e21117fc8710803fd4388445fe21c4201bf58a2100ffea510807fe5288403f72944201ff54a21007daa510807fc5288403ffa144223fbd0a2100ffc8510807fd4288403fe2144201fb10a2100ffe6510807fe3288403f71944201ff4ca21007da6510807fc32884037f30c4224ffd4621007fca310893fc5188447ffa0c4200ff90621007fa831088ffc4188445ff98c4200ff8c621007fa631088bfc3188403ff90c4201fbc862100fee4310807fc2188403fa10c4200ffd8221007fcc110802fe6088401feb044200bf58221007f8c110893ff5088449fe2844223ffd022111ff8811088bff3088445fe1844201ffc822100ff84110807ec2088401ffb2a4200bfd952110ffcca9084efe6548401feb2a4200bf5952110ff8ca9084efc6548401ffb224200bfd9121107fcc89080efe6448401feb224200bf59121107f8c89080efc6448443ffaa24220ff95121007faa890883fc5448401ffb1a4200bfd8d210fffcc69080afe6348401feb1a4200bf58d210fff8c69080afc6348443ffa9a421fff94d21007faa69087ffc5348441ffa1a421fff90d21007fa869087ffc43484037fb124201ffd492100ffca490807fd5248403fe2924201ffd092100ffc8490807fd4248403fe2124201ffcc92100ffc6490807fd3248403fe1924201bfd852110ffea290803fe5148401fea8a4221ff14521107fe8290803fe4148401fea0a4220ff105210fffe6290803fe3148401fe98a421fff0c52100ffe4290807f72148403ff10a4200fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c090887ff5048443fe2824220ffd0121107f8809087fff304843ffe1824201ffc812100ff8409080efd6490001ffb1c801eff98e40015fcc720003fd63900017eb1c801eff18e40015f8c72000fff4390007ff21c801eef90e4001ffa872000ffc4390007de21c8000ffd8a400effcc520006fe6290001feb148000bf58a400eff8c520006fc629003bff2948000ff54a400eff8a52000fff4290007ff2148003ff50a4001ff8852007bff329003bff1948000ff4ca400eff86520003ff6190001ff30c8000bf98640007fac320002fd6190001fe30c8003ffd064001ffc8320003be4190007fea0c8003ff1064001f78832007bff3190001ff18c8000ff4c6400f7f86320077ff2190001ff10c8000ff486400eff8432000efe6090007ffa048003efd024001ff6812000ffc4090007fc204801effcc2400f7f86120077ff209003bfe1048003bfd9140007fec6a0002ff6350001efb1a8000b7d8d400e7fcc6a000afe6350001feb1a801cff18d40015f8c6a0003dc63500056e31a8003ffd0d4001f7e86a000ffe4350007fea1a8000ef50d4001ff886a0003ff62500017fb12801bff989
  | 4 => 0x802fe6090401feb048200bf58241007f8c12080fff4090407fe2048203ef10241167fe61208b3fc3090457ff904822bff0824101dfec8a0803ff63504017fb1a822aff98d41015fcc6a0803fd6350455fe31a8202bf18d4101ffe86a080ffe4350455df21a8203ff50d4101ff886a080fbc4350401ffb128200bfd8941007dec4a0802ef6250453ff3128201bf98941007fac4a08a7fc62504037e3128200fb1894100dd8c4a08a7fe5250401fea928229ff1494101ffe84a080ffe4250407fea128203ff10941157fe64a08a7fe3250401fe9928229ff0c94101dfec2a080fff4150407fba0a8203ff905410077c82a080ffc4150407de20a8203fd1054101f6882a08abff3150455fe18a8229ffc854114ff842a0803ff60504017fb028200ff98141007fac0a0803fc60504017e3028203ffd014101f7e80a080ffc4050455ff982822aff0c14114ffe40a08a7fc2050401ffb246200bfd9231147fcc91880efe648c401df3246203af99231007fac918802fd648c401deb246200af59231147f8c91880efc648c4057eb1c6202ffd0e31017fc871880bfd438c405fe21c6200ffd8a3113ffcc518806fe628c401feb146200bf58a3113ff8c518806fc628c44fff2946200ff54a3113ff8a5188a3ff428c44fff2146200ff50a3113ff8851880bff328c405ff1946202ff4ca31017f8651880afe618c451ffa0c6200ff90631007fa83188a3fc418c405ff98c6202f7cc631017ee631880bfc318c405fa18c6227ffc863113ff84318803ff608c401ff3046200bf98231007fac118802fd608c401fe3046228ffd0231147f8811880bff308c405fe1846202f70c23113ffe411889ffc208c401ffb226200bfd9131137fcc89880efe644c401feb226200bf59131137f8c89880efc644c4057fb1a6202ffd0d31017fc869880bfd434c405fe21a6200ffd8931005fec498897fe624c4037f3126200ff5893112ff8c498806fc624c44bff2926200ff5493112ff8a49889bff424c44bff2126200ff5093112ff8849880bff324c405ff1926202ff4c931017f8649880aff614c44dffa0a6200ff90531007fa829889bfc414c405ff98a6202fdcc531017fc6298803de314c405fe18a6202f70c531017e86298897ff214c44bfe10a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c09889bff404c44dfe2026202ffcc131017f86098897ff204c44bfe1026200ffd9621005fecb10893fe65884277f32c4200ff59621005facb10893fc65884277e32c4200ffd9221005fec91088ffe64884077f3244200ff59221005fac91088ffc64884077e3244224ffd522111ffca910803fd5488447fe2a44200ffd8e21005fec71088bfe63884057f31c4200ff58e21005fac71088bfc63884057e31c4224ffd4e21117fca710803fd5388445f
  | 5 => 0xc95200ff864a9003ff61548017fb0aa400ff98552007fac2a9003fc61548017e30aa432ffd0552197f882a90c7ff3154863fe18aa401ffc855200ff842a9007ec2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a400bf18152197fe80a90cbfc4054863ff982a431ff0c15200ffe40a9007ef2054803fe102a400ffd9542005fecaa10c3fe65508277f32a8400ff59542005facaa10c3fc65508277e32a8401bfd914201ffea8a100ffe5450807feaa28403ff15142007fec6a1002ff635085fff31a8402bf98d42007fac6a10bffc63508057e31a8430ffd4d4217ffca6a10bffc5350807ffa1a8403ff90d4201ffa86a100ffc43508037fb128401ffd494200ffca4a1007fd5250803fe2928401ffd094201fde84a1007fe4250803df2128401ff1094200f7884a1007ec4250803ff9928401ff8c94200fdc64a1007fc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8400bf18542187fea2a10c3fc5150807ffa0a8403ff1054217ffe62a10bffc3150803ff90a8401ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050861ffa828430ff1414201ffe80a100ffc405085fff982842fff0c14200ffe40a1007fc2050801ffb2a6400bfd9532177fcca9904efe654c801feb2a6400bf59532177f8ca9904efc654c801ffb226400bfd913216ffcc89900efe644c801feb226400bf5913216ff8c89900efc644c85dffaa2642dff95132007faa8990b7fc544c8037fb1a6402ffd4d32017fca69900bfd534c805fe29a6402ffd0d32017fc869900bfd434c805fe21a6401bfd893200ffea4990bbef524c803ff2926401ff5493200ff8a499007ec524c803ffa126401ff9093200fdc8499007fd424c801f6a126401ff1093200ffe649900bef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003fe614c801feb0a6400ff18532005f8c2990bbff514c85dfe28a642dffd053216ff8829900bff314c805fe18a6401ffc853200ff84299007ec214c801ffb026400bfd8132007fcc099003fd604c801fe3026400bf18132177fea0990bbfc504c85bffa02642dff10132017fe609900bfc304c803ff9026401fbc813200ff8409900efd6490401ffb1c822cff98e41015fcc720803fd63904017eb1c822cff18e41015f8c72080fff4390407dfa1c8203ff90e4101ffa8720803bd4390407fe21c8200ffd8a4115ffcc520806fe6290401feb148200bf58a4115ff8c520806fc6290457ff2948200ff54a4115ff8a52080fff4290407ff2148203ff50a4101ff885208b3ff3290457ff1948200ff4ca4115ff8652080efe6190407ffa0c8203efd064101fee832080ffc4190407fa20c822cffcc641167f863208afff2190457fe10c8200ffd8241007fcc120
  | 6 => 0x80080280480680080081100000100080280080800300300380100000400800180080580680400180380280000000100400180080280b80080080300680080800000180080300c01500d80080180880200c01c81100300000600900080002100200000000000000000180080a80100200c00080100680680000001180300000280000080480700000000300080000380280580080500180000000100280a80000d00080300100100000000000000000100300680000080500e80000100280080080500180480300100001900000280680600480080080b00900100380100080080780180500500100000081080280100380000080580480200480100000280080380180001001180f00200200101580200980080000100680b80000880300080000280080480000000600000100800a00000600100200080001901400000280400680500e00200700100180380780080200480001880000300000300080000600081880100000000182780180000700000b00c00000000080580000500000200080100180300700080480680300000f80000600000000000b00000300300080800100100000480080280000000000081180700480000980200680200a80080000600300280100280100001800180080a80800100100380d00180281300200080480180000900080080880080480001a00700000680001080000000280300400100501380000002e00380380080000c80180700080180200180000180b00000000000180000780180000100000180b80c80f00880080380280b00680000000200400200780080200500000000c02300780000280181a80e00280180000080000000000b00000080200200002900580000100000480280a01300000000c00500180600000780080600000380480100383280000380980aff6450c057fb1a8602ffd0d4301fbe86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c01ffb128600bfd894319ffcc4a1806fe6250c01feb128633ff1894300df8c4a18cffe5250c67fe2928603ffd094301ffc84a180ffc4250c05ff9928602ff8c943017f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a8603ffd054301ff882a180fbc4150c05ff98a8602ff0c54319ffe42a18cffc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028600bf1814301ffe80a180fbf4050c07fe2028602ffcc143017f860a18cfff2050c67fe1028600ffd9152005fec8a90cbfe64548077f322a400ff59152197f8c8a900efc6454801ffb1aa400bfd8d5218ffcc6a900afe6354801feb1aa431ff18d52015f8c6a90cbff4354863ff21aa400ff50d5218ff886a9006ff6254803ff292a401df9495200ff8a4a9007ec5254803b6292a401ffd095200ffc84a9007fc4254803ff992a401ff8
  | 7 => 0x14c11080000000000012800002744b0a112a2baa7f051a9d48a2873991fe53529622e4258c23ed80047f4d4070c3a4ef02811e4b04c00003b14b29f530b08f1560eb43c2c23ec45f36b05da5a0000d5439aced1200029114f1e650b05f2480c30451ea2c93ce94221e5160005665771b31730e226736d1c800017785b10151e1250002ae8a341146d80042c56443390db2056d0081e14ed3d00871762272e000010c0594934a40005032f238b0ca0003c709a0002789ad11d2bb0da0ccbea00013f9f5c7a4cb57206dbd82bc45d0003733d64e7078cbc515068000084103b0035a2f91313bac188ed3010222c51bc3581f224138e0001873bf000438436bb3cda43d0f00239aaad118e0003e034a07423634e4495555321bd55bb880e48bd00049e2d2301c1531309504e0bec1f1542290f080000051d4d10003d9040216d2728c9270004843a243512931446c8c7d34a6aaf82ca4db0000003d21c94723253d72790003c087e8f210f39a35880002a4ea4279c52420005698002aa324cc823697013317a1ce40ba210ee00b4a154e9a3573d7900002b27a0000000c51de0003863e73b09363744190c639313b05fa121bf5610ec0a61d251a1104232d731955c1714793ab28f14a4402a23c20001d62830001008fb1c117d53829f3b713957537a4e1574a11c3206f9132cc09d2904ba14702180011842a25e0002cd8000000001e500000013d56b30e4cd53000018f3a84c5000000354295966c32b21053c2b00036600056c1df0003e51071342263ca20943600001b02682b8bcb4506903e4cf0000001cc46fbcf00037f00006038941432e31f9321da5470620340b63840c6c8b0000c1ad44900000001fb00000004f0cd00015316600000039100003120c8cf3162d51432af3311624850003a280c36317800023b0720000cdaed15c8000003828f29dc33c3d50004480000000000a73171a828a5328000000730000000004301a628bbf839c3548000004250e695a316cb60790000002281ee0000000819971173b299b463190215cb21be524396c0603942682ed689800de38c37b2cb8000000000ca9c33f2d1b0812d083a00010280042d46eadcc5a43300500080000400100000a00080000401f00280080c00b80c00001e00400a80001c80080200880000280700000c80080400c80480500000200180d80000080b00080700180200080200000001d00500080702400400080d80100000000400c80080100000400c00b00700080400180001180580480000080100000000300300080080080380480780000080780b00501080000000300000300080480180100400000080080c00e00580b00300380200100300000080000080000000080000100f00500280100880100f01000000080502580380100080100000100000801800000080180300
  | 8 => 0xa25480a411f1025520cb8004c700046921702540b27e4b42d654e53d07bd75a5507d000259a522650002778289922fc29c01c15700000000036a5050c00000001350002030000000000000000004370000003ff00500000000000014010d0b74892b10003af2630a000046b86b2549740c38003728000040004a635780042f1b400005e45fbbba48bc004300021c39850000000053e09e54446480000f51f1850003500000534583e9a621550ea4698004be48619422552e48e3e80002ad252bba23d33024da3300035c19c57b4bd4715401f38000002580000aa00053a90aa140912f53bd80025b2eb45c0ff1cfb472a548c33337fca34f61378004e61fd0003040234f32cf05ebcc3770003f12c02b212b2154c102d00045b18f8003461eb1d116d3bc8004f7515b1126d1f34d00002d28670be253bf01305222543f40891a90930000e02195561d03ad533a010002e646b3d101129400000019f430b2c2231cd00003d53100000046ab520151dd26111107a1953530fe00011a0000ac34d3bd1db9a680053a0002693ae3960001503f50088f129a882cfe0b02db18819300055f257025d4d0e62b31a521a4831d5367455b901193e7a38000015ca51c60a38824443f8c0a2ef234ac745528d0c095b9c24f85094df369353bcb0172d68002402a754903025d2cd56a1452600b0c9f190c740123e127d1cb4fa2341bb3ecd293f1a534280000b2214a909ec00009b0228dd0100001d95190f194d00020a0ad3f930f470c1e43594b0ab42b87f97e3360970318c9a5893c46a00000056ccc94a200001d08e0fa2b80001e583807c56f22455103512c2db8000500d40521f90000000000003a62a452f5420bda0ba720b849426f21300000000055847640e39f0d02e33680d81db32746413380007825f2cf9ab360029079a86070000147a082979e838d21f37844736c03290b2d90003c806600021b48132a4e82b8d410611481260c451738735d4e228b50f073bf622c4d92ba09f51000230933808b2973db8cc57e22252c2a91ac5369d2cdc2b52ff0001c70c752808056842600004d25797b4e9132a4d50d38bd70c9a4042992f04489980000002713769223e400036e00027649d01782e4fc3282289a28db465a3c3db3415718582ccb954e40330001a03f724e80050e2d9ac10001ba0b2adf1a13851ed3fb57d00031f00031b00028d8e32dd1e30003050004620000000e52e824b2050000000004e5459143800405024d2d162bb32d3276b6cb791b853f4c606e4fd48842880aba32781b956a84935f1821033153aa0003750bfa13b1ba68446498000305af416c3fc3b6a7347044c0a58f90000000f401800000041833437110681955b32235538241000005a36f00000028ab3a51680600004b0004805530b30000000000001205113c505d0b4000
  | 9 => 0x51002b62da144a853f5afb12fa1853180025590186c807b1c2450f633937d38a0c14a801a000517b8000035b4210005250652c6071b06bbb4d24a90b54564130768a2d141ae4b93921e212420d18449921110c80000018b2590c2800083329536275bb800044e23702c0004a00005702e23d302400000000011c0005462a839710810ba323bebc62988003b95330df0001f69522804179791910d631d0550e70bf5592ac193cec43e25c10927523029e2dac60d5aa4983c0001680001a5d3409c42016f37c4cc0004733702442983cd3e91b23da34844244523f1c2d630808984170004c40000004ee00055a2128001ca0000000002d000000029a4c09863230003afd7a00000046747d3a933530c2fa2502bd2adb1233b4b800e1cf05cbbe0ff95c3bfa08bb4aa00003b990e12d2d1b2611b172af106a1e6b020a954c07ac78104d082bf0f84a715e109a740003c132d1f70000308004530210001408001a700032b8413eb8002ce1f805291248d05633f4dd05c2432ea43f4ac0000d357c19e0990bc456800302cbf3100002d800008518d5308004d308c4ad2e92d880047e4820003dc0000e80000002378c88001770d7438b6516e0000000003d400016528e2e700000020b1e0565000077a88449a0c1414bb81f3564eb229d45462951269d4dbf697221027b4083833e315f4291892f317f4c24fb1e70164d828fb30c1d1aa07dbe8ab040aa4bd200cb1610ba0860003a40000001b13fa3a047700a51842acb545249200055e53956baee0b13a1d064574f547c42728c0bb0002390000000004090a53ac2004bb12e0efcaf3ef2cb30d34323a3c91a1a9695b4663a15690003df0fd0004b103f3f7bc337e50746f5540e5c4f39d0ef0005710e900000000046507115d41c00001680026e475116050a0799d55716b91424e20439b52fc3441200033e5264e32060000000643620002c80b1800000000000000072a4f5398320000000ce36bcf680000000000022a00000012318c00000053b0002c426c0000003dcbc4572d7321d49b36440d04814616306f0903070ceab913a00046d00054a47b1371440002b40005500002fd5014604ff2ae4393e611524728912f02f9e949534920e3fd2fe57638152a14890e9b02704d556703b2ec20f0015740034310000203eaaa141646e04a42408840200018a0000003cf80000016938f5022ab50c2563514de30a97c0001043de0003b426604c0001c6c61cae395c31a4aa492b9bf24f948f32f0e3a163a71b6437af730a0000e14b34f20573443245622640003724d60f754328202d9059d83b5a0a9a41642f62843fe04712133d1fa111a949d3044277205bb2403523c6c4f40094413ed06c0074220c937609656026a0d93575234683615041c052b1bcd4b20f9ff1834d700022b44a3ee2513f340f5388
  | 10 => 0x514ab24c4513a541b10a31e2202920fc0f32d5abe4974c31814669c400023e014d3c34230320742f80d01e000033b181af26b07cb2b24fcacade14900016b34b009a9320207e0000f54070af8000003f390f80000031a03601400054f0a800006d35e0b906ec0c1e43b542e0461f056e22d5228a48000af06307b00000002cbb608d537000105299c4d0000000000001993321f41600001382d796756e8d149600022f3bc0004431062952e42098c825692e9f628982f246394210800454000293c5013e14e487424d5d33724a34c1b739e51c0750dc07f4002a64ce28ecca27c1f4bce46145e13f0375678771d7359434c29d2129b0000924b705449c3f48d21960e44f041a0761a242e8ae2dc19a0002e51f14f12b7cfb8000005249d42814911590001580942c34aa17534043b16a0004e03e22310005783083060421ef3eb1948134639b540134f235d0a3b024ca06ab73dd02782608a2a33b18002e11a9beed131fc56fa3
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe749841007cfd749841001cfc7498410014fe7398410074fd7398410014fc739841000cfe729841006cfd729841000cfc729841007cff769041001cfd769041001ebe6490410006bd649041007ef66190410005fa7090410005f9709041007cff765041001ebe6450410006bd6450410005ef7250410025ec725041007ef66150410037b44150410074ff768c410014fd768c410035be748c410005bd748c410146be648c410006bd648c410016de638c410006dd638c410076f6618c410005fa708c410005f9708c410074ff764c410136be644c410006bd644c410076f6614c41002fd4314c41006cff768841000cfd768841011ebe6488410006bd648841000eee6288410006ed6288410005fa7088410005f9708841006cff7648410106be6448410006bd644841001cfe7498010064fd749801001cfc7498010014fe739801005cfd7398010014fc739801000cfe7298010054fd729801000cfc729801003cfd7198010064ff769001001cfe769001001cfd7690010034fc769001001ebe6490010006bd6490010005f67190010005f57190010064ff765001001ebe6450010006bd6450010005df735001002ddc735001005cff768c010014fe768c010014fd768c01002cfc768c0100d6be648c010006bd648c010016de638c010006dd638c010005f6718c010005f5718c01005cff764c010005bf744c010035bc744c0100c6be644c010006bd644c010054ff768801000cfe768801000cfd7688010024fc76880100aebe6488010006bd648801000eee6288010006ed6288010005f67188010005f57188010054ff76480100057f75480101a57c754801008ebe6448010006bd644801007ebe64c4010006bd64c401006ef576c4010006f764c4010007b664c4010006f564c4010007b564c4010006b564c4010006f763c4010006f563c4010066be6484010006bd6484010005f57184010006f66184010025f97684010056f9768401000cf97684010007ba6484010007b96484010005f97184010006fa6184010007f26184010004ff7644010005bf7444010035bc744401004ebe6444010006bd6444010005df734401002ddc7344010005ef7244010025ec7244010005f77644010006f77644010004f77644010007b77444010007b47444010006f76444010007b66444010006f56444010007b56444010006b56444010007d77344010007d47344010006f76344010006f56344010007e77244010007e47244010005f77044010006f66044010007f25044010007f15044010005fb7644010006fb7644010004fb7644010007bb7444010007b87444010007ba6444010007b96444010007db7344010007d87344010007eb7244010007e87244010005fb7144010007f37144010006fa6144010007f26144010007f25144010007f15144010
  | 1 => 0x9010036bf4259010006be4259010036bc425901001cff715901001cfd7159010034fc7159010036bc415901001cff705901001cfd7059010034fc7059010036bc4059010035bf7659010036bf765901001cbf7659010006be6359010006bc6359010006be6259010006bc6259010006bf7359010006be7359010006bd7359010006bc7359010006bf7259010006be7259010006bd7259010006bc7259010006be5259010006bc5259010006bf3259010006be3259010006bc3259010036bf7159010006be7159010006bc7159010006bf3159010006bc3159010006bf2159010006bc2159010036bf7059010006be7059010006bc7059010006bf3059010006bc3059010006bf2059010006bc2059010006bc1059010035be74d8c10005bd74d8c10006be64d8c10006bd64d8c1002ede63d8c1001cfe74d8c10006be74d8c1001cbe74d8c10004fd74d8c10006bd74d8c10004bd74d8c1001cfc74d8c1002cfd73d8c1000cfe72d8c10004fd72d8c1000cfc72d8c10074fe71d8c10006f671d8c1005cfe70d8c10006fa70d8c10014ff7658c10006be6458c10006bd6458c1002edc6358c10004ff7458c1001cfe7458c1001cfc7458c10006df7358c10004ff7258c1000cfe7258c1000cfc7258c1002edf3258c10014ff7158c10014fd7158c1002cfc7158c1002edc3158c10014ff7058c10014fd7058c1002cfc7058c1002edc3058c10004ff7650c10004fe7650c10004fd7650c10004fc7650c1001ebe6450c10006bd6450c10005fb7050c10005f87050c10035be74d8810005bd74d8810006be64d8810006bd64d8810026ee62d881009cfe75d8810004fd75d881009cfc75d881001cfe74d8810006be74d881001cbe74d8810004fd74d8810006bd74d8810004bd74d881001cfc74d8810014fe73d8810004fd73d8810014fc73d8810024fd72d881006cfe71d8810006f671d8810054fe70d8810006fa70d881000cff7658810006be6458810006bd6458810026ec6258810004ff755881009cfe755881009cfc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810014fc7358810006ef7258810026ee5258810026ee325881000cff715881000cfd7158810024fc7158810026ec215881000cff705881000cfd7058810024fc7058810026ec2058810004ff7654810004fe7654810004fd7654810004fc7654810196be6454810006bd645481000eee6254810006ed62548100276c5254810004ff7650810004fe7650810004fd7650810004fc765081001ebe6450810006bd6450810005f77150810005f47150810004ff764c810004fe764c810004fd764c810004fc764c81016ebe644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c81001cf
  | 2 => 0x12eec624c510005fb704c510005f8704c510045f4764c510016f4764c510014f4764c510005f7744c510005f5744c510007b7644c510007b4644c510045f7734c510007d7734c510007d7634c510016f6634c510016f4634c510047d4634c510016d4634c510007e7624c510007e4624c510007f3704c510005f4704c510007f0704c510054fe76885100067f65885101267c6588510006bf648851011ebc6488510006df6388510116dc6388510006ef628851000eec628851000cfc76485100067f654851010e7c6548510006bf6448510106bc6448510006df63485100fedc6348510006ef624851000eec6248510005fb7048510005f8704851007cfe7690110006bf649011001ebc6490110006df63901100f6dc6390110006ef62901100eeec6290110007b6419011001cff765011004cfd765011001cfc7650110006bf645011001ebc6450110005df7350110045dc7350110006df63501100e6dc6350110006ef62501100deec6250110005f77150110005f47150110007b54150110074fe768c110006bf648c1100d6bc648c110006df638c110016dc638c110006ef628c1100ceec628c110007d6318c110014ff764c110044fd764c110014fc764c110005bf744c11004dbc744c110006bf644c1100c6bc644c110006df634c110016dc634c110006ef624c1100beec624c110005f7714c110005f4714c11006cfe76881100067f65881100b67c6588110006bf64881100aebc6488110006df63881100a6dc6388110006ef628811000eec628811000cff764811003cfd764811000cfc76481100057f75481101ad7c75481100067f65481100967c6548110006bf644811008ebc6448110006df6348110086dc6348110006ef624811000eec6248110005f77148110005f47148110006bf64c411007ebc64c4110006df63c4110076dc63c4110006ef62c411006eec62c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c4110007e862c4110007f241c4110007f141c4110007f231c4110007f131c4110006bf6484110066bc6484110006df638411005edc6384110006ef6284110056ec6284110005f77484110005f57484110007b76484110007b46484110005f77384110005f57384110007d76384110007d46384110007e76284110007e46284110007f36084110036be64d9010034fd74d9010014fe73d9010004fd73d9010014fc73d901000cfe72d9010004fd72d901000cfc72d901007cfe71d9010006f671d9010064fe70d9010006fa70d9010004bd7699010006be6399010006bc6399010006be6299010006bc629901001cff7659010036bc6459010006bf7459010004ff7359010014fe7359010014fc7359010036bf4359010006be4359010036bc4359010004ff725901000cfe725901000cfc725
  | 3 => 0xc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc735891003cff7258910006ef7258910054ff7158910006f7715891006cff7058910006fb7058910005ee761891003eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910004ff7654910004fe7654910004fd7654910004fc7654910006bf6454910196bc6454910006df635491018edc6354910006ef625491000eec625491003f6c5254910005f77154910005f47154910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101867c6550910006bf645091001ebc6450910006df635091017edc6350910006ef625091000eec6250910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101767c654c910006bf644c91016ebc644c910006df634c910016dc634c910006ef624c91000eec624c910064fe7690510006bf649051001ebc6490510006df6390510166dc6390510006ef629051015eec6290510005f67690510066f6769051004df57490510007b7649051001ef6649051001ef4649051004fb4649051001eb46490510005f57390510007d76390510007d4639051004fb74390510007b54390510007e76290510007e46290510005f6709051004fb4409051001cfc7650510006bf645051001ebc6450510006df6350510156dc6350510005ef725051003dec7250510006ef625051014eec625051004fb44150510005fb7050510005f8705051004df4765051001ef4765051001cf4765051004df77450510007b77450510007b7645051001ef6645051001ef4645051004fb4645051001eb46450510005f77350510007d76350510007d463505101b7b6435051004fb44350510007e77250510007e47250510007e76250510007e46250510007f37050510005f47050510007f0705051004fb7405051005cfe768c51004dbe748c510005bd748c510006bf648c510146bc648c510006df638c510016dc638c510006ef628c51013eec628c510005f6768c51005ef6768c510005f7748c510007b6748c510005f5748c510007b5748c510005b5748c510007b7648c510007b4648c510045f5738c510007d7638c510016f6638c510016f4638c510047d4638c510016d4638c510007e7628c510007e4628c510005f6708c510047d4308c510014fc764c510006bf644c510136bc644c510006df634c510016dc634c510006ef624c510
  | 4 => 0x8d10005bf7458d1004dbc7458d10006bf6458d10006bc6458d10046dc6358d10005ef7258d1003dec7258d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10044ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1005cff7158d10006f77158d10074ff7058d10006fb7058d10005de7618d10046de7618d10004de7618d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d10047d57118d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10006bf6450d1001ebc6450d10006df6350d10016dc6350d1019eec6250d1000cfe76d8910006bf64d8910006bc64d8910006df63d8910006dc63d891003eee62d891009cfe75d8910004fd75d891009cfc75d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d8910006ef52d891003eee52d891003eec52d8910006ef42d891003eee42d891003eec42d8910006ef32d891003eee32d891003eec32d891000cfe71d891003cfd71d891000cfc71d891003eef21d891000cfe70d891003cfd70d891000cfc70d891003eef20d891003dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ec65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891003eee71d8910006ed71d8910006ef51d8910006ec51d8910006ef41d8910006ec41d8910006ef31d8910006ec31d8910006ef70d891003eee70d8910006ed70d8910006ef50d8910006ec50d8910006ef40d8910006ec40d8910006ef30d8910006ec30d89100057f75589101ad7c75589100067f6558910005bf745891004dbc7458910006bf6458910006bc6458910005df7358910045dc7358910006df6358910006dc635891003eec6258910004ff75589100067f75589100047f755891009cfe755891009cfc75589100067c755891009c7c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cb
  | 5 => 0x5bf744c210065bc744c21000cfd768821000eee6288210006ed6288210005f67188210005f57188210024ff76482100057f75482101bd7c7548210005f576c4210006f576c4210006f764c4210006f564c4210006f763c4210006f563c4210005f976c4210006f976c421001cfe76d911004ebe64d9110014fe73d9110004fd73d9110014fc73d911004ebf43d9110006be43d911004ebc43d911000cfe72d9110004fd72d911000cfc72d911004ebf42d9110006be42d911004ebc42d911001cfe71d911004cfd71d911001cfc71d911004ebf41d911001cfe70d911004cfd70d911001cfc70d911004ebf40d911004dbe76d911001cbe76d9110006be63d9110006bc63d9110006be62d9110006bc62d9110007b771d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110006bf71d911004ebe71d9110006bd71d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d911004ebe70d9110006bd70d9110006bf30d9110006bc30d9110006bf20d9110006bc20d911004ebc6459110005df7359110045dc7359110005ef725911003dec725911004cff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec7259110064ff7159110006f7715911007cff7059110006fb7059110005be761911004ebe7619110004be7619110006be6319110006bc6319110006be6219110006bc621911004fb57119110014fe76d8d10006bf64d8d10006bc64d8d10046de63d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10046de43d8d10046dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10046df32d8d10006de32d8d10046dc32d8d10014fe71d8d10044fd71d8d10014fc71d8d10046df31d8d10014fe70d8d10044fd70d8d10014fc70d8d10046df30d8d10045de76d8d10014de76d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10007d771d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006de52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d10006df71d8d10046de71d8d10006dd71d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d10046de70d8d10006dd70d8d10006df40d8d10006dc40d8d10006df20d8d10006dc20d
  | 6 => 0x7714c310005f4714c31003cfd7688310006ef628831000eec628831000cff76483100057f75483101c57c754831000eee6248310006ed6248310005f77148310005f47148310066be64d9210055ee72d9210005ed72d9210014fe73d9210004fd73d9210014fc73d9210006be43d9210066bc43d921000cfe72d9210006ee72d921000cee72d9210004fd72d9210006ed72d9210004ed72d921000cfc72d9210006f571d9210066bc41d9210006fa70d9210066bf40d9210066bc6459210006bf7459210004ff7359210014fe7359210014fc7359210066bf4359210004ff725921000cfe725921000cfc7259210066bf4159210066bc405921005ede63d8e1001cfe74d8e10004fd74d8e1001cfc74d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006f571d8e1005edc31d8e10006fa70d8e10005bf7458e10065bc7458e1005edc6358e10004ff7458e10006bf7458e10004bf7458e1001cfe7458e1001cfc7458e10006bc7458e1001cbc7458e10006df7358e10004ff7258e1000cfe7258e1000cfc7258e1005edf3158e1005edc3058e10004ff7650e10004fe7650e10004fd7650e10004fc7650e1001ebe6450e10006bd6450e10056ee62d8a1009cfe75d8a10004fd75d8a1009cfc75d8a1001cfe74d8a10004fd74d8a1001cfc74d8a10014fe73d8a10004fd73d8a10014fc73d8a10006f571d8a10056ec21d8a10006fa70d8a10056ec6258a10004ff7558a1009cfe7558a1009cfc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a10006ef7258a10056ee5258a10006ef4258a10056ec4258a10056ee3258a10056ef2158a10056ec2058a10004ff7654a10004fe7654a10004fd7654a10004fc7654a1000eee6254a10006ed6254a100576c5254a10004ff7650a10004fe7650a10004fd7650a10004fc7650a10005f77150a10005f47150a10004ff764ca10004fe764ca10004fd764ca10004fc764ca1000eee624ca10006ed624ca10005f7714ca10005f4714ca1004cfd7690610006bf649061001ebc649061001cff765061001ebe6450610006bd6450610005ef7250610055ec7250610067b44150610005fb7050610005f87050610044fd768c610065be748c610005bd748c610006df638c610016dc638c610014ff764c610016de634c610006dd634c61005fd4314c610005fb704c610005f8704c61003cfd7688610006ef628861000eec628861000cff764861000eee6248610006ed6248610005fb7048610005f8704861001cfd769021001ebe6490210006bd6490210005f67190210005f57190210034ff7650210006bf645021001ebc6450210005df735021005ddc7350210014fd768c210016de638c210006dd638c210005f6718c210005f5718c21002cff764c210
  | 7 => 0x8f10006df7358f10006df4358f10076dc4358f10004ff7258f1000cfe7258f1000cfc7258f10076dc3158f10076df3058f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006bf6450f1001ebc6450f10005fb7050f10005f87050f101c57e75d8b100057d75d8b1006eee62d8b1009cfe75d8b100067e75d8b1009c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1009cfc75d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10014fe73d8b10004fd73d8b10014fc73d8b1006eee52d8b1006eee32d8b10006f671d8b10006f970d8b1006eec20d8b1006eec6258b10004ff7558b1009cfe7558b1009cfc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10014fc7358b10006ef7258b10006ef5258b1006eec5258b1006eec2158b1006eef2058b10004ff7654b10004fe7654b10004fd7654b10004fc7654b10006ef6254b1000eec6254b1006f6c5254b10005f77154b10005f47154b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006ef624cb1000eec624cb1001cfd769071001ebe6490710006bd6490710005fa7090710005f9709071007df5769071001ef5769071001cf5769071001ef6649071007fb66490710007b5649071001ef46490710005f5739071007fb74390710007b54390710005f67090710007f27090710007f1709071007fb44090710034ff7650710006bf645071001ebc6450710005ef725071006dec725071007fb44150710005f77650710036f77650710007b77450710007b7645071001ef6645071001ef4645071007fb4645071001eb46450710005f773507101cfb6435071007fb44350710007e77250710007e47250710005f4705071007fb74050710014fd768c71007dbe748c710005bd748c710016de638c710006dd638c710005fa708c710005f9708c710075f5768c710016f5768c710014f5768c710005f7748c710007b6748c710005f5748c710007b5748c710005b5748c710016f6638c710077d6638c710007d5638c710016f4638c710005f6708c710007f2708c710007f1708c710077d4308c71002cff764c710005f7764c71002ef7764c710005f7744c710005f5744c710007d7734c710016f6634c710016f4634c710005f4704c71000cfd768871000eee6288710006ed6288710005fa7088710005f97088710024ff764871004cfd7690310006bf649031001ebc6490310007b6419031001cff765031001ebe6450310006bd6450310005df7350310075dc7350310005f77150310005f47150310007b54150310044fd768c310006df638c310016dc638c310007d6318c310014ff764c310005bf744c31007dbc744c310016de634c310006dd634c310005f
  | 8 => 0x9cfe7518520004fd751852009cfc751852001cfe7418520004fd741852001cfc7418520014fe7318520004fd7318520014fc7318520026ee5218520006ed5218520026ee3218520006ed3218520006f74118520006f44118520006f73118520006f43118520026f62118520026f52118520026ec2018520004fe7694520004fd7694520004fc76945200067f659452009e7c65945200076d5294520004ff7654520004fe7654520004fc76545200067f655452009e7c6554520004fe7690520004fd7690520004fc76905200067f65905202367c6590520006bf649052001ebc6490520004ff7650520004fe7650520004fc76505200057f75505200957c75505200067f655052022e7c6550520005ef725052000dec725052008fb44150520004fe768c520004fd768c520004fc768c5200067f658c5202267c658c52008dbe748c520005bd748c520006df638c520016dc638c520004ff764c520004fe764c520004fc764c5200067f654c52021e7c654c520214fe769412020e7f659412009e7c659412000dec729412020f6e52941200977b509412020fe8209412000cfe7654120204fd765412000cfc7654120005ef725412000dec72541200076d5254120207e820541201fcfe76901200067f65901201f67c659012001cff765012000cfe76501200dcfd765012000cfc76501200067f65501201ee7c6550120006bf645012001ebc6450120005df7350120085dc7350120005ef725012000dec72501201e4fe768c1200067f658c1201de7c658c12000dec728c120014ff764c12000cfe764c1200bcfd764c12000cfc764c1200067f654c1201d67c654c120005bf744c12008dbc744c120006df634c120016dc634c120005ef724c12000dec724c120005ef7588120005ed75881200076f65881200b6ee65881200b6ec65881200076c65881200b66c6588120005ef7388120005ed7388120006ec618812000dee708812000fea708812000eef608812000feb608812007ebe64d9310075de73d9310005dd73d9310014fe73d9310006de73d9310014de73d9310004fd73d9310006dd73d9310004dd73d9310014fc73d931007ebf43d931000cfe72d9310004fd72d931000cfc72d9310006f671d931007ebf41d9310006f970d931007ebc40d931007ebc6459310006bf7459310004ff7359310014fe7359310014fc7359310006be435931007ebc4359310004ff725931000cfe725931000cfc725931007ebc415931007ebf405931007dbe74d8f10005bd74d8f10076de63d8f1001cfe74d8f10006be74d8f1001cbe74d8f10004fd74d8f10006bd74d8f10004bd74d8f1001cfc74d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f10006f970d8f10076dc30d8f10076dc6358f10004ff7458f1001cfe7458f1001cfc745
  | 9 => 0xe7359120014fc7359120006dc7359120014dc73591200dcff7259120006ef72591200deee3259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f47159120254ff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200067f655512009e7c6555120014fe76d8d200067f65d8d200067c65d8d20086de63d8d2009cfe75d8d20004fd75d8d2009cfc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df43d8d20086dc43d8d200ccff72d8d2000cfe72d8d200ccfd72d8d2000cfc72d8d200cedf32d8d200cedd32d8d20004fe71d8d20004fd71d8d20086dc31d8d2000cfd70d8d20086df30d8d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d2008dbc7458d20086dc6358d20005f77158d20005f47158d2024dfb7058d20004ff7558d200067f7558d200047f7558d2009cfe7558d2009cfc7558d200067c7558d2009c7c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d2001cfc7458d20006bc7458d2001cbc7458d200ccff7358d20006df7358d200bcff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d2024cff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d2009e7c6554d2000dee7254d202476e5254d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2023e7c6550d20095ec765492009eec765492009cec765492000def755492000f6f75549200076f655492009eee655492009eec65549200976c655492009e6c6554920005ef73549200976c5154920007eb7054920005ec7054920007e8705492000eef605492000feb60549200976f5054920085ec764c920016ec764c920014ec764c920005ef754c920005ed754c9200076f654c920176ee654c920176ec654c9200076c654c9201766c654c920006ef644c920006ed644c92000def734c92000fcf734c920007cf634c920016ee634c920016ec634c920087cc634c920007eb704c920005ec704c920007e8704c920005e8704c92000eef604c92000feb604c9200067f65d85200067c65d852009cfe75d8520004fd75d852009cfc75d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d8520006f741d8520006f441d8520006f731d8520006f431d8520056f621d8520056f521d85200957e75985200057d75985200067f65985200067c6598520006f7619852003df970985200057f75585200957c75585200067f65585200067c6558520005bf745852008dbc7458520005df7358520085dc735852006dfb70585200067f65185200067c6518520006f56118520
  | 10 => 0x220005df73502200a5dc735022000cff768c220014fe768c22000cfd768c220016de638c220006dd638c22000dee728c220005ed728c22024cff764c220005bf744c2200adbc744c22009cfe76d95200967e65d952001cfe74d9520004fd74d952001cfc74d95200967f54d95200067e54d95200967c54d9520014fe73d9520004fd73d9520014fc73d95200967f53d95200067e53d95200967c53d952020cff72d952000cfe72d952020cfd72d952000cfc72d952020e7f52d952020e7d52d9520004fe71d9520004fd71d95200967f51d95200967c51d952000cfd70d95200967f50d95202157e76d952009c7e76d95200067e64d95200067c64d95200067e63d95200067c63d95200076f72d952020f6c72d952020f6e32d952020f7b20d952020f6c20d952020f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d952020e7f72d952020e7e72d952020e7d72d952020e7c72d952020e7f42d952020e7e42d952020e7d42d952020e7c42d952020e7f32d952020e7e32d952020e7d32d952020e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067c31d952020e7f21d952020e7e21d952020e7d21d952020e7c21d952020e7f70d95200967e70d952020e7d70d95200067f40d95200067c40d95200067f30d95200067c30d952020e7f20d952020e7e20d952020e7c20d95200967c655952025dfb7059520004ff745952001cfe745952001cfc7459520004ff7359520014fe7359520014fc7359520204ff7259520006ef7259520004ff7159520004fc715952025cff7059520006fb705952020d7e76195200967e761952020c7e76195200067e64195200067c64195200067e63195200067c63195202176e72195200976d72195202167f62195202176e32195202167f60195202177b20195202176c201952021778201952001cfe76d91200067f65d91200067c65d912008ebe64d912009cfe75d9120004fd75d912009cfc75d9120014fe73d9120004fd73d9120014fc73d9120006be43d912008ebc43d91200ecff72d912000cfe72d91200ecfd72d912000cfc72d91200eebf42d91200eebd42d91200eeee32d9120004fe71d9120004fd71d912008ebc41d912000cfd70d912008ebf40d91200057f75591200957c75591200067f65591200067c655912008ebc6459120005df7359120085dc7359120005f77159120005f47159120255fb7059120004ff75591200067f75591200047f755912009cfe755912009cfc75591200067c755912009c7c75591200ecff7459120006bf7459120004ff7359120006df7359120004df7359120014f
  | 11 => 0x4fe7655220004fd7655220004fc7655220005ef725522000dec72552200a6de63d8e201e5fa70d8e2009cfe75d8e20004fd75d8e2009cfc75d8e2001cfe74d8e20004fd74d8e2001cfc74d8e200bcfd73d8e20006ed72d8e20006ef52d8e200ceec52d8e20004fe71d8e20004fd71d8e200ceec21d8e201e4fe70d8e20006fa70d8e200ceef20d8e20014ff7658e200a6dc6358e20004ff7558e2009cfe7558e2009cfc7558e20004ff7458e2001cfe7458e2001cfc7458e20006df7358e20006ef5258e200beec5258e200bedf3258e200bedd3258e20004ff7158e20004fc7158e200beec2158e2000cfc7058e200a6dc3058e200beef2058e20004ff7654e20004fe7654e20004fd7654e20004fc7654e2009e7e6554e200067d6554e20005ef7254e2000dec7254e202476c5254e20004ff7650e20004fe7650e20004fd7650e20004fc7650e2001ebe6450e20006bd6450e20025fa70d8620006f7619862009cfe7598620004fd759862009cfc759862001cfe7498620004fd749862001cfc7498620014fe7398620004fd7398620014fc7398620006f75198620006f4519862006ef6219862006ef521986200057f75586200b57c7558620004ff75586200067f75586200047f755862009cfe755862009cfc75586200067c755862009c7c7558620004ff745862001cfe745862001cfc7458620004ff7358620014fe7358620014fc7358620006f75158620006f4515862003ef6215862003ef5215862003eec21586200adbe7418620005bd7418620006f56118620055fa7018620004ff7694620004fe7694620004fd769462009e7c659462000dee7294620005ed72946200b76f5294620004ff7654620004fd7654620004fc7654620005ef725462000dec7254620004ff7690620004fe7690620004fd7690620006f66190620006f56190620004ff7650620004fd7650620004fc76506200057f75506200b57c755062001ebe6450620006bd6450620005ef725062000dec7250620006f66150620006f561506200afb44150620004ff768c620004fe768c620004fd768c6200adbe748c620005bd748c620006f6618c620006f5618c620004ff764c620004fd764c620004fc764c620005ef724c62000dec724c620006f6614c620006f5614c6200b5ee75886200b5ec7588620006ef6588620006ed658862011eee648862011eec6488620006ef6388620006ed638862000dee718862000fe67188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862000eee608862000fea608862009cfe769422000cfd769422000dee7294220005ed729422020f6c529422020feb209422000cff769022001cfe769022000cfd769022001ebe6490220006bd649022000dee7290220005ed7290220254ff765
  | 12 => 0xc64d853001cfe74d8530004fd74d853001cfc74d853000cfe72d8530004fd72d853000cfc72d853005ef631d853005ef531d8530006f721d8530006f421d85300c5be7498530005bd7498530006bf6498530006bc6498530006f76198530045f97098530005bf74585300c5bc7458530006bf6458530006bc6458530005ef72585300bdec7258530075fb7058530006bf6418530006bc6418530006f5611853001cfe7418530004fd741853001cfc741853000cfe7218530004fd721853000cfc721853002ef6311853002ef53118530006f72118530006f4211853002edc3018530004fe7690530004fd7690530004fc7690530006bf649053001ebc6490530004ff7650530004fe7650530004fc7650530006bf645053001ebc6450530005ef72505300bdec72505300c7b44150530004fe7688530004fd7688530004fc7688530006bf648853011ebc6488530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530006bf6448530106bc6448530264fe76901300f6bf649013001ebc649013001cff7650130014fe76501300e4fd7650130014fc7650130006bf645013001ebc6450130005df7350130015dc73501300079f648c1300d6de648c1300d6dc648c1300079c648c1300d69c648c130006dc618c130015de708c130017da708c130016df608c130017db608c1300b67e65d96200adbe74d9620005bd74d962020f6c52d9620005f671d9620005f571d9620215fa70d962001cfe74d9620006be74d962001cbe74d9620004fd74d9620006bd74d9620004bd74d962001cfc74d9620014fe73d9620004fd73d9620014fc73d962020e7e52d962020eec52d962020e6c52d9620004fe71d9620006f671d9620004f671d9620004fd71d9620006f571d9620004f571d962020eec21d9620214fe70d9620006fa70d962020eef20d962009cff76596200b67c655962000dec72596200b76f52596200067f7559620004ff745962001cfe745962001cfc7459620004ff7359620014fe7359620014fc73596200b67f53596202067f52596200b6ef52596200b66f52596202067d5259620206ec5259620004ff7159620004fc7159620206ec215962000cfc70596200b67c5059620206ef20596200aebe64d92201fdfa70d922009cfe75d9220004fd75d922009cfc75d92200dcfd74d9220014fe73d9220004fd73d9220014fc73d9220006ed72d9220004fe71d9220004fd71d92201fcfe70d9220006fa70d922001cff76592200aebc6459220004ff755922009cfe755922009cfc7559220006bf7459220006bf54592200aebc5459220004ff7359220014fe7359220014fc73592200aebf43592200debf42592200debd4259220004ff7159220004fc71592200aebf415922000cfc70592200aebc4059220004ff7655220
  | 13 => 0x630015dc73506301579c4350630005ef72506300cdec7250630006f66150630006f561506300d7b441506300d5de748c6300079e748c6300d59e748c6300079d748c6300d5dc748c630015de718c630017d6718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c630016de608c630017da608c630004ff7688630004fe7688630004fd768863000eec6288630004ff7648630004fd7648630004fc7648630005df7348630015dc7348630014ff769023001cfe7690230014fd769023001ebe6490230006bd6490230015de7390230005dd73902300f79c4390230274ff7650230006bf645023001ebc64502300d5df7350230015dc73502300d79f435023001cfe76d91300c6be64d91300f4ff73d9130014fe73d91300f4fd73d9130014fc73d91300f6bf43d91300f6bd43d913000cfe72d9130004fd72d913000cfc72d91300c6bf42d9130006be42d91300c6bc42d9130004fe71d9130004fd71d91300c6bf41d91300c6bc41d9130014fd70d91300c6bf40d9130265be76d913001cbe76d9130006be62d9130006bc62d91300f7bb30d91300f79c30d91300f7b830d91300f6bf73d91300f6be73d91300f6bd73d91300f6bc73d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006be52d9130006bc52d91300f6bf32d91300f6be32d91300f6bd32d91300f6bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d91300f6bf31d91300f6be31d91300f6bd31d91300f6bc31d9130006bf21d9130006bc21d91300f6bf70d91300c6be70d91300f6bd70d91300f6bf30d91300f6be30d91300f6bc30d9130006bf20d9130006bc20d91300c6bc6459130275fb70591300f4ff7459130006bf74591300e4ff7359130006df73591300d4df7359130004ff725913000cfe725913000cfc7259130004ff7159130004fc7159130274ff7059130006fb70591300f5be76191300c6be76191300f4be7619130266bf6319130006be6219130006bc6219130266bf6019130267bb30191302679c3019130267b8301913000cfe76d8930006bf64d8930006bc64d89300beee62d893009cfe75d8930004fd75d893009cfc75d893001cfe74d8930004fd74d893001cfc74d893000cfc73d8930006ef52d89300beec52d89300beee32d89300a6ed32d8930004fe71d8930004fd71d89300beec21d8930014fd70d89300beef20d89300057f75589301d57c7558930005bf74589300c5bc7458930006bf6458930006bc64589300beec6258930005f77158930005f4715893026dfb7058930004ff7654930004fe7654930004fc7654930006bf6454930196bc64549300bf6c5254930004ff7650930004fe7650930004fc7650930006bf645093001ebc6450930006bf64d8530006b
  | 14 => 0x1fb77150540007b76150540006bc6150540007b46150540006b46150540007bb7050540005bc7050540007b8705054001ebf605054001fbb6050540004fe768c540004fd768c540004fc768c54001dbe748c540005bd748c540006df638c540016dc638c540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c540006df634c540016dc634c540004fe7688540004fd7688540004fc768854001dbe7488540005bd7488540006df6388540116dc6388540006ef628854000eec6288540004ff7648540004fe7648540004fc7648540006df63485400fedc6348540005bd73901400079f63901400f6be63901400f6bc63901400079c63901400f69c6390140005bd7190140006bc619014001dbe709014001fba709014001ebf609014001fbb60901400d6be64d92300f79c43d9230265fa70d92300e4fd74d9230006dd73d92300d6df43d92300f6be43d92300f6bc43d92300f6dc43d923000cfe72d9230004fd72d923000cfc72d9230004fe71d9230004fd71d92300d6bc41d9230264fe70d9230006fa70d92300d6bf40d923001cff76592300d6bc6459230015dc73592300d79f4359230006bf74592300d6df73592300e6bf43592300d6df43592300e6bd43592300e6dc4359230004ff725923000cfe725923000cfc7259230004ff7159230004fc71592300d6bf4159230014fc70592300d6bc40592300ceee62d8a3027dfa70d8a3000cff7658a300057f7558a301dd7c7558a300ceec6258a30004ff7558a300067f7558a300047f7558a3009cfe7558a3009cfc7558a300067c7558a3009c7c7558a30004ff7458a3001cfe7458a3001cfc7458a300ceee5258a300ceee3258a30086ed3258a30004ff7158a30004fc7158a30014fc7058a300ceec2058a30004ff7654a30004fd7654a30004fc7654a3000eee6254a30006ed6254a300cf6c5254a30004ff7650a30004fd7650a30004fc7650a30005df7350a30015dc7350a3002dfa70d8630006f7619863001cfe7498630004fd749863001cfc749863000cfe7298630004fd729863000cfc7298630076f63198630076f53198630005bf74586300d5bc7458630005ef72586300cdec7258630004ff7458630006bf7458630004bf745863001cfe745863001cfc7458630006bc745863001cbc7458630004ff7258630006ef7258630004ef725863000cfe725863000cfc7258630006ec725863000cec7258630046f63158630046f53158630046dc31586300d5be7418630005bd7418630006f5611863005dfa7018630004ff7690630004fe7690630004fd7690630006bf649063001ebc6490630015de7390630005dd73906300d79f4390630006f66190630006f56190630004ff7650630004fd7650630004fc765063001ebe6450630006bd6450630005df735
  | 15 => 0xc31d8d4001cfd70d8d400e6df30d8d400e5de76d8d40014de76d8d400079f74d8d400d79c74d8d40006de62d8d40006dc62d8d400d79f41d8d400d7db40d8d400d79c40d8d400d7d840d8d400d6df74d8d400e6de74d8d400d6dc74d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006de52d8d40006dc52d8d400d6df42d8d400d6de42d8d400d6dd42d8d400d6dc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d400d6df41d8d400d6de41d8d400d6dd41d8d400d6dc41d8d40006df21d8d40006dc21d8d400d6df70d8d400e6de70d8d400d6dd70d8d400d6df40d8d400d6de40d8d400d6dc40d8d40006df20d8d40006dc20d8d400e6dc6358d40295fb7058d400d5de7618d400e6de7618d400e79e7418d400e79d7418d400f6df6418d400e7ce7218d400e7cd7218d40006de6218d40006dc6218d4028f9f4118d40276df6018d4028fdb4018d4028f9c4018d4028fd84018d400e5bc7650d40016bc7650d40014bc7650d4001dbf7350d4001f9f7350d400079f6350d40016be6350d40016bc6350d400e79c6350d400169c6350d40005bf7150d40007bb7050d40005bc7050d40007b87050d4001ebf6050d4001fbb6050d4000cfe76d8940006df63d8940006dc63d89400deee62d894009cfe75d8940004fd75d894009cfc75d894000cfc74d8940014fe73d8940004fd73d8940014fc73d8940006ef52d89400deec52d89400deee42d89400aeed42d8940004fe71d8940004fd71d89400deec21d894001cfd70d89400deef20d89400057f75589401ed7c7558940005df73589400e5dc7358940006df6358940006dc63589400deec6258940005f77158940005f47158940285fb7058940004ff7654940004fe7654940004fc7654940005bf745494001dbc7454940006df635494018edc63549400df6c5254940004ff764c940004fe764c940004fc764c940006df634c940016dc634c94000eee624c940006df63d8540006dc63d8540014fe73d8540004fd73d8540014fc73d854000cfe72d8540004fd72d854000cfc72d8540066f641d8540066f541d8540006f721d8540006f421d85400e5de7398540005dd7398540006df6398540006dc6398540006f7619854004df97098540005df73585400e5dc7358540006df6358540006dc6358540005ef72585400ddec725854007dfb7058540006df6318540006dc6318540006f56118540014fe7318540004fd7318540014fc7318540036bf4318540006bd431854000cfe7218540004fd721854000cfc7218540036bf4118540036f64118540036f54118540006f72118540006f42118540036bc4018540005bf73505400079f6350540156be6350540156bc63505400079c63505401569c6350540007af7250540007ac725054001dbf7150540
  | 16 => 0xc5210ffd4314c521006ef6588521006ed658852111eee648852111eec6488521006ef6388521006ed638852100dee718852100fe6718852100eef618852100fe7618852109cfe75d8121004fd75d812109cfc75d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d812106efa20d8121006fb60981210057f755812110d7c7558121005bf7458121105bc7458121005df73581210fddc7358121006f9601812109cfe7518121004fd751812109cfc751812101cfe7418121004fd741812101cfc7418121014fe7318121004fd7318121014fc7318121006ee2118121026ec2118121026f920181210f6de63d8e400f79c43d8e4028dfa70d8e40014ff7658e4001dbc7458e400f6dc6358e400f79e4358e400f6be4358e400f6de4358e400c6dd4358e400f6bc4358e40004ff7258e4000cfe7258e4000cfc7258e40004ff7158e40004fc7158e400c6bc4158e4001cfc7058e400c6bf4058e400f6dc3058e400eeee62d8a4029dfa70d8a4000cff7658a400eeec6258a40004ff7558a4009cfe7558a4009cfc7558a40004ff7358a40014fe7358a40014fc7358a400eeee5258a400eeee4258a4008eed4258a400eeee3258a40004ff7158a40004fc7158a400eeec2158a4001cfc7058a400eeec2058a40004ff7654a40004fd7654a40004fc7654a4000eee6254a40006ed6254a400ef6c5254a40004ff764ca40004fd764ca40004fc764ca40005bf744ca4001dbc744ca4000eee624ca40006ed624ca400edee72d8640005ed72d8640035fa70d8640006f76198640014fe7398640004fd7398640014fc739864000cfe7298640004fd729864000cfc729864007ef6419864007ef54198640004ff7358640014fe7358640014fc7358640006be435864004ebc4358640004ff725864000cfe725864000cfc725864004ef6415864004ef5415864004ebc415864004ebf4058640006f56118640065fa70186400f5be73906400f5bc7390640006bd639064001dbe719064001fb67190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b9709064001ebe609064001fba6090640004ff768c640004fe768c640004fd768c64001dbe748c640005bd748c640006f6618c640006f5618c640004ff764c640004fd764c640004fc764c640005bf744c64001dbc744c640006f6614c640006f5614c640004ff7688640004fe7688640004fd768864000eee6288640006ed6288640004ff7648640004fd7648640004fc7648640005bf744864001dbc7448640014fe76d8d400e6de63d8d40014fc74d8d400e6de43d8d400d6dd43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400e6df32d8d40006de32d8d400e6dc32d8d40004fe71d8d40004fd71d8d400e6df31d8d400e6d
  | 17 => 0x3efa205822103eec205822111dbe7418221005bd7418221006f9601822109cfe76d952110e7e65d952101cfe74d9521004fd74d952101cfc74d95210067e54d952110e7c54d9521014fe73d9521004fd73d9521014fc73d952110e7f53d95212dcff72d95212dcfd72d95212de7f52d95212de7d52d952100cfd71d952110e7f51d95212deec21d9521004fe70d9521004fd70d952110e7c50d952110e7c6559521005bf7459521105bc74595212d5f77159521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff7359521014fe7359521014fc73595212b4ff7259521006ef72595212d4ff7159521006f771595212b6ec2159521004ff7059521004fc705952101cfe76d9121106be64d912109cfe75d9121004fd75d912109cfc75d9121006bf54d9121106bc54d9121014fe73d9121004fd73d9121014fc73d9121106bf43d912115cff72d912115cfd72d912115ebf42d912115ebd42d912100cfd71d9121106bf41d9121004fe70d9121004fd70d9121106bc40d91210057f755912110d7c7559121106bc64591212cdf77159121004ff75591210067f75591210047f755912109cfe755912109cfc75591210067c755912109c7c755912115cff7459121006bf7459121004ff7359121014fe7359121014fc735912114cff7259121006ef725912111cef72591212ccff7159121006f77159121004ff7059121004fc7059121004ff7655121004fe7655121004fd7655121004fc7655121014fe76d8d210fede63d8d2109cfe75d8d21004fd75d8d2109cfc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2113cff72d8d2113cfd72d8d2113edf32d8d2113edd32d8d2100cfd71d8d210fedf31d8d2113eec21d8d21004fe70d8d21004fd70d8d210fedc30d8d210fedc6358d212c5f77158d21004ff7558d2109cfe7558d2109cfc7558d21004ff7458d2101cfe7458d2101cfc7458d2113cff7358d21006df7358d2112cff7258d21006ef7258d212c4ff7158d21006f77158d2112eec2158d21004ff7058d21004fc7058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2109e7c6554d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc6450d212bcfe769452109e7e659452100cfe76545212b4fd765452100cfc7654521005ef725452100dec72545212acfe769052101cff765052100cfe765052114cfd765052100cfc76505210057f755052110d7c7550521006bf645052101ebc6450521005ef725052100dec7250521107b441505212a4fe768c521105be748c521005bd748c521014ff764c52100cfe764c52112cfd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724
  | 18 => 0xe7359221014fc7359221006be435922111ebc435922111eef725922114ebf425922111eef425922114ebd425922114eec425922114eee325922100cfc715922111ebc4159221004ff7059221004fc705922111ebf4059221004ff7655221004fe7655221004fd7655221004fc7655221005ef725522100dec725522111dbe74d8e21005bd74d8e21116de63d8e212a5f671d8e2109cfe75d8e21004fd75d8e2109cfc75d8e2101cfe74d8e21006be74d8e2101cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e2101cfc74d8e2112cfd73d8e21006ed72d8e212a4fe71d8e21006f671d8e21004fe70d8e21004fd70d8e21014ff7658e21116dc6358e21004ff7558e2109cfe7558e2109cfc7558e21004ff7458e2101cfe7458e2101cfc7458e21006df7358e2112edf3258e2112edd3258e2100cfc7158e21116dc3158e21004ff7058e21004fc7058e21004ff7654e21004fe7654e21004fd7654e21004fc7654e2109e7e6554e210067d6554e2100dee7254e212476e5254e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21005ef7250e2100dec7250e21125ef7654a2109eef7654a2109cef7654a2100def7554a2100f6f7554a2109eee6554a211276e6554a2109e6e6554a210076d6554a2109eec6554a2111dee7454a2111dec7454a21005ef7354a21005ef7154a21007e77154a21007e47154a2100eee6154a2100fe66154a211276c5154a21005ec7054a211276f5054a21115ef764ca21016ef764ca21014ef764ca21005ef754ca21005ed754ca21176ee654ca21176ec654ca2111dee744ca2111dec744ca21006ef644ca21006ed644ca2100def734ca2100fcf734ca21016ee634ca21117ce634ca21007cd634ca21016ec634ca21005ef714ca21007e7714ca21007e4714ca2100eee614ca2100fe6614ca21005ec704ca2109cfe769462100cfd769462100dee7294621005ed72946210076d52946212dfe7219462100cff769062101cfe769062100cfd769062101ebe6490621006bd649062100dee7290621005ed72906212ccff76506210057f75506211257c755062111def725062100dec725062111fb4415062100cff768c621014fe768c62100cfd768c62111dbe748c621005bd748c621016de638c621006dd638c62100dee728c621005ed728c6212c4ff764c62100dee724c621117d4314c6211257e75d82210057d75d8221006fb609822109cfe7598221004fd759822109cfc759822101cfe7498221004fd749822101cfc7498221014fe7398221004fd7398221014fc7398221056f92098221004ff755822109cfe755822109cfc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221014fc735822103eee5258221006ed525822103eee3258221006ed3258221
  | 19 => 0x9131004fd70d9131136bc40d9131136bc6459131005ef725913112dec72591312f5f77159131005fb7059131005f87059131164ff7459131006bf7459131154ff7359131006df7359131156be4359131156bc4359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec72591312f4ff7159131006f77159131136bc4159131004ff7059131006fb7059131004fb7059131004fc7059131006f87059131004f87059131136bf405913100cfe76d893112eee62d893109cfe75d8931004fd75d893109cfc75d893101cfe74d8931004fd74d893101cfc74d893112eee52d8931006ef42d893112eec42d893112eee32d8931116ed32d8931014fd71d893112eef21d8931004fe70d8931004fd70d893112eec20d893112eec62589312edf77158931004ff7654931004fe7654931004fc7654931006ef625493100eec625493112f6c5254931004ff7650931004fe7650931004fc7650931005f77150931005f471509312e4fe769053101ebe6490531006bd649053101cff7650531014fe7650531154fd7650531014fc7650531006bf645053101ebc6450531005df7350531015dc7350531005ef725053112dec7250531137b441505310079e748c5310079d748c531015de718c531017d6718c531016df618c531017d7618c53101cfe74d8131004fd74d813101cfc74d813100cfe72d8131004fd72d813100cfc72d8131006fb40d8131006f840d8131076fa30d8131006fb6098131005bf7458131135bc7458131005ef725813112dec7258131135be7418131005bd7418131006f9601813101cfe7418131006be741813101cbe7418131004fd7418131006bd7418131004bd741813101cfc741813100cfe7218131004fd721813100cfc721813102ef57118131006de311813102edc3118131006fb4018131006f8401813102ef930181311267e65d96212bdf671d962101cfe74d9621004fd74d962101cfc74d9621014fe73d9621004fd73d9621014fc73d96212bcfe71d9621006f671d9621004fe70d9621004fd70d962109cff76596211267c65596210067f7559621004ff745962101cfe745962101cfc7459621004ff7359621014fe7359621014fc73596211267f53596212b67f52596212b67d525962100cfc71596211267c5159621004ff7059621004fc70596211267c505962111ebe64d92212adf671d922109cfe75d9221004fd75d922109cfc75d922114cfd74d9221014fe73d9221004fd73d9221014fc73d9221006ed72d922111eef42d922115eec42d922115eee32d92212acfe71d9221006f671d9221004fe70d9221004fd70d922101cff765922111ebc645922100dec725922111faf4259221004ff755922109cfe755922109cfc7559221006bf7459221004ff7359221014f
  | 20 => 0x6fb3018141006f83018141146be64d92312e5f671d9231154fd74d9231006dd73d923100cfe72d9231004fd72d923100cfc72d92312e4fe71d9231006f671d9231004fe70d9231004fd70d9231154bd76992312f6bd6399231006be6299231006bc62992312f6be61992312f79f31992312f7b731992312f7b431992312f79c309923101cff7659231146bc6459231006bf7459231156bf4359231156bd4359231004ff725923100cfe725923100cfc7259231146bf4259231006be4259231146bc4259231014fc7159231146bc4159231004ff7059231004fc7059231146bf4059231146bc40592312f5bf7659231146bf765923101cbf7659231006be6259231006bc62592311579f3159231157b73159231157b431592311579c3059231156bf7359231156be7359231156bd7359231156bc7359231006bf7259231006be7259231006bd7259231006bc7259231006be5259231006bc5259231156bf3259231156be3259231156bd3259231156bc3259231146bf7159231156be7159231156bc7159231156bf3159231156be3159231156bd3159231156bc3159231006bf2159231006bc2159231006bf7059231006be7059231006bd7059231006bc7059231156bf3059231156be3059231156bd3059231156bc3059231006bf2059231006bc2059231145be74d8a31005bd74d8a31006be64d8a31006bd64d8a3113eee62d8a312fdf671d8a3100cff7658a31006be6458a31006bd6458a3113eec6258a31004ff7558a3109cfe7558a3109cfc7558a31004ff7458a3101cfe7458a3101cfc7458a3113eee3258a310feed3258a31014fc7158a3113eec2158a31004ff7058a31004fc7058a31004ff7654a31004fd7654a31004fc7654a31196be6454a31006bd6454a3113f6c5254a31004ff7650a31004fd7650a31004fc7650a3101ebe6450a31006bd6450a31005f77150a31005f47150a31014ff769063101cfe7690631014fd769063101ebe6490631006bd6490631015de7390631005dd73906312f4ff765063101ebe6450631156bd6450631005ef725063113dec7250631147b44150631145be74d8231005bd74d8231006be64d8231006bd64d8231006be6498231006bd6498231006fb609823101cfe7498231004fd749823101cfc749823100cfe7298231004fd729823100cfc729823105ef6719823105ef93098231006be6458231006bd6458231004ff745823101cfe745823101cfc7458231004ff725823100cfe725823100cfc7258231046fa3058231046dc3058231145be7418231005bd7418231006be6418231006bd6418231006f9601823101cfe76d9131136be64d9131164ff73d9131164fd73d9131166bf43d9131166bd43d913100cfe72d9131004fd72d913100cfc72d9131014fd71d9131136bf41d9131004fe70d
  | 21 => 0xe32d894114eec32d894101cfd71d894114eef21d8941004fe70d8941004fd70d894114eef20d894114eec20d894114dee76d894100cee76d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ec65d8941006ef63d8941006ee63d8941006ed63d8941006ec63d8941007ae43d894111fac43d894111fe741d894111fac41d894111fe441d894111fa441d894111faf40d8941006ef75d8941006ee75d8941006ed75d8941006ec75d894111eef74d894114eee74d894111eec74d894111eef54d894111eee54d894111eed54d894111eec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ec53d894111eef43d894111eee43d894111eed43d894111eec43d894111eef71d894114eee71d894111eed71d8941006ef51d8941006ec51d894111eef41d894111eee41d894111eec41d8941006ef31d8941006ec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef50d8941006ec50d894111eef40d894111eee40d894111eed40d894111eec40d8941006ef30d8941006ec30d89410057f755894122d7c75589410067f655894114eec625894130df77158941107b4415894111dee761894114eee7618941006ef65189410076f65189410066f6518941006ee6518941006ed6518941006ec65189410076c65189410066c651894115eef6418941006ef6318941006ee6318941006ed6318941006ec6318941007ae4318941307ac43189412ceef6118941307e74118941307ac4118941307e44118941307a44118941307af4018941004ff7654941004fe7654941004fc7654941006ef625494100eec625494114f6c5254941197b44154941004ff764c941004fe764c941004fc764c9410067f654c9411767c654c941005bf744c94101dbc744c941006ef624c94100eec624c941005f7714c941005f4714c94116fb4414c941155be7390541155bc7390541006bf6390541007af6290541007ac629054101dbe719054101fb6719054101db6719054101ebf619054101fb76190541005bd7090541006ef62d8141006ec62d814107fb441d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d814107efa40d8141006fb30d8141006f830d814114dee7298141005ed7298141006ef6298141006ec6298141067b44198141006fb6098141005df7358141155dc7358141005ef725814114dec7258141006ef6258141006ec625814104fb44158141006ef6218141006ec6218141037b44118141006f96018141014fe7318141004fd7318141014fc7318141006be4318141036bc431814100cfe7218141004fd721814100cfc7218141036f57118141006be4118141036bc4118141036bf4018141036f94018141
  | 22 => 0x8132004fd75d813209cfc75d813201cfe74d8132004fd74d813201cfc74d813200cfd73d8132014fd72d8132004fe71d8132004fd71d8132006fb50d8132006f850d813226efa30d813224efa20d8132006fb60981320057f75581321757c7558132005bf745813216dbc7458132005f77158132005f471581321757e75181320057d7518132006f9601813209cfe75181320067e751813209c7e7518132004fd75181320067d75181320047d751813209cfc751813201cfe7418132004fd741813201cfc741813200cfd7318132014fd721813227eed7218132006ef52181321e6ec5218132004fe7118132004fd71181321e6ec2118132006fb5018132006f8501813227ef930181321e6ef20181321e6f92018132166de63d8e4131df671d8e41014ff7658e41166dc6358e41166de4358e41136dd4358e41004ff7258e4100cfe7258e4100cfc7258e41166df3258e4101cfc7158e41166dc3158e41004ff7058e41004fc7058e41166dc3058e41165bf7650e41016bf7650e41014bf7650e4101dbf7350e4101f9f7350e41016be6350e411679e6350e410079d6350e41016bc6350e41005bf7150e41007b77150e41007b47150e4101ebe6150e4101fb66150e41005bc7050e4115eee62d8a41305f671d8a4100cff7658a4115eec6258a41004ff7558a4109cfe7558a4109cfc7558a41004ff7358a41014fe7358a41014fc7358a4115eee4258a41106ed4258a4101cfc7158a4115eec2158a41004ff7058a41004fc7058a41004ff7654a41004fd7654a41004fc7654a41005bf7454a4101dbc7454a4115f6c5254a41004ff764ca41004fd764ca41004fc764ca41016de634ca41006dd634ca4100eec624ca41005f7714ca41005f4714ca41165de73d8241005dd73d8241006fb6098241014fe7398241004fd7398241014fc739824100cfe7298241004fd729824100cfc7298241066f67198241066f94098241004ff7358241014fe7358241014fc735824104ebf4358241006bd4358241004ff725824100cfe725824100cfc725824104ebf415824104efa405824104ebc4058241006f96018241014fe76d8d4101dbe74d8d41156de63d8d411579e43d8d41147b441d8d41156be43d8d41156de43d8d41146dd43d8d41156bc43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d4101cfd71d8d41146bc41d8d41156df31d8d41004fe70d8d41004fd70d8d41146bf40d8d41156dc30d8d41156dc6358d41005ef7258d4114dec7258d41315f77158d41137b44158d41005fb7058d41005f87058d4100cfe76d894114eee62d894111fb441d894109cfe75d8941004fd75d894109cfc75d8941014fe73d8941004fd73d8941014fc73d8941006ef52d894114eee52d894114eec52d894114eee42d894111eed42d8941006ef32d894114ee
  | 23 => 0x1fef9201814209cfe76d95321767e65d953200dee72d9532015ed72d95321776f52d9532244fd75d953201cfe74d9532004fd74d953201cfc74d953200cfd73d953235e7f53d9532014ff72d9532014fd72d953235eed72d9532014ed72d95323567f52d9532176ef52d95323567d52d9532356ec52d9532004fe71d9532004fd71d9532356ec21d9532004fe70d9532004fd70d95321767c50d9532356ef20d953209cff76595321767c6559532005bf745953216dbc7459532345df735953234def72595322476c5259532005f77159532005f47159532005fb7059532005f87059532004ff7459532006bf7459532004bf745953201cfe745953201cfc7459532006bc745953201cbc7459532344ff7359532006df7359532244ff7259532006ef72595322467e5259532246ec52595322466c5259532004ff7159532006f77159532004f77159532004fc7159532006f47159532004f47159532246ec2159532004ff7059532006fb7059532004fb7059532004fc7059532006f87059532004f87059532246ef205953201cfe76d913216ebe64d913209cfe75d9132004fd75d913209cfc75d913219cfd74d9132006bf54d913216ebc54d913200cff73d913200cfd73d913233ebf43d913233ebd43d9132014ff72d9132014fd72d913232ebf42d913232ebd42d9132004fe71d9132004fd71d913216ebf41d9132004fe70d9132004fd70d913216ebc40d913201cff765913216ebc6459132325df7359132335ef7259132004ff755913209cfe755913209cfc755913232cff7459132006bf7459132324ff7359132006df735913219cff7259132006ef7259132004ff7159132004fc7159132004ff7059132004fc7059132004ff7655132004fe7655132004fd7655132004fc7655132005ef725513200dec7255132015ec765093201eec7650932014ec7650932175ee7550932175ec755093200def745093200faf7450932007af645093201eee645093201eec645093216fac6450932007cf7350932015ee7350932015ec735093217fcc735093200eef635093200fcf6350932005ec7150932005ef70509321757e75d85320057d75d853209cfe75d85320067e75d853209c7e75d8532004fd75d85320067d75d85320047d75d853209cfc75d853201cfe74d8532004fd74d853201cfc74d853200cfd73d8532014fd72d85322eeed72d8532006f751d8532006f451d85322eef631d85322c6f621d85322c6ec21d8532004fe70d8532004fd70d853216dbe7498532005bd7498532006f76198532006f5611853209cfe7518532004fd751853209cfc751853201cfe7418532004fd741853201cfc741853200cfd7318532014fd7218532006f75118532006f451185322fef531185322a6f52118532004fe7018532004fd701853209cfe75d
  | 24 => 0x74118552006f44118552006f73118552006f431185522bef52118552004fe7018552004fd701855225f6c52d815201cfe74d8152004fd74d815201cfc74d8152014fe73d8152004fd73d8152014fc73d815209cfd72d8152004fe71d8152004fd71d8152006fb30d8152006f830d815225efa20d8152195be7498152005bd749815220f6c5298152005f67198152005f57198152006fb60981522076c52581522176c5218152006f9601815201cfe7418152004fd741815201cfc7418152014fe7318152004fd7318152014fc731815209cfd721815239eed72181522167e5218152216ec52181522166c5218152004fe7118152004fd7118152216ec2118152006fb3018152006f83018152216ef2018152216f9201815209cfe76d95421867e65d9542374fd75d954200cfd74d95423967f54d9542014fe73d9542004fd73d9542014fc73d95421867f53d954201cff72d954201cfd72d954238e7f52d954238e7d52d9542004fe71d9542004fd71d95421867c51d9542004fe70d9542004fd70d95421867c50d954209cff76595421867c655954237dbf7459542385ef7259542005f77159542005f4715954237cff7459542006bf7459542004ff7359542014fe7359542014fc7359542374ff7259542006ef7259542004ff7159542006f77159542004f77159542004fc7159542006f47159542004f47159542004ff7059542004fc7059542014fe76d8d4217ede63d8d4209cfe75d8d42004fd75d8d4209cfc75d8d4200cfd74d8d4217ede43d8d4236edd43d8d4201cfd72d8d42326df32d8d42004fe71d8d42004fd71d8d42004fe70d8d42004fd70d8d4217edc30d8d4217edc6358d42365ef7258d4209cfe75d8542004fd75d854209cfc75d854200cfd74d8542014fe73d8542004fd73d8542014fc73d854201cfd72d8542006f751d8542006f451d854230ef641d85422cef621d8542004fe70d8542004fd70d8542006f761985420057f75585421857c7558542006f5611854209cfe7518542004fd751854209cfc751854200cfd7418542014fe7318542004fd7318542014fc731854201cfd7218542306ef42185422aeec42185422aeee3218542006f75118542006f45118542306f541185422aef52118542004fe7018542004fd701854209cfe75d8142004fd75d814209cfc75d814200cfd74d8142014fe73d8142004fd73d8142014fc73d814201cfd72d8142256ee32d8142004fe71d8142004fd71d8142286fa40d8142256fa20d8142006fb60981420057f75581421857c7558142005df735814217ddc7358142005f77158142005f47158142006f9601814209cfe7518142004fd751814209cfc751814200cfd7418142014fe7318142004fd7318142014fc731814201cfd7218142004fe7118142004fd711814229ef94018142
  | 25 => 0xc000002000000c038000000400200a00900180040070000004002011005800004c001000800404c00800000b8000003004800800600300100040040000018000004004000000401401a001800c00000600cfe76d894319eee62d894309cfe75d8943004fd75d894309cfc75d8943014fd74d894301cfd73d894319eee42d894319eee32d8943004fe71d8943004fd71d894319eec21d8943004fe70d8943004fd70d894319eec6258943014fd74d85432f6bd74d854301cfd73d85432f6be43d85432f6bc43d854300cfe72d8543004fd72d854300cfc72d8543316f641d8543316bc41d85432f6f631d8543004fe70d8543004fd70d8543316bf40d8543006f76198543005ef725854319dec7258543005fb7058543005f87058543006f56118543014fd741854301cfd731854300cfe7218543004fd721854300cfc721854331ef541185432e6f53118543004fe7018543004fd7018543014fd74d814301cfd73d814300cfe72d8143004fd72d814300cfc72d8143004fe71d8143004fd71d8143296fa40d8143276fa30d8143006fb6098143005f67118143005f57118143006f96018143014fd7418143266bd741814301cfd731814328edf4318143266be4318143266bc4318143266dc431814300cfe7218143004fd721814300cfc7218143004fe7118143006f67118143004f67118143004fd7118143006f57118143004f5711814328ebc411814328ebf401814328ef94018143266f9301814301cfe76d9152196be64d915237f6c52d9152014fe73d9152004fd73d9152014fc73d9152006be43d9152196bc43d915209cfd72d915237ebf42d9152004fe71d9152004fd71d9152196bc41d9152004fe70d9152004fd70d9152196bf40d9152196bc64591523776c5259152005f77159152005f47159152014fe76d8d5218ede63d8d523476c52d8d5201cfe74d8d52004fd74d8d5201cfc74d8d5209cfd72d8d523467e52d8d52346ec52d8d523466c52d8d52346df32d8d52004fe71d8d52004fd71d8d52346ec21d8d52004fe70d8d52004fd70d8d52346ef20d8d52005bf7458d52195bc7458d5218edc6358d522476c5258d52005f77158d52005f47158d52005fb7058d52005f87058d52004ff7650d52004fe7650d52004fc7650d5219f6c5250d522d76c52d855201cfe74d8552004fd74d855201cfc74d8552014fe73d8552004fd73d8552014fc73d855209cfd72d85523a6ed72d8552006f741d8552006f441d8552006f731d8552006f431d85522d6f621d85522d6ec21d8552004fe70d8552004fd70d85522df6c5298552006f76198552005bf7458552195bc74585522b76c52585522bf6c5218552006f5611855201cfe7418552004fd741855201cfc7418552014fe7318552004fd7318552014fc731855209cfd7218552006f
  | 26 => 0x1402a000003000001200000c000000002101e0104000011018800401200b00000000000010008000006000005803800e02a0088038000000002800401800f002000400400e0018000000004003000802e00300b801401a01f0050110026005000000802a007003809c00000000100380080100000000002000001801c01000000000180080070078000000000000800002801d0000008004002001803800800500080ac02c00200c000c00c00e000803400000100180200020180018048002013002805c00200c0090040030006000002c00001600000a002c00f008000002c0000148010008009008800001c009006801c01000000c003408e0070030010002031004803000000600080000060000018018000003000000000c03f001805800a000000000000001800c00000000020010004006000007003c000002004007802a00500c808406e006001000c0160040008000000023000800000000100c007c00800f0050050000004002806000000c000006401c00b00e0004008003002800401a0060010004000012001802000200d0068008006000005808800400d0038014000000001807c03e004000001401600e00000000000070000008000018003801c00000000d000c00600000c001400a00700580dc00c000000002402c00c00080200020020000008000003003810001000300c806001c003002801800200b003000c00c0000010004006004005000407a009000000000c000000001000400b0088040004008001802000800100e8018044019001002c00a002000002000200000000140000150048028000000007802400c001000002001e003001003400c0000060008000003000800000200c001005000c0000030000008000000000400a00000c801002c000007800400e0130040014014016003001000000000000200000200230008000000000001c01802c000000c006009000001000000b00301500020000000000016000001802c024000000000c02a00300c001400c010000002000e001006000409000200b80ac00000c00f002000a00200280080e401300f80a40060010050028000008006800801200101f000000c0040050044006008001002800401b000800401c01a001000801e008002000c002004000800401a00f00000a000000d02280000040030000000004002002802c00c0000080088006065003003c00a05800600980160090008090000002014000c0020030000014000016001000801201c00000100300030088014000000001001c002000001000000203e007800000800300080480000150010098006000003001000a000002807800200000b0010000006000806400c010005000006c027004800807c004002000400a00500000000380000000014008015002800001000d0008008002002002801801
  | 27 => 0x60000028014042007000001401a0000000004002022000809c00000000c0000000010005800800000c003000400200c001000400e01e0040000006000003800000600500000d001c004006806c0020000028030000010005001400003f004005800a00f003001c00e0000210000004012009802801200100b000001200b0018074018000000802801400b001810801200500000b400c000002000000201700d0004000002001800000c01400a002001200b0020000010000000800c00c001000000c070002000000c01e0000000024008006001004c0060050000000000004000800000002f0040028016009007001c0040230008018028005002802800400100000080060000178058008000000002404800b00200000060030000014058000000006400c0230010004076000001804400200000000000040180010000024000001007801e00400080180040050058004016000000801000e000000800000e0010010050000006002801c05800c00380bc00a001000802c0020050098000000000004800800000a000000c000001001808402c000001004400002e00e0068002001027806802a0000000004000005014000802c000000800c02a0000000014000000007808400000000780100040000018004008000002002800800100280d0016000001800000e00600180100020090010000038007019000403200c000800800001b006800801c0000000020004008001808400800d004006001c001000800001c00b0018004000000000000c002000005800c000016000802c00403401000080360020050000000001020001404600b0010194000004000802400000000100080000030008034000023000800001000300100c0000011001801403400100001dc000001001800004c003000803000001a000000000000b0030034000007002001400200e00400280020090010014008002007000400000400180180220030018000028002000800800000a004005c006004007000000600100c005c004000003801800a0010008060018000003800400000400500080000000000014002000000001800e009000800002a0000058054004001018000000600000080140020000000010044000009802c026015000002005200000000b0002000004000000001001a000c006000000000800400a001805000000300300a400401b000800401600102c800000000800080240080000008030000006000000c00402a009803400401b004800800a002000003005200600100200280150010044008001000004c00c000002803804003d008001c00000000000040320040020000002008002002405000000000dc0020100000020020001001000c01200700000780060040008008004016000000003200600280040000110080018052002000800001200000
  | 28 => 0x840000000ed8800086d00000000000a8e4094d920c00ffa0000772021cabd30001113fdc6c609ce8d536547390000f54000020898c4f4d0000000015d0a519ece86441c1ea2a88dad2d5455401ccd8d000ce693c00256a15000002e48c80000000379cef7000000044a0c8d31080000a84d6d0f0c00006f4fcf2414bb80c1c910b66cab90000530089e76e00000000a5024106c450530e22d52558ea01e0c65d1b70136890c29d16503202940c89182907f30f4c4bacfc97bb050a579a6493b1ffc69f306401a24540001178f282e24b3331181089e6c0210000ffd29a0fce313ceed3e2cef4363cb52160c72f38c8cd3b3d0359000015c2b085d9aecca201634c7405a48513884ba241ac7a4138cc5012fcb8c00006551348dc59c4c2d60704da601f839f14d0a5442c45ff000105a04fa640bb26740254488104c8abc8990c35a06c3a5a53c00016840001844000405897500008792bc08b6000078a29b907b000018a1cf8700000049c000092e00000000000004010000008000000000b000802c0000030110044010010005801806a001003000400e0010068054002000001000c016003000800801c007002003c03800300e8000002006000800000a0000068024006000000800401e02800c0068006001006800c00001000e0004024000001003c0020000000010000002000000c00001500000e800200200a003401e005002000800200401b80f0000000001800000802a0000020000017002000401a002000000400400000300040040100050040006007004803007c00b000000000000f000800000a02900b00080040020000000002001000001402800100080840000030000020012005006801c03801a000802401c01000b800000601d000010800a001000002000a005002803000000e0040000000018000000001e003002001401c0270050020004005000801400a003000000405e005001800c012000008000400e00c00a00080000110000098000002000000000200001480280040010008000006008005002c02800000080040000060000000030000004004c000040001000c00200c003800000e003000002c0020050000068000004001000001400600000640080080000000004025011000c000004002001c07800001900000420030018008014002001000400000000e802004000e000804c008008000001c00000700a804400e00600a8078010003005001c01000100700a4000000001000402e03b0000010002013000002000001f00100000060360000008000032000000800200400080000140100000044000003000003c010000007000800801c000001400a000000804c01200a003808c000001000000402c004000003808a0000008004000004000805401401e00680040060060078000006002002800000000800400240
  | 29 => 0x4c05ce108262462c0000340a12400007c8dc9079c8572c0653e09a44c100011400eb090b04def760a62d13125603016a0cb30bd0f80237c0a3a5ec0004078b002c7c71c32f44351a243a933e806d3b345eb0520df617b85b10ca075c0000000322c20142010712ba489302c05510448a04068ca6c0f7c03f194cfe71d480003d30d8a239ce1d8eca0003c146370000db1000016a800019b26ece443de4f7033d8b400000d962dbcd41a14c217262e9df4028119b2ecc0d11f26e63470f723e9084e03d2351436442d3a64ee418f60000000a320ff80000e5c2cd3f4c36c3bf80e442d400000002c1800048d21d00901dfb121c34080f000073c2c2c0000000161c34884a1ea866f12900003c5432d0e5e000130c7a80cc10180534d8b3adc0000000000000000013dee060eac0390e540001694e4a0024f73000000025dc0002420d7f1154000000000000003f20b9c00d11a40003ab0aec291c1850000c53000057c166864437e837e13204b803cc12d36b8d4580006d63b045460cc496f9ded0090d783c20d0600036e8000410506a04046242b446ef23920982ac21b33972e7f138055812841f90a883f508b88a919a0d80ba1450b13f10e9275000010c0cf038b483d0000c550000adb0070c8c187829814388e900a8b2f289ea9f2bd03882c7e2d80710c6e1aec6f4a928844bf2069420449b8046cccb270cbcc2394c9f07d0df09edcf31083470111ae2e52846f1d858418da49c63eb58480742883b3360cff20d6065b2d6c64c2d988fc00001603e1840d0f604c23d48e7234d053337300004110c9715dc42f09942d7800000035a0fdd1e5c0002b48d180000104127c0003dc49b0923c21b19fc1bc18a87d13dbc5c8008c99515d06868000eab000088404e4d6f0000aba2cc400000000f0223c1be0000ac725b2bd806c0bca0000e1f0000ae238407ee37781b23270ad30ac89db31e831f364c000421a9414202b06122c7818c84a3d1f643e9000000005520000dec5f30000e9811a60000000000000000041a4a52434c00000002361458000378c1ed80000002f2400043d0902952d0f71b110d992b8c2105040000da01cf13a80000d088a51c9400000001de428400028587991774485bebccf100005ed24c0b771e9c00c1358997000000020d8f371d1c3333688a17000000000000002cb8000000000001b80003a1c2c4000000029906d8013c000359000044d4000000007b3816f270e1a3a1172475da7d90ed054086504d02e936d83c5a97709e32c00003c6894d000000043d8ef018880c2000000036940000000fb910d0deb00009cb00bc17700dc00e119cdf831f400006a66ea09242142f389ed43ecf4604700261259142000069800004d40dfd08d0000822091ca8b34847810f343341584d570000000000000010e4000157200004
  | 30 => 0xf0c154331064ab82cd4116eaa58070f02d151406b22a05d100003d400003483e544043b00a860000e6a0000000000043a12c00002ab00003c88000000000031340000000332000046a04bc000396091131a8dd9210076d00000001f2848a40d02184440425000054244389dd297839d0000000000000003882a0143c9522ea09e5c054fd510a06f91e1400000008d30000000282087a0000a4d4184c6f0ce86a728f08331de6bd90a0821a10e0e9212c876c1ff08d644e056e07d4426afe8b212500ee51630cd31528b64074219121300a342ae0c817002c53e6cece2ef00001d94000011cbd202a02ea2190d3536ac979295474b000000011700979818d720e880002c4023b000000004f4f6600009fc000025b2a14000362425941d0d42bd04e5a8001003439861512689090a6884832600000000ba600000000000a48000069b08fa6b400000003c0c8832a1023c447cb761d52b2303e10872824cb7035ca7809347601fa0b35309400005fc926210c91038c200002282221c0c0d1235c7f93a04609438026716d00003238015018cedf3c6000013d877e10900003fc01f607800312a68c2e0b2c8350922c5e390021100000000be1014448220e032e2f018da433000043c3314466000095b282e1dc31fc025b7d01a106d800030143e50000000000000000000000000dbb0000a571600d2c3f3423833fc3982eb48c33c40cd14174b59351a0b52ff4fc211e84e9aa641e8875437c06864ed058af6d170400001f4c1d41d8c7c2a20b1a3d7018741dc23a420830a0000718356500d0bc434f18c000a0c482f90c5059244881ce0c68f92bafa0000cf0ef18fbc0001c840000000ed1386c0003ad815f000000009dccd93f7c5f70dac60d1830000336c3e318e414623bc6a327f8000053899e35f80db397907c8a560002d8482f1a740001cb0cffac58aa3965c7690d5a000241e8a00e9a91e373cff301b112601588212c60b631eccfd410f674ab3f80dd0d143cb2ddafed0ec43b799dc36518010f2a9da82c2bc4372120ea9c05587b12864c85167435202c83d319703e21c089f1003c79597e825a42a0335189400014b00c90ea8f241d9c0b41b640000000c2a158cebf8000ec71e78372a252bc7000012e0f4f0860b18d071e4cdce3a745481f2ceef0d70673041e2780318b021264ca5286ed090ef43400c5cd731a58a6710c411e0170452260ceae24e643712508151f84af90f2478c001451e125a88c2f08b3b3e245d9205c3361b9c8f6275c5d6312438e25d8852038c5861838a28a788b9440f00590840053012cd0ac494898000000024d80000000000410104f0000f99177e000254d06c12d0e88242200042fce5415b40003acc4349ce8876000090733f0000000055c0000c6b19e8b973b2c00034c8f8113acab1bda8a0a9d44bd42238c
  | 31 => 0xb46302c4e40c2d1321920d061044c8622bc5961fc85b60e2d1181d748100e9cc02173a00000001030f98cfe800105c190d0dec268da70dc0eca034cffc14e032403281d7405c8dc38866fb0a707dc33d4f193a4c87116405be2a84a1c0000ed543f46ab27ec0000d2859b05b2287945a7b2371000022b90a927d00000f3828fa2283ae1389117a1c05a21e8cb8142c8b1c432865e0000f7c08d0770329cbff25fc866450400028e089e332a02b28508ed41960000000e8a40e8b9a38b0cc225d00002560e6c079065816901763e140003c48b071e600002a04000192817a1d3400000001e621d26e9179407924600000e80000000057b1cfca4f377c00021160000000d0d3df40000c8258216544ab3da4e0a318c000000000000010b61a00279b1b4b3c0000f8e27404ca35785191b7c64039e400029bc72620380003f840e70000ba304ec000397caf200000000000f8c00002bd00009040000b690001068800019800007f0000000006680962d78fb533accbe000000000000000bc8ade00000001bdc1ec12e47480000c3e3a3cb364304cfda9e42fa0000000448a8d2800000000000003af8a3a3f8cc481e2c9d932b88caa88c3ad0e40d3e242856f29740b64188d98000089012f889c3cd4a0624dce5893bcf8301047041e7c18609c0db42e60b240000d533d7c0003fac9d61274dbd3f1600000000003eb49a7000000000002fb000066a38d400612ecc5127440003c2cd1a8278f6700000000000e5a221910031a400012c400000000001d50be2057800040c8d3942740001334000059c4aa000041523cc2289a2c8bb330000037c80003160000356058731d8fe80000d9c0a2af3d0c24d3f20a9023000000000000001b8c0a0374901c0e1ee3c2704cc8174c63f21801e536bccaa1bb2aed13a020f39b4aaa034047005a0a600c6446b06a0b4b0e8710f0c4cd881595119208c5b7072c0173ef07bc338cf1b05e4da683fcc650db82002bd8e702314591283c7a00338642337cf0f11fc41640e41902d106b3139cbe53a1033e2d58d738648f910e506a816b02ab0f1a4590000e9bc3e40000000b14199807838a641b450c00008b068414409bf06e407f371c5ef2b8c8398000000097c0fd38441551c645b8308601b1394adf3468225222c0000000dea378a000000056cc154000247400006642f5359c00004a6215000030c0cfe53b000000018641ad29f42b122682802e4893820a00001d2869b8a6c50d0000e73427c0001c903b40000c27384acea80ec0001ddc0003c7a00038889b242e06c729f09cd1ad453f206879101c6a2ca6f00fa0c38579b020ba523dc1f33f42ff4043c9e52564fd1112cbcd1b481f725b83381f38ab51a482f63db8a98b518def1c28f2f076c2b7364672703d807c17a81dd3d84ef92f710071144e36280c3dd3
  | 32 => 0x229309c07f45113b6a00012143a29726895a350a0c416c08c12420681530c638000db800000000daaa050a46388a4fc8560b2898200007c2000009100000000cb60002f8000044c68683ee80ea2cf8cc100003cc000058a204c00000000000000000440400031840003ae0000000070e04c05354306f7527a4b9500b44500000eeb00001ed2a5a000000000000000002c7a145375c9a111e067400002af07ecc4e0760551adf85fd2dc443e800000017025551af80003fb80000000d032b6800031701c6404096241587e2433006741b846202b42d90a106a915ae734175c4f7291a49207284203a0030f1dd014407fe7101924ce52d44344b174d5115e4000364481914e81ba8e3000037e4e1c1e40a7620943e7251c0002d76aaf1b3050305601ae8000dc21fdc000298c13327140003c4c0000c0200013e80ec3f60a01bd1ca720e008010360491ae0c932273c40a278c31b000108c29a50430698a463a980000da2adc05b8c183e9c00022fc28bc15063d0000000089c000247e000211cc83271000032a02bd99801240978d1900d40bc0b4004c081ca91087cd8410f492901d07f431c0f2c331c6ec13eca370c122563d7851b2aa40b5a184ee818f83b1a4128f812a4d381f60e2b20ec3e4ba8299a0000bed000081d1b0cf252620c6717300802e2c0002d886ed243506f147ce521be806600010fc143061028a4524000000001c0d81b23cdfb41802a29f409fa11b8fd2116d0d115e0ffb22f47863bf49e0113ca6d31c8c222264be319c034e11f465a03ecae48bb2571117c5471d786e52a94a10aa8cab33f80a2e3e28a5a10501a044c4cd52d042f32170fa83d24869033c35a2404a440ee00442ed06162614d273f6c463388e97e4008f1622dc8fd451c0602db044c01a8aa81aa86c127c020828f8d9f0b210ea0148cd425851330254812181c91f0fcc66b0bdc5a60a0402822be2c244710682d306f60696665000076f07240000000ca420e000000b08a12d201a7b348000037c00017d40002778ef6000001d120c2b4037a31fa398a77b61491a17287a108668da9ec103b0000f7407e8000053c321bc789244388000000000039d06ac42f098e06723ca88f69c2c09843f38a05e8016074605e000010c8bc3000012200000000c54fcb10a80000ef812030d07143ae4dcb311cdfd005ad1f3f5c301b48c000189896c3af42ba095488b8d74a7f35107840fa8c59394c2be000000023345432628e63000000031805b011b01eb2af08b0356a000409c0002a900002b0a0000000d77441ee3e000000021c87c42f6800045102853ad0c98c3f8fc500000000c200001456a74804d0849798aee2a5895406220004068dc7a78a29604e217e375404221d46f23c50ccd20908f936f0117837028303dc8f1077e0000000db728880001ef80000000
  | 33 => 0xe5618d0c6c18140000000e0e246cdac133ca1e3e80d7497c8000000000000007e90cdc73725682b816dea5c800000000000000e68ff634cc9783248d2d00005e6a9fe7c135388fb3640e65383e96b14702098d0eee487006b9433439601340f44272d5636e605b3ac49683428e6f3fa84c7149c9490a2652e30b4c5a0ed8cca107c00035669172800a27000022b1950559195c35502a43d5445d04e29d087b0e450670ddc923270046530101422400f4e4290b6a1e2e52a0fb06f0324c000025c427a38c28db0782fe3b30131269455d8264612284847a90ad0c51ee46ad16a20000fdc6b20000000128cce616d4d6a3054ae100000ee1dfc0fc16b4000178870c079201e41f70c29a1400000001e68000000159c55e029ccba0f6c50700002d200000003858c4b00000bd0d9c000448c4bd1474bb60a480000face0428b07df0f200000de0d3d000000000000001fe0cbc0000e001f24ce737b87ac3dfc96dc35a00000000003a78ea715eaed60bbe7ed1eac78000000880000c44176c000000000000000000c0c000101c9633e4019e01ca173430c0f11b9600027180000000000078400024fa8ed88fe9db8bb6b25000097c0874b994088c4300000002b800002ab89b02f9817b0b8c0c718d899f146019f182c7f12ed510801900001a98829b8c68b53f004e910883413e488fe0000264b798d360f58cb12b3865115fc65f05f6ba907209a4014085e18b80000564e7b42f4de033190e09a4c0002dd40000d5d0202d38c3b0654e0c25c29aa0f680000eecd123b9c62d166a4f33ce00000000c2307f00002ce49720c1000038dcd301c788872580e5d0f3cabe000066d315a00000009f2000000000000001de05023600d75216c38f0000000134cc791d6c43b000056400000002ce8f7e22c80004134ae437cc2d74176fe0bc7c15d38082ad0c0ad0826443992a8052b40b0dc33d2c3e5b4e80002650e8d0e1047722965fe3704e4b047449b144656d87441a0830d0a6064cfeda154c2841ccea1000090680b8d7937f80000ffc6c83d88e203c1c00037d4a131b6c59f261834c3f64000234468200002730208fbd23fc0003554484b918832177086d9e3838ab458373000000043a00002bfc00043e87080000b8810f86d32fdc0000000b6dae905b9174800000003ba315ef58415cf092fb300c0aa8418420c2d118d41a53c70add260466422b012a3920290903cd9e2c82621316c402155810d069cb851d8aec344344df1a8079c0008dafac041b430c00ba0368d4c0e783fd3cd822a02f824b3ca88c0398a36d04f0c750a223bf0634d4a380404d80003a53ae90dd0d8455011087a9049c9b6000014c1ee00079d90ec40f2e000144a2ba9cd85c34408a0e411400041910f20afa94213e4fbf0c600b31bf48ea1e5a8aa2488ab2b42e9ee3498fa1
  | 34 => 0x72dc800018085e93bbb0f0379099223842ff0000bea006055eb99c00041248f692530dc44ecbe9000000022f067d1eb81a2386a29f37fcf0641c800012888349fe8e45000036b92d8f633894270bf68e1215980000598b540b7c73126c4d1db3a2cbf0000ab4446200014800000000c400000c1600002cc1b345a70a4c4db23240000000da80de423206100002712c5200008ee03941b802dc1051cc0cb400002952834ad700000000c8e0000f8e33ec4b411a06fc04629f8b8d060408e000053c3c8452116fcd14246e792c2ac0001c56acf04acfab347b12919e4032414110643d40003fe40af1add0d429a86d538fe9008de86753eb07200000a5b13308b83040bde38602400e98f2094bc75644a8a87c44855d0000641231c00028c4ec93a688a200002372de860805944d8000106687400002b2cb0f1a18b2c00000190000a9d1dca98036842ae000113c0b84dd80f5d07934a8329356c9191614e420d1c32242544fe18ccf1f9e1c74f031418eafbadd63400d25155c42612e82680d9e00b16b8b8408089ff2114c67b3308293cb41282b987fd17344722c4c1c32480b9038d02a4135cd7b37b0df737e6c3115d87123ffceca9b2c20430801642df0beb39c461308f8c9e0f220002b283ed1b5097034ac000385000036746d103f83c99c7cb5a06244472c8877a00000001c6800023308373ec024804624b70aa0f421000da0020279439050923becda782acb52b90f10903787dd1b28edc3988bf10e9ee903cf87c84178f393af00000a780002a60000000058f000076b04e8f930000dbaa9c08f58f141ee9c1c0000e189f50000000271d10582ec32a38c02210dd092c0000ec825a8bd6077d1328dc4e051160be41e943d227b05af32aca0a137905228a8cc31dc48311b905df3580f8208a68db01281022eb0a9b26109afa430e0333a490e36c070d27245521f502fc394691301743822eeca931718e9b4244dabaef83b22b60e290dd40000d8cfc438f431c39a000012383e03b407b6000005414200000e6c7e5378281c15f4ed72769085a416e2f0afcb4a370e79620fc7cf97e0f9439f4fcd8000e570500e603d107e4257c27109e844d23a00332eb822f4484d310000d5d375295700000000528000228cfd600000bd80000001da8f9830e50dfb2c859300010bcaa3c0000000ee12ebc00000000401ca861f28d409d0dbc0122a311152e0040e3b9872e2bdc3d00000ad60ab0bf3000048c243c0d62060eea11ece15b07cdd30094306089ad5c27dc089348089126b8f0c073446d34906fe095ee3333806521f14203098ca6b298468343241b73bb8fe23c286040df421c20e426b37940000ad86271a349d800004a00878000188c000000113e0ee5130384e49c8a65105407502a3ec492133ec78f20000000c2200000004b32134000091
  | 35 => 0x2c36904547d60000da405a80000000d49321c87f000024780005b310645bd1680650912912711d0cac108451cb1dcdbe0424fbea366526393040c2c98d51a1a8a413aa827e28ac750062064bb152aeb0d180e10f44311246b02b20f810c028a98ec2cc7f600a4fc72fd022d124035f104c26026ac26245183068864233446d0bbb1ecdfc2010ee937141cc13d10d730ac408424c4640ad48880d4cb6d017c9ac00000000b8894618507c700003dc1c241431d640c00b00bfc00000002d0c000270810e0000b9f00000000ac093a3a2c40b1f98a282edccd7000086fb7710ad05c00000000cad0fc00003e7c3012adc2202028fb7032a00007bc00017aa000000000014a401404270782d1487e2ca000013fc349262c7db444432b37a466122006dd000006110cf0db000037640001fe3ac8d8eaf44ca92f8a5aa24461f83b1402693640af971ad62013e62930680b4a5f4f782fa009f0306e4e11f098c25a4a5935ca25c2cc850405c49ad0a386de1b3839300001000e28b2a0eda279171449e1254eda422c276000035581470f1986c28621086ee012478210a4d810ebcb8e3024a02b8200013bf0e1d000100e3c34d42422091ec048fb200d0000002080b4250000399809a000000000000000000f7b00004d10000c243502000000000041b40621a2086e35a22c1033a198800094a2bf094e2f3c000000092b000028700002729a380001c2c0000a3ce9412050cf21e000014290ec31f895180010111d8200019f10b90000baa281cc84066a26a1cc836211d400000000002b64b0508c0c4a33d673880008f421e6d7836d4b502b300003ea4000153806f2c020c42ef40000000b931bd4bdb20b44b5377e45610b0daa2cdcb5719f85da3f1856b060c2611da0e170b690b4205036a000097aab00e612224cb519b0e913a8c743014452d1be0fcc0000f3f268813abe3508135122310e148d009d0a7596ac086429c11002b8c411e7418024e4000000000038e0e07bbb0896320018230d41ac2c34c1311e41dbc2b80003be8a88a0204123b8e00003550ac33dc4c006eca3f3bc87eb2b96e4d0828c2ab1563c40776656294ca62000007086bc2ce00010661ff6267ac44228166065932404f80000e22ab10b27000046f0c785000000eaf05d23922a5cdf007a0c1c37c510a1b68a181500a802ce01370ed446822549b426345fb2008edd00009d200008b10ce40000c348a6100422420248bb946e39c31900002b4103d234e00000005720000a939ca4000000000000000000000dc80000a35bf94454301883a4014000227464e401800000000001e9884f13107af25ba00000008031e320003f92e7a2b0ca43171c0002728cd00ec01521354e1927840000000b8f0000000229afa6301c9a01a94fb30a2819c3b6c96700000000000e8218806e0000104
  | 36 => 0x1c45a31c400043691068000bb10000000372835d975b07c0000f30000000005883be94183023b50e8330f0705232c2cf2db200007c00004260000217caaeb4103ee28d84600d2c205000069500009d32aecd6b2a340002bec1da09bc10a00005130000b493756e5b00000ac38b88e43404fb60edc70f297c3560000d4b000000022cd0e136087cd3d5d0464004ac914c4ae8425e6bd1f4af552fb0f500acc00027a800000001260d92d1d0512a733842d1b3f04c9131bed970982000109c3e1b520d541778389856878d27200aa2d9ab1e124cb342aac0cd088c687426ce14854cffe3ccc87313147661fcc26284f6ea935b8000449000016380001c8c0000b1ca2d231000044ce00000000000000b58000000002040003d64ba10000251125c98f992cab006a854140110878c2a63a000000042c0af68a20000157d0ee294400022b4d40000000000004a50a4000000001ba1450697020e5991ae000000006a21860000000023f2494000216800000000451e6894537865f029dcb7886b8c0e40f8ed23c7460f1f000b137188ff8c942580c9cd8c26cc9fd04d4776187084638c500f333800041f44032a660000bd291da28200000000000a450361d14abf23b0ef3172cd942d4c000000106fc3ad12f0da657b844cf9e3fd40000000d7d26bd02e3f3a0003fbc09c00001a93284c812a4ac540c14d7a38350d622ac54d16105601ff84572f4020b3e947fcb1cca012f744532f9c6f1297081f1bac00037448fa3e3c4e10a8c72d3d5888509144442b203a491248cf3e5816f2ac896d0d725b23f3ee4f04590bb06acb863d90bf900003bd91ee9f93a70bb933a87411f4c0d234406b600002dc0000594ab5077926dc94344ad11e171090207fc75300000004194af0b4a00003dac0f53824128c468bee00008440000ca22771139037edca80010133be07e70000982c06c0002bbebc512767444450ab60bb000030c8eb50000ef12e9688cbc98b680a9cc171afc990440c156b4b90c01b244cb42dc532319816bb734a0b2a081cfc2247e003a04ad2c389b9220838921dc4ec41204711074f3b179d07a2e74a919fbc2661a8499b094c03d2ab40f38112f483454da9010ca102c247152e6d119b72e6a42cac17c0a2d0c2222b029153c6f40210c2f1b5ce24231842329308adabf4d8e2898afa35627c607126470cb841c336835013c400000004c9227ce5b800001632980a4000023d3542d5a054400000007612380c2c1494000000032605c8d290d0d0380000bef2e70dc2a6f428c3044143800024e2c1032e845084b0000c373ac00002b9cf60342c00036648200000d470e34d66000077d0fd03e803980382a6a7e328c09b53028ac6046080d0d9007a0fe0b3020d095d21b02391a30ce08f847b50d3ab0a2a9ccf904d8079ad7074e43
  | 37 => 0xd745bb43900e919e00000ff000016dabb000010e3055668f24511299e54aaf80401d206d4b0308026af0650c3604f864f20181d41120ff10494363c338e763b78a251dccee3145cc2634148da33cc3e0b11483c325ec953788757000000034bcf342900cb81cacf3200000002348a45a3c094424bc491402003c35a708a0364f65386e0000c8a9c3ab545d41208775353cce233908de322068a0818ec890d90353a584da30a400038a82092854b7e8000a560000b9e07a51451740b7832583f629087ec3eb8119391cf0200000000000bc01e6afd017b000027a0487261c282bbd4000218ca45448024c32e4b0829380002dc00000bd6ba044100b8439c9931784c8209486f301c907e0194cdc07c44af2a2896f2bf68672f4cd7c237457300001309f2eaa29f5513d383c88697544ac045ce2608985f624d07ea3f9087599c8628425cdf7b0e0a6605d425d25c6b292f5c64526070c4078c0cc2364e501f48a90287caf33c387162f2041e1fd419d37748922142f2e240662f26c6de82c742e02c5510b1ccc1293274bd7a09c23cafe0b0c0dc6e3a266472842e8bf00d0a9cc11d800015d40e03afc4a80b24eff0f4ab471874000000031d000000021f4742054ee8c00570630bbcfe639f800000002bb0000e8e292c0000c40bab33e000013c0197000050902c6000263d0a6bab400000002d44064562000113a1ba01d301d42ed416008b0000bba0bf40001a709be16a4a950af0dc00000dac855c00014a0bfe1024dda343ce0690b82892be09ddc4dc00000000000b7471d3e740c096209ba000000000002e82924000086a00012604f500007c9a0143fb0a3400009d513626a071b35a48a72a522291df0c9a230800021f0187a29058113daa330000fec024cca036cc4a61cd4f2937bee392b04c033a94e75210483cc4b894830300f936c8f9c1100bdf041d0f1391229aaa785e421bc05291cc92d10140113a66cec354014929d43fa0154652998d0a31104b203188ac53e8c50100006623e5aaa627bcb6e267024f3f70000402c78919b800000004e6033e00014d8d0c1ab904c3f7889b1678ded0000f3c279c0000000489029200028ec46abaa06cf2ec86c52540b17437c5372d806321d6820c388c8943ea8c9428904bc063ce6b3b64fb429ec7a22f10758439507523050371c4412fb146b122030ab109402e4260216d39700042f4e52334f0df8bc44c3a00004dd3ee0ce9832c000240c0a2042c00014e4e134214955228635b4354dc4c3e017d345c3969cecc5881c479ea0ac00000000003e1066709e20241c8867600006c9ad9458b22e851a178c2f1b6fc5c22472163000063c00002f9bb888f20e8e48001dcee030daf17137000000002c32fd505f1d30aef191847e29e8f5300006ff00000001a400001448a9228aecaf2d3cd4530cc0
  | 38 => 0xecf00000004090f4300006b12d7c8e220b8123238efe92bde7bb1d8cd4318ac2f7a4f869e20c0e2735d003e0658283ac6c6c0358cf97042a9123ddcc1b368c9d542580b995c113f1a0455a00003f110e6dc8b6190be0ae624200003bc35c400038fc1471a2200018fe27d09eced83d4413f412ce539a6913403c860300009f300000000000297176000000000200f0400038a200000000001d5508441645442bd456926a4f7a33745890ea0b8233b41c2133805a190a00023ba5ba0000a1d00000ef25c400000008e5ac64f04055e33d21644c62698b8a1efc8973534717000034f80d8aeeb868dc9baecfbe2f2d0de117491c18690ff3b6665aacf40002dc210600002162994d0e326d0a041c00000a98022054ad873a88fdf929cc8a2590cde3324a2f09b026e326406923d418b105cd9a3c80afe424016c00000000714000052c34425310c62098cf22328a022b9417ea86844514888bca8b6a0fb3bc0000000000000000004f2f4a30fd0211e20000407c385bdb102835d870617383c48000ed312200001184617328cc1224cc6b00fe4e974264cb63594c62b33ce6e03770310000f5a2a5e08d28e40002418e77252ccd62b340000f903c01d7f05cb7402130638b742798fca317c2db3e889a3000040622e44461cd62723964c5b826c0920e8cab3a4f04f217800000000000000057a0a72e15350e00024f40000000b7d3e2000000000000000a1b0e04383000005e43206c20918b7f047c13b9bf08502a24b79303c7cc39e02121eb40941ee85152f050332338096994031617f0c782dacc683b8a16b001a5a33e690af0b4c15b2f8427c0e1c323020d116154c56c2ba899d37503c6000000026582e644b055b124ecee21ea00022d0ea4152400000010dc800000000000000000000071c95287b859c17d10420000e3b00000003cac0c1000085d4474e8900000000cec0000a945f11b409e42160f011040a83357c0001d7c1d92efc4ee36c20000f2800027ac9981f7800024d50c70000e3d973c00033f444e0000c560298254221f11300002ee0bcade122f82a90000e43423910c000000023ad0d829c4e1e00000000bea965376c86b0f6454fb5c026d25789ce1f6836024a8cf69b2eec63c8c48400000000000027000026c8000d3716f06e236e48621f0cd3b44a302f09bad6ab54881e1f3c6690000ce8124aa113c200bc80002eb0758ae699c4e5140c0bfb00009733d001b99bb691603b47491cf433f0120e1c8bee97a42a80e48c7ab2d0d5000013f44433a543a402fce7c01d800000005e5b360486259804e3b0905106b656813a308f24a0266adecb8735b05f90a66646a872bd6adccbf21a44fc92d9c7bd27e0c013da02b943bc43aa4c40001ce07b42d082352234816315c0002f18b963fe008540fca37807c0a5000034d095c03a3
  | 39 => 0x1068000000018c0284e073924297ad342de3d140d40f32e6409fc1380d98f4f2a020003488f5b1b84f3a0f1c63b34783de00000002ae012c0cbcde38000ce128d000015f80000d96972800000019340002a50f87000017431a60001542d113408bd52fd87920f8b0532e44e5500000001ae87fb03ace9f2a1c1e2000024a000000000000001d884d02e9c95c2360fbb000032c41286012d750f30a161a400006bc00002f398e0000023c56a0000a213792000000053d00000001f5c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaae82cc5640400155b0598ac808002aea0031590100055cc0062b202000a3e85c85640400147b0b90ac808002aba0a705901000556c14e0b202006ab5811c1640400117d0e182c8080022f61c30590100055741060b202000aad820c1640400156d02182c808002ad60430590100051f42840b202000a3d85081640400156d02102c808002ad60420590100045ec3cc9b1820008bf87593630400717f0eba6c6080032d5d271d8c100045ec24eca1820008f6811d943040051790eb2286080032e5937050c100047cc30e0a1820008bd87993620400117f0eb26c40800e2fe1d74d88100065aba4e3b1020038be849d9520400117b093b2a4080023da06765481001c5f420eca9020008bd841d952040051bd063b2a4080023760c765481000716292c8a9020138ec8758952040274d90ab12a4080022f61276508100043fc2aeca10201387c855d942040031790eb2284080032d59371508100047ac30e2a102000cb5641c5420400717d093b264080022f612764c81009c3f428ec990200087d851d9320400717d083b264080022f610764c81000c6e43ac699020028ec87589320400196ac9b8a64080023d618714c8100065ab20e29902000cb9645c24104001958e4b22820801aad205645041011e57326e4a082000cad64dc9410400117f0cba462080e72d985748c4102f45fc3ac9188202a8bd87592310400196ac938c80080023de1971900100065ab22e32002000c9c73591400403593cc9b9a80080032759373500100065ab24e318020008f7865c6300400196ac8b8c60080622f61b744c0100045f43ac898020068bc87591300400196ac938c40080032d59171880100061f326ea9002000c3f755912004001878eab22400800e3d61f64c40100147ac3ec78802000ab584d8f10040011eb0f30c200800f2e5da64840100365cbb2c908020008f987986100400717909bb220080262f61b74440100045f43ac888020068bc875911004001938e6b2220080032b1c964440100064f326e68802000c9d64dcd100400195cc9b9220080032b59372440100065bc26ec8802000cb484dd9100400196eedba220080032ddd874440100047b43ec88802000ab586991100400196eed32220080032ddd964440100055b43ac88802000ab48759110040019aeedb9a2008003a559373440100066bbb0e68802000e95641cd10040011ed0fb1a2008002ad613634401000673bb6e48802000ea564dc910040019ceec3922008003691d0724401000752b20e48802000dc4731c9100400196ac9b8220080032ee1376440100065c426ec8802000cbb76dd11004001976ec3a220080032edda64440100065dbb2c88802000cdb76dcd10040019b6ec39a2008003661d0734401000675bb6e48802000ceb761c910040031f50f30a2008003ac5926144010
  | 1 => 0x8edb128288003a91936250510006723b0c4a0a2000ea4641894144001d88c631282880035cdd47050510006d9ba0e0a0a20288bc865d23144055938c6ba462880032b189748c5100045fc3ec918a20098bd87d92314400193ce9b1c6288003275d3638c510006573a6c518a2000cad74d8a31440eb36b0f3a4628817ba518e748c5101574a31ae918a2036d94635d2314400136f0fb246288003a518f648c510004dac38c918a2000e946319231440055ad0db1c6288003359db638c510006caba6c718a2000da574d8a3144001d88c7b146288003399d8628c510006d2ba0c518a2000ea46418a3144001d88c631462880032e193704c5100065c320e098a2000cdb631c131440011e90cba262880027c201744c5100065a3b6c898a2000e9463d913144001968ec3226288003a518c644c51005d6b436e698a2002cd476dcd31440055ad0db1a6288023351db634c510006723b6c498a2000ec463d8931440019c8ec3126288003a9190624c51000762318c498a20009b5841c13144001ba6e638262880033ad88704851007e5b3b4832022000c9c73d9140440011bd0db9a808800327d9373501100d64e326e6a022000ccc62dcd40440a31bd0fb1a808806a3721f635011000667b9ec4a022000ccc73d8940440019c8c5b8a80880032dd90715011000672310e2a022003ab4865054044007968eca0a80880db651cd4150110005d840282a02200ecd6768c6304400117d0dba2608807b2718f744c11000656316e8982204c8be87d91304403d1790fb22608800327dd3634c1100064e3a6c69822000caf74d893044001958e9b1260880033918b714c1100066bb18e29822000ce4621c530440010fd0dbaa40880030f19375481100062e31eea9022041c6c62dd520440850fd0fb2a40881061f21f65481100061fbaec89022000c3c75d9120440018beebb1a4088003171d7634811000637baec49022000c6c75d892044001968c9b8a40880033518f71481100065a320e29022000cd4631c520440019cec438a4088003a619063c4110005d8c246388220038f686dd2104401396cedb24208800f2d9d864841100147b436e708220009b7845ce10440119acedb1c208800b359d8638411003e733b6c50822001ce67618a1044001d48c83142088003b118c628411000557410c73202000aad8218e640400156d0231cc8080028fa1462990100051ec28c53202000a9e8318a640400153b06314c808002aba08635901000556c10c6b202000a3e85189640400147b0a312c808002a7a0c62590100054ec18c4b202000ab8805cd640400155d0439ac808002ab60873590100051fc2ae4b202000a3c855c9640400156902b92c8080028fa1732590100051ec2e64b202000a9e839c5640400153b0738ac80801a2fa1f31590100045ec3e62b202000
  | 2 => 0x265189100056741cca3122000acd8399462440011df0eb28c488002abe11651891000556422ca3122000acf83594624400159906b28c4880031b9d86518910006573b6c83122000e2f65d906244001c58cbb20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400155d0c320c4880032b9d8641891000717b28c83122000e2c651906244001d4b02320c488003339db631891000727b2ec63122000e4c65d8c6244001d1ec9b18c488003a3193631891000476c3cc63122000a6e8598c62440014db0b318c488002aba12631891000556c24c63122000ace8398c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488002b3a186318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d90631891000746320c63122000ec58118c624400717d09bb2a4880022f61376549100146f41eeca9220008dd83dd952440018d8a53b2a4880022fe11765491001c5e422eca9220008df835d952440051b906bb2a4880023be09765491000636290eca922000e2c52d915244001c98a5b1aa48804e3ba1f625491009d3742ec4a9220008f686dc552440018eecbb8aa4880032d19371549100066a31ee2a922000cb4641c552440019a8c638aa48800339d88715491009c3f42eeca12200087d85dd942440051bd07bb284880023760f76509100043fc2aeca12201387c855d9424400117f08bb2848800237e0d76509100146e41aeca1220008ef825d942440011ef02bb284880062fa1f645091001c7743ec4a12201387e85dd932440010fb0bbb2648800e2fa13764c9100045ec26ec992200087f855d932440270f90abb264880022fe11764c91001c5e422ec99220008df835d932440011df04bb264880023de05764c91000c6f43ec699220028ee87d89324400756d0db2482880032d9db64905100074a326c720a2000e946418e41440015690ca1c8288003a91936290510006733b0c520a2000ea46418a4144001d88c631482880032b1cb645051001d5b40ec8a0a2000ccc72d8d4144001d2883b1a82880023ba1b72505100063632ee4a0a2000caf64dc94144047958c9b92828800333d8f72505100066631ee4a0a20608ee87d8941440471d90fb1282880031bdd76250510006363aec4a0a2000ea441d8941440019b0c7b8282880032ed9070505100066c318e0a0a200cab686dd14144007968edba2828800eada1b645051004e5a3b6c8a0a2000cd476d8d4144001d28c9b1a8288003351d863505100074a320c6a0a2023ce476dc94144047d48c9b928288183391d87250510006b23a8e4a0a2060ea4641c941440019c
  | 3 => 0x831a2000e957119063440014bd0b310c688002976166218d100054f424c431a2000a9d8498863440031dd05bb286880023b60b7650d100045fc22eca1a20008df835d943440011df04bb286880063b2097650d100047dc02eca1a20028be87d9143440071bd0fb1a86880029ba1732d891000536c2e65b122000aae84997624400155b0932ec488002b3a0e65d891000566c1ccbb122000e2f65d9362440014dd0b326c4880029b61664d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c488003a960464d891000727b2ec7b122000e8f64d8f6244001d18c9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000747b20c7b122000e8c6418f6244001d8b0231ec488002b960775d891000637bacebb122000ae6811d362440015cb023a6c4880038bd5254d891000537428e7b122000a6d851cf62440015cd0239ec488002b960473d89100047743ca7b1220008ed8794f6244001c9ea729ec4880023ba1c43d891000476c3887b122000a6e8510f62440014db0a21ec4880029be1571d89100053642ae3b1220008ee87d4762440011db0fa8ec4880023ba1f31d891000476c3e63b122000a6e85cc762440014db0b98ec488002aba1331d891000556c2663b122000a6e85dc362440014db0bb86c4880023ba1c50d891003c76c38a1b122000ae68110362440011dd0e186c48801e3b61c30d89100053742861b122000a6d850c3624400155d08186c488002ab61030d89100057340861b122000c6c62dd56244001878e9b2ac488003171cf65589100061fb2ee8b122000cac62dd1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac48800327d9373589100064e326e6b122000ccc62dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d0635891009c3f43eeab1220038be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000cb474dc562440019a8e7b8ac4880031b9db651891000476c3cca3122000a6e85994624400155d09328c488002ab61
  | 4 => 0x4840031df0eb96c9080031b9d572d921000636baae5b2420038be87dd163840031dd053b287080023b60a7650e100045fc22eca1c20028bc87591438400717d093b2a5080022f6127654a1009c7643ac4a942013a6c8558952840270fd0b3b285080021f6167650a1000476c14eca1420008bf845d9328400717908bb2650804e1fa14764ca100043ec28ec99420028ec875893284001938e7b22810806aa7211638c2100055bc22ed8842000ab78458f108400155d0531ec888002ab60a63d91100051f42cc5b222000a3d8598b644400153d07316c888002a760e62d911000557414e7b222000aad829cf644400156d0239ec888002ad60473d91100051f42e65b222000a3d85ccb644400155d05b8ec888002ab60b71d91100045f43e63b2220008bd87cc7644400155d0598ec888002ab60b31d91100051f42e43b222000a3d85c87644400153d07b86c888002a760f70d91100045f43861b2220098bd870c3644400155d04186c888002ab60830d91100055b40861b222000a3e85083644400147b0a106c88800327193735911000656326e4b2220028de87dcd644400193ee9b9ac88800327dd0735911000c7743ee4b222000c6f75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440019c8e5b8ac888003361cf705911000557414c63222000aad8298c644400147d0b310c8880028f61662191100054f41cc43222000a9d8398864440010ff0ab96c68804e1f21572d8d1000567414c9b1a2000acd82993634400159f04b26c688002b320964d8d100074ac08c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000ace829d3634400159b053a6c688002b5a0474d8d100056ac08e9b1a2000a5f855cb63440014b90ab96c688002a7e1171d8d100054e422e3b1a2000acf825c7634400159904b8ec68800297a1721d8d100052ec2e43b1a2000a9e84dc3634400153b09b86c688002b5a0440d8d100052f42841b1a2000a5d850836344001938c7ba2c6880022fa1f6458d1000656396c8b1a20008be871916344001958e4322c6880032bd937258d1000656326e4b1a2000ccc63dc9634400717d0fba2c68800327dd37358d100064e3a6e6b1a20018ee87dc963440018deebb92c6880032bdd37258d10006563a6e4b1a2000ccf73dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d100065c3a6e0b1a2000c9e76d906344001d2ae3b20c6880023761e6418d100054f424c831a2000ace82990634400159b05320c68800237e1d6418d1000567c12c831a2000acc82590634400153d0c320c688003279d86418d100074ac08c
  | 5 => 0x2ada1331d85200043f43ecab0a4000c3c74d9561480018b8e7b2ac2900021fa1c65585200061e3a0cab0a4000c5c73195614800187ecbba2c2900030f19774585200062fb2ee6b0a4000c5c65dcd61480011ef0eb08c290002ad21161185200056a41ac230a400087f855d061480270f90aba0c29004f1b1d552185200065aba08230a4000ab684cc461480015cb05988c29004e9b2195294520006373b2a528a400087f855da41480270f90abb4829004e1fa1776505200043ec2eeca0a401387e859d941480010fb0b3b282900032d106765052009c3e428eca0a40018ec821d94148001968823b282900021fa1b75505200043f43ecaa0a400087c87d9541480838d8e5b2a82900038d107655052000637b2ee4a0a4000c6c65dc941480010ff0abb4629004e1f215768c52001c5f420ed18a40008bd841da314800187ce9b2c62900030fd95748c5200061e32ae918a4000c9e74d8e31480270fd0bbb262900021f617764c5200b63632ee4a824013a6c8654950480038d8eca92a090002da20152541200062e39ecaa024000c9c73d9140480018becbb9a80900031719773501200063632ee4a024000c3c74d95304800187ecbba260900030f197744c1200064e3a6c69824000c6c65dc930480271dd0dbac409005b1b197758812000c76432eb1024016c6c655d620480854dd0db2c40901071b9db658812020f35b06cb1024013c6e7619620480051dd0db9c40900031b19773881201e4f5406e71024000c6c655ce20480051bf0eb9ec988002a7a0f74593100055b40c86b2620038bf875d363c400153d09b9ac788002b5a074358f1009c3f42ee4b1e200087d85dc963c400117b093b287880023760e7650f100145f43ec8a1e2002a9e83d9143c40013e302382878804e1fe1d75d8b100053742ee4b162000c6f75d4962c40018d8a5bb2a5880023b60a7654b100045fc22eca9620038bc845d952c40018d8a4bb2a58804e3ba1f6254b1009d3742ec4a96201387e859d942c40010fb0b3b2858800a37a0e7650b100046ec1ceca16201387e85dd932c40010fb0bbb2658804e1fa16764cb100043ec2cec99620038be849d932c400117b093b2658800a3ba1f624cb101753742ec49962000ab78650e41c400176100a1c83880aaa7a0f64507101cdcb41ec8a0e2000bb180d9141c4047d48c9b9283881db39dd87250710006b23a8e4a0e2060ea4641c941c400193ce8b1c638817b2d5da748c7101565abb2e918e2000db1745c231c400136b09bb263880027c201744c710004dac20e098e201ea9e83d9240c401396aed20c8188003271cd64503100065ab20e2a062003cb47650540c4073b28e6a0a818806aa7a13638c3100466abb4631862000c9c7458d30c40019aac638a618805a9ba176288310006363aac49062000c6e759cb6
  | 6 => 0x536c1663b2a4000a768110365480014eb02206ca900021fa1c30d95200943ec3861b2a4000a3e840c3654800147b08186ca901069ba0830d95200053b40861b2a4000a75810c365480014db05320ca900029b60a63195200043f43ecab224000c5c73d9564480010fd0e32ac890003171cc65591200062fb2ee6b224000c5c65dcd64480018eecbb8ac8900031d19771591200063bb28e2b224000c74651c56448001968c838ac89004e1fa1f75591200146f43ee6b224000c5f75dcd64480018b8ebb9ac89000317dd473591200062e3a8e6b224000c9f741cd64480018d8ebb92c8900031ddd771591200063a3aee2b224000cd773dc564480019a8e7b8ac8900031ddd471591200063a3a8e2b224000cb7741c564480019aee638ac890003351cc715912000673b90e2b224000ce6321c564480011bf06bb2a89000a3720d765512000477c12ecaa240008f7815d954480011e902bb2a89000e1fa1f655512021636390cbb1a40008ef825d763480031d904baec6900021fe1571d8d2009c3e42ae3b1a40008bf845c7634800717908b8ec6900063b20971d8d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d203c63db80cab1a4000c3f65dd16348001878cbba2c6900031dd977158d200063a32ee2b1a4000c77651c563480018e8ca38ac6900033518c7158d2009c3f43eeab1a40038be87dd1634800187eebba2c6900030f1d77458d200061fba8e8b1a4000c3c751d16348001938e9b9ac6900031b1d77258d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480018f0ebb82c6900022fe117654d2001c5e422eca9a40008ef825d953480011ef02bb2a6900023d2057654d200047dc02eca9a4000c6e521d953480050fd0fb2aa69004e1fa177650d200043ec2eeca1a400087f855d943480270f90abb286900022fe117650d200046fc1aeca1a40008f7815d943480011e902bb2869004e9ba1b6554920096363b6caa924077c6c65dcd52480831dd0c382a49010b1b1947054920216b5ba8e0a9240008ee86dd5324805d8d8cbbaa64900023b219754c9201763632aea99240009e8805d532480854dd0db2a64900031b1db654c9200072631eca9924000c6c7619532480051d90eb2264900ba9b215644c9200156641ac89924000ae4815913248001c98cbb1a64900039a197704c9200cc77430e0992400096d851c132480018d8ca38264900039a194704c9200ccf5430e09924000cea861c13248001ad50a38264900035a614704c920006b5b28e09924000cea651c132480019d0ca38264900035a194704c92000634328e099240008bf845cf614800717908b9ec29
  | 7 => 0x7c855c7624c00117d0fb22c4980030fdd764589300061e3aec8b1260008be87191624c00187eea322c4980030f1d464589300065bb26e2b126000cb464dc5624c00196ec838ac4980032d190715893000672310e2b1260038be84dd9524c00117b09bb2a4980031b14a765493000636290eca926000e2c52d91524c00317d0fb2284980029da1721d85300045f43ec8b0a6000cac72d91614c00117d0e322c2980032b1c864585303de5db80c8b0a6000caf64dc9614c001958c9b92c2980023de1d611853000572412c230a6000a7685c84614c0015ab06108c2980063ba0a765053000476c14eca0a6000cac72d91414c00156d03b2282980032bd93725053011e56326e4a0a60008bf845da214c00717908bb4429800e2fa1376485300045ec26ec90a601ec9c73d91404c035938c9b9a8098132a7a1b648c1300f64f3b6c91826003c9e76192304c001c58a53a6cb1000e2fe1d74d962000716292e9b2c4000c6c525cf658800196ce938ecb100032d5d271d962000732294e3b2c4000cb6745c7658800196ae8b8ecb100039914971d962000672412e3b2c407ae68529c365880838d8e5baacb100030fdd754592200045ec24ecaa440008f6819d954880011eb033b2a9100029b21572d8e2000636baea5b1c400087f855c763880270f90ab8ec7101e73a5ca70d8e2000636296eab1c40038be849d9538800117b093b2a7100031b14a7654e200047b40ceca9c40008f5819d953880011f5013b2a71000a1f21d6554e2000636b2ee4a9c40008f6811d943880011eb023b2871000a2f21d6450e200154e41ac8a1c4000ae582d4661880270fd0fbaac3100031d60775586200063610eeab0c4000ae582d4561880018eeea28ac3100023de1d61186200065aba2c230c40028de83dda41880011bb07bb4831000e3d61e61906200043fc2aeca0c401387c855d94188001878eab228310002ad205645062011e57326e4a0c4000c747598541880075690930a831000339dca615062001c7a43ac2a0c4000c7475585418800756908b0a831000e2fa13768c6200045ec26ed18c40028f587986318800196ae930c63100032d5d1618c6200043fc2aec98c401387c855d9318800717d083b263100022f610764c6200147a43ac298c4002ad483585318802d8dcebb2c431008eaba13658862005477c3ac310c4000a6f85586218801b1df0cb8443100031b59572942200b4b642ae51844000c3d7495365480018bae729eca900029b60a53d952000c76412e3b2a4000c3d741d365480018bae639eca901069ba0873d952000536c10e7b2a400087e8710f65480010fb0e21eca901069ba0843d952000536c1087b2a4000a6f825c765480834d904b8eca900021fa1f31d95200043ec3e63b2a4000a3e84cc7654800147b0998eca901069ba0b31d95200
  | 8 => 0x8b8ec6a0072a721171d8d4000567c12e3b1a8000acc825c7635000153b0838ec6a000297a1721d8d400052ec2e43b1a8000a5e8508363500014bb0a106c6a0002a76126218d400154f436c6a1a801cc9c76d8d435000117d0db8a86a017b2718f7150d400d45f430e0a1a804cc9c631c1435000136b0238286a014766dcc7050d4000636baea5b12800087f855c762500270f90ab8ec4a000237a1f63589400062fbaec6b128000c5c75d8d62500011bd0e31ac4a000317dd463589400062e3a8c6b128000cd763dc562500019a8c7b8ac4a000335d8c71589400066a318e2b128000ce4621c562500051bd07bb2a4a00023760f765494000636294eca928000c6c521d95250001938c7ba2a4a00039314b635494000c6f43ec69928000a7685c8761500011bd0fb1ac2a0003331cb63585400046f438c6b0a8000ccc7218d61500f99b6e031ac2a000333d8f72585400066631ee4b0a805ec9e7418c61500011ef0eb08c2a0002b920961185402f45fc3a8630a8000a7685c84615000156b08108c2a00022fa1b73505401564e31ee6a0a802aa9e86d8d4150001d18c7b9282a00034b1d4725054000746318e4a0a8000e9463d85415001f17d0e30a82a0003a5d8c61505400074a318c2a0a800fab687185415000196d0e30a82a0003a9dc8615054000752390c2a0a8000e9863dc1415001917d0c38282a00032718c70505400069dba8e0a0a8000e98631c1415000717d083b462a00ab2718d748c5400d64f3a6c718a802ac9c635d1315000137100ba262a000237e0d76885400146e41aed10a8000c9c635d221500051bd07bb242a00023760f764854001c5e432e7202801ec9c635ce405003d53d0db1c80a0073279db63901400164f3b0c72028000c9c635c6405000717b0e30c80a00032d5c4619014009c3f43eeab146000c6c521d9528c0271d90eb12a51804e9b2156254a300043fc2aeca14601387c855d9428c0011ef02bb285180023d2057650a3001c5f43ee8b0c60018ee87dc9618c0018deebb92c3180032bdd37258630006563a6e4b0c6000c6f751c9618c0018d8ea392c3180032bdd07258630006563a0e4b0c60008f787584618c00196ae8b08c31800e3d61e619063001d5a422c320c60008ef825d9418c0031d904bb28318002ad205645063001d5a424c2a0c60038f487585418c00756908b0a831817a67e1d748c63005c6fc3ac318c6000d9a749c2318c01d1bf0cb84631804e1fa1776886300043ec2eed10c600087f855d9218c0270f90abb243180022fe11764863001c5e422ec90c60028be87d91408c03d938e7b228118002aba0b71d913000556c16e3b226000cb7719c7644c00147d0b90ec8980028f61721d91300051f42841b226000a3d85083644c00153b07310c8980031b5d752d89300043fc2ae3b1260138
  | 9 => 0x64582310045ec3cc830462008bf87590608c47396ce2b20c1188023ee1d60182310065c320e0b2262018ee87dc9644c4018deebb92c8988031bdd47259131006363a8e4b226200ceb72dc1644c4019d0e5b82c8988032edd070591310066db98e0b226200ceb721c1644c4019d0e4382c8988032ea1070591310065d218e0b226200cb8431c1644c4019e302382c8988032e104705913109c7743ec4a926213a6e85d89524c4051ed0db8a849880a2fe1d64905310055c402c920a622ac9e765d2314c4015e302206c0988023ee1d60181310055c422c03026200cb5719d0604c40717f0eba0c0988032d5c574181310064fc1ae83026200c9c835d0604c40197100ba0c0988032e5d340181310063d286e0b2c427dab681dd164884011ed033b2a91080e2fe1d74d8e210065aba4e3b1c42038be841c1638840117b08382c71080e2fa127654e210045ec24eca9c42008f6819d953884011f5013b2a7108023e6027654e210143e43acaa9c42008bd849d943884274df0cb2aa5109df1b9977354a212b476c36e2a944273c6e651c1528845d8dccabaa651088e6b211754ca21004f4402ea99442028ee87d91328840559d07b22651088f2b1d1644ca2112c76c36e2994420096d85dc532884012db0a382651084e9be19529462100e36bb2a528c4200b678154a518840117f08b9cc11080e2f211739822139c7643aa4b044213c6e7554960884011f70eb00c1108030f5d254d952100c77414e1b2a42038be87dd16548401958e9b92ca908032d1d371595210061ebaea9b22421387e87dd56448401878ebba2c8908031bdd77259121006363aee4b224200c7475dc5644840117f08bb2a8908023be0976551210047bc0aecaa242018ee829c363484011db05bb2a6908022fe117654d2101c5e422eca9a42008f7815d953484011f700bb2a6908023e2017654d210143f43ecaa9a420087f855d943484270f90abb286908023be097650d210047dc02eca1a42008f8805d9434840517d0fb2286908031bd9772545210061e3aec8a0a4223cac64dc941484271df0eb2c429088eab211658852101477c3ac710a42008fb8758060484031dd05b8ac7200023b60b7158e4009c3f42ee2b14800087d85dc562900271d90eb12a52004e9b2156254a400047bc0aec99480008f4815d932900270fd0a3b265200021f614764ca400147643ac499480008be8790d619000156d0321ac3200023de1d61186400045fc3ac720c800c8bf87586419001f17f0cb8483200063ba0a768c64000476c14ed18c80028f587986319000196ae930c63200032d5d1618c6400147a43ac298c801387e859da21900010fb0b3b443200021fe1572d8d4009c3e42ae5b1a80028bc845c763500011df04b8ec6a00063b20971d8d400052fc2ae5b1a8000a5c855cb635000153f
  | 10 => 0xb128223aae84cc7625040155b0998ec4a08029ba1770d894100536c2ee1b128200a6e859c362504014db0b386c4a0802ab61070d894111d72c08e1b1282008ee8714362504011db0e286c4a08023ba1c30d894100476c3861b128200a6e850c362504014db0a186c4a088eaba1030d894100556c2061b128200ae6810c362504015cb02186c4a08031b18b75589410069a20eeab12828bc6e76d946250515e4883b28c4a08023b61e651894144d3742cca3128288ea44199462504011df0eb28c4a0a1eb9e05651894142f52208ca3128286c6e76194625050be4882328c4a0a178b10c651894142f33a08ca3128285e2c41194625050bcc882328c4a0a1789104651894142f17a00ca3128284ea441d8c62504011db0f318c4a08029ba16631894100536c2cc63128200aad8498c62505075cb03318c4a08023be1d631894100537c2ac63128200a6c8558c6250505d4882b18c4a0802bae01631894100574402c63128200aae8690c6250401c58cb218c4a0802e9a0643189410065a20eeca928200c6c529d952504018d8a43b2a4a08032d104765494109c7743ec4a928213a6e85d8952504270fd0bbb264a08021f617764c9410061e32ee899282009b681dd132504051dd0fb1264a088f2b1d3624c94101c7b436e29928200c7465dc5325040736d09b8a64a08031d194714c94101cda420e29928200ce7621c5325040717b0fb1c82a08ab279cf639054111ed338ec520a8200e2c6518a41504c1b4ce231482a0802ae61030d814100578c0861b028200da4415ca60504018dcebb14c0a08031b5d76298141006373a8c53028200c6d7518a6050503d4882314c0a080365107735814114c76436e4b028200da441dc960504011dd0fb12c0a08031bdd76258141006363aec4b028200ccf73d896050401998e7b12c0a08023ba1c625814100637ba8c4b028200c6c75189605040199ee6312c0a0803331cc625814140e73b88c4b028276ea44118860504011f70eb00c0a0802b620d60181410045ec3c863028203cb57190c60504010ff0ab90c0a084e1f215721814101c5ec3c823028200ab9809046050501d3086180c0a0802a760c62992313fd5b40ee8b246200a3f855c9648c4014790ab92c9188aaad20572592310051f42e42b246200a3d85c85648c40155d05382c918802ab60a70592311555b40ce0b246200a9f835c1648c47356d02382c9188a2ad60470592310051f42840b246200a3d85081648c40156d02102c918802ad60420592310045ec3cc9b1462008bf87593628c4fd96ce2b26c51880e2fa107654a310045ec20eca946200e2c52591528c4010ff0abb2851884e1f2157650a3100c5e43ac8a146200cb564dc5428c4051eb0c38a85188032d5907150a311564f39ac920c6223cae64dc9418c40195ac9b92831897b271ce
  | 11 => 0x5092187eebba2caa10032ddd0715954200673b90e2b2a840087f855c763508270f90ab8ec6a1002b960b51d85420047bc3ac230a8400a7485584615091f5cf04b08c2a1002b960b51185420055ac20a230a840087f855c061508270f90ab80c2a100237e0d70185420146e41ae030a84008fb8758060508010ff0ab88c0a104e1f21571181420063d282e1b2a6400c78651c1654c801ad0a4382ca9900e2fa1f745953200716296e8b2a6400e2c521d1654c91d8beebb9aca992379314b73595322453742ee4b2a6400cb774dc5654c801968e9b8aca990039914b715953200673416e2b2a6400cb7741c5654c801968e838aca990039914871595320065dba6e0b2a6400cb874dc1654c801cd0a5b82ca990033cdc770595320067838ee0b2a6400c6c521c1654c801976e8382ca990032e1d0705953200675b90e0b2a6400e68521c1654c8019e6e2382ca990033c1c4705953200675410e0b2a6400c7a521c1654c8019d0a4382ca990031a148705953200674108e0b2a6400c3d75d53644c80117f08bb2a8990023de0576551320047a40aecaa264008fb805d9544c8011f100bb2a89900a3ba1b725513200636b94ebb0a641387f875d7614c8018dae4baec2990031de0575d85320063610aebb0a6400ae582d47614c8018eaea28ec2990032d5d361985320047bc3ac230a6400ae582d44614c8015ab06288c2990021fe15701853209c3e42ae030a64008bf845c0614c80717908b80c29900e2fa1271d81320045ec24e3b026400c7975d43604c8015b307a86c099002ba60850d81320047dc3ac03026400a7885580604c8018dae53a8c0990031b149751813209c3fc3aea3026400c6d725d4604c8018df04ba8c0990031b20975181320063610aea3026400c78805d4604c8018de40ba8c0990023b61f521813200636baea43026400c7975d40604c801cd6a5a80c099002ba608501813246734290a030264268bd86dc5439040117b0c38287208026d6047050e410146f418eca9482008dd831d952904031b90eb1a652080e3d618714ca412645e43a86b0482008fb8758060904010ff0ab96c6a084e1f21572d8d410145f424e1b1a82018ee829c363504011db05386c6a0803691077258d41006d820ee0b1a8200cd8631c16350401b6082382c6a08029ba1732d894100536c2e65b12821387e859c362504010fb0b386c4a0a2fc910765d89410053742cc7b128200a6d8598f62504014df0ab1ec4a08029b21563d894100575c02c7b128200ae88058f625040174d0321ec4a08031bdd675d894100556c26e7b128223ae581dcf62504014dd0a39ec4a08029b61473d89410047743ca7b1282008ed8794f6250401c9ea729ec4a088e3ba1f51d894100476c3ea3b1282238ee87cc762504011db0f98ec4a08029ba1731d894100536c2e63
  | 12 => 0x500000180000180080000080500080280600000000180000000080000000000380000000000000000080200480300000100000000000000000080300200000180000100280000780100000180500000000200080000580580000080000000500000080a80580000900000180280000080180000100200200400000000080180480000180380000080080f00380300000100200100000180180100081180000080000080080180300080000000000200080000000000000280380200000700080000000080080000000180080000080380000d00980080000100200000080080000000100600180b00280180000200000080000000080580300200380000480180080380280000100000700080100700000080180180000000200180000600280000000080300000100000500200100000200280080000280180080000000000000800100080000080000280080180500000180300180100380000280000200600100000880000000400100100000000200080000000000a0028000000008000000000008000010050008000008010028028008028018000038000038028028028000010008000000030018078008008000000000028000008020088108000008000000050020000020008000008018028018010008058000038000020010000040058018000000048000098000068008000008068008010000040000018010010000000068018010000000008000000028000021fe1571d894309c3e42ae3b128696cb574d866150c011ef0eb08c2a18023ee1d60181434ad5dc22c03028694adb835806050c0196ae9388c0a18023be09711814300c76412e23028600cb4415c46050c0196ae8b88c0a18032de1171181430065a422e23028600cd7835c46050c019a906b88c0a18032d90d71181430065a21ae23028600ce7825c46050c019c904b88c0a18032dd0171181430047b40ce1b22a4008f5819c36454801ac8a5b8ac8a90032d1907159152006b2290e2b22a4008bf845c7635480717908b8ec6a900e2fa1270d8d520045ec24e1b1aa400c6c529c363548011ed03386c6a90023d60670d8d5200696296e8b1aa400d6452dc56354801ac8a438ac6a90035a14b7058d52006b4290e0b1aa4008bf845cf615480717908b9ec2a90029d61741d85520053ac2e63b0aa400ab684cc7615480717d09386c2a90022f61270d855200696296e8b0aa4008f787584615480156908b08c2a90032d5d041185520055b4266230aa400ae582cc461548019aae6188c2a9002ba60830d815200696292e9302a400d64529c66054801ac8a4b8cc0a90023ee1d601815249d75c12c0302a4008bf845cc605480717908b98c0a90031b14973181520045fc22e2302a4038bc845c46054925cd0a5980c0a92479a14830181520063d282e1b2a8400c74651c565
  | 13 => 0xca521d120000c50000000000e2000224b71256d5004226920c2b300033f4d92d23270000825de4466936908004922ab610000000278ccf1f400037540f0000005091cf2ec0000000005cb3740000005a00000000000003b95f769000014c16c4075ee59e4064d31f80003f354a0000590000000944b90f764c29515c0000914700005f029853b5116860060004f51cb0864293450960001c40f80001895aa38c00000035e00043d0000000300004fc0000000000004ef00038326600000000000000023edbfc8c585a370cbe4926a01d1b544280000019162e5eb4652610006256750006b75494c81985740ab65411800045fdb15733eb3864df42559220322732e5b457620a5ff62f3020000000000000000000003064ab0c6df309900030f00029663300011d4b6d2d65d17c1e00006322f70a84bd00023f8001a40003aa32b0000000005330002fe0000001a022020906c4620172ea3a83948265793355c768b92100003303c5ef0000000e600000000000000000055b00000054563c09b00c06e170ec1611178e4d64200036300000057d2440000720000000004b4bf910023d8004ff3f210c94204b00000000043a0000003c44a0d169c2000000609d753e90000000000004a55d20aa3be5531ff9ec16f80017120480058f31107302e2243f70005e50006120fe164a2fadd0000650f52fd377106a258000003ec55600000042c3b80004b107a3d14ea6ba67f94b62963a0000003500000000000541fe9d100000017219b1609320006a065300012b4f063700000000038b00280300000000180000780180100000100100080380100000000080180e80000200000100000000000180100200780300000200080000100400180080200000080000000100880580300480180100300180080080300300080080280000600000080180580080780000000180000600180180400280000000100000000380080080080000100080180000180000000000e80180400000100000400000100c00000000000000080000180080a00680080000180200080000100100080080000180100000000080000480200100000180000080280000000080000000080500500080180080080500100000480180080000180480280300400280080100080080000200280000000200080000300000000200f803000002800003000001000001000000000801801002003000800802001000804800806000002000004800004007800001000000001800000801001000801000000005000001007004000000801001801000000000000004000801000800002000000802001800801000000802800007800000800002001002800001001001000000000002800000000000000003000000000803800005002001801001800000000000801006800801800800800801800002
  | 14 => 0x34743900054b4874970000000000bf00046b095cbf0000006884270002a545635d3001a500019f00000000000018a66380009e3c52da3980000002433c33cf00011458a00000021300000060900005b1bc5fb00033100000000000000006f0000000000000b40001da48300000063e69e3bf471b4b0245b30002a60003e000024e5c8b5cb374408002410000002318004242290390006302c800054e40d4db4081581432d50002ba0000004154b3e510005852025290002ca00000000066e4a407b1b149b2cf29d0a48005954760870000001359aa5f600000000000004d80005600024b00000006280000000000011a0000005b000000056c00023226000008f4d84cc0000006bf00040361c09a0001b726f00000014e0000000003e10000006910004360000004020000a900000000000000024900065f00053f0002208005470572c4000255b0833a0b05675190194e233c2403fc0000520000002e41936061fd00000000010b3903bd0001266380000b10000003c112e8d800000037a181de10004d10000004d20002106780005d40000361ee00024500000000000000000000009c8000005df4cd3440003760003580005206a84780000001808510003845150006220000000002ac20ad4130d00029404e0001826c300000000000027a0000000000000000002aa339000218000000000000000694265cf658d2784535c620e00049e08a0000000001640000004710000004e0493209b511833174ba02b6553360002752a300000012c3031620108000000000980000003d85bf10a00056937293e02341325c0dd00000040518568a43c0e000031d00056256003a47c0893dd0000000180000006a500021e4310003ab0004f800000000065b00100028531c31e0000002cb0002b14896b280013a561e920f31354c40854e53ee0a400027211c0000314dc4ae3570000000000003280000000000000f78000004d413941600025a1e12f36a40003340001301470004421898f880000000000000000051400000000024bd400001de0140006a700000052c8001f300000041e29f0000000fa95d3ae00000000064625f3f10003ad00009f00000064514868c000197b7d46d2155510001a200066d42f035557a49d6287848e15e00034840a1770000000003b26448000001810000000ee35654337000052500032d02700069c44c0000000002224b444f00043480000034268e49f000199000000198cad0000002870005a30000a20003380000001838000600e81805241284375a90000e36140ec0005ce0000005060000836595ca0000000000000005f40000003d600000000060a47281e35300022f0000000000000000002a80000003af00065000000000000000000000000000020b4fd8000000cd00000065e00030e0000100000000000003dc3
  | 15 => 0x4c05d03a538044b1220000b95078000006956350220000001eb0002520028000000004efc3b42b00000061703d1c956b3ac000474003a0500000001a2f40000000a700000e5270630d535b1c100000000050432600055e57e5dab4f2d90700006396a10000001094323161cd0131968004966433ea0dc5550d431f0001ce1af47300000042645500026200012400055dc8800016000018e0ef26687f00000057100004f0002ed0003228000006ae0000005280000000000002cd52a0000001020001460db2d664fbb615b1ca0d33fb27b0da58e00000021600007948222d1be5680ca0ed381000141187d3950e0000e5000028e6a26736e21c0001fc0000002dc00000055200000000000025300028da830000000000002113d755e8005c937e43417a1e5145176de823349d20d23ba0f6526b52c268453139b00045f477024e8f6a600000019cb640000000006261c80001b36b9038285bf460d0004636c42fc00039c0001588000f006b3a0202af200000000000000000000022180043800006d4172e660c500dfe59981200a0003b01c734d2300001d34388001d00001ba0b800019e0004c35da4ee2df0f41c63252764ca0d945024a67a248c9905a00000046700000000000060f19c6bb2730000663945460000093690000000025dd54200029a28947b0484e15821cc62700000050d00051d0001d62a94ce4662a400039e00056d0000000000000000006528c28001785bc37852600055c247c5943b80026c00000000000054d68b36736f0af0005030001f92b90000006690006180006760003e20006363e40000002848002700000000000005f100000048400031b00000010e3930000000000432e900010141404c47c82550c4b32916b82844a71120000d71904526a964813b4404443233a20005db5081a757811e1946b1d5400062a000000572533ac62713c82c100061f0000e740e0281170001b856e00015764700008b00000000000000067d000000290e3b00015a4810cc4da0000000000004c11ed4d500000021d0000001760000000000004d70000001732fa0000000004e74642540000a00000001a3bb50004ed1d22e041a44e49c2b20006851d84fd00000001b0000001d71e602a1340000004b000016a4b86ad00000000000000000000012a0002355842d70004af15600b00000000060400069839d41f8005d36b2485ae800053000039aca01a85894a22a72748003d30042174c20000000000001db6b42cc67f5bb23c3d952b0373a92b422a00016e0002ad0a3a4622e0000035f50000b300000033d2b000000030959660865c00010d0000001ac51f0002c52653ef4723c218c43e9dd4866aa13d5323976c20c24e63922d00000000003e553d00000048b2042c727c2e31ad00055f0000ae5a162000000000031a62800000000
  | 16 => 0x55760b1ef3e741c22ecf708e4124901a10751b93652ce0003895050004692408000476bc8000000005830000000005940000002d32de3660bd5cc6b000041f00062c30100000059e80000000000060000067400038238d1795f24610000005590005e200007e9c03a61e30e16805163f031900000000000009480000000033e0003b300000048f48000029c80000006449f8000000840003045cbb1507e137e6400039a41962ae4e53c0005900000003cc0a68c456a0bc8fb6162790b60742120003964c71c300026e8003db68d43300009baee2f62364430fc1e95d700043797d011de45c82ef5865132a10838930e41a6657e133bb0005ec1dc6772b4dc41165019a36736635e36ac0a780025b27f47a3cb5933554f957a013b5201f5e068700022c40916600000000034100034a1740000000621e22d83a70e90610002b72e20002bc00000000004d00000028600032f00050209d4453c00002bb04963f0000000005b20003210954fb0004c63cd0005c10000f68000000002813133d00bc57c55800009c4aa00042e00046c39f1e400040103f232ce41756a22a22085a69ea93818b80052e0d63a15a665a0004285a52e70c100011512f00000041147d00044900000000000000067c37c00031800021a00000000062100000000000050f00052140000035a80000000029c3c720f80000000000001500045d00fcdecf400000000047bd442f012880013c14f10500000025d80000000033b00069d37200066b42d0000000001bb0000ad4583ff64a2fa8005ad26e23466119d00000000055a291d382580128004b63200000000214040df0004bc4a959a0ac00ed9146e58049842223d1372b0abd2ae13f09235f17b0006686155648d5ce90ce0006795810f10a603e35c62d4c95c7b6200022b04653414902045733000040c0000000000000690002075fc3ba0110000005b70000000003ce0000004fa3c95d533245e5f900030b2bf25e8002255d60000000000c859800038f19516b61680029369b5870000002a00001f22e099a18461d6831ea00053a00041d0005ab2798000000d38000000eb0000dac3f28c80000000000000000027d0002728000000006ab6a35dc1962e118634000000000012e3b700000000053744724f59b92923b0f61e75650d7cb712515f6078004a61d42011328002d118d2511874752b1ded06728037b6600685ac18b0973b445a0810c90000000ff12d48543d8000000000000000000005d80005c20000fd00064b00023e5fd00026400000004a80000000028f050435385420000404e7b6021083f84be0000003610000000000000002be4789c500000000f0000000000000000000000004a35be00056115332906a50a4de00036800000049a45419a80032a02d58b1672885ba00000060300000000023f000535
  | 17 => 0x264eb600000000057746f65801657032cb5a1200c31df0004fe0000000000000000002c96340cb1521d50000000000000006bbce800002c2973540002820000001884f351e00056300002f5ea6c00005c51f1084eb3297934da8ab50320000003075d953e0002770000882f900000001c0002230000000002b60772920005d14c50000000000001695cd0000002481f60410000d22740000002064ac08034c0006662f81510002260003df66f0005ae2194d00000000000000004ec00000005f0000000000000001440000000000000003da0000000000002553bc00000056400024751c1704f100000000000000000000064139910f607515ebc0900003792383fd04410c495111bd46050bb0000001190003220000002eb0004e5e240000002d4089cd612339f8a12685a713349400d16f16d5185e9172aff3de00065636c44d41b606d1b00030e8f904a1b60005cf692c413430c03490000000000000000000000000be2500000000000000000000000000002c30002db00000023900028d00025e20025654800000000000062b00029b0000000003120000004bb2678000ea61e00838800000000064f6890004180000004a10000005a83a30000b552f2fb00044a0004dd1d96b160125728c69963d50b27e6723d22c01b026d15055d51a4b559b58c0d141023a66c61a0c65e08004216811923875995a085c0001546406bd0005102e553617f40b08d10312c85e46800028a0000005a400000052c0a580000000500000000069f000155436e1b24c47e5af3e85fa45b1bf22100056f273a96ca844823159c5c000036032c0000003734793a44912af04559f00000000000000000014a6823e365380000000012743e0006713f600003b00038a5c32280c74e32990006440405bd0cf00021b0006190000002630002e48d0657000000615800000277d849ff0ba1b438e00032400036d50100007c36b00003410400062325d10611b1610a291100059d2abc6a26b11024248d5970000f21e80000000000000c4bed0006971f70000000005001fe1ae00000018f05547ae312388000290003051f00000710003c654c3f500029e57f05d43037f14d5b85883b16672718b746047f0e4a901590004b208a87d39130c24d6af0000535b9000000000000000517460c778006be00000000000018d85854f00060e1bd1400000001f54dfe625a3a8e1630004cb1749a900069a000665000000000000000000168239e700a300000007f80010700000029d8000003330000000de000000451000211d7b00011f48a0004e4bfa4b08004b88070000000005225b6184a140004eb0000000006963fe3e600000017e1fb1b208c0004f23593d500000042a34626fa3acf0db50a500000031413600000000045c00030a6519130000000b20000000765661fa28b0000
  | 18 => 0x5a200067e1650fa2f52f100000051893142336a5230005072595e73952769ab0001970005f834e00021f5e62b831
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xca5535d10070c870000306b4580cc3703e87a420a1aa32810ab926a80160c00d00008403b0000000010001c3c000000000000004601d10053807cf002f122c000004583f6ccd0000901ea662b549f14ac9050eb8002006c1c0030000000001c48620040061c7010700049090052c640435c46050c014669614871591520041b660529c3635480142e9614b7458d5200519a58521c5635480146a9614b7058d520050ba5c52dd1654c801466971487159532007091d0521c5654c80146a9714b70595320051a640521c1654c801c2b7414870595320070a1d0521c1654c801c6052dc4705953200718148711c1654c80146b9814870595320051a660521c1654c80146a9114870595320051a254211c1654c8014699008575181320051a65f52d40604c801a24412156318941006a81048058c6250401a2465a06431894100709148411d9525050bc26711946290541007091067518a605040186a65201754ca210062518d811c1435000106d9814a7654940007031d4631c94150001c24751c8615054028e25604631c14150001c1b7518c70505400062618c805d1315000106d981487654a300041b660529d9524c00142d9714a74d96200050b65c525d365880014659714a71d9620007099d0529c765880014659714971d96200061a9c0855cb638800186852a027654e200041be6165dc9538808306c9859572942200061a194805d5324800106d98194704c9200051ae60651c1324800146998194704c9202161a1d880549504811986a8019773881200041b66052dd952c400106e981497654b100046c65c8050e41c410bc24641d472507100051a640521d9524410bc24641d472505100062561c6319231440014a597190628c510007215d06318a31440019907320141501100052925d641c91004001c85641cc7244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x81a2a1900857518132
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x4b
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x124b
  | 11 => 0x124c
  | 12 => 0x124d
  | 13 => 0x138b
  | 14 => 0x138c
  | 15 => 0x138d
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x6
  | 20 => 0x128c
  | 21 => 0x128d
  | 22 => 0x128e
  | 23 => 0x9cb
  | 24 => 0x9cd
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0xa0b
  | 28 => 0xa0c
  | 29 => 0x130b
  | 30 => 0x130c
  | 31 => 0xb0c
  | 32 => 0xb0d
  | 33 => 0xb0e
  | 34 => 0x140c
  | 35 => 0x140d
  | 36 => 0x140e
  | 37 => 0xb4b
  | 38 => 0xb4d
  | 39 => 0x144b
  | 40 => 0x144d
  | 41 => 0xb8b
  | 42 => 0xb8c
  | 43 => 0x148b
  | 44 => 0x148c
  | 45 => 0xccd
  | 46 => 0xcce
  | 47 => 0xd0c
  | 48 => 0xd0e
  | 49 => 0xd4c
  | 50 => 0xd4d
  | 51 => 0xe8b
  | 52 => 0x4e
  | 53 => 0x94e
  | 54 => 0xb8954
  | 55 => 0x124e
  | 56 => 0x138e
  | 57 => 0xb9394
  | 58 => 0x9ce
  | 59 => 0x12ce
  | 60 => 0xcb
  | 61 => 0xa0e
  | 62 => 0x130e
  | 63 => 0x10b
  | 64 => 0xa4b
  | 65 => 0x134b
  | 66 => 0x14b
  | 67 => 0xb4e
  | 68 => 0x144e
  | 69 => 0xb8e
  | 70 => 0x148e
  | 71 => 0xe8e
  | 72 => 0xecb
  | 73 => 0x168b
  | 74 => 0x180b
  | 75 => 0x198b
  | 76 => 0x10c
  | 77 => 0x150c
  | 78 => 0x180c
  | 79 => 0x8c
  | 80 => 0x150d
  | 81 => 0xcd
  | 82 => 0x168d
  | 83 => 0x8d
  | 84 => 0x24b
  | 85 => 0x28b
  | 86 => 0xbcb
  | 87 => 0x2cb
  | 88 => 0x16cb
  | 89 => 0x184b
  | 90 => 0x19cb
  | 91 => 0x14cb
  | 92 => 0x28c
  | 93 => 0x154c
  | 94 => 0x184c
  | 95 => 0x20c
  | 96 => 0x20d
  | 97 => 0x154d
  | 98 => 0x16cd
  | 99 => 0x24d
  | 100 => 0x18cb
  | 101 => 0x178b
  | 102 => 0x188c
  | 103 => 0x160c
  | 104 => 0x1a4b
  | 105 => 0x1a0c
  | 106 => 0x17cb
  | 107 => 0x164c
  | 108 => 0x170d
  | 109 => 0x15cd
  | 110 => 0x104b
  | 111 => 0x1a8b
  | 112 => 0x1a0d
  | 113 => 0x194b
  | 114 => 0x164d
  | 115 => 0x8e
  | 116 => 0x154e
  | 117 => 0x94b94
  | 118 => 0x20055
  | 119 => 0x15ce
  | 120 => 0x15693
  | 121 => 0x8994
  | 122 => 0x15353
  | 123 => 0x11394
  | 124 => 0xd395
  | 125 => 0xb8293
  | 126 => 0xb8214
  | 127 => 0xb8294
  | 128 => 0xc055
  | 129 => 0x21255
  | 130 => 0xb4215
  | 131 => 0x20b55
  | 132 => 0x144215
  | 133 => 0x2c215
  | 134 => 0x2d415
  | 135 => 0x219d5
  | 136 => 0x19c215
  | 137 => 0x202d5
  | 138 => 0x14c215
  | 139 => 0x14d415
  | 140 => 0x140d3
  | 141 => 0x1a4ed3
  | 142 => 0x1a57d3
  | 143 => 0x21415
  | 144 => 0x1a9953
  | 145 => 0xc153
  | 146 => 0x168153
  | 147 => 0x9296
  | 148 => 0xd2d5
  | 149 => 0x11314
  | 150 => 0x184b94
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 1407
  | 6 => 4424
  | 5 => 1733
  | 4 => 64
  | 3 => 1
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
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (59175+((h/593+packedAt gbK7 (52059+(h % 593)*12) 12) % 2135)*12) 12
  | 6 => packedAt gbK6 (234621+((h/1713+packedAt gbK6 (212352+(h % 1713)*13) 13) % 6170)*14) 14
  | 5 => packedAt gbK5 (110119+((h/656+packedAt gbK5 (102247+(h % 656)*12) 12) % 3142)*12) 12
  | 4 => packedAt gbK4 (4641+((h/23+packedAt gbK4 (4480+(h % 23)*7) 7) % 100)*7) 7
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1ffc07ff003fffffffffffff447f1f8e31ffff
  | 1 => 0xfffff81fffc0fc03e03f007fbb98e4ffde6267
  | 2 => 0xe03fffe00000ffffffc0007fc3e0f8f1e07f87
  | 3 => 0x3fffffffff0003ffffff80fc00ff01ff83f8
  | 4 => 0x3ffffffffffffc00000000ffff0001fffc00
  | 5 => 0xffc000000000000000000000fffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x54800a504092d2468515351002b098610acab
  | 1 => 0xb99c580b6d485461a23a053a1998643ad66265
  | 2 => 0xc436ad6019109bcade880a6cc2e0b8d1e05786
  | 3 => 0x88273652b1b20083172cac08ec00f6016b0350
  | 4 => 0x113bc79cde3ce2f004103030f7dd0001bdf800
  | 5 => 0x1e020400e02003001820c040ff76dfec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36653
namespace PEqualNP.Outside.L_meta_36653
open PEqualNP.Outside.L_meta_36653.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_2_0 : Interval s3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 5 := bs3_2_0
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
theorem bs3_4_64 : Interval s3Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 91 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
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
theorem bs4_3_0 : Interval s4Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 24 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 117 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 64 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1728 : Interval gbAtlas 5 1728 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1733 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)))) (concat (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728))))))
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
theorem bgb_6_4416 : Interval gbAtlas 6 4416 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4424 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))) (concat (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896)) (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))))) (concat (concat (concat (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312))) (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)))) (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))))))) (concat (concat (concat (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)) (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))))) (concat (concat (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)))) (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)))))) (concat (concat (concat (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424)) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552))) (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680)) (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840))))) (concat (concat (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))) (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 bgb_6_4256)) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416))))))))
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
theorem bgb_7_1376 : Interval gbAtlas 7 1376 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1407 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))) (concat (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 2 zero, 34, 38),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80eeeaeac8eea0aa80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 4003506816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36653.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[2,5]⟩,⟨.or,[2,6]⟩,⟨.or,[1,4]⟩,⟨.and,[1,8]⟩,⟨.and,[7,9]⟩,⟨.or,[5,6]⟩,⟨.and,[10,12]⟩,⟨.or,[3,11]⟩,⟨.or,[0,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4003506816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4003506816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36653

open PEqualNP.Outside.L_meta_36653 in
theorem PEqualNP.Outside.L_meta_36653 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4003506816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4003506816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
