import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40059.Model
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


end PEqualNP.Outside.L_meta_40059.Model

namespace PEqualNP.Outside.L_meta_40059
open PEqualNP.Outside.L_meta_40059.Model
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

def SBf (j : Nat) : Nat := [8, 6, 7, 5, 5, 6].getD j 0

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

end PEqualNP.Outside.L_meta_40059

namespace PEqualNP.Outside.L_meta_40059
open PEqualNP.Outside.L_meta_40059.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x4a402412000061c7c88100011030068023003040a167891c425c7804e154002a74226301c019004d01400012901a6cb0400808a21c6105481ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x281bd42502fea2a07dd4540bba8a817c51503e8a2a05d14540df20a81bc41503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4206f90840de210817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc2fca5985f54b30bf28e617d51cc37c83986f10730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61be418c3788318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2987dd4530bba8a617c514c3e8a2985d14530df20a61bc414c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830bea9061de320c3b864185f94430bea8861be410c3788218778c430ee188617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c82fca3905f54720df20e41bc41c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ef32883d865105f94620bea8c41be418837883107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837c82906f10520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ef32083d864105f94420bea8841be410837882107b88420f6108417e50083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c437c83886f10710fd98621f830c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f7418437c83086f10610fa20c21b441843ee63087d0c610fb90c21f421842fca1087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53443bea68857d4d10bf29a217d53442f8a6887714d10ae29a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221be414437882887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be290217e51043ee82086f90410de20821f4410436882087dcc410fa18821f721043e842085f94010fd98021f830043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf504caf8a0995fd5032bf2a0657d540caf8a8195f94c32ef21865dd430cafca4197b90832f6a1065df320cbdc6419774c832f699065cd320cafca2195f54432bf280657d500cafca7a0df54f41bf296837d52d06fca1a0df54341beaa4837e53906faa720efd0e41df21c83bd43907788720df94a41bea9483bf429077c8520ef50a41de214837e519077e8320fdd0641bf284837d509077ea720ef94e41dea9c83bc539077ea520ef94a41dea9483bc529077e6520ef8ca41de99483bc329067ca320efd4241df28483bd5090778a120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef90c41dea1883bc43106fca420df54841dfa1083be421077a8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020efd4c41df29883bd5310778a620efd4841df29083bd5210778a420efcc841df19083bd32107786420ef944419f28883b6511077ea020ef94041dea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598df54b31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c77c8318ef10631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa9263ef524c6dea498df14931f6292636c524c77c8298ef10531fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c77c8218ef10431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877c8390ef10721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e518877c8310ef10621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21df20a43bc41487ee4290fb88521bfa8243fb50486f6a090df14121fc282437850486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f6190437e510877c8210ef10421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740df20e81bc41d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a07bd4940b7a92817c52503d8a4a05b14940dfa1
  | 2 => 0x80002583184e382491208682a4604000002a0b6cf78003fe0000000054e05d0ca0d3321e80014900042c001b92643dcb8aa2410b50501680ea000000000008a4001870000010b94c000000000ef270874002311a0000ef19c000444001bf5025b9470000005913714400044855000514000002a50000004b8000e85d40000000000000000460024c1800000acc000000000000011416c220ada2f000000001a72366bc0002e00000000207550578c70260dc0014e8000003c4000001aa7cce62b645a0000006a584410000000005983e8001b68f8001d80002280004f0003804a8001ac00000000000188000004d26b89b2b15067f56d07620e0000000031693c0017a0000000023700000000000000af96f0320007a0128fb000000000000002315a2d725665471000000a680000007c00086851096001292b00009205109c1560000001c0f67ec309a2342034b080014c00000000000938a2acf10692c690495823cc2824044a87cbc18917c828968a80604d06b9f202c000519ce000000eb1370000000010812278100a0e00070090000000324078003018001c08468810218000218408e01210200e00e00400008410009e00608211018230000020600010000400041870000211220a00a78238008008090200208000018000408820008018021a10011628000820c18600808409a00059e10000600008400008018428828410810088008400002308268000808410000008200000208880001230a40058008260008200eb8238200268400c20011c00012200a41808430410218010418c0101821001802061062000004084017e52d0fdca5a1db94b43bea9687ed52d0edaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0bbca7a15794f42bea9e85dd53d0abaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665ee42ccbda85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32ef21c65dd438cafca51977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265ef324cbbc64995fd4532be28a657
  | 3 => 0x1a81ea0000000018888c70abb4989f4639f02ee9f0851b13483e8a38732d8000f8800000a8d5607f0000001b0000004b0f48003887e5089be36c575139e23528000999e4943682180027a21ca78003ba1a5551ac0006e80000039400000000000000051f848600000000090a4400000000944fa80000000000000000104001653044991113f314a1026a5c16a97490a124e60000f11a3783b0f3a57132000538de000000001ec58800000000542000a08000000012a0e3276000260000000000023b0581e4002c9000000000ad000001390b3000001230b9000001048003860000028b10263c000003e8000b3a24218814000004708095fa440006b44f1280000004da1b3f86c8d500007e05400000000880971b353e001300001ca3fce38000000000016a000000cea644d63f49129b442000d1acc000000730004a0770ff0373c84a85916b00a000002ca19e0000016930c57c77000000000002d20003a4000000348ac000b7000224470b00009f8000000222e8e5a5500026000000000558cc028202000001251b8001672744e26110c0a100084ca429710c0006417c0000015c19003676524aa44069789f0005aa0000015451e000da9ab00034cdc00007a474de85f1040516c10532e97c002870000016c80056e3d90609d0001640025b2da7856b29534a0000011c0321f14f1620c84c0000000000013d80000000000172000000600002ae00163000000580671d10d68a02313c14a0000006d00000000000000b14000ed0006ecb7a150060cce415100e268ae1d00000011a8002327dc0006c55ca500008d51a43cad0000009d9460c53d60180900147242400000000a001480058e040000000000007212901000049800454328002750009a023a935a2999430001080000000047823cc69403842f00000013e5ec0025900044000071000518001db4b4000000000000006a2340000013d19a0001f9658a4000000250cb33677d0a00045c150738000b674d6e247000000cb00057808c1e26d000000978001d4000e785a0000001a80047400001000000000000000001740020400082c6081f4fe0000000006800022866000408f6acd0000e0560000000885f94d000001410003aa001162af49a19c5797900046000192524748001034eeb4caaa1e3a8000bb1b00c01c08b26300044c000000000000029c1f2000000bb0002140005e0000000000019a000e29313f447c000270002f4002ad0003a00000048a5380022640c0ec2b185000859530fc000000000550000000002000000075ac3556960000000000015d07800058d4c000152000001e3048374000001000000012720c7a8000c31849a8c99e60548f4b981d07437c689591689b0802a90000008f000000000002422e8000a12100004e81c800000000000000002e0459332fc000b82c
  | 4 => 0x9bc32ac000067ce490e4f2ac86600000000000000000988000004f03e0000044a6a14058003dc698c60002fe794000001281dc001394ac768002b50000000000046600000072000000c8a650000000000039a00016a8843436029add18c6211f842000248ac06f0a400144953572001380b101c000ca0ae3400bd4c94336800091a6700083c00000000000be8d90ae0002e0fe3ae8d8002bd0006000000026ab40780005201113080c22a3c800000000000a50001200851902b0621600000038c0014b2a00300000014b22e1000021c1e86dcfb
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4534831f5414d20c7150534823e64d45208f593514833754d4520cd153514835753d4520d514f514833664d4520cd59351483375414520cd15051483575314520d514c51483376414520cd190514823e65905208f196414831f5390520c714e41483375190520cd146414823e65105208f194414831f5310520c714c41483375110520cd144414837051c8120cb152204834c5388120d9146204823d65950208f986540832c62550208f185540823e64150208f993530823d64d4c208f990530823d6414c209d98453082756114c20cb55342082ce63d08209b59442082ae64cc820cb553320826d650c820cb550320834d530c8208fd91510823c645442097d8d510825c63544208fd96410823d65904208fd94410823d65104209bd9520082ac6448020b318d20082e461480209ed9520082f061480209798f54c425d63d53109b98b54c426d62d53108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b10cdd85548423e64d4e108f593538426e62d4e109b58b538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f59052843355410610ad59441843356510610ad99331842b664c86108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544427761551108f994544423e61151108f184544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534427b6054d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524427b60549109b994524432f5414910cb150524434f5314910d314c524423e6590510c7d4e414431c5390510cbd4a414432c52905108f994414431f5310510c714c414432f5210510cb148414435853c4110da14b10443345484110d514e104436452841109798c540425d63150109b988540426d62150108fd91530423c6454c109bd89530426c6254c108f990530423d6414c109b988530426d6214c108fd91520423c645481097d8d520425c63548108f990520423d64148109798c520425d6314810ad98641042756510410bc58041043366510410cd59441043b26010410ec58041042b664cc4109d59431042b664c84109d594210423e64940108f59250043344194010ec1073004279650c010ec10430043d0310c010ec10720042796508010ec10420043e021080109e59610043b041840109dd9510042b46444010b518d10042e462440109ed9510042d86344010ba18910043b24144010
  | 1 => 0x863e64948218f592520866d650c821d354c32086e5610c8219bd9521086cc6348421e910521086e860484219dd9521086f060484218fd91500863c645402197d8d500865c6354021ab58b43d029d63d0b40cd94441d033551107409bd89539026c6254e4097d8d529025c6354a40cd946419023e65d0d40c714f43502ad62d0d40c714d435034f53d4940d314f525034f5314940d314c525032f4314940cb50c525023e65d0940a758f425031c53d0940cb14b425031c5350940cb149425035753d4540d514f515036752d4540d914b51503575314540d514c51503675214540d914851503376414540cdd0c51503354314540cdd0851503354214540c7d4e415031c5390540cbd4a415032c5290540cd146415031f5310540c714c415032f5210540cb14841503375110540c714e405032c5290140cd146405023d6590c408f596421033651104408fd95401029c6350040ab18940102b461500409ed95401026e62d53309b58b54cc27661d53309d58754cc23e6494b308f59252cc23f64547308f19151cc3365110730cd54441cc26e62152309b588548c2ce62d0e308fd91528c23c6454a30a7992328c23f64546308f191518c23e61d51308f992544c26e62951309b58a544c27661951309d586544c25f63551309bd89544c26c62551309dd85544c27461551308f994544c23e6115130cbd53524c32c54d4930cbd50524c32c54149308f993514c23d64d4530cdd53514c33454d4530d9d4b514c36452d4530cd993514c33564d4530cdd50514c3345414530d9d48514c3645214530cdd90514c33464145308f996414c23c6590530cbd4a414c32c5290530cdd46414c33451905308f994414c23c6510530cbd48414c32c5210530cdd44414c3345110530dc147304c31c548c130d314a304c354518c1308f596540c23e6195030c718d540c23c61550308f990540c31d54d0c30b398b430c25d6510c30a7992320c31d548c830c7550320c34d520c8308fd91510c23c64544309bd89510c26c62544308fd96410c23d65904308fd94410c23d651043097d95300c29c644c030b3189300c2d4614c0309ed95300c2f0614c0309798f54c825d63d53209d98754c827561d53208f99353c823d64d4f209d98753c827561d4f208f99253c823d6494f208fd9151c823c6454720cd94441c833551107209798c548825d63152208fd91538823c6454e208f990538823d6414e20b398f42882ae64cca20d3d4c328823f64546208f191518823e61d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551208f994544823e6115120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d209799
  | 2 => 0x654c8329bd95320cacf654c832d3d95320cacf644c832b3591320cacc614c832b3181320ca3f64544328f191510ca7b60544329e181510ca3f64540328f191500ca7761540329d185500ca6f6254e419b18953906ae62d0e41ab58b439071e5350e4197d8d529065c6354a41a798f429069d63d0a41cb94942906b661d4e41c7d4e53906af6254e41ab18953906ae6214e41ab58853906b66114e41ad987529072f5294a41a7d8d529069c6354a41a798c529069d6314a41ad984529063e65cca418f597329063e658ca418f596329078d320ca41a798f509069d63d4241ab98b50906ad62d4241ab98b43106ad62d0c41c754c431069e63d0841a758f421072d52108418fd954110677655044197d8d501065c63540419bd89501066c6254041ab98b53106ad62d4c41ad987531071d5314c41ad984531069e63d4841a758f52106b661d4841cb54852106b661148418f997321063d65cc8418f996321063d658c841add8532106b4614c841e34c832106b6610c841ad58432107366194441ad982511069f6354041a718d50106af6254041ab189501069e6314041a758c50106ae6214041ab588501066e62152319b588548c63f6454a318f191528c63e64942318f592508c63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c72f54d4931cb153524c72f5414931cb150524c63e6590531cbd4a414c72c52905318f994414c72f5210531cb148414c74c528c531ced53504c73854d4131dad4b504c76852d4131ce907504c73841d4131ced50504c7385414131dad48504c7685214131ce904504c7384114131dccc4504c75a31141319b98b540c66d62d50318f992530c63d6494c318f992520c63d6494831d3548320c6d5610c83197d95310c6cc624c431e5105310c6d8604c4319dd95310c6f0604c4318fd91500c63c64540319bd89500c66c62540318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798c548865d63152218fd91538863c6454e218f990538863d6414e21d3d4c328863e64942218f592508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219bd89534867b6054d219e181534865e6514d21c7d50534871c5414d218f996414871f5390521c714e414863e6510521c7d4c414871c5310521d314e214873b54d4121ce153504875b53d4121d614f504873a41d4121ce107504873b5414121ce150504875b5314121d614c504873a4114121ce10450487732114121da884504865e63d50219758f540863e64d4c218f593530863e6494c218f592530
  | 3 => 0x230000004bcaac2c8e42925d4ca2c626c850001fb3a0000219701965687d19a29c9ac3f0af3c8410bc2841cc0010e8a200012d4e9e630e45030a2717c0000012450c13c7f0004aa0000002947aa2d239472744b4002ae0843b43424f4166e4b924b50089887aa91548a53da68000b0d1825a366681211545025c4fd24810c3a8d780020c81d33ab35443580e8a614aae5628a1200234001f134e6c4001284141bcbd27c05495c450df102349261cd0002d92c18e3fc1ec068003c21b46a0003c4000c40492d45f8fe00046c9b4588762149443485a000584cf0974cc5a516137100304599d939806c00000270424001224e20000019d2f20015908e0004053c064000344780002e62ac001e501ca8400220000000002952aa0006a8003ce000491e04e6378001db0006540029137c7a8002b10ee19c648004781400015312c4d0001e3000a90208b03a2000000000000009d800000468ab1122fa46036000000000002794720f503000000860000a80003e48c9a4580000b39982bc00000000000001328000e6368001020383648ea88000545550003825ac0027d4e4290001d3018001179f32c0631472c10b60c017a212661281712c4a640c5dabd0c4000330000008ec0000000034c001742863fce01591b04c0f79c250a4310892011e598418c317e534afa3109821130276164240c6803000000d296833e96c610001126592a00036a000fa8db000768d60124ee6f51180041a0001e000011400030410031c501f20f0076c210014000624100008620304500008100400816f3040800810280b82000060001842e21030054411446403c02010111400074c03400ca2c6201001780010f0638b10e00014810000c1c319b00009531804000e1c51001660d2ac108005328700080408910220d0011401800010440010011050020040c004200099b4591c000108304c10518004014000004200a1dc54e2091400870050d00050820052024066c0101ab58b4390ece62d0e43b398b4350ead62d0c438fd954310e5f6550c439bd895010e6c62540439dd855010e746154043c754e43d0b1d5310f42ab58b4390a9d63d0a42b398f4290a3e6510d42b398f4250aad62d0c428fd954310a9d63d08428fd954210a6f655084297d8d5010a5c63540429dd855010a746154042cb58a54cca3e61953328f18554ccb2e5490b328fd9151cca3c6454732c758e548ca3e61952328f185548cb1e5490e32a7593328cb2d54cca328fd91518ca3c64546329758e544ca6d62951329dd85544ca7461551329ed81544ca7860551328f993514ca3d64d45328f990504ca3d64141329d987540ca7561d50328f992530ca3d6494c3297596430cacd6290c328f992520ca3d64948329b596420cacd6390832e350e420cb8e4350832a7593320caad648c832b358e320ca5f
  | 4 => 0x4584a9100509c09a8004a0a6d31a825263cd0807a39011d419254102e51d00022e0890a9830a40000018449aaf0000001400087b8000009585b8cf3260006397c0007ac100000007d80f8ce5303c9028364de454000002d81940004e0000013f9d70000011900035c000a400006288915011000000002a618a000001ed4c80001a80004a0e1450072647c8040e90000015a1f4000af80312a5740000c940000514ec0004927e1091853a82f49891b0e4000e900000021c5e0000009e87e1e90000015185e000000002c700a4fd061b43fe8ccdc12f3e0000000000802e8000e30d40040009f55a5fcd0923242a24701c338a508001801900ace78540e091488a6c43e35d0d1dc1ce4985613c32263cf405d402964429893bc2b9352521526882899b1f655cad8b8412134d695242ca34cc83444a988828e13386ec3a0260663f4d30e85883b07b04456e90d0caa006e7b80005c07e574b2058558a64a80cd2dc41c3f9ba3783754800057e000c322b13600000294000388000003023180b8c02ca000000000e2028021bf2560595b079400a7c650dc2820680002355e0f8bd92736e395271d51340793a89d41c5195a86052c1f41212932e8b47a90d076970c5963130000c51df23868d5d88846a1583e1fd2888e11f96d3200013f00b0005bd5809c43c6484f22823e1d4e3800000a5cd90000ae000d4800000a69539aa0000250e1d65844f4002132c400101a6108c4f90108b00000056800000000d5a87020000410000000000014f0000e8002170d604c000000000000006323c061230001e28d1528c446e084c121b00042ce514a3d805120a2439c0004a1b61de000a5a441260c9478000583303700014e9d0899a8480000bb0005700e40000016a00075a8c0aa5dce5a2e1f017c0a9c9298000519f704e03c000004be001078004ba000000000f00b4872a8000a49250000003414e1390a6000d80000000009729e1229a4000990003d0228003887e4ee80047c0005a1582b89b8000000903b9021c6210
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x61033600e2aa000b087800244b2e00000000b8011a000180894000726580c280200b4e803040004021a38ac828265235d3654c832988e2b2264194c870591320ca46ba0c099065611c5320c841960e0b086420cd070584320c7423108298863a4104604c4319c0e0b086410e84631052108750208c0908438314d62d0d40c1ac629684a052572d0c515028ab9e8428a818355262d0c3083eecaa4641860d5498f4208217bb2a999041341cd60104109c0e4b0082085907358041042d0392c0208212c5d8410c010962ec20840084b276905100434831c8288021a818a4144010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x800884815d3654c832884815d0604c832
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*2) 2
  | 6 => packedAt s0K6 (742+((h/14+packedAt s0K6 (672+(h % 14)*5) 5) % 55)*7) 7
  | 5 => packedAt s0K5 (21315+((h/245+packedAt s0K5 (19845+(h % 245)*6) 6) % 1195)*11) 11
  | 4 => packedAt s0K4 (28478+((h/237+packedAt s0K4 (27056+(h % 237)*6) 6) % 926)*11) 11
  | 3 => packedAt s0K3 (1510+((h/10+packedAt s0K3 (1470+(h % 10)*4) 4) % 49)*6) 6
  | 2 => packedAt s0K2 (121+((h/1+packedAt s0K2 (120+(h % 1)*1) 1) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffffffffffffffff03ffffffffffff0fffff
  | 2 => 0xfc07fffffff80ffffffc0ffffff80ffff1fe3f
  | 3 => 0xfff807f80ffff01ffffff03f01fff03ffe63c7
  | 4 => 0xfffff8000fffffe03fffffc001ffffc0ff83f8
  | 5 => 0xfffffffff00000003ffffffffe000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc0090908a28922448a00b2cb525b145106acdb
  | 2 => 0x74252514510e489152c0555a4a88aaa71562d
  | 3 => 0x4957446269a241d2275550263135a23cba6346
  | 4 => 0x926467458e448903b99a6980c1c6cf08dd83b0
  | 5 => 0xe38787860f870e1c3ee38e38f8070c30eff800
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa1c300d0090052c120600000030f4003820040001a12be43bc43be42bc42f741be41bc41f441b441f731f431f721f421bf40bd40f710f510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2026180a0a01c00800000400002000e30079051262202401a580f4145cb94a439b28c871e5390a6ca3214d946419b2988336521066aa020cd95331b32966334540c66ca990d594f219a2a0431c5350258a4a04d145409a2a6213454442a8a6885914910
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x48000c8998a531061663948418518d50106246254041
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s1K4 (287+((h/5+packedAt s1K4 (272+(h % 5)*3) 3) % 28)*6) 6
  | 3 => packedAt s1K3 (588+((h/7+packedAt s1K3 (567+(h % 7)*3) 3) % 35)*6) 6
  | 2 => packedAt s1K2 (153+((h/1+packedAt s1K2 (152+(h % 1)*1) 1) % 6)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 2 => 0x7f03fc07e03f01ffc3e07c0f07e07e07b32cc
  | 3 => 0x7ffffff8003ffffffc007ffff8007fffc3f0f
  | 4 => 0xf8003ffffffc001ffffff800fffff8007fc3f0
  | 5 => 0xffffc0000000001fffffffff000000007ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1010844910408202008a494910a29229015455
  | 2 => 0xb2a59c8724d526af2c16c2d8747437433b32cc
  | 3 => 0x44c329120d1a4c95554104b2ad1045965c2b0a
  | 4 => 0x668a3224499068d99a659020ce5961046e83a0
  | 5 => 0x870c3c3871e38f1ee3b9e73c0861861877fc00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaa00aaaaaa00faaaaa00aaaaaa00faaaaa00aaaaaa00faaaaa00aaaaaa00faaaaa00aaaaaa00faaaaa00aaaaaa00faaaaa00aaaaaa00faaaaa00aaaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4e70000108c00000a0b0000906ad5800003243c315126929d007c00014000000000000082c8af04315931c0550000011000ea40002e0001800010052064a1e368572600154a0020b622ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x300000000000000000000000000f64d3800000001300000000000000000000066000000000000000000000013c0000000bc00001f0000000000001a001a000000000000000000000007c000000000000147e000000000000000000003a000000000078000000000000000000000000000060000000aa00000001600001280000000000000000000000000000000000000000000000000000e03600000dc000000000602400000000000000e40000000001d2b000004800000000100000c80000000000000000000000000000000000000000000000000000002200000b00000000000007000007900000000036000000000000000000000004700124006800000ea000000038000b000780000000000000028000000000d200000000000000000000001140000000000000000010a8014800000000000004b270ac460000000000000000000000000000000000720000000000000000000000100000000000000000000006d0000000002d001045c001e8580000000001400000001100000000000000760013800fa00000000000000000000000001e0000000001f0000000000000000000000000000000000000000000000000000000000000002200000000000000353c21032002d80000000000000000000000002b80000000018c000000000620000000006b00000000006188000000000000000009060000068000016800e600000000000000000000000000000190d800130018400000000000000000082002f000000000000104140014010850010067aa5a1cf947439f286873d5490eeea2a1dd14543cfa9a873f5250f6ea2a1cf14543da28a87345150e78a0a1cf950439ea9e853e51d0a7ca1a14f55242bba8a85745150a7ea6a16bd4942dba8a853c5150b68a2a14d145429e282853e5410a7ca9994f55332bb28e657551cca7ca9194f55232bb28c6575518ca7ca8994f551329f2a0653d540cb9a64194f54e419ea94833e519067ca120cf54c419ea90833e511076ca220cf940419f2a6633d54cc6dca598db54b31da20e633f548c678a918cfd51319e2a2633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5488678a910cfd51219e2a2433e540867aa810ed10421bb28c8175519027aa7204f54a409f28c81b6519026ca3206d546409f284813d531027aa4204f944409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f553209faa4413c548827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310da20e213e548427aa9084fd51109e2a2215f53442b8a6885bd4910b629221b4414427ea8084f15010
  | 1 => 0x5c0000329d8007e0300000000000000002f800000000000004c00000fe00001980000000000060000000051000000000000002400000004a711e810001000000000000000120003800a6000000000000000000000000000000419c0000000000000000000000000000043001504000000007400000000000000000000000000081140000000351b8000000000000000000de2e28000000000000ba000010800000a800000000000000000000b2210000000523b8a80000001180
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc0201202672433211668a02a7a0390500000b80000228000000b18886000000fe3430628d18552d0e3661943438d18553d0a3661943428d185544ca3860551328d185540cb2652107318b588548c6356510431a558c410c71653107218758c54886356510421a958841086346154c408d185521023461553308d987548c23461553208d98754883145310510c9148414423661d50108758c540422d6215010
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s2K5 (816+((h/16+packedAt s2K5 (768+(h % 16)*3) 3) % 79)*7) 7
  | 4 => packedAt s2K4 (3706+((h/44+packedAt s2K4 (3618+(h % 44)*2) 2) % 665)*9) 9
  | 3 => packedAt s2K3 (1020+((h/8+packedAt s2K3 (988+(h % 8)*4) 4) % 43)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xe07fffc07e0fc1ff0f83e0fffe1e0781d27ecc
  | 3 => 0xff83ffff800ffffff003ff07ffe007ffe38f0f
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x21000889100200002284a108802290a404b055
  | 1 => 0x4b199187249492cb05a168d3b214350cd256cc
  | 3 => 0x862aa2120d29315550425a4555404659630b0a
  | 4 => 0x145344244981a5a69968108669996011b80da0
  | 5 => 0x1863873871ce39f8ee739ce071118461ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfc07ffc0ffffff81fffff80ffe07fffe7f1e3f
  | 1 => 0xffffffff01fc07fe0f81fffffff81f0193ffcc
  | 2 => 0xfff81ffffe0007fff001fff03fffe001e3e3f0
  | 4 => 0x1ffffffffffffffe00003ffffffffc03ff
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x53044462448a180529259454622a54c270e15
  | 1 => 0x4851888a1c912a9605a0aa599aa896149176cc
  | 2 => 0x90a2d514483ab5aab05135652d36c42963a370
  | 4 => 0xc2c51a209123064d2964060831c518b1d801aa
  | 5 => 0xe3061c38e1c3c771ce79c78e018610c1fed800
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8eaea0000eaeac8c8eaea0000eaeac8c8eaea0000eaeac8c8eaea0000eaeac8c8eaea0000eaeac8c8eaea0000eaeac8c8eaea0000eaeac8c8eaea0000, s3N, s3R, (fun _ _ => 0), s3I⟩
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfc07ffc0ffffff81fffff80ffe07fffe7f1e3f
  | 1 => 0xffffffff01fc07fe0f81fffffff81f0193ffcc
  | 2 => 0xfff81ffffe0007fff001fff03fffe001e3e3f0
  | 3 => 0x1ffffffffffffffe00003ffffffffc03ff
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x53044462448a180529259454622a54c270e15
  | 1 => 0x4851888a1c912a9605a0aa599aa896149176cc
  | 2 => 0x90a2d514483ab5aab05135652d36c42963a370
  | 3 => 0xc2c51a209123064d2964060831c518b1d801aa
  | 5 => 0xe3061c38e1c3c771ce79c78e018610c1fed800
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeac8eac8ea00ea00eac8eac8ea00ea00eac8eac8ea00ea00eac8eac8ea00ea00eac8eac8ea00ea00eac8eac8ea00ea00eac8eac8ea00ea00eac8eac8ea00ea00, s4N, s4R, (fun _ _ => 0), s4I⟩
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x289812002ee21ec21ef20ed20f710f510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x12d2a010f848110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s5K4 (98+((h/2+packedAt s5K4 (96+(h % 2)*1) 1) % 8)*4) 4
  | 3 => packedAt s5K3 (55+((h/1+packedAt s5K3 (54+(h % 1)*1) 1) % 3)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fffff81ffffc0ff0ff83ffffc1fffd18fe3f
  | 1 => 0xfe07e0ffe07e0ff0ff0ffc1e07fe0f02ef33cc
  | 2 => 0xfff800ffff800fff000fffe007fff0030fc3f0
  | 3 => 0xfffffffffffff0000007fffffff003ff
  | 4 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8c104408c1044401101190aa30c85518085615
  | 1 => 0x14b18511472854b07106948c534a46286b32cc
  | 2 => 0x2862d6a28a1d6d57088b5ac8a5ad64530dc370
  | 3 => 0x714518c414510a6aaaa04201063188e3b001aa
  | 4 => 0x4186108718618b8ccccc6311c0210083d6a800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00, s5N, s5R, (fun _ _ => 0), s5I⟩
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x427de2300c130118000140a1000010cc0000048d177001a8000c8da5540071d38d00002a0001e5c00980004002800005a45ae5d00000001176ac02004c418f7a9c68000005000cbcc8000000093001b0000a562200583b700200040e4a01b149007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4805fe52007f54805fc52007fd0805fe42007f50805fc42007fcc805fe32007f4c805fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31017fc8401fe21007f48405fc2100ffd4003fe5000ff54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003ef2000ff88003fd2000fb48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x6207ff10031047fe601881ffe300c40ffe9806208ff0c03103ffe401881fef200c40fff1006207ff4803103fda401881ffc200c407ff8806203ff8403101ffa201880ffc100c407ffb2c4203bfd962101ffccb10816fe6588407feb2c4200bf5962101ff8cb1080efc6588407ffb244203bfd922101ffcc910802fe6488407feb244200bf5922101ff8c91080efc6488401ffaa44200ff95221007faa910803fc5488407ffb1c4203bfd8e2101ffcc710802fe6388407feb1c4200bf58e2101ff8c71080efc6388401ffa9c4200ff94e21007faa710803fc5388401ffa1c4200ff90e21007fa8710803fc43884057eb144202ffd4a21007dea51080bfe5288405fea944202ff14a21017d8a51080bff4288401f7a144202ff90a21017fa851080bfc4288405f62144202ffcca21007de651080bfe3288405fe9944202ff0ca21017d8651080efe6188407ffa8c4203ff9462101ffaa31080ffc5188407ffa0c4203ff9062101ffa831080ffc4188407ff98c4203ff8c62101ffa631080ffc3188407ff90c4203fbc8621017ee431080ffc2188407fa10c4203ffd822101dfec11080ffe60884037f3044203ff58221035fac11080ffc60884037e3044206ffd4221037fca11081bfd508840dfe2844206ffd0221037fc811081bfd408840dfe2044206ffcc221037fc611081bfd308840dfe1844202ffc8221017de411080bfe2088405fe9044206fb48221017f8411080fff1088407ff0844203ff4422101ff82110803ff65484017fb2a4200dfd9521004feca90803fe654840b7f32a4200ff59521005faca90803fc654840b7e32a4200df19521004f8ca90803ff64484017fb224200ff99121005fcc890803fd64484017eb224200ff19121005f8c890803ff5448401ff2a24200ff55121007f8a890803ff63484017fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803ff5348401ff29a4200ff54d21007f8a690803ff4348401ff21a4200ff50d21007f8869080eff6248405ffa924202ff94921017faa49080bfc5248405ffa124202ff90921017fa849080bfc4248405ff9924202ff8c921017fa649080bfc32484057fb0a4200ffd452101ffca290803fd5148407fe28a4200ffd052101ffc8290803fd4148407fe20a4200ffcc52101ffc6290803fd3148407fe18a4202ffc8521017ee429080ffe2148407f710a4203ff0852101fd8429080bf42148409ffb024204bfd8121027fcc090806fe6048409feb024204bf58121027f8c090806fc6048409ffa824204ff94121027faa090813fc5048409ffa024204ff90121027fa8090813fc4048409ff9824204ff8c121027fa6090813fc3048405ff9024202fbc8121017fc409080bfd2048409f69024202ff0812101ffe2090813fe1048409fe8824203ff04121
  | 1 => 0xfdf318c401fb98c6203ffc863101ff8431880fff608c4077fb046203ff9823100dfcc11880ffd608c41b7eb046203ff1823100df8c118837ff508c41bff284620dff5423106ff8a118837ff408c41bff204620dff5023106ff88118837ff308c41bff184620dff4c23106ff86118837ff208c41bf7904620dff8823106ffa4118837ed208c41bfe1046203ffc423101fee211880ffe108c407fe884620dfd4423101ff82118803ff654c4017fb2a6200dfd9531004feca98803fe654c40b7f32a6200ff59531005faca98803fc654c40b7e32a6200df19531004f8ca98803ff644c4017fb226200ff99131005fcc898803fd644c4017eb226200ff19131005f8c898803ff544c401ff2a26200ff55131007f8a898803ff534c401ff29a6200ff54d31007f8a698803ff434c401ff21a6200ff50d31007f88698803ff624c4017fb126200fbd8931005dec498833fe624c4057f3126200ff58931067f8c49880afc624c401f63126202bb18931007fea498833fe524c401fea92620cff14931007fe8498833fe424c401fea12620cff10931007fe6498833fe324c401fe992620cff0c931007fea29880ffe514c401fea8a6203ff14531007fe829880ffe414c401fea0a6203ff10531007fe6298803f7314c407ff18a6203f78c531067fe429880ffc214c417ffb02620bbfd813105ffcc098806fe604c417feb02620bbf5813105ff8c098806fc604c417ffa82620bff9413105ffaa09882ffc504c417ffa02620bff9013105ffa809882ffc404c417ff982620bff8c13105ffa609882ffc304c417ff902620bfbc813105ffc409882ffd204c417f6902620bff0813101ffe209882ff7104c417ff082620bff4413105fea209880ffc104c407ffb286203bfd943101ffcca18816fe650c407bf32862009f9943101ffaca18802fd650c407beb2862009f5943101ff8ca1880efc650c407ffb206203bfd903101ffcc818802fe640c407feb206200bf5903101ff8c81880efc640c401ffaa06200ff95031007faa818803fc540c4157f3186200ffd4c31047fca618803fd530c411fe2986200ffd0c31047fc8618803fd430c411fe2186203ffd883101ffcc41880afe620c407feb106200bf5883101ff8c41880efc620c401ffa906209ff94831007faa418827fc520c401ffa106209ff90831007fa8418827fc420c411ff9906209ff8c831007fa6418823fc320c4077f3086203ffd443101ffca21880ffd510c407fe2886203ffd043101ffc821880ffd410c407fe2086203ffcc43101fbe621880ffe310c407fb1886203ff4c43101fba6218803f5310c407ff9086203ff0843101ffec01880eff600c407ff3006201bf9803101ffac01881efd600c407fe3006201bf1803103ffea01881ffe500c40ffea806207ff1403103ffe801881ffe400c40ffea
  | 2 => 0x4101ffcc620802fe6310407feb188200bf58c4101ff8c620803ff5310401ff2988200ff54c41007f8a620847ff4310401ff2188200ff50c4108ff8862080fff6210407ff3108202bf9884101ffac420802fd6210407fe3108203bf18841007fea42084bfe5210401fea908212ff1484108ffe842084bfe4210401fea108211ff10841007fe642084bfe3210401fe9908212ff0c84101dfcc22080fff5110407ff2888203ff5444101ff8a22080fff4110407dfa088203ff9044101fec822080ffd4110407dea088200fd5044101ffe422080ffc2110407ffb008203bfd804101ffcc020806fe6010407feb008210bf5804101ff8c020806fc6010421ffa808210ff94041087faa020843fc5010423ffa008210ff90041087fa8020847fc4010421ff9808210ff8c041087fa6020843fc3010421ff9008210fbc8041087fc4020843fd2010421f69008210ff0804101ffe202080ffe1010407fe8808203ff04041047fecb98802ff65cc401ff32e6205bf99731007facb98802fd65cc411fe32e6205bf19731047fec998802ff64cc401ff3266200bf99331007fac998802fd64cc411fe3266200bf19331007fea998803fe54cc401feaa66200ff15331007fea798823fe53cc401fea9e6208ff14f31007fe8798823fe43cc401fea1e6208ff10f31047fec59883ffe62cc4057f3166200ff58b31005fac598823fc62cc4057e3166200ffd4b3107ffca598803fd52cc41ffe2966200ffd0b3107ffc8598803fd42cc41ffe2166208ffccb3107ffc6598803fd32cc411fe1966200ffd473101ffca398803fd51cc407fe28e6200ffd073101ffc8398803fd41cc407fe20e620fffc873101ff84398823ff60cc4157fb06620aff9833100dfcc19882bfd60cc4157eb066208ff1833100df8c19882bff50cc415ff286620aff54331057f8a19882bff40cc415ff206620aff50331057f88198823ff30cc415ff186620aff4c331047f8619882bff20cc415f7906620aff88331057fa419882bed20cc415fe1066203ffc4331057fc219882bfd10cc407fe0866203ffd963101dfecb1880ffe658c40b7f32c6203ff59631005facb1880ffc658c4077e32c6203ffd923101dfec91880ffe648c4017f3246203ff59231005fac91880ffc648c4077e3246200ffd5231007fca918803fd548c401fe2a4620bbf58e31007fea718803fe538c401fea9c6200ff14e31007fe8718803fe438c401fea1c6200ff10e3101ffec51880ffe628c4057f3146203ff58a31005fac51880ffc628c4077e3146200ffd4a31077fca518803fd528c41dfe2946200ffd0a31077fc8518803fd428c41dfe2146200ffcca31077fc6518803fd328c41dfe1946203bf9863101ffea31880ffe518c407fea8c6203ff1463101ffe831880ffe418c407fea0c6203ff1063101ffe631880
  | 3 => 0xf2868213ff5434109ff8a1a0847ff40d0427ff2068213ff5034108ff881a084fff30d0427ff1868213ff4c34109ff861a084fff20d0427f79068213ff8834109ffa41a084fed20d0427fe1068203ffc434109ffc21a084ffd10d0407fe0868203ffd964101dfecb2080ffe659040b7f32c8203ff59641005facb2080ffc65904077e32c8214bf59241007fea920803fe5490401feaa48200ff1524101ffec72080ffe63904017f31c8203ff58e41005fac72080ffc6390401ffa9c8200ff94e41007faa720803fc5390401ffa1c8200ff90e41007fa8720803fc4390407ffb148203ff98a41015fcc52080ffd62904017eb148203ff18a4101df8c520803ff529042fff2948200ff54a410bff8a520803ff429042fff2148200ff50a410bff88520803ff329042fff1948200ff4ca410bff8652080efe6190407ffa8c8203ff9464101ffaa32080ffc5190407ffa0c8203efd0641007ee832080fff2190407fe10c8203ffd824101dfec12080ffe60904037f3048203ff582410b5fac12080ffc60904037e3048216ffd42410b7fca12085bfd509042dfe2848216ffd02410b7fc812085bfd409042dfe2048216ffcc2410b7fc612085bfd309042dfe1848216ffc82410b7de412085bfe209042dfe9048216fb482410b7f8412080fff1090407fb8848203ff8424101ffa212085bf51090407fe0848200ffd9541005fecaa08037f65504013fb2a8200ff9954102dfccaa0803fd65504017eb2a8200ff1954102df8caa08037c65504013e32a8200ffd5141007fca8a0803fd5450401fe2a28200ffd8d41005fec6a0803fe6350401feb1a8200ff18d41005f8c6a0803ff5350401ff29a8200ff54d41007f8a6a0803ff4350401ff21a8200ff50d41007f886a0803ff62504017fb128200fbd8941005dec4a0857fe62504057f3128200ff589410aff8c4a080afc6250401f63128202bb18941007fea4a0857fe5250401fea928215ff14941007fe84a0857fe4250401fea128215ff10941007fe64a0857fe3250401fe9928215ff0c941007fea2a080ffe5150401fea8a8203ff14541007fe82a0803f74150407ff20a8203ef905410affe42a080ffc2150429ffb028214bfd81410a7fcc0a0806fe6050429feb028214bf581410a7f8c0a0806fc6050429ffa828214ff941410a7faa0a0853fc5050429ffa028214ff901410a7fa80a0853fc4050429ff9828214ff8c1410a7fa60a0853fc3050429ff9028214fbc81410a7fc40a0853fd2050429f69028214ff0814101ffe20a0853f71050429ff0828214ff441410a7ea20a080ffc1050407ffb288203bfd944101ffcca20816fe6510407bf32882009f9944101ffaca20802fd6510407beb2882009f5944101ff8ca2080efc65104277f3208200ffd504108ffca820803fd5410423fe2a08203ffd8c
  | 4 => 0x803fe5354401fea9aa200df54d5102ff8a6a8803ff4354401ff21aa200ff50d51007f886a8803ff62544017fb12a200fbd8951005dec4a8873fe62544057f312a200ff589510e7f8c4a880afc6254401f6312a202bb1895102ffea4a8873fe5254401fea92a205ff14951007fe84a8873fe4254401fea12a21cff10951007fe64a8873fe3254401fe992a21cff0c95102ffea2a8817f75154407ff28aa203df945510e7fe42a880ffc2154437ffb02a21bbfd81510dffcc0a8806fe6054437feb02a21bbf581510dff8c0a8806fc605440bffa82a21bff941510dffaa0a8817fc5054437ffa02a21bff901510dffa80a886ffc4054437ff982a21bff8c1510dffa60a886ffc3054437ff902a21bfbc81510dffc40a886ffd2054437f6902a21bff0815101ffe20a886ffe1054437fe882a203ff0415102dfcca2880fff6414407ff320a200bf9905101ffac828802fd6414407fe320a205ffd505102ffca8288037e541440bfeaa0a205ff1505102ef8a82880fff6314407ff318a200bf98c5101ffac628802fd6314407fe318a205ffd4c5102ffca6288037e531440bfea98a205ff14c5102ef8a628803ff4314401ff218a200ff50c51007f8862880fff6214407ff310a202bf9885101ffac428802fd6214407fe310a203bf1885102ffea428817fe5214435bf290a205ff5485102ff8a4288177c5214401ffa10a21aff90851007fa842886bfc4214401ff990a21aff8c851007fa642886bfc32144077f308a203ffd445101efea22880ffe5114407fb288a203ff5445101efaa228817f55114407ff908a203ff0845101ffec02880eff6014407ff300a201bf9805101ffac028866fd6014407fe300a201bf1805102ffea0288177f501440bff280a205ff540510cefaa028817fc5014433ffa00a219ff900510cffa8028867fc4014433ff980a219ff8c0510cffa6028867fc3014433ff900a219fbc80510cffc4028867fd2014433f6900a219ff0805101ffe202880ff71014407ff080a203ff440510cfea202880ffc1014423ffb2e8200bfd9741007fccba0816fe65d0401feb2e8200bf5974108ff8cba0816fc65d0401ffaa68211ff95341007faa9a0847fc54d0423ffb1e8200ff98f41005fcc7a0803fd63d04017eb1e8211ff18f41007fea7a0803fe53d0401fea9e8200ff14f4108ffe87a0803fe43d0401fea1e8211ff10f4108ffec5a0863fe62d04057f3168200ff58b41005fac5a0847fc62d04057e3168200ffd4b410c7fca5a0803fd52d0431fe2968211ffd0b410c7fc85a0803fd42d0423fe2168200ffccb410c7fc65a0803fd32d0431fe1968200ffd474101ffca3a0803fd51d0407fe28e8218ffc874101ff843a0847ff60d04277fb068213ff9834100dfcc1a084ffd60d04277eb068211ff1834100df8c1a084fff50d0427f
  | 5 => 0x8532017fe429900bfc214c843ffb026421bfd813210ffcc099006fe604c843feb026421bf5813210ff8c099006fc604c843ffa826421ff9413210ffaa099087fc504c843ffa026421ff9013210ffa8099087fc404c843ff9826421ff8c13210ffa6099087fc304c805ff9026402fbc8132017fc409900bfd204c843f69026402ff0813210ffe2099087fe104c843fe8826421ff0413202ffec9a8817fe64d44017f326a205ff59351005fac9a8817fc64d440bffaa6a205dfd535102ffca9a8817fd54d4401beaa6a205ff1535102ffec7a8817fe63d44017f31ea205ff58f51005fac7a8817fc63d440bffa9ea205dfd4f5102ffca7a8817fd53d4401bea9ea205ff14f51007fe87a8803fe43d4401fea1ea200ff10f5102ffec5a8817fe62d44057f316a205ff58b51005fac5a8817fc62d44057e316a205ffd4b5102ffca5a8817fd52d440bfe296a200ffd0b51107fc85a8803fd42d4441fe216a200ffccb51107fc65a8803fd32d4441fe196a220ffc875101ff843a8817ff60d440b7fb06a205ff9835100dfcc1a8817fd60d443f7eb06a205ff1835100df8c1a8817ff50d440bff286a205ff5435102ff8a1a887fff40d443fff206a21fff503510fff881a887fff30d443fff186a21fff4c3510fff861a887fff20d443ff7906a21fff883510fffa41a887fed20d443ffe106a203ffc43510ffee21a887ffe10d443ffe886a21ffd4435101ff821a886efd6594407ffb24a203ff99251005fcc92880ffd64944017eb24a203ff1925102ffea928803fe5494401bf2a4a200ff5525102ff8a9288037c5494407ffb1ca203ff98e51005fcc72880ffd63944017eb1ca203ff18e5102ffea728803fe5394401bf29ca200ff54e5102ff8a7288037c5394401ffa1ca200ff90e51007fa8728803fc4394407ffb14a203ff98a51015fcc52880ffd62944017eb14a203ff18a5101df8c528817ff529443dff294a21edf94a51007faa528817fc529443dbe294a200ffd0a510f7fc8528803fd429443dfe214a200ffcca510f7fc6528803fd329443dfe194a203bf9865101ffea32880f7f519440bfba8ca203ffc865101ff8432880fff60944077fb04a203ff9825100dfcc12880ffd609443b7eb04a203ff1825100df8c128817ff509443bbfa84a21dff942510effaa1288777d509440bfe284a21dffd02510effc8128877fd409443bfe204a21dffcc2510effc6128877fd309443bfe184a21dffc82510efde4128877fe209443bfe904a21dfb482510eff8412880fff1094407ff084a203ff4425101ff82128803ff64544017fb22a200ff99151007fac8a8803fc64544017e322a205ffd5151006fea8a8803fe5454401feaa2a200df5515102ff8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc63544017e31aa205ffd4d51006fea6a8
  | 6 => 0x9f69068402ff08342127fe21a1093fe10d0849fe8868424ff04342007fecaa1002ff6550801ff32a8405bf99542007facaa1002fd6550801fe32a8405bf19542015fec8a1003ff5450801ff2a28400ff55142007f8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508017e31a8400ffd4d42007fca6a1003fd5350801fe29a8400ffd0d42007fc86a1003fd4350801fe21a8402bfd8942017fea4a100bfe5250805fea928402ff14942017fe84a1003ef4250805ff2128402ef90942017f884a100bbc4250805f62128402ff8c942017f864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508077e30a8402ffc8542017f842a108fff60508477fb028423ff9814200dfcc0a108ffd60508477eb028423ff1814200df8c0a108fff5050847ff2828423ff5414211ff8a0a108fff4050847ff2028423ff5014211ff880a108fff3050847ff1828423ff4c14211ff860a100bff2050805f79028402ff88142017fa40a108fed2050805fe1028423ffc414211ffc20a108ffd1050847fe0828408ffd9732005fecb99003fe65cc80b7f32e6400df99732004fccb99003fd65cc8017eb2e6400df59732004facb99023fc65cc80b7e32e6408ffd9332005fec999003fe64cc8017f3266400ff59332005fac999023fc64cc8017e3266400ffd5332007fca999003fd54cc801fe2a66402bf98f32007fea799023fe53cc801fea9e6408ff14f32007fe8799023fe43cc801fea1e6408ff10f32015fac59900bff52cc805ff2966402ff54b32017f8a59900bff42cc805ff2166402ff50b32017f8859900bfe32cc805ef1966402fb8cb32017f8659900bdc32cc811ffb0e6400ff9873201dfcc399003fd61cc8017eb0e6408ff18732017fe439900bfc21cc805f610e6408ffd8332115fec19908bfe60cc8037f3066422ff58332115fac199023fc60cc8037e3066422ffd4332117fca19908bfd50cc845fe2866422ffd0332117fc819908bfd40cc845fe2066408ffcc332117fc619908bfd30cc811fe1866402ffc8332017de419900bfe20cc805fe9066422fb48332017f8419908bff10cc845ff0866422ff44332117f82199003ff654c8017fb2a6400ff9953202dfcca99003fd654c8017eb2a6400ff1953202df8ca99003ff644c8017fb226400ff99132005fcc899003fd644c8017eb226400ff19132005f8c899003ff544c801ff2a26400ff55132007f8a89900aff634c801ffa9a6400ff94d32007faa699003fc534c801ffa1a6400ff90d32007fa8699003fc434c8057fb126402ffd4932017fca49900bfd524c805fe2926402ffd0932017fc849900bfd424c805fe2126402ffcc932007de649900bfe324c805ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6403bf1
  | 7 => 0xa9002fd64d480bfe326a405ffd535202ffca9a9017fd54d480bfe2a6a405ffd8f5202ffcc7a9002fe63d480bfeb1ea400bf58f5202ff8c7a9017ff53d480bff29ea405ff54f5202ff8a7a9003ff43d4801ff21ea400ff50f52007f887a900afd62d4805ff296a402df94b52017dca5a900b6e52d4805fe296a402df14b52017fc85a900bfc42d4805ff196a402ff0cb5202ffec3a9017fe61d48077f30ea405ff58752005fac3a9017fc61d4805ff90ea402ff08752017d843a9017ff60d480b7fb06a405ff9835200dfcc1a9017fd60d484d7eb06a405ff1835200df8c1a9017ff50d480bff286a405ff5435202ff8a1a909bff40d484dff206a426ff50352137f881a909bff30d484dff186a426ff4c352137f861a900bff20d4805f7906a402ff88352017fa41a909bed20d4805fe106a426ffc4352137fc21a909bfd10d484dfe086a402bfd9552007fec8a9002ff6454801ff322a400ff59152007f8c8a9002fc645480bffaa2a400ff95152007faa8a9017fc5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa400bf18d5202ffea6a9003fe5354801fea9aa405ff14d52007fe86a9003fe4354801fea1aa400ff10d52015fec4a900bff525480bf7a92a402ff94952016fca4a900bfc5254805be292a402fb14952017fc84a900bfc4254805ff192a402ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a900efc6154805ff90aa402ff0855212ffec0a9096ff605484bff302a401bf9815212ffac0a9096fd605484bfe302a401bf1815202ffea0a9097fe505484bfea82a405ff1415212ffe80a9097fe405484bfea02a425ff1015212ffe60a9097fe305484bfe982a425ff0c152017fe40a900bef2054805ff102a402ff4815212fda40a900bfc205484bff882a425ff8415212ffa20a9097fc1054823ffb2e8400bfd9742007fccba1016fe65d0801bf32e84009f99742007facba1002fd65d0801beb2e84009f5974208ff8cba1016fc65d08057f3268400ffd534208ffca9a1003fd54d0823fe2a68411ffd8f42007fcc7a1002fe63d0801feb1e8400bf58f4208ff8c7a1003ff53d0801ff29e8400ff54f42007f8a7a1047ff43d0801ff21e8400ff50f4208ff887a100afd62d0805ffa968402ff94b42017faa5a100bfc52d0805ff2168402ef90b42017dc85a100bfc42d0805de2168402ff8cb42017f865a1047ff61d0801ff30e8403bf98742007fac3a1002fd61d0823fe30e8402ffc8742017f843a100bec21d0823ffb068424bfd8342127fcc1a1006fe60d0849feb068424bf5834208ff8c1a1006fc60d0849ffa868424ff94342127faa1a1093fc50d0823ffa068424ff90342127fa81a1047fc40d0849ff9868424ff8c342127fa61a1093fc30d0805ff9068402fbc8342017fc41a100bfd20d084
  | 8 => 0xfd5243007fca921803fd5490c01fe2a48627bf98e43007fea721823fe5390c01fea9c8608ff14e43007fe8721803bf4390c01efa1c8608ffd8a4316ffcc52180afe6290c01feb148600bf58a43047f8c52180afc6290c5bff294862dff14a4316ffc85218b7fc4290c5bff1948608ff0ca43047fec321803fe6190c077f30c8600ff58643005fac321823fc6190c5bff90c862dff08643047fec1218a6ff6090c53ff3048601bf9824314ffac1218a6fd6090c11fe3048601bf1824314ffea1218a7fe5090c53fea848629ff1424314ffe81218a7fe4090c53fea048629ff10243047fe61218a7df3090c53ff1848629ff4c24314fba6121823fc3090c53ff9048629fbc824314ffc41218a7fd2090c53f69048629ff0824314ffe21218a7fe1090c53fe8848629ff04243007fecaa1802ff6550c01ff32a8605bf99543007facaa1802fd6550c01fe32a8605bf19543007fea8a1803fe5450c01feaa28600ff15143007fea6a1803fe5350c01fea9a8600ff14d43007fe86a1803df4350c01ff21a8600ef90d43007fec4a1802ff6250c59ff3128602bf98943007fac4a18b3fc6250c057e312862cff94943167f8a4a18b3fe4250c59fe212862cff8c943167f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c077e30a862cffc8543167f842a18afff6050c577fb02862bff9814300dfcc0a18affd6050c577eb02862bff1814300df8c0a18afff5050c57ff282862bff5414315ff8a0a18afff4050c57dfa02862bff9014315ffa80a18afbd4050c57fe202862bffcc14315fbe60a18affe3050c57fe982862bf74c14315ff860a18afff2050c57f7902862bff8814315ffa40a18afed2050c57fe102862bffc414315ffc20a18affd1050c57fe0828608ffd9443005feca21803fe6510c0b7f3288600ff59443005faca21823fc6510c0b7e328862abf99043007fea821847fe5410c01feaa08611ff1504314dfcc621803ff5310c11ff2988600ff54c43047f8a621847ff4310c01dfa188608ff90c43007bc8621803fd4310c01dea188600f750c430073a8621823ff6210c51ff3108602bf98843007fac421802fd6210c11fe3108602bf18843147fca4218a3fc5210c51ff2108611ff10843147fc6421823fc3210c11ffb088600ff9844301dfcc221803fd6110c017eb088608ff18443147fe42218a3fc2110c11ffb008627bfd804313ffcc021806fe6010c4ffeb008627bf58043047f8c021806fc6010c4fffa808627ff9404313ffaa02189ffc5010c23ffa008627ff9004313ffa8021847fc4010c11ff9808627ff8c04313ffa6021823fc3010c4fff9008627fbc804313ffc402189ffd2010c4ff69008627ff0804313ffe202189ffe1010c4ffe8808627ff04043015fccba9017ff64d480bff326a400bf9935202ffac9
  | 9 => 0xc01bf2a2a600ff5515302ff8a8a98037c5454c0bffa9aa605f7d4d53007fca6a98037e5354c01ffb12a600bfd895319ffcc4a980afe6254c01feb12a633ff18953015f8c4a98cffe5254c67bf292a605ff1495319ef8a4a98cffe4254c67fe212a633ff8c95319ff864a9803ff6154c017fb0aa600ff98553007fac2a9803fc6154c077e30aa633ffc855319ff842a98cbff6054c657fb02a632ff9815300dfcc0a98cbfd6054c657eb02a632ff1815300df8c0a9817ff5054c65bfa82a632ff94153197faa0a98cb7d5054c0bfe282a632ffd0153197fc80a98cbfd4054c65fe202a632ffcc153197fc60a98cbfd3054c65fe182a632ffc8153197de40a98cbfe2054c65fe902a632fb48153197f840a98cbff1054c65ff082a632ff44153197f820a9816fe6514c11ffb20a605ff99053005fcc829817fd6414c017eb20a608ff1905302ffea8298177f5414c0bff2a0a605ff55053006faa829817fc5414c637f318a605ffd4c5302efea629823fe5314c0bef298a605ff54c53006faa629817dd5314c11ffb10a605ff98853015fcc429817fd6214c017eb10a608ff18853015f8c429817fe5214c0bfe290a630ff90853187f884298c3fe3214c11fe190a608ffd845302ffcc22980efe6114c0bfeb08a600bf58453047f8c2298c3ff2114c61fe108a608ffd805302dfec029817fe6014c037f300a605ff5805317dfac029823fc6014c037e300a605ffd405302ffca029817fd5014c0bfe280a62fffd005317ffc80298bffd4014c5ffe200a608ffcc05317ffc60298bffd3014c11fe180a62fffc805317fde40298bffe2014c5ffe900a62ffb4805317ff840298bfff1014c5fff080a62fff4405317ff82029847ff65d0c017fb2e8600ff9974302dfccba18037e65d0c013f32e8600ff59743005facba18037d65d0c013eb2e8611ff1974302df8cba1803ff54d0c23ff2a68600ff5534308ff8a9a1803ff53d0c01ff29e8600ff54f43007f8a7a1847ff62d0c5dff3168602bf98b43007fac5a1802fd62d0c23fe3168602bf18b43177fca5a18bbfc52d0c5dff2168611ff10b43177fc65a18bbfc32d0c23ffb0e8600ff9874301dfcc3a1803fd61d0c017eb0e8611ff18743177fe43a18bbfc21d0c23ffb06862abfd8343157fcc1a1806fe60d0c55feb06862abf5834308ff8c1a1806fc60d0c55ffa86862aff94343157faa1a18abfc50d0c23ffa06862aefd0343157fc81a18abfd40d0c55dea068611ff10343157fe61a18abfe30d0c55fe986862aff0c343157fe41a18abef20d0c55ff106862aff48343157da41a18abfc20d0c55ff886862aff84343157fa21a18abfc10d0c11ffb2c8600bfd9643007fccb21816fe6590c01bf32c86009f99643007facb21802fd6590c01beb2c86009f59643047f8cb21816fc6590c577eb248600f
  | 10 => 0x60aa0ebfc3055075ff902a83afbc81541d7fc40aa0ebfd2055075f6902a83aff081541d7fe20aa0ebfe1055075fe882a83aff0415402dfcca2a0e6fe641500bffaa0a805dfd505408ffca82a017be541500bfeaa0a800df5505402f7aa82a047ff631500bff318a800bf98c5402ffac62a002fd6315023fe318a811ffd885402ffcc42a00afe621500bfeb10a800bf5885408ff8c42a00afc621500bff290a805ff148541c7fc842a047fc4215071ff190a838ff0c85408ffec22a017fe61150077f308a805ff58454005fac22a047fc6115071ff908a838ff0845408ffec02a016ff601500bff300a801bf9805402ffac02a0defd6015023fe300a801bf1805402ffea02a017fe501500bfea80a805ff1405408ffe802a0dffe401506ffea00a811ff100541bffe602a0dffe301506ffe980a837ff0c0541bffe402a0dfef201506fff100a837ff480541bfda402a0dffc201506fff880a837ff840541bffa202a0dffc101500bffb26a605ff99353005fcc9a9817fd64d4c017eb26a605ff1935302ffea9a9817fe54d4c01bf2a6a605ff5535302ff8a9a98177c54d4c0bffb16a605ff98b53015fcc5a9817fd62d4c017eb16a605ff18b53015f8c5a9817fe52d4c6dbf296a605ff14b5302ef8a5a98dbfe42d4c6dfe216a636ff8cb531b7f865a9817ff61d4c0bff30ea603bf9875302ffac3a9802fd61d4c0bfe30ea636ffc87531b7f843a9817ff60d4c0b7fb06a605ff9835300dfcc1a9817fd60d4c6b7eb06a605ff1835300df8c1a9817ff50d4c0bbfa86a605ff9435302ffaa1a98d77d50d4c0bfe286a635ffd03531affc81a98d7fd40d4c6bfe206a635ffcc3531affc61a98d7fd30d4c6bfe186a635ffc83531afde41a98d7fe20d4c6bfe906a635fb483531aff841a98d7ff10d4c6bff086a635ff443531aff821a98cafd6594c11ffb24a600ff99253005fcc929803fd6494c017eb24a608ff1925302ffea9298037f5494c01ff2a4a600ff55253006faa929817fc5494c0b7f31ca605ffd4e53006fea729817df5394c01afa9ca608ffd8a531a7fcc52980afe6294c01feb14a600bf58a53047f8c52980afc6294c69ff294a605ff14a531a7fc85298d3fc4294c69ff194a608ff0ca53047fec329803fe6194c077f30ca600ff58653005fac329823fc6194c69ff90ca634ff08653047fec1298c6ff6094c63ff304a601bf9825318ffac1298c6fd6094c11fe304a601bf1825302ffea1298c7fe5094c63fea84a605ff1425318ffe81298c7fe4094c63fea04a631ff10253047fe61298c7fe3094c63fe984a608ff0c25318ffe41298c7ef2094c63ff104a631ff4825318fda41298c7fc2094c63ff884a631ff8425318ffa21298c7fc1094c01ffb22a600bfd9153007fcc8a9803fd6454c01fe322a600bf1915302ffea8a9803fe5454
  | 11 => 0x6148c2018040008080002008c020004300400014601800800841004012040108c270808100801094e1004600000103841000200046200041108234000400004100c108141001801dc2501c21080020802100ca6094210024310c041a882100601800409c620002000560000200040020041000e00000100041100001802200421080610308018582184000a0e40004000d23004ce104e100c01280200044301c00004010184018040004601008c0886a00001040010004000442184200840430802000600040130464204205ffd8f5402ffcc7aa002fe63d500bfeb1ea800bf58f5402ff8c7aa017ff62d500bff316a802bf98b5402ffac5aa002fd62d500bfe316a802bf18b5402ffca5aa0fb7e52d500bfe296a805df14b541f7fc85aa0fbfc42d507dff196a83eff0cb5402ffec3aa017fe61d50077f30ea805ff58754005fac3aa017fc61d507dff90ea83eff0875402ffec1aa016ff60d500bff306a801bf9835402ffac1aa0f6fd60d500bfe306a801bf1835402ffea1aa0177f50d500bff286a805ff543541eefaa1aa017fc50d507bffa06a83dff903541effa81aa0f7fc40d507bff986a83dff8c3541effa61aa0f7fc30d507bff906a83dfbc83541effc41aa0f7fd20d507bf6906a83dff083541effe21aa0f7fe10d507bfe886a83dff043541d5facb2a016fe649500bffaa4a800dfd525402f7ea92a0033f5495023ffb1ca800ff98e54005fcc72a003fd63950017eb1ca811ff18e5408ffec52a0f3fe62950057f314a800ff58a54005fac52a047fc62950057e314a83cff94a5402ff8a52a0f3fe4295023fe214a83cff8ca541e7f8652a047ff6195001ff30ca803bf98654007fac32a002fd6195023fe30ca83cffc86541e7f8432a047ff60950737fb04a839ff9825400dfcc12a0e7fd60950737eb04a811ff1825400df8c12a017ff5095073ff284a839ff5425402ff8a12a047ff4095073ff204a839ff5025408ff8812a0e7ff3095073ff184a839ff4c2541cff8612a0e7ff2095073f7904a839ff882541cffa412a0e7ed2095073fe104a839ffc42541cffc212a0e7fd1095073fe084a805ffd515402f7ea8aa003fe5455001bf2a2a800ffd8d54005fec6aa003fe6355001feb1aa800ff18d54005f8c6aa003ff62550017fb12a83bff98954015fcc4aa003fd6255077fe312a802bf189541dffca4aa0ef7e525500bfe292a83bdf149541dffc84aa0effc4255077ff192a83bff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa00efc6155077ff90aa83bff085541d7fec0aa0eaff6055075ff302a801bf981541d7fac0aa0eafd6055075fe302a801bf1815402ffea0aa0eb7f5055075ff282a83aff541541d6faa0aa017fc5055075ffa02a83aff901541d7fa80aa0ebfc4055075ff982a83aff8c1541d7fa
  | 12 => 0x55b06f00000002e4198884477673f07b210540600000001053dc00036d8000e609d036a998c0000004b9800000011132980006b80eb00000008c294312a9d3c91249f08e000072c000000036c0006a30000d2c95e0002d294bc0000864e88000000000000000096e000000000000040b0000000d760003be976107e7821bc06ac57000000001091a60000000000000422000000143633b00000000006fc41117680000003cea6c80000000eb00009fc9c51ad00002dc00021800000000000000000188000000000000092f000000000000000000004480ab4b40c4c0007474bc2834b2800000024d09f000000000009d6996016800000000050a9cd403a0e713d94f80000000001c2c00000000000004d07eb00000011407441819b200000000000000000000107a5908a689b0000dc90a8896000000000097500000000ce0004fb87d80000000000000ecc11d220986030651e000158800078c1a8800000022816d80000000000000e4c000000000171d0923391e40080fdc00000028cc3de63b4fa192c00000000000000005d30001560e3815a32a8000b4c000000185407c00000000000006810000000000000413800000000046028103ae0000000ab135c9812f30c9800027a00000011147da35aa36c000000000000000033f16f80009526f1000000021c1f8000032400000014a26e8000000000188c0000403d90000dae0001b015f4000000373800000000000000000000002b2800000000035900000e076500015800000003b18870a04478000201c70a3b8000193c00000020515c8000000194000000078e4240000cf4000471800000062523e8000000000000000000039a1579e1c0000000bd8000000800000000079e16a11a80000000002d114a903c6f30000000ea864c00000005cc00000026f0000000000000000083c26898145989040000000000018010002005821108e20040100022190401008708041280403880010c041800000000008211882308401200000044000802004203946508401004021800100c65080a81040200045004600942001040180840000301822300020000a01c00008a0010830000100800010042082138c40024013800000840080400844200043200800000002c02100000002008801080050004419066080a01802008c0102504000052102000cc00002b000000800100000011810000009cc10044111400084201002418020000800986308001000021042000025094010180028081188401008001021084810000000040180000840006c800004018005180200100000020080000052300420004250006900003304200008200020100800242000c20084200002108243004430000000000080080200200020000a1004200840300162294201016a000611006608800018622248400400080410a0
  | 13 => 0x8000000000000000000019024289280a22f536e0000c8c0003080034a781e600000000000000000000c0e55f00000010c200018b27fd3ce00000000000000002c80000000a28000000000000041280000004c40000638b60193368911c000000000000054639c000100c00038f15f80000000003a9800000000030200000000000000000000000198000000070300015c40000000ef00010d40004e616183f26ad22900000000001d78000000000000000102c97231aa4907e4000000000116674e000000095c680000000108600047600000000000b380000000000000000a7400013c13e800000000000000000000001c1800068e1a68000000000000000000099b000000035c5e018fa39c51a04b4150000000000000014884a000000000056000000013a4000000000000000000000013b400042d36784d00002a800026f4de8000000000044200000023680000004c4a2b000068f0b5a7ac6a862c137a25094e55907b91fc3aa4c90000000932931153000050e0000000000c520001eb000051c000464a63800000000000000000000dc00000000000fd8000000000000000000000000010bd418000000086000000000000010de0000000fb8000078000000000000016c000000000000000007d0000000000000085800004dc62e922000000000071841980000009e113980000000000000000000440000000000000000027c49ce9f2000000000000000000000000000000ac901037100007180008992f0857c4842e20908b3c86a78a42d00000000000419bd87309150e500012c29bf4619ce8bf0000000162422a89221c9e6400010828a88000006781d427f00000000000db934000000000002f869800000000000b813389a8b7c0000000000aea992000000000000006300000000000001f180003430d380000007d8000000083c000000000000050b000000000021b0b422080000000000ce905600051a00000000000000260fcc8cd0000a5c84e20b00000580000003468adc000000000000000000000000440000000002054e4028c09e02b0df6792000019800000002d28880000004e20ed50200000001d6000000000000000003db11b91dc31630b000000000000000000000002d200008240000003c78f0c0000000000cf80000000001fbc00053732d000000000025115300009fe000000000000016392d8fc03072c691604980ad1d480008e8000000101519e3230002444be6000375a53400084e11c00000000000001b0400085e4818598000a2607a0000c7e00025e0000c702f236b0f9854a7dd00011206642c416000000000000001e0c0000000001cb800000018722f0a4a9d600024b8e080920000c88eae3be00000012000000002734000000000000000000000000c80009462e700645f2000100a0800000004cc09b12da
  | 14 => 0x5384db8cb119858e04803f49b88ab33b1908e423010f39fdc7087f32d593c800091739b977c97c0002a413c08d082100000000000002e900000002260000ec4000000000000068086d30e1268a6a8602f7800062473b00020b842a7f51ce8000f6e000000000142c00000002d51be0000000000e260000001de8f406724298c200000001ea800000083544aa5d09e60000a7a17000054909c23d134e1a23249e6071a0004ad884800066a20c800000000008280000008f10000000dbc2dd1bd05d09985f00e900004b82c50001ae48d400000009b878e0000001a300000000f28000000192000000135036934e05410e40c341482b915c66714582991189373ab00009160000000a6c7be8c800000000000000679f904b26e50000000eec61400025412167ce00000000003e3000000000010941300002c86340158ba400081c47b000000000000000010b23d0000099400000040516a40004372d607200004a80002678000000000276800000000000000000001e107dc0000000b89d80cfe7221c584e888c4fd1d006582964d5093a6acad000000014b910c9393e91ac400015b102000092c000000274800000000000000000000689000bae000000000000000030f0c784200000001208000187000228516e000000000000089700008e50f8000000141110642c2378330000000000000055a00034e8000ee20fc0000000000000000000000000000000000006f2454951c538920000010c24400001e00005761c74dd88a4e6c00000000010a28a321b17b86082460001bfc00008d00000003fe00000004580007f24c404fd3900001ae80c4c4c00000000005f48fb000182400000000000000007310001334c72483044249d2c09b62ec87f114a30f2881628a6249300016780001063a6800000079c3fa000130a00000016a80000000af16e400000041900000ee0000000000000873000000000093e047800056c0000001dc00000000000000000000000222ce3a0d6000165c0000aa36180000006fa0001a9800000050e02f0000000000270c00007448f000000000015995e0c740003f5182c0000000000000f6c00000000002fc00025e96bc0006f700005200b890f19b800000000000027000000004fd00000000004d9800000000044e8000a100000000000ac200035f94640004e83f2a81ca1495f08f07a11aa8232c28000bac00001407042fe0000820f188c600050f843062281b3541098f5e00000000000005c203f83c065a2c242804b40005574dc000033c6402c180000004150000000000000000000000000000000000004c100000004580000000000000000000000000066b00004a800001051200000004ec000000000000031b0394000000015097400045c00020240003ef00021a13b820800002f4280000501000108e00001f
  | 15 => 0xb800000016c3418000b920000001340d2c7c93d70000a8c2d92a89ab0000a0f28780000003974348000bda00024889f8a3a1690001ec400000027c86a8fa80000000db0a0c5fd2108f85234000000056000000043b0000b8c69500024d40d400049d0000000000000000000000015d116400000006914c000000000000000726fe236800075a7ca3761c900008310002290e200003a30e0c0009c748e8000000000000000012a4cb3ffa86458674b0000000496000000224d2ce7ab2c012982160004e992600002a400000000000000a600006829a52c1000003e000000000000000100013200000af000000000028a3d523e50e26e04f78000000a0b30d800007a95e0000e7d2c60000000f8068800000000006ea1024c000000000000001b7c000000000032000016f000215d0dc55205212c52420002eaa7746f600000007140000002390000000000000000086893c2ff166400000000026b400000013680000000d400004d474c00000000003b48bf3de00001f06c922681bc0060004f400003a20000001a892600000001ae000000000000002860000000000000000000000000078d000000140c00011780000000004d1a3f80000000000000ac600000018300006590000000ba00000180000f4218048c000000005d000000040e96e0c2076c6480000001b8c6da00046e800089c000000000000094f00000000000542fb000095660624e177800047c1d09514140044294a504fb633c3b400000000000000000a1a0000000364000707045911400009b09f09c0000000000000000099d3221aa543a7a2000070000000000000000c800001d0f6057c4d4000000016400000018c800000030092cc00000009da3500000000000000e040001dc83ec00000000000013969d948400000000000000000f9e0000000000010a292b61fe000087b0001f08000000000000000000025a9838000000000000060a00000000004867ad00000000000001c600000003ab51702fccac1b700024ac00000000015380006ce217255c00094a23980002300000001f4c0006900001484d100000710000000000000000000004800000000004c50000a3cf3e0e84068a080000002e524b40000001c900000000001b100000007bd00000e068a6ab4a90d3c00000000000005ec86b0000b8c72000000004686180000ec80980000004ab23fcc5c5030000000898000000000119c61326c083000096b18d0000da80001fd8f445ee0000000000ca21860001d080000000001fb4ffa00050508342481702c20a1400000000000000008633d480000000001aa9a7c8b44e5000000009a000000000128419736580000000000000d909280da2080d480000001d228480001b900000000000000a38000c4240103f215400000000000000008911e59ac062a1ba000131c00
  | 16 => 0x6331ca800020e06d00000000000000000a64e2e5280000000000091000000000036b4f003d47bc5b60000838ea400014f93b8ff80000000c800086000000ddc9a61890000000000000000000000000000000007ea00000011a46d00000000000b487a5000000000048a4c18000000000000199800000023b1c300004d900026c000087900023880000000001f3103499a12c07ac00000000000005f0a1e030215915a99100023640000000000000376000000000000000000000006bc4b436308686548f50000fd80000720000000000000000000000000027e1c7806c0000000000f506973e806503f400041c8001204000000125400000039180000000000000000000000000019400000002c800000000049c00010680003f800008400940d480008e200050800014421bd0031d9d258302000000131a00000000001a02d1016000000000046e0760eea3344b49fd923e6370cc1ce128a88d0f191b88962b11e9917834c9aa19c232c1ba41d13f800000000000000005446bd17010a514400039e25940006f53ea9ee132a00038882c52e200047ea6f8c5422d1e607c80f69ec00020f823600038a1430000000000000000065b00000000c40001ea0c64000000361000028c7cb3c423e8eee3744da800049a0583450000000000000000000000000d800000023600000005060ba00596800009400cd8000000000000000003008a06c2610ba27ac3218000000000097000012e0000000000000000000000000000039795280000002a1a4f400000000015d00000001fa284cfac00000000001aa02f29a000086400008797c4bd42ea00022f8cba00000000000009e5000082800000017880000001e43fd80000e6959000000049e4600000000000000000000000072d1b2982850c00004123a40000000000000e684ff39380011767914fea0b49d43b200000000006bc4ed8000a4e61700001186fca1700000004ec22a3cb00500007813afa064000000000000097247b12380000000000000b0400000031880000000000001a440002140000000c9413000000000000000001c1452048c00000000000000d80070d4e9ce3d20000250000000013cfbe000000015800000049300000006861c48094ce20000000f480007080000000b166b40000000000907000000000028005b800000000000018481440004bc927400000006580000000000000000b342cb00000000006e62358878da666200015fc6ce00000021880000001de9e0000070f0000258f4600012a183c44400c00027604cc00000000011d66d04a4863000000018e8000e7a0000000a840d00000708bfc000000000000000090d00022a8000000000166c00000000002a00006af000130800000014b148000015400000003d820300023780002d5000000000097b47
  | 17 => 0xc000000000000000000008b10900000c503ff1e215580ec57b00000000000000000b400009290612269348213472800000012b3520000bee00000000000000000000fcc00044300000007660000000fb480ea2005d80009f698200000007820000000000000a3033680000000000000eb8f7c0000001c24f90000000000000000000000004be0001738000d8a1cb04387b466c97f2a0000000000021d20a000089f2f3a12c00000000005545940001188a100005260389d4400015d000000000065225c00008f28d200022249ac70e000000000000046c000000030009c80013ae0000000000d3c000240000076c81200001b800051100027a400000046500000000000000000000000000185800400043f15100005ba0001d403ea00032f00000000003508bb00006c744c22d800005b0002210bd69050db00004a000f00000000000000001c9800064800000000000000000000af800019a8000efc40827000000000000000000e989320000000b38000280a530b2a119000014000000036000002a267c0000000d66000000000000000000007a92905131550000000000444000000000000019d40000e00000f5c6a000037800000465bc43f8000964000341235c0000004dc80000000000000000c8e000000000000002213e13880147741ff05f40002633e68b20000a181ac0000f4c75a4b600010f41fe00000005120004c6000000000027300000001721a71980f889d400003a800e00000025bd18e0004bb0e380003ec0001950a96428129000125484612400004e400000000000009f000000000000003e8800000079b2f91a1c0000000a49dfc000000267862000000037207c40f44bb2a0899000000000000000000000000ad4000000000000000000000000000000000da0000c441be2f4000000000037c80009ba0000000cbc0008750002708000000000000000022033f00008ac5183770000eb297c0000000fd200000000000003100001938cca9f800000000003fa0001704000a2f00003980007f12fd054cc485b500000004ae7b9000000000000030d00010c8000000000000000000000000000000000000000000000000000062d000125c0d600000000000005542b9800078a0004bb85d40000000000b5c00000000024cc0000002af09d400004a0000000a7e3ca3d80000000000000166000000000000006c69a200005854585a300009012245e52b814ec3b8000000073c00000035b90f889e21f00000000000000098dc00000000b2800000000000000000006930000000000000000173c0008243370000000a014bf03c400000014900000007fe04f0000000260000030474e4a01a61a8035e00000000003dc3061e68000f7e00000012c00005dd41b05080007642fa80010b60001ca000134c00000000005ac69a00000000
  | 18 => 0x6451ad84944823b000000000000000ef80000000000000000000000000014c8a81ad00000002a48f2000160400000021200003a8564000000141000000020e800000000023e06ec8c517e0e950608d103c9658a280000000000f74000394a8a80000002651ccc0c60000001bbc00067000000003c233300027d4b7a00045c916ced40f21aca8146f20a332b80000000fa000000090200000018c000016d0bc0000f26348000000000093b43800011dc0000000000000000000034c00000000017e400000000000000000000000000acc0001500a049543800000000000000000000000000000000000000004b8000000044229e8694000000000000083800000000000000000000000000132000000000090c00000006924570001b34bc60472a9939000000000000000001560000000a1c00000000000000004c98000000000000239000004c2ae97fca2c08423f2114000000000000118423c000000070c14d00000000000000f0167400012c2df8000942000009000000032e4a89f000000000000e28f6a3f005c9a50000206000000064a46646310ad076000000031c0000004730000000593000000000088100000000003d9000000145a1170002428e1a0e400000000000000001c940000001b7800039845f000000091035f000000000000021d80000004e332e000027a0002b5a02c36a00000000000008030000000000000127146c9080be194983400000038f8af464e0000000000cd20000000001296000000000117400044800008f47012e206641c67f912d8000000000208800045c2694e5000000000000024503a00000f48000d3600000000007f000024706c87d443f00024a0000000000000000000014d0000000000000000000074800012480001232c88d1cd0a00035500000000000000b84000000000087400090600011280008e000000002c600000025540006640529534000000000000000040213883b4000000119000000019c0471b48ebc7120000958000475000149082600000000000005f400020f40000004780000000309330800000000047500000000002e68000000000000190402e000491894c0000000000bf52202d4000000052a00003e870c0000000000000c060004d8953c8660000001e68e2c2ed4ef88cc366a093d39fa0a6c0ff480800068427700000008c800017997ec98c58c22a976ce5010333d8774ef00000001db115e1620001f1d41c00022888f800061d000187c000a113cb9ba80006dd00012b52f4000000000090c75d000000000050500021b000000010ca5100000b43f3a65c39a9e6000147130e00000010f05dc00006e21946e611f0000000000000000000000000040f8c50e540c52e280ec00010d000000000083700000000008110348000bc87e300009103420290000000d740002
  | 19 => 0x474119c9a40000000000ef600013c80000007552f4994047e99f00026bc0000000000000000000000000000000013e80000002fe0001b30b1e0000002640f128ed00026b10f0000000000000000031f000075855c013800063662000002c0b4e3dd2bd00b917066836ca1f4ef82cd0000000000000479a63c00011217a00000000000000a4c58c25a2b4801468c245000000000030a0000000744356442800071000018c22d4000000000000000000000022380000000000000fae0001f2800000000000000013aa86611a089c3146da000126c000936000000000007c0000000358470000000019c78b3a500000001d3211a85000000000000000009f30669384000000000180800099900022a0000000000000000000000000013da0000000ed00000f34e7800000051200017713285884fb1a249ec30d02aa0bc00000000015b83883eb2dd8bbc00076f16f189d11e29e00023f0a3e0000000000fb298b000000000072b1c382252d40000001c6c000000519000000085d2e42790f820000000000000000416000008a1450000000aa00000000000b5019d1fe800000049000017888285001ab93dcbf800000000000002e83dda4fc00000000000000007b4000000076e0d731e063c00008148c9b1010a00000000000000000000000ee600000000000009b4000203102e000000026400000028d000000000000000000005d400a8000f2009f4c300007b84442cf800031a555000170d18270a000000081a5770000000000000000145c00073e0002008b6e60800022703920002328000b6600000027a88544380000000db00000000000b8066c0000fe40000000000000d0800000001d400048f00000005520002d089791de000426a17cfbc000000000122c20500005802020b6513867c0000242f608587543e720b1db8f664df065020037e0003b90a9c0000000000e081422300000000dda0003529038000179518a1484740000000000000110000080916474029589240003660002470000000000000077800044380000000002b78000722000000000000001e00000000000000000af00000000000000000000400984459284034580cc9ea00000000000001b138000006a652d37080000009c900005e85d60a700000dc5f62ab4ae80003e80004ac000000000000000005721000d2000000044920d80000005320001cc80000000001de400076d0001bf400031c46b04980005b81f2000000000000027180000002da000097e00034c83a401c00000000012a615c0000000d5c76b00000000001c22918c84746000000000000000000010c400000000022d07e20000001b280000000000b940005cc00008ec000867000164800039e00000008d82ae000000000040f47080000000000001d14000000000000081898a00000000000000001fe8
  | 20 => 0x2d30000cac1dc00000000000006e944008940007dc0778000152000000242400000027a0000a580002d693007363e2000008413850743b99dc39c56d000000099c000000000087a8050c280005e00004fc80003fa0000de251d3bc65f000000009200039609d0f2800000008ac1be0003740000ad48a600002cc0000000000ee800078649280010e80002468b704a20000000e04e825224d09d88afc009339800000000000013780008140000000e3400000000009483f72e5a78c00055a0000fa40000000000000000000261800000000000000005680000001f84000000000246c8c4000000000000000000000004460003c2a7ecdf0000000026847a0004e08000dc400000000000000000ab9d700000000000a60b62000000000000005e0000dfc00000000000000007c3000129400000000000000007693cf0000a123bf468000000000000000000000000000000000000000053800000001aa570000761000196000000025d000033469216d14e40000fe0000000b5c00020905105228a70ac9f142e684f38c9d0c95812f1be8e6479c80e1ed0000e2a0004f106a022600000006446947ec085107c2ee1330c08cf400000000025989ae6193c2000100c05f5158000282a250000000a6600000000012b41e22281d6d33800000000014340003379174ce857600012780000000000000000000000000000080f326a5887f80c01308000cfa3614bea074f2a26250007c02283c90000274000000144000090e0340000000af200000000000000000001ad81181a300000000000000000000e92838049800000041a00000000008440a50000b6400009b00009b67390ca8000c5629d20213c4000000036000026200033c80009de1a000003e40000003f10000000417000102500800000009ac00084a26d244c2520000000000000567251a2c0000000511800059c9a92030000000000000000000000040c000030400031780000006be0bb24386f8000000231108400045e8000000000030800000000000000007808130000da800063d00025380ae04e10ba5500005424260000b0e89e00007cc0340ec
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc6558d2107df77158d21004ff7558d210067f7558d210047f7558d2102cfc7558d210067c7558d2102c7c7558d21004ff7458d2108cfc7458d21006df7358d21064ff7258d21006ef7258d21004ef7258d2107cff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d21066ef2058d21006ed2058d21074fe7618d210067f6518d210067c6518d21006dd6318d2102cfe7518d21004fd7518d2108cfe7418d21004fd7418d21046de7318d2101cff7218d21014fe7218d2101cfd7218d21014fc7218d21046df3218d2104edd3218d2101cfe7118d2101cfc7118d211feee2118d211feec2118d21044ff7018d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21046dc3018d2104eef2018d21006ed2018d2102cff76d4d21004fe76d4d21004fd76d4d2102cfc76d4d210067f65d4d2102e7c65d4d21044ff7694d21004fe7694d21004fd7694d21044fc7694d210067f6594d2102e7c6594d210075f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2102e7c6554d21044ff7614d21004fe7614d21004fd7614d21044fc7614d210067f6514d2102e7c6514d2108cff76d0d21004fe76d0d21004fd76d0d2108cfc76d0d210057e75d0d210057d75d0d210067f65d0d210067c65d0d21006bf64d0d2108ebc64d0d21044ff7690d21004fe7690d21004fd7690d21044fc7690d210057e7590d210057d7590d210067f6590d210067c6590d21006df6390d21046dc6390d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210067f6550d210067c6550d21006bf6450d21006bc6450d21006df6350d21006dc6350d21044ff7610d21004fe7610d21004fd7610d21044fc7610d210067f6510d210067c6510d210079d4310d21015ee7210d21005ed7210d21014fe76d4521014fc76d45210067f65d452102e7c65d4521015ee72d4521005ed72d452101f7651d452102cff7654521014fe76545210e4fd7654521014fc76545210067f655452102e7c6554521005ef7254521015ec725452101fe42154521014fe76d0521014fc76d05210067f65d05210067c65d0521006bf64d052108ebc64d0521015ee72d0521005ed72d052101fe421d052108cff7650521014fe76505210acfd7650521014fc76505210057f75505210057c75505210067f65505210067c6550521006bf6450521006bc6450521005ef7250521015ec7250521014fe76cc521014fc76cc5210067f65cc5210067c65cc521006df63cc521046dc63cc521015ee72cc521005ed72cc52101fe421cc521044ff764c521014fe764c521064fd764c521014fc764c5210057f754c5210057c754c5210067f654c5210067c654c521006df634c521006dc634c521005ef724c521015ec724c521
  | 1 => 0x9121004fd70d912100cfc70d9121006be40d9121006bc40d91210beef20d9121006ed20d91210057e75991210057d75991210067f65991210067c6599121006bf6499121005de7399121005dd73991210adf5719912102cfe759912108e7e759912102c7e7599121004fd759912108e7d75991210047d759912108cfe7499121044fe739912108ede7399121004de7399121004fd739912108edd7399121004dd73991210c4fd729912108eed72991210acfd719912108ef57199121216ee2199121216ec219912108cff709912100cfe7099121004fd709912100cfc70991210c6ef2099121006ed20991210057f75591210057c75591210067f65591210067c65591210c5f77159121004ff75591210067f75591210047f755912102cfc75591210067c755912102c7c7559121006bf7459121004ff7359121044fc73591210acff7259121006ef7259121004ef72591210c4ff7159121006f77159121004ff705912100cfe7059121004fd705912100cfc70591210aeef2059121006ed20591210bcfe76191210067f65191210067c6519121006bd641912102cfe7519121004fd751912108ebe7419121044fe7319121004fd731912101cff7219121014fe721912101cfd7219121014fc721912108ebf4219121096bd421912101cfe711912101cfc711912120eee211912120eec211912108cff701912100cfe7019121004fd701912100cfc7019121006be401912108ebc4019121096ef2019121006ed201912102cff76d5121004fe76d5121004fd76d512102cfc76d51210067f65d512102e7c65d512108cff7695121004fe7695121004fd769512108cfc76951210067f659512102e7c65951210073f5495121004ff7655121004fe7655121004fd7655121004fc76551210067f655512102e7c655512108cff7615121004fe7615121004fd761512108cfc76151210067f651512102e7c65151210067f65d8d210067c65d8d2102cfe75d8d21004fd75d8d2108cfe74d8d21004fd74d8d2101cff72d8d2101cfd72d8d21076df32d8d21076dd32d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21076ef20d8d21006ed20d8d210057e7598d210057d7598d210067f6598d210067c6598d21005be7498d21005bd7498d21006df6398d21065f57198d2102cfe7598d210467e7598d2102c7e7598d21004fd7598d210467d7598d210047d7598d2108cfe7498d21046be7498d21004be7498d21004fd7498d21046bd7498d21004bd7498d21044fe7398d2107cfd7298d21046ed7298d21064fd7198d21046f57198d21206ee2198d21206ec2198d21044ff7098d2100cfe7098d21004fd7098d2100cfc7098d2107eef2098d21006ed2098d210057f7558d210057c7558d210067f6558d210067
  | 2 => 0xf6ef20d9521006ed20d952102c7e76d95210f77721d952122f6e21d952122f6c21d95210f77421d95210067f60d95210067e60d95210067d60d95210067c60d95210f76f20d95210076d20d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d952122e7f72d95210f67e72d95210f67d72d95210f67c72d95210f67f42d95210f67e42d95210f67d42d95210f67c42d95210f67f32d95210f67e32d95210f67d32d95210f67c32d95210f67f71d952122e7e71d95210f67d71d952122e7c71d952122e7e41d952122e7c41d952122e7e31d952122e7c31d95210f67f21d952122e7e21d952122e7c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067f30d95210067e30d95210067d30d95210067c30d95210f67f20d95210f66f20d95210f67e20d95210f67d20d95210066d20d95210f67c20d952122e7f10d95210067e10d95210067d10d952122e7c10d95210067f6599521226ef62995210e5f57199521105f771595210067f7559521004ff745952108cfc7459521004ff7359521044fc73595210e4ff7259521006ef7259521004ef7259521104ff7159521006f77159521004ff705952100cfe7059521004fd705952100cfc70595210e6ef2059521006ed20595210f4fe761952102e7e65195210067d651952121eef62195210f57e76195210067e76195210f47e76195210d777211952121f6e211952121f6c21195210d77421195210067f60195210067e60195210067d60195210067c60195210d76f20195210076d201952102e7f741952102e7e741952102e7d741952102e7c741952102e7f731952102e7e731952102e7d731952102e7c731952102e7f721952102e7e721952102e7d721952102e7c72195210d67f42195210d67e42195210d67d42195210d67c42195210d67f32195210d67e32195210d67d32195210d67c321952102e7f711952102e7e711952102e7d711952102e7c711952121e7e411952121e7c411952121e7e311952121e7c31195210d67f211952121e7e211952121e6e21195210d67d211952121e7c211952121e6c211952102e7f701952102e7e701952102e7d701952102e7c70195210067f40195210067e40195210067d40195210067c40195210067f30195210067e30195210067d30195210067c30195210d67f20195210d66f20195210d67e20195210d67d20195210066d20195210d67c201952121e7f10195210067e10195210067d101952121e7c10195210067f65d91210067c65d912102cfe75d9121004fd75d9121044fe73d9121004fd73d912101cff72d912101cfd72d91210bebf42d91210bebd42d9121004ff70d912100cfe70d
  | 3 => 0xc7098e2107eef2098e21006ed2098e21004ff7558e2102cfc7558e21004ff7458e2108cfc7458e2101edf7358e21006ef7258e21066df3258e21066dd3258e21066ec3258e2101cff7158e2101cfe7158e2101cfd7158e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e2100cfe7058e21004fd7058e2100cfc7058e21066ef2058e21006ed2058e2102cff76d4e2101cfe76d4e21004fd76d4e2101cfc76d4e2102e7e65d4e210067d65d4e21015ee72d4e21005ed72d4e211b76c52d4e21044ff7694e2101cfe7694e21004fd7694e2101cfc7694e210075f5394e21015ee7294e21005ed7294e21004ff7654e2101cfe7654e21004fd7654e2101cfc7654e2102e7e6554e210067d6554e21005ef7254e21015ec7254e2119f6c5254e21044ff7614e2101cfe7614e21004fd7614e2101cfc7614e21015ec7214e2108cff76d0e2101cfe76d0e21004fd76d0e2101cfc76d0e210057e75d0e210057d75d0e21015ee72d0e21005ed72d0e21044ff7690e2101cfe7690e21004fd7690e2101cfc7690e210057e7590e210057d7590e21015ee7290e21005ed7290e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e21005ef7250e21015ec7250e21044ff7610e2101cfe7610e21004fd7610e2101cfc7610e210079d4310e21015ec7210e21225ed76d4a21246ed76d4a21015ee75d4a210176e75d4a21226ef65d4a212276e65d4a21246ed65d4a212276d65d4a210066d65d4a21005ee74d4a21005ee73d4a21227e671d4a21225ed71d4a21247e571d4a21005e571d4a21016ee61d4a21017e661d4a21245ef70d4a21265ed70d4a21226ef60d4a2125eed60d4a21215ed76d0a21006ed76d0a21245ee75d0a210076e75d0a210056e75d0a210076d75d0a21245ec75d0a21015ee74d0a21017ae74d0a21216ef64d0a21217ae64d0a21006ed64d0a21217ad64d0a21005ee73d0a21217e671d0a21215ed71d0a21007e571d0a21016ee61d0a21017e661d0a21255ef70d0a21255ed70d0a21216ef60d0a2124eed60d0a21205ed76cca21006ed76cca21245ee75cca210076e75cca210056e75cca210076d75cca21245ec75cca21005ee74cca21005ec74cca21015ee73cca21017ce73cca21206ef63cca21207ce63cca21006ed63cca21207cd63cca21207e671cca21205ed71cca21007e571cca21016ee61cca21017e661cca2123def70cca2123ded70cca21206ef60cca21236ed60cca2102cfe76d952108cfe74d9521004fd74d9521044fe73d9521004fd73d952101cff72d9521014fe72d952101cfd72d9521014fc72d95210f67f52d95210f67d52d952101cfe71d952101cfc71d9521004ff70d952100cfe70d9521004fd70d952100cfc70d95210067f50d95210067e50d95210067d50d95210067c50d9521
  | 4 => 0x883101eee215883101eec2158831004ff705883100cfe7058831004fd705883100cfc705883104eef2058831006ed205883102cff76d483101cfe76d4831004fd76d483102e7e65d48310067d65d483104f6e52d4831004ff7654831004fd765483101cfc765483102e7e65548310067d6554831005f7715483101df4715483108cff76d083101cfe76d0831004fd76d08310057e75d08310057d75d08310067e65d08310067d65d083108ebe64d0831006bd64d0831045de73d0831005dd73d083101df671d0831005f571d0831004ff7650831004fd765083101cfc76508310067e65508310067d6550831006be6450831006bd6450831016ee6250831006ed625083107cff764c8310067e654c8310067d654c83101df7764c431006f7764c431004f7764c43100777754c43100774754c43101f76654c43101f75654c43101df7734c43101fd7734c431046f6634c43101fd6634c431047d6534c431007d5534c431007e7724c431007e4724c43101ef7604c431276f5604c43126fe7204c43126fe5204c43101e7f7559621004ff745962108cfc7459621004ff7359621044fc7359621006ef72596210e67f52596210e67d52596210e6ec525962101cff715962101cfe715962101cfd715962101cfc715962101e7e515962101e7c5159621004ff705962100cfe7059621004fd705962100cfc70596210067e50596210067c50596210e6ef2059621006ed205962102cfe7599221004fd759922101ebe7499221044fe7399221004fd739922108ebf42992210c6bd429922101cfe719922101cfc719922101ebe419922101ebc419922108cff709922100cfe7099221004fd709922100cfc70992210c6ef2099221006ed2099221004ff755922102cfc755922101ebf7459221004ff7359221044fc7359221006ef72592210aebf42592210aebd42592210aeec425922101cff715922101cfe715922101cfd715922101cfc715922101ebe415922101ebc4159221004ff705922100cfe7059221004fd705922100cfc70592210aeef2059221006ed205922102cff76d522101cfe76d5221004fd76d522101cfc76d522102e7e65d52210067d65d5221015ee72d5221005ed72d52211f76c52d522108cff769522101cfe7695221004fd769522101cfc76952210073f5495221015ee7295221005ed7295221004ff765522101cfe7655221004fd765522101cfc765522102e7e65552210067d6555221005ef7255221015ec72552211df6c525522108cff761522101cfe7615221004fd761522101cfc7615221015ec721522102cfe7598e21004fd7598e2108cfe7498e21004fd7498e2101ede7398e21046df3298e2107edd3298e2101cfe7198e2101cfc7198e2101ede3198e2101edc3198e21044ff7098e2100cfe7098e21004fd7098e2100cf
  | 5 => 0x1e7c5159431004ff705943100cfe7059431004fd705943100cfc70594310067f50594310067e50594310067d50594310067c5059431006ef2059431006ed20594310067f74594310067e74594310067d74594310067c74594310467e73594310467c73594310467e43594310467c43594310067f72594310067e72594310067d72594310067c72594310067e42594310067c42594310467f32594310067e32594310467c325943101e7f715943101e7e715943101e7d715943101e7c715943101e7f415943101e7e415943101e7d415943101e7c415943101e7f315943101e7e315943101e7d315943101e7c315943101e7f215943101e7e215943101e7d215943101e7c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067d40594310067c40594310467f30594310067e30594310067d30594310467c30594310067f20594310066f20594310067e20594310067d20594310066d20594310067c205943101e7f105943101e7e105943101e7d105943101e7c105943102cfe7599031004fd759903101cfe749903101ebe7499031044fe7399031044fc7399031046be4399031046bc4399031014fe7299031004fd7299031014fc729903101cfe719903101cfc719903101ebe419903101ebc419903108cff709903100cfe7099031004fd709903100cfc709903108ebf4099031006bd4099031006ef2099031006ed2099031004ff755903102cfc755903101cff745903101ebf745903108cff7359031044fe735903115cfd7359031044fc7359031046be4359031046bc4359031004ff7259031014fe7259031014fc725903101cfe715903101cfc715903101ebe415903101ebc4159031004ff705903100cfe7059031004fd705903100cfc7059031006bf4059031006bd4059031006ef2059031006ed205903102cff76d503101cfe76d5031004fd76d503101cfc76d503102e7e65d50310067d65d503108cff769503101cfe7695031004fd769503101cfc769503102e7e65950310067d65950310073f5495031045de7395031005dd7395031004ff765503101cfe7655031004fd765503101cfc765503102e7e65550310067d6555031005f7715503101df4715503108cff761503101cfe7615031004fd761503101cfc761503102e7e65150310067d6515031004fd76d4c3102e7e65d4c310067d65d4c310475e53d4c31004ff7654c3102e7e6554c310067d6554c31004fd76d0c310057e75d0c310057d75d0c310067e65d0c310067d65d0c31004ff7650c310067e6550c310067d6550c310479c4350c31004ff755883102cfc7558831004ff745883108cfc7458831014fd735883101eef725883104eee4258831046ef3258831046ec325883101cff715883101cfd715883101cfc715
  | 6 => 0xf655493102e7c6554931006ef6254931016ec6254931004fe76d0931004fd76d093108cfc76d09310057e75d09310057d75d09310067f65d09310067c65d0931006ef62d0931016ec62d0931004ff7650931004fe7650931004fc76509310067f65509310067c6550931006ef6250931016ec6250931005f7715093101df47150931074fe76cc9310057e75cc9310057d75cc9310067f65cc9310067c65cc931016ec62cc93101cfc764c9310067f654c9310067c654c931006ef624c931016ec624c931005f7714c93101df4714c931004fe76d4531044fc76d45310067f65d453102e7c65d4531005de73d4531005dd73d4531006ef62d4531106ec62d453101f7651d453102cff7654531004fd765453102cfc76545310067f655453102e7c6554531005df7354531005dc7354531005ef7254531065ec7254531006ef62545310e6ec625453101fd43154531004fe76d05310067f65d05310067c65d0531006bf64d053108ebc64d0531005de73d0531005dd73d0531006ef62d05310c6ec62d053108cff7650531004fd7650531004fc76505310057f75505310057c75505310067f65505310067c6550531006bf6450531006bc6450531005df7350531005dc7350531005ef7250531065ec7250531006ef62505310aeec62505310067f65cc5310067c65cc53101dde73cc53101edf63cc531006ef62cc53107eec62cc53100cf676cc5310077765cc5310077465cc53101df673cc53101ef763cc53101fd763cc531007e762cc531007e462cc531045f770cc53127df570cc53127fe720cc53127fe520cc53102e7f749943102e7e749943102e7d749943102e7c74994310467e73994310467c73994310467e43994310467c439943102e7f729943102e7e729943102e7d729943102e7c72994310067e42994310067c42994310467f32994310067e32994310467c329943101e7f719943101e7e719943101e7d719943101e7c719943101e7f419943101e7e419943101e7d419943101e7c419943101e7f319943101e7e319943101e7d319943101e7c319943101e7f219943101e7e219943101e7d219943101e7c219943102e7f709943102e7e709943102e7d709943102e7c70994310067f40994310067e40994310067d40994310067c40994310467f30994310067e30994310067d30994310467c30994310067f20994310066f20994310067e20994310067d20994310066d20994310067c209943101e7f109943101e7e109943101e7d109943101e7c109943101cff755943101e7f7559431004ff745943108cfc745943102cff7359431044fe735943102cfd7359431044fc73594310467e53594310467c5359431004ff7259431014fe7259431014fc72594310067e52594310067c525943101cfe715943101cfc715943101e7e5159431
  | 7 => 0xd310067f65d0d310067c65d0d31006bf64d0d3108ebc64d0d31176ec62d0d3101df671d0d31005f571d0d31004fe7690d310057e7590d310057d7590d310067f6590d310067c6590d3116eec6290d3101cfc7650d310067f6550d310067c6550d31006bf6450d31006bc6450d31166ec6250d31005f77150d3101df47150d31004fe7610d310067f6510d310067c6510d310079d4310d31146ec6210d31014fe76d89310067f65d89310067c65d8931066ee62d893102cfe75d8931004fd75d893108cfe74d8931004fd74d893101cfd73d8931014fc73d8931066ee52d8931066ec52d8931066ee42d8931066ec42d8931066ee32d893101cfe71d893101cfc71d8931066ef21d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931066ef20d8931006ee20d8931006ed20d8931066ec20d8931065ee76d8931014ee76d8931006ef65d89310076f65d89310066f65d8931006ee65d8931006ed65d8931006ec65d89310076c65d89310066c65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d8931207ce31d8931207cc31d8931005ef70d8931005ed70d8931006ef60d8931006ee60d8931006ed60d8931006ec60d8931007e710d8931007e510d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931206ef73d8931066ee73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d8931206ee71d8931006ed71d8931206ee51d8931206ec51d8931206ee41d8931206ec41d8931206ee31d8931206ec31d8931006ef70d8931004ef70d8931006ee70d8931006ed70d8931004ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d8931006ef30d8931006ee30d8931006ed30d8931006ec30d8931206ef10d8931006ee10d8931006ed10d8931206ec10d89310057f75589310057c75589310067f65589310067c6558931066ec6258931005ee7618931066ee7618931006ef65189310076f65189310066f6518931006ee6518931006ed6518931006ec65189310076c65189310066c6518931006ef6418931006ee6418931006ed6418931006ec64189311feef63189311ffce31189311ffcc3118931065ef7018931005ed7018931006ef6018931006ee6018931006ed6018931006ec6018931007e71018931007e51018931004fe76d4931004fd76d493102cfc76d49310067f65d493102e7c65d4931006ef62d4931016ec62d49310676e52d4931004ff7654931004fe7654931004fc76549310067
  | 8 => 0x67d20195310066d20195310067c20195312867f10195310067710195310067e10195310067d10195310067510195312867c10195310067f65d91310067c65d913102cfe75d9131004fd75d9131014fe72d9131004fd72d9131014fc72d9131004ff70d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d9131006ef20d9131006ed20d9131006f710d9131006f510d91310057e75991310057d75991310067f65991310067c6599131006bf6499131065ee7299131005ed729913102cfe759913108e7e759913102c7e7599131004fd759913108e7d75991310047d759913108cfe7499131004fd739913108edd7399131014fe729913108eee7299131014ee7299131004fd729913108eed7299131004ed7299131014fc7299131004fd719913108ef5719913108cff709913100cfe7099131004fd709913100cfc7099131006ef2099131006ed20991310057f75591310057c75591310067f65591310067c6559131005ef7259131065ec7259131005fb705913105df87059131004ff75591310067f75591310047f755913102cfc75591310067c755913102c7c7559131006bf7459131004ff7359131006df7359131004ff7259131006ef7259131004ef7259131014fe7259131014fc7259131006ec7259131014ec7259131004ff7159131006f77159131004ff7059131006fb7059131004fb705913100cfe7059131004fd705913100cfc7059131006f8705913100cf87059131006ef2059131006ed2059131006f71059131006f51059131004fe76191310067f65191310067c6519131006bd641913102cfe7519131004fd751913108ebe7419131044fe7319131044fc7319131014fe7219131004fd7219131014fc721913108cff701913100cfe7019131004fd701913100cfc7019131006be401913108ebc4019131006ef2019131006ed201913102cff76d5131004fe76d5131004fd76d513102cfc76d51310067f65d513102e7c65d5131005de73d5131005dd73d51311f6ec62d513108cff7695131004fe7695131004fd769513108cfc76951310067f659513102e7c65951310073f54951311e6ec6295131004ff7655131004fe7655131004fd7655131004fc76551310067f655513102e7c65551311deec625513108cff7615131004fe7615131004fd761513108cfc76151310067f651513102e7c65151311c6ec621513101cfe76d4d3101cfc76d4d310067f65d4d3102e7c65d4d311b6ec62d4d3101df671d4d31005f571d4d31004fe7694d310067f6594d3102e7c6594d310075f5394d311a6ec6294d3101cfc7654d310067f6554d3102e7c6554d3119eec6254d31005f77154d3101df47154d31004fe7614d310067f6514d3102e7c6514d31186ec6214d3101cfe76d0d310057e75d0d310057d75d
  | 9 => 0x673cc631047d653cc631007d553cc631045f770cc631295f570cc631297e720cc631297e520cc63102cfe76d953108cfe74d9531004fd74d9531044fe73d9531044fc73d9531014fe72d9531004fd72d9531014fc72d95310067e52d95310067c52d9531004ff70d953100cfe70d9531004fd70d953100cfc70d95310067f50d95310067e50d95310067d50d95310067c50d9531006ef20d9531006ed20d953102c7e76d95310067e62d95310067c62d953128f5e31d953128f5c31d95310067f60d95310067e60d95310067d60d95310067c60d95310076f20d95310076d20d95310077710d95310077510d95310067f74d95310067e74d95310067d74d95310067c74d953128e7f73d95310067d73d95310067f72d95310067e72d95310067d72d95310067c72d95310067e42d95310067c42d95310067e32d95310067c32d95310067f71d953128e7e71d95310067d71d953128e7c71d953128e7e41d953128e7c41d953128e7e31d953128e7c31d95310067f21d953128e7e21d953128e7c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95310067f30d95310067e30d95310067d30d95310067c30d95310067f20d95310066f20d95310067e20d95310067d20d95310066d20d95310067c20d953128e7f10d95310067e10d95310067d10d953128e7c10d95310067f6599531065ee7299531005ed7299531005ef7259531065ec72595310067f7559531004ff745953108cfc7459531004ff7359531006df7359531004ff7259531006ef7259531004ef7259531014fe7259531014fc7259531006ec7259531014ec7259531004ff7159531006f77159531004ff705953100cfe7059531004fd705953100cfc7059531006ef2059531006ed2059531004fe761953102e7e65195310067d65195310057e76195310067e76195310047e76195310067e62195310067c62195312875e31195312875c31195310067f60195310067e60195310067d60195310067c60195310076f20195310076d201953100777101953100775101953102e7f741953102e7e741953102e7d741953102e7c741953102e7f731953102e7d731953102e7f721953102e7e721953102e7d721953102e7c72195310067e42195310067c42195310067e32195310067c321953102e7f711953102e7e711953102e7d711953102e7c71195312867e41195312867c41195312867e31195310067d31195312867c31195310067f21195312867e21195312867c211953102e7f701953102e7e701953102e7d701953102e7c70195310067f40195310067e40195310067d40195310067c40195310067f30195310067e30195310067d30195310067c30195310067f20195310066f20195310067e2019531
  | 10 => 0x473108ebe64d0731006bd64d0731045de73d0731005dd73d07310057f75507310057c7550731006be6450731006bd6450731005df7350731045dc7350731005ef725073107dec725073101e7f7559631004ff745963108cfc7459631004ff7259631014fe7259631014fc725963101cfc715963101e7e515963101e7c5159631004ff705963100cfe7059631004fd705963100cfc7059631006ef2059631006ed205963102cfe7599231004fd759923101ebe7499231014fe7299231004fd7299231014fc729923101cfe719923101ebe419923101ebc419923108cff709923100cfe7099231004fd709923100cfc7099231006ef2099231006ed2099231004ff75592310067f75592310047f755923102cfc75592310067c755923102c7c755923101ebf7459231004ff7259231014fe7259231014fc725923101cfc715923101ebe415923101ebc4159231004ff705923100cfe7059231004fd705923100cfc7059231006ef2059231006ed205923101ef71059231006f5105923102cff76d523101cfe76d5231004fd76d523101cfc76d523102e7e65d52310067d65d523108cff769523101cfe7695231004fd769523101cfc76952312a67f659523102e7c659523108ebe6495231006bd64952310073f5495231005de7395231005dd7395231004ff765523101cfe7655231004fd765523101cfc765523102e7e65552310067d6555231006be6455231006bd645523108cff761523101cfe7615231004fd761523101cfc761523129e7f651523102e7c651523102e7e65d4e310067d65d4e3101df671d4e31005f571d4e3128e7f6594e3102e7c6594e310075f5394e3102cff7654e3102e7e6554e310067d6554e31005f77154e3101df47154e312867f6514e3102e7c6514e310057e75d0e310057d75d0e3108ebe64d0e31006bd64d0e3101df671d0e31005f571d0e310057e7590e310057d7590e31006be6450e31006bd6450e31005f77150e3101df47150e310079d4310e31004ff7558a310067f7558a310047f7558a3102cfc7558a310067c7558a3102c7c7558a31004ff7458a3108cfc7458a3101eef7258a31076ee3258a3101cfc7158a3101eee2158a3101eec2158a31004ff7058a3100cfe7058a31004fd7058a3100cfc7058a31076ef2058a31006ed2058a3102cff76d4a3101cfe76d4a31004fd76d4a310776e52d4a31004ff7654a31004fd7654a3101cfc7654a3108cff76d0a3101cfe76d0a31004fd76d0a310057e75d0a310057d75d0a31005de73d0a31005dd73d0a31004ff7650a31004fd7650a3101cfc7650a31005f77150a3101df47150a31064fd76cca310057e75cca310057d75cca31016ec62cca31014ff764ca31016ee624ca31006ed624ca31005f7714ca3101df4714ca3101df576cc631046f576cc63101fd
  | 11 => 0x46de73d9331014fe72d9331046ee72d9331014ee72d9331004fd72d9331046ed72d9331004ed72d9331014fc72d9331046f571d9331044ff70d933100cfe70d9331004fd70d933100cfc70d9331006ef20d9331006ed20d9331004fd76993310057e75993310057d7599331046bf649933102cfe759933108e7e759933102c7e7599331004fd759933108e7d75993310047d759933101cfe7399331046be4399331046bc4399331014fe7299331004fd7299331014fc7299331006be429933108ebc429933108cff709933100cfe7099331004fd709933100cfc709933108ebf4099331006bd4099331006ef2099331006ed2099331046bc6459331004ff755933102cfc7559331046bf745933101cfc7359331046be4359331046bc4359331004ff7259331014fe7259331014fc7259331006be4259331006bc4259331004ff705933100cfe7059331004fd705933100cfc7059331006bf4059331006bd4059331006ef2059331006ed205933102cfe7519331004fd751933108cfe7419331046be7419331046de7319331014fe7219331004fd7219331014fc7219331046f57119331044ff701933100cfe7019331004fd701933100cfc7019331006ef2019331006ed201933102cff76d5331044fe76d5331004fd76d5331044fc76d53310067f65d533102e7c65d5331006be64d5331006bd64d5331045de73d5331005dd73d533108cff7695331044fe7695331004fd7695331044fc769533102e7e65953310067d65953310073f5495331004ff7655331044fe7655331004fd7655331044fc76553310067f655533102e7c6555331005f7715533101df4715533108cff7615331044fe7615331004fd7615331044fc761533102e7e65153310067d651533108ebe6415331006bd64153310467f65d4f310467c65d4f310475e53d4f310467f6554f310467c6554f310057e75d0f310057d75d0f310479c4350f31014ff7658b31046ec6258b31004ff7558b3102cfc7558b31004ff7458b3108cfc7458b3101cfc7358b3107eec5258b3107eec4258b31046ef3258b31046ec3258b3107eef2158b31004ff7058b3100cfe7058b31004fd7058b3100cfc7058b3107eef2058b31006ed2058b3102cff76d4b31044fe76d4b31004fd76d4b31016ee62d4b31006ed62d4b3107f6e52d4b31004ff7654b31004fd7654b31044fc7654b31005f77154b3101df47154b3108cff76d0b31044fe76d0b31004fd76d0b310057e75d0b310057d75d0b31016ee62d0b31006ed62d0b3101df671d0b31005f571d0b31004ff7650b31004fd7650b31044fc7650b3104cff764cb3102e7e65d47310067d65d4731045de73d4731005dd73d473102cff765473102e7e65547310067d6554731005df7354731045dc7354731005ef725473107dec725473101fd6315
  | 12 => 0xc3158c41004ff7058c4100cfe7058c41004fd7058c4100cfc7058c41006df3058c41006dd3058c41006ef2058c41006ed2058c4102cff76d4c4101cfe76d4c41004fd76d4c4102e7e65d4c410067d65d4c41044ff7694c4101cfe7694c41004fd7694c4102e7e6594c410067d6594c4108dbe7494c41005bd7494c410075f5394c41004ff7654c41004fd7654c4101cfc7654c4102e7e6554c410067d6554c41005f77154c4101df47154c41044ff7614c4101cfe7614c41004fd7614c4102e7e6514c410067d6514c41004fd7690c410057e7590c410057d7590c410067e6590c410067d6590c41004ff7650c410067e6550c410067d6550c4108f9c4350c41004ff755884102cfc7558841014fd7458841004ff7358841044fc735884101eef725884108eef425884108eec4258841096ee325884101cfc715884101eee215884101eec2158841004ff705884100cfe7058841004fd705884100cfc7058841096ef2058841006ed205884102cff76d484101cfe76d4841004fd76d484102e7e65d48410067d65d48410976e52d4841004ff7654841004fd765484101cfc765484102e7e65548410067d6554841005f7715484101df471548410c4ff76508410067e65508410067d6550841044ff76cc84101cfe76cc841004fd76cc8410057e75cc8410057d75cc8410067e65cc8410067d65cc84108dbe74cc841005bd74cc841046de63cc841006dd63cc84101df671cc841005f571cc841004ff764c841004fd764c84101cfc764c8410067e654c8410067d654c841006de634c841006dd634c841016ee624c841006ed624c84101df77650441006f77650441004f7765044100777755044100774755044101f76655044101f75655044101df7745044101fb7745044108ef6645044101fb6645044108fb65450441007b55450441007e77250441007e4725044101ef760504412b6f560504412afe720504412afe5205044108cfe74d9731046be74d9731004be74d9731004fd74d9731046bd74d9731004bd74d9731046de73d9731014fe72d9731046ee72d9731014ee72d9731004fd72d9731046ed72d9731004ed72d9731014fc72d9731046f571d973128e7e51d973128e7c51d9731044ff70d973100cfe70d9731004fd70d973100cfc70d9731006ef20d9731006ed20d9731004fd76997310467f65997310467c659973102cff76597310467c65597310467f7559731004ff745973108cfc745973101cfc73597310467e53597310467c5359731004ff7259731014fe7259731014fc72597310067e52597310067c5259731004ff705973100cfe7059731004fd705973100cfc70597310067f50597310067d5059731006ef2059731006ed205973102cfe75d93310467e75d933102c7e75d9331004fd75d93310467d75d93310047d75d9331
  | 13 => 0x944102e7e739944102e7d739944102e7c739944108e7f439944108e7c439944102e7f729944102e7e729944102e7d729944102e7c729944108e7f42994410067e429944108e7c42994410067e32994410067c329944101e7f719944101e7e719944101e7d719944101e7c719944101e7f419944101e7e419944101e7d419944101e7c419944101e7f319944101e7e319944101e7d319944101e7c319944101e7f219944101e7e219944101e7d219944101e7c219944102e7f709944102e7e709944102e7d709944102e7c709944108e7f40994410067e40994410067d409944108e7c40994410067f30994410067e30994410067d30994410067c30994410067f20994410066f20994410067e20994410067d20994410066d20994410067c209944101e7f109944101e7e109944101e7d109944101e7c109944101cff755944101e7f755944102cff745944108cfe745944102cfd745944108cfc745944108e7e545944108e7c5459441004ff7359441044fc7359441004ff7259441014fe7259441014fc72594410067e52594410067c525944101cfe715944101cfc715944101e7e515944101e7c5159441004ff705944100cfe7059441004fd705944100cfc70594410067f50594410067e50594410067d50594410067c5059441006ef2059441006ed205944108e7e745944108e7c74594410067f73594410067e73594410067d73594410067c735944108e7f435944108e7c43594410067f72594410067e72594410067d72594410067c725944108e7f42594410067e425944108e7c42594410067e32594410067c325944101e7f715944101e7e715944101e7d715944101e7c715944101e7f415944101e7e415944101e7d415944101e7c415944101e7f315944101e7e315944101e7d315944101e7c315944101e7f215944101e7e215944101e7d215944101e7c21594410067f70594410067e70594410067d70594410067c705944108e7f40594410067e40594410067d405944108e7c40594410067f30594410067e30594410067d30594410067c30594410067f20594410066f20594410067e20594410067d20594410066d20594410067c205944101e7f105944101e7e105944101e7d105944101e7c1059441004fd76d504102e7e65d50410067d65d504108f3e54d5041004ff765504102e7e65550410067d655504102cfe7598c41004fd7598c4101ede7398c4108edf4398c41046dc4398c41014fe7298c41004fd7298c41014fc7298c4101ede3198c4101edc3198c41044ff7098c4100cfe7098c41004fd7098c4100cfc7098c41046df3098c41006dd3098c41006ef2098c41006ed2098c41004ff7558c4102cfc7558c4101edf7358c4108edf4358c4108edc4358c41004ff7258c41014fe7258c41014fc7258c4101ede3158c4101ed
  | 14 => 0x7e510d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941216ef74d89410aeee74d8941006ef54d8941006ee54d8941006ed54d8941006ec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ed53d8941006ec53d8941006ef43d8941006ee43d8941006ed43d8941006ec43d8941006ef71d8941216ee71d8941006ed71d8941216ee51d8941216ec51d8941216ee41d8941216ec41d8941216ee31d8941216ec31d8941006ef70d8941004ef70d8941006ee70d8941006ed70d8941004ed70d8941006ec70d8941006ef50d8941006ee50d8941006ed50d8941006ec50d8941006ef40d8941006ee40d8941006ed40d8941006ec40d8941006ef30d8941006ee30d8941006ed30d8941006ec30d8941216ef10d8941006ee10d8941006ed10d8941216ec10d89410057f75589410057c75589410067f65589410067c65589410aeec6258941005ee76189410aeee7618941006ef65189410076f65189410066f6518941006ee6518941006ed6518941006ec65189410076c65189410066c651894120eef6418941006ef6318941006ee6318941006ed6318941006ec631894120fae411894120fac41189410adef7018941005ed7018941006ef6018941006ee6018941006ed6018941006ec6018941007e71018941007e51018941004fe76d4941004fd76d494102cfc76d49410067f65d494102e7c65d4941006ef62d4941016ec62d49410af6e52d4941004ff7654941004fe7654941004fc76549410067f655494102e7c6554941006ef6254941016ec62549410bcfe76d09410057e75d09410057d75d09410067f65d09410067c65d0941016ec62d094101cfc76509410067f65509410067c6550941006ef6250941016ec6250941005f7715094101df47150941004fe76cc941004fd76cc941044fc76cc9410057e75cc9410057d75cc9410067f65cc9410067c65cc941006ef62cc941016ec62cc941004ff764c941004fe764c941004fc764c9410067f654c9410067c654c941006ef624c941016ec624c941005f7714c94101df4714c941004fe76d454108cfc76d45410067f65d454102e7c65d4541005be74d4541005bd74d4541006ef62d4541106ec62d454101f7651d454102cff7654541004fd765454102cfc76545410067f655454102e7c6554541005bf7454541005bc7454541005ef72545410adec7254541006ef62545410e6ec625454101fb441545410067f65d05410067c65d054101dbe74d054101ebf64d0541006ef62d05410c6ec62d05410077765d05410077465d054101df674d054101ef764d054101fb764d0541007e762d0541007e462d054108df770d05412bdf570d05412bfe720d05412bfe520d054108e7e749944108e7c749944102e7f739
  | 15 => 0xf65d514102e7c65d51411f6ec62d514101df671d5141005f571d5141004fe76951410067f659514102e7c65951410073f54951411e6ec629514101cfc76551410067f655514102e7c65551411deec6255141005f7715514101df47155141004fe76151410067f651514102e7c65151411c6ec62151410067f65d8d410067c65d8d4102cfe75d8d41004fd75d8d41014fe72d8d41004fd72d8d41014fc72d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d41006ef20d8d41006ed20d8d41006f710d8d41006f510d8d410057e7598d410057d7598d410067f6598d410067c6598d41006df6398d410adee7298d41005ed7298d410057f7558d410057c7558d410067f6558d410067c6558d41005ef7258d410adec7258d41005fb7058d410a5f87058d410067f6518d410067c6518d41006dd6318d4102cfe7518d41004fd7518d41014fe7218d41004fd7218d41014fc7218d41044ff7018d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d41046dc3018d41006ef2018d41006ed2018d41004fe76d4d41004fd76d4d4102cfc76d4d410067f65d4d4102e7c65d4d41005be74d4d41005bd74d4d411b6ec62d4d41004fe7694d41004fd7694d41044fc7694d410067f6594d4102e7c6594d410075f5394d411a6ec6294d41004ff7654d41004fe7654d41004fc7654d410067f6554d4102e7c6554d4119eec6254d41004fe7614d41004fd7614d41044fc7614d410067f6514d4102e7c6514d41186ec6214d41004fe76d0d410057e75d0d410057d75d0d410067f65d0d410067c65d0d41176ec62d0d4101cfe7690d410057e7590d410057d7590d410067f6590d410067c6590d41006df6390d41046dc6390d4116eec6290d4101df67190d41005f57190d4101cfc7650d410067f6550d410067c6550d41006df6350d41006dc6350d41166ec6250d41005f77150d4101df47150d41004fe7610d410067f6510d410067c6510d410079d4310d41146ec6210d41014fe76d89410067f65d89410067c65d89410aeee62d894102cfe75d8941004fd75d894101cfd74d8941014fc74d8941044fe73d8941004fd73d89410aeee52d89410aeec52d89410aeee42d89410aeee32d89410aeec32d89410aeef21d8941004ff70d894100cfe70d8941004fd70d894100cfc70d89410aeef20d8941006ee20d8941006ed20d89410aeec20d89410adee76d8941014ee76d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ed65d8941006ec65d89410076c65d89410066c65d8941006ef63d8941006ee63d8941006ed63d8941006ec63d8941217ae41d8941217ac41d8941005ef70d8941005ed70d8941006ef60d8941006ee60d8941006ed60d8941006ec60d8941007e710d8941
  | 16 => 0x9541014fe72d9541004fd72d9541014fc72d95410067e52d95410067c52d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410067f50d95410067e50d95410067d50d95410067c50d9541006ef20d9541006ed20d954102c7e76d95410067e62d95410067c62d95412a73e41d95412a73c41d95410067f60d95410067e60d95410067d60d95410067c60d95410076f20d95410076d20d95410077710d95410077510d95412a67f74d95410067d74d95410067f73d95410067e73d95410067d73d95410067c73d95410067f72d95410067e72d95410067d72d95410067c72d95410067e42d95410067c42d95410067e32d95410067c32d95410067f71d95412a67e71d95410067d71d95412a67c71d95412a67e41d95412a67c41d95412a67e31d95412a67c31d95410067f21d95412a67e21d95412a67c21d95410067f70d95410067e70d95410067d70d95410067c70d95410067f40d95410067e40d95410067d40d95410067c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410066f20d95410067e20d95410067d20d95410066d20d95410067c20d95412a67f10d95410067e10d95410067d10d95412a67c10d95410067f65995410adee7299541005ed7299541005ef72595410adec72595410067f7559541004ff7459541006bf7459541004ff7359541044fc7359541004ff7259541006ef7259541004ef7259541014fe7259541014fc7259541006ec7259541014ec7259541004ff7159541006f77159541004ff705954100cfe7059541004fd705954100cfc7059541006ef2059541006ed2059541004fe761954102e7e65195410067d65195410057e76195410067e76195410047e76195410067e62195410067c621954129f3e411954129f3c41195410067f60195410067e60195410067d60195410067c60195410076f20195410076d201954100777101954100775101954102e7f741954102e7d741954102e7f731954102e7e731954102e7d731954102e7c731954102e7f721954102e7e721954102e7d721954102e7c72195410067e42195410067c42195410067e32195410067c321954102e7f711954102e7e711954102e7d711954102e7c711954129e7e41195410067d411954129e7c411954129e7e311954129e7c31195410067f211954129e7e211954129e7c211954102e7f701954102e7e701954102e7d701954102e7c70195410067f40195410067e40195410067d40195410067c40195410067f30195410067e30195410067d30195410067c30195410067f20195410066f20195410067e20195410067d20195410066d20195410067c201954129e7f10195410067710195410067e10195410067d101954100675101954129e7c101954101cfe76d514101cfc76d51410067
  | 17 => 0x2e7e65547410067d6554741005bf745474108dbc7454741005ef72547410c5ec725474101fb6415474101e7f7559641004ff7359641044fc7359641004ff7259641014fe7259641014fc725964101cfc715964101e7e515964101e7c5159641004ff705964100cfe7059641004fd705964100cfc7059641006ef2059641006ed205964102e7e65d52410067d65d524101df671d5241005f571d52412a67f659524102e7c65952410073f549524102cff765524102e7e65552410067d6555241005f7715524101df4715524129e7f651524102e7c651524102cfe7598e41004fd7598e4101ede7398e41014fe7298e41004fd7298e41014fc7298e4101ede3198e4101edc3198e41044ff7098e4100cfe7098e41004fd7098e4100cfc7098e41006ef2098e41006ed2098e41004ff7558e410067f7558e410047f7558e4102cfc7558e410067c7558e4102c7c7558e4101edf7358e41004ff7258e41014fe7258e41014fc7258e4101ede3158e4101edc3158e41004ff7058e4100cfe7058e41004fd7058e4100cfc7058e41006ef2058e41006ed2058e4101ef71058e41006f51058e4102cff76d4e4101cfe76d4e41004fd76d4e4102e7e65d4e410067d65d4e41044ff7694e4101cfe7694e41004fd7694e4128e7f6594e4102e7c6594e41005be7494e41005bd7494e41046de6394e41006dd6394e410075f5394e41004ff7654e41004fd7654e4101cfc7654e4102e7e6554e410067d6554e41006de6354e41006dd6354e41044ff7614e4101cfe7614e41004fd7614e412867f6514e4102e7c6514e410057e75d0e410057d75d0e410057e7590e410057d7590e41046de6390e41006dd6390e4101df67190e41005f57190e41006de6350e41006dd6350e41005f77150e4101df47150e410079d4310e41004ff7558a410067f7558a410047f7558a4102cfc7558a410067c7558a4102c7c7558a41004ff7358a41044fc7358a4101eef7258a410beee4258a4101cfc7158a4101eee2158a4101eec2158a41004ff7058a4100cfe7058a41004fd7058a4100cfc7058a410beef2058a41006ed2058a4102cff76d4a4101cfe76d4a41004fd76d4a410bf6e52d4a41004ff7654a41004fd7654a4101cfc7654a410acfd76d0a410057e75d0a410057d75d0a41016ec62d0a41014ff7650a41016ee6250a41006ed6250a41005f77150a4101df47150a41044ff76cca4101cfe76cca41004fd76cca410057e75cca410057d75cca41005be74cca41005bd74cca41004ff764ca41004fd764ca4101cfc764ca41005f7714ca4101df4714ca4101df576d064108ef576d064101fb674d064108fb654d0641007b554d064108df770d06412c5f570d06412c7e720d06412c7e520d064102cfe76d954108cfe74d954108cfc74d9541044fe73d9541004fd73d
  | 18 => 0xd73d974108edd73d9741004dd73d9741014fe72d974108eee72d9741014ee72d9741004fd72d974108eed72d9741004ed72d9741014fc72d974108ef571d97412a67e51d97412a67c51d974108cff70d974100cfe70d9741004fd70d974100cfc70d9741006ef20d9741006ed20d9741004fd769974108e7f659974108e7c659974102cff765974108e7c655974108e7f755974101cfc745974108e7e545974108e7c5459741004ff7359741044fc7359741004ff7259741014fe7259741014fc72597410067e52597410067c5259741004ff705974100cfe7059741004fd705974100cfc70597410067f50597410067d5059741006ef2059741006ed205974108e7f65d534108e7c65d534108f3e54d534108e7f655534108e7c65553410057e7598f410057d7598f4108edf6398f4102cfe7598f410467e7598f4102c7e7598f41004fd7598f410467d7598f410047d7598f4101cfe7498f4108edf4398f41046dc4398f41014fe7298f41004fd7298f41014fc7298f41006de3298f41046dc3298f41044ff7098f4100cfe7098f41004fd7098f4100cfc7098f41046df3098f41006dd3098f41006ef2098f41006ed2098f4108edc6358f41004ff7558f4102cfc7558f4101cfc7458f4108edf4358f4108edc4358f41004ff7258f41014fe7258f41014fc7258f41006de3258f41006dc3258f41004ff7058f4100cfe7058f41004fd7058f4100cfc7058f41006df3058f41006dd3058f41006ef2058f41006ed2058f4102cff76d4f4108cfe76d4f41004fd76d4f410067f65d4f4102e7c65d4f4108dbe74d4f41005bd74d4f41006de63d4f41006dd63d4f41044ff7694f4108cfe7694f41004fd7694f4102e7e6594f410067d6594f410075f5394f41004ff7654f41004fd7654f4108cfc7654f410067f6554f4102e7c6554f41005f77154f4101df47154f41044ff7614f4108cfe7614f41004fd7614f4102e7e6514f410067d6514f41046de6314f41006dd6314f410057e7590f410057d7590f4108f9c4350f41014ff7658b4108eec6258b41004ff7558b4102cfc7558b4101cfc7458b41004ff7358b41044fc7358b410c6ec5258b4108eef4258b4108eec4258b410c6ec3258b410c6ef2158b41004ff7058b4100cfe7058b41004fd7058b4100cfc7058b410c6ef2058b41006ed2058b4102cff76d4b4108cfe76d4b41004fd76d4b41016ee62d4b41006ed62d4b410c76e52d4b41004ff7654b41004fd7654b4108cfc7654b41005f77154b4101df47154b41094ff7650b41044ff76ccb4108cfe76ccb41004fd76ccb410057e75ccb410057d75ccb41016ee62ccb41006ed62ccb4101df671ccb41005f571ccb41004ff764cb41004fd764cb4108cfc764cb4102e7e65d47410067d65d474108dbe74d4741005bd74d474102cff7654741
  | 19 => 0x50510047d769505102d7e749505102f3e74950510067d64950510057e73950510d57e72950510d57c72950512a57d71950512a67e619505102f7661950512d57f70950512d57d70950512d76f20950512d76d20950512a77710950512d775109505108cfe7498c51004fd7498c5101cfe7398c5101ede7398c5102edf5398c51046dc5398c51014fe7298c51004fd7298c51014fc7298c5101ede3198c5101edc3198c51044ff7098c5100cfe7098c51004fd7098c5100cfc7098c51046df3098c51006dd3098c51006ef2098c51006ed2098c51004ff7458c5108cfc7458c510067e5458c5102e7c5458c5101edf7358c5102edf5358c5102e7c5358c5102edc5358c51004ff7258c51014fe7258c51014fc7258c510067e5258c5102e7c5258c5101e7f5158c5101e7d5158c5101ede3158c5101edc3158c51004ff7058c5100cfe7058c51004fd7058c5100cfc7058c5102e7f5058c510067d5058c51006df3058c51006dd3058c51006ef2058c51006ed2058c5101ef71058c51006f51058c5102d7d7694c510067d7694c510047d7694c510057e7494c510067d6494c5102d7e7394c5102f5e7394c510067d6394c510d57e7294c510d57c7294c5128d7d7194c5128e7e6194c5102f766194c512cd7f7094c512cd7d7094c512cf6f2094c512cf6d2094c5128f771094c512cf751094c5108cff76d0c5101cfe76d0c51004fd76d0c5102d7e75d0c510057d75d0c51006de63d0c51006dd63d0c51044ff7690c5101cfe7690c51004fd7690c5102d7e7590c510057d7590c51006be6490c51006bd6490c51004ff7650c51004fd7650c5101cfc7650c510057f7550c5102d7c7550c51005f77150c5101df47150c51044ff7610c5101cfe7610c51004fd7610c510057f7510c5102d7c7510c5108ebe6410c51006bd6410c51046de6310c51006dd6310c510079d4310c51014fd7558851004ff745885108cfc7458851004ff7358851044fc735885101cff725885101eef725885102eef52588510d67e525885102e7c525885102eec525885101cfc715885101eee215885101eec2158851004ff705885100cfe7058851004fd705885100cfc70588510d6ef2058851006ed205885108cff76d085101cfe76d0851004fd76d085102d7e75d08510057d75d085108ebe64d0851006bd64d0851004ff7650851004fd765085101cfc76508510057f755085102d7c7550851006be6450851006bd6450851005f7715085101df47150851044ff76cc85101cfe76cc851004fd76cc85102d7e75cc8510057d75cc851046de63cc851006dd63cc851004ff764c851004fd764c85101cfc764c8510057f754c85102d7c754c851006de634c851006dd634c851005f7714c85101df4714c85108ebe74d9741044fe73d974108ede73d9741004de73d9741004f
  | 20 => 0x76d53d8951247e751d89512276e51d89512276c51d8951247e451d8951005ef70d8951005ed70d8951006ef60d8951006ee60d8951006ed60d8951006ec60d8951226ef75d89510e6ee75d8951006ef74d8951006ee74d8951006ed74d8951006ec74d8951246ef54d8951006ee54d8951006ed54d8951246ec54d8951006ef73d8951006ee73d8951006ed73d8951006ec73d8951246ef53d8951006ee53d8951006ed53d8951246ec53d8951006ef43d8951006ee43d8951006ed43d8951006ec43d8951246ef71d8951226ee71d8951006ed71d8951246ef51d8951226ee51d8951226ec51d8951226ee41d8951226ec41d8951226ee31d8951226ec31d8951006ef70d8951004ef70d8951006ee70d8951006ed70d8951004ed70d8951006ec70d8951246ef50d8951006ee50d8951006ed50d8951246ec50d8951006ef40d8951006ee40d8951006ed40d8951006ec40d8951006ef30d8951006ee30d8951006ed30d8951006ec30d8951226ef10d8951006ee10d8951006ed10d8951226ec10d89510e6ec6258951005ee76189510e6ee761895121eef651895121e6f6518951006ef6418951006ee6418951006ed6418951006ec64189510076f54189510076d5418951006ef6318951006ee6318951006ed6318951006ec63189510076f53189510076d5318951106ef61189512dfe7511895121f6e511895121f6c51189512dfe451189510e5ef7018951005ed7018951006ef6018951006ee6018951006ed6018951006ec601895101cfc7654951006ef6254951016ec6254951005f7715495101df47154951004fe76d0951004fd76d095108cfc76d095102d7e75d09510057d75d0951006ef62d0951016ec62d0951004ff7650951004fe7650951004fc7650951006ef6250951016ec6250951004fe76cc951004fd76cc951044fc76cc95102d7e75cc9510057d75cc951006ef62cc951016ec62cc951004ff764c951004fe764c951004fc764c951006ef624c951016ec624c95101cfe749905101ebe749905102ebf549905108ebc5499051044fe7399051004fd7399051014fe7299051004fd7299051014fc729905101ebe419905101ebc419905108cff709905100cfe7099051004fd709905100cfc709905108ebf4099051006bd4099051006ef2099051006ed209905101ebf745905102ebf545905102e7c545905102ebc5459051004ff7359051044fc735905102e7c5359051004ff7259051014fe7259051014fc72590510067e525905102e7c525905101e7f515905101e7d515905101ebe415905101ebc4159051004ff705905100cfe7059051004fd705905100cfc705905102e7f50590510067d5059051006bf4059051006bd4059051006ef2059051006ed205905101ef71059051006f5105905102d7d76950510067d769
  | 21 => 0xc62551511de6c625515100777715515101d7e715515101d7c715515100774715515102e7f615515102f77615515130e7f605515130e7d60551513076f20551513076d205515108cfe74d8d51004fd74d8d51014fe72d8d51004fd72d8d51014fc72d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51006de30d8d51006dc30d8d51006ef20d8d51006ed20d8d51005be7498d51005bd7498d51006df6398d510e5ee7298d51005ed7298d51005ef7258d510e5ec7258d51006dd6318d5108cfe7418d51004fd7418d510067f5418d510067d5418d51014fe7218d51004fd7218d51014fc7218d512867e5118d512867c5118d51044ff7018d5100cfe7018d51004fd7018d5100cfc7018d51006de3018d51046dc3018d51006ef2018d51006ed2018d510057e76d4d5102e7e76d4d510047e76d4d510057d74d4d510067c64d4d510467c63d4d511b67e62d4d511b67c62d4d511b66c62d4d5101d7e71d4d5101d7c71d4d5102e7f61d4d5102f7761d4d512fe7f60d4d512fe7d60d4d512f76f20d4d512f76d20d4d5101cfe7694d512e57d7594d51006df6394d51046dc6394d5102f5f5394d511a6ec6294d5101df67194d51005f57194d5101cfc7654d51006df6354d51006dc6354d5119eec6254d51005f77154d5101df47154d5101c7c7654d510057f7454d510067c6454d5102d7f7354d5102f5f7354d510075f6354d510467c6354d510075c6354d5119e7e6254d5119e7c6254d5119e6c6254d51007777154d5101d7e7154d5101d7c7154d51007747154d5102e7f6154d5102f776154d512ee7f6054d512ee7d6054d512e76f2054d512e76d2054d51004fe76d0d51004fd76d0d5108cfc76d0d5102d7e75d0d510057d75d0d51006bf64d0d5108ebc64d0d51176ec62d0d51004fe7690d51004fd7690d51044fc7690d5102d7e7590d510057d7590d51006df6390d51046dc6390d5116eec6290d51004ff7650d51004fe7650d51004fc7650d5102d7e7550d510057d7550d51006bf6450d51006bc6450d51006df6350d51006dc6350d51166ec6250d51004fe7610d51004fd7610d51044fc7610d5102d7e7510d510057d7510d510079d4310d51146ec6210d51014fe76d89510e6ee62d895101cfd75d8951014fc75d895108cfe74d8951004fd74d8951044fe73d8951004fd73d89510e6ee52d89510e6ee42d89510e6ec42d89510e6ee32d89510e6ec32d895102cfd71d89510e6ef21d8951004ff70d895100cfe70d8951004fd70d895100cfc70d89510e6ef20d8951006ee20d8951006ed20d89510e6ec20d89510e5ee76d8951014ee76d8951006ef64d8951006ee64d8951006ed64d8951006ec64d89510076f54d89510076d54d8951006ef63d8951006ee63d8951006ed63d8951006ec63d89510076f53d8951
  | 22 => 0x4e5128f767194e5128d7d7194e51007757194e51005757194e5102e7e6194e5132d7f7094e5132d7d7094e5132f6f2094e5132f6d2094e51006de6354e51006dd6354e51005f77154e5101df47154e5102f775154e512857d7614e5102e7d7614e510057e7414e510067d6414e5102f5e7314e510067d6314e510f57e7214e5102d7c7214e5102d7f7114e512857d7114e5102f766114e5102d7f7014e513257d7014e513276f2014e513276d2014e5108cff76d0e5101cfe76d0e51004fd76d0e5102d7e75d0e510057d75d0e51044ff7690e5101cfe7690e51004fd7690e5102d7e7590e510057d7590e51004ff7650e51004fd7650e5101cfc7650e510057f7550e5102d7c7550e51044ff7610e5101cfe7610e51004fd7610e510057f7510e5102d7c7510e510079d4310e51004ff7458a5108cfc7458a51004ff7358a51044fc7358a5101eef7258a510f67e5258a510f6ee5258a510f66e5258a510f67c5258a5101cfc7158a5101eee2158a5101eec2158a51004ff7058a5100cfe7058a51004fd7058a5100cfc7058a510f6ef2058a51006ed2058a51014ff7654a5122d7f7554a51016ee6254a51006ed6254a5102f6c5254a51005f77154a5101df47154a5102f775154a5108cff76d0a5101cfe76d0a51004fd76d0a5102d7e75d0a510057d75d0a51004ff7650a51004fd7650a5101cfc7650a510057f7550a5102d7c7550a51044ff76cca5101cfe76cca51004fd76cca5102d7e75cca510057d75cca51004ff764ca51004fd764ca5101cfc764ca510057f754ca5102d7c754ca51044fe73d9151004fd73d9151014fe72d9151004fd72d9151014fc72d9151004ff70d915100cfe70d9151004fd70d915100cfc70d9151006be40d9151006bc40d9151006ef20d9151006ed20d9151006bf6499151005de7399151005dd73991510e5ee7299151005ed7299151005ef72591510e5ec7259151006bd6419151044fe7319151004fd7319151014fe7219151004fd7219151014fc721915129e7e511915129e7c511915108cff701915100cfe7019151004fd701915100cfc7019151006be401915108ebc4019151006ef2019151006ed20191510057e76d515102e7e76d51510047e76d515108e7c64d51510057d73d51511f67e62d51511f67c62d51511f66c62d515101d7e71d515101d7c71d515102e7f61d515102f7761d515131e7f60d515131e7d60d51513176f20d51513176d20d515101cfe76951513057d7595151006bf649515108ebc649515102f3f54951511e6ec629515101df67195151005f5719515101cfc7655151006bf6455151006bc64551511deec6255151005f7715515101df4715515101c7c765515102d7f745515102f3f74551510073f645515108e7c64551510073c64551510057f73551511de7e62551511de7
  | 23 => 0x79d4310f5101cfc7558b51004ff7458b5108cfc7458b51004ff7358b51044fc7358b5102eef7258b5102eef5258b5102eec5258b51106ec4258b51106ec3258b51106ef2158b51004ff7058b5100cfe7058b51004fd7058b5100cfc7058b51106ef2058b51006ed2058b5108cff76d0b5102cfe76d0b51004fd76d0b5102d7e75d0b510057d75d0b51016ee62d0b51006ed62d0b51004ff7650b51004fd7650b5102cfc7650b51005f77150b5101df47150b51044ff76ccb5102cfe76ccb51004fd76ccb5102d7e75ccb510057d75ccb51016ee62ccb51006ed62ccb51004ff764cb51004fd764cb5102cfc764cb51005f7714cb5101df4714cb5101ebe7499251044fe7399251004fd7399251014fe7299251004fd7299251014fc729925101cfe719925101ebe419925101ebc419925108cff709925100cfe7099251004fd709925100cfc7099251006ef2099251006ed209925101ebf7459251004ff7359251044fc7359251004ff7259251014fe7259251014fc72592510067e52592510067c525925101cfc715925101e7f515925101e7d515925101ebe415925101ebc4159251004ff705925100cfe7059251004fd705925100cfc70592510067f50592510067d5059251006ef2059251006ed205925108ebe6495251006bd649525102f3f549525101df67195251005f5719525102d7e74952512a73e64952510067d64952512a73d64952510063d64952510057e73952510f57e72952510f57c72952512a77671952512a57d719525100775719525100575719525102e7e619525133d7f709525133d7d709525133f6f209525133f6d2095251006be6455251006bd6455251005f7715525101df4715525102f77515525129d7d761525102e7d761525102f3e74152510067d64152510057e73152510f57e721525102d7c721525102d7f711525129d7d711525102f76611525102d7f70152513357d70152513376f20152513376d201525108cfe7498e51004fd7498e5101ede7398e51014fe7298e51004fd7298e51014fc7298e5101cfe7198e5101ede3198e5101edc3198e51044ff7098e5100cfe7098e51004fd7098e5100cfc7098e51006ef2098e51006ed2098e51004ff7458e5108cfc7458e510067e5458e510067c5458e5101edf7358e51004ff7258e51014fe7258e51014fc7258e510067e5258e510067c5258e5101cfc7158e5101e7f5158e5101e7d5158e5101ede3158e5101edc3158e51004ff7058e5100cfe7058e51004fd7058e5100cfc7058e510067f5058e510067d5058e51006ef2058e51006ed2058e51046de6394e51006dd6394e5102f5f5394e5101df67194e51005f57194e510057e7494e510067d6494e5102d7e7394e5128f5e6394e510067d6394e5128f5d6394e510065d6394e510f57e7294e510f57c729
  | 24 => 0xc3290d3208cff7650d32014fe7650d32164fd7650d32014fc7650d32006bf6450d32006bc6450d32005ef7250d32015ec7250d32167cc3250d3216cfe7610d320079d4310d320476e75cc9320476d75cc932015ee73cc932017ce73cc932016ef63cc932017cf63cc932045ef70cc93236ded70cc932366ef60cc932366ed60cc93202cfe75d8532004fd75d853208cfe74d8532004fd74d853207ef621d8532004ff70d853200cfe70d8532004fd70d853200cfc70d853207eef20d8532006ed20d8532006f610d8532006f410d8532006f761985320057f75585320057c7558532206ef621853201ef66118532006f5611853201cfe759935101c7e759935108ebe749935108e7f549935102ebf549935102e3f549935108ebc5499351044fe7399351004fd739935102e7f5399351014fe7299351004fd7299351014fc72993512a67e519935102e7c519935108cff709935100cfe7099351004fd709935100cfc7099351006ef2099351006ed209935101cfc755935102ebf745935102ebf545935102ebc5459351004ff7359351044fc7359351004ff7259351014fe7259351014fc7259351004ff705935100cfe7059351004fd705935100cfc7059351006ef2059351006ed2059351006f71059351006f5105935102d7f76553510067f765535102f3f745535108e7e64553510057f73553511de7e625535102e7c625535101d7e715535101d7c715535102e7f605535135e7d60553513576f20553513576d205535135777105535135775105535101cfe7598f5101c7e7598f5108cfe7498f51004fd7498f5102e7f5498f510067d5498f51046de7398f510467f5398f5102edf5398f5102e5f5398f51046dc5398f51014fe7298f51004fd7298f51014fc7298f5128e7e5198f5102e7c5198f51044ff7098f5100cfe7098f51004fd7098f5100cfc7098f51006ef2098f51006ed2098f5101cfc7558f51004ff7458f5108cfc7458f5102edf7358f5102edf5358f5102edc5358f51004ff7258f51014fe7258f51014fc7258f51004ff7058f5100cfe7058f51004fd7058f5100cfc7058f51006ef2058f51006ed2058f51006f71058f51006f51058f5102d7f7654f510067f7654f510057f7454f510067e6454f5102f5f7354f510467e6354f5119e7e6254f5102e7c6254f5101d7e7154f5101d7c7154f5102e7f6054f5134e7d6054f513476f2054f513476d2054f51347771054f51347751054f5108cff76d0f5102cfe76d0f51004fd76d0f5102d7e75d0f510057d75d0f51044ff7690f5102cfe7690f51004fd7690f5102d7e7590f510057d7590f51004ff7650f51004fd7650f5102cfc7650f5102d7e7550f510057d7550f51005f77150f5101df47150f51044ff7610f5102cfe7610f51004fd7610f5102d7e7510f510057d7510f51
  | 25 => 0x9532004fd70d953200cfc70d95320067e50d95320067c50d95321a6ef20d9532006ed20d95320067f659953219ddd73995321b5df7359532005f77159532005f471595320067f7559532004ff745953208cfc74595321b4ff7359532006df735953219cff7259532006ef725953219e7e525953219e7c5259532004ff7159532006f77159532004f7715953201cfc7159532006f4715953201cf47159532004ff705953200cfe7059532004fd705953200cfc705953219eef2059532006ed20595321a4fe761953202e7e65195320067d651953202cfe75d9132004fd75d9132044ff72d913216cfd72d913216ebf42d913216ebd42d913201cfe71d9132004fd71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d9132006be40d9132006bc40d913216eef20d9132006ed20d91320057e75991320057d7599132006bf6499132165dd7399132005f67199132005f5719913202cfe759913208e7e759913202c7e7599132004fd759913208e7d75991320047d759913208cfe7499132164fd739913208edd7399132174fd729913208eed729913201cfe719913208ef6719913201cf67199132004fd719913208ef57199132004f5719913208cff709913200cfe7099132004fd709913200cfc7099132176ef2099132006ed2099132175df7359132004ff755913202cfc7559132006bf7459132174ff7359132006df7359132164ff7259132006ef7259132004ff715913201cfc7159132004ff705913200cfe7059132004fd705913200cfc7059132166ef2059132006ed205913216cfe7619132006bd641913202cfe7519132004fd751913208ebe7419132044ff7219132144fd721913208ebf4219132146bd421913201cfe7119132004fd711913208cff701913200cfe7019132004fd701913200cfc7019132006be401913208ebc4019132146ef2019132006ed201913202cff76d5132004fe76d5132004fd76d513202cfc76d51320067f65d513202e7c65d513208cff7695132004fe7695132004fd769513208cfc76951320073f5495132005de7395132005dd7395132015ee7295132005ed7295132004ff7655132004fe7655132004fd7655132004fc76551320067f655513202e7c655513208cff7615132004fe7615132004fd761513208cfc7615132014fe76d4d32014fc76d4d320067f65d4d3202e7c65d4d32015ee72d4d32005ed72d4d32184fe7694d320075f5394d32047cc3294d3202cff7654d32014fe7654d3219cfd7654d32014fc7654d320067f6554d3202e7c6554d32005ef7254d32015ec7254d3219fcc3254d321a4fe7614d32014fe76d0d32014fc76d0d320057e75d0d320057d75d0d32006bf64d0d3208ebc64d0d32015ee72d0d32005ed72d0d32144fe7690d320057e7590d320057d7590d32047c
  | 26 => 0x67f10597320067e10597320067d10597320067c105973202cfe75d93320467e75d933202c7e75d9332004fd75d93320467d75d93320047d75d9332044fe73d9332046de73d9332046ed72d933201cfe71d9332046f671d933201cf671d9332004fd71d9332046f571d9332004f571d9332044ff70d933200cfe70d9332004fd70d933200cfc70d933216eef20d9332006ed20d9332164fd76993320067e65993320067d6599332046bf649933202cfe7599332004fd7599332014fe7399332014fc7399332046be4399332046bc439933208ebf4299332176bd429933201cfe7199332004fd7199332176ec219933208cff709933200cfe7099332004fd709933200cfc709933208ebf4099332006bd4099332176ef2099332006ed20993320067e65593320067d6559332046bc6459332004ff755933202cfc7559332046bf7459332014fe7359332014fc7359332046be4359332046bc4359332166bf4259332166bd4259332004ff715933201cfc7159332004ff705933200cfe7059332004fd705933200cfc7059332006bf4059332006bd4059332166ef2059332006ed205933202cfe75193320467e751933202c7e7519332004fd75193320467d75193320047d751933208cfe7419332046be7419332044fe7319332046de7319332046ed721933201cfe7119332004fd7119332146ec2119332044ff701933200cfe7019332004fd701933200cfc7019332146ef2019332006ed201933202cff76d5332044fe76d5332004fd76d5332044fc76d533202e7e65d53320067d65d533208cff7695332044fe7695332004fd7695332044fc769533202e7e65953320067d65953320073f5495332045de7395332005dd7395332004ff7655332044fe7655332004fd7655332044fc765533202e7e65553320067d6555332005ef7255332015ec725533208cff7615332044fe7615332004fd7615332044fc761533202e7e65153320067d651533219cfd76d4f3202e7e65d4f320067d65d4f320475e53d4f321b4ff7654f3202e7e6554f3219e7d6554f3219fce3254f32164fd76d0f320057e75d0f320057d75d0f320067e65d0f320067d65d0f32174ff7650f320067e6550f320067d6550f320479c4350f320067e65987320067d6598732046f7619873201ef461987320067e65587320067d6558732046f46158732004ff755873202cfc7558732004ff745873208cfc7458732014fc7358732046f73158732046f43158732066f62158732206ec2158732004ff705873200cfe7058732004fd705873200cfc7058732066ef2058732006ed2058732006f71058732006f5105873202cfe76d953208cfe74d9532004fd74d9532044ff72d95321a4fd72d95321a67f52d95321a67d52d953201cfe71d9532004fd71d9532004ff70d953200cfe70d
  | 27 => 0xe74d9732004fd74d9732044fe73d9732046de73d9732046ed72d973201cfe71d9732004fd71d9732044ff70d973200cfe70d9732004fd70d973200cfc70d97321a6ef20d9732006ed20d973219cfd76997320467f65997320467c659973219c7d76997320467f64997320467c64997321b75e32997320476e32997320475c32997320467f61997320467c61997321b76c21997320467f60997320067e60997320067d60997320467c60997321b76f20997320076d209973202e7f749973202e7e749973202e7d749973202e7c74997320467e73997320467c73997320467e43997320467c439973202e7f729973202e7e729973202e7d729973202e7c72997321b67f42997321b67e42997321b67d42997321b67c42997321b67e32997321b67d32997320467c329973202e7f719973202e7e719973202e7d719973202e7c71997320467f31997320467c31997321b67f21997321b67e21997321b67d21997321b67c21997321b66c219973202e7f709973202e7e709973202e7d709973202e7c70997320067f40997320067e40997320067d40997320067c40997320467f30997320067e30997320067d30997320467c30997321b67f20997321b66f20997321b67e20997321b67d20997320066d20997321b67c20997320067f10997320067e10997320067d10997320067c109973202cff76597320467c65597320467f7559732004ff745973208cfc7459732014fe7359732014fc73597320467e53597320467c535973219e7f525973219e7d5259732004ff715973201cfc7159732004ff705973200cfe7059732004fd705973200cfc70597320067f50597320067e50597320067d50597320067c505973219eef2059732006ed20597320457f76597320067f765973202c7f76597320467f64597320467c645973219f5e32597320476e32597320475c32597320467f61597320467c615973219f6c21597320467f60597320067e60597320067d60597320467c605973219f6f20597320076d20597320067f74597320067e74597320067d74597320067c74597320467e73597320467c73597320467e43597320467c435973219e7f725973219e7e725973219e7d725973219e7c725973219e7f425973219e7e425973219e7d425973219e7c42597320467f325973219e7e325973219e7d32597320467c32597320067f71597320067e71597320067d71597320067c71597320467f31597320467c315973219e7f215973219e7e215973219e7d215973219e7c21597320067f70597320067e70597320067d70597320067c70597320067f40597320067e40597320067d40597320067c40597320467f30597320067e30597320067d30597320467c305973219e7f205973219e6f205973219e7e205973219e7d20597320066d205973219e7c2059732
  | 28 => 0x8742006ed2058742006f71058742006f5105874202cfe76d9542044fe73d9542004fd73d954208cff72d95421e4fd72d95421e67f52d95421e67d52d954201cfe71d9542004fd71d9542004ff70d954200cfe70d9542004fd70d954200cfc70d95420067e50d95420067c50d95421e6ef20d9542006ed20d95420067f65995421ddbd74995421f5bf7459542005f77159542005f471595420067f75595421f4ff7459542006bf7459542004ff7359542044fc73595421dcff7259542006ef72595421de7e52595421de7c5259542004ff7159542006f77159542004f7715954201cfc7159542006f4715954201cf47159542004ff705954200cfe7059542004fd705954200cfc70595421deef2059542006ed20595421e4fe761954202e7e65195420067d6519542014fe76d5142014fc76d51420067f65d514202e7c65d5142015ee72d5142005ed72d51421c4fe76951420073f549514208fac429514202cff7655142014fe76551421dcfd7655142014fc76551420067f655514202e7c6555142005ef7255142015ec72551421dfac42551421e4fe761514202cfe75d8d42004fd75d8d42176df32d8d4201cfe71d8d42004fd71d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006de30d8d42006dc30d8d42176ef20d8d42006ed20d8d420057e7598d420057d7598d42006df6398d42005f67198d42005f57198d42006dd6318d4202cfe7518d42004fd7518d42046df3218d42146dd3218d4201cfe7118d42004fd7118d42044ff7018d4200cfe7018d42004fd7018d4200cfc7018d42006de3018d42046dc3018d42146ef2018d42006ed2018d42004fe76d4d42004fd76d4d4202cfc76d4d420067f65d4d4202e7c65d4d42004fe7694d42004fd7694d42044fc7694d42005be7494d42005bd7494d420075f5394d42015ee7294d42005ed7294d42004ff7654d42004fe7654d42004fc7654d420067f6554d4202e7c6554d42004fe7614d42004fd7614d42044fc7614d42144fe76d0d420057e75d0d420057d75d0d4208fac42d0d42014fe7690d420057e7590d420057d7590d42006df6390d42046dc6390d42015ee7290d42005ed7290d42014fc7650d42006df6350d42006dc6350d42005ef7250d42015ec7250d42167ac4250d42174fe7610d420079d4310d4208f6e75d094208f6d75d0942015ee74d0942017ae74d0942016ef64d0942017af64d094208def70d094237ded70d0942376ef60d0942376ed60d094202cfe75d8542004fd75d8542044fe73d8542004fd73d85420c6f621d8542004ff70d854200cfe70d8542004fd70d854200cfc70d85420c6ef20d8542006ed20d8542006f610d8542006f410d8542006f761985420057f75585420057c7558542216ef621854201ef66118542006f5611854208cf
  | 29 => 0x67f765974202c7f765974208e7f635974208e7c63597421df3e425974208f6e425974208f3c425974208e7f615974208e7c61597421df6c215974208e7f60597420067e60597420067d605974208e7c60597421df6f20597420076d205974208e7e745974208e7c74597420067f73597420067e73597420067d73597420067c735974208e7f435974208e7c43597421de7f72597421de7e72597421de7d72597421de7c725974208e7f42597421de7e42597421de7d425974208e7c42597421de7f32597421de7e32597421de7d32597421de7c32597420067f71597420067e71597420067d71597420067c715974208e7f415974208e7c41597421de7f21597421de7e21597421de7d21597421de7c21597420067f70597420067e70597420067d70597420067c705974208e7f40597420067e40597420067d405974208e7c40597420067f30597420067e30597420067d30597420067c30597421de7f20597421de6f20597421de7e20597421de7d20597420066d20597421de7c20597420067f10597420067e10597420067d10597420067c10597421dcfd76d534202e7e65d53420067d65d534208f3e54d53421f4ff765534202e7e65553421de7d65553421dfae42553420067e6598f420067d6598f4208edf6398f4202cfe7598f42004fd7598f42014fe7498f4208edf4398f42046dc4398f42046df3298f4216edd3298f4201cfe7198f42004fd7198f4216eec2198f42044ff7098f4200cfe7098f42004fd7098f4200cfc7098f42046df3098f42006dd3098f4216eef2098f42006ed2098f420067e6558f420067d6558f4208edc6358f42004ff7558f4202cfc7558f42014fc7458f4208edf4358f4208edc4358f42166df3258f42004ff7158f4201cfc7158f42004ff7058f4200cfe7058f42004fd7058f4200cfc7058f42006df3058f42006dd3058f42166ef2058f42006ed2058f4202cff76d4f4208cfe76d4f42004fd76d4f4202e7e65d4f420067d65d4f42044ff7694f4208cfe7694f42004fd7694f4202e7e6594f420067d6594f4208dbe7494f42005bd7494f420075f5394f42004ff7654f42004fd7654f4208cfc7654f4202e7e6554f420067d6554f42005ef7254f42015ec7254f42044ff7614f4208cfe7614f42004fd7614f4202e7e6514f420067d6514f42164fd7690f420057e7590f420057d7590f420067e6590f420067d6590f4216cff7650f420067e6550f420067d6550f4208f9c4350f420067e65987420067d659874208ef7619874201ef461987420067e65587420067d655874208ef46158742004ff755874202cfc7558742014fc7458742004ff7358742044fc735874208ef7415874208ef441587420aef62158742216ec2158742004ff705874200cfe7058742004fd705874200cfc70587420aeef205
  | 30 => 0xd6318d5208cfe7418d52004fd7418d52044ff7218d5202cfd7218d52046df3218d52186dd3218d5201cfe7118d52004fd7118d52044ff7018d5200cfe7018d52004fd7018d5200cfc7018d52186ef2018d52006ed2018d52014fe7694d52006df6394d52046dc6394d5202f5f5394d52015ee7294d52005ed7294d52014fc7654d5219e7f6554d52006df6354d52006dc6354d52005ef7254d52015ec7254d52004fe76d0d52004fd76d0d5208cfc76d0d5202d7e75d0d520057d75d0d52004fe7690d52004fd7690d52044fc7690d5202d7e7590d520057d7590d52004ff7650d52004fe7650d52004fc7650d52004fe7610d52004fd7610d52044fc7610d520079d4310d5208cfe74d8552004fd74d8552044fe73d8552004fd73d855202cfd72d8552106f621d8552004ff70d855200cfe70d8552004fd70d855200cfc70d8552106ef20d8552006ed20d8552006f710d8552006f510d855222e7f6598552006f7619855222e7f6518552226ef621855201ef66118552006f5611855208cfe74d974208ebe74d9742044fe73d9742004fd73d974208eed72d974201cfe71d9742004fd71d974208cff70d974200cfe70d9742004fd70d974200cfc70d97421e6ef20d9742006ed20d97421dcfd769974208e7f659974208e7c65997421dc7d769974208e7f639974208e7c63997421f73e429974208f6e429974208f3c429974208e7f619974208e7c61997421f76c219974208e7f60997420067e60997420067d609974208e7c60997421f76f20997420076d209974208e7e749974208e7c749974202e7f739974202e7e739974202e7d739974202e7c739974208e7f439974208e7c439974202e7f729974202e7e729974202e7d729974202e7c72997421f67e42997421f67d429974208e7c42997421f67f32997421f67e32997421f67d32997421f67c329974202e7f719974202e7e719974202e7d719974202e7c719974208e7f419974208e7c41997421f67f21997421f67e21997421f67d21997421f67c21997421f66c219974202e7f709974202e7e709974202e7d709974202e7c709974208e7f40997420067e40997420067d409974208e7c40997420067f30997420067e30997420067d30997420067c30997421f67f20997421f66f20997421f67e20997421f67d20997420066d20997421f67c20997420067f10997420067e10997420067d10997420067c109974202cff765974208e7c655974208e7f7559742014fe7459742014fc745974208e7e545974208e7c5459742004ff7359742044fc73597421de7f52597421de7d5259742004ff715974201cfc7159742004ff705974200cfe7059742004fd705974200cfc70597420067f50597420067e50597420067d50597420067c50597421deef2059742006ed205974208d7f7659742
  | 31 => 0x935208ebe749935202ebf549935208ebc5499352044fe7399352004fd739935208ebf42993521e6bd429935201cfe7199352004fd71993521e6ec219935208cff709935200cfe7099352004fd709935200cfc70993521e6ef2099352006ed2099352014fc755935202ebf745935202ebf545935202ebc5459352004ff7359352044fc73593521de7e525935202e7c52593521debf4259352004ff715935201cfc7159352004ff705935200cfe7059352004fd705935200cfc70593521deef2059352006ed2059352014fe7598f52014fc7598f5208cfe7498f52004fd7498f52046de7398f5202edf5398f52046dc5398f52046df3298f521a6dd3298f5201cfe7198f52004fd7198f521a6ec2198f52044ff7098f5200cfe7098f52004fd7098f5200cfc7098f521a6ef2098f52006ed2098f52014fc7558f52004ff7458f5208cfc7458f5202edf7358f5202edf5358f5202edc5358f5219e7e5258f5202e7c5258f5219edf3258f52004ff7158f5201cfc7158f52004ff7058f5200cfe7058f52004fd7058f5200cfc7058f5219eef2058f52006ed2058f5208cff76d0f5202cfe76d0f52004fd76d0f5202d7e75d0f520057d75d0f521776e52d0f52044ff7690f5202cfe7690f52004fd7690f5202d7e7590f520057d7590f5216f6e5290f52004ff7650f52004fd7650f5202cfc7650f52005ef7250f52015ec7250f521676e5250f52044ff7610f5202cfe7610f52004fd7610f520079d4310f52015ee7210f52005ed7210f521476e5210f52014fc7558752004ff745875208cfc7458752004ff7358752044fc735875202ef7715875202ef7515875202ef451587520e6f62158752226ec2158752004ff705875200cfe7058752004fd705875200cfc70587520e6ef2058752006ed2058752044fe73d9152004fd73d915202cfd72d91521f67e52d91521f67c52d91521f6bf42d915201cfe71d9152004fd71d9152004ff70d915200cfe70d9152004fd70d915200cfc70d91521f6ef20d9152006ed20d9152006bf6499152005f77159152005f47159152006bd6419152044fe7319152004fd731915208cff721915202cfd721915208ebf42191521c6bd421915201cfe7119152004fd711915208cff701915200cfe7019152004fd701915200cfc70191521c6ef2019152006ed2019152014fe7695152006bf649515208ebc649515202f3f5495152015ee7295152005ed7295152014fc76551521de7f6555152006bf6455152006bc6455152005ef7255152015ec725515208cfe74d8d52004fd74d8d5202cfd72d8d521b67e52d8d521b67c52d8d521b6df32d8d5201cfe71d8d52004fd71d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d521b6ef20d8d52006ed20d8d52006df6398d52005f77158d52005f47158d52006d
  | 32 => 0x467c65d4c430475e53d4c43004ff7654c430467f6554c430467c6554c4308f3e75d0c4308f3d75d0c43045bd73d0c43046be63d0c43046bf60d0c433b6bd60d0c433afaf20d0c433afad20d0c430475e7590c430475d7590c4308ddd7490c433859d7490c4308ede6490c430479e6490c43046df6090c433a6dd6090c4339fcf2090c4339fcd2090c43004ff7650c43045bf7650c43006bf7650c43004bf7650c43045bf7350c43046be6350c430079f5350c430479e5350c430079d5350c430479c5350c433979e3250c430479c3250c43046bf6050c4338ebd6050c430479f3050c433879e3050c433879d3050c430479c3050c43387af2050c43387ad2050c4308ddf7650c43006df7650c43004df7650c43045df7450c430479f7450c4308ede6450c4308f9e6450c430079f5450c4308f9e5450c430079d5450c4308f9c5450c433979e4250c4308f9c4250c4308edf6050c4338edd6050c4308f9f4050c433879e4050c433879d4050c4308f9c4050c43387cf2050c43387cd2050c430079f7650c430059f7650c430069f7650c430079f7550c430079e7550c430079d7550c430079c7550c430479f6550c430079e6550c430079d6550c430479c6550c430079f7250c433979e7250c430079d7250c433979c7250c430479f6250c433979e6250c430479c6250c433979e5250c433979c5250c430079f7150c430079e7150c430079d7150c430079c7150c430479f6150c430479c6150c433979f2150c433979c2150c433879f7050c433879e7050c433879d7050c433879c7050c430479f6050c4338e9f6050c433879e6050c433879d6050c4338e9d6050c430479c6050c433879f5050c433879e5050c433879d5050c433879c5050c433879f2050c433878f2050c433879e2050c433879d2050c433878d2050c433879c2050c433879f1050c433879e1050c433879d1050c433879c1050c43014ff76588430079d4358843046ec6258843004ff755884302cfc7558843146ec525884308eef425884308eec4258843046ef3258843046ec3258843004ff715884301cfc7158843146ef2158843004ff705884300cfe7058843004fd705884300cfc7058843146ef2058843006ed20588430079d4398443046f7619844301ef461984430057f75584430057c75584430079d4358443005ef7258443145ec7258443046f46158443004ff75584430067f75584430047f755844302cfc75584430067c755844302c7c7558443004ff7258443006ef7258443004ef7258443014fe7258443014fc7258443006ec7258443014ec725844308ef7415844308ef44158443046f73158443046f43158443004ff705844300cfe7058443004fd705844300cfc7058443006ef2058443006ed2058443006f71058443006f51058443014fe7599352014fc759
  | 33 => 0x8705954300cf870595430067f50595430067d5059543006ef2059543006ed2059543004fe761954302e7e65195430067d6519543004fe76d5143044fc76d51430067f65d514302e7c65d5143005de73d5143005dd73d5143004fe769514302e7e65951430067d65951430073f549514302cfc76551430067f655514302e7c6555143005df7355143005dc7355143004fe761514302e7e65151430067d6515143004fe76d4d4308cfc76d4d430067f65d4d4302e7c65d4d43005be74d4d43005bd74d4d43004fe7694d4302e7e6594d430067d6594d430075f5394d4302cff7654d43004fd7654d4302cfc7654d430067f6554d4302e7c6554d43005bf7454d43005bc7454d43004fe7614d4302e7e6514d430067d6514d430057e75d0d430057d75d0d4308f5e75d0d4308f5d75d0d4308ddf70d0d433c5dd70d0d4308f9f40d0d433c79d40d0d433c7cf20d0d433c7cd20d0d430057e7590d430057d7590d430473e7590d430473d7590d430079f6390d43045bf7090d433bdbd7090d430479f3090d433bf9d3090d433bfaf2090d433bfad2090d43014fe76d89430057e75d89430057d75d8943166ee62d894302cfe75d89430067e75d894302c7e75d8943004fd75d89430067d75d89430047d75d8943166ec52d8943166ee42d8943166ee32d894301cfe71d8943004fd71d8943166ec21d8943004ff70d894300cfe70d8943004fd70d894300cfc70d8943166ef20d8943006ed20d8943166ec625894302cfe75d8543004fd75d8543014fe72d8543004fd72d8543014fc72d8543004ff70d854300cfe70d8543004fd70d854300cfc70d8543006ef20d8543006ed20d8543006f761985430057f75585430057c7558543005ef7258543165ec7258543005fb705854315df870585430057e75185430057d751854301ef66118543006f5611854308cfe74d9443046be74d9443044fe73d9443046de73d9443014fe72d9443046ee72d9443014ee72d9443004fd72d9443046ed72d9443004ed72d9443014fc72d944301cfe71d9443004fd71d9443044ff70d944300cfe70d9443004fd70d944300cfc70d9443006ef20d9443006ed20d9443004fd76994430467f65994430467c659944302cff76594430467c6559443044ff75594430467f755944308cfe745944308cfc745944308e7e545944308e7c5459443044fe7359443044fc73594430467e53594430467c5359443004ff7259443014fe7259443014fc72594430067e52594430067c5259443004ff715944301cfc7159443004ff705944300cfe7059443004fd705944300cfc70594430067f50594430067d5059443006ef2059443006ed2059443004fd76d504308e7f65d504308e7c65d504308f3e54d5043004ff765504308e7f655504308e7c6555043004fd76d4c430467f65d4c43
  | 34 => 0x96430067c72596430067e42596430067c42596430467f32596430067e32596430467c32596430067f71596430067e71596430067d71596430067c71596430467f31596430467c31596430067f21596430067c21596430067f70596430067e70596430067d70596430067c70596430067f40596430067e40596430067d40596430067c40596430467f30596430067e30596430067d30596430467c30596430067f20596430066f20596430067e20596430067d20596430066d20596430067c20596430067f10596430067e10596430067d10596430067c105964302e7e65d52430067d65d5243045de73d5243005dd73d524302e7e65952430067d65952430073f549524302cff765524302e7e65552430067d6555243005df7355243045dc735524302e7e65152430067d651524302e7e65d4e430067d65d4e430475e53d4e4302e7e6554e430067d6554e430057e75d0e430057d75d0e430067e65d0e430067d65d0e43045bd76d0e43006bd76d0e430073e75d0e430073d75d0e430473e65d0e430473d65d0e430479e53d0e430079d53d0e43046bf60d0e433d6bd60d0e433cfaf20d0e433cfad20d0e43005dd76d0e4308edd76d0e4308f5e75d0e4308f5d75d0e430075e65d0e430075d65d0e4308f9e54d0e430079d54d0e4308ddf70d0e433cddd70d0e433cfcf20d0e433cfcd20d0e43014ff7658a430067e6558a430067d6558a43046ec6258a43004ff7558a4302cfc7558a4316eee4258a43046ef3258a43046ec3258a43004ff7158a4301cfc7158a4316eec2158a43004ff7058a4300cfe7058a43004fd7058a4300cfc7058a4316eef2058a43006ed2058a430067e65986430067d6598643046f7619864301ef461986430067e65586430067d6558643046f46158643004ff755864302cfc7558643004ff7258643014fe7258643014fc7258643046f73158643046f43158643006f72158643006f42158643004ff705864300cfe7058643004fd705864300cfc7058643006ef2058643006ed2058643006f71058643006f5105864302cfe76d9543014fe72d9543004fd72d9543014fc72d954301cfe71d9543004fd71d9543004ff70d954300cfe70d9543004fd70d954300cfc70d9543006ef20d9543006ed20d95430067f6599543005ef7259543165ec7259543005f77159543005f47159543005fb705954315df870595430067f7559543004ff7459543006bf7459543004ff7359543006df7359543004ff7259543006ef7259543004ef7259543014fe7259543014fc7259543006ec7259543014ec72595430067e52595430067c5259543004ff7159543006f77159543004f7715954301cfc7159543006f4715954301cf47159543004ff7059543006fb7059543004fb705954300cfe7059543004fd705954300cfc7059543006f
  | 35 => 0x75f5394f4302cff7654f4302e7e6554f430067d6554f43005bf7454f4308dbc7454f4302e7e6514f430067d6514f43014ff7658b430067e6558b430067d6558b4308eec6258b43004ff7558b4302cfc7558b4308eef4258b4308eec4258b43176ee3258b43004ff7158b4301cfc7158b43176ec2158b43004ff7058b4300cfe7058b43004fd7058b4300cfc7058b43176ef2058b43006ed2058b430067e65987430067d659874308ef7619874301ef461987430067e65587430067d655874308ef46158743004ff755874302cfc7558743004ff7258743014fe7258743014fc725874308ef7415874308ef44158743006f72158743006f42158743004ff705874300cfe7058743004fd705874300cfc7058743006ef2058743006ed2058743006f71058743006f51058743046bd74d9643046de73d9643014fe72d9643004fd72d9643014fc72d964301cfe71d9643004fd71d9643044ff70d964300cfe70d9643004fd70d964300cfc70d9643006ef20d9643006ed20d9643004fd76996430467f65996430467c65996430047d76996430467f62996430067e62996430467c62996430467f61996430467c61996430467f60996430067e60996430067d60996430467c60996430475f30996430075d30996430076f20996430076d209964302e7f749964302e7d74996430467e73996430467c73996430467c439964302e7f729964302e7e729964302e7d729964302e7c72996430067e42996430067c42996430467f32996430067e32996430467c329964302e7f719964302e7e719964302e7d719964302e7c71996430467f31996430467c31996430067f21996430067c219964302e7f709964302e7e709964302e7d709964302e7c70996430067f40996430067e40996430067d40996430067c40996430467f30996430067e30996430067d30996430467c30996430067f20996430066f20996430067e20996430067d20996430066d20996430067c20996430067f10996430067e10996430067d10996430067c109964302cff76596430467c65596430467f75596430467e53596430467c5359643004ff7259643014fe7259643014fc72596430067e52596430067c5259643004ff715964301cfc7159643004ff705964300cfe7059643004fd705964300cfc70596430067f50596430067e50596430067d50596430067c5059643006ef2059643006ed20596430457f76596430067f765964302c7f76596430467f62596430067e62596430467c62596430467f61596430467c61596430467f60596430067e60596430067d60596430467c60596430475f30596430075d30596430076f20596430076d20596430067f74596430067d74596430467e73596430467c73596430467e43596430467c43596430067f72596430067e72596430067d725
  | 36 => 0xd2058453006f71058453006f5105845308ebe74d974308edd73d9743014fe72d9743004fd72d9743014fc72d974301cfe71d9743004fd71d974308cff70d974300cfe70d9743004fd70d974300cfc70d9743006ef20d9743006ed20d9743004fd769974308e7f659974308e7c65997430047d769974308e7f62997430067e629974308e7c629974308e7f619974308e7c619974308e7f60997430067e60997430067d609974308e7c609974308f3f40997430073d40997430076f20997430076d209974308e7e749974308e7c749974302e7f739974302e7d739974308e7c439974302e7f729974302e7e729974302e7d729974302e7c729974308e7f42997430067e429974308e7c42997430067e32997430067c329974302e7f719974302e7e719974302e7d719974302e7c719974308e7f419974308e7c41997430067f21997430067c219974302e7f709974302e7e709974302e7d709974302e7c709974308e7f40997430067e40997430067d409974308e7c40997430067f30997430067e30997430067d30997430067c30997430067f20997430066f20997430067e20997430067d20997430066d20997430067c20997430067f10997430067e10997430067d10997430067c109974302cff765974308e7c655974308e7f755974308e7e545974308e7c5459743004ff7259743014fe7259743014fc72597430067e52597430067c5259743004ff715974301cfc7159743004ff705974300cfe7059743004fd705974300cfc70597430067f50597430067e50597430067d50597430067c5059743006ef2059743006ed205974308d7f76597430067f765974302c7f765974308e7f62597430067e625974308e7c625974308e7f615974308e7c615974308e7f60597430067e60597430067d605974308e7c605974308f3f40597430073d40597430076f20597430076d205974308e7e745974308e7c74597430067f73597430067d735974308e7f435974308e7c43597430067f72597430067e72597430067d72597430067c725974308e7f42597430067e425974308e7c42597430067e32597430067c32597430067f71597430067e71597430067d71597430067c715974308e7f415974308e7c41597430067f21597430067c21597430067f70597430067e70597430067d70597430067c705974308e7f40597430067e40597430067d405974308e7c40597430067f30597430067e30597430067d30597430067c30597430067f20597430066f20597430067e20597430067d20597430066d20597430067c20597430067f10597430067e10597430067d10597430067c105974302e7e65d53430067d65d534308f3e54d534302e7e65553430067d655534302e7e65d4f430067d65d4f4308dbe74d4f43005bd74d4f4302e7e6594f430067d6594f43
  | 37 => 0x4d530067f6494d530457e7394d530467f6394d5302f5f6394d5302e5f6394d5319d7e7294d530457c7294d530057d7194d530457f7094d534057d7094d534076f2094d534076d2094d53014fe76d895302d7e75d895319eee62d895319f6e52d895308cfe74d8953004fd74d895302cfd73d895319e7e52d895319eee52d895319e6e52d895319e7c52d895319eec42d895319eee32d895301cfe71d8953004fd71d895319eec21d8953004ff70d895300cfe70d8953004fd70d895300cfc70d895319eef20d8953006ed20d895319eec6258953005f77158953005f4715895308cfe74d8553004fd74d8553014fe72d8553004fd72d8553014fc72d8553006f721d8553006f421d8553004ff70d855300cfe70d8553004fd70d855300cfc70d8553006ef20d8553006ed20d8553006f710d8553006f510d8553006f76198553005ef725855319dec725855328e7f651855301ef66118553006f56118553044fe7499053046be749905308e7f549905302ebf549905302e3f549905308ebc549905302e7f5399053046be4399053046bc4399053014fe7299053004fd7299053014fc729905301cfe7199053004fd719905302e7c519905308cff709905300cfe7099053004fd709905300cfc709905308ebf4099053006bd4099053006ef2099053006ed2099053046bf745905302ebf545905302ebc5459053046be4359053046bc4359053004ff7259053014fe7259053014fc7259053004ff715905301cfc7159053004ff705905300cfe7059053004fd705905300cfc7059053006bf4059053006bd4059053006ef2059053006ed205905302d7f76550530067f76550530047f765505302d7f745505302f3f745505308e7e64550530057f73550533fe7e635505302f5e63550531de7e625505302e7c62550532857c715505302e7f60550533f67d60550533ef6f20550533ef6d20550530457f7654c530067f7654c530047f7654c530057f7454c530067e6454c530457f7354c5302f5f7354c530467e6354c530475e6354c5319e7e6254c530467c6254c532857c7154c530467f6054c533e67d6054c533df6f2054c533df6d2054c53004ff745885308cfc7458853046ef725885302eef525885302eec5258853046ef3258853046ec3258853004ff715885301cfc7158853004ff705885300cfe7058853004fd705885300cfc7058853186ef2058853006ed2058853004ff745845308cfc745845302e7f54584530067d545845302e7f53584530067d5358453004ff7258453006ef7258453004ef7258453014fe7258453014fc7258453006ec7258453014ec7258453046f7715845302ef7515845302e7c515845302ef45158453046f73158453046f43158453004ff705845300cfe7058453004fd705845300cfc7058453006ef2058453006e
  | 38 => 0x2f5f74d4e5302f5e74d4e5302f5d74d4e5302f5c74d4e530475f64d4e530075e64d4e530075d64d4e530475c64d4e5302f5f72d4e5302f5e72d4e5302f5d72d4e5302f5c72d4e530475f62d4e534275e62d4e530475c62d4e534275e42d4e534275c42d4e5302f5f71d4e5302f5e71d4e5302f5d71d4e5302f5c71d4e530475f61d4e530475c61d4e534275f21d4e534275c21d4e5302f5f70d4e5302f5e70d4e5302f5d70d4e5302f5c70d4e530475f60d4e5341f5e60d4e5341f5d60d4e530475c60d4e5341f5f40d4e5341f5e40d4e5341f5d40d4e5341f5c40d4e5341f5f20d4e5341f4f20d4e5341f5e20d4e5341f5d20d4e5341f4d20d4e5341f5c20d4e5341f5f10d4e5341f5e10d4e5341f5d10d4e5341f5c10d4e53014ff7658a530075f5358a53046ec6258a53004ff7458a5308cfc7458a53044fc7358a531a6ee5258a531a6ee4258a53046ef3258a53046ec3258a53004ff7158a5301cfc7158a531a6ec2158a53004ff7058a5300cfe7058a53004fd7058a5300cfc7058a531a6ef2058a53006ed2058a530075f5398653046f7619865301ef461986530075f5358653046f46158653004ff745865308cfc74586530067f54586530067d5458653044fc73586530067f5358653004ff7258653014fe7258653014fc7258653046f73158653046f43158653004ff705865300cfe7058653004fd705865300cfc7058653006ef2058653006ed2058653006f71058653006f51058653014fe72d9153004fd72d9153014fc72d91530067e52d91530067c52d915301cfe71d9153004fd71d9153004ff70d915300cfe70d9153004fd70d915300cfc70d91530067f50d91530067d50d9153006ef20d9153006ed20d9153006bf6499153005ef725915319dec7259153005f77159153005f47159153005fb7059153195f87059153006bd6419153014fe7219153004fd7219153014fc721915301cfe7119153004fd711915308cff701915300cfe7019153004fd701915300cfc7019153006ef2019153006ed2019153006bf649515308ebc649515302f3f5495153005de7395153005dd739515302d7e74951530067f64951530073f64951530063f64951530073c64951530457e73951530075e73951530075d739515302e7f639515302f5f639515319d7e729515319d7c72951530057d71951532a67c61951534157f70951534157d70951534176f20951534176d2095153006bf6455153006bc6455153005df7355153005dc73551530057e761515302e7e76151530047e76151534157e741515302f3e74151530067f64151530457e731515302e7f631515302f5f631515319d7e721515302d7c72151530057d711515329e7c611515302d7f701515340d7d701515340f6f201515340f6d201515302dde7394d5302edf6394d530057e749
  | 39 => 0xd719935308cff709935300cfe7099353004fd709935300cfc7099353006be409935308ebc4099353006ef2099353006ed209935302ebf745935302ebf545935302e7c545935302ebc545935302e7c5359353004ff7259353014fe7259353014fc72593530067e525935302e7c5259353004ff715935301cfc715935302e7f5159353004ff705935300cfe7059353004fd705935300cfc705935302e7f50593530067d5059353006be4059353006bc4059353006ef2059353006ed205935302d7d76953530067d769535302f3e74953530067d64953530457e73953531b57e72953531b57c72953530057d71953532a67e619535344d7f709535344d7d709535344f6f209535344f6d2095353004ff7458b5308cfc7458b5302eef7258b5302eef5258b531b67e5258b5302e7c5258b5302eec5258b531b6ee3258b53004ff7158b5301cfc7158b531b6ec2158b53004ff7058b5300cfe7058b53004fd7058b5300cfc7058b531b6ef2058b53006ed2058b53004ff745875308cfc7458753004ff7258753014fe7258753014fc725875302ef7715875302ef7515875302ef45158753004ff705875300cfe7058753004fd705875300cfc7058753006ef2058753006ed2058753046bf6499253044fe7399253046be4399253046bc4399253014fe7299253004fd7299253014fc729925301cfe7199253004fd719925308cff709925300cfe7099253004fd709925300cfc709925308ebf4099253006bd4099253006ef2099253006ed2099253046bc6459253044fc7359253046be4359253046bc4359253004ff7259253014fe7259253014fc7259253004ff715925301cfc7159253004ff705925300cfe7059253004fd705925300cfc7059253006bf4059253006bd4059253006ef2059253006ed20592530057d76d525302e7d76d525308e7e64d52530057d73d525302f5e63d52531f67e62d52531f67c62d525328d7e71d52534467f60d52534467d60d525343f6f20d525343f6d20d525308ebe6495253006bd649525302f3f5495253045de7395253005dd739525302f5f5395253006be6455253006bd6455253005df7355253045dc735525302f5f535525302d7f745525302f3f745525308e7e64552530073e64552530073d64552530057f73552530075f73552530055f73552530075c735525302e7e63552531de7e62552531de7c625525328d7c71552533fe7f60552533fe7d60552534376f20552534376d20552530457d76d4e5302e7d76d4e530057d74d4e530067e64d4e530475e63d4e531b67e62d4e530467c62d4e534275e32d4e530475c32d4e5328d7e71d4e530467f60d4e5342e7d60d4e530475f30d4e5341f5e30d4e5341f5d30d4e530475c30d4e5341f6f20d4e5341f6d20d4e5302f5d76d4e530055d76d4e5302e5d76d4e53
  | 40 => 0x8d54006ed20d8d54006df6398d54005ef7258d541ddec7258d54005f77158d54005f47158d54005fb7058d541d5f87058d54006dd6318d54014fe7218d54004fd7218d54014fc7218d5401cfe7118d54004fd7118d54044ff7018d5400cfe7018d54004fd7018d5400cfc7018d54006ef2018d54006ed2018d54014fe76d895402d7e75d89541deee62d89541df6e52d895402cfd74d8954044fe73d8954004fd73d89541de7e52d89541deee52d89541de6e52d89541de7c52d89541deee42d89541deec32d895401cfe71d8954004fd71d89541deec21d8954004ff70d895400cfe70d8954004fd70d895400cfc70d89541deef20d8954006ed20d89541deec6258954005f77158954005f47158954044fe73d8554004fd73d8554014fe72d8554004fd72d8554014fc72d8554006f721d8554006f421d8554004ff70d855400cfe70d8554004fd70d855400cfc70d8554006ef20d8554006ed20d8554006f710d8554006f510d8554006f76198554005ef72585541ddec72585542a67f651855401ef66118554006f5611855408d7f76550540067f76550540047f765505408d7f745505402f3f745505408e7e645505408f3e64550540057f73550541de7e625505408e7c625505429d7c715505408e7f605505445e7d60550544576f20550544576d205505402e7f5498c540067d5498c54046de7398c540467f5398c5402edf5398c5402e5f5398c54046dc5398c5408edf4398c54046dc4398c54014fe7298c54004fd7298c54014fc7298c5401cfe7198c54004fd7198c5402e7c5198c54044ff7098c5400cfe7098c54004fd7098c5400cfc7098c54046df3098c54006dd3098c54006ef2098c54006ed2098c5408edf7358c5402edf5358c5402edc5358c5408edf4358c5408edc4358c54004ff7258c54014fe7258c54014fc7258c54004ff7158c5401cfc7158c54004ff7058c5400cfe7058c54004fd7058c5400cfc7058c54006df3058c54006dd3058c54006ef2058c54006ed2058c54004ff7358854044fc735885408eef725885402eef525885402eec525885408eef425885408eec4258854004ff715885401cfc7158854004ff705885400cfe7058854004fd705885400cfc70588541c6ef2058854006ed205885402e7f54584540067d5458454004ff7358454044fc735845402e7f5358454004ff7258454006ef7258454004ef7258454014fe7258454014fc7258454006ec7258454014ec725845408ef7715845402ef7515845402e7c515845402ef4515845408ef7415845408ef44158454004ff705845400cfe7058454004fd705845400cfc7058454006ef2058454006ed2058454006f71058454006f5105845408ebe749935302ebf549935308ebc5499353014fe7299353004fd7299353014fc729935301cfe7199353004f
  | 41 => 0x2e7d76d525408f3e64d52540057d73d52541f67e62d525408e7c62d52544773e42d525408f3c42d52542a57e71d525408e7f60d525447e7d60d525408f3f40d525446f3e40d525446f3d40d525408f3c40d525446f6f20d525446f6d20d525402f3d76d52540053d76d525402e3d76d525402f3f73d525402f3e73d525402f3d73d525402f3c73d525408f3f63d525408f3c63d525402f3f72d525402f3e72d525402f3d72d525402f3c72d525408f3f62d52544773e62d525408f3c62d52544773e32d52544773c32d525402f3f71d525402f3e71d525402f3d71d525402f3c71d525408f3f61d525408f3c61d52544773f21d52544773c21d525402f3f70d525402f3e70d525402f3d70d525402f3c70d525408f3f60d525446f3e60d525446f3d60d525408f3c60d525446f3f30d525446f3e30d525446f3d30d525446f3c30d525446f3f20d525446f2f20d525446f3e20d525446f3d20d525446f2d20d525446f3c20d525446f3f10d525446f3e10d525446f3d10d525446f3c10d52540073f5498e5408edf6398e5408cfe7498e540067f5498e5408edf4398e54046dc4398e54014fe7298e54004fd7298e54014fc7298e5401cfe7198e54004fd7198e54044ff7098e5400cfe7098e54004fd7098e5400cfc7098e54046df3098e54006dd3098e54006ef2098e54006ed2098e540073f5458e5408edc6358e5408cfc7458e5408edf4358e5408edc4358e54004ff7258e54014fe7258e54014fc7258e54004ff7158e5401cfc7158e54004ff7058e5400cfe7058e54004fd7058e5400cfc7058e54006df3058e54006dd3058e54006ef2058e54006ed2058e54014ff7658a540073f5458a5408eec6258a5408cfc7458a54004ff7358a54044fc7358a541e6ee5258a5408eef4258a5408eec4258a541e6ee3258a54004ff7158a5401cfc7158a541e6ec2158a54004ff7058a5400cfe7058a54004fd7058a5400cfc7058a541e6ef2058a54006ed2058a540073f549865408ef7619865401ef461986540073f545865408ef4615865408cfc74586540067f5458654004ff7358654044fc7358654004ff7258654014fe7258654014fc725865408ef7415865408ef44158654004ff705865400cfe7058654004fd705865400cfc7058654006ef2058654006ed2058654006f71058654006f5105865402dbe749515402ebf649515408d7e749515408e7f649515402f3f649515402e3f64951540057e73951541dd7e729515408d7c72951540057d719515408d7f70951544657d70951544676f20951544676d20951540067e54d8d54014fe72d8d54004fd72d8d54014fc72d8d540067e52d8d540067c52d8d5401cfe71d8d54004fd71d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d540067f50d8d540067d50d8d54006ef20d
  | 42 => 0x10811005860004000811031030c91820c414604408300404108708004e1421430130040041c50000400c30400010c41013c01c800b3000400800c50050c40000401410401410001c10440403800020421820071401401471c01890830880020011c01420800010010c90403830411c11030010800001010011410000440440030820042001c100500500d0460810090050823061c01820c234008020004008400000404304e5850410c90c00410440850012401400000800010010000070810030c40000002010421010434880482030c01c40c11460001410000c31420c40c00480c20851802021032400010010000800850c034c1c12000000010000010c10801ca0020010820040010030c00050030880030420080410014001010800420012010c00000c014014300120f0812c50c80840c50801800820c001004004008310108518009300218100e0400020440c00840c00061400813c40090001c00020800041482810080030c010200100404008208100200a0000810c03401811010c00811030090011800830080c10032421400c16080018850040010411010830050802020c01c00410040050011010445400432010000000850090040020020841400c10020c00020012400400020030061801400040010000410050c00832410880400000c001200004500110300318010000800144900400a0080400400840c03440030801c09c004104210c0002400c208314508008718714b0001420052441951830430400030c034a3060040010400800801c00002000030c200314820f0030082434030c1043081280006280080080185101000046de7398f5402edf5398f54046dc5398f54014fe7298f54004fd7298f54014fc7298f5401cfe7198f54004fd7198f54044ff7098f5400cfe7098f54004fd7098f5400cfc7098f54006de3098f54046dc3098f54006ef2098f54006ed2098f5402e7c5458f5402edf7358f5402edf5358f5402e7c5358f5402edc5358f54004ff7258f54014fe7258f54014fc7258f540067e5258f5402e7c5258f54004ff7158f5401cfc7158f5402e7f5158f54004ff7058f5400cfe7058f54004fd7058f5400cfc7058f5402e7f5058f540067d5058f54006de3058f54006dc3058f54006ef2058f54006ed2058f54004ff7358b54044fc7358b5402eef7258b5402eef5258b541f67e5258b5402e7c5258b5402eec5258b541f6ee4258b54004ff7158b5401cfc7158b541f6ec2158b54004ff7058b5400cfe7058b54004fd7058b5400cfc7058b541f6ef2058b54006ed2058b54004ff7358754044fc7358754004ff7258754014fe7258754014fc725875402ef7715875402ef7515875402ef45158754004ff705875400cfe7058754004fd705875400cfc7058754006ef2058754006ed205875408d7d76d5254
  | 43 => 0x400800a1081010430000150400400c50820011460410016801c00820420021800440090820000430c40010860000060012130000010010ca0000400040000011020400000410011400410020002c100004504000110d18104014108000014108008000014404e2820c00001053010400080420410020401403d30400003c40450c31001c20110401110400050011840002800410020881400c20400072c204404018000104b1800840020810cd00c14634600009c0c50010012400410c20000060830400001871401010810852c30400020800001020c20030810010022860090052c008618000100008100401c0400810c30c014400d0c50411030020800020c61010812000062151090000430450091870413010c60000000800030031410402c100700204200b00000600200558200a00e1020003860030020400000011470c208001140108304504018f2420080030010010800c004108334b0405c008108000000a0010000800880120800474030031050401c308318000400704000520100200f00100b0812800000420c808304604704400c1040c108000200204504004700105910300e0000012420410070090010010c33000000000c00802010001c31800050032400030402410010800c200c0800000cf0420000060000800d20020001c038204000000200300416124000108000804608224008018200204d0800800410460022c004c0020000030004c004014a1080c308300b0c10c108100014500c1800010001010400c10400c10c20c00012801000031850841c00010000801071400000400c410408000010a0400000000480800030824c00420430150c704250314b0c00001801c90050400001801400021850811412c90400020012010002810020004000800411c00000040080410060820411c628504104104300a00019c1820830413c31c32000001050c10020c534000b0010410031400c10062c318004334000000000004a0081c000018000000000004204400108004108218014100318f0c20400800013000821410810040c21880440011071c30420416400430050020c34010420030c00040010000401000400080020400050820460040000010830024400400040820401400060450440c004514200e1c30c90020410c100104d00604302404d0013c004208100a24300608400804100400000000018900018000300200d1c03c00071860000052010805801001ca2050010810420c40011c61c500129400100100004b0c51010040c200420001124104000100104a0000c60003100421001490020800812c104200800000200004100205a0810880011cb0002400000400001045460820400010c508124100001e2010412001802800000ce0012870000c00020000010070060800000810831820c00030041051c108c0
  | 44 => 0x188cac00001610000ba780000000000000000024d800000034a274882227c299a836b070e7858e7e5bc00002abb7d6bdd19ba000000000000002588000000083cd73129c00034ae00033fe2b283ce9a5b76e2ecaf18d7bb00a5afaf5653b8588a930aa299c14d452780000000000d4207bc5b58000000000014f03d631b1b2c8a280000000000d6b800067bafc00001b1800000000000ddc8b780000002438d6320200000000a1e8000000000000016c6128b7f0ace00000001bc25280b3800017309ff000050e8d5ea590000d589880dca2db20000c5039633e41db8000000000000000000000f52ccc80002ad36ac00007fa000156a1dc00ee00d8000000124ccbe938abe29170623000021036c6b972c36bf80000c3900006ab000000037a267a38148d526b824016ea00017f8b1180000000326b6a0000000381a8afb38077f8000aea041800000007d20c980000c40bad00000002668d5aae6ca48190a5aca2d4c8a00fa0380cf6d230000000000000000008be80001b280009ca00000001928000246e64e800000000005509cd00000000aef122a0c4a9d82b4952a3bb00005140000dd735f600000000fe80006fb37a431336480002ef86083512245a2103fa1f2a6259a3800000005e38000000143e00000000000000000131400000000000000d888a800000000a11240253d8000d6705b2000000000000000001a120000000a89000052125d83e7800010b135600000000002c4400000000000d1a9f49f6670300005fd00003f60f16bb092960000c320000000d400000000348e0000000498000000016a6aa20bc821e000000030160000000c3e954e1838000c5680ca8860772000357687a20a869f844ed20800077e0fc05b700009b808f65cd1028000000063d1742000092c0002d067ad8000dce1d74ba0275ed87196e6078000000000053c800000000007a789460002bd600037be0000000ad3a158000000000000000000000000087c0000000adb9128c2d80001818e88ce6925a82684940b59824a489560cb427604ee376cb0800002f099a000000006f01ca60000a4cad682708939ff88771d5236d8f1a040857664980004e400000000000000102691198b00000000d3e00008bb0244905abf8747000000034dc42f349600015ee13886d48ec810411c70471401800410830530800013c05c004300d04304c04214000204700000c2480800050cc0000c31890000004000890400810000813052c20000000830483020430800860410041440062870070010020420420c01000020400c00590430460060470431080c11c00000020c11810420810800002800c10090c00032810861811000031011441013801811411800460061c008000914000018a0001800000020000011061170000c00000410080c638000d04604504004700
  | 45 => 0x2fbb6300001922bd8800000000000000000b3a8e32000039cc63091483c8cf06711ad200030544cb208202c0000b23800000035bad3f9dcc20129aa732000012916924d780003e480000000000000000000000fe5520000184806e0418000b40047264499f0a1e0000000000039d800000000000a59500000000099584d0000013c00000000001c3ec501a84b4d0e2a0a726de287000077213bc64d8000a738000769340a5f980000000d0e2ee8000000000028604702e08f1800005aa63c05208f00000000000000000000001c160000000951000000000ea000000047782920000000cbb800084292800a315f4e2083f6db722a48d991e01d6b59ecd98000506887000000000000000000320800013de00006ec00000000000000cdeaebc63a8d684dc025a1ed00008722f880000000696000047c9d16cdb80148b18000000349827f14861a400000000614cc4800034928e60001f980001a020c4000000025940000d5a2b1800064c296a36780000002982c93000085c0000d4422e41be800092380000cd809e3670c3ed0a32ba0940000c2aa460d17aa8ea362ccc000127632c09d8abd800000026329a080000000000000000026400002068000a810c040000000000089600013da00016e4d8b8540447b17469e28fecbc8d7a6e1322c154aee4597b186ac580004c58000000298e00000000002e92000281c0000000000000000000000000dc0d66800000000000002048000125c0000000885ab0a000291aac98d7e00012fe4a28000d90b60ab4d8ba40001ef2c708000b940000da6a8b8bb995d09b20ccc44e29e46041562000000020b8000b550000e1fa0ec3c721900e9b1fc2789d260000000e130000b9f237a0000000ade80000002d9692280000000000c94800053a8000000242c00035580000000c60000000019be3458000cc12924000110e000360c9242918ac6800097c107c0002b1022188ec82e137e332b864b1eaeecdf78000b1c2b8882d0fa49b60000000248c0000000a76aeba3f7000004a8000b4f800000029a20f0800087aaa58000105a9ad9d0400029880c22412a9ca1723ccb2d22088000000000087c1ffec329d2c00000000000000d8500000000000158161a000052c7928000daab3302a90000000000076a80000001df65f1000020000000000db43e1884ab5b15341038104de380004b589e60002b62d01af34000232c0000000d1d0848dc8800000011cc1d28674b6b30be951abc42c1132800909dc12b06208e008425dd00001ca8f24bef8000c4f800000030dc96d2492c669d9c13a80000001e3c0002b5e4a3833a0002cd43ec808e00000000000630b52b78200000000000000000368089e000000007fc0fd0ee40451908000202400037e85ba000000000000000000747b522cd6000000000002538c287821
  | 46 => 0x2f06b7f03e6cfa1952d16253098b0000719aa38b6315065faa82c89c80008c600005ae11a2000185032c998c2e51fe005f0000000189a00023121168000db30912d7286b800000000000000000000065380000002bca0000000297b10a60184a86c5960200029160003370c332514aac820400003fc6c2800000000000000000b291240000000058100009b4000008c000026b0b4a71a800013a000067f0000cd42d945d228c20000000c4695180000000376aa98de400006a72c0a8ee907a00000009fe000013e0000c0916060000000000000000002ec0000000000000072b8000b2034de00000001d88c8a000000000000007b080008de238a000144463800000d700004dd03a092c00001df16d8a3e2e9ad84b7440660000d6429b80000000000000071380ae62e000000000006ce0ae400000000003018e1380000000000000000063411bcb69b5d2000000036facdec0d894200012e0000000000000003318000000000000000000000000000000000029c05ff9650b43264e17480006d21f1c000000000037dc000202276da7ea00027dc0001612b1daf0cc879f441c2aba25bd938200031ec0001510d770000417a8366f432181c60a760000fee00000006be000017f277886e80007ff00007db9f4e00000000001ac223e800000000000001c5c0000000000000033012e60000000000040833e801600004665230d0a64f2d5c25e213e6daaf780000b46c021e2cdc080008832d460000000344828e02b088cd628000a70800000013ac000000086900001cb800035080000000000793000000000008822c22000086200000005b33314662200479f00000000fac00000000002d3c49b0000ad09faa4658000ce780003a7000050badca2df9a10368168e4a1211e6a48000000000000035b00001ed20002d7a0002a168da21168330f0a9c082c8525998e22534d4c5734a00002cce000078e9ac000053780009c580008252c94b9785be6ac21660001c5644c00009309860d0f90322d78000bec0cc4143800000000000000000000035400008580001b98a8080009eda5e683b9bdac2b9d7239180007780c1c17b000000000000000414d98000000021ae000023e5da1e780000000697000000000006fc8000947000040f2fb80002dd800034ec00000000000000091ae2600004c200000000000e548808000b77a340ce5b7b0cf7800060619b820fa3ce00000000879112a2a1ebcc4919d6b8081ac1a58458ca80a04353a012cfb00000000000000278abeb00000e2884c38621dad382b044ea800000000000002d7600028a60003272a6100000cf1dd632985ba95780003de94fc000000000032824138000af8158e0002ac89528efc4e394a4c4803586c098c87f6000078132f022880000002b020000000000206a000000089f837e7c49e8c
  | 47 => 0x225800024eecb680007cc0000000324a0000000cbf117c2322c4a3ba33f474ea2f2c6e0020726ae320820a06857a0703b4b4144a7acba485906cb1b115495b0808437846a6b9000094104ca000000000000000000634d968a2c7359e0e3b7a1362169a3acea17dedec8000000371c55980006a40000000123061e8000cc180006402164000215446c8000138000022f846e000000074006e4d1400000000000000117800000000000e82de7000000000001d18d280000f280000ff84528cda03b114e0000000b0a2b6476d337e03e0000a550e26466379e16480000000000524038c3921cfa2958000000003a01f000000017d095e8000000000064e0000a4180009f300007540d2a4a4975c000000000020a687fb67e45bb5480ee991cdbe00007bda1000000cc20000930c73b7565ef0000c202d6e0000000a9f83e4000000000000006850000dea19c80000000000000031f000046d80002e985dcd0a8000ba91bc800000004ba83300001cd800010c0000285ac2426360002f7a081ac0c00129565cbb6a0ae58a260001580365b07c3cf00000cd000000022423649338c5da392c5a9f369fc8b56b5a8000add00008ea80000001cac00000006a90178a3a8000c938fc228e11187650ca02cc0c382e3000005e979a000134a285000000000009950000000385ccb1071444023a80001cf8d5984fa910000000031c454294aa00000000002032000000000004120001f9a16d8000d8fa53469bb5321132a960758e12d2c2c1a12125aab7e3554000381808db19e18880004e98000d690000000020069d0d8ad7a000007cb0f6495b00e57a000061ba74e0000fc400029d2a0825ec000000000036d257988b20003690a66252e6e200003f195b8af3000000014ce1d7000000027e20001f040000000b1f09c8000231047b076629136da000800000000000002e760002b48000000052a01322f4210cc3b1f6cc011a6ab3a00004d08000000000000015c28508cead8b2a0608600000dc31aa0000000267800054500004e80000000018225dacbc000227a70f10ac19a80007090000cd180000000000000119259f00001618000d169278000230a69409729c9aada00014b40000000bfd00006b68000059800000035b213dadec0dba220903174a40480006210000b9000002f000002c1b0600f0152800002540002dee00000005e02124ca7800000010ba2a5b1d800023507d8271e0000000c3a341c00000f4000000000000004d500000000000000089074f8000b91800084aab283512f142bab67a029237228e99627969a0828a2712230014858a80004e9071200000005130000deb0000526800063e0866baaa1a6386920c6718ae27f0000061a9048e1181dca4f8f5a0000b1a0000000000365800000000000ea8d29000098ea9e6249
  | 48 => 0xcb78c3dd300c7ce0b00b74a0e49baa4d01e72828000000045a000047c080c4cc1f58bf73068c2e99b4b75899407530f4000000000000000001a5a7738000000096e55f00009e180007ef304cd3c93fe60f00004ff07c6d39a750000000000016b4cd880b20001efe000204000036e0519800000000000003046a6500008059ce600023f000006c60000000097acb44f8aaca59200007eb000000000009de8f2a00000000000000ad6146e07d0000464000000006dcb00135038bacfc00000000000000d930ad87b8a30e4e2279842c2b1c84e28e200034641aa8b2e000024880031e4b171b202220e401229576000000000000007392b08000110a00000000001ff60001fd2000000027288a600017aabf400000ea8ff600018e895da5e000006ea47faea24fa0000d3626f66280ef87a90000000377ac109dbc0000000115000015d00000000f6481a29028caaeb20000000d9100000000000479800056d00000070f2e65e1bb40000000de8239638431f0d9c00000d880002948000000076a9c3a602b6d014e64300001638b10000123a00000004ec1480d15800000032544f008e20000ef400000008a5170469902bc55eb0c0a560086dc52a7c9be243e00000000000d580000158c5800009930000cd800007c92a2a00023e64e00000000064499da2c24c824524ecaa1088e80000ad2c86cd0060ce153784379365e4e89d7a29500003ef0000832800015b0996261294c20800000000000254815600013f6c5630260000a66a3b352a0000000c190000033a94677936ca052800000006a60000000000000000000006b980008a61124a118ebab320000c1d8000bba887667ea17e0000880e02894a8f19bb05e180003001d6e9c62f36602800021fa56a825a3ee15c00009a80fbe0000000500b276542164e00000000000dd4000000048897b8000365c9f925200000000a7f11a40000760000314800000001c700000001830a6488ae39681882ed25d673f86d84560bf279da8ae5c6aaaa074000088987a693d87ca878000000000006b22c52423800072100002879d7656a00003048000cda800000001a60048000000000076100000000000df00000853b0f2d6fa28003f000019b00005c8000000000002d4000031a07e601f95aa44125520ec82d800000002420000a2f85c800000005528000000186c6b431180001eac127b87c000220e00000000000000000237e3ec0fe011b15ba14a111a00032a400024e800007b6d860000b38285800000009ef000000000009d100000001bc442129360002c5a00000ba20e00000002186d7380005100000000000000000000a7a0282b50000000000012d311248e000000035c800014d251c299e000000047b964cc9997ae00011b8be99ccaa710c8eb421b780002f320000b7800007a400003a8721800
  | 49 => 0xca165aa2cbb137603a48c2e0bf0b0a13f8bb0c4c015055e25227cb2488e1d8000000334c73c8000477000000020800de000033b95b00e20000000034a7f3331c43baf2a00023342a68cce31aa0fca5e8ba037582868d10000b139b442a781ba81f1a1e0003344dafa3dea208000793b08c1fa800000000005a20000000161400000001bf9a0e00000000000ef6000000057188ce65e8000c6d8000528a68c85200000d4946a0000ee600000000000262649000000000000003710ac198367b7090e0000000000274cb560000000237627cade40000000000000000000004c300007fb80007080046bd700000002aa800027b2b04b3fcdcf0000c89289041581004de847428caff6d0325280000d8e0000000c1d0000000239c000000048b0a4a1ab28020002aee000000042e1e0a66b150c000000000003b8000000000010d6000000060f80000001cb800000000001a30a42b80c0001bfe0000496000045e00007f80000000000000032f00001458df627b800006fa9608531ed6583a590d0d1726481355297ea33ab259ceeb240d062d0802898c2c0845d8000d1eb15656880d2399000000000000001d2a0000000000000031601903c400003e68000df300003698000d3d940606a8c4acd50a0a2f58b6e0bab67c00014288a580000000000b588000d7b231a000000000000000002d9a0f48000dbb0000000000096b85ac137000000025a000011400000000e102e004920dec55313b421d0c6e80f88d0aceb4ce01c800011103720001caa40183060e0091818f2f402ef902400025b2cdc9626d4596e00003394000088400004dec868e6c0002ae6b6f00000001e903f9800089016ec0002faa2b825e44fc10463e42e683f294c251fa53caa2b49eb0b80004b20000000109e000000000011645a6a638cc200009cfa3b600011d8000099a000260456700007ed0dccbeb800000000000000000d620988000277600009f8000000072380003ea000000025780001bde0000d32c7200008c59d68af197b216a00001071f760000000ac908ea01e000063f0640999800013b8000a3727622c82a64e1a95688ff9a3657b0b680000000bd08000380806000000000002128000000017c17d20001cb61a11b1e69780003b02680000314e4739baca8d8fa0d7192101f116e60439efa0000000b44800080f05a0000292a1aa1f800c008186b30d820000000000000012ba1c6a348f62a2290e6b78009a7870000000078a0002038a3daac09caa25edada92e92fa96877100004848000171892e1d30000000000000020640000000aeb30c8cd788fe0000000451000002e000000980005fb9a1646d000061680000792dead7eb7300002f980000c700000000000000000004649252b52a06969c92ca60adfe3700260a2cae20077e8f2a054076800018699aa71
  | 50 => 0x7ec000000000003a18000c5c80008a210c4a62aa660000d567208a9435cb15e0000000000000000032ca9ed17ce0000eda0000000987ad3828dae062e42d9e86e28123cdafe6000199eb348000cf18000623887a00000000000000a90a5c0bc91d7882ba8fc00028ca554800081197620000000000000000021964b380000000000000000000000000000000d36b5d6b719dc29c826e4be401309e91044cf60a5c7c6992e1c1800087380007f680006800000bb2a5debe691d059800540001d020001cdcd57a30898aa84200000008a80000b072a5238f8000180878c9302f547b1a5f61f6a50806492ec65d80000000c9e48c8000851b68a000353496919d226825d2c8593f298fac5694786541ff8c605d036ea00012985d58000b2314381589a8ca4b34840001ac4285823a000000000029cc0001b763170000bf3b1844d1a16e0000000141000065788e8000000000000006fe8000000000052f8b14ba3327c000000002d9cf6000000065ca9be84d3022d2e12aab470000000231e09080000000000000000000031d40000000c39b1bed45278844d90780000000bd327d0b738000bb780000002ee81350000dbc2d0e0000000b5c8e660b52b4a0000aec9298000ad100000002a70c5e9994270327e06cb806c4d00000000000000000000010640002a680000dca0000000b8a80009af0000cf6952200019100001ddc0001e140002cc48ca000000019b00000000000205e0002dba290800000008f0b4127da62a2ffe30ab6f6d0e0000000272c00000007e08000d0c0bcc00034ee67fa5660aa8000000000056facf836e92b84e720848b400000000a8c000093aacd000092120c4635af7c751000075780000001c9600033221a6a5ac5c51c7c0002ce600000000001afa111b0eae0100000000000000000000031960001ec480b80009860000753a6600aa073e15a32aa7e580000000a68000000000000000000000400013e049800000005460f202a4bb019bc00000002d037ae0000000000000093c0c1e000000098d00000000000000000035ba752be9159688d80005038ea41390274046a4548129986bc4332a35f358e27488bc68104f0000050c69880001668a22000000000032b64619fdcc2a1b7e00000681d3800026f8e7000015fe0003646a9db0f0966864e93d13ea0002e1cd4300000003844000000000000000001f7a77eb5fc95d000020a9bd4c06800000000006ac822c5619c7aabc1d46b7eb38a0002ee29b2b18a3df187c1c0348a00000000000000000000056400003231a40000000011005ee3ed815ab95800000000000000174000000000010fa75f80000000000b638c025b680005149ea00000a7a00000000001ff4000119400000003c89c60d580000000029a624892aaab81c6a4401ae5f632a23f4a7ba4459d
  | 51 => 0x7d6000000071b000020e800000010e200035e074496780002efc00000001568e0000000004a1b286b8d1a982e192b68f9000000014c69d2000000000000000fcc17400000000000bd115f62d3b0442598cf4763157289d1a4e18f8000c378000a6c800060e00000000000000323e11887340000e5c0000000daa00000000fdaa6b8d3c94692be3ff9010ccb8000742800018e0000807805c000225a169b31adfaa68600000008e98000d3a0e903d222f80002afc9262d1600002200000b28199851e4241c880000000d0780004c4310c6c20280000000000000004a68db200000004408000a6a00000000000000235c00000000002db000013d61be0000b4b80c8573a17670c24e2d9887ac2fd338c6e80f40df508cac9423acaf0b32cd6b0000000000000000004b10a7461f8000d9cb466d5f80000000000935000032b9bee06d1b5c420a3eadfba11c54c000048832e4b7a00000003258d4700000000000a2d80000002a1c14200001b4800094180000000000b36a94e0f78000000000025f00001840f1400000004df00000000000000000000000000001122b2b80009c52f123ababbeda5115038181fe0000b2600008e47b9877a00035a087e0000b40a7a84332afa09db0b89b49fe679ead6052bab000000de0000093e0000000c00800000009ba7c18000821800000028f299780003d580000000000b8f2e5a6559e200001f56a2c2b120001fe800035560000000000000000000000001c3a0001e540000d6200000000000000db1345c0590e563530dead410000892276e0002ef271602b60000000c2881ca5962cd81402a6000021049d59ce88620000000000000006c800000003eea1c270d81e0652800000021f400000004712f6600019c000000003fe80007433290bfc80000000000189203426d0de216723045f2000088a19d4000000028682667aea9484e1918a0001258d5a000047aac0600001403fc0a8200000008c9000060300000000c4800014761bc9d649b8800010a800000028a25d180009588000bc98ea0000347053f80000b0054c5bf0000755a28e321b75a000000000031f8a0c000078303ac0002e780000000c4580003dba5808d6ae307190000000139200000007c60ac4000000000013d442d25e81ee0dd261900003b180009291fa471280002f9000000000000002a220000000bb38000202aefa26389b81ba00000003716000000000021f2637043884b000000010a68f5b5467d90000000000000000009daa2aa000000000013660002f20000000041d000000000007890f4c540a40e00017900000fe45a88000576257e00029b64ce81fa0002a9215722ce00006a02ea238e57290a8b648ab0000000000007a8000000008a11ae4b282c29259ec096c24de2bd1c22b8427ac248b736a578f3030806ae12db68e0
  | 52 => 0x3600892b502af8000000024a0000ccfa36a402000000005182190000938271c37c2ef01e200002ce8000cf287aa92f093c662974c0d309e09c90000bfc00000000000afa30ac0000000000317020500000000000c638000637800077a000000000005820000000000043407a235980000000bf60000000c362c427e115380001af60000d180000000000000000024ae5ff0ed092708b89aa8d2272f800000000001260ace177832c0000000c5286be35723861d5aaac00035d00188000574a1d029c0000df900000002bf65333072c7fa87611f0000169039e2fa918000006169a6a78400026be7bf000000027a6ae4886c00029e800000001cb185c77b1ace25d00000dd0000728107e0000000816b594000000074a1e3800000006ceb26a1bc0000b1304d286606cc00009c4000160c000043c2e79f4651ca81640e1b5686d158200009d4a2e80000001b42bf7a45ea9700000000d2c0000000000000000036d600027ca1b003ec00010e8df280000000e300002f60b7d8ed4e080000000145e0000fd6000000000034fc669945a06809c629426f0ab910862fa14880001e5263600009ae9c1e22c0000cb08a026f8b3a29d2a89624cb0fe1b989b6b50b62686c000000000001650000000030e1862b400001c8023c800039d0000000000000000003ce8ad087d8000201a5000001782ce20e4e0001a2c8c0b1f27971c68768b7f47148000823250c0002e2e2cf00006e035a2a7c38260ae139a00026c0acb00001e00b6a00024b40001b920ae83201600000000313ca2119cebff0000ce62b700003152bce00000000000aba00000000f782d48c543498000155000000000004bc87e003780220001fe2b949bb6ac80992b098afe42bb56e000000000000000000000000155c9a8800000022bc8b1369877d06ba4d0184294c85f6442372e8ae27c8c100000667264800004c01ce94c8000000000000000000340bc880008d8b85800000004039282651ac3c0000000000196adf48000000000052e00009df0000000000000028aaadb05106f300000001622dff800000000001b5b4c00d8000003100001c9000044195a6000000009e26f20002a743528000a3807d62ff9364003168a5cdb1b00000000bed8000a6f0000ab0831e00000001540000c3127220000000000388ad6134d60002f9400009f634f8000000000081737ce585b57a3949a5400000004100f76d6600008342c24d800000000000058d00001469e44ced309c351b788d820000d01385aae28970a77000000003f2000225c0002974000000054680009fb1aa00000f0c000237c00016d40000000764aa6288c3732d4c00004bd80000003460000000087e80007491a3e3dc92a24c005b8c47289a68a0a8e05c02264f420101728000e0e00000000d409f780003f5000000016c80001
  | 53 => 0x12a6000376a9e8256e6f82688a589564a87b2365a60000ca51e2ab47a61a3cfb526875adf20e51ba2aa536505f8a3ae3c8000000000005be0dfe000000000027420000000000293a0259624000000073500000000000519262200032ae5e2944e8fe00003689d5cdae800096612f06af8000c3e2e4c0001002a05226c1ad000067e32d60001d065949422000313894b00000001a6cc172110da11dd4cc7ac687ea0000213b30c6b7309483da95a0001a96def0000c698000a5c80000000000c1b9e482b01dd8912b3f6217355cc880b36d60a2b048380000002a340001a520002fc6000000086da8700000000000301eac8b6387df800000006920e6123400000002530000000298c00000002b6adc000000000000000000000000000006d280003940000c6818ae74d0000000327438e951e49500000001a1800027300001ea28580000c92000000000000002fee000365675300004ab22f614c800000000000001148a4d269000000006c3ac6a000000000022620002e7439e00003ab054a0000000a0f8f50802b4943cd000000037400000000b838000000325e0000000bb30000000089c00030780000000000000000036204068268bd68000000233e45b30c6db98000000073000019b299a80000000000000000081b2ca20000cbe0000000d24135aa0c82e60000c22705096aa140000716a08a0002178d9e270a82cb77e12813e428035865af34f0000378a6568000000240a00030380000000000000000026d400000007f1800023580008ab80000002b8600000000f280007a380003b7332400000000001c8c00000007f528c661d000000025da6760000000000007322d87b80b6408e23dcbcf9e0262082d0a84b238b5400000000e80000000000010eab222464a92a5b800000000000000000233010d000041316c0000000004494f00e880000002ac6bd780008d59db2b4a00002f180004c188fc2e8865caecb1080a2271093eab3c08f000017513120000000000000077680000b100000000000000000000000005ab37582dc00000002398c4002e25209c04000140a0001aaec3686688ad0506000338609e9c107c0011cb981868d76af863fc9862a8c9e80983b5b417ea5c832902144fb800000023a400013ae9dc00008ee0000000000001b00000000482000326c00037e600000000000000a3d024cb732bfa0001a68a9ea7320000000638953a000040040d32880000e3817680000000000afba20a9f08000000127aad4000000004ec102b0000000000b2e00004d8b1e05c0000093a80007afb0d400000004351540ae10bda8cb8000468255603a0000000038400034c6814b5f0c0e9c260003624200968c0d098ec0ef20fa0002f8c00000003709804c4a80000002652000000011e0000000289c992a1140003798db011c20002a0c
  | 54 => 0x21f90302a64089a7a6800000000002ef0000000000066106b6d09382c16280007ba00000000000000000069db4220000948cec0000000000000018f20000000c8c00000000000000000079b00000000e68d0e80007df0000000000046c00000001d820ab18c64d48000b2780000000000590a246ab40b08000000094d88d400000003e60000354aa0819621061f0ada06c70000000000000033ba00018fee198000ce912283c18526c0d28bcc16ad820002d8679c8a5a79008242e01cba33896744e325c600035b800aaba60001fb23ebb53a000000004e94e299080008ba80000000000c839f5c08b946035da57c0ef9bd8000000000000000000000952000000000000002ad600000000000000dfb000000000006ca1c4c76a1670abd035a0000000000000000000000001b4039b915a0000f94000000000000000000000a1d00007d40ac800000006cc9b3e0001bae0001546000000000000004dca75a00000a657eb13a5c59de68dbb02e0588000d8123f41d7b316c21ab309aba0e20a295b63a385827fc82ae3c4b30e00006c267d20a0e0485f443710f68b5a06e41a96d0000112662d258a6b193dc0000cf20002f4a2ba14948570000000069400022a60000b229b6800091d800009f2d5200000004dbb4d0bb58000cf01a8eacc8110835363c0000000e1800000000ab2d792ad833800006009aa600009b083a8000aed36bc551334200000006eeb1c000018ce50100000000a1200032c09618000be585586fa81e60002b36000337c0c33564766160a61d8386c0c8000cca1c5454f800000020360000c440002fa2d92b28a6669db800018bc62f9b5adc81cea1b4273a1f49aa8c7280007f3974e000000000000000000000c8700007bd3628842083645800005a00000693037a0000000963000000000cc97f8000000357c000164a000000000000001c08000000000000000000000000000139e0000eaa4ab899cae933d2045800000002e87ab826ac35800007880000001184a3c000000012e437e00007000aba000343627ea290c9ba0740f600000cc8566bc70aa8000000022d87ae939264600014166ef8000000000000000006eca34e000120ad0cb79a2838c660000000cba2c6e000076c3630f8c8a4b7b80000000000000000000000000000000000000000005d78000a89800000000007142fb266ba478000000000000005900000414800083720300f319ccd14924200030580190d7000008f4000039a00000000000000ca100006290000000341aa7c951c00000000002bba0002996000000000000005562e98000090cd7ab198000352c00031cc71bae2c9ea8a980000000a742e62668860aa24aa560000000000112c0000000786a07217e0000000221a10800000002e4898a223e5d9afd6dc996a8065a1c09f8356c0000000000
  | 55 => 0x1ab46dc612665780dfc65b30980002c4057200000000000a0186ce99e230c2beab0e04e0000000052a0000e1618ead0a0002a9c5a7800081f9f8c62700000250366d2480000001b8250d952cce70cbaa950e626f3b7fc97700009b1001ed7600c68138000c268000e1580009e00d6c1c691da0003122115896c00000006bf00000000000ba28000cbf9c06236375eadfb030000123c334304e04d00000000000da489ea0001e2e000000053e25ee171000000033a031c9574a7aa55437b8000730216800000004aca1c49db0dc8000079e9349a88000067ae149e3a00001a8b1f80005e79ed4a720000895b742809a13c000306a0550e2c093a7b0875000012cabaa35e20dedd195047991eda907963a0000000000000000000000000a40000000030f1dac0000ed8a5c0000000286600000009a98e1e00000000000a089820000000129000000006c3300603c1cf02b7068a7cd000000016a000000000002fd40000000b2c800000000000001ea847e9a2000020bebd2000078f857800000007a50000366279a0000000c8e80000002f2c173aeda58613ca522aea0dce80009818000000000060e805eb82a5380110c5acbb214a12201ce7dd0000000000000000000000000000000000014d600020623e292de0000f446dc99500580000a66927c2692620addb6ee000285e5f7025cd1e000014ea4687701d36c9e908c908265c9371cce000000000017546ca936a6b60000000000014d800000022c00bf881cd18aa00a042e94c14a43c48d9156c6b37a643f80347c7a3e2c4b00000000000000000086fa07a5de80006769bf400032f64db235e58f2fd8ae68000000081200000003d78000d0f189e44705443a6185e08329f4000276493b3194577a914b86a6ee6bcab7c4d12aa288e117a0000000692268e89813785ee8fea5df800000000be2fe800033703f88b68d867718b544c698520ca20d205b8000704b210c43896400004a610100004f1b1f4000242ebc083ae5c700002dda84018782f000009e8a2200006d8ae22b0cabb8660000000000006db8000000126a9c137d809b0810bbd8ef20068f6a0000000000000000019963978000830827e5c8af847d30f704eda35217004b0101800000006b0c05000000000008c700000001a42dfda6c679b8736c3b800000013240001120c5f00003c20396c4a130a0002c5e00000000000eb6000184e000000001a8000509a3f62dd31460000000c0800003d98000459800000029a4c8f0000b0c18fa950aea8db200000001aca8110000913090600000003188000b46979600000000000000db79a345b7a6e65aaa25416c0000b2b1c983050000c68800000001080b4807a0002ce20002d204f629300002d8a00020e001093be0001feab892cee7860a9c00014f4d901e0600000003259654000347
  | 56 => 0xe4000101e000086e000000005780006b5355a000000068f0000670ab4ca0d2dc29f1a4c81e5000000000002d98000000279600000a8020b31893681ee3ee2d3000027a2000000000000000029d900000000bda06640001df2d79800091c00000000000000000000027e672f0000ca5a33c0000e9a688a00694aaa6e1b782600001846000000000032e06aa81c4150a2040002346000000000000000000000819800000033ce72c0000756000028c00006b000007290e420000000c418000000000000000000000000069000056606bc08a9d6a00000000c680005a1279000000008ac9b267028798c04b2f4a50ab9000028a4933000000000003fd30483a1000000030840b1834e196a54eaf794ec88d1914789a70c00010d8dbead68cb500004b500006898000000032e2ff01844749434000344200000008e685384b300000000a840002ed27d6998200000009b390d2d6000000000000000000000000000300000000000000000007ae0000d542a461630000000266c5ac357400000009b30000000000043200000001d1a3b10000cec8a204feabfc0000a6cd8d00000002912080a52430d279400000002c08000b120000622800000009ae398293200000007e4a0acddd98d2000148e0000000c3f00000000000000000078c0efe13d290c0001250c9135a600000e61490000430b08aae08cf887f000000000005db862a00000009501e866d1982a0001f947e41c28dd8b7f21f40b84d1381b80001a86126932a56f000093f0000c6c80008dd000000001200000000db62bb60000000b9c2ec80000000aeba3ec0160000d7d1c1c49101c875089400000000000000000032d898015f2b611262304017e000249a000035e6d430e2cdd853021c972865200000000180983218c00000008d28000000000032a00000000000d6a9822b269a700002e64971000068b8000b2a80000000000000128c0002f0edd480000002c986d7ae820000000af4366c0001eb295800001f03506dc7a0aa901a7c400025720000000000000079898e471210a400000000000000074b15429e070c00018da0002018a1884328e8b7e200000000000c560000c0a11430d000000003178000885000000000000000000000000044f1bf821799060000a3e05b366eb4634baae523fa0000000b6629867108000487a3c80002624dad07ded5e0e96de507ee77f17fa90625cce1c000000000000000000000149283036741369e8285d25b60001d104f096c2b90aa90c83292883a00007528000cc01f780000000588000000000380001fba854934c52981ea00001bc000000092e078400000007a280000002c54152004e0002b68610000000000009ce336c3df8aacd273800aaea89430380007eba41c00027685f3000000013cc0361be6860afbc00002f64188be031ea08e05
  | 57 => 0x279200018700000ebe000000077b84fc7178c18000000000025d480200006df0000718810c00024086463392cf2000000000009140c1a0002e12a3500000000000000000000005e60001d8a0000000000226e91980000000cec00019740fba8cc00000007a731146d900000000000000000002400000000000000000000000000001f3eaae000000033d60001d620000000000191e0000000000007000000006580000b35800000020f425e8000000000000031eaa1f2232d77a2f05e9b84a000269c00000000000000c0a80005c2800000035441f2000000026faa35a092410a4f22992ba0000145c0000000788b52037d00002890f80000261c355000022d21a07e2018a0000fe2a6d2f6e7ef8000884919a0000000dc388c66e798a60001772ab49c2a969aaea0000000000000000000000000000195800066900003b8adf40001fec00000002c90000a57221e7598000000317e0f69a8a41500004288000000074000000000000000124b5c4383109200000000000000c29000000000005648000000000000022fe40d80002aa80009ee0b8e4268000b812d2cb62293c657134e00001245da80000c50000b8e8d3600026b414282123f380003090652c2cb368bf912c0bb600009498bde655000000000008cc97520000000053383eb4927f40ca8118000000000000000000000b9511be7d00f5836c025285421568ef062e3241e84da71788cbab676d1a84803a982826bb00000000bb6cfb80008a7a610a0f28604228c0cb57b07e000357092ea09cd118d9ab2087860000000000346c00003c61088000c5b0776aff80008ad84c4000000000036fc0000000c7d800000032a8382ac740d18000dba2cc24369644d10081e00003d40002c8a000000074b800000018667389018af3b6a4a0ba43abf303481c8b82a0001b7000000001908000000000000000002f501b640ab83600037c600004524ddad7cd8380000000000000274628b8000dc9091ed750000000068646b09c20002a407748000aa18000000202c0002782a5994b00000442d2f2f9e000000000009fe48680002a400000000000000000000002f2c758000727b1bc13202ce0002ec60002f6400000000002d90bb700000000000000000036f00000000210000083200000000000698000366a0000dfadea8000000000034bafa8967000000008a84e51ed8af8800019c841e93fa46a86a22ee77a945600024ce000344c1e6800060a04280000000d001e1e725190e00000000000000000039052614acc59800056780002099fa638f1424274254ca78ab66af537c499f8000920b68821128d022287f6b6aa502c7899e22698000dbf80000000000000000075b0c362c7acb6b390000c7b8000000288044ab80200017f28d80c78a50308870b19e00002cf69590000b9615
  | 58 => 0x706ca30000000000000000aaba2000000000005e4859829f80004ae80000003188692ac92d268e1c403114c0000000e1a000000023580001636d7890b6c96800000000001d906b2000000000000009dca42835a8000489869e00034be1f5000072a1bca0fc000000000002e6800000027ae3522664191ae36a78219c0003374000212000000004861af40000834c8a80008db3832609af580000882000000007e0f96867b50a47d2118328895409623383851b6889d999200000003f200002739d3cc608cfc6ba80006c9000000000000000000db402844a910f2ceb9fca000281e0368000000222a00000008f480000f7067c0000eb000000000000732a191fb6a9780000000cb60002bf088731041f88de6b4a824ad3e80006f1812c00008c287b2c6219bb0e00a605906c406fc262918e7840000a262b7800000004180720510b6105f50b60cab0000d4931446fc09f0599b384b51000079ab3560000af862a800000000006262e188802dc8575155ad200caa59d8234e22185862200000002592d0200000002e4e00005b449f991a0478f883320000157800000008e604da6400000000b3d000000022640002eb800000008a11f8a88b8000815800000022e634714dcb5e0ec852d997c00026ac09c890a0af8e94d7e1712ddf2518035acca326910c856b6025c3000084ca616b1902f8b44279e9fa2d4cc128e4c2cb21b20002f309362b1ed9a31620f12322c5096ba2290040828a0ba5c09e124ee94e6b6921e236b82b0cac80561ee9abc08594d84c600a09440da80faa9786bc01425f900000000000e090000b8fb3200000ad65d6926e0000af60000000000344a26c872600000000000de865c149c6ff12fc2f8800000000000000000000147a00010b2b3ea5c20daa2ccb161e4200000000000b0e6218000000319ca939a826de80005f280002381448135ae8e0000bae77790a000032b4000000060596ee0000000507ab54bf2996800000f2c5307b01fc8468ce9b0c29398f5400000000000f2685b00000001776000133402100000000000c81800019411fc29898ee0000000c7700001733468ccf00000001b74cf5098c6d50000de1800000034d205d87f46a698c02cc8000db8800005cb2be55c22d2000062c494800028a9d88bf4800000033c290900004a80796a23a4ca6f48000000000000000000000000d7095a00002f1e00000000000fd00000000000000069f2c2cbb40000b198d90000192aa02800056b9520c159fa2000285419d86886778df20002e720000000bac1d320000000000312ec8bac18b598d845d6361abdc800016782a238d86820002d4e00000000000000734800024e0000b3005f2000000067b25846a0280c12aa1ca9912f8eb4c800000000008638000a21977c0000000024800000000004b88000831aaa00
  | 59 => 0x96eb448e2127001a3a8ce095944a6003126cb38b18a30347e46e8d0c96f9c3858c0926c2c21440688f0e6288dc40669d7c2d21db0cb78d0212e0b6c9c18338a83a78c41a07b29cd1c34c1b23be603a2709288522b011094bd3ae164d711e40000000ad585d66c50000a779b008b800006350402000000045d0000b6e00008c506e216f000000012462440fa2c072cdcbf21d540778000e0e800000000003b800000002ef40000fde9cb847ac768bf03d8109600000000000186000085400026920000000000000000026e8000113a246ab72b00a7d800005d80002a9eda1ae6689f184c3a2a3b4ab780300bb8e22b34088e6e93696001803c0000000458b71a000094400037482eb2ab6a5b16feb0e32bc0000000816000015ea05083c0e340001f3200025f80d5b70a000014430ea2dc0002822cfe05e2ccda4489f380008f6000000000dc0201fa027784480002ed40000000347afec768309e480166a40f8000e2180000000000000263c00023fc23780007a49c0200006a4dc21dbe88b1b96d6a16ae14fb88c4cf374eb55aca8deea3d0065072894589860003772000165caf980001b80000000000000038500000000000211200000007d4800000025f4000000000000000000000000000000000000001c1a00000000000000000000050ca47a83380000308faaa5f1c44000000034826a85f800000000000000000000035f204b8000000000000000006790000ad7000000005fe0000000000386cc5b80007da8a0c0000460c1c224c68a8000000351a8071f140000ece7582422000056e00000005ef800085882a6797b53e3bb939600019648f300000638000000000000019420000c9cc5400004ea00000da34a822780000cf89da0000c0600006f40001b34000000000000000000000000091c7f41fc2314acf20000000674000000017702372ddc0000e6a00000001559f164bbb1d000000000000000000000099b822434032f8c970000000319200016900002abe2b0b81e000333ae08b168000019ece3800047a0860ded800013181220001b940000000000000000029b0000335c2d316a4000000062b0000000000088f1e961d5020e23e0708cc40000000161c0001f22acb8f9c123229c4f8076800000000001f72309880e3a324328bf255cd1d9eb0c82a7faae6000095c00002f99ab80001d0e0000382c7a000025f800034eaebe49c90762b7ad487d8a70818dac0eb8e25ca27b1738000005ad3226940002a5aa3a00004752bec00000000000000000273c00026127f11eccd0980001c4234264c8850000381c8f5000000000001ef800060695ac62504ce000000000028c472d00000001d087659d5a96380009188e7a0000000000000000010ec0001f10000000000031909a1176c231219400000000000000000132e835ac72cd29
  | 60 => 0x96780000000000000000078000000002f0815fa45800000006e980000002b0ca1fa3b00f4019c5e1364e0001550c718000000280eb3b0ae67cf00008260000000165655792c6a9e0aeeb3c1a32000000000000007310dc642a997e916a34ca4706c400014fa55fa2f400030620000000482000080099040000000000183400000000000000e0f308e06300006510000a0aa5fcd990eb200019206ef0000000000000027d6c4400004bd000000000000000cde000000000000008368000000000053400007e1a7580001808000000029200000000000c041b4e60b8000000000000000000001eec2f483e22481b066a79f028ab375487b8000862b6b85ed8a9266615c411f8088538068c3222c107c800000c594e815ab54e42f841a81826d6ca393e653137b40002f2e5bd00001d0a6740001b4c85f1cc662e800000031ae000000000000000000000000000000000000001fc8000000000000000002a2e00032920001c9c0000000a8c1eea335228c96a2a3a00007e8000000000000005391b304af20f800000000002bc0cc99b900002c9c584303c4c08f4e3c7a9385878670a0e1ad6d15309690d08d287480000000b7c1d4b5280001d407cbabdc12400f6000000035d00002a830b444b802ebc6882889a94da76b8426da79a0a457b5960003136da999904ad21e600025d0db92f708ae80006adb2cc0bd3682000238cb5900004c7b768c692442b2fa900c85166e4b0800000000004d600000000b1c000000000014cadde2c1e11d800080317e800003e893e32261f380000001b8a6d620c8d8da7fe460800000022680001d14000184878d247c2deadf072c8cb8bfe8a7c0129662000178c0000000c8480000000000c91b4a6cb9b82ee1d00002e59270000124ea71800058e1c180b2b3483399aee2260b585fc12fa6bfabb00000b5c0000f5caad12e80ffb302000000000000000000000a14942c88920fecde07a0a5b9332457000000018ca000000000000a2afab3520002e6e004026458c800078d8000ddc0000956800000027c00002102000000000033e20002dae00001ec2e6045c2410ab66e39d380000000d4da1bc000000000028b40001a723e089d6d6f23909d52eee00010c66fd91720001ed0dabb33400015a40000000000000000000006cf31fa2580000be00dd85080f2ca3784e600000002a29348000000000000000000e0400000000000000000000000030d2c6ea4041e4242600011a80001ae0931095621a0a3c000162c00000005b886602af2fc498b866245097c0722800000029d40000e4a00033d0cae2650054aac43c027660b937960000000d2d9f9e0003810000000019f800056c9878a5d800000000003a79512e02000094e80000000000a54b54a00019caa172adc000000046700000002b9e
  | 61 => 0xba7100a000277e000000000009cc0ed291e00021e4000000000000000002d7e0002ff80002d2600028e400000000000000000283a0000000cfc040c0000000956103ad3338343742bf400000004b680000002180000000000033aa00001f00000b62c808f680000000a86800086a80008730000000000000000004aa2f823ae354200036166ba10582283766383a12e6869ce0e038000136000033fb2c636200000000000d7000000000a6a9c69c7e9f5305e00000d434e00007f5b3be0000000000000000033388a18c460000000c478000000000000008ba4da00006ea8000000000000000006e691aa000354000011f8599020a59c9cda00010201c7800000018900000eca000152e38823e8b298b2a94385ae02d0c3000028eebab02cc702121c0000000aa9800000013ec68900000000000c0b01687669a56000044a79f9b9cb8800001ce00000000000000362a577000083980000001b600000000a002ae000033f249d2f3c7a60350a139b8c12e99f600000005021d8000009802570600cef00000002bda0002abc0003706576904a4f1000079180005b28000915a2c8000101c00016ce3bc0000a278000000095e0003538ba4000000036a20000000a15afe263d800000020a463105ea6c10c4e9fc1ede44d37c88910000d048000000000000004be00029a0b5d248000017c239109980a826b240c2e081d10eead4087cc08ca7ee000299ca1229f879c3082b8523263e3943ccfea698c8d000000035b6a42326800000002a20000942a3da1f7000090a80000001c465a532dc2fe34ac591b70c78a166890c15560000000bd483184f3b74a305b3e60000000000000000002e079a096891380000c700000000000abc9f4a19780742840000a1b0000e058000516169600005e03358000a940000000000057a8e280000000d3a8000000000058b81b0b31a3707d7b6d4d9480008e1000000000005c934b2be4a7be798190269180005ea0000000000000000000000000000354c027000000000009b71f9c00004bc0340000a130000dcaa09e8940000000000000015360000000b2800004380b16ca69c2e00029ec26a02dabfa80000000000aa680000000000000000073b000000000000001fe40000000000167a8f0821a00000000000000310853400000004f494782a18000d998a4e0001098000000000000000001cfc145004800006a2000317819300000001d2039c80007be1e88ba194c04f232c80000000000000084c32044cf973c00003767c9923e2688d144d800003590000d0b06ee3581f0ec5913840002fa07feb420000000000000005e89ef000033c4a7e96d2000000000000003442b9c20c0000a6b000064fab6a20580bc5f182de36525825612474214956cc248f6c00004f2b71000000000000e480e200000000000000000
  | 62 => 0x2c600000000000000062d80000390000000179800026fe022ad220000000799a41a0000000cee13360000000c2f0000000000065337da21a991600000000000000000000024d000084e9446e108000000158a00000000000000000000000007f0df823a0cfa800000000000a40000e1e861c0000000dcd3780dbca662000150ed461de2d879398000070440123360002a8400000002cf8000000000081317184818b7257e253e00000000000000c4c9132aa3000052e9c78c888000e1b8000000310279403b0000000019e27400000000000340e2b30000e0c000000004167ad0000296171e192b30a0000b4434224aab059cc200037d000000000000000000185451b0000000268aa0900005d100004728f04bc02c3aaa0000000c80000001a44a020000acaa14000000000ac92d25fb35feddd2b8e6cdb6f4c9800008fc956ea128dde3ce146210c173a3d0aafec280ce4659b2561bdadfe44500768e7906641cafb4a52aa200001b2e00000000000000566800000026a4000000000000000000c6422b036cd5c8344d22329c1471d1800029eea7f9832b0a9ee48ba117e973b3b63bea4a01d60cb460b010ab7880009bf000ebbf91e2000000000002fa0001bdc0000000d312bc8000353c00000000002626bab9c405fd8bb8e0a3364bd180000001146a4980003252e4a0000000c33a014769afda000000044400000002aa4000000000000000003848cd6800000000000000e7c14492b009b8c7400000000001600dfe81c00001ae2dd417a05e70000000351e0b71f3aa9b37920001dba1f6360684999340000000927816a45a8000c198a601688000d438000000000000000000000000000000000010f859fb8780000b120000000cf70000abb269e0000000dd30b8abce843a38224a89cda1d800000005f680003e996b6000000000000000000000000000058f80009bb000000000007958000215800000000002e2000000000000000000000000082f000000000000000000000118ca5428720000000cf803b607d8000a5f80000000e244a20000000142a0000000c6a29ca0000000000216a00015547a980000000000c7980000001b5204a17b090daf7ed3920b099612d067723200199a60c7791d6a2b008c0001df0ab39be436a8fec00032640001c700000000ab300000c907824fd24b6df083a470380004700cd200025e200000000002dd41219050000286a34d2da2b8300980000db800000002bf00002e480004c70000000203a00017507ca2db6a7d800048090225de21ac00000000000cac1270000000130409010f031f87162bc9400d1baf50405b654a9233822f2aad400000008e504ccdd916c4dac24ac104030a00008da843800000000006c694bc000000000000005d90ce80002588000000000011c6699a29a0000000000000
  | 63 => 0x8aa279c000245cd64976049a36ce00000000001526504800000000000002a6a3b5800047d8000469800000012d80001dd00000000472000000010889050000bee8eb4000000000028c8000170e000000093580000000000562172c70c941c0002b149d723c400005c29b0b6b2000286e767acb03412dd0ae3000095a000021180000d90cd8b76800000000004a500006fa21de00000000001d700000000a2c8000000278e0000fb4000069c0df00005cf800000000000001e320000000ab8a6720000000b6000000872090cf30000000224a000000096f0f02dcb00007b2843691b048eba9ab3edc1000000000006c880000001eee0000632000000025619b60001b66d328d50af48000b67222200019e664b0000c8cb4028a8854e6ee00000001326254062631da7f65bc93f8000000000000007ee2e280000000d3d000041c000000025f261580005e534c200000000003486d2a95e2000152415f113ed2d158c05700007f7a826c98aa82c9000000000c920000750e1890fc639a4447aaa5a2810ae1ec0f9c769448bcebdd8a46d060680c6d277400fa07800000000002266000050200028686e1965ac7495c0b450000000000000000006ad2f0400017a400015d62af972a737a55069e9eced8c8000000000000000000002e967c300000000000181000048900008612bf200009aa00000000000dce00023e0000000085eb87200018cc59b000000009bc4929b12c802c3eb56aee0b1e2a3cb3fb2420002a18bfa352e467ac34a439a0c80a902cc9e234876385e8ca9a11abada2060f832988e08ffc29b800010b800000029d60000322240ab606a50000bf09cf40001f083af01d8b9ab68c23b8000000038e57c2de67240000a8a00000000000921af1600014300001a06c1e81e800b2c50bdb12144c380006500000000004c99e9bd610f80000000000b2107ec000000051f00000000000000373e3212a4407f0b0c43d00000000000000005000009f40002818a51000000000000000c080000000dc4800000033ac61c8baa256800091fabd8894af0a58a000079d06489002076b6faf286b7a980866a61474c1710000000000000000000000000000000000000002904405000054f0000b050000e179264c29ad706ea14188688000a3e80008488ecca2804240002b800002ab08a0a01a29c8f4a18a0000d8e90ca0002b1851a2a0aa01000067a80002fb15ccd111f8e8d9000000000006ae8000cd38748ba1288c00012f83b08000724800000000005651aa2ca000520c1000050525960000d30000000000008cc427168200000002f132e20001708836265a515184a00000000000000000000000000007332e44d1f05640001958000077841702940001ff0000000000020b6000153200023880001a1c1cf0da400013224c2339000
  | 64 => 0x2e7a8c1a67c52c8000a6e80000000f46b4e8a3467c8000000181c0000c2c0000000000000000010ce00000000000000728800032085e445489e4000052e7d09d48761800054598b2a8505727b22f9c0000000000230000000086db060800036c24b7200e000000000000002f700184978b5a4390000a8f800000000003a88000000082c00016860002f6a5bea41007097ac000000000017b400006da7da3050605173241b8ab848b8f8432026f460495fcd388000000102e0000af000000007d51080d05800000007747961f70c0a2e7e00000000000000af9000000020882cd0000c9c0000000000000018c20000000000247200000002e71474000141000028da0000000000184422a800097aa4c60001c7400007922f60aa6864b42e8b8a9a6d04140c00000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaad8290064484230f90abb6a8908028f61365951210043fc2aecaa242008ef825d954484011ef02bb2a8908461fa1f655512102c3e42aec2a242488ef825d854484010ff0aba6c6908161f21574d8d210054ec2061b1a4200acd820c363484015ab02186c6909231bd8a7598d210061fb2ce931a4200c3c659d2634840187ecaba4c6908030f1957498d210464e31ae931a4200c9d74d8e63484018de40bacc6908032b8867498d210065610ce931a4200caf209d2634840195e40ba4c6908063be1d2098d21486373aa4131a4200c6d75482634840195ce8904c6908032b5d12098d2100674b824131a420087e87d9563484010fd0e32ac690a471ddc46558d2100637906eab1a4200c6f75dc963484018d8ebb92c6908023b6037258d210063a3aee2b1a42018ec82dc163484010ff0ab82c6908161f2157058d210045fc22e0b1a42118bc845c163484011bf06b82c6908023be097058d210047bc0ae0b1a42008ee8748163484031d90e902c6908031bdd52058d21486363aa40b1a4200ceb7048163484011bf0eb18c6908223720d7018d2100566c146031a420887c855db53484014bb07b2ca6908021fe157654d2100477c12eca9a42008f7815d9534840b0f90a3b2a6908221fa1f6554d2122c3fc2aec29a420587c855d853484911df04bb0a6908021fe1576d0d2102c3e42aeda1a42088bc845db43484010fd0d3ae86908021f21975d0d210043fc3ecba1a420087d87d97434840b0ff0e32e86908021f61c65d0d210043fc2aed21a420587c855da43484111b906bb486908021fa1a7590d210043e432eb21a420087f87d9643484010fb0fb2c86908161fe1c6590d210043ec38cb21a420587e85dd943484010fb0bbb286908021fe157650d2102c3e42aeca1a42008ef825d943484011f700bb286908063e2017650d210445f43ec8a1a4208a9e83d9143484231bd0fb1a8690846a7a136350d210043fc2aec21a420587c855d843484011df04bb0869086b1b9c86510d210064f3b28621a4208c9c7650c4348401c3ecaa188690803871954310d2101c76432e421a4200c6c655c843484073c902b9086908171b19572d45210f636396caa8a4200c6f65dc951484918d8cbb92a29086b1b9c865d052121f32108cba0a4200c6c655cb41484350fd0dbaa829087a1fa1875505210043f43ecaa0a421e87c87d95414843d8d8e5b2a82908021fa1c655052102c3e438caa0a421ac6c7219541484018decbb9282908031b197725052100656326e4a0a421ac6e721973148487cc84232e62908031b19572cc5210d43f436ea98a421e87e861d531484010fd0fb2a629087a1f21f654c5210f636396ca98a420087e87195314840b0f90e32a629086b1b1c8654c52100c77436e498a4200c6f65dc931484018d8cbb9262908033318f724c521
  | 1 => 0xae639eca9087a9ba0a70d952100536c14e1b2a421ea6e821c3654848b4db04386ca909169da0470d95210f53ac08e1b2a421ea6e8290365484014db05206ca908021fa1c40d95210043ec3881b2a4200a5e8310365484014bb06206ca9087a9ba0840d952100536c1081b2a4245a768110365484014eb02206ca9087a9ba0a30d952100536c1461b2a420087e870c365484010fb0e186ca908028fa1030d95210051ec2061b2a421ea6e820c365484014db04186ca909169da0430d95210053ac0861b2a4293c6f8748365485298d90e906ca9087a9be0120d95210f735c0241b2a421e87e8784365484010fb0f086ca9087a9ba0a10d952100536c1421b2a4200e69208436548401cd240886ca909179c04110d952100476c06e4b2a420087f855c1654840117f08b82ca908462f21170595210046fc1ae0b2a42088dc835c165484011df04b82ca908023ba1d205952100c7643a40b2a4200ceb7048165484010ff0eb28ca908021f61e60195214ad3ac0cc032a420087f87580654840147f08b00ca908028f21160195210052fc1ac032a4200a5c8358065484874d90c900ca9087b1b9d9201952100735b024032a421aa6e8290065484014db05200ca908161fa1c40195210043ec388032a4200a5e8310065484014bb06200ca9086a9ba08401952100536c108032a4243a768110065484014eb02200ca9086a9ba0a301952100536c146032a420587e870c065484010fb0e180ca908028fa1030195210051ec206032a421aa6e820c065484014db04180ca9090e9da0430195210053ac086032a4294c6f8748065485278d90e900ca9090e9ba05201952121d3640a4032a421aa6f804806548435cd700900ca908161fa1e10195210043ec3c2032a421aa6e8284065484014db05080ca908039a482101952100537c122032a421aa6c824406548487cc842880ca908039a48110195210043fc2ae7b22420587c855cf644840153b06206c890802ab60840d91210055ac0881b224248c6f629d664484018becb39cc8908031719673991210062fb2ae73224200c5c655ce644840193ec8b9cc89084727191739912100637902eb3224200cce219ce64484019984339cc89080333c82739912100667902e732242018ef8748264485218dcea904c8908031b5d520991210066739a413224200ccd7348264484019d2e0904c8908021fa1f65591210043f438cab224292c777119564484018de41baac8908031bdd77259121006363aee4b2242008ed80dc964484018e8ebb8ac8908021fe15705912102c3e42ae0b2242008bf845c164484011bf06b82c8908223720d705912100477c12e0b2242008f7815c164484011dd0e902c8908063b21d205912100637baa40b224290c6c7548164484019d6e0902c8908022fe1d641912108c5e422e03224200
  | 2 => 0x5725943100537414e0b286200a6d829c1650c4074ed03382ca188029d60670594310052fc1ae0b286208a5c835c1650c4014dd04382ca188029b60870594310053741480b286200a6d82901650c4014bf06a02ca188229720d40594310043f43880b28620087d87101650c4114bd06202ca188029760c40594310053741080b286200a6d82101650c4074ed02202ca188029d60440594310053741460b286200a6d828c1650c52f4db05102ca188021fe1d20594310043e43a40b286200c6f87481650c4018d90e902ca188039ae0120594314bf3508240b286297e6910481650c52d4dd04102ca188161fa1772590310043ec2ee4b2062088dc835c1640c4031790ea02c818822a720d405903101c3fc3acb2a06200a3f84596540c4018bacab9ca8188023be09765503101476412ecaa062038f4815d9540c4070f90eb2aa8188031d597715503102c3fc3ccba18620087d87997430c4010ff0eb2e86188021f61d65d0c310470e21ccaa186208e1c43595430c4010ff0ab82c4188161f21570588310045fc22e0b1062118bc845c1620c4071e902b82c4188063b21d20588310456641a40b106200ceb70481620c4070fb0abb6a41880e1f217765483101c7a40aeca90620387c87595520c4018eacbb8aa4188021f61a75d08310043fc32eba10620587f87997420c4010fb0f32e84188021fe1d65d08310043ec3acba1062038bc87591420c4018ef0bbb262188031d217764c4310466b29eec9886200ce720dd9310c4019ca41bb262188031dddb754c4310063bbb0ea9886200cd77654d310c4019ceedb92621880339dd8724c431006b23a8e49886244a6c85dc965884070fd0f282cb108029b60a505962101d3b40ca0b2c4200c7b7094165884014db04282cb109229b215205962102c77c32e5aa442118ef865ca54884070f90eb2aa9108031b597725522102c77c32e5a9c42088ef865ca53884070f90eb2aa7108031b5977254e2108c77c32e5a1c42088ef865ca43884011f700bb287108063e2017650e21244b742ee4a1c421ea6f8759752884878df0eb2ea51091279e1971d4a212de73c32e3a944200c6d769d74288401acce33ae85108fb1b98675d0a211f6b330ceba144200c6f609d742884018dac13ae85108fa5be1d75d0a2100636bb2eba1442418ef875934288401acaeab8e85108031b5da75cca21006b338ceb9944236c6e619d7328846daccc33ae65108031bd8275cca2100636b04eb994423696f875d732884018daecbae65109225ba1474cca211fc77c3ac79944200d65755c732884014db05286ca908061fe1d50d952100536c10a1b2a4200a3f84583654840147908b06ca9080297e0d60d95210052e41ac1b2a4245a6c8648365484358dcec906ca908039ad8120d95210073430241b2a4200c3d741d365484018b
  | 3 => 0x83126200a6c85590624c4015d700b20c498802ba201641893100637b2ae03126200c6c655c0624c4019d2e1b00c4988023b61e60189310053742cc03126200a6d85980624c4011df0eb00c4988029be1560189310053642ac03126200aaf84580624c40155908b00c498802b3e0d601893100573c0ac031262028ee87180624c4011db0e300c4988033a5c0601893100573436203126200e6465c40624c4015c90c880c498803991951018931006f0b82203126200c6e529db524c4050f90abb6a49880a9b20b65d493100536c2ec5a92620287e87d95524c4010ff0abb684988161f21576d09310043f434eba12623ec6c629d7424c4010f90cbae84988ef1b18975d09310043fc3ecba12620087d87d97424c40b0ff0e32e84988021f61c65d0931006373aec5a126200c6d75d8b424c40b0fd0bbb284988021f61776509312863a388caa126240ce471d89424c4111ed0db8a84988031d197715093100673b16e2a126236c6c629d7324c4678d8c4bae64988021fe1f65cc9310043ec3ecb992620587f87197324c4010fb0e32e64989431d1c4654c9312067238ec49926200c7465dc5324c4a38eca33b6a2988171719673d453128eab28ce7a8a6240e6651d8b514c4051d904bb2a2988031b1cb65545310062fb2ee6a8a6200c5f651cd514c4011dd0db92a2988031bd9772545312463632ee4a8a625b8ee87d89514c4018b8cb39e82988033318a73d05310062e32ae7a0a6211c9c645cf414c401998c4b9e82988021fe15765053102c3e42aeca0a62028ec825d9414c4011f700bb282988063e201765053101476410eca0a620087e86dd5414c4018d8c5baa82988021fa18755053100636310eaa0a620087e87d95414c4010f90fb2a82988031b1cb65505310043f438caa0a620587c87195414c4018d8e432a82988023ba1b725053100637b2ee4a0a6200c6c65dc9414c4011dd0fb1282988031bdd76250531006363aec4a0a6251c7676d97314c4a3caec7b2e62988171d9d865cc531206733b6c598a6202ce67618b314c401cc8ca31662988029ba0a409943100536c1481328620587e87102650c4010fb0e204ca1882297a0c40994310052ec18813286200a6e82102650c4014db04204ca1880e9da0440994310053ac08813286200a6e828c2650c4014db05184ca18a5e9b60a20994310043fc3a41328620587c87482650c4018df0e904ca18a431b21d209943100735c02413286297e6a10482650c52fcd220904ca18a5a9ba08209943100637b94a4b2862088dc835c1650c4070fd0f282ca188029ba0a505943100536c14a0b286203a7681941650c4030f90ea82ca188029ba08505943100536c10a0b286200c3f749d1650c4114bd073a2ca188029be09745943100536412e8b286203a74815d1650c4018dee5392ca1880e9d20
  | 4 => 0x44c51dc58c5aa4a89880a3ba0b765513100476c16ecaa262008ef825d9544c4051d904bb2a8988023de0576551310047dc02ecaa262018f8805d9544c4230fd0fb2aa8988023be09761513101476412ec2a26208a5c83d97534c4a34bd0da9ca698a139318b5394d3128dab40ea729a6251c7471d95534c4a30fd0d3ae86988031b18a75d0d312843e432eba1a6200c6c625d7434c4a30ff0fb2e86988021f61f65d0d3102c3fc38cba1a620087d87197434c4018d8c53ac86988031b1897590d310043fc3ecb21a620087d87d96434c40b0ff0e32c86988021f61c6590d312863a388caa1a6208a9c83191434c4018e8cbb8a869880387d954310d310070e32a8621a6272e8c6250c434c40b0fd0bb86c4988021f61770d893100572c0c41b1262018ef87483624c4014df0a906c4988029b21520d893100674b8241b126200a6e85993624c4014db0b326c4988029be1564d89310053642ac9b126200aeb80593624c4015d100b26c4988031bd9770d89310063632ee1b126200c6f655c3624c4018d8cab86c4988033a5c360d89310053742cc1b126200a6d85983624c4014df0ab06c4988029b21560d893100557c22c1b126200aac84583624c4191db0e306c4988033a5c060d89310073232e21b126200e6465443624c401bc6e0886c498803b818110d893100636ba8ebb126200ae581dd3624c4014dd0a3a6c4988029b61474d893100717aa4a9b126200e4f5394f624c4014dd0ba1ec4988029b61743d89310053742c87b126200a6d8590f624c401d1a8621ec4988029ba1771d893100536c2ee3b126200aae84dc7624c40155b09b8ec4988029ba1770d893100536c2ee1b126200c6e85dc3624c4018db0bb86c4988033ae0170d893120573408e1b126200ae5811c3624c4011dd0f286c4988023b61e50d89312057340ca1b126200ae581943624c4011dd0e286c4988023b61c50d89310047743c81b1262008ed87903624c4011dd0e206c4988023b61c40d89310053742881b126200a6d85103624c40159d06206c498802b360c40d89312057340881b126200ae581103624c4811dd0f186c4988023b61e30d89310047743861b12620c8ed870c3624c4014dd0a186c4988029b61430d89310055742061b126200aad840c3624c4815cd02186c498802b960430d89310047743c21b1262008ed87843624c4014dd0b086c4988029b61610d893100675b8421b126200ceb70443624c4018d8c5baac4988031b18875589310043f43ecab12620087e87195624c4018dcedb28c4988031bdc3651893100476c3cca3126200a6e85994624c4011df0eb28c498802b9e05651893100537430ca3126200c6e76194624c4018dee0328c4988023b61e64189310053742cc83126200a6d85990624c4015cb03320c4988023be1d641893100537c2ac
  | 5 => 0x8803d848110195310052f4188432a6200a5d83108654c4014dd05200ca988029b60a40195312853b40c8032a6200a7581900654c40b0fd0e200ca988021f61c40195310052f4188032a6200a5d83100654c4014dd04200ca988029b60840195312853b4088032a6200a7581100654c4014dd05180ca988029b60a30195312853b40c6032a6200a75818c0654c40b0fd0e180ca988021f61c30195310051f4206032a6200a3d840c0654c4014dd04180ca988029b60830195312853b4086032a6200a75810c0654c5214db05100ca989429da0620195310053ac0c4032a620087f87480654c40b0f90e900ca988031be1d20195314863643a4032a6200e6b80480654c5354dd04100ca989429da0420195310053ac084032a6200e6720c40654c401cca41880ca988161fa1e10195310043ec3c2032a6200a6e82840654c4014db05080ca98a629d6061019531007349042032a6200a5f83440654c4014b906880ca988039a48110195310072bc1a2032a6200e5483440654c4a14ef00880ca989439ce011019531007339022032a6200e7220440654c401cca40880ca988039c4811019531007309022032a620087f855cb644c40b0f90ab96c898802a760c40d91310055ac0881b226200ee120443644c4018dce5b2cc8988031b9c8659913100637b2ae53226200c6c655ca644c4011df00b94c89880a3be1f209913100476c3e41322629ac6e75c82644c4018daeb904c8988023be1d209913100476c3a413226290c6e75482644c4018daea904c8988021fa1f655913100636396cab226200c7870d95644c4010fd0e32ac8988031b1c865591310063c380cab226200c6f65dc9644c4018d8cbb92c8988031ed9770591310063c32ee0b226200c6f75dc9644c4018d8ebb92c8988023b603725913100637ba8e4b226200c6c751c9644c4018e8ebb8ac8988031edd770591310063c3aee0b226200ceb72dc1644c4019d0e5b82c8988033ae0b705913100674416e0b22620087f855c1644c40b0f90ab82c8988022fe1170591310046fc1ae0b2262008ef825c1644c4051d904b82c8988031edd470591310063c3a8e0b226200cbb741c1644c4019b6e6382c8988033adc8705913100674390e0b2262008ee87c81644c4051d90f902c8988031bdd720591314d6363ae40b226200ceb70c81644c4039d0e1902c8988023ba1d20591310047643a40b226200c6f75481644c5218d8ea902c8988033adc1205913100e7438240b226299c7475c41644c4039e0e1882c8988063d21d10591314c63a3aa20b226201cf070441644c401dc240882c8988022fe1d64191310055c402c832262118bc845c0644c4230f90abb6a8988023be0976d513101476412edaa26205c5c659cf544c4071b90cb9ea8988023be09769513101476412ed2a26200a3d84d965
  | 6 => 0x537c2ac5a96623ec6e629d742cc4018dceab1685988463de1971d0b3128c3fc3acba8e6200c6c7259551cc401878eb32283988032b1ca64507310061e3aac8a0e6208c9c7359141cc401958e4b2283988021fe15705923102c3e42ae0b246200c6f75c81648c5358d8eb902c9188031bdd52059231486363aa40b246298c7475441648c401dc240882c91894e1fe1d65d523102d1e42ac92a462118df865ce548c42393cc8b9ca9189521fe15765523101c3e43acaaa462038bc87591548c40b0f90abb0a9189421fe1d65d4e3108e1f322eba1c6200c3d75593438c40b0fd0fbaac5188031bc837558a310043fc2ae0b14620587c855c1628c4031d90e902c5188031bdd52058a31486363aa40b146200ceb70481628c48b0ff0abb2a5188021fe157650a3102c3e42aeca1462038f4815d9428c4079c8e2b1265188031b5ca52d953100537414a1b2a6200a6d82943654c4030ff0ea86ca988029ba0850d953100536c10a1b2a6200a6e82983654c4014db05306ca988028fe1160d95310051e422c1b2a6200a6f82583654c4014d904b06ca988029ba0860d953100536c10c1b2a6200a6e86c83654c4014d90c906ca988039c18110d9531007b090221b2a6200c3d741d3654c4018dae4396ca988028fa1371d95310051ec26e3b2a6200a6e82dc7654c4014db05b8eca988029ba0a70d953100536c14e1b2a6200a6e821c3654c4014db04386ca989469da0470d95310053ac08e1b2a6200a6e82903654c4014db05206ca988021fa1c40d95310043ec3881b2a6200a5e83103654c4014bb06206ca988029ba0840d953100536c1081b2a6251a7681103654c4014eb02206ca988029ba0a30d953100536c1461b2a620087e870c3654c4010fb0e186ca988028fa1030d95310051ec2061b2a6200a6e820c3654c4014db04186ca989469da0430d95310053ac0861b2a620087f87483654c4010f90e906ca988031be1d20d95310063643a41b2a6200e6b80483654c4010fd0f086ca988021f61e10d95310053741421b2a6200a6d82843654c401cd241086ca988039a48110d953100637396cb32a6200c6f655ca654c40b8d8cab94ca988031bdd7725953100476c06e4b2a6200c6f751c9654c4019c8e5b8aca988021fe1570595310045fc22e0b2a62118bc845c1654c4011bf06b82ca988023be09705953101476412e0b2a62008ee87c81654c4051d90f902ca988023ba1d20595310047643a40b2a620087f87594654c4014df04b28ca988029b20965195310043ec3cc032a6200a6e82980654c4014db05300ca988021fe1d60195310051fc22c032a6200a3c84580654c4014df04b00ca988029b209601953100537410c032a6200a6d82180654c4014dd0d900ca988031b9db2019531005364324032a6200c6e76480654c401ce6c0880ca9
  | 7 => 0x6e8214165104014db04282ca208468fa1273594410062fb9ce6b288200a6f825cd65104014d904b9aca2080e9d205735944100637b94e4b288203a74815c965104014dd05382ca208029b60a705944101d3b40ce0b288200a75819c1651040147f08b82ca208468f211705944100537410e0b288200a6d821c165104014dd05202ca208029b60a40594410053741460b288200a6d828c1651040147f08982ca208468f21130594410043f43860b28820087d870c1651042347d08182ca208028f61030594410053741060b288200a6d820c165104074ed02182ca208029d60430594414bd36c1440b28820087f8748165104010f90e902ca208031be1d20594410063643a40b288200e6b80481651052fcd420902ca20a5f9a44120594414b53741040b28820587e85dc963104010fb0bb92c6208063721d3058c4108d4e42260b188200a5f83596531040187acaba4a6208023be097654c4101476412eca988200c7565dc5531040b0ff0f32c86208021f61e6590c410043fc3acb218820087d875964310423c388732a86208478710d6550c410043fc2ae0b10820587c855c162104011bf06b82c4208223720d705884101c7a40ae0b1082018ec87481621042355908902c4208033adc1205884101c3ec2aeda90820387c85dd952104071e902bb2a42080e1f21d65548410063ab2ee2a90820087d869d732104010ff0cbae64208161fe1e65cc8410043ec3ccb990820087f8759732104010fb0eb2e642080e3721d634c8410063bc2eeca088200c7485dd9411042396ca9bb2822080339c83765044100672906eca088200c7776dd541104018eeec3aa82208032ddd9545044100673bb6e4a088200ce7761c94110401ac8ea39282208230fd4e74d97310461ea9ce9b2e6200c3e519d365cc401878a33a6cb988023be0172d973101477c3e41b2e62008ed87c8365cc40195ce9906cb988032b5d320d973100477c3a41b2e62008ed8748365cc40195ce8906cb988032b5d120d973100637b94a4b2e620187c8754165cc4011df00b96c99880a3be1f20d933100476c3e41b26629ac6e75c8364cc4018daeb906c9988023be1d20d933100476c3a41b266290c6e7548364cc4018daea906c9988222f211759933108e1e422eb326629ac6e75c8264cc4018daeb904c998a431b9d5209933100636baa41326620587e85dc964cc4010fb0bb92c9988062f21d405933100675b8240b266201ce87048164cc4230f90abb6a9988468fa1365d53311f537416cbaa66200a3d8599354cc41117f0eb26a9988028fe1564d53310464f39ac9aa6620887f8759654cc40147f08b2ca9988461fa1f655533108d1f426caaa6623ba6e82d9554cc4010ff0eb28a9988021fe157058b3102c3e42ae0b1662018ec8748162cc4014d90a902c5988033adc12058b310
  | 8 => 0x2206c4a0802b960440d89410047743c61b1282008ed878c362504011dd0e186c4a08023b61c30d89410053742861b128200a6d850c3625040155d08186c4a0802ab61030d89412157340861b128200ae5810c362504011dd0f086c4a08023b61e10d89410053742c21b128200a6d8584362504019d6e1086c4a08033adc110d894100636316eab128200c6c621d562504010fd0fb2ac4a08021fa1c6558941006373b6ca3128200c6f70d9462504011db0f328c4a08029ba16651894100477c3aca3128200ae78159462504014dd0c328c4a08031b9d8651894100637b80ca31282008ed8798c62504014dd0b318c4a08029b616631894100572c0cc631282008ef8758c62504014df0ab18c4a08029b215631894100575c02c63128200ae88058c62504018decab80c4a08031b195701894100674b86c031282008ed8798062504014dd0b300c4a08029b616601894100477c3ac03128200a6f8558062504014d90ab00c4a0802abe11601894100567c1ac03128200acc8358062504015cf02b00c4a080a3ba1c601894100476c38c03128200ce97018062504015cd0d880c4a080399197101894100572432203128200e64654406250401bc2e0880c4a08031b94a76d49410143e42aeda928202a6c82d9752504014db0bb16a4a080a1fa1f65549411f636314eba12823bc6c625d742504010ff0fb2e84a08021f61f65d094102c3fc38cba12820087d8719742504a78e8e232a84a090b391c762509410063a32ee2a12820087f855db325040b0f90abb664a08021fa1a75cc9411b636314eb992820087c865d732504678d8c4bae64a08021fe1f65cc9410043ec3ecb992820587f8719732504010fb0e32e64a08031b9d762cc94100636baec5992820587e85dd932504010fb0bbb264a094f1d1c4654c9412167238ec49928200c7465dc532504019cec5b8a64a09531d94676d454102e1e32ce9a8a8254d36519d35150485ccca3b16a2a080a3b209765454100636396caa8a8200c3f65dd1515040187eca3a2a2a08023ba1b725454100637b2ee4a8a8248c6c65dc951504b71dd0fb12a2a09531d9db65d05412a71bb26cba0a8205c767619741504859ccedb1682a080b399d862d054100732328c5a0a8200a6e8290265104014db05204ca208029ba0a309944100536c1461328820587e870c265104010fb0e184ca208468fa1030994410051ec20613288200a6e820c265104014db04184ca2080e9da0430994410053ac08613288297a6d8288265104010ff0e904ca208161f21d209944100637c3a413288290c6c874826510401cd700904ca20a5f9a84120994414bf34882413288296a6e8208265104018dee5292ca208462f211705944101c3f43ca0b288200a6e8294165104014db05282ca2080e9da06505944100c3e43aa0b288200a
  | 9 => 0x10195410043ec3c2032a8200a6e8284065504014db05080caa0a629d6061019541007349042032a8200a3f84440655040147908880caa08039a48110195410071bc222032a8200e348444065504a74ef00880caa094f9ce011019541007339022032a8200e72204406550401cca40880caa08039c4811019541007309022032a8211a3c84d9754504a947d0daa4a8a0a3b8b18b54951412a59b40ea92a28254c7471d9554504010ff0ab96c6a08161f21572d8d410054ec2061b1a8200ad5810c36350401dc240886c6a08031b9cb6598d4100637390cb31a8200c6f655ca63504018d8cab94c6a08021fa1f6558d4100636396cab1a8200c7870d9563504010fd0e32ac6a08031b1c86558d410063c380cab1a8200c6f65dc963504018d8cbb92c6a08031ed977058d410063c32ee0b1a82008df8758c63504015b100b18c6a08221f21576d4d4100477c12eda9a82028ec825db535040b878cb3a6a6a08023be097694d4101476412ed29a8200a5d83d965350509c98c5a9ca6a080a3ba0b7654d4100476c16eca9a82008ef825d853504051d904bb0a6a08031b18a75d0d4100636312eba1a820087f87d9743504010fb0fb2e86a08161fe1c65d0d410043ec38cba1a825487e869d643504018d8c53ac86a094e1f2197590d4100636312eb21a820087d87d9643504010fb0e32c86a094f1d1c46550d410063a32ee2a1a8200e1f6550c4350401c38caa1886a09cba31894310d4102c3f42ee1b12820087d85dc362504015cb03106c4a08063be1d20d894100537c2a41b128200a6c8548362504019d2e0906c4a08029ba1663d894100536c2cc7b128200a6f8558f62504014d90ab1ec4a0802bae0163d894100574402c7b128200c6f65dc362504018d8cbb86c4a08031bd9570d89410063632ae1b128200ce970d8362504014dd0b306c4a08029b61660d894100537c2ac1b128200a6c85583625040159f06b06c4a0802b320d60d89410ac76c38c1b128200ce9701836250401cc8cb886c4a08039919510d8941006f1b8221b128200ee06044362504018daea3aec4a08038bd5254d894100572c0ee7b128200a6e851cf62504014db0a39ec4a080393d4e53d89410053742e87b128200a6d85d0f62504014dd0b21ec4a08029b61643d894100746a1887b128200a6e85dc762504014db0bb8ec4a0802b3a0f71d894100566c1ee3b128200a6e85dc362504014db0bb86c4a08031ba1770d894100636c2ee1b128200ceb805c362504855cd02386c4a0802b960470d89410047743ca1b1282008ed8794362504855cd03286c4a0802b960650d894100477438a1b1282008ed8714362504851dd0f206c4a08023b61e40d89410047743881b1282158ed8710362504014dd0a206c4a08029b61440d89410056741881b128200acd8310362504855cd
  | 10 => 0x994820587c855d932904071e902bb265208031b5ca52d954100537414a1b2a8200a6d8294365504030ff0ea86caa08029ba0850d954100536c10a1b2a8200a6e8298365504014db05306caa080297e0d60d95410052e41ac1b2a8200a6f8258365504014d904b06caa08029ba0860d954100536c10c1b2a8200a6e86c8365504014d90c906caa08039c18110d9541007b090221b2a8200c5d731cf65504018dae4396caa080297a0f71d95410052ec1ee3b2a8200a6e82dc765504014db05b8ecaa08029ba0a70d954100536c14e1b2a8200a6e821c365504014db04386caa09529da0470d95410053ac08e1b2a8200a6e8290365504014db05206caa08021fa1c40d95410043ec3881b2a8200a5e8310365504014bb06206caa08029ba0840d954100536c1081b2a8254a768110365504014eb02206caa08029ba0a30d954100536c1461b2a820087e870c365504010fb0e186caa08028fa1030d95410051ec2061b2a8200a6e820c365504014db04186caa09529da0430d95410053ac0861b2a820087f8748365504010f90e906caa08031be1d20d95410063643a41b2a8200e6b8048365504010fd0f086caa08021f61e10d95410053741421b2a8200a6d828436550401cd241086caa08039a48110d954100637396cb32a8200c6f655ca655040b8d8cab94caa08031bdd7725954100476c06e4b2a8200c6f751c965504019c8e5b8acaa08021fe1570595410045fc22e0b2a82008df835c165504111b906b82caa08023be09705954101476412e0b2a82008ee87c8165504051d90f902caa08023ba1d20595410047643a40b2a820087f8759465504014df04b28caa08029b20965195410043ec3cc032a8200a6e8298065504014db05300caa08021fe1d60195410052fc1ac032a8200a5c8358065504014df04b00caa08029b209601954100537410c032a8200a6d8218065504014dd0d900caa08031b9db2019541005364324032a8200c6e764806550401ce6c0880caa0803d848110195410051f4206432a8200a3d840c865504014dd05200caa08029b60a401954129d3b40c8032a8200a7581900655040b0fd0e200caa08021f61c40195410052f4188032a8200a5d8310065504014dd04200caa08029b608401954129d3b4088032a8200a758110065504014dd05180caa08029b60a301954129d3b40c6032a8200a75818c0655040b0fd0e180caa08021f61c30195410051f4206032a8200a3d840c065504014dd04180caa08029b608301954129d3b4086032a8200a75810c065505214db05100caa094e9da0620195410053ac0c4032a820087f87480655040b0f90e900caa08031be1d20195414863643a4032a8200e6b8048065505354dd04100caa094e9da0420195410053ac084032a8200e6720c406550401cca41880caa08161fa1e
  | 11 => 0x544015cb03300c4a88023be1d601895100537c2ac0312a200aaf84580625440155908b00c4a8802b3e0d60189510056641ac0312a2028ee8718062544011db0e300c4a88033a5c060189512267238ec4a92a21187c859db42544778d8c4bae84a89231b9d762d095100636baec5a12a20887c859db32544678d8c4bae64a89231b9d762cc95100636baec5992a2028ec821d9325440717908b9cc8288472710d73990510051f424a4b20a200c6f72949641440b0f90ab82c8288062f21d40590510077090220b20a200c6f205da54144018da40bb4a8289531dc4176950510063a882ed2a0a2038dc835d2631441193886ba4c62880297a0e5258c5100637b94a4b18a20587c855c163144031b90e982c628803b84811058c5100637902ed298a200c6d205da53144a38ee20bb4a6288031d4417694c5108c3ec2aeda18a205c5e7598f43144110fb0abb486288170f9d66490c5100477c12eca18a2028ec825d943144011f700bb286288063e2017650c510043ec36eaa18a20087d86dd443144352dd05ba88628802a7e194310c510054ec3286218a29487f855c1621440b0f90ab82c4288063b21d205885100675b8240b10a21187d855db421440b87ceab26842880e2f21d645085101e5a38ac8a10a20887d855db321440b8bceab1e642880e3721d634c85101e6a38ac6990a211c5f549cf65d04238baa939ecba08031794673d97410062e28ce7b2e82008ef805cb65d04051df0f906cba08023b61f20d97410066739e41b2e8200ccd73c8365d04011df0e906cba08023b61d20d97410066739a41b2e8200ccd7348365d04018dee5292cba08061f21d50597410446e41aeb31e8208c5c835d663d05358dceb904c7a08031b5d72098f41486373aa4131e8200c6d7548263d040b0fd0bb92c7a08021f6177258f4100c6e43a60b1e8200ceb7048163d04039d0e0902c7a08221f21576d4f410452f41ecba9e8236a6e82d9753d04014bb0b31ea7a080297e1563d4f4108e4f3a2c7a9e8200a5f8359653d04110fd0fb2aa7a082297a0f6554f4119d37416caa9e820087f8759453d04010ff0ab82c5a08161f2157058b4100c7643a40b168200a6c8548162d04019d6e0902c5a08029be1562d4b411b637314eb9968200c6e7558b32d04a90ff0eb2ea3a08031b1c9655474129c3fc3acbaa4820087f855c1639040b0f90ab82c7208031bdd72058e414d6363ae40b1c8200c6f7548163905218d8ea902c720a631d1d51058e410077090220b1c825087f87597539041193cc6ba4a720816972156394e410462f31aeb21c8200c5d7558e439040b0fd0fbaac5208031bc837558a410043fc2ae0b14820587c855c162904031d90e902c5208031bdd52058a41486363aa40b148200ceb70481629048b0ff0abb2a52080f391c56250a410043fc2aec
  | 12 => 0x8031bc8276d515100636904edaa2a200c6c625cf54544a10fd0db9aa8a88031b18b735515100732316e2aa2a200e64621c554544014bb0a186c6a8802a761030d8d510056ac0861b1aa208c9c635d2635440193ae9b1cc6a89123b21b7258d510046fc3ac631aa20087f8755063544018de413b6a6a88031b48276d4d5100636312e9a9aa25387e86dd153544018d8c5ba2a6a88021fa1c6454d5100732316e2a9aa200e64621c553544230f90b3b686a88023be0976d0d5101476412eda1aa200c6c625d7435440187aebb2686a88221f2167690d5100477c12ed21aa2028ec825da43544018d8c4bac86a8803175d76390d5101477416eca1aa2008ed82dd943544070f90cbaa86a88031b1897550d5101cba40aeaa1aa208a9e83d91435442353d09b1a86a88023be097610d5101476412ec21aa200c6c625d4435440193ceca1886a8823271d94310d51397463128621aa20587e85dc362544031df0e906c4a88029be1520d895100e7538241b12a200ce970483625440159d07326c4a8802b360e64d895100537436a9b12a244a6c8655362544778dcecaa6c4a8802aba1263d895100556c24c7b12a200a6e86d4f62544894d90ca9ec4a88cf1b9d953d895100674b86c1b12a200aaf84583625440155908b06c4a8802b3e0d60d89510056641ac1b12a21c8ed8718362544019d2e0306c4a89129b61474d895124717aa4a9b12a244a6d851cf6254491c9ea729ec4a89229ba1743d895100536c2e87b12a248a6e8590f62544014db0b21ec4a8803a350c43d89512267238ae3b12a248a6e85dc362544894db0bb86c4a88031ba1770d895100636c2ee1b12a200ceb709c362544019d700b86c4a89123ba1e50d895100476c3ca1b12a244ae68194362544015cb03286c4a88023ba1e40d895100476c3c81b12a2008ee8710362544011db0e206c4a89229ba1440d895100536c2881b12a200ace83103625440159b06206c4a8912b9a0440d895100572c0881b12a2008ee878c362544011db0f186c4a88023ba1c30d895100476c3861b12a248a6e850c362544014db0a186c4a8802aba1030d895100556c2061b12a244ae6810c362544015cb02186c4a89223ba1e10d895100476c3c21b12a248a6e8584362544014db0b086c4a88033adc210d895100675b8221b12a244ee01044362544011db0f320c4a8802b3a0e641895100566c1cc8312a2008ef8759062544015cf02b20c4a88fa9ba14641895100537436a8312a243a6e8655062544874d90caa0c4a88038bd91541895100476c3cc6312a200aae8498c625440155b09318c4a88023be1d631895100573c0ac6312a236a6e8518c62544014dd0da98c4a890e9ba19531895121d36432a6312a200e4f6354c625443d8decab80c4a88033a5c3601895100476c3cc0312a200a6d8598062
  | 13 => 0x636b2ee4aa6640587f8799743cc8010fb0f32e87990021fe1d65d0f320043ec3acba1e6408e1c4399543cc811c3886b2a87990033a5c1205873200c7a43a20b0e6400ee12044161cc8014db05286ca990029da0650d95320063cb84a1b2a6400a6d82143654c9378beebb9aca9900339c8371595320063bba8e2b2a6400ce7721c5654c8010ff0ab82ca990022fe11705953208c5e422e0b2a64008f7815c1654c8071e902b82ca990063b21d205953200673b8a40b2a6497ce471481654c8019d6e0902ca990021fe1d65195320053a40aca32a6400a9d83103644c80155b04206c8990031bc81759913200673902e332264018ef87482644c9218dcea904c8990031b5d520991324be7338a413226400ce571482644c8019d2e0904c8990021fe15705913202c3e42ae0b2264008bf845c1644c8011bf06b82c8990023de05705913201c7a40ae0b2264018ec87481644c8019d6e0902c8990073a1c120591320045fc3ac8322640087f855c4644c80b0f90ab88c8990462f211701913200556c1480322641187c855db544c8011ef02bb6a89900e3d20576d51320146e432e72a264088ec865ca544c8011df04bb2a8990023de05765513201c7a40aecaa264008fb805d9544c8031f100bb2a8990461fa1f655513200637b2ee4a9a6408d4c325d6434c8019d6e0906c2990029da1610d853200572c1421b0a6400ee120843614c8015cb04086c2990023de1d61185320053a42ac230a649ae2f54c8264d4521c5ea8904c9a8803b8481105935102e1fba6ecaa6a200a5f8355263d4535c9ea7904c7a8a4393d4d2098f510077090220b1ea205c5f73dd953d440187ee9322a7a880e1fa177650f5101cba40aeaa1ea20097585dc543d44070f90ab82c5a88063b21d2058b5102d3642a40b16a200ceb7048162d440b8dceab1685a88025d6177150b5102e373aac5996a20097585dc532d440147d08292c92880237e0d70592510446e41ae0b24a200a3e84d41649440147f0eb24a92894f0fe1d649525100717902c92a4a200e2d2059254944010fb0d39ca9289525de1971952510063bc32e32a4a200d67205c65494401aca40b8ca9288021fa1e5458e510052f418a8b1ca200a5e83149639440117f08b82c7288462f2117058e510052f41ea0b1ca20087d869d253944010ff0eb24a72880297e1d6394e512862fc3ac729ca200e4f2058e5394401c9a40b1ca7289465de197194e510063bc32e329ca200d67205c65394401aca40b8ca7288030f9d16414e51004bac0eeaa1ca21e96e82dd443944012eb03ba887288063b21d2058a5100537c2a40b14a200ceb70481629448b8deeab12a5288025d6077550a51004bac0eea994a200a3d85103645440153b06206c8a8802ad60440d91510064fb22e7322a211c9c645ce645440117f0eb20c8a8
  | 14 => 0xc4359543d08019d2e0902c3a10063d21d10587420077090220b0e8400a6d8294365508014ed03286caa10031e5c250d954200536c10a1b2a849cc3f75dd165508019ce41b8acaa10031ddd4715954200673b90e2b2a840087f855c165508011bf06b82caa10223720d70595420047bc0ae0b2a84038f4815c165508031d90e902caa100339dc520595424be7238a40b2a8400ceb7048165508010ff0eb28caa10029d205651954200637b2ee4aa28400a9d840c3635080159b04186c6a100237e1d6318d420043fc2ae231a840587c855c463508111b906b80c6a1002b360a3018d420443e42aeda9a84008f7815db53508071e902bb6a6a100a2f2197494d4208e96212eba1a8400ceb7048361508014ed0b086c2a1002b960a10d85420077090421b0a8400ae58204361508011ef0eb08c2a10029d215611854200c77c3a41b2e6400ce97048365cc8678daec904cb990039a58120997321b5374148132e6400a6d8290265cc80b0fd0e204cb990021f61c40997320452f4188132e6400a5d8310265cc86d4dd04204cb990029b60840997320053b4088132e6400a758110265cc86d4dd05184cb990029b60a30997324a637c3a4132e6493c6c8748265cc8014d902904cb990da9be0120997321b735c024132e6436a6c82c4265cc80b0fd0f084cb990021f61e10997321b5374142132e6400a6d8284265cc801cd241084cb990029be0910997321b5364122132e6400e692044265cc86d4dd04084cb990029b60810997320443f43ca0b2e6400a6d8294165cc8014ed03282cb990029d606505973200c3e43aa0b2e6400a6d8214165cc86d8deec902cb990039a981205973200734b0240b2e6400c3f749d165cc8114bd073a2cb990029be09745973200537c12e2b2e6433a6e829c165cc8014db05382cb990029da0670597320053ac0ce0b2e6433a6e821c165cc8014db04382cb990ce9ba0a405973200536c1480b2e640087e8710165cc8010fb0e202cb9902297a0c40597320052ec1880b2e6433a6e8210165cc8014db04202cb990029da0440597320053ac0880b2e6433a6e828c165cc8014db05182cb992531be1d205973249e3643a40b2e6433a6f8048165cc867cd700902cb990021fa1e10597320043ec3c20b2e6433a6e8284165cc8014db05082cb990039a48210597320073490220b2e6433a6e8204165cc8014db04082cb990031bc8175d933200673902e3b2664018ef8748364cc9218dcea906c9990031b5d520d93324be7338a41b266400ce57148364cc8019d2e0906c9990021fe15719933202c3e42ae332664018bc8750164cc8018de40ba8c9990063be1d2019332486373aa403266400c6d7548064cc8019d2e0900c9990221fe1d65953320051fc22cb2a66400c5d655ce54cc8110f90eb2aa9990cf1b1c9655533200
  | 15 => 0x902c42180347dd543584430068e3aa86b088672d8c7250d6110c01b1a87b92c2218031bdd77258443006363aee4b0886008ed80dc96110c018deea392c2218031b1d472584430043fc2ae0b08860587c855c16110c011df04b82c22180a3b20970584430047743e40b0886028ec87c816110c018deeb902c221a6b1b1d720584430047743a40b0886008ec874816110c018deea902c221a431b1d520584434ce3a3ae20b0886018f4874416110d318e8ea882c221803b848110584430047dc02eca1ea4018f8805d943d48012db0bb9287a91cbc39494310f52004b7c2ae421ea401cea7048161d48019d2e0902c3a927b0f5d7649915222e3bb28e2b22a4008bf8759064548778decbb92a8a9277175d76398d5222e3bb28e2b1aa4008df8758c63548678decbb92a6a900a1f21975d0d520143e432eb21aa40087d85dd943548011ef02bb086a900e3d2057610d5200675b8241b0aa4018f78744361548039e4e0886c2a9003b848110d85520047bc3ac230aa445a778558461548031df0e906cba10033a5c120d97421de36bb24132e8400e696048265d087d4dd05204cba10029b60a40997421f5374146132e8400a6d828c265d080b0fd0e184cba10021f61c309974208d1f4206132e8400a3d840c265d087d4dd04184cba10029b60830997420053b4086132e8400a75810c265d09298df0e904cba124f1b21d20997420053640a4132e843ea6f8048265d087dcd700904cba10fa9b20b109974202c3f43c2132e840087d8784265d087d4dd05084cba10029b60a1099742007349042132e8400a6f8244265d087d4d904884cba10039a48110997421f5374102132e8400a6d8204265d08230fd0f282cba10029b60a50597420053b40ca0b2e8400a758194165d08030f90ea82cba10029b60850597421f637bb240b2e8400e6a6048165d0801cd2c0902cba10468fa1273597420062fb9ce6b2e8400a6f825cd65d08014df04b8acba10ee9ba0a705974200536c14e0b2e8400a76819c165d08014eb03382cba10ee9ba08705974200536c10e0b2e843ba6e8290165d08014db05202cba10ee9ba0a305974200536c1460b2e840087e870c165d08010fb0e182cba10468fa1030597420051ec2060b2e843ba6e820c165d08014db04182cba10029da0430597420053ac0860b2e8494c6f8748165d09278d90e902cba10ee9be0120597421df35c0240b2e840087e8784165d08010fb0f082cba10ee9ba0a105974200536c1420b2e8400e692084165d0801cd240882cba10ee9ba08105974200536c1020b2e840087f855c663d080b0f90ab8cc7a10063721d3058f420052fc1acb29e8400c3d655d253d08778d8e4b2aa7a10031b5977254f4202c3fc3ccb21e840087d8799643d08010ff0eb2c87a10021f61d6590f4208f0e21ccaa1e8411e1
  | 16 => 0x15954300673b90e2b2a8600ce4721c56550c019d6e5b82caa18033a1cb705954300679b8ee0b2a8600cf071dc16550c019d705b82caa18033a20b705954300477c12e0b2a86028ec825c16550c011ef02b82caa180e3d205705954300675b90e0b2a8600ce8721c16550c019e6e2382caa18033c1c470595435063a38ea0b2a8601c7870d416550c030f90ea82caa1a7f1d1c5505954300e3c382a0b2a86008ee87c816550c051d90f902caa180339dc720595434b67238e40b2a8600ceb70c816550c039d0e1902caa18023ba1d20595430047643a40b2a8600ce7714816550d2f9c8e2902caa18033adc1205954300e7438240b2a860087f875946550c014e902b28caa18028fe1165951432a53a40acb2a28600c5f65dcd5450c010ff0eb28a8a194e9d20565151430052fc1acb29a8651a74815965350c051d904bb2a6a18023ee017654d4300c7c402eca9a8600c3f65dd15350c010ff0eb28a6a19429d2056514d4308e8e21ceba1a8611d1c435d74350c11a38873ac86a18234710d7590d4302c3fc3aebb128600c6f825d76250c018d904baec4a18031bc8175d894302c3f42ee1b12860087d85dc36250c031df0e906c4a18029b21520d8943486373aa41b128600c6d754836250c019d2e0906c4a18033adc120d854300e7438241b0a86008f7875846150c014e90ab08c2a18023be0172d944301477c3e41b2886008ed87c836510c011df0e906ca218023b61d20d944300637b94a4b28860187c875416510c0b0fd0bbb286218021f6177650c430061f42eeca188600c3d85dd94310c1193ca7bb286218032bc837650c4300656906eca188600c9f7654d4310c018bd0bbb28621803176177650c4308e4f2a6eca188600ccf20dd94310c0199a41bb2862180327dd95450c430058f42eeca188600b1d85dd94310c0193b0dbb2862180347a177650c430068ec2eeca188608c9f65dd94310c01b1e41bb28621803634837650c430464f43eeca188600e1e85dd94310c01c3b0bbb28621802a7e037650c430054ec06eca188600e8f20dd94310c01d1a41bb2862180327ddb7550c430054ec34eaa188600d1f759d54310c0153f0cbaa862180327dd97550c43005c7c12eaa188672b8c825d54310c0172f02baa8621802e52057550c43005cdc02eaa188670b98805d54310c11c3ecb32a862180327dd96550c430058f42ee4a188600b1d85dc94310c0153f0cb928621802a761a7150c430054fc32e2a188600b1f855c54310c016390ab8a8621802e3e097150c43395c6412e2a188600b9b805c54310ce173100b8a8621802c7a147150c430058ec28e2a188608e8c6250d6210c010ff0ab82c4218161f21570588430047bc0ae0b1086038f4815c16210c031d90e902c4218029b215205884308d5642240b108608acc834816210c019d6e
  | 17 => 0x2e8600a6e8204165d0c014db04082cba18170f99574d4f430058ec26a729e8600c3d65dd153d0c010ff0ab82c5a18161f2157058b4300c7643a40b168600ceb7048162d0c015e30010ac3a18063d21d10587430077090220b0e8600a6e829826590c014db05304cb218029ea0021996430053cc004332c8600a6e829026590c014db05204cb218161fa1c40996430043ec388132c8608a5e831026590c014bb06204cb218029ba08409964300536c108132c8600a76811026590c014eb02204cb218029ba0a309964300536c146132c860087f874826590c0b0f90e904cb218031be1d20996434863643a4132c8600e6b804826590c0b0fd0f084cb218021f61e1099643005374142132c8600a6d828426590c01cd241084cb218028fe1110996430051e4222132c8600e69204426590c014dd04084cb218029b608109964300637b94a4b2c860887e879416590c014dd05282cb218029b60a50596430053b40ca0b2c8600a75819416590c030f90ea82cb218029ba08505964300536c10a0b2c8600a6e829816590c014db05302cb2182396cc260596430052fc3260b2c869ac6f76c816590d218deec902cb218029be09745964300536412e8b2c8600a77815d16590c014e902ba2cb218029ee0174596430053c402e8b2c8608a5e839c96590c014bb07392cb218031bdca72596430452e41ae2b2c8600a6f825c56590c014d904b8acb2182297a0c21596430052ec1842b2c8600a7a800856590c014f30010acb2182297a0e70596430052ec1ce0b2c8600a6e829c16590c014db05382cb218029da0670596430053ac0ce0b2c8600a6e821c16590c014db04382cb218029ba0a405964300536c1480b2c8600a5f835016590c114b906a02cb218021fa1c40596430043ec3880b2c8608a5e831016590c014bb06202cb218029ba08405964300536c1080b2c8600a76811016590c014eb02202cb218029ba0a305964300536c1460b2c8600a6d828816590c010ff0e902cb218021f21d205964300637c3a40b2c8600c6c874816590c01cd700902cb218029ba0820596430043f43c20b2c860087d878416590c014dd05082cb218029b60a10596430073490420b2c8600e69204416590c114bd06082cb218029760c10596430053741020b2c8600a6d820416590c0b8bccab9ea921802c760f54952430062eb2ee6aa4860087d879974390c010ff0eb2e87218030f5da75d0e430061ebb2eba1c8600c5d769974390c018baecb2e87218021fe157058a4302c3e42ae0b1486018ec874816290c019d6e0902c521802bc600215864300c7a43a20b0c8600ee1204416190c011db01b92caa18031bdca525954322e3a38ca4b2a8694c78709496550c018dee4292caa190f1d1c4525954349e3c380a4b2a8600ce772dc56550c019c8e5b8acaa18031ddd47
  | 18 => 0x4c015e30010ec2a98063de1d10d85530077090221b0aa6008f7875846154c015c904b08c2a9a6b8bd53209905348717aa241320a6018bc875016414c0b87ee9bb2a8298031bc83765505300636906ecaa0a605c5f83dd95314c118b907bb2a6298031bc837654c5300636906eca98a600c3f749915314c0b0f90ab82c4298063b21d205885300675b8240b10a65087c875516114c778d8e4aa2c2299421f21d535845319e36392a6b08a650a748154d6114c051dd0fb92c2299231b1d7725845300476c06e4b08a61ec6f751c96114cb78d8ea392c2298022fe11705845308c5e422e0b08a6008ef825c16114c051d904b82c2298023ba1f20584530147643e40b08a6008ee874816114c011d90e902c2298063d21d10584530456a41a20b08a600ee1204416114c014dd05304cba18029b60a60997430053d4004332e8600a798008665d0c014dd05204cba18029b60a4099743005374146132e8600a6d828c265d0c0b0fd0e184cba18021f61c309974308d1f4206132e8600a3d840c265d0c014dd04184cba18029b60830997430053b4086132e8600a75810c265d0c010ff0e904cba18161f21d209974300637c3a4132e8690c6c8748265d0c01cd700904cba18161fa1e10997430043ec3c2132e8600a6e8284265d0c014db05084cba18039a48210997430052fc1a2132e8600a5c8344265d0c01cd240884cba18029ba08109974300536c102132e8600c6f7294965d0c230fd0f282cba18029ba0a505974300536c14a0b2e8600a768194165d0c014eb03282cba18061f21d505974300537410a0b2e8600a6d8214165d0c014dd05302cba18029b60a605974308f1da04c0b2e8600a3f8650165d0d358deed902cba1a431bdd9205974300537c12e6b2e8600a6c825cd65d0c014ef02b9acba18029d20573597430053dc02e6b2e8600a78805cd65d0c2347d09392cba18028f612725974300637b94e4b2e8611a3c845c565d0c014df04b8acba18029b209715974308d1f42042b2e8600a3d8408565d0c014f50010acba18029e600215974308d1f424e0b2e8600a3d849c165d0c014dd05382cba18029b60a70597430053b40ce0b2e8600a75819c165d0c014dd04382cba18029b60870597430053741480b2e8600a6d8290165d0c014dd05182cba18029b60a30597430051fc2260b2e8611a3c844c165d0c010fd0e182cba18021f61c305974308d1f42060b2e8600a3d840c165d0c014dd04182cba18029b60830597430053b40860b2e8600a75810c165d0c014db05102cba18021fe1d20597430043e43a40b2e8600c6f8748165d0c018d90e902cba18039ae0120597430053741040b2e860087e8784165d0c010fb0f082cba18029ba0a105974300536c1420b2e8600e692084165d0c01cd240882cba18468fa1010597430051ec2020b
  | 19 => 0x29720d5058f5402d2f42860b1ea800a9d840c163d50015ab02182c7aa0461f2157058b5400c7643a40b16a800ceb7048162d5001a5e40bb6a92a0034b48176d525408e1f3a6a931ca800a5d83d5263950011df04b8cc72a00a3b2097198e5408f0e31ea8b1ca8018dc874c1639502353908982c72a0063b21d2058a5400537c2a40b14a800ceb7048162950a90fd0faa2c32a0470f1d354586542a53b40ea8b0ca8018f48744161950014ef0a882c32a003b8481105865402c3e432e32a2a854c74615c6545500b0fb0f2a6c6aa00297a0e54d8d540052f418a5b1aa800a5e83d4363550011bf0eb18c6aa0023be097118d5401476412e231aa8018ef8748362550014df0a906c4aa0033a5c120d895400672310e2b12a800af18008761550031ef0e886c2aa003b848110d85540047bc3ac230aa800ae482584615500b87f09bb2a82a0470f213765505400637906ecaa0a800c6d20dd954150014bf06aa4c62a26b93d4f2098c5448727a9a41318a8018dc874c1631500b0f90ab82c42a0063b21d205885400675b8240b10a85387c8755161150778d8e4aa2c22a14e9d20554584540147743ee4b08a848c6c75dc961150011db01b92c22a07b1bdd472584542de363a8e4b08a8008df835c161150111b906b82c22a0023be09705845401476412e0b08a8008ee87c8161150051d90f902c22a0023ba1d20584540047643a40b08a8018f487441611502356908882c22a003b8481105845400477c12e3326a6028ec825c664d4c2317908b84c9a98221f21570593530051e422a0b26a6058be8790164d4c0b47d0a202c9a9802a760c40593530055ac0880b26a65487f865c654d4ca98ecc2b8ca9a98221f2157058b5300c7643a40b16a600ceb7048162d4c011df04b8cc92980a3b20971992530446e41ae0b24a6018bc875016494c1153906a02c929823271cd6455253004aec36e6aa4a600c5d86dcd5494c01a9e41b9aa9298035348373552530061eba4c9a9ca608a5e839935394c01a9e40bb6a7298035348176d4e530470e322c9a9ca6018ec874816294c014df0a902c5298033adc12058a5328c3f43ea8b0ca651a7681d516194c010f90eaa2c3299461fa1f53586530462e39ea6b0ca651a7681d4d6194c031e90e882c3298029de1510586530077090220b0ca600a3e8414b6454c0b1bb07b86c8a98028fa1350d91530045fc3ac8322a6008ef825c46454c051d904b88c8a98472719173951530051ec3ec92a2a600c3d87d925454c01c5e41b24a8a98038b48364951530043e432e32a2a605c5f639d85454c018de413b0a8a98031b482761515329c3e432e22a2a63396c825c45454c0b0fb0fb24a6a98030f9d36494d5302c3e432e329aa651c74615c65354c031df0e906c4a98029be1520d895300674b8241b12a600ce4621c5625
  | 20 => 0x72e0000000ace9e332b9ebd52015738a287400099d00b8a3c18c00006b00013cea650000ee80005b810ca26800000000005300001dd0000000d0871a541298c00030c4be964421000903b00000000084a428382321b304b0d30358000000000136416c000000000000043300011d60000000000fdc968000000000000000000000001b9000142d57e00000006b553000023a80000000002f880003aa89008e98707526233d01b180000003df800061e7e121b0e200e21121d301813ba78b0b4a13083c95f0000e3047618507418386f252800022993f052900019f0ba2925000000000085c4ca800067829400000007b08c7000000000026348b801116c9813fb16543b80004868000ea0a493b782f4518927057888d4d60005310000dc80003c1101d4266b647a91a421665627c823806c00014b04110014010014108000110e0400800431000410002481400c000308041100000208104000100010008318a0170840890c200a0400808010c21070010050c114000200110100840224108014b0c600010100000410e0440823c31000c30000012c00c70c02401c10400000010450010810c30000933420000c10c00051c00000030010000410060430060810c00850000130c21800c41820000820000430000800400820070c700100a0401410000400011c00062071800951c00800420800c01c21050081400002830000452800420451c01800001d30000030c50000001420831000001c00c00800010c008508018e0092406812040001c30811052417c108005168e10c0050800402802c61c034104704904584300e0821431440840880440000c000c10104124118a3020021c114200000004004900400b0020051c80552c00040420450404c00041010801000030402c10050820402420070c20020c00c50400000011010400080500020440830c96c10c31000094001c050700700110000f1470021400420100800110081002411010000000540000000020430401031461023d61c10810000810c30041424c50030015841840080031821400400010430852e41030801025800000400400070861c70800860814001040800010040820000110810020000040010000441c30070831010820c400208100c2464860420800801082800940022c108000120d0c00410020c10c00400040800010803031000040000000010472000810021400080000001430810400d30010002044c30000cc05001414708400c0001400c30090010841000020041000402000c00021460000424c00c10400400410c604000140f1040021862c30010c10450020410011010c904004400000000218308700500411304300200300500400428000000000604000018018404208000000108a0021000c008200477c12e331ea8028ec825c663d50230f90ab82c7aa0
  | 21 => 0x1ff914cc92ac617193108000004be0000e8800027e80000006c300004400008b300000000008571208ec000000041b00000000000000000c4c00026109403c00002de83090dc0002a980000008bc4c980000000000001968e9400028c9fb0ad645f2ba00000007470001a912e20a400000000001c623e07f4a0a547000000041e76b51913341623fa3de840879e00037a06e80007c7041000000041f00014ec93e23500000000000002e780007ee4de000000092000049e80000000b833c00000003624fc80000000004eaaaa800032c16b800130400050e0000f1a0000000000c984b6000000123a8700000000000000000000142476102406487be91b2041a18dee5a538e85dc352a464f89ca00003c013c9bb000000000000000000000001a38000898035071c0000cd00000000000000001a6cc020005049b7c40800000022bc00095e000000000000000026900000df00000005ce0000000000ee40fb41d80000002b500000001aa000000000128451f000102c00000000000000006704f30001294a0b15fa45071600000006dc0000001e10ac128200000000009580001481ae40300000e019bc0002b25028e048184f50001b780000233bd00000003e947991ec44a7f0000000000000000024d4bf08f600000009360000dc000000000000024f80009ce0000bf460c58000000004c04164e5800000033500016687e200021299a8820ad8000000000036809380004de0000001c140000001ff000000078c00000000001cd0000000000000000000059ca01000098400082d0000000052441000000000048202680000002ca33480001b682a0000000c907a5207000000000020c111043c3f610e80000007a600000010946664e2971890c6a653eaa84ce800000000000000002a78000430000000000113a0001df93b00000000000c3821e496000006499e7c244600008e02d613a06bc0000e24b08000000160000010000000037a800030e3b8451951507400004c12e52421260000ad83c200046695340006bb0001124c7c7c94728b34dcc0001288000000000485889000038a0000000e922af4171ac8c1014a13d08ac3420d024904c4d680c013da610cfe00004180b80000000000ba4000000000285400000000000010da00029a8000bc05fb371800082600010da06400000000000000000000000704000000145a20d55c888000097c0000000000000fc80000000001374059000139800007553d8000000000000000036aa5c24e9470000a7c50f934c3ca7b648d229cd920000000f940005f51baa24512c00000000009c400054325dcc0e9503fd9660e08aa914400015760003ea1aa4d264790509a5400089213900015840be0000000fb44d4098227c00079d0000000000093427800061637a0c7883059889347111986c2000000067c
  | 22 => 0xae600000011905da2d24962678a040523502a780003c9000000084c7dc06580000be00005000000004ef000000145a9872bb9ea80000000001e6110800000021d01c822a0a2800000065b0fd800000000000023f42a2a9a28027008b80ab01580000000004b580000003db0001e295388ea204ab58af801254e84c80000000000be04243a22589e0509a52a27210e0db41e90141384396a1a11c1a4957874d2978000000ab8000000000000052a89ac3c4aab13a8000000000000050000012b26d1500b1c00000000000003b500001900ba00000000000003802d7800000016a0001ffd55e000287947400000029a0a1d3dc0000001c780003fb00000001d26d545880000000de021a428a22697390227120c5ad459130c08e00000002a400000042f12fd1742560001ba8a8494915d003d1a60d3520a2b8e683130000000c6a00000000008040003198ae14a000026700013f488e3bb80000006640b80eb80000000001d1400000000000003f0000181000134a4e03f582781b000000000008520004940cf40000003bc800000000001513ec000000000000000000033420d4f7835500022b00008a246d8d4400000035f0fb400049903c97054b400000017384e03bc2b9000c0840000d800000002c500023740009a24eb1a340005ab00000005ec00000018ac52e0001b599acb08000446a1054a476947da69d17200041300000001ed46500002f04621468000e2206f35824bc00014700000000000000000000000000000000000075b2bd80005583dc34814cc362aa00001c6ca284ab2bb000046e23a07ca5f92a2a5310702640007ea16800740000000d400000bc4d809012ec0b4a3740600001080002ed8000f5699b0001e483560000cd9594f4e00003f197cf763e7402000045e3a1235000159a5cd2f490149aaa2200027d0672791000000009242438c8001244a4c3428000ab4114396296038a84835107780004b42930df02420001f500009b894436213c0ee0999343939c00000042c20613200000c014f8c7068934e86fd4c24cc0001cdd3b4000000000000000000007c48a2a5b00028502fc99419c00000000ca25d000064ca5f000000102200000022003a4a6f000000000017c0c1800000000000f887000039f33a8a2800000000029d0000960471a69800025a0000000dc40003958144e5488548e064ce8c6ed0000f20b3a000549000157238313429746ae273556805032e9a300024050468320069c7141492007925d8b8e70150c800126c7293d1a5140008f92450f7945249300000000000000000000000000000150cee295729600002922be0000f585b85bf42300003544911b496cc5be00000004384620004f4131422a1642bf9e000008d100000005729d042591688bc00000023dc0001f40000000b3200000013752e07b7
  | 23 => 0xd0001c8cc2e8ce39f1db000000037f00008dc45d55603651563460012080000000000000064220213e8000dd0000000000139a00000000007c22a807701a49ee0002e99fb544e42c3640f0c0b826a53000000000c40bb01b521253f0001628000000366a6f4bbc0000b90000ef89ad56a270c00000000000000000003df00000000002c6000000000031d81ac00074e000244ce0ea200001054c1a0002e81e5c0a87f74310618000446000156cbdc00000000007ea0004c3000037670a1d6800151c0000000ff00006ce30ca1545dc5090b79a793823434959d7840a55800018847c42eb4918fbcf9418435689b80000b70000000d1040100000001763c545c17cc00012a24480003140920a10cac77200056026c10d000000000000000001290bd00009e2180000049e00000000000000001ce000095c4761cf03dc0001ce31b94b800000002da3fc00074c41b8b44d066f030317704908be09da10cd347e04dd88b12ba9b83ab9e8820607c030857113c2c42d900002b4292000000000065200017b40009ea0099e5400000027722d0b6a00000000003be9633d9800000046d000295c1f800000020f0aaa1ec1330bbd3b6000000165c77c79c00019840000000001530c36000460aa30c445302f41c005f40001f01c0d3bc1231c318a8c5a0004cb1300000456000000000000006b961400000048a85493eea1012715d4fb60005130d9434e13400011640000004d40000000000000260d5a000000023bc0007430002a144d200000000010246400000c7c0007d82fb15200000000002b2c33c00042480007047a40ac8f300008303cd03489d60700000001232a5600012c0d223593d6847c000360000172903e85451180000009531a6800158a4bd00000000002e600016795a630451e000131e2b7562177d19280f1088e10dd2a543090000c0800013884fd4b26283f30000c946c71f700008620003be800079476d00015a837a3a711f00000008ed00000007e60bf2649c580f499f566234114a00000000011ac4df210a9f80000000000000000000123155800000000014882aa808222962d32200000000000002b300000014a220146a217400000032e84b80008e400012940000004d7000000000000000014ea0d100000000000000001fc90b400045480014508162bc9f0c8b062f3af809023c1000d71c2d31284000007ac000663000000000c00037c000137896c0000000000000000000000012800000000000112ca15e0f980002ea8000e6c00009780000000004292a254fe2c90001ab854008d00000003e4150000128c29000056d80000000000001ff00004fc3d41d040c446b1da1d90ea28d23188000acc90716c80000009e90000b0933862415e85346de09537b0db400000034600003ae0000000000000569481a31889653114e800
  | 24 => 0x513a479b39c8cb40005d600025a432a00017a95b400000049c0dc000000051f8000000a8450027b00007cb000162000000000000000000004db26ac00067941298680000003e801c866e0004288f40faa796498000069600018180000000f00fb10cc92e0000b2a7f069488a2e4a914bb08270000c9486496e000000082479300000004b24d60001e24fae85f3051d880000001fc9f2148e0000d2110883463224789f8c8e25824d00014f43a023180006480000001da800000000008b809625e00022082300001ae2b64c8c0002ed090c00000043a90e44001e31b19b4033239b10380007267cd34528b03c877410f800136665531d230cade3c7000000146a0ea000209000016328b20140000000b9800134000007381fce3041b3a90e9489a23655900001a818b32c000000000004b8000000000000203462a000000000000000023d000000081a00000011485272b100000004a00949b08dae323144800090ea3e00003b000062e02c00007e8a4f00000000000000000000000104000000102aac10da05fd1e80e042200013e60000000aa84f82e551511543865c31c8800000050d00025ece782ec19400012c80002de115d224975000000148615f000000068a5d900000006e84d137388c91d226429c066000062c00000000000000000000000000000000112a0001808d4c00000000002b8df233a00000000002422bea79439e627447ab447d8802000000000064d000000047a000077a11c00023000016c00000004008001188000109ab0c68e0004e780000000f40c880c400003e456800123e000153000000010c41a0000b5c44f000011800000004d062400000009992e00009594351548aaea880000000d506cc5078b045e400049a0000df80000000000e70000000000087a10a2470038eea2c010b800000000000000000000000c4157000000036e10a00000001f400009d20000fb84e4b52a7347d002c52c0dc00001992d487727a17b06a40000001d3c0000004cb80007d6a3b28415b0c2c00012a9f043fe3c105d055898271200018fd2c42bc0000c780000000000000fce4ea0000000e740003bf00000008c000003740ee00000000000003a84058cc00000b50001964000000000000000016b00000012205714c500000008712598e640000003589c3127e0000000000db26800000f346a81d00000c9d40800000000000006cb16ea0a0000000000180800e01a00008815b458310426312748331d5000000088b0798b3c0000000000000000755000281c00068b540000000029c000068c0767860001590f5800000000000003c451c1e7d19e9584da91c40000004cd0001176ab000000000000000001b94e600000de1578e20000000000000000030e9854e1c3ab00011d0d7a000006225cffa6b500003f4000411155800000083
  | 25 => 0x17c9c347a256e0001181210000075800095a5684ad18f4000a4000000000006623a100000000002139c2000000000000000003a45438bcc0000000001910000000091000000039a259000000054a00000008e43b215180000004b500007c058612d18ea1bcecc0bc10a9b4400075c3772a500000000b100007660003060000aa86d207d00014904db0270000c6c85909b185118a0002db80008560000001a0800000000000000003b10b880008860da00000012f20001979e646ce00000029c00000000000e4003c90f47c1a70ce64a73bc29b5262a7747896d0620000434a830d1e00054f9afcd820b3174000000000029200001165360001cc80002214019010c8294b2b80b5400030a1e70114bc29b41bf1be905229e12226a800089b2428b8800000001300000003121cba884bf839814c1f3929e0002c380000003423898000cf465348c29a4ba88c80000e74068a4e1ac00013fe9ef4fd819c7f00000001698f1e0b05128000000000016a9900000fe140a80cf7081e4a19200f6850141f00000005fe4c0000000060919b14808e60a61ad28ccd8a00000013d80004a2000000000000000000015263c6000000075e54952219dc000a8d10680009028503579e50d66a8b0001bc80006ac4b9979ca2660300000000000000000c1d0421a509e98805b446716a12904660000000000d4a19a21b87cd4ce00033680000000000000d980000000000000ac200015684e000055d2ce2a5cc3022d409859cb0c42a000092c0009c6000000000000000000015749a95640000000706000197818e52500027800000000000000c6800000024141ea0003ff154000018121a80000007f90000b180000004bf963d3be00037e8dc439017d30800005220004ad8ad02ea4191c90a8433877f0319b5117aacf1788d004729fd2a7050cac69401db1e0c1025461dd8a6c138a781a806f81f081d56a9aad4049003cf20e13b0625000000000005350b119505817a0c12b1cb026c000000000000003ac0aec00087c0001f191d8000404a5710ac00000000001687d62c100011aa2f71ca2018be07a94d09f8924c15d206800140c99214195f92663ac13120c54488b553510e80000002ee8d58be469415883c402cabe5211fc424840f0000cc468203900028f55464ed497000022600025b800000000000028d00000003b1a4ec00098d4ab0140a740001ec99c51f84c80001c945e0000000000000034e0db0000a5a0a20c813e88fe4c600023c105600000029c529c7dd00022dc00000043f218c0000000001a8c00000027c0000f600000000000000abd24a9d751be40a25e01d04127021b52a54b24000000047008270f1af80009d080e3f980840000002dc8424b5000000000000008e000021906ee1db2fb90b82bc8871fe8c58f0801b08088883ac75a3e219
  | 26 => 0x4786fb3c816247466bc4b6a78422200031800000000e101624e40d82ff43f84b083a32e0a780009ca00025426b0114000133800156c00000003300000000001aa86545a224c0000b8a0004e9853824a000027800000019d32804f00002a900006348388a800800003de00043d800039800a5179db800050e54d8828000000000000044c000000020000000043000013e40002c680014bc00007b074416c72f33600000002762d500010f400003290ed1960b900025e8fa608900005b543610600000011ce0003f2aadc0004d70001970000709000000000076827f800000003d00000000004ca0002708e665a445512f8ece9661a4800000081b26900000000004360000dba5a14ff16c400000000023f80000910000000c005410001d4c00a00000017084062490001fd0f9ea812a88000688144000000013691e201966c0003d53f18ba863264f0c601ec0005320000000000000564941c00000019a000000000000000002dc00000000004ca7e800000000007b52550000000000000182c6ba00000024a8000000000000000000000000000005be00007f000024d0001ee42a61050000a9cef636c1b20000ff40000000b80eca00001280011845cb0730928e4e00055aa0890ce00000029c8000aa710b20512ca00045094f136e3e437980013b208f21780012088d80d92a2800000000000000005c42830000abe9d70001e1c2d069955880000000000000000000a992252660000000000000098e7764e2000139400001e13f871c0005488c6c000000330000038893730980000009240000000504000000095d0ca3483ec87b9072000000146145c37d20310c08fa0000001e14a6e5f439080000007245341eb8f1000024180010e456010d079c9b26a714a800147400022403fd54c1f5062a2fc00007841f8ef48447d200000013ec2774500000db05103d08000000000000015871a00028921ac22e5ef00002954f2ad70002b4800000039d80000000004d7800000000000000000002db35d01a0000015000028c532000000000000000024f0688ab280009d00000004940000000b20a4a00010fc000000314800119800048700fc00052b53726c400000028b968cbc85d704417005347592fc90f86223292f5072800000000021e4e62135000000156603754b243000000042d86380002fe00017e8000000322800000000000028ac000387000000014e00036980000000000000001548000000183c00035e4c2800000061f2a227c053e0002460708bfe00008d800071e1ea0001a7c5f800000000006ec9bf12e85ec20e00000017209420000002530000539245800006a00030880005088ee0182ad04b695439e964c6108892f3193807098e4b3932c00000000000012aa000000000049805500008d082e0000ba00006f000044300000000
  | 27 => 0xb84a2a6f13a58f2c00000039300006440e329e83b4ca200056718e40006670429bfd12800000023a00000000001d58000000000000127800034b094c0000003390fc00002a40a58000a0804c22911501920000000768ee67350432834dc01d30ff27207a83f221014291b800010819080000010000000000911000201c0004af1b99c5c000a4d34c1b2800000023c00004fe17933d800000028e43e80000001d848b1430952000000000000057a067000063400000000000000003b0095062800051b0a9400004a43b0b4c44e9d112e0001430754000000000024501396d90141d4552800000048440e000000000026800011b41161368468f1c50316f0d6cbca0003f4a0bc70a00000009005900000000000000000000000067e00006180000003d20000000d023da230a5486307ba35082749c6a3121e000151e396211a51c2b6aa800019d87cc000332a4c8b9851b039a364000a390480724db6a66551116c59600000000006fe9eb00025348de0000000edc910000279226415892d375827d5060001401680a9663c15124a40004f1017a71ccfa84205911f93da0c14bc0b9089837b43c10d032c00023400013160000000c700004a611480000004f30551f7c00064b0679adc0000e50000000e440002cf97ac58e00000000000000000000000bc41540001bbc0000003a41b3c47e7b219994688a0389000000021a0004580320e80873000187800084500023c8b769d44e499f8fde0003708000000000508800064090242700c800081000010b44d87c04b780e827c00038f9138000a1e35c1f4469ea3016c02a088052313c2620a4215803717480009e44df00007ae000000127050c0003fc00000000000000000fea5a74ba1cfc0002473e280004503951f1858400000050ba5c80380000001c54b2c3170000000000643000000004400000005193ea33e15700000009b90000000000000000105061a1a647081f55941e80000000000309430800000020602b8000664000000178c00000017d800000000033700000005ac0001cb426e2930fd00000005fd1e9800000048d01991dc2cc0003ef18143280000000000000000000220467636e142a5180401f90d00000000000000000141081752582b40004470001ec43b20000002398000000000235c000000000214c60a51e0f300014eca6c00016e93983dd04a021c8d88de00000000000000001b580009dc022085028220b00002300003720000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1000000000000010980000000000001118002800000000003800000080003c0000000480003a4018038005001600d80000000034044800000000000000000000080000000003c0000034000085800000000000c5cc800000013001cf80285401280c000060761b759d54310d43c607548110584431f49a2612044265d086d26898481109973221e19204625d54354401c6120441769505100718481105da5314543c60754811058e410059825920443655054366192881101954100718e5d204406550543c6097481101954100788e11204406550401e20844811019541007181977044362504018e0865c1101894100718195704406250543c607548110592310059825920443654c54366192881101953100718e5d20440654c543c6097481101953100790e0d20440654c401e408348110195310053825d20441644c4038e087481105913150f181d520441644c401c6065dc110d89310063821970440624c401c60655c1101893121c9a2612044065484014c99008673991210052a640219d26348487864811957210d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x2
  | 4 => 0xb09
  | 5 => 0x6
  | 6 => 0x1409
  | 7 => 0x249
  | 8 => 0x4
  | 9 => 0x24b
  | 10 => 0x1d49
  | 11 => 0xb49
  | 12 => 0xb4b
  | 13 => 0x1449
  | 14 => 0x144b
  | 15 => 0x1d4b
  | 16 => 0x289
  | 17 => 0x5
  | 18 => 0x28b
  | 19 => 0x1d89
  | 20 => 0xb89
  | 21 => 0xb8b
  | 22 => 0x1489
  | 23 => 0x148b
  | 24 => 0x1d8b
  | 25 => 0x2c9
  | 26 => 0x2cb
  | 27 => 0xbc9
  | 28 => 0xbcb
  | 29 => 0x14c9
  | 30 => 0x14cb
  | 31 => 0x1dc9
  | 32 => 0x1dcb
  | 33 => 0xcc9
  | 34 => 0x1ec9
  | 35 => 0xd09
  | 36 => 0x1f09
  | 37 => 0xd49
  | 38 => 0x1f49
  | 39 => 0x589
  | 40 => 0x58b
  | 41 => 0x1789
  | 42 => 0x2089
  | 43 => 0xe89
  | 44 => 0xe8b
  | 45 => 0x178b
  | 46 => 0x208b
  | 47 => 0x5c9
  | 48 => 0x5cb
  | 49 => 0x17c9
  | 50 => 0xec9
  | 51 => 0xecb
  | 52 => 0x17cb
  | 53 => 0x20c9
  | 54 => 0x20cb
  | 55 => 0x749
  | 56 => 0x74b
  | 57 => 0x1949
  | 58 => 0x1049
  | 59 => 0x104b
  | 60 => 0x194b
  | 61 => 0x2249
  | 62 => 0x224b
  | 63 => 0x3ca
  | 64 => 0x1eca
  | 65 => 0x40a
  | 66 => 0x1f0a
  | 67 => 0x44a
  | 68 => 0x1f4a
  | 69 => 0x164a
  | 70 => 0x141ed1
  | 71 => 0x1ed411
  | 72 => 0x140e
  | 73 => 0x141f11
  | 74 => 0x1f1411
  | 75 => 0x141f51
  | 76 => 0x1f5411
  | 77 => 0xb4251
  | 78 => 0x24b51
  | 79 => 0x1d4b51
  | 80 => 0x5ca
  | 81 => 0x17ca
  | 82 => 0x1d5451
  | 83 => 0x74a
  | 84 => 0x194a
  | 85 => 0xb8291
  | 86 => 0x28b91
  | 87 => 0x1d8b91
  | 88 => 0x1d9491
  | 89 => 0x17c2d1
  | 90 => 0x1942d1
  | 91 => 0x20e
  | 92 => 0xecbd1
  | 93 => 0xbced1
  | 94 => 0x20cbd1
  | 95 => 0xbe0d1
  | 96 => 0x104bd1
  | 97 => 0xbd051
  | 98 => 0x224bd1
  | 99 => 0xbe251
  | 100 => 0x5d4d1
  | 101 => 0x17d4d1
  | 102 => 0x754d1
  | 103 => 0x1954d1
  | 104 => 0xeddd1
  | 105 => 0x1dced1
  | 106 => 0x105dd1
  | 107 => 0x1dd051
  | 108 => 0xcded1
  | 109 => 0x1eccd1
  | 110 => 0xd1f11
  | 111 => 0x1f0d11
  | 112 => 0xe8591
  | 113 => 0x58e91
  | 114 => 0xe8593
  | 115 => 0x178591
  | 116 => 0x59791
  | 117 => 0x208591
  | 118 => 0x5a091
  | 119 => 0x178e91
  | 120 => 0x208e91
  | 121 => 0x209791
  | 122 => 0x17a091
  | 123 => 0xec5d1
  | 124 => 0x5ced1
  | 125 => 0x1045d1
  | 126 => 0x5d051
  | 127 => 0x17d051
  | 128 => 0x17ced1
  | 129 => 0x74ed1
  | 130 => 0x194ed1
  | 131 => 0x20d7d1
  | 132 => 0x20d7d3
  | 133 => 0x17e0d1
  | 134 => 0x1057d1
  | 135 => 0x2257d1
  | 136 => 0x17e251
  | 137 => 0x1960d1
  | 138 => 0x104751
  | 139 => 0x75051
  | 140 => 0x195051
  | 141 => 0x225951
  | 142 => 0x225953
  | 143 => 0x196251
  | 144 => 0x98e
  | 145 => 0x1d42d3
  | 146 => 0x1d82d3
  | 147 => 0x449
  | 148 => 0x1649
  | 149 => 0x942d3
  | 150 => 0x1b8a
  | 151 => 0x98a
  | 152 => 0x94e
  | 153 => 0x1b4e
  | 154 => 0x1b8e
  | 155 => 0x17e0d3
  | 156 => 0x196253
  | 157 => 0xee0d3
  | 158 => 0x106253
  | 159 => 0xa4a
  | 160 => 0x1c4a
  | 161 => 0x98956
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2613
  | 6 => 7239
  | 5 => 2780
  | 4 => 34
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*2) 2
  | 8 => packedAt gbK8 (1672+((h/20+packedAt gbK8 (1612+(h % 20)*3) 3) % 101)*7) 7
  | 7 => packedAt gbK7 (101036+((h/871+packedAt gbK7 (96681+(h % 871)*5) 5) % 5308)*13) 13
  | 6 => packedAt gbK6 (361950+((h/2413+packedAt gbK6 (347472+(h % 2413)*6) 6) % 11764)*14) 14
  | 5 => packedAt gbK5 (169576+((h/926+packedAt gbK5 (164020+(h % 926)*6) 6) % 4518)*13) 13
  | 4 => packedAt gbK4 (2413+((h/11+packedAt gbK4 (2380+(h % 11)*3) 3) % 108)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc0ff01ff80ffffff80fffff013e7f1d18fe3f
  | 1 => 0xfff0ffe0fff01f00fff01f000ec993feef33cc
  | 2 => 0xfff0000ffffe000ffffe000f0f1e3e30fc3f0
  | 3 => 0xfffffff00000000ffffffffff01fc03f003ff
  | 4 => 0xfffffffffffffff00000000fffe0003fffc00
  | 5 => 0xf00000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x540110011844a5461844a5460012270c085615
  | 1 => 0x64b076206a50960a6a50960a064891746b32cc
  | 2 => 0x4d570108b56ec414b56ec41470b163a30dc370
  | 3 => 0xa6aab5a01020020c78b18b8bb01d803b001aa
  | 4 => 0xb8ccd9cc78b18b801020020ddec0003d6a800
  | 5 => 0x80000e10060c10c0060c10c0effffed8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40059
namespace PEqualNP.Outside.L_meta_40059
open PEqualNP.Outside.L_meta_40059.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 2 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 30 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_544 : Interval s0Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_608 : Interval s0Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_640 : Interval s0Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_704 : Interval s0Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 712 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bs0_4_0 bs0_4_32) bs0_4_64) bs0_4_96) bs0_4_128) bs0_4_160) bs0_4_192) bs0_4_224) bs0_4_256) bs0_4_288) bs0_4_320) bs0_4_352) bs0_4_384) bs0_4_416) bs0_4_448) bs0_4_480) bs0_4_512) bs0_4_544) bs0_4_576) bs0_4_608) bs0_4_640) bs0_4_672) bs0_4_704)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_704 : Interval s0Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 735 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bs0_5_0 bs0_5_32) bs0_5_64) bs0_5_96) bs0_5_128) bs0_5_160) bs0_5_192) bs0_5_224) bs0_5_256) bs0_5_288) bs0_5_320) bs0_5_352) bs0_5_384) bs0_5_416) bs0_5_448) bs0_5_480) bs0_5_512) bs0_5_544) bs0_5_576) bs0_5_608) bs0_5_640) bs0_5_672) bs0_5_704)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 42 := (concat bs0_6_0 bs0_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) bs2_4_64) bs2_4_96) bs2_4_128)
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
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 34 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2752 : Interval gbAtlas 5 2752 28 := block_range (n:=28) (by decide +kernel)
theorem ggb_5_0 : Interval gbAtlas 5 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) bgb_5_64) bgb_5_96) bgb_5_128) bgb_5_160) bgb_5_192) bgb_5_224) bgb_5_256) bgb_5_288) bgb_5_320) bgb_5_352) bgb_5_384) bgb_5_416) bgb_5_448) bgb_5_480) bgb_5_512) bgb_5_544) bgb_5_576) bgb_5_608) bgb_5_640) bgb_5_672) bgb_5_704) bgb_5_736) bgb_5_768) bgb_5_800) bgb_5_832) bgb_5_864) bgb_5_896) bgb_5_928) bgb_5_960) bgb_5_992)
theorem ggb_5_1 : Interval gbAtlas 5 1024 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) bgb_5_1088) bgb_5_1120) bgb_5_1152) bgb_5_1184) bgb_5_1216) bgb_5_1248) bgb_5_1280) bgb_5_1312) bgb_5_1344) bgb_5_1376) bgb_5_1408) bgb_5_1440) bgb_5_1472) bgb_5_1504) bgb_5_1536) bgb_5_1568) bgb_5_1600) bgb_5_1632) bgb_5_1664) bgb_5_1696) bgb_5_1728) bgb_5_1760) bgb_5_1792) bgb_5_1824) bgb_5_1856) bgb_5_1888) bgb_5_1920) bgb_5_1952) bgb_5_1984) bgb_5_2016)
theorem ggb_5_2 : Interval gbAtlas 5 2048 732 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_2048 bgb_5_2080) bgb_5_2112) bgb_5_2144) bgb_5_2176) bgb_5_2208) bgb_5_2240) bgb_5_2272) bgb_5_2304) bgb_5_2336) bgb_5_2368) bgb_5_2400) bgb_5_2432) bgb_5_2464) bgb_5_2496) bgb_5_2528) bgb_5_2560) bgb_5_2592) bgb_5_2624) bgb_5_2656) bgb_5_2688) bgb_5_2720) bgb_5_2752)
theorem allgb_5 : Interval gbAtlas 5 0 2780 := (concat (concat ggb_5_0 ggb_5_1) ggb_5_2)
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
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 7 := block_range (n:=7) (by decide +kernel)
theorem ggb_6_0 : Interval gbAtlas 6 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) bgb_6_64) bgb_6_96) bgb_6_128) bgb_6_160) bgb_6_192) bgb_6_224) bgb_6_256) bgb_6_288) bgb_6_320) bgb_6_352) bgb_6_384) bgb_6_416) bgb_6_448) bgb_6_480) bgb_6_512) bgb_6_544) bgb_6_576) bgb_6_608) bgb_6_640) bgb_6_672) bgb_6_704) bgb_6_736) bgb_6_768) bgb_6_800) bgb_6_832) bgb_6_864) bgb_6_896) bgb_6_928) bgb_6_960) bgb_6_992)
theorem ggb_6_1 : Interval gbAtlas 6 1024 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) bgb_6_1088) bgb_6_1120) bgb_6_1152) bgb_6_1184) bgb_6_1216) bgb_6_1248) bgb_6_1280) bgb_6_1312) bgb_6_1344) bgb_6_1376) bgb_6_1408) bgb_6_1440) bgb_6_1472) bgb_6_1504) bgb_6_1536) bgb_6_1568) bgb_6_1600) bgb_6_1632) bgb_6_1664) bgb_6_1696) bgb_6_1728) bgb_6_1760) bgb_6_1792) bgb_6_1824) bgb_6_1856) bgb_6_1888) bgb_6_1920) bgb_6_1952) bgb_6_1984) bgb_6_2016)
theorem ggb_6_2 : Interval gbAtlas 6 2048 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_2048 bgb_6_2080) bgb_6_2112) bgb_6_2144) bgb_6_2176) bgb_6_2208) bgb_6_2240) bgb_6_2272) bgb_6_2304) bgb_6_2336) bgb_6_2368) bgb_6_2400) bgb_6_2432) bgb_6_2464) bgb_6_2496) bgb_6_2528) bgb_6_2560) bgb_6_2592) bgb_6_2624) bgb_6_2656) bgb_6_2688) bgb_6_2720) bgb_6_2752) bgb_6_2784) bgb_6_2816) bgb_6_2848) bgb_6_2880) bgb_6_2912) bgb_6_2944) bgb_6_2976) bgb_6_3008) bgb_6_3040)
theorem ggb_6_3 : Interval gbAtlas 6 3072 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_3072 bgb_6_3104) bgb_6_3136) bgb_6_3168) bgb_6_3200) bgb_6_3232) bgb_6_3264) bgb_6_3296) bgb_6_3328) bgb_6_3360) bgb_6_3392) bgb_6_3424) bgb_6_3456) bgb_6_3488) bgb_6_3520) bgb_6_3552) bgb_6_3584) bgb_6_3616) bgb_6_3648) bgb_6_3680) bgb_6_3712) bgb_6_3744) bgb_6_3776) bgb_6_3808) bgb_6_3840) bgb_6_3872) bgb_6_3904) bgb_6_3936) bgb_6_3968) bgb_6_4000) bgb_6_4032) bgb_6_4064)
theorem ggb_6_4 : Interval gbAtlas 6 4096 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_4096 bgb_6_4128) bgb_6_4160) bgb_6_4192) bgb_6_4224) bgb_6_4256) bgb_6_4288) bgb_6_4320) bgb_6_4352) bgb_6_4384) bgb_6_4416) bgb_6_4448) bgb_6_4480) bgb_6_4512) bgb_6_4544) bgb_6_4576) bgb_6_4608) bgb_6_4640) bgb_6_4672) bgb_6_4704) bgb_6_4736) bgb_6_4768) bgb_6_4800) bgb_6_4832) bgb_6_4864) bgb_6_4896) bgb_6_4928) bgb_6_4960) bgb_6_4992) bgb_6_5024) bgb_6_5056) bgb_6_5088)
theorem ggb_6_5 : Interval gbAtlas 6 5120 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_5120 bgb_6_5152) bgb_6_5184) bgb_6_5216) bgb_6_5248) bgb_6_5280) bgb_6_5312) bgb_6_5344) bgb_6_5376) bgb_6_5408) bgb_6_5440) bgb_6_5472) bgb_6_5504) bgb_6_5536) bgb_6_5568) bgb_6_5600) bgb_6_5632) bgb_6_5664) bgb_6_5696) bgb_6_5728) bgb_6_5760) bgb_6_5792) bgb_6_5824) bgb_6_5856) bgb_6_5888) bgb_6_5920) bgb_6_5952) bgb_6_5984) bgb_6_6016) bgb_6_6048) bgb_6_6080) bgb_6_6112)
theorem ggb_6_6 : Interval gbAtlas 6 6144 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_6144 bgb_6_6176) bgb_6_6208) bgb_6_6240) bgb_6_6272) bgb_6_6304) bgb_6_6336) bgb_6_6368) bgb_6_6400) bgb_6_6432) bgb_6_6464) bgb_6_6496) bgb_6_6528) bgb_6_6560) bgb_6_6592) bgb_6_6624) bgb_6_6656) bgb_6_6688) bgb_6_6720) bgb_6_6752) bgb_6_6784) bgb_6_6816) bgb_6_6848) bgb_6_6880) bgb_6_6912) bgb_6_6944) bgb_6_6976) bgb_6_7008) bgb_6_7040) bgb_6_7072) bgb_6_7104) bgb_6_7136)
theorem ggb_6_7 : Interval gbAtlas 6 7168 71 := (concat (concat bgb_6_7168 bgb_6_7200) bgb_6_7232)
theorem allgb_6 : Interval gbAtlas 6 0 7239 := (concat (concat (concat (concat (concat (concat (concat ggb_6_0 ggb_6_1) ggb_6_2) ggb_6_3) ggb_6_4) ggb_6_5) ggb_6_6) ggb_6_7)
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 21 := block_range (n:=21) (by decide +kernel)
theorem ggb_7_0 : Interval gbAtlas 7 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) bgb_7_64) bgb_7_96) bgb_7_128) bgb_7_160) bgb_7_192) bgb_7_224) bgb_7_256) bgb_7_288) bgb_7_320) bgb_7_352) bgb_7_384) bgb_7_416) bgb_7_448) bgb_7_480) bgb_7_512) bgb_7_544) bgb_7_576) bgb_7_608) bgb_7_640) bgb_7_672) bgb_7_704) bgb_7_736) bgb_7_768) bgb_7_800) bgb_7_832) bgb_7_864) bgb_7_896) bgb_7_928) bgb_7_960) bgb_7_992)
theorem ggb_7_1 : Interval gbAtlas 7 1024 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) bgb_7_1088) bgb_7_1120) bgb_7_1152) bgb_7_1184) bgb_7_1216) bgb_7_1248) bgb_7_1280) bgb_7_1312) bgb_7_1344) bgb_7_1376) bgb_7_1408) bgb_7_1440) bgb_7_1472) bgb_7_1504) bgb_7_1536) bgb_7_1568) bgb_7_1600) bgb_7_1632) bgb_7_1664) bgb_7_1696) bgb_7_1728) bgb_7_1760) bgb_7_1792) bgb_7_1824) bgb_7_1856) bgb_7_1888) bgb_7_1920) bgb_7_1952) bgb_7_1984) bgb_7_2016)
theorem ggb_7_2 : Interval gbAtlas 7 2048 565 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_2048 bgb_7_2080) bgb_7_2112) bgb_7_2144) bgb_7_2176) bgb_7_2208) bgb_7_2240) bgb_7_2272) bgb_7_2304) bgb_7_2336) bgb_7_2368) bgb_7_2400) bgb_7_2432) bgb_7_2464) bgb_7_2496) bgb_7_2528) bgb_7_2560) bgb_7_2592)
theorem allgb_7 : Interval gbAtlas 7 0 2613 := (concat (concat ggb_7_0 ggb_7_1) ggb_7_2)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 56, 60),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00feeaeac8eeeaea00
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40059.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.and,[7,5]⟩,⟨.and,[3,4]⟩,⟨.or,[1,9]⟩,⟨.and,[8,10]⟩,⟨.or,[7,9]⟩,⟨.and,[6,12]⟩,⟨.or,[3,4]⟩,⟨.and,[13,14]⟩,⟨.or,[15,11]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40059

open PEqualNP.Outside.L_meta_40059 in
theorem PEqualNP.Outside.L_meta_40059 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)