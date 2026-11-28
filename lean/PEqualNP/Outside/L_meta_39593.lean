import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_39593.Model
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


end PEqualNP.Outside.L_meta_39593.Model

namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
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

def SBf (j : Nat) : Nat := [6, 4, 6, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_39593

namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x405240102a0ef21ec32bc40de30be40ef32ec20f410ee20f610ec42ed21ef42dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8000009207808010cc200612e54ccb6080085a14121e8180212c544869ca7a15314d21
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s0K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/10+packedAt s0K3 (243+(h % 10)*4) 4) % 9)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 3 => 0xf07c1ffff801ff00ff807fff01fc03f807ce38
  | 4 => 0x7ffffffffe0000fffffffffe0003fffff03f
  | 5 => 0xff801fffffffffff00007ffffffffc0007ffc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x22088258292a490a2889158b162d545aa9d6db
  | 2 => 0x441104aea24c929451522ac0ab569aad342b6d
  | 3 => 0x8ea3a932b7691ca69a474fd58198d331a6ce38
  | 4 => 0xef4211c4c471d8d8e4647366cd0303c7c77036
  | 5 => 0x87bde070781e0e0f8787c78f1e3e20607bd80
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000ccc0c0c0c0c00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_39593
namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
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
  | 3 => 2*((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff00fffe01fffc07c0fff81ffe07ff0139e7c
  | 3 => 0xffff01fffe03ffffff01ffe07ff81fffce38f
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1210a08422420490105162a288a8a215452cb5
  | 2 => 0xa4aa694a51d4a90aae0ab591556455a0d2965c
  | 3 => 0x88c94a529491b22a4ea81954465511ca98c30a
  | 4 => 0xce8d8d9d191923b3773cd061879e78831f03e0
  | 5 => 0xf0e0e1e1e1e3c3c7bcf1e79e418610c1ff800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00aaa0aaa0aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_39593
namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x800a001000bc41d431bd40be41bf40dc31f431f731be43be42bc42de31bc43
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x100190003009a28a8194540c72862a04b14940cbaa06356518c66ca32165108318e29a819431d03288618e510431cb210631e5390b2c8218e590c31
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8004000851943150304520c540a198b540c6166590831
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s2K4 (208+(h % 11)*4) 4) % 13)
  | 3 => 2*((h/12+packedAt s2K3 (432+(h % 12)*4) 4) % 16)
  | 2 => 2*((h/15+packedAt s2K2 (152+(h % 15)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffff81fffffffffffff87ffff
  | 1 => 0xfffe03fe03ffe01ffe0ffe03e07ffc079f27c
  | 3 => 0xf01fffffffc0ffffffff03fffff80ffffe3f8f
  | 4 => 0xffe0003fffff0001fffffc003ffff0007fc3f0
  | 5 => 0xffffffc000000001ffffffffc00000007ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1024228a248824a050052caa4a8b145502d4b5
  | 1 => 0x854949964392486ab96055661645ae8339725c
  | 3 => 0xad118524890691492aaa0254a5508b2a5c2b0a
  | 4 => 0xc99d163912241d8dccd3981839e6c20c6f83e0
  | 5 => 0xe1e183e1c38e1f1f71ce39f01870c3077fc00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xee88aa00aa88aa00ee88aa00aa88aa00ee88aa00aa88aa00ee88aa00aa88aa00ee88aa00aa88aa00ee88aa00aa88aa00ee88aa00aa88aa00ee88aa00aa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_39593
namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x2010034000f0801c41010032813c154044058028efe32ff42ff40fc32bc42fe43fc40ff10fd42fe31fd30ff43bd43fe41ff41fd32fc31fe21fc41ff21ff20fd31fe42fd20fc10fd41ff32fd10fc43fd43ff30fe10ff31fc21fc42fe30fc20bf43be42fd40fc30fe20fd21fe40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xa877e534837ca818ef50d30f7a92217c5150f7887216f90b21de2a2217f53c867aa998dfd5232cea1c617e54886f8a6a17d08610dfa1a637e53d0b7a8621ef141439f2a663bf434c2faa71977cc230beaa4437c53502faa520df54720afa9a417e53083bc87186f90931dfa18217e544cafaa5886f50842bea8c85be424c2faa118fe14121fb18863bd43c82fca720df95010bea86877d544437a86215f94440beaa261f451482fea4a1fdc8610dfa10857c548cb7ea0a1df54630bf298637c548c7b8a6905f94642bfa9a83bf43c82f8a4a0cf55032fd90621be51d0efca210ef10832bfa9281bc421077e86215dd4520bea80877d51842f8a710ef90b20df290857e5290efca9196f15132fd20081bd43042faa018df94021dea0e81bd434877ca8195f54432dea86877e54cc3d843107bd0942bf284857c54cc2faa2204f55332f721085bd5150f7c8490df54b30be29a217e508cafca8985f94042beaa465ef4290bbea6886fd0d21cea18637f53c82fca690dfd4941df210217e53882fca218df54321bf29065bf40902fea6084f95220de28a877f54887788590f754f41be282637d50107bc8618ef14743dea8e87bf419077ea5a1df54f10fba8a65bf411077884986f90b31dea1e637e500c7788498e750c30bfaa6437e5110b7c84995fd4e10be29a41dd434cafaa3195f14121bf2a0837d528c77c8518ef10c429e2a2217e53107b86218774c832de28085de430c2dea4887bcc932fd98641dd438c73a87995f95031bf29083de43ccafca9905f14f10f790441ee21082fca5205fd4f10be2a2617c53c837e8798df54042fba0a83bc42c837a86887e4c030afa9a437e54103de6519770ca31bf2a0417f54c8278a8995fd4e20bea90837c54cc6fca810efd0040be2a021fb304c37ea890ef50d32bf2a221df300c37ea8885fd5032bea9461fb104437e86885f15210ee29a43bc4204278a890efd4543be298437c524c6fea2a16f90910fb08221bd438c73ca6215fd4b10be2a665f830c83da84217b4c832eea18637e51042faa998ef94242fc100217d52d06fea8186fd0e31bf29421ef21087788490df54242bea94877850487baa7a05fd4520dfa1c65bc5110afea898df15221fa108217d51cc2fca8906f94943bf280617c54c82fea6a06fd4343be2a063bd43d06faa918dfd4910bf29a213d5310b7aa999778c531fa908433d540c2fca520df94b41de216637e53d03ee4290efd0f40dfa1e837e544c6fea918ef55010fba8a41bf5310b7a82a06f90b41afa9a2177514cbee8320dfd5031dea8c85bf5390afea810f750e30dea1e81f721043f0a0996f50e30bf298855d53d02faa790df14e10bea8c817e50d06fca2105f548409faa243ed210877885195f14540df20281f7318c77a8710df15220bf28e817e54cc6fca120dfd4142
  | 1 => 0xd5110afea710cfd5132df210617e524437e87986f90b32ef218873e540c27aa8085f94b31fda0481bc420837ca5a1cf15120bfa82877c5250efaa6885f94441bea86857e50902fea690ef55221dea9c85bd52d0f7a8620df55021aea9885fb308c37a87206f50d41df21661be411027ca910ef90c42bf296811d5310b78a6216fd4442bf28663be5310afea9995f54c42bf29687bf548cafaa421cf95332dfa1a83be5050e7aa910ef50441be282857f53442faa7106fd0e40bf280417e50042f8a6a0ef50e32be292217c544c6faa221df55320df212837e51ccbf060104f15232df214657d529037e86995f54740ba28a657d534877ea4a1df55243ae29a21ef218877884a05f55330bf28e61bd434827ca8086f14642bea9c817d548c37885995d14520bf28065be5110b7883205fd5010df29c857d520c7bc63186f90a40fa18e43f431086faa9215f54420beaa0617d508877e8690778ca30fb880217f524c3e220085f54c20bf2a0857e521037c84905fd4121deaa0655c53482faa7a06f10830dfa1c837e519067ca9985f94843dea1c83bf41d02fea2a07ec8010bf28643bd43102fca2195f14f21bea92217e531037aa998df94842bf294657e5410fbe6218ef90840beaa4417e53d077ca998df55031fd98041bc42cc37a87085f95332bfaa221bf43103ea6218df54e41de28485be540c2fca610df54743df21483bd43882fca518df95230de208817d52042fca918df94621be2a4617e53c43ea8220ef10a41dfa18877e53c833a86994fd5232bf28e41bc42506fea890fb08420bfaa441fb10842fea610ef50c21f710a43bf438437aa0a1df54e30ef18861bc420877e87106f55220efa1a87bc50d0fbc86996f90a10cea1c637d528877ca3216f90a20de214817f520437a86a15f54742eea98857d544cbf280205f948219f2a0637d538c7bc6418f790e31bea9a41ef20082f8a4a07b88120fc900417e50ccafca118df15310ef29e817c54082faa2187e44010bea9c85bf4350b7884905f54e10bfa82837d53886fea098dfd4d42bf29c87bd43d0b78a5a1dfd4530dfa18437c53486faa7a0ef95332df21285de320c37a86196fd4d43dfa1e437e5290afca4105f14532beaa4217f544cafea9985f94743ef994657c540cb7a87216fd0f42bda82437d544c7bea690df94f21de21081bf430cb7c84195f94a30dfaa2413c5250efca7086fd0a42bf28e85bd5110b78a8905f54f20be28287bf43107ba8621efd0e42fb20883be42106bca7a06f15121bfa94217c51482fca8185f94643be290215e5310afca8195f94632bfaa241bd5310afca5885fd5130df2a661bc42842fca021df15120be2a0437e50843f440106f10a20d729085be42087b863185f55010dfa0a81bd434c6faa8105f94b30dea1e43bd5250ef8a5085f54341bfa8
  | 2 => 0xc00021000050980d00c02190c302c290800b000360440901401000030180000804024150c40045c13024fe000ac024080180003c440015403c040102515c06030005a04601891a58bc0384a030aa000040140005c010dc35048020086d000560148c00838008340dc1f01c1710c170000e02c02052080040d03001008100240001808021cf000046d08c0d0050b4110d8dd1bc0300832000000140f0400600c0d000000000115c01020023680001003000b7094042543d00c0601c090880130c2c000550000000808000000000200800000270180a1000e0740d05983008b704401084010e40b000010380c0041f014070243d000080081e040dc01422118470003404dd00300b00dea0281b0740100405794060bc040000000820188080c8121280100c02050c700002324040140000c1202405000010000800003030070500000c01014080203d0708300c060880102011004601bc0301c0b08c160081b1a8190040f0cc313400a0067aa9986fd4242bf29c817e510c2faa890df94810be296217e538877c85a0770ca30bf29821df534837ca8087dcc421de212217d544837a87887ec8120de21265bf43886fca890df14c20de29c85ec524427aa921dfd5210be29c417e50d0f7c8510ef14943bf28c81be428c37e87885f94220be28265de304c2fca621dfd4132fda82657e518c6faa4185f15321beaa065be42c42fca1a15fd4c20df280853d54883788518cf95043bf28c41f731c86faa9206fd0e309faa221f7314c67aa818ef50040ee19063be419027ca4215f55332bf2a621be5150f7ca1a1dfd5331bf290617d52842f8a2a17794f41bf28461dd300c37ea8995f94630fb88421de324cafca121fd14532bea86657d508caf8a2985f94c32bfaa621bc42d077ea3a1df14c10bf298617c544caf8a0a0e7d4d43be292615d53d06faa5a06f10831fd904417d52cc6faa610d714d21bea96877c540c37c8418df54732bfa9263dd43ccbbe6318df95321bfa9a417e54882fca221ef90d43de216817e520c77e8721df940409ea9c85df4390fdc64195f54c10bf28443dc53443ba86185f54331beaa4837d50906faa010ef50c31f710c417f514cb7c82a0e754c42de214437c54443f420085fd5230de2a4657e54843f680a06f50c20dea8085dc320c37ca9107e08310bea9e85df320cafca7216fd0c31df21041fb50486faa9885fd5020bea9883bd5090b7885186f10b10deaa061bd43503ec4210efd0c20bea9441be425037aa818ef553309f296873f544827ca5217d44010dea1861de328c6f6a0995f94041bea8c41bf43502bca7a0efd4642beaa643be4390ad8a488774c431dfa808578504cafaa321fe8c030be2a243ed200837ca910df54032bea8487bd43cca7ca8195f54c40fb90c43de5310b7e87996fd0c30dea1e617
  | 3 => 0xae71
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd100432c54d4910bc189100425e6315210bc181210865d6394910c758f548cb7351141329dd8553483385414132a758c429025d63152109d586544ca3c6454b109e980530863e6515120bc185200825d6590c30c754c42d063d63151218f590520431f6550c309e982534865e6514d108f990534869f6550c30cd153514823d65108108fd96420c71c5390910ad5845010b3943141329e181544879b434c030c7d955310a3c6454231c7d855310b1d53d0f40a758e428ca786054d21e5185438c75453d45209758e548863f65908328f59442cc25d63950108f18954cc71d5390b41d68c8504ca3d64d4e218f992544831c6154c42ae1815150e3c6454632c7d4d434423d64d4910a758c420823d6414d209798e534823e6414c10a718943ccad96090c309718d5090b6452841108f191510825e6514d218f99251c82786055132c794d43d026f654c8328f197434831c5350d208fd97438871d6414d10a758c42d029c6250c318f592508cab56114343cd908514826c6255131c754d43c425e63950108f19743442ac6250e328f191520c29d63108418f595438831d43940308fd91520c7b254440109798f52c423e6494632c714c42487645188120ced0f5048799430c320da14b104423f6454a108f990530831d43548308f996424423c6255010ad98450d0e5c6354021a758c42cca3e6494c32a758c420c71f5350d218f992530c34f53149108f594420c25c63544208f990530863e6515110dc144504cb8d5394842a798c5010a796094d219d185544c35b5314121ad9845010b1c5414d218f590530431e5450c318f191528c6f365440109bd95210871c5350d10c754d430829e63d4442ec10910042766114c208f59642cc23c6510910cd50c514832e5290a418f98b544423e65d0d21e650c300832c6414910a758e548869f6550f329718d509071d63952219d594210423e64943219758e544c65f63544209bd89544c69d6310931a758c420871f5350e218f58f544431e5350c218f59053c82b661d4b43cdd0f514823d65908109798e548831d4394332c7153534423d6414c208f995434869d6310a10ae1815250e5e63952218f191500866d6214c108f191524425e63951208f19152cc63f6454a318f191520c6ae6214c42d314c524431d53d40428f59253c86e86244010c7553320cab46154143c754f4310b1f5390920dcc84504863d64141318fd91534866f6550842a758c424867561d4e20ba181210871f6550e31d590c514cb1c5490d328f597430c25e6394910a7590320c7b24244010cb593524429d639501097d8d544863c6454a108f596540c31d5350c21cbd5052442ac6250c209b58a534425f63540218758e548834f53d491097d8d520423d6494e10c7195438c23d63d51218fd91520435853141219d584540823e64d4a10
  | 1 => 0xca6f6255130ab189438823e651092197d95300c32f5290910cb948421023e6494c20b6181320cbd06344010a7d92328c66f6255110e3d89434caf16108010c7d4d430431d4394430cb50c52443384214132c754f5110a3d63952208f992544ca7b65480209758c54c878f434c832cbd48424c71f53d0d218f992544423f6454231cb99352442ac6250e21dc147504ca796095132c750c514ca9d63d0441ecd91100431f5350d419798e534871f5350e20c714d438823d6590830ad58752d0e7b60548319dd85520c29d63d07408fd8d54042ba60147438f592530c31e5350c42cd50c514ca5f63551208fd9152cc23e6590921a798c5310a3f6550e21d614f504872e62d52328fd95430ca766194d20ad185435073854d41328f191508ca3d63151109758c54c429d63d02408f594420caaf6254143c795143ccb5632145329ed81534863f6510b30e350f324cb1c5350d41c754d43c833754d45208f99253c875753145209ed95401023d64145309b99452442d9600c43097d95320cbe021080108f590530869f6550c31c799053442f26244010c79895310b1d639501097d8d5090a9d6314042c754d41d032c5290941c7551320ca3f65108108f996424823e62953319e59430083374314520d614f204825d63148108fd9442cc63d64944218f992538871e5310b40c794d438432c5414910c754f43d071f5310910cb50f524423c6550d328fd91534431e5394842c79855310b1c5350d408758e548863d65d0e21c7990534871d53d0f42c7d4d435031d4354a318758e540423d6590b31e650c504ca3e6494020c798e540427960d4e219dd9521087345414532ce908504ca5c6355121c794d430ca9f63546428f992510863d64947208f191520423f6590b30e5d0d310c63d6414d218fd9152c435b53d4121ae58343102756114c20a758c424431c5310920b618d200832c52909408f99253c432e5210b40a7590310c29d6310a32d514f214871f5310921c750d520c6ac6250d32ab98b438ca3e65109329dd95411069d6490c318f597430cb1e6414d208f590538831c54d4d21c75855310af160084108f99053c831d548c4309d586544827b6055131c7d4e424423f6550c43c7d4c424823d6414f108fd96420c25e6395121c754e5110a3c6550d20c714c424423d6510b31a718d5090a3d6590440c754d5110b1c53d0d218fd9743883344214520a758c425071e5390b409758e544426e6214c10dc147204833950143439798c540ca3d65950328f997434ca5d631502097d8d5190a5e6394d10c79514310fa842480208fd9642cc63e6415030c7d5053487b15444010c7d4f43482756194d20aed815150e9d63d0540a7593318c63f64546329dd95310c6b86050d409b189534425e6315310c714e42482b960147439e181544c69d6310b20ecd0
  | 2 => 0x63108308f59253c825f63542419ed81544ca3d6494c20ae58352d0f1e5350f418f990534823c62550308f98a54cc31f54d4d10a758c5110a3f6454910cd90b51482796095121a7189438c73842d41329bd89534423f6355220ce108504866d6295110cd90b514ca3e6415032ce150504871e6454f419b189544c31d5310c42b5185320ca5c6355110cbd0f524425d6315320a7593310c737541452097d954310e3e6414f108f98854482bb6054943ab98b5390b3943d4121e6d81438c29d6310b319798f52842e46244010c7d9543ccb1e6454c429ed81544869d6490d328f99253042cc6250d3297596430c71d5350f218f597438826e62951108f595430432e5210b418f993524427a6015021b9185200823e64d4e20cd1505148395430c7218f59352c432c5210910ab1895050f1d43946308f98a540429d6310a20ce908504878c6250d328f993530423e6414810e550f514ca3c6454b30ad1855250e3f6550c31c714d43043545314520a758c42c42746155120c7d50534433a42d41328f992534425d63d4a10ae98352d0f9943d4132b518d210863d6414d10a758c428869e61d4d43abd895150f3950141438f990538432e5290a40c75815310ab561d0c41c754d4390a3c6255031cd108514ca3d6590832c758c544cb1d4394031cbd48424c36a21141218f993524c63d6494f10a758f5110a3d64949109e59610043986050e309d185520c27a60d4e21c758e548826c6255110c7d93534431f64d4d218f994424831e5450c3097d95310c63c6255330cd54451d0e7765440109718d5190395438c431cd5445150f3543d4520a758c420ca9f6354242d650c504ca5e6315320ce50f504cb2c52909109dd85534871f5394e428f58c544831e5350f20c7195438c73b43d4132a7d92320c31c5350e219dd85544ca3f6590810c754f4210a3e64145308f997434427b6054d20cd50f514ca3e64949108fd91534833b54141329798c54086796015021c754f431029d640ca31a758c420427860548319e59420043d363440108f992530c71f54d4d208f98a540c32f5210910b8189100431c6254c42ced0c504cb1e5350c208f195434431f5350d42a758c42907364214532e550c514cb7351d4132c750e508c63f64546309758c54086b761549438f593524c23d65d0c109718d524426e62949108f593520429c6250d32d5544310c275650c421a758b5350e9d640c630c71815310a3f6550040c7d4f434423e6494232a758c424ca7661d4e20ce50c504863e64d4e21c7153534823d6510831c754e5010a3c645463097d8d544425d6395121c7d53328caae62d0d32a7d92324ca5f63549109e980548c71c5390921c7193534831f54d4d218fd95438831543145328f992530863d6494c32c7d4e424871d4394732c714f434831c53d0d10a758e420
  | 3 => 0xd20c754f41d033754d45329e982544ca3d63d5120d5d4f514829d63d00409bd95200831d4354a30a758c428c25e6395110a79835350eac62545438f992538831e5350e428f993524c23d6494c31a758c424c23d65950319758e544825e6314810a758c424823d65d0c31bc586100427960152318fd9152cc71c5350d218f996424ca5e63150208f994544ca746154d20a7d92320c63e6414f218f593530423f6550441a7592430c23f6550c3097994534823d6414f21a758c425027b6544010a75965310b1d5390c42d314f524427661150208f992538431d6414d21c798e540c33854d4121a758c42d06e9620c020a7590328c23f65d0c10e394e5210b1d43944319dd85544c23c65d0d219e580530868c6250d328fd8d540c3b14344010cb988548cb1f5350d20cbd53524421c6550d32d690c504caae62d4c428f994424431d6315232ab9885390a3c6454d21ced53504cb1d4314132ab189430863f65508428f592538871d5314c428fd94420c23d64940208f590538423e6515121c794d43c878c424c8328f997415023e6414131c754e42d023d6494d218f596540433842d4121cdd0f514ca3d6414e218f992534871e6454f408fd91528c33b4314121add855050e9d6310840c79815310a3e6494f20e9109210863e6414d109d584548c32f6414910cd153514cb1f6550d328fd94420c69d63d4042a758f419063d6494d20c754e5210a76619512097d8d51903e06244010ae5805110a7a60951218f59250c863d64946328f98a540c71f6054c428f58e548865d6395220a7590320c399438c030a718d5190a7461551328f993520427661152308f990538831e5350f10a758c42cc23e6550d208f58d540c2d56190c318f5964310b1d53d0c41c7193534865d63d4b10ced50504865d6395130cb148424c65e6315321ae9805110a3d6494e20c794c42d067b654c030cbd0c524423d63950108f990540423c6454d108f59543887554314532cb948421071d5354042c7d50534823e65d0d42a7593300c33a42d4121c754d4210a3d64d49319dd85544823d64d4e20ec191100429c6250c30c754d439023e6414e219d986544ca9e6314442c798e548823d64d4a10c798e540c71e6395221cdd50514ca3f6454232a7d92328c29d6310a31cd10b514831943141328f99352c423f65108329ed81524423f6454420c7d95438c27761549108fd9150087374314532c7193534423d6590831c7150534831e6395332a758e548825c6354642c754d439063c6215120c7550310c2e5620c4218fd91520c26e6294d108f191528c29e63d40428f992544871c6550d3297195434cb976150e31dcd95100423c6454d20a758c42c863e64150318fd8d548863e6494d209718d544823e65d0d20cd10b514cb1d5314442c759053483e36244010c794e42d069d
  | 4 => 0x41706401010000204c0047205aa100848038232e83a04c0100c430380201c5e0402101c02054000c800094050000a00407000020002f0e8f802c661300000003b64590308500c060400203c4500012040020e03f054000c02a00c10010080000100000008490240b008032bc003780603029028110701001c010000303c550a80700004000224e4010080d02c0126403000c40140a0e4211d08c0080300800285a403000014030481e028630481f0801b52859204020218d08c0a00804028010080001404000315d4b60040003c000005c00c0e0ac01004020c80000800005b30000002c567500000c04038000000103c34004020403a1f801040120087105802000050d4010244a0dcb049050044150b4060180033c030080001409014002a80902c070a88c014b0000e6000041f00000803874230140d02c162813e015e90780a044229e809030000100e04c73008510081208003008d700c001e40700810030001b4000940b0c407054690700007c0014400094002ec190081c00c00038106a40c000130104b0023f6550c108f988544433b54d4121c754c42d023e6550d108f1964244395430c421cb148424c29d64cc2308f592534431c5414d108f592530865c63548108f592530431f6550c318f195434872e6294842a7189438c31d5350e10c754c5010b1f64d4
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x4000210000321001903180b6b000b130f1d0207010a0100051d300129010106050222000b070304020003680a007c0c1900430038000100000c09010c07020204000203c62a2b00a3a1e0d63d484244388a18a228265a818a4244010a50e4a80a0a1d187250c504cb51b20c488021459c76550d32b10e4a18601051671195438c20ebb0a6212438554e611404283eeab1c841941d73d94420428cb988428243a8dd06244010d40c421220085857310921087503a0c488021a150d620c42183aed29885a0c1f73596420428cb9885a8265621c94314132a2ee9190a29950c7250c514ca0f3b6a6a1821a85506244010d4686312200841d739925008298bae8688021431c96054c42a32e6216a090e19539805110b0ca18c0a9063469c06550e31a60e0a88a2a1d0d7214d430428db82c2a9885611c943d4532a18e4b0aa6217047250c514cb06b1ea421263431c94314132c1aa63128610e19601815310a8639286a9061075ce6494321b08e4a18a29950d7399352442843928628265455c66454c4283aec298848848e75189434cb18b0aa028687075cc6454b10d40843024210c1f76d4c4244306b18a4212214a1c94314132a90e4a18a0995047250c514ca8ab8cc8a9e81465c26454c42c2a8630aa41841d731895404286b98c8292218354c6250c2083ae7324a210f087250c504cac8b9ca888021a250d620c020a62ea212200841f76d4c4248344210c099065075cc6454a10a18e4a1aa418d897310920082923928628a65075cc6215120d088430a641941d73194424428bb8ac0a9885455cc421452083aec29884905887250f504ca583b28688021611c9430c421d40c83122008684631092108748320c688021491c95114543858e4b2a860861554185320ca0eb9cc928e41855846154c429c0e2b1060106156550c310870cb2a8618041381c1620c421a2ce3a9a87107077250c514cb0caa0c099065071d56310910c1ea6312871041d7694c42d0350210c290041455cc42d4520d80c6312200860f531894388761b18c488021075ce62d5110c1ac7316a91951a70d95434ca8cb84c8a9e83451c56054c42a30e0b0aa621619535805110a8ab9885a8a65075ce64d4810a60e2a80a0a1e0d63d48424c28d386a6a1c43645cc4244010e16e4a18a09941d73993524434431884900418554d6114042a32e6210a09941f76d4c424868ab988428a65839d46250d32e228628ea0994e272989100428b38cc8a988546dd23214132d44a8312200850d75109320ca86bae8699065511c94314532e2287a88a0996a143189100428a3928628a65469c26454c42
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x4273000140463280000040078403c05651c9430c421a088250c6054831a048250c6154830c81731884244010a08825806054c42c81431c1620c421a2185d0c6244010a21851d06244010a04825846154c42a0681d4c6250e20b008250f5114132b008250c51d4132a81831086148020890865ce5444010b008250c5114132a0a80d4c6250e21a10815806054c428858718c4248421c81431c5620c020890865cc4244010a81839506244010a818310860484218898718c4248020a81831d06244010c21751884244010a10805846154c42c09651c9430c020
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 27
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
  | 6 => 2*((h/28+packedAt s3K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/295+packedAt s3K5 (21654+(h % 295)*10) 10) % 802)
  | 4 => 2*((h/315+packedAt s3K4 (33554+(h % 315)*10) 10) % 883)
  | 3 => 2*((h/69+packedAt s3K3 (7056+(h % 69)*8) 8) % 144)
  | 2 => 2*((h/23+packedAt s3K2 (1620+(h % 23)*5) 5) % 27)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffc07fff01ffffff03ffff03ffc1fffcfc71ff
  | 1 => 0xffff80fffe03fffffc0ffffc0ffe0fff3f8e3f
  | 2 => 0x1ffffffffffc07fffff03ffffffff03fc7ffc7
  | 4 => 0xe00000fffffff80fffffc0000fffffc3f80ff8
  | 5 => 0xffffff000000000ffffffffff0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x24530a311c48912300b2cb2192c096645c30db
  | 1 => 0x48852652243922452c05556485520aa92d862d
  | 2 => 0x110a1484489074885550268a29a5201282db46
  | 4 => 0x9c2c58e8912240ee9a6980c30e39cd03f00db0
  | 5 => 0x1e3060f0e1c3870fe38e38f3c0318e23ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xe8e8e0e0e8e88080e8e8e0e0e8e88080e8e8e0e0e8e88080e8e8e0e0e8e88080e8e8e0e0e8e88080e8e8e0e0e8e88080e8e8e0e0e8e88080e8e8e0e0e8e88080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_39593
namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xc03c004100e0000000080003470010000850050000000010000412400011c00000000111c0fd20ff10fd10ff32f421fc30dc30fd32ff31ff21fc20fd43be42ff42fe21fe43fe10fd30ff41f721fe32fc10fc32fc40fd40ff43fc42fe41ff40fc43fe42ff30fc41fe31fd31fe30bc42fd21fc31fe40fc21fd41fe20de30ff20fd42
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2208403000800300441801804d012e080003200b06000c183040c9800c2400001140033e000800800f80000800d100491c0c0430c0040c8100081f5084309eaa4415c535039aa4185ed4132bb2904378504caeaa321d754c42d7290853c54486eca321cfd5132ba28a656f5250678a8886b10a32f3190439e420c3ce8410f594430ceaa0619d5310aeca3a16d10b21cf214615e53c82baa7905bd49109e2a2417551883ca6410ddd4540d6210413d54cc7c842106b10932bba8a41a442087b4a0185b14941e72906175510c33ca8184f55332af29e813d5404278a8997994821db216433f54487ae42185d14540b6a94877651102bca788760c020baa8e655c53443ae431857d4d10b7a928176518867ca5215b94a439f2908577514cb588510d754c219faa2215e5310a7ca910cf552219f2a663ac42086eca3106d108219f2a665745150b6c8410d754f10bb288615c53482e8a2906794c42afa9a817551103aaa610cf55030b6292813e54882baa7a07910821b6a96636d520c2dca41875544309faa2416e52cc6bea6905794230af28061d830c83c843107594c21bba8a853e540435885105d54742b629221b541106eca3994f95030af298439c428c3a843186710830
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x410088019c04014028b18954042a66290821c910a518821d6510830a918941107855310821b158c420870d5310821c3551520c2556508430d1549510c3844208630c9108514cb8663108219918951103844208430ca108504cb865310821e210830082a4644c821c995021883c0210c020b818132087856310821
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x400090aed2988410d057598c4208702b288410861415d44208430
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/50+packedAt s4K5 (736+(h % 50)*6) 6) % 46)
  | 4 => 2*((h/67+packedAt s4K4 (3159+(h % 67)*7) 7) % 117)
  | 3 => 2*((h/15+packedAt s4K3 (912+(h % 15)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s4K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffe07f01fc07fff83e07ffc1f07e03fd9e267
  | 2 => 0x7fffffffe0007ffffc007ffffff8003fe1ff87
  | 3 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641230a29a20b0cab
  | 1 => 0x2a14b321c91aa4e5816c2ad50d4742b4d96265
  | 2 => 0x4c28644483a3492aac104d1a56d1051960b786
  | 3 => 0x68b1468912320db34a59019218e59611f40350
  | 5 => 0x70c1870e1c3c71dc739e71e380861821bfd800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80eae0eae0aa80aa80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_39593
namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x1840000030400031000c00000c529524c057042ff40ff31fd10fd32fc31fc21fd41fe30fd30fc40ff42fc32ff32ff30fd20fe40fc20fe21ff20fd21fc43fe32fe42fc30dc30fc10fd42ff43fe10ff10fe43ff41fd43fc41ff21fe41de30fe31fc42fd40fe20fd31
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa877f52042faa898df54c40bfaa263ec428cafaa8885bd4910beaa0437e52906fca7885f94343bf298437f524437a87215f55010bfaa0637e548c6f8a9885f94331bfa9e43df410c2fca2185f94321bfa9a837c540caeca2185f15132be29e41f75150bba64195f94821ee29a21ef4290af8a0997b08420be28a655e500c3ba43185f94e40be294217c540c6fca8217710830bea88877d53d07bca7a07750f32be282877e520cbba81185f94a42bf284637d53c43da64907d90441efa8861ee32c83ba869957d4d10be292637f5050efea710f714630bf29421de43ccbbe60186f50c42b6a96637e54443baa621774c630bf2a083df548c3be87185f95321fa20843de548c3bca0185f54b10ef21a657d54cc7eca2185f94342bea9c81bf4310fec20886f90a41bea88657f514cbbe85185f54b31ef90861bc42103f621087790430f6990655d53d02fca690fe90040bf28c417e50086faa5985f94441f790441de30042faa7a0770c320fd88221bf41106fea990f7cc630bea88813e54ccbde64997dd0631bf28c857e530c2fea910cfd5121bea8e877e53d0afaa8187b8c821df210837e50ccbbca3185f14f10bea9c85bc544839ca4185f94030ee29a81dd540c33ca8187794c42be2a4217c544877e86a05fd5010f699443dc30083baa610df14e10bfa9a21f7414c6faa720df94420bfa8a41ed21086faa5a1fb54b31f610c41fb40902d8a4885dd4520ef290617f53883dca521f78c630ee10861f741042fca4105f14520ee208617c530877a8720d714d40bf2a0633f54442faa9185f14943bfa9a43df518c2fca1215d14520dfaa2437d52102fca421fd54732df20881fb308c2fca0215b94830bf296837c52442bca7905f94641bf2a043dd518c3be6218dfd4a10bf29663de218c2f8a6a07790030bea9e857e518c6f8a918df94040bf290617e54083b886186f50c419f2a0617f54cc6fca7107dc8521bf28c437c54cc3ea8220f78c120bf28863f531c87de84105f54d219f2a6637e54882fca5987e4c030bf28c657e51903b861885f94220f7290617d52907bea8185f55020ef19061775150bee42086f10440bf29c83dc310c3de8410dfd5332bea80877c51502faa7195f15120beaa6437d544837ca8187948421ef182617c52c43bea4187bd4910ba28a817d54cc3f420086f95331b7296633f54483ba6218fe50040eea1061de30843d88410dfd4d42bba8a81f910043b865185fd4142eea9e415e508c2faa8197d48421fa28a81fb40502fca998770c220ef18221f451482fca898fd4c421ef994617e53c83ec6390dfd5030bf28e87ec424cafca5187790e30dfa04817e53042fea4a1d754c21fa108217e51042fca7a0f750430bea8c65f4414c6fea890df94810ee994617c53883ba87187dd0610bea94877d51d0bb8a8186f50c43
  | 1 => 0xc544c6fca8987795030f7194437e50843bc62185fd4530b6a9061bf43d037c84a15f15230bf290817c54886f8a8105f95232bfaa0417e53c87e883085f54321f710a437e54cc7dc64905fd4540b629281ee21083be61186fd0e42d6a1085df328cbb8a4185f94442aea9e417d5210efaa4185f54c42beaa4655e53107daa4185f14131bfa92617d5090fdc40905f54221ef19265ee4210af8a090df14d41afa9a81df418c2faa5207794c21aea98857e518c2fca8187794f10bfaa2617c54c86f8a810ef50842bea8483dc428c3f460185f94e10eea18877d53483b860905f94c42be2a465dc548c2baa620fdc4210bfaa621ee320cafaa5087dcc531efa9a817d51c82b8a6907b14940be29841fa20082fea498f790c43df20c817f504cafea7087bcca32bea86877e52903b861087b14941eeaa4617e500c6faa518df15332bfa9a417f54482faa9905f54910ae29a21dd300c2fea5885fd5320bea9c217d52882faa221770c830bea8c85dc30442fca3a15fd4543ef90c61de30c82faa3985f94341b629283f7318c77e85216f50441ef99061df324c7ba64185f94f40bea9821bc41903bc42185f54031fb28e657d510c2faa8995f54f20bea8683ee21882fca620f78ca309eaa6637d53883baa2187714430eea9e217e510cafca5195f14941be29281dd430c2f8a0a0dfd4d40ceaa061df528c3aaa2185f15130dfa18857e50042fca6195f54a30bf29c437d538c2fca4887710030ef20c61dd434c6faa6887790c30efa1c87dd324c7eaa321f7ccb31bf29887be41506faa3086fd08429eaa0617c53043ba8798fd94643b7294877f54cc3ba6598f708630bfaa421de30082faa1215f94b40bfaa043ec42082fca6907790d31ee20c6175510c2f8a998df94c20bfaa4657c534437c86a1f7d4d20beaa4877c5348378a8887ec8120bf2a6417e5290efaa9887d10721efa00617d50ccbbc8798df94421bf28887be40502f8a298778c310bf2a0815e53c43ee8320cf15121ef204617c54882fca1205f55031af298437d548437aa998fd14542fa98a21f741087f660985f94b43dea1e81b541106f8a4987bd0932bea96817d51ccbde8510dfd4c21bea80437f530837aa8185f54342faa88617d53082fca8996f55332bea88417f50487b863185f15110eea0c61ed5290efaa418efd0e41fa880216d5290f7e80205d547329e2a2417e5190ebaa7885f54041bea9083de30882f8a790ef15121f7908437e54842faa910df54620bf28465de528c2faa02177d0d43f7900417c5150afca4215d14542bea84657d53106fca7215f55332ee29a41de53c82fca6887750a30bfa8a85de510c3be64196fd0c41fba0a83d6510c3f240105fd4f20bea96837d508c7d885105f94c40f6a10857d51d03bc84185f95121bfa9e21f6314437c84207710e30be28
  | 2 => 0x302c02b020080a0000c030000085c00052000000000e000b27a0061980a02818ba8709002013800158988400238870018287a8120080008022058120180003d762f8120f00400806000000400c078022182ec90023586a0980037806210440009e038040083812806098022ea384a000090f03311400824008082f000000002581e0303a000341e07e0605832818008ce010040e826050043b05203858014c40e00c060000180e0280a0e1240f02407006101e22308213022050601081803802cc8020000e03014028000002a028060080c0280a11002000001603c0380e050aa2800e0e8140b80c00022040000280c00800150001c81e00800180e6028020181204822388080201e1600819002c3802239dc11016008a800000008000680201022028046a80025000028d2218160b06000006018260004203896008ea038001703215032005f14e21efa9a217c54043d88510fd10410bfaa441bf4390efaa9107714a30bf28e617f50506faa9215f54032bb28c87dd528c3dea4a07dd0721ee20461de53106fea8195bd4940f7296637d520437ca9997b4cb20bf280657f52502fca721ef10841eea0061f751483baa4186f90a40fa98e21ef428cbea6218df94020fb18843f621087de84a15f55241be2a6417e5010efca618f754c41bb28e657e5090fbe86185f94221bf284837e51ccbbe811877d0830fb88021bf41907ee43087d10631dfaa221755190efca420df14d42f6292217d5190ebca7a07bd0a20bf2a241bd43502bea6906f10a41ee90861dd310c2fca821fb48020f7a92837f548c6f8a690df55121ef98861cd520c2fca1185f95221bea86637d53086faa920770c010bf28e417e520c77a80205f14142bf28881ef21886f8a4085f95332bf296217c540c2dea4a0cf15110ef98c63fb20882faa3205fd4131bfa9821da500c2faa3185f95230bfaa2657d53c86fea9187d8c710fb188635e5310afaa918df94a31bf2a0657e50107baa7a05f95010bfaa2217d538c6faa710df55130bea9443f7218877885206fd5120bf28e81f421842fea4a0df95310ef18a63ed320867aa9997dd4540ef214617
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc54c825f6550c43cd151314423e6414810d5551510c354538c510d54c9510c32f5414910a758c421065e6315020d550d510c26f6255121d9146204825f6354241b3189418c2756194f209758c54c425e63946209798e524423d6414e109d58754c831d5390841d5cc9510c26f6254743b958a310866e62d5310b3988540c3965494430cdd5041c865d63d5021cb550420871e6494f209dd85534825d6590c309d98454083566194c42d354b510c2cd6215030cb95152cc66d6214e109798c540865e6394820b9191210873765504419758e51883575454430b958a210865c6355110f20c120082cc62552309b189544429d64d48309dd85544c364528c5109ed9510042d86050830d5d44304834f53d49409798c530869e64150309dd85528c25e6510a30b958841086756115020e350c424ca5f654c8329798f54c42cd62d4430b5986438c3655294430d914931442776550441e9189411074c5314940971815310ae46148020b3189400c2af6350842b5d85428c2ae6290d43b6983528c2ae64cca32ad584421065e6094c41c7d5230442cf6250430c7552500c26c654c9209758e519027461550208fd9153486d76150230cdd0e5190e7765484219b58853042cd6290d319798e548431e639503097982530863d6414c20c799253c423e6495121b6983548c26f654c832d598653c423d6494c329b997424ca5f6354321c7d535344366525464397994420c2d56190e30a7993318c25d63d4121ae181435026f6255010cd551510c25e6094c42a7593510c36765484219758c540825d63d5310b5987324c65d65104309758e52843374314540a7d91518c3d15194030d994a5190ece62cc4309798e529025e63150318f992530866f6254d10cb951520c23d6494c219ed95300c2e462504419798e510427661d5320a7191210c25f63551309bd89518c26d62d5210b6980528c32c548c9209b98b540c7c521084309758f54c833554947329e980540867661d5032cbd53524434d524c4309d58653486d661cc830d558653c829f6454a30b6d81420c26f625523197d8d508865e6394a108fd91520429d64cc9318f99254442cd65948309798e53443c552944309798c54c432f5410a209758f52c4315545443097d8d50d0ae46048421b3189518c2b7655044197996304825e6315010b958d21086776155232b5185408c2d56190f32c7153534831d544c8309798c520427561150309798c52c429d64cc8308f592534826f6255130c7553320c25e650c120b3588510c2ac6050842b5185428c31e5450f319758e52082cf62502309718d50086d56190d32b358a430c3354314540c754c421067661153329e58054086da60d4630c7d5230482776155132d3d4c525026f6254440d394a500c277654c431d398a530865d63951108fd9152443955454430
  | 1 => 0x863c6454d109d594410429e64d44309b98a53106d76150830f14c9310865e6395220d558453443665294430e594d41106d761500308fd954310e766114e20b6983510c31d6494f109b189544c32f5410a21e554d41106d561d48309b58b54cc33754145208f994544825d63152218fd91534826d62d5030b398b510c2756510421d314f524429e64cc430cb55152cc6d66190c309b98853082746155130c798c544874f5454830ad185401025e6514d20b6d81210c25d63951209758e510427661d53309b189501074c528c1109b98b540c34e6294c41d354f420866f6255230cb95252cc69e64cca30c794d43d02ce6214830b398a438c32c54d4910d598653d02db60504309758c5150a7561d52209b58a53d033554106319d98754cca5d6315121d354b310c23e6414c10c7152304829f6448630a91854210b4f5314910cd550410866e6215030cbd0e5290ee662cc5319758c540427561d50329d984530423e6494d20b5185420c31d5454830d914b41506776154b43a7990520c356534c421d550d51cca9d64ccb3197994304423f64540218f99053c86d860504309b189544c7c95294030a7191528c23e6494f10cb551520c26f6550842cb952520c2766194c42b998b318c6746154d20b3d89400c36452145409b98a544423e6494f20a7593318c25d6314810f194a510c34c53d4940d390d52cc67b60551329758e548427561d5332b5987520c3545314540d598653c827565084109e596100426f6548020b5185400c34d4354b319718d50d071c5414d20cdd535148356514c430c7d50304826f6255110cd152104423c6454910d5546500c3655108420cb54842106da6014830d598c5150a7761548408f99352c425d63951309718d501065e63d4142d95495190f4d6294f108f59053043564354430d5d4f51483674214542c3551520c27461552309798f540874d5254430b398b540c31e5350c41c795143ccb4d528c830b5d85548c29e64144309ed9520083365494430c7d505344365529464397d8d5010acd62d5030b9987328cae76348421e9108410866e62d52109718d509071e6395331c7553430c3566194c419d185548cb9541106309798c548863e64150308f592534863f6550842d5d4f515026d6215030e3508428c27b6054d218f993528426d658c821b5984510c29d6310a418f59053883645284110d398a53c827461551329dd8552442ae64cc932e3952520c34f528c110c755132cc6ce6290d32d3d95520c32d5410a329d18554483575314540a7590510c2ac62500409b594420834d6294c4197d95300c32c544c92097594430c38d5454830add8d411071d54ccb31d358a53d0334548c51097594418c23f6454d10d594d31c42ac6150842d5144304834f53d491097195434ca5c6014d109798c5150a3c64546309758
  | 2 => 0x6114830ad587431066c62550109b99452442af655084297d8d54482da60144308f1915348755518c4309798c54c833642145429b98a53d02756194f40cb1522048335545473297594210c2cc6250230d9d4b5150357518c120b5596510c29d64cc43097996304425f6355110cb54842103a764484219798c54486ce6290c309798c54c871c5414d10b6980540c23e6414e21d5d49510c25c6354342b358b318c29c6454630b5987328c3ca5294030d5549510c27561d5030d94c851482da60d48309b58a534423f6454632e6500400c32d54948309b594420872c5290140cd95251ccab464440109bd89501072d5494b31cd153214872c54885219d984540c32c52905419b58b54cc6d561d50309b18951d0ecf6250630b999121086d561148309d987548823d6595030b3189410c25c6354221a7993520c34e6294f40d558653d031d54d44309758c540865f63549109e181544c63c64548109d5865310b1c6355030b5586430c2ad6490842b398b318c2cd6290e30f1484218c26c6255230d514f514831e5450c30c7d95540c25e63d4b10b9d95210867661d5031ab19120082756114e209d58454cca7661d5030e5504410c25d65108309b189548c7d25194030d394d32c826c6254440b398c424ca3e6494910ab189411067761551108f593528434f520c11097d95400c3675214540b6980518c3c55348421cd552510c2e46244010b5d85528c3a76250441f40c1100426d6294f10cb150524423e6515110e5951510c34d5294030ab19121087556194c42b91854210a766194f40c759253c83355410410e394d4210a6d62d5310d398a53c429d64cca309dd85544863d6414f21d314c524426f62551209d586534833554105319e181544ca9c64486309758f5050a3e6414e109b988538425c6354042cb550420835a6094030e3552520c27665d0531d5d4c514825e631494197d95310c66e6294d10d9549510c3365454732d5d95510c2da6015230cd544411029d659503097994418c2d661d50309d185521034d6214d209b58a531065e63d532097994210c38d4210830d590d51ccad66190d31d394932cc6776544010c7d5353482f0604c5108fd91518c2d5631072197994410c32d54109329d584530834d54548309798f50506d66115030c794d4310a766194f209758e548826e6215010c7551310c26f6255131e354d4210bc552544308f592524426c6254630d390d520c2756195120b3d89518c25d63149419b58a544425c6354242d558c5150b6552084108fd91528c395549443097597400c2b46150842cdd50418431c548c110ab58b4310b663214520e6952500c34e534c8218f590538871d54d4830d1549510c2d561cca30b9987324ca3e6414c20d914b515031f540c110d514f515025e6395110c7153534434d43548309d596310
  | 3 => 0x40400e00400030001400d138000581601c470580003c020165b02800020100000001c000005808063000120007208400024150e40a3580c000030900e0001603d4b028001489303851000020643b02c710740205c0a03c01014130ac000440442802040170001302c0400400000120143500001584cf00000308270144c05004000440040d0040412c1d0000500408804011b00606007054120084202c29008016c807000146dc0a1002901c1a00c507a0050258f0182f38006150000783f1540000ca7000000280204c5c0280a0140902da160805004280280034800018120000000c03000140040000002000000441e004050046f7fc0000c1000801000075dc690000000434155e3004180f80705c0100000014000082148c000458c000140d4010001b018003843d0241002c000102a0000307801000050000500c300100508801ad18941106cf6255230a7590520c3c653484219b58a534865d6394a409b98a524434e63149419d1855010a766195120d5986530865e6315032ad191210878e54548309758f50506d860484309b98b54cc26d62150109798e54483665254430d9d48218434c538c9209b98853043555310421e9d854210b3451901408f994544863f655044197195434c63c6454d20ad181411063e6494c329b98a53c425e65086308f59052043a4644842197d8d501071d54cc430c758c544875651940309d984530831f5414d209d98653482e8604c920cd15051482d561cc8308f992544831c540c1109758c54c874d6314941b358a43cc65e6014d109dd85544823c6454a309758c52c423d6494c318f191528c65e6514d109ed81544c63c64540218f191510832f4314940cbd954210a3d64d4b1097594428c23d6494f209b58854cc65c635512097d8d5090b9543105319d58754cc2776155020c798e54ccb54518c120b598c414c74e524c8309758e52442cd6310a218f992530c66e62d503297181531065c63543219798f504863f64544209d18552d0f9954940309b58b540c63e6494d10a9189411071e6494c2197596530865f63540218f992534865c6054c218f191518cacd62cc4308fd95401025f63543419ed95401026e6215331d354c42086b66190d439d195314423f6454a31d314830442a46448421c7592530866c6254d10b5185548c31c53d0d408f59253442776154042b9584420875453145209718d524431d54544309dd85548c2ce6214430f1949510c23e6414e20d554f410866f6548421a7d91210c26e62d5331d398a5310a3d6494f10b5185528c2d56115030b958632086b664cc531ad993318c65e6394640b558c410865e6394d20cb50c525029e64cc8309d185528c336545443097594218c2b56490441c7952500c3a46150842b358c420871c540c120b6983540c33454d45209e18153486d6
  | 4 => 0x30440200001000cf00400038c40100000004000000440206c11048051a80514801000000380200010034010081403063064010101500037001100091b02000148000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x71e000080000200040c000225810052dcd800000481000c24400019000e182140c4c0035a00450d75951520c28abaca8a8861a19cc6250441b08e4a0882186456258653d0270382c690843611d12108630cc0a4302628860d6454b310c342a98c4a0883c1551525443092ae63128220d247255041042c43928020061499cb5410610a8ae321aa4185287050c5250306b22c529e21455d35254430c2acaa08821854572d51510c306b22a5a88618a150604c920e0ca8a92a21870554949510c246b98c2a1085a21903048020b08e2a1084184a47158b4310b483206088021315cc6448421b08e4a0883186846494d210869238aa821465a15cc6250441e0aa62108210d3070550414c6a2baca4a88618355162cc430a48e2aa0849960d5458b510c2c238a8421461291d1618c821e0aa8a94a2185c070484210c2c838a80200614a1c15410932c2ac8b0ca790686731854210b603106088021455d33254430a8ae521aa21852671d5042882533a4c890843641c14110430d0ae630a842161554587520c2923a2a410821621c14210830d0aa630a8421585731084108692392a220881135d46250430948e8b146210e867319121086523a2c690843a15cc64484218aaea30a84185247154842102983828628a81581c1321452083aea32242186846454d2108722b2a4210861b01843048020a48e4aa08298e3054181314429238aa821041835954210830a48e8a8842104a4725874310692ba884208438555161cc830d0ca63128220d8474484210c343298c2a1085499d35208610a8ae3aa2a41852472550418c712b288420843a158c4210421
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x40140080000a05859cc6250441a05859cc6150842c05651c94110430905851d12108430905851c54210830c05651c542108308858794c62504418858794c6150842905851c94110430a05859cc6448421c05651d12108430885871925348421
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 5 => 2*((h/261+packedAt s5K5 (20007+(h % 261)*10) 10) % 741)
  | 4 => 2*((h/313+packedAt s5K4 (30172+(h % 313)*10) 10) % 794)
  | 3 => 2*((h/44+packedAt s5K3 (4459+(h % 44)*7) 7) % 91)
  | 2 => 2*((h/11+packedAt s5K2 (720+(h % 11)*4) 4) % 12)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf80fffffffffffe07ffffc0ffffffffc78ffff
  | 1 => 0xfff03ffc07f03fff83e0fff0ff83e03fa71e67
  | 2 => 0xffffc0fff8003ffffc00ffff0ffc003fc7e387
  | 3 => 0xffffffc0ffffff00000fffffc3f803f8
  | 4 => 0xffffff00000000fffffffffff0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa6082049120080014a12c0111842984086cab
  | 1 => 0x50a58c487245526581685550a6a342a9a31665
  | 2 => 0x6143169120e9a4aaac109a6a0b690532c5a386
  | 3 => 0x458a28e2448d06f34a5a03488c739623f00350
  | 4 => 0x860c30c3870e38dc739ce38cc04218037ed800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80eae8aa80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_39593
namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5003fd3101ff14007fe52007f04001fd21007f88401ff2100ff4c003ff53007fc8005fc40007f90801fe4100ff8c805fc4201ff94003fe53007f08403fe4301ff54807fc52017f10407fd51007f08005ff4100ff14c01fe20007f90003fc3000ffcc407ff51007f50801fd4100ffcc803fc43007f44007fd50007fc4005fc54007f84007fe5100ff8c401fd4000ffd0c01fd2001ffd4807fc5101ffd4003fd43017fd0007fd54017fd0803fc31017f95003fc3200ff4c803ff3000ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824001bf98f100fffaa4a0037fc3284033ff2a4401aff54a20027fc8090027fd65c8413feb048402ff9514004ff88590003fe4104013ffa964209fd4842114ff88110806fc6344013fc9004033ffd4542197fe62a106ffd53c800fffaa02000ff9062106ffe6508027be4250809ffa048000bf58420117fa6010827fd52c840dffa10202cff9532104fd8421002afd6344001ff3128202ff90a410affaa6900c7ff6590409ff2064004ff50210017f886a1003fd2104009ffb184004bfd9140027fccb10046fd65c4001fbb0a8404ff44010007dc4210013fe50900037f31a2004ff88210077fe830804afd6308043ff28c8004bf19640007fc82108b7fd54c84073f32c4009ff59421027fc6108003be4190001ff10a2024ffd5021007fcc110803fe42040037f31c840dffd4e1004ff864a1017fc5304065ff9928409bf98a41007fe4308013fe64080017f30c802affd5221025f8c8080c7fc5290425ff2184002ff90e40025fec508027fd21084017eb004232ffcc142007fa8510013ff5090005ffa0a8400ff88521007f84288002bf64484073e32a201bff4c72001dfccb08023fe53c4001763122000ffd8142007f8c0a0813fc50c80057f3202021ffd4640017fa84a0013fd50840677eb2a8409ff10920027fe8010013fd2008053ffa144204ffd9210197fc60a1027fe420841ffea8c2004ffc8020027fcc520027fd42c8405fe21c8009ff90a21117f8a610813ff629003dfe98a8004ff1412004ffc6590002df635003f7fb2a8000ff1852004fdc6410897fc5388401fea0e4009bfd8f2104ffe8521013fe5008013ffb1e4218ff4c620027fea11007fff505001dfe20c2009ff4c82102ffa6408012fc628405dff31a8220ffcca40027f8a110057fd3148067fea828400ff5052004ffe8410853fe5108009fd1004001b718d4000dfcc710026fe629081ffeaa42004fdc4010007fec2a100bff439045bffa864200bf5832117ffca2a0806de6308467fea8a8417ffd9520007fe4320003ff6088409feb202002ff50e41025fecb100bbff3250431fea9c4009ff993210f7faa6a001bfc5404009ff2028008ff0c710005f8c290013ff3090015fea1a2000ff18121025fcc11002bff434403fffb2a8000bf18540017f882a109bff434845fffa8a8220ff0ca400bdfeca9000bff4190009ff2044001bf98e4115ffaa790897fd32884057eb248212ffcc420137fa869083bfe548401fffa942002fbd094207ffaa50800bff4390861ffb1c822effcc541007f8c120853ff5108061fe1848202ff50e42027fec310027fc5248401efb1a8012ff10c20027fc6120006de63c8005ffa0a8210ff99310067f8a48805ffe6548041ffa9c8003bf99540017ee82a080bfc4350409ff8802013ffd042010ffaa320027fe324803dee31a8000ff98542
  | 1 => 0x3ff3290409fe3182020ff8c640017f8832085ffd5048001ff3048204ffd9220007fc4208057ff5348039fe20e401effcc540197fc62a106bff5188059fa20e421fffd45400bffaa290097fe6388405fe21a8009ff8c921057fc6488026fe6208413feb184202ffd0540005fec888027fd3208009ff206202bffcc721017fe80a0803bf6444005fe2a4802bff10f210f7fe64a005bfc414805dfe9928202ef95241027fa81100b7ff51c8401bfb2a8400bbd891004ffac3900bffe6550413ff1084208fd4c710167ee8390802ff6150809ff3244009ff8ca42155fecb1080afe6190431ff9944000ffd854009ff8a810003fc6250037f69964004ffcc22017ffacaa0827fe65084097e3282000ff989100e7fca990013fc20c4043fe28c801effcc140047fa6388026fc6250009ff328200cff59510027fac720043fc42c40017eb048204ff18c2018dfacb20812ff648405dfe31a8200ffc854004ffe6590827fc61c80017fb128209ff54b20117fa8610857ed324802fffa924001bf18e210cffe8310027fe65c8409feb20401eff0c940017788321027fc3288045ffa184204ff1431000dfcc7908afff30c84137f3162001bf18f1001578c89085ffd524800bffa182016ff95120167fe8390813fe3050009feb242004ff8c22004ffe4310017fd43040017eb0e4021ff94a4018f7aa920813ff4084013fe1964225bfd8e210c7fea710027dd63c8009fe3084000ff50710055fec688027fe63084097f3048204ffc8210017f8a8a081ffc52040017fb24422bff8c321017fc86a085ffd5448009ff284202dbf59721027f8c520003ff6250409fea844025ffd0e210a7f8a21005ffc65480016eb1e401fff54140137fca690877fd54c805ffe28a8204ffd8e40027fa410807bff5350015ff29a201aff54620067fcca88013fc3004013feb0c8409bfd8c210fffaa2a00beff6550469ff29c840fff9461017ffaa4a0827fc52084137e316202ebfd8d4112ffa87108b7fd50c8401df20a8204df99410017f681200afff53c841bff21c2019ff10620017f882a0013fe628405dff18a8200fe4401016ffaa390827fd42c805fff2828209ff14a2119ffca0a1013f510040057f3264203bf1952012fdc6510803fd6448425ff1884028ff9952101dfccb10003fd42480016eb184220ffcc640025fcc0080b3fc41c8409fe2002022ff0c021187f86320827fe52080097f3004202ff5514012ff8611086bfd5488009fe9802004ffd9010047fc6588013ff640805fff292820dffcc6100effea1900137e6588037ff29e400fffd461005ff8c888027ff650844dff31a421fffd494006ff8870808ffc4008405ff21a8402bf9921004ffcc790846ff65c404dfe18a4200bf58b1004ff8c72100efc6544035ffa944002bf19310027fe610802bfc314402fffa
  | 2 => 0x21057fac688043fc41c403fff2928009ffc81200b7fe8090027fe4250851ffa824202ff50d41027fca190027fe6408409fe30c8032ff14d42007fcc5208bffc6550413ff31c8404ff98e1006ffa6508033ff50440057f320402fff14941007f62108013fd3090015ff31a2009ffd932104ffac990003fd6148013ff296420cbfd9510177fa60a08bbfc3050401f610c4004ff0c0200effca390013fe5048015fea9a2003bf19641005fac11080bff549004bfe9844235ffd4242137faa690817fe53040017fb224211ffd4b10017f880a0816fd6304001f63122033ffd9542007fec890013f71084023fea962017ff945200077ec890843fe54c4005fda02801eef50d40027f8c90800aff6050001fe3162009bf98820066f8ca88013fc650802bff21a4004ff90110197fa64a1006dc63440017eb122004ff10020005fac908003fd21900017f30c8400ff581410dff8879007bfe6350005ff2148029ff99221005fac910813fd3008069fea9c8404ff594200effea39006fff31c8015fe31a2000ff98121025feca080137d6504001f710c4000fbc862104fde4210856fd6288045ff2984220ff14e4004ff86590096fd6388467fe28a8415ffcc52012ff8631082bf53144061fe98c8215ff10d2012ffca71080efe6588401ff2084030ff98e4104ffa421005fff5148063fe2848226ff4c521027f8a088013ff10840137fb26400eff1521004ff88490803fd62c40037f31a8200bfd9120187fca72088bfc31084077e32c4228bfd952104dfecb21043fc64c4013ff996400bff109100dffe619000bfe415040bfe1882009bf98a10017fe8520013fd6584023feaa62014ffd50200277880a0013fd6284051fe2824211ffd9710027fca0a000bff40500137f31480009fd951004ff8852100bff5450409feb1c2000ff501200affe649003ffc5184015fe98a2004bfd922004ffc8410003fd40c8009fe1022008ff98f10027fcc608013ff208806bfe2848409ffc8720167fe8190803fd42c4001fea0a4202ff15142107fa6520057ff304801fff2942004bf98020027fca110003fd41440017fb0a8012ff14c200b7fe8290013fe6108009ff186401aff94620027fc409000bbf4190413ff90a4000ff9814204fec421087ffe5150013fe1924000ff1894106ffc6308013fe6590069fe98c8411ffd4310017fc84a08b7fe50c8431ff21c402eff14d41004feca9080bff4050861ff1948204ff8c1200c7f88710027fe525083bfea864002bf9922008ffacb88077fd51c80077f32e4200ff98940015fac920022ff63c4031ff98c402dff94721135fac6908cffe51508037e31c8230ffd4e4104ffe8410013fc6408037ffa9e4032ff18d42005eec2a1027ff52c8057ff21e4200bfd8142017788520823fd53c4001fe1082002bfd8541017fe84a08c
  | 3 => 0xeb264204ff58a4006ffa87080d7fd50908017eb202022ff54c2104ffac0108a3fd5048457fe29e4234ff8c24207ff8a508003fd20c4001fe10c8009ff90b210b7f8a8900a3fd5148419fea822031ff59641025f8c908003ff6050409beb2c4011ff94710015f8c89009bff53484097e3184002bf19221015fcc89080bff42500077f32c841dff14720027f8610802bff534405dfe18a8200ff50621037f88408002fd6408019fea8a2009ff997200bff8a29000bff43508017eb0c4015bfd8d20015fac921013fc5004001ff30a4034ffd4e4213ff88290827fc4288409fe2042009ffd0b21007fec52080bfd4350801de322421eff4c94005ff88288027ec429086bfea8c8434ff0c6420c7fa6510022fe6104009ff1062033ff19542197f860a106ffe31c8013ff3264002ff10642027f8400800afc64484077f32e4015ff8c52007dfacb0800efc6548411ff98e2035ff9424202ffa6208047ff51c4013ff2964000ff50410005fac98800bfe5490463fea948234ffcc24204ffa6590827de63084017eb142008ff10f101a5fac721036fd6384051ffa924225ff4c621017de8521003fd6250009ffb1c2000bfd8b10127f8a0108a3fd5248413ff2924033ff5954213ffca890813fc65840017eb102004fd84110105fac72000bbe5450855fe2844204ff58620027fa610808bfd3108467ff32a8409ff08420067fea4880cbff5350811ff9962002ff50e4004ffc4210027ff5290819fea922000ff50421025f8c40802ffe5444065feb1a8408ffd8f10197fca6a1003fe4184005fe2a28009ff18f20005bec68800bfc4050805ffa1c800fffd5210027f08120043ff41c40037e31a8408ffcc310027fcc31002bff63440057f3264009ff54a42007e8c2a100bfe5490801feb02840effd0a10027fec408003fd40c4067be32a8432ff4c142017faa920867fc5488011fe1962004bfd8c20017f88520887fc52900097fb2040039f19521007fa4308013fe10440137fb204205ff8c81004ff640900027f6550813ff1944200bf59021027fc6188003ff21c40097fb1c8032ffd8d42167f8a99080bfe4190005dfa1a8009bf1972004df8c488013fc3090013ffb264002ff50a41017fe84a10a3fd54484017eb264000ff90a10017fea8a106ffe43c803ffe28a8000ff18221067faa888027fb2088023fea86200cff19510007fac4a0873ff41c801bfe29c2030ff54e4116ff8a390827fc5208023fea8e2008bf58f10027fac320013ff6304013ff1904212ffd0c2018ffea120802fd6290411ffa9e2002ff55242007fa8490803fe62c40557eb2c4209ff94a200c7fc6310003fd4244005ff21a802eff58d41097fa861000bff4350439ffa064004ff59410047f8c788027fc630843dff18a8004ff1024000dfcc6a0027fc65c8009ff310202bff8c7
  | 4 => 0xafe64480073f3282000ff59310005fac9908affd43c8455ffb2c4223ff1042105ffe808800efe6550805da20a8207ff55010027da4010002fd6190001ffb224211ff14710145faca90803fe4148013fe90e4002ffd0d40195fac6a10c7fe509043b7eb2e402bffd0f21067feca8809fff404840ffea902002fe10140025fcc120003be42904097e3284006ff95010025fec708003fd6244013ff3064201bf18d210c7fa8710097ff6388413fe2944017ffd51200fff8a4a0027fd5208409fe32c4004ff94110147fca090812ff6404009ffb2c2032bfd8d42025fcc110833fe5144013fe3264008ff8c710017fe81210abfd528844bf69944200ffd9221007fa4290027ff630845dff1928235ff9464200dfcc790013fe1004023ff2962000ff4811004ffc8590006fe6348451ff28a4209ff14b2111ffca810813fc305006b7eb2c8404ff0c220197f862a100afe64440137fb2e4200bfd9310157fea51080aff645042bfe29a4009ffd8021005fac9100cbfe6350853ff2a44209ff90920187fe6320883fe5390013f71964031ffd4641007f8c5208a3ff6548463fe32c8209ffd8f20017f887208affc30c8411feb1e2009ffd82420f7fa60a0026fc64c8015ff9922009ffd0b20017ee8320802ff6244005ff21c8400ff58540135fac510803fd21880017fb024202ef10541055fac308003fd420402ffeb2a4000dfd9510007f84308013fc4050013fe1948408ff90f10015fec4a109bff31484077f32c8216ffd0920147fea290803ef6244015ff98a2024ff5502104ff8c32102bfc32440077f32c800cffd4510005fcc210026ff645084dfe21a422aff55221167f88190827fd32c8069ff98c8400ff1854204ffecb9080bf4419044d7fb1a4200bf5912004df8c4a084bfc3108009ffa802009fdc852100dfcc708026ff6390801ff10c8009ff10821027facb100c3ff3090457fe9864204ff592200affa6490003fe4188005ff20a8004ffd9640017fe832089bff32484137fb1e4005ff54c10004facb10003fd4288441fe18c8004ff59640097fca610003fe61500097e3204009ffcca4204ffcc010803fe41c8405ffaa2800bffd051001df8cb88027fe659085dff29a8226ff58d2113ffe8290827fc65c844dff9824230ff8c24104fbac610827ff6590861fe31c8200ff50110027feca10027fc5250863fea84821eff14d40007fa42a0026fc6508409ff102202dffd532106ffe8708027fc32484037e31a8200ffc8310007fac2a105bfc6448005ff2128009bf19021007fac12080abc6444021ffa06202affd42210c7f8a710027bc42508617eb1c8226ff8c12104ffe4290813fe4004039fe2a64018bf58e20027f8c808013fe3044005ffa0c8400ffc85100affec690067ff4288063fea8c822fbf59541007fec888013fe50c4013f
  | 5 => 0x8141107faa720047ff54c402f7eb2a4000ffd931004ffecb90003fe2148049ff2804204ff5842004ffa841002bfc434404bfeb1c4215ff18d20187f865208cbfd315082bfeb1a4000ff592210f5fec6a002bff30440137e31e4000ff48710025fcc108093fe510840bff9882000bf1854218ff8a32089ffc644843dfe18a8027ff1512104dfcc3108abfe5188401ff9022000bf58a40007fe208801fff5104009fe3282031ffd4a41147f8ca90826ff65c8009ff3202009ff5082118ffca320813ff5008001ff20e4025ff90e2104df8c790817fc4304015fb18a2000ff18142027fc801000bfc549081bff1942009bfd9421007fc8588063fc31880457eb184209ffd9021047f8a7880affc31c8451fe28a4201bf18d2019dfecaa1056fd6348005fe214802aff19621037fe820808bfc4308461ff18c8225bf98421157fea310812fc6304019fe28a2003bf9942102ffe6408057fd4348009fe2848022ffcc42111fee8210863ff4388049ffa884210ffd0b10097faa610027fe3250863ff2948200bfd894012ffe6310827f721884097e3244003bf99541027fe6008003ee214846bfe28c8415ffd0d20107fa632006ffd43c804dff18a421bffd0f2004ff84310097fc43884637fb2c820aff8c510017fa8320003df6344009fea002002efd0e41027fc4008027fe5248419ff2922009ffcc821027fec710017fc3204009feb1c4009bfd932108ff8cb88023fd32c403ffeb2a8005ffd4c1004ff8a59005bfe6448009ffb084033ef5514200dfcc690013ff4088035fe28c4004ff8c010007fe42080c3bd4390409fe31c8034ff8c642005fac89080efe6504013feb2e4001bf18d40117fe6010827fe5290809fe2044009ff1492015dfac790827fc4208001feb148209ffc842100dfcc6108bbfd3150401fe3122000ff0854006ffca708027fc3208447ffa084204ef90140007fc42a0027fc3288409ff3184004bf18121025fcc190827fc609085d7eb1a8202ff10941027faa008027ff218844dff21a4204fbc802004ffac721013fc3048009fe2804002ef10241117fc6010813fc648803dfe31a8000ffd894003ffaa20802bdc634405ffe282821effd8d40017fc8720827fe320804bff1844200ffd8520027f8819006afd65880077e32a8224ff5402101cf8caa1003fd4108001f69084212ff4c420057fc868801bfc41040077e32a8415fb8c92001dfccb88012fe6090813ffb0c8404ff98e40025f8cb08003fd644804bfea9c4202ffd024106ff863080abfd5088445f69904204fe84010027f88090012ff6388045ffa98421dffd5320087f8a988093fd51084617fb1c8209ff18f21017fa86a0012fc6588053fe20c4225ffd4e2104ffcc79001fff52040017fb0a401bff14f200dffa6190023f631c402bfe982402aff54621017f88721
  | 6 => 0x9fe3102000ff50620137f8c690887ff5290005fea0a8000ffd824104ffcc321027bf4290805f6212842eff0c941017fa84a08abfc5188409ff1804000ff50a1004ffcc39000bfc40908077f3284005ff8c41015ffa639087afd6350001fea0e4201bf98e40017fea9208bbfe3050405fa20a8209ff5832103ffca40809bfd3048405ff2a48004ffd9620005fcc310012fc6050809f79044002ff55142057fa608800afe64084197eb2a2009bf1972104ffac790827fc6008409f71024000ff90521027faa01004ffc41080097fb182004ffd4210147fea89084bff5308069fe9848400ff9051010ffaa520006fe6308013ff3048407bf59410067fea888026fe62040137f312202fff541410a7faa21008bfe3108413ff2904209ffd8321027fac4080bbff535044bff18c4215ff94d20027f8c310003ff624405ffea8a820bff99110007fec090806fe638844bff9844202ffd5242146f8ca90827fe3288061fe29c8200ff4851004ffca510827fd6590805fe20a8200bf98720007fcc0a0823ff43c405fffa92821eff8c94006ffaa708003fd6048413feb204202bf99221125faca1080efe65440017eb0c841eff58d40047fa87880cfff5050813feb1e4009ff9092104ffc6590813fe4084013fe3264226ff14d21137fec690803fe4244005ffa148204ff99610157fccb10847fc52c4015fe29a2011ff9971004df8c61088bfe4308409ffb142023fd10421127fea010813fc6590065fea9a8404bf18e201a7f8a72107bfe53500077e32a8002ff552400d7fea910013fc638804fffa124218ff94e200dff86390057fc3148013ff2144000ff88620187fa6520813fc30c4017ffa122009ffd8e42027fa6110012ff650806bffa8c8409ff548200fdfacaa0027ff5208009fe3142013ff9502004df8cb210027d650402bff31a402eff54d41027fcca1000bfd42900297eb284004ff58c10077f8850800bfe5450401ffb162030ff58e4117ffecaa0897fc638844fff3224200fec4110137fa6490813ff40040057e3222004bfd9640025f8c7080bbff6350409fe206201bbf58f200fffccaa0013fc5084001de3222004ff18e10007fa830802bfd3244001bfb2a4204ffc801001dfcca90813fe5004055feb2c4202ff15241025fecb08086fd65900017fb028225ffcca21027f8410808fff40084017eb04840dff4c610007fac1108bfff5050409ffb282009ff4ca4214ffe831087ffc6550041ff1948014ff55020027fa4008002f46150809feb184001bf98d4204ff884a1003fe2184013ff10e4000bf5911005ff8a88801ffe5104011fe9862009ffd4821015fcc988013fc30c8013fe10e4009ff0852019ff8a0a1013fe6190005feaa28205ff90c100277e81200a7ff40884137e31c842bff94f21007fc83880abfe50884037f3182004bf1
  | 7 => 0xc0b5c68bd0000d4850140100303180a0420000082601610c0180002602c03800004000000300180c01b00000a2f801091066000020062a4000731c500000c0b80000001d060090100c40380658c198001eb0001e80001000000c028940362340200011e18c0080300001c09003002000004971760042901003c0080b80900a07c1a8020b20048d0040621cc019570040000500100a00c0780200001c068010c200005275268270b413202c0001f0001780240002000005c0a0183720240200006400c298040005498a0ac004000011580c818c870130006580106800c0404d803062ab0028190180e80001b00c00400014026006b280001e058028001d40245e1ec3602700100e0000140001801836c0c818018014000720000880002e0000040981100012c00976018000000000180000006a00001407805030000098170029f0038010020082480001e0040600c018008000002de0c80d003000030000010000004000100e0186c8040380014705a00605c1c804004084110480040080280400805c3000002400c110010000000080504202c9903d05803c0402400e0002b80104200c6b02a0000081280000029c5e805074000018040020440400005000c00002000088010420000080203d00a00c0000602000400014004114000010ca35400523000039f286f000034030001400c401004006000e28250000a8c40000040140380001801002001000044001260107d40580800001c0000926a04c0c000050000590023161240180500004400016018004000a216649c030000000101000400c0b0001ec0c402cc1cf5002078028150266c854003bbc0280480603631c040520001bc000440550b01903e0020100303b04004c8580815a0140000700005c00011004090000000160003883201656c0300a0de00c0800a03c00c0809c008020040010000000226700e0043c8720c73900e80f032000028000060000687800017c2a00200c1441b86305c028050040021640000300c03c6900000003c009dd0020282600000001a488170020380c0030a200003005008028020000000e47c00000e000058000100000100d072418e300400633ff54942127f8a210827de63c8013fe3284229ff19221137f86090813fe6388013fe3064209ff14a42027f86088027fc6408409ff1004004ff54240017f884a0027fc4288013ff9904033ffd4942017fca8a100bbc4190005fe2048204ffd8640025f8c72000efe6548009ff9804023ff15021027f8a0a00d3fc3090809fe2022007ff1441004ffec390027fc6590813fe2164228ff5952104ffe4210003fc21c4061fe9848204bfd8810027fcc90809ffc4048401fe30a8000ff88710177fe60a080bfc4190001feb222004ff500200057ec888027fc320805bfe2864209bf1932114ff8a9108c7fe659040
  | 8 => 0x80121dc0300113c00003a110120080000c01c0080100000c008058561a27c00200100a00000002002000001080180000680100c0000c01c02e0044c81300c07c028220000101782522815c1a80700000826004006000010000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe5158f20004fd7598642007af641891001cfc75d8520004ff7318540006dc4158c211deec201852009ebf4359020004fd7558b1004ebf7459321006df7358221006dd6350421026fa6018141004ff765052028fb642d854223edc4058f20014fe74587202067c10d9510004fd7359020014fe76d9120004ff71592200ccff72591200067c30d9521014fe7458910226ed6308620014fe74d8520004bf7458420277e75148421056dd10d8d10004fd75d8941005f771509200047f755911004ef721987200067d71d9542006ef74d8910006df6350110006f570d8542196dc635091004efb205802105ebe7619110166f443d8542006de7158c21006f55198420007eb724401000cfc739842024edc42d8d40105de7308640006bf7458420005ef7250620006bf64485102ee7f43d95420067f72d9521026ef7258a1001cfe75582422c6bf6390541006df63085100e6be5459320014fc74587200063f65191100073c6519121007e87244010004fd74d8b10296b44218542006fa5058021006ed73d8910006dc7558f200067f6590521004ff7398420016bc649052104cee76d8910007b554d8542004fd75987200075c65d8d1004efb2058321005bf7448620006df5158c210067e325941004cfc76505210067d32d9521006bd71d9110006f74158620026bf7459010006ee63d8910005dd7398910014fc7458910007bb64c4110006bf30d91210b6bc54d912000cfc7359120006ef7259121025fa7090410004ff7058910005f671c8110024fc705901004cff7690810006bc75d9110004ee761891004eec2058021004ff7558a4104edc5258c2104ef42198720004ff70592210067e31d95100077631d95100067c65585420067d659081004efb70583211ffba7090640006ee631891011fe74218542004ff75986201f6bc4018540004ff7458b10166f640d85420067f70d9542006f550185420066c65d891004eed711891005ebf43d91100067c63d9510006f431185200067f7559121004fc715912004dec7250320004ff7558810004be761912123ede7058f2004cfc76507200077465d85420067c315941004cfd7688410005f970c8610005f4715894000cfc7359220006dc63989400267d3059620014fc74584200066c6518910006f96018142296be42185420067765d8542006f47018542004ff705864213cff7459121004ff7558242006ed31d8910006df63d8540004ff7358321006dd73d9310005bd74c8640006be70d9121005fb7050a202367f21596202ee7d42d9542004fd76c86401ffb410d9110024fc7058a41006ed71d891001cfe7518540004fd7218540006ec74d891004cff76c86402bded73c8621165f77158941006f46188520166f643d85422e67c32d95420fd7c7548540007af6488521006bf50d91210067c6518121
  | 1 => 0x81210047f7558910006bf6498910006ee32d894104cfe721854005ebe64d9110007776518542006df52d8d1001cfc75583210057f7548520004fe71d8142006dd635032004dec725042004eed7418910006dc6318940024fe70d894101c7c75584200f5dc73585401febe10d911028ef774d8542006ef42d891014ebe64d9221015bc7448640006dc51d8d400067f73d95422ae7c20d9521004fd73d8941006ef50d891011ebc6408510006df7458c2104efb2058242006ef5018910025fb7144010006dc63589100067c7558420014fc7498620006ed618842011ebe5459021005f9708852005dbe76d91100067e43d95210067d72d951014cfd74d9221256be42d9221024fe7690620004fd759864000cfe7358241006dc7558c21285ef7348421004ff7559121006f65198640006f76198540024fe70d9221005df73503200067f74d9521256be32d9121006dd63904210073c651911004edd7258c210067e3159620006ed6218940004ff755922001cfc7558021005f471509210067c6598121004ff7558221004ff755842001cfc7558910016bc64501100057d759891001cfe7559210006ed618862003d7c754841013eee4258a4105cfd70d9110027f371440100267c10596200067f7558642016be6450610084ff7650410004fd72d931001cfe7598620006df63c851001cfe7558b10006ed651891001cfc7558620004ff76884102ef3c74d9542014fe7458810166be5459321246de10d8d40024fd72d912012ddc7358221006f731d8542005ef7250320004fd73d911024edc54d8d4012edc6388540006bc53d9110006ee7618910045de7308710005f77150b10006dc73591100057d7518241014fe7458a1005ebc42d9110006ed65d8910006de5458f2004edc7258f20006dc7358221026f6105862005ebf40d9110025fb76440100067f75591202e67c42d954224edf70d8d4014eee42d89410069c63d9110005dd7318a41006bd6450320006dd74d8d10006ed62c831005ebf41d9110006dc72d8d10004fd755932011ef74318542006bf7459120007e97088620006bd54d9121006bc31d91210aedc63481100067c65985420067f655092104cec7259110077b4419814124edf41d8d400067c73d9542024fc7650610246de50d8d40004fd73d8142006dc63985400067e7459620006f76198142006bf53d9110026f67198640026f6105842001cfe75d931003e7d7159410004fd7358221004fd7398420007af64d89100057f7550921014fe74d8121006f67318542014ff76505212ee7f40d9542006dd71d8d40006de7558c21005df7358221004fd755922000cfe735832129eed6388521006bf6488521166bc40593210067e74d9521026bc4059010016bc645092105ebc64591102077410d951000cfe735802101cfe7559220006d
  | 2 => 0x4edd2058c21006f53158420004fd75d9310006ef6288510025fa7008710024fc7059220006f53158620006f671d9310006bc6458121006dd50d8d10076bf435921004eee62c8310006f65018542006dc63d894011fb65418542006ef73d8910025f87050a200057f7548710006ec65d89100067c70d9542006ec65189100067c64d951013ebe64d9121006bd43d911018e7c65905101efd410d8d100067f40d9510006f765d85420067f70d95210067e73d95420076f6518910004ff7558a1000cfc73d85421e6ef6388620006ef7259120005f9708871004edc2058c21004fd7559210006ed62486100067f4359620296f77418542006df65d8d10295f67190721004ff75d9110005df73581212ee7d43d9542056dc71d8d100067d7359410006bf64d8121085bc7448710005ed729062104cff7658b10005f47150a10005dd7318b10006f66150420006bc51d9110006f7715912009ebf415902000cfc735922104fe4215092101cfc75592100067f6548510004fd73592211eedc10d8d10006f671d8b10004fd7688640006dc7358910006bd51d9121004fe71d894003e7f715941005cfd7690610004ff7650620166f440d8542006ef30d8910004ff765072004fce6348421005bd7408540055dc7359110006ef30189100067f43d951004edf2158f20004ff745842004eef7018910006ed72d92210067f6558121006ed7688420005bd749891004eee7018910006df635894000cfe731854011cff765062100cfc739864005ebc54d91101e6ec70d8910006bd54d922104eee62c8610004fd739864201c7c755864000cfe7398420014fd715901001cfe75986422ee7e74d954217d7c75581410077b65c4110006bf72d91210067c43d9521006dc7359120296f44218542006f77018542004fd764864000cfc73987200069c64d8d10006bd4359220006bd75d9110005df735814100cfe73d85200f6de76d8d4004edd4258c2104edf7258f20006f773d8542006f45318542014fe7498420006de52d8d40006de72d8d4011ef4715902101cfe7559020005fb7050610166bc64c8510004fd735901004eef6388420006f675d8542006bf54d9121025fa70086400047f75591200057f7550a10014fe71d9110004fd7358b10006f563d8542007e54148421057d471d8d10004fd7558321006ec75d891011ef67418542006bf64c81101ffb610d9110006de73d9310004fd7518540025fa70884102479e40d8d401febe50d91102e67f20d954217e7c6550510024fe7059010046dc63c4110005dd73c8110004fd75d9121004fd7358a40006f7531854204edc2158f202067f71d9510006f76118142246dc50d8d40045de7318b100addc7358520166f572d85420057f754864001cfe7558642056de76d8d10007e6414842104eed7518910005bf745
  | 3 => 0x976c4210004ff7358a41004fd75d85400267c3059410004fd755824200cfc73d8141006bd31d9110076bf4159210004ff75d9121004ff70593211e5ed708862004def71484211e6ee6088420004fd70d8941006f450185420067e64d95102d5bd7390a41006bf74592210267d70596200b5bc74485200057d75981422067c70d9510006f775185422367c42596200067e63d952101cfc7558720006f470d8542004ff7358810004fd7559221006be65d9121006f830d81210067f415962001cfe75d8910026f6719842001cfe75d9120005dd73087100067d65904100067d32594101f7b4101911001cfe755872014cff76904210067f6598910004ff73591210f5de7308540007ac7448421006bf51d9121004ff7648540004fd7690a10007b531d911004cfc72582412077610d951004cfd72590201457c755912111ef5431854204fac4250a2001c7c7559120296f43218542055de7308510024fe7298720014ff7650320014fc745802114ebf42592212067e10d9510006ee73d89100067c40d95210b6bf42d9120006df7158f201ddec7048421004ff7458321004ff73d91101efd771d8d10006f575d8542006df7458f200067c7559120006ee32d8910256bc72d9121006bc32d9110006be53d9110014ff7650a2001cfc7559021024fc7608410006fb7058910296f720185421267e65084102ae7f71d9521006f66190420256bc52d9121014fc765031000cfe7359310004ff755911004def7008620024fc7650a20016be6190a411eedf71d8d10006ec52d894101cfe755922104eec62909100067f6558142005f77150910006bd4359020006f45118542006f530d8542006dc6359110024fc764852019e7c6550910024fe7688520004fd7498720024fc7159310006ef6290910006dc63d9110006bd651912101cfc7559220004fd7650910006bf65191101467c71d9521006ed54d891011ef454185422e67c72d9542006dd75d8d1001cfe75d85201457e76d9521006ec31d89100067c4159410006be52d91100065c63d95100b7b44150520006f66108640006ec311891001c7e75d9221004ff735891004edf5258f200067c42d95100f6dd70d8d40005dd73086400076f65d891009fb4415042000cfc73d814204cfc7258242024fd7608710006ed54189100067f41d9510006dc65d8d400067f31d952104eee621894128ef672d854200cdc7359120006f44118520166f540d8542007b63119110006bf6319121006bc6319110164ff71591210067e30d95210067f72d95100067d6548620004ff73d81410e4ff705912004ebc425902004cfe72d9110004ff7358021014fc74588101febc50d911000cfc7358b100067c71d95420067d6550410006ed70d8910006df7558f20014fc71d911004eec6288510006f732d8542005fb7048520
  | 4 => 0x710004fc7159320016be6450a21024fe70185421ffb66190640004fd735872008e7c65c4110006ee32582211febf64181410057f7548510006ed6288710004fd765042001cfe7559110006bf649052104fcd6348421014fc745822101cfc75582210067e71594100067f63d9521004fd76481102cebd6590541004ff75591200067f73d952111eb441590212ae7c21d9521006df41d8d10076f541d85400063c65191210267c20594102479c40d8d40006be631912100cfc735824124edf42d8d40006df50d8d40166f654d854204edd5258c21015bc744854001cfe75d91210057f7548540005ef725854001cfe75586401deef620861004cfe7690421006bd32d9121295f671904210076f7548421006bd75d91210067f32d952100cfe73592100067c655891004cfc7690b100267f405962001cfc75586400067f755864015edc63c8510185de7318a41017b67190640007bb7444010004ff7458021006f653185420067c32d95100267f205962001cfc7558420006f531185420057f7558941007cf63d891000cfc73d89410067d43d9510006df75d8d40004ff7398620006dc4058c21006df40d8d101febf6490420014ff765931001cfc751854004fe67108620004fe71d9120006ed32d8941004ff7558a40006f661c8640006f6319864000cfc7358640007cf6318910006bf72d91102ddbd7590a41024fc70586400667e71d9510076bc4259210004f77159120116df7158c210b4ff7459120006f830d8142004fd74d891001cfe7558321025f87048620006f63198620006ed6218b100067c65d8542006f751185200067e70d9542024fc70d911001cfe75d8141006f751d8540006f752d85420067d655081004eee6218a4101cfc7558a100067e7259410006be63d91101df6d6508620006f46158142004be761911004eee6218940006df6348510084fd74d9310006de5158c21024fd7058810004ff7559310006f431d85202f57e76d9542016be6490621006ee65d8910004fd7559021024fc7650620006ef54d891007d7c7548610006f5515864028ef472d8542055de76d8d100267e1059620004ff7558910004fd7418520007db63c4110004ff7359020006ef5418910024fc7058620296f6521854201cfc75582410067c65d8142006dd5058f200be7c65481100063c65d9110006ef725911005efa4058241024fe7098640116dc6308510024fd7690710006ed51d8910056dd71d8d10006bf645052100cfc73591210067f65c811004cfc7259321004fd7558642006ed511891004cfc725921000cfe7358a10024fe70986420f6dc6350110006ee65189100b6be64d9120006dc64d8d10024fe70d89100067f735962016e7e65c841001cfc759864213ebe71d9121014fc74d8520087b4415071013ebe5458a41006f76188520025f
  | 5 => 0x6ec41d8910004fd75d81421457e7598121024fc76908101467e6548620005fb7048510024fc76505100067f73d9510006dd72d8d10006f673d854201cfc75d8b100057f75585420267f105941008d7c7550b10006f631d8542006df4058f20006df6388540256bc20d9121036f541185400047f75586400067c65d9110006bf70d91210069c6319110006de64d8d10006f77318542016bc649061004edf7258c21006bf54d9120036bf4318540006f56118520025f8705051000cfc73d8520036bf4359010006bf75d91211557e75d922104ebc4259320004bf7458910004fe7688540024fd74d89402367e725962001cfe75d81422ee7f42d954200cfe7358420176de6350720005ef725042001cfe7558a4101cfc75d9221004fd735864205ef54158640024fc7058642006df63c8110024fc7059321024fe70d91100e6fa40d814223edc1058f20005ed76c86210067f6518542004fd755822114ebc4159221004ff7358a4001cfc7558242007ac64d8910016bc649052000cfe73d922104efb70582421eede50d8d10014fe7690621005fb7050920026f77158640006ef511891002dde7308410004fd75580210077531d95101efd610d8d100cebf4259220006df639891013eed4258a41014fc765092105fb44158141004ff7358241005dd73d93100067d43596200067d74d951004edd2158f200067f6558542004fd7690810076f641d85400067c43594100067d31d951001cfe75590210067d30d9521006ec52d89100067c63d9542014fe7498620004ff7359010006bf64d8910166bf4359321005df7358142026ef7258810004fc7648540006bd435921000cfe7359020006bd65d9110006de5458c21004fd75d894000cfe7359010006bf64189102ae7f21d9521055de7398910004ff7458a10246de20d8d4024fdb40d8d400067f651812101cfc7559020004ff74586202367c32596201eede10d8d101febe40d9310006ef629894004def73c8621004ff75d85400067c75586420e6bf4059320024fe7059020006f550d854214eed42d89410bd7c75509200267e4059410006dc42d8d1013ebc6448510296bf611912111cf471590210067e4359410024fc7690410004ff75d8121006dc7458f20026fa76c411004eee6248610005f77150810025fa700854000cfe7398620004ff769062004efb70580211febf6390640006ef70d891004eec6288540007b864c4110006bd52d912101cfe7559310004fd75d8910004fd73593200267d2059410034ff7650710026f41098640005ef725911004eec6208610006bc641812105dbc744851013df57198941006df6398940055dc7358910006f96018241006bf7459310004ff72582411e6ee20987200067c7359620006bc30d912104dec7250721167b44198941006f96018141005f9709
  | 6 => 0x3144010006bc651912121fe44108620006bf70d9110004ff7518540025fa700841005ebf42d9110045dc73503101deec301891023ede5058f20006ef62905100057f7550a2100cfe735881004ebc42590210067e31d9521006bf648851011ef74218542006f75018542006f7311852004ded7688420006bc65d911014ef541986420067d72594102067e70d9510004fd70d85420067f65981210073f65d9110005ec7258141004fe76905200067c651814204cfe72590210057f754841001c7c7558b100067e63d954204fe77148421006ed52d8910006dd7058c210067d31d9542006f57018542006de52d8d100bd7c75585201febf6490610006ec62905100067c70d952104cfe72d9310006ed32d8910014fc74185200e6bc64c8110006f66318542006bf6458121006f47159120186de6390720006bc6498121005f771509210067c755911004cfd7690621035bc74484100067d73d9542006f66148620004fd7398620006fb6098142036f6411854000cfe73d894113ebc43d91210ceee42d8940006f751d8520004fb7644010296b642185421eedc50d8d101febc40d9310006bf645092101cfc7598720004ff73d8b100057f7558141006df735911011ef441590212e73c42d9542024fc7058a40006bc6498910006f761985200b5bc745852013ef6415864204ebc42593211f7b6101911004eec74189100267e305941005cfd76501100addc73501200267c4059410004ff73d854011fb4415042100cfc7358321006de74d8d10024fe769081005ef64158640006f5611854204edf2158c212b7e551c86210077b7544010015be7190541004ff73d854204cfe72d8540024fc7650a10006bf30d911000cfc7359110006f46318542185de73d8241166bf41593211f6bf6119110014fe74586200067c655911001cfe75d85420067f30d95420067f3159410006bd65d9121116dc7158c21006df6398540166f743d85420057f7550a20006be43d912101cfc755912004fea608842004edc4258f20006f75118540006be75d9121006ed63d8910004fd70d9121004df7358910005f5719814204dee7188521005bf7448640007ad6290a4101cfe75d9221006dc51d8d10006ed6318910166f4415932111ebe54185420047f7558642014ff7650a210067e63d951004eee329872001cfe75d8b10006ec62505100067c74d9521004fd7558a4024edd54d8d40005bf744852001cfe755862004cfe7690720006f561886201e6ee20d8b10004ff75d9221016bc6450920004fd7558810006ef51d8910024fc725872004edc2158c21006dc54d8d10024fc70590200067d315962005cff7459110005f47148310006746518542006ef6250510006f65198420006bf50d9110006ec41189100067c6598142005dd7308540005dd7308510007ac6418910
  | 7 => 0x8420086bc415931004cfc72586420067f42d951004ebe4259020005dd73084100067f3259410026fa6018221004ff73587200267d4059410004ff764864023edc5058f20006ee4318910004fd7559321005f47150a2104cff76483101bff1514401011fb44118941004fd7690520026f6109864000cfe7359221045de73d931001cfc75d9310024fe76c864004eec70189101febf6590640006fb609812100cfc73d9221004ff73d8142006df75d8d101e6ee70d8910006dc72d8d40024fd7688710006df63d8940136dc63485101dded7608620005f77150310005f77150a10006dc5158f20004ff75185200073f6519121005bf7448710006de7158f20256bf71d912100cfe7318520006bd5459020004fe76909100065c65d8d100b6bc41d91200067f715962004ef4219842001cfc759862019e7e76d9542006f4751854204eee628871011ebf4059021004ff73d8940167b654d8542026ee2058a4013ebc40d9121006bd43185401fdbd7090640006bd72d9110004ff75d8520004f47159120024fc7058810005dd7398540004fd74d812100cfc7358a10014fc74d8b10006bd6450a210657e76d951016e7c65c85100657c7559110004ff73986421cfd863c41101fdbe7090a41006bd54d911000cfe73d9110006ef629894101cfe755932014df67118a411febe20d9110025fa70c8510006f5515842004eee7418910014fe74d8910006be32d9110006f74198620006f57318542297b44218542006ee75d8910006be51d9121006f453d8542004ff74589102e67e32d9542006bf63d9121006ef6250910004fd765062005fb44150510005df73591100b6ee4258a40006bf6490910004fd7358a4100cfe7358242006df4158f2004ebf7459021006bf31d9121006dc5458f20006ee3258a4004eec6250910004ff75d894004eee6218b10006bc31d9110006be30d9121025fa76c41100fd7c75585401e5ee70c8621086be64d931000cfc7358810257b57190a4124ede42d8d40004fd74d852000cfe73d9121006b5541854200cfe73d8b10006f73018542006dd72d8d40004fd7318520005f47150a2004cfe71d89101df6e6508620006ee32d8b10024fd7059010246df74d8d400067f65d8910006df63189401267c6508510006f753d85421467e76d95210067f6518910006dd51d8d40166f77159321014fe7458420005f97088410006ef7258b100067e73d951004edf5258c210067e75d92210067c755891000cfc73d911001c7e76d9521004fd73d91201467d71d9521006bc74589100067c31d95420067f71d95420073c65d9121296f66118a41004ff7650a101e6ec30d8910004fd75d8b1001c7c75591210067e735941004edf2058f20006f441d8520026f41098620166f740d85420fe7c6550110006f473185421467e65484101b7f
  | 8 => 0x24edd41d8d40006f5511854204eee6288410006dc63989100067c31d951000cfe7359321006df6318910005f9709041013dbe74981210067d7459410005dd73d8241006bf32d912111ef7541854224edc41d8d40006be73d91211febc40582410267f305962014cff7650421006dd65d8d10006ed75d89100d57c7548620006ef62c4110017b67190541014fc7458a10004fd75d8542004fd7690b100267e2059620006ef6318910004fd7359121166f543d8542167b4415072128ef432d8542007b97090640004fd73d8940006bd6490621004fd73d8141006ef63d8910006bd64907100067f72594100067c75591210067f6588510024fe7650a100047d75d922100cfe73987200063c6519110005f4715031001cfe7558021006ed62884100667e76d9510006ed62189100063c65d9121024fd74d854000cfe73d8540006dd7558c21006ef725891024edf54d8d40006be63d9121006dc71d8d40006ec52d89402a76c658852101cfe75d9110004ff7559021014fe745802103e7c71594100e5fb705894014ebe54d9221045de73c8310025f870509200067d65c8410255bf7590a410057d7518141006dc52d8d40005df7358540006ef628854004ef77158642006f451d854223ede1058f20006bd43593210079f64d8d10006bc6319121004ff75590100267f7059620006df51d8d4001cfc75d8121006bf649052011fb44108640166f454d8542004ff7690720297b4211912104ef72198420006ec43d8910006dc6358540135dc7358121004ff7558640015be71906401e6ee40d8910005df735912004eec624811005df970985400267d3059410026ee2058a10004fd76c8540004fd75582412af7421d9521006fb609824101cfe7558a100d67f72596200067c63d9521296f632185421467d21d952128ef720d8542006be65d91101deee401891006dde7308610026ee205881020ff151c4210005dd731894104fce7308620007b531191100067f4259620004fd73d854000cfe7398642007e521084100f79c74d8d40006ed74d891013ebe54d91210657e759891004cff71588102ee7d74d9542026bf7459020007cc63d891013dbe76d91210067f30d9510006bd4359010004fd72d8141007db734401001cfe755932105dbe7498910005f471481102067e20d9510006bd51d911011ef55418542006af64d89100067f65985420267d1059410004fd735802104ede5258f200067e70d9521004fd7559010037b4415041001cfc75d8941006ed325822104cfc7648110006af6418910006ef6248110006bd70d91210067d70d9542004fd7608410006ee43d8910006dd5058c210657c7550910006bf54d9110004fd70d922104dec72505210067d65084100067f43d952126fe63148421006f43118542026f61098620007cc6318910004fd749
  | 9 => 0xd6519110006bc64d89100267c10594102367e3259620006bf645051018d7e75d8a410067f40d9521006bd30d912104ef6719872005ebe71d9110004fc715824203d7c755081001c7c75586420066f65189100057f7559120005f771483102ae7f20d9521246de70d8d400067f63d95420f5de7398540005f771501100067f75589102ee7c41d954204ef42158642006ef64d891004def7648421006ef6298b101febf71d911004cfc7650721004ff73d8121006df4058c21006f531d8542006f6319842000cfc73587200cebc41592202367e4259620004ff75d8941026f761c4110006be43d9120026f41098420026f6719862004fe67188420006f76108540024fc725932001cfc7558b10006bd73d911001cfc7559121006dd52d8d40006f7715891004eef7518910006bf6450920074ff7159110016bc6450120006ed6108620006df42d8d10004ff7559221014fe7498720086bc6459310004fd7398720014fe745822113fb44150521006f531986200067e32d951015edc63c85400067c3159620006f5319864004cff769091001cfe75d8121006f56150420006f650d854204ede7258f200657c7558910256bf21d91211567c6588521024fc76c8510006ef31d8910006bf75d911005dbc7458910006bf51d9110004fd7690910004ff76886400047f7558b10006f7615814204edd2158c210057f7548610004ff75d93101deec4018910004ff7458221056dd70d8d100067d71596201e6ec40d8910257b67190a41024fc7650810006bf64181210067c73594100f5de76d8d40004ff7158a40014fe7458321006ee3258810006ee51d89100067d6588620006ee511891004dee7290621006bc52d9110024fc70185201deee3018910075bc7448610006f67518542006bd70d911004eee6290810014fc7458321006df50d8d10006ef31189100067e31594102e67e72d9542025f671c4110004ff72591100057f755814200cfc735891000cdc735911004cfc7690910005ed729042128ef652d854200cfc73582421e6ee30d8910006ed32987202e67e42d95420067f7359410006ee3258a10024fe70588101e5ed7088420005bd74981210dedc63c811000cfe7358a410057f755852004cfd70d9120025fa70886200f5de7398940055dc7350110005bf7448510004ff73d9120004ff7558642004fd7358242007b87444010016be649071001cfe7598720167b441c8640006f671d92210067f65909102ae7c42d9521116dc6308540006f475d8542006de65d8d40006ec431891001cfe7598640166f474d8542006ed62908100067f41d95210067c74594100067e74d9510256bc21d9121014be76d9110004ff7058a41006f450d8542256bc4258a4114ebc6459221005df7358940006be6319110006f77159110006df63d8910006ec62c4110
  | 10 => 0x401001cfc75d854004eec6208510004ff7359221004fc7650b10006f770d854200cfc73586200addc7359120006f761c854019d7e7598542006ef62501101febc30d9110024fc70592100076c65d8910006ef32d8910006ec62501100076c651891011ef5411854204df67188521006f46518542034fc7159010006df6390910006de5058c21004ff7059121006bd6450a200067c30d9542014ff7650610004fd7558640006be72d911000cfe73986400067c6559121077b44150610004ff75d8b10285ed7348421055de73c81100067f65d8542014fc7458b100067d43d95210f6de6350320006ed32d8b10246dc20d8d40004ff735932004cfd7158810014fe76d9110006bd52d9110005f9700864001cfe7559121006df5058f20006dd54d8d10006bf6490510056de71d8d10014fc74d8121006f960181210067f755911004fcd7308620006bd32d911004eec209872022eed6388620005dd7308610006f56108640256bf64907212ee7e41d95420067e71596200067d32d95421c6fa6144010024fd71d91100ceed42d8940005f571c8310006ed3258a40006bd6450420004ff73593212ae7c32d952119d7c7558142004ff7358b10006f65158640005fb7048610006df72d8d101467c6548510006df7558c21296f64218542024fe76904200067d73d9510006f731d8520006df638851011ef7401854201cfc75d9110017ae7290a4124edd42d8d40087b441d8141004ff75d8142006fb609814104dec72501200063f6519121004ff75593201d77865c411004cfd71d9121297b72119121016be6090640016be6490720006ef6418910024fc7650920164f771591210067c65d9121025f87050610006dc65d8d1000cfe731854204eed76c862104ef72158642006bf52d912104ef82058021006be31d9121296f4521854204cfc7259021024fc765042004cfd74d8142004fd7558a41006bd6490a100067c73d9510006ed64d89100075f65d8d101467e71d952104ebf7459320025f87048520006ee54d8910006bd64906200b6bc43d9120024fc70591210067c74d9510014ff7650310006de7558f20006ed641891000cfc73d8121006ee5418910006bd63d9110007af7448421004ff75580210267d7059410004ff725921001cfc75d912104edc4258c21004ff7558321004ff73d93100073f65d912100cfe73d854204ef8205832124ede41d8d40006ef52d8941005ef72507210067c715962000cfc7318540006f56118540006f56190420006f653d854200cfc735901028ef76198941195dc73581420067c7558b10005bf7448540006df4158c21006bd54592102ee7d41d9542004fd7358620006bc6418910004fd7358a10006ed6248310084ff70591100066f65d891001cfc755901004eee60886201eede20d8d1004eec2158420006b
  | 11 => 0x4fc71592201deef63086202e67c20d95420057f7550920004fc7650520006bf6450910014be76d9121004ff7558b100067f65505101cff231c411011fe44218542006fb6098221006f63158640005ec725911028df771507210067c65d81212367c725962004eee7318910024fe7018520016bc6490910006f461d8142006f76318542006f663d8542006be43d911004eed7018910006dc5058c211febc20d9110006df7058c2100cfc73d9120006dd51d8d102ee7e43d9542006f750d854204ede2158f2004eec62c8510005df7350310016be6450721006f43018542006f6761854204cfc7159221006cf63d8910026be4059220006bc65d9121006ee74d89100067c41d9510277e45148421004fd7650a10006f565185420067c73d9521004fd7398640006dc63d854011df671d8a4117d7e7518141006cf63189101b7d873440100b6fa4058242006f552185420067d7459620004ff7359110004fd7690620006bd71d912104ede2058f20006f66518542026ec2058a4000cfc73d9310004fc7159020004ff7598420006df54d8d10014ff7159010004fc7688540006f77159121006f4614852004ebe4259320004fe768851004cfd74185422e67f74d954204cfe72d912004eef7318910006f463d854204cff7690a1000cfc73590200057f7559110006de65d8d100067d6548410024fd74185401e6ec20d8b1014ebc64885101457c755092100cfe73582212b7e651c86210067f74d9510004fd751852001cfc75d9120036bf4259010005f970087100f6de74d8d40004fd73d912101cfc755931028df77150421004ff75d8910004fd75d9221006f461c8540006de72d8d10006bc651911000cde76d8d100bd7c7559120006bd5459320006dc5458c210667d71d95100267e7059620006bd50d91210057f7558540086bf43d9310006bf73d9110005ef72501200067d31d95210073f651911004ef82058242005df73501200057d75d922104edf4258f20296bc421854201cfe7518520004fc76509100667d70d9510016be6490421006ed3018910005f77158142005f771591200057d7598121006bd53d9121024fe7690a100067d63d9521006f561c8640006dd65d8d400067f435941004cfd74d854211ef474185420e7b4415072001cfc75d8142006f751185422ef6c42d9542006ec72591100b6ed4258a4001cfe7558420024ff7059010006f441586200267e7059410006ef6298a41006bf6498121004fd7608640005bf7448410246de40d8d40005ee761891029eef6388521006ed1018910005f471501100067d735962001cfc7559320017b76190541006bd6319121007e52108610026fa6018142006f960182211e7e561886202af7721d95212ae7c72d952104edf2058c21006ef6208510006f46108540004ff73582420277a654
  | 12 => 0xe2018520006dc74d8d101dded70086201e6ec10d8910006bd6450310017ba609064013ebf40d9121006f66188620006ed6218941006dc52d8d10006ee3118910006df65d8d40005f47150920006ed3258a1000cfe7358b101e6ef621812100774651854213dbc74581210067d725962001cfc75593210067d75d9221006f775d85420079c63d9110004ff7559210004fd7318540026ef7258a40005f571c811004ebe425902113ebf43d9121006ac64d8910006bf64c411000cfe73586200057f755891011ef64318542006f65158420014fd7690421006dc6318540004ff73d912126fe53148421026be405902004ef421587200057f7550b100057f755894000cfc73d9121006ef65d891000cfe7359121004ff7158910006bf64501200067f745941004cff7648610006ed53d8910006ef65189101557e7518221026bf7459220006ed5318910004fd76508100267e1059410006ac641891028fb442d8542086fa40d8141004ff7398640006be6519110027f26144010006bf6458910004fd7298640257b421d912104eed7318910006bc63d9121136dc634854001cfc7558642006ed3258810006bd5459021246dc40d8d40005be76191210067f6590510006f730d8542006f670d85420067d32d951004edc7258c21006dc75d8d4004ebe42593211ffb561906402ee7c43d9542004ff7359210026bf745921013cfd7690721006bc75d912104eee751891017e7c65505212e73e42d9542004ff735864201cfe75984200067d6550620004fd75d9110005ef725052105ebc43d91100067f65d8142006dc63d8910006dc6318910024fc7058a10007e631d89100067c4159620006bd5459321007e63118910116dd7158c21006de71d8d4000cfe73d8121005f77150a201567e65886200067e72d9510004fd75587200067c4259410006de51d8d40006f74118520026f61098420006ee31d89100067f7558b10006ef52d8910024ff7058810004fd755842014fb441d8941006ec63d891004ef72198642004ff7598720004ff7648410006bf6519121004ff735842000cfc73d8940024fc7690a10006ec631891004cfc76c8540004ff7558720004fe7650520006de7458c2104ede4258f20004ff759864000cdc735891004cfc7690421006bf6448110246dc70d8d400067f41594102ee7f72d954228ef442d8542006f630d8542005f771481100ee7c65c8110166f742d85421febc70d9110006ed30d89100067c65989102ee7e40d954201cfe7518542006f53218542004ff7158242014ff7650110004fd7518542004ef725911004cff76481100067c64d9521006ef62c8510025fa70c861004ede5258c210dedf7058f20005ec72585400267f4059410006dd5458f2001cfc75d8940014fc7650110016be64504200067d63d9510004fd73d9310
  | 13 => 0x8142006bf7458910006dc7158f20014fe741852000cfc735932112edc638851011ef64018542006ee321852019d7c75585420cdbc7448620006f57518542004fd7098642006f573d8542007b554185421457c75581210067f65481100063f65d9110014fc7458620004fe7650b10014fe76d91210067d4359410026f41058640004fd73591200f6dd40d8d4000cfc735822100cfe7359220005df7358520005f47150b10004fd73d8b10004ff75986420075c63d95101febe70d91100067d6550a200067e73d9521014fc74d8910006bd43d93100267c70594100067f651814200cfc7358021024fe7608410024fe7608640005f97088620006dc75d8d1013ebc41586421ae7e6590810005bf744861004dec72506200067c32594100067e43d951013cfd72d9121006bd6450610256bc42d92210067e71d954200cfe73590210f5dc735894000cfc7359210004fd73592200067f70d9510007ac648852104ef7215872000cfe73587200076f658852120ff251c4210004fd7359210256bc6290541006f67018542004ff73d9221014ff7650721026ec20588102067c20d95100b4fd7650120006dc5158c21004ff735862001cfc75d8141014fe7458b100067f42d952119d7e7598142016be6450310004ff7159320006df6350510006f4511852018e7c65905211bff2514401028ef632d8542257b721d91210067d73d9521006dc41d8d102ee7c40d9542006be51d9110296f42018542005f970c8510025f870485100067765185420267c305962004cfc7608540004ff7558620004ff735822104dee71886200067f655912128ef642d8542005bf745852011eb65418542297b64218542006ef764842111ef542185421febe30d91100067f31d954211ef443185422ee7d72d9542256be72d9121006bc53d912114cff725912104eee6250810026ec2058a100057f755912117d7c7558941006bd73d912104eef7118910006bf31d911004eec62085401567e65884102067c30d9510006df71d8d40004fc7158a4013ebf41d91210067e30d954200cfe7359120296b7611912104eef7418910004fc7690520006df635854001cfe755822107d7c7550a1000cfe73d8940006ed50d8910006f431d854201cfc75d85420067d659062024ede54d8d40004fd75d8121006df51d8d1013ebc6459121006df5458f2004eef61885211e6ef71d8910166f554d8542004ff739872028ef76118941006ed50189100067d32596201dfe410189100067f65509101e7e410d8910006ed6250810006ed6208710004ff7518542004fd735881000cfc73d891004fe661c8621006bf53d91211b7f331440100267f2059410006dd5158f200079c64d8d10006bf63d911004eee62483101deec101891011ef57218542026bc40592200067f6598142005f77150a211dee
  | 14 => 0x73c65d9110006ef40189100057f7550910006bc73d9110256bd6290a410067c4359620006bf640851004eec628861001cfe75d8540004ff7359120166f772d85420fd7c7558940004dd73d9310266bd6590640004ff7358a10006fb7059120006bf6450110025fa7088520006fb70591100067c31d952104ef72158420015b67190541006dd6350720006bf32d911001cfc7558810006df6350910006dc4158f20175dc7358141004fe76085102ee7d40d95422cebf65905410067f32d954213ebc54d912101cfe7558810006df5058c21004fd735842009ebe5459020006df74d8d10026be40592100067d70d9521004fd73d9221004fd7650b10256bc32d9121004fd75d9120025fa71c4110004fd7358640006bd43d912104cfc7650120006bd6319110004fd71d81420067c655814200cfc7359310006f46118142004fd735832101c7c75591100067f65885211bf78754401018d7e7518241006be73d9110004ff75593210067f65c411004cfe72d814105ebc4158640004fe764854001cfe7558a400267e4059620004fe7650910016be6450320024fc70590211eede70d8d10004fd7559110006bc51d9121006bf73d91210067c72594101e6ef62886100067f63d95100bd7c7548520016bc6450510006bc73d91210267d20596200067d315941004ef42198642016bc6490721006ef624851004edc5258f2004fea600862004eec6248510005bd7190a41024fa76c4110006df63c8540004ff7559020004ff731854201c7e76d9510257ae6290a410067c43d95100267c20596200b5f970989400067f6558910006ec64d8910006df5158f2000cfc73d8b1004cff7690b10025fa7090710007eb62c41101a6dc6390910006ec6418910004fd7559120007e862c411004ef42158420006f551986400067e4359620014fe74d8b10026fa6018241004ff7458810024fc76485102ee7f41d954200cfe73d9310006df72d8d40006df7358910006df63905101e76d658862011ef44018542256bf20d9121006dd52d8d10006ef43d8910006f651d85420077765d85420067465d8542006f761985420e6bc415932005ebe54d9110006ef4318910006ef6208540006f65118542006bf7459110006f5319842011ef77218542004ff73d8941006f551d8542024fe76c8510004fd72d8540005f970085400067f30d9521167e742d8542006df70d8d10006f553d85420dddc7350320005f77158940004ff7159120256be6290640004fd76c841005ebf43582410057f75486202ee7c74d9542006f465d85422067e40d9510006f63018542004fd7598420005df7350110216ed6388420024fe7688640006ed6218a41004fd73d8121006be50d9121026bc405902000cfe7358a40015be74c86400063f65d9121006df630854004eee3258021006f4619
  | 15 => 0x674d8542024fc7648640006ee641891011cfc71590211e6ee50d891004edd7258f2004cff7259020005f671c831023edc7058f20004fd7359310006dd7458c211deee5018910006f763d8542246dc10d8d40005f47150910085fb705854001cfc75185200067c75586400067f65d812100cfe7359110004fd7688540006f473d8542006ee64d8910004fe7608540016bc64509101e7e610d8910004ff7359220006ef6298910006dd6390720006f73118542296f4721854204eee621891000cfc7318520016be6450a201dfe61018910024fe76508102e67f21d9542006dc6358940014fc7498720166f754d854204eee620871011ef540185420067f3159620025fa708871004fac4250921004ff7259310024fc70592210057d7598542006be53d91210067c72d951004ede2158c2113cfd76505210267e30596201eede40d8d100067f65d9110006f631584201e6ee10d89100057f7558121005be76191100057d75d8a410067f65d91211deee1018910006f76518542006df735912004edd5258f2000cfc739862008d7c7558b10006df6348110006bd6190640074fe7690510006f63158620006bf64c85100067c65d8910006cc63d891001cfe7559120006bd72d9121006f751d8542005fb7050510006bd31d9121004fe7690b10004fe7618910004fd75d814102779654401004fe42148620166f7415932125ebd6390640005f9700841004cfe76d89100267f105962011ebc415902113ebe7619121004ff73593102ef6f42d954217e7e6550620004fd71d9120006ef52d89400cfb4415062000cfe73589100067d63d9542015be740854028ef452d8542006f451d8540016be6490410004fd7690720006ec53d8910006dc7058c21004fe76c8540036bc4159010004fd73d8910016bc6490510004fd7559310027f361c41101eedc20d8d1000cfc7358a41006ec531891008d7c7548710026f610586400067c651891001c7e76d9542006df52d8d40006ec42d8910006ef5318910005f47159120006f563185422e67c21d95422067c40d951019e7c655092104cfe7298642006bd30d91102ae7e32d9521016be6490620006ef41d8910006ef75d8910004ff73185200067d30d9542026fb61c411004edf4258c21004ff7650910004fd75d85200667c71d9510256be52d9121024fe769041004ede2058c21004ff7650420006ef4118910006cc6318910014fc7498420006fb30d8121006bd6450721004fd7598620005fb7048620006bc50d9121004df73591100067f31d9510006f976c421014ebc648852110d7c754864013fb44158941006bd6490720006de75d8d4004cfc72586402ae7e42d9521026fa601812100cfe73d912011ef654185422067e30d951001cfe75d8941006ef40d89100057d7518221004fd73d8520006ef53d8910
  | 16 => 0x8d100047f7559121006f565d8542004fe76c81102e73f74d95421febc10d91101deec5018910005f67198142076be5459210006f970d931004edd2058f201e6ec50d8910006f430d85420057f75508101f6be4018540004ff75d8542006de51d8d101567c658851000cfe73586420667d10d951004cff7608640006dd5158c211eedc70d8d10006dc7458c21004fd75586200b6bf40d9120006df5458c2104edc2058f200067c7459620004fd71d8940006f761d8142006bf65d9110005df7358910004fd73589100067f650851004cff760841004fe761885210067f75584200067f425941001cfc75986400047f7558420006f552d8542086f64198640006ec32d8910006ed6208410006bd64508100067f32d95100067f6550110006bd53d911004eec731891000cfe73d8142006ed43d8910004fd731854201c7c7558910004ff7259010026f77158420006f532d8542024fe70d85420b6bc6448110006ed431891004ef67198642014bc745891027eee614842100cfc731854201cfc75185422776c7548421006ec73d891001cfc7598420004ff7650810006bc63d9110006bf65d9121004ff7359021004fd75589101467d72d9521006dd75d8d40006bd4358241006f4511854001cfc75d8910024fc70d891004cfe72986400079c63191100067c65185420067e64d9521004ff75d9120016be6490a10006ec51d891017e7e6550410006be31d9110004ff745872000cfc7358a40006f970d8b10004ff715902004ede7258c2101cfe755901000cde76d8d40007b631d9110006ec5118910004df7359120005bf7458910176de6350421164fe769052104cfc7259110014ff765012001cfe755824100cfc7398642006f76148520296f67218542006df63c4110006ec54d891004eed7608620006f665d8542004df7358221014bc7458420026f41058420006ec5418910006bf52d9110006be75d91100067e7459410006dd5458c210069f64d8d1000cfe7358640006f7321854200cfe7359320006f741d8520006bc7458420004ff755824104cfe7259020004fd7558a10016bc6490420004fd7018542004fd735824121fe74108620006bd5458a41006bd6490421006bc64d81210267c405962004edd4258f2000cfc7358420006bd64904100067e31d9542006df6358910026f77158620004fd7359110026f410586200b6bc6459120015be7290a41024fe70d9121006f53018542086f54198640006de7058c210067e735962004ede4258c211e7ea70886200067d74d9521004fd76085400067c6558121006ef62c8110006dd50d8d40004ff7059021006de7458f20026bc40592102479f74d8d4004fe66148421006f441986200067f6559110016bf6190541016be645081004eec62c811000cfe73d814111ef7415902114fb44150621166f
  | 17 => 0xd0010bb0000cd00001201b00c00d00d00113500300102a01600009600202100e00001e02c00004002006700000202301a00202704800300800000001c03301d00705100800c00300000505622200901b00c01b0670270000f900001d06200b15500301a03d01d03214800000200f00600001e0000670000140000010020001a502d00200000700000700e00308f00000b04100600800100b0a900101cfe755891024edf40d8d4004cfc72590200067d6588410006dd64d8d101557c7550a2128ef420d85420057f7558b10006fb30d814213ebf42d9121005f4715081019e7e6550810186dc639051000cfe73d8910014fd769041024fd840d8d40006de54d8d10004fd73d85421e7e66188620025f87048610006bc70d91210067f6550521005dd73c8310024ff74590200cebf4359220007e531d8910004fd72d9110005ef7258141006f56148620005f471581420067c41d952101cfc7558a41006bd63d9121027f271c4210006ed311891004ef77158720006ee5318910004ff769042004ef76188521004ff72586402c6bd6390541006dd7458f20004ff73d8910016bc6450521006dd7158f20026be4059010007e531189100657c7548510006de75d8d10006df6318540006bf7459121006f6311854204cfc72d91200267d1059620006f55318542086bc64c4110006bf631911004cfc7259310004fd7698b10014ff76592210267c7059620006f451d8520004ff7358640006ee53d891000cde73d931004dee7290421006df63485400065f65d8d102367c215962001cfe75d8940024fe709862019e7e6550a200267f305941001cfc7558a400067f65c851004dee7188420006ed62c8610006df64d8d10006f95058021006dd7558f20004ef764842100cdc73582210267d4059620004ff73d85200067f745962001cfc75591101cff131c4110006f75218542166f641d85420f6dd74d8d40004fd75590200067f3259620165f67618542006fb7644010004fd755912118e7e6590620175de73189410267e2059410006be6519121004fd76904201ae7c6590910004fd7650720167e442d854201cfc755922104cfc72590100d57c7550a20004ff75d8141004fd7498620176dc6350510006ee52d8910086bf4059310006ed321852004eec7518910255bf7390a41006bc6458910004fd73590212ae7e72d9521186de639042100cfc73d8540006f53158640006ed3258021084ff769041000cfc735864218e7e65904100f6dc74d8d400067d30d95100267f7059410006bd50d9110006bd541854200cfc7359320017b66190a41037b44118141296f66198a4104cfc765032000cfc7359021005dd7398940004fd735932104cfc71d8910006bc72d911023ede4058f201e76e6588620006dd7058f2004eee6208410004ff7650b101eedc40d
  | 18 => 0x600a01a03900600303700d00603a00202601000001f0020a700a21400200700903400706800900000000003701503000004500000200000000304602e00200401f04b00200d02201500601f00802402801600f0000000000fa00002029904801201000000d01905319e01400000001000500208e01902a04c00300000b00900e0040580000143af00903600000100002b00305e04147b00100001101600201600101c009005038003016036a170be00300002c00703602c0cc01c02c00000800f00102101100002402e01d00808400001400004d0680000e00f800f00a01600100407800700a0010090010c60000050060000050170000000121a600705803a00000600100f00001a0ca0c505000f03500101400301d00400200000000000000700103a04500602400000500304000101700c6380160110710190111d602b00f0060000734a60ae01878d00a00100000001206701e05104b00d08000d1ac0070070040040040080060020080000a50bb00400000800210201c00213a01008a00a00006a00001b0090070e912101f01301900001105300401400000000300000100a10302e00300805205d00600301b00400401111600201102a8c400402501501b00a0a700100800206606600000204a00302a00502d01400305300000f0aebaf09704900201002801a01200a00300000000a03209000f0010060030c300003506900800503800001b01b00600200203706415705311405202e00200900500000b00800306600000200000002600000f45400300701000a00200001800306008704300000401c00b12d00004202e02200000303a02c00300502900200700100f04302902b00900000801a16800600c00000600000a00100c11b6fe19b04200e79600700a02902806900000300600f02300000000701a0000010a60520000ab00911a00008314402307002000804806900221a01300e06211a00302000000201400100001002104000201d01500900000e00007b0b800000500301e0e40150f600700106c02201b00000000000000001e00d00000400400000000a00003300301300100000700200800700000203a08f00000c00200201a00f03900201300b02101801401d09c00e0c900007300100200700202f00000600200000104f17d00204f00a0000d802801101100000e01a01400b00000000403503400000900901f07d01804e01205516d00602200401a00800106402501200000600d00900b2ae00100900101f02601300b0f901100001e01019a00c00d04b00000100001901400201200400a00100000117001002200100701600100000500004602602404300001800e1080ce04100001700901306900100600000000400e00700c0010000d600600c00302300609800000200700406900000000800500008222d00000600b
  | 19 => 0x200000000501b01107a08a04200b19401100400003a07205b00018300b0210230350000200200230cd05600a0060120180290090010fe01600e03f01801700317100900000000600114f01000e07300200b00900c00000700702a00200001801500300e00201f00202b08600008201100500400200100210505400c88000104203e00009913f00108600c00400b02804a18516f00700800502200c02917c02a0680040221d800002001700204902100301700305f11c05201500801f00200200f0385c200102e32c02501c09b07401100c07a02100f01400000700000500273203305f0d300a03315004500000600001100300c00302e06d00500100301700000b03000104c00000a00402800601102012500400b00700203601201203a01624212300700305a00601208403300200003200001400a32f00100100002b0f40470050744c300000107600500915801d14547f00200002005c00a02800402e0030000a000500c01c00101700201b00016f01400f02400300404a00a00000000000009b00500000f00101f0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e87d952144047968e2aa2c810802b3e095458c2128d5ac26e1b0a8443ce772185605080117f08b9ac8900031799573084100055c402c63224200a5d851c163084014e902ba2ca080f23be1d62c831000557c12ca3222000aaf8259764440018f0ebbb2200800317dce73596200054f426a2b184200acf8354362440014790a996c8880ef9a94350189100075232462312200087e87d9564440011ef0eb08c2a100333d8c725854000667b1ee4b0a80008bd870c364484010fd0e206ca908032d10776506200053ac0861b2a42008dd86dcd40c80010fb0b3b284880023ee0173591200046ec38a5b1a800087e8710b65440018f6edbaa20080032bddb74484210052ec1cc9b2a2000a3d859cb64440011bb0e296c6880032d1d061485200043fc2ae6b00422887d86dd521040018b8ebb1a4288002aba1263189102945fc32e32148200e3554d48615080147d0998acb1000297a167158f200043f438cab028400c5f7518d624400159904b26c6880023be1d64189100045fc22e6b0042018f5878c461508014ed0b988c2a11ff1d9db651854200536c2885b1220028bc845cd620400156f02b28c8908022fe1175589100063a32ae33028400ad7835c061508091d90e992c408003171d763589100052f42ee5b1a2000c9c74d8d62440014eb0b398c2a1003b14cb31185200043fc2aed2162000a5d859d163084018beebb1a42a00021fa1c755912104e67312e61082052cac721d1610800153b07b86c8909a237e1d5058f201e572c0ee9b122000a5f85593634404756d083a8c2a11beb3e097058f200057340ca63122074e3421d94644840155b08296c4880029b60b315941000675bb6e48802000ae581d50624400147f0ab9ec8880022f61e63191210053ac2ce1b0a8455a6e82cc7654840157100b1ec890802b360e64d89102ec3f43acaa1440008bd87d47644840196ac838a81880123d21d61504200145f43ee8b08400387f875d7648848d4dd0598acb10002972157058f2004d66412e0b184200a3f855c76448401c6aa8a90c2a1003271cf64589100069a20eeab0282008ef8758c624400193ee839ac4880023d61e6318542006d220ee4b028223cb6641c5428840159f04b26c6880021fe1d63d951029556412a830a8400c9c73d914044001938e6322c4880023be0975589100043f438cab0242018dc835da21500018b8ea31ac488002b560f70d854228d5ac20e7b0a8400acf835c362440014ed0b988c29000297e157058f2004c76412eab204200c74751c564480070f90ab94c32000637a0e7650b100074a20ac6a0e4000a5e839cb65440018beea31ac8880029760e74596200051ec2061b2a4251ae781588625040153f06b2ec8880123e20173590200054fc1aca32220008ef825d56448003998e6992c1108028fe1171d9542
  | 1 => 0x88438a851000e1fa1f75591100066bb9ee2b224000ab584cc7615080147d0998aca08003335cf62c81100047a40aeab224000e3441595410400187ae83a2cb10003b160463189100043e43a64b2820008bf875946448401878e9b2ac48808f2d19071509100052f41ce2b2c40008bd84dd762c400153906a86c8880122f21d43592200043f43ecab122000c5c7518d62500014d90ab20c4880031b1d772589100257440264b102000c5c73195644400153f06a86c89080a2fa1373d8b100046fc3acbb1a8000cb47458521880011bb07bb2848814b2d9c564904210052ec2cc9b1a2000a6d82cc765440014dd0b320c48800aad21261504200063a32ee29022000aac8258f64440011bb07baec5880029da14301854231e36390eab084000aac8258c64440019a8e638ac8900029ba0a63d951001c3f43eeab0840528f4811d942440014ed0ba0ec290002b9608411852011d5b426a030a84008df835db215000159b07328c4880029761474d8d100043f43884b282000acf8359362440014db0531eca880028f61670d91211e47743e63b1220098ec825d564080091e90ea8ac2100031bdd762485100065a320e29022000ae5820c06150801c6aa8298c2a1002b52057058f200046ec1eebb26200387c855d942c400f0f90eb2a42080023b60b75d93100051e422e4b2c400087e87d95615080147b0bb96c888002ad606631912101c3e42ae6b142000acc83593624400117d0e322c0909473918b7150910006563a6e4b1220008f7815d564080031b906b80c2a11463de0576508102ec3e43ecaa124200ab584d4761508015e100b1ec2a10ff8e94350d91100043ec2ee7b1282048bc8755164080015d304186c090803721cc72440101dc7643a64b004200a3e840c365484010fb0fa0eca88002a76135158c210056bc0acbb1a8003c7475945619000159906a80c488003279cf64c81100047ac3861b0a8400caf761d121084070fd0bb9ac9108030f1d4745842000636baec53122000c3c64dd5644409517d0fa8ec8908021f61773987202955b412a830a8400ccc63dc9644400156b09990c2a10021fa1f65581420055ac266230a8400a7585dc361508a5d4885a90c2a10021f61c30d95210061fbaee8b222000e1f5394f64484c51b90eb1a81900022f61e631911000566412cbb1a20018de83dd760484a59c8c438a84881b21fe1d32d95423c71a210ca30a8400a5e851c7635000147b0b318c888003a510763505100043fc2ae6b084000c9e76d93634407d17d0dba24288002aba12651891001c3e42aeca10200087d85dcf62500775d100990c290002ad60754d91100062e3aec690a8000c5d731cf65484cbd8820318c48800317dd763589100062fbaec6b0a8073e342119464484031df0e996c5880263b20973584200056641acbb122063
  | 2 => 0x865191210062f3b6cbb1a2000a76850c3615080159904b2ec6a008ead21132185420066a39ee2b122009aac825516408401938e9b9ac48800335d8f7158940006673b6c631220008fb805cd6448401d2b0231ec888002a7e1165d8d100145f426ebb162000a6f854cb62440070fd0b3b242a00030f5d7649812101c3e42aed2162000c7465dc540440091eb0f18cc2100263e21970085400075220ec4a0a2000a7685d046148001968823b282900030f9d865191211e572c08e7b122000a76859cc61508014e90ab08c2a00023b61e65189100062f3a8c7312204ac9f645cc62504014dd0b988c4880031bdd7725891001c3f42ee7b24420087f855c764480b90f90dbaac0a10023de0575589100051ec2663b2a8400c7465dc5605080147d08392ca081569ba0830d952101c3e42ae6b0482098be87d914244001878ebb22c0908021f61c40d95210051e42ac7b2242038f587944615080187eebb2284880029d61473d85420053642a65b1220018ef874cb625040199cec318c4880021f21d654862004c7743e623122000ad78155163084010fd0e32ac88819ba984064189100061eb2ee890c4000e958118c64440014bd0738aca080b32d19371509100046f438c6b0a800087f855cd62904018b8cab9e408800e1fa1776907200043e43a65b2a20048ec874c9629000187aea3aec8880273318973085100043f436eaa122000a3c854cb64484451b90cb9842880032d1d361485200046fc1aed10a8000a9d8414b635000117f08baac8900032dd9071509100061f3b6ca32242008de8718d625000159d05326c688002a761265d8d1000536c1061b2a8400ae5829842190001878ebba2c8880023b61f31189100065ab20e2a144000c6c65dc96444001968833b282900021fa1c30d95210065bb26e2a1220008df87d8c21500011ef0eb18c2a10063720d76909100062fb2ae79022000c6c651c964440014dd0bb9ec48800237a1c42d8d100062e39ecab222000c6f65dc9644400155b09a88c4880038d552511854204d66412a8b184200c6f651c964440015cb04186c2a10029ba0b31594100070faa4a8b184200a5d851c7635000155b0598ec8908029da1470185420061e3a0cab122000c5c7319560508010fd0fa0acb10002a760e65d91100053a40ae4b2c4000a9d8399464440031b906baac12080e1f21576486400063dc2eec8802000c9f741cd64480010fb0bb8ac9900031b1d762485100055ac26a630a840087f874c965040011bf06b80c2a1002b3a0e65d89100051ec20e4b2820008f787594615080153f08b8ec6a0002a7a0c52d91100043fc2ae7b224000a7685cc761508014df0ab26c4881731b18b75509100062e32ee6b222000c5d751d763500131790ea1ac990802a7a107058c2100c6e41cec10a2000c5f65dcd64440a5b4
  | 3 => 0xab024200aac8444062440a35690caa6c2a11561fa1f31d952100556c24c63122000a6d85d0f62440014bd07b86ca8800297a0c71d95420062f39aca10820008df835d560c84014bd0a202c610802ad61351185400045fc22ec9022000a5d859d163c800517908baac2100038d19554185420165d3b0c988220098ec825d56404001c38ca318c8880030f10775586401fe5d3b6c9882200087d8798f655080317f0ea1ec8880f2b921931d891001c3f42ce3b028400e1c6518f644400187aebaa6c8880022fe1173584200053742e87b122000c9f74d8d21440014f700b1eca90802b9a0473d891000477c3ac43128200cd7631c5625000117f08b9ac408002b9e0550189100070fb28c7b222000ab58414461508db0ff0e992cb1000387d94631911000578c00a230a4000e8c64d8f62440014bd06392ca08003179d7639891000566c14c9b1a2000e8f64d8f62440018bcec32ec68807aa721171d8d4004c77416ebb262000ec4634c462440010ff0abb28210002b5a0f70d854200537c12c7b2a2000c9c63dd12144001c98cbb18c4880028f21563191100053ac28e030a84008df835d56090801d1ec831ec4880030f1d4645812100666318e4b0a8000c7475d856050801c9ecbb18c4880028fe15619064000667b9ec4a0220498dc87543635000187eebb22c0908029ba16631891033f32080ca3122000c5c65dcd604840147d09b8acb100028fa16651912100477c3ac43162000a6d8599362440018b8e7b2ac09081e1fa1f41594100046fc1ae130c8400e575394f615080155b09988c4880029b61731d891004e56312e93122000ad5831c061508014bb0738aca0800297a1865d8d100064e3a0e6b12205dc3c64dd542440fbc6f09b28c2a10023de0573589100062e31eea90a8000a3e84cc765440ed5cb05318c2a10030f5d4649812101c3f42ee7b128200a3c8558c644840155908b18c4880028f21573d91210053741663b2a203fcb870d9141440139d4ec3162088003361cf70591200061e3a2ca90c4000e8c6418f62440018e8ea30ac0a10033958871483100046e43aa0b184200acf825c763500018b8ebb9ac488002abe0965191211dd74402623122000ab684d476148001c6883b2a8288002b520565d8d4000536c2cc7b122000a3d84dc56588001c98ca318c48800393d94631891002477c3ac51082000a6f825d165040014bd0a382c61080395d4e53185420046ec1eeb30c40008bd8714b644400193ec8b984288002b360e75d89100052ec2e82b1e4000c9c645cc214400117d0fb22c48808ab36087058c210046fc1aed212200087f855d94204001c5ea92a0c4880023be0975591100043ec2ee2b244000ace8399062440018becbb9ac09080317dd4735912000556c14c63224200aae84cc762440010fb0f31eca880028fa1
  | 4 => 0x44800187aebaa6c8900031b9db65189100066ab9cc210c8040a74864c765440131f10ea82c0108029720d72596202f43e43acaa144000a5d83dc3654400147b0b98ec8908031d5d76198142006373aec53122000a6f8558f624404756d08280c2a11021fa1f41d95100245fc3ac9214200387c855cd61900abccec3b2c429080f1d1d651584200066739ec410a2000e1c6519363440014bd06212ca080029da1663d85420066631ee4b0a8000a748558461480011bb0fb1842a000e1fa1771592200043fc3ac7b2a843cce870d8921440011bf0eb26c688003175d475d8d1000c6e41aeab222000ae582cc4615080155d093aec4880028fa1672d91103ef1a216ca30a8400aaf8458862440015c902b10c4a00023760f76485400051e42ae3b224200cd473d8560508014bb0bb96c6880021fa1c655854200c6e41aec10a800087d87d05658800156b02186c890802b5e0d50d854200556c24cbb122000a3c8558f64440018e8cb38cc0a10273318973989100245e43a86b242000a76810c3655080155b093aec48800637a0f759864000c6f41ce3b128000c5d731cd65880010fb0fa1eca880023da1c301854200672310e2a022000aae82997644400147d0b318c8880028fa1731d91102043f43e63b2a2000c5f751cd6244001c6eeaaa0c2a100297a1665d8d1000557c22cbb122000c3e75192604840187acbba242080ff0fd9175181410047a40aeab204200e35541446150801c3ecbb26c688002ade0565191100063b32ee2a14405e87e87d954248401938e9b1a42880028fa1663d91102955a432a830a8452ae68214c61508015cb05988c29000e1f21573584200247643a64b14200087f855d942440018eaea30cc0a10028fe1573d91210064fba6c690a8000cd47318560508014ed0b318c2a1002b5e0d501854200537c12e2b2c4000c3e65dd1218809517d0f98ec8908038719764d8d100063bb2ae33028400a3c8458f65484014e902b92ca080032d5d061085400247c402e6b10200087e871d562c40014d90ab18c4880033c547764401001c3f42ee730c8400ab5849d4615089555d0598ec8908029ba1674d89103571a080ca3222000aae82994644400187883baac321002ad205645042004c76412eab22200387c855cd6190801c3eca326c68808f2d9907150a200046e432e610a803cae8804cb62c400517908baac4080022fe1175588100062e3aec6a122000c3f7519160484018beebb9ac4880023760f75d81210062fb2ee6a022000e94634c464440014bb0ba0ec6880031d9947150a200056dc02e2b1e4000c7775dc564480010fb0bbb28488003171d4735891000537c12e8b2c4000c5c65dcd40440db0f90e996caa1002b360c52d89100046fc1aec10a8000c5f7518d61500019a8c7b8ac4a0002abe1110189100062e398c
  | 5 => 0x100e1fa1771593200052f42ce8b1e4000ab784548615080159b07320c4880023760f75d814211d72c10e030a8400ceb761c91004001a58ea3a242108038b19764d89100061e32ee890a2000c7675d86605080117f0eb28c8880031dd9471581420047b438c2b028400acf82597635000156d09988c290002b5a047058c210061e3aec8a124000c3d751d764484018eeebb0ac0a1002972157058c210061fb2ee890a20008df835d942440018eaca38a851008f2d99071508100043fc2ae6b222000a5e8510b634400127f0ab8c85208029ba1774d89100063a32ee2a124200c3c75dd16448401c9ea7298c4881c6b5e057058c212ac3f43e83b2a42008df875416308401b4882392c0a0926a7a1351d8d400056741885b122000e2f6519362440018d8ea392c88800297a0c74d952100536c2e83b122000ab9840c36050801d28c718ec8880021fa1f43d95100065bba0e2b224000c5f75d8d62500010ff0abb042a00028fe1163d95100069a20eeab128200a3f855c76444001d28c7188c88800297a177158f200045ec26e7b162000a3e84cc765484014bb07396ca8800e1f21573591100066a318e290220048f48754561900019aae6b084320002ab61052d89400053a42a65b0a8400acf8259763440011bb0738ec4a000237a1c52d8d100247a43a62b0c80008f980dcf648840117f08b9ac4880123da1b71509100052f41ee1b2a420087e87d9564484010fd0e186caa100e1fa1f75591201bd3b40ee1b2a2000c74651c5424840156d02186c890802ab21165189100046ec3885b1a2000a6e85d0462440014bb0b38ac7900028fe1563d912100536c14c9b2a20008bf845d564484d90ff0e996ca9080237e1f63c811000657ba6c490a2000aaf8458f62440031bd07bb284880031dd9771509210062f39eca10a2000c5c65dcd605080196ae820cc3100f23ba1e325822101c3e42ae6b2240008f787584614800117f08b9ac8908031d5d751d85400062e3a8e6b22200087d87d0765484018eeebb8ac890802b5a0c70185420046e432e79022000cd7731c5644800156f02b18c8908031b1d762509100062e39ecab028400c6c75dc9644800147f0a996c8908032719173989100064fb22e73122000a5e85dcb635000196ec838a849080637a0f75185420056dc02e8b1e4000a9f845c163c80d31b90ea82c7900030f1d165484100054f426a3b1a200087e87d0f65484014bb0a202c6108023ee1d60182210053a42a6430a8400cb7641c54044001c58ca32442908021fa1d654841000537414c9b2a2000ae582cc761508efcce84328c2a1002ad2116118520006373b0ca3122000c77651c542484014bd0ba0ac610802a7a0e72d91100076231c623122047e5a50d4163c80018bee739aca080030f9d764981210064e326e6b024200c3c75dd16
  | 6 => 0x1c3e42aeca142000e675194462440010ff0ab9ac1210022f61e651911023536412e8b2c400087d859c760508011bf06baac12080333dcf725891029573414e630a84018dc835d560084070f90ab80c2a100637a1f73591100046ec3ce7b2620008be87191624400193ec9b9ac0908029de0572596200055ac26a3b0a8000c5c63dd5424401359d05b8ac790003171cf65501100054f41ee1b224200c79655c0210400155d09a8ec4880029760e715962001c3e42ae430a8000ad88358060484070f90ab8ec89000e3be1d52d891032f63080c63122000c5f759d563084091eb0f28cc210003175cc73d95100045fc22eab0042008bd8799464484f1c6c84328c2a10021f61f43596200061f3a6cb3024200ab58414061508019aec7b8a8488003179cc65989100062fbaee6b22403cbe0804c762440014ed0b386c2a10021fa1c655912101c7bc3aa3b0a8400cbb76dd1100400317f0ea1ec9880033518c71589400063bb2ee2b028448e5a50d43635000159b073a6c4881df9910865185422555741061b224200c3c75d9142484d31bf0ea86c6a00031719773589100043ec2ceca162000cbb761d110040010fb0bb9ac9108021fe157650b1000567c1aa03122000ccc73dc962440018bce7b2cc48800a2f21175580210046f43ec6b122000ab5840c061508010fb0f98acb100021f61b75486200155a422c2a084000ae68190c6244001878e9b2a4288003331cf625011000477c3ac4312200087e8719562440070f90ab9ac01080637a1f73591200053a42ae030a8400a5d831c7655080159906b28c48800335d8c71509100057240a603122000a77854cb61508018e8ebb8ac8880028fe1172596200066a31ee2a1220048f8805cd644844756d09398c2a100297a167158c210047bc0ae6b224200a9d84d4563c80031b906b84c3210029de0563d95423cf1b420cbb0a8400e2f65d93624400159f06b2ec4880fead60475d91100054f424cbb1a200087e87cc765508014db0bb9ec4881729ba0b31d95420071ac20cbb0a8400c5c75dcd6444001c3ea729ec888146ad61075d85420055ac2061b0a8400e575194563084011eb0f328c2a102a3761f63085101fd5ac08e7b2220048bc87551648407f56b03b96c888002b5a0f75185423bf1b420ca30a8400a5e8310b6544001c6aa9298c2a1003339cf629891000e6739a6430a4000c7565dc54288001c58ca326c4880021f61e63d95210071aaa6a030a8400a6d82cc7655080517908b9ac21000237e0d75591100073232a623122040b70804c765440014bd0a3a6c6880021f61f43594100056641ae1b122000a3f8558c64484014ed0b98ec2900032b1d362485101ef2d286a1b1a200087d87109650400153d09a8ac7900033618f70485100066a318e2a122000a77854c8615084756d08298c2a
  | 7 => 0xf687d85605080193ae831cc488002a761351d8d4004c76412e6b222000c3d741d36548401968c838ac8900021f61f315941001c3e42ae7b2242018de83dd764c408959f04b82c61080e1f21576504200052ec2ee2b1e40008f78758461500131790eaa2c99080e1fa17731854000557424cbb12200087d85dcd64040070fd0bb92c120802a7a137158f200071ba8ca3b222000c5f759d563c800187ecbba2c0908028fa1670d912100536c2cc6312202cab6841cf61508015cb03218c4880021fa1c75591100061e326ea90a2000a3e85dcb644840193ee9b9ac8880021f61772582410056a40ae0b184200c9c64dcd64440ab8d8c5baa42881ba9ee01725962000536c2ee9b1220008df835d562440a517d0fb2242880029be1564189100052ec18e9b2a4200a3d840c36550801938e7b22809000e1fa1773592200052ec1ee1b2a42018f7874c761508011ef02bb2848800339d8871481100056741cebb122000a5f835c965880015af02b82c790003339cf62c81100046ec3ec790220008dd83dc1629040157700b1ec89094aad209541854235d3b408e7b2a2000aad82cc7644400193ee839ac8880031b99772506202955ac20ea30a8400ab7844c861508014d90ab10c488003a510563504210051ec2662b2c4000aad8299764440070fd0dbaac0908273318973c811000556c14ca3222000e376555061508010fd0dbaa84908028f61772d91210063ab2ee2a102000c3d7519262440011df04bb2848814ab9a076298a4100557414c7b222000aae8298c64440014dd0a216c488002a761351d8d1000556c14c7b2220008de86dcd40440018beebb1a84880029d60663d954200556c14c63222000c9c63dd121500070f90ab9ec89000237a1c52d8d400054fc1aa1b222000cb464dc520440011df0eb10c52080637a0f75d8b1001c3e42aec9022000e34654c464440011e902baac808003a9e0954185420061fbaee8b084000e1f5495163c808f5b100b8ac79014aad610701854204c7743ee4b222000c9c73d9160484015cf02980c4880023761e65d8d400047b43861b0a8400a3d84cc7654840155b08296c4a08063be1d32d891001c3f42ee7b162000a7585cc4615080147b0a186c89080297a1664d8d1001c5fc3aa9b224200c75651c54204001c6aa8a80c2a1002b320d641891000567c1ac83122000a7585cc761508014b90ab8ec6a00271b189759891000556422c43122000c5c73d9562440a35cd0439ec2a10031b1d7725911001c3e42ae6b048400af1810c360484014b90ab26c6880029de1570185420055b408e7b222000a9c8359764440018eeea38ac890002a720d65191100062e3a8c6b222000c5f65dcd62440091e90e98ac21000a2f211764811024c6f43ac6a06404ea7681dcb65484018b8e632ac4880021fe1d63d95210
  | 8 => 0xebba2c48800237e0d75582211f45fc3ac320c8000c3f7519162440018e8cbb8a8488003279d063989101655b42061b0a8400a9e8399764440070f90abb484880030f19375591210051fc22c7b2a4200e8c6418c62440070f90bbb2420800317d9773581420054e41aa1b22420387e85dcf624401395ce4b2482108031bdd7625091001c3e42ae6b16203dcda76d8f10440d90f90e992cb100021fe15729864000556412cbb22200387c855cb6050401d90c63162088002ab20965191100053a42ac230a8400c3f749d1658800193cec326c6880022fa1f64581210245e43a86b20400387c855d942440014bb0bb96c6a00029de1563185422ed1f42061b2a84008df8759763440014d90a996c4a08021f61773185400043f43ecab024246a6c825c5658800147f0a996c8880030fdd474584200061e32ae93024200c3d75d9262440455ab02382c61080e1fa1773987200065bb20e2a124000c7475dc564484018b8ea39ac890003335cd62084101fc5f43e63b222000a5e859d163084019c8c5b8a80880022f61f31d912100c5fc3a87b224200ce7621c5424400147b0b31ec888002b3e0d10189100053ac0861b2a8400cf251dd91004001958c9b92c8880031dd94715091000477c12e6b122000c74651c5424400155d09988c4880023d20573588100053642ac9b1220028bc845cd600840153d08296c6880028f61663d91210062eb2ae61082050acd829c5630840147d0b31ec8908030f5d074d95100052ec2ce2b18420087d85dda41c80c90fd0dbaa428808eada1332185420055ac24e630a840087f855cd64480095e10098ac2100029b20963d951000566c1ccbb1220008f7815d5644400187ce832cc090803a9104625051000c6e41aed90a8000a9e8399464440010fb0dbaa851000335dcf61581420070faa4a9b1a2000a6e85993624400155d0931ec48800339d8b71509100061e32ee8b0242018dc835d5644800187ecaba4c0908029be1562189102ac3e436eab024202ab681d91414400187eebba2c8908030f1d764485100056641a2031220048ec8758942040135c904a8ac210002aee01631912100567418a5b122070cdb7018d62500011db0f318c4880031dd9671981420073232c623122000caf74dc964440010ff0abb2408800637a1b735891029552412a830a84008bd87d4764440019aee630ac0a10030f1d774589100071a32c623222000c9f645cf2044001938c8b9e40880030f1d464589100063a328e2902200087d86dd542040018b8ebb1ac2a00021f617739864204c76412eab084000c9d74d8e6244001878ebb22c4880273918971c811011f1bc2aa830a8400ace8399462440018bce7b2e40880029da1770d854200656320e4b222000c3f75d91214400195ee8392c8880021fe1572185400056641aa1b1220008
  | 9 => 0x74594101665a326e2a12420087d870c365508031b906baac1108031719573085100043ec2ee6b244000e2f549536244001938e6322c0908023de0575591200063a3aee2b22406ae361019464440014bb06392ca08002b3a0e64d89100053b40861b2a4200c3f75d9142484019b0e7b82c488002ab61265189100062fba8c6b128049c9c74d8d215004756d08180c2a10021fe15735824125556412a9b2442529e68790521084011bb073b285880028fa1263d95100062fb2ae610a2000ab684d44614800193ec9b9a80880029b21563d891000477c3ac43128049c9c64dcd4044081ce6c3b2e20881fb8d21365185420053742e63b122000ab58199464484010ff0ab9ac3210032d1d261486200045f438a5b2220048f5878c661880070fd0bbb2848814ba9109321854200656ba6c531220018dc835c362504010fb0fa0aca080028f61731d91100046ec1eeb30c8000c6c65dc941484015b106b00c0a10029da1473d854233f33080ca31220098bc875516408401d1ec8318c4880029b617311891024c6e43ec6a02204acac72d914148401878ebba2c2100ee3be1d62c861004c76412ed2122040a75811cf654400159d073a6c4880028f61331594100056a41ac230a40008ef825d564040a374904aa6c2a10021f61773d92210043f43e62b2c400387e87dd561908031bd07b82c52094b2d190715092130d3bc0ae8b2820048f5861c542c40a35cd04186c2a10021f61f31d9521005734346231220038bf8755364440014dd0ba18c488026ab209545902000747b26c63122000aaf8258f644407f17d0fa8ec888002a7a1864d8d100145e422e6b12202cae582dc361508a574904aa0c2a10021f61f31d95100043fc2ae6b12200087d87d0f654840199ae7b1042880031dd9771509102ed1f42663b2a840387e859d942c400187ccbba242080030fdd764589100043f43ecaa122000c6f76dd5210840147b0b318c890803a319363189100245e43ac8a1020008df835c362504010ff0ab9ac890802a760f70d911000c6e41cec10a800087f855c061508031b906baac1908032d590715081033752080c83122000e558118f6544013958c4ba042a00030fdd2745941000477c12e6b222000aaf8258c644400155d0598ec888002a7a1264d8d1000667b98c4a022052ae6820c061508010fd0fa1aca080021fe1573d91210053642ac43128200d94415cc62504070f90ab9ac890802ad61352185420055ac20a630a8400a3e8598c64484010f90fb2a848800e1f217765081001c3e42ae6b148049a9e8414b63500014ef0ab1ec2a10029b61664189100064fba0c6b122000ae4825846150001d4904aa0c2a10023761e65d8d1000567414cbb1a2079c767619461508011f70eb00c09080637a0f769062000556c26a3b1220008dd83dd7605040187e
  | 10 => 0xb0a840087f855cd62900951790dba2c0908272b1c964503200053642a203122000c7475d8521480070f90abb042a00034d10575181410047bc0aeab2242018dc835d560908031b9073b640880021fe157358b1001c3f43eeab162000a3c855cf644400153908b2ec6880029de1561185420072a31a63b2a2000c7475dc5624400195ee9b92c48808eade155418542006573a6c53122000cae76190624400155f08b18c48800237e1f630851016572c10e7b0a8400cd473dc564480019b0e7bb220080029760f70d95420052fc2ae0b18420387e86dd560508014db0598eca908021f61676485403446e43aa1b1a2023ab48454861508c14ef02b92ca080028fe1172594100062eb98e7b2a8400ae48154062440014bd0ba0ec6880028f61331d95100043fc2aeca142000c3f655d262440091eb0f28cc3200022fe1173591100046fc1aeab00420087f855cb60504018ecebb0cc2a1002bae01311891000537c2a203122000c5c7518d61500014db0b3a6c4881729ba0830d954200476c3cc8312207ca7685994615080147908b1eca8800e1fa1b75589100046ec1eed20c40098bc8755164c80018eceb38ec9108021f61c42d95103ae37b90cab028423ab6849d461508051dd0fb1284880023ee1d60182410247a43a62b0c400087c8759542040011e902baac8100eeba20132580210047a40aeab102000a5d85d0563084018eeea30ac0a10032d1d371589100063a3a8c290a4000ae681d5062440011bb0f326c688002bc20163185420064f3a6c73122000c7575d86615080147d0b98ec8908029d614301854201c3f43eeab224200a5d8310965040070fd0bb9ec4a000e1f2157358a410051f424c7b2a4200a6e8598f624400187aebaa6c8908032d5907150a210052f41cc9b2a205dc3c64dd542484014bd07b86caa10029d616631854201c3e42ae7b222000a9d8314b64440011eb0c38a840800393d9463d89100247ac3c6330c8000a9d839cb64440018d8ebbb242108031d9d4619814200c6f41eebb028200aad84cc7624400155f08b28c4880029e20163d95210063a328e2b028400ad48155163084018eaeb38ec910802ade1170185420047dc3ac03028400c3d741d1650400156902aa2c8108f33a9db62c41100247ac3cc320840038bf875536488401878caba4c48814b69dc4744842100556422c7b122000a75850c361508070f90a3b2848800237a1c73591200054ec20e0b184200a3c845c9650400155d08296c488002b320971d8d4000726328c7b1220008bf845d564440031b906baac48800339dc871591200053a40ac7b2a843eab4864c464440911b90db9ac2a00032d10576506201dd72432623122000c9f74d8d624400153908b82c61081e1fa1f31594100045fc3ac632220008bf845d561080014db0ba18c4880029b209
  | 11 => 0x440014bf0ab8ec6a0003175d7639891000637baee4b222000ae9820c3605080199ee7b92c8880031d99471508100047bc0ae6b224000c5c655ce62440091790ea1ac80800637a1b73585400046f438e6b222000c3c74195604841359d04382c6108039319763d89100076231c63b122000c5f655ce624400556908b0c82100031d1947150110006363aee4b224200a768198f6550801d48c8988c4880273918a71c81100056ac1eea30a840087d85dcf624400156d0998ec2900023d61c30185421b56b40ee1b1a205fa79809c56504001d8b0231ec488002b520d50d854200536c2e823122000a5d8310b654400153908b82c79000637e1d73d93100046f43ec6b128072ad7815d163084098f4e0b284208002b520d70185420051f42861b224255c6c72dd561080e9c6e43b28c89080297a0e74596201f5d8402623222000a3e8599464440070f90ab9ac40800237a1c635891000567c1ac431220008ed87cc762440015a906a80c2a100317dd7735911000c6f41eec90a8000c3e74d966244001c58cbb20c4880feec20131d91100062eba8c7312200387c855cd6244001878ebb2284880033518f71481100043ec2ee7b16203bbe0804c462440810f90fb2a42881031e9db65c411000716328c83122000a5d8510b63440011bf06bb24088002b960853185420061f3b0ca3222000e2f65d9062440011e902b9ac810802ab60830d91210054fc22e0b184200e3584194615080117b0f98ec88800333dcc72591100043fc2ae6b102000c3c65dd162440018f10bbb22008002a7a0f70d911000666b9ec53122052ce6621c542040010ff0e996ca880030f9d065989100051f424e5b2a20008f4815cd64480010ff0ab9ac5080021fe1573586400071a3aaa830a840087e87d0d65880011df04baac8908038bd9464189100dd66c16e2b1e4000c3f65dd162440018beea39ac8880030f9db651911000572c106230a400387e859d94244095958c5ba24288002bce0163185420066639ee4b22207de3642d946150847968c838a84900030f1d474589100051ec24c7b2a2000c5c75d8d62500010fd0eb2a8408002b52057458c2100556c24c7b122047ad8805d163c809dcccca9084208002ad61350185420066dbb6e68802000a3f8558f64440014eb0b31ec2a1002b360c42d89100051fc2ac632220018de83dd760508014f100b1ecaa100e1fa1f755864025656396e8b084000a6f8558c624400156d023aec88800a2f211755891000536c1662b2c400087f855d921900bb47908b8ecaa1003279cf64085100051ec24e5b2a2000c3e75192624407f5690c98ec8880030f9d7649891000566c18a5b128200cae76d9062440070fd0bb9ac8080fe2f21f644851036c3e43a65b2a4200c3c74d956048401998e6392c88810eb9e0970185421655b420eb
  | 12 => 0x4c13700a008010660c20400981b002080000f10460340583501c3e40000000654d9408504807400000000028000000a4024069cf0074640083902612c090615da3f40982e008129b280201803c0481a08e0000200400e2200400500600c0004b0104bc0001101e08c0009f00a008000000240392b80205a0043a8002b00143104600090c000450060000100107607c002040720ec030110000040300801112c4f0330000ccd10202381540204f000200078570075cc1a01f004064020a501e0000b81b0000040300c060058008020006b87886b0000c80501000c00025805002000030050bc0800064e00003c0400d0b20605280d124469cd0770040102eca10020d80189f08e00610a5509c008010a801a08c02812076094011860020054d00517e0301f00c0e0004000040020b81502a0a801d980030a20080801702e0089b82300802c0103100e05c8c85319a000230090000500200e00c03c015a2002bcc070090141482d8070081880684000007000007044bf4590440002e00200a0082e00102003a0001682300002026be501b3300080305205c8b81d0020000000d67743800807000bac0680b0001e80001502001006000004024080940b00040280021e000780040260482e01619a144d50080020002486c0080049606b05c00c008010060047f00a11a0a4308330160040803d000008039a637e1d50d8d100052f42e82b1e4000e3441595418804756d09a90c2a1002ad613511854200572c0ca6312200087d87cc765508018beebb1a428800395d4651d8d100053642ac431280008ef8759462440011bb07ba8c2a1002bce0163d85420064f39ec93122000aae84d44624400193ee9b9ac488003171d773591200047dc3ac03028200e4f65d8f62440010ff0ab9ec8880028f61263d95210053a42ac7b0a847aa768619461508011f700b9ac4880039518e31d95100064f398c93122000a6e85d07624400196ae8208c2900031bdd472591100064e326e6b122000c9f64dcd624400155908b2ec48800a2f21076485400063b32ee2a102023ab684d4c6150801998c6392c888002a76137158f203b572c14e630a8400a3e85dcb6444001b2883b9ac0a08038d10765505210043f438eab224000a3e8619464440010fb0f3aec910a031bdc8655854200536c1061b2a4200acd829976344001c9ea729ec488002b320d62189103dd73c12ca30a8400c3f751d162440011bd0fb1ac2a0002b3e0d651891039f1b908ca32242008df835d564480091f501b9ec91098a37a1f635011000c6e41aeca1220008bf8758c64484018b8c7baa42880029ee0163d95420043fc2aed2122000ccc7318940440014e90ab18c2a1003391cb71591100045f43861b224200a9d8414b63440031bd07bacc3100028f21571d911000c6e41aec9022000c9c7418d62
  | 13 => 0x817b0000e222c0000164600c4405e0001500300112402801800003544008000082ad40000412010028000ce1600f02022e020050570040000102d0000000c901002050041d0016010010190360c96c80955802c0800d0000cc0000c0dc0058100301e0080e8000000080700705a0246b8000000000880712e000080000340280c803530004000030000000005200602c2601404000c010000a20240605519028a3d80a01a2ac040045480640200b000e097a004106080000400020442a00000005c03012000194130050060002b80b00e0500e000322000000000201600a00b1380400080e01a2a00000a04a05c051611800000881b00200020015502420028280100257d000030289978030661080ce7703a0240000923a654060030040140300c0dc018300140020443383d004295
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1a00a80c220148029803b440000c0041e89108854c861508cfa60801953118910294a9249849d461508e76249255051185422958924954548615080161693dd554185423c689208655506150801a25546085318542336a8200644c462440a5624925535218542294a9a6382550615090b6249255253185420068920b7555061509076249255053185422948d26154548615080103f985d074596203a58924954944615090362492553501854240f0910a651c542881056249255150185424248de6154d4861508a52a49261050185420040fe61741d1650400105f985cc735962032eb0200634c46244001a155420d5018542006892087555061508fba2482d95541854242689e1482550615080142c925d074594103568c200654c464440a52a4926135318542
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x821a224a95518214c6150801502512a841aa030a8400c81a4c82dd55418542
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4205b92895420d5018542004205baa4c82dd55418542
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x138c
  | 9 => 0x3
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124c
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138d
  | 17 => 0x138e
  | 18 => 0x8c
  | 19 => 0x8d
  | 20 => 0x8e
  | 21 => 0x98c
  | 22 => 0x98d
  | 23 => 0x98e
  | 24 => 0x128c
  | 25 => 0x128d
  | 26 => 0x128e
  | 27 => 0x150c
  | 28 => 0x150d
  | 29 => 0x150e
  | 30 => 0xa0c
  | 31 => 0xa0e
  | 32 => 0x130c
  | 33 => 0x130e
  | 34 => 0x20c
  | 35 => 0x20d
  | 36 => 0x20e
  | 37 => 0x140c
  | 38 => 0xb0c
  | 39 => 0xb0d
  | 40 => 0xb0e
  | 41 => 0x140d
  | 42 => 0x140e
  | 43 => 0x154c
  | 44 => 0x154d
  | 45 => 0x154e
  | 46 => 0xb8c
  | 47 => 0xb8e
  | 48 => 0x148c
  | 49 => 0x148e
  | 50 => 0xd0c
  | 51 => 0xd0e
  | 52 => 0x160c
  | 53 => 0x160e
  | 54 => 0x94054
  | 55 => 0x94056
  | 56 => 0x95394
  | 57 => 0x138954
  | 58 => 0x138956
  | 59 => 0x209
  | 60 => 0x1409
  | 61 => 0x1449
  | 62 => 0x289
  | 63 => 0x1489
  | 64 => 0x14c9
  | 65 => 0x139256
  | 66 => 0x140094
  | 67 => 0x21295
  | 68 => 0x21294
  | 69 => 0x141294
  | 70 => 0xa4b
  | 71 => 0xcc9
  | 72 => 0x18c9
  | 73 => 0x12cd
  | 74 => 0x148b
  | 75 => 0x149314
  | 76 => 0x149316
  | 77 => 0xb0214
  | 78 => 0xb0216
  | 79 => 0xb1414
  | 80 => 0x20b14
  | 81 => 0x184b
  | 82 => 0x28b
  | 83 => 0x140b14
  | 84 => 0x140b16
  | 85 => 0x14cb
  | 86 => 0x155416
  | 87 => 0x141554
  | 88 => 0x148b94
  | 89 => 0x148b96
  | 90 => 0x149614
  | 91 => 0x149616
  | 92 => 0x194b
  | 93 => 0x164d
  | 94 => 0x44d
  | 95 => 0x4956
  | 96 => 0x5556
  | 97 => 0x5856
  | 98 => 0xcd
  | 99 => 0x2cb
  | 100 => 0x2c9
  | 101 => 0x24211
  | 102 => 0x28211
  | 103 => 0x2c211
  | 104 => 0x12ce
  | 105 => 0xce
  | 106 => 0x2c291
  | 107 => 0x95456
  | 108 => 0x44c
  | 109 => 0x164c
  | 110 => 0x129516
  | 111 => 0x151294
  | 112 => 0xd515
  | 113 => 0x21254
  | 114 => 0x21854
  | 115 => 0x2c293
  | 116 => 0x14c293
  | 117 => 0x45295
  | 118 => 0x20cd5
  | 119 => 0x44215
  | 120 => 0x74293
  | 121 => 0x45555
  | 122 => 0x21655
  | 123 => 0x21a15
  | 124 => 0x20455
  | 125 => 0x194293
  | 126 => 0x164215
  | 127 => 0x165555
  | 128 => 0x45415
  | 129 => 0x198293
  | 130 => 0xa4293
  | 131 => 0x5c293
  | 132 => 0x29953
  | 133 => 0x17c293
  | 134 => 0x285d3
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1601
  | 6 => 3046
  | 5 => 1737
  | 4 => 32
  | 3 => 3
  | 2 => 2
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/638+packedAt gbK7 (59237+(h % 638)*11) 11) % 1601)
  | 6 => 2*((h/1050+packedAt gbK6 (146208+(h % 1050)*12) 12) % 3046)
  | 5 => 2*((h/586+packedAt gbK5 (102483+(h % 586)*11) 11) % 1737)
  | 4 => 2*((h/24+packedAt gbK4 (2240+(h % 24)*5) 5) % 32)
  | 3 => 2*((h/8+packedAt gbK3 (243+(h % 8)*2) 2) % 3)
  | 2 => 2*((h/7+packedAt gbK2 (184+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff01fffffe01fffffffffff433e3f1c78ffff
  | 1 => 0xc07fe07c07ffe07ff81fc01fbccfd9e3a71e67
  | 2 => 0xffffff8007ffff80ffe0001fc0f1e1ffc7e387
  | 3 => 0x7ffffff8000000ffffffe0ff01fe03f803f8
  | 4 => 0x7fffffffffffff00000000fffe0003fffc00
  | 5 => 0xff8000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x14800295096008b1182854d101160b0c086cab
  | 1 => 0x4431602c42aaa05a691e815a1c4ad961a31665
  | 2 => 0xa95ab58084d4d500b742028cc0a160b6c5a386
  | 3 => 0x87cd94ad0068408c7972b08ee01f403f00350
  | 4 => 0x306f1e73e71f1e6c02040c00f7fc00037ed800
  | 5 => 0x3e0810030018187004183010fbffbfd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_39593
namespace PEqualNP.Outside.L_meta_39593
open PEqualNP.Outside.L_meta_39593.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 9 := bs0_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 16 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 13 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 27 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 144 := (concat bs3_3_0 bs3_3_96)
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
theorem bs3_4_576 : Interval s3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 883 := (concat (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 (concat bs3_4_288 bs3_4_384))) (concat (concat bs3_4_480 bs3_4_576) (concat bs3_4_672 (concat bs3_4_768 bs3_4_864))))
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
theorem bs3_5_672 : Interval s3Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 802 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 bs3_5_288)) (concat (concat bs3_5_384 bs3_5_480) (concat bs3_5_576 (concat bs3_5_672 bs3_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 24 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 117 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 12 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 91 := bs5_3_0
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
theorem bs5_4_768 : Interval s5Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 794 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 741 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 bs5_5_672)))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_5_1728 : Interval gbAtlas 5 1728 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1737 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)))) (concat (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 (concat bgb_5_1152 bgb_5_1248))) (concat (concat bgb_5_1344 bgb_5_1440) (concat bgb_5_1536 (concat bgb_5_1632 bgb_5_1728)))))
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
theorem bgb_6_2976 : Interval gbAtlas 6 2976 70 := block_range (n:=70) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3046 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672))) (concat (concat (concat bgb_6_768 bgb_6_864) (concat bgb_6_960 bgb_6_1056)) (concat (concat bgb_6_1152 bgb_6_1248) (concat bgb_6_1344 bgb_6_1440)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1632) (concat bgb_6_1728 bgb_6_1824)) (concat (concat bgb_6_1920 bgb_6_2016) (concat bgb_6_2112 bgb_6_2208))) (concat (concat (concat bgb_6_2304 bgb_6_2400) (concat bgb_6_2496 bgb_6_2592)) (concat (concat bgb_6_2688 bgb_6_2784) (concat bgb_6_2880 bgb_6_2976)))))
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
theorem bgb_7_1536 : Interval gbAtlas 7 1536 65 := block_range (n:=65) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1601 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672))) (concat (concat (concat bgb_7_768 bgb_7_864) (concat bgb_7_960 bgb_7_1056)) (concat (concat bgb_7_1152 bgb_7_1248) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536)))))
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
  · exact allgb_2 i (by omega) hi
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 50, 58),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80eee8eae0eae8aa80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241888 * 2 ^ 32 + 3941116544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_39593.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[2,4]⟩,⟨.and,[3,5]⟩,⟨.and,[2,6]⟩,⟨.or,[0,8]⟩,⟨.and,[1,7]⟩,⟨.or,[0,11]⟩,⟨.or,[3,11]⟩,⟨.and,[10,13]⟩,⟨.or,[9,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 3941116544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3941116544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_39593

open PEqualNP.Outside.L_meta_39593 in
theorem PEqualNP.Outside.L_meta_39593 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 3941116544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3941116544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
