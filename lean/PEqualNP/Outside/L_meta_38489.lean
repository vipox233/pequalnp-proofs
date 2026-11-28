import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38489.Model
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


end PEqualNP.Outside.L_meta_38489.Model

namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
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

end PEqualNP.Outside.L_meta_38489

namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x50001052020f610bf43ec20bd42be40de30bc41bd43bf42be41bc40ee20f410dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa48023aa7a178080108ea9883d0300425aa420cb54b43
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s0K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/9+packedAt s0K3 (162+(h % 9)*3) 3) % 6)
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
end PEqualNP.Outside.L_meta_38489
namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
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
end PEqualNP.Outside.L_meta_38489
namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x804f01c0403c101418d00d20009f0423cffd41fd43fd10fd40fe40fe31fe32ff40bc43bc40fd21fd30fc42fe20fd31ff20fe43fe21ff30ff43ff32ff10fd42f731fc31bd41bf42fe10fc32fc30fe42f431fc21fc41be40fd20ff21ff41fe41fe30fc10be43bf41fd32ff31fc20ff42bd42fc40fc43
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xb8042800d03040583800a96120018102781ca039b028c0500028aaa122100840e03800c90ac9a8000178000001c801acd0400a1028000038380280014066d54742daa0e213e5090e7aa2204f550209faa4215e53c867aa421edd08319f28683b6430c6eca2106d54440bb28c61b454cc67ea8886dcc440da18c81ba501027ca810dd94440db28e855c5348278a0a14f151319faa4413f544ca7aa9195b14930dba0e63b541086eea2a1dd54632ba28a653c50506e8a2a1cf95020b7a92213d5110e78a9086d504319f2a4653e54cc27ca9904f94c409f2a0213f5250678a8905d544209eaa4433f54cc67aa9884714d419aa88813c544ca7aa321d714d10eb29863b542cc6bca6107510c31cf298873c544c27ca0206d508319f29e857551d0a7ca8214f951219eaa66175518c27aa920dbd4930ea18c613e540c67ea8986d95031daa0e433e5310e7ea9994f55230bc28265d7430c67ca7204f953219fa8a857751482bea6884f942409eaa4853f544827aa3206d55031d7a928576518cae8a2986dd4541aea9e433d51d0aeca618e7d4d419f2a083b4430c76862204f55032dbaa6633e5390eeaa3a1cf54b419f2a4639c430c67ea898e714d419f29e83b541cc6baa6106dd0431ea188617b504caeca3a1cf14d42db28881b742cc6eaa2205714d419ea948774514827aa9904f55031afa9a833e5010f6e63204f153319e2a6653c548836c8798cf952309e2a2217651d0b388718ddd45329eaa6433e540caeca318cf55010daa0a213d548c7ae6418cf150309eaa04377514c27aa5205b149109faa0613e54c43aa6418cf14d419f286853e54887688798e510c319aa8e853d521027aa890d7d4d20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x5800021009cb008145040428a800c004404300201b3c10476408dd8552902356115030c5d8d51102976510c318d584548821463547428dd973110316540c6308d597420c6a56215331c594c3190294644c831a5594430c61d6510c31c5150310c2966010c318d5865090e346354742a518d420c62d62153318d594311029463507218d19541442946354440a518d41c43145350510a598c54cc7146354742a598f54cc69463505108798f548431653507218d99742cc6386055121c514f515063561951218dd855290e956210c31c5d8d51d0ad0604c831c9149414431463544408718d544862d62150308518d511025463547428718d51d0a356195320c5d8453506946354742a518d410869464cc8318d18d511023561153328d5845050a1c63544409518d511023561953308d586540ca966390c31
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x80900000014000020a3b0a6a0a21215cb6510c3182ce7b0aa520604631494144282b90a818861051cd6195121828e6b08a0a14147358654c820a39ac22a441419cb6114d41
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/23+packedAt s2K5 (800+(h % 23)*6) 6) % 50)
  | 4 => 2*((h/62+packedAt s2K4 (4455+(h % 62)*8) 8) % 165)
  | 3 => 2*((h/34+packedAt s2K3 (2280+(h % 34)*6) 6) % 60)
  | 2 => 2*((h/17+packedAt s2K2 (490+(h % 17)*4) 4) % 10)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 1 => 0xfc07ffe03ffe07fe0fc0f81ffc3ff01d8ce7c
  | 3 => 0xffffffffc0fffffff000ffffffc1fffe0ff8f
  | 4 => 0xf0007ffffff0007ffffff001ffffe001ff0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2045088c48824408052c9292500529540b50b5
  | 1 => 0x6493391439248cb9605585b0b6435a0cd8c65c
  | 3 => 0x890a522090691852aa0209652aa814a960ab0a
  | 4 => 0xcc2c64492241d164d39b2041cd328031b50de0
  | 5 => 0xe307871c38e1e7f1ce3ce780e2318c1fef000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38489
namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2437f54ccbde84a15f95321bf2a2657c53442faa818df94b30bf2a0855c53507dc6510fe10010f790c43de438c3ec20885f94830faa8e85df320ca7ea8995f94421df202817c52506faa710df54440bf280657e5310efca7207794f21dea1c817d540cbf061905f54031faa0e217d508caf8a0995f94641bea86637c540cafca5a0df55231be2a265dc53483ec4210df14520be2a421be4350efea0a0dfd4c20bea9e857f52842fca710df14131dea18817c54c8278a8905f15220bfaa6617f54482dea4a0df94210bfaa041ef4290a7ca910df95043bea8c657f514caf8a2985f55331bea94837c53042fca2105f94740bf284837e53842f8a710df94230dea00817d52887e842085f14d41bea8e81dd430c2faa5205f94c41fda8265bf40902fca421df14f20de2a2217e5290ef0a099774c030fc20621fb10442f8a7105f55330fd98461df300c2fea8085fd4121bda8283fa10042bea6a0df95020bea84837d54086fca7905f14143be29281bf401027aa8085f94440beaa641f521086faa7105fd4530bfa8a877e5010efca598dfd5021bf290657e51882f8a090f794c20bea9c83fb10843ba64987e90040bea8c41bc41902fca8905f94c31f7190657e51042fea488774cb30dfaa22174514caf8a998f74c431beaa2417e528cafea7087d50510beaa665fa200837e8721dfd4d42beaa4857d50887da64196fd0e40aea9e43bf4290afaa6885f55132ae29a41df320c7bea6a0fb54b31f7a92837c5150bb863185f94821de2a2657f5250efaa890fdcc421de208817d540c2faa4085f54730bf28c856c52507da64905b94830bf280817c53c42faa5a1fdd0641efa1c635e53c86fca6885f54642bea9c657f544caf8a2a04f15110df2a661fb50506faa420df54b10bfa9a217e52442fea0a16fd5120bfa8287ef52442f8a5887b8c920bea8865bc4310afca8185f54d20deaa443bf43102faa021fecc130df210817d52882fca1215f54e40be282837e5210bbe6318ef109419faa2217c53c87baa6105fd5030be2a021de5310af8a4087ec8120fa98863fb30082faa020df54243bfa9263ec21882fca1205fd4d21bfaa2637f54cc6fca610f7d4d20de216837d53c82faa6105f54341bea8c217d54886f8a6105fd4810bf29e85ee52cc7d88410dbd4910bfa8a81ec21082fca0215f54343beaa421be540437a86a0df94b40bf29481de310c2fca3996f50c43bf288837e54c43d8a4a0df94643be294217e544c6fca7107714d10dea0a81fb40502f8a498df95010be2a243bd43d06faa518fb8cb20bfaa4657e500c7be8721df54032df21285bf41503da65905e14141beaa4417e54842fca4105f950319e2a265f7514cafaa321ef90a40ee994637f54c42fea9107dc8621be29843f641087bc87994f55031fd180617d54442f8a4a1df15332
  | 1 => 0x7415077e83a07bcca32f710c417d548c2fca3195f14532bf28c637d5210fee6318df54e10bf298817f504caf8a690f790c30bea80853d54cc3d88510fdc8521ee990655f53483ec8220df94a30bf28c61be41903eea2905f14930bb28e857e52106fca9985fd5032ae29a217f53c87ba8621dfd5320bfaa4637c548c7bc60987d14520ef19265f551103e86210df55241bfa96216d52cc77a8220df15131bea98837d51d0fbe8618f750e30ef984617d53d02fca3a1df95121bfaa0637f53506f8a818ef95221bea9221f850507bc86995f94a41bfa9c41dd53d02fca4206fd0c43bda8265dc430c6fca721dfd5321dfa0883f731c87daa4185fd4930f710841ef42086f8a8987ed0010bea9c63bf43506fca720fd44010faa0e437c53502f8a910ef90440bea88417e500c2fca190cf95031af298857d520c6fca118fe0c020f719043f9300c2fea2905f14910bfaa421bf43d07be64985f54630be2a0617c53482dca598df95130bea9e43df32cc3ba87995f54430bea90617c5050afaa118df95221dfa10857e54106fea910df15232f699443f940102fca7a0df94221fb28881df53442eaa2205f55130be2a6617d53c42fea610df54a30f690843be4310bea8210df15020bf29485f431c87de64995f94f21f6a10857f504c7be65195dd4520be2a0437d50cca7ca8085f54021bf2a441f7314c7f681885754c42deaa0217e52042faa2215f94342bea98437e530cae8a2905fd5230ef988637e50082faa8085f95110fc900417e51c83d8a4886fd5132bf2a4617e540cbec83887bd0a21bea9661dc310c2f8a8907ec8220f7900417d53486eea2995f94c10bf294637e50cc6fca5a1cf55221bf296215f534437887215f54c42bf288637e54c82fca310df54742bf29a437d53042faa990ef50842f710241fb40903b8a6a0f710e31fb28e85f910042fca418fb90842beaa621de314c6faa7185f94443df2a0637d5490fec8390df14d42ee990637d52d07ec6218dfd4f20bb28881f541106fea4a05fd5130bf298617d5390bee21085f94742ef18c61ee21486fca1107bc8421beaa4817d50c86fea6086f90941bf280437f52507f6619077cca31f6990437e50ccafaa9195f94442eea1a65be42d06faa6205f15110beaa2637e51902faa598df54720b6a9061f8504caf8a9885b14910beaa0415d53d037aa9985f54a43bf29e817d52842bca6105f54b40fb90c213e54cc3da40105f95331bfa8a857e50d0efca8205f54443ee194617c548c2faa1a16f10a40f790441bc42102fca918df94232be2a6437c5150efca020df94f10df20a83f641442fca1a0f7d0d43ef29e81bf41906faa1215f94243bfaa221bc54482baa610778ca30eea9e437d53d07bc8621df54732bfa9e217e54ccafca6105fd4d40fa28a65ee520c2fea6905f94430bfaa
  | 2 => 0xc070b08f19cd500c08080001240000c12000010b80401042020020000b03c0a00040000000259102004000050000a25c1f0249f02c04004040080e09c210100f004d80301200001000180001a5dc0a0007e01c0500037068000100300003020000049b0dc0032942050d60001a594000002b7982f04800010130540000c000040400021050360001f030000200000c05004d1000390a40802804364060489d408020ec7e02c20000020003c00802004260000700415324048ec0e2a01c034a800c003cc0009c01000000f80000006024001280710c660346f03000060040280002c003a4010280006c01000432b0025d415058000000109c0000c063a0000080a000002180f0000205800048280040d494002a8050041b00802000b50040000000034430040a0240a01800008d603800018060f0090282d01011fb880217e548cbb864185f94e42deaa0637e50042faa3206f50740be29c213f54482fca3985f95021af29e817e5310b7c87215f94432eea98857551d0afca5087dc8410ef190617f53886faa4205f94d20fa10c21f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd524425f635511097594430c6776154a438f191508ca3f6454232ad592210877051d41329d986544ca5d6314940ce50c50506b561d0a429dd95100423d6414f209e582544cae562cc4219b98b548423e6515132b6582430c27a60d5032d9d8552cc69d6310b419798e544425f63542419798c540835853c81209758f540827761551209758f54c86e7614c821d9587525066d6510821a758c4210335515004097d8d544836532145209e982544ca5e63d52108f590530863c6454b31dad4850507344254440ce904505066f65484219b58a534431f5414d209d584540827461551209758f52c43676154830d614c505066f62551108f992524434c53149419dd95411069d63109419718d51d0b2f6454b31b6181320c67561152209ed81544c77051141329e98354cc6776154d21cd909511033543544408fd95411071d53507409798e534823f64548308f992518ca3e6414f109e18154486b860507409e583538863d6414f10cd153514cb645250510d9d89511031c53109419798e520873b4314141c714e425063f65508429b98854cc6cd63c86219e580548c71d54cc8319d584548c23e6494e10ab191320871d54d0c31d918951102cc6250d32ad590310867561150308f994544834d43548309798e529066c6254743bc18141086f060507109718d511033551d00409b98a5344276611501097d8d518833b54d4132ec50740c425d6315321cd553218863d64d481097d954310e5c6355121d914a10443355190440cdd50514cb5b53d41419b988530427965840109b18954442d8604ca31d314f525063e64150319798f540827661d4e20cdd53514832d5410a219d58454cca6d62150309e98053086cd63c8421ae181411065e63153108f990530865f654c0308f992544ca3f65500409d1855290e6d62d50309d984548831d53d07409d984548c32c64548309758e544827a60d4e21da181520c35453d4520cd553100427b605512197596430c25c6550d329dd8552442b960108408f191528436461548309bd95200829c644ca319dd95210866c62544409798e534433561151109758e544433754145208f191534435b5314141cd550210427b65480209d185534831d544c831cd54441103594314132a758c429023e64951208f590514c25e63952209b994524427b654c0309d594210431c5414d20d554c31c86786055132f14c8310867b6055132ba181328867561953209758e544c31c5490d329d984540c2d463504219bd8953442cd62cc4319b98a524426e6214e10d354e210833454d452097d8d544866c6254d109dd85544c3545314520d5d8d51d0b1d54ccb309b98a544427b65500409bd89544c63e64d48109bd89511025e63949109758c54c82b5640c721d314e32482cd6310a219799453442756195120ce153504cb586054c20
  | 1 => 0xc25d6315310a7590318c23f6454d219718d544423c6454231ce181540436852d41418fd91508c65e63150219b98a53c42d86348020a7593300c25c63551208f990540432c6454b31cd55321043706054440d354f200825d63948219d98454ccb576154f219b189544c23d6494d208f992544427b6054d20ba18132c832f5210941d98c8514831c63550318f99353882746155132da148505063d64944218f993538874f53149109ed95100425e6394b108f593538832f64548308f59252442cd6310821d518d51d0ad46350721d3549300c23d65904409d594310863d6414c109b98b540c23e65d0540d5d4f514823c6454d219dd85520c26d6294d219dd85534831f54d4d20a758f401034f53d4910f24cb30c825d63148108f592534427565904218f99253483645290510a7593308c25e6315320d354b300c25e6314c209e58354cc7345414532b358b318c66c654c920c7150534423f64549109b58a544427a60d532197994534825e6315321ec90440c434d6214d209758f548426e62d53319798e54482e461480209bd954210a3e65151108f993530423d64d4b109b58b548423e64944218fd9152cc63c645491097d8d511034d528c430b6181320cab86444010d354d200827b60551109798c540ca5d658c830cdd53514ca6c62551318fd954310f735114132d5d4c514825d6394a419798c528423d64946329798f54c863e64148109d185529032c54149109e58054086756194d20d354c210834d528c8309758c528431c54d4d108f992534426c62546308fd91534427561d4e20b9587420871c54d4d209b98853082b46150d4197596530834e4354830ce55340042b860505409718d509063e6494c309798f52c437351d41329e59430082e8604c821cb153524432f6255221d690c504ca3f6454021c7d5053442e76250421cd15241442d9600c4309e594400425c63542429e181544c63d6494c30c758c544cad8604cb309b58854cc67960d53219d586544874d520c4308f590538873554440109e980548c65c6354021b5d85320c67461548309758c54086ac644ca219798c52042f161103109bd89544c3374354440d518d511026d6214c10ce150504cb5953cc0209d586544ca3c64548309d98654c82796014c219758e52442d8604c9309bd89518c31c53d0d419b988540c27661150208fd91534827b6054d218f990538863d65950108f59251c836451881209718d518826d62d5331cbd50524429d63d02409d98654482786054d21c7d53534427465505108f990514c3ca320c3209758e52c434f53d49419dd85544cb6b52d41419b596320863d6414810b918910042b960d0c408f9905304277654c4319758e548823c6454021ad5874210a5f6354021ce108505066f6254743e9109410872f54d4910d68c8504cb3a421414197d8
  | 2 => 0x450144200000002e0b25974001704000201f0182c003d008000070171243a059300006005580408041d84c0001000185a00890180ac800000520d0000c1010000043e0001048d600060142a00001f80004008580001000000aed008000421818041200068048205040000001bdbadbc010200a4365165081009026327600518000400028293a8d049a1b4240185070000100400170501400160604800160881004023b00408009e800004c0284c102d00ad410000404c1c00000000c00018a8060900824480000820444f000a8481302040403e1b8000002b00085c12040247219218106c03000365e6314940c754e4310a5f654c8329bd89544873854c41108f5925384357635444097d95310c63d659503197d8d51d0a6f654c8329e583540ca6d6214e108f593538865d63150208f59353042e9620c32097d8d5090af060507218fd91528425f6355131ced50504ca766194d20c755132cc23e6494720d3d4c525067461551309dd85529023e6414f209718d524434d520c830a7191320c63e64d4b10d314c524427a601502197997324c23c6454d209b58a53c434c53d4910cd150514835853d4141a7590310
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x400000000808001040000010000a8800000014c1c54314141c2ac6a8e80204c9768c830c828cb988428283a81086050421c8aa630a4010685644c8310870ca98c0a0e814c5c34354440c1ac8a90621862464185520c330308c0a9061615cc4250421a2ae6212a2205c0704c8310870caa0c0996612c5da4110310a62e0212a22064952580310c322318c4a8881895506244010838ecaa26418d487250c504caa4b8486a9061a118c4250421b08e89906210e0d6454b300c30caa0c099063981886054440
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x488487591320c421c81641c1320c421a81831086050421
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 6 => 2*((h/27+packedAt s3K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/252+packedAt s3K5 (17064+(h % 252)*10) 10) % 632)
  | 4 => 2*((h/206+packedAt s3K4 (17974+(h % 206)*9) 9) % 473)
  | 3 => 2*((h/30+packedAt s3K3 (1421+(h % 30)*5) 5) % 29)
  | 2 => 2*((h/8+packedAt s3K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffc07ffe03ffff03fffffe07ff81ffcff1e3f
  | 1 => 0x1fff80fffffffffc0fc07ff81ffffff31e3ff
  | 2 => 0x1ffffffffc07fffff0007ffffffe07fc1ffc7
  | 4 => 0xfe00000fffff80fffffff80001ffff83fe03f8
  | 5 => 0xfffffff0000000fffffffffffe000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc2530a2238912300b2ca9642a590ce4570e1b
  | 1 => 0x5488526644922462c05582aca0aa39493160ed
  | 2 => 0xa930a14889074895550224d14d354432c0b746
  | 4 => 0x31a2c58d12240ed9a69b301849c79623ea03b0
  | 5 => 0xc1c3060e1c3870ee38e3c71e70061843bdd800
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0c8c88080eaeae0e0c8c88080eaeae0e0c8c88080eaeae0e0c8c88080eaeae0e0c8c88080eaeae0e0c8c88080eaeae0e0c8c88080eaeae0e0c8c88080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38489
namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xc01c0041008000000a0800020700100208500700000000000004200000004000000000f180fd20ff32fd10fc30f421fd32ff20ff10ff31ff21fc20fd43be42ff42fe21fe43fe10fd30ff41f721fe32fc10fc32fc40fd40ff43fc42fe41ff40bd43fc43ff30fe42fe31fe30fd21bf43bc42fc41fc31fc21fd41fe20fd31fe40fd42
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2a6e00500040079300001030a000000a20389162c001000c30f0884000000048606b00800a040820008280080c0000d3d540c6e8a2994f94a42afa9a21b543c867aa7214fd5232f3290433e54043c843104fd51109eaa0653e52d0f3a86994fd5120cea1c61e4420867ea890f94c821bba8a657551d0b688410cf15120d2210437b504caeaa2205d946219eaa6633e540c2eca2186b948429f2a661b743c867ca998dd94742d6210437651ccabca7a07908420d6214433d540c3cc6410d714d10ae29a41b642c86eaa3994f14943ba28a8578504cabca62179d0821cea1e656e52cc67aa910ed50c21afa9a419d5310a7aa9105d145209f2a08775510c27ea8994f151329f2a4415d5310a7aa8085b548309f290853e540cb3ea6a1c754c42b7290615d53d03688590dbd4941baa8c4176511036e8610cf54c429f2a0637652086d8a4885b54b319eaa6653c548caeea2904f95332b6292833c544867ca910ed90821bba8a859d430c27aa921cf55330bb28c413c54442dea4886794c42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x100302c021005290a1d6395220a958c420870d4354830c9950218828d6310a21a919132086c56310821e158c420868d6310821a91923208695631082187195434ca856310821a558c42c86e0604c8219918951103866310821e150d32086a66290821a918943087194314132
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x80505739502188340a18c099043211d9434c821
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => 2*((h/54+packedAt s4K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s4K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s4K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xff81fff01fc0fffe0f81ffe0ffc3e03f678e67
  | 2 => 0xffffffffe000fffff001fffffffc003f87ff87
  | 3 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x530444624488208052925909180529a42c30ab
  | 1 => 0x852cc8a1c919499605b0ab286a4342a9658665
  | 2 => 0xa19114483a2922ab0413452b4a8051282db86
  | 3 => 0x2c51a20912301b4d29640610c7329603d00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06231823ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80eae0eae0ea80ea80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38489
namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x2102003001000000000080045080140043041900005000004001fd10ff31ff32fc42fc32fe42bc41ff43fd41ff20fd32fc43ff21ec21ff41ff10ff42fe41ff30fe20fd42fe10fd40fe32fd30fe43be41ff40fe21fd20fe31fd43fd21fc40fc10fc20fc30fc41ee21fe40fe30fd31fc31fc21
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x421bc41482fca5185fd5331be2a661bf4290afca1a1dfd5110de20a637e53c43da8310efcc841bf28e61ee21482fca620fe4c030f721265be414c7e88390fb50920bf29687ef43086fea818df15331beaa061ed318877c82a0fb14021bf29a417d5490fdca5a0ef50d42f7108417e548c6fea8195fd4d41df298837e548cb7aa8106f90420be298436c524c6dea498df54440bea9885bc53906f8a7085f14141bf296837d52d0e7aa998fec4110f72a0437f54886f8a0a1fb08540fa28a85ec410867ea890df54e21bf29865ec214c2fca0084f95210f7aa0437f53502faa9196f10610bf280617e5410efaa9086fcca41bf294877f53842f8a898fe44010fd986217e528c6fca318df15230f7994437d52d03dc8210fbd5221f710241ed53886fca3905f94c10bfaa641bf52907daa421df15320f7218437d5090bdc43086f10431dfa04817e5110fde84a15f54f40be28a81f75150af8a890df94e21bea9a21fb30042fea898ef90610f618c437c5050b7a84215f94630b7296837d5390bd86410ef94841bea84657c524c2faa6085f14e20df208637e53d03f480207b94e21deaa6637e540c6f8a8907b94a10bda82637d5210efaa9995b54a10bf28c81be50106faa420fec8220f7290617e5010af8a8995f15221bfa8265de304c37a6520df54b31bea88657d5090fde8710ef50f42bea9443ef210867aa990db54b31bf2a643dd300c2fca998df94031bea86877d53082fca3a16f10630bf280837c540c6f8a7885f54e32de20a43bc410c2faa5987b48020bf2a2657f524c2e8a2a16f4c841f7900417f50487eca2186f95032bf298437d54087da84995f15321f6a9061fb40502fca021df54e20beaa4637c548c6faa518fb90821dfa1085bc53106f8a4a07b4ca21f710a43f510043ee82a0fd90441bfaa241ec21d037c8290db54843bf28461be410c2faa990774c832f629263f6314437ea620fd48421bf2864375510c3f6a098dfd5132fd10041ee218c3dca010f7cca32f7a9263f531442fca71077d0e43bf28465be418c2fea9187b10c21bf29083bf43106faa6907b88430bf2a043f721486f8a9885f148109eaa065df534437e86a06f54841be29a857d549035a84215fd5330bea9c617e53d06fca120df94641de20a813e540837ea020fb8c821f719065bc414c27ca320df14941bf28883bc32106fea6906f107319f2a0617e54043d88310df14131bea8c87bf43906fca9997ec8120fc282637d52442fca9907b88540f7a9843be414c3dc42985f94342f699641be415037ca220df54a30df284837c53c86fea810df54342beaa0417d50c86f0a098df95221dfa1e817c50486fca690dfd5231dfa1c87ed52cc7e88210df94242bea8c617e530c7dc8310efd4241bf298875f534437ca9086fd0441bf2a263ed42086faa5a0df95121
  | 1 => 0xc53043dea4884f95032ef980617c54ccafca4186f8ca41bfaa261df310c77e8420cfd5131bf294837d518837e86a15f94f20f7296633c544c6faa520df94f42bf29481dd4310f7a8220fb90842fba0e43df4350fda8210fbcc421fc18021ee211037883985f54a40dfaa263bc42106faa898df95230f7a0c437e54106fca7215fd4943bfa8a877e50903d843907b88730b6a9061bc41886fea8087b50a21bea9e217d540cbd843887d8c431f718843bd43106faa3a1fb08640f6292217e518cb7aa520df54830fa988637d50087dc42887b08410b7290877f540c2faa3995f14910be2a4653e54cc77e8320df54720bea8c217f54ccadca4185f94c42beaa643be4350efaa8906f10510de284837e530c2fca5a05f14943fba0843be52906d8a4a0df15210f7a80437d5490afca8187714d10bfa82837f53042fca210df94032ee988637f525037a84a06d94441dea1083ec54086fca8905f54041bea8e85be418877c82885f94910b7a9221bd429077e87a15f94d10be29a437c514cbda6210fb50e21dea80837e5410bdea4a0df94a10f6a98437d51cc37e84a05f55230be2a065be41cc37a80205f15220bb28861bf52106faa2216fd0a41f6298437d520c6d8a4887b08420f7196417e5290b7ca8185f14d20ae29a21f621086faa9107bd0a21dfa16817d52102f8a2a1cf95321bf280417e52cc7da84216f95331be298417d51d03ce8210cf94441df208817e5190afea5087dc8621da20843ec428867aa8105b94421f6aa043bc41882faa920df55130bfa82857c544c2fca8107b14941d620c437e51d0efaa3207b88640f799043bc42907be6419778c630be28a85ee42482fea710dfd4810f62a4437d518cadca5085fd4520beaa661ee50887dc4310778c430bf28e657d54487d843087b88720d720c43be41882fca2107b14221dfa0081ed52103d843187ed0240f6a1641e651086faa818fbd4e21f6188437e51d02fca4206d10721de2a263ef318877aa990df54f41f7192417d510c37aa9087b4c832bf2a0656d52102fca4106f50b409e2a2217e50886fca1085f15010bea8663bc54442f8a2907d50441dea1e817d500cb7883905f94410f6108617d50906faa3216910421bfa8263bc41c42faa118ef90520bf29661bc50106fea9196f90731bf280817d52c43f460186f15121bfa9e41be40503de65196f55032df20e21be41c82fea6885f94432dea1887ec53887dc43886f10640be29c437e50882fea9086f90942be2a0417d53086faa6206f54241be2a043bc41043dca4206f10631f6990437c524c6fca7205fd4931bf2a621bc41082faa7a15b94840be29621be41903dca610df14a10f690843ee21043b863185f54a20deaa0617d53842fea9106f90631df208217e53103dc6310fbc8220ee18861bc52106faa718dfd4542bea9
  | 2 => 0xa020002a01b3a8080a8020302c7d012019c201800012080a01000000080b600026040004b0069e024000040004e018000aae6268200786acb834010000480000800240060007e3b00a02006008f6000032b803048021681800010280160081a00006008440580c2e008022440f15604812030ac000060300a0507e01958020062c8001c8302a006ad0000000800020fa01a0c016008b20c04202800028222a0000083e038940b02e038020380068934020000793c080a80302c59064001240c8021c0024380001002f70020080603010000000004a038420180012b165dad202820008040000657000008360082e0600a068f05d8240003c098201100424a42090005684e000010c0fa008301d84600006038aa07958dd87c0003e2e84a3bacc0b074050041c0060000c080241387e01000040080880002800268061987a358080405e0501c02002018d809822048020000e0300425034008e607000028e400800278464d8415880e100020700004016080360505c0005b7f53c86f8a099778c932df21883f610442fea0a1df94341be29a21bc529075c8210fb54b41bf29063775150bdc43a05f54221bf284877d53907dc8710df94430bfa8a657e528cafea990fecc230dfa9c83be43907de8210df95110dfaa221bc41c86fca321df55310bea9883d9300c3dca421fb0ca21fb98a63f7318c6f8a6a0ef0ca41bfa9621ee428cb7aa620df54e40bf28665ed50086fca310dfd5310bf29043f920082fea4a0ef54e41df19083f710043c88210fec4210bf2a441ec214437c8420df95040bea9487bc41087daa910fd8c710bf296217d53c83dea110f7cc631beaa443be54c86fca4087b54a10bea88877e5390fdca910df14d40bea9a437d50ccbdca210fb50c21fd080217d500c7de4310fecc130de20e81ec21cc2f8a7906f90421dfaa243f531c42dea4a0cfd5110f6992417e510c6fca010df15110dfa18877e53c877a86a05f94e41de20881f5510c27aa8187b90b20df20e81bc43107de8410fe50040df20e43bd43906faa8085b94b31ef21887ed50886fca3107b08520f6108817e54cc2fca4215b54b41bfa9e21be54082fca2215fd4d42bf284637d5010edca310df54f219e2a243ec43886fca7087b90a21bfaa243ec42087788720dfd4e20d6208437f53486fca4195f95130bf288813d54842fca6105fd4c21bea80857e5210efaa4085f55331bfa98417f51503d843105f14530be2a0617d50d06faa2106f90a41f719443be53907de64995f55110fba0c83de314c6fca9085fd4910fb884217f54083da85197bd0a42ef984617e50cc7f061885fd4530beaa2657
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1510c2ad6210c41e910421d023e6415030ab993318872d5494b318f592538865c63549109bd895110f2d52904408fd9151ccaea6014c21e994c41086b4614c841e9994410863f64544329758e544432e51904218f994544c66d62150319b59443086e66114e219b994524433b54d4131e98c8410873651107408f593530832d5290731e6105300c3a56510421a9986410866f6254740cbd52548863d65104209d18554482b661d4e41cbd48414c6ae6414c219b19532482ae61104218fd954310f2f54d4910ab993310866e62d5331cb5095010a6f6255131cb55320082ae6214c41cb148414c63c6454432cb153524434c534c9208f994321072d54480208f99641443a441085308f992544866e6214143e958c410872d5454a10cb552210c2f1610c310cb151424827765504419718d544823f65904309bd8951902e661d4c219b588540c32d54886109b18951d029d6314841d9944210c35b654c030a798c501072d52108419ed95100432d548c8329b98b540c3a654104218fd9441083a66110621ab98a53906796584010ce904504c6b66114c41ad984521063f65500409d98754cca6e6194840ce540501063c6454732c714c414426e6215330cb54841843695014021b9987538866c6254643c7d4e539065d6394910ad987529063e65151108f59053c863f65504419bd94211036565d04218f99250043645108540ad59441c867860551329b189544c67960152328f992544432c5290510cd191510c2e661904219b988548c23f6454720c7d4e414425d6315010e9908410872d52104408f990540823d6414a10ba980540872e51104219bd89518c26d6510e218f993538426c62544438f5905384354538c510e9104215026d6215130ae58041102b662944419b59442086ae6210e419bd96210c27960150219b98a544c6ae62d0641cd948410866d65084308f59053482ce63150219b98a53c426d658c821ad58732106ad640ca21d994421c832e5450a21dad42508863d6494d10cb54d4210b6651084209bd89544423c64547309bd95310866c65509328f99454486ad6214041cb951520c32d54086108f59353c866e6294010cb552210827461551308f992544c66d6215230cd144414825f654c431b958b41086e76510421cbd0d5210e3d6494d2197d954310e6c6254743d314e214423d6494b10da148504c66d6294e418f99053086b66190421b9984530863c6155032e914c410872e5494a10b9185424823e6414e109b189544c2e46150b208f992538863e64d4532d3d4e5388674654c510f2885300c26f62544409b58b538426d6294d109b9865210ee661d50219ed81534423e6494b10cb149425023e64150329b58b540c23f64544308f19151883655254430ad98752107a441140218f992528c7a56010421ab986410863d6494f10
  | 1 => 0x866e6215032cd153214872d5250040abd91310867661150308f99250887a4418c4219ed81534863e64149308f593514ca5d6314810e9106500865e6315010dad4b504c7355110430cb152214432e5488610b6580310c26f6508430cbd52214425f6354910e9104218426d6215010cb151428ca6d6294d21ce107504c7a46310421cb950218436852d4131cd944411032d5454b31cb952210827b654c030cd552510c277654c431e910421cc3a441484218f994414c6ae6294241ad191210863c6454d209d58453083345190540cb552520c26f6254743cdd905150a6d65908218f592524426d6588430cb952210c34f53d49108f993514825d6315320e910421082ae62140419e980548ca7a60150319b988535023d6414c21cb15021442e96015021e9104210426f65508429b98a539063d6494821c714d435023d6494a31d558453442b661cc8419b594211023e65105109b98854842ac644842197d8d544426c6114910cbd50214423e6414c20cb14a414c63e64d45309b98a508c6b661d4c41b618d10042e76150c21cbd50524426e6294910f4545300c36762544309798c52042ad62d06418f593538432e5290440e9944410866e6295310cd55041c866f6255130ab58843906e461509329e59430043a4410c4218f592530c72d4294442cb950210832f5410a219d584540c25f654c832bad8131887645108530cb948410c2756510421cdd44414c365518843097994534432c5414910b958642087375110520cd944410c2ad62d04419b59731087a74310421d68c4504c66e6294d10e9104210c3a44210421b6185300c2db654c0308f994414865e6395110e94c8410866c61548308f593514823f6550842c715353442756114e208f992520863d6590420e9107210863e6494c318f593514c32f5290541ad18542502746154d208f986540c26d62d4543c7d5353442d8604c431e990c410867761551209e580540c69e6314841e910421443356510721abd91210872d5290610add85321072e54084309dd8554486e664104218f594321072d54084309b588535027b60551328f990528426d6214e10bc18131c42eb604c4219b988540c27b60551319b98854cc66d62d5331ab5924210aaf6250441ab191310876651884309b189511023e6414f209b5885050fca524c030e950c410867960d4f21f4945300c2ac6250d42ced42509063f64546329e580530866d6214c10d9d085150b655108430ab59050086ad6494221c714e414423c64544209ed9520083646294430cb95152cc6ba6014841ce150504c66e6510e21c754c531066e6214e10e6551300c23f6454420d9944219023e64d4a10cb948411027a6095131d394d328872e5250a41e6905300c32d5415021d9d44214c26e61948309b189518c23c6454430cbd954210b1e5350e41dc18
  | 2 => 0x52904308f984544426e62d5210ba18131887665254430cb54841cc6ac6150842d9d8a510c23d64149309b58a54443a73210421cb15142c82ce63140219b98a509063c6454d21ab993210863d64942319b58a548c7665188620cb550420874f5388510e955041086e46150842e9104218826c61548409bd8954486776544010ab593210866c6254430b9597410866e6295231e90c8410866e62d4e108f990530427561d5332cb551520c3a66110421e910c410866d6588440cb151420867a60150219d987548823d650ca419b189544423d64d4a108f596540c2ad6414c21ab99032887a441cc421d9d44215023d6414810d654c300426e6215010ced50504c7365494430cb94a41cc66e6215020cbd4841442ad6214c41cbd50524c66c6154843ab59331886e56190c219b18951cc25e63153209bd9621102786055131cd946410c32e5494b31d314f524425e63150219798e534434d530c821ab19131886b46150842ae18143502af65508428f18554083a441086409bd895190e3d64940108f99641486e46150a32cb54b40103a76150842e958841087a66410421ba181310863c6454910d614f104436652944309bd89534872e5290610c754c431063e64d4c20e910421c43a66210421cd986511065f654c030b9594410863e6494f10ab58a539063e6494d109bd89534423e6195020e9d8c410874f53085109b98b515026d6294f10cd946419027761551328f986540ca7561d5030cd144414c23c6454d10e9d8041087655108640cd544418834f5314910e910421c823c6115110ce907504c7355190430b9d85420863e6494d219b594320866d6295131ba982214826d6295121cb548410c26d62940109b98a544427b65500409b588548436452d0541d9189510c25c6355110cd192510c2ae640c8219b58b515033761553218fd91518c32c5290541cb552528423d659503297d8d544823e650ca418f19151c82e46250441cb151424cba44154021e954c41086e96008420d6d4c30c43c9524c030ab59331087d2310c310cb951528423e64949108f596540832c54885219dd9521086b66114a41cd50c5150a776154d20cd551510c2ae6494e219758c540863e6414810e6951300c3a44108520e9504410866f6548421b658e300c2b46150b40cbd52214863d64141328f59053082e664944219b98b514c26f62547309798e524426f62544309b98853042e96014c21cb94841cc7a651904219b189519031f5414d10d354c530871c5414d10ae580521066f6550421cd9085150ae66190c21ab58a50907a461508429b195424826e6114910cb153524c72d52148418f99353c86786054d21ae982415026d62153309e98353c87a75310421cb948418423e6414e20e9d94410863e6414f218fd9151cc32c5414931cb94a410c2ac62504419b597410
  | 3 => 0x4b91b401120b80040306001188010b48f0100200c040000c30c1a084900013602402018a40543309624019e200800054ec090001c000020001040200c0e00000004040040f0283634010014001440005c0202c0215400170a40140f0001b51ce80040026c0300028104610380507cf8054b60b01c030060680a010060a0bf05000080140b00800c891141100802084121f8030000101c3525407124100000f12c1532c002580500045018232805102024328001489500000000000203302c0500002010000f812038010442002000128900150803059178000043000c061502a008270483e0280b0001824802000020f80800403014000000800c967400a0082a07c000002800074000030ac01004010b4020010305c00000040700700023104000181a00407000112740d2100c0404304c090002307000109970040827c0c01800cb551320ca3f6454620e9104218c32f54d49318f996414c63f6454d10e950841086e661d5221cbd4a52907a74210421dad48504c6ae62d04419b58b54843a46010421d5546310c32c52105108f990504ca6d6294241add85421067a6014c21ad98453906e8604c9209d185544cab561d0841cb50d5210f384114131e9194410863d6414f209dd85544c23f6454d218f185540c23f6510430d9986510866e6510c21ab59032087a663104219b189534433565104219d98453882ba6014c41d9146214826d6295310c7d4c414423c64546328fd96410834c5308510cd951510c32f5290510ab988431072f52905318f990534823d6414c109b994214426e6215130cd944418834c5314910b9984540863f6454910d9d885150a7561d5220cdd92510c3c8214c030cb550210826f654c832b358c500866f6548020cdd0c5150ba44108440e998041086a46150842ae580531063f6454d209b996214433665104218f596410c2ad64c86218f191518c26d62942319b98853082766114c109e582544c66e62150319d98453082ae6414021b9984548863e6494231e9105310873854d41318f59053883655294430d9d8552d072e5494830b358c54086ae64c8621ab592538863d64942219b98b5150fa441d40218f594410c2af644c6219b58b514c29d6314041b918543086ae64942219d987540c33764544309b58854cc72d
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x9116200030038c0104004000034102140018b08187910a3c016241464f17619cc6510421c48a830a85195247250c5150a9238a8528885435cc5450b208c8e2b10a898649535805308750b00c02084349dd44108420c1aa6b108620e2565104210c2933a6a210a61689c06310421a48e2a90822062765104210c3122a0c2a1641e0104214c030c4aa630a8421704531042144294b80a8a1043689c06510421a4ce3a94a520d2970151428cb06b1aa4290838658d5014041c48c8314a2186256510841086d1380a620843495d44108430b0ae63288210d4975085300c3122a0c2a1265491c45408510d0cc6208a010d2472544410c293396a220a61499d46310421e4082a80a010e245418542482533b0a620843495d46310421a48e2a12a02150d73151420869238aa8108618354d6214c41c52a8b00a810e29525804110342b188228043465d4414c030a4eea20842186856318c4108713b28821088183591530c821e22a8a8a601852471548410c21a38ac8292618a5915014021d4083b026210d2671d52548876030842980618a5496014841e0ea6208428860d6454c5308724b1aa028043619cc6010421d40823026210e27651854210ad0b80a620843685c06310421c52a8b0042105a1701944108712b28ca20843491d15108430c52c4a80a020e2464189510c252bb0a62084389dd46150842d20c220a60187055314c4108712290c2a1281491c55408420c32a6b00a620e0d5458c54087a0a92a298061615cc6010421
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x5a000033120000b0013a05831506150b20c057654c5310421e01631055014021a21801506150a32a20815516008420c21655c06510421c057558c6310421c81635c06310421c1175184414c030a20815496010440c05655cc6510421c81735806010421b0185104214c030d01535c05310421d0175104214c030
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 15
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
  | 6 => 2*((h/35+packedAt s5K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/301+packedAt s5K5 (21033+(h % 301)*10) 10) % 779)
  | 4 => 2*((h/258+packedAt s5K4 (28652+(h % 258)*10) 10) % 754)
  | 3 => 2*((h/35+packedAt s5K3 (4165+(h % 35)*7) 7) % 85)
  | 2 => 2*((h/19+packedAt s5K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf80fff03ffffff81ff87ff07fc3ffffb1c71ff
  | 1 => 0xfffffffc07f07ffe0ff83fffffc1c07ce7fe67
  | 2 => 0xfff03ffff8007ffff0003ff87ffe007f078f87
  | 3 => 0x3fffffff81ffffffc0007fffff87f80ff8
  | 4 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa6091189124108052824b448c1253490c30ab
  | 1 => 0x10a302287240a416058815093440851061d665
  | 2 => 0xa145b45120ed49aab04626d45ab40a67068b86
  | 3 => 0x858a288244880d4d2954808063292c06b00d50
  | 4 => 0xc60c30e3870e71f1ce6738e602303047df6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80eec8ea80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38489
namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc8004004008001a00100200000680049102a2c000000000000e000080002100003388701007080000000004080100015f54c03fe3201ffd0001ff10017f90c09ff50007f88007fc41017f50c09fd5200ff90809fd51007f44005fc31007f88407fe5400ff08001fd42027f94409fe50017fd0c05fc30017f14c01fd20017f8c005fc4301ffd0805ff32027f14401fd2101ffd0405fe31017f4c401fe1000ffc8005fd32027fd4405fd30007f50403fc2100ff14809fd50007f500057f5300ff0c807fc4000ff94801fe4100ffc8403fc42017fcc409ff54007f90007fc54027f55001fc10017fd4c09fc50017f94c05fd53027fd4805ff30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8c4003ff90a41057fa6588027ff5104035ffa0c401fffc864001ffe82a1017ff619005fff28a8400ff59121127feca90807fc5248415bea9e201bff94620007dc429083bfe5144007de20a8427ffd5221087f88708003fd410400bfe3142010ff90e10157fea4a08a3fe3250403ff90c4000bf1854010ffea3200abfc6550419ff98a200afd8c7100b7f8c690003fb10440317fb2a400eff551100dff8a31009ffd51884017e30a8409ff1441000ffe42a100ffd545000bffa002022bfd8d2102ffec70808bff304842bfaa8e200dffd051002ffe411000fff415003bff98a8001ff8ca210b7f8a690017f610440077e3224003ffd0a4001ff886a08b3ff6390445fe9824202bf18d200f7fca2a009f7e6588407ff21a8205ff19410087fca708002fd609040b7e31c200ebfd951000ff8431080afc63504217eb1c200adfd4f100c7f8ca90063ff65480037e3128001ffd0a2001df8c910803fd4284017ff90a2003ff5094102ffc410800efc6444059bfa9c8201eb109420e7fe42a002bfc63c405fffa8a842cff8c64102ff84090003fd4188015ff18e2016ff58d2002ffaa008003fe6048453feb1a8200b7d8d10007f8c110807ef2188401feb122004bf19520015fcc60806fff5188053fe98a822bff18a410b5fac6900a7fe535040bff9848005ffd401010ff8a320017fc300400bf79044000bf5931002ffc208800fff425003dffb2a800dffd091002ff8c9080abff655044dff2a44217ff1512001df8c890812fc655000bffa048005ff1031002ffa810807bff525000bff3244003ff5054002df8c608017ff2084027ff1962002bf98e21007dec488017ff408805ffe28a8415ff997100f7fea2a003bff5144007ffa028400ffd824107ff8a50800ffc409040bfc104401eff14540117faa690807fe2148401fea0a2000bfd812100ff8849080afe6348403fe2944005ff5941001ffe80a0033fd634401dffa822000ff90710087fea7080a3ff205040bff2862005ffd8c1000ff8411088bfe3048401bfb2a4003bf9901002f7c80a0017ff5090001f6a12402dff94241077f8a288003fd625040bfeb244016ffd0d20077fcca880bffd505080dfe1902023ff1052102ffe6108097fc5388407dfa1c8228ff1494100ffa4290017fc309002dfe18a400dffd0110005fac508027ff5204001dea128028ff1894100ffe6490803fe609042ffe3224005ffd9610117fa8690857fd51c40017eb0c4001ff9492109ff8438807ffc329005dfe1828402bf98d4202ffea11002ffe624400bfe184402fffd414217ffacaa10b7fd519040bfea84402bff0864102ffa6108057ff54c40013fb2a202bff8ca41007fac110803ff64c4031ffa8a4007ff10c1000fd84290816fc605080fff2182000bfd852002ffec808017fe6388031be32a4001bf58a21
  | 1 => 0xffd41900017eb148005fb0812002dfcc120037fe5444023ffa14202affd454112ffea710803fd6448007ff2a28004bf9964002ff84120017fd50900017eb224002bf18d400cffe87100a7fe6350445fe31a4201fec812002dfcc110077fc53500597fb1c8219ff14e2012dfec71084bff518405dfe29a8405ff0822002ffe8108097fe318844ffe2844201ff54a2103ffe86080b7bf5490407fa20c8200ff9062113ffccb10803fd418400bff320200cff14d10025fccb1085b7f5348001feb162001ff0814203ff8620804bfc518400bffa842025ffd8e2102ffec91003bff6544015fea9e2000ff88710005fec4a0012fe6584027fe2162001ff90a21015f8c688003fe60884093f32c4200f7d8d1000ff8649080afe63c402dff18a4001ff4ca21167fc6120817fd6584007ffa028205ff8c3100cdfac710003fd2104015ffb1e2008ff1501001dfec8a0802f761508037e314821cff18940015f8c788037fc6444059fea9c8201ffd492112efaa710853fc41c400bfe1022005ff08140015fcc70800afc6350801fe9062022ff94d21025fccb88003fc6050441ff29c802aff99541005fec89080ffc4190415ff9962000ffd8b1001d78c888007ec2088415fea1e202aff1454102ffac31004ffe52c400bfe314802bff94a4101ffe872007afd6550001ff20a4023ff99121117f8869088bfe434840bdfa048005ff1012000ffc649000fbf425000bff2824005bf19640107f86320002ff6150859ff9948222ff58d210f7f8caa0027fd54040017fb262003ff50a4002dfecb2000fff43508017eb0c8000bf98640007fcc0a102afe610400fff9882005ff0c2100cff86310023ff4104007dfa028403ff1524000ffa84908bbfc3150807de2048209ff9441001ff080a0017fd640400bffb148005ff54210177fcc6a1007ff5288001fe3028416ffd8d20007fa432005ffe544802d7fb1a4020bf58e400a7fcc9880abff5050445fe98a4203ff1514014ff860a08977f538840b7f304821bff552200d7f8a91001bff210400bfe31c4005ffd9640057fea788033ff4344007fe2a28418ff5452001ffe86a0007fd2188031ffaa2402cffd4e4100ffe84a1017fc50c4015ff31e201bbf59620147f864a0833fc314400bff30c402aff5414100ff84290077fc315000b7fb244005ff5881000fe843108b7fd5290425ffa94201dff18d4001f7882a0817f840900037f30c4203ff55240107fe6320017fe100401ffe1942027ff9422102ffec7200037f6544043ff28c8014ff1931000dfcc408023ff420401bfe2a22003ffd0640077eca2880b37d5390401fe90a8010ff4c610007fa4288002f4615085dff98a8405bf1961000ffe40908a6ff635042bfea962005ff99210005fac52080ffd545080b7fb102013ff90b1014ffe60a0817fe4084033ff9
  | 2 => 0x20067ec6288093fe5148415fa98e2028ff081411677a87208027f6550803fe10c4025ff4c22110dfacb2000ffe4390401feb024205ff58e2002ffca0a007bfd6550015fe21e200aff90f10127faa890803fd625000dff1902019ff8c620177fc62a1002ff644404bff9844200fdd8542117fe6290817fe6204047ffa0a4200ff18241087f863080127c655084fffb2c4202bf98e4002ff8811000afe6344019ff18a2000bf58b10037f8420800ffe4150007ffa048205ff10240155fecaa085ffc4148001fea16200cff18d10127faca9084ffc62c4013ffaa0202dff59641055fec7880777f5350021ffa1c2005ff58a1012ffc6110807ff214840bff2062016ff54d2001ff880a10bffe50508077f30c8205ff94240057fa638800ffe4190059fe98c821dff8c54017ffecaa1003fe6148003fe2124000bfd8141007fac910803bc644400bffb102000ffd8a41077eaa288007fe52480017fb162005ff8831002ffac720006fe6250003ff9924000bfd854016dfacb20803ff6150807fea148200ff9062002ffca110007fc428840bff30c8000ffd894000fdc64900b3fd63904077f3242003ffd0d41047fca8080b7fe6590403ffa124211ff1521000dfec490817fc40440037eb144000ff4861010ffaa32007bfd5150001ff30a8001ff5492014ff862a085bfd434803fff1948003bf9911002ff880a00bbff6350807ffaa48024ffd4521007fa8188017fe5044001ff882201bff54620137f883108bbfd6350827ff9062005ff59620007fc82880bffd5150825feaa42016ffd4d20007fa829080efe64c4057ff9048203ff1514100ffc6510007ef2050849fe32a4211ffd061000ff842a100ff7415044bfea9c4205ff98a100dffea910012fe6548407ff2a28413ff14b1015ff8a52080efc64c400bfe30c401cff8c940007f62108002fd64440017fb028401bf1891000dfcc520017fc504800bfe32c2007ff14c10077faa288093fc5148417ff1922010ffcc610167f8c720802fd6484047fe322421cff0854011ffe8090803f46150807dfa1a8001ff9092014ffe62a080ffe5490025ff28c2003ff5514102ff84008017fe6304001ffb04420affcc3100b6faa690016fe6088403fe9924000ff1854205ff842880b2fd6390407fea1c822cffcc241077fea88806bfe548800bffb242024ff54121057fa61880b7fc5090407ffaa28001bfd914202df8c09083fff2184003f71944202bf98d41005fac11080ffd4350407ffa0a8205bf1922000ffc4290007ff32884017fb128205ff18c10006fecaa10abfe5150407f7a128403ffd0941007fcc0a0897fd4388401ffb12822fef5514213fdea510816fc64040037f3148207bf58c10177f8c6a10b3fd3090441fe29c8022ff0c121007f8c2a00a3ff2150459fe9948226ff10221127fea09080
  | 3 => 0xf2842001ff4ca200a7fe858800ffc42900457eb1a421aff1062002ffc8090017ff1084007ff20a821fff94a4004ffaa408067fd5388007ffa14822dff1464101ff882a1003fe4184001dea148200bfd9221057fac788057ff51c4003ff2928401bf18b1002ff8c910016ff6384041ff9948012ffd52100057ec8880bf7c65508197eb0c200cff98d10025fcca08016ff6504001fea0e2003ff50e400b7fa6290003fe2104033fea1c400bff9491000ffe651004bfd518400bfe3202005bf1881000fdc64a10a6fd6350403fea124005ff88120117f8a690803be419003bff9928001fb08620037fc8408037fc4144055ff2828201fb0854200ff86510803ff604840ffe9902005bf1962001ff882a0077fd535001fff1942015ff14710004faca08073fe5250003fe1024201bb18910067faa68801f7d5304029ffa06200fff08610107fea72002ffc4244045ffb1a4201ff54a2001ff884a000afe6350057ff3148201bfd8120007fa8090033ff3244041bea9c8005ff1964002ff8a120007ee42480077eb24802effd4d42007fa4088002ff6244003ff214402aff54541007fec0a1057fd50c4003fe2924000fe4401006ffcc888097fe4388403ff9024024bfd9521007fec2a000ffd43500017eb224228ff0854100ff8a510817fc508800bde2028029ffd8d41067fa86880bffc5050819ffa9a201cff9894001ff8852085bed324802bfeb2e2005bfd8e20117fcc69085ffe6448001feb22200cbfd8d1008ffca908087fd5290007ff2148016ffcc120025f8cb10817fc30c40077f3224001bf18941107fa652001ffe310402bffa86201dbfd8d4003efea608003fe219002bfe32e201dffd4d4005ff8c4880b3fc3090401feb0a802dffd4241117f86290897fe5388401ffb244201ff5494216ffaa120817f7100400bfeb148005ff1411000ffc84a10677d5388045ffa1a4204bf9964100ffa64a1017fc5050007ffaa28401ff8862001ffca8a0817fe659005f7fb2a84049f99410176faa6a1012fc6550807fe21c8216ff4c12002ff8c708012fe6550807df2a2842abf59541175fec6a10affc329040bfeb1c2005bfd961016ffecb20857ff65c4059ff29c8213ff98b1012fda6510817fc208403ffe10c8010ff14e10007fac0a103bfd524400bfeb0c8001fec822013dfecb10833fd3244017ff212200cdfd4d100f7faa4a008ffc5448427fe1962020dfd4e4001ffc84a00bb7f5350801ff10a201ddf54d4002ff88008076fd635003bfe9928005ffc401002dfec508003fe2150053fe31a820cdf54d1000ffe4110807f72148403ff2944201fb90a2116ffea520857ff52c40037f3128200ff9041001f7e86a1017fe500404ffe32c4229ff14d4102df8c90802bfe53c40017eb244205ff8c120025fccb10027fd5104041ff18c8019dfd4e
  | 4 => 0x80efd649040bff9802003efd0a41007f8c290003be415040177b122000efd911001fee8320803ee218804bff98c4203bfd8140137fe83108177e650400bfe32c4029ffcc94113dfacb10807fc3248003de2128422dfd4d21025f8ca90817fe404404fff28c420cbf58d100effa62a0007ff205081dbe32a2005ff90140007fa8488017fe204403bff29a8018ff14520067fca688002fc61480257eb2c2015bf5971002ff8a108073ff2050045ff18a4200ffd814102ffa600800ffc5490401f63122001ffc862101ffe872087ffc5290015fe18e2000ffd891001ffa84a0017fd4088053bea9a8205bf18141015f8c72083ffe428405d7eb1a8429ffd4d41057fe878800efe6488403fe2928400ffd912102ffec710003fd605040bff1848004bf19641177da64a1063fe654800b7e3282001bf9891001ffea8a080ffc4050401f6a144223ff1012100ffe851084bfd5284059fe18c822aff14141067fec6880b6ff6590403ff1924200bf59220007fac2a102fff204404bfe21c4210ff4ca1000ffa8510803fe2184001fe90e2000df59621007fa808809ffd658840bfe1824001fe0812002ffe61100437d538405dff9828414ff15310025fcca90077bd4350007ff2128209bf5941000fe84290863ff504804bfeb1c4200ff9052105ff8a488057f651c4049ff2824227ffd462112ff861108abfd5250431fea82402fff195420e7f8a4a00bbfd305080bfe9848002b718d1001ff681200b3fe6390441fea9c8029ff4c94102ffc6008003fd4188411fe2082003bf992200effec6a0017fd308800bff32c401dff98d40015f8c690817ff61880097e32e2015ff9471003ffe6408077ff3050003f62944207ff50c10025f8ca88033ff3044003df2128427ff14621086fea708093fd514843d7fb2a8002bf98e2000ff84290816ff658802bfeaa62001ffd4920137fe811081ffd5304007feaa482009f5962102ffcc7200bffe6550815ff98e2005ff996100a7fe8388093ff544840dff2902006ff10810137fcc910856ff65c4059ff98c8203ffd064102df8c720097fd318845dfea9a8403ff1064002fee2108006fe62c404dfe3244205bfd914002ffa40080b7fe5190419fe9822010ff8c61002ffc60a0016fe6084031feb2a4016ff94d200effa60a0012fc655045bfe32c8213ffc871002dfec608017fc4084033ffa9c4001ffcc94200ff884a1077fd635000bfeb182005bfd892017dfacaa1017fd6590053bfa9a822bffc864100ffca51000ffb40500093e32a2029ff8c54100ffea510897fc6388403ff1928405ff8c11003ffea608003ff64440077f3224227ffd422102dfec80805bfc4348047ff2a24205ff140100c5faca90017fe308801d7eb2a2016ff90d20177fc60a1016fc628404ffea844205ff98e1016ffea320817fe629000bf
  | 5 => 0x330e61243701602416c0081003400415803014030a905304c0cc0024f0020000d8b00140000701303c0000000006800002801078014210000060ac0b000000094000222729081ca3e01801c000ea038004038020af0b40b02b004150020010020e402008000068308222560040800c0021540d02a0000040108700c490028003aa0180c8060620242190701a05c2b807252010000090003a4068100040180000f2360cc0080006000808000078000011a910203c0201c0021182d80003006001800176000d6038000020008010000f42b00c0ec000098040020401281c02408c0e0380000a40181703e00c00009000084140080000008107d18c000aa0220001240000300a014ab87d0120f8280040005880d85202a03c0180301603c1580005c0001180300a0444c0010002900480300203c018010040001b80804e01c020170a4a200483c00c0400885500207c1e82c00206c0000a00800c001720000002080000c1504180a00000407ffaa48205ffd8a100f7fea0a005fff40480037f31420049f1952002df8c5200affc209040bffb2c4003ef1064012ffcc7108027f6548031feaa24002bf98e4101f78a920817fc3050007fe21a8400ff5081002ff86088087ff529001dfea82200cf718d1014ffa60a087bfe655001fff294200cfd4c51002ffcca08017fc620400bfa8802000ff58a4102ffc8008007fc325081dffa922005ff18640117fea690807ff424803dfea828003ff10e400a7fca98801ffd31040077fb0a820eff1951003ffca608093fc504842dff98a4003ff9524100ff86510093fe654842fffa0a4026ff152210cffca710017fe2004003ffa928401ff10a2012ffe8710863fe5148007ff21a8010ff54e1002ffa8008043ff328400bfeb242001ffc852002ffeca0800ff4415040bbeb282024bf5952112ff86310817fe30840017eb12200cff90d1001ffc8720047fc4184001ffb224003ff90d42007fac120817ee2048021fea1c2019ff4c62001f7e8320812fe654400b7fb24201cff0c94005ff86488002ff6448003fea924219ff10e20147fcc4a0817fd1004003f62128401ff9092100dfec290867fe438800bff904802eef50d4200ffa6490803fc6048415fe29e2000bf9862002dfec72000ffc415040bff9002000ff58520167f8a7208a7fe3050445bea9a4225bf58e21005fac40803ffc42840017eb20200cff10d10007fa829003bfd6544041fe98c8005ff9022002ff8418801bfc52040057e31c4200ffd852002ffa4108006ff625082dff31a402aff5954102df8c7100bbfd315084ffeaa44205bf9801000fee431080afe634800bfe31c8003ff10d40177fca6a1007fd4288001ff30a8403ff50d4214ffaa6a0812fe655000bfd0802004bf99541007fac9880a3fe5250419fe98a200abf58f1001ff884a0
  | 6 => 0x200c00c0783d00201c000260da000058010120000582406e20c138000300100000a3aa000408000080840706e0000e40180b020094b707c0240380680b0680000f8010006401181032a020000010002fc0002700a008000040100200787e0ea00c6400f0c2000000b501a004011be0001100200e00200c0480700e000038960000000100900002c0101b1be0180000000004c1b0650380583b3980100402a80200e00c0b0510000040a00007a144138002560186a0060020000001400206c0000000c2d80102f032a4c000db0040500480005c05c5080100020048002000000160750060000000000c0340000b00a0243700101e000008000922c80102e004024
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf43596210067d53d854002e7d70594100067c31594102aef674d85420067f65c41100067f43d9520007e651189100067c64d95202676e758852101cfe7458a10006de74d8d10004fd7559121006be43d91200047d73d95101cebf64906200067c31d9542014fe7358a41004ff7458b100067f6518520006ed32d9120004fd7358a100067e63d9510006ee54d8910004ff73d894000eec6248110004fd72d8540277e720d854216dbc7550a41006ed32d8142004fd73591200067c62d9510014fe73d8540024fc75d9221006ec72586400067e43d9510004fd75d812102ef41058620006fb76440100e6bd4259220014fc73d89412c73c7550a41276f574d85420e6ee62d8940004fc715912009eee32d8b10046bc4159010004ff7318542004ff75d81210067c7359410007b65119110004fd73d931002eef725881002cfc705862006df9709854000ebe6250a410ad7c7550b10006f6519864002e75105941007cff7158910024fc755901026df671d92210067f755912109fac4250b1001fb66150a410067d65d8221007b5541854226ef6721854226ef521185420067d6590410006be52d91102e67e41d9542006f551185420057d7588710006ec65189100067f65981420067f659852002cfe7690410277b642d85422473c7550940014fc735921026ef5321854201cfe74d8520004fd7018542006bc651911015eee4258a410067f75591200067f70d95100067e71d9520006bf73d9110006f663d854201cfe745881002ef6109864001cef7650a21004fd73d81210067f53d8142004ff73d81410057d7518540007b97090640024fe75d89412e76f42d954226ef57218542005df7358540006de52d8d1000cfe72d931002cfc7059220006f56118520004ff7359120006df72d8d10005f9708871015fae6250a41004ff7558a100067f53d8141006ed30d8910006bd71d91100067c73d95102967f4259621004ff74588102167f42d9520006dc7359120004bf745862020e7e30d95200067e7518540004ff768864005eec6258910006df74d8d1002e7f70594100067d53d81420a6bc4159310136ed42d8941006de62d8d10005f7715894002e7d405941017d7c75585422aef454d85422e67e74d9542006bc6458910024fc75d91202aef654d85421d67c70d9510006ed6418910004fd755901005eec52d891001ebe64905212e67d40d9542006bf32d91101cebf6490610006ef6250910006f631986402de7d20d9542004ff73591212976e32596210067c4059621006ed75d89100067f535864020e7c40d9520004fd7558810004ff75d9120006f673d854201cfc76501100e4ff725912000cfe76505210067c651854226ef4421854226fac421854207ef621d8520006bc72d91102177820d952002ebe4059210005f771501100067c7559120
  | 1 => 0x854211ebf41d91211257c755912107eee3258a100067c6558910024fe75d8540276f621d854205eee52d891000eec6250b1006ebe64d9110014fe73d91200067c6598520006ed32d8910006bf64d8910275f771591210075c63d95100076c65d891015eec6290510004fd73d8b102e67d41d9542007b551d91100067f53d85400076f75509200067e6559221024fc7558b10024fc75d812104e7c71594100073f65d9110006de64d8d100067c43d95200067f655852005eef21d89100ad7e7588710006be42d9110014fe73d85200067e71d9542004fd70d854201ebc6490510014fe73d8910146ef21d89410067c435962109eec2158b1002efa76c41100067f53d9121004fd74d852009cff76484100067f3059621006ee65d8910006f461d8142146bf4259221004ff7158a40006df63d8910005df73581410067d53d814100fe66150a211d67e10d951015dbf7650a412167d20d9520006de42d8d100075f65d8d1001ebe64503102df3e42d9542024fe75d92210047d75d92210067e7359410246bd6550940044fc7159010024fc7598620006f72118540006bf53d9110014fe73d9121006f773d8542014fc73591101257c755812105eec42d891002cfc7690410006bc32d91102967d20596211d67c30d95100067d53d9121006ef7259110004ff7650b1027f6d5350a212de7f20d95420067c65591100067f53d8910006f431185201c6be4018540005fb7048510014fc735912001cfc74d891000cfe76d8910004fd76486400e6ec6250110024fc75986400067d31596210c67e76d952002dfa709041000ebc6250a410057d75884100057f75581410067d31d95200067d53d8941004ff75d85200067c65d8542006dc75d8d10004ff7359210276f532d85420067d71d9542006f5751854217d7e759854201ebc64501100ad7e75d8b1000cfc72185400067f539862001cfc74986200057f7558910007eb62c4110006f970d93100067d53d89100067c73d95420067e6598221024fe755822117e7e76d95420047f75582410247e76d9520004fd755822116d7c7558241007b554d8542006ec41d891001faf7250940024fe7559310014fe7359010004fd7358a40006f421d854019ff231c4110004fd73d89411b6ec2058221146ec62589410767e71d9510006bf7458620004ff7559220006bd43d814207fac4250a100957c7550a100febf42d912009eec6258b1002e7f20594100057d75d8b102967e7159621276f442d8542007ad42501200247e76d951005cfd768861011ebf4358a410067c645962126ef732185420067c71d95200bebc6448110276f472d8542004ef725911000eee628841001dbf725094002cfc70592100e6ef20d89400067d651822100ebc76509400047d7518540006dd74d8d1001cfe741852002ff361c41100067
  | 2 => 0x6bf64501201cfba7090640006bf6519110136bc64592212de7f72d9542005f77150310014fc7359010014fe7359121007e47150a211c7b41019110006f47159120004ff735881000fea60886201eeef6350920007e9708862000cfe72986402de7c74d95420067c3159621006ef73d8910005f77148110006ed6318910005be76191100bebe64d9120006bd6319110005ef72505210067f41d9510004ff7558a40006f53198640006ef32d8910007e53218542006bc745862002ef4109864006cff74591101aeec201852000cfe72d81410067f5358241014fe735911009efa20d81210067f535912102dfb7144010024fe755881000cfd769062100ebe6250940006ed74d8910024fe75185420767c71d9510004ff73986200a6be64d93100e7af205094026ef4321854226ef64218542006f7419862001cff715901015eec2158a410067e74d9520004ff7648640024fc7559221065de76d8d100067f5359120014fc73d8121066dd10d8d102de7f74d9542014fe73d8141006bf54d9110014fe7359221004fd73588101977b5344010006f761d8142004ff73d91201cebc70d91100067d535824101cfe76d91200067f7359410024fc75d911026fe442185422de7d42d9542004fd72d9110006f551d8542024fc75d91210067d65906210067d65508100c67c65481100067f659052002cfe70185200067c74d95201e77b53c4210005f7715814200cfd70d9120004ff73d89410077753185420067d5359120014fe7358640006bd43d9121004fd765081027fad4350a2101ebe649062120e7c10d952006ebf40d91100957e758861002cfd7218520004fe76505201977953440100067f30d952002ef6105864002cfc7058810004fd75d91201b6ec20d8b10276f652d85421bede40d8d10006bd53d9110006bf6450b1001cfc7650310006f6319862000dec725062001eae6450a21006ed51d8910006f55318542066dd71d8d1001faf7250a410067d43d95100067e64d9520004fd70d9221004fd73d9121007b870509400bebc4158a40006dc63d8910006df40d8d1000775531854226cfe71d92211e77953c42100067d6550410006ef648852100eee6150a2102eee2058a100247c75591102e73f40d9542006ed32d8941065dc735891002e7d3059410024fe7598640006ed73d8910274ff71591210067c6558520004ff75d93101a7f251c4110004ff75592211f5ef7350920006ef62485100067c6518520007d551d8d100057d758854002efa60181210067f655012000def7450a21007ad4290520004ff735824101ebe64907100067c7559110024fc75588100d6ed42d8940004fd755922001cbc74586200067f65d911027f6f5350a21004ff75591102de7e72d954205eee62d8910006ef62885102966c725962101ebe649041026ef6521
  | 3 => 0xc62509100067f215941005eec32d891000dee71885212167e72d95201cebf6390640006dc21d8d1001ebe64508100067d535912122f6e758862002cfe70d8910006f461581420057f73d954200cfe76d89400067c42594100076f6550920006ef53d89102de7f21d954211ebc40d9121006bd6490621005f471501101cebc50d9110006ec75d8910004fd7690620024fe7559210006f573d85420067f6550520014fe7318520007e77150a2102df870505102976c20596212de7c42d95420047d75d8b101bedc50d8d1015ebf42d91210067c73596211cfb66190640006f475d854216e7c65905200067f42d9510006bf51d9110006ed53d8910006ec725911013dee7550a210069c64d8d10007e532d854201ebc64505210067d72d95100067c63d9510276e672d85420067d63d95421d67c40d9510004ff7058a411bede20d8d1000eec6288610006ed32d9221006cc631891002e7c7059410014fe73d8b10005df7358121006af64189101d67f71d95102b6bd6350a410067c4159410006f96018121006ee75d891000ebf7650a410f67c655011002e771059410006bd6519110276f642d8542006bf31d911001cfc74d852008ebf415921002cfe76886400247e76d95422ceb7431854216e7c6590510007ac64189100069c63191100a4fd74d93102cef75418542006bd70d9110006df51d8d100067d7359621005f4715091002cfe7690620006f553d854200dec7250120014fc7358810006ed651891025f6f53885210bebc43d91200067f63d9510004ff7358a100067f53592102cef64018542014fe73d81210067e72d951002cfc7058640006de72d8d1000cfc7648110006f77318542006f77518542006f753d8542006bd4359120024fc755824100eec62886400067f53d9221006bf6490520004ff75586200067f745962100fe67188521006f65198620006ed72d92210f67c6550120006cf631891000cec72591100067e63d954201ebc6450510024fc75d854002eec2058a40006df54d8d100a6bf40593100bebc6459120277e442d8542146ec6250510006ed64885210067d53d8940024fc75d8b1013e6f7259621006f441586200067e31d95102bdbd7350a411d67e30d951025f6d538852101cfc7458b10004fd7359121007db7344010006ef65189101d67c20d9510006776518542007b54318542024fe7558241007b53119110004fd73591101afe41018910197d87344010024fe7598620007e531189102167f20d95200077553d8542006f473d854226ee63218542006bf75d9110004ff72591100067c31d95202967f2059621004ff7559210014fe73185420067f53d8941276f732d8542006f770d8542006ed32591200247e7518540006fb6098241004fd73986400067d535921000cfe721854013eee6588521007bb7444010
  | 4 => 0x95101d67c10d95100065c65d8d100777471d9510007e862c411026ef6201854202cfe7058810006f665d8542005ef7258141024fe75586402a73d5390541006ef54d891001eec64509200067e65d82210067e64596211cebc4058241007ad6250a412a6bf639054124efa40d814206ebf4258241007b864c411006cfd76501100067e75d8b1001eef7650a211b6ee40d891009cff76884100067f32594100a6fa40d81410057f73d9510004fd7318542004ff75d8142006f761581421bede50d8d1002cfc7650a100067f725941008cfe76905100067c7559121005fb7050510014fc7358a412de7d72d95420767e76d9510006ef40d8910004ff73d91210067d531854205ef52158620024fc7518540146ee3259221006f4631854202cfa76c41100757c7558910007af645092002cfd71d89101b7e66188620137af4350a21014fc735891027eed6350a2113e7f76596210067e6558221006f970d8b100067c6518142024fe7558a4100dee7250621005df7359120006f475185420067f43d95101cebe20d9110024fc75d93100f57c755854002cfd7418540006bc53d91100067d73d9510004ff73d92210047f7359410006f671d9221006bc745891001ebc649062002df976c4210006bd61906402167d42d9520037ac42508100067d65884102aef754d854204d7c7550810236bf63509402df6f20d9542006f73118542005ef725854000cfc72986402967d42596212a6bd6390541004ff73d85202d7ac4218142036f521185200067f655891002cfe70d91100bfac4150920004fd75d8141005f77150910274ff76506210247f765962102ff2614401019ff131c4110004fd73d9110006dc74d8d102177b20d95200057d751822101cfc7158a410067d32594102de7c72d954202ebe40590102de7e21d954221d7e76d95200067f53d852004e7d715941024ebf43d81422aef640d85420067c6359621006bd54d91100a6f641986400247e75d8b1005eee42d89100067d53d9221007e551d8910004fd73592210067d6548410006ef62885400067d75d8b10146ee42d89411d77610d951001ebc6450910006ee64d8910006be32d91102aef740d8542006f4731854200cfe72591102de7d32d9542006dd54d8d100067d7359410276f432d8542006ed6250810006df75d8d100076f65d891005df9709852002cfe7018542006bd43d894000cfd74d8142007b543d854201cbc74589100077753d854205cfd70d891000cff76483100067f53d8940006bc21d911013d7e75d92210feee32d9120005f97088410006ec64189100067d3059621004ff7358640006f66518542006ef725864015faf2050a41024fe7558a101cebf64181410067d30d9520004ff7558640006f441185200067f6559110006bd43d92210067d65506210077631d951000ee
  | 5 => 0x1b6ec70d8910014fe73d8940004ff7259310006ed628841002ef4105864002cfd74d8940276f774d854202cfc7650810004ff751854000cfe7258640276f672d854202cfc765061011ebc54d9121056dc63c4110006ef31d89101d77771d9510024fc7558a41006dc51d8d10006f650185422967f21596210067e73d95200047f73596212967c4259621006ed325881002cfd7058810006f53198620004ff76505202167f21d9520146bd425922100cfc74d89400247c7558a10006bf64c411002cfc701852004d7e7588410006bd431854202cfe76884100076d32d9520006bc62d911002eec2058a1002cfe70d9121006f531586400ffac4298142006f45318542004bf74589102167c42d9520006ac64d89100247c7559120006be63d9110014fc73d8940237ad3250940004ff75582410e5ec725854002cfe70d922100eec6288510297772159621006f450d854202cfd72d912000cfd768841002dee70509200067f6550110007eb72440100067d53d8542006df63c4110006f450185420047f7559120136bc648851016ebc6590541024fc75586402b73d5350a4117e7c6550910004fd755911002ebe405922002cfe70d8542004ff751852000eec62485101557c7558141066dd70d8d10006f761985420067d535881001cfe7690621006f463d8542006ef7259121006f751d854211ebc64485100067f53185420067c41d9520206ee32d814202eef7258a40006be6219110004ff7358b100067f53588100067f65d814202ebc4059210006be43d911005cfd76481100057d75d8a4102fb840501100c57e759852016e7e6590410004fd7358a410067e651822101fb67190640006f731d854202ebf4058a40006ee65189100f57e7518540014fc7358221006fb7059120006dc62d8d10006ed3218542006ef75d8910005fb704861002cfc76884100067f5318540004fd7558a400076c65189100067c43d951002ef671986202967f725962101ebe6150a4108ebf4259210014fe7359310006be6519110034fc7158810006f565185420a6f541986402373f53509400067c6598142006f77159121004ff76508102a73f5390541004fe71d81422cef55418542024fe75d85420057d75985200073c65191100bdbc7458520006bd4359210004ff7159120004fe7688540004ff7558a410063c65d91102967c7259621014fc735922026ef632185420067f654811001cff76503101ff6c6550920024fe75591210067d531854026ef472185421567c65505200067d53d8520004df7359120276b574d8542006f976c42102373d5350940014fc73d91201567c655051002dec705092002eed2059220004fe71d894013d7e7518221005ee7618910006f551586201cebe50d9110006bd43582412de7d21d9542004fd7558a4102ff371440100067d31d
  | 6 => 0xd5359310146ee32d8941005f47150b1001dbe71905412167c72d9520004ff7359310006ec53d891001cfe74d8b10136bc415922102cfe705901002ef77158640246bf65509400067d63d95100057f755912016e7e6590621004ff7059221024fc75582212b73f5350a4102cff72d9120004fd73185400c57c7559120014fc7358a40004fc765052006ef641586402967d7259621005df7359110006f96018221006dc63d91100067e425941001cfe74d89101bedf71d8d10006be31d911006ebf41d91100057f755911000cfc72591101567e6550410276f632d85420067f65905100079c63d9110006f650d854208ebf435921000cfd74185420f57e7588540006df41d8d1006ebf4358241006ef7258b102967d32596212167f32d952002eef7258a10005df735891011ebe64d9121004ff7558b101cfb561906401a77865c41100076f7550a21004ff75d85420d6bf43d8940146ee62d894102efa60181422967d715962101cff7650521007b4715094000cfc7259010006df64d8d101b6ef6218121006ed54d8910006bd52d911002cfc7058a40006bf74589102de7f32d954226fb7741854202eef2059220006bd72d9110004fb764401005eee32d89100076d32d954202cfd70590100bebf4359120206fa20d81420057d759814215eec21d91210067c31d95102aeb674d85420079f64d8d10014fe7358241006f771591100067f53d8542024fe75591101cebe10d9110024fc75d894001cfc7458a10004fc76905202cef6431854201fba60906402de7e42d95420bebc41d9120006dd52d8d100067d63d9520006f651586400057d7598542006f561185420febd42d912009eee62d8b100067f53d9110066dc71d8d10006f453d85420067c7459410006f75318542006bc75d91102967e2159621005ef7150a210067c3259410014fe7359210004fd73d81412df6c42d954200cff76906210067d6559221136bf43d92210073f53d91102aee572d854205eee71d89100067c41596211bede10d8d10006dc73591102167e21d9520014fe73582210067c74596210047f75591210067f65d9120004ff73d8121004fe76509100067d53d91100067f30d9510004fd71d8940024fe75d91101b6ec50d89102967d21596212de7c32d95421cebc30d9110007ad429062101cff7650120004fd7298640187f25144010005ef72506202167d21d9520006bf629054100cfe7259310006f565d8542005f77148310004ff75986202aef554d854200cfc7259210024fc75591100e6ee42d89400073d53d91100767d70d95100075c75d8d10014dc735911002ef41098620004ff73592212b7ad3250a41014fe73d9310014fe7398620006bc51d9110006ed4258221006dc72d8d101dff251c42101bede70d8d10006ef51d8910285ef7350a210047d7359410
  | 7 => 0x910006dd75d8d100067d71d9520007bb7050940004fd75d922105eee76189101cebe30d91100bfaf4050920006f451d8542006ed3258221006ee43d89100067f75589100076f6518910004ff7650a10014fe7358810007e55118910006df70d8d10006ee64189100eddc735854002dfb7644010006fb60981210057d75d9221006f6311854200cfe72d854001cfe7458221007b77150a4102ef761c411002ebf7459210004fd76506201bedc20d8d10014fc73d891000cff7658b100eddc735894002df87050610014fc73591210067c64d9510006bc64d8910004fd75d8940007b5511911001eec6450a210067d5358221004fd76905200065c63d951001fb76190541006f6751854211ebf43d91211bedc70d8d1020e7f72d95200073f6519110006bd64905210e6ee325912002f796544010014fc73986400067765d85420067f65585420067f6558142006f63158640006f570d854225eef63885210f57c7558940006f55198640006f765185420067d30d9510005df7358940014fe73d8941024fc75592101b6ee50d8910005f77150b10007b7715094008ebc545921006ebc4158640005df73581422e67e40d95422cef67418542006f563d85420066c65d89102276f53886202ed7e76d95420057f7558940006f763d8542024fe75185401c6bc401854013d6c7550a210057d75182410067d73d95420065f65d8d10005f4714811026fe6321854200cfe7650120006ec74d89100067f655051000cfc72d9310146ec215912123dbd7350940004ff7458a1002ebf745901002cff7058810004fd735901000fe6718862000cfc7258241006de51d8d100067f5358221004fd7518540046bf421854000faf7450920006f4211854013e7c658851002e7d105941016dbe7550a4100eee6248310006f7219864017e7e65508100067e75d9221007ad4288540006ef7259120005f471503100067c71d95422aef643d85420067c73d9520135ef7650a211d77410d951026fe472185422967c7159621004fe7690520006ef6250b100b5dc73591200057f75509100077531d951002e7e40594101267c65485100a6bc645931002cfe709862002ef610986200a4ff7690410006f6761854201cfe7458620005bf7458520006bd43d9110004fd75d9110004fc7650b1005ef62158620004fd7559221014dc73591202967f325962100cfe72d911002e7f40594101ff6c7550920004fd75593102e67f40d954202cfe76d8142145ec72581410067f7359621006f43018542014fe7358b102167d32d95201cebe40d93100047f755891002cec76509200067c65d9120006f741d8520007b47150a41006f763185420073d43d95420bfae54509202afb743d8542024fc75d8141014fe7358a10006f731d85200067f20d9510036f6211852001cfc71d91100067
  | 8 => 0x6bf74591102e67c41d9542007e87244010004ff75d81410067f5358910006dc635911000cfe725901001dbc74486402aef543d8542006bd43590100067e63596212de7e32d954202efa601814100cec72586400067f635962101cff7659310006ee31d8910006de75d8d10046bf4318540007b87444010006f630185420067d725941001cfc74d8b100067f5358620004ff7648540004fd75d8941007cf63d8910004fd73d894009dfb7058520006ed6188620004ff75d8540014fe7358a40024fe7558a4000cfe76d894116ebe65906401cfb610d9110004fd735862001eee64509201b6ee10d8910006f73118520137ae5450a2106dbe76d9110004ff7318540004ff73d81420067d5318520006f765d85420076d6550a210067d53589100075f75d8d10067d471d8d102cef74018542066de76d8d1006ef54158640004fd73d9221005fb7050610004fd7688540137ae6450a21004ff7458221024fe751852002cfe709864005dee76d89100076f53d891001ebf6050940006f830d8142024fe75d8520006bd73d911001cfe76d91102de7c21d9542006f673185421bedc40d8d10014fe7358910024fe75d8b101b6ec30d89100067f53d8b10006ed42185200067c7558241004ff73591100057f7558520006f651185422967c32596211bfd610d8d10014de76d8d1015eee32d92211cebe70d911000cfd74d854206ebf42d91100067f5359110007e8705092025eed6388521006ec51d89100067d5359110006f76198540276f474d8542004be7619110004ff72582412967e4259621006be51d911000eee60886200076d53d891004e7f7159410006bd4318540004f471591200067f5359010276f572d85420067f31594102167e42d9520004ff735891002e7e205941002cfc715931009cff7058910006df42d8d10006bc63d91100077765d8542006fb7058910005f47150a1002cfc76485100067c63d95422276d53886200067f65985422de7e20d9542004fd75d891009cfd72d8b102976c72596210047d73596210067f5359310004fd73d912001cfd71590101567e655062102dec7650920005f77150a10004fd75d8b1002ff271c421002cfd72d85200067f31d95420e6ec21d8940006ef62c41102967e725962115ebd42d9121277e672d85420067e3159621006ee73d8910006746518542006bf64505210067d535862026fa4421854200eec6288540004fc71592202967c2059621004fd7559210006ee63d89100067e65d9221036ee4258810006f77159120006bf63d9110006f430d85420063f65d911008ef641d8540014dc735891000dee71886202176e42d95202cebf431854200cfc71592210067d5359010014fe73d911002df671c4110006ed62483100077765185422de7d74d95421cebc20d91100beed4258a400067f655
  | 9 => 0xd6450a21297742159621024fc7559310004fd73d81420067f65885100067c63d95202167d70d9520024fc755912002eee2058810007b651d9110006ee51d891018efa61440102bdbf7350a41004fe764854001cfd7218542006ed6488620005f571981421b5ec7050a21006bf644811011dbc7458121007af62509400057f7558142004fd73d8520006bd31d9110006f575d8542276f552d85420067e7159410276f720d8542276f620d85421cebc10d911017d7c7558142276f420d8542014fc73d9110006f75118542006ef5258a10006f45118542006f57318542005f471591200067d32d951006efa405824101dbe719064026ef742185420067f5358a400067f654851014ddc7358141006f630d854220f6e20d95202cef54118542006df63481102cfb74318542006f4419862000eef60509200067f53592202cef54318542006bd4258241007d651d8d10006f651d8542024fe75d8141006bd6450a10006bc65d911026ef552185420047d73d9520004fe71d91200057f754811009eef2058b100067d73d95200067f655912001fbb6050940006f77158910004ff7398640004fd73d85400067c72d95100b5dc73585200067f21d951002cfd7688710004ff745862013f6f72596210067c65d8910004ff731852002cfc705912126ef452185420067c7558a1015eec6258a4111ebc6459121004fd73582210067f5318520277b574d85420057d735962123dbf7350940014fe7359120004ff7558810006ed43d89100067f40d9520014fe735922008ef541d85402cef44018542006dc65d8d1006ebf43d91102e73f43d9542006e532185421f5ed7350920004fd73592102cfb654185420067d53d8b10004fd70d8941006ac6418910006ed3218520006dc63589100047d73d954226cf671d9221006ed32d8b10004fd75d9121004fd75d8540004ff73d8b10024fc75d8142277e632d85420067c42d9510006bf64589100057d7588640006f960181420067e735962115cfd72d91210057d7588510006f6701854200cfd71d912101cff7659221014fe73d85420067d5358a4013e7e6588410004ff7559310006f761985201a7f151c4110137ac4150a2100cfc76501200077b65c4110004fc7158a401b6ef62886101267e6548410014fc73d8142136bc41d8941006dd64d8d10006be53d9110006bd6450610004fd75986200067c41d95100067d5359220006dc7358910006ed52d891001cfe76d9121006df6358910006ef64d891020e7e40d952000cff7658a41007b631d91100067d7459410007cc63d8910004ff75d89400067f4059621014fe739864000dee72906212167c32d9520004ff7358a41004ff73d85401bfd771d8d10277a442d85420067465d85420057f7558241006ef41d8910007af64d89100067c21594100067e3259410
  | 10 => 0x9542005f671981420757c7559110166dc639051000cfc72d85400066f65d89100047f7558a10004fe7650b10236bd63509400067f53d9310006bf6490510276ec21d8542004ff75d9121006f741586202967e32596210067d74d952000cff7648110004fd71d8142006f9601824115fae3250a41207ac42d8142006f631586201b6ec40d891002dfa7088710006ef42d891002e7c3059410004fd7558b10004ee761891026ef520185420067c74d95102167e32d9520014fe73d922101ebc649052001ebf6190541276f742d85420e7ae32509400067c30d9542006df6390510006f55158640006df50d8d10006f53118542006ed6250a10144fd74d92211b6ee70d89100067d6598221005f47150810006ec63d89102afe572d85420067d53d9310006f551986200067f73d9520005f4714831029d7f7659621006f461181421bedc10d8d100067e62d95100047f73d9510004fd73d89101877875440102176e32d9520006be75d9110036ee325881000cfc71d8910004ff75591211ffad5450920014fc73d92212967c215962100cfc72d91100047f73d952002cfe7650a1002df870485100eedc6350110004fd72d9310006bf64501102167c21d95200057f755854202cfc70590100067c65d814200cfd71588100067c7259410006bf50d91100076d325962102e7f10594101cebc659064009ef621986200067d751854006ebc54d9110004fd755891001ebe64506101b6ef648862015fac2150a4120e7e70d95200247c75589100757c7548110146ec20d8941005f4715894026ef77218542006ef63d89100067c70596210067f63d9542006bf72d91101b6ee30d89102573d539064001ebc645012000eee6250a10005bf7150a412967e205962113e7f71596210757e76d951009ef521986202cef74318542004fd73586402aef440d854202ebc4059010006df6350110046bf42590100067f32d9510006dc54d8d10024fc75586200073f755094020e7e20d95200067d65d92210067e73d95420067d30d9542036ec215881001cfc745822126cfe769052107eec5258a10004ff7358a40274f77159121004ff75591200067e43594100067f31596210247c755912126fb442185420067f31d952000cff7158810005ef7259110024fe7559120024fc7558a10006ed70d891006ebc43d9110006ed3258a400fcff7459120006f5611854000cfe72d9120014fc7359221175dc73581420057f7558941004fd7598640006bf30d911001cfe71d91102976f21596210057d73d95102e67e43d9542006bd43592202afb654d8542277ac42d85420b6dc6348110256bd639064001cfd72d85420e7ac2150940006f960181410057d75d8221024fe75d814205eee4258221004ff75d9221004fd735891026eee321854226fb474185420067f6518542007a
  | 11 => 0x6f421986400067f53d81210feee4258a400067d75d9221005bf74581212aef443d85420065c75d8d102df2c42d9542006df65d8d10004ff73582210067f5358a101b5ed7088620006f730d85420076d758852113dec7550a21006df52d8d100c57c7558520006bf74592211ef6d535092026ef420185420067d43594100067f63d95201ef6f53509200067d539864002cfe70d8941006f65158620006f57018542006ed64d8910004fd74986200067d5358a10004ff73586202c6bd6550a4109eec62c411028f6c7550a21204ff70591200067d5358b100067f65d8542006bd63d91100067d70596212e67d43d9542006ef43d891026ef57418542024fe75592212cfe742185420073f7550a410067c32d9510006bd6490710024fe75d8121006ee6318910014fc73d85400a6bc64c4110006f431d8520276f520d8542005f77150810006bd43d931020e7c70d9520014fc7318540006f74118520006f531d8542004fd7650a10006ef725891013d7e75d8221006bc621911001cfc74185202167d72d95200a4ff7059110006f470d8542006be631911000cfc72d814101eee6450a21024fc75d894102ebc4059220024fe7559220006f76118142036ee4218520006ee53d891011eed4258a41004ff73d9110006bd75d9110004ff755891002fe8204811016ebe6590541004fd7558620006be72d91100e6ec6258940004ff73d891002cfe7058a40004fd7518542006bd6450310006f775d8542014fc73d8141004ff72592100e6bf42592202cef54018542006bf20d911001cfe7458910004fd75d85202cef4541854201cfd70d8940004fd74d89100067c6559120006f653d8542006f75018542046bf4359010136be64d922116d3c7550a410067c75589100067f4159410004fd75d8142014fc735931001cfc7458620004fd7518520006ef70d89101b6ef71d8910006bc31d9110006bd50d91100067f65d8520006bf70d91102e67f41d9542004fc768854002cfd71d911026ef77418542006f670d85420067e3159410006df20d8d10004fd75d8542006f65318542006f461981420067e31d954209eee42d8b102df6e32d954202cfc7158b100067f7459410006f721586402aef743d854200feb60509202573f5390640006bf7459120004fd7358241006f4701854202e7e1059410006dd50d8d100066c651891001eec7650920007e631d89101b7e610d891001eac64509200bebf40d9120066de71d8d1001cfe7498620006f675d85420067f7558241004fd73593100057f7550a10277b442d85420057d73d95202cef4431854200cfc7258640004fd7650b10006fb70591100063c6519110006f7301854201ebe6450a102b6bf6350a410057f7550b101cebf71d91102afb674d854202ef61058620006ed71d8910005f970907102df6c21d
  | 12 => 0xd75591202cdf671d8a41024fe75d89100067f7059621024fc755922005fac4250910014fc7358640144ff725912102e7e3059410006bf54d912100eae6250a41006ef50d89100079c6319110176dc63509100067f5358a411b7ea708862000cfe7258241005bf744864006dbc745891026fb64218542007cc63189100067553185420067c655854201cff76501102cfe77218542006bf645091024dfb70589400067c3059621006ef625011001ebc6450b100067e73d9510006df7359120006ef74d8910004df735911000dec72505210077465185420067f73d954200cfc72d9120006ef64189101d67e40d95100067c6558142006fb6098142024fe75d8940004ff7598640005f471581420a5fb705854013eee6588620024fe7558b10006f750d8542004ff705912105dec72591100047f755911001ebe6090640007af6418910006df63509100067f40d95102de7c20d95420076f53189102976e425962111ebc41591211efad4350920006f671d9310004df73589100067e435962102cfe76508100069c63d91101bfd410d8d102afe742d854207cfe76885100067e30d9542024fe7558620205fb70591200d6bf4359220024fc75185200067e7059621004fd71d91201b7e56188620006ef30d891002f7a6544010006dc64d8d10004ef725864001cfc74d8121006ed6288710007cf6318910006bd30d91100063d53d9110024fc75d8910006dd72d8d10006bd65d911002dfa709071005eee3258221004ff76506200067f71d95200069f64d8d100247e75d92210079c64d8d101aeef6118910006bc52d9110276f772d8542024fc75d854226ef72018542004ff76509100067e43d9520014fc73d8b100757c75509101cfb410d9110006df635051014edc6350510014fc73d85420bfac6450920006be73d9110006ed3258a100057f73596211c6bf61191100057f7559121024fe75d9121006dd65d8d100067f74d952002cfc76506200067e74594100057f73d9520007e651d8910006bf6450510006f761981420067e63d9520006dc52d8d10014fc7358b1000def745092000eee6288710006f55018542006ef6248110004ff735901001cfe74d8121006bf52d911002efa601824106cfd76906100073f5319110024fe75d91200067f65d8910006f770185420073d5319110024fc75d85200063f53d9110276bd74d854201cfe7458b100076d5318910044ff7650710004fd74185200067f5398640006bf65d9110004fd7688640007b531d911000faf7450a21004ff75d89410767d71d95102167f70d952027eef6350a21004fc7648540004fd73592200067d53d8121004fd70d912100eac6250940006bd42185400067e42d951001cfd7690410006ec65d8910226ed638862000eee62486100067f5358b10004ff73d8542004fd74d8b10
  | 13 => 0x911000cfc7650521006dc42d8d101cdbd70906400a6bf43d931006ebe71d9110006ed62486100067753d854202dfa71c4110006bd62906400067f53d91202df3c42d954215eee62d8a41276f752d85421b6ef638862002cfc76486400067f70d9542007db63c4110014fc7358241006bc73d91100067f7559110006ec73d891002eee2058a4002efb61c4110004ff76906200063f65191100057d73d95421d67e20d95100247c7558241006b54318542004ff73d9310024fc7558a400067d74d9510014fe7358620004ff7558221006f721d8540006dc41d8d10004ff751854205eef20d89100067f31d9510014fe73d81420067553d854201cfd71d89412e73c41d954202dbc7650940004fd74d8121006f631d854206ebe761911017d7e759814201dbf7250a410067d43d95200066f6518910006ec43d8910006ed50d891020e7c30d9520006bd4358a410067d53d912000fe761885210067e74d9510046f5411854019f7b53c411013eec6588521004ff7259010004fd7558a100067c70d9542006ec31d89100a4ff76504100757e758851002cff70590101b6ec10d8910004fd731852001cfd72d814202ef6719864000cff7648610034ff764871002cfe70592200ae7c65c411002ebd4058a4002dfa76c411010d7e7588640004fd755864001cfc7458910006f465d85422cfb74018542024fe755901002dbc705094002e7e7059410137af4050a2102cfc70d9110006f465185420067e725941002e7c20594101aeee2018520024fe75d93100057f754831015fac42985420077465d854219f7953c4110005ed7290621006fb30d8142006f530185422aebc41d85420067e70d95420067c6598542006bf7459121006df73589102df3c74d9542014fc73d91212aef540d854226ef75218542004ff75590100067f4159621014fc73986202df3f74d9542014fc731852002ebf7459220006ee74d89100067f72d9510004ff73592202de7f42d954202ef771586200067f4259410024fe755891020e7e10d9520046f641185400067f74d9510006ef6290510014fc73586200067f41d952002e7c40594100057f7558121187f151440102aeed72d85420067c65d8520006fb60981412aef641d85422e67c40d9542007e47150920006bf7459310006ed31d89100077b7544010006f4311854206ebe54d9110004f771591200067d5358a410067e31d952005eec2158620014fc73d852028f6e6550a21014fc73d93100a6bf42d9310006df7359110006f550d85421b6ee20d8b100e7ac42581420057d7588610006f431d85420067753185421dff151c42101cebc40d931015cff7459121006ec54d891007eef2158a100067e64d95100067d635962105cff7258910006bd6490410004fd73d85420767d10d951005efa2058221006de54d8d10004f
  | 14 => 0x6ec64d89100067c435941006ebc6459110024fc755912102cfd7690710006cc63d89100bfaf4350920146ec52d8941006bd6450810006bf21d9110005bf7458910007ac64d8910006f4215864000cfe71d891026ef474185422c6bf6550a4107ef521d85200067f7558a100065f75d8d10024fc7558910147ac42585420067d5398620006af64d89100067f30d9542276f452d8542004ff7159220006ed65d89101afe6101891002e7f305941007eee4258a10007e6311891002dfa70884102e67c43d95420067c65d911012edc638851000eef61885210067d535864002cfc765051026fe7201854228fad5450a21006df6388510006bf648851000cfc7259310006ed32592210067d3159410006be62d9110006bd32d9110007b6311911002e7d20594100e7ac625094000cbf7650a41006cf63d8910275f676185420057f7558540006bd51d9110116dc6348510004fd7398620006f663185420067d70d9542006bf545921002cfc7058a41006be65d911015cff72d912102cfc70d89101c7b61019110024fc7518542006bf644851000cfc76483100057f755081020e7c20d95201b6ec6588620007eb7050920005f771591200047f73d954202e7c10594101d67e70d9510004fd72d81410feee3258a400067e305962102cfd74d8540006ef52d8941005f97090410006dd51d8d100076d758862002cfc76486100066f53d89100067d31d9542006df63485100067e32d951000cee76d8910005df7358520006ef65d891016d7e75d8a4102efa601822102df87048610007e531d891001cbe76d9110004fd755824102cfc7058a101b7e410d89100067d65582210067f65181422afb740d8542004fd7650910006de65d8d100067f71d95420067f53592210067f73d9510004ff72586400ad7c75483100073c65d9110006ec6318910004fd721854001cfc74588100067d43596212e67f43d9542006f441d852002eec205881001cff765061019fd863c4110006f530d854226ef542185420066d53d89100067e74596210e6ec2159220004fd7358b1000eee6250810036ee3218520006bc6319110285ed7350a21006fb609822106ebc42d91100067d74596210075c65d8d10014fe7318540115dc735812101ebc64906101cdbc7050a41006ef6318910006f671d8b10006f53158620014fc73185420067d535922102cfc705922116d7e75182410067c21d9510005ef725012006cfd70d91100067f4359410006ed63d8910006df21d8d1008cff715911002cbc765094000ebc6250940144fd765052100cfe725921002dbe70509402adf771589412cef65418542004ff75d8b10004fd75d93101557c7558941004ff75d8910007e771509201eeed6350920004ff75d9110007bb64c4110014fc7358a100e4fd765012020f6c20d9520006bf631
  | 15 => 0x7b703c0291a100000100006201801f01c0010050a70090000100c70010a40830000060790000b41070111b32ec00003c03b0022280300b70f705f00000e00000020401104502208f00200001100700716b03800406c14b04000100c0090060100d104400200000425600c02477d08b04903900a02a00000f0290060090f801801408100f02d04c11804a06f03900300b04d00400200e00800006f0b60120ca00000000000200b04600001900204605a00201f03106a03900004400800820000175401000202801d00f00000700500801100500f00c00803703300001303d0870010010ab0020170300150c403f00000800000a01e00a7c400001461b0140050cc0016b000203228135c00000300500b00102400001e11a00116903600d00d0150b901b04b0020ac00103c00e00803c01209804601710000200505b1d505f0e800601906904700400000003e00100205a00400301a01519109e42401201800002901b00603600005800500000d00500f00000200100500800300a01301701004711a02d0000020020041fa00500902d0010ad00701400600300c0176cf00d00500000400a05a0080010a307d00100600100757502d00200001c00200a0270230000030a400010300006601b00402204c07400000100100201201203300001002e51101a0030070011aa0120033940040b100100d00000300c03803000c00006221d00c01a0430065b102f0180000010060000170310a400600010309e00f00200c00002307f0f40000030100290020f90130050050080100000040950020000380031360000040000d20010060010b600000201401400a00000000109c00c0010000240040010010550110040000430010040030b600000000602200705d0270000146af00404900100202304b01400b00500209702401e00336c0000900020aa01500004c5a90100a612600100902907700005d02a03013c0bc01f02200100101301b00000900a2d60000000010f601e00000201b00000b05500009004d01200101902300d0300020050120070eb00102800000001a00000000402600d1e00280000000100510030f704e0080120b10510210920280030160050000a404003032a08100005d00000000005d0030137e100003c00903305400100d1490010010a00010260131e400100800800400d06e02a00c00001631a0ff01d00001400402e03401829800600102e00a0bd05106501321900000900600202d00d00301d04610e01104a0032dd00709501300037903600100b00101000b52b05e00019708100a0101f314900100b38900002300003300601908a00b0010000070010000000050050000030430030f903000b00402c00b00e002002004fc7650910006f56318542065dc7359110004ff7458910006ef625051001fb67190541006ef52d8910
  | 16 => 0x2b00203002c04c00000106400003c0010090040040000040170180180020060060000480100380080010140080363a010c00008c00a00b00006502327507600b00201009a00002200000100800119c01600900203f16e00701f11400800100a00005300000002107001601300000d04a04512801d00c03e02a0080c00bd00505e00603500101700100106200300701300800000d01647900a08011f00400701a00200005d0710d80000190010a200300100003900200100000000004200000102200009000007703305600024d00601e01d0130d100100605601012904d00300000b00d00000f00a00100501302c0000c800005900300100800000700300801800f00000007d37700600f00a0a100b04a00000200003f0020c000000000000000905d0190f90121a816f00100602100100700400000000000202e00400100c06d00002600f00100200104a0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6e85d0362440c5d8c20318c4880038b19365509200162e39aa6b04424eae682dcf61508b947d0839ecaa11f78dd0d53185420051f42cca3222000c7475d85605086d1dd0fa0ec4880028f61463d91100072642ec7b122000e2f64d4f624400187ee93a2ca08137a99887150a4100746320c7b1220058ec874c962040018beea31ac48800395a0475d8d100051f424c5b2a2000c5e76dd7634409d968edb8a84a00029ba0a63d951026d73414a630a8400c77659c6605089d9ccc3b8a8510a13a9108651854200572c1061b0a8400a6d82cc5650409d9ccc5b8a85080028f61321594100047dc3ac03024200a76851cf61508090f90ab9ac1208021fe157690520296373b2eb10a420087d879cf65508018bae6992ca0824f8d9d365d85420062e3a8e6b224000ec463944624400153d07316c8881cf1d9c753d922102c7ac3ca330c4000c77651c560508010fb0e192ca080db3a9db62c411048732b92a7b0a8400aae829cf64440018bee6a9ac8880021fa1c65585200053b42861b0a8400a7685cc7615080159d0c318c48810a9ba0843d952021537410e7b2a40008ed87cc762440051b906baac48800297e1574d8d100043f43c86b2c4200c5d731cf65440655ad03b86c6880031ddd675185420043f438e7b2a8400a75850c361508b7878edbaa84a00023de0573591200061fbaee8b122000a3d8598864440014f100b1ecaa100b179cd53d93100052ec2cc5b1a2000aae8499062440014db0ba06c4880121f21576905200053ac2882b0c4000c9f741cd64440018e8ebb8ac890803175cd53d93100043f43aa6b222000a9e8414b63440010fd0e18aca080029e600215941000536c28c7b122000a3e840c165884014e90ca9ec2a10029da1663d854200477c12eab222000c3f7454d61880090fd0a38ac9100023be0973589100164f39a87b244200c5d73d8f65440090fd0fbaac120966b921932185420063abaea3b0a84038ed82dcf615080156b08186c2a10021f21d535891000536c1061b2a8400acd8399462440cf87ae8a9ec2a1002a7e1151d8d100061f3b0ca32220008dd839d942c409d74904a1ec2a1136b9a0853185420051ec1eca3222065c3c74d4d61880015c904a8ac320002b360e64d891000557424ca3122000a6e8510f6244001a68ea38a84a00121f21570d912141f52216c630a840487e851da21500011eb0f318c2a100a2fe1d43d911000557430c83122000a3e849cb654401d0fb0fb2c42880023de1d6118520006363aac4a142000a3d8598b64440018f0ebbb220080021f60f7558a100243f42ee0b24426087d879cd65040014eb0b386c2a10030f19774585200162f39aa7b0a8400ae582940615089d74904aa6c2a1002ab60a73d911036f1aba6a7b0a8400e2e64595428840155f08b18c4880023760f7650910
  | 1 => 0x90ea9ac508003a3190631891000667b98e4b222039ab4864c764440015e300108c2a000387d8f53d91100064e3a0c6b122000ace82993634400317d0fb228588002aba0a651911029536412e6b2c420087d87cc76550801ccaa6990c2a10029b608435941000c5ec26e7b0a84008fb875806090511d4885328c2a10031d5d671d92210052f42e81b1a2000acd8399062440010fb0f21eca900031ddd7615814200727b2ec7b122000acc83590624400147b0931acb1080317dd473591200062fb2ee6b028400c7675d8660508010fd0e32ac888006aba0b645091000556412a3b222000e4d8518f62440010fb0fa06ca900033518f714811000566c14e9b1a2000acf8259363440018b8e7b2ac8900021fa1c65591201be6d3b6c788220008bd87c8764440014dd0b328c4880028f21163d9510006b3baee2a144200e2f6519362440c5d8820318c488136e9209541854200727b1ea7b12205ea79809c565040014ef02992ca080031ee01735941001e5d3b0c98822000e1c6518f644411fc588432cc2a10121fe1f53d92210051ec2cc7b22200487e85dd94244001958c9b92c8880022fe1173591100043ec2ee0b244200caf74dc9624400b4f100b9aca080038bd5254d89100052ec2e81b1a200087d85dcc615000147b09396ca880031d994715081000717b2ec9b122000e575394c6150807958e8a10c2901cb998c953185420043fc3ac7b2a205ca6d82dc765508014eb02182cb10a1b999c865d854243d3b430ca30a845cb2c844cb65508f7d4e86990c2a1003a3d9063189102153741683b2a4059ea4641c5424800593ce6a1ec9880031dd9771591200052f42ccbb1a200087d85dd942440010fb0bb92c3200dab921931d89100069a3a8e2a148200e1c75d9363440011bd0fb1ac488003171d463589100051ec28c63222000cd4731c56448001a6eebb8a85208031ddd771591200045f438a5b222003aaf86591428840155d0532ec8880e72e9db64c41100243fc3ec7b2a400087d8710d65040018ba65b9ecaa100317e17735912000716326a7b12200487c855cd62440011df04baac488002b9a0475d891000666390c6b222000a5c855d363440014db05382cb108029b60f651891000537c2ac6312200087d83dd560904014db0b31ec4880022fe1173589100056641acbb122000a7686d4c6150801caf06a9ec2a10031dd94715091000726a9a64b244261a7b805cd6504001c98ca31ec4880032bdd372591100053ac2863b0a8400c7475dc5644800196ee820ac310002a761052d8d100052f41cc9b2a2000a3e859cf6444001a9ee6996ca900163d61e31986400043fc2ae6b048200a9e8398864440ab5cb043aec2a10028f61073d95200243fc3ec7b2a844dab5841d4615080156b09980c2a10030f1d7745891001c5f426e7b162000
  | 2 => 0xd53592200064f3b0c9b1a20008f7815cd6448401e8aa6996c2a10030f5d074d95100043f43ecab028400c9f741cd6448001d8b0231ec4880131d9d6511854200763b1a6430a845ba6e82cc76550801ac8ea38a85108063b209755864000557c12c320c8000ce7621c5204400147f08b1eca900030f1d764509100066639ee4b222000e1d53ccb64440090fd0bb9ec9109071b60b7558a102fc3f438e6b282065c3c74d4d6244001c3b0a318c88821399108651854200578c00e630a8400a3e8518f64440019b0e7b82c890156ada1375d85420243f436eab122000ea5434c861508039d4ec316208800387d9464d8d100063aa9ee2b224000a6d831976244001c5885b2a84880039321763189100053a42ae030a8400ab684cc4614800b75100a128090003a950821185400064f3b6c9b1a2000c6c65dc9644400117f08baac8908163b21d62508100056a41ae030a840087d87d4c61500b356d08398c2a10028fa1263596210043ec1eeab224200e1f5495363440051df0e996c9108028fa1431d91100145fc3a87b244200a758598f61508d18d8e5a9ac88800387d8f53191100043f43ea6b224200a6d85ccb62440010fd0fa02cb1080327dd363589103e7531928630a840487c87d4d64480014dd0421aca080029b6084059621006a6b9a64b2c4200aad82cc7644400147d0990aca0800297a1672d8d100070ec28c7b22204dea4621c542500010fd0fa06ca880032b108765091020c3f438eab1420008f78759461508c18ea20b9aca080031b1d762509100062e398cab222000ab584c8461500014dd0a20ec488002ad61351d85420066c39eec8802000c3d751d76444001c3ecbb26c6880029de1561185420043ec3ce7b2a2038ab4864c464440015cb05980c2a10063b20975591100071aa9a8630a840487e87dd562840071df0eb2442908029ba0b31d951000536c2c87b122000a6d82993654400147b0998eca90002b3e0d64d8910006363a8e4b222000cd773d85605089b56b08380c2a1002bc20163d854202c7c402e6b224200a6e8518f62440090f90abb28488002b3a0a65d8d100055a422c230a4084e347419461508010fd0ea9ac4880121f215765081000566412a3b1a205ca3e84dc7655080153906b28c888003871d464d8d1033e36392a6b0c8060c78805cd65040019a8e630ac0a1002abe1171d89100045ec38a5b222000e4d534c962040b765904a1ecaa1002a720d65d91100062e31aeb10a200087e87d4d624400147b0b318c8880028fa1063d95200053ac288330c4000a6e850c762440090f90fa9ac5080039354f32d89100072a31c63b2a2000cce7618c62440018bf0bb9ac8880029b60b31596210043ec1eeab22200087d85dcf6488401c38ca318c8880021fe157650b100243f42ce3b224092e368419761508010f
  | 3 => 0x4b14800087d85dd941480b947d0998ecaa10031d197715912002e5d382c92082000a768598c61508014790da98c8880028f60c65d91100064fba6e6b222000a3e849cd658840156b09a80c2a10023de1d611854000557424ebb122000a6c86d4f62440b35cb04398c2a10163be1d62884100061e32ee8b1220008f7815cd62440014bd0b3aec6880036cdc470509400065a320e29022052a6e829d165884014790da9ec8880038bd9464189100053a432a630a840087e8790f654400b1d90e992c5080034b10b755854200637a9ee4b0c8000a6e85dc362440018f6a7bb22008156e921132d85420043fc2ae5b0a80008fb805cd6448401c9ecbb18c488003175cc63d95102dd1ec20e7b2a8452a6e829cd6588401c9b0a318c488003a560463191100043f43864b282000a3d8319464440011df04bb284880021fa1c41d95100243f42ce3b028400a748558461508010fd0e39acb108031be09735962100722a9a6430a8400e4e8518f6244001878ebba2c888003a560463d91100051f42663b2a2000c747518560508d9caa64a9ec2a11cbc910953185420069dba8e0a1280008f68714361508015ab07b86c2a1003171d763509100053b40860b2c4200a3e85dcb64440011df0eb28c4880029b21953d891000536c2883b122000c7565dc54204005998e6992c890002b620d60181420045f43865b222000cac41dc961900014df04b1eca880023da1f61581423545fc3aa3b222000c5f65dcd61480019aee7b8ac8900031b9db53189100243e43ea6b224200c74751c564480018b8e632ac8900032d190715912046733396cbb0a8400c7885dd910040018bae639eca900032b18b745891001c5e422eab122000a3d84dc765480014bd0a20ec68813ab9a0873d854226dd24128630a8400ab6811d7644400755d09b1284880021fe1975884101ad72432623122002c5c7354d6448001c9ec7a98c48800317dcf5359120006b23a8e2a124000a74814c9650400147b0931eca88002bce01631854200d56412c8a142000a6d8298f65440051bd0fb9ac8880029b61463189100064e326e6b222000e2c64d4c624409b5cd05980c2a10038bd9764189100051f428c63222003aaf8650a41884014dd05a0aca08166ada13301854200636396cab222000e2f64d4c624400159906b28c4881b7999cb53d854200536c1086b2c4200c3f75d5164840011bf06bb284881df1b5c865d85423663bb8aa6b224239ab5811cf64440014d90ab26c4880029b61443d891000726a9a6430a8400c3c74d956244001878eab228508156b960b70d854200556422cbb122000a9d84c8763440014dd0bba6c4880028f61643d91102ad72c10e7b0a848ec6f7219561508090f90ab9ac890002ad60754d91100062e39ecab0a4000e4c6518c62440014db0b318c48800317dc
  | 4 => 0x54400155904b1ec8880029d61731d85420066bb98e2b22405ce2e64dd54288401c9ee6a9ec4880121f21572d854000537436a7b122000c5f7354d62440018be64b9acb108029ba1473d89100072639aa7b122000a5e86197634400117b0f318c8880039318f53d89100071a32aa830a847096c8759542884010ff0eb1eca900021fe1573591210043f438cab0a8400c5e76197634400147d0c328c8880123d61e51185422cd5b424a630a8400ec58118c624400117b0f98ec8880021f61e63d954200673b90e2b224000a7486d4f61508014d90da98c4880021fe1d65182210070fa9ca7b222000f45534c861508b74dd04386caa1002a7a1321d8d100051f420e4b282000a6e85ccb624400187eebb228488003171d473589102755ac20ebb0a8460c77105cd65040051df0e996c4a08029b60c651891029536412e0b2c4200a6f825d1658840159f06b20c48800a37a0f76509100043fc2ae6b14200087e8754d644800196e8638ac8900021fa1f32d951000752322a23122000a6d82d07654400147d0b21ec88800a2f21d43591200046fc3ac9b1a200087d859c76448001c3d0a318c8881970f9db53d911000477c3ac83122000a768654f61508018beea39ac4880022fe1176509103b53b40ec6b2c420087f855c06150801ca8c698eca88156ada1073d854201c5f426ebb0a4052a6e82d05658840147d08192ca080028f61331594101cd5ac08ebb222000aac825c764440015d304186c0a1003391cb71591100052ec2883b1a2000a3c8654c64440014eb0a180c2a12138ddd065185420053ac286230a8400c5c65dcd644400187cedb28c88800b171cd53589100053b42e6230a8400e578354c615080147f08b1eca880021fe0d75d8b1032e36b96a7b0a8400c5c75dcd64480010fb0f98eca88156b960b73d854200c76412ea30a4081ae7825d461508015cf04a88c2a1002bc201631854202c5e43a86b2420288ed86dc5428840195ec9b9282908029760e72d95100043f436eaa122002c5c7354d61900018baea3aec688002a721165d8d100062e42ee6b1220028dc835d942440014dd0a318c488002aba1263d891002c7743ea4b142000e4f5394f62440011ef0eb18c2a1002b960830185420072ab9aa7b0a8400c5c7319561480018f6edbaa200800b271cd435912000637baec4a122000c3e76d4c64440014b90ab26c68814a9ba08435962100696212eb30a840087d851c56488001cace6a9ec2a10031b9db65189100043fc2aeca10200087e87d4d628400159d07318c4880031d5c471d95200051ec2e65b222000a6e8590f62440015af06b80c2a11069b21932d95200063bb28e2b224000a3d851cf644400156b08180c2a10031ddd4715912000572c168230a400087d8710565040014ed0a180c2a11372d1d8715094000726a9a6
  | 5 => 0x81729b60870d95420043fc2ae6b122000a778158f65508090f90a3b2848813b39ddb7150a2126e73310e2a1020368ec87547624400159d053a6c6880021f61c31d95200053ac2cc630a840087e8710f654806d1dd0f98ec4880028fa1b53191100053b428c7b0a8400ccc73dc9624400156908a8ac3101b38d5d153d854200537c12e6b2c4200c5f835cf654400147d0b996c8880dab960473d89100064e3a6e6b12200487c855cd644840156b09988c2a1003394c87159120006b5ba8e0a124000a7583d9761508018ecea30cc0a113aad61073d85422ae5a326e2a122002c5c73d4d64440019c8c438ac4a00261fa1f31594100070e31ea63222000cd763dc542440014ed0b39ec2a100387d9463d911000537430ca3122000ae5820c461508051df0e996c5880021fe1d53d92211b572c0ee9b12200087d83dd564480018e8ca38ac8900021fa1c31596210051f420e7b2a4000a3e86d4f64440014bd06392ca081e739dc861581423261e3a2a6b0c4000c6e82dd562840019aee630ac0a10021fa1c31d952001d56422c4a102000e4e8518c62440011bd0e296c6880021fe1d53185400051ec2662b2c420087d87cc365440018b8ebb9ac4880028f61432d91100051ec24e0b2c4200ce462dc540440090ff0ebaec9108121fe1f53d8b100052f436ebb1a2000ace82d07634401d0fb0e20eca88002ab61331d89100055b408e7b222000e1e8518f64440014d90ca98c4880021fe1576509100054ec1cc43222000c5c65dcd61480011ed0e180c2a1003171d473591102cd5bc1a8630a84008bd870cb64440011bd0e39ac88800a2fe1d43d912100656214eca12200487e86dd5605080155904b18c88814a9ba0840596210043f43e64b282068c6e76d4f62440014eb0bb86c2a10028f61072594101cc5f43e43b222000e1c63d4f644410bc6d08328c2a1213991c865185420045fc3ac6322203ae6820d9520440011ef02baac8908121fa17765052000667b9ee4b222000a75851cc61508019e2a3bb2200800317dd773589100045ec26e7b162000cb7741c5644800b1e90e98ac32000317dd763509100056741cebb12204eea664dc542884854dd043a6ca9017f1d44373594100043ec3e60b2c4200c5f75dcd64480018becbb9ac8900028f21953d911000727b28c7b1220038bc845cd618800153b07316c888003351cf71589100053b40ce1b2a84028de86dcd624400155908b28c4881730f19375509100064e3a0e6b122000a7585cc361508011ef02baac890166e9211321854200c5fc3ac920a420087d870c565040018eeea30ac0a114a1f61d65884100053642ac83122041a6d821cf65480051d90e992c8900023d20573588100066631ee4b2220008f78758461508011df04baac8909731bddb7550a210043ec3883b2a4000c5f73ccb6
  | 6 => 0x6f63c1a6430a8436ae486547624405f0fb0e31ecaa1002b9a0473d891000726a9a65b028400d2c42dd56050801c9ec6a9ec488233c910b65d85420051f42cc43222000e358119464440b947d08186caa11cb954c9531854200572c10a630a8400da4421c560508758f4edb2e2088006aba0b6450b1000566412cbb1a2084e364219461508010fd0f21aca081572d9937150a1000716322a7b122000c5c65dcd6448001c98c7a98c4880021fa1c65581420064e398c8b12200087e87d956444001c9f0bb1ec488003a950841185200063a32ee2a12205dc3d7419761508014dd0b98ec4880031d594715081000556412ca3222000a3d840c165884018be65b9ecaa10163b21d3258a400062f996e7b2a4000aae849cf62440010fd0dbaa40880023b61c43d89100055cc2061b02844387e87d9520440018deea392c8880028fa1270596210062e39ecab028439e98304c364440018bee731acb108162f21d6450a103fd72c14e630a840087e87195624409b9cce2996c9108023da1c5018542006d2216e2b028400c5f7354d64480010fd0e21aca08002ad61053185420053742cc7b12204ece462dc5424400187aebaa6c8880031d54c71591202755a43287b0a8400a5e8398b6544001c6b0232ec888136b9a0a731854200667b9ee4b122085e674219461508010fd0f98ecaa100b271cd43592100064fba0c6b122000975851c5404400147d0b316c88813ab9a0830d85422dd3741061b2a844dcb7761c54290509c4884328c2a1002b960b51d854200573434623122000e2f6454f624407356b03b96c8880121fe1f63d95100043ec3ce6b2c4200a9d8498b63440018dea7b92c8880031bdc973596210053b42ee1b0a8400c9c73d91624400196a8638ac890002ab20965d91100053b42e61b0a840087d8798f65440010fb0ea9ec9108032b9d942905200043fc3aa7b16200087e8754d62840010fb0f39eca900021fa1d53582410047ac3861b0a840487e87dd564440011db0fa0ec4880023ee1d60181410051ec24e6b2c427acb77418560508eb8ece332ec9109b7c910b53d85420062eb9e64b2820028dc835d5644404f0fd0f98acb1080378dc4705092000732c08cbb122000ce6321c56448001b488538cc0a10023ee1d601822100c77416ebb0a8000c5c73d9564440015cf04a8cc3100dab960475d89100052ec1cc9b2a2000a75851cf61508010fd0e21acb1080297a1875d8d102de36316eaa122000e1f6518c644406d9cb03b92c3200021fa1f53591201ac77c3ac310c4000aae8498c62440010fb0bb9ec5880031b1d772591102755ac26e7b0a8400d69755c221880018bf06b9ecaa116e8f21943d95422153741663b2a4005aac8650940480010fb0fa06ca880021f61d53d8b100243f42ceca122059ab4845d4615080147b08196ca8
  | 7 => 0x6632194615080b1e90ea8ac32000317dcd53d89100053741662b2820008f587994615081d0fb0e18eca88136ad219541854200732c08ca3122000ec6534c861508010fd0db9eca880e2ad21951191100061fba6a6b0c400087c87d954244001c6ecaa18c2a1003171cc65589103963b38aa7b24420087d870c765508058b8e6a9ec488166ada1273185420043f43c87b2a400487e85dda2190001d2ec6a18c2a11a30f5d353d854200557c12a3b222000c5f75dcb63440018b8ebb9ac8880023ee1d60181420146e41aeab224000c3f65dd1624407117f0eb0c832016e9ba0b71d954202c7643ac4a14200087e87d4d644409d1ef02bb2840800387dd464d8d1000d57c32c4a148200a3d850c764440010fd0fb2ac29013aad21954d85420043f43863b2a203aa74864c7654400147b0bb96c88800317e0d73594100070fc1aa7b222000a6e8599362440010fb0b3b28588002ab21163d89104155bc22ea30a8401cad7650a41884010fb0f3aec9108032b9d942885401cd5a432a3b222000e675194762440018b8ea31ac8880023de0576509103cd73c12e030a84008f681dcf64884018eaebb0cc0a1003175cc63d952001d57436c8a124000ae582cc4614810bc6e86328c2a10031bdd7624811000c76412e3b224002cce734cb62c4001c3ec6a9ec8880deb560475d8d1049732b90cbb0a8400c9c64dcd62440010fd0e21eca880121f217765081000536c2863b122000a3e8598c64440018d8ebb92c8908021f61f53d922100536c1060b2c4200a6f85593624400187ee9a9ac4880021f21d65508100055a422a330c4000aac845c76244001c9aa6992c508156ada1030d85421cc5f43e63b222000ab58414461508010fd0f982cb108033518c714811000752324623122000e1f75d93634400147d0998eca900023761c52d8d1026d73c1a6430a8484e6720194615080317b09baec2a100eab21942905200055bc22a330c8000d8c42dcd6050801c9eca318c4880021f61e43594102dc3e436eab028400c5e761d763440010fb0f98acb108063b209735864000d56412c8a102000c3f42dd560904010ff0ab86c8908029d21563d85420051f42e63b22200087e870c365508b396ce2a1ec9108062f21171d89402143f43e61b2a40058bc8750d6404001b4884b8cc0a10029ba0a64d951000727c1aa7b12200087f8759764884ef8dae4328c0a10ea9d60473d951000536c2ee9b122000c9f64dcd62440090ff0ebaec5881de4fa1f7550a412fe3b886e6b282000a3e8598f644404f4eb02382cb108063ba1f725864040d73c12ca30a8459ab6841d46150801cab0232ec6880031ee17764401042716210ca30a840087e8759542040014bd0b316c6880031bd9772591100043f43e61b2a8400c5f835cd65884014dd0da98c4880021f61c30d95422
  | 8 => 0xe5b2ec2a114e1fe1d65884100043fc1aebb24420087e87cc36544117c6e87b28c2a100237e0d75591203e752212c630a8400a6e8654f624411bd48853b0c2a114a9b20974596212ce5a320e2a122000c5d7318f655080b1e90e98ac310002ab61265d89101ad72432a23122000e346550c615080117f08b9ac8900121f2157650b1000727c2ec63122000acd82997634410dc6b0832ec2a10163da1b71509100054f424c5b1a20008ee8710f6244001d88c6996c2a10028fa1432d91100072ba8ca3b1a2059ce7761c542884051bd0fb9ac4880029761674d8d1000556c14ca3222000e2c6454c6244001c9aa6992c8900030fdd474589100061fbaee8b222000a5e8599363440018dcebb14428800a3720d70185420062e32ee6b122000a768654c61508014eb0a380c2a10029b61673d89100147bc3a63b0a845d96e87dd542884014eb0b988c2a116f0fddb7550a410053ac18cbb0a8400a5e859d3634410156b09318c2a10039318d32d95200046fc1aeab222000a6e8598c62440018beebb1a40880029b60b31d954201c5e422e6b122000c7675d86615080196ec838a8488167a5e0d431854226d73414a030a8400c3c64dd520440010fd0fb2a8488002b360e75d89102cf53320e2a144200c6c825cd658840335f0ea14831080297e1564d8d100061e3a0cab0a4000a778558f61508ab56d09b9ec2a1213c9108651854200666316e6b122030a7681dc36544001c38c6a1ecaa10121f21570185420061e326eab2220018be87d91424400155d0531ec888002abe1161886200056b41ee1b0a84008dd87993634400355d0db1284a00031ba1772586400145fc3a87b26208fc3f74195615080155b0532ec8880038bd91531891000536c1683b2a4091e6572d4f61508071dd0fb1285880031ddd751185420062eb98e7b2a8400e2c425954204001c6ea328ec8881930f1d153589100076231aa23122000e64654c8615080155f08b2ec4880121fa1773d8b100043f43883b2a4000c5e76d9763440014db0598eca880032bdca72d91100061e3a6cab0a405ca3e841c3655080159f04a8ec6880028f61321d951027573416ebb0a8400e4c634cb655080187eebb2240880028f21163d95200043ec3860b2c4267c6c7254d64440fdc6e87a98c2a11df0f1d065185420062fb9ea6b222000a7585cc061508010fd0e3aac8908e62f21d51d911002c5e43ac8a1020028de87dcd64480014e90da98c2a10021fa1b73d952036733392a7b0a840087d8799460884014db053a2cb1080387d8d53191103a63b38acbb24425287d870c565884014eb02186caa103a1f61c63d95100045fc22e6b0c40008f5870c061508018bf0bb9ac4880021f61f40596210056ac18ebb0a8400ace83993624406f5a90ca8ec6880021fe1d63d954200673b10e2a122084e
  | 9 => 0x64189100063ab88e3b2a8400ace83990624400755d09b12858808e2f61b7150a4134636396a6b0c8000a3e84c876544115ccc65b28c2a10029b21563d89101ce5c386c8a0a2064c3e7654f644409b9c8c438a8488002b960752d891000726a9a65b122000e94638c4644400196883b8ac5200038d19651d91100062fb9aa6b0c8000aad849cf62440031d904b9ac88800297a1c75d8d100046fc1ae030a8400c3e7654c64440014ed0b980c2a1003a319363d89100062fba8e6b222000c5e75d8e214400153908a8ec6880021fa1c31d95424055ac24e630a840087d851da215000147d0ca98c8880031b1d772589100043ec3e61b2a8486f244219761508011bd0e39ac488156b960b75d85420043ec2eed10c8000e55811d763440090f90abb285080031bdd772589100055bc22a230a8473e6632d4c615080187f08ba8c2a00021fa1f65591202e53643265b2a840487c855cd644409d5cd043aec2a11ae9da0473d951000556c14c632220008bd84dd761480018b8e632ac0a10039354d32d9120004bac28e2a062000a6e8599062440750fd0f98eca880121f21f53591100064fba0e6b1220008ed82dd761500010f90ea9ac8900072b1d9425012000556422c6312200487e87dd56448001a5884b9ecaa110a1f21f65481100043f436e7b2a8400caf749d36244001d28c718ec8882438d9d153d85422ae723b6e2a124042c6c62dd52044001968e9b8ac4881cfc910b531854242f33b90ca30a8400a6d85dc3624400147d0ca9ec88800399d4d32185421b674386c490a2041a6d821d365480018bb0e31eca880029d61463d85424363b3b0ca30a8400ae48254661900018bd0e3aec68800317dce73596211d739b0ecb8822000e6465947624409d96eedb8a85208030fd0975185400054fc22cbb1a2000c7953dd910040010fd0e20acb108029d60f65185420243fc3ea630a8004c747594761508011db0f318c4880028fa133159410006363aec49022000ea4644c46244001d1ec9b1ec4880029da14631854200536c1087b2a2003aac84589428400187cebb2442880031b54f725864000476c3cca3122000c7465dc560508090fd0fbaac89096e8f61070d95422ce5b320e2a10200487e8758d658850556f08b28c2a10023ee01735912000557414c63222000aac8454762440014ed0a18ec2a100317e0d73d9520006373b2a631220008f5871406150801d88c718ec4880031718f75509100061e3a8e8b122000cd463dc542440b98d8edbaa84901b395cc953d854202c7a43aa2b0c40058bc8750d6488001c9ec6a98c48800335d8c715091000477c12eab0c8000c5f65dcd6444001cab0231eca880021f61c43d95100043ec1eeab122000a76851c061508010fb0ea98c2a00163ea0373d92210043fc2ae6b224000e946350f6150927cca
  | 10 => 0x30a842787e8798d658840159904b26c6880021fa1f31d95200047cc06e7b244200ad6831d761508014ef02b1eca90156ada1075d85420061e3a8c8b1220008f6870c361508018bae7b1eca900038718d53d91100043ec3886b2c4200ec4638c462440010fb0f986ca900123de1d51d854200572412c230a80048ef8754b62440090ff0eba8c2a00029b61730d89102143f43e81b2a405ba3d84dc765508014e902b1ecaa10121f2157358a102e716326eaa124000e4c65d8f62440010f90ea9ac8909bb1d9c5651822100636baec510a200087f855d942840015e300208c29000297a0e72d95100055742663b122000a9e8314b644400155b09328c48800b171cf535912000537432a63122086e357419761508014dd05a0eca88166ada10301854227753316e2a14825dc6c72194615080147d0931eca880038b19464d89100054ec24cbb1a20008ef8758c62440010fd0e20aca0813aad61070d85420263b3aca330c4000cf251dd9100400147d0a39ec8880021fa1c755912033477c3aa3b122000e8c42d8d42440010fd0e39eca900030f1d764589100051f42662b2c4284e344219461508c7d4c20320c4880021fe1573591100053b42ce1b0a8439cb581dd1618800195ee8392c8880029d21563185420043f438eab222085e374019461508014ed0a398c2a100317dd763589100045ec3cca322200087e87d95615080193ee9b9ac488166ada13501854237d9642a8520c4200a768198f65508014790ab1ec8880021f61c43d9520006563a6e4b122000c74655c66050801c9aa6996c4a08163d6187150b100061fba8c8b122000c5c85dcd6448001ca8cb28ec68800317dcd535822100476c3cc83122000e4c6354f624400195843ba2c3100029b60b41594100043fc1aea30a80008be87191624400155f08b28c4880021fa1f53582410055741663b222000aad8498f62440018eea7b8ac89000e2fa1f74586202ae5b30ee2a148200e2c65d9362440011eb0c38a84080038d19651191100062e3aec6902208af2442d9461508018eaea30cc0a10032d59071508102943ec3882b2c4200ae582d0661880b7c5cc5baa852080399d9532185420243f42ceca162000ea4649446244001c3aa6996c8880021f61676509100043f43ec6b2c420087e870cb6544001a5885b9ecaa10021f61f31d95200062eb9ec7b2a8400ab684cc761480310fb0e31eca900031d19471509100147ac3c6230a8455ae4864cb61508b35cb04380c2a11931b5c953d85420061e3aec89022000ce77208561900014ed02186caa1136ad219431854226d734106030a8400aad8298f644400156b0990cc32009e1f21975885100053ac0ce1b2a8400e4d534cb62c40014dd0421eca880031bdcb73596210071ba9a8630a8400c3f75d916244001c9aa6992c1108029be15
  | 11 => 0x904f556f08b80c2a10029b60b31d95201cf1d286a1b222000c6d53dc964440014eb06328c2a1003351cf61581420062fb9aa7b128000a748158f654800147b0998eca880031d19471581420054ec24e5b1a2000c5c73d95624400199cedb18c48800e2f211751854002e75382c5108200087e871cf65440018baebb1c42880121fe1975182210245fc3aa9b222000ae58294c61508014ef0ab18c2a10121fa1773185402cd5b424a030a8400c3c645d62144001d28c6988c88800b331cd3258a1000e563928430a800087e8754d6448401a5884bacc0a10b68f21564905210070e328c9b1a204187c86dd561480ab5cb04386c2a10029de15701854200636c2ee4b0c8069ad6811d7634400147b0b39ec888002b360a64d8d100063abaec330a8400ab584940615080147b09316ca880032eddb74440100263b3aca330c8000a3d85cc36444001cc8cb288c48800b171cf535891000637bb2caa144202c5c7354f6250001caea729ec2a1002ad61031185420162e39aa6b0c4000cb7641c540440010ff0cb9acb10803b154d32185420054fc1acbb222000aaf825c764440010f90ea9ac888003a319363189100052ec1cc5b2a205dc3d7419460508836d100996ca9000317dcd53586200061fba4e8b2c4200ad483584614800155f04b1ec88814a9ba0a70596210051ec20c7b2a406dc7771d4d64484090f90fa9ac4880031b18b75589100062e42ee6b222000a3c8558c64440f5d488430cc0a10023be0973586400061fb2ee8b0a40008de871cd644800187aebb2442880038718d53191100070e32ec9b1a200087d87ccb65440014df04b82cb108021f21d535824100566c1ccbb122000aaf8258c644400153d07328c8880022fe1175591102755ac26ebb0a840087d8790d658840147b08192ca080030f5d074d9520006573b6c83122002c5c7354d64440014bf0ab96c6880030fdd542582412953741662b2c4200a6c8258f65440011ed03baec91080237a1c635891031f52080c83122000c5d32dcf65480834db05b8eca9000237e0d755891000675bb6e4880208cc7676d94615080155f08b1ec48800e3b60b75d854200747b26c6312200487e85dc961900abd48c9b8a84900028fa1371d952021537416e3b2a4000e4d534cb648840159f06b2ec4880032d19371481100052ec2ce5b1a2000c9c74d8d62440011e902baac890002b9e05631891000557424cbb1220008ef825cd64440e356d03ba2c910802b3a0e65d89100063b32ee2a10206ea76811c165884014db0b326c4881363d204765091001c5e422eab0c40028de839d942c40018eecbb8a84880029b61731d89100043f438c6b2c420087d8799764884018deebb92c88819f1b9d953d89100051e42ae1b22205ba6e821cf65508018b8ebb1ac4880039354d32185200055ac24a6
  | 12 => 0x63ba1f72591100051ec2061b2a8400a3e85cc364440b94db0439ecaa1002b3e0d6518910006373b0ca3122000a9e849cb63440014eb0b39ec2a10028fe1570d91100062fb9ac6b2c425be2c62dd542500ff5cb05318c2a1003a3d9063d891002c7ac3c6330c4092e367419761508010fb0f21eca880030fdd153589100054f424c9b1a2002cce734cb64884d9e4884a9ec2a10029ee0163d95420062fbaae5b1a2059ce4761c542480019a8c638a84880023d61c50d85420076231a62312204dae4825d461508014eb0a318c2a10039319763189100045fc22eab0c40008f68718560508015ad06380c2a114b1b18975885100062fb2ee6b1220008be87d9162441134ed0b328c2a1002ab61275d8910005d3c0a8520c4200a9e839976444001878e832ac4880028fe1563d91100043f43860b2c4200c5d7354f61508014dd0b986c4880029721572d8d102cd5b420a630a8400a9e849976344001c98c6a98c4880162fa1f545921000566c1683b1a2000e2c6519062440018bee7a9ac4882338d5d365d85422953741060b2c4200a9e86193634400795ce8a12c1108029da1b53d85420063bb2ae33028400a6d851cf62440018bee739aca080021fa1c75589100054ec18a5b222027a6c85592214849b56b08398c2a100317dcd32d95100043ec3cebb16204dae6821cc61508010ff0fb2c42880021f61b75508100043ec3865b2a2005a7a8008565040014ed0a188c2a1003351cf71591201bf2d286a1b1a2000e2c65d9062440e5cae64a98c2a100237e1d65d8d1000557c12cbb222000e4e634c965884010fb0f98aca08003174c973596212755ac26e1b0a8400a9d8399464440838d8edb2a84900029b60f65d891000572c166230a8400ace83994624400159f04b2ec688002abe1151d89100056ac18e030a8401cae7250960904014ed0b398c2a10028fa1032d95100243f436eab0a40008bf845d5624409dd48c5b8a84a00030f21175185403c752210c230284058f58794661900014d90ab18c488002bca007318542006a7b9a65b2a8400ccc731c9644400155f04b28c8880023761e65d8d100043ec3ea7b1620028ef874cb62440014eb0331ecaa10031d196719814201c7743ec4a122000c5f75dcd64440010fb0b38ec0a10029761664d8d100043f43ecab122000a9f8359464440019b6edb9a20080031d5d475d854200556c24c63122000cae7619062440018eeebb8ac8908028f61731d91100061ebaea9b224200a6d829cd6588509c6b08328c2a10029760c72594100061e3aee8b224200a6f8558f624400147b0998ecaa10021f61f32594100053ac2ce630a8400c5f7518d64440011e902b9ac8900032edd8744401000636390cab222000c5c63dd5204400153b0732ec8880031d9d671d92210043ec3cc7b2a400487c87d4d60
  | 13 => 0x4003e0080408c038040000050060fc010090120000080a13a0080b000006030088f10440a80002400000408009000044120b4018024028012ec1dc0201a0060100900104e01c0100d12e09403005028000122ad0360280500c020000000b30893540005d0002940880300e0400980c0020300600501422c26444000fa40201d096030008340aa00a43001088008070000080140c0000280001f80000002001801006000058650480000100007aa3007d9d064010b30223060081e82504602c000120023e4030000080380105a0002b80000602400c0004308a0000582a0f000c008050000000180002a204000b70280740d80800802c0100e0001b40317e000074000012d00100000100c0282d9ad0000140381735a0bc1a80f000170000010060002600b03202c000970000000680100c0040380100821c11009054008030440de26806002838144000010800000a8268860100e0122560680900201e0100011b00e0043a00300e0381383c0000000102400207c0e05400203c0102e00c0d00000b00c0f40284900000832067002034078030240882f02300801c098290ec008060cb0000000d0010040140500406002c0282800002c0980000c000040010060340009e4be0d00400201a00c190000000000800b1c41cae685600202c03005010000040260060d40681f044000000d600000cbc8b210c0002180007211010a2f248000f480b5162380400100806c0982500347c1580504a15c00011008004030020002e02c05200002c03804002348008010041464800b0000000282e00413c068140040200300720a0000281f08c1d004801012010040c204c0600003c0000000883f0120500101c00e020000010000181280025c0040002907e00000011090000030020020c0458080060f4008eb0000000180800808c0003800006c0c000004040000210100000080f8980f402002032014058e40041dc0301a074024da00b00e0100e00400a004070280780000681600a0003000c014040000070201780904a02e04c0080605e048010050003541204d0120300100a02a0989d8011260000582b85c660008290120101181800003c0a8110560000100201c0a4068000540040000f1181340880100e2e82301a00600000004028aa8000000001dc1100e11c0200501f0000000400908800d299d50300b4000250000401781600203c7d01711200c018040680a8008121fa1f75589100063bb2ee2b028402c5c7354d648800717d0fba2c488002bce0163d854200675bb0e48802000c5c65dcd60508035590ca1442a00022fe1d65191100051ec1ecbb222000a6d859906244123c6ce9a9ec2a10166b21d42501200061ebaa8430a8000a6d8210f654800147f0ab18c888002b320d64d89100063ba98e2b224000ce4621c540440014dd0b39ec488
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x16c300000b0030004c00006c054080f000040144c9754d325912000591a59534c86150801aa04220163185420052a640421d9424400144d93a177258640426892086550c6150801aa14260041185200051325d534c96284001e055350d32185420068910983194615080144f9754d32d8b1000591259534cb615080142e9610975985420040f26175508615010bc24641d4715092042e89210654c8615080150d9310b73d954242709188751c5425000144f9754d32d922100685d0d831946150801c45534c87159120006891088654c6150801a244221b53185424268920865550615090bc26641d47150a210070910a751866050801a244221563185420059164c654c861508e5c467154d32d92210161321d534c96448129e074354d321854200513e59734c96588401aa142600211854000513a5b734cb6548109c26621d47150a41
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x100032048464c654c86150801502d1884432a630a8400a8168c4260c6518542
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
  | 59 => 0x139256
  | 60 => 0x139254
  | 61 => 0xd0994
  | 62 => 0x98d14
  | 63 => 0xd0996
  | 64 => 0x180b
  | 65 => 0x1649
  | 66 => 0x134b
  | 67 => 0x14b
  | 68 => 0x141294
  | 69 => 0x141296
  | 70 => 0xd0a14
  | 71 => 0xa0d14
  | 72 => 0xd0a16
  | 73 => 0x150d
  | 74 => 0x149314
  | 75 => 0x140b14
  | 76 => 0x140b16
  | 77 => 0x28b
  | 78 => 0x184b
  | 79 => 0xd1414
  | 80 => 0x140d14
  | 81 => 0xd1416
  | 82 => 0xbcb
  | 83 => 0x19cb
  | 84 => 0x148b94
  | 85 => 0x154d
  | 86 => 0xd1494
  | 87 => 0x148d14
  | 88 => 0xd1496
  | 89 => 0x20d
  | 90 => 0x10b
  | 91 => 0x194b
  | 92 => 0x164d
  | 93 => 0x74b
  | 94 => 0x4956
  | 95 => 0x1a49
  | 96 => 0xec9
  | 97 => 0x5696
  | 98 => 0x24211
  | 99 => 0x28211
  | 100 => 0xecd
  | 101 => 0x1a4d
  | 102 => 0x20e
  | 103 => 0xecb
  | 104 => 0x1a4b
  | 105 => 0x954d4
  | 106 => 0x28e
  | 107 => 0x95456
  | 108 => 0xed853
  | 109 => 0x1a5853
  | 110 => 0xbd393
  | 111 => 0x149416
  | 112 => 0x140455
  | 113 => 0xb8293
  | 114 => 0xec293
  | 115 => 0x1a4293
  | 116 => 0xbc293
  | 117 => 0x19c293
  | 118 => 0xbc253
  | 119 => 0x44d
  | 120 => 0x28113
  | 121 => 0x21295
  | 122 => 0x29313
  | 123 => 0xcc215
  | 124 => 0xe8293
  | 125 => 0xec215
  | 126 => 0x1a4215
  | 127 => 0x20cd5
  | 128 => 0x28e93
  | 129 => 0x21a15
  | 130 => 0x29a93
  | 131 => 0x18c293
  | 132 => 0x74293
  | 133 => 0x44215
  | 134 => 0x75853
  | 135 => 0x29953
  | 136 => 0x1a8293
  | 137 => 0x28753
  | 138 => 0x194293
  | 139 => 0x164215
  | 140 => 0x195853
  | 141 => 0x184293
  | 142 => 0x45415
  | 143 => 0x75493
  | 144 => 0xed555
  | 145 => 0x1a5555
  | 146 => 0x45555
  | 147 => 0x165555
  | 148 => 0xeccc21d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1250
  | 6 => 2567
  | 5 => 1825
  | 4 => 35
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/62+packedAt gbK8 (1612+(h % 62)*6) 6) % 62)
  | 7 => 2*((h/451+packedAt gbK7 (46250+(h % 451)*11) 11) % 1250)
  | 6 => 2*((h/876+packedAt gbK6 (123216+(h % 876)*12) 12) % 2567)
  | 5 => 2*((h/636+packedAt gbK5 (107675+(h % 636)*11) 11) % 1825)
  | 4 => 2*((h/25+packedAt gbK4 (2450+(h % 25)*6) 6) % 35)
  | 3 => 2*((h/8+packedAt gbK3 (243+(h % 8)*2) 2) % 3)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fc07ff01ffe03ff81ffffff44fe7e3b1c71ff
  | 1 => 0x80ff81ffe07ffffffe07c01fbb31b3c4e7fe67
  | 2 => 0xfffffe00007ffc0ffff8001fc3c1c3ff078f87
  | 3 => 0xffffffff80000fffffffe0fc01fc07f80ff8
  | 4 => 0xfffffffffffff000000000fffe0007fff000
  | 5 => 0xff0000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x15400a5004962191804a54d9005616190c30ab
  | 1 => 0x900580b6202a8726a20681521930b2c061d665
  | 2 => 0x66ead6010c4d688b55d0028cc2c1416f068b86
  | 3 => 0x20b3652b5900400c79a52b00ec01e806b00d50
  | 4 => 0x44fc79cd9e71f2c010c00c08f7ea0007df6000
  | 5 => 0x7820400e1001830061063010ffbdffb0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38489
namespace PEqualNP.Outside.L_meta_38489
open PEqualNP.Outside.L_meta_38489.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := bs2_5_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 29 := bs3_3_0
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
theorem bs3_4_384 : Interval s3Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 473 := (concat (concat bs3_4_0 bs3_4_96) (concat bs3_4_192 (concat bs3_4_288 bs3_4_384)))
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
theorem bs3_5_576 : Interval s3Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 632 := (concat (concat bs3_5_0 (concat bs3_5_96 bs3_5_192)) (concat (concat bs3_5_288 bs3_5_384) (concat bs3_5_480 bs3_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := bs3_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat bs4_4_0 bs4_4_96)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 85 := block_range (n:=85) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 85 := bs5_3_0
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
theorem bs5_4_672 : Interval s5Atlas 4 672 82 := block_range (n:=82) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 754 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 bs5_4_672)))
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
theorem bs5_5_768 : Interval s5Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 779 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 35 := block_range (n:=35) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 35 := bgb_4_0
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
theorem bgb_5_1824 : Interval gbAtlas 5 1824 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1825 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)))) (concat (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344))) (concat (concat bgb_5_1440 bgb_5_1536) (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824)))))
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
theorem bgb_6_2496 : Interval gbAtlas 6 2496 71 := block_range (n:=71) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2567 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440)) (concat (concat bgb_6_1536 bgb_6_1632) (concat bgb_6_1728 bgb_6_1824))) (concat (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112)) (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 bgb_6_2496)))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1250 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)) (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 bgb_7_1248))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
def fullWord : Sig := 0xeeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80eeeaeae0eec8ea80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372960 * 2 ^ 32 + 4006144640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38489.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[2,6]⟩,⟨.or,[2,3]⟩,⟨.or,[4,7]⟩,⟨.and,[1,8]⟩,⟨.or,[1,6]⟩,⟨.or,[4,8]⟩,⟨.and,[9,10]⟩,⟨.and,[0,12]⟩,⟨.and,[11,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4006144640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4006144640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38489

open PEqualNP.Outside.L_meta_38489 in
theorem PEqualNP.Outside.L_meta_38489 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4006144640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4006144640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
