import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37481.Model
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


end PEqualNP.Outside.L_meta_37481.Model

namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
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

def SBf (j : Nat) : Nat := [5, 5, 6, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37481

namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
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
  | 3 => 0x83ffff007f807fffc03fff01fc03fff80f38f8
  | 4 => 0xffffffff80007ffffffffffe0003ffffffc0ff
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x104b052290851444848a8b162d545b2a535b5b
  | 2 => 0xa095d44b254a28a3a915c0ab569aa8a568adc5
  | 3 => 0x752656ea46534d2923a7d58198d335b14d38e8
  | 4 => 0x4238988c746c7232323966cd0303c6c78ec0b6
  | 5 => 0x7bc0e0f078707c3c3c3e78f1e3e207060ff600
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc00000ccc0c0c0ccc00000ccc0c0c0ccc00000ccc0c0c0ccc00000ccc0c0c0ccc00000ccc0c0c0ccc00000ccc0c0c0ccc00000ccc0c0c0ccc00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37481
namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffff00ffff807fffffff80fffc03fffff8f8ff
  | 3 => 0x7fffff00ffffffc03fffff01fffff807ff1fc7
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x104b210924851444848a8b162d545b4a936b5b
  | 2 => 0x2095e85249532ca9291740ab54c2ad9728b8ad
  | 3 => 0xc1264ad88e4a4923b225d5819a9b30c5cd15c6
  | 4 => 0x76388c9cec6c723223b9e6cd0313c6e18fc0f0
  | 5 => 0x7bc0f0e0f0707c3c3c3e78f1e3e207060efe00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xaaa0aa00a0a0a000aaa0aa00a0a0a000aaa0aa00a0a0a000aaa0aa00a0a0a000aaa0aa00a0a0a000aaa0aa00a0a0a000aaa0aa00a0a0a000aaa0aa00a0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37481
namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1054a82221967180028840be42bc42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc8414100018000018c420ca58a4a0ce14141a7294632e5290298a4985514530
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 1 => 0xffc0fffffffffffff81ff80fffffffffe38fff
  | 3 => 0x3fff01fff80fe03fffe0fff03ffc0f80fcf3cc
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4a4414423122490a01652a544a2194aa0d3615
  | 1 => 0x909228a442449414580a510a94c629546288ea
  | 3 => 0x230a4d2890e90566aaa09d6227688e06b4d34c
  | 4 => 0x3a2cb1d12481d9bb34d3064c39b3c418df03b0
  | 5 => 0x3c30c1e1c70e1e3dc71ce78f01c30860fbec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xee88aa88cc888888ee88aa88cc888888ee88aa88cc888888ee88aa88cc888888ee88aa88cc888888ee88aa88cc888888ee88aa88cc888888ee88aa88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37481
namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
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
end PEqualNP.Outside.L_meta_37481
namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x9a00000000018018287c000000122b4e5c01e0038e82504068c009400400240112aa4596001550836001994c003a2407118a24840131e0060800040c0000280080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x420000000c00561c64660052a24c6e8468000088b0000016a400003400288600000080a02a0000000006462c6a4a008e7a0400000000008c18b200a6000000240000000072ae78605e9a3c484e9832003e007c003800ac909630b69408209c580a7400000e1aa8929e000222361e6c0000007e147610aa6270448212b48a0026005c504000002e003a000000005a000054000002000903030a1500080f05000a0300000000000003000000020201010a05b7a92876c5250ebea6a15714d42d6a10853f544ca78a8995b94b41b6a96835e53906baa720db94a41b6a94835e53106baa620d794331aea9c633f544c678a898dbd4931b6292637b504c6f0a098e7d5131ce2a263cf524c798a498f5d4531eda82635c504c7b0a098d614131af298633e54c867aa990cf952219eaa4435e53886baa710d794c21aea98435e53d02baa7a057d4d40ae29a816f52502d8a4a05dd4540ba28a816e52102daa4204f952309eaa4616e528c2daa5186795230ceaa461ce528c39aa5185754630af284615d510c2bca0187694030af29e415d53c827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca7885754f10ec186215f53842b8a7084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa408760c010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x400aec68200040a318d4210b0c5414931c6d50504c7185414131d2d48504c7485214131c3952528c259650c010
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
  | 4 => packedAt s4K4 (2724+((h/30+packedAt s4K4 (2484+(h % 30)*8) 8) % 147)*8) 8
  | 3 => packedAt s4K3 (312+((h/2+packedAt s4K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xff81ffffffffffe07ffffe03fffffffe3f8fff
  | 1 => 0x3ffffff81fffffff81f03fffff03ffffc8fe3f
  | 2 => 0x3ffe03ffe03f81fffe003ffc1ffc1f01f0f3cc
  | 3 => 0xc00003ffffc001ffffffc0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x80a428890489204016524a41254431541384d5
  | 1 => 0x15085110c91248a580a414964a234aa8c83a2a
  | 2 => 0xa6149aa243a42b6aaa0a275913e91c0d70d34c
  | 3 => 0x3459634492074db34d3c81921cb38831ed03b0
  | 5 => 0x386183871c3871dc71cf39e380c210c1beec00
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888eac8eac8a888a888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37481
namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037c84a06f10940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52102faa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5987b94b30b7296617d52cc3daa5985b54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830bea9061df320c3ba64185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ee32083da64105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dd0410fa208217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xd5090afea6a177d4d42afa9a857c5350bb8a6a15714d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0df54b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41f7294836e52906faa520fb54a41b6a9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x78001310001f93f0001b6000f88000f00f1201e90000003e98139297c7c80037c000000353e000000000000000078004102486a0000004a800000000001218002940012e00006857c000ca1cc71007000000000001ab000048000001600008499902e8f40000045c0003d86e00000108a33154000f2000000000001500003f8439ac0001900b16a4a83e800000000000000001740010c2514682cca20d900000000000000000001df0cc888cf058000200000002ec8104988c22a2044f920000000000000003452c0000000000000028255c0000000000015901000000aca8524a000e68001847e4e300019a9fc1807f4824600a9604c24d9480f83d66609c9b20181cc0000046a3fc001681b80002c9bf00051c000b200053cf51912700000000001600000000268001271b80000000000019c0006800000000000000000001028000003682a0002660000020d3f87884c0003141e8000004340000014c008854240000b491c8d00020e3305a8e33ee0012300a0342a5398770009f000000000000001861f6000000000de3213ca231be000d28005246b8da1c2114838110000007cc0000027c0000000000018c198004ee08400000000358000002480012493d10c0000016e4000007980031e00000000000000000002180000000011c730fc0001480010f0000002fc8100008c000d38003fa000000000000010124c000000a89082200fc00000000000628000000060000000100c0000000000000003800000000010060000040200400200800002002004028020020040180000e010010000000000000000000000802000000000000000040000100000001006002000000030000000000000e00000000000000028000000000100000c00000004004000028030220040000100000800000002000000000040000000801201402800002000028020160000280000e0000200000200400800000018008080020000000b00001c000000020000180200400c000030000000000300000800801002000030030000000080000000000002002000018000040000100300800001001000004000020000080080000000c00008006000000040000100000000000000003002000020030000080000600000001800000020000020100140200000600000800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857
  | 3 => 0x1de000000000f2000000002242ac09875000000a4800000000000000000000000037400012850360000de0824ba000a2800346000000004d2000d4000000a500000000000012000000000000e4000000000001fa8e51f0004d600000000000001039b60005c400062000000bf0000009c400000000000658000000010189500000000000000594000003a000064800000000aa0001069d4000000002b429000000394ba80006455800210000874001a6424000000f6000000000b4352000218001ae000ce0311e86340000000000c002372da0000028c0000000028b134000538000d87f8001950000005d946080000ea29500095518800132000001f64789e8000002566cd2284c0003047126e4d00000000000000000225000418000000005f0c280000000000000000178e5a8a000000d8806000600768000000010b8000000011400050400000057000000000002aa014000000008a85701113a6308c8bc2843b8000004401c0002210ba0003b000000000000000b889c2524f000000000d200000000000032001048e750e354000de510000001730460003e28f0006a8000002c28c0001dd3b6000001000e88ec228000007280000050c000000000007700000018012c0024a00000000216458060000672b87b00000003a7b8000000006252203b000608cb000000158001b900000000000342110000c60001354b000320000002560009bc0015a0d673c000be4b4001258001e04ecb31b5162948301ce0000000000000000000000000000000000009e0000000000000017f16e000788000008180000029600042800000000000000004b8000000000000021c000000420001160000002d1420000000000000000250054000000000003f0e39e34160003280004c7d016029000488000000002451210d0009ec17a8311a2a00012d000000bd8003f400000000000000a700008e000000004faa441c00022c561322420be94c0000017a00133000000620758000000000000000000000000502000000004b60011480025e87c579e500000087000000271351f500079c6e8f70505a50780009c00000000000000001e60a60000000000066c00000000000ba0000000000018e00249852962000805468a646c00070000000000e18000000005617d0000f400000000000e90002080003505500000000000000144ae9c1000000001230000012f0004288e8000724e8428000000000000020c19e62cbd22f0009b0a6800000000039e023a000000945127840000033e001498002220004b80023600000000000000340002384c8741ff4c01a4000001ea4512b8000000006c0960002240024835e000000000000000000025000000000000000ad86d0000000000003e4148f800000000000003e400000276000000fd8001360240003700
  | 4 => 0x27800000121010000002190928e00019d0005ac000000009c12c935216720001de000668c201c3ac18470800074000000000000000000000000000041456828c39ef07250c0d83e000000001780005dc001373a2649318000000005b0025084fc0000000000000000000000d0129000280000002c600000000000000751c00200002792c3aa40d40226110590b780000054ca000000000089a6d000000001da000000001970b660ca90ec2bc5c8f40000004e8000004ca0011f80000086c8b9a2348001168c4000a5c000c70000000000000000139000120000001671727640000004e520e280013c934000004260000000000043c0000000000000000000000000001700000000036e0000002000000000000000000001ad0000000017000000000000000000001940848c8f692700000131000144000000000004c051800000000000000005e4619933b0000001bd000000068e906c34c000000e24781728e00099c0000000075c000000000507908f000000001d30000000016c0006ec00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2310c31d540c430b3588310c31d54cc030b358b300c25f654c030c7551300c27b654c0309798f54c825d63d53209d98754c827561d53209798c54c825d6315320d354f21c834d5348720ba18121c825e63d52209758f548832f62552209798c548825d63152208f993538823d64d4e20c7952538831d5494e20d358a538831e5454e20c7551538823e6414e208f590538834e53d0a20cb55042882cd6310a20d394c428834e538ca20ab19132882cd6308620b358f208825f63551209718d544826f62551209dd85544827461551209798c544825d63151209b58a534823f6454d208f19153482776154d209d185534825e63145209758c514826e65c8520ba181214825f63550209718d540825e63150209758c540827661150209d584540823e6414c208f59053082766114c209d584530825e63948209758e520826d6510820b358c42082e960108209b59632082ac644c8208fd91510823c645442097d8d510825c63544209b59621082cd63084208f992500823d64940209798e500825d6394020b358f200826f65480209ed95200825e63d53109758f54c426e62d53109b58b54c425e63953109758e54c423e6494f108f59253c426e6214f109b58853c423f6454b108f19152c425f6354b109718d52c425e6314b109758c52c425f63552109718d548426f62552109b189548425e63152109758c548426e6294e109b58a538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427b60549109b994524432f5414910cb150524434f5314910d314c524436852c4110cd152104425e63d50109758f540426e62d50109b58b540423d6595010cd185540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436860548108f990520423d64148109798c520425d63148109b988520433554d04109d594410436952c80109e594200427965840109dd9510042b464440109ed9510042e86244010
  | 1 => 0xc65e65cc931a7191324c63e64141318f590504c65e63d50319b98b540c66d62d50319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c65f6550c31b3189430c63f64548318f191520c72f6454831cb191520c74e4354831d350d520c65d658c831d354a320c74d520c831a7593310c74d52cc43197d95310c74d524c4319dd95310c65f63553219718d54c865e63153219758c54c863e6414f218f59053c86cd6310b21ab19132c863e64943218f59250c865e63943219758e50c865e63d52219758f548865e63952219758e548863e64d4e218f593538865f63542219718d508872d62d51218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d21d3588534866e65d0921d314f424872f5410921b358c424874c5310921d314e324866c654c921ab191324873b54d4121ce153504875b53d4121d614f504873b5414121ce150504875b5314121d614c504876b4214121da108504876a3214121da4c8504876a21141219798f540865d63d50219b98b540865e63150219758c540867a60150219e580540865d6594c219798c530866e6214c21d354f210866f6548421d354d21086e860484219dd9521086ac6250f4097d8d52d025c6354b40a758c42d025e63947409758e51d026e62947409b58a51d029d63d07409798e529025d6394a4097d8d519025c6354640c714f43502ac6250d40d3d4f525034c53d4940d3d4c525034c5314940c714e425029d6310940c714c425032f5210940d5d4f515035453d4540d9d4b515036452d4540d5d4c51503545314540d9d4851503645214540cdd0c51503354314540cd908515033442145408f997415029d63d0540cd14741503345150540cd146405023d6590440c754e411031d5310440c754f401023f6550040c754d40102b461500409ed95401026e62d53309b58b54cc27661d53309d58754cc26e62153309b58854cc2cc6250f308fd9152cc23c6454b30cbd9152cc32c6454b30d390d52cc34d4354b30d354a32cc34d520cb30a759331cc34d52cc730d354931cc26e62d52309b58b548c29c644ca308fd91518c23c6454630b3588318c2cd62cc23097d8d544c26f62551309b189544c27761551309d185544c25e6590d3097195434c2cc6250d3097994324c26e62145309b588514c25e65cc530a7593314c23d65950309bd89540c26c6255030c718d540c32f6255030cb189540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c31d54cc83097d95320c29c644c830c7551320c25d658c430c755
  | 2 => 0xac000810680809900038a2bcc5800000000dc80000021c001c9292348279310005a0698ed0000cc0000026a7ac608d5000768a80ea384500dd04404e64c9014a1400000002312c51c3d855274070920240ae4a8799f01ba1bcf61fe22a2387e000000838d60000006008e000214000000e40002a8ff8000c23c4000000d01c46b1e6260000d400016c2880009a0001b8bf89b000684000001ea160000000000684287d2c23a44209916a33c140003ee388620003b0634290001f6384758002186686d800000308000000004eca30003aa000ef014206218b1905094000001280e42008920b0a6000000cc000000e30b334c000001bc0000288f1fa13c004e21c03967405f17e16400016000000000000001fe0010989d3100403284c0040000700407000000040601402014000002d0340300003000070200200800008200a40401c2201c0000c080140000800020080201e03405000020000501c030240002400000000a800000000080101c1a000030000b000010000302400004030000d07c000040805c140140004000008010081003c000080902001028040300401002000000000000c0202c000081701c00028020000001c03000060100701c010540c0080805c0401006008020180004001000060101100c1f0000007402000040000001c0001000024020040305813000030380a008020140101000018060026e62947439b58a51d0e6f62543439b18950d0f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310e5e63947429758e51d0a5f63543429718d50d0a5f63546429718d5190a5e63942429758e5090b4c53d0942c714e4250b4c6254c42c754e4310a3f6550842a718d4210a6f6550842b318d4210a7a60153329e58054ccacc6250f32b358c42ccb8e4310b328fd91518ca3c64546328f992508ca3d64942328f992544ca5f63551329bd89544ca3e6515132c758c544ca5e6590d32c7152434ca5c6550d32c7151434cacc6250d32cb153324cb1c548c9329d987540ca7561d50329798c540ca5d65d0c3297594430ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320cb1e53d0e41ab189439074e5394a41d354e529074e5354a41d354d529071e5390a41a758c429071e5310a41cb548429069d63d06419798c525065d63149419798c505065d6314141ab189431065f63548419718d521069d6310841ad584421069d63d04418fd954110677655044197d8d501065c63540419bd89501066c62540419bd8954cc66c6255331c718d54cc72f6255331cb18954cc71d54d0f31c755043cc71d54ccb31a719132cc71d544cb319b98b548c66d62d5231b3189438c69d64cc6319bd89508c66c62542319758e544c66f62551319b189544c67b60551319e181544c65e65d0d3197994434
  | 3 => 0x11700042c0013e1c01b03f0ac232484e093d2681580c0032ce00000000000794001d424a814a41b6000000001fb2720000020a170000568003480000015f000614be1e70ea7385d09f00076c0000042e6e0f4000000680c10c04046bcb92150002f4f1199000254001b001a4b432000000334811561b46b8fa05c2c4674cb21112e860e880018e1442d0de2363e00316a0081881f9be23e4000015b000000680000000146895d0006781295a3c067c5d8000000000f98a1625049f8d803a1f0d98453445f465977194248670f731e7d8000494023e4b9800156000f08c32f62605f83c2c023c2f97a40e48c2319129c73c000003b26d48d11000049c000f62f01d0171060007c4aa8004081ac1800000074c000003240005380000037cc39891fa3986c994320088ef821168734da1b22d63f86a01b00050c0012b000544000ef0002901907f2b2244f50470000009e000052000000000f04bcb60000003b0c19112127e05e1e9406138001740ba10800136080020f21371166ed0a1dd3a48644a12c06a5c4350d7410604fc8880a80000020c14c824641441e075ce400932e5d86306611a0008c063000404a1152000818099293de1340003a37e39c508483fa1401d86d34e0a89c1a51b8868a580c2a80dd078e502e19c3b99512678c871fc1d06a4b32103360003016521e730070a501e44c2c8071463b8ae122356630b721238e5b4581693386185480000041cf99ed1920589308228a3c8000b72661e8000150001783b1f200056000043070800c2000394770130830001e4a99aa22c000000000005c0000003622a0000120000644e0310e00007d14c0223d10b0902c8000001570006dcb7975000228001ee2104b88a00b1122b85c8693860f4179040e668cd694f0006f4bc80003c38c2d90d31c0000019841a1041688c18a5348e8393ea0d80003e3ac000af0000960000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xd35cb58e5512401c50043c028030d0880544800006101851d8020007831506250d32c18c6312a998d0c7255043cc60e3b2a899663431d1520c831c1ac8a966218d0c745885348626bb0a621243525cc4214121a50e8990a090e495318121086923928628a81455cc4214540c2ac628e82a06155318540102863a2a4196618359152cc730c18c6312a81850c72550430c20e3b2a89906183551620c430c1aa8b1660186495318121c82863a2c529c41135da5310a20
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100340000000080c8759152cc43180c8759152cc73080c87551620c43080c8755162cc030
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
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s5K3 (1265+((h/8+packedAt s5K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (245+((h/1+packedAt s5K2 (240+(h % 1)*5) 5) % 17)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03fffffffffff81ffc0f83ffffffffce07fff
  | 1 => 0xffc0fff81ffffffe07ffffc1ff03ffff3f8e3f
  | 2 => 0xffff01ffe03f83fff800fffe1ffc1e03c3f3cc
  | 3 => 0x1ffffc003ffffff00001fffe003fc03f0
  | 4 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x148414890489410059502813254622a86034d5
  | 1 => 0xa1122810c9121096028551404a2155510d8a2a
  | 2 => 0xc28a4d2243a416aaa8249da413a9181b82d34c
  | 3 => 0x8b2cb1c492075bcd34f605311cf39063f403b0
  | 4 => 0xc30c1871c386371c738e63980c20182fb6c00
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888ece8a888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37481
namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5005fe5401ff55005fc5401ffd4c03fe5301ff54c03fc53017fd0c03fe43007f50c03fc4301ffd4807fe5201ff54807fc52017fd0801fe42007f50805fc4200ffcc801fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fd0401fe41007f50405fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0001fe40007f50005fc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84200effd9510075feca880037f65440013fb2a200eff9951001dfcca8803bfd654401d7eb2a200eff1951001df8ca8803b7c65440073e32a2000ffd9110005fec888003bf64440015fb22200dff99110015fcc888003fd64440017eb22200dff19110015f8c888003bc64440055e322200effd511006ffca88803bfd544401bfe2a22000ffd8d10005fec688003df63440016fb1a200cff98d1000dfcc688003fd63440017eb1a200cff18d1000df8c688003dc63440036e31a200effd4d10067fca68803bfd5344019fe29a200dffd0d10067fc8688003fd4344019fe21a2000ffd8910005fec488003ef624400177b122000ff9891005dfcc488003fd62440017eb122000ff1891005df8c488003ec624400176312200effd4910077fca48803bfd524401dfe292200dffd0910007fc8488003fd424401bfe212200cffcc910007fc6488003fd3244019fe192200effd4510077fca28803bfd514401dfe28a200dffd0510007fc8288003fd414401bfe20a200cffcc510007fc6288003fd3144019fe18a2000ffc8510007fc4288003fd2144001fe10a200effd4110077fca08803bfd504401dfe282200dffd0110007fc8088003fd404401bfe202200cffcc110007fc6088003fd3044019fe1822000ffc8110007fc4088003fd2044001fe1022000ffc4110007f62088003fe1044001fb0822004ffd9410045feca08023fe65040077f3282008df9941001cfcca08023fd65040117eb282000df59410004faca08013fc65040077e3282004ffd9010005fec80801ffe64040057f3202000ef990100157cc808003fd64040017eb202000ef590100057ac808013fc64040057e3202008ffd501003ffca808023fd540400ffe2a02004ffd8c10005fec60801bfe63040037f3182000f798c1000dbcc608003fd63040017eb182000f758c10005bac608013fc63040037e3182008ffd4c10037fca608023fd530400dfe2982007ffd0c10037fc8608003fd430400dfe2182004ffd8810005fec408003fe62040177f3102000fb98810005dcc408003fd62040017eb102000fb58810005dac408013fc62040177e3102008ffd4810047fca408023fd5204011fe2902007ffd0810007fc8408003fd420400ffe2102006ffcc810007fc6408003fd320400dfe190200abf98410047fea208017fe5104011fea882005ff1441003ffe8208017fe4104001fea082005ff10410037fe6208017fe3104001fe9882005ff0c410007fe4208017fe2104001fe9082005ff0841004dfcc008023ff5004009ff2802008ff54010027f8a00801fff4004009ff2002000ff50010027f8800801bff3004009ff1802000ff4c010027f86008003ff2004009ff1002000ff48010027f84008017ff1004001fb8802004ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xffd61080017eb084004ff184200affea210057fe510802bfea884015ff144200a7fe8210003fe4108001fea084014ff1042009ffe6210003fe3108001fe9884013ff0c42005ffe421002ffe2108001f7108400bff4842005ff8421002fec210802d7f3004015ffd4020027fca010057fd5008009fe2804014ffd0020027fc8010003fd4008009fe2004013ffcc020027fc6010003fd3008009fe180400bffc802005fde4010013fe2008017fd100400bff48020007da401002ff9200800bffb2e200abfd9710057fccb8800efe65c4015feb2e200abf5971002ff8cb8800efc65c400bffb262000bfd9310097fcc98800afe64c4001feb262000bf5931002ff8c98800afc64c4015ffaa62012ff95310057faa98804bfc54c400bffb1e2000bfd8f1008ffcc788006fe63c4001feb1e2000bf58f1002ff8c788006fc63c4015ffa9e2011ff94f10057faa788047fc53c4025ffa1e2011ff90f10007fa8788047fc43c400bffb162000bfd8b10007fcc58802efe62c4001feb162000bf58b1002ff8c58802efc62c4015ffa96200aff94b10057faa58802bfc52c4025ffa162000ff90b10007fa858804bfc42c4023ff9962000ff8cb10007fa6588047fc32c4015ffa8e2005ff94710057faa388017fc51c4025ffa0e2005ff90710007fa8388017fc41c4023ff98e2005ff8c710007fa6388017fc31c4001ff90e2005ff88710007fa4388017fc21c4015ffa86200aff94310057faa18802bfc50c4025ffa062000ff90310007fa818804bfc40c4023ff9862000ff8c310007fa6188047fc30c4001ff9062000ff88310007fa4188003fc20c4009ffb2c2009bfd961004ffccb0800efe6584013feb2c2009bf59610027f8cb0800efc6584009ffb242000bfd9210087fcc90800afe6484001feb242000bf59210027f8c90800afc6484013ffaa42010ff9521004ffaa908043fc5484009ffb1c2000bfd8e1007ffcc708006fe6384001feb1c2000bf58e10027f8c708006fc6384013ffa9c200fff94e1004ffaa70803ffc5384021ffa1c200fff90e10007fa870803ffc4384009ffb142000bfd8a10007fcc50802efe6284001feb142000bf58a10027f8c50802efc6284013ffa942009ff94a1004ffaa508027fc5284021ffa142000ff90a10007fa8508043fc428401fff9942000ff8ca10007fa650803ffc328401d7eb0c2009ffd461004ffca308027fd5184013fe28c2010ffd0610007fc8308003fd4184021fe20c200fffcc610007fc6308003fd318401ffe18c2000ffc8610007fc4308003fd2184001fe10c2008bf9821004ffea108013fe5084013fea842004ff14210087fe8108013fe4084001fea042004ff1021007ffe6108013fe3084001fe9842004ff0c210007fe4108013fe2084001fe9042004ff08210007fe2108003f71084001fd8
  | 2 => 0x200b7fea91006ffe548802dfeaa4401bff15220027fec710002ff6388035ff31c4001bf98e20007fac710002fd6388009fe31c4001bf18e200b7fea71006bfe538802dfea9c401aff14e200dffe871006bfe4388001fea1c401aff10e200cdfac51005bff5288017ff2944016ff54a2005ff8a51006fff4288017ff2144000ff50a2005ff8851006bff3288017ff1944000ff4ca2005ff86510013ff6188001ff30c4000bf98620007fac310002fd6188009fe30c4016ffd46200b7fca31005bfd518802dfe28c401bffd0620007fc8310003fd4188037fe20c401affcc620007fc6310003fd3188035fe18c400bffc8620007fc4310003ee2188001fe90c400bff08620007d8431002efe608802dffa844004ff942200b7faa110013fc5088037ffa044004ff90220007fa8110013fc4088035ff9844004ff8c220007fa6110013fc3088017ff9044000fbc822005ff64110067ff65480337fb2a4000dfd9520004feca90067fe65480077f32a4019ff595200cdfaca90067fc65480077e32a4019df1952001cf8ca90003ff64480017fb224018ff99120015fcc890003fd64480017eb224018ff19120015f8c890067ff5448031ff2a24019ff551200c7f8a890003ff63480017fb1a4017ff98d2000dfcc690003fd63480017eb1a4017ff18d2000df8c690067ff534802fff29a4019ff54d200bff8a690063ff434802fff21a4000ff50d200bff88690067ff5248017ff2924019ff5492005ff8a490063ff4248017ff2124000ff5092005ff8849005fff3248017ff1924000ff4c92005ff86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a4019ffd45200cffca290067fd5148033fe28a4018ffd0520007fc8290003fd4148031fe20a4017ffcc520007fc6290003fd314802ffe18a400bffc8520007de4290003fe2148001fe90a4000fb4852005ff84290067ff5048033ff2824019ff541200cff8a090063ff4048001ff2024000ff501200c7f8809005fff3048001ff1824000ff4c1200bff8609002fff2048017fd9024000ff88120007dc4090013ff65080177fb28400bff9942001dfcca1002f7e65080073f328400bff594200adfaca1002f7d65080013eb284004ff1942005df8ca10013ff64080177fb20400bff99020015fcc81002ffd64080017eb204004ff1902005df8c810057ff5408029ff2a04015ff550200a7f8a810013ff63080177fb18400bff98c2000dfcc61002ffd63080017eb184004ff18c2005df8c610057ff5308027ff2984015ff54c2009ff8a610053ff4308027ff2184000ff50c2009ff8861002efe6208017ffa90400bff9482005ffaa41002ffc5208017ffa10400bff9082005ffa841002ffc4208017ff990400bff8c82005ffa641002ffc3208009ffb08400bff98420005fcc21002
  | 3 => 0xf20c6000ff5063010ff88318007ff318c003ff18c6000f78c63000ffa6318007fc318c003ee18c6000ffc8630007fc4318003fd218c001fe10c6001bf98230117fea118013fe508c045fea846004ff1423010ffe8118013fe408c001fea046004ff1023000ffe6118007df308c003fd9846004ff0c23000ff06118083ff654c0417fb2a6020ff9953001dfcca98083fd654c0417eb2a6020ff1953001df8ca98003ff644c0017fb22601fff99130015fcc898003fd644c0017eb22601fff19130015f8c898083ff544c03fff2a26020ff551300fff8a898006ff634c003ffa9a6001ff94d3000ffaa698007fc534c003ffa1a6001ff90d3000ffa8698007fc434c001ffb126000bfd8930007fcc498003fd624c001fe312600bbf18930107fea498083fe524c041fea926020ff149300fffe8498003fe424c001fea12601fff1093000ffe6498007fe324c003fe9926001ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c041ffa8a6020ff94530107faa298083fc514c03fffa0a6000ff90530007fa829807ffc414c003ff98a6001f7cc53000ffc6298007fd314c001ee98a6001ff0c530007fe4298003fe214c001fe90a6000ff0853000dfec098083ff504c041ff2826020ff54130107f8a09807fff404c001ff2026000ff501300fff88098007ff304c003fd9826001ff8c130007bc6098007fc304c003ee1826001fe0c13005ffecb9002eff65c8017ff32e4003bf9972005ffacb9007afd65c8017fe32e400bbf1972005ffec99002eff64c8017ff3264002bf9932005ffac990002fd64c8017fe326400bbf193200f7fea990077fe54c803dfeaa6401dff1532005ffec79002eff63c8017ff31e4001bf98f2005fbcc790006de63c8017feb1e4000bf58f2005fbac790002dd63c8017fe31e400bbf18f200f7fea790073fe53c803dfea9e401cff14f200effe8790073fe43c8001fea1e401cff10f2005ffea59002ffe52c8017fea96400bff14b2005ffe859002ffe42c8017fea16400bff10b2005ffe659002ffe32c8017fe996400bff0cb2005ffec39002ffe61c80017f30e400bff58720005fac39002ffc61c803dffa8e401eff947200f7faa39007bfc51c803bffa0e4000ff90720007fa8390077fc41c8039ff98e4000ff8c720007fa6390073fc31c8017ff90e400bfbc872005ffc439002ffd21c8001f690e400bff087200f7fea19007bfe50c803dfea86401eff143200effe8190003fe40c8001fea06401dff103200e7fe6190003fe30c8001fe986401cff0c320027fecb1005aff658802dff32c4003bf996200b7facb1005afd6588009fe32c4003bf19620027fec910002ff6488037ff3244002bf992200077cc91000abe6488001feb244000bf592200077ac910002bd6488009fe3244002bf192
  | 4 => 0x6fc639004dffa9c8025ff94e40137faa720097fc5390005ffa1c8002ff90e40017fa872000bfc4390009ffb148000ff98a4005dfcc520003fd62900017eb148004ff18a40137fea52009bfe529004dfea948026ff14a40017fe852000bfe4290005fea148002ff10a4012ffe6520003fe3290001fe9948025ff0ca40027fec320003fe61900017f30c8000ff58640005fac320013fc619004dffa8c8026ff94640137faa32009bfc5190005ffa0c8002ff906400077c832000bfd4190005fe20c8002ef1064012ffe6320003fe3190001fe98c8025ff0c640007fe4320003fe2190001fe90c8000ff08640015fcc12009bff5090009ff2848026ff54240027f8a12000bff4090005dfa048002fed0240027f8812000bf8409004bff9848004ff0c240127fecaa0092ff6550049ff32a8003bf99540127facaa0092fd6550049fe32a8003bf19540015fec8a000bff5450005ff2a28002ff55140017f8a8a0003ff63500017fb1a8000f7d8d40005bec6a008ffe63500037f31a8000ff58d4011ff8c6a0006fc6350001ee31a8001b718d40127fea6a008ffe5350049fea9a8023ff14d40017fe86a000bbf4350005ff21a8002ff50d400077a86a000bfc4350001ffb128000bfd8940007fcc4a0003fd6250001fe312800bbf18940127fea4a0093fe5250049fea928024ff14940017fe84a000bfe4250001df2128002ff50940017f884a000bbc4250047ff9928000ff8c940007fa64a008ffc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf18540127fea2a0093fe5150049fea8a8024ff14540017fe82a000bbf4150005ff20a8002ff505400077a82a000bfc4150047ff98a8000ff8c540007fa62a008ffc3150001ff90a8000ff88540007fa42a0003fc21500057fb028024ffd4140127fca0a0093fd5050049fe2828002ffd0140017f680a000bfe4050001df2028002ff101400177880a000bf84050047ff9828023ff0c140027fecb1808aff658c045ff32c6003bf99630116fccb1800e7e658c045feb2c6022bf59630006facb180027d658c009fe32c6003bf19630027fec918002ff648c043ff3246002bf99230007fac918002fd648c009fe3246002bf19230117fea918087fe548c045feaa46021ff1523000dfac718007ff538c003ff29c6001ff54e3000ff8a718007ff438c043efa1c6001ff90e3000ffa8718007fc438c003ee21c6004ffd8a30007fcc51802efe628c001feb146000bf58a30027f8c51808bff528c045ff2946022ff54a30117f8a518087ff428c001ff2146000ff50a3010ff88518007ff328c003ef9946001ff8ca3000ffa6518003dd328c003fe1946004ffd8630007fcc318002fe618c001feb0c6000bf58630027f8c31808bff518c045ff28c6022ff54630117f8a318087ff418c001f
  | 5 => 0xca2105ffc6510803fd3288417fe194420bbf98621157fea310817fe5188455fea8c4205ff1462117ffe8310817fe4188401fea0c4205ff10621177fe6310817fe3188401fe98c4205ff0c62105ffe4310803ef2188417fb90c4205ffd8221007fcc110802fe6088401feb044200bf5822102ff8c1108abff5088455ff284422aff54221157f8a1108bfff408845ffe204422effcc221177f861108b7ff654845b7fb2a422dff9952101dfcca908b7fd654845b7eb2a422dff1952101df8ca90803ff64484017fb224200efd91210057ec8908b3fe64484057f3224200ff59121005fac8908b3fc64484057e3224200ef1912101578c8908b7ff5448459ff2a2422dff55121167f8a890803ff63484017fb1a422bff98d2100dfcc690803fd63484017eb1a422bff18d2100df8c6908b7ff5348457ff29a422dff54d2115ff8a6908b3ff4348457ff21a4200ff50d2115ff886908b7ff5248417ff292422dff5492105ff8a4908b3ff4248417ff2124200ff5092105ff884908afff3248417ff1924200ff4c92105ff864908b7ff514845bff28a422dff5452116ff8a2908b3ff4148401ff20a4200ff50521167f882908afff3148401ff18a4200ff4c52115ff8629082fff2148417fb90a4200ff88521007dc4290803ff60484017fb024200ff98121007fac090803fc60484017e302422dffd412116ffca0908b7fd504845bfe282422cffd0121167f880908afff3048457fe1824205ffd942105dfeca1082ffe65084077f328420bff5942114dfaca10817fc65084177e3284205ffd902105dfec81082ffe64084057f320420bff59021005fac810817fc64084177e3204229ffd5021147fca8108a7fd5408451fe2a04205ffd8c2105dfec61082ffe63084037f318420bf798c2100dbcc61082ffd63084017eb18420bf758c21005bac610817fc63084177e3184229ffd4c2113ffca6108a7fd530844ffe2984228ffd0c2113ffc8610803fd430844ffe218420bbf9882105ffea41082ffe5208417fea90420bff1482105ffe841082ffe4208417fea10420bff1082105ffe641082ffe3208417fe990420bff0c821155fcc2108a7ff510840bff2884229ff5442102ff8a2108a3ff410840bff2084200ff5042102ff8821089fff310840bff1884200ff4c42102ff8621082fff2108417f79084205ff8842105fec421082ffd2108401f6908420bfd4842102ffec01082ffe60084017f300420bff58021005fac010817fc6008453ffa804229ff9402114ffaa0108a7fc5008451ffa004228ff1002113ffe601089ffc3008409ffb2c8026bfd9640137fccb2000efe659004dfeb2c8026bf59640027f8cb2000efc65900057eb248002ffd5240017fca92000bfd5490005fe2a48004ffd8e4012ffcc720006fe6390001feb1c8000bf58e40027f8c720
  | 6 => 0xdff2846236ff542311b7f8a1188d7ff408c46bfe2046201ffcc23100ff86118807dc308c469ffb2a6234bfd9531006feca988027f654c469ff32a6203bf995311a7faca988d2fd654c469fe32a6203bf195311a6f8ca9880e7c654c401ffb226200bfd913119ffcc89880afe644c401feb226200bf5913119ff8c89880afc644c469ffaa26233ff951311a7faa8988cffc544c4037fb1a6201ffd4d3100ffca698807fd534c403fe29a6201ffd0d3119fbe8698807fe434c403fea1a6201ff10d3100fb88698803ff624c4017fb126200ff98931007fac498803fc624c4177e3126234ffd49311a7fca4988d3fd524c469fe2926233ffd0931007fc8498803fd424c467fe2126201ffcc93100fbe6498807fe324c403fe9926200f74c93100ff86498806ff614c469ffa8a6234ff945311a7faa2988d3fc514c467ffa0a6200ff90531007fa82988cffc414c403ff98a6201fdcc53100ffc6298803de314c403fe18a6201f70c53100fe86298803ff604c4017fb026200ff98131007fac098803fc604c4017e3026234ffd41311a7fca0988d3fd504c469fe2826233ffd013119ff88098807ff304c403ef9826201ff0c13105ffecb9082eff65c8417ff32e4203bf9972105efccb9080e7e65c8417feb2e4232bf5972105efacb908027d65c8417fe32e420bbf1972105ffec99082eff64c8417ff3264202bf9932105ffac990802fd64c8417fe326420bbf19321197fea9908c7fe54c8465feaa64231ff1532105ffec79082eff63c8417ff31e4201bf98f2105ffac790802fd63c8417fe31e420bbf18f21197fea7908c3fe53c8465fea9e4230ff14f2118ffe87908c3fe43c8401fea1e4230ff10f2105ffea59082ffe52c8417fea96420bff14b2105ffe859082ffe42c8417fea16420bff10b2105ffe659082ffe32c8417fe996420bff0cb21197fea3908cbfe51c8465fea8e4232ff1472118ffe8390803fe41c8401fea0e4231ff10721187fe6390803fe31c8401fe98e4230ff0c72105ffec19082ffe60c84017f306420bff58321005fac19082ffc60c8465ffa864232ff94321197faa1908cbfc50c8463ffa064231ff10321187fe61908c3fc30c840bffb2c422abfd9621157fccb1080efe6588455bf32c42039f99621157facb108aafd6588401beb2c42009f5962102ff8cb1080efc658840bffb244200bfd922117ffcc91080afe6488401feb244200bf5922102ff8c91080afc6488455ffaa4422fff95221157faa9108bffc548840bffb1c4200bfd8e21177fcc710806fe6388401feb1c4200bf58e2102ff8c710806fc6388455ffa9c422eff94e21157faa7108bbfc538845fffa1c422eff90e21007fa87108bbfc438845b7eb14422affd4a2105ffca5108abfd5288417fe294422fffd0a2105ffc8510803fd4288417fe214422effc
  | 7 => 0x2080efe6590475feb2c823abf5964102ff8cb2080efc65904057eb248202ffd5241017fca92080bfd5490405fe2a48205ffd8e411cffcc720806fe6390401ef31c8201b798e41007fac720802fd6390401eeb1c8200b758e4102ff8c720806fc6390475ffa9c8239ff94e411d7faa7208e7fc5390405ffa1c8202efd0e41017fc872080bfd4390401dea1c8202ff10e4102ffec520803fe62904177f3148200ff58a41005fac520817fc6290475ffa94823aff94a411d7faa5208ebfc5290405ffa148202ff90a410077c852080bfd4290405fe2148202ef10a411cffe6520803fe3290401fe9948239ff0ca41015fcc3208ebff519040bff28c823aff5464102ff8a32080bff4190405dfa0c8202fdd064102ff8832080bf44190473ff98c8205ff0c64102ffec120803fe60904017f3048200ff58241005fac120817fc6090475ffa84823aff942411d7faa1208ebfc5090405ffa048202ff102410177881208e7ff3090473fe1848238ffd95411c5fecaa08e3fe65504077f32a8238ff595411c5facaa08e3fc65504077e32a8202bfd9141017fea8a080bfe5450405feaa28202ff15141007fec6a0802ff635046fff31a8201bf98d41007fac6a08dffc63504037e31a8238ffd4d411bffca6a08e3fd535046ffe29a8202ffd0d41017fc86a080bfd4350405fe21a8200ffd8941005fec4a0803fe6250401feb128200ff1894105df8c4a08e3ff5250471ff2928238ff549411c7f8a4a080bff4250405ff2128202ff50941017f884a08dfff3250401ff1928200ff4c9411bff864a080aff6150471ffa8a8238ff945411c7faa2a08e3fc5150405ffa0a8202fdd0541017fc82a0803be4150405fe20a8202ef10541017e882a08dfff315046ffe18a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08e3ff5050471ff2828238ff541411c7f8a0a080bff4050405dfa028202ff101411bffe60a08dffc305040bffb2c6236bfd96311b7fccb1880efe658c46dfeb2c6236bf5963102ff8cb1880efc658c40bffb246200bfd92311affcc91880afe648c401feb246200bf5923102ff8c91880afc648c46dffaa46235ff952311b7faa9188d7fc548c4037eb1c6201ffd4e3100ffca718807fd538c403fe29c6201ffd0e3100ffc8718807fd438c403fe21c6205ffd8a31007fcc51882efe628c401feb146200bf58a3102ff8c5188dbff528c46dff2946236ff54a311b7f8a5188d7ff428c401ff2146200ff50a311aff88518807ff328c403ff1946201ff4ca3100ff86518806fe618c46dffa8c6205ff946311b7faa318817fc518c46bffa0c6205ff90631007fa8318817fc418c403ff98c6201f7cc63100fee6318817fc318c403fa18c6205ffd8231007fcc118802fe608c401feb046200bf5823102ff8c1188dbff508c46
  | 8 => 0xf1954205dfec8a100bff5450805ff2a28402ff55142017f8a8a1003ff63508017fb1a843fff98d4200dfcc6a1003fd635087ffe31a8401bf18d42207fea6a10fffe5350881fea9a843fff14d42017fe86a100bfe4350805fea1a8402ff10d42015fec4a1103ff5250817ff2928440ff5494205ff8a4a100bff4250805f7a12840bff9094205f7c84a102ffc4250817de2128402fb109421fffe64a102ffc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8400bf18542207fea2a1103fe5150881fea8a8440ff14542017fe82a100bfc415087fff98a843fff0c542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050881ffa828440ff94142207faa0a1103fc5050805ffa028402ff101421fffe60a10fffc3050817ffb2c640bbfd963205ffccb1900efe658c817feb2c643ebf5963205ff8cb1902efc658c817ffb24640bbfd923205ffcc91900afe648c817feb246400bf5923205ff8c91902efc648c87dffaa4643dff952321f7faa9190f7fc548c8037eb1c6401ffd4e3200ffca719007fd538c803fe29c6401ffd0e3200ffc8719007fd438c803fe21c640bbf98a3205ffea51902ffe528c817fea94640bff14a3205ffe851902ffe428c817fea14640bff10a3205ffe651902fdf328c803f7994640bff0ca3205fd8651902fff618c817ff30c6400bf9863205ffac319002fd618c817fe30c643effd46321f7fca3190fbfd518c87dfe28c643dffd06321eff88319007ff318c803fe18c640bffd823205ffcc119002fe608c817feb046400bf5823205ff8c1190fbff508c87dff284643eff542321f7f8a1190f7ff408c87bfe2046401ffcc23200ff861190f3ff654c8797fb2a6400dfd9532004feca990f3fe654c8077f32a643cff595321e5faca990f3fc654c8077e32a643cdf1953201cf8ca99003ff644c8017fb226400efd91320057ec8990effe644c8057f3226400ff59132005fac8990effc644c8057e3226400ef1913201578c8990f3ff544c877ff2a2643cff551321dff8a89902eff634c803ffa9a6401ff94d3200ffaa699007fc534c803ffa1a6401ff90d3200fbc8699007fd434c801eea1a6401ff10d3200dfec4990f3ff524c817ff292643cff5493205ff8a4990efff424c817ff2126400ff5093205ff88499007ff324c803f7992640bff8c93205fbc649902ffc324c817ee1926401fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c879ffa8a643cff945321e7faa2990f3fc514c877ffa0a643bff1053200ffe6299007df314c803fe18a6400ffd8132005fec099003fe604c801feb026400ff18132005f8c0990f3ff504c879ff282643cff541321e7f8a0990efff404c877fe2026401ffcc13200ff86099007dc304c80bffb2c823abfd96411d7fccb
  | 9 => 0x8002002800000000000a000800e00200180000000000010004000000000000800200100300140080000000004000001000000000c0020008000008000000800000000100180000000030020000002000001000c00200000080000000010000004000000000800000a0000048000000001000000000200000080080020000000010000000000000000a00100000000000000040008000005000000000600000000000040020008004000003001001c0000010008004000000001800000000000580040000030000000000003001800c0000010000004006000000803c00400200000000000040000000002000003000c0000000018000000015000001c00000000000000120050010008008000002800400a0000000000000003000000800c0000000000000001000800400c0010008014006002001000000600500000000040030000000000006000002087ffb2a8643bfd954321ffccaa180efe6550c87feb2a8643bf5954321ff8caa180efc6550c037fb228602ffd5143017fca8a180bfd5450c05fe2a28601bfd8d4300ffea6a1807fe5350c03fea9a8601ff14d4300ffe86a180bdf4350c03ff21a8601ef90d4300ff886a1807bc4350c03ee21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894305df8c4a190fff5250c87ff2928643ff5494321ff8a4a180bff4250c05fe2128601ffcc94300fbe64a1807fc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8600bf1854321ffea2a190ffe5150c87fea8a8643ff14543017fe82a180bfc4150c05de20a8601ffcc54300ff862a1803ff6050c017fb028600ff98143007fac0a1803fc6050c017e3028643ffd414321ffca0a190ffd5050c87fe2828602ffd01430177e80a180bfc4050c03ff9828601ff0c14305ffecb2102eff6590817ff32c8403bf9964205ffacb2110afd6590817fe32c840bbf19642015fac92100bff5490805ff2a48402ff55242017f8a92102fff6390817ff31c8401bf98e4205ffac721002fd6390817fe31c840bbf18e42217fea721107fe5390885fea9c8441ff14e42017fe872100bfe4390883df21c8402ff50e42017f8872100bbc43908177f314840bffd4a4205ffca52102ffd5290817fe294840bffd0a4205f7e852100bef4290817fe214840bfb10a4205ffe652102ffc3290817ffb0c840bff98642005fcc32102ffd61908017eb0c840bff18642217fea32110bfe5190885fea8c8442ff14642017fe832100bfc4190805de20c8441ffcc64220ff8632102fff6090817ff3048400bf9824205ffac121002fd6090817fe3048442ffd4242217fca12110bfd5090885fe2848402ffd02420177e812100bfc4090883ff9848441ff0c242207fecaa1102ff6550881ff32a8403bf99542207facaa1102fd6550881fe32a8403b
  | 10 => 0x4b7623117796b8000000368a0149e24280000ba030809236b80000000000001d00f5a5ca000017000075c0001808000539000000035a0003e500000006c200000000000003138000000000000000000000013000001e8000000000012000000010640003a8000000098229b00000000007a639980000002bf000000000000000000004e400000000680000000001d3cefa4020000d1800000000015b000000018b00000000002b392e8000300000000000000030c800000083d0000000c620000000000f9200000000000000020004000000000000000a00200200040040010000020002000000801c000001000000c008000002800000a000000000800200000000000040030040008000007000000c0000000020004002003000002c00600000080080000000010000000000000801400200400000040020000000000000000000001400a00b0010008000001001000000000000000080040090000000006002000000400400000200000000000000000000004000802800200e000001000e0000000004008002000000c00000a00200000000000000000002001000000800201100000000060000000018006001000000000200000000000060000000008000000000800000600100080040000010050008000001000000800000200000000000000008000000001001000c00600000000080020010010000002000000000400000000000140020020008000004000001000801600200180240000000000040000000001800000000100000000080000008004002000000800000200900000000000000000038006000000000c0020000000000002000000001c00a001000000801000000000000020000018004000004000000400000100100000060060010000000000000000800000200180040020000000000008000000800800e000000000c00200100000080000000008004000001000800400e000000001400c0000000000002000001801400a00200100180000020000000004000005800000000400000000020070050034002000001000000c001000800000200100000040040000000008000001000800000200000280040000000000000002002000000c006001001000000a00000000000060060000004004002000800000200000000040000010010004002002002800400a000002801400000000000000000000010000004000003001c00200000000140040020000000000000002800000000000000000040000028008002002000000000000200000000060000018008016000000800000000000000000020000000008002000004800401800700000080000030000000000000001800000800100400000000030000004004000000000000800000080000000050008014000000001800400200200400240000000010000002000002
  | 11 => 0x40001d780000003489a0103a6f50000000c2a56e0000000f3235732080000000cd0000000000000133000094c7222558000000517223800000000000000005a855300000000007da2bc8b2800000031400000000000470000bf65260000000b3800000000001ce0000000f880001af00000000000000000000000000000000000083c000000000000000000000000000000000c3c00022915dc0000000001bdc0006ba00006b80004423190b040000003a7000000020f3be00000000000000000e1e00039d00004ee7c300000000000000f0000000080900000000000000000ea80005920000b000000002ec00000000000000000fe2000000000000000000000001e000009c81980000000000000000000000000073e0000000000000000000076cd2674d000000000044c0000000cb60002ef00000004962ea004cd5c000000000000060900000000005df0000000000000187800000050d28804a02bc00033a0bc06727e00000a340d6169000000016c167301934000000000009b800000024300000006de00008d451c0000000000000000000000000000000018a42f20000f598584600003a219a88a075f2b0104800003217587e80001b142e89b0852000362000092800000005446bc335000017800000000000006de0000000000000000383800082844a0000000000000000140c00000000000000002c33d495980007130a800000004db18480000000002dc106800069814ea02c0000001e79558c9c000000000099400039a8000a34000000000000024b000000000000031700000006cf000000000018a0000f2c00054c0001950c1a71f00000f0c200d1000000022e00000000600003810000d6cb0a6ff0000000c7200023000000003140bf00003245ef14900000c4000000000000059f00008e41ba00000000000000003bc0a9c3ea0002289214c4800032504000006751be000103c06a26c000000000036a0000cc200000000000004f6000000011400015e0000d5e0002d080000000001ef000000000000000000000000d2800000044d000000000000000000009e66cc34e80000004d600020fc77e00000000000005fa377054c0002cd30ba0dc8f40c912d0de0e4e4403508ec800000000016f000000000000000000000000000000000000000097200000000000000000001908cf400000014ec000000000000000000004a80000004bb1238000cb23760000000c1e0000001118000000000000000000000000000000000001a140000001ea80000081d700000000000db00014ac5005bf0001db80007b32f888a01ca51d00004d0000000000155000000000019c0daa0000000000934000000000000000007f86e80000000001cc80003d3000175800000000000000000141281d60bba0d610a0000e361e800000006204742160b9
  | 12 => 0x183760003360e0c2fe1c31f597c000063a1db98442182f300002900000000000a800000001e1965892a4660000000bea21d06600000004a00000128dec7380000fe00000000000b5436810e0000d4c88a46903a1110fe60000001b200a00003f40640c960ac0320000000000134151469e4410000f7cb840000000000f4a0c700000000000000001e5458c00005b8280aea000000000023000000000000007940cc1e304ce000041800000000001f8000e5000001b9b280007ce2a9000000000000000000000b1000000101c0bd0000000d280000000d346f60c00c6000000017a24e000000000000000000000000000000000000000000000000004b06740007ac0000000c8600029b8000f300a800000000006a219317940001e908e00005280002d4000000042007c9a18000000000126030200015800000002fd26f8000fc8000000000000000000017e022c0003c91d302540e40e20000ed40000af973444a62a42c86b09203bb00000000000000000000000000000000086800007580000000000000df8a7800036180000000000000000e5e00016b1fac0002be3d919182ac00041b0e1c00000031300009a41f13c8000000003a00009a82746dd00000007ca0000000000000000067800045e31332e9344a107b83951dbc0000000000000452000090800000000042d8cec0001c92061f4827a00000000000000000000000d628153e680000007142a0068c6e432b1f184744ec0000001ef0a480000000000db600000000000000000e780000000000000b6c6b206800e80000000002408000a1e59138114e80002b61b88000284000075115505a31a3b99f7c23284227b86fc3c43511168000ea600017004e0a2429e1068000cec000376000031260e0000f340005cc000000000000008500000008223b68264e8600020e000044e1f7168800000082b000000000000019e8b3c2c039500000000007462528f3029c1fe1ff99c87405ac0000000000000000031421e00000000a400000000000000000002020cb00007f83cb8000be80000001350c7e30400006e0de20003ee000106a0000001f5c1185412b8800000000000000001b20000000000000000000000000000040000000000000000000000000000000080e0001fe00008ce699045800000000000010882ee0000000000ee87ab29e85940000000001c540004c81170000d503740000520dfa00007d8000000000000074c75a00000010dc5f00000000000abe53500000000001722ca8094cb450500010e80000003ad87f4af80003b80000bd40001919ea800022a00000000000000001aa818218e0000e640000d70ad9a8c000000000000102c0000000000ed03d00000000046000000000044617c00000000000000958000f120000000c840000000001c68000000000000038484
  | 13 => 0x982d80000bc80340c116885cc1580000b8400000034d80000006f81b0805466e48700000000000001d296080004fd02d16d10620862b80c44d780000229a98f7e00013a000071e00000009b40003421e2000074251309800000000000cb000000000000000000000001d3180400005f0001c9805400020800005060001201900ab600000000000000000000cb40000000a680000000f10000000ca600003d89440005a600000000000000ff9d1cc306e03f49c1000000000000005520002a480000008013d71020bd85870001e8c93a08416714d8000000000000054612c2b420e40002fa00000008d629125686a40000002a20000b723802c6095884a2980ea80003b000000013e8f4e07e2f400d881c810000062c00000017b071400004b000000022076900005cc0005c000008900000000000000afa7cb000000025e000000176418405427015bc00019300020a000000013e800000000000000005ae00026387044ca4a800000007b800000000000000002f01cb40000001d180000000002318fc4c6c4780001cd80004d73c1800000069230a10e03c600000006a000073d00000000000000000b4c0000001c400000000000001a2c00013c00000000000000000ba483000000000000006210001c8c000000000000091450915d0000f222030000000000000000000081400042280006ee28227f9be8ccc000000214400085525a800033600034d09700000000169fd00006b0076972000000000000007c80000000cc07600002858a200008252e812fc93c1a4238a04800000000016a8000000000000055c42f000000095c0003e204cc00023c0001fbcc6630113c00000003d40000000f0e0000000000188000000000080a19e0b08adc03e4c522f80009f6000000000042c7a03410000bf2000216938463a6b700007680000002678268f8436000000000000000001ae03b800000f03cc0002b10000ed400015d053151c6d00ba38680000000000000c6c93e58000000000000000000000000492000061478a09133684c41a80000000bc44340000000000c40075425052c71255d00000000001040708db8a280000000fb80000001de00000000002d91c58000000176180000000000000009e07d800000000aa0002730f6c60a078000000017657300000000000030000d1c0004c300000000001200000000000748000080000014000013acd6849725b1c480003e6096800000000037c8000ae43ca3e31c2000000017a00000000000000000000000000000029238e03e800000000000013700004721c880010180000000001066000359000022236600000000006123ad000000040b0000000ec472b010a1400007591cd850c3bc00000000000006d6000126cc9e0002af0c7cf3805139a140455609b20d9660f101ef04494bccb847f13d88
  | 14 => 0x56400000028701cc000000258000000000000011d401a6d20000000000207000000012840125203380000000001b1c61000031d8774afe0000000000fa200000000000000002d78058c3467935c9d0454c0000000de40000000000000624000000000000000000000000000002670000c0e5e100003d85e4635364800000000000000000000000080000d1800000012106180000000000c1400011f8138a082cb03285040000000000000000000000000000000000021500000000000000000056000210c7ac67d00016d800000021e1a0c0000000000d2090436c00000003a800000000000000003da800000000019c09880000000000000000000000000000055a00000080001023980000ad24ec000000000000000000004fc000000000000007a000000082600041620345f20000f28000f3e63c2e99a7c0e00000e61bc084e00040307cc12670c1e48000ea00000001520000687000000000052100000000007dd33289e873800000016780dc613000017400000021318e00006dc16e8000494599000000036e0000001a04ca41800000000d7e0000000e504c20000000eb800000027a00000003f300000000005d20001680c566563c103f8000000000082800000000000000002c90440df50340000000000df6000000000000000036d00008b23f902c0000d7a00022b89cc00000000017d869403b2d294b400000029603f00002540000e480000000000000000000000000000029a01700000000000308000000000000000000046a265a05c00a3313fe00004ba00039496e80003b30000000ec28271811a20ec04e201200004364331940348d5a79e034800000000000002c80001370001bf8000000000001c000257191000000023b0000000fce85c000000031e0000cd081085461c0509e180000000001a1000000000005bc7b40000000000b364de10a85f452a1b629480289227db00000000004f2097000000038a00000000002ad2ed99dc0003560d3000000000041f0000b020a9000000000000000000002b2000000000059081f293800109807701f00000000003ab00000007810001194424219370803c70c1ec0000000000000000000000000000015e0d4e0ca2190c2c6983d8000000002e3e700006ac0000000b51150a8c71e000000000036a0000000ea85e60000840c8e00000000009880000000000a38000000000000000000000bc1d800000007b40002bd00015ac0387b92ae1aa47523e1199000000000000018200007050000c6000000000000000000000000000cce00000003700007e600000000000001e3800000066404e08600000000000000000000000000000005b00004c80001d000317acac82970000a94e140000000000b8c36708584fc00000000013e000000023b800000000042b800094e0001f619544f80
  | 15 => 0x54f0319e3400009d0000000000000000162432a00000000000006780000000d4a000000000000000000000000001990e5800095200014b00005c4000000041800000000019400000001610000000164000000049e400000000034057b00000007a200000000000000003ff00000005cb16e00005580000001560000648000032097c00005a80000000000000000aa20003dd82e0b3a6e221b00300002b31bfa04c000000000117000000007c213400000000020100005c900000000000000000098000000000000000011f0000000900170000000017c2ed19210f400000007b9edc11e72e00001b10047e21af9bace321d2000000000000000000000000000000000000000000000000000000000000000000000000b207af39f000000042e0000000b267d03fd8618000000171800033e53117a80000001ce306000050a000000000003600000000000006c60002100fa80390ba049800068e1dc8c5c3e000000000002a4000172191038c7200de0b7caf42b227c8bb8ec8000000103437200000000004e0000000087c27c0000b700006543f600000000002d81de80004925230f380008f20000000000c5e44900000000000000de85140005e20000000dc80000000000000000121000082e0000001f3c1a0067000148874463d00001f008c00000000000008033a9000000000000020e8d7c0fa1a18830c987240000000000000000000000070000000000000002a180000000000000000b6a6d90000000000246000000087c6251058cf10b07ff3779acce38424000000000000000005d50704b11b800000001b22830000812658000152800031908a9bc80004620000000fea0002ca000000079300000000120000001db000000000000000000002740000000000000094c3d42c40a216340000000919324bb417100000000000000001dd895e000000000000023700009bc0007be00000000000000000ff4ffa4a300021680003ba221936800016212f80001867c800003180004cd33f1a7000041d000000072e000350000000000029295b4f160003928000f0a0002270354000000000000000028f00000000000003558de8000000146000104000000003683e47bd32f000000000000000c04c878000006440004392fb93d4c5a72c1999c84ce26c0000000033820e23e00000007e135600000000000000fd08bc00000020840000000001a5400000000080000000000001c5ccdc00000000000580003fd000000023400000000002af00000010a40000000cbc00000000000000007d319d0f5c0004b20c69ba42a80000bd800000000000c80000000000000000c6e0000000a70cc60d80001478000315144a0d00006c517f122026c16c00002b80000000000000f8a0000001cec0000000001364b060001498eac0006a40000000cf66e73f61
  | 16 => 0x178c8462691a80000b164683e60000eea1e12f704a400000028c058c76c68f0539d2c000000311a06410e2523bb81005084e500000e000000011c00000000002c2041c000000379800000000000000000000000000000be425901100000000de0000000000000247000000032039c965c69c3ef00000008f6097000153800000003b000000000028500001fa56a0700000d6a000000103c00038d0001e3c06a44f00019a000000000011c0a003272e380000004e9286118400000038c00010ac709089800000000000000000000000a516f800000000007b8dbe61f000014c1c600000000000000000000000f2c3dd1458000344000000000000000000020c00000002498000a9a5501f5179c0000000000000000000000214c73057600000008d80002ff8ad4c3a0001d893184b04b827e14c80008322768a1c9320e800019bc00000000000009a600037e00000000000000000f8000e3bc800000000000008e80000000000000b5200013f939c00030a25e80009122a10000000d9a000294000000009f0841d947ea80838300000001aa110000000024426000005540001ce80000000f500000006e60003fc80000000000000938da621700000002d02e700005980000003aa80000000000000d6800000015d88446b839600000000000000e000000000000ca0904fac17821f800000000000019ac00000006f9dfc6a40000000d8c80c00000002bc2d60000000fe800046e2b180000005ce1388f380000003180b48f5000000010ec3ec00028893b800069608680000000001dc051ccd23f21358914a0e11e02b80000000ee0000000bda00000000000000001ff000000034900000003ac82f1e004680004032109fb400023e00013a80000000001d143be0000fd8000000533000182ca840b318e1ec40000001cf1480a042fb000000011a103000000000000000000009c6000000000000000000011580000003bd80000000ad0000000cf82f703c800000000000000000001833b30d88000000110800073465f3a88000000000000082429800004007200006f400000006da0003608fecb3462c20f0790c685ad0000000f446cb24616c47167ea00000000007b63c20ba800000000011cca70000000000104800016d0000000000000000000015c28a895400013b1df02f0e1600035d80000847de1fb8000d1a000000000000000029f0000000000372800067e0000001168fe047e0e69dad022329000000044c3ac0001cc40003e82de93541687490001a2505c52e000009c00020100008cca327ba32b9e8400000000000000005cf3b89e6864a35816f08ac00047d0000000000000000000000000008a01fce7e00000000000000b00000124f140003da0a7c00000038811900003750001fdc00021c00000003a21b01c117f809e0000000000244
  | 17 => 0x197000023600000000003f0000000000082a00000000008ba00000000005a030724780000000000001d5c00000000000004260000000e9000079d0268000bae5a30ec80000000001e080010925c133f8000ac200015c947c0000000000e3000000000000000000003030000000673245800104c00000018f800000000008d80000003cd8000fe400000000000000000da80001c40000000d7409800008080004107c10a780008ec6ea0000000afc3af000155c00000000000000000000000000a3600000000000005a41f481bd09c82a1639fb80000810d980000005a73311770000000000000000025b000000000000000000008b653f2db800006612400000000da00040c211c66c61b30280009660001b48fc07265e90000b14000000000000000024c0000000d3c000000000000000040e00000000000ad00000000002368f480000003b90000ba20000000278458109000000000000009a8000000000000000000043521580000000000000000da0000000000082c2ff152010c0000001e300000002633f280010140713480d000000002f9800000010500000000000000000000b8827500000000000004078000954000330090c0000000000000b0c00000000000000f242789340006ed3f182e414a0000001b604f20003871c443e8000000000000078e00000002ae4a10000000ca20000698000000000000000010a44b0238978000000000000000000001000010960000000000dc63440001df863c000000000000011232493080000000000554000000000068401604107316280002cc0e514d10760001aa80000003062aa90c467c0003450000f606971240aa0000299009112000000000000009680ef00000000005ab0001e9000030e0000ad000003d151000000076714802890907032980d945f81e600008f42da222000107c0000001a580001d23d900017f000000040a000038e0000000000000000000000076858e0001330310574000000000000000013f88a60aa0938000e024ac0001de8ec60000000a04baa21e000000000000000008c8ac42d90241f1cb103850000f080000000000000c4434526e9d7400048d0cb8000c8a458000208c0006ce102800000056505180000000000391f546d671d414800000000000891bc196000022000000073c00000000000000000c3494400000017149060280000d0508c6e802914580002860d39ad800000000002ac0003a71f680000624301c200000000002778208b8681b0fc84942ec7d90000cd00000000000000000146000000079039040380000000000000ae0fec0003269d280000003a11b984040002c7800096e0000000000c0800000001640000000000000000000000152c00000000000006a80bf42080000000000000a283f80001f00c0c822000000
  | 18 => 0x29506f8e6e0001b200000000002d980ac9781870301390bfa008000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x4415041008cff764c4100057f754c4100457c754c4101a67e654c4100067d654c41019ebe644c410006bd644c41000ede634c410006dd634c410006ee624c410006ed624c410004fd76c84100457e75c84100057d75c84101967e65c84100067d65c841018ebe64c8410006bd64c8410186de63c8410006dd63c841005eee62c8410006ed62c8410004ff764841016e7e65484100067d6548410005bf744841003dbc7448410166be6448410006bd644841015ede6348410006dd634841005eee6248410006ed6248410084ff76500101267e65500100067d6550010016be6450010006bd6450010005df7350010035dc735001011ede6350010006dd6350010006ee6250010006ed625001007cff764c0101067e654c0100067d654c0100febe644c010006bd644c01000ede634c010006dd634c010006ee624c010006ed624c010004fd76c80100f67e65c80100067d65c80100eebe64c8010006bd64c8010035de73c8010005dd73c80100e6de63c8010006dd63c801005eee62c8010006ed62c8010004ff76480100057f75480100457c75480100ce7e65480100067d65480100c6be6448010006bd64480100bede6348010006dd634801005eee6248010006ed6248010027e8204801002ef576c40100277665c40100277565c4010027b664c4010027b564c4010027d663c4010027d563c4010027e662c4010027e562c4010025f570c4010026f660c4010025f97684010026f9768401005cf976840100277a6584010027796584010027ba6484010027b96484010027da6384010027d96384010027ea6284010027e9628401002df9718401002efa6184010027f26184010004ff76440100057f75440100457c75440100767e65440100067d6544010005bf744401003dbc744401006ebe6444010006bd6444010005df7344010035dc7344010066de6344010006dd6344010005ef7244010005ec7244010006ee6244010006ed6244010025f77644010006f77644010004f7764401000777754401022f747544010027766544010027756544010007b77444010007b47444010027b66444010027b56444010007d77344010007d47344010027d66344010027d56344010007e77244010007e47244010027e66244010027e56244010025f77044010026f66044010027f2504401022ff15044010227f33044010027f0304401002dfb7644010006fb7644010004fb76440100077b754401022f78754401002f7a654401002f796544010007bb7444010007b8744401002fba644401002fb96444010007db7344010007d8734401002fda634401002fd96344010007eb7244010007e8724401002fea624401002fe96244010025fb7144010027f3714401002efa614401002ff2614401002ff2514401022ff15144010227f3314401002ff03144010
  | 1 => 0x8810004ff735881000cfe735881000cfc7358810024ff7258810026ef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef4258810006ec4258810006ef3258810006ec325881005cff715881002cfe715881005cfd715881002cfc715881002eee215881002eec215881005cff7058810024fe705881005cfd7058810024fc7058810026ee2058810026ec2058810025ef7658810006ef765881005cef7658810026ef6558810006ee65588100276e65588100066e6558810006ed65588100276d65588100066d6558810026ec6558810026ef6458810006ee6458810027ae6458810006ae6458810006ed6458810027ad6458810006ad6458810026ec6458810026ef6358810006ee6358810027ce6358810006ce6358810006ed6358810027cd6358810006cd6358810026ec6358810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eee715881002eec7158810006ef515881002eee5158810006ed515881002eec5158810006ef415881002eee415881002eec4158810006ef315881002eee315881002eec3158810026ee7058810026ec7058810006ef5058810026ee5058810006ed5058810026ec5058810006ef4058810026ee4058810026ec4058810006ef3058810026ee3058810026ec305881002eef1058810026ee1058810026ec105881005cff7690810024fe7690810004fd7690810024fc76908102167e65908100067d6590810016be6490810006bd649081020ede6390810006dd639081005eee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc76508102067e65508100067d6550810016be6450810006bd64508101fede6350810006dd635081005eee6250810006ed6250810005f7715081002df4715081005cff768c810024fe768c810004fd768c810024fc768c8101f67e658c8100067d658c8101eebe648c810006bd648c81000ede638c810006dd638c81005eee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c8100057f754c8100457c754c8101e67e654c8100067d654c810005bf744c81003dbc744c8101debe644c810006bd644c81000ede634c810006dd634c81005eee624c810006ed624c810005f7714c81002df4714c810005fb704c810025f8704c810094ff76504101c67e65504100067d6550410016be6450410006bd64504101bede6350410006dd6350410006ee6250410006ed625041002fb
  | 2 => 0x6dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006dc4258c10036df7158c1002ede7158c1002edc7158c10006df5158c1002ede5158c10006dd5158c1002edc5158c10006df4158c1002ede4158c1002edc4158c1002ede2158c1002edc2158c10036df7058c10026de7058c10026dc7058c10006df5058c10026de5058c10006dd5058c10026dc5058c10006df4058c10026de4058c10026dc4058c10026de2058c10026dc2058c1002edf1058c10026de1058c10026dc1058c10004ff7650c10024fe7650c10004fd7650c10024fc7650c1021e7e6550c100067d6550c10016be6450c10006bd6450c1000ede6350c10006dd6350c10005fb7050c10025f87050c10024ff75d881001cfe75d88100267e75d881001c7e75d8810004fd75d88100267d75d88100047d75d8810024fc75d8810014fe74d8810026be74d8810014be74d8810004fd74d8810026bd74d8810004bd74d8810024fc74d881000cfe73d8810026de73d881000cde73d8810004fd73d8810026dd73d8810004dd73d8810024fc73d881002cfe71d8810026f671d8810024fe70d8810026fa70d8810004fd76988100067e65988100067d6598810006be6498810006bd6498810006de6398810006dd6398810026ef6298810026ec6298810004ed7698810026ef6598810006ee65988100276e65988100066e6598810006ed65988100276d65988100066d6598810026ec6598810026ef6498810006ee6498810027ae6498810006ae6498810006ed6498810027ad6498810006ad6498810026ec6498810026ef6398810006ee6398810027ce6398810006ce6398810006ed6398810027cd6398810006cd6398810026ec639881005eef759881005eee759881005eed759881005eec759881005eef749881005eee749881005eed749881005eec7498810006ef5498810006ee5498810006ed5498810006ec549881005eef739881005eee739881005eed739881005eec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881002eee719881002eec7198810006ef519881002eee5198810006ed519881002eec5198810006ef419881002eee419881002eec4198810006ef319881002eee319881002eec3198810026ee7098810026ec7098810006ef5098810026ee5098810006ed5098810026ec5098810006ef4098810026ee4098810026ec4098810006ef3098810026ee3098810026ec309881002eef1098810026ee109881005cff76588100067e65588100067d6558810006be6458810006bd6458810006de6358810006dd6358810026ec6258810004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810014fc745
  | 3 => 0xc6259010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006bc325901003ebf715901002ebe715901002ebc7159010006bf515901002ebe5159010006bd515901002ebc5159010006bf315901002ebe315901002ebc315901002ebe215901002ebc215901003ebf7059010026be7059010026bc7059010006bf5059010026be5059010006bd5059010026bc5059010006bf3059010026be3059010026bc3059010026be2059010026bc205901002ebf1059010026be1059010026bc1059010024ff75d8c1001cfe75d8c100267e75d8c1001c7e75d8c10004fd75d8c100267d75d8c100047d75d8c10024fc75d8c10014fe74d8c10026be74d8c10014be74d8c10004fd74d8c10026bd74d8c10004bd74d8c10024fc74d8c10034fd73d8c1005cfe72d8c10026ee72d8c1005cee72d8c10004fd72d8c10026ed72d8c10004ed72d8c1002cfe71d8c10026f671d8c10024fe70d8c10026fa70d8c10004dd7698c10026df6598c10006de6598c100275e6598c100065e6598c10006dd6598c100275d6598c100065d6598c10026dc6598c10026df6498c10006de6498c100279e6498c100069e6498c10006dd6498c100279d6498c100069d6498c10026dc6498c10026df6298c10026dc6298c1002ede6198c10026de6098c1000cff7658c100067e6558c100067d6558c10006be6458c10006bd6458c10026dc6358c10004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10014fc7458c10024ff7358c10026df7358c10006df5358c10036de5358c10006dd5358c10036dc5358c10006df4358c10036de4358c10036dc4358c10004ff7258c1005cfc7258c10036df3258c10036dc3258c1000cff7158c1002cfe7158c1000cfd7158c1002cfc7158c1002ede3158c1002edc3158c1000cff7058c10024fe7058c1000cfd7058c10024fc7058c10026de3058c10026dc3058c10025df7658c10036df7658c1000cdf7658c10026df6558c10006de6558c100275e6558c100065e6558c10006dd6558c100275d6558c100065d6558c10026dc6558c10026df6458c10006de6458c100279e6458c100069e6458c10006dd6458c100279d6458c100069d6458c10026dc6458c10026df6258c10026dc6258c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10
  | 4 => 0x4110007eb62c4110007e862c41100067f658411004e7c6584110006bf6484110086bc6484110006df638411007edc6384110006ef6284110006ec6284110065f67684110007776584110237746584110007b76484110007b46484110007d76384110007d46384110007e76284110007e46284110007f360841100257f76594100467f765941001c7f76594100267f64594100067e64594100267c64594100267f63594100067e63594100267c63594100267f62594100267c62594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067c42594100067f32594100067c32594100467f715941002e7e71594100467d715941002e7c71594100067f415941002e7e415941002e7c41594100067f315941002e7e315941002e7c315941002e7e215941002e7c21594100467f70594100267e70594100467d70594100267c70594100067f40594100267e40594100267c40594100067f30594100267e30594100267c30594100267e20594100267c205941002e7f10594100267e10594100267c1059410024ff75d901001cfe75d90100267e75d901001c7e75d9010004fd75d90100267d75d90100047d75d9010024fc75d901003cfd74d901000cfe73d9010026de73d901000cde73d9010004fd73d9010026dd73d9010004dd73d9010024fc73d901005cfe72d9010026ee72d901005cee72d9010004fd72d9010026ed72d9010004ed72d901002cfe71d9010026f671d9010024fe70d9010026fa70d9010004bd7699010026bf6599010006be65990100273e65990100063e6599010006bd65990100273d65990100063d6599010026bc6599010026bf6399010006be6399010026bc6399010026bf6299010026bc629901002ebe6199010026be6099010014ff76590100067e65590100067d6559010026bc6459010004ff755901001cfe7559010004fd755901001cfc7559010024ff7459010026bf7459010006bf545901003ebe5459010006bd545901003ebc5459010004ff735901000cfe735901000cfc735901003ebf4359010006be435901003ebc4359010004ff725901005cfc725901003ebf425901003ebc4259010014ff715901002cfe7159010014fd715901002cfc715901002ebe415901002ebc4159010014ff7059010024fe7059010014fd7059010024fc7059010026be4059010026bc4059010025bf765901003ebf7659010014bf7659010026bf6559010006be65590100273e65590100063e6559010006bd65590100273d65590100063d6559010026bc6559010026bf6359010006be6359010026bc6359010026bf6259010026b
  | 5 => 0x1a67c654c510006bf644c51019ebc644c510006df634c51000edc634c510006ef624c510006ec624c510005fb704c510005f8704c510004fe76c8510024fc76c85100757e75c85100057d75c85100067f65c85101967c65c8510006bf64c851018ebc64c8510006df63c8510186dc63c8510006ef62c851005eec62c8510005fa70c8510005f970c8510004fe76885100757e75885100057d75885100067f65885101567c6588510006bf648851017ebc6488510006df6388510176dc6388510006ef628851005eec628851005cfc76485100067f654851016e7c6548510005bf744851006dbc7448510006bf6448510166bc6448510006df634851015edc6348510006ef624851005eec6248510005fb7048510005f87048510004fe76085100067f650851014e7c6508510006bf6408510146bc6408510065de7308510005dd7308510006df630851013edc6308510006ef620851005eec6208510094fe76901100067f65901101367c6590110006bf6490110016bc6490110006df639011012edc6390110006ef6290110006ec6290110014ff765011006cfd7650110014fc76501100067f65501101267c6550110006bf6450110016bc6450110005df7350110065dc7350110006df635011011edc6350110006ef6250110006ec6250110005f77150110005f4715011008cfe768c1100757e758c1100057d758c1100067f658c1101167c658c110006bf648c11010ebc648c110006df638c11000edc638c110006ef628c110006ec628c11000cff764c110064fd764c11000cfc764c1100067f654c1101067c654c110006bf644c1100febc644c110006df634c11000edc634c110006ef624c110006ec624c110005f7714c110005f4714c110004fe76c811002cfc76c81100067f65c81100f67c65c8110006bf64c81100eebc64c8110065de73c8110005dd73c8110006df63c81100e6dc63c8110006ef62c811005eec62c8110005f671c8110005f571c8110004fe76881100067f65881100b67c658811006dbe7488110005bd7488110006bf64881100debc6488110006df63881100d6dc6388110006ef628811005eec628811005cff7648110004fd764811005cfc76481100057f75481100757c75481100067f65481100ce7c6548110006bf64481100c6bc6448110006df63481100bedc6348110006ef624811005eec6248110005f77148110005f47148110004fe76081100757e75081100057d75081100067f65081100ae7c6508110006bf64081100a6bc6408110006df630811009edc6308110006ef620811005eec62081100067f65c41100567c65c4110006bf64c4110096bc64c4110006df63c411008edc63c4110006ef62c4110006ec62c41100077b65c411023f7865c4110007bb64c4110007b864c4110007db63c4110007d863c
  | 6 => 0x77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc631891005eee6218910006ed6218910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc631891005eef751891005eee751891005eed751891005eec751891005eef741891005eee741891005eed741891005eec7418910006ef5418910006ee5418910006ed5418910006ec541891005eef731891005eee731891005eed731891005eec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec431891005eef711891005eed7118910006ef5118910006ee5118910006ed5118910006ec5118910006ef4118910006ec4118910006ef3118910006ec311891005eef701891005eed7018910006ef5018910006ee5018910006ed5018910006ec5018910006ef4018910006ec4018910006ef3018910006ec3018910006ed101891005cff7690910004fe7690910004fd769091005cfc76909100067f65909102167c6590910006bf6490910016bc6490910006df639091020edc6390910006ef629091005eec6290910004ff7650910004fe7650910004fd7650910004fc76509100067f65509102067c6550910006bf6450910016bc6450910006df63509101fedc6350910006ef625091005eec625091005cff768c910004fe768c910004fd768c91005cfc768c9100067f658c9101f67c658c910006bf648c9101eebc648c910006df638c91000edc638c910006ef628c91005eec628c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100757c754c9100067f654c9101e67c654c910005bf744c91006dbc744c910006bf644c9101debc644c910006df634c91000edc634c910006ef624c91005eec624c910084fe76905100067f65905101d67c6590510006bf6490510016bc6490510065de7390510005dd7390510006df63905101cedc6390510006ef6290510006ec6290510014fc76505100067f65505101c67c6550510006bf6450510016bc6450510006df63505101bedc6350510006ef6250510006ec6250510005fb7050510005f8705051007cfe768c5100067f658c5101b67c658c510006bf648c5101aebc648c510006df638c51000edc638c510006ef628c510006ec628c51000cfc764c5100057f754c5100757c754c5100067f654c510
  | 7 => 0x8d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1021e7c6550d10006bf6450d10016bc6450d10006df6350d1000edc6350d1005cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d891000cfe73d8910004fd73d891000cfc73d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef42d8910006ec42d8910006ef32d8910006ec32d891002cfe71d891002cfc71d8910024fe70d8910024fc70d891005cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ec41d8910006ef31d8910006ec31d8910006ef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ec40d8910006ef30d8910006ec30d89100757e75989100057d75989100067f65989100067c659891006dbe7498910005bd7498910006bf6498910006bc6498910065de7398910005dd7398910006df6398910006dc6398910006ef62989100057f75589100757c75589100067f65589100067c6558910005bf745891006dbc7458910006bf6458910006bc6458910005df7358910065dc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f
  | 8 => 0x1cfe7559110004fd755911001cfc75591100067c755911001c7c755911006cff7459110006bf7459110004ff7359110006df7359110004df735911000cfe735911000cfc7359110006dc735911000cdc7359110004ff7259110006ef7259110004ef725911005cfc7259110006ec725911005cec7259110084ff7159110006f77159110094ff7059110006fb7059110005be761911006ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc631911000cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10066de63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df53d8d10066de53d8d10006dd53d8d10066dc53d8d10006df43d8d10066de43d8d10066dc43d8d1005cfe72d8d10004fd72d8d10066df32d8d10066dc32d8d1002cfe71d8d10064fd71d8d1002cfc71d8d10066df31d8d10024fe70d8d10064fd70d8d10024fc70d8d10066df30d8d10065de76d8d1000cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006dc42d8d10006df71d8d10066de71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df70d8d10066de70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006dc40d8d100057f7558d100757c7558d100067f6558d100067c6558d10005bf7458d1006dbc7458d10006bf6458d10006bc6458d10066dc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10014fc7458d10006bc7458d10014bc7458d10064ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1005cfc7258d10006ec7258d1005cec7258d1007cff7158d10006f77158d1008cff7058d10006fb7058d10005de7618d10066de7618d10004de7618d10006df6518d100075f6518d100065f651
  | 9 => 0xd7588610006ef628861005eec628861005cff7648610005bf7448610085bc744861005eee6248610006ed6248610005fb7048610025f8704861007dde7308610005dd7308610006ef620861005eec620861003cff7650210026bf6450210026bc6450210005df735021007ddc7350210034ff764c210026df634c210026dc634c21007dde73c8210005dd73c8210026ef62c8210026ec62c82100057f754821004d7c7548210026ef6248210026ec6248210025f576c4210006f576c4210005f976c421002ef976c42100757e76d95100767e76d951001c7e76d95100067e64d95100067c64d95100067e63d95100067c63d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f32d95100067c32d95100067f71d95100767e71d95100767d71d95100767c71d95100067f41d95100067c41d95100067f31d95100067c31d95100067f70d95100767e70d95100767d70d95100767c70d95100067f40d95100067c40d95100067f30d95100067c30d95100767d10d9510014fe76d91100067f65d91100067c65d911006ebe64d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d911006ebe54d9110006bd54d911006ebc54d911000cfe73d9110004fd73d911000cfc73d911006ebf43d9110006be43d911006ebc43d911005cfe72d9110004fd72d911006ebf42d911006ebc42d911002cfe71d911006cfd71d911002cfc71d911006ebf41d9110024fe70d911006cfd70d9110024fc70d911006ebf40d911006dbe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006bc32d9110006bf71d911006ebe71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006bc31d9110006bf70d911006ebe70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006bc30d91100057f75591100757c75591100067f65591100067c655911006ebc6459110005df7359110065dc7359110005ef7259110005ec7259110004ff75591100067f75591100047f7559110
  | 10 => 0x9210004fd72d9210026f571d9210086bc41d9210026fa70d9210026bf40d9210014ff7659210026bc6459210005df735921007ddc7359210004ff755921001cfe7559210004fd755921001cfc7559210026bf7459210004ff7359210006df7359210004df735921000cfe735921000cfc7359210006dc735921000cdc7359210086bf4359210004ff725921005cfc7259210086bc4259210086bf4159210026be4059210026bc4059210024ff75d8e1001cfe75d8e100267e75d8e1001c7e75d8e10004fd75d8e100267d75d8e100047d75d8e10024fc75d8e10014fe74d8e10004fd74d8e10024fc74d8e1007cfd73d8e10006df43d8e1007edc43d8e1005cfe72d8e10004fd72d8e1007edf32d8e10026f571d8e1007edc31d8e10026fa70d8e10026df30d8e1000cff7658e10026dc6358e10004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10014fe7458e10014fc7458e10026df7358e10004ff7258e1005cfc7258e1007edf3158e10026de3058e10026dc3058e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10016be6450e10006bd6450e10024ff75d8a1001cfe75d8a10004fd75d8a10024fc75d8a10014fe74d8a10026be74d8a10014be74d8a10004fd74d8a10026bd74d8a10004bd74d8a10024fc74d8a1000cfe73d8a10004fd73d8a10024fc73d8a10026f571d8a10026fa70d8a10004fd7698a1007dde7398a10005dd7398a10026ef6298a10026ec6298a1005cff7658a100057f7558a1004d7c7558a10026ec6258a10004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10014fe7458a10014fc7458a10004ff7358a1000cfe7358a1000cfc7358a10026ef7258a10026ee2058a10026ec2058a1005cff7690a10024fe7690a10004fd7690a10024fc7690a10016be6490a10006bd6490a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10005f77150a10005f47150a1005cff768ca10024fe768ca10004fd768ca10024fc768ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca1004d7c754ca10005bf744ca10085bc744ca10006df634ca1000edc634ca10005f7714ca10005f4714ca1006cfd7690610006bf6490610016bc649061007dde7390610005dd7390610014ff7650610024fc7650610016be6450610006bd6450610087b44150610005fb7050610025f87050610064fd768c610006df638c61000edc638c61000cff764c610024fc764c6100057f754c61004d7c754c61000ede634c610006dd634c610005fb704c610025f8704c61004d7e75c86100057d75c861005eee62c8610006ed62c8610025fa70c8610005f970c861004d7e75886100057
  | 11 => 0x2ef970d8f1008edc30d8f1000cff7658f100057f7558f100557c7558f1002edc6358f10004ff7558f100067f7558f100047f7558f1001cfe7558f10004fd7558f1001cfc7558f100067c7558f1001c7c7558f10004ff7458f10014fe7458f10014fc7458f1002edf7358f10006df4358f1008edc4358f10004ff7258f1005cfc7258f1008edf3258f1002ede3158f1002edc3158f1008edf3058f10004ff7650f1002cfe7650f10004fd7650f1002cfc7650f10006bf6450f10016bc6450f10005fb7050f10005f87050f1002cff75d8b1001cfe75d8b1002e7e75d8b1001c7e75d8b10004fd75d8b1002e7d75d8b100047d75d8b1002cfc75d8b10014fe74d8b10004fd74d8b1002cfc74d8b1000cfe73d8b10004fd73d8b1002cfc73d8b1002ef671d8b1002ef970d8b10004fd7698b100557e7598b100057d7598b1002eef6298b1002eec6298b1005cff7658b10005bf7458b10095bc7458b1002eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10006bf7458b10004bf7458b10014fe7458b10014fc7458b10006bc7458b10014bc7458b10004ff7358b1000cfe7358b1000cfc7358b1002eef7258b1002eee2158b1002eec2158b1005cff7690b1002cfe7690b10004fd7690b1002cfc7690b10006bf6490b10016bc6490b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b1005cff768cb1002cfe768cb10004fd768cb1002cfc768cb10004ff764cb1002cfe764cb10004fd764cb1002cfc764cb100057f754cb100557c754cb10005bf744cb10095bc744cb1000ede634cb10006dd634cb10005fb704cb10005f8704cb1003cff765071002ebf645071002ebc6450710034ff764c7100057f754c7100557c754c71002edf634c71002edc634c7100557e75c87100057d75c871002eef62c871002eec62c8710005bf7448710095bc744871002eef624871002eec624871006cfd7690310006bf6490310016bc6490310014ff765031002cfc7650310016be6450310006bd6450310005df735031008ddc7350310005f7715031002df47150310064fd768c3100557e758c3100057d758c310006df638c31000edc638c31000cff764c31002cfc764c31000ede634c310006dd634c310005f7714c31002df4714c31008dde73c8310005dd73c831005eee62c8310006ed62c831002df671c8310005f571c8310095be7488310005bd7488310006ef628831005eec628831005cff76483100057f75483100557c754831005eee6248310006ed6248310005f7714831002df471483100557e75083100057d7508310006ef620831005eec6208310007e92008310024ff75d921001cfe75d9210004fd75d9210024fc75d9210084fd74d921000cfe73d9210004fd73d9210024fc73d921005cfe72d
  | 12 => 0xd6450c2000ede6350c20006dd6350c2002cff759842001cfe7598420004fd759842002cfc7598420014fe7498420004fd749842002cfc749842000cfe7398420004fd739842002cfc7398420024fe7198420026f6719842005ef7219842002ef42198420026f61098420026f41098420004ff755842001cfe7558420004fd755842001cfc7558420004ff7458420006bf7458420004bf7458420014fe7458420014fc7458420006bc7458420014bc7458420004ff735842000cfe735842000cfc7358420026f7715842005ef7215842005eec215842005ef4215842005eef2058420026f61058420026f4105842002cff7690420024fe7690420004fd76904201d67e65904200067d659042025ebf6490420016bc649042009dde7390420005dd739042002ef66190420006f56190420004ff7650420004fd7650420024fc76504201c67e65504200067d6550420016be6450420006bd6450420005ef725042005dec7250420006f66150420006f5615042002cff768c420024fe768c420004fd768c4201b67e658c4200067d658c42002ef6618c420006f5618c420004ff764c420004fd764c420024fc764c4200057f754c4200ad7c754c4201a67e654c4200067d654c42000ede634c420006dd634c420005ef724c42005dec724c420006f6614c420006f5614c420005fb704c420025f8704c42005ded7688420006ed7688420004ed76884202576e75884200076d758842005f6e658842005f6d658842005dee718842005fe67188420006ed6188420005ed708842024eee608842005fea60884200dcff76500201267e65500200067d6550020026bf6450020026bc6450020005df735002009ddc73500200d4ff764c0201067e654c0200067d654c020025ef7648020006ef7648020004ef76480200076f75480202476c75480200276e65480200276d6548020005ec7148020006ed6148020025ef704802005feb7048020026ee6048020027ea6048020027ea5048020247e95048020027ea4048020007e9404802002cff75d931001cfe75d9310004fd75d931002cfc75d9310094fd74d931000cfe73d931002ede73d931000cde73d9310004fd73d931002edd73d9310004dd73d931002cfc73d9310096bf43d931005cfe72d9310004fd72d9310096bc42d931002ef671d931002ebf41d931002ef970d9310096bc40d9310014ff765931002ebc6459310004ff755931001cfe7559310004fd755931001cfc755931002ebf7459310004ff735931000cfe735931000cfc7359310004ff725931005cfc725931002ebe415931002ebc4159310096bf405931002cff75d8f1001cfe75d8f10004fd75d8f1002cfc75d8f10014fe74d8f10004fd74d8f1002cfc74d8f1008cfd73d8f1005cfe72d8f10004fd72d8f1002ef671d8f1002edf31d8f10
  | 13 => 0x8520005bf74485200c5bc7448520006f76148520006f46148520005fb7048520005f870485200076f654852026f6c6548520007af7448520007ac744852005def714852005fe77148520007e7614852002eec6148520007e46148520007eb7048520025ec7048520007e87048520005e8704852005eef604852005feb60485200ecfe76901200067f65901201367c6590120014ff76501200c4fd765012005cfc76501200067f65501201267c6550120006bf6450120016bc6450120005df73501200bddc7350120005ef725012005dec72501200e4fe768c1200cd7e758c1200057d758c1200067f658c1201167c658c12000ede638c120006dd638c12000cff764c1200bcfd764c12005cfc764c1200067f654c1201067c654c120006df634c12000edc634c120005ef724c12005dec724c1200067f65881200b67c65881200c5be7488120005bd748812005dfa708812005efb60881200076f65881202676c6588120027ae7488120027ad7488120005ed7188120006ec6188120025ee7088120026ef608812005feb60881200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067c435942005e7f725942005e7e725942005e7d725942005e7c725942005e7f425942005e7e425942005e7d425942005e7c425942005e7f325942005e7e325942005e7d325942005e7c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067c41594200067f31594200067c315942005e7f215942005e7e215942005e7d215942005e7c21594200ae7f70594200267e70594200ae7d70594200267c70594200067f40594200267e40594200267c40594200067f30594200267e30594200267c305942005e7f20594200267e205942005e7d20594200267c20594200267e10594200267c1059420004ff755902001cfe7559020004fd755902001cfc7559020024ff7459020026bf7459020004ff735902000cfe735902000cfc73590200a6bf435902005cff725902005cfe725902005cfd725902005cfc725902005ebe425902005ebc4259020004ff715902002cfc71590200a6bf4159020024fe7059020024fc7059020026be4059020026bc4059020004ff7558c2001cfe7558c20004fd7558c2001cfc7558c20004ff7458c20014fe7458c20014fc7458c20024ff7358c20026df7358c2009ede4358c2005cff7258c2005cfe7258c2005cfd7258c2005cfc7258c2005ede3258c2005edc3258c20004ff7158c2002cfc7158c2009edf3158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20004ff7650c20024fe7650c20004fd7650c20024fc7650c2021e7e6550c200067d6550c20016be6450c20006b
  | 14 => 0x67c6558d20005bf7458d200c5bc7458d200bedc6358d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20014fc7458d20006bc7458d20014bc7458d200bcff7358d20006df7358d200d4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2002cfc7158d20006f47158d20004f47158d200bedf3158d200e4ff7058d20006fb7058d200bedc3058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2021e7c6550d20005ef7250d2005dec7250d20014fc76509200067f65509202067c6550920006bf6450920016bc6450920005fb7050920005f8705092005fe8205092000cfc764c9200057f754c9200cd7c754c9200067f654c9201e67c654c920005bf744c9200c5bc744c920006df634c92000edc634c920005fb704c920005f8704c9200067f65d85200067c65d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d852000cfe73d8520004fd73d852000cfc73d8520006f741d8520006f441d8520006f731d8520006f431d85200cd7e75985200057d75985200067f65985200067c6598520006f761985200057f75585200cd7c75585200067f65585200067c6558520005bf74585200c5bc7458520005df73585200bddc73585200067f65185200067c65185200bdde7318520005dd7318520006f5611852002cff751852001cfe7518520004fd751852002cfc7518520014fe7418520004fd741852002cfc741852000cfe731852002ede731852000cde7318520004fd731852002edd7318520004dd731852002cfc7318520006f7411852002ef44118520006f7311852002ef43118520004fe7690520004fd769052002cfc76905200067f65905201d67c6590520006bf6490520016bc64905200bdde7390520005dd739052005dee7290520005ed7290520004ff7650520004fe7650520004fc76505200067f65505201c67c6550520004fe768c520004fd768c52002cfc768c5200067f658c5201b67c658c520006df638c52000edc638c52005dee728c520005ed728c520004ff764c520004fe764c520004fc764c5200057f754c5200cd7c754c5200067f654c5201a67c654c52000ede634c520006dd634c520005ee76c852005eee76c8520004ee76c852005f6e75c852005f6d75c85200076f65c852027f6c65c852002eec61c8520025ee70c852005eef60c852005feb60c85200cd7e75885200057d75885200067f65885201567c6588520275ed7288520006f7618852002ef46188520005fa7088520005f9708852005fe820885200067f654852016e7c654
  | 15 => 0xe6448620006bd6448620006f66148620006f56148620005fb7048620025f87048620005ed760862005eed7608620007ae6408620007ad640862005fce730862005fcd730862005fe67108620006ed6108620005ed700862005fea60086200a4ff7650220016be6450220006bd6450220005df73502200d5dc735022009cff764c2200febe644c220006bd644c220025ed76c822005eed76c8220027ae64c8220027ad64c822005fce73c822005fcd73c8220005ee71c8220006ed61c8220027ea60c8220027ea50c8220297e950c82200cd7e76d95200ce7e76d952001c7e76d95200067e64d95200067c64d95200067e63d95200067c63d952028f7b20d952028f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d95200067f72d952028e7e72d95200ce7d72d952028e7c72d95200067f42d952028e7e42d952028e7c42d95200067f32d952028e7e32d952028e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067c31d952028e7f21d952028e7c21d952028e7f70d95200ce7e70d95200ce7d70d95200ce7c70d95200067f40d95200067c40d95200067f30d95200067c30d952028e7f20d95200ce7d20d952028e7c20d9520014fe76d91200067f65d91200067c65d91200c6be64d9120004ff75d912001cfe75d9120004fd75d912001cfc75d912000cfe73d9120004fd73d912000cfc73d9120006be43d91200c6bc43d912005cfe72d91200c4fd72d912005cfc72d91200c6bf42d912002cfe71d9120004fd71d91200c6bc41d912005cfd70d91200c6bf40d91200057f75591200cd7c75591200067f65591200067c65591200c6bc6459120005df73591200bddc7359120005f77159120005f47159120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c75591200c4ff7459120006bf7459120004ff7359120006df7359120004df735912000cfe735912000cfc7359120006dc735912000cdc73591200dcff7259120006ef7259120286be4259120286bc4259120004ff7159120006f77159120004f7715912002cfc7159120006f47159120004f471591200ecff7059120006fb705912000cfe76d8d200067f65d8d200067c65d8d200bede63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df43d8d200bedc43d8d2005cfe72d8d200bcfd72d8d2005cfc72d8d200bedf32d8d2002cfe71d8d20004fd71d8d200bedc31d8d2005cfd70d8d200bedf30d8d200057f7558d200cd7c7558d200067f6558d20
  | 16 => 0x9220026be7059220026bc7059220006bf5059220026be5059220006bd5059220026bc5059220006bf3059220026be3059220026bc3059220286bf2059220026be2059220026bc2059220026be1059220026bc1059220024ff75d8e2001cfe75d8e200267e75d8e2001c7e75d8e20004fd75d8e200267d75d8e200047d75d8e20024fc75d8e20014fe74d8e20026be74d8e20014be74d8e20004fd74d8e20026bd74d8e20004bd74d8e20024fc74d8e200d4fd73d8e20026ed72d8e2002cfe71d8e20004fd71d8e20026fa70d8e2000cff7658e20006be6458e20006bd6458e20026dc6358e20004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20014fc7458e20026df7358e20006df5358e200d6dc5358e200d6df3258e20004ff7158e2002cfc7158e200d6df3158e20024fc7058e20026de3058e20026dc3058e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20016be6450e20006bd6450e20014ff7650a20024fc7650a20016be6450a20006bd6450a20005fb7050a20025f87050a2000cff764ca20024fc764ca200057f754ca200b57c754ca20005bf744ca200ddbc744ca201debe644ca20006bd644ca2000ede634ca20006dd634ca2005fcc324ca20005fb704ca20025f8704ca20006be6498620006bd6498620026f7619862002cff759862001cfe7598620004fd759862002cfc7598620014fe7498620004fd749862002cfc749862000cfe7398620004fd739862002cfc7398620024fe7098620026f61098620026f410986200057f75586200b57c7558620006be6458620006bd6458620026f46158620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620014fe7458620014fc7458620004ff735862000cfe735862000cfc7358620024fc7058620026f61058620026f4105862002cff7690620024fe7690620004fd7690620016be6490620006bd64906200d5de7390620005dd7390620004ff7650620004fd7650620024fc7650620016be6450620006bd6450620005ef725062005dec725062002cff768c620024fe768c620004fd768c6201aebe648c620006bd648c620004ff764c620004fd764c620024fc764c6200057f754c6200b57c754c62019ebe644c620006bd644c62000ede634c620006dd634c620005ef724c62005dec724c6200b57e75886200057d758862017ebe6488620006bd648862002ef66188620006f56188620025fa7088620005f9708862024f6e75886200076d7588620007ae6488620007ad648862005dee7188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862005eee6088620005bf74486200ddbc7448620166b
  | 17 => 0xcfc735872005ef7715872005ef7215872005ef4215872002cff769072005cfe7690720004fd7690720016be6490720006bd64907200e5de7390720005dd73907201cede6390720006dd639072005dee7290720005ed7290720004ff7650720004fd765072005cfc76507201bede6350720006dd635072002cff768c72005cfe768c720004fd768c72000ede638c720006dd638c72005dee728c720005ed728c720004ff764c720004fd764c72005cfc764c7200057f754c7200f57c754c72000ede634c720006dd634c720005fb704c720005f8704c72005def7648720006ef7648720007af7448720007ac744872005fce634872005fcd634872005fe7714872002eee6148720025ec70487200c4fd769032012ede6390320006dd6390320014ff765032005cfc7650320016be6450320006bd6450320005df73503200e5dc735032011ede6350320006dd6350320005ef725032005dec72503200bcfd768c3200f57e758c3200057d758c32000ede638c320006dd638c32000cff764c32005cfc764c32000ede634c320006dd634c320005ef724c32005dec724c320024ff75d922001cfe75d9220004fd75d9220024fc75d92200dcfd74d922000cfe73d9220004fd73d9220024fc73d9220026ed72d922002cfe71d9220004fd71d9220026fa70d9220004bd76992200df3e75992200df3d7599220026bf6599220006be6599220006bd6599220026bc6599220026bf6399220006be6399220026bc6399220026bf6199220026bc6199220026be609922029fbb2099220027b82099220014ff7659220026bc6459220004ff755922001cfe7559220004fd755922001cfc7559220026bf7459220006bf54592200debe5459220006bd54592200debc5459220004ff735922000cfe735922000cfc73592200debf4359220006be43592200debc43592200debf4259220004ff715922002cfc71592200debf41592200debc4159220024fc7059220026be4059220026bc4059220025bf76592200debf7659220014bf7659220026bf6559220006be6559220006bd6559220026bc6559220026bf6359220006be6359220026bc6359220026bf6159220026bc6159220287bb2059220027b82059220006bf7559220006be7559220006bd7559220006bc7559220006bf7359220006be7359220006bd7359220006bc7359220006bf5359220006be5359220006bd5359220006bc5359220006bf7259220286be7259220006bd7259220286bc7259220006bf5259220286be5259220006bd5259220286bc5259220006bf3259220286be3259220286bc3259220006bf7159220006be7159220006bd7159220006bc7159220006bf5159220006be5159220006bd5159220006bc5159220006bf3159220006bc3159220286bf2159220286bc21592200debf705
  | 18 => 0xe7388530005dd7388530006ef628853005eec6288530004ff7648530004fe7648530004fc7648530005bf74485300fdbc7448530004fe7608530004fd760853002cfc760853000dde7308530005dd7308530006ef620853005eec6208530006f7610853002ef461085302a4fe7690130014ff765013000cfe765013011cfd765013000cfc7650130006bf6450130016bc6450130005df735013000ddc73501300275e758c1300275d758c13010ede648c13010edc648c130006df628c130005dd718c130006dc618c130025de708c130027da708c130026df608c13000fdb608c130004ff755932001cfe7559320004fd755932001cfc755932005ebf74593200eebe5459320006bd5459320004ff735932000cfe735932000cfc735932005cfc725932005ebe425932005ebc4259320004ff715932002cfc71593200eebc41593200eebf4059320004ff7558f200067f7558f200047f7558f2001cfe7558f20004fd7558f2001cfc7558f200067c7558f2001c7c7558f20004ff7458f20014fe7458f20014fc7458f2005edf7358f20006df5358f200e6de5358f20006dd5358f200e6dc5358f20006df4358f200e6de4358f200e6dc4358f2005cfc7258f2005ede3258f2005edc3258f20004ff7158f2002cfc7158f200e6df3158f200e6dc3158f200e6df3058f20006df7558f200065f7558f20006de7558f20006dd7558f20006dc7558f200065c7558f20006df7458f20006de7458f20006dd7458f20006dc7458f20006df5458f20006de5458f20006dd5458f20006dc5458f2005edf7258f2005ede7258f2005edd7258f2005edc7258f2005edf5258f2005ede5258f2005edd5258f2005edc5258f2005edf4258f2005ede4258f2005edd4258f2005edc4258f20006df7158f20006de7158f20006dd7158f20006dc7158f20006df5158f20006de5158f20006dd5158f20006dc5158f20006df4158f20006dc4158f2005edf2158f2005ede2158f2005edd2158f2005edc2158f20006df7058f20006dd7058f200e6dc7058f20006df5058f20006de5058f20006dd5058f20006dc5058f20006df4058f20006dc4058f2005edf2058f2005ede2058f2005edd2058f2005edc2058f20004ff7650f2005cfe7650f20004fd7650f2005cfc7650f2000ede6350f20006dd6350f20005ef7250f2005dec7250f2002cff759872001cfe759872002e7e759872001c7e7598720004fd759872002e7d75987200047d759872002cfc7598720014fe7498720004fd749872002cfc749872000cfe7398720004fd739872002cfc739872002ef6719872002eef219872005ef7219872002ef4219872005eec2098720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff735872000cfe7358720
  | 19 => 0x8630005df738863000ddc7388630004ff7648630004fd7648630024fc764863016e7e65486300067d6548630005bf744863010dbc7448630005df734863000ddc734863005eee6248630006ed624863002cff7608630024fe7608630004fd760863014e7e65086300067d650863000dde7308630005dd73086302b4ff76502301267e65502300067d6550230026bf6450230026bc645023010ddf735023000ddc735023010f9f4350230014fe76d91300febe64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d91300febe54d9130006bd54d9130024ff73d913000cfe73d913012cfd73d913000cfc73d913012ebf43d913012ebd43d913005cfe72d9130004fd72d91300febc42d913002cfe71d9130004fd71d91300febc41d913000cfd70d91300febf40d91300febc64591302b5fb7059130004ff755913001cfe7559130004fd755913001cfc755913012cff7459130006bf745913011cff7359130006df735913010cdf7359130004ff725913005cfc7259130004ff715913002cfc71591302b4ff7059130006fb7059130004ff75d893001cfe75d8930004fd75d893001cfc75d8930014fe74d8930004fd74d8930014fc74d89300d6ee32d89300d6ed32d893002cfe71d8930004fd71d89300d6df31d89300d6dc30d8930006ef62989300bdf970989300057f75589301057c7558930005bf74589300fdbc7458930005f77158930005f471589300e5fb705893005eee6218930006ed6218930004fe7690930004fd769093005cfc7690930006bf6490930016bc6490930004ff7650930004fe7650930004fc7650930004ff75d853001cfe75d8530004fd75d853001cfc75d8530014fe74d8530004fd74d8530014fc74d853005cfe72d8530004fd72d853007ef631d853007ef531d8530006f76198530065f970985300057f75585301057c7558530005bf74585300fdbc7458530005ef7258530005ec725853008dfb7058530006f5611853002cff751853001cfe7518530004fd751853002cfc7518530014fe7418530004fd741853002cfc741853005cfe7218530004fd721853002edf311853002ef63118530036f53118530036dc3018530004fe7690530004fd769053002cfc7690530006bf6490530016bc649053000dde7390530005dd7390530004ff7650530004fe7650530004fc76505300075f754c5302af5c754c53019ede644c53019edc644c530006df624c53000ddf714c53000fd7714c530007d7614c53002edc614c530007d4614c530007db704c530025dc704c530007d8704c53000edf604c53000fdb604c530004fe76c8530004fd76c853005cfc76c85301057e75c85300057d75c8530006f761c8530006f461c8530004fe7688530004fd768853002cfc76885301057e75885300057d758853000dd
  | 20 => 0x11edf3259230004ff715923002cfc715923010ebf4159230024fe7059230024fc7059230026be4059230026bc40592300067e6598a300067d6598a30026ef6298a30026ec6298a300067e6558a300067d6558a30026ec6258a30004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30014fc7458a30006ef4258a30006ec4258a300beee3258a300beed3258a30004ff7158a3002cfc7158a30024fc7058a30026ee2058a30026ec2058a3005cff7690a30024fe7690a30004fd7690a302167e6590a300067d6590a30016be6490a30006bd6490a3000dde7390a30005dd7390a3020f9c4390a30004ff7650a30004fd7650a30024fc7650a302067e6550a300067d6550a30005df7350a3000ddc7350a3005cdf764ca300075f754ca302c75c754ca302c75e654ca300075d654ca300079f744ca3010dde744ca3010ddc744ca300079c744ca3010d9c744ca30006df644ca30006dd644ca3000ddf724ca3000fcf724ca3005ede624ca30007ce624ca30007cd624ca3005edc624ca30005dc714ca30005df704ca30007db704ca30007d8704ca3000ede604ca3000fda604ca300067e65986300067d6598630026f7619863002cff759863001cfe7598630004fd759863002cfc7598630014fe7498630004fd749863002cfc749863005cfe7298630004fd729863002ef6319863008ef53198630024fe7098630024fc7098630026f61098630026f410986300067e65586300067d6558630005bf745863010dbc7458630026f46158630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630006bf7458630004bf7458630014fe7458630014fc7458630006bc7458630014bc7458630006df4358630066dc4358630004ff725863005cfc7258630066df3258630006dd3258630066f63158630066f53158630066dc3158630024fc7058630066df3058630026f61058630026f4105863002cff7690630024fe7690630004fd76906301d67e65906300067d6590630006bf6490630016bc649063000dde7390630005dd739063010f9f4390630004ff7650630004fd7650630024fc76506301c67e65506300067d6550630016be6450630006bd6450630005df735063000ddc73506302bf5e658c6300075d658c63010dde748c63010ddc748c630005dd728c63000dde718c63000fd6718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c63000ede608c63000fda608c63005cff76c8630024fe76c8630004fd76c86301157e75c86300057d75c86301967e65c86300067d65c863000dde73c8630005dd73c863005eee62c8630006ed62c863002cff7688630024fe7688630004fd76886301157e75886300057d75886301567e65886300067d658
  | 21 => 0xe764c540004fc764c5400057f754c5401257c754c540015be744c540005bd744c540006df634c54000edc634c54019f9f434c540004fe76c8540004fd76c854005cfc76c85401257e75c85400057d75c8540285bf74c8540015bc74c8540006df63c8540186dc63c8540006f761c8540006f461c8540004fe7688540004fd768854002cfc76885401257e75885400057d7588540015be7488540005bd7488540006df6388540176dc6388540006ef628854005eec6288540004ff7648540004fe7648540004fc7648540005bf7448540015bc7448540006df634854015edc6348540004fe7608540004fd760854002cfc7608540015be7408540005bd740854011dde7308540005dd7308540006df630854013edc6308540006ef620854005eec6208540006f7610854002ef46108540005fa7008540005f97008540005bd73901400079f63901400079c6390140285be7290140005bd7190140006bc6190140025be7090140027ba7090140026bf6090140017bb60901400257f76596301167f765963001c7f76596300267f64596300067e64596300267c64596300075f43596302cf5c43596300267f62596300267c62596302cf5f32596300267f61596300267c61596302cf5c31596300275f30596302cf7b30596300277830596300067f74596300067e74596300067d74596300067c74596302ce7f73596302ce7e73596302ce7d73596302ce7c73596302ce7f43596302ce7e43596302ce7d43596302ce7c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067c42596302ce7f32596302ce7e32596302ce7d32596302ce7c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067c41596302ce7f31596302ce7e31596302ce7d31596302ce7c31596301167f70596300267e70596302ce7d70596300267c70596300067f40596300267e40596300267c40596302ce7f30596300267e30596302ce7d30596300267c30596300267e20596300267c20596300267e10596300267c1059630024ff75d923001cfe75d92300267e75d923001c7e75d9230004fd75d92300267d75d92300047d75d9230024fc75d923011cfd74d9230026dd73d923010edf43d923012edc43d923005cfe72d9230026ee72d923005cee72d9230004fd72d9230026ed72d9230004ed72d923012edf32d923002cfe71d9230004fd71d923010ebc41d9230024fe70d9230026fa70d9230026bf40d9230014ff76592300067e65592300067d6559230026bc645923000ddc735923010f9f4359230004ff755923001cfe7559230004fd755923001cfc7559230026bf745923010edf735923011ebf435923010edf435923011ebd435923011edc4359230004ff725923005cfc725923010ebc4259230
  | 22 => 0x8d402d7d84018d4011dbc7650d4000ebc7650d4000cbc7650d40015bf7350d400179f7350d400079f6350d4000ebe6350d4000ebc6350d4011f9c6350d40285bc7250d4011f9f3250d40005bf7150d40007bb7050d40025bc7050d40007b87050d40016bf6050d40017bb6050d40006df63d8940006dc63d8940004ff75d894001cfe75d8940004fd75d894001cfc75d894000cfe73d8940004fd73d894000cfc73d8940006ef52d8940006ec52d89400deee42d89400deed42d8940286bc42d894002cfe71d8940004fd71d894011dde7398940005dd7398940006df6398940006dc6398940006ef62989400c5f970989400057f75589401257c7558940005df735894011ddc7358940006df6358940006dc6358940005f77158940005f471589400edfb70589401257e75189400057d7518940006df6318940006dc631894005eee6218940006ed6218940005bd73909400079f639094020ebe639094020ebc63909400079c639094020e9c6390940015be7290940017ae7290940286bf6290940007af6290940287ac6290940005bd7190940025be7090940287ba7090940287b97090940016bf6090940017bb6090940004fe768c940004fd768c94005cfc768c940285bf748c940015bc748c940006df638c94000edc638c940004ff764c940004fe764c940004fc764c9400057f754c9401257c754c940005bf744c940015bc744c940006df634c94000edc634c9400079d434c940006df63d8540006dc63d8540004ff75d854001cfe75d8540004fd75d854001cfc75d854000cfe73d8540004fd73d854000cfc73d854005cfe72d8540004fd72d8540006f751d8540006f451d8540086f641d8540086f541d854011dde7398540005dd7398540006df6398540006dc6398540006f7619854006df970985400057f75585401257c7558540005df735854011ddc7358540006df6358540006dc6358540005ef7258540005ec7258540095fb70585401257e75185400057d7518540006df6318540006dc6318540006f5611854002cff751854001cfe751854002e7e751854001c7e7518540004fd751854002e7d75185400047d751854002cfc751854000cfe7318540004fd731854002cfc731854003ebf4318540006bd431854005cfe7218540004fd7218540006be421854003ebc4218540006f7511854002ef4511854002ebf411854002ef6411854003ef5411854003ebc4018540005bf73505400079f63505400079c6350540285bc7250540015bf7150540017b77150540007b7615054002ebc6150540007b46150540006b46150540007bb7050540025bc7050540007b87050540016bf6050540017bb6050540004fe768c540004fd768c54002cfc768c540015be748c540005bd748c540006df638c54000edc638c540004ff764c540004f
  | 23 => 0xcfc7358640004ff725864005cfc725864006ef6415864006ef5415864006ebc4158640024fc705864006ebf4058640026f61058640026f410586400079e73906400079d7390640006bd639064025ebe6290640015be7190640017b67190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b97090640016be6090640017ba609064002cff768c640024fe768c640004fd768c640004ff764c640004fd764c640024fc764c6400057f754c6401357c754c640005bf744c640015bc744c64000ede634c640006dd634c64005cff76c8640024fe76c8640004fd76c86401357e75c86400057d75c8640015be74c8640005bd74c864005eee62c8640006ed62c864002cff7688640024fe7688640004fd76886401357e75886400057d7588640004ff7648640004fd7648640024fc7648640005bf7448640015bc744864005eee6248640006ed624864002cff7608640024fe7608640004fd760864012dde7308640005dd7308640025fa7008640005f9700864000cfe76d8d401257e75d8d400057d75d8d4011ede63d8d40004ff75d8d4001cfe75d8d400067e75d8d4001c7e75d8d40004fd75d8d400067d75d8d400047d75d8d4001cfc75d8d4000cfc74d8d40006df53d8d4011ede53d8d40006dd53d8d4011edc53d8d4011ede43d8d4010edd43d8d4005cfe72d8d40004fd72d8d4011edf32d8d4011edc32d8d4002cfe71d8d40004fd71d8d4011edf31d8d4011edc31d8d40014fd70d8d4011edf30d8d4011dde76d8d4000cde76d8d400075e75d8d400075d75d8d40006df65d8d40006de65d8d40006dd65d8d40006dc65d8d400079f74d8d4010f9c74d8d4010f9c42d8d4010f9f41d8d4010fdb40d8d4010f9c40d8d4010fd840d8d40006df75d8d40006de75d8d400065e75d8d40006dd75d8d400065d75d8d40006dc75d8d4010edf74d8d4011ede74d8d4010edc74d8d4010edf54d8d4010ede54d8d4010edd54d8d4010edc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006df52d8d40006de52d8d40006dd52d8d40006dc52d8d4010edf42d8d4010ede42d8d4010edd42d8d4010edc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d40006df51d8d40006de51d8d40006dd51d8d40006dc51d8d4010edf41d8d4010ede41d8d4010edd41d8d4010edc41d8d4010edf70d8d4011ede70d8d4010edd70d8d40006df50d8d40006de50d8d40006dd50d8d40006dc50d8d4010edf40d8d4010ede40d8d4010edc40d8d4011edc6358d402ddfb7058d4010dde7618d4011ede7618d40006df6518d40006de6518d40006dd6518d40006dc6518d4011f9e7418d4011f9d7418d4012edf6418d402d79c4218d402d79f4118d402b6df6018d402d7db4018d402d79c401
  | 24 => 0xe5158c21006dd5158c2102edc5158c21006df4158c2102ede4158c2102edc4158c2105edf2158c2102ede2158c2105edd2158c2102edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006dc4058c2105edf2058c2105ede2058c2105edd2058c2105edc2058c2102edf1058c2102edc1058c21004ff7650c2102cfe7650c21004fd7650c2102cfc7650c2100ede6350c21006dd6350c21005ef7250c2105dec7250c2117cff76504211bede6350421006dd6350421174ff764c4210057f754c42114d7c754c42100ede634c421006dd634c42102def7648421006ef7648421004ef7648421007af7448421007ac744842102fce634842102fcd634842102def714842105fe7714842102eee614842102fe66148421005ec7048421024ff759802101cfe7598021004fd7598021024fc7598021014fe7498021004fd7498021024fc749802100cfe7398021004fd7398021024fc7398021026fa7098021026fa5098021006f9509802105efb2098021026f8209802102efb1098021026f81098021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021014fe7458021014fc7458021004ff735802100cfe735802100cfc735802105eef2158021006ed215802102efb7058021006fa5058021006f9505802105efb205802105eec205802105ef8205802102efb105802102ef8105802100cff7658e40026dc6358e40004ff7558e4001cfe7558e40004fd7558e4001cfc7558e4012ede4358e400fedd4358e40004ff7258e4005cfc7258e40004ff7158e4002cfc7158e400febc4158e4012edf3158e40024fe7058e40024fc7058e400febf4058e40026de3058e40026dc3058e4012dde7398a40005dd7398a40026ef6298a40026ec6298a40026ec6258a40004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a4000cfe7358a4000cfc7358a40006ee5258a40006ed5258a400c6ee4258a400c6ed4258a40006ef3258a40006ec3258a40004ff7158a4002cfc7158a40024fc7058a40026ee2058a40026ec2058a4005cff768ca40024fe768ca40004fd768ca40004ff764ca40004fd764ca40024fc764ca400057f754ca401357c754ca40005bf744ca40015bc744ca4000edc634ca40026f7619864002cff759864001cfe7598640004fd759864002cfc759864000cfe7398640004fd739864002cfc739864005cfe7298640004fd729864002ef64198640096f54198640024fe7098640024fc7098640026f61098640026f41098640026f46158640004ff755864001cfe7558640004fd755864001cfc7558640004ff735864000cfe7358640
  | 25 => 0x521006bf6450521016bc6450521005ef725052105dec7250521167b44150521184fe768c521006bf648c5211aebc648c52100cff764c52115cfd764c52105cfc764c5210057f754c52116d7c754c521006bf644c52119ebc644c521006df634c52100edc634c521005ef724c52105dec724c52116d7e75885210057d7588521006bf648852117ebc648852105df6718852105ef7618852102f6e758852102f6d7588521007af6488521007ac648852102dee718852102eef618852105fe76188521005ed7088521006bf64d8121006bc64d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d812100cfe73d8121004fd73d812100cfc73d8121006fb50d8121006f850d8121006fb30d8121006f830d8121165be7498121005bd7498121006bf6498121006bc6498121006fb60981210057f755812116d7c7558121005bf7458121165bc7458121006bf6458121006bc6458121005df735812115ddc735812116d7e75181210057d7518121006bf6418121006bc6418121006f96018121024ff751812101cfe75181210267e751812101c7e7518121004fd75181210267d75181210047d7518121024fc7518121014fe7418121004fd7418121024fc741812100cfe7318121004fd7318121024fc7318121006ee2118121006fb5018121026f85018121006fb3018121026f83018121004ff755902101cfe7559021004fd755902101cfc755902102cff745902102ebf7459021146be5459021006bd5459021004ff735902100cfe735902100cfc735902105cfe725902105cfc725902105ebe425902105ebc425902102cfe715902102cfc715902102ebe415902102ebc4159021004ff7059021024fc7059021146bf4059021004ff7558c210067f7558c210047f7558c2101cfe7558c21004fd7558c2101cfc7558c210067c7558c2101c7c7558c21004ff7458c21014fe7458c21014fc7458c2102cff7358c2102edf7358c21006df5358c2113ede5358c21006dd5358c2113edc5358c21006df4358c2113ede4358c2113edc4358c2105cfe7258c2105cfc7258c2105ede3258c2105edc3258c2102cfe7158c2102cfc7158c2102ede3158c2102edc3158c21004ff7058c21024fc7058c2113edf3058c2113edc3058c21006df7558c210065f7558c21006de7558c21006dd7558c21006dc7558c210065c7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2105edf7258c2105ede7258c2105edd7258c2105edc7258c2105edf5258c2105ede5258c2105edd5258c2105edc5258c2105edf4258c2105ede4258c2105edd4258c2105edc4258c2113edf7158c2102ede7158c2102edc7158c21006df5158c2102ed
  | 26 => 0x6bf65d9121006be65d9121006bd65d9121006bc65d9121006be63d9121006bc63d912125fb721d912125fb421d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d9121006bf72d912125ebe72d9121006bd72d912125ebc72d9121006bf52d912125ebe52d9121006bd52d912125ebc52d9121006bf32d912125ebe32d912125ebc32d912125ebf71d9121166be71d9121006bd71d9121006bf51d9121006be51d9121006bd51d9121006bc51d9121006bf31d9121006bc31d912125ebf21d912125ebc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006bf30d9121006bc30d912125ebf20d912125ebc20d9121166bc6459121004ff755912101cfe7559121004fd755912101cfc7559121164ff7459121006bf7459121004ff735912100cfe735912100cfc735912117cff7259121006ef725912118cff7159121006f77159121004ff7059121024fc7059121005be7619121166be7619121004be76191211673e75191211673d7519121006bf6519121006be6519121006bd6519121006bc6519121006be6319121006bc63191212e6bf61191212e7b721191212e7b4211912100cfe76d8d21006bf64d8d21006bc64d8d2115ede63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21014fe74d8d21004fd74d8d21014fc74d8d21006df53d8d2115edc53d8d2115cfd72d8d2115edf32d8d2105cfd71d8d2115edf31d8d21024fe70d8d21004fd70d8d2115edc30d8d210057f7558d2116d7c7558d21005bf7458d21165bc7458d21006bf6458d21006bc6458d2115edc6358d21005fb7058d21005f87058d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21014fc7458d21006bc7458d21014bc7458d2115cff7358d21006df7358d21174ff7258d21006ef7258d21184ff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d21024fc7058d21006f87058d21004f87058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21016bc6450d21014fc7650921006bf6450921016bc6450921005f77150921005f4715092100cfc764c9210057f754c92116d7c754c921005bf744c921165bc744c921006bf644c9211debc644c921006df634c92100edc634c92105fcc324c921005f7714c921005f4714c92118cfe7690521006bf6490521016bc649052115dde7390521005dd7390521014ff7650521164fd765052105cfc765
  | 27 => 0xc755922102ebf7459221004ff735922100cfe735922100cfc7359221006be435922117ebc435922117ebf425922102cfc715922102ebe415922102ebc4159221004ff7059221024fc705922117ebf405922102cff75d8e2101cfe75d8e2102e7e75d8e2101c7e75d8e21004fd75d8e2102e7d75d8e210047d75d8e2102cfc75d8e21014fe74d8e2102ebe74d8e21014be74d8e21004fd74d8e2102ebd74d8e21004bd74d8e2102cfc74d8e21174fd73d8e2102eed72d8e2102ef671d8e2102edf31d8e21024fe70d8e21004fd70d8e21176dc30d8e2100cff7658e210067e6558e210067d6558e2102edc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21014fc7458e2102edf7358e21006df4358e21176dc4358e21176df3258e2102cfc7158e2102ede3158e2102edc3158e21004ff7058e21024fc7058e21176df3058e21004ff7650e2102cfe7650e21004fd7650e2102cfc7650e2121e7e6550e210067d6550e21005ef7250e2105dec7250e21014ff7650a2102cfc7650a212067e6550a210067d6550a21016be6450a21006bd6450a21005f77150a2102df47150a2100cff764ca2102cfc764ca210057f754ca211557c754ca211e67e654ca210067d654ca21005bf744ca2117dbc744ca2100ede634ca21006dd634ca21005f7714ca2102df4714ca21144ff76506211c67e65506210067d655062102fb4415062113cff764c6210057f754c6211557c754c6211a67e654c6210067d654c62102edf634c62102edc634c62102ded76c862105eed76c862105f6e75c862105f6d75c862102f6e65c862102f6d65c862102fe661c862102fe651c86212efe551c8621005ee70c86210067e65982210067d659822102efb6098221024ff759822101cfe7598221004fd7598221024fc7598221014fe7498221004fd7498221024fc749822100cfe7398221004fd7398221024fc739822102cfe719822102efb1098221026f810982210067e65582210067d6558221005df7358221175dc735822102ef86058221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff7358221006df7358221004df735822100cfe735822100cfc7358221006dc735822100cdc735822102cfc7158221006ef215822102efb105822102ef81058221014fe76d9121166be64d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121166be54d9121006bd54d9121166bc54d912100cfe73d9121004fd73d912100cfc73d9121166bf43d9121006be43d9121166bc43d9121164fd72d9121166bf42d912105cfd71d9121166bf41d9121024fe70d9121004fd70d9121166bf40d9121166bc40d9121165be76d9121014be76d9121
  | 28 => 0x8f21004ff7458f21014fe7458f21014fc7458f2105edf7358f21186de4358f2105cfc7258f2105ede3258f2105edc3258f21186df3158f21004ff7058f21024fc7058f21186dc3058f21004ff7650f2105cfe7650f21004fd7650f2105cfc7650f2121e7e6550f210067d6550f21016be6450f21006bd6450f2100ede6350f21006dd6350f21164fd76907211d67e65907210067d659072125ebf6490721016bc6490721185de7390721005dd7390721014ff765072105cfc76507211c67e65507210067d6550721016be6450721006bd6450721005ef725072105dec725072115cfd768c7211b67e658c7210067d658c72100cff764c72105cfc764c7210057f754c7211957c754c7211a67e654c7210067d654c72100ede634c721006dd634c721005ef724c72105dec724c721024ff759832101cfe7598321004fd7598321024fc7598321014fe7498321026be7498321014be7498321004fd7498321026bd7498321004bd7498321024fc749832100cfe7398321004fd7398321024fc739832105eec2198321026fa7098321026ef209832105efb2098321026f82098321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321014fc7458321004ff735832100cfe735832100cfc735832105efb705832105efb205832105ef8205832102d7f76596211567f765962101c7f765962102e7f64596210067e645962102e7c645962102e7f63596210067e635962102e7c63596212f777215962102f74215962102e7f605962102e7c60596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067c43596211567f72596212f67e72596210067d72596212f67c72596210067f42596212f67e42596212f67c42596210067f32596212f67e32596212f67c32596211567f715962102e7e71596211567d715962102e7c71596210067f415962102e7e415962102e7c41596210067f315962102e7e315962102e7c31596212f67f215962102e7e215962102e7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067c30596212f67f20596212f67c205962102e7f105962102e7c105962102cff75d922101cfe75d922102e7e75d922101c7e75d9221004fd75d922102e7d75d92210047d75d922102cfc75d922117cfd74d922100cfe73d922102ede73d922100cde73d9221004fd73d922102edd73d9221004dd73d922102cfc73d922102eed72d922125ebe42d922125ebc42d922102ef671d9221024fe70d9221004fd70d9221014ff76592210067e65592210067d655922102ebc6459221004ff755922101cfe7559221004fd755922101cf
  | 29 => 0x30f5c654c9310079f744c93119dde744c93119ddc744c9310079c744c93119d9c744c931006df644c931006dd644c93100ddf724c93100fcf724c931007cf624c93105ede624c93105edc624c931007cc624c931007d7714c93102ddc714c931007d4714c93100edf614c93100fd7614c931005df704c931304fe76905310067f65905311d67c6590531016be6490531006bd649053100dde739053119ddd739053119f9f4390531014ff765053100cfe76505311bcfd765053100cfc76505310067f65505311c67c6550531006bf6450531016bc6450531005df735053100ddc73505310075f658c5312ff5c658c53119dde748c53102ddc748c531005dd728c53102dde718c53102fd6718c53102edf618c53100fd7618c531005dd708c5310067f65d81310067c65d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131014fe74d8131004fd74d8131014fc74d813105cfe72d8131004fd72d8131006fb40d8131006f840d813108efa30d81311a57e75981310057d75981310067f65981310067c6598131006fb60981310057f75581311a57c75581310067f65581310067c6558131005bf745813119dbc7458131005ef7258131005ec72581310067f65181310067c651813119dbe7418131005bd7418131006f96018131024ff751813101cfe7518131004fd7518131024fc7518131014fe7418131026be7418131014be7418131004fd7418131026bd7418131004bd7418131024fc7418131006df4318131036dc431813105cfe7218131004fd7218131036df3218131006dd3218131006de3118131036dc3118131006fb4018131026f84018131026df3018131026fa3018131036f930181310067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067c435972105e7f725972105e7e725972105e7d725972105e7c725972105e7f425972105e7e425972105e7d425972105e7c425972105e7f325972105e7e325972105e7d325972105e7c32597211967f71597211967e71597210067d71597211967c71597210067f41597210067c41597210067f31597210067c315972105e7f215972105e7e215972105e7d215972105e7c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067c40597210067f30597210067c305972105e7f205972105e7e205972105e7d205972105e7c2059721004ff755932101cfe7559321004fd755932101cfc755932105ebf7459321004ff735932100cfe735932100cfc735932118ebf435932105cfc725932105ebe425932105ebc425932118ebf4159321004ff7059321024fc705932118ebc4059321004ff7558f2101cfe7558f21004fd7558f2101cfc755
  | 30 => 0xc43d953131f5f32d953131f7731d953131f5c31d953131f7431d953131f5f30d95310067f74d95310067e74d95310067d74d95310067c74d953131e7f73d953131e7e73d953131e7d73d953131e7c73d953131e7f43d953131e7e43d953131e7d43d953131e7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067c42d953131e7f32d953131e7e32d953131e7d32d953131e7c32d953131e7f71d95311a67e71d953131e7d71d953131e7c71d95310067f41d95310067c41d953131e7f31d953131e7e31d953131e7d31d953131e7c31d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067c40d953131e7f30d953131e7e30d953131e7d30d953131e7c30d9531014fe76d91310067f65d91310067c65d913119ebe64d913100dde73d913119f9f43d9131004ff75d913101cfe75d9131004fd75d913101cfc75d913102cff73d91311ccfd73d913119edd73d913119cdd73d91311cebf43d913119edf43d91311cebd43d91311cedc43d913105cfe72d9131004fd72d913119ebc42d91311cedf32d913100cfd71d913119ebf41d9131024fe70d9131004fd70d913119ebc40d91310057f75591311a57c75591310067f65591310067c655913119ebc6459131005ef7259131005ec7259131315f77159131005fb7059131005f87059131004ff75591310067f75591310047f755913101cfe7559131004fd755913101cfc75591310067c755913101c7c75591311ccff7459131006bf74591311bcff7359131006df735913119edf43591311bedc4359131004ff7259131006ef7259131004ef725913105cfc7259131006ec725913105cec72591311bedf3259131314ff7159131006f7715913119ebc4159131004ff7059131006fb7059131004fb7059131024fc7059131006f87059131004f8705913119ebf40591310067f65d89310067c65d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931014fe74d8931004fd74d8931014fc74d8931006ef42d8931006ec42d8931176ee32d8931176ed32d8931024fe70d8931004fd70d89311a57e75989310057d75989310067f65989310067c6598931006ef629893115df571989310057f75589311a57c75589310067f65589310067c6558931005bf745893119dbc7458931185f77158931005fb7058931005f870589310067f65189310067c651893105eee6218931006ed6218931004fe7690931004fd769093105cfc76909310067f65909312167c6590931006bf6490931016bc649093100dde7390931005dd739093120f9c4390931004ff7650931004fe7650931004fc76509310067f65509312067c6550931005df735093100ddc735093105cdc764c9310075f754c93130f5c754c9310075f654c931
  | 31 => 0x8941006ed52d894117eee42d894117eed42d8941006ef32d8941006ec32d8941024fe70d8941004fd70d89411c57e75989410057d7598941006ef6298941165f5719894118df771589411bdde7318941005dd731894105eee6218941006ed6218941004fe768c941004fd768c94105cfc768c941004ff764c941004fe764c941004fc764c9410057f754c9411c57c754c941005bf744c941015bc744c94100ede634c94102f9e739054102f9d7390541006bf639054125ebc629054102dbe719054102fb6719054102ebf6190541017b76190541005bd7090541004ff75d814101cfe75d8141004fd75d814101cfc75d814100cfe73d8141004fd73d814100cfc73d814105cfe72d8141004fd72d8141096fa40d8141006fb30d8141006f830d8141006fb60981410057f75581411c57c7558141005df73581411bddc7358141005ef7258141005ec7258141006f96018141024ff751814101cfe7518141004fd7518141024fc751814100cfe7318141004fd7318141024fc731814105cfe7218141004fd7218141006be411814103ebc4118141026bf4018141026fa401814103ef94018141006fb3018141026f8301814102cff75d923101cfe75d9231004fd75d923102cfc75d92311bcfd74d923102edd73d923105cfe72d9231004fd72d923102cfe71d923102ef671d9231024fe70d9231004fd70d9231014ff765923102ebc6459231004ff755923101cfe7559231004fd755923101cfc755923102ebf74592311aebe5459231006bd54592311bebf43592311bebd4359231004ff725923105cfc72592311aebc425923102cfe715923102cfc715923102ebe415923102ebc4159231004ff7059231024fc70592311aebf405923102eef6298a3102eec6298a3102eec6258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31014fc7458a3115eee3258a3115eed3258a3102cfc7158a3115edf3158a3102eee2158a3102eec2158a31004ff7058a31024fc7058a3115edc3058a3105cff7690a3102cfe7690a31004fd7690a31016be6490a31006bd6490a31004ff7650a31004fd7650a3102cfc7650a31314ff765063102efb6098231024ff759823101cfe7598231004fd7598231024fc7598231014fe7498231004fd7498231024fc749823105cfe7298231004fd729823102cfe7198231026fa309823107ef9309823102efb1098231026f8109823102ef86058231004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231014fc7458231004ff725823105cfc725823102cfc7158231066df3158231066fa3058231066dc305823102efb105823102ef810582313257e76d95311a67e76d953101c7e76d95310067e64d95310067c64d95310075f43d953131f5
  | 32 => 0x2ede2158e4102edc2158e41006df7058e41006de7058e41006dd7058e41006dc7058e41006df5058e41006de5058e41006dd5058e41006dc5058e4119edf4058e4119ede4058e4119edd4058e4119edc4058e4102edf1058e4102edc1058e411cdbf7650e4100ebf7650e4100cbf7650e41015bf7350e410179f7350e4100ebe6350e411cf9e6350e410079d6350e4100ebc6350e4125dbc7250e411cf9f3250e41005bf7150e41007b77150e41007b47150e41016be6150e41017b66150e41005bc7050e411d57e7598a410057d7598a41006de6398a41006dd6398a4102eef6298a4102eec6298a41006de6358a41006dd6358a4102eec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a4100cfe7358a4100cfc7358a41006ef5258a41006ec5258a41166ee4258a41166ed4258a4125ebc4258a4102cfc7158a4102eee2158a4102eec2158a41004ff7058a41024fc7058a41005bd7390a4120ebe6390a410079e6390a4120e9e6390a410079d6390a4120ebc6390a41015be7290a41017ae7290a4125fae6290a4125ebd6290a41007ad6290a4125fb67190a41005bd7190a4125fb57190a41016be6190a41017b66190a41005be7090a4105cff768ca4102cfe768ca41004fd768ca4125dbf748ca41015bc748ca4100ede638ca41006dd638ca41004ff764ca41004fd764ca4102cfc764ca410057f754ca411d57c754ca41005bf744ca41015bc744ca4100ede634ca41006dd634ca410079d434ca41006de6398241006dd639824102efb6098241024ff759824101cfe7598241004fd7598241024fc759824100cfe7398241004fd7398241024fc739824105cfe7298241004fd729824102cfe7198241026fa4098241086f9409824102efb1098241026f810982410057f75582411d57c7558241006de6358241006dd635824102ef86058241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c7558241004ff735824100cfe735824100cfc735824106ebf4358241006bd4358241004ff725824105cfc7258241006be425824106ebc425824102cfc715824106ebf415824106efa405824106ebc405824102efb105824102ef8105824100cfe76d8d411bede63d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d411bede43d8d411aedd43d8d4105cfe72d8d41004fd72d8d41014fd71d8d411aebc41d8d411bedf31d8d41024fe70d8d41004fd70d8d411aebf40d8d411bedc30d8d410057f7558d411c57c7558d411bedc6358d41005ef7258d41005ec7258d4132df77158d41005fb7058d41005f87058d41004ff75d894101cfe75d8941004fd75d894101cfc75d894100cfe73d8941004fd73d894100cfc73d8941006ee52d
  | 33 => 0x5611853202cff751853201cfe7518532004fd751853202cfc7518532014fe7418532004fd741853202cfc741853205cfd731853202edf311853202ef6311853213ef53118532024fe7018532004fd701853213edc30185320067f65d81320067c65d8132006bf64d8132006bc64d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132014fe74d8132004fd74d8132014fc74d813205cfd73d813202cfe71d8132004fd71d81320e6df31d81320e6fa30d81320e6dc30d81321e57e75981320057d75981320067f65981320067c65981321ddbe7498132005bd7498132006bf6498132006bc6498132006fb60981320057f75581321e57c75581320067f65581320067c6558132005bf74581321ddbc7458132006bf6458132006bc6458132005f77158132005f471581320067f65181320067c6518132006bf6418132006bc6418132006f96018132024ff751813201cfe7518132004fd7518132024fc7518132014fe7418132004fd7418132024fc741813205cfd731813202cfe7118132004fd7118132026fa301813209ef9301813202edf6598e41006de6598e41006dd6598e4102edc6598e411cf9e7498e411cf9d7498e411bedd6498e4102edf6298e4102edc6298e4132f9c4298e4102ede6198e4102f9f4198e4132fd74198e4102fd44198e4102edf6098e4102edc6098e4132f9c4098e4100cff7658e410057f7558e411d57c7558e4102edc6358e41004ff7558e410067f7558e410047f7558e4101cfe7558e41004fd7558e4101cfc7558e410067c7558e4101c7c7558e41006df5358e411cede5358e41006dd5358e411cedc5358e411cede4358e4119edd4358e41004ff7258e4105cfc7258e411cedf3258e411cedc3258e4102cfe7158e4102cfc7158e4102ede3158e4102edc3158e41004ff7058e41024fc7058e411cedf3058e411cedc3058e4102ddf7658e411cedf7658e4100cdf7658e410075f7558e410075c7558e4102edf6558e41006de6558e41006dd6558e4102edc6558e4119f9e7458e410079d7458e4102edf6258e4102edc6258e4119f9c4258e4102f9f4158e4119fd74158e4102fd44158e4102edf6058e4102edc6058e4119f9c4058e41006df7558e410065f7558e41006de7558e41006dd7558e41006dc7558e410065c7558e4119ede7458e4119edd7458e411cedc7458e4119edf5458e4119ede5458e4119edd5458e4119edc5458e41006df7258e41006de7258e41006dd7258e41006dc7258e41006df5258e41006de5258e41006dd5258e41006dc5258e4119edf4258e4119ede4258e4119edd4258e4119edc4258e411cedf7158e4102ede7158e4102edc7158e41006df5158e4102ede5158e41006dd5158e4102edc5158e4119edf4158e4102ede4158e4119edd4158e4102edc4158e41
  | 34 => 0x913220fac32d913220f9f31d913220f9c30d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132356bf73d913220ebe73d913220ebd73d913220ebc73d913220ebf53d913220ebe53d913220ebd53d913220ebc53d913220ebf72d9132356be72d913220ebd72d9132356bc72d9132006bf52d9132356be52d9132006bd52d9132356bc52d913220ebf32d9132356be32d9132356bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d913220ebf31d913220ebe31d913220ebd31d913220ebc31d9132356bf21d9132356bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d913220ebf30d913220ebe30d913220ebd30d913220ebc30d9132356bf20d9132356bc20d91320057f75591321e57c75591320067f65591320067c65591321debc645913234def7259132004ff75591320067f75591320047f755913201cfe7559132004fd755913201cfc75591320067c755913201c7c755913220cff7459132006bf74591321fcff7359132006df735913234cff7259132006ef7259132004ff715913202cfc7159132004ff7059132024fc705913220dbe76191321debe761913220cbe7619132006bf65191320073f65191320063f6519132006be6519132006bd6519132006bc65191320073c65191320063c651913233f9e73191321df9d7319132346bf631913233ebf621913233faf32191323479e32191323479c321913233fac321913233f9f311913233f9c301913205ddc7650d32016dc7650d3205cdc7650d320075f6550d323375c6550d3200ddf7450d3200f9f7450d320079f6450d32016de6450d32016dc6450d321df9c6450d320169c6450d32007cf7250d3205dde7250d3205ddc7250d32007cc7250d3205dcc7250d3200edf6250d3200fcf6250d32005df7150d321df9c4150d32005dc7050d321df9f4050d32014ff765093200cfe76509321fcfd765093200cfc76509320067f65509322067c6550932006bf6450932016bc6450932005df735093200ddc73509320067f65d85320067c65d8532006bf64d8532006bc64d8532004ff75d853201cfe75d8532004fd75d853201cfc75d8532014fe74d8532004fd74d8532014fc74d853205cfd73d8532186f631d8532024fe70d8532004fd70d85321e57e75985320057d75985320067f65985320067c65985321ddbe7498532005bd7498532006bf6498532006bc6498532006f761985320057f75585321e57c75585320067f65585320067c6558532005bf74585321ddbc7458532006bf6458532006bc6458532005fb7058532005f870585320067f65185320067c6518532006bf6418532006bc6418532006f
  | 35 => 0x1cfe7598632004fd759863202cfc7598632014fe7498632004fd749863202cfc749863205cfe729863202cfc729863202ef6719863202ef63198632176f5319863205ef7219863202ef42198632024fe7098632004fd7098632004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632006bf7458632004bf7458632014fe7458632014fc7458632006bc7458632014bc745863205cfc725863205edf325863205edd325863205ef7715863215ef6315863205ef7215863205ef42158632004ff7058632024fc7058632024ff759823201cfe7598232004fd7598232024fc7598232014fe7498232026be7498232014be7498232004fd7498232026bd7498232004bd7498232024fc749823205cfe7298232024fc729823205edf329823205edd329823202cfe7198232004fd7198232026fa7098232026fa30982320d6f9309823205efb2098232026f82098232004ff755823201cfe7558232004fd755823201cfc7558232004ff7458232014fe7458232014fc745823205cfc7258232004ff715823202cfc715823205efb70582320befa305823205efb205823205ef8205823236d7e76d95321e67e76d953201c7e76d95320067e64d95320067c64d95323675e43d95323676f32d953235f5e32d953235f5c32d95323676c32d95323675f31d95323675c30d95320067f74d95320067e74d95320067d74d95320067c74d953235e7f73d95323667e73d95323667d73d95323667c73d95323667f43d95323667e43d95323667d43d95323667c43d95323667f72d953235e7e72d95323667d72d953235e7c72d95320067f42d953235e7e42d953235e7c42d95323667f32d953235e7e32d95323667d32d953235e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067c41d95323667f31d95323667e31d95323667d31d95323667c31d953235e7f21d953235e7c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067c40d95323667f30d95323667e30d95323667d30d95323667c30d953235e7f20d953235e7c20d9532014fe76d91320067f65d91320067c65d91321debe64d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132006bf54d91321debe54d9132006bd54d91321debc54d913205cff73d913205cfd73d913220ebf43d913220ebd43d913200cfd72d91321debf42d913202cfe71d9132004fd71d91321debf41d91321debc41d9132024fe70d9132004fd70d91321debf40d91321debc40d913233dbe76d9132014be76d9132006bf65d91320073f65d91320063f65d9132006be65d9132006bd65d9132006bc65d91320073c65d91320063c65d91323579f73d913220f9c73d913220faf32d91323579e32d91323579c32d
  | 36 => 0xd759864202cfc759864200cfe7398642004fd739864202cfc739864205cfe729864202cfc729864202ef6719864202ef6419864217ef5419864205ef7219864202ef42198642024fe7098642004fd7098642004ff755864201cfe7558642004fd755864201cfc7558642004ff735864200cfe735864200cfc735864205cfc725864205ef77158642166f64158642166bc415864205ef7215864205ef42158642004ff7058642024fc7058642166bf4058642024ff759824201cfe7598242004fd7598242024fc759824200cfe7398242004fd7398242024fc739824205cfe7298242024fc729824202cfe7198242004fd71982420debc4198242026fa7098242026bf4098242026fa40982420def9409824205efb2098242026f82098242004ff75582420067f75582420047f755824201cfe7558242004fd755824201cfc75582420067c755824201c7c7558242004ff735824200cfe735824200cfc735824205cfc7258242004ff715824202cfc715824205efb70582420c6fa405824205efb205824205ef8205824200cfe76d8d421fede63d8d42004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d4205cfd74d8d42006df53d8d421fedc53d8d421fede43d8d421eedd43d8d42014fd72d8d421fedf32d8d4202cfe71d8d42004fd71d8d421fedf31d8d42024fe70d8d42004fd70d8d421fedc30d8d420057f7558d422057c7558d421fedc6358d42375ef7258d42004ff75d854201cfe75d8542004fd75d854201cfc75d854205cfd74d854200cfe73d8542004fd73d854200cfc73d854218ef641d8542024fe70d8542004fd70d85422057e75985420057d75985421fdde7398542005dd7398542006f76198542006f5611854202cff751854201cfe7518542004fd751854202cfc751854205cfd741854200cfe7318542004fd731854202cfc73185422e6be42185422e6bc421854202ef64118542146f54118542024fe7018542004fd7018542004ff75d814201cfe75d8142004fd75d814201cfc75d814205cfd74d814200cfe73d8142004fd73d814200cfc73d814229ebe42d814229ebc42d814202cfe71d8142004fd71d81420eefa40d8142006fb60981420057f75581422057c7558142005df73581421fddc7358142005f77158142005f47158142006f96018142024ff751814201cfe7518142004fd7518142024fc751814205cfd741814200cfe7318142004fd7318142024fc731814202cfe7118142004fd7118142026fa40181420a6f94018142004ff755923201cfe7559232004fd755923201cfc755923205ebf74592321febf43592321febd435923205cfe725923205cfc725923205ebe425923205ebc425923205edf325923205edd3259232004ff715923202cfc7159232004ff7059232024fc705923202cff7598632
  | 37 => 0x6005003805000000100300000040000000000000000006005001000c00e8000040000000800800e00400000400300000018000008002005804400200b00000100060220008018000001007003c0160010010194006021005003c00a00700000c000002b0088000000014000000c000006003008c03c01d00080200020000010000000014001003000000d001801400202500000100000000038000032001000001c006003002804400200400f8098004000003800001c00b00d0064002013000000006e0000028034014000000000000000400d8014000009002804800200400c8114048000000001800200605cfe76d8943004ff75d894301cfe75d8943004fd75d894301cfc75d894300cfd74d8943014fd73d8943006ef52d8943006ec52d8943376ee42d894334eee32d894302cfe71d8943004fd71d8943024fe70d8943004fd70d8943356bf6498943006ef62989430057f755894321d7c7558943356bf641894305eee6218943006ed6218943004ff75d854301cfe75d8543004fd75d854301cfc75d854300cfd74d8543316bd74d8543014fd73d854332edf43d8543316dc43d854305cfe72d8543004fd72d8543316df32d854332ef641d854332ebc41d8543316f631d8543024fe70d8543004fd70d854332ebf40d8543006f761985430057f755854321d7c7558543005ef7258543005ec7258543005fb7058543005f87058543006f5611854302cff751854301cfe7518543004fd751854302cfc751854300cfd7418543014fd731854305cfe7218543004fd721854302ef6411854337ef5411854302ef63118543306f53118543024fe7018543004fd7018543004ff75d814301cfe75d8143004fd75d814301cfc75d814300cfd74d8143014fd73d814305cfe72d8143004fd72d814302cfe71d8143004fd71d81432defa40d81432b6fa30d814321d7e75981430057d7598143005ee7298143005ed7298143006fb6098143006f96018143024ff751814301cfe7518143004fd7518143024fc751814300cfd7418143026bd7418143014fd73181432d6df43181432a6dc431814305cfe7218143004fd72181432a6df321814302cfe7118143004fd71181432d6bc4118143026bf4018143026fa40181432d6f94018143026fa30181432a6f93018143004ff7558e420067f7558e420047f7558e4201cfe7558e42004fd7558e4201cfc7558e420067c7558e4201c7c7558e4205edf7358e4220ebe4358e4220ede4358e421dedd4358e4220ebc4358e4205cfe7258e4205cfc7258e4205ede3258e4205edc3258e42004ff7158e4202cfc7158e421debc4158e4220edf3158e42004ff7058e42024fc7058e421debf4058e4220edc3058e4202cff759864201cfe759864202e7e759864201c7e7598642004fd759864202e7d75986420047
  | 38 => 0x8000002000000800406e0040010004034010002002000000c0098024002000000002402c03b0010004000027000807400e003001803400e0000008004010018001001801e002000000002600300b000404a023001800400c000012800401600500d0000018013003002c02a00702780400000000048008026003009004401c00a000800401e002005000800c011000001800000200c003000c000010802c00c0070250004010020009001000a000000000c000002000800001c00d00b015400200100b8014000011002000c000036000004c002000000804000600000080180020000000004034000010801000800400d00080140060000050000006000002000400e0010000004001000000800c000001000000a007006800801e004000000000200000300840080100000020020089003000000400103680000020010000010004006001800c03c004004800000c0180000050000007002800801401000080340040120028038002002004000000000100101900000060080018006001003000000000700581cc00e0080008008006015003807010a02200b001001200000280040000010018014000000000804000c01b0028080002011001003402a00000b801400c05d0038020000000002000807c00e0148000016002002002401800300000380040140000004004002001802c034001001000c066046000001806000400000000000000010008000001003001c0fc0050008014002000003800c0280000010000000001000800c002003006806407a001001000000800a00c805800200000e801c000000000801801c0000018008020006000800c010000003001000e005003802000600202a000004a0140048000002003002800000a0090048000002007001008800800000580000b2004007000c01001a0058044000001002002000001f004801c032059004803405e01f001803800000700480000040090150008000000003000800800c0040024000000001003c00000000080000280000000000018000000000000200a00480080000040018004014002002002000e001001000c02c006000005c00a00e014800001800a008009000001a00700240060040090008008005008000c00600e000801000403a00080840180230008064004034013800000200000e000803601000080100000020048000018047004801800000100080b4022001001001000a0050018008000011002000002000700200040340040030000016000000002c00001700c8048008004001803c002000002801000200000c000403a0020018050004000005006400600000e80040140010098004000003010001400c00000080140000030078058006070000802c04c00d00280000020060018008000000002001c06a01800f003000c0050000010002008000000400
  | 39 => 0x7e0070008000002000001002802800000180080060020000008034001001000003e0020080008004003002001400c01e003003007200a0068020000010000001000200b000002c00001301580c00000190078014016000002001000201e00d000402e006019800400800600d806800200c0010028000005004003800a001001001000000900282ac006001008000c00a013002809c00000000080280a201200000300260000010080046001000003c01600a0078000000010005003c000000002800000000100a8000008008003800400e00001b807800a0030008000000000003000808e00f001803000400b0038034024004003800c00000f002000c008019000000000400500b008400001c00280a40000120018014006038008800c036007000000000e045002000000200500000000c80070000000002013003800400400d000001000401a004804c02601e000001001800f0040004000002001002c020000000003400000501c0010000006008800000c00800000e800e002001001c01000700000240000000070008000002002800803e002000801800a0000020014028003000800001c00000281180060260068010000012002003c0040020038014010023001001000e00200000340080000038018060000000804c00e000013800400000200680000260000000034020001018001402000d000000c02a00a0078018000002022800001a000000000c000005000000800600100b8040000030009000000200c003000400800000380000100020070024030004000800c0020040008000006003003000801400d01700a80000000018074038000001006406800f002001000a0020028078062003001802c006000003808000e04f00f802801c00000000000180050028034008008002007000c001005802801c00100280000d802600000300160000050000000000002000401a0010000030044000001001c03000d0000034002000000801003800b005000400a0010098028008002010800001c007008000800200100680240040180000000020002005800800a001009001800002600201a800400d0018054010004000007c0120010000084000002000804004400100800180ac002002000000200102f810000000f0020000004008001000801c01900c800001a01400b000400000900080a00020000040000000001000808800a0080420020000012000000001a00200000080060010008000008003002000000e000001000801e01d012000001000f000004400e013007000800000a00000040000000010074002000002801c02000b01c802c00600b0038000014045000000000600000f805c02c00a0028004038008001000400600300400040020210008028028001001806401c02a002800c02800000e8000006011000000400600200
  | 40 => 0xc0000000002003001001606b0010018000006000001c014020000000802601f0030000018000007002800600001b000400e009000000c02c00c009000c00c001001000000c006003800404a01d0058008002009000000001400000000240160160028008006000003801801e01e0090004000001004800000c037001804c0000140528004000003002006c00200000600000260870008000004000013000002e002001808000200b006000000403600f80d803000e000802c0040060000000010003000003c00800401d804001000b003800802c00000000840140010010000004000002002800c0030000004000000001001c00200100180000020270060004000000000800c00a008001800800000000080000060100000200000010003000000a000001802c014001000002402a000003000800000a0010008004002001001001000500280000280020000008030003006000001e000008800000200c001800000000a000000800800b000802800400d005800c002008002001c00201c00000000060080018000008029001001400000902f800c03a00201a000401600200c00000000000010008000003005007400800100000240000160000058006027000001802e00d002003400c00900180180000000048018036000000806800e000001812404800000c801c03800801480d805a02b006805c000003008800801a00c00500000360020008008000007002800002c000003000001000c008810c01000f00d0054000000001000801c005005000801000d00480f40340040000008002009006800c01000a000803c0580070090018010001007800003601f0000000006017001009c00000101680d40000080000018000007000003400200e000800800e002001000c00200a00680100660020090018036000005008c01801c003000000601e004000003e00300700a400a023012000000400900000a000200000c000409c0000010000008002008801804c00200b806000c004000000000403000f0010002022017803801c00600c003000000100d800c000006000000001402500e800001600900280000060090008004004000003802c01400701f805c02a01201b80b000a003000800000400100a801c000009001007c000000000803c0b20040018000000011009827800a0000000000006001000000c00a00701900180040000010020064003004800000200a01580080020000048008000000000000000000c000001803200000a00080280080000000032008006801c0020060040004002034003000c0020020048000000002002002c0000050038010000004000000c00001b004002c00800a000000001e00500e80280020070000014000015004805000000700d800007600300000140660000008000014012000001802a00201600000
  | 41 => 0xc98e8c5342096aba800091d2c721101732594027828db18c9c0a82aa5b2576c7c827a350a4ae29bb1264c594142fd2b4ebe5982062b00000001e0e165ae080002d72000132c0000afa5469800ac08d9ca1d000a000302014530de1dc0b6e779053e771ade6a7080005389aa25f023b278b2eac000000043988783b9989498ca2029ecabd6aae9c6e02100006728384ad7ae4499330cc861233400000001da945631b93ec97b9e6057508506952e4a27b87ae55b27560003180c3c27763d6000040900006a1a0f68559ddc5c5323059cb0d29d51f76c44974c245a8d800024586580a0e00885163cd32326862f086e10000000000000028bc7280000bb6aba0b0085feb879e8038680000002cbcb962f76175b25426a8066c7b8000aa11cae61fa598a001570142b06c19880008fcae9a000063e42980006749afac8aa53ea7a19b60002f067ab0db21fe907207e2b608701f7e7ad0ff294a07e241f27620000ca81041bbc0810000000276e84116040000000000043a00000000002b0c0000000bb8255e000019405e0000b61b046000000000000001df800010da6febb42d942fa8b6cc3a00007a424dca00a3b695300001c41a6602300002ed2212b70900000002644329ae66fc1eba178800057100006248000b5e936c7b89a300001cc83798f2031b12082bb000037c23f48100000000192234c8000342007012b80ae4b4800000020ae6550000c5f8000c25800000007ca59e1286000221486331849b180001bc1a50062223663daa7c2f0072a25d1256af3208e169012438d2f645b694380269c0600028d600000008921ed079e28727af160a23da9804e1834c47f8a78bff0000748a1de21f152200000000000802b38210a0002166000102e9089368000225c0002564000185c74d88d000013b4b6200000001d5800022161ad80006f9088aa0f00be38419e000022fe6db2990a9195e08728b20000805e1e69b863e0235abf330b0838ac3e667953082c0b367f727588341006ba2a04400014f4031202685a014c7b78ff895ba97a4a42c38203140c5618a826bc26c283d0da66909cba0f81200bacae8c92620465a3941cc3b0fca7e2ab080860f609e52c82924075a8008c462288abe97819087369e7cbfcaa6c4de895e8ff0eea0c8a08c2d69dfabb304bc6d38b3200300080580030028000002013003809c0020000000000000001000800002000b000000000800d001004400a0010070004000001000000400a0040018010004018001803000a00801b008c00000500000180600080000000028000000800000000b007800c00000700a002800e00f001001c00c00a0000014002004003000c000016003803400800f009802c084011000802400607c00000180040030020000000008001003401800100e800000600000c000002a0030
  | 42 => 0x8b16966dd0000106972a511276c0000c0e4d100004131e6c9cea9ce1be09da5911302c7e08cc96f8b4a87e00640c8103611fa59a6210f2207615361910976af631f4c019ee4491aede00000000f12dd800004dc00003b22851e6ea7103c22d71b585768b4296ea3aa68a983886198c2816273c0c4a172000233a0000dd09fb1640000298600020804901e86000135202415945cd8e8ec848000384800000000004cd325000e800000021f00001fa00000bfc76e0be449cb1409038bcc80a00007ef29726278000025a1822721038b90000000008aabb92d1e41526b87121c6a9f6a4e434302905638840a1ba9a83d680d043086a21aba97862b9a4c1f18000000000000021a800007a0b4c9e44870a2b828e01f69921e9ab7f1090c67b0b638b26f45de24a6b2984da2210a748daa1420bf2b7ab250c48c170fbc9cf805008d18d63438534000073c9548000000316200014629ebaca2614000000003489f7a47c3ac00002fb9db4ac8117481b800000000623cc1c28b21ab0a86f800049a800000026563461ca28458000c4185d0959800008c8bd6c79a16c4b5ae0e25598b24ba83e28929c76c4231e28bc9d82000165eb64800000014c274bafac2e616c60000ce000021dc0d804ca292260c14492d84a5089cc2a800077880005cf06680001b3a00024546e423502fe00000001f1651a00006d100000000000000000010d000000008c67fca5e2b5c1c5075e9d60c01112c5e5a9960b48706000000029500000002bf8c190000aa880000001c7a4819bcc9048f5000009ae0000000bb500000000fc608c30144dd1aacae38a522ed9f304842bc8000252625482d06a6b0287c3a1fa8e3b0f2a3d1c4a63f8ce26e384de3cd84be83b97d86cd00008cc30c69fb820ab15a6c0b9e1af2aab00004b130fcae7000000024086ac0000000286abe723b43fa98f80001d424bda29248eaaf47230000078000051a906e1ea000070e80000000000000078481817ca1e88482b94ac3670701228f0062ac0627e88301524030b1faa292c1c41f9eb612593a621508123718bc237b147e91c8f2408e11f468514f694023e6a77150eb5593da4b82a489718a02795a6a6b2706dab75923837891d23e8a62e1a4267478a91a4a400e2e9ac00147a32f6873d09be16e2cea09728c63bda90c3e58c9a1fd0fe2056046c233a8603dca4f018915b415db214052a2ccb5922a0a82975c07c8776588243e7a8253ab7a062812991d05a40c62314b1d6a671d1c887903e1310c5a49e0c2a1551f68a75272ab6d222079da3ee2a5121e353a34e44b94dcc3f89c2bbc075e5c1910a97229be2c32a1ab81204e89e00d8549836865a87d04ea0e38b3e00001b7a94e706985ec1307c04c9969e58319bab1f8cbe0001a98a608406445190c9222be4bce0ca28f32f4223cadf45b08
  | 43 => 0x2e2c9d39ea61bc8dea6bd8a4631c000000000006c18206c7399ce000000000008eaa50800012c8548988966e8952f16213ac188422bd2c0988a62ef2d144920a8a65ca1a06fa8000376b18810229a62538000c511cd871812048938942000078e6168fce1b61608a1a2b7e0001ba818baca00dc00005a4a786956092e34b969459680004928000bf906ec79fab908b9ae4e348a4d2000000055080005cd2da00470c3ebe300003c029de00000000000ec8526293402509a800009e200029bc0000d6800030568860000886a9d07660a5800023ca51d8b14b8a83b000000000000000000000088929586fd80000002442c36936e8ab08e6ad900003f430b257220a68f2310e647ae2eb2416f867912ae118154aa54a28eb06845808eacf06da9da44a30d740b7a4700cb319046b0c904589f145552bbc7e118268dc931405231ac76203d6b510a6a3429fa2c45896cc7490fe6ad161a3482e3eb9ba1b214a9eeab4410b40aa0ce45802b285e115be2eeab1e1979b762ae25d44531e1e7bd029c9fe23521c920fa70b13203640f04b2b9f9a82f1a0861f08221a29d18b6b04e6ac914e63ce0dcc99ca28243217164938e800dca77c68e8dca7c6a13e3d98c8252f0e980932ac45632ae4297b0720608cee365a780180130886b268025501fe1f4a0de34e266e8b82626af714a27f12f4a901958245d942c3c495a29a42a6e4379936000219a0222cda56b961016310b6420a7f6c3a827497930a6bcd839e44e8000b2c981ab342a2e0000cae4fa85dc0001a4e9cd8a2626304040d9258037fa49c2b69ed44368340b630b948e911de2e90d005f501a264b07d4389a39e80899d80e207983d11424ae1a8ec7a11c56c2280005f79a5a6a30000c81a63c0000000931aed25a08000559a19c7ca8000640a1ec103055e2e119ea61e8ca0a998c180000000a198a2e00000000000cc20001d5c00014c83d8894c2a00edc0000fbe0fa10525d61804ac40fa884625cca8700002b2933a1d9a02e0000000c221bb475d906057c000046183c08ae8000900800083e26aa2a906a833025d6000152e5f931be8e0abf2422099a48f00005521ac46040dce6aa9d683b380769f00b808c78b5e97711beb40b1f0000217093e928eb4fa8a6004072c0000d580000d06383a6660822dda0e885783ca08720000f2600022944daa8ae113101e3e526fa4a720a2bad256a8f7826e81aa378be8953800684fc4d0b0785c8842c44a13aa258a09e0dea28c14e0a5a61e18080001a7a94284a465c000012e0f5c096800097b0c0a0002f824a78d103d483d049f8b8aab5088e356abbe77a05220000cc8368a83200024f216d9178760082cc880f164e3a6425171ed89670000000000085e800000007dc3dd8000c57000000000000002512000000079a00001d1800000027a29110000
  | 44 => 0x489d80000001366c1d201abd8a79e2d49f0a2ab26ae112ac008358b3a6538438c7a0ee8665aea8c8726c8aa4aaa66d08ef0bc090d60000000506948e00000007f99c549818000300101403faec083f9fc249680006052e680001f02000000023495fe2b883e427d0c921df00007afb08e326172c00024cc49b1ce0713974a3950f8224321e018887c461a1fd809d80000000000000295ec54896467c9ea21b08e8a54f27c457631d438f96d4649909cc4b8000bbb97429609b4a5248d2498802200a230805a02e38c801f7a6bd0000c30866c00020340001f4c34d80006602ff80000a726682b3e9ee00008b714ac9512264000287e45ca7f00000000a951182864a954000000000029362b22a5ebf02ea60d289e4847aee6972a270345a2982aaa57876786589d0192827a9592bc8290a273058eb3c8dbc04a89309168f8a5b11e5c0a32f1053b1adcb1ba056952ac6a606063259f9092844097884e9d38645a22c16515cc8c40b463d797be2f400006b1908e362800030980008c8b10000015e87108948b65a7140fe94f881fb14e15c1b12af42c8c516a9500000000b61024674500000000550000290e0ee8634a5d1fce2df11c0306b17a07695fa20299948c0800000016c098400007e3886c52bb23eae90584714800064703920002a8023f0000000276857018801952bb800000007ba2e760002196155ad50265adbe1c286d200000009e3000026db1fc0000c6a95f8ab4755ab04a52a6ecc58024a000000000009f069e2be600030080fc23168c397689939c0e00011e615d06607130fe65ff800063c31da98f98cc28c966aa48324e62083620001f7c80b0848a4f2be0be799765c4b06e1e088c2a473196bd5818047daa740000000206109494b2f289029b7c0ce1ac89b81bb6bfd01ae7e1a54e00005005cc31ec8c01fb291028b6c281c3c0001c90c3d269cbd3833e20a004472d0000aad13a00adaef2aa20000b2e1a4426784160001bd000006dc0002b1c0001c188eea68e00000007ff80006b8838270c16b80000a9861d80007c42f70b1280006b4000000009fcc8980001e980003dfa8845f712ec00001d600013d83b6190eaa3934c403066a79400005da8000000285699c0000c6a03086aea8b4939ad18a6c29e00001e047cf0eaa0002b9400001c6aa080002692434a371f50c55a4e072497746f8947a70104128519b72061a946afd900820d801899f1a0c33d20082ac284a22d8590211119a0f9ac4e8011904535815e1a70a301fca46a986a01e688aeea20ba2c813918a25ed043e7e0a9986491dcc856a3d667b27282fc26083468396b9a88104d58f8873119de2dc143491812027fd9f5273a96a2b700736a33842a32e9ba2653114833a121a3cf8d702c1a9649d40ad2835026807916d85f322f800008ba34b2354baa875c000
  | 45 => 0x1bba0000000000305a9a18c22be9ad4c435180c46584a25f9a5b42a6a1944cd9b9e05e9ade0f39f80a2398e2349a718c6c02a25668000a3d91fc3511dac50a9d665a6916097e914e5ad09b86cc173e4442522a58020c32180000000000a8e099c9d82726b4d853a3981754aceaefe8a71b20b04061a0001fe4b1417a6117177a8739e161c00f701e311b67e498540000a7a000224c26232041b300000001b407031dd4000000000030020002fee0a9000000000000002a1e0002fe80bb130c2bf13c479484521b58efe3ae0faab5e0a1cc1485fc585a46895b2d82c2a17a4220877209c860abd5130e3d2ae463b422c60b21fca00020da013b0e0194a1806609c86c5288da0000000000000000b1e9600026500002b5a00027461d12cc2a5a0474021a10c6d6ae1431e19340002ae0000199814200000000e9692e8000517974003b2e664d01fe87dab10c387800000002d8a2a95acb468d8e0000ec496880005f485584df0000c00000000022da00008380001504a66800069b00002d22342312986a732889a77a80008470fd221805ecc4c9f6c9ec0000c188000000000000013e2bae1b48000000057d8000260243252e00000002d403d38000161a6120000000909000099d99e600000005b3800000015840000e360000b163ad9ab639c31288a680001f91c0a4998be25fb164842e2d006f480000002450000234a8ef10fc692146038f116c72c0a1a6c526343fd2a1600011c200028707491dde2ba024464280000001a68b3eaf3060a80003d50000000128a7ea2662acc085c8b10a2496427fe9ea82ea9cd18ec41a041c91e13f042002bec8395de0a696b21671ad2477039463b94aa49091f21fb1bde4d50c7625e84e2b01172424791346c10298986153a72516f00cc922aa80132239eaa8c55a8d886298b3800024a03c221881ef8bb000000000eb9a4aab9915c18c1c9e0002e8000000000001d049ad80000d5a8da69da2102d52d5e4dc80000000000c2e8ea40002fe296b00000001f880000000afb2cb43ab8226554178e6e50b9e7dc141e17c0112b7429306322d6c36c16fc30592527b9800085d18b00ce999272205e61b99e1c24981a48eb2cee00000005eb0000b4f0d5e4492e6475c800004600007dc9632871b0420000e900002abea7b86a6223090200024bc01800005e280009291ffa9c92bb6b2600008f3a04837e18e04dda696a02a9a404f91ecb73a2de00001ec78e324ac17a04200023d200012284210b920002d7c5e427c241b2aa449d1c683f5241ab560e584098000ac38dfa68dab5c89996b693680dc45f090085794ca0002256898830405100000002b34bf622720cf2b52bbe0d1c20ea50e00000000000be071988a400026b47fa8da09c801f0c7223a6a610cb46f800005278000000163cb77ad48a178a0c1c69ce
  | 46 => 0xbf700000003182a1900002f718a0a810000b8904284420000c048000a8a80000001ba48b280000000cbc00018c600016a0c4112c23090000c1c0ffc531800090e29f052e9250c2308209efa006b9580002cf000000000003bc9caa0000000000181c7e31d748c49c1013a91ee97c00009c701624f29d9c58d010803020825fd8e200000000351836e38a0c946bb83ea5339c34189aa9025687e0739a6f20a12eca94c0608b982b760000000c0d800000000008a8877a13c984e0002a9c5591bb8000281c000189600020c4ade25c4c520dd88a11860b931e3a50a30bc55f0df4a78aefc5878946c1f821400003028b49e4827716bc39d15fc8c2aa7a0001a7e4a91fec000029e0000dd20002cca42895727aa1bc64d6265ab01ab1689ea51ca62166200000000000f1c4a480000ea8b863591f002c028822c92a326eb839c696003694816e09a91ec880c05a889f80000001e5400008dc1a201300001efe35e8000a31000094d25e851288420c507cc92297609cc000023880d6b8608c462e8fd8981000017a80008030b0e1a91e74000000084525fc8ce2b2600000000000000711000047180000000166c948a340d680002ee0000c84000013a0cd800017d665b9d0c0002704c6980008c200000e687521cf80000000000448800000029cc00000003968000000005840a8cca97404d0000324c0001b6836e0bda20221006b080000000eee222000022b274aab18000a2ea9fc48517aa0002e92a39082600000000000000b8c19d66a820a8bc880009a69edc7d12c3a8e1a9247b38e16b3f130a0000a4cb2594cc3f716e836b1d484400000a68000089f210e1839ad6b2e892a89186489d71a2ea5f15b267410f60410eb262faad25b98b8c0fe222a2bc0c545ce07645f18a4e19291ca2281d12bbe8b82adba2f071d25b69ff05c02ada4ac2119ed23f304ec583999a3ed807451e01a64eea5f6bfc055a3550ae6acb2a9a81b03f60c71b0e60fa9262d019ee01491382a705e4be4a1641c701b43349a521e9000046c8b1c00015ca0000000000233e0001d906fe1c140000000b7fa1aa87d047a6e98fb09458940b9c99c8000000065583545fa877800006bc21d9f94000195e0b8000005baec604594d487ca4623da198e74c819218127e4a80a76ac0b19f40d412aa9879b787fc24806c695eeab588f44e59b4600030867e78cfe3e68540bf1ac2e1f6948c43395022d39da846a800000d22ee0731de6697a99433da89ea9092dc4a2318aa5d8ccc0f2a6ea16c2f8801aabac2efa39202b17624ac0d0298aa3886a9097cabc91061a4a12e654aa4eb7dadca6d51dd0be90ec6905942e050b0447d905ba8a40f740961d706b69bd478d0b0a24a18d21d012ce8f6af483d5aa446b323b0459a4f800000000591c0227289600000000000246e38
  | 47 => 0xd1ae1059c00000c3add440f22f600015ce78680003f59b0c0000a3a000000025f800078511d8b8a0000912874ca1ea7b62f29e28000223a20f94d20c68000c6720c2070134a78927e62e700383c1800068429fa08a182e1a807582f502f46c8aabc56aa1609a09f4e00000008a980000000000bd7244e00000008bb16ba90b2bb461600005482810436291898c02ca1ce8c7a2c61cbebe2979840111401ee88b0b2027f2b8717f8a05abc42b09e4207aa07ca121a2c4438c1c78d98a82f191a6c0588f89d4b2286b5105c25421b47758dc4c358fc485899a8783116a0f6a5728f507b66fd140e4e023e037792ca6ef84924228544522899415482b88f19ff8558a5b86af0914bc3147094f2e8616099a29a2998a0d19f741768df61bb9b5c02a24eec5d202413d1f1cc2faa70b5283a81262a864f99ca6085984c55301aa36103fc77102dc61220dc8c19f32a24021c38a87fe4558e22172a52414093ae36b9fc8ac88c384f80768634103aac51feeb6ea6e207ea10603c83b8000000021a80003a21770ae22e9633cae6c0000e9a9b91b0a4ee2c408e400000002b960001cd2502000000018063b080003da80006008e9e5ee00007978000bcb1a7cbe81e0628a26ca0000f98000000000000fa000148800000002dd0000000000000004188788ce60001ba000000000000000541a6ee2cb9490604838007f0c501fc0eb4b0d1222a6b00007161d2ca4a176e58d8bc4c771452294072694418b85462b3c8d1925c4e6a932c129ab82781118a1e064c4b40000b0300000002b9838eab00c2706564afb15a3198970000207044480002449de0898195c23b30b49f18c04951868e2dfabba8002be200023f668f0000b690000160275e76309ac60c26885e88678b7ea23eb88986c6c40da89520032b3180007c9800000030dcb2b000005c22f431392585b32c62260a586119000016480000000000a5aa8d42471ac0122ade40b1000097698d430d9f423fc0000c830390000066e05db1e06a987bc6ac8e6a34c16065b28f7caf00000bca9216000000000027d8a4ab16c15a000084e2a984ec8602b16979c4b1a398afc1e467b09684000069a26f1044a3f80004c7af9020d11c843191c423f80008b419202dc800024e9d8418800007bb2eec0000d6600002ee8bf055c9a6278a000259608bae54000166c26e8000554a8fc000000000000000002568262800093d0000365318642a95f25678a180001df82ab8f4218798f292d243617da41c1cd10bab9f8000b8c8000153b0fa007af60a92b1760d399bc13500002bd076e0001b50a5025602c692a00002c280002d74b518d14511984ab9f14e0457ac549e980001fb97d000c00004478874a9ca3a85aa95b07821fae4c9000056290f48d8000001f8000731853c000000016d10f04ce0e44989000020680
  | 48 => 0xf368528910b399ad87ea9750687b12a6f3aa343d32d0e0be82101b284f07d8030c82da93ab2c1900b181f5c80f06fe6ff09ec0fb2ac25471f4aa0887de70f9e0a1e2896e2970c10737098661c08982f98c9c592adaa6ca0b08bac1d929e82d0abb8ad90a1490b0c711dc86f281d0c542b700000000bba1c36bd30a1200030ac73b9b32b293234709800000025c2000175a55d1d7e078b1de7ce197e21788fa20780001c88c8e0000000723b1c2904231a8a1af04031b16e00015d2c72a95683205c2ad02b92bf81102c85a1d853930f87e61d5a2da101c60791bc9928d802baa4d0043a5e6a5303c832919900002414a568a8e32d84d21ac8cd6c68aa2447a91505ab2a764980000004b0a277296883b311f05fb927a0bc8756b7b99749e7167c626139e1b112ac16629023190680c4eac220d6041e402a4b262384d6c96af6e5d19f347681a0ec090000000000058c00006e0182c6c580002e68cb24ae282c0000000090000092a96d00d10478c24b02eafd211277f2050c269fc0397ac1400010a000faad08e6846a51c800000021b000031549c20b5041220be38528088c62f3a1320892038005643e04702218454c7a85ae33f2d0c43b895c168216e52dae5ac103170a7018d82840ad8901312036d2fd04b78e526de992a8392d284d40cc604db0c40c5aace42b856c37b9fd6914892c9118c8c7ec0000a8fa3146419b8ca230a9200018bcbc92edc37709c6ba08a643e8062cae799b24f40ee2bf5af4073f1b564301f12c491b02115accc6398dfc804901a9649788c15089e6c212dac4799380582e70b722db2848a6ac4a0979a698a70a6eb0670741a8244bcaafc46421e4869809240383d4437000049a1c5a6e72cf40629474595a49600025886462c6c7ef800000000001b5000021c0000718870c73c899800020740000000a7d0000a9318ea5be9fe0000290600015a81d08000ab30000000057a0002f1e58e9184000301c0002b721b919b086e16f400001740000a3c00008900000286b02800000000007d595a474010e0514000055e19ac8e2a1489e600a45ff0bcec6d80004e41d6c0000000ae327663db22a8705acc800027960001c1e0000000b7c2e029309d6a00025f44ac964e88c2fb446c0546b5727eac66984606e8414b719eb2bf21a940b0a4a883b1df653f05668052bfa000005c54d265c89797949250c844f58bd28dc0198557154661c84d8af18f8c86e840ac731cfa579056262705aa000199c8cf0e78000123238c9f6e00000007bbb00a0002bc2b71157ebe39f044179dd89b6a0f20a3a594a2fa20880aad247cb8a904c69262525a68c67f87187f68cd471faea0bbd29b802cac30bd78ee42611f5a4be24d601e17ba2e8a89a59700bc47e06f48082d42074818c0002506b178000b120dc256580000000e4e00018aaa
  | 49 => 0x32c2a3c0000000c198ace7d00000000148692da1f6264868635006424ef80005ba85c400024fe7b01e4ec0ca43c0000000360a898aaa800000006740002fb602e0082bc287380002d76281b15e49900000000000bc680003050000000000024c99c2abe000064f00006eaaf125f88cd016980000002f9800028500000000199935c215995000000000ab000000000000559834000051e00029eab24a1ea000000000000003080000a0c2cd600000008e8a93e26984f681d800076c8000a862db87f41c8027a150839b0b1e11222e20572fb05290000c5c9ca8a6aa74886923e2000000000009b04899782557ae2619d97f29a7906a4ad800052028ccb1f0ab24260a04a18800039b9c9a59624c45c402c049b800000000002fb19da0000000c8225d276e8af84f0ab801dd00009de8000181ad3a299b0f69dd0ea81531ef2375186e3be8ba0a5112842641d50285a2b2821a97e0000762000117e1c1096800022bead106d04ed979ec910794a200fc86ce010c0ed978c9f805068a7a71050499fab80067cb130150aa28a2c4ca97203bb25b24ef006e69aaadcc2407ea9fd1d2000006109c6800000b8bf600028ca000000034e80000d49d1e5538d2a2da958846382ce894962cb111e70c1a2032b1a16dc3f916b000000f8a8c226c78880009f30d6a81e197c80e0000b099e024291a0a1a5000019700000bc308249797e0000000023bafd2000092001029ba1a30000000000000000009589a3ea83b030317998455b99324cc232c7ee2654a84800013e81848fe067a46a280413e0ed45db015400025183f8266c3afae94beb800000000001f6000056600003e39d62c2e20688de8000c900f022b5aa0872901348fc116e5f6a296bef234823600001e728f29b7a2ae0b882925d7a328b9791680001704589b134000000082104ee000188a98e2e8e5269d8e32200009e6b05085313ee51326dc2cb2a5c4fea80690a8d3ea09a8401830a844670ade671000073528e21aeaff6938a7160002f3c2b90000473a28828a800000000005fc000000019ae2caa5bc152909a58517862ec9e4c0002b2e67c121884c80008dd9154681193a0a53256aac18b67688e4a0f728389432e620ad1eaa00002b2124059a7a0800016cae2000013a2a5b99b89190e047f8876c2bcadbc5400c8a4aeb03a382930402800003378ad000000a2344ad9e25cae0c1eb1e920e816f222d1f2c000000053b9cfe39704c6bae93640cd85268769a34b1900489409ecc01f0e72a6ca636a89a0d89d6b118a9f9b0053c020e5cb88806cba8b2c8f0262113a80ea8d867244a88b2a762aa092797c800017f499a2b8267316ec9ba26be8d89e3eae10b0477b01b801682e81581676b35152cc5e04acb0a86eab0212a2663171ac71adb0c4523587de108641391981fe2f5068492209321
  | 50 => 0x9bd643a8ebc9991d10000074a0001864ad5908cb03848400000009e103660001776a488000650aa506c980002d8918a4a5933c72282f8378086800012f4749a55a6100c3004c80000482d066f71e72ba21136adf00000002da66e628545f1019c7301a265ea0a421bd80002911328009ab540001dce9422ba261488e455a00001c81f2200028883a70896427893c0c41164445b0e25ef1dbc51010d2201000078c99aa45eaaf03ed0000000258cb68ab38921a72e000000081322504190080ba780b605693f46fe890a1f213c80451392abb0000000000000015f40000d780001fc656729b6000148436f81524d396983eb92fca0fa3aeb161a964391b8aa1f1836615a03a73b132e2598792b4b320229d8f483f6800051924a2318214e67f00cc9a8a9ec5ec2064c89059e0dfad8e00028c0000000099024fc7d52ffa2a32908a4b000000000207d20ca68d3085a29f82d68262844850051cac6920a000289600027bc4c401d40500000419b0940e32e062cc139c15a80000001d0e1718dbabec98320000e0c8070000a11a7440000000950a1fead8800029801b688f1daa01500005a9aba600028d20a015121629a468fb20ceb5aae4291210760b693c648d2ade05b0d3c8e11a1a69bacec047b03e9f5313ea98800079906503a8038e7bd9c2220cb16a75789380001752866225a5d38698c96000035b91e218e98cec8e266a00000009cc93782b18ef824200000002c202eb8c3c03980004d686120000afe168a67e410162a871000000007324758a3e4ff913ca3e0000501086e3ccac1e073a4cea969cd054521288beb04e0a5a72c50998161d527ba8b60862336ab50270021259180f6831b0e4b3705faada0ea2bdb2ef602988be7cf80006c70d7e6a01bee00026ba42f8fbaa9a235c3130000000000063928ac1e1825ec59809831fa41e9960d9e70a8796398a2b00c90000ba88be811891940002b420001bc80c2a0162bd80006a4a1ae4b2000000009f24e094c073c321aa2e11da4b30b5812a14827529bc4875a58450ca3dc991027e6f0b00e00029fe000191a0001560af785288f42336acca60a0a81a20badabda00000003a50000000000024d0374000157a51515a000000009f280000001f66afa80009979306598000014daf944ec00000001842126a9120000000000212c72609d0bcfa176408801c0000adc07a03f295e8f1e7179b62b9d2e3676d86387b6800069000002d819a40001c5c6aba9aebc9a540aa59910afb84e00000000000022232a81e6754ab18b2f915a0cc0000ba906ac935000003a3136000289c123b00c00025a4c4b000030c9e2e8b3904253f9686000195a00000000000000671a55c0678c0c000000010caafe1b0083c000081431f310200002822f222d650f2ce246e1170af280000cd274c1a7a46c0001346
  | 51 => 0x45a72c2c822b1fe05a1436000000044ca3568ffaa56000049e00023ea06caae800000009f7136201326940000dc00002430a4500f40000000277800032b0f0a4b98a004cf80006d80000c122722274a4e8aff2ec863000005c215b66cb0000762991494793f6000089494c868418f10b2379021e3ff96be39922b67f49ae88d126ccb392d128a28aa66df9948071066487b8000000222e43e80004d821a2353236e5848000b220712a76a200c692aca74e92765d5800000015284fc8e06072ac248328000aeba45e00012e4733000e00015a6a1b2e4800000009800000a2487b2c29143067d8d56390a13c27da5fe0000cdcad2aaa8651800000000001c08138c0e1416bfa898e2381b961b38000000239ca5c12bcbc507501e000002dea0d27f3154035f0acc7bf105a17d0000bd1200a6560aee84811a04470a220002d5440b1af88aa9e308c924de4f914be114284e29a1c7c0c79f184f7848c48913cc30b827c7e9963861d2d661ee0d869ce12e28ba8c3aa04acc48d9220c3fdb2486e220ea1b8994095581be8da1dd2896090e9858b4c48c1f906c9313c1d81ace8b0232a32595e2beea30403285d486393d4aeaa2a4599834256f2484b5b8b909bc04feaa52f842c8aa78279aeae3860f6e9f8a44c2e590325b8a34001b1a02c8889245f0a938b781d9a14682aa331056444fa17caf504022001c9ca1da5548ad1b9269cad8a8efad802b11deea289b703931e201721a002aea9041969394070aa1466220b4352ac9a9000d921431ae48551ecabde9dfe38902f642f25ce818a0cc9541e3c17e1c72a0ea124103a5a033a9b8263f2c42a841c087768466b662d4e651080e980a2e835d871696381f46bb0d98502817c4c71f46b0495c625a9cd690a02420fd13323a98a208731ea40002d22a052a2827e26a01f5998635229b4a6880e48a019e85431d9633e00004a60468bf29c2036d951e00000003110000c1a96223e1000023000009c326b2a9616c800012ee49f30d0000000010b9d542cd000000020520001624c5a1bb27c78b64575884c882800c22a1e1802e9d78770318ec1f1d944f38000b7319c0c1eacf684d80007209df00002e124bc00009679962000114a0000fc00002d1c24898dea9a9244c8600006980c2c9de00009268000000010a85f842000000002e9af6a00000000000000abd800026d02aec8b2bb03a10000b4d1ee08c809a24951e4a8151bec4e206e872d98888f616d216b08d49f3a9d6c5617b215ca9f2621825653a83ee14c03c68222d9ab8f146e6ba82bc33eae7ab770000a13270e0000a0844c2fd43009a7400000002cfa31c531138a0000000930000086f0fa66819532849a12a00004a06ec0d5033b1448baf918054f83d8917000000000006371cf6000000000019680cbadae0002834b45887e7378518011
  | 52 => 0x2044448f826cc8ea47a87f152a1f9886400914a89238d28b8595b85002fde06c189ac7d8df2c4700001092d260129654c828b780000e9298e84b6b34adb64aa12c05df301068e18dabdf2fa817a1b3c484a4d841293a40e9260e4630250afa00e24c627d647a052e176000015f0ed2a37a7002358172ab6ac8a8901cacad9aa0c3721e8ea6788661782f720681642000221c14b2466be6836c812951650ea514ab200003f78000c6a84729bf000090600003200000a8eaf78b33800000000001ff01c8a03000000000005360d346c7a1e6000000000010023e48c126cda2e4a1605f270c9e6abd4af80c3010d06b808ae9e415c23f09f0c4a9800089d0b10086a9e43c5011a000025298a26780c628e8c3380000001dbeb1e0c1eb7c93fc669940227f9b3e46eac8e2b52c52a81a18a3c318a485a80007b5a3960002bb23e7b22e908236ca08049c3caa764089261c2149b180000d602528fa4536a5dea4582b0a7e27ac276143e464a42e2aa29661cba03666d1a64c4c0feca7d8cb87d6050e1ae11fa46d2d524e628e66a784c02b8016a03f0fac5d901461ad19e21851d4400030ae9fe8c585740c728572c7a55d802a65900000ff96eea2800006188bac7532fc4a228eac87204ce040a07aabe81dc53c9348aea19d43d1a692798af4657a800000000000000000baf306082cad625a28000111ac747ee8504a8b0000c590000bf6b01e404ab1260f2b489ed3098b3a05d20000f64856188c411869600000000000c5620c000006697003d01d1a290026088e1e5a8281bf20000e86bc605ce1179cce52709c43cb000004f243a3022b6a00024761cc000000025f2a078fee0b180009aa0000befaaae5ce800056e971cbc3935ec6ea09420a89366bf870e74aaab85299cb8a2a2a40a06a52e04a007a12aaa5294e00b4677166857703d294127925a326f643888b84259f3a867ab4c5990c28366a9caa9804887899d0aa0a2e0abc7012e556aec452c2c5c00028ea0bf9e5856417ae3c3971e5808000a3210a895f1494b7b0480c6813001b206fc3410000854a3c47a285420001d40769ac3281710c4027b1d0a250958a3b9e7a0002caa1ea8e462d5b1d8c87a0901c206185dc9d647ab9a5683c0000000061600000000000000000298cbee07b4c0f30ee7191844816a5ea0001a70ab887c24082f7e751996c6f61c84697161c0638da4bcb8bde92326ce5bda78211f06be5e4a2bca062d04819a5c00002ed8000008e36aa7a4a990000000170ab7880001fd80000000a701f388e82321bda71182ba4782788ba62b2a000177ec6c8000b1980deb8d22227f5170e72ca3263dea178c532c3c15b8000740acb6093b138109af662fe96a872f01aca0d92e843c852470b832820723fab1d85bc4560f86b1192b40108254924abce483afce3fa0d52c90af7
  | 53 => 0x84659800080600d2c6d0edab6710ac2dda4caa1696fe8ee1abe8640000000000000000000000d5c00021d400017808899df4000043c3921f96317209200000007e900003c680000000000b1c247e58a1c127e71c960000a562eaa1b61ac000009aa7a89981cf880400002059ec458bab36000000030180003b2a6460640e1c1939d300000266c4284c212d1f085378378000129a11d80002328000000305883a0f10a64aac06891eb087401060000c9e700258a0658000000000000014e812c14061e429106a1074e2ffaaee5b7b17cb421e94c6e26d4ac1800018d89ce00000aa8c316d601a107a39d9718b4a800071026e6449b236209319400025d87308000b6a23a0416180ac0ab192216000000000b029f193e000036a000000001c8000946a5ae6db800037580009b1209a0000f9c11b906244814200001f203ceaf8643b0000108901800016e40002d68bc0311a68a0126a2c1b9a3630400ba1170c89aa71e57b14a07ed9bfe74d3246738a9d244316742ea09b24b50c34246800057e14b40000ede5d997449e3a8d06f99aca551232e7b1ae9006f1a9038225b0c088100a71a2343b824ea5560ac029b17a000012fa63a30d88b50000b480bd85108f18a0ba3947c1905664c0c687900000bff86e00001d7c82b314200011e4ad6000052c83a6b56a0aa62d252a40d26d856000009851270000000008f9b4cadd20a4000023c9f22ec200580000ef1d164832df81621ef070e0e028dd1652080afe6237aed65442c9ea1089d6770835c45080ce00a0b44753a11a07797289f4137e0e2887a19019f892e0eba7c910106a71eb840c31e419fa772121af58001aca893b0b66631044265297264e305204058906c701824173049403aac84a21963e241000000217fab4e02d4632880631d1aa82a58e7e6f00430aff8e7c07b9b520001e88000014e00012fea38000000021e800013f804b071e45197485a900f059e87147be121c9a1000071b209c71e09184f48fb882e835e3de000023c19787618000aa780000000000aad800000024b02e210500000e5027e9d6e8908000903110451628c274f05ee80fad600002e1a0002f5a5f380001e780000001c702a78000a720000bea8300adb15563ec80000000000c6f0000709000000010e881cb09e00022327d8ae9c2af003c0c19e9ca7982e48df98281aa813a7ff00007bea8f083f26522a19a1648b00000003034b942cde644a204817811003211d4799a706a47ad3041c037c5eda92e027020031098f42c9a7421331d283901a82742123651b141095d25a648ba4be6240000519902841e1152287ab8a4a01a1c9b40c40881800088380008540a4a89a0000000024850882e635c80006d99b2a3b590748e32fc29df9dae022a5706088a0ab5f86460ed25a84468ec01ec17e8c6623e4803a6bc2a
  | 54 => 0x1fa1a8a0b31d3e9b5a6d23cf1fac0ef8e6600023c23bd131296a9b646a3adeab8e95e682e0b8e542acd81ca237c22f253639a180e468a1442a894fa347acfea1719be1442456a3e918897e22282128b284eb074803530ca03b8f2e780000077cac1608a8682000235e0ddb1107f783cc0000000b300000a8803aca58861c73a124c839817e9f4a7705ab90cc036944ec1d832a09c291aa570f907841be8c3980000000532275301a35b2dd2395997a7a78efc0001fb400109a01e2000000021304dc02a60e1800012ea244c519a8800000001bea1020a28000000147c00000006bf2482aac86c624faf3289b8ffa7a605deae6a7127fd119e4f01f280000000c3500000000000bb3964c16f800083800000e60000bfb298a000238038c000000024f668ca98e2fc80006d791cc298a94884d1418c6b800099e8cf015f9db000018fa4fa00008b08236ab613dc60eae5c9be11ae358b0c8c488b1200000000f780002c0a3e8251192e000045a0000de88d99f5e2a82a223a0961845100007848cce00000000002f348cca1d206a13845c0a426619a62cb4bb0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c7359140040471bb0db9a80080031799773500100062eb2ee6a002021c9e64dcd400400193ac9b9a800800237a1d63500100346e43ac6a002000ccf739894004001998e7312800800333dcd62500100066639ac4a0020018de835db20040091db04bb64008003179cd65c80100064f39ac9900201c8df865cf20040018bccab9e40080031759573c80100064f322e79002000c9d645cf200401799cc4b9e400801a37e1d63c80100046ec3ac79002000cce7358b200400199ae6b16400800e1f217764801002476416ec900201987d86dd5200400187cc9baa40080031798f754801028e37316ea900200087e8759520040110f90eb2a40080139a08165480100061fbaac89002000c3c755912004009d5040b22400800317dd563480100062e3aac69002000c6f7558920040018d8eab124008012ba201624801001c3e42eec88020028bc84dd910040031b907bb2200803a1f61b75440100061f326ea8802000c5e63dd510040010fd0eb2a20080221f21d65440100061e3a2ca8802000c5c73595100401b17b0dba220080030f99774440100061eb2ee88802000c9e63dd1100400117d0eb22200801e2f21d64440100061fbaac88802000c3c755911004001938e6b2220080323761b73440100062f32ee68802000c5d65dcd100400193cc9b9a20080032759373440100046f43ac688020068dc8758d10040018beeab1a2008003171d563440100064fba2c68802000c9c7458d10040018dccbb9220080031b597724401000657326e48802000cad64dc9100400199cc7b9220080033358f724401000637328e48802000c6d651c9100400195cc839220080032b590724401000667318e48802000ccd631c910040011dd0f312200802e3b21e624401000637bacc48802000c6c75989100400195ee931220080032b1d2624401000667b9cc48802000ccc7398910040011dd0eb1220080023b21d624401000637baac48802000c6c75589100400195ee8b1220080032b1d1624401000667b9ac48802000ccc7358910040018e8ebbb220080031de1776440100063a42eec8802000cb784dd9100400196909bb2200800335e0f76440100066a41eec8802000ce782dd910040019c905bb220080031dddb75440100065bbb6e88802000cb7761d11004001a68ea3a2200800335ddb73440100066bbb0e68802000ce776dc910040019ceec3922008003691d07244010006e2398e48802000c7875dd910040018f70bbb220080031e21776440100065dc26ec8802000cb884dd910040019b707bb220080033620f764401000675c16ec8802000ce882dd910040018f6edbaa20080032eddb74440100065dbb0e88802000cdb76dcd10040019b6ec39a2008003661d0734401000675bb6e48802000ceb761c91004001ad0ea3922008003721cc7244010
  | 1 => 0xea729cc4080029ba17439881000536c2e873102000aae84cc6620400155b0998cc4080029ba17409881000536c2e8131020048f8805d562040091dd0fa92c4080031bdd7525881001e373aca4b1020048ec8754962040091dd0fa12c4080029ba14425881000536c2884b102000ace83109620400159b06212c4080123ba1f325881002735082cab102005e69105956204009d4e20b22c408013aa841645881002752882c8b102005ea9105916204009d8e20b1ac408013b1441635881000637baceab102000aeb805d562040095d100baac408016b9205745881000537428e8b102000a6d851d1620400159d063a2c408002b360c745881000717aa4a8b102000a6f855cd62040014d90ab9ac408002abe11735881000556422e6b102005ae4815cd62040095d100b9ac40800393d4e53588100053742e86b102000a6d85d0d620400bccca3a8ac408002aba13315881000556c2662b102004e6a50d4162040014dd0ba02c4080029b61740588100245fc3ac921020048bc84dd9420400b1e902bb284080122f21d64508100247643ac4a102000cb564dc542040019cac5b8a840801237e1d638c81001c3e42eec99020028bc84dd932040091b907bb264080021fe15764c81001c3e42aec99020008bf845d9320400517908bb264080163d205764c8100247c402ec990200087d86dd5320400187cc9baa64081b31798f754c81035e37316ea990200087e8759532040010f90eb2a64080030f1d1654c8100045ec36e89902000c3e65dd1320400187acbba264081072798f744c81035657316e899020008be8759132040011790eb2264080030fdd5644c8100061e3aac899020048dc8758d32040018beeab1a6408003171d5634c8100064fba2c69902000c9c7458d32040091d90eb1264080031bdd5624c810006363aac49902000caf745893204001958e8b1264080033558f714c81000672b16e29902000cd963dc132040019d2c5b826408016ad205645041002f5220ac4a08203487d86dd5310400187cc9baa620818f1798f754c4100043f43aca988200887c87595310400187eeab2262080030f1d5644c4100062fbaac69882000c5c7558d31040018deeb31262080031b1d6624c41000637baac49882000c6c7558931040070fd0abb642080ca1fe1975c84100061f322eb9082000c5e635d721040178dcc4bae42080221fe1d65c84100043ec3acb9082000c3e75593210400187aeab264208003179d563c84100062ebaac79082000c6e7558b21040018daeab16420800a2f21376484100061e3a2ca908202c8bd86dd1210400187ccbba242080030f59774484100064f31ee8908204bcae62dd1210400117d0eb22420801e2f21d64484100064fba2c69082000c9c7458d210400195ee8b1242080032b1d162484100062e39acaa002000
  | 2 => 0x365881100dc5e432e91022000c3f655d22044001878caba440880032718d748811028656312e910220008bf87d92204401b17b0fb244088003279d363881100064eba6c71022000cae74d8a204400195ae9b1440880021fe15764811001c3e42aec90220008bf845d9204400517908bb2408800237e0d764811000c6e41aec902200087e86dd52044001878c9baa40880031718f754811028e36316ea902207287e87d9520440a30f90fb2a40880030fdd764481100061e3aec89022000c5f75d8d20440018b8ebb1a40880031bdd76248110006363aec490220048f686dc52044001968c9b8a40880033518f71481100065a320e29022000cd4631c520440019cec438a408800e1f21676081100ac3e432ea1022000c3c645d420440018b8c6ba8408802f1b18975081100043fc3eca102200e87d87d94204400187cebb2040880030f5d764081100062f3aec61022000c5d75d8c20440018dcebb1040880031b5d762081100074c320c78822000e686518b1044001d90c6316208803b1d9db658411006e5b3b6c90822002cb6761921044001c68ca3242088033359db638411000e6b3b0c70822000ce676d8a10440179ccec3142088003a9190628411000762318c50822000c3f749d165040e34ef02ba2ca080169d20574594100062fb9ce6b28200087e87d0d65040010fb0fa1aca080031bdca72594103853dc02e4b282004a78805c965040010fd0e212ca080021f61c42594100052f41884b282000a5d83109650400147d0998aca080028f61331594100443f43e80b28200087d87d01650400b1e902baac8080122fa1f54590100061fbaea8b2020048bc8755164040070fd0bb9ac8080021f61773590100245f43c86b202000c3f759d5640400156f02baac808016ad20575590100051f42ee6b202000a3d85dcd640400957100b9ac80800387d4e535901002d5a40ae4b202000a3e851c9640400147b0a392c808002a7a0c72590100054ec18e4b202000e2f52949640400bc6ca3a8ac80801e2fa1f31590100045ec3e62b202004e3a50d4164040091bd0fa9ac60800317dd75358c100246e43aa6b1820048de87d0d63040014bd0ba1ac608002976174358c100272b882cab182004e55105956304009d3420b22c608017a64416458c100062fbaceab182000a5e859d163040014bb0b3a2c608012b62017458c100070faa4a8b182000a5f855c963040014b90ab92c608002a7e117258c100054e422e4b182005ad4815c963040095b100b92c60800393d4a5258c100046f43884b1820008dd8710963040014bd0a212c608002976144258c1002f2b28ea2b182004e5a50d4163040014bd0ba02c608002976174058c100247c402eca1820048bc8759143040091b90eb1a86080032e5937050c100066cb1ee0a182000e2f549526204001c9
  | 3 => 0x720a2000c5f655ce41440018b8cab9c828800327d91739051019e4e322e720a20008df87d8e41440191bb0fb1c8288003339cf629051000666b9ec520a2000cce7318a414400199ae631482880033618f70505100065db20e0a0a2000cd8631c141440010fd0dbaa62880030f193754c51031e2e31eea98a206487e87d9531440c70f90fb2a62880030fdd7644c5100061e3aec898a2000c5f75d8d31440018b8ebb1a62880031bdd7624c510006363aec498a2000c6f7518931440018d8ea31262880032e193704c51000674316e098a2000cb8641c131440019b6c638262880033a188704c51001c3e42ced90a200087c865d72144001878c8bae42880031718d75c851005e36312eb90a200087f87d9721440010fb0fb2e42880030f9d764c85100061ebaec990a2000c5e75d8f21440018baebb1e42880031b9d762c851000636baec590a200bce8629c321440179d0c4b86428800e1f21676885101543e432eb10a2000c3c645d621440018b8c6bac428817b1b18975885100043fc3ecb10a200e87d87d96214400187cebb2442880030f5d764885100062f3aec710a2000c5d75d8e21440018dcebb1442880031b5d762885100061e3a6ca90a20008be86dd1214400187ecbba242880030f19774485100064e31ee890a204bcac62dd121440b917d0fb22428812e2f21f64485100064fba6c690a2000c9c74d8d214400195ee9b1242880032b1d362485100063c32ee090a2000cd863dc121440018f0ca38242880033618c704851000675b10e090a20018dc839d821440018bce7b284288003279cf640851013c6e432e610a2000c5f655cc21440018b8cab98428800327d9173085100064e322e610a200bccc625cc21440011bf0fb1842880323761f63085100066739ec410a2000ccd73d8821440018b8e7b2a8088003271cf64501100046f436e6a022000c5f65dcd40440018b8cbb9a808800327d93735011010e4e326e6a02205a8de87d8d40440431b90fb1a808800333dcf62501100066639ec4a022000ccf731894044001998e631280880031d197715011000672316e2a022000c74651c5404400196ec838a80880033918871501101143e432eb1822000c3c645d630440b38b8c6bac60880021fe1f658c1100743ec3ecb1822000c3e75d92304400187aebb246088003179d7638c1100062ebaec71822000c6e75d8a30440018daebb1460880031b9d4628c11000636ba8c51822000ce462dc530440019aec638a608800339188714c11000c6e41ced9022000c5e73d97204400193ce7b2640880023721973c81100062fb2ae79022000c5c655cf204400193ec8b9e40880032719173c811005e66312e790220008df87d8f20440011bb0fb1e4088003339cf62c811000666b9ec5902200bce4629c72044005179093b440880030f9d
  | 4 => 0x24400155908b10c488002b3e0d62189100056641ac43122000c6e76d9462440011db0f328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac84594624400159f06b28c488002b320d6518910006373b0ca3122000cae76d906244001c5ecbb20c4880038b197641891000476c3cc83122000a6e8599062440014db0b320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400195cec320c4880038bd94641891000716328c83122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e8c64d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab2116318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d90631891000746320c63122000e2f549506244001c9ea7298c4880029ba17431891000536c2e863122000aeb8054462440015d100a88c4880029ba14411891000536c28823122000aae84cc4624400155b09988c4880029ba17401891000536c2e803122000aae840c0624400155b08180c4880029be1510189100053642a203122000aaf84440624400155908880c488002b3e0d10189100056641a20312200087f855da42440070f90abb4848800237e0d769091000c6e41aed212200b8ec825da42440070fd0bbb284880021f617765091000c6f41eeca1220008dd83dd942440010ff0abb2848800e1f21576509100046fc1aeca1220018dc835d942440011df04bb284880023de05765091005c5f43ec8a1220028ee87d8942440010ff0abb4648800e1f215768c9100045fc22ed19220028bc845da32440171d904bb4648800e1fa17764c9100043ec2eec99220028be84dd9324400117b09bb2648800e1fa16764c9100043ec2cec99220028be849d9324400117b093b264880021fe15764c91001c3e42aec99220008bf845d9324400517908bb264880023be09764c9100047bc0aec99220008fb805d932440070f90a3b2648800a2f210764c9100043f436ea9922000c3c64dd532440d98b8c7baa64881af1b18b754c9100043f43eca992200087c87d953244001878e9b2a64880022fa1b744c9100061fb2ee89922000c3c65dd13244083938c7ba264881ab2b18b744c9100045f43ec899220008bc87d91324400187eebb2264880030f1d7644c91005c6f43ec69922000c5f75d8d32440018b8ebb1a648800327dd3634c9100064e3a6c699220018ee87d8932440018deebb1264880031b1d7624c91000657ba6c49922000cac74d8932440018bce7b2c8288003279cf64905101cc6e432e
  | 5 => 0x8003a3d9363d891000746326c7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000c6d751d762440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d36244001c5ea92a6c4880029ba1773d891000536c2ee7b122000aae84dcf624400155b09b9ec48800393d4e53d89100053742e87b122000a6d85d0f624400155d09b8ec488002ab61371d891000537c2ae3b122000a6c855c762440014dd0a20ec4880029b61441d89100055742663b122000aad84cc762440014dd0bb86c4880029b61770d891000567c1ae1b122000acc835c362440014dd0ba06c4880029b61740d89100055742061b122000aad840c362440178d8c4bacc4880030f9d365989100062f39ecb3122000c3e7419662440018bce632cc4880030fd9574989100061e32ae9312200bcac625d2624400187cebb24c4880030f5d764989100064f39ec93122000c3e75192624400187aea324c488003279cc64989100062fb2ae73122000c5c655ce624400193ec8b9cc48800327191739891005e66312e73122000c5e75d8e62440018baebb1cc488003279d363989100064eba6c73122000c5e7518e62440018baea31cc488003279d063989100064eba0c73122000c6e75d8a62440018daebb14c4880032b9d3629891000656ba6c53122000cce73d8a624400199ae7b14c48800e1fa1b75589100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d624400117f08baac48800a2f21175589100046fc1aeab1220018dc835d562440011df04baac4880023ee0175589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891000637baee4b122000c6c75dc9624400195ee9b92c4880032b1d3725891000667b9ee4b122000ccc73dc96244001968e9b8ac488003351cf71589100063c3aee0b122000cd873dc162440011df0eb10c4880029be1562189100053642ac43122000aaf845886
  | 6 => 0x46ec3885b1a2000a5e8510b63440014bb0a216c68800297a1771d8d100052ec2ee3b1a2000a9f845c7634400153908b8ec68800297a1441d8d100052ec2883b1a2000a5e85d0363440014bb0ba06c6880031718f7558d100043f43ecab1a2000c3c74d9563440010fd0e32ac6880030f1d06558d100061fb2ee8b1a2000c3c65dd16344001938c7ba2c6880022fa1f6458d100061fbaec8b1a2000c3c75d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a2000ccc63dc963440018deca392c6880031b1947258d1000657b20e4b1a2000cac641c96344001998c6392c68800e1fa1f7558d100045fc22eab1a20028bc845d563440011bf06baac6880023be097558d1005c76412eab1a200087e871d5634400517d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac68802e3ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac6880032e1d37058d1000674396e0b1a2000c5e76d9463440011bb0f328c68800297a166518d100054f424ca31a2000a9d84994634400159d05328c688002b360a6518d100046fc3aca31a2000a9f84594634400153908b28c688002b3e096518d1000566412ca31a2000a5e8619463440018bcec328c688003279db6418d100070fb2ec831a2000e1c65d9063440011bb0f320c68800297a166418d100052ec2cc831a2000a9e84990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000a9e86190634400193cec320c68800387d946418d100070e328c831a200387e85dd943440010fb0bbb2868802e3ba0b7650d1000476c16eca1a200087f855d943440070f90abb286880022fe117650d100046fc1aeca1a20008ef825d943440171d904bb286880023ee017650d1000c5f43ec8a1a20028de87d8d43440018daeba96c48800f1b1d652d891001c77c3aa5b122000a6e8510b62440014db0a216c488002b3a0c42d891000566c1885b122000aae84997624400155b0932ec488002b3a0e65d891000566c1ccbb122000aaf84597624400155908b2ec488002b3e0d65d89100056641acbb122000e2f65d936244001c58cbb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000e4f65d8f6244001c98cbb1ec48
  | 7 => 0x7d87107654400147d0998eca880028f61331d951022d3b40ee1b2a200087e87d0365440010fb0fa06ca880028fa1030d95100051ec2061b2a2000c3d75d53644400717f0eaa6c8880021fe1573d911001c3e42ae7b222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb222000a9f83597644400153906b2ec888002abe0965d911000556412cbb222000a3e8598f644400147b0b31ec888002aba0a63d911000556c14c7b222000c3d751d7644400147f0ab9ec8880028f21573d91100070fa9ca7b222000a3e859cb644400147b0b396c888002a7a0e72d91100054ec1ce5b222000e2f5294b644400117d0f98ec8880022f61f31d91100054f41ee1b222000a9d83dc3644400147f0ab86c8880028f21570d91100045f43861b22200d8bd870c36444001878c9baac8880021fa1f65591100062e39ecab22200087e8719564440018b8e632ac88800317d9773591100062e32ee6b222000c9c64dcd64440018decbb92c8880031b197725911000656326e4b222000c6f651c964440018d8ca392c8880032b190725911001c3f43eeab2220008bf845d564440011bf06baac8880063720d755911000477c12eab22200b8ec825d564440011ef02baac8880021fa1c75591100061fbaee8b222000c3c75dd164440031bd0fb9ac88800317dd773591100062e3aee6b222000c9f74dcd64440018beea39ac888003171d473591100064fba0e6b22200b8ee87dc964440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100063a3aee2b222000ce472dc564440019b0e7b82c8880030f9db65191100045ec3cca3222000a3e85994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c888002ade0565191100051f430ca3222000c3e76194644400147d0b318c8880028f616631911000557414c63222000aad8298c64440018baeba9ec68800e37e1d53d8d100052f42e87b1a2000a5d85d0f634400153d0932ec688002a761265d8d1000567414cbb1a2000acd82997634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc825976344001c3ecbb26c6880038719764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c6519363440018baea3aec68800297a1474d8d100052ec28e9b1a2000e1f5495363440014bd0bb96c6880029761772d8d100054f426e5b1a2000a9d84dcb6344001c9ea5296c68800237a1c42d8d100
  | 8 => 0x4b8aca1002e9b209715942039d3dc02e2b284004a78805c565080010fd0e20aca100021f61c41594200051f42662b284000a3d84cc565080174dd0598aca100029b60b31594200ac3f43e80b28400087d87d0165080011bf06baac8100063720d755902005c76412eab20400387e85dcd64080010fb0bb9ac8100122f21d6450c200246e43ac6a18400087f855ce61080070f90ab9cc2100022fe1175584200145e422eab0840008df835d561080031b906baac21002e3b20975584200145f43ee8b08404bcac72dd161080b9958e43a2c210003179cd65904200062f32ae72084000c5d655ce410800b9acc2b9c821000aad21161904200066ab9ac3208400bc6c7259541080018dacbb9282100123d21d615042001c3e42eec988400087f855d931080070f90abb262100022fe11764c4200145e422ec988400087d86dd531080010fd0eb2a62100021f21d654c4200247a43ac29884004cf07058531080018dceabb442100031ba15768842000636c2aed1084000c6d765d621080018b8e6b2a80100031799773500200062eb2ee6a004000c6c75dd920080018df0bbb240100031b217764802002675286ec9004000ce950dd920080018deedbaa4010003391c561480200043fc2ae7b26200387c855cf64c40018bf0ab9ec9880031721573d931001c3f43eeab1e200087e871d563c400b1bd0fa1ac7880021fe157650f1001c3e42aeca1e20008ef825d943c40171d904bb287880062fa1f6450f100045fc22eab1620028bc845d562c40011bf06baac5880063720d7558b100145f43ee8b162041a9e83d9242c400117f08bb285880022fe11768cb100145e422ed196200087f855d932c40070f90abb265880022fe11764cb100145e422ec99620058dc8758d32c4001938e8b1a65880172d1c5645031000476c3ec410620008df835d564840031b906baac9080023be09755921005c76412eab24200387e85dcd64840010fb0bb9ac90800637a1f73592100062f42ee6b242000c5d85dcd64840011bf06bb287080122f21d6450e1001c3f43eeab14200087e871d562840010ff0abb4850800e1f2157690a100245fc3ac92142041a9c8359242840010ff0abb2850800e1f2157650a100046fc1aeca1420018dc835d942840010ff0abb2650800e1f215764ca100045fc22ec99420028bc845d932840171bd0fb1a6508003271d3634ca1002674382c490c20008ed87d8821840014bd07326ca880029760e64d951000537414c9b2a2000a6d82993654400147d0931eca880028f61263d951000537414c7b2a2000a6d8298f654400187ae83a6ca88003175cc73d95100043f43e87b2a200087d87d0f65440018dae4396ca880021fa1c42d95100043ec3885b2a2000a5e8310b65440014bb06216ca881169ea0371d95100043f43883b2a200e8
  | 9 => 0x7158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4005cd6831c563480019a86038ac6900033c1c77058d2001c3f42eeca1a400087d85dd943480010ff0abb2869000e1f2157650d200045fc22eca1a40008df835d943480011ef02bb286900163d2057650d2002477436e4a1a4000c6c65dc943480010fd0dbaa64901b61fa1f654c9203643e43eca9924000c3c74d95324800187ecbba264900030f197744c9200064e3a6c699240008df835d361480031b906ba6c290002ada1331d852001c3f436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac290003179cf65185200062f398ca30a4000c5f655cc61480018b8cab98c2900023de1d61185200055a422c230a4000ad48358461480010ff0ab98c29000e1f21573185200062fc2ae630a4000c5c855cc614800b9a902b98c290002ada1331185200066ab9e6230a400087f855da41480070f90abb48290003179cf65905200064f39ec920a4000c5f655ce41480018b8cab9c82900031b1957290520024f4402e520a400387e85dd941480010fb0bbb282900021fe15768c52001c3e42aed18a400387e85dd931480010fb0bbb2629000e1fa16764c5200043ec2cec98a400387c851d931480010fd0dbaa62900021fa1f654c5200043e43eca98a40058dc8758d314806753908b1a6290016b5205634c5200063632ced90a4000c6f859db21480018d90b3b642900031b9db65c85200043e432eb10a405ed68205d621480010fb0fb2c42900030f1d365485200061fb2ee890a4000c3c65dd12148001968e9b0a42900032d1d061485200063c32ee090a4000c78651c12148001cceca30a42900036add07048520006d43a0e090a40009ea861c121480099d50c38242900135aa147048520026b4c28e090a4000d6b651c12148001ad0ca3824290003171cf65501200064e39ec8a024000c5f65dcd40480018b8cbb9a80900031b19772501201143e432eb182400087f87d9630480330fb0fb2c609002e37e1d638c12010d4e422c71824000ad48158e304800187ce9b2c40900030fd9574881200061e32ae91024004da8205d220480a38dcedb2c40901479ad83658812005c76c38c31024000ce571186204800187ee93a2ca1000297e0d74594200052e41ae8b284076a6f825d165080174d904ba2ca1000317dce735942005d37414e6b284075a6d829cd65080010fd0fa1aca100021f61f435942005d3741086b284000a6d8210d650800147f08b8aca100028f21171594200052fc1ae2b284000a5c835c565080e94df
  | 10 => 0xb2440008be87cc5648800117b0f98ac9100138e94350592200246f43ea6b1c4000c5f75d4d638800517d09b8ac7100022f6137158e200245e43ac8a1c4000cb964dc1428800187cc9baa65100022f61b744ca2020c5f43ac899440678bc87591328800187eeab2265100030f1d5644ca200062e3aac6994400087f855ce61880070f90ab9cc3100030fdd664586200061e3acc8b0c4000c3f755916188001878eab22c3100021fe15769062001c3e42aed20c4000c9e73592418806793cc8b9c83100032759173906200245e426eca0c400087f855d941880070f90abb283101432b1c9645062002d5a40ac8a0c400087f855d931880070f90abb263100030f993754c6200061fbaac898c4000c3c7559131880018b8eab1a63100032b993724c6200061f322eb10c4000c3e75592218800187aeab2443100035a5d570886200045ec36e890c40008bc87591218800195aed32043100032b5d964086200064e39ac8a044021c9e64dcd408800193ac9b9a8110003399c561c82200061eba0e9b2a4000a5e831d365480014bb063a6ca90003175cc73d95200043f43e87b2a400087d87d0f654800147d09b96ca900028f61372d95200052f41ee5b2a4000a5d83dcb65480914f501b96ca9000297a0c71d95200052ec18e3b2a4051a6e821c765480014db0438eca900021fa1c41d95200043ec3883b2a4000a3e84cc7654800147b0998eca901461fa1f40d95200043ec3e81b2a4000a3e840c3654800147b08186ca900021fe1573d912001c3e42ae7b22400087e87d9564480018b8e7b2ac8900021fa1c65591200062e398cab224000c5f65dcd64480018b8cbb9ac8900031dd9771591200063a32ee2b224000c77651c564480018e8ca38ac8900032d190715912001c3f43eeab2240008df835d564480031b906baac8900023be0975591200047bc0aeab2240058f4815d564480010fd0e3aac89000637a1f73591200062fbaee6b224000c5c75dcd64480018beea39ac890003171d473591200064fba0e6b224000c6c75dc964480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89000339dc871591200065b210e2b224000cb4421c5644800117f08b8ec69000a2f21171d8d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d200061fb2ee8b1a4000c3c65dd163480018eecbb8ac6900031d1977158d200063bb28e2b1a4000c74651c563480019a8c638ac69000e1fa1f7558d200045fc22eab1a40028bc845d563480011ef02baac6900163d2057558d200043f438eab1a40028be87dd1634800187eebba2c6900030f1d77458d200061fba8e8b1a4000c3c751d16348001938e9b9ac6900031ddd7
  | 11 => 0x4c0011df0eb10c498002b920562189300043fc2aed212600387c855da424c0010ff0ab96c29800e1f21572d85300047bc3ac230a6000ae482584614c00117f08b90c29800a2f211721853002c6e41ced20a600087f855da414c0070f90abb482980cf271917390530006adba8e098a60028be849d9214c00117b093b242980163720e76085300043fc2aec10a600387c855d8214c00117f08bb0429800a2f211760853005e66312e610a6000ccd73d88214c0019aae7b08429808727193735013000c6ec38c31826000cd571186304c0171790eaa2c99000e1fa1f7558f200062f41eeab1e406bc5d83dd563c80d70fd0e3aac79002e37a1f5358f200062fbaea6b1e400b8dc8754d63c80171bd0fa1ac79000297a174358f200052ec2e86b1e40028be84dc563c800117b09b8ac7901de97a167558f200062fbaceab1e406ba5e871d563c80018bd0e3aac79000297a167458f200052ec2ce8b1e4000a5f855d163c80014b90aba2c79002eb32097458f200064eba0e8b1e4000e1f5495163c800153d09b8ac790002a76137158f200052f42ce2b1e4000a5d859c563c800153d0938ac790002a76127158f2005d67414e2b1e4000a5f855c563c80014b90ab8ac790002b6e017158f2005d67414a2b1e4000acd8294563c80014bd0a20ac790002976144158f2005d6741082b1e4000acd8210563c80014bf0ab82c790002972157058f200054fc22e0b1e4000a9c845c163c80015af02b82c790002b52057058f2000567c12a0b1e400bacc8254163c80014bd0ba02c790002976174058f2005d6741680b1e4000acd82d0163c80010ff0abb2879000e1f2157650f2002476412eca1e400b8dc8758d43c800553908b1a879002f331c96350f2000666b1ee4a1e40018de83dd161c80011bb07ba2c39000637a0d76907200046fc32e720e40008df8758e41c80011bb0eb1c839002f339c9638c72000666b1ae518e400b8dc83dd931c80010ff0abb2639000e1f215764c72031e2f31eea98e4000c5f7558d31c80018b8eab1a63900033658c704c72000657bb6e890e4000caf761d121c80011bb0db9a819008637a1d63503202d46e43ac6a064059c5e635d630c80018bceab1c6190003175d5638c32005e66392c69864000ccd63dc930c800917d0faa2c9100030fdd754592200245e43aa8b24400387e85dcd64880010fb0bb9ac9100122fa1e43592200061fbaceab244000aaf825d564880a155904baac9100028fa1773592200051ec2ee6b244000e1f5394d648800147f0ab92c9100028f21572592200054fc1ae4b244000a9c835c9648800156f02b92c910002ad205725922028717296a4b244000a9e839c5648800153b0738ac9100028fe1571592200051e42ae2b244000aaf825c5648800147d0a38ac9100028f61471592200065ab88e2
  | 12 => 0x126e201744c5400062fbaec698a8000c5c75d8d315000917b093b642a000237e0d76c854000c6e41aed90a8000c5c635d721500018bcebb1e42a0003175d763c85400063b3aec390a8000c7675187215000196ee830e42a000237e0d768854000c6e41aed10a8000c5c635d62150001938c6ba442a0003179d763885400062ebaec710a8000c6e75d8a21500031bd07bb242a00023760f764854001c3f428ec90a800087d851d92150005179083b242a00032718f74485400064fba6c690a8021c9c74d8d21500031b9073b042a00021fe15760854001c3e42aec10a80008df835d821500031b906bb042a00172d18574085400046e432e610a80008df87d8c21500011bb0fb1842a00163e219700854011e4f3b6c72028001c9e7618e405000517b0e30c80a00032d5c461901400061fba4e8b2c6000a5f835d1658c0b34b906ba2cb1816697a0e72596300052ec1ce4b2c6000c6f729c9658c0010fd0e212cb180021f61c42596302cd2f41884b2c6000a5d83109658c0018eee338acb180028fe1171596300051e422e2b2c6000a5f835c5658c0b34b906b8acb180021fa1c41596300043ec3882b2c602287e87d01658c0010fb0fa02cb1800317dce65592300070fa1acab246000acd83109628c0070fd0bb8ac5180021f6177158a300062f32ee6a14606bc5f76dd5328c001a38e8b2a651819e67a1f744ca303564fbb6e89946068c9f761d1328c001a3eea3a26518003471d4744ca3005c6f43ec89946021c9c74d91328c01759d05b226518087271d1644ca3000726b2cc49946000d8c74989328c001b18e8b12651800237618714ca300bc6ec36e09946000d5b75dc1328c001b30e838265180022fe1172986300145e422e530c6000c3c74995618c001878e8b2ac3180030f99774586300061eb2ee8b0c60008bf845d5618c00517908baac3180032710f74586300145f43ee8b0c6000c9e83dd1618c00193b07ba2c31800327ccb74586300064fba686b0c600387e85dc9618c0010fb0bb92c318002a721132586300064fba264b0c6000c9f435da418c0b38bce6b2c831812eaba0b64906300062f32ae720c6000c5d655ce418c01f1bf0eb0c631800395595618c63008c6fc32e118c600387e855db218c0010ff0cbae43180021fe1d65c86300043ec3acb90c600387e855da218c0010ff0cbac43180021fe1d65886300043ec3acb10c602199e84dce218c00117f08bb2431800a2f21176486300061e3a2ca90c6000c3e65dd1218c00187acbba24318003179977348630006563a2c490c6059c5e73594218c0018bccab9843180031759573086300062fb9acaa046059c5c73595408c00717f0eaa6c89800237e0d755913000477c12eab22600b8ec825d5644c0011ef02baac8980163d20575591300043fc2ae3b12600387c855c762
  | 13 => 0xc6e41ae9300420387e87dd560084a38d8e5baac0109cb1b1c875580210057440242b004203c7875941600840b1f10ea82c010943275917398a400247643aa4b14800087f855d932900070f90abb265200021fe15739864001c3e42ae730c80008df835d561900031b906baac3200422fe1d61906400945fc32e120c800087f855d931900070f90abb2632002f1b98975c864000636baac590c804bcae62dd121900010fb0f3aec6a000e1fe1d75d8d400062fc1aebb1a8000c5c835d763500018baeba9ec6a000e37e1d53d8d4000c5e422e3b1a8000c5e769d763500018bcecbaec6a0002b3e0965d8d4000566412cbb1a8000ad78159763500015a902b2ec6a0002e3a0b74d8d400052ec3cebb1a8000c5f875d763500014bd0a3aec6a0003175d475d8d400052f42ee5b1a8000a5d85dcb635000153b09b96c6a000297a1472d8d400052ec28e5b1a8000e4f5294b63500014bd0bb8ec6a00029761771d8d400054fc22e3b1a8023a9c845c763500014bd0a38ec6a00029761471d8d400054ec20e3b1a8000e5b5094363500011bb0f328c6a0002a76126518d400046fc3aca31a8000acf82594635000159904b28c6a0002b5e056518d400056a40aca31a8023c9c76d8d435000117d0db8a86a016b66dcc7050d4000636baea5b128000aad84d4b62500010ff0ab8ec4a000e1f21571d89400046f43ec6b128000c5f75d8d62500018b8ebb1ac4a000237a1c63589400062fba8c6b128000c5c7518d62500019aec7b8ac4a00033518f71589400066bb18e2b128000cd4631c562500018bcebb18c4a0003175d763189400062f3a8c63128000c5d7518c62500cf938e8318c4a00023be1d62189400053642ac43128000ae4815886250083938c6b9c84a0106a7a1b639094000746310c721280008bc865c6425000917b093b464a000e1fa16764c9400043ec2cec99280028bc841d932500d98b8c7baa64a01072718f744c9400062fbaec69928000c5c75d8d3250043938e9b1a64a000a6721d434c94000d4e432869928000c9c7650d32500a171904a1a64a00021fe1572d854001c3e42ae5b0a80008de87d8d61500018beebb1ac2a0003171d763585400046f438c6b0a8000c5f7518d61500018b8ea31ac2a01e336dc0635854000667b1ee4b0a8000ccc63dc9615000199ec6392c2a00033318c72585400062f3aec630a8000c5d75d8c61500018bcea318c2a0003175d463185400047bc3ac230a8000a748558461500015c904b08c2a00171d20575185400063abaea230a8000e97631854150001d28c630a82a004aada1c615054002e5b438c2a0a8005e3685185415000bc6b0a30a82a00032d1c8615054010e4f3a6c718a800387e859d931500010fb0b3b262a000327d0c764c54031e2e31eea98a80048bc865d131500a135904ba262a0
  | 14 => 0xf75d916348401878ebb22c6908022fa1c6458d210061fba8c8b1a4200c3c751916348401976c9b82c6908032e1937058d210065db20e0b1a4200cb8641c163484019b0c6382c69080e1fa1f7558d210045fc22eab1a42028bc845d563484011bf06baac6908023ee017558d210247c402eab1a420087e871d5634840517d0fba2c6908030fdd77458d210061e3aee8b1a4200c3f751d16348401878ea3a2c690803171d77358d21006563a6e4b1a4200c7b75dc163484018f0ebb82c6908032edd37058d210065c3a6e0b1a4200c7b751c163484018f0ea382c6908032edd07058d210065c3a0e0b1a4200cdb731c163484019d6e4382c6908033cdc47058d210043fc2aeca1a420387c855d9434840117f08bb286908023be097650d210047dc02eca1a42048f8805d9434840317d0fb2286908032dd9071509210061e326ea99242008be86dd132484cf17d0fb2264909062f21f644c9210061fbaec89924200c3c75d9132484018b8ebb1a6490803279cf64905210064fb22e720a4233c9c645ce4148497958e5b2282908030f193754c5210061fbaec898a4200c3c75d9131484018b8ebb1a62908032b193724c5210061e322eb10a4200c3e75d92214840187aebb2442908021fe1573d812101c3e42ae7b02424b8bc86dd1604840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9c73191604840193ec9b9ac0908032719373581210061f3aec83024200c3d75d90604840187cea320c0908030f5d464181210047dc3ac03024200a788558060484015b106b00c0908131e201751812105c76c3c423024200ae98088460484018f2eba80c0908162f21d545902101c3f43eeab184200c5e83dd563084d78bb07baac6109ae1fa1c7558c2102c6f43ea6b184200c5f75d4d630840b1b90ea9ac61081637a1f4358c210052f42e86b184200a5d85d0d63084ef4bd0b3aac61080317dd67558c2135d2f438eab184200c5e871d563084014bd0b3a2c610802976167458c210052fc2ae8b184200a5c855d1630841759904ba2c610803275d07458c210070faa4a8b184200a5e859c163084014bb0b382c61080297e157058c210052e42ae0b184200a9f845c1630840153908b82c61082eb32097058c2102d6a40ae0b184200a9e841c1630840153b08382c610802b3e095058c2105d66412a0b184200a5e85d0163084014bb0ba02c61082eb3a0b4058c2100566c1680b18420087f855d943084070f90abb2861082e3b2097650c2102c6e43ac6a184202a9c8458d4308417998e4b1a86108033358f7250c2131e2f31eea9884200c5f7558d31084018b8eab1a62108031ba17764842100636c2eec9084200caf76dd1210840195eec3a2421080237e0d749802100
  | 15 => 0x998acb908028f613315972105d3741662b2e4200a6d82cc565c840147d09382cb908028f61270597210052f41ce0b2e4200a5d839c165c84174dd05382cb9093e9b60a70597210043f43e80b2e420087d87d0165c840147d08182cb908028f610305972105d3741060b2e4200a6d820c165c84011bf06baac9908063720d755932102c76412eab26420387e85dcd64c84010fb0bb9ac99080e1fa1770593210043ec2ee0b26420b8bc8759143c84171b90eb1a8790803179cd65907210062f32ae720e4200c5d655ce41c84178d8e4b2a83908031b59772507210043ec36ea98e426387e8759531c84c90f90eb2a639080e1fa1773583210043ec2ee6b064200c3f749d165884014bd073a2cb108029760e74596210062fb9ce6b2c420087e87d0d65884010fb0fa1acb108028fe1172596210051e422e4b2c4200a5f835c965884014b906b92cb109e69de0572596210053dc02e4b2c4200a78805c9658840147d0998acb108028f61331596210063db84e0b2c4200a5f835c165884014b906b82cb108029be0970596212f536412e0b2c420087e87d0165884010fb0fa02cb108028fa1030596210051ec2060b2c4205a76810c165884014eb02182cb1080e1fa1773592210043ec2ee6b2442058be8790d64884070fd0bb82c9108021f617705922102c6f43e86b1c4200c6e65dc943884010fb0dbaa65109b21fa1d654ca2136c3e43aca9944200c3c74595328840187ccbba265108030f597744ca210064e3a2c6994423487d86dd531884010fd0eb2a63108aa1f21d654c6210046fc1ae930442018dc835d260884018b8e732ac110803171cd65582210062f32ee6b044200c5d65dcd60884011bf06baac1108063720d755822101c3f42ee6b04420087d85dcd60884018bd0bb9ac1108031761773582210057540642b0442058ed82dd7644840187aebaa6c89080e2fe1d54d91210043fc2ae7b22420387c855cf64484010ff0ab86c89080e1f21570d91210054fc1acbb224200a9c83597644840157700b2ec890802ae20165d912125d57416ebb224200aad82dd7644840187aea3aec8908028fe1573d91210051e42ae7b224200e1f5394f644840147d0bb96c8908028f61772d91210054f41ee5b224200a9d83dcb6448497c5ca5a96c8908038dd4651d912125c5f43e63b2242008bd87cc7644840153d07b86c890802a760f70d91210051fc2ae1b224200a3c855c3644840147d0a386c8908028f61470d912100556c10e1b2242008be870c3644840117b0e186c8908022fe1175591210046fc1aeab2242018dc835d564484011f700baac8908123e20175591210045ec3cca3224200aad82994644840117f0eb28c890802a7e0d65191210054e41aca3224200abb80594644840157100b28c890803175d753d8d210045f43ec8b1a4200c3
  | 16 => 0xd91310043f43ecab22620087e87195644c4018decbb92c8988031b197725913100637b28e4b226200c6c651c9644c401958c8392c8988031ed9770591310063c32ee0b226200c7b651c1644c4018f0ca382c8988032e190705913101c3f43eeab2262008ef825d5644c4171d904baac8988023ee0175591310247c402eab22620087e871d5644c4018deebb92c8988031b1d7725913100637ba8e4b226200c6c751c9644c40195ee8392c8988031edd770591310063c3aee0b226200ceb72dc1644c4019d0e5b82c8988031edd470591310063c3a8e0b226200cbb741c1644c4019b6e6382c8988033adc8705913100674390e0b226204cba841c1644c4019b686382c8988033610c70591310066d990e0b226200cb8411c1644c40159b06216c4988021fa1f65589310061e3a6cab12620087e87195624c401878e832ac4988030fd9774589310061e32ee8b126200c7b65dc1624c4018f0cbb82c4988031ed9470589310063c328e0b1262008ef87588624c40155908b10c498802ba20162189310043fc2aed212620387c855da424c4070fd0bbb284988021f61776509310062e32ee6a12626bc5c76dd5324c401a38e9b2a649899e67a1f744c9313564e3b6e89926268c9c761d1324c401a3eea3a26498803471d4744c93119e4e3a6c8992620b8dc87591324c467938e8b22649882eb3209644c9310056c402c89926200d8c74d89324c401c9eca3126498803631d0624c931006ca3a6e29926200d57751c5324c4011bd0db82649898f179cf65905310062eb9ecb20a62018bf87592414c49755904b248298802ae201649053131f2bb0ecb18a62008bf845cb604c40517908b96c09880e1fa1b755813131c3e436eab02620087e87d95604c401878e9b2ac0988021fa1c65581310061e3a0cab026200c3f65dd1604c401878cbba2c0988031bd9772581310063632ee4b026200c6f651c9604c4018d8ca392c0988030f9d365181310061f3a0ca3026200c3f655d0604c401878caba0c0988023ee1d60181310055c422c03026200ae882580604c40193886ba0c09880327e0d74181310064e41ae83026200c9f325d0604c40997100ba0c098803275d343181310043fc2ae4302620387c855c8604c40153908990c098803275d132181310056dc026430262018dd878c4604c4015b301188c0988032e5d340181310074da1e803026200c3f749d165c84014bf06ba2cb908029720d74597213dd37c12e8b2e420ba6c825d165c84018bee739acb9082e9ba0a73597213d536c14e6b2e420087e87d0d65c84010fb0fa1acb9082e9ba08435972100536c1086b2e4200a3f845c565c840147908b8acb9080297e0d71597210052e41ae2b2e425da6f825c565c84014f700b8acb908029e20171597211943f43882b2e420087d8710565c840147d0
  | 17 => 0x2640087e87d95604c801878e9b2ac0990021fa1c65581320061e3a0cab02646a8bc86dd1604c80187ecbba2c0990030f19774581320045f43ec8b026400c3f75d91604c801878ebb22c0990022fa1c64581320061fba8c8b026400c3c75191604c8018eecbb8ac0990031d19771581320065bb26e2b026400cb464dc5604c8018eeca38ac0990031d19471581320065bb20e2b026400cb4641c5604c8cf938e6320c0990023ee1d60181320057840ac0302640087f855c4604c8070f90ab88c0990022fe1171181320145e422e2302640387e87dd563904018bd07baac7208031760f7558e410043f438eab1c8200c5f75d4d639040b1b90ea9ac72080317ddb7558e410062fbb0eab1c8200b8c825d1639040173100ba2c72080297a167558e410062fbaceab1c8200a5e871d563904018bd0e3aac72080297a167258e410052ec2ce4b1c8200a5f855c963904014b90ab92c720802a7e117258e4100727a94a4b1c8205e5651d4563904014bd0b382c720802976167058e410052fc2ae0b1c8200a5c855c1639040153f08b82c7208e6a7a107058e410054ec20e0b1c8239c9f7658d439046717b0db8a872099765dcf7150e410045ec30e0a1c8200c5e7598e62904018baeb31cc520803179d56398a410062ebaac73148267c9c7498d62904018deeba92c520802ab6135258a4100c6f41ee0b1482008dd83dc1629048393cc6b9c8520803a398a6390a4120d4fc32c7214825c8bf865c6429040117b0d38485208021fe15764ca4101c3e42aec994826cc5e63dd5329048393cc7ba2652080317dd5634ca410062e3aac69948233c9c7458d32904053390ea1a6520806a7e19434ca410064fbb286994824bb8c8250d32904010ff0ab94c12080e1f21572982410062fbacc6b048200c5c7598d60904018beeab1ac120803171d5635824101c3f43eeab048200cd8631c163504071df0ea96c4a080237e0d70d894100c6e41ae1b12820bc6c625d662504018daebb14c4a092f27d91731894100477c3ac4312820387e859d932504010fb0b3b264a08021fe1573d814101c3e42ae7b028200ab9840c360504011f70eb00c0a0802b620d60181410145ec3c823028200ab980904605040b1790eaa2c9188021fe15729823101c3e42ae530462008ef825d5608c4171d904baac11880a2fa1372582310045ec26e4b046263a5e83dd3654c4014bb07ba6ca988030f5d074d953131d2f418e5b2a6200a5d831cb654c4018dae4396ca988021fa1c42d95310043ec3885b2a6263a5e8310b654c4014bb06216ca988021fa1c41d95311a43ec3883b2a6200a3e841c3654c40147b08386ca9898e97a0c70d95310052ec18e1b2a620087e87d03654c4010fb0fa06ca9880387d0f65d91310062eb98cbb2262058dd83dd7644c4010ff0ab86c89880e1f2157
  | 18 => 0x8011f70eb00c0a10022fe1175586320145e422eab0c64028be87dd1618c80193d07ba2c3190032760f745863225e4f996e8b0c644bc9d32dd1618c80193f06ba4c1190032720d74982322864f992e93046450c9d325d2608c8010ff0ab8cc11900e1f215719823205c76412eab046400c3d741d3654c8d94bd063a6ca991ae9760c74d95323652f418e3b2a646ba5d831c7654c8d74dd0438eca991b29b60871d95320063ab88e3b2a640087e87107654c8010fb0e20eca991b297a0f70d953235d2ec1ee1b2a646ba6e82dc3654c8d94db05b86ca990031e5c070d95320043f43e81b2a640087d87d03654c80187aebaa6c89900e2fe1d54d91320043fc2ae1b22640387c855c3644c80187aea3aec8991ab8b94b52d91320051f42ce3b226400a3d859c7644c8d553b0638ec8991aaa760f70d91320051fc2ae1b226400a3c855c3644c801878c9baac8990021fa1f65591320043f438cab226486c6f72195644c8070fd0fbaac8990022fe1175591320046fc1aeab2264008ef825d5644c8010fd0e3aac8990030fdd774591320061e3aee8b226400c5c75dcd644c8018d8ebb92c8992170f9db65191324270f39eca3226400e1d73d94644c909c3e63b28c899213870c365191320045ec3cca3226483a3e85994644c80117f0eb28c899002a7e0d651913241557c12ca3226481a3e86194644c90187cec328c8991fb879cc65191320070eb98ca322647ee2f32194644c8ffc3c64328c8991ff870c865191323f716190ca322647ee1f31194644c8fdc3860328c8991af171db6550d320070e326caa1a646bd4c72d95434c80553d0db2286991ab271db6450d32356c6396c8a1a640b9ce87dc9434c8d5b1ee83928699197271937150d322d64e320e0a1a6441c9c73d91424c8018b8cbb9a84990030f9d365985320061f3a0cb30a6400c3f655d2614c801878caba4c2990030f9d764985320061ebaec930a6400c3e75192614c80187aea324c2990021fa1f65585320061e3a6cab0a640087e87195614c801878e832ac2990030fd9774585320061e32ee8b0a64008be87d91614c80187eebb22c2990030f1d764585320045f438c8b0a6400c3f75191614c801878ea322c2991f72bdc864585320063db2ee0b0a6400c7865dc1614c801976c9b82c2990032e19370585320063db28e0b0a6400c78651c1614c801976c8382c2990032e19070585323be2eb98ca30a6467c9e73190614c8011ef0eb08c299002bc20161185320043fc2ae030a640387c855c0614c80117f08b80c29900a2f21170185323be2eb98cbb0264018ed82dd7604c80187ce9b2cc0990030f9d065981320061fb2ae93026400c3c655d2604c80187cebb24c0990030f5d764981320061f3a8c93026400c3d75192604c8f995ae4324c09900e1fa1b755813235c3e436eab
  | 19 => 0x400400000800401001800e02802c00200000005800000200801200400000000604600c00400600400000a00000400400000003200200c00009a02201c00000801400a02003800600600800a00014e00a01000202800800200004200003c00200400e00200000002600200e00401600200000c00c03a00e01600000201a00800e02c01400402402c04200400201400403800000006a00601e01600002400200200008000601001001400402400800e04e01003c01e05200000a01200800000600602e01201802000001200600800a01800600e01400000000c00000202201803202c01e05c00600400400602400201800802003800400611e00e01200406c00200000a00000600001e00800c00202401800a00000603a00402c00800001600800000000000200600200000a00a00000400000601c00207e00a00200003e00201e00602a00000801a04e00200000600400404a01000200002201e04c00000601c00200600004208204a00600600201401000202a01203600a00001202802600008400801601600002600001400000800200605e00a00000a01600401a01a00802c00001600800003a00400000000200400e02c02000a00800000605a01c01800800a00600c0020040040020000580000000000000120f001600e00001600001a04200000001202e05400600400003201200003400000000001401205a00000400c01c01800004800000000a04c00000000001a00800e00200601400a00801200200004200200001600000a01e00c01000202604000200001000c01600200400001e00c00401000000e01200600004000200000800200a00000000000001203c00000200c02600001200402600000800000800000201e00000e00000200601204c00000200601a00007e00a04002c00000000402400000000000001c00000600200400200200400200000600000001000000402400807200e00400001e0e200400402200000000401203e00c00200800200000c00c6d75d4b6250c010ff0ab8ec4a180e1f21571d894300477c3ac43128600a6c855886250cd555f08b10c4a18062f61375d85430146ec1eebb0a860087f855cb6150c070f90ab96c2a1a23355cf61985430047bc3ac230a86008fb875806050d0f5b706b00c0a18021fe15721814301c3e42ae4302860087f855c46050c070f90ab88c0a18023be09711814305c76412e2302860387e87dd5639080187ee9baac7211ae1fa1c7558e420061fba0eab1c84008df835c261908031b906b84c32100237e0d755864200c6e41aeab0c840087f855c660908070f90ab8cc12100e1fa1f75582420062ebaea7b1a84008f78758461508010ff0ab98c2a100e1f21573185420043fc2ae030a840387c855c061508011bf06b80c2a10063720d70185420043fc2ae7b02840387c855cf605
  | 20 => 0x400d8068ff80e936a1d3c7440e816e263c96a26440f86014d66301aba7b52be0c14ab9dc944a3194c21d68ea41261b5a160f9e31d4f98de88509d22c910140006890cb9d9494806a3049fb0d4439527488fcdec625000077476c0f01d994bc0004ef333828d1ce43e0000f2c41600014c0a94dfa06f00000004c04a62510cb5300000122800021e000244093125884e03090440008480ba936c00055a00005085d034a4f224042545890002164a362e41ee8f3929c0bb3052190156a505258a9c0005090ff00000009291ec8e9028200052a158500293f1f98b18efe73920001190843d53fd80000006ee46ca3b40000002289f60b3e08600010185fa8c52100040e6e000023a2c80000000001f7400033030000000005e51271a6cc5004f0d9886c4961fc4e419645569f84741888cc60a20380a012f87ac00019ac0000000fa00014c840200000003f400000025c80000004e106880002e72bc19d8f2095013f9c3cec65542d500e85b649023a8b509b81204d6208c2140003578a6931c39610f12c09362de2188ac42420202389c2cf4418417c1e4802001002000400000001200200003c00202601000c00409800200a00202600000400001800800602000200001205e04401000000a05000401400201401201000600000801200400201200200000000c04600c01000000402400600207801a0a200c07003400c0040140040180bc00a00200c00406600000000600c00200a00600401c01e00c00200003605600208800400201402800200403801403c00000005000200000206800400800000207600602000400a00000600201000a04c01e03c00000200201000000003800e00000200000002c01000803200000200600a02801002801000000000000600a0040000000f400800200a00000800000a01205c00400202402e00c02206607c00400000600200a00200200800803402801202200a08000000401c00401604000805800601803001000e04000e02800400000000202601000c01801801400001201800001607000200001207a07c00000201000a00802800e00401c00200000200000600800600200000a02003800000001a00400401401e00002401001200400601a00001400600801003000c06200200600000001a01601001400000000000006800201800201e00400200c01a00206203800800002400c00e00000003000404e03600000000e01e02c01000800001400202200205800200800000c00000200000400001601801403e0000040960ae02a0000000000020be00600a00600c00400800005601e00000800c00600000c04c00801e00404e00c00e00600a00000202c01600404c00001400200800600203200002000600001200000a01800800a00800a00200e00801000200000000000400400000003203601a01801002e0
  | 21 => 0x388ba8d336304d40d0435315a4cc60a3091ea09949807a33e71554e260af3f207a443895a03c9b902686a71ed899d2a62181821d4444447824d0ac80005334f7a258d5000000028b00007c90000e08f600004d506e84da00024606f42345ff208014800037f000267c43a0ad3cd039089c20c00010b05dc34c00027dd3406a623480002fc00003e80001c698710f80000ac000293000000016e2df07c00008ba0000628f0267700005e0000802000286c9e600034500007224210000efc00080f47884440000003200000000432067a4d45c21f74901a2c7323c723f99b40006805031fbc3767174618b801160d74780b342c05d200000000000003cd9ac8c86813324910010e32a3d899045945462368419332a2633903141be0be168a3d87f24332df821090c9d426c1a8148a69a4888e044e03e923e260465c03524f952075a2fb1b0172c4fc7cb20a00005822050ca8000e3a8dc25fa6d43e63ef21a08ac7347b234e14c90060a92b3a074c4e6952838c50026a410a600014703d31940f053441620fd95cd0fe7612f18001130000000033800032f004a40cbf8a372c385a0ca457452902700007d200026603c462f50e000000044b00015880001ea0000bb01ea0002ce1b040009ad2c427300000002f70b54d289d51948674f827e60f71b709ca62e366023885a3490aa105c2c808847a9cd49407ae000187ceda4c544e076c056a4300000000009f5000226c45092d0699ab445a000000181c0000000000000fc42272fb8ae54ec5b94ee97f471800000c00014346df2d48c7c9f000041b1d4c4928d100027a9322537362932c5366b64a5951098e25d1ff90f4f188e5356000084865d07098f8000a3b11e000067c5ab2a515fc41e6eb07fa5f4000000382800022e45b45b000109639b311842d198865000096c5869c13868a541362c00000000c1e0000002090aca3714ae00008ae21a3161788eb0a0a0ac0000cc86f233825ac0003324408d8d4044530b9a2e000007741d060d24641c31500000004e34b0a6f939673f4b31ed51fe73c4d708c00000001388000714a5a2889e704e461100c8820d940003c121e107265f2730bbd2b0729249a93c1f24820d81be03ea2b74828c4cf9034b4f38000fa83d84281de800072c00000000706382ef0000b909e20761f78000000000070cf4800024b05480000003821c187987711efa0cd1f61f2098929c71a39e00000002d68b50b517c04325b2147a3d09e82fa35f80000003f8223000000038639d800092e9bb45001f83da193000269400000002e0a2cd9c52c26f1fdcdba925192800000099751c800096234f276a42c0007473df82d06683a01488ccc0003cf50e9d6ca9280530f1978f727491ca22ecb747754ce884d30a5a030a8464d7c7e51f6a08429e8ac43d95c43b043812e075cf1a37
  | 22 => 0x8024f00000008d500000000000004b9800057e2513718001352a5600014340da9f42bd804400065851689b0ee82013ea98803eca5721109a895a0003d38d786b227a0ef1e548f412506e9c30a7c32b3d320806b4000363a5fc4dc4ab0d922344c20000000cc4ef207a4aa8001326924000000052091c3c8a1889a85b42da815146c95e46d039c6c28851210ae002808f460140086e6884ef17907d076415aa4e400077343924ecb5877b4611e5d3d211417106252f40bc5250678c2c8be50a89541dc82b2fb24653709760ac8cfd24218e5331eec95e2bb20c94e09d473e0f5844cd807e90d41db091606c0d4a2383be4a816289a0ad611b06b1ad05da4f9316929412c0691a0292498c191209a17ceac86d33302784085f30ca04b40ec2df0aea3cccdc4831509d78a1442f4761968a840f226d24484460bf1ee28648023e01a425e4a9636537a1d2834a19f4d2029d2dc1e1381a2ac0dc9c43bc19a400047b44f96754c69641fea1107ac0003799d0800000003e24e889490d35a9f6c9e223d33ea8f42f60000001d103d000000000010fc0000001fe4394262000194cca24161542424b9a8df2949d2cdc0a0d3eb1a841127b32b426508ce8cb0000108b1a043141a6d850804911b17248d07b6212915412299500017f820e0001089cd142000041a13844520654eb800128220339580000008170001709284000000100cc347384981bbca321f1431a9945881d4301017cab2209084237466e569429040c00807513c1b24c6e00c309800023036e3760a806ec56e4eda3911329284b41a14b8809d52022f54a230100017b0ede000163a020fe64f226924a842c35616c235d3ac82905ba6c800071b0a381354106d9417020c23c60649b951450487d0e80bc89703bc0dc000000031819c15700000000000fd13dc02c3eca9c45e0055403008cc98719530073062e0ef0e58f28c7252e48400044e63fc224866104463f08200013f61480b30228d5286f3b70000f1400031e0ee947e35018d8f00bcc0a03ce9ff40000000001fac10a0002af20012ba0004631244bf46d22ed033096e96d38d14a09ae7be50a26bc0006b7531185079269202890fc7dc38f436036883465c0499ea92ee00021ca0f883a9474f29c1cb2676227f8cf14462f42859a4c6b0701489a9c015c0782d80a8c7a00a132d9edc3024890e9091875c016066870005c71127703786b60a54cd8b3cafc9a730697c92ce0b51cc0bccd2c79f1c198cd4e483119c9f34b4e39011ca9743160d219a964412e52532588806f62470621d30e8631c121993c49036c04f955c044510448a2f0004a5b5019cf4d3a54315f0e2419074d22c82049841d9168009545405033614913784f74bd98e8f2630c2d715d4e000825211c40b7045f0b89c4825e6e139408192a85970b793d42945e85181d
  | 23 => 0x112e000281800148e01f23618d4d6679429892640005d61879c50a9c7761ce04900005cf1960000a0c0000391f7c0003770001be80000000001048d785f851e09f434693e000000000090400000011dc0001bc86b0dbc88615813040000004c316ec40064e448289cd1e0000a191792b64260f184f097ca741250e84a028111900e4cf2c5841449840a98a5e352974ce6c4634bc000107e7d10758000de296300000004ee27631487701d46170178bf81540000d50790552321108000124c8a94fe8594c3687505e80013a676a1aa17c499a3410002830e600002c1000001600014f11e40003e11eb80000002bd000269823a8430000d90000000000000000000042d974000056c0001b451e41d5517a68cdb04c32eb95489c0a17000000099c3470000ba4cfc03c27600003046b10000b2519c1a13e50e9505e000049000034c000115005425628e000121081014e000075939c9483902130a3800038e000123e3e5242a0540005360ff8b940001501ce95e8e043c83108a150bc7ed3669628e44287429831936072e0002030e143c529ea7d8f520440db80011c482a00011041ee92e1f58f8800028a2e000000000b9445a098bd400053a8000d843f02c6000000000000011d07d48a2000000000025a4b480000000002db000009439f1599be477c1c72660000a286ff1db8ed141e0c71a98d554de4f04f8a73400038809d2278000a593c587208b007100028d538062418b20c941615c1d40000f4a7ab00000000006912350e10b3612e000000129a27411d1c78c8e74504d16a0a188092280000b3c00040698711625201b3856ca2e5bd00712a83f00640598578ade10904a0b207763b01d78734ce818f3e214200607ba1a697711f090e04600c47529b31510bfd0e28951f203ec59600050000013722251c284dc332671466a6dc0003430b600000000000001e14cc27f4000036c46605847321d8096541000063081c76817e27994886cb000000000000000280013c69f05088c78dd015319200fd0ae82700008c481a68e40c00010e800000019e4c7a76942a960c7a29592650cd80007570d6a350ebe5eb230000072e0000000f0ca089e800526250b42f93e6032412a6e9232a23cca098322d20dc0f61da29e02647ea01c4ec24f00005020131a78000129405a25040400015b2514b5a0000dc9d9ca1c5f522900000008c42599e0d32419b0000da437c8771291660eb21e6441110c0002f53908a04000a2010a03700ae5ce459a040b1e0003750260bf272300024882fe51f1e200000a600000004cd4ce4ba03f939d18e1b6000156cd3290c126800032403d00000005e210e27419a800019608000010344d32e50200cae590503800026029f20780006763da0bc8000b2c89a11da938d0c00009b27400006cf2710000a5a0ca2d89fc460c3
  | 24 => 0x98a180071830c16928a9d192e82ad000278478c74824e09d51de5790e98000a80a6a0d59310cac5a310b80190cc000000000000058601a25246848b421716949a26ba48a80000001510001f68e626e64efa12489a5c30001b4cf1c6e500002b14be6e707f1c5427e4272bb249c00056d00ba13c00048d517144c7d8000420000047c599240000004e7c500007bcdc425014ba44091e7b814c8a9938c2a43518000e661c929a032d3d68eb5361560cca6120001e10cf82c2341a4d000069000013e881203e2ee8ee0bb254f1b300744bc8a723f168944471f11908344f281e2be15802aa04e4169f9c072244250a7fc50c00043824d80000451ff246d21e2264fd00012c09b40000fc81da472407202800090a3fd278067a0001c5901c99e45c1bf05c811a30331900001f43e331d911c0b253b46d937cfe03fa4250ea86748e10710ab0a2c55147507111122d323b8ed51929c34421bb42da55f2de10c01f01490541df41a88ca146195062a9652828dbcde07e33d0800131072f4b81a90a8ea4d10928c502c00051919154560004d4000075613b28f25bc4b03224c584410324ac0da20482181c11fda1b904a83b01ba37889018d1bc240095234e33d1a0429666025907440481f945b8d710288e04cf06212ea72427202e8b3452746c1b112c40d83f423f839ca463c4002046e4f6146913cf5e8e308b001d2a4000392800000010d4e38000a9a52328e819c688000000000092a88c2f78af000074142396005684d91050364dfc8fc435a21d4420001d8a1443ce000509a6fc06477c0000e48aac8832331a088e06fb4ab22c0bb6a581b4118943c02800006906ba87307e9f000527c700025185ae0003840d7c000835433800092422c48d24c400079e4e52838e2c15f0001b6800000000022b53a250f000122928019c00004086a40001d3a54503668d44e8838c9a0000c828a4ce645424e9a1c00048720600000000000da91acb2a6f74dd21142ac05b4d59f5cb4825319399214e69cf11a1ddcd606684451c3890217a3aea4743785c70be85d0ffe0000001af464c00014901ac08047d3ee0a4cbf64444520dd423e5a646417141cc5b71fb19bca44755474a1f04b2a5c1b81814c169d9000000068a0002c2958c4d68683939f1800000014ea2a092800000005f08780004cb24e0f3012c000000000000000000000000002148c1c2508f70001f40cc41402518c68d5673211081746da37c27f201c0c60a43930d44f683083bf051861698d006873c0000d517b858416441802d22e54985e032106c45ba6784ce15f523c4b450204c82ee0483de27148361a051220e01802562d98000c4c0004c626f41840004cd18745ac0002b329201e800002095910c02d923201cc000a6d32aa15845c75c2309e3cd7676642a00000002882f480005c64b62260
  | 25 => 0x41e20508d522c4c84fc92386469fe460a0f0dae2aa36b183830a0a600004880064bd030093c61c7991d31b40a723621de834497200f44028043340e51330eb09f67d33a814fc9ba5c60e102e10f246f0829a7ccf68881ef0c492866984d8a685256000000224d3b86c320a80010ba3b2000276895c00000000012887e02c594480006db00900ccd5443b3460b3927a0003f70f3400000036408900760000001f0c00053507996040006440df80000000000d79f08fe486a0000001204144093a1842ae2d2181000125e9f2000234005a0e04c8233c20200033fa7240005721d1935546625f2d0a2bc0000b1000108c00087a0f028f89d68bf0b811b8aa640b0151ea12985e72f6800034e84d0000000bbe0003d698d035c000068000000025710aa5c4c1883d2fa1ce8fec4d02c712f01f86194c119d4b9843a00007f400000043480010388f91b9048c00000013da8604a8a05416058d47496a452954112401e24c2104daa8a630094e878491707b0000000000504a53d1f45e127e170546884600000007e200009e9108f4027c0000000000a1f2bb8a58c0659430c0ab920e94a14a0000160a6917b0dccee00003950ba88563d20000000fd42e60a2946053811534b81889ac1763969918120a6e52982d94500002981c24ba88fd0000b30c6c78752a861d3d840411c23484806ae01b1bd40007f50000000c087bd2e89ae40003110000000ed60000001fe00005d80000df4000906000000000000000004e00cc000534000000051a2b5079418697e08e13f47cc57002f081c4c626948c1e180005d540200000000000001d0106000050b00000008281c391584de00042e0c4083e4bb21b1484ffc42a3421928e304763f09d804828d63c48c34a543b91b501d000004c09c9ae01e28a115d044915c780185228c00047317598c43d8a1209f27f12d80001c700002b46fc26480847ce22f0e2982029a9322958fdc000a6148a1114aba16716d0abd1547541a30000b5e
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8200c0e0604a703fd8324973194644c8cf09c98dd9434ca41006261d080591324c40109d97211321813100427261744c8604c4cf09c981d9434c94000427a5c844c9618c00109e98dd13258630
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x2
  | 6 => 0x4c
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x124e
  | 10 => 0x138e
  | 11 => 0x3
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124c
  | 16 => 0x124d
  | 17 => 0x138c
  | 18 => 0x138d
  | 19 => 0x8c
  | 20 => 0x8d
  | 21 => 0x8e
  | 22 => 0x128e
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128c
  | 27 => 0x128d
  | 28 => 0x150c
  | 29 => 0x150d
  | 30 => 0x150e
  | 31 => 0x9cd
  | 32 => 0x9ce
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xa0c
  | 36 => 0xa0e
  | 37 => 0x130c
  | 38 => 0x130e
  | 39 => 0x20c
  | 40 => 0x20d
  | 41 => 0x20e
  | 42 => 0x140e
  | 43 => 0xb0c
  | 44 => 0xb0d
  | 45 => 0xb0e
  | 46 => 0x140c
  | 47 => 0x140d
  | 48 => 0x154c
  | 49 => 0x154d
  | 50 => 0x154e
  | 51 => 0xb4d
  | 52 => 0xb4e
  | 53 => 0x144d
  | 54 => 0x144e
  | 55 => 0xb8c
  | 56 => 0xb8e
  | 57 => 0x148c
  | 58 => 0x148e
  | 59 => 0xccd
  | 60 => 0xcce
  | 61 => 0x15cd
  | 62 => 0x15ce
  | 63 => 0xd0c
  | 64 => 0xd0e
  | 65 => 0x160c
  | 66 => 0x160e
  | 67 => 0xe8e
  | 68 => 0x94054
  | 69 => 0x94056
  | 70 => 0x124956
  | 71 => 0x138956
  | 72 => 0x98096
  | 73 => 0x141296
  | 74 => 0x140096
  | 75 => 0x148b
  | 76 => 0x128996
  | 77 => 0xb0996
  | 78 => 0x98b16
  | 79 => 0x154996
  | 80 => 0xa0b
  | 81 => 0x134b
  | 82 => 0x151296
  | 83 => 0x180b
  | 84 => 0x10c
  | 85 => 0xb49d6
  | 86 => 0x180c
  | 87 => 0x1452d6
  | 88 => 0xcd2d6
  | 89 => 0xa4c
  | 90 => 0xcd
  | 91 => 0x168d
  | 92 => 0x28b
  | 93 => 0x155416
  | 94 => 0xbcb
  | 95 => 0x144b56
  | 96 => 0x28c
  | 97 => 0xccb56
  | 98 => 0x184c
  | 99 => 0x14cc
  | 100 => 0x2cc
  | 101 => 0x16cd
  | 102 => 0xe8cd6
  | 103 => 0x40c
  | 104 => 0x58b
  | 105 => 0x188c
  | 106 => 0x178b
  | 107 => 0x17cb
  | 108 => 0x164c
  | 109 => 0x44c
  | 110 => 0x170d
  | 111 => 0x24d
  | 112 => 0x5516
  | 113 => 0x5856
  | 114 => 0x14b
  | 115 => 0x9396
  | 116 => 0x9416
  | 117 => 0x8cd6
  | 118 => 0x9896
  | 119 => 0x5cb
  | 120 => 0xd395
  | 121 => 0x141556
  | 122 => 0x154cd6
  | 123 => 0x155896
  | 124 => 0x40994
  | 125 => 0x41414
  | 126 => 0x44414
  | 127 => 0x5c593
  | 128 => 0x45614
  | 129 => 0x41654
  | 130 => 0x41a14
  | 131 => 0x40454
  | 132 => 0x164414
  | 133 => 0x165614
  | 134 => 0x45894
  | 135 => 0xd2d5
  | 136 => 0x16cb55
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2142
  | 6 => 6446
  | 5 => 2679
  | 4 => 8
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
  | 7 => packedAt gbK7 (88536+((h/714+packedAt gbK7 (79254+(h % 714)*13) 13) % 4552)*13) 13
  | 6 => packedAt gbK6 (337332+((h/2148+packedAt gbK6 (309408+(h % 2148)*13) 13) % 7736)*14) 14
  | 5 => packedAt gbK5 (168777+((h/893+packedAt gbK5 (158061+(h % 893)*12) 12) % 3215)*13) 13
  | 4 => packedAt gbK4 (568+((h/2+packedAt gbK4 (560+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff80fff007c07fffffffffff473e3f8ce07fff
  | 1 => 0xffff01ffffff807ff00fffffb8c7c8ff3f8e3f
  | 2 => 0x3fffe0007ffff81fff03e00c0f9f0f3c3f3cc
  | 3 => 0x3fffffff8000001ffffc000ff01ff03fc03f0
  | 4 => 0x3fffffffffffffe00000000fffe0003fffc00
  | 5 => 0xfc0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa5001650814034b2551462aa031a13846034d5
  | 1 => 0x488b00a62a928044a08a95541844c8390d8a2a
  | 2 => 0x22d5aa0124eb59013ea23806c0a970d382d34c
  | 3 => 0x43e6cd3bb00a0c11cbcf1018ed01ed03f403b0
  | 4 => 0x8378f1cdc73c6e7803040060f7f60002fb6c00
  | 5 => 0xf040800e003070600c082180feffbeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37481
namespace PEqualNP.Outside.L_meta_37481
open PEqualNP.Outside.L_meta_37481.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bgb_4_0 : Interval gbAtlas 4 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 8 := bgb_4_0
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
theorem bgb_5_2656 : Interval gbAtlas 5 2656 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2679 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))))))
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
theorem bgb_6_6432 : Interval gbAtlas 6 6432 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6446 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)))))) (concat (concat (concat (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784)))) (concat (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200))))))) (concat (concat (concat (concat (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584)))) (concat (concat (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000))))) (concat (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))) (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384)))) (concat (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))) (concat (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800)))))) (concat (concat (concat (concat (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992))) (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)))) (concat (concat (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280)) (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376))) (concat (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472)) (concat (concat bgb_6_5504 bgb_6_5536) (concat bgb_6_5568 bgb_6_5600))))) (concat (concat (concat (concat bgb_6_5632 (concat bgb_6_5664 bgb_6_5696)) (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792))) (concat (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016)))) (concat (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat bgb_6_6144 (concat bgb_6_6176 bgb_6_6208))) (concat (concat bgb_6_6240 (concat bgb_6_6272 bgb_6_6304)) (concat (concat bgb_6_6336 bgb_6_6368) (concat bgb_6_6400 bgb_6_6432))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2142 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
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
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
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
def fullWord : Sig := 0xeee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888eee8eac8ece8a888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241864 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37481.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[2,5]⟩,⟨.or,[0,7]⟩,⟨.and,[2,4]⟩,⟨.and,[1,4]⟩,⟨.and,[0,6]⟩,⟨.and,[1,8]⟩,⟨.or,[3,9]⟩,⟨.or,[10,11]⟩,⟨.and,[13,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241864 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241864 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37481

open PEqualNP.Outside.L_meta_37481 in
theorem PEqualNP.Outside.L_meta_37481 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241864 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241864 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
