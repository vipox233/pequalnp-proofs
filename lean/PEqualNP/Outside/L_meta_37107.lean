import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37107.Model
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


end PEqualNP.Outside.L_meta_37107.Model

namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
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

def SBf (j : Nat) : Nat := [7, 6, 6, 5, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37107

namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x110008b0f8c4e4c003362831e4c0189140208175e70a15484800f2c018000000000008400200000005a1c4a80ab8e9a322c00030946aa56a51811c1e1c101060428114003042a24200ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4a0c800008d00000d80010001060000000ae000380128433500000491d800cc5a1f2604496000000006000b42852311801e1b00000aa0051010e8364b80132794a9fcbc7348054003a188d48e4b00070009b1a058422316000002a0000000002d800007d3400000420700000512c9bd0c000f8744e0d422144c9f000011c0020800782f120011800001311232048c010002e8e45013240000018280008017001d4f44f051ecec12000152601478fc8c9238270209d3ba2d027c3915822a0521e0c287270f418a1228a4340332a780491269b8b8820599cc65451990d6331717d3437400acda53129107088001a4b07e451c43c000000010002890e00000006800001000f038c028b810506010080010004029608008886000101000a80000000800002850609828c8380804f94b439ea8e873e50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e7ea2a1cf141439f2a0875e53d0abaa7a14f54e429f294853d5190a7ca12157d4d42ae29a853d5310a7ca4216b948429ea88853e5010a7ca9994f55332d6216653f548ca78a91967d0e32cea1c659f548cb38a9195794a32cf214659c428ca7ea8994f151329f2a0653d540cb3e86196750c32d6210659e540cb3aa8195794832e729065cf420cb3c84196710832e6210658c420cabca7a0d754f41cf29e833d53d073aa7a0c754f419f296839e32d073865a0cf943419eaa4833f5350678a4a0e78c941ce19283b75150678a0a0cf950419f2a6633d54cc67ca918cf55231cea1c636e528c6daa518cf951319eaa2633e540c67aa818e750c319faa6433c54c87986590cf952219eaa4435e53886baa710cfd51219e2a2435f53486b8a690f30c921bda824378504867ca810cf550219ea9c813e529033c6520670ca409ea8c813e50902bca6205754c40cf298813d531033aa6204754c409f290819e321033864204f544409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ca9104f55220af29c415d538839865104fd51209e2a2415f53482b8a6905dd4520ba28a413f5408278a810730c8209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x76440222abd5363e2800f0c000ac00d002d2c9c025407149800d4b8270411b12478693166930e48e590308dd5801201d004274407666540536018000031700281e000080c20584060010d0c0408f0004000c3d4c5250f0f631494387d8d5190a1d63942428d584548ca8e62d5232a3988548ca9561152328b594420ca8e6290832a3d94420ca8d6510832a3584420ca8e60108329318953d062c6254f41a318953d070f6254f418718953d070c6254f418318953d061f658cb418759432d070c520c9418758c505068c6250e31c350e528c61d63951318b189544c6386055131a3189430c61d6315321c315032c870c540c921d20c8504861d6395021c3948329021f635464093189531022c6254c40a3189531030f6254c4087189531030c6254c4083189531021f658c84087594321028c6250f308b98b548c21c6550d30a3189434c30d4314930c550c514c21d6395320c3950328821d63150208d584540830c540c8208758e54c421d6315210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x4004800820cc0000a2380428338ec629287215c76510832818e4b18a0a0c0c7258e5408607396c6a8c81411c9431453081aec2a06410505711503208206392c72a621031c96315210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (912+((h/16+packedAt s0K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s0K4 (4895+((h/55+packedAt s0K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s0K2 (502+((h/3+packedAt s0K2 (490+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 3 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1105108c412248100594a8a25012915414d0d5
  | 2 => 0x248a29103244942960294454a6412aa8ca262a
  | 3 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 4 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37107
namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x986021500100e010bf42bd42f731de31dc31f431d431be40bc40
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xc0a000802006e400ab28c6396540c72aa818e5d0831caa106394319025aa420650c440
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x100c020a158a540c61565d0831855943110305520c440
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
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
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (156+((h/3+packedAt s1K4 (144+(h % 3)*4) 4) % 11)*5) 5
  | 3 => packedAt s1K3 (224+((h/2+packedAt s1K3 (216+(h % 2)*4) 4) % 16)*4) 4
  | 2 => packedAt s1K2 (156+((h/1+packedAt s1K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 2 => 0x80fc0fff81ffc1ff0f83c1f03ff87f81d2ce7c
  | 3 => 0xff000ffffe0ffffff003fe003fff87ffe30f8f
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8a10002304008000118442118a0088940450b5
  | 2 => 0x262996451ca512cb06a1d1a296c8550cd2c65c
  | 3 => 0x144aaa88286a31556042b48425550669630b0a
  | 4 => 0x58b34d125143a5a6bb68210939a66031bc0de0
  | 5 => 0x60c38e1c618c39f8cc7339ce01c44441fba000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37107
namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x8a1140849c6009800580020000de43dd43de32dc32de31dc31f721f421df30dd30f710f510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x110030aa28a871d540ca3aa9985914910
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf80fc0fff03f07fc3e07fc3e07ff0781b3b3cc
  | 3 => 0xfff000ffffffffffc007ffc007ffffffc3c3ff
  | 4 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10a10804608221004628804a31484c94141615
  | 1 => 0x32629948a3942b2c1aa3a42c52d9450cb1b2cc
  | 3 => 0x4144a2910528845581054a8084a2926942c16a
  | 4 => 0xe58b3ce24a0eb79aedb06229273ce431fc03b0
  | 5 => 0x860c30c38c30c6e331c67331c0308041eb6800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee00aa00eeaaeeaaee00aa00eeaaeeaaee00aa00eeaaeeaaee00aa00eeaaeeaaee00aa00eeaaeeaaee00aa00eeaaeeaaee00aa00eeaaeeaaee00aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37107
namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
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
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 1 => 0xe07e07ffc1ffffe0f81ff0f80ffe0fffb3338f
  | 2 => 0xff8007ffffffffff001fff000fffffffc3c3ff
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60128e390990c14563c
  | 1 => 0x4910ca448ca28ca06a8a90b124b28a54b13285
  | 2 => 0x842514891144114d04152a02494524a942c15a
  | 4 => 0x1659e7122876de76b6c188a48e79c831fc03e0
  | 5 => 0x1861861c31871b98c719ccc7006100c1eba800
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae0e0c0c0eaeaeaeae0e0c0c0eaeaeaeae0e0c0c0eaeaeaeae0e0c0c0eaeaeaeae0e0c0c0eaeaeaeae0e0c0c0eaeaeaeae0e0c0c0eaeaeaeae0e0c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37107
namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8ee21ec21
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (34+((h/1+packedAt s4K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 1 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 2 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 3 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x6108023084001004404c048c6024621801515c
  | 1 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 2 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 3 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37107
namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8437c53086fca410fbd0821f6210437e51087ee8210fd10421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720fd98641f830c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620fb28c417651882faa3107d54620baa8c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f719241ed32482fea2905f14520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea88417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd20421f940843f661087e0c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ec62887d4c510fb90a21f421443f480887e50110fd98221f830443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1fed4143bda82877c5050ff0a0a1de14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0df14d41df21a83bc43506fea4a0fbd4941b7a92837c52507d8a4a0db14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41bea98837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf28463fa508c6f4a118df54231fca846379508c6fea898df95131beaa2637c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f6214437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea9
  | 2 => 0x17a0012c82f1ba0d8298b44804ec2610e000220000b912a000d09f40000ec769243980007408326c2e00000429e000f78000001ec00000054000000c100000000000000830eb93316e674c009138837c3c8411863847617f3d8838a71743f41bc8b058236864180cc04c875031ff49249800161000224ec800000528000b2000000ac0e9000794e919415c5f4002054c832cb398c1de4a8b88060b40010e00a28240d2b0000a4804fa9e738e0000f0002de088a3800290000000000005750b8000784450117719a24cca8504c04d44ca391f00000008a30e740f99c90f8460560444a24e9080fd2527acc70af3721cd171903be4280e1aa2502f04680c31e39cd78d413487c680430ec7b84000d344170cd9c3258108038d50d84fc2525b0ba4c842846450940628392600a00020f00095c4b21b0000000001521e0380021333c9941b8000000004d8080d634511800000274c595c02e394c1a540006d4e51dd3c65b03f181000000500001440012a87507e6a43c000234768881de1928587f19900a430a986d052508380d60ca6a0122614349043408b442000509962a252d330d72b60004c00010c6e00023c1cc5a11882e2d2910ad150414000001dc12e670869a03083010c0000005f8f522a0006d8e29e200019d1a90507c368079783340008380040e500ed890408295069213da9747813c0ac4bc971e837a564461cd11e238e00f62c07d80084d0fe7450588444a5486e0ad36e4251d0ce0e280c000002dc698000322e06949a0123ac0746c95f00008c638001bc4e10480004a000410001a407c000510003e40115e204000000a30003b83925a066000558000000800016b0a80852280030a93c7214c3903e80819743c8dcd623f2006c000163188000ec00037c704001624bc00c00198000718001e62da478d1a3e24011413a2c00012d100a93a833d198e30004f80025f09e53434847000001271640009188ba290dc934249e118434c099f9150120c49bc37e1e92398841055d0a0344440d4160090040000003050010080400007004000000b03c0100004004000641000c020001c02401000000080801c02000020140000014004020000c00c1f0001700c010240406c02000050a404010030040701c04000000340102401000010001104c010040300404004000140700c03008000500005c1302004000070a00002003060020000102402018030201f014000140000000010000280101c020040000000004000100100c0e000030340800c0200c00000010000a0100f038000180e0080303800000080340304c3d0000c028030040100c05000240000b06000010010200f05c00010010180500409000030001e0080c0180004c010000f004180040206012bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x24a0227f8890002328f45f0004ce0000011425600121000000000ab17b2d44dc4a131000000c11a70003d47000000073c0009203000092800012000d69f1000000798a60006c4cf8ba00072c000b3000065138001f8058000000284748322d24e000000000000006c23b0746cc001c21e26e9310001027ec2fa154a6594918620c08c00026324447c001d52108bc00000000948001ce0000001c03d00002c5205e2cc2d89e80046818c0000031a8e0d717c00000000000496000d20310b20008592d4000002b8db0007c8001f82ea000a2800000628580000003d0c88610002fc0d9720340011321210e0003b8000007f52e155154154758000006c8a1800000000641e40cc3ecd59794862711b1010c864c630004482ec00144000550f491c13c8c82d9923e0328a480028c44c750b1272000000000001d0001bb1e4000da00009c5d8000004560004f8000000012600005a0002000016a7803e8ff49074c712580000000017a0d4618fb8004225cc158a70007f0000f722a410000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x941d023e65d0d40c714f435031c5350d40ae181435031c5390940ae982425031c5310940c714f415031c5350540ab189415035853d0140c714e405023d6590c40cd90d51103344354440cd547401037151900408fd95401029c6350040cd545401027b6550040b618d401037151500408fd9152cc23c6454b309dd8552cc2746154b308f99251cc23d6494730bc58440cc27661152309d584548c23e649513097d8d544c27b60551308f994544c33854cc130c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c33860550308f990540c26e62150309b588540c27661150309d584540c31d54d0c3097594430c32e5494830cb552520c32e5454830cb551520c3686054830cd952510c3355494430d994a510c3655294430dc982510c3365454430cd551510c3665254430d9549510c33954d0030e6d0f400c2796510030e610c400c2f1611003097d95300c29c644c0309ed95300c2b8644c0309798f54c825d63d53208f99353c823d64d4f20ba18132c82e9620c3209d987548827561d52209d984548827561152208f993538823d64d4e209d987538827561d4e208f990538823d6414e209d98453882756114e20cd95251883355494620dc98251883365454620cd551518825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534827b6054d209b195324823e64145208f590514825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f590530826e6214c209d98453082756114c208f992500823d64940209e5943008359530c0209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108fd9152c423c6454b108f99052c423d6414b109798c52c425d6314b10b918941c42b5648c710ad59021c42d56308710d954821c426e62d52109b58b548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f59352842d86350210ae5903084359530c210ba58830842b9648821097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c63549109d19541442e46250510ad59231442f2608c5109d195314427665c8510ad59021442d56308510bc98021442786550110b618d40443b141501109e99730442b9640c110ba58830442f2610c110ae59220442f261881109e195204423d65950108f990540427661150109e980540423e64d4c108f593530427a60d4c108f990530423d6414c109b988530426d6214c109d984530423e64d48108f593520427661d48108f990520423d64148109798c520425d63148109e980520433554c40109e596100433954840109dd95100433554440109ed9510043395444010
  | 1 => 0x10040000001000000040800000010020080c0440000401004000000301c01030000080200c00018020000a00804010030140000c00004000140001c0800400038010101100c07000010100001800050029e9825190e7960946439d9845050e756114143d6d0c5050f3a4314143dc9845050f7161141438fd954310eb86050c4397d954310ed86050c439dd855210e7461548439d9865090a7561942429e9805150a796014542d9d085150b364214542dc9805150b7160145429ed815310a786054c42c754c4310aad6210c428fd954210ab461508429bd954210ae461508429d98754cca7561d53328f99251cca3d64947329e98251cca7960947329e983548ca7960d52328f992508ca3d64942329d986508ca7561942328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb7051141329d984540ca7561150329e980540ca79601503297d95320ca6f654c8329ed8153d06786054f41ad18542d06b66190d41cb90c525072c43149418f997425072c52d0941cb14942506b46150941d914b415072c52905418f596421063f6550441ab18941106776550441b9189411073a4254041ce109501073b4154041dc90550107394154041dc505501066e62d53319b58b54cc6d4614cb319e983548c67960d52319e980548c6796015231ce952508c7395494231ce951508c73954542319bd89544c66c62551319ed81544c67860551318f990504c63d64141319b988540c66d62150319e980540c67960150318fd91520c63c64548318f992510c63d649443197d95310c677654c4318fd9153c863c6454f219ed8153c86786054f21bc58041c863e64943218f59250c867a60152219e580548863e64d4e218f593538867a60d4e219e583538863e64951219bd89544867761551218f994544863e6494d218f592534863f6454d218f19153486776154d219ed8153486786054d21cd153214872c54885219798f540865d63d50219e983540867960d50218f596540872c6255021cd185540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755153087546154c218f990530863d6414c219798c530867a6014c219e580530872d54d08219b594420873554d0421e9d0b41086756510421e910841086f16010421d554f3108675650c421b9588310866f6548421ab19121086776548421ad191210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50086b86050f409dd8552d02746154b40ab18
  | 2 => 0x8a0000031e45ac6402c81315e5fb2a002ba0022e50800958001c800000005f0004e80000000002b000000000ac00000b1000730001816c00000000000026000000000006d00000000ce9828d184000009333200000989d62a03e45150100002300000000a01c253800000a0000001880000000001da781ecb78000027422a14a50ba4b92aa2a7c011d277ac200030000cc602900000013832c886e548b8000f23109a000008729a0010e00000ad80000000001b2000000014400000000f0002fea4aaec1b2ea384a901fe00000c507a9e076962f0afab4492ac001fc8f8a6222c06781ea79a4760e48c2aa35146a61ac10800000000ea36af1904d8f80013220a684400000276001e8001221e13c0016a888ea001c83e8ec009ca000002027a5d0dab4868c417200000000120013000000b70009b2180000027ab86223ca9b12003363783c23800482ce4300062800000461121ec72da02800219780000000000000000019c918c6c9162a70280000030238b40e61d318060000001c80000001041aaa800000c2800bba5061b307e8006a8000032c0000099acc83000360dc001e6c68c2a892800070000e2001a226000171e23d0009c16eba0be82176003380011e1f00000000068bc40800000000023a040b4000c84f8000e26a91050000000018e3f9f61491ac00000000089a8c16000002d80520a71a5e0d8485c12c2500000204a20e0000000011c928f65e8005a21acd3209b80000000bc9649732600000000007d000ba960210063380000022000005280000000461a80a800c5ae02b912921669f926a90006e000939061b2eca5800002f80d09c329967c10a29000000004220e2db0e0000000000a1a02948000305e16800bd284001dc001406f0960028200272000a23f000000002c1b600000ca0000000e6c0006602c00000002d60015c81816842a07e07e3b8e8c2148550007c8004e2d4680b2c12e2000244d2e485a642400009956000aa0000000000be8000022c66800000007000024854000007baf653000849e4000000015a0018c7a8003480073ab200000882ca002fc080568ca5a752e60000000000000006e9c4190000002e000000022ac0a42699bec3066740d68919434192001ae0000095008560000140b00400004000040a00800018000100000000000010000102c02020000280300008008050100e004020041400000004060080200401000000000001804014010040000003000000000000c0200806014000041c010020240100
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x28000000030020e0000180000005130000001400160870444520c634b2400000004000000000170000000003d50000200408010b461c15310c42948e2b1086214b170986435069338c86292832c5c06150941a50e4a0aa020d60725055010712310c2aa0434c5c06155021d4084b008210ca4745883108658b88c0a1a818614e6090940962e330484a060c53189415030a31aa2a00819418d5150040c30c6302a81853171181540c34821ac220061461d1530c020a48e8a9043885187454c308434831a82a0221681c94150110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x60840020000921809c64314941c20625c06155021c10535c66090940c10635c46055030c80631c94150110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 814)*11) 11
  | 4 => packedAt s5K4 (17112+((h/138+packedAt s5K4 (15732+(h % 138)*10) 10) % 660)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 62)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 12)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf01ff81fffff841f1f0ff87f8ffffc008e73fc
  | 1 => 0xffe0ffe07e1fffe01ff0ff87f1e03ff8f38ccf
  | 2 => 0xffffffff801fffffe000fffffe003fff03ff0f
  | 3 => 0xffffffe007ffffff0007ffffc007fc0ff0
  | 4 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x14c288c515044c0505893c498329a43086315c
  | 1 => 0x214a9143212944a00b984cc29142a950b284c5
  | 2 => 0x428422880c52014b20009115240512a3015b0a
  | 3 => 0xb1444124803127252220006489600c5580ea0
  | 4 => 0x8c18871c719c679c9ccce66001182306efe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0fee0eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37107
namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5005fe54017f55005fc54017fd4c05fe53017f54c05fc53007fd0c01fe43007f50c01fc43017fd4805fe52017f54805fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4003fe50017f54003fc50007fd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001fb8812000ff84090007ec2048003fc1024001ff8412000ff42090007fc1048007ffb2e2003bfd971001ffccb8800afe65c4007feb2e2007bf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc98801afe64c4007feb262000bf5931001ff8c98800efc64c400fffaa62007ff9531003ffaa98801ffc54c4007ffb1e2003bfd8f1001ffcc788002fe63c4007feb1e2000bf58f1001ff8c78800efc63c400fffa9e2007ff94f1003ffaa78801ffc53c4001ffa1e2000ff90f10007fa8788003fc43c4007ffb162003bfd8b1001ffcc588016fe62c4007feb162000bf58b1001ff8c58800efc62c400fffa962007ff94b1003ffaa58801ffc52c4001ffa162000ff90b10007fa8588003fc42c4001ff9962000ff8cb10007fa6588003fc32c40037f30e2003ffd471001ffca38800ff651c4007fea8e2007fd5471001ff8a38800fff41c4007ff20e2003fd9071001ffa8388003f541c4007fe20e2003ffcc71001ffc638800ff631c4007fe98e2000fd4c71001ff8638800fff21c4001fb90e2003ff8871001ffa438800ffc21c4007fa10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188013ff65440097fb2a2000dfd9510004feca88013fe65440057f32a2004ff59510025faca88013fc65440057e32a2004df19510014f8ca88003ff64440017fb222000ff99110035fcc888003fd64440017eb222000ff19110035f8c888013ff5444009ff2a22004ff55110027f8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688013ff5344009ff29a2004ff54d10027f8a688003ff4344001ff21a2000ff50d10007f88688003ff62440017fb122000ff9891002dfcc488003fd62440017eb122000ff1891002df8c488013ff5244009ff2922004ff54910027f8a488003ff4244001ff2122000ff50910007f88488003ff3244001ff1922000ff4c910007f86488006ff6144009ffa8a2003ff94510027eca288013fd5144009faa8a2003ff14510007fe828800ffe4144001fb20a2000ff50510007ea828800ffc4144001ff98a2003ff8c510007ec6288003fd3144001fa98a2003ff0c510007fe4288003f72144007ff10a2000ff4851001ff84288003f421440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044007fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3ff414c001ff20a6000ff50530007f88298003ff314c001ff18a6000ff4c530007f86298003ff214c001ff10a6000ff48530007f84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826000fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fe1026001ff8413000ff82098017ff65c800b7fb2e4005ff99720015fccb900177e65c80053f32e4005ff5972004dfacb900177d65c80013eb2e4005ff1972002df8cb90017ff64c800b7fb264005ff99320035fcc990017fd64c80017eb264005ff1932002df8c990027ff54c8013ff2a64009ff5532004ff8a990017ff63c800b7fb1e4005ff98f20005fcc790017fd63c80017eb1e4005ff18f2002df8c790027ff53c8013ff29e4009ff54f2004ff8a790003ff43c8001ff21e4000ff50f20007f88790006fe62c800bffa964005ff94b2002fdca590017fd52c8013f6a964005ff14b2002ffe8590017fe42c800bfea164005ff10b2002ffe6590017fe32c800bf71964005ff4cb20007da6590017fc32c800bffb0e4005ff9872001dfcc390017fd61c80017eb0e4005ff1872004ffea390027fe51c8013fea8e4009ff14720007fe8390003fe41c8001fea0e4000ff10720007fe6390003fe31c8001fe98e4000ff0c72002ffe4390017fe21c800bfe90e4005ff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff0864001ff04320047feca90022ff6548011ff32a4002bf99520047faca90022fd6548011fe32a4002bf19520007fec890002ff6448001ff3224006bf99120007fac890002fd6448001fe3224006bf19120047fea890023fe5448011feaa24008ff15120007fec690002ff6348001ff31a4000bf98d20007fac690002fd6348001fe31a4000bf18d20047fea690023fe5348011fea9a4008ff14d20007fe8690003fe4348001fea1a4000ff10d2000dfec490023ff524800bff2924008fb94920047faa490023ed524800bfe2924000ffd092002ffc8490003fd424800bfe2124000ffcc92002ffc6490003ee3248001fe9924000fb4c92002ff86490003ff61480017fb0a4000ff98520007fac290003fc61480077e30a4008ffd4520047fca290023fd5148011fe28a4000ffd0520007fc8290003fd4148001fe20a4000ffcc520007fc6290003fd3148001fe18a4005ffc8520007fc4290003fd214800bfe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe4090017fb2048003ff1
  | 2 => 0x40007fa86a0003bd435000dfe21a8000ffd8940005fec4a0003fe6250001feb128000ff1894002df8c4a0037ff525001bff292800dff5494006ff8a4a001bff4250001ff2128000ef90940007fa84a001bfc4250001de2128000ffcc940007fc64a0003fd3250001fe1928000ffd8540005fec2a0003fe6150001feb0a8000ff1854001df8c2a0037ff515001bff28a800dff5454006ff8a2a001bff4150001dfa0a8000ff90540007fa82a0003bd415000dfe20a8000ffcc540007fc62a0003fd3150001fe18a8000ffc8540007fc42a0003fd2150001fe10a8001bfd814000ffea0a0007fe5050003fea828001ff1414000ffe80a001bfb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ff8c14000ff860a0007fe2050003fe1028001ff8414000ff820a002fff65cc0197fb2e600cff99730015fccb98033fd65cc0197eb2e600bff19730015f8cb9802fff64cc0017fb266000ff99330035fcc998003fd64cc0017eb26600bff19330035f8c998033ff54cc019ff2a6600cff55330067f8a998006fe63cc019ffa9e600bff94f30067bca798033fd53cc019eea9e600bff14f30007fe879802ffe43cc001fea1e600bff10f3005ffec598003fe62cc00b7f3166000ff58b30005fac59802ffc62cc019ffa96600cff94b30067faa598033fc52cc001ffa166000ff90b30007fa8598003fc42cc017ff9966000ff8cb30007fa659802ffc32cc017ffb0e6000ff9873001dfcc398003fd61cc0017eb0e600bff18730067fea398033fe51cc019fea8e600cff14730007fe8398003fe41cc001fea0e6000ff1073005ffe6398003fe31cc001fe98e600bff0c730007fe4398003fe21cc001fe90e6000ff0873000dfac198007ff50cc003ff2866001ff5433000ff8a198007ff40cc003ff2066001ff5033000ff88198007fe30cc003ef1866001fe8c33000ff86198007dc30cc003ff1066001ff0833000ffc2198007fc10cc015ffb2a600abfd9530006feca980027f654c015ff32a6002bf99530057faca9802afd654c015fe32a6002bf19530056f8ca9800a7c654c001ffb226000bfd91300077ec898002bf644c001ff3226006bf99130007fac898002fd644c001fe3226006bf1913000778c898002bc644c015ffaa2600aff95130057faa89802bfc544c0037fb1a600affd4d30057fca69802bde534c015fea9a600af754d30057f8a698003ff434c001ff21a6000ff50d30007f88698003ff624c0017fb126000ff98930007fac498003fc624c00b7e312600affd4930057fca49802bfd524c015fe2926000ffd0930007fc8498003fd424c001fe2126000ffcc930007fc6498003fd324c001fe1926000ffd8530005fec298003fe614c001feb0a6000ff1853001df8c29802bff514c015ff28a600aff54530057f8a29800
  | 3 => 0xeb284203ff1942101df8ca1080fff64084077fb204203ff99021035fcc81080fbe64084015f3204203ff59021005fac81080fbd64084015eb204203ff1902101df8c810843ff5408421ff2a04210ff55021087f8a81080fff63084077fb184203ff98c21005fcc61080fde63084016f3184203ff58c21005fac61080fdd63084016eb184203ff18c2101df8c610843ff5308421ff2984210ff54c21087f8a610803ff4308401ff2184200ff50c21007f88610816fe620840bffa904205ff9482102ffaa410817fc520840bffa104200fbd082102ffc8410817fd420840bfe2104205fb1082102ffe6410817fe320840bfe9904205ff0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108401fb9884203ff8c42101ffa621080ffc3108407fa1884203ffc842101fde421080ffe2108407fb1084203ff4842101fda4210817f52108407ffb004203ff9802100dfcc01080ffa60084037d3004203ff58021005fac01080ff960084017cb004203ff1802100df8c010843ff500841fff2804210ff5402107ff8a01083ffe400841ffe200420fff8c02107ff86010817fe200840bfe1004203ff8402101ff8201081bff65d000d7fb2e8006ff99740015fccba001b7e65d00053f32e8006ff59740075facba001b7d65d00013eb2e8006ff19740035f8cba0006fe64d000dffaa68006ff953400377ca9a001bfd54d001ddeaa68006ff15340037fec7a001bfe63d00017f31e8006ff58f40005fac7a001bfc63d001dffa9e800eff94f40077faa7a003bfc53d000dffa1e8006efd0f40037fc87a001bfd43d0001dea1e8006ff10f40037fec5a001bfe62d000b7f3168006ff58b40005fac5a001bfc62d001dffa96800eff94b40077faa5a003bfc52d000dffa168006ff90b400077c85a001bfd42d000dfe2168006ef10b40007fe65a0003fe32d0001fe9968000ff0cb40037fec3a001bfe61d00077f30e8006ff58740005fac3a001bfc61d001dffa8e800eff94740077faa3a003bfc51d000dffa0e8006efd0740037fc83a001bfd41d0001dea0e8006ff10740007fe63a0003fe31d0001fe98e8000ff0c740007fe43a0003fe21d0001fe90e8000ff0874000dfac1a0007ff50d0003ff2868001ff5434000ff8a1a0007fe40d0003df2068001fe9034000ff881a0007bc40d0003ff1868001ff0c34000ffc41a0007fc20d0003ff0868001ff0434006ffecaa0036ff655001bff32a8002bf9954006ffacaa0036fd655001bfe32a8002bf1954000dfec8a0037ff545000dff2a2800def9514006ffaa8a0037bd545000dfe2a28000ffd8d40005fec6a0003fe6350001feb1a8000ff18d40005f8c6a0037ff535001bff29a800dff54d4006ff8a6a001bff4350001dfa1a8000ff90d
  | 4 => 0x817fd42c840bfe2164205ffccb2102ffc6590817fd32c840bfe1964216ffd472101ffca39085bfd51c8407fe28e4200ffd072101ffc8390803fd41c8407fe20e4200ffcc721007ee639080ffe31c8401fe98e4203ff0c721007e86390817ff60c840bff3064201bf9832102ffac190802fd60c840bfe3064201bf183210b7fea190857fe50c842dfea864215ff143210affc8190857fc40c842bff1864215ff0c32102ffc4190817fc20c842bff0864203ff0432101ffecb1080eff6588407ff32c4202bf9962101ffacb10852fd6588407fe32c4203bf1962101ffec91080eff6488407ff3244206bf9922101ffac910802fd6488407fe3244203bf192210a7fea910853fe5488429feaa44214ff1522101ffec71080eff6388407ff31c4200bf98e2101ffac710802fd6388407fe31c4203bf18e210a7fea710853fe5388429fea9c4214ff14e21007fe8710803fe4388401fea1c4200ff10e21095fac510853ff528840bff2944214ff54a2102ff8a510803ff4288401f7a144205ff90a21007fa8510817fc4288401f62144200ffcca2102ffc6510803fd328840bfe1944203bf9862101ffea31080ffe5188407fea8c4203ff1462101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fe98c4203ff0c62101ffe431080fef218840bfb90c4203ffd822101ffcc110806fe6088407feb044200bf5822101ff8c110806fc6088429ffa844213ff942210a7faa11084ffc5088427ff2044213ff1022109ffc611084ffc3088427ff1044205ff0822101ffc211080ffc1088425ffb2a4212bfd9521097fcca9080afe6548425feb2a4212bf59521097f8ca9080afc6548401ffb224200bfd91210077ec890802bf6448401ff3224206bf99121007fac890802fd6448401fe3224206bf1912100778c890802bc6448425ffaa24212ff95121097faa89084bfc5448401ffb1a4200bfd8d21007fcc690802fe6348401feb1a4200bf58d21007f8c690802fc6348425ffa9a4212ff94d21097faa69084bfc5348401ffa1a4200ff90d21007fa8690803fc4348425ffa924205ff94921097faa490817fc5248401ffa124205ff90921007fa8490817fc4248401ff9924205ff8c921007fa6490817fc3248425ffa8a4203ff94521097faa29080ffc5148401ffa0a4203ff90521007fa829080ffc4148401ff98a4203ff8c521007fa629080ffc314840bff90a4205fdc852101ffc429080fee2148401ffb024200bfd812108ffcc090806fe6048401feb024211ff1812100df8c09084bff5048423ff2824212ff5412108ff8a090847fe4048423fe2024211ff8c12108ff86090847fe204840bfe1024211ff8412101ff8209080fff65084077fb284203ff99421015fcca1080f7e65084053f3284203ff59421085faca1080f7d65084013
  | 5 => 0x823101ffcc118806fe608c407feb046200bf5823101ff8c118806fc608c43bffa84621cff942310effaa118873fc508c439ff204621cff102310e7fc6118873fc308c439ff104621cff0823101ffc211880ffc108c437ffb2a621bbfd95310dffcca9880afe654c437feb2a621bbf595310dff8ca9880afc654c401ffb226200bfd9131007fcc89881afe644c401feb226200bf59131007f8c89881afc644c437ffaa2621bff951310dffaa89886ffc544c437ffa9a621bff94d310dffaa69886ffc534c401ffa1a6200ff90d31007fa8698803fc434c401ffb126200bfd8931007fcc498803fd624c401fe3126205bf189310dffea49886ffe524c437fea92621bff14931007fe8498803fe424c401fea126200ff10931007fe6498803df324c401ff1926200ff4c931007ba6498803fc324c437ffa8a6203ff945310dffaa29880ffc514c401ffa0a6203ff90531007fa829880ffc414c401ff98a6200fdcc53101ffc629880fde314c401ffb026200bfd81310d7fcc098806fe604c401feb02621aff1813100df8c09886fff504c435ff282621bff541310d7f8a09886bfe404c435fe202621aff8c1310d7f8609886bfe204c435fe102621aff8413101ff8209880fff650c4077fb286203ff99431015fcca1880ffd650c4317eb286203ff1943101df8ca1880fff640c4077fb206203ff99031035fcc81880ffd640c4017eb206203ff1903101df8c818863ff540c431ff2a06218ff550310c7f8a818866fe630c431ffa98620bff94c310c7faa61882ffc530c401ffa18620bff90c31007fa861882ffc430c407ffb106203ff9883102dfcc41880ffd620c4017eb106203ff188310c7fea418863fe520c431fea906218ff14831007fe8418803fe420c401fea106200ff1083105ffe6418803fe320c401fe990620bff0c83101dfcc21880fff510c407ff2886203ff5443101ff8a21880fff410c407ff2086203ff5043101ff8821880fff310c407ef9886203ff8c43101fec621880ffd310c407ee9886200fd4c43101ffec01880ffe600c4037f3006203ff58031005fac01880ffc600c4037e3006218ffd40310bffca018863fd500c42ffe2806217ff900310bff8801885ffe300c417fe1806217ff880310bff8401880ffe100c407fe0806205ffd972102dfecb90817fe65c84057f32e4205ff597210b5facb90817fc65c840b7e32e4205ffd932102dfec990817fe64c840d7f3264205ff59321005fac990817fc64c840b7e3264216ffd53210b7fca99085bfd54c842dfe2a64205ffd8f2102dfec790817fe63c84017f31e4205ff58f21005fac790817fc63c840b7e31e4216ffd4f210b7fca79085bfd53c842dfe29e4200ffd0f21007fc8790803fd43c8401fe21e4205ffd4b2102ffca590817fd52c840bfe2964205ffd0b2102ffc8590
  | 6 => 0x7fe0828203ffd944101dfeca2080ffe65104057f3288203ff59441105faca2080ffc65104077e3288206bf99041037fea82081bfe541040dfeaa08206ff1504101ffec62080ffe63104017f3188203ff58c41005fac62080ffc6310441ffa988220ff94c41107faa620883fc531040dffa188206ff90c41037fa862081bfc4310407ffb108203ff9884102dfcc42080ffd62104017eb108203ff18841107fea420883fe5210441fea908220ff14841037fe842081bfe4210401df2108206ff50841037f8842081bbc4210401ff9908200ff8c841007fa6420803fc32104077f3088203ffd444101ffca22080ffd5110407fe2888203ffd044101f7e822080ffe4110407fb2088203ff5044101f7a822081bf54110407ffb008203ff9804100dfcc02080ffd60104017eb008203ff1804100df8c020883ff501043fff2808220ff540410fff8a02081bfe401040dfe200821fff8c0410fff8602087ffe201043ffe1008203ff8404101ff8202082fff65cc4337fb2e6219ff99731015fccb988677e65cc4053f32e6219ff597310cdfacb988037d65cc4013eb2e620bff19731015f8cb9882fff64cc4017fb266200ff99331035fcc998803fd64cc4017eb26620bff19331035f8c998867ff54cc433ff2a66219ff553310cff8a998867ff53cc417ff29e6219ff54f3105ff8a798803ff43cc417ff21e6200ff50f3105ff8879882fff62cc401ff3166205bf98b31007fac598802fd62cc417fe3166219ffd4b310cffca598867fd52cc433fe2966200ffd0b31007fc8598803fd42cc401fe216620bffccb31007be6598803fe32cc401fe9966200f74cb3105ff86598867ff51cc407ff28e6219ff5473101ff8a398803ff41cc407ff20e6200ff5073101ff8839882fff60cc43dff3066201bf98331007fac198802fd60cc417fe3066201bf183310cffea19887bfe50cc433fea86621eff143310f7fc819887bfc40cc43dff186620bff0c3310f7fc419887bfc20cc43dff0866203ff0433101ffecb1880eff658c407ff32c6202bf9963101ffacb18876fd658c407fe32c6203bf1963101ffec91880eff648c407ff3246206bf9923101f7cc918802be648c407feb246200bf5923101f7ac918802bd648c407fe3246203bf192310effea918877fe548c43bfeaa4621dff152310ddfac718877ff538c43bff29c621dff54e310eff8a718803ff438c401ff21c6200ff50e31007f8871880fff628c407ff3146205bf98a3101ffac518802fd628c407fe314621dffd4a310effca518877fd528c43bfe2946200ffd0a31007fc8518803fd428c401fe2146200ffcca31007fc6518803fd328c401fe1946203bf9863101ffea31880ffe518c407fea8c6203ff1463101ffe831880ffe418c407fea0c6203ff1063101ffe631880fdf318c401fb98c6203ffd
  | 7 => 0xa081bfc65d040d7e32e8206ffd5341037fca9a081bbe54d040dfeaa68226ef55341037f8a9a081bff63d040dff31e8200bf98f41037fac7a0802fd63d040dfe31e8226ffd4f41137fca7a089bfd53d044dfe29e8206ffd0f41037fc87a0803be43d040dfea1e8206ff10f410377887a081bff62d040dff3168205bf98b41037fac5a0802fd62d040dfe3168226ffd4b41137fca5a089bfd52d044dfe2968206ffd0b410377e85a081bfe42d040dfea168200ef50b41037f885a0803ff32d0401ff1968200ff4cb41007f865a089bff51d0407ff28e8226ff5474101ff8a3a081bff60d040dff3068201bf98341037fac1a0802fd60d040dfe3068201bf18341137fea1a0897fe50d044dfea868225ff14341037fc81a081bfc40d044bff1868225ff0c34112ffc41a0897fc20d044bff0868203ff0434101ffecb2080eff6590407ff32c8202bf9964101ffacb20892fd6590407fe32c8203bf19641115fac920893ff549040dff2a48224ff55241037f8a92080fff6390407ff31c8200bf98e4101ffac720802fd6390407fe31c8224ffd4e41127fca720893fd5390449fe29c8206ffd0e41007fc8720803fd439040dfe21c8203ffd8a4101ffcc520816fe6290407feb148200bf58a4101ff8c520893ff5290449ff2948224ff54a41127f8a52081bff4290401ff2148200ef90a41007fa852081bfc4290401de2148200ffcca41007fc6520803fd3290401fe1948203bf9864101ffea32080ffe5190407fea8c8203ff1464101ffe832080fbf419040dfba0c8203ffd824101ffcc120806fe6090407feb048200bf5824101ff8c120806fc6090449ffa848223ff94241127faa12088ffc5090447ff2048206ff1024111ffc612088ffc3090447ff1048223ff0824101ffc212080ffc1090445ffb2a8222bfd9541117fccaa080afe6550445feb2a8222bf59541117f8caa080afc6550445ffaa28206ff951411177ca8a088bfd5450445deaa28206ff15141007fec6a0802ff6350401ff31a8200ff58d41007f8c6a0802fc6350445ffa9a8222ff94d41117faa6a088bfc535040dffa1a8200ff90d410077c86a0803fd435040dfe21a8200ef10d41007fec4a0802ff6250401f7b128200bbd8941007fcc4a0803fd6250401fe3128205bf18941007d8c4a0802ec6250445ffa928222ff94941117faa4a088bfc525040dffa128200efd0941007fc84a0803fd4250401dea128206ff10941007fe64a0803fe3250401fe9928200ff0c941117fea2a080ffe5150445fea8a8203ff14541037fe82a081bf74150407ff20a8203ef90541007fec0a0802ff6050443ff3028201bf98141007fac0a0887fc60504037e3028222ffd414110ffca0a088bfd5050443fe2828221ff90141037f880a0887fe3050443fe1828221ff8814110ff840a0887fe105040
  | 8 => 0xfd923202ffcc91901afe648c80bfeb246400bf5923202ff8c919016fc648c85bffaa4642dff9523216ffaa9190b7fc548c8577eb1c642dffd4e3216ffca7190b7fd538c85bfe29c6400ffd0e32007fc8719003fd438c801fe21c6405bf98a3202ffea519017fe528c80bfea946405ff14a3202ffe8519017fe428c80bfea146405ff10a3202ffe6519017df328c801f79946405ffd863202ffcc31900efe618c80bfeb0c6400bf5863202ff8c3190b7ff518c85bff28c642dff5463216ff8a319017ff608c80bff3046401bf9823202ffac119002fd608c80bfe3046401bf1823216ffea1190b3fe508c85bfea84642cff14232167fc81190b3fc408c859ff184642cff0c23202ffc4119017fc208c859ff084642cff0423215ffeca990aeff654c857ff32a6402bf9953215ffaca990aefd654c857fe32a6402bf19532007fec899002ff644c801dfb226400afd9132007fcc89901afe644c801feb226400bf59132007f8c89901afc644c801de3226400af1913215ffea8990affe544c857feaa2642bff1513215ffea6990affe534c857fea9a642bff14d32007fe8699003fe434c801fea1a6400ff10d3215ffea499017fe524c857fea926405ff14932007fe8499017fe424c801fea126405ff10932007fe6499003ef324c80bff1926405f78c932007fec299002ff614c801fbb0a6400bdd8532007fcc299003fd614c801fe30a6403bf18532007e8c299002f4614c857ffa8a642bff9453215ffaa2990affc514c801ffb026400bfd8132157fcc099006fe604c801feb02642aff1813200df8c0990afff504c855ff282642bff54132157f8a0990abfe404c855fe202642aff8c132157f860990abfe204c80bfe102642aff84132157f82099017ff650c80b7fb286405ff99432015fcca190177e650c8053f3286405ff59432145faca190177d650c8013eb286405ff1943202df8ca19017ff640c80b7fb206405ff99032035fcc819017fd640c8017eb206405ff1903202df8c8190a3ff540c851ff2a06428ff55032147f8a8190a6fe630c851ffa98640bff94c32147faa61902ffc530c801ffa18640bff90c32007fa861902ffc430c80b7f3106405ffd483202ffca419017fd520c80bfe2906405ffd083202ffc8419017fd420c80bfe2106405ffcc83202fbe6419017fe320c80bf71906405ff4c83202fba6419003ed320c80bffb086405ff9843201dfcc219017fd610c8017eb086405ff18432147fea2190a3fe510c851fea886428ff1443202ffec019017fe600c8037f3006405ff58032005fac019017fc600c8037e3006428ffd403213ffca0190a3fd500c84ffe2806427ff9003213ff8801909ffe300c817fe1806405ff8803202ff8401909ffe100c84ffe0806406ffd9741035fecba081bfe65d04057f32e8206ff59741135facb
  | 9 => 0x867ff2048406ff1024219ffc61210cffc309080bff1048405ff0824219ffc21210cffc1090865ffb2a8432bfd9542197fccaa100afe6550865feb2a8432bf59542197f8caa100afc6550865ffaa28406ff95142197faa8a101bfc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8400bf18d42197fea6a10cbfe5350865fea9a8432ff14d42037fe86a1003fe4350801fea1a8406ff10d42197fea4a1017fe5250865fea928405ff14942037fe84a101bef425080bff2128405ef90942007fec2a1002ff6150801ff30a8400ff58542007f8c2a100efc6150865ffa8a8432ff94542197faa2a10cbfc5150801ffb028400bfd814218ffcc0a1006fe6050801feb028431ff1814200df8c0a10cbff5050863ff2828432ff5414218ff8a0a10c7fe405080dfe2028431ff8c14218ff860a10c7fe205080bfe1028431ff8414218ff820a1017ff651080b7fb288405ff99442015fcca210177e65108053f3288405ff59442185faca210177d65108013eb288405ff1944202df8ca2101afe641080dffaa08406ff950420377ca82101bfd5410861deaa08406ff1504202ffec621017fe63108017f3188405ff58c42005fac621017fc6310861ffa988430ff94c42187faa6210c3fc531080dffa188406ff90c420077c862101bfd431080dfe2188406ef10c4202dfcc421017ff521080bff2908405ff5484202ff8a421017ff421080bdfa108405ff9084202fdc8421017fd421080bdea108406fb5084202ffec221017fe61108077f3088405ff58442005fac221017fc6110861ffa888430ff94442187faa2210c3fc511080bffb008405ff9804200dfcc021017fd60108017eb008405ff1804200df8c0210c3ff501085fff2808430ff5404217ff8a02101bfe401080dfe200842fff8c04217ff86021017fe201080bfe100842fff8404217ff8202102fff65cc8537fb2e6429ff99732015fccb990a7fd65cc8537eb2e640bff19732015f8cb9902fff64cc8017fb266400ff99332035fcc999003fd64cc8017eb26640bff19332035f8c9990a7ff54cc853ff2a66429ff5533214ff8a9990a7ff53cc817ff29e6429ff54f3205ff8a799003ff43cc817ff21e6400ff50f3205ff887990a7ff52cc80bff2966429ff54b3202ff8a599003ff42cc80bff2166400ff50b3202ff8859902fff61cc801ff30e6403bf98732007fac399002fd61cc817fe30e6429ffd473214ffca3990a7fd51cc853fe28e640bffd8332177fcc199006fe60cc801feb066400bf5833205ff8c199006fc60cc853ffa86642eff9433214ffaa1990bbfc50cc85dff206642eff10332177fc619902ffc30cc85dff1066405ff08332177fc21990bbfc10cc80bffb2c6405bfd963202ffccb1900afe658c80bfeb2c642dbf5963202ff8cb19016fc658c80bffb246405b
  | 10 => 0xa4a18effc5250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8603bf185431dffea2a18effe5150c77fea8a863bff14543007fec0a1802ff6050c75ff3028601bf98143007fac0a18ebfc6050c037e302863bffd41431d7fca0a18effd5050c75fe282863aff90143037f880a18ebfe3050c75fe182863aff881431d7f840a18ebfe1050c75fe082860bffd9443035feca2181bfe6510c057f3288606df99443014fcca2181bfd6510c717eb288606df59443004faca2182ffc6510c0d7e3288606bf99043037fea82181bfe5410c0ddf2a08606ff550431c77aa82181bfc5410c737f3188638ffd4c4305ffca6218e3fd5310c17fe2988606ffd0c430377e862182ffe4310c0def2188606ff50c430077a862181bdd4310c17ffb108606ff9884302dfcc42181bfd6210c017eb10860bff188431c7fea4218e3fe5210c71fea908638ff1484305ffec22181bfe6110c077f3088606ff58443005fac22182ffc6110c71ffa888638ff944431c7faa2218e3fc5110c17ffb008606ff9804300dfcc02181bfd6010c017eb00860bff1804300df8c0218e3ff5010c6fff2808638ff540431bff8a02181bfe4010c6fdf2008606ff100430377880218dffe3010c17fe1808637ff880431bff840218dffe1010c6ffe0808606ffd9742035fecba101bfe65d08057f32e8406ff597421b5facba101bfc65d080d7e32e8406ffd5342037fca9a101bfd54d080dfe2a68406ffd8f42037fcc7a1002fe63d080dfeb1e8400bf58f42037f8c7a10dbff53d086dff29e8436ff54f421b7f8a7a101bff43d080dff21e8406ff50f42037f887a10dbff52d080bff2968436ff54b4202ff8a5a101bff61d080dff30e8403bf98742037fac3a1002fd61d080dfe30e8436ffd47421b7fca3a10dbfd51d086dfe28e8406ffd8342037fcc1a1006fe60d080dfeb068400bf58342037f8c1a1006fc60d086dffa868435ff943421b7faa1a10d7fc50d080dff2068406ff103421affc61a10d7fc30d086bff1068405ff083421affc21a10d7fc10d080bffb2c8405bfd964202ffccb2100afe659080bfeb2c8434bf5964202ff8cb21016fc65908657eb248434ffd5242037fca9210d3be5490869feaa48434ef55242037f8a921017ff639080bff31c8400bf98e4202ffac721002fd639080bfe31c8434ffd4e421a7fca7210d3fd5390869fe29c8406ffd0e42007fc8721003be4390801fea1c8406ff10e42007788721016fe629080bffa948405ff94a4202ffaa521017fc529080bffa148405efd0a42037de8521017ff619080bff30c8403bf9864202ffac321002fd619080bfe30c8434ffd46421a7fca3210d3fd5190869fe28c8405ffd824202ffcc121006fe609080bfeb048400bf5824202ff8c121006fc6090869ffa848433ff942421a7faa1210cffc5090
  | 11 => 0x380780000100400300000100400300000080280280180080280080000000681900000e80400080280080200200180180280080080380680600000c00080200000000080080180080080080100780000600280480000400000100480100280100000a80000080682d00080000000100080180180180300000000580180180600080b80000a00000980e80480000c00180280780000380b00080180000400000600c80100d00100c00700081100080380300000300000080200000200380180280100100000900100280380980380080500480000180300100080b00901200400080100680a00800100100600a00080000200180d80300080a80080600200000000700000200400200100000000080380080300080280180100000280000300080200200080180100000000400180500080300d00400080980200000180000180000080100600280500080780080000280280000000001bff65d0c0d7fb2e8606ff99743015fccba181bfd65d0c7d7eb2e8606ff19743035f8cba181bff54d0c0dff2a68606ff55343037f8a9a18fbff53d0c7dff29e863eff54f431f7f8a7a181bff62d0c0dff3168605bf98b43037fac5a1802fd62d0c0dfe316863effd4b431f7fca5a18fbfd52d0c7dfe2968606ffd8743037fcc3a180efe61d0c0dfeb0e8600bf58743037f8c3a18fbff51d0c7dff28e863eff547431f7f8a3a181bff60d0c0dff3068601bf98343037fac1a1802fd60d0c0dfe3068601bf183431f7fea1a18f7fe50d0c7dfea86863dff14343037fc81a181bfc40d0c7bff186863dff0c3431effc41a18f7fc20d0c7bff086863dff0434305ffecb218e6ff6590c73ff32c8602bf996431cffacb218e6fd6590c17fe32c8602bf196431ddfac9218e7ff5490c0dff2a48639ef952431cffaa9218e7bd5490c0dfe2a48606bf98e431cffea72182ffe5390c73fea9c860bff14e43037fe8721803bf4390c0defa1c860bffd8a43007fcc521816fe6290c01feb148600bf58a4305ff8c5218e7ff5290c73ff2948639ff54a431cff8a52182fff6190c01ff30c8603bf98643007fac321802fd6190c17fe30c8639ffd46431cffca3218e7fd5190c73fe28c860bffd82431e7fcc121806fe6090c01feb048600bf5824305ff8c121806fc6090c73ffa84863cff942431cffaa1218f3fc5090c79ff204863cef90243037f881218f3bc4090c79ff184860bff0c2431e7fc41218f3fc2090c79ff084863cff042431dffecaa18eeff6550c77ff32a8602bf995431dffacaa18eefd6550c77fe32a8602bf195431dffea8a181bfe5450c77feaa28606ff151431dffea6a18effe5350c77fea9a863bff14d43037fe86a181bdf4350c01ff21a8600ef90d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1816fc6250c77ffa92863bff949431dffa
  | 12 => 0x4c71c0001f181748ec0000f7c3642c706496f8e021ed3dc800117066e38900000002ff00000000009bb090240c000323505000000055c00000010b006a434893471e28f0000af4b847a100000000601900080280080000000980000102080500000100100000080200480380000d00500080b80100180880100300180680200d00600600100080080200000000280000180200801200000300300000001300200000800a00180080180000080100400080080f80200080080000300d00900000280780900000180201f80380080100080000381880480280e00280080480480180200880300800080900300400080680200000080081000200000100800400380500080080400400880180680000100881280000080100580100480a00000080900380980180080000380c00100680180000500300000602380780001080080180500a80000080700780900280080000000280080000000080880380180000000200200000800080180603500680500000400a00180780100000500480000300280080000680000100600100100000000400000700200480401c00080d00100100000000080000200580100000000080000080080100200000100500381d01380b00400001180280000081200200400080080280500180000300980300280180580000d00000200000100200080d00280e00000180301680580000600600080080000080480200780680180000000a80080180000000b00400000100100000000000e80180380080001300180580e80081280080480000200380000200200480100b80180000180d80380300280100500500300080000180080300000080080201680400380000100480080980400280100280380a00000000000400000b00580180200002780300280000200080000000480000000481000100480580180000080680100000000280300100600b80080080200380100080080680300100080480080380500080000080000600680000280180380380480380000080100000200380080000780101980000180300380000180000080c80880200000000000000080000300000200000000200780000080680000280080000380000000100100100000080380a00000000600180000200100280200c00000100080100300000100500900180300300180780000000000000800000001000280080000080180100000000380080800000200300000280100000000080480000380000b00080000000000100300200000c80680080280280000080000180680000080280080180000f80800500000200000180080000000f80a00000480680100000080480280280300080000880000000400300100080d00080080000380b00080000500000e00180080580080000180100500280180301080400080400000b0020000018028010
  | 13 => 0x18e4ac21f10000001196340016a4701fe4ae1fe22f0f5089b306a3f0eaa0003bf026102651a490800077a2f4354a130ca041032797f4b263b328485d118a4df3ff01082a642f46f05e50f800000027d800085d00000004a865e00006e0000322344072400069b3810b38ac62e12f50000a067a9356800000043700000000000b00001b3400036d370a36800083c46a1f08c80817000147c8fc1b9308868811c3954a70b3c04628d0b08000adc60c1e416586e04e54021ce40009830330000a100002c81ff4e6c30300017b40007f800000007c49a302a0000d780000001080cc45e5000000086c000000000044a0003c3000000000000000000004c1000044400000031b80000002884d686a06200001311164a462be09180009c21e54af210cece64701e973c76030533e907c0000004dd000000000031c000124a3164830ee81500000001c1cc40a153af88c000005b00014e43766923b2800000011f169000000000004e8000bf40004d614dc00098018f1ec8904a0f00000011d6374443993936244622892b000036b0000cb0d6000000021b84463d14a50000000139000000000000044f8664dba20f36489f893877543409a00001f20c580001a41a42239f2509497f3a280008e400024d0d3c63a5bb2ef82b939491337100000000000001c3d4180003538000000907000000000000048ca6784840000f714993cca114f884400000000000000000894268228c282433237991099084038513280428aa00000012588f744417d4e82000046266850463638c10149280003e9921472200000011b019a5c8378104ca8a68f12a8304c148b200000002b28ad00021d07789d914d00013c40004ea1c58a626590ab8000d8c5193c50ce025e000082800000034522480000003c713280000000000000cac9a833900000000000001be16083360ad15a18083c47d73f095fc0684a808ba574600000230a80074250148b81ad35209f11397d8d727280d48d882604eb3b58d38a869d63e6a6240945970f603a4afa3260be1f9855215212426109d26ca353109cf1232037ba29816a8492ed9b085361f311d8000cde9b5000051c02c935000000008c00000009f000000000007bc00031a040977834255f13c88308542b800000013f036645f201d0541261b00000ec200027f00000000002a3000094c16c000054023013c0000d1050295144b8000de64e30000cec6b60590002394e7863a3dc150000004b00020440000d026b865818879b08203ec0002453ed000095203f05b00004782cd4e32808f2a2e0081a3b50c41dd4149bf8c4e00040727685ee3f81fd0e5092403000013e0cb00001d480008587a73be8f40cee09b28996b4000000000087806686a2721fcc6dc92b234928c0009ae000000013c40b35a0e9c2d4773000000000097e3c19f004
  | 14 => 0x61854206c07551b83cf00021c433e1fd357264cb4c25c21e95340007874b980000007a62ed0000df000039f219c6f01e9002277c6f48ff09a95b000072a1c4932d00c5d82539cd00e692a0ff9fa0e6200047009e05fa00000010fc9da0000000000000000000156475c000382000082c80b22b8388384276252a2000000002581aa800027b39fa56c0005a029225f031099200016940008164670000c20000287003c00077450b0be8f6800000003e85220004f01b380f426f49494d00000d51031e3438c5c730c12f01f00004878e9800081e330a82d3384ef4b90b7405ca10241a2f50580002f405ac190000000087413239b3e800006e452009480acad4791095a7043b4743000000012c6691320bd4e7432136619282fa21b43e800092e1690348a500003d750905707381ab000000058081d4a59594c2e97519891fc1e68d0000000107a00027ba7907c81d63458a2ce9c7f213688080c41971b7823d20064100a83a09f834c00019a11aa7a014b1b0430802435d23194260004521338000000417050c4643863f81e2c3c888110b0bf89ea3042a41a3410077109b00003b610d07895a112c3db00014ac5ec20b0000f042a80004aa80013326f12f30000000a08000000000000000000000007270c522ec07608b0100fd437a00a42b0850c5839e16a0b702260a60a2057851250b2b8833c45c23d0e2a5991404ab09d800089c53f4000fccfb04d5000249800047c33f1884f2800000026cc00082b000255c000373000079800071300027c800084f49c1170ca65e9273101c79c0004bb000000010b0001bd4db8000000037cbc200000024c800000021a9ec00000004b50000d1400025109b8aea00046080005184d101c80005663c900619547dc81a1420290edc9ee0a11f78c283de3ea27e40ee1714d808b105a4243e79b1d2f218e428800116058840500000009d000007c01e47232ce1b54aac9ab4e599948d66c408796180000002019b6c210000127a098c4869e00011740000002da07787d888d0000d04000000296000000079c00000f004400033a1eb94067782258eed13885e09d00d8dc80a7046859817a21538693ec45e52e24482850aa51615806786a444d34f92e491a22915ba308fec55518e0dfc77c9d5000212ca669c32dc154000037b00000000005dd0002730d12000000166835a96d00015e03ce2c223880000069b720e1fb09189012eb96b116e0001b080013b01b00390c948006ea16286089e27b10000538000000000000000098a4c109449709f73d580006ca59524b000096691d00025484662754660c7c00000048b1c800001801c180000a41ac0000d4d2182c100005e821c30f1f38aac5e08820eb936ce7a4c60000000000000000000000035f0000000000000000064c000733000000067a3ed49b80008081650
  | 15 => 0x12c99c934266c248800000000006191ccbf80001221c840220f500021e40000003ac18185e28204bd96288946a003e1eb4000000103a4b8000050000186400000037d063c902026183a4f889005e07295500000db44f00002701830000244ea0314232a34c4305eb000000003485b4d28000e9e687201119c7d20850091e48fdc72900388200008221261efc00020035286680fa1cb14901d126014014705185c80513990ffc50090a16c22b8b1850a3e926d8e4478e44720e431847531a21b096e3792c080248848c350a133cdae2362f00bec38811218c0ddcb6c4384de8ab48687a545101d4acc13f1ac038ce1c70644587d8d0a7ff0da000131c1c80000a0c8aa8ab30f00008320063e290780002533a107380002c901f0cf05ce72d0080f7121604122022305be00000002a53c696103d965121290419d02fc0000001189d2926c9de2a893c88860001f82328d0000000000000000da000134c0000002c9041c2f03a3186a6a903e88a442800065a7d64f580000006b5200818000000000000000000001358ec40003d818400d43220002fc81940000000001a9137e00005000000004b42bf0cd0e9276c1b888a0f6638821e014d32a5b014f0000b5000022991e0636000000053d3182a13260000000000283a4c43820ef2bb25ad3d400000000000007ea00000000009ef4109ff000000015e22640003b2000000125a0002fc25306947c800e97ccce00002c180000002fc19915f0ef211b00002207801f714b90484249280911d9080c7992ae8cd44e091536895c800000037a115888289a0ba84cd2ce65d14e813918e11e314923c5a045037e182c00041503202e40006be49784187400001208000000000000000000000000011d00000000000928000645420a5352ac67a000108cf3c3a2037185923611a07a0fec22a8f3000238cdd82a60000c38000347313207061614c02697c0d20000262202000093412f02412b85044e000940900000fe1fe447242623304090c06fb1201ef01700b329d91a0cce4292cc085d02498500000000001e81111440ddc00000021ec00074638f00000005d100022e4ca885025fa39ceee0001ad00008ec00000000000000cc0000158c8c9b242116f466634b4f39528d3a8280220abd0c849e36f90e41807cb0e7a83868675247b1ed8efe58e20780005d0756348945140c7150001eec00000000000000000003859b200005c04f980000005b90561e10f9800043998a02be00033b0000000000000000000000009700000000000001970d8a6b63de800000000000026180000003f200008f6258000000070424733c80008121d300000000000000000fbc0009580001038b98946000031c5c600045a21b4ef479a4c41510b6464b00017102b638a0000001402000000000000000036b2480c126e5022a3a8
  | 16 => 0x447c8980bf13b0a520001cc1a883a84ad098810c7a49633b103c01286d43f3a0bc0001b10001200a1e8d12771c6858c71400000000d83641aea0607a86120000000dd23872b000006322f900f8f6872c00014c25d0bde0004d10c244260000cc2720650000045078091037e29407e8cc64580f5a508f74625000000000082700014b466e3aa0001b0d2ca00032b16780006972a789a4c460000000ab8000000335800018c57008b19d40003b71a42604d329270002650b4e13e3a58b680003150000000bfe00027ea4ec90e44f4508000ce604900023e10f00d74cc158836c00000002d05e41d84a18b2c3be000373103527823a4e10be00004b2000000127204045483442940ed43a963c00061500014d4b789472a0800006407100000010a80004488a80ed49401d40a8903614d39ba67c5205744b49abd0f48f200d80000003eb00027fc9a45362e5a3d07945ec3330c0410c48e37404d0e5c2100000d34a926e03db9460faa99b454000024246d41b98c857414924c12909b400005d80001a83574ee8000a701e124505ccd7666a1021180fba7e04620880a5e3c21d58e5ca005dc34b0c28b486833a6a6449328460fd80000000001d28000000000292800000023734c0d0885600000022b000055b0000938c084d9000102827a00000025240002d613d0dd80000004de000137c00047d800000050200018bc0005993ee04a00006d249e917d0687c743f84a80027f722d00008881553ef80002d09cf2d992105485ce037800098e00000003f00003b8000000097c000000132528206143800002f632e0002358d02156000127c00019c0000000b6e00007f0ad47d40004891c6c9360000189d5c0008380001e0000000000000001388e84c6a3bcade80d4f6000087c62b1ab087c5264e742998cc0004f42f392c4b565172d0a7391260003c2868c0002ed2891fbc000a04096800000000031d80000008d8432a29457253c0a283380004e834200000007ed00000000006a84dc861832800033e17900006e33b78ed800028a0001868cda7a21c6a39000072b19b06f0f9c0cb4e922c534c5ae0ac0d406aa2d30001ded0fc0000ca86e80006a14199370c102870001d2000000043080005a20000000378dde60103404300007d923b9dc09ac8df00000012c4000447a0080000004f49434da600046da170a3c000000171400083b15395605ae0ec01d00000006ac000281c7ee10a21693a80000000d000013f490e3bb007920400005286d40000001168d78ec08833f1097cfca08928d8f98eb61c32610b28b820382af11f50ee0003aa06a941a69a08e828c9c461f1388afc24a3593f489f445600028e188897670c0001ae03660001d61c9815646e2ab8b98a441dc1591b681c80bc00010c4e208f10000bb839a05816427d40007af00019c501e000
  | 17 => 0x726ea4400003cd39209cc8f2082158a1c933a7972f8819c41a0472eb0a18e1260f40a8d508b66de00020c0e808fd00000001b800011c02c800000049f8f140003a400000000000004d423e800000042909d000000000019800003d90002364000250255000055000000000004ba0f60c904253c295900000000000000002710ebc33047f1e5895e1be2e31530c062d5000000005074400022d40003e105500dc0000003da83dc000000049800062200010c800000030605118d472660731f08a84c283a08e0000c7a2aa00000000540002ec8e3800000000016bc6fa9e500023b8000000000000000043a04a9d4d38e1703ce88688c63e034323012c03b54ed97f84ee6b72b98bbd3e0205360234864e35100019e01cc4252a5a1680004084fa013c6b896806c9eb0a60252315049d35e0002600174c382ea0000624db0234000004c1f202f125a3882e44903d21bc8f8815d02d25c0af61bf161a44413407e35893e8fd667b1049d6818a95039d8e6448c0001da25dcd183af3d1a17c46a7474049ce0bdc53e3c0a6d00001cc0000cbc0587f544916745ca0001f887e02963fe10e13340100972bd17ecac886f1c915489426fd226193400038c302a5bc83a6e700007280007934f6a7a128a3d31712090b3e3f23b423986486d937b149cba091a324a114108948384253cf8263c00ca1d862400500004000001ae4319afd3f870500000002de3d5300063417c56d35e89fd3fa52a0f187440004b55029e7cb7e6943c400006040004dc0000ab4000000000106a1a620a02c47986304221218cb62bb1b4254c4ae9233241d992c83dd152a42107c55317595388361b716619080be6cf2c216451e033e316a0c46d43c40b02164e3a42223d1e603809dc00014443e82ac0b214e8e068891fa1f0c8a459b1ba869cb0a4bd15b1be4d264cc347170d23019d13194f40000001fe83580009fb214115096c8c8208a4e82ec1244af945509a05c0fc9a54ca24f04c591a90d68b6397815cad68a72f1090c9160020a40e001ce82324e896c9b01813fd237467e0e103806147c69c90ff1df0d462242d89da45d20c238c9748aee6ff4b623349405d328297dc2fe2493b1805001c997142a510b549fe139018c9bc7822c3a3847d075903c87a879607f0d283811ae1d04829754cae20a0e905dce588c91c210c923c1324bc034c5386ab210a33c0000af0000000f7c3c32321e3001a9c500000000da7db03c22188762d90000000ea239f4599acc00056910194c800015a0b1858800044500000005d80004018000f943490e394305b675c00012e93ae39d38b800134e81408c8b784421f549100000009d30002030a4265a30709b004e801359141885c3d6000197c92a34600009581247fb1301ea80984c51c590600521012fa0ca52664e002aa5c4f200b70000ee
  | 18 => 0x106c000000000110895a1dfa68109029f4128000b747354e890c070a00027b130d17e75d0a885b8ace41a0001fc4b9476d12d16346ce772238059c3b29870000e400000000001030000000000000134839a09b905cfa28ba0000bcc0002674c78f18b4489d318a824af20001b4800065495440280006260001fb1b40a3a96e000000032073006e8d8c4d43f94921f8c70245e11fa0c86d84f93171724d0400000023e400000000000000000000000000fe84f3000002c35e5f20000000e000eb16203f40ec000000000040289000000004cc81023119fce4a6cb077173400099600024340000184578a8cca45a942700013205a3000219852a643375a0fd23e00040c820c62e613107007000097d00023a400016d388a7340004ff09603a8c7e08700000012280ca2ea000042269c1d68f9492674c2da96252f458b42b9bb51ea61b2f1805cc3a78f3320a642280000001600e3e0002a3861d12a84
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd75cc5100067f65cc5100ce7c65cc510006df63cc51005edc63cc51000dfa70cc510005f970cc5100bdf6768c51001ef6768c51001df7758c510245f5758c51000777658c51023f74658c51001df7748c51001fb6748c510005f5748c51001fb5748c510005b5748c5100d5f5738c51005ef6638c51005ef4638c5101fdf6728c51000df6708c51000df4708c51001ef7608c51001ff3608c5100e7f2208c51005cff764c51000cfe764c5100d4fd764c51000cfc764c5100067f654c5100de7c654c510006df634c510006dc634c510005fb704c51000df8704c51000df4764c5100d6f4764c51000cf4764c510235f7754c510235f5754c51000777654c51022f74654c510005f7744c510005f5744c51001df7734c51001fd7734c510007d7634c51005ef6634c51005ef4634c510007d4634c5101fdf4724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100d7f0704c51001ef7604c51001ff3604c5100d7f2204c51000cfe76c851000cfc76c85100067f65c85100b67c65c8510006ef62c851002eec62c851000dfa70c8510005f970c851000df676c85100aef676c851000cf676c85101fdf775c8510225f575c85100077765c851021f7465c85101fdf774c8510005f574c85101fdf773c8510005f573c8510006f663c8510006f463c851001df672c85101fef762c8510007e762c85101fef562c85101ffe462c851000df670c85100aff270c85101fff170c851000df470c851001ef760c851001ff360c85100aff220c851002cff764851000cfe764851008cfd764851000cfc76485100067f65485100967c6548510005bf7448510005bc7448510006ef624851002eec6248510005fb704851000df8704851009df6760851001ef6760851001df7750851001f767508510215f5750851001f75750851000575750851000777650851020f74650851001df7740851001fb67408510005f5740851001fb57408510005b5740851001df7730851001fd67308510005f5730851001fd57308510005d57308510006f66308510006f463085100adf6720851001fe672085101fef762085101fef56208510007e742085101ffe4420851000df6700851001ff2700851000df2700851001ff1700851000df4700851001ef7600851001ff3600851007ff2200851001df8764811002ef8764811001cf876481100077b654811020778654811000dfb724811000feb7248110007eb624811002efa624811002ef86248110007e86248110207ea5248110207e95248110007ea3248110007e93248110007f3714811001dfa714811001df87148110007f0714811000efb614811000ff36148110207f25148110207f15148110007f24148110007f14148110007f23148110007f131481101fff321481101fff02148110
  | 1 => 0x89100067f65189100067c651891002eee6218910006ed6218910034ff76d0910004fe76d0910004fd76d0910034fc76d09100067f65d09101b67c65d0910006ef62d091002eec62d091001df671d0910005f571d091002cff7690910004fe7690910004fd769091002cfc76909100067f65909101a67c6590910006bf6490910036bc649091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101967c6550910005f7715091001df4715091002cff7610910004fe7610910004fd761091002cfc76109100257e75109100057d75109100067f65109101867c6510910006bf6410910036bc6410910006ef621091002eec621091001df67110910005f5711091000dfa7010910005f9701091005cff76cc910004fe76cc910004fd76cc91005cfc76cc9100067f65cc91014e7c65cc910006ef62cc91002eec62cc91001df671cc910005f571cc91002cff768c910004fe768c910004fd768c91002cfc768c9100067f658c91016e7c658c910006df638c910006dc638c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91015e7c654c910005bf744c910005bc744c910005f7714c91001df4714c91002cff760c910004fe760c910004fd760c91002cfc760c9100257e750c9100057d750c9100067f650c9101467c650c910006df630c91005edc630c910006ef620c91002eec620c91001df6710c910005f5710c91000dfa700c910005f9700c91000cfe76d051000cfc76d05100067f65d05101367c65d0510006bf64d0510036bc64d051000dfa70d0510005f970d05100fdf6769051001ef6769051001df77590510265f5759051000777659051025f74659051010df57490510036f66490510036f46490510005f573905101fdf67290510007b64290510007b4429051000df6709051000df4709051001ef7609051001ff3609051011ff22090510034ff765051000cfe765051010cfd765051000cfc76505100067f65505101167c6550510006bf6450510036bc6450510005ef7250510005ec725051001fb44150510005fb705051000df8705051001ff0105051000df47650510036f4765051000cf47650510255f77550510255f5755051000777655051024f74655051001df7745051001fb77450510007b76450510036f66450510036f46450510007b4645051024fb6545051024fb55450510005f77350510007b64350510007b44350510007e772505101fdf47250510007e47250510005e47250510007b74250510007b54250510007f3705051000df6705051000df4705051010ff0705051001ef7605051001ff3605051010fb7405051010fb5405051010ff2205051000cfe76cc51000cfc76cc5100257e75cc5100057
  | 2 => 0x5e7d7598d100047d7598d1005cfc7598d10034fe7498d10004fd7498d1005cfe7398d1002cfe7298d10004fd7298d100d4fd7198d1005ef57198d100f4fd7098d1005ef97098d100057f7558d100257c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d10005ec7258d100f5f77158d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d10034fc7458d10006bc7458d10034bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1002cfc7258d10006ec7258d1002cec7258d100f4ff7158d10006f77158d100d4ff7058d10006fb7058d100e4fe7618d100067f6518d100067c6518d10006dd6318d1005cff7518d10014fe7518d10004fd7518d1005cfc7518d10034fe7418d10004fd7418d1005ede7318d1002cfe7218d10004fd7218d1001cfe7118d1005ef57118d1001cfc7118d1001cff7018d1000cfe7018d1001cfd7018d1000cfc7018d1005edf3018d100bedd3018d10034ff76d0d10004fe76d0d10004fd76d0d10034fc76d0d100067f65d0d101f67c65d0d10006df63d0d10006dc63d0d1001df671d0d10005f571d0d1005cff7690d10004fe7690d10004fd7690d1005cfc7690d100067f6590d101ce7c6590d10006bf6490d10036bc6490d1001df67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101de7c6550d1005cff7610d10004fe7610d10004fd7610d1005cfc7610d100257e7510d100057d7510d100067f6510d101c67c6510d10006bf6410d10036bc6410d10006df6310d1005edc6310d1001df67110d10005f57110d1000dfa7010d10005f97010d1002cfe76d89100067f65d89100067c65d8910004ff75d8910014fe75d8910004fd75d8910014fc75d8910034fe74d8910004fd74d891005cfe73d8910004fd73d891001cfe71d891009ef571d891001cfc71d891001cff70d891000cfe70d891001cfd70d891000cfc70d891009eef20d891009eed20d89100257e75989100057d75989100067f65989100067c6598910006ef629891008df571989100057f75589100257c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc73589100adf77158910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf7458910034fc7458910006bc7458910034bc7458910004ff7358910006df7358910004df735891005cfc7358910006dc7358910004dc7358910006ef72589100acff7158910006f7715891008cff7058910006fb705891009cfe761
  | 3 => 0x7764c710295f7754c710295f5754c710005f7744c710005f5744c71001fd7734c71005ef6634c71001ef4634c710285f4724c710007d7324c710007d5324c71000df6704c71000df4704c71001df576c8710286f576c8710285f775c871028df575c8710285f774c8710005f574c8710285f773c8710005f573c8710006f663c871001ef463c871001fe672c871001ef762c8710286f562c871000df670c871000df470c871027d7e76d95100267e76d95100147e76d951026f7771d951026f7471d951026f7a20d95102777b10d951026f7610d951026f7410d951026f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100067c72d951026e7f71d95102767e71d951026e7d71d951026e7c71d95102767e41d95102767c41d95102767e31d95102767c31d95102767e21d95102767c21d951026e7f70d951026e7e70d951026e7d70d951026e7c70d951026e7f40d951026e7e40d951026e7d40d951026e7c40d951026e7f30d951026e7e30d951026e7d30d951026e7c30d951026e7f20d951026e7e20d951026e7d20d951026e7c20d951026e7f10d951026e7e10d951026e7d10d951026e7c10d9510034fe76d91100067f65d91100067c65d9110004ff75d9110014fe75d9110004fd75d9110014fc75d911005cfe73d9110004fd73d911002cfe72d9110004fd72d911001cfe71d911001cfc71d911001cff70d911000cfe70d911001cfd70d911000cfc70d911011ebf40d911011ebd40d91100257e75991100057d75991100067f65991100067c6599110006bf649911010df571991100057f75591100257c75591100067f65591100067c6559110005df7359110005dc7359110005ef7259110005ec725911012df77159110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110006be5459110006bd5459110004ff7359110006df7359110004df735911005cfc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef725911002cfc7259110006ec725911002cec725911012cff7159110006f7715911010cff7059110006fb705911011cfe76191100067f65191100067c6519110036be6419110006bd64191100067f65d8d100067c65d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10034fe74d8d10004fd74d8d1002cfe72d8d10004fd72d8d1001cff70d8d1001cfd70d8d100e6df30d8d100e6dd30d8d100257e7598d100057d7598d100067f6598d100067c6598d10006df6398d100d5f57198d1005cff7598d10014fe7598d1005e7e7598d100147e7598d10004fd7598d10
  | 4 => 0x8f1001edc3198f1001ef42198f1005edf3098f100f6dd3098f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f10034fc7458f1001edf7358f10004ff7258f1002cfc7258f1001cff7158f1000cfe7158f1001cfd7158f1000cfc7158f1001ede3158f1001edc3158f100d6df3058f100d6dd3058f10034ff76d0f1001cfe76d0f10004fd76d0f1001cfc76d0f1001df671d0f10005f571d0f1005cff7690f1001cfe7690f10004fd7690f1001cfc7690f10036be6490f10006bd6490f1001df67190f10005f57190f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f1001df67150f1005cff7610f1001cfe7610f10004fd7610f1001cfc7610f1003d7e7510f100057d7510f10036be6410f10006bd6410f1001df67110f10005f57110f10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b10006bf7458b10004bf7458b10034fc7458b10006bc7458b10034bc7458b10004ff7358b1005cfc7358b1001eef7258b1001cff7158b1000cfe7158b1001cfd7158b1000cfc7158b1001ef47158b1000cf47158b1001eee2158b1001eec2158b1001ef42158b1001ee42158b1008eef2058b1008eed2058b1001efa1058b1001ef91058b10034ff76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b10036be64d0b10006bd64d0b1001df671d0b10005f571d0b102bfe421d0b1002cff7690b1001cfe7690b10004fd7690b1001cfc7690b102b6bf6490b10036bc6490b1001df47190b102b7b64190b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b10036be6450b10006bd6450b10005f77150b1001df47150b1002cff7610b1001cfe7610b10004fd7610b1001cfc7610b1003d7e7510b100057d7510b102aebf6410b10036bc6410b1001df67110b10005f57110b102afb64110b102afe42110b1005cff76ccb1001cfe76ccb10004fd76ccb1001cfc76ccb1005ede63ccb10006dd63ccb1001df671ccb10005f571ccb1002cff768cb1001cfe768cb10004fd768cb1001cfc768cb1001df4718cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb10005bf744cb10005bc744cb10006de634cb10006dd634cb10005f7714cb1001df4714cb1002cff760cb1001cfe760cb10004fd760cb1001cfc760cb1003d7e750cb100057d750cb1001df6710cb10005f5710cb1001df77650710006f776507102a5f775507102a5f5755071001fb7745071001fb76450710036f6645071001ef4645071001fb4645071029fb6545071029fb55450710005f77350710007b64350710007b44350710007e77250710285f47250710007e47250710005e47250710007b74250710007b5425071000df6705071000df4705071010fb7405071010fb5405071001df7764c710006f
  | 5 => 0x2eef608c92002feb608c920167ea108c92005cff764c92000cfe764c920154fd764c92000cfc764c920005bf744c920005bc744c920006df634c920006dc634c920005f7714c920005f4714c920005fb704c92000df8704c92000dec764c920156ec764c92000cec764c9202c5ef754c9202c5ed754c920007af744c920007ac744c92002def734c92002fcf734c920007cf634c92005eee634c92005eec634c920007cc634c920007e7714c920007e4714c920007eb704c92000dee704c92000dec704c920157e8704c92002eef604c92002feb604c920157ea104c92001cfe76d8520004ff75d8520014fe75d8520004fd75d8520014fc75d8520034fe74d8520004fd74d852005cfe73d8520004fd73d852000cfe70d852002cfd70d852000cfc70d85200aef710d8520006f761985200057f75585200457c7558520005bf7458520005bc7458520005df7358520005dc7358520005be7418520005bd741852001ef66118520006f56118520004fe76d0520004fd76d0520034fc76d0520036be64d0520006bd64d0520004fe7690520004fd769052001cfc7690520006bf6490520036bc649052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520036be6450520006bd6450520005ef725052002dec7250520004fe7610520004fd761052001cfc7610520006bf6410520036bc641052000dfa7010520005f97010520004fe76cc520004fd76cc52005cfc76cc5200457e75cc5200057d75cc52002dee72cc520005ed72cc520007cd32cc520006f761cc52001ef461cc520004fe768c520004fd768c52001cfc768c520005be748c520005bd748c520006df638c520006dc638c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520007cd324c520004fe760c520004fd760c52001cfc760c520006df630c52005edc630c52002dee720c520005ed720c520006f7610c52001ef4610c52000dfa700c520005f9700c52000cfe7688520006f7618852001ef4618852000dfa7088520005f9708852000cfc7648520005bf7448520005bc7448520006f7614852001ef46148520005fb704852000df87048520004ff7559310014fe7559310004fd7559310014fc755931001ebf7459310006be5459310006bd5459310004ff735931005cfc7359310004ff725931002cfc725931001cff715931000cfe715931001cfd715931000cfc715931001ebe415931001ebc415931010ebf405931010ebd405931005cff7598f10014fe7598f1005e7e7598f100147e7598f10004fd7598f1005e7d7598f100047d7598f1005cfc7598f10034fe7498f10004fd7498f1001ede7398f1002cfe7298f10004fd7298f1000cfe7198f1001ef67198f1000cf67198f1000cfc7198f1001ede3198f1001ef6319
  | 6 => 0xe72d912002cfc72d912001cfe71d9120004fd71d912002cff70d912002cfd70d912019ebf40d912019ebd40d91200457e75991200057d7599120006bf649912018ded72991201adef7259120004ff7559120014fe7559120004fd7559120014fc7559120006bf7459120004ff735912005cfc73591201acff7259120006ef72591202d6be42591202d6bc4259120004ff715912001cfc715912018cff7059120006fb705912019cfe7619120036be6419120006bd6419120004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20034fe74d8d20004fd74d8d2001cfe71d8d20004fd71d8d2002cff70d8d2002cfd70d8d20166df30d8d20166dd30d8d20006df6398d20155ed7298d2005cff7598d20014fe7598d20004fd7598d2005cfc7598d20034fe7498d20004fd7498d2005cfe7398d20154fd7298d2005eed7298d2001cfe7198d20004fd7198d20174fd7098d2005ef97098d200057f7558d200457c7558d20005bf7458d20005bc7458d20175ef7258d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d20034fc7458d20006bc7458d20034bc7458d20006df7358d20174ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2001cfc7158d20006f47158d2001cf47158d20154ff7058d20006fb7058d20164fe7618d200457e7518d200057d7518d20006dd6318d2005cff7518d20014fe7518d2005e7e7518d200147e7518d20004fd7518d2005e7d7518d200047d7518d2005cfc7518d20034fe7418d20004fd7418d2005ede7318d2002cfe7218d2005eed7218d2002cfc7218d2001cfe7118d20004fd7118d2002cff7018d2002cfd7018d2005edf3018d2013edd3018d20034ff76d0d20004fe76d0d20004fd76d0d20034fc76d0d2005cff7690d20004fe7690d20004fd7690d2005cfc7690d20006bf6490d20036bc6490d2002dee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2005cff7610d20004fe7610d20004fd7610d2005cfc7610d200457e7510d200057d7510d20006bf6410d20036bc6410d2002dee7210d20005ed7210d2000dfa7010d20005f97010d2000cfe76d092000cfc76d0920006bf64d0920036bc64d092000dfa70d0920005f970d0920034ff765092000cfe765092018cfd765092000cfc7650920006bf6450920036bc6450920005fb705092000df8705092000cfe76cc92000cfc76cc920006df63cc92005edc63cc92000dfa70cc920005f970cc92013dee768c92002eee768c92002def758c9202cded758c920155ed738c92005eee638c92005eec638c92000dee708c92000dec708c920
  | 7 => 0x8f20004fd7598f2005cfc7598f20034fe7498f20004fd7498f2002ede7398f2000cfe7298f2002eee7298f2000cee7298f2000cfc7298f2002ede3298f2002eee3298f2002edc3298f2001cfe7198f20004fd7198f2005edf3098f20176dd3098f20004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f20034fc7458f2002edf7358f2002cff7258f2000cfe7258f2002cfd7258f2000cfc7258f2002ede3258f2002edc3258f20004ff7158f2001cfc7158f20156df3058f20156dd3058f20034ff76d0f2002cfe76d0f20004fd76d0f2002cfc76d0f201f67e65d0f200067d65d0f20006de63d0f20006dd63d0f2005cff7690f2002cfe7690f20004fd7690f2002cfc7690f201ce7e6590f200067d6590f20036be6490f20006bd6490f2002dee7290f20005ed7290f20004ff7650f2002cfe7650f20004fd7650f2002cfc7650f201de7e6550f200067d6550f2005cff7610f2002cfe7610f20004fd7610f2002cfc7610f2004d7e7510f200057d7510f201c67e6510f200067d6510f20036be6410f20006bd6410f2005ede6310f20006dd6310f2002dee7210f20005ed7210f2002def764cb20006ef764cb202ddef754cb202dded754cb2002f6e654cb2002f6d654cb20007af744cb20007ac744cb2002fcf734cb2005eee634cb2002eec634cb20007e7714cb20007e4714cb2000dee704cb2000dec704cb20004ff7558720014fe7558720004fd7558720014fc7558720004ff7458720034fc7458720004ff735872005cfc735872000cfc725872002ef7715872002ef7215872002ef4215872002efa205872002ef9205872008ef71058720034ff76d072002cfe76d0720004fd76d07201367e65d07200067d65d0720036be64d0720006bd64d072001cff769072002cfe7690720004fd76907201267e65907200067d6590720004ff7650720004fd765072002cfc76507201167e65507200067d6550720036be6450720006bd6450720005ef725072002dec725072001cff761072002cfe7610720004fd76107201067e65107200067d651072005cff76cc72002cfe76cc720004fd76cc72004d7e75cc7200057d75cc7200ce7e65cc7200067d65cc72005ede63cc720006dd63cc72002dee72cc720005ed72cc720007cd32cc72001cff768c72002cfe768c720004fd768c7200ee7e658c7200067d658c720005be748c720005bd748c720004ff764c720004fd764c72002cfc764c7200de7e654c7200067d654c720006de634c720006dd634c720007cd324c72001cff760c72002cfe760c720004fd760c7200c67e650c7200067d650c72002dee720c720005ed720c720034fe76d9120004ff75d9120014fe75d9120004fd75d9120014fc75d9120006be54d9120006bd54d912005cfe73d9120004fd73d912002cf
  | 8 => 0x6bf6450530036bc6450530005ef7250530005ec7250530004fe7610530004fd761053001cfc76105300067f65105301067c6510530006bf6410530036bc641053000dfa7010530005f970105300bcfe76cc5300557e75cc5300057d75cc5300067f65cc5300ce7c65cc530006bf64cc530006bc64cc53000cfe768c5300067f658c5300ee7c658c530005be748c530005bd748c530006bf648c530006bc648c530006f7618c53001ef4618c53000dfa708c530005f9708c53000cfc764c5300067f654c5300de7c654c530006bf644c530006bc644c530006f7614c53001ef4614c530005fb704c53000df8704c5300f4fe760c5300067f650c5300c67c650c530006bf640c530006bc640c530004fe76c8530004fd76c853002cfc76c85300067f65c85300b67c65c8530006bf64c8530006bc64c8530006f761c853001ef461c8530004fe7688530004fd768853001cfc76885300067f65885300a67c6588530006bf6488530006bc6488530006ef628853002eec6288530004ff7648530004fe7648530004fc76485300067f65485300967c6548530005bf7448530005bc7448530006bf6448530006bc6448530004fe7608530004fd760853001cfc76085300557e75085300057d75085300067f65085300867c6508530005be7408530005bd7408530006bf6408530006bc6408530005de7308530005dd7308530006ef620853002eec6208530006f7610853001ef4610853000dfa7008530005f9700853000dfa76cc13000efa76cc13000cfa76cc1300077b65cc1302ef7865cc130007bb64cc130007b864cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc13005fda53cc1302efd953cc1300067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c735972002e7f725972002e7e725972002e7d725972002e7c725972002e7f425972002e7e425972002e7d425972002e7c425972002e7f325972002e7e325972002e7d325972002e7c32597200067f71597200067e71597200067d71597200067c715972002e7f215972002e7e215972002e7d215972002e7c21597202e67f70597202e67e70597202e67d70597202e67c70597202e67f40597202e67e40597202e67d40597202e67c40597202e67f30597202e67e30597202e67d30597202e67c305972002e7f205972002e7e205972002e7d205972002e7c20597202e67f10597202e67e10597202e67d10597202e67c1059720004ff7559320014fe7559320004fd7559320014fc755932002ebf7459320004ff735932005cfc735932002cff725932000cfe725932002cfd725932000cfc725932002ebe425932002ebc4259320004ff715932001cfc715932018ebf405932018ebd405932005cff7598f20014fe759
  | 9 => 0xf6510d301c67c6510d30006bf6410d30036bc6410d3002cfe76d89300067f65d89300067c65d8930006bf64d8930006bc64d8930004ff75d8930014fe75d8930004fd75d8930014fc75d8930034fe74d8930004fd74d893001cfe71d8930004fd71d8930176ef20d89300557e75989300057d75989300067f65989300067c6598930005be7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300557c75589300067f65589300067c6558930005bf7458930005bc7458930006bf6458930006bc6458930005f77158930005f471589300067f65189300067c6518930006bf6418930006bc641893002eee6218930006ed6218930004fe76d0930004fd76d0930034fc76d09300067f65d09301b67c65d0930006bf64d0930036bc64d0930004fe7690930004fd769093002cfc76909300067f65909301a67c6590930006bf6490930036bc6490930004ff7650930004fe7650930004fc76509300067f65509301967c6550930006bf6450930036bc6450930004fe7610930004fd761093002cfc76109300557e75109300057d75109300067f65109301867c6510930006bf6410930036bc6410930005de7310930005dd731093000dfa7010930005f9701093013cfe76cc9300067f65cc93014e7c65cc930006bf64cc930006bc64cc93005fd830cc93000cfe768c9300067f658c93016e7c658c930006bf648c930006bc648c930006ef628c93002eec628c93000dfa708c930005f9708c93000cfc764c9300067f654c93015e7c654c930005bf744c930005bc744c930006bf644c930006bc644c930006ef624c93002eec624c930005f7714c930005f4714c930005fb704c93000df8704c930157d8304c930174fe760c9300557e750c9300057d750c9300067f650c9301467c650c930006bf640c930006bc640c93001cfe76d85300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d8530014fe75d8530004fd75d8530014fc75d8530034fe74d8530004fd74d853002cfe72d8530004fd72d85300f6f710d85300557e75985300057d75985300067f65985300067c6598530005be7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300557c75585300067f65585300067c6558530005bf7458530005bc7458530006bf6458530006bc6458530005ef7258530005ec72585300067f65185300067c6518530006bf6418530006bc641853001ef66118530006f56118530004fe76d0530004fd76d0530034fc76d05300067f65d05301367c65d0530006bf64d0530036bc64d0530004fe7690530004fd769053001cfc76905300067f65905301267c6590530006bf6490530036bc6490530004ff7650530004fe7650530004fc76505300067f65505301167c6550530
  | 10 => 0x91300079d53d91301e79e30d91301e79c30d91301e7b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d91301e6bf73d91301e6bd73d9130006bf53d9130006be53d9130006bd53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d91301e6bf70d91301e6be70d91301e6bd70d91301e6bc70d91301e6bf50d91301e6be50d91301e6bd50d91301e6bc50d91301e6bf30d91301e6be30d91301e6bc30d91301e6bf20d91301e6be20d91301e6bd20d91301e6bc20d91301e6bf10d91301e6be10d91301e6bd10d91301e6bc10d91300557e75991300057d75991300067f65991300067c6599130006bf64991301d5dd73991300057f75591300557c75591300067f65591300067c65591301eddf7359130004ff75591300067f75591300047f7559130014fe7559130004fd7559130014fc75591300067c75591300147c7559130006bf74591301ecff7359130006df7359130004ff725913002cfc7259130004ff715913001cfc71591301d4ff7059130006fb70591301e4fe76191300067f65191300067c6519130036be6419130006bd64191301e5be7619130006be76191301e4be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c65191300079e53191300079d53191301bf9e30191301bf9c30191301bfb83019130036bf7519130036be7519130036bd7519130036bc7519130036bf7319130036bd7319130006bf5319130006be5319130006bd5319130006bc5319130036bf7219130036be7219130036bd7219130036bc7219130006bf5219130006be5219130006bd5219130006bc5219130036bf7119130036be7119130036bd7119130036bc7119130006bf5119130006be5119130006bd5119130006bc5119130036bf7019130036be7019130036bd7019130036bc70191301bebf50191301bebe50191301bebd50191301bebc50191301bebf30191301bebe30191301bebd30191301bebc30191301bebf20191301bebe20191301bebd20191301bebc20191301bebf10191301bebe10191301bebd10191301bebc101913000cfe76d0d3000cfc76d0d300067f65d0d301f67c65d0d30006bf64d0d30036bc64d0d3000dfa70d0d30005f970d0d301bcfe7690d300067f6590d301ce7c6590d301e6bf6490d30036bc6490d30034ff7650d3000cfe7650d301d4fd7650d3000cfc7650d300067f6550d301de7c6550d30006bf6450d30036bc6450d30005fb7050d3000df87050d301e4fe7610d300557e7510d300057d7510d300067
  | 11 => 0x4f77158b3001cfc7158b30006f47158b3001cf47158b30156ef2058b30034ff76d0b3005cfe76d0b30004fd76d0b3002cff7690b3005cfe7690b30004fd7690b30006bf6490b30036bc6490b30004ff7650b30004fd7650b3005cfc7650b3002cff7610b3005cfe7610b30004fd7610b300657e7510b300057d7510b30006bf6410b30036bc6410b3005dde7310b30005dd7310b30154fd768cb3002eec628cb30164ff764cb30005bf744cb30005bc744cb30005f7714cb30005f4714cb30005be7498730005bd749873005ef7619873001ef4619873001cff765873005ef46158730004ff7558730014fe7558730004fd7558730014fc7558730004ff7458730034fc745873000cfc7358730004ff725873002cfc725873005ef7315873005ef431587300d6f71058730034ff76d073005cfe76d0730004fd76d0730006bf64d0730036bc64d073001cff769073005cfe7690730004fd7690730004ff7650730004fd765073005cfc7650730006bf6450730036bc6450730005ef7250730005ec725073001cff761073005cfe7610730004fd76107300d4fd768c730005be748c730005bd748c73001ef4618c7300e4ff764c73002cff76c873005cfe76c8730004fd76c873001cff768873005cfe7688730004fd7688730004ff7648730004fd764873005cfc7648730005bf7448730005bc744873001cff760873005cfe7608730004fd76087300657e75087300057d7508730005be7408730005bd740873005dde7308730005dd730873001ef4610873000dfa7008730005f970087302fd7e76d95300567e76d95300147e76d95302f75f73d95302f75c73d95302f75e30d95302f75c30d95302f77830d95300067f74d95300067e74d95300067d74d95300067c74d95302f67f73d95300567e73d95302f67d73d95302f67c73d95300067f72d95300067e72d95300067d72d95300067c72d95300067f71d95300067e71d95300067d71d95300067c71d95302f67f70d95302f67e70d95302f67d70d95302f67c70d95302f67f40d95302f67e40d95302f67d40d95302f67c40d95302f67f30d95302f67e30d95302f67d30d95302f67c30d95302f67f20d95302f67e20d95302f67d20d95302f67c20d95302f67f10d95302f67e10d95302f67d10d95302f67c10d9530034fe76d91300067f65d91300067c65d9130004ff75d9130014fe75d9130004fd75d9130014fc75d9130006bf54d9130006be54d9130006bd54d9130006bc54d913005cfe73d913005cfc73d913002cfe72d9130004fd72d913001cfe71d9130004fd71d913005cff70d91301e4fd70d91301e6bf40d91301e6bd40d9130034be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91300079e53d
  | 12 => 0xe70d054000dbc70d0540036bf60d0540037bb60d054000cfe769054010dbd7490540006f7619054001ef4619054000dfa7090540005f9709054000cfc7650540005ef7250540005ec7250540006f7615054001ef46150540037b44150540005fb705054000df87050540037b8405054000dbc765054001ebc765054000cbc765054030dbf755054030dbd7550540306bf6550540306bd6550540005bf7350540006bc6350540007af72505402d5bc7250540007ac7250540005ac7250540006bf6250540035bf7150540037b77150540007b7615054001ebe615054001ebc6150540007b46150540007bb705054000dbe705054000dbc705054010fb87050540036bf6050540037bb6050540004fe76cc540004fd76cc54005cfc76cc54006d7e75cc5400057d75cc540035be74cc540005bd74cc540004fe768c540004fd768c54001cfc768c540035be748c540005bd748c540006df638c540006dc638c540004ff764c540004fe764c540004fc764c540035be744c540005bd744c540004fe760c540004fd760c54001cfc760c540035be740c540005bd740c540006df630c54005edc630c54000dfa700c540005f9700c540004fe76c8540004fd76c854002cfc76c85402d5bf74c8540035bc74c8540004fe7688540004fd768854001cfc7688540035be7488540005bd7488540006ef628854002eec6288540007ac4288540004ff7648540004fe7648540004fc7648540005bf7448540035bc7448540004fe7608540004fd760854001cfc760854006d7e75085400057d7508540035be7408540005bd7408540005de7308540005dd7308540006ef620854002eec62085402d7ac420854000dfa7008540005f9700854005cff75d9330014fe75d9330004fd75d933005cfc75d9330006be54d9330006bd54d933005cfe73d933005ede73d933002cfe72d9330004fd72d933001cfe71d9330004fd71d933005ef970d93301e6be40d93301e6bc40d93301d4fd769933005ebf649933005ebc6499330034ff765933005ebc6459330004ff7559330014fe7559330004fd7559330014fc755933005ebf7459330034ff735933000cfe7359330034fd735933000cfc735933005ebe435933005ebc4359330004ff725933002cfc7259330004ff715933001cfc71593301d6bf40593301d6bd40593301d4fd76d0f3005ebf64d0f3005ebc64d0f301ecff7650f3005ebf6450f3005ebc6450f3005eef6298b3002eec6298b3002cff7658b30005bf7458b30005bc7458b3005eec6258b30005f77158b30005f47158b30004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b30006bf7458b30004bf7458b30034fc7458b30006bc7458b30034bc7458b3000cfc7358b3005eef3258b3005eec3258b30004ff7158b30006f77158b30
  | 13 => 0xd4000dbc70d0d40036bf60d0d40037bb60d0d4000cfe7690d401d5bd7490d401e6bf6490d40006df6390d4005edc6390d4000dfa7090d40005f97090d4000cfc7650d40006df6350d40006dc6350d40005fb7050d4000df87050d4000dbc7650d401d6bc7650d4000cbc7650d40345bf7550d40345bd7550d40035bf7350d400379f7350d400079f6350d4005ebc6350d400079c6350d400069c6350d402d5bc7250d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d401d7b87050d40036bf6050d40037bb6050d4002cfe76d8940004ff75d8940014fe75d8940004fd75d8940014fc75d89401aebd74d894005cfe73d8940004fd73d894001cfe71d8940004fd71d8940034fd70d89401aeef20d894006d7e75989400057d7598940005de7398940005dd7398940006ef629894002eee6218940006ed621894000cfe7690940006ef629094002eec629094000dfa7090940005f9709094000dbe769094019ebe769094000cbe76909402d5bf759094033dbd7590940336bf6590940336bd6590940005bd7390940006bc6390940035be72909402d6bf6290940007af62909402d7ac6290940005bd71909402b6bc619094000dbe709094019fba709094000dba70909402d7b9709094000dbc7090940036bf6090940037bb609094000cfc7650940006ef625094002eec6250940005fb705094000df87050940037b840509401adbe7610940036be7610940035bf75109400373e751094032dbd75109400373d75109400053d7510940326bf6510940326bd6510940005bd7310940006bc631094019dbe7210940037ae72109402d6bf6210940005bd71109402aebc611094000dbe701094000dbc7010940036bf6010940037bb6010940004fe76cc940004fd76cc94005cfc76cc940035be74cc940005bd74cc940006df63cc94005edc63cc940004fe768c940004fd768c94002cfc768c9402d5bf748c940035bc748c940004ff764c940004fe764c940004fc764c940005bf744c940035bc744c940006df634c940006dc634c940005f7714c940005f4714c940004fe760c940004fd760c94002cfc760c94006d7e750c9400057d750c940035be740c940005bd740c94000dfa700c940005f9700c94001cfe76d8540004ff75d8540014fe75d8540004fd75d8540014fc75d8540006be54d8540006bd54d854005cfe73d8540004fd73d854002cfe72d8540004fd72d8540034fd70d854012ef710d8540006f761985400057f755854006d7c7558540005df7358540005dc7358540005ef7258540005ec725854001ef66118540006f561185400fdbe76d0540036be76d0540035bf75d054031dbd75d0540316bf65d0540316bd65d0540005bd73d0540006bc63d05402d5be72d0540006bf62d054001ebe61d054001ebc61d054000db
  | 14 => 0x4fd764cb40034fc764cb4015e7e654cb400067d654cb40005bf744cb40035bc744cb40005f7714cb40005f4714cb4002cff760cb40034fe760cb40004fd760cb400757e750cb400057d750cb401467e650cb400067d650cb40035be740cb40005bd740cb40004ff7558740014fe7558740004fd7558740014fc755874000cfc7458740036be5458740006bd5458740004ff735874005cfc7358740004ff725874002cfc7258740036f77158740036f74158740036f4415874010ef71058740035bf7650740006bf765074036dbf755074036dbd7550740036bf65507400373e6550740366bd65507400373d65507400063d6550740005bf7350740006be6350740007af7250740355bc7250740007ac7250740005ac7250740006bd6250740037b77150740037b7615074001ebe615074001ebc6150740037b4615074000dbe705074000dbc705074005cff76cc740034fe76cc740004fd76cc7400757e75cc7400057d75cc7400ce7e65cc7400067d65cc740035be74cc740005bd74cc74001cff768c740034fe768c740004fd768c7400ee7e658c7400067d658c740035be748c740005bd748c740004ff764c740004fd764c740034fc764c7400de7e654c7400067d654c740035be744c740005bd744c74001cff760c740034fe760c740004fd760c7400c67e650c7400067d650c740035be740c740005bd740c74002cff76c8740034fe76c8740004fd76c87400b67e65c87400067d65c8740355bf74c8740035bc74c874001cff7688740034fe7688740004fd76887400a67e65887400067d6588740035be7488740005bd748874035fac4288740004ff7648740004fd7648740034fc76487400967e65487400067d6548740005bf7448740035bc744874001cff7608740034fe7608740004fd76087400757e75087400057d75087400867e65087400067d6508740035be7408740005bd7408740005de7308740005dd7308740357ac420874000dfa7008740005f97008740004ff75d8d40014fe75d8d40004fd75d8d40014fc75d8d40006df53d8d40006dc53d8d4002cfe72d8d40004fd72d8d4001cfe71d8d40004fd71d8d40034fd70d8d401eedf30d8d40006df6398d400057f7558d4006d7c7558d4006d7e7518d400057d7518d40006dd6318d4005cff7518d40014fe7518d4005e7e7518d400147e7518d40004fd7518d4005e7d7518d400047d7518d4005cfc7518d4005ebd7418d40006be5418d40006bd5418d40006df5318d4005edc5318d4002cfe7218d40004fd7218d4001cfe7118d40004fd7118d4005cff7018d40034fd7018d401bebe4018d401bebc4018d4005edf3018d401bedd3018d401bdbe76d0d40036be76d0d401bcbe76d0d40035bf75d0d4034dbd75d0d4005ebc63d0d402d5be72d0d40005bd71d0d4000dbe70d
  | 15 => 0x9325802102ef8325802101efb715802101efa715802101ef8715802101efb515802101efa515802101ef9515802101ef8515802101efb415802101efa415802101ef9415802101ef8415802101efb315802101efa315802101ef9315802101ef8315802101efb215802101efa215802101ef9215802101ef821580210367f74597400367e74597400367d74597400367c74597400067f73597400067e73597400067d73597400067c73597400367f43597400367e43597400367d43597400367c43597400067f72597400067e72597400067d72597400067c72597400367f42597400367e42597400367d42597400367c42597400363c42597400067f71597400067e71597400067d71597400067c71597400367f41597400363f41597400367e41597400367d41597400367c415974038e7f705974038e7e705974038e7d705974038e7c70597400367f40597400367e40597400367d40597400367c405974038e7f305974038e7e305974038e7d305974038e7c305974038e7f205974038e7e205974038e7d205974038e7c205974038e7f105974038e7e105974038e7d105974038e7c105974005cff7598f40014fe7598f40004fd7598f4005cfc7598f4000cfe7498f4005ebe7498f4000cbe7498f4000cfc7498f40036be5498f40006bd5498f4005ede7398f4005ebf4398f40036df4398f4005edc4398f4002cfe7298f40004fd7298f40036bc4298f4001cfe7198f40004fd7198f40036bf4198f401e6be4098f40036bc4098f4005edf3098f401e6dd3098f40004ff7558f40014fe7558f40004fd7558f40014fc7558f4000cfc7458f40036df7358f40036df4358f40036dc4358f40004ff7258f4002cfc7258f40004ff7158f4001cfc7158f401d6df3058f40035bf7650f40006bf7650f401e4bf7650f40385bf7550f40385bd7550f400373e6550f400373d6550f400379f7350f4005ebe6350f40355bc7250f40005bf7150f4000dbe7050f4000dbc7050f40004ff7558b40014fe7558b40004fd7558b40014fc7558b4000cfc7458b40036bc7458b4000cbc7458b40004ff7358b4005cfc7358b40036ef7258b40036ef4258b40036bc4258b40036ec4258b40004ff7158b4001cfc7158b40036bf4158b4018eef2058b40035bd7690b40356bd7690b40355bf7590b4037dbd7590b40036bf6590b400373e6590b40376bd6590b400373d6590b400063d6590b40005bd7390b40006be6390b40037ae7290b40036bf6290b40356bd6290b40005bd7190b402b6be6190b4000dbe7090b4000dbc7090b4005cff76ccb40034fe76ccb40004fd76ccb4014e7e65ccb400067d65ccb40035be74ccb40005bd74ccb4002cff768cb40034fe768cb40004fd768cb4016e7e658cb400067d658cb40355bf748cb40035bc748cb40004ff764cb40
  | 16 => 0x8c2101edf1058c2101ed71058c2101ede1058c2101edd1058c2101edc1058c21034ff76d0c2101cfe76d0c21004fd76d0c2101cfc76d0c211f67e65d0c210067d65d0c21036be64d0c21006bd64d0c21006de63d0c21006dd63d0c2101df671d0c21005f571d0c211eefa60d0c2105cff7690c2101cfe7690c21004fd7690c2101cfc7690c211ce7e6590c210067d6590c21036be6490c21006bd6490c2105ede6390c21006dd6390c2102dee7290c21005ed7290c213b7ac4290c211e6fa6090c21004ff7650c2101cfe7650c21004fd7650c2101cfc7650c211de7e6550c210067d6550c21036be6450c21006bd6450c21006de6350c21006dd6350c21005ef7250c2102dec7250c21005f77150c2101df47150c211d6fa6050c2105cff7610c2101cfe7610c21004fd7610c2101cfc7610c210857e7510c210057d7510c211c67e6510c210067d6510c21036be6410c21006bd6410c2105ede6310c21006dd6310c213afac4210c211befa6010c2102ded76d08213a6ed76d082102f6e65d082102f6d65d082102dee74d082102fae74d082102eef64d082102fae64d08213a6ed64d082102fad64d0821006ad64d082102fce63d082102fcd63d08212bdef71d08212bded71d08212beee61d082102fe661d08212bfaf41d08212bfad41d08212bfe431d082102fea60d082102fe960d082101df576cc421006f576cc42139f7675cc4210077575cc42101f7665cc42101f7565cc42101fb664cc42101fb564cc42101df673cc42101fd673cc42101ef763cc42101fd663cc421006f563cc42101fd563cc421006d563cc421395f772cc421395f572cc421396f662cc42101fe662cc421007e742cc421397e442cc421397d732cc421397d532cc421005f570cc42101ff260cc42101ff160cc421004ff7558021014fe7558021004fd7558021014fc7558021004ff7458021034fc7458021004ff735802105cfc735802100cfd725802100cfd715802101cff705802101efb7058021006fb505802107efa5058021006f9505802107ef8505802107efa405802107ef8405802107efa305802107ef8305802102efb205802102ef8205802101efb105802101ef81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802102efb725802102efa725802102ef8725802102efb525802102efa525802102ef9525802102ef8525802102efb425802102efa425802102ef9425802102ef8425802102efb325802102efa325802102ef
  | 17 => 0x1eb7105902101ebe105902101ebd105902101ebc105902105cff7598c21014fe7598c21004fd7598c2105cfc7598c21034fe7498c21004fd7498c2101cfe7398c2101ede7398c21006df5398c2105ede5398c21006dd5398c2105edc5398c2102cfe7298c2102cfc7298c2102ede3298c2102edc3298c2101cfe7198c2101cfc7198c2101ede3198c2101edc3198c2100cfe7098c21004fd7098c2100cfc7098c21006de3098c2105edc3098c2105edf7598c21006de7598c21006dd7598c2105edc7598c2105edf7498c21006de7498c21006dd7498c2105edc7498c21006df5498c21006de5498c21006dd5498c21006dc5498c2102edf7298c2102ede7298c2102edd7298c2102edc7298c2102edf5298c2102ede5298c2102edd5298c2102edc5298c2102edf4298c2102ede4298c2102edd4298c2102edc4298c2101edf7198c2101ede7198c2101edd7198c2101edc7198c2101edf5198c2101ede5198c2101edd5198c2101edc5198c2101edf4198c2101ede4198c2101edd4198c2101edc4198c2101edf2198c2101ede2198c2101edd2198c2101edc2198c2105edf7098c21006de7098c21006dd7098c2105edc7098c21006df5098c21006de5098c21006dd5098c21006dc5098c21006de4098c21006dc4098c2102edf2098c2102ede2098c2102edd2098c2102edc2098c2101edf1098c2101ede1098c2101edd1098c2101edc1098c21004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c21034fc7458c2101cff7358c2101edf7358c21006df5358c21006de5358c21006dd5358c21006dc5358c2102cfe7258c2102cfc7258c2102ede3258c2102edc3258c2101cfe7158c2101cfc7158c2101ef47158c2101cf47158c2101ede3158c2101edc3158c2101ef43158c21004ff7058c2100cfe7058c2100cfc7058c21006de3058c21006dc3058c2101ef71058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2102edf7258c2102ede7258c2102edd7258c2102edc7258c2102edf5258c2102ede5258c2102edd5258c2102edc5258c2102edf4258c2102ede4258c2102edd4258c2102edc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101ed47158c2101edf5158c2101ede5158c2101edd5158c2101edc5158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ede2158c2101edd2158c2101edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006de4058c21006dc4058c2102edf2058c2102ede2058c2102edd2058c2102edc205
  | 18 => 0xe415942101e7d415942101e7c415942101e7f315942101e7e315942101e7d315942101e7c315942101e7f215942101e7e215942101e7d215942101e7c21594210067f70594210067e70594210067d70594210067c70594210067e40594210067c40594210067e30594210067c305942102e7f205942102e7e205942102e7d205942102e7c205942101e7f105942101e77105942101e7e105942101e7d105942101e7c1059421036bf7599021036be7599021036bd7599021036bc7599021036bf7399021036be7399021036bd7399021036bc7399021006bf5399021006be5399021006bd5399021006bc539902102ebf729902102ebe729902102ebd729902102ebc729902102ebf529902102ebe529902102ebd529902102ebc529902102ebf329902102ebe329902102ebd329902102ebc329902101ebf719902101ebe719902101ebd719902101ebc719902101ebf519902101ebe519902101ebd519902101ebc519902101ebf319902101ebe319902101ebd319902101ebc319902101ebf219902101ebe219902101ebd219902101ebc2199021036bf7099021036be7099021036bd7099021036bc7099021006bf5099021006be5099021006bd5099021006bc5099021006be3099021006bc309902102ebf209902102ebe209902102ebd209902102ebc209902101ebf109902101ebe109902101ebd109902101ebc1099021004ff7559021014fe7559021004fd7559021014fc755902101cff745902101ebf7459021006bf5459021006be5459021006bd5459021006bc5459021004ff735902105cfc735902102cfe725902102cfc725902102eec725902102cec725902102ebe425902102ebc425902102eec425902101cfe715902101cfc715902101ebe415902101ebc4159021004ff705902100cfe705902100cfc7059021006be4059021006bc405902101ef71059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc535902102ebf725902102ebe725902102ebd725902102ebc725902102eac725902102ebf525902102ebe525902102ebd525902102ebc525902102ebf325902102ebe325902102ebd325902102ebc325902101ebf715902101ebe715902101ebd715902101ebc715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021006be3059021006bc305902102ebf205902102ebe205902102ebd205902102ebc205902101ebf1059021
  | 19 => 0x8d21004f77158d21004ff7058d2100cfe7058d2100cfc7058d21004fe7618d21006bf6418d21006bc6418d21006dd6318d2105cff7518d21014fe7518d21004fd7518d2105cfc7518d21034fe7418d21004fd7418d2105ede7318d2105ede5318d21006dd5318d213bef72118d213bef42118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d2105edc3018d21034ff76d0d21004fe76d0d21004fd76d0d21034fc76d0d21006bf64d0d21036bc64d0d2105cff7690d21004fe7690d21004fd7690d2105cfc7690d21006bf6490d21036bc6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21036bc6450d2105cff7610d21004fe7610d21004fd7610d2105cfc7610d210957e7510d210057d7510d21006bf6410d21036bc6410d2102dee7210d21005ed7210d2101df67110d21005f57110d2101cfe76d092101cfc76d0921006bf64d0921036bc64d092101df671d0921005f571d092102fe421d092101cfc7650921006bf6450921036bc6450921005f7715092101df4715092101cfe76cc921006bf64cc921006bc64cc921006df63cc92105edc63cc92101df671cc921005f571cc92101cfc764c921005bf744c921005bc744c921006bf644c921006bc644c921006df634c921006dc634c921005f7714c92101df4714c92102fe4214c92102cfe76d052102cfc76d0521006bf64d0521036bc64d052102dee72d0521005ed72d052101fe421d0521034ff7650521004fd765052102cfc7650521006bf6450521036bc6450521005ef725052102dec725052102cfe76cc5210957e75cc5210057d75cc521006bf64cc521006bc64cc521006df63cc52105edc63cc52102dee72cc521005ed72cc52105cff764c521004fd764c52102cfc764c521006bf644c521006bc644c521006df634c521006dc634c521005ef724c52102dec724c52101fe4214c52100cfe76d8121006bf64d8121006bc64d812108efa60d8121004ff75d8121014fe75d8121004fd75d8121014fc75d8121034fe74d8121004fd74d812105cfe73d8121004fd73d812101cfd72d812100cfc72d812102cfd71d812100cfc71d8121286f721d8121286f421d812108efa20d812108efa10d81210057f75581210957c7558121005bf7458121005bc7458121006bf6458121006bc6458121005df7358121005dc735812108ef860581210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c735942102e7f725942102e7e725942102e7d725942102e7c725942102e7f425942102e7e425942102e7d425942102e7c425942102e7f325942102e7e325942102e7d325942102e7c325942101e7f715942101e7e715942101e7d715942101e7c715942101e7f415942101e7
  | 20 => 0x3cebf21d91212b6be21d91212b6bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006be30d9121006bc30d91213cebf20d9121006be20d91213cebc20d91212b6bf10d9121006be10d91212b6bc10d9121006bf64991212beef6299121004ff7559121014fe7559121004fd7559121014fc7559121006bf7459121004ff735912105cfc7359121004ff7259121006ef7259121004ef7259121004ff7159121006f77159121004ff705912100cfe705912100cfc7059121004fe7619121036be6419121006bd64191212aeef6219121005be7619121006be7619121004be7619121006bf6519121006be6519121006bd6519121006bc65191213c7b721191212afae21191212afac21191213c7b42119121006be6019121006bc6019121036bf7519121036be7519121036bd7519121036bc7519121036bf7319121036be7319121036bd7319121036bc7319121006bf5319121006be5319121006bd5319121006bc5319121036bf7219121036be7219121036bd7219121036bc7219121006bf52191213c6be5219121006bd52191213c6bc52191213c6be32191213c6bc3219121036bf7119121036be7119121036bd7119121036bc7119121006bf51191212aebe5119121006bd51191212aebc51191212aebe31191212aebc31191213c6bf21191212aebe21191212aeae2119121006bd21191212aebc21191212aeac2119121036bf7019121036be7019121036bd7019121036bc7019121006bf5019121006be5019121006bd5019121006bc5019121006be3019121006bc30191213c6bf2019121006be20191213c6bc20191212aebf1019121006be10191212aebc1019121006bf64d8d21006bc64d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d21034fe74d8d21004fd74d8d21006de53d8d21006dd53d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d210957e7598d210057d7598d21005be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d2105cff7598d21014fe7598d2105e7e7598d210147e7598d21004fd7598d2105e7d7598d210047d7598d2105cfc7598d21034fe7498d2105ebe7498d21034be7498d21004fd7498d2105ebd7498d21004bd7498d2105cfe7398d21004fd7298d2105eed7298d21004fd7198d2105ef57198d21396f72198d2100cfe7098d21004fd7098d2100cfc7098d21005bf7458d21005bc7458d21006bf6458d21006bc6458d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21006bf7458d21004bf7458d21034fc7458d21006bc7458d21034bc7458d21006df7358d21004ff7258d21006ef7258d21004ff7158d21006f7715
  | 21 => 0xc7098e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e21034fc7458e2101edf7358e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e2100cfe7058e2100cfc7058e21034ff76d0e2101cfe76d0e21004fd76d0e2101cfc76d0e2105cff7690e2101cfe7690e21004fd7690e2101cfc7690e21036be6490e21006bd6490e2102dee7290e21005ed7290e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e21005ef7250e2102dec7250e2105cff7610e2101cfe7610e21004fd7610e2101cfc7610e210a57e7510e210057d7510e21036be6410e21006bd6410e2101df67110e21005f57110e21036be64d0a21006bd64d0a2101df671d0a21005f571d0a212bded76d0a2135eed76d0a2102dee74d0a212beef64d0a212bfae64d0a2135eed64d0a212bfad64d0a212bfe671d0a212bded71d0a2135fe571d0a2102eee61d0a212bfaf41d0a212bfad41d0a21034ff7650a21036be6450a21006bd6450a2102fac4250a21005f77150a2101df47150a212aded7610a2102eed7610a2102f6e7510a2102f6d7510a2102fae7410a212aeef6410a212afaf6410a2135eed6410a212afac6410a2135fae5410a213d7ad5410a21007ae4310a2135fac4310a2102def7110a212aded7110a2102fe66110a212afae4110a212afac4110a2105ede63cca21006dd63cca2101df671cca21005f571cca21005bf744ca21005bc744ca21006de634ca21006dd634ca21005f7714ca2101df4714ca21004ff75582210067f75582210047f7558221014fe7558221004fd7558221014fc75582210067c75582210147c7558221004ff7458221034fc7458221004ff735822105cfc735822101cfc71582211fef7215822101ef4215822101efb705822109efa205822101efb105822101ef81058221034fe76d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121006bf54d9121006be54d9121006bd54d9121006bc54d912105cfe73d9121004fd73d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121034be76d9121006bf65d9121006be65d9121006bd65d9121006bc65d91213cfb721d91212b7ae21d91212b7ac21d91213cfb421d9121006be60d9121006bc60d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d91212b6bf72d91213cebe72d9121006bd72d91213cebc72d9121006bf52d91213cebe52d9121006bd52d91213cebc52d91213cebe32d91213cebc32d91213cebf71d91212b6be71d9121006bd71d91212b6bc71d9121006bf51d91212b6be51d9121006bd51d91212b6bc51d91212b6be31d91212b6bc31d9121
  | 22 => 0x80310befa405803105efb305803105ef830580310befa205803101efb105803101ef81058031004ff7559321014fe7559321004fd7559321014fc755932102ebf7459321004ff735932105cfc735932101cfc725932102ebe425932102ebc4259321004ff705932100cfe705932100cfc705932105cff7598f21014fe7598f21004fd7598f2105cfc7598f21034fe7498f21004fd7498f2102ede7398f2101cfe7298f2102ede3298f2102edc3298f2100cfe7098f21004fd7098f2100cfc7098f21004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f21006bf7458f21004bf7458f21034fc7458f21006bc7458f21034bc7458f2102edf7358f2101cfc7258f2102ede3258f2102edc3258f21006f77158f21004ff7058f2100cfe7058f2100cfc7058f21034ff76d0f2102cfe76d0f21004fd76d0f2102cfc76d0f2101df671d0f21005f571d0f2105cff7690f2102cfe7690f21004fd7690f2102cfc7690f213b6bf6490f21036bc6490f21004ff7650f2102cfe7650f21004fd7650f2102cfc7650f21005f77150f2101df47150f2105cff7610f2102cfe7610f21004fd7610f2102cfc7610f210b57e7510f210057d7510f213aebf6410f21036bc6410f2102dee7210f21005ed7210f21036be64d0721006bd64d072102dee72d0721005ed72d0721034ff7650721036be6450721006bd6450721005ef725072102dec725072101fb441507210b57e75cc7210057d75cc72105ede63cc721006dd63cc72102dee72cc721005ed72cc721395f576cc721006f576cc7213df7675cc7210077575cc72101df673cc721396f763cc721397d663cc721006f563cc721397d563cc721397e672cc721395f572cc721007e572cc72101ef662cc721397d732cc721397d532cc721005f570cc721006de634c721006dd634c721005ef724c72102dec724c7213bdf5760c72101ef5760c72101fd6730c7213bef7630c721006f5630c72101df7720c7213bdf5720c72101fe6620c721005f5700c721004ff7558321014fe7558321004fd7558321014fc7558321004ff7458321034fc7458321004ff735832105cfc735832101cfc725832102efb705832102efb205832102ef820583210aefa1058321004ff7559221014fe7559221004fd7559221014fc755922101ebf7459221006be5459221006bd5459221004ff735922105cfc7359221006ef725922101cfc715922101ebe415922101ebc4159221004ff705922100cfe705922100cfc705922105cff7598e21014fe7598e2105e7e7598e210147e7598e21004fd7598e2105e7d7598e210047d7598e2105cfc7598e21034fe7498e21004fd7498e2101ede7398e2101cfe7198e2101ede3198e2101edc3198e21396f72198e2101ef42198e2100cfe7098e21004fd7098e2100cf
  | 23 => 0x1dde714c93101ddc714c931007d4714c931004fe760c9310dd7e750c9310057d750c9313f5de730c931004fe76d053105cfc76d0531006bf64d0531036bc64d0531005de73d0531005dd73d0531034ff7650531004fd7650531034fc7650531006bf6450531036bc6450531005df7350531005dc7350531005ef7250531005ec725053101fb441505310dd7e75cc5310057d75cc53101dde73cc53101edf63cc53105f7675cc53105f7575cc53101df673cc53101ef763cc53101fd763cc531396f462cc53105fd732cc531007d532cc531005f570cc53100cfe76d81310d6fa60d8131004ff75d8131014fe75d8131004fd75d8131014fc75d8131034fe74d8131004fd74d813101cfd73d813102cfe72d8131004fd72d81310d6fa30d81310d6fa10d81310057f75581310dd7c7558131005bf7458131005bc7458131005ef7258131005ec72581310d6f86058131004ff7559031014fe7559031004fd7559031014fc755903101cff745903101ebf7459031006be5459031006bd545903105cfe735903105cfc735903105ebe435903105ebc4359031004ff725903102cfc725903101cfe715903101cfc715903101ebe415903101ebc4159031004ff705903100cfe705903100cfc7059031004fd76d0c31004ff7650c31004ff7558831014fe7558831004fd7558831014fc7558831004ff7458831006bf7458831004bf7458831034fc7458831006bc7458831034bc745883101eef7258831006ee5258831006ed525883105eef325883105eec325883101ef4715883101edf315883101edd315883101eee215883101eec215883101ef4215883101ee42158831004ff705883100cfe705883100cfc7058831034ff76d083101cfe76d0831004fd76d0831036be64d0831006bd64d083101df671d0831005f571d083102cff769083101cfe7690831004fd76908312b6bf6490831036bc649083102eee6290831006ed6290831004ff7650831004fd765083101cfc7650831036be6450831006bd645083102eee6250831006ed6250831005f7715083101df4715083102cff761083101cfe7610831004fd76108310c57e75108310057d75108312aebf6410831036bc64108312afe42110831004fd768c83101df4718c831004ff764c831005bf744c831005bc744c8313eede634c831005f7714c83101df4714c83101df7764c431006f7764c431004f7764c43101df7734c43101fd7734c43105ef6634c43101fd6634c43105fd6534c4313e7d5534c4313bdf4724c431004ff75580310067f75580310047f7558031014fe7558031004fd7558031014fc75580310067c75580310147c7558031004ff7458031034fc7458031004ff725803102cfc725803101ef63158031006f5315803101ef4215803101efb70580310befa5058031006f9505
  | 24 => 0xe644ca31006bd644ca3102eee624ca31006ed624ca31005f7714ca3101df4714ca310ed7e750ca310057d750ca31006be640ca31006bd640ca3101df576cc63105ef576cc63105f7675cc63105f7575cc63101fb664cc63101fb564cc63101fd673cc63105fd653cc631407d553cc631396f662cc631005f570cc631004ff7558231014fe7558231004fd7558231014fc7558231004ff7458231034fc7458231004ff725823102cfc725823101efb7058231006fb50582310e6f850582310e6fa30582310e6fa205823101efb105823101ef81058231034fe76d9131004ff75d9131014fe75d9131004fd75d9131014fc75d9131006be54d9131006bd54d913102cfe72d9131004fd72d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d9131006bf6499131005ef7259131005ec7259131004ff7559131014fe7559131004fd7559131014fc7559131006bf7459131004ff7359131006df7359131004ff7259131006ef7259131004ef725913102cfc7259131006ec725913102cec7259131004ff7159131006f77159131004ff705913100cfe705913100cfc7059131004fe7619131036be6419131006bd641913101cfe76d0d3101cfc76d0d31006bf64d0d31036bc64d0d3101df671d0d31005f571d0d31004fe7690d31036be6490d31006bd6490d3101cfc7650d31006bf6450d31036bc6450d31005f77150d3101df47150d31004fe7610d310dd7e7510d310057d7510d31036be6410d31006bd6410d31004ff75d8931014fe75d8931004fd75d8931014fc75d8931034fe74d8931004fd74d8931006ee52d8931006ed52d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef6298931005bf7458931005bc74589310dd7e75189310057d751893102eee6218931006ed6218931004fe76d0931004fd76d0931034fc76d0931006ef62d093102eec62d0931004fe7690931004fd769093102cfc7690931006bf6490931036bc6490931005de7390931005dd7390931004ff7650931004fe7650931004fc7650931004fe7610931004fd761093102cfc76109310dd7e75109310057d7510931006bf6410931036bc6410931005de7310931005dd7310931006ef621093102eec621093101df67110931005f57110931004fe76cc931005de76cc931006de76cc93102ede62cc93102edc62cc93101dde71cc93101ddc71cc93105edf61cc93101cfe768c9313fddd738c931006ef628c93102eec628c93101df6718c931005f5718c93101cfc764c931005bf744c931005bc744c931006ef624c93102eec624c931005f7714c93101df4714c93101cdc764c9310079f744c9310079c744c931007cf724c931007cf624c93102ede624c93102edc624c931007cc624c931007d7714c931
  | 25 => 0x9231006be5299231006bd5299231006bc529923101ebf719923101ebe719923101ebd719923101ebc719923101ebf519923101ebe519923101ebd519923101ebc519923101ebf319923101ebe319923101ebd319923101ebc319923101ebf219923101ebe219923101ebd219923101ebc2199231036bf7099231036be7099231036bd7099231036bc7099231006bf5099231006be5099231006bd5099231006bc5099231006be3099231006bc3099231006be2099231006bc209923101ebf109923101ebe109923101ebd109923101ebc1099231004ff7559231014fe7559231004fd7559231014fc755923101ebf7459231006bf5459231006be5459231006bd5459231006bc5459231004ff725923102cfc725923101cfc715923101ebe415923101ebc4159231004ff705923100cfe705923100cfc7059231006be4059231006bc405923101ef71059231006bf7559231006be7559231006bd7559231006bc7559231006bf7359231006bd7359231006bf5359231006be5359231006bd5359231006bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006be5259231006bd5259231006bc525923101ebf715923101ebe715923101ebd715923101ebc715923101ebf515923101ebe515923101ebd515923101ebc515923101ebf315923101ebe315923101ebd315923101ebc315923101ebf215923101ebe215923101ebd215923101ebc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006be5059231006bd5059231006bc5059231006be3059231006bc3059231006be2059231006bc205923101ebf105923101eb7105923101ebe105923101ebd105923101ebc1059231036be64d0e31006bd64d0e3101df671d0e31005f571d0e31036be6490e31006bd6490e31034ff7650e31036be6450e31006bd6450e31005f77150e3101df47150e310ed7e7510e310057d7510e31036be6410e31006bd6410e31004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a31034fc7458a3101eef7258a3101edf3158a3101edd3158a3101eee2158a3101eec2158a31004ff7058a3100cfe7058a3100cfc7058a31034ff76d0a3101cfe76d0a31004fd76d0a31036be64d0a31006bd64d0a3102cff7690a3101cfe7690a31004fd7690a31036be6490a31006bd6490a31004ff7650a31004fd7650a3101cfc7650a31036be6450a31006bd6450a3102cff7610a3101cfe7610a31004fd7610a310ed7e7510a310057d7510a31036be6410a31006bd6410a3101df67110a31005f57110a31006be64cca31006bd64cca31006be648ca31006bd648ca3102eee628ca31006ed628ca3101df6718ca31005f5718ca3102cff764ca31005bf744ca31005bc744ca31006b
  | 26 => 0x5eee72d933102cee72d9331004fd72d933105eed72d9331004ed72d933105ef571d933100cfe70d9331004fd70d933100cfc70d9331004fd76993310067e65993310067d659933105ebf649933105ebc6499331034ff76593310067e65593310067d655933105ebc6459331004ff7559331014fe7559331004fd7559331014fc755933105ebf745933101cfc735933105ebe435933105ebc4359331004ff725933102cfc7259331004ff705933100cfe705933100cfc70593311f67e65d0f310067d65d0f311de7e6550f310067d6550f310067e6598b310067d6598b3105eef6298b3102eec6298b310067e6558b310067d6558b3105eec6258b31004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b31034fc7458b3101cfc7358b3105eef3258b3105eec3258b31006f77158b31004ff7058b3100cfe7058b3100cfc7058b31034ff76d0b3105cfe76d0b31004fd76d0b311b67e65d0b310067d65d0b3102eee62d0b31006ed62d0b3101df671d0b31005f571d0b3102cff7690b3105cfe7690b31004fd7690b311a67e6590b310067d6590b31036be6490b31006bd6490b3105dde7390b31005dd7390b31004ff7650b31004fd7650b3105cfc7650b311967e6550b310067d6550b31005f77150b3101df47150b3102cff7610b3105cfe7610b31004fd7610b310cd7e7510b310057d7510b311867e6510b310067d6510b31036be6410b31006bd6410b3105dde7310b31005dd7310b3102eee6210b31006ed6210b3101cdd76ccb3105f5e65ccb3105f5d65ccb3102ede62ccb3105fce62ccb3105fcd62ccb3102edc62ccb3101dde71ccb3105fd671ccb3105fd571ccb3101ddc71ccb3116e7e658cb310067d658cb3115e7e654cb310067d654cb31005bf744cb31005bc744cb3101df4714cb31005df764cb31006df764cb313ef5e654cb310075d654cb310079f744cb310079c744cb3105fcf724cb3102ede624cb3102edc624cb31007d7714cb3101dde714cb3101ddc714cb31007d4714cb3101dd4714cb311367e65d07310067d65d0731036be64d0731006bd64d073105dde73d0731005dd73d0731034ff76507311167e65507310067d6550731036be6450731006bd6450731005df735073105ddc7350731005ef7250731005ec725073100cff76583310067e65583310067d655833105ef86058331004ff7558331014fe7558331004fd7558331014fc7558331004ff7458331034fc745833101cfc7358331004ff725833102cfc725833105efb305833105ef830583310f6fa1058331036bf7599231036be7599231036bd7599231036bc7599231036bf7399231036bd7399231006bf5399231006be5399231006bd5399231006bc5399231036bf7299231036be7299231036bd7299231036bc7299231006bf529
  | 27 => 0xc4298c4101ebf4198c4101ebd4198c4101ede3198c4101edc3198c4100cfe7098c41004fd7098c4100cfc7098c41004ff7558c41014fe7558c41004fd7558c41014fc7558c4101edf7358c41036df4358c41036dc4358c41004ff7258c4102cfc7258c4101ede3158c4101edc3158c41004ff7058c4100cfe7058c4100cfc7058c41004ff7558841014fe7558841004fd7558841014fc7558841004ff735884105cfc735884101eef7258841036ef4258841036bc4258841036ec425884101ebf415884101ebd415884101eee215884101eec2158841004ff705884100cfe705884100cfc7058841035bd76908413c6bd7690841004bd7690841036bf6590841416bd6590841006be6390841035be7290841037ae7290841036bf62908413c6bd62908412b5bf71908412b5bd71908412b6be6190841037b6619084105cff76cc84101cfe76cc841004fd76cc841035be74cc841005bd74cc84105ede63cc841006dd63cc84102cff768c84101cfe768c841004fd768c84102eee628c841006ed628c841004ff764c841004fd764c84101cfc764c841005bf744c841035bc744c841006de634c841006dd634c84102eee624c841006ed624c841005f7714c84101df4714c84102cff760c84101cfe760c841004fd760c8411057e750c8410057d750c841004ff7558041014fe7558041004fd7558041014fc755804100cfd7458041004ff735804105cfc7358041004ff725804102cfc7258041006be4258041036bc425804101ebf415804101ef6415804101ebd4158041036f5415804101cff705804101efb7058041006fb50580410fef85058041036fb4058041036f840580410fefa30580410fefa205804101efb105804101ef8105804105d7f76597310ce7f76597310147f765973105e7f645973105e7c645973105e7f625973105e7c625973140f5e315973105f5c315973105e7f60597310067e605973105e7c60597310067f74597310067e74597310067d74597310067c74597310ce7f735973105e7e73597310ce7d735973105e7c735973105e7e435973105e7c43597310067f72597310067e72597310067d72597310067c725973105e7f325973105e7c32597310ce7f715973140e7e71597310067d715973140e7c715973140e7e415973140e7c415973105e7f315973140e7e315973105e7c315973140e7e215973140e7c21597310067f70597310067e70597310067d70597310067c70597310067e40597310067c405973105e7f30597310067e305973105e7c30597310067e20597310067c205973140e7f10597310067e105973140e7c105973105cff75d9331014fe75d933105e7e75d93310147e75d9331004fd75d933105e7d75d93310047d75d933105cfc75d9331006be54d9331006bd54d933105ede73d933102cfe72d9331
  | 28 => 0x89413a6ee5418941006ae5418941006ed5418941006ad54189413a6ec541894102eef731894102eee731894102eed731894102eec7318941006ef5318941006ee5318941006ed5318941006ec53189413a6ef4318941006ee4318941006ae4318941006ed43189413a6ec4318941006ac431894102eef711894102eee711894102eed711894102eec7118941006ef51189412aeee5118941006ed51189412aeec51189413a6ef41189412aeee41189412aeae4118941006ed41189412aeec41189412aeac41189412aeee31189412aeec311894102eef701894102eee701894102eed701894102eec7018941006ef5018941006ee5018941006ed5018941006ec50189413a6ef4018941006ee40189413a6ec4018941006ee3018941006ec30189412aeef1018941006ee10189412aeec1018941005be76d0941036be76d0941004be76d0941035bf75d0941425bd75d0941005be73d0941007af62d094102ebe62d094102ebc62d0941007ac62d094102eac62d094101dbe71d094101dbc71d0941036bf61d0941037b761d0941005bd70d094101cfe769094141dbd7490941006ef629094102eec629094101df67190941005f57190941037b4419094101cfc7650941006ef625094102eec6250941005f7715094101df4715094101cbc765094141dbf755094141dbd7550941005bc7350941035bf7250941037af7250941007af625094102ebe625094102ebc6250941007ac625094102eac6250941007b7715094101dbe715094101dbc7150941007b4715094101db47150941036bf6150941037b76150941005bf7050941004fe76cc941004fd76cc94105cfc76cc941005bf74cc941035bc74cc941006ef62cc94102eec62cc941004fe768c941004fd768c94102cfc768c941035be748c941005bd748c941006ef628c94102eec628c941004ff764c941004fe764c941004fc764c941005bf744c941035bc744c941006ef624c94102eec624c941005f7714c94101df4714c941004fe760c941004fd760c94102cfc760c9411157e750c9410057d750c941035be740c941005bd740c941006ef620c94102eec620c94101df6710c941005f5710c94100cfe76d8141006ef62d8141006ec62d814110efa60d8141004ff75d8141014fe75d8141004fd75d8141014fc75d814101cfd74d814100cfc74d8141006be54d8141006bd54d814105cfe73d8141004fd73d814102cfe72d8141004fd72d8141034fd71d814110efa40d814110efa10d81410057f75581411157c7558141005df7358141005dc7358141005ef7258141005ec7258141006ef6258141006ec625814110ef8605814105cff7598c41014fe7598c41004fd7598c4105cfc7598c4101cfe7398c4101ede7398c41036df4398c4105edc4398c4102cfe7298c41004fd7298c41036b
  | 29 => 0x42dbf7590d4142dbd7590d41446bf6590d41446bd6590d41035be7390d41006bf6390d410079f6390d410079c6390d41005bd7290d413b6bc6290d4101dbe7190d41007b67190d4101db67190d41007b57190d4101dbc7190d41036bf6190d41037b76190d41005bd7090d411e6be6090d411e6bc6090d4101cfc7650d41006df6350d41006dc6350d41005f77150d4101df47150d41037b44150d41005be7610d41036be7610d41035bf7510d410373e7510d4143dbd7510d410373d7510d410053d7510d41436bf6510d41436bd6510d4142dbe7310d410379e7310d41006bf6310d41005bd7210d413aebc6210d4101dbe7110d4101dbc7110d41036bf6110d41037b76110d41005bd7010d411bebe6010d411bebc6010d41004ff75d8941014fe75d8941004fd75d8941014fc75d894105cfe73d8941004fd73d8941006ef52d8941006ee52d8941006ed52d8941006ec52d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef65d8941006ee65d8941006ed65d8941006ec65d89412bfaf74d8941007ae54d8941007ad54d8941006ef63d8941006ee63d8941006ed63d8941006ec63d8941007ae43d8941007ac43d894135fe741d89412bfae41d89412bfac41d894135fe441d8941006ee60d8941006ec60d8941006ef75d8941006ee75d8941006ed75d8941006ec75d89412beef74d894135eee74d8941006ef54d894135eee54d8941006ed54d894135eec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ed53d8941006ec53d894135eef43d8941006ee43d8941006ed43d894135eec43d894135eef71d89412beee71d8941006ed71d8941006ef51d89412beee51d8941006ed51d89412beec51d894135eef41d89412beee41d89412beec41d89412beee31d89412beec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef50d8941006ee50d8941006ed50d8941006ec50d894135eef40d8941006ee40d894135eec40d8941006ee30d8941006ec30d89412beef10d8941006ee10d89412beec10d89412b6bf6498941006ef62989411157e75189410057d75189412aebf641894102eee6218941006ed6218941005ee7618941006ee76189410076e75189410076d7518941006ef6518941006ee6518941006ed6518941006ec6518941007ad7418941007ae5418941007ad5418941006ef6318941006ee6318941006ed6318941006ec6318941007ae4318941007ac43189413a7e741189412afae41189412afac41189413a7e44118941006ee6018941006ec601894102eef751894102eee751894102e6e751894102eed751894102e6d751894102eec751894102eef741894102eee741894102eec7418941006ef541
  | 30 => 0xd4198e4101ede3198e4101edc3198e4100cfe7098e41004fd7098e4100cfc7098e41004ff7558e41014fe7558e41004fd7558e41014fc7558e4101edf7358e41004ff7258e4102cfc7258e4101cfc7158e4101ede3158e4101edc3158e41004ff7058e4100cfe7058e4100cfc7058e4101ef71058e4105ede6390e41006dd6390e4101df67190e41005f57190e41006de6350e41006dd6350e41005f77150e4101df47150e41004ff7558a41014fe7558a41004fd7558a41014fc7558a41004ff7358a4105cfc7358a4101eef7258a4101cfc7158a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a4100cfe7058a4100cfc7058a4102eee6290a41006ed6290a4101df67190a41005f57190a412b6bf6590a41456bd6590a41006be6390a41035be7290a412b6bf6290a412b7ae6290a413cebd6290a412b7ad6290a412b7b67190a412b5bd7190a413cfb57190a41036be6190a4102cff7650a4102eee6250a41006ed6250a41037ac4250a41005f77150a4101df47150a412adbd7610a41036bd7610a410373e7510a410373d7510a412aebf6510a4144ebd6510a41006be6310a41037ae7210a412aebf6210a412afaf6210a413cebd6210a412afac6210a41035bf7110a412adbd7110a41037b66110a412afac2110a4105cff76cca4101cfe76cca41004fd76cca41035be74cca41005bd74cca4105ede63cca41006dd63cca4102cff768ca4101cfe768ca41004fd768ca41004ff764ca41004fd764ca4101cfc764ca41005bf744ca41035bc744ca41006de634ca41006dd634ca41005f7714ca4101df4714ca4102cff760ca4101cfe760ca41004fd760ca411257e750ca410057d750ca4101df6710ca41005f5710ca41004ff75582410067f75582410047f7558241014fe7558241004fd7558241014fc75582410067c75582410147c7558241004ff735824105cfc7358241004ff725824102cfc7258241006be4258241006bc425824101cfc715824101ebf415824101ebd415824101efb705824111efa405824111efa205824101efb105824101ef81058241004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d41006de53d8d41006dd53d8d4102cfe72d8d41004fd72d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d411157e7598d410057d7598d41006df6398d41005ee7298d41005ed7298d41005ef7258d41005ec7258d41006dd6318d4105cff7518d41014fe7518d41004fd7518d4105cfc7518d41006be5418d41006bd5418d4105ede5318d41006dd5318d4102cfe7218d41004fd7218d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d4105edc3018d4101cfe7690d41006df6390d4105edc6390d4101df67190d41005f57190d4101cbe7690d41
  | 31 => 0xc83202f6d654c832007af744c832007ac744c83202def734c83202fcf734c83205eee634c83202fce634c83205fce534c832477cd534c83205fce434c832007cd434c832007e7714c832007e4714c832004ff7558432014fe7558432004fd7558432014fc7558432004ff7458432034fc745843202edf325843202edd325843202ef7715843205ef7315843205ef4315843202ef7215843202ef42158432004ff705843200cfe705843200cfc7058432004ff7558032014fe7558032004fd7558032014fc7558032004ff7458032034fc745803202eee3258032006ed3258032004ff715803201cfc715803202efb705803213efa405803205efb305803205ef8305803202efb205803202ef8205803213efa105803205cff7598f41014fe7598f41004fd7598f4105cfc7598f4101cfe7498f41036be5498f41006bd5498f4105ede7398f41036df4398f4105edc4398f4102cfe7298f41004fd7298f4100cfe7098f41004fd7098f4100cfc7098f41004ff7558f41014fe7558f41004fd7558f41014fc7558f4101cfc7458f4101cbc7458f41036df7358f41036df4358f41036bc4358f41036dc4358f41004ff7258f4102cfc7258f41004ff7058f4100cfe7058f4100cfc7058f41036bf4058f41035bd7690f41006bd7690f4146dbf7590f4146dbd7590f41036bf6590f41466bd6590f410379e7390f41006bd6390f41005bd7290f413b6be6290f4101dbe7190f4101dbc7190f41005bd7090f411e6be6090f41036bc6090f41004ff7558b41014fe7558b41004fd7558b41014fc7558b4101cfc7458b41004ff7358b4105cfc7358b41036ef7258b41036ef4258b41036ec4258b41004ff7058b4100cfe7058b4100cfc7058b41035bf7650b41006bf7650b4145dbf7550b4145dbd7550b41005bc7350b41037af7250b4102ebe6250b4102ebc6250b4101dbe7150b4101dbc7150b41005bf7050b4105cff76ccb41034fe76ccb41004fd76ccb41005bf74ccb41035bc74ccb4102cff768cb41034fe768cb41004fd768cb41035be748cb41005bd748cb41004ff764cb41004fd764cb41034fc764cb41005bf744cb41035bc744cb41005f7714cb4101df4714cb4102cff760cb41034fe760cb41004fd760cb411357e750cb410057d750cb41035be740cb41005bd740cb41004ff7558341014fe7558341004fd7558341014fc755834101cfc7458341036be5458341006bd5458341004ff735834105cfc7358341004ff725834102cfc7258341036f64158341036f54158341036fb7058341036fb4058341036f8405834112efa105834105cff7598e41014fe7598e4105e7e7598e410147e7598e41004fd7598e4105e7d7598e410047d7598e4105cfc7598e4101ede7398e4102cfe7298e41004fd7298e4101cfe7198e4101ebf4198e4101eb
  | 32 => 0x6f76418532007b76418532006b76418532006f66418532006f56418532006f46418532007b46418532006b46418532007d57318532007e732185323bfd632185323bfd43218532006f66018532006f4601853201ef7751853201ef6751853201ef5751853201ef4751853201ef7741853201ef6741853201ef5741853201ef47418532006f75418532006f65418532006f55418532006f4541853201ef77318532006f75318532006f65318532006f55318532006f45318532006f74318532006f64318532006f54318532006f4431853201ef7721853201ef6721853201ef47218532006f752185323bef65218532006f552185323bef45218532006f742185323bef64218532006f542185323bef44218532006f732185323bef63218532006f532185323bef4321853201ef7701853201ef6701853201ef5701853201ef47018532006f75018532006f65018532006f55018532006f45018532006f64018532006f44018532006f63018532006f430185323bef72018532006f620185323bef4201853200cfe76d8132006bf64d8132006bc64d8132006f761d8132006f461d8132156fa60d8132004ff75d8132014fe75d8132004fd75d8132014fc75d8132034fe74d8132004fd74d813202cfd73d813201cfe71d8132004fd71d8132006fb50d8132156f850d8132156fa30d8132156fa20d81320057f755813215d7c7558132005bf7458132005bc7458132006bf6458132006bc6458132005f77158132005f47158132006f76158132006f46158132156f860581320067f74594320067e74594320067d74594320067c74594321467f735943205e7e73594321467d735943205e7c735943205e7e435943205e7c435943202e7f725943202e7e725943202e7d725943202e7c725943202e7f425943202e7e425943202e7d425943202e7c425943202e7f325943202e7e325943202e7d325943202e7c32594320067f71594320067e71594320067d71594320067c715943205e7f315943205e7c315943202e7f215943202e7e215943202e7d215943202e7c21594320067f70594320067e70594320067d70594320067c70594320067e40594320067c405943205e7f30594320067e305943205e7c305943202e7f205943202e7e205943202e7d205943202e7c20594320067e10594320067c1059432004ff7559032014fe7559032004fd7559032014fc755903202cff745903202ebf745903205cfe735903205cfc735903205ebe435903205ebc435903202cfe725903202cfc725903202ebe425903202ebc4259032004ff715903201cfc7159032004ff705903200cfe705903200cfc7059032004fd76d0c321f67e65d0c320067d65d0c32004ff7650c321de7e6550c320067d6550c3202def764c832006ef764c832004ef764c83202f6e654
  | 33 => 0xd7119132036bc7119132006bf5119132006be5119132006bd5119132006bc51191323aebf21191323aebc2119132036bf7019132036be7019132036bd7019132036bc7019132006bf5019132006be5019132006bd5019132006bc5019132006be3019132006bc30191323aebf2019132006be20191323aebc2019132006be1019132006bc101913202cfe76d0d3202cfc76d0d32006bf64d0d32036bc64d0d3202dee72d0d32005ed72d0d32004fe7690d32006bf6490d32036bc6490d3202cfc7650d32006bf6450d32036bc6450d32005ef7250d3202dec7250d32004fe7610d3215d7e7510d320057d7510d32006bf6410d32036bc6410d320079d4310d32004fe76d093205cfc76d0932006bf64d0932036bc64d0932005de73d0932005dd73d0932034ff7650932004fd7650932034fc7650932006bf6450932036bc6450932005df7350932005dc735093202fac425093202fcc3250932006bf64cc932006bc64cc93202dde73cc93202edf63cc932007af64cc932007ac64cc93202dee73cc93202eef63cc93202fcf63cc932005ed70cc932006bf64d8532006bc64d8532004ff75d8532014fe75d8532004fd75d8532014fc75d8532034fe74d8532004fd74d8532006f751d8532006f651d8532006f551d8532006f451d853200cfe70d8532004fd70d853200cfc70d8532006f610d8532006f410d8532006f765d8532006f665d8532006f565d8532006f465d8532006f764d8532007b764d8532006b764d8532006f664d8532006f564d8532006f464d8532007b464d8532006b464d8532397d773d8532007e732d8532397d632d8532397d432d8532006f660d8532006f460d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d8532396f773d8532006f753d8532006f653d8532006f553d8532006f453d8532006f743d8532006f643d8532006f543d8532006f443d8532006f772d8532396f672d8532006f752d8532396f652d8532006f552d8532396f452d8532006f742d8532396f642d8532006f542d8532396f442d8532006f732d8532396f632d8532396f432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f650d8532006f550d8532006f450d8532006f640d8532006f440d8532006f630d8532006f430d8532396f720d8532006f620d8532396f420d8532005be7498532005bd7498532006bf6498532006bc6498532006f76198532005bf7458532005bc7458532006bf6458532006bc6458532006bf6418532006bc641853201ef66118532006f56118532005f67618532006f67618532006f76518532006f66518532006f56518532006f46518532
  | 34 => 0xe32036bc6410e3202ded76cca3205eed76cca3202fce73cca3205fce53cca3247fcd53cca32005ed70cca32004ff7558632014fe7558632004fd7558632014fc7558632004ff7458632034fc745863202edf325863202edd325863202ef7715863202ef7215863202ef42158632004ff705863200cfe705863200cfc7058632004ff7558232014fe7558232004fd7558232014fc7558232004ff7458232034fc7458232004ff715823201cfc715823202efb7058232166fa305823202efb205823202ef82058232166fa1058232034fe76d9132004ff75d9132014fe75d9132004fd75d9132014fc75d9132006bf54d9132006be54d9132006bd54d9132006bc54d913201cfe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d9132006be40d9132006bc40d9132034be76d9132006bf65d9132006be65d9132006bd65d9132006bc65d91323b79e32d91323b79c32d9132006be60d9132006bc60d9132006bf75d9132006be75d9132006bd75d9132006bc75d91323b6bf73d9132006bd73d9132006bf53d9132006be53d9132006bd53d9132006bc53d9132006bf72d91323b6be72d9132006bd72d91323b6bc72d9132006bf52d91323b6be52d9132006bd52d91323b6bc52d91323b6be32d91323b6bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d91323b6bf21d91323b6bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d9132006be30d9132006bc30d91323b6bf20d9132006be20d91323b6bc20d9132006be10d9132006bc10d9132006bf6499132005f67199132005f57199132005f77159132005f47159132004ff7559132014fe7559132004fd7559132014fc7559132006bf7459132004ff7359132006df7359132004ff7259132006ef7259132004ff7159132006f77159132004f7715913201cfc7159132006f4715913201cf47159132004ff705913200cfe705913200cfc7059132004fe761913215d7e75191320057d7519132036be6419132006bd6419132005be7619132006be7619132004be76191320073e75191320073d7519132006bf6519132006be6519132006bd6519132006bc65191323af9e32191323af9c3219132006be6019132006bc6019132036bf7519132036be75191320363e7519132036bd75191320363d7519132036bc7519132036bf7319132036bd7319132006bf5319132006be5319132006bd5319132006bc5319132036bf7219132036be7219132036bd7219132036bc7219132006bf52191323aebe5219132006bd52191323aebc52191323aebe3219132006bd32191323aebc3219132036bf7119132036be7119132036b
  | 35 => 0x35bd7690c42006bd7690c4248dbf7590c4248dbd7590c42036bf6590c420373e6590c42486bd6590c420373d6590c420063d6590c42035be7390c420379e7390c42006bd6390c423b5bd7290c423b6be6290c42037ae6290c422adbe7190c42005bd7090c421e6be6090c42036bc6090c42004ff7558442014fe7558442004fd7558442014fc7558442036be5458442006bd5458442004ff735844205cfc7358442006be4358442036bc435844202ebf425844202ebd425844202ef77158442036f74158442036bc4158442036f4415844202ef7215844202eec215844202ef42158442004ff705844200cfe705844200cfc7058442036bf4058442004ff7558042014fe7558042004fd7558042014fc7558042036be5458042006bd5458042004ff735804205cfc7358042004ff715804201cfc715804202cff705804202efb7058042036fb4058042036f8405804217efa305804202efb205804202ef8205804217efa105804205cff75d9332014fe75d9332004fd75d933205cfc75d933205ede73d933205eed72d93323b6be42d93323b6bc42d933201cfe71d9332004fd71d933200cfe70d9332004fd70d933200cfc70d9332004fd769933205ebf649933205ebc6499332034ff765933205ebc6459332004ff7559332014fe7559332004fd7559332014fc755933205ebf7459332006be5459332006bd545933202cfc735933205ebe435933205ebc4359332004ff715933201cfc7159332004ff705933200cfe705933200cfc705933205f9c4350f32036be64d0b32006bd64d0b3205dde73d0b32005dd73d0b32034ff7650b32036be6450b32006bd6450b32005df7350b3205ddc7350b32005be7498732005bd749873205ef7619873201ef4619873205ef46158732004ff7558732014fe7558732004fd7558732014fc7558732004ff7458732034fc745873202cfc735873205ef7315873205ef43158732004ff705873200cfe705873200cfc705873200cff76583320057f755833214d7c755833205ef86058332004ff75583320067f75583320047f7558332014fe7558332004fd7558332014fc75583320067c75583320147c7558332004ff7458332034fc745833202cfc7358332004ff715833201cfc715833205efb305833205ef83058332176fa2058332004ff7559232014fe7559232004fd7559232014fc755923202ebf7459232006be5459232006bd545923202cfc725923202ebe425923202ebc4259232004ff715923201cfc7159232004ff705923200cfe705923200cfc7059232006be4059232006bc4059232036be64d0e32006bd64d0e3202dee72d0e32005ed72d0e323b6bf6490e32036bc6490e32034ff7650e32036be6450e32006bd6450e32005ef7250e3202dec7250e3216d7e7510e320057d7510e323aebf641
  | 36 => 0x8205824219efa1058242004ff75d8d42014fe75d8d42004fd75d8d42014fc75d8d4201cfe71d8d42004fd71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df6398d42005f77158d42005f47158d421957e7518d420057d7518d42006dd6318d4205cff7518d42014fe7518d4205e7e7518d420147e7518d42004fd7518d4205e7d7518d420047d7518d4205cfc7518d423aebe4218d423aebc4218d4201cfe7118d42004fd7118d4200cfe7018d42004fd7018d4200cfc7018d4202cfe7690d42006df6390d4205edc6390d4202dee7290d42005ed7290d4202cfc7650d42006df6350d42006dc6350d420379c4350d42005ef7250d4202dec7250d42037ac4250d42004ff75d8542014fe75d8542004fd75d8542014fc75d854205cfe73d8542004fd73d8542006f751d8542006f451d854200cfe70d8542004fd70d854200cfc70d8542006f761985422b6bf64185422beef621854201ef66118542006f5611854200cfe76d81421957e75d81420057d75d814218efa60d8142004ff75d8142014fe75d81420067e75d81420147e75d8142004fd75d81420067d75d81420047d75d8142014fc75d814202cfd74d814205cfe73d8142004fd73d8142034fd72d8142356be42d8142356bc42d814201cfe71d8142004fd71d814218efa40d814218efa20d814218ef860581420367f74594420367e74594420367d74594420367c74594420067f73594420067e73594420067d73594420067c73594420367f43594420367e43594420367d43594420367c43594420363c435944202e7f725944202e7e725944202e7d725944202e7c725944202e7f425944202e7e425944202e7d425944202e7c425944202e7f325944202e7e325944202e7d325944202e7c32594420067f71594420067e71594420067d71594420067c71594420367f41594420367e41594420367d41594420367c415944202e7f215944202e7e215944202e7d215944202e7c21594420067f70594420067e70594420067d70594420067c70594420367f40594420363f40594420367e40594420367d40594420367c40594420067e30594420067c305944202e7f205944202e7e205944202e7d205944202e7c20594420067e10594420067c105944205cff7598c42014fe7598c42004fd7598c4205cfc7598c42036be5498c42006bd5498c4202cfe7398c4202ede7398c42036df4398c4205edc4398c4202ede3298c4202edc3298c4201cfe7198c42004fd7198c4200cfe7098c42004fd7098c4200cfc7098c42004ff7558c42014fe7558c42004fd7558c42014fc7558c4202edf7358c42036df4358c42036bc4358c42036dc4358c420369c4358c4202ede3258c4202edc3258c42004ff7158c4201cfc7158c42004ff7058c4200cfe7058c4200cfc7058c42036bf4058c42
  | 37 => 0x80431befa105804305cff7598f42014fe7598f42004fd7598f4205cfc7598f4202cfe7498f4205ede7398f42036df4398f4205edc4398f423b6be4298f42036bc4298f4201cfe7198f42004fd7198f42036bf4198f4200cfe7098f42004fd7098f4200cfc7098f42004ff7558f42014fe7558f42004fd7558f42014fc7558f4202cfc7458f42036df7358f42036df4358f42036dc4358f42004ff7158f4201cfc7158f42004ff7058f4200cfe7058f4200cfc7058f42004ff7558742014fe7558742004fd7558742014fc755874202cfc7458742004ff735874205cfc7358742036f77158742036f74158742036f44158742004ff705874200cfe705874200cfc7058742004ff7558342014fe7558342004fd7558342014fc755834202cfc7458342004ff735834205cfc73583422d6be4258342036bc4258342004ff715834201cfc7158342036bf4158342036fb7058342036fb4058342036f840583421aefa205834205cff7598e42014fe7598e42004fd7598e4205cfc7598e42006be5498e42006bd5498e4202ede7398e4205ede5398e42006dd5398e4202cfe7298e4202ede3298e4202edc3298e4201cfe7198e42004fd7198e4200cfe7098e42004fd7098e4200cfc7098e42006de3098e4205edc3098e42004ff7558e42014fe7558e42004fd7558e42014fc7558e4202edf7358e42006de5358e42006dd5358e4202cfc7258e4202ede3258e4202edc3258e42004ff7158e4201cfc7158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42006dc3058e4205ede6390e42006dd6390e4202dee7290e42005ed7290e424adbf7590e424adbd7590e423b6bf6590e424a6bd6590e42035be7390e423b79e6390e42006bd6390e423b79d6390e423b7ae7290e423b5bd7290e42007ad7290e42036be6290e422b5be7190e42005bd7090e421e6be6090e421e6bc6090e42006de6350e42006dd6350e42005ef7250e4202dec7250e423adbd7610e42036bd7610e42035bf7510e420373e7510e4249dbd7510e420373d7510e420053d7510e423aebf6510e42496bd6510e420379e7310e42006bd6310e42035bf7210e423adbd7210e42037ae6210e422b5be7110e42005bd7010e421bebe6010e421bebc6010e42004ff7558642014fe7558642004fd7558642014fc7558642006be5458642006bd5458642004ff735864205cfc7358642006be4358642006bc435864202cfc725864202ebf425864202ebd425864202ef7715864202ef7215864202ef42158642004ff705864200cfe705864200cfc7058642004ff7558242014fe7558242004fd7558242014fc7558242006be5458242006bd5458242004ff735824205cfc735824202cfc7258242004ff715824201cfc715824202efb705824219efa405824202efb205824202ef
  | 38 => 0x4fd75d8943014fc75d894301cfe71d8943004fd71d894300cfe70d8943004fd70d894300cfc70d8943006ef6298943005f77158943005f471589431dd7e75189430057d75189433b6bf641894302eee6218943006ed6218943004ff75d8543014fe75d8543004fd75d8543014fc75d8543006be43d854302cfe72d8543004fd72d854300cfe70d8543004fd70d854300cfc70d8543006f76198543005ef7258543005ec725854301ef66118543006f5611854300cfe76d81431d6fa60d8143004ff75d8143014fe75d8143004fd75d8143014fc75d8143034fd73d814302cfe72d8143004fd72d814301cfe71d8143004fd71d8143006fb50d81431d6f850d81431d6fa40d81431d6fa30d81430057f75581431dd7c75581431d6f860581430367f74594430367e74594430367d74594430367c74594431c67f735944305e7e73594431c67d735944305e7c73594430367f435944305e7e43594430367d435944305e7c43594430067f72594430067e72594430067d72594430067c72594430367f42594430367e42594430367d42594430367c42594430363c425944305e7f325944305e7c32594430067f71594430067e71594430067d71594430067c71594430367f41594430363f41594430367e41594430367d41594430367c415944305e7f315944305e7c31594430067f70594430067e70594430067d70594430067c70594430367f40594430367e40594430367d40594430367c405944305e7f30594430067e305944305e7c30594430067e20594430067c20594430067e10594430067c105944305dbf7650c43006bf7650c43004bf7650c434c5bf7550c434c5bd7550c4305f3e6550c4305f3d6550c4305dbf7350c430379f7350c4305ebe6350c4305f9e6350c4305f9e5350c434bf9d5350c433adbc7250c43005bf7150c431bdbe7050c431bdbc7050c434b79e3050c4305f9c3050c43004ff7558843014fe7558843004fd7558843014fc755884305eef7258843036ef4258843036bc4258843036ec4258843036ac425884305eef325884305eec3258843004ff715884301cfc7158843036bf4158843004ff705884300cfe705884300cfc7058843004ff7558443014fe7558443004fd7558443014fc7558443036be5458443006bd5458443004ff725844302cfc725844305ef77158443036f74158443036f4415844305ef7315844305ef43158443004ff705844300cfe705844300cfc7058443004ff7558043014fe7558043004fd7558043014fc7558043036be5458043006bd5458043036bf4358043006bd4358043004ff725804302cfc7258043036bc4258043004ff715804301cfc7158043036bf415804305efb7058043036fb40580431bebe4058043036bc4058043036f8405804305efb305804305ef830580431befa205
  | 39 => 0x1a0018002000802f00240000000006007000000340040038000000c0060000002000000400080070004000000c000000400800000020018004000001200080030008007002c00300240100008000000400c000001200040050018000001800b00180010010001001c002000000000300070010006002400800040020014006001c0020000000002800000c000300000050078000003800f00f000300100010008002000c001003000300000010014002001001e00140020048008001c000000000000240080064001001c00000080060004011003c00300000070010007000400000380000000001000400100e4010000c0020000002000000d000000f00080020038001002401b0004008008c00600340050000001002401200000000000008000800f004ff7558b43014fe7558b43004fd7558b43014fc7558b43036ef7258b43036ef4258b43036ec4258b43004ff7158b4301cfc7158b43004ff7058b4300cfe7058b4300cfc7058b43004ff7558743014fe7558743004fd7558743014fc7558743036bc4358743004ff725874302cfc7258743036f77158743036f74158743036f44158743004ff705874300cfe705874300cfc7058743036bf4058743004ff7558343014fe7558343004fd7558343014fc7558343004ff725834302cfc7258343004ff715834301cfc7158343036fb7058343036fb4058343036f840583431eefa305834305dbd76d0e43036bd76d0e43035bf75d0e434ddbd75d0e4305f9e63d0e4305f9e53d0e434d79d53d0e433b5be72d0e43005bd71d0e431e5be70d0e43035bc70d0e4305eef6298a4302eec6298a4305eec6258a43004ff7558a43014fe7558a43004fd7558a43014fc7558a4305cfc7358a43006ee5258a43006ed5258a4305eef3258a4305eec3258a43004ff7158a4301cfc7158a43004ff7058a4300cfe7058a4300cfc7058a4305ef7619864301ef4619864305ef46158643004ff7558643014fe7558643004fd7558643014fc7558643006be5458643006bd545864305cfc7358643004ff725864302cfc725864305ef7315864305ef43158643004ff705864300cfe705864300cfc705864300cff76582430057f75582431cd7c7558243035bc745824305ef860582431e7ba4058243004ff75582430067f75582430047f7558243014fe7558243004fd7558243014fc75582430067c75582430147c7558243006be5458243006bd545824305cfc7358243006bf4358243004ff725824302cfc7258243004ff715824301cfc71582431e6be40582431e6fa40582431e6bc405824305efb305824305ef83058243035de7390d43036df6390d434cebf6590d434cebd6590d4305dbe7390d4305ebf6390d430379f6390d43005bd7090d431e6be6090d431e6bc6090d43004ff75d8943014fe75d8943
  | 40 => 0x1c00000180020074017000000300280030008002014c000003c010002000700000070014004000400a00bc0010000012000000f0000002001c00a000400000100070000011000c00d000c01c00680130094003000800d00000020004002000000100000210000001000800200900000020003001c002001800000180060000000000002f0000001006000000080000000001000400300280010004006005801100680000008000000400c00000030000019003c00300100000024000005c0010028004000c003000000500000080058006000c0160020003000000200000030000000000800200000000014006000000a000000000000000000000003c00300000010000000000000b00000030088005000000600000010000002000800800000100000000000800300000030008002002001900100000008003001400000000070014000000400700440100000004002c00b002000f001800400000000000000000c004000000900300010014000001400c0034003002000300040050004016000c003000000000140000018003001801800040010020002002c005000c008000000000000030008003000c0000000000000000200040010000006000400c000c0060000001001c00c00840000058001000001300000000010000000c01c0000005002c001004c0000004000000c0120000003001c0000044003000000b00240000000000001c001000c003001400700240020024005001c00d0000000000800000000050008003000c0020004011001400400140000004006001c000005000700a800100040070008022000c00000fc000000000800100000000004001000100040220010001000c000001c003000000200000000004002003000000000000004001000c016001c00000040010000007000000b00d000e003c00100040010014001004400a000400400040100010001000400b0000005001c002000800200000090008000000800000680070004003000c0020000000004000000040020050005000001e000400400340020084001000c003001c006004c00000080000000006001c02b000000100040000000000005000900b00020024003000000200080050070005000c002000000000180070008005005c002000c000000801100080010038007001000000bc002000000400000000000001014000c0024010001400000840000000010003c001003c008001c006002400a002000600a4008001000200000050018007000c0000048001000c02b008c00400080000024000009401d000c003001000e0014001003400800300010018002005c001000000000040040004001000000700300090010002000400500b80090004000000400b009c005008000000140010008008000000000500020000000002c01c005400000000050018
  | 41 => 0x800600000000038004000001300100030000001000400100140050000005000801e0000005003800000600000004000000c0010008003000801d0034000000c0060000001001000700340010004001000000000040010004000001401e000c00000180030008006000400200280080000009001400b0038000001400100180000024002000000100200040018009000c0090000009000000000000050040002005c00000040000004006001800e00040000080000000400000000110000006006000a001000d00040000014002000c000000c002000000500040000000000000400800040010000000000c00c00040030000011000c00e00000020004018002400f000800000000160030002001800000b000600000000000007000800700080000000000000001100100040014004000c003000000300240210018013000000400140060094000002c00200380180010000000c00400140000010005004c000001400a000000200180000000000000000200080020008001001000a00100000008002005800000000030060000000c000000000000040060008005000000600100000008017000000a001c000003000d009c0020064002005802e00040000058001000c00000280000020000003400d0000005000c000000c0070000003000000a004400f00100070008000000000700200020000014000000800000030000001002400f000c005000400400000010008000000000800000150004006000000000c00030018003000801f0028001003801300000010000000001c004006c00f00440040004012000000b001400800900010014009006800300340010000000002000000040070028000007c000000c0000004000002000000800000014000000000700080000000000000000b00300010000000000400300040010024005000000000100050038000003c008008c00200000000020002000000900000030008003002400100000090000002000000200a00000000002000000a00000050004027000c00b001000500480060008009003000c0000002000400f0004000002800200080020000000000000b000c00b0000000005c0080000006001800200040010004011000c000001000b00000080018002000001800040000000002003c00000040130008006000801a00000000008000002c00100100030004003000001d0054003001800000140010004008000000100000040004005002000200000040050008009000000140040014000000400500000010014001002400100a0003000400100040060004014001401a0008010003c01400e40030004000006c006001000c000400a0020000000000600000000008005001c004000400100080040048004000000e0040000005c00200040000008003001000300000050004004002c008
  | 42 => 0x6003c0040008006000c0040018007001000500000030028000000000100440000000000000006a00200020018003000800200040000038011001000000040010000002001000000000010004001001000900080000000000000400000180010000000001000b00400050020008000c001000800300000000014012001c000005800000700010008007002c0020018003003c00000140010000001001000500700010010000001000a0000005007400200080000000002000000200000000020000001c006000c001000000500300020008003001001000000030008017000c01a00000000000000013000400240010094009000400b000c00a000c0050000001001000800180030050014000800100000000000012000000200080010004000000c002000800c0004003000c0050004007000000a000800000040000000002000c004001403a000001000440050000023001c00000180000008006000c0000040006000001a000400d00040000058000001c0000000003000800600100000000000000c000000c0060008002004000800000040018000003800000080070088008010000000540020024007001c000000400d0004001000800000000020020001000000600600380004001002400200000120008005002c010001c00900000000000000001803c0014004005c000000400000000010024006006c002000c000002000800100010000002000000f0010000002c000000800000080060030001000000b000400800240010000001000c001000401b00000000000007000000600100000004015000800a00080450000007002800e0000005000000600180020004006000c00200080030020004000800c002800100140000000000003401b0008000000000b000c002000800b000400f00180150000000005c0010010005010c0000010000000c001002c02800100010000003001000200a80000000001001000600600050004000003c010000000800100030028003002c00c003800f0020000001c003000401c0000001000000e001c00000040060010002000400e000400c0004002001800000cc00100000020040002000000000000040010001002401a0014001000000100c40010034005001800c006c0000034004002400f001800600000010040008000c006002400c004400c001c00f0008004000000f000000c0004009001000000080080000001002c002001c005000000000080010000006000400600300010000000000000500140070014000000000d0014006001800600000040040005000000000040060000001000000600000020000000000400500000000004001000000e0014000000400100080160000012000400a000000100200270088000002400000000090000000005c0030020002000400200240050020009002
  | 43 => 0x500762941dd43c09f2447617eec7780003c7ab18a089d7e345a9a42020d2c21d8bd64312b24ab48502000242a0d526ce317008c00034820000000a85af868aa1ad077d88aca4020026588000000076026f343e0000000000000065bb27a94fabbe5dbb16c333298c000000075913a23e9a7141de1e9c49c9708411800003a1e247358000000307a55e80000002ecc01f800016ea9f6000000048e1f54ae4a8cc6a701624a4816a7e622c800000005cf8000c9424343f8935644fa24c3bd84f41250000c0200002e199cc889800051d989c2180a020000000000062a50b8fc07e1800000000009e725ba74902c084127905940000000000000030d63cb8044bb50f8a0001828346800000000005c60000b94000054000007e88aec0000de20000000000000019b856c0eb1dc60c5800010f0afeae78000aeaa9862d28000000030c98e800077c97e80002c8834520dc23593942ec11ee23bb1320cf9a22a7a06307171cba1a20352a353302000000000022d426e15ba090a1d6000000020d0538cfb80a8000099057080540000d04000256c0000000000260e111800031480000000af83c9307c73b0000b1d29100001bc65928000004c00000040000000000000400600040000054001000c0020048011000001d00080000018005001400100780080000006000c016002c000001800000440020020013004400b0020008001401000c400200080000000024006c0050018002000c010000800000000010004000000000f000000300200000008004000800300680050010007000000d000000600040050008002005c016002c0020000004000000000180050004020001c0010004002001c001000800000800000000004000c001003000d0020000000800000180020008007000000000000000004003000c006000800600180020020008001400a0000001000800f001c008002c0010004002000000600280010010003000000200dc00200080000008001000400000500000004000004401300140090004000000000200140050000009000800300380030000000000403900040100000007000000000080080004001000800000040080004000000800000080080024003000000000100030004010001800900d400300200080000002000c00200300040028000000c001005001b000c00600040010058006000400a002400400200000004003000c0000008000006c01b0020000000400000100030018006002c003000400d000000100040070004001002c005000000f0000001001400100180010010003000c000000000d000000f000801800380000020012002400000100020128004008000400040010000012000400e0054001000c000001001900200030024000001c015000c01d0000000003400300240080020011000c0000000000001400
  | 44 => 0x64bae335a84d07041eb00004411dde0f8000010800000000000af6abc8c350000d320d4698300008cda7fc51880008c7881800a93ac00000007e5000024b0000cbca7848ed2d34b4b80008ec0000304ae1011500003853018223078208d8c4c0000000513800088fa9e001f236200005da000000062480006eb8cde73200000000f6491d13b42ea9090000170aa3900003b680007f780001fc8fca5e8000000033ba2fa80001cda79896b9e6a000161ca0993c02f6012232fa9a67660dac948a16449f2f1e7652ed67272f3800000000002f6ccad9aa639c8628b1e8000000275a6ab32a0193302c0000000d1b13ae3a22d4c31599522a2913a00018f200019c0853000035f8b00000239a10a1ccc5f70000959800087c122ab132c44a0689f80a2000000015b00000e0c84087be8bc97607839294c2a11f629ca41a000215a17186d2915a2f80001cd01c5000049e9e140fb132239dac70c8d1ddc00017ce00000a406a8000000032c96a889c6958000a21800042ca5681a021ce68b9c2a4ba0000c5880002c0a75ca0c821073ab4c600030100001eae6f0129a3a6965a00029304c280ce00000009939a4a0000542a90875090b8000000000018430f8b4305440001d0cb6080000a3000081780001d6879ea00008e93612be00000003c80ed08c2a1e496e03f2a15afca21e93d0a9a1a8e02d0000a4f002c72e1894ad0b4e007b0bca6b22ff05ffa352522ae665720364101aaa466f17e0335a5983700184b2119ca8230000000310e2b503962e422da3a910fc972add028a0c7409b11b062e8f1075508fc50408c60000000af907760298b7600013fa0f99b32a1b1806ca607dab1623129cfa14eaf42a7e6ce28fa897aa1e20523a2bc099845421ac25aaa01a04c8f9ea6a0dda3633068a9a9ca867eaebcaa59ba60990a3a3ce2b6c25500ca7eeadacce4980c71d8000c5900000000000000000007598180000000a9b22ee750b0da000000000000000000d88d30024a25731f41cd0f9a39331ae5149ce87181ec633a0d506c08000000333432c1f4083c0a089500b100f3320695c80009f5a58cb9f8ba2472b43262d04aa225000003580008101de6b36a0a60fd1b5c0000000b1b00006ac06a800000000001e2ead7976ad260000c37ab32898012c521a69889906b06228444d250fda3d492e6baf8a1860c264a00000000000a0025d898e372160c5e30000ca32d264549d7a00000009e02b30355ae30149800054bac060001bec57f2d6eccc81f00000532000000082a8590a73a6d20000000682809e7cca94e3318aba00000005782af4000167a5d6000000004c8bbb25300001c9eb58255000024fe00007f600020280002962352292ea5c80001ea80000001eea37b80003a580000000f4e50c80004a01178644800005c9c62000000006d8dd89d
  | 45 => 0xdc9dc0b5eb18e12f25368b3ace27b81694bc19d02cc292dc9529914ca4800088ea0c25ab185abd10000000000000018c41d2967825b28a48d7884a58884a40000a0600007c600000007a60a545f59b8600025b010500009ac0ff2b7332c48e804260002d9a26a0f4c854b10cd1115f0036a478c6c9362d1e83665848a6a43eafac9be8492864b2d600029d49d0800030f00002dd1c4ab05800000024be99829c8256000074d809a15f000005a32d8c6480008c89250ce900001d63436acf0000851a20872ba72c27385d209a94f863c23962d7932c2ea2f82ac820e66412c32b79a84677bade0b0791cc9bc2bf61109dec3c708207e81d3e00007fc08e2ac66f41e34af0344883aab166531b48711110e5d415b423087124ef996a4b49c5a637803c7fba712240261acd9800068799f6d1d088a0002a7a03da792996a524bfa1d166582c5aa61268c6c012a44e4954a0000b6e9f28c1c4a29e3aa09138ca59830a080adfe9fb92541a5851a9521e10b7c85ce4ab2c725f083e8d2e8f7e00032088208000b379052041000080a800000026ecb2a18ea11ca7c094b9920bd3a0ca568800000000005270000000000081c071a00000000f8800000024f800017cc00024a2ced800000021a4000237634a19d852e9b3c000172ecf00dae96f084e99d2330a30af3442d8000ae71688c3b26ae2e61ec87620000cd49340477214a7ca240600031860001f480000000bff80005200bae0002ba6000307800000003289ec413518106fa945cad88f284e780000002b2c967af6acc480000000000d118d2052088241ce33e659a80005d31a3221a800096480005f934c422f0000892abccc9e09522d6800028c881e65d8000000000000000000002d1cbc60698c709efa00021120838f42046167066b216625a000000028200000000252800084500007ac800041a98688fd086e83804fa0002aa633012222c53180450a5b40280534a10800000030765a80d320002e2ecc69632c5000000002b4a0001f9696b1cd421580000000000000000074e00000002b38685800086f8d26b96b308c17000069aa9500001f0822c800079118a8916800000031100000898bc0143e129b4e80001d220000000cbd000002c000083b0000c299caa54388b40002446373201c0428fc8816ad1000010820001116a0a814a93911de000247003080000001f90aecb210433234c0948000d2f0ce64a112560ce80009268000000000005fb490780ace62f01226c0c84da8fa8ef0a9ba4c06aca4b0c4205a669480564622b063e0aa246fda05411d80003ad1a208161ada89c1dea8e31ac0c9d2ab64f68000560b40886d32ee0002590ba816f46c3a670493a4ae4c3994448300006ee8f347a68000d188b3408f0000567a0be039800067d0f16b050000385845eb26935a38c98443b2ac
  | 46 => 0x4cd91d61b620920001e5c00031a044080004e00ed800000000002cfc00023020001be400033142ee919a55f1ea41a50ef88f517f030d0170cf1000069500005d480000000000cc915f88361efe31ba62c6348d448da956a3f930e85a283a6b7aa14800012628e40000000000057c800000030c6d28800000006000000d649b780003a600000000d5a6cea0f400000000001eca7558c2e80f8f5c2980000cd386b2bbe8000684966ebc480000002efeabe000000006deaa0b29c0002b08413a696603a7ac51987b87ea84a0a94b33a4441e8400000001340c6483e1bc20002be69c019369f992c80e183c67fe8bc25370db608100005350ca0c888000000000000000006519c2882409d60a9800063980008afa21284027188eb1fe058b1d84af61e2c3bc999c9dc8eb606783d800017a216299b8000070eac0999410c00001f120b2077835e00026c228b05f227d961083f0548beb80002cc049a6c58e7e8969470000000079306709a033e22aa8a2616f18e865000000000000a900000b08000000a05c200004c4c57800000028ee9b880000000000c2428b0955227a873146ec15acb0c0c02c200009f00002ea6cbe8000679a15c5ac80180000c1a0002d72bee876220a10ecbdf13860000f749db80000ca22560000000000231c5f52b8a81380000001bc86e2adb4000000027d15e60002bb6b2ba4de32332e69e59b90b1796c200031c445b29ee0e30000224173491b92521069bee000000024513a006311508cb807400008c09258612adc0000b38082c0e38000000000085500000000e1a38700001160000c139c3637a21944b31c0a7e38c6000000009fb0000000090a3da80000002bb4421000040891e600003120000000af380004070000c4010343250f6223e266c8a52c045262570aab20222569910bb41564b8b2c4a4ec878a04783926f7a34608c920850608260832c78c60b1c61e4b4ce6bf95ca921a48804b865e165258a823816cc5c80000002db600000004481c123b10a6400000000002b106d38000548a9268d800000001e183638cbaaa890e0000000000000005c68d4e021b13a766a9ae67c043a9419db897995a61ae19da608121854aa01098c800079f800095b945e64700004de0000000216cada00000000174be20000ce9a47c000000000026a8801936890e2e6014211640001bb628c053e7f0000059088ba4f9000010b80000002b0c92d2d84000000000000000000000a85229c13594c20001d1e7ce00000000000000209a000000000025420000000000000000000000002d9e7d8195009c9dd6076aadc670a0bc47b20e86538000000293a0938000016ae0a33121ca193a1eeb4e0ee8aae000a2ef1e9e0000e6c0001578cf213a4b44ac8a0e1269a5d694886e006447b6a0000d321d01b425a0426298262013ce3
  | 47 => 0x205a1360829ee400000002f18000000000000000007d0800000000003b09d2a84180008228000000000047185500002ac2874a2a028e00000000000000000063700000b3127e24f04be909247e266a42049600007c5aa22c5183d68aa800000020d40001dbc00000000000000cc380000001e82436b4f200000001960000000000000031ee6cfa892988800079f19d25a482ae48f87e08d121285c306362960c107c106721b8aa045f18000c3f8c6c1e6000044480006d82df6000181200012120002116011800004a82863ab80000001f2e00033ce40127f81902aae0e0030065e1dca3588be6c9c1590253aeaa000115460d21964270c2ca590000000281c80990be6cb950c2e9a2ba18d217e81d13f4781b04839a15105af2e6c343167288105f64f187720000000000242cd22800060003fa2b70ae461aa7b699ab3febc920a4a2a1c2c000214200012688ed89c268522468ba00003d188c40001156cf79fc693f298a784a7201ea0266b9309986368fd26150f688c3000049900000000d5e4b690762e0951e41b02282c11a34000225200000005d723400000b06060a546640063ca00a68e39683c40000000876000000000008a216fa63b96ee64592e0acb9c74415aae60002e8842a232a395160e0001daec17a40429c1d405f78134bdfa608bf32b1400015a4a3b2e72d14a7fa8e2910600000006489dba4ceac08bfe000093c26147b5863aa9c163c5b598aca98a3de6659d6a0000000c8e00004698000a150000000211e0000206000296ec8a986c80b32a6a38abe2a452eb4ba187e20000a48000141449c000019f000039122c07ec88dea1e100e7ec06a2cacae221ad13aab4da04ac6b00006e48000a078f3cce10000c182afc00000001c1aad000200000000330b13b022a838e70ac7a21e90c13b67d2a6660f08fa43e411188fb00007099fce4c096869842cd446a8e1227880687c3312c54080b23c02e7a0aa154e30ea29e0442e5e65a01a2c3e915c5948ffe78025a632d9c726c5000097420a8a8a27b863f0000000000000023c4a492fb80000eb200000006e82bbad37a6a092d80008d414b63cc0cd074805004d380006b80cac00000008170000016132a21122204780c96c45849000001a60001b9a00000001a284740000bb2ab20000a46a22e201000009580004ac800052f0000000000000031348b5800000028700000000d1393180002aba7b78d6c8acb17e79ca70422c10a203b92287e298ccd2f9c1ad362b72abf97f63390b804c78fe025f21a2c79817c9809ecc6562fb48c800008641e5a00016d2000190ca45800098f3246000284e00000009732ba437e045c00007c0000209400031a21c9000000003fe8b0800087f24ea955aeee1f09de419e32e004c001a153905e78f15167d41260b2e8e3a934a10ca410456cb78
  | 48 => 0x31bc0002d7c000283c000000065209727db80000000000b6a800016480001e99f9c9ba800000029e21410e043729c1c2d40000000000000000007402a1a5b7adc0223ab647a389d497b349e0000000ccf80000560bb8000223c9ab2d3098800000000000c6100000000000000048ad158000521000000000002d3ac5200034a8c4c000048d17402410000cda84f60000000000000066804b6a42090858c3322b342b4c42c000020e800000000003a1967e00020186b1ad2445a0000000206c57d80007a18000a68af2806fa85081f0178000137c1061af692ea74e62883bc923a8520a6b3ea8ab000021c917cb6a26f4884221407208fe94a80000000000c5380001e11ee2a1d0000000016e0000ca48900000408000000017820000000000199e00030ba000000087f800029498d457184f00000b420000fe660e83a45b284388440000b5c050c37eb044d329ac400024162f11492000259a4cbb3aaa501c42370997e5cc1ffc39832626c11286000225481fa9f211f2ece008136c9eb834052c23e478ab4e691213a8b5527564f713f62e4a1f8000062e03c244c7fc229200004f8a5c2b0e4e6a932951000000000009712bde000000026c2c3c9b009443338000a9815dcc0f8000458a138c78000095fa88a7a410a03061d8a4bfb40cc790516bb11a5a08804a800001440a828ce00014b894118ce2de2a666dc00008752e820001f0e000000000000001b2285e424aa18299998a50db0925680e2e3bf8fb89fc8d7661203b4d2d34162b18a7a000000081880003ddb2fc500a4b200027fed1e0000d00190e774826872483504fb00009650000c2e00007532b2280132b8b4e80005b41ea600022f650c143a34780000001fda16f8f6099433d86cd227c051a13065e996cb54171e7cf8b0e4fb91a8a91a2e29f200060001dfc48d806ab61885e00000000bf800000003ca326b44257600000000000b9710ee51286fc6021d720dd848874d0cf88dd0eba9c429debc5a73699f317c65d2f3e00015d284b82301681d2e6f827e87390aa81c5800000000001f280000002290000000024d2de83e00000ab2a6a4000027e077218000002aaab50000b3234e4000156600003ea5d8ada40001704c7622e06a194da6f1214404a0000236060832d0000822000084b2fe622db15600000008ee88327a20000a6d00000000000000000000024d47c0073a791a94600000006df80000000000b24aa489420000000000096f80005f680000001cf6aea226649b89ba1f700009e30000d2e0d409ba1a847bc2a500131858b9900000b601380ea800000000000000000c630000000224898a800010db1c000527249720f3e2f22fa800000004829ae4000076e9d209a6cbda5fa41322068f60000794916ea4a800000000003780c727c80000a7193ea00000000003342
  | 49 => 0xc833b14a397ab7a10912f8b8cb3265d208228831e7085e0a74a82000041c261c9fab272cb7174a72b1e542958000af714a6af4911ca95271c000130846da44ec151434c0980009f8a9d66b995e440f0000984800027800008049e6600025d6d21ad3e7f88000cfd1c5ea2301d296a0c62b849c300001fec357311a95600006389d7600026d40001038c20b1981c0274a1b5b28a000027ca1c800083e80005ec8ede92b2996b78800000033466aa9e8a00000000001054c7311bc85cb224000000067880003c881a89ec22fa3238c6a34c000000000000001c3c1e70000cfe000046f9956156800053daef8c2f03e437cad520001074b0b8000000263e13180000000d609578108b0a1b1800018c803eacc448b0b325b395ac30aa300c6680004bcaa208cc8000b5a80004ce16e6000000000029380000000ce608be0002b4e000062649a800027f168c82885f06cc24800b7299265c00009a28ec892101e200020d6a30213c2188180555b4885a032e480bb412bcaabaca100f364d184607dead74a2a80000b931d660084048f002c47788d9e99e117e3a780009e5000000033c236f00002be800030180000003154b2e00002118000539af74977b0504cd000000029ec917136430f8000d1a99c4b8834da2a08d34a6801402a7800000011920000ee200000000003064000000000004c000003744320000c8028da38d1e20000000098b8d96a2d822aa55114e7d5a33a24b8000876add49f6a77e86e1ab60003228200aabc3e705301f784d8000135c451800058b9f2600006a02372d4400032b0be3a9121a42ab078d8b8c9d00000000000000000002dc949e000000073380007b5021c39e800000003b6000172258ea6dc0be17287cd88b862b864256a33d400d2f2e29e198c7bd0a20cc116741be8be05db16ea52a166836d30f60008d0a6900000a2880005ce2f3c259236600017320de06eec128000000223600000005ee04860000e7c6939abc0fd8992aa4b3a23d2290a5c0217023232689d88b1c4a7873cba4adecc7400dcc6c056864ea83e8a294b473e24c226d311c08e9e7aaee09329e9800051920465a8b30653a00ac9f5075c37da84cab8b05a2d4a51a95f27822d20b7e6f6ae0247101567f32c7691d85185ea047e81da5764ae80005e71f02773ad8e44c28f0000217a0090000bfd000045e9dac8a12238327a01402da562a0a0e904000a88300aa5e8da32ac2b8a4dcade248c00d97861688a90a0b80509a1933223689404b39f2c4201d280690000991a11a5751e6820e0fbec05000000000000000cec6e080007b60000954800000006022e589b246d2dd81b9233891a8e106751d9082d914c00032ccac2a88800020f600000005bdaa12b58800044c80006172b60071144c0ef8000000266e4a811fa000312680c159cad52f682e5
  | 50 => 0xc9e8050b0c445e6165e7cf053a7929c0c6a68000c62affa9c180004a59ebc5f6048e38fa998aa10e7477fa020ce417ca50e18ca8802fe472d06165ba1d780002d6447497aeb288052c200d9c9ef27580000b840002f5e4642e8e00000ba8d5308c69f000053898a6c75192423d800000010d6ad69e8c5d5218ac2b0fb43938000b0d95b655d13960000000234343c00018d632f272e0000622000274c05399a800001ca28932daad60000000000000000000000000bf50f0e8720f400e722800000000afd05880000000abca67ecf4800066d2aec00000001730000192000000025127232ee823a1cdc9fd2bbc00000000000000bd60000000113800000000da992ccfda49264c86ba5359bd65fa8d2ad0e9388a8c00f24d2a4a84910a96ad41d0e55532e280780000000e0e000011a55825f40d633640820ab2919126600027f6000000000000000000000000000038f00005e90000a7f8000cfa083ca5e9de855b10ae2ada8d2198936aa121b6835a95441e80cfacf704e8868058083308ccba010666568da400397f86ca9d3a80f15e82db26647120dbe4112c1c722acb2c4a9dc4ba897c0963a3da0e61c866908ac2b03000049b24ec9afa06643a95ce23291f034623d6c389f128cd12e400009d0c0680000178216c5815fe00032ae1d187b00a5800000000003e8a2987039f1eae1866805e9bd48f1a942b6e2b8057b8aee59f00225f99c56b892c4260586f6d389002cb205d4c2933862fc039a6ba8e28021000007502f47daa0b8bd881fc2f7aac48e72582c1c8c38a41aa1000000003d40000000169c961000016c0000c4e109e7058e38b121fc400016b451000000001c8e7c6000051400000000c509620f2a94400005b326c838814fa00000006be800066b8d841418000160866c6dc9df4000000077e118a1d5b1140000000aaa00000000000000000051d128e3b0000086200008ba80001812b2a000177a67210600002410000080ca65184a00000000000000b642bee9c780003db8012bfa800041900005b180008420000000000037f8a9800014ecbd49702bef9dfa0000000be70000000000093b954035e9b4288c8000000000000000007908000b4b00009049ff400000005ef2cd615ea2aec2d1b8c22a17449ce0a3ebe02c860002d0a00023caa030000cd300000001c9432c8000000251c0000af09de9f8c0000be4000000011a194a3371be601726a6bc404ce4dc3496751ad567e08bd46ea9d7490081643e494ce000177400400000000000c5226386188d3a78311fe070a09ebab2f6e0002f403c680008972b3a509800000006cc932197c31ea3c873d2c98390000007180007cd152076aaa90196b3e000000006e6000017100006b59780000022cb8eadb0018ac7e11ea1ba0002268000000000000000000eeab1800000002fd
  | 51 => 0x622b3003e1c82dda725acd29df08a40000f12591a7469971e76a56a4aaa5e2378c9f0da26bb800006c262457691409369cb69438000000306227caf7223926420001a183508c885ddafb026891c8000104a0000000cd6000080212c05ec001eccba50c2a327c616a80000b22f36241a4145058eec9538000a2826f2863800035500008cfb0ca985add20001b4654c1b28000042234f1d6c38926cc4309c384972e6e754195c2baa2180e8b33081b80007ef9fbc48c000093e98722210632d151b6ca2f85225ed80002c6a6aa1fb8000186a58069b000000029fc525332045832c00648ce0c6225001020842c86119811b2df0c1c06826698ff80001fd47ff939063db1f8885ae1400000608db1108a96a6fc2041842000118e6c200000000000a470ccaa0190f81fd27320d58ab8b9a94ea073830ebf20ee014f0ade7698d58589a468b20aa9c98c0e802a39fae786859c99a0ebed2800005b6abfe7c19282675a4f663b293e56101987720512a669a085168d241e522dc00000007261f6c1212b8e7d113fe6fc1a640000000ce726b2056b4ac000246c40a0000d1f00000000000000077a0000464c0d800000028ca405000000000006870000c0a863800000003d680000f0153e843800000000009d49b36107082e6f32fc413717367fc80000000fde0001c541e69a44cfb1f624a40cfe005a0508588e8c395a7d88a30e0a2c8045a3ea168200000000129444000000000030c8000160800028b200000009829a28ac71a1007300000002aaa8b9980a000000068e33f03fc213200000003a8000034480000d80000000000013f924895a80000002526acf80000000000659b276701000006b857657785e80000000a9580000000b7099cb21652c900a0002f1ab1a06dc5df8000000158c03b00ea0000000bbf000000000000002c0e0e500000000000a209794778007a6b61206434338c40b80000000692ce8000012b80647fd8000c5a000075293120002cc290727dec6a000010a800097d8c4ab1b8e8ec0380006b31f92cad334aaa500000d686fe0001f0a330968ebc9903a80e8000731962800000000000000226b20aa8700000bf00000000d6e8f48578c571da2c009a5e000000013301909b19804a7081c04c006be9ee93d6000000021f3256000046ea6200009ae0c8a0002d060000af43c12ba2cdfa7600001ea8429a0de0001902b8f06ca000000000016a423d2d280000b6a00019a200016342e79e566290dd408617d2a8b80009899fb46bc85580492dde0bb82da6b3a0ac51c8298cb2a2d0c2700006a0147a624245e4452640531a9346c180000000000a2e2cf200000000000000b360000c0100006b70ad6aac90aa0000000a52000000004ee0bd80004612b5257aac5c2d90fd6398a0c0000000022200000000000a1900001ba800081
  | 52 => 0xe6309ec950ad803903bad2c8b7ca5828f88712b8cbd9801c9da287a19d337a46081ee6050f5859da3fa3c2ac2283897a6cdc891eb30124a1391bb270780000000e0836e112ea4d8000929a89600005e097a0000af280008fcad9c83482703d293d4c6e17560002de48bf279e5dc965c16183389e928e054f00000000078b8e020000009020001a0ea0494fe87733b4c01953a00028ea0001a360c18d90c67110c39400000002a2c40910a40002b00000336c2a71a267380294a8f322ca479840770af4a00000008f39b5a78e2f560ba94aa6159a903e5818612e0fb02a6ae1a000185055d813e66caf20686a968863000058da17438b02f21fb00040000cea9e800000001c2e60b8000a9c9176997939c9ae8a4e1d902ce3ef00006d10000c221d82be9af46a8080000001f528798acec1f8000878800000000005fd12bc0000150ac100002870000284ad7e8a380005230000cbb0ee60eca4ce9691bfc00007f0a602d78000082a4ca2a983a99088ca519425c98000b7380002a180000db28f600030b094823f050498bc62da95c987a516d01acee9a2025e7ee128c87d8766bbd1ab80a7a1507420000d0d2b4014795385d197967ceb1f08312f32b0fb2305818382a7493f2c74af5a0000000ac9886635285b23eab21e0c60788a0e24828829a8876fafe0be1000079232023dc155c1590b54a1680005283484722314497886d40003394bf5927827b0000000068c00014900f495520002eb2ada9cee3f387969dd00002ed9ef600033960c8aa86000138e562000052598e00000f842b2000000000004d7b4400000000c2524e6acd331830db40a00024620000e028a900008c591da3e216966d999ba0878bb400e1a063e180000430dd079b01ac6af854010b0000271b24817987020001c90bb80e061e01448d129aec46eb44c9931c3a00016140000800315187e593026e361a6d80001716157ad5e00000009f833fa67b81260001e0a07fb41c03113fc09d29b08a880000d39d0a7e121ac1758c861fe2c344ef0d2e4a7154c4230aa29cc05d8cd5a494938a9f4d2b832e203974e41ead92207072cca93106998981ac83b19e31f2f9213807a4be582e80d2035c3a497ba147102c2c6018aa6fa7287dd800057b1a9255a2fd04adb2e8711a0429a88aa0508813c6a326764f0800021b1c5222011f42d99f80bcb2e2a1788462c4da452aad22586c32628c8d92f62ce0000a3f1a4c5b80a0aaf1066643011f8620a55cc0e84ac97c32ce88080c04d4a38671a2f78000009c0c922d800005fa00000000000000974958000009ca43c869c587800094a10bc55f821a5d92e44b7225ee86ab17646ca86662314d08c50f32000306a1ef2d32320ad8c959000018b31e25df171200032f86360000a31a78a7a49e5e5bb2224cd89594206800000009786e7ae
  | 53 => 0x5e083187a2785b41800023e800026929c884d2ae40000000123c00000000000000846000000011ce74b1724d0c257a92f000000000007ae12deadd899c0c9af0e61d80d4847132497a9822000216ab6eb328000025ac39963e0000ad000000008f8064a3d5b45c590346846bb39a6b8893a7f98000b150000000000000014d8c56924643880000000a5a0002f94af5800000020c87812f9e1660bf88f8ad969e2238e28f26c45c1861423800cc213140487a84de1491d8e03f0000066b49a6191b7cc4282d69d9839e92287fac6e9770afe00805b884b48ebb1ea759a898b4009de2462a5c11999884633058a6b2e4a7f400bed190000bb4899694d0f3a7c72098861306c0c71e08392111e74418c0574000000000000000000b0a80000ad800067b0ba0b6f21260000000b46afbc0000dc4a5130aa000329675b891aaf832209569d62c0d2f500a3b4264d233388bb2122a128cfc15c322e40d8070ad19fd214da03460e147c1079ade050946c182b13c708b0669d10984534843e5e69c1067e091c4789c9aa5f8362adb8a1e34886506781ca29261a724f99a3e1be04f26e71bce4851a0c7c696642a4b4d23feb1cabed88fabb78000cf5905c6c6ad3c6ea15ae69d2d168719f7489113204b5824ca82a40a9801532366048cb438528caf8b2c41032880001a70343aeb6401b08e5bc0b4c0000a0c3f10868ccaac663a0949a4e08eac07d22f00000000c4480000002860000326c1a18000767800097e00000000000995a40c1e380006268000000143c7fe00004f78a460000000025158a54b2d5ca72972c6e388a67bb80005b52e7400000004058d103d109c04351c7a490af8c000000016d919c75c000027ba94c8c1000076a2cf8cd80bac000069a000000085a1db200000d20001586549000000015b8c59800031f800000015fa9b984705712ed89462fc24c10fcc42b2a06b529d265a62ce84aa065cad71efccd79bd2ca1299e68b13f0d16000000000006ec0000000000063d1c024318042cd530285e2b0a23120c321398000451094889ca99c6c9ae46d3b80008c60152374a26e0000000000000041fb38e81a000000000002161e406c80000b0e1c14bfb0000202a41ebc3000033c101eb202a8cc2db17000000001ec989e1d480bca32271a71908d440333102fa2cbcd08a7c40dbae0e00300009d79fdcbde800000000000001cfe69f8a6e00000006640854000008a4bc252c0001cfa148039082589d204729dc977140a00032fe98183f04cc00007210000000306e0000000166a12a5882e3e40fae8acff00008a589cc01ba5b6a3c80000000000aa7800075f23569a1030400027e44b2b0cc23cb24a0000048000142a0002c9c2ca1f7800006e80dc33369a709dc6d031a606221bc698800036994c89763226c3c3316b9a0c68d1c052c3
  | 54 => 0x30c29de247aa48ae34ad9a9fabbd8ffcaa202d4cef8a1abea8282736987c50927025afb0dc27a861877c0c1415f82ca924182c74f1aa2bbc8fb272ca786bc891a237386203a8b3da16b908a09605eab1f0ca804482e696c8b441bc92eeaca037cb96146a5a4300a8b18a441b0a4b8425a2b6b2793109e887b690c9616b59acdc7bca10aa93b1f20002a8e00000000001eba1db22de7b7000065c8000000141c88c1c2443c00000000000000000006c9f7e21c1f3055225d4ceb00000000ae099514a20001fa600000001d200a200000000000482a11122e0002cfe8e522e470cabf0364a726a5f2aeead20000467978e0eb9d9c0408000afa94f42288000cd0316e7b380f40000000ce200000001a78add09ae000000064b828a73c0bd0268000000032eaae59e963c52f8a4740e5815993e8b909b58a0627a812e9a667762d76067033600023a400012207471f7cbb186c074600000000e00c101a2a0001b6a56f800000011ac15500000000000000191aaa0182a595a974000312429780000000000c3c80002518c0e000000037aabaec36185237781f86c923bc000000000021fa38629ba00015cc00000001cc983e8f083de0af198e71c0adac2616a6172b460cde0000000287e3c9830214386a427696440221b882efa89e00020eec0813cc6259ca4000000000002b4bc50000578a7cc8d28000c11a9563de1bb870d324263410dc5fe8000097000000024000002b823faa8d041a000000000000000b269b40000010000006e80000000248000301e9db1dccb1ab11e9d400001678000c05a94a00010586e50000ca7960abcc0000ad1000000000000002deeb460000000000000003ce394971c000260426324f47eb1fd645d20ba30122760e816ae9b580000000000283827a2a991e495e06763f18000beca96c942b428d35222a80e2a3a6dd01b45382f5c5541f9a76d8000157075e0b487900002282931b0869860ea871632bab68148ebae800041e157000031da7c525c01778e306ffaa4a0dc984c5660000a430d7c5f41e28af08b8e46e2636bf3b2400002d80c993174b7d1d3225a8f7a3e39908a3d05b84b1acfa28b8a7e000000067a26b4c46000000016d8c7705ec00000000002ee60000000375a078000320400000009ed00000001bfa8b2854a0000000b7f195e3090c1e501b0b2ab3a8bcc96b0388941bf46e11c665e4858c93a2a58cee23802f3ad889060000a39800079d05fc61780009f3b00c9f719b00001662000000000012ea154ae960cd072e113a9da7d7893800023b855688ce7d69926000278e4601c4e24c198219fa1a800000004f800000000000000040c1ca8b600001e1ccf19fc80000ddc2fd800000000000000caa06e0fb6b661a00b502c9429a3350c7f85a4481234200032a8c8f80000598000c73ac8e6d4a
  | 55 => 0xb95342e00000000c502789ef9ef80000cf400018b05b1028000003a83db00000002cacbd202440000db000000000c400001da80009580000000000000016fc300301244aaf3a08500008d6a4409be0e6e41c88a03098000103941e000010e00008740000000000000070823b2c4b8000000000000000000a42032c5a80004e980002cb9d8c8e9a80aa482c0020d8000bb280000000000c10800000000005e2346e73111c20002a38000332c00015f47538b569ada6584f11a760002f4c61c33001faab7e12c1420599a514afb0cb8c8481e0201aee41272a9ac4f86ae99e8be205715340000000000000000000000000000248a0645eaa8360b41e5041206601f392c20bb05dc27923707c400008e48450510800089d2e16b15871e4ec27aa0ec30e436289c800020480001ed06ab8000992291804d80006d50fd8000000061e2ada0000000000000000000002348000000000061d287c00033820f680d00000000000000067726ee8b30000afe8a84a4b30be5290000be698240002084cdf000072019aa51586f44b525da0ff2398b6f9170932818e737a1246a2a2b070220364ae056e0001b4c82d1e32000325220fa86ea360000000000000031048c91cbca6a80003718000c910b220002a4c0a10000b8113caa7aae264040a6c24d8000c99b158cb18c0c60780deb452a3e0001bd862623484dc800000016b80002a4402a80006e900000360b4049d8e4687c8224a2526bc3eb1884224ada252b9d920000df0b4817b4c6d8af246500008678000ad5800000007aeba7288000005620000c70be9094275800000001f4c5e4131a00011a071f800054633708c6800090a341a0001a82b709cfc1b98000c8514de359846ab25a0b0c229400c640a222651298729b4140198aa4732a8a686b8c30c871ebecfc9d8017417c4d0aa85c4d834eaca1aac0cf2abd41b828dcce0000003231028cb00000001a0200009203eb8000bf48000000000000000000000000000022647c800000032d20000000c3807fe0000000238800035d00009c5a0525b934b01261c4085593507b9a6ca249aacc1bc1dda16393f80000000000237a00000000002bc695330c0000150a9cd0b3a0000b3622780002850e1ec7f04802209a942ba04ea0001e26b3a86525ef8000cec972087a336e08b951c7d634a683faea4c000eb0b568276a270ce2d2d9100994979e55791c08a191963bd240e11493587dc1a040000000497a51ebdd8efc000092aca38de4b291a30bf180000001ea20cca4223cb21c0890860c5030c982c3282c9709bdc08498be4c320e443794ee33d9a24911347e64e1a6e14529f81919afcd0120246071e1ebfb97845bf92aa1f4121e69219de39aac2613f0510cef1d86bc21b621af10ba3f50916b24298e17e01a04ac12d026002626a5a2344abb1ec
  | 56 => 0x4f8ab7c000191eb7e2d2a52b1fe836a93ba563abfc40982a49dda8e8b4081e8caf1af0be41c820001536866ae5658900000002a0c1991b5e000141a3419ec2105b47653f000015181d060c800000009822f4b1206ed340e000000053284a23298de6b0b0cda2fd09c42ac00000002fda66929d82b28bf26aa2da6d20000000002ac1f3231004e84340000082000349c0000c785adac8c00011d44390edc8fbb0d0bc714be2ff9c4c000000067a93543fda6e031180000002d5888680000000000000000004508505d080002858b2a00bafd842680003b32d6811329b2a4a2e78c1d31b441f106eae6904271e02b263e00e096890fe81810940481d06bd502b8000239e30a33ae0002dca0b8227800025860000fa0000000073c8684c939860c6908ec4bf02f00002e7c00000009e6ae1e29f00007b024d600020868dfaf048a689860f417ac45aa19800000003d79f4e4169aa0bf79eec558ae086e5a69e62807443b5866a0000fee86c923a00008647a50ebc366aff271b230679887e8a1d999221e1986b2d2ff6000000022a8000000000089ab45e62e074c00000fe4b6000018782b047f05fe31682de5c38e9c44d15420580efacb0a73c40a800078c00005c4078c916000000000000000000d0b2abea8aa40842d10cea7c1ab4c532fa27561b783a2acce70008e60000ac43e30000544b02428d08407f9000058625cec9ba42644f11eaa2d0410b629172803296aaec0606b7106c62ad006c0de888675a27640318000434a85888a2a3600005c000010e800000000001b2cc7a327ec338ece0fba8de6919d14a899d965a6969e933112431626e432b9b1e17d0c16bb887d400034028ca0c5e0798d948c98b3e8e217fc0000ec65fb000058e26342fe84b2a8d0ba40001906bbc1aba1ee933e94eadd62d1a38231080000001a606199ae8302085c0002dc6406226226d8fec67c8d3e29324423272edc73086ce0002d220000000516083024a121a3ae000000000000001658d2a9e582b9b17a0df80006c40a1047a22bc2afb2a21da16c8a80040ac5480b88df0a761ab2e766239654cd71eaab93a3cc6dd9dd064f0ac06792d4849d108659207267ad0dec2e29f5cb2821b66b49bf28fd825411209122c2b3d0000000050a0cd2621a01687b00000c6b17800000000000000138b21a025a5c60002f6000000000000000399220e79b8d722c5b42094c80004d994c4d04269092780008028a2a788abf29290e78388a06a84815d6b9c23f8b518000ca0ab124568246bd92f983970000630acf615d0000000283a000000093425fe56691a400034ecaba2d9453ca158000270cc9780001c413748778fe87e92ce4586acec000290e05db0a0639218200019286138d0834d870a8d39cc01bb00005f2331eb8328345cf24500f72e845d788ae5938c921dc
  | 57 => 0x625e4ae80c908783348c6fac10262ab882588a428ae023451e0a808c23122a3fb0ee48000002c492a6000177802489aa33c930613280303c198c67680b084f604c234e15bc35a2e98549800000000002e700004429da400032f0057aaf003e065695d1b120b1aeea000000036c98b20002454000000000000004b88cd4142822260980005ae8000c97000094e1342b0609e800029e664c2d049fc1b1c9da8ad260d9ce26602e94b5b115851a2ddc7468bcc0f234c206f031e2d88342b0087b45b71f9e1c728ac490147ea56085a00034920002890b318cd8cf915720003052d199c3e7f624c46741a686a7901a0d293d25118c7602610b872816a8c1314c09c209e6b06936e6f2a3e685ba3581c30ed271aaec227e869e1df286275731c80001cd200023fc000345a3899ce61f919ce0000000000007200000000000000baa24604ad000048c80000000e4ab0900001e1895eaba852e0000000204800000eae1c41894608ffaeae4870b1e00017e2a021f88195162a25baae05cab1aad0907305701d5a0002b840d12f70c4a077e64a80000000496afa0f0c07c82be00017f2000000009427c20b8832a38aab98a35a2d2697224e00012fa1b11d482148000bff000000006aa74c1326a26940e72c0fdc815aec0cea0fba938000000015aa0002436000156e00000006a919c600000001c880000001592000000000030f4436000000000001720c0a000000000000000002d4e000000000000003a1000096580000e280000000f9404180002d60000c9a80002430000bf0094c82b80000fe339e000000006520a0340ae28d238000000000000000009c294f07062176000000059823dc439a22c079000000000000000000000000000000000001b224e103084bd07e600000900000000551a2a6112b2d080380002490000b8db2d479900003089f460458000000000040488ea489000000031960000eaa67f8000000000000000002bf190a00000000001b7a546a9528ea000015a84400000e9432113b8000000000002600000000ba79d44a058d00b3280004839684caa80002fb87d651530c434718880001b50262090e8bd0bdc857814876d2c301580000000302e836a30e000247200016c0000111aa1a00009280d4c000074e100000000030ae68e8000000131410c80009f4204c3d51cd882001003df000000001967ad8d82a710000ca0138acc31768496acf4b119c6e59b29c00000718a9d0a4043280002120000b920b88cf31eb00002990485b4f00000956000000000009fe000000000000001b6800061b80008dc800000034a4a1a80009dc0000b7e93768ea9fcab299f221d00708000000040208960001a9837d0000000128800000000a480009a500000001f72cda150674109beb900a62a990b7ab818000ab922b40000728000323c000000
  | 58 => 0xa2e8000000058463f800000017140002fe20000e664c580006db9b4a0002c126c28000000112262a88f02e681f625c060e00000007b494cc2ff004e54507c8d232d42a0500ae646000025fa88400000000000000827000075480006668000bac0000000000000000000001846000218689f915e4d102a2d340478a9e2e90000000000000006552d084520000000000035e19fc0002e8c9eca19c00000002d70c80a042ad6000273a8871fa80000000b860ed40002caac9333740000000757a35c0000910a6d800060f10304de9fb60000000354a22200015b20001e4e000000045996028cf1f6610482faa9da9bc3c2323a92723d0b94ad1e36e8240c650cee541063e7d9093ec071eac502075485809509f4a17c449af0a8110b689a0b33c155933c63eac4000000000002fa04a8800039080008bf9af490fa4f2991226c17b852aaa28000000108e90f2e9a0001bbc0000000696303ccdd8000c8c85ac0000032292a9cc71f0000ab6213abb2014c61e800000000005bc80e2c98288e00031f62ab10f416d00005d9a3be3bb800019eb31c3320a947ba21f47a807740003096000000007a86a60000a360000000000159600000008db800000009d89c3adb20da21b00ee049e319800000000000001fc200030842c90fd00000000000068eaa8283068f1136b0ea80e00000004b10320b18a72a5ac2eda0a700004e62a32b3c09602cf31504619acab6ba53cd3719bec9634ccb802afac50a0f2281000040c89ac44a09a4267800000030fca790fc2414213e48080000000000000243a313b3b079e0000ae512ec9bf80001792af60001e601659be897ca95e74480006f88dfcbd083d4ce28000c830000ca400000001f2a1d08000b1410f600026f664d1c50a311af86e8a38429709740000aae0001ad4b02854c0ae8000000000000000009b68402556343813b25fc7fa86b683430ea8d92b1a8b100263fd0000a6e034600007d2000137e2f6a44aca6896664fa1c22fb21a61870da8d07ab36967207a2bd8572b2d99645ce9bbe69429d06d916f807e8624a2b8d70d14199844b152866d80004f21db00002cbe70180000002804d1c87d80551210ab7800094094e4d35873e0e20000452aa7ca5d9cbe3600da04932ccc6d580004d324666eb00006fe0f66c7e80003100abc0000000a4080003081e3e00030d20000ee425e887e08f85a84c70f1869e80005811f68c26b34438d96000cf214007
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xce8625c042440010ff0abb6648800a1f21576cc91000c7a432e399220018f5819da32440010ff0abb4648800a1f215768c91001c7c432e1192200287e85dd932440010fb0bbb2648801a2fa12764c9100045ec24ec992200087f855d932440050f90abb264880022fe11764c9100345e422ec99220008df835d932440011df04bb264880023de05764c91001c7a408ec992204ec7471d95324400187ecbba264880030f197744c9100061fb28e89922000c3c651d132440031ed0db8a64880031dd97714c9100063a32ee2992200287c859d832440010ff0abb0648800a1f215760c9100045fc22ec19220068bc845d832440171b906bb064880163b209760c9100043e432ea192200087f87d9432440010fb0fb2864880063d219710c91002e72312e219220038f8865c032440179b0c6b80648813b8d107655051000637b2ee4a0a2000c6c65dc941440018deca39282880031b194725051000657b20e4a0a2074cac641c941440abb488239282881371d1db65505100071bb28c8a0a20039b68790d414400156d0d21a828801b2d1da43505100365a3b086a0a2000b358510d41440017630021a82881af391db72505103a6723b0e4a0a2055da7741c9414407facd0a39282880ff596147250510006b3b28e4a0a2000d64651c94144001b4ec83928288003691907250510006d32a0e4a0a2000da5541c94144001b4c8639282880036910c72505101fef1400e4a0a203fde1801c941440ab9cec0392828815778d807250510006d3a00e4a0a2000da5401c9414400136d0fa1282880ff691cb425051001cda43a84a0a2000ab486509414407fb48e4a128288003781cb705051027c3e432eb98a204d87f87d9731440010fb0fb2e62880034dd95748c5100069a32ae918a2003cb7605d23144007b66c0ba462880036c881748c51026e3a3b6ca98a20018f4865d1314407f3c904ba2628800395d94634c51001cea43a6498a2000ad4864c9314409b8ecedb2e42880026de1173c85100047ac3cc790a2000e6765d8b214400187ecbba242880030f19774485100061fb28e890a2000c3c651d121440f1958c43a242880032b1d3624851000c7d436e090a2042974865d421440078eec0ba8428800f5cd8175085101feb9102ea10a203fd71205d421440012ef0fb2842881375c9c365085101fcf2412e810a2000d37655d02144001a68caba042880ff69209740851001e5bb02e810a2003db3605d0214407fb6440ba042880ff6c48174085100066a432e610a2000d57655cc2144001aa8cab98428800f35d81730851001ee9b02e610a203fdd2205cc214407fba240b984288003355ce63085100047ac38c610a2000ae58218c2144001b4ae9a10428813b1e1db6548110005d8c20e2902203fbe08250520440017630918a4088003f04c93148110
  | 1 => 0x301baec6880021fa1f6558d100043f438cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a2000c6f65dc963440018d8cbb92c6880031bd947258d1000636328e4b1a200287e87dd5634400117f08baac68801a2f2117558d1000477c12eab1a20058ec825d563440010fd0e3aac6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000ce472dc5634409f8eae2328c68800237e1d6318d100054e422c631a2000acc8258c634400117f08b90c68801a2f2117218d100043fc2aeda1a200287c855db43440031e90cb8e86880021fe157690d100143e42aed21a20018f4865c643440050fd0bbb286880021f6177650d100043fc2aeca1a200287c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20058ec825d943440050f90b3b086880021fe157610d100143e42aec21a20068bc845d843440171b906bb086880023be097610d1002c76412ec21a200087c865d443440010ff0fb2886880021f61f6510d1000c7a432e221a2006cb4645c443440179a8c6b88868800e3e2197010d1005e6c31ae021a204fc757119762440031eb03baec48800a1fa1b755891026c3e436eab12200087e87d9562440010fd0e32ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c48800317d9773589100062e32ee6b122000c5f651cd62440018b8ca39ac48800a1fa1f75589100045fc22eab1220068bc845d562440011bf06baac48802e3720d75589100043f438eab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000cd7211cd62440019a84239ac4880032b1d372589100066639ee4b122000cd473dc562441398f2e0328c4880023be1d621891000556422c43122000acc8358862440010ff0abb6848800a1f21576d091000c7a432e3a1220018f5819da42440010ff0abb4848800a1f215769091001c7c432e1212200287e85dd942440010fb0bbb284880021fe1576509100143e42aeca1220008bf845d942440011bf06bb2848802e3720d765091000477c12eca1220018f686dc542440018e8cbb8a848800a1f21676109100043fc2aec212200287c855d8424400d17908bb0848800237e0d761091005c6e41aec21220058ec825d842440010f90cba884880021fe1f65109100043ec3eca21220018f4865c4424400b9c8c4b88848800e3e21970109100365c322e02122005
  | 2 => 0x8744c920006723b6e29924000ce4761c53248001b48e838a64900022fe1173d85200345e422e7b0a40008f78758461480015a906b08c29000e2fa1276d05200043fc2aed20a400287c855da414800b1d9043b2829000e2f21d64505202d656392c8a0a4003ab48159141480031dd0db9282900022f61f64105200365c322e020a40018ec865cb3148001998ec99262900021fe15760c5200143e42aec18a40008bf845d8314800d17908bb0629000e3d205760c52000c76432e418a4003ce4615c8314807f1eb0fb0c429000e2f21d545931005e2f982eb31e2000c5d305d663c400717f0eb24878800f2d9c56490f1000c7b40eeca1e2006c3e645d443c400187aeab2087880022fe117558b100345e422eab1620018f4815d562c40ad968e3ba2c58815ba90877458b102ae5a388e8b162055ea4211d162c40ab17f0eb2685880063d2057690b102b45fc22eca1620018f4815d942c40071790eb22858800f2d1c56450b100345e422ec2162055ce4215d842c40031e902bb465880022fe11764cb100345e422ec99620728f7815d932c40031e902bb2658800f351c6634cb1001c6e43ac69962003cd47158d32c400756d0d21a8388002cd61443507102aed3ba0e4a0e2050d66851c941c40a1acb0a39283881576961072507102aed3b20e4a0e2055da4641c941c4001b4ca83928388003695507250710006d3218e4a0e2000da4431c941c4001b4e8039283880036950072507102acdb43e84a0e2050da472d0941c40075690ca128388143691c94250710284f2412e898e20009b7845cf21c40011eb0f31e43880030f5d074d95102753b408e9b2a204da75811d3654409b4f5003a6ca8813a9e60074d951026d3d406e7b2a204ea7980dcf654400147f08b9eca880028f21173d95100062eb98e7b2a204ea76811cf654409b4eb0239eca8813a9da0772d951026d3ac0ee5b2a2000a3f845cb654400147908b96ca880031b5c872d951026d3d400e5b2a204ea79801cb65440010fd0fb2ac8880021fa1c65591100062fb2ee6b222000c5c65dcd64440018beca39ac88800317194735911000637b2ee4b222000c6c65dc964440018deca392c8880031b19472591100143f43eeab2220008df835d564440171b906baac8880023be09755911002c76412eab22200087e871d56444005878eb2a2c88827b2b1ca54591100145e43aa8b22209dcac7255164440018beebb9ac888003171d773591100062fba8e6b222000c5c751cd644400193ee839ac8880032795073591100064eaa0e6b222000c6f75dc964440018d8ebb92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c9644409f8eae2328c8880022fe1d64191100054e41ac83222000aac8259064440071f
  | 3 => 0xa10a600087f87d94214c0010fb0fb28429817b1e9c365085300045f434e810a6000c3f659d0214c001878cb3a042980022f21974085300061fb2ae810a6000c3c655d0214c00117f0fb2042980022f61f64085300061f3aec810a6000c3d75d90214c079974e1b20429801a2fe1c64085300045ec38c810a6000c3e75190214c00187aea32042980df2e9c064085300062fb2ce610a6000c5c659cc214c00193ec9398429800327192730853000c6e432e610a6000c5f655cc214c0018b8cab98429800327d9173085300064e322e610a6000ccd73d88214c0019aae7b0842980031ed9570085300063c32ae010a6000cbb645c0214c001970c8b8042980033ad89700853000679b0ae010a605ec7a76d97304c0bdcb6c7b2e60980f32e9db64cc1300365d3b0c99826000e3865193304c00187ee93a2cb900028fa1373597200051ec26e6b2e4000c5f739cd65c800b4dd0539acb9016e9b60a73597200053dc02e6b2e405ca78805cd65c800147d0838acb900028f610715972002c6e41ae931e400287e85dc563c80010fb0bb8ac79001637e1d63d0f2002e37392cb21e40058bf8759243c800b95ce4b2487900031b5957290f200143f42aec21e400087f865d443c80010ff0eb2887900021f61d6510f2000673bb0e29964000da4741c532c800d17d09b9ac3900022f61373587202bc77c12eca0e40018ec825d941c800b8d8e4b2a83900172b1c9645072001d5a40ac8a0e4000c6e65dc941c80018dacbb92839000a1fa1576cc7200043fc32eb98e400087f8759731c80010fb0eb2e63900030f996748c7200061eb2ce918e4000c3e655d231c800187acaba463900171b9c9650c72000636b2ae418e40028bf87553644800d878c8bacc8900030f5d764991200046fc1aeab22400b8dc835d564480011ef02baac89000e3d20575591200045fc3ac8322400087f855c763480050f90ab8ec69000a1fa1f7558d200045fc22eab1a40068bc845d563480011ef02baac69000e3d2057558d200047dc02eab1a400087e871d5634800187eebba2c6900030f1d77458d200061fba8e8b1a4000c3c751d163480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200063c3aee0b1a40008df8758c63480015a902b18c69002f17cc17518d200062e982ea31a400087f855da43480050f90abb486900063b2197290d200043fc2aeca1a400287c855d9434800117f08bb286900023de057650d2001c7a40aeca1a40068bc845d8434800d878c8ba886900030f5d76410d2000c76432e421a4006cac645c8434800b1f10cb80869016a2f61f64d09200066bb18e29924000cd4631c53248001958edba264900032b1d
  | 4 => 0x24c0010fb0fb2884980030f9d764109300061ebaec82126006c9c649cc424c0031b90cb98849801b2719173109300365c322e021260378be86dd1324c00187ecbba264980030f197744c9301e45f430e89926000c3f651d1324c001878ca3a264981d62fa1f644c9301e45e43ec899260768be87191324c00d1790e32264980031dd97714c9300063a32ee29926000cb764dc5324c001968c9b8a64980031dd94714c9300063a328e29926000cb7641c5324c001968c838a649800339d88714c9303be72310e29926000c7865dc1324c0510f90cba864980021fe1f650c9300543ec3eca1926000c3e75d90324c00187aebb2064980030f9d4640c9300061eba8c81926000c3f659d2614c001878cb3a4c2980030fd9574985300061e32ae930a6000c3e75d92614c00187aebb24c2980030f9d464985300061eba8c930a600287e86dd5614c0010fd0fb2ac2980021fa1c65585300061fb2ee8b0a6000c3c65dd1614c00187eca3a2c2980030f19474585300045f43ec8b0a6000c3f75d91614c001878ebb22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c13f93ee6322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980031bd94725853000636328e4b0a6000caf641c9614c001958c8392c2980023de1d611853000572412c230a600087f855db414c0050f90abb6829800e2f21176d05300043fc2aed20a600287c855da414c0050fd0bbb282980021f617765053002c77414eca0a60008ed829d9414c00756d03b2282980031bd9772505300063632ee4a0a6000caf64dc9414c0d7958c9b9282980031bd94725053000636328e4a0a6000caf641c9414c0e9958c839282980021fe1576105300143e42aec20a6000c78655c0414c00d970c8b8082980661f21975cc5300043fc3ecb98a600a87d87d97314c00187cebb2662980030f5d764cc5300061f3a8c998a6000c3d75193314c07917d0d3a462980030fd96748c5300061e32ce918a60378bc865d2314c00187ecaba462980030f195748c5301e45fc3ec918a60008bd87d92314c00d17f0e32462980022f61c648c5300063c32ae118a600087f855db214c0050f90abb642980022fe1176c85300345e422ed90a600087f855da214c0050f90abb442980022fe1176885300345e422ed10a600287e85dd9214c0010fb0bbb2429801a2fa1376485300045ec26ec90a60068be849d9214c00117b093b242980022fa1b74485300061fb2ee890a6000c3c65dd1214c00117d0c3a242980030fd9474485300061e328e890a60008be87d91214c0011790fb2242980022fa1c64485300345e438c890a600287c859d8214c0071b9073b042980063e20276085300043fc2aec10a600287c855d8214c00117f08bb0429801a2f21176085300043e432e
  | 5 => 0x80032bd9072507303a656320e4a0e60008bf845db21cc00d17908bb643980022fe1176487300345e422ec90e60038dd835d821cc0071e902bb043980030f5d074d95300051fc22e5b2a6000a3c845cb654c0018dae4396ca980028fa1271d95300051ec24e3b2a6000c3d75d53644c00153b07aa6c89800b0f1d654d91300145fc3aa9b2260a3e1d83197644c001c38cb29ec8980f2a721953d91300061eba8ebb226000a9e831d7644c07953b063aec898002aba0875d913000556c10ebb22603c8be87d4f644c00117b0fa9ec89800387d4e53d91300051f42ce5b226000a3d859cb644c00117d0fa96c8980022f61f52d913000717a94a5b226000aae82dc7644c00155b05b8ec8980032ddc671d91300045f438a3b2260008bd87147644c00d878c8bacc8980030f9d764991300061ebaec9322600087e87d95644c0010fd0e32ac89829f17dcc65591300143f43eeab2260008bf845d5644c0011bf06baac8980023ee0175591300043f438eab226000c3f75dd1644c001878ebba2c898003171d773591300063c3aee0b2260008bf87590644c00147f0ab20c8980028f21564191305361f3b6ca32260008bd87994644c14347d0b328c8980022fe1d651913052d4fc1aca32260a4a3e86194644c14787cec328c89828b8760c65191305170f180ca32260a2e1c30194644c145c7060328c898286a7a1a53191300070e32ca63226037a9c8654c644c001c38caa98c89801a2fa1f53191300045ec3ea63226000e1f5394c644c00157700a98c8980deae20153191300070ea98a632260068be87d48644c00117b0fa90c8980038bd4a52191300054f418a43226000a9d83148644c00153d07a88c898002a760f51191300345f438a232260008bd87144644c079970e1b2286980031e1977050d301c43e432ea21a6006c3c645d4434c0010ff0fb28869802a1f61f6510d300061f3aec821a6000c3d75d90434c00187ecb3a4c4980030f19674989300061fb2ae93126000c3c655d2624c00187cebb24c4980030f5d764989300061f3a8c93126000c3d75192624c14193ae6324c4980021fa1f65589300043f438cab126000c3f65dd1624c001878cbba2c4980030fd9474589300061e328e8b1260008be87d91624c00187eebb22c4980030f1d764589300045f438c8b126000c3f75191624c001878ea322c4980031dd9771589300063a32ee2b126000cb764dc5624c001968c9b8ac4980031dd9471589300063a328e2b126000cb7641c5624c001968c838ac4980023be1d62189300057240ac4312600087f855db424c0050f90abb684980162f21176d09300043fc2aed212600287c855da424c0050fd0bbb284980021f61776509300143e42cec212600087f855d8424c0050f90abb084980021f21975109300361e322ea212600087f87d944
  | 6 => 0x61eb2ee890e800287e855d821d000717b08bb043a00021fe1975087400043fc3aca10e800087d8759421d000d87ce8b2843a01d38b109650874038e3d382ca10e8000c3e655d021d000187acaba043a00031799673087400062eb2ce610e8000c5e655cc21d00018bacab9843a00031e99570087400063cb2ae010e8000c5d75d4f635000153b09a9ec6a00021fe1571d8d400143e42ae3b1a80008df8758c63500014b90ab18c6a02a2a7e116318d4005c6e41aea31a800bc5c835d463500178be60ba8c6a0003174c17518d400045ec3ca831a8002c3e75950635000153b072a0c6a000b0f9d55418d400054fc1aa831a8000c5d75d4c635000153b09a98c6a0003875535318d4005d4f436c6a1a8000a9e8718d435001793d0e31a86a002f87a146350d4005f0ec28c6a1a80018bd84dd762500011df0eb10c4a00de2f21973909400051ec28c72128000c9d7318e425000d87ec0ba884a001b4ed8175109400045ec38c62128000a3d8518c425000187aea31884a0003275cc631094000556c10c621280558bc865c442500010ff0abb664a000a1f21576cc94000c5e432e9992800bc9c635d3325000317b093b464a000e3da06764c9400047ac0cec99280068bc841d9325000317d0dba264a000327dd0634c9400066bb18e29928000cd4631c532500031790cba064a00023de1d61185400045ec38c7a0a8000a3d8518f415000193ae631e82a016a2f61f62d054035ed4206e4a0a80378be86dcd415000147b0a31a82a000327dcc63505402be563b6e4a0a8000da870dc941500ab958ec39282a016b2ba1872505402d656c30e4a0a805ad2e851c941500b5a5b0a39282a00032bd94725054000656b28e4a0a8000cac631c941500ab95cc239282a01572b184725054035657b00e4a0a8074dab601c941500ab17d0fb1282a016b2b1cb6250540006d4396e0a0a80018bc865d33150007179093b462a00062f219748c5400064eba0c718a80018bc865d131500b535904ba262a00021fe15760c5400143e42aec18a80018bc865d03150017938c6ba062a002f3618d700c54000c5ec24ed90a800087f855da21500050f90abb442a000237e0d768854005c6e41aed10a80018bc865d2215000d179083b242a00062fa1b744854000cdd406e890a80038bc849d821500031790cba042a016a6b209740854000656ba6c410a8000ceb625c0215000517f0eaa6c9980022fe117558b300345e422eab1660008f7815d562cc0071e902baac5980032ddd37158b300065a3a6e2b166000cb7741c562cc001968e838ac5980022fe117650b300047bc0aeca1660038f4815d942cc00d17908bb0859801b0f1917510b300061ebaec82166006c9c645cc42cc00717908bb683980023be09765073002c76412eca0e60038be87d9141cc00756d03b22839
  | 7 => 0xea821d5600841f5d3043aac01080ebca04755802107d78c08eab004200a7a859d160084014f30b3a2c010816ba209745802101d79408e8b00420faf1811d1600840b5d505aa2c010802ba60b54580210071daa4a8b004200a7b855cd60084014f10ab9ac010802aee1173580210055c422e6b004205ae8825cd60084075e102b9ac0108029ea1473580210053cc28e6b004200aba841cd60084015730839ac010816baa08735802107d74c10e6b004203af2811cd600841f5e30239ac010802aea1353580210055cc26a6b004205aea82d4d60084015d305a9ac01080ebca07535802100578c0ea6b004200e5b5394d60084075e503a1ac010802bc607435802102d7541486b004200ae98290d60084014f50a21ac0108029e61443580210351f426e6b2e800ea3d84dcd65d000d47d0939acba01c28f61273597400062fb9ce6b2e8000a7b805cd65d00e34f100b9acba0003175cc73597400351f426e4b2e800ea3d84dc965d00018dee5392cba01be8fe1172597400351e422e4b2e8000a77815c965d00014e902b92cba001a8fa12715974036d1ec24e2b2e8006a3e841c565d001d47b0838acba00022fe1d5498f400143f42ee2b1e800087d85dc563d000317908baac5a00023de057558b4001c7a40aeab168006c3e7259642d000dc5ce4b2c85a00022f61e6390b402b45fc32e32168000c3d655c642d000d87ce8b2e65a00030f59574ccb4000c5e422ed19680768bf845d932d000317908bb265a00023de05764cb4001c7a40aec9968006c3c7459532d000187ccbba265a00030f597744cb400063b32ee29968000c7565dc532d00018ecca38a65a00031d594714cb400143f42aec196800087f865d432d00010ff0eb2865a00021f61d650cb400061e392caa0e8000e378159541d0001c6902b2a83a001b0fdc565507400371bb8acaa0e80a9e371059541d0153c6a20b2a83a00022fa1e635074001d5b40cc6a0e8000e2d65dc941d000195eec39283a00038b594725074035657430e4a0e806acad861c941d00d5a5d0a39283a01ab4b61472507403a657b28e4a0e8074d2e651c941d000195aca39283a01d34b594725074000616b28e4a0e8000cae631c941d00ab95cc239283a01572b1847250740356d5400e4a0e806ada9801c941d00d51790eb1283a01ab2b1c9625074001d5a40ac4a0e800287e855db31d00010ff0cbae63a00021fe1d65cc7400043ec3acb98e80038bd845da31d000d87ce8b2c63a00030f995748c7400061eb2ae918e80018be84dd931d000117f0cba263a01aa6b209744c7400361f3a2ca18e8000c3d655d031d000317908bb643a00030fdd165c87400361e3a2cb90e8006c3e7459621d00d7c5884b2c43a00030f59574887402b45fc22ec90e80018bc845d921d000d878e8b2a43a00030f99774487400
  | 8 => 0x9a9cc6108021fe157098c210143e42ae131842008bf845c2630840d17908b84c61080e3720d7098c2105e2fbaceb3184200a9e849d6630840153b093acc61080387d525498c210052fc2ae13184200a5c855c2630840153f08b84c610802a72117098c2105c6f438a131842008dd87142630840153d08284c610802a76105098c2102d67410a13184200acd8214263084075ad02284c610802b56045098c2101d6b408813184200ad58110263084071e902baac61080e37a1f5358c210062fbaea6b184200a9e84d4d630840153b09a9ac610816b3a0b5358c2101d6b40ea6b184202c5e7594d63084071b90ea9ac61080eb5a063058c210052f42860b184200a5d850c1630840153d08182c610802a76103058c2102d6741060b184203ad6810c163084018beeb3aac610802a7a127558c210054ec24eab184205ace829d5630840159b053aac61080eb5a067558c210056ac0ceab184200ad7815d563084075a902baac61080eb5a067458c2102d66412e8b184203ad4815d163084014bd0a3a2c610802976147458c2102d67416a8b184200acd82d516308401c3ea92a2c61080eb52077058c2101d6b40ce0b184200ad5819c163084014bf0ab82c610802972157058c210054fc22e0b184200a9c845c1630840b59904b82c61080eb52057058c210052f428e0b184200a5d851c1630840153d08382c610802a76107058c2102d67410e0b184200acd821c163084075ad02382c610802b56047058c2101d6b40ca0b184200ad58194163084011bd0e282c6108023761c5058c210054f420a0b184200a9d84141630840b59d04282c610802b36085058c2101d6b408a0b184200ad581141630840b59d05202c610802b360a4058c2101d6b40c80b184200ad58190163084075ad02202c610802b56044058c2101c6fc3ac7a184203cd67158f430840d96cc8b8e86108033558d71d0c2102e37392cb21842038bf8759243084ed55904b2486108172b9c96490c2100636b2ae52184200cad645ca430841799cc6b9486108163b2097650c2101c7a40aeca1842038bc8759143084071b90eb1a86108032b5937250c2100666b1ee4a184200cb564dc543084019aac7b8a861080a1fa157610c213ae56212ec218420087f865d4430840d87cc8ba8861082f1798d7510c213a696212ea2184200c7a605d443084010ff0eb2886108021f61d6510c210061f3aac82184200c3d7559043084eb55904b208610803179d56310c210062ebaac62184205aaf87593420840b95f0eb26841095fa9c4164d082101d6ac1aed9884203ad78758f31084079af0eb1e6210803959d563cc4210072abaac79884200cd5635c331084013cf04b86621080e3ea1f505802101c7c43aa0b004200aba841d56008401573083aac010802b6a0c75580210056cc18eab004205a
  | 9 => 0x64cc5213c657390c998a4200c5d75d8f3148401958c8b9662908022fe11764c5210345e422ec98a4278cac721913148401958c9b9262908022fa1f64581210061fbaec8b024200c3c75d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9f64dcd6048401938c9b9ac09080327d9073581210064e320e6b024200c3f749d165085594df04ba2ca108169b209745942155d3bc0ae8b284203a74815d1650840147d09b9aca108028f61373594210062fb9ce6b2842aaa77815cd65084074e902b9aca1080e9da06705942120d3ac0ce0b284200a3e841c1650840147b08382ca1080297a0c70594210052ec18e0b284205a6e821c165084214db04382ca1080e9da0470594210853ac08e0b284205a6e8290165084014db05202ca1080e9da0640594210053ac0c80b284203a768110165084014eb02202ca1080e9da0630594210053ac0c60b28420087e870c165084010fb0e182ca108028fa1030594210051ec2060b284205a6e820c165084014db04182ca1080e9da0430594210053ac0860b2842068be87d4e640840117b0fa9cc81080387d4e53990210345f438a132042008bd87142640840153d06284c810802a760c509902102d57410a13204200aad82142640840756d02284c810802ad60450990210345f4386132042008bd870c2640840147d0a184c8108028f614309902102d57410613204200aad820c2640840756d02184c810802ad604309902102c76412eab2042038f4815d5640840717d0faa2c8108030fdd7545902102d57416a8b204202c3e75951640853d958e52a2c81080e2f21d54590214ee56392a8b20420287e85dc164084010fb0bb82c81080eada06405902101d5b40880b20429ecac72dd5640840187eeb3aac810816aba0a755902100556c14eab204200aaf825d5640840b55904baac810a772b1c975590210055bc0aeab204203ab4815d5640840b55d0539ac8109db2b1ca735902102d56412e6b204203ab4815cd640840147d0a39ac8108028f61473590213ae56390e6b2042008be87d4d640840117b0fa9ac81080387d4e53590210051f42ee0b204200a3d85dc164084d5958e5b82c810816aba0a705902100556c14e0b204203ab6819c1640840156b03382c810816ab209705902101d5b408e0b204200ab5811c1640840756d03282c810802ad60650590210045f438a0b2042008bd87141640840153d06282c810802a760c505902102d57410a0b204200aad82141640840756d02282c810802ad604505902101d5b40c60b204200ab5818c1640840117d0e182c8108022f61c30590210051f42860b204200a3d850c1640840b55d04182c810802ab608305902101d5b40860b204200ab5810c164084071b906bacc61080e3720d7498c2105e2fbaea73184200a9e84d4e630840153b
  | 10 => 0xb224200ab581103644840153d0732ec890802a760e65d91210061eba8ebb224200a3e859cf644840147b0b39ec8908022fa1f53d91210045ec3ea7b224200e1f5394f64484ad17d0fa96c8908022f61f52d91213cf17296a5b224256e3651d4764484ad56d03386c890802ad60670d91210065db84e1b224200a3f855c364484014790ab86c8908022fa1c50d91210045ec38a1b224200a9e83143644840153b06286c8909e6aba0850d912100556c10a1b224256ab681143644840156b02286c8908022fa1c30d91210045ec3861b224200a3e850c3644840147b0a186c8909e6aba0830d912100556c1061b224256ab6810c3644840156b02186c8908022f61e20d91212b55b40c41b224200ab581883644840117f08baac8908023be0975591210047bc0aeab2242008bf87590644840117b0f328c890802a7a0e65191210054ec1cca32242008bf87594644840d17d0fa98c8908022f61f53191210070fa9ca63224278aae8214c644840155b04298c89081a2fa1f52191210045ec3ea43224278e2e52d48644840156f02a90c890956ad20552191213c557416a23224200aad82d44644840155f04a88c8909e2ab20951191212ad57c124232242068be87140644840117b0e280c890802a7a0c50191210054ec18a03224278aae82140644840155b04280c890956ada0450191210055ac08a032242068be870c0644840117b0e180c8908028fa1430191210051ec28603224278aae820c0644840155b04180c890956ada0430191210055ac086032242008bd8788064484ab56d03100c890802ad60620191213c557414203224200aad8284064484051bf0ea9ec6908029761430d8d2100566c1061b1a4200ad5810c363484178b8c6bacc6908030f9d76498d210061ebaec931a4200c3e75192634840187aea324c690803175d76398d210045f43ec8b1a42008be87191634840117f08baac69081a2f2117558d210047bc0aeab1a42008fb805d563484031f100baac6908032b1d37258d210065bba6e2b1a4200cb474dc563484011bf0eb18c6908021fe157018d210143e42ae031a42008bf845c0634840d17908b80c69082e2f21176d0d2100477c12eca1a42008f7815d9434841717d0fb22869081b0f1917510d210061f3aec821a4200c3d75d9043484071d90cb90869081b2b1917210d2102c7a432e221a4206cb4645c4434840d968c8b8e849095b2d1c764509212ac5f436e899242568be861d132484ebb48423a264908022fa1f644c9212b45e43ec89924256cb471d91324840117d0e322649081a2f21c644c9212ae5a388c89924200cb764dc53248401968c9b8a64908033518f714c92103656322e5a0a4279cac72d9141484d7958c9b92829082f1718d75cc5210061f3aec998a4200c3d75d93314840187cea32662908030f5d4
  | 11 => 0x8c40156b03182c9188022f61c30592310051f42860b246200a3d850c1648c40155d04182c918802ab608305923101d5b40860b246200ab5810c1648c40117d0f102c9188022f61e205923101d5b40c40b246200ab581881648c40756d02102c918802ad60420592310365b322e3a1c6200cb564dc5438c40d87cc8ba887188030f9d56410e310061ebaac821c620287e85dc1628c4010fb0bb82c518816ab2096450a310361f322ea2146200c3e75590428c40187aeab20851881b2d9917110a310045ec36e899462008bd861d1328c4ed17d0f322651880f2d1c6644ca313ac5e43ac89946203cb471591328c40196cc9b8a65188032d593714ca310061f3acc81946200c3d75990328c40187ceab2065188030f5d5640ca310345f426e4b0462008bd84dc9608c40517f0eaa6c8988021fe1570d91310143e42ae1b226200ab581103644c4011df04baac8988163b20975591310047dc02eab2262018f8805d5644c40195ee8392c898803391cb71591310045fc3ac83226200aac82590644c4ed55904b2486988022fe1d6410d313ad56412c821a62028ef8754b624c4010ff0ab86c49880a1f21570d89310055742441b1262008ef87588624c40155908b10c49881b0f191751093102e36312ea2126200c3d75d90424c40d938c8b98849881733189731093100636baec42126275cac621d1324c401958e9b1264989cb3918b714c9313b64e3b6e89926275c9c761d1324c4e59a8edb8a64988032bd9072505313a656320e4a0a620bd54315d7314c4e5d88c499662988022fe1172d81310345e422e5b0262018f4815cb604c4071790eaa2c8188022fe1175588310345e422eab106256cb471dd1620c4add4843ba2c4189572d1c474588312af52108e8b1062038ec87549620c4075c902a92c4189562fe1d64d083103556422c52106203cb471591420c4079c8e2b12841895739085761083105e6b29eec9886200cd553dd9310c4050fd0fbaac01893a1fa1c755803100c7ac0ee4b0062038f887541600c4050fd0bb82c9908021f61770593210043fc2ae131e420287c855c263c840117f08baac79081a2f2117558f210047dc02eab1e42018f8805d563c840196ee9b8ac7908032d1d37158f210347bc32e3a1e42768bf845d943c840d17908bb087908030fd917510f210361e322ea21e4206cac645c843c84ad17f0eb26839095e3be1972d072102e56392c8a0e4200c76755db31c84018eaecbae63909de3de1d63cc721006b2baae598e42038bc87551648840717f0eb24871082e3be197290e210361f322ea21c426bd2c425d4438840187aeab2087109562fe1d64d0a2101e5a38ac8a1442728f7865c732884079a8e331a651080a1fa1f75582212743f438eab044200c3d75d53644840517f0eaa6c8908021fe1570d91210143e42ae1
  | 12 => 0x81b271d2634c84101e6a38cc699082018bd84dc960104071f50fa82c0208030fdd274597310051f426e4b2e6200a3d84dc965cc4174bd07392cb98ab69760e725973100637b94e4b2e6200a77815c965cc5034e902b92cb98a0297e0d71597310051f420e0b2e6200a3d841c165cc4174bd06382cb988669760c705973100537410e0b2e6200a6d821c165cc5034ed02382cb988029d604705973140d3b40880b2e6200a758110165cc40147d09102cb988028f612205973140d3b40c40b2e6200a758188165cc4174bd06102cb988029760c205973105d2f41c20b2e6200a5d8384165cc40587ceb2a6c998a7b2b9ca54d93310145fc3aa9b26629dcae7255364cc4050fd0bb82c9988021f617705933105e2f39ccb316620bc5e7359662cc417c9e64b2cc59880a1fa177058b310043ec2ee0b16620bc5e7359642cc41793ce6b248598803175957390b310063b32ee2a16620287e855d842cc4010ff0cba885988021fe1d6510b310043ec3aca2166281c747159532cc40187ccbba265988030f597744cb310061f328e89966200c3d651d132cc4018beecb2a6598a07551c5654cb310066bbb6e29966200d97741c532cc401b28e838a659882f171cd65507310062eb2ee6a0e6200c6e65dc941cc4018dacbb9283988031b994725073100636b28e4a0e6274cae641c941cc40195ac8392839881a2fa1372583310045ec26e4b0662068be87d4e648c40117b0fa9cc91880387d4e53992310345f43ea532462008bd87d4a648c401c5ea5294c91881a2fa1c50992310045ec38a13246200a9e83142648c40153b06284c918802aba08509923100556c10a13246203ab681142648c40156b02284c91881a2fa1c30992310051f428613246200a3d850c2648c40155d04184c918802ab608309923101d5b408613246200ab5810c2648c40d17d0f104c9188022f61e209923101d5b40c413246200ab581882648c40717d0faa2c9188030fdd754592310054ec1ea8b2462038bc87551648c4050fd0bb82c9188021f617705923101d5b40c80b246203ab681101648c40187eeb3aac918802a7a0e75592310054ec1ceab246200aae829d5648c40155b053aac918802abe09735923100556412e6b2462008be87d4d648c40117b0fa9ac91880387d4e53592310051f428e4b246200a3d851c9648c40195ae4392c9188022fa1f52592310045ec3ea4b246200e2f52949648c40147d0bb82c9188028f617705923100557414e0b246200aad829c1648c40756d03382c918802ad60670592310054fc1ae0b246203ab6811c1648c40156b02382c91880eada0650592310055ac0ca0b2462008be87141648c40117b0e282c918802a7a0c50592310054ec18a0b246200aae82141648c40155b04282c91880eada0450592310055ac08a0b246203ab6818c164
  | 13 => 0xd5640ca83128200aad8095062504015cf02aa0c4a0956b920554189414ed57c3aa83128274e2f85550625053bc5ceaaa0c4a0a778b5d554189410055641aa83128200ea78155062504ab55d02aa0c4a0956ab20554189410075240aa83128200aaf8055062504e955d09a98c4a0802ab613531894100716aa6a63128200e4f5394c625040155f08a98c4a09d2ab211531894100716aa2a63128274aae8414c625040155b08298c4a09daab61e431894100557c2c863128200aad8590c62504edc5ceb218c4a09db8b5d643189412ad5740c863128255aac8190c625040155b01218c4a0802b9e0543189412ad7240a863128275aaf8710c62504eb55b0e218c4a09d2abe1443189413a717428863128200aad8510c62504e9c5b0a218c4a08028b61443189413af173a8863128275e2d7510c62504e9d1d06218c4a09d7a39cc43189413af46b98863128255aae8110c62504ab55902218c4a0802ab60043189413a557426a23128200aad84d44625040155f08a88c4a09d2ab21151189412ad57c22823128274aae84d40625040155b09a80c4a09d2aba12501894100556c24a03128200e2d5494062504ab5cd03280c4a0802b9606501894102c77438a031282008ed8714062504e955d08280c4a0802ab610501894100716aa0a03128200ace83140625040159b06280c4a0956b9a04501894100572c08a03128255ae68190062504015cb03200c4a09d2aba12301894100556c24603128255ae6818c062504015cb03180c4a08163ba1c301894100476c38603128200a6e850c062504014db0a180c4a09d2aba10301894100556c20603128255ae6810c062504015cb02180c4a09d2aba12101894100556c24203128255caf829db42504ab95c433b684a09572b08676d09413b656314e7a1282039b6819cf425040195cedb1684a09572b9d862d09412d656312e1a128205ce4625c642504af9c8e3b1284a08024f61473509413ae56310e6a128205aae86d8942504af958edb1284a095f691c762509412ae573b0c4a128255da471189425040736d0fb8a84a095f69dc871509410049ec2ee0a12826acac62dc1425040717d0dba664a09db2b18b74cc94101cdb40ee999282058ec825da325040b958c4ba464a080e6d205748c9413b656316e8992826bcac74d8932504af9c8e3b1264a09cb3918b714c94102e36312ea1928205cac625d032504018dcebb1064a08031b5d7620c94102e72312e21928202c3e75553605040317908b96c0a08023ba1f625814100637baec4b028200c6c75d89605040199ee7b12c0a0803331cf625814100477438c4b028200c6f7518960504018d8ea312c0a080333dcc625814100666398c4b02820087f855c263104050f90ab84c62081a2f21175588410143f42ee0b10820087d85dc1621040117f0cba66420
  | 14 => 0xe84041650c80147b08082ca1900a1fa1770590320043ec2ee0b20640bcce53dd9320c80199aa7bb264190032bddb744c83200657bb0e89906400ce776dc5320c8019ceec38a6419003691d0714c8320043fc2ae131e820287c855c263d040717908baac7a08023ee017558f4100c7c402eab1e82768bf865ca43d047917f0cb8487a08024fe157090f410143f42ee0b16820087d85dc162d040127b0a39a85a08024f6177050b4101c5e422ed99682038bc845d932d050387e82bacc720a070f5057598e412ac77c3ac52148200a3d8598e42904079c8e2b1285208028f6166310a4100556c14c621482038f4815d9329040193ee931a652080f351c6634ca410143f43eeab04824ec3f41dd5609049d87a83baac12093a1fa1c75582410061fbac84b048200c3f7510960904051bf0ea9ec6a08029761430d8d410054ec2061b1a8200ad5810c363504178b8c6bacc6a0803175d76398d410046fc3ac631a8202c3e755506350401c3aa8a98c6a08021fe157018d410143e42ae031a82558bc865ca43504ed958c4b9486a080e6de1d7190d410049fc2ae121a8200c3c625d4435040d87ec2ba886a081b4dd857510d413ac5e432e421a8275cac625c8435040736902b9086a08de2f2197010d4100636baea5b128200aad84d4b62504051df0ea96c4a08021fe1570d89410143e42ae1b128200ace83997625040159b0732ec4a095eab21954d89410053742cc7b128200a6d8598f62504af55d0d21ec4a095ee9a0643d894100596c2887b128200c6d751d762504d755d083aec4a095eab61075d894135f172a6a9b128257aad84dcf62504d75cb03b9ec4a08029ba1673d894100536c2ce7b12826baae84d4f625040155b09a9ec4a080393d4e53d89412bf3328ea3b128200a6f855c362504014d90ab86c4a09aeaba1070d89412bd56c20e1b128257ae6811c362504d75cb02386c4a08023ba1c50d894100476c38a1b12826baae84143625040155b08286c4a0802b3a0c50d894100566c18a1b128257ae68114362504015cb02286c4a08023ba1c30d894100476c3861b128200a6e850c362504014db0a186c4a09aeaba1030d894100556c2061b128257ae6810c362504015cb02186c4a08171b189751894100477c3ac43128200c6e769d462504f3c5ec93a8c4a08031b9d975189413cf17b22ea31282008ed87994625040159d07328c4a0802b360e651894100477c3aca3128200aae8695062504ab5590caa0c4a08038bd95541894100476c3cc63128200a6e8598c62504014db0b318c4a08023be1d63189412ad57434863128200e8c6390c62504ab74d03218c4a0802aba18431894100596c28863128274e2e54d50625053d55f0f2a0c4a0a7aab61e54189414f7173aca8312829ee2d75950625040155d072a0c4a0956aba0654189412a
  | 15 => 0xbb96c2990029d61772d85320055b426e5b0a6400ab584dcb614c80156d09a96c299002ad61352d853239733296a5b0a6400a7685dc3614c8014eb0bb86c299002ada1270d85320055ac24e1b0a6472ae6821c3614c8015cb04386c2990023da1c50d85320047ac38a1b0a6400ab684143614c80156b08286c299002b5a0c50d85320056ac18a1b0a6472ae682143614c8015cb04286c2990023da1c40d85320047ac3881b0a64008f6870c3614c8014ed0a186c2990029d61430d85320055b42061b0a6400ab5840c3614c8e55cd04186c2990023d61e20d85320055b42441b0a6400ab584883614c807968c33a4c29900f2d18574985320065b3a6c330a6400cb574d86614c80117d0fb22c2990022fa1c64585320047bc3ac230a6400ab784584614c80156908b08c2990023d61e65185320055b424ca30a6400ab584994614c8011ef0eb28c299002ade1165185320055a422ca30a6400af380594614c8015e100b28c2990032d9db64185320047ac3cc830a64008f787590614c8014ed0a320c2990029d61464185320065b3b0c830a6400e3685190614c801c6b0a320c299003a5d9173185320074a322e630a6400ea464cc8614c80156d09300c299002ad61260185320056b41ea830a6400ad583d50614c8ef5cd05aa0c299002b960b54185320071baa4a830a6400ab684d4c614c80156b09a98c2991deb9a0b531853200572c16a630a6400e575394c614c8015cf04a18c2991deb920943185320053b4288630a6400a758510c614c80156d09a90c299002ad61352185320056b41ea430a6400ad583d48614c8efccca5a90c2991dfa910942185320055bc226430a6400ab4844c8614c8071ed0e280c2990023d61c50185320055b420a030a6400ab584140614c8015ad06280c299002b560c50185323bd73410a030a6400ae582140614c8ef5cd05200c299002b960a401853201c7b4388030a64008f587100614c8071ed0e180c2990029da1430185320053ac286030a6400ab6840c0614c80156b08180c2991deb9a0830185320047ac3c4030a6400ab684880614c80156b09100c2990031e5d750d81320045f43ec8b026400c3f75d91604c801878ebb22c0990022fa1c64581320061fba8c8b026400c3c75191604c80196ec9b8ac0990032d19371581320065bb20e2b026400cb4641c5604c8011ed0fb0ac0990031ddd761581320063a3aec2b026400cb774d85604c801968e9b0ac0990023da1c61581320063bba8c2b026400c7475185604c80196ee830ac0990032d1d061581320061fba4e8b286400a3e841c5650c80147b0838aca190028fa1070594320051ec20e0b28640ba5e831c1650c8514bb06382ca190169ba08705943214536c10e0b286400a76811c1650c8014eb02382ca190029da0440594320053ac0880b286400a3
  | 16 => 0x5d91320055c402cbb226400ab681983644c80156b03306c8990030f5d475d91320054f418ebb226476a9d831d7644c8ed55d043aec899002ab60875d91323b45f43ea7b2264008bd87d4f644c801c3ea729ec8990022fa1f52d91320045ec3ea5b226476e2e52d4b644c80155b05b8ec8991daa760c71d91320045f438a3b2264008bd87147644c8ed53b07b86c899002ada0670d91320055ac0ce1b226400a3f855c3644c8014790ab86c8991daaba0870d913200556c10e1b2264008be87143644c80117b0e286c899002a7a0c50d91320054ec18a1b226476aae82143644c80155b04286c899002ada0450d91320055ac08a1b2264008be870c3644c80147d0a186c8990028f61430d91323b55741061b226400ab6810c3644c80156b02186c8990022f61e20d91320055b40c41b226400ab581883644c80117d0e086c8990022f61c10d91320065bb24e33226406cb4649c6644c80196ec8b8cc89901b2d19171991320045fc22eab2264008f7815d5644c8071e902baac8990023ee01755913200c7c402eab226400cb774dc5644c80196ee838ac89900339dc871591320361e322ea32264008bf87590644c80156f02b20c899002ad20564191320061f3b4ea3226400c3e765d4644c80117b0f328c899002ada0665191320055ac0cca32264008bf87594644c80156f02b28c899002ad20565191320055dc02ca3226400ab880594644c80156d03300c899002ad60660191320345f43ea632264008bd87d4c644c801c3ea7298c89901a2fa1f52191320045ec3ea43226475e2e52d48644c80d17d0e288c8990022f61c51191320345f438a032264008bd87140644c80153d06280c899002a760c50191323ad57410a03226400aad82140644c80156d02280c899002ad60450191320345f438603226400a3e850c0644c80147b0a180c8991d6aba0830191320055b408603226400ab5810c0644c80117b0f100c899002ada0620191320055ac0c403226475aae82840644c80155b05080c89901a2fa1c10191320045ec38203226476cac72d91434c80d878c8ba886990030f9d76410d320061ebaec821a6406a9c8650c434c80d938c939e849900327d9073509320063abaea3b0a64028f787547614c80156d0828ec299002ad61051d85320055b42021b0a6400ab584043614c80156d0932ec299002ad61265d85320055bc22cbb0a6400ab484597614c8015e700b2ec299002bc20165d85320053b428c9b0a6400a7585193614c801c6d0a326c2990038d61464d85320055b424c1b0a6400ab584983614c80156d093aec299002ad61275d85320063aba8ebb0a6400ae582dd3614c8014ed0a3a6c2990029d61474d85320071baa4a9b0a6400ab684d4f614c80156b09a9ec29900395d4e53d85320053b42887b0a6400a758510f614c8014ed0
  | 17 => 0x288638a3d841c56510d5f47f08b82ca2181a8f21170594435752fc1ae0b28860ba5c835c16510c0d47d08382ca218e28f610705944305d2f418e0b288638a5d831c16510c014dd04382ca218029b60870594430053b408e0b288600a75811c16510c0d47d09102ca218028f61220594430053b40c40b288600a75818816510c0d47d08082ca218028f610105944305e4f29eeca188600c9d53dd94310c011ef02baac42180e3d20575588430143f42ee0b10860087d85dc16210c0d17908baac0218de2f21d54580431bc5e43a86b008637ab88050d6010c010ff0ab84c7a100a1f2157098f420161f3aaa931c8400e1d5454e63908010ff0ab84c72100a1f2157098e4202c6e43aa6b1c8400a5d850c1639080153b08182c721016b3a083058e420056ac0860b1c840093f855c2439080d87cc4ba8872101b4b9897510e421bc5fc32e021c8437cba605c043908ad17d0f2a2c32115a2fa1c43586420051ec2886b0c8402c3c7555160908011bf0eb18c6a10030f9097518d420061e212ea31a8400c7575d47615080156b0828ec2a10023de1d61185420043ec3cebb02840287f875d7605080187c84baec0a10030f10975d81420351f426e6b288430a3d84dcd65108018bee739aca212468fe1173594420351e422e6b288400a7b805cd65108014f100b9aca212268fe1171594420351e422e2b28847aa6f825c5651080b4d904b8aca2101a8fa1071594421851ec20e2b288406a3e849c165108c947b09382ca2101a8fa1070594421851ec20e0b288400a5e831c165108014bb06382ca210169ba08705944218536c10e0b288400a76811c165108014eb02382ca2101a8fa1230594420051ec2460b28840087e870c165108010fb0e182ca2101a8fa1030594420051ec2060b288405a6e820c165108014db04182ca210029da0430594420053ac0860b288406a3e84841651080147b09082ca210169ba0a105944200536c1420b288406a3e84041651080147b08082ca210021fe157098c420143e42ae131884068bc845d563108011f700baac6210063e2017558c420143f42ee2b18840087d85dc5631080d93ce6bb4862101b0f9cd6590c420370f39acb218843c8bf865c2431080127f0ab8486210030f5957090c422ac5e43aa8b0884558be8790d61108ab56d0321ac2210021fe1570d93320143e42ae1b26640b8bc8755164cc8ed17f0eb26859900a1fa1f75583320043f438eab0664058bc87551648c8050fd0bb82c9190021f61770592323545f43880b246400ab581101648c8eb17f0eb2687190030f5d754d91320054ec1ea9b226400aad82d53644c80517f0eaa6c8990021fe1570d91320143e42ae1b226400ab681103644c80156b02206c899002ada0665d91320055ac0ccbb226400ab781597644c80156902b2ec899002aee016
  | 18 => 0x3800e00001e05800200201c00e00c00003001200801002000003200000201000200000001600400400a00401001601e00200400001800200200a00a00600c00001c00200000200600000c00c00001e00a00400200000200200200000600001000200002a00e00600000200000200400200200004a02600000400601e00000000e00a02000206400400401200000c00401000a01200e00000000e00000401200405200a01000c00400c00800201e00a03000200000001a00600000400000c02601000000800000000400200000000000000a00200200200e00400e01402c01c00000000602600800002405e00600000000005600003001801200600200000400400e00400005a02e00603401400c00400001600000405600001400200000400401807201800200000000000a00800000200201200400800400000600200c00001c00401e00802400001a00000201c06200400204402400200200200000a00000401600a00200001400600800200000000007202001000a00600800001200e00200a00000000400201000001c00000600200200601603a00000001602c00200a00000400408c01600203200000601000200200800000400201000004200000000400200201600000000400400000603201803c00202800202a00a00200e00400000c00e00000000004600801800001000200002800000200000001200000000e05400200000000c00000200c01800400200e00002c00001200e00600002e00200c00800200000200001201600a03a03200001201a00e01c02001e00400803a00201800401402803800002800601400003e00006000600002203000400000200600001202201e00200801600200000000000201201a01001c00400a07600c00004a01401600c00c00200600a00600a00200400000000600400600200200200000601a00600600000000202200600000801200800200803800600400a00e00000e00800200000000400200200800000200400601000401c0100000060020040b800400000600000400400000400400807801c00801600a01c00c0287e85dc162d0c010fb0bb82c5a180e3da0772583430047ac0ee4b06860b8ec875496290c050fd0fbaac1218030fdd375582430043f438eab048600c3f741d56090c7917d0f2a2c12180b0f1d654582430161e3aaa8b04863c8be87d0d6090c7957501a1ac12181a2f2197090d431e65c302e121a860087f855c36250c050f90ab86c4a19db0fd91751894300477c3ac43128600ae4815886250c011ef0eb08c2a1802b920961185430047bc0ae5b0286038f4815cb6050c018f2eba86c0a181a8fa1372594431c51ec26e4b288600c6f729c96510d2547f08b92ca2181a8f21172594430053bc0ae4b288600a74815c96510c0d47d0938aca21a1a8f61271594430351f420e2b
  | 19 => 0x294131c21e00000023681201cd00023d002c97a37c0780eb655300006488227f241b14c47fa0000000b1400053c2a282604ec738200857800005f1f58000f2e3670ad826800010400000012643474230a8002e0ff365a6f470c0002218ff031c1f800021dc3942840159d843dc95f19e9b8000041200025a44cc0004bc8fc89226c300000000000004c626b077205905ca4ac0006ba3f4800000000000013280000000001dc00004cd000000084a0002cfa3d5132000000038c41a4783ed0b3c6a64b338880b4b8e0000689410400000000000000005d242001932600019d87600780000000000f300004af153128e83d356089921826212fa754d220001d7a59c5a20003c58000a320004d100000000000f524bc000000058105c6420003a8084000089035b99b8c120e64118dec00000044d11786e057c45a80000003ef0001acc9284b51d700bcb4c8df00009484b21e14918d0d24a06d4511284f4a50c00a1c38b683230e193c41ca00027d00003c898d38101e400000000025b80000ca0659f990d21c8000000012e03a06a9d701a09e44dd80000003031b2269ca8c00013c84d925007024b000008218b0000c013861b7367115400085e08096fc6bc00000611cc6c25682cd0540bde39d0dd8a28e1040d09a25f49b68d3095a6e8bc230d29095d023856b39c8d00c2284915116c01b27b52e08eb11da4eb00002d104a1e52d6180000200002000600000601201200a00002600000200800200000a00400600001e00200200400c00000600000e07601000207200200c00400000400000200000a00400000200200400201c00800000c00e03800200200002001a00200000800000000000200403c00401a00600204a02a01200001a00000804e00000400400001600201200401000000e00c00000000400800a00200200400600000200200a00000601400000400601000e01e00000201000000c01a00005402a01600000000001400003401800601000200000c01800000401000000001a00000600400000e00200c00000000600000600400400a02601000400000405c00e01600601600200601000001000601400200006400000c01205401200401601400c01201200c00800600000401200000801400a01400000000000a00202602200001200200c00800200600400800002e00c00000002000800200000406200602a00800800400000200800000200602601400402200602a00201000401000001400600200000000600201401400000200600c00a00a00a00001602401000000401002401000c0020100000000000040000020000080020060060000000000140000080000b200400000601200000601204000009600601000000001e0040060040080060160c201a01600200a00e01000208c04a01201200000000402c002014002032008
  | 20 => 0xca3c0001db00000000003a2142429800047406b000081929a2010b6a4f219319cc26e1ed295190c8109571020000d5c6810bd8e445186a6136987c08667825c1614e9844f21d27445588e92829fb826a33c054196d1885b64de12d11d81712e22490b9a0684b6193424a82609c05e465224f467a2b007a2b52551068106670487998c88e00000006d807678c4ec092cad8275383168c0002150de169c0144f3000079c35431f371a13074021c31414b5116163239008000087f0d48c500007bb00000000002de0000000cfc00025691287129650000000eaa00021c0000a00000417800000031a4ee18dc7ea00020c899400068800000000002a600007e40000000000000de200000000000005a2489a4580000232c80a5429e93800000000000283eb1fc000000000000002c216200009b883e3dc0000194a529e349f0718f065c31912350b508714710de131609916711e88d81952249b013407b84a880012440004160b3003c1db2928100c9c33a3ff165033a23f4432768bf287626f99481906b44980978e408bc130800096c0a500580000009c44ed80007682443b2000016c0a01078000e6a77144d8bd429673d14f9010bc64d627c0ba83347ff01989284ae57123e0610eda6d612893242ae00049300000000004718000dce000468158c7628b623327300000130001cf083c00046b09c92286c60001d2012a8404470c40d640000000f28360296216910926e1ce25ea4709185d140921883a07232bd009c0004d80b504c862600000000000000004808ca91084ac4a900006102e800001cd0160c2483265d2e68f62741024b5a225101000078a00018c1d0c0000001509194f0488033080010fc4764b6801cb2e9c70a9000cfa47214538af10908d734780000002dc000000061e63c4e2977422814017994cc00056d0000e082f05233330000df44ec000000089801b0000000ee60002730e340005ea2388000d303360a08000c4c30933a800000052744996ac1e62d20fd0bacbfc50b2fa9a752c82ad2d2890c6928ef05e815008a000372075cf0216608c0001030726381831066212608b80002580f41f8a748ff80001f817200007283cd9b7000075d22d1fbc93679a09480004401c524b81806829d901b81f90fa9cf2ba80005886f2349104caf60000000ac84b000006715c10c6620000000000000000008e400049539f8000a642df42580010c269700013f40000d81f38bdd05a000312800000000000020fc93a48d42a8acc3406214b802dcbe49710000d1400000000008640420004ea000000057303e101476a00000e000045263a36688252969353c503d8a220291ca87a0d340000001b5ca0e61538f000051c1e300009c400012a3c88bb40004902280000f200000860bc41f888a1760bd813a9210c41b10ac89c02af972c754514
  | 21 => 0xe40380002d81090000000d8e6170000001222867000056800089d4520da0c1a00049c9ec80008b72c390510e490a19817645f47131c800d0c082981438000f406bd2c9000094e7b013e115013c51a0000a2000000048f92151fa70a00000000005e23b180000000a62f2000106001f0001e38e4a0000f980010f831c211000000000000000000003d400007f40007091e607882ee3830439218ecc7db000026c1160000000af42b05c6000000000042f1019b847c436d3e7144cf560114408d4800093a3961ed0b8a0000aa98d019a4ab30c000046282918b800012448200015fcc5e63634e000000000015a0c30c202d00001680f7a5353e58d090667c5000200443e28d0cf16dc00079d10a1b040000933510d209e813a1780c2800046103e800049a0000001d803e01f51eca6d447699a0001270b2a0000001e980000e214d000049280d2f6000000091d0000000e741a536f999c0001c216b80009bc00000000006e83562818000e0029c3c4a6007860004d41d4c00000027182f071e35d26326c434629332f21acea46841d19a340003c900000006660000002018a4c41b09206c411e48e00000000008f81d9922c9aa3ee2aa06d0e600121a209087c02e1000000134880e32780008dc8fb3b38000fc80000000000946000376264400012f000107400000042e00000004fc2e116c414492d2b325f0000064000241485c0b82620000a4895a427a44034479403d1c1cf4e40200026c0c820002c699fc0005f130919b0000000000191c0004a22c59f8c56c8b228b09051c831d27f8e4ccf66054e127784c083b22c07542460002ab0dbc5f800000000012cc8eb32a0c480002f404000005280000002000c1090400021c035a1100000d88cbe30b0000000000000000000000000048c0e5852037e0001870e086ea0000000b4258345524f486a06b1b50624dda33f21993040004831200f4894a2b00002070000000261800106e17611a205871c2cb4bb1534c444b02fb95a8e180002c1000000078000018ac1f064014d800000000007811342942690601dd4fba8031b280000005693b2a434df864816d26501da62e26d0618000000000000000060300000005043e30d715751d422b3c78f6c4a00000000000c7c00000000011fc91543ca55917c000000000000019035d80000000fb000000000091232613e499c00037a1910cee000000000000000021901390e647f0f621940009722520f7cc2c866455a61484c0ec2fc1aa00006820000000eae0000000ffc0007ac1401ea8cde00000016e89b825c0000f9087812800025547ca08d12b06600009b913a11048a60000b29838dcc6c82a38ec0ca632c2a20e10d543390001af03fe1e63df813009a074077209d18a9cb1f409c099e2b742c8e1c9024480661994cfa42c3f520304500cf00099a
  | 22 => 0x9017c7af23015001b889400025d400041521802fd3028a9024a11409408903119903ac3fe13209742322c744e04206640004601a1432800d4b5800000021232598e0c020772a809f4a1c24c2f71660d422e53858e306b000008300000005301ea8bfc80e00045c989135c29d1bf8001392000290119000099815f8000fa83c44659aac00001a29d25652a647d0001f240005de1dd21743b896f0bea6b40007dc36d9a180000004f308b4a1a8150548158be00e026e9f352066940000000ca29332a125e0e020002eda2b4d943692fb227d09453f490179c9007143a58d688f29ce2379b2414e00039103f50a09a52a70a90d729dd27119a511e33700000009a87de48413306fa51f23a1e70ff05912c48fe50b06a9165187893c1cc0fe1da425a56017905103643554e31edc49c22a1c00001354944088843481e6d00e88000f527ae1b618cd18e8282bb908463243102b80000008b83a11e208ba000177246459a2f93e118a89ee1ab1459eb4bb4676284131400000012d00004348f1116000027c0520741c7d3c07ca22c86f850c59c23f26489ec0ba44b23dc1229430bf94053907a213d9584bac69e1f68000a384fb06280012ee0002c608f80002451e99b6045e3bc1c5232020418c2d99d1ca3042733413c000091a07516e52000d74ce92f118c4ed00013086a01c12499f6514c5cc43785a0d168022fe188cfea88c3689a250f49bf45887d829a0323aca1692e819c42184f135277241003a4b142e404a00000007e7000000004860f37f0000e9e889000000000000000020c49721e90001f88000000000000000066d00025307ec8f93bba1444180750000000d1c000061876514a3253c980003fc1af19f0000c3600033e0fe885645700c00000009a600019c84d47a31170cd521c00011d1c6cf8239a00020440003cb0002248d0055c39b915882c9e10001fe40000000000538000048029a148da87d74e0a25c5906740be01112820002e9a28113c0004d99a7d3a02a50a31ac42be0630b200002725ce06f13200003f43cc840d09a3e63e880001fc38500c800062c67a4db0000b0c8e02cca1b8000000405266400000000000003880000001fac00075828825fc5c0306000000006c00012a80011dc71636d000000040c0000000000982000213839200032b00008a20001190000e2e00001f0000a0c8532ec1248f3e0003301cb420a740000258022a94a29720f924e00000000007f00003be80010880004971df131c00021d9c600008cc42120200001b334809fc3420554238af8bd20003938000fee3da1f6000000000000010400000004540000ba000000014bc00000031d80000ec00000017ec00000000005140003460000000afc00036c800000000000016751fe00000007c4000000147874c0000000000000bf453b4a700001ee29
  | 23 => 0x1b01d181f218006903902e081001322c07ae4e52e788d8fbe9a12b726282405e61d3950c00040b03894f4bc01d42cf035832e2a810c0f2047023c0f5a42c21668a303088c57261a3b602080003630c68020f660c645a2088ebc11b17d8d30ab001549fa1a8f0863d0001b9520400039d8fcc5061832de800060274a415000000005e000000036a00000000007304bf3b10b6c5329461d109dd0123f7042800004a64600000004e68dd3e38000e820002a920680004ba4b523c81426f038e2284dee5bb4cf85f90428e50408e952b80390001384ba45bc1d326c86e40004191b4c5a6000133a3f13942e2018000072e8ce000000000000000000000008680000000efc000395800028e000057061405454a01c0a9cc5a7c60ef189c00005b29600000b842334992dcf2400000000000000000001fec00003f0001a1c000895000000062a2c300000003ba2d64d1811d1840f10ef9f8000000003c00010f000007098fc0007c33ca8db8f0a3ad30c800000000000000001a87f3000175000043600000000004d1131889000000000003d40002c900000005540000000000c162110b680001be0001de95e400000003500007bc7f11b3000088a403000277cb364400ba8f8527828106480008403990000ea4000000000175c0009d600000c40de74e0fa1170000088451800000063009e95c81f42c23061f612845aa39a09b0ade4c022f8e0444e776023159c90e46736e94ac5c63040839a5928a8832271390a828f02c9a2f42a89582cb22ec7d480f47319e53101fb37702ccb002a312402c452442a32121ec4029870000000c2891b2d90fa4baa6f500100009764a800004b82ce40625300006685760cb0ae111a99c004a20843694909100002009d70608dd405858e32e24d129a0664948ae8f721740308e90f9e58f0aca4782e62ef3a69f546b81a84bf1f0091215d000184c6965dc4dc0b6423c18728a9cc800000026c93401d67a135c1c3c0008ae1609700a70787000103800000000000000000004b1000078e0000551bec64e4d32e488140003ab000233400000005900000000002a41914d5a874000000000036b0002328a7c30732b82281ce71a00024a800a0000c9a244d4a000000226031400027023044f04684739bfce920000f7891800052225f1a8118600038298d533c75605a82100001f22ad06fc15a0dd0001ef107800043609a000064a0ae05a4d840001bb047d39a35731499752c27d00000000d1813b16a1564f9016e4f2935c95c5f41cf1da03a43bb43a9ca877c31e2b102305767121a715e08c497b2aba074d4811a1af882d0687fa38a873c0b400000008740845554c321508d258420000008da0003740000622000000000027e0000001e340007101db9cb87a0000000000136e39f196a57515e53642f9ec4e323ce16e90
  | 24 => 0x7d300000000000002a49d7c0d2000000094cd32000281139cdbc15342b800010c00030e9b3cc6430524d1de07ba5e83d420e8dde9b40ab066c42c34d0698efc52e99048491d434c0960a10c38ed66cc1a520d434e662000000079e00026906440000004cb1abc0000002140000000131157a180000000000049c00045b00000001de17a00000002c00000000b98e8a11310718c51aa00047080000446713cf266cca00002a5800103649828911c00004af41c827c9624a902897ad28000021b8f3438e1300cf9afc0003710cc9dd0cb07290ed081c00088700020e126c72f0d21e59276172392241c580237303932c86850f3050ca0b486b51eb0bf8f880041110a1400048a0000f041585f339b18e47642891e893bc88855b3989ac0ea207f0638c80e666493f62378b529e21559fd0d4e6830a88bf4fca10a46d88291a42ae10f0700fda35b3690e6cdec5fd1fd803cdf28172c0a6ac77000021ca0b8b100000000e206ee0a41b9a5510ac6e92231b548d425b00022cc64827e301000126200034a800000066a000000137c9630000000a3a88546c836c0000000c108cc8526b62f682700000000c7800000000006d000047a7e816306043964e9195953cb9485b0a416b92b631b39f209096499502580400e465a02c0074abc81e23d9d6811c00000000389fc7cc16a891c7b08882291a6c0000a34029af8dfa0000000ba4000000000052400000028b8000156000000000000000024f93b82660000dd000122e000415a60c8c66e20b78b9c05c41c0000aa52a094f20504841e43c62df14e471696821f8f0000014328da2e80007e1000000000000011a80004de00000000008305653fb00d51b092c3fe82ed02865517c000023a1163df1dbc00076a1a78e70f0c20600000000a071d00025206f83593b701ec8ee39423598b04265e53bd16bd1a24f50de882135e57d000177c0004ea0000d450823a8432000060498f24c895102643d29ba07d1e68bf2dc01b8aa2000158912c940659464942800006710b8d510da112375a624bfe6c54e9843891006c1c908840009843bca3704d63c200000003ee3380000cbcefe2d83dd00003700003bd9d506f427a1488de4f6c6a30001c3487c6f302780002d68fa3d202bc7421b919708c091e0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x516d804a0704a3800e00022c01aba401018003401e000c0098c032880a80e822986c20002c20020000058324d5454c62504ab2a691e1643189410048be558090c625040122f9761443189410048b65d8510c625040182d8755050189410068355183140625040182c6261473509410060b18985dc1425040103d98994744cb310060b1c9851cd640840182c7261770590213a60b20975590430840105f985cc73597400050be61651c941d000142d98594725074000709e45651c941d0001c249159472507403a60b209655d021d000105c984c17518d400052324d651c9415000142d9518c725054000487e615314c644c0015259510c725071000549657401c941c400103d98194744c91000568642541c941440015259510c725051000568640431c9414400152595d007250510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x94e
  | 5 => 0x3
  | 6 => 0x5
  | 7 => 0x138e
  | 8 => 0x98e
  | 9 => 0x150e
  | 10 => 0x9ce
  | 11 => 0x4
  | 12 => 0x168e
  | 13 => 0xa0e
  | 14 => 0x180e
  | 15 => 0x209
  | 16 => 0x20e
  | 17 => 0xb09
  | 18 => 0xb0e
  | 19 => 0x1409
  | 20 => 0x140e
  | 21 => 0x1549
  | 22 => 0x154e
  | 23 => 0x249
  | 24 => 0x24e
  | 25 => 0x16ce
  | 26 => 0xb49
  | 27 => 0xb4e
  | 28 => 0x1449
  | 29 => 0x144e
  | 30 => 0x16c9
  | 31 => 0x289
  | 32 => 0x28e
  | 33 => 0xb89
  | 34 => 0xb8e
  | 35 => 0x1489
  | 36 => 0x148e
  | 37 => 0x1849
  | 38 => 0x184e
  | 39 => 0x3c9
  | 40 => 0x3ce
  | 41 => 0x170e
  | 42 => 0xcc9
  | 43 => 0xcce
  | 44 => 0x15c9
  | 45 => 0x15ce
  | 46 => 0x1709
  | 47 => 0x409
  | 48 => 0x40e
  | 49 => 0xd09
  | 50 => 0xd0e
  | 51 => 0x1609
  | 52 => 0x160e
  | 53 => 0x1889
  | 54 => 0x188e
  | 55 => 0x589
  | 56 => 0x58e
  | 57 => 0x178e
  | 58 => 0xe89
  | 59 => 0xe8e
  | 60 => 0x1789
  | 61 => 0x18c9
  | 62 => 0x18ce
  | 63 => 0x94b
  | 64 => 0x98956
  | 65 => 0x20956
  | 66 => 0x94216
  | 67 => 0x154956
  | 68 => 0x95556
  | 69 => 0xb4956
  | 70 => 0x94b56
  | 71 => 0x144956
  | 72 => 0x95456
  | 73 => 0xb8956
  | 74 => 0x94b96
  | 75 => 0x148956
  | 76 => 0x95496
  | 77 => 0x14c9
  | 78 => 0x134a
  | 79 => 0x2c9
  | 80 => 0x138b
  | 81 => 0x139556
  | 82 => 0x138b56
  | 83 => 0xb9396
  | 84 => 0x138b96
  | 85 => 0x40a
  | 86 => 0x160a
  | 87 => 0x188a
  | 88 => 0x98cd6
  | 89 => 0x995d6
  | 90 => 0xa0b
  | 91 => 0x150cd6
  | 92 => 0xd49
  | 93 => 0x1689d6
  | 94 => 0x17c9
  | 95 => 0x5c9
  | 96 => 0xb8a16
  | 97 => 0xa0b96
  | 98 => 0x184a16
  | 99 => 0xa1856
  | 100 => 0x40a16
  | 101 => 0xa0416
  | 102 => 0x160a16
  | 103 => 0xa1616
  | 104 => 0xa0e96
  | 105 => 0xa18d6
  | 106 => 0x180b
  | 107 => 0x140d
  | 108 => 0xb9816
  | 109 => 0x180b96
  | 110 => 0x161816
  | 111 => 0x181616
  | 112 => 0x180e96
  | 113 => 0x1049
  | 114 => 0x16cb
  | 115 => 0x16c216
  | 116 => 0x20d
  | 117 => 0x58b
  | 118 => 0x178b
  | 119 => 0x24b
  | 120 => 0x28b
  | 121 => 0x148b
  | 122 => 0x41416
  | 123 => 0x16d556
  | 124 => 0xb4256
  | 125 => 0xcd6d6
  | 126 => 0xb5716
  | 127 => 0xb4cd6
  | 128 => 0x16d456
  | 129 => 0xeca
  | 130 => 0x160296
  | 131 => 0xb8d16
  | 132 => 0xb9896
  | 133 => 0xb9796
  | 134 => 0x58b96
  | 135 => 0xb8596
  | 136 => 0x178b96
  | 137 => 0x41496
  | 138 => 0x161496
  | 139 => 0x184d16
  | 140 => 0x179856
  | 141 => 0x185796
  | 142 => 0xcc3d6
  | 143 => 0x1715d6
  | 144 => 0x178416
  | 145 => 0x41796
  | 146 => 0x59616
  | 147 => 0x160596
  | 148 => 0x179616
  | 149 => 0x161796
  | 150 => 0xe8591
  | 151 => 0xe8596
  | 152 => 0x58e96
  | 153 => 0x178e96
  | 154 => 0x18d796
  | 155 => 0x1798d6
  | 156 => 0x14a
  | 157 => 0x104b
  | 158 => 0x194b
  | 159 => 0x59451
  | 160 => 0x58cd1
  | 161 => 0x585d1
  | 162 => 0x5c591
  | 163 => 0x5d791
  | 164 => 0x597d1
  | 165 => 0x59a51
  | 166 => 0x17d791
  | 167 => 0x5d8d1
  | 168 => 0x59791
  | 169 => 0x104b91
  | 170 => 0x216d6
  | 171 => 0x21856
  | 172 => 0x21896
  | 173 => 0x16ccd6
  | 174 => 0x592d6
  | 175 => 0x59316
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2583
  | 6 => 6778
  | 5 => 2535
  | 4 => 30
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
  | 7 => packedAt gbK7 (105903+((h/861+packedAt gbK7 (95571+(h % 861)*12) 12) % 3410)*13) 13
  | 6 => packedAt gbK6 (356970+((h/2259+packedAt gbK6 (325344+(h % 2259)*14) 14) % 8947)*14) 14
  | 5 => packedAt gbK5 (159705+((h/845+packedAt gbK5 (149565+(h % 845)*12) 12) % 3347)*13) 13
  | 4 => packedAt gbK4 (2160+((h/10+packedAt gbK4 (2100+(h % 10)*6) 6) % 44)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff83e07c0ffc0ff87ffff80013e89f88e73fc
  | 1 => 0xf00fc007ff07ff07f87807ffc6d97660f38ccf
  | 2 => 0xffff80007ffffff8007fff8e1878703ff0f
  | 3 => 0xffffffff80007fffff8003f01f807fc0ff0
  | 4 => 0xffffffffffff8000000003ffe0007fff000
  | 5 => 0xfff0000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x50e80a014849c84980c93481800a00a886315c
  | 1 => 0x61294002d94259428850552a82583260b284c5
  | 2 => 0x24296c80004a2955500a25518a18583015b0a
  | 3 => 0x404e554a29000066626c0062d01d805580ea0
  | 4 => 0x488f39a73ce73ce00043041837fe0006efe000
  | 5 => 0x8f0001c030803080440400603ff5ef50000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37107
namespace PEqualNP.Outside.L_meta_37107
open PEqualNP.Outside.L_meta_37107.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_160 : Interval s0Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
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
theorem bs4_4_0 : Interval s4Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 2 := bs4_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 30 := bgb_4_0
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
theorem bgb_5_2528 : Interval gbAtlas 5 2528 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2535 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)))))))
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
theorem bgb_6_6752 : Interval gbAtlas 6 6752 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6778 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)))))) (concat (concat (concat (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))) (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))))) (concat (concat (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 bgb_6_2912)))) (concat (concat (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136))) (concat (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360))))))) (concat (concat (concat (concat (concat (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776)))) (concat (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 bgb_6_4192))))) (concat (concat (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 bgb_6_4608)))) (concat (concat (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)) (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 bgb_6_4832))) (concat (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928)) (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 bgb_6_5056)))))) (concat (concat (concat (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))) (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat (concat bgb_6_5376 bgb_6_5408) (concat bgb_6_5440 bgb_6_5472)))) (concat (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664))) (concat (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760)) (concat (concat bgb_6_5792 bgb_6_5824) (concat bgb_6_5856 bgb_6_5888))))) (concat (concat (concat (concat bgb_6_5920 (concat bgb_6_5952 bgb_6_5984)) (concat bgb_6_6016 (concat bgb_6_6048 bgb_6_6080))) (concat (concat bgb_6_6112 (concat bgb_6_6144 bgb_6_6176)) (concat (concat bgb_6_6208 bgb_6_6240) (concat bgb_6_6272 bgb_6_6304)))) (concat (concat (concat bgb_6_6336 (concat bgb_6_6368 bgb_6_6400)) (concat (concat bgb_6_6432 bgb_6_6464) (concat bgb_6_6496 bgb_6_6528))) (concat (concat bgb_6_6560 (concat bgb_6_6592 bgb_6_6624)) (concat (concat bgb_6_6656 bgb_6_6688) (concat bgb_6_6720 bgb_6_6752))))))))
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
theorem bgb_7_2560 : Interval gbAtlas 7 2560 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2583 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248)))))) (concat (concat (concat (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568)))) (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 (concat bgb_7_1696 bgb_7_1728))) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888))))) (concat (concat (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 (concat bgb_7_2016 bgb_7_2048))) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))) (concat (concat (concat bgb_7_2240 bgb_7_2272) (concat bgb_7_2304 (concat bgb_7_2336 bgb_7_2368))) (concat (concat bgb_7_2400 (concat bgb_7_2432 bgb_7_2464)) (concat bgb_7_2496 (concat bgb_7_2528 bgb_7_2560)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0feeaeeeafee0eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37107.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,4]⟩,⟨.and,[3,6]⟩,⟨.or,[1,7]⟩,⟨.and,[2,4]⟩,⟨.and,[1,3]⟩,⟨.and,[2,8]⟩,⟨.or,[0,10]⟩,⟨.or,[7,9]⟩,⟨.or,[5,13]⟩,⟨.and,[12,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37107

open PEqualNP.Outside.L_meta_37107 in
theorem PEqualNP.Outside.L_meta_37107 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
