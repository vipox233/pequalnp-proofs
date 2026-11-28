import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36699.Model
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


end PEqualNP.Outside.L_meta_36699.Model

namespace PEqualNP.Outside.L_meta_36699
open PEqualNP.Outside.L_meta_36699.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 49]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_36699

namespace PEqualNP.Outside.L_meta_36699
open PEqualNP.Outside.L_meta_36699.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x600039c2a5b800006e401fa2202b7aa640404c270854b276d0291ec2030549b461a80c58800e080041040210223ff42fe42fd42fc42ff41fe41fd41fc41fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841ff41083fc82107f50420fe20841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887d88710fe90e21f521c43f843887fd0310ff20621fd40c43f881887fcc310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7087fd0e10ff21c21fd43843f887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21f741843fc83087f50610fe20c21f441843fe63087dcc610ff18c21fd31843f863087d0c610ff90c21f721843fc43087f48610fe10c21f421842fca1087fd0210ff20421fd40843f881087fcc210ff18421ff20843fc41087f48210fe10421ff10843ee21087ec4210ffaa2217f544437ea8884fd5110ff2a2217e54443faa8885f55110fe2a2217c5444378a8884f15110ffa9a217f53443bea68857d4d10ff29a217e53443faa6885f54d10fe29a217c53443b8a6885714d10ffa1a21fe43443fa86887f10d10ffa92217f52443dea4885bd4910ff292217e52443faa4885f54910fe292217c52443d8a4885b14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff98a21fe31443fa62887f0c510ff90a21fe21443ec42887f48510fa90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fe98221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087dd0410ff20821fd41043f882087d10410ff98821f731043fc62087f4c410fe18821f431043fe42087dc8410ff10821fd21043f842087d08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a07f50b40dea1681fc42d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff18e81fd31d03f863a07fc8740ff10e81fd21d03f843a05f55240ffa9481fe52902fca5207f54a40bea9481fc52903fe85207f90a40df21481fd42903f885206f10a40ffa8c81fe51902fca3207f54640bea8c81fc51903fe83207f90640df20c81fd41903f883206f10640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4940bfa9281ef52502dea4a07f94940fea9281fc52502f8a4a07b14940b629281ff425037e84a07f90940fea1281bd42503f884a07fd4540bfa8a81f751502eea2a07f94540fea8a81fc51502f8a2a07d14540ba28a81ff41503fc82a07f50540fe20a81fe31503fa62a07f0c540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff52103fca4205f94840fea90817d52103f8a4207fd0840ff21081be42103fa84207f10840de21081ff51103fca2205f94440fea88817d51103f8a2207fd0440ff20881be41103fa82207f10440de20881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa1641fe42c83fa85907f10b20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fc63907f4c720fe18e41ff21c83fc43907f48720fe10e41ff40c83fc81907f50320fe20641ff54882fea9107f95220bf2a441fd54882faa9107f15220be2a4417d52883fe85107bd0a20ff21441fd42883f885107b10a20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fc63107f4c620fe18c41ff21883fc43107b88620fe90c41fc21883d843105f94220ffa0441fe40883fa81107f10220ff90441ef20883f641107fd5120bfaa241bf544827ea8907f95120bf2a241fd54482faa8907f15120be2a241bc5448278a8907fd0920ff21241fd42483f884907fd4520bfa8a41f751482eea2907f94520fea8a41fc51482f8a2907d14520ba28a41ff41483fc82907f50520fe20a41fe31483fa62907f0c520ff90a41fe21483fa42907f08520ffa0241fe40483fa80907f10120ff90241fb20483fc40907b88120ffaa0417f54083fca8105f95020df2a0413e54083faa8105f55020deaa0413d54083f8a8105f15020bf29041ff42083de84107f90820fea1041fc42083d884107fd4420ff288417e51083eca2105d94420fea88417d51083eaa2105d54420fe28
  | 2 => 0x7fa8220ef50441faa0883b541107fea020ff94041bf28083fd50106faa020ff14041ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7be8718ff90e31fea1c63fc438c7b88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe214637e518c7fe8318ff90631fea0c63fc418c7fe6318fdcc631ffa8463fe508c6fca118ff54231bea8463fc508c7fea898dfd5131dfaa2633f544c7fca898df95131feaa2637d544c7f8a898df15131de2a2633c544c7fea498dfd4931ff29263fd524c7f8a498df14931ffa1263fe424c7fa8498ff10931ffa0a63fe414c7fa8298ff10531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c6fca218ffd0431fba0863fe410c7fa8218ff10431fa20863fe310c7ec6218ff4c431fa98863d5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa6437f54c87fca990df95321df2a6433e54c87faa990df55321deaa6433d54c87f8a990df15321ffa9e437f53c87fca790df94f21ef29e435e53c87faa790df54f21eea9e435d53c87f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ff8cb21ffa0e43fe41c87fa8390ff10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710ff94e21bf29c43fd53886faa710ff14e21be29c43ff43887fc8710ff50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510ff8ca21bf28c43ff41887ee8310ff90621fea0c43fc41887e88310ffcc621fb98c43fe31887fa6310ff0c621fa18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243ff41487ee8290ff90521fea0a43fc41487e88290ffcc521fb98a43fe31487fa6290ff0c521fa18a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ff55021beaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087fa8410ff10821ff99043fe32087fa6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843f
  | 3 => 0x401c00000000801800000c00001401000c00000c00400000000400000401800000800000800000002000c00000000000000800000402800800800401001400000805400002000c00800000005800000400800401c00c02c00000000800000800c00000c03c00401c00000401802803400401c00000800000000000402000c00001400c00000000001c00400000801c02400801401000000400002c00000800400001400400001400400000002002801c01c01001800802800002001400804c00000000403000000000c00000001000000402c00400000400001c00000000405400000c00400800401400000800401c00001c00001002800c02000400000800800000000000000400000800800800000803001c00001800801c00000400000400400005402000c01c00000000802800800801000400400801000801400000c00404c00003000801400000400c00801400000805401400400000c00000c01000c00000c00000000800000800800000003400c00c00400400800400001c00004000800000c024037fea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190beca3215d94642fea8c857d5190beaa3215d54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41df21c83ff52907fca520df94a41fea94837d52907f8a520ffd0a41dfa1483fe42907fa8520ef50a41fe214837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4d41bfa9a83df53506bea6a0ff94d41fea9a83fc53506f8a6a0f714d41ae29a83ff43507fc86a0ff50d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41ff21883be43107fa8620ff10c41de21883ff52107fca420df94841fea90837d52107f8a420ffd0841dfa1083fe42107fa8420ef50841fe210837e51107fe8220efd0441ff20883f6411
  | 4 => 0x670924be0000000988000000838000000000481689e81228000c143000000012f1b8990a1980014780014ad3aa218b2e071a9224d1f9bbc001fd80012415b4a800004912700000002f8001db000190e1a0998c50aa5c80b980000000020746d0000002068001910000000000339dc89940005f8000000b180004c97f5f603580000000004a80021f0b140001ca06c2e8ad8001e600021b0cd8000000c4c000000070001790000b20000000000000ca8000b88000000000c951780880004d1b480000009095c0cc85aa160654001191155644000ad515d5742f00000b0001b00c35f192445652580001b8000b49f512200000000012159c02a4000000001ef800000122c724000964000b61db9118000000000000000001390000cd0af8abd0b92a04ede38468001a2c690001630000001935498b240000020d8200000001d1400000075d1d00000022250e8948000000001bf80000012047297140000008b80004f09c12c94885104e57f9348cb0408000000b089740000007ac6814a00000000000014e9f2c0000000019240000003448350e0000000001a3c31000003c000000000000f60000b51ce8438001128a3063000000149153d3d80021580010dc0000019797e95f063c0000e54f0001ad0c74029b2549c168000000000000001d255080000000000016ca148509e305907b43c00000000005c89bd6f0eb4000000000000000f80000000000000000000000a10002180d38000000030c1d0d9ff8000000000000119480000000001728000001889ce00005805980000000016f8001268bc8001840001d116b80000613f8000e9c000aac000b680000000002d83f00005861912900000000000011005880002a8e60211560001960000000000c90000720dbca702c00000000000000005e800000000136000401400400401001800000003800400002000400c00001000400003401800002001000004800c00000000804000800400400400c00001c00000000800400401800000800800000001000400400c00000400002000001800000400000400000004800800800c00000001400c02400000400400400800804c00001800001001800001401400000402403c00c00000000000004800000400000c00000c01c04000000000802401000803800800000001400000400002000002801400000004000400400400406400402800401000000000c00001800400000400000c00401400400800000800c02400400000400000c00003c00000000400401000403000000c01401000000c01000000000400401001000800400400001405001004000000c01c01800c00001401001c00001400400000400400000000800000001400000000001000400400000401800007008000001800c00401c00000400001c00400400000401401c02400000c00401
  | 5 => 0x15992b12c03b0000000000000ab1b7400000000000211800060c000001f0041194db08f09b3800146a0400020b064c000b30000001df800138c0002880000021e17cc000001138c8c000000ff4000985f58020f8e0648820c00020380000000017e4000000d44000001dc4b0400000113de50001ca8001ba1cf09c8000280240b413ca05de580009e080d4105ec001a60c48380000000604000002000001d6905a1209e80a1551a5000082056163c001849420000000000001e0db6501c000000520180000ad00000000000020906e1face6d004000000a08000e209680000000a90800005500001d9a319f056943e142221e090b0e1876027e0561e80005b1c317d482571016c00000115800207a249535e719b1ab0b821955b11107e083142800030c001d2855940df280020109a97000000000000000019e8001f380018614d85b8001851d0c000fc45f40750700003c80000001ccc645e00011c8000000000000d7c0009b991c6f41ac0000000008f000000151400000089800000020c000bf21bc8e1c295c8248000000000001318bd0aed52c6a8000000fa80000021c46ecd60c180019a0980ffcfecda0000000c54000000000000548000000a90000fd4001761311351e200000000000018a8000eacaa8d8c0009acd90259608001e28000000000adc084000000c0c8e8001378000000000000990001b780000540d0c8891c0012f8000001878000d10e88841e8a1a80012e8090001fc8001d098320182600006b81b0001326210000001a082300022080000c151ddc0e10000958000000ec4bc13000000008a5c100d80001a00006381200000019905780000021b9c00000001a15a206c800000007c0002214400009c4000c80000001db40000000007800c8954000002168000001d2098dd980000001f09d0000391dcc000cb8128001068ca0ef51e8000000001de9a1c3ec1500000000002d09f01bc000ff8000001a40000c00cc000000093c000000001448000001938000000b583a5a580020306f0000679ba9ea1f9c0000000011e1bd8c60d9978c0000000000000000000013e801848428dfb46092180b9329998001a680004dc15c0000011dc6ea0280000007d8001780fc0ae95d8000001568009940001890175590d78000659dbc5740000000000016240020fc000501c402840000009d90781900003d800000000161800000051800000000000000000000111d7b80000000111511d80000006a4000e49a48540be96857315d08900000022019d9ab8000649808bd96000009b4eaa1f80004516d5c59be9621fa40000021b4000001668f513b5280000000000001748000000a895880e8001a78d011057716e13b81652e0a7a1055aa1892258b5f69c382c879d8c9610000000001be4000000001c68000000000000001818c7d0c9
  | 6 => 0x401ac8000001b70b100008b0000ebe1c8a200006c150400013ddf070c2a1948c9c00179c00123800154c000000000430fe47c9ed0e4097c0000000010901c00014c8000001ca00010cc000000001c480380000000000021c0e69d18374ea4fd8369e4800000136c81cb7800058c00207c000a58000000ee82680000000011080011b00e0789d60001839a89458850f487e800067000186500c8a8fea08950d4d1e914b86d82acdb120c8681d03f5b60001ebc001d000000015e85a000000104000123c9007bc000001aa90fc0000000000007ddee58f805824c87192c7d5168dd11411980014c16e8b714711f000000000080000000000218494000151118800000000000000000129921c349c9ce580010e5145de17f00000004e8710fc9529720000001901cc40000006f8094001e156b0939500000d80000000001010000000001001788ed82bd944970ee0000000000001340f184e21ad4c451c294000934f41558699395800002244c24000001750000000001ecda380dd62c5d400000223c0000000007c4fdc000000bb81f8000000001089021fe96c0d08709170001cb13bcf2814d898eb8cf1c70798000001880000000930c10000688da5e180015180000000000002b4000c201d4000001cacd200000000000000015b8858000001b6c001628000000778000000000da8000aa0001c7a0a0000000399c18c78810edc0003e80000015701100000016d0001c083e5231dd8000bb21d8db58d0a48ed1f080015e00007717dc27a0e20b8000154000000e311307b9bc52d10a1eb9ee18e80000000010d4d1924a020f840012883092a80000007d0001bb8888000000d3c001d900007a8365ae83f94f8420130049ff17fd7392089505fca00a29c90000000000000000001744fb80013e037c848000000000001a188a0000d718b0495f8192806443617c0010080000420620800000019e0000001da0ecc506130000db8000001bd065ce64208000002235f90000fb4ed49a000213a19c000bfa0597a8000e38d6d028000b4622c7f8c700000011c1018dc1da80fdf70000000d9d2340010507c1d48c38000000ea00016c4001eca1144599c8dd8a98f9d3ac0009b1e789f8000000001400000d5400036d61c0014600004b0000000000000e9400096c000000530001061f40c31114ac15386e5bac000c68dac00224062a239024f00000cf85140008f9525a34000764001658000488c2c4f5385b908d9c500009a400021de40f20ab80009200014504410f0e7d8210c1d4139c53895dbb509a1a4000af0000001039e694a8499a0112c7a0ab4001c98001544620dc8000001309cc1a258d8001c61d883a000000000000008c328c297080000000017ed548b0c47050d1a9eb0000000000000000000001980000000000916170145b5c8080000
  | 7 => 0x1210000000000000000001cf83e211c000f386002e20082cc0017d9bc0000001a98001e000807747585d98f1edc09993099dfa8051e9916000000000133924c960c990f8001f11f496a5148000000000000000001ef0000238304000750000001a280000014b00000015800000017b0000000001bb00000000004f98fc790000178000c5d331cbdea87b15a03540018b9cc8001e10f11380f792b96cc0007421248d16a03fd4bdd50d30079f8810193cce80017580001c539a178eec1385f0000ae4c41371f30fa16780000d58a1ec40000000000000000000000008c13d0000d584c0b1c748000000ba8f30a6061a050001660c6c0f0eb01099f9135ac1fc11a1f79124ac8f980018700000005cc91037071e108e50d51ee835c00000004d408fd0001540001ca51cc000000000f943b4af4d880000000000007a4d4c0010a80f800000141866800000191a0f8e8017c2710d0158429388000045be131d201b683303d110c0000005d0170ec800052a1521d0148a394300018e0000000000f90001530e782993c4df9dd0e29829d71a80001988ee53755a592114ca50e08ec0d480000000000007680011fce74000001b400006d60e8000001ad9c211b9250000b3c000001ed831c069aa00000000017a0000000a19915b19b80002101278000000001d78de8c84001bcdc88ef0f597791e40019500000002b9af16bc00137c1a9368001a117982281601e0290e7164800196a1297847f00000004b800210ded5b500017c8000001bc819800064000000218dbd57419707cc000525d39ec1695f996da0f0b34219cd97e0fb00f5181579cb4d696390493a1650c59fb1a717c0878e99d595f865152056cba08281e8730000448ce18047016adf202b12604a00000000000000004d882c000340fe0718000000ae1af80013fc5700000000000007396411204783205dc251b983aa0c98c0ef9959690ff21119d02c5334140818e90b91cd06654e06a1d310146106616a99b892dd1cdf0001768000000000000e0000000135834c0016803b97d0000000a68001c1441897a2320490318100000007153b1fa143806c000b29bf1868318fce228001b20c09b3169c928d95fd1cb8918d843601891d5859fe0de00000006fc5e4b000004600020d0afcf68f893205c0379fb8f70a40001d80000d28874b380006b08c8350000fbdb10001b294a40000000019a8860d41b593c1ae13f169800038a0980000012d9718000000d760a800
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3104355530c410f5d0c31043d4430c410bd9883104377520c410dd54831043d7320c410f54c831043f2600c410bd58031043f1600c4109f59721042be64c8410af59321042de63c8410b758f21042f565c8410dd597210427565c8410bd99321043b664c8410ad99321043b564c8410bd19321042f663c8410f598f21042d663c8410f558f21042f463c8410ddd4b210437552c8410bd583210427f65884109f596210436e5288410db54a21042f66188410dd94621042fa6088410be582210427f6548410dd945210427f65084109f594210436e5208410db54821043e52108410be98021042f96008410dd59421042756508410bd99021042f46408410bd98c21042f46308410bd98821043e66208410ddd4821043e65208410dd54821043e55208410fc98021042f56008410fc580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d6194010ddd0650043744194010ddcc650043743194010ddc86500437421940109f597400427f65900109f596400433e5490010cf55240042f66190010bd58640043b441900109fd9540042df6350010b718d40042ef6250010bb18940042f76150010bd185400427f65100109f994400427d65100109f194400433e5410010cf55040042f66110010bd58440043b441100109f597300427f658c0109f596300435e538c010d754e30042f6618c010bd58630043d4318c0109fd9530042bf644c010af19130042ef624c010bb18930042f7614c010bd185300427e650c0109f594300427c650c010bd98430042f5610c010f50c4300427d65c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010f9086200427f6548010afd9120042bc6448010b7d8d20042dc6348010bdd8520042f461480109fd94200427e65080109f594200427c6508010af99020042bd6408010b798c20042dd6308010db948200436d5208010bd98420042f56108010f9084200437565c4010bd99310042f464c4010bd98f10042f463c4010bd98b10042f462c4010ddd4b100437552c4010bd58610043765184010be596100437965840109e59610042f96184010de94610043f25184010fcd0610043f04184010fccc610043f03184010fcc8610043f021840109fd9510042bf6444010af19110042df6344010b718d10042ef6244010bb18910042f76544010ddd9510042776544010edd9110042f66444010bd19110043b46444010ad19110043d76344010bd98d10042f46344010f518d10042d46344010f9d8910042f66244010bd18910043e46244010b918910043775244010dd54910042f76044010dd94110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010
  | 1 => 0x435f5310c10e750c430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f58152042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109d984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf55342042f661d0810bd587420427f65908109f996420427d65908109f19642042de6390810b758e420436e5290810db54a42042f66190810bd586420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420427f65cc8109f997320427d65cc8109f197320435e53cc810d754f32042f661cc810bd587320427f658c8109f996320427d658c8109f19632042be648c810af592320436e528c810db54a32042f6618c810bd586320427f654c8109f995320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320427e64944109f592510427d63944109f98a510427d62944109f59741042f565d0410dd597410437754d0410dd55341042f663d0410dd94f410437453d0410bd98b410437752d0410dd54b41042f560d04109fd96410427d6590410cf952410433d5490410bd98641042fa6090410be582410427f6550410b7d8d41042dc63504109fd94410427d6510410cf950410433d5410410ed50441042fa6010410be580410437565104109d59441042f66410410ed99041043775410410ed95041043755410410ed55041043355410410bd98c41043765310410dd14c41043b64310410ed10c41042f66210410ddd4841043755210410edd0841043b54210410fc98041042f56010410fc580410427d65cc410bd597310437565cc410bd99331042f464cc410dd953310437454cc410ddd4f310437553cc410bd98b310437752cc410dd54b31042f560cc4109fd96310427d658c410d794e310435d538c410bd98631042fa608c410be582310427f654c410afd9131042bc644c4109fd94310427d650c410d794c310435d530c410f54c431042fa600c410be5803104375650c4109d59431042f6640c410bd1903104376540c410dd15031042f6630c410f598c3104377530c410f594c3104375530c410f554
  | 2 => 0x53c8110d714f204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c5288110f9886204427f65481109f595204427c6548110afd9120442bc6448110cfd51204433c5448110b7d8d20442dc6348110d7d4d204435c5348110dbd49204436c5248110bdd8520442f461481109f99420442be6408110af590204433f5408110cf15020442de6308110b758c204435f5308110d714c204436f5208110db14820442f66108110bd58420443e62108110cfd53104433c54c4110d7d4f104435c53c4110dbd4b104436c52c4110eed5310443b854c4110f6d4f10443d853c4110fad4b10443e852c4110fc88710443f121c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110edd5210443765484110dd15210443b45484110cd15210443d75384110dd94e10443745384110f514e10443545384110bdd8a10442f56284110f9d4a10443765284110dd14a10443e45284110d914a10443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010b7d8d54042dc6355010cfd91540427f6355010d7d8d540425f63550109f18d540435c63550109718d540427f62550109f189540427f61550109f585540437461550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530437661d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a53042bf6454c10af191530427f6454c10cfd91530423f6454c109f191530433c6454c108f191530435f6354c109fd89530427c6254c109fd85530427d6154c10dd18553042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10d7d4f43042f661d0c10bd587430427f6590c109f996430427d6590c109f196430433f5490c10cf152430435e5390c10d754e43042f66190c10bd586430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd185430427f6510c109f994430427d6510c109f194430433f5410c10cf150430
  | 3 => 0x910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c9109f997414433f54d0510cf153414435f53d0510d714f414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c52905109f195414433f5450510cf15141442df6350510b718d414435f5350510d714d414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510d7d4c414435c5310510dbd48414436c5210510ed504414433f54cc510cf153314435f53cc510d714f314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c510afd9131442bc644c510cfd51314433c544c510d7d4d314435c534c510dbd49314436c524c510bed8131442f8604c5109f994314433f540c510cf150314435f530c510dbd48314436c520c510f54c4314427e65c8510af99321442bd64c8510cfd53214433c54c8510b798f21442dd63c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f5288510db14a21442f66588510dd99621442766588510edd5221443765488510dd15221443b45488510cd15221443d75388510dd94e21443745388510f514e21443545388510bd58a21443e75288510dd94a21443745288510f914a21443645288510bd982214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f86048510dd19521442746548510edd5121443765448510dd15121443b45448510cd15121443d75348510dd94d21443745348510f514d21443545348510f9d8921443e75248510dd94921443745248510f914921443645248510fcd8121442f46048510fc181214427e6508510cfd50214433c5408510d7d4c214435c5308510dbd48214436c5208510bd984214427e65d0110cfd53404433c54d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf152404435f5390110d714e404436f5290110db14a404427f65501109f595404427c6550110cfd51404433c5450110b7d8d40442dc6350110d7d4d404435c5350110bbd8940442ec6250110dbd49404436c5250110bdd8540442f461501109f994404433f5410110cf150404435f5310110d714c404436f5210110db148404427e65cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc110cfd52304433c548c110d7d4e304435c538c110dbd4a304436c528c1109f595304427c654c110cfd51304433c544c110dbd49304436c524c110bdd8530442f4614c1109f997204433f54c8110cf153204435f
  | 4 => 0x3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910f9d87524436f64d4910db993524436d64d4910db193524436f63d4910db98f524436d63d4910db18f524436f43d4910db90f524436d43d4910db10f524436f61d4910db587524436f60d4910db58352442be6494910af592524433f5494910cf15252442de6394910b758e524435f5394910d714e524436f52949109f992524433e64949108f992524427d6494910cf592524423d64949109f98e524435e63949109798e524427d6394910d758e524425d63949109f98a524426e62949109f586524437561949109f58252443796094910afd9152442bc6454910cfd51524433c5454910b7d8d52442dc6354910d7d4d524435c53549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427761549109fd81524437b60549109f994524433f5414910cf150524435f5314910d714c524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c52443e56114910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436e4314910db50c524436c4314910dbd84524436d6114910d9584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910b798e42442dd6390910d7d4e424435c5390910dbd4a424436c5290910bd98642442f561909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910bd98442442f561109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910af99232442bd648c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910cfd50324433c540c
  | 5 => 0x544427e6295110db98a544426e62951109f58a544436d62951109b58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109dd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f994544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf580544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d53534435e54d4d10d7553534435c54d4d10e7153534431c54d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a53443756194d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534427f6254d10dbd89534426f6254d109f189534436c6254d109b18953443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427c6114d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c7150534435f6414d10d7990534435d6414d10d7190534435f6214d10d7988534435d6214d10d7188534435f6114d10d7d80534435d6014d10d7440534427f65d0d109f997434427d65d0d109f197434433f54d0d10cf153434435f53d0d10d714f434427f6590d109f996434427d6590d109f196434433f5490d10cf152434435f5390d10d714e434427f6550d109f995434427d6550d109f195434433f5450d10cf151434435f5350d10d714d43442f76150d10bd185434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c434439d4310d10bd98443442f56110d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d
  | 6 => 0x2fa60d0610be583418437565d0610ddd5341843b654d0610dd55341843b554d0610bd98f418437653d0610bd98b418437752d0610dd54b41843f260d0610bd58341843f160d0610cfd52418433c5490610cf951418433d5450610b7d8d41842dc6350610bed8141842f86050610cfd50418433c5410610ed50441842f56510610dd59441843b66410610ddd5041843b75410610cdd5041843755410610ed15041842f66310610dd94c41843b64310610ed10c41842f66210610ddd4841843755210610edd0841843b54210610bd580418435e53cc610d754f31842fa60cc610be58331842f664cc610bd193318437654cc610dd15331843d653cc610dd54f31843d553cc610bd98b318437752cc610dd54b31843f260cc610bd58331843f160cc610d7d4e31842bf644c610af191318435e534c610d754d31842fb604c610be18131843d5310c610bd5943184375650c610bd99031842f4640c610dd9503184374540c610f598c3184377530c610f5d4c3184357530c610dd54c31843d4530c610f5d0c31843d4430c610bd9883184377520c610dd54831843d7320c610f54c831842f5600c610af99321842bd64c8610b798f21842dd63c8610db94b218436d52c8610be98321842f960c8610dd59721842f664c8610ed99321842b664c8610ed59321842f464c8610bd98f21843d663c8610b598f21843d563c8610bd18f218437752c8610f994b218437552c8610f954b21843f260c8610bd58321843f160c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610dbd48218436c5208610f948421842f56508610dd59421842f66408610bd19021842f66308610bd18c21843e66208610ddd4821843e75208610dd54821843e45208610bd580218433e5490210cf55240842f66190210bd58640843b44190210b7d8d40842dc6350210bbd8940842ec6250210bdd8540842f46150210cf950408433d5410210bd98440842f56110210ed10440842f6618c210bd58630843d4318c210db94a208436d5288210bd98620842f56188210f908620842bf6448210af19120842df6348210b718d20842f76148210bd18520842be6408210af59020842de6308210b758c208436e5208210db54820842f66108210bd58420843e42108210bd597108437565c4210bd99310842f464c4210bd98f10842f463c4210bd98b10842f462c4210ddd4b108437552c4210be597108437965c42109f98f544427d63d51109f98b544427d62d5110cfd8f544433e63d5110cf58f544433c63d5110cfd8b544433e62d5110cf58b544433c62d5110cfd87544433d61d5110cfd83544433d60d5110cfd5254442de6395110b758e54442ee6295110bb58a544427e64951108f992544427e6395110d798e544425e63951109f58e544435d63951109758e
  | 7 => 0x4d0310bd98740c42f561d0310cfd5240c433c5490310cf95140c433d5450310b7d8d40c42dc6350310bbd8940c42ec6250310bdd8540c42f46150310cfd5040c433c5410310bd98730c42f561cc310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310f988620c42bf6448310af19120c42df6348310b718d20c436e5248310db54920c42f76148310bd18520c42be6408310af59020c42de6308310b758c20c436f5208310db14820c42f66108310bd58420c43e62108310b798f54842dd63d52109f98f548435e63d52109798f548427d63d5210d758f548425d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210ddd85548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de98054842be64d4e10af593538427e64d4e10cf993538423e64d4e109f593538433d64d4e108f593538427e62d4e109f58b538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427f65d0e109f997438427d65d0e109f197438435e53d0e10d754f43842f661d0e10bd587438427f6590e109f996438427d6590e10cf952438433d5490e10bd98643842f56190e109fd95438427e6550e109f595438427c6550e10bdd8543842f46150e109fd94438427e6510e109f594438433e5410e10cf550438435e5310e10d754c438439d4310e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10ddd8552842be6414a10af59052842de6314a10b758c528436d5214a109f990528433e6414a108f990528427d6414a10cf590528423d6414a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433e54d0a10cf55342842f661d0a10bd587428427f6590a109f996428427d6590a109f19642842de6390a10b758e42842f66190a10bd586428427f6550a109f995428427d6550a109f195428433e5450a10cf55142842f76150a10bd185428427f6510a109f994428427d6510a109f194428427f65cca109f997328427d65cca10d794f328435d53cca10bd98732842f561cca109fd96328427e658ca109f596328427c658ca10af99232842bd648ca10bd98632842f5618ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10bdd8532842f4614ca109fd94328427e650ca109f594328433e54d0610cf5534184
  | 8 => 0x10d7d4e53c427e6494f109f59253c427e6294f109f58a53c427f6454f109f19153c427f6254f109f18953c435d5314f109f99053c427d6414f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c435e53d0f10d754f43c427f6590f109f99643c427d6590f109f19643c433e5490f10cf55243c427f6550f109f59543c427c6550f10bdd8543c42f46150f109fd9443c427e6510f109f59443c427c6510f10cf95043c433d5410f10d794c43c435d5310f10e750c43c42f66110f10bd58443c42be64d4b10af59352c42de63d4b10b758f52c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c42be6494b10af59252c42de6394b10b758e52c436f5294b109f99252c433e6494b108f99252c427d6494b10cf59252c423d6494b109f98e52c435e6394b109798e52c427d6394b10d758e52c425d6394b10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cfd5342c433c54d0b10db94b42c436d52d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10b798e42c42dd6390b10bd98642c42f56190b109fd9542c427e6550b109f59542c427c6550b10cfd5142c433c5450b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10db94842c436d5210b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10db94b32c436d52ccb109fd9632c427e658cb109f59632c42be648cb10af59232c435e538cb10d754e32c42f6618cb10bd58632c427f654cb109f59532c427c654cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10d794c32c435d530cb10db94832c436d520cb10bd98432c42f5610cb10cf95241c433d5490710be98241c42f96090710b7d8d41c42dc6350710cf95041c433d5410710ed50441c42fa6010710be58041c435e538c710d754e31c42fa608c710be58231c42bf644c710af19131c435e530c710d754c31c43d5310c710be98031c42f9600c710af99321c42bd64c8710b798f21c42dd63c8710db94a21c436d5288710be98221c42f96088710dd59621c43765488710dd15221c43765388710dd14e21c43765288710f994a21c43e55288710dd14a21c42f66088710fc98221c43f16088710bdd9521c43776548710dd95121c43745448710dd94d21c43745348710f9d8921c43765248710dd14921c42f46048710db94821c436d5208710be98021c42f96008710cf95340c433d5
  | 9 => 0x58f210835e53c8420d754f210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420d794e210835d5388420dd54621082ed6588420db59621082ee6488420bb19221083ae5488420eb55221082ee6388420bb18e21083ce5388420f354e21082ee6188420f9946210836d5188420f954621083655188420f9d0621083e44188420f9cc621083e43188420bb582210827f6548420cf951210833d5448420d794d210835d5348420dd945210833e5408420cf550210835e5308420d754c21083765108420dd54421083e52108420be98021082f96008420bb99021082ec6408420eb95021083ad5408420bb98c21082ec6308420f394c21083cd5308420bb98421083e66108420f9944210836d5108420f954421083ea6008420bb58021083e960084209f992500827d6494020dbd0a500836c4294020db886500836c21940209f597400833e54d0020cf55340083af42d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020bb98a40082ed6290020eb10a40083765190020dd546400827f6550020cf951400833d5450020bbd8940082ec6250020ebd0940082f76150020bd18540083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840083ac4210020dd94440083755110020cf953200833d54c8020dd947200837551c8020bb99320082ec64c8020eb95320083ad54c8020bb98720083e651c8020f9547200833e5488020cf55220082ed6288020db94a20083765188020dd54620083ba5488020ee55220082f96288020de94a20083ea5288020fad0a20083e84288020fc94620083f15188020fa88620083e821880209fd9520082bf6448020af191200833e5448020cf55120082f76148020bd18520083765148020dd54520082ef6548020dbd95200826f6548020ebd9120082ee6448020bb19120083ac6448020ab19120083ae5448020eb55120083e76148020bb18520083e46148020b918520083e65148020f954520082ef6048020db94120082fb6548020ded95200827b6548020eed9120083b86448020ee95120083b95448020bed8920083eb6248020de94920083ea5248020fcd8520083f06148020fc94520083f15148020b798f54c42dd63d5310bb98b54c42ed62d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c433e64153109f98c54c427d63153109f98854c427d6215310dd98454c43796015310af99353c42bd64d4f10bb98b53c42ed62d4f
  | 10 => 0x20832d54d0820bb98742082ed60d08209fd96420827d6590820cf952420833d5490820bb98a42082f66190820bd58642082fa6090820be582420827f6550820cf951420833d54508209fd94420827d6510820cf950420833d5410820eb50842082fa6010820be580420836d65108209b59442082ee6410820eb990420836f5410820eb950420836d5410820eb55042082ee6110820fa98042082ed6010820fa58042082be64d4420af593510833e54d4420cf55351082de63d4420b758f510833e5494420cf552510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420f918a51083e74294420f910a51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083746294420ddd0a51083764294420dd50a51083744294420dd98251083746094420cf951510833d5454420d794d510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083e46254420f9d0951083e44254420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420dd98951083774254420dd90951083754254420dd10951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f41082ee62d0420bb58b410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420bb98a41082ed6290420ebd0a41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420b7d8d41082dc6350420d794d410835d5350420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410833e5410420cf550410835e5310420d754c41083af4210420dd94441083755110420ed504410827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420bb98a31082ed628c420dd9463108375518c4209fd95310827d654c4209f19531082bf644c420af191310833e544c420cf55131082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420cf950310833d540c420dd9443108375510c420f54c431082be64c8420af593210833e54c8420cf55321082de63c8420b7
  | 11 => 0x7751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520d7d4e414835c5390520ddd46414837451905209fd95414827e65505209f195414833f5450520cf15141482df6350520b718d414835f5350520d714d41483775150520dd145414827e65105209f594414827c6510520cfd50414833c5410520d7d4c414835c5310520bb98841482ed6210520ddd4441483745110520ed504414827e658c5209f596314827c658c520cfd52314833c548c520d7d4e314835c538c520ddd463148374518c5209fd95314827e654c5209f19531482bf644c520af191314833f544c520cf1513148377514c520dd145314827e650c5209f594314827c650c520cfd50314833c540c520bb98831482ed620c520ddd443148374510c520f54c4314827e65c8520af99321482bd64c8520cfd53214833c54c8520b798f21482dd63c8520d7d4f214835c53c8520dd147214833f5488520cf152214835f5388520d714e21483775188520dd14621482fa6088520be582214833f5448520cf151214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520cfd50214833c5408520d7d4c214835c5308520ddd44214827e65d0120cfd53404833c54d0120bb98b40482ed62d0120ddd47404837451d01209f996404833f5490120cf15240483775190120dd146404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec6250120bdd8540482f46150120ddd45404837451501209f994404833f5410120cf15040483775110120dd144404833f54c8120cf153204837751c8120dd14720483bb54c8120ee15320483f351c8120fc147204833f5488120cf15220483775188120dd14620483af5488120db952204836c5488120eb152204832c5488120f9d46204836c5188120f914620483645188120fad4220482f661d5020bd587540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e61950209f586540823d6595020eb18a540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd89540827d6255020db189540827f61550209f185540833f6555020eb189540833e6255020cf189540832c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082f66115020bd584540827e6415020cf990540823e64150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f992520827d64948209f597420833e54d0820cf55342082ed65d0820db597420836f54d0820eb953420836d54d0820eb5534
  | 12 => 0x88620dd94521883755148620bed8121882f86048620f948421882ed6508620db59421882ee6408620bb19021882ee6308620bb18c21883e66108620f9d44218836d5108620f914421882ed6008620cfd53408833c54d0220ebd0b408833e5490220cf55240882ee6290220bb58a40883ac4290220cfd51408833c5450220bbd8940882ec6250220ebd0940882f76150220bd185408833e5410220cf55040882ee6210220bb58840883ac4210220bb597208836d65c8220bb99320882ec64c8220bb98720882f965c8220de597208827e61d51209f587544833f62d5120cf58b544833f61d5120cf987544833d61d5120cf187544833f60d5120cf583544833f5495120bd98654482f561951209f992544823e64951209f58a544836d62951209f986544837661951209d986544827d6195120dd586544827561951209f58254483796095120bdd8554482f46155120cfd91544827f6255120dbd89544826f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e62151209f188544827e61151209f58454482be6515120cf994544823e6515120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544827e65d0920cfd53424833c54d0920be98342482f960d09209f996424833f5490920cf15242482f66190920bd586424827c6550920cfd51424833c5450920bed8142482f860509209f994424833f5410920cf150424833f54d4520cf153514827e64d45209f593514827e63d45209f58f514837754d4520edd53514833754d4520dd953514837554d4520dd15351483b454d4520cd153514837753d4520f5d4f514835753d4520ddd93514837664d4520dd593514837464d4520ddd8f514837663d4520dd58f514837463d4520ddd8b514837742d4520dd90b514837542d4520dd10b514837760d4520dd58351482be6494520af592514833f5494520cf15251482de6394520b758e514835f5394520ddd4651482bf6454520af191514833f5454520cf15151482df6354520b718d514835f5354520cfd50514833c5414520d7d4c514837551145209f990514827d64145209f98c514827d6314520bd99451483766514520ddd5051483b75414520cdd5051483765414520dd55051483745414520ed15051483345414520ddd4c51483d75314520d5d4c51483765314520dd54c51483745314520f514c51483545314520ddd9051483766414520dd59051483746414520ddd8c51483766314520dd58c51483746314520ddd8851483774214520dd90851483754214520dd10851483776014520dd580514837520145209f997414827d65d05209f197414833f54d0520cf153414835f53d0520d714f41483
  | 13 => 0x9fd9741c827e65d07209f59741c837651d0720dd54741c827f65907209f99641c827d6590720cf95241c833d54907209fd9541c827d65507209f19541c82df6350720b718d41c82fb6050720be18141c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed6210720dd94441c83755110720ed50441c827f658c7209f99631c827d658c720d794e31c835d538c7209fd9531c827d654c7209f19531c82bf644c720af19131c82fb604c720be18131c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94431c8375510c720f54c431c82be64c8720af59321c82de63c8720b758f21c837651c8720dd54721c82fa60c8720be58321c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c833f5490320cf15240c833e5450320cf55140c82ef6250320bb18940c82f76150320bd18540c833f5410320cf15040c836d62d52209f987548827d61d5220de983548833f54952209f986548827d6195220bdd8554882f46155220cfd91548836f62552209fd85548837761552209dd85548827c6155220dd18554882746155220cf550548833e6415220db588548827e61152209f584548837a6015220cf953428833d54d0a20be98342882f960d0a20db597428836f54d0a20eb953428836d54d0a20eb55342882ee61d0a20fa98342882ed60d0a20fa583428833f5490a20cf15242882f66190a20bd586428833e5450a20cf55142882fb6050a20be181428833f5410a20cf15042883ad4210a20bb594428836d6510a20eb990428836f5410a20ebd50428836d5410a20eb15042882ee6110a20bb580428837751946209f992518827d64946209f98e518827d6394620afd9151882bc6454620b7d8d51882dc63546209fd91518833f64546208fd91518827c6454620cf191518823c64546209fd8d518835f635462097d8d518827c6354620d718d518825c6354620dd544518827f65d06209f997418827d65d0620bb98b41882ed62d06209fd96418827e65906209f596418833f5490620cf15241882ee6290620bb58a41883af42906209fd95418827d65506209f19541882df6350620b718d41882ef6250620bb189418827f65106209f994418827d6510620cfd50418833c5410620ebd0841883b541106209fd96318827e658c6209f59631882ee628c620bb58a318827f654c6209f595318827c654c620afd9131882bc644c620bbd8931882ec624c6209fd94318827e650c6209f59431883d5310c620af99321882bd64c8620b798f21882dd63c8620dd94621883755188620be98221882f96088620bb99221882ec6488620bb98e21882ec6388620f9946218836d5188620f954621883e74188620f910621883e73188620f90c621883ea6088620bb58221883e960
  | 14 => 0x8842103ae6210840eb948421033d5210840eb54842102be6110840ee98042102bd6010840ee580421037751944409f98e511027d63944409f98a511027d6294440b7d8d51102dc63544409fd8d511035f635444097d8d511027c6354440d718d511025c63544409fd89511027c6254440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be583411027d6590440af596411033d6590440af98e411033e5390440af98a411033d5290440af986411033d5190440af582411027f6550440b7d8d41102dc6350440dd94441103755110440ed50441102fa6010440be58041102be6310440cf94c41102be6210440cf54841102be6110440ed98441103b65110440cf54441103b55110440cd54441103ba6010440af58041103b960104409fd96311027e658c4409f59631102be648c440af592311039c438c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af1913110376514c440dd545311027f650c4409f994311027d650c440afd9031102bc640c440ed10431103d5310c4409fd97211027e65c84409f59721102be64c8440af59321102de63c8440b758f211036e52c8440db54b211027f65884409f996211027d6588440af99221102bd6488440dd94621103755188440ed106211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440ed10521102fb6048440be181211027f65084409f994211027d6508440afd9021102bc6408440cf90a501033c4294040cf906501033c4194040af98b401033d52d0040af98740102bd6490040cf95240102f96490040de95240103ba5490040ee90a40103b84290040ee90640103b841900409fd9540102ef6250040bb18940102f76150040bd18540102bf6550040cfd95401023f6550040ebd8940102bc6250040eb18940102ac6250040cf54940103b76150040af18540103b46150040ad18540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040fad8940103e86250040fcd8540103f06150040bd98754c82f561d5320db98b54c827e61d5320dd98754c827661d53209f58754c837561d53209d58754c837960d5320cfd5254c827e61953209f58654c833f64553209fd8554c827c6155320cf55054c833e6415320db98854c827e61153209f58454c83796015320cfd5342c833c54d0b20cf95242c833d5490b20bd98642c82f56190b20be98242c82f96090b20cfd5142c833c5450b20cf95042c833d5410b20be98042c82f96010b20af99351c82bd64d4720b798f51c82dd63d4720ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c8375511472
  | 15 => 0x5036c5294540ddd4651502df6354540b718d515035f5354540bbd8951502ec6254540dbd49515036c5254540d7d4c515036f5214540db148515037551145409f98c515027d63145409f988515027d6214540cfd08515033d4214540bd99451503766514540ddd4c51503d75314540d5d4c51503765314540dd54c51503745314540f514c51503545314540ddd4851503e75214540d9d4851503765214540dd54851503745214540f914851503645214540edd0851503b54214540ddd9051503776314540dd98c51503756314540dd18c51503776214540dd98851503756214540dd18851503774214540cdd0851503764214540dd50851503354214540dd10851503776014540dd580515037540145409f997415035f53d0540d714f415036f52d0540db14b415037451d0540d7d4e415035c5390540dbd4a415036c5290540ddd4641503745190540be98241502f96090540b7d8d41502dc6350540d7d4d415035c5350540dbd49415036c5250540ddd4541503745150540bed8141502f860505409f994415035f5310540d714c415036f5210540db14841503775110540ed504415027e658c5409f596315027c658c540d7d4e315035c538c540dbd4a315036c528c540ddd463150374518c5409fd95315027e654c5409f19531502bf644c540af191315036f524c540db1493150377514c540dd145315027e650c5409f594315027c650c540af99031502bd640c540dbd48315036c520c540ddd443150374510c540f54c4315027e65c85409f597215027c65c8540af99321502bd64c8540b798f21502dd63c8540d7d4f215035c53c8540dbd4b215036c52c8540ddd47215037451c85409f996215027d65885409f196215035f5388540d714e215036f5288540db14a21503775188540dd146215027f65485409f995215027c6548540d7d4d215035c5348540dbd49215036c5248540ddd45215037451485409f994215027d65085409f19421502be6408540af590215035f5308540d714c215036f5208540db14821503775108540dd144215036f52d0140db14b405037751d0140dd14740503eb52d0140fa14b40503bb42d0140ee50b40503f351d0140fc147405036f5290140db14a40503775190140dd14640502bd6290140ebd4a405033c5290140eb14a405032c5290140edd46405033c5190140ed14640503345190140eed42405036f52948409f986521027d61948409fd85521027c6154840db54852102f66114840bd584521033e54d0840db94b421036d52d0840be98342102f960d08409f59642102f66190840bd58642102bd6590840cf596421023d6590840af98a421033d5290840af98642103b66190840ad98642103b56190840af582421027f6550840cf951421036e5210840db54842103ad4210840be98042102f96010840af9
  | 16 => 0x96090a40db949429036d5250a40bed8142902f86050a40eb50842902bd6510a40cf59442903ae6210a40ebd48429033d5210a40eb14842902be6110a40af58042902de63d4640b758f519037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640dd54451903765190640dd54641902fa6090640be58241902be6390640cf94e41902be6290640cf54a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241902df6350640b718d41903765150640dd54541902fb6050640be18141903b54110640af594419033d6510640af98c419033e5310640af988419033d5210640ed98441903b75110640cf54441903b45110640af580419027f658c6409f996319027d658c640af99231902bd648c640d794e319035d538c640e710e319027f654c6409f595319027c654c640afd9131902bc644c6409fd94319027e650c6409f59431902bf640c640af1903190376510c640dd54431903b4410c640f54c4319027f65c86409f997219027d65c8640af99321902bd64c8640b798f21902dd63c86409fd96219027e65886409f59621902be6488640af59221903765188640dd54621903b441886409fd95219027d65486409f19521902bf6448640af19121903765148640dd54521903b441486409fd94219027e65086409f59421902bf6408640af19021902bd65d0240cf59740902be62d0240cf54b40902be61d0240be597409037965d02409f987525027d61d4940ebd93525036f64d4940dbd87525036e61d4940db587525036c61d4940dbd83525036d60d4940dbd4a52502f66194940bd58652502f76154940bd185525036d52149409f984525027d6114940bb994525036e6514940eb590525036f6414940dbd84525036e6114940db584525036c6114940dbd80525036d6014940db500525027e65d0940db14b42502be65d0940cf997425023e65d0940ebd4b425033c52d0940eb14b425032c52d0940af98342502bd6490940dbd4a425036c5290940bd98642502f56190940be98242502f96090940dbd49425036c5250940bed8142502f86050940ebd8942503af5250940cf14942503ac5250940cb14942503bb6050940af18142503b860509409f99442502be6410940dbd48425036f52d4540db14b515027e63d45409f58f515027e62d45409f58b515037753d4540f5d4f515035753d4540ddd4b51503e752d4540d9d4b515037652d4540dd54b515037452d4540f914b515036452d4540edd0b51503b542d4540ddd93515037763d4540dd98f515037563d4540dd18f515037762d4540dd98b515037562d4540dd18b515037742d4540dd90b515037542d4540dd10b515037760d4540dd58351502de6394540b758e515035f5394540bb98a51502ed6294540dbd4a51
  | 17 => 0xc4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421dd94431087d5310c421af99321086bd64c8421b798f21086dd63c8421eb99321087ad64c8421f398f21087cd63c8421bb98321086ed6288421db94a21087765488421dd15221087765388421dd14e21086f56288421dd94a21087e65288421bd982210867f6548421bbd95210876f65484219bd9521086ef6148421db94521087e64148421f950521087e63148421f94c521086ec6048421bdd95210877765484219dd9521087765448421dd15121087765348421dd14d21086f76248421f9d8921087765248421f994921087e64248421f950921087e63248421f94c921086f46048421ded42500867e64940219f592500867e63940219f58e50086bf6454021af19150086df6354021b718d500867f6454021cfd91500863f64540219f191500873c64540218f191500867f6354021d7d8d500865f63540219f18d500875c63540219718d50087762154021dd48550086be6414021af59050086de6314021b758c50087795014021bd98752d02f561d4b40dbd4a52d02f66194b40bd58652d027e6194b40dd98652d02766194b409f58652d03756194b409d58652d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40cf94b42d03ae52d0b40eb54b42d02be60d0b40ee98342d03b960d0b40bd98642d02f56190b40afd9542d033f6550b40ebd8942d033e5250b40af18142d036e5210b40db54842d02fa6010b40be58042d02de63d4740b758f51d02ee62d4740bb58b51d037751947409f98e51d027d63947409f98a51d027d6294740cfd0a51d033d42947409fd8d51d027c63547409fd8951d027c6254740dd54451d037651d0740dd54741d02fa60d0740be58341d02df6350740b718d41d03765110740dd54441d03b54110740be98041d02f960107409fd9631d027e658c7409f59631d035e538c740d754e31d027f654c7409f59531d027c654c740afd9131d02bc644c7409fd9431d027e650c7409f59431d02be640c740af59031d0376510c740dd54431d03d5310c7409fd9721d027e65c87409f59721d02be64c8740af59321d02de63c8740b758f21d037651c8740dd54721d027f65887409f99621d027d6588740db94a21d036d52887409fd9521d027d65487409f19521d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740db94821d036d5208740dd94421d03755108740dbd4a529027e6194a409f586529027f6154a409f185529036d5214a40bd98452902f56114a40db94a429036d5290a40bd98642902f56190a40be98242902f96090a40eb94a429033d5290a40eb54a42902be6190a40ed98642902b66190a40ed58642903ba6090a40af58242903b
  | 18 => 0xed99321486b664c8521ed59321486f464c8521bd98f21487d663c8521b598f21487d563c8521bd58321487e75188521f9d0621487e44188521f9cc621487e431885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121ddd0450487744114121ddcc450487743114121ddc84504876e2114121b798f54086dd63d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219d987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf550540867e6415021cf990540867e63150219f58c540867e6215021db988540867e6115021dd984540867e60150219f58054086be64d4c21af593530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530876e62d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21d754c530867e6414c219f590530867e6214c21db988530867e6114c21dd984530867e6014c219f580530867f65d0c219f997430867d65d0c219f197430875e53d0c21d754f430867f6590c219f996430867d6590c219f196430873e5490c21cf552430867f6550c219f995430867d6550c219f19543086f76150c21bd185430867f6510c219f994430867d6510c219f194430873e5410c21cf550430875e5310c21d754c430879d4310c21bb98843086ed6210c21bd98443086f56110c219f992520873e64948218f992520867d6494821cf592520863d64948219f98e520875e63948219798e520867d6394821d758e520865d63948219f597420873f54d0821cf153420867f65908219f596420873e5490821cf55242086de6390821b758e42086f66190821bd586420867f6550821cfd51420873c54508219fd94420867d6510821cf950420873d5410821bd98442086f561108219f597320875f53cc8219fd96320867d658c821af99232086bd648c821d794e320875d538c821bd98632086f5618c8219fd95320875f534c8219f59432086f6610c821bd584320867e64944219f592510867d63944219f597410877651d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd9541086df6350421b718d410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb58841087765110421ed504410867d65cc421dd947310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c421afd9131086bc644
  | 19 => 0x544867e63151219f58c544867e60151219f580544867e64d4d219f593534877561d4d219f983534867d60d4d21d7d4e534867e6494d219f592534876d6294d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534867f6254d21dbd8953487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f43486ee62d0d21bb58b43486f661d0d21bd587434867f6590d219f996434867d6590d219f196434873f5490d21cf15243486ee6290d21bb58a43486f66190d21bd586434867f6550d219f995434867d6550d219f19543486f76150d21bd185434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434879d4310d219f997424873f54d0921cf15342486f661d0921bd587424867e6590921b798e42486dd6390921bd986424867c6550921cfd51424873c5450921bdd8542486f461509219f99442487ad42109219f997324875f53cc921d714f32486f661cc921bd58732486be648c921af59232486f6618c9219f19532486f7614c921bd185324867e65d0521cfd53414873c54d0521bb98b41486ed62d0521bd997414877665d05219d997414877754d0521edd53414877554d0521ed15341486f663d0521dd94f414877453d0521bd98b41487e662d0521b998b41487e562d0521bd583414867e6590521cf952414873d5490521bd986414867f65505219f595414867c6550521cfd51414873c5450521b7d8d41486dc6350521bbd8941486ec62505219f994414873e5410521cf55041487b54110521bd99441487766510521bd99041487b66410521ddd5041487b65410521dd55041487b55410521cd55041486f66310521dd94c41487745310521ed90c41487b44310521bd98841487b74210521ed50841486f56010521d7d4f314875c53cc521bb98b31486ed62cc521bd997314877665cc521bd99331486f464cc521dd953314877454cc521ddd4f31487d753cc521f514f31486f662cc521f998b31486e662cc521f958b31486f560cc5219f996314875e538c521d754e31486f6618c5219f59531486bf644c521af191314875f534c521d714d31486ef624c521bb189314867e650c521d794c31487d5310c521bd9943148776650c521bd99031486f4640c521dd9503148774540c521bd98c31487d6630c521ddd4c31487d6530c521dd54c31487d5530c521d554c31487d7430c521f510c31486f6620c521f5cc831487d5320c521bd58031486be64c8521af59321486de63c8521b758f21486f664c8521
  | 20 => 0x867d6414e21cf590538863d6414e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438873e54d0e21cf55343886f661d0e21bd587438867f6590e219f996438867d6590e219f196438873f5490e21cf152438875e5390e21d754e43886f66190e21bd586438867f6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bdd8543886f46150e219fd94438867e6510e219f594438867c6510e21cfd50438873c5410e21e750c43886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd58742886de6390a21b758e42886f56190a21cf951428873d5450a21bdd8542886f46150a21bd98732886f561cca21af99232886bd648ca21bd58632886f565d0621dd597418877754d0621dd55341886f663d0621dd94f418877453d0621bd98b41886f560d0621cf952418873d5490621bb98a41886ed6290621b7d8d41886dc6350621cf950418873d5410621bb98841886ed6210621ed50441886f56510621dd59441887b66410621ddd5041887b65410621dd55041887b55410621cd55041886f66310621dd94c41887745310621ed90c41887b44310621bd98841887e66210621f958841887b74210621ed50841886f56010621bd597318877565cc621bd99331886f464cc621dd953318877454cc621dd54f31886f662cc621bd583318875e538c621d754e31886ee628c621bb58a31886bf644c621af191318875e530c621d754c31886ee620c621bb58831887d5310c621bd5943188775650c621bd99031886f4640c621dd9503188774540c621f598c31887d6530c621dd54c31887d5530c621d554c31887d7430c621f510c31886f6620c621f998831887e5620c621f5cc831886f5600c621af99321886bd64c8621b798f21886dd63c8621bb597218876d65c8621eb99321887ad64c8621f398f21887cd63c8621bb98321886f565c8621dd59721886f664c8621ed99321886b664c8621ed59321886f464c8621bd98f21887d663c8621b598f21887d563c8621bd58321886be64d4221af59350886de63d4221b758f508877b50942219f992508867d64942219f98e508867d6394221ddd0650887744194221ddcc650887743194221ddc86508867f64542219f191508867f63542219f18d508877950142219f98f544867d63d5121dd587544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf99
  | 21 => 0x6454f21d798953c875c6254f21d758553c875f6054f21d798153c875d6054f21d718153c86be6414f21af59053c873e5414f21cf55053c875d5314f219fd9743c867e65d0f219f59743c867c65d0f21cf95343c873d54d0f21d794f43c875d53d0f21bb98b43c86ed62d0f219fd9643c867e6590f219f59643c873e5490f21cf55243c875e5390f21d754e43c86ee6290f21bb58a43c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f21cf95043c873d5410f21d794c43c875d5310f21e750c43c86f66110f21bd58443c873e54d0b21cf55342c875e53d0b21d754f42c873e5490b21cf55242c86de6390b21b758e42c875e5390b21d754e42c86f66190b21bd58642c873e5450b21cf55142c875e5350b21d754d42c873e5410b21cf55042c875e5310b21d754c42c87ad4210b21bd98442c86f56110b21cf95232c873d548cb21bd98632c86f5618cb21cf95341c873d54d0721d794f41c875d53d0721bb98b41c86ed62d0721cf95241c873d5490721d794e41c875d5390721cf95141c873d5450721b7d8d41c86dc6350721d794d41c875d5350721bbd8941c86ec6250721cf95041c873d5410721d794c41c875d5310721ed50441c873e54cc721cf55331c875e53cc721d754f31c86ee62cc721bb58b31c873e548c721cf55231c875e538c721afd9131c86bc644c721cf95131c873d544c721d794d31c875d534c721bbd8931c86ec624c721cf95031c873d540c721d754c31c87d5310c721af99350c86bd64d4321cf95350c873d54d4321b798f50c86dd63d4321d794f50c875d53d4321cf95250c873d5494321d794e50c875d5394321ded4250c867e64943219f59250c867e63943219f58e50c873e5454321cf55150c875e5354321d754d50c867f64543219f19150c867f63543219f18d50c86be6414321af59050c873e5414321cf55050c86de6314321b758c50c875e5314321d754c50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f58254886df6355221b718d548873f64552219fd8d548875f635522197d8d548867c6355221d718d548865c6355221dd185548867f60552219f181548873d5415221b798c54886dd6315221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f580548875f5394e219f992538867d6494e219f982538867d6094e21afd9153886bc6454e219fd91538873f6454e218fd91538867c6454e21cf191538863c6454e21dd185538867f6054e219f18153886be6414e21af590538875d5314e219f990538873e6414e218f990538
  | 22 => 0x431bd992310c6f4648c431bd58e310c6d5638c431dd94e310c7d6538c431f5d0e310c7d4438c431bd58a310c6f6608c4319fd95310c6bf644c431af191310c6f7654c431ddd95310c677654c431edd91310c6f6644c431bd191310c7b4644c431ad191310c6f7634c431dd94d310c7d6534c431f5d0d310c7d6434c431f550d310c7d4434c431bdd89310c6f4604c431f5d95310c6d7654c431d5d95310c7d7644c431e5d91310c7d6644c431b5991310c7d5644c431f5191310c6d4644c431e5191310c694644c431f5d51310c7d6544c431f5551310c7d4544c431f5d89310c6d7624c431f5989310c7d5624c431f5189310c7d7524c431f5949310c7d5524c431f5149310c7d7424c431f5909310c7d5424c431f5109310c7d7604c431f5981310c7d5604c431f5181310c6d4604c431f54c7500c7d53194031ded42500c67e64940319f592500c67e62940319f58a500c7774194031dd106500c6bf6454031af191500c6ef6254031bb189500c7d531540319fd91500c73f64540318fd91500c67c6454031cf191500c63c64540319fd89500c76f62540319bd89500c67c6254031db189500c66c6254031af990500c6bd6414031bb988500c6ed6214031f54c4500c7795014031b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f6395321cf98e54c873d6395321cf18e54c873e6295321cf18a54c873f6195321cf58654c873f6095321cf98254c873d6095321cf18254c873f64553219fd8d54c867c63553219fd8154c867c6055321cfd9554c873f6355321cf98d54c873d6355321cf18d54c873e6255321cf18954c873f6155321cf58554c873f6055321cf98154c873d6055321cf18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c873e54d4f21cf55353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f219f98353c867d60d4f21cf95253c873d5494f21d7d4e53c867e6494f219f59253c867e6094f219f58253c875f5494f21d795253c879e5494f21c795253c875d5494f21e755253c871d5494f21d715253c875f6494f21d799253c875d6494f21d719253c875e6294f21d718a53c875f6194f21d7d8253c875e6094f21d758253c875c6094f21cf95153c873d5454f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875f6554f21d7d5153c875e5454f21e795153c871e5454f21d755153c879d5454f21c755153c875c5454f21d7d9153c875e6454f21d759153c875c
  | 23 => 0xf997424c67d65d09319f197424c73f54d0931cf153424c6f661d0931bd587424c67e65909319f596424c67c6590931cfd52424c73c5490931bd986424c6f561909319fd95424c67e65509319f195424c73f5450931cf151424c67e65109319f594424c67c6510931cfd50424c73c54109319f997414c73f54d0531cf153414c6de63d0531b758f414c67e6590531cfd52414c73c54905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531cfd50414c73c5410531ed504414c73f548c531cf152314c79f548c531d7952314c75c548c531e7152314c71c548c531d7d4a314c7d7518c531cfd53504c73c54d41319f993504c67d64d41319f98b504c67d62d4131af992504c6bd6494131cfd52504c73c5494131ded42504c6bf6454131af191504c73f5454131cf151504c6ef6254131bb189504c73f5414131cf150504c77950141319f990504c67d64141319f988504c67d6214131d78c4504c6ee62d5031bb58b540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c6255031dd185540c67f60550319f181540c73d54150319f990540c73e64150319f988540c67d62150319f984540c77661150319f980540c67d6015031af993520c6bd64d4831af992520c6bd6494831dbd4a520c67e6494831cf992520c63e64948319f592520c73d64948318f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c76d52148319fd97420c67e65d08319f597420c73f54d0831cf153420c76e52d0831db54b420c67f65908319f996420c67d6590831cf952420c73d5490831bd986420c6f561908319fd95420c67d65508319f195420c73f5450831cf151420c6f76150831bd185420c67f65108319f994420c67d6510831cf950420c73d5410831db948420c76d5210831bd984420c6f561108319f992510c67d64944319f597410c6f565d0431dd597410c77754d0431dd553410c7d763d0431bd58f410c7d463d0431dd94f410c7d743d0431bd58b410c77552d0431bd983410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c6f661904319fd95410c6df63504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431ed504410c6f56510431dd594410c6756510431bd990410c7b66410431ddd50410c7b65410431dd550410c7b55410431cd550410c7d66310431bd58c410c7d56310431b558c410c7765310431f5d0c410c7b64310431ed10c410c7d44310431e510c410c6f56210431dd548410c7b74210431ed508410c6f66010
  | 24 => 0x548c67e62952319f58a548c67e60952319f582548c73f6455231d7d8d548c67f62552319f189548c67f60552319f181548c73d5415231bb988548c6ed6215231cf990548c75d63152319f988548c76e62152319b988548c67d6215231db588548c66d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c75d65d0e31d7d53438c79e54d0e31d7553438c79d54d0e31b758b438c7d661d0e31b7587438c7d561d0e31b7983438c73f5490e31cf152438c73e5450e31cf551438c6f76150e31bd185438c73f5410e31cf150438c79d4310e31b7594438c75d6510e31e7990438c75f5410e31e7d50438c71f5410e31d7550438c79c5410e31b7588438c6dd6110e31b7980438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a31d7d0d528c75c4354a319fd81528c67c6054a31af990528c6bd6414a31db548528c67f65d0a319f997428c67d65d0a31cf953428c73d54d0a31e710f428c6f661d0a31bd587428c67f6590a319f996428c67d6590a31b798e428c6dd6390a31db94a428c76d5290a31bd986428c6f56190a319fd95428c67d6550a319f195428c73e5450a31cf551428c6df6350a31b718d428c79c4350a31db949428c76d5250a319fd94428c67e6510a319f594428c6de6310a31b758c428c73e5490631cf552418c6de6390631b758e418c79c4390631b7d8d418c6dc6350631cf950418c73d5410631b798c418c6dd6310631e710c418c7b54110631bd597318c77565cc631dd953318c77454cc631dd54b318c6be64d4231af593508c6ee62d4231bb58b508c77b50942319f992508c67d6494231d7d0e508c75c43942319f98a508c67d6294231ddcc6508c67f64542319f191508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd8b544c73e62d5131cf58b544c73c62d5131cfd87544c73d61d5131cfd83544c73e60d5131cf583544c73c60d5131cfd52544c67e64951318f992544c67e62951319f58a544c67d6195131dd586544c67e60951319f582544c73f64551319fd89544c67c62551319fd85544c77761551319dd85544c67f60551319f181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d6015131af994544c73e65151318f994544c73f6215131cf988544c73d6215131cf188544c73f6115131cf584544c73d3115131cfd80544c73e6015131cf580544c73c6015131cfd53524c73c54d49319f993524c67d64d49319f983524c67d60d4931af992524c6bd6494931cfd52524c73c5494931dbd4a524c6bf6454931af191524c73f5454931cf151524c6fb6054931be181524c73f5414931cf150524c76d52149319f990524c67d64149319f980524c67d60149319
  | 25 => 0x6ee62d4c41bb58b531075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c41dd185531067f6054c419f181531075d5314c41d794f431075d53d0c41bd98743106f561d0c419f59643106bd6590c41cf59643106be6390c41cf54e43106bd6290c41edd8643106bd6190c41ed18643106be6090c419fd9543106f76150c41bd98443106f56110c41ed98443106bd6110c41ed58443106b56110c41b798f52106dd63d4841b798e52106dd6394841dbd4a521067e6394841d798e521065e63948419f58e521075d63948419758e521077661948419f982521067d60948419fd8d521067c6354841cf90d521073c43548419fd81521067c6054841db548521076e52d0841db54b42106f661d0841bd58742106be63d0841cf94f421073e52d0841eb94b42107ad52d0841ed98742106bd61d0841ed58742106b561d0841af983421067d6590841af59242106de6390841b758e42106f561908419fd9542106bf6550841cfd9542106bc6350841cf94d42107af6250841cf94942106bf6150841ed98542107b56150841af18142106be6410841db948421076d5210841bd98442106f56110841cf90e511073c4394441cfd0a511073d4294441af98f41106bd62d0441af98341106bd6490441cf95241106f56490441ad59241107765490441ed95241106f66390441ed90e41107b44390441bd58a41107b74290441ed50a41106f660904419fd9541106df6350441b718d41106bf6550441cfd95411063f6550441e7d8d41106bc6350441e718d411069c6350441afd8941106bf6150441cf94541106bc6050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107d76350441bd18d41107d46350441b518d41107b74350441ed90d41107b54350441ed10d41106f76250441edd0941107b64250441ed50941107b44250441bd18141107b76550441add9541107376550441edd8d41107976350441ed98d41107b56350441ed18d41106b46350441e518d41106946350441edd4d41107b65350441ed54d41107b45350441edd8941106b76250441ed98941107b56250441ed18941107b75250441ed94941107b55250441ed14941107b76050441ed98141107b56050441ed18141106b46050441ed50750107b54194041ded42501067e63940419f58e501073e4394041cf10e501067e62940419f58a50106df6354041b718d50106ef6254041bb18950107b541540419fd8d501075f635404197d8d501067c6354041d718d501065c63540419fd89501076f62540419bd89501067c6254041db189501066c6254041cfd09501073d4254041b798c50106dd6314041bb98850106ed6214041ed50450107795014041d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52
  | 26 => 0x3543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906ee6214e41bb58853906f66190e41bd58643907b66190e41af58643907b56190e41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529073e4354a419fd81529067c6054a41b798c52906dd6314a41db54852906bd65d0a41cf59742906be63d0a41cf94f429073e52d0a41af58742906be60d0a41b798e42906dd6390a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41af18d429073e5350a41ebd89429073e5250a41eb949429072e5250a41eb54942906bf6150a41edd8542907b46150a41af18142906bd65d0641cf59741906be63d0641af58b41906be60d0641bd597419077565d0641dd94f419077552d0641b798f50906dd63d4241bb98b50906ed62d4241ded42509067e63942419f58e509073e43942419f98a509067d6294241ddd06509067f63542419f18d509067f62542419f189509073f4254241cf509509077950142419f98b535067d62d4d419f983535067d60d4d41d7d93535075f62d4d41d798b535075d62d4d41d718b535075f61d4d41d7587535075f60d4d41d7983535075d60d4d41d7183535075f5394d41d754c535067e6214d419f588535067e6014d419f58053506de6514d41d7994535075f6414d41d7d88535075e6214d41d7588535075c6214d41d7d84535075d4114d41d7d80535075e6014d41d7580535075c6014d41d714f435075f5390d41d714e43506f66190d41bd58643506f76150d41bd185435075f53d4941d714f525067e63d49419f58f525067e60d49419f58352506de6394941b758e525075f5394941d714e525076f5294941b7d8d52506dc6354941d7d4d525075c5354941bed8152506f86054941d7d4c525075c5314941db548525067e63149419f58c525067e60149419f580525067e65d0941d7d4f425075c53d0941b798e42506dd6390941d7d4e425075c5390941dbd4a425076c5290941bd98642506f56190941d7d4d425075c5350941dbd49425076c5250941bdd8542506f461509419f994425075f5310941d714c42507ad4210941d7d4f415075c53d0541f5d4f415077453d0541f514f415075453d0541ddd4b415075f5390541d714e415079f5390541cf14e415079c5390541c714e415073f5290541edd46415075f53d4141d714f505067e63d41419f58f505067e62d41419f58b50506de6394141b758e505075f5394141d714e505077b5094141b7d8d50506dc6354141d7d4d505075c5354141bbd8950506ec6254141d7d4c505075c5314141de540505067e63141419f58c505067e62141419f58850507774114141cf9045050
  | 27 => 0x42b758f5190b7751946429f98e5190a7d6394642cfd0a5190a7e60946429f5825190b775394642dd94e5190bd65394642d594e5190bb74294642f9d0a5190b776494642ddd8e5190b766394642dd58e5190b746394642dd18a5190b774294642cdd0a5190b776094642dd9825190b756094642dd1825190b5e53546429fd8d5190a7c63546429fd815190a7c6054642ddd955190b775354642dd94d5190bd65354642d594d5190b755354642f554d5190b555354642edd095190be74254642dd5915190b776354642dd98d5190b756354642dd18d5190b766254642ddd095190b776054642dd9815190b756054642dd1815190ade6314642b758c5190b5e5314642d754c5190b755114642bd9875090af561d4242dd9475090b7551d4242dd9465090b755194242ded425090b6f42942429f9865090a7d6194242dd9455090b755154242cfd095090a7f61542429f1855090af66114242bd5845090b765114242dd5445090b795014242bd9864250af56190942ebd4a4250abe6190942ed9864250ab66190942ed5864250abd60909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d63145429f9805150a7d60145429f9875050a7d61d4142ded425050af76154142bd1855050b795014142dbd085050b3e42141429f9845050a7d6114142dd9865210b756194842af9834210abd6490842cf9524210af66190842bd5864210aed6490842db9524210bae5490842f99864210be56190842bb9824210a7f6550842afd954210b3f65508428fd954210abf6250842cf9494210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210aec6050842b798f5110add63d4442ddd465110a7e63944429f58e5110b3f4294442cf50a5110a7e60944429f5825110a7f63544429f18d5110a7f60544429f1815110b755114442ded425010a7e61940429f5865010af76154042bd1855010b3f4254042cf5095010a7f6154042ddd855010a7761540429f1855010b7461540429d1855010af66114042bd5845010b795014042d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41bb98853d06ed6214f41bd98743d06f561d0f41dbd4a52d067e6394b419f58e52d07756194b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41b798c52d06dd6314b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d06de6390b41b758e42d06f66190b41db94842d076d5210b41eb50842d06f66110b41bd58442d06de63d4341b758f50d06ee62d4341bb58b50d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c6
  | 28 => 0x30000001000000900500050054002002800900ac0130038004000001d0000007000000a002c012000c0070014005002000900080040014004000000000000050064015003801300040030018002000c001000c009007400100800060000005002800f004400100740010010012001401800440080010010000c0090030006002c011003800f0004000000000c003800200b001c0024049000800d00040000070010002c000000000000280050000007003c01600000060064000002c00000dc005000000d000000700000150000002001c00b0000004000400d000401a001000100440030010018000400000140010014000000400000000180034000009800100180050008000005000300000020000018000800700040200068007009800e001002500200000024007000000e000c00b0074002003c00000440000020002000000c0008013000c006002801500280010028002000000f000800f0000002000000b000000b0018000006c0060054002000000300000020030000001000000000000008008006c02a001800300000000000006000400b000000f0000022003800a003000400b800300100030000014002c001000400800780200000009000000c000800000380000010004002c000000000500f401a0014001000400a00100030000017001001500a8001000000e0008001005c000002c0040010004000000b00c000000000420068007001400000140040008000003002d00840000030004000400a00080010018001003000c0060008001c000002003a007800900200110058000002400d00000000008009000400401bc00a0000001007c00000a0007000000b004c0000040000004c0000000000002c0040004005000400500080000020001018407a000400e00080000000000002c005000c007000800b0004000000800c008402c00040050000004001400700c001400000010000000006800000380050000017008c0050000006000800000200090018000005800f00040180030006001400500080020014008000000100240000014000000c014000800c0030005001000000040060004004000801f0004000008001d004000300000090024000000400100580020000000006004f002801b00340180018003010c00a000000100200060080005001800a00080550028002002c001001400a0004000002800200100190000001008402bddd4651d0a7e63947429f58e51d0a7e60947429f58251d0adf6354742b718d51d0a7f6354742d7d8d51d0a5f63547429f18d51d0b5c63547429718d51d0a7f60547429f18151d0ade6314742b758c51d0b755114742bd98750d0af561d4342ded4250d0a7e61943429f58650d0a7f61543429f18550d0b795014342af5974290b3d65d0a42af9834290aed65d0a42db5974290ade63d46
  | 29 => 0x14001000800700b400a00c00000000003000400b000c02100000020068009000c000000000800080030070000000800300340030000029000000100100200000002003c00d000403d00cc016000400b0008000001000d01b0000001000300100090000001001c0140000000000000100040020008000002c00000000000090004000c00b0004001002802a000400f01980010014000001400800000090024013003403600000010028003001000000140080040015001c004001c0150018002000400200000000028000001c0000010000002c0000004000013c001005800000040040000001004000500c0000011c003003402000340090054000000400100380060004002001800d0014009000400100000100010000017c0350020016004c0000004000000c0000000003000001300040020000000003000d00100000010000003c0000094006003c00e000000800400000158000000c00400b4001001000f004c0000038031000c00500000670080018000000000000220030006001000000300070000000000c0030044032000c0000048003000000200a80000004004011c0040004000001401f00040030010000001400000040030010004006c07f00000010018000000c005004400000240030000008000c00300140070004000000c00000680000084008000402b0004000001001900a00020004012000c001000c000001400400000060008033005802300000010018005000c0000000001013c01d0004000000c00e0014001008800c000000400000400000009000000a00080000020004004000c002000501f4000000400400000290008001001400e000803100080010004002003c003004403c00400010010007003000e00000000004000008804d0000001001400300300180018003004400d0010000001c0000024005000800d0000016006400400180250000007000c006012000000040000000006003c0060000015009000d00700170010005005c00000080250004007002c00d000c00f00100090054002001000000040000030000005c00300000000084003009400b0000001003c0000008003000001900000030000005000801b0050007002800100000000000000001002900000000004006004c0010048001002c001000800500040020018000000001a0018003005001e0010000002400300200020000004004c00b001000101340000078007000c000000000e003c01300080ad00a000d0000002001c0010008000000c00600100010030001000c004004c011000c00d00300110000002000c00000140000000009000800000500030008014002800000340020060008000000f000800300000010040018003800000a4001000800700080000008008004800300080050050000004c002002401e0000005000003b0020
  | 30 => 0x1802d00180010004001000c016000400000000010004002001400800100030008000002400000d0018004c0010048004000000000100040018000006c004001400100f4003002400000040070044005000001b0024000001000e0000004010c0190008001007401500400010000000000401b00b0007000400000000020024016000401a0004000000c00d021400100140020008000002c000006c0000098002000000c000000000080060044016006800f002000600200070020001001404600280000028007012c000000800000000040014031002c00e00000000044012005c001001000a0040006000800c0018009000000c000400e0024000000000000140110008000000c000005c002000801200000050030004003c00000000130084000003803300040040028002004800100280000088010000400000480040024008001002500680000014000002400200240120028008000c00b000400e00000010008010003c00500500010004003000c0000008000003800d000406d0004006002400d00300000018000000807c000800100140030030002008800c000003f000c002001800800280350010000004800400200020000009001c0070008008000400c001000d0000000000400002f0006002800b003000000000060034000000400900040130000000000400200140010000005001800a00100060004000000001300100070084001009c00700040090000001002c007002c005000000000000020004002001800e004001b001000100540530004011000001a000c000000c00000000010000003000c0040004013003000900000160078000001c023000002c000000c0004001002c0000030003000005d0034001002400d00100250004009002c000000000500380000004014000c01500200000030001000400c005001c000001d00280620000001001401b000000900180240000002001002a00140180010004005c01200000040068004002c00000300700034002000400702580010030001001c000001400200280000050000001000500000040000002000800200800070018008000400b00180020000000000000200180050000002000c06300200040000001001c00f007400100040050104007000400c0034002006c00900000000000000000c003008000000140100010001004800000000000010003020801400040200018004000000000a000a0050002003801c000400100000070054009002c00000140010028006004c00200300010000002006c001000c01100000020018001002801d006c001006800700080140008002000000400000170014005000401200000000000003000800000080000018000000c0070000001000401d001800500040000000002002400600180020018002000003e00080010080007
  | 31 => 0xd000c0000008003000000e002803f00b80000114000000801000000000018008003400000480030004001002c00f004007b000000000a40300004000004400300bc005002401d00a400100a801700480070000000000801e0070000000c00c0000020000000600000210018005003800c00ac0010138001001c02000000220128004000c006001c002000000100200020038002000400100040080000007000000b0000005001800100400220014000000801d0020000002001600000090010004000000300980010000001002c00e00000130000006000000b00000040060005000000000340000018003000c0120044004006c002002400900000000038019001c011003c007000001400300370004022000400600080010018000000c0050064008000400a00600070198011001000000240000084001002c00b000000300000060000013002c001002c006000402a00000000000003001000f0000000003000000000050070000005000400100070108001000c000000006b0008018008000000080020018001004c00000a803e0070019000000100100070054087007c000000003e000800200040030054006000001a0018054001000200080000000004000400200100590000001000000c00080000038000002000b0038002001000600100040004000000004600080000018001001400100040000000000000800a00040010060002004c057003400b00040010024000001c002000c013000400900100110010001013c03d001001100040170058000001001b0000006000000900080070004005004c00300000010020002002c000000c0140014000000000e006000100000040000016000001c002c0040090004000000a00080090060022001c000002802f003400500a000100000000000043000800000440100010015000c01b000400100000000010025000001300380000000002006000100000010014001002c000001c005006802700040020000038000c0170024019001400100100280034003002c00500100090004002000000000080110004000002c021006400c000800d00740060028001000001b00040100000000000800100080000028000000000b00080080000008001000000080010000003007c00d000c01700a80060000005000c00e00080000018002005c00600240000018016000000c00040060000001000400600140170000004005003200180010020000000000d004800a0004001001c00a0104001007c03900280000000000008c0080028006000c014002402c00000020004011001c002007002a0008016000400600380060014004007000f004800c001000900240000000000003800100e0002000c00000080020038001000006a001400b001001200000020018001000800000000020018007000002b004
  | 32 => 0x12183a284fa00016e257824ec2d222aa13d9fa800018580bc8f140000000a269ca0b63aecab00a2a618f1772a78065a1dba3128ac99a0733a77207200d964e51e09c4a746773a19676a88e25071092a6a8a8c700956441a00006150515b19106680aa4560712cec8d0173e9b0d5e84c1834a4ea11f007884a800000006afd6220002a945b8daf2a7102f461c09b201e80007a2d36a29f1d4f460e0a963691b65ac263c78d2ee81a9a2fa7e70b3a65f0000b3f8ff860504aca919c09000164a7cf0c484b408c255f03b21d6296427310067510393a1469b2032c724043a1dc4e6908fa79622e1aca05542414b4af89efd074144036129942020318127ae40b7a416e24b8a61725aac80e72e6c0001ff60001c364e52ae60000f32000197e5fae96628e0eb822f23375ed8e50a37995a9d6a3ba0331ab24eaab85bd72a0e605a0382128a7a0000ee262a0000791a03700020e8b88ac6a2be9b547f5066a0f100000000a8800000000000000000180c70597c30640707381456300028c4ba3625400003527928ee400026749f0595b95fa1332ca83fe7192ea747d02d400001e92faaed231fab6e7c180006f4000051892cb7d400000000aab00000009ef000000009ac00008147dd80007742f0e0002078390c0002f100005c900000001b2900001dc2ab800004981f0315ad9b2d062c4675a27603f83587810974000000080f079eae1a6367c0248e31380cab0d028197a16c12dfac3f6cb2b883351b0858280000018029001400a001800400280030000002003802b001800700640000004015002c0070000000001c0060000005002800300000200014000000c00200100000018000002002500180000004007000c002000000f000000000000000030005001800f000800000480000040000000c00b00080080000002000400b0024009000001100840120008000001400200200010000005004001800780030020008001c013000c0010000001005802f00080070000002002c00300540010000000000c0000004003000003f00040820008004006c000005c000000006500000000038001000800c004c0030074001000c00000080010008027000c0020054002000c014000000e00000020028001000400000000000008000001800500200000000001000c00500200030008002001c0060068002000c0030078000000401e005c004001800b00100000018018000800000080070014008002c0040000001002800000280020020001006c04f001800a000000000140000004008000002d00000010000008007c00400100080004009004800a001c005003800100080010000002000c001002000b00000040064002001c006017000a0008009000800200280030004001003c000001c002006c015003c009001800b000000800180060010002000000
  | 33 => 0xd02e8904d0000b3200000000002410a7d0404ba01d4e6ce09c24a92980a9fa5ae6f12f3049f01ce5a69ebe87f886073319409839d7e57883903c2dd02b7fa278278c00024d22e661b06df9f1211e0000d244f951b0767c35b8f41bbc00000005c7215068505ef83f80101abc000000051f6531c7c482c00015a1894251939070b80000000a8e000121e76b85da38f82ca2e608364851472b5191eeb59a38082da8ce0001955000237e14097a0011aa3e93c09b80e180008d9896019e0a8461ac00069e910c000152a802e46a53f15234c015801058000b76a4fe40d00000bfef2c766e9368549f595440a1c6952e826cba0b02382c322eb8a143df2dcc491238e0aaad3479498ec32c4c509bd6b6a1f400006f610183161067178a00e0e00ee632d8a5600016d444988cc54cd2e7549df16213071ab9d904a5fe23001858000000000000000004cf0d4528e865d35b04f46b102580b7839618680007d7a47500016e67dd16708348b1ca07aeb000024a0000158e0b04000748d05000015b450fe1363ca8ba66af0000000054c41f131e1b482762ad1d308c600002d8841c0000c1ab37643d4e7c0000002c8a88c99ee0000000a93019db31a95955294ac00000000c2000000008a900000e800000009420e366a453cc7188872b8a1c425da9db6bd11ade69f96848798de06ad5fe63b70a6c263a9e6262a94a78800ce3f4c8767c996b36200f6e80980007cc24325348d9a7b72c2c8e812e80de2c5097f9cd270a1436973a6af8186c1a63605d0579874a78a29cd000000031a27b40000000000000000000000dae35e00000000001106000000000021750001a9800001668c380008c28000b945d162e39a39000145170d11029c5ac420352973554849400005f00000654bd687783798000ba605e479217dc869aba60000bb83bb16e45f800006ec157a9e09b0c82b17ba8c2c0003ada7dab802f380000f9d05d90caa73967a9c164a8a7d9c050000c166ed24fa89dd4819320ee546113049a88000000254250e01bc00000006898c6400029440000000997970a359445600015fcb95000000009c054840000001085a0c2eaf4c8add60002b0facc9d8057d8000000155b8fe8e9c6ce97cc499034eae6436e4fc20e066b1405351da8987a2742665133e5305dbc4a8429a4210a0a93998c289b4e3805904e601312c483429bf01228f346c9b28956071e6738bfe5572606000042400001597b90e4412f1f3a9dd06dc3f5ad826cbc081462410ca6a4bd6bd30000897474574da8190cb00002a980002f7ace479d18db9e5c23415b502f0001c3e539c19c6f19312249a83249203428329d9247e9d64741179622380003e589822471f14000000042623a684f8000b3726680001ac38c040002fd48e81a6940f000000067e000000000000000000a7499e700
  | 34 => 0xa519a21df298c000051800007bd59400000f60da09d8911a67280002d5ab5400003cf0002ab56078000000075246e502c00000003fb8e6d17145221a897d22bd0a8300009aa0000ed025a80000744c03249019aa498e623a61912479c58a0000000ae1c00062b8000af923425b499360c491988c211f54392be0392101aa821630787247e9d600006eaaf60174800015b0e567f1ade36ec9e4d5e0e0e65bade2446b0be8b56875417380000000504a185ab70451844b55d8d0b669118adf1ec4b7f2d8c666a6f27862f5828d100a622aeec61e13eab4f2ef5819da1a72e8496b45a3196479c2a90484922cd818889e40005c58d041761e864a8e2b800eab5225d88227bd28fa4e70b5400000002d729ac39b80f54541ddaa779d6ab5598f094b156e0966940b31112b0002ac08318aa06dd82c00ee9e4bae79490bb715507ca80003d5aeea9c921e5000020083b61c300026b4bb2c000372d74a0001f9e87c800089c2c6c1e397260a900000000000849141e000190863cd4c80002b8f90953a9000012c2ae12165dc053169650f8b77c0001e3205c8d28000924a92e0001dde72d956300015d858910de399e73168eabfebb99ec03ef68f69441a527b9c6c323a8d8e9070fd144ea720aad9e9e19da2bcb82da007081f4e00022e45ab1417000251a2ce62961198d2cb706e3e0000b2708f24b64b01e1296915c40c519770002732830a3290000b456a90000596e91c45882a6464aa3c2bb8e0a36b0e8484f0a623a0aad894ae3d264ba2a0132a666398220411a0437a0c634818c976c47ca66e00005646e8c0005e91fee501956102e09423a2084e000259200021da02d220c9ac8cb4000071c3891ae400017607c8c0b7b94808f0910304bc80dea556909b30864b01deab1ea2c8f9b86f0f202b9a56ca858aadba200006b3000059080009c20000801231007bc61400019e222113ee7de15a2722116ab0a0000145df37000000078fa0888f9940ab199190a361496469851aa3c623e3c593ac65b24342069f187efae6a22699dc7f68c3471f83bc5f3edb80002ea06176e891a903542c493a20dfc6a800015463149dc60002344217a1f67304000464e6283e8e3116e1a4377646da6b9b883200015fa38e41061e907bc675108234b9ab191724964b19e3c28402f3bba4000389aaa00002ed01e800621d6adf55732816a761ac89af2e261d5a9416bb2c009de216c826a8b49d9a6da90592b631020200818d902ab27c267e413a86a091e1ac52f7547a5a6a6f8deeb46a4f16f4831e24f033e51214689e51b3f4109f2f874a76a2292499895a2e24e387ea1af9191a7e000082880009d299bc177a31c53b12245c60000b1fab100000202000142c37bef0f0001cc430e8a644998a825c492ac7a7d85a0000042321ac143bf82660000000376a2aeaaaa5
  | 35 => 0xe3cb3c86285abae9e20b81ea6a69dee4c0d0d080c6de6a08c00062600002836ea100000007b2008a20d1dc23fd0000844029e324ac9e468d1310000000000279e4f9a7ea5dd1e1e22ca42043a254e50b6e380ee00000af1eb898f93e72b397320afd2be73bcdde0fe5f9aadd0e13000000069625ea913102840f1bd600002ee4290fc8a1819b677f800073b13c6b4200004d6a25a536128878c80000c688c00ab941625f97fc8732142b6b80007b997f5a8c800043f00000002eda28194693e788542ac853c6daa5c62f89db81438c466521b23899eede83d58d29ff20b2992a04100026cd00026204aac0000000000a0f998d5631adb3df922015f800000023fc0000f60000000010d80009c9400000003d6000296800000007ac23aa0002d543b3112f911105c88a254197818ac000227e00029b751e80f0af5285e0001d8c61009e840866ca500c00063e8186380580443ca6a06b2ecff683ead6229d544232562fb1d9d9ea5fc000b3d88625309e63663e8d27b3ae2408e4fbb8ac21310002afc9f800006f88f220001c072e512a60ddc00000022f4564ac18b87800048680990000944000121246a0533000149583f024a7610000a62223a8058fae9f913a1b4f9b7c292aab83c791602572bc80002ba0a002a82baf66a6bbe92020000000b1000000002e830002f37000009a1730000910800060d400019412d800010994d5800068d68cfa15815734c026d313006e0218cd2056000076f80000a4800084119c84ee800026c121538d549200026dd1240da272f828b72ca68913218a2191af523c62bf67ae8398929c90c98a89492ef019b4fa53de51e28748c92134b520a2c3471a6e94823f867a890086390e075097ca2d8c0005d88f683d180003dc28ec29a00003c106c7874086a53cea70000241e000225801daeb16809aba0f4a339000090a32893623ac0bd10000fe41f5295c77489030e8805800000005e600000002a0c00004b6897aa3a9e8800000018b88259219044ae5d6a3c00056047dd307800000000260a5a72200023ec000072e3e31afc1f098a7a3355f8b0f9abd7a8400000000003e01866b3d115c9511e840001db000028c800000d10002bc279b1a32ab2920c6e116180000000a99800058f9ba46c5800055d4d9c000168c00026082c80fdc678e4b2001a84010193d835420ef2a7acfa64b11085b011f17b400008e3177a1c811da3ee000018700000000000000000000000002e280000001aae6c2800000000006a10972ac9a9ba1f59910036951ca6ae013ae51e0e7d902a022e500773b93322c6c0b65fc0c6ea0b89b486793a33cc15189678b5907e6c829989da8984135c38ca2ac1cc8f0070f0e900c41e302f41bb15045ff0b1884147cd20631bd11638954000129245472182fcb52823257289bca70400000000002
  | 36 => 0x76957e2046d98600015842a14000000000002a19780000516000000010fa958600800000017467a9a24c00001280000000000000000003502978b6a43e400064f8ca487585a8194a5cc0001a480001bf000000000000000631a334000199ea75c64e471000000000007ec0e1987e1a64ba721f49a140002820000a56e15c9028000aeeab7a5a9a2de1888a24a04c4728c588d052ba0bc1829638abb15727020a9206796600b481f642adfc8aaf13666bc16aa3705b643d11c7a00023135b316f400703c65fb40000002750a9700002b0000049c96da000054034d1cf02658000b23887e0000000a2483f000009c6000000005b000083761227e5a1687d22c5a47ce1550002b0679b82ec000201c9449c0e9672554507612078fc00068f400000000009cc0c705eb000000009fc00019041f68e155cd172a825159c881800000000001188c7c3918d728fd9e5a0939aa874893fa0002b6206a60dc0001cda00000000001078471dced9720ae0000201eb8481fbbc79b5034503703418b961c204c97c913ab4639ed69090000426ab373e82a2a80293360002dc453128aaa06a6980cf04c2767026c0002e0d42a235c07140005ad800082a055c4724000000257845c1c460001547b4297f60baa50000024fc43b05fc2698b185d482f83e0ae5c66222576a985fa7e8a27f1f895836290b3572a2c4650c29cf77ea112956822a47d970e1318aa964c003636e261888b282a56620ebad0252a865000010ba60a66f44f2859a4868d827e6bbc80206db229c000290a3a6aca81298000aa7098416f8f1c47b1b2278f46f005295582258a873038fca0000e0600004a211380329792aa4a2710436b3a7450a4e430b80a3550000f26bb9c00000007ee33b8790168aec40112e1c122989bb1a1f905f9add206d166a5022b22473455a8c780698de80005682f1f757000038d00008e888a1bb59769000062a48967234821b3e74d12fa936805053d000000027885032a887d82efc945aba74081aca2d1c000683ab3b0aa40000001e70663800072ec00035eab517ed8bc268e091a332182000016520002f3600000d084580009632df3979a0a00002b61216a4e134ccffc527800003123ae467db8c000073463381ed84e8d8d67d5e6a54a2932044521f3b54b5e8e2216700026b02255ae633e8ae203b266a0aeaf0c4b82ef430620ea7901cd0334166e354adc840153e4278ad7813f991c69363284ec5e53a4f80006371c102e80ff30000ff60002c440000000000000013b8b217f880000000000649833396c2ac20001b4200001302fd2d9673e80005ba549354100007c312bcaedeaae44b0000bc4a9b843a80d2103902aa95264600302464b483c82541e561e626b3687064a6e481044fb5f58a8c214d45e60da4289b9a1d980000000000674d83091c0e9246b8
  | 37 => 0x9ede87b04c45919d3c309000000026d25e20a6a18b855e0dfa8c043de8f400000007db0556b381a18000000078ba06900014768055380000049a25e91be0002b2eb992546badda86a9d853886a8000a5396a08b7050a72c2e44a0bd5453aaa3c84686c7833f00005f798e02d45b521cd921b0002db2798a9c7aa608280001de465a14440000000a075f2b00010b38e400002d2c0001ee2107b1c00001b6ad6e5f6d45c6891c004e10f282838d32a861fe00b32b2ab68182a6818898675400001e6184000000089651fe000042a58b24b436588468e4acb201c9db28bb58debc2808e508296c8938d4a2db80006d7835c0000000000000000024de00028065e892427911f0e6c502ce00000000001b2400020ae6fcc9648360000000070b3439bd40002c881e6979325680002ae9d0b000172c3860000bca80fd2a8ae53a69cd665381e9299516344c65bea0001740047210e37107004fe13c00df09f08b426569a6a65a72a94733392e4eb8f0ab003ce6486a324f65c206293be8d6b71d9efbb8e66f379088f010b26fb3f94c78b6781cb0000000000000062c00007c700000002b8c5d41e7700000009c0864ca4683225bf91450001efe24f8000bbdac1690b40000000c998cc5e7e5f909d49419e06bc700000000916bb6e596079520da4180004ae4f5e4a10c060f92b663a515fe65c96f22c389ee6f3634da2da99e0002a8abad0a3e2af9c400639c5e97094589e9000098019819e59aab9ed928385c8000436016ba12221a0002271732c51eab387ac67f8000202aa445364000b602aee0000bb0003904172900001ab0a1a00294de2fe1f2c5df2dd0a5c1e750000fb020c100217b018220b1eb18d38d3917e18920e201ac0002d100002ca600000004765ecc64e000004e0dcc930a0ab776288a529945a800277c9b2da0d54228782f39525901101f582252854d68bc4d91a81662e4e01d4e5de01e12ce069475eae917094d40faa66d2178353d8b62c120988879c9e66aa20e42fa4ae075d1129c408ae474eb1a3525bfc0302d514088b6b7422bd24d368226e7178a2af1052ada147c9a0963cb3216beb47a8ee34deb4c40f896e3efc306400114a1f11a689e10dd2b8608fc3bd07c69c02272ba953bd0a8e7a87b693401799a6254f2c2471e28da054ab3042d1075b1d108a0ab19d8035a40cb30af14a881bba11812a8819968eac221496c95f5c51d0d76ae4cbe4a4116864bb5cd83cb0b339d72e974ca1f800d00b2c0d915f49c79efc62813341a8001a4d7a05e6609afa29c04a0ae5a51c08ea1caa038d7008da3ac5c09ef89fb0af397b0e7a80d912a02f81488f5269144a4000934abf0a3749ae8271206ba483f8000086c4bc8c125e38f1a42c82be8d500002240d880001771ae46de057b9888b1f5d1a1fc0fc14efd84a8158cb84d3c20e
  | 38 => 0x3aa297e0002cba42a6834a82860691f19440000000000000000011cf0000000697d1829e00000bb322dd96420ad5488a602680000a030000533000030021be000035e91029165df80000002e7a6572839000237c0000ca3000148a1ab80009cb6c5876682283bec00096187e0327217e01680000000000a13157690ba7b80001532000125047a1fe8722959693b91788501668b5f82da7df82b244f2a12a2b27dcb51247402315094df5fa08e52d88a6d27a600000009a0df08085e3525f5ad0e5cc00000ec1bbb9498e0d00029e947ddcd690388feb1588000630a964fb205854e87f62a5e2022d622be0e569306ab514f830de898f917b81ba00009d5ae931fb0cc50c00000b499fcaa744dfd37e2f2e135022cbab2332184823bb7d80000fe800000026581c88000a400000000155967800fc2cf8d71606570770b40002771dd61a71fd007280006dc8ade3f8d36038205b70002f3e605c26e81204be75b19da0f0062c8f69256155199025486dd0002ba2a8d255ca26098030f1276000000000b1ef93e91cf840c8d02215a9fc813c0000002a9200015700000446b969fc0ac76b8b790514d3d222ef58f656446ec2865811b2b0002a2191a00007ab5b6500009229c2453285294196c392f84ceceeb323977826480dc59795ae0ba23ea80328f0aea69b64e2161091618f4a72000049cc0009fe83266d1087a9500c88056abb8019a49e04d931b39603ea549a7511dd118b2f28ae8b75226e4454096a9e82b451280002c690c602eacd415f1096190db34000074c93e000000000000fca67a00027260002e9d843137a01b26e80001342765c00079cc68aa200c2e9a5a7c00001e8e00001fca3580006f2edec214191aa0edfa4a48138faf70000075943e00012e92f00ed230b0000000016814000de0000000000270cb2400004cf662cb44ddcc097013e0001d990002d2895d00002d91e1f00000003de16a418e92ee0001ecd0001c149b3a3de4c7d0d482290c4b998dc69bf05ae88a9c0c3970fd82922c3646a998066fe8e433084084e9193430cd78c000293c3c4800000000000000000b39800000010b64bc1dc469beb18000000055a022058780003e1a61484280007acc00098ea2ee18026880000000a9280009cd003861a85508d90dd41ce800030a944e7232ad28146b9556e2f2616e800000024e4467269938117c02baabcaa04243e25780000f08fac000157e8d600000001bae8dd9e8aaf9800039468d000002d048b00000001d1e3b6169879850c10000008121846400022a872105b6559a95a1fd02a75882d7467a02c452d95c0b4c930d0466bb217587beabd9f1a5c7ac4c488694dadf812e98e26bf5d5835d86b1be018c24c419982a836792e23fa000080a6f3d12084c032f231a5b4000073021937e8e11894899ba72a50b5901
  | 39 => 0x957fa13a697141915e8f896b800000a13400000560a66060baab3852e22219e821c5dad4f69fca0c4558ad5053719d16dd0beb9f42dbc7f380007f7011607c83ca96124a600008129bb8000a8e1e47000000045d800000026804d18e22b1e6deda546d702ee8ca6318287a54d98503b02d12356a9874e4d14c156cec204402f0892902e52183be57c2b3e68ecad6baf2cc00950328ad3a6f60000000690800044891a500005bc00023569b8d4183e48ebc5f06d60347923cb04862bb1786fc26a2ec22712c920cc596e4c557ae11e1422ae240007ce0d7409dd5600e78000000179c69e2976aa1815c47f0c5a12220fa0001b687770000b1380004c080009a2d75c00000c2357800067980000001cdc80c9cc9144950a167aea6b7ba0ec5b2ab72b3589148c30818417ab040f7aa24526aab29931f68303164cb69000000000002f82d76a14aa5634407464db20ee9cd96482b1c8fa5af22847bd6132ab40d5995280002fda84291da2683c09a1e0000daa446d23a1481fbc0708d8a86da9546149654817da5e355139e8b39538bb62aba8998e0237622443f692ca32801bf768a1458471af36f85812525eafab5a04aa9fe03a093c99565fee1eab2901e8b64a1de735106057f63cc528a18000002e67bb02686fe00000001c4800001781170e4e06aed027321b5a192c00079e24cf67a499a0000d601121ae3a3f96064168a2a4c72e8e0002af0337ae1a0000000b50a8386a2a19500003a94464f8a0000dd6b0f699a4238a77a9e0000553c000548046a5bd93549ae0cc025594820b84a28a7c13eb03fc5760001f4631e800000005364e80c72bd040000e69dd43c4151abd7ae45aa0041884c28f829e08943f3af083382438a191e5017294f5b7900006f09a6cb4ba2d86c014280001c6e7d0850800011487f7a5666982b84000144614310d2985a6ed2fc181865a662d0ca853a91680c800011202808c106f39b8900029ee4fd0f8864f2a605cee1d49759512864000022a8f8e4971826858818a1a3dd2e0000172431e1448eda92cb1c9e2a5010000a4ccdc89bfa252000000053887d2bcf0b600001a7900000000002b5c764110e9a6e61e10780002539be89a28000ba283e0613a9786caa2fc27282b880099f642c10c55152c480001d4091991d669987a80000000000000098d000090610d3671eaa27a46d6c5749700b7726eb0002cb3a318bee2fa4000536a19c47552f997ca7435619d76b93d6954191cab88f2c7f00021250000b23370ceda66b8b108f81ffc92a41be74b1f94621c00037b40004e9400028b80e461ca0f60000000aa680009ce87d80001ae24f0800094f800047aae0a7dc000093889128ee1ce1000000061800000000000a5091d00000c073cf8f900a0ad9314b0b0070180000001d321b080000002e4a363165370e000
  | 40 => 0x380001b27715058c0a8ae8f0001410000000011300006c726ba309d07e7e080004dc00007d4a386000089c00000006d2a3300002e90000052b000130c37e952e0000000000000000000001fe041a768400000000000001f2e000132a000039700000003894000aac00004bf03038bf9ad89efc57a691ab5840e080e27d8aafba5834c38fd4b041c953e1b913b85002e5b9c119a51eaa72ea819c044da2d6ab95800089bd2a01c180004dfc59c0001c265614000855adb000015c87131d684f580000002807205abaaa71438285a801e0c2a028ac7de10962a5180002dcea61187a5f2000000000006a8186213b282ca2a4b882e300000001b60640800061f25d4b0c1ea20820000237414482e0000333000000004d60000ed6809d84c27225a02ce0000760a89000890701080a9a75ba15a5dd995800029d300022738238a4649b88483ba4db40b1800000028ca6018a7d76e830c22b16dc00022a978e2808769800000000008e60f7d6400000b45000066763848a9217a84b027d61ce8b84ce0d7e5eca8ba75dcb1d0002a365094b5000026ea4f20d5b7b815743ab823000000008084000a6c00129ec99fb3fc87fc7a71af881a97d1000027c489800020e2e360000a907ad98573dc9f5fb9fa2241a0885800025b203d800000002d81661b8029ec000725108ca7195690000000000011e00000000000000000000000018a90000000b2c00000001626a5f0000000022e1040000a9604220001e5f1fc8d942a24000b5060d60002023aeb54ba9b08a760000000758a3a479d9ac231d1d5a8c7e121931eead31a87c02030f7f61226df9f49bfeba919bb201169e6056630b70e7ac821934477c1d8e00022ec1821bfa708d9d24e45ba65179f881810f0a0000ff00001ef25ad169080c1567737a9712de16a256990dd4e05b1d39c2e161560cf84618000000156c0001bcc000000000008242b52b288f7294b2aa9ce4717c00016c00007701acd43992a5b3c101c07b8000000002e2d0297a000000099080001cc29f271c88e61ee4000000146000000000001ab3000000073d1a560001a2cbca15d042b800011f0298ace04e800029da744214c75f16a8000112d5fe800083d14a02d0e6d48fc96e0602937243e93ce1fa205ab49d14024eacb8436c1203f3c99452fae043db0d5c4b90c9802f487c9a48dfc6cc83023ad1ee15131282198a80fa3aabde49613b35b864c08b508e45d1019f00017da9009adf5c400002fc8000454c00085ba141b0aa4230001f8c095a85c9c180000000000a6d400034ea6e0000038943c22e806a8da8790c1f86cd67d84b5cd560002c06342065603560407578c379b048a669c6b703098000772130ba3880000002d94868add8a69a33a6359f101129e96000114eae010126001dec09a8bdd14d22ff000206c0000b4c5a
  | 41 => 0x35bb81391d52735439d0002d7a81505f6028c5d90002b9c38685b20001333520183e645ade7718d4fa3879382a888684000197da94000000017ec1a01d1c8d0cb6d0001c1295c9d50223037a3daa8e8000000000001842d680002fe8000acf1eaa11f86980000000000000032440003ed0c230e9992200001cf1be1d3eb2d23784e18000231000000018c8000292271996b52cf0b7fad5816a049dac500009100000000000000018eda9c81b814232aa9b100002e30b3db58670275e0fd8a7438c148c645190e1e500006889cb8ad822cc82f8e40b500000b7a9e51325d1bc3d52ee03acadf080520609ad80000ea80006311d96391652e4cd4d5d91ce02e88607a6ad187925b111b80d680009d5228b00003169a4e4084f49fea22d8bb66b1dbc119600000000b66bd8aaf800022f06070b265238a221840034b18024dad78ef6b34100800a814e1d1d9a6192239a8b2136e9138c04af1a7e2158635059940fb359281ca110000b43cd35bbc0ffe9808770026db260f41cae0000ebe00026a80001cbc77894378a89ab4b6605c46d71f925400000000000094795d469d23ce00025ee342aadc4e995be0d851163bb4f063519d6646695de02c25f815c86f300006640000000b7e946bbc00e5438e866086ea670741888290e4ee055964bd2901a90b98e0459769e4eb1700007cd80005b66374000000000000000202b423872ba81029eae6690c5c0296bf241612989a040df9408ae47a6a033bc62ed490d9ac07af1be69148e782eb12dc0002f4a78e95c27e198552f3000000004b842980000f6a88e0001afe7a21de853a000000001aeae28000a0f20f0000006b00017a60152f646b7081ea87800043b8ee8a6898f58c98e420001ee300018e4627ab2c0000c300000000307da2e0d44000bc8949808318aa000100ca86930a7cf87766af9e600850fd000021f000000000001c5a9c29e80aa4250a086000080fc00000003a100000006c49a5c9e19cf600005149c6199c4fd8c44ae6e576084277e55594a47ba0ac266c9aee84680005bd5a2a806000021127de5d616fcbb656d88195faaa3517f97181d4a1e11632ba118c07d98b0c4b0a04c7a668116e85a888f60000336a1e48f1146a1bfa7cc70c1f8e34817e76bd06fa5622d30bce42245d79ff28cf13749c34ed7833140eaa32c9c735ca2651f8b521332d298d685283a18de822e0000a67285336d95773e68000af686347fb21b02790566610a8542962bee8a223c224856362bd800025b018031782f6219a43c10c9d86079ed9d4c5069ea808ea2655e866630ee0c027025e92de497596890421e0602744acbc26408647551a7b22d0000bc9249001480bc78217d000012b488212da000103a00028963948000960a3f4000000067c2e0e97f22362f2118a000000000000002f5661a59017
  | 42 => 0xb2aa87639a11470001c4a0eba74848da8469f3a70f7991da700005742102076657a9dfa4a194a15c06bcaf38b807de8cceaf02b788a1862419f036627486e049b2d86075679c4cb108d4011ebf94d1d0c9c70b7c0ed89ea6710c4aab8a9c36ece4bab362744493a2344edacdeae40000489c0000002b82000273eb1b80000001ec608995909372ea281fdc321c39baf827856a0d101fa89f6de200027fe9bd0000000185c269190c61a40007ad128e00012ea9da00003a780007d8a58001faf466ad9a3cb8d1e2c000246227fa8687feac7b9890000082a72c09315786e65bc070912b012700005e1138a34a12cc2f5e1c200000003c3a2ea00000002cb80000000000492800000010a03fc45c84839f444688afea8bae8559d858e5ea2cbe10d232a8800daead41e5e29f968076b05948db27d611b28844075f041971742afa201a85783349209aaf3eda83a33299424478ddc3e7ebd65738b0a000000003ea068509c00014e41de036ecea00017e12bb00000002bac0e32cae0000978746291e19f9d261f392f400020116d192ae0000000461d0e79d3152c708588e38380a43d320e72d5511498b94aa14991364d28394000231da2c0da4000052a1c629cc308ac10527ca0451ec92c668ea840002f19873aebb810881c51900009fd964d6c847e69260fe000000003d72ab40002c7c01aad8a56b17ef23161c0000253a4a30d6e203c54a59700000d80000000053e1b404ef14405e065aac3c898886e02a80000000e748551a3600021865069bf6b981ccd6c7e072a3c800000000002171df60002833000165542e2db4277e68d4cb8d4d3ee94b29268adc1dc8fe626705a45f526c86e80dce9a7036a4632e868b49acf76922f866e076c6178372305c00084d40004a8800000000246a508a85ba8aca3f79d955384b740001dca1fe8cea5b380001ed87de3b79fc200010ad4559d78666c00090690d62ea8fa81ac1d2411babc467f146e4841e900000d319a3e90c49507486de0000a989479ae5e9e31bdaeb52ced8d4a060b441b980003c9154e000278e1b88b7073aa7ee6b058a600000004f4000092a80008b09ec32f62eb2b77997619799cc51b627c13861024d8d95958e81b70000c2894d9dfc00000006ac1f8a1009c5069b48427c2e2502b40000b850000a7bc2d39b6e72800020820000000291000092b1f6e3e994320ff281401c2a5230728a00b8906951b108805d689e9db88062a913da0bdcfb26ea000050a40001e00000720adca0000000a160102000000000001b97bb82889870efc27c9ea44ed2eee51411885fa14dfa8a11b46ae193218dac9634f2a68b5314bc000082000000284ade3be05509cb73289583228be79ca82e074e984f000038e5149aa5000116dbaaac775ef0f66421a7385ba14a839fa4605ce909c0749365a
  | 43 => 0x33580000a100004b6400000000000002a4209ed4f80e0447072397868d1a30488714e608782e40869bad3bc9f2800011db4038e645bc569cbced4e34244fff0b080000525780a32cb9c5339e54325696349e97f19b608c800000004d2189aac32aea000038f4e540000001b9800003cc73f8000000111762f206400000002862d367aac8eebd393dc035cffa6ed800080e4d189be250e5870b9a0002d6400021fa9ab83d4449288289a80005b7ae870000f640001352000150c22c14db8c09ad40002821156400000000000b71838a028d0c8298000000207c0001c0a1c118f255085882362b5a25a1b03a752a6e9dc2f342932e6213a61061898fef1f6427869d8f7a8cfad2a16a927894f10ac69aaa2c3a91e94bacd92820ea6e666a0bff17ca8094159eb20319ef6000000450ba71b090182d0b9e5f406980146fb15bc52bc6c0b54dce211d0121b6891993ba98fe724943ab03abbc382d72e6dfa56e4394c20406c00017b856e37b2dc205c25fa0000000a66000000000009eb969439f0000b02218250e64bb0000000a588bbe00000ef3f115ea3841ffe00000bf54501a40000438000204a1b6d1664b7847a2c1a9d6000000005b5e36763c0000001524000282d00029743a30c90430c0007d29af1aa7860c7c82448000199645d0c382c0a90260e90267d31b9663e5a1277d2c866fba0ce5925b0709fa59a59e0000438a48433c95348a34000413a84a9f4da0a4df00000002b2d3e8428a72e55c60659ae139dac4a0000000026130e20aa548bc09d987271e020000ac80000e41a7ea8a23e94000ac5a62b3f0a11439999be07692eb093e338000279a7be9ef7a36d29ea6f60e96240674420cd7354c19c2231985632125307435ed516e146646005ac79611c57aa5db453baee16d395949a126b7a522efe8cbeb7669263bc12e91940c3aa5f2b6916c4592d7c036149c121125e4770476117a9fea842c8c32bc56b038d8979c50782070d42aafe0cf600016e779f2ee39a500006611f3278027608cfdde65859073af620c83a003a484dde6859c80002a640006f91a8e743800000000004bb20460000bb200023701492090bd503920fa000000000008a4000000023ca0001a77000000068a249c0001104a1f222000026a4968ac846c41f022ca00004d4c00011014e40518cac976079c04f103600023f06c82bb0000246438f59f496b1df3bc5af66b4825b6a2901df93417544731c1c60d9470abd13963a5943b039a9773cda65092e10710002f424df9b8b000130730dad9c7b0431c69c80002d4d24065e93b0049221410e61ae3cb87230279f12632949963f22adbad80008c3c00000000000001b1e1eeac9a1b7a914a7aa81b3f300005bb2ee200000006b82f0142f00007b500008788dca277a77a9b703321f22888224497081e919e35e0
  | 44 => 0xffd00013ae3bc1cc7868000000003ee00011373388000000000023680000c8000000028270001a9e70b22169001b940000948b34989657b4a980000000a850f76b909554296800091780000001c80b462146304c9750000c8052fc0008cd80005772396b9793512fb02648c89983935970c9810d6729e6deb00fa8e053c0b5b05f9540aeda6957005df80bea105371509e32b81d8ad2912e8dbce00bbe147748a997f619202c65997895cd93e036081b277aab007381c44bd0131350093784569b1827d1cc32b325ca3be0000728a6ff42aa93aaa999c17b4a6e77402f174c76cce3b29a702b111ca0d9d38c43d87ca5050d4cbbfe1b2a9022644bd9bdc16401416a594452d38a9c0810eee00011960acef3aa6a190a22f800019a00008920000611c930240871400017947ee000080d285a1eb8ca8884094a3284a801169de0042836c7ec85520000000000217c82d00000000000b984e16000236860d00005091280a7540000002c0c00010d50000000000122248e2ce888c2e4c0000d2a72985465375a4c1b31b8d00000003b3ad594b5ae485ed0a000002e9b00000006461fd2000220a42251a042dc00000000007b2975539280000000dcd726acee1acea48a0dcda6a72a2512f4865bb9c208c7e61487994a92a818974c0000000287808d0000000000263281d279290b146f1d8c4090316baba62ae2e4872514837c1b010a2e3a3e88d928782b1283524212e41b9b3e116d65108cbb10f01e66a48b689ea8a5248d12b85db98b27f59b9e5ea942610024d1a7404d04c423068668f4a532a6d01b124283830740707c7372999d8a0a6c8dcb7c9b1aa658c855bfdb025a4892a2dd90876331c5c9228f40bc413987068b3081119d06cda12a63d982cba8cd801c0a7909c56ee5a9783f439aa6784e0c2b05f121c81cce7f4a5412326b417f254192b210e8ea056da9ae7138150675e538741dc5284e2dc0552244a48fae2a19112aa5351bc8432201b95e88f636f15b001720520da296a413c4cea3f0aa813a9c74b7dd39271b113ead9214868c179a60c894007d41187b6414071a12c76d3091849f81ba6aa52c50e10a329f19040b47054109492a785c0e2a138ccb08a5425abaa07fe7dc83ac8ad033a6419960069ca865ce61b81bb84b40cc01a85c51ee25b1924994c8000498ae68bb927ba9c2c8a584b829047625f050d107499f14a957698101cb0e5d4aea2126c18b7a9b19e26b6d8458b6aa3b06480786530163592ac0685f604dc51f4b46aff00e000000eeb3890100000a8aa1f80cf1e2212616590939849f0a63ba5be803daa78f0044248b9ea822205625bc28261649fba08add946624260b151230169800096a91c800000005be0162000017a0002622000000089e86946e281d418e1475246c53062151d24980c9447e1cf5adb0c08
  | 45 => 0xe45080007a8ebb41bcad58b076f1123c80006c12e3b59b0000ae48000146df7c09888d464e983770eab0e0002f562b49e666492d0c40500004400000814c000583810167917df3d42d2420f955e77c923d9e60000243ae321610fbe2c6627491ca7a000013bc0002da800011d490e934c24d80007c88000a8728251878000b2dae7c0000f3800016620000ac6000027ab2625c073c90cc17a18ba6119a3e93a07420001494000232c000000079e40005c680004c5873ead20eac5938b316538000896deea00000002c92ec08a5cd3e0000000866000000000004f50000267923b34e0ec800029727c5e64443f88a2acd0002055a1883c20ec6a7851ce05d12a9b01097c025126a0fd686c273959aa1c0e7200c003c15811c623381a14ff400080f80003c1452e7fd1f11000247ab32809337251e6751a65cb281aa29621cb414646206d040000001b8fbd20000aa5898c622400021d202bac52ae02c22a26285ae9457582c81d909da82000007428b4a6e964d834daf3266c0af82688bfc83e0084a4d22800001757b785de3000000013827f04548b84abc8688b819998864926809c8d482218b3492009ba2908000a648c0aa298c3e96a197900004260790b67000000000026be5408a7278681fea2180009a7871f19c09d68bac09100021c438529606816bf4688588c83944de00006c60001964029c4dab9d0cc602543ce8b80c9e00009e6444162a222a9bc6aa8a0c4470cb220090f4a7b029f00016144bf9274a0093435da0e657f90fe203d1a873f343e600014d0349a929b8406ea1b59fac8bcc696767469242e9e7a79c9c39ace9bca60ac4e28291b7000000000002776b3e24f40a51f79b4e80007226010bae000017d1048a0a0d6a2042d00ae69456000159e48d52526c151ba0000d58bd0c0009d489476d99ada000101e6a0268e153878a0001a0c06ee2f6512e079b08089e36c198a782800051c40160002a4eafb196292500009660b2259d0cbab2b103006498ea983299081ac0002882a047b2d1e4b7a0000a9aa18c90aa3fe94326cf000000000000008bc958a000000084a5a440002946183a55041b89f834690462280000000232e4dd80004585cac7e98dc0b411134833d98c58b9e141924000ab78238013a9106a35ba2a439b62209ab39837a4bc1b61a4b0000738ad1236e0001d884b5029d07ce382000000000012700002d527b5cbd4ac800005359ea57e9c00073a40004a681c77c794bb6ef960c4189cad00029529710000a5ba55e9b58dbeb0e9fcc1c3068c993a568a0d8c7663540000f880000002dbe95f03621ae1eac5fa80004c14fd41d427be8f1aa5a0002ec62f1944f470800092313459d917920d580600ad992a8125ec2933000092f8e8e60f26723c328620fb19b113f12330780ce800010c244c15493050c8c000
  | 46 => 0xb800000000005fdc00028c05a05e7a006a0540000001d2a5cf06729530d2248a0bdc5f3944d2c780003cd16883789a08369dad6a55a1008900cbeb79587e350ac52ac919fa99b18f8531874e6d58b142e782131752b0a838a2b68c52c2e33c1b302942b9d9aa81990388be5488c36d1d128c2ac35d933372c2682a93d1627141262d180802b25bc56a08ba8ed2c2249d680b5fa4e2e20f0ce695a8f4e9d4d0544b9974896d1b670dd8bf7b1ea7953dd13e256e8122315038ab0288de12620927262f1aa23178152f69a486d148875c9c7073f0df4131c0926f4df4047015a43f4871013c006407000008a29aac000181a37c158b889a0f2a4e0000aca6e08351156a851d9e56ba051da9d1ad2310916e48761a12f6a275693aabe6e7e5d2224c00027405420000e53b4c51c37520d69676e6f08c815935f080001b200000000ad800000000002e2c5c180009f22bbe00019afbb391a44810000b7d20c02950fec6ee6570118e850ae61290000009093a8000b57a4cab90dc562fc48ec54380009900000a4225e290526b92db017c0002471a4480a6abf8de47bc107600021764111b88bd40cabae3a73c65c136d809093269cd4a100004d23e711463362711608800002222600158eba0a71b48813686a000196774e0ea65fd13097ce4cc44a280b2170a34c7ed154da9b1aea5ef86ba7fe0e4c9e9e4ddae340003fa9c901cf1d255a29d2041e8000685925a6f6ae8c36c8e6c1ada1ee425295da29e2910001c581902ebe12398d771aae200b7e39e9f2a29a0001b6e8ea0d5f39786ed2dc8e282bf13302bc19c60a32070084a2810002cfc000167c42024461ec9d4db5c9a34147161a0cb81004a19cc69a40e2c61da04e35f000084a1ea0a680216241ae460dd06ec521246c62f9e4c5f64b864c6019891413e889b09629fa12176bd8074b6e9ca74dbdf13057ad4eb93516789191e2a7907a286284b00f4c00000026f7000000000024a2b6b2b3f520db8e000203abc10c9653a9a4a0001bf2a2a2d909492d626f78d407d680001ca0000a17c00000001b51aaa3e847ae04756a400097d9ce80001e970002bfa83840000000000696c0000000000031c000071800000001b8000000000000000001a20000000000007676cf11280000ba4000203d1d704d85a580009a196000ded1654ff000045ddfd800009d825502b74b24000aba07b09ab4000a7087cc8b59e8c68113249b316d79d0142b9ec1154491a86e00000004339d743d685781c594e9000000000000001a4287299d800006500001048000aeb8712000000007300000002e5033b0000a2f8d4e09fe594b4e10c073091e97a0a6e98f580000e1cb827680000609294c9558a36abddd587061766ac098863588892152150700006ce842228e3dec5443965e981b2910a57ae012a0107e4ac453f
  | 47 => 0x7c4c9958d27e8a1224a09b65f18a5c93387969b78b42bc18134134629eaaa1e2211481a211101b66ba64783459ce69ab0986475cf42177023eb7e5e0c57c92963d604548d16a7226f9af98c36bd0569e8944c81952a3719743f0004084560226d00e038a093be3cf0ba8638917c234934e758154ba49250444c868ea398b4f3661666821013213c4f94ab91f8423293085bdd4f228f064218f962875e95aa96e0c32480174e3ef011a1861f0f5395d140d21d75b4880ae9e281f44cad7b0958223867de74e938c8529b4586e4745720b28929480205fe0ead950a7724199548b4d59104cf8908b92a0495d36e4239c8b00df667787dc5e424d4220115824e154c02884eb3926ccc49300ea0000000000000012c86531a193ff29380000000000300917a2c5906c38484ae0940000853aac400025dc00019540002aac23e2e781caa9c056ca6e450f23b223d001852c56128b2932d1c9a66411400f21da916867ada40af303360d18cf400000007d511443d892925fb9633ba640c91d3c00000016c809080cd8a6000089a66c0000151619b00000d7c0000000000068298291f501640c68ae8da975da9f166469f57825bf40003968000000000000000000000000abd68cc00000000421fc47a740000002ad47da99f24a7115b9cbd8840001a5a41ae28c0b585ea000242f620a71a7559656000016018e5ac6afa8ec43708c9a58deb1c9a1c270a578f3a7531172b8c102462e6c806840c8269f0762b079b8274a298e66492c8020a91817000000002b3655ac00016d1a8234bc9885ff80009f50af281403a80726df8b3696b24d6187441a8f520ce177d8a48fc6aa391cb4f100003e61b2d6c24c62b610663161814c5d6a6e200018e821c2d062780324b5721a4849c28f89713f287f1add5790c6c1ed133a3b50e206fd048012316c2b0705828b6917d691d4b8639890809d19469099602171896610c004a6de83dc6039828b71a2941df81c1bab9c2221a09ec0aec70a4372e580000ab6871892026616ba44865ba2532ac6000206d9c386d4ab6812a99fa4a429bae728d889c98761f5637c8d431bbc000500570482e943d8bc4dfe61a276c0000000a61859a8aeaa00a72e38a436a6ec8560e6900016ee74ad6e50001a1f92221645ca1fae0000dba092184d95895ecb0e246e413216079701ec45edbac4c6a8242c940002da520a75c16fa1ad04f893183b45bcc29500011385962d55000207e0179a50235567e3741813b2529e89cccd125c8a4770002e951031a374eca0e47858b7185d22c670f4000bb20be67b620f39b124223de48d6a0826fa4f3eeba45fa68cb4940000a00d6800014fe98980001da0000000000000013ca00000f8ba6800000002fe9e31edd0001a8b8dc800000000000000000000028ea78800031997642ed0cfe000000019
  | 48 => 0x361947f4778ed3ab3258e6975c1e1d80580088812984e59ec9b840a0b4b23eea9900
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x85547454c310438a3a2a618821451d1530c410aaee4a98620855775d0c310438b2a68618821555d4430c410e28a8218620847575988310425b3a4c4188211d5db520c410aaae7a9062086666254831042aabae641882195597320c410aaaea9906208655654c831043a2a926418821741c1320c4108eeeab0062084b4745803104272392c0188218d59664c8410c6acab26420847575193210426b398c9908219559663c8410d2cc931e42086956498f210432ab2ac790821a599163c84108eaea31e42084b67418f210431b326a5908219598f52c8410c6cc8a9642086566354b210421f3a6cb108210f5d365884108bce7b2c420845d73d96210423aba8c8108211d5d4630841096ce931042084d673988210423bbb2a4108211ddd56008410968e8b0042084d473580210421fba2c3280210f1d161940108dee4b0ca00846c72586500429b3a64328021559cf21940108eaec10ca00845e73d96400422eb9ecb20021471cd5490010c6aa930c800853575106400431bb2883200211ddc765500108bce6328800845d731944004237390ca200211b5c86510010a38e6aa080084d473584400429aba882200218d594411001087ce9b2c600843d74d96300428e3a2a7180219554e618c010caeca18c600847771d95300421f3a0ca180210f5d0650c0108dce4328600846d72194300425a3a2c21802195594310c0108eeeab0c40084b474586200426a39ac310021595d421880108eee3b2a400843e74d94200421eba6ca10021179cf65080108bae7b28400847571594200421f3a0ca100210f5d065080108bce6328400845d731942004316b24a4100219358e5208010c5ac8a90400864d635482004332a94c210021595d42108010bc2e0108400847575193100423aba8c7880212d9d262c40109ace731620084757518b100423abb6a5880211ddd952c4010cccc4a96200847576946100423cbb4a3080216c9d32184010ba4e790c200863765d91100423abacc8880212d9d264440109ace732220084e672991100431bb28c88802195d976344010d28c9b1a20084757598d100425b3a4c688021359ce63440109cce531a20086576518d100434bb20c688021a51906344010ccecbb1220086a464d89100436231ec4880211d5d6624401096ce931220084d6739891004273394c48802199d946244010d4ec831220086a4641891004363b18c488021b118c6244010ccaea312200847676d49100431a326a4880219518f5244010cc8c5a92200847476549100431a322a4880219518d5244010cc8c4a92200863464941100432a31ca0880219918a5044010c76cbb22200863b65191100432db2ec68802196d946344010cd6cbb12200866b651891004354320c488021b218c6244010d60c9b0a20086d063d851004370316c2880211e9da5144010
  | 1 => 0x430423aba8c2a18218d9506150c10c6aa830a860865653185430432aa98c2a18211b9c86510c108dae4328860843d76d50430421ebb0a821821475cc5410c10a5ae42a0860845d76d4c430428f3aa8621821471d54310c10c3ecaa18860861d6550c43042ca38a862182117dcd64d48108b8e6b26a40843f7458f520421e3a2c7a90210f9d3615481087ae9b0aa40845e73d85520421fba2c0a90210f1d160548108deeca90a40862d645485204326b1aa429021879926314810c3ac9318a40861e6458c520430eb22c6290218b5926214810c9ac7310a40863664984520431ab24c2290219598e6114810caac7308a40845e73197420422eb98cba1021471cd54d08108eaeb30e84084d473587420422f39ecb21021175cf65908108eae2b2c840845e73196420422eb98cb210211d9c46590810c9ac7294840864d6354a420423abacc3210219954a61908108bee6b2a840845c73595420422f398caa1021175cc6550810a38e6aa2840847575185420431aaa0c2a10211e5d460508108bce6328840845d73194420423b388ca210210f9d065cc81087ae832e640851c7454f320425a3a2c3990210f9d3658c81087ae9b2c640847571596320421f3a0cb190210f5d0658c810c5ac9294640862d6454a320423abacc3190219954a618c81087ee8b2a640843c74595320421f3a0ca990210f5d0654c810a38e8a9a640847575185320432aa98c2990211e5d4604c81087ce8328640843d74194320421f3a4c5288210f5d262944108bce7314a20845d7398a51042aa39aa9a08211d5d853d0410a6ae829e82085657214f410423bbb2a5a08219998952d04108bce7b2c820845d73d964104237396cb208211b5cb6590410a38e6aa4820851c73550410429ab8aa820821651cd4110410a6aeb320820853575950410423bbb2a820821551cd5410410b28e6aa0820853776550410431bbb2a820821c5dcd5410410a68e6aa0820871473550410428a39aa8208214ddc954104108eaec29882085357414c41042b2b90a6208214ddd64310410e2ca721882085357510c410438a29886208211d5d662104109ace7310820847576d48410429aba6a420821999895210410a6aeba10820863565d08410429abaa84208218d5954210410e4aa4a1082085b070508410423bbaac020821351cd60104109c8e4b008208475751933104273390c9988211d5d854cc410aaae62a6620856572153310429a3a2a7988211ddd952cc410cccc4a96620843e74d96310421eba6cb188211b9cb658c4108dae5b2c620851c7454e310428e3a2a618821555c5530c410b28e8988620847575190310423abb0a818821555cc540c410acae42a062085557598c31042aabaca6188211ddd9530c410a68e8a9862085947454c31042abbb2a61882195dd9530c410e2ee8a9862
  | 2 => 0x4310221d114e218811087ce9b2a408843d74d95204422eb9eca902210fdd16548110878e8b2a408845f73595204421f3aec8902210f9d4644811087cedaa2408843c76d51204421f3b0a8902210f1d854481108bcebb1a408861f54d8d204430e2a6c690221179d46348110c3ea831a408861c5418d204422f3b6a690221171db5348110c3ec9a9a408861c64d4d204422f3b0a69022187d905348110c38c829a408862f64d492044316326a49022193d8f5248110c98c7a92408862f641492044316320a49022193d8c5248110c98c6292408863754d85204431a2a6c29022195d4f6148110ca8a7b0a408866452d85204431baa0c2902218d1506148110caea630a4088654531852044333a90c29022199148614811087eedaa0408843d76d50204421fbb0a8102210f5d85408110c3ea9318408861c5498c204430faa2c6102218715163081108beeda98408845d76d4c204430f326a6102218759353081108beec298408845d7614c204430f320a610221875905308110c5cc9a90408862d64d48204432731ea4102219358f5208110c5cc8290408862d641482044327318a4102219358c5208110c6ea9308408863454984204432ba9cc2102219514e6108110ccea5308408866452984204431baa2c2102218d1516108110caea6b084088654535842044333a92c210221991496108110acceb10840886666588420443922a44210221d114e2108110e50a829620887485314b10442ab39ca908221599ca5484110e28a9a9c20885367494e10442b3394a708221c5d505384110e28a829c208863454d8a104432a29ec5082218d1516284110ca8a6b14208872454d4a10443a229ea5082214d9d25284110aace729420886656214a1044393aa0a508221c91505284110e8ea629420887445314a10443333b0a508221995d852841108bce7314a80845d7398a540423b38cc52a02187d9063550108b8e6b0aa80865763185540432a318c2aa0211bdc960550108d8e4b02a80843f76550540428e39aa82a021875516315010c5aa8b10a80861e6458c540432a38ac62a0219398e6215010c9ac7310a80862e64588540432731ac42a0219358d6215010caac7308a80866562984540421f3a4c5298210f5d26294c10c3ae6322a60861c64d8d530421fba2c2a98210f1d16154c10c6ec830aa60863464185530422fbb2a629821471d15314c10c3ac8a98a60864d53588530431a38ac8298218b9926214c10c5ac9310a60862e645885304316b22c4298218d5926114c10ccac5308a60846e721974304236b90cba1821471cd54d0c108eaeb30e860846e721964304236b90cb21821475cc5490c10a5ae42a4860851c7454e430421fba2caa182117dcd6550c108eee2b2a860846e721954304236b90caa18210f9da5450c10a38e6aa2860851c7454d
  | 3 => 0x9053c8510c3ac829e428862e64d4b2144316b26a590a219398f52c8510c9ac7a96428862e6414b2144316b20a590a219398c52c8510c9ac62964288668529832144333b94cb10a218d99754885108eaed2a442885567395221442b3394a910a218d9945488510caccba9c428871454d4e214423abb4a710a214d9d25388510acce529c42886566514e214438baa0a710a21c51505388510ccccba94428872454d4a21443a229ea510a214d9d25288510aace729442887275414a21443922a0a510a21d1d4c5288510e88a6294428863454982214432a29cc110a219914a6088510c70a9b02428865853d81214431c2a0c090a219614c6048510cd6a4302428847676951214429b3a4a890a21559ce5448510acce52a2428871454d4d214429b3a4a690a21599ca5348510e2ea829a42887145414d21442b33aec490a21991976248510e48a9b12428874453d8921443922a6a490a21d114f5248510a6ce929242885567394921442b3394a490a211d9d85248510e4ea829242887245414921443a3a98a490a21d114c5248510accec29242886667614921443982a6c090a21d414f6048510c68a83024288654531812144332290c090a21cc1506048510ea0a630242886e362181214431a2a4c210a219914a6108510c68a930e8088654539874044332294c3a02218d15161d0110ca8a6b0e808866452587404422eb9ecaa02211b9cb65501108dae5b2a808845f735954044237b92caa02211b1c965501108bcebb1a808861f54d8d404430e2a6c6a0221179d46350110c3ea831a808861c5418d404422f3b6a6a0221171db53501108bcec29a808846e75d894044317aa6c4a02218b1536250110c9ea7b12808864c53d8940442373a8c4a02218bd506250110c58a8312808864f531894044326298c4a02211b9db52501108d8eda92808864f63d49404432631ea4a02211b9d852501108d8ec292808864f631494044326318a4a02218d1536150110caea7b0a808865453d854044333a96c2a02219914b6150110c6ea830a808863454185404432ba98c2a02219514c6150110ccea430a808866452185404431a2a4c3982219514e61cc110cc8a530e608863454587304432a29ac3982219914961cc11087ee8b2a608843c745953044237b92ca982211b1c9654c11087cedaa2608843c76d51304421f3b0a8982210f1d8544c1108dceda92608846c76d493044317b26a4982218b193524c1108dcec292608846c761493044317b20a4982218b190524c110c6ea9b0a608863454d853044333a96c2982219914b614c110c6ea830a608863454185304432ba98c2982219514c614c110ccea430a608866452185304431a2a4c3902219514e61c8110cc8a530e408863454587204432a29ac3902219914961c8110acceb10c40886666588620443922a4
  | 4 => 0xbee6b2e848845c73597424422f39ecb21221175cf65909108eae3b2c848845f73596424422e39acb21221179cc65909108bae632c848847671196424422f3acc72122187d526390910c38a931c848845c7558e424430faa2c7212218715163909108beeda9c848845d76d4e424422fbb0a721221175d85390910c9cc7a94848864d63d4a4244327318a5212219358c5290910c6ea930c848863454986424432ba9cc3212219514e6190910ccea530c848866452986424423a3aac3212218d1516190910caea6b0c8488654535864244333a92c3212219914961909108bce7b2a848845d73d95424422fb9acaa1221171cd65509108eee2b2a848847b70595424422f39eca21221175cf65109108bee6b28848845c73594424423bb8aca212211d9d66110910c68a93088488654539844244332294c2212211d1d56110910c68a8b088488654535844244332292c2212210f9d365cc91087ae9b2e648843f74597324421e3a2cb992210f9d3658c91087ae9b2c648843f74596324421e3a2cb192210f9d0658c91087ae832c648843e75992324421e3aac9192210fddb548c91087aedaa4648843f76152324421ebb0a91922187993538c910c3ac9a9c648861e6414e324430eb20a7192218b993528c910c5ac9a94648862e6414a3244316b20a5192218dd52618c910c68a930c648865753986324432a29cc31922199d4a618c910cc8a530c648863754586324431a2a2c3192219514d618c910ccea4b0c648866452586324421f3a6ca992210f5d3654c91087ee8b2a648843c74595324423db82ca992210f9d3650c91087ae9b28648843f74594324421e3a2ca192211d9d6610c910c68a93086488654539843244332294c2192218d151610c910ca8a6b08648866452584324431c2a4c1a0a21179d76350510c3ea9b1a828861c54d8d414422f3a8c6a0a2187d506350510c38a831a828845e76d4d414422e3b6a6a0a21179d85350510c9ec7a92828864c63d494144327b18a4a0a219318c5250510cd0a5b02828863b541814144334290c0a0a214d1d54110510b28e6a08828871753504414438a29a8220a21c9d494110510e48a4a08828865853983314421f3aec898a210f9d4644c51087cedaa2628843e76151314430fb26a698a2187193534c510c3ec829a628861c6414d3144317b26a498a218b193524c510c5ec8292628862c641493144334296c098a2196d4c604c510cd0a43026288594744c4314438baa26218a21c5151310c510e8ea49886288744524c4314421f3acc990a210f1d564c851087eedaa6428843d76d53214421fbb0a990a210f5d854c85108bceb31e428861f5498f214430e2a4c790a21171d563c8510c3ea8b1e428861c5458f214422fbb6a790a21175db53c8510c3cc9a9e428861d64d4f214422ebb0a790a21879
  | 5 => 0x863754d85434431a2a6c2a1a2195d4f6150d10ca8a7b0a868863754185434431a2a0c2a1a2195d4c6150d10ca8a630a868846e72d944344236b96ca21a211bdc96510d108d8e4b28868851d73150434428eba0a621a21479d54310d10a38eaa18868861e6550c434430e32a8621a21651c54310d108eceb308868863454984434432a29cc221a218d1516110d10ca8a6b08868845f73593524422e39ac9a92211ddc564d491087ee8b1ea48843c7458f52442a739ca9a9221535ce54d4910a9ee6aa6a48854c735535244387aa6a7a9221c315353d4910a5ce929ea48852d7494f5244297ba2a7a92214b1d153d4910e1ea829ea48870c5414f52443922a6c3a9221d114f61d4910a9ee6b26a48854c7359352442b3b8ac9a92214bdd163d4910a58e8b1ea4885677158f52442b3b8a87a9221591c543d4910e1a8621ea48852f7458752442963a2c3a922153dcd61d4910a98e6b0ea48852e74d835244296ba6c1a9221539cf60d4910a9ae7b06a48861f5498e524430e2a4c72922187d516394910c38a8b1ca48861e64d4e524430eb26a729221879905394910c3ac829ca48862e64d4a5244316b26a5292219398f5294910c9ac7a94a48861e6498e524430eb24c729221879916394910c3ac8b1ca48863664586524432b31ac3292210f9db545491087cec2a2a48861f54d8d524430e2a6c6a922187d506354910c38a831aa48845e76d4d524430fb26a6a92218719353549108bcec29aa48861f6414d524430e320a6a922187d936354910c38c9b1aa48861f6418d524430e320c6a92218bd936254910c58c9b12a48864f63d89524432631ec4a92218dd936154910c68c9b0aa48865763d85524432a31ec2a92218e1936054910cb0c7b02a48846f765485244297ba2a4292214b1d15214910a9ee6a90a48854c7354852442973a4c4292214b5d26214910a9ce7310a48854d73988524421f3a0c0292210f5d06014910c5ccbaa0a48846d7695052442a739ca829221535ce54149108deecaa0a48854f7355052442a639aa8292218b9945414910c9ccba98a48870f54d4c52443862a6a6292211b5da5314910a5ce9298a48852d7494c5244237bb2a6292214bdd15314910a58e8a98a48864e6514c5244387aa0a629221c31505314910e4ea8b08a4887245458452443a3a9ac229221d114d6114910a9ce7b20a48854d73d9052442b2b8ec829221595c46414910a5ce9b18a48852d74d8c52442b2b8ec629221595c46314910acee2a18a4885647150c5244386a188629221599c44314910acae2218a48852e74d845244296ba6c229221539cf6114910a9ae7b08a48852f7458052442963a2c02922153dcd6014910a98e6b00a48852f7444052442963a2202922153dcd1014910a98e6880a48845e73d97424422eb9ecba12211d5c765d09108
  | 6 => 0x1842373b4a490c211b5db52086108eaeda9043084e576d4821842f1386a410c21789c05208610968e8b0043084d473580218431b2a2c220421351cd6110210968e8b0c41084d4735862084332a92c2104212d9d262c42109ace731621084777654b1084333312a5884214d5c763d5110c3ec731ea88851e7318b544428eb98c5aa2214d5c462d5110a3ce7b0ea88851d73d87544428f39ec1aa221475cf60d5110a5ce5b06a88852d72d83544430faa4c72a22187d516395110c5ea9314a88862f5458a544432731cc52a2219358e6295110ccae3314a88864e6358a5444326b1ac52a2219598d6195110cccc4b0ca88861f64d8d544430fb20c6aa2218bd936255110c9ec7b12a88864c63d895444317b20c4aa22193d8c6255110c98c6312a88865763d85544432a31ec2aa22199d8b6155110cc8c5b0aa88866862d81544421fbb2a82a22147dcd5415110a38e6aa0a88852f725505444296392a82a221479ce6415110a3ae7320a88852e729905444296b94c82a221179ce62151108bae7310a8885377158c544430eb18c62a2214d5c46315110a3ce7310a88851d73988544429ab8cc42a2214d5c46215110a3ee6b08a88851c73584544428fb9ac02a221471cd6015110a5ee4b00a88852c7258054442a7394a9a9a21535ca54d4d10a9ee4aa6a68854c7255353442aab8ec9a9a2187d9264d4d10a3ce8316a68851d7418b53442aab88c5a9a21479d361d4d10a3ae9b0ea68851e74d83534428eba6c1a9a21539cb60d4d10a9ae5b06a68861e64d4e534430eb26a729a218bd526294d10c58a9314a68864f5398a5344317aa2c529a218b1516294d10c9ea6b14a68862e6498a5344316b24c529a21995c66294d10c5cc8b14a68862d6458a534431b322c329a21999896194d1087cedaa2a68843e761515344317aa6c4a9a218b1536254d10c5ea8312a68862c541895344317b26c4a9a218b1936254d10c5ec8312a68862c64189534431bb26c2a9a218d1936154d10ccec5b0aa68866462d855344334316c0a9a2117dd95314d10a3ee8a98a68851c7454c53442a7b92a629a21531c95314d10a3ce9318a68851d7498c53442a7394c629a21535ca6314d1087ce9310a68843d74988534430f32ea829a21175da5414d10a9ce52a0a68854d72950534422fbb2a829a2153dc95414d10a98e4aa0a68861e6515053442abb8ac829a21875906414d10aaae2320a68851e74988534428eba4c429a21555c66214d10aaae2310a68851f74580534428e3a2c029a2153dc96014d10a98e4b00a68851f74440534428e3a22029a211b9cb65d0d108dae5b2e868846f725974344236392cba1a211b9cb6590d108dae5b2c868846f725964344236392cb21a211b9cb6550d108dae5b2a868846f725954344236392caa1a21479cf5450d10a3ce9a9a868
  | 7 => 0x8a0621879506350310c3aa831a818862e5418940c4316aa0c4a06218d9506150310c6aa830a818843d76d5040c428f39ea8206214b9cb5410310a5ce9a94418854e73d4a20c42373b4a4906218b1925248310c98c7292418862c6454920c432631aa490621999486148310ccaa430a418846d76d4820c42973a6a410621539cf5208310cacc6b0ea90851e73d52548422f39cc52a421175ce6295210a3ce7b22a90843f7655054842aa39ac22a421479d35394e1087ce9314a70843d7498a538428f3a6c6a9c2117dd95314e108dce5b2e870846d72d974384237396cb21c211b5cb6590e10a3ae72a0870851d7494c438428fbaa8621c21475d54310e10b28e2a1887085347458752842aa39ac3a9421179cf6454a108bae7b22a50843e74d8d528421eba6c6a94211bdd95214a10c3cc9318a50861d6498c528430f322c629421875916314a10c6cc8b08a50863564584528432b31ac2294219558d6114a108bce7b2e850845d73d97428422f39ccba1421175ce65d0a10c6ca8b0e85084d473587428422f39ecb21421175cf6590a108bce632c850845d73196428422f39ccaa1421175ce6550a10a58e4aa2850845e73194428422eb98ca214210f9d365cca1087ae9b2e650843e74997328421eba4cb994212d1d161cca10caca6b0e650843e74d96328421eba6cb194210f9d0658ca1087ae832c650843e74995328421eba4ca99421531c9534ca10aace7aa683084757598b4184333316a5a0c21479cf549061087ced2a2830861e5418d418430eaa0c6a0c210f5db5410610a3ce7aa0830859473504418423abb6a820c21559cf541061096aedaa0830859673d5041842d9386a820c214d5db5410610c6aedaa0830853673d50418438b39ea820c21459cf5410610e2ae7aa0830853572d504184399386a820c216c9c05410610a6ae929883085367510c418438b2988620c21359ce62106108eeeca90830853774548418429b3ae8420c214d9d542106109a8e6b0083084e4725804184273390c998c211d5d662cc610cccc5a96630851e74d4e318430e324a698c2187191534c610b28e8988630855573950318423abb0a818c211d5db530c610a6ce9a9863084d576d4c31842cb3a6a618c21749c3530c610aaaeda98630865576d4c31842ab3a6a618c21c59d3530c610a2ce9a98630871574d4c31842aab96a618c21d49c3530c610ba4e0298630855475d0c31842ab3a88618c21c5950430c61096ce931063084777654831842abb9aa418c21559d7320c610aacea99063084b4745803184272392c018c218d59664c8610c6acab2643084d673193218432ab2cc790c21a599263c8610d2ac931e43086556558f218434b322c790c212d9d063c8610c6cc9a96430865663d4b218431b322a590c219598d52c8610d64c930643086d2639832
  | 8 => 0x6148020c6aa830a401047476945200831bb24a2900418d1925148020caec728a401065463945200823b3b2a2900418dd915148020c68c8a8a401065763545200832a31aa2900418bdd36548020c58e9b2a401066771d95200833238eca900418bd9764480208daeb32240104ae74991200827338cc8900418bd946448020958ed2a2401062f6595120082563b2a8900418bd955448020ccecbb0a40106a464d852008333b28c290041a9d906148020d48c830a40106c7631852008362318c290041a99506148020d4aa830a40104e4769452008333b2ca290041a91925148020d88c728a40104e4765452008333b2aa290041a91915148020e4aa8a8a40106c46354520083a2a9aa2900418b1925048020c76e9b2a401063874d952008339b8eca900419c1c76548020c76cbb22401063b65191200831db2ca8900418ed955448020d50c9b12401067365d852008339b28c290041ac1906148020da0c630a40106e3621852008339b2ca2900419cd955148020c9cc7316a98864d6398b54c432731ac5aa6219358d62d5310cacc730ea9886556398754c4333314c3aa6219958a61d5310a3ce7aa4a98852e72d5254c428f39ec8aa6214b9cb645531087eecaa0a98845e7398854c422eb9cc42a621479d35394f10a9ce5a9ca78845f7654c53c421f3a4c429e210f5d26214f108dce432c878846d7219643c4237396ca21e211b5cb6510f108dce5328878846d7299443c428eb9ca821e21475d25310f10a3eeaa18878851d7550c43c42ca38a8621e218799263d4b10c3ac931ea58861e6458f52c430eb22c7a96218d99261d4b10c6ac930ea5886566398752c432ab1cc3a96214b9d35294b10a9ce7a94a58862c7259252c430f324c729621875926394b10c3cc8b1ca58861d6458e52c431b324c3296218d5926194b10cacc730ca5886556398652c422f39ec8a9621175cf6454b1087ce9b1aa58843d74d8d52c42973a6c4a9621539cf6254b108deeca90a58845e7319742c422eb98cba1621479cf54d0b10a5ce5aa6858852d7494b42c422f39ecb21621175cf6590b108bce632c858845d7319642c430f2a4c721621875526390b10c6ca930c85886355498642c422f39ccaa1621175ce6550b10a3ce7aa2858852e72d5142c421f3b0a8a1621179cf6510b108bae7b28858845e7399442c422eb9cca216210fdd95410b1087ce832e658843d7419732c42a6b9ca5996210f9d3658cb1087ae9b2c658861e6494e32c430f322a7196219594e618cb10caaa730c658843e74d9432c421eba6ca196210f9d2650cb1087ae932865885947350441c42ca3a26218e214d9d25288710aace729443885667295121c423b3b0a890e21599ca53487108ecec29a43885367494921c42ab39ca490e211d9d85248710a3ce7aa4818852e72d5240c421f3b4a
  | 9 => 0xaa7314821062d5458a4108326a9ac5208419958a51904208bee6b2a821045c73595410822f398caa0841175cc6550420a68e2aa2821045d75d8d410830f2a6c6a08418755363504208baea31a821061e5418d410830eaa0c6a0841179da53504208b8ed29a821045e7654d410822e3b2a6a08418b5536250420caec728a821065463945410829a3a2a2a084195d8d5150420ca8c6a8a821066762545410831caa6c0a08419c54760504208bce7328821045d73994410829ab8ca8208418b5974210420a6ae9288821053775504410829abaa82208418dd954110420c6acaa08821059473504410838b29a8220841c554d4110420b4ee4a0882105b070504410821f3a4cb188410f5d2658c420c5aa9314621064d5398a3108316aa2c5188419354d628c420ccac528c621043f74595310821e3a2ca988410f9d0654c42087ae832a621043d75d91310821eba8c8988410f9da544c420878ed2a2621043e76551310821e3b2a8988418dd92514c420c68c928a621063764545310831a322a298841551cd514c420ccec4a8a621067151d81310821f3a4ca188410f5d2650c420aaae72886210557754c431082aabaa621884195d95310c420caaca9886210594744c4310838b2a26218841c5551310c420b8ee498862105d0704c4310821ebacc9908410fdd564c842087aed2a6421043f76553210822ebacc7908418795263c8420c3aa931e421045f7558f210830f2a2c7908418755163c84208baed29e421061e6494f210830eb24a79084117dd953c8420c3cc8a9e421061d6454f210831b324a3908418d59251c8420cacc728e421065563947210831b322a3908418d59151c8420cacc6a8e4210655635472108338a8ac1908411b5d4648842099ce6324421062d655522108236ba8c7108412b9d06388420c9acaa9c421070d5454e2108332b2ca310841c99515188420e4aa8a8c42107465354621083a2a9aa310841595d44188420acaea18c42107255448421083a2a9a42108419c9456008420e1aa8a9842107255454421083a2a9aa2108412b1d16008420998e6b0042106e2615802108316b2e85a00418b5516290020a5aea214801062e54d894008316aa6c4a00418b9506250020c5aa831280104ae76d094008317b2e84a00418d9536150020c6aa9b0a801063654185400831aaa0c2a0041a9d0861500208eced28a801047476945400832bb1ca2a00419518e5150020ccec528a801066462945400823b3b2a2a00411d1d95150020caec6a8a8010654635454008333b12a2a0041991895150020c5ca8b10801052d7510840082d4b808420041999895110020ccac4a8880107255454720083a2a9aa3900411b5da52880208f2ed294401043e76951200821e3b4a8900410f9d95448020878ecaa2401063654d85200831aaa6c2900418d95
  | 10 => 0x7305414720483a8298a390241599c65488120e48a9a8c40907275414620483922a0a310241d1d4c5188120e88a628c409065663987540832b31ac3aa0419558d61d5020a6ce3aa4a81053571d52540822fb9ac32a041171cd6195020a6ce3314a8105357198a5408297396c32a04147dcd6195020a38e6b0ca81063561186540829b38ec8aa0414d5c76455020a6ce3312a810535719895408297394c2aa04147dcd6155020a38e6b0aa81052c72585540829c382c2aa0418d5846155020c58c5302a81062c62181540821fbb2a82a0418d5526115020c6aa8b08a81063664984540832b31cc22a0418d9916115020cacc6b08a810655635845408333312c22a0418b59654d08208eaeb30c841063654986420831aaa4c3210411ddd56190820c6ca8b0c841063554586420831caa2c1210418b5954210820c74a8b00841062d659904208237bb2a8210418b99154108208deeab0084104e4715804208355322c0210418795263d4420c3aa931ea21061e5458f510830eaa2c7a88414d9d35194420a6ae9a8ca21055673d4651082aab9ea32884117dcd64944208b8e6b24a21043f7458e510821e3a2c728841559cf5494420aaae7aa4a2107247255251082ab398a928841555cc5494420a6ce9a9ca21053574d4e510838b2a4a728841c55525394420e4aa9a14a21056672d9251082abb9ac928841551cd6494420c6ac8324a21056672d8e510829bba2c7288414d1d16394420caac631ca2104757690a51082ab39c8528841555ce42944208ecedaa2a21055673d5151082aab9ea8a8841c91c954544208ecec2a2a2105567315151082aab98a8a88414d9d35354420a6ae9a9aa2107165494d510838aaa4a6a8841c59515354420e2aa8a9aa210726541895108392aa0c4a8841d194c6254420e8aa6312a21056575d095108392aa684a8841d154f4254420e4aa8212a2107455310951082b3394c8a884155dcd6454420aa8e6b22a2105647259151082b8382c8a88418d5906454420acce531aa2105377458d510829a3a2c6a8841591c96354420ae0e0b1aa2106556318d510829b3a4c4a88414d5d26254420aace7312a21055573989510823b3b484a8841559ce4254420aaae7212a21072542109510829b3a040a88414d5d02054420aaae6102a21043d76950510821fbb2a828841879526314420c3aa9318a21061e5458c510830eaa2c628841175da5314420c3cc9298a21061d6494c510822fbb2a628841879915314420c3ac8a98a21063654984510831aaa4c2288419594e6114420caaa7308a21047776544510831b322a2288418d5915114420cacc6a88a21065563544510822f39ccba0841175ce65d0420c9aa7316821062e5458b4108326a9ac5a08419998951d0420ccac4a8e821045e73996410822eb9ccb208418b5526290420c9
  | 11 => 0x482abb9aa228a41551cd51145208bee6b20a29045c73590514821fba2c628a410f1d16314520c6ccbaa0a2904757695051482ab39ca828a41555ce54145208eeecaa0a2905577355051482aa39aa828a418d9945414520caccba98a29071754d4c514838a2a6a628a411d5da5314520a6ce9298a2905357494c514823bbb2a628a414ddd15314520a68e8a98a2907175414c514838a2a0a628a4155dcd6414520aa8e6b20a2906356419051482b2b90c828a414ddd16314520a68e8b18a2906556318c51482b2b90c628a411d9da4214520aace7210a2905557390851482b9b828428a415c1c14214520a6ee8b00a2905347458051482abb9ac028a41551cd6014520a6ee8900a2905347448051482abb9a4028a41551cd20145208bee6b2e829045c73597414822fb9acb20a41171cd65905208bce7b2a829045d73d95414822f39ccaa0a41175ce6550520a6ce3aa2829045e75d8d414830faa6c6a0a418715363505208bcea31a829061f5418d414830e2a0c6a0a41179db53505208b8eda9a829045e7614d414822e3b0a6a0a414d9d35150520caec7a8a829065463d45414832bb18a2a0a419518c51505208bee6b28829045c73594414829ab88a820a411b9d66210520c58a9310829064c5398841483162a2c420a419314d6210520a6ae82888290666621444148332b10a220a414d9d54110520a68eaa08829063665504414831a32a8220a41651cd4110520e2ea6a08829071453504414821fba2cb18a410f1d1658c52087ce9b2a629043d74d95314821f3a4ca98a410f5d2654c52087cebb22629043e75191314821f3b6a898a410f1db544c52087cec2a2629043c76151314831bb26a298a418d193514c520aace7a8a629063764145314831a320a298a410fdd1650c520878e8b28629046e7598831483162a4c418a418b151620c520aaae62886290666621443148332b10a218a41559d5310c520aa8ea9886290656654c4314832a32a6218a41651d1310c520e2ea89886290714544c4314821fbb6a990a410f5db54c852087eec2a6429043d76153214830faa4c790a418715263c8520c3ea8b1e429061c5458f214822fbb6a790a418799353c8520c3ac9a9e429045f7614f214830f320a790a418759053c8520c6cc828e429063564147214832b318a390a419558c51c8520ce0a3304429063854d81214832c29ec090a418e1506048520cb0a630242906735118121483162a4c5a02418b15162d0120cccc428e80906656214740483162a6c4a02418bd506250120c58a8312809047675d85404831baa6c2a02418d15361501208ecea30a809063754185404831a2a0c2a02411d9db5150120caec7a8a809065463d454048333b16a2a02419918b51501208ecec28a809065763145404832a318a2a024199d885150120cc8c428a8090
  | 12 => 0x90e419598e51c8720c6cc8a8e43906566354721c829b38ea9206410f9da5450320c5ca8312819062d5418940c831b2a0c2a06418d550615032087aedaa0819053671d5040c832bb1ec2aa44199d8b6155220c6ec830aa91065763185548832a318c2aa44199d88615522087eecaa0a91053471550548822fb9ac22a441171cd6115220a68e2aa685105a471553428831baa4c3214418d1526190a2087ced2a2851053471551428821ebb6a821441391c56510a208daedaa085104ad76d5042882d5386a8214416a9c05410a209c8e2b00851061f64d8d518830e326c6a8c4187d906354620c38c831aa31047776544518829a3a2a228c41551cd51146208bce7b2e831045d73d97418822f39ecb20c41175cf6590620c5ea9314831045f73595418822e39acaa0c4117dcd65106208b8e6b28831053571150418829a3aa8220c41651cd4110620b4ee4a08831043e74d96318821eba6cb18c410fdd1654c620878e8b2a631043f74594318821e3a2ca18c41551d5310c620b28e898863105c7724c4318829a3a2a310c41551cd518862099ce632443104ae7418e21882d23a2a310c41711cd5188620a68e8a8a43105547354521882563a2ca10c41331cd65086209caeda8843105e270d4421882f1380a210c412b1d16008620998e6b00431053471552408821f3b0a8a04418b150625022095ceda12811063754185408831a2a0c2a0441a9d08615022087eecaa081105347155040882563a2cb90441391c565c8220a3ce7b0ea89051d73d87544831bb0cc3aa2414d9c760d5120a6ae3b06a89063754986544831baa2c32a2419598e6195120ccac530ca89065663586544832ab1ac32a2418dd936155120caec7b0aa89066762d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544833830ec0aa2410fdd95415120a6ee2aa0a89053471550544829b38cc82a2414d5c664151208bee6b08a89045c73584544828fb9ac22a241471cd6115120a5ae4308a89063561184544829bb8ac02a2414d1c56015120c70a9306849063754986424831a2a4c3212418dd516190920c68a8b0c849063b5418142482ab39ca9a8a41555ce54d4520aaee6aa6a29055473553514838baa6a7a8a41c515353d4520aace7b26a29055573d93514831bb24c9a8a414d9d363d4520a6ae9b1ea2906576398f514823b3b485a8a41559ce42d4520aaae7216a29053674d83514829aba6c1a8a41559cf60d4520aaae7b06a29061f5498e514830e2a4c728a4187d516394520c38a8b1ca29061e64d4e514830eb26a728a418d9935194520c6ac9a8ca29065663d46514832ab1ea328a410f9db545452087cec2a2a29061f54d8d514830e2a6c6a8a4187d506354520c38a831aa29061f64d4d514830e326a6a8a411ddd95114520a6ee8a88a2905347454451
  | 13 => 0x51c8540cacc628e42a065563147215022fb9acb10a81171cd65885408bce7b2a42a045d73d95215022fb9aca10a81171cd650854087ceb32042a061e6414c215030eb20a610a818b9905208540c5ac829042a063664144215031ab20a210a81d814851d0140c5ac429480a062d7614a4050392296a320281c5d4c5190140e28a628c80a0727521464050392290a3202818d58851901408deeca90a42066552584521031ab2cc321081a598e6190840c6aa530c842063565586421034b31ac3210812d1c560108408bce7314a22045d7398a511023bbb2a228881551cd5114440caac6a88a2206656254451102aa39aa3a08818b9895290440a38e6a8c82205547354441102ca39a82208810f5d6621044093ce7310822062e62548411029abacc220881471cd5110440b28e6a88822053776544411031bbb2a220881c5dcd5110440a68e6a88822071473544411028a39aa2208814ddc95110440938e6b0082204ac72580411030fb288718881c510e518c440aa8e6a8c622046e721953110236b90ca988818d192514c440c68c8a8a622055473545311021ebaec8188812b9cb640c440c6aca2086220554754c4311032bb2a621888195595310c440b28e8988622045e73d97211022eb9ecb908819358e52c8440c5cc8a96422064d6354b211024e39ac910881551cd5188440c6aca20c422045f73595211022e39aca90881179cc65484408bae632a42206346454521102aa39aa2908818d5944148440e4aa420a42206b041181211021ebaec810881279cf640844096ce3b2042205367190a501021ebb085280812d9c662d004087eeca96802062e6254b401021ebb4a9200811e5da5490040b64e3214802062f65d894010317b28c4a00818b5d46250040c58c4a92802063765d854010352316c2a00818dd946150040d2ec630a8020694631854010353b10c2a0081a91886150040c6aa430a802066b65d894010335b28c4a0081aad906250040ce6cbb0a8020673651854010359b20c2a0081b81886150040cacc730ea9906666298754c832b31ac3aa6419558d61d5320cccc4b0ea99053671d5254c822fb9ac32a641171cd6195320a6ce3b22a99043f7655054c829b38ea9a16418d9526190b20c6aa930c859053671d5142c821f3b0a8a16410fdd95410b20a6ce9a8ca39055673d4651c822fb9ac928e41171cd649472087ee8b1ca39043c7458e51c823bbb2a228e4117dcd65507208b8e6b2a839045e73d9441c822eb9eca20e41179ce65107208bae732883905357195041c829aba4a220e414ddd54110720a6aeaa0883905947350441c82d83828220e410fdd1654c720878e8b2a639043e74d9431c821eba6ca18e410f9d2650c72087ae932863905557394431c82abbaa6218e41555d5310c720b28e898863905d0704c431c831b324a3
  | 14 => 0xe9b1ea2a06576398f515029aba0c5a8a81559cc62d4540aaae6316a2a04757690b51502ab39c85a8a81555ce42d4540aace7b06a2a055573d8351502b3396c1a8a81595cb60d4540c9ea7314a2a064f5358a515032731ea528a819358f5294540c9cc6294a2a064d6314a515032b31ea328a819558f5194540cccc5a8ca2a066562d465150327a9ec4a8a8193d4c62545408dceda92a2a064f63d49515032631ea4a8a811b9d85254540c9ec6292a2a064c63149515023bbb2a228a8155dcd5114540aa8e6a88a2a05677254451502b2392a228a81179ce62145408bae7310a2a065665d4c515023abb4a628a81599ca5314540acae5298a2a04777654c51502b3b92a628a81591c95314540ccccba90a2a074753d4851503a229ea428a81c9dd352145408eaed290a2a05567394851502aab9ca428a811ddd95214540aaee6a90a2a0554735485150333328a428a81d1d4c5214540e88a6290a2a072574148515029b3ae8428a81c5d4f4214540e28a7a10a2a072752d0851503922968428a81c5d4d4214540e28a6a10a2a07275250851503922928428a814ddd16314540a6ae8318a2a06556318c515029aba4c428a81559ce6214540aaae7310a2a053574188515029b3868428a811d5da4214540aace7210a2a05557390851502b9b828428a815c1c14214540e4ee4a10a2a073370508515029a3828428a81cc1c14214540aaee6b00a2a05547358051502b3b92c028a81591c96014540aaee6a00a2a05547350051502b3b928028a81591c94014540ce0a330482a045e75d8d415022f3a8c6a0a81179db53505408bcec29a82a064f63d49415032631ea4a0a8193d8c5250540c98c629282a065763d45415032a31ea2a0a8195d8c5150540ca8c628a82a066852d814150334290c0a0a819cd446050540b28e6a0882a071753504415038a29a8220a81c9d494110540e48a4a0882a046f725963150236392cb18a811b9cb654c5408dae5b2a62a062f64d493150316326a498a818bd90524c540c58c829262a063764d45315031a326a298a81559cf514c540c6ec828a62a0634641453150237b92ca18a811b1c9650c54087ceb32062a062e641483150316b20a418a818d990510c540c6ac828862a05557314431502ab3aa6218a81551d5310c540cacca98862a0654654c431502ca3a26218a81d1d49310c540e88a498862a045f73597215022e39acb90a81179cc65c85408bae632e42a045e7598f215022e3aac790a8117ddb53c85408baeda9e42a061e64d4f215030eb26a790a8117dd853c85408baec29e42a061e6414f215030eb20a790a818b99352c8540c5ac9a9642a064e63d4b2150326b1ea590a818b99052c8540c5ac829642a064e6314b2150326b18a590a818d99351c8540cacc7a8e42a065563d47215031b320a390a818d590
  | 15 => 0x94744c43108746b22c7908431b5da52884218eaed2944210d367494a21086ab39ca51084359dd54148421b8ee6a0a4210d67754c521086d3ba262908431d9d854484218ecec29a4210d367494921086ab39ca490843695d25248421b8ae72924210d657590921086e2b9c8490843c91514248421acaeb1924210da5748c921087a229a649084317dcd64940218b8e6b24a010c3f7458e500861e3a2c72804387d936354021c38c9b1aa010e1f6418d500870e320c6a80438d1922154021ca8c710aa010d7270885500871a32242a80439518d2154021ae0e090aa010c7b7654050086b338ea5296819598e6194b40cacc6b0ca5a06556358652d022f39ec2a9681175cf6154b408deeca90a5a05367194b42d029b38ca4a1681559cf5194740acce5a8ca3a062e6250a51d023bbb2a228e81651cd41107408dce5b2863a046d72d9431d0237394ca18e811b5ca650c740aaae728863a0557754c431d02aabaa6218e81651d1310c7408bce7b2e43a045d73d9721d031b324a390e819598e51c8740c6cc8a8e43a06566354721d02b2b8ca510e81179cf65087408bae7b2843a045e7399421d022eb9cca10e81179cf6154a408bae7b0aa52046f76548529034b31cc3214818d54a6190a40d2cc6b0c85206b2619824290256bb6a4214816a9c35210a40b54e029085204b47158042902ab39ea328c81179ce62946408bae7314a32047776544519021ebacc520c819518e5150640ca8c6a8a832059473504419029ab8ca620c81279ce6210640a6ee2a9083204b576d4441902cb39ea220c816c9c35110640b64e0288832049c735804190256392c020c811b9cb658c6408dae5b2c63204ae72d9031902aab9ca218c818d994410c640e2ca62086320557754c431902aabaa6218c81651d1310c6408bce7b2e432045d73d97219022f39ecb10c81175cf65886408bce732c432045d73996219024e39ac910c818d5925188640c6cca20c432056472545219024f39ec810c812d9c662d0240c5cc4a96812045f73587525022e39ac3a92814bdd161d4940a9ee6b0ea4a054c7358752502b338ec1a9281595c760d4940ccea530ca4a0667525865250237bb2a42928159dc55214940ac8e2a90a4a056671d9052502b2b8ec8292814b5d36114940a9ce7b08a4a054d73d845250296ba0c22928159dc56014940ac8e2b00a4a062f72997425031732ea5a12818b14a60d09408eceb30c84a0667529864250332294c3212811d1d56190940ccea4b0c84a0664525864250334294c1212819ad486050940a5cebb1284a052e7614942503173b0a4a1281aad886050940e8ea7a96a2a05567394b51502aab9ca5a8a8155dcd52d4540aa8e6a96a2a07475314b5150392ba0a5a8a814d9d742d4540e48a5a16a2a07245250b51502ab39ec9a8a81555cf64d4540a6a
  | 16 => 0x878bb9aa820a434d1cd5410521e28e6aa08290d1473550414869bb92a820a43c9dc95410521e66e0aa08290d34705504148798382a820a434c1c154105219cce53188290c757694c414869aba0a620a434ddd64310521b4ae52188290d357510c414878a2988620a43359ce6210521a6aeaa108290cd4735804148672392c020a43399c864cc5218eaed2a66290ce67598b31487333acc598a431d1d560cc521a38e8a9c6290d587054e314861fba2ca98a430f1d1654c521c38c9a9a6290c5e7614d314870e320a698a43651d1310c5219cce53206290c7675190314863abb4a818a43555cc540c521b8ae52986290c777654c314869a3a2a618a435c1c1530c5219aeeca986290d947454c31486e3b92a618a43741c1530c521aaeeca986290e577654c314878bba2a618a43551d1530c521e28e8a986290d147454c31486abb92a618a43d1dc9530c521ea6e0a986290d547054c31487a8382a618a43541c1530c521aaeeba186290dc572d0c31486aaba88618a43c5150430c52196ce93106290d55754c8314865a3a2c018a43391c9600c5219ace63264290e966498f214874ab24c790a43a599163c8521b4ce9a8c4290dc673d46214863dbb2a0282434e1d15014121ab0e6a80a090c5f73590504862e39ac8282430fdd16314121878e8b18a090d6672d04504871ab208228243599cb3114121caac6188a090d3674c8450486ab39e42282435c5c32114121c9ac7316a810e5663987540872ab1cc3aa043479cf54950218e8e2b1ca810d1e73d91540861fbb2a82a043175ce62150218bee6b00a810c5c735805408716b24c5a98438d99261d4c21c6ac930ea610d1e74d4e530868f3a6c6a984317dd95314c2187ce9310a610c3d74988530861fba2c0298430f1d16014c218dce432c8610c75751854308672b90c2a18431d9c66510c218f4e03288610c7970194430868eb9ca821843475d25310c21a3eeaa188610d1d7550c43086ca38a86218431b5d66210c218eeeab088610e1e6498e520870eb24c729043879916394821c3ac8b1ca410d1e73d53420869b38ea9a1043179cf65908218bae7b2c8410e1e5498e420870eaa4c7210438d9526190821c6aa930c8410d1e73d514208697396a8a10434d9c7545082187cec2a28410c5e73d94420862eb9eca210430fdd954108218eeeab088410d1e74d4f320861f3a6cb190430f5d3658c821c3cc929c6410e1e6454e320872b29cc3190439554e618c821a3ce9a9a6410c7775584320862fb9ac928843171cd649442187ee8b1ca210c3c7458e5108716aa4c520843179cf65104218bae7b288210c5e73994410862eb9cca208434d5d25110421a6eeaa088210d94735044108726a9cc5188430f9d3650c42187ae9b286210c3e74994310861eba4ca18843555ce510c421aaeea9886210d
  | 17 => 0x9c43471cd54d0e21a3ae62a48710d1c7454e438861f3b4a8a1c43471cd5450e21a38e8a9a8710e3654185438871aaa0c2a1c439594c6150e21caaa630a8710c3d76d50438868eb98a821c43471d54310e21c3ecaa188710e1d6550c43886ca38a8621c43395c66210e21a38e6aa68510cd473587428868e39aa8a14438d5506150a21968e8b0e6510d5473553418863abb0a7a0c434d5d053d0621a38e6aa48310d1c7355041887172a2c420c43651cd41106218eeecaa08310d547355041886ca39aa820c434ddd95410621c6eecaa08310f1773550418869a39aa820c43c51cd5410621a28e6aa08310d3470550418869aba0a620c434ddd64310621e2ca72188310d357510c418878a2988620c43695c843106219ace73108310c7775580418866a39ac020c43391c960106219cce43266310c757615331886aab98a998c434d1d153cc621a38e8a9c6310d1c7454c318872729ac418c43651d1310c621aaae62a06310d347454c31886ca3a2a618c4355dd9530c621caeeca986310f177454c31886aa3a2a618c43c51d1530c621a28e8a986310d547054c31886abbae8618c43c5953430c621aaaea2186310f145410c31886e2b908618c432d9d2620c6218eeeab006310cb4745803188672392c018c438b59664c8621c5acab264310e4d6598f2188726b2ac790c43a359163c8621c6acb3264310e3565593218866b398c990c439559663c8621d2cc931e4310e956498f218872ab2ac790c43a599163c8621a6ce990ca110d5673c8650886b8b8643284431edd95014221aa8e6b0ca890e1f6418d544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544861fbb2a82a243471cd5415121a70e0aa0a890c5f73580544862e39ac02a2434d1d16194d21c68c9b0aa690e3b64d81534871c326c0a9a438ed906054d21c70c8302a690e6b621815348739b08c0a9a4317dd95314d21a38e8a98a690d587054c534861fba2c029a430f1d16014d218f4e1b2e8690c7970d97434863d386cb21a431e5c36590d218d8eab148690c7b70595434863c382caa1a43399cb6150d218dae5b288690c7b70594434863c382ca21a43475cc5410d21a3ae82988690d1e7550c434868e3aa8621a43651c54310d21c68a8b0e8490cd473587424865a3a2c3992439514d61cc921aa8e6aa68290d707055341486733acc5a0a43999d662d05218e8eab068290d1c73552414869c382a920a4317dcd655052187cec2a28290e1f5418d414870e2a0c6a0a434d5c6541052187eecaa08290d1c73550414869c382a820a43651cd4110521b4ae52a08290c777655041486aa39aa820a435c1c1541052196eecaa08290d947355041486d3b92a820a436c1c15410521a6eecaa08290e3776550414
  | 18 => 0x494f21aaee2b24a790e1d6419253c86aab88c929e43479d26294f21a3ae9314a790d5571d8253c868fba2c129e43471d16094f21a98e4b04a790d577158253c86a7390c129e43479d36354f21a3ae9b1aa790c5e76d5153c862f3b0a8a9e43539ca6454f21aaee2b22a790e1d6419153c868f3a4c4a9e43475d26254f21a3ee8b0aa790d1c7458553c86adb82c2a9e43561c16154f21a3ee8b02a790d1c7458153c86a6392c0a9e4355dc56054f2187aed2a0a790c3f7655053c862fbb2a629e43879915314f21c3ac8a98a790e4d5398b43c87172a2c5a1e439354d62d0f21c5aa93148790e2d5458a43c872729ac521e43471cd5450f21a38e8a9a8790e3654d8543c871aaa6c2a1e439594f6150f21caaa7b0a8790e365418543c871aaa0c2a1e439594c6150f21caaa630a8790d1d7395043c868eba4a621e4347dd54310f21a3aeaa188790e1f6550c43c870eb2a8621e43651c54310f21c6ca93088790e565398443c871b2a2c221e439594d6110f218baeb31c8590e1e5498e42c870eaa4c72164317dd56390b21c3ca8b1c8590e1d5458e42c862ebb4a72164317dd95390b21c6ca930c8590e355498642c872b29cc3216439554e6190b21c6ca8b0c8590e565358642c872aa9ac321643c354d4210b21c6ca93088590e565398442c871b2a2c2216439594d6110b2187aed2a46590c3f7655232c871b2a4c3196438d552618cb21caca730c6590e365458632c871aaa2c3196439594d618cb21c9aa73168390e2e5458b41c8726a9ac5a0e43175d76350721c3ca9b1a8390e1d54d8d41c862eba8c6a0e43879506350721c3aa831a8390c5e7694d41c862e3b2a6a0e438b5536250721b28e6a088390f165350441c878aa9a8220e438b55262cc721c5aa8b166390e4e5358b31c861ebaec898e430f5d4644c72187ced2a26390c3c7655131c870fb24a698e4387192534c721c3ec8a9a6390e1c6454d31c8726a9ec498e43651d1310c721e2ca89886390f15544c431c870f2a4c7a86438755263d4321c3ca8b1ea190e1d5458f50c870f324a7a86438759253d4321c3cc8a9ea190e1d6454f50c862fb9ac928643171cd649432187ee8b1ca190c3c7458e50c861ebb4a8286430fdd95414321c3ca9318a190e1d5498c50c870f2a2c6286438755163143218baed298a190e1e6494c50c870eb24a62864317dd95314321c3cc8a98a190e1d6454c50c863dbb2a02864317dcd60952218b8e6b04a910e1f6418d548872bb18c2aa4439518c615522187eecaa0a910d1c73550548870eaa2c62a443879916315221ca8e2b18a910e4e63588548872ab1cc22a4439958a611522187ee8b04a710c3c74582538870eb98c8a9c438dd906154e21c68c830aa710c5f7654c538868e3a2a629c43875915314e21c68e2b20a710e2e64588538871ab24c22
  | 19 => 0x43226218cd670191310c6cb3b0c898863a59d8644c431d2eca3226218f1765191310c74bba8c898863a55d4644c431d2ee43226218e9672191310c74ab90c898863a51c8644c431d2ee03226218e9670191310c74ab80c898863a51c0644c4319acedaa26218e9464d51310c6e3396a898863715cb544c4319a8ed2a26218e9464951310c66bbb2a898863351d9544c431d28c8aa26218cd676151310c74a320a898863c5550544c431d2ec9b126218e9464d89310c66b3a6c498863359c3624c431aaaeb3126218d9674989310c6caba4c498863a5192624c431aaeeab126218d9774589310c6ca3a2c498863a5d91624c431d28c8b126218dd370589310c6e8382c498863a5190624c4319aceda926218d9674d49310c6caba6a498863a5193524c4319aced2926218d9674949310c6caba4a498863a5192524c431d8ec52926218cd676549310c74a322a498863b1d89524c4319acec2926218e9464149310c7a2a90a498863351db424c431aaceba126218d5575d09310c74a3268498863359da424c4319aaed2126218d5675909310c6aabac8498863a5192424c4319aeeca126218cd476509310c74a3228498863359d8424c4319aaec2126218e9464109310c74a326c098863555d6604c431b2ce93026218d9574981310c74bb24c098863a5192604c431aaeeab026218d9774581310c6ca3a2c098863a5191604c431b8ee4b026218dc472581310c74bb20c098863a5190604c4319ace83026218cd572181310c66bbb263a8063651d131d40319a8ec98ca018d94744c6500c6e838263280631bdc964940318d8e4b24a018c3f7458a500c61e3a2c528063c510c41940319a8ec98aa018d94744c5500c74bb2262a8063a51913154031d8ec498aa018ec4624c5500c6e838262a80638bd936254031c58c9b12a018e2f64189500c716320c4a8063999c46254031ccae2312a018cd7764c4500c6ca3a26228063a59913114031d2ac8988a018ec6624c4500c762b1262280631edd95014031cacc6b0ea990e556358754c868f39ea92a643475cf54953218bee6b04a990c5c7358254c8697396c72a6434ddc56395321c3ac631ca990d357118e54c868f39cc52a643475ce6295321a3ee6b0ca990d1c7358654c869ab8ec12a64347dcd6095321a38e6b04a990d2c7258254c869bb8ac12a6434b9c86095321a3ce7b22a990d1d73d9154c8697394c6aa6434ddc56355321c3ac631aa990d1e7398954c868eb9cc4aa64347dcd6155321a38e6b0aa990d3b7058554c869c382c2aa64347dcd6055321a38e6b02a990d2c7258154c869bb8ac0aa6430fdd95415321c3aa9318a990e1d5458c54c870f324c62a643879916315321c9ac7310a990e566358454c8733312c22a643479d35394f21a3ae9a9ca790c3f7458253c861e3a2c129e43539cb6
  | 20 => 0x57110c418c6ca39a8220c63595c854cc631c3ac821ca118c3e74189508c61eba0c4a84631edd95014231c5ec5316a898d357118b544c697396c1aa2634b5cb60d5131a6ae3b06a898c3f76550544c637b92c02a2631b1c96015131a6ae3b10a898d3571988544c716b10c42a2634b9cb6115131a5ae5b08a898d2f72580544c696392c02a2634ddc56015131a5ce4300a898d2d72180544c69ab88c02a2630f9d260d493187ae9306a498c3e76d51524c61f3b0a8a92638ed536054931c70a9b02a498e3b54181524c71c2a0c0a92631bdd95214931ad0e0a90a498c3f74580524c61e3a2c0292638d15261d0931c68a8b0e8498cd473587424c71baa4c3212638d1526190931c6ea8b0c8498e3454586424c66a39ac3212634b9cb5450931a5ae42a08498e1c5498f414c70e2a2c7a0a63871536350531c3ea831a8298e1c5418d414c69a3aa8220a63651cd411053187ce9316a098c3d7498b504c61f3b6a8a82630f9d85454131c5ea9b12a098e2c54d89504c717aa0c4a82638b15062541318f6eca80a098d6872540504c61fba2c4282630f1d16214131ccac530ea818d2e72d52540c697396c8aa0639518c615503187eecaa0a818c6f72580540c636392c02a0634b9d35294831c58e4b24a418c3e74181520c61eba0c0a90631bdd95214831a5ce5aa68418d2d7494b420c71b2a4c3210638d55261908319aae730c8418c7b70595420c63c382caa10634b9cb545083187cec2a28418cd573185420c61fbb2a821063355ce6110831acae5aa68218d5575d8f410c6e2b90c7a086335dcd62d04319aae73068218e1d5498e410c69abacc820863595cb5410431a6aeb2a08218c7776550410c69bbb2a8208638ddd95410431e28e6aa08218d3772550410c69a382a8208631ddd563104319aeeab188218e577558c410c66bb92c620863351c16310431caacba188218f1554d0c410c69bbac86208638d5964310431b2ce72188218e956390c410c69aba886208638d5944310431caaca2188218f166510c410c74ab288620863c55944310431c2aca2188218e9443588410c78a21aa4208634d5d74210431e4aa5a108218d3575508410c6ca39a8420863a510e60104319cae43246218c757694e310c74b3268718863a5190438c431c6ecbb226218c7575991310c65b3a4c8988638dd94644c431d2ee63226218e9573191310c71a324a698863a5192534c431d28c9a1a6218cd67690d310c74a3248698863351d9434c431d28c8a1a6218e946410d310c72abaeca98863359d3654c4319aae5b2a6218cd670d95310c72b3b6ca98863a5d97644c431e2ecbb226218d5575991310c6cb3a4c898863355d6644c431caaeb3226218cd674991310c64b3a4c898863355ca644c4319ace13226218d5775591310c74ab20c898863a59d0644c4319aae
  | 21 => 0x6cb39c84a0883655ce4250441d28c72128220e94635094110753b1284a08832d9d84250441d28c62128220e3575d95411065b39ecaa08832d5cb655044196ce1b2a8220e3676d95411074bb2ec6a0883c5d976350441a6aeb31a8220d967398d411069bbaac6a0883a558c635044196ae431a8220cb67018d41106cb3b0c6a0883a59d86350441d2eca31a8220f176518d411074bba8c6a0883a55d46350441d2ee431a8220e967218d411074ab90c6a0883a51c86350441d2ee031a8220e967018d411074ab80c6a0883a51c0635044196ceda9a8220e9463d4d41106d3396a6a0883695cb5350441968ed29a8220e946394d411065a3b2a6a0883a518d535044196cec29a8220e946314d411078aa98a6a0883a5d8f6250441d28c7b128220cb673d89411065b386c4a08834d5d66250441b2ce73128220d9573989411074a31cc4a08834ddd56250441b2ee6b128220d9473589411074bb1ac4a0883a518d6250441b66e0b128220db070589411074a318c4a08832d9db5250441b2ce7a928220d9573d49411074a31ea4a08832d9da5250441b2ce72928220d9573949411074a31ca4a0883a9d8a525044196ceca928220e94635494110753b12a4a08832d9d85250441d28c62928220f2552149411074a31ec0a08834d5d66050441b2ce73028220d9573981411074bb1cc0a0883a518e6050441a6eeab028220d977358141106ca39ac0a0883a518d6050441b4ee4b028220da472581411074bb18c0a0883a518c605044196ce63028220cb572181411065bbb283a8083651cd41d4041968eca0ca020d947350650106d838283280831bdc963940418d8e4b1ca020c5f7358a501062e39ac5280832d1d94154041b28e6a0aa020e9763505501074a31a82a8083a9d894154041d48c4a0aa020db0705055010727b1ec4a80839318f6254041c9ec6312a020e4c6318950107173a0c4a80838b5d06254041ccce2312a020e6571189501061f3b684a80838718f4254041c58c5a12a020e1c63509501071631284a80832ddd94114041b28e6a08a020e9663504501074ab1a8228083a99894114041d4ac4a08a020c7b76540501072ab1cc3aa4631bdc960952318d8e4b04a918c3f76550548c716aa2c42a4639358e6215231c9ae7310a918e2e64588548c72ab1cc22a4639958a6115231a5ae42a48718c3e76951438c71b2a0c2a1c638d5506150e3187aedaa08718d2d72150438c62ebb6a821c63275db5410e31b2ce3aa08718d1d76d50438c70ebb6a821c63475cb5410e31e2ce3aa08718d1e70d50438c6c6b90a821c63659c45410e3187ee8b04a518c3c74582528c70fb2086a94631bdd95214a31c5ac8a90a518e1e6510f428c74a21cc3a1463351cd61d0a31c9ac72948518e4d6354a428c732a94c321463c310d5250a31c3ca8b188318d9
  | 22 => 0x859598d6194842caac6b0ca42143d769524210a36bb4a921085b158d6190842b4ae3b22842155673d465110a3bbb2a22888517dcd61940428b8e6b0ca02153a70d095010a9c38284a808595d8f6154042caec630aa021654631855010b1ba10c2a80858d50861540428f6eca80a02146f7258253d0636392c129e8317dd95314f41c9aa6b10a7a0c5f7358252d062e39ac1296831bdd95214b41c9ac6a90a5a0cd47358742d062f398c4a8683175cc62543418f6eca80a1a0c6f725825390636392c129c8317dd95314e41c9aa6b10a720c5f73582529062e39ac1294831bdd95214a41c9ac6a90a520c9c735874290726b1ca5214839358d5290a41ccaa530c8520d2e7694942907173b4a4a14838b9486050a418bce6312a120c5d73189509061e3b284a84831edd95014241c9ec5316a6a0d1d7418b53506aab88c5a9a83475d360d4d41a9ce5b06a6a0d4d72d8353506aab8ec1a9a8317dd95314d418dee4b00a6a0c6c7258053506a7396c829a83535cb6414d41a3ae9b10a6a0d5571d88535068eba4c429a83555c66214d41c9ac4310a6a0d4e72d8453506a6b96c229a8347dd16014d41a9ee4b00a6a0d4c7258053506abb8ac029a83475d06014d41a9ce4300a6a0d4d7218053506aab88c029a839514e6190d41caea630a86a0c5e73983525062eb9cc1a9283179db53549418bcec29aa4a0e5b53d81525072c29ec0a928396d4c6054941cb0a6302a4a0c6f7654852506b4382a42928317dcd60149418b8e6b00a4a0c5e7598e425062e3aac721283175db53909418baec29c84a0e5753986425072a29cc32128395d4d6190941ca8a6b0c84a0e6752586425072a29ec2a12839514c6150941c5ccaa1084a0f0f53508425062f39cc5a8283175ce62d41418bceda9aa0a0c5e7614d5050727a9ec4a82839314f6254141c9ea6312a0a0e4c53189505063dbb2a0282835a1c950141418bee6b10a0a0c5c7358850506a7396a72988317dd95314c4196ee2b148620d3575d8643106d2b90c3218832d5c66090c4196eeab088620e3775584431065bb92c2218832d1c16110c41a9ce7a94a420e5663986521072ab1cc329083179cc60548418bae6302a420c6f76548521066a39ac3a1083479ce52d0841938e6b0e8420d9473587421065bbaac3a10838ddd561d0841d2ee6b0e8420cb473587421074a39ac3a1083251cd61d0841968e0b0e8420cb57118d4210697394a6a1083479ce5250841a6eeab0a8420d947358542106d8382c2a10832d5c4605084187aed2a48220c7576952411074b31c8720883a95894290441c3ecbb1a8220e1f6518d411074bb88c6a0883a55c46350441caecbb1a8220e576518d411074bb20c6a0883a5dd06350441d2ca831a8220cb676d0d411074a31e86a0883a518e4350441d28c6a1a8220e9463d094110
  | 23 => 0x10000000008002003001400a0000008020000004001800c0000160000038000001000001001600100080040000020008004000001001000800400400080000040010000010020000001001000000200080040020010018034014000001803801a011000001c008011000001c00600300100240020000148000000000000002c03600200700000060050048008028000005000400200c0020004012006009800c00a004000000000c00600300000020000008020000002000000000200900f801800400b00180040000010000024006000004002800800300300040000000008000002005000800000000300d001400200000280000000060050014002004001001000401b00000c400001200300240020050000008002001001000000000800600100060000000008002003000801800600700000040040010000024006000000800c002000005802c00a00d001001001e000002000000000000080080000000018004008008000000c002004000000400c003000002400400500100200000040008000020003000000000600d009009c000000004000400200e00100100000000008024000007006000400200200000000000020088048000001001002800400100000000b4000007005800600200180040060020008000002008000000001a006000800001600400000140020040028000004007000800001e015000802c010001002000004800b00100300080000000020000004009000801800400200000000060018000002003000001400400500100000000028bee6b04a3a145c7358251d0a3bbb2a228e85551cd5114742caac6a88a3a147b7654050d0aab39ea328c85555cf51946428bee6b04a32145c735825190a9abae8528c85c594f4294642acaeba14a32156672d8e5190a9bba2c728c854d5d06394642caac631ca32153670d0a5190a9aba6c128c854ddd16094642aaee6b04a321554735825190ab2392c128c85599c86094642a6aeba12a32171653d095190ab2bae84a8c85d154f4254642aaee6b22a321554735915190ab9b82c8a8c855c1c16454642acce531aa3215377458d5190b2ab18c6a8c85559ce6254642aaae7312a321537745815190aabb9ac0a8c85551cd6054642ac8e4b02a32145d7694c5190a2fbb2a628c851ddd95114642cacc6a88a321655635445190b2b31ca3a84859558e51d4242cacc6a8ea121655635475090a2fb9ac328485171cd6194242a74e1a12a121475769445090b2b31ca2284859558e51142428eeeca88a121656635445090b2ab1aa2284851edd95014242d2cc730c84a16a7529864250b4b31ac3212851ddd95114542aa8e6a88a2a1570705445150a2fb9ac028a85171cd60145428f6eca80a0a1570715405050a9b38c84282854e5c242141428bee6b08a0a145c735845050b2b31cc329
  | 24 => 0x1403800b00480400000050000008000000006000401c016001000c00002b00100080000000028004004000000800000402b0018000008000000000c0000000018008032001001000c0020060000000000000006802400000600000000000080008000000004000803000a00f000800c00200900a00200020080008010004010001801000000100080040140000000008000000002801000c0000008010004000002800401a000003805c00a003001000400000b0000004004003000800001e006000002c000000001001000200d001002800400100280040000000010000002001005800c00000100a003c002003000800c00600100000000000110078000002000001001c00c002004000800c0060000000004000000000000a000002000c00800300200000000010008004002025000807000c005003800c00e0000020004000003002001c000013003800000e000000000400200d00080000060010030060008001002002c00000500000400100010000000006000000000400a003000800c002005002801000000000180000000000008038016003000003c00e00f006800400400e000000c000000004803400000300400040020010018034008004002001c00600200180100000030000014008000001000001c00000e800400a0070000004004001003803800800200000080060000060004016000000000400400d00180a80000000020000010006000000000e004002002000a0010020004004000000000c0020000030000000000001800c00a00300080000040000020000010000002800c01a0020048010000012000001000c006003801400000000000080080030000020000002000000000000100180100060090008018000000002000800400300400080000000000000000000000001c01a00500d00600000050040004000002001800003400100180240000000030000006002000803c00000000180000000000058020000002000000001a01200000000020000020008000008001000c00600b0000008006004003000400200e000801400400c00080000100140008024018004000001400a0000010008000006000000c0040030038004008007000800402600700380100020000008020002000000001800000d000000000a0080018008026000002801c0000010018010008005002800000e00000180080020020000004024000004802001c00000380180000060010008000031000806400000000b80040040000028000002000009800000200d001001c00000f006000c0000060000000000000008000402800d000800400400100680200000040000008006014003000000000700180000060050018004002002006000000400e003801c00000200000040000000008000000008000800000200100e802400e006001004401000
  | 25 => 0xaaa2268e854a0000000368da94c32602033d7aa732c98976200071200037a17e66d824180000000005f793c4f848240000000000c510000000000000171a0a4000e4d79f40018790000001524000dec2e8800197600039854c91f60000d38002004002000c02200400000440040010000008008004001004c00400300180080000010000028010004000001801000100000040040000018000008000003801000400d002806400800200000000020010040004016002004000c01c002003801c000005003002c0160000008020022001005003400400200a8008002015002000000000200080000000000060004000013000800400000100080000000000098018008046000800800000400b8010002000000800800e001000000000200000000240100060068004000001002800c008000000000c000000004000000a0000018000000001001001400000000000040020010000024038000000800c0060010008000018000002800c0180010000000002000003801c00a002003800800e0040008000000004007800000000c000802000600a0010020008010001000c000000002800c000000008002c00a000003000000a00700000040020000008074002012000800000c0080038004004000000803400800200180000040010038004008000007000c04001c0000000016003000800801800000280080080000008000008004002000001001400080000000010038010054001000000400c007000800800c0020020040014000000002c0000050038004002000000000000000d002800000a0000040014006000002000c00a00d001800400001500280380080030048000000002000006401a00400000040000000018004000005001801401e0010000028006000000800c00000000000180000020000008004000000001400000100180140000060078030010000000000000200200a004000a000000001c01c001000801000e01a000002800600000800000040000028008002000000800c00c000001000000001a0010000002000000800400a00600680080040030000004010001001001c00000300000080020010040024000004000001000c003000001c04200000200140040000000038010000001809c0000010068020002000000000001201200200000000000040000002000007000001c0020008018008003000001400400d0090004000002000800c000007000000000600300300080080010010004000000001801801c004000000400000200080040080000008004000007001000c004000005801000000300600080040120030004008000000000c02c0010008004000001000001c01600e001003400000000280000000020000010012013000800800000b00000100000000000000002016003000400400200c000c00200400800
  | 26 => 0x3b6000025f34b0b6cac41bb1159311671c003219f30c985d9682278400053f437c00000000010b80016d2f4700f929cd804563b507ec508ed000000000003ea6d680009fe0004201dc92901eeb9620760000b16c8b8b8000e1c0003028931c1d56012a03a4008529819043e0006f3103d32f0000660dbc0000d30000000eac00000000013e44001b08583aa804a6b32fd11c05b6f3c0a8481c5046e8a1b53c35c72c51cf000050f8000000000000447a9a9d0e5180d99afd616b1900028fd622b264130000d57b1f1d334fd5b6dba4d0f6c9de658c0da97ecb440d64ef8869a341852ebdd04eec6c42650b8588ee6f1ac2f58ebeb1b00006d8000c660003179214dd4b62b4fe0000000000f6400000000000002f454300025c959c0b98001dcc000b9d00000000000000000000c1cd568000001e88c366bb800000000000006288f6000000217467c00000000000000004ce4000000b490000001e2ea037990e14995e7c76380000000006730000f8de0f596813f102e3720896947ec0e85864db5e843fe83a2a1960e06f1f32d74ce87fc80f22fdb764d12fec7f909ab47320a7b0558a9f72c9bdc8a49d51b885118427262901fc8a44d59578bbc09ea6b3082057d3346a93d1a5150ca509257308cd2880b000095c0009b96be846c10da6125b824c098d5819db0cc4b8cba231995c000b9500027cb5f70004e13c62490098c158d7d17fb6a57c98a925e0007a18000f690004d326f576000038f9fbd2228171f384f6000a340002b0ce0e07fd1abc6c80a0001d200000005810fe8c849681cf2101e443b23a943b1c5e000c2a432f62000097d55c73c14960001e880004eedbd4cfc3bb65807c03eee9174c93f45a00016a79805d88000f3a8e74e7ee441a039e63d81b1ab69347673b0de87eb1297b53200094e088367457875c546a6679626480000001932f1900000006a40002f1507132eefc0000ebc9cc00059480010ac0002dc000103779400002b4d3b2a84dd33ec1de00000002f4000ea25b300015fc00039ce5fa686a1b5b3b1a9bc40000000000c970000659ab4000f3f014b51e000ef500000000000000000000000af1ab602f34d209517db94167f6f4747c00171151e25bc000a8c0000002b889525850a5a1b80000000b4065da5134838ea2e000061410f090dab88a92600000ee20003cb80007cb00038680000000005ee80000009a900000000002991f19a3000048a05db67736e0007103c7c0002d1e03309011c8cf1e63588e9883050a09270c09478000f1dc3a52c221336000037d1a237404040df04c11298c7000000116d4aa1b1581d71aa06ca67529d5c000f3e00008b8d9ad8000004895ea8545ccc6c800048f00001a88e49742eac00144a9cc000000000066b39eba812d026a398303950debe00010760000005290e740
  | 27 => 0x12300073680018a098516fbb09ac86311860200f4063507833409e86a4556972576412f56dee9dcb80001fd121800000000016780000c185abcb5e9260043ace807aed9257000002fc27e3a223dc0002c54eb4001dcc0001b40000000000000000000000031e0000000185cf7fc800000006a75940000d6480000011bf6a9b032018dbac2234da234fea7823802d6d472889000241ad3e00000007e897800000001cc000c383e0dc1600078000013d8000c3a0d203d99d0888298129ea3e000775000169ca1137db7d49f8dce363a99c00038841b2d3c000000000000138b0000001c90000f26785629aee18e15d84532000a9b8000001dc861317640000006ba76a9430000c292f32032000a95000255c00000000000016b230274c86bc000b0a458b52d6f02ca0001a180005faa308001a53a828000000000000736000000000000037a82bf0001201f11aceeb781f6a10cce00068e800000045d1b52590b7ab550000001e2600050f92d33620004899ee10ceed26fd8001cd20000265e480004cd0000000b71000000252d010cc60002eae000ab60ea282e1aa000000343ce3fd344fe0000000b370000d25530a1a0000000ebc0000003a18310a8c0002e2d81e09e3aea15d62a8c25af00000000000000000cf8000487b5549f2000538800036ea7256f11643c2a7ef218000d8c00000019a4942119ee000000003960000480000f23046af6db5002b2b98b0032a84a1a82080e5ae9b42f1879bc8a9a59ca42c15935e6ea1a3c4f606222300000007c58d18b0a13b0000000000c7c00000012c8000d0903800019d80002352d90000a7480001c4000a5600031115ca1ec0000000000e0a0000644000e5300020583ea6cc80000003e400000000008c0000000000001600049117fa3402aa2b680000000000000001d525ee48e2b60000f0c000391d004d704fbaf200003c84e743e8bac0000000000000156442b8d80000000d407fc0001510aadd098a816c5a98f28afc22710c1eceda8bf218df4e0f5ad8bdf71e7ca9cb4b0001ecd3ec00035095bd4ca2e9533324c166971000000000019358906b17d67862771fa82d25f293228800003bf11b8aec85363037b57e6a02cd51f0a7f900598d45bbbd000aea4351ace93dc0003ce137d4450003adb1f8d7a31580000000000003eb00000000000002a097ae5ff0000001c9618d11ea304000137cca5e2842400056e8c78000289800000087888668722ccbef4ed0390252bc6b180442375d50d7529bbab9c0200045510d01dc6a8b02b3d19945410001eff85821c1c32b4185a0000f2b04123e74280024f1824000000000000028c0000000dca00020480cc488000000000006800035c800150e255000000110841e5e900005a00000000000000e6500039c980a2b2f5981e000000023fb6559824890
  | 28 => 0x98c030800000085a05a12cc00062215c2742d26c620f8821d6200157a63878e5390236fa07803a6290001394ca400031392540000003de125058400000033300007cf000000037d7cd9b2bcd0000bf9000363800000015f97c40002620002cac4940ea000346d46c15b80029f8ac00007481ea6d4e11d0249bf400000071a3bec00097d80035ec000a273a30e490420dc5e0800000097b45a40017fc00000000000000000000001cd100017b8001cc40005668000000df46c0a610c8e0c34a74001310000000000000054c800342d564eb046c80000000e30000000c0260a00000000005920000000000b4120cb8a457bbfef701ba34cb0000003a0133a42763e8a89d22d0532703b43e30000000838dd0ca53658000e32a8ab9be0f00000004fe66d9b38844000000000068e0cd08a19cadde71d2904000a234f7800120b15a000354cc7a00030830ac0000000001f600007358003ce0e12d602d9b0a1a4ee760a0c5bcace23845c42f0000e660e00f144527498bb13dce2e39a00014640000000001508420da119496502a700000000000000005750000f2c000000142954b00050eab200000004e0a188000a80b640001b9700000021a4a3a0004d04000000a310d283fde1441ce793b34e689b308d00000008af80009b4000140236ac5c00000052600015b15580003181c5400036ac0000d500030ae75d5fe2dd27d25fc0f2701000000140273e000050c76800059a0000000f31000000030400000020e897c91400004f819a00001803dc0006722c02e104a800062e08fe0000003f2800099000058252e4b610000000f79b0600000000000007330003bf47280000002fd2498000608997d0534a18000000000dae0000000da600033717c8e1c3c678e8000000000380caac0001f80000000f8704657a332c6f882f66d1cb800000000010ad66cb2e3e480010f3d3cab300b80000007408000a201d850cc00000037000000012be00033e976758804736d02ac20d9ea1419b98983a5a52cb71e000edd40acd896ea041235acf4c9edf05840ad89ae63b0001c4d7b0068476b408e54e88dae1cbac7e64269270fc000ee829880005480005a00000000a6d6e2a4641a23f44d0bcdc7f900071e1eb8e4e39802565bc2b000063d124554e180537000000000079066259a8d2314085f41b2c3e55e30f10386fa400a44800000038208f93470000001caa95488b24ea7b6af45299e73a3d0b64c958a0000c884a03fe9b8bdb20003ad0bd40006b04fa2e815d8b8235fc0015f8cab00000001bc58879e00000000001fee1d05f83e78001fa40000006cc9351644aae9df017dae7020431bb9521c000351183d3d0effb81bc10f2a96b00025e025a80180022a732000000000000003310000000f1601900020a20006490000cd4
  | 29 => 0x800055b0908aa45ec0002f299d40008a67180000f807626a1934800000054c8b04000b006888771952a060000bd000000014b8000000000000000055c0a5112800093ce60599000000019b0003af06f4c70427901000024f000114c000274000000000048800000000000000000000d7c0a70000f91d563375c1a8f5ad4101000157501cd5618d0001bbbbe93c680000001b40000000dc050236f0001d881636b60dd427400015694e400056336180011404ac00000000000004c8af07a717d9000051400060d0651f4423827f5218eec818000000000097f09455c279d3b642c01282a84160000002b5d01acbe000000000000000032504dc4fe4d407832061554b9d774edc0004fdaab8fd8d8400023344f4bc456490500000003e40001029c5b47d170b1d88a0a3e1b5ca1a11965239d1e1c68b4feb858976b8d681b260000c4f4b8cfe0b3484c03a4000bb40002ea0001e946ae746d85931b6eb03940400002a60000000e31b960001dba7866ed000277ac2e3b12bb0001c7277900003800005770001cb200055a6011f8400015b0000001a3c4db781030885c0000000000462cb2212a21c2f03d570036613acd4c4563c9b67c0a06fb22ced2a33a01900015f02cd04c800000054f5dd93a96049f14cb12654c42696e8debc0000004d10000000b9e69927cf38c10928322494d8eca4a6b48a0003902522fa91dc9d3c4aaa2840ee3b532373042c723178bcdbd2e00041272795d200000013c9bf4c3d00001fc02600018907ad7b800000014b40002886bc927c00000000017466758b900007804ccc435fb0eac560f284228550900246d5f0591ba6a76ad490e8000000000000129165d5d1a901aa901a0c8000000000000037101c200056a01d60009510000000ff25af6f1a2b9a554d922c1680c931842f607bce6e5f62222ea4ab89611e848b5a2af154ea05652aac597021a0820a2c746600001ad954304818d1143d80003129a0e0002d4f6dcce0aeb0003b5951290c000205a2d40000001e95b4d00078ad5280003fb46bad880000000002484000d3080033dc0007025d70000142000149ba080000002908000000d495a234d62d6805131800000000047e8001b9b00061391c5b0c00045d0000a6c00011236d96fe0007358a70000000000000000000058e125972600000000000004971a26d68000000026b5780002d46d98f00708f35b61337d4d0c3945f27219dc1b02200000e0500024703c48be0002178719cbf0003751054000e4e5809bf04c008c000000000078f01302410b8b544076dea5a40006e7923471c13c01896096f694200005c0000000706000037c6210000e956ed72940aa6bd032e2516b1a4824c5683dba3e031e00029bc4e3898f2226f080701400000019500000000000001a4f0000001f26c7000044013a509055e
  | 30 => 0x5000000000000000006b400000000004c0000f4b00000000008dc00020113700004a7bbd60009c315e98698be00000000008f20005134000000cbf00000000000000001540000728000000000083400024ece19ce923a3c7b3786e904b0000000914e12b0d497706e790800000000034c2d85e0e69c3266a4601c12c000090800095a5512be9cc5cc358f1a64a68eec648860fe06868000172cfe600025c0001def0004af39480003190000000ca27ff8001f0d5e5585af10cf4000d1600031a00000007678c8800068500020baaf600000000012cee18006e791cb0bfa000076d6810002338585ba58d80002d1823c00041c80001900000000670000325fa323a918a4545aa4000a2ea2f2ab9fdd0de3463f8c0004e20000002f38000c771340fd4000c64d001c9405e4556c626b16dac3880021aa0002f800000005140002f66934c3a00000025996fc0003ea800162c46c74e28e97028d400034b062a41b0001ce055eb9a00017f089600900032000004a675e8e8ccee78100000010b2b7a3ef082000000000025a80004a6cc4c205c360000001b847ee42a000000062c0005da00004de0005ca00000000003320001d34d3d30d8f35b1977b17fb4f67a85c6488762de487a27211935853dab2ee11dc1678c4176800130632661321d200000021dbb18b4b5bb2181c19454d7448763e50f200000009640069a303392e316c112ad62eea00029b0800734000bb82b500012f1092075ec75b7e000361400002c5c5265814171043e72aa2315c64b544e8d9dc88b70209b951b7547a788f8a1096691391462d640bcf53ebcec49a7ac047a85c65a9ca5dbb020c3069d4633191c1c6594b1278c051aed46d3844698b0e284078c3615d05050e6c864ced451e8ade720ba4498142b2e1e851e249899e43722727e0f6877e5f3bbb56f816200013180000003d397164120000003b258bab13671abb89bab85251a19b3fe8c057d6388b4c3806809490a78db11a013ed9de92d55c84516d06e49479514b0e0005cda1904ba9436ec22380002cf71917ce6102474cf9c2dac616e107a31ac5000008503d0beb7d400000000000f513c273cf9600000031737ea6e30861ef8ff019f6900000bbc0b60000fa0fb8000629108d12e30b2f8cb440000007380000000000000000186839f32d969a0000000e80000000a1600017e40005ae00000010c98ff53b8a0000000028a2ffd2090d580003481cb952b23c49159eae665e1ab000000000000000004289a8b465972022022b7e0c24208c69a1f8000a97257a81cb364ba0001fb8000000083055c41b0000001b3cec25db85bc0000000005b00969e5e2340001ec80005e141dba340007f0ed5000000095b0000da5766a833c625e461c87835dade5be22c81db387c3940001953d3db1fb570002003d900ced5a225
  | 31 => 0x370d90000000000000df20003a8c000caa0000000f320003d809d8bde0006c140000fdbe52760000000000000000000005b0000000af80394ac00013ccc8a0000000cda0004bd0000ffc64637fe971de96a03c4924999016d084c00000076000003ce926df90000001bb40000002cbc00000000000000001b900000000000003d86479e9a000000323400000000010b4ecc0000002bb6000000052000000000000000000004c50a31a203180001db983e000d364c73c0171c3ff36940000a48ae8000000000000591800120a44c59ab1fc6ac0000000000000000000000000046821994440008ca6a28000281e07692000000099e8002394ecd000533c0016be2eb0001feb74490cf41b19c000000000088c152e104308001830ebf60380013e6c190f51d354f2000092903513274f5ac0000c80de03855f35a5772bdc380010a24d300029398827fd800204648cc205f0800058c25e1002312ee83b50001d64000bc3f7c00004a2000658000000069a40f6ccc25200017400000000000000000000000000365941000055d0fa4524000000321cea2ae80e1aff406a7c766e8a865696022f38000000d3e0e8a909418bcc356678800000033092afbceacc07852c5328ca700016f60000007278000000d46742bcada8b0000000000b900000000000000c48000271451a0000000000f1c4e20003c960005533eeb1a48509a284d364dad252555eb901b9000002f269dd24b65000316e000f255fdaf34a4e907242b0fab26291270aa90000de1183a78b21500059800016789d180000000c30002ab00011aa0003f8ba54000000368b9e508cca8000000178430300023d4000f0f7168000fae5bc00000012dcba1006000000000047240013b20000002dc9e7a00064b00000008708002dd0a52a460000001dde082188241f42086b000020c0000004f6b4e516057210600000000b8f2f00000008f61a6aaac81000000000000000b70000bc331ec0c0000001dfe00000034607ca0003e064a8d008f261725ef2fc1124963594e1e872ded000185e3ae48096b48342e22c180006ece8cdd500009840002da06e88064f363908813920863c8145464ed538bab6bd98e99ada909840000003e99f417ed0002c58f6cc180003b79381b5215e13e2bc889e0002e62d8d39c145e0980499c01230a9b055bda6cbe51800075091b35327d383479a0001e147603c437800018366fe800000000058f197b596cf66e4027a8b1b219760aa400181a0000002b48000e3e00019a9db4ad30dc0000b2c90600000001a835500000000001135828001904d25adb800144c1ed3f300002f8af8cf740007380004bfef50f1020d38422ac6a612e2df0ba8a96e082b89ef4b560000002ef40000000000000002c6500000011d3c8e346aed2716b090000001280e463eda691c568b
  | 32 => 0x4532b11f514ec422c811cd37e81ff3baf284e0285237150139a4172f5b384a2417b4e39f18000e7d0fa1f8c000a9100030dd908ab56eb00010c10004918000e641653fb0d0860aa8e415100924a29f3a81aadcfcd2a77c8000000cd2000372542415d4bb86a9b704a20c70698dcf9de164b7b8e7e2b742def80e7b655364c4c8000f45e4e8000837bb1800199880285038c0e5c7c702c6daa540f9c1ee0002f7d7dad2e8001b7e772000782818196ee946cf2740eee0006e598b8dd8e270000000c668e946f151c2cbe2252da20800000008380015b4000000265a00000000000013caa9b6ffa6280000040001639c7a554322b4ad4be0000001ee800000056f506196a000000086c0000000000000c2a0000000fb0000a7300000017565ed4a480008242fe0000000000a780000000000ad90000000882000367022c000000383c0016e60006629b5866859571c0000a7f0000000d39d1836e000000022c075000000000065e16d29cb190000000000032c00000000007f2d2839b0a181caa213b3bbd8859f36453dda400007c8000dc8c940000000001b4892b1ca97a05aa27d6a699e0000f0d4dd8fc4e330004e999d82e65ea3be053000006945180000002d9344af152d879e003196332bb980c91de96d856e00000016de000232000106600000011202a4000205b794cb80000001e6c770bf1461871d025cfa0a4a481d30c093b19ead5c200060fb0514ec0000003078342979d23661ceb000000000000003da000204582e000000000101b000372c0011c67a841900013025f54b1bae566b0f30000000a98d410003500e18a5d44fbad02012e72edbcd41f50000ca00000006c388bb774b6f93d45786b8f579ad00019fda4477180001f44ca5b10000001d1c81455bcd6965900000000000000005427688432abb3a39fb5bfabac263a3c5d135fa4e025050aae210000000000000459000066c00021fa9149d9000000000000091837735d80006791ae3ac9b09cbd000000113f5ca0002b08000e5a1d935c4870f160003850000baf000169d32498b0001691ced7700657255412991bfd88743ba0005bcc001b120000002e7c00000008fc000a540000cc00019c8c6f00000000000000000000000e64000000029c0001c182fc2163d06ec80f6904aa152201dc000edb000000056a10352f00000000005478000000b2100000000002507971e98dcdf2a56ec0003af0007370b7002e000000080c7d300000025d400046949b1cbc6ae000640b5060700430000000000e8922e2f3e4ac0c76b7b5fd1431ce6a06564d208415480001771e094d2dd0000000000002caf6a0000003b04000db047f00f019247e1358000000000005000000000012d84ed61eb4c2d540007c0cb65fac000d6e5ba4565cbfb0b5cd0002d143f80000002e41d4c00000004
  | 33 => 0x271a4a9a500025480000000000000000c61000181000000073527a4000ab034bb71200020a00017dc000916035892c596000192a2a1bd27e76579790000d0000000011289563255610fd66d000000019ce00000028f851c0e4552744dc6a0000000cc8000b0d09e8cb800000004f8310c273174f00000df045e09b00015b381841f17aa270e3164b8ef49ac12380034852722d33b58d996f17755b712c00009985fe2f18e0ae240000d80478000669ab04f95bcb2ceafc1c8ad1410a8000000f1e557bc04dc40006c280006fe2b4562a139af8dfe00000d958cf4e2b29f15912505000275600000040d322c2a09d800000000001cb27ebb8415b00000000000000ce413400135c4e80000001270ba83e2528a8c45dea9a80000b46810f200000000006a39ce9a891df00000000009c4b8aa1f10fa73c80019b046a5b1b9d80015620003db3544bb54984d91df5774bb948ebbf8e636b61f700007b111c80020d5d745df36579fc0db0000000000000ea751428a41d8a570002dd829ea6b0001c89200000000000035634a00024e930c00033897760000000000ae46c800000002b1d08e730000000f823182d240019ae634161b20de220000873ba4d6aeaf0f81870f269a057ea72c5bc5cf5180d2c0000007a011940006f50000000bbf000000293d686d370000001860000000111d28c00045bea1f8064d0086a8a2000e0600000000009f037880000000000000001b580002b239d40008f3000196153c872000106a682000000000000000054080000008b5d1c17e00000000000001bee3fb8fca916c16df30003d0400000002c347164ea024a7f6d0ba4ab349a9d95aa03a7624aa98d5400077b80000006080000c18000c710c1b4180dd2b262585205e30000958f250fe68a1bf1b36f48092e9a65c1b15b28391e9f71921a9526f3e103eddf00008c80000002e2231d526911d5e4f2c0000a60001d97da24813d50ae8a703dd61dab2c504057542a98c732cb406c371818281245296e4b820005a80ee80000000001969ca2eb7182000000031f00380010000000000c7191ee7b00000000000000002928934be632340000005f6ae25ecadec2f205c0f7d18f97c3d54110c06a7f6980a74a2cd17064584575aab73a41c28000000289a8886589f500015f4000000000348e000f120003c4140a2f969705340003fe0003ad4000cf3524000141eaa80138674bad7350c48d1c79e00000000008ec0003f4000030c0002d40fcc3cc0000000000000000000000000000002980019202900003c66bf93000000001980d6e5ef07dcefeb9753e192d8ec67a203971e45e5a300000a907eafe800000000000076fa66c000f128002e4800000044f40000000000000000e9c000000355c0000005d456a2c640000000001e8a9b04ed3c860aa22c4568165c26c
  | 34 => 0xa9c8a52a53aa475526c27744265f0110b280e1700052c000000091067b0398e8a0004670061b410006a10001338115659800000060dd5ff5e9944c8800029d00ba6ef00028b55de0003438000ccacff000214800000056e019e0000002ac80000000001d513540009818002ab2c74545b901b646bab4dafc400132600000023907d61bc0003606844be47240001db85fd0000af35160000003708000e8b6dc9be40b882d14a163400000014b0000000000000245d1f8e5f0000000778c1c2a4000000000000000000220000002ed400060080005dc000230656b51a000e2c25b000000000000000001d22a30000000000734800083399ae2f3c3ab90b733fc6009a67e1001c542f4c67ac36c119b434d64ef213950f40005d2e39abc3d14c7867895ac0746aad73937132509c5023854b9b23931c8e4dd102045e9826dd767106e9321901e3140f3a10c97e1c121083180da38257b0000000135000000193edef09fabdda3e0000950000000a88179b6afb7c5690003928cc095c2fa16651c73fd245a9b741cdfc01d50999240001898001c34c5510e40000007f400000017385bec6daca8e360004e92ddd05ce6738a012d0cf62340e9b04c4a2670001a100ab8d1000000000087700000005ca00000000000000001f837551cc32339c8c24f99bd972b00503bcdcf9f7b608000a92a0e84e4714e2624225307025bb97ebc50000523000279fa520000b900000000000001c589c6a512dfb15c9de000000342094a000435369804800066e00007441ba9850d1400000000000000001710001b5200000010a000000071e800177352c0763f1011e00000044c3b9c139b75af01d24dfc00027380018ea0000001fc11ac0000000001b36ba9cbd75b54e06732dff904000ec069b400128eaa90003448f76725f84ae300000003690a946c6da780000019ea754166206c284990a9f2b7c0e7ad11bb98653887bf25e8af8aaa9d4f69ae3e70e5e08000f040003c265040019840000bf8b1131d4a9af5e285500000224800171399921ca08dd2c2266e75bc88480000003c27a62000492121dcaebe377880ec6b69b54efc15853c02d00031b8b3eb9900000000000893a18001c0600000034e800000000016610e02a711b2f25d540000000000f0843605819f8000aa5103000026dcd600004094f45b5000000000023f3b40000000aadeaea5112e690d40d570d53aa3b79d000000023ccae98b400000000024dc0007168003735e301274523214000a493fe28320000000ae25b400074380020dda6a6a50001ffc0006621f904a157e00005f284d0cc3894298000cde0001f12bcc00062c170000000062600000000005c380023c0000d440000001432000000000188c4ad00000014ffbf70002a76bff7833ef8c058d8a2e3ed258108e08a63680a000025373d2
  | 35 => 0xa9ed368aa0762b4ef44894a69d8000e2292862c0000fdf00064fc001020e714fc80015580000328000da392729580000b50000591f22000e0b01f0eb5a4d00019200010be0000334000a5c0005c00ce121209700036f741a93053a9ae0f62c315f40504c566c1a7821cdddc92e0b315456d6d4ff2eb53cc480003298000ae09f5c758000000d5f0000000000d484691499e2dc8c0001db5bae2f000022883e600036600009180000002fde0000398002bde0000004048000000c4e0000000000f273e500006f0e9d64e1ec600062f6c397cd69a0004b8467942addb0000000122909ec7bc7f64a0006ca3bad69400000021b0000000000000063a0003846063ac20005de0000edb000000000000045100036fa98200047400008de00000000000000fc0003c700cc00015983684a4f0603d3ccc0f610f6e500dd0090006de333943030d0000001b2e0210000721cc6f3079be26d8a600000037adb3ef04b419d4c00033365617a546497ce5703f5062a3300038fce961a22d097f80000004c106f515504bac300003ac4570000000b6000000000010260006cd35cda4c11127c396c9201991c6b4ea000b3f29d0a600003280001f903a6b046e081000001f65a126f800000019fb5e00002410002f8800000000029bc00029a53033880000000000d3c00000034f1a6a000862b677b300000000841058000d72267000000023a3dc83ab9d61018000001d70000000047c00024e09a2595c04000233291c0002b123800009790231d600000811e906e80000007fa00000000006a0a721b24000000000006d15b00036e33e400026c620000161d9534d5b4cc9496634b48804000205000333c0008ef0bcc9c9018cd163e29508f062000014cd77c5b24f844c48ea93263ca0ab4eb000000000066039100001f90e20002ec00000000000e20001729e33525f1341e52d80000001df4728cf44b9800000000006058ac000007a268baa0db0003634852a8380000004f200073080000000004c640000009d16d02bffa5ec6b00016f200074a54e0000a0051a702ac2aa88cdb0002a261505c025f62f40000001c6000000089e0003b2c6a800045e000013a0004c542e483e0003687b780000005c49b5467f2110000108000af3bd4a8dc1d600041c0a2426e5c0aafbb893d630f401b636dfecc43a93694000bc70000000000aa30e624cc1fcda700039b7d5887b35a000000024905d40000002ef58d3a79c2e7cf800127000061f6a6c0000003dc6b4000062200000021e800000046581a2c0ebec5989c795282d750e000000000000000001f6af002a00002ce000000000088656100014709981e2167146d35427547a0001c92c30bb23b8c5f40000df8000000ed4371c00176c000000000000009f800030000000041eb4295acf1a5fc18ddb8682c706942de58
  | 36 => 0x33f4000e4c6c51de00000002a6800121b000000000054000070924200000f800018d800035942c0460b120004680de409000017708ed01f00000000000007fba188000000721688343000000000000000007d2023439cd6200052fe878b546e73cc3c2cd2f000000220c00000029e9e84b2257f19c95e1d26c5a5b8b8656186a8631a016af200069683e504e9155c780000000001902088cd0c268002d4486a1601f680002f200022d3a7c6f649b76b803504a507000000000000059d80003aa1746ee289e0000000a54bae000d6b0001cda00093e5df9f0a0005d348d24a41aed5a5491671942000000000014600044800004441c900010188a00000000a2c144d5b943a82d9d49953b600000006db01e8b90d780b1dc300009b4cc90a6c00178650f2618000000eb60000768000000071173912200060b33f1816afb711b04358ead52f840000008b9a7580000000ef8000000bc3c740eb89cc81403f04b60a03840004d261241e400006bf64018a0000000f4888a33c5a40000e38cfe000000000000061d5b28000c9b0002546000000398814428e0846e3af019bc519800000010a00065c22ec000875000201dd4200000000016480000001abce34d2db95800133c5d759c16d9b5d1870999cea000ba55833d200006f34746771a783730000000413ead14a8000fc0904000000000000000000000000000000000000000581bae39341c530d4f4c00000000000008202ec18d8dac6e804e0000000000d4e45d6d5800000005780000000005650008766000000096000022a2a900006218df00034dea76d7e2940000656bd00000000000bd10000000000d5a800000000038f2e112ad3f457466c800171486ea8715d5cd0820f94a10848a0ae5be
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd411054091687d4d4110540d0473d494110540d04731494110540c14649cf514c540c16651d1310c540c14651d1310c540d0474d49310c540d0474149310c540c44735895114440c14641cd514c440945821d5310c44085487595310c440c17651d1310c440c14641cd5148440a14835944148440914835c65410720914835d25110720914835d54110720914845ce510c720914845d5310c720914835c45410620a1683d8661d5120a14835846115120a1683d9264d4520a1684d8e63d4520a14835906414520a148458c6314520a1681d506350520c167418f5150520914835c45410520914835d05110520916839d54110520916851cd4110520c16651cd4110520c14651cd411052091687d4d41105209148714d4110520c14649cf514c520914845cc510c520916849d5310c520916851d1310c520c16651d1310c520c14651d1310c52091687d51310c52091487151310c520a14835846195020a14835846155020a30805846155020a14835906494420a148458c6394420a14835906454420a30805906454420a148458c6354420a508058c6354420a14815506350420c147418d5150420914835c65410420914835d25110420914835d54110420915851cd4110420c17651cd4110420c15651cd41104209148794d41104209148754d4110420c2565dc94110420c14641cd514c420914845ce510c420914845d5310c420915851d1310c420c17651d1310c420c15651d1310c42091487951310c42091487551310c420c4565dc9310c4209a0815c04210020a24865515148020c24765515148020e055418d5148020c447654d5148020e046454d5148020c16541cd61d0a10c147494d61cca1091683dd15210610916839d74210610916839d5421061091684dcd520c610916849d7320c610916849d5320c610c16541cd6110210a1683d506150d10a1684d4c6150d10c16651c54310d10c14651c54310d10b048150c43d4910b048150c4314910916851cd411051091687d4d4110510d0473d494110510d04731494110510916851d1310c51091687d51310c510d0474d49310c510d0474149310c510a6285d886048510e2054d886048510e4053d886048510a0c835516215010a14815cc6454c10a0c8454d6214c10c14731c56414c10a14835506150c10a148454c6150c1090d821d54310c1081c875954310c10c17651c54310c10a14835506150810a148454c614c810914835c55410410a158614c4310410b058214c4310410914835d35210410914835d54210410931851c14210410914845c5530c41091587150430c410a1586150430c410b0582150430c410914845cf520c410914845d5320c410951851c1320c410a14835526190010a1683d944190010a148454e618c010a1684d94318c0109a0845c021080109c0835c02108010
  | 1 => 0x1a84825c06350441a15851c06350441a86821c06350441a85821c06350441c84639cb5350441c84635cb53504418a5821da5350441896839c36250441c157518e625044189687d8d6250441c9063dc16250441c93631c16250441c90631c162504418978718f52504418958718f5250441894865ce52504418978718e52504418958718e5250441e046354852504418968718d6050441c177518d6050441c8463dc96050441c84631c96050441894835c86050441896861cd415404189687d8d41540418948718d4154041c8473d894154041c84731894154041ca0621c141540418948798d41140418948758d4114041c84739894114041c84735894114041c14541cd61d0931c14541cd6190931b05829944310431930805d54210431a8582190438c431a8682dcc644c431a8582dcc644c431894845cb654c431896849c3654c431a8682dd4644c431a8582dd4644c431a1585dc8644c431a15859c8644c431c85721c8644c431a17855c0644c431a87825c0644c431a84825c0644c431a15851c0644c431a86821c0644c431a85821c0644c431c84649cb544c431c84645cb544c4318c5821da544c431a1486550544c431896849c3624c431c1575192624c43189687d91624c431c9064dc1624c431c93641c1624c431c90641c1624c43189787193524c43189587193524c431894865d2524c43189787192524c43189587192524c431e0464548524c431854865d7424c431c1675193424c431c1675192424c431c1575192424c431a8582190424c43189687191604c431c1775191604c431c8464dc9604c431c84641c9604c431894845c8604c431896861d1315403189687d913154031894871913154031c8474d893154031c84741893154031cc0621c13154031894879913114031894875913114031c84749893114031c84745893114031a14835506150f21a148454c6150f21c17651c54310f21c15651c54310f21915851cd41107219148754d4110721915851d1310c72191487551310c721a14815cc6454e21c14731c56414e21a14835506150e21a148454c6150e2181c875954310e21c17651c54310e21a14835506150a21c14541cd61d0921c147414d61cc921d1073dc15410521c33761c15410521d13731c15410521d10731c15410521d23721c1541052193280dd64310521930805d44310521d1074dc1530c521c53761c1530c521d13741c1530c521d10741c1530c521d43721c1530c52195280dd7430c521950805d4430c521914845d5320c521a14835904114121a148458c3114121914815ce5410c21915851c54310c21985821c54310c21914835d25110421914845ce510c421c30641c12154021c50631c1215402191683dc55210640a14835925188640a16839944188640a2a85d886050940d23721c14214540916851c
  | 2 => 0xb90010e15c3c158283546a3c824010bf138332383a10cb725cbe304b51c8a50e6e83e400380e1000f002b07001162a6002d800048ba3200b19c92000e41f400000001ec82000f124b1126ca600040056938342e80c00000bc000003ace8c480000000000950bc383b401164ea9b90c0000021c102d02114c4625091a74061cd130b9143e00e000223cd1009d21410233dc6b0b4ce328c4300990f8ff314640701a04ac945d00204fb0f40006200000d92143b2849a0004d000000d4a21702c47cee3d03917800242792443ab0800008762807c253012a50b35cda37909046f523048078843bc62185083e8d328cd00009f335200ac8d080070c0b13b0930000f06c142a1030b689ab2320746c398501683707c05258a41983f1d0001a05b1c4441e84a2cc1539c541146f20ccf36c00358e2030d8000ae000c600000000474786946c3c93c00194ab37c00000112d6410d0d20008f40800260b68000021889000250000031cb034400098001d4e90000030c000000038c000c40a180cb000001e119454002a8b2000553af1c1c0513f50d1b47f220000ae003d8e9bf9218f649270abad218148804688b3f0ad04c4c05c77278bb3745f020e50d863474d40240042804af4902e10f0a45d1f8af02edc2b08a29ccc4142a06442066001611812cea0590607c020900094020118800000a028081208008140207000280c03030181603008001801168001a02020140c000008c00020300c48090002046080702468000000812130081c00020d81c0000008005c01000040421000180c02000102203000000a04050002820040040a220001802000d00c020c010480e15a30805086154042894835c46050841a8682dc46350441a8582dc46350441a8682dd06350441a8582dd06350441894865ce42504418958718e4250441894835cb6550441896839c36550441a8682dd46350441a8582dd46350441a1585dc86350441a15859c86350441c85721c86350441a17855c06350441a87825c0635044
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3920
  | 3 => 290
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (510+((h/13+packedAt gbK7 (432+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (35670+((h/502+packedAt gbK6 (29646+(h % 502)*12) 12) % 2404)*12) 12
  | 5 => packedAt gbK5 (265990+((h/2529+packedAt gbK5 (230584+(h % 2529)*14) 14) % 9107)*14) 14
  | 4 => packedAt gbK4 (212230+((h/1550+packedAt gbK4 (192080+(h % 1550)*13) 13) % 6752)*13) 13
  | 3 => packedAt gbK3 (18363+((h/107+packedAt gbK3 (17400+(h % 107)*9) 9) % 387)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffffffffffe07fffffffffffffe1fffff
  | 1 => 0x3f80fff80fff81ff83f07c1ff83ff01e89e7c
  | 2 => 0x3fff03fff03ffffffc007fe0ffc1ffff0e38f
  | 3 => 0xfc00003ffffc001ffffff8000fffe001ff03f0
  | 4 => 0xffffffc00000001ffffffffff0000001fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x808a10092209000014b094212842154032cb5
  | 1 => 0x595262990e4922ae581542d1a5a35a0ce8965c
  | 2 => 0xa26144aa241a4696aa8084b489691ca970c30a
  | 3 => 0x33458b34489074db34e6d0210e738831bd03e0
  | 4 => 0xc3860c3870e3871dc738e739c04210c1def800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0eaa8a8a0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36699
namespace PEqualNP.Outside.L_meta_36699
open PEqualNP.Outside.L_meta_36699.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 290 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3808 : Interval gbAtlas 4 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3872 : Interval gbAtlas 4 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3904 : Interval gbAtlas 4 3904 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3920 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928))))) (concat (concat (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152))) (concat (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)) (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 bgb_4_1664))) (concat (concat (concat bgb_4_1696 bgb_4_1728) (concat bgb_4_1760 bgb_4_1792)) (concat (concat bgb_4_1824 bgb_4_1856) (concat bgb_4_1888 bgb_4_1920)))))) (concat (concat (concat (concat (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016)) (concat (concat bgb_4_2048 bgb_4_2080) (concat bgb_4_2112 bgb_4_2144))) (concat (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400)))) (concat (concat (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528)) (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656))) (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))))) (concat (concat (concat (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136))) (concat (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)) (concat (concat bgb_4_3296 bgb_4_3328) (concat bgb_4_3360 bgb_4_3392)))) (concat (concat (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)) (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648))) (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)) (concat (concat bgb_4_3808 bgb_4_3840) (concat bgb_4_3872 bgb_4_3904)))))))
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
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6068 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
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
theorem bgb_6_1088 : Interval gbAtlas 6 1088 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1098 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 27 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeeeeeeeeeaa8a8a0eeeeeeeeeaa8a8a0eeeeeeeeeaa8a8a0eeeeeeeeeaa8a8a0eeeeeeeeeaa8a8a0eeeeeeeeeaa8a8a0eeeeeeeeeaa8a8a0eeeeeeeeeaa8a8a0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3941133024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36699.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[2,6]⟩,⟨.or,[4,5]⟩,⟨.and,[1,7]⟩,⟨.and,[1,8]⟩,⟨.or,[7,10]⟩,⟨.or,[2,3]⟩,⟨.or,[0,9]⟩,⟨.and,[0,11]⟩,⟨.or,[12,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941133024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941133024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36699

open PEqualNP.Outside.L_meta_36699 in
theorem PEqualNP.Outside.L_meta_36699 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941133024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941133024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
