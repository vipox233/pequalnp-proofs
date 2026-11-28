import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36581.Model
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
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


end PEqualNP.Outside.L_meta_36581.Model

namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
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

def SBf (j : Nat) : Nat := [6, 4, 8, 7, 7, 7].getD j 0

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

def checkRow (g : Atlas) (k i : Nat) : Bool :=
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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_36581

namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xcd5306501029008003a1610807be43bc43be42bc42bf41bd41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3800221800414610004b94a438f29c851c5350658a4a0ce14141e418041b040043a060087808010
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
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s0K3 (255+((h/3+packedAt s0K3 (243+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 3 => 0xff83fffff803ffff807fffff01fff807ffc7c7
  | 4 => 0xffc1ffffffc01ffff807ffffe03fff807f8f8
  | 5 => 0xf0001ffffffffe0000007ffffffc000007ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x21108259092492588909168b162c5b4b49db5b
  | 2 => 0x422104af424924a952522b40ab56ad95942dad
  | 3 => 0x847609325762393247644dd5819b30c6e6c6c6
  | 4 => 0xe843b1c46473b1c4644771e6cd03c6e0c770f0
  | 5 => 0xf7bde078783c1f878787e78f1e2070707bf00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000ccc0c000c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36581
namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
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
  | 2 => 0xfc0fc0fe07e07e07fe1e0f07c3c1f0f87d5293
  | 3 => 0xfff000fff8007ff81fe00ff803fe00ff86631c
  | 4 => 0xffffff80001ffff00003ffff000783e0
  | 5 => 0xffffff00000000001ffffffffc00000007fc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x4000002000000000000100840021008000425
  | 2 => 0xaaa99965354ad4ae8f168b468ad1a2d1755292
  | 3 => 0x326aaaa954d369a2b7710dd2137484e7166318
  | 4 => 0xa34d34d1a69a4d34dbbba88423b9ce422783c0
  | 5 => 0xc38e38e1c71c71c71dddcee73a21088447f800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36581
namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x81fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107bcca20f6194417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f621041ef32083d864105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ec62887d4c510fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e882087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd529077e8520ef50a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0ef90d41de21a837f52506f8a4a0ef90941de21283f7415077c82a0dfd4141be282837e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220ed50441bf280837d50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc7be8798f710f31bf29663ee52cc6dca598df54b31f6a96636d52cc7bc6598f70cb31fb20e63f541cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c63de438c7ba8718df94a31f7294636e528c6faa518fb54a31b6a9463df328c7ba6518df94631fba0c63f4418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f710d31bfa92637c524c7bc6498f70c931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f7cc831ee990637e510c7ec8218fd50431ef98863f6310c7ba6218fd4c431ea988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790fbd0b21f621643ef32c87d86590fd90721faa0e43f631c87ea6390df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52887dc8510fb50a21f719443ed32886fca310fdd0621fa20c43f731887e86310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fbd0921f621243ef32487d86490fdd0521fa20a43f731487e86290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843f641087ea8210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0
  | 2 => 0x802005002008000000000000080000005c030040040000000200400c0000100a000000060080040000a0000040280100a00c078000020240080000e0040e0020000100280700400000803004000000000000040080c0080000000300e0040480101200c00000000004010000000040980000a01401800000000000020020380200800a0000080000001401800002000008080020300080000000c0280000201c030000200000100000c014010040000000000200c0040280a0000000000000400001005008000000020040080200100a0100080a000044058020020000080900200c0280100000400001000000000000100280a00b0000040d809010014050010120640080200600002810000002fca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e87f651d0eeca3a1df54743faa8e877551d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390b7e87216f50e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42be29a85be4350b7886a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84216b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332efa1e65dc43ccbdc85997b50b32bf28e65f651ccaeca3995f54732faa8e657551ccafca1995f54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c65de438cbba87195f94a32f7a1465ec428cbbe65197bcca32bf28c65f6518caeca3195f54632faa8c6575518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65dc434cbde84997b10932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832e6990657e510cafaa2195f94032bea80657e53d07bca7a0d794f41bea9e83dd53d06baa7a0ef90f41de21e837e52d07dca5a0db94b41bea9683ed52d06daa5a0ef90b41de216837e50d06faa1a0df55241bf29c83de53906bca720df54e41eea9c835d539077e8720ef50e41bf29483ee52906dca520df54a41f6a94836
  | 3 => 0x75299670000012c20f0000000004153089400000000001930002ec0000c00011c7155e0003f2000baa5e00000000000000600e39b26500005e2a762c07000210000bc0000744c0a5c000d5000778ec80063c2353f8001d00000aafc00000009b0c2460006a05e00068c0031b2b8001170000809387baa05fa00024922262000d133331aa500010709a9104e03942c5f8d39182da4983080c39a87d5a97a436654dc8082f818000289480000000000003ac00000430000002de0000000015f048000000990000000024c0000013580046a89d029131dc544580000002cc0014e158000cb80060a0c4c71df3b40f0f92d0000084d98000004912b3144b80013f11553c000000000000cc000685a40000007e14280c4d0534000d514b3048c3e57c81d35ab640032c51c3d17925000000000000000000001d600000000000000000001e8000c2cb4800000000002b400000169800000530048000000dd668004788888e092224a30f21f85c26d4002c9000000000100002905a8fd456a18001b72a0b044181215c2dc1417447e0383b1f02a66797bab26540019a8001941080025500081c2392e086000f7aeb62e4f00000010c000000000009c8000b40d60014e8000007cce48f63ee001901483ae001851b8510830002fe2229a8f025d45a0008b91f108618379e1000b503e00000043800000000000000000000000000045e4dd8a93f47cc35632e34fa000000940002445d8ba000001938e2074000730ea2bc8100000038600000000000aa91307f4d03210e2cf0f01640008a66e3b4000e4000000d799f5620c0980005580000018b4280005f2620000014130141464c000dd5feaa00033c2205149a03230e37c0000061cc881f80006c0018932d5a20f81eb001e00000020e670af470800000340000a90007880000040c9e4de0002c40012b9fc28eb7c0333a0b00000f8b800000000046000b00001705cc000000002cc000ee1b00000001615400000079000000744000000002140022a20aad8001d0016b2d4f86e0006c52502e2349051e800000001490000005e17785200086800275458298000000ca0000d0000000005c8003d6114000003ba00000000200000000002061314684f000430a11165d427413abf63e76c003235d000000000000b3933ab00005100b8002420000000755e00000000000c3c00000000c1961a78324cb80000065e05085177000a04728003960ecdfafa000278e9a421f8a6c270005dc0000091b00078c001ed4a4000e40000000018e80000000204800801018010020000120000000100000800001018000000020080040100200000007001008008028020000000080400003c00811014000000110000000000000c00c0000300400c05000004014010030000040100000400c018080080040100100202c0080000e
  | 4 => 0xcb0da5060006b80000067000287000000438002566e8e90c4000aec000fe2aa2314c800000b900019450a06451000000000610000a20019096464a1c4159d55d8a2ce731c5665e42e000490730f7000446450943070c8808e21ff0003596206734c0010f2370dabd04982f52a4b0600cd232690588770a05840b0a312a61452b191a20012f800358000ec0ab000000000000000000000000080400000500000000d9472794618001b832ce780033abd8000003cc9b0ab80000000000000000b200002d000000100000009b521800000a4c000c900000000000000000000004969940000000a000001ea000b5d9880055c000002084260999919a000000cc2d5000000000005b67c4000000ac5ccb59ca58425d0aae74a89b8b42a33144359b1f54421c9228a85201e477880116151190290001c09529a00023c00000000000ad00034a0000f07362006c00231000000f63132920006604a00031c3500023c03538ac52080011a0005da0000000000029d34800000000b0000000000000e301e6a1140004e62b4000812de5c4001320000005513b0002d8088ff0544e5920001128499a27c0000000025a5706ed81a495ca0013793d24e60884101416844bd9ae5425a80025b1f6000701c61f04d91b07b0ae86574aa25143e8c18000004f96ea611bc79c84a17000000948000ea9ec001be5220002d800000408a00002820019c9b46340000018c0001e80004b4c60000000031000000000302aac672f82ac7f41c0004ee5b8000000000000031818a0004c1580009917a91d6084cc000000000016b0000000000000021e000112ca0cc0000028f000adc00003000000001bd28c00000184014000002a60000000000017e00000125270000c48d20000011d2f153834d520c6000208000905b07a42fae046033cd5088140b8873a7443a0012c959622000002dc296b30ae8f5000000003080001891d8e93569d8010002d80002a95b000000fd000000000be8000008cc000ec1647f8001c10009e80026626a000a51f436ccec220000005c9422c7000000830000000006d87d1b00015c800000000002ba000cf4a780000050ca90002cab68002a54482585ea4d068001068003206452780057caa4001f6652bcc318002404e8001a900000000296384000360f13363cc2d1a138094595a2031e08cfda3848e0017daad2fe4b4d000009058c0027000082400000000000020001820000009b2160004f8000001a40000033200057b09604534ea12f04a1
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x252c425e6394b109758e52c42d56390710b958a41c43345450710ad59231c42e5628c710d514d31c42b56488710b558e21c4364524871097d8d548425c63552109bd89548426c62552109798c548425d63152109b988548426d62152108fd91538423c6454e109bd89538426c6254e108f990538423d6414e109b988538426d6214e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10b598f41842e662d0610cdd5041842b664cc610b998b3184357530c610ad99321842d663c8610d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544423e6515110cd584544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766590510cd15241442d56390510d514e41442e56290510d914a41442746550510cd15141443545350510d91494144276658c510ad5923144334548c510d514e31442e5628c510d914a3144274654c510cd1513144354534c510d914931442766588510ad59221443345488510b558e21443545388510d914a21442746548510cd15121443545348510d914921443345484110d514e104436452841109798f540425d63d50109b98b540426d62d50108f596540433461550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c755153043546154c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597410433554d0410b598f410435553d0410b998b410436552d04109d59441043355410410d554c410436552104109d59731042b664cc410cd553310435553cc410b998b310436552cc4109d5943104335540c410d554c3104365520c4109d59721042b664c8410cd55321042d663c8410d554f210436552c84109d59421043355408410d554c21043655208410cd553100435553c4010d954b100427965840109dd9510042b46444010cd55110042d46344010d554d10042e46244010d9549100427b6544010
  | 1 => 0x827661953209d58654c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c82766194f209d58653c82cd6390b20b958642c832c5450b20ab59232c82e5618cb20d314d32c823e64947208f59251c825e63947209758e51c82ad64c8720b358f21c825f63552209718d548827761552209d185548825e63152209758c548827661152209d584548823f6454e208f19153882776154e209d185538823e6414e208f59053882766114e209d58453882ce63d0a20b9987428832f5410a20ab99332882e661cca20d3d4c328823f64546208f191518825f63546209718d51882ae6488620b398e218823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209bd89544827761551209d185544823e6515120cb588544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d20d3588534826e6590920cb15242482cd6390920d314e42482e561909209b195424832c5450920d314d424826e658c920ab592324832c548c920d314e32482e5618c9209b195324832c544c920d314d324833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c51483664214520d950851483663214520d94c8514826e65c8520ab593214832c54c8520b358f214834c53c8520d9147214832c5448520d314d21483645148520cb152204834c5388120d9146204825e63d50209758f540827661d50209d587540823d6595020cb189540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c20d3189530823e6414c208f590530825e6314c209b98853082766114c209d584530826d65d0820cb55342082ce63d0820d354f42082e661d08209b594420832d5410820d354c420826d65cc820ab993320832d54cc820d354f32082e661cc8209b594320832d540c820d354c32083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083674254420d910951083673254420d90c9510826d6588420ab992210832d5488420b398e210834d5388420d9546210832d5408420d354c21083655108420cb553200834d53c8020d9547200826f6548020ab191200832d5448020b318d200834d5348020b9185200836551480209ed95200825e63d53109758f54c426e62d53109b58b54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c426e6294f109b58a53c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59
  | 2 => 0x5310c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840c754e421032d5290840ad986421031d5310840cb54842103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d51103364254440cd109511023d6590440a798e411031d5390440ab98a411032d5290440cd546411031d5310440cb54841103355110440c754f401032d52d0040cd547401023f6550040a718d401031d5350040ab189401032d5250040ad185401033551500409ed95401026e62d53309b58b54cc27661d53309d58754cc26e62953309b58a54cc27661953309d58654cc2cd6290f30b558643cc31c5450f308f99252cc23d6494b309d98652cc2756194b30a759332cc2d561ccb308f99251cc23d64947309b98a51cc26d6294730a759331cc2cd62cc7309bd89548c26c62552309dd85548c27461552309b988548c26d62152309d984548c2756115230b398b438c2d661d0e30c7d50438c23f6454a308f191528c2776154a309d185528c29e648ca30b5986328c23f64546308f191518c26f62546309b189518c29e648c630b398a318c23e64951309b98a544c26d62951309d986544c275619513097d8d544c26f62551309b189544c27761551309d185544c23e6515130c758c544c25e6590d30c7152434c2cd6290d30b5586434c25c6550d30c7151434c32f54d4930cb153524c32f5414930cb150524c34e4314930d350c524c25e65cc930a7593324c31c54cc930d314b324c2d561cc930c7151324c34c524c930cdd53514c33454d4530d9d4b514c36452d4530cdd50514c3345414530d9d48514c3645214530d590c514c3554314530d5cc8514c355321453097997314c29d64cc530c7153314c2cd62cc530d314b314c35451cc530c7151314c34c524c530d5145314c31c548c130d314a304c354518c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c275611503097597430c31d54d0c30b398b430c2d661d0c3097594430c31d5410c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c435483097596320c29e648c830c7552320c34d528c830b5986320c31d540c830d3548320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3563254430d50c9510c25d658c430a7992310c31d548c430b398a310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030b3189300c34d524c030b5185300c355514c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63953209758e54c
  | 3 => 0xa21cd55341886d663d0621d554f41886e662d0621cd55041887555310621e950841886b664cc621cd553318875553cc621b998b3188735540c621d554c31887c5320c621ab593218872e54c8621b358f218874e53c8621ad993218873554c8621b598f218875553c86219798f544865d63d51219798e544865d63951219b58a544867561951218f993534863d64d4d218f992534863d6494d219b58a53486756194d219b99742486ce63d0921b9987424866e6510921cb550424866e65cc921ab99332486e661cc9219b994324874d530c9219d99741486d663d0521b998b41487a442d05219d99441487355410521e9d08414867665cc521ad99331486e662cc521f10cb3148676650c521d554c31487c7320c521ad99321486d663c8521ab99221486ce63885218f990504863d64141219798c504865d63141219798f540865d63d50219b98b540867661d50219798e540865d63950218f993530863d64d4c219b98b530867661d4c218f992530863d6494c218f992520863d64948219798e520865d63948219b59642086cd6390821b9586420866f6550821cb151420866d658c821ab59232086e5618c8219bd95320874c534c8218f992510863d64944219798e510865d63944219d59641086d56390421b958a41087a542904219dd9541087345450421e99094108675658c421ad59231086e5628c421f14ca3108677654c421d514d31087c6324c421ab59321086cd63c8421ad59221086d56388421b958a210866f65484219dd9521086e76548421d9d9521086e76448421b959121087665448421d915121086e76348421b958d21087665348421d914d21086e460484218fd91500863c645402197d8d500865c6354021d9485500866e6294f409b58a53d02766194f409d58653d02ad62d0f40ad58743d025e6394b409758e52d02766194b409d58652d029d63d0b40ad58742d025e63947409758e51d026e62947409b58a51d029d63d0740ab58b41d026f6254e409b18953902776154e409d18553902ae6290e40ad986439025f6354a409718d52902776154a409d185529029e6390a40ad986429025f63546409718d519026f62546409b189519029e6390640ab98a419023e65d0d40c714f43502ad62d0d40ad587435031c5350d40d3d4f525034c53d4940d3d4c525034c5314940cbd0c525032d43149408f997425029d63d0940c714f425032c52d0940ad587425031c5350940cb149425035753d4540d514f515036752d4540d914b51503575314540d514c51503675214540d914851503374314540cd50c51503374214540cd508515023e65d0540a758f415031c53d0540ab58b415032c52d0540cd147415031c5350540cb14941503345150540c714e405032c5290140cd146405023d6590c40c754e43102ae6290c40ad986431031d
  | 4 => 0x718d54cc66e62153319b58854cc71d54d0f31b398b43cc6d661d0f31c755043cc72e5494b31cb55252cc7656194b31cb95152cc72d5454b31d3d0d52cc74c4354b31a799232cc71d548cb31d354a32cc6d6618cb31c755032cc74d520cb31cd95241cc6d56390731e5d0e41cc6e56290731d994a41cc7365450731e510d41cc76652507319b98b548c66d62d5231c758e548c73461552319b988548c66d6215231c7952438c6cd6290e31b5586438c71e5450e31cb952528c72d5494a31d390e528c74d4394a31cb951528c72d5454a31d9185528c69d64cca31c7953328c74e52cca31b5587328c71e544ca31d3949328c73554d0631b598f418c79643d0631b998b418c76552d0631cd550418c7954310631d9548418c69d64cc631c7953318c6cd62cc631d394b318c6b664cc631cd553318c6e662cc631d954b318c66e62d51319b58b544c65d63951319b98a544c66d62951319d586544c65e65d0d31b398b434c6d661d0d3197994434c71d5410d318f993524c63d64d4931a7992324c6d6618c93197994324c67665d0531b598f414c79443d0531b998b414c6766510531cd550414c7974310531ad993314c6e662cc531a7992314c6ce628c5318f990504c63d64141319b988504c66d62141319798f540c66e62d50319b58b540c67661d50319b98a540c66d62950318f992530c63d6494c3197596430c6cd6290c31b5586430c65f6550c31c7151430c63e64948318f592520c69d64cc831b5587320c65f654c8318f992510c63d64944319d596410c6d56390431e550e410c6e562904319dd95410c7345450431e590d410c69d64cc431b358b310c6b5648c431b558e310c6e5628c43197d95310c677654c431b5d95310c757654c431b5d91310c6d5644c431d5951310c754544c431b5d89310c756524c431b5181310c63f64540318f191500c66f62540319b189500c75531540319798f54c865d63d5321cd58654c872c62553219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21d558653c871e5454f21c755153c874c6254f218f99053c863d6414f21cb55342c86ce63d0b21d354f42c86e661d0b21cb55042c874d5310b21ab99332c872d54ccb21d354f32c86e661ccb21cb55032c874d530cb21cd95241c86d56390721d594e41c86e56290721cd95141c87565350721e910941c86b5648c721cd95231c8756538c721b958a31c8736544c721d594d31c87c4324c7219798f548865d63d5221cb58a548873461552219798c548865d63152218f993538863d64d4e21c7952538871d5494e21d358a538871e5454e21c755153887546154e218f990538863d6414e21cb95242886cd6390a21d394e42886e56190a21cb951428874e5350a21ab592328872e548ca21d394e32886e5618ca21cb951328874e534c
  | 5 => 0x43ccad661d0f32c755043ccb2e5490b32b358e42ccb8f4390b32b958642ccb2e5450b32e310d42ccb365494732cd55251ccb664294732d950a51ccb365454732cd55151ccb574354732d510d51cca7661d52329d587548cb1d6395232cb189548ca7661152329d584548cb1e5490e32b358a438cad56190e32c7951438cb2d54d0a32b398f428cb8e43d0a32b9987428cb2d5410a32e350c428ca9d64cca32c7953328cad561cca32ab993328cb2d54cca32b9987328cb365494632cd552518cb564394632d550e518cb573294632cd951518cb355454632d9d09518cb644254632d9cc9518ca7661d51329d587544ca5d63951329b58a544ca7661951329d586544ca5e65d0d32b398b434cad661d0d3297994434cb1d5410d329b997424cace63d0932e310f424cae661d09329b994424cb2d5410932e3d0c424caae64cc932b9987324ca9e648c932b5986324ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca5e63d50329b98b540ca7661d50329d587540ca7661950329d586540ca3e6494c328f592530ca5d6590c32b358a430cad56190c3297d95430cb1c5450c328f992520ca3d64948329b596420cacd6390832e350e420cae561908329bd95420cb2c5450832e390d420ca9d64cc832b5587320caad648c832b358e320cae5618c83297d95320ca6f654c832b3d95320cb4f654c832b3d91320cacd644c832d3951320cb4c544c832b3d85320cacc604c8328f992510ca3d6494432d34ca510ca3f64540328f191500cb4d32540329dd85500ca746154032d558653d071d5390f41ab98a43d06b66190f41c754c43d074e5394b41d354e52d07656194b41d394d52d074d5354b41cb90d52d072c4354b41a798e42d071d5390b41cb54a42d06b66190b41c754c42d072d5210b41d5185539071e53d0e41ab58b43906b561d0e41c794d439074e5394a41d354e529072f4394a41cb50e529074e5354a41d354d52907646154a41a758f429071e53d0a41cb94b42906b561d0a41c794d429072e5250a41a758f419071e53d0641ab58b419072e52d0641b598f419075553d0641b998b419076552d06419b98b535066d62d4d41ab98a43506b66190d418f994435065e63d49419758f525069e6390941ad986425063e6510941b598f41506e662d0541a798e41506ae62905419798c505065d63141419b988505066d62141419b98a531066d6294c41ab58b43106b561d0c418fd95431065e63948419758e521069d63d0841ad587421063f6550841a758f41106ad62d0441ad59241106d56390441b958a411063f65504419dd9541106b76550441cdd9541106b76350441cd94d41106b76250441cd94941106b4605044197d8d501065c63540419bd89501066c6254041cd505501066e62d53319b58b54cc7356195331c
  | 6 => 0x400400c01401c00000000c00002000001400c00800800400000400400800400000000000800403c00401000c02000800400400800800001000800000000400001000800000400000000001000002800000000000800800000000401c00002400003800000000801400000c01000c01003402000000000400c00400c01400800000c00000000400000405c00000800800000000000800000000400000000400000000401400401000000000401400000400000800000001001001800000000000800000004000400000000000000400000000800002400801c00800000400400000003802800800000000000000c00c01400000801001000001400802000000000000800003001000001000001c00c00400000000000800000002400001400400c00400003c00802800000801000400000001400000400800400800400000c00000c02400401800000401400000000401400800800000000000000000800800800000000000000800401800400002802000800400000000000000000000401001400400c00000000000400400c00000400000400401400000f665294743d954a51d0f665254743d954951d0ead62d0e43ad5874390ece62d0e43b59874390f2f4394a43d3d0d5290f665294643d954a5190f374394643d99495190f655254643d5d0d5190ece62d0d43b59874350eae6290d43ad9864350e7661d49439d5875250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050ead62d0c43ad5874310e9d6490c43b358a4310ed56190c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9f6150c43a71814310f1d43948439d9865210e756194843c750e5110e6e62944439b58a5110f1d43540439bd895010e6c62540439dd855010e746154043d358a53d0b1d5390f42ab98a43d0ab66190f42c754c43d0b565394742d554e51d0b565354742d554d51d0b364354742cd10d51d0b4c6254e42c794f4390aad62d0e42ad5874390b1e5350e42a758f4290b1e53d0a42ad5874290ace63d0a42d354f4290ae661d0a42d594e5190b555394642cdd0e5190b354394642cdd0a5190b565354642d554d5190b6742546429d9875350a7561d4d42ab98a4350ab66190d428f9944350ace63d0942b99874250a9e6390942ad9864250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050a766194c429d5865310aad62d0c42ad5874310a3f6550c42a758f4210ab561d0842ab5924210acd6390842b95864210a3f65508429bd954210aaf6550842cbd954210aaf6350842cb94d4210aaf6150842ab1814210a5e63944429758e5110b2d429444297d8d5010a5c6354042cb5095010a7761540429d1855010a7661d53329d58754ccb2d6295332c718d54cca7661153329d58454ccb1d54d0f32b398b
  | 7 => 0x18100022d00023d0be80000000000028d0000000002a58001bd80021a88d00024fa440000bc80022f13300000000000000026200013b8000000002b081c95780000000000000029d8498000060001120000790000001e885b87286b2c22272328828f01ea29714a1e1227800119ac318d07f0000f18cd9922b18001c100000000000000000004118f8001bb00000000000000011a0000000f40e20000002ba0f99da8329959698000000000000000000e58000000000000000000000002578001850ef0d31a480000006d01c000000000054800000000145234aa41b5a001ca8000000000448000002340000000000000d48000000001fe10f800000000000000152ab40000000a7000000196800025a0900000021e2a690b208a619789fc26e80000000000000009d2bc25c0000000d18000001e780000006400000000000200000000000000029c2290000468a58000000e41eb8000000000cf07218d80005415e1c386300a8178ba18282713b10787500000017b80000000080000008414e92c0df0a6aa997c0580b48d10748001490001a924800000000000026d88b9620002058000000000000001e800023e8000ec0000002b620f9ac9148000000000002828f480000000019494c80027680000000028600000000000027e00000001408219d95aaa100010cac080008b0001ff97d88e9c99ee9f480000012800000000000012112780011680000000000000000000000018580012a00000006380000000016027a00000000027a865886a0722b9cc02b0000002128001d7a3909400911513d0a12682bf1dd0001611cd84d88529180000000000000000000002100000000000008fa7cab91a824f00b00000002e2948000000c20001eaa389bf8330fca838001730100da0702c60cb0a32401a1013000231a58a7e94bac68589aa94d987a2d8000bc22c02f80027187829a8002880000000a994482692280014d147000169120a0100007e24aa77824167800000001000001400000003000400400400400000801800805000000401801400400800400400400000000400001401001400000000000000000400000000000001800000400000001401c00400800000000000000000000801800c00000c00400800800801800800800000000000000001400000400000000000000000000400001403800401800000400001000400800400800000801800000000001c02800801000800001400c01800000000000800000000000000401400c00800001000000801000401400400800000000c00400000400802c00000000800800000c00400c00c00400401800802c01800800401000400000c00401000000c00400000001c0100000000000000080000000000040100000000040000000140000080080100040000080080040000080100000
  | 8 => 0xc391f9cb80026000000012000000000000001a1008000948000000000568739cd0000000000000000000000000000000000c40501681cb1d480006e29280000000013e0000f780000000000000000008099020d20611e8bf91406c191abc9a003000f0000000001c4a9ca88808a899308b42b5a361871250e10201361f928520400000000000018c9a980013280024695f13a8000eb1fc9c01589c28000001c08001351898a0000000000245a758000000c4800113836800116000029104a0d98a0a900000028a24899b80007713c09180010aa3aa0204d00000000025d0000002960f30000a19371ec25fa4c0e700029787d90d0001a79420000000802830000000002159960da8c50000000000000000000000000001fd1f38000000000000000000000002a297826d00003c0001320000000000000000000000000000e680022c8001798000030000000000000002c52a88000000000001ce00016f0251be80000000000000000000012480000016d23e0000000000000000000000f380009e9131118000000002c700022a04500006d8001e2a760c61a407d033800204a980000000000000000000000e380001b0000000000000000002ba8001c40001791bf00018600017485e80011e00023f00000028f0000000002bb1a39868000000000000001fba968000000000000001930000001c5000000241a6500003885300012194b102115a1c0cc17d08e1300838b92460000002338e800000000d8001df0002018d40000849f69510000000000002130000978000040a0a702242098002308000908001ce83080026f8000758000000000000000000000001a68000000000000000000000000000818000002490001ae9c78000000000002698000000000000000000000000f70000000d80000000002a61b700024d80000025c80013c8000000000000000001658000000001a7270a3300010b8000001b50000000c98000000000000000000000000000001e200000000019a1b88ff81f8001bc0d58000bb0000000dc0000002550002500000000000d88000001d70000000e289c800000000059a9f84c2370000421839f723c9d61d1034140827a7b80000000000012aa6c1e9a100000000000001258000001488000001e62990000002420c3a870118861bb93697c8038121980ce80000000018c00000011d18f00002310e10da4b80029b1e38000fe1dc000180000000260a1c8001768390001318bbabe0000000002118000000001232302a7a0699080000000000000000000000000000023b80016700025380000000021b80018886b80000029f0000000000000001380539de8310000000012610000002788d00002190000768000870001c700024505b09a00000000023800013ea6780000010280000000000005f84b92c87ca4b000000000
  | 9 => 0x2a000000000000016491800018094122e9630228001722c00a200000009b8890000000000000002668000000000001b28000000000000000c69f0242aa90de00020a0002ae9128001a516f8000000000000000000002379570002780001ae09b12f84180027292d0000000000001098000dd1a2264aa380000020e8000002310c8800000225000105a02a1d00000000019d0000000000000002b800026300025a80022b0000002510000001bc9f80000000000000f58220001398352532220370718001d980008799500006980027300025f2be80000005500000000016b9e40000000000002b88e002b9929ef0000000000000b98190000000001dd80013400003e9df8fc0e48001d1a2180028e8000b00000000001d500027901729999380815384280000000007b1d41afa198000000000000000000000000000aa00000016a87095a02605183fa800ed94f0cb8000000ad80000015e8002470c71b00000e600024c9f50000002ae1b60000000000000000711240000000000000000000a800000000001b8000000f613f83d9428d99171fa00000000000012e86a943867999933a750408001baa1d8000000000000000000000002691830000000d28001d3000256805a2000000016c80000020780000000000000004f0000000ac0138000000000000001b78000000002051971390000000d200003a0b58000000000000fda8400000003e029a6e0000000000001e700016a00000000000007c01515c83aa5716e0fa8e316d80000f80019897780023d8001eda2801a80000026280010604a0000000001530000000ab2ac00000004c9cc8000f800000000000000015b9650002180000000000000001d581d09880009f8000050000002498000888001f880011c2a70b08000000000000ee20e0000e915f8d080028b800241079a6a0ae19e0000000b386880004a87a0000000000000002169c800021f0001b30000001d01088001c20b68000001710002299d916b10816190f0e8a6f0489041e18001ab00000000000000000000000000001d8000000002548002350000002080c10000000000510df8001d8a7fab78001d8244ab70dca140000348740161662b291100000000000000000000000016400000004e2868608f50000a50000000000ec83580000006fa7f00028491b80000009e0001e085d85c0000000000af8000000000ff00004300000012f0680000000001750000f20b31740938000000398002748001771819a600002392381ea1e99ca4305908f00028c9ec95427100000006683b80000010a0000be0001881568ca0000ea03d0001038528098000a48000000000000ad0c30320000000858000000899979e31310000000000001092b98490442258000002bd1f60001ed05e0000002740611500000002438000002af17e0002
  | 10 => 0x25980000024d0000c58ab80006514017e8002a21550001b196ea212238f12152bda120000000000000462b51ee25629b95d08aa359ef8000000000001f299a9050002160001188002260002558000000000001220000000001ab80026380000016899b00000000015b11b0d60000e980022897a08318b2b68dd8001348001e900000014584700000000000000028c22e1b39c617f21fa4e9b908104f8fd15d8aa80025e8018c90d72a51419760000000cc93780000000000019f1be064a8e0fa00000000000001997f8f28001c300000000000002d000000100015a7c0960379441ad151ab20000db1ca00c20f29d20c0a2a4a236878800166a5e0000002931b2129000000147a3210e95580009a8110002c113880000000002ea9a0000001c1a658001738972398eb8b5000045a6721391f0000000000602878000000002030002b388a09c0ce26b8001a188d80013a11d8002008000000000b80000000002c41190001e5816aa485f1719a58000002aa018a642920570000000000000000b2000000096a228000000000002ac8000cf8000bd9d2290975a988001b983600b8000000280002770000000db8000288002268000ae8000000000000000000109468000000000002720318001db20b8001b680000019f8000000000180b180000000000000000000000018400005d1fe80000000ea820002738000001af1c585a8000b61590000002ad8001d283f0000000ba9b800000000000018a8ac8000000000000620000000c780000005a00000000000000015089800028900006600010180000000000008800000000009000006c8ed06702d80000028a80001f00000000001280000000000000022325d9709101a28002858000ca80000000000000000000018204e8000000402c180000000002f0d91da1f18000000000000000c00e180001e00000e0001b10001dc9fd9992b005589d89100000000015c1272108000b89a88000e7a0a82c87b87600000010700000020c9fa80012b12b8002408001d087327b0219ac14602080000a0001f78001608000001108000000000001cf92987fa810f90002ab18ea17a7d8001628000a89358a780014aa0b14e00012880000000000000000000000498e25200000023f92d8000000000000000000d78000000000001bd00000000009280013d97b0c80001d68562a82209269cf0c094f8478000000000001031ba00016c0000000000000002808b28000000002518002c58691f40002910480de972a5280026c8000001f98000000001910f080029e00003800003c80028d88c8000001700001f09430001c91b48002818e500000000023b12e1a329423a06180016389500000024e1aa1fb0001eb00014c00000029021b0c299c2ab8c18001848000000000000000000000001e68000efaa089300
  | 11 => 0x23c28b04380022f82a9f5aa19178958000778000000070000e08002ad00000006a00000000000002c00000010c2580001890001580ea8000b7a6b27d00000000003b00006f0000d39d38001012aa88c05c80009f0000000000148000002688000bf0000001f100019e8000000001f200000006e8000000000579c880000009980028f8000990001e50ee80000012607aaafa1a000295ab111aa950001e4a5b2b49db8af0cd00d1c680c8d525b9ff0fe8002479548bd1942110000248f68b10d68000068002171b4254293a2a9b08a42508fb04b0629a08000000b70000000000002590000000000fb8001068001e01521ad8a600027980029eabb97a8000002c28f8800000149abfa18a14a5a2a302a18b8001560000002c4a6609200787e80000000000000015994811c80000000000000005226aa24a038000000a38000509f31de00293f2b3
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x10e166454f2188652ba6ca90843315cf6548421a4ce9b2a4210d4673d952108662b9ec890843199da5448421a8ce72a24210e25641512108652ba6c690843199da5348421a4ce929a4210e456314d2108652ba0c090843315cc6048421c48c890aa010e4463485500870629ac5a1a818514d61d0d40a4ae3a18a4a060d6314b425030a29ac3a12818914961d0940a4ae5a18a2a051573d08515030629ac5a0a818358c52d0540c2ac628e82a0625621474150306a9cc5218818554e6190c40a4ce321aa42060e6354a421030aa9cc3210818954a6190840a4ce521aa220516739095110306a9cc5208818398d5290440c2cc6a8c8220626625464110306a98c4a00818318d5250040c2aa630a802062552185401030a31aa2a0081891895150040c18a8b14869861454586434c2a2b8c8629261075d854cc930c1ac8296649861454587324c322292c399261515ca4314530a2ae9990a29841d76153314c3062a2c598a618359052cc530c2ac828e629864562147314c306aa4c5a18618555261d0c30a8ce3a1aa41841f76552320c307322a51906185552618c830c8aa530c641854672d0d510c28b3a464a886107dd9548c430c1aa9314621860e6454a310c30b322a31886191989518c430838ecaa2601860d54189300c306322a49806185550614c030c8aa430a601861464545300c322312a29806183151639092089aec29c849062454586424832229ac3212410b5d8548c920c1ac829c649062454586324832229ac319241515ce4214520a4ae9190a29042d7615321483062a2c790a41135d853c8520c1ac829e4290625641472148322b18a390a418355263d082089eeca9e8410625549874208322a9cc3a10410bdd954cc820c1cc8a9e6410625549873208322a9cc399041519cf4254420a4ce9992a21042f765522108306aa4c71084113dd95388420c1cc8a9c421062664546210832331aa3108410b1d95448020c1aa831a401044c7654d2008306322a690041895506148020c8aa630a401062464545200832231aa2900418515163905108aaec29c82886245458a414432229ac520a21195d85290510c8ac6294828843576152314430ab20a718a2189151628c510c88a6b1462884657614a3144312b20a518a210d5d85488510c28a8b1c42884557614e214430ab20a710a21895905288510c8ac629442886155498f410422bbb2a7a08218955262d0410c8aa731682084677654b410432331aa5a08210ddd954cc410c2cc8a9e62086255498b3104322a9cc59882119dd952cc410c4cc8a96620843776553210430aaa4c79082115dd953c8410c2cc8a9e42086266454b210432331aa5908210d1d95444010c2aa831a20084547654d100430a322a688021895506244010c8aa63122008464765491004312322a4880219118d5244010
  | 1 => 0x4210a8739ecaa1085499c7655084294ae3b1a842160f6394d4210a9338ca6a1085235cf615084291ae630284214a5711814210b0731a85288858318d4254042c4a8430aa02160d5498b43ccb0aaa4c3a1e65839516390b32c4ca8b0c859948e7610d42ccaa2b9c8528e65519cb4354732c1ca8b14871961654586438cb06aa4c7a14658955261d0a3291eeca18851941d76953328cb0b2a2c3994650bdd954cca32c4aa930e65195457290e518ca8aba66528c65519cf4254632a4ce9992a31950e7510f424cb0732e862126543dd54390832c1ecb21a841948d74d95320ca62b8eca99065439d3654c832a8ce3b2a64194c571d91320ca273b4a89906583d92544c832a8ce32a2641960d64151320ca46ba6c299065235d0604c83298ae2302641960e644ca510cb0632264a8065914c86154032c1aa731487a0e155398643d069338c86a96838398d5290b41c2aa730c85a0e255298642d070729ac5a1c838594d61d0e41a4ae3a1ca520e0d6394b429070b29ac3a14838994961d0a41c1ca6b168320e0d6394b4190722a9cc5a0c839198d52d064192ae7b2a8220ca572d95411068b39ecaa0883499cb655044194ae5b1a8220e176394d4110693394a6a0883255cf6250441a2ce72928220c95731814110652b90c0a08838518d4154041c48c4a0aa020e0d5498b43cc70aaa4c3a1e63519c74354b3183eecaa46598e0e6454a32cc70aaa4c3196639154a618cb31c2ca8b1c8398e265458a41cc632bb4a520e639158e529073192cec21a8398e0e5458a438c70b2a2c321c63515c64394a3183aed2a66518e0d6494b328c70b2a2c3994639194961cca31c2aa931e8318e255498b418c633bb2a5a0c639198d52d063192eeca188318c1d76953318c7072a2c598c638359252cc63186eecaa66318e255498b318c713322a598c63459d443d0531c2ccba188298d177550e410c70bb2c86a0863255d3654c43198ae5b2a6218d1674d95310c6a3396ca98863315cb644c4318aced2a26218e1764951310c6a3394a89886385590544c43192ae9b126218d1674949310c64aba0c098863315c8604c431c28c898aa018e44624c5500c706aa4c7a164313dd953d0b21c4aa930e8590e455398742c8617bb2a9996438399153ccb21c4aa930e6590e455398732c870b2a2c720e43155da5390721c4ca8b148390e465358a41c861abb4a918e4385592538c721c4ca8b146390e465358a31c87072a2c721443135da5390a21c4ca8b0c8510e46535864288616bb4a91944383592538ca21c4ca8b0c6510e4653586328870aaa4c7a0c4315dd953d0621c4aa93168310e455398b418861bbb2a998c438599153cc621c4aa93166310e455398b3188616bb4a990c438395163c862189aed29e4310e0d6494f218861bbb2a990c438555263c86218aeeca9e43
  | 2 => 0x110188002b8593a409000003641306cf5224f9518002d4181a08d4cc003c12f2a82653000450005a1494b00d00000454cc19c2c000d51ad3b3049f000e4000dc000ed38c00000fe460c92f8d42145156d293e043000b742c0049c002d1671003546cef00071000ca0e80050c6a31400000000016907c00110604596014c0000000080001e80042491378463dc9e4e5545749c55c4c058e24c8652f05447921534414802508558000700a400000a6000722740045c002e80000108000000000051c000cc0033d374a8784f8b0000000489a13d0f280fb05c5539c07578040b923174e61905f16073290f15000e1f86334800528991b94f28d34259244c023108d3000d60a0d100000220bd148690a845498eb43014124573fca723c98004005042b414000ec15465380e47c1d474568004d40015836374b30208e590314a0c316cc70bd114f565494100686c134b82b40a474792a0d70c91a2180052ce53210a3a08343492090f64009303c760000026cac0000000000000a1000004fc00208000000000112000000004a2100057cda0fd13001030451f0c0bf3c8c41200038000360b20000000cb641cfd1eca92c40658ca5000bb000003b022000e1000c61b47d12c024f000000cd34037228002543400000000004ac610000025c1c3f0a24041e51480000ab178af1980c2052d410005388b2503d521565641d408191fd614e8770f1064b9365ac000005a00000014000008c11d624c400000f400166001550003800144138b95a8f300027470ea1bd523b8db1400021c000000002d223090e00142000cb3e800170ce000df0f8c0571530b55054400240190081c04150103802021081c00010100c0408000184403038a00600040080003000042a000080806020100800000002c0000000000600018001800000003a020001008060080c0000040040603100040200000502807038000407058040a12020000201018083e06058240003028280211068081609020241212088001c060001014050380c020ba4ae3a1ca521d4671d0d5290e92b968728c87519cb435464391ae5b2a8621c9571d954310e87396caa1887459c76550c4392ae3b128621c8d72d854310e46b90c0a1887255c46050c43a1ee4a1ca421e15439865210e8bb8a87288878350e6294443c1a86312a021e15431855010f06a9cc521e858554e6190f42a4ce521aa3a160e5358b4390b0b29ac3a1c858594d61d0a42c8aa730e852152572d0e5190a8ab9e8528c85519cf425464291ae7b2a84214a571d95
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x100080f87590544c83281787590544c431
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 830
  | 4 => 1423
  | 3 => 364
  | 2 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (25446+((h/276+packedAt s2K5 (22410+(h % 276)*11) 11) % 1325)*11) 11
  | 4 => packedAt s2K4 (59762+((h/474+packedAt s2K4 (54074+(h % 474)*12) 12) % 2747)*12) 12
  | 3 => packedAt s2K3 (18925+((h/121+packedAt s2K3 (17836+(h % 121)*9) 9) % 480)*10) 10
  | 2 => packedAt s2K2 (123+((h/1+packedAt s2K2 (120+(h % 1)*3) 3) % 5)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffc0ffffffffffffffc3ffff
  | 1 => 0xfc1f03f83e07c0ffff1c1c1f0e0f87c3fd5293
  | 3 => 0xffe003ffc007ff03ffe01fe00ff007fc3e631c
  | 4 => 0x3fffff80003ffffe0000ffff8003f83e0
  | 5 => 0xfffffc0000000003fffffffff00000003ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4000008000000000000202100108040000425
  | 1 => 0xa946659194aa95d1cb0d0d1a268d168b9d5292
  | 3 => 0x30caaaa28d353456d56217484ba42738ae6318
  | 4 => 0xa294d34529a1a69b66b742108dce72113783c0
  | 5 => 0xc318e38631c638e3b8db9b9ce10844223bf800
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36581
namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2f4e5c70020005800050080126559604614111080da318b051a06540004414380267879d383551242193293e1002d000122e4a1400016852c502e3c414e010ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6a0a0015004410c00043000012e00002d04418572c80e002a960b80000000fa1d08820b245388f416415493c52063a9c800a01600000000029170000e22c50b0300e088665980000b600000ceaf1d87920962e80064733b2b06a8a468cc7400001784e7a5c800628016a7800912b1bce8835514400005aa6c6e2634a841e0000008844d3d968007732a2024003716c00393c8d01a004c0013a000523ca6a30080000000a800000000000fe4b4d084d69240938007812a24f813018393200000003463101a054a6000000095122dc565f17270da8617ac47c19239c020160d83078364f8014e00001014423029250e8428000a40004a14980036000c4ab0f9840000000fcae173223894935695118464a294007e240007c000400140008080028341020041c04041400181414401400083c040000000c04200420280404100c0c00340000000410103434041404000c00244006dca5a1db54b43bb28e877551d0f5ca5a1cf54b43d6a96872d52d0f6ca3a1cf54743daa8e873551d0e7ca1a1cf55243cfa9a873f5250e7ea2a1cf141439f2a0875e53d0abaa7a15d94742baa8e859e53d0a7aa7a16754f428ea9e85b651d0a7aa3a16d547429aa8e853e50d0a7aa9214fd4d42d7a92853f5150a78a0a14f950429f2a6653d54ccb5a85995d94732baa8e653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86196b50832e6990655e53d06baa7a0db94b41b6a96839e53d067aa7a0e754f418ea9e83ae52d067aa5a0eb54b4196a96833e50d067aa920cfd4d419fa9283b75150678a0a0cf950419f2a6633d54cc6dca598db54b31daa0e633e548c67aa918e750e31b7294636d528c67ca898cf551319f2a0633d540c73a8618ed50431ea988633e54c867aa990d794f21aea9e43b541c867ca910cf55221af29c435d538875a8510cf951219eaa2433e540867aa810eb50821daa0843e5210867aa7204f54a409ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298813d531033aa6204754c40d7290813d521035aa4204b54840db288813d511036aa2204d544409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c835a85904fd52209e2a4413f5448278a89057d4d20ae29a41ad42482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x44a6a4e8c5e4c9e3452063e8e540026501a00446c00001ca42a380a80007e0030746e2c66009a362e2298189000623a720058244240767a005a84005682789602a6927c0e943c001400000016a246701000006888320086081e601228208a9c640c48a05c00040840810b8004284995274581004c00e0010402041c78dc954a51d0f265254743c954951d0e8e62d4d43a59875350e3561d49438b58b5150e2d62141438d5845050f155394742c594d51d0b1553547428d5875350a8e63d4942a99875250a1d63d45428758c5050a356114142c950a51ccb1543946328758e544ca2d62951328d586544ca356195032a3591320cb0d5394b41c394d52d070d5354b418b58b535061d63d4941a598f51506a662d45418758c505062d6214141c994941cc70d4394a318758e544c62d62951318d586544c62d6295031a5591310c7165350721c394d428861d63951218b58a544863561951218758e54086a564484218bd8953902376154e4087d8d52902376154a4087d8d519022f6254640c354e521030e5354840c354d52103155394440c954a51103165354440c554d51103265254440c9549511022d62953308d58654cc22d62152308d584548c21c6550d30c350c524c31543145308758e54c823561953208758c548823561152208b195424830c5350920c9508514821d63953108b58a54c421d63152108b58854842346550510c514d41443245250510
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
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
  | 5 => packedAt s3K5 (864+((h/16+packedAt s3K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s3K4 (5518+((h/62+packedAt s3K4 (5022+(h % 62)*8) 8) % 246)*9) 9
  | 3 => packedAt s3K3 (3388+((h/28+packedAt s3K3 (3192+(h % 28)*7) 7) % 101)*8) 8
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffff87fffffffc0fffffffe07fffff8ff1ff
  | 1 => 0xc1f03ff83e0f83fff1c1c1f0ff878787f54e93
  | 2 => 0xfe003fffc00ffc1ffe01fe00fff807f8798f1c
  | 4 => 0x3ffffff0001ffffe0000fffff8007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x40000080000000000002021000088080001025
  | 1 => 0x946659119495270cb0d0d1a26c851517354692
  | 2 => 0xcaaaa228d2a613556217484b5502671598b18
  | 4 => 0x294d344529834a5a6b742108da6670226e0dc0
  | 5 => 0x318e387631cc739f8db9b9ce1c4444447fe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaaaaaeaeaa8a8eaeaaaaaeaeaa8a8eaeaaaaaeaeaa8a8eaeaaaaaeaeaa8a8eaeaaaaaeaeaa8a8eaeaaaaaeaeaa8a8eaeaaaaaeaeaa8a8eaeaaaaaeaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36581
namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xdab4e21700003d3000000019004c58e343000000000000000014147162f482401000a8105000141200b4687406020000000000054f233a000a12c5c180000000000a52804400000000000000440003e00006000000080020008108080060000081ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xcea804c000009e002591eab36001126e248d80000020ec7e0000000000038a6c16000000000000025c00000f8b088123b898007b350008c58412b03400000ac660f00000000000000800000000001300028000004818000030000009f001500000002c40072080656e00001a54667430e9148c002c84200000014e000010cfe0e408000000002a54c00100007c1e468e400482721c0000420007a0008800000000140f46500070007d52a74c200288540027168000000002cc840000000bab55c238968b5213572074a834004c029e42ea15726864830d8005463001f800002b000b2762500000000000000003680082ad0008c0000000000000000009e003a2a0b8002d8a4bc00000006a0055000005a170300000002d15e002a8d000005b1bcf0002f800f831001c0000000000a40000000a69c000012600000000016488003a88002510a0200800010000402000001004040200000000100000000080c0003000000a010000002000080800050000002000002c02010100c000000000100201800020000808000103002dca5a1db54b43bb28e877551d0f5ca5a1cf54b43d6a96872d52d0f6ca3a1cf54743daa8e873551d0e7ca1a1cf55243cfa9a873f5250e7ea2a1cf141439f2a0875e53d0abaa7a15d94742baa8e859e53d0a7aa7a16754f428ea9e85b651d0a7aa3a16d547429aa8e853e50d0a7aa9214fd4d42d7a92853f5150a78a0a14f950429f2a6653d54ccb5a85995d94732baa8e653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86196b50832e6990655e53d06baa7a0db94b41b6a96839e53d067aa7a0e754f418ea9e83ae52d067aa5a0eb54b4196a96833e50d067aa920cfd4d419fa9283b75150678a0a0cf950419f2a6633d54cc6dca598db54b31daa0e633e548c67aa918e750e31b7294636d528c67ca898cf551319f2a0633d540c73a8618ed50431ea988633e54c867aa990d794f21aea9e43b541c867ca910cf55221af29c435d538875a8510cf951219eaa2433e540867aa810eb50821daa0843e5210867aa7204f54a409ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298813d531033aa6204754c40d7290813d521035aa4204b54840db288813d511036aa2204d544409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c835a85904fd52209e2a4413f5448278a89057d4d20ae29a41ad42482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | 1 => 0xa1241423a64c445122880000002404473000000000000616000000000000000000068320000037000000000332807000128000000008005e020000078000015c000018020000035800000000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x421e0018860000004036007e06685e005600520400000000009676008c08000062009a00008032a4a2001600007226540c4c900000001c00120000305878849e3c5a50003e2a006c3a224400460088604824008a105ca6a00000340000000038008e00000000000000009c74640e2000001400926a2e288200000002000000007a002c944a1a007c664e986e0a70000000000000000002010601030000000103020300000204010000000101000100c954a51d0f265254743c954951d0e8e62d4d43a59875350e3561d49438b58b5150e2d62141438d5845050f155394742c594d51d0b1553547428d5875350a8e63d4942a99875250a1d63d45428758c5050a356114142c950a51ccb1543946328758e544ca2d62951328d586544ca356195032a3591320cb0d5394b41c394d52d070d5354b418b58b535061d63d4941a598f51506a662d45418758c505062d6214141c994941cc70d4394a318758e544c62d62951318d586544c62d6295031a5591310c7165350721c394d428861d63951218b58a544863561951218758e54086a564484218bd8953902376154e4087d8d52902376154a4087d8d519022f6254640c354e521030e5354840c354d52103155394440c954a51103165354440c554d51103265254440c9549511022d62953308d58654cc22d62152308d584548c21c6550d30c350c524c31543145308758e54c823561953208758c548823561152208b195424830c5350920c9508514821d63953108b58a54c421d63152108b58854842346550510c514d41443245250510
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
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
  | 5 => packedAt s4K5 (880+((h/16+packedAt s4K5 (768+(h % 16)*7) 7) % 99)*7) 7
  | 4 => packedAt s4K4 (5580+((h/62+packedAt s4K4 (5022+(h % 62)*9) 9) % 358)*9) 9
  | 3 => packedAt s4K3 (3416+((h/28+packedAt s4K3 (3192+(h % 28)*8) 8) % 147)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffff87fffffffc0fffffffe07fffff8ff1ff
  | 1 => 0xc1f03ff83e0f83fff1c1c1f0ff878787f54e93
  | 2 => 0xfe003fffc00ffc1ffe01fe00fff807f8798f1c
  | 3 => 0x3ffffff0001ffffe0000fffff8007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x40000080000000000002021000088080001025
  | 1 => 0x946659119495270cb0d0d1a26c851517354692
  | 2 => 0xcaaaa228d2a613556217484b5502671598b18
  | 3 => 0x294d344529834a5a6b742108da6670226e0dc0
  | 5 => 0x318e387631cc739f8db9b9ce1c4444447fe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36581
namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1810c80008d59e2ca07004c0908000011002420000009100a16a8e033625487225cf93305469034147810c94a27007560f2123cd1022002d508c242ff43bf43fe43de43fd43bd43dd439d43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc008101b49a001a9680a0700150900000104f80a3980076752983492000e99822770d84c4c470d12cf03601000027d1a1c8d4001e09464390017832180000070652b0dc5e0f31984f245358b4000309000aa0027000424c001d0e0003f1d87e001499c00000480000001100000000012800001885cd00b290cc3e000005808001400000620007000151f16454571580000503d110fe000016000420017c4e1017038181440170e23d36100603a32118486e0f1ec864f288b0d25b031bcba2305078380000002800485810200000080838782000580828604130d001080010200160580838281000f03814f55243aeaa4871d5490f3ea6a1e7d5143cfa92879e5250f3aa4a1e714943cfa8a879e5150f3aa2a1e714543cfa82879e5050f3aa0a1e7141439f2a0875e5310f3a8621d794f42aea9e859d43d0aeca3a15d54742cea1c859d4350abca6215754c42cea18853e54cca7aa9996750f32bb28e657551ccb3a87196750d329f2a0653d540cb3a86195794f41aea9e839d43d06dca5a0db54b41cea1c839d43506bca620d754c41cea18833e54cc67aa998e750f31b7296636d52cc73a8718e750d319f2a0633d540c73a8618cf953219eaa6435e53c86baa790e750f219f2a4433d54886bca710d754e21cea1c439d434873a8610f948421af29e815d53d033a87a06750e40cea1a815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc33a87986750e30cea1a613e540c27aa8186750c30b7290616d520c2eca2185d54430cea1e419d438827ea8904f15120afa9a415c534833a86905dd4520ba28a413e540827aa8105794c20aea98419d43082eca2105d54420cea1e219d438427ea8884f15110afa9a215c534433a86885bd4910b6292213e540427aa8085794c10aea98219d43042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x138000208b000d80000408000000031400000000000002a18c8480000998001300000e801f8d18861a9285950196999017000000001d001780210000160b80000000009f1c02071e068a159e850a80001480000000038c00200007801b80001b0e09121c8000088000001a0f91811d8000110010990f0200080000010100020a0018506202800438104a59875250e9561d4943a59865250e956194943c35485250e8e62d4543a358b5150e8e6294543a358a5150f155114543a3d895050e8c6254143a5d855050e946154143a39885050e8d6214143a59845050e956114143c550e51d0b154354742c550e51ccb154354732c350e52d070d4354b41c350e52cc70d4354b318758e54c861d6494f2187d9543c861d6550f218758e548861d6494e2187d95438861d6550e21e150d210870d4394840c350d52103154394440c550d511021d6355030c350e520c30d4354830c550e510c31543544308758c544821d6414d2087995434821c6550d20c550f514831543145208758e540821d6494c2087d95430821d6550c20c550e510831543544208758c544421d6414d1087995434421c6550d10c350f524430d43149108758e540421d6494c1087d95430421d6550c10c350e520430d4354810
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 5 => packedAt s5K5 (810+((h/15+packedAt s5K5 (720+(h % 15)*6) 6) % 55)*7) 7
  | 4 => packedAt s5K4 (3827+((h/43+packedAt s5K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s5K3 (2738+((h/22+packedAt s5K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x87ffffc3fffffff03fff07fff07fffff38f1ff
  | 1 => 0xf83e0ffc1f07c3ffc707f8787f87870fd74e93
  | 2 => 0xffc00fffe007fc3ff807ff807ff807f0e78f1c
  | 3 => 0xffffff8003ffff800007ffff800f80fe0
  | 4 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x80000040000000000008008800088100001025
  | 1 => 0x128c9488ca4a8612c34348513485122e534692
  | 2 => 0x219529114695206558859502595024e2a58b18
  | 3 => 0x7529ce2294c1aab9add0c4446e667044f80dc0
  | 4 => 0x46318c3b18e6333e36e6e6670c444088fee000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36581
namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x484e6ba459448c434000560001680a52003b944990060001002e41ed878bc6538d50c5080b8a3444e073faa18b2a98205590081d000000e369c014292678aa656f8e051a0000e0000003420010b0600a81000007ff53017f94c01fd53017f14c05fe43007f50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffcc803fe3200ff4c803fc3201ffd4401fe51007f54407fc51017fcc401fe31007f4c405fc3100ffc8403fe2100ff48403fc2101ffd4001fe50007f54007fc50017fcc001fe30007f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c200dff10e10027fec508012ff6284009ff3142001bf98a10027fac508032fd6284009fe3142004bf18a10067fea5080337f5284019ff294200cff54a10066faa508033fc5284019ff994200cff8ca10067fa6508033fc32840137eb0c200effd4610007fca308003fd518401dfe28c200dffcc610007fc6308003fd318401bfe18c200cffc8610067fc4308033fd2184019fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9042004ff08210027fe2108013f71084001fd8842000ffd9510005feca880037f65440013fb2a200bff9951001dfcca88003fd65440017eb2a200bff1951001df8ca880037c65440073e32a2000ffd8d10005fec688003df63440016fb1a200aff98d10015fcc688003fd63440017eb1a200aff18d10015f8c688003dc63440056e31a200bffd4d10057fca688003fd5344015fe29a200aff90d10007fa868802bfc4344013ffb122009bfd8910007dec488002ef6244013ff3122001bf9891004ffac488026fd6244013fe3122001bf1891004fd8c488006ec6244013ffa922009dfd491004ffca488027fd5244013bea922009ff1491004ffe6488027fe3244013fe9922009ff0c91005ffea288003fe5144001fb28a2000ff54510007eaa28802ffc5144015ff98a2000ff8c510007ec6288003fd3144001fa98a200aff0c51004ffe4288027fe2144013fb10a2009ff4851004fea4288027fc2144017ffa822004ff94110007faa088013fc5044015ff9822004ff8c110007fa6088013fc3044013ff9022004ff8811004ffa4088013fc2044001ff8822000fec4110027fc2088013f61044009ffb282004bfd9410027fcca0800efe6504009bf32820039f99410027faca08002fd6504009beb2820009f59410027f8ca08012fc6504009ffb182004bfd8c10027fcc60800afe6304009ef3182002b798c10027fac608002fd6304009eeb182000b758c10027f8c608012fc630400fffa982006ff94c10007faa60801bfc530400dff2182000ff50c10037f88608013ff62040097fb102004ff9881000dfcc408013ee6204003773102004ff5881002dfac408013ed620400176b102004ff18810025f8c408017ff520400bbfa902005ff9481002ffaa4080177d520400bfe2902005ffcc81002ffc6408017fd320400bfe1902008bf9841003ffea208003fe5104001fea882007ff14410037fe6208003fe3104001fe9882006ff0c41002ffe4208017fe210400bfe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0xbfd318c005fe18c6002f70c6300affe4318057fe218c02bfe90c6015ff08630025fcc118013ff508c009ff2846004ff54230027f8a118013ff408c009ff2046004ff10230027fe6118013df308c005fd9846004ff0c230027f06118013ff208c009ff1046004ff48230027f84118003ff654c0017fb2a6000dfd9530004feca9804ffe654c0077f32a6000ff59530005faca9804ffc654c0077e32a6000df1953001cf8ca98003ff644c0017fb226012ff991300a5fcc898003fd644c0017eb226012ff191300a5f8c89804fff544c025ff2a26000ff55130097f8a898012ff634c005ffa9a6002ff94d30017bca69800bfd534c001eea9a6002ff14d30017fe869800bfe434c005ef21a6002ff50d30007ba869800bfc434c023ffb126011bfd893008ffcc498006fe624c023feb126011bf5893008ff8c498006fc624c023ffa926011dfd493008ffca498047fd524c023bea926011ff1493008ffe8498047fe424c023fea126011ff10930017fe649800bdf324c005ff1926002ff4c93008fba649800bfc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf1853009ffea298003fe514c001fea8a6013ff14530097fe8298003fe414c001fea0a6012ff10530017fe629800bdf314c005ff18a6002ff4c530007ba629800bfc314c023ff90a6011ff8853008ffa4298047fc214c0057fb026013ffd4130027fca098003fd504c009fe2826012ffd0130027fc8098003fd404c009fe2026002ffcc130017f66098013fe304c009ef1826004ff0c130027b8609800bf8304c023ff9026004ff8813008ffa4098013fc204c001ffb2e2000bfd9710087fccb8800efe65c4001feb2e2000bf59710087f8cb8800efc65c4001ffb1e2000bfd8f1007ffcc78800afe63c4001feb1e2000bf58f1007ff8c78800afc63c4021ffa9e200fff94f10007faa78803ffc53c401fff21e2000ff50f1007ff88788023ff62c40117fb162008ff98b1000dfcc588023fd62c40117eb162008ff18b1000df8c588023ff52c4011bfa962008ff94b10047faa5880237d52c4011fe2962008ffccb10047fc6588023fd32c4011fe1962010ffd4710007fca388003f651c4001fea8e2000fd54710087f8a38803fff31c4001ff18e2000fd8c710007fa6388003f531c401ffe18e2008ffc8710047fc4388023f621c4011fe90e2008fd48710047f84388043ff50c4009ff2862000ff54310027f8a18803fff30c4009ff1862000ff4c310027f86188023ff20c4009ff1062008ff48310027f84188013ff65840097fb2c2004ff9961001dfccb08013fd65840017eb2c2004ff19610025f8cb08013ff63840097fb1c2004ff98e10015fcc708013fd63840017eb1c2004ff18e10025f8c70803bff538401bff29c2000ff54e1006ff8a708037fe4384001fea
  | 2 => 0x31007fec098802ff604c401ff3026200ff58131007f8c098812fc604c43dffa82621eff141310effe8098877fc404c405ff9826202f7cc131017f86098873ff204c439ff102621cff481310e7f8409880efd6594009ffb1ca004ff98e50015fcc728013fd63940017eb1ca004ff18e50025f8c72800fff5394007ff29ca01bdf94e5001ffaa72800ffc5394007be29ca01bff90e50007fa872806ffc4394009ffb14a004bfd8a50027fcc528006fe6294009feb14a01abf58a50027f8c528012fc6294007ffa94a003dfd4a5001ffca52800ffd5294035bea94a003ff14a500d7fe652806bfe3294035fe994a01aff0ca50027fec328013fe61940017f30ca004ff58650005fac328013fc6194007ffa8ca003ff94650006fca32800ffd5194007fe28ca003df146500dffe6328003fe3194001fe98ca01bff0c6500d7fe432806bfe2194035fe90ca01aff08650025fcc128013ff5094009bfa84a003fed4250027f8a128013f85094009ff984a004ff0c250027fe4128013fe2094009fe904a004ff08250025fecaa8003ff63540017fb1aa019ff98d50015fcc6a8003fd6354033fe31aa002bf18d5001ffea6a800f7f5354007ff29aa003ff54d50006faa6a800ffc5354033ff21aa000ff50d500cff886a8063ff62540317fb12a018ff9895000dfcc4a8063fd62540317eb12a018ff1895000df8c4a800fff5254007bfa92a003ff9495001ffaa4a80637d5254007fe292a018ffcc9500c7fc64a8063fd3254031fe192a000ffd8550005fec2a8003fe6154001feb0aa000ff18550005f8c2a800fff5154007bfa8aa003ff9455001ffaa2a80037d5154007fe28aa019ffcc550007fc62a8003fd3154033fe18aa018ffc85500c7fc42a8063fd2154031fe10aa003bfd815001ffea0a800ffb5054009ff282a004df94150027f8a0a80137c5054007fc282a019ffcc150027f860a8063ff2054009ff102a018ff48150027f840a8013ff658c0097fb2c6004ff9963001dfccb18013fd658c0017eb2c6004ff19630025f8cb18013ff648c0097fb246004ff992300a5fcc918013fd648c0017eb246004ff19230025f8c91805fff548c02dff2a46000ff552300b7f8a91800afd638c005ffa9c6002ff94e30017faa71800bfc538c005ffa1c6002ff90e30017fa871800bfc438c009ffb146004bfd8a30027fcc518006fe628c009feb146015bf58a30027f8c518012fc628c02bffa946015dfd4a300affca518057fd528c02bbea946015ff14a300affe8518057fe428c02bfea146015ff10a30017fe651800bfe328c005fe9946002ff0ca30027fec318013fe618c0017f30c6004ff58630005fac318013fc618c02fffa8c6000ff94630007faa31805ffc518c02dffa0c6000ff90630007fa831805bfc418c005ff98c6002ff8c630007bc631800
  | 3 => 0xfa9aa203ff94d5111efca6a880ffd5354407fe29aa203df14d5111ffc86a8803fd4354447fe21aa222ffd8951115fec4a888bfe62544037f312a222ff58951115fac4a888bfc62544037e312a203ffd495101efea4a880ffe5254407fea92a222df5495101ff8a4a888bff3254445ff192a222ff4c951117f864a880eff6154407ffa8aa203fdd455101ffca2a88037e5154407fe28aa203df1455101fe8a2a888fff3154447fe18aa222ffc8551117fc42a888bfd2154445fe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151025f8c0a880fff5054407bfa82a203ff1415111ffe60a888ffc3054445ff902a222ff88151117fa40a888bfc2054401ffb2c6200bfd963110ffccb1880efe658c401bf32c62039f99631007facb18802fd658c401beb2c62009f5963110ff8cb1880efc658c401ffb246200bfd9231107fcc918852fe648c401feb246200bf59231107f8c918852fc648c443ffaa46220ff95231007faa918883fc548c4057eb1c6202ffd4e31017fca71880bde538c405fea9c6200f754e31017f8a71880bff438c405ff21c6202f790e31017fa8718803dd438c405fe21c621fffd8a310fdfec51887ffe628c4037f314621fff58a310fdfac51887ffc628c4037e314621fffd4a310fefea51887ffe528c43ffea94621fdf54a310fff8a51887fff428c43fff214621fff50a310fff8851880bff328c405ef9946202ff8ca31017fa651887fdd328c405fe1946202bf9863110ffea318803fe518c401fea8c6221ff14631107fe8318803fe418c441fe20c6202ffcc631017be631880bf7318c405fe18c6202fd0c6310fffe431887ffe218c43ffe90c621fff08631007fec118803fe608c4097f3046200ff58231005fac118803fc608c443ffa846221ff14231107fe8118883fc408c405ff9846202ff0c231017b8611887fff208c43fff104621fff482310fff84118803ff654c4017fb2a621eff9953101dfcca98803fd654c4017eb2a621eff1953101df8ca98803ff644c4017fb22621dff991310a5fcc898803fd644c4017eb22621dff191310a5f8c89887bff544c43bff2a26200ff551310eff8a89880aff634c405ffa9a6202ff94d31017faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c439ffb12621cbfd89310e7fcc498806fe624c439feb12621cbf589310e7f8c498806fc624c439ffa92621cdfd49310e7fca498873fd524c439bea92621cff149310e7fe8498873fe424c439fea12621cff10931017fe649880bfe324c405fe9926202ff0c931015fec29887bff514c401ff28a6200ff545310f7f8a298877ff414c401ff20a6200ff505310eff8829880bff314c405fb98a6202ff8c531007bc629880bfc314c405ee18a6202fd0c5310e7fe4298873fe214c439fe90a621cff085
  | 4 => 0x802ff6454c53ff322a614bf99153007fac8a98a7fc6454c297e322a603ffd515301ffca8a98a77e5454c07feaa2a603ff1515301ef8a8a980aff6354c05ffa9aa603f7d4d53017fca6a980b7e5354c05fe29aa602df14d53017b8a6a980bff4354c05ff21aa602ff10d53147fec4a98a2ff6254c51ff312a601bf98953147fac4a98a2fd6254c51fe312a601bf1895301ffea4a980f7f5254c07ff292a603ff54953146faa4a980ffc5254c51ffa12a628ff90953147fa84a98a3fc4254c05ff992a602ff8c953017fa64a980bfc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa600bf1855301ffea2a980ffc5154c07be28aa629ffd055314ff882a980bff3154c05fe18aa602f70c553147fe42a98a3fe2154c51fe90aa628ff08553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9812fc6054c07ffa82a603dfd415301ff8a0a98a7ff4054c53fe202a602ffcc153017be60a980bfc3054c51ff902a628ff88153147fa40a98a3fc2054c01ffb2a8600bfd954313ffccaa180efe6550c01feb2a8600bf5954313ff8caa180efc6550c057fb1a8602ffd4d4313fbea6a180bfe5350c05fea9a8602ff14d43017b8a6a180bfe4350c05df21a8602ff10d43017b886a180b9c4350c4dffb128626bfd8943137fcc4a1806fe6250c4dfeb128626bf58943137f8c4a1806fc6250c4dffa928626dfd4943137fca4a189bfd5250c4dbea928626ff14943017fe64a180bdf3250c05ff1928602ff4c943137ba64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8600bf1854313ffea2a189ffc5150c05ff98a8602ff0c543017b862a189bff2150c4dff10a8626ff48543137f842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c097e3028627ffd414313ff8a0a180bff3050c05ef9828602ff0c143137fe40a189bfe2050c4dfe9028626ff0814301dfacb28803ff639444bff31ca202bf98e51007fac728802fd639444bfe31ca202bf18e5101ffea72880f7f5394407ff29ca203ff54e51006faa72880ffc539444bff21ca200ff50e5112ff88728893ff62944497fb14a224ff98a5100dfcc528893fd62944497eb14a224ff18a5100df8c52880fff5294407bfa94a203ff94a5101ffaa5288937d5294407fe294a224ffcca51127fc6528893fd3294449fe194a203bf9865101ffea32880f7f5194407fba8ca203ff1465101fe8a328897ff319444bfe18ca224ffc8651127fc4328893fd2194449fe10ca200ffd8251007fcc128812fe6094401feb04a200bf58251007f8c12880fff5094407fe284a203df1425112ffe6128897fc3094449ff904a224ff88251127fa4128893fc20944077fb2aa200ffd8d51005fec6a888ffe63544057f31aa200ff58d5111ff8c6a880afc6354407f
  | 5 => 0x92e9e712a082e1809805819b94498987287d59c9010000f11ad80000000022500003c8000001668000811bd8e04140001b780000000000013210f9c1db70f900014d80002d08984fdb801dd3b90717f8655e8ce4800141cf49c493c000031961c1109883c57a80022604e9c8c000c89ed85c9540f402380013c8000db1531aec0006a81f80399f8b91ec9b60d5000000109d5210c92a9cd976800180901d335969ea08c810d9012297b00000000000000014e1a180018d844000006da118e89b1e2000214a088eb8439a68ed80807a85b61684c1ff8018000e38000945d09379241e30304c702980019e11e9151b8cf6064019a1f2060000001280cb1500609dd9dfa270e69aa89614898498b0821700aed2493d43b81a8000000b58362292079c01219209680cd9198a5cd187894500019e4650869c817e0855e61d8d2c89b940483c450b79720fec968e81ec0220d81d903c020c0c0c186f00f85117817b91f46e87e91d8269d498dd4c9dd1e78480fd8cba0519303721204797299710600011c9ab9bc000800014008038060000140080a0000040280201a0481500000a04c01804000120008020080180100901a000008000000100280d01400c008010020640000801e020018000040300000800001c01800002024058000000200100300e000000090160080000200003c00002000000030000040000200000a00813000002000018130000000280a0200480c00000001c080000420000580f00a0100401100a0000400000400000000000038058010060040180b008018040080060140400b0000040000200000400007000004010050000000200000200c0180701a000000000020040281600000400806006008000000280040080000a0240200100000000000006004008000000100000401e00000005008004000020040200180002a0040100c0040080100e0000080000b0000000400200200c0400900006000802002040020090040000200002e004008060020040100400200804807000008008020000000000201a0180080000e024000030020380101f0200100280b010034088010240580080b00800c0200b0040100000e00200c0000100000002807000048008000080140080600c0200100001004c06805000008068060000000b8020000000500f00000002804000010020030080080000201a0000100000000800015008010008040320340101300000000000000018010140000080100f0160040380f0040180180000005400000002008010000040200280400000c0100800401c06009008000068050000000000003805c0401804600407000016004088000080200000800a00804001004004018060080040c0000000040100600600c0280c00c00c0000c006034040010020080100400000c0580500002bfd9553007fec8a9
  | 6 => 0x96c91298785bc758f721f9178879299fa2130c800020980000000010a19d000060c000894000000001f613a12d030c0021e93e00001714a1fa9a947304ac000365bc8dd9544af9708e7834a200a919112bda51631201e0c6608b0ff16f0f80000e980019400756392adfd93190f03d0000001e7e000f2a01827179a161cd5ac0000b300000c40000000000000000006d00019e897542c000c28001170000be0001cf0000c11e185060317e8c00691b41138119a30000000518001f51f004021b00000017d92b04c8201bb04cc4f021552c0020a1f7148097da084616e9e41b31270aa0000592241810002040e58b709d80000000000002e0001400000149d9470dda0000001e897a12390b0c640000011dc44a0f099049c600d70a00001a70000000df00009315a0c99fd1040359d19978000001510000000048939750000998001288000a71748630624a200000013994b91201e4000f50e70000908c597ec3a1d718906140005d0ab19980000b971176112527800038c790a30fb9a15d811ac3743204d8ae12b5da9f480000000000007d81a00012444ec9100e8e51788459f10fa9382159eb1a98ec07c11edd200000000de110cf81b00000000cd5f8b00089d280019a8000001558000002179b205586180000015b11610285d88616914b0000d280018b97d1418380000000229369b68af08a9c28000328f68001fc40008340000011f8001c50000850598db8000000000001730000000b680002a09c0e413b10242e908cee00d0000001ce9ef8091f404b1671ba98e02498d1c91b48b885f0001169d30e195f03693f06c1a78000001301ba0df89c9880e09efc341118000d89a480500008416880000021b873d3e80000014f8000001c5861c000ef1f940015795982b98c80a910074c5a4779b8400129000220800071c8b8288384001c38000000fc8001c60000000001628b50000001149b10000fe0de1b940d57199200000000200002f4be93cc0019198d5aa0000010000e31358800000d9057094d3ddae0ca9cf9008fa0001bcd790b120586984bd2c0000c219f00000012616cc001e151cc40932805c954d310800014a8001220fe8001adc7388451d0f78000c31e859506e0000000001a40da9fc824d871fea2689f18188a0160471ab0151d9d5191e5479ee9939d3895d410ca13242110b9f7c50104802a1707100003a88a54152d80010a51585b01b9be6070001570a184a10952120d0708dc00000003011f092c000000e0022c001f780004984105f96f8000001ce0168a49ce4000e1c001f20748530000351a59e38001bb4d600011bc1e9838000000000001d6c001c41d40068000000001fb8d00d8d5c1ac8b801e01fc000001df0689098001a88000ab8000704001ea80010580b0000b083f9fb4ec8000000659fe0000494000000d
  | 7 => 0x9a0dd0244000e92211b896401580000006380000007bc9e04e56b0979b900300000000014d14600013d20e0a080003b0001f197f4000001828c3865d6653d8d40d849aa298c6a0821d1db1faca887608d03cc001ee0225c14f880000004f80000010d0678001cb00f0da15b8000000000000000f592f8001088cdc3e8ae8d5a231edd6c0001c98000919661de0a3cc518f8ad9a222a00001161284b4529d102581f55696a9908870e11258000002068001ed5108000ac8a58000000130948000ce00014380000000011a8b38001d587c91a0000001db9af86d8000940000000002028000000001580000000ce9389a90000000000000000818000ed1340000cc00000011b9d980000010912ba2820aa1c911c520e20984aa82796b8bd8000cc9001741d88000a621004d06f80004d4000f1d4204680007000008c1c7898ce88489e98230dfc0000000001f00010d8bb901a0c09e8b2093c00049000000185993cea9dc1b51e802092f118821dd008900017c1068000001030001021da58c21a9a3940e0481d1b091b5b9d351408000a780007994300001d9f995514f0001d85ed00000013e46a1bdc000000a542910a9f91cd05a888c0008e9e521985c00000000000015080015603102f99b0ad16e19c1dc47e1bf0431204bc8a280000004b8001de9bac4e0000000c7800056a1e00000016204f61d9ccd6188f0671dc82c0399dadbd4001eec3e18693f4000060001bc4620078000000bf8000c080010c000020436dad0389af1800f30560260000baa2287cc001215f38f39af5591115440000001e00000d38001498002219dcc00012933d1816d9a2a090a99339429e5a038881961b7cf0082a0b00d8bf1131459949fa4508e24001e11e48000001fcc000000000000379eb80012693c4002288000000d486c94c1658c04001e922380008889f8c4a189cb9c882a86811d5468fc2249830d78a108d8929928744c421089201883f0acd491cc9539a620e98a9851958755b58781250000000000a80002138000fb00007258f0769bbc838000000000d995d82348e1a1c89cea0338de9f32011d68138715a8ccf0001d613700007a1608b98000000001db42b124d1b1ae84a5d78422150000000001cdc0001792a5ee4000000000a681ec37c001bf87b8c615480016a04c4cd0b411c0538000001fbdbe1f080019809d13306689347f8000001cc13fc001c1158874066c719739f683d8ee87d16d00015d00081003dc6f51fc72c548b29b195a89640000000000000016017c87c4000000b61ef40006b0120858484000f65361c68eb1d75c20000000126008001c18a50001425ef1039821a001cddbc4dcef800096d699ba5be800177930a0f98a00020c8001770000218af400123120c001ca0000750001b98419a80fd0000000a39f8c0013ec000251f5
  | 8 => 0xbd1651c95b39078ad50e9ff024010998a0d86106654e95e954de29f89e041c8f99b285892e0000001ae62793115293f9678bb01c00018883d5dd61402d8000000848770000001758d69990001b0132c5a00007f1470191141ca8000001f29d5011d349d7c4a82800c82f00000421c0a40951bd05ea1910511c4e287b0dc9391f80ac00000017f06fc0003313a91119a04285b8000ff9c315c88f8308d108080990e15e05ac48e220831840b48f0800095864805823ce60629c08000000390b1a021190541fc1f9d6102fcbc110c7347200a0f20000f198619d8000180578070ba22581d4901fb1c700005521a000084c2c8bfc5e00006ba0b9649e69e089700021180011e0064c90001bb8d200e0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd4258c10006dc4258c10036df7158c10006de7158c10006dc7158c10006df5158c10006dc5158c10006df4158c10006dc4158c10006df2158c10006de2158c10006dd2158c10006dc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026d71058c10026de1058c10026dd1058c10026d51058c10026dc1058c10004ff7654c10024fe7654c10004fd7654c10024fc7654c1001e7e6554c100067d6554c1014ebe6454c10006bd6454c10016de6354c10006dd6354c10146ee6254c10004ff7650c10024fe7650c10004fd7650c10024fc7650c1013e7e6550c100067d6550c10016de6350c10006dd6350c100379c4350c10136ee6250c10005f77150c10005f47150c10006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ee4358810006ed4358810006ec435881002eef7158810006ee715881002eed715881002eec7158810006ef5158810006ec5158810006ef3158810006ec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026e71058810026ee1058810026ed1058810026e51058810026ec1058810084ff7694410024fe769441001cfd7694410024fc769441001e7e65944100067d659441012ede6394410006dd6394410126ee6294410006ed6294410086f6619441003f775194410025fa7094410005f97094410084ff765441001e7e65544100067d655441011ede6354410006dd6354410116ee6254410006ed6254410086f6615441007cff768c410024fe768c410014fd768c410024fc768c41003d7e758c4100057d758c41010e7e658c4100067d658c410106be648c410006bd648c410016de638c410006dd638c4100feee628c410006ed628c41007ef6618c410025fa708c410005f9708c41007cff764c4100f67e654c4100067d654c4100eebe644c410006bd644c410016de634c410006dd634c4100e6ee624c410006ed624c41007ef6614c410025fb7644010006fb7644010004fb76440100077b75440100077875440100277a6544010027796544010007db7344010007d87344010027da6344010027d96344010007eb724401015fe87244010027ea6244010027e9624401015f7b524401015f795244010025fb7144010027f37144010156fa6144010027f26144010
  | 1 => 0xc110014fc764c1100057f754c11005d7c754c1100067f654c11009e7c654c110006bf644c110096bc644c110006df634c110016dc634c110006ef624c11008eec624c110005f7714c110005f4714c110007d5314c1100067f65c41100867c65c4110006df63c411007edc63c4110006ef62c4110046ec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41100077865c4110007db63c4110007d863c4110007eb62c4110167e862c41101677b52c41101677952c4110025fa71c4110026fb61c4110027f361c4110007f251c4110007f151c4110007f231c4110007f131c4110167f221c4110167f121c41100267f7559410004ff7359410014fe7359410014fc735941003e7f53594100067e535941003e7c5359410004ff725941000cfe7259410004fd725941000cfc725941003e7f52594100067e52594100067d525941003e7c525941001cff715941001cfd715941003cfc715941003e7c5159410024ff7059410024fe7059410024fd7059410024fc70594100267e50594100267c5059410026f71059410026f510594100067f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100047f72594100067e72594100067d72594100047d72594100067c72594100067f32594100067e32594100067d32594100067c325941003e7f71594100067e71594100067c71594100067f31594100067c31594100067f21594100067e21594100067d21594100067c21594100267f70594100267e70594100267d70594100267c70594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267710594100267e10594100267d10594100267510594100267c1059410004ff7558c1001cfe7558c1001cfc7558c10004ff7458c100a4fe7458c100a4fc7458c10026df7358c10006df5358c10036de5358c10036dc5358c10006df4358c10036de4358c10036dc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10036df3258c10006de3258c10006dd3258c10036dc3258c10014ff7158c10014fd7158c10034fc7158c10036dc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026f71058c10026f51058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c100065d5258c10006dc5258c10006df4258c10006de4258c10006d
  | 2 => 0x6ef30d89101c6ee30d89101c6ec30d89101c6ee10d891004eed10d89101c6ec10d8910074fe76945100067f659451001e7c6594510006df639451012edc6394510006ef6294510126ec6294510005f67694510076f6769451005df5759451000777659451001ef6659451001ef4659451005f74659451001e746594510005f57394510007d76394510007d4639451005f7753945100077553945101bdf772945101bdf57294510007e762945101b7e4629451005f7752945101b7755294510025f67094510025f470945101af7650945101af745094510024fc76545100067f655451001e7c6554510006df635451011edc6354510006ef6254510116ec625451005f745154510005fb7054510025f87054510025f4765451001ef47654510024f4765451005df7755451000777755451000777655451001ef6655451001ef4655451005f746554510005f77354510007d76354510007d463545101a776535451005f74535451019df7725451019df57254510007e76254510197e4625451005f775254510197755254510007f37054510025f67054510025f47054510007f0705451005f77505451006cfe768c51005d7e758c5100057d758c5100067f658c51010e7c658c510006bf648c510106bc648c510006df638c510016dc638c510006ef628c5100feec628c510005f6768c51006ef6768c510005f7758c51000776758c510005f5758c51000775758c51000575758c51000777658c51000774658c510005f7748c510005f5748c510007b7648c510007b4648c510055f5738c510007d7638c510016f6638c510016f4638c510057d4638c510016d4638c510057d6538c510007d5538c510057d6438c510007d5438c51018df7728c51018df5728c510007e7628c510187e4628c51018777528c51018775528c510057d7328c510187d5328c510025f6708c510025f4708c51017fd6308c51017fd4308c510024fc764c5100067f654c5100f67c654c510006bf644c5100eebc644c510006df634c510016dc634c510006ef624c5100e6ec624c510057d4314c510005fb704c510025f8704c510025f4764c510016f4764c510024f4764c510005f7754c510005f5754c51000777654c51000774654c510005f7744c510005f5744c510007b7644c510007b4644c510055f7734c510007d7734c510007d7634c510016f6634c510016f4634c510057d4634c510175f7724c510175f5724c510007e7624c51016fe4624c51016f77524c51016f75524c510007f3704c510025f6704c510025f4704c510007f0704c510057d7304c51001cff765411005cfd765411001cfc76541100067f655411001e7c6554110006df63541100cedc6354110006ef62541100c6ec6254110005f77154110005f47154110007755154110014ff764c110054fd764
  | 3 => 0xe21d8d10006dd21d8d10006dc21d8d10006df70d8d1017ede70d8d10006dd70d8d1017edc70d8d10006df50d8d1017ede50d8d1017edc50d8d10006df40d8d1017ede40d8d1017edc40d8d10006df20d8d1017ede20d8d10006dd20d8d1017edc20d8d1017ede10d8d1017edc10d8d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d101d5bc7458d10006bf6458d10056dc6358d10005ef7258d1004dec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d100a4fe7458d100a4fc7458d10006bc7458d100a4bc7458d10054ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d5258d1006cff7158d10006f77158d1007cff7058d10006fb7058d10005de7618d10056de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d100075f5218d100075d5218d10057d57118d101cedf6118d10007d62118d10007d52118d101cfd61018d101cfd41018d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d10006bf6454d1014ebc6454d10006df6354d10016dc6354d10146ec6254d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1013e7c6550d10006df6350d10016dc6350d100579c4350d10136ec6250d1004dee76d891004eee76d891000cee76d89100076f75d89100076c75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89101c7e771d891004fe471d89101c7e610d89101c7e410d8910006ef75d89100066f75d8910006ee75d8910006ed75d8910006ec75d89100066c75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d89101c6ef71d891004eee71d891004eed71d891004eec71d8910006ef51d8910006ec51d8910006ef31d8910006ec31d8910006ef70d89101c6ee70d891004eed70d89101c6ec70d8910006ef50d89101c6ee50d89101c6ec50d8910
  | 4 => 0x95100067f32d95100067e32d95100067d32d95100067c32d95101ae7f71d951005e7e71d95100067d71d95100067f31d95100067c31d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95101ae7e70d95100067d70d95101ae7c70d95100067f30d95101ae7e30d95101ae7c30d95100067f20d95101ae7e20d95100067d20d95101ae7c20d95101ae7e10d95101ae7c10d951005e7c6559510005df7359510055dc7359510005ef725951004dec7259510006ec625951005cff75595100067f7559510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc7359510004ff7259510006ef7259510004ef725951000cfe7259510004fd725951000cfc7259510006ec725951000cec725951005e7f52595100067d5259510074ff7159510006f77159510084ff7059510006fb70595100057e761951005e7e76195100047e76195100067e63195100067c631951005d7f72195100057d72195100067f62195100067e62195100067d62195100067c62195100076c62195100066c621951005f7571195101de7f61195100077621195100077521195101df7610195101df741019510014fe76d8d100067f65d8d100067c65d8d10056de63d8d10006ec62d8d1001cfe75d8d10004fd75d8d1001cfc75d8d100a4fe74d8d10004fd74d8d100a4fc74d8d10006df53d8d10056de53d8d10056dc53d8d10006df43d8d10056de43d8d10056dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10056df32d8d10006de32d8d10006dd32d8d10056dc32d8d10014fe71d8d10024fd71d8d10014fc71d8d10056df31d8d10024fe70d8d10054fd70d8d10024fc70d8d10056df30d8d10055de76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100075f52d8d100075d52d8d1017fd771d8d10007d621d8d10007d521d8d1017fd610d8d1017fd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d100065f52d8d10006de52d8d10006dd52d8d100065d52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d1017edf71d8d10056de71d8d10006dd71d8d10006df51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006d
  | 5 => 0x5f7744c710005f5744c710007d7734c710007d7634c710016f6634c710016f4634c71007fd4634c7101f5f7724c7101f5f5724c7101ef77524c7101ef75524c710025f6704c710025f4704c71007fd7304c71001cff765431001cfc765431001e7e65543100067d6554310005f77154310005f47154310007755154310014ff764c310014fc764c3100057f754c3100857c754c310016de634c310006dd634c310005f7714c310005f4714c310007d5314c3100267f7559610004ff7359610014fe7359610014fc73596100767f5359610004ff725961000cfe7259610004fd725961000cfc72596100767f52596100067d52596100767f5159610024fc70596100267e50596100267c5059610026f71059610026f51059610004ff7558e100067f7558e100047f7558e1001cfe7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e100a4fe7458e100a4fc7458e10026df7358e1006ede5358e1006ede4358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e100067f5258e100067d5258e1006edf3258e10006dd3258e1006edf3158e10024fc7058e10026de3058e10026dc3058e10026f71058e10026f51058e10004ff7654e10024fe7654e10004fd7654e10024fc7654e1001e7e6554e100067d6554e10016de6354e10006dd6354e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10016de6350e10006dd6350e1006f9c4350e10005f77150e10005f47150e1005cfd76946101ae7f659461001e7c659461007777519461001cff7654610024fc765461001e7e65546100067d6554610005fb7054610025f87054610054fd768c6100757e758c6100057d758c61017edf638c610016dc638c610014ff764c610024fc764c610016de634c610006dd634c610005fb704c610025f8704c610025f976c4210006f976c42101e77b52c42101e77952c4210027f271c421001cfe76d951005e7e65d9510006ec62d9510014fe73d9510004fd73d9510014fc73d951005e7f53d95100067e53d951005e7c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d951005e7f52d95100067e52d95100067d52d951005e7c52d951001cfe71d9510024fd71d951001cfc71d951005e7f51d9510024fe70d951005cfd70d9510024fc70d951005e7f50d951005d7e76d951001c7e76d95100067e63d95100067c63d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95101af7771d95100077621d95100077521d95101af7610d95101af7410d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d
  | 6 => 0xf76597100867c65597100067f7559710004ff7359710014fe7359710014fc73597100067e53597100867c5359710004ff725971000cfe7259710004fd725971000cfc72597100867f52597100067d5259710024fc71597100867c51597100867f50597100857e75d8f100057d75d8f1007ede63d8f1001cfe75d8f100067e75d8f1001c7e75d8f10004fd75d8f100067d75d8f100047d75d8f1001cfc75d8f100a4fe74d8f10004fd74d8f100a4fc74d8f1007cfd73d8f1007ede53d8f1007ede43d8f10004ff72d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100067f52d8f100067d52d8f1007edf32d8f10006dd32d8f10006f671d8f1007edf31d8f10006f970d8f1017ede30d8f1017edc30d8f10014ff7658f1007edc6358f10004ff7558f1001cfe7558f1001cfc7558f10004ff7458f100a4fe7458f100a4fc7458f10006df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10024fc7158f1007edc3158f1007edf3058f10004ff7654f10004fe7654f10004fd7654f10004fc7654f100067f6554f1001e7c6554f10006df6354f10016dc6354f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006df6350f10016dc6350f1007f9c4350f10024fd769471001e7e65947100067d6594710025fa7094710005f97094710025f5769471001ef57694710024f5769471001ef6659471008776659471001e76659471000775659471001ef46594710005f5739471008777539471000775539471022df7729471022df57294710087775294710227755294710025f67094710007f27094710007f17094710025f470947101af7650947101af74509471003cff76547100067f655471001e7c6554710087745154710005f7765471003ef7765471000777755471000777655471001ef6655471001ef46554710087746554710005f7735471021f765354710087745354710215f77254710215f5725471008777525471020f755254710025f67054710025f47054710087775054710024fd768c7100857e758c7100057d758c710016de638c710006dd638c710025fa708c710005f9708c710025f5768c710016f5768c710024f5768c710005f7758c71000776758c710005f5758c71000775758c71000575758c710005f7748c710005f5748c710016f6638c71007fd6638c710007d5638c710016f4638c71007fd6538c710007d5538c71007fd6438c710007d5438c710205f7728c710205f5728c7101ff77528c7101ff75528c71007fd7328c7101ffd5328c710025f6708c710007f2708c710007f1708c710025f4708c71017fd6308c71017fd4308c710034ff764c710006df634c710016dc634c71007fd4314c710005f7764c710036f7764c710005f7754c710005f5754c710
  | 7 => 0xd302675d5250d300979f4250d302679d4250d30005df7150d300979c4150d30007db7050d30025de7050d30025dc7050d30007d87050d30016df6050d30017db6050d300979f4050d300067f65d85300067c65d853001cfe75d8530004fd75d853001cfc75d85300a4fe74d8530004fd74d85300a4fc74d8530024fd73d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006f741d8530006f441d853006ef631d853006ef531d8530006f721d8530006f421d853009d7e75985300057d75985300067f65985300067c6598530006f76198530055f970985300057f755853009d7c75585300067f65585300067c6558530005bf7458530095bc7458530005ef725853008dec725853007dfb70585300067f65185300067c6518530006f5611853001cfe7518530004fd751853001cfc75185300a4fe7418530004fd74185300a4fc7418530024fd7318530036de5318530006dd5318530036de4318530006dd4318530004ff721853000cfe7218530004fd721853000cfc72185300067f52185300067d5218530036df3218530006dd3218530006f74118530006f44118530036df3118530036f63118530036f53118530006f72118530006f42118530024fe7018530024fc70185301cede30185301cedc3018530004fe7694530004fd7694530004fc76945300067f659453001e7c6594530015de7394530005dd73945300075d5394530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530015de735453011f5e5354530004fe7690530004fd7690530004fc769053009d7e75905300057d75905300067f659053025e7c6590530006bf64905300a6bc6490530015de7390530005dd73905300079d4390530004ff7650530004fe7650530004fc76505300067f65505302567c6550530015de7350530024dc764c530005df754c530005dd754c5300075f654c5300075c654c530005df744c530005dd744c53024ddf724c53024ddd724c5302475f524c5302475d524c530015df714c530017d7714c530007d7614c530006dc614c530007d4614c530007db704c530025de704c530025dc704c530007d8704c530016df604c530017db604c53001cff7654130014fe76541300ccfd7654130014fc76541300067f655413001e7c6554130005df7354130015dc73541300075d5354130014fe765013023cfd7650130014fc76501300067f65501302367c6550130005df7350130015dc73501300079d43501300867e65d9710084fd75d9710014fe73d9710004fd73d9710014fc73d97100867f53d9710004ff72d971000cfe72d9710004fd72d971000cfc72d97100867f52d97100067d52d9710006f671d97100867f51d9710006f970d97101ae7e50d97101ae7c50d971001cf
  | 8 => 0x2c67e20d95300067d20d95302c67c20d95302c67e10d95302c67c10d953009e7c65595302bdfb70595300dcff75595300067f7559530004ff74595300a4fe74595300a4fc74595300ccff7359530006df7359530004ff725953000cfe7259530004fd725953000cfc725953009e7f52595300067d5259530004ff7159530004fc71595302bcff7059530006fb70595300dd7e761953009e7e76195300dc7e76195300067e64195300067c64195302af5e731953009f5d73195302b67f63195302af5e431953009d7f72195300057d72195300067f62195300067e62195300067d62195300067c62195302af5f32195300075d32195302af5f31195302ae7f60195302af7b30195302b75e30195302b75c30195302af7830195300a4fe76d91300067f65d91300067c65d9130096be64d913001cfe75d9130004fd75d913001cfc75d9130024ff73d9130014fe73d9130024fd73d9130014fc73d91302a6bf43d91302a6bd43d9130004ff72d913000cfe72d9130004fd72d913000cfc72d91300067f52d91300067d52d9130006be42d9130096bc42d91302a6df32d9130006dd32d9130004fe71d9130004fd71d9130096bc41d9130014fd70d9130096bf40d91300057f755913009d7c75591300067f65591300067c6559130096bc6459130005ef725913008dec7259130005f77159130005f4715913029dfb7059130004ff75591300067f75591300047f755913001cfe755913001cfc75591300067c755913001c7c755913023cff7359130006df7359130004ff7259130006ef7259130004ef725913000cfe7259130004fd725913000cfc7259130006ec725913000cec72591300067f52591300067d525913023edf3259130006dd3259130004ff7159130006f77159130004f77159130004fc7159130006f47159130004f4715913029cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc76551300067f655513001e7c6555130015de73551302975e5355130025dc7654d3001edc7654d30024dc7654d30015df7554d300175f7554d300075f6554d3001ede6554d3001edc6554d3009f5c6554d30005df7454d3028f5e5454d3009f5c5454d30285df7254d30285dd7254d3009f5f5254d3027f5d5254d30005df7154d3009f5c5154d30007db7054d30025de7054d30025dc7054d30007d87054d30016df6054d30017db6054d3009f5f5054d30025dc7650d300a6dc7650d30024dc7650d30005df7550d30005dd7550d300075f6550d3013ede6550d3013edc6550d300075c6550d3013e5c6550d30015df7450d300179f7450d300079f6450d300a6de6450d300a6dc6450d300979c6450d300a69c6450d302779f5450d300979c5450d3026ddf7250d3026ddd7250d30266df6250d30266dd6250d302675f525
  | 9 => 0xf725863000cfe7258630004fd725863000cfc7258630006ec725863000cec72586300067f52586300067d5258630026f77158630056f63158630056f53158630056dc3158630006f62158630006f52158630024fc7058630026df3058630026dd3058630026f61058630026f41058630004ff7694630024fe7694630004fd76946301ae7f659463001e7c6594630006f66194630006f56194630004ff7654630004fd7654630024fc765463001e7e65546300067d6554630005df7354630015dc7354630006f66154630006f56154630004ff7690630024fe7690630004fd76906300bd7e75906300057d75906300a6bc6490630006f66190630006f56190630004ff7650630004fd7650630024fc76506300a6be6450630006bd6450630005df7350630015dc7350630006f66150630006f561506300075e758c6300075d758c63017edf658c630006dd658c63017edf648c630006dd648c63017edf628c6302cedd628c6302cf5f528c6302cf5d528c630015de718c630017d6718c63017fd6618c630006dd618c63017fd5618c63017fda708c63017ddd708c630007d9708c630016de608c630017da608c63001cfe76d953009e7e65d95300a4fe74d9530004fd74d95300a4fc74d953009e7f54d95300067e54d953009e7c54d9530024ff73d9530014fe73d9530024fd73d9530014fc73d95300de7f53d95300de7d53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d953009e7f52d95300067e52d95300067d52d953009e7c52d9530004fe71d9530004fd71d953009e7f51d953009e7c51d9530014fd70d953009e7f50d95302ad7e76d953001c7e76d95300067e64d95300067c64d95302c75f73d95300df5c73d95300df5e43d95300057f72d95300057d72d95300067f62d95300067e62d95300067d62d95300067c62d95300df5f32d95300075d32d95300df5f31d95300df7b30d95302c75e30d95302c75c30d95300df7830d95300067f74d95300067e74d95300067d74d95300067c74d95302c67f73d95300de7e73d95300de7d73d95300de7c73d95300de7f43d95300de7e43d95300de7d43d95300de7c43d95300067f72d95300047f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300de7f32d95300de7e32d95300de7d32d95300de7c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067c41d95300de7f31d95300de7e31d95300de7d31d95300de7c31d95300067f21d95300067e21d95300067d21d95300067c21d95300de7f70d95302c67e70d95300de7d70d95302c67c70d95300067f40d95302c67e40d95302c67c40d95300de7f30d95302c67e30d95302c67c30d95300067f20d9530
  | 10 => 0xd500cf9c4350d50024fd75d8550014fe73d8550004fd73d8550014fc73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d85500767f52d85500067d52d8550076f651d8550076f551d8550006f721d8550006f421d8550006f7619855005df97098550005df73585500cddc7358550005ef72585500c5ec7258550085fb7058550006f56118550024fd7518550014fe7318550004fd7318550014fc731855003e7f53185500067d5318550004ff721855000cfe7218550004fd721855000cfc721855003e7f52185500067d521855003e7f511855003ef6511855003ef55118550006f72118550006f421185501de7e50185501de7c50185500247c76545500057f735455011e7e635455011e7c63545502dd7f72545502dd7d72545502d67f62545502d67d625455001d7f715455001f7771545500077761545500067c61545500077461545500077b70545500257e70545500257c705455000778705455001e7f605455001f7b6054550004fe768c550004fd768c550004fc768c55001d7e758c5500057d758c550006df638c550016dc638c5500075d538c550004ff764c550004fe764c550004fc764c55001d7e754c5500057d754c5500267f7559630004ff74596300a4fe74596300a4fc74596300be7f54596300ce7f53596300ce7d5359630004ff725963000cfe7259630004fd725963000cfc72596300be7f52596300067d5259630004ff7159630004fc71596300be7f51596300cedc3159630024fe7059630024fc70596300267e50596300267c5059630026df3059630026dd3059630004ff75592300067f75592300047f755923001cfe755923001cfc75592300067c755923001c7c7559230026bf74592300b6be545923023ebf435923023ebd4359230004ff725923000cfe7259230004fd725923000cfc72592300067f52592300067d52592300b6bf4259230006bd4259230004ff7159230004fc71592300b6bf415923023edc3159230024fe7059230024fc7059230026be4059230026bc4059230026df3059230026dd3059230004ff7655230024fe7655230004fd7655230024fc765523001e7e65552300067d65552300a6be6455230006bd645523001cfe7598630004fd759863001cfc75986300a4fe7498630004fd74986300a4fc7498630004ff729863000cfe7298630004fd729863000cfc72986300067f52986300067d5298630026f6719863007ef6319863007ef53198630006f62198630006f52198630024fe7098630026f61098630026f41098630004ff75586300067f75586300047f755863001cfe755863001cfc75586300067c755863001c7c7558630004ff7458630006bf7458630004bf74586300a4fe74586300a4fc7458630006bc74586300a4bc7458630004ff7258630006ef7258630004e
  | 11 => 0xde5e5358e5009edd5358e500de7c5358e500dede4358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e5009e7f5258e500067d5258e500dedf3258e50006dd3258e50004ff7158e50004fc7158e5009e7c5158e500dedf3158e50024fe7058e50024fc7058e500267f5058e500267d5058e50026de3058e50026dc3058e50004ff7650e50004fd7650e50024fc7650e500057f7550e5001d7c7550e50016de6350e50006dd6350e500df5c5350e500df9c4350e50014fe7398650004fd7398650014fc7398650004ff729865000cfe7298650004fd729865000cfc72986500867f52986500067d5298650026f67198650086f65198650086f55198650006f62198650006f52198650024fe7098650026f61098650026f41098650004ff7358650006df7358650004df7358650014fe7358650014fc7358650006dc7358650014dc73586500067e535865005e7c5358650004ff7258650006ef7258650004ef725865000cfe7258650004fd725865000cfc7258650006ec725865000cec725865005e7f52586500067d5258650026f7715865005ef6515865005ef5515865005e7c5158650006f62158650006f52158650024fc70586500267f50586500267d5058650026f61058650026f410586500dd7e73946500dd7c73946500067d63946503057f72946503057d72946501ae7f62946502fe7d629465001d7e719465001f7671946501af7661946500067d61946501af7561946501af7a70946501ad7d709465000779709465001e7e609465001f7a6094650004ff768c650024fe768c650004fd768c65001d7e758c6500057d758c650016dc638c6500df5e538c650006f6618c650006f5618c650004ff764c650004fd764c650024fc764c6500057f754c65001d7c754c650016de634c650006dd634c650006f6614c650006f5614c650014fe76d8d500cede63d8d50024fd75d8d50014fc75d8d500a4fe74d8d50004fd74d8d500a4fc74d8d500cede53d8d500bedd53d8d500cede43d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500be7f52d8d500067d52d8d50006de32d8d500cedc32d8d50004fe71d8d50004fd71d8d500cedc31d8d5001cfd70d8d500cedf30d8d500cedc6358d502f5fb7058d500257c7654d500167c7654d500247c7654d500057f7454d5014e7e6454d5014e7c6454d5001d7f7354d5001f5f7354d500075f6354d500167e6354d500167c6354d500cf5c6354d502ed7f7254d502ed7d7254d502e67f6254d502e67d6254d500057f7154d500cf5c3154d500077b7054d500257e7054d500257c7054d50007787054d5001e7f6054d5001f7b6054d500cf5f3054d50004ff7650d50004fe7650d50004fc7650d5001d7e7550d500057d7550d50006df6350d50016dc6350d5013f5f535
  | 12 => 0xd72d953100cfc72d95310f67f52d95310067d52d9531014fd71d95310f67f51d953112edc31d9531024fe70d9531004fd70d95310f67c50d953112edf30d95310f67c655953133df7715953112cff75595310067f7559531004ff74595310a4fe74595310a4fc74595310067e54595310f67c545953111cff7359531006df735953111e7e535953111e7c5359531004ff725953100cfe7259531004fd725953100cfc72595310f67f52595310067d525953133cff7159531006f771595310f67c515953111edc3159531004ff7059531024fc70595310f67f505953111edf30595310a4fe76d91310f57e75d91310057d75d91310eebe64d913101cfe75d91310067e75d913101c7e75d9131004fd75d91310067d75d91310047d75d913101cfc75d91310eebe54d9131334ff73d9131334fd73d9131336bf43d9131336bd43d9131004ff72d913100cfe72d9131004fd72d913100cfc72d91310067f52d91310067d52d91310eebf42d9131006bd42d9131014fd71d91310eebf41d9131336dc31d9131024fe70d9131004fd70d91310eebc40d9131336df30d91310eebc645913132df77159131004ff755913101cfe755913101cfc7559131314ff7359131006df7359131004ff725913100cfe7259131004fd725913100cfc72591310067f52591310067d525913132cff7159131006f77159131316dc3159131004ff7059131024fc7059131316df3059131004ff7655131004fe7655131004fd7655131004fc76551310067f655513101e7c6555131006bf64551310a6bc6455131324fe769453101e7e65945310067d65945310f777519453112fd4319453101cff7654531014fe765453111cfd7654531014fc76545310067f655453101e7c6554531005df7354531015dc735453111fd4315453131cfe76905310f57e75905310057d75905310a6be6490531014fe7650531314fd7650531014fc7650531005df7350531015dc73505310075e758c5310075d758c531006df658c531006dd658c531006df648c531006dd648c53130edf628c53130edd628c53130f5f528c53130f5d528c531015de718c531017d6718c531016df618c531017d7618c531005dd708c53101cfe75d8131004fd75d813101cfc75d81310a4fe74d8131004fd74d81310a4fc74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d813107efa30d8131006fb60981310057f75581310f57c7558131005bf74581310edbc7458131005ef72581310e5ec72581310f57e75181310057d75181310edbe7418131005bd741813117edf63181310e5ee7218131005ed7218131026fa6018131006f96018131004ff7458e500a4fe7458e500a4fc7458e500067e5458e5009e7c5458e50026df7358e500de7e5358e500dede5358e50
  | 13 => 0x9231006f671d9231024fe70d9231004fd70d92310a4ff76592310067e65592310067d6559231106bc6459231004ff755923101cfe755923101cfc7559231006bf7459231316bf4359231316bd4359231004ff725923100cfe7259231004fd725923100cfc72592310067f52592310067d5259231006be4259231106bc4259231316df3259231006dd3259231014fc7159231106bc4159231004ff7059231024fc7059231106bf4059231004ff7655231004fe7655231004fd7655231004fc765523101e7e65552310067d6555231015de73552312975e535523110ddf7654e3101edf7654e3101cdf7654e31015df7554e310175f7554e3101ede6554e3110f5e6554e310075d6554e3101edc6554e31005df7454e3136f5e5454e3110f5c5454e31365df7254e31365dd7254e3110f5f5254e3135f5d5254e31005df7154e31007d77154e31007d47154e31016de6154e31017d66154e3110f5c5154e3117ddc7054e3110f5f5054e31105df7650e310a6df7650e310a4df7650e31005df7550e31005dd7550e3113ede6550e310075e6550e3113e5e6550e310075d6550e3113edc6550e31015df7450e310179f7450e310a6de6450e311079e6450e310a69e6450e310079d6450e310a6dc6450e313579f5450e311079c5450e3134ddf7250e3134ddd7250e31346df6250e31346dd6250e313475f5250e313475d5250e311079f4250e313479d4250e31005df7150e31007d77150e31007d47150e31016de6150e31017d66150e311079c4150e3117ddc7050e311079f4050e31014ff769463101cfe7694631014fd769463101e7e65946310067d6594631015de7394631005dd73946310075d539463110f77519463112fd7319463133cff765463101e7e655463111e7d6554631015de735463111f5e535463111fd731546310a4fe7690631014fd769063125e7e65906310067d6590631015de7390631005dd73906310079d439063110d7e75d82310057d75d82310067e65d82310067d65d82310067e65982310067d6598231006fb60982310067e65582310067d6558231004ff755823101cfe755823101cfc7558231004ff74582310a4fe74582310a4fc7458231056de5358231006dd5358231056de4358231006dd4358231004ff725823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231056df3258231006dd3258231056df3158231056fa305823117edc305823110d7e75182310057d75182310067e65182310067d6518231105be7418231005bd74182310fdee7218231005ed7218231026fa6018231006f9601823101cfe76d95310f67e65d95310a4fe74d9531004fd74d95310a4fc74d95310f67f54d953112cff73d953112cfd73d953112e7f53d953112e7d53d9531004ff72d953100cfe72d9531004f
  | 14 => 0x115ec72581511ae7f651815111dde7318151005dd7318151115ee7218151005ed7218151026fa6018151006f9601815110e7e65d9631325f671d963111cfd75d96310a4fe74d9631004fd74d96310a4fc74d9631006dd73d9631004ff72d963100cfe72d9631004fd72d963100cfc72d963110e7f52d96310067d52d9631324fe71d9631006f671d9631024fe70d9631004fd70d963111c7d76996310067e64996310067c649963133f5e739963110f5d739963133e7d639963133f5e439963110d7f72996310057d72996310067f62996310067e62996310067d62996310067c629963133f5f32996310075d329963133e7e619963133f5f319963133f77319963133f74319963133f5c309963101cff765963110e7c65596310067f7559631004ff74596310a4fe74596310a4fc745963110e7f54596310067e545963110e7c545963111e7f535963111e7d5359631004ff725963100cfe7259631004fd725963100cfc725963110e7f52596310067e52596310067d525963110e7c5259631014fc715963110e7c5159631004ff7059631024fc705963110e7f505963110e7c505963133d7f765963110e7f765963101c7f76596310067e64596310067c645963111f5e73596310075d735963111f5e43596310057f72596310057d72596310067f62596310067e62596310067d62596310067c625963111f5f32596310075d325963111f5f315963111f77315963111f74315963111f5c30596310067f74596310067e74596310067d74596310067c745963111e7f735963111e7e735963111e7d735963111e7c735963111e7f435963111e7e435963111e7d435963111e7c43596310067f72596310047f72596310067e72596310067d72596310047d72596310067c72596310067f42596310067e42596310067d42596310067c425963111e7f325963111e7e325963111e7d325963111e7c325963110e7f715963111e7e715963111e7c71596310067f41596310067c415963111e7f315963111e7e315963111e7d315963111e7c31596310067f21596310067e21596310067d21596310067c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067c405963111e7f305963111e7e305963111e7d305963111e7c30596310067f20596310067e20596310067d20596310067c205963110d7e75d92310057d75d92310067e65d92310067d65d9231106be64d92310fdee72d9231005ed72d923131df671d923101cfe75d92310067e75d923101c7e75d9231004fd75d92310067d75d92310047d75d923101cfc75d9231004ff72d923100cfe72d9231006ee72d923100cee72d9231004fd72d9231006ed72d9231004ed72d923100cfc72d92310067f52d92310067d52d9231336df32d9231006dd32d923131cfe71d
  | 15 => 0xf32d8143006dd32d8143004fe71d8143004fd71d814329efa30d81432a79c4398143006fb60981430057f755814313d7c755814323f9c4358143005ef7258143135ec7258143005f77158143005f4715814313d7e75181430057d75181433a79c4318143135ee7218143005ed7218143005f67118143005f57118143026fa6018143006f9601814312ede63d8e5139df671d8e51014ff7658e5112edc6358e51004ff7458e510a4fe7458e510a4fc7458e5112ede5358e510f6dd5358e5112ede4358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e510f67f5258e510067d5258e51006de3258e5112edc3258e5101cfc7158e5112edc3158e51004ff7058e51024fc7058e5112edf3058e5112d7f7654e510167f7654e510147f7654e510057f7454e5114e7e6454e5114e7c6454e5101d7f7354e5101f5f7354e510167e6354e5112f5e6354e510075d6354e510167c6354e513957f7254e513957d7254e5138e7f6254e5138e7d6254e510057f7154e51007777154e51007747154e5101e7e6154e5101f766154e5112f5c3154e511ad7c7054e5112f5f3054e51004ff7650e51004fd7650e51004fc7650e5101d7e7550e510057d7550e51016de6350e51006dd6350e5113f5f5350e5112f9c4350e51005f77150e51005f47150e51006fb6098251004ff7358251014fe7358251014fc735825105e7f53582510067d5358251004ff725825100cfe7258251004fd725825100cfc725825105e7f52582510067d525825105e7f515825105efa50582511ae7c505825112dde7318251005dd7318251125ee7218251005ed7218251026fa6018251006f96018251014fe76d8d5101d7e75d8d5111ede63d8d5111f5e53d8d510a4fe74d8d51004fd74d8d510a4fc74d8d510067e54d8d5110e7c54d8d5111e7e53d8d5111ede53d8d5111e5e53d8d5110edd53d8d5111e7c53d8d5111ede43d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d5110e7f52d8d510067d52d8d5111edf32d8d51006dd32d8d5101cfd71d8d5110e7c51d8d5111edf31d8d51024fe70d8d51004fd70d8d5110e7f50d8d5111edc30d8d5111edc6358d51385f77158d51004ff7650d51004fe7650d51004fc7650d510057f7550d5101d7c7550d51006df6350d51016dc6350d5111f5c5350d5111f9c4350d51005f77150d51005f47150d5111d7e739455111d7c73945510067f639455137d7f729455137d7d72945513767f62945513767d629455101d7e719455101f76719455101e7f619455101f7761945510057d7094551014fe73d8151004fd73d8151014fc73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d81510867f52d81510067d52d8151086fa50d8151006fb6098151005df735815111ddc7358151005ef7258151
  | 16 => 0x8553006f76198553006f56118553014fd75185530a4fe7418553004fd74185530a4fc741855301cfd7318553004ff721855300cfe7218553004fd721855300cfc721855339e7f52185530067d521855339ef55118553326f53118553024fe7018553004fd7018553024fe76d8153014fd75d81530a4fe74d8153004fd74d81530a4fc74d815301cfd73d8153004ff72d815300cfe72d8153004fd72d815300cfc72d81532f67f52d81530067d52d8153004fe71d8153004fd71d81532f6fa50d81532befa30d81532c67f6598153006fb60981532c67f651815314dbe7418153005bd7418153145ee7218153005ed7218153005f67118153005f57118153026fa6018153006f9601815301cfe76d954313e7e65d9543015de73d95430a5dd73d954313f5f53d95433b79c43d9543294fd75d95430a4ff73d95430a4fd73d95433c6dd73d95430a4dd73d95433b67f53d954313edf53d954313e5f53d95433b67d53d95433b6dc53d9543004ff72d954300cfe72d9543004fd72d954300cfc72d954313e7f52d95430067d52d9543004fe71d9543004fd71d954313e7f51d95433b6dc31d9543024fe70d9543004fd70d954313e7c50d95433b6df30d954301cff765954313e7c65595433bddf73595432975c53595432979c43595433b4ff75595430067f7559543294ff7359543006df735954313edf53595432967e53595432967c5359543296dc5359543004ff725954300cfe7259543004fd725954300cfc725954313e7f52595430067d5259543004ff7159543004fc715954313e7c5159543296dc3159543004ff7059543024fc705954313e7f5059543296df305954313d7e75d85430057d75d854332f9c43d8543135ee72d8543005ed72d854301cfe75d85430067e75d854301c7e75d8543004fd75d85430067d75d85430047d75d854301cfc75d85430a4fd73d85433aedd73d8543004ff72d854300cfe72d8543006ee72d854300cee72d8543004fd72d8543006ed72d8543004ed72d854300cfc72d85430067f52d85430067d52d854332ef631d854332edc31d8543006f621d8543006f521d8543024fe70d8543004fd70d854332edf30d854313d7e75985430057d75985433379c4398543135ee7298543005ed7298543006f761985433179c435854331f9c4318543006f5611854301cfe7518543004fd751854301cfc75185430a4fd7318543004ff721854300cfe7218543004fd721854300cfc72185430067f52185430067d521854331edf3218543006dd321854331ef53118543006f62118543006f52118543024fe7018543004fd7018543024fe76d814329f9c43d814301cfe75d8143004fd75d814301cfc75d81430a4fd73d8143004ff72d814300cfe72d8143004fd72d814300cfc72d81430067f52d81430067d52d814329ed
  | 17 => 0xb00c00000000401400000100000200200000200100101200700b00500b00c01800200b00200101000004200000000400002f02d00000200500700000100000001100900200d00201800500100000101100a00100400000202500102e00000a00400000200400201d00001100300d00401b00a00000000100700000b00200100800400800200000700a00b00000c00d00000600200000000400802200100b00a02c00100100000800200200301500000800f01100203600000500900903400200400300401001000000000300401800000000100700101a00a00600101400d00101400000200b00000000000100000300f00801a00900400100f00f00000301700200b00000003400400300000002202801003500200200200900100102500a00100a00000700600700000100100a00702d00001900000000004600001300000003500a00300102501a00200000000700000500200800000100000800100000001801b00400f00000000100300001d01700000a00001800700000100503100702a00100800004d00001c00400100f00200900100000402800700f00300102500200a00000001102a00400a00000100000001600000801200001502a02301200500000701200100300a00800500600100000400501500100f00100100e00300200000400200e00900200200601500200500a00300800a00500300200000e00000000000000001500400200000100000500a00600200200101900d02a00b00000800f00800b00501400100000100000f00000300000000600201c00003300102000301300100000000001207a0160000010040a4fe76d915301d7e75d91530157d75d915314ebe64d915314f3e54d9153014fd75d91533d67d75d91530147d75d915314e7e54d915314ebe54d915314e3e54d915314e7c54d915301cfd73d91533dedf53d91533d67e53d91533d67c53d91533d6dc53d91533d6bf43d9153004ff72d915300cfe72d9153004fd72d915300cfc72d91533de7f52d91530067d52d9153004fe71d9153004fd71d91533de7c51d91533d6dc31d9153024fe70d9153004fd70d91533de7f50d91533d6df30d915314ebc645915314f3c54591533cddf735915314dbe74d8553005bd74d8553145ee72d8553005ed72d8553014fd75d855333e7d75d85530a4fe74d8553006be74d85530a4be74d8553004fd74d8553006bd74d8553004bd74d85530a4fc74d85530067e54d85533867c54d855301cfd73d8553386dd73d855333e7e53d855333e7c53d8553004ff72d855300cfe72d8553006ee72d855300cee72d8553004fd72d8553006ed72d8553004ed72d855300cfc72d85533867f52d85530067d52d8553386f651d85533867c51d855333ef631d855333edc31d8553024fe70d8553004fd70d85533867f50d855333edf30d
  | 18 => 0x900002300300300300700400b00000600000104000300906100100e00300000000500200100801f00001300c00300c02400800100000003400601800000f01900100201000200300000601800500001700102000300200100400000000900000006700a00000000900900a00201100500000000000100100000300201600300500a00200200000a00200c00100a00003400303900001101700300c01502101500100200200900100000400000100305500200200000400301100000102501d00500000400900300501300a00101600d00002100100000300900200000000100800100002500201700200e00400700000100000500001b00901100e00600b00200e00e00000000100200200300f00800000000000300200000200501600f00001300700900001c00400501500200300500900000100100b00500100d00600001b01500e00000000a01800800300400400000000101201e00f00e00500100000000a00100300b00100000700f00603003100b00000400b00600800000000b00200d00000000800000900400401000300700000001c00200a00002600200a00001000800400600f01600600101400500200300200300000400301600500800000600100000101202700100001900000300d00600203500000703800800100000000800300200000300b00301100a00000000600500300600100203502b00400000500102500400200000300000400100800000200d00000c01700300c01f00200201c00200000000b01300000407200f02600000000100a00d00000a00800102300100200c00100801000500900000500301d00002000d00300700700d00101103700f01a00c00101f00402600100101d00800100300100800501604700300100800100000202701b00000b00000001400102500000e01e00400002c00000101f00400200302500002101100400401000100a02500500500201b00000500400900000101104f01200a03800200200400301600700200001004900300600200400200f00100100300f01c00001100400200800000a00800700c00e00500800705b00600200301101b00000100000204500000201e00100100400200500b00200200700000000003800100b00000000400201000900a00000006000900000700000002b00100901b02a00200300000001100000f00000f00d02d00001100700600300400400000102301400000900000000200a00800d00000300100001400100000100a06a00401800100300400e02303100201200900400a01c00000400c00000700500c00c00300a00500d00001300300000200100200000c00000002300700003400800a00800300000b01000006100100000402200700200100904000000600600b00600200200200100000e00100000000000000600100a00d002000001
  | 19 => 0x3280001995cd000067ddc196a4869b5435485254c2b0799bad5968e64d0fb857d73028d2b31a6049924985d0ce4a977b249880240d27ee2df1f900c568412b81ecfe647a1e8ac6eab8527246082c0158b51418896ada7c33e6ec2cbb8b40087e6c4c1a8892cd1a50e227a73fb1bc8d7eab19778f84abf34856b598c4800004d001741e456028708f3354941252526c42b0bd374261910665032e8be08ce61e06a14bd54c9e818d8e4cdc2127ca45780468597266aad449871650ca2100623520ee000016a63154385b40007971b1a9d15ca20336700006dd28e11d11800005655350190000a942ce06a8bfe8af13c21280004ae4fc905826ab2d5188001236a1108e008af94b8e50c44b543f1cc0bf0b404f445041b8f8d6540000002d9133c926534134c01c68f09451c54ee0564c9055c98c000000168879a7f95c387ec25c4ca0f01a0f2040f9000056000000041d400034d000000054c6644ac4a28bdd4e67084888a511a811f13280b153cb6b000069000085d2ad04072d658d1429f3e0da852dc6086ce509660936c7627106241a89f16280572bd1db00008094fba79000090b00010540005060001578a625923c9933d71a0190f40094000aad0768b86f7a88b46e90f14b477747308810bc0002f804a0000000197c0000009d3568c000e406a32da00000001448002bc075a6414028000c6e94929fac60592a55c69892f6ec0003f5974892a0003699eb40005f81db819eca805315711887dcb690001ca25fe6bd4f106dc1ce43321c2480f5682d30e8b0906666e1aecd52000b0d5a6a590000a4f43e953f21e77114f00004cc01d541acf0cd0b5c26f1258e8497d3eb12a405200018ca970e080390000f9cf2c08744aa45a20118400000001244dc80091b8d6e9ab28122585bd1b006f9a311b80000002ca484664b0949f8cf5c99d0520000a3c55638816a11c1b5909389c41ba9013efc01c07073039e82e097cb170e4430c57635d28aa6007cc1f442f922407d3540000ed064a5bc439abe4d6c50019eaa105c800000018d80000e151c81c065866b3f1274952023934912ec2eb0003bc8000eaa73b1b29664000151d82a3a41ac8c400013cce757de000000169e0001f98000e9ab4929c1d9000071d4e400000001dd000204c0940000000000000aa200009a4000000130c2c542e99447112800c75c000027d968c8590000000ca650f00009d817c0000000a6535a0002f61f700005211ea979000014d5b709640003ce56497783dc9fd56aad491f284100028335c70004d1a32d091b089fca16c0002530001a0c0004221728a5d39a8ad113810061100047911742ba00200000500100e00500000700600b00601a00b00100001200200000400100200900000000800000000000000000600000d00200405200b00b0040200000040000040
  | 20 => 0x1860bca72d00022845be2c64c3982c9e473c941018499856900017c8ab24640000000a78729096e5294f84144c518950dc0000610000b020000f48f708d03990b50b040006525c2892800070b93b94c01d000043d820a00087711343c03260bc2148480c34b1513200015ea0004f1a759582ac427aa1fd6020f43eb9c509288a75170ee13ce3361782da0bc45bf0041758e0eb1a88d04c80008fc31090b128e21802cd03038295b0238230cc4b00953271126800004202dc000a6f5cb0862fee0601e021a05db9392450e48000000000059400000017000010441f6800065200000000000012da000405800126c40735a0ac0a7c0f7000088cf789b70001d4885c18526d1a6c61051600000003620ce2fb000000068e4ae8f7e4841ab1d09338e5438b5578000dcc107291115040867e03e00010a800009083116ce9fc0001c9c0000450c58404df667f02595c4ed656e2e3000068a5d00002de400000051a9a1cdee50d46125e82567002b61a98b924ff2f880b4dcab1600022d896f81846d2952000750144806000029b0122c482f08bc1d78ac494d1720f3c6943c246b11c0aac0000002ea20e3290584310247c00080815fa27c00044d1ef5f30ad076112d0a44000b385c480010e22e31659d42a5a0104c59b892eeaeb08b8e510de4272cd91cc25e26200004a91c874f20a60844cb79c52ca3205ac6323c1800000000054400003d140b256a2180005a3dba2aa151279847a0fe80006ab097432811e1812718000f7c6cb0ac800101856a3ac04fd230418000028400000053e996087a41f45282cd63d06502c9870036853000000006878f20b809c40a52a3a1da900008fcbca254933622a00010e96220003502e20a825240000d3cabe07f1ce97f5604a962a3800022c17a3e68d7d02a3b000017d400028a15f0e0ed42ada1d30e10767a2f1a0ddbc000b580a5d6580000001c600001c038e081d2f60004c03436c244480001d4400133471b0000000ffe29800011bc00098827da3ea6045460000cc26e25a6436869c754a1835706191ae0630d924a91467af252e9c53de75c02751f485a251255ae6932e03606f005ac6a81755b2c980001ce0000000cb357d041a25c0000003c488665b4b0e2fc87cc48821e25b875d2959fb0bcd3489d21c5d5d212c4b64064de8e8d2ca42600003ac8999f13bb26a164a103542a9c061600010b88acd8c0882582c824be4beb9c00007d21a3523ad5d5b82eb374c7fc000b240e9800081a71f00007500000000000000671603371ac28a520f0a1516b83a285a42306582728d523c0de07149e032d09a6f8a0002352962bdab6a2ef914532a56754ca0280004442ae91d0ac2757ba493246789c200000005dc8d106600002a28b23ea00000008300b580005daa9722ec00000000000000000007b6000000
  | 21 => 0x2b4a1d9a82e10e38a1027c9cac53e0000a1d9c17327a04c080010f25cc00016e91f600000992d0000b2f0001da50c80003992deb01c490319a8a508854d0341e140009cc50296cc1804cb35d00f00009a44c88a001567f450be70cd94b5016b96800000db34b9d580000cd80029307988ce500aaf340e1788dca6940351234da8b7046c71a4d82560b90b325958e0a91009436198910ce00008780e92e69d00f7a718000000000000000054a000147c000a410000000a320005b1800170c000132460070d0000861d1875218e4d3079a89c3a9ab922b11be8b145405c0cd47a541f09841901612541774f9d35143300792068b31878ff8d344f00a819e95f85abad21acc36c1c02552a74a463d62a4ad3833c2bd09e8d0519a1de00020c92a6b7840a1e300002fc48692fcf467623ac91fcf68a331a70c7122940a4a028b544800055085796caafa2f70f50f1f22958321140a0469a5300011b68ec0000000312963154ab34cdeaef000162d4925180000f94cee45a16ec6d5136480243215d0b048b4fec90493400017ca21d0eb5b257b0000000000253913d2ad327598167875c39c167800000026843299d83890001b04000b604583d816ec3b007606d20480b13f51b82a540004e8524174d09224516c24b80001b3da127d4cb830d55b8cf89d69900b2098d41709f48c9040e7eb19ab7a768e852919a62ce52f6319ad7995c41284c4cf9b802ea45731e01c80000cd261cd2c9fa2148d11924bd021500021c129a00047dec7ebaa8e18000036dd61fdb6c80cc0fc8941e21958e629121b0055849e0780e498116073693bea5c0a9e89d26e0e1e74a5a2ccc9fd4ac83c234a9cb034bae43cf1e283323c80000c1486ca2c562409b4af8691964bec47683c14e92e6e824fb9192270e8600000000000007360e780011e2000000000111ea3d37cac101c6af30a414040003b30fc800135c6d853280013bc00000019640004a3a005c485a87b7000000000000045f9a740000cc892cba763809151f28c82226ef2a8d67ca6816bbe886f4a260d944983bf29eb1d1d3800054611819481e4ac652657480d271a4353dd01794f26f61910728330798ae3a4941021261cf013f20cb2012b26bc84548126c00006769f407980002fe6881125d511443b124c2d8400000013780000009f819817d11820002fe09d488e63f3bd07f00006fe49e052c00000000000008481ad2d09a0065606ad4d9320bce6bc133add409c98e197652c76c82457f416d3ca36f84c9ec506c9ba12c1024aae15b119ac860d84022f488689628250ebc1495b0a130e1800048c0000a18000a665044304000f100000000c191244b68000000000a551fb9b5442715252f800000079f3721ea40000003d8400005c4342c49b3d4bb4d417b1e8317200000005f000013b000270441a00
  | 22 => 0x2944a2e8630001e385400000b0220150086c1bb803042c1e3427263568a58e01921205c404d90961de4ba353ae245eaa84908b4992e20fa9eb1c1196caee3ac2a90ee54bf5b120d156c000a780000000000a028001f64b280000882d6855e189bcc8a910224c10429e4068585621ca0d15afaab212a36435703044f1fc85ba72529a98640de5db50918e889d0f553482543fa2a223a9f26c02ad40001636000a06000076d2aaa3c0e285f50bf0003999e1c00082a18d56e46d422e3aaeb8ab0e16f26e8cb4e732cd4ac82168244030ef8ea033a18c57503a4c5c2e4af7860d43681c5139f80c206c400007491227cb4531514d8009805286bc18a6ed249055409e87200008f07e4b1e511ac6cc222e7360a988eea01a2bc0dd508448409249c804c000441275154e54b34284e80007533242b2072000041f9480876715c30000020016c27a0000898a750e214211bc00025b000062e0001e5ac9d48034946184c055a74a00011a55943de4f4a4152d44931038fc5046af1275053c96435ca7883bced060f31c0bbf3260752f58e0032e54c9e317f8c1c15da754938ee663e3970be86da8f50032aa711a2d33a8aaf65cb23125229e922a6b506bacb147e82ecc78c0172e0714678c051ac9b9446010d3c249c3d10ae889402800e0a4808894236fabec7824bd00024a4d3872400000fcf97066cb886294945ab0518f2569644b3231f8ead7aec549a39c6502b2170a4b14d86fc3b388fd4ad31f48b87681123641cf8c293f46cc4a61a185aa0d82d69fc4a342491b594302881b59fb1c9f4164112639620d291194021fe161e29583b5bcc7646224840e04fa046d1ec81d13ae0fb1b6128cbee4f0a1fa1e0da442f0001194ee0756ab106ec1d80000209b5d530b7a04e26c89f85a539b9bd40040fa000000058e6c20001e98a9cb02c161704000000218000108ea20524cb00d8a10c8001c543ea76a568871f6a60480fd023560eaffb2291f868e00000000011da38600000001930000002a446b85fb4abc0006806bb48d08eeb2674057900004512de1d12e4d2c437e00000000006c81e997842c44669dd96e078a7ce2e10000160b3d0001c0d6e447232f80003ce7951399f929860003ed80006ce64c2b8043a5d84689fe295c5fc000313000119211b22f00008b6abe29d000000000000009505d297848a205909ab7d1bf800020a78645f00006463d71b98dc966c0170b38c90046000183865e000b370002db49b200000000011406d035104dc90ead949c1ee4fd8b2e1482a480a86393b02456594068ca715e55be80600000001b802b00000000003b500aac8cf9145eb8302a01ca14a56b80008ee1a837fab8856a19a5aea3600429c042e1858cbc10e00000016946b117eabd0000000000099e000a0d1c40c98aa05764af800030f0003ec00
  | 23 => 0x430cf6a0036d0494f70b3a2eb981521c6782d183f08868620df00015fa67100022e84bcb3400023b8734ac700019c927408a3329d465980000000000000b3534f09410361743e640000009ec35928dc6240000d08001516ab90dd0d7961f8030000d0e5661b82a008aa00077f378a974b7a0003eea77cfce95657b8719212b190f126886aa6c73da9a2801993f1ac93f84fc6751c4800072c89050d1fa8000a674552a3510a0a7094db7409273c198c00000004d08140004fe00000000002483760d0e8090040c91d58fd00390003cd03c6000b514b3a5a66840004d60d5c00072200000007c47910000c26bf4a1ed561f4c0000001a2000163ea8f028acc400087c000198452c2792ca82a543cb3e54312750507e83ccea29056855539172d220211dc91db40f48814c4aa7c6c4a250d0146c000064beaac92c541f65c02870e3075e0b9800000018237508f8000000394c00035c924000000157a00000013d8e0a00044d0000000a14000154c00062330600002663562428f7d6008c640c80000002813f29af8000000210248472a000207000119400047c21d0000aee39788882731d60002738067a5636b144537c0b42292c2e07c2135842dfc9f0a033a5abf83d880732a9f1ef17ae306324ec41868947b9980bcc2d127786be9ac0004f6889e1009c952c13b13965c5000273d5e934d80015113b288e4bca39441c28818c19ca9a268100024c1470a6b00000000003661ad9450ff48b01791295704405552842ebb00005680000000b8f00009f4802ab3150a4ad2de7bb05fadbc71e6f44a20c410721ea3321bc0da88ab47145d81f02111af6e717284af02e16755fe58f3f059d02084bc35c04f915c6004db0ccc396b60321a658572b6631493b406a3ca41d062007f47b4abac691d45510da1d1d4423680f68ef8000669376042028c3ef2604ab01a0a9c2ac170c000a3600002080004bfae880006069ee000238c862000348863412c0003abaaaae1d43210b40a22582f43f140007229db297149400091e0001c30000000101000005e37c4a18000ff678d162a3d8000864b2380000002c4000000000000034810a00246d10a0000049a0005aaa45f05200034f99995045cf1cc02bc3ebadb26b95512ec5821ed028800000057326a40000000830c8400000041a43489440fe136ad8832210b4da002d5461685785efcdfa4b350703b8000a0f16da8a0c587ef2be1c4cfb40b60001c24c7600052a14149c28e14de210c000b4c0001d740002740000c500000000000e0c8d834d49980100003ff00000007b05ea00009552fe53b00023311de00000000000001c8143a07957ea3454d0f7600096c55d80000009c70002d7800016e29b06711527721169f486deadd07b1df105c5371afe86626c74e007897f3cc40f3e083552d200000000000000
  | 24 => 0x70a39087c8ce65ca53180014ec0003030c755c0b8a1181f841c4539482127ca3a6ac143000163966d3c2000056ca4e4fe56452fc32dbad08af3188fd31807093fc31e02313dc838a5b36e185cd1a0fd52f6aa47481fe356882964256880025d410c96e29e98f57226070df800040243e00019289dc28b3010a9451e000000000082668b21acae128c44637d000015800000024b5170ad31dea3406c290028393810a24a10f5a61018e4414c28f3d01a2215132264d0444010bdf214885b54d9ab5951c0005998fa904e2f314d27fcf50351834d1990f432a3ef8cd004070f53213549cc115000249ce2e0f29d00840f00ac60e3561888a0000000c69062752b17853ebc63e43140cc55ce6e90bb9c2c9040000000000b3000000001d75480005a42be00003d20000fc0000840262800000000000013e81c893550f9ce95706c905702980000004c18f752e479d0788344f5874c2a603fc11c0005882c0c0007ca8c826096500003e38000000b8109e1828e321130000488411acc40f9278fcc7c44be1e6d42a0003afa9b5250614049883c3f000052122900006de35787c4b2d0003d7c0012263f80001738c4e00000a17112d00000002b84ffc0002ba11708846340002d6c0004210000000ca25ac2c2a31d5188fe43f0ee90349225b615ec000000000241c45e0773a20c543e09980988b7e5d058a45b80015da64259d80003aa5da39f1b347d03eb253c7aa0008fdbe3000089024311b8f8358aa4d5c5a03cedc14241ad37c0007a428928367d82d250b20bc03e0425bb917d17a1950f4c00160300039a8a100009325371e482e243720e92e96e250a3fe1ce400000033e8000be633833d43990ad50b0cf83f358034641e8d4c9322190b1827456e77b41da92a05493e327ad115549d53f4842421432f14aa874b063fb53f230001aa225935d20ae678248e140a4c51cd20dae6c4d45322c801b8554acb4919c38ad65aa0cd91e43cc0004af085049673b8ba49ed6f8a0c3338f1c17622c0002aee6f67c915a2140aeaa4653f936c00046345da38030e38595e0efd0d42c32159be015aae81d8539c36639b10ea080a12b25a380970f637631a643a89063581042428bb27ed0d624d60144c422b18ac5ea8e3b220a7148a0003092af02980a012928a8b188880ec80003c830e0000ba84e00000000cb8e8a76518b268449022806582a800092f3d525680b49f0294125d47411e51581cc0cb81004d09ac1729603c853941640373cb45705295552db12e4922436c3b27c870aab049ea82547636e03381980d4a08026498e000ac22479b9c4dc1920ff434c2d22120aa00007a04593c0a8283070900000a9c7b60c79e1a6e05c762d30fa474efc50330a91f172ab7325aa14e5901bc569002f4035a72e6a9489e70001ad27615641e500280005cc7388e82
  | 25 => 0x98408000000000099c0002d04c3637452808013b88f0112ab3c8aa9742959c04000309000182448f7260000598000343045800167e93704d95206734e4274451c618a4319a8000c1000000000012a02a8000087002c449000000091a44db69e5500008b40110000000b431fe9e842829bf0000000000aa691e8434cd82079360ef0e0409717880013ba0000002b0c000a04327000000070d00027ccc2654300008d41019bb0bc81ac000569bad90113d42ce4798a305b2723000069800037a3e784372c2aae07dd2e10000000001d991cb0c13e1000098409e2c013413a20580002c88f664194740c800aa6a509a004420426047f80016e00003540d4b4603ed02f871d59c11213553886947f000023e8db63043ba2df80006965862dec44c1a935c8e13568311000299800000053da1d4e3c21f0678de56be1a2b4c88a6d60000400a0e070e5b70c79bb8a5837d32bea04b2f1383c58000800000000231511411446912385d7000413213c0006a740e800023a0004290000000b1344c000c00000056f15fc00033a529990067ea5e1cb99f007a9160bd80000000005301de15406aa0000c4d56214e22987620008eb000000028a0000000000f80293288091c00057e20f00000000003ef48197200001f0292d0d64e9ce2a544a3826bcd3a18539467901d85728ec1ffcae1ff48c2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe5710d4963040fdcaa21a92c6081fe976165258c100056bc0aa4b182000ad4815496304001c9f04a92c60800395e055258c100072a40aa4b18207fe4f2054963040ffc9a40a92c6081ff95c415258c103ff2a882a4b18207ea5e8514963040014bd0b212c608002976164258c100056bc0a84b182000ad48150963040011bd0e212c6080023761c4258c100052f42884b182000a5d8510963040014bd0b38ac608002976167158c100346f43ea2b1820008dd87d45630400153d09a8ac608002a76135158c1000567416a2b182000acd82d45630400d1bd0fa0ac6080023761f4158c100052f42e82b182000a5d85d05630400159d05a0ac608002b360b4158c100346f43e42b1820008dd87c8563040014bd0b90ac608002976172158c100054f42642b182000a9d84c856304001c9aa510ac60800297a142158c100052ec2842b182000e4d520856304001d8a4210ac608012b6a002158c100056cc0042b18200487c85dd953040090f90eb2aa6080123721d6354c100246e41eeca182000c9c43dd9430400193886bb286080038710d6550c100246e43ac6a182014a9c8458d43040011eb0db8a86080031d5977150c100066ab1ee2a1820008f5861c543040018eaca38a86080033558c7150c103fd36c3ceab10207ee67109d562040fdcca213aac408202b9e0575588100057240aeab102000c6f875d56204001ccf02baac4080039920575588100063638aeab10207fc6f705d562040ff8dae0baac4081ff99c4175588103ff32882eab10207ea6e851d562040014dd0bb9ac4080029b61773588103ed73c0ae6b102000ae4815cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd620400155d0929ac408002ab612535881000727a9ca6b102000a6e8590d62040014db0b21ac408002b9e0543588100057240a86b102000e8d4310d62040018daeb38ac4081f2ba602715881002c7743ea2b1020008ed87d45620400159d07a8ac408002b360f515881002c7743e62b1020008ed87cc562040014dd0b98ac4080029b61731588100055742662b102000aad84cc562040095d50018ac408002ba60031588100072ba8ac72882000e675158a51040018f2cab84a2080021fe19758c4100061f322eb1882023c5e635d631040018dcc4bac620810f1d985758c41033c3fc3acb188202387d87596310400187ceab2462080030f5d5648c4100246fc3ac71882000c5e7558e31040018baeab1c62080031b9d5628c41000636baac51882000cd9635c231040019d0e5bb220080031ee1776440100063c42eec8802000cdb83dd910040019b107bb220080033ae0b764401000674416ec8802000c7b52dd910040018f2a5bb220080031eddb75440100063dbb0ea8802000cdb76dcd10040019b6ec39a20080033addb7244010
  | 1 => 0x90ca9c6288002b5219438c510006b2baec518a2000ec463d8a3144001ca863b2a62880bf361c3634c5100247a432ea98a2035c7476d953144001ca8c7b2a62880ef1d1d8654c51000732310ca98a200097585dd131440091e90cba2628820b2d1db644c51040e5a3b0c898a2000e94631913144001d48c4322628800b351db734c51017e6a3b6c698a2038ce476d89314405fba6e638262880031dd97715411000672316e2a822000c77651c550440019c8c438aa0880125d21d51541100253a432a2a822004b708054550440010fd0dbaa60880030f193754c1100de2e31eea9822000c6c62dd530440ab0fd0fb2a608806e1f21f654c1100061fbaec89822000c3c75d9130440018beebb1a6088003171d7634c11000637baec49822000c6c75d893044001968c9b8a60880033918b714c1100065a320e29822000cd7631c530440019c8c438a60880127521d314c1100256a432629822004bd0804c5304406b8f4edb2e208800f1e9d865c411017e6d3b6c78822002cda7618f10440719d4edb162088002dc61631c41100243f43ca6b282000a3e8494d650400147b0929aca0800317dce535941000c3e42ee4b282000c6f525c965040011e902b92ca080121fa1e52594100243e43aa4b282000c6f7254965040014e902a92ca080028fa1273594100051ec24e6b282000c5f739cd65040010fd0f21aca080021f61e43594103f63b886e4b28207ec7510dc965040ff0fb0f392ca080029de0572594100053a40ae4b282000c6f825c965040018ef02b92ca080031d20572594103fe3b882e4b28207fc75105c965040fd0fd0e392ca080021fa1e32594100043ec3c64b282000a77814c965040014e902992ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca0801e1fa1f31594100043ec3e62b282000a3e84cc5650400147b0998aca080029ba0b315941000536c1662b28200787e87c8565040010fb0f90aca0800297a0f21594100052ec1e42b282000c6d7288565040010fd0e10aca080021f61c215941000636b9042b282000e6521085650402917d09baac6080022f6137558c1001c3f42ee8b18200087d85dd163040091bd0fa9ac60800317dd75358c100246f43e86b182000a5e85d0d63040014bb0ba1ac6080023d2057258c100246f43c64b182000a5e858c963040014bb0b192c6080123721d3258c100056a40a64b182000a9e84dd5630400153b09baac60800317dd67558c100052f42ee8b182000a5d85dd163040014bd0b3a2c608002976167458c100056a40ae8b182000c9d741d163040011bd0f2a2c6080023761e5458c100070faa4a8b182000a5e859c963040014bb0b392c608002b5e057258c100056a40ae4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b18207e
  | 2 => 0x57650d100064e218eca1a2000e1c43d9543440291bd0fb1a8688052a7a136350d1000537436ebb122000c6e76dd76244001ac8e3baec4880029ba1875d8910006373b0ebb122000c6e76d9762440011db0f32ec4880029ba1665d89100056741ccbb122000acd8399762440011df0eb2ec488002b3e0d65d89100056641acbb122000a6e8619762440018dcec32ec4880039960465d8910006673b6c7b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000727baec7b122000e4c75d8f62440011db0f31ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec488002b3a0e63d891000477c3ac7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000ace8618f624400199cec31ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec48800393dd463d8910007263a8c7b122000ec58118f62440018dce3baec4880031b1c775d891000636b86ebb122000a6e859d7624406f5cd023aec4880e2b960475d891000537438ebb122000c6e871d76244001ccd023aec4880039960475d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000537c2ae7b122000a6c855cf62440635cd0239ec4880e2b960473d891000557424a7b122000aad8494f6244001c9ea729ec4880029ba1643d891000536c2c87b122000e8d4310f62440711dd0fa8ec4880023b61f51d89100056741ea3b122000acd83d4762440711dd0f98ec4880023b61f31d89100053742e63b122000a6d85cc7624400155d0998ec488002ab61331d891000637baee1b12202bae681dc362440019c8c53b4a28800e9da1b65945100063b3b6cb28a2000e5465d8e5144001ca8ca31ca288003a5190639451000762310c728a2000a748654e5144001cc8cbb14a2880d71e1c3655451001e3a3b6eaa8a2035c7476d955144069aaca7b9aa2880bf351db63545101ce6a3b0c6a8a2000e946418d5144001d88c431aa2880e3391db62545101aeb9ba8e0a8a202187c865d63144001878c8bac628808f1718d758c51000636312eb18a200087f87d9631440170fb0fb2c62880030f9d7648c5100061ebaec918a2000c5e75d8e31440018baebb1c62880031b9d7628c51000636baec518a2000ce4629da31441072eb0f3ac628819f9518e758c51011f2a31aeb18a2034d54635d631440012ef04bac62880025d609758c510006b2312eb18a200097787d963144001ca8c7b2c62880025d61c658c5100072a318cb18a2000e646219631440011ed0dba462880025d617748c510004f2c16e918a2000d3575d923144001d28c7b2462880032d9d8648c5100069aba8c918a2000e94631923144001d48c4324628800ab5a1b638c5100066b3b6c718a2000d5575d8e31440015a
  | 3 => 0x4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000637c2ee4b1a2000c6c85dc963440010ff0ab92c68800e1f2157258d100045fc22e4b1a20148bc845c963440011bf06b92c6880023de057258d1000477438e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440010fd0fa92c68800e1f21f5258d100061fba6a4b1a2087c3c74d4963440018dee5a92c6880071b1cb5258d100043f43aa4b1a200087c87549634400187ee8a92c68821b0f1d15258d1000637b92a4b1a2001c6c725496344001968e9b8ac688003391cb7158d100062f3b6ca31a2000a5d82d946344001caae3b28c6880023761e6518d100052f42cca31a2000a9e84994634400153b09328c688002b3a0a6518d1000566c14ca31a20008df87594634400153f08b28c688002a72116518d1000567c12ca31a2000acc8259463440014bd0c328c688003179d86518d100052ec10ca31a2000e55811946344001caae2328c688003279db6418d100070fb2ec831a2000e1c65d906344001d2ae3b20c6880023761e6418d100052f42cc831a2000a5d85990634400153d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc82590634400193cec320c68800387d946418d100070e328c831a2000e9571190634410bd2c20320c688217a50406418d100046ec3cc431a2000a5e8598863440014bb0b310c688002a7a126218d100054ec24c431a20008df8758863440014bf0ab10c688002972156218d100054fc22c431a2000a9c8458863440015af02b10c68800297a146218d100052ec28c431a2000e4f651886344001c98ca310c688003a3d906218d1000746320c431a2000e4e851886344001c9b0a310c688003b16046218d1000763388c431a2000ec5711886344109d8c20310c688213b10406218d100052f436a431a2000a5c86d4863440018bceda90c68800387d935218d100070e326a431a2000e4f62d486344001c98c5a90c68800297a195218d100052e432a431a2000c5e765486344001c3ec8a90c688003871915218d1000727b12a431a2000e4c6254863440015ad0d108c688003a51922118d10007623144231a2000f455288463440735a90c908c688003a51912118d10007623124231a20148be84dd9534400117b09bb2a6880063ba0b7654d1000476c16eca9a200087f855d9534400117f08bb2a6880522f2117654d100046fc1aeca9a20008ef825d953440031d904bb2a68800a1fa1f6554d1001c6f43ec6a9a200387e85dd943440010fb0bbb286880063ba0b7650d1000476c16eca1a2000c9c439d943440010ff0abb2868800e1f2157650d100046fc1aeca1a20008ef825d943440031d904bb286880023de0
  | 4 => 0x344001c3ecbb26c6880038719764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d100052fc2ac5b1a2000a5c8558b634400153f08b16c688002a721162d8d100052f428c5b1a2000a5d8518b6344001c9eca316c6880039319462d8d1000747b20c5b1a2000e4e8518b6344001c9b0a316c688003b160462d8d100052f436a5b1a2000a5c86d4b63441138bceda96c68800387d9352d8d1000727b16a5b1a2000e4c62d4b63440014bd0ca96c6880029721952d8d104462f3b2a5b1a2000e1f6454b6344001c9ec4a96c6880039318952d8d100076231443b1a2000f4552887634405f5a90c90ec688003b118921d8d100054fc22ebb1a2000a9c845d763440018baea3aec688002b5a0475d8d1017d6ac08ebb1a2000c9f749d363440014bf0aba6c6880029721574d8d100052f428e9b1a2000a5d851d363440015ad023a6c6880beb560474d8d100046f43ca9b1a20008dd879536344001c3ea92a6c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c68800297a1472d8d100052ec28e5b1a2000ad6811cb634405f5ab02396c68800393e0952d8d100052f42c85b1a2000a5d8590b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440014bf0ab8ec6880029721571d8d100054fc22e3b1a2000a9c845c7634400159f04b8ec688002b320971d8d1017c6f43ea3b1a20008dd87d47634400153d09a8ec688002a761351d8d1000567416a3b1a2000acd82d47634405f1bd0fa0ec6880023761f41d8d100052f42e83b1a2000a5d85d07634400159d05a0ec688002b360b41d8d1017c6f43e43b1a20008dd87c8763440014bd0b90ec6880029761721d8d100054f42643b1a2000a9d84c876344001c9aa510ec68800297a1421d8d100052ec2843b1a2000e4d520876344001d8a4210ec68800297a1770d8d100052ec2ee1b1a2000a5e85c8363440014bb0b906c6880039354b20d8d1000726a9241b1a2000c5c63dd563440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd16344001938c7ba2c6880030fdd76458d100061e3aec8b1a2000cac72d9163440031dd0db92c6880031bd977258d100063632ee4b1a2000caf64dc96344001998c7b92c6880031bdd46258d10006363a8c4b1a2000caf741896344001958e8312c68800e1fa1f7558d100043ec16eab1a20148be87dd1634400187eebba2c6880030f1d77458d100061fba8e8b1a2000c3c751d163440018beebb9ac688003171d77358d100064fba6e6b1a2000c9c74dcd63440031dd0fb92c6880031bdd77258d10006363aee
  | 5 => 0x80029d60653d951000637a96e5b2a2000a758194b65440030ff0ea96ca880031b5c952d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d951000636b96c5b2a2000a5e8398b65440014bb07316ca8800297e0d62d95100052e41ac5b2a200b87d8718b65440018dae4316ca880031b61c62d951000732c08c5b2a2000e6462887654406b4e90c90eca880039918921d95100051f420e7b2a2000a3d841cf65440018bae639eca880029da0473d95101ad3ac08e7b2a200087e8790f65440010fb0f21eca880031be0972d95100053b408e5b2a2035a75811cb65440010fd0f196ca880021f61e32d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100052fc1ae3b2a2000a5c835c765440014df04b8eca880029b20971d95101ac3f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100053741663b2a2000a6d82cc7654406b0fd0f90eca880021f61f21d95100052f41e43b2a2000a5d83c8765440010fd0e10eca8802e1f61c21d95100073290843b2a200087e87c8365440010fb0f906ca880031bdcb20d951000637b9241b2a2000c5c65dcd65440018d8cbb92ca8800333dcc625951000666398c4b2a20028de87dcd65440018beebb9aca8800327dd373595100062fa96e6b2a2000c5f751cd654400193ee839aca88003271d0735951000c7743ee4b2a2000c6f75dc9654400199ee7b92ca88003331cf725951000637c2ee4b2a2000c6c85dc965440010ff0ab92ca8800237e0d72595100146e41ae4b2a20008f7815c965440011dd0e392ca880031bdd4725951000667b98e4b2a2000ccc731c965440030f90ea92ca8800317dcd52595104462e39aa4b2a2000c6f7254965440038d8e4a92ca88003391cb71595100043ec14ec32a2000a3e8498c654400147b09318ca880029ba0a631951000536c14c632a200087f87d8865440018dae5b10ca880021f61e62195100052f41cc432a2000a5d8398865440010ff0eb10ca8800297e0d62195100052e41ac432a2000a778158865440070fd0e310ca880021f61c621951000636b90c432a2000c6d871886544001ccb02310ca88003999c4621951000732b88c432a208ae66101886544115cc820310ca880029da1a2119510006b2b944232a2000e646288465440774e90c908ca880039918921195100045fc22ebb1a20148bc845d763440010ff0aba6c68800e1f21574d8d100062ebaea7b1a2000ad581d4f63440014bd0ba1ec6880029761743d8d100052f42c65b1a2000a5d858cb63440031bf0e996c6880029760b65d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052ec10cbb1a2000e55811976
  | 6 => 0xa45f420ed28a60008bd841da514c0378bce7b2ca29800317d957394530014afc3aa728a6003a5c8654e514c0070f90a3b2a2980031794c765453001c3e42ced20a600087f855da414c0070f90abb4829800e1fa1476905300043ec28ed20a600087c865d6414c0010ff0fb2c82980021f61f6590530014cfc3a8720a6014a9c8650e414c00193ceca1c829813b479d5439053046f0e32a8720a600387e85dd9414c0010fb0bbb2829801237219754c5302c62e3b6ca98a6056c5c76195314c0012bb0bba2629801237219744c53007c6f438c298a6000e5765185314c0378b8e7b2aa09800317d977354130024ae43aa6a826004a5c8654d504c0096b100a9aa0982321fa1f65501300dc3e43ecaa026004a9c8650d404c005938eca1a809822f871954350130025cc40286a0260028de83dcb65c40011bb07b96cb880061fe1d52d971000636b92a5b2e2000a3e8494d65c40018bee729acb880061f21d525971000637b92a4b2e2001c6c7254965c40070ff0ebaec7880021fe0975d8f1001c3f42ee5b1e200087d85dcb63c402917d09b96c7880022f61372d8f1001c3fc3ea5b1e200087d87d4b63c40010ff0ea96c7880021f61d52d8f1000c6fc3a65b1e200387e85dd163c40010fb0bba2c7880031bdc95258f1000e36392a4b1e20148be84dd953c400117b09bb2a7880063ba0b7654f1000476c16eca9e200087d859d953c40050fd0fb2aa78800e37a1f6354f1001c3f42eeca1e200087d85dd943c40031dd05bb287880023b60b7650f1001c3f42ceca1e200087d859d943c40031dd053b287880023b60a7650f100a46f43ec6a1e2027a5e85d8d43c402953d09b1a878800e9de1965947100053bc32a728e200487e87d9551c40013ab07bb2a3880027960b765471003e3bbb6eaa8e2000c7776d9551c40016e301b2aa38810f5594f73547100247ac36eb18e2067c75769d631c40478eaecbac63880025de09758c710004bac12eb18e20048f586dd231c40012eb0bba463880027960b748c710006b8baae118e20048de87d8d31c40012eb0bbb263880026d613764c710004f2c16ec98e200097585dd131c40017a301b1a63880125d21d5154310024ea43a6298620008df835c965840051b906b92cb080121f21d525961000637b92a4b2c200387e87dd563840010fb05baac7081631dc437558e102c63a886eab1c200087f855c963840070f90ab92c7080022fe117258e100a45e422e4b1c200087e87d4963840070f90fa92c7080021fa1d5258e100043e43aa4b1c20048dc874c963840b10ff0abb2a7080121f21d6554e100246e43ac6a9c200087f855d943840070f90abb287080023be097650e1000c76412eca1c20048dc8758d438404f4b90ab1a8708052a72116350e100051f424a7b2a2000a3d8494f65440018bae729eca8
  | 7 => 0x6f72549654c0014bb07320ca9800353cc972195300043fc3ec432a6000c6d72d88654c0010fb0f310ca980021fe1d62195300051fc22c432a6000a3c84588654c0014bf06b10ca980029de0562195300053a40ac432a600387e87188654c0010fb0e310ca980028fa1062195300051ec20c432a6000c6d72188654c0ad4b90c990ca98157171cc65d91300146e41aebb22600087f855c7644c0070f90ab8ec89800a3720d71d913000477c12e3b2260018ec825c7644c0010fd0fb2ac8980031b1cb65591300043f438cab226000c6c72195644c0018decbb92c8980031b19772591300063bb2ee2b226000c7465dc5644c0018eeca38ac8980031d19471591300065a320e2b22600387e87dd5644c0010fb05baac8980063ba1f725913000637baee4b226000c6c75dc9644c0018df0bb92c8980031b21772591300043fc2ae4b22600387c855c9644c0011bf06b92c8980023de0572591300047a40ae4b2260008ee871c9644c0018deea392c8980031b1d4725913000667b98e4b22600087e87d49644c0070f90fa92c8980031bdcb525913000e36396a4b22600087e87549644c0010f90ea92c8980031bdc9525913000e36392a4b2260018dc874c9644c003998e4992c8980031ddd771591300063a3aee2b226000ce772dc5644c0019c8e5b8ac8980031dd4b71591300063aa96e2b226000c77751c5644c0018e8ea38ac89800335dcc715913000673b90e2b226000ce4721c5644c0018eea438ac8980031d54871591300066b990e2b226000cd5321c5644c0010ff0abb2a8980023be09765513000c76412ecaa260008f7815d9544c0011e902bb2a8980031794c76551300a43f43ecaaa26014a3e84d95544c0b18b8edb2aa69800a576177454d3028e8f2a6e8a9a60398de86dc5534c00133b09b8aa6980027360b7154d302c6adba8e0a9a6027c5c65dd5434c00533b09baa869813b47d537550d300246e432eaa1a6055a5e86d95434c0b18b8edb2a8698003871936550d302b62e3b0caa1a6000e1c64195434c02953d0db228698003871976450d301cc6f436e2a1a600095d85dc5434c00139b05b8a86980021fe1574d853001c3e42ae9b0a6001c6e7254b614c0018dae4a96c298002b9a0b41d85300055b42643b0a6000ce772087614c001ccaa410ec2981621f21b75585300043f43ecab0a6000c3c74d95614c0018d8e5b2ac2980021fa1c65585300061e3a0cab0a6000c6c72195614c00187ecbba2c2980030f197745853000637b2ee4b0a6000c6c65dc9614c0011ef0eb08c298002ad211611853000572412c230a6014c9c7450c614c0015af02a18c298002b5e0532185300056ac1e8230a6000ae682d04614c001d2a86208c298002ada1321185300056ac1e4230a6000ce572084614c001ccaa4108c298003b14c821185300
  | 8 => 0x63ba2c31820b27cc374586304164e986e8b0c6000c3f751d1618c001878ea3a2c3180063ba1f725863000637baee4b0c6000c6c75dc9618c00195ee9b92c3180032b1d3725863000637c2ee4b0c6000c6c85dc9618c00199863b92c3180e333cc372586301c666986e4b0c600087f855c9618c0070f90ab92c3180022fe1172586300a45e422e4b0c6000c6f751c9618c0018d8ea392c3180032bdd07258630006563a0e4b0c600087e87d49618c0070f90fa92c3180030fdd3525863043e1e3a6a4b0c6000c6f72d49618c0038d8e5a92c3180021fa1d52586300043e43aa4b0c6000c3f74549618c10d878e8a92c3180031bdc9525863000e36392a4b0c6001ce472885618c001ccaa510ac3180123d21d215863000e7239242b0c60048f587986518c0074ed0b30ca31800e9d21561946300045fc22eca8c60148bc845d9518c0011df04bb2a3180063b20976546300062eb2ee6a8c60048f487585518c0070fd0bbb483180021f61776906300247ac3cc320c6000c7575986418c0018eaeab0c8318052ad21161906300043fc2aeca0c600387c855d9418c0011df04bb283180063b20976506300247a43ac2a0c6000a5f85592318c0731bf0eb0c631800297e15618c6300054fc22c318c6000acf82586318c001ab2eab8463180030f5d254d95300052ec1ca9b2a6000a5d8394b654c0030ff0ea96ca980031b5c952d95300045fc22e3b2a60148bc845c7654c0051b906b8eca980023be0971d953000c76412e3b2a6000c6d72d8b654c00147f08b16ca980028f21162d95300053bc0ac5b2a6000a748158b654c0270fb0e316ca980028fa1062d95300051ec20c5b2a6000c6d7218b654c0b14b90c996ca980039318932d95300061fba4e9b2a6000c3d741d3654c0374bd063a6ca981629760c74d95300043ec3ce5b2a6000c6f825cb654c00147d08396ca980028f61072d95300dd2f418e5b2a6058a5d831cb654c0010fd0f216ca980021f61e42d95300043f43885b2a600087d8710b654c0374bd06216ca980029760c42d95300051fc22e3b2a6000a3c845c7654c0014bf06b8eca9806e9720d71d953000537c12e3b2a6000a6c825c7654c00147d0838eca980028f61071d95302c52ec18e3b2a600087e87d07654c0010fb0fa0eca9806e97a0f41d95300052ec1e83b2a6000a6e82d07654c0014db05a0eca980021fa1f21d95300043ec3e43b2a6000a3e84c87654c00147b0990eca9806e97a0f21d95300052ec1e43b2a6000c6f72887654c0010fd0e10eca980021f61c21d953000637b9043b2a6000e6521087654c0370fd0f906ca980021f61f20d953000637b9641b2a6000c6f72483654c0010ff0ab92ca980022fe1172595300a45e422e4b2a60008df835c9654c0011ef02b92ca980023d205725953000c3e43aa4b2a6000c
  | 9 => 0x219865000e723924330ca000c5c53dcd61940051bd0fb9ac32800327dd373586500062f42ee6b0ca000c5d85dcd61940018b8a9b9ac32800317d4b73586500062e28ee6b0ca02fc5f50dcd619405f8baa1b9ac32800327dd073586500064e3a0e6b0ca00087e8794d619400147d0929ac3280030fdd253586500062fb9ca6b0ca000a768194d61940018dea5b92c3280063ba1f725865000667b9ee4b0ca000ccc73dc961940018df0bb92c3280031b21772586500063729ee4b0ca000c6c53dc961940018d8a3b92c3280e31bd4372586501c636a86e4b0ca0008df835c961940051b906b92c32800333dcc725865000666398e4b0ca000c5f7354961941118b8e6a92c3280031bdc9525865000e36392a4b0ca001ce4728856194001ccaa510ac3280123d21d215865000e7239242b0ca00087f8758e51940378bce6b1ca3280ee1fe1d61946500052fc1ac328ca000a6f8258651940018bca6bb463280123d61e618c6500063abacc318ca000c757558631940055a906b0c63280039594d618c6500045fc22ec98ca0148bc845d931940011df04bb263280063b209764c6500062fbaac698ca0048f48758531940050f90aba6c6a80029761632d8d500143e42ae3b1aa0008bf845c7635402917908b8ec6a80023be0971d8d5000c76412e3b1aa08f87e86dd153540770fd0db8aa6a80024f6137154d50004b6c16e2a9aa00487c865d543540291bd0fb1a86a8052a7a136350d5000e37392a5b0aa000c6d7254b61540014eb0b90ec2a80029d61421d855000673b9043b0aa000e655208761540011ef0eb08c2a8002b9209611855033c3fc3aa630aa000c6f525c861540018dee4a90c2a80029de0552185500053ac2e4230aa000ce5720846154001ccaa4108c2a815a1fa1b735455011e2e31ee6a8aa01087e87185515400117f08bb462a80522f211768c55001c3f428ed18aa023c5c635d631540018baebb1c62a800e57e1d538c5500152e432a718aa00487c865d5315400117f08b92cb180522f21172596300047bc0ae4b2c60008f4815c9658c0090f90ea92cb1800297e0d525963000637b92a4b2c600387e87dd5648c0018bd07baac9180031760f75592300043ec16eab246000c5c31dd5648c11d8be61baac91823b174c375592300043fc2ae4b24600387c855c9648c0011ef02b92c9180023d20572592300043f43ea4b24600387c87d49648c0010fd0ea92c9180021f21d52592300245e43a84b246000cd431dc5648c11d0ff0abb2a9180121f21d65552300245e43ac8aa46000c6f7254a618c0038d8e4a94c3180123d61e219863000732a944330c6001ce472486618c0070fd0fbaac3180021f60b75586300062e18eeab0c6035c5f30dd5618c06b8ba61baac3180522fa1f74586300061fbaee8b0c6000c3c75dd1618c001938
  | 10 => 0xb24620087d87d4b648c4038dce5a96c9188031b5cb52d92310043fc3aa5b24620087d8754b648c4038dce4a96c9188031b5c952d923100c6fc3a65b246201cce724cb648c4018eaeb38ec918803395ca71d923133e2f39ccab246200aae82dd1648c52556d03ba2c91880a3d20572592310062f29eecaa4620087d859d9548c4031dd053b2a9188023b60a76552310a43e43acaaa46214a3c84595548c4438beecb2aa71880a576177454e3136e8f2a6e8a9c62238dd86dc5538c40133b09b8aa7188027360b7154e3133eabbaee2a9c6227c5e65dd5438c40533b09baa87189ab47d537550e310062fbb4caa1c6200e1e64995438c4cf4bf0cb2a871880317dd96550e310070f322caa1c6214a9f86591438c401c3ccab22871898a3761b7150e31004aec2ee2a1c62009cd82dc5438c4478bce6b2ca318803175957394631014afc3aa728c6203a5f8654e518c4016af02a9ca318a461fe1d659063111c3ec3acb20c6214a9f8650e418c40593aeca1c8318a37879954390631005cbc0a8720c6214c9e7450d608c4010fb0f328c1188030f9d2651823100637394ca304620087f87594608c40187ce8b28c1188031b9c9651823121e3b38aca3046200c3e655d0608c40187acaba0c1188031b995721823100636b2ae430462008fb87580608c42917d09b96ca988022f61372d95310046ec1ee5b2a62028f581dcb654c4030ff0ea96ca9880297e0d52d953100636b92a5b2a6200c3f74951654c4474bd072a2ca988061f21d525953111d2e41aa4b2a6200c6f72549654c4038d8e4a92ca988029d205525953101c3fc3aebb226200c5f835d7644c4018b906baec8988021fe0975d91310062e18aebb226200c5f305d7644c4070fd0bb96c8988021f61772d91310046ec1ee5b2262028f581dcb644c4070ff0fa96c8988021f61f52d91310043fc3aa5b22620087d8754b644c40317f0ea16c8988031bdc9525913100e36392a4b2262008dd83dd9544c4031dd05bb2a8988023b60b76551310043ec2cecaa2621487e87d95544c40717d0fb22a89880a1fe1d65945310062fb2ee6a8a6223c5e765d6314c447aace2bac629880e37e1d658c5310052ec2ec918a62148df87592314c4051b90cb8462988bf36181708c53100637b92a5b026201c6c7254b604c45f8bec6ba8c0988bf27d8d741813117e67b1ae430262008fb87580604c4010fd0f2a2c72806e97a0e5458e500045fc22e4b1ca0148bc845c963940011ef02b92c7280023d2057258e500dd2f41aa4b1ca0048dc874c963940014bf0a992c7280023be097650e5000c76412eca1ca0008f7815d943940011e902bb287280025e6037550e500246e43ac6a1ca000c5f7558d439402953908b1a8728243871516350e5000637b92a530ca001c6c7254a61940091eb0f10cc3280039954a
  | 11 => 0x5452bc38a9b1a86a880e3da1b7150d5101c3ec3ec728aa223c5e73d8e51544070f90cb84a2a88d71e181709455100637b92a5b02a201c6c7254b605446b8becab98c0a88d71bd9572181510047dc3ac0302a2148be84dcb658c40117b09b96cb188061fe1d52d963100636b92a5b2c6200a5d83192658c401a9e64b94cb188028fa1362996310051ec26c532c6200a5d83d8a658c40147d09314cb188028f612629963100636b94c532c6200c6d7258a658c4014bf0c994cb188030fdd254596310052ec1ca8b2c62028f4815c9658c4010fd0f292cb188029760e525963100c3e43aa4b2c6200c6f72549658c4014e902a92cb188021fe1972596310043f43ec4b2c6200a3e84d89658c40147b09b12cb18a529da07625963110c3f43cc4b2c6200a3e84989658c40147b09312cb188031bdca625963101c3f43ac4b2c6200c6f72589658c4010fd0e312cb188039398932596310061fba4e8b2c6223a5e839d1658c4014bb073a2cb188030f5d074596310043ec3ce4b2c6200a3e849c9658c40147b09392cb1888e97a0e72596310052ec1ce4b2c6200a77815c9658c4474e902b92cb188031be0972596310063bc0ae4b2c6200c74815c9658c4010fd0e392cb188021fa1e42596310043ec3c84b2c6200a7781509658c4014e902a12cb188021fa1c42596310043ec3884b2c6223a5e83109658c4014bb06212cb188861fa1f41596310043ec3e82b2c6223a5e83d05658c4014dd05a0acb188029b60b415963110c3f43e42b2c620087d87c85658c40147d0990acb188028f613215963111d2f41e42b2c6200a5d83c85658c4018dae510acb188021fa1c215963111c3ec3842b2c6200c6d72085658c401cca4210acb1888e9da0670596310051fc22e0b2c6200a3c845c1658c4014bf06b82cb188028fa1070596310051ec20e0b2c6223a5e831c1658c4014bb06382cb188029ba08705963100536c10e0b2c6243a76811c1658c4434eb02382cb188021fa1c40596310043ec3880b2c6223a5e83101658c4014bb06202cb188029ba08405963100536c1080b2c6200a7681101658c4014eb02202cb188021fa1f20596310043ec3e40b2c6200c6d72c81658c4014ed03102cb188029d606205963100636b9240b2c620087e87081658c4010fb0e102cb188028fa1020596310051ec2040b2c6223a5e83081658c4014bb06102cb188029da0420596310053ac0840b2c620087d87997648c4018dce532ec9188021fe1d65d923100637392cbb246293c7671597648c4018dccab96c9188031b59572d923101c3fc3aebb24620087f825d7648c4070fd0bb96c9188021f61772d923100476c3ce5b246200c6e759cb648c4018daeb396c9188063be1d72d9231006373aae5b246200c6d755cb648c4018dd0ab96c9188031b61572d923101c3fc3ea5
  | 12 => 0x8031b94d72d85530063629ae5b0aa600c6c515cb6154c0199862b96c2a98031bd4172d855300667982e5b0aa68887d8754b6154d0d87ce8a96c2a98030f5d152d855333d2e41aa5b0aa603c5d7354b6154c038dce4a96c2a98031b5c952d85534be3abaec330aa6008f7875846154c018dee4a90c2a98031bdc952d81532c61fb2ae8302a658c6f655c86054cb18eecab88c0a98023ee1d60181532c53dc2ac0302a6148dd83dcb6550c011ed03b96caa18023d60772d954300c3fc3aa5b2a8600a5f8354b6550d0d8bae6a96caa18031b5c952d95434b62fbaee6b2a860187c875496550ca54b906a92caa18031bdc9525954300e36392a4b2a86018ee82dc56550c011db05b8acaa18034710d75d8543006c621ae5b0a8600c5d739d76150c070ff0ebaec2a1803175cd75d85430043fc12ebb0a8600c5c315d76150c018be60baec2a180e1fa1772d85430043ec2ee5b0a86148dd83dcb6150c011db0f396c2a18031b9d672d854300636bace5b0a8600ccd739cb6150c031df0eb96c2a18031b9d572d854300636baae5b0a8600ccd735cb6150c018dd0ab96c2a18031b61572d85430066618ae5b0a8600ccf305cb6150c070ff0fa96c2a18021f61f52d854343e2eb9ea5b0a8601c6e72d4b6150c018dae5a96c2a18021fe1d52d85430043ec3aa5b0a8686c5d7354b6150c038dce4a96c2a18031b5c952d854300e7339443b0a8600e65528876150c031ef0e90ec2a1807399c921d85430068e21aeb30a8600d8c435ca6150c018eaebb0cc2a1803395cb61985430047bc3ac230a8692e94435846150c018dee4a90c2a18071b1c9521854300e663926430a86018f5878846150c01ccaa5108c2a1803b14ca211854300e723924230a860087f855c06150c070f90ab80c2a18023be09701854300c76412e030a8600c6f7254b6050c038d8e4a96c0a1807331c932d814301c3f42ce3b02860087d859c76050c031dd0538ec0a18023b60a71d81430068e21eeab028600d8c43dc96050c01b2887b8ac0a18036510c71581430068e21aea3028600d8c435c86050c01b2887388c0a18036510d71181430047dc3ac030286038f4815c963944014bb0b192c7288021f61b7454e510f43ec36e2a9ca20093d84dc553944012db05b8aa7288523721d6350e510a54e422c6a1ca20397685dc543944071eb0c38a872880e5da147150e510066ab18e2a1ca25587c8754d60944018dea5b92c1288031b5c952582510047dc3ac0304a20087d8795363544474bd072a6c6a88522fa1372d8d510045ec26e5b1aa2038f581dcb63544474bd06a96c6a88029d20552d8d5100c6fc3a65b1aa200a5f854cb63544010fb0bbb286a88063ba0b7650d5100476c16eca1aa2018ee829d943544011db053b286a885237a1f6350d510062fbaec6a1aa214a9e84d8d43
  | 13 => 0x6813004c03800411004400c00000802800801402c00001c03401c02002000006002400406c01800800400003000403c02000c00400400006801c00400001004401c01403010c00406000c00000403000002c03405000001802000000001400001806c01003400c00c0000300700080040540440b400001c00c02400804400400000400000c05001001800800401805403405800000000001003000000002802000000805405c01c02005000000000c00400403001000c03800002800006c00403c01000000002c00800400800003800c00001c00802800800006000c02c05800004c01801415801801007c11000c00800000003400401804c01008c00c02c00400001802403c0200680b801008409800401000c00403400800006c00002408c00412403c0080000000000040040480100000040380140040740200041300000040740c803800002c02400000c01005800000401001000000002000400c0040600f401000000404000400800800400c00005001801004001004800804c0000f00080500840141180080100000080000700080000140000c00080b00100c402800404801403807000805801c02801c00404002000c0000040000180740480000ac00804406803c00800c00c00c02003400800801802800c00008c01001c04001c01800000800802805000001400800c01407801001400001000000403800401401800002000402409400800400001404c00800001006c05c00807400413800800800406401803401803400801c0b80040e00b000000401000405000804000802400400c00000400000800001000403c01800407400000004404006c00807400c00406c01002c01000c00002404800401c0080000440580080040040000000080000040ac0100400b806800400400000400c0080300000b808000000c02808c03403800800000000c02000000c0300cc000010000050fb0bb96c8a980e3760f72d91530047b40ee5b22a6008f581dcb6454d110fb0ea96c8a99ea9720d52d91530066a18ae3b22a600c3d759d36154c0193ae73a6c2a98030f15174d85530a45fc3ae9b0aa600c3d755d36154c0193ae6ba6c2a98030fe1574d85530061e42ae9b0aa600c3e535d36154c01878a6ba6c2a98030fd4974d85530061e28ae9b0aa600c9c315d36154c0187ea0ba6c2a980327cc174d85530043ec3ca9b0aa600c3d749536154ccf4bd072a6c2a980f175ce54d85530143ec2ee5b0aa6148be84dcb6154c0117b09b96c2a980e3760f72d855300476c3ce5b0aa600c6d759cb6154c0195ce9396c2a98032b5d272d855300666b9ce5b0aa600c6f525cb6154c031df0eb96c2a98031b5d572d8553006573a2e5b0aa600cad745cb6154c0199ae6b96c2a98031ba1572d855300636c2ae5b0aa600c6e545cb6154c018d8a8b96c2a9
  | 14 => 0x8f1181368ffebe3468e18e611f8001b397d19380000028d80000036c0abc00344a0867ca490001f383983937b4000fee25a29287a2b000000042b3f96a801b4a910b0a2108cd31a36a98d8222288760000001e38000002e496c9b400009f9720000f41590000001d72c5124367c0000017a000000000297e1919baee0a08000f10c4d221780ec1ba8e51d003128113bb6508e80028f80000009b1f50002440168003572b73218001e708b29e95809f0000ab40000000036d932a70b5c7428dd9d633430e13f800216add2fb291800329297800199e5d352338000383b7a0000000bfacb80000019a5963222c99d30002b08b18ae34e919b22acfb682fd8001d276d17c74020f97f4002932300369619791a52ab4c492328c83229d23511897c8308d9819a3a8001c4857981000000100d2a000179a318ea1b615a9f75774f5b8187b1fe2788703780001a313eab8aa96aab62a5bb9bb715a6aec8ead730a5330ad39809b1011075b51a500000372e9adb8e400017591c92d80000033d2d580026285d82b2b4b6b4d0a759cd90617796f80000017cc6b144a2187e8c3cc59eab729c00cf16b90b2f48430000000c9c0009a95b2a4b9c84189db0b14a2ac0002f980021f8002df8b50e4980df5a4db59984b68b1e0001ac238aa388b80005e0c71e699103c8cc03e00031b9a9b5f1560d1800177d550d3a129fcaf54000001b2b6e00038a0640000ba818b988bc0b297ed2b9e107211f2e8125001777b6200008794080028614700011dae904c0000c3b59223a47b6f19c2e70000001213048000538ac2f300006c21000013a1a71039cfafba3f8001ed8d329fcd228237918b8b31ed26331d8a42ed9b895e00016430034900000029f0118000000000000001bf865a14e3b2a6c001f09148003692b1ab39ef00000024c0a10000d68000000003118003249f80000001128000000c7c0019a114203a7190d80100c91016fcf70939b4a1790d02a205000001c01401c01c00800400002c00000407400008401800400000400002c03400c00000000c03000400000804401400002401401400004c0000080000080040b801800001000000001000000002400c02401002000413401000400800c00800004c05003402801400400000c04005000800c00004c0000040640180140b80300000080d800400000c01004000007400400801800c01c00c01800008400009000401800c02000400001002402410000401c00000c03800002403800000407800000409c05000400000401801805c01802803c00800000005004405000403403011800002c03802000000c01007c03002400802000008400000400800800000000c01001006000000401401801802000802801000400403c00009400c00401001c1a800c06000400400c01c03c01001c02c03401800c0000
  | 15 => 0xe80002760c545a5822ab87e2a725da4ce7e36c9d2a7a92d32880213f37f2562430bf37b053d8c8001cb089244afc14e0749259862b604ca4b197ac1294b6499c81bb0f00033797fade32412fa910003068000000302268a2a920f01461738000060001824f3791b57b9022d11100000037516823dae2400028acd8d400000010525201f2b50003950000002d7b8900025299088f8000c1a0a12e0fb24000037fb03b01a771432b928b82d9c206e92cb12ad4800000000000358ae102c8c611baa7b76c820bb5aa02580000013500032b000000000096069acc000000267298924822800378b00a733420c51dd19d89c8dc88435592393a9331fb0250b433a81e9a18915ad0fe1d3b2396b0af21db9293b3850e3327a4a876e27b8e0eba0c3942962fa3911fd0848fa9c096f292b502143849b9b120a3976823b302c3073ae36be8200eb5dc23b94cf389ceb32a49a72938b1f2e7daf4c094436f4cba67b352b781422608352919b00022a829aa74001bae800001eb9da0001b5abf817000192ae30002fe31433612f1df8818930b000023f0e91ae817a3d0001839c102f28b301373800000071400000367af88000000001633758002c499900029aa9921f00018b1bea99978800088af0010371a5e20095726e9d0872935a6d8850001ad9e334d8001031920000f897505a894b47000000205c108000ff9e1a9cb770000001de2a5106a5f0e59d19dd80000000000000017da95314aca1288001558e00fe9d114c8d2b7c1123958001d22723542c280000000016d31d00027d8001879748001f0051b6baf09598003032e015bcff0b4a7438c86f000005a0c8000000db8a22681818001ab80019b40033a000066b9780821528a0be00027b80e80013e321260b829c83949df10c879a2992eaa8932085c64b2007934103527509798936b3052311888ed0182ca9056ff1a007f8ed89182620032ab5a311013b532550af8c343d8c124a21e22721d06cb208264dd23a0b39700d79efa79800000175cfc292ed32d029012a80030e90014d241369b8ba8483d30222e9f10a6800377f529cb9bd14b13384b22034bf0437cac6063a4f35e127a3206634a1bb199a509762028b12df012878a5a93619680004f0c6ab8078000000102251000000235b8109024380000000000000008a8d03108000fb40016f78c33695b9170c33318d88040eaacf284121a09979dc280b25c00035b05a1764000000c9529aa20708ab854a088002451c706886f8c2000233aaf2e5a241b01d6aea20d35c100a1c80926a22100011921c1a41caa483172b004131caa640aa9b0531aaa329ca1e402785b0001728e71f8856af5027cc0386aab0500072ff8000a30002cb77940000003585b963b3f0000348000000000002420dfb6f9b932ba7a2ce96c1bb9a4a2a1c8b66382269af8
  | 16 => 0x91a78000002ce0d90002188000ca2f934615ce30a7f03f25730c00033c8000001cc882d530ccb9a82ab138b60001d500025588c32d80000038da2c1273418bb88a105e7b0219bde0930f8000000001c6a59b35aa915116880002fb7338007c1858002b58000fb8a635e9e580030b849800295920a3caf1b6311197198a9c3a9f8000d61ea0000000b085c2fd37e2040000810000b9e8e15f85cae093c8000a48cfafc9d34450000f4abc00015cb830001cf0fdf3e8da9262dc38f91516e14fb3da76964a3eaf78bc8b92de94510586db2f8aeaeb0e0d0e09208307f22d98e0fd0000000df2cc8000000000002eaa0e820b76b0d086807ad280000026580015c22f00d94e9fb81ab608a816729c0003083073882ba2b94ef9e8a642ed1650882858000ee35da4e00028a80012b0b59a5800378dab10f99a937000000273800000374a048cedb0a80b0c95dc05278141296b982c79bda6498700000011e9540ba307b0a95482c35fb26000198994b673727479db2a18249480b6a87ed71526ba9a82d610185702d282943b399678caaa5a90b8e8629e0004de214911685d3961841ce2c0abb1a381490123815d1918508aca7d0f18542a54ad95eb1e9092208d12e5002aa4069239907b2d0241a901faa6b909c5852a0aa4b8e808d82bc4ba6c2bf00085ea1b9ec1d5b442ef1bc21b2221b79a8b6e90731804db2a0ef1312ee8c9995acb1db8940490678088bb2d68c908580007539c1c99520003640001f400000007795d9ae0a8814c0a22cac933b2e7ad9b2687700027c000242b99392000083c000f6d9426210419fa1e9fa004acd0bd9fa8bbc002a2a250002bbadd9f99f9142ae2800245ae38600000e8b4f1af00000008d061a14b8f0270bd2ad8003708000fbe012692c689a1d0c599709be07a8002060d1c55ad23552aa2231e7a0b00009280000014ab1b0000003312c7369f15813325000000108ad40002fab40b4b8000002899229fe8610d508637ea8c2c8aafb5d06e0a1b178f28000be800187d9809c1b314c0438146bca56ac1a83a280001f327480023717b06a0682a5ccb2c58a00fa2e68440e9a37ab1042319a121f704e02308e1cc38989900d2b20190340a71c900c3736792ae5f6db18eb1eb12837d0b82532dc94f1d4962a48b2f0e3953957a710f522b9daae408a4fca93ae88001b519af1c0a90001afa9bb8ab2700000024c9319a118f8ba4000621308002d1000038800000000009a0309e9499aef8084000006300013da888158002a30000001028000b2370c00239397045800000211de0a5380033489126a80019d263a16217071089965a0580008d40003b93c060a7eb093702349c41203390f8181eda3889d894b8f5d32e59341c382c02c22159693059e62082b404a15182b800333800c9d03b0db00000018ddb726107d1
  | 17 => 0x3510002940000000000000001800001502618001fd8c81f682680000000019e98f1f4a6b0001972ad0c404e9c1800241a4d0328002a4f54800000000058b860c8b4c84625c8b780029d8000000002070151cd0f08998844000001c797aa3e1130ab1d1718a1a8da19002117100022fb16915a1a07d952d1e3654448ad01c84a96d8001ee8000001c53969ee166950b4e2d80ee8808e7b3b9d93843998f990e8aa0e2037af434b3870c873316103c00002eb87af4ccea36000117b6d41204091385633228929a3481ba16a37997c3611875d9af281daf6098aec38b18806d0fa75a97f3430ce31f80f162266940356a77800224b3c37a8000e69d825880016985800009e37434f8ea57a41d082aa636963c0f6b29a650801a2a46146a6b977028071d85343a056daafeb9b2078dc18d03a0972019b839a033938285152a68af5b638d58cd8d49e9b50a871f21e91740e465180b80565a2d50f4e1824e91a0de98c0732c393d1160e2a6e1e520dad91e28bc7426bd2e20003192d0b6a0e089834e6e62a0a0b9f60000a580025fa8f30604d1ac9829bc8003562ae11b0000b715f07b99e2a99fc25eabd8b9b9330d945a13a7025b1f79c310f17e1268f39b6865108071b1623426633e26d213302b4500e06728d1de859158a831d41bf0e108ed8e9e4b9396dc001423259ff04824723335808cf60059c0035381631035ba54947b280fdad880f87cb2e9a0960681a2e00684788382e1f1a6fb49a369379608a98000f32a816e8550909660472eb99f37104690c2f3b1538583e9b22021ec934b233720872b68d800316e50a91c0aaa0e27f87a0002efadb0002acaa9d1ab37130260186a6f00015680017e9c60f22b06980002e750a1048000a798d78d0000000000002118002f10000002868f6076b2e0d7189b6688cab2a0f0c7848ac8141939a542f226c95a10996028e85f81a17b8e269e09580024f852376051000348ac418a345b5c8001833098002580001390000001a22ae8002971340f900004f9ff83a8002b3000003acfddc8969d7b1a8330b88000000ecae194891d01b24685f06b94daabc0019536599330880009baf7361a22a06a880de0f7aa006aaa11f28362d1a57b7b831a1107409501c00034c00012c1a600021981e00010b8000000c2b1300032c24080032cb4d2f683fab980037d82
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x100a332028936009003440f14328c006001c000003400000009c01c00c13187c895083d09d2e0859c0689216021c700760b0400c20c0000141e93e1574d855300607a0d749536154c0144c9361572d855300513a4e545cb6154c0142e9494d72d85530060720d7454b6154c0184c835c952d855300519e5d528876150c0144d96cc972996310060b6117298a658c40103f985d0745963133c17e5d85d92314c40141c9461773586500040fa5e8494d619400181e84dce53586500050ba5253dc961940014649754a21586300041765f85592318c00103f985d074d953000513a5b325c8654c00182d845c8621953013d072567650e414c00105c96617744c53000619a197288465440016449654a21d8d1000591259528846344001a468654a2118d10007811915288463440014969110c7650d1000619a1871dd7624400107496609758c5100071118c625d631440018558718c658c5100061961c621963144001c157518c648c510007095d4621923144001a49526002158c10
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
  | 8 => 0x138b
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138c
  | 16 => 0x138e
  | 17 => 0x9cb
  | 18 => 0x9cd
  | 19 => 0x9ce
  | 20 => 0x5
  | 21 => 0x12cb
  | 22 => 0x12cd
  | 23 => 0x12ce
  | 24 => 0xa4b
  | 25 => 0xa4c
  | 26 => 0x134b
  | 27 => 0x134c
  | 28 => 0xb4b
  | 29 => 0xb4d
  | 30 => 0xb4e
  | 31 => 0x144b
  | 32 => 0x144d
  | 33 => 0x144e
  | 34 => 0xbcb
  | 35 => 0xbcc
  | 36 => 0x14cb
  | 37 => 0x14cc
  | 38 => 0xe8b
  | 39 => 0xe8e
  | 40 => 0xecb
  | 41 => 0xecd
  | 42 => 0x95393
  | 43 => 0x94053
  | 44 => 0x138953
  | 45 => 0xb4953
  | 46 => 0x94b53
  | 47 => 0x1449
  | 48 => 0x144953
  | 49 => 0x95453
  | 50 => 0xbc953
  | 51 => 0x94bd3
  | 52 => 0xbc954
  | 53 => 0x14c9
  | 54 => 0x14c953
  | 55 => 0x954d3
  | 56 => 0x1409
  | 57 => 0x249
  | 58 => 0x94d
  | 59 => 0x2c9
  | 60 => 0x139253
  | 61 => 0xb5393
  | 62 => 0x138b53
  | 63 => 0x145393
  | 64 => 0x139453
  | 65 => 0xbd393
  | 66 => 0x138bd3
  | 67 => 0xbd394
  | 68 => 0x14d393
  | 69 => 0x1394d3
  | 70 => 0xa0e
  | 71 => 0xa0c
  | 72 => 0xb49d3
  | 73 => 0x9cb53
  | 74 => 0xb8e
  | 75 => 0x148e
  | 76 => 0xe89d3
  | 77 => 0x9ce93
  | 78 => 0xe89d6
  | 79 => 0xec9d3
  | 80 => 0x9ced3
  | 81 => 0xec9d5
  | 82 => 0x104c
  | 83 => 0x180c
  | 84 => 0x130c
  | 85 => 0x14c
  | 86 => 0x5c9
  | 87 => 0x198c
  | 88 => 0x17c9
  | 89 => 0x1452d3
  | 90 => 0xbca53
  | 91 => 0xa4bd3
  | 92 => 0xeca53
  | 93 => 0xa4ed3
  | 94 => 0x168e
  | 95 => 0x14d353
  | 96 => 0x1354d3
  | 97 => 0x144b53
  | 98 => 0xb8c
  | 99 => 0x28c
  | 100 => 0x2cc
  | 101 => 0x184c
  | 102 => 0x148c
  | 103 => 0x19cc
  | 104 => 0xe9453
  | 105 => 0x144e93
  | 106 => 0xe9456
  | 107 => 0xed453
  | 108 => 0x144ed3
  | 109 => 0xed455
  | 110 => 0x14cbd3
  | 111 => 0xbd4d3
  | 112 => 0x16ce
  | 113 => 0xed4d3
  | 114 => 0x14ced3
  | 115 => 0x24e
  | 116 => 0x10c
  | 117 => 0x16cd
  | 118 => 0x194c
  | 119 => 0x1a4d
  | 120 => 0x17cd
  | 121 => 0x18ce
  | 122 => 0x1a8c
  | 123 => 0x178e
  | 124 => 0x4953
  | 125 => 0x56d3
  | 126 => 0x1a09
  | 127 => 0xd49
  | 128 => 0x59d3
  | 129 => 0x289
  | 130 => 0x1489
  | 131 => 0x94bd4
  | 132 => 0x20251
  | 133 => 0x28251
  | 134 => 0xd4d
  | 135 => 0x1a0d
  | 136 => 0xd4c
  | 137 => 0x1a0c
  | 138 => 0x202d1
  | 139 => 0xe8a16
  | 140 => 0x14d
  | 141 => 0xe9496
  | 142 => 0x1949
  | 143 => 0x749
  | 144 => 0x9ce96
  | 145 => 0x19cd
  | 146 => 0xb8294
  | 147 => 0xbc294
  | 148 => 0xbc214
  | 149 => 0x144e96
  | 150 => 0x1a57d5
  | 151 => 0x19cbd4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 45
  | 7 => 1109
  | 6 => 2973
  | 5 => 1850
  | 4 => 37
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
  | 8 => packedAt gbK8 (1310+((h/20+packedAt gbK8 (1170+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (46038+((h/455+packedAt gbK7 (41033+(h % 455)*11) 11) % 1805)*12) 12
  | 6 => packedAt gbK6 (156180+((h/1123+packedAt gbK6 (142704+(h % 1123)*12) 12) % 4046)*13) 13
  | 5 => packedAt gbK5 (117166+((h/668+packedAt gbK5 (109150+(h % 668)*12) 12) % 2408)*12) 12
  | 4 => packedAt gbK4 (2668+((h/13+packedAt gbK4 (2590+(h % 13)*6) 6) % 51)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffc07fff807fffe01fffffff4238ff38f1ff
  | 1 => 0x7e0ff8703ff83e0ffe0f83c1fbdd754d74e93
  | 2 => 0xf800fff803fffc00ffff003fe0c1e798e78f1c
  | 3 => 0xfffffc000000ffffffc000fe07e0f80fe0
  | 4 => 0xffffffffffff0000000000fff800fff000
  | 5 => 0xffff0000000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8200000040004200001080400000001001025
  | 1 => 0x4742458321b483426d20d0a85e1cd354534692
  | 2 => 0xd104aad842d96804b65a0133c2c16598a58b18
  | 3 => 0x8208f36de80c2108db9ce78084ee06e0f80dc0
  | 4 => 0x410fc76f36e739e0308420108f7b800fee000
  | 5 => 0xe79e2040807042101c10842210fbfffe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36581
namespace PEqualNP.Outside.L_meta_36581
open PEqualNP.Outside.L_meta_36581.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 2 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_128 : Interval s2Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_160 : Interval s2Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_192 : Interval s2Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_224 : Interval s2Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_256 : Interval s2Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_288 : Interval s2Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_320 : Interval s2Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_352 : Interval s2Atlas 3 352 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 364 := (concat (concat (concat bs2_3_0 (concat bs2_3_32 bs2_3_64)) (concat bs2_3_96 (concat bs2_3_128 bs2_3_160))) (concat (concat bs2_3_192 (concat bs2_3_224 bs2_3_256)) (concat bs2_3_288 (concat bs2_3_320 bs2_3_352))))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_736 : Interval s2Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_800 : Interval s2Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_832 : Interval s2Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_864 : Interval s2Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_896 : Interval s2Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_928 : Interval s2Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_960 : Interval s2Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_992 : Interval s2Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1024 : Interval s2Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1056 : Interval s2Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1088 : Interval s2Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1120 : Interval s2Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1152 : Interval s2Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1184 : Interval s2Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1216 : Interval s2Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1248 : Interval s2Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1280 : Interval s2Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1312 : Interval s2Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1344 : Interval s2Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1376 : Interval s2Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1408 : Interval s2Atlas 4 1408 15 := block_range (n:=15) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1423 := (concat (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 (concat bs2_4_192 bs2_4_224)) (concat bs2_4_256 (concat bs2_4_288 bs2_4_320)))) (concat (concat (concat bs2_4_352 bs2_4_384) (concat bs2_4_416 (concat bs2_4_448 bs2_4_480))) (concat (concat bs2_4_512 (concat bs2_4_544 bs2_4_576)) (concat bs2_4_608 (concat bs2_4_640 bs2_4_672))))) (concat (concat (concat (concat bs2_4_704 bs2_4_736) (concat bs2_4_768 (concat bs2_4_800 bs2_4_832))) (concat (concat bs2_4_864 (concat bs2_4_896 bs2_4_928)) (concat bs2_4_960 (concat bs2_4_992 bs2_4_1024)))) (concat (concat (concat bs2_4_1056 (concat bs2_4_1088 bs2_4_1120)) (concat bs2_4_1152 (concat bs2_4_1184 bs2_4_1216))) (concat (concat bs2_4_1248 (concat bs2_4_1280 bs2_4_1312)) (concat bs2_4_1344 (concat bs2_4_1376 bs2_4_1408))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_704 : Interval s2Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_736 : Interval s2Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_800 : Interval s2Atlas 5 800 30 := block_range (n:=30) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 830 := (concat (concat (concat (concat bs2_5_0 (concat bs2_5_32 bs2_5_64)) (concat bs2_5_96 (concat bs2_5_128 bs2_5_160))) (concat (concat bs2_5_192 (concat bs2_5_224 bs2_5_256)) (concat (concat bs2_5_288 bs2_5_320) (concat bs2_5_352 bs2_5_384)))) (concat (concat (concat bs2_5_416 (concat bs2_5_448 bs2_5_480)) (concat bs2_5_512 (concat bs2_5_544 bs2_5_576))) (concat (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)) (concat (concat bs2_5_704 bs2_5_736) (concat bs2_5_768 bs2_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 20 := block_range (n:=20) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 84 := (concat bs3_3_0 (concat bs3_3_32 bs3_3_64))
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
theorem bs3_4_160 : Interval s3Atlas 4 160 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 186 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 84 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_160 : Interval s4Atlas 4 160 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 186 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_128 : Interval s5Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 129 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 45 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 37 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1824 : Interval gbAtlas 5 1824 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1850 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)))) (concat (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824))))))
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
theorem bgb_6_2944 : Interval gbAtlas 6 2944 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2973 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864))) (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))) (concat (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248))) (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))))) (concat (concat (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))) (concat (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)))) (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))))) (concat (concat (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))) (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)))))))
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
theorem bgb_7_1088 : Interval gbAtlas 7 1088 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1109 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 45 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8eeeaeaaaeaeaeaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36581.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.or,[0,6]⟩,⟨.and,[5,8]⟩,⟨.or,[2,9]⟩,⟨.and,[1,10]⟩,⟨.or,[0,11]⟩,⟨.and,[7,12]⟩,⟨.or,[1,10]⟩,⟨.and,[0,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36581

open PEqualNP.Outside.L_meta_36581 in
theorem PEqualNP.Outside.L_meta_36581 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
