import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36655.Model
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


end PEqualNP.Outside.L_meta_36655.Model

namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
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

def SBf (j : Nat) : Nat := [5, 4, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36655

namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
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
end PEqualNP.Outside.L_meta_36655
namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
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
end PEqualNP.Outside.L_meta_36655
namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
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
end PEqualNP.Outside.L_meta_36655
namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
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
end PEqualNP.Outside.L_meta_36655
namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x15804a006801030916400cd8a00003001208d23381000e3a0142d321d62128788184e5c8852a05493447c580540078048013040800c43c32800000c0640ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x20aa2c5e12003c7c009864884e0a764c84bc0e689432408e3e720caea836c4acc214789052665a18703a220000b0009a10b2c09eb48200000000928a861c005800004a00a22e560008346c003806b62854a01a5c46168074ba6a6e9c0496be627a6050a40000422430b8004400261e0248a67e008c2a08144042219390000c284162c00202001031e4400200148000230183113e51d0e7aa921e7d4d439e28a873e5410eeea2a15d145429f2a6653d54ccaeca3995d547329f2a0653d540cadca5a0db54b419ea9c833e51906dea4a0db14941af298835d531073ca620cf54c41cea98831d531067ca220ed944419f2a6633d54cc73a8798db94b31b6a96633f548c678a918cfd51319e2a2639d434c6dea498db14931bda826378504c67ca818cf550319f2a6433d54c87688390ebd0e21d6a1c436e518875c8310eb106219faa2433c54487688210ebd0c21d6a18436e51087cca210f9d0421d720843ac41087c88210e910421f318843e531086bca7a05754f40b7290816d521027ca9984f55330cea1c613e540c27aa8186750c30b7290616d520c2eca2185d544309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209f2a4213d54842dca5085b54a10f210c213f5444278a88857d4d10ae29a216f52442d8a4887908410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x40123875053cd3014000001802ca09300020325100008c054821c6550d31c650c504c6956310721a358c41886956310421a918543086a66190421a358c41086c56310421e198c41086a56310421e158c41086856310421a919231086a4644c421e150d31086e0604c42199185521031543544308758e54843265408610
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4404847650d3108740a18c098843415ce5408610
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
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (2904+((h/33+packedAt s4K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s4K3 (833+((h/7+packedAt s4K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s4K2 (150+((h/1+packedAt s4K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xfffffff01fc0fffe0f81ffffffc1e03f27fe67
  | 2 => 0xff81ffffe000fffff001ffe0fffe003fc78f87
  | 3 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x530444624488208052925909181229a44c30ab
  | 1 => 0x851888a1c911491605a0aa326a41428921d665
  | 2 => 0xa2d514483aa92aab0513548b4b40532c68b86
  | 3 => 0x2c51a20912301b4d29640610c7299603b00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06311823ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36655
namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730bfaa4617e548c2faa9185f15230bea9c617e528c2faa5185f94630bea8c61de318c3b863185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a61f7514c2eea2985f14530fa28a6174514c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720fd98641f830c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c53882faa5107b90a20f6a1441ef32883d865105f94620fb28c417651882faa3107d54620baa8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc64907b4c920bfa8a417c51483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ee42083da84107bcc820f6190417e51082faa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ec62887d4c510fb90a21f421443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f731043e862085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbdc84997b50932f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331bf29663ee52cc6dca598df54b31f6a96636d52cc7ec8398fd50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418df94431fb20863f5410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf29043ef42087d88410fb8c821f6990437e51087ee8210fd10421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf29681ee52d02dca5a05f54b40f6a96816d52d037c85a06f10b40bf28
  | 2 => 0xa0001ea2049e000001c948c2cd1b800492000c1000338000000004c20006300024c000c89ab4e260c1580000052c640973cc000d503500058c848001e898d3d1ef10657c8700008e6913a0884a61b4000002704b4568e542c8ac1000047000000004000000a21bf0009400000006c908a00000000880000015c818108000008c0000004000005480000000000000000000000e9000490000000000000000000066c449d60000000000004600000151000000001a028477400178476000002260001149190f0a807400000000001178000000009408532e77d47800000000001cb19a000000001dc054ba26c51200000000000000388da22a000000c400027d13a0b09262400000000000001f12f6870a28004fe2d0000ce00012c001f252e0000001c0004ecf400028c5d4000000ee82860875000000001704ba0000000032a4c03f9ed000000000001a2000000700000e49f0a32d69b8f380000000000000000001338000009494a91319824d2718134c4002fa864ca80d2c8000000013010d30023935832328a00cd000000000000000000004800014867c00000000000300022080000000001c47c160bb000a34e0800264000280000000006e8000007cce99160000001d0424f02e01506f0002689a1bc01400000000000794001a80000000017d2ee3fcf00003bc2a000000290178000160000000016d3628fc001a109c41cab06323a580b89190007000013a00100c00c0180a00000001800008000030000100380100000e01000003000000008050060000000300000401000000008050000000080000000000001001006000008050000080000100c0080280300e000068020000040480000000003800002004000000020040000102400c010000000000000f0340180080700a0000100200000c020030000040081102601c000020020000180000a0080000600000000000000008018030020040000d00000003009000008008010000140300000000403006004010008010000000280600a02c0180200200000000006004000020000000100000200800000000000010070000040000301e00c03801002000018000000140080000201000002000008028000000080180100000c0000000000401000000000030070000080000000000000001bf296877d52d0efca3a1fd94743bb28e877d51d0feaa3a1dd54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857
  | 3 => 0x1783e8000000000000003f0000011f02e0fa29ce612900055c000004d206c000000002e4f82190000010a000000000001ca010a50001b04ac5540026d0b453c5e9733fa2753b9c53aa9547c91a3142553801839a3ad1528b000420f58bf4bc000001f800022c0022d0002d4002720d0001398870064c4000000d6000000000001a83a1b736815862800000000000000000013a8000a6418000000008c87aa400fc8d800000000000000003a8000000a60000000000032c3500008c240000ce80000059c828000005e8000000004282b80000000023000218358002640008e80014e4d40000000036c6b4d1a761ae744650002b4890390990ca40c30a8a0001e80001e0008790a9b806e6f8000000004cc6c8000a40011996c15442ce82111d8920fd80d09e3f10d03e0b8000a50250002345080048a3900320e498000a0a932d492d4417e156000d900014461c1394d04c96c1222100010c00000366000000000008e4001ea00054cde9da000000e90001b6000001021583980028c0004e400000000324311c42de46cee17c19e000000b152416400079000000600940000000000049a4d4000001fa00000284000204008c20ba1200912a00038cc2a051a400047800076968ac00026e8c46e00048800059000000001098000009704c0002f2840001b52a451cf117f0000000020c2c29450f9103d8000000001ee0000000024e3a0000000001287d95000083cd38330000005d0760004bc00000000001092851400008e18b38c000ad8732242dd470000005a10b800032000000004027643d800000000000000000bd011af0005d800058000a0c000000000000019e000000000ef47a4f4339e403e000ec1f6000000c7000000000000af060000f08003dc0000000000091c000002781b10d8001ce8108c1901380e00000000076c0021d06205c7c291494000079114be6e8430001c0000928840006340380000000000000000588002292869bc451d7000708000c3458000e18130000013300035868800268000024af0000209ec529640cc0014b0fe352000488693ea385048002a80d0000d03725c8002250000500027e4a8248c900000000000287000a089f800376014ac8444307d000000000000208001d4000000000f87e469800000000000000000000000026c000581844c4068e3800000000fb8f30000000000000003000000000478658000000004f0e230c0a0000d50000000000000026c00000326450911e30a2134a61c80007fc63969000000000290003b4001ae100000c400000000000234104661480004fa3609080025c8a00022e2583c800149000000002350005b84b28139c9e4958f60000012187816c1013e1014782f90698f0003c00006433200026000000000000000000008b8002b8000e78000dc000002410003c4058002c
  | 4 => 0x4100000003c02216cae80034a000fe0000000002aa5700096111166000378fd02d0007a40018c44637cff00000081c00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d5546310c25f654c030b5185300c27b654c030ba189300c23e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c832d548cb20cb55132c82e8604cb20ba58830c827661d52209d587548832d62952209d984548827561152208f993538823d64d4e209d987538827561d4e208f990538823d6414e209d98453882756114e20cb95242882e46150a20ab59032883365494620cd55251883365454620cd551518832e5488620ab590218832e5408620d954421882ad64c82209b58a544825f63551209718d544827761551209d185544823f6454d208f191534826f6254d209dd8553482746154d209ed81534823e6414d208f590534826e658c9209b19532482e8604c9208f990514823d64145209798c540825d63150209d984540827561150208fd91530823c6454c209dd8553082746154c208f990530823d6414c209b98853082766114c209d584530823e64948208f592520826d6590820b9185420826d65cc8209b59432082ad640c8208fd91510823c6454420ab59021082e960084208f992500823d64940209e59430082ad64c80209bd95200827b65480209b98854c426d62153108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f109b98a53c426d6294f108fd9152c423c6454b108f99052c423d6414b10b918941c42b5648c710ad59021c426e62d52109b58b548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b18953442776154d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d4910d9587524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c52443345490510d514e41442746550510d514d41442e462505109d99631442b5648c510d514e3144274654c510d514d314427665c8510cd153214435453c8510ad59021443345408510d514c21443675208510d514e104423d65950108f990540427661150108f993530423d64d4c108f990530423d6414c109b988530426d6214c109d984530423e64d48108f593520427661d48108f990520423d64148109798c520425d63148109d597310433554cc4109d5943104335540c410cd553100427965840109dd9510043355444010b518d100427b6544010
  | 1 => 0x63f6550441ab18941106776550441b9189411066e62d53319b58b54cc73561953319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b31d9d8552cc7365490731b918941cc73554cc6319d586544c66f62551319b189544c67b60551319e181544c63e64149318f590524c63e64141318f590504c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c63e64944318f592510c6756590431b9189410c6b5648c43197d95310c677654c4318fd91500c63c64540319bd89500c66c62540319798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21ad99331c863e64943218f59250c867a60152219e580548863e64d4e218f593538867a60d4e219e583538863e6494e218f59253886ac644ca21ba181328863f64542218f191508863e64951219bd89544867761551218f994544863e6494d218f592534866d6294d218fd91534863c6454d219dd85534867b6054d219e181534873454c8521cb152214863d6595021cb189540873461550218f990540863e64d4c218f593530863e6414c218f590530867a6014c219e580530872d54d08219b594420866d658c821cb55232086ac644c821cb55132086e7614c821ba181320873554d0421e9d0b41086756510421e910841086b664cc421cd55331086e562cc4219d5943108735540c421d554c310866f6548421ab19121086776548421ad19121086b561d0f409dd8552d02746154b40cbd0d52d032d4354b40d9d8552d03646154b40cb54a42d032d5210b40cb54b41d02ac6250740cb54941d02776154e409d18553902ad6210e40ad18542902ad62d02409b988535026d6214d408f99743502b561d0d408f994425023e65d0540ab189415023d6590c40ab588431023f6550840ad185421026f62544409b18951103364354440cd10d51103676254440d918951103374254440cd509511023d6590440cd54641103355110440ab58b401033551d00408fd95401033551500409ed95401027661953309d58654cc26e62153309b58854cc23f6454b308f19152cc2776154b309d18552cc23e64947308f59251cc26e62952309b58a548c27661152309d584548c23e6494a308f592528c23f64546308f191518c26f62546309b189518c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c32f54d4930cb153524c32f5414930cb150524c33754d4530cd153514c36752d4530d914b514c3375414530cd150514c3675214530d9148514c36852cc130d5146304c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c3686054830cd95
  | 2 => 0xa07c1c41480b10a3f82382e156744d4063108000261dc000000c18dc0000381aa08000084ec0b40005840f9c100000000175000620f3800000001078000007ec7480035a22ca51ec13430c0b85141435503a1009a2ccd212107e6a4a289b0fa15c200c2000368002142304d8690a33c4218da00c0e40a04c0d717a1a8de0f4234864e60442a81dc6a2053d0824708ae0001d0a88f91d86449780913278c0004e0000000f02d2462fc0005535c2e8021632b4194089e0210114000cd1043e8969bd22a3c4e80310000000001426e124f68662486dd0620101423800167000098b519029e1b4000000007387f8002f44e4278f60be000fb1d52b2088b41ca0742281183b42219102106226298000410005ec001fa2041e8e587912c8082e0000b60180000c01000000001005c05024b1200010000d0100600000008030680500003004170080103c1d000120042601403000000846f00c5b000070640201404004000001300401024340200403002014000140e0680d01c270040002c01078060000501c1302000024000140000c190c40001c0f000021780300406028010682a01c000400c0000c01c0302c0001c130040c038010100b018000040308000028002b81303c0c0040203c04010010041204001070140040102403060080540100405000020101f00c050000700400060030ac0600805004000502c4180d014060de6f62547439b18951d0f676254743d918951d0eb561d0e439bd895090e6c62542439d9845050e756114143ad5874310e3f6550c4397d954310e7761548439d1855210f2f4354843cb50d5210f676154843d91855210eb561d0f429dd855390a746154e42ab5884390a7661942429d5865090a3e65d0d42ad5874350b374314542cd50c5150b674214542cd9085150a3d6590c42ab5884310a3f6550842ad1854210a6f6550842b91854210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7661152329d584548cae46150a328fd91518ca3c64546328f992508ca3d64942329d986508ca7561942328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132cb588544cb2c54909329b195424cae46150932cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132da908504cb694214132dacc8504ca3d65950328f990540ca6e6215032cb552320ca5f654c8329bd95320cb2d544c832ba181320caad6210f41ad18542d066e6294e419b58a53906b561d0e419bd89509066c62542418f99443506ad6210d41cb90c525072c43149418f997425072c52d0941cb14942506b46150941d914b415072c5290541ad587431063f6550c418f596421
  | 3 => 0x13b1b00680000002a004000ed0007a82b0000005c0001eb1d0174e79cd2a021c95800000478000000dc1ec6500037e00000000278000529c6000000448a4000410a90832b84402193324c2880e03d0360002402c280590000330003c00017913e1b0561a5290108000810942a8c917c3621401a000000000000003e8000000000fe7e40c0c120236c48a1830077cd58000000007a80000024cfa80032a04c00000334000a700023a000000002ca664af10534c000380003a8774848000002c8029fd0004a06c8c927a3a8679421420009f0d62064d10a84b12a4001e0753024c4c99c33a4660710001526b0081841ca61c7e16015e5b0cd9d32ee000a982f3445b5058320106e4f7800364650000003846c0100df17c638a6a0040c458b99a00c00dd0710d2323dc6895b2fe0a8890eb240018ce1972de5b8e49f24246bcc50003b67f8d393a1e43cc1c9ee02c868698dd2d22741818536c558f81413ae220dd0541a06ed099e91c63809a98b16c1784b9290a43f473862000090338800004700e97d04a8345889e2926585393f3ca000ed1c03e6000398bc118034000941201f00c8b70de4940006b2ae320658e421c57cbf0ee1f03ec1b0c519c43ca38692aa510fc0592e2444ec8002585180016b0047c4631c83bc2b4500a82c4000299e424e1843c0bb1706d48b94c42e300e285831a01ccf88d0fc574d51d62441d8c79743cc80cd08b938e4c8860122605c88d868228000b317620e560bc1e104e31c9c1b808c42c6600f1243bc019890006f8580383f87dcd18003182d40012a296378c10e63fe50cd999e42c23c1591f33a310c31c41384b88505
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xf00330040245558000024061300028048500401700b18704001400034e20000018000007495c74354843948e2b10862152471588544cab038a84282658a550604c832948e4b0e8620d247258654cc712310c2aa0430b1d9544c821c52a83026410c37765533108692b8e86a9681491c55210b40a4ae421aa220524725444110312b12a3a00818a550604cb20a48e2b14a91042d769502188292392c22a2219114c6250510c2ac829c628843576150214430ab20a610a21855506344010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4182000824865c74354843824865c74354b40824865c843544408248758951d0040
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffe07ffffff81ff81fffff83ffffcc7f1ff
  | 1 => 0x7c0fff80fe0fffe0ffe0fc0ffc3c07f798e67
  | 2 => 0x7fffffff000fffff0000ffffffc007f81ff87
  | 3 => 0xf800ffffffff03fffffff000ffffff83fe0ff8
  | 4 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x3042223122482080529092c91806532442b0ab
  | 1 => 0x50966450e489499605b285586a428569598665
  | 2 => 0xa50cc8a241d2932ab06109b2b6a80a53815b86
  | 3 => 0xc428910489101a4d29452020c5312c02ac0d50
  | 4 => 0x630e1c70e1ce3f1ce79ce3c06223063f7e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80eea0ea80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36655
namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c180027fd5007fe54027f55007fc54027fd4c097f53017f94c09fd53005f54c05fc5301ffd0c05fe43007f50c05fc43027fd4803fe52027f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32007f4c803fc32027fd4409fe51027f54409fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21027fd4009fe50027f54009fc5001ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42005ff08210007fe2108003f71084001fd884200fffd951007dfeca880037f65440013fb2a200fff99510025fcca8803ffd654401f7eb2a200fff19510025f8ca8803f7c65440093e32a2000ffd9110005fec888003bf64440015fb22200eff9911001dfcc888003fd64440017eb22200eff1911001df8c888003bc64440075e322200fffd5110077fca88803ffd544401dfe2a22000ffd8d10005fec688003df63440016fb1a200dff98d10015fcc688003fd63440017eb1a200dff18d10015f8c688003dc63440056e31a200fffd4d1007efea688037fe534401ffea9a2000df54d1006ff8a68803bff434401bff21a2000ff50d1006ff88688003ff62440017fb122000fbd8910005dec488033fe62440037f3122000ff58910005fac488033fc62440037e3122000fb1891000dd8c48803fff5244019ff292200fff54910067f8a48803bff4244019ff2122000ff50910067f88488037ff3244019ff1922000ff4c910067f8648803fff514401fff28a200fff5451007ff8a28803bff4144001ff20a2000fd90510007fa8288003f5414401dfe20a200dffcc510007fc6288003f63144001fe98a2000fd4c51006ff86288033ff2144001ff10a2000ff48510067f8428803fff504401fff282200fff5411007ff8a08803bff4044001ff2022000ff50110077f88088037ff3044001ff1822000ff4c11006ff86088033ff2044001ff1022000ff48110067f84088003ff1044001fd8822000ff84110007ec2088017ff65040137fb282009ff99410025fcca08027fd65040137eb282005ff19410025f8ca08017ff64040017fb202008ff9901001dfcc808003be64040075f3202000ff59010005fac808003bd64040015eb202005ff1901001df8c808027ff5404011ff2a02009ff55010047f8a808017ff63040017fb182007ff98c10015fcc608003fd63040017eb182005ff18c10015f8c608027ff5304013bfa982007ff94c1004ffaa6080037d530400ffe2982008ffd0c1003ffc8608003fd430400ffe2182005ffd8810005fec40801bfe62040037f3102000ff58810005fac408017fc62040037e3102009ffd4810037fca408027fd520400dfe2902008ffd0810037fc8408003fd420400dfe2102007ffcc810037fc6408003fd320400dfe190200bbf9841004ffea208027fe5104013fea882009ff14410047fe8208003fe4104001fea082008ff1041003ffe6208003fe3104001fe9882007ff0c410037fe4208003fe2104001fe9082006ff08410055fcc008027ff500400bff2802009ff5401002ff8a008023ff400400bff2002000ff5001002ff8800801fff300400bff1802000ff4c01002ff8600801bff200400bff1002000ff4801002ff84008003ff1004001fb8802005ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x2fc6148031ffa8a4018ff945200c7faa290063fc514802fffa0a4000ff90520007fa829005ffc414802dff98a4000ff8c520007fa629005bfc3148003ff90a4001ff8852000ffa4290007fc21480037fb024018ffd41200c7fca090063fd5048031fe2824017ffd0120007fc8090003fd404802ffe2024016ffcc120007fc6090003fd304802dfe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048017ffb2e200bbfd971005ffccb88012fe65c4017feb2e200bbf5971005ff8cb88012fc65c4001ffb262000bfd93100affcc98800efe64c4001feb262000bf593100aff8c98800efc64c4017ffaa62015ff9531005ffaa988057fc54c4001ffb1e2000bfd8f100a7fcc78800afe63c4001feb1e2000bf58f100a7f8c78800afc63c4017ffa9e200bdfd4f100a7fca78802ffd53c4001bea9e2014ff14f100affe8788053fe43c4001fea1e2014ff10f10007fec588002ff62c4027ff3162001bf98b10007fac588002fd62c4027fe3162001bf18b1005ffea58804ffe52c4017fea962013ff14b100affe858804ffe42c4001fea162013ff10b100a7fe658804ffe32c4001fe9962013ff0cb1005ffea38802ffe51c4017fea8e200bff147100affe8388003fe41c4001fb20e2000ff50710007ea8388057fc41c4029ff98e2000ff8c710007ec6388003fd31c4001fa98e2014ff0c71009ffe4388003fe21c4001fe90e2013ff0871005ffea18802ffe50c4017fea86200bff143100affe8188003fe40c4001fea062015ff103100a7fe6188003fe30c4001fe9862014ff0c31009ffe4188003fe20c4001fe9062013ff0831002ffecb0802aff6584015ff32c2004bf99610057facb0802afd658400bfe32c2004bf1961002ffec908002ff6484025ff3242003bf99210007fac908002fd648400bfe3242003bf19210057fea90804bfe5484015feaa42012ff1521002ffec708002ff6384023ff31c2002bf98e10007fac708002fd638400bfe31c2002bf18e10057fea70802b7f5384023ff29c200aff54e10006faa708047fc5384025ffa1c2011ff90e10007fa8708047fc438400bffb142000bfd8a10087fcc508006fe6284001feb142000bf58a1002ff8c508006fc6284015ffa942010ff94a10057faa508043fc5284025ffa142010ff90a10007fa8508043fc4284023ff9942010ff8ca10007fa6508043fc328401f7eb0c200affd4610057fca30802bfd5184015fe28c2012ffd0610007fc8308003fd4184025fe20c2011ffcc610007fc6308003fd3184023fe18c2010ffc8610007fc4308003fd2184021fe10c2009bf98210057fea108017fe5084015fea842005ff14210097fe8108017fe4084001fea042005ff1021008ffe6108017fe3084001fe9842005ff0c210087fe4108017fe2084001fe9
  | 2 => 0x30017f8a69800bff434c005ff21a6002ff50d30017f88698003ff624c0017fb12601cff9893000dfcc498003fd624c039fe3126001bf189300f7fea498073fe524c03dfea92601cff149300effe8498073fe424c001fea12601cff10930017fe649800bfe324c005fe9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c03dffa8a601eff945300f7faa29807bfc514c03bffa0a6000ff90530007fa8298077fc414c005ff98a6002ff8c530017fa629800bfc314c039ff90a6000ff88530007fa4298073fc214c0057fb02601effd41300f7fca09807bfd504c03dfe282601dffd0130007fc8098003fd404c03bfe2026002ffcc130017f6609800bfe304c001ef1826002ff0c130017b8609800bf8304c039ff902601cff0813002ffecb1006eff6588037ff32c4004bf996200dffacb1006efd658800bfe32c4004bf1962002ffec910002ff6488035ff3244003bf99220007fac910002fd648800bfe3244003bf192200dffea91006bfe5488037feaa4401aff1522002ffec710002ff6388033ff31c4002bf98e20007fac710002fd638800bfe31c4002bf18e200dffea71006f7f5388033ff29c401bff54e20006faa710067fc5388035ffa1c4019ff90e20007fa8710067fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944005ffd8620007fcc310002fe6188001feb0c4000bf5862002ff8c31006fff5188037ff28c401bff546200dff8a31006bff4188001ff20c4000ff506200d7f88310067ff3188001ff18c4000ff4c6200cff86310007ff2188003ff10c4000fb8862000ffa4310007fc2188003f610c4001bf982200dffea110017fe5088037fea844005ff142200d7fe8110017fe4088001fea044005ff102200cffe6110017fe3088001fe9844005ff0c22000ffe4110007ef2088003fd9044005ff0822000ff04110063ff65480317fb2a4000dfd9520004feca90063fe65480097f32a4018ff595200c5faca90063fc65480097e32a4018df19520024f8ca90003ff64480017fb224017ff9912001dfcc890003fd64480017eb224017ff1912001df8c890063ff544802fff2a24018ff551200bff8a890003ff63480017fb1a4016ff98d20015fcc690003fd63480017eb1a4016ff18d20015f8c690063ff5348031bfa9a4016ff94d200c7faa6900037d534802dfe29a4017ffd0d200b7fc8690003fd434802dfe21a4001bfd892000ffea490007fe5248003f72924001ff549200c7daa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000fdc6490007fd3248001f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c29000
  | 3 => 0xea848005ff1424001ffe812000fbf4090007fda048005ff1024001ff0812009bff309000bfe1848025ffc824002ff84120093ff65500497fb2a8024ff99540025fccaa0093fd65500497eb2a8024ff19540025f8caa000eff6450007ffaa28003ff9514001ffaa8a000ffc5450001ffb1a8000bfd8d4011ffcc6a000afe6350001feb1a8023ff18d40015f8c6a0093ff5350049bfa9a8023ff94d40127faa6a00037d5350047fe29a8003ffd0d4001f7e86a000ffe4350007fea1a8000ef50d4001ff886a0003ff62500017fb128022ff9894000dfcc4a0003fd6250045fe3128001bf18940127fea4a008bfe5250049fea928022ff1494001ffe84a000ffe4250007fea128003ff1094011ffe64a008bfe3250001fe9928022ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150049ffa8a8024ff94540127faa2a0093fc5150007ffa0a8003efd054001ffc82a000ffd4150001dea0a8003ff1054011ffe62a0003fe3150001fe98a8023ff0c540117fe42a0003fe2150001fe90a8022ff0854001dfec0a0093ff5050049ff2828024ff54140127f8a0a000fff4050007fda028003ff901400077c80a000ffc4050007de2028003fe1014011ffe60a008ffc3050045ff9028022ff0814002ffecb18086ff658c043ff32c6004bf9963010ffacb18086fd658c00bfe32c6004bf1963002ffec918002ff648c041ff3246003bf99230007fac918002fd648c00bfe3246003bf1923010ffea918083fe548c043feaa46020ff15230015fac71800bff538c005bfa9c6002ff94e30017faa71800b7d538c005fe29c6002ffd0e30017fc871800bfd438c005fe21c6005ffd8a300fffcc518006fe628c001feb146000bf58a3002ff8c518006fc628c043ffa94601fff94a3010ffaa51807ffc528c041ffa14601fff90a30007fa851807ffc428c005ff9946002ff8ca30017fa651800bfc328c00bffb0c6000ff98630005fcc318003fd618c0017eb0c6005ff1863010ffea318087fe518c043fea8c6021ff14630107fe8318003fe418c001fea0c6020ff10630017fe631800bfe318c001ef18c6002ff4c630017f8631800bdc318c03fff90c6000ff88630007fa431807ffc218c0057f3046021ffd423002ffca118087fd508c00bfe2846020ffd023002ffc8118003fd408c00bfe2046002ffcc230017be611800bfb308c00bfe1846002fe0c2300fffe4118017fc208c03dffb2a601ebfd95300f7fcca98012fe654c03dfeb2a601ebf595300f7f8ca98012fc654c001ffb226000bfd91300077ec898002bf644c03bff3226003bf99130007fac898002fd644c03bfe3226003bf1913000778c89800ebc644c03dffaa2601dff951300f7faa898077fc544c0057fb1a6002ffd4d30016fea69800bfe534c005fea9a6002df54d
  | 4 => 0x806fd6288403ffa944201ff94a2100fdca510807fd528845bf6a944201ff14a2100ffe85108b3ef4288403ff2144201ff50a2100ff88510807ec4288403ff9944201ff8ca2100fdc6510807fd3288401f69944201ff0ca2100dfcc3108b7ff518845bff28c422dff5462116ff8a3108b3ff4188401ff20c4200ff50621167f883108afff3188401ff18c4200ff4c62115ff86310807ff2188403f790c4201fdc862100ff84310807f42188401ffb044200ff98221005fcc110803fd60884017eb044200ff1822116ffea1108b7fe508845bfea84422dff14221167fe81108b3fc4088457ff984422bff0c22100ffe4110807fc2088403f6104422affd9521155feca908abfe65484097f32a422aff59521155faca908abfc65484097e32a4200ffd9121005fec8908a7fe64484077f3224200ff59121005fac8908a7fc64484077e322422affd512114ffca8908abfd5448453fe2a24200ffd8d21005fec6908a3fe63484057f31a4200ff58d21005fac6908a3fc63484057e31a422affd4d21156fea6908a3fe5348455fea9a4200df54d21147f8a6908a7ff4348451ff21a4200ff50d21147f88690806ff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201ff9092100ffa8490807fc4248403ff9924201ff8c92100ffa6490807fc32484037fb0a422affd4521157fca2908abfd5148455fe28a4229ffd0521007fc8290803fd4148453fe20a4228ffcc521007fc6290803fd3148451fe18a4201ffc852100fee4290807fe2148401f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024200bf18121157fea0908abfe5048455fea82422aff1412114ffe80908a7fc4048451ff9824228ff0c12100ffe4090807fc204840bffb2c8027bfd964013ffccb20012fe659004ffeb2c8027bf5964002ff8cb20012fc65900077eb248003ffd524001ffca92000ffd5490007fe2a48005ffd8e40137fcc72000afe6390001feb1c8000bf58e4002ff8c72000afc639004fffa9c8027dfd4e40137fca72009ffd5390001bea9c8026ff14e4001ffe872000ffe439004ddf21c8003ff50e4001ff8872000fbc439000bffb148025ff98a4000dfcc520003fd62900017eb148005ff18a4000df8c52009fff529004bff2948027ff54a4012ff8a52000fff4290007dfa148003ff90a4001ffa8520003bd4290007fe2148026ffcca4012ffc6520003fd329004bfe1948005ffd8640007fcc320002fe6190001feb0c8000bf5864002ff8c32009fff519004fff28c8027ff5464013ff8a32000fff4190007ff20c8000ef9064001ffa832000ffc4190007de20c8026ffcc640007fc6320003fd319004dfe18c8025ffc8640007fc4320003fd219004bfe10c8003bf9824013ffea120017fe509004ff
  | 5 => 0x8141005f8c0a08dbff505046dff2828236ff541411b7f8a0a080fff4050407dfa028203ff101411affe60a08d7fc3050469ff9028234ff0814119ffecb188ceff658c467ff32c6204bf9963119ffacb188cefd658c467fe32c6204bf19631007fec918802ff648c465ff3246203bf992310077cc91880ebe648c401feb246200bf592310077ac918802bd648c465fe3246203bf1923119ffea9188cbfe548c467feaa46232ff15231015fac71880bff538c405bfa9c6202ff94e31017faa71880b7d538c405fe29c6202ffd0e31017fc871880bfd438c405fe21c6200ffd8a3118ffcc518806fe628c401feb146200bf58a3118ff8c518806fc628c467ffa946231ff94a3119ffaa5188c7fc528c465ffa146231ff90a31007fa85188c7fc428c405ff9946202ff8ca31017fa651880bfc328c4057f30c6233ffd463119ffca3188cffd518c467fe28c6232ffd0631007fc8318803fd418c465fe20c6202ffcc631017be631880bf7318c405fe18c6202fd0c63118ffe43188c7fc218c401ffb046200ff98231005fcc118803fd608c4017eb046200ff1823119ffea1188cffe508c467fea846233ff14231197fe81188cbfc408c405ff9846202ff0c231017b861188c7ff208c463fe1046230ffd9531185feca988c3fe654c4097f32a6230ff59531185faca988c3fc654c4097e32a6200ffd9131005fec8988bffe644c4077f3226200ff59131005fac8988bffc644c4077e3226230ffd513117ffca8988c3fd544c45ffe2a26202bfd8d31017fea69880b7f534c405ff29a6202ff54d31016faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c401ffb126200bfd8931177fcc498806fe624c401feb12622eff1893100df8c4988c3ff524c45dff2926230ff54931177f8a4988bfff424c45dff2126200ff50931177f8849880bff324c405ff1926202ff4c931017f8649880aff614c461ffa8a6230ff94531187faa2988c3fc514c45fffa0a6200ff90531007fa82988bffc414c405ff98a6202fdcc531017fc6298803de314c405fe18a6202f70c531017e862988bbff214c45dfe10a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c0988c3ff504c461ff2826230ff54131187f8a0988bfff404c45ffe2026202ffcc131017f860988bbff204c45dfe102622dffd962116dfecb108b7fe65884097f32c422dff5962116dfacb108b7fc65884097e32c4200ffd9221005fec9108b3fe64884077f3244200ff59221005fac9108b3fc64884077e324422dffd5221167fca9108b7fd5488459fe2a44200ffd8e21005fec7108affe63884057f31c4200ff58e21005fac7108affc63884057e31c422dffd4e2116efea7108affe538845bfea9c4200df54e2115ff8a7108b3ff4388457ff21c4200ff50e2115ff88710
  | 6 => 0x5bea9a6402ff14d32017fe869900bfe434c805fea1a6402ff10d3200dfec499007ff524c803ff2926401ff5493200ff8a499007ff424c803ff2126401fb9093200ffa8499003ed424c803fe2126401ffcc932017de6499007fe324c803ef1926401ff0c93200fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf185321dffea2990effe514c877fea8a643bff145321d7fe82990ebfc414c805ff98a6402ff0c53200ffe4299007fc214c803f610a6400ffd8132005fec099003fe604c801feb026400ff18132005f8c0990efff504c877ff282643bff541321dff8a0990ebff404c875fe2026402ffcc132017f86099007ff204c803f79026401ff081321cffecb208e6ff6590473ff32c8204bf996411cffacb208e6fd6590473fe32c8204bf1964101dfac92080fff5490407ff2a48203ff5524101ff8a920803ff6390471ff31c8202bf98e41007fac720802fd6390471fe31c8202bf18e411cffea7208e77f5390471ff29c8239ff54e41006faa7208e3fc5390407ffa1c8203efd0e4101ffc872080ffd4390401dea1c8203ff10e41007fec5208dffe62904037f3148200ff58a41005fac5208dffc62904037e3148239ffd4a411bffca5208e7fd529046ffe2948203ffd0a4101ffc852080ffd4290407fe2148238ffcca411bffc6520803fd329046ffe1948203bf986411cffea3208e7fe5190473fea8c8239ff1464101ffe832080fbf4190407fba0c8203ff1064101fe883208e3ff3190471fe18c8237ffc86411bff84320803ff6090401ff3048200bf98241007fac120802fd6090401fe3048239ffd42411cffca1208e7fd5090473fe2848203ffd024101ff8812080fbc4090471ff9848238ff0c2411bffe41208dffc209046dffb2a8236bfd9541006fecaa08027f655046dff32a8204bf995411b7facaa08dafd655046dfe32a8204bf195411b6f8caa08127c65504077fb228203ffd514101ffca8a080ffd5450407fe2a28200ffd8d41005fec6a08d7fe63504057f31a8200ff58d411aff8c6a080afc635046dffa9a8236dfd4d411affca6a08dbfd5350401bea9a8235ff14d4101ffe86a080ffe435046bdf21a8203ff50d4101ff886a080fbc4350401ffb128200bfd8941007dec4a0802ef6250469ff3128201bf98941007fac4a08d3fc62504037e3128200fb1894100dd8c4a08dbff5250469ff2928236ff549411a7f8a4a080fff4250407dfa128203ff9094101ffa84a0803bd4250407fe2128235ffcc9411a7fc64a0803fd3250469fe1928203bfd85411b7fea2a08dbfe515046dfea8a8236ff1454101ffe82a080ff74150407ff20a8200ef9054101ff882a080fbc4150407fa20a8235ffcc5411aff862a08d3ff2150469fe10a8200ffd8141005fec0a0803fe6050401feb028200ff1
  | 7 => 0xa980a7f6354c09afb1aa602dfd0d53016fc86a980b7c4354c01bfb12a640df98953006fac4a99037c6254c83bfa12a640df90953206f884a980b7f3254c05bf192a602df0c953006fec2a98037e6154c01beb0aa600df1855320efe82a99077c4154c05bf98aa602df0c553206fe42a99037c2154c01bfb02a600df98153006fac0a98037c6054c83bfa02a641df10153016fe60a980b7c3054c81bf902a640df081531fffecaa18feff6550c7fff32a8604bf995431fffacaa18fefd6550c7ffe32a8604bf19543015fec8a180fff5450c07ff2a28603ff5514301ff8a8a180aff6350c05ffa9a8602dfd4d43017fca6a180bfd5350c05bea9a8602ff14d43017fe86a180fdf4350c05ff21a8602ef90d43017f886a180bbc4350c05ee21a8600ffd8943005fec4a18fbfe6250c037f3128600ff589431f7f8c4a1806fc6250c7fffa92863eff949431fffaa4a18fbfc5250c07ffa128603efd094301ffc84a180ffc4250c05ff9928602ff8c943017f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a863fffd45431fffca2a18fffd5150c7ffe28a8603ffd054301ff882a180fbc4150c05ff98a8602ff0c5431f7fe42a18fbfc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028600bf181431fffea0a18fffe5050c7ffea82863fff1414301ffe80a180fbf4050c07fe2028602ffcc143017f860a18fbff2050c7dfe102863dffd95421edfecaa10f7fe65508097f32a843dff595421edfacaa10f7fc65508097e32a8401bfd914201ffea8a100ffe5450807feaa28403ff15142007fec6a1002ff6350879ff31a8402bf98d42007fac6a10f3fc63508057e31a843dffd4d421eefea6a10f3fe535087bfea9a8400df54d421e7f8a6a100fff4350807dfa1a8403ff90d4201ffa86a1003bd4350807fe21a8401bfd894200ffea4a1007fe5250803fea928401ff1494200ffe84a100fef4250803ff2128401ef9094200ff884a1007bc4250803f62128401ffcc94200ffc64a1007ee3250803fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542005f8c2a10f7ff515087bff28a843dff545421eff8a2a100fff4150807dfa0a8403ff105421e7fe62a10f3fc3150803ff90a8401ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc605087bffa82843dff941421effaa0a10f7fc5050807ffa028403ff1014201f7880a10f3ff3050879fe1828401ffc814200ff840a10efff654c8777fb2a643bff99532025fcca990effd654c8777eb2a643bff19532025f8ca99003ff644c8017fb22643aff9913201dfcc899003fd644c8017eb22643aff1913201df8c8990efff544c875ff2a2643bff551321d7f8a899006ff634c805ffa9a6402dfd4d32017fca69900bfd534c80
  | 8 => 0xd48000546000142a3e2a62e4a26db22d03126f005655c8424f20a6d9006698200078e000a92000c623d200088689ecfa000d14000d1a1a800074a29824e188dd075c34a0ec9fa2465b25385f8a80968a0227233603e03021e4226544de0d09564c600085ab9438887aca20007b6000c9884a00000001a00300000000501e00800000400500101300102600400300103b00d00b00200100700500101600700700d00100200a00000901600100300000700100000d00100d00100000000300900500201700800300e00a00600d00400000100700602000000700800600d00200900500400100d00100001901c00200000100000a00a01000000700500000400200200400700001900000d00003000700101501200100900600e00500500700300900003200302c00001b00701b00400400502b00200300e01200100b00002301300001000500300500002100200100201300700200b00300001e00f00100800200400000201400000000300000300200300300002700100000b00301900101b00500000300800c00001d00a01e01700600100f00500101d00400200100200800c00001b00500700400300002502300000900200a01700800000100300000000400100400600300000200001c01100100500001300600100000500000a04a04900802000401000000802400000000200100e00300001701800f00b00100000000100200500100600100000600200701600100500501501d00401900100000400401d00f00600000a00401a00002600900100100000901900000900200300100800a01c00b01502900000000000200600500000101500800700801001106400200400e01c00000101f00100000001501000401200000000000200101500500000000400400200101700100e00b00000900000400900b00000802c00001200000400901100000300c00700200200000200000300101100301200000a00400200700000200500101900400701600400000601a01400201b00700000100000001000500000000000000000100101800200900400202500902d00300001e00000000000000001f00000100600101b00200300800700b00000000e00a00a00600500100000e00600000002200600f00c00600100400000c00c00600100300500001000900100c01802400600500700200200001400000b00000800200500400b01200000000300c00000100300a02900400900800100103200000b00500200c00000000300403700200000100800001f00100c00400501400400200401a00000000700200000100000300b00000300400100700100300000600300000300500601800000400a00d01000101900a01b00400d00000000400500600000500700802700d02601a00800500100000100d006fec8a99077e6454c01beb22a641df19153016fec6
  | 9 => 0x4606e000000cf60004e24304b69eea4e000000b2e768b70a841b61d0000a58000c78c200167c4c40c1283262e5e055e9060000000008805cebda0000704c20002000d6d9e210dbc054000b128820009582acafad02a0c3beba6dc0ad4458658c144a8952dd86a80008a43743a04d2d68b562dc0001e80d2b461da3fc48c83e33aa2e000146c6c90a7e2bd00824383840009180002a41540000be816b62b9c508cd80005ecb260004661c8860af8b2c856cf86a66d601ca00000d266084ec8f23aa990cb20007f0784000000bbc012aeeace4c400047404c000b0e02842009200012e7327cc468cdac2eb981721b4304c0226200003277e39a3861b07b27fece2c3830ea687560c08029625202049a07f21f24261302e0340258634acccba37aa422c22f62aabf89de33449c3761a4aec3061ca37034c000c5c3c04e67ba57209400091cb4abe0ababba0005be000356000000946736a66bc2072136238c0c302c42416752000490000b38d6ea0a000c960004f46decac18c00065671e00000000000000050ec3c24215879e088a547385f619045682a54e0009485ea3ea1ec000000288ab8c76540000dd64502bc3da85242a9a2528ce6c7080cd6c9d65ac6507e09aa0749540006b6b663ee4602ccc58aac0004147da1a683c5780868e47bea7a404ceeda263e0000ae5844ee3b018699200020a01896600061075a79c0002a29b653600043e00002ec6858e000290aea00052a00024ca207ea2d2718a7660a6bc0dedae1988acc2cb50000000cfe9f4280b22000aaa3ae696da6c9ec7e0001200008f04dc494bf247ab9222602456a00000033c00097a47e0b01f466e000000b6c6be0000003ecbde008000c22a1023467adb83dc6b489890eb8c1566da228000b40c8c4d0000ae25f08d83f0b3a1e28f600048e2c0d9200004469e348000d640008e81bab7cd1e81811aabe89c72426aae4552b6e9385482b0a0e166562636a24282b5e0e40da55450c0f0000a3cbe87421d65061482febd6a9613e8284e0bced8c040000b2a5ee758af04b46740f836876a06a68443c000964b180004cea72000000930bf0d8e0c69084ae30c6404bc51c9008f866c208af24285164762f47d064eca68b09f8424d762022a880040c9a6a566dcb480003648d2cdc712174d5e2da6ea1e69b89866126f400009e9fc00023e62ca6a06c300a8e434a22aa295a5801d47bcb4e8c807acb62c60c8ba2d78bac9f6b8a0000004be00015c1c4000c8000049a9ce78668c0a0bc8212ba40500007c805ca70000000cb80003083c6cc67b8b1600037800000044a0008200000005a4000000000c24840b586781380002e2ccca5080e65c3a29ca88487e8ea15a8bed005420009340007d42b23f2000000c74c343c82f07a20000e038eb8637c00c0263fe75e96a8ae5a0d3814aa18
  | 10 => 0x3cc502d9c2540fed20d8a3167507d249808c76c0000d851892e81e472000cb41c003a5d60222146449603d8a649b0a4a76009896c000dac4927fc3c20f4372754000804ca82e652ed16cd685cb825b0000000bb40000000ba04600049e0000001aa036352574caa35e4701feb083b4a7c19e7a06fa87091ad568624c08e012469040217025ca1ed3634612a0000004f00524cc7fa0000022c8bc619cb440001064d699600008e0001763e600000000022cdcc36a82c5ba5fe000904cea6ee0bc0f2d583de164000cf400035acc00000000e29d8cd02ca89674840e7302640907ec1349c61f6b7401493cbd41847286c80069b21bc1c6796a1491e6669423c45ae8ceb023806521d25dcca0000c326fe000000a3831a000d802d41dcc269165f46ec000534620000b0a382432000250b3cb14902adc8a82fa3385988b649626c57e9d00008782ea770beab9e68e94c73c9bed500347c68aa0006e4000000806b64a605a62203e80003b6dba000c10c52b0042e6a07c2000daa1044f6dca5bc592c66bf6000000c289dcdc8ada532a483e0bfeb5a7a8180866db0c00a28698322c4a82ed82000558000b9a358332c46324708da45642324800006c6ab6a9a000000b3425a2ba84e6804646cc6646ba99c68a694d9816a23aa5e2784886d4702ac6cbe682950b7a11c62841878ac943142300007a490c00098ebb600056e7820006887784c88120000008e2160000ab4c54000978d104a01c248ad74b1c0ea8927eebf4c0a454c821020003b8dbecf2a9e88a76677c000932c5e86ab782e8ac28149b466a114c6e66883a00000e4e87de5908a271484cd84a3aaa88eebd2d400000000000fcbcc74c6a4aa027e96e2745ded12980a621ce8dc76228ad662de6184103fa98c2b4bb28500006ca0008360004e4cd411e6920006fc8d644e798080d8645e292822b1072c3306b81aeaa671c0008c4484ce470c1a0c9a6d2a4492a4a48e61acd447e85561ee000000a2a54a1a27d8c7a3a8aca6f82180000629140000dc42c76ed60cc441cbfa0007c0716000000000810000000000000000bbe1004fc18a62499a53cda0d467b07221ea3e2408318000bd818e9362f8178672000000000dc25260000000646e2000c6acc20000008d02ee000794000a2c89ab3000000000081a00000000053e3945940fa00000072050a6d8000a4c0000000008f46a200056c4440008c6b600004520000004fa000248ce8b80d6a00000087ca080007dc2ec398998000660a8c4400b2320224000c5a08440a8bccf04366f627a0000008b8ca4b8ebec6264ca000dce0000005e80007ca000d2a24a638868206522b689ecc64ac861a58a196000b4cc04000000642504514000000da80000005cc3f63e400016c00000059ab907aca40874000c2a3acbaaad64d40b4d2c864286000a
  | 11 => 0x9e600000001e28e7b44eadda2600000000006140001f88589fe354112c4cc609bacae5fa6c0c485c64da67e000000000d3c3620006e623637e2c477a6b28fc00a000c900001cc3f42be448b3e994af651a2fc71aba82a013a9a888c1e410a27c5006b0af469a34205ab7e92828cd22db497c51e1927a63ce4821f09f000065e3d49e073e00025670a5822168ded32048ae01e0240a9cb368082ce168020c16b968b44b26aa61c00038c00069c7aaae632a5c05d02d89c864800000099e9240ce1409bc00070483017a14e1fcab2b28000a820000000009103f811036c000ade9a4dde8b2bc4c06ac0b1ad3459e00058c604cb0000b20000000cde00034454c04278c000b420004a217c32cad04d86d029e25e1281be000000c84ac457ad42744cc8000000ab085400046a63cc08d08772000c886ae000c3e3d0a349725b4000266000d7ad0c04a9e4000b0630a060a6e0007f474e000dd45c477484695cc1a0008941d836667cd7e0a20ca0ee45a0d40001de9d2d0a974cca132676d9457664cd3072ebc0dd22f29dab0c940310824122d627e4d249c4b32a5c4a663a5a82b607c26848683800055ac7c988392d7061687257c10845ca9808ac720000000004622526860000cc568a900f6000db60003ca6cec8a28407e26e29c6e814c144be67e60008fe4f831c0009cc222000d1800086e000000000c923a494aa5a6f23b20e67262ae4b073ac0e93a7465b603836ea30bfc00061e46ece02965a2550560c36d9601080a5d8566912aa416edc4b88ba0bae9eaa5219a970d063a6c50700a1c00060023c2b89226c252c7f800081c00000002cb5c4468ca3ba0001260005ca000000d3e1b8162a368fab046e035c03c9840b644253a8da606cec8d48a629ac56510d3a1165fc60cc3aa04a789d4c18a12bb005e1820e83500768cc328c8e2760580aad4a890d041b222acd25f24ba93e5d4a06400b845e4a7413c02a6acd527d6afecce5aa8c2662d0eddc72a0b819447cbdc39044cbee01acfc09aae8b1e790512068478bb8c9cbcad5a0005e60009c27f607870e92c10eb7236038a2940008486300ac00000046c32e20c94e64a8a0000dc63bc780000d54b54788596826920000000888b6a34e000afc000a8665aad85301fa0c209c33e8c06469ae20e244abc8eca327404fe39eb5283412cc304aa000ad221c000c862d640686c41a41221a43a706d1c3d6d7c17e85e588544c4e5c89265b89e80007926700009e27ce000a944ac41e7ae0005c2d4c000000622a7e79aaae844c1e0c4000d9a5701509ac0a45da8ba59c000be263211897ed28000a6ca1600060222e15e73400498a0009f23269446c4152d4ec4410c9c0b24000096d8877658660e976524876000c1c000d5c4b8000a8a04e00095ea88cbcd2e5d2d72b7688e71062a76400039627000
  | 12 => 0xa1a5e20a800031e000be439c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf715881000cfd7158810034fc7158810036ec215881000cff705881002cfe705881000cfd705881002cfc705881002eee205881002eec2058810004ff765081002cfe7650810004fd765081002cfc765081001ebe6450810006bd6450810005f77150810005f47150810004ff764c81002cfe764c810004fd764c81002cfc764c8101d6be644c810006bd644c810016de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c8100acff769041002cfe769041001cfd769041002cfc769041001ebe6490410006bd64904100aef6619041002dfa7090410005f970904100acff76504100057f755041004d7c755041001ebe6450410006bd6450410005ef7250410035ec72504100aef661504100a4ff768c41002cfe768c410014fd768c41002cfc768c410045be748c410005bd748c410196be648c410006bd648c410016de638c410006dd638c4100a6f6618c41002dfa708c410005f9708c4100a4ff764c41017ebe644c410006bd644c4100a6f6614c41003fd4314c41009cff768841002cfe768841000cfd768841002cfc7688410166be6488410006bd648841000eee6288410006ed628841002dfa7088410005f9708841009cff764841014ebe6448410006bd6448410094ff765001001ebe6450010006bd645001008cff764c010005bf744c010045bc744c0100eebe644c010006bd644c010084ff76480100057f754801004d7c75480100bebe6448010006bd64480100aebe64c4010006bd64c401009ef576c401002ef764c401002fb664c4010006f564c401002fb564c4010006b564c401002ef763c4010006f563c401023f7753c40100077553c401002df570c401002ef660c401002df9768401002ef9768401000cf9768401002fba648401002fb964840102377b538401000779538401022df97184010226fa618401002ff26184010004ff76440100057f754401004d7c7544010005bf7444010045bc7444010076be6444010006bd6444010005df734401003ddc7344010005ef7244010035ec724401002df77644010006f77644010004f77644010007777544010217747544010007b77444010007b4744401002ef7644401002fb66444010006f5644401002fb56444010006b56444010007d77344010007d4734401002ef76344010006f56344010217775344010007755344010007e77244010007e4724401002df7704401002ef6604401002ff25044010217f15044010005fb7644010006fb7644010004fb76440100077b7544010217787544010007bb7444010007b87444010007ba6444010007b96444010007db7344010007d873440102177b5344010007795344010007eb7244010007e8724401002dfb714401002ff3714401021efa6144010007f26144010217f25144010217f15144010
  | 1 => 0x9010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bc3259010046bf7159010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006bc3159010006bf2159010006bc2159010046bf705901002ebe705901002ebc7059010006bf505901002ebe5059010006bd505901002ebc5059010006bf305901002ebe305901002ebc3059010006bf205901002ebe205901002ebc205901002ebe105901002ebc105901002cff75d8c10024fe75d8c10004fd75d8c1002cfc75d8c1001cfe74d8c1002ebe74d8c1001cbe74d8c10004fd74d8c1002ebd74d8c10004bd74d8c1002cfc74d8c1003cfd73d8c1003e7f53d8c1000cfe72d8c10004fd72d8c1002cfc72d8c100a4fe71d8c1002ef671d8c1002cfe70d8c1002efa70d8c10014ff7658c10006be6458c10006bd6458c1002edc6358c10004ff7558c10024fe7558c10004fd7558c10024fc7558c10004ff7458c1001cfe7458c1001cfc7458c1002edf7358c1003e7f5358c1003ede5358c10006dd5358c10004ff7258c1000cfe7258c1000cfc7258c1003edf3258c10014ff7158c10014fd7158c1003cfc7158c1003edc3158c10014ff7058c1002cfe7058c10014fd7058c1002cfc7058c1002ede3058c1002edc3058c100067f7654c100067e7654c100067d7654c100067c7654c100067f6454c1020e7e6454c100073e6454c1020e3e6454c100067d6454c100073d6454c100063d6454c1020e7c6454c1003d7f7354c1004f5f7354c1003e7f6354c100167e6354c1003f5e6354c100165e6354c1003e7d6354c100075d6354c100065d6354c100167c6354c102067e6254c102067c6254c10007777154c10007747154c100a67e6154c1008e7e6054c10004ff7650c1002cfe7650c10004fd7650c1002cfc7650c1001ebe6450c10006bd6450c10005fb7050c1002df87050c1002cff75d8810024fe75d8810004fd75d881002cfc75d881001cfe74d881002ebe74d881001cbe74d8810004fd74d881002ebd74d8810004bd74d881002cfc74d8810014fe73d8810004fd73d881002cfc73d88100067f53d88100067d53d8810034fd72d881009cfe71d881002ef671d881002cfe70d881002efa70d881000cff7658810006be6458810006bd645881002eec6258810004ff7558810024fe7558810004fd7558810024fc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810014fc73588100067f53588100067d535881002eef7258810036ee5258810006ed5258810036ee325881000cf
  | 2 => 0xfeec628c110007d6318c110014ff764c11006cfd764c110014fc764c1100067f654c1100f67c654c110005bf744c110075bc744c110006bf644c1100eebc644c110006df634c110016dc634c110006ef624c1100e6ec624c110005f7714c110005f4714c11009cfe76881100067f65881100de7c6588110006bf64881100d6bc6488110006df63881100cedc6388110006ef628811000eec628811000cff7648110064fd764811000cfc76481100057f754811007d7c75481100067f65481100c67c6548110006bf64481100bebc6448110006df63481100b6dc6348110006ef624811000eec6248110005f77148110005f47148110067e820481100067f65c411005e7c65c4110006bf64c41100aebc64c4110006df63c41100a6dc63c4110006ef62c411009eec62c41100077b65c411024f7865c4110007bb64c4110007b864c4110007db63c4110007d863c411024f7b53c41100077953c4110007eb62c4110007e862c4110007f241c4110007f141c4110007f231c4110007f131c41100067f65841100567c6584110006bf6484110096bc6484110006df638411008edc6384110006ef6284110086ec6284110065f6768411000777658411024774658411002df77484110005f57484110007b76484110007b4648411002df77384110005f57384110007d76384110007d46384110247775384110007755384110007e76284110007e46284110007f3608411002cff75d9010024fe75d9010004fd75d901002cfc75d9010044fd74d9010014fe73d9010004fd73d901002cfc73d90100067f53d901000cfe72d9010004fd72d901002cfc72d90100acfe71d901002ef671d901002cfe70d901002efa70d9010004bd769901002ebf6599010006be6599010006bd659901002ebc659901002ebf6399010006be639901002ebc63990100073f539901002ebf6299010006be629901002ebc629901002ebe609901001cff765901002ebc6459010004ff7559010024fe7559010004fd7559010024fc755901002ebf7459010006bf5459010046be5459010006bd5459010046bc5459010004ff7359010014fe7359010014fc73590100067f5359010046bf4359010006be4359010046bc4359010004ff725901000cfe725901000cfc7259010046bf4259010006be4259010046bc425901001cff715901001cfd7159010044fc7159010046bc415901001cff705901002cfe705901001cfd705901002cfc705901002ebe405901002ebc405901002dbf7659010046bf765901001cbf765901002ebf6559010006be6559010006bd655901002ebc655901002ebf6359010006be635901002ebc63590100073f535901002ebf6259010006be625901002ebc6259010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be735
  | 3 => 0x54390510007e76290510007e4629051002df67090510077b4409051001cfc76505100057f755051007d7c75505100067f65505101b67c6550510006bf645051001ebc6450510006df63505101aedc6350510005ef7250510065ec7250510006ef62505101a6ec6250510077b44150510005fb7050510005f87050510075f4765051001ef4765051001cf4765051000777755051026f74755051000777655051026f746550510075f77450510007b77450510007b7645051001ef6645051001ef46450510077b46450510005f77350510007d76350510007d4635051026f775350510007755350510267b64350510077b44350510007e77250510007e47250510007e76250510007e46250510077b74250510007b54250510007f3705051002df47050510007f07050510077b7405051008cfe768c5100067f658c51019e7c658c510075be748c510005bd748c510006bf648c510196bc648c510006df638c510016dc638c510006ef628c51018eec628c510005f6768c51008ef6768c51000777658c51025f74658c510005f7748c510007b6748c510005f5748c510007b5748c510005b5748c510007b7648c510007b4648c51006df5738c510007d7638c510016f6638c510016f4638c51006fd4638c510016d4638c51006f77538c51006f75538c510007e7628c510007e4628c51002df6708c51006fd4308c510014fc764c5100067f654c5101867c654c510006bf644c51017ebc644c510006df634c510016dc634c510006ef624c510176ec624c510005fb704c510005f8704c51006df4764c510016f4764c510014f4764c51000777654c51025774654c510005f7744c510005f5744c510007b7644c510007b4644c51006df7734c510007d7734c510007d7634c510016f6634c510016f4634c51006fd4634c510016d4634c51006f77534c51006f75534c510007e7624c510007e4624c510007f3704c51002df4704c510007f0704c510084fe76885100067f658851016e7c6588510006bf6488510166bc6488510006df638851015edc6388510006ef628851000eec628851000cfc76485100067f65485101567c6548510006bf644851014ebc6448510006df6348510146dc6348510006ef624851000eec6248510005fb7048510005f870485100acfe76901100067f659011013e7c6590110006bf649011001ebc6490110006df6390110136dc6390110006ef629011012eec6290110007b6419011001cff7650110074fd765011001cfc76501100067f65501101267c6550110006bf645011001ebc6450110006df635011011edc6350110006ef6250110116ec6250110005f77150110005f47150110007b541501100a4fe768c1100067f658c11010e7c658c110006bf648c110106bc648c110006df638c110016dc638c110006ef628c110
  | 4 => 0x89100076d53d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910066ee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ec41d8910006ef31d8910006ec31d8910006ef70d8910066ee70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ec40d8910006ef30d8910006ec30d89100057f755891007d7c75589100067f65589100067c6558910005bf7458910075bc7458910006bf6458910006bc6458910005df735891006ddc7358910006df6358910006dc6358910066ec6258910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc73589100067f53589100067d5358910064ff7258910006ef7258910084ff7158910006f7715891009cff7058910006fb7058910005ee7618910066ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d5318910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101ee7c6550910006bf645091001ebc6450910006df63509101e6dc6350910006ef625091000eec6250910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101de7c654c910006bf644c9101d6bc644c910006df634c910016dc634c910006ef624c91000eec624c910094fe76905100067f65905101ce7c6590510006bf649051001ebc6490510006df63905101c6dc6390510006ef62905101beec6290510005f67690510096f67690510007776590510277746590510075f57490510007b7649051001ef6649051001ef46490510077b4649051001eb46490510005f57390510007d76390510007d46390510277775390510007755390510077b74390510007b
  | 5 => 0x6df20d8d10006dc20d8d100057f7558d1007d7c7558d100067f6558d100067c6558d10005bf7458d10075bc7458d10006bf6458d10006bc6458d1006edc6358d10005ef7258d10065ec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d1006cff7358d10006df7358d1006e7f5358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1008cff7158d10006f77158d100a4ff7058d10006fb7058d10005de7618d1006ede7618d10004de7618d1006f5e7518d1006f5d7518d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d1006fd57118d100067f7654d100057e7654d100067e7654d100047e7654d100067d7654d100057c7654d100067c7654d100047c7654d100067f6454d100073f6454d100063f6454d1020e7e6454d100067d6454d1020e7c6454d100073c6454d1020e3c6454d1006d7f7354d1007f5f7354d1006e7f6354d100075f6354d100065f6354d100167e6354d1006e7d6354d100167c6354d1006f5c6354d100165c6354d102067e6254d102067c6254d102066c6254d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d101fe7c6550d10006bf6450d1001ebc6450d10006df6350d10016dc6350d101f6ec6250d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910066ee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006ef52d8910066ee52d8910006ed52d8910066ec52d8910006ef42d8910066ee42d8910066ec42d8910006ef32d8910066ee32d8910066ec32d891000cfe71d8910064fd71d891000cfc71d8910066ef21d891002cfe70d8910064fd70d891002cfc70d8910066ef20d8910065ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d
  | 6 => 0xe50d9110006bd50d9110006bc50d9110006bf30d9110006bc30d9110006bf20d9110006bc20d91100057f755911007d7c75591100067f65591100067c6559110076bc6459110005df735911006ddc7359110005ef7259110065ec7259110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c7559110074ff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc73591100067f5359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec7259110094ff7159110006f771591100acff7059110006fb7059110005be7619110076be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc63191100073f5319110006be6219110006bc6219110077b57119110014fe76d8d1007d7c75d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1006ede63d8d100075f53d8d10004ff75d8d100067f75d8d10024fe75d8d10004fd75d8d10024fc75d8d100067c75d8d100247c75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d1006e7f53d8d10006df53d8d100065f53d8d1006ede53d8d10006dd53d8d1006edc53d8d10006df43d8d1006ede43d8d1006edc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d1006edf32d8d10006de32d8d1006edc32d8d10014fe71d8d1006cfd71d8d10014fc71d8d1006edf31d8d1002cfe70d8d1006cfd70d8d1002cfc70d8d1006edf30d8d1006dde76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10007d771d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d10006df71d8d1006ede71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d1006ede70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006dc40d8d10
  | 7 => 0x861000eec628861000cff764861002cfc764861000eee6248610006ed6248610005fb704861002df87048610044ff765021002ebf645021002ebc645021003cff764c210005bf744c210095bc744c210034ff76482100057f75482100557c754821002fe8204821002df576c4210006f576c421002ef764c4210006f564c421002ef763c4210006f563c421027f7753c42100077553c4210005f976c4210006f976c421027f7b53c42100077953c421007d7e76d951007e7e76d95100247e76d95100067e64d95100067c64d95100057d73d95100067e63d95100067c63d95100067e62d95100067c62d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d95100067f71d951007e7e71d951007e7d71d951007e7c71d95100067f41d95100067c41d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d951007e7e70d951007e7d70d951007e7c70d95100067f40d95100067c40d95100067f30d95100067c30d95100067f20d95100067c20d951007e7d10d951001cfe76d91100067f65d91100067c65d9110076be64d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110006bf54d9110076be54d9110006bd54d9110076bc54d9110014fe73d9110004fd73d9110014fc73d91100067f53d9110076bf43d9110006be43d9110076bc43d911000cfe72d9110004fd72d911000cfc72d9110076bf42d9110006be42d9110076bc42d911001cfe71d9110074fd71d911001cfc71d9110076bf41d911002cfe70d9110074fd70d911002cfc70d9110076bf40d9110075be76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d91100073f53d9110006be62d9110006bc62d9110007b771d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110006bf71d9110076be71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d9110076be70d9110006bd70d9110006bf50d9110006b
  | 8 => 0x4ed72d921002cfc72d9210096bf42d921002ef571d9210096bc41d921002efa70d921002ebf40d921001cff765921002ebc6459210004ff7559210024fe7559210004fd7559210024fc755921002ebf7459210004ff7359210014fe7359210014fc73592100067f5359210096bf4359210004ff725921000cfe725921000cfc7259210096bf415921002ebe405921002ebc405921002cff75d8e10024fe75d8e10004fd75d8e1002cfc75d8e1001cfe74d8e10004fd74d8e1002cfc74d8e1008cfd73d8e1008e7f53d8e1000cfe72d8e10004fd72d8e1002cfc72d8e1002ef571d8e1008edc31d8e1002efa70d8e10014ff7658e10005bf7458e10095bc7458e1002edc6358e10004ff7558e10024fe7558e10004fd7558e10024fc7558e10004ff7458e10006bf7458e10004bf7458e1001cfe7458e1001cfc7458e10006bc7458e1001cbc7458e1002edf7358e1008e7f5358e10004ff7258e1000cfe7258e1000cfc7258e1008edf3158e1002ede3058e1002edc3058e100067f7654e100067e7654e100067d7654e100067c7654e100067f6454e1020e7e6454e100067d6454e1020e7c6454e1008d7f7354e100575f7354e1008e7f6354e100167e6354e1008e7d6354e100167c6354e102067e6254e102067c6254e10007777154e10007747154e1006e7d6154e1003e7e6054e10004ff7650e1002cfe7650e10004fd7650e1002cfc7650e1001ebe6450e10006bd6450e1002cff75d8a10024fe75d8a10004fd75d8a1002cfc75d8a1001cfe74d8a10004fd74d8a1002cfc74d8a10014fe73d8a10004fd73d8a1002cfc73d8a100067f53d8a100067d53d8a10084fd72d8a1002ef571d8a10086ec21d8a1002efa70d8a1000cff7658a1002eec6258a10004ff7558a10024fe7558a10004fd7558a10024fc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a100067f5358a100067d5358a1002eef7258a10086ee5258a10006ed5258a10006ef4258a10086ec4258a10086ee3258a10086ef2158a1002eee2058a1002eec2058a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a10006bf6450a1001ebc6450a10005f77150a10005f47150a10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca1000eee624ca10006ed624ca10005f7714ca10005f4714ca10074fd7690610006bf649061001ebc649061001cff765061002cfc76506100057f75506100557c755061001ebe6450610006bd6450610005ef7250610085ec7250610005fb705061002df8705061006cfd768c610095be748c610005bd748c610006df638c610016dc638c610014ff764c61002cfc764c610016de634c610006dd634c61008fd4314c610005fb704c61002df8704c610064fd7688610006ef628
  | 9 => 0xe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10014fc7358b100067f5358b100067d5358b10006ef7258b1009eec2158b1009eef2058b10004ff7650b10004fe7650b10004fd7650b10004fc7650b1001ebe6450b10006bd6450b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006ef624cb1000eec624cb1001cfd769071001ebe6490710006bd6490710005fa7090710005f970907100adf5769071001ef5769071001cf5769071001ef664907100afb66490710007b5649071001ef46490710005f573907102977753907100077553907100afb74390710007b5439071002df67090710007f27090710007f170907100afb44090710044ff76507100057f755071005d7c7550710006bf645071001ebc6450710005ef725071009dec72507100afb44150710005f77650710046f7765071000777755071028f747550710007b77450710007b7645071001ef6645071001ef464507100afb46450710005f7735071028f775350710007755350710287b643507100afb44350710007e77250710007e472507100afb74250710007b5425071002df470507100afb74050710014fd768c7100adbe748c710005bd748c710016de638c710006dd638c710005fa708c710005f9708c7100a5f5768c710016f5768c710014f5768c710005f7748c710007b6748c710005f5748c710007b5748c710005b5748c710016f6638c7100a7d6638c710007d5638c710016f4638c7100a777538c7100a775538c71002df6708c710007f2708c710007f1708c7100a7d4308c71003cff764c710005f7764c71003ef7764c710005f7744c710005f5744c710007d7734c710016f6634c710016f4634c7100a777534c7100a775534c71002df4704c71000cfd768871000eee6288710006ed6288710005fa7088710005f97088710034ff7648710074fd7690310006bf649031001ebc6490310007b6419031001cff765031001cfc765031001ebe6450310006bd6450310005f77150310005f47150310007b5415031006cfd768c310006df638c310016dc638c310007d6318c310014ff764c310014fc764c310005bf744c3100adbc744c310016de634c310006dd634c310005f7714c310005f4714c310064fd7688310006ef628831000eec628831000cff764831000cfc76483100057f754831005d7c754831000eee6248310006ed6248310005f77148310005f4714831002cff75d9210024fe75d921002e7e75d92100247e75d9210004fd75d921002e7d75d92100047d75d921002cfc75d9210094fd74d9210014fe73d9210004fd73d921002cfc73d92100067f53d9210006be43d9210096bc43d921000cfe72d921002eee72d921000cee72d9210004fd72d921002eed72d9210
  | 10 => 0x12013e7c659012001ebe6490120006bd649012001cff765012000cfe7650120114fd765012000cfc76501200067f65501201267c6550120006bf645012001ebc6450120005ef725012000dec72501202acfe768c1200067f658c12010e7c658c12002dec728c120014ff764c12000cfe764c1200e4fd764c12000cfc764c1200067f654c1200f67c654c120005bf744c1200bdbc744c120006df634c120016dc634c120005ef724c12000dec724c12002def75881202a5ed75881200076f658812029f6c658812002def7388120005ed738812029f6f53881200076d5388120006ec618812002dee708812002fea708812002eef608812000feb60881200aebe64d9310004ff75d9310024fe75d9310004fd75d9310024fc75d93100acfd74d9310014fe73d9310004fd73d9310014fc73d93100067f53d93100aebf43d931000cfe72d9310004fd72d931000cfc72d9310006f671d93100aebf41d9310006f970d93100aebc40d931001cff76593100aebc6459310004ff7559310024fe7559310004fd7559310024fc7559310006bf7459310004ff7359310014fe7359310014fc73593100067f5359310006be43593100aebc4359310004ff725931000cfe725931000cfc72593100aebf42593100aebc41593100aebf40593100adbe74d8f10005bd74d8f100a6de63d8f10004ff75d8f10024fe75d8f10004fd75d8f10024fc75d8f1001cfe74d8f10006be74d8f1001cbe74d8f10004fd74d8f10006bd74d8f10004bd74d8f1001cfc74d8f100a4fd73d8f100a67f53d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f10006f970d8f100a6dc30d8f10014ff7658f100a6dc6358f10004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f1001cfe7458f1001cfc7458f10006df7358f100a67f5358f10004ff7258f1000cfe7258f1000cfc7258f100a6dc3158f100a6df3058f100067f7654f100067e7654f100067d7654f100067c7654f100067f6454f1020e7e6454f100067d6454f1020e7c6454f100a57f7354f1005f5f7354f100a67f6354f100167e6354f100a67d6354f100167c6354f102067e6254f102067c6254f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006bf6450f1001ebc6450f10005fb7050f10005f87050f1005d7e75d8b100057d75d8b1009eee62d8b10004ff75d8b10024fe75d8b100067e75d8b100247e75d8b10004fd75d8b100067d75d8b100047d75d8b10024fc75d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b1009cfd72d8b1009eee52d8b10006ed52d8b1009eee32d8b10006f671d8b10006f970d8b1009eec20d8b1000cff7658b1009eec6258b10004ff7558b10024f
  | 11 => 0xfcff7358d20006df7358d200b67f5358d200e4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d202d4ff7058d20006fb7058d200067f7654d200057e7654d200067e7654d200047e7654d200067d7654d200057c7654d200067c7654d200047c7654d200067f6454d2020e7e6454d200067d6454d2020e7c6454d202cd7f7354d200c75f7354d200b67f6354d200167e6354d200b67d6354d200167c6354d202076e7254d200076d7254d202067f6254d202076e3254d202067f6054d202077b2054d202076c2054d20207782054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201fe7c6550d2001ebe6450d20006bd6450d200b5ec764c920016ec764c920014ec764c9202c5ef754c9202c5ed754c9200076f654c9202bf6c654c920006ef644c920006ed644c92000def734c92000fcf734c920007cf634c920016ee634c920016ec634c9200b7cc634c9200b76f534c9200b76d534c920007eb704c92002dec704c920007e8704c920005e8704c92000eef604c92000feb604c9200067f65d85200067c65d8520004ff75d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520006f741d8520006f441d8520006f731d8520006f431d8520086f621d8520086f521d85200c57e75985200057d75985200067f65985200067c6598520006f76198520065f970985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520005df73585200b5dc735852009dfb70585200067f65185200067c65185200bdbe7418520005bd7418520006f56118520004ff7518520024fe7518520004fd7518520024fc751852001cfe7418520006be741852001cbe7418520004fd7418520006bd7418520004bd741852001cfc7418520014fe7318520004fd7318520014fc73185200067f53185200067d5318520036ee5218520006ed5218520036ee3218520006ed3218520006f74118520006f44118520006f73118520006f43118520036f62118520036f52118520036ec2018520004fe7690520004fd7690520004fc76905200067f65905201ce7c6590520006bf649052001ebc6490520004ff7650520004fe7650520004fc76505200057f75505200c57c75505200067f65505201b67c655052001ebe6450520006bd6450520005ef725052000dec7250520004fe768c520004fd768c520004fc768c5200067f658c52019e7c658c5200bdbe748c520005bd748c520006df638c520016dc638c520004ff764c520004fe764c520004fc764c5200067f654c5201867c654c5202b4fe76901200067f659
  | 12 => 0x820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067c43d95202e67f72d95202e67e72d95202e67d72d95202e67c72d95202e67f42d95202e67e42d95202e67d42d95202e67c42d95202e67f32d95202e67e32d95202e67d32d95202e67c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067c31d95202e67f21d95202e67e21d95202e67d21d95202e67c21d95202e67f70d95200c67e70d95202e67d70d95202e67c70d95200067f40d95200067c40d95200067f30d95200067c30d95202e67f20d95202e67e20d95202e67d20d95202e67c20d952001cfe76d91200067f65d91200067c65d91200bebe64d9120004ff75d9120024fe75d9120004fd75d9120024fc75d9120014fe73d9120004fd73d9120014fc73d91200067f53d9120006be43d91200bebc43d912002cff72d912000cfe72d912012cfd72d912000cfc72d912012ebf42d912012ebd42d912012eee32d9120004fe71d9120004fd71d91200bebc41d912000cfd70d91200bebf40d91200057f75591200c57c75591200067f65591200067c65591200bebc6459120005df73591200b5dc7359120005f77159120005f471591202ddfb7059120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c755912012cff7459120006bf7459120004ff7359120006df7359120004df7359120014fe7359120014fc7359120006dc7359120014dc73591200067f53591200bebf4359120114ff7259120006ef7259120116ee3259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f471591200bebf41591202dcff7059120006fb70591200bebc4059120014fe76d8d200c57c75d8d200067f65d8d200067c65d8d200b6de63d8d20004ff75d8d200067f75d8d20024fe75d8d20004fd75d8d20024fc75d8d200067c75d8d200247c75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d200b67f53d8d20006df43d8d200b6dc43d8d2002cff72d8d2000cfe72d8d200fcfd72d8d2000cfc72d8d200fedf32d8d200fedd32d8d20004fe71d8d20004fd71d8d200b6dc31d8d2000cfd70d8d200b6df30d8d200057f7558d200c57c7558d200067f6558d200067c6558d20005bf7458d200bdbc7458d200b6dc6358d20005f77158d20005f47158d202d5fb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d2001cfc7458d20006bc7458d2001cbc7458d20
  | 13 => 0x8e200e4fd73d8e200ce7f53d8e2002eed72d8e20004fe71d8e20004fd71d8e200feec21d8e2002cfe70d8e2002efa70d8e2002eef20d8e20014ff7658e2002edc6358e20004ff7558e20024fe7558e20004fd7558e20024fc7558e20004ff7458e2001cfe7458e2001cfc7458e2002edf7358e200ce7f5358e200e6df3258e200e6dd3258e20004ff7158e20004fc7158e200e6ec2158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e200e6ef2058e200067f7654e200067e7654e200067d7654e200067c7654e200067f6454e2020e7e6454e200067d6454e2020e7c6454e202cd7f7354e200df5f7354e200ce7f6354e200167e6354e200ce7d6354e200167c6354e200076f7254e202076c7254e202067d6254e202076c2154e202067e6054e202076f2054e202077b2054e20207782054e20004ff7650e2002cfe7650e20004fd7650e2002cfc7650e2001ebe6450e20006bd6450e2002ef76198620004ff7598620024fe7598620004fd7598620024fc759862001cfe7498620004fd749862001cfc7498620014fe7398620004fd7398620014fc73986200067f53986200067d5398620006f75198620006f4519862009ef6219862009ef5219862002cfe709862002ef6109862002ef410986200057f75586200dd7c755862002ef46158620004ff75586200067f75586200047f7558620024fe7558620004fd7558620024fc75586200067c75586200247c7558620004ff745862001cfe745862001cfc7458620004ff7358620014fe7358620014fc73586200067f53586200067d5358620006f75158620006f45158620066f62158620066f52158620066ec215862002cfc705862002ef6105862002ef41058620004ff769062002cfe7690620004fd7690620006f66190620006f56190620004ff7650620004fd765062002cfc76506200057f75506200dd7c755062001ebe6450620006bd6450620005ef725062000dec7250620006f66150620006f56150620004ff768c62002cfe768c620004fd768c6200d5be748c620005bd748c620006f6618c620006f5618c620004ff764c620004fd764c62002cfc764c620005ef724c62000dec724c620006f6614c620006f5614c6202f6ef65886202f6ed6588620166ee6488620166ec6488620006ef6388620006ed63886202f76f53886200076d538862000dee718862000fe67188620007e66188620006ed6188620007e56188620007ea7088620005ed7088620007e9708862000eee608862000fea60886202dcff76502202d4ff764c220005bf744c2200d5bc744c2202ed7e76d95200c67e76d95200247e76d95200067e64d95200067c64d95200057d73d95200067e63d95200067c63d95200076f72d95202e76c72d95202e76e32d95202e77b20d95202e76c20d95202e77
  | 14 => 0xce7f53d89300ce7d53d8930006ef52d89300e6ec52d89300e6ee32d89300ceed32d8930004fe71d8930004fd71d89300e6ec21d8930014fd70d89300e6ef20d89300057f75589300f57c7558930005bf74589300edbc7458930006bf6458930006bc64589300e6ec6258930005f77158930005f47158930305fb7058930004ff7650930004fe7650930004fc7650930006bf645093001ebc6450930006bf64d8530006bc64d8530004ff75d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853008e7f53d853008e7d53d853000cfe72d8530004fd72d853000cfc72d8530006f751d8530006f451d853008ef631d853008ef531d8530006f721d8530006f421d85300edbe7498530005bd7498530006bf6498530006bc6498530006f7619853006df970985300057f75585300f57c7558530005bf74585300edbc7458530006bf6458530006bc6458530005ef72585300e5ec72585300a5fb7058530006bf6418530006bc6418530006f56118530004ff7518530024fe7518530004fd7518530024fc751853001cfe7418530004fd741853001cfc741853003e7f531853003e7d531853000cfe7218530004fd721853000cfc7218530006f75118530006f4511853003ef6311853003ef53118530006f72118530006f4211853003edc3018530004fe7690530004fd7690530004fc7690530006bf649053001ebc6490530004ff7650530004fe7650530004fc76505300057f75505300f57c7550530006bf645053001ebc6450530005ef72505300e5ec7250530004fe7688530004fd7688530004fc7688530006bf6488530166bc6488530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530006bf644853014ebc64485302fcfe7690130136bf649013001ebc649013001cff7650130014fe765013011cfd7650130014fc7650130006bf645013001ebc6450130005df7350130015dc73501300079f648c1300079c648c130006dc618c13002dde708c13002fda708c13002edf608c130017db608c13002cff75d9220024fe75d9220004fd75d922002cfc75d9220114fd74d9220014fe73d9220004fd73d922002cfc73d92200067f53d922002eed72d9220004fe71d9220004fd71d922002cfe70d922002efa70d922001cff765922002ebc6459220004ff7559220024fe7559220004fd7559220024fc755922002ebf7459220006bf54592200d6bc5459220004ff7359220014fe7359220014fc73592200067f53592200d6bf4359220116bf4259220116bd4259220004ff7159220004fc71592200d6bf415922002cfe705922002cfc705922002ebe405922002ebc405922002cff75d8e20024fe75d8e20004fd75d8e2002cfc75d8e2001cfe74d8e20004fd74d8e2002cfc74d
  | 15 => 0xc7350630005ef72506300fdec7250630006f66150630006f561506300079e748c6300079d748c630015de718c630017d6718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c630016de608c630017da608c630004ff768863002cfe7688630004fd768863000eec6288630004ff7648630004fd764863002cfc7648630005df7348630015dc734863030cff765023002ebf645023002ebc645023001cfe76d91300eebe64d9130004ff75d9130024fe75d9130004fd75d9130024fc75d9130006bf54d91300eebe54d9130006bd54d91300eebc54d913002cff73d9130014fe73d9130134fd73d9130014fc73d91301367f53d91301367d53d9130136bf43d9130136bd43d913000cfe72d9130004fd72d913000cfc72d91300eebf42d9130006be42d91300eebc42d9130004fe71d9130004fd71d91300eebf41d91300eebc41d9130014fd70d91300eebf40d91302fdbe76d913001cbe76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91301373f53d91301373d53d9130006be62d9130006bc62d9130137bb30d91301379c30d9130137b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130136bf73d9130136be73d9130136bd73d9130136bc73d9130136bf53d91301363f53d9130136be53d9130136bd53d91301363d53d9130136bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130136bf32d9130136be32d9130136bd32d9130136bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130136bf31d9130136be31d9130136bd31d9130136bc31d9130006bf21d9130006bc21d9130136bf70d91300eebe70d9130136bd70d9130006bf50d9130006be50d9130006bd50d9130006bc50d9130136bf30d9130136be30d9130136bc30d9130006bf20d9130006bc20d91300eebc645913030dfb7059130004ff7559130024fe7559130004fd7559130024fc7559130134ff7459130006bf745913011cff7359130006df735913011e7f535913011e7d5359130004ff725913000cfe725913000cfc7259130004ff7159130004fc715913030cff7059130006fb7059130135be76191300eebe7619130134be7619130006bf6519130006be6519130006bd6519130006bc65191302febf63191302ff3f53191302ff3d5319130006be6219130006bc62191302febf60191302ffbb30191302ff9c30191302ffb8301913000cfe76d8930006bf64d8930006bc64d89300e6ee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893000cfc73d8930
  | 16 => 0xc540004fc764c54001dbe744c540005bd744c540004fe7688540004fd7688540004fc768854001dbe7488540005bd7488540006ef628854000eec6288540004ff7648540004fe7648540004fc7648540005bd7390140136be6390140136bc63901403173f53901400073d5390140006bf6290140005bd7190140006bc619014002dbe709014002fba709014002ebf609014001fbb609014002cff75d9230024fe75d9230004fd75d923002cfc75d923011cfd74d923002edd73d92301367f53d92301367d53d9230136be43d9230136bc43d923000cfe72d9230004fd72d923002cfc72d9230106bf42d9230004fe71d9230004fd71d9230106bc41d923002cfe70d923002efa70d923002ebf40d923001cff765923002ebc6459230004ff7559230024fe7559230004fd7559230024fc755923002ebf745923011e7f535923011e7d535923011ebf435923011ebd4359230004ff725923000cfe725923000cfc7259230004ff7159230004fc7159230106bf415923002cfe705923002cfc705923002ebe405923002ebc405923000cff7658a300057f7558a3010d7c7558a3002eec6258a30004ff7558a300067f7558a300047f7558a30024fe7558a30004fd7558a30024fc7558a300067c7558a300247c7558a30004ff7458a3001cfe7458a3001cfc7458a300b67f5358a300b67d5358a300feee5258a30006ed5258a300feee3258a300b6ed3258a30004ff7158a30004fc7158a3002cfe7058a3002cfc7058a3002eee2058a3002eec2058a30004ff7650a30004fd7650a3002cfc7650a30006bf6450a3001ebc6450a30005df7350a30015dc7350a3002ef76198630004ff7598630024fe7598630004fd7598630024fc759863001cfe7498630004fd749863001cfc74986300a67f53986300a67d539863000cfe7298630004fd729863000cfc72986300a6f631986300a6f5319863002cfe709863002ef6109863002ef410986300057f755863010d7c7558630005bf7458630105bc7458630005ef72586300fdec725863002ef46158630004ff75586300067f75586300047f7558630024fe7558630004fd7558630024fc75586300067c75586300247c7558630004ff7458630006bf7458630004bf745863001cfe745863001cfc7458630006bc745863001cbc745863006e7f535863006e7d5358630004ff7258630006ef7258630004ef725863000cfe725863000cfc7258630006ec725863000cec725863006ef6315863006ef5315863006edc315863002cfc705863002ef6105863002ef41058630004ff769063002cfe7690630004fd7690630006bf649063001ebc6490630006f66190630006f56190630004ff7650630004fd765063002cfc76506300057f755063010d7c755063001ebe6450630006bd6450630005df7350630015d
  | 17 => 0x4ff75d8d40024fe75d8d40004fd75d8d40024fc75d8d40014fc74d8d4011e7f53d8d4011ede53d8d40006dd53d8d4011ede43d8d40106dd43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d40006de32d8d4011edc32d8d40004fe71d8d40004fd71d8d4011edc31d8d4001cfd70d8d4011edf30d8d4011edc6358d4032dfb7058d400067f7654d400067e7654d400067d7654d400067c7654d401367f6454d4011d7f7354d401275f7354d4011e7f6354d400075f6354d400065f6354d400167e6354d400167c6354d4011f5c6354d400165c6354d4011f3f4354d402067e6254d402067c6254d4020f3f4154d4030e7f6054d4020f7b4054d4020f3c4054d4020f784054d4011dbc7650d40016bc7650d40014bc7650d4001dbf7350d4001f9f7350d400079f6350d40016be6350d40016bc6350d4011f9c6350d4011f3f5350d4011f3d5350d40005bf7150d40007bb7050d4002dbc7050d40007b87050d4001ebf6050d4001fbb6050d4000cfe76d8940116ee62d8940004ff75d8940024fe75d8940004fd75d8940024fc75d894000cfc74d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d89400d6bf43d8940006bd43d8940116ee42d89400d6ed42d8940004fe71d8940004fd71d89400d6bf41d8940116ec21d894001cfd70d89400d6bc40d8940116ef20d89400057f75589401257c7558940005df735894011ddc7358940116ec6258940005f77158940005f47158940325fb7058940004ff764c940004fe764c940004fc764c94000eee624c940004ff75d8540024fe75d8540004fd75d8540024fc75d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854000cfe72d8540004fd72d854000cfc72d8540096f641d8540096f541d8540006f721d8540006f421d8540006f76198540075f970985400057f75585401257c7558540005df735854011ddc7358540005ef7258540115ec72585400adfb7058540006f56118540004ff7518540024fe7518540004fd7518540024fc7518540014fe7318540004fd7318540014fc73185400067f53185400067d5318540046bf4318540006bd431854000cfe7218540004fd721854000cfc7218540046bf4118540046f64118540046f54118540006f72118540006f42118540046bc40185400073f755054031f3c7550540005bf73505401aebe63505401aebc635054031f3f53505400073d5350540007af7250540007ac7250540006bf625054001dbf715054001fb77150540007b76150540006bc6150540007b46150540007bb705054002dbc7050540007b8705054001ebf605054001fbb6050540004fe768c540004fd768c540004fc768c54001dbe748c540005bd748c540006df638c540016dc638c540004ff764c540004fe764
  | 18 => 0xc7258e400eebf4258e40004ff7158e40004fc7158e400eebc4158e4002cfe7058e4002cfc7058e400eebf4058e4002ede3058e4002edc3058e400067f7654e400067e7654e400067d7654e400067c7654e400073f7454e4020f3c7454e4011e7d6454e401357f7354e4013f5f7354e400167e6354e401367d6354e400167c6354e401373e4354e401373c4354e402067e6254e402067c6254e4020f3f4254e4020f3c4154e402fe7e6054e4020f3f4054e4020f7b4054e4020f784054e4000cff7658a4002eec6258a40004ff7558a40024fe7558a40004fd7558a40024fc7558a40004ff7358a40014fe7358a40014fc7358a400067f5358a400067d5358a4012eee5258a40006ed5258a4012eee4258a400beed4258a4012eee3258a40004ff7158a40004fc7158a4012eec2158a4002cfe7058a4002cfc7058a4002eee2058a4002eec2058a4012dbf7650a4000ebf7650a4000cbf7650a40135be7350a40135bc7350a40006bd6350a4033f3f5350a400073d5350a4001dbf7250a4001faf7250a4000ebe6250a4012fae6250a40007ad6250a4000ebc6250a4012fae3250a40005bc7150a40005bf7050a40007bb7050a40007b87050a4001ebe6050a4001fba6050a40004ff764ca40004fd764ca4002cfc764ca40005bf744ca4001dbc744ca4000eee624ca40006ed624ca40007ad424ca4002ef76198640004ff7598640024fe7598640004fd7598640024fc7598640014fe7398640004fd7398640014fc73986400067f53986400067d539864000cfe7298640004fd729864000cfc72986400aef641986400aef5419864002cfe709864002ef6109864002ef4109864002ef46158640004ff7558640024fe7558640004fd7558640024fc7558640004ff7358640014fe7358640014fc73586400067f53586400067d5358640006be4358640076bc4358640004ff725864000cfe725864000cfc7258640076bf4258640006bd4258640076f64158640076f54158640076bc415864002cfc7058640076bf405864002ef6105864002ef41058640135be7390640135bc7390640006bd63906403373f53906400073d5390640005bd729064001dbe719064001fb67190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b9709064001ebe609064001fba6090640004ff768c64002cfe768c640004fd768c64001dbe748c640005bd748c640006f6618c640006f5618c640004ff764c640004fd764c64002cfc764c640005bf744c64001dbc744c640006f6614c640006f5614c640004ff768864002cfe7688640004fd7688640005bf748864001dbc748864000eee6288640006ed6288640167af4288640004ff7648640004fd764864002cfc7648640005bf744864001dbc7448640014fe76d8d4011ede63d8d40
  | 19 => 0x91210047f7559121024fe7559121004fd7559121024fc75591210067c75591210247c75591211bcff7459121006bf7459121004ff7359121014fe7359121014fc73591210067f53591211a4ff7259121006ef7259121164ef7259121364ff7159121006f77159121004ff705912102cfc7059121014fe76d8d21146de63d8d21004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d211467f53d8d2118cff72d8d2118cfd72d8d2118edf32d8d2118edd32d8d2100cfd71d8d21146df31d8d2118eec21d8d2102cfe70d8d21004fd70d8d21146dc30d8d21146dc6358d2135df77158d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d2118cff7358d21006df7358d211467f5358d21174ff7258d21006ef7258d2135cff7158d21006f77158d21176ec2158d21004ff7058d2102cfc7058d210067f7654d210067e7654d210067d7654d210067c7654d210067f6454d2120e7e6454d210067d6454d2120e7c6454d212cd7f7354d211575f7354d211467f6354d210167e6354d211467d6354d210167c6354d212067f6254d212067f6154d21207772154d212076c2154d21207742154d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc6450d21354fe769052101cff765052100cfe76505211a4fd765052100cfc76505210057f75505211557c7550521006bf645052101ebc6450521005ef725052100dec725052134cfe768c52114dbe748c521005bd748c521014ff764c52100cfe764c521174fd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724c521147d4314c521346ef6588521346ed6588521166ee6488521166ec6488521006ef6388521006ed63885213476f53885210076d538852100dee718852100fe6718852100eef618852100fe76188521004ff75d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d812109efa20d8121006fb60981210057f75581211557c7558121005bf745812114dbc7458121005df7358121145dc7358121006f9601812102cff7518121024fe7518121004fd751812102cfc751812101cfe7418121004fd741812102cfc7418121014fe7318121004fd731812102cfc73181210067f53181210067d5318121006ee2118121036ec211812102efa2018121036f92018121014ff7658e4001dbc7458e4002edc6358e401379e4358e40004ff7558e40024fe7558e40004fd7558e40024fc7558e401367f5358e40136be4358e40136de4358e400eedd4358e40136bc4358e40004ff7258e4000cfe7258e4000cf
  | 20 => 0x4ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e2101cfe7458e2101cfc7458e21006df7358e2115e7f5358e21176df3258e21176dd3258e2100cfc7158e2115edc3158e21004ff7058e2102cfc7058e210067f7654e210067e7654e210067d7654e210067c7654e210067f6454e2120e7e6454e210067d6454e2120e7c6454e212cd7f7354e2116f5f7354e2115e7f6354e210167e6354e2115e7d6354e210167c6354e212076e7254e210076d7254e212067d6254e213776f4254e212076c4254e212076e3254e212067e6154e212076f2154e21207772154e21207742154e212076c2054e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21006bf6450e2101ebc6450e21005ef7250e2100dec7250e21167af4250e2115def764ca21016ef764ca21014ef764ca2136def754ca2136ded754ca21165ee744ca21165ec744ca21006ef644ca21006ed644ca2100def734ca2100fcf734ca21016ee634ca2115fce634ca21007cd634ca21016ec634ca2115f6f534ca2115f6d534ca21005ef714ca21007e7714ca21007e4714ca2100eee614ca2100fe6614ca21005ec704ca2100cff769062101cfe769062100cfd769062101ebe6490621006bd649062100dee7290621005ed7290621364ff76506210057f755062116d7c7550621006bf645062101ebc6450621165ef725062100dec7250621167af425062100cff768c621014fe768c62100cfd768c621165be748c621005bd748c621016de638c621006dd638c62100dee728c621005ed728c62135cff764c62100dee724c62115fd4314c62116d7e75d82210057d75d8221006fb609822102cff7598221024fe7598221004fd759822102cfc759822101cfe7498221004fd749822102cfc7498221014fe7398221004fd739822102cfc73982210067f53982210067d539822102efa2098221086f92098221005bf7458221165bc7458221004ff7558221024fe7558221004fd7558221024fc7558221004ff7458221006bf7458221004bf745822101cfe745822101cfc7458221006bc745822101cbc7458221004ff7358221014fe7358221014fc73582210067f53582210067d5358221066ee5258221006ed5258221066ee3258221006ed3258221066fa2058221066ec2058221165be7418221005bd7418221006f9601822101cfe76d912114ebe64d9121004ff75d9121024fe75d9121004fd75d9121024fc75d9121006bf54d912114ebc54d9121014fe73d9121004fd73d9121014fc73d91210067f53d912114ebf43d91211bcff72d91211bcfd72d91211bebf42d91211bebd42d912100cfd71d912114ebf41d912102cfe70d9121004fd70d912114ebc40d91210057f75591211557c755912114ebc6459121365f77159121004ff75591210067f755
  | 21 => 0xe62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893115e7f53d893115e7d53d8931176ee52d8931006ed52d8931006ef42d8931176ec42d8931176ee32d893115eed32d8931014fd71d8931176ef21d893102cfe70d8931004fd70d8931176ec20d8931176ec6258931385f77158931004ff7650931004fe7650931004fc765093101ebe6450931006bd6450931005f77150931005f4715093137cfe769053101ebe6490531006bd649053101cff7650531014fe76505311acfd7650531014fc76505310057f75505311857c7550531006bf645053101ebc6450531005df7350531015dc7350531005ef7250531175ec72505310079e748c5310079d748c531015de718c531017d6718c531016df618c531017d7618c531004ff75d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d81310a67f53d81310a67d53d813100cfe72d8131004fd72d813100cfc72d8131006fb40d8131006f840d81310a6fa30d8131006fb60981310057f75581311857c7558131005bf745813117dbc7458131005ef7258131175ec725813117dbe7418131005bd7418131006f9601813102cff7518131024fe7518131004fd751813102cfc751813101cfe741813102ebe741813101cbe7418131004fd741813102ebd7418131004bd741813102cfc741813103e7f531813103e7d531813100cfe7218131004fd721813102cfc721813102ef57118131006de311813103edc3118131006fb401813102ef8401813102efa301813103ef93018131166be64d9221355f671d9221004ff75d9221024fe75d9221004fd75d9221024fc75d92211a4fd74d9221014fe73d9221004fd73d9221014fc73d92210067f53d9221166bf43d9221006ed72d9221166ef42d92211beec42d92211beee32d9221354fe71d9221006f671d9221166bf41d922102cfe70d9221004fd70d9221166bc40d922101cff7659221166bc645922100dec7259221167af4259221004ff7559221024fe7559221004fd7559221024fc7559221006bf7459221004ff7359221014fe7359221014fc73592210067f5359221006be4359221166bc4359221166ef72592211a6bf4259221166ef42592211a6bd42592211a6ec42592211a6ee325922100cfc7159221166bc4159221004ff705922102cfc7059221166bf4059221165be74d8e21005bd74d8e2115ede63d8e2134df671d8e21004ff75d8e21024fe75d8e21004fd75d8e21024fc75d8e2101cfe74d8e21006be74d8e2101cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e2101cfc74d8e21174fd73d8e2115e7f53d8e21006ed72d8e2134cfe71d8e21006f671d8e2102cfe70d8e21004fd70d8e21014ff7658e2115edc6358e21
  | 22 => 0x9231006bd7059231006bc7059231006bf5059231006be5059231006bd5059231006bc50592311aebf30592311aebe30592311aebd30592311aebc3059231006bf2059231006bc2059231195be74d8a31005bd74d8a31006be64d8a31006bd64d8a3118eee62d8a31395f671d8a3100cff7658a31006be6458a31006bd6458a3118eec6258a31004ff7558a31024fe7558a31004fd7558a31024fc7558a31004ff7458a3101cfe7458a3101cfc7458a311467f5358a311467d5358a3118eee3258a31146ed3258a31014fc7158a3118eec2158a31004ff7058a3102cfc7058a31004ff7650a31004fd7650a31004fc7650a3101ebe6450a31006bd6450a31005f77150a31005f47150a31014ff769063101cfe7690631014fd769063101ebe6490631006bd6490631015de7390631005dd739063138cff76506310057f755063119d7c755063101ebe64506311aebd6450631005ef725063118dec7250631195be74d8231005bd74d8231006be64d8231006bd64d8231006be6498231006bd6498231006fb609823102cff7598231024fe7598231004fd759823102cfc759823101cfe7498231004fd749823102cfc749823108e7f539823108e7d539823100cfe7298231004fd729823102cfc729823102ef6719823102efa309823108ef930982310057f755823119d7c7558231006be6458231006bd6458231004ff75582310067f75582310047f7558231024fe7558231004fd7558231024fc75582310067c75582310247c7558231004ff745823101cfe745823101cfc745823106e7f535823106e7d5358231004ff725823100cfe725823100cfc725823106efa305823106edc3058231195be7418231005bd7418231006be6418231006bd6418231006f9601823101cfe76d913117ebe64d9131004ff75d9131024fe75d9131004fd75d9131024fc75d91311c4ff73d91311c4fd73d91311c67f53d91311c67d53d91311c6bf43d91311c6bd43d913100cfe72d9131004fd72d913100cfc72d9131014fd71d913117ebf41d913102cfe70d9131004fd70d913117ebc40d91310057f75591311857c755913117ebc6459131005ef7259131175ec725913138df77159131005fb7059131005f87059131004ff75591310067f75591310047f7559131024fe7559131004fd7559131024fc75591310067c75591310247c75591311c4ff7459131006bf74591311acff7359131006df73591311ae7f53591311ae7d53591311aebe43591311aebc4359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec725913117ebf425913138cff7159131006f7715913117ebc4159131004ff7059131006fb7059131004fb705913102cfc7059131006f87059131004f8705913117ebf405913100cfe76d8931176e
  | 23 => 0x67f65981410067c65981411a5ee7298141005ed7298141006ef6298141006ec6298141006fb60981410057f75581411b57c75581410067f65581410067c6558141005df73581411addc7358141005ef72581411a5ec7258141006ef6258141006ec62581410067f65181410067c6518141006ef6218141006ec6218141006f9601814102cff7518141024fe7518141004fd751814102cfc7518141014fe7318141004fd731814102cfc73181410067f53181410067d5318141006be4318141046bc431814100cfe7218141004fd721814102cfc7218141046bf4218141006bd421814102ef57118141006be4118141046bc411814102ebf401814102efa4018141046f94018141006fb301814102ef83018141196be64d923137df671d9231004ff75d9231024fe75d9231004fd75d9231024fc75d92311acfd74d9231006dd73d92311c67f53d92311c67d53d923100cfe72d9231004fd72d923100cfc72d923137cfe71d9231006f671d923102cfe70d9231004fd70d92311acbd7699231006bf6599231006be6599231006bd6599231006bc659923138ebd639923138f3f539923138f3d5399231006be6299231006bc629923138ebe619923138f9f319923138fb7319923138fb4319923138f9c309923101cff76592310057f755923119d7c7559231196bc6459231004ff75592310067f75592310047f7559231024fe7559231004fd7559231024fc75592310067c75592310247c7559231006bf7459231006bf5459231196be5459231006bd5459231196bc54592311ae7f53592311ae7d53592311aebf43592311aebd4359231004ff725923100cfe725923100cfc7259231196bf4259231006be4259231196bc4259231014fc7159231196bc4159231004ff705923102cfc7059231196bf4059231196bc405923138dbf7659231196bf765923101cbf76592310073f75592310073c7559231006bf6559231006be6559231006bd6559231006bc65592311af3f53592311af3d5359231006be6259231006bc62592311af9f31592311afb731592311afb431592311af9c3059231006bf75592310063f7559231006be7559231006bd7559231006bc75592310063c75592311aebf73592311aebe73592311aebd73592311aebc73592311aebf53592311ae3f53592311aebe53592311aebd53592311ae3d53592311aebc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006be5259231006bd5259231006bc52592311aebf32592311aebe32592311aebd32592311aebc3259231196bf71592311aebe71592311aebc7159231006bf5159231006be5159231006bd5159231006bc51592311aebf31592311aebe31592311aebd31592311aebc3159231006bf2159231006bc2159231006bf7059231006be705
  | 24 => 0xc65d8941007af74d8941167ac74d8941006ef63d8941006ee63d8941006ed63d8941006ec63d89410076f53d89410076d53d8941007ae43d8941167ac43d8941167e741d8941167ac41d8941167e441d8941167af40d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941166ef74d89411a6ee74d8941166ec74d8941166ef54d8941166ee54d8941166ed54d8941166ec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d89410066f53d8941006ee53d8941006ed53d89410066d53d8941006ec53d8941166ef43d8941166ee43d8941166ed43d8941166ec43d8941166ef71d89411a6ee71d8941166ed71d8941006ef51d8941006ee51d8941006ed51d8941006ec51d8941166ef41d8941166ee41d8941166ec41d8941006ef31d8941006ec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef50d8941006ee50d8941006ed50d8941006ec50d8941166ef40d8941166ee40d8941166ed40d8941166ec40d8941006ef30d8941006ec30d89410057f75589411b57c75589410067f65589410067c65589411a6ec62589413b5f77158941165ee76189411a6ee7618941006ef65189410076f65189410066f6518941006ee6518941006ed6518941006ec65189410076c65189410066c65189411a7ae74189411a7ad74189411beef6418941006ef6318941006ee6318941006ed6318941006ec63189410076f53189410076d5318941007ae43189413afac4318941366ef61189413afe741189413afac41189413afe441189413afaf40189411a5bc765094100ebc765094100cbc76509410073f65509413a73c65509411adbe73509411adbc7350941006bf63509413a73f53509410073d535094101dbf725094101faf7250941007af625094100ebe625094100ebc62509411a7ac625094100eac62509411a7ae3250941007b77150941005bc7150941007b47150941005b4715094101ebf615094101fb76150941005bf7050941004ff764c941004fe764c941004fc764c9410067f654c9411de7c654c941005bf744c94101dbc744c941006ef624c94100eec624c941007ad424c941005f7714c941005f4714c9410073f659054139f3c65905411adbe73905411adbc7390541006bf639054139f3f53905410073d5390541005bd7290541007af6290541007ac629054101dbe719054101fb6719054101ebf619054101fb76190541005bd70905410067f65d81410067c65d8141006ef62d8141006ec62d8141004ff75d8141024fe75d8141004fd75d8141024fc75d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d814100cfe72d8141004fd72d814100cfc72d81410aefa40d8141006fb30d8141006f830d81411b57e75981410057d7598141
  | 25 => 0x8241006f960182413cd7e76d95411b67e76d95410247e76d95410057d73d95410067e63d95410067c63d95410073e43d95413c73c43d95410067e62d95410067c62d95413c73f42d95413c77741d95413c73c41d95413c77441d95413c73f40d95413c67f74d95413c67e74d95413c67d74d95413c67c74d95410067f73d95410067e73d95410067d73d95410047d73d95410067c73d95413c67f43d95413c67e43d95413c67d43d95413c67c43d95410067f72d95410067e72d95410067d72d95410067c72d95413c67f42d95413c67e42d95413c67d42d95413c67c42d95410067f32d95410067e32d95410067c32d95413c67f71d95411b67e71d95413c67d71d95413c67c71d95413c67f41d95413c67e41d95413c67d41d95413c67c41d95410067f31d95410067c31d95410067f21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d95413c67f40d95413c67e40d95413c67d40d95413c67c40d95410067f30d95410067c30d95410067f20d95410067c20d9541014fe76d8d411b57c75d8d410067f65d8d410067c65d8d4101dbe74d8d411aede63d8d411af9e43d8d41004ff75d8d410067f75d8d41024fe75d8d41004fd75d8d41024fc75d8d410067c75d8d410247c75d8d411ae7f53d8d411aebe43d8d411aede43d8d41196dd43d8d411aebc43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d41196bf42d8d4101cfd71d8d41196bc41d8d411aedf31d8d4102cfe70d8d41004fd70d8d41196bf40d8d411aedc30d8d410057f7558d411b57c7558d410067f6558d410067c6558d411aedc6358d41005ef7258d411a5ec7258d413bdf77158d41005fb7058d41005f87058d410067f7654d410057e7654d410067e7654d410047e7654d410067d7654d410057c7654d410067c7654d410047c7654d410073f7454d4120f3c7454d411c67f6454d411ad7f7354d411b75f7354d411ae7f6354d410167e6354d410167c6354d411af3e4354d411af3c4354d412067e6254d412067c6254d412066c6254d4120f3f4254d41007777154d41007747154d4138e7f6154d4120f774154d4120f3c4154d4120f744154d4120f3f4054d4100cfe76d89410067f65d89410067c65d89411a6ee62d8941004ff75d8941024fe75d8941004fd75d8941024fc75d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d8941006ef52d89411a6ee52d8941006ed52d89411a6ec52d89411a6ee42d8941166ed42d8941006ef32d89411a6ee32d89411a6ec32d894101cfd71d89411a6ef21d894102cfe70d8941004fd70d89411a6ef20d89411a6ec20d89411a5ee76d894100cee76d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ed65d8941006ec65d89410076c65d89410066
  | 26 => 0x4fd74d813201cfc74d813200cfd73d81323067f53d81323067d53d8132014fd72d8132004fe71d8132004fd71d8132006fb50d8132006f850d8132306fa30d81322d6fa20d8132006fb60981320057f75581321dd7c7558132005bf74581321d5bc7458132005f77158132005f471581321dd7e75181320057d7518132006f9601813202cff7518132024fe751813202e7e75181320247e7518132004fd751813202e7d75181320047d751813202cfc751813201cfe7418132004fd741813202cfc741813200cfd73181323de7f53181323de7d5318132014fd721813202eed7218132004fe7118132004fd71181322aeec2118132006fb501813202ef8501813202efa30181323def9301813202eef201813202efa20181322aef920181321c6de63d8e413d5f671d8e41014ff7658e411c6dc6358e41004ff7558e41024fe7558e41004fd7558e41024fc7558e411c67f5358e411c6de5358e41006dd5358e411c6de4358e4117edd4358e41004ff7258e4100cfe7258e4100cfc7258e4101cfc7158e411c6dc3158e41004ff7058e4102cfc7058e410067f7654e410067e7654e410067d7654e410067c7654e411ae7d6454e411c57f7354e411cf5f7354e410167e6354e411c75e6354e410165e6354e411c67d6354e410075d6354e410065d6354e410167c6354e411c73f4354e412067e6254e412067c6254e41007777154e41007747154e4137e7e6154e4120f3f4154e4120f774154e4120f744154e4120f3c4054e411c5bf7650e41016bf7650e41014bf7650e4101dbf7350e4101f9f7350e41016be6350e411c79e6350e410079d6350e41016bc6350e411c73f5350e411c73d5350e41005bf7150e41007b77150e41007b47150e4101ebe6150e4101fb66150e41005bc7050e411beee62d8a413adf671d8a4100cff7658a411beec6258a41004ff7558a41024fe7558a41004fd7558a41024fc7558a41004ff7358a41014fe7358a41014fc7358a410067f5358a410067d5358a4114ebf4358a41006bd4358a411beee4258a4114eed4258a4101cfc7158a4114ebf4158a411beec2158a41004ff7058a4102cfc7058a4114ebc4058a41004ff764ca41004fd764ca41004fc764ca4100eec624ca41005f7714ca41005f4714ca41006fb609824102cff7598241024fe7598241004fd759824102cfc7598241014fe7398241004fd739824102cfc73982410067f53982410067d539824100cfe7298241004fd729824102cfc729824102ef6719824102efa4098241096f94098241004ff7558241024fe7558241004fd7558241024fc7558241004ff7358241014fe7358241014fc73582410067f53582410067d5358241076bf4358241006bd4358241004ff725824100cfe725824100cfc7258241076bf4158241076fa4058241076bc405
  | 27 => 0xf41185423aef54118542356f5211854202cfe7018542004fd70185423aebc4018542004ff75d8142024fe75d8142004fd75d8142024fc75d814200cfd74d81422debd74d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d8142326bf43d8142006bd43d814201cfd72d81422deee32d8142004fe71d8142004fd71d8142326bf41d8142326fa40d8142326bc40d81422defa20d8142006fb60981420057f75581421ed7c7558142005df73581421e5dc7358142005f77158142005f47158142006f9601814202cff7518142024fe7518142004fd751814202cfc751814200cfd7418142014fe7318142004fd731814202cfc73181420067f53181420067d531814201cfd7218142004fe7118142004fd711814202efa4018142406f9401814202efa20181422b6f9201814201cfe76d91321d6be64d9132004ff75d9132024fe75d9132004fd75d9132024fc75d91321f4fd74d9132006bf54d91321d6bc54d913200cff73d913200cfd73d91323fe7f53d91323fe7d53d91323febf43d91323febd43d9132014ff72d9132014fd72d91323eebf42d91323eebd42d9132004fe71d9132004fd71d91321d6bf41d913202cfe70d9132004fd70d91321d6bc40d913201cff76591321d6bc64591323e5df73591323f5ef7259132004ff7559132024fe7559132004fd7559132024fc75591323ecff7459132006bf74591323e4ff7359132006df73591321e67f53591321e67d53591321f4ff7259132006ef7259132004ff7159132004fc7159132004ff705913202cfc7059132015ec765093201eec7650932014ec765093200def745093200faf7450932007af645093201eee645093201eec64509321d7ac6450932007cf7350932015ee7350932015ec73509321e7cc735093200eef635093200fcf63509321e76f53509321e76d53509321e7af43509321e7ad4350932005ec71509321d7af4150932005ef70509321d7ac40509321dd7e75d85320057d75d8532004ff75d8532024fe75d85320067e75d85320247e75d8532004fd75d85320067d75d85320047d75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853200cfd73d85323867f53d85323867d53d8532014fd72d8532386ed72d8532006f751d8532006f451d8532386f631d853235ef621d853235eec21d853202cfe70d8532004fd70d85321d5be7498532005bd7498532006f76198532006f56118532004ff7518532024fe7518532004fd7518532024fc751853201cfe7418532004fd741853201cfc741853200cfd73185323967f53185323967d5318532014fd7218532006f75118532006f45118532396f5311853234ef5211853202cfe7018532004fd7018532004ff75d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132
  | 28 => 0x854302cfe70d8543004fd70d85433bebf40d8543006f761985430057f75585431fd7c7558543005ef72585431f5ec7258543005fb7058543005f87058543006f56118543004ff7518543024fe7518543004fd7518543024fc7518543014fd741854301cfd731854337e7f531854337e7d531854300cfe7218543004fd721854300cfc72185433d6f5411854337ef5311854302cfe7018543004fd7018543004ff75d8143024fe75d8143004fd75d8143024fc75d8143014fd74d814301cfd73d814330e7f53d814330e7d53d814300cfe72d8143004fd72d814300cfc72d8143004fe71d8143004fd71d814332efa40d814330efa30d8143006fb6098143005f67118143005f57118143006f9601814302cff7518143024fe7518143004fd751814302cfc7518143014fd741814302ebd741814301cfd73181432fe7f53181432fe7d53181432febe43181432febc431814300cfe7218143004fd721814302cfc721814341ebf4218143004fe711814302ef67118143004f67118143004fd711814302ef57118143004f5711814341ebc411814302ebf401814302efa401814341ef9401814302efa30181432fef93018143014fe76d8d421e6de63d8d42004ff75d8d42024fe75d8d42004fd75d8d42024fc75d8d4200cfd74d8d421e67f53d8d421e6de43d8d42416dd43d8d4201cfd72d8d423e6df32d8d42004fe71d8d42004fd71d8d4202cfe70d8d42004fd70d8d421e6dc30d8d421e6dc6358d4240def7258d420067f7654d420067e7654d420067d7654d420067c7654d422067f6454d422cd7f7354d421ef5f7354d421e67f6354d420167e6354d420167c6354d421e73f4354d422067f6254d4220f6f4254d422073e4254d422073c4254d422076c4254d422076e3254d4220f3f4154d4220f3c4054d4200dbc7650d42016bc7650d4200cbc7650d4201dbf7350d4201f9f7350d420079f6350d42016be6350d42016bc6350d421e79c6350d421e73f5350d421e73d5350d42007af7250d4200dbe7250d4200dbc7250d421f7ac7250d4201ebf6250d4201faf6250d421f7ae3250d42005bf7150d42005bc7050d42004ff75d8542024fe75d8542004fd75d8542024fc75d854200cfd74d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d854201cfd72d8542006f751d8542006f451d85423b6f641d8542366f621d854202cfe70d8542004fd70d8542006f761985420057f75585421ed7c7558542006f56118542004ff7518542024fe7518542004fd7518542024fc751854200cfd7418542356bd7418542014fe7318542004fd7318542014fc73185420067f53185420067d53185423aebf4318542006bd431854201cfd72185423aeef4218542356ec4218542356ee3218542006f75118542006f451185423aeb
  | 29 => 0x57f72585532057e72585532057c72585530077761585530067e61585530057f70585530057c705855346d7e761855320d7e74185530057d741855320d7c74185530067e64185530067c64185530257f73185530157e73185530257d73185530157c73185534567f63185534675f63185532057e72185530057d72185532057c72185530067f62185530067d621855345d7e71185530067f61185530077661185530067d61185530077561185534577631185534577531185530077721185530077421185530057e70185530057d701855320d7e74d81530057d74d815320d7c74d81530257f73d81530257d73d815343e7f63d815344f5f63d81532057e72d81530057d72d81532057c72d81530067f62d81530067d62d81530057e71d81530057d71d815343f7a30d815343f7930d81530077b20d81530077820d81534457d769815320d7e74981530057d749815320d7c749815342d7d73981530075d73981530f55d739815342e7f639815310f5f63981532057e72981530057d72981532057c72981530067e62981530067c62981530057e71981530057d71981530067e61981530067c61981534257e70981530067f60981530077b60981530057f74581530073f74581530053f745815320d7e745815320d7c74581530073c745815320d3c74581534457f73581530075f735815310d5f73581534467f63581530f75f63581530057f72581530076f72581530056f72581532057e72581532057c72581530076c72581532056c72581530067f62581530067d62581530057f71581530077771581530057771581530057c71581530077471581530057471581530077b60581530067e605815343d7e761815320d7e74181530057d741815320d7c74181530257f73181530157e73181530257d73181530157c73181534267f63181534375f63181532057e72181530076e72181532056e72181530057d72181530076d72181530056d72181532057c72181530067e62181530067c62181530057e71181530057d71181530067e61181530067c611815342d7e70181530067f60181530077a60181530067d60181530077960181534277a30181534277930181530077b201815300778201815300cfe76d89431f6ee62d8943004ff75d8943024fe75d8943004fd75d8943024fc75d8943014fd74d894301cfd73d89433f67f53d89433f67d53d89431f6ee42d89431f6ee32d8943004fe71d8943004fd71d89431f6ec21d894302cfe70d8943004fd70d89431f6ec6258943004ff75d8543024fe75d8543004fd75d8543024fc75d8543014fd74d854338ebd74d854301cfd73d854338e7f53d854338e7d53d854338ebe43d854338ebc43d854300cfe72d8543004fd72d854300cfc72d85433bebf42d85433bef641d85433bebc41d854338ef631d
  | 30 => 0xb00000000160050028058000000000002800a00900080000000030000008000007000000003c00700180040000050000004000009000000c00e00900100000060290008004004000000000000800000a800c00000b00800000020000010000002005006802800600400180000040000040020016002003800c0040054cd7e76d91534a57d74d915320e7e64d915320f3e64d915320e3e64d915320e7c64d91530257f73d91530157e73d91530257d73d91530157c73d91534b67f63d91534c75f63d91534b73f43d91534b73d43d91532057e72d91530057d72d91532057c72d91530073e42d915320f3c42d91530057e71d91530057d71d915320f3f41d91530057e70d91530057d70d915320f3c40d91534bd7f76591534b57f74591530073f645915320e7e645915320e7c645915320f3c64591534a57f73591530075f73591534ad5f73591534a67f63591531ff5f63591530057f72591532057e72591532057c72591530057f71591530057c71591530057f70591530057c70591532057e76d895320d7e74d89530057d74d895320d7c74d89530257f73d89530157e73d89530257d73d89530157c73d89534967f63d895349f5f63d89532057d72d89532067e62d89532076e62d89532067c62d89532076e32d89534976d32d89530057e71d89530057d71d89530057e70d89530057d70d89532076c20d89532057f76589530057f74589530073f74589530053f745895320d7e745895320d7c74589530073c745895320d3c74589534857f73589530075f735895348d5f73589534867f63589531df5f63589532057f72589530076f62589532067e62589532067c62589532076c62589532066c62589530057f71589530077771589530057771589530057c71589530077471589530057471589532076c21589530057f70589530077b70589530057b70589530057c70589530077870589530057870589532076f205895320d7e74d85530057d74d855320d7c74d85530257f73d85530257d73d855346e7f63d855347f5f63d85532057e72d85530076e72d85532056e72d85530057d72d85530076d72d85530056d72d85532057c72d855346f7631d855346f7531d85530077721d85530077421d85530057e70d85530057d70d85534757d769855320d7e74985530073e749855320d3e74985530057d74985530073d74985530053d749855320d7c74985530067e64985530067c649855345d7d73985530075d73985531855d739855345e7f639855319f5f63985532057e72985530057d72985532057c72985530067f62985530067d62985534557e71985530067f61985530077761985530057e70985530057d70985530057f745855320d7e745855320d7c74585534757f73585530075f735855319d5f73585534767f63585531875f6358553
  | 31 => 0x2004000801400e00a00b000000200100000000000000050000002000000804c0000000038000002000000000000200900c00000000010000000012000000001800200100380000160100060068004006000000000e00e0000020004001002801800c0000000090012006000000002c00301300040160070008000006001000000c00200600a0010000001002000c00c0000018040006001000000c010003002800c000001003000c00601000a80000120010018000014001000000c0000000040004000003003003000600400300000000000008058008003001801c03a00300200a8002003005802800000100180200200040000018028002000800000000100080100000020000004000000000802000e003000000c002000000000400000a0068010002000000002800000000300080140000018000000006005800000200000080140000010010004002002004000000e008003800c00601300000000100010008000004012000000403e002000800400000200180300040010010004000008002002c000004000801c00e0070008004002002000800000200600100080000010100010008005002001400200000000000160000000014006005000800800a00100a000000000500000000000000080044012002001000000000200e8004010007000800c006001001000400000000280000000000030000002003005000400e00100280000000040050000002001004800400200c001800003c002002800c006001004800c0000020018004000001000000800600700080080060000000014004003001800c00600000000000020020020000002004001800c0000010040008000000002004c016013005000c000007000800800400800f80040260070000004002002006000800200f000800800c0000008018000001005000c00000d0008010002006003000400a0000008018008007001000402a005000000401a0020108000000001004000000000300080080080190048008000007003800000a000003000c006000002800000a000000001c002002000000400400000100580000000028004004000001000c0000060000058000005000801400000300300000040010028010042003000000c01a00000100000160060000000004003000001c01c00c002000403c006000802400800c00200000100060008008008002000003803e006000000000200300300140060000000020012001000002c00e00000a00040020030010020004002000001800a000002000c01a0050000000000003002000000000600780000020010010000000003001000000000000e000c000004001000c0000180008008016018000800000200b000000000000100200000020010020010004001000000001a00400c800001a000001000c000002002002800000
  | 32 => 0x10090004006000000000400200000000100080040138000000004001000800000200100040000010000000000001003800c00c00000000240000000060000004005000000800e00500080000040040010004010013002800400a001008000000a00900080000000040000014012000001000000200100400340000020008038004000001000c000001002800c00200000680080000000008010000001000000000001b0018008000002000803000e00f00100040060020010004002004000800400000f006800000400000680240000040000000006000000002401200d0008014008004003000801a001009000400c000001800001600200200000000150000010000007001801c0000020008014002001004806c004008000800000400000000000180000000000006000009004400600100600000000010000008012003000802c0080000000000002000003800000000800500080000010068004004001004800400a01500000140080000010000008001001800c00400200900000080020048000000002000000003200000080000040020040008002007003804000e000001000c00600900180040340050010008000001002000c010002000001000e002012001800200d000000400a0000000008002019000000400e008001000000200b002000000000800080100020090010004030001000000801000100000100200000010008000000001800000401c001003000600200b0000004000000800000400500280000000000000000018008002801c00e0070000004000000008000400a00000000040000020018000000001000802c002007002802c0060010030000004001003800000200400100200000050010000012024003001000c007001006401800f0000024000000000001400000b000000000e0020020000000005005800c018006001000400000c00100040200000018004002000007000400800100080040020060000030000000001002c000003001000c006001000000402601000080640020010018040002003000000c00e028002801000000100000040000010010000012003000001c00600000080000060020098000000000000001c00a00300000000160000000000002016000001001200000580100060020000034000005001002c006001002800c0040000028014000000002001800c000000801800600200080000000010000048000000000000801a001005800400c0010000000002000005800000000c0008000002006001800401401a0010000024000000000c0060000000000008002001000400a00000200000060000000004050007001004c000001001003000e0000010008000000000004c00400000280000000010040000004001000000000400300400000000010018040000007000000c00c00000780
  | 33 => 0x319e8e000241e4e08fe43c6018c34f800000016381510988000023e0318000462905c1ba03467ca800000014b020600007130608a0511f800000000491f4800000000000000000000000017c693f11ca70b1e369ad81cca3e24ea2238000626000000024180c4154a46a1eb45f89cf60001b7211d8b7c632121417c869c2fa9df4a39a8f63628c200c3846a644938c000000000023f029719e60cba3763e1960e05c800000013486d500006ab800047c05d8000000e3f98000000000049226f62490000000000000016d600021d400010c22b99e087f30f2c0000eca821984e99c94ae0000000000042800000000002068000192c7f698a800000002f781880000000000127200000002ac8000000000023b00001a600002ca1d6a85c000059d9c0e8a080008328000000251c868093291908f65049ce05a700008ff80f4729a40280180001f3275a109937667a255a76197d00000000002801c000011000004800000d005000000200100a80200000000068004000011000800000e0000000004002006000800000c00200100140160000008000000000002001800800400080000040090000064004009000000000000a003800400a00100000140000010010000012001000005802c005002802000801d00100000000070000018000005001001400601c0000010000003001001c04c000000000003000100300000000090000004002000000001c00200b0030014004000001001000000000180180060090028018002000004000c00200400080040000030008004004018000801001400b004001800200000400000020080018038002003000001800000000200000100040008008010013001800000400200280080040020010000000002001001000000d001800000c00500180240000010020000012004000002400000800100040280020010008018000001800801c0080008000000001000000000200500a001c00c00e00500000040010000004000002002005400e00100180000000000030000000001005001c004000005001802200300000000360050088038000004000000000600e0000020000002000800c0000030000000000005001802000a00300300140120060030008000001001000000000000300080040120040008000004002800400c006000000400200000100000000040038000004000001000800400600300000100000000008000001005002c002001000800802800c0018044006007000000c00e004000001c00000a0000004004000003000001200300d00bc0040000000000000014001006c0000050008018002000000800400e00200700100020000000000004000000002c004000003000c00800500980100000060010018004012005000800000600480080080010010014002000002800001200100100040000
  | 34 => 0xd3608b82c2000000013d00000001b80000000017f9cd680100000001c540000000000000088380008798000725800060b9072557192a14d8178a2f10662da24c809e20f20e91cd00001ed8818060200000001ab8bb084a000000004469e009368de160400019b687a8ddc7e6800009f98045981ef03d3277e73f800014697f09ee000052f93147efa4de59c94569420c6287b92ea18c21ca000232000007fa0000e525d100480989e32000000012f88fc9b29fc40001f4e61b0ce0234155a5db000000016e4000000000027dc50fa82c94a01320030e2889f09666460984a3723121c90ec800000009bf983c282972e06b03d400024962d2000040526789a31a9230d8bf8000034a77a83e6492800080a968c077800006c873e80f000000000006918c4e0001d642ac096ca3a0e267bd00000000aae0198000586800027427c42540a5400007dc27aa7225a9031ea4400000001a985ce283267c0b44754a6c69618c9a4181f5e526997266725f4660800004980007d98000000073456e0000000244442d085468793d8076800039580008f01f6821d83c48f395341da9cee40b0f3c00018d049422fc0c61c122f5a8c290b000075600000000a661bb0000a07000049e80000000c562c7957200002ec1891ae023980003788000000243c15b185c1d880008a80000a1b9ea47d697720000a9042180008ca0000000059a000000004e041c7c426bc57300000000d0c000000064f85925aa8c048d294c400026c09fb9a6645801c43300bac2e283e01d9a674288012c90e879065b889c1a4900e86f88f03b191da5900788046a5426c00bc8765a1e078b84b68880e4468090da000000028b8a2270f80da98c13be772909427282802008d604c700000000d56000000000009948e11ba8870a706158288a804271e78a882676999780220b328eb82d470d80009fe878c9e200000000000461943435e278a3d1268e0e10000000010e95895680000f6400000000000aba997800047011124ee1cdc00015fe17c0edc28c0000959a50a00012bc000000000003b05cd949069c800014923885471e7456e8702000000047510ec64e0000227a60600009f8000000000000bc00000000f20000885000093897406650ef42f084da8c224b88e3a1240000dc2000000058b164250288623418000000043865080f22ef80007ec80008c3162aa2d022453585807c28ef600b2920212178c22f13a651909388a6045634e874c71d83540dd954013490428c0800088c93e4000000092d96c45f8146a91981f64a5119e3d6a3a675382420eca330000000064f054261290b6876a46286e9cbe1eb000068e8000000134a000038a0001df60b197dc0001d1c00026227b6a59c322000014e090241d060428528480aaa80418f9582135203e000000086100008d580004551e562
  | 35 => 0x610c2c5aca34c0001a20000000000000008628ed60001a8a4ce11fe61680000000e4e00000005dd000090100ae25524d26bb0c8c0001a90000192400024262f91ece33320ec8720c748b1a5242b6225682c16087e381e811105be131a70c803870c1239a387d89f240000838000000058010a009e8cd230b8540a04a80ca1da746842800022923e09c080000000000000000000000002ec800037991d896092102b180006c217d6000000016c0000000120600000004e6800000000006271c4e0e8a64467225c8000278e0001e8873f207000009e87c700002bc923405b8000913846605d26da957000080c201a00013f40002792221129289ca51678306568ab26d0269a46e9bb273a6af82b825a1dbe102802a43588286278eba99a10541911d5c000000000017560000000000247222c000000000000000a7c8672618733807c000263494500000000000000000039a926e68d0000000210400019be000000035f161800000000000ac000000000b80bfa00000000f48c529178fea38b2058817840c00000008d60fd6000249e5a7800020a84f609380000000000000000000009c68c924da134019675200000000000232000001819ee273a06a96900344cb96a8000159c0002306000000044ba50c00000004d900000001b340000bd216724d8000215a3a580003f7263a316800000020e46fd8000a2b1ac04c3a34800000000001ec2000000044600004b700000720094000264072d000000022880001ec677e8eb015900004d9877261d93b40932038000000096d8000a3d1ad4000000000000000000d5e3f81d9073927c021c192e4301bac6bf1f926fa800060a201e981214c91223f800005b40cd00000000000000000000011649c7000008e80000000000000000004c009000000006aa18bc2e0a7ca47a129672c000000000009fe290e4b526a0000152c79b8bee8e48000992800068100007280e8a88d87ba62b8176298887a8fba24e14200004be9a264ea000071208123a20a584c207703739b7a51f80000bf1b76000000000012a44d608be0000ac4000000000017601e5800000006de00000008f8a2fe36b00003ae0d4c1688000443800053c171469208300000000000000000000004cd8000000284aa08900c645290c03525f20008cd41151e426d0050c568832c86d92ce2af12fc19880005e680006470e7a5e586968a324946ff00000000f541e800005ee97be000000095c8000457894464280007b3024000026281271a7c000125a6ae000001f972c000000081700002fb1dd02f680009680fb00d4800050980004021758a2022e22e8000028a10a4000219400000000000930000000000000003060d6c00006a85fc8000000000061183880001db67cf000082328cc21a0170000033a000260c00001d45c82150000277285e8
  | 36 => 0x756000204c05f1ab000020d8230890000000003a4800084f00008a10d22881815e6af1b3c246096a0001f585ce8704000000000027bc5641f120001dd8000132800026a8000000000000000001f3885e06be000000000000002d8049073e80004e21cd897e996a02317988cd90d8000037200023e66b4000027b800083700008d700001ea04ea000165c76c219e5ef06387bf1bfe4f4a61e9c690dc8e688c072c80009718e2e7fd871e009800060d00006081c8008789080000000642046209680004222216000000000006720871eae3f8800026a87e20000000000000000000000001f604e2800048200000001b6c48704ec00000000ef8ffc9b98c6a431a4200c9a7c63479696000276e0fa800053622b4000108294625ca7b48000000122828e9200861a592000047ca36a31e6140000501000011924fa84b8f563c5000049980003ca866444a00000001ce22b7a7682e31f984afa2901cb931e0f00dd8802094a00016e67fe800047f26381eb80000000bfe00000006e39e72805800090d8e909b48acc1fc800053316f402c91c83ada2c26941c7e4df94c08a51a6e07d000087b00000002020309000067c922a9f08f1079f00003900000450000000001f000019b21ff11560001612000000000000001d20c7e1631d8e9eb800000000320001ac81f780000000cb600015960000000000216e000000000000b696fa676677162626c941e09d24560000b18000150a000000009a83440000ef200012645a2800072a25e0615861644f969a3b0027645316f683d8a2a0000cac23e1cc080620b8000000000000000001c340001d285b7000000023da564893e5be87b06971e4e26f11de20ca6de45727ba9308000000174e26e00003ac800038c0856000148a95307405d701564ec03305f296b0a2b945c1bc94e82e21a8000021f2088800087107764b9999e45ba8ea0fc26b41578286258800000013e0000000082a05684c280007819dec000224057c847470c00002590000000032265714a0000000045a0000000065800010240001832000000035424f45b2800003c217233e07c60000000792800019ea73200000000000e8010ca6e21f6800000006b20001fa815e9ade00000004a280002ada7cc2770a5e061a06c748000000021a217f05a000000000001a58311862c9ca097476c848835080000000000000000000000001618000000116637481ca304031600010eea2e977a74d800000000000000000222000000021764959bf019e000047b9776000245c60f8c72a361c5242e1e3e6009b0c7942372000049a8ea8bf475f0000a0c00000000000099957e63780000000000000291475c251e5fea4580a593c424427560001d940000714800800061800006d71d827f4000055380fe5c58000382848c16e168045c210c0001a6051e08e2
  | 37 => 0x46e10000000000050f038e8f60c149d38bf0537800074200000000000000015800013b600004ba00000001bf9e3c55f000035d029881ca8606d812c284793ea03496528509c6206a11621d100008fa1aaa00022ec14e8a6e0001ed400000001ed0000286a47a5b188008e0000000000000002096340178e70185b61738000000236200026d6000000079695de0000c3c0000a0400000003411c0200010645c41f74000231a8b5a8260000d72a3c037000019c02819fa6000019802780004e89adc661183a3759b9e1ef000068d84861dfa22c840a85448f9952427946e01286b824826dc0001c460238f580da81c26efa08467da2961b10b465d4089600485982701ff40000c8224d1eac20d82d69bd1c4a6dd000018c80000000000000000086001940001bb44a080000000202869a4225b21dba48900000e616280000000000000000000004e7a47e5d3000000000002bd924009780005880000000233c56a99fc099216c0db178a2fd9c40223221286c884e000000000015da000000000013e866b833e7a722ea000288c08c80000e680000fa0000977a25446423680000cf6000104400001ea00002d07be800077b8000000000000003667aa981c36200006e90e160eb9f266c61e5e39900003a6a9280001fc8000180a834111c29680002b28000000000000000002c51bd24dc80000000000102102a1a89b5000002a0000000028784cc0f09b4c707912a99b095214a80004b108427f7107e4c416920000cb8891800000000207328000322910231900003d000009b5224800000009288000000000064880002c280003840cb27bd80002f7000020380000000000000101670699aa0000000833000000017ea3c1902200015b40001c88000000013211360001cde7bb180e00000000001ca46f3209a00880000000000000204600000008e706d29688000263800092600007d0048259ba8b000000000a7800032e886e3e2225a00000003e8013c0000000483990200000007a3241622a8000000000080b206400002e200013ce2199be6758227e391800000000006eb93e2000000000008ea37d1ea833e8e8400000008241f2e000000004d0d34000000010615f000007b277998580001ee80001ff00d3000036e14e41708a8c21aa3cc543a50026b80de9fb181000000000001584a1c282871422d0263051200006f40828c581ca947c8bc95e49848000404800036d11ae23d05468e5a332855060e09f17705859d9a57b8eda1938bd47711f303d9981488983823db1e70504000000000007f280006f400005c496465f5010c38080000001fba03b0af49fc00000001602000000000000006988fcc00000009330000000000081e000000000005a603000001ce80001f064b20f6a00001d217e18709d921ce45080000000e36572911a8930000000
  | 38 => 0x14dc7e895c84b580000001284000000077e1fd4a281c6a000000003e80007c0800079b0d547d180000001bfa0000dfc0000d5a0001f0470221389ea00007768b9a8ff1e963730000000088a955913c8ea00002e01d0e000000000002122f990ae00015e82a4843e5110778a0da1828470e4281085ac41b031200000007a0859e5032636a270c3200008ce7070000956209e00000006b28000000064a58c1a2459597a055a92800000fb8694947003e16b6777872218480007870df8000126803a15c67fe000000013042d424680001b5824780005c9a1b48ba24bea1a9ee044b18ac00027e6000000049b000050902ea2dd8000000268a1721bd61299d9c16b80004aa812a032104a00014c25d4a1528c9a4b20cd85d4000262c3101afa5398000000000035a8000a29a4004ef00000000000028000043e0a24000000000000007bc8000000054e32600000000000000000099f91302ea873212a111e68b8bcc87d989455784e487a000000023c22fa170c5d08000029a6fa4060f7e1a68d0841d87603c39bca50e800084d87a66fc83fa27620d4000060c135800019d0000000000000026f800000001180000015875c0eb0dba000143800024b06230c0c1f4a4a41e501220ef0a9a9049bb657e800011423704130a4071e039e64c22e03fc85909538000071a6b030a8ce20a68e688b6a7de9aba36a3c804ac0c70ec47f08786000000035f994a0000000000241493d9cd4363a7e2a0628724f0a1fc7250106924000055906f604506a624280001a100001e792442ab0ef83128afc1e68000000000068a045240100007db122200010583a500000b21dce22ca6e80001de89c58c927270bd85258d9269a21064cc138480e800059501441e08f7400000000f381bea32800079aa8b67499288a410d8049d961c443000000001e25e086f80000e70a0f8eae9940000000000000000000001e042d79dc6000158a3cf953868f80001788fe8873005c8c8a85a417800033b00000001b68a0800004ce800000014fa0000000000103a00018a00000000a1a24d64541000000138e5b000000000000000000034380002131cba8b016a6000283a64592b076604360000ffa44ea12c122828c5520b044e91a6c1d6818215fa65668221161058b1a2af800000013867db82203bc26988101c9000024f875d94ea06aa7405f324323640000000000052d96da00024341b30ae2000000031e00004bfa32c000259a000000046f94f658e927ca04000021d00007a4a17c039800035880008949fb058f813a507141412d09a89ac9f8a000266e00018b819c28d6a1186a466480fc5c6014c0001dc26ab19d41b5a1fa000236e5c1a48c307128e053835882ca5d032727841438000000253825e9b9242f19fe8a1a7740000000145887e0000000a1880001338b9c2459a7
  | 39 => 0xea0000000000000064d949c00019e44ff91e400000008d9000011ca61a00000005a82682849a44c3be80001311152000014800025ba5b480008e800000001ffc65d00008b900001b1800074610286e510ca00020d27ba91e62ed053e8f4000000000000000000000000081993d600022cc00000003818a3242015625559ca23e611964cc98ec0001d84243a5ac225209227c07f401897fc11e1a5a611271485600001850d4032a90a6000000000025da00018dc0a48e7200025d63198000000000093911460000000000000000000002371666790000000000006e60000a1b000029200007f8109a46002f08438f3065301ee4ee81bc2e9a8e426904f289987f65c100000001b5e68f00002a6000000000009e515ec9d20e9e3590ad26f719c297619d0368800018400000000000000081a55d800000008fa1c815d06c880005e100007600b7a29189803b60f5e85397d245f000012b9f180000000683800054400006390000000103e0002654136000000000003cb8820393204893198ce9de8b422a8a92a02b10f46c080005eda02406d86b000008046a780004169a30000182600000000470d206d100002d0000076a07f000000002fc8dec100800000000000000cd0000000000000000000000000000047482720d912de65900001fe1efe636873067182348dea8860000000000132c0f2a91a62395540e7060a4239e186bf986a58893dc62682ce87927be00e0bcea3794d25f90396619a46c4c813c019180000000d2e000113400000006b3a3f24d4264e0001a14000000074d00008770c6000000000001d4c635253a268a72c2df8a764d880180000ca00f1a3e484c858e7c8800038380003e5800000015580670960999900650628be22d87520000750000000048c80000000000000000000011ce3728000000272a2450000000000000000000f30000902800013ea844000077a00000000000000000215600013f88cb800000000009310142000000078a0000852065a299118e000102e0000bba5b395f637a005a0000308545800000000004c59d140570cea510001e330a85ca0594300bb99fa5ee18f85fba5ec448a41c0140aa6398a2fa779139835ba802526032052892983692130130975a1a208ba5618e24228994472f1b4200022f05fd0000000000000000002bb000000010fe0000000000141a000000000014e09c38b86000263e000015a97a00000000aa0337800000007000001b907e9000000005dc000000000000007a6000031d951a33980005c21da210d2790025800000010e2014a4465291f903f6250e00008582d5a3f62a5857c58d8d68000173c5d985524a81b524b18b9e9a721684d323de46f267c00026c25b5000000000000000000000083c00000000000000000000000000006c105e68b7800032791588f200000e
  | 40 => 0xf9a0000000a079b660910ff63d7002e00002bc174804e8c502ae64022ae042906a00000009448d9e000110038c9d8a4fe80000001fb815c9ab68b4a6c86ee9b06547800018d0d3c00012f40000ab800013962c71f1e88f9bda7b28b2c000211800001d808985d60001e207b8800647580005198fba359a34692214080ad80008b10000000033c000000000a092810880001b40000000000000004c069d9c7a00009fc23805485da880885780000ca01922d4800096ba7ea00000000551faa70e800019ba89813f8b6a59401365db8000000000014f25dc4740b708c70f3a00000000000000000144e686116c7c81c749b30442000233810902dea2ca79666c20b60d406da00003146a9a3600d083069628000709924c0000b38000000000022b0658071299084de000253200000002ba055600000d8571269428d085c6f0a2a82f4000089a0dd06d280000001fde00000744428e7e11680006ea80009f68a120000000207266a3d8800056385aa7208fbe0b314ba19312a83af89068e9239082a97325cd220045227b42aaa4080000000000183098a94fe06d0fac5930b060ed897093b800000000003121e481700a7227d00006e6823c000000041a070e31f000000025a800000006cd800089108e860311dc3e8a7189b104a4140a75c8ae028204480003f526104b00852000172a89b0ee800020825c90f48000202200226ac0df1a7802e94ec425a5b28e612263f4102090910fc8ce94b28e194549e80e1e3bf87683210fda3a621f817e9f525ec88f20000d4800003de000236617d901023b96eca409b782cd016c8d08c6c00000003c2000045c9cc82662140092800000013020df968495f01fc83598d60000000787800056ba54653b9ccc52f23b62e1095c63da14675124bc9c4251000024e00f91a8248ea52e3868000000000002c0850000140e000078e01e0000000000000000000001be811380000000c168ef21e20000000000015000000000000000000098275d137042b07464bb0000000070a7cd80006c79d3c8d79f827e58000a3380000000000000000034a000039600008700000000000000025fea1f0d9400000002f0231082921de75515b638e8a26152a0b49cc145a00010d21869a64693000036c000000000000000694000000075c8000000000066b08d6000000000000006bd80006e295440000986822064890e15ea1f0800000007803150d58247135e382251a045a5c49419f800000f8e30e80000001dac0000000000000066808da3b88000000134043815f40000000a2500007e190620000ea400012ca0000a8a0000000921947657f089200000000000ad0000000041b80a85bc97b000000001b2a73641492527990bae4210000154000000000000000000000177800006c20c0800019f0000622a552000000000006
  | 41 => 0xa42428a62e0d225ce606000084699da5df0a3675e000000024d088617d863f0904000208e70819d87b78000038179400002008fb000038d2866935006a00000004e81f640a200007df265c000000057891741f816145d781a677f270861f8aa88140a3818803da9d50dc44ab21fe84403384229cec2d726145d9081e1cf18aa3c58d9c3f10000000170075a0000a3f235400024820000000000223a6950340121006c5129fa02d304309d40a80000168e27b0de430a05e00bd8578000000041e9c3295528c449c0000221a29220f9b2c9e6a82e7c6800013a01188988ece30c032495e94063c49bb2663097683380001a3942a000000032984fc70a9dbc7489c566a71e60054800082f19463f08000000291205e80007701a9489288ca0000356276923c17aa91e00027fe00015d2000000099682f4466a3000001306000000091f00000000b660001d0a2d921c6000000000000003bb00000e309e4000000065500004ad8e6e000000047310e61a787ee6a18ca23a39c2470000004c9000072600003fb16242a50d32000019e0ab27d47a2937400023c6000000000000000d6a0da000000000027200388e1407c89de00007fe2a392d283d00006858000101a4b400000000000a1c3e2999662d800000001ae6fe00000000dda7f980000e409e20001f7200018681f280a4a49968800002146b5a00a00001e4000000000027ce000019a6f78000000158c33b80005e982ca000000098807d85f6800056f00004f1986200019f8a488c5c00026ba00001283ff8000000050000012180000f2600019803c2862e7169bd484e83320041524629087288294167d7020e7df8000000220232b925433c800000015125d181e00000000000000000000000001dd4000000040e25642190ea013e026859d258c3830000000000000005ec48690320000000000145e609234400007ce0689ad8000209c1e880004070b3c000006e548087c21e03e214c00000000000000001432001e69638a503608ff429a1360000034e04fa0a20000a567759a4e76a94b854d80009a8914e92692a68c28fb221808e49bb88249cb97ce73e000054c80000000000471020c7ae98c066e0000000000045280002240000243000018700000000d1a82000002c4800025598646da9920565135490aa4aa92128ee0da246078903605278d104d08102982080c2a18a885f212904d39574a1f979c94991921a19ec081e804485700000db98b2751a4a04f221203a08b4e24b97c268694227b11e9e3458f686a3260a18604408f50e6629d11b800008980440b3e09210482dd1d62000100a0000f840000f04592000084d25c274c800000000006c280009510946a018c0a92e9b963570b108fe9f3a965982a00000009ec00000001e664919f3e00005da79d933e00000000000c0e2ef00000
  | 42 => 0x4da00003e080001568000a2225d20000000000000091080007cd00000000000000174a66f0c708e285bc20b9bce0001500395118c37c8cfe4cf0120000000084fa3b400000000001c64000000000028827f19c3c722a25c3fe049474093f207024309d60fca398084600028507dc00004b9000000028400001bc60000000336800000000002a11fea00000008308c6e5f111769f4109250b0000736a2bc0bfa77c86b8000386000000014420000a080000e762f81a88000000081398c450a21b08ca800010ba82a02d22760400e1c794a4706c6a76c973105059e1d1672ba222000061e15d80000000ea226d8c8e7d31e108d4107808d80007961eb200016440a280005df93000001c8c2c21a0058c9eb803900c2a10a686000197e9de056e4a31178678047e00023ba212883a1389f9416922ca09b84206baa4ac000139280995e089d00005cf8e5a54a9caa51c8b3a3089108000000051d1e0297c10f209b000012f136a47b000064105660000000000000011794487dd8000000000015c00c044800004eb0d966dc0d7a25e0b02632849e72e00580b01ae408c1ec83ea000072116580ee80000000be200000000001ea68eb000000012d042a97908398000366800065e80000000db6000137c68193ae000016a7ed92f62711a2c0000562488161e0c691ba7401e223df1f081d298b46a5a0ea00003f65b79bc049e273c1e90000000097200000000001d12397800003da0ac36ba3c47440c861ae8aee00014ca449a7624b880002be936c9a900008318000570000096d0254199a1f055c1194000239e71704043498806081987456b19ea7a195a8302126a0219bee08b1de24b324e869fa7ac2209d5e8f598ea4e01b2413b9a44283844850d8ace00000009e98000000066c6130b2a00018fa3258000000275e2ea1c287a891b466a0e741941b3213295801db1e909600000825000030680009e08000575a7b21b7000000000007fa000019d8a7a49706a03e500000001e3a6c8000000008ae6a880007ef037a5990506672953e32a0f1e70b9c5e00000008400284000000037b8000000000000002a6000000091e150c59a80003f2186e075830a00000002e514620001c180001e8483e26028a791b62670cb40001cc214b9b2a2c309260ea22d80001768000000005992308fd0afe0011f0ea4016e08df24ec71810e88df82167af0eaa31a1be2513179e04788de37009a01a316ea034058a3b98a446a8175483fa07c6d39fd219f800023318065b402467970000643279e70517b4273000083797de00000000000000000000000008ac0000000000000000000003c003aa4158b20000000000000000000ba463c000052a800000020ba02600008420000000000000000000000f1a63483dc00027c800021640001dae1ab03d85a5007a7f39ab42748
  | 43 => 0x14f25c686429a4136e1978d869ae03f21af09e65bb982c2ed80005928e220000f5036a00006c729067bb83a60960a3c0b701ce19828a45519ea09af9c9a7a68f52816802424482da00020be325252a34482e871c00001f9a45207e0000583269200000000000000441273888209d44cd00000948d2456fa204566984853d00004c89bb00fd099000000003c7202e33c11aa54c153a000283c6bd022882613523b5220c896208a39e00000000000a4228841bc1dc83ed074e000000081880000000000000000018987d467d18f20001b869d2927e0f5800000011e283ba23478d228e1fa000000011f4531a0127f61ee676480002759ac662109c2124904e0229e0e7848d4a000267a71600003c9122e6001dd2785280a01a1560a46225e000243e75b008081d27f483c28c06e808b800016ba00000001fa8000000123888e07d02800a0c2a70de095a00003ce2824000259800000004ff1a8e2b6a89a000126283a017e9100880536800095b00007ff8940000000005285220002036310996845125b853880002cb8000000000013823b070589f609c0cc665b1f846fd16344de082c0d89ee485d255ea190c123dc8a028c399c41950fa486b14c826c04b26b889fa7cb0e7c00021621df000067b00005988b000e516f89c48fd20a3894200012ae545168251403fc633189214d1bec0b9253e0000000684045c568103068a82fa000000000013128ef800000000007e3198a00016900000072000000000000d6000000000009ba00003b80001b625aba8560000ad41728000257800070e0eee00022be887800074e260e3f380008d0000061780000000000000000000021d200000002ad05ee00000007af8000000066800022f425f143200015ce7f90e3e2c3800000000001040000208800000000005c09286094000000000002a7921200000006e2000000000007d2800034aa0e200027e493f80004fc0ad663a000097d80000001f42000000011b0000058a41a5bf9bc400726ea11a0f8c00019a20000c063c0a5748311346a45a3527de0b966909e7a13c20544831e2636a80be86f1d564c60fc00029aee894000076e072c91a937a657a50459f80007a01786000195a0000d302e611a6000000052d16d842418d821b0dde00026325eb10404620d7607f81800001cf46ae800027f9e160000000000196268c800063f80365761e3073c018a74b99b400020fa2e494d000018803a98a608e3191e79e1aa40000c2678b000048b05880001b3a0000000000102687d000045e800000000000000164000000000022ee000153c1d09e9400000001b917f600028d46308eac0001e1a0000df600013f60fe0e5c69e82c4a289b7e9aaa6a60000000721800055b803e0001bbc0001cd20690da696aa5363b79d06335a616724885e0000ee000000008580000
  | 44 => 0xe0fb80000000000000000076913de75680004d5a1aa7fc800000000000000ebc0000000000000000005cc0000000470a0a08c60000000226400000003409518000187249611c63eb8aa45548d461c61da08aaa14a664157a98999586d9244a9301934838000024a8000441a4067989f56a49000081fa48a72da01436819d66b69c0c2f11198095a07604127fc43206ee2ff19a461e06b600018961ad00005969af0610873a0000ed0000000039b152e46c8b223881ad28690680000079894f000000000000aea4ce8128000000000098700003328000000000000000000000000979084000000002b2152800000000000000a318070000211473117880000000000229a000050400011ea5ad000000000004fb800000028085eb82908fa8000000000025200000000c3e0000000000041a14285a8674a4f20001a0c9a00b6c2de1a2274690be00000006e7000021680009ed8000000223ca160000000000000016ac8bd9fd60770e507620c5055980005230a1643e981a00011848d3a7d240f07aa73180001f9101a19a800000001d0780000000013da0000000000248e128842a4bca7a220d19ce890a0c899321129dd9f9e3111ba67ed0f3405a0c0245a800059795dc433897e4ec800037520341499948068198e12c047a00021d01a400000000000000000000000006f6000000000001d79fae000035e61e8f46000000000000008b3a60000012b8800255014c96bc15aa67000010a87b400005208f0c791000006e2382964035c6558bca1aa9d4a3a199de830000062228c877f8000570a2c80001a5600000000000260000174851a14580001df2000170a522051e000132a00003922cd8d2c00027046c5201c47c87840000a6c2b08600145044c3fba0fc4d68d1400000000001fee000000000000000001a121b802180ac000010509580dd0b8e1c580003cc800000000000000000000000059e911400018be00011a400008148f294f890405200000000011a12200000000000000000160686a0000000111681ba8e06c414fc0000dc8400894e00000000000adc29c0c7a426000064e800093700000000000000000089e0d0a000000000015d40001670773171c29298a60000000000000095da2a2000216681480000001e46197135c90a235a8e50eb40bc9a9a4c3004241188c438014945cc18860000a100058f424a6912472b14ac1b39b2879a0000000000000000007011fe279327e000002f82d280003610000000181690b81ec767809c0001822a14800030d06c000000009d097f882b8ce419018f4a42a40e7e719282dc8000000000085a9598a3f80000000000a2a00000b620329a200001d626ce1b6000077800003c8a1441b5120a00025789f582a20b99d42782960a86600765c899403dd89e01038000929959e5000e1214417aa6be
  | 45 => 0xcfc0001cea0000aea5bc245a204000093297fe29e00000000e041048fbc460800028b00003b307284bb98ba9d48000000221c1dd218c1b225ea0001ddc4f30f36584157841c0cd8000000002a8000363000035493d00000b5a59a26963ea80405d8873604ba76614728926c5899e3de800095011b000000000001c2218e8a185699c9e4bc181e1eda81a524a744000000088aa0a637a9f0c00003d000024f0641964e55416e200022800002652514a5bc1ee05c67ac00ee00005c400000005bf1b5a1db8d44803000076319707ca26f26cc07387411e7e16512d89b81f1601795f80c111f65b32798638a1b803399323db800029383ec27200009529d1e467101e1c714028a29a5e8ac9d667da80008db025c00026461ef800018f02b48b50000332000000021d800e9d303e48e4a00000005ba00001fb22f81f002b27de8b6207e86fc86580000e180006e880004f50f904ae85966f91c7c48104aaa2e0000000226a000062a4e4000001526fc9c923165e48cc400000006ee1f887d5079258b80004c9946c1818ff000025c027c97a20c30000000000060d9394644152600000ea000029c00000002f1929c33a21d605185a6063a5e22530000000000000000004d11b3e62080004c6800008416a2a1e25200000f9c0001a4034611e0000020874e800074a800053380ca1e702be4392304205800000000000000622000084418d8e8c000156c10e80a24f280003e9a8906e09f5085f9ef8a1e98ee2cc1fc02280000000000046884a000000001c4000011c05827108c00541000000000002a0a27a4680a7e262948400009220000000000226e59b142e16ea2300248e3ca23800000017e8998800000024765fb075469c2492903000074300000000000000009a00017e61d900002e40cdc10f12a20000000a3b15b024ea3745ca0a525798584719a4ae00000004be0000643800000000000001d6e7040c4c00000000000000000091a00000009d3010850819e21c691ac0001edc43500005ae000000027aa67327860000dc645fa5486f800000000000000124e9dc000071a00000002648112800060485f45f0256a000078a0001e54000000096992161b89b466241ce6317814095b80843f1998612600000000b5832f968665d84968e8a5f8a3c832a3a7163c000000043426240000000638000000004009620e2a000000089c000000000008b9800000015062c98652749021a0208000000000000000001778b165c3800000000000000000000000052a000000000003de0000000252233d24740000000000191a975054c00000007ad800000028e2754000000005d0000280000000009e300005c7800073c8ea88669b12a039f329fd8fde30784b88639b4826b004c74f8ee499605e88980682a348190000000055085e4815a5e6000000029a8db
  | 46 => 0xdbc3b4a6f077c05289a7a53000010b2811233e3ca02a49399b7c00022dc88b8c9015525345ea0cb0226a89e000041e8ec80000000000000115a0000000000000023f80000000d4e0000f8015627340000e3842c0030521800075f82048a925841f2000071115880000b6e0000ec2000006400000000000000000279c000000000000000000000000000032907d660200006e31c6e00008a8433000044c803c88425b064980006c98e4868295085b0800044409927fb07c4000284e0001db412022b61571ac254882a8000062894080000002334431257e00019501a297a400022ba33390f616c800000013e64eaa2244909c8e71b2570000000040d9a6a423000000005749b9000000011fa8649ac40001faca17800043a8db29f60f700000000a0e00002298f609b6148e9c9800000008d8000187c000000000000002bc1a4a0000000958046e08e00006151b0e41f23dc88a0d9880a22a6000000022d1966529a6846b9a664037183826692b48ee28346288ae466202944e70a4c3ba816074b197ca1324546b327a41c1896e55314609cf8d38666a8d02d5099600025fc06c037814b13ec43c1b2e3e7a4506db8a3ea2aa3d26539446137287492a167c37f80000000000631800000000004b800008641f4442e8c387c51f0000000000000fb626d042c1be80000000000702909c03100009a680006398efc00004584ba0b2400000000000000000000049780003d39b380b480006ac903475015a492003b402e291c0000df037e92022ee0ba29d800001460af800017806ba00000000000006a18826f800000000004878000000270a535127462c270008aa8fa56c893c9fa0d70000259e06ea7f20ff80003d298401b98000139a5949981998234a21a00019ba6a1000098f18524b6923697b80008a71ed6000252c2029bc800015020001d7a43780000000000000000078e092c498072625680cc687289600000000000cbc00000002b8000034700001c200006bc92b20000000000212a51e96be000276a0001c7200019a60e81138927129e00008d45201b5600
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa3d85cc1640401117d0f902c8080022f61f20590100061fa9ae9b182000c3d535d3630400b96e20ba6c6080172d44174d8c100047a40aeab1820058dc8754d630408347d093b2a6080028f6127654c100052ec1ceca982000a5f835d9530408347d083b2a6080028f6107654c1020537410eca982000a6d821d953040054bd07b22a6080029760f6454c100051ec34c8a982000e1e63991530408347f0cb22a6080038798d6454c100061fb9ac8a982000e1f7359153040054bf0cb1aa608003879916354c100070eb22c6a982004a5e8758d53040094b90eb1aa6080038d5937154c100072ab1ee2a982000a75861c55304001c6ac838aa6080039558c7154c1002c7c402eca1820058bc875914304001972c9b82860826b0f9d353d88100061eba6a7b102041c3e7454f620400187ae8a9ec40800b179cd53d88100062eb9aa7b1020058ec87549620400b17909bb284080021fe1576508100243e42aeca1020058bc87591420400355904b2284080032d59371508100047ac30e2a102000cb5641c5420400b1b90eb1a64080163b21d624c8100065ab26e299020008f5861c5320400196ac838a64080032e59170904103c61f326eaa082000c3f755914104001878eab2282080032b1c9645041016657326e4a082000cad64dc9410400117f0cba462081432d985748c41038c5fc3ac918820358bd87592310400b1df0eb1442080173a9c162884100ec5ec36e898020008be8759130040111790eb2260080030f99375480100061fbaac89002000c3c755912004001c6ea6b2620080172d5c164c40100071ab22a78802000e556354f10040058f2eca9c200800e2f21376440100061f326ea880200e8bd86dd1100400117d0eb2220080222f21d64440100061fbaac88802000c3c755911004001938e6b2220080032b1c964440100064f326e68802000c9d64dcd100400195cc9b9220080032b59372440100063a3aeec8802000cb784dd9100400196909bb220080031dd4f76440100063bbb6ea8802000cb776dd1100400196eec3a22008002ada1d64440100055a43ac88802000e37755911004001c68eab2220080038dd4d644401002e5bb82c88802000cd776dcd1004001d2ac9b9a200800335dd87344010006aa3a8e68802000e95641cd10040012e90ea9a20080031ddd953440100071ab22a68802000e556354d10040019ceedb922008003a9593724401000673bb0e48802000da4741c91004001d4ac83922008003711cc72440100063c3aeec8802000cbb84dd9100400197109bb220080031ed4f76440100063dbb6ea8802000cbb76dd11004001976ec3a220080032edda64440100065dbb2c88802000cdb76dcd10040019b6ec39a2008003661d073440100063dbb2a68802000ceb76dc910040019d6ec3922008003ac5926144010
  | 1 => 0xcedb1c6288003655d3638c510006d2ba6c518a2000ec463d8a31440019ccec3146288003695d0628c51000752320c518a2000ec46318a3144001970c9b8262880032e190704c5100066db18e098a2000c7476d953144001ca8c7b2a62880163d219744c51002cf8402e898a2000cb476d913144001d28c7b2262880032d1d8644c5100074a318c898a2011ad686dcd31440059a8edb9a628800ab5a1b634c51006e6a3b6c698a2000ce476d893144001d88c7b126288003391d8624c51000752320c498a2000ec4631893144001ba6e638262880033ad8870485100ae5b3b4832022000ce462dc5404400196ec838a808800339188715011002d5a43282a022005bb08050540440299aced18c60880030f1d3654c1100045f436e89822000c3f65dd13044001878cbba2608809b2718f744c11000656316e8982205f8be87d91304404d1790fb22608800327dd3634c1100064e3a6c69822000caf74d893044001958e9b1260880031d197714c11000672316e29822000c74651c530440019aec638a608800339188714c1100043f436ea9022000c3c64dd520440018b8c7baa40881731b18b75481102ec3f43eca902205c87c87d952044001cd041b2a40880030fdd764481100061e3aec89022000c5f75d8d20440018b8ebb1a40880031bdd76248110006363aec49022000cb464dc520440019a8c7b8a40880026d61071481100065a320e29022000cd4631c520440019cec438a4088003a619063c4110005d8c2463882200fc7676d96104401d96cedb24208800f2d9d86484110004dbc22e7082200dcd676d8e10440059acec31c20880039519463841100053a432a7082200cce676d8a10440039ccec3142088003a9190628411000762318c50822000a3e8598e640400147b0b31cc8080162fa1f54590100061fbaea8b2020058bc87551640400b17d0f21ac8080028fa1643590100051ec2c86b2020058be87909640400147d0b31ac8080028f61663590104d61fbb6a6b202000c3f759d5640400147d0b39ac8080028f616735901002d5c402e6b202000a3e851cd640400147b0a39ac808002aba08735901000556c10e6b202000e1f5394d640400156f02a9ac808002ad20553590100051fc2ae4b202000a3c855c9640400156902b92c8080032b5c872590100051f42e64b202000a3d85cc9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400155d05a8ac808002ab60b51590100071ba8ca2b2020088be87cc5640400117b0f98ac8080028fa1731590100051ec2e62b202000aae82cc5640400155b0598ac8080028fa1431590100051ec2862b202005aba800c564040015730018ac8080028fa1721590100051ec2e42b2020008be87085640400117b0e10ac8080178e94350590100051f42e60b202000
  | 2 => 0x631891000746320c63122000e4e8518c6244001c9b0a318c488003b1604631891000537436a63122000a6c86d4c62440018dceda98c4880038bd93531891000716326a63122000e4f63d4c6244001c98c7a98c4880029ba19531891000536432a63122000c6e7654c6244001c5ec8a98c4880038b191531891000727b1aa63122000e4c6354c62440090fd0bbb284880021f61776509100146f41eeca1220008dd83dd942440010ff0abb284880121f21576509100045fc22eca1220008df835d942440051b906bb284880023be0976509100047bc0aeca1220018be87d9142440071dd0fb1284880121fa17764c9100043ec2eec99220038be84dd9324400117b09bb264880021fe15764c9100243e42aec99220008bf845d9324400717908bb2648800237e0d764c91000477c12ec99220008f7815d932440031bd0fb1a648800a3ba1f624c9100071a326cb20a2003ab686d92414400196cedb248288003a519363905100072a328c720a2000e946418e41440014e90ca9c82881078d1915390510006aab9aa720a2000ab48650e4144001d48c9b148288003399d8629051000752320c520a2000ec46318a41440010fd0dbaa82881e30f19375505100062e31eeaa0a2000c6c62dd541440f30fd0fb2a82881e21f21f655051000636396caa0a2000e3441d95414400187eebb2282880030f1d7645051000656396c8a0a2000c5f75d8d41440018b8ebb1a8288003331cb635051000477436e4a0a2000c6f65dc941440018d8cbb9282880032bd93725051016656326e4a0a2000ccf63dc94144001998c7b9282881d63ba1f62505101647643ec4a0a2000c6f75d8941440018d8ebb1282880033618f70505100065db20e0a0a2000cd8631c141440f18e8edbaa82880031d1db65505100071a326caa0a2003cb476dd1414401d968edb228288003351db63505100066a3b0c6a0a2000e546518d4144001d28c831a82880029d219535051020e3a3b2a6a0a202cce476dc941440eb9c8ec3928288003591d47250510006723b6c4a0a2000ce4761894144001d48c83128288003b118c62505100055a43284a0a2003cb4765094144001ae6ea38282880036cdd07050510006f1b90e0a0a2000c3e74d9631440651790cba462880030fd95748c5100061e32ae918a2035c9c635d23144001958c4ba462880022fe1f648c5100745ec3ec918a2000c9e74d8e314400193ae9b1c62880032b9d3628c51000656ba6c518a2000c74659da3144001ca8c7b2c628826e6d61e748c51038f4a31ce918a2035e94635d23144001a6f0aba462880034d215748c5100069bb2ae918a2000d34655d23144099b28c6ba462881334dd4d748c5102669aa9ae918a20009b787d923144001d28c7b2462880026d61c648c5100074a318c918a2002ad686d8e31440019a
  | 3 => 0x1b122000ae6810c362440090fd0dbaac4880031b18b75589100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400187ecbba2c4880030f197745891000656316e8b1220008be87d91624400187eebb22c4880030f1d764589100064e39ec8b1220008be87191624400187eea322c4880030f1d464589100064e398c8b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b122000ccc62dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d063589100243f43eeab12200087d83dd5624400117f08baac48800e2f21175589100046fc1aeab1220028dc835d562440011df04baac4880021fa1c755891001c5f43ee8b122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200487c87d4d624400187ee9a9ac48826b0f1d353589100062fb9ea6b122002c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b122041c3c7454d62440018bee6a9ac48800b171cd535891000637baee4b122000c6c75dc9624400195ee9b92c4880032b1d3725891000667b9ee4b122000ccc73dc96244001968e9b8ac488003351cf7158910006373b6ca3122000a6d83d9462440011db0f328c4880029ba16651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000a6e8619462440018dcec328c4880029b60c6518910006573b6c83122000e2f65d906244001c58cbb20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400155d0c320c4880032b9d8641891000717b28c83122000e2c651906244001d4b02320c488003339db631891000727b2ec63122000e4c65d8c6244001d1ec9b18c488003a3193631891000727c2ec63122000e4c85d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c488002b3a0e631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000a6e8518c62440014db0a318c488002b3a186318910006673b0c63122000e4f6518c6244001c98ca318c488003a3d9
  | 4 => 0x3440014df04b22a6881029b2096454d100051f430c8a9a2000c3e761915344001878ec322a6880038718c6454d100152f436c6a9a2000c5c76d8d5344001c3ec9b1aa688003871936354d100062fc3ec6a9a2004a5e87d8d53440094b90fb1aa6880031721f6354d100243f42eeca1a200087d85dd943440031dd05bb286880023b60b7650d100043fc2aeca1a200487c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20018ec825d943440011f700bb2868800a2fa1f6450d1001c6f43ec6a1a20058f581dd762440091df0ea96c4880029ba1732d891000536c2e65b122000a6d83d97624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc8359762440014db0632ec4880038bd9764d89100071632ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c488003a960464d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec488003a319363d891000727c2ec7b122000e4c85d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f62440014dd0a31ec4880029b61463d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727428c7b122000e4d8518f6244001d8b0231ec4880029ba1b53d891000536436a7b122059c6e76d4f6244001c5ec9a9ec4880038b19353d891000727b1ea7b122000e4c63d4f62440014dd0ca9ec4880029b21953d8910206373b2a7b122000e2f6454f6244001c58c8a9ec48800393d8d53d89100072631aa7b122000ae681dd762440015cb03baec488002b9a0474d891000572c08e9b122000e2f5495362440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf62440014dd0a39ec4880029b61473d891000573408e7b122000ae5811cf6244001c9ea729ec48800393e0d53d89100053742c87b122000a6d8590f62440011dd0e21ec4880023b61c43d89100053742887b122000a6d8510f62440014df0ab8ec4880029b21571d89100047743ea3b1220008ed87d4762440011dd0f98ec4880023b61f31d89100053742e63b122000a6d85cc7624400155d0998ec488002ab61331d89100053742863b122000a6d850c762440014dd0bb86c4880029b61770d891000557c22e1b122000aac845c362440011dd0e286c4880323b61c50d89100057340881b122000a6e85cc362440014db0b986c4880023ba1c30d891006476c3861b122000a6e850c362440014db0a186c488002aba1030d891000556c206
  | 5 => 0x80030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd16344001938c7ba2c6880022fa1f6458d100061fbaec8b1a2000c3c75d916344001958e5b22c6880022fa1c6458d100061fba8c8b1a2000c3c751916344001958e4322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880033318f7258d100243f43eeab1a20008bf845d5634400717908baac68800237e0d7558d1000477c12eab1a20018ec825d563440011ef02baac6880021fa1c7558d1001c5f43ee8b1a2000c3f75dd16344001878ebba2c6880030fd4f7458d100061ea9ee8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880063ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f53dc963440018daa7b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100063a3aee2b1a2000ce472dc56344001970e9b82c688003179db6518d100052ec3eca31a2000e5571d9463440011bb0f328c68800297a166518d100054f424ca31a2000a9d84994634400159d05328c688002b360a6518d100046fc3aca31a2000a9f84594634400153908b28c688002b3e096518d1000566412ca31a2000ad78159463440014bd0c328c688003179d86518d100052fc38ca31a2000e56711946344001caae2328c688003279db6418d100070fb2ec831a2000e1c65d906344001c3cebb20c688003875d76418d100074ab8ec831a20008dd8799063440014bd0b320c688002976166418d100054f424c831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100054f430c831a2000c9e761906344001c3eca320c688003871946418d100070f3a8c831a2000e1d751906344001d2b02320c688003a55c46418d100052f42cc431a2000a5d85988634400153d09310c688002a76126218d1020d1f426eca9a2000a3d84dd953440814dd05bb2a6880029b60b7654d100043f434eca9a2000c5c639d953440014bb073b2a68800317dce7654d100043ec1ceca9a2000c5d839d9534400147f08bb2a6881068f2117654d100052fc1aeca9a2000a6f825d953440814d904bb2a6880029de057654d100043f430eca9a2000c5f731d953440090ff063b2a68800317e0c7654d100243ec18eca9a2000c5c831d953440018ec623b2a6880031d4c47654d1020d1f436c8a9a2000c3e76d915344001878edb22a6880038718f6454d100061fb9ec8a9a2000e1f73d9153440010ff0eb22a6880021f21d6454d100052fc1ac8a9a2002a5c835915
  | 6 => 0x62fba8e6b222000c5c751cd644400193ee839ac8880021fa1f53591100243e43ea6b222000c5f73d4d64440058b8e7a9ac8881671b1cb535911000c7743ee4b222000c6f75dc964440018d8ebb92c8880032bdd3725911000667b9ee4b222000ccc73dc964440018dea7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b222000cd873dc1644400187cedb28c8880028f60f65191100071ab8eca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100051f430ca3222000c3e76194644400147b06328c8880038d9c465191100071ab88ca3222000a3e8598c644400147b0b318c888002aba0a631911000556c14c63222000a3e8518c644400147b0a318c8880028fa1b53191100070e31ea63222000a3e85988644400147b0b310c888002a7a0e62191100054ec1cc43222000c3c75d936344001878ea326c68800b179db53d8d100070fb26a7b1a2000e1c64d4f63440014bb07baec6880029760c75d8d100043fc2ae9b1a200487c855d363440018baeba9ec6880031761f53d8d100246fc3aa7b1a200087f855cb63440090f90ab96c68800297a1875d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100070fb2ec9b1a2000e1c65d936344001c3eebb26c688003871d764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c651936344001c3eea326c688003871d464d8d100074ac08c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000c5d751d763440018bd0e3aec68800297a1674d8d100052ec2ce9b1a2000ace829d3634400159b053a6c68800297e1574d8d100052e42ae9b1a2000ad6811d363440015ab023a6c68800387d5254d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d100052fc2ae5b1a2000a5c855cb63440014bf0ab8ec6880029721571d8d100054fc22e3b1a2000a9c845c7634400159f04b8ec688002b320971d8d1000567416a3b1a2000acd82d4763440014bd0b90ec6880029761721d8d100054f42043b1a2000a9d84087634400153d09b86c688002a761370d8d100052fc2ae1b1a2000a5c855c3634400159d04286c688002b360850d8d100056b40881b1a2000a9e84c83634400153b09906c68800297a1420d8d100052ec2841b1a2000c5c63dd563440010fd0fb2ac68
  | 7 => 0x7e87ccb65440010fb0f996ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca8810a9ea0371d95100043f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100053741663b2a2000a6d82cc765440010fd0e18eca8803e1f61c31d95100043f43e43b2a200087d87c87654400147d0810eca880028f61021d95102153b40ee1b2a2000a768110365440010fd0f986ca880021f61f30d95100043f43861b2a200f87d870c3654400147d08186ca880028f61030d95100053741061b2a2000a6d820c365440014ed02186ca880028fa1320d95100051ec2641b2a200087e87083654401f0fb0e106ca880030f5d754d91100245fc3aa9b222000a3e8590f644400147b0b21ec8880028f60f65d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100051ec18cbb222000a3e8598f644400147b0b31ec888002aba0a63d911000556c14c7b222000a3e8518f644400147b0a31ec8880028fa1b53d91104d61f3b6a7b222000e1c63d4f644400147d0b316c8880028f61662d91100054f41cc5b222000a9d8398b644400187aea3aec8880028fa1673d91100051ec2ce7b222000aae829cf644400155b0539ec8880028fa1473d91100051ec28e7b222000ab6811cf644400156b0239ec88800387d4e53d91100051f42e65b222000a3d85ccb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644400147d0bb8ec8880028f61771d911000557416e3b222000aad82dc7644400155d05a8ec888002ab60b51d91100045f43e63b2220008bd87cc7644400147d0b98ec8880028f61731d91100055741663b222000aad82cc7644400147d0a18ec8880028f61431d91100051f42e43b222000a3d85c87644400117d0e10ec88803a2f61c21d911000557410a1b222000aad82143644400147d0b986c8880028f61730d91100045f43861b22200e8bd870c3644400147d0a186c8880028f61430d91100055741061b222000aad820c3644400156d02186c8880022fa1f20d91100045ec3e41b222000a3e85083644400147b0a106c8880030f19375591100043f43ecab222000c5c73d9564440018d8e5b2ac8880021fa1c65591100062e398cab222000c6c7219564440018becbb9ac8880031719773591100064e326e6b222000c6f65dc964440018d8cbb92c8880032b19372591100243f43eeab22200087d83dd5644400117f08baac88800237e0d75591100146e41aeab2220008ef825d564440031d904baac8880021fa1c75591100061fbaee8b222000c3c75dd164440051bd0fb9ac88800317dd773591100062e3aee6b222000c9f74dcd64440018bf0bb9ac8880031721773591100
  | 8 => 0xe9b1a60900031b197724c1202e6373b6cb102405ce6b60d9620480014d90ca9c409000e2fa1375d8f100045ec26ebb1e20018ee82dd763c40011db05baec78800e2fe1d74d8f100061fa9ae9b1e2000c3d535d363c40090fd0bb92c7880021f6177258f1020537416eca9e2000a6d82dd953c408347d093b2a7880028f6127654f100052ec1ceca9e2040a6e829d953c40014db053b2a78800297e0d7654f100152f41ec8a9e2000a5d83d9153c400117b093b2878800a2fa1f6450f10004f8c08e0a1e200087d879d762c40090ff0ebaec5880021fe0d75d8b100243fc3ea7b16200087d87d4f62c40010ff0ea9ec5880021f61d53d8b1002477c3aa5b1620008bf845d562c400717908baac5880163d2057558b100243f42ceca16200087d859d942c40051bd073b285880023760e7650b1000c5e43ac8a16200487e85dd932c40010fb0bbb265880121fa16764cb100043ec2cec99620038be849d932c400117b093b2658800a3ba1f624cb1020e3abb2a720e2000d557354e41c400156f0ca1c8388002ec201439071002c5f43ec8a0e2000bb180d9141c413f9ceec3928388003591d472507100055a43284a0e20058f586dd231c40e396aed3a463880d72d5d9748c7100069bc2ae918e2000d34855d231c40a1a6ea6ba463881434d54d748c710006d8ba2e118e20009b584dd931c400b3e100ba2638803b2d5da419031006e6abb4631862000cd5631c530c400136b0838a41880021fe0d75d92100243fc3ea7b24200087d87d4f64840b38dce5a9ec9080031bd4d72d92100045fc22eab1c20038bc845d563840090fd0bba2c7080021f6177458e1001c5f43ee8b1c2000c3e85dd1638400187b0bba2c7080030fd4f7458e100061ea9ee8b1c2000a5d839d9538400147f08bb2a7081068f2117654e100052fc1aeca9c2040a6e821d953840014db043b2a7080021fa1f6454e100043ec3ec8a9c2040a6e82d9153840014db05b22a70800297e0d6454e100152e41ac8a9c20008bf845d9438400b1790eb2287080163b21d5258a1002c7743e84b1420018be87d91428400355d05b2285080032dd907150a100045fc22ec99420038bc845d9328400b1d90eb126508002ade1176c42100055bc22c78842000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200f87d8718f65440018bae631eca880028fa1262d95100051ec24c5b2a2000a5e8398b65440014bb07316ca880030f5d074d95104f53b408e9b2a2000a75811d365440018bae639eca882769da0473d95100053ac08e7b2a200087e8790f65440010fb0f21eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca882729da0772d95100053ac0ee5b2a20008
  | 9 => 0x7158d200065a3a0e2b1a4000cd7731c563480019cee438ac6900031dd4c7158d200063aa98e2b1a4000c7875dc163480010fd0d3b2a6900029760e7654d200043ec1ceca9a4000c5d839d9534800147f08bb2a6901068f2117654d200052fc1aeca9a4000a6f825d953480014ef02bb2a6900029d2057654d200053dc02eca9a400087e861d953480090ff063b2a6900121f60c7654d2000637410eca9a4000c6d821d953480018dc643b2a6900031b4c87654d200063d900eca9a4000c6c201d953480018f0403b2a6900021fe1d6454d200043e43ac8a9a4000a5f8359153480054b906b22a6900029de056454d200053a40ac8a9a4000a6c865c953480018d8ecb92a690286d3e0d7254d20005b4402e4a9a400487e85dd943480010fb0bbb286900021fe157650d200243e42aeca1a40008bf845d943480011bf06bb286900023de057650d200047a40aeca1a40028bc87591434800553906b228690002ad2056450d20006363b6ca9924000e4c63d9532480051d90eb22649000ab320d644c9200057240ac899240059ea87dc1324803f3d50c38264900173aa18704c92002eb5428e09924005d69851c13248001ad6ca38264900035a194704c920506b5a98e099240a0d69531c1324800117f08b9ec29000e2f21173d85200055b42663b0a400487e86dd561480010fd0fb2ac2900030f1d365585200062e39ecab0a400087e871956148001878e832ac290003171cc65585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200061f3a6ca30a4000c3e74194614800187ecaba0c2900030f19574185200047bc3ac230a4000ab48458461480015a906b08c29000e2fa1375185200045ec26ea30a400087f855d061480090f90aba0c29000e2fe1d74185200061fc2ae830a4000c3c855d0614800195f04ba0c2900032b209741852000657192e830a4000cb4815d0614813587ce9a98c2900030f5d3531852020e1f3a2a630a4000c3d7454c61480058bce6a98c290003175cd531852000656ba26430a4000cb574d04614800156d09988c290002b960b31185200043fc2aed20a400487c855da41480090fd0bbb282900021f61776505200243f42ceca0a400087d859d941480090f90a3b282900063b20876505200043f436eaa0a400087e87d9541480010f90fb2a82901731b1cb65505201ad4e41ac8a0a4000ab48159141480018decbb9282900031b19772505200043fc2aed18a400487c855da314800717d083b462900022f610768c5200061f3a6cb18a4000c3f655d23148001878caba46290003279d3638c5200243f42eec98a400087d85dd9314800717d083b262900022f610764c52000c5fc3ac92024026a9c83592404800156902b2480900030f1d3654c1200061fb2ee89824000c3c65dd13048001938
  | 10 => 0x98c4002ad48358531880211df0eb0c43100029be15618862009c77c32e110c401887d8718f654800147d0831eca900028f61063d95200062eb98c7b2a4018a6e86dcb654800187ae83a6ca900028fa1073d95200051ec20e7b2a4000c5d731cf65480b94dd0439eca900029b60873d95200043f43c87b2a400087d8790f65480010fd0e21eca900021f61c43d95202e53741087b2a4000a6d8210f65480014df04b8eca901729b20971d95200051f420e3b2a4000a3d841c765480010fd0f98eca900021f61f31d95200051f42663b2a4000a3d84cc765480b94dd0598eca900029b60b31d95200043f43863b2a400087d870c765480014ed02206ca900029d60440d95202e43f43e61b2a400087d87cc365480010fd0e186ca900621f61c30d95200051f42061b2a4000a3d840c365480b94dd04186ca900029da0430d95200053ac0861b2a400087e87d9564480018b8e7b2ac8900021fa1c65591200062e398cab224000c5f65dcd64480018b8cbb9ac8900031dd9771591200063a32ee2b224000c77651c564480018e8ca38ac8900032d19071591200243f43eeab22400087d83dd564480011bf06baac89000a3720d75591200047bc0aeab2240008f4815d564480010fd0e3aac89000a37a1f73591200062fbaee6b224000c5c75dcd64480018bf0bb9ac8900031721773591200062fba8e6b224000c5c751cd644800193ee839ac8900021fa1f53591200243e43ea6b224000c5f73d4d64480058b8e7a9ac8900031ddd771591200063a3aee2b224000cd773dc564480019a8e7b8ac8900031dd4f71591200063bba8e2b224000c74751c5644800196ee838ac89000335dcc71591200066a398e2b224000ce7721c5644800196d0838ac8900031dd4c71591200065ba18e2b224000ce6321c564480019688038ac8900029760f75d8d200052ec18ebb1a400087f855d363480090f90aba6c6900121fa1671d8d200043ec2ce3b1a400087f855c763480090f90ab8ec6900022fe1171d8d2001c5e422e3b1a40018ec825c763480010fd0fb2ac6900030f1d36558d200043f438cab1a4000c3c7419563481458f6e032ac6900030fd977458d200061e32ee8b1a4000c7765dc563480018e8cbb8ac6900031dd947158d200063a328e2b1a4000cd4631c563480090fd0fbaac6900022fe117558d2001c5e422eab1a40008ef825d563480011ef02baac6900023d2057558d200047dc02eab1a400087e871d5634800717d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f53dd1634800187aa7ba2c6900030fdd47458d200061e3a8e8b1a4000c9c74dcd63480018d8ebb92c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031dd4f7158d200063aa9ee2b1a4000c77751c563480018e8ea38ac6900032ddd0
  | 11 => 0x4c00155f04b2ec898002ab20965d91300055bc0acbb226000ab481597644c00147d0a316c8980028f61462d91300061eba8ebb226000a3e851cb644c00147b0a396c8980028fa1771d91300051ec2ee3b226000aae82dc7644c00155b05b8ec898002aba0b51d913000556c16a3b226000a3e85c87644c00147b0b90ec8980022fa1c21d91300045ec3843b226000e3b50943644c00155d04286c898002ab60850d91301345f43e41b2260008bd87c83644c00147d0a106c8980028f61420d91300045fc22eab2260008ef825d5644c0031d904baac8980023de0575591300047a40aeab2260008bd87994644c00153b07328c8980022fe1d651913000557c12ca3226000aac82594644c00156f02b28c898002ad20565191300051f428c43226000a3d85188644c0018daeba96c49800e2fa1271d89300045ec24e3b12600087f855c7624c0090f90ab8ec4980022fa1f64589300061fbaec8b126000c3c75d91624c00117d0e322c4980030fdd464589300061e3a8c8b126000cb764dc5624c001968c9b8ac4980032dd9071589300065a320e2b126000ce4621c5624c00317d0fb228498002b9a0b51d85300053b42e43b0a60008be87d91614c00187eebb22c2980030f1d7645853000656396c8b0a60008be87191614c00187eea322c2980030f1d4645853000656390c8b0a60a3cbb70191614c00195ec9b92c2980032b19372585300047bc3ac230a6000a7485584614c0015c904b08c298002b9a0b51185300056ac18a230a6000a7685c84614c0015ab06108c2980121fa1676505300043ec2ceca0a60018ee829d9414c0011db053b282981e30f19375505300061fbaec8a0a6000c3c75d91414c001958e5b2282980032bd93725053016656326e4a0a60008bf845da214c00717908bb4429800e2fa1376485300045ec26ec90a6026c9c73d91404c04d93cedb24609800f279d8648c13002c5f43ea8b244000c3f75d5164880010ff0ab8ec7100121f21571d8e2020d1f424eca9c4000a3d849d953880014bb073b2a7100031b1ca7654e200053b40ceca9c4000a75819d953880014f5013b2a71000297e0d7654e2000636bb6e4a9c40058bc8759143880015cb05a8cc3100121fa1f75586200043ec1eeab0c4000c7581dd561880018d843baac3100021fa1f53586200243e43ea6b0c400087e8754d61880010f90ea9ac3100031ddd7515862000572c16a2b0c4000c7775145618800b1eb0f30c83100021fe1576506200243e42aeca0c4000c3c75591418805995cc9b9283100031d1d6615062000673b94c2a0c40058f48758541880018e8eab0a831000e2fa13768c6200045ec26ed18c400087f855da31880090f90abb463100163d61e618c6200065aba4c318c4000cb57458631880010ff0abb263100121f215764c62002c7a43ac2
  | 12 => 0x8023ee017650d2102c7c402eca1a42028be87d914348401878ebb2282908b32b193725052101477c3ac710a42008fb8758060484011ef02baac7200023d2057558e400243f42ee2b1c800087d85dc563900031dd05b8ac7200023b60b7158e400052ec1ceca9c8000a5f835d953900014ef02bb2a7200029d2057654e4020537410eca9c8000a6d821d9539000187aedba2a7200163b21d5258a400243f42ee2b14800087d85dc5629008187eeca9a85200022f6187150a400bc5ec36e0a1480008f7815d932900011e902bb265200163b21d624ca4001cd643a849948001aaf8650932900018bee6a9ac32000b171cd53586400045f43c86b0c8000ab68190d619000117f0eb1c832009b479cd53906400945fc3ac320c80158bf865c2419000b1eb0f30c63200032d5d2618c6400065aba2c318c80058f48758531900091bf0ea9ec6a00021fe1572d8d400243e42ae5b1a800087f855c763500090f90ab8ec6a000a2f21171d8d4000477c12e3b1a80018ec825c763500014bb073b2a6a00028fe117654d400052fc1aeca9a8000a6f825d953500814d904bb2a6a00029de057654d400053a40aeca9a8002a5e86d8d53500094bd0fb1aa6a00129721f6354d400045f436e2a1a80018be849c762500010ff0ab8ec4a00121f21571d894000672310e2b128000ab58408761500011ef0eb08c2a0002b9209611854038c5fc3a8630a80008be86dcd415006b938c7b9a82a00d78718d5350540006963a8e4a0a80158be871854150001a76ea38282a00021fe15768c5400243e42aed18a80038be841da315006b938c6ba462a00162f219744c54002cdc402e898a80038bc865ce405004d938c6b9c80a009b8718d539014001c5ec38c32028000cb57118640500090fd0fbaac5180021fa1c7558a3002c7643aa4b1460038be841c5628c00117b0838ac5180021fe157650a300243e42aeca1460008f7815d9428c0011e902bb285180062fa1f6450a300243f43eeab0c60008bf845d5618c00717908baac3180023be09755863000c76412eab0c60038be87dd1618c00187eebba2c3180030f1d774586300061fa9ee8b0c6000c3d53dd1618c00187eea3a2c3180030f1d4745863000c7743ee4b0c6000c6f75dc9618c0018d8ebb92c3180032bdd37258630006563a6e4b0c6000c6f53dc9618c0018daa7b92c3180031bdd47258630006363a8e4b0c6000caf741c9618c001958e8392c3180163d61e619063001d5a422c320c600087f855d9418c0090f90abb283180023be09765063000c76412eca0c60058f487585418c0231bf0eb0c631805237e19708c6300243f42eed10c600087d85dda218c00117f08bb4431800e2f21176886300043fc2aec90c600487c855d9218c00117f08bb2431800e2f21176486300061ebaea9b2260048bf8755364
  | 13 => 0x477c12eab2262018ec825d5644c4011f700baac8988163e20175591310043f438eab2262018ee87dc9644c4018deebb92c8988031b1d7725913100637a9ee4b226200c6d53dc9644c4018deea392c8988031b1d472591310063dbaee0b226200c7875dc1644c4019d6e5b82c8988033a1cb70591310063da9ee0b226200c7953dc1644c4018f6ea382c8988031e1d470591310065dba0e0b226200cdb731c1644c4019d6e4382c8988033a1c8705913102e5d420e0b226200c7b531c1644c4018f2a6382c8988032e90c70591310065c218e0b226200cbb421c1644c40b9e302382c8988032e104705913102477c3aa5b1262008bf845c3624c40717908b86c4988062f21d645093100d56412c8a126200ab880591424c4051ed0db8a84988032d59071509310145fc3ac920a6200ab880592414c46b93cecba46298802bc60440d81310047dc3ac03026200ab884580604c40187ea6ba0c0988030f54d741813102e5c402e83026205cb7105d0604c40b96a20ba0c0988032e5d340181310047b40eebb2442a6ab681dd1648840717d09baec7108022f61375d8e210047b40eebb1c42058fa80dd763884011f301baec71080e2fe1d74d8e210061fa9ae9b1c4200c3d535d3638840196ae938ec7108121fa177058e210043ec2ee0b1c4241a3e849d9538840147b093b2a7108029760e7654e210053b40ceca9c4200a7a809d953884014f3013b2a71080297e0d7654e210152f41ec8a9c4200a5d83d9153884018deecb92a7109bacb2117254e2152da7c1ae4a9c4200b68805c9538840117b093b2871080a2fa1f6450e210147743ec89944202ace83d913288459958e8b2265108ba3b61b714ca21004b6c2ee2994420096d851c1328840317d0fb2283109d6ada0764506210045fc22e730442038bc845ce608840117f08baac11080e2f211755822101c5f43ee8b044200cae32dd1608840187ee9a9ac110a6b0f1d353582210061fba2a6b044241c3c7454d60884018bee6a9ac11080b171cd535822100657ba264b0442008fb87580608840187aebaa6c8908121fa1f75591210043ec1eeab2242008bf845d564484011df04baac8908023de0575591210043f438eab224200c3c75dd164484010fd0fa9ac8908121f21f535912152637b96a6b224200c6f75dc964484018d8ebb92c8908031d1d771591210043fc2ae9b1a420487c855d363484010ff0ab86c6908121f21570d8d210045fc22eab1a42038bc845d563484011ef02baac6908023ee017558d2102c7c402eab1a4200a6d82dd953484014bb073b2a6908028fe117654d2120d1e422eca9a4200a5f835d953484014ef02bb2a6908029ee017654d210053c402eca9a420087f8759153484010f90eb22a6909ba9be096454d210043fc2aeca1a420487c855d943484011df04bb28690
  | 14 => 0x9840c360504015e302186c0a08031b9cb659814100637390cb3028200c6f655ca60504018d8cab94c0a08031b9d7629814100636baec53028200c6e7518a60504018daea314c0a08121fa1b75581413c43e436eab02820087e87d9560504018b8e7b2ac0a08031b1cb65581410043f438cab028200c5c7319560504018d8e432ac0a080317d9773581410062e32ee6b0282348ec86dc960504018decbb92c0a08031b19772581410047743ec4b028200c6f75d8960504018d8ebb12c0a080333dcf62581410066639ec4b0282008ee8718960504018deea312c0a08031b1d4625814100667b98c4b028200ccc7318960505559cee2312c0a09e71d5c465181410047dc3ac03028200ad88358060505358eae3a98c0a080b179cd53181410062eb9aa630282008bd8790c605040796ae3218c0a08021fe1572181410243e42ae43028200ab481508605040717b0f208c0a0802ae60241181410054ec18cb3246200a3e8598a648c40147b0b314c9188121fa1f75592310061f426eab246200c3d84dd5648c4010fd0e3aac918aa6ada0774592310045f43ea8b246200c3f75d51648c4091790eaa2c9188030fddb75592310061fbb0eab246200b1d831d5648c40117d0fb2ac918aa2ada0765592310045f438cab246200a3e85989648c40147b0b312c9188028fe0f75592310051ec1eeab246200a3e859d5648c40187eeb3aac9188028fa1c75592310061f438eab246200a3f831d5648c40147b063aac9188028fa1672592310051ec2ce4b246200a3f855c9648c4014790ab92c9188d6ad205725923100656b90e4b246200aae82d45648c40155b05a8ac9188038dd4651592310051f42e42b246200a3d85c85648c40117d0e10ac9188d62f61c21592310051f42ce0b246200a3d859c1648c40155d05382c918802ab60a70592311ad5b40ce0b246200a3f855c1648c4014790ab82c918802a7e0d70592312855b408e0b246232ab5811c1648c40156d03282c918802ad606505923100557410a0b246200aad82141648c40156d02282c918802ad60450592310045f43e40b2462008bd87c81648c40147d0a102c9188028f61420592310055b40840b246200ab581081648c40117b0f326c5188022fe1d64d8a3153e5b38ac9b1462038be84dc1628c40117b09b82c5188021fe157650a310243e42aeca1462018bc87591428c40355904b2285188032d5937150a310147ac30e2a146200cb5641c5428c46b93ce6b2483189e30f99375506310061eb26eaa0c622ccae64dc9418c40195ac9b9283188030fdd664582310061e3acc8b046200c3f75591608c401878eab22c1188121fa1f75582310045ec3cc830462008bf87590608c4a196ce2b20c1188023ee1d60182310065c320e0b22620487e87dd5644c4010ff07baac8988021f60f755913100
  | 15 => 0xb996c4a08062f21170d894100536c1ecbb128200a6d8319762504014dd0b31ec4a08029b61663d894100537c2ac7b128200a6c8558f62504015d700b1ec4a0802ba20163d894100537428c7b128200a6d8518f62504014dd0da9ec4a08029b21b53d89412ce373b6a7b128200a6e8654f62504014d90ca9ec4a09031b9d953d894100556c26e7b12822cae581dcf62504014dd0b39ec4a08029b61673d89411a557424e7b128200aad849cf62504014dd0a39ec4a08029b61473d894100727a9ca7b128200e4f8354f62504591dd0fa8ec4a08023b61f51d894100733a8ca3b12822c8ee87cc762504011db0f98ec4a08029ba1731d894100536c2e63b12822caae84cc7625040155b0998ec4a08029ba1431d894100536c2863b128200a6e85dc362504014db0bb86c4a08029ba1670d894100536c2ce1b128200aaf845c3625046955908b86c4a0802ab61070d894116572c08e1b1282008ee8714362504011db0e286c4a08029ba1730d894100536c2e61b1282008ee870c362504011db0e186c4a08029ba1430d894100536c2861b12822caae840c3625040155b08186c4a0802b9a0430d894100572c0861b128200c6c62dd562504010fd0fb2ac4a08021fa1c65589415a63bb88cab1282b3c6e76d946250565c5ce9b28c4a08038b5d3651894100536c1eca31282008ed8799462505634dd0b328c4a08023be1d651894100557c22ca31282b0ae781594625055f4dd0c328c4a0abb1b9d8651894156f173a0ca3128200e2d7419462504014db06328c4a0ab78b10c651894156f33a08ca31282ade2c41194625055bcc882328c4a0ab78bd00651894100476c3cc63128200a6e8598c62504014db0b318c4a0802ab612631894156572c0cc631282008ef8758c62504014df0ab18c4a08029b215631894100575c02c63128200ae88058c62504014dd0a318c4a08029b614631894100537436a63128200a6c86d4c62504014dd0ca98c4a08029b219531894100557434863128200e2c6590c6250401878edb2a84a08038b18b655094100d56416c6a128240c3c7654d4250481c58c4a9a84a0806aba1b62509411a6563b6c4a12822c8be861c542504ebb4ee438a84a08b26da1871509410065b430e2a128200d37651c54250401a68ca38a84a08032dd8c71509410069ba98e2a128200d35531c54250401b4ec438a84a09d769188715094155ed3190e2a1282009b5801c5425040117d0db8284a08121fa17764c9410043ec2eec9928200c3c65dd132504051dd0fb1264a08b32b1d3624c94101cd643a849928201aac865093250401958eca1264a0802e9205424c94101c7b436e29928200c7465dc532504018e8ca38a64a080339d88714c9413c71bb0ecb20a82038bd87d8e415046b93ce7b1c82a08d7479cd539054100716328c520a8200ab
  | 16 => 0x5d85320063abaea3b0a6400ae582d47614c8018eaea28ec2990032d5d361985320047bc3ac230a6400ae582d44614c8015ab06288c2990021fe1570185320243e42ae030a64008bf845c0614c80717908b80c29900e2fa1271d81320045ec24e3b026400c7975d43604c8015b307a86c099002ba60850d81320047dc3ac03026400a7885580604c80b1f100ba8c0991661fe0d75181322043ec1aea3026400c6c215d4604c80b8f100ba8c0990171bc81751813202e36902ea3026400c7975d40604c8071e902baac7208123721d5358e410052ec1ceca9c8200a5f835d953904054bf0cb1aa72081297a1d6354e410252e43ac6a9c8200e5563dc553904834eb0c38aa7208039558c7154e4117c5ec36e2a1c82008bd861c1439040136b02382872080e3d618714ca414d63b38ea730482008ef825d560904031d904baac12097e2f21d43582410047dc3ac03048200a6e8298f65504014db0531ecaa08da1f61c63d95410062eb98c7b2a8278a3e84dcf655040147b09b9ecaa0ad69da0773d95413c53ac0ee7b2a8200c5d731cf65504f147d08396caa08028f61072d95410043f43e65b2a820087d87ccb65504010fd0e196caa08021f61c32d95413c51f42065b2a8200a3d840cb65504f10fd0f98ecaa08021f61f31d95413c51f42663b2a8200a3d84cc765504014dd0598ecaa08029b60b31d95410043f43863b2a823687d870c765504f10fd0f90ecaa08021f61f21d95413c51f42043b2a8200a6e829c365504014db05386caa09e28fa1070d95410051ec20e1b2a8251a76811c365504f14eb02386caa08021fa1f30d95410043ec3e61b2a820087e870c365504010fb0e186caa09e28fa1030d95410051ec2061b2a8200a6e820c365504014db04186caa08029da0430d95410053ac0861b2a8278a3e84c83655040147b09906caa08021fa1c20d95410043ec3841b2a8200e1e43d97635040187ae832ec6a080e3d60775d8d410052ec1eebb1a8200a5d831d763504010ff0ab96c6a08121f21572d8d410043fc2ae1b1a820487c855c363504010fd0fb2ac6a08031b1cb6558d410043f438cab1a8200c6c7219563504018decbb92c6a08031b1977258d410063db2ee0b1a8200c7865dc163504018f6ca382c6a08031e1947058d410066c318e0b1a8240a6e82dd953504014db05bb2a6a08021fa1a7654d410052ec1ceca9a8200c3e849d9535040187b093b2a6a08031760e7654d410063ac0ceca9a8200a5f835d953504014df04bb2a6a09029b2097654d410053dc02eca9a8200a78805d953504090ff063b2a6a08121f60c7654d410051f436e8a9a8200c3e76dd15350401c58c5ba2a6a09069da1b7154d4100732316e2a9a8200c76761c55350401a68e838aa6a0803991887154d4102477c3aa5b128200a6e85ccb62504014db0
  | 17 => 0x2a600c3f63dd16054c01a3ec7ba2c0a980347dd373581530068e3a6e6b02a64096e87dc96054c01a5ee9b92c0a98034b1d37258153006a7b9ee4b02a600c6f63dc96054c01a9ec7b92c0a98034bdd07258153006963a0e4b02a600d4f731c96054c010fd0fb12c0a99031b1cb625815320636392c4b02a600a78805896054c01a6ee9b8ac0a98034d1d37158153006abb9ee2b02a600d6772dc56054c01ac8e5b8ac0a98031dd8f7158153006abb1ee2b02a600d37741c56054c01a68e838ac0a980355dcc7158153006b3b90e2b02a600d64721c56054c018eec638ac0a980355d8c71581530063bb10e2b02a600c75621c56054d77ab6e7b02c0a98035a1cb605815300636394c0b02a600c74719816054d2b2bf06ba0c0a99025be1d721815300637b1ae4302a600d4f635c86054c01ad100b90c0a98021f61e621815300636b94c4302a600c6d721886054c672bf06b88c0a98031b5ca611815300636b90c2302a600a79801846054c018dae5b00c0a9aead660e60181530043fc3ac0302a600a6c825806054c018dae4b00c0a98029d2056018153004bdc3ac0302a6b9b5b835806054c016d104b00c0a9802d660f2018153006b4b9640302a600e6a62c806054c01cd0c4100c0a98021fe1571d89430243e42ae3b1286028bd84dd76150d7196ae9b0cc2a18023de1d61185430047dc3ac030286b7abb845806050c018eea7388c0a18031d54e71181430043fc2ae2302860487c855c46050c011df04b88c0a18063b20971181430065a20ae23028600c77855c46050c018e90ab88c0a18032de1171181430065a422e23028600cd7835c46050c019a906b88c0a18031dd4d71181430063aa9ae23028600cb6435c46050c0196886b88c0a180339e09711814300672412e23028600cb7425c46050c0b96e80b88c0a18172d50171181430043fc2ae3b1a840487c855c763508010ff0ab86c6a10121f21570d8d420052ec1ceca9a8400a3f845d953508014bf06bb2a6a10029de057654d420053a40aeca9a8400a7b805d953508014f100bb2a6a10026d6047050d420063abaea3b0a8400ae582d4761508011ef0eb08c2a10029d21561185425b573c12c230a84018bd84dd461508b387ae9a98c2a11c62fe1d431854200572c16a230a8400ab58414461508010ff0ab80c2a10121f21570185420046fc1ae030a84028dc835c0615080317b09baec0a100e3b60b75d81422ce1eba6a7b02845f8bf8750f60508011f70eb00c0a10021fe1571181420243e42ae23028400c3d75d53644c80117f08baac8990023de0575591320047a40aeab2264008fb805d5644c80b1f100baac89900a3b60b75d85320043ec3cebb0a6400c6d729d7614c8090ff0ebaec2990031b5c975d85322cc3fc1aebb0a644087d835d7614c8018ef02baec2990031b0857
  | 18 => 0xc01100001600e00501701a00900004400700400000000400900500100003c00100001f00000900000d0010030030010140020160060060000070020010010000020010010070000030060051ec3485b22a63395f835c76454c052b906b8ec8a980a57a0e70d91530f4aec1ce1b22a641c3f76d916454d87a3ee9b9ac8a99064fa1271d89530049ec24e3b12a60295e839c76254c612bb0738ec4a98024fe1170d895320c9e422e1b12a62195f835c36254c052b906b86c4a99064fa1f745895300716316e8b12a600c3f63dd16254c01a3ec7ba2c4a98038b18874589530068fba6e6b12a600d1c74dcd6254d85c98c5b9ac4a99029ba1b625895360ea7b9ec4b12a600d3774dc56254c01a68e9b8ac4a980355dcf715895300732316e2b12a600c7586dc56254c018eec7b8ac4a980355d8f7158953006b3416e2b12a600d37741c56254c01a68e838ac4a980355dcc715895300732310e2b12a600c77631c56254c01aaec638ac4a98034edd370589530069c3a6e0b12a600d5b73dc16254c01cd0c5b82c4a98035cdc77058953006b838ee0b12a600c7b63dc16254c01ab6c7b82c4a98031b18870589530069dba0e0b12a600d38741c16254c01ab6e6382c4a98039a1887058953006b9b88e0b12a600d70711c16254c018f30c382c4a98031ed8c7058953006adb18e0b12a600d6a821c16254c01ad6c4382c4a98031e98870589530063c310e0b12a600d68621c16254c018d0c4382c4a98035a08470589534acafc1ae9b0aa64096f875cb6154c018dec6b96c2a980353d8d72d8553006b3c0ae5b0aa600a7586c876154c0166b0810ec2a9802d560c21d8553006b2b9043b0aa61e95d839c36154c8327f0eba4c2a98030fd8d74985530068fb1ae930aa600c3d749926154c014eb03324c2a98030f5d064985530068f3a2e730aa600d1d745ce6154c0147908b14c2a99031b9c962985530053c402c530aa600a6d82d866154c01a6ae9b0cc2a9b03555cf61985535feabb9ec2b0aa600a75819906154c014eb02320c2a99021f61f62185530053ac0ec430aa600a3c845886154c818d8e4b10c2a98029de0562185530053c402c430aa600a6d82d846154c0166b09308c2a9afad560e61185530043fc3ac230aa600977875846154d7b6af06b08c2a98029d61b21185530059ac204230aa600b55830846154c01ccac4108c2a98024fe11701855320c9e422e030aa62195f835c06154c012df04b80c2a99025b20970185532043ec3ec5b02a640c6c7258b6054c014f100b16c0a99064fa1271d81530049ec24e3b02a63095d839c76054c014f30d906c0a9802d660f20d815300734b1641b02a600a79860836054c01cd6c4106c0a98031b5ca62981530053cc04c5302a60096f825c66054c812d904b8cc0a9af3565cf609815320c9f43ee8b
  | 19 => 0xa00100100000700001200001000102400400000100400100100f00000101a02700c00200200000600400000000800f00500404300000200100100401700300000100300100100100200a00000900501500000000102400c00000000100000100201400100500100000400000a00501300500000000300000100401400300100100100b00500501000000a00500402b00300902500200500a01500000000000300800800001a00001c00700000500d00500200402600100600100000100601100000201100000000000300000000100200500d00900000000000000300d00000000000200100101200001f00600100200700c00000100400100300000500101200200c00100000100300200200100000d00100900e00100900800000300400001601b00700000303000400001400000f00304200000a00300900000000900200000100402700700600200200101800c00b00200000000000f00600000300800200100000200600000800500000100500c00200400100500000000502100e00100500c00100000100100400b00000100300000001f00000000000100000900800001300000200000100200200e00800000000000300000200f01600000000a00000100000001602000700200200200001400000701601800100000101700100b00500100000900000500700000301800501700401900202900000500100400300401b00b01401101d00000100000a00200000003200000000100000400900c00501700100000100000202300b00100100100100100900000400400900200401600400000300200100b00100d00200d00000001601500200c01501300400400000500300100000002b00000e00300000302500000000c00000800f00500002200400000b00c00b00700400100100301400600901300a00400500600701d00400200200000200401b00100100b00300706a00700000000401700600000100801d01c00000000301200000100000000201400800100000800902700500500e00000100200300600000201300d00400000800c00200000f00400a00800100100100000a00600c00400100700500000000200201200000100f00100000100900200400400b01b00100300500400600a00000000000000800000200000600000d00000304102a00202100f02800200300100100000200000700a00000400100b03800400100000100300000100a00000300100900100000101a00000100100600900000100001e00100100000201700000a00300f00100000400000100000e00000100700400500101e00000b00400b00000300000400700100000500500200800000300200000400c00600200200000201200b00500100000600a00f00200700001200700300101100600700a0000000290000000050030000070010030050030070010
  | 20 => 0xe46221e500017949e89d50d3a65413c3873be9d10a867361bb800001e00000000011029520001e9800081427c105c0003a10000000de24b14279cf80003f83fa800137e7262479820cea00021280005f819031823ed35000000020290fc5f816d0000ebe2a94cc136d3f214513c00009060f234718d81426352b48644a600782c488bc8b46000000000e1000000016d0000a3623388e40007a24b004ecf687d71d021c00004d800017ec00085d0001eb8000456000204419c91721200007949d630a9b402880002f79ac1214a2c031800030e1c02438000d2c18f279800000093f5040000000000000000127608c3b0833007e2f900017f488229400e26c4f1e79300814a53288e20000310bd633002f21b0fe24e10000000b1a216481000000038632b13b8ea83e0000000000013e38281ac00000022a01a11ca587042a55c0be00043c83dd17667a00000013320000cd0a4000099d1721ea400000000000000004df0d6800037646800001d85422f616700011369bd0000000e422541a1242099200031e0e08bb29f718b8728b820002da9c087600000000ff80008a30000b740008d8431060485e23030d82008245b94798ac4ff60e629a0a64eca8d13739190f8002b25600010040002bfa15c0002bd2f4a0d052604945825581d04211cea2cc36e0004f12880e260f1000000000003a3c680013a226000000006b40000001d14b9e7b12b9a6ac000512174240c7c478b2be92c8d9e1e60721d0528a2703022304df800028b85b4eb07ff36e85fc55c8bd3870c6000062c480000000089d33e21240006d34a61e8cf644553480000b222ee30a27086e020927d03440000000000e5c4f46ee30307dcb2e5a544d1c7483469742f118d1400300360df09e47850a324940008e14dc900c9823a3000277cbc63c10001ac4028000308a2dc9489a130c0ebcacc00023004b48be0691d28000c8464e260142cbfc47e09b239940c4452ac90b940a59d04195b44708b220a1ee467218300e94680f611304f9c18d0c2530a608985240232d1909c1b60a74a59470bd02064358f40e8689f259a3f862a5161f60f581d257208d037518428d08a28d010882821915488dc0c150116584402c833614845d201300100200b00000000100000500e00400300400000000900400100f00200100200500400100e00500101000201000700f00000700700100500600000400000000000200300000200000500300001a00c00800203100101400d00200000100000200000900000a01100000a00200801102200100100300d00000100000801e00201500300200601200100300000000500700100100004600400100000500600300500f00d01e00100500000100900100000600200000101000000c01800200001000002a00400000000000a00000101c00c00000200000
  | 21 => 0x7705b800000000000000000009f100000013b68b826f05380005c70001accdf200025c80012c60003f6000000000000000000000000002848f9069520308b101c65b183290000000018296e90360002e98eb10b26d84bf995034c8d50001dd02b4a38167a7954520001a013513e40ba0b0a0b420e9b00ae0000a563b7010a11060e7f819004789600003c2000132292217d21349ae000389261436259f423a81d05c69c296231c29a6a91590f3cbcc86e2bc11dce003fa410a4cc9fe00031185640001683c11ef857c17643b01c8b965843f091f118066d00014d8fa800000006f934ea16424140800031e13099980009bc00000002222cc2a29804b6288510993880002eb37a9298daa6444f622700009134f00cb46d63502e40000db40001559eac5c6000411801c42829130628c90c89f4197068c7501414aa8294a020362270a6886a3094178a884345db077870cb168c351e80000008af0001a508502360efa2940003833f00da8f86830331217d46a2a52a9800130499f40d00000007d6266814811698920c1e650063bb3521e44e663131111fbd4187252cd00003a09880000b5cbfe98b07c1198d3087a4951cd0c445c53d824b923e1510d591b4d8493e5129a8cee285a0b38e000ee3b13a91230e1236c000144033c05705591a4dc240f4d297dc74c0004c685292221b42c000000008a40f71cb4c7200000019fc36a0003d080005300000e68000d1a0003f9158800073945f11e80006a60af90dcb5000d4a521600005400000f152b85180e3899800067934e8000e506280a820fc57200017c1d8cc94366395000000000000013c52480cb34d00012624e907e07cc7fa99e00024d0f4068110880e400094700000000006cd0001cf400000010ca4c0ad4097000160cc4200011da16cf8865200022b89220b300005540009fc30480000000434ed0ef89f217416507c800021d000000000096f000182800068946309083c677304d8a800002470c28804d946b215327b8000000000000000000007000ccaf64854f300009348da00002603e000009113ecfa038c3ca08712825a600000000000001080990bce52409808602024810000000b2a88845e00011c60001cd099400030d16a1d647ee76f227830072608d26194f069e4be4080e4813a1034969db893ca3717007887e2a3b04489dc00a33201a84581ae9ff4351e1845c7550001dc85e41f420e8cd936c1e0000089c8a00d30331ae871c44b25d27701946fb3e9098c41e0be49184147d026e1518d2492c27451f1af400000005500010aa00010692b53fc12834196640000fd3750db832a00006a8f4c0004f618d89202de0f614a8a18e9010f0b29cbc0527661a30f0d01e8b13e507189966cb0ce0ef425400019a1d40c528f607c933855e5933121dc02fc71e4ea10f4e9e87819201
  | 22 => 0x3f2000000000098a3250db028091c3222b7222873668c4be8020e6e60e2721078d240002f0000000065900004d04be0000000000000444345000056c01f0001a6400026216e000000000000010e867e00029ba1380003c83be13b00002ef10516e02f81f82f912a00900002de08211ce0000001d24cbc2c60000de8b049d805f814c5122690002834d0a4331b20c992088980a487d80005850001480ad049c0a780007ae00016da20096830a0df825400031613901d40002400000000a2693631f80013ce0003bfa0909100000000000ce65cd18c800075c31041c073c59600c090800043c3030c49680f6a546173800123a9924831a94a4642d2ce000000000000009740006d73502000892a4202080000000000000438000000405897800000034410e400000050c9184f9a9cd3129c1cf924cf0b61f680268261e9088c5581ce4621bdd19e6ad1f300000000f4360895c000929090210870a389156997000000000017b02bc899415800121e0510000fd0000751519a15046228512e13ac5a62cd1dc16c945c4e54ac1a791e80e30a1914400000023115094141884f9a4c8f665bd317a100dda94320b12f06ec9270f7863872a50745c94f413240c00006a8da80373f11ce929c5af3029e7472c4710001d2897a1404a000010fe00015a86e40000002ae8e604ce0002298000d22000000000142000020d87f12cc000270000078c49f00009d90125e418120a814c5411411aa08ec9391aa288544e059122a4410f662e3809af011c98401e0aa02ea28c000000016838d0c51c702b60b83a00c38b20173268a61800050c31880006e613c0c319c416200000017789ee9e80000efc98c2fd4fb14ec24837f20700000000004e795947168330000000000000000000000000024e87ec00027f014000052e650000087c0000000ac0d1458600041f0000000000000000000088e25c218478e0003b2149400005b39e018400010a0d100001d89213cd0f10aa03411fc9fd000093a37918f48e00004b2800000076a000000000000000000000009d20000f780000000001e388d4000414941400000041e80000002c2000000000000051d000000000000022880588ad1db0000f8c09246d80000001a83239bb09125cc00000000000002020000b6c5c400000000009c1000272948600006e208089a1fa00000000000000938108d800000170d48a3c0000be8000b289972ba800000006d0001c3d43c7f3000286cb5800049583212245a224513f40005be3fc84b00000ed30918e13d28160949f647fe7bc064800058804a01a10201720934d68000dc801a2841b6cbf400050a2724f1476730d207d2700c203781012e660b41e00000009c64a8105400078c0001e9528411d0f680002c80004fe9c6000066138500000002c00d8057441895b0001b8818c6
  | 23 => 0x7ce45d189ce440002730c7463495d0000fc00008e422e992d0cc6515130d30b4200030183582201d9063a8acf2c5572be20600000310ea05e845a0003c910f8ec07bb1d10de0a14331000000000073f0000e1103c6a105780001101cc0c1000053a4f51028cf943a50000004b884c3ee0fa96fc66a2c70000000000000000000000000000c280c0008a1339000000059e00009e400073000023400006550000000af424400014b519600000000010ee44241600000003d947c0e7800019b0001b7869c75c00026e00000f314f83149300004f58c3103a0a326d0d742f016b15a05dc87800021114c912a9d93341cec33a06747400013ba79f2c500c8aa898738b80000003e129880004e27f705e9b7ccec6d22d7210c23097146723e46b800000023fc0000001f991ad06a54f4651fa8b1e16309780000005ee0001de446e7690e2880c0401711f68000f8a3571689e210768c90000000d4e00011506f40005d60000f248b65981dc800000053e1f50494ea60000001340ae211c37a02507e49440000a0ccae1024ef00a800067d4d784e400000000008a404e000000156800000000000008987e825d8000000000309a470b1000000000000001a42eb9afd35400000000000000001a2000000000034204540008c8000000142a7800f39f989542d800c9ed892a35543a0000eac3e53c19b2005a88216926ecfdc40b143a01520e7772878eacb8407e22928041e04583a721c936a8073f3a638c6616046b876885600000028c4f2a0000000b7cffc6fd28aa128a722fe14797d4ad6000000169c05e00012aa2fd26e44816b000131e00000000000006483df93084005df3ec07a86585d0178800000003e000000000000047e2430c8285c26b0c7c4d67bd1d980000000000b489f000036950588088b804b20f9b380009be14509f45f600025f80009da07000000012a80000438aecbaa104324a8912322d909e85c036619f45a1adc34098c48d1774e3619930690ecbd42b8099a690ab6822103800020c4a31ac1fe800000050497380000003fe02c91de3fb1109bbc3fe52a4b70f708261c407f14251e263e3d68000bda37b3620000f2e9963a58f002cc32b18210fd15833848d998d2c46be5168cbc42a3e94e421186f212b428a2ac20064607f98740001421b123b8cc00000000190e0883128e8d44e6a0000e102f00005ca3c80dd53147275209f54ae83d44b49c44c320a8000275d0e60001ad80000f44a20549cac6768de2639fac8fe9090dd000000223d3d400000000000000d0c0ac0fb28a23acdc60e137812d839246f00021f4a927c22a61f90bb49c338a8010d4462d43417c400099024594cd27a97e28da4d4f5ea1f2b19ea8a7e9532b801a90986164cd882d20a544000090c00000000014bd1a635f27f0000d3649047e8
  | 24 => 0x61e0000f59df8b0c24f0001c6924c05a00000289267380000000bc200000008a000007c0000430fb600035500012d02ea50c000800028100022186460000000a2c7ea8cd12702087b43cc45aa5b44ac9b71729de88ca197011284d0e20064491d3534c5d40f20e9008c0002dd8dc800023230800000001983ab8630b92a2a03a1cc500c08a13f259c6fc11f1b02350dc09ef15f800138e00000000000003db000042c0004e83632140000693068000035c2b338fa2a000000000002186ac0002e1a68d1986b825289452785b32b2000000019600006490ac1a90001bad41e024301068400000044f00013340004af2460f120002a40ea40002330001cb106c3df00003e800034a1cc8f748126674a8a0dc85250300025e40e200010221f000022b28c90700003ce2bb875c0000000e090a800000049427407963472aa94d535239f1d500012d8732420800000042326622d8000062067813000028447827c01c471022c90001447dc00027853da1170000e049c62252ec19b891a28e3c0a5e06da69f000000058a23e000144509684517613492d66bb08c9c30d5e29c0668e9cd0402527e126c02458c43a9dac80277b303844921c4190238f9c04c3b522383d52f44a934006bcfda92f24ba0700fe94635725346285584041f4c02a4e72b794b89083290ed9d1c56023c00f1f782748191ea934c28e66514f0110c1e17936b190c8f023f1dd13286c68910f60f600dc4dd44596a52f87763560000a945262b08c200001e81998c04fd240543282692ea6e615e24586b247317f8cdc4a025a0750180fe09ae33da4511525c60eb223c1388dd13a93644b60e5381800096a0000000bd40000003e8800031663b4448dd02aca041b3a7a80006e820816dc0000004460634d6a0001a9800067a2e618e1ae40001d107380000000002b3a7e049a82751199f80000000000000f8210d04b196118a75e1401c2c95600044b268000025837f9434c561dc2a580013981f1434800123c003000000094e1e90001ad081499c32d0f08c746d129c00006bc55c3b6966cce00eb000225c54e04e4ac8fbc95c0d21b7a14c0002f74e59f74bf26f800018a935844021b23c800015700000000006693458000e322e10eaa24c0001e136380000000003d39320ffa65300000013028671798d340001932c90000000637000000008a000293915c0003b22390d8407a64d475278c4de90d00000001be01b0d28b40dfc5ad107260cc3e0002f10194000000397151d02e61e337a791374365250a14947804d3ad894821034b47a958064e2a425780e000000011a800088c50e000037800000049602440001370001a1c0008d900020c8b5400006c023c1a85061398adc0223cd26a9edc75a0004e9921800000e0001b240008a721606c8de600b33c00008f60a42fa1d887d6
  | 25 => 0x7a239041ca71073857620390d081a00009188912ee300000000000024109f908087024b30e28692f62de00022344680002e8800136413200000000762f0000238021226810b80000000c340a9534c980004e705880b000013526004365f04bb27ec0000bb1859b140b80002af0a6cf584a002e8b24eb40000001f8d45e9481c42568f9613143687f942e32819d00009249200001e78ad86fa0ef190048c9b34b923e91d24020002404900000039814000081300b00011080003a122991ac7df1de00000000000de000000081227800000009932f995f88bc551027a84522a8d21710b047c86d90e598d000000000000000000904ba00000000000b900000004432d5955800000000000012c8000514218c000000208a8892161350000650d562f43e7800000000000000000000000001e600001483ae9b30e401fd16a80000000000000cf037032a0e987480aa7e52e9253c7684750aa054cb486f623e87748d87c73dc23b47f852203e92dcfec7783ba97f00a823a05a86b0cba9a25072004abe0002180720af214b30b800138066b4b80848cc8000372800000049900013109d41842c0800071400014b0000b8047400000012be0003d205a800000000000008621380580da000000000021bc2a41804b5237c49400000014e80000004551e7072264f24a25854008dc32f82b54720003dd00000000d93478000f366dc44a0000a086323350c84e5254e294000000080d4e2800110e0004128000e985f600000001024dc00b8000e283713b420e946000000000000007240ec1d189de6c30001db000044a1be83b87c626c00002b0f0e47908d8fd800012644802b91ee000000036947e00000009b455400013d800000016e4300000000883000201000000047600014386e914409645745b040600000009f505b000000000000000000000002c709240009494fd177000000000009302f63480000000c4000035b19d0a3e70d0000bb40000003228e50c4c7cc1c79c58e469b42410024000312000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xd802958d13150c9cd8d6e7c00034947a106acb280088000608cca4000001000004815461a91000070000bc43204740000000000262c3a0005000a3c00633000000062b402e385c0000a48200811008602021000404046000a241860050ba5c62dd16254c01466971887158953007091d0621c56254c0146a9718b70589530051a640621c16254c01c2b7418870589530070a1d0621c16254c01c6062dc4705895300718188711c16254c014709161870589530051a660621c16254c0146a9118870589530061a9c88058a6154c0186872201621855300589251620846154c016609058821185530061a1c88058b6054c0126998d8820d81530061a1c8805896054c014709058871581530049a249801846054c01869726006118153006195c8815806054c014699798b20181530070554c435c46050c014a59210d71181430052c640435c46050c01469900857518132007091d0621c55350401a0c4360c651894156f09188651c5425040145593194714c941004ac64081508605040181f7660c75592310070654c431c1644c4014a99210c70591310052c241641c5424c40186b762017254e210061a1ca809d9538800106f985db7254e200051a241321d9534800106d980807654d200061a1d8805c953480011b19720143907100050d652311d95344001854865cd53905100070518c655d231440018958718c648c5100052965c6418a3144001c857418c628c5100042d660641c52044001c147559073440100060d21d6454d10040018548758d53440100052925d641c91004001c85641cc7244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd004008000081a2a572600611815300680aa6c9086b88c0a180341153640435c46050c01406d3886c18ca3128200d0254d9210c7059131
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
  | 10 => 0x124e
  | 11 => 0x138e
  | 12 => 0x94b
  | 13 => 0x94c
  | 14 => 0x94d
  | 15 => 0x94e
  | 16 => 0x124b
  | 17 => 0x124c
  | 18 => 0x124d
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138d
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
  | 34 => 0xa0b
  | 35 => 0xa0c
  | 36 => 0xa0e
  | 37 => 0x130b
  | 38 => 0x130c
  | 39 => 0x130e
  | 40 => 0xb0c
  | 41 => 0xb0d
  | 42 => 0xb0e
  | 43 => 0x140c
  | 44 => 0x140d
  | 45 => 0x140e
  | 46 => 0xb4b
  | 47 => 0xb4d
  | 48 => 0xb4e
  | 49 => 0x144b
  | 50 => 0x144d
  | 51 => 0x144e
  | 52 => 0xb8b
  | 53 => 0xb8c
  | 54 => 0xb8e
  | 55 => 0x148b
  | 56 => 0x148c
  | 57 => 0x148e
  | 58 => 0xccd
  | 59 => 0xcce
  | 60 => 0xd0c
  | 61 => 0xd0e
  | 62 => 0xe8b
  | 63 => 0xe8e
  | 64 => 0xecb
  | 65 => 0xecd
  | 66 => 0x94056
  | 67 => 0x95396
  | 68 => 0x125396
  | 69 => 0x4956
  | 70 => 0x124056
  | 71 => 0x138056
  | 72 => 0x124956
  | 73 => 0x138956
  | 74 => 0xb4956
  | 75 => 0x144956
  | 76 => 0xb8954
  | 77 => 0xb8956
  | 78 => 0x148956
  | 79 => 0x139256
  | 80 => 0xb9394
  | 81 => 0xb9396
  | 82 => 0x149396
  | 83 => 0x128996
  | 84 => 0x99296
  | 85 => 0xcb
  | 86 => 0x10b
  | 87 => 0xcc996
  | 88 => 0x98cd6
  | 89 => 0x1a4b
  | 90 => 0x168b
  | 91 => 0x180b
  | 92 => 0x134b
  | 93 => 0x14b
  | 94 => 0x141296
  | 95 => 0x10c
  | 96 => 0x150c
  | 97 => 0x180c
  | 98 => 0x130a16
  | 99 => 0xb8a16
  | 100 => 0x150d
  | 101 => 0x168d
  | 102 => 0x149316
  | 103 => 0xd1316
  | 104 => 0x140b16
  | 105 => 0x24b
  | 106 => 0x28b
  | 107 => 0x16cb
  | 108 => 0x184b
  | 109 => 0x140cd6
  | 110 => 0xed415
  | 111 => 0x28c
  | 112 => 0x154c
  | 113 => 0x184c
  | 114 => 0x20c
  | 115 => 0x148b96
  | 116 => 0xd0b96
  | 117 => 0x20d
  | 118 => 0x154d
  | 119 => 0x16cd
  | 120 => 0x14cd
  | 121 => 0x2cd
  | 122 => 0x24d
  | 123 => 0x8c
  | 124 => 0x18cb
  | 125 => 0x178b
  | 126 => 0x188c
  | 127 => 0x160c
  | 128 => 0x8d
  | 129 => 0x170d
  | 130 => 0x15cd
  | 131 => 0xcd
  | 132 => 0x14c
  | 133 => 0x134c
  | 134 => 0xce
  | 135 => 0x198c
  | 136 => 0xa4c
  | 137 => 0x168e
  | 138 => 0x2cc
  | 139 => 0x14cc
  | 140 => 0x24e
  | 141 => 0x19cc
  | 142 => 0xbcc
  | 143 => 0x16ce
  | 144 => 0xd4c
  | 145 => 0x15ce
  | 146 => 0x1a0c
  | 147 => 0x170e
  | 148 => 0x104c
  | 149 => 0x18ce
  | 150 => 0x1a8c
  | 151 => 0x194c
  | 152 => 0x178e
  | 153 => 0x74c
  | 154 => 0x1a4d
  | 155 => 0x94b94
  | 156 => 0x94216
  | 157 => 0x95456
  | 158 => 0x95496
  | 159 => 0x20055
  | 160 => 0x8994
  | 161 => 0x995d6
  | 162 => 0x15693
  | 163 => 0x11394
  | 164 => 0x1a5415
  | 165 => 0x1415d6
  | 166 => 0xb8293
  | 167 => 0xb8214
  | 168 => 0xb82d4
  | 169 => 0xb8294
  | 170 => 0x21255
  | 171 => 0x28b93
  | 172 => 0x20b55
  | 173 => 0x2c215
  | 174 => 0x2d415
  | 175 => 0x214d5
  | 176 => 0x219d5
  | 177 => 0x202d5
  | 178 => 0x14c215
  | 179 => 0x14d415
  | 180 => 0x2d555
  | 181 => 0xb8256
  | 182 => 0x21415
  | 183 => 0x11314
  | 184 => 0x184b94
  | 185 => 0xd2d6
  | 186 => 0xc9d6
  | 187 => 0x1692d6
  | 188 => 0x1689d6
  | 189 => 0x25456
  | 190 => 0x24b56
  | 191 => 0x16d456
  | 192 => 0x16cb56
  | 193 => 0x1715d6
  | 194 => 0x1a4ed3
  | 195 => 0x18d796
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1776
  | 6 => 5270
  | 5 => 2628
  | 4 => 56
  | 3 => 5
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (72816+((h/592+packedAt gbK7 (65712+(h % 592)*12) 12) % 2132)*12) 12
  | 6 => packedAt gbK6 (275788+((h/1756+packedAt gbK6 (252960+(h % 1756)*13) 13) % 7652)*14) 14
  | 5 => packedAt gbK5 (165564+((h/876+packedAt gbK5 (155052+(h % 876)*12) 12) % 3469)*13) 13
  | 4 => packedAt gbK4 (4046+((h/18+packedAt gbK4 (3920+(h % 18)*7) 7) % 89)*7) 7
  | 3 => packedAt gbK3 (409+((h/1+packedAt gbK3 (405+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fe03ff803fffffe03ffffff447f3f1cc7f1ff
  | 1 => 0xffffc0fffc0fc03ffc0f803fbb98c9ff798e67
  | 2 => 0x80ffff00000ffffffff0003fc3e0f1e381ff87
  | 3 => 0xfffffffff0003fffffffc0fc00fe03fe0ff8
  | 4 => 0xffffffffffffc000000000ffff0003fff000
  | 5 => 0xff0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x152005282092d2460114a9a9002b130c42b0ab
  | 1 => 0xe662c05b6485461aa40d029a19984875598665
  | 2 => 0x10d56b00c109bcad6ba00534c2e0b1a3815b86
  | 3 => 0x2099b2958b200831d2ca5600ec00ec02ac0d50
  | 4 => 0x44fe3ce6f3ce2f0060841818f7dd0003f7e000
  | 5 => 0x781020070200300183086020ff76ffd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36655
namespace PEqualNP.Outside.L_meta_36655
open PEqualNP.Outside.L_meta_36655.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 56 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2624 : Interval gbAtlas 5 2624 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2628 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)))))) (concat (concat (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))) (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))))) (concat (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))) (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))))))
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
theorem bgb_6_5248 : Interval gbAtlas 6 5248 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5270 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)))))) (concat (concat (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920))))) (concat (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))))))) (concat (concat (concat (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)))) (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072))) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))))) (concat (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712))) (concat (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)))))) (concat (concat (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))) (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))))) (concat (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))) (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))) (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))))))))
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
theorem bgb_7_1760 : Interval gbAtlas 7 1760 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1776 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))))))
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
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
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
def fullWord : Sig := 0xeeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80eeeaeac8eea0ea80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36655.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,2]⟩,⟨.or,[1,4]⟩,⟨.or,[5,6]⟩,⟨.and,[7,8]⟩,⟨.or,[3,9]⟩,⟨.and,[1,2]⟩,⟨.or,[0,11]⟩,⟨.and,[1,4]⟩,⟨.and,[3,13]⟩,⟨.or,[12,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36655

open PEqualNP.Outside.L_meta_36655 in
theorem PEqualNP.Outside.L_meta_36655 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
