import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40525.Model
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


end PEqualNP.Outside.L_meta_40525.Model

namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
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

def SBf (j : Nat) : Nat := [8, 6, 6, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40525

namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4417d53c43e8a2985f943319eaa621bd5250efea8885f14b10dfa0c817e50d07baa7a15f94643eea1887bf438c2fca3206fd0c31beaa2617e534437a86186f50d21fa988637c54cc6fca3996f50f41dfa10817f52443e86208770c830de282873d54086faa1a0dfd5320bf298837c51502faa3205f54a20dea9687bd51d0efca2105f14532dea1883fa20082faa5a05f54242bea9c83de320c7bc87987dc4210dfa8c81be41507eea2986f90310bfaa463bf43886faa8185f15220dea1a217e50842fca190dfd45439eaa661be5050f78a4205fd4930bf28685bd43842fca0216f95320dfa1e437e5390efca0207d50441ef19461fa10042f8a898df55031beaa4857c528437a42205fd4f10ef188617751482f8a0a0df95320bfa96217d51ccafca810fdc8410bfa9841bf411037e86106f8ca40fc88021bd43ccafea9986f50d41be29a837c524c6faa6886f50c32ef99065ec218837ea4a1ef90320be2a421be50d0fbc8618d754f41de20881bc42907de40105754c40bf29e85be4350f7842205f94620fa908433c544c3b862186f14e40efa9a21bc404437a8718cf95031bea94637e511037ea8887790c32cea1a61df4350f7881986fd0e41bea8841bc40843f641885f14c10bfaa4437e530837ea5207bcca20be29e417e539077a86216f50f31dfa9a87be400c2fea2905f14e10f7908437e50ccafca4217714d21bf28e417e5110afaa3986f94b43dea1683bc5150efaa5186fd0a42dea0881be531037e64205f14d42bfa8a81de53d077a87106fd4743ae29a415e53103be8721ef54543df218817d51c83d865107b88521bfa8263bc21903be61185f55120bfaa265bf434c37a43205f95040de2a241de438c77ca818df540429eaa4877d548ca7aa998dfd5131de190817d530437ea5a1ef10640ee19463f741507e843085fd5321deaa6637d5110b7ea8905f550329f28481bc42102faa890df14d40f629221be540cb7ea7205f95020dea1c617d5090f78a4a1df94742fb082217d528437ca810df95130df20421be404437c81987750e32bf2a0617f548437a8618df55321bea80637e544cafca7085fd5331bfaa0637d5110f7c8420df15321bf288617c548877e86205f94443bf28483be311037a84a0f70ca30bf29e817d518cafca208770c831de20441bd41902baa7a15fd4c10df994817e508cafaa7194fd5110be2a4637f5250f7aa7205f54831bf29663df318c67ca8195f54830df98881ec21082fca4197ec4110afa9a415f53442f8a710df54440df21c817f53c837ca2a1ef50e21be2a461bf434c77e86905f94820fd88421bf435037865206f0c440dfa8287de53d0afca7216f50d42dfa18217d53d06faa8887bcc820bfaa0217d5010f7a8790df15332ef98863bc42902fca8215f54b31df2a0617d508c6b8a690dfd4931
  | 1 => 0xd52902fea710ef55332dfa1e857d50d0b7a86a05f94432bea8665f6310c6f8a2a1efd0842dfa8a87bc50d0f7ea890df95230bea9841bf438cbba8618cf15230bfa8a65bd54c42fca8905bd4910be2a465bd43903f480205f54f42ae29a217c540cb7e87905f14142bea9e417e53487bc60985f94020bea9a43bc54486fca218de14121f7102417f54ccafaa3106750e31df202617f53442faa910dfd4d20dea0883bf52102faa7a06f50c43ef21887de324cafaa5886f90a41fc10621ed4210afaa9886f14a40bfa9a836f524c3bc6298df94030bea9c437d540877aa1a1df54810de98881bd401037880907ed4121af29e85fa300c37880085fd4121bf29483bc42106fca318df94730de2a461df53482fca6215f54910bea96877f548cae8a2985f54e20dea1081bf430c37ca32057d4d21cea1e617e518caf8a4a1df15030f719065bd43d02faa7085f15132bea98839d430c77e8610efd0f41dea1c857c53086f8a690df94243dfa1a437e53d067aa9995f54743de2a221bc43103d8a4986fd4440bf28843be50103dc84217ecc230de98c81de320c27ca998f74c431be29221bc439037e8620df94f20df292877e540c7e8a2904f14143eea1a619d53102faa9984fd5130dfa1c87bd43cc27aa6205f94032be28a61f421042f8a4a0efd0d10bfaa0657c53c86fca410cfd5121dfa1e6177514c2faa110efd0e109eaa6417c53c433a86197dc86219faa461f510043f680a05fd4810bf29843be405037c80906fd0d419e2a241ef324cafca12079484219faa241be40042fea7086f90840bf284413e54c42fca1a1df54041df2a6637d50cc73ca6206fd0f32bea8c617e53902fca418df94021bea94817f52502f8a4986f50f10dfa00817c544c33ea6a1efd0a40fda04817e5190afaa010df54b41dfa1865bd429027aa7204f15121be2a0637e52d037a86996fd5230df288817d5490378a3205fd4142bf296217e51106fca710f74c832dfa9881ba50102faa7187b4c832dfa1c637f534877ca3a1ef50f20de206217e5010fda40106fd0c429f2a661bd32902fea2987bcca32bea9c857b50486faa1195f94b43bfaa6217e53c87be65194f15110bf294817f504cafaa921dfd4a10eea9e837d54cc6fea810ef50e32de29687f9300c2fca898df54840bf28083de328c67ca9995f94a10f690843be4250afea790df94740ef980617d5290efca9086f55330ef21c65be429027ca821fec8120bea8483bf438837a87a15f54a41dfa0c837f54082faa0195f95231dea1085f7314c6fca8196f4c840fd900217e544437aa6205f14131dfa1e63be521037aa2204f94343bea9c63bf544c37aa8185f94843de20061bc40c82f8a7105f15010fb98821fb304c2fea6a16fd0240be29a21be32103dea4985f55230bea9087bd43086fca118df94810f790
  | 2 => 0x210149203c000000002c1c00010000010c000000022401a000110580000000010d5078000000200c050240b00c1c03c0100001000060007a0600b03004014890740b0140504a6103400040590200c020050080504c340046a04400008020f4000340d020030002b0241011803028930fc0504c01018400440303c1104c08024070040101c012b00e074020500000c0002c0009c020640000c00000180080100001010030e40e02c1c000003283d0546d08c0000c1702c000180000c0001c01000e610cc5010080000a0500000402180510000404c0002c0200c000040115c7e068149fc08000090680b054390a00106c000b00642400000000240906800248950000c104a4000150001f0180007402000950100005084020673a4970d81a000000002f0600500008000060381b008000302f00013000353fd42360000080403006000000001f28015000040240007c370000f3982d0001006c16004000105d0181000000000620004d11c010137881184f55030ee980617f540c378a6204f55031ef18c61bf4310efca998f750f30bf2a083bd434c6fca910df54643f790c43bf4350b7c42205b14910bf296837c544877e87205fd5220bf29c41ee218827ca9906f0c640af29e837c540837c81105d14520df18c817d5310afaa9105f55020bea9881bd43082fca3a1df54343be29281ec320827ca0205f94f10ef298817d544cafea2a15f55332beaa641bf31903ee63087bd0942bfa98433e54087b863185f94a43fc28243bf211037a8720df94230bea96617d52886fea0a0fe48020de2a261be54cc2f8a810df15120fa18c21f8200437aa818df14121beaa483be54c423aa6207714d10bea8c857c5050f7aa9906f94e40dfa1c85dd53102fca6905f95220df204617f544c3ba86195f95232fba8a41de434c2faa190efd0b41bf28c836c524c2faa420df95121bf298217e51886fea9187ec8220bf2a6217c54c437aa8197dc8521bf28485f621087dea4886f50d30bea8e81bc40082fca6185f14520bea8c217e520c37e87a05f94031bf298637e50042fca6195f94a31bf290817f53502fca110dfd5121df208817c53483bea690df54d20bf2a021be21902f8a2a15fd4941df294817f5050fde85215f14c20df2a6657e53102fca821df948419f2a0617d54042fea8905f94c43fb90c217c504cafaa7205f54742df90c81bf50d0ef8a4085f95321dea9081bc404c2faa610e750e32fca00813d540cb7a86205f55231dfa12837e52443ee8320f750e31bea9e437e52cc2fca9985f15330fb98c637d548437aa810df15320dfa0883bd5050f7e87885f94a32f7108417e54ccafaa2196f14743bea8861f641106f8a8885f94630bfa9c41bd51902fca5187dc4010ee29a41bc511037a86085f94a42df20041bf434cb7c83205f55131dea1a41b
  | 3 => 0x2b98a000010001c00821064494f81f00000150280301601000214000c8020140500c810000203800294000500b02c12024bb0100c1fc1905
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x7430863c6055032dc147204825d6315020c7989531031e6154c40b9d95210871f6554c408fd954310f1c5350c21cdd44404829d63103208fd94400c23e6414f10d9148514c31f5350d429718d520432d4314930c750d508c71e53940409b189544c6786054d21f818121086f061480209dd95310c63d65d0c328fd9743c429c6050c328f59253c823c6454a308f58f544426c62551108f59253083585314121cb14a404c23f6454032c758c544c3385414121abd895150e3d6414b10c7193534869f63546409798c520429f6354a408f594329023f6454321b9185200831e5350f218f191508c71f548c630c798e540865f6355120ae98353103676548421a798c53103986050d308f59543c833754d4530c758e54c431f64d4d10c718953102756115020d514c514831d53108408f98254cc72d43d4930cdd0c51483954314530e694e501023e65d0d218f180544423e64d4131c794d438831c54d4d20c7193534431d5350e42c7d85531031d548c8308f990538871e6395031cd150514825e63951108f58c54486766114c208f99352c42986050d309799453442bb604c440a758c40c425d63d4a109798f52c4367521453097d8d520423e650c840c754d438431f53d0d20e350c524c2ac6254143a758c400438f434c832b9181210863d64946208fd9150cc63d63550308fd95430c29e61d4d439dd85544831e6414d10cb153524423e6494820cbd4a404c25f6354910c754d52103732114121c794d439029d63100208f992538836551084209b98a524423c6055332cd50f514825d63951328f195211033a60940408f992538867b6544010cd153514c31f5414d219b988548c7c763484219718d5190ae462440108f982540867765484218f594400c23d65cc640c715353486ba60d4a40c7d935348795438c431c794d43d0a3d65900309758e524429f6550c32a7590328c737519012097d95300c31d6414d10bc181210874c53d49108f992528c31d6154c408fd91528c66e62150108f996404823f6550c218f590538832f54d4910bc580310431d53cc440ad98750d0e3e60950319bd8953442b46154143c714f43442b761541439758c540423d6414f108f590524c63d6395320e9d0d210871e6395320e6d0d300c31e6414d20a798f429029d6490c329ed95401026e62951109dd85544cb1d5394440c7152434c23c64549108f590530831543145309d58753c82ba6014e40add855250e3d650c6408f59421102756195120c794d431031d53948408fd91518c31d530c8408f593504ca3c6454420c750d500ca5d63951219d594310427b60549108f59053c865f654c832c754d511033754d4520a758f4210a6f6255130e350f524c25d6590c31ae983539023d65d0c31c754d430425f63551108f980544423d6494630c714f434872c5414910
  | 1 => 0xc27b654c030b358a430ca9d6310030c754d321031d5350440cb148404c23d6494c21e3d89438ca5d63d4b108f597311031f6550e318f99053482ac6254543c750e52cc23d64d41218f590538425f6550c43a7181438cb1f5350d409758c548829d6490c31ae181434c32f43d4930d3548320c71e5350e10cd5445150f1e5450f30ab988511031d530c440ab58b50d0e3d6590c409d58653482d5610c831c754f42103564314530c794d430423d64949108f191500c7a840480209d986544831f540ca308f597430c31e5450c31b5185300c35453841109d586544c25e6394910a758c511021d63950219e982534863d64d4f10d5d4c514833a60d52309e59420042ba6014440c7d93534831d5390c40e550f514c29d6395021cd54451d0fa55448421c750c514c31d5350e40c7d95430c73451101308f99253487c46348421cd1535148395430c4108f592520831d54cc030c7d4d435065c63549109bd954210abb6048440a798f511034e4314930c7d4d434423c60553318f992510429e63d0440cb50c524431c5414d109b98b53c431e6395032a758e54c42cc624c030c7d4e404423f6590030aed81321035453d4520ad984521036752d45308fd91500c69d6310110c754e411023e64d412197994534863f6355310c754f42d06ba60d0d309ed81534869e63d4840a798c511025d63153218f990534432c5290110c7193534825f654c4319b58b53c423e6510110cdd0f514831d63950218f997329023d65cca409d185534838d430ca209e181544cb1e6414d218f994544863d64d4131ae181438c29e62d4d438f992518823e64150328f590520429d64cc631a758f429031d4394832ad185435063e6095032e9191210871e5350c20ce980548c26f6255110a758f511031f6550d308f992544823e6415030ae1815150e5e63150209d984548ca3f6550040ab98851d0e3e64d4a10ae983438c31d5310440c754c511023c65486408f59743c823e65cc6408f990530829f6550c31c7d50534431e5350f41c754e321023f64546329798c54c871e6454c40a758f4250795430c610a758e400c2756115232c7589531031d540c4309b58a544423f6454332c794d438863e65d0d10b8181210873b54141218f590534423d6494e209798e5348397434c4319b588548c6ad6214440a7d92304c33943d4121a798f421023d6494c30a758f419073543145309b994524425d6395320cd146404c23c64540219dd85534431e6454f418f992530871f5350f108f596540ca3e609533297195434c29d6310120e9d91210863c64540328f597430863e65cc840cbd48404c31d43947309b98a544c23d6414e218fd91534823f6355030c754f511029d63953208fd9743c82bb60486408f58e54c431f5350c21a798f419023e6494c109e580530871d6414d208fd9
  | 2 => 0x63d0b41a75835350e3c6454331a7d8d211025c6354021c7d4d43c83976150e31c7d4f434425d63951318fd8d540863f64542329b98a534429d63902309718d544423f64542319e181544c65e6395120ae1815250e746154032c754e42102ac6250d42c754d401023f64542218f592534425f6354021ae983521023d6414c218fd95411063e65084408fd8d54c82b8604c840da14b104431d5348440ae18143c431d5350c20a798c521025d6395120ae181311023e64d4f20c7552310c3375110130e350c320829d640c8318f191520423d6494d21d3d4f524431c5310120ce50c50486ba6014a40a7593320cb1d53d0f418f99053c863d65d0f108f19153482ba6014c40ba18121086756114c208f994544c23d6414d218f992524423f655084297d8d529063d6494f108f58e54086d86050d30ae181219029d6594c409ed81544863e6414b108f990534871d43540318fd91520431f548ca308f592530ca3e64d4132c758e54c823d6414d208f992518c2e86244010d5d4f514825e6394d218f994219023e6414c218f99543482b86050c208fd9153486796094d21ce993504863d65950318f990538431e6454f428f592538863e6495130ae181430425c63551209758c520431c5414d219b988530426d62150108f992544869c6050c31ab98b50d0e3e6494c32ced53504863c65d0d21c7195438c66d6214c10a758c521023e64951108f594219034c5388120c7d95438ca9c6050f30c754d421029f63486409718d529033751901309798e54c831f5394e408f59253c872f43149108f59053c831d53d0c42c754f43d0a756508410c7181531033543d45309798e544866d6294d108f181540c69d63d04408f596540871e63953109d986544c31c5350d208f197434825e6394d10b958a210871f6550c32c714d43c823d6494a308f994329023d6494c31c750d508ca7860551218f99353087995394040ad584521023e6494a109799453482776544010d6d4f504871f5350d219e982544863e6510130c7550320c63d6494a10d550c514c23d63d5120a758f4290a5c63551218f996404423e60151218f995434866f654c8328f19153486746155132cb5485250e3e65151108f191534426c6254d108fd9543c423f64544208f990520431f5310110c7590534869d63d0640b518d100423e6414f20cb50f524431d4394831c714e40483374314530f8084200431e5350c30c7185531031d5350e418f59352c434d4314930c754d438831c6550d30cb54852d0e5d6395310ae983511031c5350d41abd895050f2f5290110c754d42d076452d45308f596421063c6454a31c754e501023c6454630d3d4c52442ba6014840c7d50534833b43d4121cb148404429d63103309798e540863f654864097d8d5190a3f6454a30c754f401029d63d0840cbd0c524
  | 3 => 0xd308f990538825e6315220d6d4c504866d650c8209b58a544c3946150e3197d8d529029d6310210ced90504863d6414c108f992530c71e63953309e582544865d6315210c714c404439b6050d30c7d4c404823e65d0d208f58f544871f6550f308f59253043645284110ced0c504863e64149319798e54c431d53cc8408f992530c23e6494d20e9484211023e6414c108f590514ca3e6494e10a7d9543cc27761540328f994544829c6348440ec101100423f6454910c714d43c426f6548421c7d53308c23e65101208f997435029d63d0441c7d53534425e63d4a10c754f43d02ba6014640d9146204827a6014c21c754c52103375414530c7550320c25f6354420c754f41102ad62d0c42e3189438ca3d6550c21ad58750d0e3e6415031ae983519025d6395110aed815250e3c6550d108fd91534432f54d4930a7592434c31d5350f21b5586430c65f6354640c7d53534863d6595030d314c5244354518c130a7181438c63e6494f208fd9543c823d650c4409758c54886cc6348020cbd50524c23c6550d21cbd50524429d63101308f181540863d64944108f1954348398404c0309ed81544c63e6494f109bd89534829d64cca328f594321033743d4530e950d210871c5350d21c7951430ca3e60d51218f992534431c5414d208f99353c423d63151108f191508863c64543329b189500c79943cc130c7195438ca3c65d0d10cd150514c31d5314c40a758f521023d64d4c218f597321023e650c6409dd85524433543145208f592534831d53d0c41c754d43886746155120ae181211023c64542329dd85534827b6055132a758c408833451901209798c548867765504419b189544c34c528c130c754e211031f5390120a758c408c26f6255131f8d81210869c6354a40c754f211031f540c6308f19150c865d6590c32e9484219031f5350d20c754d311023f6454021c750e510c71d4394a31ad98452d0f3964d4121d9d4821842746155130c714d434432c54149309bd95200825c6354a418f995434423d64d4f20c7d4f434871d548c831ce153504872f43d4910c754e311035853d4121e350e320ca5e6315030c754c431023d6494e108fd9521102ad6214743cbd48404431d544c030c714e404429c6348640cb153524c31d5308440ad58452d0eb46154943c714f434831e5450c43c758f548c36552084108f99731103a654484219e596100423e65901309dd85544c23d6550f10c754f43103386414121cdd50514831d63152308758e54c825c6354640c750c524c23d63151208f99253c871c5350d42c754f521036a21141219d98753c823e6494c208f191518ca1c6550d3097d8d544867b6548020ba58032082b86050f208f990514ca3f6550c32c750e518cb1d43944328f99431102b561d0c41c7d53534831f6254c409d986534829d
  | 4 => 0x2200b500040a990d100400044030000502400078380002508c030e52a0140f0241e01c0d0200318c130cc6608026010001840f00005894130080c03c150040801c6400407024010d000000120005100c22158070041098c010040030c1e0340d02c0019455004650e003000074e415084024ac080000d04a910200011c01042650c800004000d81f000027644500874008150050600074000271500007810004000080504430000125b81d01805000090305b1b01a0101709c283200c004720fc000000005c21008030800a0a43f13c002b80b0102902c49000200041b000410000007c00175cc0241200019004000b432014050a00b014cc000a601401000011141b01018064174fcbe0000000afc00c0e004140280000c0b0404f0040308c0019066000d201020000e902c09004000000701c001380a038000000000006130010080a0346200c00004070000211c170140109c5801000184630002a090530405e0345c088030d0081ac040400c0141b00c00004de048003dc005b8133b80103f1e6054c40a7593310c6bb60545439718d51082766115020a718d519031c54d4d108758e54c423e65d09418f195434c26f62540319798c548423d64d4a109758e540865e6315010c350c524c23e65d0d30cd144404823f6550c318f990540869c6050
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x7b020900050d00010c462985082402240206001e0c040b0500000104081c093800070000410920060d16000b00120200030f060502000300101c000b0827a2ae3322a6206195318121102c43828619041985942108010c2ac6288809869063101100420eb9cc928821075d85310110c32c7306a91860d53588511030aa18c2a8065895952108440a30e0a1aa018e0d43189500c687396a6a1e21a85506048421c2aa6b08a4205907050f514c20ebb0a620241451c14314530d46e83024210d85739512108698382a228a87435ca6454f4183eeda9880905087050c524c30ca98c0a1841075cc654844083ae7320a5884e07158032082983828628a61681c12108640a2ce232a871960d63d484044312a92c229687291d94348421c1ec8294609841d73180544430d3a8c0a1a61c41c14314530e0a86290a29841f7359421902c438286292614a1c14314930c32a630286085157199153d0b8438286292618654f604c440838eca9a4220591731011004351a18c090843075cc6055021d40c83024210e0d63d48404c20fbaac720061461c16254c40d40c2202401041d73994211020eb98c8a84438654f6048440a30e0a18a2986c063181210870bb20a31826183595430c820a32e6320a090d907050c514c312b12a228e87521c14314930a2ce3b2a8698524715485250f4431080980614a1c15214943a1ce5b2a869861563d444048287b92c2a9881459c66454c40c2ac230aa620518705855310292392a228a87681c12108440e26e0a18a29870b7050c524c28c3828629261451c56254c40870e0b2a8610e156550c310420eb98c8a8643075d46348440e0aa6908422061b5318143c82a83828628a61465d4404c030a1ce432a8718c1d7598f421028c38286a8065621c143d4930a20e0a18a29851975d0d300c292bae869084307ddb531011083ceca9a42206a062101100420eb9cc9a8243459c75350f20d2286b00620861563d44404c270392c018821c150f521453083aeb31e82205197399350487503a0c09084385550614c030c1aa8312601849a75181434c361b18c090843a8d906048421d20c2202601841d7399252843512a0c090843a850c6048421a18e4b0aa62041d73992520830aa9cc229081075ce6494620d08c831a4210e1953d813210287394c8a9881641c1430c410a1ae5322a62060d63148404c30ab18a2202418358c5210110c36a63028788688631012008306b10c4a988145dc56254c4083ae7306a890c1e76d4d43086863828629261465c05350c21d1286b0064107054314b514c2c4b9880900418354e6214440
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x8828127000c0100026b220000010000000000d01531c12108440a81831d06048421a04825846154c40b008050c52d4530c81431c9600c4109048754d2108440b008050f5214530b008050c5214530c81731844048020c21651c12108440c09651c1430c820c81431c5600c820c81731884044010a818395060484218918718c4044010a1281d4c6050f20a04815886254c40a0a82d4c6050f10a21851d06048421a08805886254c40a2185d0c6048421a108050c6154032c11651c1430c410a088050c6254031884865ce54484218898718c4048020a10805846154c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 27
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
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/337+packedAt s0K5 (21654+(h % 337)*10) 10) % 802)
  | 4 => 2*((h/308+packedAt s0K4 (33554+(h % 308)*10) 10) % 883)
  | 3 => 2*((h/62+packedAt s0K3 (7056+(h % 62)*8) 8) % 144)
  | 2 => 2*((h/30+packedAt s0K2 (1620+(h % 30)*5) 5) % 27)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffff01ffffff03ffffffffc0fffc7ff1ff
  | 2 => 0xffc07ffffe03fffffc0fff03ffff07ff9c7e3f
  | 3 => 0x1fff80fffffc07fffff03ffc0ffff83fe78fc7
  | 4 => 0xe00000fffffff80fffffc0000fffffc3f80ff8
  | 5 => 0xffffff000000000ffffffffff0000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x24450a211c48912200b2cb4512c04a4429b0db
  | 2 => 0x48931452243922452c055522a55904a994562d
  | 3 => 0x110a269448907489555026a889aa9032c68b46
  | 4 => 0x9c2c58e8912240ee9a6980c30e34e703780db0
  | 5 => 0x1e3060f0e1c3870fe38e38f3c038c623ff6000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40525
namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1300000130000000000000300850000bd42bf41df30de31dc31be40bc40bf42bd41dc32de32dd30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xc0008041425aa5a0cd547429aa888195410c698a4985514530a72946356518cb1a84194b54840
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/32+packedAt s1K4 (192+(h % 32)*4) 4) % 12)
  | 3 => 2*((h/10+packedAt s1K3 (270+(h % 10)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 3 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 4 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 2 => 0x48a65910ca5138658321a3445642a85a694652
  | 3 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 4 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40525
namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x10004000020000f421dc32f510dc31dd30de31f710de43f721dd43df30de32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x80008eaa0651d54cc2c8a4885514543
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
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt s2K4 (192+(h % 18)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s2K3 (108+(h % 8)*2) 2) % 4)
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
end PEqualNP.Outside.L_meta_40525
namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x24090031000f421f710de32dd30de31dc31f510de43dc32f721df30dd43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x208eaa0651d54cc2a8a2a1d914910
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s3K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s3K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf80fc0fff03f07fc3e07fc3e07ff0781b3b3cc
  | 2 => 0xfff000ffffffffffc007ffc007ffffffc3c3ff
  | 4 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10a10804608221004628804a31484c94141615
  | 1 => 0x32629948a3942b2c1aa3a42c52d9450cb1b2cc
  | 2 => 0x4144a2910528845581054a8084a2926942c16a
  | 4 => 0xe58b3ce24a0eb79aedb06229273ce431fc03b0
  | 5 => 0x860c30c38c30c6e331c67331c0308041eb6800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40525
namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x130160b18a002181140080000380382fc21fd31ff41fc42fe20fc20fe21fe10fd41fe41fd42ff43ff42fc10fd43fc40fe40fc43ff30fe30ff10fe31fc30ff31ff40ff21f710fc31fd20fe43fd21fe42fe32f510fc32ff20fc41ff32fd30fd32fd10fd40
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe657c54c86fca82077cca32b6a9087f5210877e81205714d10bf29885f642442fea2905f94210fba1e217c5150bba86997dc8310bea90817c53482fea5885d14543dfa1a85dd4310ff681206fd0040f6a10437d510cbea40885fd4d10be292837c51502fea4987d88110f690041dd320c7dc84995f94410fb98a217e530c2fca8885fd5232bea9c61ed32483ee6088774c030beaa0217e510c6faa610fd10431dfa1e85f454442fca7215f94e40fba0a837651042faa990fdd0421be282637e5210afea610fdd4f10bf29e83f654c43e880885f15332fb90a437c53843bc621877cc930faa9a217e54c83ec87885f94a40dea1681bf4310e7ea888774cb30fba8a657c52043bca6205f95331bfa9421bd540c2f8a818df94b41bfa8a817e50d06fea6106f55032ef994637c54c83e88398ef55331fb88021f651082faa6905f54442fba96217d54cc2fca1a15f54b41bea84437d51083be8721db54840fba0621f631c42fca318df94321af29885bf42d02faa5186fd0d40bf29065f530c42fca521f790d30fda0281f552442fca3a17d50910bf2a0637d54cc6fea4a1fd88710fba0e437551083de65197d94430faa8861f630442faa120fb50932afa9a213e54083de4210df55121bfaa621f5518c2fca8995f54d21f7290617c54c43ee84887754f21beaa421f541106fca898fd90110fba0c837f53486fca4207b08420bf284857e5290afaa9885fd5010bf28021ee32c82fca420df94f10fba8a85bf43907dca421df94743fba92217d54c83ea42885f55243faa0a21f754442fca990df94e41bea9441fb308c2fca4185f94f21bea96617f534837ca998fd08510eea1e657e540cbbaa6205f54430fb196213d540c3b862185f94240bf284437c52842faa418fd94f10ef21c63f551882fea9107b4c821dea1e85bd4210afca0107ec4110bf28861f531443e885886f90942beaa2657c544427aa8197d94440ef99063f551102fca620ef50d42bea9e216d52d06fca618dfd4941bf28465f653443f220087dc4210beaa2637d5010aeca2187754f41faa0221f741442fea910f7cc030fa28a87f431c42faa918fb54b31dfa1085ef52443ea87887d55310ef99661f754c43e88210df55130f7216417d54083e8a9887dc8510beaa665fa40103eaa3205f54d10fb20a21f651902dca4185f54910bf2a2617f54087e6a0885f95332f7904417d51cc2f8a60877d0d43f3a92217e53d02fea7085f14c21fb216217c53502eaa2185fd5130f7194437e53886bca790df54332bfa9a85bf4290afaa018df54c42f6a1085be540c2fca9197d4c910bea84657d50d07ec6218fd48310d6a1085de5310beaa7887d88310beaa4857e500c3e886887dcc710bf280837e518caf8a998efd0c41fb98621f441c86fea6a0df94b40bf288417e50086fca8217750d30
  | 1 => 0xe54483baa6105fd4c10bf288657d51c83bca6105f94441beaa0617c540c3e860885f94c40ee99065dd430c7ec4210efd0940f6a14437e50906baa7a0f78c130be282657e528c2faa5a1df94a32b6a9061bf4390fe8a6887bcc932fd904417d540cbee83886f50a41fb992217c5050eeca3105f54f20bea9c837d538cafca721fd4c710bea94837e53086f8a4885f54343aea9e43775150b7c80a05f946439eaa6437e51cc2fea898dfd4142ef18c619d4310fee43886fd0f40deaa041bd43106fea2a1fd94b10de2a221ee21486fca1107dc8110be29c41ed32c82fea4a07b90920eea1e617e52c42faa4085f55110beaa443f552c43da85197dc8621ef988637f524c77c83205f94910fb98843b454443ec83885f54610ee988637c53487dc40905f94e20ef98461f743442fca8085f54630bf28e657e50ccaf8a6a0fdcc721e6990657d508c77882207d44010bfaa643f443c42eaa3086f90541bf28687ef20082bca6207dd0110f6a90617d51ccafaa420ddd4543fa99621dc53442fea918df54c40bea90617c52502faa6106f50441bea94217c5250fdaa421fd08310ef18a63de53d07f640905f15220ea29a217e53082fea090df94641bfa8a85ee32086e8a2995f95221fb21a217c5350ad8a4887bc8621be2a661ee52102fca1185fd5210bf28065f431087baa6215f54740fd080217c53c42f8a8106fd0641bf294837e52d0efca918fdd4d10f7296637c54887da84907d95110fba822175518c3bc8621df94443fa982217d53d0afca7905f54041bf2a243dc318c3ee8398fd88510fd88421df320cb7ca8197e8c030bf288857c514caf8a918df15010bea8487bf54442fea0a1df94640bf2a421f631442faa710dfd4131bea8c81bd42106fca5085f54a31f6994437e52042fca220774c930fa20e217c53442fca6195f15210beaa465b754443ba6518df94d21f6a96833e54c86eca3206fd0841baa8c81745150abaa6205f54e42faa8841ee21082f8a0a0df54c41bea96637c544c6fca118dfd5031bea8065f7314c67aa998df54f40bfa9a81bc41902baa61077d4d10be2a0655e530837c86a1dfd4e21fb28c617d51103d843107d0cb10fb19221f453c437ca8105f54043bf280877e52082fca6086f50f40bf288437d53842fea7107ecc130bf29e853e54cc6eaa2205f14530f7190657e50cc6fca810df54742eba9a21ef4290aeca2205f94042baa8c417c50486faa1215f94642bea8c853c54443e861885f54620be28a417f54483bc64997d10910ef29e43f651882faa7105f950439eaa0417d54882fea4085fd5330f7a1285f6104427ca8195f14543af29e837d50087ee65887b94b41bea90877f53c43da4210dfd5132fa18a217c548cbea86885f95310dfa08837e5310edaa598df95030beaa063f75150efca518dfd5032ef21
  | 2 => 0x1760f0100900202804018a60a0000001e0100e01002000d60e81c058567002019000090100d81a1f1680200601800260001198003302000000280200008000040080001008010040903038800108043702e690ce000000280a0e0000300429a88010620005202804008040002c4a00c0216a0800406004038120009e03000010080a8081000009024010130607e0581c07070008660c0000088845028010dca885a0000c89d4a3d0500500600802328108d0420f9980800000808458020e006068061b80e0700e000040000037800070320b0005f03a0814402814018ec00808000020100c010120100a0004a08800400fa008009f0920180a00076048021503c0181413816038d21880c04a9a028000003c0000c458fe0a01a058100082a0100c048140000e090003381c030080300211278000860d8000b8040104a0283a0380608004a413e01002050520980400042078200001400000000207a01e2501a03004098a808802020020286803000068001aef50d40b7296837e5210f7aa990fd14910bfaa6416e52103bc8618dfd4530fa98863f7318c77ca990df55241fa206217f53c86eca2107d0c721fa102217d53043ec8220df54321be29e41f940102fca3187d55110f721043de434cafca418fe4c030be29e43ee42886fca3a05f54643fb292217e50102faa510df54342f6a1641f45150aeca3185f54e40bf29663de43cc2fea8886f50940beaa043dd438c6fca9106f50e41be2a4617e51882fca410df54e31bf28e417f52442fea9187b88620bf28c437c52c42f8a8986fd0a41f6a90817c53082fea998fd8c310bea86637f50506fea8185f14931faa16217c54482faa221df94243aea98857d54483f440105f54f21f6292217e54cc3e882885f54632fc900417f54082faa5a07d14532beaa4617e534437a80205f15132dea1887f521c42f8a710f7cc631bfa9e417c524c3c8a4887b8c920bf2a4617d549037c82207dd0b10bf2a0837c54086dca421cf95030be282857e500c7e864887d90310f72146577514cafea2995f54a40faa0e217d5290efaa5885fd4132be2a243f7410c7ea81885f54f41bf2a0417e53842fea9997d08710f6990657d51d0edca598fb90842b7a92217e52cc3e8a5885fd5121bf29a417
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc424436452cc510d9549511033554107219d5845050a6c62546409d984504ca6d6215330b958843443576154f219dd8552cc23e64d45329d987520426d6214c10b9185424cba754d49109b98853502776550441d354f200823f6454d209bd954210a9d64cc63197d8d544823e6414810c350d5210f2e5494830f414f5044355510c630ad99253442b6640c9109798f54c86756194010b558c40c431d548c4309d594310867465485109b195424ca3d6414f209dd85540cb4d3254032b9189544427661d4e209d584538832c5450b209d1855310a6d6215030d9950524423e64150309d594410c7675208510cb552520c2d76150c319d997414431d53d0842b558e52c423e64949109b98b54cc74f53d4910d958b5150f546154c429d18553c8276658c110cd951510825e6394821ad99020443655254430bc58353c435453d4110c755153083b354d4110b998b410c65d63951109b988548425d6394a41cd95331c874e53948409758f5150ba46150842d354d200833551904409b58853843646254640f14c832c43646154843c754c411025d6315021cdd53504433564d4532c754e411035543145329758c525025c6354910cd58454442cc6250d32cd191518c35763546409758c54c823e6414a108f99053842746550b10cb95142886ad6490842d3949328c74d5354b41d394d52102d66310b109b588535038d5350842ad992524425c63546409d984548826d6295110ad99321c42756195132cb949429072c5250940c7550310c35643145329ed9510042b5640c1109d18554482b6640c110d554e51083545314910b5185434ca6f6548421b598f21442b46150f429d997214423d6414d20f814b504431c5450f32b9189534427661141439b189518c27a6014c21ad99253c426e6215331b558e544426e6514910d354e210823c6454630f14c831086b564cc510b558f410c7376155321e3551320ca7b65480209798e52442b564083109758e544c6766115230d314d32482776155132c3551320cb0d53508428f99353c86766194232b958b41c43c7614c832d914b504427561150208f59053882776154f20b598c40c431c5414d109b58a544c7a542109109b988548c26e62951109d195424423e64141329b988544c34d544c832bc58352c43346155032c715143cc23d6494a319759653082f16014b10b518d52443645314910add8542107576154f419b588540425e6314940cd15241443d353d4110d518d519025d6315321d5994534425d63d50209758c54882746154f408f59253c43555354440cdd91518c34d528c4309798c54842e56295110b598e52442756014543b598f41c86ad64c86218f59252086d663d0710b9994524427561d52309d98454043725144010a7593310c74d53508429d987540c23d6414c109b98a54c425e6395110
  | 1 => 0x82d66394d10b998a54c423e6414c20b998b41c426e62150309d984540c34d4354843cd552510c23e64948218f99253c42ac6250d42b518d5444274654c5109d584548838e5350842d558753443545394910d5d4c31442756194042c7951438c67761551219798c54c823d6494c319d18552cc23f6550441cb5095010a3d64949109d996204433743145429b988540c66d62d50308f596540825e6315010b358f21087c753149109ed81544ca776154f4097d95300c2b56494b10f14c832442b46150d42e9153524429d63d06419dd9543442e662cc710b958840c42766114e209798c540c26e62949109798f540827b65500409d5835150ad66310910ba58021082b564c87109d987548ca7661d5020f1185320cab665151109d584530826d6294e41a758f411063d6414132b598f414426e6214143d594e51103376155331bcd8152442776548421ad993310866d6295121d994841cc67561d5332d9d89518c2b664c85109758c54843355410731c795253c865f6550c43c755153c865d6395221d314f5244275611523097994534434c524c9309758e54c42f26010910cd587544427661148108fd915244335545442097596430c73464546209d19543c42b564949109d5865090a3d6414a10b998a524433454cc510cd551510c2b564081109d587538833654944209798e529072d5210440c714d4350b365454430cb54a411026f62546309798c5050ae66210f10ec153504425e6315120b598c404423d6414810d994c524434d524c030abd954210b6561149108f59053c872f43548439b58b5150f2f54d4910d558f5150a3e6494a319d185544c27761551319b18954442e562cc710add91524432c54508219b58a54c427560145429d994304435463546209d99731442b66494b109d185544cb555394440b958b414425d6314a10c754d401027661940428f990540cab5640cb10cd153504434d32944329b988530833454c8510e350e5210e6c6254d10cdd9151882756510421f44c0304438d4350932bcd8153442d66514d108f992530c65e6315220e9d854210a5e63951219d586500ca6d6215210cd15053442d9600c430d9189518c3954310f10b598c20c43565414d109d5865010f4d52cc030ec500404423d6494e218f596540c36551884209e596100436652d0731cb55021082766115020d9949511025d6314142d514f21442cf654c8329d5835150f65529443097195434cb1d54cc832d9d8552cc6d563c87109d986544cbc453d4910cb552320ca746154843d354d521023e6494d109d580514cab664cc5109dd95310c74d5394840cb151428ca5e6314a10f1d4f52442e76150821b598e52c427561943329798e54c4277654cb10bc98043443345414910b958a53c427661943328f9905408276659011097d8d51902e6620c110b558
  | 2 => 0x54105108f99053882e56210f10b358f218863e6414c109b58a53442cc63509328fd954210b2d54548308f99252c425e63148109dd855210f2d5494b319758c54482f160d5310e5153534425e63150219b988530431c5450d32cb151424827661d5010b598e544423e64951108f596540cb354314542d394d328866f62551308f99253486b6640c310c755253c874c53149109d9865010f976150c43b598f21c43565310721d594e510834d5308420cd994544426f6254640cb55152cc6b564cc710d3d51320cb2d54c8020e5d50534431d53d00409798f5150b665294440d9150524423e6414d209d587540c23d6494d10d394e52d07676154843b518543ccb2d5250040b9988434423d6414e109718d54442b5640c3109bd8954443e352d411097d8d518825e6394b10c9150524432f54149109d987530431e5350e419dd855310ae56294d10e950842c427661d52309dd9542443645210510a75924310e7761553309bd89534423c6454d108f99053c825d6394821d514c21442e562cc510d314d32c832d4294442bc58254442746550510f114c524423f6454d10d9d8951902f1600c9109d587548ca6e6295131b558f41c43345494910d994a510c2756114132cd152534423c6454d209dd9543c42b66495110e550c43443576154c428f990524c23e6414f219758e52c426d62153319b98b540c2d563c85109b988540436752d4110ad59253c426d62152309d98753082d7614c831cb50d5210ead64c84218f59353c866e6214e10cd993514ca5e6314c20bc58053c43676154b419b58a53c43a542104219798e548865d631502097d8d524432d5448020b9d8954442b5640c9108f99353082766114c1097195434c23c6454910e9d5052442e662d0731c7d53534425d6394910c750e5110f36540c721cbd954210a7561942329d987548825d6315010d354e52d06746155032b358b310c71d544c8329b189544c3565354420e350d5210e5c6354620c795253082776154d20add91534436662d4543bc580424426f6548020b998a53c42e76254d10ad592534427561d52208f19151883946150c43cd55251082e7614c821d5546310c25e6394d109798c540cb6665149109d5865090f1c5350d40cb551320ca7561943429d18554c83655294440cb5522108364520c510ad191534423d6494d21d3d4c524423f6550040d9949510c31d544c030b558c404431d5350842b558c20c42776550b10d594f41c86766510110e3951320cad663d0421b5d8d52442d66308110b958830c434e5354b419e580540c72c5450932b958b41086b46454910b358e320ca7a60150218f99253887445314910e5d53534432c54d4910cd952510c2d56394910cb54d4210a6e62153308fd91518825d6395121b998840c427560d45328f994544431d54cc030d5d8d518
  | 3 => 0x14560b4000541e03c6f050000541302800020080180a0401b000006481b05444630030ac60020000001208c1d0180302006048000083300426008220000109c281a4590e82c0150f074020980309c92018000001f0081f2010b004130004e2e08800c000540700c120241100c760041e07c0000425008c4060e20001d1b0f60241c0080200417008690180e05c000041c1842f03c0102c0806c220200100000000010e82e000a1014030040000000028130040d010040040c00c190101c4e4000280001800000001e40a0040715c1002834000040000606c0d7cc040080c0dc740046a034312180d0084a0b4234c408010640000d0000d00c0007c000000201414214080240c0080f87c021bc0a0340000c040140023c020380f00c290500007404198010000c0ac05018050c00021c08000160a800010060b00f0100a0b8070a8100180f97d8d544426d62d5331c7151434c2e46150a32d5d4f50442f160153109dd8554482776544010d514f41442796015021e5150534426e62150209d98650d0a3e6414c219b98a53c42746154b4097d95320cae662951108f590530874d5390842dc997504432c5414910d9508514ca6d6215031d598f5150a7661d53329b195324834e43548439d19532c426d658c8219758f54c866d62952319b596420871e5454c20ab58b419067761553209798c54c86e6620c310bcd8154442776154b4097d95310c6d563d05109d195324426e6294d108f590530831d43540438fd91518c31e5454f219e580530866e62d4543d9587524432e5494b31ab58b4110754538c510ad99331c425c63551209d185534825d6314810d3548310c3555354420d9544218823f6550c439d18554cc2b66408310b958b31086b664cc7219b588544c2d76355110d9908514cb34540c5108f59252c42e56295310b558c204436452885109d986500cad56310b109b19542482e662cc510c7d954310f1c54d4d109bd95320cab6640cb10b958830442f2600c910b998b41443e12008110cd150214427661141429d5845050e7561d50209e980540c69f6550c439d984530827b654c030b9988404436452d05109d9865090f3761550329798c540832d52d0040b558e54c427561150308f593530831c5450c31bc58253443a454149108f590524c2766194242cb95152cc6b96010440d594d51102d66395310add85431074c534c8219d98650d0ef16010d10b998a53443145414d10cb951520c2cd62cc631c7552530833551106409d58650d0e6e6295231d514c414427561d4c209dd85544c277654c910c7d50534431d43548438f593514cb4f654c8329dd8553486746550d10ad593214427665081109b988540cb55530c7219b58a53487545414d109b5885050f954310431d558453442e56210110bc582524426e6294e419e181544cb37
  | 4 => 0x40b048421b801020040ec400600605c050180d04c610bc0300c0b00c2908807000013a000080020
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xe000020000a173200024013409a020400800000850000009022c109002c0000008003000018220300000010080040001002480940a00003040110a040004547558c4244360992c019221c154c6150842a48eaa1084886856350842c432229cc5a0a21435cc5450821d2286b008688526749505244383aa0a629221511d5320c910d0a86b108788529701514208748b226018221c11505314910a4ce9298a488705431855210e86ba0a49926186551600c430e0aa7b0a84215497014d3208686baca899065435ca5350e41c18caa1a849954673950524438238aa6a1085465c05450c31a8ce52a0a688691635004044286b90a8a1a61c150d4214532e0ee2aa264196a16250040442863aa86a1265851526394910a1ae72928520f0454d4c5244286b9ca8a1443a85096010910c28a931e428850d7315142c8342b2264192218599053c8510e0a87b0aa421d467394c5244312320c4a8c61a150d6210d10a1ae829a64906c1634802044286b98a8a12418a5496010440a1ae829a6410e4463189519030aa18c2a90879198c52d0510e08e2a1aa421d16749505344342b1a8421221435d0534cb20d82c4980608870554185320cb83b8aa6a108592549600c430a1ae42a28618f0554d85320cb822a0a7a92218654d6010440a1ae92926518d147550c4344286b90a6a1a81611c54350932e0ee2a1aa421c64755884344286ba4a699443a150c6150932a88e2aa26419434755903244286b94a8a1c638a5516008420c48a93166288685644c832c438238aa8990658999052cc510c48a9314a68850d7215143cc30a320c6a8c41859905394910d42c8900408850d731494250324a9ac010841491c55350842
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4200309020c047550d6210d10a048558d4210910a0485591320c9109078754f6150842a0686dc5535084290787553614c8329078750f6154843a0686dc54354843c047558d4210910a048550d6210d10a0686dc5544c832c0475591320c910
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/21+packedAt s4K6 (672+(h % 21)*6) 6) % 42)
  | 5 => 2*((h/296+packedAt s4K5 (20007+(h % 296)*10) 10) % 741)
  | 4 => 2*((h/292+packedAt s4K4 (30172+(h % 292)*10) 10) % 794)
  | 3 => 2*((h/72+packedAt s4K3 (4459+(h % 72)*7) 7) % 91)
  | 2 => 2*((h/11+packedAt s4K2 (720+(h % 11)*4) 4) % 12)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc1ffffe0ffffff81fc3fc3fffc3ffffd11f1ff
  | 1 => 0xfe07c3ff03e1f0fe3fc3fc383fc38382eececc
  | 2 => 0xfff803fffc01ffffc003ffc03ffc03ff0f0f0f
  | 3 => 0x3fffffe00fffffc00003ffffc03f00ff0
  | 5 => 0xfffffc00000000ffffffffffc0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x44100022080000000404404884048888005055
  | 1 => 0x8cb184463942a1161c41c4119c41191866c6cc
  | 2 => 0x1062aa8850d548aac222aa822aa822730b0b0a
  | 3 => 0x39453310a2906acd6aa8220433327023b00da0
  | 5 => 0x2186221cc3198cf1b333332702204043dda000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeaa0eaa0eeeaeeeaeaa0eaa0eeeaeeeaeaa0eaa0eeeaeeeaeaa0eaa0eeeaeeeaeaa0eaa0eeeaeeeaeaa0eaa0eeeaeeeaeaa0eaa0eeeaeeeaeaa0eaa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40525
namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x6c000100100100000a0c00050021000000000000000000001420000030840400c000014000004000000002b000ff30fe43fe31fe41fc10fd42fd10fe30fe20fc20ff10fc40fd43ff41fd41fc30fc42bf40fc21fc31ff40fd32fe42fc43bd40fc41ff32fd40fe32fc32fe21f510fe40fd31ff21ff42fe10fd21fd20ff43ff20f710fd30ff31
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x281bf40cc37ea3a05d94630bea9083bf32d02f8a8905f940419eaa4817d544ca7aa8184f55020dba0221be535037ea898df55130bf28c81bd54882f8a9997d4c910df29e81f551102fea2a05f14d40bea9443b140442fca1997d10d10bba8a657e501037e80185f94443bf294817d52d02eca2105fd5021fda0281bd40083e8a9886f90540fb98a21fa40102faa3905f94b10bfaa2437e53103ee65886f50130bfa9a43f730c437e83a05fd50319faa265f741c437c86215fd4b10fb98a637d51903eaa8885f54031bea9c417651882fea7907d88110bf28c85bc42d03ee84885f54443bca80837d520c2fea6905f55010fa18e217f54cca78a890de14132dfa9a813f54487f481084f95230bea8c21f453c437e8721df14530df10e81f721487f220087d10b10f699641ed4210be861885f54d20be2a6217e54083f620884fd5131fb192217d5490be8a5885f95032de21c83fb20882f8a6a0df54430df90a81f7514cafaa2215f94030ef19265f420442faa8905f94d20bf28c65bf53d02fca8995f553209f2a021f441cc6fea8997dd4f10df2a4417e54cc2fca1185f54043dea0883f743c42fca198df15330fb20a21bd548c3ba64985f54a20df18a817d53c83ea60887e50110be2a4617c524c6faa7a0df94740fb10e217e51d0afaa920dfd5321bf296877e54483be64197d94630bf298616e520c3be86a1fd90441bea9c637f54c83eca7887bd0a42fba0e63ef20883eaa3186f55210bf28485be31d037842a05f54c42bf28c83bc421077c65a05f55121ee98863be52d02fea6106fd0010dfa0421bf40c437281085f15231be29a41f741c87eca48877cc230bfaa2617e5410efca120ef48540bf29a217f504cb7ea890df54221beaa4617c51483ee42885fd4910bfaa421bd40c82fca7107d48421dfa9281be43503ec62887d94440f7196417e530cafaa4085f15320be2a441bf50502f8a710ef15121dea10857f54482faa610df14f20be2a2657d51ccafaa1215f94743f699065bf411067ca8187d14542dfa00817551903de40107d54f109f2a421f710042faa910df94631df212813d54882fea2a15f54440bea9221f740442f8a7886f14d40dea9a81f543442fea090dfd4d41bfa9e43f552c42f8a5885d54610bf29e857e53902f8a8885f55030deaa0217d51cc37ea2a05f14143be282837f524c37ca9185d54430f9a8221df318c6fca820f7ccb30fbaa621f7108437c80a07c50110fb902217d518cafca5215fd5331fa10a21f6424437886217d50310fa20621bd32d02faa918efcc7409f2a4417c5150f6a8220dd94640beaa041bc43d02fea7887b4c920dea1887ef21086fca9995f95021bfa9263f6434437887217d94430bea8c857e53842faa6087d4cb10bf28843bc325037e81105fd5221fba9a21f741907dc64195f94810
  | 1 => 0x621086fca0217bcc932fa20a21fb20482faa8885f94e43df2a041f721c42fca620ef50030be2a4217e54c86fca121df95030be292837c52842eca2205f543439f2a0817c5050be8a2a1df94c31beaa0637d54882faa2105f55321de2a2657f5150efca0105f14121fb90c437f54883dca4185754c20bf29061fa40443e843885f54620faa08837f548c6fea6085f55131bf2a085bc544c776a0a07dcc110fb29a21bc21d02f8a4a1fdc8310fb18e21be43d037c86a1df54032bf29081be42d03e862886fd0d40bfa9021f554c43eea4886f50d40be2a065f732442f8a0997d54430bf2a621dd32cc3eaa2105f94a41bb28821df310c77c82a0fe94041dfaa2657e50086fca790dfd4142fd986417c540c3f061905f15131be2a043be540c3e8a8886f50f40bfaa661bd52d02fca4195f54e30bf288617e54883eaa488778c130fba0a217d54cc7e860885f94342bf298437d539037ca8085f94441bea98837e508827aa8085fd5230bf29c83f740c43de4310ded4132bea8c617f540c3ec87887d10910bea96837d5090efaa3a16f48740dfa1887bd40c43ec42885fd4143fb98e43bf40903ee6318ef545409e2a2633e54083ec85885f54743ba28a657e52cc37e84215f54740fba8a85bd40042fca5a0fd50f10bf29463f743442faa5187d4c431bf28087be51502faa5205d54420bf28c617e500c6fea91977d0e43de19681f4410c6fca321df94232bea9e817d50c86fca1a0df14542de28a81df328cbec81885f94910be2a443bf408c2eaa3105fd4532dca0221f452442fca420df94821bf29821f7415077aa8107d48710bf2a463bf41907788520df94420dea0421bf40443eca8885f14e10bf29841f6518837a80205fd4e10fa29a213d548c37863a06f4c940be2a261bf40483e480885fd4d40be2a0417d5290efaa9885fd4530bf2a0637d53d0beca2105f54021bf28c417d5010afca218df94a43ef99261f432c42fca6215f94a32fba96217d52cc378a4a05f55210df2a4217d520c6faa520df94231fd10041f652c43eea0887dcc421fa88021de314c7ee8218fd4c710de21a81be431077a85a05fd4131faa9a217d53842faa690dd54630bf28065f441c86fca1a1df94820df21285bf52d03ba60187ecc230df21083ee4210beea8886fcc540de98e817f5388678a8996f50740df28e817c53487ec61886fd0940bea8865bc41d02fca3987dd4543bea8463ee21486f8a6105fd4940bf28c437f53442faa6107d50110fa202217e5210af8a098fd84110bb288617e5310efaa1a0efd0f40bf2a081bc52d03f460185f54f21bf2a641f520c437a81105d14542be29021f441c42f8a990dfd4520bfa9283bc51d036a81887d50b10e6990657d5490efea7107e14132f6a9061bc53d02faa810df95331bf286437e544c6faa518fd50710df19
  | 2 => 0x4641000190460000219842000482602e020000104a1112a010100284a0100a00002070020000001802660000081400010030ae0202208802120140103a08012000401581c0c0300e85c02a8a1181203004018f40009a0480001800000160e80400000030140200c092ac0c80017a6a1e00e0d0021e0744d81e04804000005d800008001082000000e8802130760a81400024018800290e06892008740004a0000207876660f609000248be058a00402200aa2058040001a0082a0b04a120000a80a140003d00c9d0d2000040281601826060000018216800010cc3e02c0001e028220080e038281b0001d82e0024402804038044202400012128042502a00060048080003e0a85551810188ec020000c82203002000740481a04052000160004e0783608850138301880c018040801400034248380212a06000950040200a000060000e840b20280400000300000080003016060001180003804978d2138000c90c02808268537c540c6faa598fe54041ba28a877e53887ec6218df95121dea0221dd4310fbc8621efd0b40be29c417d52843e86390df54232be29e437c52442fca2205f95230bea9881df300c2fea0a0fb88120ef29841bd540c2f8a890df94a30faa8c817d540cbe887886fd0a42fb98e217e5210fee8210df95110dea9281bd408c36e81887d48510fc90041bf40082f4a020df54332bea90817e53c43de84a17d90110bf2a0217d54ccafca8985f14d10f719241bc415037c8720df95221bea9c43bf404c2fca5085fd5131fda8265bd42503e88210ef50120fb10621f432442faa9985dd4542bf288657d52c42fca1085fd5010bea8c87f742c42faa1a15f15331df20e81bd41502fca2086f90a41ee99065ed20083f681205d54440be29821f6519037a62a07d14532bfa92877e5110afea8885f94e42fb2a6217d50107ec83885f94240bea9a21fb30082fca7906f54740beaa4657e50886faa9205fd5020bfa98437c515037e64a05f95232fb19621f420c42fca3905fd5310eea98417e52d02fca3995f94d21bf29e817c5350afea5087e84010bf28021f431087f660985fd4d42fb18221bf40c82fea8197ec4210bea9e21be4390b7aa7a06f10c419eaa4217c52502f8a4985f54b43bf2a421bf21d037a81987b48421be29843f530c42daa4186f94940bea90875e53083f060105f94831fa902217d53906f8a2995f54331fca04217e53d07de65196f10940df10a81f551882f8a8086f0c540faa12217e52cc6eea2a1ed50110be2a4657d5390afaa120efd0540faa0a21f9300c3f280205f54e32fa98a21f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1510825d63d50209ed8153482b56490441bcd8132442b5640c110c714d43502b76448710dc144504cbb26550110cd550410c6f1600c910add91524425d6314a109dd8554c82ba6008540ad191324423c654c7409d987540c2766194242ec4c9404423e64d4e10f1185320cab46154f408fd91524427661141429d58754ccb4d53480209d594410863d64943329d98650cca6d6215030ecd51404432e54548308f992544caf16094d10cd94740882756194232add91324426e62d53318f59253486766195132ae59240442b961d41409b189544c27860551329dd8553d023e64943218f994544ca7560d4532dcd87504ca7661d4c109e583538867561141329e983538867561d5220add9541107b360503109d984540cb3a4354041bc583424426d62d5331ae58053d02b46154940d618153083365150010ad19153c43b165501109d587548c2e6620c3109d18554cc27661150109ed95300c37351d4132add8542502b76454f10ecd4940442b66488110add8141106b960949409d584538827a6015031b9d8953442ac62545409e580540c63e6414132d554e510833554153108f99250082746155320dc90550106746550f10ce55110043655214b109bd89534433754107219d5845050e796095132b9189534433454d4532da181520c23d64d4f21ec149404423e64d4c209dd95434423e64d4e218f19151cc32e52d0030ad191310c6f265501108f592508ca6c6254d10cd953108423d64940218f590538833b5414132cd55310042b46448710cd945408833754d45329d9944044276658c110ecd0d40442776155131ae98032502746154b40cd54451d025d63148108f992500c2746550b109d98650d0e3f6550c43ec10940442e8604cb20bc580424436552087108f99353c87b153501109e980548c6b56488310ad191314427661d5230ec50130443b2415011097d954310f4d32540328fd91510cab7644c7108f597400823e6495131e3d91320caf36054910ad584421063d6015132cd15141442f160107318f59250c873a4254041ad99020c43385414132d654f30082d66308310cb548525026e6214e10ec50030442756194043dc99750442b960d47408f19153086e46255110ae980415023d64d4c20ad99230442f164d4110cd951518c2776155121ab5884310a7560d45428f99250cc7b05350110ad19153443cb604c832cd547401026c62551109d185540cb3654c4010ce990504ca77654c9108f191534433551d00308fd9532502f261901109d986508ca3f6550842ad59020c43b33250110ad19121086776550441d554c534438c644c832bc980324427661940439798c540863f6055010cd552518823e6414c21c794f400823e6414e20ec0c940442b564841108fd9540082f260105109d18553d027461551208f580544c7354154041
  | 1 => 0x433b64d41329b988540c6b7644cb10cc505501066f65480208fd9540103b06550110cd54451502b4644c7109d586500ca766194042ec94940442776154843ce50550106776154b309d98452043645248510ad99230c42cd638c832ced05501063f6454730cd15141c425d63d53219dd85544823d6414c20ce55210043565394420c754c4310a5f654c832c754d40082d8604cb308f19532502b76454d10f14c832442e5620c421cd952518c23e6494332cd945400c33b65502109dd85544c2bb604cb40cd54540882b96014b40ad18542d02f260109108f191510cb6652944309dd8552d023e64148109d584548c23d6414c218f99050487b363501108f993530425e63d5020cd952510823c654cb40ecd0940443355494420ac592404427561d4e208f590504cbb02150110dcd44504cb726590110dc546401023e6494221cd54540082b76154f40ae58221502bb6054540cd952510c2746155130ec94d404433651d0230bc58354c432d5214b409d98754883b16350110dc94510043386550110b518d54442b46154b40ec506501067765484218fd9532d03b1408c110f1d85320cb4c524c9309dd95424427a6095132ad185425027865501109d58454883b13150110cd94740102b960d4b409d594310865c63551108f99250086af6254540ec50110042756114c208f992500ca7661942439d996204425f654c030cd90c5150f4c534cb20ecd91404426d6214e109dd9543c433654946208f992508c63d65d00309798c540823c65487409d580514ca5d6315021ce99150107c8604c8328f592508873454c85219b98853042b46454b108fd9153483b14350110cd551518823d6414131dc584504ca7a6015021aed8132502b76150b40cd5531084276650c110ec90d40442766115220ec50320442f160104319d984530423d6595030d514d31442756194342ae58032502f36055110ec18940442bb6550210b558c20442b76150f40dc985501067665c85109e58054086756194243bc58252443655254430ec589404432c52509409d5805150e3d64940328f593538827560d45439759653083b063501109d1855210ebb60549409b988540c2796015231d594d51082f06550110cd945408c2e5620c1109d195214431d5314d409758c54083b24250110ec0c540442746154d20cd945401023d64d48108f59052843384354041ad5923044274654cb10cd9085150b355454630ec50020443396414132ab189535026c654c920b9d89544431e5454c208f592500c23f6454b10cd947400423d64942319bd95320cab96094540bc983414433554544309d98753882b96094d409bd89544431d5454c2097d95310c67b6550040cd951510826f6255130bc980404427761550328f59053042f26590110add85435034d52cc0308f19521503b35350110cd55
  | 2 => 0x6590110cb551520c3384254041ce153504cab56488110ad18d411066e6214c209d99420442bb6054d409d1855310bc5320cb108fd95315033551107409d987548cbb15250110d554c310863f6454f10ae18132d02f260d0d10cd153314c63e6494010bc582544431e5494c20ae98241502b664841108f99352843355444010ce951401029f63545409d18553c83b263501108f59250082b464485109d5865090af164901109dd8553c83365454620ad58640502b960d4f409d58454082756510431cd552518c32d54948308f596540423e64141318f19151c827665cc5109d584540ca3e6495121add8552d02776155330ecd05404427561940108f593538433651d00209d587530823f6454b30b598c204434d524c030add8532502d76355110ec10540442b7644c5109d19531442776550b10cd550544427a6015032d554c31c427465505108f992500c72d5250030ad1854210b8d320cb40cb952520c26f65508428fd9153486b46150d408f59654082f16010421abd8953502d76354910ec485404433b54d4132add85525025f63551108f994544c63c6454910ad18532d02b464549108fd9540043b14048110ae582315025e6314c209d5805150a796584010ecd4340443b362501108f99054082b664883109b588540c736545443097d8d524426d6214c10cb54b400c33554104219d984548c3726114132ae580215033a5450210ec989404423d60d51328f990528423e6414e108fd9541106d563083108f580544863e6414c108f992534866e62d5030ad990204432d5210b408f59050486b8604c9409d1954244277654c431ad58443106b56408110cd95110043b142501109d987540823d60d51218f191520c67a60152219d5845050acf654c832c755253082796015221ae98231502b76454b10bc58352c431d5310f40dc50550106b6640c1109d987540423e6415010cd945400825c63551209d984530823d64d4a10ae58031502f160153109d984540c3655214910b958830c438d320c940ad59230c42756194042bcd8153442746550d108f990540c2776154d21cd547400823e64d4e208fd9153c833651d0030ec500404427b65480209798c52042b46150c439d99741442756115030cdd5041cc63f6548740ecd9540442ba600c540cd54740883c932cc320ec502104423e64942329d986500cb3b6550110ce941400434c534c9209dd855310a3f65500309dd95100423f6454d10ad185535031d53d0020dc5454010277654cb10ec50220442b5640c3108f597400431d5314f40ec10d40442f3604cb10ec50330443b05450110ae98221503b06150110ec505404427b6054d21bc18132442b76154d40a718d515023c6454b309d18552cc23d6494031ad18532502756194343ae58051d03b35050110bc58343442b4644cb10ec885404
  | 3 => 0x7f8082a0200000001c170cc00010210003f000ba1181b018030840313c0d03c0c004100200100407008051280066c0000802034020001100845000060043307c0b00c00000f700408000040e00100c00064000000c01c14028000c46d00400010001e5d20983d001c7008600bc22000420f8020005c00001010e20000100400010470cc100040d00460050140140a0c41703c060680919400010010000016000014020045024c00000007a6070940302c24068011c1251000002c00000c60088a0141400000044030180001926050100e0010143400c000000a0000500405010170140006c3c7b01b07c17020000000a0041a0e8231781b004017a40600106000883082b2a8600000003d42000010002b01c020000019001024602141a00404004000043905805018002080210c13020000480800c0010800128020005301800088032080c030174d4000382c01cbe0400a4080400042000070a5e2014000003800c1200c0b0053d3a41a1cc010241b0a00f000000045bad99040443376550441a7d8d525033a6095210cd547408c3b33150110d3d95320ca3c6454b10dc147504ca7561d50209b58b540c27661d48109d587540c32e525003097d8d544836552944308f59250042766194342d354f200833864d4132ad99030c42b76448510d554d51082f16010d109d195324427960150329718d524423f6454c219e98053086f16010721ad986405023d6494331cd150514cb3451505408fd9151c82796014c219ed9510043b361501108f59052042d46354910cd947409027b6055132ba58830c823e65151219e980540427561d52329d984504cbb23150110d554c53c42766115020ecc8540443b360501108f59353043375414532bc58353c427561943329dd8553482f26010d10add8532d033554944308f990530823c654c5408f583544c67761551329d586544ca7661d5332d9949510c2f0604cb108fd9531d033551500309d9845050e79650c020a718d525025e63d5321cd54540102e6620c110bc58052c426f65484219798c528423f64548318f593538863f65485409d98753082746155132bc983424437061d41328f191534833551d0240cd545408c31e5350020ad59240443b14154041ad189411063c6454f20cd55041c42b46150f408f59053842786054d219d984538823c6454d218f993520433554105108f581540423c6454f10dc98251902f16014f10ec8c94044276
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x40000000180000402c4e0051100100250000480000c19f00046006408a8e00b9380060402708004870200480280003e59451cd5410510a62e2212a020d147454c5344259bb2a6a022168dc95350110962e8302648852672d5041cc69839a82a80834cdd53250110f026419280885a07258d4044319aa2c020e432c1d93250110d22c6a0040886916318d40442c9b9ac4a0221b0184604c832d42c431280885937359540442a23aa64192212c5c0614c940960eca928088544735485244299baac4a0221451c55314d40a18ea99064a05a37258d4044292392a820a214cdd56350110962e230264a052474548524431832a82a02212c5c6600c940a48e2a90a4a05907359540442983aac6a02218c5516010421a28e6a88a2a0692635002044292392a228a81511c95314d10962e032264884b1749803244360992c0192211c5c06155032d1264b0064a0533765055010718b28caa0221c85485250110c48c82924288531705511004344320c0990658c5516015310a18e4a98a6a053370505501070a298c2a1a812c1d95350110b20e6b1280887115314d40442c9b9aa4a02212cdd93250110b40e4b2a80886335458041cc68b39ea820e43a8589400c110966eca9280885317110d501068639aa429281451cd5415110c28c829a628863364d87504cb18aa2c0208634c1c94154041c62c8b08a099624521854250318a8ac028e81681c95350110a60eab128088590735494044292392a82a2214c1d53250110d44c4a00608843970191510ca99baa82a808368dc96550110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x14201800201a1283d516010721a80835886250110b008254c5350110b00835485250110a20865485250110a20855886250110a108654c5350110a808258c6350110b00854c83250110a2282d516010731a40854c9600c910a10835946550110a20825946550110a108558c6350110a80864c83250110
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
  | 6 => 2*((h/63+packedAt s5K6 (704+(h % 63)*6) 6) % 44)
  | 5 => 2*((h/287+packedAt s5K5 (21033+(h % 287)*10) 10) % 779)
  | 4 => 2*((h/300+packedAt s5K4 (28652+(h % 300)*10) 10) % 754)
  | 3 => 2*((h/56+packedAt s5K3 (4165+(h % 56)*7) 7) % 85)
  | 2 => 2*((h/12+packedAt s5K2 (900+(h % 12)*4) 4) % 15)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfc0ffe0fffffff03c7c3fe1fe3fffff88e31ff
  | 1 => 0x3ff03ff01f87e1fc07fc3fe1fc781e00f3cecc
  | 2 => 0x3fffffffe007fffff8003fffff801fff03ff0f
  | 3 => 0xc0003ffffff801ffffffc001ffffe007fc0ff0
  | 4 => 0xffffc000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8520a2224441110081624b1220ca5290861055
  | 1 => 0x8865a461c94a532c02e61730e450d430b2c6cc
  | 2 => 0x10830884831480554800244549010963016b0a
  | 3 => 0x2ca11091200c49a5488800192258045580da0
  | 4 => 0x230c21ce1c6719e3a733399800461186efb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0fee0eaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40525
namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x20060002002c03c01070230890ce0400089412cc08004104008c017f90c07fd52007f8c407fd5301ff14805ff4100ffd0005fd5400ff54007ff5200ff94003fd3000ff14003ff30017fd0801fd3100ff0c005fe4201ffd4c03fe20017f50403fe30017f95003fe40007fc8407fd51007fcc803ff5000ff10003fe10007f0c403fd2000fd44003fd10007f0c807fe53007fcc403bd40007f8c807fc5300fdc4005ff43017f10405fd4300ffc8003ff1000ff08003bf40017f10c05fc5401ff14407fe5201ff94403fc10017f10805fe41007f08407ff5100ff50001fd21007f88405ff54007f4c805fd42
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84222ff44132015fcc91907bff51cc421fea064206ffd972112ffa811906bff438c409ffa0c4210ff9432112ffca11900efc654c415ff302420cffd45210cf7e811889fff518c8477eb22641bff54a31027fcc11884bff51c8413ff21a6409ff9833108ffaa99080efc654c809ff20a4203bf9943101dfcca10802fd620c42f7fb226206fbc8232117be6099027f5310c409fe20e6223ffd9132027f8a318812fc630840dff2926401bf18132027faca10877fd54cc445fb8826423ff95132117fc8099026fe63084077f328641fff5403204ffe6498826ff60cc453ffa0e6404ff19231027fe209882afd628840dee9906406bfd9232027f8a398826fe630c4073f32e6209ff0c3320b7fa809882ffd5448413ff30e6404bfd8c21037fea519027fc60cc813feb2e6416ff58131037fea41900efe654840dfeb246406bfd903211ffe849904ffd200c4097fb244228ff503320ffee2019073ff20cc40d7f3104206bf98832027bc629886bfd438c435fe2a46206ffd80320c7fea298813fe414c409fe8806204ff580210c7feca98803ff3288433ff2846213ffd403104ffc8618827fe430c80dff9024214ffd0831037fec219027fd30cc81bfea044201bf18321004faca19013fe658c40dff9064207bf5902101dfccb9081bff208c80dfe2926403bf195210affca418813fe658841bff2844206ff19432027fc6210806fc60cc839ff1066204ffd4621027ee201881bfd2008447fea0a6406ff948210bf78c898813f6210842d7eb1c6201bf98031057fc4090813ee214840dff1046406ff184320f7faa398812fe610c8097fb246217ff55131035fec119087fe510c813fe21e6202bf19132027fa201081bfe20c840bffa804202bf991210b7fc409881ffe4308451ff886640bff10d21027fc8310813ef2188409fea08620cff54521025fcc399083fd410c809fe32c6209ff14e31097faa390803fc6348413fe21c6411ff10f2104dfcc710827ff308c44bdfa046406ff10a320b5fec0988a3fe50cc80d7f316622affd473213ffaa319002fd628c409fb8804206bf193210dffea51885bff204c40dff32c6404ff54631077faa91081bfc204c8097f308421fff84032037fec790827ff30cc40dfe3006404ff182310bff8849885afd604c441fe2086406ff580320aff8a418813fe100c40dffb0c6406ff94832007e8c29901bff4208445dfa026419ef502310b7fcc098813fc100c453ff20e6424ff5493204ff86099003fd6348413fe21a621fff44032067fea490813fe628c413fe1946216ff10131117f8809905bfd504c429fe2a06201bf18031037fe41108aafd65cc80dfe9006425ff4c2320bffea898827fe534c845fe3026404ff19031035f8cb90867f5108c4037e3046206ff58f2101cfccb908a7fd54cc839fea866209ff99732
  | 1 => 0x7ff508c4097e3284209ffcc33200dfcc010813fc41c8409fe3286204ff9452104dfec998827fd60cc813fe29e6202af1913206dfac11089bfc418c81bfa8844209ff90e310e7fe819884bff53c840ffeaa04204ff94721067f8a690827ff60cc409fb8846209df997310bffc849889fff538c815ffa02421bff94a310effc8598843ff40c8413f7992640cff99521007fe629085ffe544c40dff3246401bf182320fffe2019003ff31c844bffa04640bff9912109ffc4018826fe6348409ffb004206ffcc83207ffea71088afd604c839fe1066204ffd9421037fc8519013ff6388401feb0a6406ff08321037f8411901bfe324840dfe30c6422bfd8132025fec110876fd64cc43fff2806406ff08121027f8831087efd600c835ffa146228fd44332037f8851080efe658c413fe2186224ffd4932037fe401083bff548843bfea166222ff54132077fca910813fc108c40dfeb206416ff08131027f88298827fc30cc409ff28a620bff509210bffec898813ff650c451ff2066406ff50a3200dfcc19902afd6048431ffa9a6206ff880210b7fe809881bee320c80dfea164220ff9043204ff8a698803fd31c84037f3044201bf98132015fcc910827fd64cc819fe32a4209bfd9731025f8c81081bfc60c8453ffaa66406ff10b32025fec81883ffc5388413ff98a6207ff10c21007fa6290813fd418c455fea8e641dffd0731027fac11888bed204c80dff32e4218ff19531107faa81908bff104c853ff2a66404ff94621007fc6498812ff6588437fe294620aff0c12100dfcc190813fd5108409ff084620bffd05210a5fac8188a7fc41cc8517eb066410ff0c321147fe8199027fe62cc4037f3046426ffd063204ff861190a3fc40cc823ffa0e420dffd0221027fac01881bff648c84dfe2a46406ff90a210cffa6118813fe41cc40dfe9046406ffc8032125faca99013ff3188433fe2846217ff50931027fe211085bfe504c427fea806223bfd9132027fec910813fe310c409ff10a4204ff4c62104ff8861901bfe32884057f3266215ffd4831037f8c990812ff658c409ff31c422aff94732037f84110813ff2188413f79946429ff50b32117f82099027fc53cc80dff1006409ffd4f32027fe219080efe65cc44f7eb2c6419ff10231027facb1881bff608c809ff20e4200fd0c721025fec71083bfd428840dfe3206419ff8c231125feca99013ff10cc40d7fb286406ffd4821117fc2099027fe538c4057f3226417ffd053104ff86098803ff3248413ff9966206ff90b3206ff86110802ff614c809ff882421cff5033102ffaa01080afe640c40dfe32c6406ff197210e7fca19882bfd404840dff9964221ff5443212ffe211901afe620c415ff2824206df99721007fa651881bfc20cc8437eb286400fdcc421027be631888bfd204c80dfa9
  | 2 => 0x210a7fa8418827fd53cc81fff29c4206ffd9432107fea81904afd65c8423fe2a6420dff8c221027fec610813ff3108401fe9944218bf59531037f8841904ffe500c409fe28a6222fbc8132005fac219013fd210840d7f3146220ff9503207ffaa710813ff2108409ff3006206ff58232025fcc310813ff410c433fea846218ff99531077fe871081bfc200840dff190420defd0221027fac81083ffd528840dfeb286419bf5823104ffac39909bfd548c8013eb2e6204bf98631027fa6218827ff530c81bff2044209ff94f3204ff8c39901bfc608c821ff9864222ff4c132037fa841088bfe304c82ffea1a621cff14331025fec810813fc5188413ff1866401bf98032077f8a91082bfc5048413ff992640bbf5912104ffec99908bfd404c8057f320420affcc121005fac31905ffc544c413ffa1e6413ffc8031025f8c81884bfc53c841dfea1c420cbf59521117fca099027ff308c821fe2864229ff1533212ff8a119093ff514c815dea024204ff0c62100df8c0108a3bf40cc855fea96641fffd0032037be651901bfe42484057e32242009f59721027fe8210806fc60cc40bfe1804204ff4c42104fee6318813fe410c413fe1966206ff90832027fac11081bfc3248439dea066210ef50321005fac59887ffd400c855fe28e6400bd1853211ffc8299073f510cc443ffa886409ff8cb31027faa218802fd61cc8137e32e6206ff8c83204dfecb99006fc60484097e31c4206ff08032037f8659082bf51048409feb146225ff9023204ffe6418897bd408c821fa8864204ffc4031027fc421088bdd304c809ffb044206ff508320b7f8a09881bfe60c84397eb066223ff55132037fec819027fc300c8457eb1c6409ffcc13111ffac899026ff64cc827fea006204bf192210e7fc8198827fe64cc409fa1884228ff14332015fcc819027fe65cc40dfe2164200efd91320ddfacb18802bf644c415ff2024204ff94731027fcc918833ff534841bdea044204ff18031027fea218843fe40c8417ff2a24206bf98a3202ffa8010806fe608c449ff32a6406ff59632025f8c91881bff204c81bfe284421dffd53310a7faa818827fc324c409ff8804224ff59532037fe6410877fe54cc41bff984421dff10b31107fe821902fff5448409fe8846226ffd52320b77a8098827ff61cc823ffaa64204ff98221037f8849088bfe204c801fe30a6404ff1052102ffca01080afe64c8409ffb006216fd44131137fca919013ef2108423ff2a64203bf99531027fcc91082eff6448415feb024204bf9863212dfac119056fd650c40dff19642039f99432027da421081bff2148433fe9046204ffd442104ff8a719027fc434c809ffb2c4206ff98232035f8c7908a3bd40cc80dfe1944204ff9042104ffea798827fe60cc809feb184216ff90131127faa29906
  | 3 => 0xe32e6204ff8c621077fc871084fbd400c409fe18a4200fdd8532027fec818813fc6408413beb2e6201bf1813102ff8a01081aff60c8417fea0a420aff18121035fec019083fc540c8537eb266411ff50721027f8209088ffc414c80dfe2924225ff04232027fa2110827ff43cc409fb1886223ffd513206ffea11081bfd52c8413ffb266224ffd9532027f8219088ffe644c809feb244204ff18221037f88499017ff300840dbf3286425fb48232007fec29901bfc52c8427fa8806206bf194320b7fec098827fd430c839ff0866209ff583310bffa829881bfe528842ffe322620cff59521057fc2090853fc420c413ff9946204fdc422108dfac990843bf40c8413fe3066227ff54e32037f864108a3fd20cc801ff30a6424ff94532037fac31902ffd6448431feb2a6209f7cc33212ffc211904ffe400c4017fb126209bf19732147fa219902bfd3048451ffa866403bf9963209dfac01883efd658841dffa144224ff1953211ffa8499027fe43cc80bdea004224ffd4d3204ffa6598827ff65cc813fea9e6210ff4c321036facb9081afc624c409fe0826222ffd01320e77e819881bfd528c8197fb2a4202af19121147ee2199027fe30cc40bfa8804218ff149310fffc8019053ff540c439fe2066209ff94f31005fec690813fd4188417ffa1a4200afd91210a7fca818813fe650c4157fb024205bf580210bdfac898833fe534840dff2126400ff4c921027fcc418813fc1088415fe2024212ff94f21057fc6090827fe538c813ff9806406bf19232037fa65908a7ff42cc80bff2004210ff1032112ffc6119027fd43cc821ff1864225ff10232025fcc21887bfd52cc40dff1926406bfd9632037be641900afe648c419fea924206ff14a2103ffea810847ff43c8415dfa024204ff5883114ffa839904fff400c413fe298620cff54d2100df8c019013fc51c842dfe982620bff50d2104ffea618827ed320c80dfe2104207ff95021027f8c418802fd6388409ff2886212ff54f210cffe411889bff438c801ff31a4227ff9463200df8c110842fd60c8409fe28a4204ff84221037fcc31901bfe610c83fdea006409ff94d3111ff8c899003fd324c44dfea1c6428ff0433213ff8a319013ff310c413fe3166204ff99421037fcc99082ffc6448429ff210621ffd440320cffc411889bfe418c813ffb166209ff50f310b7fc6098837fd308840dfe2966409bf98f21047f8a61084ffc200c411ffa98420bffd912112fea211901bfc63c841d7eb244218ff54d31027f8821088fff414c801dfb226209ff8c83106ff88110813fe5108431fea92620bff15121027fac918827fc438c43bfe2a66204ff18c21037fc8410813fc648842ddfa026204ff98c21015f8c8988a3fe10cc809fe31c4222ffd413208ffa8790826fc64cc413feb266205ffd00
  | 4 => 0x86bff548c413fe1806206bfd972104ffaa61880efe658840dff216421aff10a31027fec810882fd640c801fb98e4204ff54621037fa4190803fd624c40dffb064206fdc85210ff7e8019093fc514c835ff2a4621aff90a3104ffc871904ffc400c40dfeb064201bf98331087fc2190813ff620c40dffa106404bf19621027fc201086ffd538c40dff2924206ff58432037fe6519063ff524c43ffe0806428ff8833204ffca618827fe300c413fe9906223ef1913204ffac598813ff608c40bfe9804200bf58c21037fca59905ffe644c409ff18a6213efd003101dfccb99013df310c4097fb006219ff50231027fec51885bfc604c40dfeb264200afd913200dfcc09881bff658c80dfb90c4215ff5483111ffa8699012ff6008409fe2886222ff5813204ff8c999003ff6348437ffa9c620bff90d2104ffe8618813fc418c447fe2a26409fdcc53104ff8a69902fbc6448401dfb224226bf5923204ffec199013fc600840bfe2004209ffd9731025feca1080efe654c809ff28c6202bf993320cffe811881bfc520c811ff2984228f74c332037fec990827fc530c80dfe9904205ff8c02106ffaa110812fc650c40dff3006404ff594310c7fca498813ff108c41fffa944204f74c43104ffc6019013ff318c415ffb02420aff48121027f8c51885bfe104c42dfe8826204ff8c5210e7fa4198812fc614c80dfe3246402af1913103ffe861081b7d650c815ffa824205efd0021007fec498823fd530840dfea90420cffd95210cff84118826fc64cc813feb2e621cff44331027fc6390803fe328c44bfe8846404ff99021117fcc099073ff50cc413fea186209ff90f31005fac69088bfc504c815fe8824209ff4c032027f8a21086afd648c413ff9826404ff99031147faa199043fd10c84137e31a4204ffd963104dfec19906bfd428c43dff2966217ff5913112ffea119047fe43c8421ffa86422affd4b320e7ee219888bff604c801fe3126206bf19032037fcca1907ffc400c809ff20c6200bdd8532027f8621086bfd548c415fb8824206ff94b21027fac71081aff63c8409feb2c4206ff94a32087ee219088bf5104c84bfb8846416ff4813104ff8611887ffc500c80dff3206404bfd9431027fec91881bff42c843bffa166207ff50c21037fa6419013fc6588445dea026409ffcc031027f86390837fd208840dfe2946404ff10431027fcc01082fff4248413fe3266204ffd063103ff8a81081bfe63c84017eb1e4217ffd0d310f5facb9881bfd520c84dfea0c6406ffd0a32037facb90827fc320c43dfe2966206bfd932104ffaa619027ff430c813fe9866202bf99131045faca1085bff504c427fe2806209ff19732027fac818877fd41cc413ff21a6204ffd4631025f8cb18813fc10cc42fffa126204ff194210b7ee2098887fc510c813f
  | 5 => 0x8048020580e4002fe0180000000200c1204780a6a80080d80802e204018060020043200a0005a80104b0c60240034301e000000010100b00302617402c018020040000200b02e074163040006600001c0621480001a020018668730001c4e60003d000c0480a5880080402200403c04016004000048010080600001f0044d05d8010060441200081e0b8000080440085580600004013053014000148120060000c80400242004801062830930000001480000000c0000384b000082240040260340080f00214c009b0002018010044f60000000c0140040301300001c00817006224010013b600c008a200853c098000060080981e012004050000a60680107000a0000400a0140000000508e000058070020040301d07210c890143560302b0ab05898c7426c004128a381400000d3402b004370048302680080600000c040070001d8000af01304a214000000aa06c5800000a0011d8b0696dac0a0f33a4000000f00381140402b014728020025b80011f00d02c008088030228284581900c0e05b0000000041500809a05c01ac700c000031b100000c020020080a00b0b9010000e900306e00c0000e37e2e8018120162b40a000044000028580f2000000320000000000700009003057000064000330740000200104a000010000fe0340480b1423d80200a00000004801000004020120062c4158e90801600b9bb05c04400000054c301d1d400401c028000140180480d0000240083917a000070b94ca0080100106a0e40e00005602940813fc100844bfea84641fffd4032025fec118863fd514c4137f318641effd4b31035f8cb19027fd300c415fea824200f34c832037f8a410827fe64cc81bff1044200ff98931027fa8210843fd50c84317fb2a6223ffd0d32037fea59081bde324c81dfe21c4219ff9023104ffca61901bff20cc813fe21e6424ff54d3200dfcc090
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x564d8532006bf7458d211b5f570cc721006f530d8532006be60d9131035ec724c721176f642d85320067c4359721006f510d8931005f5718ca31006bc6418532006f46518532006bf64989310063f4059721006bc64189311a6f730d8532004ff7058f21006bf64d89311cfb731d9131006bc6498931216bc73d9132176f760cc7211dfcf504c8320067e40594321a6f732d8532186bf72d9121034fd7258c21006be75d913104fcc324c93104ede6318d2100cfc7058432006be53d912104e7c435973101cfe7558c2100cfc70d8931006bc64d8931197b7400c721006f641d85321a7e432d8532006bd51d91310367f4259432006f66018532006f71058b31014fe74d893120ebe72d9132006df3058c210067f7059731006f553d85320067f4159432004f770d8532006dd63cca21006bf4058e21007e520185321f7cf514c83200cfe70584321c6bf10d913104e7f3159731005bd70d9131005ef724c7211efcd414c8321d67e7159731006dd3058c21005f7714c921006bd52d91210067e70597310067f405972105dbe76d91211a6f673d8532004ff70d8d210367d325943214ebc64cc921014fe7458732024f47158c2101cfc755843217ef6521853201c7e75d85320367f20597210367d72594320067e1059731006771059432006bd50d9132006f77158d211c6bc10d91311e7cf704c832006be70d9121027d4314c521006bf53d91311dfcc504c83205dbc744c92100cfc7058e21006bf75d9131035ee72cc72104cff764c52101cfe7558b31026dc3158e21006bf644c921037ce614c832006bf4058c2120f9c32d9132216bc30d91320367f7259432006f51058831005f5718c931005bd7498d210063f40597310067e4059721025f7720c721006bf52d91211dfcd404c832036f72158632006bc6458532006f560d85321c79e31d9131006bc6458d2100cfe70d8931025f4714ca31004ff7058831005bf744ca21036f72158432006771059721006dd5358c210067f4059731004ff7458b3104ede634c721014fc74d8d21006bc75d9132026dc3158c210367d725972104e7e3059432007d730d8532006bd4058732036ec628c931006f460185321df8d404c8321cebf30d9131006dd634c721014bc7458432006f665d8532006bd51d9132006ef628c931005f7701853217df5760c721006bc10d9132006bd75d9132006f543185321a5f770cc721006bc70d913117ef43218532006bf65d91320067f2059731006bf6498532036cf604c832004ff7058a31006bf4058432014fc7458432026f57018532006be30d912104eef3258b3101cfe75d8d21004fd7558d2100cfe7058f21006f520d8532005ed72cc521006b764d8532006bd30d9131006bc65d9121216bf72d91320067e405973104e7e3159731165f570cc4210067f7459731
  | 1 => 0x8b31004ff7058c21004bd70d9121006ed624ca310067d7359721025f7700c721004bd70d9131006be50d91310bdbc7458931176f773d85320bdbe7498931075bc744ca2105ebd72d91210067f7359721006bf51d9132175f572cc421004bd70d9132006ed52588310067e7059432006f740185320057d7598d2118ebf71d9121006be70d91320067d7459432026f57418532006bf648c931136bc648c9311efcc414c832005f7714ca2100cfc7058d21006be20d9131037cf764c832037cf644c832004bf7458831014fc7458f210367d425972100cfc7058732006bf60d9132006f510d8d2101cfe7558d21005bd70d913217ef720185320367f4259721006bc50d9132006f775d8532036f77158432006f551d853204cff764c721006bd71d9132026df7358c211c6bc21d9131004ff74586321dfce504c832004ff7458831006f75218532014fe7458f210067f715943201cfc7558d21006bf7458432006f532185320067c71594320067d205973104e7c4359432006f6401853204edc634c9211dfce704c832005f571cc921034fc76cc52116ef65318532006f710d85320067c7059721006bc60d91310063f4059432007af20d9132216bc53d9132006f440d85321aef560cc72104ef43158732006f410d8532006bf64cc521006bf4058b31006ee52d8931006bc745883104e7f31594320bebd71d9131006f753d8532035cf764c832006bf70d9132024fc7358b31006be71d91320374d654c832006b464d8532004fd7058c2120ebe32d9132006be10d9121027e4214c52100cfe7058c21026f47518532177d632d85321cebc73d9131006bd70d912104fcc324ca31006bd4058f21006f654d8532006be50d913200cfc7058f21006be75d912117ef452185320067e10594321f7cc514c832005f770d8532006f55218532006bf64189311777665cc721004fd70d8931006f664d853200cfe7058732004ff75d8d21024fc7258f2115ef560cc421186be51d91211a7e572cc7210067d4259731006f76198532006ec20d8931006bf60d91211be7e71597210067e7459432004ff7158d2116fe732185320067f7459721006bf71d913200cfe7058e21006f74218532027e6620c7211a6f563cc721006f56518532006dc30d8d21026df7358e21006f770d8532006bc71d91321cebf71d9131004fd7558e21006f6761853218ebc52d9121006bf72d913101cfc7558b31006f63018532006bc649853220ebc21d9132004fd7058b310067f4059432004fd7058e2101cfc75d8d21006bd50d9131005bf7458d21006be20d91321257e75d85320067e1059721006f51058a311cebc30d91310067d7059721006ee5258831004fd75d85320067d65cc7210067e75d8532014fc7458a31004ff7558a3118ebf20d91210367f2059432006b710d9121006f
  | 2 => 0xcfc70d853200cfc7058632006bd4058432006f464d8532006bd75d9131004fd7558f21006f55418532004ff7558f21007ad20d9132004ff70584320067c7459721006f540d85320067d30597210367e4259721006cf764c832026e42158831025f6718ca310067f305972100cfe70d8d2117f76650c721007b740d8532006be60d9132005bf744ca3104eec3258b31004fd74d8532006bc73d912104cfe76d8d21014bc7458d21006be65d9131175f572cc721034ff764ca31006f475d8532006bc75d9121006f474d8532005bf70d9121006bd4058831037cc644c8321dfce404c8320067e4259731014fc7458b310657e75cc521006bd4058a31007d53018532006df634c521007d73018532005f571cca21037e4214c9210367c7259721006bc60d9132006f620d85320367f3259721006bd73d9121004fd7558a310bebd31d9131014fc7458d21036ec624c931176f672d853204e7d305973104e7f3059731006751059721004ff74d8d21006bc50d9131014fc74d85321a6f5630c721006bc51d91320367d21597210067d7059432005bf744c721006f743d85321be7e4159721006bc64d8d211be7c3159721006b740d8532007b7401853204ede63cca21006f640d8532006bd10d9132036de3258c2116ef576cc421006dd63cc72101cfc75d893116f7575cc421006f51058e21006f454d8532026f47418532006f71058732006bf51d91311dfc7104c832006dc4358f211cfb431d9131006bd20d91210367d2059432004ff7558d211a6f643d8532007b764d85321cebc32d913104edc63cc521006ed52d8931006f65018532014fe7458831006b740185320067d7159432006751059731004ff755843200cfe7058a31006bc20d9131004fd755843217ef7600c7211c6be21d9131025f6718c931207cd754c8320bdbe76d9131006f51058c2100cfe7058632006bf40d853220ebf21d9132006bf6418d21026f67318532007cf714c83215fb540cc42108dbc744c72104e7f3259731176f442d853200cfe7058831006ef2058831006f754185320067d7459731037cc604c8320057d75cc521014fc74586320067e705972104e7d31594320367e205943204e7d73597311d67e415973116ef4431853204e7c3159731175f772cc421037ce654c8320374e654c832004ff7058d21004fd70d8532006ef624c9310367d4259432006de4358c21006bf73d9121005bf744c931014fe7458a31006bf50d9132006f51058632006bd4058d21177d432d85321efcf414c832006f550d853220ebc32d91321a6f430d85321cebc53d9131007b464d85321dfcc704c83204ef731584321f7cc754c832024ff7158c210367d20597210067f745943211ebd73d91321dfcd104c832007c4714c832006bc7458c21006f670d8532006f774d8532006ec425
  | 3 => 0xd6318d21005f57018532186bf10d912116ef7321853211ebc644c931026f6741853205ebe76d9121006bf53d91210067c40594321a77675cc7210077575d8532006de30d8d21004ff7058632004fd705863211dbe76d913204e7e7359731007b76418532006f55318532004fd7558632026de3158c210067c42597310067d7259731006f674d85320367e2159721007b710d9121006be73d9121026f662cc721026f47318532006be30d91311777565cc721006dd4358c210f67f71597310067c4059721006bf52d9132037cd604c832034fc764c521004ff70d893120ebc20d91320067f70594320057d75d8532006bd70d913220ebc52d91320067e745972101cfe75d853201cfc75d8532006ed2058831006df6398d21175f576cc721006bd52d9132006bc7458432006f66518532217af32d9132006b710d9132006f750d8532005f7714c93104e7d735943204ef431584320067575d85320067e71594320367e7259432034ff7258c211d67c1059731036ee628ca3104e7f3059432006bd65d9132007b540d85321be7c1059721007b710d913104e7c3059731006f64158432024fd7158831024fe71d8d21006f71058f21037cf654c83204e7e7359432004ff7558e21006f751d8532004fd745843211ebd32d91320bdbc744c931196f5600c7211be7f1059721006bf64d853204e7f735973104e7d3059432006f541d8532014fc74587320bebc644c521004ff7558b31004f57018532006b540d8532006f470d8532004fd764c521176f432d8532006be52d9131006ed4258831026f77018532176f761189311efcf544c8320367e42594321d67e215973118ebc72d9121006bd30d9121014fe745863211dbc7458532006f51058b31006bf30d9121176f420d8532006bf64cc921006bd10d9131006bd40d8931014bc7458c21006bc65d91321a6f453d8532006f52018532006b764185321afb540cc72100cfc70d8d211dfce104c832006f760d8532006be60d9121006be30d9132006f765d8532014be76d9131006bd40586320c67e654c721026f763cc4210367f3259432036dc3258c21006bf4058732006bf70d91311c6be71d9131037cd654c8321c6be31d91310367d21594321c6bc51d9131176f76198d211f7ce514c832006f56018532014fc7458c21004fd7458632006751059432034fc73587321df8f404c83220ebe52d9132006f764185321dfcf404c832006b510d9121176f763cc72104e7c3159432004fd74588311d67f105973105ebd21d9121037cf614c832006bd53d9121006f54218532014fc7458e210067c4059731007e720d8532186bc71d9121186bc31d9121006bf50d913104ede63cc72116f7675cc42119df5700c721026f77518532006f651d8532006bf6458d21176f632d8532005ed72cc721006f650d8532
  | 4 => 0x8a31006f65418532006bd4058e211decd604c832024ff7358c21006dd634ca21037cd644c83201cfe7558a31006f741d8532006bc64d8532024fc76cc92118fb421d9121005ef724c52100cfc7058c211f7ce754c832034fe7258c210067d405972104e7e4359432007cd714c832006bf4058d21004ff7258d21004fd7558831006bd52d913101cfe7558632004ff7558632004bf7458432197b5400c7210067c705973117fd632185320067675d853205dbe7498d21006f753185320067d4059731176f662cc4210067e4159432006bf65d9131006ef7258d21006bd72d9131034fe76cc521006bd4058c2101cfc7558e21024fc71d8931006f76518532004ff75d8532006f44018532004ff70587320657e7598d210063d40597310367c425943218ebe72d9121006b46418532006ee4258831004fd74d8d21035ee72cc521216bf31d9132006be75d9132006bc70d912101cfc75588311a6f772d8532014fe7458d21006bd65d9131006de53d8d21034fc72586320367e2059721216be73d9132006bd50d912101cfe7558831014fc74588310367c2159721006ef4258b31004f77158d21004ff7458e21006f464185320067f4359721007e520d8532026f6611853200cfc7058831014fe7458c210067c7359721006be10d913204e7c3059432006f71058432004ff7458432006bc6498d2116ef563cc42104e7e3259731014be76d9132006f66418532176f652d8532014fc74d8931004fd7458c21004ff7558732037ce604c832006be51d9132006bf4058f21006dd3058f210067e4359721006f660d85320078f744c832006df3058f21014be76d9121004fd74587321c6bf73d9131006b710d913105ebd71d9121006f460d853204e7f4359731006f71058d21024fc764c9210067c1059432006bd60d9121186be21d9121024fe76cc921006bc52d9131187ae21d9121004fd7458d21026f5760c7210367e21594321e7cd704c832007b710d913204e7e435973100cfc7058b31004ff7058e2101cfe7558f21006bd40d8d211d67c2159731006f530185320067c30597210067e2059731006f77158b311a77575cc721006f510d8532006f56418532006f451d85320367c4259721005f7714ca31006df634c92101cfc7558a31024fe7158c2117ef6421853220ebf20d91320067c7059432004ff7458f21006bd51d912116ef73018532006bc65d9131006f543d8532004ff70d8532006bf52d9131005bf745893101cfe7558732006bf644c9311efcd544c832216be53d9132004ff745873204edc63cc92116fe43218532006be72d9131026de3158e21024fc7158c2104e7f73594320d5bc744ca31006f5611853204eef7258b310067f10594321c79c31d9131186bc10d9121026d43158c21006f441d8532006f450d8532025f4714c921006d
  | 5 => 0x7b510d9131006bc7458d210067d4159432006bf7458831006f7431853216ef64318532004fd75d8d21026f4715883118fb721d91211dfcc104c832177e672cc7210067d4159731006be65d9121004f570d853218ebc32d91210367f2159721207cf754c832037cc654c832006f620185320057d75cc721006f740d8532005bf7458532026f47218532026f774185321ef8c744c832004fd75d8931006be65d91320bebd73d9131037cf604c832014fe7458b31006f45418532034fc72d8d211d67c71597311efcc744c832006bc50d9121006bf405883104e7d43597310067d1059731006bf60d9131004fd7058831006f630d8532007cc714c832176f720d8532025f671cc92101cfc7558c210f67e65cc7211efce544c83201cfe75d8931007ce714c8320957e75cc721006bd4058b31006bf4058a31006be10d913100cfe7058d21006bc75d9131006bc70d91320067d654c721177d663cc721006bc53d91210367e325943201cfc7558632004fe7618d21026ef7258a31006bd20d91321d67c4159731036f42158432187ac21d9121026ef72588311cebe73d913117ef76118d21006f710d8931006bd60d9132024fe71d893104ef77158732037cc614c832006bc60d9121006ed62189311ffcd744c832004fd7058f21026ee21588310063d405943220ebf73d913201cfe7558e21037cd614c832026ee2158a31006f710586320067d70597310367e325972117ef44218532036df7358f210067d415972104e7d315973117f75650c721005bd70d9121006be50d91210367c32597211a7e732d853218ebe32d9121176f452d8532004ff7458d210067d4059432025f4714ca211efce414c8320077675d8532007b464185320367c2059721025f673cc421177d563cc7210067f7059721006bf7458c211cebf31d9131006df63cc521006f55018532006be20d9121006f575d8532004ff7458a31026f760cc4210067e735972101cfc7558732006f552d853216ef4301853217fd43218532006bf64d8d21006bc30d9121026f57518532026f77318532006f742d8532026f77218532037ce644c83215fb740cc421006bf20d9131035ec724c521006de5358c21004ff74d8532004fd7558b3104eef3258831004fd74d8931006f565d8532014fe74d8d210063d40597210079d30d91320067e7259731006ef2058b31034fc7258c21006f51058732006f752d8532006bd70d91310067c7459731004ff74d893100cfe70d85320067c20597310079f30d91320367c2159432186bc21d9121004ff75d8931027d673cc42104e7f4359432006f465d853211ebc644c92101cfc7558f211dfc5104c83204e7c3259731004bf7458d21037cc324c921004fd7458a3117ef7630c72104fd4314c9311c6be51d9131026f7105883101cfe7558432026f7105
  | 6 => 0xc6418d210c57e759893111ebe76d9132036dc3258f21025f671cca210067e7459731025f4714c9310067f4159721026f71058c21006f554d853218ebe52d9121006f542d8532006b510d9131036ee6218931014fe74d85320067f4259731006ef62989311efcc544c832005bf744c521006f750185320067710597310067d75d853204e7c7359432004fd7058d211c6bc71d9131027e662cc421014fe7458e21006bd53d9131024f770185320067e30597211c6bc31d9131007d530d8532004fd7458f2116ef45318532006f51058d21006f45018532014fe745843204e7d3259731024fc764c931024fd7158c211cebe53d9131006f675d8532004fd7558732006bd75d9121006bf6458931006bf6418532004bf70d9121024fc7158e21186bc51d9121216bf30d9132006ed2058b31004fd7058732005f67618532006bd53d913204e7e315943220ebc72d9132186be31d9121004fd7458e21006bd40d8532004bf7458c2111dbe749853217ef420185320067d1059432005bf70d9132006bd10d91210067f725973104e7d4359432006bc72d913100cfe7058b31006ed628ca31036f42158632004ff7458c210367c7259432007b510d9121024ff715883105dbc744c521006bd65d91210067f41597311be7c7159721006f76018532014bc7458831026f47158c21005bd74985320067d7459721034fe72d8d21006bc64589310067c41594321dfcd504c832006f54018532186be71d9121006bd60d9131004fd7058a31006f541584320067c745943204e7e3059731026ec2158a310bebe76d91310967f7159721006bf75d9132216bf32d9132217ac32d9132024fe768c931007e7201853216df770cc4211be7e3159721026ec2158831025f673cc721005bf744c921036de3258f21026f47018532006f710d8d21006f570d85320047d75d8532006b540185321a6f576cc721216bc31d9132006b510d9132006bf70d9121036f77158632006be70d9131006f754d8532004fd7558c21004bf70d9132006bf40d8931006bd20d913117ef63218532026f67018532004ff7558c21005f570d85321afb740cc72105dbc7458d2118ebc20d91210067d715972100cfc7058a311f7cd514c832037cc324ca211a6f443d8532027d6730c721006bf4058632005bd7498931025f576cc421004ff7058b31006f51058f21006bf644c521006bf64585320367c3259432006df4358f210057d75989310067d1059721026f42158831006f610d85320067d4359721006bf50d912118ebf21d9121004fd7458b310eebc64cc5210367f2159432007c7714c8321ffcf744c8321efce744c8320367c2059432036ee624ca31004ff7558831006bf51d912111ebd72d91321dfcc404c8321a6f653d8532026f43158c2104e7c7359731006bf65d91211be7c4159721
  | 7 => 0xc0040200004a0001100f27c0080f02000c00009000038104148270040780017a0000380f82f0180100183302c0d00181e6fe0080001e00201c0000100a0044200206a0380100400039c04864000010222d10020060f81200603c0009c01a005920040000000001000413c060021100100700e58e004110410300740d00001403800126032048118100000740480001e01c1380100c0000480e00800005a4c0000180380900209c2f8e90000080001202801d4e88702e01c398594ea0a8018250f00014503605c430008200040140c01203600000001000110008000200040200203406c0b00000c000180050040b40800a0140000401100a0e83200600a000000000000000b0000120000080802401c0680500e028078260081042380002e0042480000e0080080107a0bc0300901a0000080000a0000083a01476c2784c000050000110081942a8081ea00007806024114030000080040300f01c1f4000480622701100f1260340b00b00c00400045032430130000200000102a00002c0101623001c6b80000c1b9718000000041b000000008000057fe0c01e82f00a0101e8040000000901d00801c01005020000020210020602d81e0001d8080090000241306a05613c3900501c050021320001180300203a000050050e601c048000000000180b000010138461ba074020034be02800236004014028000044c1a681d0b20000700202000cb402f004024008000100840b81c0000100100a00400405800044014038011160640000000600c0904e01200043001000020000010060000100a003278060120020000000000815c138520060000a804000874000000000303c00300a0040002501601c0180700c010000750040000181d0020184f8010020140000003204c0201500410c0015502a0000000306008c12abd01e0281a800004bf70d91310367e7259721006bf75d91210367f7259721024fc71d8d2104cff764ca210067d715973104ef7315873204eec3258831006bf10d9132004fd70584321dfcf104c832006f764d8532024fc7158a31006f77158f21006bf53d913217df5720c721006f51058432005bf70d9131026f71058e21006bf6498d21006df7358d210367d3259721006bf40d8d2104edc634c5211cebf32d913120f9e32d91320067c7259731026f67518532007b510d9132006bd30d9132004fd70d8d21006f574d8532006dd53d8d21026f67218532007b54018532006ee20d893104ede634ca21006df63cc921006b
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6d820c165c840147b09b9acb90907c3597744c8320043ec3884b2e62008bd87d4b644c401972e0306c89880a2f21f4058d211c55b40ca1b226200ab581143644c80117b0f186c898802ad60670d91310061eba8ebb2242008be8719163484a771d0fba264190022f61f52d91210055b420e1b0a64008f587940614c80155f04b06c898913ac5c140185320051fc2ac1b226200cf370441618c8015cb04280c2990032d5c310d91210055a422ca30a6455a758184165cc4091ed0e280c299012b920520588310045ec3ea7b226400a7585180614c8014790ab86c89094e2fa1f644c9310043fc32eb98e4200ad583d50614c80196ae1886c8988022f60374588310061fba4e8b2e4206a6e8284165c840156d09306c2990021fe1570588310061f3aec9b0a6400a7585dc3614c85dccca5a96c2990022fa1f40584320070fa9ca7b22422ebc6871c5320c8018e90e882ca19003acd8110d91210065a326e29926200cb570503614c8134b906a0acb988028fe1171597210055ac26a7b0a6400a3d85183644c8015ab06286c2990032ee0170d91321d53a40ae4b2e6200cb764dc0614c8691ed0f882c7908d2b921920d85321bd3bc0220b2e4200ab684d4f614c809968c2ba4c2990022f61e10d913203476412e8b0c6409a5e831c1650c89d0ff0e882cb90802ade1165d85320045f438c8b0a6400ab684147614c80117d0db86c8990030f5d540d85320055b42441b0a6430ab6819c3644848355d04286c8990022fe1d65d91210045ec3ca1b224200ab584043614c8014ef0ab00c299002ada1940185320071ba0220b2e42008f687143614c85d1ef02bb2629080a2fa1b74585320061ec3e80b2e4237a76811c165c840147b08102cb98906aba0875d91321a66a31ee2992420087e8708165cc40117b0e28ec8990032ddc110d91320063a42ae030a6400e3740441650c8011ed0f286c299003b1583714c832007c3ba0e29906400c7575147614c80156d09386c2990022fa1f64585320055ac0c61b22424e87f8744165cc40187f0ab86c8908be3d21d10588310055bc226430a6400ae581083624c47117d0fa9ec898802a7e0d60d91210247643aa4b1062008bd87d4f644c40147d09382cb908bab9a0870d85320051ec2440b2e6200e3585193614c8015e700b2ec29901a9ba0870597210055ac08e1b226400ccd75dd9320c801c690a886c898802ad61270d85320063bc3a20b286400a3c8544364484a347b09202cb9091a2fa1b744c9310055ac08a1b226200ab681883644c85b5a906882c610802aba0850d91310051f42420b286439a9e83083644c4091b90ea1ac6108033c5c140185320047bc3aca30a6400a9e8314364484010fd0e182cb908030f9d7649893104c6e41ae0b10623aa768110165cc40156f02b2ec89900a2fa1b7458d21
  | 1 => 0xb0b39ec8908032ddc310d91310051f42ce7b224200a3f855c3644c86355d04186c89081ab3a0b634c9210055b408e1b2264038f787547614c80187cebb2662908d2b5a0c50d85320065b3b6c830a640087e87d0165c840517d0dba2c4989262fa1f644c9210065bb8681b0a6400c3d75193614c80147b08382cb908022f21d40588310145e43e80b1842008be87083644c40147b09382ca190bbb1d83714c8320055bc22c030a6400e36849d7614c80517f0fb06c890802ad60650d91310061fc2ae1b22622ebc4824c3614c85d5ab07ba6c2990028fa1430d91210051f42420b2e4200ab486d00614c86f4ed03182cb908029d617401853200c77436e498a4200a75851d3614c8010fb0bb86c2990032dd93714c9310065a3a6e2b1a4200e3685190614c80117b0e186c8908031d6177158d210055ac00c830a64008bd879c3644c40147d09382cb988031de1570185320045ec3cc1b226200e354044165c84018eaeba8ec2990038dd0310597310045f43a80b1062048f4815d1630849d8ef0e882cb988033cdc110587320043ec3e80b2e625ac7675443614c88353b063aec89901b1b18975989310045ec3c41b226200e3675d03614c80156b08386c2990030f61f405943200c7a43a20b0e6400ab584d4c614c8014eb0a326c2990032ddd37158d210047ac3c4030a6430eb380443644840187ccbba263908029d60670597210053b42cec30a6400c6d75d8a624c48d96ced886c8988022f61e60d912126c3e43a20b2e6200c3d75192624c4138b8c6bacc6908029de1510d85321865a38ee8b10622fae682d50614c80196ee820ec2990022f61e20d91210247b4388030a64048f4815d56308401c6a8220aca1910f2d1d1105883100747bb6e89906400ab684843614c80187f0ab86c8990032ddd110588312655ac0c21b224200ab681943644c80156d09180c2990063d2077058d210053ac0c80b2e62028f787507614c801968c8b86c2990023da1e40d85320045f43ea5b2262008bd879c36448495968e23a2c418802ad60364d85320055ac0841b226200eb380500614c8014e90ab00c299113a50c54058c2100c7c402eab1a420087f855c1610c80147d08102cb98803e1d00714c8320061f43e80b2e62008bc875016348401878e8b2a63908bb3918b714c9311c74a18ee8b1842428be87d4b644c8014ed02202ca1900237e1d6318d2100678b86c1b0a6400cb7645c0614c80117b0e286c8988028fe1171597311756a43261b0a6400c3f749d1650c861968e3b2264908028fa10305972100636b2ee498e4200ab484580614c8015e100b2ec2990029d604305972122e5a38e80b184200cb970d83644c8014790ab86c8989371d21d10597210065cb86c1b224234ae5821c3614c8070fd0bb86c2990eb9ce011059731006e3ba8e29906400
  | 2 => 0x76398d2100537410e0b2e62028bc845d931484014ed0ba06c2990063d21d105843200678b82a030a6439ab486443644c40147f0ab86c8988b6f120d201853218c5f43c21b224200e35849d7614c8711790dba2c498802ad61060d85320051ec2060b2e42008be87143644c40117b0f286c8988063b21d20588310045f438c8b126200bc580dc5320c8011ef02ba2c6909770f9d740d85321c45f43c61b226200e3675503614c801c6ea92a6c2990029d20574594320071a42a21b224245ea421d01620c49f4eb03082ca190038dd0310594320045fc22ec98a42008f580dc563484bd56d02086c899002ad20565d91320051f420e0b286400f4585dc5320c80169b0bb8a641902697a0c20597310054ec18a1b2262018ec8748162cc40517f0fb06c8988c2ada0620d91210053ac0c60b2e42028bc845c1630840117d0e386c898802b360c20d89310045fc3acbb226400e8d60dd1320c80156d02286c8990123d2057058c2121e5b3b221b224200a3e84041650c8071df0ea96c4988023d61e30185320053ac0c80b286400f8774dc5320c8014ed0a300c2990029da1774d85320257240a84b10624bcb474c4163484091ed0f100c299003b1443764c8320055ac2441b0a64008bd879c3644c80157700b2ec8990021fe1570587320055b43681b0a64008f587180614c80147d0b396c8988d39594f53d85320051ec2861b224204ae481549620c4010fb0bb8ac6908e2ada0450d9131007c2a00e29906400a77815d165c84011eb0f200c299003b1dd8714c83221e5a3a220b0864008bd87997644c47156f00886c8989132d1c54058c211d53a40ae8b2e62008be87943644846fc6882a0acb908030f5d764989310055ac20a3b0a642fae4824c0614c8018ecebb86c299002ab60850d91210065bba620b1a42008f587103614c8091ed0f200c2990032d9d3619853200c7a43a20b1a4200ab684943614c8070f90ab82c4188bbd1997714c8320051e42ac1b226234ae582dd3614c801c6f0a886c8908029de0572597310071dc0280b2e6200cb774441630840156b09180c2990022fa1d4058d2117d73410a030a6400a758110165c840117d0f086c8990d2b5a0c70d85320061ebaec998a423aa768188165cc401972e0306c890803ac18110d91210256a40a60b184200ab584140614c801b8ce038a6419002ada13521853203636392ca98e4200e7380441650c871968e3ba2c6108030f597744c7211c55b408e1b2262008bd878c3644c80196ae1886c899002ad60650d913200678b80c030a6456a3e8410165cc40117f08baac2190029d21510d853221556c10e1b22642ff45651c5320c8011ed0e206c2990031d5d710d85320051ec20e2b286400e3585d03614c8754ed02102cb9880e37e1d53d8d210052ec18e0b2e4200a5d8384165cc40147
  | 3 => 0xbb0a6400e3585190614c80187d0fa02ca190030f9d76498d210061ebae81b0a64008be870c3644840156b03106c8988022fa1c70d91210065ab8221b224239ab5811c3644c40196ae9b0cc299003a3d03764c83200567c32e29906400a75819c165cc40196ae0886c8988022fa1c10d91320145e422e0b1a4242a9e831d7644c80196ee93a6c2990c2ada0650d91211bf39c0220b2e4200a3f85443644c45f5c904882c418802ada1010d85320065a326e1b0a6438e3651d47644c46156d02186c8908033c5c240185320054ec18a1b22642ead5831c3614c87bb1d0fba264190029d60420597310047ac3ca1b0a64008f587883614c8014790ab86c89900e1fa1774d85320346e41ae8b0e6438ab6818c3644c401d8ac038a64190022fa1d4058c210053ac2ee9b0a6400a76819c1650c80117d0fa02c61080297e0d41597311845f43c41b224200cb570d00614c801c6ea92a0c29908e2f61c60d91320051f420e0b2e624fa758184165c840156d0ca06c29900333dd7764c83229537c12e2b2e4200e3685d00614c8010fb0fa02cb90803acd8110d91310045ec3ca1b226400cb770c43644840156d09328c2990023de1d641853204c7743e84b166258a5f835c565cc40153b06106c8988022fa1b70d912118c5e43ec898a4200af380594614c80159b0d38a6419012b52055358c210071b3a8c9b0a640087d8710d65c840147d0838aca191078b94b52d91320062fb9ce6b2e423db8e849c5320c801878c8bae62908b6b520d20185320061e42ae1b2242028be87dd163084018eaeab86c2990038d503105973101c3e42ae0b1842008df835c163484011790ea02c21901a37a1f4358f211d53b40ce0b2e6200ab880597644c80153906b06c8908022fe1170584322bd1ec2480b2e6200e3b80501650c801f08e838a6419002ad61260d8532176e3bb6e299064048f6878c0614c8014db05082cb908021fa1c42597311cdca41a21b226200ab584940614c80156d08280c2990028f61210597310055a4226430a6400ae582d50614c8015ab02186c6908d2b5a0f74d85322155643241b226450a3e84101650c80156b09a90c2990029da1464185322763bc3a20b2e4200aad82997644c47b71908b8a6419002ada12201853222e5bb868030a6400a7785583614c80196ee0a06c2990869b608705943200566c1061b1a42478be87d913148495d48423a2c418802ad61265d8532005c6c06e89906400ab486500614c8018790ab86c8990031de1d75d85320055b420c1b0a6400a3c845c5650c80196ee9882c219002e3e11714c832006e3438e299064018dc874c16308473d1865b2264988028f61270597210055ac08a1b224237a768110165c8461d4843ba2c4188c6aba0850d91210055b40ce1b226400e3575d93614c801f0e21ba26419003175d
  | 4 => 0x3484010fb0fa02ca190032ddc671d91322374a188e8b1842008f587980614c801968c9b80c299002ad60630d913216d6b41ea830a6400a7585d03614c80196ae0a00c2990ea9de0110597310047ac3c61b0a642fad4864c0614c80117d0db86c8988030fdd274597310055bc22ca30a64008be87883644c4018ed0bb8ac6908031d5d475d85320045f438e1b226404cf3805c0614c86f4e902b9acb9090aab60875d91320045ec3cc1b226400a3c85443644c8254db04382cb908028fa1372597310047b43e20b1a423aa76811c165cc401b8aea38a64190bef1a06714c8320071ba0220b2e62008f587143614c80d59904982c6108e2ada0670d91310055b42461b0a64008bd879976448401958c8b9662908063721d3058f2100566c06ec9906400ab681997644c88796cec886c8988021fe1d10594320055ac0ca1b224200ab6849d7614c80117f0eb2ec8988033c5c250185320063b42ee1b0a6400f8740dc5320c8015ad0d980c299002b9e0930185320043ec2ee9b0a6400ab5818c3644c46f4e902ba2cb90803ace0140d853220d4ec1ee3b226400ae582d4c614c80117f08b82c418802b3e03764c8320047b436e030a6430ab6811c3644846374904886c8908028f21510d91310366743eec9906400cb764dc532484a347b09202ca19002ada1260185320045fc22eab1842028bc845c1610c801c6e81882cb908022f61e10d91310043f43e80b2e62028bc845d5630840156b0332ec8990028fa1460d91320055b408c1b226400a6f8250565c840156908b06c299003ac18110d913116d724324030a6400af080594614c80156b03106c8990030f5d475d91310045ec06e8b0864008bc87501630840196ee3a02c69080b271d24358c210045f43ea7b224239a9e83143644c40d4dd04382ca190032ddc310d91320051ec2420b286400ad583140614c88996ee0a00c29901a9ba08305972120d4e43261b22640087f855c163484015cb04286c2990028fa1220597310055b426a630a64008bf845c163084091ed0d3b0c2990028fa1470d91320051fc2a21b226403c7675947614c85d5cd05ba6c2990022fe1d60d913200c7bc3a21b0a6400a75819c1650c88571906906c8990ea9da06405973118d5a43221b224200ab486443644c80156902b06c8990022f61c10d913220c5e436e8b0a6431ab5811c364484014eb0a306c2990029d60640597212e61f3aa81b0a64008be87943644c48796cec886c8990029d21560d85322170f29ea7b226444ea421501620c48553d06386c8990022fa1e50d91320061ebaec9b0a64428be87883644c801c690a886c8990038d50310594320065dc02e1b22624dc748744165cc40156d03186c899002ad61265185320051fc2ae1b224202cb474905610c80156908b2ec299002ad60460d91320055ac24e
  | 5 => 0x8c7a30cb644c9212fd5ac0c21b2264008f587100614c8014eb0a386c2990029da1460d85320063abaee1b0a6400a9d83997644840156b02186c8908e3ace0110d91310051ec26e4b2e6243cb47444163484015af06900c2990c22f21f644c9210045ec3ccbb226400c3e87d0165c8401f0a81b8a6419002ad60670d912100c7a43a20b0c64008bf875836448401b62e0a00c299003b1ddb714c8320145e43e80b086400cb970d83644c40117b0e286c890802ab60830d912103476412e0b1842308bc86dd163484010f90e882ca190032d193714c92120c5f43c61b2264008bd87883644c85b5ad06280c29912a2fa1b744c921007463a6ec990642ef4565dc5320c8011ef02baac690802a760c50d91210045f438a3b22645bc7675c43614c80117d0fa02c41890aa7a0f71d91320045ec06e8b184200cf370441610c8014ed0a3a6c299002e3612714c8320055ac2461b0a64008bf845d5620c40196ee2a02c6908031d61770d85320063abaa21b0a64008f587994614c8014eb02202cb988022f61f52d91320065bba220b1a4202cb674507614c8010fd0e21acb90802ad21161185320065dc02e1b224200c3d75d92634845f78904980c299152ad60610d91310055ac20a1b0a6400cb4645c0614c89b0f90e882cb90802ad60660d91320055ac2421b0a64308be87d4b6448401c6b0ba00c29901a9b20941597210051ec24e0b2e62048dc8754d630840147b08382ca190023d61c50185321865b886e8b1062028bc845d5610c8015cd0d900c299002ada1352d8532227593828030a6400a75811c1650c871968e3b22649880a2f21f4058831005e3c06e29906400c3d87d0165cc40153d0732ec8908028f61010594320053bc0ae8b2e62028bc845d563484014eb0a320c299002ade1161185321855bc0221b2242008bf845c163484019e2e1b00c2990271718d75cc5210055ac06c830a6439e1e53d4f644c4070f90ab82c2190c2ada0450d912100658b828030a6400f4685dc5320c8010ff0eb2e63908023da1d1058d210053b40c80b286400a3e848c165c841717b0e306c8908032d5c110d91321747bc32e39944200c3e75192634840156f08b06c2990032dd9170d85320055a43681b0a64008fb805d563484014ed0a386c29907a9760c70597310053bc0ae8b286400e3575d03614c80147d0bb8ec8990023de1d61185320145e422e0b106200a3d859cb644c47317d0f086c8988033c5c060d853220f47b06e89906400cb770443644c401d1a81bb264190028f61070597310145e422eab106241f0e65dd1320c85d5cd04286c2990029de0573597210051f424e0b286400a75859d8614c801c7700a02cb908023de057058d210065cb80c1b226450a3e8410165c840147d08382cb908ba3da1f1058b31005c7c06e899064008bd80dd16
  | 6 => 0x53b42ee1b0a64008be8714364484011ef0eb00c2990033cdc11058d2100556412c1b226209a5e8384165cc46f4ed02182cb908b63d21d1058c211c55b40c41b226200ab584d4b614c88317d0fa9ec8990038de1510d91320051e42ac1b226400aad82143644c40117b0e106c898802ada0660d91320257240e40b106200ab684180614c8095a903982c610802ad60670d91320053b42e8030a6400a3f85443644840147f08b8aca190030f5d46498d210055ac0c41b2242008be87143644c87117d0e3a2c610802ad21940d853200679c02e1b0a640387c855c1618c8018baebb1e62908e2ada0420d91310047ac3c81b0a644acb676c436448405968e8a0ac2190029d60440594320052f418e0b2e42008be878c36448461c6ca3a8ec8908032dd9370d853217d73416a630a6400ec710dd9320c80156b09300c2990022fa1f4058d210051e422e2b2e6200ab781583644c8014eb02382cb908032d5c340d85320056ac1ea430a640087f855c163084070f90ab82c6908032ddc110d91210bc5ec38c1b226230ab6818c36448413998c6b9662908038de1510d91310051f42841b226200f8474dc5320c80156b09286c299002f1e00714c8320061e42ae1b226200a3e84dcd65c848353b06386c8990029da0470594320063bc0aebb0a64008bd8784364484135a906882c21912f2d1d310584320053ac08e0b2e6200a3c85583644847196e21ba2c61080a2fe1f60d91320071abaa81b0a6409acc83481620c4134bd06382cb988123da1e50185320055ac244030a6442a9e83143644c8070f90ab82c3990022fe1d60d913100557414cbb226241aae821c3644c8014eb03102cb988d2f120d20d853210d2ec18e0b286400a7685193614c80117d0fb22c4988d23da1e20d85320071b3aec9b0a64068f487505610c87d69d0bb8a64190de9da0670597210051e422e2b2e422dad683d48614c8010fb0e182cb908032d9d864185320061f3a8c931262048f481dc16308401c6a81882cb908030f9d464d85320061eba8ebb226441b8c824c3644c80517d0fba2c41890aab60b71d913220ec7bb6e8990642e8f6878c3614c80147b09182cb908032ddd1105843201c3f42ee2b1a4200ab684143614c801b88e038a64190028fa12105973100536c2841b1262008f587990614c85fd8ec038a641910f2d1d11058c210045fc22eab1a4200ab686d00614c80156d09280c2990be3de19718ca3100759c0221b226404ad48150d6308401f0a21ba264190033c5c110d85320043fc2ae0b0c6406ae482441610c80147b0bb8ec8990038da1464d85320055b43621b226431e2e52d4b64484014db04382cb988028f61210597210071aa0220b2e6200a3d851c3644c80117d0fb22c6908029760c20597310051fc2ac1b226400ab580193614c88d968e23a2c61
  | 7 => 0x40a000020000001c1c0041c0000e39c050001001c7c0040300c4a00c170380000401004000089e148020280002405020000001200885368000284104430070030140000c03004080280902c060000010c0600c0b00c050045f000180080811017a5c01d314409f01000450080b1580000025000f41fc8706c66004880000a0b00c000020080f2182a0846a004180000027802000621a0070000001422220050840d0b8320240600c0007469110000000700c0000c0401c10004000389102c010140b030000001f1fc03020080040f02ca500400dfc120000a0302f00068000050040400c460b001010030580b0040a6c0070bc00000000000101000038a3020f002c000006b0245c000010040227c040444801c0084c2d0184b014680040d0680001c032e4090140409c1f0041a0bc010d8d200003018000c00500801000010043347c0004404000020540c0b88a028130cc1800032020170002300003001a2004040b8b60000c0041f2481502c0b0103d00a95000000009007c0c0100101c1007c110102e688000180b0000001c010cda10440001410040030d40b0a8001b8060f4186740302820000010001f010000143d0180700003008070d82c000000084500000008010044705c0407c0a0140500c0c2ec090200a0081a25c080100a124000040009431040080040002c450140203c000040d1dc011fc0147b0a106c898917a50c74058c2125e5b3b621b22640087e87d01650c801c6a80882ca19002ada1265d85320045ec3c61b224200ab584180614c80117b0fa9ec8909222fa1b744c52117ee3bb0e29906400c76755c3614c801c6d0ba06c2990de9da0640597210071aba8c9b0a640087d8708165cc40d998e4b1a63908bfd1994714c8322cd3b40820b28643ae344150565cc4011df0eb10c498802f1600714c8320045f43a80b086400a5d850c3634840155b04286c899003271d1634c7210247643a84b1062008bd87143644c88355d05b8ec8990023be097058d2116f2b29ea630a6400a3f855836448405958e9212c41880a2fa1f74584320
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x19044400107740301008200062c61170940614c801ac380583714c8320061c61570180614c801ac180580714c832007a058140dc5320c8014c497580714c83200471660701c5320c80103d989d464d85320062c21970500614c80164596a17714c8320052c64064dc3614c801c30955c140185320062ca1970500614c801e8160443744c8320052c640645c0614c801235989d464d853200551654701c5320c8015c0905d4714c832006e0601401c5320c80158697d00714c832006a2e0160dd1320c80158497443744c8320056125d401c5320c801235989d740d853200551656871c5320c801e8160500714c8320070ce5570500614c801cc070580714c8320062c61170180614c8898b1845c24018532
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xe0000518350382c038a641900318097601401c5320c801a404bac0a00e29906400d2025d60443744c832
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x209
  | 6 => 0x3
  | 7 => 0x20d
  | 8 => 0x20e
  | 9 => 0x4
  | 10 => 0xb09
  | 11 => 0xb0d
  | 12 => 0xb0e
  | 13 => 0x1409
  | 14 => 0x140d
  | 15 => 0x140e
  | 16 => 0x1549
  | 17 => 0x154d
  | 18 => 0x154e
  | 19 => 0x249
  | 20 => 0x24d
  | 21 => 0x24e
  | 22 => 0xb49
  | 23 => 0xb4d
  | 24 => 0xb4e
  | 25 => 0x1449
  | 26 => 0x144d
  | 27 => 0x144e
  | 28 => 0x16c9
  | 29 => 0x16cd
  | 30 => 0x16ce
  | 31 => 0x3c9
  | 32 => 0x3cd
  | 33 => 0x3ce
  | 34 => 0xcc9
  | 35 => 0xccd
  | 36 => 0xcce
  | 37 => 0x15c9
  | 38 => 0x15cd
  | 39 => 0x15ce
  | 40 => 0x1709
  | 41 => 0x170d
  | 42 => 0x170e
  | 43 => 0x16c211
  | 44 => 0x216d1
  | 45 => 0x20c
  | 46 => 0x16cb
  | 47 => 0x24b
  | 48 => 0x160a
  | 49 => 0x148b
  | 50 => 0x25551
  | 51 => 0x154251
  | 52 => 0x154c
  | 53 => 0x16d551
  | 54 => 0x1556d1
  | 55 => 0xd4a
  | 56 => 0x178a
  | 57 => 0x148c
  | 58 => 0xeca
  | 59 => 0xcc3d1
  | 60 => 0x3ccd1
  | 61 => 0xcc3d5
  | 62 => 0xcc3d6
  | 63 => 0x3ccd5
  | 64 => 0x3ccd6
  | 65 => 0x178b
  | 66 => 0x160c
  | 67 => 0x94d
  | 68 => 0xa0a
  | 69 => 0x180a
  | 70 => 0x58a
  | 71 => 0x28c
  | 72 => 0x28b
  | 73 => 0x40c
  | 74 => 0x40a
  | 75 => 0x138d
  | 76 => 0xb0955
  | 77 => 0x2c9
  | 78 => 0x14c9
  | 79 => 0x94b
  | 80 => 0x180b
  | 81 => 0xa0b
  | 82 => 0x155416
  | 83 => 0x58b
  | 84 => 0xb4955
  | 85 => 0x94c
  | 86 => 0x180c
  | 87 => 0xa0c
  | 88 => 0x16d456
  | 89 => 0x138b
  | 90 => 0x94e
  | 91 => 0x138e
  | 92 => 0xa0e
  | 93 => 0x180e
  | 94 => 0xcd395
  | 95 => 0xcc955
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1135
  | 6 => 1234
  | 5 => 1006
  | 4 => 30
  | 3 => 4
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
  | 8 => 2*((h/35+packedAt gbK8 (1664+(h % 35)*6) 6) % 64)
  | 7 => 2*((h/406+packedAt gbK7 (41995+(h % 406)*11) 11) % 1135)
  | 6 => 2*((h/488+packedAt gbK6 (59232+(h % 488)*11) 11) % 1234)
  | 5 => 2*((h/405+packedAt gbK5 (59354+(h % 405)*10) 10) % 1006)
  | 4 => 2*((h/17+packedAt gbK4 (2100+(h % 17)*5) 5) % 30)
  | 3 => 2*((h/15+packedAt gbK3 (324+(h % 15)*2) 2) % 4)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff03c0f81ff81ff0ffffffc13e88f88e31ff
  | 1 => 0x1f01fc00ffe0ffe0ff0f01e006d97760f3cecc
  | 2 => 0xe001ffff0000fffffff001fff8e1878703ff0f
  | 3 => 0x1ffffffff0000fffffe003f01f807fc0ff0
  | 4 => 0x1ffffffffffff000000003ffe0007fff000
  | 5 => 0xfffe000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x250d00802909290910192524800a0028861055
  | 1 => 0x16152c005b285b28710a0d4182583360b2c6cc
  | 2 => 0x4020555900009452aaa0109b18a18583016b0a
  | 3 => 0x409a6a94520000ccc4d8022d01d805580da0
  | 4 => 0x1489e3b4e79ce79c0008610c37fe0006efb000
  | 5 => 0x98f0003806100610088080103ff5eed0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40525
namespace PEqualNP.Outside.L_meta_40525
open PEqualNP.Outside.L_meta_40525.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 27 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 144 := (concat bs0_3_0 bs0_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 883 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384))) (concat (concat bs0_4_480 bs0_4_576) (concat bs0_4_672 (concat bs0_4_768 bs0_4_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 802 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 4 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 12 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 91 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 794 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 (concat bs4_4_672 bs4_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 741 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 bs4_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 42 := bs4_6_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 4 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 30 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 46 := block_range (n:=46) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1006 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
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
theorem bgb_6_1152 : Interval gbAtlas 6 1152 82 := block_range (n:=82) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1234 := (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152))))
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
theorem bgb_7_1056 : Interval gbAtlas 7 1056 79 := block_range (n:=79) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1135 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat bgb_7_288 (concat bgb_7_384 bgb_7_480))) (concat (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)) (concat bgb_7_864 (concat bgb_7_960 bgb_7_1056))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0feeaeeeafee0eaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276152992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40525.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[1,4]⟩,⟨.and,[2,7]⟩,⟨.and,[1,6]⟩,⟨.or,[2,3]⟩,⟨.and,[9,10]⟩,⟨.or,[0,11]⟩,⟨.or,[5,10]⟩,⟨.and,[3,8]⟩,⟨.or,[12,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276152992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276152992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40525

open PEqualNP.Outside.L_meta_40525 in
theorem PEqualNP.Outside.L_meta_40525 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276152992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276152992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
