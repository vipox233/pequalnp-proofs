import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36432.Model
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


end PEqualNP.Outside.L_meta_36432.Model

namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
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

def SBf (j : Nat) : Nat := [5, 5, 5, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36432

namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
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
  | 1 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 2 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 3 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4310046201108004c04809198091888c085391
  | 2 => 0x490088a240400881441882288824928422c0b4
  | 3 => 0x842551042aa445582225504255022531850c0a
  | 4 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
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
  | 0 => 0xffffc0ff87f843f87f87fff87f07f8093f73c
  | 2 => 0xf0787ff0ff87ffc3f87f8703f87f83ff6cc9cf
  | 3 => 0xff807fff0007fffc007ff803ff8003ff8f0e0f
  | 4 => 0x7ffffff807ffff800003fffffc01f00ff0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x6110046210800804809809198091188c01531c
  | 2 => 0x250088a2400a0081882882288825092424c145
  | 3 => 0xc23551443555455c44555053550232598b0e0a
  | 4 => 0x8a466208a441566a55044082664a6011d00ca0
  | 5 => 0xc64438cc66667b3666664e0440c4061fea000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfafafaaafafaf000fafafaaafafaf000fafafaaafafaf000fafafaaafafaf000fafafaaafafaf000fafafaaafafaf000fafafaaafafaf000fafafaaafafaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7fc3fe0ffff843f87f0fe0ff87fff809733fc
  | 1 => 0xf87fc3ff0787ffc3f87f0ff07f8703ff69cccf
  | 3 => 0xff8003fff807fffc007ff0007ff803ff8e0f0f
  | 4 => 0x3fffff807ffff8000007ffffc01f00ff0
  | 5 => 0xfffffc00000007ffffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x310840261100080480b012231809188c03115c
  | 1 => 0x511004423009004188110461288229142144c5
  | 3 => 0xa22aaa8c4356459c446aa086555052698e0b0a
  | 4 => 0xc6533310a64356eb550881486664e031f00ea0
  | 5 => 0x4622218c4646732664cc98c04408041dca000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x843f441087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d02fca3a05f54740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c52502fea2a07dd4540bba8a817c51503e8a2a05d14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a617c514c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620fb28c417651882faa3107d54620baa8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f460907e4c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bcc820f6190417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10f7294216e52842faa5087b54a10b6a94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fb18a21f531443ee42887d08510fd20221f940443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f741043e882085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a85f75150aeea2a15f14542fa28a85745150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa92837c52507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea9883bf431077a8620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331ef21e63dd43cc6fca598df54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7ee8318fd10631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931fba0a63f4414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87ee8390fd10721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f721243ed42487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ef32087d86410df94421fba0
  | 2 => 0x790b08001c25cc460911840003f0003fe0d8d8a69326858140003e80000000034600000000000618000f9000614c00bc2da358cd24e4b2934588ff43e0b0000882ec000000e80aa9300aa1802639c4f8671900092191d4480002b00037a37cb50f10c24f911a3e37c730770a043c3c86499c19e3f47b2254c662cb780045c28d188c00ee56caf96e3b42351b89204c5201701428060cb180c2f2494520e00004e4f5000000684a38000002ec7a0004b46ac001d40009d84800026685d0a1154728bcf89680be6fcfb86a4543b4bf90249e9d0239e225c000000f501e99000000248000000a134e62458000086604ee26f1262ac450d036a76d2f87300000102127320000001ef2b0294028693581886e9c60b261d1a2540006301e921000000d923638a2a86c9844d06600004b00083cbe0004748f471258046001300be18c2093923b000738a31c8152844851fa3664ec7f2271a4000f3800072838001310d68541e0003764780002234a25c319120f27c91c19541635c3e08913234c8f8bf0dc9b0d326b46a2009618d00000119a510905f46d1e83d84dc1200021e52c000e935a394868d41c81a1331510000e8da2071f83440c037000598a6a7145a004de0163500d013a282f02f48d00d4c446ccc81b14e978e1922102754798000001c8149df0e85d03c1fc0000000006c0bc5913513024075c250843bc0009b1440008c933a4b3e0045240ef0a04ac6690e000078f6800396581208000000000003006a53cd480033600094934000000f49f5000000b58000005640010804a48c6199428400005177000000270002a8104d21e52d21993715d0207ec100210006752b90700832d2d842414728001b04e65680fa4013421c9e20c1e00f81780032c5252e8003c6298e98d84e0874fc8cc000000001dd3887f8000000ea170001f31bc5701684d01600c07014060940600017000460100004c1009c00008120242402c010040301c000140900021028080280102c0801c02020000002a000080000c000000000c04805010020540903c2002800008040100200000064100040f0142002c051141000800008080203c008080300501400004020000607c0102c0c0140c0001a04c0a0100e0000200c0000000010040100108c0e0043b0000004400000110640901c0500c020300203c12010020000000400008110001a0740306c2b0200e004010140500002040050040000003004000140a0000501000000050400602c0400000010030000d01000010160080400015004090001601828004030000c040000a40210c000000503825bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c87f65190eeca321df54643faa8c87755190efca121df54243efa1a87b
  | 3 => 0x13690b09841495083166539101190001f4d508f000678d79c912c2b0512050f47f43b09d2e0970b600002e558bf2211167e0a09d80e250c2da063dc14cdc12f4345948490048c1452493808a1900c85707e000931e110c3a8000c74ca3e90c8db26a648031ba0a8748e39910565c4000af16c578aa8004ee238001b60002d00003100000000000000000000004020007b8000126b922918000001041450700741d8000a486d23a2915c2e4861c13a07d8150120c092871917420450809eb3a2888dba4231e1952b0b70109d5090e62744444c1881d85485423c4aa1fc6a9b92a01100000012a80c7c00022684cd0110380910369e03ac419001d944c5307599f08c5ec0d07b47e2708183310a2785d22b19454c1911c4a0628b92530e02d4ab92d18833824a0d0806388b23018265cf30fb00000d048000004fca50584c28700013d0de1680016715a8b00009b344410991cd1b8000b120200013c5c00e18a2c8039cf2ea4a0c117a4a47084a05d038
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x524c34c528c1309b98b540c26d62d50309d987540c27561d50308f596540c23e64150309798c540c26e62150309b588540c27661150309d584540c32e5494830cb552520c32e5454830cb551520c31d548c830d354a320c31d540c830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430c7553300c369528c03097d95300c31d544c030b3189300c27b654c030da549300c27661d53209d58754c825e63953209758e54c823e6414f208f59053c82766114f209d58453c82e46150b209d987548827561d52209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e20ba58032883673294620d90ca51883c8328c220ba189308836651c82209798e544825d639512097d8d544825c63551209dd85544827461551209798e534826f6254d208f990534823d6414d209d98453482756114d2097994534831e6414d20c7590534834d6214d20d598453483556114d20d6580534834c53909209b195424834c5350920b918542482e860509209b996324834c538c9209b195324834c534c920d314e21482ea6088520d314c2148358538c120f28ca3048278654c120d314e20482e661881209dd85540827461550209798c540825d63150209b988540827661150209d584540823e6414c208f590530826e6214c209d98453082756114c209e980530826d65cc8209b59432082e9600c8209bd9520082cc63480209ed95200825e63153109758c54c426e62153109b58854c426e62d4f109b58b53c423e6494f108f59253c425e63d4b109758f52c42e4624c7109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108f990538423d6414e109b988538426d6214e10d994b41843665210610bc58041843b04190210bc185408436652c42108f992544427761551109798c544425d63151109b988544426d62151108f994544431e6315110c758c544432e6215110cb58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d52442766590510cd15241442746550510cd1514144334548c5109d1953144334544c510b918931442f0604c5109d997214433454c8510bc98321443345408510ce15240443b241901109e19540443345484110b998a104425e63150109758c540426e62150109b588540427661150109e980540426f6254c109b189530423e6414c108f590530426e6214c109b58853042766114c109d987520423e64148108f590520425e63148109758c520427565d04109d59441042f160104109b98a500426d62940109e59610042776544010ad191100427b6544010
  | 1 => 0xcb1e6395032cb98a540ca3e64150329d984540ca7561150329e980540ca79601503297596430cb1e5450c329b596420cb2e5450832e350d420cae4615083297d95320ca6f654c832cd952510cb355494432cd951510cb355454432d590d510cb554354432d9909510cb654254432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032d690d500cb594354032da909500cb694254032da8c9500cb6932540329bd89539066c6254e419b98a509066d6294241d5986531071e5350c41d394e521074d5394841d394d521074d5354841cbd0d521072d4354841d9185521063f65504419dd95411075a5394041d654e501076a5294041da54a501075a5354041d654d501076a5254041da549501073b4354041ce50d50107724154041dc505501066e62953319b58a54cc71e6395331cb98a54cc72d6295331c795143cc66e62152319b588548c67a60152319e580548c6e56210631bc580418c6b664cc6319b98a508c66d62942319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131b5986434c65c6550d31d390c524c74d4314931d9584524c67665d0531d914b414c6d66310531e550c414c6e56210531d9148414c6f16010531ad993314c67661d50319798c540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65f654c4319dd95310c67a60d53219e58354c865e63953219758e54c863e6414f218f59053c867a6014f219e58053c86e46150b21b958841c86f160107219798c548865d63152219e980548867960152219e983538867960d4e218f992538863d6494e21b958432886e9600ca21b9189318865e63951219758e544867761551218f992534863d6494d219bd89534866c65509219d195314865e63150219758c540866e62150219e980540867960150218f990530863d6414c219d984530867a6014c219e580530866d650c821d354c32086e9600c8219d59441087355410421bc580410866f65484219dd9521086766194f409d58653d02776154b409d18552d026f6254e409b189539025f6354a409718d52902b96010640cdd0c51503354314540dc58051503345190140d394e521034d5394840d394d521034d5354840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440c754e41103355190440c754c411031d53d0040dc546401023f6550040c754d40102b461500409ed95401037151500409d98754cc27561d53309b98a54cc26d62953309bd8951cc26c62547309dd85548c27461552309b988548c26d62152309d984548c2756115230b6580328c23f64546308f191518c26e62951309b58a544c26f62551309b189544c27761551309d185544c25c6550d30d390c524c34d4314930da58
  | 2 => 0x292dda06aba1a522a87119ac239e6610a3f0b64f000202b8951843d8fada01200000000028326cbc0468525827a229d3389fa7cb280055994ad2f2322d000018001fc4c8005480074a64000003d03e000988e1000820e6d1d6000001a8d8b700000000c3800b0296cf800003440000094000718007a816b4ae67ca702988430048dc000000000d17a9388200000002726fab6a4394e3b889026e9a2cecf15eda944801d08fba8b33643ba9cbd84296a340000000134c78e400000002a650810a8136002ea52ae8ec02e5000000000a7b009e8001738a000720000067058000000000000386d00002d21641af440ae0002da648440017e698000011a001e439800001a067b4ea20d2c60000030a028a23c0000016c002ba0028e25a26628aa13278c1000eb886001b60000600356000944e000590004792a000a45c0c44722ee0abe7d8b04b0b8a6928d29a4630001b2026f2ac3c8565984e8826a9d8920b0000a04a002c2001ac00190000d60000048312ea8006e9221d000d180098390bb014d50002f3920037200282d98003f800d8b36002aa84b520000000310de00000248b908c0028616b8cc0afe1d8a8d41b2c6b800a93a38036e5978863a668a42df982a62a28b3142f9f4352de821de54000022c66a800a932eb2228df038d239ac733058a10e13a22e97c0023058306b8b5c75398eb030ca060001247b89a970000021c003607e0ac1eafcd6000b5ad80024a000c25db20782f8331da000001e35ac981e37b9c63832e831619b6e000ec338000023c1c0686b8622385053b2c0010803a848a8880016ed78000e8001b800de800000220007e2b852a294665a0432930c9186931260023600252b10dc241585c9ccca93e0140601c0a000010540004007008020000900005004140240105c0702801000010340500c040141a0000a00403014020200503003000090000d0000000c0401802000000040500c0c0080004008058130000001801014000300502016004000040c000130080202400004090c0000100300000000000040e0300100806000020000101801000000300502403008000742303008000000000205401004010001a0240100800000030240c0180000001004020780002c00004020400300c060380000000002ce62d0e43cdd0e5190ece62d0d43ad9864350e6e62141439b5885050e7661141439d5845050e3f6550c4397d954310e766194f429d58653d0b566194f42d558653d0b1e5350f42b398f4290a7661942429d5865090aae62d0d42b398f4250b374314542cd50c5150a3f65508429bd954210a7661d53329d58754ccae46150b329dd85548ca7461552329d986508ca7561942329758e544ca6d62951329dd85544ca7461551329ed81544ca7860551329d987540ca7561d50329e983540ca7960d50328f596540
  | 3 => 0x990ee936c788b25d2facc8ea068da0003c0020a8e8e2702b26a01c44b228912e55188441b8000f8d08000024434000af024b524600334532b07a118318a0458000015a770001016a4134c1f0002280ca01fe7e8640025e000006c0004529400004571c88c800dd1ca001c2000540028c00000001d8431f079a1e0030c0026200180ce9ce999ec178005a2ee002560000000000270003a
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1b0c400a00b4c150e58015c30745221069801525908f000180357001b008011e183a150c6150832e0a86a12a21970943509500cab038a84a8065a150d62105318caec2908298f0543148414c748a1ac020a63981496010531c92a6b006410e3154580410870aa98c2a008183550624c030ac2e0194a31061564584534830cb22c029a419114c6150920c90a630284906485398221482a53ac65182419114e6188120cc4a4b00830860d63588544430cb1ac02a22189150624c510c60a830262886305498321442993ac8320221891526284110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x440d01431c54254032c057650c5210531e01431496010531
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
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (19164+((h/210+packedAt s3K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s3K4 (19544+((h/157+packedAt s3K4 (17974+(h % 157)*10) 10) % 624)*10) 10
  | 3 => packedAt s3K3 (1475+((h/9+packedAt s3K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s3K2 (182+((h/1+packedAt s3K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe0ffc7f07e3ff0e38fe3f03fe381ffc27327f
  | 1 => 0x1ff0ff8ff803c7f03f1fc7fc1fc01c1cd9cc67
  | 2 => 0x1fff000ffffc07ffc01ff8001fffe01f1e0f87
  | 4 => 0xe000000ffffff8ffffe000001fffffe3e00ff8
  | 5 => 0xfffffff0000000ffffffffffe0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc26208813044800208260908c60844c403122b
  | 1 => 0x44a6301211c90a30190a42385a418948494c65
  | 2 => 0x8844592462819456401c90518c92c0911e0686
  | 4 => 0x188a248850202a8b24000a211251302e00950
  | 5 => 0x1108c000c61224cd249124c300060203b4a000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeeeefafa8080fefeeeeefafa8080fefeeeeefafa8080fefeeeeefafa8080fefeeeeefafa8080fefeeeeefafa8080fefeeeeefafa8080fefeeeeefafa8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x243ed42487dc6490fb4c921fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206fd0c40dea18817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fda0461f8408c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a617c514c3f680987e10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bcca20f6194417e51882faa3107bc8620f690c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920bfa8a417c51483f460907e4c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bcc820f6190417e51082faa2107bc8420f6908417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c43dca5885b94b10bea9621ed52c42daa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f481087e50210fd18421f930843f641087e08210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd20221f940443f460887e4c110fd90221f820443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0xe4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6197790c32eea18657e520cbdc84197b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841f7290836e52106faa420fb54841b6a90837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f721643ed42c87dc6590fb4cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110fe94221bd284437d50887f2a110de54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f721
  | 2 => 0x1648c192000000001f90000000024523c034000f8424858501350449a40024d0000009600007e000b90af26c4ac3fa47000948810de000000818ca4ce828000072f611c1013a396000002263aa000002060f62484e9bb45a4589c9bf00075c418f03c0258f80001140f8b29cc000000c180016e2d06e2131e81c89b91223e764ee80000036c0025a000000060d139000104976000000000001f64b800051000000002720001d4bc8000000bc000000009251288d0983a4410c20007bd111230863d83122b04865527163000060b302714a000118784ca1c0b58002b2000fa80035e66c001093fc630b9a03360000000001545a80024b4847249d85a458900c500030e450df15b4cc83c4c9d41dc64c0007300067cb400049e001311043680e81925014c7f4000863042c4002630008d0a81f6116000a31d14de570088691cc18000000000000bb8000000000000043e008ed84600a0013ba243866185e1e52666f0f701f3345e83702824c1251ba7633c00c129670da6513009041840400000000545191e30005a4f8857000000659fb000270000b24b605532056000000000000fa1d0ba16400018c070d40000012f220000255070002343340000026268c170004363804790d2aa38c8ca6126019c3b8ab2ae884af80019c0a432a0b41a698000d03c2278e91c41e4768fa0454b80009c10a2d8360768002da8e92c9de0000011d9320006b0c58580007140b1490002fc000e8000000078b60bc354001d0454614001ed39c8f44611b3489045c9432a6000fe10b1b22a11c87e3ac311008cf1467000008e31a2d4d28a44e80c11f9df39e568580c13d42e0f39dc4e635875a460ba320270002a82a4000000009200000029c2b000000356040908a718a95902a33428680728000000007e1b11a6588090044509c47f19903c268be0410d4574a7a6b3020000b0000307c2a03001000020040304c04000030000a0140100c000280100005008000040600c1a014020280000c00044080080100002010150001d058000000d020030000100000000040080200801004000000300001048020040000804028030080203c000180b0000005c0600402008090000102c07014050080801c05014000400000c0c0100402001000010140101002010180040000c1300c0701419000060980900402004000040600c0c0000002013004020200000403008000080c00c0a03c010001b040030a0020140001801008010380002c01000010000e0080100406028030080100001034010640100403028010040101c080000000c03004010240201409bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121fe94243bd284877d5090ff2a121de54243efa1a87b
  | 3 => 0x2071022104d9470000004f8002222cd178000000000002b000000000003f06a448a514e08a500000000000b72150007a0000000009b4ab000000000000d2000000000c72c0000c80a232c1900023100030121a682e0000928bd28437400000112928d70cc0007e83b04b00021d2c0372a40007a800036000910980f86851c0e103a718d3a3c39487088017000000d406f0880000000043465cd50000b64d0d69bd2fe7b08a8ea226000001880008d48401a000134001c221e94c000063c44f8828351ee4a42f93d2008108386645c644a583901204c358ff2380c400052028660000931b4184c218e282930a024440485c1a03815a6e1040191f47c8388792de35cdc8000b83e48319d058000000000001505f10e364000a600009e0850c000000000281613e64f0788e72187dc001713123cd2b800000000778c637425cac1484462b8001eb18674cd98333b049c9fa3e0aa3250880b0002848b8ec2949a87e9b6094388c017e1284809783d432510da9240000000011d3fe2ec3418f25a028f303610a0ed3627539a070001a22ea0a91b21036e790211c729a7a4000000000050e97d0d81001683c0f4098bc19c28a9512a88843c2012f8df00000024000000391180000a64a9138084ba0000026e2507045d0002bc
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd521034d5354840cbd0d521032d4354840da18152103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374354440cd50d51103706054440cd546411029d6310440dc546401023f65500409ed95401037151500409b98a54cc26d6295330c798e54cc32e6295330cb58a54cc31e5450f309b988548c26d62152309d984548c27561152309b98a518c26d6294630ba588408c2f16110230ae993308c26e62951309b58a544c26f62551309b189544c27761551309d185544c2da6090d3097195434c34e4314930d350c524c36960149309e997404c36852d0130b698c404c3994310130ba588404c3685210130bc584404c2ba64cc1309e983540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c3097d95300c27b654c0309d98754c827561d53209798e54c825d63953208f99053c823d6414f209d98453c82756114f20ba18142c82e96210320bc58440c825e63152209758c548827661152209d584548827661d4e209d587538823e6494e208f59253882e5610ca20ba58032882cc6348620d994521882e8624c2209798e544825d63951209ed81544823e6494d208f592534826f6254d209b1954248278654c1209798c540825d63150209b988540827661150209d584540823e6414c208f59053082766114c209d584530827a6014c209b594320834d530c820b958432082cc63484209e59440083395410020bc584400826f65480209ed95200826e62d53109b58b54c425e63153109758c54c426e62153109b58854c426e62d4f109b58b53c423e6414f108f59053c426e6214f109b58853c42f06050710da94b40c436a5210310bc58440c43b241103109798c548425d63152109b988548426d62152109b98b538426d62d4e108f992538423d6494e109798f528425d63d4a10ba18930842ea62c42108f992544427b60551109798c544425d63151109b988544426d62151108f994544431e6315110c758c544432e6215110cb58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524433454905109d195414427a6590110ce15240443b241901109e19540443385450110ce1523044278654c110ce15130442e8624c110bc185304427a65c8110ce15320442f261c8110ce150204433854c4110ba98b104425e63150109758c540426e62150109b588540427661150109e980540426f6254c109b189530423e6414c108f590530426e6214c109b588530427a6014c109e983520423e64148108f590520425e63148109758c520426e62944109b58a510427965d00109e59440042f161100109e596100427765440109ed9510042b86444010
  | 1 => 0xcb1e6395032cb98a540ca3e64150329d984540ca7561150329e980540ca79601503297596430cb1e5450c329b596420cb2e5450832e350d420cae8605083297d95320ca6f654c832cd952510cb355494432cd951510cb355454432d590d510cb554354432d9909510cb654254432d98c9510cb653254432ce952500cb395494032dc946500cb715194032ce951500cb395454032dc945500cb715154032d690d500cb594354032da909500cb6942540329e98253d06796094f419ed8152d06786054b419bd89539066c6254e4197d8d529065c6354a41ced0c50507394314141ce904505074e5394841d354e521074e5354841d354d521071d53d04418fd95411071d5350441ae18141106776550441d694e50107595394041da94a50107695294041d694d50107595354041da94950107695254041dc905501077141540419e98354cc67960d53319b98a54cc66d62953319bd8950cc66c62543319ed81548c67860552319b988548c66d62152319e980548c6796015231b5584328c63f64542318f191508c66e62951319b58a544c66f62551319b189544c67b60551319e181544c65c6550d31d390c524c74d4314931d9584524c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319798c540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c71d548c831d354a320c71d540c831c7553310c765528c43197d95310c71d544c431b3189310c677654c431d9549310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c67a60d53219e58354c865e63953219758e54c863e6414f218f59053c867a6014f219e58053c86e86050b219e983548867960d52219798c548865d63152219e980548867960152219e983538867960d4e218f990538863d6414e219e98053886796014e21b958432887c4328c621b9189318876b3294221da0ca508876b21942219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d218f990534863d6414d219e98053486796014d2197994534871e6414d21c7590534874d6214d21d5584534875a6014d21d6580534874c53909219b195424874c5350921b918542486e860509219b996324874c538c9219b195324874c534c921d514e31487c6328c5219d195314874c5388521ba982214867b60550219e181540865e63150219758c540866e62150219e980540867960150218f990530863d6414c219b98853086766114c219e98053086796014c219b597320866d650c821b9584320866f6548421b318d210867765484219bd89539026c6254e409b98a519026d6294640a758c41902b96010640d6982531031e5350c40d394e521034d5394840d394
  | 2 => 0x80050000002c4000d4ae8006d99c2d0004db121c23a05b4ec2046002dc6295c2109eaa23e00178000002080088000c3218749aed19dc002e84b800dd0bc002449a800c6800c080040800002007eaec50a0c000004d1567f800e629c59326000003a3960ca681f000e92debfa0a002bc0b8000700003000d897c0287251a8c0521e0033000a96b6b3e0e92435aaa6e9a20036e0000000000d29f6898000022e002f00029e00000c1a8e003923280000000100c000000b824e7b9c4c40005808e001be0034cbdb44001e20000676800000000025695206003606d382a0b38000ae0facc000c491a28b08da2700046b9c99998252101a13a2b3409e37a4a0a87082c16204002700e39a0035ebd38c45b54022c810812bab22b18dca2a40e807485112d9afad483497892001e6b52bea20a6cc9f07ca427191892800000000000000020000007b00016ace520004f0769f1c0930369da1add92039054a6000da02a0000077b0e34000b01803e18c728ba6580054b342827e259d4d93a8a423c1bbac8d9c84b03c6904cb60f6e122a2d8c28b000183569bab6739d80c1a6e40d23f970b8878ae23000000000fa0000000000be00009a505400058b2a612f21eb3c240aa7e2864036a6c000e98e2001260037c5521ce389a21a4800028ad314440b80000018bb09800000000c72d2001580004ea6974948c8a014e9e87e412644232e80a3207a5c3b2ee5b1447ab36892fc000f260986ea93000192df800ac8fc66800c12085295a002a2000506f2a6599fcb58b2438e039932ac292a11cc001909d0f0db10cd73206a386318006b04a000441abae28a587800000234b41947d0000000000370001a0de08a3d3502c0645b800000045a000034000000300c060180201800000010000301c010000a01800028020280201803000020240500020034020181500804000380340b00420028000000900c0a0040509401004000180000c0800013008080000200004028070481800001008010000000400004000240104c0002408014000080d00401008020100501807010010000a000070000f09800004020000201004000000000200c0002401010030480c01000008000000a0100e0200100003014020100b054010140503c00040020140800000002ce62d0e43ced0e5090ece62d0d43ae9824350e6e62145439b5885150e7a60145439e5805150e3f6550c4397d954310e7a6094f429e58253d0b5a6094f42d658253d0b1e5350f42b398f4290a7a60946429e5825190aae62d0d42b398f4250b3b4314142ce50c5050a3f65508429bd954210a7a60d53329e58354ccae86050b329ed81548ca7860552329e982518ca7960946329758e544ca6d62951329dd85544ca7461551329ed81544ca7860551329d987540ca7561d50329e983540ca7960d50328f596540
  | 3 => 0x62114859aa00000c58008e35a0039e002cadcb2442800e213e2625a1581006822039d0170000026c4898ecb12ab916a1b2ac00000002620011e3a8ce5db80a50d819b1ed22a400000530eee51e4ca1b20008017800a808c5c80037b3a5f8247a22247000e884884906221b8b98be5e800d60009c8002915e0020e0631867800330000000000342001d600052c030a002ae0013800000e2
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x184cf7000001c50004910021176cc54040904669400b64d2880ce58006000100002311a250c6050832e0a86a12a21956070509510cb84a1a84a80658654c6050441c1aa83126218d61710ca508870ab22c229a43865916014d21c88a630a8490e485318142486a33ac6518a439214e6088521d1286b10809846976148404c384a18a420261a450d6110130cc0a4b088098644639452188322a9ac2190418c5516110020cc4a4b08818860d63588544430ab1ac22a2218c9964190110c50a831260886305418530443182a4c3902218a15262c4110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x10020d01431c14254432c097650c5210130e01431496110130
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (19164+((h/210+packedAt s4K5 (17064+(h % 210)*10) 10) % 834)*11) 11
  | 4 => packedAt s4K4 (19544+((h/157+packedAt s4K4 (17974+(h % 157)*10) 10) % 624)*10) 10
  | 3 => packedAt s4K3 (1475+((h/9+packedAt s4K3 (1421+(h % 9)*6) 6) % 38)*6) 6
  | 2 => packedAt s4K2 (183+((h/1+packedAt s4K2 (180+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe1ffc7f03e3c71e38fe3f07fe381c1c673667
  | 1 => 0x1fe0ff8ffc03ffe03f1fc7f81fc01ffc99c87f
  | 2 => 0x1fff000ffffc07ffc01ff8001fffe01f1e0f87
  | 3 => 0xe000000ffffff8ffffe000001fffffe3e00ff8
  | 5 => 0xfffffff0000000ffffffffffe0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc2ca288138448a0618260911d6094544231663
  | 1 => 0x4446101208c90020090a42304a4088c809482d
  | 2 => 0x888459245181946a401c90628c92c0911e0a86
  | 3 => 0x118a248a2020294b240008511251302e00550
  | 5 => 0x1110c000c31224d9249124c600060203d4a000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeefeeefc80fc80feeefeeefc80fc80feeefeeefc80fc80feeefeeefc80fc80feeefeeefc80fc80feeefeeefc80fc80feeefeeefc80fc80feeefeeefc80fc80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x243ed32487ec8290fd50521fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410df94421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206fd0c40dea18817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fda0461f8408c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8a61f7514c2eea2985f14530fa28a6174514c3f680987e10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3907d94720bb28e417d51c83eaa3905d54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883f481107e50220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520fd20241f940483f460907e4c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310fd10621f920c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c21f621843ea43085f94210fd18421f930843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443f460887e4c110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2087dcc410fa18821f621043ea42085f94010fda0021f840043f440087e48010fb88021fa10043ea20087e44010
  | 1 => 0xe4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf28885f65110aeca2215f54442faa8885755110afca0217e94042bd280857d5010bf2a0215e54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e83de53d06bca7a0df54f41eea9e835d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ec8398fd50731bf286637d50cc6fea918df95231beaa4637c548c6faa718f790e31eea1c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863de430c7ba8618df94831f7290636e520c6faa418fb54831b6a9063de320c7b86418df94431fb20863f5410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c87ee6390fd0c721bf28643fa50c86f4a190df54321fca86437950c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621fb20c43f541887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719
  | 2 => 0x5d0004d219c818383c20dce387c05075117a5e23620d312040f41dc001300bc000002702304b8b72474ae368bca4d2fe0c48884624a4805b1ed1464f4061cd33a680152112b46fc800a81fc440cc8000003c8a18003b81d8af23d0c693c6980a2a85e8e30d90005a0611463d485cd60ac19896c0f8b22703c06006e3ba80cada160b25dc0b95c4903d4ca80109c170351f01602dcac8722386511926f14453cd68803aa5805f22106a0008b8fd2fc99c9f85015e478c48004ea4900026b00000078800140349341153fa538030202444bcb0a534b20000014933c21815a7629a484000000009c44d996388129209f50007590ea1200030c001cb0827244391f4207ad188103f82c40a0441726e8001934807790d8211b0000490083300b52483e04408cc61410008a4001762085a8000002ea498cd1d742a555198f422c4f912a343509501d20f0fa124ed0cf0902f0680071ce1e0d99884a2820968004765c40000010a25d1e0001c01680007b4484482289e022000000640e8000470004aa528d220c0128e02b8d44ba5742986d0a2000be26416a5890c8001f60004118f07e6f1350ab0006a4488e328e708b798b19c48d2620528a001291662a03a8dd800342000838e80008380008840e44c711d82fa000551b045a2b4f7052076000329364547cced95647c5c131a0126e0003898d1fe6d0079d321e92880974264315069c11b84ac9ca23194290070ed11e7413996d338240b21091d62586325f1a21acc11d902a324199522845203824535452c5f8a630e780da8792886c40f21830029c9e1631027a4269c33ec5c8989973c6180a89e438a36c2386c3081000ea444860012c1291dc0005c1f70604647488921866ce020a1f042c2a0002108791f9a200655cc503d0385cc571832d2158002090003e47299224e84c2d99135c500dc0004dc0d000000201880d00803088160000204c15000180540004400014000000100c14000000040001848008341180d0000301c0a01801004000184e0000e0081c0001801c280ac0e0980403c040440702006020010080002019004070301300000000090000002c1800c0300c0108c0c0b40000c190080a02c0c030270c80a00026008010040200009018000084f0140200c000040700008014010a82d024010002001c0308c4a0000006432004000000204001000070480901457008000440d01401000140000101400000080100400001004050001600800004040000e0241006c0503c0600c0f010010280000c1f04009000000140202c030001201c010102f008040000202801bf296877d52d0efca3a1fd94743bb28e877d51d0feaa3a1dd54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121fe94243bd284877d5090ff2a121de54243efa1a87b
  | 3 => 0x7e1671cc67c669af05e9dc000e11d84504a89a4c20350e1ab3f40604588436457c6404b4e80d80023514a1ccc28000000000000005c898f3102000428309fb0686953903c00000118266390131011b93fe994bc1d239e2a43493339417c3f81b0047c40002700031c00000000174001f9458000bd8c425079c608321ae959270000d00984e2421660003f16c4c069cf10003980004a2064b4264001a60003cc9609f2a65943a84f0342300000002c2f402005058888000000008d8000004564ec8d00000000000000000000000001ee358000000004747b00000094009a2e0007bd0008a03260536a461681985096b2687e00900b44e560f6042472000128e429810cefa2817624d2e21a0de37c00186000274ff0000000000023a3d0850950000c443446a200aa000c7000000000e883937a0006f0003e468c829be0003bcc8000000738db20b0000000000021c001361350000a4000003ca32c7d13a0003750f8241307d1259b71aa0008305846e
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd521034d5354840cbd0d521032d4354840da181521032d5290840a758c42103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374354440cd50d51103706054440da54a401023f65500409ed95401036952500409d98654cc2756195330c798e54cc3366195330cd58654cc31e5450f309b988548c26d62152309d984548c27561152309d986528c2756194a30ba588408c2f16110230ae993308c27661951309d586544c26f62551309b189544c27761551309d185544c2da6090d3097195434c3564314530d550c514c37160145309e997404c37051d0130b698c404c3994310130ba588404c2f16110130dc144404c2ba64cc1309e983540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c3097d95300c27b654c0309d98754c827561d53209798c54c825d63153209d98454c827561153209d98753c827561d4f208f99053c823d6414f209d98453c82756114f20ba18142c837251d0320ba58840c83aa4210320dc94440c825e63152209758c548827661152209d584548827661d4e209d587538823e6494e208f59253882f0614c220bc987208823e64951209ed81544825e63151209758c544827661151209d584544823e6515120c798c544831d6315120cb58854483366115120cd584544833960151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb152424826c65509209e99640483385490120ea90a40482786550120ce1514048338548c1209e1953048338544c120ba18930482f0614c120ce15320482f261c81209798c540825d63150209b988540827661150209d584540827a60150209dd8553082746154c208f990530823d6414c209d98453082756114c209e980530827965d00209e59440082e962100209bd95200827b6548020ae191200826e62d53109b58b54c425e63953109758e54c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c42f06050710ba58840c42f16110310ae19120c436a52483109798c548425d63152109b988548426d62152109b98b538426d62d4e108f992538423d6494e109798f528425d63d4a10b958831842f1600c610b518d21843665248610bc185308425e63951109758e544427b60551108f992534423d6494d109dd85534427561949109e582524423f64549108f191524425f63549109718d524427465505109e195304425e63150109758c540426e62150109b588540427661150108f990530423d6414c109b988530426d6214c109e980530423e64148108f590520425e63148109758c5204275650c410d554c31042e5620c4109d59621042d463484109e59440043395410010ba58840042796588010ae191200427965840109dd95100427b6544010
  | 1 => 0xca7661953329d58654cca7761543329d18550cca7b60552329e181548ca7661152329d584548ca7a60152329e580548ca3f64542328f191508ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5c6550d32d590c514cb554314532d58c8514ca7661d50329d587540ca7a60d50329e583540ca3d65950328f990540ca5e63150329d984540ca7561150329e980540ca796015032c7553320ca5f654c832c7551320cad4614c8329bd95320cb365494432cd552510cb365454432cd551510cb663254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500ca7a6094f419e58253d075a6094f41d658253d071e5350f419e98252906796094a41b598f41906b661d0d41b598f415073b4314141ce50c505063f65504419dd95411067a60d53319e58354cc6f060507319ed81548c67860552319e982528c6796094a31a7590328c6d5610ca319758e544c67561951319bd89544c66c62551319ed81544c67860551319b98b540c66d62d50319e983540c67960d50318f596540c71e6395031cd986540c63e64150319b988540c66d62150319e980540c679601503197596430c71e5450c31cb952520c72d5494831cb951520c72d5454831d390d520c74d4354831d9185520c74d528c831a7590320c6756590431d954a410c7365450431e550d410c7655250431bc181410c765528c43197d95310c677654c431d9549310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c75a4354031d650d500c7724154031dc505500c67a60d53219e58354c865e63153219758c54c867a60153219e58054c867a60d4f219e58353c863e6414f218f59053c867a6014f219e58053c86e4614cb21b958831c87c6320c721dccc650c877031943219e983548867960d52219798e548865d63952218f990538863d6414e219e98053886796014e21bc18141886f260c86219798e544865d639512197d8d544865c63551219ed81544867860551219798e53486776154d218f990534863d6414d219e98053486796014d2197994534871e6414d21c7590534874d6214d21d5584534875a6014d21d6580534874c538c9219b195324875453905219d19541487545350521b918941486f060505219d9963148754538c521f18ca3148674654c521d514d314875453c8521bc983214867b60550219e181540865e63150219758c540867661150219e980540867960150218f990530863d6414c219b98853086766114c219e98053086796014c219d5973108675650c421b9588310866f65484219dd9521086d463484219dd8553902746154e409d98652902756194a40a758c42902b96010a40d6982531031e5350c40d394e521034d5394840d394
  | 2 => 0x108959825a9f6001ba2b142000002301a05000ab214001b07e18027b82e1a4e36a6e178347c800002c833020000007d00000000c2b9e98a10872be09800ca2d0d0a9c6c8000003a5303ea01ea32abc0038c449503dada0016c64bae6700003000000320037439348ae8006db4e00354000002aafc118d0d880000000c9000949d4721484292c86b6cad2c60000094106000008ab6e000001a88a0000000000d9800000006f800000006d1c0e99fe001ecd4b728105ce68000028200110512c49dacad1800003649182e0006696b3800000001620029800226da800001c257000ea00000156688007f26c3023a002f69024a00058c384ac2146b7a7e09092b8ab2a11382f9fa138f47724865b586207adc02a37000000006280047000d72aad7b04c893c38a0e291e082390379520b0e0790d63c36818b16b525e9f100e12422c844641986b378550b82404cad8a0910188e0506138e8912a4800e298807a094990540031acc178e88004d2ee59a1800132858028b92273a300008614860ce91e6aa884ebaabea3e668707403c560fe6b95e122f20018c56afe002741d082e2856c1a6a49a2c0200026800eb06edd80045a66be10e00388193b00286c16800d40b404ad2768007b81e058000039c001141d97c9a0bc8483622000a327adf0fac7a928d800cb0005eac00035a52b349800075830a9884321cc1a000778ae33800c625400160000004a200970788f0fccd8008c96eb5800650004faaed31b8c5000bb0a29c356259360a2b8a2b20de8eec0800c32a8b980023b44748c2bc12e000980029e678009c924c99a6d833e0020ce5ace78940cc8424c0000034a43000000004680053a8ec0104001760000040822bd1748298e00c010000500003000030200001c0700800000010040000c1a028020081100806000020100000000004000040004c0f00c0000001028020283c008010280301400008000080c000060041f02c0000402000000000806407004140000e014060100000c0800001034010080900000064140100200c180001001c00000040080000000014010140000004010050280000000008170580c05001004040040800801000020000501c000000c01c040000100402004050100a0000d010000d4060000100003012d661d0e43ced0e5090ed661d0d43ae9824350e7661149439d5845250e7a60149439e5805250e3f6550c4397d954310e7a6094f429e58253d0a7b60547429e18151d0a776154e429d1855390a5f63546429718d5190b3b4314142ce50c5050b3a4214142c754f4210a3f6550842c754d4210ab860508429bd954210b565394442d554e5110b565354442d554d5110b5a5394042d654e5010b725194042dc5465010b5a5354042d654d5010b725154042dc5455010b6a4254042da5095010a7a60d53329e58354c
  | 3 => 0x5c800b6000000e6a50400707c71220888ba87b2e001e60000068000000b6df9ca00000a90d801a96b0ae86f20200000000d23a2e4c7000a8800e480000072760a8001f0001a800286618008a278692dc461c68d258002e0b30f23e0000132ae534093164cf00081ba0a40c4e616800000000001f97e3509ca6800000003b2ea002b0a8380e90c65c0ea00038c4010c48002c0000000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1600714244a21540d0002c00000004c000000061b0000000140c04970006403c100900068470e306000040020021838654c6050842c2aa830a641970543549410c748a18c0a0863985486050431e2286a0aa018d61720c650c8706b22c429a43865916014d21c88a63128290e5053181414872332c6518a439414e60c8521d1286b10809869143584404c238bb0a220261c450c5110130cc2c428880986616294440c8306b1ac42a2418558d6115120c54cb21480906285418930483182a0c2982418c15261c8120c50c92924188644639492184322a9ac4188218a5516210010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x408e01435486050431c117650c5110130e01435885110130
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 624)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 53)*6) 6
  | 2 => packedAt s5K2 (182+((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1f8fff03c7c71c78fe383ffe38381c64f667
  | 1 => 0x1fe00f8ffc07ffe07f1fc0381fc03ffd98c87f
  | 2 => 0x1ffff00ffff807ff801fffc01fffc01e1f0f87
  | 3 => 0xe000000ffffff8ffffe000001fffffe3e00ff8
  | 4 => 0xfffffff0000000ffffffffffe0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc2c5150138888a0c18260889d60a8944245663
  | 1 => 0x444b221249930460291a43124a4112c898c82d
  | 2 => 0x8882032411019024800c91808c9180900d0a86
  | 3 => 0x1144c48a20402995240040511262503600550
  | 4 => 0x11180800c22624d26491262600040603d2a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80fefafc80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5005fe54017f55005fc5400ffd4c03fe5300ff54c03fc5300ffd0c03fe4300ff50c03fc4301ffd4807fe5201ff54807fc52017fd0805fe42017f50805fc4200ffcc803fe3200ff4c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41017f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84200fff5421007ff2a108013fc508401dffa042004ff90210077fa8108013fc4084013ff9842004ff8c21004ff46108027fd3084013fc9842004ff0c210007fe4108013fe2084001fe9042004ff08210007fe2108003f71084001fd884200dffd951006dfeca880037f65440013fb2a200dff9951001dfcca88037fd654401b7eb2a200dff1951001df8ca880377c65440073e32a200cffd9110065fec888033fe64440057f322200cff59110065fac888033fc64440057e322200cffd5110067fca888033fd5444019fe2a2200bffd8d1005dfec68802ffe63440037f31a200bff58d1005dfac68802ffc63440037e31a200bffd4d1005ffca68802ffd5344017fe29a200bffd0d1005ffc868802ffd4344017fe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e312200dffd491006ffca488037fd524401bfe292200cffd0910067fc8488033fd4244019fe212200bffcc91005ffc648802ffd3244017fe192200dffd451006ffca288037f6514401bfea8a200dfd5451006ff8a288033ff4144019ff20a200cfd90510067fa8288033f54144019fe20a200bffcc51005ffc628802ffd3144017fe18a2000ffc8510007fc4288003fd2144001fe10a200dffd411006ffca088037fa504401bfea82200dfe5411006ff8a088033ff4044019ff202200cff50110067f8808802fff3044017ff182200bfe8c11005ffa608802ff93044017fe1822000ffc8110007fc4088003fd2044001fe1022000ffc4110007f62088003fe1044001fb0822004ffd9410045feca08023fe65040077f3282008ff59410045faca08013fc65040077e3282004ffd901003dfec80801ffe64040057f3202007ff5901003dfac808013fc64040057e3202007ffd501003ffca80801ffd540400ffe2a02004ffd8c10035fec60801bfe63040037f3182006ff58c10035fac608013fc63040037e3182006ffd4c10037fca60801bfd530400dfe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810005fec408003fe62040017f3102000ff58810005fac408013fc62040017e3102008ffd4810047fca408023fd5204011fe2902007ffd081003ffc840801ffd420400ffe2102006ffcc810037fc640801bfd320400dfe190200abf98410047fea208017fe5104011fea882005ff1441003ffe8208017fe410400ffea082005ff10410037fe6208017fe310400dfe9882005ff0c410007fe4208017fe2104001fe9082005ff0841004dfcc008023ff5004009ff2802008ff54010027f8a00801fff4004009ff2002007ff50010027f8800801bff3004009ff1802006ff4c010027f86008003ff2004009ff1002000ff48010027f84008017ff1004001fb8802004ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xbfe520802bfea904012ff148200a7fe841004bfe4208029fea104012ff1082009ffe641004bfe3208027fe9904012ff0c820027fec210003fe61080017f3084000ff58420005fac210013fc610802bffa884015ff944200affaa210057fc5108029ffa084014ff904200a7fa8210053fc4108027ff9884013ff8c42009ffa621004ffc3108025ff9084000ff88420007fa421004bfc210802d7f3004015ffd4020027fca010057fd5008009fe2804014ffd0020027fc8010053fd4008009fe2004013ffcc020027fc601004ffd3008009fe1804012ffc8020007de4010013fe2008001fd1004000ff48020007da4010003f9200800bffb2e2011bfd971008ffccb8800efe65c4023feb2e2011bf5971002ff8cb8800efc65c400bffb262010bfd9310087fcc98800afe64c4021feb262010bf5931002ff8c98800afc64c4021ffaa62010ff95310087faa988043fc54c400bffb1e200abfd8f10057fcc788006fe63c4015feb1e200abf58f1002ff8c788006fc63c4015ffa9e200aff94f10057faa78802bfc53c4015ffa1e200aff90f10057fa878802bfc43c400bffb162000bfd8b10007fcc588002fe62c4001feb162000bf58b1002ff8c588002fc62c4023ffa962011ff94b1008ffaa588047fc52c4021ffa162010ff90b10087fa8588043fc42c4015ff996200aff8cb10057fa658802bfc32c4023ffa8e2005ff9471008feca388047fd51c4023faa8e2005ff14710087fe8388017fe41c4021fb20e2010ff50710087ea8388017fc41c4015ff98e2005ff8c710057fa6388017fc31c4001ff90e2005ff88710007fa4388017fc21c4023ffa862011ff9431008ffaa188047fc50c4021ffa062010ff90310087fa8188043fc40c4015ff986200aff8c310057fa618802bfc30c4001ff9062000ff88310007fa4188003fc20c4009ffb2c200fbfd961007ffccb0800efe658401ffeb2c200fbf59610027f8cb0800efc6584009ffb24200ebfd9210077fcc90800afe648401dfeb24200ebf59210027f8c90800afc648401dffaa4200eff95210077faa90803bfc5484009ffb1c2009bfd8e1004ffcc708006fe6384013feb1c2009bf58e10027f8c708006fc6384013ffa9c2009ff94e1004ffaa708027fc5384013ffa1c2009ff90e1004ffa8708027fc4384009ffb142000bfd8a10007fcc508002fe6284001feb142000bf58a10027f8c508002fc628401fffa94200fff94a1007ffaa50803ffc528401dffa14200eff90a10077fa850803bfc4284013ff9942009ff8ca1004ffa6508027fc32840177eb0c200fffd461007ffca30803ffd518401ffe28c200effd0610077fc830803bfd418401dfe20c2009ffcc61004ffc6308027fd3184013fe18c2000ffc8610007fc4308003fd2184001fe10c2006bf9821007ffea108013fe508401ffd2
  | 2 => 0x20027f8cb1000efc6588009ffb24401bbfd92200dffcc91000afe6488037feb24401bbf59220027f8c91000afc6488037ffaa4401bff952200dffaa91006ffc5488009ffb1c4016bfd8e200b7fcc710006fe638802dfeb1c4016bf58e20027f8c710006fc638802dffa9c4016ff94e200b7faa71005bfc538802dffa1c4016ff90e200b7fa871005bfc43880317eb14401cffd4a200e7fca510073fd5288039fe294401bffd0a200dffc851006ffd4288037fe2144016ffcca200b7fc651005bfd328802dfe1944004ffd8620007fcc310002fe6188001feb0c4000bf58620027f8c310073ff5188039ff28c401cff546200e7f8a31006fff4188037ff20c401bff506200dff8831005bff318802dff18c4016ff4c6200b7f86310003ff2188001ff10c4000ff48620007f8431004efe6088039ffa844004ff942200e7faa110013fc5088037ffa044004ff902200dff4811006ffd4088037fca044004ff102200b7fe6110013fe308802dfd1844016ff4c2200b7f26110013fc3088001ff9044000fbc8220007f6411006bff65480357fb2a401aff9952001dfcca9006bfd65480357eb2a401aff1952001df8ca90067ff64480337fb224000efd91200057ec890067fe64480057f3224019ff591200cdfac890067fc64480057e3224019ef1912001578c890067ff5448033ff2a24019ff551200cff8a890063ff63480317fb1a4018ff98d2000dfcc690063fd63480317eb1a4018ff18d2000df8c690063ff5348031ff29a4018ff54d200c7f8a690063ff4348031ff21a4018ff50d200c7f8869006bff5248035ff292401afb949200d7faa49006bed5248035fe2924019ffd09200cffc8490067ee4248033fea124019fb509200cff88490063ff3248031ff1924018ff4c9200c7f86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a401affd45200d7fca29006bfd5148035fe28a4019ffd05200cffc8290067fd4148033fe20a4018ffcc5200c7fc6290063fd3148031fe18a4000ffc8520007fc4290003fd2148001fe10a401affd41200d7fca09006bfd5048035fe2824019ffd01200cffc8090067fa4048033fea024019fe501200cff88090063ff3048031ff1824018fe8c1200c7fa6090063f93048031fe1824000ffc8120007f64090003fe2048001f71024004ffd94200adfeca10057fe65080077f3284015ff594200adfaca10013fc65080077e3284004ffd90200a5fec810053fe64080057f3204014ff590200a5fac810013fc64080057e3204014ffd50200a7fca810053fd5408029fe2a04004ffd8c2009dfec61004ffe63080037f3184013ff58c2009dfac610013fc63080037e3184013ffd4c2009ffca61004ffd5308027fe2984013ffd0c2009ffc861004ffd4308027fe2184017bf988200affea41004
  | 3 => 0xf1924224fb8c921127fa6490893ed3248449fe1924226ffd4521137fca29089bfd514844dfe28a4225ffd052112ffc8290897f6414844bfea0a4225fd5052112ff88290893ff3148449ff18a4224fd8c521127fa6290893f53148449fe18a4200ffc8521007ee4290803fe2148401f710a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c09089bff504844dff2824226ff54121137f8a090897ff404844bff2024225ff5012112ff88090893ff3048449ff1824224ff4c121127f86090817ff65084437fb284221ff9942101dfcca10887fd65084437eb284205ff1942101df8ca10817ff64084417fb204220ff99021015fcc810883fd64084417eb204205ff19021015f8c810883ff5408441ff2a04220ff55021107f8a810817ff630843f7fb18421fff98c2100dfcc61087ffd630843f7eb184205ff18c2100df8c61087fff530843fff298421fff54c210fff8a61087fff430843fff218421fff50c210fff8861088efe6208443ffa904212ff9482110ffaa41084bfc5208441ffa104212ff90821107fa841084bfc420843fff9904212ff8c8210fffa641084bfc32084457f3084221ffd442102ffca210887fd510840bfe2884220ffd042102ffc8210883fd410840bfe208421fffcc42102ffc621087ffd310840bfe1884212ffc8421007de4210817fe2108401fb1084200ff48421007da4210803f5210840bffb004200ff98021005fcc010803fd60084017eb004205ff1802110ffea010887fe5008443fea804221ff14021107fe8010883fe4008441fea004220ff100210fffe601087ffe300843ffe980421fff0c021097fecb9007aff65c803dff32e4003bf997200f7facb9007afd65c8025fe32e4003bf19720097fec990076ff64c803bff3264002bf993200effac990076fd64c8025fe3264002bf193200effea990077fe54c803bfeaa6401dff15320097fec79005eff63c802fff31e4001bf98f200bffac79005efd63c8025fe31e4001bf18f200bffea79005ffe53c802ffea9e4017ff14f200bffe879005ffe43c802ffea1e4017ff10f200f7fea59004bfe52c803df7296401eff54b200f7daa59004bfc52c803bffa164012ff90b200efdc8590077fd42c803bf6a164012ff10b200bffe659004bfe32c802ffe9964012ff0cb20097fec390003fe61c80017f30e4000ff58720005fac39004bfc61c803dffa8e401eff947200f7faa39007bfc51c803bffa0e401dff907200effa8390077fc41c802fff98e4017ff8c7200bffa639005ffc31c8025ff90e4000ff88720007fa439004bfc21c803dffa86401eff943200f7faa19007bfc50c803bffa06401dff903200effa8190077fc40c802fff9864017ff8c3200bffa619005ffc30c8009ffb2c401cbfd96200e7fccb1000efe6588039feb2c401cbf596
  | 4 => 0x800000825ffb2e422abfd9721157fccb9080efe65c8455feb2e422abf59721097f8cb9080efc65c8425ffb264229bfd932114ffcc99080afe64c8453feb264229bf59321097f8c99080afc64c8453ffaa64229ff9532114ffaa9908a7fc54c8425ffb1e4223bfd8f2111ffcc790806fe63c8447feb1e4223bf58f21097f8c790806fc63c8447ffa9e4223ff94f2111ffaa79088ffc53c8447ffa1e4223ff90f2111ffa879088ffc43c8455ffa964212ff94b21157dca5908abfd52c8455f6a964212ff14b2114ffe859084bfe42c8453fea164212ff10b2111ffe659084bfe32c8447f71964223ff4cb2111fda659084bfc32c8455ffa8e422aff94721157faa3908abfc51c8453ffa0e4229ff9072114ffa83908a7fc41c8447ff98e4223ff8c72111ffa639088ffc31c8425ffb064200ff98321005fcc190803fd60c84017eb064212ff18321157fea1908abfe50c8455fea86422aff1432114ffe81908a7fe40c8453fea064229ff1032111ffe619088ffe30c8447fe9864223ff0c32102ffecb108a2ff6588451ff32c4203bf99621147facb108a2fd658840bfe32c4203bf1962102ffec91089eff648844fff3244202bf9922113ffac91089efd648840bfe3244202bf1922113ffea91089ffe548844ffeaa44227ff1522102ffec71088aff6388445ff31c4201bf98e21117fac71088afd638840bfe31c4201bf18e21117fea71088bfe5388445fea9c4222ff14e21117fe871088bfe4388445fea1c4222ff10e21125fac5108a3ff5288451ff2944228ff54a21147f8a51089fff428844fff2144227ff50a2113ff8851088bff3288445ff1944222ff4ca21117f8651087efe6188451ffa8c4205ff94621147faa310817fc518844fffa0c4205ff9062113fec831089ffd418844ffaa0c4205ff10621117fe6310817fe3188445fb18c4222ff4c621117ea6310817fc3188401ff90c4200fbc8621007ee4310817ff6088401ff3044200bf98221007fac110802fd608840bfe3044228ffd4221147fca1108a3fd5088451fe2844227ffd022113ffc811089ffd408844ffe2044222ffcc221117fc611088bfd3088445fe1844226ffd9521135feca9089bfe65484077f32a4226ff59521135faca9089bfc65484077e32a4225ffd912112dfec890897fe64484057f3224225ff5912112dfac890897fc64484057e3224225ffd512112ffca890897fd544844bfe2a24224ffd8d21125fec690803df63484016fb1a4224ff98d2100dfcc690893fd63484497eb1a4224ff18d2100df8c690893dc63484036e31a4224ffd4d21127fca690893fd5348449fe29a4224ffd0d21127fc8690893fd4348449fe21a4226ffd4921137fca49089bee524844dfea924226fb54921137f8a490897ff424844bff2124225ff5092112ff88490893ff3248449f
  | 5 => 0x700019a0001571e00b580007ea1980005382d17388880000021080022805f0000cd19192d9ec8000000000000001a41af92196ca1c9b404520a05b1c98410a297b9da0069029b11491539f72069dea0fa0f20381c893823a1f18394305e0760000d58002211cf9f68000000da82910d00000009707501e0778ee8001299d68001090731a69cf08c82117a0c61a10368351f980009d00000008d8698000878001038b687e15086380021e12587f0d917300000f1d71c30ea80000d2170ff0c51000be88c1660589b285302693614b9a91018720090fd16f85622718f8d682e0148a993b1ba00008b91700019986f9af00021316c1f003f8d88ea2031e180011d82a0e210c9149ca83d8001ef0008968bb0001e206b0390d39349b89130a80dc04683a0f41b9213a0c12002506b8960fc01e8af1c49a211694f0261d988f0c20000da1769ee8601c09a38f019e00212b0fa1971160850b0a288b48820178b791782ba040d991b8631a09630a78e89551230509fa8d516f1f48740f59cd8311f50a50ec1db8b518e0710f6a070000088840ab00014b09112b9c71bd2219778749f100018220d2009f30180a90fb11a13400403881400001100005d0ec9fb9bc88e18d9e286f0578dd9a8a1884988386220e8a88001fd1df8bc80980000010f80013918b0000e49b58fe20604a031a1ea1590e8331910000429610001760fe9e10812091f08c38cf80012280000000702800801012000010018060000040080200601400000002064020010180200000301a0d005800000000008090000700100600805c0100000002c0080600400c01802004000000030300000200100005803003000038050040020000283300a0100d8030000080180102c000018000140140480a0000000080001c0140000402800401802000000010050080000181800c070048040380280000101a0001a0030060100480600800c050020020040002600403c07002012034008230260082001301a060000030b200c00005000048000030200080680101c01c03807000010018010000000001301c0200000400a0280c02e056004040010020000f8020000540100000600c0500200200003004002004018050000640100000c004030070ae0d40380400a008010140020040380c00200801000012000048000060200080602e0bc0000501c0040800d0140100480002000003004000024000000040340080a000044030410080000100600201800019006000000030120380000500e0142400c00003c0000100c0000000f02e0a4000000000040780600000c04813006018020000120ac0986b0100000f80003a0280d00900a0640000a04000c008000020180000301600c03000004000078000040d80280b000058010000000000500104a0000100700008c000000300000c00b00e0080
  | 6 => 0x97c9d51840a10001809c58000880000ae15486c1569711350e180c10d95e8c31a59959a49dc9248b189c172a1107c83486484d8001e506694600012112d00007592a80002f9e69ef86d00018812600014580000015100019b09301703c90999494780021a8000bf2101889a28001ff20d9e09df1d115194d0f799f85481c0c10490570b406084e9de14200502315897f10a12704f8c7a141940691bc08d1c78000158ff9d38000000000a58a180002b21200491f8871129ba9ae16a0000768f89721559d916900012c0340e119307800008490317993f0001748002119590c5800047954000198a2392f00000002214a81503399693e00014700012f87f872a260d00128980001f90f39688189658000ce00000005c0000ca0e680012a1d60002168d805404713d9c4016a0c9b990090200010f0e61f58001ec00004a8b39b71ae9bd8700449f392791986e00000010c0160002079d18002250f18000fc97b16b01b00000004d0a00000000000489e39bb9c88028de8bd1ed94a0b914009e08f99600000000007899a89a9fd9bb1791741cd0000480000660a700018508291500011e0000000ee06a80000001a0f90e420e00000020b9501d4800000209a2080017880000007d9ab800000091a089d283b0000e31878c98db00019b97da1b18d0000000b11f42160000000001c01fa1629180db8c40658301c612397008e84c1251db0d20f500011c000011a2014ca268ad90b96a82e8d605e96e99f0aa0c0a1f8ca9832059b60131ea0459ac8108001b484e20200002808a8a300013f88180e85a92206815813389a0ef1759939529118430001561fb02c92e8198c72029b78419048aa85d8958709781e89601ce8e01cc04f0001b185a0001c812c9cb83f18280d94506102785512889b0000d30000d49bf93683c2259d421905009280b02704b83614c0f297d17e1900909eb9e807b9981b0059a0a9f18fa8eb1908591680cf0d78289e58079fe03e218067941989a0816e0001cb00020b1dd1ab00009787a05581d80013d00811b037a1c0c491f06715d0d70000a6a051e9a178a40000001a78b28dc944a1496498c8cb0000001088441a81281e91751641fc1520000380001f2a1b80002d82080f8f21f809f0000000e586514e80c81f87988680117a87b00013999515a19e80005f93a01007711d15e21a1068299d20e903d1c287d18a9c198c1530f11141309b30890258c805284000a9c68018001441ed01f0bb92902489b85180b95d9191b38000000629858409869208001c90948000ed1410ed91107a94f9be1060c00ad1aa8000e38c29848af83b9499011c100005c90a851143a010f614e1d30951ac1699041e482f15c95b0619240218e28000988001e310780000017e86e8e50808001979dc1e61669ff9330ab80013193c8c69f793e9c390
  | 7 => 0xe80000240000001d59a998f01d0399dda278d29378860b88061e70f988a16b80010b0b610e0d18200ac98e9ca0ae8d41a622416081211a813a221800be1d0a1d1fe8dd11ea048001d000015b8569770000000000001a19488359650001da8f71371408000439b691099d80e06889206a1b80521321bf1269c209002296204613a81b8a3a1509f8000ce8de1f60000e79929d80000cc1e78a616d8a22019619fc9810e71f89389b08000bf8ba86403e9b200000002a8c18cc91200a13818180000000000000010518a1138858c88000000000ac00011880005b9ad9860000000f491c8000c900000009e9578e99481ee0000f31a51a01ad1aa03a8ba18b87390818919d16780389c80007180702c13c0b98b700008b00006c9639871c50000b006d95f0791100001058000f820004c9920191598e095a8fd8d09d78371ea8990cd96d1310df8328940a499c935a1d8308bc1f21a70d115c01a9cc9158ef8001be8998f08831e41eb2230df1ce0000fb80317f99922484b0cb99c2228000eb80000017180015f80000014d9429468899a31329670800001d889d8b30b817c05813000012e0002128000bd93b8a080587c0000000321b50b2042000000170
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x15084110027f23084110197f13084110024ff75d881001cfe75d8810004fd75d8810024fc75d8810024ff74d8810014fe74d8810004fd74d8810024fc74d8810024ff73d881000cfe73d8810004fd73d8810024fc73d881002cfe71d8810026f671d8810024fe70d8810026fa70d8810004fd7698810026ef6298810094ff759881001cfe7598810004fd7598810094fc7598810094ff7498810014fe7498810004fd7498810094fc7498810094ff739881000cfe7398810004fd7398810094fc7398810024fe7298810096ee5298810006ed5298810096ee4298810006ed4298810096ee3298810006ed329881002cfe719881002cfc719881002eee219881002eec2198810024fe7098810024fc7098810026ee2098810026ec2098810026ec6258810004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc7358810024ff7258810026ef7258810006ee5258810006ed5258810006ee4258810006ed4258810006ee3258810006ed3258810094ff715881002cfe7158810124fd715881002cfc715881002eee215881002eec2158810094ff7058810024fe70588100c4fd7058810024fc7058810026ee2058810026ec2058810024ff751881001cfe75188100267e751881001c7e7518810004fd75188100267d75188100047d7518810024fc7518810024ff7418810014fe7418810026be7418810014be7418810004fd7418810026bd7418810004bd7418810024fc7418810024ff731881000cfe7318810026de731881000cde7318810004fd7318810026dd7318810004dd7318810024fc7318810094fe7218810026ee721881002cfe7118810026f67118810024fe7018810026fa7018810004fd76c8410004ff7648410005df7348410035dc7348410004fd76c8010004ff7648010005bf744801003dbc744801002ef576c4010026f765c401018ef565c4010026f764c4010186f564c4010025f570c4010026f660c4010025f97684010026f9768401000cf97684010026fb658401017ef96584010026fb6384010176f9638401002df9718401002efa6184010027f26184010004ff76440100057f75440100457c7544010025f77644010006f77644010004f7764401000777754401015f747544010026f7654401015ef56544010026f7644401016ef56444010025f77044010026f66044010027f2504401015ff15044010027f22044010007f1204401002dfb7644010006fb7644010004fb76440100077b754401015f78754401002efb654401015ef9654401002efb6344010166f96344010025fb7144010027f3714401002efa614401002ff2614401002ff2514401015ff1514401002ff22144010007f12144010
  | 1 => 0x891000cfe73d8910004fd73d891000cfc73d8910006f641d8910006f541d8910006fa30d8910006f930d891006d7e75989100057d75989100067f65989100067c6598910006ef6298910094ff759891001cfe75989100967e759891001c7e7598910004fd75989100967d75989100047d7598910094fc7598910094ff7498910014fe7498910004fd7498910094fc7498910094ff739891000cfe7398910004fd7398910094fc7398910094fe7298910096ee5298910006ed5298910004fd7198910096f57198910004fd7098910096f970989100057f755891006d7c75589100067f65589100067c6558910005bf7458910065bc7458910005df735891005ddc7358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc7358910006ef7258910006ee5258910006ed5258910004ff7158910006f77158910006f64158910006f54158910004ff7058910006fb7058910006fa3058910006f93058910004fe76189100067f65189100067c6518910006ed6218910094ff751891001cfe7518910004fd7518910094fc7518910094ff7418910014fe7418910004fd7418910094fc7418910094ff731891000cfe7318910004fd7318910094fc7318910096ee721891002cfe711891002cfc7118910024fe7018910024fc7018910004fe76c85100067f65c85101567c65c8510006ef62c8510096ec62c8510005fa70c8510005f970c8510004fe76885100067f65885101467c6588510004fc76485100067f65485101367c6548510005df734851005ddc7348510006ef6248510006ec6248510005fb7048510005f87048510004fe76085100067f650851010e7c6508510007e52108510004fe76c81100067f65c81100f67c65c8110006ef62c8110096ec62c8110005f671c8110005f571c8110004fe76881100067f65881100e67c6588110094ff7648110004fd7648110004fc76481100067f65481100d67c6548110005bf7448110065bc7448110006ef6248110006ec6248110005f77148110005f47148110004fe76081100067f65081100ae7c6508110007e920081100067f65c411008e7c65c411002dfb75c41101cdf975c41100077b65c41101bf7865c411002dfb73c41101c5f973c411002ff251c41101bff151c411002ff241c41101b7f141c41100067f658411007e7c658411005df67684110025f775841101adf5758411000777658411019f746584110025f774841101a5f57484110007f36084110027f2508411019ff
  | 2 => 0x24fc73d8a10026f571d8a10026fa70d8a10026fa30d8a10006f930d8a10004fd7698a10026ef6298a10094ff7598a1001cfe7598a10004fd7598a10094fc7598a10094ff7498a10014fe7498a10004fd7498a10094fc7498a10094ff7398a1000cfe7398a10004fd7398a10094fc7398a10096ee5298a10006ed5298a10096ee4298a10006ed4298a10006ef3298a10096ec3298a10026ee2098a10026ec2098a10026ec6258a10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a10026ef7258a10006ee5258a10006ed5258a10006ee4258a10006ed4258a10006ef3258a10006ec3258a10006fa3058a10006f93058a10026ee2058a10026ec2058a10024ff7518a1001cfe7518a10004fd7518a10024fc7518a10024ff7418a10014fe7418a10004fd7418a10024fc7418a10024ff7318a1000cfe7318a10004fd7318a10024fc7318a10094fe7218a10026ee7218a10026f57118a10026fa7018a10096ee62c8610006ed62c8610025fa70c8610005f970c8610005df734861004ddc7348610006ee6248610006ed6248610005fb7048610025f87048610005bf7448210075bc7448210027e82048210025f576c4210006f576c4210026f765c42101eef565c4210026f764c42101e6f564c4210005f976c421002ef976c421002dfb75c42101ddf975c421002dfb73c42101d5f973c421006d7e76d951006e7e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100067f63d95100067e63d95100067d63d95100067c63d95100077771d951006f7471d95100077641d95100077541d95100077b70d951006f7870d95100077a30d95100077930d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951006e7e71d951006e7d71d951006e7c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f70d951006e7e70d951006e7d70d951006e7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d951006e7d10d95100067f65d89100067c65d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d8910004ff73d
  | 3 => 0xc7358420006f65158420006f55158420006f64158420006f54158420006f63158420006f53158420096f72158420096f42158420026f61058420026f41058420004fd7688420004ff7648420005df734842009ddc7348420026ef65c8020226ed65c8020026ef64c802021eed64c8020025ed70c8020026ee60c8020026fb6488020216f96488020026fb638802020ef96388020095f97288020096fa6288020027ea6288020004ff7648020005bf74480200a5bc7448020025ef7648020006ef7648020004ef7648020026ef6548020206ed6548020007af74480201f7ac7448020026ef64480201f6ed6448020025ef7048020026ee6048020027ea40480201f7e94048020095fb7648020006fb7648020004fb7648020007bb74480201f7b87448020096fb64480201f6f96448020096fb63480201fef96348020025fb7248020027eb7248020096fa6248020097ea6248020097ea42480201f7e94248020097eb2148020007e9214802002cff75d8b1001cfe75d8b10004fd75d8b1002cfc75d8b1002cff74d8b10014fe74d8b1002ebe74d8b10014be74d8b10004fd74d8b1002ebd74d8b10004bd74d8b1002cfc74d8b1002cff73d8b1000cfe73d8b10004fd73d8b1002cfc73d8b1002ef671d8b1002ef641d8b10006f541d8b1002ef970d8b10004fd7698b1002eef6298b10094ff7598b1001cfe7598b10004fd7598b10094fc7598b10094ff7498b10014fe7498b10004fd7498b10094fc7498b10094ff7398b1000cfe7398b10004fd7398b10094fc7398b10096ee5298b10006ed5298b10006ef4298b10096ec4298b10096ee3298b10006ed3298b1002eee2198b1002eec2198b1002eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b1002eef7258b10006ee5258b10006ed5258b10006ef4258b10006ec4258b10006ee3258b10006ed3258b10006f64158b10006f54158b1002eee2158b1002eec2158b1002cff7518b1001cfe7518b10004fd7518b1002cfc7518b1002cff7418b10014fe7418b10004fd7418b1002cfc7418b1002cff7318b1000cfe7318b10004fd7318b1002cfc7318b10094fe7218b1002eee7218b1002ef67118b1002ef97018b10005df7348710055dc734871002fe42148710096ee62c8310006ed62c831002df671c8310005f571c8310005bf7448310085bc7448310006ee6248310006ed6248310005f7714831002df47148310024ff75d8a1001cfe75d8a10004fd75d8a10024fc75d8a10024ff74d8a10014fe74d8a10004fd74d8a10024fc74d8a10024ff73d8a1000cfe73d8a10026de73d8a1000cde73d8a10004fd73d8a10026dd73d8a10004dd73d8a10
  | 4 => 0x9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120006bf72d91200cebe72d91200cebd72d91200cebc72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf32d9120006be32d9120006bd32d9120006bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006be31d9120006bd31d9120006bc31d9120006bf70d91200cebe70d91200cebd70d91200cebc70d9120006bf50d9120006be50d9120006bd50d9120006bc50d9120006bf30d9120006be30d9120006bd30d9120006bc30d91200cebd20d9120006bf64d8520006bc64d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d8520006ee52d8520006ed52d8520006fa30d8520006f930d85200cdbe7498520005bd7498520006bf6498520006bc6498520006f761985200057f75585200d57c7558520005bf74585200cdbc7458520006bf6458520006bc6458520005df73585200c5dc7358520006bf6418520006bc6418520006f5611852002cff751852001cfe7518520004fd751852002cfc751852002cff7418520014fe7418520004fd741852002cfc741852002cff731852000cfe7318520004fd731852002cfc7318520004fe76c8520006bf64c852014ebc64c8520006bf648852013ebc6488520006f7618852002ef46188520005fa7088520005f97088520006bf644852012ebc6448520005df73485200c5dc7348520006f76148520006f46148520005fb7048520005f87048520004fe7608520006bf6408520106bc6408520007e52108520006bf64c81200eebc64c8120095fb74c8120265f974c8120007bb64c812024fb864c8120095fb73c812025df973c8120097ea52c8120257e952c8120097ea42c812024fe942c8120006bf64881200debc6488120025ef7588120245ed7588120025ef748812023ded7488120007af6488120237ac6488120007eb6088120027ea4088120237e94088120027ea308812022fe93088120026f7619842002cff759842001cfe7598420004fd759842002cfc759842002cff7498420014fe7498420004fd749842002cfc749842002cff739842000cfe7398420004fd739842002cfc739842002ef65198420006f5519842002ef64198420006f5419842002ef63198420006f53198420096f7219842002ef42198420026f61098420026f41098420026f46158420004ff755842001cfe7558420004fd755842001cfc7558420004ff7458420014fe7458420004fd7458420014fc7458420004ff735842000cfe7358420004fd735842000cf
  | 5 => 0x26fa5098021006f95098021026fa4098021006f94098021026fa3098021006f93098021096fb2098021026f8209802102efb1098021026f8109802102ef86058021004ff755802101cfe7558021004fd755802101cfc7558021004ff7458021014fe7458021004fd7458021014fc7458021004ff735802100cfe7358021004fd735802100cfc7358021006fa5058021006f95058021006fa4058021006f94058021006fa3058021006f93058021096fb2058021096f8205802102efb105802102ef81058021096f7619872002cff759872001cfe7598720004fd759872002cfc759872002cff7498720014fe7498720004fd749872002cfc749872002cff739872000cfe7398720004fd739872002cfc7398720006f7519872002ef4519872002ef64198720006f5419872002ef63198720006f53198720096f7219872002ef42198720096f46158720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc7358720006ee5258720006ed5258720006f75158720006f45158720006f64158720006f54158720006f63158720006f53158720096f72158720096f42158720005df73487200bddc7348720097e42148720026f7619862002cff759862001cfe7598620004fd759862002cfc759862002cff7498620014fe7498620004fd749862002cfc749862002cff739862000cfe7398620004fd739862002cfc739862002ef65198620006f5519862002ef64198620006f54198620006f7319862002ef43198620026f61098620026f41098620026f46158620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620014fe7458620004fd7458620014fc7458620004ff735862000cfe7358620004fd735862000cfc7358620006f65158620006f55158620006f64158620006f54158620006f73158620006f43158620006fa3058620006f93058620026f61058620026f4105862002ef66188620006f56188620025fa7088620005f97088620005df73486200b5dc7348620006f66148620006f56148620005fb7048620025f87048620025ed76c8220006ed76c8220026ef65c8220286ed65c8220026ef64c822027eed64c8220005f976c8220096f976c8220095fb74c8220275f974c8220095fb73c822026df973c82200cdbe76d91200cebe76d9120014be76d9120006bf65d9120006be65d9120006bd65d9120006bc65d9120006bf63d9120006be63d9120006bd63d9120006bc63d9120007af72d91200cfac72d9120007ae52d9120007ad52d9120007bb70d91200cfb870d9120007ba30d9120007b930d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d
  | 6 => 0xd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21006df72d8d21126de72d8d21126dd72d8d21126dc72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df42d8d21006de42d8d21006dd42d8d21006dc42d8d21006df71d8d21126de71d8d21126dd71d8d21126dc71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df41d8d21006de41d8d21006dd41d8d21006dc41d8d21126dd21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21006df63c852111edc63c8521095f774c85212fdf574c8521095f773c85212f5f573c8521007d763c85212e7d463c8521097e652c85212efe552c8521097e632c85212e7e532c8521006df6388521116dc638852102def75885212dded758852102def73885212d5ed7388521007cf63885212c7cc6388521007e7618852102fe641885212cfe5418852102fe631885212c7e53188521006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d8121006ee52d8121006ed52d8121006f641d8121006f541d8121125de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211357c7558121005bf745812112dbc7458121005df7358121125dc7358121006df6358121006dc6358121006df6318121006dc6318121006f96018121024ff751812101cfe7518121004fd7518121024fc7518121024ff7418121014fe7418121004fd7418121024fc7418121024ff731812100cfe7318121004fd7318121024fc731812102eef65c84212beed65c842102eef63c84212b6ed63c842102ded71c842102eee61c842102ef764884212aef5648842102ef763884212a6f56388421095f57288421096f6628842102fe66288421004ff7648421005df73484210fddc734842102def7648421006ef7648421004ef764842102eef654842129eed6548421007cf734842128fcc734842102eef634842128eed634842102def714842102eee614842102fe6314842128fe53148421095f77648421006f77648421004f77648421096f76448421296f56448421007d7734842128fd47348421096f7634842128ef5634842102df7724842102fe77248421096f66248421097e66248421097e6324842128fe5324842102efb6098021024ff759802101cfe7598021004fd7598021024fc7598021024ff7498021014fe7498021004fd7498021024fc7498021024ff739802100cfe7398021004fd7398021024fc7398021
  | 7 => 0x100200000f00400500100000200000200100100001300600000100000200000300000100000400100200100100000200000000000000a00100300700000000000000000400100100000100100000000200300000700800000100700000700000000000600200100000300000100100200400200400101200000000e00400200000000300000200200100000100c00400300100000000000000600500a00000000000200000000000200400000000000a00100200000000900000200000700100000100400300000000000b00000000000b00300500000000300d00000000800600000000000700600200200000400001100100000400400300200200000200000700100000e002000001000000000096fb6098321024ff759832101cfe7598321004fd7598321024fc7598321024ff7498321014fe7498321004fd7498321024fc7498321024ff739832100cfe7398321004fd7398321024fc7398321006fb5098321026f85098321026fa4098321006f94098321026fa3098321006f93098321096fb2098321026f82098321096f86058321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321004fd7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc7358321006ee5258321006ed5258321006fb5058321006f85058321006fa4058321006f94058321006fa3058321006f93058321096fb2058321096f8205832102ded76c8621006ed76c862102eef65c862131eed65c862102eef63c8621316ed63c8621005f576c8621096f576c8621095f774c862130df574c8621095f773c8621305f573c862102efb6098221024ff759822101cfe7598221004fd7598221024fc7598221024ff7498221014fe7498221004fd7498221024fc7498221024ff739822100cfe7398221004fd7398221024fc7398221026fa5098221006f95098221006fb4098221026f84098221026fa3098221006f9309822102efb1098221026f8109822102ef86058221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221004fd7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc7358221006f64158221006f54158221006fa5058221006f95058221006fb4058221006f84058221006fa3058221006f9305822102efb105822102ef81058221125de76d8d21126de76d8d2100cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d21007cf72d8d21127cc72d8d21007ce52d8d21007cd52d8d21007d771d8d21127d471d8d21007d641d8d21007d541d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006d
  | 8 => 0x4fc0008d47800006b637e0009da0000000000001820000000fc0000000000ee00000000035c00000000009800000000027e00000090400000000000000000028000000093c000a2200088e89000062062e01a7060002bc000096a369f89469126109566340004380000000000008fa0005e695c0000000000001b00000000005a091a6124160003705b87fe0007d600000070e00095868c0000d20000000000001762fe3dc4800002540003aa39800096a6d833ea2a3ee51e04c00000000085400000061800076a3a24b64e008072000000066063a0000000009926767ce0000000000000360000000000003448700000000000000002c04923d41480ba00085c00040600000000003c8327480002840000000000000000003c60000000005024080000000000ae4249b692821c6fe7a836684699a0000e607e64400000017871e46699e4ae7d800013a0000000005fa7fa0001ec7e475081c5060e44aa62a79812600000000000004e9420ac51404203e00008a422788000a049183f460e1382cc3e29d25963b66c000000076600012c81a9ae0004460003222e839c0e82e400026200013c5ee1da00066c7d200059c0007e80a40005f400058a88c4c800000000000000073635080e42694e63000008e99457840022470a96e0000000000f41326f419200000000000036a5520007745c000000010240200000023c36e00073e000000000a3400076000000000000039e00008c3185c276496643c00000031a00015800000000000079455000000003a32875a0001d026c0000002368524ce9600008800004840000000001809ca3909680000003120000000000008504b437c00065a0002120000284860004c03320000001300000009ba00033000200000000000300900000200300100000000000600200300300500000000000000400000000000200000500b00200500100200100400300100000000100500100700000000000000200000100000000a00000100700300000200300000400000100000200100400000100100200001100300000200000000000300000400000000100000800000100000000400200000100200000000000800000500100100000900000100500100100200700100000000000900000100000100000100000200000600000000000000100400001b00000100100600200400000100000300000400100600800100200100500200000000100000e00600e00200700000000000800100000d00300000000b00300000000100000500700000000000100300100000100100100700600100100400100200100100600000100300500400000300000200000000000200000100800500600000200100100d00600900a00100e00800000001200200200000300000400200000e00100600100500000200300f00000100900800
  | 9 => 0x520000003da8a05889220345de7122dc4ca08282a79a00081019600000058256499815e4903a40f80000000006b26e07b8a2800000080600046e01498a34a5624960d45ba0000000000000002cea1e0000000006d48ec00022840479200011a000a460fa0001084fa1864644f069c5602f26ec00075650c00000032e8a80006ae0008f883427600000000000046a4e24ec2e206a4d009024200000000010600016a5807bea068181ea00000000000033835e4740000003d67ca00000061a000000000000000000066a3a59400081e00000048a0c03ce0000001ba000772000000000000a48184000000210a0a8fe87c00000043a2465668de00057e0007380007fc91e0000000001ee25a04a71c0000007025be77800083c95e4e645a0005087ea00000012e11600000059a8200008be0000000005a40000000000008940000b60002488a600045e6984781a437625c00019c0007b2000000a184fe0000000005ec0000003560000000000000000007a026868e9e28028ea0ce2c22560000004202f60000000003de0003800000220000003087da988a200001cc202156a440000003cc4420cc7240004c63068d000000076801637a8e81662a29c82f42080000005fe0aa0005540000000000a000000000022c7706aa87e4bc61e65822a2aa7c691000000000000000000000000000036c000a40000a380004ba72a0000006fa4f41bc00052e2be7e07bc00000033c60453a5d80008b000000000044000000000000023e0580006844cc5f650e66a0006680001b29f200000011027489e1f60000001b435a00000000000015c71686e36200079635228e000084000000a3e0008fc0006e200018e00000020079e0000002c80000003b800000000000000039a0000009f400000000000038c63c0000000000e25d039216e6be7b651022e0004ee11252a0000000000000380000000007f600000084253c00000047e5480000009d800000069e0009b49e48b858c09a2da1000008ac05456e9ea94098c32a49c6ee47064816826400080c17e8921d802624a77c0009cc0bc17a0003bea3c6ea9a64985b27dc9f000056a27c00000057a5560000000000000005d40000000001b800000000090800009e66416473a8580007f000000000000000099072c2ea0002fa5bc00039497e51240e0004545422d40005e20d61900008ee87412400000096207c09c0000000000000da000000654a1a00000090c00000060a9a01a24da85aa2e14a67210c3e089c6805445a83f641853809267400000000000088a0007449a881217c6520000000000000000000004ea0000009760003d895a6460000008b600000000000000000000000000000000062c8380009b81ca0005aa0c20007425ca9fea168400008d67ba2980000001d200029e60c000000000000782000000
  | 10 => 0x8c01be5d24ac00000000097200000000000000000014c0000003165348d88281a87d43840002ee0000000004c24f245c5848f03d0a260005000ea0120002700000003400000004b87e6000000302000000a2400000020e0000000000006400006c89ee6da9de0f091611e5a6a0c67c67e0005b421a00000064200000074a86653633a0063603100007220e08a4000324000656622000222a0e93a6a49d465059000e6080002a000068a0000001c26a059e0000000000003821aa29600076e00007600018c5e40042781c66320000007840000000007ec0007541ce0000001fa0000006880000000000005587f80000000000003e600053e3ae1987900000000000000002b41e082e47200030e0007083a00005220880f60000000000b82322e600031e00000000000000007055a0004e847c0021ac00000000000063e4940003fa7140003f0a323ea9000008160520088267a607805656879c5860865cc0003789bc64e0009740004d27c47003c200000088200054a00000083000000011400074000000007a4dc57646800016c00000000065c0000001e80004a00000000001d689a0006ba0620000000000000009782c60003200000000004d80000000008aa4884140003e40000000000000000000001fe000160000000000000000a120009543fc6e8a0800000000098222000000000018a00061466e00030a8a284c6064581228681e600089635431c95077695243e7f48c2000570000094a004e486c9e01540000000000b40000000002380000001883e89aa0000002b8000000000000598000a1c872000000a3051c2880004b26287345720c690e4f82ba72686000067a00000000048e32693841c69a6f23c42a80001429b202c0005ce0000000006921740006ce00034e4503ca00000014e0000000320000005e083a82c48c4623742580006020002180b027a67892a00000074e0000000000005f22262660000000000004d620c0000001c00000000000000000000003c000000000093000000000049e00026a0004600006de0000be0000008d207400000015a3b40000000007a429468290600025e44c52c0005dc0000000008ae5f08dc4300000000000640000008f60008b40000000000000000000006f00009341181c494a5d642878a86a10e34c2d60f25300ec1de7c029c8860009c49fc5a28c68c88043ba42e0003866c605c1f20001e286264c00000020a00000000000000000040a00076c0001040000000000000c400024c5c42d245200006c0000000000000000000002a63a69843ec00055c85e00025000000000059200054600a28c0000000000003340001520000fe8642340008369d654e11c6962ae1ae0000006d27ae0000000005183041f80000009a421400000000049a58e00000000090a00028200000000044870c0002
  | 11 => 0x7c89d00006b4a024de5ae0000000008bc0000460000009ce7a223a0180d83f24a220433600075e6fc05e00000084400085600000019492e2c401e0000000000000000003b09e600000024e0004c43b284892c38e3720000006f89be8e27460000004100009dc0000009866c22607aa0c82b05fc9a251a9ac50a5da0008ce80a13e7c200047a83e0001a05280000000002ac8846e61342ca0008cc1d44b084e0000200001f05240689267585c64829320007f200000021638891400000087600005a00093e0000000007b03464a60000000002d80000000ca8240001407ac00000000000000046c63600000092498e0000000006a26ac000000a4a0b2a4263800c0000000000000006c477e9802900000007627b400002e00000097ca4c8e064a8c400000000044e99c6262ec0406dc3482063ac00052096c3969c612a10a2b600047669461c80087a0008220000006bc4be9480008e60000000440000006d66ca01c00000000000000000000043273029297a61632c00000036865e29a0004360000003c86e400071000006e0005e800094c00057424400040c3000000609ec5402a40003f813600000002a02457c6a68140000006000009701dc6d000000000030c8da4120000000a887819a00054c662146808a4e0000000000008f27d02de0000000000009fa0000007520dc3420002e096477a9c045671a1a60000000004a80000009b01e421e8ca0009360a20a600000000078c56c1446a86cc0006b80000000005320000003580002400002d06f60001fc0000002b2000898718120000172a107de15073c00042a3fe00044a5b64a46700000000000d01b6000000000a140002fc5160000de0480001c86240000000003bc0000003a800000000000078e0000000000007cc1705b00304f67866660009443141f47ee2308ba5ac69001028a0000000005f841a27270412800088800000000000026e00052668674c9962863d22f07288b20006b0a2c5ea00038a8e400000000000007219e0000000003640009c275c42c8f40505c844490241e9f62f800000043400000091c0007e255e72e0009200009e884a7325044d400000000000016200000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xccc7358921840010fb0f326ca8800297a0e64d95100052ec1cc9b2a200087f8759365440010fb0f31eca880028fa1263d95100051ec24c7b2a200087f8758f654401b4ed0db8eca880369ea1b70d95100052f41ce9b2a2000a5d839d3654400187ae83a6ca881969da0474d95100053ac08e9b2a2000a3e849cf654400147b0939eca88003175cc73d95103253d400e7b2a2000a79801cf65440010fd0e21eca880021f61c43d95100051fc22e5b2a2000a3c845cb65440014bf06b96ca880029720d72d95100043f43885b2a200087d8710b65440014bd06216ca880029760c42d95100053b40885b2a2000a758110b65440014f500216ca880029e60042d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100053b40865b2a2000a75810cb65440014f500196ca880029e60032d951015d3d406e3b2a200087e87d0765440010fb0fa0eca8800297a0f41d95100052ec1e83b2a200087e870c7654401b0fb0e18eca880028fa1031d95100051ec2063b2a2000a6e820c765440014db0418eca880029ea0031d95100053cc0063b2a202ba7681dc365440010fd0e206ca880361f61c40d95100052f41881b2a2000a5d8310365440014dd04206ca880029b60840d95100053b40881b2a2000a758110365440010fd0f986ca880021f61f30d95100051f42661b2a2000a3d84cc3654400b1f301ba6c4880123d60773d891001e373aaa5312200387e86dd562440010fd0fb2ac4880030f1d365589100062e39ecab12200087e871956244001878e832ac488003171cc65589100061fb2ee8b122000c3c65dd162440018becbb9ac4880031719773589100045fc22eab1220028bc845d562440011bf06baac4880063720d75589100061fbaee8b122000c3c75dd162440010ff0aba2c48800e1f21574589100046fc1ae8b1220018dc835d1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100043fc2ae6b12200387c855cd624400117f08b9ac48800a2f21173589100062fba8e6b122000c5c751cd624400193ee839ac488003271d0735891001e363aca4b1220038ec875496244005968e920ac48800a3d21d415891000e6c39c60b1220018f8874c162440011df0eb10c4880031e19670c85100063c32ae190a2000c5c73d9521440018becbb9a42880031719773485100063a32ce39022000c74655c720440010ff0abb2408800e1f21576481100045fc22ec90220028bc845d920440011bf06bb240880063720d76481100061e3a6ca9022000c3f65dd12044001878cbba240880123da1b714811006e3b3b6cb08220048ec8754962040091d90ea12c4080123b21d32588100063a3aeec8802000c7776dd510040018f0ebbb220080031eddb7544010
  | 1 => 0x8e7bb2421080335ddb734842102c7c43aa0b0042058f887501600840b1f10e982c0108163d20575987200947b43ea2b0e4000ab58414561c80015ab0628ac39004ab9a08515872000578c00a2b0e40128f48750561c80251e90e98ac3900123e20175586200247a43aa2b0c40048f48750561880014eb0a18ac310002ad610315862000572c1062b0c4004af2800c561880019a8e730a4310003351cd61486200045ec3ccbb224000a9e83997644800153b0732ec8900022fe1d65d91200045ec3cc7b224000a3e8598f644800147b0b31ec8900022fe1d63d91200cd57436e5b224019aba86dc3644800153d073aec890002a760e75d91200061eba8ebb224067aae821d7644800155b043aec8900028fa1673d91200051ec2ce7b224066aba801cf64480015730039ec89000387d4e53d91200045f438a7b2240008bd8714f644807d57501b96c8900022fa1f52d91200045ec3ea5b224000a9e83d4b644800153b07a96c8900022fa1c32d91200cc5ec3865b224000a3e850cb644800147b0a196c890002ada0432d91200055ac0865b224000aba800cb644800157300196c8900028fe1571d91200051e42ae3b224000a9f835c7644800153906b8ec8900022fa1c51d91200045ec38a3b224000a9e83147644800153b0628ec890002aba0851d912000556c10a3b224000aba8014764480015730028ec8900022fa1c31d91200045ec3863b224000a3e850c7644800147b0a18ec890002aba0831d912000556c1063b224000aba800c764480015730018ec8900faaba0b70d91200045f438a1b2240198bd87143644800153d06286c890002a760c50d912000557410a1b224000aad82143644800156d02286c890002ad60450d91200045f43e61b2240008bd87cc3644800147d0b986c8900028f61730d91200947cc06ebb0a40028be86dd1614800117d0fb22c2900030fdd764585200061e3aec8b0a4000c9c73d91614800117d0e322c2900030fdd464585200061e3a8c8b0a4000c9c73191614800193ec9b9ac2900032719373585200047bc3ac230a4000cb8649c22148001970c8b844290003271cf64485200064fb26e690a4000c9c64dcd214803395cedb2440900123d21d51584200247a43a82b0840048f4874c56108001958e9bb240100032bddb74480200065c3a6ec9004000cbb76dd1200800596ce8a0ec5880163b2097498b100247a40ae6b1620058ec8754962c400b1dd0fa12c5880029b6144258b1000566c1884b162005ae68110962c40015d300212c5880163b21d3258b10006563a4c49062000cac7458920c40039b4e6986c5080123b2097398a100247c402e8b1420048ec8754962840091d90ea12c5080123ba1f3258a1000536c2864b142000aad840c962840015cb02192c508012baa003258a100066639cc490c2000
  | 2 => 0x3dc00000002d813000c90009a3040016d4b0003b00000248800c4003d562274db4f09c2c8545547101d6510400000003f01d1010e5149031467001540014f31c000010300000000000003700174001200007b000e41303f00000000000000000107000005640013d16000c01356b1e9563b8000e16114c860007f15c004d003168002b146000001c935340af09cae00032000943a40052400000000ac10334000000200006828000000081e0280003004030000e8000480001002000080380000808008000001e01006000140300a008060400603006000200000400006018660000003004010020980a000000081803822028020a800000040380c07808008000000001000020060000e020000000802000000000600e01002050020080200802020000100600806028000a0120080a0000002830020020580800002ae61050583210056cc18a0b064212aea8214160c84015e302282c19084a3e21d40583210947c43a60b0642058f88754160884014f30a202c110802b660c405822100574c1080b044205af281101608840b1f10e982c1108023761e65d8d210054f424cbb1a4200a9d8499763484011bf0eb2ec6908023761e64d8d210052f42cc9b1a4200a5d8599363484011bf0eb26c690892b3a1b72d8d211256b436e3b1a4200a9e849d7634840153b093aec690803175d475d8d2134d67410ebb1a4200acd821d763484014bd0b3a6c6908029761674d8d213456b408e9b1a4200ad5811d36348401c3ea92a6c69080237a1c54d8d210046ec38a9b1a4251ad681dcb63484011bd0fa96c6908023761f52d8d210054f426a5b1a4200a9d84d4b63484011bd0e216c6908923761c42d8d210052f42885b1a4200a5d8510b63484015ad02216c690802b560442d8d210056d40085b1a4200ad98010b63484a359d05b8ec69080237a1c51d8d211246ec38a3b1a4200a9e84147634840153b0828ec690802b3a0851d8d2100566c10a3b1a4200ada8014763484015b30028ec69080237a1f41d8d210046ec3e83b1a4200a5e85d0763484014bb0ba0ec69080297e1570d8d210052e42ae1b1a4200a9f845c3634840153908b86c69080237a1c50d8d210046ec38a1b1a4200a9e84143634840153b08286c690802b3a0850d8d2100566c10a1b1a4200ad68114363484015ab02286c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c690802b3a0840d8d2100566c1081b1a4200ad68110363484015ab02206c69080637a1b73581211246e436e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac0908023ee1d60181210066639eec9084200ccf76dcd21084019a
  | 3 => 0xa03c13f0d0181a81b49406590a75cc7e0b00054400528000d4290009e0bc6d1388a164001d4d55712f3ec000010f034813590d0896705828198bc148a6261290001a5b0bd0008500000000004a80033cd42f95e3945c1a4493840a000004b00037c1400000114001784b3a0004f8000007c32d0c0000b00000110e7360360017048419448002348335c00000fa368005a88f1cce34ccf3365102d4ad47d3d0003a3f4514ecf2000a2000c607000188424e92346d302fc65420763751e4e137175140cc3d5085f310000005545d27000842dd4d00017460b928c111d14c00000000004b82d001432cc3c001061c122405414a00003c000014e000002c42422000000084e40000077000f60002300060259320000e4080000000000b029000000433f80024c00084014d800510ff080d33ad501211d030e02248221d485c8a507c000000200000001533d06e1bc6c00104320cc0e4c24b4004ac00001630006800000000585a000444002540000000000f925c003bd6f2386b010300f947244093c4002ac000011c388003481e0000000126190dc0000000157378aa568ea3b50046856128ec18c05338b8548125b825001692ed5d44c004910a0002645519001580b879000b4000d14c5403e02a140472a4460008b27d6d0550530ca11e15b000002315f2a17142cca598e60010926cba1f40058000184000000026400000
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
  | 9 => 0x124c
  | 10 => 0x138c
  | 11 => 0x94c
  | 12 => 0x94d
  | 13 => 0x94e
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138d
  | 17 => 0x138e
  | 18 => 0x3
  | 19 => 0x8c
  | 20 => 0x8d
  | 21 => 0x8e
  | 22 => 0x128c
  | 23 => 0x150c
  | 24 => 0x98c
  | 25 => 0x98d
  | 26 => 0x98e
  | 27 => 0x128d
  | 28 => 0x128e
  | 29 => 0x150d
  | 30 => 0x150e
  | 31 => 0x20c
  | 32 => 0x20d
  | 33 => 0x20e
  | 34 => 0x140c
  | 35 => 0x154c
  | 36 => 0xb0c
  | 37 => 0xb0d
  | 38 => 0xb0e
  | 39 => 0x140d
  | 40 => 0x140e
  | 41 => 0x154d
  | 42 => 0x154e
  | 43 => 0x94056
  | 44 => 0x94054
  | 45 => 0x94055
  | 46 => 0x124054
  | 47 => 0x124056
  | 48 => 0x138055
  | 49 => 0x138056
  | 50 => 0x124954
  | 51 => 0x124956
  | 52 => 0x95255
  | 53 => 0x95256
  | 54 => 0x138955
  | 55 => 0x138956
  | 56 => 0x95394
  | 57 => 0x95396
  | 58 => 0x125394
  | 59 => 0x125396
  | 60 => 0x139255
  | 61 => 0x139256
  | 62 => 0x98095
  | 63 => 0x98094
  | 64 => 0x98096
  | 65 => 0x128094
  | 66 => 0x128095
  | 67 => 0x150095
  | 68 => 0x150096
  | 69 => 0x128994
  | 70 => 0x128995
  | 71 => 0x99295
  | 72 => 0x99296
  | 73 => 0x150995
  | 74 => 0x150996
  | 75 => 0x99514
  | 76 => 0x99515
  | 77 => 0x129514
  | 78 => 0x129515
  | 79 => 0x151295
  | 80 => 0x151296
  | 81 => 0xb0214
  | 82 => 0xb0215
  | 83 => 0xb0216
  | 84 => 0x140214
  | 85 => 0x140215
  | 86 => 0x154214
  | 87 => 0x154216
  | 88 => 0x140b14
  | 89 => 0x140b15
  | 90 => 0xb1414
  | 91 => 0xb1416
  | 92 => 0x154b14
  | 93 => 0x154b16
  | 94 => 0xb1554
  | 95 => 0xb1555
  | 96 => 0x141554
  | 97 => 0x141555
  | 98 => 0x155414
  | 99 => 0x155416
  | 100 => 0x952d6
  | 101 => 0x95496
  | 102 => 0x992d5
  | 103 => 0x99655
  | 104 => 0xb1494
  | 105 => 0xb1654
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1106
  | 6 => 1320
  | 5 => 373
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (44970+((h/368+packedAt gbK7 (40922+(h % 368)*11) 11) % 1328)*12) 12
  | 6 => packedAt gbK6 (68640+((h/440+packedAt gbK6 (63360+(h % 440)*12) 12) % 2318)*12) 12
  | 5 => packedAt gbK5 (23247+((h/124+packedAt gbK5 (22007+(h % 124)*10) 10) % 541)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc7e03f8e1e1fe380fffc701c072119cc64f667
  | 1 => 0xf8ffc0701fe1fc00e03f801fff46267198c87f
  | 2 => 0xff00007fe001ffff003fffe00798c7821f0f87
  | 3 => 0x7ffffe0000003ffffff8e0f803e00ff8
  | 4 => 0x7fffffffffffc0000000ff0003fff000
  | 5 => 0xffffff80000000000000000000fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xc12087060602608223ac1144510008c4245663
  | 1 => 0x484381300a21a40c44948088b202025098c82d
  | 2 => 0x92050a122000c926011924c0240847800d0a86
  | 3 => 0x8144d555400100a224b1340e0b803600550
  | 4 => 0x122069999912589c00020180f70003d2a000
  | 5 => 0x249c38010110006010000c0200fdf528000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36432
namespace PEqualNP.Outside.L_meta_36432
open PEqualNP.Outside.L_meta_36432.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
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
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 473 := (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat (concat bs3_4_96 bs3_4_128) (concat bs3_4_160 bs3_4_192))) (concat (concat (concat bs3_4_224 bs3_4_256) (concat bs3_4_288 bs3_4_320)) (concat (concat bs3_4_352 bs3_4_384) (concat bs3_4_416 bs3_4_448))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 632 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 bs3_5_512) (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 29 := bs4_3_0
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
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 473 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat (concat bs4_4_224 bs4_4_256) (concat bs4_4_288 bs4_4_320)) (concat (concat bs4_4_352 bs4_4_384) (concat bs4_4_416 bs4_4_448))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 632 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 bs4_5_512) (concat bs4_5_544 (concat bs4_5_576 bs4_5_608)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_5_352 : Interval gbAtlas 5 352 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 373 := (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352))))
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
theorem bgb_6_1312 : Interval gbAtlas 6 1312 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1320 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))))))
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
theorem bgb_7_1088 : Interval gbAtlas 7 1088 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1106 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80fefefeeefefafc80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124270 * 2 ^ 32 + 4277861504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36432.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,2]⟩,⟨.or,[4,5]⟩,⟨.and,[0,7]⟩,⟨.or,[3,5]⟩,⟨.and,[2,4]⟩,⟨.and,[2,3]⟩,⟨.or,[6,9]⟩,⟨.or,[1,11]⟩,⟨.and,[12,13]⟩,⟨.or,[8,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277861504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277861504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36432

open PEqualNP.Outside.L_meta_36432 in
theorem PEqualNP.Outside.L_meta_36432 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277861504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277861504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
