import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36268.Model
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


end PEqualNP.Outside.L_meta_36268.Model

namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
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

def SBf (j : Nat) : Nat := [5, 6, 6, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36268

namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
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
  | 1 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 2 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc22231451041240529272126048a690c26315c
  | 2 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36268
namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa0046200820de43dd43be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x202b0a0a1e610030
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (104+((h/2+packedAt s1K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s1K3 (56+((h/1+packedAt s1K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7fffff01fffe0c1ffffc1ffffe0ffe00f3f3fc
  | 2 => 0x81f83ffe0fffffe0f83fe1e03ff0ffff4ccc7f
  | 3 => 0xfe003ffff07fffff003ffe003fff0fff8f0f8f
  | 4 => 0x3fffff800fffffc000003ffff003f00ff0
  | 5 => 0xffffc00000000fffffffffffc0000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc30011c21041003184c02238e0112181151bc
  | 2 => 0x24425224642884a06a1521449290a4a944c455
  | 3 => 0x1094a4488351094d042a5409252a09528b0a8a
  | 4 => 0x596738914a1dae76b683111239ccc063f00f60
  | 5 => 0x618630e18c61cf98c733999c01888183eea000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36268
namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x3291464816208007400028400ee42ed42ef32ec32bf41bd41ef21ed21be40bc40ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x611096aa0654c534866aa2205394e20
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
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffe07fe0ffe0ff07ffffff07f03fe4ff3cf
  | 1 => 0x3f07ff87ffffff07f8783c0ff87ffffb24c7f
  | 3 => 0xfc007fff800f87ff8007fc00fff803c1c38f8c
  | 4 => 0x7ffffff007fffff80000fffffc01fc0ff0
  | 5 => 0xffff8000000007ffffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10a002300411000190088446500910540491c5
  | 1 => 0x4844a441288442502483228824824aa892441a
  | 3 => 0x296d68931daa4eb68c45ea12bd502b0dc38e8c
  | 4 => 0xb28a51245103152b59504024ca64b0116c0b60
  | 5 => 0xc30c61c661cc67cc6e6673380c40c221fb6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeecc8888eeeeaaaaeecc8888eeeeaaaaeecc8888eeeeaaaaeecc8888eeeeaaaaeecc8888eeeeaaaaeecc8888eeeeaaaaeecc8888eeeeaaaaeecc8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36268
namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xc817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a07bd4940b7a92817c52503d8a4a05b14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5987b94b30b7296617d52cc3daa5985b54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ee32083da64105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f460887e4c110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c837e52907dca520db94a41bea9483ed52906daa520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f790c31eea18637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1
  | 2 => 0x22a000bc00e100360000e53581112d05700017c000094927b8ac88e03e5792a11748493837a7800025d378a634e498e78f244c620e494b4e45e8621dc2f868c701f31062085500c3906303f2351645f81a8660000e87c000150000fd0000ac528bc80020c9753ea411443f0e800050274c2120f0000c4fe000000001348004b2318e600032c0e0b8a2c0281e08ca7633ca38da800010000000be000000000000223580026a35c6100016f00000096000000000f226101679813a02000000000a50c499814800246484000483561482c8250007a80000011a735040000926683ea970d0000000002d6000000000000013ca0c000000000000000000016d4aaa1c001f60000004a80037c144000000aa9200000000091d2613409e8a81b92e1566ec0000009a00110800000000949b7000280d9a560ee7049e000000000609b04281849c1904068fd2d8000ec27c0000046c000000002409cc0014517648853a43000000ce06d00033d2891a000048e285c000220b093601e71cdea322d4858d11912a616057a582c6a50c593b17e3e4c0239166000e217b152001100000c0268dd05421a0b8f81a83e47647b955314458259744f421028071438340fc82f3488886a09c394001168e125e78c0002b462654cd8000000003f8003022b00013e000538cea8a2ee000449f14e2000a20003284dcd48694fc000640dd000000c7800000324000002a4000000960004f4fc1c20000000005d1a6000b61573fa00020000000804989dd3ce4cc0000800007028280540301025000010081100c0007c0000800010100040000800004030000d00c0903039000000182a0000002c010180001004004040080000402020030000001004000130040300c00010060000100c0300c0100000000010000400804000080000100c0100c000200000400014050000008c0401001030030000602c01008050000307002004010000000002044040140c0000f0100000400008020740c008050080200801004000000c008000000000000000030141e00c02054040100400000004000040600c12000010040d00c19028060040703c070100000c0e0200001c02050000080002c0300001000030000205c0100c010080501c000000200001000000080e00801000040000001000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485e
  | 3 => 0x4e52f0b10f42e548a343da00000022000000000000000000023e0b62404c000034848000000000f8dfa0e446000800ba00042c6d1483fe9d4020632921940009b064218009a05060751d8670042d09fa191e80802d0000580000024043c070001ef0009100016228c0000023c000000208ff0000000000011846c8e0f6436078950793a2444a109d000428001b93e82492b82a3f68241fa4f3c4000c29e938051c000e830494d449c60d6000cba884dc99c00237000810000004000011d0cc30e04c001084302b80018d0425b85e21a1aa0012f9e502040d12047456780b91930001b80a8e4116000002271424b50ea862c0a311c043000000b411830c0011810e000000b29661fc000000000004410806420e0007a800000000ec0005200006287c0004c03a0000000001404620435d2292800077c408001de60c000000001ec0022e1b8001428000005f4921320009b0718170720d04c8000000000000021e70c00140274000749a54669b4d90002189709a8003423f4a815423c0000024a29a59ccf9b42ac7f85227b094a588a0de0320ec0021f06c3ac001053a46d9230000363e8de0731dc000000003327385b86c29e49c750003d639c000004ca5fcd8872256a54000004a00000000004824c0015f1c476d400cb2e05693e0004e8001420004160010a96435a08d050d1000000000000009a0c48c30000000023d0007b00000010a3c08e9aa324000848db00e0000000019c000899d711e000a09e852498848a9345e56c00260000000000d9000000000004e0029468450002d82f00009c92c650002022f4ae16910e75000000298698380ec05a0014586a0006e00020d00031c0000d128448000a331c000612071e200d029cb4eea3d089f50000007d89e0000012900044a000002641802d5358000002b4000002e63b5268333c27dc180050007693f9253ac4100000000047c000f32b07790995d45200000000286000260061140f4ba8000008a0bb00000085c000750302c00b0b804c37d030004c63980000000000066800000001410002a2348000000786bc299983aa0000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x310c25f654c0309ed95300c25e63153209758c54c823e6414f208f59053c82ad640cb208f99251c823d6494720b318d21c825e63d52209758f548825e63152209758c548827661152209d584548823e6494e208f592538831e6494e20c7592538834d6294e20d394f42882cd6310a20d394c428834e538ca20d394d32882ae6488620d394e218834e5308620d394f208823e64951209bd89544825e63151209758c544823e6515120c798c544831d6315120cb588544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d209b996424832c54909209b195424832c54509209b997324832c54cc9209b99432482ad640c920cb150324826e65c8520cb153214832c5448520b318d214832c5488120b398e204825e63150209758c540826e62150209d984540827561150209b98b530823e6414c208f59053082766114c209d584530826d65d08209b59442082cd63108209b596320826f654c82097d8d510825c63544209b59621082ae64884209798e500825d63940209bd9520082ac64480209ed95200826e62d53109b58b54c425e63953109758e54c426e62953109b58a54c426f6254f109b18953c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c425f6354b109718d52c426f62552109b189548425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6494e108f592538426e6294e109b58a538425e63d4a109758f528423f6454a108f191528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d6580534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524433454905109d1954144358538c1109e195304425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520433554c40109e596100435953840109dd95100433554440109ed9510043595344010
  | 1 => 0xc74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c71e63950318f990540c66e62150319b588540c67a60150319e580540c65d6590c31c7951430c6cc6250c31cb952520c72d5494831cb951520c72d5454831d390d520c74d4354831d354a320c69d640c83197d95310c6cc624c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c75a4354031d650d500c75a3254031d60c9500c75b3154031d64c5500c65e63153219758c54c863e6414f218f59053c86cd6310b219798e50c865d63943219798e548865d6395221c798e548871d6395221cb58a548863e64d4e218f593538863e6414e218f590538867a6014e219e580538872e5490a21cb951428872e54cca21ab590328872e540ca21cb953218865e63951219758e544866d629512197d8d544865c63551219ed81544867860551219798e534866f6254d218f990534863d6414d2197994534871e6414d21c7590534874d6214d219b997424874c53d09219b99442486cd6310921d314c424866e658c921d314e324866c654c921d314d32486ae6488521d314e214866e62d50219798c540865d63150219e980540867960150218f990530863d6414c219b988530867a6014c219e580530866d65908219bd95420866d65cc8219b59432086ad640c8218f992510863d64944219bd9521086cc63484219dd95210863f64540218f191500866f6254f409b18953d026e62947409b58a51d026e6294e409b58a53902ac6250e40a758c429025f63546409718d519026f62546409b18951902ae62906408f997415032c52d0540cb149415032c5290140c794d43102ac6250c40d394e521034d5394840d394d521034d5354840cbd0d521032d4354840cb54a421029d6310840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cdd0d51103354354440cd909511033442544408f59641102ae6290440cd54641103355110440cd547401023f6550040ab189401033551500409ed95401026e62d53309b58b54cc31e63953309b98854cc26d6215330c795143cc2cc6250f30cb95252cc32d5494b30cb95152cc32d5454b30d390d52cc34d4354b30d354a32cc29d640cb30b318931cc26e62d52309b58b548c26e62152309b588548c27661152309d584548c34e528c630d3948318c2d9600c630d394b308c26f62551309b189544c27761551309d185544c26e62151309b588544c25c6550d30b3189434c2d86050d30a7590324c23e64145308f590514c26e62145309b588514c25e65cc530b3189314c2ce628c1309bd89540c26c62550309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c26f62544309b189510c25d658c430b658
  | 2 => 0x10000008e00007a6f4448003ae000ab0f238a0000010e324000ce9151a8574431f12740000394636257c001bf0003fca18382440ec5a9614063082592b2f0814b90c331213c9f1f30b8114000001683cc2c800290864fa0003940b81480000046000008402740e78141001cc49898034000000000001acb58060000100012c3563008ea170d44c0c69ea2ae110b7897426810889580e0000ad8181c6354418963341942e8900002741c8113be36c5b01d0be6309c851020748cb19c0f2000ca80041c2e46c16626a5a0108c72da46c492161f634cf49100003f0fc01f3b879c068ed0188084782411a3d8000691bc6cce40170006c07d19f2c05f0001bc31021c000ec30a00000000000000001b23b221085907000000001be0003800017e00001c0100404000010080400400000090280000000028100180400c000000f0180d00001048030000001000000060640400c0b01c0e0180101c0006c000dc050040500005020000c00f03c000b0060080201c050000102c03014020280b024080580202c0101c00004080100e0000800c000040e000150000001c040440500c1a0000201c000280304c0a02407000180000006c0a0000f05c10000100240900013010080000e00000038040140e00011004000080002c000040001400028060001403405004000180504c090a410080080040b000220180400410014040040703a6e62947439b58a51d0e6f62543439b18950d0e6f62546439b1895190e6e62942439b58a5090e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210eac6250f4297d8d5190a5c63546429798e5090a5d6394242d31895310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7a60d53329e58354ccacc6250f32e350f42ccacd6310b328f992518ca3d64946328fd91508ca3c64542329d986544ca7561951329bd89544ca5c6550d329b996424ca6c6550932e350d424ca3d6595032cb189540ca3e64150329798c540ca6e62150329b597420cb2d54d08329b594420cb2d5410832b358c420cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320cb1e5350f41ab18943d074e5394b41d354e52d074e5354b41d354d52d072f4354b41cb50d52d072d5290b41a758c42d072e52d06419b988535066d6214d41ab18943506b46150d41a758c42506ae62905419798c505065d63141419b988505066d62141419bd89531066c6254c418fd95411067765504419bd89501066c62540419bd8954cc66c62553319b98854cc66d62153319b98a50cc66d62943319b98b548c66d62d52319b98a548c66d6295231b3189438c69d640ca318fd91508c63c64542319bd89508c66c62542319758e544c66e62951319b58a544c66f62551319b189544c67b60551319e181544
  | 3 => 0x2712317c6502807b06e000000002d4000f60612645dcd5199226100c30c6000000e580000006c3195c0e285000000176000178003dc0a0a21f60000002d8120006b8000c93b0000001083e400000067308000c705a0007e82b000090534bda0d000008f80d0082328001c63700f8a59360f44ecfe00e33c000f01270162dc64019410500758e90de5b0450003ca254001c41a20010d000392828e8866424178d41931408547217a1983b84a08819c37c1618305a608738d93b6244181711584789f93d292214a10151e8680000001e2000000001ae71c0000000000000000000000000b000081c7e8ad17a1300000017000054000000000ea9c10002b80016e336000001201ac26c0012d3a631453000200000fd80029c700001a2416414000000000880014f20465c7a95e000000979062340040009c074000ad00036e2fc6e981040180da1a71f2000d284a0c8800878a90f01883b8001544840199022c61cdd8580007f83b14c422000528ab102000001d634c1c8d78a13420009b9e12f20001b0003464a0000fe0fe000868a3386000cc1cd36c00077901232000ef1d4056288ba1632ca368000000647dc708000fc47c7b9541621b4f115128a5d8f40e219e0001397340c4ccfc80000004c2484d1cc014ff80006614c049b5078430341fd25c6441a9520aa62d0c08e41e310751693522f0a084213c2640013831e3350803401e4986e1ed062118f192a118424989eb00015c00000214588a38520fa000590ba1160004d1670f87bc7813c2ea76841000000830521ba0ea32cdc97d2a600000112038001049703587982a0f803c564219501ca450a51e426808cbf8003840fc000260d8000000003ea6000012500045c000002520000018a00011c001551a40004f8000000000b0250543a00016420800037000000774538001662bc8180a35a490e6000000000d207439c000000c
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x18a00000054f20251801244538c34b0400c00135c70004001090160018000c500381835516310832a90e4a1aa018d19740c9500c6a439262a80638358d6295221a1ae72a28510c2d769503288706b22c429a43135d85310921a1ae829a6490e0e6414e214869239286a8881455cc4254440c4cc4a8c8220624625454010325292c018c61835916294e2089aed298851050d7494d3288307324a710c418358d6215120a1ae62a2849042d7615032483062a0c690a41831526388120
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x80d0080d87990538852180d87992538862080d87150634852080d871526388120
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s3K5 (20138+((h/221+packedAt s3K5 (17928+(h % 221)*10) 10) % 963)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87ffffc0ffc3fe0ff0ff0ffff87f03fd31f3cf
  | 1 => 0xf81f87ff0ffffff07f0ff0e07f87fffece4c7f
  | 2 => 0xffe007fff003e3ff800fff007ff803830f8f8c
  | 4 => 0x7fffffc03fffff000007ffffc03f00ff0
  | 5 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x908500460084400190110123280910a81091c5
  | 1 => 0x242088825010050210610441082495046441a
  | 2 => 0x314b551263aa86b6888baa095d502a1b0b8e8c
  | 4 => 0x659466248a20cb2b5aa088126664b023b00b60
  | 5 => 0x46184438cc3313cc6ccccc9c0440c043ed6000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecec8888eeeeeaeaecec8888eeeeeaeaecec8888eeeeeaeaecec8888eeeeeaeaecec8888eeeeeaeaecec8888eeeeeaeaecec8888eeeeeaeaecec8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36268
namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8de32dc32
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
  | 0 => 0x3ffffe07c3fff83c3ffc3fffe1c07ffc71f33f
  | 1 => 0xc1fc3ff803ffffc03c3fc781fe007ffe4e4c3f
  | 2 => 0xfe003ffffc1f0fffc03ff801ffff87038f8fcc
  | 3 => 0x3fffffe00fffffc00001fffff803f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x882802300442000c0444088ca0450928109315
  | 1 => 0x14526441a98c89c21a1a4511520a52d2464c2a
  | 2 => 0x8498889280d01254402c9024649304188b854c
  | 3 => 0x296331252206acaaae820449992c6063700ab0
  | 5 => 0x318221c63318cf333333267010304083ed6000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfaeafaeaf888f888faeafaeaf888f888faeafaeaf888f888faeafaeaf888f888faeafaeaf888f888faeafaeaf888f888faeafaeaf888f888faeafaeaf888f888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36268
namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc437d52886fca310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53486fca690df54d21be29a43ee42487da8490fbcc921f619243f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50086faa010df94f40bea9e817e52d02faa5a05f94740bea8e81bf41d037a83a05f55240bf29c817d53902fca5205f54a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a817f52502f8a4a05fd4540fba8a817751502f8a2a07d14540ba28a81bf415037a82a07ed0140df202817e54102fca6205f54c40bf290817d52102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280206e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa418778c830ee190617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef32883d865105f94620bea8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2905f14520f790a41ed21483f460907e4c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4107bcc820f6190417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c217e50843f481087e50210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443f480887e50110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dd0410fa208217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0x400000000008000050000000000300600000800000000018030000040000200000c0200d0000040080b00201400808000004018020060000000000002000000008006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832f7a1065ec420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50507f6a0a0ded4141be28283f850506f0a0a0df95041bf29883de53106bca620df54c41eea98835d53106fca420fb94841b7290837d52107daa420db54841bf28883bf41107ec8220ef50441faa08837e50107f4a020de94041bea8083f950106f2a020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf29463ee528c6dca518df54a31f6a94636d528c6fca318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb90b21f6a1643ef32c87d86590df94321bea86437f54886fca910df55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29
  | 2 => 0x2ea264000002f4194000000046185d000000000000a22fc054000000006890f81f2a0434002281bc7e83201241c000581960165a8000b70000000005a2668a4a3185000000000000000900005e000000e08324000010900000077400000000000000000000001d1b331865c5c03c0c036c3b1f7000000c48033d4334000001fa0000008e220001189a32e80000000000000000000100100000000000004e9ec00000000000000000000001a01700002f0004c05183d1ce590000002480000012e00000013a3a154000000001c0000ed84b20a71c000572f68d4ec80005a5e5218a4018750000000001549d8b300059c001b000029400000342000000d14280003c23d000640f10000000c45e8540007fc4e16e08406000038000000002480fe7240000000000000000472000480be00013c000000c24e0000003a27c0ad0b62d8034951e8430834620001284fc000263c241cf71e5000000000000001bc000dc000000000003860011c0000ea000ab8931760003a0fc31c754d30820000005e000000000001ce00c2fc000a1286000001c034e4e400037000748ec0001b09084c0001d835c198000000000019b37a2240000048c000001830004803880000077c428af36a0010600000057c628631f2000bb8003586b4000000000008d9cf0b6790f38000008dc8f80030400000000040534000000000011307c0001b5150000007811590a23c5e11b0003fc1dcaa800000720f9800408000d493a2c200000000000000d7a49394198be82946461c6000036254418101000000c980048e00053000172000a58000008410b1b8000000a91da0000002382500006cf30010005580013e00a000001cc09a1380000033a128000e61d043c160a9000650df00024e514000002bc0000000012a0006a0ea44a27c0016500017c001bb000259018000008080022d0006900007b3160000000015c0001a0002f83e000000000634000000d08b071a113ac6a8ad87d410000961d300000000000000000000000328bc000000005a02605d29e0009aa3b000560b900035604c2995c0005506488a38488c00097000000698000001c12000000007063000250000c50000000000000040e0000004148208c959c42422201c80029223400000000124fc19800200000800806000004000010020000480000000400800000000078080000240000300a004008000080000000600000001800006004000010240080000000000c000050000040100100a00000000000004008070000000100d004014010010020080000400e000030050000000000c000000000050020000000201400000002000000018010000000100000000007000004000008020000040000200a00403000000000008040000180080000c000010080020000100100000c000020080000000100200800
  | 3 => 0x23433800000000000000b80000005380012900057423195300680b487300000000132466000588003085b4000001e8718722202185ac8a85000081400000000000110dd26c0007d0511b20003d0000001ad1200007c449058003f800000000000000d41251e0000a20ad3bc394a10000145800000000000076800196050000070000011080014e000000002b27bc6f8000000442c0000000000000028e000240001c42447d800000878408000000007a80008826cbfa0f1347d4db01640c914db8cc08a0000000006c000001f2000868001530087700021b00052800000000000000002164750b8a80d81a8000842e663d0c80022e668f886e06a000000873da7ec0014c3103d8000002223ac000000000003900044e5d8000920ce2c80708c35c5040493700084c1082a2e26e497a2200030d2200018e400b196f34a8fceb89e374458b100027a000310ee0000000000000020c000000008241400043a000fa00000048c561d00000010523e0006fc650b502e500000001827e4000790007ac000001ac0009a1c5378000d910900038400000116000000690005987f90e01067c7f03b25a468840ef39a074610000004980023000033c0f0000b278c0010400000000000000000cc8f70ac7d90a8000000011e00f00060400000000000000d5000000a4000000001170000000002185210c3c8988a011e0b815800000000c8919000471009cb0000000d00019c40c558001a47f4000000003a46d1134384509e192000000640002302d08101007e000000000000008319e00000000000244000000000006d0f48f10001f8798
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x530863d6414c219d984530867a6014c219e580530865e63944219758e510866f65484219dd9521086b86050740ae580419025e63145409758c515026e62145409b58851503566314540d558c51503666214540d9588515037160145408f997415033451d0540cd14541502b86050540dc147405033451901409bd89531026c6254c4097d8d521025c63548408f59641102b96010440ae592401023f6550040ad185401027b6550040bc18540102bb6550040ced9540103b36150040ae18540103b06150040ac185401033951500409d98754cc27561d53309b98a51cc26d62947309b98b548c26d62d5230b6580328c26e62951309b58a544c26f62551309b189544c27761551309d185544c3696014930d314b314c34c524c530d314a304c26e62150309b588540c27661150309d584540c34d520c83097d95300c2cc624c0309ed95300c27661d53209d58754c823e6414f208f59053c82766114f209d58453c825e63947209758e51c825e63d52209758f548823e64d4e208f593538834f530ca20ba58032883c8328c220ba189308825e63951209758e544825f63551209718d544827761551209d185544825e6394d209bd89534825e6514d20d6580534834c53c8520d314d2148358538c1209e195304834c53881209798c540825d63150209d984540827561150208f990530823d6414c209d98453082756114c209e980530826d650c820d354c320826f6548020b318d200827b65480209798c54c425d63153109b98854c426d62153109b98b53c426d62d4f109798f52c425d63d4b10ced5040c426f6254e109b189538425f6354a109718d52842f16010610ec10640843385450210bc18540843b341502108f992544427761551109ed81544423e6515110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524427a6590110ce15240442786550110ce15140442f06150110ce153104433454841109798f540425d63d50109b98b540426d62d50108f59654043346155010ce181540423e64150109798c540425d63150109b988540426d62150109e980540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520433554d04109d594410427965d0010ce55340043b341d00109e59440043395410010ec10440042796584010ce55210042776544010ad191100427b6544010ae19110043395444010
  | 1 => 0x80000254000007f2126d1362418a7aacc21a9c2f1324522a6e2340000004800a2aaaa88728f010001b03d80000000000000000000000742908b000002e600000400f4a18c88680000000000003c8000000ab01be00008000000f00201c000000100000000050140001406008020100101c2502801000000040300c00038040100200c000000300c00000000000d0000100400000010040000405000040200b00400014000080000c010080002804020000000102800038020200100002010000040000c0302c010280100000000040000100c00010010000400000018050040200000000000040100003000050300000000008090080f03e6e62946439b58a5190f4f43149438fd954310e5f6550c43b31894310eac6250f429798e5190a5d6394642c714f4350b4c53d09428fd954210a6f6550842b318d4210a7a60951329e582544ca5f63551329bd89544ca7661d50329d587540ca7a60d50329e583540ca3d6595032c718d540cb2c62550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cacd6210c32cb553420cb8f43d08329b594420cacd6310832b358e320ca5f654c8329bd95320cacf654c832d3d95320cace644c832b3191320cb8e544c832e3551320cacf614c832b3181320cb365494432cd552510cbc53294432cd951510cb355454432f14c9510cb3a5494032ce552500cbc93294032dc946500cb715194032ce951500cb395454032f24c9500cb725154032dc545500ca6f6254f419b18953d065f6354b419718d52d07734114141ce904505074e5394841d354e521074e5354841d354d521063f6550441ae18141106776550441bc181411075a5394041d654e501076a5294041da54a501075a5354041d654d501076a5254041da549501073b4154041ce505501067a60d53319e58354cc6cc6250f31a759032cc74d520cb31b658032cc66e62d52319b58b548c66e62152319b588548c67a60152319e580548c7666194a31d394b318c66f62551319b189544c67b60551319e181544c65c6550d31b3189434c69d640c931b5984324c6d9600c931b398a314c65e63150319b988540c66d62150319e980540c679601503197d95310c677654c4319e98354c867960d53218f99053c863d6414f219e98053c86796014f21b318d42c86ad640cb21d354c32c86e9600cb219798f548865d63d52219798c548865d63152219e98054886796015221d59865388756534c621d394f218865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534866c6550921b318d424866e65cc921ab590324874d530c921b998432486e9600c921b998a3148674654c521f10c931486ce63885219798c540865d63150219b988540867a60150219e580540866e62d4c218f99
  | 2 => 0x1ca00198002a4001945b0568f86200000a31766b9600013e1498e002c80000089000001040000000098000000029200000002260000085802b88748daec0702c000247e0002f87c002d4998d2000002d800afa0054a725f000748000015a000008514c002744c29a438002292000000000001d94e0000000000000000006c080000015400000000ac8720600000168004f16a7c80000000002640e24e000002c0006019a1629e278001800000202ac9a6001126c97200036001400000000146001e00022e592ba000001fa420000000000b6064ae000001709aa326da9630a6c959a20019e0001a0000000000ad25a000002b80000000810007900000000002e4131ce7116e75aa61a0e29fa3a9d8304310a0016800000ad800971da510fe3a8b400000000000000031000000d09e0cc0008000000ba2a02880000000002ac00000002225f8fa7d1fa3612c000003f0143780000000001560025e900504988815000ac00432974280ee9e990b590261ade109921798c2309c08832001229c2ea0003a7b0003a096001c21e218598f8980000000000000ab80082a4a0013477800000002100e00000000000000000000000003c2a8b81ba9a0ec0027c000dc000002aa38b1800300e4290460000000000001824580000178b6a0c422ee7b80000000001dc00252000000005c10000528006580000162b38000015e46800440d4000007d8000021e0000000018000340012a122d0018004e9fe002ca94000000002e00000220919063682e000a6002287611c002c400000002f275000000007a0700000012800000000000068000bd1c8000002a2f000000001ac001241b800b48ce0012896000000006701e000007c15c00000a20006120eb700000000000280000025298a01420026235800381bc2c8001e80000000a08824e21000000931506228e001a4b086a00294000005617a4789a71826521c003000af1e60003e059cc001a8921e2821aa2392e000ba8c2440000000000198009ba84110004604e248c6398000a
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4c63401c001150500b5524000090080400cf10a38c0800126059a65384c899065c15513254432e12a8992a01974132545500ca863a2a619243521c1530c921b0ae81926290dc1700c93148722b1ac428a818c5d46150040d24e630a8020691731854010351390c2a0081a85c86150040a1ce9a9865106305418540842593b682a04218c1506150110c60c2302a80863165d074004298ba882200210e1d95444010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4400c11755cc6150040c21755c86150040c81735c86150040
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
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
  | 5 => packedAt s5K5 (17967+((h/195+packedAt s5K5 (15822+(h % 195)*11) 11) % 1029)*11) 11
  | 4 => packedAt s5K4 (15662+((h/126+packedAt s5K4 (14402+(h % 126)*10) 10) % 665)*10) 10
  | 3 => packedAt s5K3 (1113+((h/7+packedAt s5K3 (1078+(h % 7)*5) 5) % 29)*6) 6
  | 2 => packedAt s5K2 (183+((h/1+packedAt s5K2 (180+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83ff8f07e3ffe1f1e3f8fc0f1c07ff873c33f
  | 1 => 0x7fc3ffff803fffe01fc7f1fffe007ff98c7c3f
  | 2 => 0x7ffc00ffffc1f1ffe007fe00ffff8e060f8fcc
  | 3 => 0x800000fffffe01fffff80000fffff007f00ff0
  | 4 => 0xffffff00000001ffffffffff00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa9051131054a0070a0a82485045135031c315
  | 1 => 0x1108a0200c88406004411086a20a24a0841c2a
  | 2 => 0x20893245240d02a92005a412349308320e854c
  | 3 => 0x532c48a4820655256900024c92c40c5d00ab0
  | 4 => 0x4623000c7131899c99264938003001076b6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888feecf888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36268
namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5005fe54017f55005fc5400ffd4c03fe5300ff54c03fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc52007fd0801fe42007f50801fc4200ffcc803fe3200ff4c803fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff0821001ffe2108003f71084007fd884200bffd951005dfeca880037f65440013fb2a200bff99510015fcca8802ffd65440177eb2a200bff19510015f8ca8802f7c65440053e32a2000ffd9110005fec888003bf64440015fb222000ff9911004dfcc888003fd64440017eb222000ff1911004df8c888003bc64440015e322200bffd511005ffca88802ffd5444017fe2a2200affd8d10055fec68802bfe63440037f31a200aff58d10055fac68802bfc63440037e31a200affd4d10057fca68802bfd5344015fe29a200affd0d10057fc868802bfd4344015fe21a2000ffd8910005fec488003fe62440117f3122000ff58910005fac488003fc62440117e312200bffd491005ffca48802ffd5244017fe2922000ffd0910007fc8488003fd4244001fe212200affcc910057fc648802bfd3244015fe192200bffd451001ffca28802ff65144017fea8a200bfd5451001ff8a288003ff4144007ff20a2000ff5051001ff8828802bff3144007ff18a200aff4c51001ff86288003ff2144007ff10a2000ff4851001ff8428802fff5044017ff282200bff5411005ff8a088003ff4044001ff2022000fe90110007fa8088003f94044001fe202200affcc110057fc608802bfd3044015fe1822000ffc8110007fc4088003fd2044001fe1022003ffc411001ff62088003fe1044001fb0822004ffd941001dfeca0800ffe65040057f3282003df99410014fcca0800ffd650400d7eb282003df59410004faca08013fc65040077e3282004ffd901001dfec80800ffe64040137f3202003ef990100057cc80800ffd64040017eb202003ef590100057ac808013fc64040077e3202006ffd5010037fca80801bfd540400dfe2a02004ffd8c1001dfec60800ffe63040037f3182003f798c1000dbcc60800ffd630400b7eb182003f758c10005bac608013fc63040077e3182005ffd4c1002ffca608017fd530400bfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd881001dfec40800ffe62040117f3102003fb98810005dcc40800ffd62040017eb102003fb58810005dac408013fc62040077e3102006ffd4810037fca40801bfd520400dfe2902000ffd0810007fc8408003fd4204001fe2102005ffcc81002ffc6408017fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff0841003dfcc00801bff5004009ff2802006ff54010027f8a008003ff4004009ff2002000ff50010027f88008017ff3004009ff1802005ff4c010027f86008003ff2004009ff1002000ff48010027f8400800fff1004007fb8802004ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3fe61080077f3084008ff58420005fac210013fc6108021ffa884010ff94420087faa210043fc5108001ffa084000ff90420007fa8210003fc410801fff988400fff8c42007ffa621003ffc3108011ff9084008ff88420047fa4210023fc21080237f3004010ffd4020027fca010043fd5008009fe2804000ffd0020027fc8010003fd4008009fe200400fffcc020027fc601003ffd3008009fe1804008ffc8020047de4010013fe2008011fd1004008ff48020007da4010023f92008007ffb2e2003bfd971001ffccb8800afe65c4007feb2e200ebf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988026fe64c4007feb262000bf5931001ff8c98800efc64c401dffaa6200eff95310077faa98803bfc54c4007ffb1e2003bfd8f1001ffcc788006fe63c4007feb1e200dbf58f1001ff8c78800efc63c401bffa9e200dff94f1006ffaa788037fc53c401bffa1e200dff90f1006ffa8788037fc43c4007ffb162003bfd8b1001ffcc588022fe62c4007feb162000bf58b1001ff8c58800efc62c401dffa96200eff94b10077faa58803bfc52c4001ffa162000ff90b10007fa8588003fc42c401bff996200dff8cb1006ffa6588037fc32c4007ffa8e2003ff9471001feca38800ffd51c401dfaa8e2003ff1471001ffe838800ffe41c4007fea0e2003ff1071001ffe638800ffe31c4007fe98e2003ff0c71001ffe438800ffe21c4007fe90e2003ff08710077fea18803bfe50c401dfea86200eff14310007fe8188003fe40c4001fea062000ff1031006ffe6188037fe30c401bfe986200dff0c310007fe4188003fe20c4001fe9062000ff08310027fecb08032ff6584019ff32c2002bf99610067facb08032fd6584009fe32c2002bf19610027fec908002ff6484001ff3242009bf99210007fac908002fd6484009fe3242009bf19210067fea908033fe5484019feaa4200cff15210027fec70801eff638400fff31c2001bf98e1003ffac70801efd6384009fe31c2001bf18e1003ffea70801ffe538400ffea9c2007ff14e1003ffe870801ffe438400ffea1c2007ff10e10027fec508002ff6284001ff3142008bf98a10007fac508002fd6284009fe3142008bf18a10067fea508033fe5284019fea94200cff14a10007fe8508003fe4284001fea142000ff10a1003ffe650801ffe328400ffe9942007ff0ca10055fac308033ff5184007ff28c200cff5461001ff8a308003ff4184007ff20c2000ff5061001ff8830801fff3184007ff18c2007ff4c61001ff86308003ff2184007ff10c2000ff4861001ff8430800efe6084019ffa842004ff94210067faa108013fc5084001ffa042004ff90210007f48108003fd4084001fca042004ff1021003ffe6108013fe308400ffe9842004ff0c210007fe4108013fe2084001fe9
  | 2 => 0x200a7faa910053fc5488009ffb1c4011bfd8e2008ffcc710006fe6388023feb1c4011bf58e20027f8c710006fc6388023ffa9c4011ff94e2008ffaa710047fc5388023ffa1c4011ff90e2008ffa8710047fc43880257eb144014ffd4a20047fca510053fd5288011fe2944000ffd0a20047fc8510003fd4288011fe2144011ffcca20047fc6510047fd3288011fe1944004ffd8620007fcc31000efe6188001feb0c4000bf58620027f8c310053ff5188029ff28c4014ff546200a7f8a310003ff4188001ff20c4000ff50620007f88310047ff3188023ff18c4011ff4c62008ff86310023ff2188001ff10c4000ff48620047f84310022fe6088029ffa844004ff942200a7faa110013fc5088001ffa044004ff90220007fa8110013fc4088023ff9844004ff8c22008ff46110047fd3088023fc9844004ff0c220047fe4110003ef2088011fd9044013ffd952009dfeca900037f65480013fb2a4013ff99520015fcca9004ffd65480277eb2a4013ff19520015f8ca9004f7c65480053e32a4000ffd9120005fec890003fe64480137f3224000ff59120005fac890003fc64480137e3224013ffd512009ffca89004ffd5448027fe2a24012ffd8d20095fec690003df63480016fb1a4012ff98d2000dfcc69004bfd63480257eb1a4012ff18d2000df8c69004bdc63480036e31a4012ffd4d20097fca69004bfd5348025fe29a4012ffd0d20097fc869004bfd4348025fe21a4013ffd4920047fca49004fee5248027fea924013fb54920047f8a490003ff4248011ff2124000ff50920047f8849004bff3248011ff1924012ff4c920047f86490003ff61480017fb0a4000ff98520007fac290003fc61480077e30a4013ffd452009ffca29004ffd5148027fe28a4000ffd0520007fc8290003fd4148001fe20a4012ffcc520097fc629004bfd3148025fe18a4008ffc8520007de4290003fe2148001fe90a4000fb48520047f8429004fff5048027ff2824013ff5412009ff8a090003ff4048001ff2024000ff50120007f8809004bff3048025ff1824012fe8c120097fa609004bf93048025fe1824008ffc8120047f64090003fe2048001f71024004ffd9420045feca10023fe65080057f3284008ff59420085faca10013fc65080117e3284004ffd9020045fec810023fe64080137f3204008ff59020005fac810013fc64080117e3204010ffd5020087fca810043fd5408021fe2a04004ffd8c20045fec610023fe63080037f3184008ff58c2007dfac610013fc63080117e318400fffd4c2007ffca61003ffd530801ffe298400fffd0c2007ffc861003ffd430801ffe2184008bf98820047fea410023fe5208011fea904008ff14820047fe8410023fe4208011fea104008ff10820047fe6410023fe3208011fe9904008ff0c820027fec21002
  | 3 => 0xe30a801bffd45400dffca2a006ffd5150037fe28a8009ffd05400077e82a0003fe4150001fea0a8000ef5054004ff882a006bff3150035ff18a801aff4c5400d7f862a0003ff2150001ff10a8000ff48540007f842a006fff5050037ff282801bff541400dff8a0a0027ff4050013fda028000ff901400077c80a006bff3050035ff182801aff4c1400d7f860a0013ff65100137fb288009ff99440015fcca20027fd65100317eb288004ff1944004df8ca20026fe6410013ffaa08009ff9504004ffaa820027fc5410009ffb188009bfd8c4004ffcc620006fe6310013feb188017bf58c40027f8c620006fc631002fffa988017ff94c400bffaa62005ffc5310013ffa188009ff90c4004ffa8620027fc4310009ffb108009ff98840045fcc420027fd62100017eb108004ff188400c7fea420063fe5210031fea908018ff1484004ffe8420027fe4210013fea108009ff108400bffe642005ffe321002ffe9908017ff0c840027fec220027fe61100077f3088009ff58440005fac220013fc6110031ffa888018ff944400c7faa220063fc5110013ffa088009ff904400077c8220027fd4110013fe2088009ef104400bffe622005ffe311002ffe9888017ff0c440007fe4220003fe2110001fe9088000ff084400cdfcc020063ff5010009ff2808018ff54040027f8a020027ff4010013dfa008004ff9004004ff48020027fd4010001dea008009fe500400bffe6020013fe301002ffe9808004ff0c040047fecb90022ff65c8011ff32e4002bf99720047facb9005afd65c8011fe32e4008bf19720047fec990022ff64c8011ff3264009bf99320047fac990002fd64c8011fe3264008bf193200b7fea99005bfe54c802dfeaa64016ff15320047fec790022ff63c8011ff31e4001bf98f20047fac790056fd63c8011fe31e4008bf18f200affea790057fe53c802bfea9e4015ff14f200affe8790057fe43c802bfea1e4015ff10f20047fea590023fe52c8011f72964008ff54b200b7daa590023fc52c8011ffa164008ff90b20047fa8590023fc42c8011ff9964008ff8cb20047fa6590023fc32c8011ffb0e4008ff9872001dfcc390023fd61c80017eb0e4008ff187200b7fea39005bfe51c802dfea8e4016ff14720007fe8390003fe41c8001fea0e4000ff107200affe6390057fe31c802bfe98e4015ff0c720047fe4390023ef21c8011ff10e4008ff48720007da4390023fc21c802dffa864016ff943200b7faa19005bfc50c8001ffa064000ff90320007fa8190003fc40c802bff9864015ff8c3200affa6190057fc30c8009ffb2c4014bfd96200a7fccb1000afe6588029feb2c4014bf59620027f8cb1000afc6588009ffb244000bfd9220007fcc910026fe6488001feb244000bf59220027f8c910026fc6488029ffaa44014ff952
  | 4 => 0x87ffc3008413ffb2e8009bfd974004ffccba000afe65d0013bf32e80029f9974004ffacba007afd65d0013beb2e80009f5974004ff8cba0026fc65d0013ffaa68009ff9534004f7ca9a0027fd54d003ddeaa68009ff1534004ffec7a0026ff63d0013ff31e8001bf98f4004ffac7a0076fd63d0013fe31e8001bf18f400effea7a0077fe53d003bfea9e801dff14f4004ffe87a0027fe43d0013fea1e8009ff10f4004ffec5a0027fe62d00117f3168009ff58b40005fac5a0027fc62d003dffa96801eff94b400f7faa5a007bfc52d0013ffa168009ff90b4004ffa85a0027fc42d003bff996801dff8cb400effa65a0077fc32d0013ffb0e8009ff9874001dfcc3a0027fd61d00017eb0e8009ff187400f7fea3a007bfe51d003dfea8e801eff1474004ffe83a0027bf41d0013ff20e8009ff507400077a83a0027fc41d003bff98e801dff8c7400effa63a0077fc31d0001ff90e8000ff88740007fa43a0003fc21d003dffa86801eff943400f7faa1a007bfc50d003bff986801dff8c3400effa61a0077fc30d0009ffb2c801cbfd96400e7fccb2000afe6590039feb2c801cbf59640027f8cb2000afc65900357eb24801cffd524004ffca920073fd5490013fe2a48004ffd8e400cdfec720067fe63900037f31c8019ff58e400cdfac720013fc63900037e31c8019ffd4e400cffca720067fd5390033fe29c8009ffd0e400cffc8720067fd4390013fe21c8004ffd8a40007fcc520022fe6290001feb148000bf58a40027f8c520073ff5290039ff294801cff54a400e7f8a520027ff4290001ff2148000ff50a4004ff88520067ff3290033ff1948019ff4ca400cff86520013ff6190001ff30c8003bf98640007fac320002fd6190009fe30c801cffd46400e7fca320073fd5190039fe28c8009ffd0640007fc8320003be4190001fea0c8009ff10640007788320067ff3190033ff18c8019ff4c6400cff86320003ff2190001ff10c8000ff48640007f84320026fe6090039ffa848004ff942400e7faa120013fc5090013ffa048000efd024004ff68120067ff3090009ff1848019ff4c240027f8612006fff65500377fb2a801bff99540015fccaa006ffd65500377eb2a801bff19540015f8caa006fff5450013ff2a2801bef951400dffaa8a006fbd5450013fe2a2801affd8d400d5fec6a006bfe63500037f31a801aff58d400d5fac6a006bfc63500037e31a801affd4d400d7fca6a006bfd5350035fe29a8009ffd0d400d7fc86a006bfd4350013fe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940045f8c4a006fff5250037ff292801bff549400dff8a4a0027ff4250001ff2128000ff5094004ff884a006bff3250035ff192801aff4c9400d7f864a0003ff61500017fb0a8000ff98540007fac2a0003fc61500077
  | 5 => 0x8e2101fbac710802dd6388407fe31c4203bf18e2111ffea71088ffe5388447fea9c4223ff14e2111ffe871088ffe4388447fea1c4223ff10e2110dfac510893ff5288411ff2944224ff54a21047f8a510803ff4288411ff2144200ff50a21047f8851088fff3288411ff1944223ff4ca21047f8651080efe6188407ffa8c4203ff9462101ffaa31080ffc5188407ffa0c4203ff9062101ffa831080ffc4188407ff98c4203ff8c62101fec631080ffd3188447fa98c4203ff0c62101ffe431080fef2188411fb90c4203ffd822101ffcc110802fe6088407feb044200bf5822101ff8c110893ff5088449ff2844224ff54221127f8a11088fff3088447ff1844223ff4c22111ff8611088bff65484457fb2a4222ff99521015fcca9088bfd65484457eb2a4222ff19521015f8ca90803ff64484017fb224200ff9912104dfcc890803fd64484017eb224200ff1912104df8c89088bff5448445ff2a24222ff55121117f8a890887ff63484437fb1a4221ff98d2100dfcc690887fd63484437eb1a4221ff18d2100df8c690887ff5348443ff29a4221ff54d2110ff8a690887ff4348443ff21a4221ff50d2110ff8869088bff5248411ff2924222ff54921047f8a490803ff4248411ff2124200fb90921007fa8490803ed4248411fe2124221ffcc921047fc6490887fd3248411fe1924222ffd452101ffca29088bfd5148407fe28a4200ffd052101ffc8290803fd4148407fe20a4221ffcc52101ffc6290887f63148443fe98a4221fd4c52101ff86290823ff2148411fb90a4203ff8852101fdc4290803ff60484017fb024200ff98121007fac090803fc60484017e3024222ffd4121117fca09088bfd5048445fe2824221ffcc12110ffc6090887fd3048443fe1824203ffd942101dfeca1080ffe65084057f3284203ff59421105faca1080ffc65084077e3284203ffd902101dfec81080ffe64084137f3204203ff59021005fac81080ffc64084077e3204220ffd5021107fca810883fd5408441fe2a04203ffd8c2101dfec61080ffe63084037f3184203ff58c210fdfac61080ffc63084077e318421fffd4c210fffca61087ffd530843ffe298421fffd0c210fffc861087ffd430843ffe2184208bf98821047fea410823fe5208411fea904208ff14821047fe8410823fe4208411fea104208ff10821047fe6410823fe3208411fe9904208ff0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084208fd4842101ffec01080ffe60084017f3004203ff58021005fac01080ffc6008441ffa804220ff94021107faa010883fc500843fff980421fff8c0210fffa6010
  | 6 => 0x7df20a8229ffcc54101ffc62a08a7fd3150407fe18a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08abff5050455ff282822aff54141157f8a0a08a7ff3050453ff1828229ff4c14114ff860a080fff65104077fb288203ff99441015fcca2080f7e65104053f3288203ff59441145faca2080f7d65104013eb288203ff1944101df8ca20826fe6410413ffaa08209ff9504104f7ca820827fd5410451deaa08209ff1504101ffec62080eff6310407ff3188201bf98c4101fbcc620806de6310407feb188227bf58c4101fbac620802dd6310407fe3188203bf18c4113ffea62089ffe531044ffea988227ff14c4104ffe8620827fe4310413fea188209ff10c4101ffec42080ffe62104117f3108203fb98841005dcc42080ffd62104017eb108203fb58841005dac42080ffc6210451ffa908228ff94841147faa4208a3fc5210413ffa108209ff9084104ffa8420827fc421044fff9908227ff8c84113ffa642089ffc32104077f3088203ffd444101ffca22080ffd5110407fe2888203ffd044101f7e822080ffe4110407fb2088203ff5044101f7a8220827f54110407ff9888203ff8c44101ffa622080ffc3110407ffb008203ff98041005fcc02080ffa60104017d3008203ff58041005fac02080ff960104017cb008203ff18041147fea0208a3fe5010451fea808228ff1404113ffe602089ffe301044ffe9808227ff0c041047fecb90822ff65c8411ff32e4202bf99721047facb9089afd65c8411fe32e4208bf19721047fec990822ff64c8411ff3264209bf99321047fac990802fd64c8411fe3264208bf19321137fea99089bfe54c844dfeaa64226ff15321047fec790822ff63c8411ff31e4201bf98f21047fac790896fd63c8411fe31e4208bf18f2112ffea790897fe53c844bfea9e4225ff14f2112ffe8790897fe43c844bfea1e4225ff10f21047fea590823fe52c8411fea964208ff14b21047fe8590823fe42c8411f72164208ff50b21007da8590823fc42c8411ff9964208ff8cb21047fa6590823fc32c844dffa8e4203ff94721137faa39080ffc51c8401ffa0e4203ff90721007fa839080ffc41c844bff98e4203ff8c72112ffa639080ffc31c8411ffb064208ff98321005fcc190823fd60c84017eb064208ff18321137fea19089bfe50c844dfea864226ff1432112ffe6190897fe30c844bfe9864225ff0c32101ffecb1080eff6588407ff32c4202bf9962101efccb1080a7e6588407feb2c4224bf5962101efacb108027d6588407fe32c4203bf1962101ffec91080eff6488407ff3244209bf9922101ffac910802fd6488407fe3244203bf19221127fea910893fe5488449feaa44224ff1522101ffec71080eff6388407ff31c4201bf98e2101fbcc710806de6388407feb1c4223bf5
  | 7 => 0x21023fd61108017eb088408ff18442187fea2210c3fe5110861fea888430ff1444217ffe62210bffe311085ffe988842fff0c442047fec021023fe60108017f3008408ff58042005fac021023fc6010861ffa808430ff94042187faa0210c3fc501085fff980842fff8c04217ffa60210bffc3010813ffb2e8209bfd974104ffccba080afe65d0413feb2e822ebf5974104ff8cba0826fc65d0413ffaa68209ff9534104ffaa9a0827fc54d0413ffb1e8209bfd8f4104ffcc7a0806fe63d0413feb1e822dbf58f4104ff8c7a0806fc63d045bffa9e822dff94f4116ffaa7a08b7fc53d0413ffa1e8209ff90f4104ffa87a0827fc43d0413ffb168209ff98b41045fcc5a0827fd62d04017eb168209ff18b41177fea5a08bbfe52d045dfea96822eff14b4104ffe85a0827fe42d0413fea168209ff10b4116ffe65a08b7fe32d045bfe996822dff0cb41177fea3a080ffe51d045dfea8e8203ff1474116ffe63a080ffe31d045bfe98e8203ff0c74104ffec1a0827fe60d04017f3068209ff58341005fac1a0827fc60d045dffa86822eff94341177faa1a08bbfc50d045bff986822dff8c34116ffa61a08b7fc30d0407ffb2c8203bfd964101ffccb2080afe6590407feb2c822cbf5964101ff8cb2080efc65904537eb24822cffd524104ffca9208b3be5490459feaa4822cef5524104ff8a92080fff63904077fb1c8203ff98e4100dfcc72080ffd63904577eb1c8203ff18e4101df8c7208afff5390457ff29c822bff54e4115ff8a720827ff4390457ff21c822bff50e4104ff8872080fff6290407ff3148208bf98a4101ffac520802fd6290407fe314822cffd4a41167fca5208b3fd5290459fe2948209ffd0a41007fc8520803fd4290413fe214822bffcca4115ffc65208affd3290457fe1948203bf9864101ffea32080ffe5190407fea8c8203ff1464101ffe832080fbf4190413fba0c8203ffcc64101ffc632080ffd3190407fe18c8203ffd824101ffcc120802fe6090407feb048200bf5824101ff8c1208b3ff5090459ff284822cff54241167f8a1208afff3090457ff184822bff4c24115ff861208abff65504557fb2a822aff99541015fccaa08abfd65504557eb2a822aff19541015f8caa08abff5450413ff2a2822aff5514104ff8a8a08a7ff63504537fb1a8229ff98d4100dfcc6a08a7fd63504537eb1a8229ff18d4100df8c6a08a7ff5350453ff29a8229ff54d4114ff8a6a0827ff4350453ff21a8229ff50d4104ff886a0803ff62504017fb128200ff98941007fac4a0803fc62504117e312822affd4941157fca4a08abfd5250455fe2928209ffd0941007fc84a0803fd4250413fe2128229ffcc94114ffc64a08a7fd3250453fe192822affd454101ffca2a08abfd5150407fe28a8209ffd054104fee82a080ffe415040
  | 8 => 0xf58742005fac3a1027fc61d086dffa8e8436ff947421b7faa3a10dbfc51d086bff98e8435ff8c7421affa63a10d7fc31d0813ffb068409ff98342005fcc1a1027fd60d08017eb068409ff183421b7fea1a10dbfe50d086dfea868436ff143421affe61a10d7fe30d086bfe9868435ff0c342047fecb21022ff6590811ff32c8402bf99642047facb210d2fd6590811fe32c8408bf1964218dfac9210d3ff5490813ff2a48434ff5524204ff8a921023ff63908117fb1c8408ff98e4200dfcc721023fd63908677eb1c8408ff18e42045f8c7210cfff5390867ff29c8433ff54e4219ff8a721027ff4390867ff21c8433ff50e4204ff88721022fe6290811ffa948408ff94a42047faa521023fc5290811ffa148408efd0a4204fde8521023ff3290811ff1948408ff4ca42047f86521023ff6190811ff30c8403bf98642047fac321002fd6190811fe30c8434ffd46421a7fca3210d3fd5190869fe28c8433ffcc64219ffc63210cffd3190867fe18c8408ffd8242047fcc121002fe6090811feb048400bf58242047f8c1210d3ff5090869ff2848434ff542421a7f8a1210cfff3090867ff1848433ff4c24219ff861210cbff65508657fb2a8432ff99542015fccaa10cbfd65508657eb2a8432ff19542015f8caa10cbff5450813ff2a28432ef95142197faa8a10cbbd5450813fe2a28431ffd8d4218dfec6a1003df63508016fb1a8431ff98d4200dfcc6a10c7fd63508637eb1a8431ff18d4200df8c6a10c7dc63508036e31a8431ffd4d4218ffca6a10c7fd5350863fe29a8409ffd0d4218f7e86a10c7fe4350863fea1a8431ef50d4204ff886a10cbff5250811ff2928432ff54942047f8a4a1027ff4250813f7a128408ff909420477c84a10c7ff3250811ff1928431ff4c942047f864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508077e30a8432ffd4542197fca2a10cbfd5150865fe28a8431ffcc54218ffc62a10c7fd3150863fe18a8400ffd8142005fec0a1003fe6050801feb028400ff18142005f8c0a10cbff5050865ff2828432ff54142197f8a0a10c7ff3050863ff1828431ff4c14218ff860a1023ff65108117fb288408ff99442015fcca210237e65108053f3288408ff59442185faca210237d65108013eb288408ff19442045f8ca21026fe6410813ffaa08409ff9504204ffaa821027fc5410811ffb188408bfd8c42047fcc621006fe6310811feb18842fbf58c42047f8c621022fc631085fffa98842fff94c4217ffaa6210bffc5310813ffa188409ff90c4204ffa8621027fc43108117f3108408ffd4842047fca421023fd5210811fe2908408ffd08420477e8421023fe4210811f72108408ff508420477a8421027ed4210811ff9908408ff8c842047fa6421023fc3210811ffb088408ff9844201dfcc2
  | 9 => 0x2800000f04400000000a00200e00200201000700900000000200000600101500200802c00000000000705a00000100000a00300000000100100000000100502700200200200000100100700800000200300700600002100900200700000100e00500300600000203d00200000004900d00000e00401c00601400102701800000401800a00800100700300101b00a00000102f00002100000300000000200300900100000100000100201e00603000700300100200b00301d00000101100100000900300000200402400600300400101200300201c00200400000600600a00200401200500202700400c00000300200100503b01300000700200101d00800100000600e00d00f00200200702803f00100000206800000100b01901700700202200000000000001200400001000400101d0080180cb00000100b02c00000000400004d00500300400800000000b00400300b00000000000001500700000002700b00700200000101800802400100403b01600000100200900702a00000d00100f00800d00e00100c00301500203100100000a00000500101c00a00000800600000000a00500200500000200a00100200500000800601200300000f00400c02300400300800900201e00600000200000800000300700800100700206a00200502200d00200000c00100000700600b00400000000000000700300000d00205600a00902100d04500700000000200200000400d00100401103700201103a03c01400500401e00100000200d00c00000101d01a00401900200100500000000500400500700102905500202200001500200c00600101e00701300600000100003900900501c00100400101206000200100400000900100b00100300700000000000501b03300000000300101600000000e01500b01200d04600100b01501902100a00100200200300600000100201100907801800000b00000001600000900100901a01d00700400000000600503c01802d00200100100c00000500000a00600000c00400400000701c00000100400000100300100000400901200004000000002000600102900202b00401003700200001e01000000100100201900000001d00800800800000000100a00700101301b00d00e00000500400004ffecba1026ff65d0813ff32e8402bf9974204ffacba10dafd65d0813fe32e8409bf1974204ffea9a1027fe54d0813df2a68409ff553421b77aa9a1027fc54d0813ffb1e8409bfd8f4204ffcc7a1006fe63d0813feb1e8435bf58f4204ff8c7a1006fc63d086bffa9e8435ff94f421affaa7a10d7fc53d0813ffa1e8409efd0f4204ffc87a1027fd43d086bdea1e8409ff10f421b7fea5a1023fe52d086dfea968408ff14b421affe65a1023fe32d086bfe9968408ff0cb4204ffec3a1027fe61d08077f30e8409f
  | 10 => 0xb2e1ea4037c2c8a36d584202d45967183e2282000496d7ca022fad5ceccad0148e8ae86132024654c2252a9d0298b349e81fc14a7681accc891287c9783402427b49d81c09b27ccad87805449a667c3c891892ac686e06143f6fdcb7208a0000005fc88ee5ad38070e02f5839a556f8c01aef634c0004ace329fc336a72ed470079e0009f4030c609b60008120000000000000000d2000c480007eea26e70620000604400b580006d82e80003108545542dc4a85360008ccaf879c1d4c3a29e060000520c12886f9211a58e000aa474cd6a386000b521ba6dad78a826081744e4314a0aa4e538000000000d6ccfeae6000dd0c84c3e000f1665ee9eb8c0000006f86ee000692000d3ee8eed8434e3485e00069c7f48880009c0e608780000003c65e864cf0815000093871c77a000000b5cdcc51eb900000000000003f82066c289800000072406e0000000f43e84bc00056423a97e88afd22f46d600000093e000000a2c0aa4803b2c4ede022256e1d6f000003e0000ed6000cac70c0003dc000a289266f6000b62000000c5a882758d98bc084eb98694ca4000844000e24bf292026200046883aa7c2a41be928192000130deebca1bcc180000007920f2d8ada844eeee8b4ba4b10e04f7abb4756304fd40005a203200034e000690470ea4a324f8fd6d9e64aa048facaeedeba8fca0005f03c08f096c30882a80a246eae00022c000622884cc48109985668024be3a803a00043a000b1a000790000fa2fce4ae00035619689054cf86bee106000df08b200000cc1aece6708aa5426d20e0a645e400062aa502704a620c000f4274e0009f20009340000ec2f24589248bc00054a0000008665928c8000a7e000a46280abe000362f14fb0046b0a8e000085a7f2000fd04e68b8000cbc23c05c0e4296236000764ee0c067daf6e38263af66b18be64a0ce0c1c5bc908000a3c3d43bc000000000510138e143f2b5000000068e00065a6b03be832734000b4a37a0006684ecf4ed90acac924fed365a8b6cce8e1cae09ca1081d03a666ea06c783d021e41a9cc5ee224fb275471687ea0c0dcb08946ba682c1f69929bc7668e2322054d9659016c75e7a4ec2f5ce166e8bec0500f05c651a0de042cba0eeec06306346ae98435ecd0084dda73064ee7266c00000200900304002f00600700000100400002400001f01001e00702106700001d00801401000000100200300400502e00200100000000100000b00200104701002e00000300600900b0c200100000100201400a01e00000600301600102200400000302201500400000200700900302500300000000200900200600500b01200d00300800100000600000e00200000301302200200c02100500100100301101c00700100000200400200f00000100a00700000001c000018006018000000005020
  | 11 => 0x6000000d1400000000094a000b920000007084b0c6400056cdc06fe000000000fe49e69e04c6000f6ad1e0000000000008640ca92e500000a10a3e04412ee2e472e82360092fe0000ee6000e40000f500000000000000006382685aad1a00032e9c4848000278c162b2074a422486b4e1800073e136c1edb6000000eda000f189526c46f2f0a000906a88000ac8e0800076093cf2e6ca6e43cce10a8686ed1c78ed4671023e4025f2104b60e3edfc574000000000000000000dc68f4e68000000000000994162fae00e974f72e3083653c0f6eb49907a20005d8d041e0bf8cd2ea200040c288d88d9c720440a62b4e8be01e54e762492000b48910f1a33a5e6b0610e000000000128272a5400052c0007b67f61e8000000000036226594352b7ad24000000e46954a48000c28db8000a1ab3a9bee120fc000a787ca4181408281b6fba194e1aae2000d06626072bea75a000000fc6d08000000bf6438fc2000000f7800076e7d2b642bab389163ca5c85700000004c8ab41f4000000b9c000078b041a2f440007acc4400000000028a00020aa8accc57a6e6b78cc28de4c41dcd00648f46324d4e2f00002764d0be2e4819845c5ae2586f04f08f884ce7c49cd18d824ee31a7780b00aeda294476c006bfe182d268503b6c769aa274000f84430cf0dba488cf83fa252e7e6fa17a490d023b85d6698900b147e241406c64688c44c36cc94b4072a5a699a5e0ab2e545861a6202abac8caea69ae524dc12c8146bc0642e04fca206621f005a348d94cb226438a4540d838018641242e00022ab169367def5e428320000338a7a8fc722ef41d8110fa09b47bcc306b2dead54d62658118076d70c4a232f3a5fadbc4f41ee2c00000006c632a8cece4448000dbe860cd60c0adcc0019aeb8fa4bbaea00ace9402c20081a7dc86c152b8201cfda0343b40e861c7044827702ce59e21650e04a350366f7ca8ceace4e2ea5d291e06a000a98582e804646965ba90e4d8b42606aceea69bafc80007466a0624d7a63e25eb1242c124000902516398aae0c44d6568c0e0889821a0a0eaa64c05525c200058067ae5613c284e6cbccc6c8d4f24000000000a00fb8f0600000040ef381b49300d618efe2000000000000c5248af9659c000000d8479821ae20fa85b61eaca0424cb4fe6000c7c4f2f10af65f4f82e220005080002a878873a00000099ef54cf6000c36000bac0be8380007a8000750932000f28426000000000cbe0000000008e63e600000018cbbc9ea134c80f30ee2df469ed400009a270e254b884608b68ba00012015cc5ce62eea5241588220009d2000a740d4000bb62c46c810aa8ea9a04cceeb9ec8a47c96ea7677ebc636846c0c29e21c261217660ece6f0e1645cedca11e4d27a057cf22b36cd46406d0daa7c46de8daf740562d0782a807bad
  | 12 => 0xd9a000000000000000000000000000e2800083e77cc2e6567c23061e4028b76eec51c3440005ca7f09c24aa000d560007060000000bce849c6ce200000030a00000032c000014ada000820c98dce618cd8266000012000b80000862da4330b54000ade000faa9f0bb8d0c00050a000bfacc686a70af8e808c56aaa85800055c00081c3740a08eaf6c000eb08a20006864b41220004844768740006ce2fc02e0b68d8000000784576a2a83c894080000478904e3ad8c4ccbb08b0cec90c0862aec385e209a6ecf9adac8d6396b3c24c6a491a8520009eec9e00000024eed09726d4238678442960d8000000005e000facebabc2dd6292220436ae4000000b1eda038471a9f6000000000bf43183c48187f80ba8e848c1a4af4726786fb6684b8a8c065c090540212208d608fe3de0000000040003a039047e16a0ea29ae3c9805dc34a54824495cb5ab1cf9800044459a000260000afe996cb0de25303723fc474184fa609e7d44043ec9660fa0006824663ac0003a4bf0d3a5dedd853200041c07c000c6e000f021dadaec6a11487224a2be6f4e5c07e45002246e5042a67941c693ade433e8041a81e2000000000f3cdfabd0c7a1f82565a4eaacce5b0000cca000a168d2c08eb66107364fae749dca346a200018804800098cf8016e956364a5ca940003c20000007fe4987745f66a8b025ec97cc9cd529a845222eec82cc9f855af4ac7e4a2000bc400063c000e00be8000b0e89ee6a1fef4c5b200019ccdc4c21547e0f76d3456a6dc5daca29b0accc1497a52e17efc0572ca84b22b63aa4ca0628a62ee98ae9058a3a20004e01807fc2a27be0a4660f1e82e388b6e3b0e78dec2de49e2a0cf400060a07ad2c41efbed4ab5ed76b4ce0a21c61e9a47e628cc20d16066f48f62d30fc49641905beb0038c2e6526b709feceaa4c5121449700388e4d6e13aae8c344320201ce7e833c6a6f568a4e92664f60cde3541fa2da000d28f70edcb26ee4b56000aec00000068a2b4000e4a2ca0000d0000a3ae9c60c628efc000000000c66b86598a9610cf8a9428ac6cc7b0b0c7d63f4c2c204c5e7a6a5e79a0f817c5fe976abc392b66000d4837000226c674000546d5e0001ae112a56876c0ae7608ee8c3ae12a1d2f2cf3ed6830e39e0000000828963ea00003ef68000dc8b7e8c2740230b2475c0cc0a23fe00058c000c5035a68084200009495e72c0004e2ed2000c821c476a7e4c02000fd81600000007ea29c62e7721dec5878cafcbaa000b68178eca32643c8065a0000be0522af0000f9000094c4f6ac2c2a0001ca20e53a6eaa242f8742b4431ed3c8ee6885eaa84b9691cdf2f5abc8bb20ce000562000e5eb7c000c409d636e4ba7445144e87c814c000000748cf29888ae4069ce558a600000005c0c0c100000f9edf673cf12efe000ba227a63
  | 13 => 0x9a091421492cf2a652d643003941b2a66fdeaac39c87a56002a19ea70302bdc35cad608c95a68cec63460406767fa840d1243e6bea58be4de67c02c65d426e65067e3ba15ef34dc23ceac65884b838e61aaf2a90958a9c0526322bc21049aad4d928ecea83d24462ec5f8afaac4ec49c83780a845a068950dd2d3228eef0d503f013e968f0474af889ec40aca64de89a868a141708001ccd5acaaab8e50f36ebc2509d418a96a9dab3266648666af947c69e41e680ce880dac4ce58de8e4c7968a0d0a48ef9c5d0aeebd6168d866ba7b8db42fec721569ac00027ebde00ad2e0002940002ac7aaee890a000a686fc0000001aaf648a8a5a84afb45accb86c05504566ac3765029408c6410856d8e03cd2a44ac74098c88d22830e96dd4358c10ab6a22efa2e2ebe1027d00e25b4d42b30e44e0cc96bd8a382d8a6c506dde00023457862c712e6455ec3cd66ac0b2e8f64ceab0bda2282d20a6c86a92c32000e6e0b41ec4b6a9e7ec126dfe2d6000892d72962000cfc0008ca00025ccb69b8000000986db00e6b8e26ab6abd2e98000000e06bce018644ddcb84000f1c000000c62880f403340000000009fa4ea30cf0c42adf80c8a30d10c70462e0e78a6aac0471e98ed7ea525c4a1e60257e1b0bfcb2af20b3e85c518a6a142218642b2c50c80e816c24a4a04e4947385b85cc3d8922c8eaa2b46016ef27020962b0c9ac464d4cdabd4e3667217231236a00000033299c146000870a1c5287d8824000416000000b74c544227ae6b600031c0009ae6003162b8fcc1160febbe3daa08728d0ed440b2826e6671414e00000094e000a2e000fbc1f2b28b22a6ead2a44000f32aa00008c40003e4000bae834d4cf26000286dc4f5202645e7b2000000cc0000e2a732e7a000ba0342000000000000e38a12000000000000ef80c67766b80102e48d053e00000047a27caa8846328616cfa166c9053400000072e2f6008000000e9a3d63ee752290000d204dad7415a46a2aae2611c94889c0b8240f7e6e21b8e2cb9a000e42584b208f20007ce81eb9400025ac26000eb2a1805840809c9de37e8dc2c24a4da60001c8000000000000c42000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881001eef715881001eee715881001eed715881001eec715881001eef515881001eee515881001eed515881001eec515881001eef415881001eee415881001eed415881001eec415881001eef315881001eee315881001eed315881001eec3158810026ee7058810026ec7058810006ef5058810026ee5058810006ed5058810026ec5058810026ee4058810026ec4058810006ef3058810026ee3058810006ed3058810026ec305881001eef1058810026ee105881001eed1058810026ec105881004cff76d0810024fe76d0810004fd76d0810024fc76d08101b67e65d08100067d65d081004ebe64d0810006bd64d08101aede63d0810006dd63d0810046ee62d0810006ed62d0810044ff7690810024fe7690810004fd7690810024fc76908101a67e65908100067d659081004ebe6490810006bd649081019ede6390810006dd6390810046ee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc76508101967e65508100067d655081004ebe6450810006bd6450810005df735081002ddc735081018ede6350810006dd6350810046ee6250810006ed6250810005f7715081001df47150810044ff7610810024fe7610810004fd7610810024fc76108100357e75108100057d75108101867e65108100067d651081004ebe6410810006bd641081017ede6310810006dd6310810046ee6210810006ed6210810004fd76d00100357e75d00100057d75d00100f67e65d00100067d65d001004ebe64d0010006bd64d00100eede63d0010006dd63d0010006ee62d0010006ed62d0010004ff76500100de7e65500100067d655001004ebe6450010006bd64500100d6de6350010006dd6350010006ee6250010006ed62500101cefa6050010004fd76c80100b67e65c80100067d65c8010006be64c8010006bd64c80100aede63c8010006dd63c8010046ee62c8010006ed62c8010004ff76480100057f75480100357c754801009e7e65480100067d6548010006be6448010006bd6448010005df734801002ddc7348010096de6348010006dd6348010046ee6248010006ed6248010025f77644010006f77644010004f776440100077775440101c7747544010026f765440100277665440101c6f56544010027756544010006756544010007b77444010007b47444010027b66444010027b56444010027d66344010027d56344010027e66244010027e56244010025f7704401001ff37044010026f66044010027f26044010027f230440101bff13044010027f22044010007f12044010
  | 1 => 0x901001ebf215901001ebe215901001ebd215901001ebc2159010026be7059010026bc7059010006bf5059010026be5059010006bd5059010026bc5059010006bf3059010026be3059010006bd3059010026bc3059010026be2059010026bc205901001ebf1059010026be105901001eba105901001ebd105901001eb91059010026bc1059010006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001edf5158c1001ede5158c1001edd5158c1001edc5158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c1002edf7058c10026de7058c1002edd7058c10026dc7058c10006df5058c10026de5058c10006dd5058c10026dc5058c10026de4058c10026dc4058c10026de2058c10026dc2058c1001edf1058c10026de1058c1001edd1058c10026dc1058c10046ef7598810046ee7598810046ed7598810046ec7598810046ef7498810046ee7498810046ed7498810046ec7498810006ef5498810006ee5498810006ed5498810006ec5498810046ef7398810046ee7398810046ed7398810046ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881001eef719881001eee719881001eed719881001eec719881001eef519881001eee519881001eed519881001eec519881001eef419881001eee419881001eed419881001eec419881001eef319881001eee319881001eed319881001eec3198810026ee7098810026ec7098810006ef5098810026ee5098810006ed5098810026ec5098810026ee4098810026ec4098810006ef3098810026ee3098810006ed3098810026ec309881001eef1098810026ee109881001eed1098810026ec1098810004ff7558810014fe7558810004fd7558810014fc7558810004ff745881004cfc7458810004ff735881000cfe7358810004fd735881000cfc7358810024ff7258810026ef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef3258810006ee3258810006ed3258810006ec325881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810044ff7058810024fe7058810044fd7058810024fc7058810026ee2058810026ec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006e
  | 2 => 0x67f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c325941001e7f715941001e7e715941001e7d715941001e7c715941001e7f415941001e7e415941001e7d415941001e7c415941001e7f315941001e7e315941001e7d315941001e7c315941001e7f215941001e7e215941001e7d215941001e7c21594100367f70594100267e70594100367d70594100267c70594100267e40594100267c40594100067f30594100267e30594100067d30594100267c30594100267e20594100267c205941001e7f105941001e7710594100267e105941001e7d10594100267c105941004ebf759901004ebe759901004ebd759901004ebc759901004ebf739901004ebe739901004ebd739901004ebc7399010006bf5399010006be5399010006bd5399010006bc539901004ebf729901004ebe729901004ebd729901004ebc7299010006bf5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bd3299010006bc329901001ebf719901001ebe719901001ebd719901001ebc719901001ebf519901001ebe519901001ebd519901001ebc519901001ebf319901001ebe319901001ebd319901001ebc319901001ebf219901001ebe219901001ebd219901001ebc2199010026be7099010026bc7099010006bf5099010026be5099010006bd5099010026bc5099010006bf3099010026be3099010006bd3099010026bc3099010026be2099010026bc209901001ebf1099010026be109901001ebd1099010026bc1099010004ff7559010014fe7559010004fd7559010014fc7559010024ff7459010026bf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff735901000cfe7359010004fd735901000cfc7359010006bf4359010006be4359010006bd4359010006bc4359010004ff7259010044fc725901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc415901004cff7059010024fe705901004cfd7059010024fc7059010026be4059010026bc405901001efa105901001ef91059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315901001ebe315901001ebd315901001ebc315
  | 3 => 0xc641091001df67110910005f57110910005fa7010910005f97010910004fe76d0510024fc76d05100067f65d05101767c65d0510006bf64d051004ebc64d0510005fa70d0510005f970d051004cfc76505100067f65505101567c6550510006bf645051004ebc6450510005fb7050510005f87050510004fe76c8510024fc76c85100067f65c85101367c65c8510006bf64c8510006bc64c8510006ef62c8510046ec62c8510005fa70c8510005f970c8510044fc76485100067f65485101167c6548510006bf6448510006bc6448510006ef6248510046ec6248510005fb7048510005f8704851001ff0104851001cfe76d011001cfc76d011005d7e75d01100057d75d01100067f65d01100f67c65d0110006bf64d011004ebc64d011001df671d0110005f571d0110004fe76901100067f65901100e67c6590110006bf649011004ebc6490110005fa7690110006fa76901100077b65901101ff786590110205f97490110007bb649011004efa649011004ef86490110007b8649011004eb8649011001dfa719011001df87190110026fb61901101fff251901101fff151901101f7ba41901101f7b8419011004cff7650110004fd765011001cfc76501100067f65501100de7c6550110006bf645011004ebc6450110005f7715011001df4715011001df8765011004ef8765011001cf876501100077b65501101ef786550110007bb7450110007bb645011004efa645011004ef86450110007b864501101efba54501101efb95450110007f3715011001dfa715011001df87150110007f071501101eff251501101eff15150110007bb4150110007b94150110004fe76101100067f65101100c67c6510110006bf641011004ebc64101101e5fa7010110007b9401011001cfe76c811001cfc76c81100067f65c81100b67c65c8110006bf64c8110006bc64c8110006ef62c8110046ec62c811001df671c8110005f571c8110004fe76881100067f65881100a67c6588110006bf6488110006bc6488110044ff7648110004fd764811001cfc76481100057f754811005d7c75481100067f654811009e7c6548110006bf6448110006bc6448110005df7348110055dc7348110006ef6248110046ec6248110005f7714811001df47148110004fe76081100067f65081100867c6508110006bf6408110006bc64081100067f65841100667c6584110006bf6484110006bc648411001dfa708411001efb608411001df67684110026f6768411001cf67684110025f775841101ddf575841100077765841101d7746584110007b76484110007b46484110025f67084110026f7608411001ff36084110027f24084110007f140841100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c7359410
  | 4 => 0x9110006bd6319110006bc6319110007b65119110007b55119110007b9701911020fbb101911020fb8101911004ebf751911004ebe751911004ebd751911004ebc751911004ebf731911004ebe731911004ebd731911004ebc7319110006bf5319110006be5319110006bd5319110006bc531911004ebf721911004ebe721911004ebd721911004ebc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911004ebf711911004ebe711911004ebd711911004ebc7119110006bf511911020ebe5119110006bd511911020ebc5119110006bf311911020ebe3119110006bd311911020ebc311911020ebe211911020ebc211911004ebf701911004ebd701911004eb97019110006bf5019110006be5019110006bd5019110006bc5019110006bf3019110006be3019110006bd3019110006bc301911020ebf1019110006bd101911020ebc1019110044fe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910004ff75d8910014fe75d8910004fd75d8910014fc75d891004cfe74d8910004fd74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d8910006ef32d8910006ec32d891001cfe71d891001cfc71d8910024fe70d8910024fc70d891005d7e75989100057d75989100067f65989100067c6598910005be7498910005bd7498910006bf6498910006bc6498910006ef62989100057f755891005d7c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df7358910055dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891004cfc7458910006bc745891004cbc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910046ee6218910006ed621891004cff76d0910004fe76d0910004fd76d091004cfc76d09100067f65d09101b67c65d0910006bf64d091004ebc64d0910005fa70d0910005f970d0910044ff7690910004fe7690910004fd7690910044fc76909100067f65909101a67c6590910006bf649091004ebc6490910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101967c6550910006bf645091004ebc6450910005df7350910055dc7350910044ff7610910004fe7610910004fd7610910044fc761091005d7e75109100057d75109100067f65109101867c6510910006bf641091004eb
  | 5 => 0x67c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95102167e71d951005e7d71d95102167c71d95102167e41d95102167c41d95100067f31d95102167e31d95100067d31d95102167c31d95102167e21d95102167c21d95102167f70d951005e7e70d951005e7d70d951005e7c70d95100067f30d95100067e30d95100067d30d95100067c30d95102167f10d951005e7d10d95102167c10d951004cfe76d91100067f65d91100067c65d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d9110006bf43d9110006be43d9110006bd43d9110006bc43d9110044fe72d9110004fd72d911001cfe71d911001cfc71d9110024fe70d9110024fc70d911004cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d9110007b651d9110007b551d91101f7bb70d91101f7bb10d91101f7b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d91101f6be71d9110006bd71d91101f6bc71d9110006bf51d91101f6be51d9110006bd51d91101f6bc51d9110006bf31d91101f6be31d9110006bd31d91101f6bc31d91101f6be21d91101f6bc21d91101f6bf70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d91101f6bf10d91101f6bc10d911005d7e75991100057d75991100067f65991100067c6599110006bf64991100057f755911005d7c75591100067f65591100067c6559110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110004ff735911000cfe7359110004fd735911000cfc7359110004ff7259110044fc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911004ebe6419110006bd6419110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be631
  | 6 => 0xc7559210026bf7459210006be5459210006bd5459210004ff735921000cfe7359210004fd735921000cfc7359210004ff7259210044fc7259210024fc7059210026be4059210026bc4059210024ff75d8a10014fe75d8a10004fd75d8a10024fc75d8a1004cfe74d8a10004fd74d8a10024ff73d8a1000cfe73d8a10004fd73d8a10024fc73d8a10026f571d8a10026fa70d8a10004fd7698a10026ef6298a10026ec6298a10044ff7658a100057f7558a100657c7558a10005df7358a1003ddc7358a10026ec6258a10004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067c7558a100147c7558a10004ff7458a1004cfc7458a10004ff7358a10006df7358a10004df7358a1000cfe7358a10004fd7358a1000cfc7358a10006dc7358a1000cdc7358a10026ef7258a10006ee5258a10006ed5258a10024fc7058a10026ee2058a10026ec2058a1004cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a10025fa70d0a10005f970d0a10044ff7690a10024fe7690a10004fd7690a10024fc7690a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10005df7350a1003ddc7350a10005f77150a1001df47150a10044ff7610a10024fe7610a10004fd7610a10024fc7610a100657e7510a100057d7510a10025fa7010a10005f97010a1004ebe64d0610006bd64d0610025fa70d0610005f970d061004cff765061004ebe6450610006bd645061001fb44150610005fb7050610025f87050610046ee62c8610006ed62c8610025fa70c8610005f970c8610044ff7648610046ee6248610006ed6248610005fb7048610025f870486100657e75d02100057d75d0210026bf64d0210026bc64d0210025f97690210026f9769021001cf9769021004efa6490210027ba6490210027b96490210026f8649021001dfa7190210027f27190210027f17190210025f871902101f7ba41902101f7b84190210026bf6450210026bc6450210027b84050210005fb7650210006fb7650210027bb7450210027bb645021004efa645021004ef86450210027b86450210227ba5450210227b9545021001dfa715021001df87150210007bb4150210007b94150210026ef62c8210026ec62c82100057f75482100657c7548210005df734821003ddc7348210026ef6248210026ec6248210025f576c421001ef576c4210026f765c421021ef565c4210027f260c421005d7e76d951005e7e76d95100147e76d95100067f63d95100067e63d95100067d63d95100067c63d95100077771d951005f7471d95102177b10d95102177810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d9510
  | 7 => 0x842000cfe7358420004fd735842000cfc7358420026f77158420006f65158420006f55158420006f63158420006f53158420046f72158420046f4215842001cff7058420046ef2058420026f61058420026f4105842004cff76d0420024fe76d0420004fd76d042004ebe64d0420006bd64d042001cff7690420024fe7690420004fd769042001ef66190420006f56190420004ff7650420004fd7650420024fc765042004ebe6450420006bd645042001ef66150420006f5615042001cff7610420024fe7610420004fd76104200857e75104200057d751042007dde7310420005dd7310420045ee7210420005ed7210420025fa7010420005f97010420004fd76d00200857e75d00200057d75d0020004ff7650020025ef7648020006ef7648020004ef76480200076f75480202376c7548020026ef6548020236ed6548020007cf734802022fcc7348020006ed6148020025ef7048020047eb7048020026ee6048020027ea6048020027ea4048020007e94048020004ff7559310014fe7559310004fd7559310014fc755931001ebf7459310004ff735931000cfe7359310004fd735931000cfc7359310004ff7259310044fc725931001cfc715931001ebe415931001ebc415931001efa105931001ef91059310004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1004cfc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b1001eef7258b1001cfc7158b1001eee2158b1001eec2158b1004cff76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b10044ff7690b1001cfe7690b10004fd7690b1001cfc7690b10046ee6290b10006ed6290b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b10005df7350b1006ddc7350b10046ee6250b10006ed6250b10044ff7610b1001cfe7610b10004fd7610b1001cfc7610b100757e7510b100057d7510b1001df67110b10005f57110b100757e75d03100057d75d031004ebe64d0310006bd64d031001df671d0310005f571d03101f6bf649031004ebc649031004cff765031004ebe6450310006bd6450310005f7715031001df4715031020ebf641031004ebc6410310046ee62c8310006ed62c831001df671c8310005f571c8310044ff76483100057f75483100757c7548310005df734831006ddc7348310046ee6248310006ed6248310005f7714831001df47148310024ff75d9210014fe75d9210004fd75d9210024fc75d9210024ff73d921000cfe73d9210004fd73d9210024fc73d9210044fe72d9210004fd72d9210026f571d92101f6be41d92101f6bc41d9210026fa70d9210004fd76992100657e75992100057d7599210026bf6499210026bc649921004cff7659210026bc6459210004ff7559210014fe7559210004fd7559210014f
  | 8 => 0x4fc76505200067f65505201567c6550520006df635052014edc6350520004fe7610520004fd761052001cfc761052009d7e75105200057d75105200067f65105201467c6510520006bf641052004ebc6410520095de7310520005dd7310520006df631052013edc6310520045ee7210520005ed7210520006f7611052001ef46110520005fa7010520005f97010520005ee76c8520046ee76c8520045ef75c8520285ed75c85200076f65c852027f6c65c8520006ef64c8520006ed64c8520007cf63c8520277cc63c852001eee61c852001eec61c8520025ee70c8520046ef60c8520047eb60c8520277ea30c8520277e930c852009d7e75885200057d75885200067f65885201267c6588520095de7388520005dd7388520006df638852011edc638852026ded7288520006f7618852001ef46188520005fa7088520005f9708852001cfc76485200067f65485201167c6548520006df634852010edc6348520006f7614852001ef46148520005fb7048520005f8704852001cec7648520265ef7548520265ed75485200076f654852025f6c6548520006ef6448520006ed6448520007cf6348520257cc6348520045ef7148520047e77148520007e7614852001eee614852001eec6148520007e46148520257e63148520257e53148520007eb7048520025ec7048520007e87048520046ef6048520047eb6048520257ea3048520257e93048520044fe76d0120044fc76d012009d7e75d01200057d75d01200067f65d01200f67c65d0120006bf64d012004ebc64d0120006df63d01200eedc63d0120045ee72d0120005ed72d0120004fe76901200067f65901200e67c6590120006df63901200cedc639012004cff7650120004fd7650120044fc76501200067f65501200de7c6550120006bf645012004ebc6450120006df63501200d6dc6350120005ef7250120045ec7250120004fe76101200067f65101200c67c6510120006df63101200bedc63101200067f65881200a67c6588120006df638812008edc6388120045fa7088120046fb6088120025ef758812024ded75881200076f65881202476c6588120007cf638812023fcc6388120005ed7188120025ee7088120026ef6088120047eb6088120027ea308812023fe93088120004ff7559020014fe7559020004fd7559020014fc7559020024ff7459020026bf7459020006be5459020006bd5459020004ff735902000cfe7359020004fd735902000cfc7359020006bf4359020006bd4359020044ff7259020044fe7259020044fd7259020044fc7259020046be4259020046bc4259020004ff715902001cfc7159020024fe7059020024fc7059020026be4059020026bc4059020004ff7558420014fe7558420004fd7558420014fc7558420004ff745842004cfc7458420004ff735
  | 9 => 0xf735912000cfe7359120004fd735912000cfc7359120006dc735912000cdc7359120004ff7259120006ef7259120004ff7159120006f77159120004f7715912001cfc7159120006f4715912001cf47159120004ff7059120006fb7059120004fe76191200067f65191200067c651912004ebe6419120006bd6419120006dc6319120095de76d8d20096de76d8d2000cde76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d20007ce52d8d20007cd52d8d2028fdb70d8d20097d870d8d2028fdb20d8d2028fd820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d2028ede72d8d20096dd72d8d2028edc72d8d20006df52d8d2028ede52d8d20006dd52d8d2028edc52d8d2028ede42d8d2028edc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d2028edf21d8d2028edc21d8d2028edf70d8d20096de70d8d20096dd70d8d20096dc70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d2028edf20d8d20096dd20d8d2028edc20d8d20004fe76d0920024fc76d09200067f65d09201b67c65d0920006bf64d092004ebc64d0920006df63d09201aedc63d0920005fa70d0920005f970d092004cfc76509200067f65509201967c6550920006bf645092004ebc6450920005df7350920095dc7350920006df635092018edc6350920047ac4250920005fb7050920005f87050920047e820509200067f65d85200067c65d8520006df63d8520006dc63d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852004cfe74d8520004fd74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d8520024fe70d852009d7e75985200057d75985200067f65985200067c6598520095de7398520005dd7398520006df6398520006dc6398520006f761985200057f755852009d7c75585200067f65585200067c6558520005bf7458520005bc7458520005df7358520095dc7358520006df6358520006dc63585200067f65185200067c6518520006df6318520006dc631852001ef66118520006f56118520004fe76d0520004fd76d052004cfc76d05200067f65d05201767c65d0520006df63d052016edc63d0520006f761d052001ef461d0520004fe7690520004fd769052001cfc76905200067f65905201667c6590520006bf649052004ebc6490520006df639052015edc6390520045ee7290520005ed7290520004ff7650520004fe7650520
  | 10 => 0xa2008ddc7350a20005fb7050a20025f87050a20026f76198620026f46198620026f46158620004ff7558620014fe7558620004fd7558620014fc7558620004ff745862004cfc7458620004ff735862000cfe7358620004fd735862000cfc7358620006f65158620006f55158620024fc7058620026f61058620026f4105862004cff76d0620024fe76d0620004fd76d062004ebe64d0620006bd64d062001cff7690620024fe7690620004fd7690620004ff7650620004fd7650620024fc765062004ebe6450620006bd645062001cff7610620024fe7610620004fd76106200a57e75106200057d751062008dde7310620005dd7310620045ee7210620005ed7210620025fa7010620005f970106200a57e75886200057d758862008dde7388620005dd738862001ef66188620006f56188620025fa7088620005f9708862001cff764862001ef66148620006f56148620005fb7048620025f870486200a57e75d02200057d75d0220025ed76c8220046ed76c8220026ef65c822029eed65c8220006ed61c8220027ea60c822009d7e76d952009e7e76d95200147e76d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200076f72d952009f6c72d95200077a30d95200077930d95202977b20d95202977820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95202967e72d952009e7d72d95202967c72d95202967e42d95202967c42d95200067f32d95202967e32d95200067d32d95202967c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d95202967f21d95202967c21d95202967f70d952009e7e70d952009e7d70d952009e7c70d95200067f30d95200067e30d95200067d30d95200067c30d95202967f20d952009e7d20d95202967c20d952004cfe76d91200067f65d91200067c65d9120006dc63d9120004ff75d9120014fe75d9120004fd75d9120014fc75d9120004ff73d912000cfe73d9120004fd73d912000cfc73d9120044fe72d9120044fc72d912001cfe71d9120004fd71d912009d7e75991200057d75991200067f65991200067c6599120006bf6499120095de7399120005dd7399120006dc63991200057f755912009d7c75591200067f65591200067c6559120005df7359120095dc7359120006dc6359120005f77159120005f47159120004ff75591200067f75591200047f7559120014fe7559120004fd7559120014fc75591200067c75591200147c7559120006bf7459120006be5459120006bd5459120004ff7359120006df7359120004d
  | 11 => 0x5bd74c8440046ee62c8440006ed62c844001cff7688440024fe7688440004fd76884400c57e75884400057d75884400bdde7388440005dd738844001ef66188440006f56188440004ff7648440004fd7648440024fc7648440005bf744844004dbc7448440046ee6248440006ed624844001ef66148440006f5614844001cff7608440024fe7608440004fd7608440025bf7650040006bf7650040004bf7650040026bf65500402bebd655004020dbc7150040006bd6150040025bf705004004fbb7050040026be6050040027ba60500402bfbb5050040027b85050040027ba30500402b7b93050040004ff7559320014fe7559320004fd7559320014fc7559320046bf7459320006be5459320006bd5459320004ff735932000cfe7359320004fd735932000cfc7359320006bf4359320006bd4359320044fc7259320046be4259320046bc4259320004ff715932001cfc7159320046ef2159320004ff7558720014fe7558720004fd7558720014fc7558720004ff745872004cfc7458720004ff735872000cfe7358720004fd735872000cfc7358720046f77158720006f63158720006f53158720046f72158720046f4215872004cff76d0720044fe76d0720004fd76d072001cff7690720044fe7690720004fd769072004ebe6490720006bd6490720045ee7290720005ed7290720004ff7650720004fd7650720044fc765072001cff7610720044fe7610720004fd76107200b57e75107200057d751072004ebe6410720006bd64107200adde7310720005dd7310720045ee7210720005ed7210720005fa7010720005f97010720045ef7648720006ef76487202adef75487202aded7548720046ef6448720006ed6448720047e7714872001eee614872001eec61487202a7e631487202a7e53148720025ec70487200b57e75d03200057d75d032004ebe64d0320006bd64d0320045ee72d0320005ed72d032004cff765032004ebe6450320006bd6450320005ef7250320045ec7250320024ff75d9220014fe75d9220004fd75d9220024fc75d9220024ff73d922000cfe73d9220026de73d922000cde73d9220004fd73d9220026dd73d9220004dd73d9220024fc73d9220026ed72d922001cfe71d9220004fd71d9220026fa70d9220004fd76992200a57e75992200057d7599220026bf6499220026bc649922004cff7659220026bc6459220004ff7559220014fe7559220004fd7559220014fc7559220026bf7459220006be5459220006bd5459220004ff735922000cfe7359220004fd735922000cfc7359220006be4359220006bc4359220004ff715922001cfc7159220024fc7059220026be4059220026bc405922004ebe64d0a20006bd64d0a20025fa70d0a20005f970d0a2004cff7650a2004ebe6450a20006bd6450a20005df735
  | 12 => 0xc7650940005df73509400d5dc7350940006ef6250940046ec625094004fac4250940005fb7050940005f87050940004ff75d8540014fe75d8540004fd75d8540014fc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d8540044fe72d8540004fd72d8540006f751d8540006f451d8540006f631d8540006f531d8540006f761985400057f75585400dd7c75585400dd7e75185400057d75185400d5de7318540005dd7318540005ee7218540005ed721854001ef66118540006f56118540005be76d054004ebe76d0540004be76d054004dbf75d05402e5bd75d054001ebe61d054001ebc61d054004fbb70d0540025be70d054004fb870d054004ebf60d054004fbb60d05402ddbd7490540006f7619054001ef46190540005fa7090540005f9709054001cfc7650540006f7615054001ef46150540005fb7050540005f8705054004fb8405054001cbc76505402d5bf75505402d5bd755054004dbf715054004fb77150540007b7615054001ebe615054001ebc6150540007b4615054001eb46150540007bb7050540025bc7050540007b8705054004ebf605054004fbb6050540004fe76c8540004fd76c8540044fc76c8540046ee62c8540006f761c854001ef461c8540004fe7688540004fd768854001cfc76885400dd7e75885400057d758854004dbe7488540005bd74885400d5de7388540005dd7388540005fa7088540005f97088540004ff7648540004fe7648540004fc7648540004fe7608540004fd760854001cfc760854004dbe7408540005bd7408540006f7610854001ef46108540005fa7008540005f9700854004dfa709014004efb6090140025bf75901402cdbd7590140005bd71901401f6bc6190140025be7090140026bf609014004fbb6090140004ff7558840014fe7558840004fd7558840014fc7558840004ff7358840006df7358840004df735884000cfe7358840004fd735884000cfc7358840006dc735884000cdc7358840026ef7258840006ee5258840006ed525884004eef425884004eec4258840006ee3258840006ed3258840004ff715884001cfc7158840026ee2058840026ec2058840004ff7558440014fe7558440004fd7558440014fc7558440004ff735844000cfe7358440004fd735844000cfc7358440004ff7258440044fc7258440026f77158440006f65158440006f5515844004ef7415844004ebc415844004ef44158440006f63158440006f5315844004ebf405844004efa405844004ef94058440026f61058440026f4105844004dbd769044020ebd7690440004bd769044004ebf65904402c6bd659044004dbe719044004fb6719044004ebf619044020ebd6190440005bd70904401f6be609044004fba6090440044ff76c8440024fe76c8440004fd76c844004dbe74c8440
  | 13 => 0x87401267e65887400067d658874004dbe7488740005bd74887400edde7388740005dd7388740004ff7648740004fd764874004cfc76487401167e65487400067d6548740046ee6248740006ed624874001cff760874004cfe7608740004fd76087401067e65087400067d650874004dbe7408740005bd7408740026ef6298a40026ec6298a40026ec6258a40004ff7558a40014fe7558a40004fd7558a40014fc7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a40006ee5258a40006ed5258a40006ef3258a40006ec3258a40004ff7158a4001cfc7158a40024fc7058a40026ee2058a40026ec2058a40046ee6290a40006ed6290a40025fa7090a40005f97090a40044ff7650a40005df7350a400cddc7350a40046ee6250a40006ed6250a40005fb7050a40025f87050a40026f76198640026f46198640026f46158640004ff7558640014fe7558640004fd7558640014fc7558640004ff735864000cfe7358640004fd735864000cfc7358640004ff7258640044fc7258640006f65158640006f55158640024fc7058640026f61058640026f4105864001ef66190640006f56190640025fa7090640005f970906402febf65906402febd659064004dbe71906401f7b661906401f6bd6190640007b561906401f7ba7090640005bd70906401f7b9709064004ebe609064001cff765064001ef66150640006f5615064004fb44150640005fb7050640025f87050640005bd761064004ebd761064004f3e751064004f3d75106402f6bf65106402f6bd651064004f9e731064004f9d731064004fae721064004fad721064004fb671106401f6bd611064004fba7010640005bd701064004fb97010640005b9701064004fba6010640044ff76c8640024fe76c8640004fd76c864004dbe74c8640005bd74c8640046ee62c8640006ed62c864001cff7688640024fe7688640004fd76886400e57e75886400057d75886400cdde7388640005dd7388640025fa7088640005f97088640004ff7648640004fd7648640024fc7648640005bf744864004dbc7448640046ee6248640006ed624864001cff7608640024fe7608640004fd7608640025fa7008640005f97008640025bd76d024004ebd76d024004f3e75d024004f3d75d0240026bf65d02402eebd65d02401f5be71d0240006bd61d0240027ba60d0240027ba50d02402efb950d0240004ff75d8940014fe75d8940004fd75d8940014fc75d8940006be54d8940006bd54d8940004ff73d894000cfe73d8940004fd73d894000cfc73d894001cfe71d8940004fd71d8940006ef62989400057f75589400dd7c7558940005df73589400d5dc7358940005f77158940005f47158940046ee6218940006ed6218940006ef6290940046ec6290940005fa7090940005f97090940044f
  | 14 => 0x4fd7559021014fc755902101cff745902101ebf7459021006be5459021006bd5459021004ff735902100cfe7359021004fd735902100cfc7359021006bf4359021006bd4359021044fe7259021044fc7259021046be4259021046bc425902101cfe715902101cfc715902101ebe415902101ebc415902101eef215902101eed2159021004ff7059021024fc7059021024ff7598021014fe7598021004fd7598021024fc759802104cfe7498021004fd7498021024ff739802100cfe7398021004fd7398021024fc7398021024fe7098021026fa7098021026fa5098021006f95098021026fa3098021006f93098021046fb2098021026f8209802101efb1098021026f81098021004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff745802104cfc7458021004ff735802100cfe7358021004fd735802100cfc735802101eef215802101eed215802101efb7058021006fa5058021006f95058021006fa3058021006f93058021046fb2058021046f8205802101efb105802101ef8105802104e7f745974004e7e745974004e7d745974004e7c74597400067f73597400067e73597400067d73597400067c735974004e7f435974004e7e435974004e7d435974004e7c43597400067f72597400067e72597400067d72597400067c725974004e7f425974004e7e425974004e7d425974004e7c42597400067f32597400067e32597400067d32597400067c32597400067f71597400067e71597400067d71597400067c715974004e7f415974004e7e415974004e7d415974004e7c41597400067f31597400067e31597400067d31597400067c31597400f67f70597400f67e70597400067d70597400f67c705974004e7f405974004e7e405974004e7d405974004e7c40597400067f30597400067e30597400067d30597400067c3059740004ff7558b40014fe7558b40004fd7558b40014fc7558b4004ebe5458b40006bd5458b40004ff7358b4000cfe7358b40004fd7358b4000cfc7358b4004eef7258b4004eef4258b4004eec4258b40006ef3258b40006ec3258b40004ff7158b4001cfc7158b40004ff7558740014fe7558740004fd7558740014fc7558740004ff735874000cfe7358740004fd735874000cfc7358740004ff7258740044fc725874004ef7715874004ef7415874004ef4415874004efa405874004ef9405874004dbf7650740006bf7650740305bf7550740305bd755074004f3e655074004f3d655074004fb7715074001ebe615074001ebc6150740025bc7050740044ff76c874004cfe76c8740004fd76c87401367e65c87400067d65c8740046ee62c8740006ed62c874001cff768874004cfe7688740004fd76887400f57e75887400057d758
  | 15 => 0xf7350a2111ddc7350a2118ede6350a21006dd6350a21005f77150a2101df47150a21024ff7598221014fe7598221004fd7598221024fc759822104cfe7498221004fd7498221024ff739822100cfe7398221004fd7398221024fc739822101cfe7198221026fa709822101efb1098221026f81098221004ff7558221014fe7558221004fd7558221014fc7558221004ff745822104cfc7458221004ff735822100cfe7358221004fd735822100cfc735822101cfc715822101eef215822101eed215822101efb705822101efb105822101ef8105822104cfe76d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121006be54d9121006bd54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d9121006be43d9121006bc43d9121024fe70d9121004fd70d9121006bf6499121005df735912110ddc7359121004ff7559121014fe7559121004fd7559121014fc7559121006bf7459121004ff7359121006df7359121004df735912100cfe7359121004fd735912100cfc7359121006dc735912100cdc7359121004ff7259121006ef7259121004ff7159121006f77159121004ff7059121024fc7059121004fe76191211157e75191210057d751912104ebe6419121006bd641912101cfe76d092101cfc76d0921006bf64d092104ebc64d092101df671d0921005f571d0921005ee7690921046ee7690921325ed749092104eee649092104eec649092101dee719092101dec7190921046ef6190921047e7619092131fe6319092131fe53190921005ed709092101cfc7650921006bf645092104ebc6450921005df735092110ddc7350921005f7715092101df4715092101dec765092104eec765092101cec7650921045ef7450921047af7450921007af645092104eee645092104eec6450921007ac6450921317ae5450921317ad5450921007cf735092130fcc735092130faf435092130fad4350921007e7715092101dee715092101dec7150921007e47150921046ef6150921047e7615092130fe6315092130fe53150921005ef7050921044fe76d0521044fc76d0521006bf64d052104ebc64d0521045ee72d0521005ed72d052104cff7650521004fd7650521044fc7650521006bf645052104ebc6450521005ef7250521045ec725052101fb44150521004ff75d8121014fe75d8121004fd75d8121014fc75d812104cfe74d8121004fd74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d8121006fb60981210057f75581211157c7558121005bf7458121005bc7458121005df735812110ddc7358121006f96018121024ff7518121014fe7518121004fd7518121024fc751812104cfe7418121004fd7418121024ff731812100cfe7318121004fd7318121024fc7318121004ff7559021014fe7559021
  | 16 => 0x721006bd6450721005ef7250721045ec7250721024ff7598321014fe7598321004fd7598321024fc759832104cfe7498321004fd7498321024ff739832100cfe7398321004fd7398321024fc739832101cfe729832101cee7298321026fa7098321026fa3098321006f93098321026ef2098321046fb2098321026f82098321004ff7558321014fe7558321004fd7558321014fc7558321004ff745832104cfc7458321004ff735832100cfe7358321004fd735832100cfc735832101cfc7258321046fb7058321006fa3058321006f93058321046fb2058321046f820583210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596211267f72596213367e72596210067d72596213367c72596213367e42596213367c42596210067f32596213367e32596210067d32596213367c325962101e7f715962101e7e715962101e7d715962101e7c715962101e7f415962101e7e415962101e7d415962101e7c415962101e7f315962101e7e315962101e7d315962101e7c315962101e7f215962101e7e215962101e7d215962101e7c21596210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c30596213367f20596213367c205962101e7f105962101e7e105962101e7d105962101e7c1059621004ff7559221014fe7559221004fd7559221014fc755922101ebf7459221004ff735922100cfe7359221004fd735922100cfc735922101cfc715922101ebe415922101ebc415922101eef215922101eed2159221004ff7059221024fc7059221006df7558e21006de7558e21006dd7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e2111edf7258e2132ede7258e21006dd7258e2132edc7258e21006df5258e2132ede5258e21006dd5258e2132edc5258e2132ede4258e2132edc4258e2101edf7158e2101ede7158e2101edd7158e2101edc7158e2101edf5158e2101ede5158e2101edd5158e2101edc5158e2101edf4158e2101ede4158e2101edd4158e2101edc4158e2101edf2158e2101ede2158e2101edd2158e2101edc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006de5058e21006dd5058e21006dc5058e2132edf2058e2132edc2058e2101edf1058e2101ede1058e2101edd1058e2101edc1058e211b67e65d0a210067d65d0a2104ebe64d0a21006bd64d0a211aede63d0a21006dd63d0a2101df671d0a21005f571d0a2104cff7650a211967e6550a210067d6550a2104ebe6450a21006bd6450a21005d
  | 17 => 0x6fa5398041006f95398041006f8539804104efb439804104efa439804104ef9439804104ef84398041026fb7298041006fa7298041006f97298041026f87298041006fb5298041006fa5298041006f95298041006f8529804104efb429804104efa429804104ef9429804104ef84298041006fb3298041006fa3298041006f93298041006f8329804101efa719804101ef97198041026f8719804101efb519804101efa519804101ef9519804101ef8519804101efb419804101efa419804101ef9419804101ef8419804101efb319804101efa319804101ef9319804101ef8319804101efb219804101efa219804101ef9219804101ef82198041004ff7558041014fe7558041004fd7558041014fc755804104ebe5458041006bd5458041004ff735804100cfe7358041004fd735804100cfc7358041004ff7258041044fc725804101ebf415804101ebd415804101efb7058041006fb5058041006fa5058041006f95058041006f8505804104efb405804104ebc405804104ef8405804104eb84058041006fb3058041006fa3058041006f93058041006f8305804101efb105804101ef81058041006fb7558041006fa7558041006f97558041006f8755804104efb745804104efa745804104ef8745804104efb545804104efa545804104eba545804104ef95458041006b9545804104ef85458041006fb7358041006fa7358041006f97358041006f87358041006fb5358041006fa5358041006f95358041006f8535804104efb435804104efa435804104ef9435804104ef84358041006fb7258041006fa7258041006f97258041006f87258041006fb5258041006fa5258041006f95258041006f8525804104efb425804104efa425804104ef9425804104ef84258041006fb3258041006fa3258041006f93258041006f8325804101efb715804101efa715804101ef8715804101efb515804101efa515804101ef9515804101ef8515804101efb415804101ebb415804101efa415804101ef9415804101eb9415804101ef8415804101efb315804101efa315804101ef9315804101ef8315804101efb215804101efa215804101ef9215804101ef82158041004ff7559321014fe7559321004fd7559321014fc7559321046bf7459321006be5459321006bd5459321004ff735932100cfe7359321004fd735932100cfc7359321006bf4359321006bd435932101cfc7259321046be4259321046bc4259321004ff7059321024fc7059321045ef7650b21006ef7650b21047af7450b2104eee6450b21046ec6450b21347ae5450b21347ad5450b21007cf7350b2133fcc7350b2133faf4350b2133fad4350b2101dee7150b2101dec7150b21005ef7050b2104ebe64d0721006bd64d0721045ee72d0721005ed72d072104cff765072104ebe645
  | 18 => 0xd7398841046ec7398841006ef5398841006ee5398841006ed5398841006ec539884104eef439884104eee439884104eed439884104eec439884101eef719884101eee719884101eed719884101eec719884101eef519884101eee519884101eed519884101eec519884101eef419884101eee419884101eed419884101eec419884101eef319884101eee319884101eed319884101eec3198841046ef7098841046ee7098841046ed7098841046ec7098841006ef5098841006ee5098841006ed5098841006ec509884104eef409884104eee409884104eed409884104eec4098841006ef3098841006ee3098841006ed3098841006ec309884101eef109884101eee109884101eed109884101eec1098841004ff7558841014fe7558841004fd7558841014fc755884104ebe5458841006bd5458841004ff735884100cfe7358841004fd735884100cfc735884101eef7258841006ef5258841006ee5258841006ed5258841006ec525884104eef425884104eec4258841006ef3258841006ee3258841006ed3258841006ec325884101eee215884101eec2158841004ff7058841024fc7058841006ef7558841006ee7558841006ed7558841006ec755884104eef745884104eee745884104eec745884104eef545884104eee545884104eae545884104eed5458841006ad545884104eec5458841006ef7358841006ee7358841006ed7358841006ec7358841006ef5358841006ee5358841006ed5358841006ec535884104eef435884104eee435884104eed435884104eec435884101eef715884101eee715884101eec715884101eef515884101eee515884101eed515884101eec515884101eef415884101eee415884101eed415884101eec415884101eef315884101eee315884101eed315884101eec3158841006ef7058841006ee7058841006ed7058841006ec7058841006ef5058841006ee5058841006ed5058841006ec505884104eef405884104eee405884104eed405884104eec4058841006ef3058841006ee3058841006ed3058841006ec305884101eef105884101eee105884101eed105884101eec1058841024ff7598041014fe7598041004fd7598041024fc7598041024ff739804100cfe7398041004fd7398041024fc7398041044fe7298041004fd7298041024fe7098041026fa7098041006fb5098041026fa5098041006f95098041026f8509804104efb4098041026f84098041006fb3098041026fa3098041006f93098041026f8309804101efb1098041026f81098041026fb7598041006fa7598041006f97598041026f8759804104efa749804104ef97498041026f8749804104efb549804104efa549804104ef9549804104ef85498041026fb7398041006fa7398041006f97398041026f87398041006fb5398041
  | 19 => 0x8941006ed621894101cfe7690941006ef6290941046ec629094101df67190941005f5719094101cfc7650941005df735094114ddc7350941006ef6250941046ec6250941005f7715094101df4715094104fb44150941004ff75d8141014fe75d8141004fd75d8141014fc75d8141004ff73d814100cfe73d8141004fd73d814100cfc73d8141044fe72d8141004fd72d8141006fb50d8141006f850d8141006fb60981410057f75581411557c7558141006f96018141024ff7518141014fe7518141004fd7518141024fc7518141024ff731814100cfe7318141004fd7318141024fc7318141044fe7218141004fd721814120ebe411814120ebc4118141006fb5018141026f8501814104e7f745944104e7e745944104e7d745944104e7c74594410067f73594410067e73594410067d73594410067c735944104e7f435944104e7e435944104e7d435944104e7c43594410067f72594410067e72594410067d72594410067c725944104e7f425944104e7e425944104e7d425944104e7c42594410067f32594410067e32594410067d32594410067c325944101e7f715944101e7e715944101e7d715944101e7c715944101e7f415944101e7e415944101e7d415944101e7c415944101e7f315944101e7e315944101e7d315944101e7c315944101e7f215944101e7e215944101e7d215944101e7c21594410067f70594410067e70594410067d70594410067c705944104e7f405944104e7e405944104e7d405944104e7c40594410067f30594410067e30594410067d30594410067c305944101e7f105944101e7e105944101e7d105944101e7c1059441006df7558c41006de7558c41006dd7558c41006dc7558c4104edf7458c4104ede7458c4104edd7458c4104edc7458c4104edf5458c4104ede5458c4104edd5458c4104edc5458c41006df7258c41006de7258c41006dd7258c41006dc7258c41006df5258c41006de5258c41006dd5258c41006dc5258c4104edf4258c4104ede4258c4104edd4258c4104edc4258c4101edf7158c4101ede7158c4101edd7158c4101edc7158c4101edf5158c4101ede5158c4101edd5158c4101edc5158c4101edf4158c4101ede4158c4101edd4158c4101edc4158c4101edf2158c4101ede2158c4101edd2158c4101edc2158c41006df7058c41006de7058c41006dd7058c41006dc7058c41006df5058c41006de5058c41006dd5058c41006dc5058c4104edf4058c4104ede4058c4104edd4058c4104edc4058c4101edf1058c4101ede1058c4101edd1058c4101edc1058c41046ef7598841046ee7598841046ed7598841046ec7598841046ef7498841046ee7498841046ed7498841046ec749884104eef549884104eee549884104eed549884104eec5498841046ef7398841046ee7398841046e
  | 20 => 0x4ef44158442006f63158442006f53158442046f72158442046f42158442004ff7058442024fc7058442024ff7598042014fe7598042004fd7598042024fc7598042024ff739804200cfe7398042004fd7398042024fc739804201cfe7198042004fd7198042024fe7098042026fa709804204efb4098042026f84098042026fa3098042006f93098042046fb2098042026f82098042004ff7558042014fe7558042004fd7558042014fc7558042004ff735804200cfe7358042004fd735804200cfc7358042004ff715804201cfc7158042046fb705804204efb405804204ef84058042006fa3058042006f93058042046fb2058042046f82058042004ff7558b41014fe7558b41004fd7558b41014fc7558b4101cfc7458b41004ff7358b41006df7358b41004df7358b4100cfe7358b41004fd7358b4100cfc7358b41006dc7358b4100cdc7358b4104eef7258b4104eef4258b4104eec4258b41004ff7058b41024fc7058b41024ff7598341014fe7598341004fd7598341024fc759834101cfe749834101cbe7498341024ff739834100cfe7398341004fd7398341024fc7398341044fe7298341004fd72983411f6be419834104ebc4198341026fa7098341026bf409834104efb4098341026f84098341004ff7558341014fe7558341004fd7558341014fc755834101cfc7458341004ff735834100cfe7358341004fd735834100cfc7358341004ff7258341044fc725834104efb705834104efb405834104ef84058341004ff7558a41014fe7558a41004fd7558a41014fc7558a41006be5458a41006bd5458a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a4101eef7258a4101cfc7158a4101eee2158a4101eec2158a41004ff7058a41024fc7058a41046ee6290a41006ed6290a4101df67190a41005f57190a41044ff7650a41005df7350a4115ddc7350a41046ee6250a41006ed6250a41005f77150a4101df47150a41024ff7598241014fe7598241004fd7598241024fc7598241024ff739824100cfe7398241004fd7398241024fc7398241044fe7298241004fd729824101cfe7198241026fa709824101efb1098241026f81098241004ff75582410067f75582410047f7558241014fe7558241004fd7558241014fc75582410067c75582410147c7558241006be5458241006bd5458241004ff735824100cfe7358241004fd735824100cfc7358241004ff7258241044fc725824101cfc715824101ebf415824101ebd415824101efb705824101efb105824101ef81058241004ff75d8941014fe75d8941004fd75d8941014fc75d8941004ff73d894100cfe73d8941004fd73d894100cfc73d8941006ef32d8941006ec32d8941024fe70d8941004fd70d8941006ef6298941005df735894114ddc7358941046ee621
  | 21 => 0xf52d8d4234ede52d8d42006dd52d8d4234edc52d8d42356df42d8d4234ede42d8d4218edd42d8d4234edc42d8d42006df71d8d42006de71d8d42006dd71d8d42006dc71d8d42006df51d8d42006de51d8d42006dd51d8d42006dc51d8d42356df41d8d42356dc41d8d4234edf21d8d4234edc21d8d42006df70d8d42006de70d8d42006dd70d8d42006dc70d8d42006df50d8d42006de50d8d42006dd50d8d42006dc50d8d42356df40d8d42356dc40d8d4234edf20d8d4234edc20d8d42006df63d8542006dc63d8542004ff75d8542014fe75d8542004fd75d8542014fc75d8542004ff73d854200cfe73d8542004fd73d854200cfc73d8542006f651d8542006f551d8542024fe70d8542004fd70d85421957e75985420057d759854218dde7398542005dd7398542006df6398542006dc6398542006f76198542005df735854218ddc7358542006df6358542006dc6358542006df6318542006dc631854201ef66118542006f56118542006df63d8142006dc63d8142004ff75d8142014fe75d8142004fd75d8142014fc75d8142006be54d8142006bd54d8142004ff73d814200cfe73d8142004fd73d814200cfc73d814201cfe71d8142004fd71d814218dde7398142005dd7398142006df6398142006dc6398142006fb60981420057f75581421957c7558142005df735814218ddc7358142006df6358142006dc6358142005f77158142005f47158142006df6318142006dc6318142006f96018142024ff7518142014fe7518142004fd7518142024fc7518142024ff731814200cfe7318142004fd7318142024fc731814201cfe7118142004fd711814204e7f745944204e7e745944204e7d745944204e7c74594420067f73594420067e73594420067d73594420067c735944204e7f435944204e7e435944204e7d435944204e7c43594420467f72594420467e72594420467d72594420467c72594420467f42594420463f42594420467e42594420467d42594420463d42594420467c42594420467f32594420467e32594420467d32594420467c32594420067f71594420067e71594420067d71594420067c715944204e7f415944204e7e415944204e7d415944204e7c41594420067f31594420067e31594420067d31594420067c31594420467f21594420467e21594420467d21594420467c21594420067f70594420067e70594420067d70594420067c705944204e7f405944204e7e405944204e7d405944204e7c40594420067f30594420067e30594420067d30594420067c30594420467f20594420467e20594420467d20594420467c2059442004ff7558442014fe7558442004fd7558442014fc7558442004ff735844200cfe7358442004fd735844200cfc7358442046ee425844204eed4258442046f7715844204ef74158442
  | 22 => 0x9004001c00a000000000002000100181d00080020070000018002000800000200b001000800200d0028040004025007003000c012000002403e000009000400000b00580580000070000000074000003801401c01200780000280000018008000001003803400800000180540040010000078006003001800c02400e001000000200400580080460010310060006003001800000e027003800400c0040000024000027004809800601b003807c00200200000000000060000000000000000005400a0000008028006003001804400800200080100000090010044004003000001802600100000080000000028034016012004ff7558742014fe7558742004fd7558742014fc7558742044fc7458742004ff735874200cfe7358742004fd735874200cfc735874204eee425874204eed425874204ef7715874204ef7415874204ef44158742004ff7058742024fc7058742024ff7598342014fe7598342004fd7598342024fc7598342044fe7498342024ff739834200cfe7398342004fd7398342024fc739834201cfe7198342004fd7198342026fa709834204efb4098342026f84098342004ff7558342014fe7558342004fd7558342014fc7558342044fc745834204ebe5458342006bd5458342004ff735834200cfe7358342004fd735834200cfc7358342004ff715834201cfc715834204efb705834204efb405834204ef84058342004ff7558642014fe7558642004fd7558642014fc7558642004ff735864200cfe7358642004fd735864200cfc7358642044fc7258642046f77158642006f63158642006f53158642046f72158642046f42158642004ff7058642024fc7058642024ff7598242014fe7598242004fd7598242024fc7598242024ff739824200cfe7398242004fd7398242024fc7398242044fe729824201cfe7198242004fd7198242026fa7098242026fa3098242006f93098242046fb2098242026f82098242004ff75582420067f75582420047f7558242014fe7558242004fd7558242014fc75582420067c75582420147c7558242004ff735824200cfe7358242004fd735824200cfc7358242044fc7258242004ff715824201cfc7158242046ef2158242046fb7058242006fa3058242006f93058242046fb2058242046f8205824218dde76d8d4218ede76d8d4200cde76d8d42006df65d8d42006de65d8d42006dd65d8d42006dc65d8d4234f9f74d8d4218f9c74d8d420079e54d8d420079d54d8d42357cf42d8d4234f9e42d8d4234f9c42d8d42357cc42d8d42006df75d8d42006de75d8d42006dd75d8d42006dc75d8d4234edf74d8d4218ede74d8d4218edd74d8d4218edc74d8d42006df54d8d42356de54d8d42006dd54d8d42356dc54d8d42356df72d8d4234ede72d8d4218edd72d8d4234edc72d8d42006d
  | 23 => 0x9c00200400300b400802400000100160020060000014000003800000601401b8000002001001800400003f001002000e002000000c01c00500a0004026014001000001000d0010004000001008802400e00e0208010006009001800401c00000580280000000000000010001000802000800100e0048016006000002c016001001801c002001002003c0040000030018000006003003c0180040000014000000006800c00e03200380800080080020000004016009000006a0050038000006000002800001601a000002c002000001800001200300300440000070000040004002001804400a000000800000000300200240260000018000010003001005800200300d000000202900f801000602e00380500040370138000000004001001401800d000000000c02b006003400201d0008000018009002000c00e000006804c002002001800803600e00380340000140080040000002000000001601701b002002a006000801404600100000040420130018004006000006013c00a00b005804402c014000808400c001001000801a0000018068002040002801402400a00180000040070000024006005000000001a031008006000802a000002402e00b0000000000004005800000000c000000802000100080200080060000000050001000008c004019006001000400100500000020170048024010001003007405c00d0008010000009003800c0260010000018018000006800001000400d002000a020007800800203c000001400602300300640000300000020008001002006c04800b000000401a00700c000000000000d801400e00100180000100010000030002007009009001c022002000000000800e800000400400f000400000100880780080190088000006001000800400c005000000800200300f001800c000001002c034004002801c000002004000000600d0038018002019000000800a00100a000000402b00100180000050000008000000000000000200300280180000010010034112002005002804e00b000800001400000a800000802f000002401e001003803403e006007801800800000900740ce02a00d80a800000201b0014002011000000405a00700280180000710008020000008006001c00802200200580080000028008010001000800803e0040038030000014001004005a00400b000001c004005800800a00100281080000000180000002002002805000000000000040240190000008002004000000000600c00100000000040050004010000004801c008000000801003200e002800c00a01e001000001000600c00100020020010004000019000803c00600102b0000066002001000000600b000001000c00e001805400e0000000020006000001000c00a00e00a8004000000001800405a0060020008014
  | 24 => 0x95020004a7000067a96432d8d6c4069223bb00017686e70000000966c7a4ba82f13384f043b3229d341f15860fe43c4cd600000b8c1074120ebb58f6e1f558f3ba1b52ae90f436a1b647e569e1de454a7742523c5d166b7d2c9a56805e11b3338014f82c3f3d60000c6c0005ca22d0eae3d446509a8380c9457983e41100672851865892d953a6b64152a3ca1740f1d49a000563928536a8e61998bf86aadcd00021889a80020468a18000a9f0400000abe0001d60001ba800000100000020010000012002000000000000b000001000a00c001008400201300500100040090008140002001005000000a00800a001400a002001800402e006000800001a00c00a007c010007002000002400e000003c00a008006000001c0020010038006000016001811400000700000000040020004000002002000000a0140080000056000007800000000200200000360090010000018003000001000c00000080240080040010054002003000000001201d000000801a00100380c806001d00280100040070058008006000001801002000100181dc0180010030000000000006000000000900880140020000028000004000002005000e0200000000000008003000800000400000040060240000034000001000001000c002000000000200700f80000000550000090000032008000c002029004003c02c0000008030010004000005c01600a00d000401201c00f000803a0000020070008004000000002c00e001800400000000d8038000009006802000200600c0030004003005802405c028004808c00200a004004000000001600000000120008008002009000002400000f0048014010008001000401e01f01a801400e0000000004004000009801c000013004800800c014002005000000200001b80120180010024000008002004c0080690038028000000000009000600300080200020000020014058000006800404c001005808c014000000800001e005000800802a00f000801800c026001802c00a00f008013800e0010008000048009003800001200a010005801a00b00100740100000000000004000010800001c00300400500120150038024000019000002000001b000016000a0040000000036025001804001e0000088024044005000000003e006000801c00800001a000000400f005000005c00000d005400001000280040020000038034004000000800801a0070010004008000004802800000000180140720250000004042006000001001e002001000400a03d003002400a004002002804200f002800000000200b000c000018000000804c001000004c000009000000c00002c00000080060020008000000012005803000800800000040000050050008002005005000c00602a002000c040004000003c006014001000801000c003
  | 25 => 0x96ff3109b6eec2217b0c45bad7e6fca6593ce3d30081f1d92eda22ea8ab952c3f176f002c57a4d00002ad44940e44c0a205270e602bbb849c92277749b41190c000414289156ee5e00018d400026500018fcd5c5e839e2b6c8940a20888000000a8a1b717840002fa0001a8cea20576e0000062c0755ec81e82bc8154f9000056432814ead207d83ad000000123838d69f15880008ea15682252343d751289b800000033f9fcde50ec9000076164a1076633134eaa37a0ca9e1cfded38094a920000ca36ab26e000078100025a4b84f205412e84ab253276580006b23950000001cc210b36da8f80006be43700004ac0003da07280009a305b34a91e80002928000000db3307a524c8e000034b2ac0008d1622b64cf14c7076015ad5da5b967427f0d8466f09e8164638c3c11d80018d290b40980599342d536e0f0d3d23dd3d0bbf0d8e20400022b5088c910930000b800000002629a020000002db86ca0004f10000524df60001e68000cd3000174400089a5cc8c8d28407702613b44463a770f95b818c791328bab8000bd67888001bfe00000008f8e9091400020811520006c700007eed8f06d2bc0b3e600280800076250f2f887dc000000791aa4046ad840002a0cf5e9080ab2815268a0d2338431dca000173b4808360006ee876400098826680018a0d8a42db7ccf107f06df05f57ea00007d9c0d1c49c84761c9d3b888a524b3d0c2805f5990001c028695fe0000de08db362329973e2b406e948c5ae0ad736b1b8026ce13868709620b3c32b2f1871eed2581b5a1e586b560880a983cdd307e9bf10de00039901c1298830071000000000000022f970219911720ad23cbbc0001e3cb6633e397b0690466b16c13aa48fe13b09c000137497400003fced61350001b258a8000000310c5fa00011a350962cad94c011cd316798000377040028e70e2f2c00001a29018c038ca44124a4850f8c986ccbb7dd381237032d1160e29b47e0000bfc3c058425b9bd834517698dc6f641851fade8000c90000366999c00009c80000c8cc81682161a627b85a48d787a08ff77aae3923eb297631ec93a275b0a503bd4cce7f185216813842b318921864ae3d26584794fe62a1d98dfc8e81ee1ef0accc42384619b93d75a0306e780854e89ca592193d3ac03722a2098b0c8dc3822b043acc0d11e35f09c2db458580004c03e30000e2d030c8800002edbc655e44e8000e1883e5d02df0cda2c3000000096eec1692293d34a0000001cc43f48800c293e4d8000041aaa955286d76f90fcdb8443255214a5340dab39c852c19261d2d58001c520002bf97783a48d40091598000ea7000000104a6d2039b4cd624dd21a88f180008e700000018000000ff00004408460130001c0e00016c237c5d254e0623bf80000000c8b6fd7060000a29931b469c157231d
  | 26 => 0xb400015320880008505e553d99885ee00052580000000495938000d4c23f35f80014e6cd5000000000019c6c91aace287e22420000a9896c2258000152bd13ed0000d7a0001ca2e8d3600000d1abfced04a644f00019880007759c4c000093374000024458c0001b743eca791840000000bba711800000022a0000000d9ed452fd000082c000000057400024143b8ad9db86614de80019e6a060b980000000000002b19816e3100023e8bce8b700030bc00038a4d623680184f24982f159088c251410fd0caece00010893d8000000186cb860005b78001d440004f823ed67e2c70003be509e4c1000000149cd1615895a0ea62df4e1800000034201e0268a682382d406cd3c07e70c91000b680000f6b79c00031a1ed80000008d30003b68a9416161a00006f054621aa5a18aa2a670487387727aa0810d5c9e6c8931f36703f05ea33da2a941834a532b7259f202863692e41ae2dc1710d41a5c54b54ea8f0a44dd90e6898cbc077f08c86b8414cad6f10a298ae13219896101da000296808d9545c855da411ad888f37c3059cf85cc05312a12e2bee59a2d4c0000000003329958ee02970000b4400042e1980000aee4b9bb4c0008e510c9a4400081b00000008f09296072664a221984c61c15580459000083c000d8300022919e2f0c73ca8a518681f1800000bb45f518d8000000c5f17ca2551c2bf718f800075c00018a16780006961b50000000c1005c992c4ecba7666b2d09c459b000275c17a00000017f4d480006d684a984a00050b00019ee00065f800100245e359222c49e0006303b1128e69d68808bcc147841582130de4d0d2ea2aa03d2f152c7932056e2da4fd133d4b02ac4292d84cf473027220b9996604474a0a8feebe53c80909a9eea111b3ca99b2e777478c547dec6b1f212f832e5ca04f1878e6e78e1b9b85138c65a2ba863521e000413845035626b0001394000006329aff4812e32000040c1d00000a38650bc807e00033c8000d536b889e000002b16882d465cb2b12ab7c55626a03c9b9b92949af12b96a5538765026b578a78f1d75335edd5ea6372437997ce38336b1a1101657e428021c000de539500558720000ad8ef80004517818b5143e7fe60a355cfc672b1b23a2ce98d75000211da72a0e77480017d07b52323488f04b9b720800000035c6b0800152219e7870a440004bc26b18a123aee42b6266d5f62720370000000c9f1cc09a1df483b4c88000000ce65ae084ce86c512d3812076ea377328000ddc5cb0000001c309ce720000110c1a7653939dd4a10d1090000f943a96b11ae03206a9292301c5163ff00000012ec00000028edab40001b0858ce660994a996bd2620000eea60dde663b00000008c29a744c8001da8a2b2d83c4c42000000005e17c40000000000b9c8090000e1d1382fb2b01574a866b
  | 27 => 0x973baa0fc0408561fdaa6dda05b1133bc355f8f105f98ce8e1e8f255d07ecfa497f70a891d1e6d9e5ed2fa8db077e7583c0887888330d3b5cd046ec47031716c85fb0f634c05c641443d3ab46d8d8109f37f14b69b93cfa56d8587ff2ef97ad9600e0547b118aca1df0430f21bb69e100015a4f40c8158c8a8122a40257606c8000000072800000018a06c0000b640000000000a900001b592d9dce3cf37f9449b763e2447296984c1e6490116902c5f464dbc2c49a0005c612a4b9ae3c480012c0001f96faa3a1dc271500023610f0c1f6c384415fab6d5999170fec4404f52e9141441e5ff2a9cb8e4da37f0f9c29eae82b20a34c5e8a21878e8d6083101cb06992f64831db1ec4daa7c21cf1b4c89caeb7169d50a28391209997c8dcbf11bca7608f64252278180b3483d6c41c18a260003f616f4d18c6a5730ed0af8d2d71009ed41e259036859861c07d0022ae0808d0c008b380588e6b6d60a1d77ac9d1df85dcf569e623535e97c297d5dba725bf624c5a80001c7c68609ba4fcf66ce94b02d580000000000000a7c0001ff17710fa35d2ba190c1e05970002b08a06b3d00014258ee8602e983ccb1200062080015443464668a5978204e25e8a15cac44763115cd5f4215090bac9d0aad11d50da48607eb6c6853950a1cf0fa21340665470ce8c0de12a7653c1d24ebee7d2c72ec13e873d6a3b121d1800000005202ae4f71d0b3f1dbaec326fae246909ff073af5068208364b1e9c03e3026b3b70d4260002859345a9c00002a80010e20004540000000cfd06e3a7543a68f217305dd56c7c5001fd5ac8b6605b813c65a0d23e8181dbdcab940baa340005bf6d39b68000b754db80000002290000b5961a00000000000007622c920b0be02a11e8a5bc000e8774030ec31c4b20232da448059c6cea4a850466524a218d8ba07b1ba0b848d86a82d72a21cd8e270af80016fce470000000000b470001fd00000000000001a8812d02e00000001242ec9ac055e27c78902b11c85ad4a59be4d10bdd19100000000003af0000000000000000091c8c977798e1b96b706752341218b7838b2b89a80096492915cbe4e5a4341c00ed4f1a30b380896075c162866da109050049d2844c2de0a910388660be4a8062400048d00011d903801421d027d59c81d405352c6a465c61eb6514ea49714c1eb9daa66670b9ec1e1e0001258fa00003090ed386c000c92457800000049e3c4a9c91f23cc3f500b403adc734800007880002290400000d5460caa60f7e07c0db0001a9ad7373500012a8081738ac28006e1a5449e183020fe2881e992b221851c8bfda8c3d96321934398cde31185f01c25a5564b7e9bb439c3682dec0006760e3abe051e0cc17c187c9040000000000b82ed959a91f5540ecc095a3ad398d4941482280000b24690000000000247b3
  | 28 => 0xbc0000000000001c54d183bc00019cec3a3bba4a00000000003060000a212518000000a62098198c000b650a2375400066e252a41d14058104e80001f45dd00000d99a22cf298afc1aba0005362555e380000001d9119ead80001a9514286a0c32d6429ac5875431d0e2052c27892558ac6030001fa17847a858c17587c0000602b5fc00035635535d916c56119ca108dc20001c406a8b78a522c10251a8225a0628000116c9e13f9b944e60225a5b184526a430600001896d17235a2f1c260000002615998c043c28b905081764c6a0154d4eb8650aa6876a58d56697dcf6ced173780002507de0000418000000179abbc4608225f7aaccf720004608e240bc0000000000ede66c2243a48974000000289d88000000011e45922065b9800192a18003c2ba80000006e89dcd6741fd6db06d0924b465d586203820000000d35556a2271ab0c94660000de345035e000000000053c0004b68f54a009724fa955990eb116fc0f84a2c21d536920542aed823e00014940a03eb0d11dfe37742281ad8cec6c2a095ed2c2b8228ca53d7d8b233893c787cae527062020d760000000000c203540618d6996260c345378177e1751c135dc00043100009e8d787d1226af3c2e01710bf8000986e696bc1020dc872e18580000000000000b800002bf66480000007ed6d00000b5442400000006301871660000d0669b77b15bc0003344d9b1a0838e335372008e52a313ea257039085e5e4984cbae0925e209704e262070c86fc0007806c880000005443a780005b200011200000000000000001d046fb44b00000003f5000117dd7a00047ba21146a0002603ad548e9ef2d03c140000000003c9400016b69e800000000008d1d9d7fe3bd67f0e81ae81e362c9328dc0cbc3111ae950e93e00d9eb4000e2f6573c050e4e0a5229acc3d4ad53f32d482e81db4ef1929508e4a5340b98a2ed274fc91246dee6648086e94aac0272e95c4000917685985d6c000074c80e998682d33e800052874445fb61513ecfa1a7abf91281135dc249c58c7451541e8ce4a4a22779cf82d02315f000006e4b722f335b4d1680d27a83d0000a085c7a460fbecef19e0cbc0e2c0a424b838000a1434716dc80ca1a4e9000065433755faaa83c00000003a8c000d3a4a2a50c858426261394cd9a796099843c0000003e4aab48ee00000018b14a800000000fc8aaaa64df28b45ca96568f8eac6b094d60620007642524fb04bd4b2cb802894e58e67f8257920152e000222814c6e02f253496995168b0000081d7aa0003208001c0a3bb16d93fdac6b957920f057f60004330850ca09b2687395038a8c71d29318e6826603294783f8bc031eb9895260000f2b44910ecb7764274175e4d27130e64686df00472655086de826eaee4b888b81e92429a0a65912ead01de8be31f58c052482
  | 29 => 0x10409fa9e8ee00000000000dea658080879139e00000014c0000c793943540d2e4685f5acbd0e80003b708e80003d80413309dd8ad71b1b841a6a7c30b503ac6a67524afb83c8e238509a0000b6c9eb26980000000005d43915cfcef8383a764ff65783273bc9a76d864bf057125ca5163884c4f488315ceb92cbc60001cbb6254326743de00016ecb51675a1505202800ffb6951ae83929f85b40009f332a9d6100e515042b428a9296313f0001af2ba64588000000f1644280008d20b138e08580001a46b81f847d42cd0001e643aef2903783c800046d314800098883c38c00000003055db1da462200078d85057be00022d92b4fb6b141010000f2a66b5a2a66814e4200002f301660cd0002bd8d6800000020e970c14922631784348b22fc94ed976e5f00026d11c639f42c80017cc37c0001db122280619586949b80000000001146000601b738d9c4ce392000000055571700000002581ed1bac000a924629870e709a2778a8b0d3271103a064dc00063453800015ecb36d72bc892c72d102b728000c215bf800002e5ec74faf4d4306f73b08fc12f80410b9000000019f41a356400000000000000d85ed2390000000e965bba4f1684e045c3800164c00000000000004427128b095000002c5800074c2430000a699b44c91e48564c92b383132e8886ccbd15c3419518f0062619a02fc51c2c038e0000daf1a018541841096d081897346014ae84d89c0e550001ab0000e2b30c01a1d54029739b07162e5851bf2175644ca24a8ab304023ba27a2c6d61c7022a9a4d9224c2475f1a9d7b60006be900d3ca000233082171493b40f34b004a0004961ef82a8b6820684940000005c88744000cb942aaed5c0686700003d837c6af488000000057034e00059529676a924d546c9c405a2b140000002a90884888cd70003600000dd63fd0c801ac00059d800137e33f24e0000156000000000000000000000013d000000000000003754bca9918de83729eb350a1a00031591c01be00075d2d8944c000000232d1800001a72610000b4172c80014ae4fb000000196a6ca02c0000c0a6c60509715d9a79720ba7ece3a0005739e2cee49236ae06814de321229bb3da7ee5b2c837a528821b7342e94696b203718e497a46454c7b8847b8d2f11630dc9c68ba1643c108fcc8c73d26a1c68acf56d1ce8dbc41531e1bf4a6eb986b921f8388d5878fb2e89f042a795abdc702cf84eaa1d40001512bca599d6849910e12fc00000061f25880000915ad277d85a30c2f707252f40316f78c5cc5a0000e80001acc5ff58ab24c954c1564116d424022d75b9661b549db6da9ba9b2e54f6a50108e44ab06e313785f82515c41f3106475a6dc9d995bacee33c11d4000da46b02e7857281448cb991122a3d2e7aabc96a55c59bb53057c24452e39c000018c1382
  | 30 => 0x328066ab4e21f077955c4ab6760ad432c24e1c72fb490e0951312f78fd20003cda23407c00e61110154e06f418229f5a4aab42c181756b0acb0650b48dde16c6819de8d446696690378ce000020fb48561e06a29b229911087b0bd2d75a2a03454324ddb62c6528f9b9895859d01608cc5d8cdf1fa0f3518c0005ec244cd6cb800d085012d48980002849870e0b00029dd43600009626840001d31449469a380004ce941d3c871e34d101c69899019b00013781b56cf80014e20000003ac4940e3a70e8dd84da0c133f0e6800020e00029f9e4415000028250c2b4f771b39000000000000000007d343680019fe000604bc98000b3974da7682d26986330ec0bf88b547b2709a5277160e8e6dd081f332434648207fd313a5e00005d8693280cc1ac0f46f096c0009b100009d47e41162c50000000e2406a9174000e570001ee8cf8d690ac2844846e5829ab5bc0003900003859738ad337b295823090d340000037a127000118d9488514088aada2248c2458000120cdd5e42c85856c4e6031c8dadcdd7646ba61be825f31d0000e120001243879e149410ea000134800000038214c2000349a031c6086c00022f40002225f4809160a61200007704a67e400010e09fae280a6182d9000000003af06c4baa4cbb22d30e68967113645440003e70290386bbe61b0000f0649b00000019a057d06d9d64d5ae515e500000008976cd80010e61b80000158a9a401169a774518f142ac36f000000021d803da361b7000000000000000000016865f80000000000e7500000000009fe6a18000196000483000153c0000000000472bc300000006c031d55b110c0005a45e71c80da2b5e26aa0489dc6c559800001a62ce0000fd87ace860f8297de0c11c01c13e9d2e33013e9030000b973389c387f0e43580000073ac781f6a17ce3ecc03aea3c55e263900028c02f2692115b8b0000a4c5d633c1020a460a192eca568210461028a04044551ab114808ef466114042e8f83ca000125a4d70000001c8800028d9d58ef8ebf69a03b800047a154847cb7000024e8c49d14000401a750c8c5055cb2c7d91e5400f38bd8000d2808903448328577598000f4a00019c34018ea00067a83ddba00003a380010940002b380018247425a63020f9a00036193f8edacb64cf31489d092608ea5209704ea2453004f3cf2772e06c1950dc82aa0c1893492b03c949808e64000029ad57c8d65951f141a8d65790adb15647210bdb8d80008701232a84be655a5f203650a6aa9435ad9c0b600001eba440000001d41ba5e32b1d3e4357d274cd851d28b8086efb7562af12660cf44d9d40c04dc53170df58463713d4bbdd39adcc2482e4ca42b365703c60d9680f108bb8948279c73a1d80c64572052b77dbc8e4e11ea64917272614cb8fda26545193802854654234a09a4d0a
  | 31 => 0x4e7650f0bbcddac27371314c000504000083063200049903d46be0ce1418ee0e1095228607bc0000003ec0c3535a3a45971addb749f104c026d5325ef61515a8c1c9165ba31fcb323df2b69818f7a5f64240ff0e6ae880b7800114a6810000000bd249173c0f099829bb76510d00000004fc23b93ee59148103b0594a101d79b04cbadeb43cb8e53c665207190e51fa00074a23f885a52f0002d6cba000042019a99b8295047a559dd48ae0000fb800081a00022ecd3c000741b38c43c08419db760db20003ddaca0358d1e776ab845d4a2002029084d813c3fe08959ca2f446ab1c8ec65ba0f93b6c3049891de11049b0ba97483315bbcadc6182fe8000117584ab48692d6a350a67c17403562d1e49708cc7642a4f4e9c98e4e996b1b6004566d872c000000000000000000005832c8c22b314021724de6000476924dc8c7dd4070b00000527214b9411244880000000c685d200000e53560f85809c2c648736000223125e0004c30000000b025e6aec400000011423645786253ceb0a0aa296b24480006587d75f9165800031e4ac282dad68f063eaeec31607220d2d35c1a6750d6a500094a38130a7016580c800000008c4b8b00402b80009093391655de0836596ad7d326427378acf8e02d234e28f397ec5a33bda20991ca1c0ad37a9b88bd0153bb14a3a45638bb11c3d60ea1931f014689aa5aba1399387f23e320e015020b0b39f2d694162528189194a3476fe8f992361552df2de5c7649f55eb13ca748895b886a41704db29408c86cc67340ca88c8c00bf2328199d8e12e4ca161d840050205a7b5b82c1b58e341c01ad36425b3d8284ebb503ab8c1f8bdc000299da902bb39625c03c2b923e794200005066f6b0a420a00060980000004c51228000000af90000fa4e76000000000000000063f0421352c2e000280400003b746800000028813ca3d55a800013208dc744ea46419fb859655b43200015e8eb9519231128c25400012b80008410000000032c630ddb8dd5a016e5aabbb85eae723d1000041a50e178000000021f00000000000004e3a9740000005899b50bb695e0002fe02ca8ab4199d2c6646c86a8a7f4000000319af1d5be90362dae14842367343a81037205a0cd269988857a572955db2c00765799ddb7a56313a0070c12977530294c94ed0f16092c4718db8733b56da3455065f333d4bc0c72ca00003aae9e000195d04890e12f0c4da040001c30e4da3ac99000015176665e49c8aa865216077301d8000e4c17580015bc73f0001684b76e2275b0001d4064453e0149c228905eb99909d6bf97839c65d025761408000000c7b27b0f2d19c0e65aa37dc0302f173180015580aa4f71f80e360000c2000004e51800000000002506aa9a7cbc4c4a684b9ec0fe9b62379be88247f93ea81851909cb4ab8fe898ecfb6c6
  | 32 => 0x2bd4f1800025a0ae89309ae32a000000069500010f530453377e8000000d8b00019080003c51772e3551cc357470ff45380002762daca704cc5151398b103070680439d2a0e92232b291ba7dc5fa00c8412d2b3661e356c677d0b200003500973e22808000000113aec886eda633cb4c8dbead600000003620f1726b660e34b0627e1f65c84b6a50b8e01634000000068822a4e9561903c1465c65d70001e1010a00000002744853a321fc6dade122c2b20d1a8ac69b9d004de8930002e4054801e0000000000e891b40a7d330183000051800018f00014a80007f100028bce1
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaae84149620400155b08292c4080123ba1f32588100247643a64b102001ccc734c962040014dd0a192c4080029b61432588100055742064b102000aad840c9620400199ae6192c40800eb9a0432588100257540064b102000ace839d5620400159b073aac408002aba10755881000556c20eab102000acf835d1620400159906ba2c40800eb9205745881000537428e8b102000a6d851d16204001c5ea92a2c4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac408003335cc735881001d73408e6b102000ae5811cd62040095d50039ac408002ba600735881000727a9ca6b102003ae68190d62040015cb0321ac4080029ba14435881000536c2886b102000a6e85cc162040014db0b982c4080123be1d62d08100245fc3ac921020018dc83dd942040011bf06bb284080063720d765081001c7a40aeca102000c5c7359542040078e8e2b2a84080122f21d64508100064e39ac8a1020008dd86dcd42040018bccbb9a84080031759773508103564f326e6a102000c9d64dcd42040d399cc5b9a840800237a1d63508100046e43ac6a1020048ec87589420400199ee6b128408003331cd62508100063ab2ee2a102000cb564dc542040019cac5b8a840800a1fa1576108100043fc32ea2102009c3e645d442040018bcc6ba884080231b98975108100043fc3aca210200087d87594420400187ceab2084080030f5d564108100062f3aac62102000c5d7558c42040018dceab1084080031b5d562108100143f42aeda0020048bd845db400403d0ff0cbae80080270f99175d00100062f31aeba00200687f8759740040010fb0eb2e80080030f9d564d00100061ebaac9a002000c5e7558f40040018baeab1e80080031b9d662d001000636bacc5a002000c6e7558b40040018daeab1680080122f213765001002476c12ed900200287c85dd920040031b907bb240080123b20b764801009c3ec36ea9002000c5e63dd520040a58dcc5baa40080021fa1d65480100343e43aca9002000c5c73595200400187eeb32240080030f1d664480100064e39cc89002000c3f755912004001878eab224008003271cd64480100946ec36e69002000c5e65dcd20040018bacbb9a40080032799373480100064eb26e69002051cce62dcd20040011bd0eb1a40080163721d63480100062fbaac69002000c5c7558d20040018deeab1240080031b1d5624801000667b9ac49002000ccc7358920040018e8ebbb220080031de1776440100063a42eec8802000cb784dd9100400196909bb220080031dddb75440100053b43aca8802038a748759510040098eee0b2a200800f9cdc1654401002739102ca8802000cb776dd11004001c6acbba220080032ddd874440100069a3a8e88802000e35651d11004001ce2ca9022008002f4e0d2044010
  | 1 => 0xcaa0080880021fe1576481100143e42aec90220008bf845d9204401317908bb2408800237e0d764811000c6e41aec902206e87e86dd520440db0fd0fb2a408810a1f21f65481100062e39eca9022000c3f75d912044001878ebb224088003271cf64481100061fba8c89022000c3c751912044001938e632240881072d1c464481100062fb2ee69022000c5c65dcd204400193ec9b9a40880032719373481100066639ec490220048f686dc52044001968c9b8a408810b1d9db65841101f65b3b6c90822009cb6761921044001c68ca32420880030fdd274594103653bc0ae8b282003a74815d165040d74f700ba2ca080129e20174594100062fb9ce6b282003a768190d65040014eb0321aca080021fa1c43594100043ec3886b282000a5e83dc965040014bb07b92ca080028fa1072594100051ec20e4b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282000e4d320c965040074ed02192ca080029d60432594100253d40064b282000a79800c9650400d0fd0f982ca080021f61f30594100070fa9ca73202000a9e83d4a640400153b07a94c8080262fa1c52990100045ec38a532020098be870ca640400117b0e194c8080028fa1432990100051ec28653202000e8d320ca640400756d02194c808002ad60432990100255d400653202000ab9800ca640400147d0b984c8080028f617309901001c7a40aeab2020048f8805d5640400917d0faa2c8080030fdd754590100161f3aca8b2020048bc87551640400957100aa2c8080122fa1e435901001d5b40c86b2020048bc8750d640400147d0a21ac8080028f61443590100061fbaceab202000ab7815d5640400756902baac808002aee0175590100255c402eab202003ab6819cd640400156b0339ac8080028fa1473590100051ec28e6b202000e1f5394d640400153f06b92c808002a720d725901001d5a40ae4b202000a3e851c9640400147b0a392c808002a7a0f52590100054ec1ea4b2020008be87149640400117b0e292c8080022fa1c32590100045ec3864b202000a3e850c9640400147b0a192c808003a34c8325901001d5b40864b202000ab5810c9640400957500192c808002ae60032590100051f42e60b202000a3d85cc164040018beeb3aac60800297a147458c100052ec28e8b182000e1f5495163040014bd0a392c608002976147258c100054f420e4b182000a9d841c9630400199ae4392c60800eb5a047258c1002d6ac08e4b182004ada801c9630400b5b300392c60800237a1f5258c100046ec3ea4b182000a9e84149630400153b08292c6080038bd52549881000727a9ca73102000a6e8510e62040014db0a21cc4080029ba17309881000536c2e6131020048ee87d49620400159d07a92c408002b360f52588100247643aa4b102000
  | 2 => 0xc50191100054f418a03222000a9d83140644400155d04280c888002ab608501911020d5b408a03222000ab581140644400147d0b980c8880028f617301911020d5b40e603222000ab581cc0644400147f0a880c8880028f215101911000667b9865b122000ae5810cb62440015d300196c4880030fd9674989100061e32ce93122000c3f655d26244001878caba4c4880030f9d764989100061ebaec93122000c3e75192624400187aea324c48800a1fa1b75589100043f43ecab122000c5c73d9562440010fd0e32ac488003171cc65589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f19474589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100045fc22eab1220098bc845d562440011bf06baac4880063720d75589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100043fc2ae6b12200287c855cd624400117f08b9ac4880262f211735891000477c12e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000ccc73dc96244001968e9b8ac4880023be1d62189100056641ac4312200087f855db42440050f90abb684880222f21176d091004e5c324e1a1220038f8865c342440010ff0abb4848800a1f21576909100143f42eeca12200087d85dd942440031bd073b284880023760e76509100043fc2aeca12200287c855d942440011bf06bb284880063720d76509100047bc0aeca122000c5c73d95424401117d0fb228488003271cf64509100062fb2ee6a122000c5c65dcd424400193ec9b9a84881ab2719373509100143e42cec212200087f855d842440050f90abb084880021f219751091004e1e322ea212200087f87d9442440010fb0fb2884880030f9d764109100061ebaec821220048f4865c44244013968c8b8884880272e192701091001c7c432e02122009cb8649c341440018f0cbb8282880031e19470505100065db20e0a0a206e87c865d74044013878c8bae808810a1fe1f65d01100043ec3ecba022000c3e75d93404400187aebb2680880272d19171d01100063c32ced2022009aba86d924044001974edb2480880038ed9464901100071c328c9202200087f855d940440050f90abb280880fb2d1c764501100063a32ee2a022042c7876d954044013970edba280880fb2e1db645011004e5c3b0c8a022000e386519140440016e30a38a80880fb6cdd071501101f4dd43e82a022003cb876d0540440073710ea0a808800f2e1d9415011001ed838a82a022009ab88650040440afc7
  | 3 => 0x5b2a2000a3d840cb6544001c9a64196ca8810a9da0432d95100053ac0865b2a2000a7a800cb65440014f300196ca880e29ea0371d95102143f43e61b2a200087d87cc3654400187aebaa6c888002ad60754d91100161e3aca9b2220028bf87553644400317f0ea1ec8880028fa1443d91100051ec2887b222000a9e83197644400153b0632ec88800387a0c65d91100070ec18cbb222000e3581197644400147d0b31ec8880028f61663d91100051fc2ac7b222000a3c8558f644400155f04b1ec888002ab20963d91100071a32ca3b222000c3d751d7644400153d063aec888002a760c75d91101f55b408ebb222000ab5811d7644400147d0b39ec8880028f61673d91100070fa9ca7b222000a9e83dcb644400153b07b96c8880028fa1672d91100051ec2ce5b222000a9e83d4b644400153b07a96c8880022fa1c52d91100045ec38a5b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000e8d320cb644407d56d02196c888002ad60432d91100055d40065b222000ab9800cb644400117d0fa8ec8880022f61f51d91100051fc2ae1b222000a3c855c3644400117d0e286c8880022f61c50d91100054f418a1b222000a9d83143644400155d04286c888002ab60850d91101f55b408a1b222000ab581143644400147d0b986c8880028f61730d911004e1e322eb3222000c3e75d92644400187aebb24c8880021fa1f65591100043f438cab2220008bf845d564440011ef02baac8880023ee0175591100061fbaee8b222000c3c75dd164440010ff0ab9ac88800a1f21573591100045fc22e6b2220008ef825cd64440111d904b9ac8880031d1d771591100063c3aee0b22206ec7970194644400117f0eb20c8880028fe1564191100051e42ac83222000c3e76d94644400117b0f328c8880022fe1d65191100054f418ca3222000a9d83194644400187cec328c88800387a0c65191100070ec18ca3222000e358119464440dfc7620328c8881bf8e04065191100045ec3cc63222000a3e8598c644400147b0b318c8880022fe1d63191100051fc2ac63222000a3c8558c644400155f04b18c888002ab20963191100055b434a23222000e34659446444001c68caa88c8880038ed9570191100071c32ae03222000e1f5394c644408356d02298c888002ad60453191100054f41ea43222000a9d83d48644408356d03a90c888002ad607521911004c5f438a432220008bd87148644401317d0e190c8880022f61c32191100051f428643222000a3d850c86444001d1a64190c888106ada0432191100055ac08643222000aba800c8644400157300190c8880262fa1f51191100045ec3ea23222041e3451544644400157700a88c888002ae20151191100055bc0aa03222041ab481540644401317d0e280c8880022f61
  | 4 => 0x1480050fd0bbb282900021f617765052000c6f41eeca0a40008dd83dd941480050f90b3b082900063720e761052001c76414ec20a40048f8809d841480010ff0abb0829000a1f21576105200046fc1aec20a40018dc835d841480010f90cba882900031718d75105200043fc3eca20a400087d87d9441480018bce7b28829014b1b9cb65105200046e432e620a4000c5f655cc41480018b8cab98829000237e1f63105200046ec3ec620a4000c5e75d8c41480018baebb188290147339cb631052000637b2ae420a4000c6c655c8414800195ec8b90829000333d8d72105200066631ae420a4000ce572d8441480018f6cb38082900031e19670105200066db1ce020a4000cd8639c041480018f6cab8082900031e19570105200065db22e020a4009cb8645c041480019b6c6b8082900033618d701052000679b0ae020a4000ccc639db21480075c902b2642900021f21975885200062e31aeb10a400087d87d9621480018bce7b2c42900023721973885200062fb2ae710a4000c5c655ce21480011bb0fb1c4290003179d763885200062ebaec710a40038ec875912148001cceca30a42901b61f21975d01200062e31aeba02405287f87d9740480010fb0fb2e8090003179d763d01200062ebaec7a024000ccc635cb40480010ff0abb2809000a1f21576501200046fc1aeca0240018dc835d940480a58dcedb2c4090147339db63881200245e43aa8b2040048bc8750d640800117f08b9ac2100262f211735842004476412e6b0840048f48754561080091e90e98ac21000e3b609761042001c7cc02ec2084000c6c75dd92008001998e7bb240100031bddb754802000667bb6e690040008ef825cd64c40111d904b9ac9880022fe117358b1004c5e422e6b1620008df835d942c40031b906bb2858800e3b21d6250b1020c5fc3ac9a062003cb47159140c40091790eaa2c90800a1fa1f7558a100046fc1aeab1420018dc835d562840010fd0e3aac50800637a1f7358a100062fbaee6b142000c5c75dcd62840010ff0ab9ac50800a1f2157358a100046f438e6b142000c5f751cd62840018b8ea39ac50800b1b1d65258a100247643aa4b14200087f855da42840050f90abb485080021fe157650a100143e42aeca1420008df835d942840031b906bb285080fa2fe1d64d06101f4dd43e82a0420049b8875054084007b60e2a0a81080021f61e63d95100051f424c7b2a2000a3d8498f65440010ff0eb1eca880028fe1163d95100051e422c7b2a2000a6f8258f65440014d904b1eca8802e9da1b71d95100061eba0e9b2a2070a7a801d365440854f3003a6ca88003175cc73d95100043f43887b2a200087d8710f654400147d09396ca880028f61272d95100052fc1ae5b2a2000a5c835cb65440010fd0e196ca880021f61c32d95100051f4206
  | 5 => 0x21fa1f65591200062e39ecab22400087e8719564480018b8e632ac89000317d9773591200062e32ee6b224000c5f7518d64480018b8ea31ac8900031dd9771591200063a32ee2b224000cd463dc564480018eeca38ac8900031d19471591200066a318e2b2240008df835d564480031b906baac8900023de05755912001c7a40aeab224002c3c7595164480e7968e32a2c89000a2f21d54591203965a38aa8b224000c5f75dcd64480018b8ebb9ac8900021fe1573591200143e42ae6b2240008f7815cd64480071e902b9ac89000317dd473591200062e3a8e6b224000c7775dc564480018e8ebb8ac89000335dcf71591200066a39ee2b224000c77751c564480018e8ea38ac8900032ddd071591200066bb98e2b224000cd4731c5644800117f0eb20c890002ad20564191200062f3b6cbb1a40008dd8799763480014bd0b32ec69000237e1d65d8d200054f420cbb1a4000a9d8419763480014bd0c32ec690003179d865d8d200070f420cbb1a4000e1d841976348001c9b0432ec6900023761e64d8d200052f42cc9b1a4000a5d8599363480011bf0eb26c69000297e1564d8d200052e42ac9b1a4000ad78159363480015a902b26c6900039319652d8d200062eba8ebb1a4000a9e841d7634800153b083aec690146b3a0875d8d2000566c10ebb1a4051ace82dd3634800159b05ba6c69000297a1674d8d200052ec2ce9b1a4000e1f54953634800153d09b96c690002a761372d8d2022d6d406e5b1a40008de87d4b63480011bb0fa96c69000297a1671d8d200052ec2ce3b1a4051ace821c7634800159b0438ec690002a7a1351d8d200054ec26a3b1a40008de8714763480011bb0e28ec69000237a1c50d8d200946ec38a1b1a4000a9e84143634800153b08286c690146b3a0850d8d2000566c10a1b1a4000ad68114363480015ab02286c690003171cf655092029716216caa1240008de86dcd42480018becbb9a849000317197735092038c6f43ec6a12406a8dc87d8d42480018bce7b2cc290003179cc65985200062fb2ae730a4000c5c655ce61480018bcebb1cc290003175d763985200062f3a8c730a4000c5d7518e61480050fd0dbaac2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c3f651d16148001878ca3a2c29000637a1b73585200062fb2ee6b0a4000c5c65dcd61480011bd0fb1ac29000317dd763585200062e3aec6b0a4000c9f74d8d6148001938e9b1ac29000237a1c63585200062fba8c6b0a4000c5c7518d614800193ee831ac290003271d063585200047bc3ac230a4000ab48458461480010ff0abb6829000a1f21576d05200046fc1aeda0a40018dc835db41480010ff0abb4829000a1f21576905200046fc1aed20a40018dc835da4
  | 6 => 0x53bc0ae0b2e8000a74815c165d00010fd0f982cba00021f61f30597400161f3aaa8b1680048bc845cd62d00131dd0f992c5a0026aba103258b4000666b9864b168000ae5810c962d00015d300192c5a000a1fa1772587400043ec2ee4b0e80018de83dc961d00011bb07b92c3a000a1fa1576887400043fc32eb10e800087f8759621d00010fb0eb2c43a0003179cd65887400062f32ae710e8000c5d655ce21d001387ce8b2843a00030f59574087400247643aa4b148000a6d850c9629000155b08192c520003335cc3258a4000572c0864b148004aea800c96290001998e6b12852000637a0f72586400046ec1ee4b0c80048f4875456190013974c0bb083200032ed9570106400065cb2ae020c803ecbb615c0419007d972c2b8083200232b98974c86401f45fc3ac3a04803ecb67158740900011df0eb10c4a00021fe1572d85400143e42ae5b0a80008df835cb61500031b906b96c2a0002ad61351d85400056ac18a3b0a80018f7874c761500011ef0eb08c2a00029d215611854004e5d404eda0a8009cb9809db415000756d0db0a82a000e3ba0a76c85400043fc2aec10a800287c855d82150007968c2ba042a000f3c185700854004c5e432e3202803ecb4615c64050009b6420b8c80a000237e0d755884000c6e41aeab1080018de87dcd62100091d90ea92c420007331ce32588400247643a64b108001ccc734c9621001317908baac2200262f211735844000477c12e6b0880088ec825cd61100091e90ea8ac2200123d21d315844001e3b30aeb1088003cd6615ce21100018eaeab0c4220003355cd61884400046fc1aec90880018dc835d92110013958e8b1242201062f21d615004020e5a38ac2a008004eb21058540100111790eaa2c9900123b20973593200445e43a86b2640088f4874c561c801387cc8ba883900030f5d5641072004657392c820e4009c9e645cc41c800193ac8b9883900272e99170107200065cb22e020e4009c3e645d740c800187aeab2681900122f21d54592200245f43c86b244004aba8090d648800147b0a21ac910003271cd6450a200247a43aa2b0c4003ab48159141880078ecc2bac43100031d5d561886200043ec3cc7b2a400087f8758f6548001cb30031eca9004e9ba1b72d95200072c31c61b2a4052a78864c3654800187ae83a6ca90003175cc73d95203a53d400e7b2a4052a79801cf65480010fd0e21eca900021f61c43d95202353d406e5b2a4052e4c324cb65480014bd0738eca900029760e71d95200051fc22e3b2a4000a3c845c765480a54dd0438eca900029b60871d95200043f43863b2a400087d870c765480a50fd0f986ca900021f61f30d952002476c16e7b224000c5e73d9664480018bce632cc89000317d9573991200062e32ae73224000c5e7518e64480018baea31cc89
  | 7 => 0x3954d4960104015b507a92c020802b660f525804101d7940ea4b008200af181d496010401c72a8a92c020826aea1052580410055cc20a4b008200abb844c9601041357108992c0208023ea1c32580410047cc3864b008200a7a850c960104014f30a192c020826aea1032580410055cc2064b008200ec9320c960104075e502192c020802bc60432580410445e43aa8b2642088bc8750d64c84050fd0bb82c9908021f61770593210066639eeca1642088f8874c160c840187ee93a2cb1080317dce735962101d3b40ce6b2c4278a75819cd65884074ed0321acb108029d60643596210043f43886b2c420087d8710d65884ef4ef02b92cb1099b930c932596210051f420e0b2c4200a3d841c165884014bd06382cb108029760c705962133537410e0b2c4200a6d821c165884074ed02382cb108929d60470596210043f43e60b2c420087d87cc165884074ed02182cb108029d60430596210143f42ee0b24420087d85dc164884018beeb3aac710802a7a127558e210054ec24eab1c4265ace829d5638840159b053aac710802b3e097458e2132d66412e8b1c4200a5e851d163884014bb0a3a2c71080387d525458e210054fc22e4b1c4200a9c845c963884ed5af02b92c71080237a1f5258e210046ec3ea4b1c4200a5e85dc163884014bb0bb82c710802b3e097058e2132d66412e0b1c42008de8714163884011bb0e282c710802a7a105058e210054ec20a0b1c4265ace82141638840159b04282c71080eb5a045058e210056ac08a0b1c4200c5c7359542884078e8e2b2a85108023761b7350a210062f32ee6a144200c5d65dcd42884d51bd0eb1a85109c63721d6350a210063ab2ee2a1442028bf87553644840147b0a21ec8908021fe1570d91210143e42ae1b2242008df835d564484031b906baac8908023ee0175591210247c402eab2242008bf845cd64484011df04b9ac89080327dd073591210066639ee4b2242008bf87590644840153906b20c890803271cf645092100596c28c8a12426accc76dcd42484011bf06bb282908063720d76505210047dc3ac030242038bc8755164084111d904b9ac81080e2f21d43590210143f43eeab00420087f855cd60084050f90ab9ac01080b1e1d6505802101c7c43aa0b0042038f8874c160084018bee739acba000297a0f72597400052ec1ee4b2e8009a3e841c965d003d47b08392cba00021fa1c32597400043ec3864b2e8009a3e840c965d000147b08192cba0003934c832597400053b40864b2e8000a75810c965d00014f500192cba00029e600325974004d1f426e2b2e801ea3d84dc565d001347d0938acba01828f61271597400053dc02e2b2e8075a78805c565d00014bd0638acba00029760c71597400063ab88e2b2e800087e870c565d00010fb0e18acba01768fe1170597400
  | 8 => 0x839ac420803335cc735884101d73408e6b108200ae5811cd62104015d50039ac420802ba600735884104d57426a6b108200aad84d4d6210401c5aa9a9ac42080393d4e535884100716aa2a6b108209aae8414d621040155b0829ac42080eb9a04535884100572c08a6b108200a6f855c162104014d90ab82c420826ab211705884100567c1ae0b108200acc835c162104075c902b82c420826aba13505884100556c26a0b108200e2d5494162104011dd0e282c4208023b61c505884104d57420a0b108200aad841416210401c5aa8282c420802b3a0c505884100566c18a0b108203ae68114162104015cb02282c4208029ba17305884100536c2e60b108209aae84cc1621040155b09982c42080eb9a07305884100572c0e60b1082048f8805d660104091f100b9cc0208021fe1572980410143e42ae530082008df835ca60104031b906b94c0208123e20172980410053d42e613008200a7985cc260104014f50b39cc0208029e61673980410072da9ca73008200a7b855ca60104014f10ab94c020802b6e0d72980410056c41ae53008200ada83d4a60104015b307a94c020826aea1052980410055cc20a530082048fa870ca60104011f30e194c0208029ea1432980410053cc28653008209aba840ca601040157308194c020803b24c8329804101d79408653008200af1810ca601040157100aa2c02080e3ea1f505804104d5d426a0b008209ab8849416010401c72a9282c02080e3e21d505804104d5c422a0b008209aba841416010401c72a8282c020802b6a0c50580410056cc18a0b008200aea8214160104015d304282c02080ebca04505804101c7d43e60b008200a7a85cc160104014f30b982c020826aea13305804101d7940e60b0082038f8874c1601041357108982c020826ae213755804104d5d424eab008200ab9849d5601040157708baac020826ae211755804100579c0aeab008203af0815d56010413575083aac020802ae61075580410056d418eab008200ad9831d560104015d5043aac020802ba608755804101d79408eab008200af1811d560104015710eaa2c020826aee15545804104f1dc2aa8b008200e3b755516010401c70eaaa2c0209caaee0554580413955cc0aa8b008272e3b5155160104e5c72a2aa2c0208029ea1673580410053cc2ce6b008209aba849cd60104015730939ac02080ebca06735804100578c0ce6b008200abb845cd601041357108b9ac020826aea1353580410055cc26a6b008200e3954d4d6010401cb6a729ac0208038e551535804104d5d420a6b008200ab98414d60104075e50229ac020802bc604535804104d5d424e4b008200a7b855c960104014f10ab92c020826ae21172580410056dc1ae4b008200ad8835c960104075e102b92c020826aea1352580410055cc26a4b008200e
  | 9 => 0x71980420143e42ae330084088f8874c160108011bf06baac5a08063720d7558b4100c6f43ee6b16820087f855ca60904050f90ab94c12080237e0d729824100c6e41ae5304820287e87dd56090405878eb2a2c12080b0f1d554582410043fc2ae6b04820287c855cd60904011df04b9ac1208223b209735824100556c2065b128200ccf730cb62504015cb02196c4a08023be1d62189410056641ac4312826ad9441dcd4250401998e7b1284a0802ae61050d814100578c08a1b0282008fb8758060504014f10ab00c0a080237e0d721814100c6e41ae43028200c5f739cd65104014bd07b92ca208029760f725944104d1f420e4b288228a3d841c965104010fd0e192ca208021f61c325944104d1f42064b288200a3d840c96510401c9a64192ca2080e9da0432594410053ac0864b288200a7a800c965104014f300192ca2097a8fe11705944104d1e422e0b28827ca77815c165104074e902b82ca208268fa1070594411451ec20e0b288200a5e831c165104014bb06382ca208029ba08705944100536c10e0b288203a76811c165104514eb02382ca208021fa1f30594410043ec3e60b288200c5f759d5631041353d093aac6209eea76127558c413d54fc22e4b188209a9c845c963104014bd0a392c620802976147258c4104d4f420e4b188227a9d841c9631040199ae4392c62080eb5a047258c4113d6ac08e4b188200ada801c963104015b300392c62080237a1f5258c410046ec3ea4b188209a9e84149631040153b08292c62080297a177058c410052ec2ee0b188279a9f845c1631041353908b82c62080237a1c5058c410046ec38a0b188209a9e84141631040153b08282c620802b3a085058c4100566c10a0b188203ad68114163104015ab02282c62080393d4e539884104477438a131082008ed87142621041355d08284c420802ab610509884100567418a13108200acd8314262104075cd02284c420802b960450988410053742e613108200a6d85cc2621040587ceaaa2c4208262f211735884101c7743ea4b108209aae84d496210401c5aa9a92c420802b3a0f525884100566c1ea4b108203ae681d4962104071d90ea92c4208038b551525884104d57420a4b1082038ee87cc962104071d90e992c420807331cd32588410053742864b108200a6d850c9621041355d08192c420803335cc325884101d7340864b108200aea800c962104015d300192c420826aba12755884100556c24eab108200ace839d5621040159b073aac42080eb9a06755884100572c0ceab108209aae841d5621040155b083aac420826abe15545884104f17c2aa8b108200e2e755516210401c5aeaaa2c4209cb8bd45545884139716a8aa8b108200aaf845cd621041355908b9ac4208029ba14735884100536c28e6b108209aae841cd621040155b
  | 10 => 0x20000100000000803800004000000330100000001d0700380200000409c0601500203001003002004000000940940780002c00400806004008040000120000280404c0040b82600c0000180c010010000000040100600200000000000010000008060000180200f040014020010080000000600c0040000001200c0400300200000804002014000020000800781404a008008000140500601001a0100d80b004008000060000140982200a0040200201c0b00000701602001000018010010020160240000b0480141781400a044028010120000280200202001813044048130040100340a00000000c0a82a062048020150080000301c02c000008000320140681900e01c00000000044110000080000006401e034078030020200080101601c060000020080080b0180040280002401802004000064008100080240000800002c07800000088f4874c561908050fd0fbaac1210021fe1573582420143e42ae6b0484088ec825cd60908111f10e982c1210023761e65d8d420056b40ccbb1a8400ad58199763508011bf0eb2ec6a11a6a721954d8d420062eba8ebb1a846aa9e841d763508d353b083aec6a11a6b3a0875d8d4235566c10ebb1a846ae1e54d5363508d51bd0fa96c6a10023761f52d8d4234f27296a5b1a8400a5e859c763508014bb0b38ec6a11a6b3a0871d8d4235566c10e3b1a846aa9e84d47635080153b09a8ec6a100237a1c51d8d420046ec38a3b1a8469ace82dc363508d559b05b86c6a100297e1570d8d420052e42ae1b1a84008de8714363508011bb0e286c6a11aaa7a1050d8d420054ec20a1b1a8469ace82143635080159b04286c6a1002b5a0450d8d420056ac08a1b1a84028f78754761508078e8c2bacc2a1003179d763985420062ebaec730a8400c5e7518e61508018baea31cc2a10031d5d761985420046f43ec6b0a84008de8718d61508e399ae4318c2a10023de1d61185420161f3aaa9b0284018de86dcd60508d31b90db9ac0a100237a1f63581420062fbaec6b028400c5c75d8d60508011bd0e31ac0a100317dd463581420062e3a8c6b028400cd763dc560508019a8c7b8ac0a100335d8c71581420066a318e2b0284008fb8758060508018bee739aca211f69be09735944204536412e6b288409a3e84dc5651086147b09b8aca2100297a0c71594420052ec18e2b288400a3f844c565108134790898aca210029be0931594420453641262b28840087e870c565108010fb0e18aca210268fa1070594421851ec20e0b288400a5e831c165108014bb06382ca210229ba08705944218536c10e0b288400a76811c165108014eb02382ca210021fa1f30594420043ec3e60b288409a3e848c1651080147b09182ca210229ba0a305944200536c1460b2884088f4874c561108135690898ac2210021fe15
  | 11 => 0x7a4741e84842001543a50e75731f00000002ab0470005c219451b0c709a00057709b1d63ef40d0000004ae0001de47757802642b3c10000c01702874c609700053b51410200054100006129545c0640c25b525d4501202563d20e426c47c0000004603244134f52d521b2c531d0000b74591010725024bb0002f30001b80000003053e63b123019100030c00000057500000032226b51900048a0000004a12492682360df0001c40cf2ed0002580944a40000001e015a0004d919d5200004e34582880004ea29217f4ce2ad39e08d4922e300826a4c302e4222ac12d1cc4bc07a0001a02e823849e0000003af0eb1371634fa16b11300000000059c5c05b72ce2bf33a55b15510a5c60003bd1b339b1f201406057f31a46829900044600054e14d1b40001ad0003354524dd1b20003b40000000ac1fe3183cf2d93442392dd57924100000000041f00000041a2b65b14b637e16932716f4870001e510815b4390f25593983a94c432608f1521d70f51fc2a93a34d55a800058105c1260000000960005b42c03e034954f4af07500d4e039755e4e93791f85600000f74f73555444a623a4800790af3334363f43280001cb3c93ee1a907739d0005a43dc3022e90000000380a820d1251963131b53a447f5914ca0912b71620ea4535340b046b01a43f55118c46e0005a335243d00027837d00000000024b0fa26700003e0004124074e82622740da11803d0004a82703823044cb2e042f5104661603190c50000d630b26e00043c25100000019e24336500025900e3f23d849345a20300047e18d4211972070ad07c1ae03328f48b0654c00004495bf1170003bc3a10002fd58517249c51c06934e25000035a0004df0002d74760005170e04734080294340e63cb25b0001cd0005af4100003960b64cc31e2af4354b81153e43675ba06720900305c000060000420600200001e040000020000140002502200005002006008020020040300480703a0081482d00400c0100202e0280100100207c0080400206002003008000000120200000c80100800003002012028008030000040380d00203800001000010118020120000080e00007c0506d0020181a00300400802824000078098070020040280203c0680700b00200402006010008000020040000000c06200c170320060000b0020240000a80100e00c0480000800802005000010010060040880e8010040340000a024020028040020440000101c02c15009004000080210400480380301200003009014000000020040040480100a0000280200201c0000200c0140300d0021340280301c0100080100e04c260210020540380103a03011008000000088050000080103601a000058030100000000201c020000000340080001e0080040100001001c098130240280400701a020018000040000b8
  | 12 => 0x1f42e65091402ff1060004641d851145b04600024c59f00a3f355500042400034700031654c2904da1e902133c56d4ee0192aa57a3205634dc09558906c36159b2803b81c01f72853152252c446f0324822085a65b82550002145bd4152405254be0c13e938f00005a0f000050d3c613623f30129d2981485be2be53e02f3fa5302d850c02716817620402d0fc17e21245e58b4790001bd0680ef45d0000ec1c132d1d93bb0de4a93eb17549d0005c921616d59d42017952d06f23336b15330a57133d0002fa22e5b30840b80cb5ad33718f2c71a258300000144318b1db3ca22c4a70bb20c4970001821dc3d335b13b3480b23460003ab0240003aa0ee00000054b3402760000002132b000029b5050000dc44b00058700000012c00024500040524613000050004b5a73d403a3d136936f0001d423c00058a0000ce00042c18400000000000000005516700037c0002425464e14851d30162b843b53a1983100a62a213c00048d0002635864fb20140e5492230003ac29709f08036000052615f0bd3815973c25953872284fc4672a801f53356a32a00009000017c0001732d60002b93fb0000f63fc4044de54351d0ff2fb11f00000014c30752a0c456848c5a91922341c730d10012a4aa0c83414283cc01b5231b000c0a228d0001a300000032c00048336200000010c0000003a000009850a55f0002c20000000004301640002942645270392db30e4b700037132325e15659627e1312774f334f4230e91a81411853ce4c805131b1104b13cd07d09e36457636315d57b1475285290375b23e224f06639450140f29e51e4d842920b0d036e11910732128e1bc1ff04824755d02229c06317b2911143b545659a4405ca1e23b71eb1283e731139f2654513c037444135052c00020204e4171ea0002f850807f3065a24eb26f53f42d08825f0f322656e3df10505401e4471581e70833a61af38b0b14695381230502cd0f85a010901c3830f12531d011243829f37544a22b4440ae14a34333443e4d035e25c33e3394f14ac3f108708b2104ff00028c4250201e32dc00000000003b4882a44cd00057d1ab00027f0005a50aa33f4f800000000017700000031f01d4d30005c410f0000c300000003c3382113c302a18a01024d23700004016c5224b221d14f3dd1390c946a36c00000000000041b4b400050659e00000017d0000250001900005ae4f40002b22b435d27c0350d927b3f80000000001832a73fd34c00000000000000000000034d00000016600049a0003da0000000001570001ba31715c0170ba0d83e54650a044d29303f42e0414db3362f642627335408c5185125bc5b05453a80003730004ef5073bf0711e61a40ca0000001df02355304f17114e21f2d40894035c51dd3d507423e4314570000280001863ed30836a0002b30d42
  | 13 => 0x1031cf2712722d25bb4ab19520e5425ac12f2f90d200b4f61221805b63c400001314b3141a756250e3b300040c1b13590000000002f02b50000000000000300000002840005474f919f4945992a05b909c3d04625580994ec39a1ac2ca0004452524e20ab03605240b4a00004e70000000e208e38400056b5c80d703113d3e30000005c30005741c61bf1a62bc00041e38c4990a45945644c51be2822cc34202b4000000041ed0cc2353c841111b2eb47207b2052c95241c94e501507e2f44d42cf38d35809d0bf50f25a0bc0b50002184814320000ed4bd04d48620619c0033c700032b00055c4913db0f928941c3ba16a0000005845aa1ce4020000822ba0021445702e75922bd3ec00f10d00005600052e37600000005d55213e40908541422a09300051323b4183f60004164750000001fa22101238e4e62d12ae1592275030001241a100000010b0d516e06e19922f49b0005c158248e0001420a700055732f1fd22d00035c4983770cd00013554a1aa0074fd4ed5661490a906d27553c57e3310001c53123003b252f4a30003f532e18715e26d2a51935c72a30000000002441f658f3854481040e512e05b52b33b58e4783800db1d140600939c1ca21737813a2e13f93f71881c25211344715801332ee1610fb56f2a63e824813239148f1741f517a56922425418950b4c721c2f511605911106b1b910e4610573d90443de3512fc2ec5ab0f439924a2c83933092602311a513f34a05f1fb39000000021e0000001c32961f107313849543318e1ee34551a0000004d649f3d700045f3572fe0004c246d0d10000000a50005500002e427d5722f15040585350004c100058d1da3a72c63880d326900006a56142a0004cf4e44890004d700000037a5a13be1653531510765154b52df0b331c29a2861b647d04515008a11a43747044e2cb1810530184540e156c12b5160e31d22323b63fe0782bb24e3b00a14d253147b21a17858800055a53d3c504c5360001ef1292f73663684b044f2831d50003ea0000493b95980e855422200035f05e2a12de2570000a338640a2812ef0001f922000040126104a4272d02e20004f24d13e10111c856512141d3ff4fe11d28a3034b92c337057c59308620a0344c93722150620424b33563295371e449639500020f54d0000c61f30064a50004ba0003890005480000000003ae56723d00046c08151f00011e11c02c37f44c2ea2da2f20003a20be4a200055634b1462660fd36d3921ec2d328b3ad2c10922295320001e10dd4f01bb00527946353921938a33258c4ad43a1434190fe14519b19a3d633045549047a3f01b71270b937b5403250b42e530f4bf0000434420702b159
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x52441c30e0201020006800000002a601201688018800001e0180030040c20068355183d49621040160d939d554588410058964675551621040182d87550505884100683551831416210401a2554604505884100686551831416010401a295460850580410058664c755516010401629921d554580410058c644755516010401a195460f52580410068c55181d496010401a0d8460865d8d200068560d811976444001a158360465191100058564c65544644400188d874c832191100042e65c805446444001434975947444010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4e
  | 7 => 0x124c
  | 8 => 0x3
  | 9 => 0x5
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124e
  | 13 => 0x138c
  | 14 => 0x138e
  | 15 => 0x8c
  | 16 => 0x8e
  | 17 => 0x128c
  | 18 => 0x98c
  | 19 => 0x98e
  | 20 => 0x128e
  | 21 => 0x150c
  | 22 => 0x150e
  | 23 => 0x10c
  | 24 => 0x10e
  | 25 => 0x130c
  | 26 => 0xa0c
  | 27 => 0xa0e
  | 28 => 0x130e
  | 29 => 0x180c
  | 30 => 0x180e
  | 31 => 0x20c
  | 32 => 0x20e
  | 33 => 0xb0c
  | 34 => 0xb0e
  | 35 => 0x140c
  | 36 => 0x140e
  | 37 => 0x154c
  | 38 => 0x154e
  | 39 => 0x28c
  | 40 => 0x28e
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x148c
  | 44 => 0x148e
  | 45 => 0x184c
  | 46 => 0x184e
  | 47 => 0x40c
  | 48 => 0x40e
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0x160c
  | 52 => 0x160e
  | 53 => 0x188c
  | 54 => 0x188e
  | 55 => 0x94054
  | 56 => 0x94056
  | 57 => 0xa1254
  | 58 => 0x124956
  | 59 => 0x95256
  | 60 => 0x95314
  | 61 => 0xa0956
  | 62 => 0x130a
  | 63 => 0x130956
  | 64 => 0x94a14
  | 65 => 0x10a
  | 66 => 0x134a
  | 67 => 0x139256
  | 68 => 0xa1256
  | 69 => 0x98094
  | 70 => 0x98096
  | 71 => 0x128994
  | 72 => 0x128996
  | 73 => 0x99296
  | 74 => 0xb0994
  | 75 => 0xb0996
  | 76 => 0x98b16
  | 77 => 0x98b14
  | 78 => 0x154994
  | 79 => 0x154996
  | 80 => 0x99556
  | 81 => 0x12cb
  | 82 => 0x134b
  | 83 => 0x151296
  | 84 => 0xb1514
  | 85 => 0x150b16
  | 86 => 0xa0114
  | 87 => 0xa0116
  | 88 => 0x148116
  | 89 => 0xa1316
  | 90 => 0xa0b96
  | 91 => 0xa0b94
  | 92 => 0xa1856
  | 93 => 0x181316
  | 94 => 0x29316
  | 95 => 0x149316
  | 96 => 0x180b96
  | 97 => 0xd0b14
  | 98 => 0xd0b16
  | 99 => 0x160b14
  | 100 => 0xb0d14
  | 101 => 0xb4b
  | 102 => 0xbcb
  | 103 => 0xd1554
  | 104 => 0xd1556
  | 105 => 0x18cb
  | 106 => 0x15cd
  | 107 => 0x5816
  | 108 => 0x5856
  | 109 => 0x14b
  | 110 => 0x14a
  | 111 => 0x14112
  | 112 => 0x95316
  | 113 => 0x3cd
  | 114 => 0x104a
  | 115 => 0x194a
  | 116 => 0x992d6
  | 117 => 0x180056
  | 118 => 0x141554
  | 119 => 0x141556
  | 120 => 0x140b56
  | 121 => 0x29314
  | 122 => 0x29614
  | 123 => 0x29054
  | 124 => 0x29256
  | 125 => 0x41716
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2036
  | 6 => 3885
  | 5 => 1483
  | 4 => 20
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
  | 7 => packedAt gbK7 (83468+((h/678+packedAt gbK7 (75332+(h % 678)*12) 12) % 2444)*12) 12
  | 6 => packedAt gbK6 (203315+((h/1295+packedAt gbK6 (186480+(h % 1295)*13) 13) % 4663)*13) 13
  | 5 => packedAt gbK5 (92931+((h/494+packedAt gbK5 (87497+(h % 494)*11) 11) % 1780)*12) 12
  | 4 => packedAt gbK4 (1436+((h/6+packedAt gbK4 (1400+(h % 6)*6) 6) % 34)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff0f83c1fe1fc03c3803fff0a638f873c33f
  | 1 => 0xf00f003fe1fe1ffffc003fff35927218c7c3f
  | 2 => 0xf000fffc001ffe003ffffc380c61c7c60f8fcc
  | 3 => 0xffffffe000003fffffc00f81f807f00ff0
  | 4 => 0xffffffffffffc00000000ffe0007fff000
  | 5 => 0xffff000000000000000000000ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110e0381402a02421408284aa002084831c315
  | 1 => 0xa10300092042091aa40529541092320841c2a
  | 2 => 0xa02254a4001754048c929820646045c20e854c
  | 3 => 0x844a94af5400009332563018b81b805d00ab0
  | 4 => 0x8088ce732999992e000180020ef600076b6000
  | 5 => 0xccf0006031011030020602040ffdf6b0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36268
namespace PEqualNP.Outside.L_meta_36268
open PEqualNP.Outside.L_meta_36268.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 2 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 6 := bs1_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
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
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
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
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 22 := bs5_3_0
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
theorem bs5_4_352 : Interval s5Atlas 4 352 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 379 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 586 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 20 := bgb_4_0
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
theorem bgb_5_1472 : Interval gbAtlas 5 1472 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1483 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))))))
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
theorem bgb_6_3872 : Interval gbAtlas 6 3872 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3885 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672))) (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800)) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928))))) (concat (concat (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152))) (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))) (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)) (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)))))) (concat (concat (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 bgb_6_2144))) (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624))) (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))))) (concat (concat (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104))) (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)))) (concat (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616))) (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872)))))))
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
theorem bgb_7_2016 : Interval gbAtlas 7 2016 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2036 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 bgb_7_992))))) (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248))) (concat (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 bgb_7_1376)) (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)))) (concat (concat (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))) (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888feeefaeafeecf888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074666 * 2 ^ 32 + 4276942984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36268.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.or,[2,3]⟩,⟨.or,[0,6]⟩,⟨.and,[4,7]⟩,⟨.or,[4,8]⟩,⟨.or,[5,9]⟩,⟨.and,[0,11]⟩,⟨.and,[1,10]⟩,⟨.and,[2,3]⟩,⟨.or,[13,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276942984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276942984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36268

open PEqualNP.Outside.L_meta_36268 in
theorem PEqualNP.Outside.L_meta_36268 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276942984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276942984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
