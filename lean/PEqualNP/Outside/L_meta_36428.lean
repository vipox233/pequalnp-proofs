import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36428.Model
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


end PEqualNP.Outside.L_meta_36428.Model

namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 8, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 16,swapRows 84]

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

end PEqualNP.Outside.L_meta_36428

namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x173c31595068000b283800a1a8c00000b0f9834a889c420912612400131ea03240065287001092d100001b0074b294e140810035023840c8c400000c4ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x6600211600146e4d004b65540000301b6f11003b030000634c5e000000001f59000049002c706d006800000000006c0000000b4f5767203f000000475100006272000100002e120000741a002b000000004000002f00456900000000710400000032000c520033131d005500000073001e534600292d073525560000000000066b393d5b4a000d0000000000050026000000002741000e0000311000000000376a34003e0000190048280000233a0000005f0061225c64080a5a1c0f00150200005800000060003600242a44004318000000003c0038005d00170900420000504e0000020080800001800201008000000180808302008200000000000001030000008281030003806750c43b7290876d5210e7aa9215794e42aea9c85775150ae8a2a16bd4942dba8a85b45150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932bba8a6574514cb9ea49967d0932e7212659d424cb9a84996350932eba8a65d4514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96633e54c867aa990d794f21aea9e43ad428879a6510cf950219eaa0435e53086baa610eb50821e6990437a50086f2a010dd94640baa8c815f53502b8a6a05794c40aea98816e52102daa4205d94440baa888176518c2eaa3184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6415e53c82baa7906b50b20e6996417651882eaa3106b50920e6992413e540827aa8105794c20aea98417651082eaa2106dd0b10daa1621d732c43aa65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d453443cea4887914910dba1221b542443ae6488754c910f9a8221f220443e240885d94410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x68001400002800a01880040058400008689c92c00000020001e00098eb8c4aa000044000001003c350d5210f254214532a3592424cac46150932e1d85424cb846150932e150b514cb854214532c354d420870d544c821ca5095008749325402193588535022d6215130c354d42c830d544cb20e150932c43245414910d114c52442346550910951953244385424c910e850920443c13248110
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x2830a0cebb0a84994877650b514ca823aa849922181195424c910
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s0K5 (826+((h/15+packedAt s0K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s0K4 (3471+((h/39+packedAt s0K4 (3159+(h % 39)*8) 8) % 225)*8) 8
  | 3 => packedAt s0K3 (960+((h/8+packedAt s0K3 (912+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s0K2 (199+((h/1+packedAt s0K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x83ffff07fffe1f07f0fe1fffc3fff81e89f3f3
  | 2 => 0xfc1e1ff83c3fe1f8ff0fe1c1fc383fe176cd9c
  | 3 => 0xffe01fffc03fffff000ffe01ffc03fff870e1f
  | 4 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x884001108000200010120244404888440050b1
  | 2 => 0x19442231905402287106208cc41192c432c594
  | 3 => 0x208954420aa91153088954112a822519850a0a
  | 4 => 0x729598852a0d559daaa11021b3270189d80f40
  | 5 => 0x431910e6333199e6cccd993822040611efa000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfcccfcccfc00fcfcfcccfcccfc00fcfcfcccfcccfc00fcfcfcccfcccfc00fcfcfcccfcccfc00fcfcfcccfcccfc00fcfcfcccfcccfc00fcfcfcccfcccfc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36428
namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x51201221586539a2048e003600000520ca021e78b8c2a9558e3a0000a40000003e8c0041a18b08541cc0b4c0512826b48a20c100b1c00d1105182080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x435711000a222f000054005b006f000200133a53041564450b5d011b2c0e2d69302003215a12554e703660005f28663200402b720026246b1f374d50083c6700140c481800636d07561a474b0d42651d580000192335003e005e006871743b000025444f415110610005000f4c4a167359493f465200622931003906343d38171c6a33271e002a6c096e2e5c001e86009504808c0f008180018000020580000088868515000d8000828e000581848207800200056750c43b7290876d5210e7aa9215794e42aea9c85775150ae8a2a16bd4942dba8a85b45150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932bba8a6574514cb9ea49967d0932e7212659d424cb9a84996350932eba8a65d4514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96633e54c867aa990d794f21aea9e43ad428879a6510cf950219eaa0435e53086baa610eb50821e6990437a50086f2a010dd94640baa8c815f53502b8a6a05794c40aea98816e52102daa4205d94440baa888176518c2eaa3184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6415e53c82baa7906b50b20e6996417651882eaa3106b50920e6992413e540827aa8105794c20aea98417651082eaa2106dd0b10daa1621d732c43aa65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d453443cea4887914910dba1221b542443ae6488754c910f9a8221f220443e240885d94410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1a0066002901000a2008b9ea0080001c48050c5ac9aa3a40116032800c350d5210f254214532a3592424cac46150932e1d85424cb846150932e150b514cb854214532c354d420870d544c821ca5095008749325402193588535022d6215130c354d42c830d544cb20e150932c43245414910d114c52442346550910951953244385424c910e850920443c13248110
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x6420a0cebb0a84994877650b514ca823aa849922181195424c910
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (826+((h/15+packedAt s1K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s1K4 (3471+((h/39+packedAt s1K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s1K3 (952+((h/8+packedAt s1K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (199+((h/1+packedAt s1K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f07f0fe1fffc3fff81e89f3f3
  | 2 => 0xfc1e1ff83c3fe1f8ff0fe1c1fc383fe176cd9c
  | 3 => 0xffe01fffc03fffff000ffe01ffc03fff870e1f
  | 4 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x884001108000200010120244404888440050b1
  | 2 => 0x19442231905402287106208cc41192c432c594
  | 3 => 0x208954420aa91153088954112a822519850a0a
  | 4 => 0x729598852a0d559daaa11021b3270189d80f40
  | 5 => 0x431910e6333199e6cccd993822040611efa000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36428
namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x23b54002083014c162d2070093a8c0bf43de43bd43dd439d43bf42ee42bd42ed42ad42df32ee32dd32ed32cd32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6c00153800000004c000b3402800115cc08905260010301a19d01e01664500050721c3d0000840000061822012d52d0e3aa921d354a438fa92878e5250f1aa4a1c754f4296aa4854d5390b1a87216390d42c6a1a852f5350b1ca6a16354d428eaa6658d42cca5aa9195354e32c6a1c651d544cb1e8499635093296aa2658f434cb1a869953d5132c72a2654d544cb1aa8994355132
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20d6595132
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 15
  | 3 => 31
  | 2 => 1
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
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (265+((h/5+packedAt s2K4 (240+(h % 5)*5) 5) % 19)*5) 5
  | 3 => packedAt s2K3 (897+((h/10+packedAt s2K3 (837+(h % 10)*6) 6) % 49)*6) 6
  | 2 => packedAt s2K2 (39+((h/1+packedAt s2K2 (38+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf1fe3f0ff8fc3f87f8f0f87f1e1fc7e3d534cf
  | 1 => 0xfe3fc7f0ff1fc3f87f1f0f87e3e1f8fc6acb33
  | 3 => 0x3ff800ffe003ff8fe00ff803fe00ffb30c3c
  | 4 => 0xffc00000fffffc000ffff00003ffff003c0fc0
  | 5 => 0xffffffff000000000ffffffffc0000003ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10020010080040080000100900024020001045
  | 1 => 0x20040001100004008001008200208040004112
  | 3 => 0xda892aaa24aab441b688d504b54129b330c28
  | 4 => 0x44a1b4ccc49a21552dbaa440939936093c0e80
  | 5 => 0x8931268886d332664edcce64d91024123fa000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeeeeeeeee88eeeeeeeeeeeeee88eeeeeeeeeeeeee88eeeeeeeeeeeeee88eeeeeeeeeeeeee88eeeeeeeeeeeeee88eeeeeeeeeeeeee88eeeeeeeeeeeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36428
namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x220e64029204c0242a9c080360040d5468c11142d02842bc61c1e5000046004804a01685560c31d5cb09163e107023c980170080101800c08202108408f003ff43fe43fd43fc43ff42ef42fe42fd42fc42ec42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x61df300c3f46018774c030fc980617f54c82fca9905f55320be2a6417f53c82fca7905f54f20be29e41ef42c83dc85907b50b20f621641ef32c83dc65907b4cb20f6196417e51c82faa3907bc8720f710e41ed21c83d843907bd5320f72a6416e54c83daa9907b15320b62a641ef53c83dca7905b94f20f6a9e41ec53c82d8a7907bd0f20f721e41ed43c83d887907bd4720f728e41ed51c82daa3907b14720f7a0e41ee41c83da83907b10720f798e41ee31c83da63907b0c720f7a0641ee40c83da81907b10320f798641ee30c83da61907b0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94416d52883de85107b10a20f799441ec32882fca3105f54620f790c41ed21882fca1107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41ef42483dc84907b50920f621241ef32483dc64907b4c920f6192417f51482f8a2907bc8520f710a41ed21483d842907ec8120f710241ef54483dca8905b95120f6aa241ec54482d8a8907bd4d20f729a416e53483daa6907b14d20b629a41ef43483dc86907b50d20f621a41ef51482dea2907b94520f6a8a41ec51483de82907b90520f6a0a41ec41483de62907b8c520f698a41ec31483dea0907ad4120f7a0241ee40483da80907b10120f798241ee30483da60907b0c120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290416e52083de84107b10820f799041ec32082fca2105f54420f790841ed21082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf29621ee52c42dca5885f54b10f6a96216d52c42f8a5887bd0b10f621621ef32c43d865887d90710faa0e21f631c43ea63887bc8710f690e21ef20c43da41885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf29421ee52842dca5085f54a10f6a94216d52842f8a5087bd0a10f621421ef32843d865085f54610f790c21ed21842fca1087e90210fca0421fa30843f261087bc8210f690421f710843f621085fd5110bf2a2217d54442f8a8885fd4d10bf29a217d53442f8a6885fd4910bf29221ee52442dca4885f54910f6a92216d52442f8a4887bd0910f621221ef32443d864887d90510faa0a21f631443ea62887bc8510f690a21fa40443f280887e8c110fc98221ef20443da40887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be298217f52042fca4087b94810b7290217d52043daa4085b54810be29021ef42043d884087bcc810f6190217e51043de42087b48410bf28021ef20043da40087dc4010fd08021f510043f220087c44010
  | 1 => 0xf54c87dca990db95321f6aa643ec54c86d8a990fbd4f21f729e436e53c87daa790fb14f21b629e43ef43c87dc8790fb50f21f621e43ef41c87dc8390fb50721f620e43ef31c87dc6390fb4c721f618e43ef50c87dca190fb54321b6a8643ec50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510db54a21f7a1443ec42887de6510fb0ca21bf28c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53486fca690df54d21be29a43ef42487dc8490fb50921f621243ef32487dc6490fb4c921f619243f721487dc4290dfd4121be28243ef54487dca890db95121f6aa243ec54486d8a890fbd4d21f729a436e53487daa690fb14d21b629a43ef43487dc8690fb50d21f621a43ef51487cea290fbd0521f720a43ed41487d88290fbcc521f718a43ed31487d86290fbd4121b7a8243ee50487daa090fb14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290436e52087de8410fb10821f799043ec32086fca210fbc8421fb10843ed21087ea4210df94021bea80437e53d02faa7a06fd0f40dea1e81ef52d02fca5a05f54b40f629681ef42d03d885a07bccb40f6196817e51d02faa3a06fd0740dea0e81ef21d03da43a05f55240bf29c817d53902fca5207b94a40b7294817d52903daa5205b54a40f7a1481ec42903de65207b0ca40bf28c817d51903de43207b48640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940f7a92816f52502f8a4a07b14940b629281ef42503d884a07bcc940f6192817f51502f8a2a06fd0540dea0a81ef21503da42a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40bf29081ee52102dca4205f54840f6a90816d52103de84207b10840f799081ec32102fca2207d94440bb288817d51103eaa2205d54440f790881ed21102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9987790f30eea1e61ef52cc2fca5985f54b30f629661ef42cc3d885987bccb30f6196617e51cc2faa39877cc730ee98e61ef21cc3da43985fd5230bf2a4617d548c2f8a9185f54e30bf29461ee528c2dca5185f54a30f6a94616d528c3de85187b10a30f799461ec328c2fca3185f54630f790c61ed218c2fca11877cc230fd984617f544c2fca8985f55130be2a261de434c3ba86985fd4930f7a92616f524c2f8a4987b14930b629261ef424c3d884987bcc930f6192617f514c2f8a29877cc530ee98a61ef214c3da42987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4187b94830b7290617d520c3daa4185b54830f7a1061ec420c3de64187b0c830bf28861f6510c2eca2185f54430faa886175510c3de42187b48430bf28
  | 2 => 0xbdaa2215b54442f628885ef5010bdca0217b54042b6a8085ec5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccbde85997b90b32f6a1665ec42ccafca3995f54732bf286657d50ccbdea9997b95332b72a665ae54cca5ca9997b55332d6aa665ec54ccad8a9997bd0f32f721e65ed43ccbd887997bd4732f728e65ed51ccadaa3997b14732f7a8665ee50ccbdaa1995b54332f6286657f548cafca9195f55232be2a4657d538cbbc87197750e32bf294656e528cbde85197b10a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde84997b10932f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6197790c32eea18657e520cbde84197b90832f6a1065ec420cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cbdea8197b95032b72a065ed540cbd8a8195b15032f7298656e530cb9ca6197bd0c32f721865ce430cbda86197350c32f621865ef510cbdca2197b54432b6a8865ec510cbdea0197b94032f6a80656d500cbd8a0195f94f41bea9e83bf43d077a87a0fbd4b41bf296837d52d07d8a5a0fbd0b41f621683ef32d07d865a0df94341bea86837d54906fca720df54e41bf29483ee52906dca520df54a41f6a94836d52907de8520fb10a41f799483ec32906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077a86a0dfd4941f7a92836f52506f8a4a0fb14941b629283ef42507d884a0fbcc941f619283f7415077c82a0dfd4141be282837e54106fca620f794c41af298837d53107baa620d754c41bf29083ee52106dca420df54841f6a90836d52107de8420fb10841f799083ec32106fca220efd0441fb20883bd41107ea8220df94041fd280837a50106faa020fe54041bca80837f54cc6fca998df55331be2a663de43cc7ba8798fbd4b31bf296637d52cc7d8a598fbd0b31f621663ef32cc7d86598df94331bea86637f548c6fca918df55231be2a4637d538c6fca518fb94a31b7294637d528c7daa518db54a31f7a1463ec428c7de6518fb0ca31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263de434c7ba8698dfd4931f7a92636f524c6f8a498fb14931b629263ef424c7d88498fbcc931f619263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c6fca418fb94831b7290637d520c7daa418db54831f7a1063ec420c7de6418fb0c831bf28863df310c7ec6218f74c431fa988637e500c7f4a018de94031bea8063f9500c6f2a018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fbd0b21f721643ed42c87d88590fbccb21f719643ed32c87d86590df94321bea8643e
  | 3 => 0x8a2ee1421e45161403d82628128267245201f81604fa06079435c07a00006841a6d25ae0302a01105705d64ae1520c85ee26852465e2500960007482a608878235e6720004f43b26f60ea17474c5402fc4f83263805d44da71e0fe0780c60040140b80800c0000180000e0040080402a0000701e01a0080900b00000002015012008020020080140080805200407006004000010000000080700a0140000180000e018008050000140101b0060040000000200c0a80401c0100100200000004002002004008230000040500001e0040701e0120340000b002058000130000100b0000000000080001a010008000060480d0010080140600200603c030090100040482100c02c0480900e0000100100200000000004008000070100200500201a0080204503200c1180300200c020000400000100001207c0080207000c0080a02400409802000048048080180080500f034014000010140441681600202403800002014000000100480700f00204c000050000000381800801c0181200002c0180000a010008020020000b80000000003806000010050010060000100501a0000100100c00c0b80200409000009012000010010060000081500a00000008004000018000000040000301003c0080201800c0180802000c00801000018000010060000000d0140000500207a0100500701803c05800002000020000000000000100e00c0200200a0000180300e0040a00500a044070040000280400401401001800004000000000260300a81c114010010070040000080200201403804bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310f3a8621fbd4843bf290877d5210fd8a421df94443bea88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e857e51d0afaa3a15f94342bea8685ef53d0bdca7a15b94f42e729e854e53d0bdaa7a17354f42f629e85ef43d0bdc87a17b50f42f621e85ef51d0bdca3a17b54742b6a8e85ec51d0bdea1a17b94342f6a86856d50d0bd8a1a15f55242bf29c857d5390b7e87216f50e42bf294856e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010bdca8215b95042d72a085ef5310bdca6215b94c42f6a9885ec5310bde86216bd0c42f721885ed4310b5a86217b10c42f7a8885ee511
  | 4 => 0x1d239800077a00009a0000b04aa1ec0b472820820664006a7f63dc60060e2703685781f42e633682046200021c19a3aa0000001d04280be00023851e00000000000018e76400078a4806a64b837202c00a0006c808a0ac3ca41c26e5744387c07084a86043663f23f85083340cc2b640e23e7a20d64c64bc12642021278e0c013a00000000000074e4644be4ee0001a400000024a4520000003ec14c0aa00062c4b06081660123880005720005b00000000003500000004d000000033e56c6ea0000083b059800025244029c40619c6541a073232e53671475452c00024e4e600000026447616e0005f048e0000006240005e600013600032c21a49e3200420001783bc6061968226ce4cc4460004726bc1063447c25c80000000004c852804a00037c3084d40006fc6c41560003e879c0002260000b67042200000005dc18677e2663b869e6845fa66a0e86800ee3a62b000000076c0740004b24f24006b20003fc55a7b04c252639671c2d04987423564d20327ae22c25a6d86742826a800013e0581be3f47a05c65f657e3b60de46c4260e40004e00008163da2ea4d83a42785567bc59255c7c41c20000006382bc01a0000000a20000005188046920006485bc65a7683920008142f40003302aa5f41d616a4fc0002e80e255217273a7ea08409c5387567d800068e23a0005600460f06b802669c54e0000007fc29200008c00000022e6c672039053e81013400011a00067a00c56e54c07600000080861a5504a274436215c6f40247801304ac75a0006b07aa0005624ba5ba0001e200045a2967e86be27a6645d871273e3c82446ec67870c13c0fa6ae0000001f04843741ac66c10c6f051215470e20a10a0001d85462c050e2ba28c4426e85d23a02e070011260c76a0001704ec6627d600072c0002401c839a23c00043a3847720000007e20000004561dc0103102ce1c01167d45b45046d073616867c59c49659e1fa74023230c18081a5c23022fa2944e452271a28e3405b829a2840c42365060000b85687607f244c47c0000442d21023a21a20002b404e4020001b839c1b65e27e415e4a000000079e41647a6760381cc2043ee0340000007dc00044812e17a3467f805a4447e67d00007502a477c7264322c800078816251a00082404c4ce4b41e65c04de38c0000003e41842886dc7860000006e46aa00037631a5b20000008060007a63140002a20007b212c40c0b243e46e0f200000031800000019224614800000000029058c1a809e01c00065c0000fc30e1bc11861e20e6346ba1287d22586a400042c4580002d834c6361200002ac25e7f400046a0621ba04018a15a66e1384fe0005a85f263c00005201852e2e42f202203c7340005e86b65be56a2ae1a679666800021458641e7025143326fa7cc76249c2a85426584680164122
  | 5 => 0x26a0001ca5e077440a0a663e76e57c6cc6c22e269671602e1827b43f04ea00020c47800081c3587b849459664e0640ba45036e0505fc1c65d01de09442e6e61b454825c27c3c00862482862422983043487785ea03a5026fe2002cc1147ca48605c3fe45e78c0002c20002ec0000002223c412469851007200021817c07c5ce29e00016480272200001e3282f87a802a1900004f042463a21630072e1c454a09214e31e7522746a27da5ac76679a06e60a4183e017e26c0a84662ca61647e3cc65259422430a0000005c43ce0000a01460000007304e22be21e2fe4900004d67ec0001006100003fa00000068c44a16c0906d679036a3a833873c12a0da6023783860005a03ae45c7104707c60000000f81580d20003ac59075800000e12258422a1e05aa3d00ae37e6da6e247450c1fe05464a5765ca2da6465e43705663121045884224a47fa03614462249a00062834a74a08e00031658a6880bc0003f60d83d25300000001e81ea67e59a1504a61b20e008211e7842d679832a00000063237a2f662650a1980f427e0006e05a638a62e1ae7a47ba5441762b809874635255862a6560ca8007701f619e58e70a48c1ce0ce4923d43822540002600002d47e00000000c211c05e4102de6f21325804c46d40dc5a400000053c1947925343064b67385b63d65ec48a52a0ec80e10e8187064ca36475e5644343e666680a35a2c63245820001b06ee0000006f845400003e22800000400014a0003546420007be0f618864c3ba4300000200000a42f028080c55e4601d461c3b40000480280006704080000006c000068a3ea64400000072a6607de6306820002301f20006ca0004360005a25f82dc0e66ac81e5de0140007ac2c40024887c80000000006de2b25322762560004e82343e21ee0007f044e3603945fe05669043c6a06940703c26183227ce57a3c675c7b618c7fe34e5da42a4f653a6145002106504820d007e34255420238e31c24c08069a06c4dc33c5cc1fc3de1da36c0d400633a2726b406668639e1087ee0004c071851c4144047763be0001aa00061262
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8534426d6214d109b992524426e63949109b586524436561949109b582524436960949108fd91524423c645491097d8d524425c6354910ab19152442cc6354910cbd91524426c6454910cb191524422c6454910d3d8d524426c6354910d318d524424c63549109bd85524436761549109bd81524436b60549109bd97424426d65d0910b398f42442e561d0910ba583424426f65109109b594424432f5410910cb15042442e56110910ba580424426f65cc9109b59732442ae64cc910b958732442e960cc9109bd94324426d650c910d3d4c324434c530c910b958432442e9600c9109d19541442f060505109d19531442f0604c510ba58321442eb60485109e19540442f06150110ec5054044278654c110bc18530443d1314c110b9587204426f65481109b59520442e761481109798f540425d63d50109b98b540426d62d50108f596540432f6295010cb18a540426f62550109b189540432f6255010cb189540423e64150109798c540425d63150109b988540426d62150109d984540427a60150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530434f6294c10d318a530426f6254c109b189530431e5454c10c7551530434f6254c10d3189530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520426e64948109b98e520432e5454810cb551520434e5354810d354d520426c64548109b18d520426f61548109b585520426f60548109b581520423e64148108f590520425e63148109758c520426e62148109bd97420426d65d0810cb953420432d54d0810b398f420434e53d0810d354f420426f65108109b594420432e5410810cb550420434e5310810d354c420426f65cc8109b59732042ae64cc810cb953320432d54cc810d394f320434d53cc8109bd94320426d650c810cb950320432d540c810d394c320434d530c8109b98a510426d62944109b597210432e54c8410cb553210434e53c8410d354f210426f6548410cb951210432d5448410d394d210434d53484109b98a500426d62940109b597200432e54c8010cb553200434e53c8010d354f200426f6548010cb951200432d5448010d394d200434d5348010cd553100435553c40109e59610043395484010d654e10042f161840109dd9510043355444010d554d10043e32044010f8481100427b6544010ce55110043595344010f8c8510043e12144010bcd9510043736544010dcd5110043b25444010dc55110043b15444010cc55110043735344010f494d10043715344010f454d10043515344010f898910043e16244010f894910043e15244010f8d0910043e04244010f8cc910043e03244010
  | 1 => 0x834d63951209b586544826d6095120da58254482eb6055120cb990544826e63151209b58454482ae6494d20ab59253482e96094d209b992534832e6494d208b992534832d6494d209b98e534826d6194d209b58253483696094d20bad81534826e6414d20d398c534826d6114d209b997434826d65d0d20cb153434826e6590d209b596434834c5390d209bd95434826c6550d20cb151434834c5350d209bd94434826c6510d20e350c43482ea6010d20ba580434826e64d45209b98f51482e96094520abd9151482ac6454520b3d8d51482cc6354520bad81514826c65d05209b996414826d6590520cb152414826f65505209b195414826e65105209b594414832c5410520b398c41482cd6310520ba98041482e960105209b197314826e658c5209b596314834c538c5209bd95314826c654c5209b994314826d650c520ab99031482ad640c520d314c31482ea600c520ba580314832c54d01209b996404826f65501209b195404832c54501209b99440482ce6310120b358c40482e66110120b958440483a94010120d314f304826e658c1209bd95304826c654c120d314d304826e650c120ab99030482ad640c120b998430482e5610c120f24c0304826e62d50209bd89540825e63150209758c540826e62150209d984540827561150209b98b530826f6254c208f990530823d6414c209b98853082766114c209d584530826e64948209b98e520826d65d0820b398f420826f65108209b594420832e54108209b59732082ae64cc8209bd94320826d650c820d394c320836551c84209bd95210826f65480209ed95200836a52480209b98b54c426d62d53109bd8954c426c62553109798c54c425d63153109b98854c426d62153109b98b53c426d62d4f109bd8953c426c6254f108f99053c423d6414f109b98853c426d6214f109b99252c426e6394b109b19152c426c6354b109bd9742c426d65d0b10b398f42c42e561d0b109bd9442c426d6510b10b958442c426f65ccb109b59732c42ae64ccb10b958732c426f650cb109b59432c42e5610cb10b958720c42e761483109b98b548426d62d52109bd89548426c62552109798c548425d63152109b988548426d62152109b98b538426d62d4e109bd89538426c6254e108f990538423d6414e109b988538426d6214e109b992528426e6394a109b191528426c6354a109bd97428426d65d0a10b398f42842e960d0a109bd94428426d6510a10ba580428426f65cca109b59732842ae64cca10ba583328426f650ca109b59432842e9600ca10ba58321842eb60486109b98b544426d62d511097d8d544425c63551109bd89544426c62551109798c544425d63151109b988544426d62151109b98b534426d62d4d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b98
  | 2 => 0x65485309b98b540c26d62d50309d987540c27561d50308f596540c32f6295030cb18a540c26f62550309b189540c32f6255030cb189540c23e64150309798c540c26e62150309b588540c27661150309d584540c32e5494830cb552520c26e64948309b586520c32e5454830cb551520c26c64548309bd85520c26f65d08309b597420c32e54d0830cb553420c2ce63d08309bd94420c26d6510830cb950420c32d5410830ab993320c32e54cc830cb553320c2e960cc830cb950320c32d540c830ba580320c26e62944309b58a510c3365494430cd552510c3665294430d954a510c3666294430d958a510c3674294430d910a510c3673294430d90ca510c3365454430cd551510c3665254430d9549510c3666254430d9589510c3674254430d9109510c3673254430d90c9510c26f65c84309b597210c32e54c8430cb553210c36651c8430d9547210c26f65484309b595210c32e5448430cb551210c2cc6348430d9945210c3655148430c7553300c35551cc030dc546300c25f654c030c7551300c355514c0309ed95300c3cb324c030dc545300c25e63953209758e54c823e6494f208f59253c82ce63d0b20b358f42c832e5410b20ab99332c82ad64ccb20d394c32c836551c8720ba58354c82ce6395320b358e54c826e6395320d398e54c824e6395320d358e54c826d6195320ba58054c832e64153209b98c54c826d6115320da58054c82e960d4f20ab99253c82ad6494f209b99253c832e6494f208b99253c832d6494f209b58653c82e96014f209b99053c834e6314f209b58453c83696014f209b99743c826d65d0f20cb15343c826e6590f209b59643c834c5390f209bd9543c826c6550f20cb15143c834c5350f209bd9443c826c6510f20e350c43c82e960d47209b19151c826c6354720ba58051c826f65d07209b99641c826d65907209bd9541c826c65507209b99441c826d6510720b398c41c82cd6310720ba98041c82e960107209bd9731c826e658c7209b59631c826f654c7209b19531c826e650c7209b59431c82ae640c720ab59031c82ea600c720ba58031c832e54d0320cb95140c82ce6310320b358c40c82e66110320b958440c834e53cc320d394d30c82ae640c320ab59030c82e6610c320b958430c825e63152209758c548827661152209d584548823e6414e208f59053882766114e209d584538832e54d0a20b398f42882ae64cca20d394f328836551486209798e544825d63951209bd89544826c62151208f992534823d6494d209bd89534826c6214d209b997424832c54d0920b398f42482cd63d09209b996424826c65509209b99732482ae64cc920ab593324834c53cc9209b996324826c654c920d9d45214826e6508520b398e54482cd6395120ba582544826e64951209b98e544834e63951209398e544
  | 3 => 0xb40e350c32d026e62947409b58a51d026f62547409b18951d026e65c87409b19521d026f6254e409b189539026e6394a409b586529026c6354a409bd8552902ce63d0a409bd97329026d65cca40ab993329026f650ca409b59432902e9600ca409b98a519026d62946409bd97219026d65c86409bd95219026d6548640ab191219026e62d4d409b58b535031c5350d40ae181435026e63d49409b587525026e6314940cbd0c525032d43149409b584525026e65d0940b398f425026e65109409b997325026c65cc940ab993325026e650c9409b19432502ae640c940e350c32502e9600c9409798c515025d63145409b988515026d62145409b997215026c65c85409b995215026c6548540d3d8a531034c6294c409bd89531026c6254c40d3d89531034c6254c40d394e521034d53948409b98e521026d6194840d394d521034d53548409b18d521026f6154840b398f421034e53d0840d354f42102e960d0840d394c421034d5310840ba580421026f65cc8409b59732102ae64cc840d394f321034d53cc8409bd94321026d650c840d394c321034d530c8409b98a511026d6294440d594e51103555394440d994a51103655294440d998a51103656294440d9d0a51103644294440d9cca51103643294440d594d51103555354440d994951103655254440d998951103656254440d9d0951103644254440d9cc9511036432544409bd97211026d65c8440d394f211034d53c8440d9947211036551c84409bd95211026d6548440ab191211034e5348440d354d21103665148440d9545211031d53d0040cd547401037151900408fd95401031d5350040cd545401027b6550040ead09401037151500409b98b54cc26d62d53309b98a54cc26d62953309bd8954cc26c6255330c715143cc2ae64d4b309b99742cc2ce63d0b309b99442cc32e5410b30cb55042cc2ce6310b30e350c42cc2ae64ccb30ba58332cc2e9600cb309b98a51cc26d62947309bd8951cc26c62547309b99721cc26c65487309b98b548c26d62d52309bd89548c26c62552309b988548c26d62152309d984548c27561152309b992528c26d6194a309b191528c26f6154a309bd97428c26d65d0a30b398f428c26f6510a309b594428c2e96010a30ab993328c26e62946309b58a518c26f65c86309b597218c26f65486309b595218c2cc63486309b98b544c26d62d51309b98a544c26d62951309bd89544c26c62551309dd85544c274615513097195434c31c5450d30b6181434c26e64d49309b587524c26e6414930d390c524c34d43149309b584524c26e65d09309b197424c2ce63d09309b994424c26c6510930b398c424c38d4310930ba580424c26e65cc930ab993324c26e650c9308f990514c23d64145309b988514c26d62145309b997214c26c65c85309b995214c26c
  | 4 => 0xa589500c76b4254031da109500c76b3254031da0c9500c75b3154031dc8c5500c7593154031dc4c5500c65e63953219758e54c863e6494f218f59253c86ce63d0b21b358f42c872e5410b21ab99332c86ad64ccb21d394c32c86e561d5321b398e54c86cd63953219b98e54c874e63953219398e54c874d63953219b58254c86e56115321cb99054c866e6315321d958454c866d6015321b958753c86ae6494f21ab59253c866e6494f21cb99253c862e6494f21cb59253c866d6094f21b958453c866e6414f21d398c53c87656114f219b58053c866e65d0f219b59743c872c54d0f219b99643c866d6590f21d314e43c866f6550f219b19543c872c5450f21d314d43c866f6510f219b19443c878d4310f21cb95341c872e5450721b398c41c86cd6310721ba98041c86e96010721d394f31c874e534c721ab99031c86ad640c721ba98031c86e9600c7219b19150c866c63543219798c548865d63152219e980548867960152218f990538863d6414e219e98053886796014e21cb95342886ce63d0a21ab993328874e53cca219798e544865d63951219bd89544863e6494d218f592534866f6254d219b997424872c54d0921b398f42486cd63d09219b996424866c65509219b99732486ae64cc921ab593324874c53cc9219b996324866c654c921b398e54486cd6395121b9586544866e64951219b98e544874e63951219398e544874d63951219b586544876561951219b58254486e76155121cb990544866e63151219b58054486ae6494d21ab59253486e56194d219b992534872e6494d218b992534872d6494d219b98e534866d6194d21d9586534866d6094d21b9d85534866e6414d21d398c534866d6014d219b997434866d65d0d21cb153434866e6590d219b596434874c5390d219bd95434866c6550d21cb151434874c5350d219bd94434866c6510d21e350c43486e66110d21b9584434872c54d05219b996414866f65505219b195414872c54505219b99441486ce6310521b358c41487a54110521ba98041486e96010521d314f314866e658c5219bd95314866c654c521d314d314866e650c521ab99031486ad640c521f14c431486ea600c521ba580314866e64d41219b98f50486af6454121ab19150486cf6354121b318d504866e62d50219798c540865d63150219b988540867a60150219e580540866e62d4c218f990530863d6414c219b988530867a6014c219e580530866e64948219b98e520866d65d0821b398f420866f65108219b594420872e54108219b59732086ae64cc8219bd94320866d650c821d394c320866f65484219dd95210876652484219b98a53d026d6294f409bd8953d026c6254f40b398f52d02ce63d0b40ba58342d02e96010b409b99732d02ae64ccb409b99432d02ae640cb40d394c32d034d530c
  | 5 => 0x525066d60149419b99742506ce63d09419b994425066e65cc9419b19732506ae64cc9419b994325066c650c941ab990325078d430c941b9584325065e63141419758c505066e62141419b588505074f6294c41d318a531066f6254c419b189531074f6254c41d3189531074e5394841d354e521066e63948419b582521074e5354841d354d521066c63548419bd8152106ce63d0841d394f421074d53d0841b9587421074e5310841d354c42106e561108419bd97321066d65cc841ab993321074e53cc841d354f321066f650c8419b594321074e530c841d354c321071d53d04418fd95411071d53504419dd9541107a742504419b98a501066d6294041d694e50107595394041da94a50107695294041da98a50107696294041dad0a50107684294041dacca50107683294041d694d50107595354041da94950107695254041da98950107696254041dad0950107684254041dacc950107683254041ced0550107724154041ce505501077141540419b98b54cc66d62d53319b98a54cc66d62953319bd8954cc66c6255331c715143cc6ae64d4b319b99742cc6ce63d0b319b99442cc72e5410b31cb55042cc6ce6310b31e350c42cc6ae64ccb31b958732cc6e5610cb319b98a50cc66d62943319bd8950cc66c62543319b98b548c66d62d52319bd89548c66c62552319b988548c66d62152319e980548c67960152319b992528c66d6094a319b191528c66f6054a319bd97428c66d65d0a31b398f428c66f6510a319b594428c6e56110a31ab993328c66e62942319b58a508c66e62d51319b58b544c66e62951319b58a544c66f62551319b189544c67b60551319e181544c65c6550d31c7151434c6d46150d319b993524c66d60d49319b990524c74e4314931d350c524c66d60149319b997424c66c65d0931b398f424c66e65109319b194424c6ce6310931e350c424c6e561109319b997324c6ae64cc9319b994324c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d6595031cbd8a540c72c62950319bd89540c66c6255031cbd89540c72c62550318f990540c65e63150319b988540c66d62150319e980540c6796015031cb952520c72d54948319b992520c66d6094831cb951520c72d54548319b191520c66f60548319bd97420c66d65d0831cb953420c72d54d0831b398f420c66f65108319b594420c72e5410831cb550420c6ae64cc831cb953320c72d54cc831b9587320c72e540c831cb550320c6e5610c831c7553310c65f654c431c7551310c677654c431f1cc9310c66e62940319b58a500c73a5494031ce552500c76a5294031da54a500c76a6294031da58a500c76b4294031da10a500c76b3294031da0ca500c73a5454031ce551500c76a5254031da549500c76a6254031d
  | 6 => 0xb2e54d0b32cb95242ccb2e5450b32cb95042ccb2d5410b32b398f54ccb2f54953329b58654cca6d6095332cb98e54ccb2c6395332cbd8654ccb2e6195332cb58654ccb2c6195332cbd8254ccb2e6095332cb58254ccb2c6095332cbd9554ccace6315332cb99054ccb4e63153329b58454cca6d6015332cb95343ccb2e5490f32cb95143ccb2e5410f32e350c43ccaae64d4732ab59351ccb2e54d4732cb55351ccb2e5494732cb95151ccb2d54547329b19151cca6f6054732ab99051ccaad6414732cb95051ccaea6014732ba58051ccaae64d4332ab59350ccb2e54d4332cb55350ccb2e5494332cb95150ccb2d54543329b19150cca6f6154332ab99050ccaad6414332cb95050ccae66114332b958450ccacd6290e32c7951438cace63d0a32cb950428cb8d4310a32a7593328caae64cca329758e544ca6d62951329bd89544ca6e65d0932cb153424cace63d09329b994424cb2e5410932ab993324ca6e62d50329d984540ca7561150329e980540ca7960150328f992530ca3d6494c3297596430cb1c5450c32b3d89430cacd63d08329b596420cb8d43908329bd95420ca6d6510832cb950420cb2d5410832b358c420cb8d4310832a7593320ca5f654c8329bd95320cace63d5032d398e540ca6d61950329b582540cb2d5415032b398c540cae66115032b9584540caea6015032ba580540ca6e6415032cb990540ca6e6315032d398c540cb6661150329b584540cb65611503299584540cb6a60150329b580540cb6960150329a580540caae6494c32ab592530ca6e6494c32cb992530ca2e6494c32cb592530cb4e6394c32e3992530cacd6494c32e3592530ca8d6494c329b597430cb2c54d0c329b596430cb2e5490c32b3d96430cacd6590c32d3596430ca4d6590c32b3592430cb4e5490c32e3952430cb8d5490c32d3152430ca6f6550c32cb151430cacf6550c32d3d95430cb8f6450c32e3d51430cb4e5450c32d3151430cb8c5450c32c3151430ca6f6510c329b194430cb2e5410c32b398c430cb8d4310c329b191510cb4e4354432d350d510ca6f6054432ab990510caad6414432ba980510cae960144329b191500cb4e4354032d350d500ca6f6154032ab990500caad6414032b9984500cae561140329b98a53d066d6294f419bd8953d066c6254f41b398f52d06ce63d0b41b958742d06e56110b419b99732d06ae64ccb419b99432d06ae640cb41d394c32d074d530cb41e350c32d066e62943419b58a50d066f62543419b18950d066f6254e419b189539066e6394a419b582529066c6354a419bd8152906ce63d0a419bd97329066d65cca41ab993329066f650ca419b59432906e5610ca419b98a509066d62942419b98b535066d62d4d41c714d43506b46150d419b98f525066d60d49419b98c525072f4314941cb50c
  | 7 => 0x2c0600100007c010000220240500a00c01407023000000000020260040080000a0180000500001c000070000180080c00e0180a0000120240000103e0d0018020640c80e00200401c030010080102980400e0740001c00400c0080a00c080010040020440002a000024000010120000000500609010802000014000240d40180380203a0500080401e0080080003a000188200380340000100a000010450000040900e02c00c000000240240000002803c0200b0000680903a010000020030000141383f00001c00009000000008000000380001e01601c0000200203c0000601204c0080400400410801004000040070000180080e00000c0000301c0266d6194b439b58252d0e6f6154b439bd8152d0e6e62947439b58a51d0e6e62943439b58a50d0ece62d0e43cbd0e5290e6d6194a439b5825290e6f6154a439bd815290e6e62946439b58a5190e6e62942439b58a5090ece62d0d43ab98a4350e6d61d49439b5835250e6d61149439b5805250e6e62145439b5885150e7a60145439e5805150e6e62141439b5885050e7661141439d5845050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43e3d894310f8c6250c43e350f5210f1d4394843e350c5210ee56114843ba5805210e6e62944439b58a5110f1d43544439bd895110e6c62544439b98a5010e6d6294043c750d5010e6f62540439b1895010f4f6294f42d358a53d0b4f6254f42d3d4e53d0a6d6194f429b58253d0b4c6494f42d3d8653d0b4e6194f42d358653d0b4c6194f42d3d8253d0b4e6094f42d358253d0b4c6094f42d3d9553d0b4e53d0f42d394d43d0b4e5310f42e350c43d0ace63d4742b358f51d0b4e53d4742d354f51d0b4e5394742d394d51d0b4d53547429b18d51d0a6f6054742b398c51d0acd6314742d394c51d0aea6014742ba58051d0ace63d4342b358f50d0b4e53d4342d354f50d0b4e5394342d394d50d0b4d53543429b18d50d0a6f6154342b398c50d0acd6314342d394c50d0ae66114342b958450d0aad62d0e42c794d4390a9d63d0a42b398f4290ace63d0942abd894310a9d63d08428fd954210a6f6550842b398e5410acd6395042cb9925410b4e6395042d358e5410b8e6395042ab58e5410b8d6395042a358e5410a6d6194c429b5825310b4d5314c42b99845310ae56114c42ba9805310ae96014c42d394f4310b2e53d0c42e394f4310b8d53d0c429b5964310aad6490c429bd954310aaf6550c42cbd954310b8f6350c42e3d4d4310b2e5350c42e314d4310aae6410c42d394c4310b8d4310c429b18d5110b2f4354442cb50d5110a6f6054442b398c5110acd6314442ba9805110ae960144429b18d5010b2f4354042cb50d5010a6f6154042b398c5010acd6314042b99845010ae56114042cbd8a54ccb2d6295332cbd8954cc
  | 8 => 0xb68000000000948138d041ac000000fa49247610c1518f802757fcd2404066d3292ac518ca0e6c8256ad01918d6e55c8000000c88d9550400165d21c4e192122805c0000545e9a0177d50d8ac00118925869c3852d59fc9e8f8c7fc5b52fd31d8b5154428000e5d2bc9cc9605d997cd611395016443f8954ba8b255094a8f9d3d54040000003a07bd2804fd48c00000000169c00038c1dc0000003b8000d404a152d7290650550e0000000fa8c6050937138c72d9c14c0f1c0000004002b408c000c092cc08582400160019c3080008012210fd905264f2c418d8475983d3502e14792ec7819c8f3ce0874d8749955c14b13ccbbc0011341f8b5400034589ce30b852e4ac1658c5c86c2fcd1d6b10c53452b992d4709d47f14a0000000d290f85007d4ae800196d7688a91e8bb84b40009d90919d9268450240000e5907d5b17487a965560c000e4533187c648104721381964c50abc0fce3cad800120cb300116d13a0818c3d0a06b1925685224a347c179d7c4000d10588600b445645607256998e9880bc4b1d6719d01e5898d5ccd4eb5721629821930a39968c8407863d61cea8635598b7487491d6f91f95dd4f145813d99c5ad5cc000ec01e15d8d7911c2c40000000002d1784fb00009fc0004340001641a42143917596640001b0e35024000454000498e40e147ac000c811455896d986d300000aa8fa00003cd1ec5a8004090010000280000200a0400000100e0100200000000003005004008010050020040180c00a000068000000000080000e0102001f0140080180901600c0400001a04c0380300a0c4008000520180280201e1680080000003c0280401e0002280600a0580301801806c1a8080000080000200a0280180103e0000280900605c000160000000800d0000140001a0020000200700600002802000008068010000040101500c0440383000a0100300704e0181000200a0100003300a02c088020040740000400c0180300d004000020000060040501801000400001008014000060000041d00e0340200780000200c0082e00408c0000608a000000000000180201500a00400000002000010030222bc088000040000b0000380f40603c0000340200000204c0001903800002808006004020440020000a0000260080080800405c0000400404800800000018168020000000300404c0000000201200000821006018130010080240080f00a01c0c8000340000080000e02c0400d0000040180003e0000500d000008000010260540000300800058013046010048020440100c00c002024000220480100200000a010068250d8000028070840000080600a0182680110403801011000034060020120340400600000402000004010148000080c00000900e000040210060300500a0020240700300c06c028000020381700000
  | 9 => 0x34f0925c810bd985962427cb88e78188c958d8de46386fc670d7167857823d60954d68d2f8100744714ab0a403d4b5c41c5fd0ecb6167c3e53f0e4d33880844d855498198f28a648d489c348238b04d80ad051c4dc1d0d65174c7012d9e9031790c0ce84bf51c54dca053ad01c29d3e4db50e8a211582cd810f99384cdc7a4a817d0b80a441c47b934d3f4e60980d54770f7cce94ac0392c4331309294ad450d43506c1953c02e86318683fda10484a6d08532c6d070cec85d073c5c18a1a080f08e0c045952919384ed3057dc02000cd596942dd4558fc3b4e04fcc1c91481298c904c47c4d14890712307541f44400014252146f8bd11bcfb8990000170f3557c0010e46545841d555c94c6998a8000774ce517000105cdbc7b09e15311c80012f000000042c000298000000a00000e64cb927850522c2d4fd57c002cbdc22c4149300008a57bce38a8c000000e000005a40005ed6e0000000000f0400149d5d13d173ca285d4000000e108f126ccc4000cfcc59660368fc85a00014093540e4ec4894000749068360000fc09b16100003514947d8d4c7900000000000010f0a98000c5400133c0000d06b93a40354bcbad7b4d9c0000014d875cdc8dd0da89006844b09c95659e00014f939c49c000000000fe40000000c00e0000000000a24f843c18516fc0019b00680019f00f97c9970000000a0cbecd8c6e4ae40014b40000000000000018280901b85700011009040016a8000ffd948000df00006d99ac2b8000000dfc5cc95915d1e04583f4be888832c5e06290b16417650a431c000374d88280000000108000000000b200000000000002711d0a1c650f54decd69778df96bc4258492d17540000000003c51a53bc0f4e24c6c918244ecd6685414ecedc000000bc8000838978d00788e2cb3c258de0221415580001690fb434c944ea54900000000005e46900486104cc398c689f4000cb4a540014e00000011d50bd6ec0000007844649f123887163c8a0f200019e40011c00011f00000008280000c8aa0000dd84f845c0002780000013797f019115000004c00000000000136c8b0b0c2bc0002089100004e80000000987f95e95e40004b902ce8c00173800036d83927178c2319089403640b86f4f603708d11a15255c537d8f543cd345c8ddcac92351d920856805916c87d9d50d87003dc110ef82d88bca94ee558d46c3a914c00030c0c481c328880178e999592dd990304c383ad0cc001058840b940008f52412a5560000e81618e1c294b908ec0000000009840000954d03114cc7355f4318f69a0440c6b45746798453fc0886201305508580013e00015293a8bfd1056a0cbc00054cd980003d82a4c8d62d634be4bc010c0019406083b0f496b48cd7d512d834849094000000000000bcd04198c84c6a50799f4000000000000000
  | 10 => 0x8b1496485c0ac0000014681744bd6816e94440013c40007dcfd90b433559c9884111204815fd7ec7e892cb717996394100bc00124d17c83c85110c6d59740000017e0e0c00000016c8c415c8ac0013b03e02c123d9982551f43c8a3d29c0010dcd180002512b40000000005380011300000011ac2acd45430a2d55135cfed5d4ab835c5205300b4f50e9ca5c248c980a94f5484868f193ec9d01196b8974be1178018a0868076cc752a077c438c253dc7d0b6551c6f19cc0014c8b34768f3195c25cf447ecf88598000000fdd891180c9d42c000001774c20000478a4c99821cfc40000015b4000c1c00096ced144d70d2497acaad9840505154182f40018f1950fd15ad42111928455d00080c0015e1450ee800011c0019a55780000000000015bd70007c000b085117b806467c6bc6c00000000005908619158700000003e800175c1e8000cc15483f00000004757f8ef17b0228a600004e40015595949c4490b6c8fcbf87c91a80000040d400000193c000b8d9893b80002250d42858600001a8728269864000cac00176d16503c0000012600001216f0000ba177124467403d8cc4ad28919188d2c08157186e90891dcf4d5a8558394efccf88e471ca58b9d3c832415068c2ed254ed96c06255850805807f4288d513242f80019dce485f51b828d8e400046865d96153956cca51617500ecae10d06ece28e7c6192a857d318ebd375274144c34f649b4cd13f8c7cead5910098300003ecb50b180741544d927d6cc044a185c53890614d40800002192c84041c00009ac614f002e4dc0fe980c704c301d974cc786055a58782a0c2c184c65818a319bd3b49ed05180539814d910c151b598001d520acd715740cf541ce74e881814280dd9c56207780012f4a741b4000c40000a79978f407a06898d07e421000000166c1606cc93519d448000c1000000134078cf6c26ccf01bc9282b0001474c000002040a18c509d760000d7d0f41ed2009b8eb8794200449a0d554aa4000001945800000d3c0000000000016c475130cd6d514e18001368dc45bc644bf0544d48820afc3140d88dd7351e547c1598ed895a15708e20ed4bb088508d9b491443090c79c8048d8ac55450154612d893cfbcaf490817d9f98b069437d0ad5700008c17d8000dacccc0009dd9192e0a488c85b0738471310000e94000124af07cd1b00014e4001724000338000a50eec3216dc3d19b85349c16c980860c000000000e90000b000b0000fac300a149a874000018c3402600000004d57a99ed8bd71c3886ad34862c0288b9034eb156813488c0251097f46dc6c8db0444b2d4c4d14f58b98765049115a186408310a8dcd1254a48546e07e0c290b800024c001250fe1011481605128c918b865853caf8000408000001464014000f9400096800131588861c1f04a40300015
  | 11 => 0xb10000ff97304c98d52e92b1574000000f90000f24b3800000098c000000000b41194834b7c99c82d54056d3d80087c459d36182cd08ea07b4898798e717e4ab528c460d314e839cdd40cc1a0ff49e58c12180011404c0000d0d359074cc8d91440168da15f0358a9c6a140d0c80005b89717cc5f84f45dcdf4f10d3809c00000097cde999572ca844c4354c197e9650f7406c52d0200000008e96140619280e9184708664291198001204000c4c5493918dc48846c00014811433c000ff000164c0000019a0f70ba4000a100a4d75044000b7963167400048c5f1934b4c0000002347108456a4ca8e54c48bd4528f78ef5168000b49038494920a89510ce0e684f14b800184d74581c38190d0997800010051fc0019a80013209f81fd8f8140000000ee0f382a895d1cd5ec0009bd029210891794cd945d7a4bb4b5985cdb96d4f0c000000a686689a5299688a7d00c8649393e95a08796495b8cb01cc58cda58a595571194c950f5c64d364adc378d2d4017a08f83a47308b55f8b289a0a700017882f066170443d8406a953caec4200000000011102654fd8156f420c0700013344a991c554d20f158e06c4c4471913c3bd884e50a91394cec5242c990143
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2056170d0951102b0b8084a8881499d33254440952e0322422060c6454d2110312322a290881629cf4250040e4684a8a802042e7499721cc2163a2ca90c61345c46050d308cae2328849860c6550c424c344a1ac021261439cf6295030a1ce7b12a81860d5498f420c264b84c7a10610b5d664cc83085eecaa6641862954580320c2a339e8528861499d33294430a88e6b12a21854673d09510c2933a664a8861585c33254430ac2e0192a21860d5418d210c264b80c6908619118d5148430b14e9992601874332545300c286b9ca821641435d2530cb20a1ae7320a99062a6458054c8286ba4c629e419298d6014f208cae2328879060c6550c43c822739ecba0e410b9d365cc720c18a8b1e849060d6414f3248286b9cc82a241435d26314d208cae2328869060c6550c43482343aac021a41a250d6010d2089ce7326a29042e7498f514822639acb20a41495c45410520c18a8b1882906285458041482163a2cb18a4183590530c520a8ae2298629064853580314822739ecaa0241a258d4010120d42c2a00809042e74d953048344b226018241b0585300c12089ce7b12a81042e74d89530822739cc9290410b9d2639482089ce7324a58842e7498e52c422739ecba16210b9d365ccb1089ce7324a50842e7498e528422739ecba14210b9d365cca10898e6b16a88842c7458b534422739cc9292210b9d26394910c18c9b1aa48860f6418d5244306320c6a9221139cf65d0910898e6b28848850d7315042443122a2c2212218a151601091085ce9b2e648842c745943244286ba0a6192219114d610c910c90a6b0064884d1731814144258ba0c098a21345cc6150110962e830a608842c74595204422639aca90221439cf629501089ce7b12a80850e73d8954042873a6c5298210b9d36254c10a1ce9b12a60844e7399252042173a4c729021139cf65d081089aeb31e840860e5498f4204306aa4c7a102113dda53d081089eeca9e840842e74d973204216bacc9990210bdda54cc81085eecaa6640860e6494f3204307322a799021c85532044010e82a790220087215448110043a0a9a4088021c85532144010e82a790a20087215448510043a0a9a4288021545cf5444010a62eb2a22008723725511004390392a8880214c5d35344010aa2eb29a20087115494d10043892a2a688021c45515344010e86e4a9a20087407254d10042b0bacc488021c85526244010e82a731220085637558910042d03a2c488021c85516244010b80e6b122008741535891004390aa4a488021d054e5244010e42a8a9220087415354910042b0bae8488021c85534244010b84e7a12200874153d0910042b0ba88488021c85504244010e82a6212200856175cc910042d13a66488021c85533244010e82a79922008561750c91004390aa06488021d054c3244010
  | 1 => 0x53d0aa5380c929e85525c06494f42a1ce830ca7a16456118653d0aa5380c329e85525c06194f42a1ce8304a7a15467118253d0aa2b88c129e85925806094f4289aed298a3a164a5398051d0b2529ac028e85135da5314342c8ca7308a1a16465358450d0b22a9ac2298859254d6014c4291cec29a86215857114d4310ac4b80a6a18851a5c06354442c18c6a1aa2214657118d5010b0631a86a8085499c46395332a4ae231ca99952a7018e54cca94b80c72a665439cc6195332c4ac230ca99952a7018654cca94b80c32a665439cc6095332a4ce2304a9995257118254ccb14b00c12a6650b5da5414732c54a9300a39962a5458051cca16bb4a828665899526114332c4ca8b08a19950d73950424ca8ab88a8a1865465c05450c32c4aa8b08a81962954580540cb13322c22a0659198d6115032cc2c3300a81962a64580540cb2531ac02a065989856015032cc2c2b00a81952571153430ca94b80a9a1865515c45490c32a92e02a4861942e76151430ca92b88a8a18654a5c05450c3291cedaa2861944e76151430caa2b88a8a1865525c05450c3291cec2a2861958571151430cac4b80a8a1865439d85450c32c1cec2a2861970671151430ca86b88a8a1865c15c45450c32a0ae22a2861970a70151430ca86b80a8a1865c25c05450c32a12e02a2861960c6550c430ca34b80c8a88658319143544328cae2322a01960c6450d500ca58b80c2a1a831a5c0650c941c18caa1864a0e854358432506873a6c529883439d36254c4189aeb31e8420c4f7654f4210722a9ac221083295c664cc841c1cc8a9e6420d8673d0941106a539e85280834a9d33294041a50e8b12a020d4a73d0950106b0b8e84a8083585c44254041a54e9992a020f23425055010668b80c2a1a631a5c06510931c18caa188498e8543584424c68739ec52a063439cf6255031c1aa931e8418cc57198f420c616bacc9990630bdd954cc831c4aa8b086418d8674cc9310c6a539e85280634a9d33294031a90e6b12a018d4a73d09500c6953a664a8063585c73254031ac2e2192a018f43324c5500c686b9ca821643435d2530cb21a1ae7320a990e266458454c8686ba4c629e439198d6114f218d2e03288790e0c6550c43c87062a2c7a12438359053cc921a1ae7320a890d0d7498c5348634b80ca21a43831954310d218c8eab088690e8543584434862739ecaa0a43a158d4110521d4282b008290c2e74d953148742b226218a43b04c5600c52189ce7326a090c2e7498f504862739cc9290430b9d2639482189ce732e43a044c735952190258b88c0a1a81195c4650c940c18caa1864a06894358032502873a6c529881439d36254c4089aeb31e842044f7654f4210324a9ac0210812a5c264cc840c1cc8a9e642054673d0a51102933a66528881491d16254440a8ce7a12a2
  | 2 => 0x7c3e24800040004d541000bf1b084419311095100000075550000037c00001102b0561e4cc3551b43894000e52740008422000003a0d70b4f9488b70c000000ff45d020011f3c0f700000429402640027c462f11329c0025c6b0000040000020000f4000000001c310640000000001214940012c0001814318512f4b63c8740247b16000000002e40000012000a41b9462710b00108000000007c00000324d9000000000000000000000000011c0023145000000b80000800001160c8b80012b4e80019ce4000e90911a1c00000000000000d0d80e07610c002ac6322d2a0fc714f4003b80051c002440033454000fd1014a000882d4004d8364b08154c000005c00000001441a0ba1200018833430000000000000240000011843d3b29400540531051c000003448613400000a03140d4fc002580013000194522ecc34b53e550571647d254aa000284dc0000027184150009e000003bcfe0002f01000320000012e538ed00c00478ad000eb00000000930000042556000004bc3b000a9284fa508001b498000003d000000732080000039000f63b1204cc00000000000000000000830005f4449a128c0000000000000049000002bcbe00072000000005e34c1821cd21140040c602881c0001700000000000000000000000f14500000016454ce3d504000d436cdd448ca00000031392980003c0a0012300143001285200e0000000000498440013c1dc00000e24c0000000000124000ea02ce6340dc174004040016d07548000000026c69000640008e0014913c6f3e0000000053ca800000000000001e140e30001a0151d464000f00049cfb2c8b30e8e0234203cccb04c2a39cae1d4b03f0854e029225345314d4a54b2d0801e08f1680128c00308b10b0de1fc00138550002b000000000043426368e11e87e1a9051982531d3208c350dcd606c11310c133c8a00000000028080080202000018060102a0200800006028000b0020080c048300000a01800038040000004812018000a002000020000001002030000000400004008000c012000000100002000000040080a0300800808018020000c008180100a000000100000000000040080000000008040100c018060180800800000000080200000008000000400004030000150e72d954310e47bb287a908723dd94314843d0a86b08a421e89435805210f06a18c4a88878350c6254043a8ce2324a7a154571192
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x30071d000000051800000000162400003d061400003f000c3720000e350008001f260036000a1211000000321a2c2d0300003c000000003321000429382a00000000001c150023000f3e3b0b0000001b010010192b0934271e22250d2e3128003a394013172f02002c0010d0000302021000006140000208282c41615c06194f42c41715806094f42a098018d4354442a058118d4354042c21615c06195332c21715806095332d01719c05450c32d02715c05450c32d01715c05450c32a09801914354432a05811914354032a0980195430c941a058199153cc841905859cf4250441921819d33254041b0283d094154041a09801954310931c05545c663d0831905859d3324c431941819cf4254031b0284cc93154031a05839916115321a058498d6114f21a09801954310f21a09801954310d21c047550d6110d21a0581195430c940a098099153cc840921809d33254440a09801915348440a21801915148440909859cf4250040b0283d095150040a05811954310930c09545c263d0830941809cf4254430c09545c06348430a418018d5148430909859d3324c030b0284cc9514c030a09839916015320a098498d6014f20a05811954310f20a05811954310d20c087550d6010d20a05811516310520a21811516010520c05645c4530c520a418114d600c520a05831516110910a09831516010910a058414d610c910a098414d600c910b0283dc95444010b0284dc95344010920875516244010d01541cd62440109408754d6244010d007454d6244010941859cf4244010d01549cf42440109438754f4244010921859d33244010923875533244010d027454f3244010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 6 => packedAt s3K6 (864+((h/16+packedAt s3K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s3K5 (32016+((h/348+packedAt s3K5 (28188+(h % 348)*11) 11) % 1253)*12) 12
  | 4 => packedAt s3K4 (69625+((h/557+packedAt s3K4 (63498+(h % 557)*11) 11) % 2006)*12) 12
  | 3 => packedAt s3K3 (17947+((h/114+packedAt s3K3 (16807+(h % 114)*10) 10) % 547)*10) 10
  | 2 => packedAt s3K2 (4047+((h/21+packedAt s3K2 (3900+(h % 21)*7) 7) % 103)*8) 8
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe1fe1ff1fc3fe3fe1e23f1f87f1f87fe13333f
  | 1 => 0xfe1fe1fe3fc3fc7fe03c7e3f87e3f87e2ccccf
  | 2 => 0x1ffe003ffc0071ffc07fc007fc0071cf0f0c
  | 4 => 0xffe000003fffff81ffff800007ffff81f00ff0
  | 5 => 0xffffffffc0000001fffffffff8000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x20424022048044000200904811048114011115
  | 1 => 0x4404044048088080200422110221102804444a
  | 2 => 0x1dc8cce49199c962ee4074833748334ccf0f0c
  | 4 => 0x888199092223002554a9000444926601700aa0
  | 5 => 0x11111180033212499932492660004401baa000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeeeeeeee8888fefeeeeeeeee8888fefeeeeeeeee8888fefeeeeeeeee8888fefeeeeeeeee8888fefeeeeeeeee8888fefeeeeeeeee8888fefeeeeeeeee8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36428
namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c06015273e10b255ea0024002d000201c00042000a600b400f0054c8246615880c44f1b147110d1c5048c5c749852400b9a520803ca58a0030801c8340002ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x59019e8000f000000000228580000000b800000000000100e0000000000e400000e838e881000841650000e04400000008467000d808000a8000000001240000048009461000008c00000000037000c400000000000000016c00433c9fc7e050000004001e86400860020c00250d81cba6b041a8a200000005400000489e661004c780000000c400000010e630012c14000b970b4000000000003b0000000060d0005812001040000000000000000000039000f66e298000052001f00c6d140009a2614800000d3c00056800a0e80000421c400000000000003991c0054300009c6c0000000003780000700000000001908c008500000000000000600000068822c2f00076351687c804c349a0be01000bc30001387800643e954ae3e0000000003f110000000000ee560004400003a920003300000000000000ca000000000000000005020040200000000200000000000020040600010080203008040005000040c0200014020003818000a000080000000000000b7296876d52d0f5ca5a1eb54b439eaa4876f5250ed8a4a1e7d4d43d7a9287ac5250e7ca821d794f42aea9e853e54cca7aa9996b95332d6aa665af43ccb5a87995b54732b6a86659d438cadca5194f950329eaa0659d430caeca2195d54432bd2806579500cb5ca8196b55032b729865ce530cb5e86197390c32d6a1865cd430cb1a86197994432b6a8865e5510cacaa2197a94032b6a8065e9500cad2a0195b94a41b6a94835e53106baa620db94841b6a90837a50106f2a020cf953319eaa6639d43cc6dca518db54a31cea1a636f524c6d8a498cf950319eaa0636e520c6daa418de94031bca80636e53c86d8a790ebd0f21d6a1e436d50c86daa510db94d21b629a43af434875a8690f9d4521f318a43e531486dea090db94821b7294816d52902bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc33a87985b94a30b6a94619d434c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c2dca7905b14f20d7a1e41ad43c82daa3905b54a20b729a416c534835e86906b50d20b7a8a41eb50483d460907a4c120b7290416e52c42daa5885b94a10b6a94213f5444278a8885b94910b6a92213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x674e1a2438014047c087009440400856800000b003c5c2a3180088d0000aa25cac02c0c007800064c00480000026bd820524151b4c0188b00004a800280270004040890c0c18d0004202000000ba398b5350f154354432c650d500ca8d6494c328b597430ca8d6490c328bd95430ca8f6550c32c3d95430cb854394432c350d510cb265454432c9551510cb854354432c9d0d510cb464354432c950d510cb454354432c150d510cb894394032d8546500cb0d4354032ca951500cb295454032e250d500cb625154032d8545500cb2b4354032d290d500cb294354032d250d500cb094354032c350c524c6696014f21c314d43c86696014d21c314d4348664654c521e150d314870d43149309958453c830c5350f2099584534830c5350d209a1953048389434c1208758c544424c6354910cc55110043515344010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x83018080044501c00000003c050d5194032e028728aa01970143545500ca84b80a6a1e43425c05350d21c08caa1a6290d057114d43c8282b88a6a1a4182195434c120
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s4K5 (864+((h/16+packedAt s4K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s4K4 (4077+((h/45+packedAt s4K4 (3672+(h % 45)*9) 9) % 287)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e3f8ff1fc3c78ff1c47e3f0fc7071ff13343f
  | 1 => 0x1fc7f1fe3fc07f1fe078fc7f0f807e3f2cc8cf
  | 2 => 0xe007fe003fff8018ff80ff800fff8038cf0f0c
  | 3 => 0xfff800003fffffe0ffff00000fffffc0f00ff0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4210a02204809100040120902411108a011415
  | 1 => 0x8481044048092020200844220882241404484a
  | 2 => 0xc1b224e4919832516c80e9066d2704a64f0d0c
  | 3 => 0x8004909222040029152000882484900b002a0
  | 5 => 0x1124498003324494da64924cc00c0900faa000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeefeeefe88fe88feeefeeefe88fe88feeefeeefe88fe88feeefeeefe88fe88feeefeeefe88fe88feeefeeefe88fe88feeefeeefe88fe88feeefeeefe88fe88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36428
namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x42c2cd2740952003a540075e7d088540488200b8e001e7918e4c6d1180040000004c68a502560c28180055a00929065ccab00180686023582007000149106ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x194f21200000c62f001c8b076030a8f624350e87234309d402410010c007e12800180a438a00000000007c7a42120663b14898a24d000000004000000035000dc001941000b2552a000006d0980058492b000705f0c000d81d3b8445a210809c2e5a3783c640000000c400000000000002002c570007c007117080f070239cca6401f9acba3d18948ce0800214607d40800bc2221000b60341980000000000120e28070008615800003c230000068011fcf80005834006911800004f1b1142a64000500e00330000a1b22000984b3a170346e250009c1e000000000000000009030d000101070a08070300000a0e030106030100140100020f020302020101000206020d0400000003000004b7296876d52d0f5ca5a1eb54b439eaa4876f5250ed8a4a1e7d4d43d7a9287ac5250e7ca821d794f42aea9e853e54cca7aa9996b95332d6aa665af43ccb5a87995b54732b6a86659d438cadca5194f950329eaa0659d430caeca2195d54432bd2806579500cb5ca8196b55032b729865ce530cb5e86197390c32d6a1865cd430cb1a86197994432b6a8865e5510cacaa2197a94032b6a8065e9500cad2a0195b94a41b6a94835e53106baa620db94841b6a90837a50106f2a020cf953319eaa6639d43cc6dca518db54a31cea1a636f524c6d8a498cf950319eaa0636e520c6daa418de94031bca80636e53c86d8a790ebd0f21d6a1e436d50c86daa510db94d21b629a43af434875a8690f9d4521f318a43e531486dea090db94821b7294816d52902bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc33a87985b94a30b6a94619d434c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c2dca7905b14f20d7a1e41ad43c82daa3905b54a20b729a416c534835e86906b50d20b7a8a41eb50483d460907a4c120b7290416e52c42daa5885b94a10b6a94213f5444278a8885b94910b6a92213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x14b03141880c0e5e4c01200848823a0c40f007cb2b3c0082d128cd99009caa9005c6804c0120008c52a234b802a000141c0a1d801160d10403c4004000242001215a398b5350f154354432c650d500ca8d6494c328b597430ca8d6490c328bd95430ca8f6550c32c3d95430cb854394432c350d510cb265454432c9551510cb854354432c9d0d510cb464354432c950d510cb454354432c150d510cb894394032d8546500cb0d4354032ca951500cb295454032e250d500cb625154032d8545500cb2b4354032d290d500cb294354032d250d500cb094354032c350c524c6696014f21c314d43c86696014d21c314d4348664654c521e150d314870d43149309958453c830c5350f2099584534830c5350d209a1953048389434c1208758c544424c6354910cc55110043515344010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4501c030188000408000007c050d5194032e028728aa01970143545500ca84b80a6a1e43425c05350d21c08caa1a6290d057114d43c8282b88a6a1a4182195434c120
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (4032+((h/45+packedAt s5K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s5K3 (1996+((h/16+packedAt s5K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f8ff1fc3c78ff1c47e3f0fc7071ff13343f
  | 1 => 0x1fc7f1fe3fc07f1fe078fc7f0f807e3f2cc8cf
  | 2 => 0xe007fe003fff8018ff80ff800fff8038cf0f0c
  | 3 => 0xfff800003fffffe0ffff00000fffffc0f00ff0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4210a02204809100040120902411108a011415
  | 1 => 0x8481044048092020200844220882241404484a
  | 2 => 0xc1b224e4919832516c80e9066d2704a64f0d0c
  | 3 => 0x8004909222040029152000882484900b002a0
  | 4 => 0x1124498003324494da64924cc00c0900faa000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88feeefe88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36428
namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x164874600f9a2048e81000030c1d120194b3f0640f32a452a94000008618abc589401c6015ca32e78b361a019c028984005c11ec50110028344dab70001142201d0803645fbb709d2861204a0080001001e00b85001c480002800001ff95001fd5401ff15005ff43016fd0c05fe43017f50c05bd43017f10c07ff42007f90801fd4201ff10805ff32017f8c805fd32017f0c809ff5000ff94001fd5000ff14007ff4000ff90001fd4000ff10005ff3000ff8c005fd3000ff0c001ff20007bc8003fe20007f48001ed2000ff08003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1a4008ff90d20047fa8690023bd4348011fe21a4001bfd892005ffea49002fef524800fff2924000fb94920007faa490003ed524800ffe292400bfb14920057fe849002bef424800fff2124000fb90920007fa8490003ed424800ffe212400afb10920047fe6490023ef324800fff1924008fb8c920047fa6490023ed324800ffe1924008fb0c920007fec290002ff6148013ff30a400cbf98520007fac290027fc61480197e30a400bffd452004ffca290003fd5148013fe28a400affd052004ffc8290003fd4148013fe20a4008ffcc52004ffc6290023fd3148013fe18a4007ffc8520007de4290027fe2148013f710a4000ff48520007da429001ffc2148013f610a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fd1824001ff4c120047f26090007fc3048003ff9024007fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001ff04120007deca9002fee6548001f6b2a400bfb19520007dec89002bee6448001f6b22400afb1912005fdea89002bee5448001f6aa2400afb15120047dec690023ee6348011f6b1a4008fb18d20047dea6900236f5348011f729a4008fb54d20046daa690023ec5348011f7a1a4008ebd0d20047dc8690023ed4348011d6a1a4008fb10d20007dec290002ef6148013f730a4000fb5852004fd8c29002fef5148013f728a4000fb5452004fd8a29002bef4148013f720a4000fb5052004fd88290023ef3148013f718a4008fb4c52004fd86290007ef604800377b024000fad812000fdea090007ee5048003f6a824001fb1412000fde8090007ee4048003f6a024001fb1012000fde6090007ee3048003f51824001fb4c120047d26090007ec3048003f78824001fb8412000fd82090003ff64440017fb222006ff9911001dfcc888003fd64440017eb222006ff1911001df8c88801bfe5444001feaa22006ff1511002ffec688016ff634400bff31a2002bf98d1002ffac688016fd634400bfe31a2002bf18d1002ffe8688017bf434400bff21a2005ff50d1002f7a8688017fc4344001ffb122000bfd8910007fcc48801efe6244001f73122000bb98910007fac488002fd6244001f6b122000bb58910007f8c48801efc624400dffa122000ff90910007fa848801bfc424400bff9922005ff8c91002ffa6488017fc32440037fb022001ffd411000ffca088007fa5044003fea822000fe5411000ff8a088007ff4044003ff2022001fe9011000ffa8088003f94044003fe2022001ffcc11000ffc6088007fa3044003fe9822005fe4c11000ff86088007ff2044003f79022001ff8811000ffa4088007ed2044003fe1022001ff8411000fec2088007fc1044003fc0822001fc04110
  | 1 => 0x7be4050003fe2028001ef1014000ff080a0007ff3050003ff1828001ff4c14000ff860a0007fe2050003fe1028001ffc414000ffc20a0007fa1050003fe0828007ffd972003dfecb9001ffe65c80097f32e4007ff59720005facb9001ffc65c800f7e32e4007ffd932003dfec99001ffe64c80077f3264007ff59320005fac99001ffc64c800f7e3264010ffd532007ffca990003fd54c801ffe2a64007ffd8f2003dfec79001ffe63c80057f31e4007ff58f20075fac79001ffc63c800f7e31e400effd4f20076fea79003bfe53c801dfea9e400edf54f20077f8a79003bff43c801ddfa1e400eff90f20077fa879003bbd43c801dfe21e4001bf98b2003ffea590043ef52c800fff2964007fb94b2003ffaa590003ed52c800ffe2964007fb14b2003ffe859003fef42c800fff2164007fb90b2003ffa8590003ed42c800ffe2164007fb10b2003ffe659003bef32c800fff1964007fb8cb2003ffa659003bed32c800ffe1964007fb0cb2003ffec39001ffe61c80197f30e4007ff58720005fac39001ffc61c80197e30e4010ffd472006ffca390003fd51c801bfe28e400fffd072006ffc8390003fd41c801bfe20e400effcc72006ffc639003bfd31c801bfe18e4007ffc872003fde439001ffe21c801bf710e4007ff0872003fd84390006fd60c8003ffa864001ff9432000ffaa190007fc50c8003ffa064001ff9032000ffa8190007fc40c8003ff9864001ff8c32000ffa6190007fc30c8003ff1064001fb8832000ff44190007fc20c8003f61064001ffc432000ffc2190007fc10c800ff7b2e4010fb99720007dacb9001fec65c800ff7b26400ffb99320007dac99001fec64c8021f7aa6400ffb95320007daa99003fec54c800ff7b1e400efb98f20077dac79001fec63c801df7a9e400edbd4f20077dca79003bed53c801db6a9e400efb14f20077de879003baf43c801df721e400efb50f200775a879003bec43c800ff7b0e400dfb98720007dac390002ed61c800ff630e4010fbd472006fdca390003ed51c801bf628e400ffbd072006fdc8390003ed41c801bf620e400efbcc72006fdc639003bed31c801bf618e4001bb5832000fdea190007ee50c8003f6a864001fb1432000fde8190007ee40c8003f6a064001fb1032000fde6190007ee30c8003f69864001fb0c32000fde2190007ee10c8003f60864000ffd9520005feca9002ffe65480097f32a4000ff59520005faca9002ffc65480097e32a4000ffd9120005fec89002bfe64480077f3224000ff59120005fac89002bfc64480077e322400bffd5120057fca890003fd5448015fe2a24008ffd8d20045fec690023fe63480057f31a4008ff58d20045fac690023fc63480057e31a4008ffd4d20046fea690023fe5348011fea9a4008df54d20047f8a690023ff4348011dfa
  | 2 => 0x420cffa64a101ffc3250801ffb0a8400bfd85420c7fcc2a1032fe6150801feb0a8418ff18542065f8c2a106bff5150831ff28a8418ff1454201ffe82a100ffe4150807fe20a8419ffcc5420c7fc62a1067fd3150831fe18a8418ff8854203ff842a1003ff60508017fb028417ff9814200dfcc0a1003fd605082ffe3028401bf181420d7fea0a105ffe505082ffe2828403ffd014201ffc80a100ffc4050833ff9828417ff8c1420cffa60a105ffc305082fff1028407ff081420c7fe20a105ffe105082ffe0828401bfd9550007fec8a8002ff645402dff322a003bf99150007fac8a805bfc64540077e322a004ffd5150026fea8a8013fe5454009feaa2a000df55150027f8a8a8057ff635402b7fb1aa015ff98d50015fcc6a8057fd635402b7eb1aa015ff18d50015f8c6a8013ff5354009bfa9aa004ff94d50027faa6a80577d5354009fe29aa015ffd0d500af7e86a8057fe435402bfea1aa015ef50d500aff886a8003ff62540017fb12a000ff98950007fac4a8003fc625400f7e312a004ffd4950027fca4a8013fd5254009fe292a016ffd0950007fc84a8003fd425402dfe212a015ffcc9500affc64a8057fd325402bfe192a000ffd8550005fec2a8053fe61540197f30aa000ff585500a7f8c2a8032fc6154009ffa8aa004dfd4550027fca2a8013fc515402dffa0aa014ff90550007fa82a8053fc415402bff98aa014ff8c5500affa62a8053fc3154029ff10aa014ff0855000dfec0a8007ff5054009fda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fe202a001ffcc15000ffc60a8007fd3054003fe182a001ff8815000ff840a8007ff1054003ff082a001fe8415000ff820a8003ff65500017fb2a8013ff99540025fccaa0003fd65500017eb2a8013ff19540025f8caa0006ff6450007ffaa28003ff9514001f7ca8a000ffd5450001deaa28003ff15140097fec6a004aff6350025ff31a8002bf98d40097fac6a004afd6350025fe31a8002bf18d40097fea6a004b7f5350025ff29a8012ff54d40096faa6a004bfc5350007ffa1a8003efd0d4001ffc86a000ffd4350025dea1a8003ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a001efc6250027ffa928000ff94940007faa4a004ffc5250007ffa128003ff9094001ffa84a000ffc4250025ff9928012ff8c940097fa64a004bfc3250001ffb0a8000bfd854008ffcc2a0032fe6150001feb0a8011ff18540065f8c2a004fff5150023ff28a8000ff5454008ff8a2a000fff4150007dfa0a8003ff9054001ffa82a0003bd4150007fe20a8012ffcc54008ffc62a004bfd3150023fe18a8011ff8854008ff842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028003fed014000ffc80a000
  | 3 => 0x140080000200a000008010020240600200a0000100103000c0a80100200c020100000280001a032008000010120580e0030020540100600001c0e0010001680f00007001c00005074020080040040000081b00a008000010180080002200c01402005006000028000020140102f00803c0002d00600c010120480200800601e068000070000040480001dfec8aa00ffe5455007bf2a2a803ff1515401f78a8aa00f3c5455041ffb1aa820bfd8d54107fcc6aa00afe6355041feb1aa820bf58d54107f8c6aa00afc6355007ffa1aa803efd0d5401ffc86aa00ffd4355041dea1aa803ff10d54007fec4aa002ff6255001ff312a800ff58954007f8c4aa01efc6255007ffa12a803ff1095401f7884aa083ff3255041ff192a820ff4c954107f864aa003ff60550017fb02a81fff9815400dfcc0aa003fd605503ffe302a801bf18154027fea0aa0137f5055009ff282a804ff1415401ffe80aa00fbf4055007ff202a803ff10154107fe60aa07ffe3055041fe982a81fff0c1540fffc40aa07ffc205503fff082a81fff0415403ffecb2101eff659080fff32c8404bf9964203ffacb21002fd659080ffe32c8407bf1964201dfac92100fff5490807ff2a48403ef9524201ffaa921003bd5490807fe2a48407ffd8e4203dfec72101ffe63908057f31c8407ff58e420edfac72101ffc639080f7e31c841dffd4e420eefea721077fe539083bfea9c841ddf54e420eff8a72100fff4390807dfa1c8403ff90e4201ffa8721077bd4390807fe21c8407bf98a4203ffea52101ffe529080ffe2948407ffd0a4203f7e852100fef429080ffe2148407fb10a4203ffe652101ffe329080ffe9948407ff0ca4203ffec32101ffe61908197f30c8407ff58642005fac32101ffc61908197e30c841effd46420e7fca321073fc5190807ffa0c8403ff9064201ff88321077ff3190839ff18c841dff4c6420e7f8632101ffe219080ffe10c8407ffd824203ffcc121006fe609080ffeb048400bf5824203ff8c121006fc609083dffa84841bff942420dff8a12100fff4090807ff2048403ff102420effe612106ffe309083bfe984841bff0c24203ffc412101ffc2090839ff884841bff842420dff82121003ff65508017fb2a841aff99542025fccaa1003fd65508017eb2a841aff19542025f8caa101eff6450807ffaa28403ff9514201ffaa8a100ffc5450833ffb1a8419bfd8d420cffcc6a100afe6350833feb1a8419bf58d420cff8c6a100afc6350833ffa9a8419dfd4d420cffca6a1067fd5350833bea9a8419ff14d4201ffe86a100fbf4350807ff21a8403ff50d420cf7a86a100ffc43508077fb12841affd494203ffca4a1003fd525080ffe2928403ffd094201fde84a101ffe425080fdf2128407ff1094203f7884a100fec4250833ff9928407ff8c9
  | 4 => 0x5c16b80038a000171866495ec7887c00011a3d8d3e63718b29665b4c20a810314e8a5772e90910434112b0768d14495640a3579b4000000008f9a34ee448001ef23050cfdb5795ad5a0008800076d9817f48c81d4d347000534a7000006000fe2933a464c0012109e71c003380003c00027c02f2f8001f628ea55602a5000c9b95cdc3aa039151a602a4fc3a1394344ce8d5dc562001363329863a874236672d223683c4cc0687d8af1709ac9a1b06240de8f2900871a44816c3ea5e8c298d384b9c83321b9c95803d1925e38c55b53594d1f8097c18a174000000002cac0f258000018c02c29448c00000000cbea588e1eac380011d2a83881f90e3347582f8002d4694c500036a0770e0001a9798570b42fc6a07dc0c47051800000000555944000310000009500000085ad8025b7cc584920a7a41388351a431080c200096d020f20001853817fa04aa83720839eac97415e2c4cedab1da62c93cfe87366e7880ac000004e998b0064c0c4f0a2f0fc3bcf680506c34a2380ab065a50987d679bc4001a70d457a000125c27000033d134305a2b420000005a8001eecb583800000548912850f4424950d117e01ae21808c934d2e8c43c636867996266000026f209a28991e8e017aeede9f82106f8a992757a1998f2c90f275d13268240cad549b4086cb1832871f86bc822e50c02a90913b035c954c297000b80215ac3ce6487b31d67c761320a006a27c2f24937421190835e55938bc9512be4a007c3957207cb9a7f130468cc02a56005b1d1f42fd459188823327b14eadb11a96914001dd48087eac36886551db46b183640026f06d4402320938645a04eaf372b712a982040a19a919e292c54003245166acc88000a4ca0254675e0072602e61c2b3806c6f366c25914d057c2755a00069c5dcf8a5445abe4388ce0000004e2f829eb142d317260d0d139815fcd24d11f2667028530ee27cb51191f90000002c1756890004b13d1120bc7c1cb00900203c0380000001808800004000008130060080700000c0000404a06e02c06804000000010000020000301c02602c000120000000a0000000000080904c0000102c00e0040680100a004000020160800200000a0184600501802c04000000014000080020000101c01400c1081b0000601280400c00801800012004000000340180e8020000240300b008000000070000080480600221800002032014010000040000480001c0480000001200c000000160800080101c000000000d80280300001a00c020010080080580101400c008000260a4000010160300100e00613401006002000000000100040080100c00c000000060040280c000000000000a60200001004e0080080700801c0800002401443804004024180040000040400505e0000000100e0000400000a02400831000004000050
  | 5 => 0xde152b04e827d4c388c0005756cb795e0d225c5154d9dd52c80a212a3b3a000000df6aa5e1691e541a9d08bad3000a319f9a130e5c98c850442a844333d8502c9668001fe2d8001ea677988992a00009e02619701ea9d3d01183c001640d742e08b1c8b945cd04ec9a021eb317e30544057094a9f482c6812ad926c41d26033000360f02405083cc008702621e00da53000bd9510bb011bf40c0006649e4001764141556e9ab8001121e8fe4ae08e2a13848e000000a56269ccc022543cb4004a4239820480b5402ebac0b15d29898cba10d4dc0350d82d11ecb70004e000a45aac45a48ce84399f42c1d4a2047e69d3d2283a5666fd810ed008cbc669c10002cd818000eca99a01f34226411820e55c6d832000000a0463b458d02b393b0f094000000d600000121d14496000f26763bec803625c0000c97d834946c4f030eb4164dd419e45763808500046a000d6a9200026c000130227345d1eb6169c8ef0005569954a048364afd0c8d50820171226a196d300a33c000cba0a5004c2ab0728003d000000000016bb4d508c114c7d282155ac7b99183700001c000c9000001215e38002840014200045500d63065000660f4000001a33330009441f0002b024cc48004bc001520138333e4000000008dd019cbb908ad85044588a3d720654d236c000000004b40000000000012c80622001400c664f91055c00000098d4af300000000350000000000000000000024a1782c0ac8000b60004a3350000ac000000000003bad53a60000021f00014c183040000014f1bb59e830e49840000000000e8000019663e338590000ca49000000000000621949fe116c344cab50965c4fb80616d3206a13c514d4f4c96f43ab1c35afa694d35952675742c41215b1d81647774993c46d7aa2c24cb198d8000678fc4901baaeb08108854f663c201414becc365aad47839197335800b44de0004ea000064e64660000016056e070390006aebbd7f9403f42a000000668639110000009b41c00000094808000000444b40001d2860d715a5d8a8d710004b208c738fa2c5000dc05c625188000295700014e31400000000000402980488452d6d444b824c139c400002000744ea2430000000020f26a6c53f019044c70001253e0ca60000047a074000bd5ee2b0d22a80005b9883226906dcff80833565089a1409366c3f91c0c6144b38dd0ac2dce50005c600eb0868de8cd81a148000000e56609485b58624d4b00000034b2582074417d00
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7058910006fb705891014efa3058910006f9305891014eef205891014eee205891014eed205891014eec2058910006ef765891003cef7658910007af7458910007ac7458910006ef6458910006ee6458910006ed6458910006ec6458910007cf7358910007cc7358910006ef6358910006ee6358910006ed6358910006ec6358910007af4358910007ad435891014def7058910007eb705891006deb705891014fea505891014fea405891014fea3058910007e9305891014fe6105891014fe8105891014fe01058910006ef7458910006af7458910006ee7458910006ed7458910006ec7458910006ac7458910006ee5458910006ed5458910006ec5458910006ef7358910006cf7358910006ee7358910006ed7358910006ec7358910006cc7358910006ef4358910006af4358910006ee4358910006ed4358910006ad4358910006ec435891014eef705891014cef7058910006eb705891014eef505891014eee505891014eed505891014eec505891014eef405891014eee405891014eed405891014eec405891014eef305891014eee305891014eea305891014eed3058910006e9305891014eec305891014eee105891014eed105891014eec1058910144fe761891013dee721891003eee6218910006ed6218910137f0101891003cff7690910004fe7690910004fd769091003cfc7690910006bf649091001ebc649091003eee6290910006ed62909100dff01090910004ff7650910004fe7650910004fd7650910004fc765091003eee6250910006ed62509100bff01050910065f87654110026f87654110064f8765411000dfb755411000f7b75541100077b6554110026fa6554110026f86554110127786554110005fb74541101277b545411000779545411012dfb735411012df973541101277b535411011f79535411011fbb435411011fb94354110007ea6254110007e96254110007f37154110065fa7154110065f871541100a7f07154110065f0715411000efb615411000ff361541100a77b51541100a7f251541100a77951541100a7f24154110007f141541100a7f2315411011ff131541100a7eb21541100a7e92154110065f8765011001ef87650110064f87650110005fb7550110005f9755011000dfb745011000fbb7450110007bb645011001efa645011001ef86450110037b86450110037ba5450110007b95450110115fb7350110115f9735011010f7b535011010f795350110037bb435011010fb94350110007ea6250110007e96250110007f37150110065fa7150110065f8715011008ff07150110065f0715011000efb615011000ff3615011008ff25150110007f1515011008fbb415011008ff2415011008fb94150110037f14150110007b1415011008ff2315011010ff1315011008feb215011008fe92150110
  | 1 => 0x9110036bc42d911000cff71d9110064fe71d911000cfd71d9110064fc71d9110176bf41d9110176bd41d9110176ef21d9110176ed21d9110064ff70d911000cfe70d9110064fd70d911000cfc70d9110166bf40d9110166bd40d9110166ef20d9110166ed20d911001cff76591100057f75591101257c7559110036bc645911015df7715911016dfb7059110157f01059110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c7559110164ff7459110006bf7459110036be5459110004ff7359110014fe7359110004fd7359110014fc73591100067f53591100067d5359110036bf4359110006bd4359110004ff725911003cfc725911015cff7159110006f7715911008eef215911008eed2159110154ff7059110006fb7059110156ef2059110156ed2059110004ff7655110004fe7655110004fd7655110004fc765511001ebe6455110006bd64551100373c545511000dfa70551100fff0105511003cfe76d8910147f010d891001cfe74d8910004fd74d891001cfc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910006bf43d8910006bd43d8910064ff70d891000cfe70d8910064fd70d891000cfc70d8910146fa30d8910006f930d8910146ef20d8910146ed20d891014cfd7698910006ef629891004df9709891013ff0109891014ced7698910006ef6498910006ee6498910006ed6498910006ec6498910006ef6398910006ee6398910006ed6398910006ec6398910007af4398910007ad439891013ded7098910007e9709891004de9709891013fea509891013fea409891013fea3098910007e9309891013fe6109891013fe8109891013fe0109891003eef749891003eee749891003eed749891003eec7498910006ee5498910006ed5498910006ec549891003eef739891003eee739891003eed739891003eec7398910006ef4398910006af4398910006ee4398910006ed4398910006ad4398910006ec439891003eed709891013ced709891003ee9709891013eef509891013eee509891013eed509891013eec509891013eef409891013eee409891013eed409891013eec409891013eef309891013eee309891013eed309891013eec309891013eee109891013eec109891003cff7658910005bf7458910035bc7458910005df735891002ddc735891006dfb705891014ff01058910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc7358910006bf4358910006bd4358910006ef7258910006ef4258910006ec4258910006ef3258910006ee3258910006ed3258910006ec325891014cf
  | 2 => 0x7af4358520007ad435852013def7158520007e7615852004eee615852004eec615852004fe4615852004fe63158520007e5315852014def7058520007eb7058520005eb705852014fea3058520007e93058520005ef7654520005ee7654520005ed7654520005ec76545201d5ef7554520005ef7454520055ee7454520055ec745452005f6f54545200076d54545201cdef7354520045ee73545201cded7354520045ec735452005f6f53545201bf6d53545201bfaf43545201bfad43545201c5ef715452004eef615452005fe7515452004f6e515452004f6c515452004fe451545201b5ef705452000dee705452000dec70545201b6ef60545201b76f50545201b76d50545201b7ea30545201bfe930545201b7e71054520005ef7650520005ee7650520005ed7650520005ec7650520005ef755052005dee7550520005ed755052005dec7550520165ef7450520057ae5450520007ad54505201adef7350520045ee73505201aded7350520045ec73505201a76f53505201a76d5350520057af43505201a7ad435052015def715052004eef6150520057e7415052004fae415052004fac415052004fe44150520155ef705052000dee705052000dec7050520156ef6050520157af4050520157ad4050520157ea30505201a7e93050520157e7105052000fea76d812000dea76d812000eea76d812003feb75d812003fea75d812003fe975d812003fe875d8120007eb65d8120197ea65d8120007e965d8120197e865d812003feb74d812003fea74d812003fe974d812003fe874d8120007eb64d812018fea64d8120007e964d812018fe864d8120197eb54d812018fea54d8120007e954d812018fe854d812003feb73d812003deb73d812003fea73d812003fe973d812019de973d812003fe873d8120187eb63d8120187ea63d8120187e963d8120187e863d8120187eb53d81201876b53d8120187ea53d8120187e953d81201876953d8120187e853d8120187eb43d8120187ab43d8120187ea43d8120187e943d8120187a943d8120187e843d812003feb71d812003fea71d812003fe971d812003fe871d8120007eb61d812017fea61d8120007e961d812017fe861d8120197eb51d812017fea51d8120007e951d812017fe851d812018feb41d812017fea41d8120007e941d812017fe841d8120187eb31d812017fea31d8120187e931d812017fe831d812001cfe76d9110036be64d9110005ee72d9110005ed72d9110167f010d9110024fe75d9110004fd75d9110024fc75d9110154fd74d9110006bf54d9110036bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d9110036bf43d9110006bd43d911003cfe72d9110006ee72d911003cee72d9110004fd72d9110006ed72d9110004ed72d
  | 3 => 0xd7655120005ec76551201f5ef75551200076f655512005f6c65551201edef7455120007af6455120057ac645512005faf54551200576e54551200576c5455120057ac54551200572c54551201e5ef7355120045ee73551201e5ed7355120045ec735512005f6f53551201df6d5355120057af43551201dfad4355120005ef715512004dee715512004dec715512005f6f5155120057af41551200fdef705512000dee70551200fded705512000dec70551200feef60551200ff6f50551200ff6d50551200ffaf40551200ffad40551200ffea30551201dfe93055120135ee76d852005dee75d8520005ed75d852005dec75d8520006ef65d8520006ee65d8520006ed65d8520006ec65d8520055ee74d8520005ed74d8520055ec74d8520006ef64d8520006ee64d8520006ed64d8520006ec64d8520005ef73d8520045ee73d8520005ed73d8520045ec73d8520006ef63d8520006ee63d8520006ed63d8520006ec63d85200076f53d85200076d53d8520007af43d8520007ad43d852004eee61d852004fe661d852004eec61d852003def70d852000dee70d852013ded70d852000dec70d852013eef60d852013fea30d8520007e930d852013fe710d852013fe510d8520006ef75d8520006ee75d8520006ed75d8520006ec75d8520006ef74d8520006ee74d8520006ed74d8520006ec74d8520006ef54d8520006ee54d8520006ed54d8520006ec54d8520006ef73d8520006ee73d8520006ed73d8520006ec73d8520006ef53d85200066f53d8520006ee53d8520006ed53d85200066d53d8520006ec53d8520006ef43d8520006af43d8520006ee43d8520006ed43d8520006ad43d8520006ec43d852004eef51d852004eee51d852004eec51d852004eef41d852004eee41d852004eec41d852004eef31d852004eee31d852004eed31d852004eec31d852013eef70d852013eed70d852013eef50d852013eee50d852013eed50d852013eec50d852013eef40d852013eee40d852013eed40d852013eec40d852013eef30d852013eee30d852013eea30d852013eed30d8520006e930d852013eec30d852013eef10d852013ee710d852013eee10d852013eec10d8520145ef7658520005ef75585200076f75585200056f755852005dee755852005dec75585200076c755852005d6c7558520006ef6558520006ee6558520006ed6558520006ec6558520005ef7458520007af7458520005af7458520055ee7458520055ec7458520007ac7458520055ac7458520006ef6458520006ee6458520006ed6458520006ec6458520005ef7358520007cf7358520005cf7358520045ee7358520005ed7358520045ec7358520007cc7358520045cc7358520006ef6358520006ee6358520006ed6358520006ec63585200076f53585200076d5358520
  | 4 => 0x8520006ef64c852025eee64c8520006ed64c852025eec64c852003def73c8520045ee73c8520255ed73c852003dec73c8520246ef63c852024eee63c8520246ed63c852024eec63c85202476f53c85202476d53c8520247af43c8520247ad43c852014ded71c852013eef61c8520066ee61c8520066ec61c852000dee70c852000dec70c852003eef60c852003feb60c852013fea30c8520247e930c852000cfc764852014eef6248520005fb704852000df87048520066ec764852000cec7648520005ef7448520055ee7448520005ed7448520055ec7448520006ef644852023eee6448520006ed644852023eec644852022eef6348520236ee634852022eed6348520236ec634852022faf434852022fad4348520007eb704852000dee704852000dec704852014fe8704852003eef604852003feb604852014fea304852022fe93048520225ee76d952020ded75d952005eee65d952005f6e65d952005eec65d9520055ee74d9520005ed74d9520055ec74d952005f6f54d9520005ef73d9520045ee73d9520005ed73d9520045ec73d952005f6f53d95200076d53d9520007af43d9520007ad43d952004dee71d9520005ed71d952004dec71d95200076e51d952005f6c51d952003def70d952000dee70d9520215ed70d952000dec70d9520216ef60d95202176f50d95202176d50d9520217ea30d9520007e930d952021def7659520215ef75595200076f655952005eee655952005eec655952005f6c6559520005ef7459520055ee7459520055ec7459520005ef7359520045ee7359520005ed7359520045ec735952005f6f53595200076d5359520007af4359520007ad4359520005ef715952004dee715952004dec715952020def7059520007eb7059520005eb705952020eef605952020fea3059520007e93059520205ee76d912005dee75d9120005ed75d912005dec75d91200bded74d9120056ee64d9120057ae64d9120056ec64d9120057ae54d9120005ef73d9120045ee73d9120005ed73d9120045ec73d91200076f53d91200076d53d9120057af43d9120007ad43d912004dee71d9120005ed71d912004dec71d9120007ae41d9120057ac41d912003def70d912000dee70d91200dded70d912000dec70d91200deef60d91200dfaf40d91200dfad40d91200dfea30d9120007e930d91201fdef7659120005ef755912005dee755912005dec75591200ddef7459120007af6459120056ee6459120056ec6459120057ac6459120005ef7359120045ee7359120005ed7359120045ec73591200076f53591200076d5359120057af4359120007ad4359120005ef715912004dee715912004dec71591200bdef7059120007eb7059120005eb70591200beef60591200bfea3059120007e93059120005ef7655120005ee7655120005e
  | 5 => 0x26ec655492005f6c6554920005ef7454920055ee7454920055ec7454920295ef7354920045ee7354920295ed7354920045ec735492005f6f535492028f6d535492028faf435492028fad4354920005ef715492004dee715492004dec7154920007eb705492000dee705492000dec705492020fe8705492003eef605492003feb605492020fea305492028fe93054920205ee769092003eee769092003def759092005dee7590920005ed759092003dec75909200bded749092001eee649092001eec6490920057ae5490920007ad549092003def7390920045ee7390920285ed739092003dec739092027f6f539092027f6d5390920057af439092027fad439092004dee7190920005ed719092003dec719092000dee709092000dec709092003eef609092003feb60909200dfea309092027fe9309092001cff765092000cfe76509200bcfd765092000cfc7650920006bf645092001ebc64509201fdef7250920005fb705092000df8705092000dec765092001eec765092000cec7650920005ef755092005dee7550920005ed755092005dec755092003def745092003faf7450920007af645092001eee645092001eec6450920057ac6450920275ef7350920045ee7350920275ed7350920045ec735092026f6f535092026f6d5350920057af435092026fad4350920005ef715092004dee715092004dec7150920007eb705092000dee705092000dec70509200bfe8705092003eef605092003feb60509200bfea305092026fe93050920064fe76d852003dee72d852000ded72d852004ef661d852004fe621d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520006bf43d8520006bd43d852013eef72d852000cfd72d852013eed72d852000ced72d8520064fc72d8520006ef52d8520006ee52d8520006ed52d8520006ec52d8520006ef42d8520006ee42d8520006ed42d8520006ec42d8520006ef32d8520006ee32d8520006ed32d8520006ec32d852004eee21d852004ef621d852004eec21d852000cfe70d852003cfd70d852000cfc70d852013efa30d8520006f930d852013eee20d852013eec20d852013ef710d85200057f755852005d7c7558520005bf7458520055bc7458520005df7358520045dc735852004ef46158520004ff7654520004fe7654520004fc7654520005ef725452003dec7254520004ff7650520004fe7650520004fc7650520005ef725052003dec7250520135ee76c852003eee76c852003def75c852005dee75c8520005ed75c852003dec75c8520006ef65c8520266ee65c8520006ed65c8520266ec65c852003def74c8520055ee74c8520005ed74c852003dec74c
  | 6 => 0x71050720024fe76d952005e7e65d952003dee72d952000ded72d952005f6f52d952001cfe74d9520004fd74d952001cfc74d952005e7f54d9520004ff73d9520014fe73d9520004fd73d9520014fc73d952005e7f53d95200067d53d9520006bf43d9520006bd43d952000cfd72d9520216ed72d952000ced72d952005e7f52d952005eef52d952005eec52d9520064fe71d9520004fd71d9520064fc71d95200067e51d952005e7c51d952003cff70d952003cfd70d95202167f50d95202167d50d952005e7c655952021def7259520214ff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff7359520014fe7359520004fd7359520014fc735952005e7f53595200067d5359520006bf4359520006bd435952021cff7259520006ef725952005eef525952005eec5259520004ff7159520064fe7159520064fc715952020cff7059520006fb705952001cfe76d9120056be64d912003dee72d912000ded72d9120057af42d9120024fe75d9120004fd75d9120024fc75d9120056be54d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d9120056bf43d9120006bd43d912003cfe72d912000cfd72d91200deed72d912000ced72d912003cfc72d9120056bf42d9120056ef42d9120056ec42d9120064fe71d9120004fd71d9120064fc71d9120006be41d9120056bc41d912003cff70d912003cfd70d91200debf40d91200debd40d9120056bc64591201fdef7259120004ff7559120024fe7559120024fc75591200dcff7459120006bf7459120004ff7359120014fe7359120004fd7359120014fc73591200067f53591200067d5359120056bf4359120006bd43591201fcff7259120006ef7259120056ef4259120056ec4259120004ff7159120064fe7159120064fc71591200bcff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200267c6555120006bf645512001ebc64551200573c5455120005ef725512003dec725512005f6c5255120057ac4255120225ee769492003eee769492020ded7594920026ee6594920026ec6594920055ee7494920005ed749492003dec749492005f6f54949200076d549492003def7394920045ee73949202a5ed739492003dec739492005f6f539492029f6d539492029faf439492029fad439492004dee7194920005ed719492003dec719492000dee709492000dec709492003eef609492003feb6094920217ea309492029fe93094920024ff765492000cfe765492020cfd765492000cfc76549200067f65549200267c655492021def7254920005fb705492000df8705492000dec7654920026ec765492000cec765492003def755492003f6f75549200076f6554920026ee6554920
  | 7 => 0x532006dec71553200876f515532007faf41553200fdef705532000dee70553200fded705532000dec70553200feed60553200ff6f50553200ff6d50553200ffaf40553200ffad405532003def7658720005ef7558720085ee7558720085ec755872003eef6558720006ee6558720006ed655872003eec6558720005ef745872007dee745872007dec745872003eef6458720006ee6458720006ed645872003eec6458720005ef7358720075ee7358720005ed7358720075ec735872003eef6358720006ee6358720006ed635872003eec63587200076f53587200076d5358720007af4358720007ad435872003def715872003fe7615872006eee615872003eec615872003fe4615872006fe63158720007e5315872000dee705872000dec705872014eed605872014fe7105872014fe51058720006ef7558720006ee7558720006ed7558720006ec7558720006ef7458720006ee7458720006ed7458720006ec7458720006ef5458720006ee5458720006ed5458720006ec5458720006ef7358720006ee7358720006ed7358720006ec7358720006ef53587200066f5358720006ee5358720006ed53587200066d5358720006ec5358720006ef4358720006af4358720006ee4358720006ed4358720006ad4358720006ec435872006eef515872006eee515872006eec515872006eef415872006eee415872006eec415872006eef315872006eee315872006ee6315872006eed3158720006e5315872006eec315872014eed705872014eef505872014eee505872014eed505872014eec505872014eef405872014eee405872014eed405872014eec405872014eef305872014eee305872014eed305872014eec305872014eef105872014ee7105872014eee105872014eec1058720005ef765472003dee7654720005ed765472003dec76547201d5ef7554720005ef745472007dee745472007dec74547200876f54547200076d54547202c5ef7354720075ee73547202c5ed7354720075ec73547200876f53547202bf6d53547202bfaf43547202bfad43547201c5ef715472006eed6154720087e7515472006f6e515472006f6c515472006fe451547201b5ef705472000dee705472000dec70547201b6ed60547201b76f50547201b76d50547201b7e71054720005ef765072003dee7650720005ed765072003dec7650720005ef7550720085ee7550720005ed7550720085ec7550720165ef745072007fae5450720007ad54507202b5ef7350720075ee73507202b5ed7350720075ec73507202af6f53507202af6d535072007faf43507202afad435072015def715072006eed615072007fe7415072006fae415072006fac415072006fe44150720155ef705072000dee705072000dec7050720156ed6050720157af4050720157ad4050720157e
  | 8 => 0x305ef7354b20075ee7354b20305ed7354b20075ec7354b200876f5354b202ff6d5354b202ffaf4354b202ffad4354b20005ef7154b2006dee7154b2006dec7154b2000dee7054b2000dec7054b2003def7650b202f6ef7650b20005ef7550b20085ee7550b20005ed7550b20085ec7550b2003faf7450b2001eee6450b2003eec6450b202edef7350b20075ee7350b202eded7350b20075ec7350b202e76f5350b202e76d5350b2007faf4350b202e7ad4350b20005ef7150b2006dee7150b2006dec7150b2000dee7050b2000dec7050b20004ff7558720024fe7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff7358720014fe7358720004fd7358720014fc73587200067f53587200067d5358720006bf4358720006bd435872000cfe725872003eee7258720064fd725872000cfc725872003eec725872000cec7258720006ef525872003eee5258720006ed525872003eec5258720006ef425872003eee4258720006ed425872003eec4258720006ef325872003eee3258720006ed325872003eec325872003ef7715872006ef63158720006f5315872003eef215872003ef7215872003ee7215872006eee215872003eec215872003ef4215872003eef205872014eee205872003eec205872014ef71058720004ff7654720004fd765472003cfc7654720005ef725472003dee725472003dec7254720004ff7650720004fd765072003cfc7650720005ef725072003dee725072003dec725072003def765972003def755972003f6f6559720086ee655972003eec655972003f6c6559720005ef745972007dee745972007dec7459720005ef7359720075ee7359720005ed7359720075ec73597200876f53597200076d5359720007af4359720007ad4359720005ef715972006dee715972006dec715972003eef615972020def705972000dee705972000dec705972020eed605972020f6f505972020f6d505972003def7659320005ef7559320085ee7559320085ec755932003def745932003faf645932007eee645932003eec645932003fac6459320005ef7359320075ee7359320005ed7359320075ec73593200076f53593200076d535932007faf4359320007ad4359320005ef715932006dee715932006dec715932003eef61593200bdef705932000dee705932000dec70593200beed60593200bfaf40593200bfad4059320005ef765532003dee7655320005ed765532003dec76553201f5ef75553202df6f65553202df6c65553201edef74553202dfaf64553202dfac6455320087af545532007f6e545532007f6c545532007fac545532007f2c54553202d5ef7355320075ee73553202d5ed7355320075ec73553200876f53553202cf6d535532007faf43553202cfad4355320005ef715532006dee715
  | 9 => 0xc75d894000cfd74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d8940336bf43d8940006bd43d8940336ee42d8940336ed42d8940006ef32d8940006ec32d8940064fe71d8940004fd71d8940064fc71d894001cfd70d89401feef20d8940006ef6298940055f9709894007dfb705894003eee6218940006ed6218940004fe7694940004fd769494003cfc76949400073d5494940004ff7654940004fe7654940004fc7654940064fe76d854008ef661d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540064fc74d854032ebe54d8540006bd54d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854032ebf43d8540006bd43d854003cfe72d8540004fd72d854008ef641d854032ef541d854001cfd70d854015eef20d854015eed20d854015ef710d85400057f755854009d7c755854008ef46158540325fb7058540004fe7654540004fc765454001dbe74545400073d545454000dbc7650540066bc765054000cbc7650540005bf7550540005bd7550540006bf6550540006bd655054031dbf735054031dbd7350540316bf6350540316bd63505403173f53505403173d535054001dbf715054001fb77150540007b76150540066be6150540066bc615054008fb46150540007bb705054000dbe705054000dbc7050540157b8705054001ebf605054001fbb6050540157b71050540157ba105054003e7f7559720004ff745972001cfe745972001cfc7459720004ff7359720014fe7359720004fd7359720014fc73597200867f53597200067d5359720006bf4359720006bd435972000cfe725972000cfc725972003eec725972000cec7259720086ef525972003e7e525972003e7c525972003eec5259720004ff7159720064fe7159720064fc715972003eef215972020e7f505972020e7d505972003eef2059720004ff7559320024fe7559320024fc755932003ebf7459320004ff7359320014fe7359320004fd7359320014fc73593200067f53593200067d535932007ebf4359320006bd435932003cff725932000cfe725932003cfd725932000cfc725932003eec725932000cec725932007eef425932003ebe425932003ebc425932003eec4259320004ff7159320064fe7159320064fc715932003eef21593200bebf40593200bebd405932003eef2059320004ff765532003cfe7655320004fd765532003cfc76553202de7f65553200267c65553202debf645532001ebc645532007f3c5455320005ef725532003dee725532003dec72553202df6e52553202df6c52553202dfae42553202dfac425532003def7654b2030eef7654b2003f6f7554b20026ee6554b2003eec6554b20005ef7454b2007dee7454b2007dec7454b20
  | 10 => 0x515036e7d63551500b73f435515036f3d43551502de7c62551500b73c42551500057f71551500b73f41551500077b705515000d7e705515000d7c70551500ff7870551500267f60551500277b60551500ff3f40551500ff7a105515003cfe76d895000cfd75d895001cfe74d8950004fd74d895001cfc74d8950004ff73d8950014fe73d8950004fd73d8950014fc73d89503667f53d89500067d53d8950006bf43d8950006bd43d8950366ee52d8950366ed52d8950006ef32d8950006ec32d8950064fe71d8950004fd71d8950064fc71d8950024fd70d895021eef20d8950006ef629895005df97098950085fb705895003eee6218950006ed6218950004fe7690950004fd769095003cfc76909500073d5490950004ff7650950004fe7650950004fc7650950064fe76d85500a6f661d855000cfd75d8550064fc75d855001cfe74d8550004fd74d855001cfc74d855035e7f54d85500067d54d8550004ff73d8550014fe73d8550004fd73d8550014fc73d855035e7f53d85500067d53d8550006bf43d8550006bd43d855003cfe72d8550004fd72d85500a6f651d8550024fd70d85501c6ef20d85501c6ed20d85501c6f710d8550005bf74585500b5bc74585500a6f46158550004fe7650550004fc765055001ebe64505500073d5450550024fe76d954009e7e65d95400fcfd75d954000cff74d954001cfe74d954000cfd74d954001cfc74d95403567f54d95403567d54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d954009e7f53d95400067d53d9540356bf43d9540006bd43d954003cfe72d9540004fd72d9540064fe71d9540004fd71d9540064fc71d95400067e51d954009e7c51d9540356bf41d954001cff70d954001cfd70d95401f67f50d95401f67d50d95401f6ef20d95401f6ed20d95401f6fa10d9540024ff765954009e7c65595401edbf745954034dfb70595401f4ff75595400067f75595401ecff7459540006bf7459540004ff7359540014fe7359540004fd7359540014fc735954009e7f53595400067d53595400b6bf4359540006bd4359540004ff725954003cfc7259540004ff7159540064fe7159540064fc715954009e7f51595400b6bf41595400fcff7059540006fb70595400fefa105954000dbc7655140026bc765514000cbc765514001dbf755514001f3f75551400073f6555140026be6555140026bc655514009f3c65551400263c6555140345bf7355140345bd735514033ebf635514033ebd635514009f3f535514033f3d53551402debc625514009f3c5255140005bf715514009f3f5155140007bb705514000dbe705514000dbc70551400ffb8705514001ebf605514001fbb60551400ff3f50551400ff3d50551400ffba105514003cfe76d8940024fe75d8940004fd75d8940024f
  | 11 => 0x3ee7215864203ef42158642004ff705864200cfe705864200cfc705864203eef2058642004ff7558242024fe7558242024fc7558242056be5458242006bd5458242004ff7358242014fe7358242004fd7358242014fc73582420067f53582420067d5358242056bf4358242006bd435824203cfe725824203eee725824203cfc7258242056ef425824203eec4258242004ff7158242064fe7158242064fc715824203eef215824203efb70582420defa40582420defa3058242006f9305824203eef205824203efb205824203eeb205824203ef82058242024fe76d95420d67e65d954203cff74d954203cfd74d95423a67f54d95423a67d54d9542004ff73d9542014fe73d9542004fd73d9542014fc73d95420d67f53d95420067d53d95423a6bf43d9542006bd43d954201cfd72d95420d67f52d954239ebe42d954239ebc42d9542064fe71d9542004fd71d9542064fc71d954200cfe70d9542004fd70d954200cfc70d95420d67c6559542395ef725954238cff7459542006bf7459542004ff7359542014fe7359542004fd7359542014fc735954238ebf4359542006bd4359542394ff7259542006ef72595422debe42595422debc4259542004ff705954200cfe705954200cfc705954201cfe765494238cfd765494201cfc7654942005bf745494201dbc7454942064fe76d85420c6f661d8542024fe75d8542004fd75d8542024fc75d854203cfd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d854225ebf43d8542006bd43d854225eef72d854201cfd72d854225eef42d854225eec42d85420c6f641d85420c6f621d854200cfe70d8542004fd70d854200cfc70d85420c6f4615854200cfe76d81420befa60d8142024fe75d8142004fd75d8142024fc75d814203cfd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d814207ebf43d8142006bd43d814207eef72d814201cfd72d814207eef42d814207eec42d8142064fe71d8142004fd71d8142064fc71d81420befa40d81420befa20d81420bef8605814201cfe76d91500b6be64d915000cfd75d91500b6be54d9150386bd54d9150004ff73d9150014fe73d9150004fd73d9150014fc73d91503867f53d91500067d53d91500b6bf43d9150006bd43d915003cfe72d9150004fd72d9150064fe71d9150004fd71d9150064fc71d91503867f51d9150006be41d91500b6bc41d9150024fd70d91501eebf40d91501eeef20d91501eeed20d91501eefa10d91500b6bc645915037dfb705915000d7c765515001e7c765515000c7c76551500257f74551500273f74551500073f645515001e7e645515001e7c64551500b73c645515001e3c64551503757f73551503757d735515036e7f635
  | 12 => 0xb00100300000202e00900b01a00b01602800001100000300000002601100200101000300300000100300800800400100000f01601300000500301c00000300000700001200000500001c00000600f01100600000100000900f00001800800c01202700000100000000300000d00000800500500100400100d00400400302200600000000100500000f00100100801900100d00300000000d00100001600100000700700700100200900000300100903200301400204100100100200400000600002801400100000000a00c00200200000000b00100600300200400a00000a00000600700200100000100100100200000100100200b00903b00900200004b00000700900e00200901100100f00700200400003cfe76d89543973c54d8954105de73d8954005dd73d8954024fd74d89543c6bd74d8954004ff73d8954014fe73d8954006de73d8954014de73d8954004fd73d8954006dd73d8954004dd73d8954014fc73d8954396bf43d8954006bd43d8954396ee42d89542debc42d8954006ef32d8954006ec32d895400cfe70d8954004fd70d895400cfc70d89543a73c5498954006ef629895438f3c54589543bf3c541895403eee6218954006ed621895400cfe76d815434f3c54d81540fefa60d815401cfd75d8154024fd74d8154004ff73d8154014fe73d8154004fd73d8154014fc73d815437e7f53d81540067d53d815434ebf43d8154006bd43d815403cfe72d8154004fd72d8154064fe71d8154004fd71d8154064fc71d815437e7f51d815434ebf41d81540fefa50d81540fefa40d81540b73c54581540fef8605815403e7f755964238e7f545964238e7d5459642004ff7359642014fe7359642004fd7359642014fc73596420f67f53596420067d535964238ebf4359642006bd435964203cfe725964203cfc725964203e7e525964203e7c5259642004ff7159642064fe7159642064fc715964203eef2159642004ff705964200cfe705964200cfc705964203eef20596422ddbf7655242026bf7655242024bf765524201dbf755524201f3f7555242026be65552422df3e65552420263e65552422df3d6555242026bc65552423b5bf73552423b5bd73552422debf63552423aebd63552420f73f53552423af3d53552422ddbf7255242007af72552422dfac725524201ebe625524201fae62552422df3e52552422df3c52552420f73f51552420f73f5055242004ff7558642024fe7558642024fc755864223ebe5458642006bd5458642004ff7358642014fe7358642004fd7358642014fc73586420067f53586420067d535864223ebf4358642006bd435864203cfe725864203eee725864203cfc725864223eef425864203eec425864203ef771586420e6f641586420e6f63158642006f5315864203eef215864203ef72158642
  | 13 => 0x6a00012391720004e829c8fecd800f314b21c4c880230604000a760f691102bf0c000027391986d809b290105009b14713b10b000000100400700600000000300900000a00800000000000200900600902000200300600500303600000800500500700c00300002800200500000001200001100d00c00000500e00601100400000401200300900d00f00400400100b00200000406000500600a00e00f00300100000703100000000101600803500600400400600300100300300200100100a01000700200000600d00400b03000100e01000000000a04800901700301d00600300000800300800201e00100c00700800603200000001200000000100e00300000f00000000100200d00200101700100000706100500700804700200300e00c00000000a00103900001300600401800500000100000000000202900002900300000f00003700100103900000e00400000000101800300700700200100400d00500000600300d00800800800000000100700901703d00400a00100402e00400105e00f00900000200700c00200200400201f01300700600101301700203704f02400a00300600500000200100e00002b00101e00000000d00000001000200400700600300900800300000000100000500f01400a00a00001200300800e00000400201500000304100000200e00400300600000d00000600f00201001700200000100200400603400800400000900301900a00b01304100800000101500300000f00300100300601500601600800000500401c00100000b02601100100100200001b00001300900600400400100700000502501200100c00b00200800000900202000400901d00100000300200101300100000b04900200000d00000700500100000700800100001900f00000700000500000201900e00100000601d00302100000200100600100200e00000000100000500800500500c00700000500400000001300200a00000200200900100500004401000100000d00100d00b04500300001200000100800d00600900501302100000e00000201501200000300800500200002000600001000001900001600600400100700200600100500f01300100200300100100000000c00000301200000500a00000100002200000000700300000300400900e02000001600100000000300700100600f00100100001400a00e00000700000900900500000001200000000e00400100d00000000200000a00201000600100000000002502700600000e00100100200300200e00400800400601f00602201700900000e00000300102106a00000400400501f00200100900200701700000400500300900000000100400103401704400001c00400000000801600400100300501f02700700a00a0060060150180000010110010010060180000040070050
  | 14 => 0xc80ffcf98327a1b19dc14025916582989bc30d263038873e1c71a796a00006333ed89d45e628a09b8000d7116b31b1edc11800037da0381560000000000c4c1098249380eda6721b11b485101b106cd76414d41f1f4800000004322f1b70bde2360b80000290000413c000ee23542d29988a2c84d141154863c86f15493bc1fe25f2378dd8c520ba00414480c267511f9cf501a2f02d197108ae320a06cdac97a45b13c94783341a70cb85004f83f126d1c5ca1e29710a93c0e5465b37302d03a264510393750d65731b493647d61142179d7482406cbe993ec8f2337092c37e16c0f04081340f1e4e316c86d0fb22c03ad066c76c150a2282320d504a38c1a48cde0be29a1c58ca418d19c52ec0d37ae2c2863d04655f396d7deca871c27e0a566700004018000c2437b28ba0c88e436d285000023810c00020f07de52306e50c451c00000007a00000000d71798b3879c000062800033b2bd9c54e648310b4873024a000000025000046e0990de462200500012ac00037a000000062c78024a90706d00421c9800047c4d080010ec33e0fe8000000cd242207c8a48c270000418b900005c100016746164b81ef089c64557c265d110af45f92479efc0d1011243dbe06de17b041e0d40c70880000e706205640874000efa39203a906c3a47d600000001200ceab581b40000000001df85120003844c4c75000000000004500002b4000023942d195d78426a3813ee17242763250b085984ee44e2219eccae004f886da9c36c33a32ca01c0480ffa52173099a36613590de00000041805a04023b500000010e80ed9680b60d881aa019039c57e68329b80006ad0002cf81dc7d47053a2048d0485fe0001cc0b1d40f0160b3c9ec35610e8ad80003cd000077ce5a0e41ec8518fc02780770ca43a83462d98e28260192079c334e6a73301a03e0cc900d0b983824f64522b687910542413d4969a00061c073df049c40362a60848ccc108be0cc190cc20029581a8eca2f416b9ed0b6e03821a96f500a22a000000451a5a242983e8ef640140b1398b3c15c2430000ac014380019947ec3cf43180000002c320103763c25b925812b04306393948b6c0b043305c20280001b90000c1cb68074b4303d66581113bd11f801e0790394fd4b4c12b38c846692632da939370000000000000067e650000070464646a03a11d000012a39747e000059211680004a60fe06617b89303410510314000028a979aa4e6800036300fc1d44e11c31990e480000001ec900c7fc20a9af48fa7cf000000064c0128e000689aa3259170212000866b478f0887c28401705c80000003470000f7275714a800000069a3411fb81ef7e63501664bdd0a988597a0dfd50332e0d5ca7a6fe35e09305de8458ed99e000013436d141400023a0001574d0e14e83489fc90e53312a00005
  | 15 => 0x8c848c068800049c58d0000b8c0007a8138000000047288692c4a2609a12b1a7c38d3b40d11258b565db1cc14941b734c00016d4d106563375fec7ac071ab3978cf2048023199b817835abac07a2ccd41814e00a81650e03da5f1858c340329c26042620e125818ab5a72f4129b785bc40b3b7023800085f198c2f2d9e1413e2119ceb66a213002b47a65260e807b21b6152a25800102a0c204dcb5443c00000017d400078b2a200004525d70de86a4e1e00028f87f86408440545864b9c34200000000e700013d0000b860000000000000000009c0006280000001f2485676f3a59d4431c0043909df076667e21accc4e4420f3710000112000430800000000040a1ad0f260b0800198011e0b13c50e94d38000000000028a83a0030000bf80f506800000000873150e7400000b25f80000001c821001640d78282ec02280000640001fa0f9a0000e55dc86448401e18000b640002618b5027865f00005600003c833ea11800000007e0b102020fd23d864403581700013e08113f315d8ab4e1a14d0001bac00043c0000e200001d521286f80001633ea06f107e0c180000002000d30001d204c20000000000e9e0001d8992106e65e355990d0b079916280000006402518b94fbe6021cb999effa5753a282000004700338000a2a73e1e097c000069e0979f027c40003a907b874e5dc2071e8c16035b3b59ae03fa45a2b10fbe000000000207603c0f61f014082f86f11b4cec00900680000892000409000000030800002b9f140c92a043b855884c01806496406665ca170982cdde00018d180a32c0001f91868eb21053d11cf027a29a000163c578077bf200d6ba487b05f4000f5a0171a8198c42c065a5a0508ab41ed10d130866f38e197c000e226d13032070de802b0409044ece0781dd0de02a73010000d2c0006cd35c823eabc23d3d21010a021d739d9ab4f0a01622a9b08cec1080e6575409a14a0000d7ae8466109f19c42963d034a9f88ab25693071804000483275a1744d81ad00003480000eac2900006e616d40f59fc00074143440000001650d421a48c13212e8800049e7d68000000e084ec0000428daa5ff07400006081543ea8df40002b731e1e7c75260ea098df02977f53dbc000b265bf390469878a60920e8f9031800010c91640002dd324800108632e86380007f053a1731eee9160af0018ac40000000000246acc0000550000d5828617d1124caa0d6000206095435c1ef996a18f6e304303ba6bc8332be8624b7600017ca1503e604b1ea972054c2c83b18000bc4385128000063a09c800182e1940000370ca263640ea038000f756702a809a00000000000d2800055c264800093a0dd00c953409c7123e50000bd66a104760e0258504014000000017e05480001966160001e100000da0001e7503c1dc1759c1c5607068
  | 16 => 0x3cb9fc40dd6ee19e800000038441c8df808c1f200007381112f600001c8000000163800000028f14d800046262430f1d7c6725fa3088c86f4000020d00009fa0002bc92e47b40000000000c4e10e348800000039100014fc23c00008a8c3cf54102083caf810d0000001e7865e0000f382904e42c223b974c00008da7f01c400000000010020008700bb80000005563020c1a0004d22028000e0025e3d749a8e723d239c165c88477908c10a80286281df0d20aae3ca08985d800011028c2000a6a2352d8976834646903e048e0007233850a447d03580bca1c8e1607e2e788943d887625f21b0fa443827703f644c5c730006507fc1b03ae06849121f73460b241505f3078c578da80d51a3951c3882ed0b7079848a4a8036cac80884322429444be81e33f39d8081a6203930c24fbc60a0890b7085068a28c82830bc1ff3531fc8ec817120307a495a52d0ec81fc0000003350f5046e7b837e049c5ac7680e11a2c08f31700f888cade0000ae83bc0036c102d0cc2a1c473000177c26c1830dbc78823700014f00000006741ee20ba0bc49200000006180000001ee827d8090090000f600a39968e5844000012e00010f253100007d2d023b2368000000055100000000003e33e895c47041b229c1e309da3db0fa13e40007763421b14fae0003f80158cdf4a93ca1eda0007bd3de07da30a32707089685463f4000000108447f40910d04125a43e800000004d100014c05660000624488a5247c2de014c8c05569cc9b741a324d01807e837e34d26a0364e506af3aa9fbc8f14cf19700000000bf4239b805000e980012b800010580003be000000369882c16a7373f180000005432c403422cb343b278eb48ca657b17a0be08b7610930e6c00080b3740f181a77532cc08350410000061f2c00084a2e300004947090000b28fd60002598e8491052800007344e600007b94c800000001bc00096a86eb1d15d0d947ab36f9ae90363150c38000bc082c1c5dc080e03353ed00003100c81d20fe49880000c10af408a7ac0d6c000d1d6940c0800000000024e053c12463530e9f0019f2ac05289c47763cc17a8332c6845f2b612f0272524436d2841a863126b8a2c84884b37c98c03d60dc17c18dcdea82210810207162e000d8db30f15862360c2025211b1429ebe0b85ed31c1f0ce262744279624f024903618e9853e66724da0980787b5b3584e06dc23b3aa06dca8068003846cc0000002b900001226b20201b64232000263a1f0274027c109e68af084e41000006920de35b8432aaa3329c809548801e53c30ee46ea36431292782a682d177158cdac7952f8965061c03b3a00fae502050bf51064a000e33a3800077a8651c49150aa800013e960882e157000052a0006ed3f49e1ccef60d0f5000000022b059cbf0dfe45300001be9286963901104
  | 17 => 0xc4180c88ac9ad8cb02a23e713d01ae62114986705a629441d8e5000053c40fd1440000002369fb400000000000000001a000020f85d009e0000d940a40000571d880000002ea08203e0804000188cde623791c9ece47817d012821666400023d0000d4a10bbd28f106603053a7d28099028c002c2923702ba12208cc64d0004088174d6221421b8d800003af0aa83aecd919d000196800000026996389083e50001120fb008d11201e24cc0d78001d245d454b0fc8d684364c0240800092e423152150800051d000000091a1780001170c2e3951d516b8f420000000918f62051000194c0000002db12940eb2640000e88a920000010490d9800013709950da5be1f820ac4ba000436400000000015a1e089940001ae88c000000031da07cb843e704ec038b744bf8000fca6144df9e399b0f906b023b180c5720d6a96016c9323342799888e746aa1b0946cbec0151020c7c7346e72ac01f44da32a8cc000050600004b1e4498a0001fb80d41d186bc24819a8001d9b07851022746b1ac96b024d68595c1740e185912d09dd43de6c8374a0d838c0390b78948197336abf0040e6f6fa1a221581f61cf18c800027e3cb078865439424807a5c7c9c73fd3251ba88491090989da90aa4f740d090c22e33c0d28924bac0fc8ea419ed3215f26f816abe40992a78474d205af4281de017a18b08d0bfc47002d99f027adb64e90971d0c7a241642c8f0043808a9ba028c1045482308d9cb0e57f0cc95d8e366c90c316a817b69b2a980010c42e9a8403c82060ec342960cf7608b1dc0c7e1643bf2c50310e20053a61ce34038000000127c3a616440e80009d412d043cb345540652e5800000068d04a8000542193175c80c5fa679000034a0000ed03cc00045e7082148ca0d2615139b18f90a27f43c70a9c10554a00008288423870000d54e8c00030600dcc3e7f6000025ce347c2b7800005e475034c197437616c0000000b8015002aa008bd21a406301dabba2992579ab85d86571b2591c1e81d61f3072414208534e8000000000348c00000080f43992980007883bf8000b5944c2c21f8446464614ea1d4dca68900020305e26140728b8819c4d6132ca609963002a096e00004103bb8ff00c611604e8e306ee37037907f085c000000008422b211000136c2054580679118cf61490001caca200002388aa045800030c00000000003f615186e400004a4fe82d44e50554c92ecc2fe13785806d4000083913401200006f424f0f00002018000442031000000019b78341e9630a9c3b73c91f1cc0a11f1ee9b2ca1a0502f50b686041f1196417cc366a8336992c9b04b20d79db00406e10a70f24c512a542606001be0e629f0b4808e34e25d21e8bf63bd87959306cf04cb4b95b8c7e0eb0000e00e284c5ad3d4a80000c022399e842e3ae00e800081f000
  | 18 => 0x18c02700006bb3da9f0800047837b9fe896c0c306ad15865300016f8d7c9146c704fc000dfa0001a980002fe60808798b838a0003ff93fc00006c00013e8000251393830400009f3398fb47dc26740080cc00014c1d01fcc35650727a8f382b40a72411bd804463d437146883c7313af16000e604f38097341e133632893050825e72d49d2807f0000bd1b600cc79b3599c74b5b00004989f90100008000ead0b638312c050d0ef40bbd3087c9340290115f746677fe0820c8eb2c857000169c00000001f1d3089e44a0001d580007be2848000000798000035204c0000000988a385f835a8a4000070e21e8b4499856a11a21a0dae78d25b800059c6bf00019080008640001eca0006be1fec2b00004b0c33d05e0743d8290880855c2f72ca9794a44641246cd8c4b685c3db000094e0004229e9c14b3d70909cb800e83442401310b44f2409876822940a053d1403ba73f000098ce3c000000000000039e0b380002155a00ec0588d4806b0024fb000037106c51d487268f99592388d01b52f20c906fe19e31340010ce7e51a89584e9c1330485668166303435142ce582af00011890321ba000041802650c41707d8f5e02d206030a40a1282ad98c868a6e4000166c6864a22831a8c2ea70300010ba0f400032680000004e404957dc0000da800000007a49103d80000002c12d80eb0bd802f2e655dc0de82905fddc06a47060e58104c58769189000010808ba671bb03ea15b0000150aca106b92800000058b00000000000001d19dd0000000090000071e0600f00becff200019a47ecff01c300000000001ac07480002e80000ef00000002ab05b81d8f1226921800009e262d0000000c563bc303818884300021f90e8a280000000ca800000a1f09dcd04e61018e0ce648082f32702e4a6c45d3a6909c5ce6152ef00004847f72e2800040c0272a28ba459852e0a90d4a35961336719a050e0388000360b0279633e02ecbfa000000095
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaad8490d62440135cd0321ac488002b9606435891014d7540486b122000ae98090d62440011df0ea1ac4880023b21d435891000657c3a86b122000aae8750d62440015590ea1ac4880032b21d43589100045643a86b122000e2f7550d6244001c58eaa1ac488003a3e0d435891000747b9a86b122000e8c7350d6244001c5ea6a1ac488003a394d435891000716a9a86b122000e8d5350d6244001c1aa6a1ac4882032bdc543589103ff4798a86b12207fea63150d62440ffd1a62a1ac4881fb2bdc143589103f74798286b12207eeaa3050d62440fdd1a60a1ac4880029ba14435891000536c2886b12207daae8410d62440135cd0221ac488002b9604435891014d7540086b122000ae98010d62440539d50fb82c4880039add77058910007343aee0b122000eab74dc16244001d50e9b82c488002ba60f705891000765b9ee0b122000ec873dc16244001cd6a7b82c4880039a54f705891000755a1ee0b122000ea943dc1624405f9d6e3b82c488003b8dc7705891017f7118ee0b122000aea874c162440015d10e982c4880039add53058910007343aa60b122000eab744c16244001d50e8982c4880a6bae0d305891014f65c1a60b122000ecb734c16244001d90e6982c4880039ad4d30589100076529a60b122000e69534c16244001d92a6982c4880039254d305891000755a1a60b122000eca434c16244001d5286982c488003b250d305891000744a1a60b122027ceb714c16244001dc6e2982c4881f3b2cc530589103e77118a60b12207cec9314c16244001dc262982c488003b04c5305891000477c3ac431220078ee829da42440531db04bb4848800eab211629091000476c14eca12200087f855d942440090f90abb284880022fe1176509100046fc1aeca1220028dc835d9424400f1dd043b2848800e3b21d6250910064f840ee8a822000db241dd1504401b9d0ed312a0880a6f8606625411006ef038cc4a822009ce8765895044001cd0cab12a08809ef8e05625411004ef038ac4a82200c9f287dc550440013e10ea0aa088003cc5514154110064f840eeaa022000d7251dd540440191f10cbaa80880327c205755011006e743b4c4a022029be181989404401bbc0e331280880273a1d9625011000754322c4a022027be3815894044013bc0e2b1280880327ca1f7150110004f843aa2a022000f315454540440037610ea0a80880336c21d415011000cd843a82a022001bb28650540440037610ca0a808800fac219415011001f59bb282a02200cdb2765054044019b60eca0a808800fac1d94150110005d9c2a82a022000bb1855054044001b66eaa0a80880036c5d541501103ddd9c1a82a02207bbb18350540440f5b66e6a0a80881eb6c5cd41501103cf99a9a82a022079f31535054044001f44c4a0a8088003e85894150110
  | 1 => 0x500192c488002ba600325891000c7d43ee0b1220028f8874c16244001cb2a6982c488003a650d30589100076898a60b12208cee010dd9624400195eedba2c488003e8043745891000657bb0e8b122000fa0101d162440011dd0fb22c4880029be1564589100053642ac8b1220008ee8719162440014dd0a322c4880029b614645891000567418c8b122000acd83191624400199eedb9ac488003f0043735891000667bb0e6b122000d8c741cd6244001f802039ac4880023ba1f635891045f70086c6b122000aae8498d624400155b0931ac48822aba602635891044f70082c6b1220008ee8718d624400155d0831ac488002ab610635891044657bb686b122084da771d0d624410fb56e1a1ac48820be80434358910004d643a86b122086caf7650d6244001d1cc6a1ac488003a358d435891000786a9a86b122080da77150d624410bb56e0a1ac4881fbe80414358910006b5baee0b122000d6875dc16244001b56e9b82c4880036a1d37058910006e5b9ee0b122000dc873dc162440537c503b82c48800378dc7705891004d7443260b122000ecb634c16244001e92a6982c488003e250d305891004df040a60b122027de3714c16244001f8262982c4880038bdd7745891000556c1ee8b122000caf71dd16244001d4c63ba2c4880032bdc3745891000755186e8b122000a6e859d162440014db0b3a2c488002aba1274589100056741ce8b122000acd839d162440015cb033a2c488002ba602745891000537c2ae8b122000a6c855d1624400159f06ba2c488002b320d745891000573c0ae8b122000aeb805d1624400155d0e3a2c4880032ba1c745891000717ba8e8b122000e2c751d1624400155b063a2c4880032bdc4745891000753188e8b122000caf701d16244001d54603a2c4880038bd52545891000716aa0a8b122000ace83151624400159b062a2c4880a6baa00545891000574c00a8b122000e8f84dcd6244001d1909b9ac488003a3dd37358910007463a6e6b122000ecb80dcd6244001d9101b9ac48800333dc3735891000557424e6b122000aad849cd6244001958e939ac488002b3a0e735891000574c04e6b122000aaf845cd624400155908b9ac488002bae01735891000557420e6b122000aad841cd6244001958e839ac488003335cc735891000567438e6b122000cce871cd6244001d1d0839ac488003a3610735891000747ba0e6b122000cce741cd6244001998e839ac488003a31d07358910006463a0e6b122000eca801cd6244001d930039ac48800333dc073589100055743e86b122000aac87d0d6244001c5eeba1ac4880038b1d7435891000747b9e86b122000e8c73d0d6244001c5ea7a1ac4882132bdc7435891041f5318e86b122082caf70d0d6244105d5461a1ac4880029ba16435891000536c2c86b122081
  | 2 => 0x176551100061e2a0ecaa220028de831d954440011bb063b2a88801e3ba08765511000476c10ecaa220048bc8759154440094790ab22a88800b279cd43d89100064eb9a87b122000e1d5350f6244001cb2a6986c488003a650d30d89100076898a61b122000a6f8559262440014d90ab24c4880029ba14649891000536c28c93122000ace83192624400159b06324c48824f3a5c3639891000557424c73122000aad8498e62440f99d2e0b1cc488002aba10639891000556c20c73122082da571d0e6244107b52e1a1cc488213e804343989100074731a873122000e8d6350e6244001e1aa6a1cc4881fb695c543989103fed4b82873122080fa01050e624404f7c102b84c488003785c5709891006d74432613122029ce9764c26244001e92a6984c488003e250d309891006df040a613122029de1714c26244001f8262984c4880038bd52549891000716aa0a93122000ace83152624400159b062a4c4880038bd4f439891041656b8e873122088ea571d0e624410995ae1a1cc488223aa5c343989100053742c873122000a6d8590e62440011df0ea1cc48801e3b21d439891000657c3a873122086cac8750e6244001d1f06a1cc48821ba3dcd43989104374639a873122000e2f5350e6244001d1ca6a1cc4880038b54d439891000746a9a873122000e0d5350e62440fd95ae2a1cc48821ba95c5439891042f4798a873122085e8d3150e624410195ae0a1cc48821baa5c1439891040747982873122080e8d3050e62440014dd0a21cc4880029b6144398910006d8086e8b122000dd010dcd624400717d0fba2c4880030fdd774589100045ec1ee8b122000cad82dd1624400195e43ba2c4880032b487745891000657906e8b122000cad20dd1624400187eea3a2c4880030f1d474589100146f43ee6b122000c9f74dcd6244001938e9b9ac48800327e1373589100064e426e6b122000ccd82dcd624400199e41b9ac4880033348373589100045fc22e6b1220038bc845cd62440011bd0e39ac48800327dd073589100064e3a0e6b1220008be87d0d62440071790fa1ac4880030fdd743589104961e3ae86b122000c9f73d0d6244005938e7a1ac4880022fa1d43589100045e43a86b122000c3f7550d6244123878eaa1ac48800327dcd43589100164e39a86b122000e1d5350d62440014dd0ba12c4880029b61742589100056741e84b122000acd83d096244121998e7a12c488002b9607425891000574c0684b122000caf74109624411f998e6212c4880023ba1f32589100055742664b122000aad84cc9624411d958e9992c4880a6baa03325891000574c0664b122002ccc738c96244001d1a87192c48800a3b21d32589100166639a64b122000aae840c9624400155b08192c4882372b1d0325891000667b9864b122000e8d430c962440535d
  | 3 => 0x6b0a4000d2f7550d6148133a58eaa1ac29000363dcd4358520046c639a86b0a4000e8f6350d6148001d18c6a1ac290003c354d4358520044f243a62b0a4000f45534c56148001f0a8698ac2900035add77058520006b43aee0b0a4000dab74dc16148001b50e9b82c29000372dcf7058520006e439ee0b0a40019ea86dc161480033d10db82c2900027a60f7058520006b5a9ee0b0a4000d6953dc16148001b5687b82c2900036a50f7058520006f1b0ee0b0a4029ce961dc1614805fbc0c3b82c2900bf788c77058520006f098ee0b0a40009ea874c161480113d10e982c2900035add530585204c6b43aa60b0a4000dab744c1614812fb50e8982c29000372dcd3058520046e439a60b0a4000ecb634c16148001d90c6982c290003d254d3058520007c4a1a60b0a4000fc1314c161480013d301bb2a2900026be117654520054d6422eca8a40009cf835d9514801139906bb2a2900027ae01765452004cb643aa8a8a400ad2c7455151480013d301bb282900025be15765052005cb642aeca0a40009cf835d9414801139906bb282900027ae017650520004f5c02eaa0a40019e8805d541480133590eaa2829002f4b1d5545052021cf5c3acbb02403f9eb875936048063e50a8aa6c0900a27ae1d61d8120005b5c2ac3b024032b6885587604800175708b0ec0900c6ea21161d8120005e5c1ac3b024030bc883587604812ddc0c2b0ec0900a67960672d911004cf4c04e5b222000de0109cb644404f3cf02b96c8880367ae0172d9110006f0082e5b222000c3d75d53644400156b03aa6c888002ae60354d911003c77416e7b2220008ed82dcf644412b8dce5a9ec88800b179cd53d91100062eb9aa7b222094c6e7254f644400517f0ea1ec88800b279cd43d91100064eb9a87b222000e1d5350f644400155904a1ec88821b2b9c943d91100043fc2ae5b22200487c855cb64440011bf06b96c88800a3720d72d911003c77c3ae5b222000c6f855cb64440018d90ab96c8880032b21172d911000667c1ae5b222000ccc835cb64440018dea6b96c8880031b54d72d911000657a1ae5b222000cad435cb644404f1df02b96c8880a63b60572d911006c77c02e5b2220098ed805cb6444001ae021baac8880121fa1f75591100043ec1eeab222000c3f43dd564440018de43baac8880031b487755911000637906eab222000c6d20dd564440014bb063aac8880030f1d774591100145e426e6b22200087f855cd64440090f90ab9ac8880023be09735911003c76412e6b22200087e87d4d64440090f90fa9ac8880021fa1d53591100043e43aa6b222002c5e7354d64440018bae6a9ac88800a2f21d43591100061fbaa86b222091c3c7550d644400193ee6a1ac8880038754d43591100061e2a4ecaa220078ee829d954440011db053b2a8880022fe1
  | 4 => 0x1480014dd0b21ec2900029b61643d852000726a9c87b0a4027aea8090f61480015d30121ec2900023be1d43d85200047643a87b0a4000e4d5350f614800195f0ea1ec2900032b21d43d852000747c1a87b0a4000e8f7350f6148001d18e6a1ec2900038bd4d43d85200074729a87b0a4000e2d5350f6148001d1aa6a1ec2900038354d43d85203ff4798a87b0a407fe8d3150f6148101d1e60a1ec290203aa8c143d85204074698287b0a4080ea71050f61480014dd0a21ec2900029b61443d852013d7540087b0a4000ae98010f614804f5d706986c29009fb2e0d30d852000765b9a61b0a4000ec8734c36148001cd6a6986c290003b294d30d852000734a9a61b0a4000ec9534c36148001c92a6986c290003aad0d30d85200076521a61b0a4000ea9434c36148001d9286986c290003a250d30d85203e76598a61b0a407cec9314c361480172dd0fbaac2900031b61b7558520004b6c1eeab0a4000d6a30dd561480178d8ebb2ac290002aba12655852000556c24cab0a4000ace83995614800159b0732ac290003331ce655852004c7643acab0a4000c6f751956148001998e632ac29002a6ba1f745852000697baee8b0a4000d2c75dd1614800195b0dba2c2900026b60f7458520006d5186e8b0a4000d2f751d16148001a58ea3a2c29002b2b1d364585200053742cc8b0a4000a6d85991614800159d07322c290002b360e64585200066639cc8b0a40098ec87591614800195ee8322c290003331cc645852000cf4406e6b0a40089ce87dcd6148001a9eebb9ac290003531d77358520006c7ba6e6b0a4000d8c74dcd614800199b0db9ac29000353e177358520006a642ee6b0a4000d8f84dcd6148001b1909b9ac29000372e037358520006e4406e6b0a400096f855cd61480172d90ab9ac2900026be117358520054d6422e6b0a40009eb805cd6148001a9eea39ac290003531d47358520006c7ba0e6b0a4000d8c741cd6148011998e7b1ac290003b18c7635852004c7743cc6b0a4000a6e8598d61480014db0b31ac2900031b1d6635852000557424c6b0a4000aad8498d6148001958e931ac290026b9a06635852004c7643ac6b0a4008ccc7358d61480014dd0a31ac2900029b6146358520006363a8c6b0a4000aae8418d614800155b0831ac2900032b1d0635852000667b98c6b0a4009ae68118d6148001d8c6231ac2900025ba1f535852005cb643ea6b0a4000d2f74d4d6148139a58e9a9ac29000353dcf5358520046a639ea6b0a400096e8754d61480012d90ea9ac2900034bdd153585204de963a2a6b0a4000d4f7354d6148011a98e6a9ac29000393d8d53585200072631aa6b0a40009ae87d0d61480153590fa1ac2900034bdd743585204d6963ae86b0a4000d8f73d0d6148011b18e7a1ac2900026ba1d4358520004d643a8
  | 5 => 0x23721cd30d9120007a4a9a61b224000f89434c3644814135909b9ac8900023be197359120004f5c02e6b224000d4f7354d6448011a98e6a9ac8900226b21d4359120006c7b9a86b224008d8c7350d6448001e1aa6a1ac8900036ad93705912018ed4326e0b2240009e983dc16448001ad6a7b82c8900035a54f705912018ed5a1ee0b224000da943dc164480013d50e982c8900227a21d3059120006e5b9a60b224008dc8734c16448001e92a6982c890003e250d3059120044e741eecaa240009cd83dd954480013d301bb2a8900027ae017655120054b743ecaaa2400ab2e84d95544801735d0fb22a89002ecba17645512004c76c3ecbb0a4000aae84997614800155b0932ec290002b3a0e65d852000566c1ccbb0a4000ae98099761480131db0e32ec2900263b61f64d85200053742cc9b0a4000a6d85993614800159d07326c290002b360e64d852000574c04c9b0a40098ed8719361480131db0fb1ec2900029ba1663d852000536c2cc7b0a4000aae8498f614800155b0931ec290002ba60263d852004c76c38c7b0a4000a6e8518f61480014db0a31ec290002aba1063d852000556c20c7b0a4000ccd7318f6148001a9ee6a9ec290023531cd53d852000727b1aa7b0a4000e4c6354f6148001b1ee6a1ec290023631cd43d852000747b1a87b0a4000e8c6350f6148001e1aa6a1ec290002ba21930d8520006e5b9a61b0a4008dc8734c36148001d96c6986c290003b218d30d8520007a4a9a61b0a4000f89434c361480015cb03baec290002aba1275d852000556c24ebb0a4000ace839d7614800159b073aec29009ebaa0275d852000574c04ebb0a4000ae5811d761480015cb03ba6c2900029ba1674d852000536c2ce9b0a4000ace839d3614800159b073a6c29009ebaa0274d852000574c04e9b0a4000ae5811d36148001c5ea92a6c2900038b55054d852000567418a9b0a4000acd83153614804f5d5002a6c290002ba60054d852000572c0ee7b0a4000a6e859cf61480014db0b39ec290002aba1273d852000556c24e7b0a4027aea809cf61480015d30139ec2900029ba1473d852000536c28e7b0a4000aae841cf614800155b0839ec290003335cc73d852000572c08e7b0a4027aea801cf61480015d30039ec29027f9a8c353d85204ff33886a7b0a4000aae8494f614800155b0929ec29009ebaa0253d852000574c04a7b0a40008ef8754f61480011d90ea9ec2900031be1d53d85200063643aa7b0a4000e4f8354f6148001c9ee6a9ec290003931cd53d85204f72798aa7b0a409ee4d3154f614813bc9e60a9ec2902779a8c153d85204ef26982a7b0a409de671054f614800155d0829ec290002ab61053d852013d75400a7b0a4000ae98014f6148001c5ea7a1ec2900038b54f43d85204275518687b0a4084ea710d0f6
  | 6 => 0x3c77416e7b2240018ed82dcf64481438dae5a9ec89000317dcd53d91200162e39aa7b2240a6c6d7254f644800517f0ea1ec890003275cd43d91200070ea9a87b2240a3cad7250f64480011df04b9ac89000317dcd53591200162e39aa6b2240028bc8750d644800193ee6a1ac89000b271cd43591200070ea9a86b22400c8ec82dc564480051bd07bb2a8900023760f765512001c3f43ecaaa24003a3e84d95544800917d0fb22a8900128fa17645512000c77436e4aa240089ce83dc9544800139b07b92a89002a5be1d5494920056973a2a9292400b9af875524248017a5ceaaa484900063b219755092006476412ebb0a400c8ec825d361480031db05b9ec2900323b20973d852050e36b96a7b0a40a7c6c72d4f61480018bee6a9ec29000b171cd53d852053636b92a7b0a40a5c6c7254f614814195ae5a1ec2902932b1cb43d85200064fb9a87b0a4002c9c7350f6148001c3aa6a1ec29028f2b5c943d85205165639287b0a4000aae84d4b614800155b09a96c290002b3a0f52d852000566c1ea5b0a40098ed8794b61480015cb03296c29009e3b21d52d852004c76c38a5b0a4000ae58114b61480014dd0ba16c2900029b61742d85200056741e85b0a4000acd83d0b61480131db0f216c290002b960642d852013c7643a85b0a40098ed8710b61480015cb02216c29009e3ba1f32d85200053742e65b0a4000a6d85ccb614800155d09996c290002ab61332d852013d7540665b0a40098ed878cb6148001c9aa7196c290003a350e32d852000572c0c65b0a40278ec874cb61480131db0e196c2900029ba1432d852000536c2865b0a4000aae840cb614800155b08196c2900039354c32d852000746a1865b0a4000ae5810cb614804f5d500196c2900039654d30d85200074ca1a61b0a4001ce9724c361480031dd0db92a2900063ba1b725052026476432eb90a400b8ed87d9721480971d90cba6429002a3b61f64c852023e56326e890a40018ec865d12148015958e9b2242900323b21d644852000477436e7b2a400896f8754f6548001a9ae6a9eca9000363dcd43d9520046c639a87b2a4000f0d5350f6548001b96e6986ca90023721cd30d9520007a4a9a61b2a4000f89434c365481432d90bb9aca900023be197359520004f5c02e6b2a400896c8754d6548001a9ee6a9aca90023531cd5359520006c7b9a86b2a4008d8c7350d6548001e1aa6a1aca900035ad977059520196b432ee0b2a40009e983dc16548065ad6a7b82ca900035a54f7059520006d5a1ee0b2a4000da943dc165480013d50e982ca900227a21d3059520006e5b9a60b2a4008dc8734c16548001e92a6982ca90003e250d305952000477436e7b224000d4f7354f6448011a98e6a9ec8900226be1d43d9120006c6b9a87b224000f0d5350f6448001b96e6986c89
  | 7 => 0x8f7350d61c801db18e6a1ac39021ba3d8d43587204374631a86b0e4000f0d5350d61c800f3c90e98ac390003d154d3158720007c2a1a62b0e4000aae849d561c800155b093aac390002b3a0e755872000566c1ceab0e4000ae5819d561c80015cf02baac3900a6baa00755872000574c00eab0e4000a6e859d161c80014db0b3a2c390002b3a0e745872000566c1ce8b0e4000ae5819d161c80015cf02ba2c3900a6baa00745872000574c00e8b0e4000e2f5495161c80015cf02aa2c390036b9205545872000716aa0a8b0e4000ace8315161c800159b062a2c390036b9a04545872000572c08a8b0e4000a6e859cd61c80014db0b39ac390002aba12735872000556c24e6b0e4000ae5819cd61c80015cf02b9ac3900029ba14735872000536c28e6b0e4000aae841cd61c800155b0839ac390003335cc735872014d75400e6b0e4000ae9801cd61c8159ccc63a9ac3902af99c43535872000557424a6b0e4000aad8494d61c801b5cd0329ac390002b9606535872000477c3aa6b0e40008ec8754d61c80018df0ea9ac3900031b21d535872000727c1aa6b0e4000e4f7354d61c8001c98e6a9ac3902ab93cc553587205573318aa6b0e40aae4d3154d61c8153c9e60a9ac3902a7934c1535872054f33882a6b0e4000aae8414d61c800155b0829ac390036b9a04535872000572c08a6b0e4000e2f53d0d61c8001c5aa7a1ac39021fa98c743587204175388686b0e4000a6e8590d61c80014db0b21ac3900039354e435872006d7340c86b0e4000ae58190d61c80011df0ea1ac3900023b21d435872000726a9a86b0e4000caf8750d61c80019590ea1ac390003a3e0d435872000747b9a86b0e4000e8c7350d61c8001c5ea6a1ac390003a394d435872000716a9a86b0e4000e8d5350d61c8001c1aa6a1ac390217a3cc5435872042f5318a86b0e4085e8d3150d61c80fdd1e60a1ac3901fba34c143587203f75388286b0e4000a6e8510d61c80014db0a21ac390036b9a04435872000572c0886b0e4007ae6874c561c800f5c90e98ac390036b9e0d315872006f63c1a62b0e4000ec7734c561c8001d88e698ac39000399d4d31587200076329a62b0e4000e65534c561c8001d8aa698ac3900039154d315872000753a1a62b0e4000ec6434c561c8001d4a8698ac390003b150d315872000742a1a62b0e40a8ae7804c561c8113d8e6098ac390227b14c1315872006cb643aa8a8e400fd2c7455151c801b3590eaa283900434b1d5545072000c76c16e7b2a400287f8754f65480018bae6a9eca9029b1b5c953d952050656b9687b2a4000c9f7350f6548005938e6a1eca900038754d43d952051e56b9287b2a40008ef825cd65480050f90ea9aca9000317dcd53595200162e39aa6b2a4000c9f7350d6548005938e6a1aca900038754d43595200
  | 8 => 0xe6a1ec2a00038754d43d85400146f418eca8a80008dd831d95150001878ecaa2a2a00062f21975505400645e43acaa0a80018ec825cd65c800f0f90ea9acb9000317dcd53597200162e39aa6b2e40a6c6c7254d65c8141958e5a1acb9000327dcd43597200164e39a86b2e4000e1d5350d65c8147958e4a1acb9001e3b20b715972048477c12e6b2640018ec825cd64c81438d8e5a9ac99000317dcd53593200162e39aa6b2640a6c6c7254d64c800f1790ea1ac99000327dcd43593200164e39a86b264000e1d5350d64c8147958e4a1ac99001e3b20b715932001c3ec2eecaa640048bd84dd954c80051bd07bb2a9900023760f765532000c77416ecaa640018ec825d954c80b72db0bb92a99016e6b6137255320074e741ee4aa640009cd83dc954c80191db05baac3900323b60b745872006476c16e6b0e40018ec825cd61c81438d8e5a9ac39025799c8753587200062fb9aa6b0e4002c5c7354d61c814b8dae4a9ac39029b1b1c953587204a727192a6b0e4094e4c3254d61c8129cce42a9ac3902832b1cb43587204475390e86b0e4000c9f7350d61c8005938e6a1ac3900038754d435872051656b9286b0e40a3cac7250d61c810dd1c64a1ac39021ba30c943587204375390a86b0e400d8ee87d4961c800155d09a92c390002ab61352587200056741ea4b0e4000acd83d4961c80015cb03a92c3900363b21d525872000573c0aa4b0e400d8ee87d0961c80014dd0ba12c3900029b61742587200056741e84b0e4000acd83d0961c80015cb03a12c3900363b21d425872000573c0a84b0e400d8ee87cc961c80014dd0b992c3900029b61732587200055742664b0e4000aad84cc961c801b5cd03992c390002b9607325872006c7643a64b0e4000ae7814c961c800f1e90e98ac3900039554d31587200074aa1a62b0e4007ae6824c561c80199cae498ac3900063ba0b765472000c76412eca8e40018ee82dd941c80031d904bb283900023be19735972003cb643aa6b2e4000d4f7354d65c801da98e6a9acb9000363dcd4359720076c639a86b2e4000f0d5350d65c80011df0cb9ac99000353dcd5359320076a639aa6b2640079ac8750d64c8001b1ee6a1ac99003b631cd435932000786a9a86b26405b96d85dd954c80b735b09bb2a99003a73a0f7655320004e6c1eecaa6400d8ee8799561c800155d0932ac390002ab61265587200056741ccab0e4000acd8399561c801b1d90eb2ac3900363ba1e64587200053742cc8b0e4000a6d8599161c800159d07322c390002b360e645872006c7643ac8b0e400d8ee8798d61c80014dd0b31ac3900029b616635872000557424c6b0e4000aad8498d61c801b5cd0331ac3900363b21d63587200766639ac6b0e4000d4f7354d61c801da98e6a9ac39025393d8d53587204a72631aa6b0e4000d
  | 9 => 0x43d89540070ea9a87b12a85baac8250f625500155b08196c4aa003335cc32d895400746a1865b12a800ae9800cb62550011df0eb10c4aa0023be0973d815403c76412e7b02a800c5f7354f605500193ee6a1ec0aa0038754d43d815403c76412e6b2c840787c8754d65908018bee6a9acb2100b171cd53596420064eb9a86b2c8400e1d5350d659080987ceaaa2c32116fa9c85545864203c77416e6b0c8495e6721d4d61908018bee6a9ac32100b171cd53586424a73390aa6b0c8400c9d7350d6190801c3aa6a1ac32121ba9c85435864203c7a43a62b0c8400e55534c56190801d2a8698ac3210130f9d554582422df55902a8b0484078ee82dcd609092bcd641a9ac12100317dcd53582420162e39aa6b048494e6b2054d609080193ae6a1ac1210038754d43582424375590286b0484018ed82dc5609080f1f10e982c1210039654d30582420074ca1a60b0484038ed82dcf65508050ff0ea9ecaa1003175cd53d95420064fb9a87b2a8402c9c7350f6550801c3aa6a1ecaa10023be0973595420145e43a86b2a8400c9f7350d6550805938e6a1acaa10038754d43595420061fb2ee8a92848e8ef825cf61508018bee6a9ec2a100b171cd53d85420064fb9a87b0a8402c9c7350f6150801c3aa6a1ec2a123a3be0973d81420062fb9aa7b028402c5c7354f605080193ee6a1ec0a100b271cd43d81420070ea9a87b0284018ec825c7605080f1dd05b9ec8a80023b60b73d91500062fb9aa7b22a0028bf8750f645400593ce6a1ec8a8003275cd43d91500070ea9a87b22a000a3d85907645400747d0db22a8a800b179cd53d89500062eb9aa7b12a002c9e7350f625400193ae6a1ec4a80038754d43d895000536c2865b12a000e4d530cb6254001d1a86196c4a8002b960432d895000574c0065b12a0008ef87588625400187cecaa484a800f0f1d154d855000477c12e7b0aa0078ec825cf61540018bee6a9ec2a800b279cd43d85500064eb9a87b0aa000e1d5350f61540051bd063b282a80023760c76505500061e3b2a8a0aa0078ee82dcf65500011db05b9ecaa000a1fe1d53d95400162f39aa7b2a8000c5d7354f655000193ee6a1ecaa00038754d43d954001c5e422e5b2a8000a3d84947655015b87eebba2caa00023be09735954003c76412e6b2a80008f7815cd65500191e902b9acaa000a1f21d53595400062fb9aa6b2a80028bc8750d655000193ee6a1acaa00038754d43595400251f436caaa28002c5e7354f62500018bae6a9ec4a000b279cd43d89400064eb9a87b128000e1d5350f625000155b08196c4a00039354c32d894000746a1865b128000ae5810cb62500015d300196c4a00023be1d62189400061f3b2a92928004c3c7555361500011df04b9ec2a001e3b20973d85400162f39aa7b0a8000c5d7354f615000193e
  | 10 => 0x629e00054e63600018e00000040311c06c2380000000000001da000000000000000a0e8e400000000027c6a162e79763c0000960000000002404440000000000000000002290000006ce00030700000055278800063a8ce1f0ae79aa00500300500000000400100000000200000000000400100000000100000000000000000100900000300100100d00100000000000000000000000000100400000000000000000300100400000100200200000000000000200000a00200100000000100000000000400100100200000000100000300600000000600900000000000300000000000200300400600000000000000000000500100100100100000100700100000900600200000000400100000500000400000000500000400100100000000100200000000800600500400200100b00000200200200000200300000000000000000b00000100000100000000000300000000000000900700100400100700500100000000000300300000200900100200000000100000900200000000100000600600000000400100400100000300000000600000800300100100000100000000500000100200000500001100000000000100000000100000000100300100200100000300100200200000000000000000000200000000000300100400100000100001200000100100200b00000000100100000200100e00900800000000300500000400200100000000000100300100100200000100400200400000100100200200000100300300600100100100200000200000000000000000200100100300000200100000000100000000100200000000000000100600100000200000000000400900300000100000100300000000100000000300000300000700000000000000000200500000100000200000000400000100100000000100000400000000000000000c00000200200000000100000200400000100000100000000100300400000000000000100000100100400100100100100100300000000000600400000000200200200100100600300000000000100200700800400100d00800f00100000000200700000000100000000100500300100000100301000000200000000100200000000200500000300300000000000000100000000000a00000000000300000000100100300100000000700100000000700100300000000200300100000600700000600300000100000100400100300100d00100100200200000d00100000000a0030000000060000010000010068e2a2e7b12a8048bd84dcf62550011bb0f39ec4aa003275d273d89540064fa1ae7b12a8028df875cf625500193ae8b9ec4aa00327a1173d89540064ec22e7b12a800ccf825cf625500193c84b9ec4aa0032710973d895448c5ec3a87b12a803c3d7550f625500593ce6a1ec4aa003275cd
  | 11 => 0x9ae9660000000002df0000006960003661aa0000000000009c60000001510d600096f0004a69b43350c78569342a484e9b700064400000041c0ba0002b352a00000000000008c0000000000000000170005485a60000006aa2027400006620000000000003f42810000000000000000000005fe0008ee0901e30000000000002d90000000000000000000008b80000000000880007ac16900000040c0000000000004c400000048400000007a00000000030c00000091e0005541150005045be0007f400000000013900035031800000000000000045c8cc1bd81886400090273600000000000000000000000000000008e0000000000bc0000009a400000000000089600075a28c0000000000000002870000000000009428486b23b86e86fa000000a6000058059e3be22470080e246aef8604861c53003d08847d45960c60e2000000a850000000000000000000000002fa0000f15a4000000450000a86000000000000294000a440006f481e47e3aa00898208aa780004200000008228a00000000002d20000000003a41f64ba0005c80000007a8000317000000ae2a423ee00017c0000ed00014c0002060006c01c04680000007720007e60000000000000004e20000000000008a23b078400073e7b214e162000000698658000000000000165a2e0000000006f60000000000009bc00095e7ee0000000000001270f30002a63940007fe0008c29cc00079e00000000034429c53e6680000000000760009da00000081c79600000038e8fc00000021aa660d041f74e298000a2c000616a6d0000000006f00000000008a400027297c00097403c9f2816432000000000adc0008660000006462f31b000000000000023b0000009f450c0000006a60000000000000ee0003628ec0000bb2690000000000008a60000000000006883080000001187de00000010e812000102000000000066abc634000000000a3600000000077a0000000ca000000000000a9c00000032f88eaec8306803fead31120000000004b40000000000000001bf000000000000000000000000190964920732000492000a5a167000000ae00000007550b900000036a4c29245da0002fc0000000000000000000be000000000404000055000000000000918acf3c49d04c800231a24a4294b815e2ce02814b4da342000000ab614100007e0009f04b20001fc00000000000002c0000000001a00000008929561c700000053a24515d1ea0000000007372310000000001d9000412000000000000000000000aa200082a99e0001a90000001a60000000005fc0000009442921fa39823fa048ea0000000000000000005460856d298a6a2000a3a0004401c812b75400000079440a000a16378000a1400083600000000068a0000000006cc0808105d040694
  | 12 => 0xe10348e25e830a63e13521ba52926058000a4a2b6742a340000000000000000000000005ac00000000005e0000006140000003c674a000ae318278cab80004ac00000000000026d0003460002c29c40ce00000000000000000000000000000037f00082e0f600000000000018a0008d000008200012d9ce5b80ae0004d684c000460a887b657e4ea2fe878a3c41488c0000000002f0a4d15323c000738180a7a0000001bb6ba00000070cade43a0001940122a068200000000000000000000000039c0000000008aa00000000098c00001d0000001ca0001e00000000000000000000000000000000000000009ec188a7626636c7700000000000000008f200083e0008ae0008be4545f00000000000000000000000000000000000000005ec5167510cc3e20000003e65aa000a9000078000000000000000000000000000000082c00000006471257897000000028b0002829b238a00041d70615a5281d085893a4d400020ca280000001e76ec0a986c0000000000000004e467b2040000000b500065a431000a4c0002e43b400000037a00000000098e0000000004984700000003027aa49c52c69e2be5120000000000002a200096c000af649a0cb01a68c32400000000064a5e60003702ae2e2000000000000000000000a080004800000000000000000000002f81500000000000000000000000000000000000000000001ec0000000009710000000000000000000000006ac00060427100000000000016a0006b80008f01fe0004e069c0009945868867bc5fa9880006660000000000000001630000000000000000000000000000000001542e8980a1eacd65416d1364082d495a00013f0000000000000000000006500002170004cc7100180000001db00000070eaa80000000000007e200069d0000000a20008140006a500000090e00000045a9ea0000000000000000000000005882e000087a52400000000000000000000000091a00022635c04e4306b6958a8a34827841e5980000c800003e6f85c08ba4dc00000000000000000063245e1204a27165e400093c0000000e9000000000000000000000000000a7401050e774aac11001c33242a84a3dc223aea93829300000000000000044e00630f6ea390a3e2960000000002c400000000032b2410005189ac4d89a87ae00094c0000003b200069000048e0000000000000005b000000000001e0008da6720000006fe00000084445200049400000000000000066a0e800000000072000002a0000000000000007ea0002800000003820fb4280000001340000000000004900000000000002f40000000000005d60000000000000000000007480300000001250007a6000000000000000000000000000582000a2200026850a6709f600000000055623e0000000000004969d8000000000
  | 13 => 0xc0de000a106c40000fc00017287c8d248261e5a000000081a0003e400000000000064e0000000007d80000003e8000000000a8e6ca0003f80002ca07497860200060c0006da7280002f60000000000000000000000000000000000000000001582860000003ce3f600000082400000000000021e92e0000000008886b022b00000040e00017800000000027e2798461fd0701164a46a004428931432672e0fd6d83a62bc13b143ae900000031337e6d19e000000097e9320000000004623c87da11a000000aaa8d84241c400041690665216061206000091c0000000848825a800000000000000013a1220000000000008024fe2569ba91047400037c000ae80009ee29b0000000000000004de9be00000004c1cc0000000036180000383ec7b88d4000000a240000000000000c966e78e00000025a0000007b40000000002207640000000000dc00072409b91200053813d0002440000000000000000001e900040232800000000000000000000c0f2000000000000aa000016651e0000000000007040000000008040000008dc49e46a0000000000000000000000000000000000000000001240000000000003a09b05220000005ae31100096069200014a99f62408300051a5b400014859c8f65f29500260008ac0c0af22e60000009b90000000004e82da9480001280e17a200000000000085a0006386dca0a00023000000000042c0001f100000099200e00000052e4ec00000009e0b69752ee24e10a00052000035a0000000000000f49e80000000000000007b000042b3de65e3d20000000000000007780000009c200025c0000003f30005ea74100089c2ac2dc0001e497270a8c622c4f02b200003667c54432c0003f02140fa0000000401de75c00000000000092c0005660004b64260000000000002eca6a5a21460b4000ad407c00000000086a51c1a830400000000035400000089a00000041036e00065c686000132000000594000592734000a96852000000a8438c3e73c055c7ba00060628d3201d42b800048a82600000000000000062a0000000000006d0000a063c20201c61bc1336e02540000000000000009d4000242322277472000000aee56c00000000000000000000058a57083400000014d015a0c3801701569900000002990000000000ac330000000000000000744abe4bc0000003e002e9c8648000000000000000000000427000000000000000000890a7e00000000005c00000068400000047a000000228000000000ab25b60000000001c200000000009dac098653caebad82ff70284000000000000016c00000046400000054c00000019e5d233600000000019c2ea46c6002aa000a8c6401f54aa64256a5bc0002845640001268945d89fe094000ac20001060000003589b80003640003d800000000000000079ca
  | 14 => 0xa320003126c660ea9a3d6a6800042f4f83ac32e7267f02d6176000000192aca0000000000000000000004fc26e71c3fc9528fa0000008b40001b4000000ac800074d00000000000055800095c1b60000000004ee8c40005c20000b700086e000000ad60002f700025e000000000000233000000000000ace47c0008ca0000000000000000000000000000000000000f500000042d0da000000000000000000000a2600082005b5f835677ea1caba00000026200000000000000000000000077622d7455761ee8429f897a0000000002bb58400067e4a827a1d816f0000000000002160000000000000000000000000003100000008c8000adf3bc0000000b80000009400000000003f25265e03052d0000a6e20a99a0420bd00018600000077c5f428311e660a583680000007f621c8f42514340004ae7d600000020e0000008982b11d39680161990000000000000000110000000000000000000000000001ae99c5365d40000c300085e75200000014069faf41960000007ec5000fe4423603f976c4f40003060001520000000001980000b01ac000acc0000002c69980007980008e01420000000000e443c00005000000009c0002d80000000000000000003524880007dc7f8000000000000340000000000000000000121a80000000af500015c00000006e0000002880000000008626e48800005cc1b20000d8000900800062000ad957c000435000000000000ad000019a00000000026c0000006a400033c60800000000000044a7be3cc1f83164ca00000071859a45818b0000002b00000000e6000a02ac44c05341550000000004fa00000000041835e17a6d60000000007a000000000000000000033a000a56048000aae0f03d467aa380227660245021290005dc315a480000000008060000000007d213093639e000a5062c1ce26050858c0004e67580000686648bc00000051027312e7c200000067800000061a39a00a1b80000f700000000005a00050627d9080000000002cc0000005ba57a00058e00000006a00010c0005900009040000006bc29a2f203a2320007469636c876000000000000097600090a0000000000000000000009de0000000000000002db0000007c63860008700000000000008b20430003ba000000000a40874138a980000001e60000000000000000006bb6280bf00000000000093e6947fc05300000000000031e0000000000004c63e94ce0007f200068e0a00ad48caa400012a0006a8a5e0a4184a465ee87200000000000000000041a8a80000000000000d5091212171a123380c10003fa0003846300c2ae676e000000000000174782000000a000000001dc00072aa7000087e0000000001d694e0000004460ec39600000000078a00000000000033e21000000000000000000000030e1cd99685
  | 15 => 0x1080000000000001a40000000000000000000005620a700000000000000000080c0000006f2a7200000000096e90c0008380000e00000727c476213e00000067600005600046e6de00000024390bada6b4af10000000000006c20000000007560000000000001f400000000000000000047600000000000056000014f0699220009a2000187ab492a69a00000000000000046627f86800000000000000000096a00000053200061038166c0000000000c44483ca0000000000001f30000007860000000000000006e29a011d0003760000000000004f200000000000000000000042e4000005c614400083c0009e62de000a200001cf6d407827471aa542479147308e654a25025226173c05400076a768763ad20000000000000000003199dc22e0004227a40005425c40005741ba2360320000000922f59d60000000000005ce0004d29a610400095400016400000000000034c0007cc0002356be0a816e0007e400094f00000000080a3b60005e20002ba0002760002484b00000d40009fc9e20000008fe9301310000000000007d00000005f60002a818d2000002084360000000007500000008d67c822a00037d0005ca0000000000000009166205682700008e8a941a2086000100290000014a8200013c0970000000000000000001e236756e0008320000003da80843e000a620000000000000000008b00000b27ce00011400025800000000000000000000057200000000038800085471e00000000000000004a00000009300000000015f74c0001dd3410000001e800000096200000026455a0000000000000000000000008b60000007fa9d20000000007220000000000006ae6e61d2000a5c0f85401be15700016800037209905216b7086567ca55e4be8de30b0007e800000015ba180000000005500000aa00000000028e00000000060a000000000478000a9200000000061c0002b400000000062209800000000017e00089e0000000003342c3000ae40000000ea0000abab01f22650000000005de0000000000000000004a000000000000000044c0003ae0c500000077509579024c0d20000000000009e400069b0000000004f600000000072c7927142bfa6482831c3a800034a75e00000018c000000000000000000a9e53094a0000006260008500010007c0000a1a00000000045664c79a0000000000000000000000000007e00000002c82c53a2a309ff21888a73a8f89fa00037409a0000005b2984000000000a2a000a6c0000006fc6ee046000674000000000137000876222000ac6000000a4e0003ea9c04d0a7c00000000000000023a00028a92812c0000a60001610009b632a5149ca000000af08c0000000000000392aa60004380000000000a183a00026a1eb0000000000040000000002340000000001052c000034e
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1a8b84e037358910006b0e0780dcd62440014ca9720373589100052364c741cd624400148c945cc735891000683615841cd624400144e959d0735891000523a52741cd6244001c0f751d07358910007031d4741cd6244001c0e851d0735891000703614741cd6244001c4875a007358910007221d2801cd6244001a49856007358910007121d5801cd6244001a89846007358910007221d1801cd6244001ac18160073589100060ba1c75d0d624400188e87dcf43589100062321c73d0d6244001c0c751cf43589100042ba5e8750d624400188f9321d435891000623cc48750d62440018a63121d4358910006234c48750d624400188f3021d43589100062a8c08750d624400188d3021d43589100060b21f7550d624400182c871d543589100058364c7550d624400188c87e0d43589100062321f7350d624400188c871cd4358910005836547350d6244001c0c751cd43589100060b21f5350d624400188c8794d4358910595836565350d62440016859194d4358910005a26425350d624400182c8754d435891058f828c15350d624400148c9754d43589100062321d5350d6244001c0f8754d435891000683a1d5350d6244001a0c8754d43589100070321d5350d624400180c8754d435891058f03dc15350d6244001e095350f70589100061a21c754c16244001649931d530589100062a21c744c16244001689931d130589100063221f734c16244001649951cd3058910005a2650734c162441616499594d3058910005a2652534c162440016c19194d30589100051a25d534c1624415fe423154d305891000712e5d534c1624400164a9754d30589100059225d534c16244001c489754d305891000692a1d534c16244001a488754d305891000782dd1534c16244001e087454d30589104ef12dc5534c16244001e0953d0d305891000592656434c162441036899490d3058910005b0646434c162440014a89750d305891000782d4d434c16244001e095350d3058910577a08c5434c16244001c8b9750d3058910005a2a5d434c162440016889750d30589100072225d434c16244001a8a8750d3058910006a221d434c16244001e0b7550d3058910007821d5434c16244101c8b7150d30589100079054f714c16244001e8143dc53058910007a0d0d314c16244001e81434c53058910006b0a1d314c16244001ac0874c53058910007a0dd1314c16244001e80744c530589100054c65641dd150440016299419562541100059264c6558950440011d19321d41541100064c21d5450550440015319494775501100058a6546458940440016899319162501100047464c87545404400193087551515011000c6c25d8550540440191b0985d5415011013e6821e6250540440539a087589415011014ea8219625054044013ca0765894150110
  | 1 => 0x652a1d534c161480119488754d305852000742dd1534c1614817bd087454d305852000562a5d434c161480015889750d305852000662a1d434c161480119888750d305852000742dd5434c16148179d087550d30585200457025d314c161480011e19804272d911000558654109cb64440015a19404272d91100057064c109cb64440011e29804172d911000558654105cb64440015a19404172d91100057064c105cb644400581f8754d43d91105a7039c95350f6444001a0d5320943d911000613214835cb644400106c9854d72d91100070354d435cb64440011729804375591100054c65010dd564440015519304375591100050764c75dd1644400905c985cd53591104a5132497354d644400141e9754d43591100040f660549d9544400141d9315276551100040f660541d9544400141d9315076551100050e640541d9544400181c5460c76551100049364c85592624400160d9598d43989105af215c56350e6244177c897058d43989105d7425c15350e6244173f001054d439891013c78261715c26244153d417154d30989103f7605c5434c2624404f3c0984c5309891044f305d9314c2624400122f9855054989100068355183152624410d48c9754d439891000703e1d5350e6244169c0c8754d43989105cf035c15350e6244169e097054d43989100046ca6010dd162440015319504374589100056464c10dd162440011d29804373589100056465010dcd624400181f85e13735891000607a1d5350d624400181c8754d4358910006131ce85d09624400148c9750e325891046c2b25d840c9624400148c9750c325891000683615430c96244171c0c7550c32589100061a1d5800c962440018a874600325891000632dcd800c96244001a49536003258910006a250d800c962440058588754d30589100162621d434c162440013a298043745891000568a5c10dd16244001721950437458910005e064c10dd162440013a198040745891000568a5c101d16244001721950407458910005e064c101d1624400124d932156458910004f0a6010dcd62440015c2970437358910005e065010dcd62440013c198040735891000570a5c101cd6244001781940407358910007601d0101cd62440010ac976126358910006680408750d624400188c8798d4358910005836566350d624416f6859198d43589105b5a26426350d624400188c8758d43589105afa00416350d624400190c8754d43589105a703dd95350d6244167d0b7054d435891058fc00415350d62440531e198dc770589100055225d534c1624413bd437154d30589100056225d434c16244101d837150d305891014cf0261314c1624400122f9855054589100043325d831516244001a0d5460c54589100068a551801516244001a0f85e13735891000692e1780dcd6244
  | 2 => 0x8001c449754d31587204a691a1d534c561c8129a448754d315872060691e01534c561c8001e0553d0d315872000591656434c561c817f6859490d315872000781d4d434c561c8001e055350d315872000721e5d434c561c8001c849750d3158720436a1a1d434c561c810da848750d31587205bea1e01434c561c817dc0d7254d43d95200150725d5350d654812944e92dcd53d91205f7035c95350f644800581c8754d43591205f7035c95350f6148093c0c7254d43d85200069154d818cb6148001a854360632d852000683611530cb6148001a0d8550c32d85200069154d810cb6148001a854360432d8520537125c9534c36148147c897250d30d852000523a5b7350f654801150c9754d43595200074254d43dc165480115489754d305952000652a1d534c165480119488754d305952000662a1d434c165480119888750d305952000513a5b7354f644801190c8754d43591200074254d43dc1644800194a8754d30591200465221d534c164480115889750d305912000662a1d434c164480119888750d3059120005836506354f614800160d9518d43d852000592654634c361480016899418d30d852000692219534c36148001a888650d30d85200048be61541536148001a0d5460c54d85200068a5518015361480018c57360473d8520005916477354f614800160d941cd53d8520005916447354f6148001649901cd53d85200069254d8090f614800184c8754d43d8520005a16477350f614800160d951cd43d8520005a16447350f6148001689901cd43d8520005a26425350f6148173e0a3054d43d85200052325d5350f6148001c0f9754d43d85200070325d5350f6148001c0f8754d43d85200070321d5350f6148173e071054d43d8520005b0647734c36148001649951cd30d8520005a2650734c361480016c1911cd30d8520005a2652534c36148001c4b9754d30d85200071225d534c36148001e0953d0d30d852000592656434c36148001e0b5350d30d85200078254d434c36148001c8b9750d30d85200072225d434c3614800188e841ce655852000613a1473991614800190f85e13735852000652e1780dcd614800198b84e0373585200041b6607518d614800144d931d463585200042b6607418d614800148d931d063585200061321f6354d614800184c8718d5358520005836506354d6148001c0c7418d53585200062321f6350d614800188c8718d4358520005836546350d6148001c0c7518d435852000543a5d5350d614800150c9754d435852000643a1d5350d614800190c8754d43585200465121d534c561480119848750d31585200074254d43dc16148001d41534c770585200076050d31dc161480118c887d8d305852000592654634c161480016899418d305852000552a5d534c161480015489754d305852
  | 3 => 0x2cd40e8c88e13396947000bdf4047b3682027911e1280d99c80031000cb02f0973e77b48136e2551d60005f000d3a523ea489e02dbe0008f62c00c7060002ba67a9e001baa928e00000000006041e0000000176b0a503080052a7602040630001e00000091670950d8003f2d6bf44cc79c4453327eb289790ebf1485a8fe028009c1f600000002f26c8002d09f24000b695e0004a0001d004190040000000008020000200c030040500800008210000000c080441300c0100400038000000001005024040080000011000010040800000000000440100c05000000080b02c000040000805004000440001812024070380000801004010000101c24000000280f06c01038070080d00c00018010040f0000600002000000280b018180240001000000000040b02800004110040d008030003a018100300000c010000a000000180800c0304000000170041603003008010884201408004110100e034000000101c020040509004004000280c004010040000447660545cf625500141e9615173d895400607615845cf625500188c825cd43d895448e0761d5350f6255185a0c8254d43d895400683615430cb62550018c97360032d89540069254d800cb6255001a894360032d895401d232497350d659092944e92dcd53586425a781c855350d61908058548754d31586424a513a4b7354d6090969e0b2054d43582420161621d534c1609080581c8754d43595424a513a4b7354f6454001a0d8550c32d89500069154d810cb6254001a854360432d89500069254d800cb6254001a894360032d8950435232497350f615400141d931d9545055043523a4b7350f6550001a0d8454c32d89400069154d810cb6250001a854360432d89400069254d800cb6250001a894360032d89404a5132497354f615000141d931d954545400150725d5350d65c817dc0c7254d43597200160721d5350d64c817dc0c7254d4359320237035c95350d61c817dc0c7254d43587205a781c855350d61c80058548754d31587204a691a09534c561c814bc457254d31587200162521d434c561c810da868250d3158720517215c9434c561c810d50c9754d43597204a64321d5350d64c81299448754d31587204366121d434c561c800122f985505458720006835518315161c8001a25546045458720006325cd801cd61c800160d941cd5358720005926407354d61c8001a455360643587200061321d5350d61c800160d951cd4358720005a26407350d61c80016859194d435872059f818c55350d61c800148c9754d435872000703e5d5350d61c8001c0c9754d435872000703e1d5350d61c8001c0c8754d435872058f81c415350d61c8001645951cd3158720005a1650734c561c80016c1901cd315872060d91656534c561c80016859494d315872000711e5d534c561c
  | 4 => 0x18c0036c00002906019600002b70dabd000b486d608cd4c0000007e65000506a621a965081400123000003b8003af267a86a7e0002fa4e00185000006d2b008e140000055cf2bda34330525c120aa1a69319a6aabc0000046c943b16e44ca84b8508900083000002ca500f83bcf40011a08870c6b3c9b892000fa0e80000000268644aa9c00192a2b4e00300594c03c28cb62c07c0775a11042964076e86e2482306600186bb1841ec0000000c92de1764268889baa36b92623ff470c26a6d800c3000000009b2b44a000918000008a00112748000013c001240005a00134091388b8000017200188003384f8e62f0a443318109b0c4844ad800a2054a82fa2c00027400b11cc948000022c000b288a3c8388d3a8006b800b20008820a002be9a0dea56860c4d11a000d25d899000116770004848a1c99800d163a770a229c01498d404a562fc7dcea5a0e3163713ac80cb321c6532ce214000c9ec001fc18aaca606e951ca001c00008ea88692b0000f9f200073000001f0670019000046c12062122a7880027071c40e014de8a10d618640154aaa6a269eef006d52bf800d49562f4002e1e3a007a000000e4ae00000000510018e1d8000dc83b53140015bd18004d9e65b000960008030235558002320000000216418004ca9d001acd282a0017fab800000000016b71c881397ec1c1a6a00000000000004772e001f40034b26000258290025c002eebe00016c000000000000d0c000000600000000009fd675f0931aec6d128216500b805e2d887060d2391e48e1d49facc5d02e040000030652f0a012107b99832a78ac9ce2ea1258b31810008616009800cc1d3001020845676800298f631800001bc8a00003b420a2608c016070000833477c009f00042505000000b4720002b7817a0030e0005c0024a000001fc811d1780d082026e6c2104001a4879c2ae1c84582c4215ad31468098a0f14eca95c541fe86a743427a031a01b0d8462d0510e2160801e55550c57aa966741
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x60b800000e044980081400f30000000000d00dc0002c0e3805601d001c0075747007800800018061900fc2d0dc03f40665497002f54a0a8024980942600f8000004b20021635620000000000000b2acc00056000006c00048d802734cc5b9002f11100000000000ebad500000320168000280054678029048001808301068080008183008009000180800083000580000030f00d952097350f62550014075472ea9a86b0e4000903aa78754d435872000501d51cbaa6a1ec29000240ea9e1d5350f614800180643b2831aa6b0a40009036a47418d53585200060190eca8c6a1ac29000240da91d46350d6148001406542a6a1ae5b2220008076a45460c765511000481d53c3aa6a1cc4882e280ca7615430c962440018064bb0aa1864b122000a1268c756003258910005113463a300192c488002848a754d800c96244001c043a2a6c0064b122000a2229d436003258910007010eaa1b00192c48800204ca764c8559162440012c0d48e8080e6b122000c60660740407358910006a032a3a02039ac4880021a1a90408750d6244001490d282043a86b122000a6068c1021d43589100048194ecacc6a1ac48800300c876566350d6244001c800810ea9a86b122000c0325d5460c5458910007010eac230039ac488003809851d1801cd6244001c403a302c00e6b122000a036973121d435891000501b4b9810ea1ac48800300c8764c7550d624400180643b2a39a86b122000c2121d9194d43589100061110ec84a6a1ac4880038063121d5350d6244001c051810ea9a86b122000903aa78754d435891000501d4f43aa6a1ac48800300e9721d5350d62440018064b90ea9a86b122000c1221d931d530589100061110ec98e8982c4880030489721d534c16244001a044b8e8a9a60b122000e0221c7454d30589100058114ea9e86982c48800340897d4d434c162440018444b90ea1a60b122000d0225c7550d30589100070110e3aa86982c488002c80a750d314c16244001488d190eaa282a822000a4468c875515150110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x80004901ba0408754d4358910005101b90408754d4358910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94c
  | 6 => 0x94d
  | 7 => 0x3
  | 8 => 0x98c
  | 9 => 0x98a
  | 10 => 0x98d
  | 11 => 0x98e
  | 12 => 0x2
  | 13 => 0x150a
  | 14 => 0x150c
  | 15 => 0x150d
  | 16 => 0x150e
  | 17 => 0xa0a
  | 18 => 0xa0c
  | 19 => 0xa0e
  | 20 => 0xa4a
  | 21 => 0xa4c
  | 22 => 0xa4d
  | 23 => 0xd09
  | 24 => 0xd0a
  | 25 => 0xd0c
  | 26 => 0xd0e
  | 27 => 0x1609
  | 28 => 0x160a
  | 29 => 0x160c
  | 30 => 0x160e
  | 31 => 0x1049
  | 32 => 0x104c
  | 33 => 0xa0954
  | 34 => 0x94a14
  | 35 => 0xa4954
  | 36 => 0x94e
  | 37 => 0x94a54
  | 38 => 0x209
  | 39 => 0x1549
  | 40 => 0x1409
  | 41 => 0xb09
  | 42 => 0xb89
  | 43 => 0x1849
  | 44 => 0x1489
  | 45 => 0x180a
  | 46 => 0x130a
  | 47 => 0x150992
  | 48 => 0x150994
  | 49 => 0x150995
  | 50 => 0x150996
  | 51 => 0x99514
  | 52 => 0xb8994
  | 53 => 0x98b94
  | 54 => 0xbc9
  | 55 => 0xbc994
  | 56 => 0x19c9
  | 57 => 0x98bd4
  | 58 => 0x14c9
  | 59 => 0x104994
  | 60 => 0x99054
  | 61 => 0x1a89
  | 62 => 0x1949
  | 63 => 0x1889
  | 64 => 0x409
  | 65 => 0xd49
  | 66 => 0x1649
  | 67 => 0x1a09
  | 68 => 0x449
  | 69 => 0xb0994
  | 70 => 0xb0c
  | 71 => 0xb0d
  | 72 => 0x154994
  | 73 => 0x154c
  | 74 => 0x99554
  | 75 => 0x154d
  | 76 => 0x154e
  | 77 => 0xd0994
  | 78 => 0x98d14
  | 79 => 0x160994
  | 80 => 0x99614
  | 81 => 0xd4994
  | 82 => 0x98d54
  | 83 => 0x164994
  | 84 => 0x99654
  | 85 => 0xb9514
  | 86 => 0x150b94
  | 87 => 0xbd514
  | 88 => 0x150bd4
  | 89 => 0x105514
  | 90 => 0x151054
  | 91 => 0x104b
  | 92 => 0xd1514
  | 93 => 0x150d14
  | 94 => 0x8d
  | 95 => 0xd5514
  | 96 => 0x150d54
  | 97 => 0x8e
  | 98 => 0xb8a14
  | 99 => 0xa0b94
  | 100 => 0x138d
  | 101 => 0x124d
  | 102 => 0x128d
  | 103 => 0x104a14
  | 104 => 0xa1054
  | 105 => 0x198d
  | 106 => 0x134d
  | 107 => 0x124e
  | 108 => 0x128e
  | 109 => 0x104a54
  | 110 => 0xa5054
  | 111 => 0x180e
  | 112 => 0x130e
  | 113 => 0xd4d
  | 114 => 0x1a0d
  | 115 => 0x194b
  | 116 => 0x164d
  | 117 => 0x105614
  | 118 => 0x161054
  | 119 => 0x44d
  | 120 => 0x188e
  | 121 => 0xb8a095c
  | 122 => 0xb894a1c
  | 123 => 0xa094b9c
  | 124 => 0x9c992
  | 125 => 0xb18d1
  | 126 => 0xe8b11
  | 127 => 0xe8992
  | 128 => 0xe9551
  | 129 => 0xb0e91
  | 130 => 0x18cb11
  | 131 => 0x18c992
  | 132 => 0x18d551
  | 133 => 0xe9512
  | 134 => 0xe8b
  | 135 => 0x18d512
  | 136 => 0x18cb
  | 137 => 0xb4b11
  | 138 => 0x989d2
  | 139 => 0x144b11
  | 140 => 0x154b11
  | 141 => 0x3cd
  | 142 => 0x170d
  | 143 => 0x40c
  | 144 => 0x188c
  | 145 => 0xe8e
  | 146 => 0x18ce
  | 147 => 0x12c992
  | 148 => 0xecb
  | 149 => 0x1a4b
  | 150 => 0x99512
  | 151 => 0x9c995
  | 152 => 0x9c996
  | 153 => 0xe8996
  | 154 => 0x18c996
  | 155 => 0xec995
  | 156 => 0x1a4995
  | 157 => 0xed551
  | 158 => 0xec992
  | 159 => 0x1a5551
  | 160 => 0x18c9
  | 161 => 0x1a49
  | 162 => 0xe8a
  | 163 => 0xe89
  | 164 => 0x18ca
  | 165 => 0xeca
  | 166 => 0xec9
  | 167 => 0x1a4a
  | 168 => 0xb0b51
  | 169 => 0xecb11
  | 170 => 0xed512
  | 171 => 0x1a4b11
  | 172 => 0x1a5512
  | 173 => 0x1a9951
  | 174 => 0xe89c99a
  | 175 => 0xec9c99a
  | 176 => 0xb0ed1
  | 177 => 0xece8b19
  | 178 => 0xe8b0ed9
  | 179 => 0xece951a
  | 180 => 0xece93
  | 181 => 0xb4e8b19
  | 182 => 0xe8989da
  | 183 => 0xe8b0b59
  | 184 => 0xe83d6
  | 185 => 0xece9559
  | 186 => 0xece899a
  | 187 => 0x9ce899a
  | 188 => 0xe89c99e
  | 189 => 0xec9c99d
  | 190 => 0xece91
  | 191 => 0x150e92
  | 192 => 0xecb0b59
  | 193 => 0x150ed2
  | 194 => 0xed053
  | 195 => 0x3ced5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 38
  | 7 => 856
  | 6 => 2173
  | 5 => 1404
  | 4 => 426
  | 3 => 59
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1142+((h/22+packedAt gbK8 (988+(h % 22)*7) 7) % 82)*7) 7
  | 7 => packedAt gbK7 (35247+((h/325+packedAt gbK7 (31672+(h % 325)*11) 11) % 1173)*11) 11
  | 6 => packedAt gbK6 (114264+((h/830+packedAt gbK6 (104304+(h % 830)*12) 12) % 2991)*13) 13
  | 5 => packedAt gbK5 (89376+((h/545+packedAt gbK5 (82836+(h % 545)*12) 12) % 3474)*12) 12
  | 4 => packedAt gbK4 (31580+((h/176+packedAt gbK4 (29820+(h % 176)*10) 10) % 700)*10) 10
  | 3 => packedAt gbK3 (4987+((h/26+packedAt gbK3 (4779+(h % 26)*8) 8) % 136)*7) 7
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x87f1f83e3843f8fc1fc701c3ff2113313343f
  | 1 => 0xf87e3fc1c07c3f1fe0f801fc3f422cc2cc8cf
  | 2 => 0xf007fc001ff803fe000fffe00389ccf0cf0f0c
  | 3 => 0xfff800001ffffc00000ffffffc0e0f00f00ff0
  | 4 => 0x1ffffffffff00000000ff000fff000
  | 5 => 0xffffffffe000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x90480408004824024104408a00011011415
  | 1 => 0x82210804004110840880888140004404484a
  | 2 => 0x10074818cd8803a40c6d25c08a60c4f04f0d0c
  | 3 => 0xad5000211256a80010824a13300e0b00b002a0
  | 4 => 0x844000421b67324939c00301100f7000faa000
  | 5 => 0xce6492738042200021000c02200fbfaa000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36428
namespace PEqualNP.Outside.L_meta_36428
open PEqualNP.Outside.L_meta_36428.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 24 := bs0_3_0
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
theorem bs0_4_96 : Interval s0Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 117 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 bs0_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 46 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 24 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 117 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 31 := block_range (n:=31) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 31 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 15 := bs2_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_32 : Interval s3Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_64 : Interval s3Atlas 2 64 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 65 := (concat bs3_2_0 (concat bs3_2_32 bs3_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_128 : Interval s3Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_160 : Interval s3Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_224 : Interval s3Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_256 : Interval s3Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_288 : Interval s3Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_320 : Interval s3Atlas 3 320 23 := block_range (n:=23) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 343 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 (concat bs3_3_96 bs3_3_128))) (concat (concat bs3_3_160 (concat bs3_3_192 bs3_3_224)) (concat bs3_3_256 (concat bs3_3_288 bs3_3_320))))
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
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_896 : Interval s3Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_928 : Interval s3Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_992 : Interval s3Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1024 : Interval s3Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1088 : Interval s3Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1120 : Interval s3Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1184 : Interval s3Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1216 : Interval s3Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1280 : Interval s3Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1312 : Interval s3Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1344 : Interval s3Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1376 : Interval s3Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1408 : Interval s3Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1440 : Interval s3Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1472 : Interval s3Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1504 : Interval s3Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1536 : Interval s3Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1568 : Interval s3Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1600 : Interval s3Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1632 : Interval s3Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1664 : Interval s3Atlas 4 1664 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1671 := (concat (concat (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160))) (concat (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)) (concat (concat bs3_4_288 bs3_4_320) (concat bs3_4_352 bs3_4_384)))) (concat (concat (concat bs3_4_416 (concat bs3_4_448 bs3_4_480)) (concat bs3_4_512 (concat bs3_4_544 bs3_4_576))) (concat (concat bs3_4_608 (concat bs3_4_640 bs3_4_672)) (concat (concat bs3_4_704 bs3_4_736) (concat bs3_4_768 bs3_4_800))))) (concat (concat (concat (concat bs3_4_832 (concat bs3_4_864 bs3_4_896)) (concat bs3_4_928 (concat bs3_4_960 bs3_4_992))) (concat (concat bs3_4_1024 (concat bs3_4_1056 bs3_4_1088)) (concat (concat bs3_4_1120 bs3_4_1152) (concat bs3_4_1184 bs3_4_1216)))) (concat (concat (concat bs3_4_1248 (concat bs3_4_1280 bs3_4_1312)) (concat (concat bs3_4_1344 bs3_4_1376) (concat bs3_4_1408 bs3_4_1440))) (concat (concat bs3_4_1472 (concat bs3_4_1504 bs3_4_1536)) (concat (concat bs3_4_1568 bs3_4_1600) (concat bs3_4_1632 bs3_4_1664))))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_832 : Interval s3Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_896 : Interval s3Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_928 : Interval s3Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_960 : Interval s3Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_992 : Interval s3Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_1024 : Interval s3Atlas 5 1024 20 := block_range (n:=20) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1044 := (concat (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 bs3_5_96)) (concat (concat bs3_5_128 bs3_5_160) (concat bs3_5_192 bs3_5_224))) (concat (concat (concat bs3_5_256 bs3_5_288) (concat bs3_5_320 bs3_5_352)) (concat (concat bs3_5_384 bs3_5_416) (concat bs3_5_448 bs3_5_480)))) (concat (concat (concat (concat bs3_5_512 bs3_5_544) (concat bs3_5_576 bs3_5_608)) (concat (concat bs3_5_640 bs3_5_672) (concat bs3_5_704 bs3_5_736))) (concat (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)) (concat (concat bs3_5_896 bs3_5_928) (concat bs3_5_960 (concat bs3_5_992 bs3_5_1024))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 48 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 9 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 50 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_128 : Interval s4Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 136 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
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
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 9 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 50 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_128 : Interval s5Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 136 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 59 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_416 : Interval gbAtlas 4 416 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 426 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416))))
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
theorem bgb_5_1376 : Interval gbAtlas 5 1376 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1404 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184))) (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))))))
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
theorem bgb_6_2144 : Interval gbAtlas 6 2144 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2173 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))) (concat (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896)) (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))))) (concat (concat (concat (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312))) (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856))) (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)))))))
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
theorem bgb_7_832 : Interval gbAtlas 7 832 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 856 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608))) (concat (concat bgb_7_640 (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 38 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 48, 52),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88fefefeeefeeefe88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124270 * 2 ^ 32 + 4277075592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36428.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[0,4]⟩,⟨.or,[0,2]⟩,⟨.and,[6,8]⟩,⟨.or,[7,9]⟩,⟨.or,[0,4]⟩,⟨.and,[1,5]⟩,⟨.or,[1,10]⟩,⟨.or,[3,12]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277075592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277075592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36428

open PEqualNP.Outside.L_meta_36428 in
theorem PEqualNP.Outside.L_meta_36428 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277075592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277075592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
