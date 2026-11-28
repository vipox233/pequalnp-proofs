import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36697.Model
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


end PEqualNP.Outside.L_meta_36697.Model

namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
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

def SBf (j : Nat) : Nat := [4, 6, 7, 8, 6, 6].getD j 0

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

def mirrorSteps : List Move := [swapRows 84]

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

end PEqualNP.Outside.L_meta_36697

namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfc07ffffffffffffffff01fffffffffffc3fff
  | 3 => 0xfff803fe01ff00ff007ffe07e03f01fc07cccc
  | 4 => 0xfffffc0001ffff00007ffff8003ffe0007f0f0
  | 5 => 0xfffffffffe000000007fffffffc0000007ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x940924921451121252151628aa4552a551d555
  | 2 => 0x2b42492528a2a4a4a42a815554aaa54aa42aaa
  | 3 => 0x4d5762394d348ec836cfab06663331f036cccc
  | 4 => 0x726473b1b1c8c88ec773cd9c183cf860c770f0
  | 5 => 0x838783c1c1f0f0f0f87cf1e79f20c18307bf00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0ccc0c0c0c0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36697
namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3200c5000100c076904b024a19080bf42bd42df32dd32f621f521be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x400218d424cb4a8490f14c921
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
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
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s1K3 (84+((h/1+packedAt s1K3 (81+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f807ffe01fffc0f03f83f07ff07fe0289e7c
  | 3 => 0x3fff80fffe03fffffc003ff83ff83fff0e38f
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x808504022420480014584508450842a832cb5
  | 2 => 0x595534a651d4a915782aa2b46ab46b41a8965c
  | 3 => 0xa264a52a9491b234baa0432d232d239530c30a
  | 4 => 0x3346c6cd191923a6dcf36a0843ce71063d03e0
  | 5 => 0xc387070e1e1e3c38ef3c73ce720842183ef800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00aaaaaaa0aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36697
namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1005d4923e8c00d3430a154c44ca40c3c513000040b1ca8f050ea019d2c40e0000000000001382400000000b10a5126112b086c00700168060420600058628aff43df43fe43be43fd43fc43bc43dc439c43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x3a7725154d2090a1f85a23001600a003420044000004c4a00371c01a2a378840046280004c7200078ce471c0002200000c8a642318dca23d36830f65d301d8b8000e1cc000013838000000000021a0c978403600020a812320004843309648a00000000000178002c003f8ac000038910003a0013c36002f9a8923b3e12c7e172d028901801010a4003a994d666310cc00001616c50003a0f82057269040615000d4780600138000f1481c007d200e4687800000982e18158f4790f8c4d80b0003810081060380000287000002808406068200000100810a0082050880808300008104800001800581845794e439f29c871e5390f3a8621cf94c43cf298875e5410f3ca821e7d4843cf290879d5210f38a421e7d4443cf288879d5110f38a221e7d4043cf280879d5010f38a021e710f42af29c855d5390b3887215d94642baa8c855f5350ab8a6a16710d42ce218859c43cca7ca9194f55232ce21c6576518caeaa3194fd51329e2a2659c434cb3886196710f41af29c835d53907388720db94a41b6a94835f53506b8a6a0e710d41ce218839c43cc67ca918cf55231ce21c636e528c6daa518cfd51319e2a2639c434c7388618cf953219eaa6435e53c86baa790e710f219f2a4433d54886bca710d754e21ce21c439c43487388610f948421ce21e815e53902baa7206710e40afa9a815c535033886a05bd4940b6292817751502e8a2a06710c40ce21e613e548c27aa9186710e309faa2613c544c33886985bd4930b62926177514c2e8a2986710c30ce21e419c438827ea8904f15120afa9a415c534833886905dd4520ba28a413e540827aa8105794c20aea98419c43082eca2105d54420ce21e219c438427ea8884f15110afa9a215c534433886885bd4910b6292213e540427aa8085794c10aea98219c43042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x520848d820e8010069e1ba11a1400070080018001001593989b1606179192151c0a000e14839689998b00000a8000000000000004001a8d000c00000000090000000000001702a000001d85a19d0c830892881e99180b9f8f800f131c80109f00110780010a000160e0010a042400708082001c04207a59875210e9561d4843a59865210e956194843c35485210e8e62d4443a358b5110e8e6294443a358a5110f155114443a3d895010e8c6254043a5d855010e946154043a39885010e8d6214043a59845010e956114043c510e5190b144354642c510e518cb144354632c310e529070c4354a41c310e528c70c4354a318718d54c861c6454f2187d9443c861d6510f218718d548861c6454e2187d94438861d6510e21e110d210870c43d4940c310c525031443d4540c510c515021c6315130c310f524c30c4314930c510f514c31443145308798f544821e64d4d2087994434821c6510d20c510f514831443145208718d540821c6454c2087d94430821d6510c20c510e510831443544208798f544421e64d4d1087994434421c6510d10c310f524430c43149108718d540421c6454c1087d94430421d6510c10c310e520430c4354810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 5 => packedAt s2K5 (810+((h/15+packedAt s2K5 (720+(h % 15)*6) 6) % 60)*7) 7
  | 4 => packedAt s2K4 (3827+((h/43+packedAt s2K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s2K3 (2738+((h/22+packedAt s2K3 (2584+(h % 22)*7) 7) % 99)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 1 => 0x7f03ffe07ffc0ffff07c1e0ff83ff03ff44e73
  | 3 => 0x7ffc0fff81fff03fff801ff07fc1ffc0f8739c
  | 4 => 0x80000ffffe00003fffffe0007ffe0000ff83e0
  | 5 => 0xfffff0000000003fffffffff80000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x11040241048000002942410904215140194a5
  | 1 => 0x2a48a64324915d1cb0290a8d2a35a0aa744a52
  | 3 => 0x4c292a890d23456d550213a44e91ca82b86318
  | 4 => 0x68b2cd12483a69b669cf41087738830cde83e0
  | 5 => 0x70c30e1c71c38e3b8e739dce04210c30ef7c00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88aa88aa88eeaaaa88aa88aa88eeaaaa88aa88aa88eeaaaa88aa88aa88eeaaaa88aa88aa88eeaaaa88aa88aa88eeaaaa88aa88aa88eeaaaa88aa88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36697
namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0xb40023a004a856285a61e015243e0031708891833238daf0030a292a000001a40b0024b171a4244c1300040000000e001000f054a1c0004e000200000000011c3498c001c200060000fff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x617e510c2faa2186fd0430dea0861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4187714830efa1061de420c3ba84187710830efa8861de510c3baa2185754430ee28861df410c33e82187790430eea08619d410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720df20641bc40c83bc6190770c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63107b88620f610c417e508837c81106f10220ef18441dc30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837e82906f50520ef98a41dd31483de42907b48520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841bf410837a821077cc420ee98841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c43be6388774c710df20621bc40c43bc6188770c310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c21df53842bea7085f94e10bea9c217c53843b8a7085714e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210df20421bc40843bc6108770c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd41443be6288774c510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa0a43bd41487be6290f74c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81df31903ba63205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c813d5190378a3206fcc640cf98c81be319037a6320674c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540dfa0a81bd41503be62a0774c540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd421037884205f94440bea8881bf411037c82206f50440de20881df31103ba62205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311033e62206f8c440de988819d311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30bf28e617d51cc37e83986f50730ef98e61dd31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa51877cca30ef19461dd328c3b865185f94630bea8c61bf418c37a831877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5187714a30efa1461de428c3ba85187710a30efa8c61de518c3baa3185754630ee28c61df418c33e83187790630eea0c619d418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061df320c3bc6418774c830ee19
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41ef298835e53106faa620f754c41aea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31ef99663de32cc7ba6598f70cb31dfa0e63bd41cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa1663de42cc7ba8598f710b31efa0e639f41cc7bc8398f750731cea0e63dc41cc7bea198f794331af28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63bd418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263de324c7ba6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a639f414c7bc8298f750531cea0a63dc414c7bea098f794131eea8263dc504c6b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43bd41c87be6390f74c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621dfa0c43bd41887be6310f74c621f790c43f
  | 3 => 0x3750007349d0f8338871269c9000f291c2dc24cb500000061a9f88c9b40002fc0018a7d8ac9c6b5b4088a8f6177052609db8005d0000000005d82740008a480b55c6056448ac40022d000000000002eacc02fa4b04054c71b3a0001d40b3b04a0001dc17a7c4b8ce23ad000cd51909402ed053aa0b60824937800074a68529982fe30000051000ac18a0001ccbcc669804ee2780038f1f6078221e26a00002d9853fccd14f2cc588d889f03b486000003376ca9599d80051e5a863b231aa3450492a16a000000030050220100200600401802000008000010130000240780000a000048010060080500000402c0400401401402011012004000040040000a00001a0080480d00c0000000d0000640080000000c000090080000180b0020140480400016c0000001a00c0080401a00401001000000058010000000480200c018000040020000080000000000800004010078010180040000001200402007028044070020020000380b00000c0680000400c0400301400800803002000058010000540480100a0280300002a02c000250220280300c0060140200d00c03c04800000004018000060980000500001c0100403e004000000000040000b00a03402006002000008010200040000a01a00c01805000004038030040540080000800c0080000e0040300b000008028010040140180101a0000180000001002800000000020000060000380000000008802006000048000020280000e0020080a80000e014000020060040300f006010020000000340000200004c0100000003c0000100e0000180e02200c0300200001000004002000010010120900080000c000058010020200800300600c020010020000780c012050010040000000500300001c0000a00201800802002000088060020000b00002e00004df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0xc8026800000200098491fe285eb00069ecfcc38423507418fafd622bb46b30e740e2c000007b47d17a81822a9ac6f3ea0009481c0a01aeb4d6412c2fa92903230000719e194600091467847000e28a51937a82ad3a2c76b2d11c9aee54a00140b180863a0790966de9981ab990b09607f00070e000002a20000000030573e7f54600078a5cc573df306f552f000000c94a1b7d1a61f0b720c06cfbc8a3d318cee88628a3e459dbfa194c8000b78ba3d64bc0195b530fe173000000000352bb372001dd99745226cefb227dca815a0fc29e86d018325be9b5780d80006b9472c00009110fb5849ccd93513f1daf419cba4222d29f8800000001bd0007440011b27f00000000000000440482176ce000001a0000d90001e70002a800316666000002fb69cf35a408c4b866c060406c6094b932670c589f80b3636a44138006e2084388d0134af975000000000dbaac6f0650092d93eae480000031e2d000000390a35619ac73440800000000c79ceab640ae95ce1063aa9e542986524b19b63175ce00081b9e276c2cd9b470ce37c2cacd720410d291c1b6a65be1fc1885105e955474841009e80d63ac6e002602e24fc3de000000000e0612fb41e800000424568006580fdd72f12d2abd4e13c5745f8f686977e000000a74a674d113c80002f0652ce0000017f3c20969f1413ab4404001f3f30289b80026033e8bded800624dc8b206661ee5044a343ae3a40018e000000000000003d08c29b01ecbc00154038cc583ae925c88c1600046249d07329298b48399d846a0a86a23f2c05a00684a6b80e5e3800182f9cdb3951e600000247000000c08000002205100000000000286516b5800398000f91a9aa31061e9aa8002f01d0199520502bc2eaa44f400171226104905a49a316ce5dd79384ae0009832d24a6ec3f00034e001cb3ac0000645b800122c4000000000669e5bdc2a2930e93467b23f57b8002468f1678ee000000001285c0b25090000008580034b0000003ea4f678001b0afc18a000f80da57800000254000141001bd7720013423711ef3ca499554efd55b84e000fa43c21d394001e48003b4000391211ba1b4f1ba13c8c20000007786c08b2da566f181180033a845b98b93706f8cb0002b40015505a71c001cda5f00051c7a8013d40017d000456835b70006e8404761452147e8ee0006d2000000e1000001531246b4a500015d000bc8360e4500d5c8fb6853a3bc0026c16452d508006cc4684e0a3618338002dd160b455c00026c4b4f095619673800165442a5402000000e01c1800000000f49ba000c54d50004ce5b449800526598001130c0001ee94e680000f2a70342a0d7b35f63a0b4bc800000000001f66a2b28649084920004b80074c0008b80e38227d2dbd7244730a83324ca0012cad8000bbc0006358aed93d8004c20
  | 5 => 0x123b33de0bd8e15e67ad59399b2022a1d7f90f10c780f9ba3290a20868220900299c28444a2a0ab84c0000c17297634c1bc7b1cb7086f1310c3604ad4000007c00011400064800000000722104fc8f0216dc10d0000003dc00132000621bb0e20367ecd117000a8f8000001624e4001af10a001d3a08252001801dd38e0009b800000b40000000fe33000000170238b1b2e3486440032769a7c4902c10100001a2b920a001da8005c85c4d68005c20012aaf4316c648db3e2b8a5c3b360596e09908532d6b08e299205cf4800000352920e00004e45040a8007c2001d4064472f983d9350000dc00000000001e71993cc074d88100aed140021341e154728003b2e15558001f2261a180055c4ac0000057a1714b1f76f600113942000dac0000055000103a4627ad794f8fa000808da9d6000001c40000000013b1340dcfc91618c000cadfb8006fc1e52d0681b222c640005ae151f40003202350f22e0000000013155a861aa1db356be4003c003e9a40000700019400062702000000000000002901a000001a100033c0000018d000000b611d4a25f0ef2bf1848ed3880001641c003b16da001940005b60ac00140626ca9d500908cd30f716123c001f58a4152850e78000009f473b1a000001e600017c2ec0000012aed1ec0ac266000130005bc00131800000fd0ba0610009e0e1bbd07800154a0a7c6348c2000000001212150000000000000057c7890e0e00002297b000d7400112000000001ff312178420006066fc408993a88f5e0bbe062001a928975200000000000018532eb7ca000001590007080036a3a2be00000000021dbba330000007530a0001dc000007a25612eb0600013dd93c47ec001bc94d52
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xc40842b56110210c7d52308431c548c210b5586308431f540c210c715030842d5610c210f808620842f06148210f8c85208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414425e65cc510c7d53314431c54cc510d3d4b314434c52cc510b6983314425c654c510c7d51314431c544c510d3d49314434c524c510e550531442d8604c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110da14a20442786548110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410425d65cc410c7953310431d54cc410d394b310434d52cc41097d95310431e544c410c7551310434e524c410d3549310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400425f658c01097596300431e548c010c7552300434e528c010d354a30042d5618c01097d94300425d650c010c7950300431d540c010d3948300434d520c010b55843004398400c0109e596100436952840109dd9510042e462440109ed9510043695244010
  | 1 => 0x8398400c2208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534825d6114d20cdd53514833454d4520d5d4f514835453d4520cdd93514833464d4520d5d8f514835463d45208f990514823d64145209798c514825d6314520cdd5051483345414520d5d4c51483545314520cd99051483356414520d598c51483556314520dc580514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414825e65cc52097197314831f54cc520c7153314835751cc520d5147314825e654c52097195314831f544c520c71513148357514c520d5145314826e65c8520d9147214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd444048334511012097996304831f548c120c71523048357518c120d5146304825e650c120c7d50304831c540c120d5d443048354510c120e61003048364518812097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208f992510823d64944209798e510825d6394420cd94541083355150420ae1814108356514c420d554531082d8604c4209b59621082e960084209bd9520082e46148020ea10120083c830480209ed95200825e63d53109758f54c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c431e5350710c754d41c431e54cc710c755331c431e544c710c755131c4395414c710c794e40c431d5390310c794c40c431d5310310c795230c431d548c310c795030c431d540c310e610030c433561d5210ce983548425e63952109758e548425f63552109718d54843356115210ce980548431f54d4e10c7153538435561d4e10d6983538423e6494e108f592538423f6454e108f191538431f5414e10c715053843556114e10d6980538423e6494a108f592528425e6394a109758e528423f6454a108f191528425f6354a109718d528431f53d0610c714f41842ba60d0610c7d4d418431c5350610ae181418431f54cc610c715331842da60cc610c7d51318431c544c610b618131842f16008610c7d4e408431c5390210ad586408431f5310210c714
  | 2 => 0x605063097994418c25d651063097996218c25d6588630a7992218c29d648863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a7586408c31d5190230a7584408c31d5110230e6980408c23d61d51308f992544c25d639513097d8d544c23e65151308f584544c23e64145308f590514c23e65d05308f197414c23e65505308f195414c25e65cc530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23f64548308f191520c29f644c830a7191320c29e640c830a7590320c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c35551cc43097596310c29e648c430a7592310c29e640c430a7590310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29f6454830a7191520c29e6414830a7590520c34d5214830b5984520c2d56114830b6980520c2da6090830b6582420c25f655083097195420c25e651083097594420c2da60d4430a7992510c29d6494430a7990510c29d6414430b3988510c2cd6214430b6980510c31d51d0430a7983410c25e659043097596410c29d6490430d5546410c3555150430b6d81410c2d86050430e5d85410c3965150430c7545410c3955150430c5545410c39b6050430a7181410c3986050430a6181410c25e651043097594410c29e641043097996210c25d6588430a7992210c29d6488430d5546210c3555148430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d06500c31d4194030d6982500c39b4194030e6506500c25d65d0030a7586400c31d5190030a7982400c31e5090030e6942400c25f6550030a7584400c31d5110030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53208f58654c823f61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209758653c831e5454f20c755153c825f6154f208f99053c823d6414f208f99251c823d64947209798e51c825d63947208fd9741c823d65d0720c794f41c831d53d07208fd9541c823d6550720c794d41c831d5350720ae18141c825f65cc7209759731c831e54cc720c755331c825f654c7209759531c831e544c720c755131c82d8604c720c794e40c831d5390320c794c40c831d5310320c795230c831d548c320c795030c831d540c3209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992518823d64946209798e518825d6394620ba580218
  | 3 => 0xe40c7d4e53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f59432902ba60d4640a798e519029d6394640a798c519029d6314640ab98851902ad6214640ae980519031d51cc640a7983319023e658c6408f5963190397614c640c7545319029c604c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d6508640a798c219029d6308640ae98021902b9600864097587535025d6114d409798c515025d63145408f997415031f53d0540c714f415031f5350540c714d4150337515054097997315025c65cc54097995315025c654c540c7d4e405031c5390140c754c431025f63548409718d521029f6350840a718d421029e6310840a758c421032d52108409798e511025d6394440cd547411023d6590440a798e411029d6390440a798c411029d6310440d59453110355514c440b6181311029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029f6354840a718d521029e6314840a758c521032d5214840ad98452102b56114840ae98052102ba608c840ae582321023f654c8408f195321023e650c8408f59432102ba60d4440a798e511029d6394440a798c511029d6314440ab98851102ad6214440ae980511031d51cc440a7983311023e658c4408f596311029d638c440cd5463110335514c440aed8131102b8604c440e5d853110396514c440c75453110395514c440c5545311039b604c440a71813110398604c440a6181311023e650c4408f594311029e630c4408f996211023d6588440a798e211029d6388440cd54621103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cc6501031d3194040ce982501039b3194040e64c6501023d61953308fd8554cc23e64947308f59251cc23f65d07308f59741cc23f65507308f59541cc2b86050730c795331cc31d54cc730d554731cc31e544c730c755131cc26e62d52309b58b548c31e5450e30c7d50438c23e6494a308f592528c29f644ca30a7191328c34e524ca30a7990328c29d640ca308f992518c23d6494630a7992318c29d648c630d5545318c29e640c630a7590318c29e64cc230a7593308c2ce62d5230b358b548c2da60d5230c7d52548c2da6015230a7993528c29d64d4a30b6983528c29e6494a30a7592528c34f5294a30b6980528c25f6550a3097195428c25e6510a3097594428c2da60d4630a7992518c29d6494630a7990518c29d6414630b3988518c2cd6214630b6980518c31d51d0630a7983418c25e659063097596418c3976150630c7545418c29c
  | 4 => 0x7590524c74d5214931b5987424c6d561d093197d95424c65c655093197994424c65d6510931e5d47414c69e60d053197996414c69d6490531e5d85414c7975150531a7181414c65e6510531a7990414c69e64d4131a7593504c69f6454131a7191504c6cf6254131b3189504c71f4114131c7504504c65e63d50318f596540c63e60950318f181540c63e64150319798c540c63e64944318f592510c63d65d0431c794f410c63f6550431c794d410c71e54cc431c7553310c65f654c431c7951310c71d544c4319dd95310c756534c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21e550531c863f64543218f19150c865f63543219718d50c865e63d52219758f548863e60952218f181548865e63152219758c548863e64d4e218f593538871e5494e21c7552538865e6094e21c7951538871d5454e2197181538863e6414e218f590538871e53d0621c754f418871e5350621c754d418871e54cc621c7553318871e544c621c7551318863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64944218f592510865e63944219758e510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410865d65cc421c7953310871d54cc42197d95310871e544c421c75513108795414c4219bd9521087a54148421f14c521086776548421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0650087394194021d6cc6500875931940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0550087394154021d6cc550087593154021dac85500876921540219758653d025f6154f409798e51d025d6394740c794f41d031d53d0740cd54741d031e5350740c754d41d025f65cc7409759731d025f654c7409759531d02d8604c740c794d439025e6394a409758e529029f6350a40a718d429032e5250a40a798c429029d6310a409798e519025d6394640a798e419029d6390640cd545419029e6310640a758c419029e63d0240a758f40902ae62d4e40ab58b53902ba60d4
  | 5 => 0x51cca3f64543328f19150cca7a60d52329e583548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca5f63551328f994544cb1d63151328f584544ca3e601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540ca3f61550328f181540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065f6354b419718d52d069f6350b41a718d42d069e6310b41a758c42d072d5210b4197d8d50d065c6354341ad58753d071d5314f41ab98853d06ad6214f41ad58453d06b561d4b41a7d8d52d069c6354b41a798c52d069d6314b41cb54852d06b56114b418fd9532d063c654cb418f99432d063d650cb41a798f50d069d63d4341ab98b50d06ad62d4341a7d8d50d069c635434197982539065c6054e41c794f419071d53d064197d8d509065c6354241c714d435065e63149419758c525069f6350941a718d425072c5250941a798c425069d6310941a798e415069d63905419798f505065d63d4141ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d5214941ad98732506b561cc9418fd95325063c654c9418f994325063d650c941a798f505069d63d4141a7d8d505069c6354141abd8950506ac625414197982531065c6054c41c794f411071d53d04418fd95411071e5350441c754d41106776550441cd951411065f63540419718d501066e62153319b58854cc71c5450f31c755043cc63f6454b318f19152cc69f644cb31a719132cc69e640cb31a759032cc74d520cb318fd9150cc63c6454331b558754cc71d5415331b398854cc6cd6215331b558454cc6d561d4b31a7d9152cc69c6454b31a799052cc69d6414b31d354852cc6d56114b3197d9542cc65c6550b319799442cc65d6510b31a798341cc7976150731a718141cc69e64d4331a759350cc6ce62d4331b358b50cc71f4194331c750650cc69f6454331a719150cc63e60952318f181548c71e54cc631c7553318c63f64542318f191508c66f62551319b189544c67b60551319e181544c65e65d0d3197195434c71c5450d31c7550434c63e64149318f590524c69f644c931a7191324c74c524c931a7990324c69d640c931a7992314c69d648c5318f993504c63d64d4131b5586544c6cf6255131b3189544c6d76155131b6d81544c6d86055131c7550544c6d56194931a7d91524c69c6454931b5d85524c6db6054931b6181524c69e6414931a
  | 6 => 0xbb05294407709825601924c83ba9ea5f8501f508d03f8ed24e19e000247a018bf0001758da8f921e296926892139a0110106e0299d0a721f70001c217414c11c19d24117a1b31cc82e8ab9918b30a70348cf00e8b79bf07b0ef2919fa8e7107000123a69165259a11a14a2f93309e00000e21b00000000000000014112f00014011e80010b0fb25784400ca7405522783700005f1c894e0001b620e0001a600000980000380300000813806000058000070180000700c0160680681100a00400002002000008000180000f00105a0040080b00a0000100003000c0980900e020000020060000000200200c0182a0000000100801c0000800d008074008210100440000000a010000210100440980000203000801000000000000080040300100000000801000080010000020000000800e00006800014014028060060080b818002008068070020000581301200000002008000010010000180482800600c0181f02001c060040000000180001c00408807000064000030020140000100600401003022000020000060080501600001c0580c0000100380f000074020160080000080000c07c0780500e024020000080040a85a00000c000010020001280d002018000050060040583500c0400080001e01c000000220300100000c000010020000140180003a00001800002000000000460001000800004c0000001c100008010020340b80b01a01c0a00001800810026010000200030000240580904a0000680103e0240500604200c008110220240480800000c0f00200403c0b0030000000480b006018000070020940486500000c060050080400780f00a048038020260000000e01000c00007004064068350140000080400001400029002000078010080000180000e038028020020280600a02c004058000100040480f024010000020020bc088030060100a80600001405000042000000000340002400a00a0300001900601c0600403204c0200700004402016044000008100120100600b0000000304902405c018000700ac060080000100300a0000000200500000c0b00a00002c040240460540500000c01e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750d5110f1d43940439798e51d0a5d639474297d8d50d0a5c63543429798e5190a5d639464297d8d5090a5c6354242975875350a5e60d4d42975845350a5e6014d428f9974350b1c53d0d42c714d4350b1c53909429798c5150a5d63145429798f5050a5d63d4142975865310a5e6094c4297d855310a5c6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98454cca756115332c715143cca3e64947328f592
  | 7 => 0x582f8f40000ca0e08d30992900ba0000750a20050581f61b789883e18020e83a00007599300027600005680004c98699b8a10000ba9688000000000001b11780d09079c300606c0df171958a398ca80027894a85215f29f0970000ef8c023e0ad0a6a1900018b9e822325197d8000001059ad00001f80000026b0000000b880005383180000000027d0000a80b49f01ef05082d9bd04c02498d99c04f24f80013400016f83c0c290c0000118ad8690e295b92e00029d1971170001f48002259eda500fd8d4200a031c006e800086146a4e93880000028b12329a8cd0b581a0a31790000002522749ee169263a429179ada709fd80027ea37a5421092114815489b29fa85865a5aa9d9ab0ac159a1b8000449841181b88d980020825d2908000000002128001ea24d125157a840c40670bc1d51b29fe09fa490330e520898790a17f286a218e80fb9aa0fc8d58738d686320c0a428312c8f38d91df8000000d18c5802859a5380580000486515e1a89daa83a498638000e182c28188f840a0926423927b0c70b709410622480002b8ec937a028000fa8378e602025b8000499f11a4a2a0a99762728f291218080003206d878a960510561b9124246000151929860a860001bba34021a5e8f51679568af8eb16d0c78350000001610689b218200008c8002970001ab8000000b02701c507c14d8368f61e519908389180002f0468001ec92d8000001839038b29798ed9921de1a10fea059291e40df8491e3a8c27900001993808714b82880003d9f39d319600022290c90e8f1a9b1391d58fd1de8cb0540002990530001540251631d38959d79528001338000800179360f7a510ab10205919aa8a9ae8a1a3d9eba879109af90e0ae80721c83d0ee9d284610802609782a1698d3a068999e91a82201eea0001b8e22572150359888db0e304597d1229f989319396b0b913f94b13e00001515caa022902b01499fa3c1f922e98e90b8b40f5a7f00023024d9119369b995612883b0810ce97c11b11a0c8974a3700200b25d9c29e00518721db8e926c89ca930de07823c97b1fa0212220209c39478cfa76806a93a4392e85e998a2728821f86626e890a5502c8b622f18c1da02427317a93017513e8cca332318ec2448790610000439498ac80024899a00315700000021783a99c8f88c908ba528399d18002660000bb250a2b062a28a6b8000471cf22c1e2905165a4c000245a9c94f06b95a00000022800018492a9d88001d40000000078000579328001d20000000001ef8bda12279800254a8ea3d0258402240001a5a189f28431131d000003607c9a300007a9bc80000014618b0000d798a1491e680022aa1d1c81ff0001280002530000ee24b11896a2888be98e2940dc962a4a29b90f8128000000aa22998d15a8038001710488b19b08d495d9358769
  | 8 => 0x9500000000000018f80001d80000020d80017300000000000023689d13d1d81f419281a8ff08b177a7da590c49e58c21be00008f19f1b815113a19488889c1fca0d20413f0001fb8000000ff8002079e7a2693b11f91b8d8a6a8d11101019279be8000c509697388280009a9c101c034000000041800038000215a9295b000119000000081a40a7a9041cb02701000000004b96b80d0000000000db8001a500003001600015c0000001e1a6080000414a1978000000a2a8c800258800000000116a8f00029c0e11b384a8000a91ca9429e11bda6807d911232800026a829af16a8b12810a01a39ec1b699b05a8000d60820001ae275a650680001b49a91c726a25a27126001114d2669bf9270a78840719d61a29f80001539fc018a7811517e12b85d8b6a35001a8025c8000a0a6885b26f90990a8000710000001cc20b27c0a480002e00000008a91c828000231294960a671900f680012d00005c8392952892141fe83e8f104522d28e2820ea808887a440570cb8cc1b516f15ea0600000000020394328524f19107fa998001c402314f8f000018108c0a3a0506c950a3f81800c1488000000000001031f0a5b21a88a12580000000007b81f15221a13c03294c9700cd8f726f0f201d03c91d8949f5a4b9a981394e99da97a171e32381998548ae131a180aa89b84f99513484e2070679aa9b4016a3b17281585a19417fa62a138e98000ea16d86a9ac2958000008000000a583f00019584d00019e8d21eb1311969a422500b8000001260b808585b87406f8f48901ca1dc0000dc0001fd00004215596492b21da7f9619bc06481e11f00d9530b39128bc889241a679d928d1708222559d9a469141c4a7a01e9f898288d92c1158c81048709449641cd9871350bfa0f94515f87d2699c08bd1421b020201086b1d4a239b59f307a064093a0f074a0a1c9a3a0dd26e18911d1a7a5e11e0d817e8eba1123f15d0000090fe2480001df114a3391a82900805f966a9e000041089800023a8a24200000027713c8f300000006200000000023b84b0e69a096e0000d51b701c9860b08d2a8fa71a0a8000002899ce0000bb97707324a80000000f8dd80023aa359981e8a5680021982a9fb0140130a5106a401671a722e02d16c92a1ce913a98a2c8000fa1ba96217b8c38c109d87f28d9a188508489f1d10010e386a17c93da8093a9409f78e7a431dca618000c19a21e49e9a471e607289a287100a648f80f095921c066a8b8e496e9d6a9825c05c1dd1db1831219680be14580f04a000238a101dd800061a3e9639201cb89e8831ea886a2d8928961f20278fc15006f00008805e11622603387e9c905d155077842a611600170000e88a62450b9a7b9000308478000000e58000001370001c793b9ba00a0001d7204800265a0b8b5209a160ce1e0879a3098
  | 9 => 0x1c59a018f00006010d8001818000000000002922630af18aa322211ac8d70001899c1a5f0e40c326c23607604d90890290d18521306d1661ed0c69f18de8000000001221090e0190920a7525820c8c080005888ea6d80017680026d0310000c980000007e0000000a881b14180005598c9720c60b2069a621f6a7c9c60000000701b1a20a9a21e88e12480000000000027e10f29128492fa778121cfa73a2b9cd14396c2348d00001a68001c695800000002289114721f0da1309321ff8809789199e70f998803884804ea1680000a8001e2000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2e5ca63416ce5a8c12001c002a0002c81e00500082c000de627ab8a860004e0842be3800aa24a200c4005e68889800267e00704cc2d60048000eb24a007cb46a00dc8a00a46cba3c00d072b6305256000000a00cd818009646ae0000069c0000c690580094003a0a14d464da04108600cc4400003eb0768474282240782000328ed21a6e9e80000000000036ac92549acabc2c66000b030601000801040c0d040000000000000012000e0c00050000080100040e0504380003a2ee2a1aa221d187050e5010e8ab88a8a1e65469c35410e32838ecaa2641960d6354842d0706a9ac429e838358d5214b41c18c629284a0d0c7254c535068c382a629a83255c66314941a18e6a90a4a0d2870548525061c382ca19283435c85450f31c1ac8a906598e0d5458854cc706b22a429663431c95410d31a30e0aa08698e0c64149324c686392a82a263461c1541513192ae3320a498d0c74548524c6a4382a429263161c16510931a30e0a08a098f11414c55008790a0a42a8043d04c52154021a2ae329a83a060c639494290287396a729c81439cf5294a40c1ac6a908420651511813110306a9ac4298818554d6114c40934e1b1aa42060d635485210312a92c2290810d5c4654c840930e0b1ca220631511813110388a8ec09888185544604c440e22a2302622069251181311030ca88c098881a4544604c440c22a230262204987058e211030ab1aa310881455c6544c730a1ce5aa0871860c64949328c287396a92a461439d35294a30a1ae42a2861851571151430c306b22a4190618c5446050430c1aa8b10a81861554584540c24d386c8a9061835915214830c8aa4b08a41845571195420c24c382c928861945446050430e22a3b02821861551181410c388a88c0a0861a49446050430c32a2302821869151181410c308a88c0a0861261c16488430c2ac8a8c421861561544400c28ab8ca6a0e418694c6050720a2ae32a2639061a5418131c83882888018241a81844048020d80c2182401061853181418430c2a0c098c2185d4d6110210c2ea8b0861084e276c85208430c298c0a0a218a1486050510a28eaa0a62886146550531443822928298a21641c1414c510c30a83026288648521813144348a08c098a218554d6110010c4aa4b088008615545843004322a92c218021465d4400c010c32ca20060087095210030042c8b888018021a4584400c010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8000a00804019c890180002a108058d5188440a10805915188430a118194c6050720a1181950604c720d00521c1414c510e0052504604c510c11655c4400c010d01525c4400c010c1175584400c010e0152584400c010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => packedAt s3K6 (880+((h/16+packedAt s3K6 (768+(h % 16)*7) 7) % 69)*7) 7
  | 5 => packedAt s3K5 (31188+((h/339+packedAt s3K5 (27459+(h % 339)*11) 11) % 1343)*11) 11
  | 4 => packedAt s3K4 (56038+((h/448+packedAt s3K4 (51110+(h % 448)*11) 11) % 1615)*12) 12
  | 3 => packedAt s3K3 (5784+((h/37+packedAt s3K3 (5488+(h % 37)*8) 8) % 148)*8) 8
  | 2 => packedAt s3K2 (612+((h/3+packedAt s3K2 (600+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 2 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x210c08c42890400165098044c022425818d1b1
  | 1 => 0x44109102412221280a422429121494a1422446
  | 2 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8eaeae8e8e8e8c8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36697
namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x500262a000008833a561c00bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x68808ea98852c525065ca5205554430
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 2 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 3 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 1 => 0x10891048252442502a11214921422528a22486
  | 2 => 0x895229034a480ca58426541654054a85454b18
  | 3 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeae8eae8eac8eac8eae8eae8eac8eac8eae8eae8eac8eac8eae8eae8eac8eac8eae8eae8eac8eac8eae8eae8eac8eac8eae8eae8eac8eac8eae8eae8eac8eac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36697
namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x302c000148248506500e0060bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x22c008ea98852c525065ca5205554430
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (208+((h/4+packedAt s5K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s5K3 (111+((h/1+packedAt s5K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 2 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 3 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 4 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 1 => 0x10891048252442502a11214921422528a22486
  | 2 => 0x895229034a480ca58426541654054a85454b18
  | 3 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 4 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8eae8eac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36697
namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x210058018c300c831c3b38d8401027a0007800020026b83f2a0c9242843a8a01b8000b800200000472c3260029400241d49a5544025806a6643c660222861513187cd8d2a00000000000000011830e06085010000102140008e0214000000401fe54007f55001fc54017fd0c05fe43017f50c05fc43007fd0803fe42007f50803fc42017fcc803fe32017f4c803fc32007fd0401fe41007f50401fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc21007fd0001fe40007f50001fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2006bf58e10037f8c70800afc638400dffa1c2006ff90e10037fa870801bfc4384001ffb142000bfd8a10057fcc508006fe6284001feb142000bf58a10057f8c508006fc6284001ffa14200aff90a10007fa850802bfc428400dff994200aff8ca10037fa650802bfc32840137eb0c2000ffd061001ffc8308003fd4184007fe20c2006ffcc61001ffc630801bfd3184007fe18c200affc861001ffc4308003fd2184007fe10c2003bf98210007fe8108003fe4084001fea042000ff10210037fe610801bfe308400dfe9842006ff0c210057fe4108003fe2084001fd1042000ff48210007f2410802bfc2084007ff8842000fdc421001ff62108003ff64440017fb222000efd91100057ec888003fe644400f7f3222000ff59110005fac888003fc644400f7e3222000ef1911000578c888003fe5444001feaa22000ff1511004ffec688026ff6344001efb1a2000b7d8d1004ffcc68800afe6344013feb1a2009bf58d1004ff8c68800afc6344013ee31a2002b718d1004ffe8688027fe4344013fea1a2009ff10d10007fec488002ff6244001f7b122000bbd8910047fcc488006fe6244001feb122000bf58910047f8c488006fc6244001f63122001bb18910007fe8488023fe4244001fea122008ff1091004ffe6488023fe3244013fe9922008ff0c910007fe828800ffe4144001fea0a2003ff1051004ffe628800ffe3144013fb18a2009ff4c51004fea628800ffc3144011ff90a2003ff88510007fa428800ffc2144001ffa022000ff90110007fa8088003fc4044013ff9822009ff8c11004ffa6088027fc3044011ff9022000ff88110007f44088003fd2044001fc9022008ff0811001ffe208800ffb1044001ff0822000fd8411001ffec80800eff6404007ff3202007bf9901001f7cc808002be6404007feb202000bf5901001f7ac808002bd6404007fe3202003bf19010007fca808003fd5404001fe2a02003ffd8c1001dfec60800ffe63040057f3182003f798c10015bcc60800ffd630400b7eb182003f758c10005bac60800ffc63040077e3182005ffd0c1002ffc8608017fd430400bfe2182003ffd881001dfec40800ffe62040037f3102003fb9881000ddcc40800ffd62040017eb102003fb58810005dac40800ffc62040077e3102000ffd0810027fc8408003fd4204009fe2102005ffcc810027fc6408017fd3204009fe1902003bf9841001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410035fcc008003ff4004001ff2002000ff50010007f88008017ff300400bff1802005ff4c01002ff86008013ff2004001ff1002000ff48010027f8400800fff1004007fb8802003ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3fe3010021fe9808010ff0c04007ffe402003ffc2010001ffb244000bfd9220007fcc91001efe6488001feb244000bf59220007f8c91001efc6488001ff2a44000ff55220007f8a91003bff638801d7fb1c400eff98e20015fcc71003bfd638801d7eb1c400eff18e20015f8c71003bff438801dff21c400eff50e20077f88710006fd6288003ffa144001ff90a2000ffa8510007fc4288003ff9944001ff8ca2000ffa6510007fc3288001ffb0c4000ff9862001dfcc310003fd61880017eb0c4000ff18620007fe8310003fe4188001fea0c4000ff10620077fe631003bfe318801dfe98c400eff0c62000ffe4310007fe2188001f710c4001ff4862000ff84310007ec21880037f3044000ffd0220007fc8110003fd4088001fe204400effcc220077fc611003bfd308801dfe1844001ffc822000fde4110007fb2088003fe1044001fe08220007fec890002ff6448001ff3224007bf99120007fac890002fd6448001fe3224007bf19120007fca890003fd5448001fe2a2400dffd8d2006dfec690037fe63480057f31a400dff58d2006dfac690037fc63480057e31a400dffd0d2006ffc8690037fd434801bfe21a4001bfd892000ffe8490007fe4248003fea124001ff1092000ffe6490007fe3248003f71924001ff4c92006fda6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4003bf18520007fe8290003fe4148001fea0a4000ff1052006ffe6290037fe314801bfe98a400dff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024000ffd0120007fc8090003fd4048001fe202400dffcc12006ffc6090037fd304801bfe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048007ffb262003bfd931001ffcc98801efe64c4007feb262000bf5931001ff8c98800efc64c4001ff2a62000ff55310007f8a98800fff63c40077fb1e2003ff98f10015fcc78800ffd63c40197eb1e2003ff18f1001df8c788033ff43c4019ff21e200cff50f10067f8878800fff62c40077fb162003ff98b1000dfcc58800ffd62c40017eb162003ff18b1001df8c588003ff42c4017ff2162000ff50b1005ff88588033ff32c4017ff196200cff4cb1005ff8658800fff41c4007ff20e2003ff5071001ff8838800fff31c4007ff18e2003fd8c71001ffa6388033f531c4007fe18e2003ffc871001ffc438800ffd21c4007fe10e2000ffd0310007fc8188003fd40c4001fe206200cffcc310067fc6188033fd30c4019fe186200bffc8310007fc4188003fd20c4017fe1062000ffd9210005fec908003fe648400f7f3242000ff59210005fac908003fc648400f7e3242000ff95210007faa908003fc548400dffb1c2006bfd8e10037fcc70800afe638400dfeb
  | 2 => 0x40007fec320003fe61900077f30c8000ff58640005fac320003fc6190001ffa8c8000ff94640007faa320003fc519000fffa0c8000ff906400077c8320003fd419000ffe20c8000ef1064008ffe6320047fe3190023fe98c8011ff0c6400affe4320003fe2190001fe90c8015ff0864003dfcc120003ff5090001ff2848007ffd02400077e812001ffb4090023ff9848011ff8c24008ffa6120047fc309002bff9048015ff08240007fecaa0002ff6550001bfb2a80009fd9540007fccaa004afe6550001feb2a8000bf59540007f8caa004afc6550001be32a80009f19540007fea8a001ffe5450001feaa28007ff151400a7fec6a0052ff6350001efb1a8000b7d8d400a7fcc6a000afe6350029feb1a8014bf58d400a7f8c6a000afc6350029ee31a8002b718d400a7fea6a0053fe5350029fea9a8014ff14d4003ffe86a0053bf4350029ff21a8014ff50d400a77a86a001ffc4350001ffb128000bfd894009ffcc4a0006fe6250001feb128013ff1894000df8c4a0003ff5250027ff2928000ff5494009ff8a4a001fff4250027ff2128000ff5094003ff884a0053ff3250027ff1928014ff4c94009ff864a0003ff61500017fb0a8000ff98540007fac2a0003fc61500077e30a8000ffd4540007fca2a0003fd5150001fe28a8007ffd05400077e82a0003fe4150001fea0a8000ef5054003ff882a0053ff3150029ff18a8014ff4c5400a7f862a004fff2150001ff10a8000ff4854009ff842a0003ff5050001ff2828000ff5414003ffe80a001ffb4050001ff2028000ef901400a7fe60a0053fe3050029fe9828014ff0c14009ffe40a004ffc205000fffb288007bfd944003ffcca2004afe651000ffeb288000bf5944003ff8ca2001efc651000f7f3208007ffd50400077ea82001ffe541000ffeaa08007ff1504003f78a82001fff631000f7fb188007ff98c40015fcc62001ffd63100217eb188007ff18c40015f8c620043ff5310021ff2988010ff54c40087f8a62001fff431000fff2188010ef90c4003ffa862001ffc431000fde2188007ffd884003ffcc420006fe621000ffeb108000bf5884003ff8c420006fc6210001ffa90800fff94840007faa42003ffc521000fffa108007efd084003ffc842001ffd4210001dea108007ff10840087fe642003ffe3210021fe990800fff0c84003ffec22001ffe61100077f3088007ff58440005fac22001ffc6110001ffa888000ff94440007faa220003fc511000fffa088007ff904400077c822001ffd411000ffe2088007ef10440087fe6220043fe3110021fe9888010ff0c44007ffe4220003fe2110001fe908800fff0844008dfcc020003ff5010001ff2808000ff54040007f8a02001fff401000fdfa008007ff9004003ff4802001ffd4010001dea008007fe50040087fe602004
  | 3 => 0x69944201ff0ca2101dfcc31080fff4188407ff20c4203ff5062101ff8831080fff3188407ff18c4203ff4c62101ff8631080fff2188407f790c4201fdc862101ff8431080ff42188407ffb044203ff98221005fcc11080ffd60884017eb044203ff182210cffe6110867fe3088433fe9844219ff0c22100ffe4110807fc2088403f61044200ffd9121005fec890803fe644840f7f3224200ff59121005fac890803fc644840f7e3224200ff95121007faa890803fc5448431ffb1a4218bfd8d210c7fcc69080afe6348431feb1a4218bf58d210c7f8c69080afc6348431ffa1a4218ff90d210c7fa8690863fc43484077fb124201ffd092100ffc8490807fd4248403fe2124201ffcc92100ffc6490807fd3248403fe1924201bfd8521007fe829080ffe4148401fea0a4203ff105210c7fe629080ffe3148431fe98a4203ff0c52100ffe4290807f72148407ff10a4203fb8852101ff8429080fec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121005f8c090863ff3048431ff1824218ff4c1210c7f86090807ff2048403f79024201ff0812103ffecba001ffe65d00257f32e8007ff59740005facba001ffc65d000f7e32e8007ffd534003ffca9a001ffd54d000ffe2a68007ffd8f4003dfec7a001ffe63d00057f31e8007ff58f400bdfac7a001ffc63d00057e31e8017ffd4f400bffca7a005ffd53d002ffe29e8007ffd0f4003f7e87a001ffe43d000ffea1e8017ef50f4003ff887a001fff62d000fff3168001bf98b4003ffac5a0002fd62d000ffe3168001bf18b40007fea5a005bfe52d0001fea968016ff14b4003ffe85a001ffe42d000ffea168007ff10b400bffe65a005bfe32d002ffe9968016ff0cb4003ffec3a001ffe61d00077f30e8007ff58740005fac3a001ffc61d0001ffa8e8000ff94740007faa3a0003fc51d000fffa0e8007efd074003ffc83a001ffd41d0001dea0e8007ff107400bffe63a005ffe31d002ffe98e8017ff0c7400b7fe43a0003fe21d0001fe90e8016ff08740007fea1a005fff30d002fff1868017ff4c3400bff861a005bff20d002dfe1068000ffd9640005fecb20003fe65900257f32c8000ff59640005facb20003fc65900297eb248000ffd52400077ea92001ffe5490001feaa48007ff1524000778a920047ff63900237fb1c8011ff98e40015fcc720047fd63900237eb1c8011ff18e40015f8c720047ff5390023ff29c8011ff54e4008ff8a72001fff4390023ff21c8011ef90e4008ffa872001ffc4390023de21c8000ffd8a400affcc520006fe6290001feb148000bf58a400aff8c520006fc6290001ffa948015ff94a40007faa520057fc529000fffa148000efd0a400affc8520003fd4290001dea148007ff10a4008ffe6520057fe3290023fe9948015ff0ca
  | 4 => 0x87bfe4290401fea148207ff10a410fffe652087bfe329043ffe994821eff0ca4101dfcc32080fff5190407ff28c8203ffd064101f7e832081ff74190407ff98c8203ff8c64101ffa632080ffc3190407ff90c8203ff0864101ffec12080ffe60904017f3048203ff58241005fac12080ffc609043fff984821fff8c2410fffa612087ffc309043dff904821eff08241007fecaa0802ff6550401ff32a8212bf99541007facaa0802fd6550401fe32a8212bf19541007fea8a0803bf545040fff2a28200ff5514103ff8a8a0803bc545043bffb1a821dbfd8d410effcc6a080afe635043bfeb1a821dbf58d410eff8c6a080afc635043bffa9a821dff94d410effaa6a0877fc535040fffa1a821dff90d410ef7c86a0877fd435040ffe21a821def10d41007fec4a0802ff6250439ff3128201bf98941007fac4a0873fc62504037e3128200ffd49410e7fca4a0803fd5250439fe2928207ffd09410077e84a0873fe4250401fea128200ef5094103ff884a0877ff3250439ff192821dff4c9410e7f864a0803ff5150407ff28a8200ff5454103ffe82a081ff74150407ff20a8203ef905410effe62a080ffe315043bfe98a8203ff0c5410e7fe42a080ffc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028200bf181410effe60a0877fe305043bfe982821dff0c1410e7fe40a0873fc2050407ffb288203bfd944101ffcca2084afe6510407feb288200bf5944101ff8ca2080efc651040f7f3208207ffd504103ffca82081ffd541040ffe2a08203ffd8c4101dfec62080ffe63104057f3188203ff58c410ddfac62080ffc63104077e318821bffd4c410dffca62086ffd5310437fe2988207ffd0c4103f7e862081ffe431040ffea18821bef50c4103ff8862080fff6210407ff3108201bf9884101ffac420802fd6210407fe3108203bf18841007fea42086bfe5210401fea90821aff1484103ffe842081ffe421040ffea108207ff108410dffe642086bfe3210437fe990821aff0c84101dfcc22080fff5110407ff2888203ff5444101ff8a22080fff4110407dfa088203ff9044101fec822080ffd4110407dea088207fd5044101ffe622080ffe3110407fe9888203ff0c44101ffe422080ffc2110407ffb008203ff98041005fcc02080ffd60104017eb008203ff180410dffe602086ffe3010437fe980821bff0c0410d7fe402086bfc2010407ffb244203bfd922101ffcc91081efe6488407feb244200bf5922101ff8c91080efc6488401ff2a44200ff55221007f8a91080fff63884077fb1c4203ff98e21015fcc71080ffd63884337eb1c4203ff18e2101df8c710867ff4388433ff21c4219ff50e210cff88710806fd6288403ffa144201ff90a2100ffa8510807fc4288403ff9944201ff8ca2100fdc6510807fd3288433f
  | 5 => 0x874203ffcc3a100efe61d080ffeb0e8400bf5874203ff8c3a108fff31d0847ff18e8423ff4c74211ff863a1007ff21d0803fe10e8407ffd834203ffcc1a1002fe60d080ffeb068400bf5834203ff8c1a108fff30d0847ff1868423ff4c34211ff861a1007ff20d0803fe1068400ffd9542005fecaa10037f65508013fb2a8400ff99542095fccaa1003fd65508017eb2a8400ff19542095f8caa10037c65508013e32a8401bfd9142007fea8a101ffe5450801df2a28400ff551420077aa8a101ffc5450845ffb1a8422bfd8d42117fcc6a100afe6350845feb1a8422bf58d42117f8c6a100afc6350845ffa9a8422ff94d42117faa6a108bfc535080fffa1a8422efd0d42117fc86a108bfd4350845dea1a8407ff10d4200dfec4a1007ff5250803ff2928401ff5494200ff8a4a1007ff425080ff7a128401ff9094200f7c84a1007fc4250803de2128401fb1094200ffe64a1007fe3250803fe9928401ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a100efc6150845ff98a8422ff8c542117fa62a108bfc3150803ff90a8401ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050845ff9828422ff8c142117fa60a108bfc3050803ff9028401ff0814203ffecba081ffe65d04257f32e8207ff59741005facba081ffc65d040f7e32e8207ffd53410077ea9a081ffe54d040ffeaa68207ff1534103f78a9a081fff63d040f7fb1e8207ff98f41015fcc7a081ffd63d04437eb1e8207ff18f41015f8c7a0887ff53d0443ff29e8221ff54f4110ff8a7a081fff43d040fff21e8221ef90f4103ffa87a081ffc43d040fde21e8207ffd8b4103ffcc5a0806fe62d040ffeb168200bf58b4103ff8c5a0806fc62d0401ffa968220ff94b41007faa5a0883fc52d040fffa168207efd0b4103ffc85a081ffd42d0401dea168207ff10b4110ffe65a0883fe32d0443fe9968220ff0cb41007fea3a0887ff31d0407ff18e8221ff4c74101ff863a0883ff21d0407fe10e8207ffd834103ffcc1a0802fe60d040ffeb068200bf5834103ff8c1a0887ff30d0443ff1868221ff4c34110ff861a0883ff20d0441fe1068203ffd964101dfecb2080ffe65904257f32c8203df99641004fccb2080ffd65904017eb2c8203df59641004facb2080ffc659043b7eb248200ffd524103ffca920803fd549040ffe2a48203ffd8e4101dfec72080ffe63904057f31c8203f798e41015bcc72080ffd639043f7eb1c8203f758e41005bac72080ffc63904077e31c821fffd4e410fffca72087ffd539043ffe29c8207ffd0e410ff7e872087ffe439043ffea1c821fef50e4103ff8872080fff6290407ff3148201bf98a4101ffac520802fd6290407fe3148203bf18a41007fea52087bfe5290401fea94821eff14a4103ffe8520
  | 6 => 0x300100400000113dfacb2a01efe649500fffaa4a812efd52540067ea92a01fff639500f7fb1ca807ff98e54015fcc72a01ffd63950537eb1ca807ff18e54015f8c72a04bff5395053bfa9ca829ff94e5414ffaa72a0a77d5395025fe29ca807ffd0e5403ffc872a01ffd439500ffe21ca807ffd8a5403ffcc52a006fe629500ffeb14a800bf58a5403ff8c52a006fc6295051ff294a828df94a54097f8a52a0a37c529500fff214a807ff10a5414ffe652a0a3fe3295053fe994a828ff0ca5403ffec32a01ffe61950077f30ca807ff58654005fac32a01ffc6195053ff98ca829ff8c65414ffa632a0a7fc3195051ff90ca828ff0865403ffec12a01ffe60950017f304a807ff58254005fac12a01ffc6095053ff984a829ff8c25414ffa612a0a7fc3095051ff904a828ff0825403ffca8aa01f7e545504fffb1aa827bfd8d5413ffcc6aa00afe635504ffeb1aa827bf58d5413ff8c6aa00afc635500fffa1aa827ff90d5413ffa86aa01ffc4355001ffb12a800bfd8954137fcc4aa006fe6255001feb12a826ff1895400df8c4aa09bfe425500ffe212a827ffcc954137fc64aa09ffd325504dfe192a800ffd8554005fec2aa003fe6155001feb0aa800ff1855401df8c2aa09fff315504fff18aa827ff4c55413ff862aa09bff215504dfe10aa800ffd8154005fec0aa003fe6055001feb02a800ff18154005f8c0aa09fff305504fff182a827ff4c15413ff860aa09bff205504dfe102a807bf9905403ffca82a01fbe541500ffeaa0a812ef550540067aa82a01fff631500f7fb18a807ff98c54015fcc62a01ffd631504b7eb18a807ff18c54015f8c62a01fff431500fdfa18a807ff90c5403ffa862a097bd431500ffe218a807ffd885403ffcc42a006fe621500ffeb10a800bf5885403ff8c42a006fc621500fff210a824ef9085403ff8842a01fbc421504bff990a824ff8c85412ffa642a093fc321500fffb08a807ff9845401dfcc22a01ffd61150017eb08a807ff1845412ffe622a097fe311504bfe988a825ff0c454127fe422a093fc211500fffb00a807ff98054005fcc02a01ffd60150017eb00a807ff1805412ffe602a097fe301504bfe980a825ff0c054127fe402a093fc201500fffb2e8407ff99742095fccba101ffd65d08017eb2e8407ff1974203df8cba1006fe64d080fffaa68407ff9534203f7ca9a101ffd54d0801deaa68407ff1534203ffec7a101eff63d080fff31e8402bf98f4203ffac7a108efd63d080ffe31e8402bf18f4211ffea7a108ffe53d0847fea9e8423ff14f4203ffe87a101fbf43d080fff21e8407ff50f4211f7a87a101ffc43d08037eb168401ffd4b4200ffca5a1007fc52d0803ff2168401ef90b4200fdc85a1007fc42d0803de2168401ffccb4200ffc65a1007fd32d0803fe1968407ffd
  | 7 => 0xe18700000000000000025302389a00063a16f0000000c8768a166cc0005068b85227ce9766f8724b0c97e5d20003924ec0000000d47fbb5c000000aba2703bc00000092800050e7da97c2fba1e0000000007056ce000ae064a67200000000000041300000900302000000000200000400000000000000000b00000000000600000000900000600000800500100000500000000000d00d00100001900400000c02101300500500100000000100700100100000100200100100000000000000600700000000000500700500401300400000003200100700000000000100700000000600000000400300000700e00100100200000200100300000000100400300000200500400100000100100200100100500000100200000800100900400200300201e00000000000100f01202500000000e00600a00200100001700800c00000200000100500800000100100d00100200300a00000400300100300500100200200000000000600700300200100100200a00300700100700200800100300c00000b00200200600300300300200100600400400000500200500000500100600000001000800200000100000100000300000300400200200100500000100200300000000500000000200100e00000000600000000800300000000b00b00100100000200700400000000400500600500000000200000400300e00500300000900100901500301200200000e01300400200200500100100301200900200801200300000000c00000500000000b00100200000200100500700500400000000400100000100000100200800400900401500300700200200100400000000200300000000000000000c00200000100000700100000000000000d00500501400000f00100100000000100401e00400200400000200100101000100300300a00201200000e01200d00300d00601000100000000200300200100400b00100701300100000200000000700000700100100100f00d00300100000200100900000200100600900300b00400100400600400200000100600100100f00600000100500200300200000100200000300300000000400001600100800400400100000200900c00000300000600900300400000000100100200000200000000000100000200000400400000800000000300200100000100d00400200100f00900900100100c00200800700100400600300200300300100c00000100001400000000400a00200000300000400400700500000000200700100100900300400000700900100100000800b00500300000500000100900000e01000800000000100000000100400002000000000400300600100100100100b00500401300800400100100000100400100000300000100b00000d00001000000800100000500300f00000000000a00000b00900a0
  | 8 => 0x1fc6de1831c658634c1b20004927c400014c398a3aa081af9a60000ee4c000086a2bb04c5303ca0f7a06a845e698961a1fe000aa2572b8635bbb28610001340006a272c000af6000000000b9755803db9cbba48a72725b45865a0c0a0000000084e025000000000000b4627332855ab0880274c420a820000005ca0005ae0ca186000a1a000bce63829a5d000059e8e40009ac000a6453e1f600033e000aab8145b607200000000000012856cadab7c1d352604abc2668a8c5479d611409b6645001da8f03d85de200b1a03a819be0840000ba0000ae22d80000000002445ee0000007c868e0000ea4360001ca9e60004ee1d1000626a480000002064281150b6974202a580000000000000e32c226451a4895a20002d41f492600055e8748be291716000a889540002c0692000138140606032bee91e2bd00093a67000000018a0000006f08fc0000009ea5ce0001490006f76a30008febcaabc40637651f00022a3351060001113db4ea604a44b6b14a0000004d2bf83e6824a420000007b211abe6000b484b60003b4857adc00000000000002c00000076c0000000002941390000005da480bd80000a3494000465b3000000000060e16c0c53dc0000000006ab0005c600000e00046677a00000000017a00069c0600007405f6540444000bf200098a000000948b740006760382d08a83a05fc0000005880007ac41a034000000000860a863cc000b1359600067d00033a24600000050547400012647e77f00022860a000aa4000212058419000000220000000554a8a2224b045a23cbc03b000002a0009c831f08238c1b600a0000e1219b3e52400000030e0b800000000055cb4c0007100002f29830009aa13238d116000199b3631600c00091444b113be451d000000000000000000000000000000000b5400000000094c00033b8a63c80005fa1362ca5f40001b800045000033200013eaf02e09d83a4000000360000b68aa50004630001cd00050335a9b08542761470004f688284a0007fe7b9a0d1040e4b969fa1d9894bf02f628800062c0002c81ef000bf686c99e000300000b3a90000052e00057440e44a90688aa2408a75aa40b765c411839a79013716613c56062489e54444960800000004682860c7be93c7b0918b2d9beb449ec00000042c8aeafebbe00000029800000004d3420008ee0001ed1c080c8702de83e895064b800005f8b886545d40005cb456b40000066000000528b644f445200032e99a39478a83a3460009c46488da7e434352a0000004dc5beac87f48c609e1242b5581af8b8131b00000036c49a0000000001aa6e80007d200000085125544825462a93805c40c000000000000000000b02c163629fe5422b81967f60008c400082c0000000003a200072239c000000000000b7d0004c9a4e00073a33f1ec8c
  | 9 => 0xda70e0000000000000000000003370004144b27232a01583de0005049a2c100004a2000a8e000816a11a4a000c0c1ce000052374000000ab80006d6000000361bc80f40000120394e81d80704786a957aa60a3891638408c00058c0002d772a0008ea0004ac00006d195117a800cc5d681e7bc9426460004640002dd5d89877ae89c00051200000050c0000003f200000000000000000046ea3e0be0000000008aa74800058a87c000000000000000bd2b2009392e2ba1127889562519240e67d65023c2742000000a341d54a83a690e00003c0002ff3fa07e000000000bfc8b492c866000bb02845833ae0006600000006f9a9a00007c5a85e40000000000008ab85e0005521cc81c1eeb9e0970fc5eb9360a50ba00000019a0004fe00038994a6340b26107080000001fa0a82fd238000000c0a1424cb984bec00069a1003f60a084800000000000024e0000000005a000077c9127521899d4363aaa1780aa00052198c0000000006023040008f800000016036880a0005c24dec040000007200000006be2b1180b9a00000043800000038600067f0000000000005800000009621357faad80000000004672fc8224bc83c5c71925465f25340006c41c8a18a7c19b0944624ca00085559c7364a6ace0000005944d84b8b1800021b9b64aaae8b2293288e25863200000000009f6e68c06a81640002a696a4027fd000ab6000a56022806000aa600000011016e2ee000000a227386aa94e7a6c1246a2da1480000000000300002b60002fa6446b2a307120000008d60009bcb787ba2c45700004123ac6f60000003f42ec00045c2d9000b953f81b0af400096600000062835c32c84c998c00b624e46e3950afbbea0b42521e85ad2974175f06b0620b56286c028b67ea18e00036a27aa7400084636526a37e0004fa1b115a9b800000029e00071f00028e7d877200091a1850000000883b3000000a980000003a80000000006585fe0f164c6f4000000000b067628982ae5c53389fc04f0006e01ba0262b70002d6000b6c98e8e285a00067c34a44300069600000000026e000345ac6306b420000000001ad000000000000000aa37ccb83b4ab8475007666d000000000770000000b317e22f45ab57cb9448e218000bc6b72000278729bf4400b3800061e000bd6a5a7a434012a7546d80001697ecb7e00020b31e9687656c6b7a00035e70c8a41f1326982bfe24061c9642be01c0a444e24f2620f64c61c267aa36880a4c94b43a00087e0008d05e80000000008fa6af00000066a0009780002bf146092bc4a4664e2a82f0367a54b5874a6ee88c09821600000086eb34aca000a0c0e7000000000293a780d200000071c000a268c2208000a687c00bc8d8be29ccbbc2cc8906b42e257f8ebba400000015c0de9e0623aa83806621d67846da00033c000
  | 10 => 0xac089f400046c0000003ce8766f28207468003fc2ac4602f823e24d2b35b27f009a8ac6804a06fb65c7307640e0b2916bbae0dc3908f483835d612000b3cb0d71a00071d7f8af74720001d040400000074e3d70006360007dc0000006bcc0e000b5a0004e6aaca0f0108f221c09977e37265eb980ce66f42e0000000003240005ac76e000b921a463e0007a2000bb87b66a50003aa54e9c63eeaae6661d20001f804b00011c83493053a986508bdc92020d3e859a0ae00000073416a8727020001a06781e230a0008b0b1c00000068132a22c0005b420436e0003af000000000a943365b8796ae46ec6a097a00077b0000008440006ad70a277a10350aa0259703a666e19f221495a4ce642c0600007400000049021d9f631d00079424a000000b6e5aa000bfa0003012e80008ed19c000000a2eba86251684dd93e9e5858ad668213076a9811e60002a2000000adeb5e275000ac068896c0a154818c79e0000eca203d01f09220506ff35f6308a249c0000003340007608de3023524180000024290f395805e40ab6a7e000000024200000091031a000af2674000896000aa189200003f83276185023200000468902e2243952df5c9000b2e83695e00000066b01600000000000000000000068c79a000000056ac4036bcc2101981723ec274000aea0008784987252339520fa6c08a06fc622b2854b312a174f2b12a5e3ba2090481b36184c2690a70b5090c0001450518d20003ad5dc0000000006850007f200000000000008e16200062e55096e000040486a92b10000ba65ea0000000c900000000001ab7000000000039300000048d27218899222f30c6df0001aec11a6e990000382024aee0008b200026643c718000704a2cb60b112ea29c0000002a470188600000094084f000a7e3540000005100000000000000c70003f0988000000b3206e1ebaf93d415e0007260000003e053c318084589000156000000000c140000000005203149b46164e042275e7b422679804473cb520000006e221e00000048479c4fcb0b06f00023a0000000000002b400087a4fd9c200003b95c0000006690000003080000005924cf00000068a7568e069e1bc8684689a473e0622572c100027c00068744c0c60001700000002560009a84114301c97aa538a043be1de00000000000000006b75809c88844526c4543d242a514207248000000234000afc56e00066c4d40000002312969d20f805a7e84240002bc5c047ca620009e22db3b6782808bd460000048c1430000000000000fe01f0c43704963963b20000001ac4cc00041c00057e0000009960004088d4ad214400000000050a39e9604349d01029440000000002680000e80009c0a5c20a000b143567b300000006800000043e4a4000b2a0008f6000b00b663c6000a90330000a72000b0f0000003
  | 11 => 0x9da19476602100000000009110a1ea000536af50000006ba0548ca1849e832054a0000001a620e07a7740004c8b8a000000a6a3485844e200071400013a7000957806e447a1d480ea7600090812eb1e0004f07a0bb40007448560000000000001a2488a121cf14e2e32ce65290aa283fe67e3644f83b12950000002e673257617c7a83690003412b23e259831937a0f55b0410be814d6b6ab402092a68b35825e65675c79234458e556a0a2e77b556200021a5cc3c4000902b82000b7faec6a7000a3c00082a19e0806406ac0000002790004d600025a2353d625c0001765321f2000000b8c9de0008dca025160000000a766e00056a68672e000000a2a13d51ebacbda141a9e1e401e00097f0003780008ec0008e65ec15427e31ca1c76371b9ae2b009d0c223044297097220c0a28c84c404200029238e000afa7210008cc72b54c63c0000000001825ba99417e000000ad000091c000236000b242c63b81224260005660000008ba7deb156c8ad4006000000000000000b1600024c82e4407281e000041e7b8ae61088121740006fe0003669dc38a28aac2a27ba215000000036b00010e000000b0e6d200004e38b45e096698000b2600049e0008af0009800000000002dc0000000005ef0f200015271e0006a107112c1b40285a49349b200094700008600000000000000078e00099c388000000000000946000000baa2aa01828252c0e58429ba000000000000000abe24b0cb0000007c9000000000000000a6c03e0009ce14bb8e00000000000006c00078c2600000000008106847060009e46b11cb7c20000006f50000000002fe786ab2ab084da146a60001c49046501d756851c58229056428c0f00003109a001413f0e222eb0413b1907e60005878f1b4e7c67fc37c0000006290000000005e2a0e7d0a960001979f0000000000476a5011eb2f2507ee0000000003e40002805238260d61be7780000008e89ee5c8000008000000000a9c0008645a6000090000b908040006ea6c20ac000120518bd000081a8186ae0d885c0001dc0003220000006a461485200000007888440f00067bb0a9ca6fa00000041600000000008f4699f86d07d44be0000005e03393c010c8bc000000815482000000bde0004d0000b6d5bca320006e5b2c1a82174704ba4da0002e4578acc4b46d40d07ca0008624ae000000446bb66b816da7a0006940000007760a634e4326ca0b03eaa520006dc2d206a2e52e18300000000005900000d
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd715881001cfc715881001eee215881001eec215881000cff705881000cfd7058810024fc7058810026ec205881001efa105881001ef91058810006ef7458810006ee7458810006ed7458810006ec7458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef4358810006ee4358810006ed4358810006ec435881001eef715881001eee715881001eed715881001eec715881001eef415881001eee415881001eed415881001eec415881001eef315881001eee315881001eed315881001eec3158810026ef7058810006ee7058810006ec7058810006ef3058810006ee3058810006ed3058810006ec305881001eef105881001eee105881001eea105881001eed105881001ee9105881001eec105881003cff76d081001cfe76d0810004fd76d081001cfc76d08100067e65d08100067d65d081003ebe64d0810006bd64d081011ede63d0810006dd63d081000eee62d0810006ed62d0810004ff765081001cfe7650810004fd765081001cfc76508100057f75508100057c75508100067e65508100067d655081003ebe6450810006bd6450810116de6350810006dd635081000eee6250810006ed6250810005f7715081001df47150810004fd76d00100067e65d00100067d65d001003ebe64d0010006bd64d00100bede63d0010006dd63d00100b6ee62d0010006ed62d0010004ff769001003cfd76900100067e65900100067d659001003ebe6490010006bd649001008ede6390010006dd63900100aeee6290010006ed629001001df67190010005f57190010004ff76500100057f75500100057c75500100067e65500100067d655001003ebe6450010006bd6450010005df735001002ddc73500100a6de6350010006dd635001009eee6250010006ed625001003cff761001001cfe7610010004fd761001001cfc76100100067e65100100067d651001003ebe6410010006bd6410010086de6310010006dd631001007eee6210010006ed621001001df67110010005f57110010054ff768801001cfe768801000cfd768801001cfc7688010006be6488010006bd6488010076de6388010006dd638801000eee6288010006ed628801001df67188010005f57188010056fa6088010054ff7648010006be6448010006bd644801006ede6348010006dd634801000eee6248010006ed6248010056fa604801001df77644010006f77644010004f77644010007b77444010007b4744401001fb6644401001fb56444010007d7734401015fd4734401001ef7634401001fd6634401015ef5634401001fd56344010006d56344010007e77244010007e4724401001fe6624401001fe5624401001df7704401001ff37044010156f6604401001ff26044010007f25044010007f15044010
  | 1 => 0x901001ebc319901001ebf219901001ebe219901001ebd219901001ebc219901003ebe709901003ebc7099010006bf3099010006be3099010006bd3099010006bc3099010006bf2099010006bc209901001ebf109901001ebe109901001ebd109901001ebc1099010004ff7559010094fc755901001ebf7459010004ff7359010014fe7359010004fd7359010014fc7359010006bf4359010006be4359010006bd4359010006bc4359010004ff725901000cfe725901000cfc7259010006be4259010006bc425901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc415901003cff705901003cfd7059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006be5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315901001ebe315901001ebd315901001ebc315901001ebf215901001ebe215901001ebd215901001ebc2159010006be7059010006bc7059010006bf3059010006be3059010006bd3059010006bc3059010006bf2059010006bc205901001ebf105901001ebe105901001ebd105901001ebc105901003cff769501001cfe7695010004fd769501001cfc76950100967e65950100067d659501003ebe6495010006bd64950100073f549501014ede6395010146ee6295010004ff765501001cfe7655010004fd765501001cfc765501003ebe6455010006bd645501013ede6355010136ee625501003cff761501001cfe7615010004fd761501001cfc761501003ebe6415010006bd64150100073d541501012ede6315010126ee6215010006df7458c10006de7458c10006dd7458c10006dc7458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006de4258c10006dc4258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c1002edf7058c10006de7058c1002edd7058c1002edc7058c10006df2058c10006dc2058c1001edf1058c1001ed71058c1001ede1058c1001edd1058c1001edc1058c10004ff745881003cfc7458810004ff7358810014fe7358810004fd7358810014fc735881001eef7258810026ee4258810026ec4258810006ef3258810026ee3258810006ed3258810026ec325881001cff715881001cfe715881001cf
  | 2 => 0x6bc6448510006df63485100c6dc6348510006ef624851000eec6248510005fb7048510005f8704851001cfe76d011001cfc76d01100067f65d01100067c65d0110006bf64d011003ebc64d0110006df63d01100bedc63d0110006ef62d01100b6ec62d011001df671d0110005f571d0110004fe76901100067f65901100067c6590110006bf649011003ebc6490110006df639011008edc6390110006ef62901100aeec629011003cff7650110004fd765011001cfc76501100057f75501100057c75501100067f65501100067c6550110006bf645011003ebc6450110005df735011004ddc7350110006df63501100a6dc6350110006ef625011009eec6250110005f7715011001df47150110004fe76101100067f65101100067c6510110006bf641011003ebc6410110006df6310110086dc6310110006ef621011007eec621011005cfe7688110006bf6488110006bc6488110006df6388110076dc6388110006ef628811000eec6288110005fa768811005efa7688110007bb6488110007b86488110007db638811017fd86388110045f97288110007eb628811000efa628811000ef86288110047e8628811000ee8628811001dfa718811001df8718811017ff2318811017ff13188110177ea2188110177e8218811000cff7648110044fd764811001cfc7648110006bf6448110006bc6448110006df634811006edc6348110006ef624811000eec6248110005f7714811001df47148110047e8204811001df8764811000ef8764811001cf87648110007bb6448110007b86448110007db634811016fd86348110045fb7248110007eb7248110007eb624811000efa624811000ef86248110047e86248110047ea324811016fe93248110007f3714811001dfa714811001df87148110007f0714811016ff2314811016ff13148110047eb2148110007e92148110006bf6484110006bc6484110006df6384110036dc6384110006ef6284110056ec628411001dfa708411001efb608411001df6768411001ef6768411001cf67684110007b76484110007b46484110155f77384110155f57384110007d76384110167d46384110007e76284110007e4628411001df6708411001ef7608411001ff36084110007f22084110007f1208411003ebf759901003ebe759901003ebd759901003ebc759901003ebf739901003ebe739901003ebd739901003ebc7399010006bf5399010006be5399010006bd5399010006bc539901003ebf729901003ebe729901003ebd729901003ebc7299010006be5299010006bc5299010006bf3299010006be3299010006bd3299010006bc329901001ebf719901001ebe719901001ebd719901001ebc719901001ebf519901001ebe519901001ebd519901001ebc519901001ebf319901001ebe319901001ebd319
  | 3 => 0xd32d8910046ec32d891001cfe71d8910044fd71d891001cfc71d8910046ef21d891000cfe70d891001cfd70d891000cfc70d8910046ef20d8910045ee76d891000cee76d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e631d8910007e531d8910177eb70d8910177eb10d8910177e810d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910176ee71d8910006ed71d8910176ec71d8910176ee41d8910176ec41d8910006ef31d8910176ee31d8910006ed31d8910176ec31d8910176ef70d8910046ee70d8910006ed70d8910006ef30d8910006ee30d8910006ed30d8910006ec30d8910176ef10d8910176ec10d8910005bf7458910005bc7458910006bf6458910006bc6458910005df735891004ddc7358910006df6358910006dc6358910046ec6258910004ff7458910006bf7458910004bf745891003cfc7458910006bc745891003cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc7358910044ff7258910006ef7258910054ff7158910006f7715891005cff7058910006fb7058910005ee7618910046ee7618910004ee7618910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e63118910007e53118910047e97018910186ef6018910187eb1018910187e8101891003cff76d0910004fe76d0910004fd76d091003cfc76d09100067f65d09100067c65d0910006bf64d091003ebc64d0910006df63d091011edc63d0910006ef62d091000eec62d0910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100057c75509100067f65509100067c6550910006bf645091003ebc6450910006df6350910116dc6350910006ef625091000eec6250910004fe76d05100067f65d05100067c65d0510006bf64d051003ebc64d0510006df63d051010edc63d0510006ef62d0510106ec62d0510005fa70d0510005f970d051003cfc76505100067f65505100067c6550510006bf645051003ebc6450510006df63505100eedc6350510006ef62505100e6ec6250510005fb7050510005f8705051000cfc7648510006bf6448510
  | 4 => 0x9110004ff7059110006fb7059110004fe76191100067f651911003ebe6419110006bd6419110006dc6319110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c6319110006be6219110006bc6219110007b63119110007b53119110197bb1019110197b8101911003ebf751911003ebe751911003ebd751911003ebc751911003ebf731911003ebe731911003ebd731911003ebc7319110006bf5319110006be5319110006bd5319110006bc531911003ebf721911003ebe721911003ebd721911003ebc7219110006be5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911003ebf711911003ebe711911003ebd711911003ebc7119110196be5119110196bc5119110006bf3119110196be3119110006bd3119110196bc3119110006bf2119110196be2119110196bc211911003ebf701911003ebd7019110006bf3019110006be3019110006bd3019110006bc3019110006bf2019110006bc2019110196bf1019110006bd1019110196bc101911003cff7695110004fe7695110004fd769511003cfc76951100067f65951100967c6595110006bf649511003ebc64951100073f549511014edc6395110146ec6295110004ff7655110004fe7655110004fd7655110004fc7655110006bf645511003ebc645511013edc6355110136ec625511003cff7615110004fe7615110004fd761511003cfc7615110006bf641511003ebc64151100073d541511012edc6315110126ec621511001df67115110005f5711511004dde76d8d1004ede76d8d10014de76d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10007d771d8d1004fd471d8d1018fdb10d8d1018fd810d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006de42d8d10006dc42d8d10006df71d8d1018ede71d8d1004edd71d8d1018edc71d8d1018ede41d8d1018edc41d8d10006df21d8d1018ede21d8d1018edc21d8d1018edf70d8d1004ede70d8d1004edd70d8d1004edc70d8d10006df20d8d10006dc20d8d1018edf10d8d1004edd10d8d1018edc10d8d1000cfe76d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910046ee62d891003cfe74d8910004fd74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910046ee42d8910046ec42d8910006ef32d8910046ee32d8910006e
  | 5 => 0x5df7350210035dc735021001cfd761021003ebe6410210006bd641021001df67110210005f5711021000cfe768821001cfd768821000eee6288210006ed628821001df67188210005f5718821001df9768821000ef9768821001cf9768821000efa6288210057ea6288210007e9628821000ef8628821001dfa7188210007f27188210007f1718821001df87188210177ea2188210177e82188210024ff7648210006ef624821000eec6248210057e82048210005fb7648210026fb7648210007eb7248210007eb624821000efa624821000ef86248210057e86248210057ea32482101afe9324821001dfa714821001df87148210057eb2148210007e92148210005f576c421001ef576c42101a6f763c42101a6f563c421001ff260c421003cfe76d9110006dc63d9110094fe75d9110004fd75d9110004ff73d9110014fe73d9110004fd73d9110014fc73d9110006bf43d9110006be43d9110006bd43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d911001cfe71d911001cfc71d911003cfe70d911003cfc70d911003cbe76d9110006bf65d91100073f65d91100063f65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d9110006be62d9110006bc62d9110007b631d9110007b531d911019fbb10d911019fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d911019ebe71d9110006bd71d911019ebc71d911019ebe51d911019ebc51d9110006bf31d911019ebe31d9110006bd31d911019ebc31d9110006bf21d911019ebe21d911019ebc21d911019ebf70d9110006bd70d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110006bf20d9110006bc20d911019ebf10d911019ebc10d91100057e75991100057d75991100067f6599110006bf649911004dde7399110005dd7399110006dc6399110045ee7299110005ed72991100057f75591100057c75591100067f6559110005df735911004ddc7359110006dc6359110005ef7259110045ec7259110004ff75591100067f75591100047f7559110094fc75591100067c75591100947c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110004fd7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec7259110004ff7159110006f7715
  | 6 => 0xf76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b1003ebe64d0b10006bd64d0b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b100057f7550b100057c7550b1003ebe6450b10006bd6450b1003ebe64d0310006bd64d031001df671d0310005f571d031019ebf649031003ebc649031003cff76503100057f75503100057c755031003ebe6450310006bd6450310005df7350310065dc7350310005f7715031001df47150310196bf641031003ebc6410310044fd7688310176ef628831000eec628831000cff764831001cfc764831000eee6248310006ed6248310005f7714831001df47148310094fe75d9210004fd75d9210004ff73d9210014fe73d9210004fd73d9210014fc73d9210006be43d9210006bc43d921000cfe72d9210004fd72d921000cfc72d9210006f571d921019ebe41d921019ebc41d9210006fa70d9210004fd7699210006bf649921003cff76592100057f75592100057c7559210005df7359210035dc7359210004ff75592100067f75592100047f7559210094fc75592100067c75592100947c7559210006bf7459210004ff7359210006df7359210004df7359210014fe7359210004fd7359210014fc7359210006dc7359210014dc7359210006bf4359210006bd4359210004ff725921000cfe725921000cfc725921003ebe6419210006bd641921003cff7695210004fe7695210004fd769521003cfc76952100067f65952100967c65952100073f5495210004ff7655210004fe7655210004fd7655210004fc765521003cff7615210004fe7615210004fd761521003cfc7615210006bf641521003ebc64152100073d5415210056ee62d8a1003cfe74d8a10004fd74d8a10004ff73d8a10014fe73d8a10004fd73d8a10014fc73d8a10054fd72d8a10006f571d8a10176ee21d8a10176ec21d8a10006fa70d8a10056ef20d8a1000cff7658a10056ec6258a10004ff7458a1003cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a10006ef7258a10056ee3258a10006ed3258a10056ef2158a1001cfc7058a10056ec2058a1003cff76d0a10004fe76d0a10004fd76d0a1003cfc76d0a10006bf64d0a1003ebc64d0a10004ff7650a10004fe7650a10004fd7650a10004fc7650a100057f7550a100057c7550a10006bf6450a1003ebc6450a10005f77150a1001df47150a1003ebe64d0610006bd64d0610005fa70d0610005f970d061003cff765061003ebe6450610006bd6450610005fb7050610005f8705061000cff764861000eee6248610006ed624861001fe42148610005fb7048610005f87048610006bf64d021003ebc64d021001cfd769021003ebe6490210006bd649021001df67190210005f571902100057f75502100057c7550210006bf645021003ebc6450210
  | 7 => 0x5120004ff7655120004fe7655120004fd7655120004fc7655120005ef725512000dec725512003cff7615120004fe7615120004fd761512003cfc7615120006bf641512003ebc64151200073d541512000dee7215120005ed721512003cfe74d8520004fd74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d8520006f731d8520006f431d8520056f621d8520056f521d852001cfe70d8520006f76198520045f97098520005bf7458520005bc7458520005df735852006ddc735852005dfb7058520005be7418520005bd741852006dde7318520005dd731852001ef66118520006f56118520004fe76d0520004fd76d052003cfc76d052003ebe64d0520006bd64d0520006f761d052001ef461d0520004fe7690520004fd769052001cfc76905200057e75905200057d7590520006bf649052003ebc649052006dde7390520005dd739052000dee7290520005ed7290520005fa7090520005f97090520004ff7650520004fe7650520004fc765052003ebe6450520006bd6450520004fe7610520004fd761052001cfc7610520006bf641052003ebc641052000dee7210520005ed7210520006f7611052001ef46110520005fa7010520005f9701052001cec76485201bdef73485201bded734852000def714852000fe77148520007e7614852001eee614852001eec6148520007e4614852001ee46148520007eb7048520005ec7048520007e8704852000eef604852000feb604852000cfe76d012000cfc76d0120006bf64d012003ebc64d012000dee72d0120005ed72d012007cfe769012003ebe6490120006bd649012003cff765012000cfe765012009cfd765012000cfc76501200057f75501200057c7550120006bf645012003ebc6450120005df735012006ddc7350120005ef725012000dec72501200acfe761012003ebe6410120006bd64101201b5ef73881201b5ed7388120005ed7188120176ec618812000dee708812000fea708812000eef608812000feb6088120004ff7559310094fc755931001ebf7459310004ff7359310014fe7359310004fd7359310014fc7359310006be4359310006bc4359310004ff725931000cfe725931000cfc725931001cfc715931001ebe415931001ebc415931003cff769531001cfe7695310004fd769531001cfc76953100967e65953100067d65953100073f5495310004ff765531001cfe7655310004fd765531001cfc765531003cff761531001cfe7615310004fd761531001cfc761531003ebe6415310006bd64153100073d541531001df67115310005f57115310004ff7458b1003cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b1001eef7258b1001cfc7158b1001eee2158b1001eec2158b1005eef2058b1001efa1058b1001ef91058b1003cf
  | 8 => 0x6bf4359220006bd435922009ebf425922009ebd4259220004ff715922001cfc715922003ebe6419220006bd64192200adfa701922003cff7695220004fe7695220004fd769522003cfc76952200967e65952200067d65952200073f5495220004ff7655220004fe7655220004fd7655220004fc765522003cff7615220004fe7615220004fd761522003cfc761522003ebe6415220006bd64152200073d5415220025fa70d8620006f76198620004ff745862003cfc7458620004ff7358620014fe7358620004fd7358620014fc7358620006f63158620006f53158620046f62158620046f52158620176ec215862001cff7058620046ef2058620005be7418620005bd7418620075de7318620005dd731862001ef66118620006f56118620055fa701862003cff76d0620004fe76d0620004fd76d062003ebe64d0620006bd64d062000dee72d0620005ed72d062001cff7690620004fe7690620004fd76906200057e75906200057d7590620075de7390620005dd7390620005fa7090620005f97090620004ff7650620004fd7650620004fc765062003ebe6450620006bd6450620005ef725062000dec725062001cff7610620004fe7610620004fd7610620005fa7010620005f970106201c6ef63886201c6ed638862000dee718862000fe67188620177e66188620176ed6188620007e56188620177ea7088620005ed7088620177e9708862000eee608862000fea608862009cfd76d022000cff769022000cfd769022003ebe6490220006bd649022000dee7290220005ed72902200b4ff76502200057f75502200057c7550220005df7350220075dc735022000cff761022000cfd761022003cfc761022003ebe6410220006bd641022000dee7210220005ed721022003cfe76d9120094fe75d9120004fd75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d9120006be43d9120006bc43d91200acff72d912000cfe72d91200acfd72d912000cfc72d91200aebf42d91200aebd42d912001cfe71d9120004fd71d9120006bf649912009df970991200057f75591200057c7559120005df735912006ddc7359120005f77159120005f471591200b5fb7059120004ff75591200067f75591200047f7559120094fc75591200067c75591200947c7559120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc7359120006bf4359120006bd435912009cff7259120006ef7259120004ff7159120006f77159120004f7715912001cfc7159120006f4715912001cf471591200b4ff7059120006fb70591200acfe761912003ebe6419120006bd641912003cff7695120004fe7695120004fd769512003cfc76951200067f65951200967c65951200073f549
  | 9 => 0xd635084003dbf725084003faf725084000ebe625084000ebc6250840195bc7150840005bf70508400aebe605084003fba6050840004ff7558440094fc7558440006bf545844003ebc5458440004ff7358440014fe7358440004fd7358440014fc7358440006be435844003ebc4358440004ff725844000cfe725844000cfc725844003ebf4258440006bd425844003ef7715844003ef7415844003ebc415844003ef44158440006f63158440006f5315844003ebf4058440094ff76d444003cfe76d4440004fd76d44400967e65d44400067d65d444003dbe74d4440005bd74d44402073c54d444001cff769444003cfe7694440004fd769444003dbe7494440005bd7494440085de7394440005dd739444001ef66194440006f56194440004ff7654440004fd765444003cfc76544400967e65544400067d6554440005bf745444003dbc74544401ff3c545444001ef66154440006f5615444001cff761444003cfe7614440004fd761444003dbc741444003dbd7690440196bd7690440004bd76904401ddbe75904401973e75904400053e75904401973d7590440195bc7590440085be73904401979e73904400859e73904401979d7390440195bc739044003ebf63904401f6bd6390440005bd729044003dbe719044003fb6719044003ebf6190440196bd6190440005bd709044019ebe609044003fba609044001cff768844003cfe7688440004fd7688440195bf748844003dbc748844001ef66188440006f56188440004ff7648440004fd764844003cfc7648440005bf744844003dbc744844000eee6248440006ed624844001ef66148440006f56148440004fd76d404003dbc74d4040004ff7694040094fd76940400967e65940400067d659404003dbe7494040005bd74940401ef3c5494040004ff7654040005bf745404003dbc7454040005df7354040085dc735404003cfe7614040004fd761404003cfc761404003dbe7414040005bd74140401e73c541404003dbf7650040006bf7650040004bf76500400073f75500401ddbe75500401ddbc75500400073c75500400053c75500400079f7350040085be7350040085bc73500401d79c73500400859c735004003ebf63500401d6bd6350040005bf7250040195bc7150040006bd615004003dbf705004003fbb70500401cebe605004003fba60500400057e75d92200057d75d922007dfa70d9220094fe75d92200067e75d92200947e75d9220004fd75d92200067d75d92200047d75d9220004ff73d9220014fe73d9220004fd73d9220014fc73d9220006ed72d922001cfe71d9220004fd71d922007cfe70d9220006fa70d922009cfd7699220006bf649922003cff7659220004ff7559220094fc7559220006bf7459220004ff7359220014fe7359220004fd7359220014fc7359220
  | 10 => 0x54025ebe655054025ebc65505400073c65505400063c6550540255bf7350540255bd73505400079f63505400eebe63505400eebc635054024f9c63505400ee9c6350540006bf625054003dbf715054003fb77150540007b7615054001ebe615054001ebc6150540007b46150540007bb7050540005bc7050540007b8705054003ebf605054003fbb6050540004fe7688540004fd768854001cfc76885400067f65885400067c658854003dbe7488540005bd7488540006df63885400cedc6388540006ef628854000eec6288540004ff7648540004fe7648540004fc76485400067f65485400067c6548540006df63485400c6dc634854003cfe76d414003cfc76d41400067f65d41400967c65d414003dbe74d4140005bd74d4140006df63d4140246dc63d41400067f65941400967c6594140006df639414023edc63941400077b5094140004fd765414003cfc7654140005bf745414003dbc7454140006df6354140236dc63541400067f65901400067c6590140006df639014008edc639014003dfa709014003efb60901400073f6590140216be6590140216bc65901400073c65901400063c65901401cdbf73901401cdbd73901400079f639014008ebe639014008ebc639014022f9c639014008e9c6390140006bf6290140005bd719014019ebc619014003dbe709014003ebf609014003fbb609014003e7f755944003cff745944003cfe745944003cfd745944003cfc745944003ebc745944003cbc745944003e7e545944003e7c545944003ebc545944003e3c5459440004ff7359440014fe7359440004fd7359440014fc73594400067f53594400067d5359440004ff725944000cfe725944000cfc725944003ebf4259440004ff715944001cfc715944003dbd76d50401debd76d504003dbe75d504003f3e75d504003ebf65d50401debd65d5040085be73d5040085bc73d504003ebf63d5040226bd63d5040005bd72d504021ebe62d504003ebc62d5040195be71d5040005bd70d5040216be60d504003fba60d5040004ff7558840094fc755884000cfd7458840004ff7358840014fe7358840004fd7358840014fc735884003eef725884007eee525884003eef425884003eec425884007eee3258840006ed3258840004ff715884001cfc715884007eef215884007eec2058840094ff76d484003cfe76d4840004fd76d48400967e65d48400067d65d484003dbc74d48401df3f54d4840004ff7654840004fd765484003cfc76548400967e65548400067d6554840005bf745484003dbc74548400073f545484000eee6254840006ed625484003dbf76508400b6bf76508400073f75508401ddbe75508401ddbc75508400073c75508400053c755084003ebf6550840006bd6550840085be7350840085bc735084003ebf635084020eb
  | 11 => 0xcfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d8940006bf43d8940006bd43d894009eee42d894001cfe71d8940004fd71d894009eec21d894003cfd70d894009eef20d89400057f75589400057c75589400067f65589400067c6558940005df73589400a5dc7358940006df6358940006dc635894009eec6258940005f77158940005f47158940004fe76d4940004fd76d4940094fc76d49400067f65d49400967c65d4940006df63d49402a6dc63d4940004ff7654940004fe7654940004fc76549400067f65549400967c6554940005bf745494003dbc7454940006df635494029edc635494000cfc76509400057f75509400057c75509400067f65509400067c6550940006df6350940116dc6350940006ef625094000eec625094003fac4250940005fb7050940005f870509400067f65d85400067c65d8540006df63d8540006dc63d8540094fe75d8540004fd75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d854000cfe72d8540004fd72d854000cfc72d8540006f721d8540006f421d85400057e75985400057d75985400067f65985400067c65985400a5de7398540005dd7398540006df6398540006dc6398540006f761985400057f75585400057c75585400067f65585400067c6558540005df73585400a5dc7358540006df6358540006dc6358540005ef725854009dec72585400067f65185400067c6518540006df6318540006dc631854001ef66118540006f56118540004fe76d4540004fd76d4540094fc76d45400067f65d45400967c65d4540006df63d4540296dc63d4540004fe7694540004fd769454001cfc76945400067f65945400967c659454003dbe7494540005bd74945400a5de7394540005dd7394540006df639454028edc6394540004ff7654540004fe7654540004fc76545400067f65545400967c6554540006df6354540286dc6354540004fe7614540004fd761454001cfc76145400067f65145400967c651454003dbe7414540005bd7414540006df631454027edc6314540005be76d054003ebe76d0540004be76d05400073f65d0540276be65d0540276bc65d05400073c65d05400063c65d054003dbf73d054026dbd73d05400079f63d054010ebe63d054010ebc63d05402679c63d054010e9c63d0540006bf62d054001ebe61d054001ebc61d0540005be70d054003ebf60d054003fbb60d05400057e75905400057d75905400067f65905400067c6590540255bd74905400a5de7390540005dd7390540006df63905400fedc6390540006f7619054001ef46190540005fa7090540005f9709054001cfc76505400067f65505400067c6550540006df63505400eedc6350540006f7615054001ef46150540005fb7050540005f8705054001cbc76505400073f655
  | 12 => 0xe30d95400067d30d95400067c30d95400067f20d95400067c20d95400067f65995400a5de7399540005dd7399540006dc6399540005df73595400a5dc7359540006dc6359540006bf7459540004ff7359540006df7359540004df7359540014fe7359540004fd7359540014fc7359540006dc7359540014dc7359540004ff725954000cfe725954000cfc7259540004ff715954001cfc7159540004ff7059540006fb7059540004fe76195400967e65195400067d6519540006dc63195400057e76195400067e76195400047e76195400067f63195400067e63195400067d63195400067c63195400075c63195400065c63195400073f43195400073d43195400067e62195400067c62195401e77b40195401e77840195400967f74195400967e74195400967c74195400967f73195400967e73195400967d73195400967c73195401e67f43195400063f43195400067e43195400067d43195400063d43195401e67c43195400967f72195400967e72195400967d72195400967c72195401e67f42195400067e42195401e67c42195400067f32195400067e32195400067d32195400067c32195400967f71195400967e71195400967d71195400967c71195401e67f41195401e67c41195400067f31195400067e31195400067d31195400067c31195400067f21195400067c21195400967f70195400967d70195401e67f40195400067d40195401e67c40195400067f30195400067e30195400067d30195400067c30195400067f20195400067c2019540004fe76d51400067f65d51400967c65d514003f3e54d51402b6dc63d5140005fa70d5140005f970d5140094fc76551400067f65551400967c655514003f3c545514013edc6355140005fb7055140005f870551400a5de76d8d400a6de76d8d40014de76d8d40006df65d8d400075f65d8d400065f65d8d40006de65d8d40006dd65d8d40006dc65d8d400075c65d8d400065c65d8d400079f74d8d400a79c74d8d40006de62d8d40006dc62d8d402afdb40d8d402afd840d8d40006df75d8d40006de75d8d40006dd75d8d40006dc75d8d40006df74d8d400a6de74d8d400a6dd74d8d400a6dc74d8d40006df54d8d402aede54d8d40006dd54d8d402aedc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006de52d8d40006dc52d8d402aedf42d8d40006de42d8d402aedc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d402aedf41d8d402aedc41d8d40006df21d8d40006dc21d8d402aedf70d8d400a6de70d8d400a6dd70d8d400a6dc70d8d402aedf40d8d400a6dd40d8d402aedc40d8d40006df20d8d40006dc20d8d4000cfe76d89400067f65d89400067c65d8940006df63d8940006dc63d894009eee62d8940094fe75d8940004fd75d8940
  | 13 => 0x4640004fe76d4640004fd76d46400967e65d46400067d65d464003dbe74d4640005bd74d46402173c54d464001cff7694640004fe7694640004fd769464003dbe7494640005bd749464008dde7394640005dd7394640004ff7654640004fd7654640004fc76546400967e65546400067d6554640005bf745464003dbc74546400073c545464001cff7614640004fe7614640004fd76146400057e75906400057d759064008dde7390640005dd739064001ef66190640006f56190640005fa7090640005f97090640215be759064019f3e75906400053e759064019f3d759064019dbc759064008dbe739064019f9e739064008d9e739064019f9d739064019dbc73906402cebf63906402cebd6390640005bd729064003dbe719064019fb6619064019ebd6190640007b5619064019fba7090640005bd709064019fb9709064003ebe609064001cff765064001ef66150640006f56150640005fb7050640005f87050640005bd761064003ebd7610640215be751064003dbc751064008dbe731064003dbc73106402c6bf63106402c6bd6310640005bd721064003fb6711064019ebd6110640005bd701064003fba601064001cff7688640004fe7688640004fd768864019dbf748864003dbc7488640004ff7648640004fd7648640004fc7648640005bf744864003dbc744864000eee6248640006ed624864003cfd769424003dbe7494240005bd74942400073c5494240005bd76d024003ebd76d0240215be75d024003dbc75d024008dbe73d024003dbc73d02402bebf63d02402bebd63d0240005bd72d024019dbe71d0240006bd61d024003fba60d0240007ba50d0240006dc63d954003cfe74d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400067f53d95400067e53d95400067d53d95400067c53d954000cfe72d9540004fd72d954000cfc72d95400067e52d95400067c52d954001cfe71d9540004fd71d95400067f63d95400067e63d95400067d63d95400067c63d95400075c63d95400065c63d95400073f43d95400073d43d95400067e62d95400067c62d95401ef7b40d95401ef7840d95400067f74d95401ee7e74d95400067d74d95401ee7c74d95400067f73d95400067e73d95400067d73d95400067c73d95401ee7f43d95400067e43d95400067d43d95401ee7c43d95400067f72d95400067e72d95400067d72d95400067c72d95401ee7f42d95400067e42d95401ee7c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95401ee7f41d95401ee7c41d95400067f31d95400067e31d95400067d31d95400067c31d95400067f21d95400067c21d95401ee7f70d95400067d70d95401ee7f40d95401ee7c40d95400067f30d95400067
  | 14 => 0x67d5359640004ff725964000cfe725964000cfc72596400067e52596400067c5259640004ff715964001cfc71596400967e65196400067d65196400967e65d52400067d65d524003f3e54d5240005fa70d5240005f970d524003dbe75d5240216bf65d52402173e65d5240216bd65d52400073d65d52400063d65d524008dbe73d524008dbc73d52402f6bf63d52402f6bd63d5240005bd72d524021ebe62d524021ebc62d524019dbe71d5240217ba70d5240005bd70d5240217b970d5240005b970d524003ebe60d5240094ff76552400967e65552400067d655524003f3c5455240005fb7055240005f8705524003fbb4055240005bd761524003ebd761524003f3e7515240216bf65152400073f65152400063f6515240216bd65152402173c651524008dbe731524003dbc73152402eebf63152402eebd63152402173f53152402ef3d5315240005bd7215240126be6215240126bc62152402e73e52152402173c521524019dbe7115240005bd701524003fba60152400057e75d8a400057d75d8a400aeee62d8a4000cff7658a400aeec6258a40004ff7558a40094fc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400aeec5258a400aeee4258a400aeee3258a40006ed3258a40004ff7158a4001cfc7158a400aeef2158a4003cfc7058a400aeec2058a40094ff76d4a40004fe76d4a40004fd76d4a400967c65d4a402173f54d4a4000eee62d4a40006ed62d4a40004ff7654a40004fd7654a40004fc7654a40005bf7454a4003dbc7454a400073f5454a40005bd76d0a4003ebd76d0a40215be75d0a4003dbc75d0a40006bf65d0a40006bd65d0a4008dbe73d0a4003dbc73d0a402debf63d0a402debd63d0a4000ebe62d0a4000ebc62d0a4019dbe71d0a40005bd70d0a4003fba60d0a4000cff7650a400057f7550a400057c7550a4000eee6250a40006ed6250a40005fb7050a40005f87050a400adbf7650a4000ebf7650a4000cbf7650a400073f7550a40215be7550a40215bc7550a400073c7550a400053c7550a40006bf6550a40006bd6550a4008dbe7350a4008dbc7350a402d6bf6350a402d6bd6350a4003dbf7250a4003faf7250a4000ebe6250a400afae6250a4000eae6250a40007ad6250a4000ebc6250a4019dbc7150a40005bf7050a40007bb7050a40007b87050a4003ebe6050a40006f76198640004ff7558640094fc7558640006bf5458640006bc5458640004ff7358640014fe7358640004fd7358640014fc7358640006be4358640006bc4358640004ff725864000cfe725864000cfc7258640006bf4258640006bd4258640006f63158640006f531586400057e75186400057d751864008dde7318640005dd73186400adee7218640005ed721864001ef66118640006f56118640094ff76d
  | 15 => 0xc7615121006bf641512103ebc64151210073d541512100cfe76d052100cfc76d0521006bf64d052103ebc64d052100dee72d0521005ed72d052103cff765052100cfe76505210e4fd765052100cfc7650521006bf645052103ebc6450521005ef725052100dec725052101fe4215052103cfe74d8121004fd74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d812101cfd72d812105efa20d8121006fb6098121005bf7458121005bc7458121005df73581210c5dc7358121006f9601812103cfe7418121004fd7418121004ff7318121014fe7318121004fd7318121014fc731812101cfd7218121186ee2118121186ec2118121026ef2018121026f9201812103e7f755974003e7e545974003e7c5459740004ff7359740014fe7359740004fd7359740014fc73597400067e53597400067c5359740004ff725974000cfe725974000cfc7259740004ff715974001cfc7159740004ff7558b40094fc7558b40004ff7358b40014fe7358b40004fd7358b40014fc7358b4003ebf4358b40006bd4358b4003eef7258b4003eef4258b4003eec4258b40004ff7158b4001cfc7158b4003ebf4158b400b6ec2158b4003ebc4058b400b6ef2058b40094ff76d4b4003cfe76d4b40004fd76d4b400967e65d4b400067d65d4b40004ff7654b40004fd7654b4003cfc7654b400967e6554b400067d6554b40005bf7454b4003dbc7454b40004ff7558740094fc7558740004ff7358740014fe7358740004fd7358740014fc7358740004ff725874000cfe725874000cfc725874003ef7715874003ef7415874003ef44158740094ff76d474003cfe76d4740004fd76d47400967c65d474001cff769474003cfe7694740004fd76947400967e65947400067d659474003dbe7494740005bd74947400bdde7394740005dd7394740004ff7654740004fd765474003cfc765474001cff761474003cfe7614740004fd76147400967e65147400067d651474003dbe7414740005bd741474003dbf7650740006bf765074025ebe655074003ebc65507402fdbf73507402fdbd73507400eebe635074003ebc6350740006bd625074003fb7715074001ebe615074001ebc6150740005bc705074001cff768874003cfe7688740004fd768874003dbe7488740005bd748874000eee6288740006ed6288740004ff7648740004fd764874003cfc764874003dbe74d4340005bd74d43400adee72d9640005ed72d9640004ff73d9640014fe73d9640004fd73d9640014fc73d964000cfe72d9640006ee72d964000cee72d9640004fd72d9640006ed72d9640004ed72d964000cfc72d964001cfe71d9640004fd71d9640006fa70d96400067f6599640094ff76596400067f7559640004ff7359640014fe7359640004fd7359640014fc73596400067f5359640
  | 16 => 0x484103dbc7454841094fe7598041004fd7598041004ff7398041014fe7398041004fd7398041014fc739804100cfe7298041004fd729804100cfc729804101efa709804103efb409804103ef8409804101efb109804101ef81098041004ff75580410067f75580410047f7558041094fc75580410067c75580410947c7558041004ff7358041006df7358041004df7358041014fe7358041004fd7358041014fc7358041006dc7358041014dc735804103ebf4358041006bd4358041004ff725804100cfe725804100cfc725804101ebf415804101ebd415804101efb705804103efb405804103ebc405804103ef8405804101efb105804101ef81058041004ff7559221094fc755922101ebf7459221004ff7359221014fe7359221004fd7359221014fc7359221006be4359221006bc43592210e6bf42592210e6bd425922101cfe715922101cfc715922101ebe415922101ebc4159221004ff7059221004fc705922103cff769522101cfe7695221004fd769522101cfc76952210967e65952210067d65952210073f5495221004ff765522101cfe7655221004fd765522101cfc7655221005ef725522100dec725522103cff761522101cfe7615221004fd761522101cfc761522103ebe6415221006bd64152210073d541522100dee7215221005ed721522103cfe7498221004fd7498221004ff7398221014fe7398221004fd7398221014fc739822101cfe719822101efa7098221056f9209822101efb109822101ef81098221004ff7458221006bf7458221004bf745822103cfc7458221006bc745822103cbc7458221004ff7358221006df7358221004df7358221014fe7358221004fd7358221014fc7358221006dc7358221014dc7358221046ee3258221006ed325822101cfc715822101eef215822101eed215822101efb7058221046fa2058221046ec205822101efb105822101ef8105822103cfe76d9121094fe75d9121004fd75d9121004ff73d9121014fe73d9121004fd73d9121014fc73d9121006bf43d9121006bd43d912101cff72d912101cfd72d91210f6bf42d91210f6bd42d9121004fe70d9121004fd70d9121006bf64991210e5f571991210057f75591210057c7559121105f77159121004ff75591210067f75591210047f7559121094fc75591210067c75591210947c7559121006bf7459121004ff7359121014fe7359121004fd7359121014fc73591210e4ff7259121006ef7259121104ff7159121006f77159121004ff7059121004fc70591210f4fe761912103ebe6419121006bd641912103cff7695121004fe7695121004fd769512103cfc76951210067f65951210967c65951210073f5495121004ff7655121004fe7655121004fd7655121004fc765512103cff7615121004fe7615121004fd761512103cf
  | 17 => 0x57f75589410057c75589410e6ec6258941004fe76d4941004fd76d4941094fc76d49410967e65d494125f3f54d4941006ef62d494100eec62d4941004ff7654941004fe7654941004fc76549410967e6554941005bf745494103dbc74549410073f5454941005be76d094103ebe76d094125dbe75d094103dbc75d0941006bf65d0941006bd65d09410edbe73d094103dbc73d094130ebf63d094130ebd63d09410e5bd72d094100ebe62d094100ebc62d094101dbe71d094101dbc71d094103ebf61d094103fb761d0941005bd70d094101cfc76509410057f75509410057c7550941006ef625094100eec6250941005f7715094101df4715094101dbc765094100ebc765094101cbc76509410073f755094125dbe755094125dbc75509410073c75509410053c7550941006bf6550941006bd65509410edbe73509410edbc7350941306bf6350941306bd635094103dbf725094103faf7250941007af625094100ebe625094100ebc62509410e7ac625094100eac6250941007b7715094101dbe715094101dbc7150941007b4715094103ebf615094103fb76150941005bf705094103cfe76d454103cfc76d45410067f65d45410967c65d454103dbe74d4541005bd74d454125f3c54d454101f7651d4541004fd765454103cfc7654541005bf745454103dbc74545410073c545454101fb44154541094fe75d8141004fd75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d8141006fb60981410057f75581410057c7558141005df73581410eddc7358141005ef72581410e5ec7258141006f96018141094fe7518141004fd7518141006bf5418141006bc5418141004ff7318141014fe7318141004fd7318141014fc7318141006be4318141006bc431814100cfe7218141004fd721814100cfc7218141006bf4218141006bd4218141196be4118141196bc411814101cff755944101e7f755944103cfe745944103cfc745944103e7e545944103e7c5459441004ff7359441014fe7359441004fd7359441014fc73594410067e53594410067c5359441004ff725944100cfe725944100cfc725944101cfe715944101cfc715944101e7e515944101e7c5159441004ff7059441004fc7059441004ff7558841094fc7558841004ff7358841014fe7358841004fd7358841014fc735884103ebf4358841006bd435884101cff725884101eef725884103eef425884103eec425884101cfc715884101ebf415884101ebd415884101eee215884101eec2158841004ff7058841004fc705884103ebc40588410d6ef2058841094ff76d484101cfe76d4841004fd76d48410967e65d48410067d65d4841004ff7654841004fd765484101cfc76548410967e65548410067d6554841005bf745
  | 18 => 0xe65d4a410067d65d4a412a6de63d4a41006dd63d4a41004ff7654a41004fd7654a4101cfc7654a410967e6554a410067d6554a41005bf7454a4103dbc7454a4129ede6354a41006dd6354a4100cff7650a410057f7550a410057c7550a410067e6550a410067d6550a41116de6350a41006dd6350a4100eee6250a41006ed6250a4103fac4250a41005f77150a4101df47150a41094fe7598241004fd7598241004ff7398241014fe7398241004fd7398241014fc739824100cfe7298241004fd729824100cfc729824101cfe719824101efa709824101efb109824101ef81098241004ff7558241094fc7558241004ff7358241014fe7358241004fd7358241014fc7358241006bf4358241006bd4358241004ff725824100cfe725824100cfc725824101cfc715824101ebf415824101ebd415824101efb705824101efb105824101ef81058241006bd74d9541004ff73d9541014fe73d9541004fd73d9541014fc73d95410067f53d95410067d53d954100cfe72d9541004fd72d954100cfc72d95410067e52d95410067c52d9541004fe70d9541004fd70d95410067f6599541005ef72595410e5ec7259541006bf7459541004ff7359541014fe7359541004fd7359541014fc7359541004ff7259541006ef7259541004ef725954100cfe725954100cfc7259541006ec725954100cec7259541004ff7159541006f77159541004ff7059541004fc7059541004fe76195410967e65195410067d651954101cfe76d51410067f65d51410967c65d514103f3e54d514101df671d5141005f571d514101dbe76d514125ebe76d514101cbe76d514103dbe75d514125ebf65d51410073f65d51410063f65d514125ebd65d514125f3c65d51410edbe73d51410edbc73d5141326bf63d5141326bd63d5141005bd72d514121ebe62d514121ebc62d514101dbe71d514125fb671d514101db671d514125fb571d514101dbc71d514103ebf61d514103fb761d5141005bd70d514101cfc76551410067f65551410967c655514103f3c5455141005f7715514101df4715514103fb44155141005be761514103ebe761514125dbe751514103f3e751514125ebf651514125f3e651514125ebd65151410073d65151410063d65151410edbe731514103dbc731514131ebf631514131ebd631514125f3f531514131f3d5315141005bd7215141126be6215141126bc62151413173e521514125f3c521514101dbe711514101dbc711514103ebf611514103fb76115141005bd701514100cfe76d89410e6ee62d8941094fe75d8941004fd75d894101cfd74d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410e6ec52d89410e6ee42d89410e6ee32d8941006ed32d894103cfd71d89410e6ef21d8941004fe70d8941004fd70d89410e6ec20d8941
  | 19 => 0x96410967e70996410967d70996410967c70996412067f40996412067c40996410067f30996410067e30996410067d30996410067c30996410067f20996410067c209964101e7f109964101e7e109964101e7d109964101e7c109964101e7f7559641004ff7359641014fe7359641004fd7359641014fc73596410067f53596410067e53596410067d53596410067c5359641004ff725964100cfe725964100cfc72596410067e52596410067c525964101cfc715964101e7e515964101e7c5159641004ff7059641004fc70596410067d74596411fe7c74596410067f73596410067e73596410067d73596410067c73596411fe7f43596410067e43596410067d43596411fe7c43596410067f72596410067e72596410067d72596410067c72596411fe7f42596410067e42596411fe7c42596410067f32596410067e32596410067d32596410067c325964101e7f715964101e7e715964101e7c715964101e7f415964101e7e415964101e7d415964101e7c415964101e7f315964101e7e315964101e7d315964101e7c315964101e7f215964101e7e215964101e7d215964101e7c21596410067f70596410067e70596410067d70596410067c70596411fe7f40596411fe7c40596410067f30596410067e30596410067d30596410067c30596410067f20596410067c205964101e7f105964101e7e105964101e7d105964101e7c10596410967e65d52410067d65d524103f3e54d52412b6de63d524101df671d5241005f571d5241094ff76552410967e65552410067d655524103f3c545524113ede6355241005f7715524101df4715524103fb74155241006df7558e41006de7558e41006dd7558e41006dc7558e410fedf7458e410fede7458e41006dd7458e410fedc7458e41006df5458e4132ede5458e41006dd5458e4132edc5458e41006df7258e41006de7258e41006dd7258e41006dc7258e41006de5258e41006dc5258e4132edf4258e41006de4258e4132edc4258e4101edf7158e4101ede7158e4101edd7158e4101edc7158e4101edf5158e4101ede5158e4101edd5158e4101edc5158e4101edf4158e4101ede4158e4101edd4158e4101edc4158e4101edf2158e4101ede2158e4101edd2158e4101edc2158e41006df7058e41006de7058e41006dd7058e41006dc7058e4132edf4058e4132edc4058e41006df2058e41006dc2058e4101edf1058e4101ede1058e4101edd1058e4101edc1058e41004ff7558a41094fc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a41006bf4358a41006bd4358a4101eef7258a410f6ee4258a4101cfc7158a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a41004fc7058a410f6ef2058a41094ff76d4a4101cfe76d4a41004fd76d4a410967
  | 20 => 0x4fd711814207ef9201814203e7f755974101cfc745974101cbc745974103e7e545974103e7c545974103ebc545974103e3c5459741004ff7359741014fe7359741004fd7359741014fc73597410067f53597410067d5359741004ff725974100cfe725974100cfc725974103ebf4259741004ff7059741004fc705974103dbd76d5341276bd76d534103f3e75d534103ebf65d5341276bd65d534110dbe73d534110dbc73d534103ebf63d534133ebd63d5341005bd72d534121ebe62d534103ebc62d534101dbe71d534101dbc71d5341005bd70d5341004ff7558b41094fc7558b4101cfc7458b41004ff7358b41014fe7358b41004fd7358b41014fc7358b4103eef7258b41106ee5258b4103eef4258b4103eec4258b41106ee3258b41006ed3258b41106ef2158b41004ff7058b41004fc7058b41106ec2058b41094ff76d4b4103cfe76d4b41004fd76d4b410967e65d4b410067d65d4b4103dbc74d4b412773f54d4b41004ff7654b41004fd7654b4103cfc7654b410967e6554b410067d6554b41005bf7454b4103dbc7454b410073f5454b4100eee6254b41006ed6254b4103dbf7650b410d6bf7650b410073f7550b41275be7550b41275bc7550b410073c7550b410053c7550b41006bd6550b4110dbe7350b4110dbc7350b4103ebf6350b41336bd6350b4103faf7250b4100ebe6250b4100ebc6250b4101dbe7150b4101dbc7150b41005bf7050b4103dbe74d4741005bd74d47412073c54d4741094fe7598341004fd759834101cfe749834101cbe7498341006bf549834103ebc5498341004ff7398341014fe7398341004fd7398341014fc7398341006be439834103ebc439834100cfe7298341004fd729834100cfc729834103ebf4298341006bd429834119ebe419834103ebc419834103efa709834103ebf409834103efb409834103ef84098341004ff7558341094fc755834101cfc7458341004ff7358341014fe7358341004fd7358341014fc7358341004ff725834100cfe725834100cfc725834103efb705834103efb405834103ef840583410967f74996410967e74996410967d74996410967c74996410967f73996410967e73996410967d73996410967c73996412067f43996410063f43996410067e43996410067d43996410063d43996412067c43996410967f72996410967e72996410967d72996410967c72996412067f42996410067e42996412067c42996410067f32996410067e32996410067d32996410067c329964101e7f719964101e7e719964101e7d719964101e7c719964101e7f419964101e3f419964101e7e419964101e7d419964101e3d419964101e7c419964101e7f319964101e7e319964101e7d319964101e7c319964101e7f219964101e7e219964101e7d219964101e7c21996410967f709
  | 21 => 0xf72195420967e72195420967d72195420967c72195421267f42195421267e42195421263e42195421267d42195421267c42195421263c42195421267f32195421267e32195421267d32195421267c32195420967f71195420967e71195420967d71195420967c711954235e7f411954235e7c41195420067f31195420067e31195420067d31195420067c31195421267f21195421267e21195421267d21195421267c21195420967f70195420967e70195420967d70195420967c701954235e7f401954235e7c40195420067f30195420067e30195420067d30195420067c30195421267f20195421267e20195421267d20195421267c201954200cfe76d514200cfc76d51420067f65d51420967c65d514221ebf64d514203f3e54d514200dee72d5142005ed72d5142125be769514203ebe7695142124be7695142135bd75951421473f6595142096be6595142096bc65951420073c65951420963c659514203dbf7395142355bd739514234f3f539514234f3d539514200dbe729514200dbc729514203ebf629514203faf62951421473e52951421473c5295142005bd7195142005be7095142094ff765514200cfe7655142134fd765514200cfc76551420067f65551420967c655514203f3c5455142005ef725514200dec725514203fac425514200dbc7655142096bc765514200cbc765514203dbf755514203f3f75551420073f6555142096be6555142096bc65551420073c65551420963c6555142345bf7355142345bd7355142007af725514200dbe725514200dbc7255142137ac725514203ebf625514203faf62551421373f52551421373d5255142005bf7155142005bc70551420067f65d85420067c65d8542094fe75d8542004fd75d8542004ff73d8542014fe73d8542004fd73d8542014fc73d854203cfd72d8542006f631d8542006f531d8542106f621d8542004fe70d8542004fd70d85420057e75985420057d75985420067f65985420067c6598542115de7398542005dd7398542006f761985420057f75585420057c75585420067f65585420067c65585420067f65185420067c651854201ef66118542006f561185420067f65d81420067c65d8142094fe75d8142004fd75d81420b6bd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d8142006bf43d8142006bd43d814203cfd72d814201cfe71d8142004fd71d81420b6fa20d81420057e75981420057d75981420067f65981420067c6598142006fb60981420057f75581420057c75581420067f65581420067c6558142005df7358142115dc7358142005f77158142005f471581420067f65181420067c6518142006f96018142094fe7518142004fd7518142004ff7318142014fe7318142004fd7318142014fc731814203cfd721814201cfe7118142
  | 22 => 0x874203ef441587420e6f62158742004ff7058742004fc7058742094fe7598342004fd759834200cfe7498342004ff7398342014fe7398342004fd7398342014fc739834201cfe7198342004fd719834203efa709834203efb409834203ef840983420aef92098342004ff75583420067f75583420047f7558342094fc75583420067c75583420947c755834200cfc745834203ebc745834200cbc7458342004ff7358342006df7358342004df7358342014fe7358342004fd7358342014fc7358342006dc7358342014dc735834203ebf4358342006bd4358342004ff715834201cfc715834203ebf415834203efb705834203efb405834203ebc405834203ef8405834209efa2058342094fe76d9542004ff73d9542014fe73d9542004fd73d9542014fc73d95420067f53d95420067e53d95420067d53d95420067c53d954203cfd72d95421467f52d954201cfe71d9542004fd71d9542004fe70d9542004fd70d95420947e76d95421473f74d95420067f63d95420067e63d95420067d63d95420067c63d95420073f43d95420073d43d95423676f42d95421473e42d95421473c42d95421476c42d95421467f74d95423667e74d95421467d74d95421467c74d95420067f73d95420067e73d95420067d73d95420067c73d95423667f43d95420067e43d95420067d43d95423667c43d95421467f72d95421467e72d95421467d72d95421467c72d95421467f42d95421467e42d95421467c42d95421467f32d95421467e32d95421467d32d95421467c32d95420067f71d95420067e71d95420067d71d95420067c71d95423667f41d95423667c41d95420067f31d95420067e31d95420067d31d95420067c31d95421467f21d95421467e21d95421467d21d95421467c21d95420067f70d95420067e70d95420067d70d95420067c70d95423667f40d95423667c40d95420067f30d95420067e30d95420067d30d95420067c30d95421467f20d95421467e20d95421467d20d95421467c20d95420067f6599542135bd749954221ebf649954221dbf7459542006bf7459542004ff7359542014fe7359542004fd7359542014fc7359542134ff7259542006ef7259542004ff715954201cfc7159542004ff7059542004fc7059542144fe76195420967e65195420067d6519542126bf64195421457e76195420067e76195421447e76195421273d74195420067f63195420067e63195420067d63195420067c63195420073f43195420073d431954235f6f42195421273e42195421273c42195421276c42195420967f74195420967e74195420967d74195420963d74195420967c74195420967f73195420967e73195420967d73195420967c731954235e7f43195420063f43195420067e43195420067d43195420063d431954235e7c43195420967
  | 23 => 0xcfe7218154004fd721815400cfc721815401cfe7118154004fd711815403f3f765505403d3f76550540063f76550540043f76550543873f73550543853f735505437f3e73550543873d73550543853d735505437f3c735505403f3f635505403f3e635505403f3d635505403f3c63550540073f72550543773e72550541253e72550540073d72550543773c72550541253c725505403f3f625505403f3e625505403f3d625505403f3c625505437f3f32550543773e325505437f3d32550543773c32550540073f71550540053f71550540073e71550540073d71550540073c715505403f3f615505403f3e615505403f3d615505403f3c615505437f3f315505437f3e315505437f3d315505437f3c31550543773f21550543773c21550540073f70550540073e70550540073d70550540073c70550540053c705505403f3f605505403f3e605505403f3d605505403f3c605505437f3f305505437f3e305505437f3d305505437f3c30550543773f20550543773c205505403ebe5458854096bd54588540063d5458854004ff7358854014fe7358854004fd7358854014fc735885403ebf4358854006bd435885403cff725885403eef725885403eef4258854126be425885403ebc425885403eec425885403eac4258854126ee3258854006ed3258854004ff715885401cfc715885403ebf4158854126ec2158854004ff7058854004fc705885403ebc4058854126ef2058854004ff7358454014fe7358454004fd7358454014fc7358454004ff725845400cfe725845400cfc725845403ef7715845403ef7415845403ef44158454004ff7058454004fc7058454004ff7398054014fe7398054004fd7398054014fc739805400cfe7298054004fd729805400cfc729805401cfe7198054004fd719805403efa709805403efb409805403ef84098054004ff7358054006df7358054004df7358054014fe7358054004fd7358054014fc7358054006dc7358054014dc735805403ebf4358054006bd4358054004ff725805400cfe725805400cfc7258054004ff715805401cfc715805403ebf415805403efb705805403efb405805403ebc405805403ef8405805403e7f755974200cfc745974203e7e545974203e7c5459742004ff7359742014fe7359742004fd7359742014fc73597421367f5259742004ff715974201cfc7159742004ff7059742004fc705974203dbf7655342006bf765534221cbf765534203f3f755534203f3f6555342096be655534203ebc655534203f3c655534203e3c655534236dbf735534236dbd735534200dbe725534200dbc72553421373f5255342005bf7155342005bc7055342004ff7558742094fc755874200cfc7458742004ff7358742014fe7358742004fd7358742014fc735874203ef7715874203ef7415
  | 24 => 0xc00a005000000e012021801000000700b800c00a000000002400e020000000c0200000008020008001000015001c004002800800c00700280e001a0000000164064005002000c000002003000c000006000001404200f007002000001003f3d76d52540963d76d525403f3f63d525403f3e63d525403f3d63d525403f3c63d525403f3f62d525403f3e62d525403f3d62d525403f3c62d52543973f32d525438f3e32d52543973d32d525438f3c32d525403f3f61d525403f3e61d525403f3d61d525403f3c61d52543973f31d52543973e31d52543973d31d52543973c31d525438f3f21d525438f3c21d525403f3f60d525403f3e60d525403f3d60d525403f3c60d52543973f30d52543973e30d52543973d30d52543973c30d525438f3f20d525438f3c20d525403cfc7458a5403e7f5458a5403e7d5458a54004ff7358a54014fe7358a54004fd7358a54014fc7358a540067f5358a540067d5358a5403eef7258a541467e5258a54146ee5258a541466e5258a541467c5258a5403eef4258a5403eec4258a54004ff7158a5401cfc7158a54004ff7058a54004fc7058a5403cfc745865425ebf545865403ebc5458654004ff7358654014fe7358654004fd7358654014fc7358654004ff725865400cfe725865400cfc725865403ebf425865403ef7715865403ef7415865403ef44158654004ff7058654004fc705865403cfe7498254216bf549825403ebc5498254004ff7398254014fe7398254004fd7398254014fc739825400cfe7298254004fd729825400cfc729825403ebf429825401cfe7198254004fd719825403efa709825403efb409825403ef8409825403cfc7458254004ff7358254014fe7358254004fd7358254014fc73582540067f53582540067d5358254004ff725825400cfe725825400cfc7258254004ff715825401cfc715825403efb705825403efb405825403ef8405825400cfe76d8954136ee62d8954094fd74d8954004ff73d8954014fe73d8954004fd73d8954014fc73d8954136ee42d895401cfe71d8954004fd71d8954136ec21d8954004fe70d8954004fd70d8954136ef20d8954136ec62589542067e54d8554276bc54d8554004ff73d8554014fe73d8554004fd73d8554014fc73d855400cfe72d8554004fd72d855400cfc72d8554004fe70d8554004fd70d855413dde7398554005dd7398554006f76198554005ef7258554135ec725855401ef66118554006f56118554004ff73d8154014fe73d8154004fd73d8154014fc73d815400cfe72d8154004fd72d815400cfc72d815401cfe71d8154004fd71d8154135ee7298154005ed7298154006fb6098154005df735815413ddc7358154006f960181541e67e54181541debc5418154004ff7318154014fe7318154004fd7318154014fc7318154
  | 25 => 0x4008000000000c00201a00000000320010000008000018013001c012002003800000600000000080140000008024024004006806c00a0000018000028002006001406800b002000800002c0000090024000000801800200b0008014012000004801c000000001801800000100580000020030150014004005000001405600700280000040090000004002004004000000401a001800400a0010060060000004005000c01600b0008028020000001007c010000002002c01e000001005c00e00100000780040020060000004001001800c0040240008000004002000000c062003000000402c00a003009800c0010000000026010003005002a00b00700000160040000004004007000008400c05b00080000180000028024000004000801c01a00a003002c00000d003002c000002000011002604000a000400a01100d00640680150000010000000002005000c0030030008000000001807400000000280a4002007009003000001900c803c0000060000060000002015802002001500b80080000110018000000000000008c002007009000008a007000001802a016000000000000000a800400a00000880000000050008154004003000002c0100210060010018009012001400000102380240020350048000006015004812c01800b00780040100000000040010002000000001200f0010000000001002000001e000004800800601201880480000000038060000000000000400a00a0000020002007000000400400700000100000050108030000005000811c00200d00280040be0000038064000014013002002600000a000c022000000004000200000280100100030000004010003007800c000000000002000400301380040000060010010000005002002400000600b800c0440020248000026007000804c00000000000280000010000008010018006001801600d0098004048008002000003600300000900000000018000012000001801801600c00d002c028003006000001400100100000080020038008026000007002c00400100a003000200c0000000002002001000c01e01300d8004008002003002804400500a000000200300580100200090030024000000000000000801a0030084006000000800400802d00a8008014006000000800000600300100b60010050050004000001807000000200000300040030000024060002005007c00200300000b00000050000090014000006001800400a00a006800c000000000400000000680080000070078000000000000800800e00e0058048000018002005401e02900300000000000018004000033006000000800000680000120110028034026009008000400a0070038018008002001800c01601b000800400001800e80380180060030004030001008802c000004005801c
  | 26 => 0xc001000809800a05b00780e8014003009800c00200600200d0002002001801000800402980000080000020000022009008800800a00600080000220030068040008008008800c01000300a00240120140088030012004006002800000a00700140000010048000000000001000000c0020088004012002027800400603b006001c008001000800000c00e005000400201400c801803000e005000001600100200b40100280010014004000001000003a0050020000058006031016c00000e0008010008013005000000000c002801400000b01280b8028012001801c00001700a003c04a0000028020004001000004400400f002800004a00b0000008014005000801006a01a0000084000006000003000a0050000094000002001003000808e0098000000008000003001000b002800801000300d002801401400000900180340000000002003001806c000008001801000c012007009c014001000801001400f000008401000c0068008006000003804c00200900e0028004006000000000a004001000403c0000118008022000007801c00001100281180000180000000010002000805000c0010028018006000009000002c000000005000e001000003000c00000d0020022000000007c008000000001c02000b0000004002000002000c00000600000000060010020044010003009800001601d01280000000000100000000012004802005c00000000180000010030020026001001000c00e002000801c00000000b00080060010010064002001000800000401b003801c00800a006006400600100a80000020140030028008002000000c062002006005000001c006800c00e0000008000010000000801c08c001005000800801200080e0004006010804c000002004800000800b00000100200040638000002003000001000000800080480140000060014004027000000004c01f001801403a004003001801a00d00080000140110090008028000003800000800100d003000a011000800000000300000180120000028008006008004001000400000280180000000118024022017014001400600b015000000200400180bc00600b0000020002000002001001200000c800800c000002000001c00f0000000014001001000000e005006800c01400800b800c0880200050004002000002000801001f000801401600000000180000070018018000000000005400c0050010028012006000000c02e0000010000038000001005800203c008800401e0030180004028001001003001e0020010000000011000007c00000b000008c008003000002402600c0068028000002004000404c001004001000200a003800003a014000002c034003005000800c00000e8000040003004800400001f008801c00000701a0020024001001800000400a
  | 27 => 0x2c59b2a147800038f0b8c624daec12cc334225806e2f184b833ec0000000000000161244f5c840000ee610adb1c0000dfe2ab9c3a26405141241d32000134542598de07b412a3fb00002ec0ab142f88b24be90f26a3067c3bc07940001f646b591d019000007ee84e83ca800059f022a7121c4c00008101eb13906b7077207086d653b9126000024248d80000f293b113aca6049b1f0206794187d486146f30d2a59212060cf8c301f6986019180002c8968221a54c602a400059001c543580008419eca762c00031a42461ad810c7a7856c12e477b7f7934c5f8d42c31b981224195ee83c14c05938d648118000676800000015531819d967d452b03cc938a3081bca00003480400c6f6878e3e0fb88846f88f8451f9dd040f9a1a05cc4a00000a786fc828650d9d4a0001a54000052e7a400001001872077065a387176840d857e4d10ada0001cbc00011c83fd00007898000496898c000016869298c000007e022a00002ba9e2c6f90df20001b025071b00222800007418907419d1834b918882594865fdc000748a0262d59c221d71569348173c542894c0200638000044c0000f135b693ce4225dd21ae8f685814e4c42b800084d0d6e30f00120130c8c1b304c464593d2029000000000003ec1e0610dc0a000005ac12b996a82d80002420fde000000000006fe3bb8000804000053200000001f0e000086200010d01a2c6264b6057001a02680001e4c0000000000060000000000c30ec64f01c8b544000064d80c6000046c3e98f9000000000001392000000079a9afe000211e4f7c97a227800052080007bb0000001007803400002b0048000018002000800c00c0050078000028008000000801a01d001800000004e0158010002000000801000e00d00e0004000014000803c0040050010000008003004000000200201180580020010020004004011001803802e024009807400400000f000009600001780000000120020000016001000803c03201600180000060000010098002000000006801200100000080020000040034002000000000c0020000008014000009005800002e00000580280180040008018022007002000401400900180640040000028000008001006003c000001000001000001500c00dc002001002800c00200100b0010002004000000c000001003005400c001001800c0160000010000004000010002400e001003003401000b001003001400400200a000004a007005000c003005000400c00c0000004004000002802c0060000070034000000001803c05400800180000060000028000024008000000403c030002800003e013001000401600c0048000006000003000800a0120020014018018001804002000301a8004000009000000c0020010018074002002000001800600b003807c002002000000
  | 28 => 0x2f10108f86e30acc4021fca5c2000053a8000343027a6410bfe3560cde0a993f264f000056a141e14d863c0c50f36000023c4be0ab702100445491e42779200a52215c615a20341b99f7e7da1e181a2028017d030866c177c62a99e257bdb8a095080621295d25b0055c1ce80006bf553e00015f15a720e60000c084b000006e4889a0000000000050850b8c606b38d40675950e6650a5c5a81b4038d60625171a8e00011cc6939b790001f046059e466b5000000014ec4eb80000e206080000ac625487777178f8e13b8ed01cc8bcd7ef0d7a515800061120140000000333057110492b4159cea0000000008e80ad05b8eaa2f50000391800004e0e0040394ce1ad147725898e864e99fc63b8ac0508800060880000001a5e46a8000000000073d852c000000008f800000000002a41a440000e5c3459cbf0001cff5a98d9e000018455a815643686fa12684520c88ce80c600007a803b42a78f6064c820e0eb400013b00fe1959f3c3cf2130522901c83a9d2e233959e11c807e47b1f961a89f2281605403f909c4785a0a015182631590fca33ad4921329c2e558130856587fa6250f1c4cfa0767c7178c41b92be3f050ea38fc3d52d98ad444714ca074d87861b904a2121cee84545767be000048a116050f800037680003bb002a02e9c201d313bb57880002fd9b782a30d623ac1df6013dd8e1f8899237009282570ee80e4976a0a402c21529ce87a181d8323853c0eb194207e89345e51d588141e0c2b584477619b4260f14106f5000000000a60001ee400000003c7902a32287c20b38885446943400006f265400002e5800007185500d0d6b400012990000a425e64ee02b4136a53c80002f380000000e02543000000004151b9400040300000000000287800000011903c9800067500000001e920001f9e52a00000001a74317848200000000001bba3d5815a0ab81d612c18a200000002ea1cb96e90f7e02793980ac14b282a80003ed800025b099822800000001d0e00000000002098445a0d678d80002e9800077a08f200015540001c8913d81f06808c6874a81b52e91f945d205aa05c51f87fe0afe51a0e1e16d95441c6046a576169004298521b009ec714160e79986281120db81248cdf27580001400f705c7988644880002a590aa52580b0116c0001ef975c342a04c00000860001bb80001fdc73cc45808d80000001a7a2608a007f88000735800017500005148bc82540f4652f1e124c9120e668010816bd91a374966c01d0d8a2bb99585f689d8809019258c0bdc00e929302d9b345bf01065a18000161010484895b01e086c20c28d1a45f16286de826760915fc02fd7907d180007e7083e2a11da47901cba0f011fc1379bd60001b367928f4012c979e60b80005ea8024250803d49b855472d8063000000000007501711dac00
  | 29 => 0x6210067428dd821c96840df87d06600958007014a7c180002f080008301f5c0000b8e0000fd8000031900018fe000029840c89da2ab15a60000000000208e55917e000008542ea92c400000006ff800027880003e90000216a0164f302ac5f412f470393160000000431875400000002538c5214e935a61b0a646d9811935502fe48f1e983a09cf24d91b935b50ac84dc05730000b703a500000000e6600016721088000849c64c68803e6000000000004ea10c0ef800a05dc34500002088141000211224f000045b8b0800012a043b147a4bf1e584cd8f3830480041fe1b5415788a50d8026622e891422f1fa660782344a218c83201fae0d60eba08991dc7c7de5e1b2098a265c12c77980000001c5834c96787ed9a385ff9d3a49a91a247394b03a000002c094f8000000000001b20001d5177500007c20b54094210567381de8340ac25c897bc5140a662f3d1ea14600022554e706a41a045c400007969e7e40b1e8c4748945120cd9a0d183b276403976fc05783aa4f3a00011e437f0d28109400044800006ff087a45785fa2141fd458d9ca42370cec0000ff0000122a0731d0800000007a200005aa9880498091a0000f807dacb107e6113e6438152000053753f1b6419e1d004d0508b00016183d704266168d344a007c05db0c4e1d19b864241b064ca8a4c17806580001d9e16ac9403338b6000000005af8b780000a2252c46ec000052839a09c05990b2400004d848f80001ff945b69d87667b89d4200002f847b80000000a6a1b4800019700007440e5413980000000b0600000007b78000000000035295f2000068a5e98da844285c26269a86228d5484d5c6620c417df6380d8c6530d8e3f8043457389de2aa90600fd1aca00008e869c8e423a7138455480000000b1200007d868513963c911804b59d747239f184e200001645cac2f9cc864b4930665c81d41270dac33e97c600017f20001d6063e0000792056e4690fa829200000ba00005c0800031700f06e80a4440b8e795770e0604a1fce7550c980e782dc0000000261005067ce0c22a902a455388283c5201a00009703ef949c7fb99767be445a0001cb20150cb0635000070a0000726918c058000083500000001dc882f1aac2598d423c618d64de800051b093210617c46c40000519036a42d80000369d2677f00003f182166ba84aa79b89563541f1a78e0000060212c0f620ce039c00028280000001a8041d8000000089c4f1950076e008962e1d0c662988562f0b984eddae022084ac3bed750211887010e162d0001c7a0000b7c56f8e8a25d03664301c9e3728b1a7a99a344de00f25cb16ce6d20dbe5d09a621f980bc69f0000000000023016fa0001c1022990563a613fc44d0188343929a5ba20e484106bc54a09fe3d142ea3248fda6fe1abe408929e28c40c379385
  | 30 => 0x3042b1c7852d80fa028882a4438b1e06cc3a41c885e17868ff80e981253b38d9c1db0fd61291ed25cf8f106c819d00b9846e7d64ae22489a704f95c903279b705a89a300cd859a32a4bf244097f4538194a3199d6662e855222b028233003bd6d184860254fa27dd128441c0d366cf04366a889967800d105c813d410a909959d96b83c214f03130dc802dda6811a0c5070c1b0e1fa07983bc8c6c09b899104c9376767169679c93aa0820da40aa0d727660b3218c000000016e20001f4a176019766b1cce20e0b2e7bc8caa5b3205607cd7b600014332ded3b20241daa0a585420089c803ca012000014f40000a0c79919f24da07145f5980c31099083098a46000112e25dd8a861012a470701c80000de069712b800015c80ee0df00001f816558000000048d1170bb200005c31fa859800000250dc011700015703858c70332974a1229d5c2e004f45af070c4df8de251b89be5d1800000000d42d00cac56d152d55b800000000004061b3e10cc000136800000000001b693de000038258a800000000004fa903a6b19f725b6000084b83fa75000000000000000000083b000009c1d943938000000080e0000c186e508e60001afa6e89cd875316ea2749c1400006940f799492fb40007f5800032e00001e209381678154632a1036199f213e68db626b0000729c0e07bf1ebe64b0f123979d8271b84fc1d7814e4e9c6d4000000054f0d3a70e0c0a00000007f90000720997434f81261b783500c5a0be00007fc000000055c40ce2148d5e00000001950c384db8a405c488348430ab47369e940001a2800013ee37500000f1104061709a60db0d744160f8a6fa17f684ad3ba3f4800010f07620b783e124c16202160f6275e000000013ca4d78e966e0c9bc2eb8e1224a84e23c810286c60e4065483cf25110447288ec220810e65fa8e9a49c80004a8800045d8000000126200017de30303fe4c8037a581d14a31284d637f494a6990bd67ac000000016f632b860a0000b762061b2852d18f21c0013b3db872c32f80000001f65023841e165181c5ad8cd02fe8e8847780667fc10a652152e81769bae5ef86742cf94e4275097869300006db13e834497543f417847f41e240000000000000024094c2000040f7770000046c33a2d08f161d5900427a186a1a79e3c3121876169069675889f447d135233c003e121400003d9c6401b17ce185928e60b0f8c05795ac11f1d7029f8ff26b60ff603783e226780006871216000191001b471c563111d286cdf666f000030e871e03713f864d03d214e54d614918950001fc8000185407814c4389066c00014e65d7425a0000000471000062b0dc6000124204e40001ef0d15160890a0d5170d5c5915a7aa0000544587400015162c3d49a00013ec1bc1d6e8100174000069243e98642da0dde04a5bec1
  | 31 => 0x36181d50000000000072600516523dc94003d6022860d1ab617192ee63180007610000000000082e09545768087248212a7f4910800004be7a3989600000516d41ec258f9b3005e0000000042c15e9cde178c3a3501204e555977665c00002e71d5a6bd039c4bc16b23de98560dd1d1e09798e6349998438dced25cd0daa4511c08845c4fa62981340468d1e3ed08142291c8f4081e5455018b40799f8236b95e65970ca0049cb6e3f89fc000011a8731183227d96446f000000264cfe7cec00000011d8000137c07b8b5265506f71735858156000000000004cdd47246680004a3db44000166a3d0844a4bc9e8a1ee812b550837c1f70000113979c28c1e78000000032590680001b8017291d45fe0a341298708320448732710b24658b1849507860c1121a698000008490a8000000010300007ce071a5db808200009fa000205e5108ea658d00007ea8e103a19cb84ed11c23088e140a50c8b7d799e62c4c2625d78fbc04704d0065451a336977e27a940a7b313405e0860e80f8c340f90da006083ff3759b623208fc431919aa6cb08860220b462e480003af10816db8000627059d193960260815e738200000a121161b29e745f60d1c274139116b400000010987e4178853403a865f04402239bfa2ff035609c800000000000001f4474f92b200008120000b0c0cc8ee4130056600014442200fe8158a06a49795880000a201d3a0d236dd0de68d818a46820cc093043e3f980f134e068d4cc00006e6800055b12960d7864a7ad835c47fc0e62ac816214997d2000000070280000001e846a1138602f8cee68480004201cfa12d8000305a09c5e1999865b1fe65d4800003d041044a80000000afc000124c000000021d15a25408fee0b0183773519e85b087964d70b8a5ca1f8044f13c26ab98b0813413e12f05be1ce12782ac166200016562c80dbf467c4245cd850a78cc7ca0001ebc0000ae81459b723e098921698d844b518ce0cb928600015c07718a684cd1aa84d088fa42688c820791382e1140c0d90e2680a99e000004c81b40c1e0dfc0002db11b854e147107f02922d7848f35f06914329b0c0021ba6812c7d682c097c08b800076305c525f8f001ed99647cf8a6273c1e1e56e888c81693322ed80185a220325420c7e58281425b206f4135000037d4e0e51c0c843ab158460a99901f48a3a57f9d9726343ea1d4927b3f207808150b7a583dea279f045906e9a9262da0804701412565083a5c50ce77be8e5a3d685f22b48bc0000029a20d817638b9174036096a51140cd14c90ba05c19ae3c30199499209a000021c08688fe61a0be37ec83901a30abc660809c47f4a7a5d5870e00017603ffd128144dfb40d6487c45987120928f660c6c3f663120222f781e86260a95000004052b94cc47a154a5d88d8d6aa80001ba80920001
  | 32 => 0x7d444421084249310214dba86bba1181f200344238a3c64a08ca74710bc4881282097170c1ac05b225d9ed620280000ad06187b995e01dd877d3c3916a4ce8ed67a089fc40f185072b8e3081c182560a027c70788c23d7865210fd87c4b28a866890fb764e1aa00354a561c29c54519864443809b231d54947b70bcc014881614494985ee152219e94f6485168c46c006b3e707744d5878e0ae188e75108e019b95b838e90fe46f04cc4199f6913341a634b107f428928a2a08e60520047473882ec01c852030910f06bd9d4606605c731d001e42e213151284ce7d319a64870496342c1ae4ca086b7760a1c18d1e966c20f0a820a0385018406337146029f15f406f00c46729d88849449418d884004f1c8a848d01444104213eb03d01558bc3685990063f148e17e15922cd041401c081a202020400000000d1084506d09dc5f7016c2638401000153a0a79af8000096e39d95d62891c06694821837982f43cd144e000107e0fb60a284ccdee5f503944b6a09200011480001ee045c05b104792922f280001c58fc2000050b00012a8583159a3599a8a114c6dc65220183460748133c9160da12e4217931419a84fb00020ac58689a874692086b79aa6354870655f04446e41a1800006e436f0d7e4ef9ebf83c9959701093a7b5147c19781b882a0ffc2d904c91188fce7888f887811f710001bb24cf053071f8b9a84719f070985e629484a24b7974067a97c22f4922c295d1462708bf87e396e42abd8a036509ba6ed0bc5330896855780fc51a89a000984ed7dcd608417977800013a631edcdc23608900001e286818adc76b4a0e117800068f9ccc6a212836b010c2000000070005690000000000000006881aa000076e8441c44000000066e205d1e412ec23306c62ef93e4609883c57d941400000c25dc000039e125279c1b4a2ca9a6e0e040001da1f2e2d290c44f980c05bc8aa064b89007bfc8b80001fe06ef854e52e9fa268b188403b13f600010847c0000076d8c1c3a785cf41a86f87b10c2c2cc046334f191458c8e8c35f5f780001df02249a6a00008ee0b18a1800019c408e1ef4000127400010380000cf16f4175f62900e40000d5c03e0eb8000208c117402e0001c3458e8d6071283ec58b93800000c9957903985c98000836896d3161f2a57b18494e39d8a5bb80004fc09ae00007a20001c4000000000000408434818602a13da329200b33a8c907780d8038cc7783868cb654b16d20ff1222396035b50f16ab80c028809a816570c915863a956b19f93e34c7908671387b455e07ce3de0000000178e5e881d249005b807b0ade82796604ce13468025ce4794003239887a05f303f27ba139a43e08ae6f10d044ec1d346500f447c30e6e5ec9fb82ce8210051206675f93fe013936039c8a1a47f8a4a4c080000000904261940e
  | 33 => 0xe77881fe0000dfa843843280798617c342d436e8000000000053f9c56131941a83e838a46090500000d6868a93a05230d5a65e21324dd1ffe2579088802000032148d267916de6838f7435393f4000000014c4e287f6054478b80a34291ed048d06fc59a1fea6a500007b61ad235dd1a615306ce1aa8da200005d27d00c441d686862cf0000081800064496943ee0e74000026472c00cb3621fe824780000001d3800000005890000601000024f9b4f000000076b800000008b4000202800014301a8113200000001b81326000000046d8000000031c000207a3e500000001f1402e1e30000005a3b504162b98fea6df80007bc077a59f816365b825900010e84c890104a608c609e1dc221b05f084bc2b26ae97ee49d8e39009d7742c29e6c0000116726d60437420845844e4d52400005b417ae7ce876a2a25dde0e6883000000005e61b56032920a000038e61880000000000000000018a94d46580ae43c8e06439e98d20001b2200003ae31a99ed07c9fb07949614394079c4f200b55dc8000107170e00010b400002144f109f82ee955a6e611142c715d41440684132d5c20000158000047041c82584660c7818111d64c0116204fc6a4209018c1d61b88666a102515086e06e431237d0f0600002a000010a030c84640eed42438b1d14722020218f83f014f990a47284f70000000000000000000000000000000188a7548bee0000000000118a0f2c0000001c5a10080000000000000000002b80006f98000000179680b0e8400017d3000050f74117a40f217e6000000044000006dd8324000206e5599e9c64887046619b5c8220efa4ef00000000000000130a2d6817c494168a489827e0000e92419158a72192f600e1a6673401ac18b089400018ae7ca16665b598da478118e2bc90ad000000000003b6000000013806987cd1f7c52f8000000142a3d215ed7d51f8a5818df777a800000012481069ebd00016f458e0ddc15d0fc0637016a12dc48079d9cfe0001a46000056000b0be05898000495840b67b1fa8441800024da0c8000172465a04dc4430d053cb1afc2470c2861c07e40001e6254d1d300a705047108f3730d80007309d6a00018140000eb66571a2235a99c8166cf982e180007bd83a06d6032a103828a00003425601cb42460e180ad800066d0f500b10edc72f85a262c97ac5aa1dba06f82241ca88a25c6a04a043801041080000bc1da677e01b7511974467e09724b709107b18548036c5d0382872445312ce71c9ece5009bdc7dc04bd64f8d0219d9db304e80000b304f81260b6a02b0000000117a77584f22c9800000000000c389640000f2d06940004d280aa5d31a326638a934e14aa6766800000002d882192a9329800000012122e807024c121140c199c00000bda6128a5413080000f30a673c240362e51d64388
  | 34 => 0x4c34e23d0fdc50992ea10b4a5143508981a68eda04f472e038934800016ac000038f61e400005987364b4000000006800000000544800000280001a40000223c0000001e3e73b06b8022927f5419daf0c802be8428c885c008a77ac9c122899dc4357e0c66961cc76778d2437a147403a165028b05bc606927a14edbce07d02d65e681c428089f20dd8538182400000000001df18e466580007fb09c64af00002e88ef623111f0482dd507c812890000742557175a334916c1d2a0f87a6800033612e00b69e1c2438b4c00a5a0c34203006e7147b379000079806660000ba900012a600012fe2961ada4c30c2e5b71a26000163c78281302c00ace518cb74596140836603280031f7629b9eea1de59ee0000d906231caa2f61fbe50583e01c8000048b88fc2ee000031dc2e415f1e517aa8a6f17d983e6ac0e0c16812681575db20000fa029c0000000005c068cb882ef0000567000070a99be25bc2e27eb01945c1069512047ec52adb2628210780d483ba6c50db2668800063149e00be952e797057246b0f76000085c16d0000776863a000000032a1bb97e1000038a959000010467ae1698373000033d800046c90341ea9f0a50a13664550ad8079000077000063c110f400003843f314aa75f0000122000045a167a41700003afa1260f3922452880003269ac274a0eb20e8507a70685ae000058f59501ea2ce19202fa1c983ab94386f0c5ec4fe98182ad8a7176c09f03bfa1003659f8c39b15583400ede7d6168070d80006770fcd0001f673d900c802d082e7298f6c7d3974e28a0ae0633056a55a0420724958655188d613f85e8597850651684f900019d848c8386700a0941a3909e11820480b49bf4554100008018820000620000000048785c06aca03a844ca2a0001b96182c0006e7a002000000013f581000ece343b60cf24db00003b28a1457403020000ef4849047e00000007728d06492817251786327ff000014ce02e00020ee32f03a25f2000014a9dec5e492c82c10e6484a1fcc00000007d8a08a0001ff66cc8000000000043b800016cdb7c05e88de81d0000000000036d1ea400000005c700007f68dc200000004684aa255f8000000002078e80000000d485d98000304005e0000b50000135800000005ce140b000086a4091be01e11fa45b120720000d70000206881e0856725920c21350748404af076a10160001a2e00000000000a94718822c432026c80f082c6f21ae62601c2482d1f8800009603119478000078c00018c27db000036c06ee1f181c361207a8000184e0000e3600000df6fb83c677f819c28400004919d48000000012383aa0000000780a01c67d1ca07d9800024988e23fe8bb466c9aa41cc18425cc0cff15697e472305ee0a319c20f5194e7480a9a1e693ac71d909c000092e0001f0b000045656d8b0
  | 35 => 0xc600004a861f81a0399404666d80d230693e23009178054042e0260aca064dc700ef8d443e18aa858b04bb7bf81f666a009608892703cf961e0f7000008c060c00008d02569440000125c2f416920000f2e7060a8821e1b687c58000423c00078a8c001890cc4000000003405350530d30000183852119c6000114e000191800000000000d825cb89124250000446177a07a5616297800000008e4243066028596e64c600770460000000112c000180060e80000001eb40000a6c0c69926788180a00000002ae03400001ef76d3400072a0244000000000006112b10c5a190800000000001b6073e47691f271180000000058052121725e5b244670cd425199926ce94a62a7061051b51567058dad639d69e62457320ef0000319d7fc74584467fc87733ee967413907f20f5c000819c000757886858cc48b000044f279001652b061a5c285c11f7812227301bb3cc1acc000047676820f671f02a201d9902088000e000000048e8b7e0c0c36e1ab12660c98ce043d98e23558f4e2fa991e35198ec3e58c045f29fc421f8a741721abc32e9d1246514351e996106c79a5a7851bbc70f136209580006d317c000000005ab88ec7198000447836268295f000006ae414913a000059c1ec000000000002099f6e420943a64180000001ae801919620000c3e16a0417188843d560929c8018b140000c7675d88b0000025b17a940d1990d735ea0b2853a0be21230000000028e0001f7a0000b3633e000039a81c00e307925680e52000000076f80001628f6a5450c0600016f8049143148e206c679d0260dc916400015132fc16e06178c7a04b938c59193a8000132e00014e200000007da82bc7ab88da6fda11a5fc0ce26a71b1a0b8053d2eb11526ec09c800017184e715302009c9c72507285ca931a73e0d4c00003eb072952a1ac850c6ae166e000000031cc0006fa89ce5a920441c403b138c8ec83b01b04546964265685904f0c9ca56f129468f005671a878a6940ea861319242190000546d2ba83d11ae0001f9200015ca41518d000000001ba12e263e800057e06c433d15b2548151c3398b2c7d2144c000084200020a6000062e00014d80d3000032d000057a800037392aa80801460fe108a6da8000619415c19405ce18783b000000b24e79a082e7447a364858c4189dee4d1cf222be8e5626d9da20b2901a30501156e1154c23d806047d80623f5107c5474a8a2d613cd26507b855c97b412260fc14711b400000005fad98c6599d4e439073c0000a123ad0fae2e4068f46e803c09d9b1233200001a992b60f5853463d19f6000000000000005281a10000115c7181b2e5080c0e2fd145881482f60980232000157a4b987640449dbc5ec009417c48006510e7e25210ce3e7a0b23c08000134960044c0f5200000008241bc67e1800000005e45c
  | 36 => 0xe2800006c1290464800066e807c3b883e867301ce11085227e81a7e13c1df26df4e3800000005710000000099a83f8b5c17f0eea1fc004a2d21c0c7838df86dd073457a4a4e80481140d69ce6114004206393dc000190c2e09ac45bf846648415046c580486671ae257adf1e4508be6527a0ff39f087647853a2235000045f997a2031cc609209aa1435ec073f0988461003040782f23ff9af20001a6c7bb800075e805f52351c67cb16f0755800079100006e09b52213943270b1f50491200c413831e46192ae0b213a40659b8e09383966b4092400016c601ededa70f96ba00008047ab1ffa75c9f3607e1a9632519a40001943210ca764961f3200002ba2968f293319f566f68f4a760200e0900ea4172df7f73d14de0668bc42691d9202311e24c39ac85fb20c40c156ca035935035e084c2bd0a50121180e3a4042817587600bb85e27cf41da2fb03da3bf0e4479e80a11d0010219202d06ce10fc7fd170f00008ea73a9baa6c28c5400008444c498f038893b83b106a30440000115127c5fa0f4c7cc01905bb0b7235d969a7409c740000aec732007a4ab0bab4f58a7283607441fd12043489d3c6679f427b20ecc2688a3222b595e01e0af819c91e64b3108c17780001731efb21813bf48018883c693d87c99f1218480ea55450022199fc20cc09b46d3929f22217ba28d9bd25499ce078c9f5a6a799466d6928c64c14dc4cb09ee17f8dc4087930359c1764450000001a8cd656a9bc259690dc0001f9a37e5d2c40495980001e6819a00001aa07ae2a2d17249380007a015de44498a553e987a75b0dff4c715ae000000084b53b346f814064a9c9316390d844455742d89518000119e00012c20001af083700ee78413822bd9b6080007cc000034a7c900000001cca6d7978009485ba5da4e0402686826748be44169f60000032c06a1d36000205c0828fb244d9a820830b4e2ae840a0000e4760d800000020ba45410b0339055b67c5cc0601839b810a12082b900a47e8cb248c0b9e54d877e5d61dcc616d0e2832800010e93d009d207c84a5bac5f95532000069c0001a5600000004ed9ab416c00000000000000000058700005a380003e496294dc888d0001a42279860212d0000000067017ce0e86a68a2e534a07e12d56b01724cfc413079e1bd97e26008000267050e60c02aa5fe8a923a88a0600000003a3817e2a01bb612e80e95ce9a488010887078858057e87ee1af9448588998823c197e0f08dea0bf0449164a0e03101bde161849e140816459320e2782127e0cf0f540000abe000189e6470c2a6b915cc00000002d10e4a63d94b800000000000ca200693e076d1bd804d80001fd94bd1a4c61c67f957656903915929df40de121800000000001a7800000007f180000000000000000000021198180d6c00000004331dfa06d92
  | 37 => 0x1c5c31580007148c6200000001f115e800013940000a3e000000031c86e220c80001ec98460000000000000078d1a003920000369958e00003381dc0a6562f87a4033000068e838028e1a40144400054bc3414d50000207151e602156222f8a8e37b1dce536a0a47c41a9841214624235d683df09b041b0a984d39eba74912020f958d822d88aa3ea80000000a0411e000079581a4000112400009b851d97a0000059624b1c6c71a20de008cc7d5c19cd231f19fa000203652900005
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe1d5415163040e95af02b92c60800eb52057258c100054f420e4b182000a9d841c963040011bd0e212c6080023761c4258c100052f42884b182000a5d8510963040e75ab03382c60801637a1f2058c100046ec3e40b182000a9e84c81630400153b09902c60800eb5a042058c100056ac0840b1820038f4815cd62040071dd0f992c40800e3b21d325881000537c2ae8b102000a6c855d162040075c902ba2c4080029ba14745881000536c28e8b102000ace831d1620400159b063a2c4080038bd52545881000716aa0a8b102000ae7815cd62040075c902b9ac408002aba10735881000556c20e6b102000a6e8590d62040014db0b21ac408002abe1130588100055642260b1020008ee870c162040011db0e182c408002aba10305881000556c2060b102003ae6810c162040015cb02182c40800e3be1d62d081001c76416eca10200087f855d942040250f90abb2840800e3d20576508100043ec36eaa10206cc3e64dd542040018bcc7baa84080a31b98b75508100043ec30eaa10206bc3e641d542040018bcc63aa84080931b98875508100043f43ccaa10201287c8799542040010fd0eb2a84080021f21d655081001c5e43ac8a102000c3f755914204001878eab22840800317dd563508100062e3aac6a102003cd47158d42040071d90eb1284080031bdd56250810006363aac4a102000cb564dc542040019aac7b8a84080033958b715081001e6b38ac72002000cb5645c640040019aac6b8c800800e2f21376500100146e41eeca00203dc3e64dd540040018bcc7baa80080031b98b75500101e61f320eaa002000c5e631d540040018dcc43aa80080021fa1e65500100943e43ccaa002000c5c7399540040010fd0eb2a80080021f21d65500100062e39acaa002000c3f755914004001878eab228008003271cd64500100a46ec36e6a002000c5e65dcd40040018bacbb9a80081572799373500100064eb26e6a002000cce62dcd40040011bd0eb1a80080163721d63500100062fbaac6a002000c5c7558d40040018deeab1280080031b1d5625001000667b9ac4a002000ccc73589400400717b08bb0800800f1d9c5651001001e6b38ac62002003ce67158840040018eacab88800801f2d99171100100066ab1ae22002000ce5625c440040079ace2b1c400800e3be1d62880100066ab1ae31002000ce5625c620040019a8e7bb220080032de1376440100065a426ec8802000cd783dd910040019a907bb2200800339e0b764401000672416ec8802000cb776dd1100400196eec3a2200800335ddb73440100056b43ac6880202bad48758d1004001d2ee8b1a2008003a51d1634401001e6bb82c68802003ed37058d10040019ceedb922008003b158f724401000673bb0e48802000da4741c91004001b88e63922008003b158c7244010
  | 1 => 0xd0db9a808800317d9773501100062e32ee6a022000c9f64dcd40440ab938c9b9a80880033318b73501103ac6f43ec6a0220318dc87d8d40440018beebb1a8088003171d7635011000637baec4a022000c6c75d89404400199ee7b128088003331cf625011000672316e2a022000ea862d922044001d50c43244088003b218b638811000d75436c51022000cea76d8a2044065968e232240880bb391c762481100065a326e29022000cd463dc52044067970edb2240880cb2e1d8644811018e6c3b6c69022001ce876dc9204405d9d0edb124088002f460c7148110176f1b90e290220039e88748520440079d0ec90a408800f781c5214811019e5b3b6c90822007cb67619210440639acedb1c20880bb399db628411000e733b0c50822000ea46418a1044001d88c6314208801e2fa1e53990100045ec3ca73202000e1f5394e640400f17d0e294c8080022f61c52990100054f418a53202000a9d8314a640400f17d0e194c8080022f61c32990100051f428653202000a3d850ca640400117f0e984c80801e2f21d30990100051fc2a613202000a3c854c2640400f17d0e184c8080022f61c30990100051f428613202000a3d850c2640400155d04184c808002ab608309901001d5b408613202000ab5810c2640400f17d0f904c8080022f61f20990100051f42e413202000a3d85c82640400153d07904c808002a760f209901001c5f43c86b202000a3e8590d640400147b0b21ac80800e2f21d435901001c5f43c84b202000a3e85109640400147b0a212c808002a7a0c42590100054ec1884b202000c3f759d5640400187aea3aac8080028fa1673590100051ec2ce6b2020008be8794d640400117b0f29ac80800387d4e53590100051fc2ae4b202000a3c855c9640400756902b92c8080028fa1472590100051ec28e4b202000a9e831c9640400153b06392c8080022fa1c52590100045ec38a4b202000a9e83149640400153b06292c8080022fa1c32590100045ec3864b202000a3e850c9640400147b0a192c8080022fe1d30590100045e43a60b202000a3f854c164040014790a982c8080022fa1c30590100045ec3860b202000a3e850c1640400147b0a182c808002aba08305901000556c1060b202003ab6810c1640400156b02182c8080022fa1f20590100045ec3e40b202000a3e85c81640400147b0b902c808002a7a0f20590100054ec1e40b202003ab681081640400156b02102c80800e1fe1d65950100051fc22cb2a02007c3f76d52540400187aedaa4a8081cb8798f549501038f17316a92a020038bc8759154040254790ab22a8080024fe1d54150100051fc32a82a02000a3d86550540400f87eecaa0a8080030f5d9541501037f0f31aa82a0206ee2e6255054040014bd0bba2c608002976177458c100070faa4a8b182000
  | 2 => 0xc64589100146f436e6b122000c9f64dcd6244001938c9b9ac4880033318b73589100046f43ec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100064fba0c6b122000c9c7418d624400f17d0fba2c4880030fdd774589100061fba8e8b122000c3c751d162440051bd0fb9ac48800327dd373589100064e3a6e6b1220008bf845cd624400f17908b9ac4880023be0973589100047bc0ae6b1220008de871cd624400193ee839ac488003271d0735891000657ba6e4b122000cac74dc9624400199ee7b92c488003331cf72589100065a3a6e2b122000cd473dc5624400195cedb20c4880038bd97641891000754b86c831220008ed8799062440014dd0b320c4880029b616641891000557424c83122000ace83990624400159b07320c4880023be1d641891000537c2ac83122000a6c85590624400159f06b20c488002b320d641891000557430c83122000cae761906244001c5eca320c4880038b194641891000754b80c83122000cce76d8c6244001d1ec9b18c488003a3193631891000764b86c631220008ed8798c624400155d09318c488002ab61263189100056741cc631220008ef8758c624400155f08b18c488002ab211631891000573c0ac63122000ace8618c624400199cec318c488003a3d90631891000746320c63122000ec58118c6244001d94e0318c488003b25c0631891000573434623122000ea4648c46244001d88c7188c488002b9219311891000752322623122000ec4634c462440010ff0abb6848804a1f21576d091000c5e422eda1220008df835db42440051b906bb6848804a1fa1776509100043ec2eeca1220028de83dd942440011bb07bb2848804a1fa1676509100043ec2ceca12200087f855d942440250f90abb284880022fe1176509100046fc1aeca1220028dc835d942440011ef02bb284880021fa1b75509103661e326eaa122000c5c63dd542440518d8c5baa84880021fa18755091035e1e320eaa122000c5c631d542440498d8c43aa84880021fa1f65509100043e43ecaa12200087e8719542440250f90e32a84880062fa1f64509100061fbaec8a122000c3c75d9142440018beebb1a8488003171d7635091003c7743ec4a122000c6f75d8942440018d8ebb12848801f2e19270d05100065db20e0a0a2000ceb621c121440010ff0abb2808804a1f21576501100046fc1aeca0220028dc835d940440011df04bb280880063b20976501103c43f436eaa02203dc3c64dd540440018b8c7baa80880031b18b75501103bc3f430eaa02203cc3c641d540440018b8c63aa80880031b18875501101e43f43ecaa02207787c87d9540440018b8e7b2a80880f61fa1c65501100943e438caa022000c5c73195404400187eebb2280880030f1d764501100064e39ec8a022033cb471d9140440ed1b
  | 3 => 0x32220008bd87c80644400147d0b900c8880028f61720191100054f41e403222000a9d83c80644400147f0a880c8880028f215101911003c5e422ed2a220008df835da54440051b906bb4a8880023be09769511000c76412ed2a22000a3d84d96544400187cedaa4a88801f0f1db54951103970e31ea92a22071e2c62d5254440051bd07bb2a8880023760f765511000c77416ecaa220008ed82dd954440011bf06bb2a88800a3720d765511000477c12ecaa220018ec825d9544402517d0fb22a88804a8fa1764551100046fc1aec2a220028dc835d854440011df04bb0a8880063b20976151100049fc3aa82a22000a3e8655054440014790caa0a8880030f9d9541511003e1e3b2a82a2206fe1c6355054440ddc58c4aa0a88801e3d219711511003e5a322e22a22000c9e76d936344001c3ecbb26c6880023761e64d8d100052f42cc9b1a2000a5d85993634400153d09326c688002b3a0a64d8d1000566c14c9b1a20008df8759363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc82593634400153d0c326c688003279d864d8d100070fb28c9b1a2000e1c65193634400153d09316c688002a761262d8d1004d6b436e3b1a2000a5f855d363440014b90aba6c68800387d5254d8d100070eaa0a9b1a2000a9e849cb634400153b09396c6881e6b6a0072d8d1018d6cc00e5b1a20008de8710b63440011bb0e216c68800297a1442d8d100052ec2885b1a202bada80dc763440631bd0f906c6880023761f20d8d100054f42641b1a2000a9d84c8363440051df0e996c4880038bd9764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000717b28c9b122000e2c651936244001d1ec9b1ec488003a319363d891000557424c7b122000aad8498f624400155f08b1ec488002ab21163d891000747b20c7b122000e8c6418f6244001d8b0231ec488003b118e31d89100053742ee9b122000a6d85dd362440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d36244001c5ea92a6c4880038b55054d891000557424e7b122000aad849cf624405d5cd0239ec488002b960473d89100053742c87b122000a6d8590f62440011dd0f98ec4880023b61f31d89100055742663b122000aad84cc7624400155f08b86c488002ab21170d891000567c1ae1b122000acc835c3624400155f08986c488002ab21130d89100047743861b1220088ed870c3624400155d08186c488002ab61030d89101757340861b122000ae5810c36244001958c5ba2c4880032b18874589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271c
  | 4 => 0x44400147b0b98ec888002aba0b31d911000556c1663b2220108bf874c364440671790e986c8880028fe1530d91100051e42a61b2220008be870c3644400117b0e186c8880028fa1430d91100051ec2861b222000aae820c3644400155b04186c8880ceada0430d91100055ac0861b2220338be87c83644400117b0f906c8880028fa1720d91100051ec2e41b222000a9e83c83644400153b07906c88801f0f192759911003e1e322eb3222000c5e73d9664440018dce5b2cc8880030f9d764991100061ebaec93222000c9e73d92644400195ce5b24c88800317d9573991100064fb22e73222007c9c645ce64440018bcea31cc888003175d4639911000667390c73222000c6f655ca644400195ec8b94c88801f2b19172991100066631ae53222000c5c73d9564440018d8e5b2ac88800317d9773591100062fba8c6b222000c5c7518d6444001998e431ac8880031bd9772591100066631ee4b222000c3f75dd16444001878ebba2c88800317dd773591100062e3aee6b222000c9f74dcd64440010ff0ab9ac88804a1f21573591100045fc22e6b2220008ef825cd64440031d904b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b2220008bf87590644400147f0ab20c8880028f21564191100054fc1ac83222000a9c83590644400155f04b20c888002ab20964191100061f3b6ca32220008bd87994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c8880022f61e63191100051f42cc63222000a3d8598c644400155d05318c888002ab60a63191100045fc3ac63222000a3f8558c64440014790ab18c888002abe09631911000556412c63222000e1f6518c6444001c38ca318c888003a560463191100051f42cc43222000a3d85988644400153d07310c888002a760e62191100074a31c6232220078be8794c644400117b0f298c88800387d4e531911003c5f438a432220008bd87148644400153d06290c888002a760c52191101955b40e643222000ab581cc8644400f17d0e190c8880022f61c32191100051f428643222000a3d850c8644400f17d0f988c8880022f61f31191100051f42e623222000a3d85cc4644400155d05988c888002ab60b311911008c5fc3a6032220078bc874c0644400147f0a980c8880028f215301911003c5f4386032220008bd870c0644400147d0a180c8880028f614301911000557410603222000aad820c0644406556d02180c888002ad604301911003c5f43e4
  | 5 => 0xe2fa1e43593100051f42c86b26207c8be8710d64c40070ff0eb2ca9880028fe11659531000477c12ecaa620018ec825d954c400127f0eaa0a9880028fe1954153100051ec32a82a6200087f855d942c40250f90abb285881af0f9907550b1001c5e43ac8a162000c3c7559142c400355904b2285880ca2fe1d64d03101e61f320eaa062000c3c7559140c4001938e6b22818800f391c562483100051f42c87b242000c3c75dd164840051bd0fb9ac90800317dd773592100062e3aee6b24200087f855cd64840250f90ab9ac9080022fe1173592100046f438e6b242000c5f751cd64840018b8ea39ac90800327dd073592100045f43e86b24207bc3c75d0d6484005938e7a1ac90800a2f21d43592103d61e3aa86b242002c9c7350d648400117f0eb20c9080028f21564192100054e41ac83242000a3d84d9654840031dd053b2a9080023b60a76552100045fc22ecaa420008df835d954840051b906bb2a90801e2f21176152100046fc1aec2a420028dc835d8548400127f0eaa0a9080028fa1954152100051e432a82a420008bf845cd628400f17908b9ac50800a3b21d3258a100043fc2aeda14201287c855db428400317908bb6850800237e0d76d0a100146e41aeda14201287e859d942840010fb0b3b285080021fe157650a100943e42aeca1420008df835d942840051b906bb285081af0f1907550a1000c5f43ec8a142000c3c75d91428400355d05b2285080ce2fe1d64d06102751e42ac9a0c2021a9c8359341840974790ab228308076a720d64506102151e42ac92042011a9c835924084079878c83aa81080030f1d764502100064e39ec8a0420008bf8759040840774790ab208108042a720d641021001c7743ec49042000be181d8920840073d10e90a410800f781c521482100051f42c87b222000a3d8590f644400517f0ea1ec8880028fa1442d91100051ec2885b222000a9e8310b644400153b06216c8880028fa1663d91100051ec2cc7b222000aae8298f644400155b0531ec8880028fe1563d91100051e42ac7b222000aaf8258f644400155904b1ec88800387d9463d91100074ac08c7b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000e94638c7644400187eeb3aec8880030f5d475d91100051f428e7b222000a3d851cf644406756d0239ec888002ad60473d91100045f43ca7b2220008bd8794f6444001c3ea729ec8880028fa1772d91100051ec2ee5b222000a3e859cb644400147b0b396c888002a7a0e72d91100054ec1ce5b222000aba801cb644406757300396c8880022fa1c52d91100045ec38a5b222000a9e8314b644400153b06296c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c8880022fa1f31d91100045ec3e63b222000a3e85cc76
  | 6 => 0x68e398eaa00803cc3f631d5401000187ac63aa802010b0f98075500401e69d300eaa00801099e87dcd401000193eedb9a8020003471d773500401945e43ac2a008000c3c755854010001938e6b0a80200cb2d1c561500400943f42ee7b24400087d85dcf64880018dceab96c9100028fa1764992200051f42ee8b2440028bc8750d6488005938e6a1ac9100022fe1d64192200051fc22cb2a440008bd849d9548800f17d093b0a9100024fe1d54152200051fc32a82a44000a3d8655054880250fd0bba2c3100021f61774586200147a43a62b0c4003cd6615cc61880011ef0eb08c310003355cd61186200943f42ceda0c400087d859db418800717d093b6831001f2b99172d062001c7cc34e120c40038f9869c041880611df0cb84431001f2b99172102200051f42c87b224000c3c75dd164480051bd0fb9ac89000317dd773591200062e3aee6b22400087f855cd64480250f90ab9ac8900022fe1173591200047bc0ae6b2240038f4815cd64480011bd0e39ac89000317dd473591200062e3a8e6b224000c9f741cd644800117d0fa1ac8901ef0f1d743591200164e39e86b22407ccb471d0d64480051790ea1ac8901eb0f1d543591200164e39a86b22407dcb47150d64480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89000339dc871591200045fc3ac83224000a3c85590644800153906b20c890002ad20564191200051ec26cb2a240008bf845d954480011bf06bb2a89000a3720d76551200047bc0aecaa240038f4815d954480011dd0db92a89001e2f21176151200046fc1aec2a240028dc835d854480011ef02bb0a89000e3d20576151200049fc3aa82a24000a3e8655054480014790caa0a890092cb209541512003c76432e42a24007cac645c85448001a5aa8b90a8900021fe1574d85200943e42ae9b0a40008df835d361480051b906ba6c2900022fe1173d852003c5e422e7b0a4000ab684cc761480011ef0eb08c290002ad21161185200056a41ac230a40038be849db414809d4790ab268290086a720d64d052001d5a40ac9a0a4040c3c649d6414800187cebb248290003279cf649052001c7c432e120a40038bc8759141480974790ab228290076a720d645052001d5a40ac8a0a400087f855d841480250f90abb0829000237e0d76105200146e41aec20a40008bd87d9041480079c8c2b90829000e3e219701052001d73436c290a400a8ee861c1214800317f0eb24809010a8f215649012008d4e41ac92024033ab4815924048079878c83aa80900030f1d764501200064e39ec8a0240008bf8759040480774790ab208090042a720d64101201955a40ac820240018ec865c6204805d9c8c2b8c409
  | 7 => 0x5e7319641500011b90cb9c82a000317d9573905400062e32ae720a80008dd87d8e41500018bcebb1c82a0003175d763905400070e31ecaa0a8000e1c63195415000187ee632a82a00030f5cc65505401e71bb88caa0a801da9e86d8d4150001c38cbb1a82a00038d19761505400074a31ec2a0a8000e37651854150001878ca38282a00032718c70505400043fc2aed10a801287c855da21500011bf06bb442a000a3720d76885401e61f3a0cb10a8000c3c655d22150001938c6ba442a004a1fa1776485400043ec2eec90a80028de83dd921500011bb07bb242a004b0f19574d41400064e31ae9a828000e5b63d4250500011bf06bb2a0a000a3720d76541400061fb2ee8a828042c3c65dd15050001938c7ba2a0a020637a1f63541402ac6e43ec6a828000c9f74d8d50500ab938e9b1aa0a00038718f65901401ef1db06cb2028000e1c63196405000187ee632c80a00030f5cc659014008d4f436c72028014c9e76d8e4050001c38cbb1c80a001e2f21971901400061e32ae32028000c9c635c64050067968c2b8c80a02030f153735944003c5e422e6b28807fc3c545cd6510101878e9a9aca2000a1f21d535944003d1e422a6b28807fc3c7454d6510081878a9b8aca2010e2fe1972d504021e57312e5aa08042cba605c354100010ff0ab9ac42004a1f215735884003c5e422e6b1080028ec874c9621000f55908992c42001e2f21176d484003e1e3a2cba9080438bf845d952100030f90eb2aa42001f0f1d165548403649f43ea8a908043e2e62d51521000f958e8b12a4201ae4fa1f75508403f61fbb0eaa10806bc3e861d5421007787b0c3aa84201af0fd8c75508400061eb18eaa108024c3e621d54210049878c43aa842010b0f980755084035e9d300eaa10803b8bc875954210077878eab2a84200ca2fa1f54584400061fbaea8b088032ab681d51611000717b09b9ac22001e2f21173584401945f43c86b088000a3e8590d611006556d0321ac2200ca2f21d42584400051e42a84b088001cac7250961100014eb0b18ac22001eada1231584400147a43a62b088065e94434c56110081878a8bb6a2201028f21165d44401949e42ae9a8880038bd845da51100079acc2b9ca22001f2d9d161944400066ab9ac3288803fc3c545d951100011df04bb2a2200063b20976544401fd1e422caa888007c3c74595511007fc68a8b0aa2201030fd8e75904400061eb1ceb2088032c3f619d6411006587ac33ac82200cf0f98275904402069d304eb208800087f855d921100250f90abb2422001f2b1d1624844000c7a43ac290880078bc845db501007b878a9bb4a0200063ba0b769404003e1f3a2cb28080428bf84dd95010079878a8bb0a020003271cf76500401e49f43eeaa008000c3f76dd54010001a38e7baa80200030fdd875500400
  | 8 => 0x810ec6a0002b6a0021d8d400056cc0043b1a80558de87c8363500011bb0f906c6a000297a1720d8d400052ec2e41b1a8055a9e84c83635000153b09906c6a000b271cd43d89400043f43ecab128000c5c73d9562500010fd0e32ac4a0003171cc65589400062fb2ee6b128000c5c65dcd62500011bd0fb1ac4a000317dd763589400062e3aec6b1280008de8718d62500018beea31ac4a0003171d463589400063bb2ee2b128000c7465dc562500019aec7b8ac4a00033518f71589400063bb28e2b128000c74651c562500019aec638ac4a00033518c715894000672310e2b12800187c855db525008517f08bb6a4a000237e0d76d49400146e41aeda9280028de83dd952500011bb07bb2a4a001e2f210765494000c3f43ecaa92803dc3c74d95525000187ecbba2a4a020f0f19774549400064e31ee8a928000c9f74d8d52500ab938e9b1aa4a00021fa1b75509400062e31eeaa12800087e861d542500018b8c63aa84a00921fa1f65509401443e43ecaa12803de2c42d9542500510fd0e32a84a004a1f21c65509400062fbaec6a128000c5c75d8d42500011bf06baec2a000a3720d75d85400043fc2ae7b0a801287c855cf615000717908b9ec2a0002ad61021d854000578c0043b0a8033c3f649d661500018bce7b2cc2a0003179cc65985400062fb2ae730a8000c5c655ce61500018bcebb1cc2a0003175d763985400062f3a8c730a8000c5d7518e61500010fd0fb2ac2a0003171cf655854000636396cab0a800087e8719561500018b8e632ac2a00031b1c865585400146f436e6b0a8000c5f65dcd61500018b8cbb9ac2a000237a1f63585400062fbaec6b0a8000c5c75d8d6150001998e5b1ac2a000237a1c63585400062fba8c6b0a8000c5c7518d6150001998e431ac2a00031bd9772585400063632ee4b0a8000ccf63dc96150001998c7b92c2a00023de1d611854000572412c230a800387c855db51500011bf06bb6a2a000a3720d76d454001c5e424ed28a80028dc839da51500011bf06bb4a2a000a3720d76945401ee1f3a6cb28a8000c5e73d96515000187ecaba4a2a012f0f19574945400064e31ae928a80008dc865ce51500018becab9ca2a020b1719573945400046fc3ec728a80008dd87d8e51500ab93ce9b1ca2a0003275d363945400146f41eeca8a80008dd83dd951500011bf06bb0a2a000a3720d76145400961e32ae828a8000c9c635d05150001938c73b682a00030f9db65d05400070e31ecba0a8000c3e761974150001c38c632e82a00f30fdcc65d05400061eb98cba0a8021a9e86d8f415000193cedb1e82a00038719763d05400061e32ce1a0a8000c9c639c341500010fd0d3ac82a00031718e75905400043e432eb20a8000c5c635d641500010fb0fb2c82a0003179cf65905400043ec38cb20a8000c
  | 9 => 0x30d954023c3e43a61b2a8000a3f844c3655007b47908986caa00021fa1c30d95400043ec3861b2a803da3e840c3655000147b08186caa00029ba0830d954000536c1061b2a8000a76810c365500014eb02186caa00021f61f20d95401ed1f42641b2a8000a3d84c8365500014bd07906caa00029760f20d95400062f39ecb32a8000c5f655ce65500258b8cab9ccaa000327dd373595400045fc22e6b2a8000c9f741cd65500010ff0eb28caa000297e0d65195400052e41aca32a800087d8798c65500010ff0eb18caa00038761063195400051f4368632a8000e1c63d0c6550001c3ec6a18caa00038718d43195400052f41cc432a8000a5d83988655000147b03a18caa00028fa0343195400943f43c8632a800087d8790c6550079c3f06a18caa00028fe0543195400051e4028632a803ca3e84cc8655000147b09990caa00038750f32195400070ea1a6432a801287e870c865500010fb0e190caa00f28fa1032195400051ec206432a801287e87cc465500010fb0f988caa00f28fa1331195400051ec266232a8000e1f43cc465500014dd05988caa00029b60b31195400943f43c6232a800087d878c4655007947d09188caa00028f61231195400070fa1a6232a803ca3e840c4655000147b08188caa004a1fa1c21195400043ec384232a803ca3e84084655000147b08108caa000297a0c21195400052ec184232a8000a7a8008465500014f300108caa00f28fa1330195400051ec266032a8000e1f438c0655008f0ff0e980caa004a1f21d30195400051fc226032a803ca3c844c065500250fd0e180caa00021f61c30195401e51f4206032a8000a3d840c06550001c3e86180caa00029ba08301954000536c106032a8000a76810c065500014eb02180caa00021f61f20195401e51f4264032a8000a3d84c8065500014bd07900caa00029760f20195401ee1f2a4edaa28007a3c84d9754500258f0cb386a8a001e8fa1365551400063db28e0aa28000c5e76d9763500011bb0f32ec6a000297a1665d8d400046fc3acbb1a8000a5e8619763500018bcec32ec6a0003871d065d8d400a54f436e9b1a8011c9e76dd36350001c38cbba6c6a000297a1662d8d400052ec2cc5b1a8000a9f845d7635002953908baec6a0003175d475d8d401d56d406e9b1a8055e1e54d5363500abc38a8aa6c6a000297a1672d8d400052ec2ce5b1a8014a9e849cb635000153b09396c6a000237a1c52d8d400046ec38a5b1a8055a9e8414b635000153b08296c6a000297e1571d8d400052e42ae3b1a8000a9f845c7635002953908b8ec6a0002b3e0971d8d4000566412e3b1a8000a5e851c763500014bb0a38ec6a0156a7a1071d8d400054ec20e3b1a80008de8708763500011bb0e10ec6a000297a1421d8d400052ec2843b1a8055a9e84087635000153b
  | 10 => 0x2a48000a3f83d94549000147b07b28a9200928fa0b651524000717416ca2a48024a2e82d945490001c5b05b28a9200928f20b65152400051ec0eca2a48000e3a80d94549004917f0cb90a9200030fd95721524012657312e42a4801199c835c054900018dcc53aec52000a3b21d3258a4000c3e42aeda948042c3f545db52900014df0ab16a5202164fa1f5454a400061fbb6a8a94804293c855db429002333906bb685200022f61f65d0a401ee1e3aecba148001aae82d97429008517f0eb2e852010b0f9d565d0a4000c5fc32e1a14804293c855c3429002333906b8685200931b9887550a40006363aac4a148028c3f76dd54290051c5cc5baa85200930fdd87550a4012717310eaa148042c3e861d5429008587b0c3aa85200030fd8c7550a400061eb18eaa148024c3e621d542900b9a5cc43aa85200930b9887550a401261e310eaa1480018be87d954290085878ebb2a8520006aba0b6550a401245e43acaa148042c3c75595429000355f0cb1285200034b1d56250a400069dbaee0a148000d38751c1429006717d0e2a2c3200030fdd4545864019d5b408a8b0c80008be8790d619000147d0b21ac3200ceada06435864019c5f43886b0c8033ab68110d619006717d0fa12c3200028f21542586400055ac2462b0c80028f4874c56190001d288698ac32000f3598573186400047bc3ac230c8000cd57358461900070fd0b3b6a32010b0f15276d464000c77414eda8c80008ed829db519002587ccaba6a3200030f597745464001e6b30ae720c8000cd573586419000187ec73ac83200030f58e759064019e1fb0ceb20c8033c3d619d641900852790ab8083200466720d701064001d7240ac490c8000c3d655d2509006717f0eb0e81200cf2d9c561d02401ee9c3aca1a048002c5c73d4f655000147b0929ecaa0003175ce53d95400143fc3aa7b2a8000a3d8414b65500014bd06296caa00029760c52d95400070ec20c7b2a8000a3e86d0f6550001c38c7a1ecaa00038718d43d95400052f41cc5b2a8000a5d8398b65500014dd05ba6caa00029b60b74d95401ed1f420e7b2a8000a3d841cf65500018bae639ecaa00021fa1e43d95400043ec3c87b2a8000a3d84dcb655007b47d09396caa00028f61272d95400052f41ce5b2a8000a5d839cb65500010fd0e196caa00021f61c32d95401ed1f42065b2a8000a3d840cb655000147b0838ecaa000297a0c71d95400052ec18e3b2a800087e87cc765500010fb0f98ecaa00f68fa1331d95400051ec2663b2a8000a6e82cc765500014db0598ecaa00021fa1e31d95400043ec3c63b2a803da3e848c7655000147b0918ecaa00021fa1c21d95400043ec3843b2a803da3e84087655000147b0810ecaa000297a0c21d95400052ec1843b2a8000a7a8008765500014f30010ecaa02121fe1d
  | 11 => 0x5040355d0db1284a08034b1d762509410069a3aee2a128200d37751c5425046517d0db8284a080e4f21574d45410961e32ae9a8a82018ec825d9515040187ecbba2a2a08ff0f5d854545410943f42ee7b02820087d85dcf60504011f70eb00c0a08030f5d454181410055cc00a830282078bc845cc605040117b0f218c0a08028fa1643181410051e42a84302820387e8794d651040f47d0929aca2080317dce53594414343f438a6b28820387c87595521040f878e8b2aa42080237e0d75980410146e41aeb300820087f855ce60104250f90ab9cc0208f70f1d375580411e61e3a0eab0082028de87dcd60104018beebb9ac020803171d773580412ae4e3a6e6b00820087f855cd60104250f90ab9ac0208462fe1173580410062fba8e6b008200c5c751cd60104eb938e839ac0209eb0f1d543580410164e39a86b0082038be8790d648840147d0b21ac9109f22fa1c435922101c3fc3acb2a44200a3f84596548840127f0eaa0a9108028fe1954152210051ec32a82a44224b2c82550548840f1df0cb90a91081f2b991721522100696aa2e42a4420087f855d260884250f90aba4c11080237e0d74982210146e41ae930442008bf845ce608840f17908b9cc1108030fdd774582210061fba8e8b044200c3c751d160884051bd0fb9ac11080327dd373582210064e3a6e6b0442008bf845cd608840f17908b9ac11080327dd073582210064e3a0e6b044202ccc734c9608840517f0ea1ec89080b279cd43d91210061e3aee8b22420087f855cd64484250f90ab9ac8908023ee0173591210047c402e6b224200c6c75dc9644840117f0eb20c8908028f21564191210051ec26cb2a242008bf845d954484011df04bb2a89081e2f21176151210049fc3aa82a24200a3e8655054484014790caa0a89081f2b19172d052103c5f426e7b0242008bd84dcf60484011f70eb00c0908021fe1574181210943e42ae8302420787e8794d65d000f47d0929acba000317dce53597404043f438a6b2e800187c8759552d000f878e8b2aa5a000a37a0f75587400046ec1eeab0e801287e85dcd61d00010fb0bb9ac3a001e2fa13735874001c3e42aeda8e8007c3e7459651d00018bce6b2ca3a000e1f61776547402043fc3aca28e80328bf865d051d006517f0cba443a00063ba0b73d964000476c16e7b2c8000a6e82d9665900014dd05baacb2000a1f21d53596400051fc22a6b2c8002c5c7354d659000147b09292cb200031bdca52596400051ec20a4b2c8000a5d8314965900010ff0eb28cb200f61fe1d65d52401ee9c2a4e1aa48042a3f87597549000187f0eb2ea9200ee2fe1970d5240004ddc32e1aa4803bcbb865c35490085878cabb0a9200024f61f65152402e597416ca2a4803cb3a80d94549007b47b0fb28a9200030f61f65152400041ec3eca
  | 12 => 0x80297e157058e410052e42ae0b1c8200a9f845c163904cb53908b82c72080297a147058e410052ec28e0b1c821fa9e841c1639040153b08382c720802b3a087058e4100566c10e0b1c8203ad6811c1639043f5ab02382c72080237a1f2058e410046ec3e40b1c8200a5e85c8163904014bb0b902c720996a7a132058e410054ec2640b1c8203ad68108163904015ab02102c72080b279cd4358a410943f42ee0b14820087d85dc162904051bd07b82c5208023760f7058a4101c3e43acaa94823fc3c74595529050787ccbba2a5208030f5977454a410064f31ee8a948200c9f7458d52904cb938e8b1aa5208021f61b7550a410062f31eeaa14820087d861d542904018bcc63aa85208a21fa1e6550a410943e43ccaa14822887e8759542904490f90eb2a85208ff8b1096550a410062fbaac6a148200c5c7558d42904079a8e2b1a85208033558f7150a410046fc1aeb30482028dc835d660904010ff0ab9cc12084a1f21573982410043fc2ae6b04821287c855cd6090405938e7a1ac1208422f21d435824101c5ec26e7b2a820287f8754f655040147f08a9ecaa080b179cd53d95410051ec24a5b2a8200c6d7294b655040147b08296caa08029760c52d954100477c12e6b2a82018ec825cd65504011f700b9acaa08023e201735954100657ba0e4b2a820087f8759465504014d904b28caa08fe1f61f65d51411fe9a2a2e3aa2824ba3d87d97545040187b0fb2ea8a08ca2f21970d514125e1fba6caaa2824bc3e659d8545040f96ec33b0a8a08024fe1d651514131596412ca2a28240b3781594545047f47f0eb28a8a08030fe1d65151410041fc3aca2a28200a3f83594545040147b06b28a8a08038be0965151411251f412ca2a28224a3c825945450401c5904b28a8a08928b20965151412051fc0aca2a28200e3781594545040147900b28a8a08922f21972151410061eb2ae42a28224cac625c8545043b33906b80a8a080a3be1d32d89410043fc2ae1b12821287c855c362504011bf06b86c4a080a3720d70d894100636310eab12820187e859db525040717b093b6a4a092f0fd5276d494100536c2ec5a92828793e87d515250401878edaa2a4a092e4fa1676d09410eccf41ceda12824b8bd87d97425049787cebb2e84a08022fe1d65d09411fe1e3aacba128201aac8259742504972790ab8684a08766720d70d094112636310eaa128200c6c75d89425049727d0fbaa84a08a30f1db755094114716316eaa128224c3c761d54250449c58c43aa84a092f0fa18755094125e1ec30eaa128200c3f631d5425040187ac63aa84a08930f98875509411261e310eaa128262d2c621d54250449858c43aa84a09af0fd84755094135e9bb08eaa1282248be87d954250497878ebb2a84a08062f21d655094125e1e3aacaa128201aac8259542
  | 13 => 0x47643a64b168207aac844c962d04250fd0bb82c5a08021f6177058b410146f41ee0b1682008dd83dc162d040717908bb6a5a081f0f1d165d4b4101c5e422eca96820187c8759552d040f878e8b2aa5a09b24fa1f5454b4121f17316a8a968207cac7458952d051387eec3aa85a09af0fa187550b412761ec30eaa16826bc3f631d542d040187ac63aa85a08930f9887550b411261e310eaa16824e8bc8759542d049d878eab2a85a080e4f21574d47410061ebaea93068200ab980d5260d040717d09b9cc1a08028fa1643983410051e42a853068201cae7250a60d04010ff0ab9ac1a084a1f215735834101c5e422e6b06827ca3f81d0e65904f947b03a1ccb209f387cc743996413e70e98e8732c8200a3e80d0e65904250fd0f21ccb208021f61e43996413ed1ec248732c827ca3f8350e6590481c3f06a1ccb209f68fe0543996413ed1ec0a8732c8200a3c8050e659048147d09994cb208028f61332996410070ea1e6532c8200e1d434ca65904250fd0e194cb208021f61c32996412051f4206532c8200a3d840ca659048147d09984cb208028f61330996410070fa1c6132c820087f874c265904250f90e984cb208028fe1130996412051e4226132c821287e870c265904010fb0e184cb209028fa1030996410051ec206132c8200e1f430c265904014dd04184cb208029b608309964101d3b4086132c8200a75810c265904250fd0f904cb208021f61f20996412051f4264132c8200a3d84c8265904014bd07904cb208029760f20996410162f39ea6b2c8200a3d8494d65904018bee729acb2080e1f21d53596410051ec20a4b2c8200a5e8314965904014bb06292cb208029be09745964100536412e8b2c823fa3e849cd659040147b0939acb2080317dce73596410043f43c86b2c820087d8790d659040147f08b92cb208fe8fa1072596410051ec20e4b2c8200a5e831c965904014bb06392cb208021fa1c32596410043ec3864b2c823fa3e840c9659040147b08192cb208028fe1170596410052fc1ae0b2c8200a5c835c165904010ff0e982cb208021f21d30596410051fc2260b2c823fa3c844c165904010fd0e182cb208021f61c30596411fd1f42060b2c8200a3d840c165904014dd04182cb208029b608305964101d3b40860b2c8200a75810c165904010fd0f902cb208021f61f20596411fd1f42640b2c8200a3d84c8165904014bd07902cb208029760f205964101d3b40840b2c8200a758108165904258eccab8ea9208ff4d95171d52410063ab2ee2aa4821fa9e84dd5639040153b09baac72080317dd67558e414456bc0ae8b1c8265e1e54d5163904cbc38a8aa2c72080297a147258e410052ec28e4b1c821fa9e841c9639040153b08392c72080237a1c5258e410046ec38a4b1c8265a9e84149639040153b08292c720
  | 14 => 0xf844c365508d947908986caa10021fa1c30d95420043ec3861b2a846ca3e840c3655080147b08186caa10a29ba0830d954200536c1061b2a8400a76810c365508014eb02186caa11c70fdd774595420045fc22e6b2a840087f87594655090747f08b28caa104a8f21276195420043ec3cc632a848fa3d8498c65508014ed03318caa10029d60663195420043fc3ac632a848ea3f8458c655091b47d0da18caa10928f21943195420070fb1a8632a846ba3f87d0c65508f747b0fa18caa11ef879cf43195423df0eb9e8632a8424a3e82d0c655084947905a18caa10028f60743195420051f4068632a841287e8790c65508010fb0f218caa11ea8f61243195423d51fc3a8632a847aa3d8750c65508d747f06a18caa11af87e0d43195421251f4128632a8424a3c8250c6550919c3e64a18caa1233874c943195420051fc0a8632a8400a3c8050c65508250fd0f988caa10021f61f311954235d1f4266232a8400a3d84cc46550801c3e87988caa10929ba0b311954200536c166232a841287e878c465508010fb0f188caa11ae8fa1231195420051ec246232a8400e1f434c465508d747d08188caa10028f610311954235d1f4266032a8400a3d84cc06550801c3e87180caa10021fe1d30195420943e43a6032a8400a3f844c065508d747908980caa104a1fa1c30195420043ec386032a846ba3e840c0655080147b08180caa100387d0c3019542125374106032a8400a6d820c065508014ed02180caa10029d604301954221e57b22e5aa28424c3e761965450897878cab8ca8a10066b20971951422161e32ce12a284019ae829c254508518d8e5b2aa8a104a8fa1b65551421461e3b6caaa28424c3e761955450825878ec32aa8a113b0f19771551421de1e328e0aa2840087f855cf61508250f90ab9ec2a1002ad61231d85420147bc3a63b0a841287e859c361508010fb0b386c2a1003179cf65985423161eba0cb30a8400c5e7319661508018becab9cc2a100317195739854201e6a30ae730a8400cd573d8661508010fd0fb2ac2a10021fa1c655854245e1fba0cab0a84008f78758461508250fd0bb9ec0a10021f61773d814200c5ec26e7b0284008bd87d0f605080593ce7a1ec0a10422fe1d43d81424561eba0cb302840087e87d9560508018b8e7b2ac0a10021fa1c65581422e61fba0cab028400c5c7319560508018becbb9ac0a10031719773581420063bb2ee2b028400c7465dc560508018eeca38ac0a10031d19471581420047dc3ac0302840087f855cc60508250f90ab98c0a10021fe1571181420943e42ae23028480c3c54dcd65d040717908b9acba09ff0f15173597410143e43aa6b2e8207a3c8454d65d0479878a8382cba090e2fe1972d534121e57312e5aa6820087f855cd62d04250f90ab9ac5a080e2f2117358b4101
  | 15 => 0x1bb2a82a0030f8c376550540061e986ecaa0a800c3c30dd9541500187e41bb2a82a0030f08376550541249f43ee4aa0a800c3f76dc9541504927f0eb92a82a0028fe1972550540061fbb2e4aa0a800c3f76dc5541508127f0db8aa82a1024f61b71550540049fc1ee2aa0a80093d83dc5541504927d05b8aa82a0924f20b71550542069b30ee2aa0a840d3561dc5541500127d01b8aa82a0028f61a71550540061fbb4e2aa0a86fb1e839c5541500163b0738aa82a0028fe1971550540061fbb2e2aa0a800b2f825c554150dd65904b8aa82a0030fdd871550540061fbb6e0aa0a800a3d869c1541500187eed382a82a1bacba0a705505400596c14e0aa0a800a3f865c1541500187eecb82a82a002c7e0d705505437d8e41ae0aa0a800c3f761c1541507927f0c382a82a0f24f61870550540049fc18e0aa0a80093d831c1541504927d04382a82a0924f20870550540049ec08e0aa0a83cd3a601c15415079a72c0382a82a0030fe1d54588541251e43aa8b10a86ec3c8755162150490790eaa2c42a0028fe0d545885400717c12a8b10a824a3e82551621504947904aa2c42a1bb8b209545885412516412a8b10a807e2f7255162150ddc5c64aa2c42a0028fe0554588543771610aa8b10a800a3c8055162150ddc5e40aa2c42a01e2f21173588541245e43a86b10a800a3d8550d621504955904a1ac42a00a3b21d325885403d5642264b10a800e2d544c96215001d1a86992c42a00a37a0c70584540046ec18e0b08a8018ee821c161150011db04382c22a00237e0d71980540146e41ae3300a8008ef825c660150031d904b8cc02a00a37a1f73580542ae4e3a6e6b00a875c9c741cd6015005938e6a1ac02a01e8fa17765534203e1fbaeecaa68440c3c65dc554d0879878ca382a9a10f70f1d375583421e61e3a0eab0684028de87dcd60d08018beebb9ac1a1003171d773583422ae4e3a6e6b06840087f855cd60d08250f90ab9ac1a10062f21173583420062fba8e6b068400c5c751cd60d08eb938e839ac1a10022f21d43583423d61e3aa86b068402c9c7350d60d080147b0929ecaa1003175ce53d95420143fc3aa7b2a8402c5e7354f65508018eca2b8ecaa10029da0663d95420053ac0cc7b2a8428a3c8650f6550801c38c6a1ecaa100317dce73d95423651f420e7b2a8428a3d841cf65508018bae639ecaa10a21fa1e43d95420043ec3c87b2a846ce1c4350f655085147b0838ecaa100297a0c71d95420052ec18e3b2a8400c75711c765508010fd0f98ecaa10021f61f31d95423651f42663b2a8400a3d84cc765508514dd0598ecaa10029b60b31d95420043f43c63b2a840087d878c765508d947d0918ecaa10028f61231d95421451ec26e1b2a8400a5e83dc365508014bb07b86caa10021fe1d30d95420043e43a61b2a8400a3
  | 16 => 0x1300000000680100100380200100281200080200f00300500200080000000180101580700080080800180600b00700480000480101800000480180200400880000080080000180000880400580000000980000000500280e80100580080000000000080281b00580300e80180380000300680600200080000400680580780580700200280500000500380300000080180280201500200000600200100000000000800700980100100200000400080180000200100000000080480100180100100000100080000100200080000000280580000000080380080000900480280280000180180100100000100000400000700180180280180080600780000000200000200100180401680100080080080000001080a80080200a00a00000100b00680300280180480380100280001480000700080580680180100280000180000880080480100400180780100580000800080200100100400300900080000080101500280000000800400100180300280200000000100400000200000100080181400380101500d80080180180000100700080000400680000a00500580000300d80000080080000180580100180080200900100280580380000280000000180300400100000600100000080000100000000100500c00000280000300400200180600300000000100100000400200500000780000a00000080100580380000000780580280180000580100780080000180200080180000080080100400000180000500100000200280180000000080580080080080780000080000000100280100000080a00000080080400500000480000000400200000000000000301c80180080080000000480200700780100500380000080000100000600080800000080d8020078000000a21fa1f5358a5414537416a6b14a802c5e7354d62950051bd07b82c52a0023760f7058a5403c5e422e6b04a802c5c73d4d60950014f501a9ac12a2121f21d53582540046fc1ae1b12a8028dc835c362550031dd05386c2aa0023b60a70d85540047bc3ac230aa8008fb8758060550011df04b88c0aa0063b209711815403e1f43eecaa0a800c3f73dd9541500187ce7bb2a82a0030f5cf76550540061e39eecaa0a800a3d82dd9541500187ce5bb2a82a0030f1cb76550540061fc1eecaa0a800c3e83dd9541500187b07bb2a82a0030f20f76550540061fc16ecaa0a800c3e82dd9541500187b05bb2a82a0030f20b76550540061f996ecaa0a800c3e32dd9541500187a65bb2a82a0030f0cb76550540061fc0eecaa0a800c3e81dd9541500187b03bb2a82a0030f20776550540061f98eecaa0a800c3e31dd9541500187a63bb2a82a0030f0c776550540061f90eecaa0a800c3c21dd9541500187f01bb2a82a0030fa0376550540061ec06ecaa0a800c3c80dd9541500187e6
  | 17 => 0x3fa0000000001180814000000000031a30c000017e27b1a0971c0000001de1698000586000000062a0000a01dd46c60000000f5c6ce06e0000f102385e937d0be4e2c05d00b04102f41ff2f400000004530000676f460000dc0000a4600000010e00000001f640000000bb339067a542332000000000000007880000e40000345eac0b80000000000a665011e38000b203e9000159c4c60003c60dbc8c878b26421a04c81d80001eb0b847cc12693d4000193a6e9e643f651007191483800320ab82b44fc7c70ff10a037a000397016cab448d11f86a000081d32414d85c208f2aa921912c378c681a2c64e76c27e12b218861f1e28bd0b4e10014b13e0dbe88c160090c54a6ff2d592f83286822ca0658392783454219092447721e849000063ec0f9d8812a1cd40e04dc0002da06180000004ce33c000077a0000000000be81010660294000000092845d0142501e9018e84255736b073f0225db00000002121e63d701920002080000104cec50c1d195ac0001c60001f94000322000118800009a984c540f7039e0161b8c0002dc2fd1eec00082331b856081c5883899ab00000000889c8ca0a3b692da08086e000164815013300000000400280100400000000580100100000100900000300901780400300080000480200000a80300480300380000380280480080000180001180000200000000400000000000500800100280200200080300700280000a80000080080600480000001080100080001100000000600280180080000000100480000000280000280000080000000000280280000580480000080180180100000180080580000c80100000280000a01a00000d80280100100300000600f00280000000680080180000300180900100000180400980100100000100080a80000100080002100000000280000000100100980000000280000080580000100200b00480000000280280300200100900a80200100780580080080480980100000300400780300180c80200480200680100200000300200400b80000380180800000100180000000300000080d80200380000100000000000000600700000600080280700000200400880080000080100300200c00b00000300000000080080080600000000080000100280280000080080e00180400280200200000101200000100100100280200000000480000a80100100280200800700380180200080000100000300000100080300080e00080080000180380000000080100200180900980080080180000500080000400680080500380d80000280580380200100280080080000180080000281180080080000280480600380300000000000000580080000180000000100080000100a80500680200181500000280100080100001c00400700080001100600200380a0008030040010000
  | 18 => 0x9a0e54ce60000590a74f5041d15f97b40000eeaa4000000000000000000000811e480000004e30681438e54581464a23c00000000000008340000bf0a6c5225761dadca4a9e22600017f4d5a3d6b6b80010341b2000000102060dc230aa46e84a58001e489747144449d684923b92429de80698dc1ac0f405fa31834e950426415600000000008130bc98e83c671f1028f70b5e0693e583fe0000003df9580da83500de1224fd400036292be4be2dd40f00002a274d05d00000005173551ff829c3fb02888188f44490000000e646228159b2e61c87d02c825a2100000af1af04265953e71f340b41531cd1ed46428cc4328594c82784158161d0b47fc0a180004a87021e5216e03255332ca2d40000002f5000094e0000000824e401f0c4a0f000003e2000073600063b19a8000f8804932793ad0cc11037c05a6d308151a580080006ab00da1080224c33de1dc03bc4f02471abcd640912ff000075e0001bb00004ac0003af00000006a938606310f840ea7606d433c5260750000300662000080014443b2fb1808722880220924cf3e4250e656b44901718e907f056425e9f814fd1824aa05c0000aba09b0000a204a56e5169a2643a664a3f8184c00000006500001b80370000f988b463ca839e285567633ac8000ce024a12a9ffd0902d80000ab11bc81b18417c40003f409c800051a0000358ce016653010ca000c546de00012600000002ec96840000000d885ca16e00009d00000006770000000bd634800000000000000000000a39181baf8a982b6660192934cdc246f1b28a8c12006200003d8c3443c1120080a7404b0000318d700000000fb80000002c5000000000037798f6c5600000000000005f711280005be00000000001ca53823e8b3475265302992c10c66d34031cf0fb85681372248d9038432609f0c8c0000001fb0dfa8d30321f5500e0331039da823e8b10438000000146349800000058300019840000003a90988b000f28dd83a4c4d65c000000010489f079e268bea000425a2a8d2a8241a993640000000bf80000680000001910df2337198135914e25c0dc8a0046603c28e98e0ba600026a8d5883e5d138787dce8026299b00010500000e81bc64386f31f58ef81686513978fccc5c2920000b10f2a5740400c14fce4ca432d6302da4e10cd80381403832e4104200000020910fc446000311000000062642b800000000007c88850040001a38bacc0a5ec00019a0a54310a0e0000af204610ec6f83ec00015516a4ac22c329701f4e7a0fc1aa22783244743bd94e493682f02801b48c241115a9ce89bc0b130000000000c100006c00000000001d946cf16e200164c4206253fa80007f30000000000af65cc21f1844a344782799e8432612730b182d1448b33e08d10000554000167400000042604602e851815c0000
  | 19 => 0xd684dc08180005e0786043ca7ca885dd2e54b48d3421214803600000ec0001d140000000000000cd60002e788b89fc5c3227163425e68f2610d9803004e07a8df8e0053b35086d71062ce1a60eec2aa4e71a91fc400052106113a00000300000c3c5c47311d81d24000355320091894878903d07386720000000000282000033c8ac3632580e608465aa6d50999088a1600001285a90f24b500016dc7d56582c280000008b701c175c0000662350cc41be75b345000000000003f468a70c00007a105446a7ee0a1000001e48a000013c1800004678408a1a000041800034d6cc2260c4cdee592000068c000434000026e8f84560b2d0bc76a0dd0000184d2c7280ee94480006fb1ff23480022cc0c2800053242a173052907c000352a12873e89034f92c45ca50f0000000f445ea80018700006340000022918009b960fe0c776431788674ada33cb2e4000a500219f7800000052700000003974a90e54664d846320d64eacdb60d40b8059235b42d3ce836c59084e2e30bbcd0244d2948e14ee64fb1768ed00000000b883680005b92b482504980bc263869d0a833e0869d3c4a223033d1adc29a4c13928000000779191a38036e000129000046276d3e4800000018a070000069e00031b2260bbe00005c84b65ec3972331ff4e306f43f691fc4c1619000000000086b00000007f237200000680000001d28ab839d6f10690000f340001d000003de0000001d0c51811537597ec7366d81140af88c60000c704e03da00035000006d40000000000c4f684b9a12ec000261b9990506ea26f2eb0d789045a512d0c483337e22cb8af117c3f11bc07e464c67d2c71e80a640990000000348451321c00019c00000016686008bb37a87c600019a22290cc0a40002af8edd0d27933829c1069b21f08dd27c5fc34339681140005bd0000d9000019a8000000c6a22a2501a500006cf00000004ee0000001dbc5b215a80007a6d6200000016c456e16f047112c0003980001f449722a827b119c00052d372001468a0000000218000000000000000087402386b00000001b102f8aa26d213900010ea6bf44e915cb548352ad800070200000013a800000042190240000000c085b001a48742480007984690000000a2c1e72830000758145439229800000040482f436d2ea3680ad80006b30c6800060662038f0ca8eac00006c95e09285bb2bd0da26ee22f101a1780548d71c79798b1e85900007940001c10000052000364a8d88e865600038318ba0000002bb826021400000005883f04af0000f2c00003a3db16f800088b00000000004102f00000f2e724000000053803b35c9500b4610633e00001aa62315e80000003ea38b8d0824464d3009e6c88854d18e92fc00000046710d48020e8000009c1e676130da1bc7ba48f3ef80b8fc25f903f8d1910c2e9
  | 20 => 0xa00019168361130000000c1e06f3ab800015c62c80000000005d500013bc77411403980000000003700dfe0007da4279b9e0005c92251d5400029a1bf800000038a000000112e4190b422b46783140001254f220000000cb8cba3c1000059092083300009040004cb000093800086a0000fa080800000014b0b603ec00000003044d21c418a0f1000000015c8b961af00000000007353b000008ea023000101437470b41b2238f0000046b000075c0000000000e3664236c98740004b897f80000000000001178dd83db00000000000003a08d00eec40d06591e40008392d202a433826046a8b28c2a8c32d420e084e56543f22043be0aa0a9000101c6910099d30a780ee2ac5590e2482b4238abc38e00008c8d340001eb3ba05e000000041e00006360001f2a16a9be7070afdfe000000036017c00001e01770000bfe000277162c4bc0000b053506cd8310000284d504c02abd8b422c0001b000000005220000e2400000000000000002b30001c8843d4542bf8000a1f5b63f5800012e0003480000ec82a71811a64d3c3da07f92c915e66d3c78a18cce0393d78f640007393bfa2c00004601968000d7c7c62628ca413a0001c00000f5a5733a2069484825721d1398b787f3073800029818b29a150cb5c4464509c050647030b46134a2a55c185117000062f8c20fc8b826dc31817b848a2d62241a242a8000360899800076933f226c5821f397a983800057e2a59680c721a60000e0800000030216d07ce4cf29b800000020400000007540003e0080465800000012d071c00000006800005ce323619cbe400000000000000002ef000079e1dfb43004e012006097041c4a61ab119102d0808ab1740fd8ad84990f49b1c7507d73d882ace1047e134872cc963b23dea3102b84f12fc035cf603091f093683c842e0000ccc0f0390158800085266c0540000f8a76e116800d08806533486449f235c2ed06b501e50a0000c5800000002c00000001cf3d50000e8c000134000036f000000000002a0000628000ef82f30000b3c51c36900014accfe4b63050b1477e6e604f20b06a26033ae05c8f2029e1ab85cc47603126804a45f67e916f22e08da55940c8a145040922f180011be13c373962472600004d20b824048440688086d675d03f108c43444740412706e604443813dc2503a64668c64fba8453e1876c91689c161181c8d63d12a60228a926e820794506b24070001c9cfb649107804d806c000073086c00e00004f9f5865e4fd45e185d0ba6c4000229420a12111e82b05408a92218910d363c62ec06867912e30000100000504000000067e0003e918bc0002bb07906d00000000d2dcacdc466a2f054f4d461da34416b0fcc0770000fdc37f71bb092144efa8251f68f5048e34a38899390b056a1ff88f018e0000965480a04000000000
  | 21 => 0x9c6e08b63f2000000074b000012000087302517100000004410000b640002ce0000000000000000019a0223388b5050238d22000005744882b10f3800085b3b904a83886ba0001c84aa40000000000d1a6f600006fc7be0960000000ab06e93dc8d8430c32400015180000003f199e492e297000130699207d800170073288823fcdc46fa0af0c447c467483a2a8217cdcd6da4058ed821656630421b0ba81b099414bc52682a1b721809c486113c8178ed05130e100483122fc1fd000086403d00000007700de1e680f890609337e0b5cf480ed000127824c07b0c4dc34a8a6ee0000f9046831038a80000000004108000d1c6923aa125863c65e0f7048cca50000000000cac26128191c0c580000d5164485613525c21700007a92cc0d688ca19530819400001bebc689d02240b6051a24c5c08bd06b0f809883a11638eb40d06751b40c343ae7810f108e0e6c2b438506d86f867287f165830d4fa1a485987a56c630492b44580140e2a0fc00000000016780001d09bd01b10e20e443116cd1b626d3b7461c3f405f2841b3481845930a1ddc0c03201fa88283424cc29a9e1469c3c310e874630f856203128836604210c189119451c0001c68ff600012780000003d300013947fa0001ec0000e6056320c00000004390e18000f90000152002ccde14705300011681f20d1116cecc0043b7c0000004f4329e148000683342885cd0e41a8f98e48f9e2e40001f4086233d845810241a07c18304b4d39556c28000000000003c80000007263c11bf801001c01300000d487b17c015c00014813b00d46767a713c0000d768181ad858050e0000e519b80000001ae8e500000003f400000005ba00019140004b728ca0dc3c20a409d823518427100023680004302e913344e687724014c4f2856e3a500000000001449ef874e1d52d100002d2000000000031e18e8001f640008c500012ac0003171328000902817b1f87580000003fd01b200023737680001183790b0936016a07640b800105a04300000002f683b30600000000001f1c0a00007de0000000c810001358964fa647b03389b000002100000002624133b887d0aea3961e100000ea0004632210d4449a367055ecbe524000015400017d00f821aa9c00002b2254afa6573249fe400000000000011a88010001e9497a8031111ec827e264842a1e102c15d0778a5476288d414813000000007d00002564f2000151c62d12c053a1b80002983f01cdcaf82669c58a88f3c61e0cf882c1d665a22f94f8cf63b7b10902880675131f0e7431f46e0e412b88e40103e121d831b17c0ad0db000069c0da40007908dd00022281f671c00017bc21c19025e4b1851e5ca0000e90cb629400e80009ae85346397841ee000285d7900e2190c6c89e849621e4090ae44ba80504e087315c5111860000d5c6c
  | 22 => 0xefc000098074e3d56ea3b5a2b04fe2f22a108e40002cb3a38dfa0521770000c1c0710001421e703b82d010a9fd84226273f79f60f6e1968d487a800059f2278c7c82c58221310d85b628b3a70036160214000043c00071d0000000de06331f1955800016c8cba32ca003fc3da1c3829688736bd7f07bc7ca000065e01d69700021b20007f20b6c34c0000000000e1cef000022109f400033d0001e1d17245d4688908b362290001e583e06c923b000095000000000010aa66320ec510000225a04000000045030699480e806bada96fc0006660000ecc000000000000094c00013380008b000039c1a9c60260641807a000074235a80000006b000000000000001d10000d8600033200008581de80022e848078e2e8000000015f000176e0000002599578000000000147c00000008d80001f0000000224400079800000000000000000220c7806300015c0000000000027219e6b63dd00000004a32f395bcbe64a532a8000ae20001450db400017502699d000002d0bb000000063f9738000506000000058cbc41670000478bca000270229000000000016e000011ec5012f0d9600000008d80007481ea80000e041700013445ee1983530c2d0f41d10449f502d6584156809027a83d352171400071040200004404683148000615183000000002e8c820f18c50da000000209c4ea6dd0001154000000000032427c6f219a000041e0002e6800073800000008300004710000000d080fd000000001800018200004e031c2ee0000a9400046c18f49fe38c41300fc84083400000bc1a237b00022fc0008854110000fee66539f87d462700284213b42b27530050000ca822706411b09d220e3fa127442c11a3239a303a80000000be80003d62929cec62259900006210fe00000004749c80002509a000000e23a800004d414f3d3000047c1ae284a030f664169761d6000000020fc3843d80002561c243074db451876403c6bd0000000e7c00000014790820002398b4421800000011e298c000000000000014920122c8e326d11af9d
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x103d98087765505400507a4c21dd9541500141d9308776550540050ea4021dd9541500143990087765505400507a4f80dd9541500141d93e0376550540050ba4a80dd9541500142d92a0376550540040fe6130dd9541500103c984c376550540040fa6030dd9541500103d980c376550540050ba4830dd9541500142d920c376550540050da4430dd95415001435910c376550540040fa6320dd9541500103d98c83765505400507a4f20dd9541500141d93c8376550541240fa63765c9541500103f9660f71550540040f65a80dc5541504912e92a03715505400607a0f769c5541500181f7660e71550540060b20b765c5541500182f76e0971550540060ba0b769c1541500182f7660a705505403c0f25f865c1541500181c83dd9705505400607ddb835c1541500103f9660c70550540040fe59811c1541504912c9260470550541240fa6387551621504922c92e0d54588541248ba6382551621504922e92e0554588541248ba4880551621504903c9761543588541248b2498550d621500122c98551325885403ca3261434c9621500160d9550d325885400417e61731cf655084922c9260743195421248ba4a80d0c655080181d87d0f31195420060761f430c06550801a174360430195421ec0fe6175d5260d044982e72215429834100685d0d810c2659044903f9761252d95410040fe5d83594545044922c9260d65151410048e24183594545044922e98e0965151410060be1f82594545040182f8720965151410060de1f81594545044903c9859572151411250b249655c8545044942c9258c75509411260ba1875d89425047f03d98d9774545410040fe5d86550548844912c9855172152210050be59545c8548840103d97a1954151211240f25d84949659000103d97e0f65152401248ba4b83d94549000182d87a0b65152400060b61d82d94549000183987a0365152401240fa63655c8549004942e92d9572152401250ba4b631d5429004982f861d56250a401ec0f261655d2509004982e74a0b74d954000685d0d810c06550001438905cc65505401fc0f66375d51611004982c7221542584400040fe5d86550548800103d97a1954151201244b261545c8544800142c9655172151200040fe5d8655054c404922c9261954153101260b2087559142c400103d97a1954152101248ba4a86550548404982e821d76450a100040fe61751d7644400103e96e1d54151100060718f87550544400182c62e1d54151100040f65e86550544400103c989d9541511000487e6154153634400122f9855054d89100040fe61751d5640400103d96e1d54150100060798f87550540400182e62e1d54150100040fe5d86550540400103e985d9541501000487e6154151630400122f9855054588100053125d631c91004001c847458c7244010
  | 1 => 0x5a5d099180000050805c00000cc1c350c1b000232f800e400109d07e009c024007a001403e442707894653c13c000d3d9540000410e4ea7d200c034143998c166a1496c220030054b0000b00082873f05c84370018400004280020480014c00000e9c0006f000008e1b188f868860220cb4513217000000000c00771292c4c003480044021399886051d8bd0262161a00056000000067000a89a57370a07a803fa10f23c0c8e800012a1b46406229c41e760e000f82b000000e2424800001226020b25200178000c001ac6c0000020000000002060b00000100060102120f00070207090c03051002020407010008010601060002530007013fc0f66273dd9541500f03d981cb765505400507a4c72dd9541500141d931cb765505400507a4c82dd9541500141d9320b76550540040fa6032dd9541500103d980cb76550540050be4981dd9541500142c92607765505400507a4c81dd9541500141d9320776550540040fa6331dd9541500103d98cc776550540050ba4b31dd9541500142d92cc776550540040fa6231dd9541500103d988c776550540040fa6021dd95415
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x248832a19550d3258854
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x2
  | 4 => 0x4b
  | 5 => 0x4c
  | 6 => 0x124c
  | 7 => 0x5
  | 8 => 0x94b
  | 9 => 0x94c
  | 10 => 0x124b
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x98c
  | 14 => 0x128c
  | 15 => 0x10b
  | 16 => 0x10c
  | 17 => 0x130c
  | 18 => 0x6
  | 19 => 0xa0b
  | 20 => 0xa0c
  | 21 => 0x130b
  | 22 => 0x180b
  | 23 => 0x180c
  | 24 => 0xb0c
  | 25 => 0x140c
  | 26 => 0x28b
  | 27 => 0x28c
  | 28 => 0xb8b
  | 29 => 0xb8c
  | 30 => 0x148b
  | 31 => 0x148c
  | 32 => 0x184b
  | 33 => 0x184c
  | 34 => 0xd0c
  | 35 => 0x188c
  | 36 => 0x74b
  | 37 => 0x74c
  | 38 => 0x104b
  | 39 => 0x104c
  | 40 => 0x194b
  | 41 => 0x194c
  | 42 => 0x95254
  | 43 => 0x94054
  | 44 => 0x124954
  | 45 => 0x98954
  | 46 => 0x128a
  | 47 => 0x128954
  | 48 => 0x8a
  | 49 => 0x12ca
  | 50 => 0x10a
  | 51 => 0x130a
  | 52 => 0x139254
  | 53 => 0x99254
  | 54 => 0x99294
  | 55 => 0x98b14
  | 56 => 0x141294
  | 57 => 0xa1314
  | 58 => 0xa0114
  | 59 => 0x10e
  | 60 => 0x14d
  | 61 => 0x134d
  | 62 => 0x148114
  | 63 => 0xbcd
  | 64 => 0x19cd
  | 65 => 0xd0114
  | 66 => 0x130e
  | 67 => 0x1a8b
  | 68 => 0x1a8114
  | 69 => 0x130a14
  | 70 => 0xa4c
  | 71 => 0x134c
  | 72 => 0x198c
  | 73 => 0xb8a14
  | 74 => 0xa0b94
  | 75 => 0xb8e
  | 76 => 0x184a14
  | 77 => 0xa1854
  | 78 => 0x184e
  | 79 => 0x2cc
  | 80 => 0xbcc
  | 81 => 0x14cc
  | 82 => 0x19cc
  | 83 => 0xd4c
  | 84 => 0x1a0c
  | 85 => 0x12cd
  | 86 => 0x1a8c
  | 87 => 0x181314
  | 88 => 0x29314
  | 89 => 0x149314
  | 90 => 0xd1314
  | 91 => 0x189314
  | 92 => 0x75313
  | 93 => 0x75314
  | 94 => 0x1a9314
  | 95 => 0x180b94
  | 96 => 0xd0b94
  | 97 => 0x188b94
  | 98 => 0x74b93
  | 99 => 0x74b94
  | 100 => 0x1a8b94
  | 101 => 0xb4d
  | 102 => 0xd1854
  | 103 => 0x1a9854
  | 104 => 0xd1054
  | 105 => 0x194d14
  | 106 => 0xd1954
  | 107 => 0x44d
  | 108 => 0x164d
  | 109 => 0x189054
  | 110 => 0x104753
  | 111 => 0x104754
  | 112 => 0x75054
  | 113 => 0x1a9953
  | 114 => 0x1a9954
  | 115 => 0x4954
  | 116 => 0x5554
  | 117 => 0xcd
  | 118 => 0xca
  | 119 => 0x134a
  | 120 => 0x14a
  | 121 => 0x95294
  | 122 => 0xe8e
  | 123 => 0x18ce
  | 124 => 0x18ca
  | 125 => 0xe8a
  | 126 => 0x75813
  | 127 => 0xecd
  | 128 => 0x1a4d
  | 129 => 0xce
  | 130 => 0xb4e
  | 131 => 0x160e
  | 132 => 0x14c
  | 133 => 0x130753
  | 134 => 0x1a4a
  | 135 => 0xb8753
  | 136 => 0x149854
  | 137 => 0x74293
  | 138 => 0x74a13
  | 139 => 0x75493
  | 140 => 0xe8753
  | 141 => 0x74593
  | 142 => 0x75793
  | 143 => 0x74e93
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 1548
  | 6 => 4251
  | 5 => 2273
  | 4 => 136
  | 3 => 1
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
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (64752+((h/623+packedAt gbK7 (57276+(h % 623)*12) 12) % 2713)*12) 12
  | 6 => packedAt gbK6 (224666+((h/1586+packedAt gbK6 (204048+(h % 1586)*13) 13) % 5710)*14) 14
  | 5 => packedAt gbK5 (143947+((h/820+packedAt gbK5 (134107+(h % 820)*12) 12) % 3250)*13) 13
  | 4 => packedAt gbK4 (9880+((h/45+packedAt gbK4 (9520+(h % 45)*8) 8) % 181)*9) 9
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe07ffff80fff80fffff807f427cf3e79f3f3
  | 1 => 0xfff81e07ff07fff07c03ffffbda34c7a63c9f
  | 2 => 0xf07ffe007fff83fff8003ff80c1c38f9c7cf1c
  | 3 => 0x7fffff800003ffffffc0000fe03f01f80fe0
  | 4 => 0x7ffffffffffc00000000000fffc001fff000
  | 5 => 0xff80000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10800a409800848008548812a000c11a08d131
  | 1 => 0xd2280a422906929068112a541ca1444a22486
  | 2 => 0xa05556084d2d02d2d002a5502c1428a9454b18
  | 3 => 0x8479e53d0184237ce72b00604ee03e01f00ec0
  | 4 => 0x87e79de77ce7018420c01818f7f4001ffb000
  | 5 => 0xce10401006084060843006060fbfbff6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36697
namespace PEqualNP.Outside.L_meta_36697
open PEqualNP.Outside.L_meta_36697.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 3 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 68 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 129 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
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
theorem bs3_3_96 : Interval s3Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 112 := (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96))
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
theorem bs3_4_1344 : Interval s3Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 (concat bs3_4_864 bs3_4_896)) (concat bs3_4_928 (concat bs3_4_960 bs3_4_992)))) (concat (concat (concat bs3_4_1024 bs3_4_1056) (concat bs3_4_1088 (concat bs3_4_1120 bs3_4_1152))) (concat (concat bs3_4_1184 (concat bs3_4_1216 bs3_4_1248)) (concat bs3_4_1280 (concat bs3_4_1312 bs3_4_1344))))))
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
theorem bs3_5_992 : Interval s3Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 bs3_5_96)) (concat (concat bs3_5_128 bs3_5_160) (concat bs3_5_192 bs3_5_224))) (concat (concat (concat bs3_5_256 bs3_5_288) (concat bs3_5_320 bs3_5_352)) (concat (concat bs3_5_384 bs3_5_416) (concat bs3_5_448 bs3_5_480)))) (concat (concat (concat (concat bs3_5_512 bs3_5_544) (concat bs3_5_576 bs3_5_608)) (concat (concat bs3_5_640 bs3_5_672) (concat bs3_5_704 bs3_5_736))) (concat (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)) (concat (concat bs3_5_896 bs3_5_928) (concat bs3_5_960 bs3_5_992)))))
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
theorem bs4_3_0 : Interval s4Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 4 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 12 := bs4_4_0
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
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 4 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 12 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 136 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_2272 : Interval gbAtlas 5 2272 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2273 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))))))
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
theorem bgb_6_4224 : Interval gbAtlas 6 4224 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4251 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))))) (concat (concat (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280))) (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)))) (concat (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792))) (concat (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))))) (concat (concat (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336))) (concat (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464)) (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)))) (concat (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848))) (concat (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)))))) (concat (concat (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))))) (concat (concat (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808)) (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 bgb_6_3936))) (concat (concat (concat bgb_6_3968 bgb_6_4000) (concat bgb_6_4032 bgb_6_4064)) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224))))))))
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
theorem bgb_7_1536 : Interval gbAtlas 7 1536 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1548 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 50, 58),(inputs.getD 4 zero, 42, 58),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8eeeaeae8eae8eac8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36697.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[1,3]⟩,⟨.and,[4,5]⟩,⟨.or,[2,8]⟩,⟨.and,[1,9]⟩,⟨.and,[6,10]⟩,⟨.or,[0,11]⟩,⟨.or,[4,5]⟩,⟨.and,[9,13]⟩,⟨.or,[7,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36697

open PEqualNP.Outside.L_meta_36697 in
theorem PEqualNP.Outside.L_meta_36697 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941133000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
